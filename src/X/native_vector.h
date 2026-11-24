#ifndef HOL_NATIVE_VECTOR_H
#define HOL_NATIVE_VECTOR_H

#include "native_memory.h"
#include <limits.h>

/* A 64-way persistent vector. A retained root is immutable; only a path with
    * reference count one may be changed. Different vector objects may be used
    * by different threads, but access to one object must be serialized.
    *
    * copy clones an element, including owned payload, into uninitialized
    * storage. On failure it must release any partial payload itself. drop is
    * called only for completely initialized elements. NULL callbacks mean
    * byte-copy and no owned payload. append copies, rather than consuming, its
    * argument. mutable exposes an existing element and transfers no ownership.
    * A failed allocation preserves values and length; it may unshare a path.
    * truncate additionally preserves the old root on allocation failure.
    *
    * bytes counts tree storage including allocator headers, not element
    * payload. A client sharing roots across accounts must charge foreign
    * storage with a lease. Nodes keep their physical allocator owner alive. */
enum { HV_BITS = 6, HV_WIDTH = 64 };

typedef int (*HvCopy)(HMemory *, void *, const void *);
typedef void (*HvDrop)(void *);

typedef struct HvNode {
    _Atomic size_t references;
    size_t count, bytes;
    unsigned level;
    max_align_t data[];
} HvNode;

typedef struct {
    HMemory *memory;
    HvNode *root;
    size_t width, count;
    HvCopy copy;
    HvDrop drop;
} HvVector;

static inline HvNode **hv_children(HvNode *node)
{
    return (HvNode **) (void *) node->data;
}

static inline void *hv_element(const HvVector *vector, HvNode *node, size_t index)
{
    return (unsigned char *) (void *) node->data + index * vector->width;
}

static inline void hv_retain(HvNode *node)
{
    if (node) atomic_fetch_add_explicit(&node->references, 1, memory_order_relaxed);
}

static inline void hv_release(const HvVector *vector, HvNode *node)
{
    if (!node || atomic_fetch_sub_explicit(&node->references, 1, memory_order_acq_rel) != 1) return;
    if (node->level) {
        for (size_t i = 0; i < HV_WIDTH; ++i) hv_release(vector, hv_children(node)[i]);
    } else if (vector->drop) {
        for (size_t i = 0; i < node->count; ++i) vector->drop(hv_element(vector, node, i));
    }
    hm_free(node);
}

static inline int hv_init(HvVector *vector, HMemory *memory, size_t width, HvCopy copy, HvDrop drop)
{
    if (!memory || !width || width > (SIZE_MAX - sizeof(HvNode)) / HV_WIDTH) return 0;
    *vector = (HvVector) { memory, NULL, width, 0, copy, drop };
    hm_retain(memory);
    return 1;
}

static inline void hv_destroy(HvVector *vector)
{
    if (!vector->memory) return;
    hv_release(vector, vector->root);
    hm_release(vector->memory);
    *vector = (HvVector) { 0 };
}

static inline void hv_clone(HvVector *target, const HvVector *source, HMemory *memory)
{
    *target = *source;
    target->memory = memory;
    hm_retain(memory);
    hv_retain(target->root);
}

static inline size_t hv_bytes(const HvVector *vector)
{
    return vector->root ? vector->root->bytes : 0;
}

static inline HvNode *hv_new(const HvVector *vector, unsigned level)
{
    size_t payload = HV_WIDTH * (level ? sizeof(HvNode *) : vector->width);
    HvNode *node = hm_calloc(vector->memory, 1, sizeof(*node) + payload);
    if (node) {
        atomic_init(&node->references, 1);
        node->level = level;
        node->bytes = sizeof(HMemoryHeader) + hm_size(node);
    }
    return node;
}

static inline int hv_copy_element(const HvVector *vector, void *target, const void *source)
{
    if (vector->copy) return vector->copy(vector->memory, target, source);
    memcpy(target, source, vector->width);
    return 1;
}

static inline void hv_summary(HvNode *node)
{
    node->bytes = sizeof(HMemoryHeader) + hm_size(node);
    if (!node->level) return;
    node->count = 0;
    for (size_t i = 0; i < HV_WIDTH; ++i) {
        HvNode *child = hv_children(node)[i];
        if (child) {
            node->bytes += child->bytes;
            node->count += child->count;
        }
    }
}

static inline HvNode *hv_copy_node(const HvVector *vector, HvNode *source)
{
    HvNode *node = hv_new(vector, source->level);
    if (!node) return NULL;
    if (source->level) {
        for (size_t i = 0; i < HV_WIDTH; ++i) {
            hv_children(node)[i] = hv_children(source)[i];
            hv_retain(hv_children(node)[i]);
        }
        hv_summary(node);
    } else {
        for (; node->count < source->count; ++node->count) {
            if (!hv_copy_element(vector, hv_element(vector, node, node->count), hv_element(vector, source, node->count))) {
                hv_release(vector, node);
                return NULL;
            }
        }
    }
    return node;
}

static inline int hv_private(const HvVector *vector, HvNode **link)
{
    HvNode *node = *link;
    if (atomic_load_explicit(&node->references, memory_order_acquire) == 1 && hm_owner(node) == vector->memory) return 1;
    HvNode *copy = hv_copy_node(vector, node);
    if (!copy) return 0;
    *link = copy;
    hv_release(vector, node);
    return 1;
}

static inline size_t hv_capacity(unsigned level)
{
    unsigned bits = (level + 1) * HV_BITS;
    return bits >= sizeof(size_t) * CHAR_BIT ? SIZE_MAX : (size_t) 1 << bits;
}

static inline const void *hv_get(const HvVector *vector, size_t index)
{
    if (index >= vector->count) return NULL;
    HvNode *node = vector->root;
    while (node->level) node = hv_children(node)[(index >> (node->level * HV_BITS)) & (HV_WIDTH - 1)];
    return hv_element(vector, node, index & (HV_WIDTH - 1));
}

/* Path length is bounded by the number of bits of size_t, not data depth. */
static inline HvNode *hv_path(HvVector *vector, size_t index, HvNode **path, size_t *length)
{
    *length = 0;
    if (!vector->root) {
        vector->root = hv_new(vector, 0);
        if (!vector->root) return NULL;
    }
    while (index >= hv_capacity(vector->root->level)) {
        HvNode *parent = hv_new(vector, vector->root->level + 1);
        if (!parent) return NULL;
        hv_children(parent)[0] = vector->root;
        hv_summary(parent);
        vector->root = parent;
    }
    HvNode **link = &vector->root;
    for (;;) {
        if (!hv_private(vector, link)) return NULL;
        HvNode *node = *link;
        path[(*length)++] = node;
        if (!node->level) return node;
        link = &hv_children(node)[(index >> (node->level * HV_BITS)) & (HV_WIDTH - 1)];
        if (!*link) {
            *link = hv_new(vector, node->level - 1);
            if (!*link) return NULL;
        }
    }
}

static inline void hv_summarize_path(HvNode **path, size_t length)
{
    while (length) hv_summary(path[--length]);
}

static inline void *hv_mutable(HvVector *vector, size_t index)
{
    if (index >= vector->count) return NULL;
    HvNode *path[sizeof(size_t) * CHAR_BIT / HV_BITS + 2];
    size_t length;
    HvNode *leaf = hv_path(vector, index, path, &length);
    hv_summarize_path(path, length);
    return leaf ? hv_element(vector, leaf, index & (HV_WIDTH - 1)) : NULL;
}

static inline int hv_append(HvVector *vector, const void *value)
{
    if (vector->count == SIZE_MAX) return 0;
    /* The argument may itself be borrowed from the last leaf. A foreign
        * account's uniquely retained leaf is released when its path is copied,
        * so remember the slot before that copy and read its new location. */
    size_t borrowed = SIZE_MAX;
    if (vector->count && (vector->count & (HV_WIDTH - 1))) {
        HvNode *old = vector->root;
        size_t index = vector->count - 1;
        while (old->level) old = hv_children(old)[(index >> (old->level * HV_BITS)) & (HV_WIDTH - 1)];
        uintptr_t first = (uintptr_t) (void *) old->data;
        uintptr_t address = (uintptr_t) value;
        if (address >= first && address - first < old->count * vector->width && (address - first) % vector->width == 0) borrowed = (size_t) (address - first) / vector->width;
    }
    HvNode *path[sizeof(size_t) * CHAR_BIT / HV_BITS + 2];
    size_t length;
    HvNode *leaf = hv_path(vector, vector->count, path, &length);
    const void *source = leaf && borrowed != SIZE_MAX ? hv_element(vector, leaf, borrowed) : value;
    int success = leaf && hv_copy_element(vector, hv_element(vector, leaf, vector->count & (HV_WIDTH - 1)), source);
    if (success) {
        ++leaf->count;
        ++vector->count;
    }
    hv_summarize_path(path, length);
    return success;
}

/* Build a retained prefix before publishing it. Fully retained subtrees are
    * shared; only the right boundary path and its last leaf are copied. */
static inline HvNode *hv_prefix(const HvVector *vector, HvNode *source, size_t count)
{
    if (count == source->count) {
        hv_retain(source);
        return source;
    }
    HvNode *node = hv_new(vector, source->level);
    if (!node) return NULL;
    if (node->level) {
        for (size_t i = 0; count && i < HV_WIDTH; ++i) {
            HvNode *child = hv_children(source)[i];
            size_t taken = count < child->count ? count : child->count;
            hv_children(node)[i] = hv_prefix(vector, child, taken);
            if (!hv_children(node)[i]) {
                hv_release(vector, node);
                return NULL;
            }
            count -= taken;
        }
        hv_summary(node);
    } else {
        for (; node->count < count; ++node->count) {
            if (!hv_copy_element(vector, hv_element(vector, node, node->count), hv_element(vector, source, node->count))) {
                hv_release(vector, node);
                return NULL;
            }
        }
    }
    return node;
}

static inline int hv_truncate(HvVector *vector, size_t count)
{
    if (count > vector->count) return 0;
    if (count == vector->count) return 1;
    HvNode *next = count ? hv_prefix(vector, vector->root, count) : NULL;
    if (count && !next) return 0;
    hv_release(vector, vector->root);
    vector->root = next;
    vector->count = count;
    return 1;
}

#endif
