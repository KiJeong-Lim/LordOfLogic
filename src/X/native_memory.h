#ifndef HOL_NATIVE_MEMORY_H
#define HOL_NATIVE_MEMORY_H

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdatomic.h>

/* An execution and its snapshots own one account. Allocation headers retain
    * the account, so a foreign finalizer may free the last shared block after
    * the original machine has gone. A fork gets an independent account. */
enum HMCounter {
    HM_VISITS, HM_NORMALIZE_VISITS, HM_BIND_VISITS, HM_SCOPE_VISITS,
    HM_NODES_CREATED, HM_NODES_COPIED, HM_NODES_EXPORTED, HM_GC_VISITS, HM_PROGRAM_ROWS,
    HM_COUNTERS
};

typedef struct HMemory {
    _Atomic size_t references, bytes, peak, limit;
    _Atomic int fault, counting;
    _Atomic uint64_t counters[HM_COUNTERS];
} HMemory;

typedef union {
    max_align_t alignment;
    struct { HMemory *owner; size_t bytes; } allocation;
} HMemoryHeader;

static inline HMemory *hm_create(void)
{
    HMemory *memory = calloc(1, sizeof(*memory));
    if (memory) {
        atomic_init(&memory->references, 1);
        atomic_init(&memory->bytes, sizeof(*memory));
        atomic_init(&memory->peak, sizeof(*memory));
        atomic_init(&memory->limit, 0);
        atomic_init(&memory->fault, 0);
        atomic_init(&memory->counting, 0);
        for (size_t i = 0; i < HM_COUNTERS; ++i) atomic_init(&memory->counters[i], 0);
    }
    return memory;
}

static inline void hm_retain(HMemory *memory)
{
    atomic_fetch_add_explicit(&memory->references, 1, memory_order_relaxed);
}

static inline void hm_release(HMemory *memory)
{
    if (memory && atomic_fetch_sub_explicit(&memory->references, 1, memory_order_acq_rel) == 1) free(memory);
}

static inline int hm_reserve(HMemory *memory, size_t bytes)
{
    size_t before = atomic_load_explicit(&memory->bytes, memory_order_relaxed);
    for (;;) {
        size_t limit = atomic_load_explicit(&memory->limit, memory_order_relaxed);
        if (bytes > SIZE_MAX - before || (limit && (before > limit || bytes > limit - before))) {
            atomic_store_explicit(&memory->fault, 1, memory_order_relaxed);
            return 0;
        }
        if (atomic_compare_exchange_weak_explicit(&memory->bytes, &before, before + bytes, memory_order_relaxed, memory_order_relaxed)) break;
    }
    size_t peak = atomic_load_explicit(&memory->peak, memory_order_relaxed);
    while (peak < before + bytes && !atomic_compare_exchange_weak_explicit(&memory->peak, &peak, before + bytes, memory_order_relaxed, memory_order_relaxed)) { }
    return 1;
}

static inline void hm_unreserve(HMemory *memory, size_t bytes)
{
    atomic_fetch_sub_explicit(&memory->bytes, bytes, memory_order_relaxed);
}

static inline void *hm_alloc(HMemory *memory, size_t bytes)
{
    if (bytes > SIZE_MAX - sizeof(HMemoryHeader)) {
        atomic_store_explicit(&memory->fault, 2, memory_order_relaxed);
        return NULL;
    }
    size_t total = sizeof(HMemoryHeader) + bytes;
    if (!hm_reserve(memory, total)) return NULL;
    HMemoryHeader *header = malloc(total);
    if (!header) {
        hm_unreserve(memory, total);
        atomic_store_explicit(&memory->fault, 2, memory_order_relaxed);
        return NULL;
    }
    hm_retain(memory);
    header->allocation.owner = memory;
    header->allocation.bytes = bytes;
    return header + 1;
}

static inline void *hm_calloc(HMemory *memory, size_t count, size_t width)
{
    if (width && count > SIZE_MAX / width) {
        atomic_store_explicit(&memory->fault, 2, memory_order_relaxed);
        return NULL;
    }
    size_t bytes = count * width;
    void *pointer = hm_alloc(memory, bytes);
    if (pointer) memset(pointer, 0, bytes);
    return pointer;
}

static inline void hm_free(void *pointer)
{
    if (!pointer) return;
    HMemoryHeader *header = (HMemoryHeader *) pointer - 1;
    HMemory *memory = header->allocation.owner;
    hm_unreserve(memory, sizeof(*header) + header->allocation.bytes);
    free(header);
    hm_release(memory);
}

static inline size_t hm_size(const void *pointer)
{
    return pointer ? ((const HMemoryHeader *) pointer - 1)->allocation.bytes : 0;
}

static inline void *hm_realloc(HMemory *memory, void *pointer, size_t bytes)
{
    if (!pointer) return hm_alloc(memory, bytes);
    if (!bytes) { hm_free(pointer); return NULL; }
    HMemoryHeader *header = (HMemoryHeader *) pointer - 1;
    HMemory *owner = header->allocation.owner;
    size_t old = header->allocation.bytes;
    if (owner != memory || bytes > SIZE_MAX - sizeof(*header)) {
        atomic_store_explicit(&memory->fault, 2, memory_order_relaxed);
        return NULL;
    }
    if (bytes > old && !hm_reserve(memory, bytes - old)) return NULL;
    HMemoryHeader *grown = realloc(header, sizeof(*header) + bytes);
    if (!grown) {
        if (bytes > old) hm_unreserve(memory, bytes - old);
        atomic_store_explicit(&memory->fault, 2, memory_order_relaxed);
        return NULL;
    }
    if (bytes < old) hm_unreserve(memory, old - bytes);
    grown->allocation.bytes = bytes;
    return grown + 1;
}

static inline HMemory *hm_owner(const void *pointer)
{
    return pointer ? ((const HMemoryHeader *) pointer - 1)->allocation.owner : NULL;
}

typedef struct {
    _Atomic size_t references;
    HMemory *memory;
    size_t bytes;
} HMemoryLease;

/* A different execution charges shared storage once, until its last snapshot
    * releases the lease. The physical owner remains retained by the block. */
static inline HMemoryLease *hm_lease(HMemory *memory, size_t bytes)
{
    HMemoryLease *lease = hm_alloc(memory, sizeof(*lease));
    if (!lease) return NULL;
    if (!hm_reserve(memory, bytes)) { hm_free(lease); return NULL; }
    atomic_init(&lease->references, 1);
    lease->memory = memory;
    lease->bytes = bytes;
    return lease;
}

static inline void hm_lease_retain(HMemoryLease *lease)
{
    if (lease) atomic_fetch_add_explicit(&lease->references, 1, memory_order_relaxed);
}

static inline void hm_lease_release(HMemoryLease *lease)
{
    if (lease && atomic_fetch_sub_explicit(&lease->references, 1, memory_order_acq_rel) == 1) {
        hm_unreserve(lease->memory, lease->bytes);
        hm_free(lease);
    }
}

static inline void hm_count(HMemory *memory, enum HMCounter counter, uint64_t amount)
{
    if (atomic_load_explicit(&memory->counting, memory_order_relaxed)) {
        atomic_fetch_add_explicit(&memory->counters[counter], amount, memory_order_relaxed);
    }
}

#endif
