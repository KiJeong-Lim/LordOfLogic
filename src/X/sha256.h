#ifndef HOL_SHA256_H
#define HOL_SHA256_H

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* FIPS 180-4 SHA-256, the same schedule and rounds as Z.Hash. This function
 * allocates no heap memory and retains no caller buffer or mutable globals.
 * Input length is measured in bytes; arithmetic in rounds is uint32_t. */
static const uint32_t hol_sha256_constants[64] = {
    UINT32_C(0x428a2f98), UINT32_C(0x71374491), UINT32_C(0xb5c0fbcf), UINT32_C(0xe9b5dba5),
    UINT32_C(0x3956c25b), UINT32_C(0x59f111f1), UINT32_C(0x923f82a4), UINT32_C(0xab1c5ed5),
    UINT32_C(0xd807aa98), UINT32_C(0x12835b01), UINT32_C(0x243185be), UINT32_C(0x550c7dc3),
    UINT32_C(0x72be5d74), UINT32_C(0x80deb1fe), UINT32_C(0x9bdc06a7), UINT32_C(0xc19bf174),
    UINT32_C(0xe49b69c1), UINT32_C(0xefbe4786), UINT32_C(0x0fc19dc6), UINT32_C(0x240ca1cc),
    UINT32_C(0x2de92c6f), UINT32_C(0x4a7484aa), UINT32_C(0x5cb0a9dc), UINT32_C(0x76f988da),
    UINT32_C(0x983e5152), UINT32_C(0xa831c66d), UINT32_C(0xb00327c8), UINT32_C(0xbf597fc7),
    UINT32_C(0xc6e00bf3), UINT32_C(0xd5a79147), UINT32_C(0x06ca6351), UINT32_C(0x14292967),
    UINT32_C(0x27b70a85), UINT32_C(0x2e1b2138), UINT32_C(0x4d2c6dfc), UINT32_C(0x53380d13),
    UINT32_C(0x650a7354), UINT32_C(0x766a0abb), UINT32_C(0x81c2c92e), UINT32_C(0x92722c85),
    UINT32_C(0xa2bfe8a1), UINT32_C(0xa81a664b), UINT32_C(0xc24b8b70), UINT32_C(0xc76c51a3),
    UINT32_C(0xd192e819), UINT32_C(0xd6990624), UINT32_C(0xf40e3585), UINT32_C(0x106aa070),
    UINT32_C(0x19a4c116), UINT32_C(0x1e376c08), UINT32_C(0x2748774c), UINT32_C(0x34b0bcb5),
    UINT32_C(0x391c0cb3), UINT32_C(0x4ed8aa4a), UINT32_C(0x5b9cca4f), UINT32_C(0x682e6ff3),
    UINT32_C(0x748f82ee), UINT32_C(0x78a5636f), UINT32_C(0x84c87814), UINT32_C(0x8cc70208),
    UINT32_C(0x90befffa), UINT32_C(0xa4506ceb), UINT32_C(0xbef9a3f7), UINT32_C(0xc67178f2)
};

static uint32_t hol_sha_rotate(uint32_t value, unsigned bits)
{
    return (value >> bits) | (value << (32u - bits));
}

static void hol_sha_block(uint32_t state[8], const uint8_t input[64])
{
    uint32_t words[64];
    for (unsigned i = 0; i < 16; ++i) {
        const uint8_t *p = input + 4u * i;
        words[i] = ((uint32_t)p[0] << 24) | ((uint32_t)p[1] << 16)
            | ((uint32_t)p[2] << 8) | (uint32_t)p[3];
    }
    for (unsigned i = 16; i < 64; ++i) {
        uint32_t x = words[i - 15], y = words[i - 2];
        uint32_t first = hol_sha_rotate(x, 7) ^ hol_sha_rotate(x, 18) ^ (x >> 3);
        uint32_t second = hol_sha_rotate(y, 17) ^ hol_sha_rotate(y, 19) ^ (y >> 10);
        words[i] = second + words[i - 7] + first + words[i - 16];
    }
    uint32_t a = state[0], b = state[1], c = state[2], d = state[3];
    uint32_t e = state[4], f = state[5], g = state[6], h = state[7];
    for (unsigned i = 0; i < 64; ++i) {
        uint32_t large_e = hol_sha_rotate(e, 6) ^ hol_sha_rotate(e, 11) ^ hol_sha_rotate(e, 25);
        uint32_t first = h + large_e + ((e & f) ^ (~e & g)) + hol_sha256_constants[i] + words[i];
        uint32_t large_a = hol_sha_rotate(a, 2) ^ hol_sha_rotate(a, 13) ^ hol_sha_rotate(a, 22);
        uint32_t second = large_a + ((a & b) ^ (a & c) ^ (b & c));
        h = g;
        g = f;
        f = e;
        e = d + first;
        d = c;
        c = b;
        b = a;
        a = first + second;
    }
    state[0] += a;
    state[1] += b;
    state[2] += c;
    state[3] += d;
    state[4] += e;
    state[5] += f;
    state[6] += g;
    state[7] += h;
}

static void hol_sha_finish(uint32_t state[8], const uint8_t *position,
    size_t remaining, uint64_t length, uint8_t output[32])
{
    uint8_t tail[128] = {0};
    if (remaining != 0) memcpy(tail, position, remaining);
    tail[remaining] = UINT8_C(0x80);
    size_t padded = remaining < 56 ? 64 : 128;
    uint64_t bits = (uint64_t)length * UINT64_C(8);
    for (unsigned i = 0; i < 8; ++i) tail[padded - 1 - i] = (uint8_t)(bits >> (8u * i));
    hol_sha_block(state, tail);
    if (padded == 128) hol_sha_block(state, tail + 64);
    for (unsigned i = 0; i < 8; ++i) {
        output[4u * i] = (uint8_t)(state[i] >> 24);
        output[4u * i + 1] = (uint8_t)(state[i] >> 16);
        output[4u * i + 2] = (uint8_t)(state[i] >> 8);
        output[4u * i + 3] = (uint8_t)state[i];
    }
}

static void hol_sha_initial(uint32_t state[8])
{
    const uint32_t initial[8] = {
        UINT32_C(0x6a09e667), UINT32_C(0xbb67ae85), UINT32_C(0x3c6ef372), UINT32_C(0xa54ff53a),
        UINT32_C(0x510e527f), UINT32_C(0x9b05688c), UINT32_C(0x1f83d9ab), UINT32_C(0x5be0cd19)
    };
    memcpy(state, initial, sizeof initial);
}

void hol_sha256(const uint8_t *input, size_t length, uint8_t output[32])
{
    uint32_t state[8];
    hol_sha_initial(state);
    size_t remaining = length;
    const uint8_t *position = input;
    while (remaining >= 64) {
        hol_sha_block(state, position);
        position += 64;
        remaining -= 64;
    }
    hol_sha_finish(state, position, remaining, (uint64_t)length, output);
}

/* The executable fingerprint must not allocate a Haskell String of its bytes. */
int hol_sha256_file(const char *path, uint8_t output[32])
{
    FILE *stream = fopen(path, "rb");
    if (stream == NULL) return 0;
    uint32_t state[8];
    hol_sha_initial(state);
    uint8_t buffer[8192];
    uint64_t length = 0;
    size_t remaining = 0;
    int success = 1;
    for (;;) {
        size_t count = fread(buffer + remaining, 1, sizeof buffer - remaining, stream);
        if (count > UINT64_MAX / 8 - length) { success = 0; break; }
        length += count;
        size_t total = remaining + count;
        size_t offset = 0;
        while (total - offset >= 64) {
            hol_sha_block(state, buffer + offset);
            offset += 64;
        }
        remaining = total - offset;
        if (remaining != 0) memmove(buffer, buffer + offset, remaining);
        if (ferror(stream)) { success = 0; break; }
        if (feof(stream)) break;
        if (count == 0) { success = 0; break; }
    }
    if (fclose(stream) != 0) success = 0;
    if (success) hol_sha_finish(state, buffer, remaining, length, output);
    return success;
}

#endif
