#ifndef UTILS_H
#define UTILS_H

#include <cstdint>
#include "invariance_types.h"

namespace inv {

// Population count
inline int popc(uint64_t x) {
    return __builtin_popcountll(x);
}

// Rotate left
inline uint64_t rotl(uint64_t v, int s) {
    return (v << s) | (v >> (64 - s));
}

// 64-bit hash function (Murmur3-like mixer)
inline uint64_t hash64(uint64_t x) {
    x ^= rotl(x, 25) ^ rotl(x, 47);
    x *= 0x9e6c63d0676a9a99ULL;
    x ^= rotl(x, 23) ^ rotl(x, 51);
    x *= 0x9e6d62d06f6a9a95ULL;
    return x ^ (x >> 28);
}

// NEW: Hash Combiner for signatures
inline void hash_combine(uint64_t& seed, uint64_t v) {
    seed ^= hash64(v) + 0x9e3779b97f4a7c15ULL + (seed << 6) + (seed >> 2);
}

} // namespace inv

#endif // UTILS_H