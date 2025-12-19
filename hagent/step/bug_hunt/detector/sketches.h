#ifndef SKETCHES_H
#define SKETCHES_H

#include <bitset>
#include <cmath>
#include "utils.h"

namespace inv {

struct Bloom1024 {
    std::bitset<1024> bits;
    void add(uint64_t v) {
        for (int i = 0; i < 3; i++) {
            bits.set(hash64(v + i) & 1023);
        }
    }
    int count() const { return (int)bits.count(); }
    void reset() { bits.reset(); }
};

struct DistinctSketch {
    std::bitset<1024> bits;
    void add(uint64_t v) { bits.set(hash64(v) & 1023); }
    double estimate() const {
        double z = 1024.0 - (double)bits.count();
        if (z == 0) z = 0.5;
        return -1024.0 * std::log(z / 1024.0);
    }
    void reset() { bits.reset(); }
};

} // namespace inv

#endif // SKETCHES_H
