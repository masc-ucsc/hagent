#ifndef PAIR_KEY_H
#define PAIR_KEY_H

#include <string>
#include <functional>
#include "invariance_types.h"

namespace inv {

struct PairKey {
    Str a, b;
    bool operator==(const PairKey& o) const {
        return a == o.a && b == o.b;
    }
};

struct PairKeyHash {
    size_t operator()(const PairKey& p) const {
        return std::hash<Str>()(p.a) ^ (std::hash<Str>()(p.b) << 1);
    }
};

} // namespace inv

#endif // PAIR_KEY_H
