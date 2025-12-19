#ifndef INVARIANCE_TYPES_H
#define INVARIANCE_TYPES_H

#include <string>
#include <cstdint>
#include <vector>

namespace inv {

using Str = std::string;
using TimeT = uint64_t;

// Maximum width to track individual bit
constexpr int MAX_TRACKED_BITS = 64;

} // namespace inv

#endif // INVARIANCE_TYPES_H
