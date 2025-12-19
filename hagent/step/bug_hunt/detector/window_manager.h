#ifndef WINDOW_MANAGER_H
#define WINDOW_MANAGER_H

#include "invariance_types.h"

namespace inv {

enum class WindowMode { EVENTS, TIME, RETIRE };

struct WindowPolicy {
    WindowMode mode = WindowMode::EVENTS;
    uint64_t eventsN = 50000;
    uint64_t timeN = 0;
    Str retireSig;
};

class WindowManager {
    WindowPolicy pol_;
    uint64_t evCnt_ = 0;
    TimeT nextT_ = 0;
public:
    WindowManager(const WindowPolicy& p) : pol_(p) {
        if(pol_.mode == WindowMode::TIME) nextT_ = pol_.timeN;
    }
    bool shouldRotateEvent() {
        if(pol_.mode != WindowMode::EVENTS) return false;
        return (++evCnt_ >= pol_.eventsN);
    }
    bool shouldRotateTime(TimeT t) {
        if(pol_.mode != WindowMode::TIME) return false;
        if(t >= nextT_) { nextT_ += pol_.timeN; return true; }
        return false;
    }
    bool shouldRotateRetire(const Str& s) {
        return (pol_.mode == WindowMode::RETIRE && !pol_.retireSig.empty() && s == pol_.retireSig);
    }
    void resetEvent() { evCnt_ = 0; }
};

} // namespace inv

#endif // WINDOW_MANAGER_H
