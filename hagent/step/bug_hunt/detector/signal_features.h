#ifndef SIGNAL_FEATURES_H
#define SIGNAL_FEATURES_H

#include "invariance_types.h"
#include "sketches.h"
#include "thermo_types.h"
#include <unordered_set> // NEW

namespace inv {

struct SigWindowFeat {
    // Legacy
    uint64_t ups=0, downs=0, toggles=0;
    Bloom1024 flipBloom;
    DistinctSketch distinct;
    uint64_t prev=0; 
    bool havePrev=false;
    
    // Stable bit masks
    uint64_t seen1=0;
    uint64_t seen0=0;

    // TIP
    SigThermoFeat thermo;
    int sigWidth=1;

    void initWidth(int w) {
        sigWidth = w;
        thermo.init(w);
    }

    inline void see(uint64_t v, uint64_t mask, uint64_t t) {
        v &= mask;
        thermo.observe(v, t, mask);

        if(!havePrev) {
            havePrev = true;
            prev = v;
            distinct.add(v);
            seen1 |= v;
            seen0 |= (~v) & mask;
            return;
        }
        if(v != prev) {
            toggles++;
            if((prev&1)==0 && (v&1)==1) ups++;
            else if((prev&1)==1 && (v&1)==0) downs++;
            
            uint64_t diff = (prev ^ v) & mask;
            while(diff) {
                flipBloom.add(__builtin_ctzll(diff));
                diff &= diff-1;
            }
            prev = v;
        }
        distinct.add(v);
        seen1 |= v;
        seen0 |= (~v) & mask;
    }

    // NEW: Get the window's unique ID
    uint64_t getSignature() const {
        uint64_t h = thermo.signature();
        // Also hash the stable masks to catch "Stuck At" behaviors uniquely
        hash_combine(h, seen1);
        hash_combine(h, seen0);
        return h;
    }

    double transEntropy() const {
        if(toggles==0) return 0.0;
        auto H = [&](double x){ 
            if(x<=0) return 0.0; 
            double p = x/(double)toggles; 
            return -p*std::log2(p); 
        };
        return H((double)ups) + H((double)downs);
    }

    void reset() {
        ups=downs=toggles=0;
        flipBloom.reset(); distinct.reset();
        prev=0; havePrev=false;
        seen1=0; seen0=0;
        thermo.reset();
    }
};

struct SigAgg {
    uint64_t winCnt=0;
    double entSum=0.0;
    double divSum=0.0;
    uint64_t stable0_mask = ~0ULL;
    uint64_t stable1_mask = ~0ULL;
    uint64_t toggleWins=0;

    SigThermoAgg thermo;
    
    // NEW: The Set of "Coverage Marks" (Signatures) seen for this signal
    std::unordered_set<uint64_t> signatures;

    int sigWidth=1;

    void initWidth(int w) {
        sigWidth = w;
        thermo.init(w);
    }

    void update(const SigWindowFeat& f, uint64_t mask) {
        winCnt++;
        entSum += f.transEntropy();
        divSum += f.distinct.estimate();
        stable0_mask &= (~f.seen1) & mask;
        stable1_mask &= (~f.seen0) & mask;
        if(f.toggles) toggleWins++;
        thermo.accumulate(f.thermo);
        
        // NEW: Capture the signature of this window
        signatures.insert(f.getSignature());
    }

    double meanEntropy() const { return winCnt ? entSum/winCnt : 0.0; }
    double meanDiversity() const { return winCnt ? divSum/winCnt : 0.0; }
};

} // namespace inv

#endif // SIGNAL_FEATURES_H