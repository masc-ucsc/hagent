#ifndef THERMO_TYPES_H
#define THERMO_TYPES_H

#include <array>
#include <algorithm>
#include "invariance_types.h"
#include "utils.h" // Needed for hash_combine

namespace inv {

// 2x2 Transition Matrix for a single bit
struct BitTransMatrix {
    uint32_t counts[4]; 

    BitTransMatrix() : counts{0,0,0,0} {}

    inline void record(bool prev, bool curr) {
        int idx = (prev ? 2 : 0) + (curr ? 1 : 0);
        counts[idx]++;
    }

    inline uint32_t total() const {
        return counts[0] + counts[1] + counts[2] + counts[3];
    }

    inline void get_probs(double out[4], double alpha = 0.5) const {
        double t = total() + 4.0 * alpha;
        for(int i=0; i<4; i++) out[i] = (counts[i] + alpha) / t;
    }

    inline void merge(const BitTransMatrix& o) {
        for(int i=0; i<4; i++) counts[i] += o.counts[i];
    }
    
    // NEW: Generate a signature of this matrix
    // We hash the counts to capture the "physics" of the transition
    inline uint64_t hash() const {
        uint64_t h = 0;
        for(int i=0; i<4; i++) hash_combine(h, counts[i]);
        return h;
    }

    inline void reset() { for(int i=0; i<4; i++) counts[i]=0; }
};

// Spectral (Inter-arrival) Statistics
struct SpectralStats {
    double mean;
    double M2;
    uint32_t count;
    uint64_t last_time;
    bool has_last;

    SpectralStats() : mean(0), M2(0), count(0), last_time(0), has_last(false) {}

    inline void record_toggle(uint64_t t) {
        if(has_last) {
            double interval = (double)(t - last_time);
            count++;
            double delta = interval - mean;
            mean += delta / count;
            double delta2 = interval - mean;
            M2 += delta * delta2;
        }
        last_time = t;
        has_last = true;
    }

    inline double variance() const {
        return (count < 2) ? 0.0 : M2 / (count - 1);
    }

    inline void merge(const SpectralStats& o) {
        if(o.count == 0) return;
        if(count == 0) { *this = o; return; }
        uint32_t new_n = count + o.count;
        double delta = o.mean - mean;
        double new_mean = mean + delta * o.count / new_n;
        double new_M2 = M2 + o.M2 + delta * delta * count * o.count / new_n;
        count = new_n;
        mean = new_mean;
        M2 = new_M2;
        if(o.has_last && (!has_last || o.last_time > last_time)) {
            last_time = o.last_time;
            has_last = true;
        }
    }
    
    // NEW: Signature of spectral behavior (quantized)
    inline uint64_t hash() const {
        uint64_t h = 0;
        // Quantize mean/variance to avoid floating point jitter affecting hash
        // We multiply by 100 to keep 2 decimal places of precision in the hash
        hash_combine(h, (uint64_t)(mean * 100.0));
        hash_combine(h, (uint64_t)(variance() * 100.0));
        return h;
    }

    inline void reset() { mean=0; M2=0; count=0; last_time=0; has_last=false; }
};

// Per-Signal Thermodynamic Container
struct SigThermoFeat {
    std::array<BitTransMatrix, MAX_TRACKED_BITS> bit_trans;
    BitTransMatrix sig_trans; 
    SpectralStats spectral;
    
    uint64_t prev_val;
    bool had_toggle;
    bool has_prev;
    int width;

    SigThermoFeat() : prev_val(0), had_toggle(false), has_prev(false), width(1) {}

    void init(int w) { width = std::min(w, MAX_TRACKED_BITS); reset(); }

    inline void observe(uint64_t val, uint64_t t, uint64_t mask) {
        val &= mask;
        if(!has_prev) {
            has_prev = true;
            prev_val = val;
            had_toggle = false;
            return;
        }
        bool toggled = (val != prev_val);
        sig_trans.record(had_toggle, toggled);

        if (toggled) {
            for(int b=0; b<width; b++) {
                bool pb = (prev_val >> b) & 1;
                bool cb = (val >> b) & 1;
                bit_trans[b].record(pb, cb);
            }
            spectral.record_toggle(t);
        } else {
             for(int b=0; b<width; b++) {
                bool pb = (prev_val >> b) & 1;
                bit_trans[b].record(pb, pb);
            }
        }
        prev_val = val;
        had_toggle = toggled;
    }

    // NEW: The "Window Signature"
    // This aggregates the physics of ALL bits into one 64-bit ID.
    // If this ID changes, the signal logic changed.
    uint64_t signature() const {
        uint64_t h = 0;
        hash_combine(h, sig_trans.hash());
        hash_combine(h, spectral.hash());
        for(int b=0; b<width; b++) {
            hash_combine(h, bit_trans[b].hash());
        }
        return h;
    }

    void merge(const SigThermoFeat& o) {
        sig_trans.merge(o.sig_trans);
        spectral.merge(o.spectral);
        for(int b=0; b<width; b++) bit_trans[b].merge(o.bit_trans[b]);
    }

    void reset() {
        for(auto& b : bit_trans) b.reset();
        sig_trans.reset();
        spectral.reset();
        has_prev = false;
    }
};

// Aggregated Stats
struct SigThermoAgg {
    std::array<BitTransMatrix, MAX_TRACKED_BITS> bit_trans;
    BitTransMatrix sig_trans;
    SpectralStats spectral;
    uint64_t winCnt;
    int width;

    SigThermoAgg() : winCnt(0), width(1) {}
    
    void init(int w) { width = std::min(w, MAX_TRACKED_BITS); }

    void accumulate(const SigThermoFeat& f) {
        sig_trans.merge(f.sig_trans);
        spectral.merge(f.spectral);
        for(int b=0; b<width; b++) bit_trans[b].merge(f.bit_trans[b]);
        winCnt++;
    }

    void merge(const SigThermoAgg& o) {
        sig_trans.merge(o.sig_trans);
        spectral.merge(o.spectral);
        for(int b=0; b<MAX_TRACKED_BITS; b++) bit_trans[b].merge(o.bit_trans[b]);
        winCnt += o.winCnt;
    }
};

} // namespace inv

#endif // THERMO_TYPES_H