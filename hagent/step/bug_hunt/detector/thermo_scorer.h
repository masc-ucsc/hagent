#ifndef THERMO_SCORER_H
#define THERMO_SCORER_H

#include "thermo_types.h"
#include "signal_features.h"
#include <cmath>
#include <algorithm>
#include <vector>

namespace inv {

inline double kl_div(const double P[4], const double Q[4]) {
    double sum = 0;
    for(int i=0; i<4; i++) {
        if(P[i] > 1e-9) {
            sum += P[i] * std::log2(P[i] / std::max(Q[i], 1e-9));
        }
    }
    return sum;
}

inline double js_div(const BitTransMatrix& a, const BitTransMatrix& b) {
    if(a.total()==0 && b.total()==0) return 0.0;
    double P[4], Q[4], M[4];
    a.get_probs(P); b.get_probs(Q);
    for(int i=0; i<4; i++) M[i] = 0.5*(P[i]+Q[i]);
    return 0.5*kl_div(P,M) + 0.5*kl_div(Q,M);
}

struct TIPResult {
    double tds; // Transition
    double sas; // Spectral
    double maxBit;
    int anomBits;
};

inline TIPResult compute_tip(const SigThermoAgg& pass, const SigThermoAgg& fail, int width) {
    TIPResult r = {0,0,0,0};
    
    // 1. Bitwise Physics
    double sumDiv = 0;
    std::vector<double> divs;
    for(int i=0; i<width; i++) {
        double d = js_div(pass.bit_trans[i], fail.bit_trans[i]);
        if(d > r.maxBit) r.maxBit = d;
        if(d > 0.1) r.anomBits++;
        sumDiv += d;
        divs.push_back(d);
    }
    
    // Top-K weighting for multi-bit buses
    std::sort(divs.begin(), divs.end(), std::greater<double>());
    double topK = 0;
    int k = std::min((int)divs.size(), 3);
    for(int i=0; i<k; i++) topK += divs[i];
    if(k>0) topK /= k;

    // 2. Signal Activity Pattern
    double sigDiv = js_div(pass.sig_trans, fail.sig_trans);

    // TDS = Weighted mix of Structural (Bit) and Temporal (Signal) divergence
    r.tds = 0.3*sigDiv + 0.4*r.maxBit + 0.3*topK;

    // 3. Spectral (Jitter)
    double pVar = pass.spectral.variance();
    double fVar = fail.spectral.variance();
    constexpr double eps = 1e-9;
    r.sas = std::abs(std::log(fVar+eps) - std::log(pVar+eps));
    r.sas = std::min(r.sas/10.0, 1.0); // Normalize

    return r;
}

} // namespace inv

#endif // THERMO_SCORER_H
