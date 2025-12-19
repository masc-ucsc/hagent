#ifndef SCORER_H
#define SCORER_H

#include "signal_features.h"
#include "thermo_scorer.h"
#include "graph_core.h"
#include "score_entry.h"
#include <iomanip>
#include <cmath>
#include <algorithm>
#include <vector>

namespace inv {

struct ScorerCfg {
    bool enableTip = true;
    double tipAlpha = 4.0;
    double tipBeta = 2.0;
    bool enableCluster = true;
    int topK = 100;
};

class Scorer {
    const std::unordered_map<Str, SigAgg>& pass;
    const std::unordered_map<Str, SigAgg>& fail;
    const std::unordered_map<PairKey, uint32_t, PairKeyHash>& passPair;
    const std::unordered_map<PairKey, uint32_t, PairKeyHash>& failPair;
    uint64_t pWins, fWins;
    ScorerCfg cfg;

public:
    Scorer(const std::unordered_map<Str, SigAgg>& p,
           const std::unordered_map<Str, SigAgg>& f,
           const std::unordered_map<PairKey, uint32_t, PairKeyHash>& pp,
           const std::unordered_map<PairKey, uint32_t, PairKeyHash>& fp,
           uint64_t pw, uint64_t fw, ScorerCfg c)
    : pass(p), fail(f), passPair(pp), failPair(fp), pWins(pw), fWins(fw), cfg(c) {}

    void run(double cutoff, std::ostream& out) {
        std::vector<ScoreEntry> res;
        
        for(auto& kv : fail) {
            const Str& s = kv.first;
            const SigAgg& ff = kv.second;
            const SigAgg* pp = pass.count(s) ? &pass.at(s) : nullptr;

            double dH=0, dDiv=0, mi=0, bitNovel=0, sigNovel=0, pat=0;
            double tds=0, sas=0, maxBit=0; 
            int anomBits=0;

            // --- NORMALIZATION FACTOR ---
            double width = (double)std::max(1, ff.sigWidth);

            if(pp) {
                // 1. Entropy & Diversity Density
                double raw_dH = std::max(0.0, ff.meanEntropy() - pp->meanEntropy());
                dH = raw_dH / width;
                double raw_dDiv = std::max(0.0, ff.meanDiversity() - pp->meanDiversity());
                dDiv = raw_dDiv / width;
                
                // 2. Static Bit Novelty (The "Stuck At" Detector)
                uint64_t pSeen1 = ~pp->stable0_mask;
                uint64_t fSeen1 = ~ff.stable0_mask; 
                double intrusion = (double)popc(fSeen1 & ~pSeen1); 
                double omission  = (double)popc(pSeen1 & ~fSeen1); 
                double raw_novel = (5.0 * intrusion) + (1.0 * omission);
                bitNovel = raw_novel / width;

                // 3. NEW: Behavioral Novelty (The "hwBugHunt" Merge)
                // We compare the SET of signatures seen in Pass vs Fail.
                double sigIntrusion = 0;
                double sigOmission = 0;

                // Intrusion: Signatures in Fail that were NEVER in Pass (Eq 1 in paper)
                for(auto sig : ff.signatures) {
                    if(pp->signatures.find(sig) == pp->signatures.end()) {
                        sigIntrusion += 1.0;
                    }
                }
                
                // Omission: Signatures in Pass that are MISSING in Fail (Eq 4 in paper)
                for(auto sig : pp->signatures) {
                    if(ff.signatures.find(sig) == ff.signatures.end()) {
                        sigOmission += 1.0;
                    }
                }

                // Normalization: Damping by complexity.
                // If a signal has 1000 behaviors in Pass, 1 new one is noise.
                // If it has 1 behavior in Pass, 1 new one is a HUGE event.
                double baselineComplexity = std::max(1.0, (double)pp->signatures.size());
                
                // Weighting: 10x for Intrusion (New Physics), 2x for Omission
                // We weight this heavily because a signature change implies a timing/logic change.
                sigNovel = (10.0 * sigIntrusion + 2.0 * sigOmission) / baselineComplexity;

            } else {
                // New signal entirely?
                bitNovel = 1.0; 
                sigNovel = 1.0;
            }

            if(cfg.enableTip && pp) {
                // Bounds Safe Fix
                int safeWidth = std::min(ff.sigWidth, MAX_TRACKED_BITS);
                auto r = compute_tip(pp->thermo, ff.thermo, safeWidth);
                tds = r.tds;
                sas = r.sas;
                maxBit = r.maxBit;
                anomBits = r.anomBits;
            }

            // --- SCORING EQUATION ---
            // We add 15.0 * sigNovel. This is a strong factor.
            // If the physics changes (sigNovel), it will spike the score.
            double S = 10.0*dH + 5.0*dDiv + 2.5*mi + 20.0*bitNovel + 15.0*sigNovel + 1.0*pat;
            
            if(cfg.enableTip) S += cfg.tipAlpha*tds + cfg.tipBeta*sas;

            if(S >= (cutoff * 0.1)) {
                // Update constructor to include sigNovel
                res.push_back({s, S, dH, dDiv, mi, bitNovel, sigNovel, pat, tds, sas, maxBit, anomBits, ff.sigWidth});
            }
        }

        // --- SCIENTIFIC SORT (MDL) ---
        std::sort(res.begin(), res.end(), [](const ScoreEntry& a, const ScoreEntry& b){ 
            if (std::abs(a.score - b.score) > 1e-4) {
                return a.score > b.score; 
            }
            return a.width < b.width; 
        });

        if(res.size() > cfg.topK) res.resize(cfg.topK);

        out << std::fixed << std::setprecision(4);
        out << "=== Per-Net Anomalies (Hybrid: Bit State + Behavioral Sig) ===\n";
        for(auto& e : res) {
            out << e.name << " " << e.score 
                << " (BitNov=" << e.bitNovel 
                << ", SigNov=" << e.sigNovel // Report the new metric
                << ", TDS=" << e.tds 
                << ", SAS=" << e.sas 
                << ", AnomBits=" << e.anomBits << ")\n";
        }

        if(cfg.enableCluster) {
            out << "\n=== Causal Clusters (Static-Dynamic Bridge) ===\n";
            CausalGraph cg;
            
            cg.buildDynamicEdges(failPair, fail, fWins);
            cg.addStaticDynamicBridges(res);
            
            auto clusters = cg.cluster(res);
            
            for(auto& c : clusters) {
                if(c.mass < 0.1) continue; 
                out << "Cluster " << c.id << " [Mass=" << c.mass << ", Peak=" << c.peak 
                    << "] Root: " << c.root << "\n";
                for(auto& m : c.members) out << "  -> " << m << "\n";
                out << "\n";
            }
        }
    }
};

} // namespace inv

#endif // SCORER_H