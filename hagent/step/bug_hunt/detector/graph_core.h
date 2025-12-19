#ifndef GRAPH_CORE_H
#define GRAPH_CORE_H

#include <vector>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>
#include <iostream>
#include "pair_key.h"
#include "signal_features.h"
#include "score_entry.h"

namespace inv {

struct Cluster {
    int id;
    double mass;
    double peak;
    std::string root;
    std::vector<std::string> members;
};

class CausalGraph {
    // Adjacency: node -> list of (neighbor, weight)
    std::unordered_map<std::string, std::vector<std::pair<std::string, double>>> adj;

public:
    // Phase 1: Build edges based on Dynamic Co-occurrence (Mutual Information)
    // Good for linking rdata <-> wdata (both moving)
    void buildDynamicEdges(const std::unordered_map<PairKey, uint32_t, PairKeyHash>& pairs,
                           const std::unordered_map<std::string, SigAgg>& agg,
                           uint64_t wins) {
        double min_co = std::max(5.0, wins * 0.05); // 5% noise floor
        
        for(const auto& kv : pairs) {
            if(kv.second < min_co) continue;
            const auto& a = kv.first.a;
            const auto& b = kv.first.b;
            
            // Jaccard Weight
            double nA = agg.count(a) ? agg.at(a).toggleWins : 0;
            double nB = agg.count(b) ? agg.at(b).toggleWins : 0;
            double denom = nA + nB - kv.second;
            
            if(denom <= 0) continue;
            double w = (double)kv.second / denom;
            
            if(w > 0.3) { // Strong coupling only
                adj[a].push_back({b, w});
                adj[b].push_back({a, w});
            }
        }
    }

    // Phase 2: The Static-Dynamic Bridge (ASPLOS Logic)
    // Link Stuck signals (mscratch) to Corruption signals (rdata)
    // Criteria: Both must be "VIP Anomalies" (High Score)
    void addStaticDynamicBridges(const std::vector<ScoreEntry>& anomalies) {
        if(anomalies.empty()) return;

        // 1. Determine Adaptive Threshold
        // Signals below this are "Noise" (like mtime) and won't get bridged
        double maxScore = anomalies[0].score;
        double vipThreshold = maxScore * 0.5; 

        std::vector<const ScoreEntry*> vips;
        for(const auto& e : anomalies) {
            if(e.score >= vipThreshold) vips.push_back(&e);
        }

        // 2. Create Bridge Edges
        // Fully connect the VIP club with weak "Co-Anomaly" edges
        // This merges their clusters
        double bridgeWeight = 0.5; 

        for(size_t i = 0; i < vips.size(); ++i) {
            for(size_t j = i + 1; j < vips.size(); ++j) {
                const auto* a = vips[i];
                const auto* b = vips[j];

                // Heuristic: Prefer bridging Static <-> Dynamic
                // But generally, if both are high scoring, they are related.
                bool isBridge = (a->isStatic() && b->isDynamic()) || 
                                (a->isDynamic() && b->isStatic()) ||
                                (a->isStatic() && b->isStatic()); // Linked Stuck bits

                if(isBridge) {
                    adj[a->name].push_back({b->name, bridgeWeight});
                    adj[b->name].push_back({a->name, bridgeWeight});
                }
            }
        }
    }

    // Standard Clustering (BFS/Connected Components)
    std::vector<Cluster> cluster(const std::vector<ScoreEntry>& ranked) {
        std::vector<Cluster> clusters;
        std::unordered_set<std::string> visited;
        std::unordered_set<std::string> domain;
        for(const auto& e : ranked) domain.insert(e.name);

        int cid = 0;
        for(const auto& seed : ranked) {
            if(visited.count(seed.name)) continue;
            
            Cluster c;
            c.id = cid++;
            c.root = seed.name;
            c.peak = seed.score;
            c.mass = 0;
            
            std::vector<std::string> q;
            q.push_back(seed.name);
            visited.insert(seed.name);
            
            size_t head=0;
            while(head < q.size()) {
                std::string u = q[head++];
                
                // Add mass
                auto it = std::find_if(ranked.begin(), ranked.end(), 
                    [&](const ScoreEntry& e){ return e.name == u; });
                if(it != ranked.end()) c.mass += it->score;
                
                c.members.push_back(u);

                if(adj.count(u)) {
                    for(auto& edge : adj.at(u)) {
                        std::string v = edge.first;
                        if(domain.count(v) && !visited.count(v)) {
                            visited.insert(v);
                            q.push_back(v);
                        }
                    }
                }
            }
            clusters.push_back(c);
        }
        std::sort(clusters.begin(), clusters.end(), [](auto& a, auto& b){ return a.mass > b.mass; });
        return clusters;
    }
};

} // namespace inv

#endif // GRAPH_CORE_H
