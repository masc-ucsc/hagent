#ifndef VCD_STREAM_H
#define VCD_STREAM_H

#include <iostream>
#include <fstream>
#include <sstream>
#include <unordered_map>
#include <algorithm>
#include "invariance_types.h"
#include "window_manager.h"
#include "signal_features.h"
#include "pair_key.h"

namespace inv {

struct VarInfo { Str name; int width; };

class VcdStream {
    std::ifstream ifs;
    std::unordered_map<Str, VarInfo> id2var;
    std::unordered_map<Str, uint64_t> nameMask;
    std::unordered_map<Str, int> nameWidth;
    WindowManager& wm;
    std::unordered_map<Str, SigWindowFeat> curWin;
    std::unordered_map<Str, SigAgg>& agg;
    std::unordered_map<PairKey, uint32_t, PairKeyHash>& pairs;
    uint64_t& globalWinCnt;
    uint64_t maxPairs;
    TimeT curT = 0;

public:
    VcdStream(const Str& path, WindowManager& w,
              std::unordered_map<Str, SigAgg>& a,
              std::unordered_map<PairKey, uint32_t, PairKeyHash>& p,
              uint64_t& gw, uint64_t mp)
    : ifs(path), wm(w), agg(a), pairs(p), globalWinCnt(gw), maxPairs(mp) {
        if(!ifs) throw std::runtime_error("Open failed: " + path);
        parseHeader();
    }

    void parse() {
        Str line;
        while(std::getline(ifs, line)) {
            if(line.empty()) continue;
            if(line[0]=='#') {
                curT = std::strtoull(line.c_str()+1, nullptr, 10);
                if(wm.shouldRotateTime(curT)) rotate();
                continue;
            }
            char c = line[0];
            if(c=='0'||c=='1') {
                Str id = line.substr(1);
                processVal(id, (c=='1'?1ULL:0ULL));
            } else if (c=='b'||c=='B'||c=='r'||c=='R') {
                std::stringstream ss(line);
                Str val, id; ss>>val>>id;
                if(val.find('x')!=Str::npos || val.find('z')!=Str::npos) continue;
                uint64_t v = std::strtoull(val.c_str()+1, nullptr, 2); 
                processVal(id, v);
            }
        }
        if(!curWin.empty()) rotate();
    }

private:
    void processVal(const Str& id, uint64_t v) {
        auto it = id2var.find(id);
        if(it == id2var.end()) return;
        const Str& nm = it->second.name;
        
        // On-demand init
        if(curWin.find(nm) == curWin.end()) {
            curWin[nm].initWidth(nameWidth[nm]);
        }
        curWin[nm].see(v, nameMask[nm], curT);
        if(wm.shouldRotateEvent() || wm.shouldRotateRetire(nm)) rotate();
    }

    void parseHeader() {
        Str line;
        while(std::getline(ifs, line)) {
            if(line.find("$enddefinitions")!=Str::npos) break;
            if(line.find("$var")!=Str::npos) {
                std::stringstream ss(line);
                Str t, k, id, nm; int w;
                ss>>t>>k>>w>>id;
                while(ss>>t && t!="$end") { if(!nm.empty()) nm+=" "; nm+=t; }
                id2var[id] = {nm, w};
                uint64_t mask = (w>=64) ? ~0ULL : ((1ULL<<w)-1ULL);
                nameMask[nm] = mask;
                nameWidth[nm] = w;
            }
        }
    }

    void rotate() {
        globalWinCnt++;
        std::vector<Str> active; 
        for(auto& kv : curWin) {
            const Str& s = kv.first;
            auto& f = kv.second;
            if(agg[s].winCnt == 0) agg[s].initWidth(f.sigWidth);
            agg[s].update(f, nameMask[s]);
            if(f.toggles) active.push_back(s);
        }
        std::sort(active.begin(), active.end());
        size_t M = active.size();
        if(M > 1) {
            size_t cap = std::min<size_t>(M*(M-1)/2, maxPairs);
            size_t emit = 0;
            for(size_t i=0; i<M && emit<cap; i++) {
                for(size_t j=i+1; j<M && emit<cap; j++) {
                    pairs[{active[i], active[j]}]++;
                    emit++;
                }
            }
        }
        curWin.clear();
        wm.resetEvent();
    }
};

} // namespace inv

#endif // VCD_STREAM_H
