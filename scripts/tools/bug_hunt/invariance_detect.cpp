// invariance_detect.cpp
//
//   g++ -std=c++17 -O2 -pipe invariance_detect.cpp -o invariance_detect
//
// -----------------------------------------------------------------------------
// Quick-start
//   ./invariance_detect                                  \
//        --pass_vcd good1.vcd --pass_vcd good2.vcd       \
//        --fail_vcd bad.vcd                              \
//        --checkpoint_retire_signal retire_q             \
//        --topk 50 --topk_pairs 16                       \
//        --window_events 50000                           \
//        --out results.txt
//
//   run ./invariance_detect --help   for the full option list.
// -----------------------------------------------------------------------------

#include <bits/stdc++.h>
#include <getopt.h>
using namespace std;

// -----------------------------------------------------------------------------
// Helpers / small utils
// -----------------------------------------------------------------------------
using Str    = string;
using TimeT  = uint64_t;
static inline int popc(uint64_t x){ return __builtin_popcountll(x); }
static inline uint64_t rotl(uint64_t v, int s){ return (v<<s)|(v>>(64-s)); }
static uint64_t hash64(uint64_t x){
    x ^= rotl(x, 25) ^ rotl(x, 47);  x *= 0x9e6c63d0676a9a99ULL;
    x ^= rotl(x, 23) ^ rotl(x, 51);  x *= 0x9e6d62d06f6a9a95ULL;
    return x ^ (x>>28);
}
// A simple pair key (ordered) for ][unordered_map.
struct PairKey{
    Str a,b;
    bool operator==(const PairKey& o)const { return a==o.a && b==o.b; }
};
struct PairKeyHash{
    size_t operator()(const PairKey& p) const{
        return std::hash<Str>()(p.a) ^ (std::hash<Str>()(p.b)<<1);
    }
};

// -----------------------------------------------------------------------------
// Sketches (bloom, distinct)
// -----------------------------------------------------------------------------
struct Bloom1024{
    std::bitset<1024> bits;
    void add(uint64_t v){
        for(int i=0;i<3;i++){
            uint64_t h=hash64(v+i);
            bits.set(h & 1023);
        }
    }
    int count() const { return bits.count(); }
};
struct DistinctSketch{
    std::bitset<1024> bits;
    void add(uint64_t v){ bits.set(hash64(v)&1023); }
    double estimate() const{
        double z = 1024 - bits.count();
        if(z==0) z = 0.5;            // saturate
        return -1024.0*log(z/1024.0);
    }
};

// -----------------------------------------------------------------------------
// Per-window per-signal feature collector
// -----------------------------------------------------------------------------
struct SigWindowFeat{
    uint64_t ups=0, downs=0, toggles=0;
    Bloom1024 flipBloom;
    DistinctSketch distinct;

    uint64_t prev=0;
    bool havePrev=false;

    // per-window bit evidence
    uint64_t seen1=0;          // bits that were ever 1 (masked)
    uint64_t seen0=0;          // bits that were ever 0 (masked)
    uint64_t changed=0;        // union of (prev ^ v) over the window

    inline void see(uint64_t v, uint64_t mask){
        v &= mask;
        if(!havePrev){
            havePrev   = true;
            prev       = v;
            distinct.add(v);
            seen1     |= v;
            seen0     |= (~v) & mask;
            return;
        }
        if(v!=prev){
            toggles++;
            // direction only meaningful for 1-bit; harmless otherwise
            if((prev&1ULL)==0 && (v&1ULL)==1) ups++;
            else if((prev&1ULL)==1 && (v&1ULL)==0) downs++;

            uint64_t diff = (prev ^ v) & mask;
            changed |= diff;
            // bloom per-bit flip footprint
            while(diff){
                uint64_t bit = __builtin_ctzll(diff);
                flipBloom.add(bit);
                diff &= diff-1;
            }
            prev = v;
        }
        distinct.add(v);
        seen1 |= v;
        seen0 |= (~v) & mask;
    }

    double transEntropy() const{
        if(toggles==0) return 0.0;
        auto H=[&](double x){
            if(x<=0.0) return 0.0;
            double p = x / double(toggles);
            return -p*log2(p);
        };
        // binary up/down entropy (order-free)
        return H(double(ups)) + H(double(downs));
    }
};

// -----------------------------------------------------------------------------
// Aggregated (multi-window) statistics per signal
// -----------------------------------------------------------------------------
struct SigAgg{
    uint64_t winCnt=0;
    double   entSum=0.0;          // Σ window entropies
    double   divSum=0.0;          // Σ window distinct estimates
    uint64_t stable0_mask=~0ULL;  // bits proven "always 0" across all seen windows
    uint64_t stable1_mask=~0ULL;  // bits proven "always 1" across all seen windows
    uint64_t toggleWins=0;        // number of windows with ≥1 toggle

    inline void update(const SigWindowFeat& f, uint64_t mask){
        winCnt++;
        entSum += f.transEntropy();
        divSum += f.distinct.estimate();
        // A bit can remain "always 0" only if it was never seen 1 in this window
        // A bit can remain "always 1" only if it was never seen 0 in this window
        stable0_mask &= (~f.seen1) & mask;
        stable1_mask &= (~f.seen0) & mask;
        if(f.toggles) toggleWins++;
    }
    double meanEntropy()  const { return winCnt? entSum/double(winCnt) : 0.0; }
    double meanDiversity()const { return winCnt? divSum/double(winCnt) : 0.0; }
};

// -----------------------------------------------------------------------------
// Streaming window manager
// -----------------------------------------------------------------------------
enum class WindowMode{EVENTS,TIME,RETIRE};
struct WindowPolicy{
    WindowMode mode=WindowMode::EVENTS;
    uint64_t   eventsN=50000;          // --window_events
    uint64_t   timeN=0;                // --window_time
    Str        retireSig;              // --checkpoint_retire_signal
};

class WindowManager{
    WindowPolicy pol_;
    uint64_t evCnt_=0;
    TimeT    nextT_=0;
public:
    WindowManager(const WindowPolicy& p):pol_(p){
        if(pol_.mode==WindowMode::TIME) nextT_=pol_.timeN;
    }
    bool shouldRotateEvent() {
        if(pol_.mode!=WindowMode::EVENTS) return false;
        return (++evCnt_ >= pol_.eventsN);
    }
    bool shouldRotateTime(TimeT t){
        if(pol_.mode!=WindowMode::TIME) return false;
        if(t>=nextT_){ nextT_+=pol_.timeN; return true; }
        return false;
    }
    bool shouldRotateRetire(const Str& sig){
        return (pol_.mode==WindowMode::RETIRE && !pol_.retireSig.empty() && sig==pol_.retireSig);
    }
    void resetEvent(){ evCnt_=0; }
};

// -----------------------------------------------------------------------------
// VCD parser (single-pass streaming, O(signals) memory)
// -----------------------------------------------------------------------------
struct VarInfo{ Str name; int width; };
class VcdStream{
    ifstream ifs;
    unordered_map<Str,VarInfo> id2var;
    unordered_map<Str,uint64_t> nameMask;   // signal name -> bit mask from width

    WindowManager &wm;
    unordered_map<Str, SigWindowFeat> curWin;   // live per-signal state
    unordered_map<Str, SigAgg> &agg;
    unordered_map<PairKey,uint32_t,PairKeyHash> &pairs;
    uint64_t &globalWinCnt;
    uint64_t maxPairsPerWindow;
public:
    VcdStream(const Str& path, WindowManager& w,
              unordered_map<Str,SigAgg>& a,
              unordered_map<PairKey,uint32_t,PairKeyHash>& p,
              uint64_t &gwCnt,
              uint64_t maxPairs)
    :ifs(path),wm(w),agg(a),pairs(p),globalWinCnt(gwCnt),maxPairsPerWindow(maxPairs){
        if(!ifs) throw runtime_error("open "+path);
        parseHeader();
    }

    void parse(){
        Str line;
        TimeT curT=0;
        while(getline(ifs,line)){
            if(line.empty()) continue;
            if(line[0]=='#'){
                curT = strtoull(line.c_str()+1,nullptr,10);
                if(wm.shouldRotateTime(curT)) rotate();
                continue;
            }
            char c=line[0];
            if(c=='0'||c=='1'){ // scalar
                Str id=line.substr(1);
                auto it=id2var.find(id);
                if(it==id2var.end()) continue;
                const Str &nm = it->second.name;
                uint64_t mask = nameMask[nm];
                uint64_t v    = (c=='1') ? 1ULL : 0ULL;
                onValue(nm,v,mask);
                if(wm.shouldRotateRetire(nm)) rotate();
            }else if(c=='b'||c=='B'||c=='r'||c=='d'||c=='h'||c=='H'){
                Str val,id;
                { stringstream ss(line); ss>>val>>id; }
                auto it=id2var.find(id);
                if(it==id2var.end()) continue;
                const Str &nm = it->second.name;
                uint64_t mask = nameMask[nm];
                if(val.find('x')!=Str::npos||val.find('z')!=Str::npos) continue; // mask x/z
                uint64_t v=0;
                char fmt=tolower(val[0]);
                Str num=val.substr(1);
                if(fmt=='b'){ v=strtoull(num.c_str(),nullptr,2); }
                else if(fmt=='d'||fmt=='r'){ v=strtoull(num.c_str(),nullptr,10); }
                else if(fmt=='h'){ v=strtoull(num.c_str(),nullptr,16); }
                onValue(nm,v,mask);
                if(wm.shouldRotateRetire(nm)) rotate();
            }
        }
        if(!curWin.empty()) rotate(); // flush
    }

private:
    //------------------------------------------------------------------
    void parseHeader(){
        Str line;
        while(getline(ifs,line)){
            if(line.find("$enddefinitions")!=Str::npos) break;
            if(line.find("$var")!=Str::npos){
                stringstream ss(line);
                Str tok, typ, id, name; int width=1;
                ss>>tok>>typ>>width>>id;
                while(ss>>tok && tok!="$end"){ if(!name.empty()) name+=' '; name+=tok; }
                id2var[id]={name,width};
                uint64_t mask = (width>=64) ? ~0ULL : ((width<=0)?0ULL:((1ULL<<width)-1ULL));
                nameMask[name]=mask;
            }
        }
    }
    //------------------------------------------------------------------
    void rotate(){
        globalWinCnt++;

        // deterministic active set
        vector<Str> active; active.reserve(curWin.size());
        for(auto &kv:curWin){
            const Str& s = kv.first;
            const auto& f= kv.second;
            uint64_t mask = nameMask.count(s)? nameMask[s] : ~0ULL;
            agg[s].update(f, mask);
            if(f.toggles) active.push_back(s);
        }
        sort(active.begin(), active.end()); // make pair selection deterministic

        // cap pair enumeration
        const size_t M = active.size();
        if(M>1){
            size_t emitted=0, cap = min<uint64_t>((M*(M-1))/2, maxPairsPerWindow);
            for(size_t i=0;i<M && emitted<cap;i++){
                for(size_t j=i+1;j<M && emitted<cap;j++){
                    PairKey k{active[i],active[j]};
                    pairs[k]++;
                    emitted++;
                }
            }
        }

        curWin.clear();
        wm.resetEvent();
    }
    //------------------------------------------------------------------
    inline void onValue(const Str& sig, uint64_t v, uint64_t mask){
        auto &s = curWin[sig];
        s.see(v, mask);
        if(wm.shouldRotateEvent()) rotate();
    }
};

// -----------------------------------------------------------------------------
// Score synthesizer
// -----------------------------------------------------------------------------
struct ScoreEntry{
    Str name;
    double score;
    double dH,dDiv,mi,bitNovel,pat,sf;
};
struct ScorerCfg{
    bool mi=true,entropy=true,div=true,bloom=true;
    int  topKpairs=16;
};
class Scorer{
    const unordered_map<Str,SigAgg>& pass;
    const unordered_map<Str,SigAgg>& fail;
    const unordered_map<PairKey,uint32_t,PairKeyHash>& passPair;
    const unordered_map<PairKey,uint32_t,PairKeyHash>& failPair;
    uint64_t passWins,failWins;
    ScorerCfg cfg;
public:
    Scorer(const unordered_map<Str,SigAgg>& pa,
           const unordered_map<Str,SigAgg>& fa,
           const unordered_map<PairKey,uint32_t,PairKeyHash>& pp,
           const unordered_map<PairKey,uint32_t,PairKeyHash>& fp,
           uint64_t pw,uint64_t fw,const ScorerCfg& c):pass(pa),fail(fa),passPair(pp),failPair(fp),passWins(pw),failWins(fw),cfg(c){}
           vector<ScoreEntry> run(double cutoff,int topk){
               vector<ScoreEntry> out;
               out.reserve(fail.size());
               for(auto &kv:fail){
                   const Str& s=kv.first;
                   const SigAgg& ff=kv.second;
                   const SigAgg* pp = pass.count(s)? &pass.at(s): nullptr;
                   double dH=0,dDiv=0,mi=0,bitNovel=0,pat=0;
                   if(cfg.entropy){
                       double fH=ff.meanEntropy();
                       double pH=pp?pp->meanEntropy():0;
                       dH = max(0.0, fH-pH);
                   }
                   if(cfg.div){
                       double fD=ff.meanDiversity();
                       double pD=pp?pp->meanDiversity():0;
                       dDiv=max(0.0,fD-pD);
                   }
                   if(cfg.mi){
                       // gather pairs containing s
                       vector<double> deltas;
                       deltas.reserve(32);
                       for(auto &mp:failPair){
                           if(mp.first.a!=s && mp.first.b!=s) continue;
                           uint32_t f11=mp.second;
                           uint32_t p11=0;
                           auto it=passPair.find(mp.first);
                           if(it!=passPair.end()) p11=it->second;
                           double f1 = ff.toggleWins;
                           double p1 = pp?pp->toggleWins:0;
                           const Str& other = (mp.first.a==s)? mp.first.b : mp.first.a;
                           double f2 = 0, p2 = 0;
                           auto itF = fail.find(other); if(itF!=fail.end()) f2 = itF->second.toggleWins;
                           auto itP = pass.find(other); if(itP!=pass.end()) p2 = itP->second.toggleWins;
                           double fMI = calcMI(f11,f1,f2,failWins);
                           double pMI = calcMI(p11,p1,p2,passWins);
                           deltas.push_back(max(0.0,fMI-pMI));
                       }
                       sort(deltas.begin(),deltas.end(),greater<double>());
                       for(int i=0;i<cfg.topKpairs && i<(int)deltas.size();i++) mi+=deltas[i];
                   }
                   // bit novel: bits stable in pass (always-0 or always-1) that became unstable in fail
                   uint64_t p_st0 = pp? pp->stable0_mask : 0ULL;
                   uint64_t p_st1 = pp? pp->stable1_mask : 0ULL;
                   uint64_t f_st0 = ff.stable0_mask;
                   uint64_t f_st1 = ff.stable1_mask;
                   uint64_t was_stable = p_st0 | p_st1;
                   uint64_t now_unstable = ~(f_st0 | f_st1);
                   uint64_t novel = was_stable & now_unstable;
                   bitNovel = double(popc(novel));

                   // NEW: StableFlip (pass-stable polarity -> fail-stable opposite)
                   uint64_t pass_zero = p_st0 & ~p_st1;
                   uint64_t pass_one  = p_st1 & ~p_st0;
                   uint64_t fail_zero = f_st0 & ~f_st1;
                   uint64_t fail_one  = f_st1 & ~f_st0;
                   double StableFlip   = double(popc( (pass_zero & fail_one) | (pass_one & fail_zero) ));

                   // pattern distance via simple simhash over (ent,div)
                   uint64_t pHash = pp? simhash(pp->meanEntropy(),pp->meanDiversity()):0;
                   uint64_t fHash = simhash(ff.meanEntropy(),ff.meanDiversity());
                   pat = double(popc(pHash^fHash))/64.0;

                   double S = 2.0*dH + 1.5*dDiv + 2.5*mi + 3.0*bitNovel + 1.0*pat + 3.0*StableFlip;
                   if(S<cutoff) continue;
                   out.push_back({s,S,dH,dDiv,mi,bitNovel,pat,StableFlip});
               }
               stable_sort(out.begin(),out.end(),[](auto&a,auto&b){
                   if(a.score!=b.score) return a.score>b.score;
                   return a.name<b.name;
               });
               if(topk>0 && (int)out.size()>topk) out.resize(topk);
               return out;
           }
private:
    static uint64_t simhash(double a,double b){
        int bal[64]={};
        uint64_t x; memcpy(&x,&a,sizeof(a)); for(int i=0;i<64;i++) bal[i]+=(x>>i)&1?1:-1;
        memcpy(&x,&b,sizeof(b));            for(int i=0;i<64;i++) bal[i]+=(x>>i)&1?1:-1;
        uint64_t h=0; for(int i=0;i<64;i++) if(bal[i]>=0) h|=1ULL<<i; return h;
    }
    static double calcMI(double n11,double n1,double n2,double N){
        // 2x2 table with add-one smoothing
        double a = n11 + 1.0;
        double b = (n1 - n11) + 1.0;
        double c = (n2 - n11) + 1.0;
        double d = (N - n1 - n2 + n11) + 1.0;
        double T = a+b+c+d;
        double p11=a/T, p1=(a+b)/T, p2=(a+c)/T;
        double denom = p1*p2;
        if(denom<=0.0) return 0.0;
        return p11 * log2(p11/denom);
    }
};

// -----------------------------------------------------------------------------
// Grouping by flop boundaries (heuristic)
// -----------------------------------------------------------------------------
static bool isSeq(const Str& n){
    static const vector<Str> keys={"_q", ".q", "_regq", "_dq"};
    for(auto &k:keys) if(n.size()>=k.size() && n.rfind(k)==n.size()-k.size()) return true;
    return false;
}
static Str deriveGroup(const Str& n){
    size_t p=n.find_last_of("._");
    if(p==Str::npos) return n;
    return n.substr(0,p);
}

// -----------------------------------------------------------------------------
// CLI / main
// -----------------------------------------------------------------------------
int main(int argc,char**argv){
    vector<Str> passFiles, failFiles;
    Str outPath;
    WindowPolicy wpol;
    wpol.eventsN=50000;
    bool groupByFlop=true, ignoreCombOnly=false;
    int  topk=100;
    int  topkPairs=16;
    uint64_t maxPairsPerWin=128;
    double scoreCutoff=0.1;
    ScorerCfg scorerCfg;
    // -------------------------------------------------------------------------
    static struct option opts[]{
        {"pass_vcd", required_argument,0,'P'},
        {"fail_vcd", required_argument,0,'F'},
        {"out",      required_argument,0,'o'},
        {"window_events", required_argument,0,'e'},
        {"window_time",   required_argument,0,'t'},
        {"checkpoint_retire_signal", required_argument,0,'r'},
        {"group_by_flop", no_argument,0,'g'},
        {"ignore_comb_only",no_argument,0,'I'},
        {"topk", required_argument,0,'k'},
        {"topk_pairs", required_argument,0,'K'},
        {"max_pairs_per_window",required_argument,0,'M'},
        {"score_cutoff", required_argument,0,'c'},
        {"no_mi", no_argument,0,1},
        {"no_entropy", no_argument,0,2},
        {"no_diversity",no_argument,0,3},
        {"no_bloom", no_argument,0,4},
        {"help",    no_argument,0,'h'},
        {0,0,0,0}};
        int idx,c;
        while((c=getopt_long(argc,argv,"P:F:o:e:t:r:k:K:M:c:ghI",opts,&idx))!=-1){
            switch(c){
                case 'P': passFiles.push_back(optarg); break;
                case 'F': failFiles.push_back(optarg); break;
                case 'o': outPath=optarg; break;
                case 'e': wpol.mode=WindowMode::EVENTS; wpol.eventsN=stoull(optarg); break;
                case 't': wpol.mode=WindowMode::TIME;   wpol.timeN =stoull(optarg); break;
                case 'r': wpol.mode=WindowMode::RETIRE; wpol.retireSig=optarg; break;
                case 'g': groupByFlop=true; break;
                case 'I': ignoreCombOnly=true; break;
                case 'k': topk=stoi(optarg); break;
                case 'K': topkPairs=stoi(optarg); break;
                case 'M': maxPairsPerWin=stoull(optarg); break;
                case 'c': scoreCutoff=stod(optarg); break;
                case 1: scorerCfg.mi=false; break;
                case 2: scorerCfg.entropy=false; break;
                case 3: scorerCfg.div=false; break;
                case 4: scorerCfg.bloom=false; break;
                case 'h':
                default:
                    cerr<<"Usage: invariance_detect [options]\n"
                    <<"  --pass_vcd <file> (repeatable)\n"
                    <<"  --fail_vcd <file> (repeatable)\n"
                    <<"  --out <file>\n"
                    <<"  --window_events N     (default 50000)\n"
                    <<"  --window_time   N     (VCD ticks)\n"
                    <<"  --checkpoint_retire_signal SIG\n"
                    <<"  --group_by_flop / --ignore_comb_only\n"
                    <<"  --topk K              final report lines (default 100)\n"
                    <<"  --topk_pairs N        MI top-K (default 16)\n"
                    <<"  --max_pairs_per_window N (default 128)\n"
                    <<"  --score_cutoff D      (default 0.1)\n"
                    <<"  --no_mi / --no_entropy / --no_diversity / --no_bloom\n";
                    return 0;
            }
        }
        if(passFiles.empty()||failFiles.empty()){
            cerr<<"ERROR: need at least one --pass_vcd and one --fail_vcd\n"; return 1;
        }
        scorerCfg.topKpairs=topkPairs;

        ostream *out=&cout; ofstream ofs;
        if(!outPath.empty()){ ofs.open(outPath); if(!ofs){cerr<<"open "<<outPath<<" failed\n";return 1;} out=&ofs; }

        unordered_map<Str,SigAgg> passAgg, failAgg;
        unordered_map<PairKey,uint32_t,PairKeyHash> passPair, failPair;
        uint64_t passWinCnt=0, failWinCnt=0;

        // -------------------------------------------------------------------------
        // PASS parsing
        // -------------------------------------------------------------------------
        cerr<<"[PASS] windows …\n";
        for(auto &f:passFiles){
            cerr<<"  "<<f<<"\n";
            WindowManager wm(wpol);
            VcdStream vs(f,wm,passAgg,passPair,passWinCnt,/*maxPairsPerWin*/maxPairsPerWin);
            vs.parse();
        }
        // -------------------------------------------------------------------------
        // FAIL parsing
        // -------------------------------------------------------------------------
        cerr<<"[FAIL] windows …\n";
        for(auto &f:failFiles){
            cerr<<"  "<<f<<"\n";
            WindowManager wm(wpol);
            VcdStream vs(f,wm,failAgg,failPair,failWinCnt,/*maxPairsPerWin*/maxPairsPerWin);
            vs.parse();
        }

        // -------------------------------------------------------------------------
        // Per-net scoring
        // -------------------------------------------------------------------------
        Scorer scorer(passAgg,failAgg,passPair,failPair,passWinCnt,failWinCnt,scorerCfg);
        auto ranked=scorer.run(scoreCutoff,topk);

        // -------------------------------------------------------------------------
        // Optional grouping
        // -------------------------------------------------------------------------
        unordered_map<Str,vector<ScoreEntry>> groups;
        unordered_map<Str,bool> groupHasSeq;
        if(groupByFlop){
            for(auto &e:ranked){
                Str g=deriveGroup(e.name);
                groups[g].push_back(e);
                if(isSeq(e.name)) groupHasSeq[g]=true;
            }
        }
        vector<pair<Str,double>> groupScores;
        if(groupByFlop){
            for(auto &kv:groups){
                if(ignoreCombOnly && !groupHasSeq[kv.first]) continue;
                double s=0; for(auto &e:kv.second) s=max(s,e.score);
                groupScores.push_back({kv.first,s});
            }
            stable_sort(groupScores.begin(),groupScores.end(),[](auto&a,auto&b){
                if(a.second!=b.second) return a.second>b.second;
                return a.first<b.first;
            });
            if((int)groupScores.size()>topk) groupScores.resize(topk);
        }

        // -------------------------------------------------------------------------
        // Output
        // -------------------------------------------------------------------------
        *out<<"=== Per-Net Anomalies ===\n";
        for(auto &e:ranked){
            *out<<e.name<<" "<<e.score
            <<" (dH="<<e.dH<<",dDiv="<<e.dDiv<<",MI="<<e.mi
            <<",BitNovel="<<e.bitNovel<<",Pat="<<e.pat<<",SF="<<e.sf<<")\n";
        }
        if(groupByFlop){
            *out<<"\n=== Group (Seq-Boundary) Anomalies ===\n";
            for(auto &g:groupScores){
                *out<<g.first<<" "<<g.second<<"\n";
            }
        }
        return 0;
}
