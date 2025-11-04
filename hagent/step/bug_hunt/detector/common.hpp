#pragma once

#include <bits/stdc++.h>
#include <getopt.h>

using namespace std;

using Str   = string;
using TimeT = uint64_t;

static inline int popc(uint64_t x){ return __builtin_popcountll(x); }
static inline uint64_t rotl(uint64_t v, int s){ return (v<<s)|(v>>(64-s)); }
static inline uint64_t hash64(uint64_t x){
    x ^= rotl(x, 25) ^ rotl(x, 47);  x *= 0x9e6c63d0676a9a99ULL;
    x ^= rotl(x, 23) ^ rotl(x, 51);  x *= 0x9e6d62d06f6a9a95ULL;
    return x ^ (x>>28);
}

Str joinStr(const vector<string>& items, const string& sep=", ");
Str fmtDouble(double v, int precision=4);
Str maskToList(uint64_t mask, int limit=8);

struct SignalMeta{
    int      width = 1;
    uint64_t mask  = ~0ULL;
};

extern unordered_map<Str,SignalMeta> gSignalMeta;
struct ScorerCfg;
void applyWeightSpec(const Str& spec, ScorerCfg& cfg);

struct PairKey{
    Str a,b;
    bool operator==(const PairKey& o)const { return a==o.a && b==o.b; }
};
struct PairKeyHash{
    size_t operator()(const PairKey& p) const{
        return std::hash<Str>()(p.a) ^ (std::hash<Str>()(p.b)<<1);
    }
};

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
        if(z==0) z = 0.5;
        return -1024.0*log(z/1024.0);
    }
};

struct SigWindowFeat{
    uint64_t ups=0, downs=0, toggles=0;
    Bloom1024 flipBloom;
    DistinctSketch distinct;

    uint64_t prev=0;
    bool havePrev=false;

    uint64_t seen1=0;
    uint64_t seen0=0;
    uint64_t changed=0;

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
            if((prev&1ULL)==0 && (v&1ULL)==1) ups++;
            else if((prev&1ULL)==1 && (v&1ULL)==0) downs++;

            uint64_t diff = (prev ^ v) & mask;
            changed |= diff;
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
        return H(double(ups)) + H(double(downs));
    }
};

struct SigAgg{
    uint64_t winCnt=0;
    double   entSum=0.0;
    double   divSum=0.0;
    uint64_t stable0_mask=~0ULL;
    uint64_t stable1_mask=~0ULL;
    uint64_t toggleWins=0;
    uint64_t changeMask=0;

    inline void update(const SigWindowFeat& f, uint64_t mask){
        winCnt++;
        entSum += f.transEntropy();
        divSum += f.distinct.estimate();
        stable0_mask &= (~f.seen1) & mask;
        stable1_mask &= (~f.seen0) & mask;
        if(f.toggles) toggleWins++;
        changeMask |= (f.changed & mask);
    }
    double meanEntropy()  const { return winCnt? entSum/double(winCnt) : 0.0; }
    double meanDiversity()const { return winCnt? divSum/double(winCnt) : 0.0; }
};

enum class WindowMode{EVENTS,TIME,RETIRE};
struct WindowPolicy{
    WindowMode mode=WindowMode::EVENTS;
    uint64_t   eventsN=50000;
    uint64_t   timeN=0;
    Str        retireSig;
};

class WindowManager{
    WindowPolicy pol_;
    uint64_t evCnt_=0;
    TimeT    nextT_=0;
public:
    WindowManager(const WindowPolicy& p):pol_(p){
        if(pol_.mode==WindowMode::TIME) nextT_=pol_.timeN;
    }
    bool shouldRotateEvent();
    bool shouldRotateTime(TimeT t);
    bool shouldRotateRetire(const Str& sig);
    void resetEvent(){ evCnt_=0; }
};

struct VarInfo{ Str name; int width; };
class VcdStream{
    ifstream ifs;
    unordered_map<Str,VarInfo> id2var;
    unordered_map<Str,uint64_t> nameMask;

    WindowManager &wm;
    unordered_map<Str, SigWindowFeat> curWin;
    unordered_map<Str, SigAgg> &agg;
    unordered_map<PairKey,uint32_t,PairKeyHash> &pairs;
    uint64_t &globalWinCnt;
    uint64_t maxPairsPerWindow;
public:
    VcdStream(const Str& path, WindowManager& w,
              unordered_map<Str,SigAgg>& a,
              unordered_map<PairKey,uint32_t,PairKeyHash>& p,
              uint64_t &gwCnt,
              uint64_t maxPairs);
    void parse();
private:
    void parseHeader();
    void rotate();
    void onValue(const Str& sig, uint64_t v, uint64_t mask);
};

struct ScoreEntry{
    Str name;
    double score=0.0;
    double dH=0.0,dDiv=0.0,mi=0.0;
    double bitNovel=0.0, bitNovelNorm=0.0;
    double pat=0.0;
    double sf=0.0, sfNorm=0.0;
    double newToggle=0.0, newToggleNorm=0.0;
    double missToggle=0.0, missToggleNorm=0.0;
    double width=1.0;
    uint64_t novelMask=0;
    uint64_t newMask=0;
    uint64_t missMask=0;
};
struct ScorerCfg{
    bool mi=true,entropy=true,div=true,bloom=true;
    int  topKpairs=16;
    double wEntropy=2.0;
    double wDiversity=1.5;
    double wMI=10.0;
    double wBitNovel=60.0;
    double wStableFlip=60.0;
    double wNewToggle=55.0;
    double wMissingToggle=55.0;
    double wPattern=8.0;
    double widthReference=32.0;
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
           uint64_t pw,uint64_t fw,const ScorerCfg& c);
    vector<ScoreEntry> run(double cutoff,int topk);
private:
    static uint64_t simhash(double a,double b);
    static double calcMI(double n11,double n1,double n2,double N);
};

bool isSeq(const Str& n);
Str deriveGroup(const Str& n);
