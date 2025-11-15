#include "common.hpp"

Scorer::Scorer(const unordered_map<Str,SigAgg>& pa,
               const unordered_map<Str,SigAgg>& fa,
               const unordered_map<PairKey,uint32_t,PairKeyHash>& pp,
               const unordered_map<PairKey,uint32_t,PairKeyHash>& fp,
               uint64_t pw,uint64_t fw,const ScorerCfg& c)
    :pass(pa),fail(fa),passPair(pp),failPair(fp),passWins(pw),failWins(fw),cfg(c){}

vector<ScoreEntry> Scorer::run(double cutoff,int topk){
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
        uint64_t p_st0 = pp? pp->stable0_mask : 0ULL;
        uint64_t p_st1 = pp? pp->stable1_mask : 0ULL;
        uint64_t f_st0 = ff.stable0_mask;
        uint64_t f_st1 = ff.stable1_mask;
        uint64_t was_stable = p_st0 | p_st1;
        uint64_t now_unstable = ~(f_st0 | f_st1);
        uint64_t novel = was_stable & now_unstable;
        bitNovel = double(popc(novel));

        uint64_t pHash = pp? simhash(pp->meanEntropy(),pp->meanDiversity()):0;
        uint64_t fHash = simhash(ff.meanEntropy(),ff.meanDiversity());
        pat = double(popc(pHash^fHash))/64.0;

        double S = 2.0*dH + 1.5*dDiv + 2.5*mi + 3.0*bitNovel + 1.0*pat;
        if(S<cutoff) continue;
        out.push_back({s,S,dH,dDiv,mi,bitNovel,pat});
    }
    stable_sort(out.begin(),out.end(),[](auto&a,auto&b){
        if(a.score!=b.score) return a.score>b.score;
        return a.name<b.name;
    });
    if(topk>0 && (int)out.size()>topk) out.resize(topk);
    return out;
}

uint64_t Scorer::simhash(double a,double b){
    int bal[64]={};
    uint64_t x; memcpy(&x,&a,sizeof(a)); for(int i=0;i<64;i++) bal[i]+=(x>>i)&1?1:-1;
    memcpy(&x,&b,sizeof(b));            for(int i=0;i<64;i++) bal[i]+=(x>>i)&1?1:-1;
    uint64_t h=0; for(int i=0;i<64;i++) if(bal[i]>=0) h|=1ULL<<i; return h;
}

double Scorer::calcMI(double n11,double n1,double n2,double N){
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
