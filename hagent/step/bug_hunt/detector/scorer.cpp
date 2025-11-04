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

        ScoreEntry entry;
        entry.name = s;

        if(cfg.entropy){
            double fH=ff.meanEntropy();
            double pH=pp?pp->meanEntropy():0;
            entry.dH = max(0.0, fH-pH);
        }
        if(cfg.div){
            double fD=ff.meanDiversity();
            double pD=pp?pp->meanDiversity():0;
            entry.dDiv=max(0.0,fD-pD);
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
            for(int i=0;i<cfg.topKpairs && i<(int)deltas.size();i++) entry.mi+=deltas[i];
        }

        uint64_t p_st0 = pp? pp->stable0_mask : 0ULL;
        uint64_t p_st1 = pp? pp->stable1_mask : 0ULL;
        uint64_t f_st0 = ff.stable0_mask;
        uint64_t f_st1 = ff.stable1_mask;
        uint64_t was_stable = p_st0 | p_st1;
        uint64_t now_unstable = ~(f_st0 | f_st1);
        uint64_t novel = was_stable & now_unstable;
        entry.novelMask = novel;
        entry.bitNovel  = double(popc(novel));

        uint64_t pass_zero = p_st0 & ~p_st1;
        uint64_t pass_one  = p_st1 & ~p_st0;
        uint64_t fail_zero = f_st0 & ~f_st1;
        uint64_t fail_one  = f_st1 & ~f_st0;
        uint64_t stableFlipMask = (pass_zero & fail_one) | (pass_one & fail_zero);
        entry.sf        = double(popc(stableFlipMask));
        entry.sfNorm    = 0.0;

        uint64_t passChange = pp? pp->changeMask : 0ULL;
        uint64_t failChange = ff.changeMask;
        entry.newMask  = failChange  & ~passChange;
        entry.missMask = passChange  & ~failChange;
        entry.newToggle  = double(popc(entry.newMask));
        entry.missToggle = double(popc(entry.missMask));

        uint64_t pHash = pp? simhash(pp->meanEntropy(),pp->meanDiversity()):0;
        uint64_t fHash = simhash(ff.meanEntropy(),ff.meanDiversity());
        entry.pat = double(popc(pHash^fHash))/64.0;

        auto metaIt = gSignalMeta.find(s);
        double width = (metaIt!=gSignalMeta.end() && metaIt->second.width>0) ? double(metaIt->second.width) : 64.0;
        entry.width = width;
        if(width<=0.0) width = 1.0;

        entry.bitNovelNorm    = entry.bitNovel    / width;
        entry.sfNorm          = entry.sf          / width;
        entry.newToggleNorm   = entry.newToggle   / width;
        entry.missToggleNorm  = entry.missToggle  / width;

        double widthScale = min(1.0, cfg.widthReference / width);
        double score = 0.0;
        if(cfg.entropy) score += cfg.wEntropy * entry.dH;
        if(cfg.div)     score += cfg.wDiversity * entry.dDiv;
        if(cfg.mi)      score += cfg.wMI * entry.mi;
        score += cfg.wPattern * entry.pat;
        double bitScore =
            cfg.wBitNovel * entry.bitNovelNorm +
            cfg.wStableFlip * entry.sfNorm +
            cfg.wNewToggle * entry.newToggleNorm +
            cfg.wMissingToggle * entry.missToggleNorm;
        score += widthScale * bitScore;

        entry.score = score;
        if(entry.score<cutoff) continue;
        out.push_back(entry);
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
