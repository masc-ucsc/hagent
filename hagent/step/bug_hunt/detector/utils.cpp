#include "common.hpp"

int popc(uint64_t x){ return __builtin_popcountll(x); }
uint64_t rotl(uint64_t v, int s){ return (v<<s)|(v>>(64-s)); }
uint64_t hash64(uint64_t x){
    x ^= rotl(x, 25) ^ rotl(x, 47);  x *= 0x9e6c63d0676a9a99ULL;
    x ^= rotl(x, 23) ^ rotl(x, 51);  x *= 0x9e6d62d06f6a9a95ULL;
    return x ^ (x>>28);
}

static const vector<Str> kSeqKeys={"_q", ".q", "_regq", "_dq"};

bool isSeq(const Str& n){
    for(auto &k:kSeqKeys){
        if(n.size()>=k.size() && n.rfind(k)==n.size()-k.size()) return true;
    }
    return false;
}

Str deriveGroup(const Str& n){
    size_t p=n.find_last_of("._");
    if(p==Str::npos) return n;
    return n.substr(0,p);
}
