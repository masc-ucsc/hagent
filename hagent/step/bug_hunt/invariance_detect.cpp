// invariance_detect.cpp
//
// Usage example:
//   ./invariance_detect \
//     --pass_vcd pass1.vcd --pass_vcd pass2.vcd \
//     --fail_vcd fail.vcd \
//     --checkpoint_interval 100 \
//     --checkpoint_retire_signal retire_id \
//     --topk 100 --score_cutoff 0.1 \
//     --out results.txt
//
// (See --help for full option list.)

#include <bits/stdc++.h>
#include <getopt.h>
using namespace std;

//------------------------------------------------------------------------------
// Types & helpers
//------------------------------------------------------------------------------
using Str    = string;
using TimeT  = uint64_t;
using SigMap = unordered_map<Str, struct SignalSignature>;

static inline int popc(uint64_t x) {
    return __builtin_popcountll(x);
}

//------------------------------------------------------------------------------
// Phase 0: per-signal full-run signatures
//------------------------------------------------------------------------------
struct SignalSignature {
    // toggles, coverage, min/max, bit-seen masks, time range
    uint64_t toggleCount   = 0;
    uint64_t coverageCount = 0;
    int64_t  minValue      = numeric_limits<int64_t>::max();
    int64_t  maxValue      = numeric_limits<int64_t>::min();
    uint64_t bitSeen1      = 0;
    uint64_t bitSeen0      = 0;
    bool     havePrev      = false;
    int64_t  prevValue     = 0;
    bool     haveTime      = false;
    TimeT    firstTime     = 0;
    TimeT    lastTime      = 0;

    // see a new sample value v at time t
    void see(int64_t v, TimeT t) {
        // coverage
        coverageCount++;
        minValue = min(minValue, v);
        maxValue = max(maxValue, v);
        uint64_t uv = (uint64_t)v;
        bitSeen1 |= uv;
        bitSeen0 |= ~uv;
        // toggle
        if (!havePrev) {
            havePrev  = true;
            prevValue = v;
        } else if (prevValue != v) {
            toggleCount++;
            prevValue = v;
        }
        // time range
        if (!haveTime) {
            haveTime  = true;
            firstTime = lastTime = t;
        } else {
            firstTime = min(firstTime, t);
            lastTime  = max(lastTime,  t);
        }
    }

    // merge another signature into this one
    void merge(const SignalSignature &o) {
        toggleCount   += o.toggleCount;
        coverageCount += o.coverageCount;
        minValue       = min(minValue, o.minValue);
        maxValue       = max(maxValue, o.maxValue);
        bitSeen1      |= o.bitSeen1;
        bitSeen0      |= o.bitSeen0;
        if (o.haveTime) {
            if (!haveTime) {
                haveTime  = true;
                firstTime = o.firstTime;
                lastTime  = o.lastTime;
            } else {
                firstTime = min(firstTime, o.firstTime);
                lastTime  = max(lastTime,  o.lastTime);
            }
        }
    }

    // number of bits that have seen both 0 and 1
    uint64_t bitsThatChanged() const {
        return bitSeen1 & bitSeen0;
    }
};

//------------------------------------------------------------------------------
// Phase 1: single‐net Δ-feature + SimHash scoring
//------------------------------------------------------------------------------
struct SingleScorer {
    // weights
    double wToggle = 0.1;
    double wCover  = 0.05;
    double wRange  = 0.01;
    double wSim    = 5.0;

    // build feature vector
    static vector<int64_t> buildFeatures(const SignalSignature &s) {
        vector<int64_t> f;
        f.reserve(8);
        f.push_back((int64_t)s.toggleCount);
        f.push_back((int64_t)s.coverageCount);
        f.push_back(s.minValue);
        f.push_back(s.maxValue);
        f.push_back((int64_t)popc(s.bitsThatChanged()));
        f.push_back((int64_t)popc(s.bitSeen1|s.bitSeen0));
        if (s.haveTime && s.lastTime>s.firstTime) {
            double dt = double(s.lastTime - s.firstTime)+1.0;
            f.push_back((int64_t)(1e6*s.toggleCount/dt));
            f.push_back((int64_t)(1e6*s.coverageCount/dt));
        } else {
            f.push_back(0);
            f.push_back(0);
        }
        return f;
    }

    // 64-bit SimHash
    static uint64_t simhash(const SignalSignature &s) {
        auto feats = buildFeatures(s);
        int bal[64] = {};
        for (auto v: feats) {
            uint64_t uv = (uint64_t)v;
            for (int i=0;i<64;i++)
                bal[i] += (uv&(1ULL<<i))?+1:-1;
        }
        uint64_t h=0;
        for (int i=0;i<64;i++)
            if (bal[i]>=0) h|=1ULL<<i;
        return h;
    }

    // Δ-feature + SimHash distance
    double score(const SignalSignature *ps, const SignalSignature &fs) const {
        uint64_t pT = ps?ps->toggleCount:0;
        uint64_t pC = ps?ps->coverageCount:0;
        double dT = fs.toggleCount>pT ? double(fs.toggleCount-pT):0.0;
        double dC = fs.coverageCount>pC ? double(fs.coverageCount-pC):0.0;
        double dMin=0,dMax=0;
        if (ps && ps->coverageCount && fs.coverageCount) {
            if (fs.minValue<ps->minValue) dMin = double(ps->minValue-fs.minValue);
            if (fs.maxValue>ps->maxValue) dMax = double(fs.maxValue-ps->maxValue);
        }
        double simd = 1.0;
        if (ps) {
            uint64_t h1 = simhash(*ps), h2 = simhash(fs);
            simd = double(popc(h1^h2))/64.0;
        }
        return wToggle*dT + wCover*dC + wRange*(dMin+dMax) + wSim*simd;
    }

    struct Result {
        Str    name;
        double score;
    };
};

//------------------------------------------------------------------------------
// Phase 2: checkpoint manager
//------------------------------------------------------------------------------
struct Checkpoint {
    unordered_set<Str> marks;
};

//------------------------------------------------------------------------------
// Phase 3: Join/Diff + 4-case confidence scoring
//------------------------------------------------------------------------------
struct ConfidenceScorer {
    // weights for the four cases a,b,c,d
    double wa=1.0, wb=0.0, wc=0.0, wd=0.0;

    // given presence counts for each case, compute confidence
    double conf(uint64_t a,uint64_t b,uint64_t c,uint64_t d) const {
        return wa*a + wb*b + wc*c + wd*d;
    }
};

//------------------------------------------------------------------------------
// Phase 0 Parser: streaming VCD to collect marks & build full‐run SigMap
//------------------------------------------------------------------------------
class VcdParser {
    ifstream                    ifs_;
    SigMap                     &fullRun_;
    unordered_map<Str,Str>      id2name_;
    TimeT                       curT_     = 0;

    // checkpointing:
    vector<Checkpoint>          checkpoints_;
    size_t                      ckptInterval_;
    Str                         retireSignal_;
    bool                        useRetireSignal_;

public:
    VcdParser(const Str& path,
              SigMap& fullRun,
              size_t checkpointInterval,
              const Str& retireSignal)
      : ifs_(path), fullRun_(fullRun),
        ckptInterval_(checkpointInterval),
        retireSignal_(retireSignal),
        useRetireSignal_(!retireSignal.empty())
    {
        if (!ifs_.is_open())
            throw runtime_error("open VCD "+path);
        checkpoints_.push_back({});
    }

    // parse full run & collect checkpoint marks
    void parseRun() {
        Str line;
        bool inDefs=false, endDefs=false;
        while (getline(ifs_,line)) {
            trim(line);
            if (!inDefs && line.find("$var")!=Str::npos) inDefs=true;
            if (inDefs && !endDefs) {
                if (starts(line,"$var")) {
                    auto tk=tok(line);
                    if (tk.size()>=4) {
                        Str id=tk[3];
                        Str nm;
                        for (size_t i=4;i<tk.size()&&tk[i]!="$end";i++){
                            if (!nm.empty()) nm+=' ';
                            nm += tk[i];
                        }
                        id2name_[id]=nm;
                    }
                }
                else if (line.find("$enddefinitions")!=Str::npos){
                    endDefs=true;
                    inDefs=false;
                }
                continue;
            }
            if (!endDefs) continue;
            if (line.empty()) continue;
            if (line[0]=='#') {
                curT_ = stoull(line.substr(1));
                // time-based checkpoint
                if (!useRetireSignal_ &&
                    ckptInterval_>0 &&
                    curT_%ckptInterval_==0)
                {
                    checkpoints_.push_back({});
                }
                continue;
            }
            char c=line[0];
            if (c=='0'||c=='1'||c=='b'||c=='d'||c=='h'||c=='r') {
                Str code,name;
                int64_t v=0;
                if (c=='0' || c=='1') {
                    code=line.substr(1);
                    if (c=='1') v=1;
                } else {
                    auto tk=tok(line);
                    if (tk.size()!=2) continue;
                    if (c=='b') {
                        code=tk[1];
                        v = parseBinary(tk[0].substr(1));
                    } else if (c=='d') {
                        code=tk[1];
                        v = stoll(tk[0].substr(1));
                    } else if (c=='h') {
                        code=tk[1];
                        v = parseHex(tk[0].substr(1));
                    } else { // 'r'
                        code=tk[1];
                        v = llround(stod(tk[0].substr(1)));
                    }
                }
                auto it=id2name_.find(code);
                if (it==id2name_.end()) continue;
                name = it->second;

                // record full-run signature
                fullRun_[name].see(v,curT_);
                // record in current checkpoint
                checkpoints_.back().marks.insert(name);

                // if retireSignal triggers checkpoint:
                if (useRetireSignal_ && name==retireSignal_) {
                    checkpoints_.push_back({});
                }
            }
        }
    }

    const vector<Checkpoint>& checkpoints() const {
        return checkpoints_;
    }

private:
    // simple helpers
    static void trim(Str &s) {
        while (!s.empty() && isspace(s.back())) s.pop_back();
        auto p=s.find_first_not_of(" \t\r\n");
        if (p!=Str::npos) s.erase(0,p);
        else s.clear();
    }
    static bool starts(const Str &s,const Str &p) {
        return s.size()>=p.size() && equal(p.begin(),p.end(),s.begin());
    }
    static vector<Str> tok(const Str &s) {
        vector<Str> out; istringstream is(s); for (Str t;is>>t;) out.push_back(t);
        return out;
    }
    static int64_t parseHex(const Str &s) {
        int64_t v=0; stringstream ss; ss<<hex<<s; ss>>v; return v;
    }
    static int64_t parseBinary(const Str &s) {
        int64_t v=0; for(char c:s){ v<<=1; if(c=='1') v|=1; } return v;
    }
};

//------------------------------------------------------------------------------
// Main driver
//------------------------------------------------------------------------------
int main(int argc,char**argv){
    vector<Str> passVCDs, failVCDs;
    Str outPath, retireSig;
    size_t ckptInterval=0;
    int topK=50;
    double scoreCutoff=0.1;

    static struct option lopts[] = {
      {"pass_vcd",         required_argument,0,'p'},
      {"fail_vcd",         required_argument,0,'f'},
      {"out",              required_argument,0,'o'},
      {"checkpoint_interval",required_argument,0,'i'},
      {"checkpoint_retire_signal",required_argument,0,'r'},
      {"topk",             required_argument,0,'k'},
      {"score_cutoff",     required_argument,0,'c'},
      {"help",             no_argument,      0,'h'},
      {0,0,0,0}
    };
    int c; int idx;
    while ((c=getopt_long(argc,argv,"p:f:o:i:r:k:c:h",lopts,&idx))!=-1){
        switch(c){
          case 'p': passVCDs.push_back(optarg); break;
          case 'f': failVCDs.push_back(optarg); break;
          case 'o': outPath = optarg; break;
          case 'i': ckptInterval = stoull(optarg); break;
          case 'r': retireSig    = optarg; break;
          case 'k': topK        = stoi(optarg); break;
          case 'c': scoreCutoff = stod(optarg); break;
          default:
            cerr<<"Usage: invariance_detect_full "
               <<"--pass_vcd <file> --fail_vcd <file> "
               <<"[--out <file>] "
               <<"[--checkpoint_interval N] "
               <<"[--checkpoint_retire_signal SIG] "
               <<"[--topk K] [--score_cutoff D]\n";
            return 1;
        }
    }
    if (passVCDs.empty()||failVCDs.empty()){
        cerr<<"Error: must specify both --pass_vcd and --fail_vcd\n";
        return 1;
    }

    // open output
    ostream *out=&cout;
    ofstream ofs;
    if (!outPath.empty()){
        ofs.open(outPath);
        if (!ofs){ cerr<<"ERROR opening "<<outPath<<"\n"; return 1; }
        out=&ofs;
    }

    // Phase 0: full-run SigMaps + checkpoint runs
    SigMap passFull, failFull;
    vector<vector<Checkpoint>> passCkpts, failCkpts;

    for (auto &f : passVCDs) {
        cerr<<"[PASS] "<<f<<"\n";
        VcdParser vp(f, passFull, ckptInterval, retireSig);
        vp.parseRun();
        passCkpts.push_back(vp.checkpoints());
    }
    for (auto &f : failVCDs) {
        cerr<<"[FAIL] "<<f<<"\n";
        VcdParser vp(f, failFull, ckptInterval, retireSig);
        vp.parseRun();
        failCkpts.push_back(vp.checkpoints());
    }

    // Phase 1: single-net scoring
    SingleScorer   singleScorer;
    vector<SingleScorer::Result> ranked;
    ranked.reserve(failFull.size());
    for (auto &kv: failFull){
        const Str &nm = kv.first;
        double sc = singleScorer.score(
            passFull.count(nm)?&passFull[nm]:nullptr,
            kv.second
        );
        ranked.push_back({nm,sc});
    }
    sort(ranked.begin(), ranked.end(),
         [&](auto &a,auto &b){ return a.score>b.score; });
    if ((int)ranked.size()>topK) ranked.resize(topK);

    // Phase 3: Join/Diff & 4-case confidence
    // build union of all pass ckpts
    unordered_set<Str> U_pass;
    for (auto &run: passCkpts)
        for (auto &cp: run)
            U_pass.insert(cp.marks.begin(), cp.marks.end());

    // accumulate case counts
    unordered_map<Str, array<uint64_t,4>> caseCnt;
    // cases: 
    //   idx 0: fail∧¬pass
    //   idx 1: ¬fail∧pass
    //   idx 2: ¬fail∧¬pass
    //   idx 3: fail∧pass

    for (auto &run: failCkpts) {
        // build “past” = union of all but last ckpt
        unordered_set<Str> past;
        for (size_t i=0; i+1<run.size(); i++)
            for (auto &m: run[i].marks)
                past.insert(m);
        // “recent” = last ckpt
        const auto &recent = run.back().marks;

        // for every signal in union of past+recent
        unordered_set<Str> U;
        U.insert(past.begin(), past.end());
        U.insert(recent.begin(), recent.end());

        for (auto &m: U) {
            bool inF = recent.count(m);
            bool inP = U_pass.count(m);

            int idx = inF*2 + inP;
            // map (inF,inP) to case:
            // inF=1,inP=0 → idx=2 → case0
            // inF=0,inP=1 → idx=1 → case1
            // inF=0,inP=0 → idx=0 → case2
            // inF=1,inP=1 → idx=3 → case3
            static int idx2case[4] = {2,1,0,3};
            int cidx = idx2case[idx];
            caseCnt[m][cidx]++;
        }
    }

    // compute confidence per mark
    ConfidenceScorer confScorer;
    struct CRes { Str name; double conf; };
    vector<CRes> confList;
    confList.reserve(caseCnt.size());
    for (auto &kv: caseCnt) {
        auto &cnt = kv.second;
        double cf = confScorer.conf(cnt[0],cnt[1],cnt[2],cnt[3]);
        confList.push_back({kv.first, cf});
    }
    // sort descending by confidence
    sort(confList.begin(), confList.end(),
         [&](auto &a,auto &b){ return a.conf>b.conf; });

    // Output
    *out<<"=== Single-Net Anomalies (cut "<<scoreCutoff<<") ===\n";
    int printed=0;
    for (auto &r: ranked) {
        if (r.score<scoreCutoff) break;
        *out<<r.name<<" : "<<r.score<<"\n";
        if (++printed>=topK) break;
    }
    *out<<"\n=== Checkpointed Confidence (top "<<topK<<") ===\n";
    printed=0;
    for (auto &r: confList) {
        *out<<r.name<<" : "<<r.conf<<"\n";
        if (++printed>=topK) break;
    }
    if (printed==0) *out<<"[none]\n";

    return 0;
}
