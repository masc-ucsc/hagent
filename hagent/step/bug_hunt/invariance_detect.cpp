// invariance_detect_optimized.cpp
//
// High-performance invariance detector with integer‐indexed parser.
// Eliminates per-sample string lookups by two‐phase, in-place
// VCD parsing and pre-allocated tables.
//
// Usage example:
//   g++ -std=c++17 -O2 invariance_detect_optimized.cpp -o invariance_detect
//   ./invariance_detect \
//     --pass_vcd pass1.vcd --pass_vcd pass2.vcd \
//     --fail_vcd fail.vcd \
//     --checkpoint_interval 100 \
//     --checkpoint_retire_signal retire_id \
//     --topk 100 --score_cutoff 0.1 \
//     --out results.txt

#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <cassert>
#include <limits>
#include <cmath>
#include <string>
#include <vector>
#include <array>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>
#include <fstream>
#include <sstream>
#include <iostream>
#include <getopt.h>

//------------------------------------------------------------------------------
// Basic types & helpers
//------------------------------------------------------------------------------

using Str    = std::string;
using TimeT  = std::uint64_t;

// integer popcount
static inline int popc(std::uint64_t x) {
    return __builtin_popcountll(x);
}

//------------------------------------------------------------------------------
// Phase 0 data structure: per‐signal signature
//------------------------------------------------------------------------------

struct SignalSignature {
    std::uint64_t toggleCount   = 0;
    std::uint64_t coverageCount = 0;
    std::int64_t  minValue      = std::numeric_limits<std::int64_t>::max();
    std::int64_t  maxValue      = std::numeric_limits<std::int64_t>::min();
    std::uint64_t bitSeen1      = 0;
    std::uint64_t bitSeen0      = 0;
    bool           havePrev     = false;
    std::int64_t  prevValue     = 0;
    bool           haveTime     = false;
    TimeT          firstTime    = 0;
    TimeT          lastTime     = 0;

    inline void see(std::int64_t v, TimeT t) {
        // coverage & range
        coverageCount++;
        if (v < minValue) minValue = v;
        if (v > maxValue) maxValue = v;
        std::uint64_t uv = static_cast<std::uint64_t>(v);
        bitSeen1 |= uv;
        bitSeen0 |= ~uv;

        // toggles
        if (!havePrev) {
            havePrev = true;
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
            if (t < firstTime)  firstTime = t;
            if (t > lastTime)   lastTime  = t;
        }
    }

    inline void merge(const SignalSignature &o) {
        toggleCount   += o.toggleCount;
        coverageCount += o.coverageCount;
        if (o.minValue < minValue) minValue = o.minValue;
        if (o.maxValue > maxValue) maxValue = o.maxValue;
        bitSeen1 |= o.bitSeen1;
        bitSeen0 |= o.bitSeen0;
        if (o.haveTime) {
            if (!haveTime) {
                haveTime  = true;
                firstTime = o.firstTime;
                lastTime  = o.lastTime;
            } else {
                if (o.firstTime < firstTime) firstTime = o.firstTime;
                if (o.lastTime  > lastTime )  lastTime  = o.lastTime;
            }
        }
    }

    inline std::uint64_t bitsThatChanged() const {
        return bitSeen1 & bitSeen0;
    }
};

//------------------------------------------------------------------------------
// Phase 1: single‐net Δ‐feature + SimHash scoring
//------------------------------------------------------------------------------

struct SingleScorer {
    double wToggle = 0.1;
    double wCover  = 0.05;
    double wRange  = 0.01;
    double wSim    = 5.0;

    struct Result {
        Str       name;
        double    score;
    };

    static std::vector<std::int64_t>
    buildFeatures(const SignalSignature &s) {
        std::vector<std::int64_t> f;
        f.reserve(8);
        f.push_back(static_cast<std::int64_t>(s.toggleCount));
        f.push_back(static_cast<std::int64_t>(s.coverageCount));
        f.push_back(s.minValue);
        f.push_back(s.maxValue);
        f.push_back(popc(s.bitsThatChanged()));
        f.push_back(popc(s.bitSeen1 | s.bitSeen0));
        if (s.haveTime && s.lastTime > s.firstTime) {
            double dt = double(s.lastTime - s.firstTime) + 1.0;
            f.push_back(static_cast<std::int64_t>(1e6 * s.toggleCount / dt));
            f.push_back(static_cast<std::int64_t>(1e6 * s.coverageCount / dt));
        } else {
            f.push_back(0);
            f.push_back(0);
        }
        return f;
    }

    static std::uint64_t simhash(const SignalSignature &s) {
        auto feats = buildFeatures(s);
        int bal[64] = {0};
        for (auto v: feats) {
            std::uint64_t uv = static_cast<std::uint64_t>(v);
            for (int i = 0; i < 64; ++i) {
                bal[i] += (uv & (1ULL << i)) ? +1 : -1;
            }
        }
        std::uint64_t h = 0;
        for (int i = 0; i < 64; ++i) {
            if (bal[i] >= 0) h |= (1ULL << i);
        }
        return h;
    }

    double score(const SignalSignature *ps,
                 const SignalSignature &fs) const
    {
        std::uint64_t pT = ps ? ps->toggleCount   : 0;
        std::uint64_t pC = ps ? ps->coverageCount : 0;
        double dT = (fs.toggleCount > pT)
                  ? double(fs.toggleCount - pT) : 0.0;
        double dC = (fs.coverageCount > pC)
                  ? double(fs.coverageCount - pC) : 0.0;

        double dMin = 0.0, dMax = 0.0;
        if (ps && ps->coverageCount && fs.coverageCount) {
            if (fs.minValue < ps->minValue)
                dMin = std::fabs(double(ps->minValue - fs.minValue));
            if (fs.maxValue > ps->maxValue)
                dMax = std::fabs(double(fs.maxValue - ps->maxValue));
        }

        double simd = 1.0;
        if (ps) {
            auto h1 = simhash(*ps), h2 = simhash(fs);
            simd = double(popc(h1 ^ h2)) / 64.0;
        }

        return wToggle * dT
             + wCover  * dC
             + wRange  * (dMin + dMax)
             + wSim    * simd;
    }
};

//------------------------------------------------------------------------------
// Phase 2: checkpoints
//------------------------------------------------------------------------------

struct Checkpoint {
    std::unordered_set<Str> marks;
};

//------------------------------------------------------------------------------
// Phase 3: 4-case confidence
//------------------------------------------------------------------------------

struct ConfidenceScorer {
    // weights for cases: (fail∧¬pass), (¬fail∧pass), (¬fail∧¬pass), (fail∧pass)
    double wa = 1.0, wb = 0.0, wc = 0.0, wd = 0.0;

    inline double
    conf(std::uint64_t a, std::uint64_t b,
         std::uint64_t c, std::uint64_t d) const
    {
        return wa*a + wb*b + wc*c + wd*d;
    }
};

//------------------------------------------------------------------------------
// Fast two-phase VCD parser
//------------------------------------------------------------------------------

class FastVcdParser {
  private:
    std::ifstream                               ifs_;
    // id→idx table
    std::unordered_map<Str,std::size_t>         id2idx_;
    std::vector<Str>                            idx2name_;
    // per-id signatures & checkpoint marks
    std::vector<SignalSignature>                sigs_;
    std::vector<Checkpoint>                     checkpoints_;
    bool                                        useRetireSignal_;
    std::size_t                                 retireIdx_;
    std::size_t                                 ckptInterval_;
    TimeT                                       curTime_ = 0;

  public:
    FastVcdParser(char const *path,
                  std::size_t checkpointInterval,
                  Str const &retireSignal)
      : ifs_(path)
      , useRetireSignal_(!retireSignal.empty())
      , retireIdx_(std::string::npos)
      , ckptInterval_(checkpointInterval)
    {
      if (!ifs_.is_open())
        throw std::runtime_error("Cannot open VCD: " + Str(path));

      // ➊ Scan definitions
      scanDefinitions(retireSignal);

      // ➋ Reserve & start first checkpoint
      sigs_.resize(idx2name_.size());
      checkpoints_.reserve(1024);
      checkpoints_.push_back({});
    }

    /// Parse the rest of the file (definitions already consumed)
    /// and fill both full-run signatures and checkpoint marks.
    void parseRun() {
      Str line;
      while (std::getline(ifs_, line)) {
        if (line.empty()) continue;
        char c = line[0];

        // timestamp
        if (c=='#') {
          curTime_ = std::stoull(line.substr(1));
          if (!useRetireSignal_
              && ckptInterval_ > 0
              && curTime_ % ckptInterval_ == 0)
          {
            checkpoints_.emplace_back();
          }
          continue;
        }

        // value change
        std::size_t idx;
        std::int64_t v = 0;
        if (c=='0' || c=='1') {
          idx = lookupID(line.c_str()+1);
          if (idx == std::string::npos) continue;
          v = (c=='1');
        }
        else if (c=='b' || c=='d' || c=='h' || c=='r') {
          auto sp = line.find(' ');
          if (sp==Str::npos) continue;
          Str val = line.substr(1, sp-1);
          Str idc = line.substr(sp+1);
          idx = lookupID(idc.c_str());
          if (idx == std::string::npos) continue;

          if (c=='b') {
            v = 0;
            for (char bit: val) { v <<= 1; if (bit=='1') v |= 1; }
          }
          else if (c=='d') {
            v = std::stoll(val);
          }
          else if (c=='h') {
            std::stringstream ss; ss << std::hex << val; ss >> v;
          }
          else { // real
            v = std::llround(std::stod(val));
          }
        }
        else {
          continue;
        }

        // update signature & checkpoint
        SignalSignature &sig = sigs_[idx];
        sig.see(v, curTime_);
        checkpoints_.back().marks.insert(idx2name_[idx]);

        // retire-signal triggers new checkpoint
        if (useRetireSignal_ && idx==retireIdx_) {
          checkpoints_.emplace_back();
        }
      }
    }

    /// After parseRun(), hand back the results:
    ///  - fullRun: a map name→SignalSignature
    ///  - cpts:   a vector of checkpoint sets
    void extract(std::unordered_map<Str,SignalSignature> &fullRun,
                 std::vector<Checkpoint>              &cpts) const
    {
      fullRun.clear();
      fullRun.reserve(sigs_.size());
      for (std::size_t i = 0; i < sigs_.size(); ++i) {
        if (sigs_[i].coverageCount>0) {
          fullRun.emplace(idx2name_[i], sigs_[i]);
        }
      }
      cpts = checkpoints_;
    }

  private:
    /// Read up to `$enddefinitions`, build id2idx_, idx2name_,
    /// record retireIdx_ if a retireSignal is seen in definitions.
    void scanDefinitions(Str const &retireSignal) {
      Str line;
      bool inDefs=false;
      while (std::getline(ifs_, line)) {
        if (!inDefs && line.find("$var")!=Str::npos) {
          inDefs = true;
        }
        if (inDefs) {
          if (line.rfind("$var",0)==0) {
            auto tok = splitWhitespace(line);
            if (tok.size()>=4) {
              Str id   = tok[3];
              Str name;
              for (std::size_t j=4; j<tok.size() && tok[j]!="$end"; ++j) {
                if (!name.empty()) name.push_back(' ');
                name += tok[j];
              }
              std::size_t idx = idx2name_.size();
              id2idx_[id]     = idx;
              idx2name_.push_back(std::move(name));
              if (retireSignal!="" && idx2name_.back()==retireSignal) {
                retireIdx_ = idx;
              }
            }
          }
          else if (line.find("$enddefinitions")!=Str::npos) {
            return;
          }
        }
      }
      throw std::runtime_error("No $enddefinitions found");
    }

    inline std::size_t lookupID(char const *idc) const {
      auto it = id2idx_.find(idc);
      return (it==id2idx_.end() ? std::string::npos
                               : it->second);
    }

    static std::vector<Str> splitWhitespace(Str const &s) {
      std::vector<Str> out;
      std::istringstream is(s);
      for (Str w; is>>w;) out.push_back(w);
      return out;
    }
};

//------------------------------------------------------------------------------
// Main driver
//------------------------------------------------------------------------------

static void usage() {
  std::cerr
    << "Usage: invariance_detect [OPTIONS]\n"
    << "  --pass_vcd <file>      (repeatable)\n"
    << "  --fail_vcd <file>      (repeatable)\n"
    << "  --checkpoint_interval N\n"
    << "  --checkpoint_retire_signal SIG\n"
    << "  --topk K\n"
    << "  --score_cutoff D\n"
    << "  --out <file>\n";
}

int main(int argc, char **argv) {
  std::vector<Str> passVCDs, failVCDs;
  std::size_t      ckptInterval = 0;
  Str              retireSig;
  int              topK         = 50;
  double           scoreCutoff  = 0.1;
  Str              outPath;

  static struct option longopts[] = {
    {"pass_vcd",      required_argument, nullptr, 'p'},
    {"fail_vcd",      required_argument, nullptr, 'f'},
    {"checkpoint_interval", required_argument, nullptr, 'i'},
    {"checkpoint_retire_signal", required_argument, nullptr, 'r'},
    {"topk",          required_argument, nullptr, 'k'},
    {"score_cutoff",  required_argument, nullptr, 'c'},
    {"out",           required_argument, nullptr, 'o'},
    {"help",          no_argument,       nullptr, 'h'},
    {0,0,0,0}
  };

  int c, idx;
  while ((c = getopt_long(argc,argv,"p:f:i:r:k:c:o:h",longopts,&idx))!=-1) {
    switch(c) {
      case 'p': passVCDs.push_back(optarg); break;
      case 'f': failVCDs.push_back(optarg); break;
      case 'i': ckptInterval = std::stoull(optarg); break;
      case 'r': retireSig    = optarg; break;
      case 'k': topK         = std::stoi(optarg); break;
      case 'c': scoreCutoff  = std::stod(optarg); break;
      case 'o': outPath      = optarg; break;
      default: usage(); return 1;
    }
  }
  if (passVCDs.empty() || failVCDs.empty()) {
    usage(); return 1;
  }

  // open output
  std::ostream *out = &std::cout;
  std::ofstream  ofs;
  if (!outPath.empty()) {
    ofs.open(outPath);
    if (!ofs) {
      std::cerr<<"ERROR: cannot open "<<outPath<<"\n";
      return 1;
    }
    out = &ofs;
  }

  // Phase 0: parse & aggregate pass/fail
  std::unordered_map<Str,SignalSignature> passFull, failFull;
  std::vector<std::vector<Checkpoint>>    passCkpts, failCkpts;

  for (auto const &f: passVCDs) {
    std::cerr<<"[PASS] "<<f<<"\n";
    FastVcdParser vp(f.c_str(), ckptInterval, retireSig);
    vp.parseRun();
    vp.extract(passFull, passCkpts.emplace_back());
  }
  for (auto const &f: failVCDs) {
    std::cerr<<"[FAIL] "<<f<<"\n";
    FastVcdParser vp(f.c_str(), ckptInterval, retireSig);
    vp.parseRun();
    vp.extract(failFull, failCkpts.emplace_back());
  }

  // Phase 1: score single‐net anomalies
  SingleScorer singleScorer;
  std::vector<SingleScorer::Result> ranked;
  ranked.reserve(failFull.size());
  for (auto &kv: failFull) {
    SignalSignature const *ps = nullptr;
    auto it = passFull.find(kv.first);
    if (it!=passFull.end()) ps = &it->second;
    double sc = singleScorer.score(ps, kv.second);
    ranked.push_back({kv.first, sc});
  }
  std::sort(ranked.begin(), ranked.end(),
            [](auto const &a, auto const &b){
              return a.score > b.score;
            });
  if ((int)ranked.size() > topK) ranked.resize(topK);

  // Phase 3: checkpoint‐based confidence
  // union of all pass marks
  std::unordered_set<Str> U_pass;
  for (auto &run: passCkpts)
    for (auto &cp: run)
      U_pass.insert(cp.marks.begin(), cp.marks.end());

  // accumulate counts per signal
  std::unordered_map<Str,std::array<std::uint64_t,4>> caseCnt;
  for (auto &run: failCkpts) {
    // build past = union of all but last
    std::unordered_set<Str> past;
    for (std::size_t i = 0; i+1 < run.size(); ++i)
      for (auto const &m: run[i].marks)
        past.insert(m);
    auto const &recent = run.back().marks;

    std::unordered_set<Str> U = past;
    U.insert(recent.begin(), recent.end());

    for (auto const &m: U) {
      bool inF = recent.count(m);
      bool inP = U_pass.count(m);
      // map (inF,inP) to [0..3]
      //  F P → case
      //  1 0 → 0
      //  0 1 → 1
      //  0 0 → 2
      //  1 1 → 3
      static int mapIdx[4] = {2,1,0,3};
      int idx = mapIdx[(inF<<1)|inP];
      caseCnt[m][idx]++;
    }
  }

  ConfidenceScorer confScorer;
  struct CRes { Str name; double c; };
  std::vector<CRes> confList;
  confList.reserve(caseCnt.size());
  for (auto &kv: caseCnt) {
    auto &cnt = kv.second;
    double cf = confScorer.conf(cnt[0],cnt[1],cnt[2],cnt[3]);
    confList.push_back({kv.first, cf});
  }
  std::sort(confList.begin(), confList.end(),
            [](auto const &a, auto const &b){
              return a.c > b.c;
            });

  // Output
  *out << "=== Single-Net Anomalies (cut " << scoreCutoff << ") ===\n";
  int printed = 0;
  for (auto const &r: ranked) {
    if (r.score < scoreCutoff) break;
    *out << r.name << " : " << r.score << "\n";
    if (++printed >= topK) break;
  }
  *out << "\n=== Checkpointed Confidence (top " << topK << ") ===\n";
  printed = 0;
  for (auto const &r: confList) {
    *out << r.name << " : " << r.c << "\n";
    if (++printed >= topK) break;
  }
  if (printed==0) *out<<"[none]\n";

  return 0;
}
