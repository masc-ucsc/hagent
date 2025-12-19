#include "vcd_stream.h"
#include "scorer.h"
#include "score_entry.h"
#include <getopt.h>

using namespace inv;

int main(int argc, char** argv) {
    std::vector<Str> passF, failF;
    Str outPath;
    WindowPolicy wp;
    ScorerCfg sc;
    uint64_t maxPairs = 128;
    double cutoff = 0.1;

    static struct option opts[] = {
        {"pass_vcd", 1, 0, 'P'},
        {"fail_vcd", 1, 0, 'F'},
        {"out", 1, 0, 'o'},
        {"window_events", 1, 0, 'e'},
        {"window_time", 1, 0, 't'},
        {"enable_cluster", 0, 0, 'C'},
        {"topk", 1, 0, 'k'},
        {0,0,0,0}
    };

    int c;
    while((c=getopt_long(argc, argv, "P:F:o:e:t:Ck:", opts, nullptr)) != -1) {
        switch(c) {
            case 'P': passF.push_back(optarg); break;
            case 'F': failF.push_back(optarg); break;
            case 'o': outPath = optarg; break;
            case 'e': wp.mode=WindowMode::EVENTS; wp.eventsN=std::stoull(optarg); break;
            case 't': wp.mode=WindowMode::TIME; wp.timeN=std::stoull(optarg); break;
            case 'C': sc.enableCluster = true; break;
            case 'k': sc.topK = std::stoi(optarg); break;
        }
    }

    if(passF.empty() || failF.empty()) {
        std::cerr << "Usage: ./invariance_detect --pass_vcd <f> --fail_vcd <f> [--out <f>] [--enable_cluster]\n";
        return 1;
    }

    std::unordered_map<Str, SigAgg> pAgg, fAgg;
    std::unordered_map<PairKey, uint32_t, PairKeyHash> pPair, fPair;
    uint64_t pWin=0, fWin=0;

    auto parse = [&](const std::vector<Str>& files, auto& agg, auto& pair, uint64_t& wins) {
        for(auto& f : files) {
            std::cerr << "Parsing " << f << "...\n";
            WindowManager wm(wp);
            VcdStream vs(f, wm, agg, pair, wins, maxPairs);
            vs.parse();
        }
    };

    parse(passF, pAgg, pPair, pWin);
    parse(failF, fAgg, fPair, fWin);

    std::ostream* out = &std::cout;
    std::ofstream ofs;
    if(!outPath.empty()) {
        ofs.open(outPath);
        out = &ofs;
    }

    Scorer scorer(pAgg, fAgg, pPair, fPair, pWin, fWin, sc);
    scorer.run(cutoff, *out);

    return 0;
}
