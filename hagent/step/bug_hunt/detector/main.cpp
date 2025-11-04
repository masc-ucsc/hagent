#include "common.hpp"

int main(int argc,char**argv){
    vector<Str> passFiles, failFiles;
    Str outPath;
    WindowPolicy wpol;
    wpol.eventsN=2000;
    bool groupByFlop=true, ignoreCombOnly=false;
    int  topk=200;
    int  topkPairs=16;
    uint64_t maxPairsPerWin=128;
    double scoreCutoff=0.1;
    ScorerCfg scorerCfg;
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
        {"weight", required_argument,0,5},
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
        case 5:
            try{ applyWeightSpec(optarg, scorerCfg); }
            catch(const exception& e){
                cerr<<"weight: "<<e.what()<<"\n"; return 1;
            }
            break;
        case 1: scorerCfg.mi=false; break;
        case 2: scorerCfg.entropy=false; break;
        case 3: scorerCfg.div=false; break;
        case 4: scorerCfg.bloom=false; break;
        case 'h':
        default:
            cout<<"invariance_detect\n"
                <<"  --pass_vcd <file> (repeatable)\n"
                <<"  --fail_vcd <file> (repeatable)\n"
                <<"  --out <file>\n"
                <<"  --window_events N     (default 2000)\n"
                <<"  --window_time   N     (VCD ticks)\n"
                <<"  --checkpoint_retire_signal SIG\n"
                <<"  --group_by_flop / --ignore_comb_only\n"
                <<"  --topk K              final report lines (default 200)\n"
                <<"  --topk_pairs N        MI top-K (default 16)\n"
                <<"  --max_pairs_per_window N (default 128)\n"
                <<"  --score_cutoff D      (default 0.1)\n"
                <<"  --weight key=value    adjust scoring weights (entropy,div,mi,bit,stable,new,missing,pattern,width_ref)\n"
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

    cerr<<"[PASS] windows …\n";
    for(auto &f:passFiles){
        cerr<<"  "<<f<<"\n";
        WindowManager wm(wpol);
        VcdStream vs(f,wm,passAgg,passPair,passWinCnt,maxPairsPerWin);
        vs.parse();
    }
    cerr<<"[FAIL] windows …\n";
    for(auto &f:failFiles){
        cerr<<"  "<<f<<"\n";
        WindowManager wm(wpol);
        VcdStream vs(f,wm,failAgg,failPair,failWinCnt,maxPairsPerWin);
        vs.parse();
    }

    Scorer scorer(passAgg,failAgg,passPair,failPair,passWinCnt,failWinCnt,scorerCfg);
    auto ranked=scorer.run(scoreCutoff,topk);

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

    *out<<"=== Per-Net Anomalies ===\n";
    for(auto &e:ranked){
        int widthInt = int(e.width+0.5);
        if(widthInt<=0) widthInt=1;
        *out<<e.name<<" "<<fmtDouble(e.score,3)
            <<" (dH="<<fmtDouble(e.dH,3)
            <<",dDiv="<<fmtDouble(e.dDiv,3)
            <<",MI="<<fmtDouble(e.mi,3)
            <<",BitNovel="<<int(std::round(e.bitNovel))<<"/"<<widthInt<<"("<<fmtDouble(e.bitNovelNorm,3)<<")"
            <<",New="<<int(std::round(e.newToggle))<<"/"<<widthInt<<"("<<fmtDouble(e.newToggleNorm,3)<<")"
            <<",Gone="<<int(std::round(e.missToggle))<<"/"<<widthInt<<"("<<fmtDouble(e.missToggleNorm,3)<<")"
            <<",SF="<<int(std::round(e.sf))<<"/"<<widthInt<<"("<<fmtDouble(e.sfNorm,3)<<")"
            <<",Pat="<<fmtDouble(e.pat,3)<<")\n";
        vector<string> bitNotes;
        auto sNovel = maskToList(e.novelMask);
        if(!sNovel.empty()) bitNotes.push_back("novel="+sNovel);
        auto sNew = maskToList(e.newMask);
        if(!sNew.empty()) bitNotes.push_back("new="+sNew);
        auto sMiss = maskToList(e.missMask);
        if(!sMiss.empty()) bitNotes.push_back("gone="+sMiss);
        if(!bitNotes.empty()){
            *out<<"    bits "<<joinStr(bitNotes, " ")<<"\n";
        }
    }
    if(groupByFlop){
        *out<<"\n=== Group (Seq-Boundary) Anomalies ===\n";
        for(auto &g:groupScores){
            *out<<g.first<<" "<<g.second<<"\n";
        }
    }
    return 0;
}
