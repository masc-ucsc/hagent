#include "common.hpp"

WindowManager::WindowManager(const WindowPolicy& p):pol_(p){
    if(pol_.mode==WindowMode::TIME) nextT_=pol_.timeN;
}
bool WindowManager::shouldRotateEvent() {
    if(pol_.mode!=WindowMode::EVENTS) return false;
    return (++evCnt_ >= pol_.eventsN);
}
bool WindowManager::shouldRotateTime(TimeT t){
    if(pol_.mode!=WindowMode::TIME) return false;
    if(t>=nextT_){ nextT_+=pol_.timeN; return true; }
    return false;
}
bool WindowManager::shouldRotateRetire(const Str& sig){
    return (pol_.mode==WindowMode::RETIRE && !pol_.retireSig.empty() && sig==pol_.retireSig);
}
void WindowManager::resetEvent(){ evCnt_=0; }

VcdStream::VcdStream(const Str& path, WindowManager& w,
                     unordered_map<Str,SigAgg>& a,
                     unordered_map<PairKey,uint32_t,PairKeyHash>& p,
                     uint64_t &gwCnt,
                     uint64_t maxPairs)
    :ifs(path),wm(w),agg(a),pairs(p),globalWinCnt(gwCnt),maxPairsPerWindow(maxPairs){
    if(!ifs) throw runtime_error("open "+path);
    parseHeader();
}

void VcdStream::parse(){
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
        if(c=='0'||c=='1'){
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
            if(val.find('x')!=Str::npos||val.find('z')!=Str::npos) continue;
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
    if(!curWin.empty()) rotate();
}

void VcdStream::parseHeader(){
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

void VcdStream::rotate(){
    globalWinCnt++;

    vector<Str> active; active.reserve(curWin.size());
    for(auto &kv:curWin){
        const Str& s = kv.first;
        const auto& f= kv.second;
        uint64_t mask = nameMask.count(s)? nameMask[s] : ~0ULL;
        agg[s].update(f, mask);
        if(f.toggles) active.push_back(s);
    }
    sort(active.begin(), active.end());

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

void VcdStream::onValue(const Str& sig, uint64_t v, uint64_t mask){
    auto &s = curWin[sig];
    s.see(v, mask);
    if(wm.shouldRotateEvent()) rotate();
}
