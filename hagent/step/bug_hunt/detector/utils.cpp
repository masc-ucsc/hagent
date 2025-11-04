#include "common.hpp"

unordered_map<Str,SignalMeta> gSignalMeta;

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

Str joinStr(const vector<string>& items, const string& sep){
    string out;
    for(size_t i=0;i<items.size();i++){
        if(i) out+=sep;
        out+=items[i];
    }
    return out;
}

Str fmtDouble(double v, int precision){
    ostringstream oss;
    oss.setf(std::ios::fixed);
    oss<<setprecision(precision)<<v;
    return oss.str();
}

Str maskToList(uint64_t mask, int limit){
    if(mask==0) return "";
    vector<int> bits;
    uint64_t tmp=mask;
    for(int b=0; b<64 && (int)bits.size()<limit; ++b){
        if(tmp & (1ULL<<b)){
            bits.push_back(b);
            tmp &= ~(1ULL<<b);
        }
    }
    string s="{";
    for(size_t i=0;i<bits.size();++i){
        if(i) s+=',';
        s+=to_string(bits[i]);
    }
    if(tmp) s+=",…";
    s+='}';
    return s;
}

void applyWeightSpec(const Str& spec, ScorerCfg& cfg){
    auto pos = spec.find('=');
    if(pos==Str::npos) throw runtime_error("Weight spec must be key=value");
    Str key = spec.substr(0,pos);
    Str valStr = spec.substr(pos+1);
    if(valStr.empty()) throw runtime_error("Weight spec "+spec+" missing value");
    transform(key.begin(), key.end(), key.begin(), [](unsigned char c){ return std::tolower(c); });
    double val = stod(valStr);
    if(key=="entropy") cfg.wEntropy = val;
    else if(key=="div"||key=="diversity") cfg.wDiversity = val;
    else if(key=="mi") cfg.wMI = val;
    else if(key=="bit"||key=="bitnovel") cfg.wBitNovel = val;
    else if(key=="stable"||key=="stableflip") cfg.wStableFlip = val;
    else if(key=="new"||key=="newtoggle") cfg.wNewToggle = val;
    else if(key=="missing"||key=="gone"||key=="missingtoggle") cfg.wMissingToggle = val;
    else if(key=="pattern"||key=="pat") cfg.wPattern = val;
    else if(key=="width_ref"||key=="widthreference") cfg.widthReference = max(1.0, val);
    else throw runtime_error("Unknown weight key '"+key+"'");
}

bool isSeq(const Str& n){
    static const vector<Str> keys={"_q", ".q", "_regq", "_dq"};
    for(auto &k:keys) if(n.size()>=k.size() && n.rfind(k)==n.size()-k.size()) return true;
    return false;
}
Str deriveGroup(const Str& n){
    size_t p=n.find_last_of("._");
    if(p==Str::npos) return n;
    return n.substr(0,p);
}
