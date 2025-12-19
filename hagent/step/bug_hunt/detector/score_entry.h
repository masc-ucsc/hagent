#ifndef SCORE_ENTRY_H
#define SCORE_ENTRY_H

#include <string>

namespace inv {

struct ScoreEntry {
    std::string name;
    double score;
    
    // Components (Order MUST match scorer.h push_back)
    double dH;
    double dDiv;
    double mi;
    double bitNovel; // Static State Novelty (0/1)
    double sigNovel; // NEW: Behavioral Novelty (Physics/Timing)
    double pat;
    double tds;
    double sas;
    double maxBit;
    int anomBits;
    
    // Width is LAST
    int width; 
    
    // Helpers
    bool isStatic() const { return bitNovel > 0.5; }
    
    // Update dynamic check to include our new behavioral novelty
    bool isDynamic() const { return tds > 0.001 || sigNovel > 0.1; }
};

} // namespace inv

#endif // SCORE_ENTRY_H