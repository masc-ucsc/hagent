#include <iostream>

int main() {
    // Bug: Syntactical error in memory allocation (missing 'new' keyword)
    int* data = int[100];  // Incorrect syntax for memory allocation
    
    for (int i = 0; i < 100; i++) {
        data[i] = i;
    }
    
    std::cout << "Array sum: " << data[0] + data[99] << std::endl;
    
    delete[] data;
    
    return 0;
} 