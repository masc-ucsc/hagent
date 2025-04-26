#include <iostream>

int main() {
    // Fixed: Proper syntax for memory allocation with 'new' keyword
    int* data = new int[100];  // Correct allocation syntax
    
    for (int i = 0; i < 100; i++) {
        data[i] = i;
    }
    
    std::cout << "Array sum: " << data[0] + data[99] << std::endl;
    
    delete[] data;  // Proper memory deallocation
    
    return 0;
} 