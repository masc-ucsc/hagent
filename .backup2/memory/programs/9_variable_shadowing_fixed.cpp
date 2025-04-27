#include <iostream>

int main() {
    int value = 5;
    
    if (value > 0) {
        int value2 = 10;
        value2++;
    }
    
    std::cout << "Value: " << value << std::endl;  // Prints 11
    
    return 0;
} 