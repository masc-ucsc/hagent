#include <iostream>

int main() {
    int value = 5;
    
    if (value > 0) {
        // Bug: Syntax error in variable declaration (missing type)
        value2 = 10;  // Missing variable type declaration
        value2++;
    }
    
    std::cout << "Value: " << value << std::endl;
    
    return 0;
} 