#include <iostream>

int main() {
    // Bug: Syntax error in variable declaration (missing semicolon)
    int number    // Missing semicolon after declaration
    
    number = 10;
    
    std::cout << "Number: " << number << std::endl;
    
    return 0;
} 