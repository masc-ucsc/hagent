#include <iostream>

int main() {
    int a = 10;
    int b = 5;
    
    // Bug: Syntactical error using incorrect division operator syntax
    int result = a : b;  // Using ':' instead of '/' for division
    
    std::cout << "Result: " << result << std::endl;
    
    return 0;
}