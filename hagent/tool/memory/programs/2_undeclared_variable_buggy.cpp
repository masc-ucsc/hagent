#include <iostream>

int main() {
    y = 10;  // Bug: y is used before being declared
    std::cout << "The value of y is: " << y << std::endl;
    return 0;
} 