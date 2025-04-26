#include <iostream>

int main() {
    int value = 0;
    int* ptr = &value;
    *ptr = 10;  // Fixed: Properly initialized pointer
    std::cout << "Value at ptr: " << *ptr << std::endl;
    return 0;
} 