#include <iostream>

int main() {
    int* ptr = nullptr;
    *ptr = 10;  // Bug: Dereferencing null pointer
    std::cout << "Value at ptr: " << *ptr << std::endl;
    return 0;
}