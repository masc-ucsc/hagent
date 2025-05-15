#include <iostream>

int main() {
    // Fixed: Proper array declaration with correct syntax
    int arr[5] = {1, 2, 3, 4, 5};
    
    for (int i = 0; i < 5; i++) {  // Fixed: Proper bounds checking
        std::cout << "Element " << i << ": " << arr[i] << std::endl;
    }
    return 0;
} 