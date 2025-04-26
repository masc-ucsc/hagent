#include <iostream>

int main() {
    // Bug: Syntactical error in array declaration (missing semicolon and using comma instead of braces)
    int arr[5] = 1, 2, 3, 4, 5
    
    for (int i = 0; i < 5; i++) {
        std::cout << "Element " << i << ": " << arr[i] << std::endl;
    }
    return 0;
}