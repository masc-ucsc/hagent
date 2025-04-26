#include <iostream>

// Buggy array implementation with several issues
class BuggyArray {
private:
    int* arr;
    int size;  // Bug 1: Should track capacity separately from size
    
public:
    BuggyArray(int capacity) {
        arr = new int[capacity];
        size = capacity;  // Bug 2: Size should be initialized to 0
    }
    
    // Bug 3: Missing destructor - memory leak
    
    void set(int index, int value) {
        arr[index] = value;  // Bug 4: No bounds checking
    }
    
    int get(int index) {
        return arr[index];  // Bug 5: No bounds checking
    }
};

int main() {
    BuggyArray arr(5);
    arr.set(10, 100);  // Bug: Out of bounds access
    std::cout << "Value: " << arr.get(10) << std::endl;  // Bug: Out of bounds access
    return 0;  // Bug: Memory leak (no destructor)
} 