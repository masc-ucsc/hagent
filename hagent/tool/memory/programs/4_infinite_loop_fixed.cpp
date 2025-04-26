#include <iostream>
#include <chrono>
#include <thread>

int main() {
    int count = 0;
    int limit = 5;  // Fixed: limit is 5, so loop will run 5 times
    
    // Fixed: Proper while loop syntax with parentheses
    while (count < limit) {
        std::cout << "Count: " << count << std::endl;
        count++;  // Fixed: Going in correct direction
        
        // Add a small delay for visual effect
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
    }
    
    std::cout << "Loop completed with count = " << count << std::endl;
    return 0;
}