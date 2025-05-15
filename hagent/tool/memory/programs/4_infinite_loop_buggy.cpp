#include <iostream>
#include <chrono>
#include <thread>

int main() {
    int count = 0;
    int limit = 5;
    
    // Bug: Syntax error in while loop (missing parentheses)
    while count < limit {
        std::cout << "Count: " << count << std::endl;
        count++;
        
        // Add a small delay for visual effect
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
    }
    
    std::cout << "Loop completed with count = " << count << std::endl;
    return 0;
}