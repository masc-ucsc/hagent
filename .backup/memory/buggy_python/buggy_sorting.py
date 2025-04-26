#!/usr/bin/env python3
"""Simple buggy sorting algorithm implementation"""

import random

def buggy_bubble_sort(arr):
    """Bubble sort with intentional bugs"""
    n = len(arr)
    
    # Bug 1: Range should be n, not n-1 (misses last pass)
    for i in range(n-1):
        # Bug 2: Range should be n-i-1, not n-1 (unnecessarily checks sorted elements)
        for j in range(n-1):
            # Bug 3: Inconsistent swap direction (sorts in descending order)
            if arr[j] < arr[j+1]:
                arr[j], arr[j+1] = arr[j+1], arr[j]
    
    return arr

# Test the buggy sorting function
test_array = [random.randint(1, 100) for _ in range(10)]
print(f"Original array: {test_array}")
print(f"Sorted array: {buggy_bubble_sort(test_array.copy())}")
# Bug 4: Original array shows as sorted in output due to modifying the array directly 