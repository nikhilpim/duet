#include "assert.h"

// A sheep is walking across a bridge. 
// The bridge is represented by an array of 1's and 0's - 1's represent the safe spots in the bridge.
// The sheep can either step forward 2 steps or jump 4 steps. Can the sheep make it across the bridge?

int aligned_access(int arr[], int ind) {
    __VERIFIER_assert(ind % 2 == 0);
    return arr[ind];
}

int sheep_walker(int road[], int ind, int end) {
    if (ind >= end) {
        return 1;
    } else if (aligned_access(road, ind) == 0) {
        return 0;
    }
    return sheep_walker(road, ind + 2, end) || sheep_walker(road, ind + 4, end);
}

int main() {
    int road_size = __VERIFIER_nondet_int();
    int road[] = __VERIFIER_nondet_array(road_size);
    int result = sheep_walker(road, 0, road_size);
}