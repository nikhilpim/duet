
#include "assert.h"

int call_count;


void quicksort (int* arr, int left, int right) {
    call_count += 1;
    if (right - left <= 1) {
        return; 
    } else {
        int pivot = __VERIFIER_nondet_int();
        __VERIFIER_assume (left <= pivot && 
            pivot < right);
        quicksort(arr, left, pivot);
        quicksort(arr, pivot + 1, right);
    }
}

int main() {
    call_count = 0;
    int size = __VERIFIER_nondet_int(); 
    __VERIFIER_assume (1 <= size);
    quicksort(__VERIFIER_nondet_int(), 0, size);
    __VERIFIER_assert(call_count <= 2 * 
        size + 1 );
}