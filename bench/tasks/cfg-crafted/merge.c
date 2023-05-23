
#include "assert.h"

int call_count;

void quicksort (int width) {
    call_count += 1;
    if (width <= 3) {
        return; 
    } else {
        int tmp = width / 2; 
        quicksort(tmp);
        quicksort(width - tmp);
    }
}

int main() {
    call_count = 0;
    int array_size = __VERIFIER_nondet_int(); 
    __VERIFIER_assume (3 < array_size);
    quicksort(array_size);
    __VERIFIER_assert(call_count <= 10 * array_size );
}