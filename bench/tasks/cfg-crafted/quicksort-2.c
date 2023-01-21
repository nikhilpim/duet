

int call_count;

void quicksort (int left, int right) {
    call_count += 1;
    if (right - left <= 1) {
        return; 
    } else {
        int pivot = __VERIFIER_nondet_int();
        __VERIFIER_assume (left <= pivot && pivot < right);
        quicksort(left, pivot);
        quicksort(pivot + 1, right);
    }
}

int main() {
    call_count = 0;
    int array_size = __VERIFIER_nondet_int(); 
    __VERIFIER_assume (1 <= array_size);
    quicksort(0, array_size);
    __VERIFIER_assert(call_count <= 2 * array_size + 1 );
}