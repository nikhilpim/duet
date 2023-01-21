

int call_count;

void quicksort (int width) {
    call_count += 1;
    if (width <= 1) {
        return; 
    } else {
        int havoc = __VERIFIER_nondet_int();
        __VERIFIER_assume (0 <= havoc && havoc <= width - 1);
        quicksort(havoc);
        quicksort(width - havoc - 1);
    }
}

int main() {
    call_count = 0;
    int array_size = __VERIFIER_nondet_int(); 
    __VERIFIER_assume (1 <= array_size);
    quicksort(array_size);
    __VERIFIER_assert(call_count <= 2 * array_size + 1 );
}