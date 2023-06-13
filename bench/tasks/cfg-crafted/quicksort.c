
extern int __VERIFIER_nondet_int();
extern void abort(void); 
void reach_error(){}

int call_count;

void quicksort (int* arr, int left, int right) {
    call_count += 1;
    if (right - left <= 1) {
        return; 
    } else {
        int pivot = left;
        for (int j = left; j < right - 1; j++) {
            if (__VERIFIER_nondet_int()) {
                pivot++;
            }
        }
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
        size + 2 );
}