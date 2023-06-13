
int call_count;

void mergesort (int width) {
    call_count += 1;
    if (width <= 1) {
        return; 
    } else {
        int left = 1;
        int right = 1;
        for (int i = 0; i < width-2; i ++) {
            if (i % 2 == 0) {
                left ++;
            } else {
                right ++;
            }
        }
        mergesort(left);
        mergesort(right);
    }
}

int main() {
    call_count = 0;
    int array_size = __VERIFIER_nondet_int(); 
    __VERIFIER_assume(array_size >= 0);

    mergesort(array_size);
    __VERIFIER_assert(call_count <= 2 * array_size + 1);
}