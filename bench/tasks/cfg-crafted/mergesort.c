extern int __VERIFIER_nondet_int();
extern int __VERIFIER_nondet_array();
extern void abort(void); 
void reach_error(){}

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
    mergesort(array_size);
    if (!(array_size < 0 || (call_count <= 2 * array_size + 1))) {
        ERROR: {reach_error();abort();}
    }
}