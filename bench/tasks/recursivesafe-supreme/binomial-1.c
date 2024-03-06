extern int __VERIFIER_nondet_int();
extern void abort(void); 
void reach_error(){}

int binomial(int n, int k) {
    if (n < k) {
        return 0;
    } else if (n == k || n == 0) {
        return 1;
    } else {
        return binomial(n - 1, k - 1) + binomial(n - 1, k);
    }
}


int main() {
    int n = __VERIFIER_nondet_int(); 
    int k = __VERIFIER_nondet_int(); 
    if (n < 0 || n > 1073741823 ||
        k < 0 || k > 1073741823) {
        return 0;
    }
    int result1 = binomial(n, k);
    int result2 = binomial(n, n-k);
    if (result1 == result2) {return 0;} 
        else {
            ERROR: {reach_error();abort(); return -1;}
        }
}