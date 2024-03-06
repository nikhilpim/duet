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
    int n1 = __VERIFIER_nondet_int(); 
    int n2 = __VERIFIER_nondet_int(); 
    int k = __VERIFIER_nondet_int(); 
    if (n1 < 0 || n1 > 1073741823 ||
        n2 < 0 || n2 > 1073741823 ||
        k < 0 || k > 1073741823) {
        return 0;
    }
    int result1 = binomial(n1, k);
    int result2 = binomial(n2, k);
    if ((n1 >= n2) || result1 < result2) {return 0;} 
        else {
            ERROR: {reach_error();abort(); return -1;}
        }
}