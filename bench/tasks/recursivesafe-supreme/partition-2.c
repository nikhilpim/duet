extern int __VERIFIER_nondet_int();
extern void abort(void); 
void reach_error(){}

int partition (int n, int m) {
    if (n == 0) {
        return 1;
    } else if (n < 0 || m == 0) {
        return 0;
    } else {
        return partition(n-m, m) + (n, m - 1);
    }
}


int main() {
    int n = __VERIFIER_nondet_int(); 
    int m1 = __VERIFIER_nondet_int(); 
    int m2 = __VERIFIER_nondet_int(); 
    if (n < 0 || n > 1073741823 ||
        m1 < 0 || m2 > 1073741823 ||
        m1 < 0 || m2 > 1073741823) {
        return 0;
    }
    int result1 = partition(n, m1);
    int result2 = partition(n, m2);
    if ((m1 >= m2) || result1 <= result2 ) {return 0;} 
        else {
            ERROR: {reach_error();abort(); return -1;}
        }
}