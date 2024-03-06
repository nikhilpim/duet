extern void abort(void); 
void reach_error(){}

/*
 * Recursive implementation integer addition.
 * 
 * Author: Matthias Heizmann [EDITED]
 * Date: 2013-07-13
 * 
 */

extern int __VERIFIER_nondet_int(void);

int addition(int m, int n) {
    if (n == 0) {
        return m;
    }
    if (n > 0) {
        return addition(m+1, n-1);
    }
    if (n < 0) {
        return addition(m-1, n+1);
    }
}


int main() {
    int m1 = __VERIFIER_nondet_int();
    int m2 = __VERIFIER_nondet_int();
    int n = __VERIFIER_nondet_int();
    if (m1 < 0 || m1 > 1073741823 ||
        m2 < 0 || m2 > 1073741823 ||
        n < 0 || n > 1073741823) {
        // additional branch to avoid undefined behavior 
        // (because of signed integer overflow)
        return 0;
    }
    int result1 = addition(n,m1);
    int result2 = addition(m2,n);
    if ((m1 >= m2) || result1 < result2) {
        return 0;
    } else {
      ERROR: {reach_error();abort();}
    }
}
