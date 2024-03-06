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
    int m = __VERIFIER_nondet_int();
    int n1 = __VERIFIER_nondet_int();
    int n2 = __VERIFIER_nondet_int();
    if (m < 0 || m > 1073741823 ||
        n1 < 0 || n1 > 1073741823 ||
        n2 < 0 || n2 > 1073741823) {
        // additional branch to avoid undefined behavior 
        // (because of signed integer overflow)
        return 0;
    }
    int result1 = addition(m,n1);
    int result2 = addition(m,n2);
    if ((n1 >= n2) || result1 < result2) {
        return 0;
    } else {
      ERROR: {reach_error();abort();}
    }
}
