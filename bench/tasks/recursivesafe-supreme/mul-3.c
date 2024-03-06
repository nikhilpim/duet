extern void abort(void); 
void reach_error(){}

/*
 * Recursive implementation multiplication by repeated addition
 * Check that this multiplication is commutative
 * 
 * Author: Jan Leike [EDITED]
 * Date: 2013-07-17
 * 
 */

extern int __VERIFIER_nondet_int(void);

// Multiplies two integers n and m
int mult(int n, int m) {
    if (m < 0) {
        return mult(n, -m);
    }
    if (m == 0) {
        return 0;
    }
    return n + mult(n, m - 1);
}

int main() {
    int m1 = __VERIFIER_nondet_int();
    int m2 = __VERIFIER_nondet_int();
    int n = __VERIFIER_nondet_int();
    if (m1 < 0 || m1 > 46340 ||
        m2 < 0 || m2 > 46340 ||
        n < 0 || n > 46340) {
        return 0;
    }
    int res1 = mult(n, m1);
    int res2 = mult(n, m2);
    if ((m1 >= m2) || res1 < res2) {
      return 0;
    } else {
        ERROR: {reach_error();abort();}
    }
}
