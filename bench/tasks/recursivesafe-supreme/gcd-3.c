extern void abort(void); 
void reach_error(){}

/*
 * Recursive implementation of the greatest common denominator
 * using Euclid's algorithm
 * 
 * Author: Jan Leike
 * Date: 2013-07-17
 * 
 */

extern int __VERIFIER_nondet_int(void);

// Compute the greatest common denominator using Euclid's algorithm
int gcd(int y1, int y2) {
    if (y1 <= 0 || y2 <= 0) {
        return 0;
    }
    if (y1 == y2) {
        return y1;
    }
    if (y1 > y2) {
        return gcd(y1 - y2, y2);
    }
    return gcd(y1, y2 - y1);
}

int main() {
    int m = __VERIFIER_nondet_int();
    int n = __VERIFIER_nondet_int();
    if (m <= 0 || m > 2147483647 ||
        n <= 0 || n > 2147483647) {
        return 0;
    }

    int z1 = gcd(m, n);
    int z2 = gcd(n, m);
    if (z1 == z2) {
        return 0;
    } else {
        ERROR: {reach_error();abort();}
    }
}
