extern void abort(void); 
void reach_error(){}
extern int __VERIFIER_nondet_int(void);

/*
 * Implementation the Ackermann function.
 * http://en.wikipedia.org/wiki/Ackermann_function
 * 
 * Author: Matthias Heizmann [EDITED]
 * Date: 2013-07-13
 * 
 */


int ackermann(int m, int n) {
    if (m==0) {
        return n+1;
    }
    if (n==0) {
        return ackermann(m-1,1);
    }
    return ackermann(m-1,ackermann(m,n-1));
}


int main() {
    int m1 = __VERIFIER_nondet_int();
    int m2 = __VERIFIER_nondet_int();
    int n = __VERIFIER_nondet_int();
    if (m1 < 0 || m1 > 3 ||
        m2 < 0 || m2 > 3 ||
        n < 0 || n > 23) {
        // additional branch to avoid undefined behavior 
        // (because of signed integer overflow)
        return 0;
    }
    int result1 = ackermann(m1,n);
    int result2 = ackermann(m2,n);
    if ((m1 >= m2) || result1 < result2) {
        return 0;
    } else {
        ERROR: {reach_error();abort();}
    }
}

