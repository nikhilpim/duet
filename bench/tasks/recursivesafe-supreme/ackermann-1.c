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
    int m = __VERIFIER_nondet_int();
    int n = __VERIFIER_nondet_int();
    if (m < 0 || m > 3 ||
        n < 0 || n > 23) {
        // additional branch to avoid undefined behavior 
        // (because of signed integer overflow)
        return 0;
    }
    int result = ackermann(m,n);
    if (result >= 0) {
        return 0;
    } else {
        ERROR: {reach_error();abort();}
    }
}

