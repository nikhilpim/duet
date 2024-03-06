extern void abort(void); 
void reach_error(){}

/*
 * Recursive computation of fibonacci numbers.
 * 
 * Author: Matthias Heizmann [EDITED]
 * Date: 2013-07-13
 * 
 */

extern int __VERIFIER_nondet_int(void);


int fibonacci(int n) {
    if (n < 1) {
        return 0;
    } else if (n == 1) {
        return 1;
    } else {
        return fibonacci(n-1) + fibonacci(n-2);
    }
}


int main() {
    int x1 = __VERIFIER_nondet_int();
    int x2 = __VERIFIER_nondet_int();
    if (x1 > 46 || x1 == -2147483648 ||
        x2 > 46 || x2 == -2147483648) {
        return 0;
    }
    int result1 = fibonacci(x1);
    int result2 = fibonacci(x2);
    if ((x1 >= x2) || result1 < result2) {
        return 0;
    } else {
        ERROR: {reach_error();abort();}
    }
}
    

