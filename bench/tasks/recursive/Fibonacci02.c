extern void abort(void); 
void reach_error(){}

/*
 * Recursive computation of fibonacci numbers.
 * 
 * Author: Matthias Heizmann
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
    int x = 9;
    int result = fibonacci(x);
    if (result == 34) {
        return 0;
    } else {
      ERROR: {reach_error();abort();}
    }
}
