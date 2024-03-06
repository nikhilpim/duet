extern void abort(void); 
void reach_error(){}

/*
 * Implementation the McCarthy 91 function.
 * http://en.wikipedia.org/wiki/McCarthy_91_function
 * 
 * Author: Matthias Heizmann
 * Date: 2013-07-13
 * 
 */

extern int __VERIFIER_nondet_int(void);


int f91(int x) {
    if (x > 100)
        return x -10;
    else {
        return f91(f91(x+11));
    }
}


int main() {
    int x1 = __VERIFIER_nondet_int();
    int x2 = __VERIFIER_nondet_int();
    int result1 = f91(x1);
    int result2 = f91(x2);
    if ((x1 > x2) || result1 <= result2) {
        return 0;
    } else {
      ERROR: {reach_error();abort();}
    }
}
