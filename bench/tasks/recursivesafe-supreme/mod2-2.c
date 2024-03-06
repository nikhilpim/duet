extern int __VERIFIER_nondet_int();
extern void abort(void); 
void reach_error(){}

int mod2 (int x) {
    if (x == 0) {
        return 0;
    } else if (x == 1) {
        return 1;
    } else {
        return mod2(x - 2);
    }
}


int main() {
    int n = __VERIFIER_nondet_int(); 
    if (n < 0 || n > 1073741823) {
        return 0;
    }
    int result1 = mod2(n);
    int result2 = mod2(n + 1);
    if (result1 == !result2 ) {return 0;} 
        else {
            ERROR: {reach_error();abort(); return -1;}
        }
}