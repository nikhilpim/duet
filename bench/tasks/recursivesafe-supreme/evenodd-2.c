extern int __VERIFIER_nondet_int();
extern void abort(void); 
void reach_error(){}

int is_odd (int x) {
    if (x == 0) {
        return 0;
    } else if (x == 1) {
        return 1;
    } else {
        return is_even(x - 1);
    }
}

int is_even (int x) {
    if (x == 0) {
        return 1;
    } else if (x == 1) {
        return 0;
    } else {
        return is_odd(x - 1);
    }
}


int main() {
    int n = __VERIFIER_nondet_int(); 
    if (n < 0 || n > 1073741823) {
        return 0;
    }
    int result = is_even(n);
    if (result == !(n % 2)) {return 0;} 
        else {
            ERROR: {reach_error();abort(); return -1;}
        }
}