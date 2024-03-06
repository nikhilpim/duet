extern int __VERIFIER_nondet_int();
extern void abort(void); 
void reach_error(){}

int unaligned_access; 
void access(int x) {
    if (x % 4 != 0) {
        unaligned_access = 1;
    }
}

int prog (int a, int b) {
    if (b == 1) {
        access(a + 9); 
    } else if (b == 2) {
        access(2 * a);
    } else if (b == 3) {
        access(a + b);
    }

    if (__VERIFIER_nondet_int()) {
        prog(a + 1, b ^ 1);
        prog(a + 2, b ^ 2);
    }
}


int main() {
    unaligned_access = 0;
    int a = __VERIFIER_nondet_int(); 
    int b = a % 2 + 2 * ((a % 4) < 3);
    prog(a, b);

    if (unaligned_access != 1) {
        return 0;
    } else {
        ERROR: {reach_error();abort(); return -1;}
    }
}