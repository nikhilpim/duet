extern int __VERIFIER_nondet_int();
extern void abort(void); 
void reach_error(){}

int leafs;
int internal_two;
int internal_three;

void child() {
    if (__VERIFIER_nondet_int()) {
        two();
    } else {
        three();
    }
}

void two() {
    if (__VERIFIER_nondet_int()) {
        leafs += 1;
        return;
    } else {
        internal_two += 1;
        child();
        child();
    }
}

void three() {
    if (__VERIFIER_nondet_int()) {
        leafs += 1;
        return;
    } else {
        internal_three += 1;
        child();
        child();
        child();
    }
}

int main() {
    internal_two = 0; internal_three = 0; leafs = 0;
    child();
    if (leafs == 1 + internal_two + 2 * internal_three) {
            return 0;
        } else {
            ERROR: {reach_error();abort();}
        }
}
