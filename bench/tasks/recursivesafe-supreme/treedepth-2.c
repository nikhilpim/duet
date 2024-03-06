extern int __VERIFIER_nondet_int();
extern void abort(void); 
void reach_error(){}

int leafs;
int current_depth;
int max_depth; 

void treedepth() {
    if (max_depth < current_depth) {
        max_depth = current_depth;
    }
    if (__VERIFIER_nondet_int()) {
        leafs += 1;
    } else {
        current_depth += 1;
        treedepth();
        treedepth();
        current_depth -= 1;
    }
    return;
}

int main() {
    leafs = 0; current_depth = 1; max_depth = 0;
    treedepth();
    if ((max_depth > 10) || leafs < 1024) { // 2^25  = 33554432
            return 0;
        } else {
            ERROR: {reach_error();abort();}
        }
}

