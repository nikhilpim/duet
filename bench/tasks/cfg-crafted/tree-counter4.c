extern int __VERIFIER_nondet_int();
extern void abort(void); 
void reach_error(){}

int leafs1;
int leafs2;

void tree_count() {
    if (__VERIFIER_nondet_int()) {
        leafs1 += 1;
    } else {
        tree_count();
        while (__VERIFIER_nondet_int()) {
            leafs2 += 1;
            tree_count();
        }
    }
    return;
}

int main() {
    leafs1 = 0; leafs2 = 1;
    tree_count();
    if (!(leafs1 == leafs2)) {
            ERROR: {reach_error();abort();}
        }
    return 0;
}

