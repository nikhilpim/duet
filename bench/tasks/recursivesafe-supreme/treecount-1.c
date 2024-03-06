extern int __VERIFIER_nondet_int();
extern void abort(void); 
void reach_error(){}

int leafs;
int internal_nodes;

void tree_count() {
    if (__VERIFIER_nondet_int()) {
        leafs += 1;
    } else {
        internal_nodes += 1;
        tree_count();
        tree_count();
    }
    return;
}

int main() {
    leafs = 0; internal_nodes = 0;
    tree_count();
    if (internal_nodes + 1 == leafs) {
            return 0;
        } else {
            ERROR: {reach_error();abort();}
        }
}

