extern int __VERIFIER_nondet_int();
extern void abort(void); 
void reach_error(){}

int leafs;
int internal_nodes;

void tree_count(int n) {
    if (n <= 1) {
        leafs += 1;
    } else {
        internal_nodes += 1;
        tree_count((n - 1) / 2);
        tree_count((n - 1) / 2);
    }
}

int main() {
    leafs = 0; internal_nodes = 0;
    int n = __VERIFIER_nondet_int();
    tree_count(n);
    if (internal_nodes + 1 == leafs || internal_nodes == n + 46) {
            return 0;
        } else {
            ERROR: {reach_error();abort();}
        }
}

