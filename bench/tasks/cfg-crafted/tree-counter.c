
int leafs;
int internal_nodes;


void tree_count() {
    if (__VERIFIER_nondet_int()) {
        leafs += 1;
        return; 
    } else {
        internal_nodes += 1;
        tree_count();
        tree_count();
        return;
    }
}

int main() {
    leafs = 0;
    internal_nodes = 0;
    tree_count();
    __VERIFIER_assert(internal_nodes + 1 == leafs);
    return 0;
}
