extern int __VERIFIER_nondet_int();
extern void abort(void); 
void reach_error(){}

int node_number;
int mem_ops;
int last_save;

void tree() {
    node_number += 1;
    if (__VERIFIER_nondet_int()) {
        mem_ops += (node_number - last_save);
        last_save = node_number;
        return;
    } else {
        mem_ops += 1;
        tree();
        mem_ops += 1;
        tree();
    }
}


int main() {
    node_number = 0; mem_ops = 0; last_save = 0;
    tree();
    if (mem_ops <= 2 * node_number) {
        return 0;
    } else {
        ERROR: {reach_error();abort();}
    }
}

