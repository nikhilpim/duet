extern int __VERIFIER_nondet_int();
extern void abort(void); 
void reach_error(){}

int node_number;
int mem_ops;
int last_save;

void tree(int n) {
    node_number += 1;
    if (n <= 1) {
        mem_ops += (node_number - last_save);
        last_save = node_number;
        return;
    } else {
        tree((n - 1) / 2);
        tree((n - 1) / 2);
    }
}


int main() {
    node_number = 0; mem_ops = 0; last_save = 0;
    int n = __VERIFIER_nondet_int();
    tree(n);
    if (mem_ops == node_number || node_number == n + 46) {
        return 0;
    } else {
        ERROR: {reach_error();abort();}
    }
}

