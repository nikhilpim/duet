extern int __VERIFIER_nondet_int();
extern void abort(void); 
void reach_error(){}

int mem_ops;
int back_len;
int front_len;
int size;
int dequeue_empty;

void enqueue() {
    back_len = back_len + 1;
    mem_ops = mem_ops + 1;
    size = size + 1;
}

void drain() {
    if (back_len > 0) {
        front_len = front_len + 1;
        back_len = back_len - 1;
        mem_ops = mem_ops + 3;
        drain();
    }
}
void dequeue() {
    if (size <= 0) {dequeue_empty = 1;}
    if (front_len == 0) {
        drain();
    }
    size = size - 1;
    front_len = front_len - 1;
    mem_ops = mem_ops + 2;
}

void harness() {
    
    if (__VERIFIER_nondet_int()) {
        dequeue();
    } else {
        enqueue();
        enqueue();
        harness();
        harness();
    }
}

int main() {
    mem_ops = 0; back_len = 0; front_len = 0; size = 0; dequeue_empty = 0;
    enqueue();
    harness();
    
    if (dequeue_empty == 0) {return 0;} 
        else {
            ERROR: {reach_error();abort(); return -1;}
        }
}