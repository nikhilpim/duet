extern int __VERIFIER_nondet_int();
extern void abort(void); 
void reach_error(){}

int partition (int n, int m) {
    if (n == 0) {
        return 1;
    } else if (n < 0 || m == 0) {
        return 0;
    } else {
        return partition(n-m, m) + (n, m - 1);
    }
}


int main() {
    int n1 = __VERIFIER_nondet_int(); 
    int n2 = __VERIFIER_nondet_int(); 
    int m = __VERIFIER_nondet_int(); 
    if (n1 < 0 || n1 > 1073741823 ||
        n2 < 0 || n2 > 1073741823 ||
        m < 0 || m > 1073741823) {
        return 0;
    }
    int step1 = partition(n1, m);
    int step2 = partition(n2, m);
    int total = partition(n1 + n2, m);
    if (step1 + step2 < total) {return 0;} 
        else {
            ERROR: {reach_error();abort(); return -1;}
        }
}