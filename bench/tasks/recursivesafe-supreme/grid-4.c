extern int __VERIFIER_nondet_int();
extern void abort(void); 
void reach_error(){}

int paths_through_grid (int x, int y) {
    if (x == 0) {
        return 1;
    } else if (y == 0) {
        return 1;
    } else {
        return paths_through_grid(x - 1, y) + paths_through_grid(x, y - 1);
    }
}

int main() {
    int m1 = __VERIFIER_nondet_int(); 
    int m2 = __VERIFIER_nondet_int(); 
    int n1 = __VERIFIER_nondet_int(); 
    int n2 = __VERIFIER_nondet_int(); 
    if (m1 <= 0 || m1 > 2147483647 ||
        m2 <= 0 || m2 > 2147483647 ||
        n1 <= 0 || n1 > 2147483647 ||
        n2 <= 0 || n2 > 2147483647) {
        return 0;
    }

    int step1 = paths_through_grid(m1, n1);
    int step2 = paths_through_grid(m2, n2);
    int bigstep = paths_through_grid(m1+m2, n1+n2);
    if (step1 + step2 <= bigstep) {return 0;} 
        else {
            ERROR: {reach_error();abort(); return -1;}
        }
}