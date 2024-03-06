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
    int n = __VERIFIER_nondet_int(); 
    if (m1 <= 0 || m1 > 2147483647 ||
        m2 <= 0 || m2 > 2147483647 ||
        n <= 0 || n > 2147483647) {
        return 0;
    }

    int result1 = paths_through_grid(m1, n);
    int result2 = paths_through_grid(m2, n);
    if ((m1 >= m2) || result1 < result2) {return 0;} 
        else {
            ERROR: {reach_error();abort(); return -1;}
        }
}