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
    int m = __VERIFIER_nondet_int(); 
    int n = __VERIFIER_nondet_int(); 
    if (m <= 0 || m > 2147483647 ||
        n <= 0 || n > 2147483647) {
        return 0;
    }

    int result1 = paths_through_grid(m, n);
    int result2 = paths_through_grid(n, m);
    if (result1 == result2) {return 0;} 
        else {
            ERROR: {reach_error();abort(); return -1;}
        }
}