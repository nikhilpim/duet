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

int binomial(int n, int k) {
    if (n < k) {
        return 0;
    } else if (n == k || n == 0) {
        return 1;
    } else {
        return binomial(n - 1, k - 1) + binomial(n - 1, k);
    }
}

int main() {
    int m = __VERIFIER_nondet_int(); 
    int n = __VERIFIER_nondet_int(); 
    if (m <= 0 || m > 2147483647 ||
        n <= 0 || n > 2147483647) {
        return 0;
    }

    int actual = paths_through_grid(m, n);
    int expected = binomial(m + n, m);
    if (actual == expected) {return 0;} 
        else {
            ERROR: {reach_error();abort(); return -1;}
        }
}