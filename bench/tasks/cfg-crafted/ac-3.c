
int a(int x) {
    if (x <= 0) {
        return 0;
    } else {
        return 1 + b(x);
    }
}

int b (int x) {
    if (x <= 0) {return 0;}
    return a(x - 1); // issue is that delta -= x - 1 \/ noop means that paramb - parama doesn't reliably decrement
}

int main() {
    int input = __VERIFIER_nondet_int();
    int result = a(input);
    __VERIFIER_assert((input < 0 && result == 0) || (result <= input+1));
}