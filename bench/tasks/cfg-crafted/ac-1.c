
int a(int x) {
    if (x <= 0) {
        return 0;
    } else {
        return 1 + b(x - 1); // Unclear if x/2 is even a valid potential, so maybe the implementation isn't even wrong
    }
}

int b (int x) {
    if (x <= 0) {
        return 0;
    } else {
        return 1 + a(x - 1);
    }
}

int main() {
    int input = __VERIFIER_nondet_int();
    int result = a(input);
    __VERIFIER_assert((input < 0 && result == 0) || (result <= 2 * input));
}