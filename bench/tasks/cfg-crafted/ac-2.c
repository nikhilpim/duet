
int a(int x) {
    if (x <= 0) {
        return 0;
    } else {
        return 1 + b(x - 1);
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
    int input = 3;
    int result = a(input);
    __VERIFIER_assert(result <= 6);
}