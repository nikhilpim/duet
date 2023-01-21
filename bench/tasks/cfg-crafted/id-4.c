
int id (int x) {
    if (x <= 0 || x % 2 != 0) {
        return 0;
    } else {
        return id(x - 2) + 2; // noop problems again? gets kinda fixed when base is x <= 1 but then no lower bound...
    }
}


int main() {
    int number = __VERIFIER_nondet_int(); 
    int result = id(number);
    __VERIFIER_assert((number < 0 && result == 0) || (result <= number));
}