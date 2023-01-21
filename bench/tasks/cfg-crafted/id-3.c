
int id (int x) {
    if (x <= 0) {
        return 0;
    } else {
        return id(x - 1) + 1;
    }
}


int main() {
    int number = 3; 
    int result = id(number);
    __VERIFIER_assert(result == 3);
}