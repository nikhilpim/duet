#include "assert.h"

int id (int x) {
    if (x <= 0) {
        return 0;
    } else {
        return id(x - 1) + 1;
    }
}


int main() {
    int number = __VERIFIER_nondet_int(); 
    int result = id(number);
    __VERIFIER_assert(
        (number < 0 && result == 0) || 
        (result == number));
}