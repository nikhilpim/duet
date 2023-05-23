#include "assert.h"

int last_access;

void random_sample(int x) {
    if (__VERIFIER_nondet_int()) {
        random_sample(x + 4);
    }
    else if (__VERIFIER_nondet_int()) {
        random_sample(x + 32);
    }
    else if (__VERIFIER_nondet_int()) {
        random_sample(x + 12);
    } else {
        last_access = x;
    }
}

int main() {
    random_sample(0);
    __VERIFIER_assert(last_access % 4 == 0);
}







