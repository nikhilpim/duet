#include "assert.h"

int a;
int b;
int tmp;

void foo() {
    if (__VERIFIER_nondet_int()) {
        return;
    } else {
        a = a + 1;
        foo();
        b = b + 1;

    }
}

int main() {
    a = 0;
    b = 0;
    foo();
    __VERIFIER_assert(a == b);
}