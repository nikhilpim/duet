#include "assert.h"

int global_lock;
int reentrant_lock; 

void acquire_reentrant_lock() {
    __VERIFIER_assert(global_lock == 1);
    reentrant_lock += 1;
}

void release_reentrant_lock() {
    reentrant_lock -= 1;
}

void parent() {
    global_lock += 1;
    while (__VERIFIER_nondet_int()) {
        child();
    }
    global_lock -= 1;
}

void child() {
    acquire_reentrant_lock();
    // work
    release_reentrant_lock();
}

int main() {
    global_lock = 0;
    reentrant_lock = 0;
    parent();
    __VERIFIER_assert(global_lock == 0 && reentrant_lock == 0);

}