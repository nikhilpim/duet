#include "assert.h"

int lock;
int lock_owner; 
int lock_releaser;

void acquire_lock(int owner) {
    __VERIFIER_assert(lock == 0);
    lock += 1;
    lock_owner = owner;
}

void release_lock(owner) {
    __VERIFIER_assert(lock_owner == owner);
    lock_releaser = owner;
    lock -= 1;
}

void thread1() {
    acquire_lock(1);
    //work
    release_lock(1);
}

void thread2() {
    acquire_lock(2);
    release_lock(2);
}

void selector() {
    if (__VERIFIER_nondet_int()) {return;}
    if (__VERIFIER_nondet_int()) {
        thread1();
    } else {
        thread2();
    }
}


int main() {
    lock = 0;
    selector();
    __VERIFIER_assert(lock == 0 && lock_releaser == lock_owner);
}