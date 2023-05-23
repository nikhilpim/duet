#include "assert.h"

struct node {
    int value;
    struct node *left;
    struct node *right;
};

int arrayListSize;
int treeSize;
int NULL = 0;



void record_tree() {
    if (__VERIFIER_nondet_int()) { // if tree is NULL
        return;
    }
    record_tree(); // left
    arrayListSize = treeSize + 1;
    treeSize += 1;
    record_tree(); // right
} 

int main() {
    arrayListSize = 10;
    treeSize = 0;
    record_tree();
    __VERIFIER_assert(treeSize <= arrayListSize);
    return 0;
}