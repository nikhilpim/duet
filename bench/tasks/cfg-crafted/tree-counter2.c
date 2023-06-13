int leafs;
int interior_seven;
int interior_four;


void seven() {
    if (__VERIFIER_nondet_int()) {
        leafs += 1;
        return;
    } else {
        interior_seven += 1;
        seven();
        seven();
        seven();
        seven();
        seven();
        seven();
        seven();
    }
}
void four() {
    if (__VERIFIER_nondet_int()) {
        seven();
    } else {
        interior_four += 1;
        four();
        four();
        four();
        four();
    }
}

int main() {
    leafs = 0; interior_four = 0; interior_seven = 0;
    four();
    if (!(leafs == (1 + 6 * interior_seven) + (3 * interior_four))) {
            ERROR: {reach_error();abort();}
        }
}