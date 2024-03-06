extern int __VERIFIER_nondet_int();
extern void abort(void); 
void reach_error(){}

int id (int x) {
    if (x <= 0) {
        return 0;
    } else {
        return id(x - 1) + 1;
    }
}


int main() {
    int n1 = __VERIFIER_nondet_int(); 
    int n2 = __VERIFIER_nondet_int(); 
    if (n1 < 0 || n1 > 1073741823 ||
        n2 < 0 || n2 > 1073741823) {
        return 0;
    }
    int result1 = id(n1);
    int result2 = id(n2);
    if ((n1 >= n2) || result1 < result2) {return 0;} 
        else {
            ERROR: {reach_error();abort(); return -1;}
        }
}