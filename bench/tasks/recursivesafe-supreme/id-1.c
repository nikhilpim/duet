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
    int n = __VERIFIER_nondet_int(); 
    if (n < 0 || n > 1073741823) {
        return 0;
    }
    int result = id(n);
    if (result == n ) {return 0;} 
        else {
            ERROR: {reach_error();abort(); return -1;}
        }
}