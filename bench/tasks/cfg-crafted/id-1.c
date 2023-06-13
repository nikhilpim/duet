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
    int number = __VERIFIER_nondet_int(); 
    int result = id(number);
    if (!(
        (number < 0 && result == 0) || 
        (result == number ))) {
            ERROR: {reach_error();abort();}
        }
    // __VERIFIER_assert(
    //     (number < 0 && result == 0) || 
    //     (result == number ));
}