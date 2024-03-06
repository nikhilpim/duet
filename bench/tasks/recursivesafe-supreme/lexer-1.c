extern int __VERIFIER_nondet_int();
extern int __VERIFIER_nondet_array();
extern void abort(void); 
void reach_error(){}

int end;
int start;
int processed;
char EOF;

char lexer(int slen) {
    if (slen <= 0) {return EOF;}
    if (__VERIFIER_nondet_int()) {
        end = end + 1;
        processed = processed + (end - start);
        start = end;
    } else {
        end = end + 1;
    }
    lexer(slen - 1);
}

int main() {
        int array_start = __VERIFIER_nondet_int();
        start = array_start;
        end = array_start;
        processed = 0;
        int slen = __VERIFIER_nondet_int();
        if (slen <= 0) {
            return 0;
        }
        lexer(slen);
        if (start <= end) {
            return 0;
        } else {
            ERROR: {reach_error();abort();}
        }
}
