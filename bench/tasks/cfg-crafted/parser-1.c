#include "assert.h"

int end;
int start;
int processed;
char EOF;

char lexer(char* s, int slen) {
    if (slen <= 0) {return EOF;}
    char c = s[0];
    if (c == '\0') {
        end = end + 1;
        processed = processed + (end - start);
        start = end;
    } else {
        end = end + 1;
    }
    lexer(s + 1, slen - 1);
}

int main() {
        start = 0;
        end = 0;
        processed = 0;
        int slen = __VERIFIER_nondet_int();
        __VERIFIER_assume(slen > 0);
        lexer(0, slen);
        __VERIFIER_assert(start <= end);
        return 0;
}
