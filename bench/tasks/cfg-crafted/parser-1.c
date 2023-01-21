int start;
int end; 
char EOF = -1;

char lexer() {
    char c = __VERIFIER_nondet_char();
    if (c == '\0') {
        end += 1;
        start = end;
    } else {
        end += 1;
    }
    return c;
}

void parser() {
    char token[10];
    int i = 0;
    char next = lexer();
    while (next != '\0') {
        token[i] = next;
        i++;
        next = lexer();
    }

    // do something with token

    if (*token == EOF) {
        return;
    } else {
        parser();
    }
}

int main() {
    start = __VERIFIER_nondet_int();
    end = start;
    parser();
    __VERIFIER_assert(start <= end);
    return 0;
}