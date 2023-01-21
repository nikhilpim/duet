int end;
int start;
char EOF;

char lexer(char* s, int slen) {
    if (slen <= 0) {return EOF;}
    char c = s[0];
    if (c == '\0') {
        end += 1;
        start = end;
    } else {
        end += 1;
    }
    lexer(s + 1, slen - 1);
}