extern int __VERIFIER_nondet_int();
extern void abort(void); 
void reach_error(){}

int id(int x) {
  if (x<=0) return 0;
  return id(x-1) + 1;
}

int main(void) {
  int input = 36;
  int result = id(input);
  if (result != 36) {
    ERROR: {reach_error();abort();}
  }
}
