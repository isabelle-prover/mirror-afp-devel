typedef struct { void (* op)(unsigned char *); } object_t;

void inc(unsigned char *x) { (*x)++; }

object_t objects[1] = { { .op = inc } };

unsigned char f(void) {
  unsigned char x = 0;
  objects[0].op(&x);
  return x;
}