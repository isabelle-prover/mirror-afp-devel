typedef struct { void (* op)(unsigned char *); } object_t;

void inc(unsigned char *x) { (*x)++; }

object_t objects[1] = { { .op = inc } };

unsigned char f(void) {
  unsigned char x = 0;
  objects[0].op(&x);
  return x;
}

void call_glob(unsigned char * x) {
  objects[0].op(x);
}

object_t objects2[2] = { { .op = inc }, { .op = call_glob } };


unsigned char g(unsigned n) {
  unsigned char x = 0;
  objects2[n].op(&x);
  return x;
}

/*
unsigned char obj_call(object_t* p, unsigned char n) {
  (p->op(&n));
  return n;
}
*/