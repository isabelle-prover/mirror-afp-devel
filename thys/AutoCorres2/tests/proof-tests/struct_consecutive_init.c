/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef struct POINT {
    int a; 
    int b; 
} POINT;

typedef struct LINE {
   POINT from;
   POINT to;
} LINE;

int G;

int same(int n) {
  return n;
};

int glob_add(int n, int m) {
  G = G + n + m;
};


int in_loop(int n, int m, int k) {
  POINT p0;
  int i;
  for (i = 0; i <= n; i++) {
     p0.a = 0;
     p0.b = 0;
     if (i==2) {G = p0.a;} else {G = p0.b;}
  }
  return G;
}

int in_loop_nested(int n, int m, int k) {
  LINE l0;
  int i;
  for (i = 0; i <= n; i++) {
     l0.from.a = 0;
     l0.from.b = 0;
     l0.to.a = 0;
     l0.to.b = 0;
     if (i==2) {G = l0.from.a;} else {G = l0.to.b;}
  }
  return G;
}

int in_loop_partial(int n, int m, int k) {
  POINT p0;
  int i;
  for (i = 0; i <= n; i++) {
     p0.a = 0;
     if (i==2) {G = p0.a;} else {G = 23;}
  }
  return G;
}

int partial_declare_before_use(int n, int m, int k) {
  POINT p;
  int l1 = 0;
  int l2 = 0;

  p.a = same(n);
  l1 = p.a;
  p.b = same(m);
  l2 = p.b;

  glob_add(l1, l2);
  return G;
};

int nested(int n, int m, int k) {
  LINE l;

  l.from.a = same(n);
  l.from.b = 1;
  l.to.a = 1;
  l.to.b = same(n);

  glob_add(l.from.a, l.to.b);
  return G;
};

int nested_partial(int n, int m, int k) {
  LINE l;

  l.from.a = same(n);
  l.to.b = same(n);

  glob_add(l.from.a, l.to.b);
  return G;
};

int string_of_vars(int n) {
    int n1, n2, n3, n4, n5;
    n1 = n;
    n2 = n1;
    n3 = n2;
    n4 = n3;
    n5 = n4;
    return n5;
};

int string_of_vars_explode(int n, int m, int k) {
    int n1, n2, n3, n4, n5;
    n1 = n + k;
    n2 = n1 + m * n + 2;
    n3 = n2 + k + n;
    n4 = n3 + m * n + 2;
    n5 = n2 + n * k;
    return n5;
};

void crosswise_init() {
  unsigned i;
  POINT src, dst;

 for(i = 0; i <= 2; i++ ) {
    src.a = 33;
    dst.a = 42;
    src.b = 8;  
    dst.b = 8;
  }

  return;
}

POINT cond_init(unsigned i) {
  POINT src;
  src.a = 33;
  if (i < 42) {
    src.b = 44;
  } else {
    src.b = 42;
  }
  return src;
}

POINT cond_init1(unsigned i) {
  POINT src;
  if (i < 42) {
    src.b = 44;
  } else {
    src.b = 42;
  }
  src.a = 33;
  return src;
}

POINT swap (POINT p) {
  return (POINT) {p.b, p.a};
};

unsigned cond_init_while (unsigned i) {
  POINT src;
  POINT dst;
  unsigned x = 0;
  while (i < 100) {
    if (i < 42) {
      src.a = i + 2;
      dst.a = i + 3;
    } else {
      src.a = i + 3;
      dst.a = x + 2;
    }
    src.b = i;
    dst.b = i;
    x = x + i + src.a + dst.b + src.b + dst.a;
    i = i + 1;
  }
  return (x);
}

unsigned cond_init_while_nested (unsigned i) {
  POINT src;
  LINE dst;
  unsigned x = 0;
  while (i < 100) {
    if (i < 42) {
      src.a = i + 2;
      dst.from.a = i + 3;
      dst.to.a = i + 4;
    } else {
      src.a = i + 3;
      dst.from.a = i + 4;
      dst.to.a = i + 5;
    }
    src.b = i;
    dst.from.b = i;
    dst.to.b = i;
    x = x + i + src.a + dst.from.a + dst.from.b + src.b + dst.to.a + dst.to.b;
    i = i + 1;
  }
  return (x);
}

unsigned cond_init_while_incomplete (unsigned i) {
  POINT src;
  POINT dst;
  unsigned x = 0;
  while (i < 100) {
    if (i < 42) {
      src.a = i + 2;
      dst.a = i + 3;
    } else {
      src.a = i + 3;
      dst.a = x + 2;
    }
    src.b = i;

    x = x + i + src.a + dst.b + src.b + dst.a;
    i = i + 1;
  }
  return (x);
}

unsigned cond_init_while3 (unsigned i) {
  POINT src;
  POINT dst;
  POINT three;
  unsigned x = 0;
  while (i < 100) {
    if (i < 42) {
      src.a = i + 2;
      dst.a = i + 3;
      three.a = i + 4;
    } else {
      src.a = i + 3;
      dst.a = x + 2;
      three.a = i + 5;
    }
    src.b = i;
    dst.b = i;
    three.b = i;
    x = x + i + src.a + dst.b + src.b + dst.a + three.a + three.b;
    i = i + 1;
  }
  return (x);
}

unsigned cond_init_while4 (unsigned i) {
  POINT src;
  POINT dst;
  POINT three;
  POINT four;
  unsigned x = 0;
  while (i < 100) {
    if (i < 42) {
      src.a = i + 2;
      dst.a = i + 3;
      three.a = i + 4;
      four.a = i + 6;
    } else {
      src.a = i + 3;
      dst.a = x + 2;
      three.a = i + 5;
      four.a = i + 7;
    }
    src.b = i;
    dst.b = i;
    three.b = i;
    four.b = i;
    x = x + i + src.a + dst.b + src.b + dst.a + three.a + three.b + four.a + four.b;
    i = i + 1;
  }
  return (x);
}

unsigned cond_explode (unsigned i) {
  POINT x;
  unsigned result = 0;
  if (i > 1) { 
    x.a = i;
  } else {
    x.a = i + 1;
  }

  if (i > 3) {
    result = 2;
  }
  
  if (i > 4) {
    result = 4;
  };
  
  if (i > 5) {
    result = 5;
  };

  if (i > 6) {
    result = 6;
  };

  x.b = 42;

  if (i > 7) {
    result = 7;
  };

  if (i > 8) {
    result = 8;
  };

  if (i > 9) {
    result = 9;
  };

  if (i > 10) {
    result = 10;
  };


  if (i > 11) {
    result = 11;
  };


  if (i > 12) {
    result = 12;
  };


  if (i > 13) {
    result = 13;
  };

  return result + x.a + x.b;
}


