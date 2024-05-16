/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
unsigned int exit(unsigned int);
*/


void just_exit(void) {
    exit(1);
}


void call_exit(void) {
  just_exit();
}


int ret_or_throw(int a) {
  if (a > 2) { 
    return 3;
  } else {
    exit(1);
 }
}

int while_ret_or_break_or_continue(int a) {
  while (1) {
    if (a > 3) { 
      return 1;
    } else {
      if (a > 1) {
        a = a + 1;
        continue;
      } else {
        break;
      }
   }
 }
 return a;
}


int while_comb(int a) {
  int x = a;
  x = 2 * x;
  if (x < 30) {
    x = x - 1;
  } else {
    x = x + 1;
  }

  while (1) {
    if (a > 3) { 
      return 1;
    } else {
      if (a > 1) {
        a = a + 1;
        continue;
      } else {
        break;
      }
   }
 }
 return x;
}

int while_comb_exit(int a) {
  int x = a;
  x = 2 * x;
  if (x < 30) {
    x = x - 1;
  } else {
    x = x + 1;
  }

  while (1) {
    if (a > 3) { 
      return 1;
    } else {
      if (a > 1) {
        a = a + 1;
        continue;
      } else {
        exit(1);
      }
   }
 }
 return x;
}



int while_ret_or_throw(int a) {
  while (1) {
    if (a > 3) { 
      return 1;
    } else {
      if (a > 1) {
        exit(1);
      } else {
        break;
      }
   }
 }
 return 2;
}



unsigned int plus(unsigned int a, unsigned int b) {
    return a + b;
}

unsigned int plus2(unsigned int a, unsigned int b) {
    while (b > 0) {
        a += 1;
        b -= 1;
    }
    return a;
}



unsigned int call_plus(void) {
   unsigned int n = 0;
   n = plus (2, 3);
   return n;
}


unsigned int fac(unsigned int n) {
  if (n == 0) {
    return 0;
  } else { 
    return fac (n - 1);
  };
}


unsigned int fac_exit(unsigned int n) {
  if (n < 0) {
    exit(1);
  } else if (n == 0) {
    return 0;
  } else { 
    return fac_exit (n - 1);
  };
}

unsigned int odd(unsigned int);
unsigned int even(unsigned int n) {
  if (n == 0) {
     return 1;
  } else {
    return (! (odd(n - 1)));
  }
}

unsigned int odd(unsigned int n) {
  if (n == 0) {
     return 0;
  } else {
    return (! (even(n - 1)));
  }
}




int main(int argc, char **argv) {
    int b = 0;
    b = plus(1, 2);
    b = plus(2, 3);
    return !(b);
}
