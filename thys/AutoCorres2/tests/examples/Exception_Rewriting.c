/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef _Bool bool;
#define true 1
#define false 0


int foo(int i, int j) {
  while (1) {
   i = i + 1;
   }
  return i + j;
}


int g;

int cond_return(int p) {
    int result = p;                                                       
    if (p == 32 || p > 2) {
        if (p != 30 && p != 2) { 
            return result;
        }
    }
    p = foo (p, p);
    return result;
}

int cond_return1(int p) {                                                   
    int result = 0;
    while (1) {
     if (p > 2) {
       g = g + 1;
       result = 1;
       break;
     } else  {
      g = g + 2; 
      result = 2;
      break;
    }}

    if (p > 4) {
       g = g + 1;
       return 3;
    } else  {
      g = g + 2; 
     return result;
   }


}

int nested_while(int a) {

  int x = 2;
  int y = 3;
  while (1) {
    y = 4; 
    if (a > 3) {
      return 1;    
    } else {
      if (a > 1) {
        a = a + 1;
        continue;
      } else {
        while (1) {
          break;
        };
        break;
      }
   }
 }
 return x + y;
}


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

int control_flow(int n)
{
    int b;    
    int j;    
    for (j=0 ; j<n; j++ ) {
        int i;
        for (i=j; i<n; i++) {
            if (b) {
              j = 0;
              return 0;
            }
        }
    }
   return 0;
}


int control_flow_exit(int n)
{
    int result;
    int b;    
    int j;
    int i; 
    for (j=0 ; j<n; j++ ) {
        for (i=j; i<n; i++) {
            if (b) {
              j = 0;
              result = 0;
              goto exit;
            }
        }
    }
  result = j + i;
  exit: 
   return result;
}


int prop(int n) {
  return (n > 0);
}
            
bool control_flow_exit1(int n)
{
    bool result = false;
       for (; ;) {

            do                           
            {
              if (n) {
                result = true;
                goto exit;
              }
            } while (0);


               do
               {
                 if (n) {
                   goto exit;
                 }
               } while (0);
         }
    
  result = true;
  exit: 
   return result;
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

unsigned int call_fac (unsigned int n) {
  return fac (n+1) + fac (n+2);
}

int fac_exit(int n) {
  if (n < 0) {
    exit(1);
  } else if (n == 0) {
    return 0;
  } else { 
    return fac_exit (n - 1);
  };
}

int call_fac_exit (int n) {
  return fac_exit (n+1) + fac_exit (n+2);
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


unsigned int main(void) {
    unsigned int b = 0;
    b = plus(1, 2);
    b = plus(2, 3);
    return !(b);
}
 
unsigned int id(unsigned int c) {
  return c;
}

int goo(int a, int b, const unsigned int c)
{
  unsigned int ix;

  if (a) {
    if (b) {
      return -1;
    }
  } 

  for (ix = 0; ix < 1; ix++) {
    if(id(c)) {
      return -1;
    }
  }

  return 0;
}
