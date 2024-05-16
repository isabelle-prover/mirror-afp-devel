/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
void exit(int status);
*/
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
  int st = 42;
  exit(st);
};

