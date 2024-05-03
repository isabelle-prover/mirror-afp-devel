/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned int no_goto_proc(int n) {
while (1) {
  n = n + 1;
  if (n < 2) { return 1;} else {return 2;}
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

int while_ret_or_break_or_continue_or_goto(int a) {
  while (1) {
    if (a > 3) { 
      return 1;
    } else {
      if (a > 1) {
        a = a + 1;
        continue;
      } else if (a > 2) {
        break;
      } else {
         goto handle1;
      }
   }
 }
 handle1:
 return a;
}


unsigned int goto_proc1(int m) {
 if (m < 2) { return 1;} else {goto handle;}
handle: return 2;
}


unsigned int goto_proc(int n) {
while (1) {
  if (n < 2) { goto handle1;} else {goto handle2;}
}
handle1: goto handle2;
handle2: goto handle3;
handle3: return 1;
}
