/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned long bit_shuffle(unsigned long x){
  unsigned  zero, one, two, three, four, five, six, seven, eight, nine, a, b, c, d, e, f, g;
  zero   = x & 0x1;
  one    = (x >> 1) & 0x1;
  two    = (x >> 2) & 0x1;
  three  = (x >> 3) & 0x1;
  four   = (x >> 4) & 0x1;
  five   = (x >> 5) & 0x1;
  six    = (x >> 6) & 0x1;
  seven  = (x >> 7) & 0x1;
  eight  = (x >> 8) & 0x1;
  nine   = (x >> 9) & 0x1;
  a      = (x >> 10) & 0x1;
  b      = (x >> 11) & 0x1;
  c      = (x >> 12) & 0x1;
  d      = (x >> 13) & 0x1;
  e      = (x >> 14) & 0x1;
  f      = (x >> 15) & 0x1;
  g      = (x >> 16) & 0x1;
  unsigned  term[60];
  unsigned long sum = 0;


  term[0] = ((g & one   & g)<< 1) ;
  term[1] = ((f & two   & g)<< 2) ;
  term[2] = ((e & three & g)<< 3) ;
  term[3] = ((d & four  & g)<< 4) ;
  term[4] = ((c & five  & g)<< 5) ;
  term[5] = ((b & six   & g)<< 6) ;
  term[6] = ((a & seven & g)<< 7) ;
  term[7] = ((g & eight & g)<< 8) ;
  term[8] = ((f & nine  & g)<< 9) ;
  term[9] = ((e & one   & g)<< 1) ;
  term[10]= ((d & two   & g)<< 2) ;
  term[11]= ((c & three & g)<< 3) ;
  term[12]= ((b & four  & g)<< 4) ;
  term[13]= ((a & five  & g)<< 5) ;
  term[14]= ((g & six   & g)<< 6) ;
  term[15]= ((f & seven & g)<< 7) ;
  term[16]= ((e & eight & g)<< 8) ;
  term[17]= ((d & nine  & g)<< 9) ;
  term[18]= ((c & a     & g)<< 1) ;
  term[19]= ((b & b     & g)<< 2) ;
  term[20]= ((a & c     & g)<< 3) ;
  term[21]= ((g & d     & g)<< 4) ;
  term[22]= ((f & e     & g)<< 5) ;
  term[23]= ((e & f     & g)<< 6) ;
  term[24]= ((d & one   & g)<< 7) ;
  term[25]= ((c & two   & g)<< 8) ;
  term[26]= ((b & three & g)<< 9) ;
  term[27]= ((a & four  & g)<< 1) ;
  term[28]= ((g & five  & g)<< 2) ;
  term[29]= ((f & six   & g)<< 3) ;
  term[30]= ((e & seven & g)<< 4) ;

for (unsigned  i=31; i<60; i++) {
   term[i] = ((f & e     & d)<< 5);
}

  for (unsigned  i=0; i<60; i++) {
     sum += term[i];
  }

  return sum;
}
