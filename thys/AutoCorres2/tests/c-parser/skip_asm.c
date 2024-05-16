/*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned asm_stmts(unsigned x, unsigned y) {
  unsigned r = x;
  asm volatile("some assembler instruction 1": "=r"(y): "r"(x),"r"(y) );
  asm volatile("some assembler instruction 2");
  r = r + y;
  asm volatile("just_a_label:");
  return r + x;
}

