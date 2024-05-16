/*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned bar (unsigned i) {
  return i;
}
unsigned foo_(unsigned n) {
   return n;
}

unsigned foo(unsigned m) {
  return foo_(m) + bar(m);
}