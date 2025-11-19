/*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned g;

unsigned read_g () {
  return g;
}

unsigned inc_g (unsigned k) {
  g = g + k;
  return g;
}


unsigned ok(unsigned k) {
  k = read_g() + read_g();
  return k;
}


unsigned reject(unsigned k) {
  unsigned result;
  result = read_g() + inc_g(k);
  return result;
}

