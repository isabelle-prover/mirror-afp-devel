/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

void inc (unsigned* y) {
  *y = *y + 1;
}

unsigned inc_ref (unsigned y) {
  return y + 1;
}

unsigned g;

void call_inc(void) {
  inc(&g);
}

void call_inc_ref(void) {
  g = inc_ref(g);
}

