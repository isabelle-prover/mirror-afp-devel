/*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */


void inc (unsigned* y) {
  *y = *y + 1;
}

void call_inc_ptr(unsigned *p) {
  inc(p);
}
