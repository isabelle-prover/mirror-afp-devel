/*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned reject_overlap(unsigned x, unsigned y) {
  x = x + 1; /* ok */
  ++x = x;
  return x;
}