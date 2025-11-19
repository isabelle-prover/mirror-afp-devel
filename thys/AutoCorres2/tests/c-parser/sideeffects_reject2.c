/*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned reject_overlap(unsigned x, unsigned y) {
  unsigned result = 0;
  result = x++ + x + y;
  return result;
}