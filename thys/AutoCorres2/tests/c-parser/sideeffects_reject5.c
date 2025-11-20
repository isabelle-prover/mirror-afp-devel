/*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned reject_overlap(unsigned x, unsigned y) {
  y = x++ + x; /* reject */
  return y;
}