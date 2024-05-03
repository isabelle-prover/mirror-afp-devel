/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int fac(int m) {
  if (m==1) {
     return 1;
  } else {
     return m * fac (m - 1);
  }
}

