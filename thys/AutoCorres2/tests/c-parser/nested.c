/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef struct {
  struct {
    char t;
  } inner[1];
} nested;


char foo(void) {
  nested sarr;
  return sarr.inner[0].t;
}
