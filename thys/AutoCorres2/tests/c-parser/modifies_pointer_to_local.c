/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned char read_ref(unsigned char b) {
	return *&b;
}

unsigned char read_ref2(unsigned char b) {
  return read_ref(b);
}