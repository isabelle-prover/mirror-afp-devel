/*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef unsigned int uint;
typedef __int128 int128;
typedef unsigned __int128 uint128;

int128 i(int i, int j)
{
  uint r = ((int128) i) * j;

  return r;
}


uint128 u(uint i, uint j)
{
  uint128 r = (uint128) i * j;

  return r;
}
