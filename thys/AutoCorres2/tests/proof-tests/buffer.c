/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef struct buffer {
  char *bytes;
} buffer_t;

char * get_bytes(buffer_t * p) {
  return p->bytes;
}

char get_head(buffer_t * p) {
  return *(p->bytes);
}

void set_head(buffer_t * p, char x) {
  *(p->bytes) = x;
}

char get_2(buffer_t * p) {
  return p->bytes[2];
}


void set_2(buffer_t * p, char x) {
  p->bytes[2] = x;
}