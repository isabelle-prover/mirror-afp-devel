/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

struct node {
    struct node *next;
    struct item {unsigned length; struct node* data;} item;
};

unsigned dummy(struct node * list) {
  list->item.length = list->next - list->item.data;
  return (list->item.length);
}


struct c {
  unsigned all;
};


struct componets {
  struct c c1;
  struct c c2;
};

struct globals {
  struct componets cs;
};

struct globals g;

void write_globals(void)
{
  unsigned value;
  value = 43;
  g.cs.c2.all = value;
  return;  
}