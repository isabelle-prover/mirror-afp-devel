/*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef enum {
    Good = 2,
    Bad = 4,
} return_t;

typedef return_t (*handler_t)(void *content);

typedef struct implementation {
    handler_t my_handler;
} implementation_t;

static return_t worker(handler_t my_handler)
{
	return Bad;
}

void bar (const handler_t implementation)
{
	return_t status = Bad;
	status = worker(implementation);
}

/*
Currently fails as function pointer is hidden (nested) inside structure implementation_t
*/
/*

void foo (const implementation_t *implementation)
{
	return_t status = Bad;
	status = worker(implementation->my_handler);
}

*/