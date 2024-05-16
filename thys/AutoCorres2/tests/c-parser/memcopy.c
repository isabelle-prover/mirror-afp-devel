/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */


typedef unsigned char u8_t;
typedef unsigned int size_t;

u8_t *
memcpy_u8(void *dst, const void *src, size_t size)
{
    for (size_t i = 0; i < size; i++) {
        dst[i] = src[i];
    }

    return dst;
}

void *
memcpy_void(void *dst, const void *src, size_t size)
{
    for (size_t i = 0; i < size; i++) {
        ((u8_t *) dst)[i] = ((const u8_t *) src)[i];
    }

    return dst;
}


