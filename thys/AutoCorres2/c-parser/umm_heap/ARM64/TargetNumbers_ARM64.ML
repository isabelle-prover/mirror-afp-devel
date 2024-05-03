(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 * Based on https://developer.apple.com/library/archive/documentation/Xcode/Conceptual/iPhoneOSABIReference/Articles/ARM64FunctionCallingConventions.html
 *)

structure ImplementationNumbersARM64 : IMPLEMENTATION_NUMBERS =
struct

open IntInf

fun exp (n, ex) = if ex = 0 then 1
                  else let
                      val q = ex div 2
                      val r = if ex mod 2 = 1 then n else 1
                      val qex = exp (n, q)
                    in
                      qex * qex * r
                    end

val boolWidth = fromInt 8
val charWidth = 8
val shortWidth = 16
val intWidth = 32
val longWidth = 64
val llongWidth = 64
val int128Width = 128
val ptrWidth : int = 64
val ptr_t = BaseCTypes.Long
val CHAR_BIT : int = 8

fun umax width = exp(2, width) - 1
fun max width = exp(2, width - 1) - 1
fun min width = ~(exp(2, width - 1))

val UCHAR_MAX = umax charWidth
val USHORT_MAX = umax shortWidth
val UINT_MAX = umax intWidth
val ULONG_MAX = umax longWidth
val ULLONG_MAX = umax llongWidth
val UINT128_MAX = umax int128Width

val SCHAR_MAX = max intWidth
val SHORT_MAX = max shortWidth
val INT_MAX = max intWidth
val LONG_MAX = max longWidth
val LLONG_MAX = max llongWidth
val INT128_MAX = max int128Width

val SCHAR_MIN = min charWidth
val SHORT_MIN = min shortWidth
val INT_MIN = min intWidth
val LONG_MIN = min longWidth
val LLONG_MIN = min llongWidth
val INT128_MIN = min int128Width

(* in Darwin char is signed! *)
val char_signedp = true

val CHAR_MAX = SCHAR_MAX
val CHAR_MIN = SCHAR_MIN

open CharLitUtil

val charliteral_conversion = schar_conv { umax=UCHAR_MAX, smin=SCHAR_MIN, smax=SCHAR_MAX }

end
