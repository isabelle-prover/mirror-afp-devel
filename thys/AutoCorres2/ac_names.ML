(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

structure AC_Names =
struct
  open NameGeneration
  val new_heap_recN = "lifted_globals"
  val heap_typingN = "heap_typing"
end