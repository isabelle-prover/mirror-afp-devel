(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Less_Monad_Syntax (* use instead of HOL-Library.Monad_Syntax *)
  imports "HOL-Library.Monad_Syntax"
begin

(* remove >> from Monad_Syntax, clashes with word shift *)
no_syntax
  "_thenM" :: "['a, 'b] \<Rightarrow> 'c" (infixr \<open>>>\<close> 54)

(* remove input version of >>= from Monad_Syntax, avoid clash with NonDetMonad *)
no_notation
  Monad_Syntax.bind (infixr \<open>>>=\<close> 54)

(* use ASCII >>= instead of \<bind> *)
notation (output)
  bind_do (infixl \<open>>>=\<close> 54)


(* enable pretty printing for do { .. } syntax globally *)
translations
  "CONST bind_do" <= "CONST bind"

end
