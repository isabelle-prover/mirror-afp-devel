(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory simple_annotated_fn
imports "AutoCorres2.CTranslation"
begin

consts
  FACT :: "32 word \<Rightarrow> 32 word"

(* defining an appropriate FACT is left as an exercise for the reader
primrec
  "FACT 0 = 1"
  "FACT (Suc n) = Suc n * FACT n"
*)

install_C_file "simple_annotated_fn.c"

context simple_annotated_fn_simpl
begin
thm fact_body_def
thm fact_impl
end

end
