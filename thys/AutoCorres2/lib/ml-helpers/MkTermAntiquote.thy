(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

chapter "ML Antiquotations"

section "Building terms: \<open>mk_term\<close>"

theory MkTermAntiquote
imports
  Pure
begin
text \<open>
  \<open>mk_term\<close>: ML antiquotation for building and splicing terms.

  See \<^file>\<open>MkTermAntiquote_Tests.thy\<close> for examples and tests.
\<close>

(* Simple wrapper theory for historical reasons. *)
ML_file "mkterm_antiquote.ML"

end