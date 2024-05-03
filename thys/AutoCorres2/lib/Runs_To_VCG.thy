(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
Verification condition generator (VCG) for the runs_to predicate.

Includes also automation to add assumptions marked with SIMP_ASSM, LINARITH_ASSM etc to the
corresponding databases.
*)

theory Runs_To_VCG (* FIXME: I guess we can remove this theory *)
  imports
    Basic_Runs_To_VCG
begin



lemma transfer_conj_imp: "rel_fun (=) (rel_fun (\<longrightarrow>) (\<longrightarrow>)) (\<and>) (\<and>)"
  by (auto simp: rel_fun_def)

lemma transfer_all_imp: "rel_fun (rel_set R) (rel_fun (rel_fun R (\<longrightarrow>)) (\<longrightarrow>)) (Ball) (Ball)"
  by (auto simp: rel_fun_def rel_set_def)




section \<open> \<open>runs_to_vcg\<close> \<close>

method_setup trace_goals = \<open>
  Scan.lift Parse.string >>
    (fn msg => fn ctxt => fn using => Method.RUNTIME (CONTEXT_TACTIC (print_tac ctxt msg)))
\<close>

method_setup trace = \<open>
  (Scan.lift Parse.string) >>
    (fn msg => fn ctxt => fn using => Method.RUNTIME (CONTEXT_TACTIC
      (fn st => (tracing msg; Seq.single st))))
\<close>



section \<open>Check\<close>
thm runs_to_vcg [no_vars]
end