(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Tests for handling Spec constructs emitted by the C parser.
 *)
theory mmio_assume
imports "AutoCorres2_Main.AutoCorres_Main"
begin

text \<open>A variant of theory \<open>mmio\<close>, but assuming (instead of specifying) hardware behaviour.\<close>

declare [[c_parser_assume_fnspec]]

text \<open>Some placeholders for a 'hardware-step' relation.\<close>

consts abs_step:: "word32 \<Rightarrow> word32 \<Rightarrow> bool"
consts abs_step2:: "(word32 \<times> word32) \<Rightarrow> (word32 \<times> word32) \<Rightarrow> bool"

declare [[c_parser_feedback_level=2]]
include_C_file "mmio.c" for "mmio_assume.c"
install_C_file "mmio_assume.c"

ML_val \<open>
val x1 =  Proof_Context.read_typ @{context} "globals"
val x2 =  Proof_Context.read_typ @{context} "mmio_assume.globals"
\<close>
(* check handling of spec-body trughout locale generation. What do we expect?*)
(* currently non-proto funs are imported to all_impl/corres. We should also add those for which
a spec-body is defined? get_defined_functions? *)

init-autocorres [in_out_parameters=(* testing IO abstraction for \<open>L2_assume\<close>*)] "mmio_assume.c"


autocorres [ts_rules = nondet] "mmio_assume.c"


lemma "step_body \<equiv>
spec_pre_post ImpossibleSpec AssumeError
 {s. \<exists>st. s \<in> {s. state_' (globals s) = st}}
 ({(s, t).
   (\<forall>st. s \<in> {s. state_' (globals s) = st} \<longrightarrow> t \<in> \<lbrace>abs_step st \<acute>state\<rbrace>) \<and>
   (\<exists>st. s \<in> {s. state_' (globals s) = st})} \<inter>
  {(s, t). t may_only_modify_globals s in [state]})"
  by (rule step_body_def)

lemma
  "step' \<equiv> assume_result_and_state (\<lambda>a.
    {(u, t). abs_step (state_'' a) (state_'' t) \<and> (\<exists>state_'. t = a\<lparr>state_'' := state_'\<rparr>)})"
  by (rule step'_def)

lemma "step2' \<equiv>
assume_result_and_state
 (\<lambda>a. {(u, t).
        abs_step2 (g1_'' a, g2_'' a) (g1_'' t, g2_'' t) \<and>
        (\<exists>g1_' g2_'. t = a\<lparr>g1_'' := g1_', g2_'' := g2_'\<rparr>)})"
  by (rule step2'_def)

lemma "unreachable_body \<equiv>
spec_pre_post ImpossibleSpec AssumeError {s. s \<in> \<lbrace>False\<rbrace>}
 ({(s, t). (s \<in> \<lbrace>False\<rbrace> \<longrightarrow> t \<in> \<lbrace>True\<rbrace>) \<and> s \<in> \<lbrace>False\<rbrace>} \<inter>
  {(s, t). t may_not_modify_globals s})"
  by (rule unreachable_body_def)

lemma "unreachable' \<equiv> fail"
  by (rule unreachable'_def)

lemma "empty_body \<equiv>
spec_pre_post ImpossibleSpec AssumeError {s. s \<in> \<lbrace>\<acute>state < 0x2A\<rbrace>}
 ({(s, t). (s \<in> \<lbrace>\<acute>state < 0x2A\<rbrace> \<longrightarrow> t \<in> \<lbrace>False\<rbrace>) \<and> s \<in> \<lbrace>\<acute>state < 0x2A\<rbrace>} \<inter>
  {(s, t). t may_not_modify_globals s})"
  by (rule empty_body_def)

lemma "empty' \<equiv> do {
  v \<leftarrow> guard (\<lambda>s. state_'' s < 0x2A);
  assume_result_and_state (\<lambda>a. {})
}"
  by (rule empty'_def)

end
