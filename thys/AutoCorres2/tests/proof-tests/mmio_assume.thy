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
(* check handling of spec-body troughout locale generation. What do we expect?*)
(* currently non-proto funs are imported to all_impl/corres. We should also add those for which
a spec-body is defined? get_defined_functions? *)
declare [[c_parser_feedback_level=2]]
init-autocorres [in_out_parameters=(* testing IO abstraction for \<open>L2_assume\<close>*)] "mmio_assume.c"
autocorres [ts_rules = nondet] "mmio_assume.c"

context mmio_assume_all_corres
begin

term "step'"
term "ts_definition_step.step'"
thm ts_definition_step.step'_def
end

lemma (in step_impl) "step_body \<equiv>
guarded_spec_body AssumeError
 ({(s, t). abs_step (state_' (globals s)) (state_' (globals t))} \<inter>
  {(s, t). t may_only_modify_globals s in [state]})"
  by (rule step_body_def [simplified])

lemma (in ts_definition_step)
  "step' \<equiv> assume_result_and_state (\<lambda>a.
    {(u, t). abs_step (state_'' a) (state_'' t) \<and> (\<exists>state_'. t = a\<lparr>state_'' := state_'\<rparr>)})"
  by (rule step'_def)

lemma (in ts_definition_step2) "step2' \<equiv>
assume_result_and_state
 (\<lambda>a. {(u, t).
        abs_step2 (g1_'' a, g2_'' a) (g1_'' t, g2_'' t) \<and>
        (\<exists>g1_' g2_'. t = a\<lparr>g1_'' := g1_', g2_'' := g2_'\<rparr>)})"
  by (rule step2'_def)

end
