(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Tests for handling Spec constructs emitted by the C parser.
 *)
theory mmio
imports "AutoCorres2_Main.AutoCorres_Main"
begin

text \<open>Some placeholders for a 'hardware-step' relation.\<close>

consts abs_step:: "word32 \<Rightarrow> word32 \<Rightarrow> bool"
consts abs_step2:: "(word32 \<times> word32) \<Rightarrow> (word32 \<times> word32) \<Rightarrow> bool"

install_C_file "mmio.c"
(* check handling of spec-body troughout locale generation. What do we expect?*)
(* currently non-proto funs are imported to all_impl/corres. We should also add those for which
a spec-body is defined? get_defined_functions? *)
declare [[c_parser_feedback_level=2]]

autocorres [ts_rules = nondet] "mmio.c"

context mmio_all_corres
begin

term "step'"
term "ts_definition_step.step'"
thm ts_definition_step.step'_def
end

lemma (in step_impl) "step_body \<equiv>
guarded_spec_body ImpossibleSpec
 ({(s, t). abs_step (state_' (globals s)) (state_' (globals t))} \<inter>
  {(s, t). t may_only_modify_globals s in [state]})"
  by (rule step_body_def [simplified])


lemma (in ts_definition_step) "step' \<equiv>
  assert_result_and_state
     (\<lambda>s. {(v, t).
        abs_step (state_'' s) (state_'' t) \<and>
        (\<exists>state_'. t = s\<lparr>state_'' := state_'\<rparr>)})"
  by (rule step'_def)


lemma (in ts_definition_step2) "step2' \<equiv>
  assert_result_and_state
   (\<lambda>s. {(v, t).
        abs_step2 (g1_'' s, g2_'' s) (g1_'' t, g2_'' t) \<and>
        (\<exists>g1_' g2_'. t = s\<lparr>g1_'' := g1_', g2_'' := g2_'\<rparr>)})"
  by (rule step2'_def)

end
