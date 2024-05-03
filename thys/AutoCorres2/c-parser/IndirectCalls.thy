(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory IndirectCalls

imports
  "PrettyProgs"

begin

lemma hoare_indirect_call_known_proc:
assumes spec: "\<Gamma> \<turnstile> P (call_exn init q return result_exn c) Q,A"
shows "\<Gamma>\<turnstile> ({s. p s = q} \<inter> P) (dynCall_exn f UNIV init p return result_exn c) Q,A"
  using spec
  apply -
  apply (rule hoare_complete, drule hoare_sound)
  apply (clarsimp simp: cvalid_def HoarePartialDef.valid_def dynCall_exn_def)
  apply (auto elim: exec_Normal_elim_cases)
  done


lemma hoare_indirect_call_guard:
assumes conseq: "P \<subseteq> g \<inter> R" 
assumes spec: "\<Gamma> \<turnstile> R (dynCall_exn f UNIV init p return result_exn c) Q,A"
shows "\<Gamma>\<turnstile> P (dynCall_exn f g init p return result_exn c) Q,A"
  using spec conseq
  apply -
  apply (rule hoare_complete, drule hoare_sound)
  apply (clarsimp simp: cvalid_def HoarePartialDef.valid_def dynCall_exn_def maybe_guard_def)
  apply (cases "g = UNIV")
  subgoal
    by force
  subgoal
    apply (clarsimp elim: exec_Normal_elim_cases )
    by (meson exec_Normal_elim_cases(5) imageI subsetD)
  done

end



