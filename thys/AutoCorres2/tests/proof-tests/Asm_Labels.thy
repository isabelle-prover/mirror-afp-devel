(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


theory Asm_Labels
imports "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "asm_labels.c" [ghostty="nat"]


lemma last_singleton[L1opt]: "last [x] = x"
  by simp
lemma last_cons[L1opt]: "last (x#y#ys) = last (y#ys)"
  by simp

axiomatization
  where asm_label_skip [L1opt]:
  "last just_label = CHR '':'' \<Longrightarrow>
   L1_spec (asm_spec ti gdata vol just_label (\<lambda>x s. s) (\<lambda>s. [])) = L1_skip"

text \<open>The axiomatic setup of named theorems @{thm L1opt} skips primitive assembler
 statements that are just labels. This results in those statements being removed already in
 layer L1\<close>


autocorres [ts_rules = nondet,
    scope = asm_labels] "asm_labels.c"

context asm_labels_simpl
begin
thm asm_labels_body_def
thm asm_unsupported_body_def
end

context l1_definition_asm_labels
begin
thm l1_def
end

context l2_definition_asm_labels
begin
thm l2_def
end

context ts_definition_asm_labels
begin
thm ts_def
end

text \<open>Function \<open>asm_unsupported\<close> also contains more complex assembler statements. These
are not removed. Currently they are propagated up to phase L1. Phase L2 fails as it not
handle \<^term>\<open>L1_spec (asm_spec a b c d e f)\<close> yet.\<close>

autocorres [phase=L1, scope = asm_unsupported] "asm_labels.c"

context l1_definition_asm_unsupported
begin
thm l1_def
end

end
