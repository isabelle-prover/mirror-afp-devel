(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory nested_array imports "AutoCorres2_Main.AutoCorres_Main" begin

install_C_file "nested_array.c"
autocorres "nested_array.c"

context ts_definition_elem_A 
begin
thm ts_def
lemma "elem_A' sa \<equiv>
  do {
  _ \<leftarrow> oguard (\<lambda>s. IS_VALID(A_C) s sa);
  ogets (\<lambda>s. array_A_C (heap_A_C s sa).[0])
}"
  by (simp add: ts_def)
end

context ts_definition_elem_B
begin
thm ts_def
lemma "elem_B' sa \<equiv>
  do {
  _ \<leftarrow> oguard (\<lambda>s. IS_VALID(B_C) s sa);
  ogets (\<lambda>s. array_B_C (heap_B_C s sa).[0])
}"
  by (simp add: ts_def)
end
end
