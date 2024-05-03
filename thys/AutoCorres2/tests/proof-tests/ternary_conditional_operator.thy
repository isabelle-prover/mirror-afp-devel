(*
 * Copyright (c) 2024 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Tests for handling the ternary conditional operator
 *)
theory ternary_conditional_operator
  imports "AutoCorres2_Main.AutoCorres_Main"
begin

declare [[ML_print_depth=1000]]
install_C_file "ternary_conditional_operator.c"

autocorres[ts_force nondet = inc] "ternary_conditional_operator.c"
context ternary_conditional_operator_all_impl  begin

lemma "ternary3' x1 x2 y z \<equiv> 
  do {
    x' \<leftarrow> condition (\<lambda>s. x1 \<noteq> NULL)
      (do {
        guard (\<lambda>s. IS_VALID(32 word) s x1);
        gets (\<lambda>s. heap_w32 s x1)
      })
      (condition (\<lambda>s. x2 \<noteq> NULL)
        (do {
          guard (\<lambda>s. IS_VALID(32 word) s x2);
          gets (\<lambda>s. heap_w32 s x2)
        })
        (return 0));
    y' \<leftarrow> inc' y;
    z' \<leftarrow> condition (\<lambda>s. z \<noteq> NULL) (inc' z) (return 0xC);
    return (ternary1' x' y' z')
  }"
  unfolding ternary3'_def
  by (simp)
end
end
