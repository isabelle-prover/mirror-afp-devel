(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory CustomWordAbs
imports "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "custom_word_abs.c"

lemma [word_abs]:
  "\<lbrakk> abstract_val P x sint x'; abstract_val Q y sint y' \<rbrakk> \<Longrightarrow>
        abstract_val (P \<and> Q) (max x y)
          sint (x' xor (x' xor y') && - (if x' <s y' then (1 :: sword32) else 0))"
  apply (clarsimp simp: max_def word_sless_def word_sle_def abstract_val_def)
  done

lemma mask_legacy_def: "mask (n::nat) = (1 << n) - 1"
  by (simp add: mask_eq_exp_minus_1 )


lemma [word_abs]:
  assumes abs_x: "abstract_val P x unat x'" 
  assumes abs_y: "abstract_val Q y unat y'" 
  shows "abstract_val (P \<and> Q \<and> y < 32) (x mod (2 ^ y)) unat (x' && 2 ^ unat y' - (1 :: word32))"
proof -
  have eq: "unat (x' && 2 ^ unat y' - 1) = unat (x' && (1 << unat y') - 1)"
    by simp
  show ?thesis
    using abs_x abs_y
    apply (clarsimp  simp add: abstract_val_def )
    apply (subst eq)
    apply (fold mask_legacy_def)
    apply (subst word_mod_2p_is_mask [symmetric])
    apply (subst p2_gt_0)
    by (auto simp: unat_mod)
qed

lemma [word_abs]:
  "\<lbrakk> abstract_val P x unat (x' :: word32);
     abstract_val Q y unat y' \<rbrakk> \<Longrightarrow>
      abstract_val (P \<and> Q) (x + y > UINT_MAX) id (x' + y' < x')"
  apply (subst not_le [symmetric], subst no_plus_overflow_unat_size)
  apply (clarsimp simp: not_less UINT_MAX_def word_size abstract_val_def)
  apply arith
  done

autocorres [unsigned_word_abs = b c] "custom_word_abs.c"


context custom_word_abs_all_impl begin

lemma "a' x y = max x y"
  by (unfold a'_def, rule refl)

lemma "b' x 4 s = Some (x mod 16)"
  by (unfold b'_def, simp)

lemma "c' x y = (if UINT_MAX < x + y then 1 else 0)"
  by (unfold c'_def, simp)

end

end
