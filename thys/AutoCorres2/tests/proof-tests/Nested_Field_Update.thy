(*
 * Copyright (c) 2024 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Nested_Field_Update
imports "AutoCorres2_Main.AutoCorres_Main"
begin

record XX =
 fld1::nat
 fld2::int
print_theorems
install_C_file "nested_field_update.c"
autocorres "nested_field_update.c"

thm componets_C_idupdates
thm cs_C_update_def c2_C_update_def recursive_records_fold_congs

thm globals_C_idupdates
lemma foo: "globals_C (f (cs_C r)) = cs_C_update f r"
  by (simp cong: recursive_records_fold_congs flip: cs_C_update_def)


lemma "globals_C (cs_C r) = X"
  apply (simp add: foo)
  oops
thm foo cs_C_update_def
lemma cs_C_update_const_select_fold: "cs_C_update (\<lambda>_. f (cs_C r)) r = cs_C_update f r"
  by (cases r) simp

lemma globals_constr_to_updates: "globals_C a = cs_C_update (\<lambda>_. a) undefined"
  by simp

lemma bar1: "componets_C (f (c1_C r)) (c2_C r) = c1_C_update f r"
  by (simp cong: recursive_records_fold_congs flip: c1_C_update_def)

lemma bar2: "componets_C (c1_C r) (f (c2_C r)) = c2_C_update f r"
  by (simp cong: recursive_records_fold_congs flip: c2_C_update_def)

lemma bar_all: "componets_C (f (c1_C r)) (g (c2_C r)) = c2_C_update g (c1_C_update f r)"
  by (simp cong: recursive_records_fold_congs flip: c2_C_update_def c1_C_update_def)

lemma components_constr_to_updates: "componets_C a b = c2_C_update (\<lambda>_. b) (c1_C_update (\<lambda>_. a) undefined)"
  by simp

thm componets_C_idupdates
thm globals_C_idupdates
lemma c1_C_update_id: "c1_C_update (\<lambda>a. a) r = r" by (cases r) simp
lemma "componets_C (c1_C r) (f (c2_C r)) = c2_C_update f r"
  apply (subst bar_all)
  apply (simp add: c1_C_update_id)
  done
lemma "cs_C_update (\<lambda>_. c) x = globals_C c"
  by simp

lemma cs_C_update_fld: "cs_C_update (\<lambda>_. f (cs_C r)) r = cs_C_update f r"
  by (simp (*add: cs_C_update_def*) cong: recursive_records_fold_congs)



context ts_definition_write_globals
begin
lemma " (g_''_update (\<lambda>a. globals_C (c2_C_update (\<lambda>a. c_C 0x2B) (cs_C a)))) = g_''_update (cs_C_update (c2_C_update (\<lambda>_. c_C 0x2B)))"

  apply (simp add: foo)
  done
(*
  apply (simp add: cs_C_update_fld cong: state_fold_congs recursive_records_fold_congs  )
  thm cs_C_update_def [symmetric] recursive_records_fold_congs 
  apply (simp cong:  recursive_records_fold_congs flip: cs_C_update_def)
  oops
*)
thm ts_def
lemma "write_globals' \<equiv> modify (g_''_update (cs_C_update (c2_C_update (\<lambda>_. c_C 0x2B))))"
  unfolding ts_def .
end

end
