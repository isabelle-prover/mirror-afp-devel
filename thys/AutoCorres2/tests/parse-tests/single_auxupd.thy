(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory single_auxupd
imports AutoCorres2_Main.AutoCorres_Main
begin



primrec
  htd_upd :: "addr \<Rightarrow> typ_slice list \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc"
where
  "htd_upd p [] d = d"
| "htd_upd p (x#xs) d = htd_upd (p+1) xs (d(p := (True, x)))"

definition ptr_force_type :: "'a::c_type ptr \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc" where
  "ptr_force_type p \<equiv> htd_upd (ptr_val p) (typ_slices TYPE('a))"

definition ptr_force_types :: "'a::c_type ptr list \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc" where
  "ptr_force_types = fold ptr_force_type"

definition page_bits :: "nat \<Rightarrow> nat" where
  "page_bits l = 12 + l * 9"

definition frame_div :: "addr \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> addr list" where
  "frame_div addr l bits = map (\<lambda>i. addr + of_nat i * 2^bits) [0 ..< 2^(page_bits l - bits)]"

definition frame_ptrs :: "'a::c_type itself \<Rightarrow> addr \<Rightarrow> nat \<Rightarrow> 'a::c_type ptr list" where
  "frame_ptrs TYPE('a) frame bits = map Ptr (frame_div frame 0 bits)"


install_C_file "single_auxupd.c"

autocorres [no_heap_abs = ISABELLE_mark_free] "single_auxupd.c"

context single_auxupd_all_corres
begin
thm ISABELLE_mark_free_body_def
thm ISABELLE_mark_free'_def
end
end