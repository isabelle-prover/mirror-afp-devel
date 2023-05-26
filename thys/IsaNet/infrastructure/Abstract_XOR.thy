(*******************************************************************************
 
  Project: IsaNet

  Author:  Tobias Klenze, ETH Zurich <tobias.klenze@inf.ethz.ch>
  Version: JCSPaper.1.0
  Isabelle Version: Isabelle2021-1

  Copyright (c) 2022 Tobias Klenze
  Licence: Mozilla Public License 2.0 (MPL) / BSD-3-Clause (dual license)

*******************************************************************************)

section \<open>Abstract XOR\<close>
theory "Abstract_XOR"
  imports
    "HOL.Finite_Set" "HOL-Library.FSet" "Message"
(*the latter half of this theory uses msgterm. If split it off, we have to add
  declare fmember_iff_member_fset[simp]
in order to show the first half*)
begin

(******************************************************************************)
subsection\<open>Abstract XOR definition and lemmas\<close>
(******************************************************************************)

text\<open>We model xor as an operation on finite sets (fset). @{term "{||}"} is defined as the identity element.\<close>

text\<open>xor of two fsets is the symmetric difference\<close>
definition xor :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  "xor xs ys = (xs |\<union>| ys) |-| (xs |\<inter>| ys)"

lemma xor_singleton: 
  "xor xs {| z |} = (if z |\<in>| xs then xs |-| {| z |} else finsert z xs)"
  "xor {| z |} xs = (if z |\<in>| xs then xs |-| {| z |} else finsert z xs)"
  by (auto simp add: xor_def)

(*auto loops with this rule declared intro!. We could alternatively try using safe instead of auto*)
declare finsertCI[rule del]
declare finsertCI[intro]

lemma xor_assoc: "xor (xor xs ys) zs = xor xs (xor ys zs)"
  by (auto simp add: xor_def)

lemma xor_commut: "xor xs ys = xor ys xs"
  by (auto simp add: xor_def)

lemma xor_self_inv: "\<lbrakk>xor xs ys = zs; xs = ys\<rbrakk> \<Longrightarrow> zs = {||}"
  by (auto simp add: xor_def)

lemma xor_self_inv': "xor xs xs = {||}"
  by (auto simp add: xor_def)

lemma xor_self_inv''[dest!]: "xor xs ys = {||} \<Longrightarrow> xs = ys"
  by (auto simp add: xor_def)

lemma xor_identity1[simp]: "xor xs {||} = xs"
  by (auto simp add: xor_def)

lemma xor_identity2[simp]: "xor {||} xs = xs"
  by (auto simp add: xor_def)

lemma xor_in: "z |\<in>| xs \<Longrightarrow> z |\<notin>| (xor xs {| z |})"
  by (auto simp add: xor_singleton)

lemma xor_out: "z |\<notin>| xs \<Longrightarrow> z |\<in>| (xor xs {| z |})"
  by (auto simp add: xor_singleton)

lemma xor_elem1[dest]: "\<lbrakk>x \<in> fset (xor X Y); x |\<notin>| X\<rbrakk> \<Longrightarrow> x |\<in>| Y"
  by(auto simp add: xor_def)

lemma xor_elem2[dest]: "\<lbrakk>x \<in> fset (xor X Y); x |\<notin>| Y\<rbrakk> \<Longrightarrow> x |\<in>| X"
  by(auto simp add: xor_def)

lemma xor_finsert_self: "xor (finsert x xs) {|x|} = xs - {| x |}" 
  by(auto simp add: xor_def)


(******************************************************************************)
subsection\<open>Lemmas refering to XOR and msgterm\<close>
(******************************************************************************)

lemma FS_contains_elem:
  assumes "elem = f (FS zs_s)" "zs_s = xor zs_b {| elem |}" "\<And> x. size (f x) > size x"
  shows "elem \<in> fset zs_b"
  using assms(1)
  apply(auto simp add: xor_def)
  using FS_mono assms xor_singleton(1)
  by (metis)

lemma FS_is_finsert_elem:
  assumes "elem = f (FS zs_s)" "zs_s = xor zs_b {| elem |}" "\<And> x. size (f x) > size x"
  shows "zs_b = finsert elem zs_s"
  using assms FS_contains_elem finsert_fminus xor_singleton(1) FS_mono
  by (metis FS_mono)

lemma FS_update_eq:
  assumes "xs = f (FS (xor zs {|xs|}))"
      and "ys = g (FS (xor zs {|ys|}))"
      and "\<And> x. size (f x) > size x"
      and "\<And> x. size (g x) > size x"
    shows "xs = ys"
proof(rule ccontr)
  assume elem_neq: "xs \<noteq> ys"
  obtain zs_s1 zs_s2 where zs_defs: 
    "zs_s1 = xor zs {|xs|}" "zs_s2 = xor zs {|ys|}" by simp
  have elems_contained_zs: "xs \<in> fset zs" "ys \<in> fset zs" 
    using assms FS_contains_elem by blast+
  then have elems_elem: "ys |\<in>| zs_s1" "xs |\<in>| zs_s2" 
    using elem_neq by(auto simp add: xor_def zs_defs)
  have zs_finsert: "finsert xs zs_s2 = zs_s2" "finsert ys zs_s1 = zs_s1"
    using elems_elem by fastforce+
  have f1: "\<forall>m f fa. \<not> sum fa (fset (finsert (m::msgterm) f)) < (fa m::nat)"
    by (simp add: sum.insert_remove)
  from assms(1-2) have "size xs > size (f (FS {| ys |}))" "size ys > size (g (FS {| xs |}))"
    apply(simp_all add: zs_defs[symmetric])
    using zs_finsert f1 by (metis (no_types) add_Suc_right assms(3-4) dual_order.strict_trans 
        less_add_Suc1 msgterm.size(17) not_less_eq size_fset_simps)+
  then show False using assms(3,4) elems_elem 
    by (metis add.right_neutral add_Suc_right f1 less_add_Suc1 msgterm.size(17) not_less_eq 
              not_less_iff_gr_or_eq order.strict_trans size_fset_simps)
qed

declare fminusE[rule del] 
declare finsertCI[rule del]
(*add back the removed rules without !*)
declare fminusE[elim]
declare finsertCI[intro]

(*currently not needed*)
lemma fset_size_le:
  assumes "x \<in> fset xs" 
  shows "size x < Suc (\<Sum>x\<in>fset xs. Suc (size x))"
proof-
  have "size x \<le> (\<Sum>x\<in>fset xs. size x)" using assms 
    by (auto intro: member_le_sum)
  moreover have "(\<Sum>x\<in>fset xs. size x) < (\<Sum>x\<in>fset xs. Suc (size x))"
    by (metis assms empty_iff finite_fset lessI sum_strict_mono)
  ultimately show ?thesis by auto
qed

text\<open>We can show that xor is a commutative function.\<close>
(*not needed*)
locale abstract_xor 
begin
sublocale comp_fun_commute xor
  by(auto simp add: comp_fun_commute_def xor_def)

end
end