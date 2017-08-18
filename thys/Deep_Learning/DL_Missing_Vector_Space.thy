(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Missing Lemmas of Vector\_Space\<close>

theory DL_Missing_Vector_Space
imports Jordan_Normal_Form.Missing_VectorSpace
begin
find_theorems vectorspace.basis

lemma (in vectorspace) dim1I:
assumes "gen_set {v}"
assumes "v \<noteq> \<zero>\<^bsub>V\<^esub>" "v \<in> carrier V"
shows "dim = 1"
proof -
  have "basis {v}" by (metis assms(1) assms(2) assms(3) basis_def empty_iff empty_subsetI
   finite.emptyI finite_lin_indpt2 insert_iff insert_subset insert_union lin_dep_iff_in_span
   span_empty)
  then show ?thesis using dim_basis by force
qed

lemma (in vectorspace) dim0I:
assumes "gen_set {\<zero>\<^bsub>V\<^esub>}"
shows "dim = 0"
proof -
  have "basis {}" unfolding basis_def using already_in_span assms finite_lin_indpt2 span_zero by auto
  then show ?thesis using dim_basis by force
qed

lemma (in vectorspace) dim_le1I:
assumes "gen_set {v}"
assumes "v \<in> carrier V"
shows "dim \<le> 1"
by (metis One_nat_def assms(1) assms(2) bot.extremum card.empty card.insert empty_iff finite.intros(1)
finite.intros(2) insert_subset vectorspace.gen_ge_dim vectorspace_axioms)

end
