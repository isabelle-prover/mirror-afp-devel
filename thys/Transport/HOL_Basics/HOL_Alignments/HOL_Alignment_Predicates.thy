\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Alignment With Predicate Definitions from HOL\<close>
theory HOL_Alignment_Predicates
  imports
    Main
    HOL_Mem_Of
    Predicates
begin

named_theorems HOL_predicate_alignment

subparagraph \<open>Quantifiers\<close>

adhoc_overloading ball Ball

lemma Ball_eq_ball_pred [HOL_predicate_alignment]: "\<forall>\<^bsub>A\<^esub> = \<forall>\<^bsub>mem_of A\<^esub>" by auto

lemma Ball_eq_ball_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  shows "\<forall>\<^bsub>A\<^esub> = \<forall>\<^bsub>P\<^esub>"
  using assms by (simp add: Ball_eq_ball_pred)

lemma Ball_iff_ball_pred [HOL_predicate_alignment]: "(\<forall>x : A. Q x) \<longleftrightarrow> (\<forall>x : mem_of A. Q x)"
  by (simp add: Ball_eq_ball_pred)

adhoc_overloading bex Bex

lemma Bex_eq_bex_pred [HOL_predicate_alignment]: "\<exists>\<^bsub>A\<^esub> = \<exists>\<^bsub>mem_of A\<^esub>" by fast

lemma Bex_eq_bex_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  shows "\<exists>\<^bsub>A\<^esub> = \<exists>\<^bsub>P\<^esub>"
  using assms by (simp add: Bex_eq_bex_pred)

lemma Bex_iff_bex_pred [HOL_predicate_alignment]: "(\<exists>x : A. Q x) \<longleftrightarrow> (\<exists>x : mem_of A. Q x)"
  by (simp add: Bex_eq_bex_pred)


end