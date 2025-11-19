(*
 Title Additional_Lemmas_for_Extended_Nonnegative_Reals.thy
 Author: Tetsuya Sato
*)

theory Additional_Lemmas_for_Calculation
  imports"HOL-Probability.Probability"
begin

section \<open> Additional Lemmas for Calculation \<close>

subsection \<open> Lemmas on Extended Real \<close>

lemma ennreal_diff_add_transpose:
  fixes a b c :: ennreal
  assumes "c \<le> a"
    and "a - c = b"
  shows "a = b + c"
  using assms(1) assms(2) diff_add_cancel_ennreal by auto

lemma ereal_diff_add_transpose:
  fixes a b c :: ereal
  assumes "a \<le> b + c"
    and "c \<noteq> \<infinity>" and "c \<noteq> -\<infinity>"
  shows "a - c \<le> b"
  by (auto simp: assms(1) assms(2) assms(3) ereal_minus_le_iff)
end