section\<open>Ordinals in generic extensions\<close>
theory Ordinals_In_MG
  imports
    Forcing_Theorems
begin

context G_generic1
begin

lemma rank_val: "rank(val(P,G,x)) \<le> rank(x)" (is "?Q(x)")
proof (induct rule:ed_induction[of ?Q])
  case (1 x)
  have "val(P,G,x) = {val(P,G,u). u\<in>{t\<in>domain(x). \<exists>p\<in>P . \<langle>t,p\<rangle>\<in>x \<and> p \<in> G }}"
    using def_val[of G x] by auto
  then
  have "rank(val(P,G,x)) = (\<Union>u\<in>{t\<in>domain(x). \<exists>p\<in>P . \<langle>t,p\<rangle>\<in>x \<and> p \<in> G }. succ(rank(val(P,G,u))))"
    using rank[of "val(P,G,x)"] by simp
  moreover
  have "succ(rank(val(P,G, y))) \<le> rank(x)" if "ed(y, x)" for y
    using 1[OF that] rank_ed[OF that] by (auto intro:lt_trans1)
  moreover from this
  have "(\<Union>u\<in>{t\<in>domain(x). \<exists>p\<in>P . \<langle>t,p\<rangle>\<in>x \<and> p \<in> G }. succ(rank(val(P,G,u)))) \<le> rank(x)"
    by (rule_tac UN_least_le) (auto)
  ultimately
  show ?case
    by simp
qed

lemma Ord_MG_iff:
  assumes "Ord(\<alpha>)"
  shows "\<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> M[G]"
proof
  show "\<alpha> \<in> M[G]" if "\<alpha> \<in> M"
    using generic[THEN one_in_G, THEN M_subset_MG] that ..
next
  assume "\<alpha> \<in> M[G]"
  then
  obtain x where "x\<in>M" "val(P,G,x) = \<alpha>"
    using GenExtD by auto
  then
  have "rank(\<alpha>) \<le> rank(x)"
    using rank_val by blast
  with assms
  have "\<alpha> \<le> rank(x)"
    using rank_of_Ord by simp
  then
  have "\<alpha> \<in> succ(rank(x))"
    using ltD by simp
  with \<open>x\<in>M\<close>
  show "\<alpha> \<in> M"
    using cons_closed transitivity[of \<alpha> "succ(rank(x))"] rank_closed
    unfolding succ_def by simp
qed

end \<comment> \<open>\<^locale>\<open>G_generic1\<close>\<close>

end