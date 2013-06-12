(* Author: Christian Sternagel, JAIST *)

header {* Nash-Williams' Version of Dickson's Lemma *}

theory Dickson_with_Transitivity
imports
  Least_Enum
  Almost_Full_Relations
  "~~/src/HOL/Library/Infinite_Set"
begin

lemma Dickson:
  fixes P1 (infix "\<le>\<^sub>1" 50) and P2 (infix "\<le>\<^sub>2" 50) and P (infix "\<le>\<^sub>\<times>" 50)
  assumes pointwise: "\<And>p q. p \<le>\<^sub>\<times> q \<longleftrightarrow> fst p \<le>\<^sub>1 fst q \<and> snd p \<le>\<^sub>2 snd q"
    and af1: "almost_full_on (op \<le>\<^sub>1) A1"
    and af2: "almost_full_on (op \<le>\<^sub>2) A2"
    and TRANS: "transp_on op \<le>\<^sub>1 A1"
  shows "almost_full_on (op \<le>\<^sub>\<times>) (A1 \<times> A2)"
proof
  fix g :: "nat \<Rightarrow> 'a \<times> 'b"
  assume *: "\<forall>i. g i \<in> A1 \<times> A2"
  def q \<equiv> "\<lambda>i. fst (g i)" and q' \<equiv> "\<lambda>i. snd (g i)"
  have q: "\<forall>i. q i \<in> A1" and q': "\<forall>i. q' i \<in> A2"
    using * by (auto simp: q_def q'_def) (metis SigmaE2 pair_collapse)+
  let ?P = "\<lambda>m. \<exists>n>m. q m \<le>\<^sub>1 q n"
  txt {*The set of \emph{terminal} indices.*}
  let ?T = "{m. \<not> ?P m}"
  have "finite ?T"
  proof (rule ccontr)
    assume "infinite ?T"
    then have "\<forall>i. \<exists>j>i. j \<in> ?T" by (auto simp: infinite_nat_iff_unbounded)
    then interpret T: infinitely_many1 "\<lambda>x. x \<in> ?T" by (unfold_locales) blast
    def f \<equiv> "T.enum" -- "enumerate the indices in ?T"
    have "\<And>i. f i \<in> ?T" and "\<And>i. f i < f (Suc i)"
      using T.enum_P and T.enum_mono
      unfolding f_def [symmetric] by simp+
    moreover then have "\<And>i j. i < j \<Longrightarrow> f i < f j" by (metis lift_Suc_mono_less)
    ultimately have "bad (op \<le>\<^sub>1) (\<lambda>i. q (f (Suc i)))"
      unfolding good_def by auto
    with af1 and q show False by (auto simp: almost_full_on_def)
  qed
  moreover have "infinite {m. ?P m}"
  proof -
    have UNIV: "UNIV = ?T \<union> {m. ?P m}" by blast
    show ?thesis using `finite ?T` and nat_infinite by (auto simp: UNIV)
  qed
  ultimately obtain N where "\<forall>m\<ge>N. \<exists>n>m. q m \<le>\<^sub>1 q n"
    by (auto simp: finite_nat_set_iff_bounded) (metis not_less)
  then interpret le1: infinitely_many2 "\<lambda>x y. q x \<le>\<^sub>1 q y" N by (unfold_locales) blast
  def f \<equiv> "le1.enumchain"
  from le1.enumchain_chain have **: "\<And>i. q (f i) \<le>\<^sub>1 q (f (Suc i))"
    by (simp add: f_def)
  from le1.enumchain_mono have f_mono: "\<And>i. f i < f (Suc i)" by (simp add: f_def)+
  obtain i j where "i < j" and "q' (f i) \<le>\<^sub>2 q' (f j)"
    using af2 [unfolded almost_full_on_def, THEN spec, of "\<lambda>i. q' (f i)"] and q'
    by (auto simp: good_def)
  moreover have "f i < f j" using f_mono and `i < j` by (metis lift_Suc_mono_less)
  moreover have "q (f i) \<le>\<^sub>1 q (f j)"
    using chain_on_transp_on_less [of "\<lambda>i. q (f i)", OF _ TRANS `i < j`] and ** and q by blast
  ultimately show "good (op \<le>\<^sub>\<times>) g"
    by (auto simp: good_def pointwise q_def q'_def)
qed

end

