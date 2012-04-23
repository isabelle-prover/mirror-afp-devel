(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c-sterna@jaist.ac.jp>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Binary Predicates Restricted to Elements of a given Set *}

theory Restricted_Predicates
imports Main
begin

definition reflp_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "reflp_on P A \<equiv> \<forall>a\<in>A. P a a"

lemma reflp_onI [Pure.intro]:
  "(\<And>a. a \<in> A \<Longrightarrow> P a a) \<Longrightarrow> reflp_on P A"
  unfolding reflp_on_def by blast

definition transp_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "transp_on P A \<equiv> \<forall>a\<in>A. \<forall>b\<in>A. \<forall>c\<in>A. P a b \<and> P b c \<longrightarrow> P a c"

lemma transp_onI [Pure.intro]:
  "(\<And>a b c. \<lbrakk>a \<in> A; b \<in> A; c \<in> A; P a b; P b c\<rbrakk> \<Longrightarrow> P a c) \<Longrightarrow> transp_on P A"
  unfolding transp_on_def by blast

lemma reflp_on_reflclp [simp]:
  assumes "reflp_on P A" and "a \<in> A" and "b \<in> A"
  shows "P\<^sup>=\<^sup>= a b = P a b"
  using assms by (auto simp: reflp_on_def)

lemma transp_on_tranclp:
  assumes "transp_on P A"
  shows "(\<lambda>x y. x \<in> A \<and> y \<in> A \<and> P x y)\<^sup>+\<^sup>+ a b \<longleftrightarrow> a \<in> A \<and> b \<in> A \<and> P a b"
    (is "?lhs = ?rhs")
  by (rule iffI, induction rule: tranclp.induct)
     (insert assms, auto simp: transp_on_def)

lemma reflp_on_converse:
  "reflp_on P A \<Longrightarrow> reflp_on P\<inverse>\<inverse> A"
  unfolding reflp_on_def by blast

lemma transp_on_converse:
  "transp_on P A \<Longrightarrow> transp_on P\<inverse>\<inverse> A"
  unfolding transp_on_def by blast

lemma reflp_on_subset:
  "A \<subseteq> B \<Longrightarrow> reflp_on P B \<Longrightarrow> reflp_on P A"
  by (auto simp: reflp_on_def)

lemma transp_on_subset:
  "A \<subseteq> B \<Longrightarrow> transp_on P B \<Longrightarrow> transp_on P A"
  by (auto simp: transp_on_def)

end
