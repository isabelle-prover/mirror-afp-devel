theory Eqi_Locale
imports Main
begin

locale eqi =
fixes eqi :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<simeq>" 60)
assumes eqi_refl[iff]: "x \<simeq> x"
and eqi_trans: "x \<simeq> y \<Longrightarrow> y \<simeq> z \<Longrightarrow> x \<simeq> z"
begin

definition in_eqi :: "'a \<Rightarrow> 'a set \<Rightarrow> bool"  (infix "\<in>\<^isub>\<simeq>" 60) where
 "x \<in>\<^isub>\<simeq> M \<equiv> \<exists>y \<in> M. x \<simeq> y"

definition subseteq_eqi :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<subseteq>\<^isub>\<simeq>" 60) where
 "M \<subseteq>\<^isub>\<simeq> N \<equiv> \<forall>x \<in> M. x \<in>\<^isub>\<simeq> N"

definition seteq_eqi :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infix "=\<^isub>\<simeq>" 60) where
 "M =\<^isub>\<simeq> N  \<equiv>  M \<subseteq>\<^isub>\<simeq> N \<and> N \<subseteq>\<^isub>\<simeq> M"

lemmas "defs" = in_eqi_def subseteq_eqi_def seteq_eqi_def

lemma subseteq_eqi_refl[simp]: "M \<subseteq>\<^isub>\<simeq> M"
by(auto simp add: subseteq_eqi_def in_eqi_def)

lemma subseteq_eqi_trans: "A \<subseteq>\<^isub>\<simeq> B \<Longrightarrow> B \<subseteq>\<^isub>\<simeq> C \<Longrightarrow> A \<subseteq>\<^isub>\<simeq> C"
by (simp add: subseteq_eqi_def in_eqi_def) (metis eqi_trans)

lemma empty_subseteq_eqi[simp]: "{} \<subseteq>\<^isub>\<simeq> A"
by (simp add: subseteq_eqi_def)

lemma subseteq_eqiI2: "(!!x. x \<in> M \<Longrightarrow> EX y : N. x \<simeq> y) \<Longrightarrow> M \<subseteq>\<^isub>\<simeq> N"
by (auto simp add: subseteq_eqi_def in_eqi_def)

lemma subseteq_eqiD2: "M \<subseteq>\<^isub>\<simeq> N \<Longrightarrow> x \<in> M \<Longrightarrow> EX y : N. x \<simeq> y"
by (auto simp add: subseteq_eqi_def in_eqi_def)

lemma seteq_eqi_refl[iff]: "A =\<^isub>\<simeq> A"
by (simp add: seteq_eqi_def)

lemma seteq_eqi_trans: "A =\<^isub>\<simeq> B \<Longrightarrow> B =\<^isub>\<simeq> C \<Longrightarrow> A =\<^isub>\<simeq> C"
by (simp add: seteq_eqi_def) (metis subseteq_eqi_trans)

end

end
