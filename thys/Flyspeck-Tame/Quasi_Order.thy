theory Quasi_Order
imports Main
begin

locale quasi_order =
fixes qle :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>" 60)
assumes qle_refl[iff]: "x \<preceq> x"
and qle_trans: "x \<preceq> y \<Longrightarrow> y \<preceq> z \<Longrightarrow> x \<preceq> z"
begin

definition in_qle :: "'a \<Rightarrow> 'a set \<Rightarrow> bool"  (infix "\<in>\<^isub>\<preceq>" 60) where
 "x \<in>\<^isub>\<preceq> M \<equiv> \<exists>y \<in> M. x \<preceq> y"

definition subseteq_qle :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<subseteq>\<^isub>\<preceq>" 60) where
 "M \<subseteq>\<^isub>\<preceq> N \<equiv> \<forall>x \<in> M. x \<in>\<^isub>\<preceq> N"

definition seteq_qle :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infix "=\<^isub>\<preceq>" 60) where
 "M =\<^isub>\<preceq> N  \<equiv>  M \<subseteq>\<^isub>\<preceq> N \<and> N \<subseteq>\<^isub>\<preceq> M"

lemmas "defs" = in_qle_def subseteq_qle_def seteq_qle_def

lemma subseteq_qle_refl[simp]: "M \<subseteq>\<^isub>\<preceq> M"
by(auto simp add: subseteq_qle_def in_qle_def)

lemma subseteq_qle_trans: "A \<subseteq>\<^isub>\<preceq> B \<Longrightarrow> B \<subseteq>\<^isub>\<preceq> C \<Longrightarrow> A \<subseteq>\<^isub>\<preceq> C"
by (simp add: subseteq_qle_def in_qle_def) (metis qle_trans)

lemma empty_subseteq_qle[simp]: "{} \<subseteq>\<^isub>\<preceq> A"
by (simp add: subseteq_qle_def)

lemma subseteq_qleI2: "(!!x. x \<in> M \<Longrightarrow> EX y : N. x \<preceq> y) \<Longrightarrow> M \<subseteq>\<^isub>\<preceq> N"
by (auto simp add: subseteq_qle_def in_qle_def)

lemma subseteq_qleD2: "M \<subseteq>\<^isub>\<preceq> N \<Longrightarrow> x \<in> M \<Longrightarrow> EX y : N. x \<preceq> y"
by (auto simp add: subseteq_qle_def in_qle_def)

lemma seteq_qle_refl[iff]: "A =\<^isub>\<preceq> A"
by (simp add: seteq_qle_def)

lemma seteq_qle_trans: "A =\<^isub>\<preceq> B \<Longrightarrow> B =\<^isub>\<preceq> C \<Longrightarrow> A =\<^isub>\<preceq> C"
by (simp add: seteq_qle_def) (metis subseteq_qle_trans)

end

end
