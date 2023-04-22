theory Relation_Extra
  imports Main
begin

definition transp_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "transp_on A R \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> A. \<forall>z \<in> A. R x y \<longrightarrow> R y z \<longrightarrow> R x z)"

lemma transp_onD: "transp_on A R \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> R x y \<Longrightarrow> R y z \<Longrightarrow> R x z"
  by (meson transp_on_def)

lemma transp_on_reflclp[simp]: "transp_on A R \<Longrightarrow> transp_on A R\<^sup>=\<^sup>="
  by (smt (verit, best) sup2E sup2I1 transp_on_def)

lemma totalp_on_insert:
  "totalp_on (insert a A) R \<longleftrightarrow> (\<forall>b \<in> A. a \<noteq> b \<longrightarrow> R a b \<or> R b a) \<and> totalp_on A R"
  by (auto simp add: totalp_on_def)

lemma antisymp_reflcp: "antisymp R \<Longrightarrow> antisymp R\<^sup>=\<^sup>="
  by (simp add: antisymp_def)

lemma irreflp_on_if_asymp_on[simp]: "asymp r \<Longrightarrow> irreflp r"
  by (metis asymp.simps irreflp_def)

lemma asymp_on_iff_irreflp_on_if_transp_on: "transp R \<Longrightarrow> asymp R \<longleftrightarrow> irreflp R"
  by (metis asymp.simps irreflp_def transpE)

lemma irreflpD: "irreflp R \<Longrightarrow> \<not> R x x"
  by (simp add: irreflp_def)

lemma (in linorder) totalp_on_le[simp]: "totalp_on A (\<le>)"
  by (rule totalp_onI, rule linear)

lemma (in preorder) transp_on_le[simp]: "transp_on A (\<le>)"
  using Relation_Extra.transp_on_def local.dual_order.trans by blast

end