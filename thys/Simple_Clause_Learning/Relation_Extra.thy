theory Relation_Extra
  imports Main
begin

lemma totalp_on_insert:
  "totalp_on (insert a A) R \<longleftrightarrow> (\<forall>b \<in> A. a \<noteq> b \<longrightarrow> R a b \<or> R b a) \<and> totalp_on A R"
  by (auto simp add: totalp_on_def)

lemma antisymp_reflcp: "antisymp R \<Longrightarrow> antisymp R\<^sup>=\<^sup>="
  by (simp add: antisymp_def)

end