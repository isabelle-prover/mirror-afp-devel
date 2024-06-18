\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Niklas Krofta"\<close>
subsubsection \<open>Well-Founded Relations\<close>
theory Binary_Relations_Wellfounded
  imports
    Binary_Relation_Functions
begin

consts wellfounded :: "'a \<Rightarrow> bool"

overloading
  wellfounded_rel \<equiv> "wellfounded :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "wellfounded_rel R \<equiv> \<forall>P. (\<exists>x. P x) \<longrightarrow> (\<exists>m : P. \<forall>y. R y m \<longrightarrow> \<not>(P y))"
end

lemma wellfoundedI:
  assumes "\<And>P x. P x \<Longrightarrow> (\<exists>m : P. \<forall>y. R y m \<longrightarrow> \<not>(P y))"
  shows "wellfounded R"
  using assms unfolding wellfounded_rel_def by blast

lemma wellfoundedE:
  assumes "wellfounded R" "P x"
  obtains m where "P m" "\<And>y. R y m \<Longrightarrow> \<not>(P y)"
  using assms unfolding wellfounded_rel_def by blast

lemma wellfounded_induct [consumes 1, case_names step]:
  assumes wf: "wellfounded R"
  assumes step: "\<And>x. (\<And>y. R y x \<Longrightarrow> P y) \<Longrightarrow> P x"
  shows "P x"
proof (rule ccontr)
  assume "\<not>(P x)"
  then obtain m where "\<not>(P m)" "\<And>y. R y m \<longrightarrow> P y"
    using wf wellfoundedE[where P="\<lambda>x. \<not>(P x)"] by auto
  with step show "False" by auto
qed


end