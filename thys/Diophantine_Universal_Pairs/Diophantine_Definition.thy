theory Diophantine_Definition 
  imports "MPoly_Utils/More_More_MPoly_Type"
begin

definition is_nonnegative :: "(nat \<Rightarrow> int) \<Rightarrow> bool" where 
  "is_nonnegative f \<equiv> \<forall>i. f i \<ge> 0"

definition is_diophantine_over_Z :: "nat set \<Rightarrow> bool" where 
  "is_diophantine_over_Z A = (\<exists>P.
    (\<forall>a. (a \<in> A) \<longleftrightarrow> (\<exists>f. insertion (f(0 := int a)) P = 0)))"

definition is_diophantine_over_Z_with :: "nat set \<Rightarrow> int mpoly \<Rightarrow> bool" where 
  "is_diophantine_over_Z_with A P =
    (\<forall>a. (a \<in> A) \<longleftrightarrow> (\<exists>f. insertion (f(0 := int a)) P = 0))"

definition is_diophantine_over_N :: "nat set \<Rightarrow> bool" where 
  "is_diophantine_over_N A = (\<exists>P.
    (\<forall>a. (a \<in> A) \<longleftrightarrow> (\<exists>f. insertion (f(0 := int a)) P = 0 \<and> is_nonnegative f)))"

definition is_diophantine_over_N_with :: "nat set \<Rightarrow> int mpoly \<Rightarrow> bool" where 
  "is_diophantine_over_N_with A P =
    (\<forall>a. (a \<in> A) \<longleftrightarrow> (\<exists>f. insertion (f(0 := int a)) P = 0 \<and> is_nonnegative f))"

lemma is_diophantine_finite_vars:
  assumes "is_diophantine_over_N_with A P"
  shows "a \<in> A \<longleftrightarrow> (\<exists>f. insertion (f(0 := int a)) P = 0 \<and> is_nonnegative f \<and> (\<forall>i > max_vars P. f i = 0))"
proof (cases "a \<in> A")
  case True
  with assms obtain f where f_def: "insertion (f(0 := int a)) P = 0 \<and> is_nonnegative f"
    unfolding is_diophantine_over_N_with_def by auto
  define f' where "f' \<equiv> (\<lambda>i. if i \<le> max_vars P then f i else 0)"
  have 1: "\<And>v. v \<in> vars P \<Longrightarrow> (f(0 := int a)) v = (f'(0 := int a)) v"
    unfolding f'_def max_vars_def
    by simp (subst Max.coboundedI, auto simp: vars_finite)
  have "insertion (f'(0 := int a)) P = 0"
    apply (subst insertion_irrelevant_vars[of P _ "f(0 := int a)"])
    unfolding 1 by (auto simp: f_def)
  thus ?thesis
    apply (simp add: True)
    apply (rule exI[of _ f'])
    using f_def by (auto simp: f'_def is_nonnegative_def)
next
  case False
  then show ?thesis
    using assms unfolding is_diophantine_over_N_with_def by auto
qed

end