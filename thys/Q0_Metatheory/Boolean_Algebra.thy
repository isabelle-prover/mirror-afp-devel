section \<open>Boolean Algebra\<close>

theory Boolean_Algebra
  imports
    "ZFC_in_HOL.ZFC_Typeclasses"
begin

text \<open>This theory contains an embedding of two-valued boolean algebra into \<^term>\<open>V\<close>.\<close>

hide_const (open) List.set

definition bool_to_V :: "bool \<Rightarrow> V" where
  "bool_to_V = (SOME f. inj f)"

lemma bool_to_V_injectivity [simp]:
  shows "inj bool_to_V"
  unfolding bool_to_V_def by (fact someI_ex[OF embeddable_class.ex_inj])

definition bool_from_V :: "V \<Rightarrow> bool" where
  [simp]: "bool_from_V = inv bool_to_V"

definition top :: V ("\<^bold>T") where
  [simp]: "\<^bold>T = bool_to_V True"

definition bottom :: V ("\<^bold>F") where
  [simp]: "\<^bold>F = bool_to_V False"

definition two_valued_boolean_algebra_universe :: V ("\<bool>") where
  [simp]: "\<bool> = set {\<^bold>T, \<^bold>F}"

definition negation :: "V \<Rightarrow> V" ("\<sim> _" [141] 141) where
  [simp]: "\<sim> p = bool_to_V (\<not> bool_from_V p)"

definition conjunction :: "V \<Rightarrow> V \<Rightarrow> V" (infixr "\<^bold>\<and>" 136) where
  [simp]: "p \<^bold>\<and> q = bool_to_V (bool_from_V p \<and> bool_from_V q)"

definition disjunction :: "V \<Rightarrow> V \<Rightarrow> V" (infixr "\<^bold>\<or>" 131) where
  [simp]: "p \<^bold>\<or> q = \<sim> (\<sim> p \<^bold>\<and> \<sim> q)"

definition implication :: "V \<Rightarrow> V \<Rightarrow> V" (infixr "\<^bold>\<supset>" 121) where
  [simp]: "p \<^bold>\<supset> q = \<sim> p \<^bold>\<or> q"

definition iff :: "V \<Rightarrow> V \<Rightarrow> V" (infixl "\<^bold>\<equiv>" 150) where
  [simp]: "p \<^bold>\<equiv> q = (p \<^bold>\<supset> q) \<^bold>\<and> (q \<^bold>\<supset> p)"

lemma boolean_algebra_simps [simp]:
  assumes "p \<in> elts \<bool>" and "q \<in> elts \<bool>" and "r \<in> elts \<bool>"
  shows "\<sim> \<sim> p = p"
  and "((\<sim> p) \<^bold>\<equiv> (\<sim> q)) = (p \<^bold>\<equiv> q)"
  and "\<sim> (p \<^bold>\<equiv> q) = (p \<^bold>\<equiv> (\<sim> q))"
  and "(p \<^bold>\<or> \<sim> p) = \<^bold>T"
  and "(\<sim> p \<^bold>\<or> p) = \<^bold>T"
  and "(p \<^bold>\<equiv> p) = \<^bold>T"
  and "(\<sim> p) \<noteq> p"
  and "p \<noteq> (\<sim> p)"
  and "(\<^bold>T \<^bold>\<equiv> p) = p"
  and "(p \<^bold>\<equiv> \<^bold>T) = p"
  and "(\<^bold>F \<^bold>\<equiv> p) = (\<sim> p)"
  and "(p \<^bold>\<equiv> \<^bold>F) = (\<sim> p)"
  and "(\<^bold>T \<^bold>\<supset> p) = p"
  and "(\<^bold>F \<^bold>\<supset> p) = \<^bold>T"
  and "(p \<^bold>\<supset> \<^bold>T) = \<^bold>T"
  and "(p \<^bold>\<supset> p) = \<^bold>T"
  and "(p \<^bold>\<supset> \<^bold>F) = (\<sim> p)"
  and "(p \<^bold>\<supset> \<sim> p) = (\<sim> p)"
  and "(p \<^bold>\<and> \<^bold>T) = p"
  and "(\<^bold>T \<^bold>\<and> p) = p"
  and "(p \<^bold>\<and> \<^bold>F) = \<^bold>F"
  and "(\<^bold>F \<^bold>\<and> p) = \<^bold>F"
  and "(p \<^bold>\<and> p) = p"
  and "(p \<^bold>\<and> (p \<^bold>\<and> q)) = (p \<^bold>\<and> q)"
  and "(p \<^bold>\<and> \<sim> p) = \<^bold>F"
  and "(\<sim> p \<^bold>\<and> p) = \<^bold>F"
  and "(p \<^bold>\<or> \<^bold>T) = \<^bold>T"
  and "(\<^bold>T \<^bold>\<or> p) = \<^bold>T"
  and "(p \<^bold>\<or> \<^bold>F) = p"
  and "(\<^bold>F \<^bold>\<or> p) = p"
  and "(p \<^bold>\<or> p) = p"
  and "(p \<^bold>\<or> (p \<^bold>\<or> q)) = (p \<^bold>\<or> q)"
  and "p \<^bold>\<and> q = q \<^bold>\<and> p"
  and "p \<^bold>\<and> (q \<^bold>\<and> r) = q \<^bold>\<and> (p \<^bold>\<and> r)"
  and "p \<^bold>\<or> q = q \<^bold>\<or> p"
  and "p \<^bold>\<or> (q \<^bold>\<or> r) = q \<^bold>\<or> (p \<^bold>\<or> r)"
  and "(p \<^bold>\<or> q) \<^bold>\<or> r = p \<^bold>\<or> (q \<^bold>\<or> r)"
  and "p \<^bold>\<and> (q \<^bold>\<or> r) = p \<^bold>\<and> q \<^bold>\<or> p \<^bold>\<and> r"
  and "(p \<^bold>\<or> q) \<^bold>\<and> r = p \<^bold>\<and> r \<^bold>\<or> q \<^bold>\<and> r"
  and "p \<^bold>\<or> (q \<^bold>\<and> r) = (p \<^bold>\<or> q) \<^bold>\<and> (p \<^bold>\<or> r)"
  and "(p \<^bold>\<and> q) \<^bold>\<or> r = (p \<^bold>\<or> r) \<^bold>\<and> (q \<^bold>\<or> r)"
  and "(p \<^bold>\<supset> (q \<^bold>\<and> r)) = ((p \<^bold>\<supset> q) \<^bold>\<and> (p \<^bold>\<supset> r))"
  and "((p \<^bold>\<and> q) \<^bold>\<supset> r) = (p \<^bold>\<supset> (q \<^bold>\<supset> r))"
  and "((p \<^bold>\<or> q) \<^bold>\<supset> r) = ((p \<^bold>\<supset> r) \<^bold>\<and> (q \<^bold>\<supset> r))"
  and "((p \<^bold>\<supset> q) \<^bold>\<or> r) = (p \<^bold>\<supset> q \<^bold>\<or> r)"
  and "(q \<^bold>\<or> (p \<^bold>\<supset> r)) = (p \<^bold>\<supset> q \<^bold>\<or> r)"
  and "\<sim> (p \<^bold>\<or> q) = \<sim> p \<^bold>\<and> \<sim> q"
  and "\<sim> (p \<^bold>\<and> q) = \<sim> p \<^bold>\<or> \<sim> q"
  and "\<sim> (p \<^bold>\<supset> q) = p \<^bold>\<and> \<sim> q"
  and "\<sim> p \<^bold>\<or> q = (p \<^bold>\<supset> q)"
  and "p \<^bold>\<or> \<sim> q = (q \<^bold>\<supset> p)"
  and "(p \<^bold>\<supset> q) = (\<sim> p) \<^bold>\<or> q"
  and "p \<^bold>\<or> q = \<sim> p \<^bold>\<supset> q"
  and "(p \<^bold>\<equiv> q) = (p \<^bold>\<supset> q) \<^bold>\<and> (q \<^bold>\<supset> p)"
  and "(p \<^bold>\<supset> q) \<^bold>\<and> (\<sim> p \<^bold>\<supset> q) = q"
  and "p = \<^bold>T \<Longrightarrow> \<not> (p = \<^bold>F)"
  and "p = \<^bold>F \<Longrightarrow> \<not> (p = \<^bold>T)"
  and "p = \<^bold>T \<or> p = \<^bold>F"
  using assms by (auto simp add: inj_eq)

lemma tv_cases [consumes 1, case_names top bottom, cases type: V]:
  assumes "p \<in> elts \<bool>"
  and "p = \<^bold>T \<Longrightarrow> P"
  and "p = \<^bold>F \<Longrightarrow> P"
  shows P
  using assms by auto

end
