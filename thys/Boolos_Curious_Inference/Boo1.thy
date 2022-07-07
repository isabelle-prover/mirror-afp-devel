section \<open>Isabelle Formalization I\<close>

theory Boo1 imports Main
begin

text "Boolos's inference"

locale boolax_1 = 
  fixes F :: " 'a \<times> 'a \<Rightarrow> 'a "
  fixes s :: " 'a \<Rightarrow> 'a "
  fixes D :: " 'a \<Rightarrow>  bool "
  fixes e ::  " 'a "
  assumes A1: "F(x, e) = s(e)"
  and A2:  "F(e, s(y)) = s(s(F(e, y)))"
  and A3: "F(s(x), s(y)) = F(x, F(s(x), y))"
  and A4:  "D(e)"
  and A5: "D(x) \<longrightarrow> D(s(x))"

context boolax_1
begin

text "Definitions"

definition (in boolax_1) induct :: "'a set => bool"
  where " induct X \<equiv> e \<in> X \<and> (\<forall>x. (x \<in> X \<longrightarrow> s(x) \<in>  X))"

definition (in boolax_1) N :: "'a \<Rightarrow> bool"
  where "N x \<equiv> (\<forall>X. (induct X \<longrightarrow> x \<in> X))"

definition (in boolax_1) E :: "'a \<Rightarrow> bool"
  where "E x \<equiv> (N x \<and> D x)"

definition (in boolax_1) M :: "'a \<Rightarrow> bool"
  where "M x \<equiv> (\<forall>y. (N y \<longrightarrow>  E(F(x, y))))"

definition (in boolax_1) Q :: "'a \<Rightarrow> bool"
  where "Q x \<equiv> E(F(e, x))"

text "Lemmas"

lemma lem1: "N e" by (simp add: N_def induct_def)

lemma lem2: "N x \<longrightarrow> N(s(x))" by (simp add: N_def induct_def)

lemma lem3: "N(s(s(s(s(e)))))" by (simp add: lem1 lem2)

lemma lem4: "E e" using A4 E_def lem1 by auto

lemma lem5: "E x \<longrightarrow> E(s(x))" by (simp add: A5 E_def lem2)

lemma lem6: "E(s(e))" by (simp add: lem4 lem5)

lemma lem7: "Q e" by (simp add: A1 Q_def lem6)

lemma lem8: "Q x \<longrightarrow> Q(s(x))" by (simp add: A2 Q_def lem5)

lemma lem9: "N x \<longrightarrow> Q x" by (metis N_def induct_def lem7 lem8 mem_Collect_eq)

lemma lem10: "M e"  by (meson Q_def M_def lem9)

lemma lem11: "E (F(s(n), e))" by (simp add: A1 lem6)

lemma lem12: "M x \<and> E (F(s(x), y)) \<longrightarrow> E (F(s(x), s(y)))" by (simp add: A3 E_def M_def)

lemma lem13: "M x \<longrightarrow> induct {y. E (F(s(x), y))}" using A1 induct_def lem12 lem6 by auto

lemma lem14: "M x \<longrightarrow> M(s(x))" by (metis CollectD M_def N_def lem13)

lemma lem15: "N x \<longrightarrow> M x" by (metis N_def induct_def lem10 lem14 mem_Collect_eq)

lemma lem16: "N x \<and> N y \<longrightarrow> E(F(x,y))" using M_def lem15 by blast

lemma lem17: "E(F(s(s(s(s(e)))), s(s(s(s(e))))))" by (simp add: lem16 lem3)

lemma lem18: "D(F(s(s(s(s(e)))), s(s(s(s(e))))))" using E_def lem17 by auto

end

end