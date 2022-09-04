section \<open>Isabelle Formalization II\<close>

theory Boo2 imports Main
begin 

text "Boolos's inference" 

locale boolax_2 = 
 fixes F :: " 'a \<times> 'a \<Rightarrow>  'a " 
 fixes s :: " 'a \<Rightarrow> 'a "
 fixes D :: " 'a \<Rightarrow> bool "
 fixes e ::  " 'a "
 assumes A1: "F(x, e) = s(e)"
 and A2:  "F(e, s(y)) = s(s(F(e, y)))"
 and A3: "F(s(x), s(y)) = F(x, F(s(x), y))"
 and A4:  "D(e)"
 and A5: "D(x) \<longrightarrow> D(s(x))"

context boolax_2
begin 

text "Definitions" 

definition (in boolax_2) induct :: "'a set \<Rightarrow> bool"
 where "induct X \<equiv> (e \<in> X \<and> (\<forall>x. (x \<in> X \<longrightarrow> s(x) \<in>  X)))" 

definition (in boolax_2) N :: "'a set"
 where "N = {x. (\<forall>Y. (induct Y \<longrightarrow> x \<in> Y))}" 

definition (in boolax_2) P1 :: "'a \<Rightarrow> 'a \<Rightarrow> bool" 
  where "P1 x y \<equiv> F(x,y) \<in> N" 

definition (in boolax_2) P2 :: "'a \<Rightarrow> bool"
  where "P2 x \<equiv> N \<subseteq> {y. P1 x y}"

text "Lemmas" 
text "I. Basic Lemmas" 

lemma Induction_wrt_N: "induct X \<longrightarrow> N \<subseteq> X" using N_def by auto 

lemma N_is_inductive: "induct N" by (simp add: N_def induct_def) 

lemma D_is_inductive: "induct {x. D(x)}" using A4 A5 induct_def by auto 

lemma Four_in_N: "s(s(s(s(e)))) \<in> N" using induct_def N_is_inductive by auto 

text "II. Proof that ${x. P1 e x}$ is inductive" 

lemma P1ex_basis: "P1 e e"  using A1 P1_def induct_def N_is_inductive by auto 

lemma P1ex_closed: "P1 e x \<longrightarrow> P1 e (s(x))" using A2 P1_def induct_def N_is_inductive by auto 

lemma P1ex_inductive: "induct {x. P1 e x}" using induct_def P1ex_basis P1ex_closed by auto

text "III. Proof that ${x. P2 x}$ is inductive" 

lemma P1sx_basis: "P1 (s(x)) e" using A1 P1_def induct_def N_is_inductive by auto 

lemma P2_basis: "P2 e" by (simp add: P2_def Induction_wrt_N P1ex_inductive) 

lemma P2_closeda: "P2 x \<longrightarrow> (\<forall>y. (P1 (s(x)) y \<longrightarrow> P1 (s(x)) (s(y))))"  using A3 P1_def P2_def by auto 

lemma P2_closedb: "P2 x \<longrightarrow> P2(s(x))" using P2_def induct_def Induction_wrt_N P1sx_basis P2_closeda by auto 

lemma P2_inductive: "induct {x. P2 x}"  using induct_def P2_basis P2_closedb by auto

text "IV. Proof that $N$ is closed under $F$" 

lemma N_closed_F: "x \<in> N \<and> y \<in> N \<longrightarrow> F(x,y) \<in> N"  using Induction_wrt_N P1_def P2_def P2_inductive by auto

text "V. Conclusion" 

lemma F_Four_in_D: "D(F(s(s(s(s(e)))), s(s(s(s(e))))))" using D_is_inductive Four_in_N N_closed_F Induction_wrt_N by auto 

end 
end