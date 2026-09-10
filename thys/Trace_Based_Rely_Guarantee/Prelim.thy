section \<open>Introduction\<close>

text \<open>
  This development provides a formalization of a trace-based Rely-Guarantee semantics. 
  The core approach is built upon the foundational work of Xu et al.~\cite{Xu_et_al}, 
  who established a framework for reasoning about concurrent programs using interactive traces. 

  To support this semantics, we first define an abstract programming language featuring 
  sequential composition, while loops, and parallel execution. This language is equipped 
  with an operational semantics explicitly designed to facilitate concurrent reasoning by 
  interleaving command executions with environment steps. 

  Building upon these trace-based foundations, we develop a robust reasoning infrastructure. 
  This includes comprehensive Rely-Guarantee inversion rules that characterize the structural 
  decomposition of traces, abstract definitions of trace satisfiability, and standard 
  soundness proofs adapted for both unary and binary postcondition settings.

  The formalization presented here serves as the foundational basis for the broader 
  investigations into coinductive Rely-Guarantee semantics and equivalence proofs 
  described by Derrick et al.~\cite{RelyGuarantee}.
\<close>
section \<open>Preliminaries\<close>
text \<open>This theory sets up notation and preliminary definitions used throughout the mechanization \<close>
                       
theory Prelim imports Complex_Main
begin

(* Facts that are very useful in proofs:*)

thm le_fun_def
thm relcompp_apply 
thm relcompp.simps

hide_const stable

(* Lists *)

lemma map_Pair_zip_replicate_length: 
"map (Pair x) ys = zip (replicate (length ys) x) ys" 
by (simp add: zip_replicate1)


(* Reflexive-transitive closures *)

lemma OO_rtranclp_le: 
assumes "U OO A \<le> V" "(U OO Z^**) OO (Z OO A) \<le> V"
shows "(U OO Z^**) OO A \<le> V"
using assms unfolding OO_def  
by auto (smt (verit, best) predicate2D rtranclp.simps)


lemma rtranclp_chain: 
assumes "R\<^sup>*\<^sup>* a b"
shows "\<exists>n as. as 0 = a \<and> as n = b \<and> (\<forall>i<n. R (as i) (as (Suc i)))" 
using assms proof induction
  case base
  then show ?case 
  apply(intro exI[of _ 0] exI[of _ "\<lambda>i. a"])
  by auto
next
  case (step b c)  
  show ?case using step apply safe
  subgoal for n as 
  apply(intro exI[of _ "Suc n"] exI[of _ "\<lambda>i. if i \<le> n then as i else c"]) 
  using le_less_Suc_eq by force .
qed

lemma chain_rtranclp: 
assumes "as 0 = a" "as n = b" "\<forall>i<n. R (as i) (as (Suc i))" 
shows "R\<^sup>*\<^sup>* a b"
using assms apply(induct n arbitrary: b) by auto


(* Logical operators on predicates and relations *)

definition notP :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" 
("\<not>1 _" [40] 70)
where
"\<not>1 P \<equiv> \<lambda>a. \<not> P a"

definition conjP :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" 
(infixr "\<and>1" 65)
where
"P1 \<and>1 P2 \<equiv> \<lambda>a. P1 a \<and> P2 a"

definition disjP :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" 
(infixr "\<or>1" 60)
where
"P1 \<or>1 P2 \<equiv> \<lambda>a. P1 a \<or> P2 a"

(* *)

definition notR :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)" 
("\<not>2 _" [40] 40)
where
"\<not>2 R \<equiv> \<lambda>a b. \<not> R a b"

definition conjR :: 
"('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  
(infixr "\<and>2" 65)
where
"R1 \<and>2 R2 \<equiv> \<lambda>a b. R1 a b \<and> R2 a b"

definition disjR :: 
"('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  
(infixr "\<or>2" 60)
where
"R1 \<or>2 R2 \<equiv> \<lambda>a b. R1 a b \<or> R2 a b"

definition interR :: 
"('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  
(infixr "\<inter>2" 70)
where
"R1 \<inter>2 R2 \<equiv> \<lambda>a b. \<forall>c d. R1 c d \<and> R2 c d \<longrightarrow> a = c \<and> b = d "

definition satR ::
"('a \<Rightarrow> 'b \<Rightarrow> bool)"
where
"satR  \<equiv> \<lambda>a b. True"
(* *)

definition imR :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)" where 
"imR R P \<equiv> \<lambda>b. \<exists>a. P a \<and> R a b" 

lemmas imR_defs = imR_def le_bool_def le_fun_def

definition rimR :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" where 
"rimR R P \<equiv> \<lambda>a. \<exists>b. P b \<and> R a b" 

definition grR :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool" where 
"grR f \<equiv> (\<lambda>a b. f a = b)"

definition diagR :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where 
"diagR P \<equiv> \<lambda>a b. a = b \<and> P a"

(* *)

definition lift1 :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
where "lift1 P \<equiv> \<lambda>a b. P a"

definition lift2 :: "('b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
where "lift2 P \<equiv> \<lambda>a b. P b"

lemma lift1_mono: "P1 \<le> P2 \<Longrightarrow> lift1 P1 \<le> lift1 P2"
unfolding lift1_def by auto

lemma lift2_mono: "P1 \<le> P2 \<Longrightarrow> lift2 P1 \<le> lift2 P2"
unfolding lift2_def by auto

lemma conjR_lift2_rel_1_OO: "(R \<and>2 lift2 P) OO Q = R OO (lift1 P \<and>2 Q)"
unfolding conjR_def lift2_def lift1_def by auto

lemma conjP_idem[simp]: "P \<and>1 P = P"
unfolding conjP_def by auto

lemma disjP_idem[simp]: "P \<or>1 P = P"
unfolding disjP_def by auto

lemma conjR_idem[simp]: "R \<and>2 R = R"
unfolding conjR_def by auto

lemma disjR_idem[simp]: "R \<or>2 R = R"
unfolding disjR_def by auto

lemma conjP_idem2[simp]: "P \<and>1 P \<and>1 P' = P \<and>1 P'"
  by (simp add: conjP_def)

lemma notP_item: "\<not> P s \<longleftrightarrow> (\<not>1 P) s"
  by (simp add: notP_def)

lemma disjR_I1[intro]:"P s s' \<Longrightarrow> (P \<or>2 Q) s s'" unfolding disjR_def by auto
lemma disjR_I2[intro]:"Q s s' \<Longrightarrow> (P \<or>2 Q) s s'" unfolding disjR_def by auto


lemma conjR_I:"Q1 s s' \<and> Q2 s s' \<Longrightarrow> Q1 \<and>2 Q2 \<le> Q \<Longrightarrow> Q s s'" unfolding conjR_def by auto


lemma lift1_inject:"lift1 P \<le> Q \<Longrightarrow> P s \<Longrightarrow> \<forall>s'. Q s s' " unfolding lift1_def le_bool_def le_fun_def by auto

(* Stability *)

(* Predicate P is stable under (the change induced by) relation R *)
definition stable :: "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool" where 
"stable P R \<equiv> \<forall> s s'. P s \<and> R s s' \<longrightarrow> P s'"

(* Q is stable under left-composition from R: *)
definition stableLeft :: "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool" where 
"stableLeft Q R \<equiv> R OO Q \<le> Q"

(* Q is stable under right-composition from R: *)
definition stableRight :: "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool" where 
"stableRight Q R \<equiv> Q OO R \<le> Q"

definition stable2 :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where 
"stable2 Q R \<equiv> stableLeft Q R \<and> stableRight Q R"

lemma stable2_def2: "stable2 Q R \<longleftrightarrow> R OO Q \<le> Q \<and> Q OO R \<le> Q"
by (simp add: stable2_def stableLeft_def stableRight_def)

lemma stableLeft_alt:  
"stableLeft Q R \<longleftrightarrow> 
 (\<forall> s s' s''. R s s' \<and> Q s' s'' \<longrightarrow> Q s s'')"
unfolding stableLeft_def by auto  

lemma stableRight_alt:  
"stableRight Q R \<longleftrightarrow> 
 (\<forall> s s' s''. Q s s' \<and> R s' s'' \<longrightarrow> Q s s'')"
unfolding stableRight_def by auto 
lemmas stable2_defs = stable2_def stableRight_alt stableLeft_alt
lemma stable_stable2: 
"stable P R \<longleftrightarrow> stable2 (lift2 P) R"
unfolding stable_def stable2_def stableLeft_def 
stableRight_def lift2_def by auto

lemma stable_rtraclp: 
assumes "stable P R"
shows "stable P R^**" 
unfolding stable_def proof safe
  fix s s' assume "R\<^sup>*\<^sup>* s s'" "P s" 
  thus "P s'"
  apply induct using assms unfolding stable_def by auto
qed 

lemma stableLeft_rtraclp: 
assumes "stableLeft Q R"
shows "stableLeft Q R^**" 
unfolding stableLeft_def OO_def proof safe
  fix s s' s'' assume "R\<^sup>*\<^sup>* s s'" "Q s' s''" 
  thus "Q s s''"
  apply induct using assms unfolding stableLeft_def by auto
qed 

lemma stableRight_rtraclp: 
assumes "stableRight Q R"
shows "stableRight Q R^**" 
unfolding stableRight_def OO_def proof safe
  fix s s' s'' assume "R\<^sup>*\<^sup>* s' s''" "Q s s'" 
  thus "Q s s''"
  apply induct using assms unfolding stableRight_def by auto
qed 

lemma stable2_rtraclp: 
assumes "stable2 Q R"
shows "stable2 Q R^**"
using assms stable2_def stableLeft_rtraclp stableRight_rtraclp by blast

(* *)

lemma stable_Eq[simp,intro!]: 
"stable P (=)"  
unfolding stable_def by blast

lemma stable_OO: 
assumes "stable P R1" "stable P R2"
shows "stable P (R1 OO R2)"
using assms unfolding stable_def by blast

lemma stableLeft_Eq[simp,intro!]: 
"stableLeft Q (=)"  
unfolding stableLeft_def by blast

lemma stableLeft_OO: 
assumes "stableLeft Q R1" "stableLeft Q R2"
shows "stableLeft Q (R1 OO R2)"
using assms unfolding stableLeft_def by blast

lemma stableRight_Eq[simp,intro!]: 
"stableRight Q (=)"  
unfolding stableRight_def by blast

lemma stableRight_OO: 
assumes "stableRight Q R1" "stableRight Q R2"
shows "stableRight Q (R1 OO R2)"
using assms unfolding stableRight_def by blast

lemma stable2_Eq[simp,intro!]: 
"stable2 Q (=)"  
unfolding stable2_def by blast

lemma stable2_OO: 
assumes "stable2 Q R1" "stable2 Q R2"
shows "stable2 Q (R1 OO R2)"
by (meson assms stable2_def stableLeft_OO stableRight_OO)

lemma stable_iff_imR: "stable P R \<longleftrightarrow> imR R P \<le> P"
unfolding stable_def imR_def by auto

lemma stable_imR_rtraclp: "stable P R \<Longrightarrow> imR (R^**) P \<le> P"
by (meson stable_iff_imR stable_rtraclp)

lemma stable_lift1_lift2: "stable P R \<Longrightarrow> lift1 P \<and>2 R \<le> R \<and>2 lift2 P"
unfolding stable_def lift1_def lift2_def conjR_def by auto

lemma stable_lift1_lift2_rtraclp: "stable P R \<Longrightarrow> lift1 P \<and>2 R^** \<le> R^** \<and>2 lift2 P"
by (simp add: stable_lift1_lift2 stable_rtraclp)

lemma stableLeft_OO_leq: "stableLeft Q R \<Longrightarrow> Q1 \<le> Q \<Longrightarrow> R OO Q1 \<le> Q"
by (simp add: order_subst2 relcompp_mono stableLeft_def)

lemma stable2_OO_leqL: "stable2 Q R \<Longrightarrow> Q1 \<le> Q \<Longrightarrow> R OO Q1 \<le> Q"
by (simp add: stable2_def stableLeft_OO_leq)

lemma stableRight_OO_leq: "stableRight Q R \<Longrightarrow> Q1 \<le> Q \<Longrightarrow> Q1 OO R \<le> Q"
by (meson dual_order.trans order_refl relcompp_mono stableRight_def)

lemma stable2_OO_leqR: "stable2 Q R \<Longrightarrow> Q1 \<le> Q \<Longrightarrow> Q1 OO R \<le> Q"
by (simp add: stable2_def stableRight_OO_leq)

lemma stable2_imp_OO: 
assumes "stable2 Q R1" "stable2 Q R2"
shows "R1 OO Q OO R2 \<le> Q"
by (meson assms stable2_OO_leqL stable2_def stableRight_def)
  
lemma stable2_OO_leq: "stable2 Q R1 \<Longrightarrow> stable2 Q R2 \<Longrightarrow> 
  Q' \<le> Q \<Longrightarrow> R1 OO Q' OO R2 \<le> Q"
by (simp add: stable2_OO_leqL stable2_OO_leqR)

lemma stableLeft_lift2[simp,intro!]: "stableLeft (lift2 P) R"
unfolding stableLeft_def lift2_def by auto

lemma stableRight_lift1[simp,intro!]: "stableRight (lift1 P) R"
unfolding stableRight_def lift1_def by auto

(* *)

lemma rtranclp_least: "(=) \<le> Z \<Longrightarrow> Z OO A \<le> Z \<Longrightarrow> A\<^sup>*\<^sup>* \<le> Z"
  by (metis eq_OO stableRight_OO_leq stableRight_def stableRight_rtraclp)

(* Inductive predicate which behaves the same as rtranclp, with the addition of a measure *)

inductive
  R_star where
refl[simp]:  "R_star 0 R s s" |
stepRel:  "R s s' \<Longrightarrow> R_star n R s' s'' \<Longrightarrow> R_star (Suc n) R s s'' "


lemma R_star0[simp]:"Ex (R_star 0 R sa)" by (meson R_star.refl)
lemma R_star_refl:"R_star 0 R s s' \<Longrightarrow> s = s'" using refl by (metis R_star.simps Zero_not_Suc)
lemma R_starRR:"R_star n R s s' \<Longrightarrow> R s' s'' \<Longrightarrow> R_star (Suc n) R s s''"
  apply(induction rule: R_star.induct)
  subgoal for s by(rule stepRel, auto)
  subgoal by (meson R_star.stepRel) .

lemma R_star_imp: "R_star n R s s' \<Longrightarrow> R\<^sup>*\<^sup>* s s'" 
  apply(induction rule: R_star.induct)
  using R_star.cases by auto

lemma R_step_star:"R\<^sup>*\<^sup>* s s' = (\<exists>n. R_star n R s s')"
  apply(standard)
  subgoal by(induction rule: rtranclp.induct,(metis R_star.refl R_starRR)+)
  using R_star_imp by metis

lemma Suc_assoc:"(Suc (x + y)) = (Suc x + y)" by auto

lemma R_star_trans:
  assumes "R_star n R x y"
    and "R_star m R y z"
  shows "R_star (n+m) R x z"
  using assms(2,1) apply-apply(induction arbitrary: n x rule: R_star.induct,simp_all)
  subgoal premises p for R s s' n s'' na x  unfolding Suc_assoc
    apply(rule  p(3)[of "Suc na" x])
    using p(1,4) apply-by(drule R_starRR, assumption+) .

(*star relations *)

inductive
  star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

hide_fact (open) refl step  \<comment> \<open>names too generic\<close>

lemma star_trans:
  "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
proof(induction rule: star.induct)
  case refl thus ?case .
next
  case step thus ?case by (metis star.step)
qed

lemmas star_induct =
  star.induct[of "r:: 'a*'b \<Rightarrow> 'a*'b \<Rightarrow> bool", split_format(complete)]
lemmas star_cases =
  star.cases[of "r:: 'a*'b \<Rightarrow> 'a*'b \<Rightarrow> bool", split_format(complete)]

declare star.refl[simp,intro]

lemma star_step1[simp, intro]: "r x y \<Longrightarrow> star r x y"
  by(metis star.refl star.step)

definition "final r x \<equiv> \<forall>y. \<not> r x y"

lemma final_star_eq: "final r x \<Longrightarrow> star r x y \<Longrightarrow> x = y"
by (metis final_def star.cases)
code_pred star .

lemma add_less:"\<forall>i'. i \<noteq> (x::nat) + i' \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> i < x"  by (metis add_diff_inverse_nat) 

lemma Suc_red:"Suc x = n + Suc m' \<longleftrightarrow> x = n + m'" "Suc x = Suc n + m' \<longleftrightarrow> x = n + m'" by auto

lemma le_Suc_iff0: \<open>m \<le> Suc n \<longleftrightarrow> m = 0 \<or> (\<exists>m'. m = Suc m' \<and> m' \<le> n)\<close>
  by presburger

(* A basic Step Locale *)

locale Step = 
fixes 
small_step :: "'com \<times> 'state \<Rightarrow> 'com \<times> 'state \<Rightarrow> bool" (infix "\<rightarrow>" 55) and 
final :: "'com \<times> 'state \<Rightarrow> bool"
begin


abbreviation
  small_steps :: "'com \<times> 'state \<Rightarrow> 'com \<times> 'state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
  where "x \<rightarrow>* y == star small_step x y"


inductive step_rel where
R_Step:"R s s' \<Longrightarrow> step_rel R (c, s) (c, s')"
|
S_Step:"small_step (c, s) (c', s') \<Longrightarrow> step_rel R (c, s) (c', s')"

lemma step_rel_cases_cfg [consumes 1, case_names R_Step S_Step, elim]:
  assumes "step_rel R (c, s) cfg'"
  obtains (R_Step) s' where "cfg' = (c, s')" and "R s s'"
        | (S_Step) c' s' where "cfg' = (c', s')" and "(c, s) \<rightarrow> (c', s')"
  using assms by (cases rule: step_rel.cases) auto

inductive_cases step_rel_inv_cases [elim!]: "step_rel R (c, s) (c', s')"

lemma step_rel_strengthenR:"step_rel R (c, s) (c', s') \<Longrightarrow> R \<le> R' \<Longrightarrow> step_rel R' (c, s) (c', s')"
  apply(cases rule: step_rel.cases)
  using predicate1D step_rel.simps by auto 

lemma step_rel_cases: "step_rel R (c, s) (c', s') \<Longrightarrow> (c = c' \<Longrightarrow> R s s' \<Longrightarrow> P) \<Longrightarrow> 
                                                      ((c, s) \<rightarrow> (c', s') \<Longrightarrow> P) \<Longrightarrow> P"
  by(cases rule: step_rel.cases[of R "(c, s)" "(c', s')"], simp_all) 


definition "lift R \<equiv> (\<lambda>(c,s) (c',s'). c' = c \<and> R s s')"

lemma rtranclp_lift_extract:
  assumes "(lift R)\<^sup>*\<^sup>* (c, s) (c', s')"
  shows "c = c' \<and> R\<^sup>*\<^sup>* s s'"
  using assms
  apply (induct rule: rtranclp_induct2, simp)
  unfolding lift_def case_prod_beta by auto

(* fair step-rel (makes sure that at least one computation step takes place) *)
definition "fstep_rel R \<equiv> rtranclp (lift R) OO small_step "\<comment> \<open> OO rtranclp (lift R) \<close>


(**)

lemma rel_incl_lift_rtranclp: "R\<^sup>*\<^sup>* s s'' \<Longrightarrow> (lift R)\<^sup>*\<^sup>* (c, s) (c, s'')"
apply(induct rule: rtranclp.induct) 
  subgoal by simp
  subgoal for s s' s'' apply(subgoal_tac "(lift R) (c, s') (c, s'')") 
    subgoal by simp
    subgoal unfolding lift_def by simp . .

lemma rtranclp_small_step_fstep_rel: 
assumes R: "R\<^sup>*\<^sup>* s s''" and st: "(c, s'') \<rightarrow> (c1, s1)"
shows "fstep_rel R (c, s) (c1, s1)"
proof-
  have "rtranclp (lift R) (c, s) (c, s'')" using rel_incl_lift_rtranclp[OF R] . 
  thus ?thesis using st unfolding fstep_rel_def by blast
qed

lemma lift_fst: "lift R cfg cfg' \<Longrightarrow> fst cfg' = fst cfg"
unfolding lift_def by auto

lemma rtranclp_lift_fst: "rtranclp (lift R) cfg cfg' \<Longrightarrow> fst cfg' = fst cfg"
  apply (induct rule: rtranclp.induct) using lift_fst by auto
end

(* lemma used in both trace and coleman jones variations *)
lemma whileAssms_inject:
  assumes st: "stable P R" "stable2 Q R" "stable2 Pt1 R" 
      and Pr1: "(evalT t) \<and>1 P \<le> Pr1"
      and P: "imR Pt1 ((evalT t) \<and>1 Pr1) \<le> P"
      and Q: "lift1 P \<and>2 (lift1 (evalT t \<and>1 P) \<and>2 Pt1)^** \<and>2 lift2 (\<not>1 evalT t) \<le> Q"  
shows 
    "imR (R\<^sup>*\<^sup>* \<and>2 lift2 (evalT t)) P \<le> Pr1"
    "imR Pt1 (imR R\<^sup>*\<^sup>* (imR R\<^sup>*\<^sup>* P \<and>1 evalT t) \<and>1 Pr1) \<le> P"
    "(lift1 P \<and>2 ((((lift1 P \<and>2 R\<^sup>*\<^sup>*) \<and>2 lift2 (evalT t)) OO R\<^sup>*\<^sup>*) OO Pt1)\<^sup>*\<^sup>*) OO (R\<^sup>*\<^sup>* \<and>2 lift2 (\<not>1 evalT t)) OO R\<^sup>*\<^sup>* \<le> Q"
proof-
  have sst: "stable P R^**" "stable2 Q R^**" "stable2 Pt1 R^**"
  by (simp add: st stable_rtraclp stable2_rtraclp)+

  have Pt0: "lift1 P \<and>2 (=) \<and>2 lift2 (\<not>1 evalT t) \<le> Q"
  using Q unfolding conjR_def lift2_def by auto

  have Pt00: "lift1 P \<and>2 (lift1 (evalT t \<and>1 P) \<and>2 Pt1) \<and>2 lift2 (\<not>1 evalT t) \<le> Q"
  using Q unfolding conjR_def lift2_def by auto

  thus PPr1: "imR ((R^** \<and>2 lift2 (evalT t))) P \<le> Pr1" using Pr1
  using sst(1) unfolding imR_def conjR_def conjP_def lift2_def stable_def by auto

  have "imR Pt1 (imR R^** (imR R^** P \<and>1 (evalT t)) \<and>1 Pr1) \<le> imR Pt1 ((evalT t) \<and>1 Pr1)"
    using sst(3) st(1) Pr1 le_boolD 
    unfolding imR_def conjP_def stable2_def2 stable_def conjP_def le_fun_def le_bool_def
    by (smt (verit) relcomppI rtranclp_induct)
    
  thus PPr: "imR Pt1 (imR R^** (imR R^** P \<and>1 (evalT t)) \<and>1 Pr1) \<le> P"
  using P by auto

  define A B where 
  A_def: "A = (lift1 P \<and>2 R^**) OO (lift1 (evalT t \<and>1 P) \<and>2 Pt1)" and 
  B_def: "B = (R^** \<and>2 lift2 (\<not>1 evalT t))"
 
  have AA: "(((lift1 P \<and>2 R^** ) \<and>2 lift2 (evalT t)) OO R^** ) OO Pt1 \<le> 
        A"
  using sst(1,3) 
  unfolding A_def lift1_def lift2_def conjR_def conjP_def OO_def stable_def stable2_def2
  by blast

  hence 0: "((((lift1 P \<and>2 R^**) \<and>2 lift2 (evalT t)) OO R^**) OO Pt1)^** OO 
         ((R^** \<and>2 lift2 (\<not>1 evalT t)) OO R^**)
         \<le> 
         A ^** OO ((R^** \<and>2 lift2 (\<not>1 evalT t)) OO R^**)"
  by (simp add: relcompp_mono rtranclp_mono)

  have 11: "A OO B \<le> A \<and>2 lift2 (\<not>1 evalT t)"
  using sst(3) unfolding lift2_def conjR_def OO_def A_def B_def lift1_def stable2_def2
  by blast

  have 111: "A^** OO B = ((A^** OO A) OO B) \<or>2 B" 
  unfolding OO_def disjR_def fun_eq_iff 
  by (smt (verit, ccfv_threshold) OO_def disjR_def predicate2I rtranclp.simps)

  have 2: "A^** OO B \<le> (A^** OO (A \<and>2 lift2 (\<not>1 evalT t))) \<or>2 B"  
  unfolding 111 using 11  
  by (smt (verit) disjR_def predicate2D predicate2I relcompp_assoc relcompp_mono)
  
  have "A^** OO (A \<and>2 lift2 (\<not>1 evalT t)) \<le> A^** \<and>2 lift2 (\<not>1 evalT t)"
  unfolding OO_def lift2_def conjR_def by auto
  hence AB: "A^** OO B \<le> (A^** \<and>2 lift2 (\<not>1 evalT t)) \<or>2 B"
  by (smt (z3) "11" "111" disjR_def predicate2D predicate2I relcompp_assoc relcompp_mono)

  have B: "lift1 P \<and>2 B \<le> Q" unfolding B_def
    using Pt0 unfolding lift2_def conjR_def  
    using sst(2) unfolding stable2_def2  
    by (smt (z3) Prelim.stable_def le_fun_def predicate2I lift1_def relcomppI rev_predicate1D sst(1))

  define Z where "Z \<equiv> R^** OO (lift1 (evalT t \<and>1 P) \<and>2 Pt1)\<^sup>*\<^sup>*"
  have Z1: "(=) \<le> Z" unfolding Z_def by auto

  have OO_A_lq: "(lift1 (evalT t \<and>1 P) \<and>2 Pt1) OO A \<le> (lift1 (evalT t \<and>1 P) \<and>2 Pt1)\<^sup>*\<^sup>*"
  unfolding A_def lift1_def conjR_def conjP_def OO_def  
  by auto (smt (verit, del_insts) converse_rtranclp_into_rtranclp le_fun_def 
  predicate1D r_into_rtranclp relcomppI sst(3) stable2_def2)

  have Z2: "Z OO A \<le> Z"
  unfolding Z_def apply(rule OO_rtranclp_le)
    subgoal unfolding A_def lift1_def conjR_def conjP_def OO_def  
    using rtranclp_trans by fastforce
    subgoal using OO_A_lq predicate2D by fastforce .

  have "A^** \<le> Z" using Z1 Z2 rtranclp_least by blast 
  moreover have "lift1 P \<and>2 Z \<and>2 lift2 (\<not>1 evalT t) \<le> Q" using Q unfolding Z_def 
  using sst(1,2) unfolding lift1_def lift2_def conjR_def stable_def stable2_def2  
  by blast 
  ultimately have C: "lift1 P \<and>2 A^** \<and>2 lift2 (\<not>1 evalT t) \<le> Q" 
  by (smt (verit, del_insts) conjR_def predicate2D predicate2I)

  have aux: "(lift1 P \<and>2 A^**) OO B = lift1 P \<and>2 (A^** OO B)"  
    by (metis (no_types, opaque_lifting) conjR_lift2_rel_1_OO eq_OO relcompp_assoc)

  have "(lift1 P \<and>2 A^**) OO B \<le> Q" unfolding aux using B C AB   
  by (smt (verit, ccfv_threshold) conjR_def disjR_def le_fun_def order_refl) 

  hence 00: "(lift1 P \<and>2 A^**) OO (B OO R^**) \<le> Q"  
    using sst(2) stable2_OO_leqR by fastforce

  thus PPt: "(lift1 P \<and>2 ((((lift1 P \<and>2 R^**) \<and>2 lift2 (evalT t)) OO R^**) OO Pt1)^**) OO 
         ((R^** \<and>2 lift2 (\<not>1 evalT t)) OO R^**) \<le> Q"
  using 0 AA unfolding A_def B_def using conjR_def predicate2I relcompp_mono rev_predicate2D rtranclp_mono 
  by (smt (z3)) 
qed


(****)

inductive terminFrom for R where
 "(\<And>cfg'. R cfg cfg' \<Longrightarrow> terminFrom R cfg') \<Longrightarrow> terminFrom R cfg"


lemma terminFrom_induct_split [consumes 1, case_names Step]:
  assumes "terminFrom R (c, s)"
  assumes "\<And>c s. (\<And>c' s'. R (c, s) (c', s') \<Longrightarrow> terminFrom R (c', s') \<and> P c' s') \<Longrightarrow> P c s"
  shows "P c s"
  using assms(1)
proof (induct cfg \<equiv> "(c,s)" arbitrary: c s rule: terminFrom.induct)
  case (1 c_inner s_inner)
  then show ?case 
    using assms(2) by blast
qed



context Step
begin


lemma terminFrom_env_step:
  assumes "terminFrom (fstep_rel R) (c, s)"
  assumes "R^** s s'"
  shows "terminFrom (fstep_rel R) (c, s')"
proof (rule terminFrom.intros)
  fix cfg'
  assume "fstep_rel R (c, s') cfg'"
  then obtain u where "(lift R)\<^sup>*\<^sup>* (c, s') u" and "small_step u cfg'"
    unfolding fstep_rel_def OO_def by auto
  
  have "(lift R)\<^sup>*\<^sup>* (c, s) (c, s')"
    using \<open>R\<^sup>*\<^sup>* s s'\<close> by (simp add: rel_incl_lift_rtranclp)
  then have "(lift R)\<^sup>*\<^sup>* (c, s) u" 
    using \<open>(lift R)\<^sup>*\<^sup>* (c, s') u\<close> by (metis rtranclp_trans)
    
  then have "fstep_rel R (c, s) cfg'" 
    unfolding fstep_rel_def OO_def using \<open>small_step u cfg'\<close> by blast
    
  then show "terminFrom (fstep_rel R) cfg'"
    using assms(1) by (meson terminFrom.cases)
qed

(* --- Helper Lemmas for the Flattening --- *)
lemma step_rel_refl: 
  assumes "R s s" 
  shows "step_rel R (c, s) (c, s)"
  using step_rel.R_Step assms by blast

lemma lift_step_rel:
  assumes "lift R x y"
  shows "step_rel R x y"
proof -
  obtain c s where "x = (c,s)" by (cases x)
  obtain c' s' where "y = (c',s')" by (cases y)
  from assms have "c' = c \<and> R s s'" unfolding lift_def \<open>x = (c,s)\<close> \<open>y = (c',s')\<close> by auto
  then show ?thesis using \<open>x = (c,s)\<close> \<open>y = (c',s')\<close> step_rel.R_Step by auto
qed

lemma step_rel_not_small_lift:
  assumes "step_rel R x y" and "\<not> small_step x y"
  shows "lift R x y"
  using assms proof (cases rule: step_rel.cases)
  case (R_Step s s' c)
  then show ?thesis unfolding lift_def by auto
next
  case (S_Step c s c' s')
  with \<open>\<not> small_step x y\<close> show ?thesis by auto
qed

(* Unrolls a single fair step into a finite sequence of step_rel steps *)
lemma fstep_has_fseq:
  assumes "fstep_rel R x y"
  shows "\<exists>N f. f 0 = x \<and> f N = y \<and> N > 0 \<and>
               (\<forall>i<N. step_rel R (f i) (f (Suc i))) \<and>
               (small_step (f (N - 1)) (f N))"
proof -
  from assms obtain u where 1: "(lift R)\<^sup>*\<^sup>* x u" and 2: "small_step u y"
    unfolding fstep_rel_def OO_def by auto
  
  from 1 obtain n1 as1 where as1: "as1 0 = x" "as1 n1 = u" "\<forall>i<n1. lift R (as1 i) (as1 (Suc i))"
    using rtranclp_chain by metis
    
  \<comment> \<open>Construct sequence: [as1 0, ..., as1 n1, y]\<close>
    
  define N where "N = Suc n1"
  define f where "f = (\<lambda>k. if k \<le> n1 then as1 k else y)"
  
  have f_0: "f 0 = x" using as1 f_def by simp
  have f_N: "f N = y" using f_def N_def by simp
  have N_pos: "N > 0" by (simp add: N_def)
  
  have step_all: "\<forall>i<N. step_rel R (f i) (f (Suc i))"
  proof (intro allI impI)
    fix i assume "i < N"
    show "step_rel R (f i) (f (Suc i))"
    proof (cases "i < n1")
      case True
      then have "f i = as1 i" and "f (Suc i) = as1 (Suc i)" unfolding f_def by auto
      then show ?thesis using as1 True lift_step_rel by auto
    next
      case False
      then have "i = n1" using \<open>i < N\<close> N_def by auto
      then have "f i = u" and "f (Suc i) = y" using as1 f_def N_def by auto
      then show ?thesis using 2 step_rel.S_Step by (metis old.prod.exhaust)
    qed
  qed
  
  have small: "small_step (f (N - 1)) (f N)"
    using 2 unfolding N_def f_def by (simp add: as1(2))
    
  show ?thesis using f_0 f_N N_pos step_all small by blast
qed


(*Auxillary functions for the step process*)
fun ch_step :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "ch_step N 0 = (0,0)"
| "ch_step N (Suc k) =
     (let (i,j) = ch_step N k in
      if Suc j < N i then (i, Suc j)
      else (Suc i, 0))"

fun start_idx :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "start_idx N 0 = 0" |
  "start_idx N (Suc i) = start_idx N i + N i"

fun forwardSS :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "forwardSS next_ss 0 = 0" |
  "forwardSS next_ss (Suc n) = Suc (next_ss (forwardSS next_ss n))"

(* --- Main Equivalence Theorem --- *)

lemma fstep_rel_iff_fair_step_rel: 
"(\<exists>ch. ch 0 = cfg \<and> (\<forall>i. fstep_rel R (ch i) (ch (Suc i))))
 \<longleftrightarrow>
 (\<exists>ch'. ch' 0 = cfg \<and> (\<forall>i. step_rel R (ch' i) (ch' (Suc i))) \<and> (\<forall>i. \<exists>j \<ge> i. small_step (ch' j) (ch' (Suc j))))"
proof
  \<comment> \<open>Direction 1: Chunked to Flattened\<close>
  assume "\<exists>ch. ch 0 = cfg \<and> (\<forall>i. fstep_rel R (ch i) (ch (Suc i)))"
  then obtain ch where ch_0: "ch 0 = cfg" and ch_fstep: "\<forall>i. fstep_rel R (ch i) (ch (Suc i))" by blast
  
  define Prop where "Prop = (\<lambda>i N f. f 0 = ch i \<and> f N = ch (Suc i) \<and> N > 0 
                          \<and> (\<forall>k < N - 1. step_rel R (f k) (f (Suc k))) \<and> small_step (f (N - 1)) (f N))"
  
  have "\<forall>i. \<exists>N f. Prop i N f" unfolding Prop_def using ch_fstep fstep_has_fseq 
    by (smt (verit, del_insts) diff_right_commute not_gr_zero zero_diff zero_less_diff)
  then have "\<forall>i. \<exists>f. Prop i (SOME N. \<exists>f. Prop i N f) f" by (metis (full_types))
  then have ex_f: "\<forall>i. Prop i (SOME N. \<exists>f. Prop i N f) (SOME f. Prop i (SOME N. \<exists>f. Prop i N f) f)" by (metis someI_ex)

  define N where "N = (\<lambda>i. SOME N. \<exists>f. Prop i N f)"
  define f_seq where "f_seq = (\<lambda>i. SOME f. Prop i (N i) f)"

  have N_f_prop: "Prop i (N i) (f_seq i)" for i using ex_f unfolding N_def f_seq_def by blast

  (*Recursive state machine to flatten the sequences*)
  let ?ch_step = "ch_step N"

  define ch' where "ch' = (\<lambda>k. let (i, j) = ?ch_step k in f_seq i j)"

  have ch_step_snd_bound: "snd (?ch_step k) < N (fst (?ch_step k))" for k
  proof (induct k)
    case 0 then show ?case using N_f_prop[of 0] unfolding Prop_def by simp
  next
    case (Suc k)
    obtain i j where eq: "?ch_step k = (i, j)" by (cases "?ch_step k", auto)
    show ?case
    proof (cases "Suc j < N i")
      case True then show ?thesis using eq by (simp add: Let_def split_beta)
    next
      case False then show ?thesis using eq N_f_prop[of "Suc i"] unfolding Prop_def by (simp add: Let_def split_beta)
    qed
  qed

  have ch'_step_rel: "step_rel R (ch' k) (ch' (Suc k))" for k
  proof -
    obtain i j where eq: "?ch_step k = (i, j)" by (cases "?ch_step k", auto)
    have j_less: "j < N i" using ch_step_snd_bound[of k] eq by simp
    show ?thesis
    proof (cases "Suc j < N i")
      case True
      then show ?thesis unfolding ch'_def using eq N_f_prop[of i] j_less unfolding Prop_def by (auto simp add: Let_def split_beta)
    next
      case False
      with j_less have j:"Suc j = N i" by simp
      have "ch' (Suc k) = f_seq (Suc i) 0" unfolding ch'_def using eq False by (simp add: Let_def split_beta)
      also have "... = ch (Suc i)" using N_f_prop[of "Suc i"] unfolding Prop_def by simp
      also have "... = f_seq i (N i)" using N_f_prop[of i] unfolding Prop_def by simp
      also have "... = f_seq i (Suc j)" using \<open>Suc j = N i\<close> by simp
      finally have "ch' (Suc k) = f_seq i (Suc j)" .
      moreover have "ch' k = f_seq i j" unfolding ch'_def using eq by (simp add: Let_def split_beta)

      have small: "small_step (f_seq i (N i - 1)) (f_seq i (N i))" 
        using N_f_prop[of i] unfolding Prop_def by blast

      have ch_k: "ch' k = f_seq i (N i - 1)" 
        using \<open>ch' k = f_seq i j\<close> j by (metis diff_Suc_1)
      have ch_suc_k: "ch' (Suc k) = f_seq i (N i)" 
        using \<open>ch' (Suc k) = f_seq i (Suc j)\<close> j by simp

      show ?thesis 
        unfolding ch_k ch_suc_k 
        using step_rel.S_Step small 
        by (metis surj_pair) 
    qed
  qed
  let ?start_idx = "start_idx N"

  have ch_step_start: "j < N i \<Longrightarrow> ?ch_step (?start_idx i + j) = (i, j)" for i j
  proof (induct i arbitrary: j)
    case 0
    show ?case using 0
    proof (induct j)
      case 0 then show ?case by simp
    next
      case (Suc j)
      (*Explicitly weaken the bound to use the IH*)
      have "j < N 0" using Suc.prems by simp
      then have "?ch_step j = (0, j)" using Suc.hyps by auto
      then show ?case using Suc.prems by (simp add: Let_def split_beta)
    qed
  next
    case (Suc i)
    (*Prove the base case where we wrap around to (Suc i, 0)*)
    have Ni_pos: "N i > 0" using N_f_prop[of i] unfolding Prop_def by blast
    have "N i - 1 < N i" using Ni_pos by simp
    then have prev: "?ch_step (?start_idx i + (N i - 1)) = (i, N i - 1)"
      using Suc.hyps by blast
      
    have "?start_idx (Suc i) = Suc (?start_idx i + (N i - 1))"
      using Ni_pos by simp
    then have "?ch_step (?start_idx (Suc i)) = ?ch_step (Suc (?start_idx i + (N i - 1)))"
      by simp
    also have "... = (let (i', j') = ?ch_step (?start_idx i + (N i - 1)) in if Suc j' < N i' then (i', Suc j') else (Suc i', 0))"
      by simp
    also have "... = (Suc i, 0)"
      unfolding prev Let_def split_beta using Ni_pos by simp
    finally have base: "?ch_step (?start_idx (Suc i)) = (Suc i, 0)" .

    (*induction over j for the current chunk*)
    show ?case using \<open>j < N (Suc i)\<close>
    proof (induct j)
      case 0 then show ?case using base by simp
    next
      case (Suc j)
      have "j < N (Suc i)" using Suc.prems by simp
      then have "?ch_step (?start_idx (Suc i) + j) = (Suc i, j)" using Suc.hyps by blast
      then show ?case using Suc.prems by (simp add: Let_def split_beta)
    qed
  qed

  have k_eq: "k = ?start_idx (fst (?ch_step k)) + snd (?ch_step k)" for k
  proof (induct k)
    case 0 show ?case by simp
  next
    case (Suc k)
    obtain i j where eq: "?ch_step k = (i, j)" by (cases "?ch_step k", auto)
    show ?case using Suc.hyps eq N_f_prop[of i] ch_step_snd_bound[of k] unfolding Prop_def 
      by (cases "Suc j < N i") (auto simp add: Let_def split_beta)
  qed

  have ch'_fair: "\<forall>k. \<exists>k'\<ge>k. small_step (ch' k') (ch' (Suc k'))"
  proof (intro allI)
    fix k
    obtain i j where eq: "?ch_step k = (i, j)" by (cases "?ch_step k", auto)
    have j_less: "j < N i" using ch_step_snd_bound[of k] eq by simp
    obtain ss where ss_less: "ss < N i" and ss_step: "small_step (f_seq i ss) (f_seq i (Suc ss))" 
      using N_f_prop[of i] unfolding Prop_def by (metis Suc_diff_1 diff_less less_one)

    show "\<exists>k'\<ge>k. small_step (ch' k') (ch' (Suc k'))"
    proof (cases "ss \<ge> j")
      case True
      define k' where "k' = ?start_idx i + ss"
      have "k' \<ge> k" using k_eq[of k] eq True k'_def by simp
      have ch_step_k': "?ch_step k' = (i, ss)" using ch_step_start ss_less k'_def by simp
      
      have "ch' k' = f_seq i ss" unfolding ch'_def ch_step_k' by (simp add: Let_def split_beta)
      moreover have "ch' (Suc k') = f_seq i (Suc ss)"
      proof (cases "Suc ss < N i")
        case True then show ?thesis unfolding ch'_def using ch_step_k' by (simp add: Let_def split_beta)
      next
        case False
        with ss_less have "Suc ss = N i" by simp
        then show ?thesis unfolding ch'_def using ch_step_k' N_f_prop[of i] N_f_prop[of "Suc i"] unfolding Prop_def by (auto simp add: Let_def split_beta)
      qed
      ultimately show ?thesis using ss_step \<open>k' \<ge> k\<close> by auto
    next
      case False
      obtain ss_n where ss_n_less: "ss_n < N (Suc i)" and ss_n_step: "small_step (f_seq (Suc i) ss_n) (f_seq (Suc i) (Suc ss_n))" 
        using N_f_prop[of "Suc i"] unfolding Prop_def by (metis Suc_pred' diff_less less_one)
      define k' where "k' = ?start_idx (Suc i) + ss_n"
      have "k' \<ge> k" using k_eq[of k] eq j_less k'_def by simp
      have ch_step_k': "?ch_step k' = (Suc i, ss_n)" using ch_step_start ss_n_less k'_def by blast
      
      have "ch' k' = f_seq (Suc i) ss_n" unfolding ch'_def ch_step_k' by (simp add: Let_def split_beta)
      moreover have "ch' (Suc k') = f_seq (Suc i) (Suc ss_n)"
      proof (cases "Suc ss_n < N (Suc i)")
        case True then show ?thesis unfolding ch'_def using ch_step_k' by (simp add: Let_def split_beta)
      next
        case False
        with ss_n_less have "Suc ss_n = N (Suc i)" by simp
        then show ?thesis unfolding ch'_def using ch_step_k' N_f_prop[of "Suc i"] N_f_prop[of "Suc (Suc i)"] unfolding Prop_def by (auto simp add: Let_def split_beta)
      qed
      ultimately show ?thesis using ss_n_step \<open>k' \<ge> k\<close> by auto
    qed
  qed

  have "ch' 0 = cfg" unfolding ch'_def using N_f_prop[of 0] ch_0 unfolding Prop_def by (simp add: Let_def split_beta)
  then show "\<exists>ch'. ch' 0 = cfg \<and> (\<forall>i. step_rel R (ch' i) (ch' (Suc i))) \<and> (\<forall>i. \<exists>j\<ge>i. small_step (ch' j) (ch' (Suc j)))"
    using ch'_step_rel ch'_fair by blast

next
  (*Flattened to Chunked*)
  assume "\<exists>ch'. ch' 0 = cfg \<and> (\<forall>i. step_rel R (ch' i) (ch' (Suc i))) \<and> (\<forall>i. \<exists>j\<ge>i. small_step (ch' j) (ch' (Suc j)))"
  then obtain ch' where ch'_0: "ch' 0 = cfg" and ch'_step: "\<forall>i. step_rel R (ch' i) (ch' (Suc i))" and ch'_fair: "\<forall>i. \<exists>j\<ge>i. small_step (ch' j) (ch' (Suc j))" by blast

  define next_ss where "next_ss = (\<lambda>i. LEAST j. j \<ge> i \<and> small_step (ch' j) (ch' (Suc j)))"
  have next_ss_prop: "next_ss i \<ge> i \<and> small_step (ch' (next_ss i)) (ch' (Suc (next_ss i)))" for i
    unfolding next_ss_def using LeastI_ex[OF ch'_fair[rule_format, of i]] .

  have next_ss_least: "k \<ge> i \<Longrightarrow> k < next_ss i \<Longrightarrow> \<not> small_step (ch' k) (ch' (Suc k))" for i k
    unfolding next_ss_def by (metis (mono_tags, lifting) Least_le not_le)

  let ?f = "forwardSS next_ss"

  define ch where "ch = (\<lambda>n. ch' (?f n))"

  have "fstep_rel R (ch n) (ch (Suc n))" for n
  proof -
    have "(lift R)\<^sup>*\<^sup>* (ch' (?f n)) (ch' (next_ss (?f n)))"
    proof (rule chain_rtranclp[of "\<lambda>k. ch' (?f n + k)" _ "next_ss (?f n) - ?f n"])
      show "ch' (?f n + 0) = ch' (?f n)" by simp
      show "ch' (?f n + (next_ss (?f n) - ?f n)) = ch' (next_ss (?f n))" using next_ss_prop[of "?f n"] by simp
      have f_Suc_eq:"\<And>i. ?f n + Suc i = Suc (?f n + i)" by simp
      show "\<forall>i<next_ss (?f n) - ?f n. lift R (ch' (?f n + i)) (ch'  (?f n + (Suc i)))"
      proof (unfold f_Suc_eq, intro allI impI)
        fix i assume "i < next_ss (?f n) - ?f n"
        let ?k = "?f n + i"
        have "?k \<ge> ?f n" and "?k < next_ss (?f n)" using \<open>i < next_ss (?f n) - ?f n\<close> by auto
        then have "\<not> small_step (ch' ?k) (ch' (Suc ?k))" using next_ss_least[of "?f n" ?k] by simp
        then show "lift R (ch' ?k) (ch' (Suc ?k))" using step_rel_not_small_lift ch'_step by blast
      qed
    qed
    moreover have "small_step (ch' (next_ss (?f n))) (ch' (Suc (next_ss (?f n))))" using next_ss_prop by blast
    moreover have "(lift R)\<^sup>*\<^sup>* (ch' (Suc (next_ss (?f n)))) (ch' (Suc (next_ss (?f n))))" by simp
    ultimately show ?thesis unfolding fstep_rel_def OO_def ch_def by fastforce
  qed

  then show "\<exists>ch. ch 0 = cfg \<and> (\<forall>i. fstep_rel R (ch i) (ch (Suc i)))" using ch'_0 ch_def by (metis Step.forwardSS.simps(1))
qed


end

definition "stableWithDescent R P ord \<equiv> \<forall>n s s'. P n s \<and> R s s' \<longrightarrow> (\<exists>m. (m,n) \<in> ord \<and> P m s')" 

lemma rtranclp_Id: "(=)^** = (=)" 
  by (metis conversep_eq eq_OO leq_conversepI order_antisym_conv reflclp_tranclp rtranclp_least sup.coboundedI2)
end