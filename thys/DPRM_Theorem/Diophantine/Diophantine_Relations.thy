subsection \<open>Diophantine Relations and Predicates\<close>

theory Diophantine_Relations
  imports Assignments
begin           

datatype relation =
  NARY "nat list \<Rightarrow> bool" "polynomial list"
    | AND relation relation (infixl "[\<and>]" 35)
    | OR  relation relation (infixl "[\<or>]" 30)
    | EXIST_LIST nat relation ("[\<exists>_] _" 10)

fun eval :: "relation \<Rightarrow> assignment \<Rightarrow> bool" where
  "eval (NARY R PL) a = R (map (\<lambda>P. peval P a) PL)"
    | "eval (AND D1 D2) a = (eval D1 a \<and> eval D2 a)"
    | "eval (OR D1 D2) a = (eval D1 a \<or> eval D2 a)"
    | "eval ([\<exists>n] D) a = (\<exists>ks::nat list. n = length ks \<and> eval D (push_list a ks))"

definition is_dioph_rel :: "relation \<Rightarrow> bool" where
  "is_dioph_rel DR = (\<exists>P\<^sub>1 P\<^sub>2::ppolynomial. \<forall>a. (eval DR a) \<longleftrightarrow> (\<exists>v. ppeval P\<^sub>1 a v = ppeval P\<^sub>2 a v))"


definition UNARY :: "(nat \<Rightarrow> bool) \<Rightarrow> polynomial \<Rightarrow> relation" where
  "UNARY R P = NARY (\<lambda>l. R (l!0)) [P]"

lemma unary_eval: "eval (UNARY R P) a = R (peval P a)"
  unfolding UNARY_def by simp

definition BINARY :: "(nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> polynomial \<Rightarrow> polynomial \<Rightarrow> relation" where
  "BINARY R P\<^sub>1 P\<^sub>2 = NARY (\<lambda>l. R (l!0) (l!1)) [P\<^sub>1, P\<^sub>2]"

lemma binary_eval: "eval (BINARY R P\<^sub>1 P\<^sub>2) a = R (peval P\<^sub>1 a) (peval P\<^sub>2 a)"
  unfolding BINARY_def by simp

definition TERNARY :: "(nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool)
                        \<Rightarrow> polynomial \<Rightarrow> polynomial \<Rightarrow> polynomial \<Rightarrow> relation" where
  "TERNARY R P\<^sub>1 P\<^sub>2 P\<^sub>3 = NARY (\<lambda>l. R (l!0) (l!1) (l!2)) [P\<^sub>1, P\<^sub>2, P\<^sub>3]"

lemma ternary_eval: "eval (TERNARY R P\<^sub>1 P\<^sub>2 P\<^sub>3) a = R (peval P\<^sub>1 a) (peval P\<^sub>2 a) (peval P\<^sub>3 a)"
  unfolding TERNARY_def by simp

definition QUATERNARY :: "(nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool)
                        \<Rightarrow> polynomial \<Rightarrow> polynomial \<Rightarrow> polynomial \<Rightarrow> polynomial \<Rightarrow> relation" where
  "QUATERNARY R P\<^sub>1 P\<^sub>2 P\<^sub>3 P\<^sub>4 = NARY (\<lambda>l. R (l!0) (l!1) (l!2) (l!3)) [P\<^sub>1, P\<^sub>2, P\<^sub>3, P\<^sub>4]"

definition EXIST :: "relation \<Rightarrow> relation" ("[\<exists>] _" 10) where
  "([\<exists>] D) = ([\<exists>1] D)"

definition TRUE where "TRUE = UNARY ((=) 0) (Const 0)"

text \<open>Bounded constant all quantifier (i.e. recursive conjunction)\<close>
fun ALLC_LIST :: "nat list \<Rightarrow> (nat \<Rightarrow> relation) \<Rightarrow> relation" ("[\<forall> in _] _") where
  "[\<forall> in []] DF = TRUE" |
  "[\<forall> in (l # ls)] DF = (DF l [\<and>] [\<forall> in ls] DF)"

lemma ALLC_LIST_eval_list_all: "eval ([\<forall> in L] DF) a = list_all (\<lambda>l. eval (DF l) a) L"
  by (induction L, auto simp: TRUE_def UNARY_def)

lemma ALLC_LIST_eval:  "eval ([\<forall> in L] DF) a = (\<forall>k<length L. eval (DF (L!k)) a)"
  by (simp add: ALLC_LIST_eval_list_all list_all_length)

definition ALLC :: "nat \<Rightarrow> (nat \<Rightarrow> relation) \<Rightarrow> relation" ("[\<forall><_] _") where
  "[\<forall><n] D \<equiv> [\<forall> in [0..<n]] D"

lemma ALLC_eval: "eval ([\<forall><n] DF) a = (\<forall>k<n. eval (DF k) a)"
  unfolding ALLC_def by (simp add: ALLC_LIST_eval)

fun concat :: "'a list list \<Rightarrow> 'a list" where
  "concat [] = []" |
  "concat (l # ls) = l @ concat ls"

fun splits :: "'a list \<Rightarrow> nat list \<Rightarrow> 'a list list" where
  "splits L [] = []" |
  "splits L (n # ns) = (take n L) # (splits (drop n L) ns)"

lemma split_concat:
  "splits (map f (concat pls)) (map length pls) = map (map f) pls"
  by (induction pls, auto)

definition LARY :: "(nat list list \<Rightarrow> bool) \<Rightarrow> (polynomial list list) \<Rightarrow> relation" where
  "LARY R PLL = NARY (\<lambda>l. R (splits l (map length PLL))) (concat PLL)"

lemma LARY_eval:
  fixes PLL :: "polynomial list list"
  shows "eval (LARY R PLL) a = R (map (map (\<lambda>P. peval P a)) PLL)"
  unfolding LARY_def apply (induction PLL, simp)
  subgoal for pl pls by (induction pl, auto simp: split_concat)
  done

lemma or_dioph:
  assumes "is_dioph_rel A" and "is_dioph_rel B"
  shows "is_dioph_rel (A [\<or>] B)"
proof -
  from assms obtain PA1 PA2 where PA: "\<forall>a. (eval A a) \<longleftrightarrow> (\<exists>v. ppeval PA1 a v = ppeval PA2 a v)"
    by (auto simp: is_dioph_rel_def)
  from assms obtain PB1 PB2 where PB: "\<forall>a. (eval B a) \<longleftrightarrow> (\<exists>v. ppeval PB1 a v = ppeval PB2 a v)"
    by (auto simp: is_dioph_rel_def)

  (* OR means (A1 - A2) * (B1 - B2) = 0
     Rewrite as A1*B1 + A2*B2 = A1*B2 + A2*B1 to eliminate subtraction. *)
  show ?thesis
    unfolding is_dioph_rel_def
    apply (rule exI[of _ "PA1 \<^bold>* PB1 \<^bold>+ PA2 \<^bold>* PB2"])
    apply (rule exI[of _ "PA1 \<^bold>* PB2 \<^bold>+ PA2 \<^bold>* PB1"])
    using PA PB by (auto) (metis crossproduct_eq add.commute)+
    (* For each subgoal, a different fact is unused. The warning is due to 'metis+' being used. *)
qed

lemma exists_disjoint_vars:
  fixes Q1 Q2 :: ppolynomial
  fixes A :: relation
  assumes "is_dioph_rel A"
  shows "\<exists>P1 P2. disjoint_var (P1 \<^bold>+ P2) (Q1 \<^bold>+ Q2)
                \<and> (\<forall>a. eval A a \<longleftrightarrow> (\<exists>v. ppeval P1 a v = ppeval P2 a v))"
proof -
  obtain P1 P2 where p_defs: "\<forall>a. eval A a \<longleftrightarrow> (\<exists>v. ppeval P1 a v = ppeval P2 a v)"
    using assms is_dioph_rel_def by auto

  define n::nat where "n \<equiv> Max (var_set (Q1 \<^bold>+ Q2))"

  define P1' P2' where p'_defs: "P1' \<equiv> push_var P1 (Suc n)" "P2' \<equiv> push_var P2 (Suc n)" 

  have "disjoint_var (P1' \<^bold>+ P2') (Q1 \<^bold>+ Q2)"
  proof -
    have "finite (var_set (Q1 \<^bold>+ Q2))"
      apply (induction Q1, auto)
      by (induction Q2, auto)+

    hence "\<forall>x \<in> var_set (Q1 \<^bold>+ Q2). x \<le> n"
      unfolding n_def using Max.coboundedI by blast

    moreover have "\<forall>x \<in> var_set (P1' \<^bold>+ P2'). x > n"
      unfolding p'_defs using push_var_bound by auto

    ultimately show ?thesis
      unfolding disjoint_var_def by fastforce
  qed

  moreover have "\<forall>a. eval A a \<longleftrightarrow> (\<exists>v. ppeval P1' a v = ppeval P2' a v)"
    unfolding p'_defs apply (auto simp add: p_defs push_var_pull_assignment pull_assignment_def)
    subgoal for a v by (rule exI[of _ "\<lambda>i. v (i - Suc n)"]) auto
    done

  ultimately show ?thesis
    by auto
qed

(* Combine the two results to show that AND has a diophantine representation *)
lemma and_dioph:
  assumes "is_dioph_rel A" and "is_dioph_rel B"
  shows "is_dioph_rel (A [\<and>] B)"
proof -
  from assms(1) obtain PA1 PA2 where PA: "\<forall>a. (eval A a) \<longleftrightarrow> (\<exists>v. ppeval PA1 a v = ppeval PA2 a v)"
    by (auto simp: is_dioph_rel_def)
  from assms(2) obtain PB1 PB2 where disj: "disjoint_var (PB1 \<^bold>+ PB2) (PA1 \<^bold>+ PA2)"
                                   and PB: "(\<forall>a. eval B a \<longleftrightarrow> (\<exists>v. ppeval PB1 a v = ppeval PB2 a v))"
    using exists_disjoint_vars[of B] by blast

  from disjoint_var_unifies have unified: "\<forall>a. (eval (A [\<and>] B) a)
                        \<longleftrightarrow> (\<exists>v. ppeval PA1 a v = ppeval PA2 a v \<and> ppeval PB1 a v = ppeval PB2 a v)"
    using PA PB disj disjoint_var_sym by simp blast

  (* AND means (A1 - A2)^2 + (B1 - B2)^2 = 0
     Rewrite as A1^2 + A2^2 + B1^2 + B2^2 = 2*A1*A2 + 2*B1*B2 to eliminate subtraction. *)
  have h0: "p1 = p2 \<longleftrightarrow> p1^2 + p2^2 = 2*p1*p2" for p1 p2 :: nat
    apply (auto simp: algebra_simps power2_eq_square)
    using crossproduct_eq by fastforce

  have "p1 = p2 \<and> q1 = q2 \<longleftrightarrow> p1^2 + p2^2 + q1^2 + q2^2 = 2*p1*p2 + 2*q1*q2" for p1 p2 q1 q2 :: nat
  proof (rule)
    assume "p1 = p2 \<and> q1 = q2"
    thus "p1\<^sup>2 + p2\<^sup>2 + q1\<^sup>2 + q2\<^sup>2 = 2 * p1 * p2 + 2 * q1 * q2"
      by (auto simp: algebra_simps power2_eq_square)
  next
    assume "p1\<^sup>2 + p2\<^sup>2 + q1\<^sup>2 + q2\<^sup>2 = 2 * p1 * p2 + 2 * q1 * q2"
    hence "(int p1)\<^sup>2 + (int p2)\<^sup>2 + (int q1)\<^sup>2 + (int q2)\<^sup>2 - 2 * int p1 * int p2 - 2 * int q1 * int q2 = 0"
      by (auto) (smt (verit, best) mult_2 of_nat_add of_nat_mult power2_eq_square)
    hence "(int p1 - int p2)^2 + (int q1 - int q2)^2 = 0"
      by (simp add: power2_diff)
    hence "int p1 = int p2" and "int q1 = int q2"
      by (simp add: sum_power2_eq_zero_iff)+
    thus "p1 = p2 \<and> q1 = q2"
      by auto
  qed

  thus ?thesis
    apply (simp only: is_dioph_rel_def)
    apply (rule exI[of _ "PA1\<^bold>^\<^bold>2 \<^bold>+ PA2\<^bold>^\<^bold>2 \<^bold>+ PB1\<^bold>^\<^bold>2 \<^bold>+ PB2\<^bold>^\<^bold>2"])
    apply (rule exI[of _ "(ppolynomial.Const 2) \<^bold>* PA1 \<^bold>* PA2 \<^bold>+ (ppolynomial.Const 2) \<^bold>* PB1 \<^bold>* PB2"])
    apply (subst unified)
    by (simp add: Sq_pp_def power2_eq_square)
qed


(* Some basic relations are diophantine *)
definition eq (infix "[=]" 50) where "eq Q R \<equiv> BINARY (=) Q R"
definition lt (infix "[<]" 50) where "lt Q R \<equiv> BINARY (<) Q R"
definition le (infix "[\<le>]" 50) where "le Q R \<equiv> Q [<] R [\<or>] Q [=] R"
definition gt (infix "[>]" 50) where "gt Q R \<equiv> R [<] Q"
definition ge (infix "[\<ge>]" 50) where "ge Q R \<equiv> Q [>] R [\<or>] Q [=] R"

named_theorems defs
lemmas [defs] = zero_p_def one_p_def eq_def lt_def le_def gt_def ge_def LARY_eval
                UNARY_def BINARY_def TERNARY_def QUATERNARY_def ALLC_LIST_eval ALLC_eval

named_theorems dioph
lemmas [dioph] = or_dioph and_dioph

lemma true_dioph[dioph]: "is_dioph_rel TRUE" 
  unfolding TRUE_def UNARY_def is_dioph_rel_def by auto

lemma eq_dioph[dioph]: "is_dioph_rel (Q [=] R)"
  unfolding is_dioph_rel_def
  apply (rule exI[of _ "convert Q"])
  apply (rule exI[of _ "convert R"])
  using convert_eval BINARY_def by (auto simp: eq_def)

lemma lt_dioph[dioph]: "is_dioph_rel (Q [<] R)"
  unfolding is_dioph_rel_def
  apply (rule exI[of _ "(ppolynomial.Const 1) \<^bold>+ (ppolynomial.Var 0) \<^bold>+ convert Q"])
  apply (rule exI[of _ "convert R"])
  using convert_eval BINARY_def apply (auto simp: lt_def)
  by (metis add.commute add.right_neutral less_natE)

definition zero ("[0=] _" [60] 60) where[defs]: "zero Q \<equiv> \<^bold>0 [=] Q"
lemma zero_dioph[dioph]: "is_dioph_rel ([0=] Q)"
  unfolding zero_def by (auto simp: eq_dioph)

lemma gt_dioph[dioph]: "is_dioph_rel (Q [>] R)"
  unfolding gt_def by (auto simp: lt_dioph)

lemma le_dioph[dioph]: "is_dioph_rel (Q [\<le>] R)"
  unfolding le_def by (auto simp: lt_dioph eq_dioph or_dioph)

lemma ge_dioph[dioph]: "is_dioph_rel (Q [\<ge>] R)"
  unfolding ge_def by (auto simp: gt_dioph eq_dioph or_dioph)

text \<open>Bounded Constant All Quantifier, dioph rules\<close>

lemma ALLC_LIST_dioph[dioph]: "list_all (is_dioph_rel \<circ> DF) L \<Longrightarrow> is_dioph_rel ([\<forall> in L] DF)"
  by (induction L, auto simp add: dioph)

lemma ALLC_dioph[dioph]: "\<forall>i<n. is_dioph_rel (DF i) \<Longrightarrow> is_dioph_rel ([\<forall><n] DF)"
  unfolding ALLC_def using ALLC_LIST_dioph[of DF "[0..<n]"] by (auto simp: list_all_length)

end