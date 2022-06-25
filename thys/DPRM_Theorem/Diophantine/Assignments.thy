subsection \<open>Variable Assignments\<close>

text \<open>The following theory defines manipulations of variable assignments and proves elementary facts about 
      these. Such preliminary results will later be necesary to e.g. prove that conjunction is 
      diophantine.\<close>

theory Assignments
  imports Parametric_Polynomials
begin

definition shift :: "nat list \<Rightarrow> nat \<Rightarrow> assignment" where
  "shift l a \<equiv> \<lambda>i. l ! (i + a)"

definition push :: "assignment \<Rightarrow> nat \<Rightarrow> assignment" where
  "push a n i = (if i = 0 then n else a (i-1))"

definition push_list :: "assignment \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "push_list a ns i = (if i < length ns then (ns!i) else a (i - length ns))"

lemma push0: "push a n 0 = n"
  by (auto simp: push_def)

lemma push_list_empty: "push_list a [] = a"
  unfolding push_list_def by auto

lemma push_list_singleton: "push_list a [n] = push a n"
  unfolding push_list_def push_def by auto

lemma push_list_eval: "i < length ns \<Longrightarrow> push_list a ns i = ns!i"
  unfolding push_list_def by auto

lemma push_list1: "push (push_list a ns) n = push_list a (n # ns)"
  unfolding push_def push_list_def by fastforce

lemma push_list2_aux: "(push_list (push a n) ns) i = push_list a (ns @ [n]) i"
  unfolding push_def push_list_def by (auto simp: nth_append)

lemma push_list2: "(push_list (push a n) ns) = push_list a (ns @ [n])"
  unfolding push_list2_aux by auto

fun pull_param :: "ppolynomial \<Rightarrow> ppolynomial \<Rightarrow> ppolynomial" where
  "pull_param (ppolynomial.Param 0) repl    = repl" |
  "pull_param (ppolynomial.Param (Suc n)) _ = (ppolynomial.Param n)" |
  "pull_param (D1 \<^bold>+ D2) repl  = (pull_param D1 repl) \<^bold>+ (pull_param D2 repl)" |
  "pull_param (D1 \<^bold>- D2) repl  = (pull_param D1 repl) \<^bold>- (pull_param D2 repl)" |
  "pull_param (D1 \<^bold>* D2) repl  = (pull_param D1 repl) \<^bold>* (pull_param D2 repl)" |
  "pull_param P repl = P"

(* FROM PREVIOUS FILE *)

fun var_set :: "ppolynomial \<Rightarrow> nat set" where
  "var_set (ppolynomial.Const c)   = {}" |
  "var_set (ppolynomial.Param x)   = {}" |
  "var_set (ppolynomial.Var x)     = {x}" |
  "var_set (D1 \<^bold>+ D2) = var_set D1 \<union> var_set D2" |
  "var_set (D1 \<^bold>- D2) = var_set D1 \<union> var_set D2" |
  "var_set (D1 \<^bold>* D2) = var_set D1 \<union> var_set D2"

definition disjoint_var :: "ppolynomial \<Rightarrow> ppolynomial \<Rightarrow> bool" where
  "disjoint_var P Q = (var_set P \<inter> var_set Q = {})"

named_theorems disjoint_vars

lemma disjoint_var_sym: "disjoint_var P Q = disjoint_var Q P"
  unfolding disjoint_var_def by auto

lemma disjoint_var_sum[disjoint_vars]: "disjoint_var (P1 \<^bold>+ P2) Q = (disjoint_var P1 Q \<and> disjoint_var P2 Q)"
  unfolding disjoint_var_def by auto

lemma disjoint_var_diff[disjoint_vars]: "disjoint_var (P1 \<^bold>- P2) Q = (disjoint_var P1 Q \<and> disjoint_var P2 Q)"
  unfolding disjoint_var_def by auto

lemma disjoint_var_prod[disjoint_vars]: "disjoint_var (P1 \<^bold>* P2) Q = (disjoint_var P1 Q \<and> disjoint_var P2 Q)"
   unfolding disjoint_var_def by auto

lemma aux_var_set:
  assumes "\<forall>i \<in> var_set P. x i = y i"
  shows "ppeval P a x = ppeval P a y"
  using assms by (induction P, auto)

text \<open>First prove that disjoint variable sets allow the unification into one variable assignment\<close>
definition zip_assignments :: "ppolynomial \<Rightarrow> ppolynomial \<Rightarrow> assignment \<Rightarrow> assignment \<Rightarrow> assignment"
  where "zip_assignments P Q v w i = (if i \<in> var_set P then v i else w i)"

lemma help_eval_zip_assignments1:
  shows "ppeval P1 a (\<lambda>i. if i \<in> var_set P1 \<union> var_set P2 then v i else w i)
       = ppeval P1 a (\<lambda>i. if i \<in> var_set P1 then v i else w i)"
  using aux_var_set by auto

lemma help_eval_zip_assignments2:
  shows "ppeval P2 a (\<lambda>i. if i \<in> var_set P1 \<union> var_set P2 then v i else w i)
       = ppeval P2 a (\<lambda>i. if i \<in> var_set P2 then v i else w i)"
  using aux_var_set by auto

lemma eval_zip_assignments1:
  fixes v w
  assumes "disjoint_var P Q"
  defines "x \<equiv> zip_assignments P Q v w"
  shows "ppeval P a v = ppeval P a x"
  using assms
  apply (induction P arbitrary: x)
  unfolding x_def zip_assignments_def
  using help_eval_zip_assignments1 help_eval_zip_assignments2
  by (auto simp add: disjoint_vars)

lemma eval_zip_assignments2:
  fixes v w
  assumes "disjoint_var P Q"
  defines "x \<equiv> zip_assignments P Q v w"
  shows "ppeval Q a w = ppeval Q a x"
  using assms
  apply (induction Q arbitrary: P x)
  unfolding x_def zip_assignments_def
  using disjoint_var_sym disjoint_vars
  by (auto simp: disjoint_var_def) (smt (z3) inf_commute)+

lemma zip_assignments_correct:
  assumes "ppeval P1 a v = ppeval P2 a v" and "ppeval Q1 a w = ppeval Q2 a w"
      and "disjoint_var (P1 \<^bold>+ P2) (Q1 \<^bold>+ Q2)"
  defines "x \<equiv> zip_assignments (P1 \<^bold>+ P2) (Q1 \<^bold>+ Q2) v w"
  shows "ppeval P1 a x = ppeval P2 a x" and "ppeval Q1 a x = ppeval Q2 a x"
proof -
  from assms(3) have "disjoint_var P1 (Q1 \<^bold>+ Q2)"
    by (auto simp: disjoint_var_sum)
  moreover have "ppeval P1 a x = ppeval P1 a (zip_assignments P1 (Q1 \<^bold>+ Q2) v w)"
    unfolding x_def zip_assignments_def using help_eval_zip_assignments1 by auto
  ultimately have p1: "ppeval P1 a x = ppeval P1 a v"
    using eval_zip_assignments1[of "P1"] by auto

  from assms(3) have "disjoint_var P2 (Q1 \<^bold>+ Q2)"
    by (auto simp: disjoint_var_sum)
  moreover have "ppeval P2 a x = ppeval P2 a (zip_assignments P2 (Q1 \<^bold>+ Q2) v w)"
    unfolding x_def zip_assignments_def using help_eval_zip_assignments2 by auto
  ultimately have p2: "ppeval P2 a x = ppeval P2 a v"
    using eval_zip_assignments1[of "P2"] by auto
  
  from p1 p2 show "ppeval P1 a x = ppeval P2 a x"
    using assms(1) by auto
next
  have "disjoint_var (P1 \<^bold>+ P2) Q1"
    using assms(3) disjoint_var_sum disjoint_var_sym by auto
  moreover have "ppeval Q1 a x = ppeval Q1 a (zip_assignments (P1 \<^bold>+ P2) Q1 v w)"
    unfolding x_def zip_assignments_def using help_eval_zip_assignments1 by auto
  ultimately have q1: "ppeval Q1 a x = ppeval Q1 a w"
    using eval_zip_assignments2[of _ "Q1"] by auto

  from assms(3) have "disjoint_var (P1 \<^bold>+ P2) Q2"
    using assms(3) disjoint_var_sum disjoint_var_sym by auto
  moreover have "ppeval Q2 a x = ppeval Q2 a (zip_assignments (P1 \<^bold>+ P2) Q2 v w)"
    unfolding x_def zip_assignments_def using help_eval_zip_assignments2 by auto
  ultimately have q2: "ppeval Q2 a x = ppeval Q2 a w"
    using eval_zip_assignments2[of _ "Q2"] by auto
  
  from q1 q2 show "ppeval Q1 a x = ppeval Q2 a x"
    using assms(2) by auto
qed

lemma disjoint_var_unifies:
  assumes "\<exists>v1. ppeval P1 a v1 = ppeval P2 a v1" and "\<exists>v2. ppeval Q1 a v2 = ppeval Q2 a v2"
      and "disjoint_var (P1 \<^bold>+ P2) (Q1 \<^bold>+ Q2)"
    shows "\<exists>v. ppeval P1 a v = ppeval P2 a v \<and> ppeval Q1 a v = ppeval Q2 a v"
  using assms zip_assignments_correct by (auto) metis

(* Next prove that one can always find a polynomial with disjoint variables given some other polys*)
text \<open>A function to manipulate variables in ppolynomials\<close>
fun push_var :: "ppolynomial \<Rightarrow> nat \<Rightarrow> ppolynomial" where
  "push_var (ppolynomial.Var x)     n = ppolynomial.Var (x + n)" |
  "push_var (D1 \<^bold>+ D2) n = push_var D1 n \<^bold>+ push_var D2 n" |
  "push_var (D1 \<^bold>- D2) n = push_var D1 n \<^bold>- push_var D2 n" |
  "push_var (D1 \<^bold>* D2) n = push_var D1 n \<^bold>* push_var D2 n" |
  "push_var D n = D"

lemma push_var_bound: "x \<in> var_set (push_var P (Suc n)) \<Longrightarrow> x > n"
  by (induction P, auto)

definition pull_assignment :: "assignment \<Rightarrow> nat \<Rightarrow> assignment" where
  "pull_assignment v n = (\<lambda>x. v (x+n))"

lemma push_var_pull_assignment:
  shows "ppeval (push_var P n) a v = ppeval P a (pull_assignment v n)"
  by (induction P, auto simp: pull_assignment_def)

lemma max_set: "finite A \<Longrightarrow> \<forall>x\<in>A. x \<le> Max A"
  using Max_ge by blast


(* FROM PREVIOUS FILE SIMPLEDIOPHANTINE_NAT *)

fun push_param :: "polynomial \<Rightarrow> nat \<Rightarrow> polynomial" where
  "push_param (Const c)   n = Const c" |
  "push_param (Param x)   n = Param (x + n)" |
  "push_param (Sum D1 D2) n = Sum (push_param D1 n) (push_param D2 n)" |
  "push_param (NatDiff D1 D2) n = NatDiff (push_param D1 n) (push_param D2 n)" |
  "push_param (Prod D1 D2) n = Prod (push_param D1 n) (push_param D2 n)"

definition push_param_list :: "polynomial list \<Rightarrow> nat \<Rightarrow> polynomial list" where
  "push_param_list s k \<equiv> map (\<lambda>x. push_param x k) s"


lemma push_param0: "push_param P 0 = P"
  by (induction P, auto)

lemma push_push_aux: "peval (push_param P (Suc m)) (push a n) = peval (push_param P m) a"
  by (induction P, auto simp: push_def)

lemma push_push:
  shows "length ns = n \<Longrightarrow> peval (push_param P n) (push_list a ns) = peval P a"
proof (induction ns arbitrary: n)
  case Nil
  then show ?case by (auto simp: push_list_empty push_param0)
next
  case (Cons n ns)
  thus ?case
    using push_push_aux[where ?a = "push_list a ns"]
    by (auto simp add: length_Cons push_list1)
qed

lemma push_push_simp:
  shows "peval (push_param P (length ns)) (push_list a ns) = peval P a"
proof (induction ns)
  case Nil
  then show ?case by (auto simp: push_list_empty push_param0)
next
  case (Cons n ns)
  thus ?case
    using push_push_aux[where ?a = "push_list a ns"]
    by (auto simp add: length_Cons push_list1)
qed


lemma push_push1: "peval (push_param P 1) (push a k) = peval P a"
  using push_push[where ?ns = "[k]"] by (auto simp: push_list_singleton)

lemma push_push_map: "length ns = n \<Longrightarrow>
  list_eval (map (\<lambda>x. push_param x n) ls) (push_list a ns) = list_eval ls a"
  unfolding list_eval_def apply (induction ls, simp)
  apply (induction ns, auto)
  apply (metis length_map list.size(3) nth_equalityI push_push)
  by (metis length_Cons length_map map_nth push_push)

lemma push_push_map_i: "length ns = n \<Longrightarrow> i < length ls \<Longrightarrow>
  peval (map (\<lambda>x. push_param x n) ls ! i) (push_list a ns) = list_eval ls a i"
  unfolding list_eval_def by (auto simp: push_push_map push_push)

lemma push_push_map1: "i < length ls \<Longrightarrow>
  peval (map (\<lambda>x. push_param x 1) ls ! i) (push a n) = list_eval ls a i"
  unfolding list_eval_def using push_push1 by (auto)

end