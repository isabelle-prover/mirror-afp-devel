theory Variables
  imports Degree "HOL-Eisbach.Eisbach"
begin

subsection \<open>Variables\<close>

lemma Var_neq_zero: "(Var v :: 'a::zero_neq_one mpoly) \<noteq> 0"
proof -
  have "lookup (mapping_of (Var v :: 'a mpoly)) (Poly_Mapping.single v 1) \<noteq> 0"
    unfolding Var.rep_eq Var\<^sub>0_def by simp
  thus ?thesis
    by (metis lookup_zero zero_mpoly.rep_eq)
qed

lemma in_vars_non_zero_degree: "v \<in> vars P \<longleftrightarrow> degree P v \<noteq> 0"
proof (rule iffI)
  have "v \<notin> vars P \<Longrightarrow> degree P v = 0"
  proof -
    assume "v \<notin> vars P"
    hence "(\<lambda>m. lookup m v) ` keys (mapping_of P) \<subseteq> {0}"
      unfolding vars_def image_def
      using in_keys_iff
      by fastforce
    hence 0: "insert 0 ((\<lambda>m. lookup m v) ` keys (mapping_of P)) = {0}"
      by blast
    have "Max (insert 0 ((\<lambda>m. lookup m v) ` keys (mapping_of P))) = 0"
      unfolding 0 by simp
    thus ?thesis unfolding degree.rep_eq .
  qed
  thus "degree P v \<noteq> 0 \<Longrightarrow> v \<in> vars P" by auto
next
  assume "v \<in> vars P"
  thus "degree P v \<noteq> 0"
    unfolding vars_def degree.rep_eq
    by (simp; metis (no_types, lifting) Max_ge finite_imageI finite_insert finite_keys gr0I image_subset_iff le_zero_eq lookup_eq_zero_in_keys_contradict subset_insertI)
qed

lemma vars_non_zero_degree: "vars P = {v. degree P v \<noteq> 0}"
  using in_vars_non_zero_degree by blast

lemma vars_Const [simp]: "vars (Const x) = {}"
  by (simp add: Const.rep_eq Const\<^sub>0_def vars_def)

lemma vars_zero [simp]: "vars 0 = {}"
  by (metis Const_zero vars_Const)

lemma vars_Var [simp]: "vars ((Var v) :: ('a::zero_neq_one) mpoly) = {v}"
  using vars_monom_single_cases unfolding monom_def Var_def Var\<^sub>0_def by force

lemma vars_neg:
  fixes P :: "'a::ab_group_add mpoly"
  shows "vars (- P) = vars P"
proof -
  have "keys (mapping_of (-P)) = keys (mapping_of P)"
    unfolding keys.rep_eq uminus_mpoly.rep_eq
    by simp
  thus "vars (- P) = vars P"
    unfolding vars_def
    by simp
qed

lemma vars_add_different_degree:
  fixes P :: "'a::ab_group_add mpoly"
  assumes "\<forall>u \<in> vars P \<inter> vars Q. degree P u \<noteq> degree Q u"
  shows "vars (P + Q) = vars P \<union> vars Q"
  apply (rule set_eqI)
  subgoal for v
    using assms
    unfolding vars_non_zero_degree
    using degree_add_different_degree[of P v Q]
    by (simp; smt (verit, del_insts) IntI ab_semigroup_add_class.add_ac(1) add.commute add.right_inverse add.right_neutral degree_add_different_degree max.strict_coboundedI1 mem_Collect_eq)
  done

lemma vars_diff:
  fixes P :: "'a::ab_group_add mpoly"
  shows "vars (P - Q) \<subseteq> vars P \<union> vars Q"
  unfolding diff_conv_add_uminus
  using vars_neg vars_add by blast

lemma vars_diff_different_degree:
  fixes P :: "'a::ab_group_add mpoly"
  assumes "\<forall>u \<in> vars P \<inter> vars Q. degree P u \<noteq> degree Q u"
  shows "vars (P - Q) = vars P \<union> vars Q"
  unfolding diff_conv_add_uminus vars_neg[of Q, symmetric]
  apply (rule vars_add_different_degree)
  unfolding degree_neg vars_neg apply (rule assms)
  done

lemma vars_mult_non_zero:
  fixes P Q :: "'a::idom mpoly"
  shows "P \<noteq> 0 \<Longrightarrow> Q \<noteq> 0 \<Longrightarrow> vars (P * Q) = vars P \<union> vars Q"
  unfolding vars_non_zero_degree
  using degree_mult_non_zero[of P Q]
  by auto

lemma vars_pow: "vars (P^n) \<subseteq> vars P"
proof (induct n)
  case 0
  show ?case
    by (metis bot_least monom_pow mult_is_0 power_eq_if vars_monom_single_cases)
next
  case (Suc n)
  thus ?case
    by (metis Un_absorb1 power_Suc2 vars_mult)
qed

lemma vars_pow_positive:
  fixes P :: "'a::idom mpoly"
  assumes "n > 0"
  shows "vars (P ^ n) = vars P"
proof (induction rule: nat_induct_non_zero[OF assms])
  show "vars (P ^ 1) = vars P" by simp
next
  fix m :: nat
  assume 0: "m > 0"
  assume 1: "vars (P ^ m) = vars P"
  show "vars (P ^ Suc m) = vars P"
  proof cases
    assume 2: "P = 0"
    show ?thesis unfolding 2 by simp
  next
    assume 3: "P \<noteq> 0"
    show ?thesis
      unfolding power_Suc2
      apply (subst vars_mult_non_zero)
      subgoal using 0 3 pow_positive by blast
      subgoal using 3 .
      subgoal using vars_pow by blast
      done
  qed
qed

lemma vars_prod:
  fixes S :: "'a set"
    and f :: "_ \<Rightarrow> (_ :: zero_neq_one) mpoly"
  shows "vars (prod f S) \<subseteq> \<Union> (vars ` f ` S)"
proof (cases "finite S")
  case True
  then show ?thesis
  proof (induction S rule:finite_induct)
    case empty
    then show ?case
      apply simp
      unfolding vars_def one_mpoly.rep_eq
      by simp
  next
    case (insert s S)
    then have "vars (prod f (insert s S)) = vars (f s * prod f S)" by (metis prod.insert)
    also have "... \<subseteq> vars (f s) \<union> vars (prod f S)" by (simp add: vars_mult)
    also have "... \<subseteq> (\<Union>m\<in>insert s S. vars (f m))" using insert.IH by auto
    finally show ?case by simp
  qed
next
  case False
  then show ?thesis
  proof -
    from `infinite S` have "prod f S = 1" by simp
    hence "vars (prod f S) = {}"
      by (metis Const_one vars_Const)
    thus ?thesis by simp
  qed
qed

lemma vars_empty:
  assumes "vars P = {}"
  shows "\<exists>c. P = Const c"
proof -
  have 0: "\<forall>x\<in>keys (mapping_of P). x = 0" using assms unfolding vars_def by auto
  have "P = Const (lookup (mapping_of P) 0)"
    unfolding mapping_of_inject[symmetric] Const.rep_eq Const\<^sub>0_def
    unfolding lookup_inject[of "mapping_of P", symmetric] Poly_Mapping.single.rep_eq
    unfolding when_def apply (rule ext)
    using 0 unfolding keys_def apply auto
    done
  thus ?thesis by blast
qed


subsubsection "Maximum variable index"

(* DEFINITION USED FOR EXPLICIT COMPUTATION *)
definition max_vars where "max_vars P \<equiv> Max (insert 0 (vars P))"

lemma after_max_vars:
  "lookup (mapping_of P) m \<noteq> 0 \<Longrightarrow> \<forall>v\<ge>max_vars P + 1. lookup m v = 0"
proof (rule allI; rule impI)
  fix v
  assume 0: "lookup (mapping_of P) m \<noteq> 0"
  assume "max_vars P + 1 \<le> v"
  hence "v \<notin> vars P" unfolding max_vars_def
    by (metis Max.insert Max_ge add.commute empty_iff max_nat.left_neutral not_less_eq_eq
              plus_1_eq_Suc vars_finite)
  thus "lookup m v = 0" using 0 by (simp add: in_keys_iff vars_def)
qed

lemma max_vars_of_nonempty: "vars P \<noteq> {} \<Longrightarrow> max_vars P = Max (vars P)"
  unfolding max_vars_def by (simp add: vars_finite)

subsubsection "Simplification rules for maximum variable index"

lemma max_vars_Const [simp]: "max_vars (Const x) = 0"
  unfolding max_vars_def by simp

lemma max_vars_one [simp]: "max_vars 1 = 0"
  unfolding max_vars_def
  by (metis Const_one max_vars_def max_vars_Const)

lemma max_vars_Var [simp]: "max_vars ((Var v) :: ('a::zero_neq_one) mpoly) = v"
  unfolding max_vars_def by simp

lemma max_vars_add: "max_vars (P + Q) \<le> max (max_vars P) (max_vars Q)"
  unfolding max_vars_def using vars_add
  by (smt (verit, ccfv_threshold) Max.coboundedI Max_in UnE finite.insertI insertCI insertE
          insert_not_empty le_max_iff_disj subset_iff vars_finite)
 
lemma max_vars_neg: "max_vars (- P) = max_vars P"
  unfolding max_vars_def using vars_neg by metis
  
lemma max_vars_diff:
  fixes P :: "'a::ab_group_add mpoly"
  shows "max_vars (P - Q) \<le> max (max_vars P) (max_vars Q)"
  unfolding diff_conv_add_uminus
  by (metis max_vars_add max_vars_neg)

lemma max_vars_diff':
  fixes P :: "int mpoly"
  shows "max_vars (P - Q) \<le> max (max_vars P) (max_vars Q)"
  by (rule max_vars_diff)

lemma max_vars_pow: "max_vars (P ^ n) \<le> max_vars P"
  unfolding max_vars_def using vars_pow
  by (metis Max_mono empty_not_insert finite_insert insert_mono vars_finite)

lemma max_vars_pow_positive:
  fixes P :: "'a::idom mpoly"
  assumes "n > 0"
  shows "max_vars (P ^ n) = max_vars P"
  unfolding max_vars_def vars_pow_positive[of n P, OF \<open>n > 0\<close>] ..

lemma max_vars_mult: "max_vars (P * Q) \<le> max (max_vars P) (max_vars Q)"
  unfolding max_vars_def using vars_mult
  by (smt (z3) Max_ge Max_in UnE finite.insertI in_mono insert_iff insert_not_empty max.bounded_iff
          max_def vars_finite)

lemmas max_vars_simps = max_vars_add max_vars_neg max_vars_diff max_vars_pow
                        max_vars_pow_positive max_vars_mult

method mpoly_vars = 
  ( rule subset_trans[OF vars_pow]
  | rule subset_trans[OF vars_add Un_least]
  | rule subset_trans[OF vars_diff Un_least]
  | rule subset_trans[OF vars_mult Un_least]
  | rule Set.empty_subsetI
  | unfold vars_neg
  | unfold Const_numeral[symmetric]
  | unfold vars_Var
  | unfold vars_Const
  | simp_all (* For discharging goals of the type {0} \<subseteq> {0, 1, 2} *) )+


end