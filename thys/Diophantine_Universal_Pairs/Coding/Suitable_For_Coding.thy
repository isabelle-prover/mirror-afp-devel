theory Suitable_For_Coding 
  imports "../Diophantine_Definition" "HOL-Library.Rewrite" "MPoly_Utils/Total_Degree_Env"
begin

subsection \<open>Polynomials suitable for coding\<close>

definition fresh_var :: "int mpoly \<Rightarrow> nat" where
  "fresh_var P = (if vars P = {} then 1 else max_vars P + 1)"

definition suitable_for_coding :: "int mpoly \<Rightarrow> int mpoly" where 
  "suitable_for_coding P \<equiv> P\<^sup>2 + (Var (fresh_var P) - 1)\<^sup>2"

lemma suitable_for_coding_degree_vars:
  shows "degree (suitable_for_coding P) (fresh_var P) > 0" 
        "vars (suitable_for_coding P) = insert (fresh_var P) (vars P)"
proof -
  have "Suc (Max (vars P)) \<notin> vars P"
    by (meson Max_ge Suc_n_not_le_n vars_finite)

  hence "fresh_var P \<notin> vars P"
  proof (cases "vars P = {}")
    case True
    then show ?thesis by auto
  next
    case False
    show ?thesis unfolding fresh_var_def 
      unfolding max_vars_of_nonempty[OF False]
      using \<open>Suc (Max (vars P)) \<notin> vars P\<close> by simp
  qed
  hence 0: "degree P (fresh_var P) = 0"
    unfolding in_vars_non_zero_degree by blast

  have 1: "degree (P\<^sup>2) (fresh_var P) = 0"
    apply (subst degree_pow_positive)
    subgoal by simp
    subgoal using 0 by simp
    done

  have 2: "degree ((Var (fresh_var P) :: int mpoly)\<^sup>2) (fresh_var P) = 2"
    by (subst degree_pow_positive; simp)

  have 3: "degree ((Const 1 :: int mpoly)\<^sup>2) (fresh_var P) = 0"
    by (subst degree_pow_positive; simp)

  have 4: "degree ((Const 2 :: int mpoly) * Var (fresh_var P) * Const 1) (fresh_var P) = 1"
    apply (subst degree_mult_non_zero)
    subgoal by (simp_all add: Const_numeral Var_neq_zero)
    subgoal by (simp add: Const_one)
    subgoal
      apply (subst degree_mult_non_zero)
      subgoal by (simp add: Const_numeral)
      subgoal by (simp add: Var_neq_zero)
      subgoal by simp
      done
    done

  have 5: "degree ((Var (fresh_var P) :: int mpoly)\<^sup>2 + (Const 1)\<^sup>2) (fresh_var P) = 2"
    apply (subst degree_add_different_degree)
    unfolding 2 3 apply auto
    done

  have 6: "degree ((Var (fresh_var P) :: int mpoly)\<^sup>2 + (Const 1)\<^sup>2 - Const 2 * Var (fresh_var P) * Const 1) (fresh_var P) = 2"
    apply (subst degree_diff_different_degree)
    unfolding 4 5 apply auto
    done

  show "degree (suitable_for_coding P) (fresh_var P) > 0"
    unfolding suitable_for_coding_def power2_diff
    unfolding Const_numeral[symmetric] Const_one[symmetric]
    apply (subst degree_add_different_degree[of _ "fresh_var P"])
    subgoal unfolding 1 6 by auto
    subgoal unfolding 1 6 by auto
    done

  have 7: "vars (P\<^sup>2) = vars P"
    by (subst vars_pow_positive; auto)

  have 8: "vars ((Const 1)\<^sup>2 :: int mpoly) = {}"
    by (subst vars_pow_positive; auto)

  have 9: "vars ((Var (fresh_var P) :: int mpoly)\<^sup>2) = {fresh_var P}"
    by (subst vars_pow_positive; auto)

  have 10: "vars ((Var (fresh_var P) :: int mpoly)\<^sup>2 + (Const 1)\<^sup>2) = {fresh_var P}"
    apply (subst vars_add_different_degree)
    unfolding 8 9 apply auto
    done

  have 11: "vars ((Const 2 :: int mpoly) * Var (fresh_var P) * Const 1) = {fresh_var P}"
    apply (subst vars_mult_non_zero)
    subgoal by (simp add: Const_numeral Var_neq_zero)
    subgoal by (simp add: Const_one)
    subgoal 
      apply (subst vars_mult_non_zero)
      subgoal by (simp add: Const_numeral)
      subgoal by (simp add: Var_neq_zero)
      subgoal by simp
      done
    done

  have 12: "vars ((Var (fresh_var P) :: int mpoly)\<^sup>2 + (Const 1)\<^sup>2 - Const 2 * Var (fresh_var P) * Const 1) = {fresh_var P}"
    apply (subst vars_diff_different_degree)
    unfolding 10 11
    using 4 5 apply auto
    done

  show "vars (suitable_for_coding P) = insert (fresh_var P) (vars P)"
    unfolding suitable_for_coding_def power2_diff
    unfolding Const_numeral[symmetric] Const_one[symmetric]
    apply (subst vars_add_different_degree)
    subgoal unfolding 7 12 using 1 6 by auto
    subgoal
      apply (subst vars_diff_different_degree)
      subgoal unfolding 10 11 using 4 5 by auto
      subgoal
        apply (subst vars_add_different_degree)
        subgoal unfolding 8 by auto
        subgoal
          apply (subst vars_pow_positive[of _ "Var (fresh_var P)"])
          subgoal by simp
          subgoal unfolding 7 8 11 by simp
          done
        done
      done
    done
qed


lemma suitable_for_coding_coeff0:
  fixes P
  defines "n \<equiv> max_vars (suitable_for_coding P)" (* = \<nu> + 1 *)
  defines "m0 \<equiv> Abs_poly_mapping ((!\<^sub>0) (replicate (n+1) 0))"
  shows "coeff (suitable_for_coding P) m0 > 0"
proof -
  have h0: "nth_default 0 (replicate (n+1) 0) = (\<lambda>x. 0)"
    unfolding nth_default_def
    using List.nth_replicate by fastforce

  have h1: "m0 = 0"
    unfolding m0_def
    apply (subst zero_poly_mapping_def)
    apply (subst Abs_poly_mapping_inject)
    unfolding nth0_def when_def apply simp_all
    using List.nth_replicate by fastforce
    
  have "insertion (nth_default 0 (replicate (n+1) 0)) (suitable_for_coding P) = coeff (suitable_for_coding P) m0"
    using insertion_trivial[of "suitable_for_coding P"]
    by (subst h0, subst h1, simp) 

  moreover have "insertion (nth_default 0 (replicate (n+1) 0)) (suitable_for_coding P) > 0"
    unfolding suitable_for_coding_def fresh_var_def nth_default_def
    by (simp add: suitable_for_coding_degree_vars(2) fresh_var_def n_def vars_finite)

  ultimately show ?thesis
    by auto
qed


lemma suitable_for_coding_max_vars:
  assumes "vars P \<noteq> {}"
  shows "max_vars (suitable_for_coding P) = max_vars P + 1"
proof -
  have 0: "vars (suitable_for_coding P) \<subseteq> vars P \<union> {fresh_var P}"
    unfolding suitable_for_coding_degree_vars by simp

  have 1: "Max (vars P \<union> {fresh_var P}) = fresh_var P"
    unfolding max_vars_def
    apply (subst Max_Un)
    unfolding max_vars_def fresh_var_def
    apply (auto simp: assms vars_finite)
    done

  have 2: "Max (insert 0 (vars (suitable_for_coding P))) = Max (vars (suitable_for_coding P))"
    by (simp add: suitable_for_coding_degree_vars(2) vars_finite)

  have "max_vars (suitable_for_coding P) \<le> fresh_var P"
    unfolding max_vars_def
    apply (subst 1[symmetric]) unfolding 2
    apply (rule Max_mono[OF 0])
    using suitable_for_coding_degree_vars(2)[of P]
    apply (auto simp: vars_finite)
    done

  thus ?thesis
    using assms suitable_for_coding_degree_vars(2)[of P]
    unfolding fresh_var_def max_vars_def
    by (simp add: order_antisym_conv vars_finite)
qed


lemma suitable_for_coding_diophantine_equivalent: 
  fixes P :: "int mpoly"
  assumes "insertion (z(0 := a)) (suitable_for_coding P) = 0" and "is_nonnegative z" 
  shows "\<exists>y. insertion (y(0 := a)) P = 0 \<and> is_nonnegative y" 
proof (rule exI[of _ z], rule conjI)
  show "insertion (z(0 := a)) P = 0"
  proof cases
    assume "vars P = {}"
    thus ?thesis
      using assms(1) unfolding suitable_for_coding_def by auto
  next
    assume "vars P \<noteq> {}"
    thus ?thesis
      using assms(1) unfolding suitable_for_coding_def by auto
  qed

  show "is_nonnegative z"
    using assms(2) by auto
qed

lemma suitable_for_coding_exists_positive_unknown: 
  fixes P :: "int mpoly"
  assumes dioph: "is_diophantine_over_N_with A P"
  assumes a: "a \<in> A"
  assumes "insertion (y(0 := a)) P = 0" and "is_nonnegative y"
  shows "\<exists>z. insertion (z(0 := a)) (suitable_for_coding P) = 0 
          \<and> (\<exists>i\<in>{1..fresh_var P}. z i > 0)
          \<and> (\<forall>i > fresh_var P. z i = 0)
          \<and> is_nonnegative z"
proof cases
  assume 0: "vars P = {}"

  define z where "z \<equiv> (\<lambda>i. if i > 1 then 0 else (y(1 := 1)) i)"

  show ?thesis
    unfolding suitable_for_coding_def
    apply (rule exI[of _ z])
    using assms 0
    unfolding fresh_var_def is_nonnegative_def z_def
    apply simp
    apply (subst insertion_irrelevant_vars[of P _ "y(0 := a)"])
    apply auto
    done
next
  assume 1: "vars P \<noteq> {}"

  define z :: "nat \<Rightarrow> int" where "z \<equiv> (\<lambda>i. if i > fresh_var P then 0 else (y(fresh_var P := 1)) i)"

  have 2: "insertion (z(0 := a)) P = 0"
  proof (subst insertion_irrelevant_vars[of P "z(0 := a)" "y(0 := a)"])
    show "v \<in> vars P \<Longrightarrow> (z(0 := int a)) v = (y(0 := int a)) v" for v
      unfolding fresh_var_def max_vars_of_nonempty[OF 1] z_def
      using 1 by (simp; metis Max_ge le_eq_less_or_eq not_less_eq_eq vars_finite)
    show "insertion (y(0 := int a)) P = 0"
      by (auto simp: assms)
  qed

  show ?thesis
  proof (rule exI[of _ z]; rule conjI[OF _ conjI[OF _ conjI]])
    show "insertion (z(0 := a)) (suitable_for_coding P) = 0"
      using 1 2
      unfolding suitable_for_coding_def fresh_var_def z_def
      by auto

    show "\<exists>i\<in>{1..fresh_var P}. z i > 0"
      apply (rule bexI[of _ "fresh_var P"])
      unfolding fresh_var_def max_vars_def z_def
      apply auto
      done

    show "\<forall>i>fresh_var P. z i = 0"
      unfolding z_def by auto
      
    show "is_nonnegative z"
      using assms(4) by (auto simp: is_nonnegative_def z_def)
  qed
qed

lemma suitable_for_coding_total_degree:
  shows "total_degree (suitable_for_coding P) > 0"
  using total_degree_zero_degree_zero suitable_for_coding_degree_vars(1)[of P]
  by fastforce


lemma suitable_for_coding_total_degree_bound:
  assumes "total_degree P > 0"
  shows "total_degree (suitable_for_coding P) \<le> 2 * total_degree P"
  unfolding suitable_for_coding_def 
  unfolding total_degree_env_id[symmetric]
  apply (rule le_trans[OF total_degree_env_add])
  apply (rule max.boundedI)
  subgoal by (simp add: total_degree_env_pow)
  subgoal 
    apply (rule le_trans[OF total_degree_env_pow]) 
    apply (rule mult_le_mono2)
    apply (rule le_trans[OF total_degree_env_diff], simp) using total_degree_env_id
    by (metis One_nat_def assms le_zero_eq less_imp_neq not_less_eq_eq)
  done

end
