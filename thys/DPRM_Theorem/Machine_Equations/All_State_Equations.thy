subsubsection \<open>Wrap-up: Combining all state equations\<close>

theory All_State_Equations imports State_Unique_Equations State_d_Equation
                                                                 
begin

text \<open>The remaining equations:\<close>

context rm_eq_fixes
begin

  text \<open>Equation 4.27\<close>
  definition state_m :: "bool" where
    "state_m \<equiv> s m = b ^ q"

  text \<open>Equation not in the book\<close>
  definition state_partial_sum_mask :: "bool" where
    "state_partial_sum_mask \<equiv> \<forall>M\<le>m. (\<Sum>k\<le>M. s k) \<preceq> e"

  text \<open>Wrapping it all up\<close>

  definition state_equations :: "bool" where
    "state_equations \<equiv> state_relations_from_recursion \<and> state_unique_equations 
                     \<and> state_partial_sum_mask \<and> state_m"

end

context register_machine
begin

lemma state_m_dioph:
  fixes b q :: polynomial
  fixes s :: "polynomial list"
  assumes "length s = Suc m"
  defines "DR \<equiv> LARY (\<lambda>ll. rm_eq_fixes.state_m p (ll!0!0) (ll!0!1) (nth (ll!1))) [[b, q], s]"
  shows "is_dioph_rel DR"
proof - 
  define DS where "DS \<equiv> [(s!m) = b ^ q]"

  have "eval DS a = eval DR a" for a 
    using DS_def DR_def rm_eq_fixes.state_m_def rm_eq_fixes_def local.register_machine_axioms 
    using assms by (simp add: defs)

  moreover have "is_dioph_rel DS"
    unfolding DS_def by (auto simp: dioph)

  ultimately show ?thesis using is_dioph_rel_def by auto
qed

lemma state_partial_sum_mask_dioph:
  fixes e :: polynomial
  fixes s :: "polynomial list"
  assumes "length s = Suc m"
  defines "DR \<equiv> LARY (\<lambda>ll. rm_eq_fixes.state_partial_sum_mask p (ll!0!0) (nth (ll!1))) [[e], s]"
  shows "is_dioph_rel DR"
proof - 

  define partial_sum_mask where "partial_sum_mask \<equiv> (\<lambda>m. (sum_polynomial (nth s) [0..<Suc m] [\<preceq>] e))"
  define DS where "DS \<equiv> [\<forall><Suc m] partial_sum_mask"

  have "eval DS a = eval DR a" for a 
  proof - 

    have aux: "((\<Sum>j = 0..<k. peval (s ! (([0..<Suc k]) ! j)) a) 
                        + peval (s ! (([0..<Suc k]) ! k)) a \<preceq> peval e a) 
             = ((\<Sum>j = 0..<k. peval (s ! j) a) 
                        + peval (s ! k) a \<preceq> peval e a)" for k
    proof -
      have "[0..<Suc k] ! k = 0 + k"
        using nth_upt[of 0 k "Suc k"] by simp

      moreover have "(\<Sum>j = 0..<k. peval (s ! (([0..<Suc k]) ! j)) a) 
                   = (\<Sum>j = 0..<k. peval (s ! j) a)" 
        apply (rule sum.cong, simp) using nth_upt[of 0 _ "Suc k"] 
        by (metis Suc_lessD add_cancel_right_left ex_nat_less_eq not_less_eq)
      ultimately show ?thesis 
        by auto 
    qed

    have aux2: "(\<Sum>j = 0..<Suc k. peval (s ! j) a) =
                (sum ((!) (map (\<lambda>P. peval P a) s)) {..k})" if "k\<le>m" for k
      apply (rule sum.cong, auto) 
      by (metis assms(1) dual_order.strict_trans le_imp_less_Suc nth_map 
          order.not_eq_order_implies_strict that)

    have "eval DS a = (\<forall>k<Suc m.
                      (\<Sum>j = 0..<k. peval (s ! j) a) + peval (s ! k) a \<preceq> peval e a)"
      unfolding DS_def partial_sum_mask_def using aux
      by (simp add: defs \<open>length s = Suc m\<close> sum_polynomial_eval)

    also have "... = (\<forall>k\<le>m.
                     (\<Sum>j = 0..<k. peval (s ! j) a) + peval (s ! k) a \<preceq> peval e a)"
      by (simp add: less_Suc_eq_le)

    finally show ?thesis using rm_eq_fixes_def local.register_machine_axioms DR_def 
      rm_eq_fixes.state_partial_sum_mask_def aux2 by (simp add: defs)
  qed

  moreover have "is_dioph_rel DS"
    unfolding DS_def partial_sum_mask_def by (auto simp: dioph)

  ultimately show ?thesis using is_dioph_rel_def by auto
qed

definition state_equations_relation :: "polynomial \<Rightarrow> polynomial \<Rightarrow> polynomial \<Rightarrow> polynomial list
    \<Rightarrow> polynomial list \<Rightarrow> relation" ("[STATE] _ _ _ _ _")where
  "[STATE] b e q z s \<equiv> LARY (\<lambda>ll. rm_eq_fixes.state_equations p (ll!0!0) (ll!0!1) (ll!0!2) 
                                                          (nth (ll!1)) (nth (ll!2))) 
                        [[b, e, q], z, s]"

lemma state_equations_dioph:
  fixes b e q :: polynomial
  fixes s z :: "polynomial list"
  assumes "length s = Suc m" "length z = n"
  defines "DR \<equiv> [STATE] b e q z s"
  shows "is_dioph_rel DR"
proof - 

  define DS where 
    "DS \<equiv>  (LARY (\<lambda>ll. rm_eq_fixes.state_relations_from_recursion p (ll!0!0) (ll!0!1)
                 (nth (ll!1)) (nth (ll!2))) [[b, e], z, s])
       [\<and>] (LARY (\<lambda>ll. rm_eq_fixes.state_unique_equations p (ll!0!0) (ll!0!1) (ll!0!2) (nth (ll!1))) 
                 [[b, e, q], s])
       [\<and>] (LARY (\<lambda>ll. rm_eq_fixes.state_partial_sum_mask p (ll!0!0) (nth (ll!1))) [[e], s])
       [\<and>] (LARY (\<lambda>ll. rm_eq_fixes.state_m p (ll!0!0) (ll!0!1) (nth (ll!1))) [[b, q], s])"

  have "eval DS a = eval DR a" for a 
    using DS_def DR_def rm_eq_fixes.state_equations_def 
    state_equations_relation_def rm_eq_fixes_def local.register_machine_axioms by (auto simp: defs)

  moreover have "is_dioph_rel DS"
    unfolding DS_def using assms state_relations_from_recursion_dioph[of z s] state_m_dioph[of s] 
    state_partial_sum_mask_dioph state_unique_equations_dioph and_dioph 
    by (auto simp: dioph)

  ultimately show ?thesis using is_dioph_rel_def by auto
qed

end

end

