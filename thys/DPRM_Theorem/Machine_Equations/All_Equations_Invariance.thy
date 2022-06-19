subsubsection \<open>Invariance of equations\<close>

theory All_Equations_Invariance
  imports Register_Equations All_State_Equations Mask_Equations Constants_Equations
                                                       
begin

context register_machine
begin

definition all_equations where
  "all_equations a q b c d e f r z s
    \<equiv> rm_eq_fixes.register_equations p n a b q r z s 
    \<and> rm_eq_fixes.state_equations p b e q z s
    \<and> rm_eq_fixes.mask_equations n c d e f r z
    \<and> rm_eq_fixes.constants_equations b c d e f q 
    \<and> rm_eq_fixes.miscellaneous_equations a c q"

lemma all_equations_invariance:
  fixes r z s :: "nat \<Rightarrow> nat"
    and r' z' s' :: "nat \<Rightarrow> nat"
  assumes "\<forall>i<n. r i = r' i" and "\<forall>i<n. z i = z' i" and "\<forall>i<Suc m. s i = s' i" 
  shows "all_equations a q b c d e f r z s = all_equations a q b c d e f r' z' s'"
proof -
  have r: "i<n \<longrightarrow> r i = r' i" for i
    using assms by auto
  have z: "i<n \<longrightarrow> z i = z' i" for i
    using assms by auto
  have s: "i<Suc m \<longrightarrow> s i = s' i" for i
    using assms by auto

  have "length p > 0" using p_nonempty by auto
  have "n > 0" using n_gt_0 by auto

  have z_at_modifies: "z (modifies (p ! k)) = z' (modifies (p ! k))" if "k < length p" for k
    using z[of "modifies (p!k)"] m_def modifies_yields_valid_register that by auto

  have "rm_eq_fixes.register_equations p n a b q r z s 
      = rm_eq_fixes.register_equations p n a b q r' z' s'"
  proof - 

    have sum_radd: "\<Sum>R+ p d s = \<Sum>R+ p d s'" for d
      by (rule sum_radd_cong, auto simp: s m_def)

    have sum_rsub: "\<Sum>R- p d (\<lambda>k. s k && z d) = \<Sum>R- p d (\<lambda>k. s' k && z' d)" for d
      apply (rule sum_rsub_cong) using s z m_def z_at_modifies \<open>length p > 0\<close> 
        by (auto, metis Suc_pred \<open>0 < length p\<close> le_imp_less_Suc)

    have "rm_eq_fixes.register_0 p a b r z s = rm_eq_fixes.register_0 p a b r' z' s'"
      using rm_eq_fixes_def local.register_machine_axioms rm_eq_fixes.register_0_def sum_radd[of 0] 
        sum_rsub[of 0] using r \<open>n > 0\<close> by auto

    moreover have "rm_eq_fixes.register_l p n b r z s = rm_eq_fixes.register_l p n b r' z' s'"
      using rm_eq_fixes.register_l_def sum_radd sum_rsub rm_eq_fixes_def 
        local.register_machine_axioms using r \<open>n > 0\<close> by auto

    moreover have "rm_eq_fixes.register_bound n b q r = rm_eq_fixes.register_bound n b q r'"
      using rm_eq_fixes_def local.register_machine_axioms rm_eq_fixes.register_bound_def 
      using r by auto

    ultimately show ?thesis
      using rm_eq_fixes_def local.register_machine_axioms rm_eq_fixes.register_equations_def 
      by auto
  qed

  moreover have "rm_eq_fixes.state_equations p b e q z s 
               = rm_eq_fixes.state_equations p b e q z' s'"
  proof - 
    have "rm_eq_fixes.state_relations_from_recursion p b e z s 
        = rm_eq_fixes.state_relations_from_recursion p b e z' s'"
    proof - 

      have sum_sadd: "\<Sum>S+ p d s = \<Sum>S+ p d s'" for d 
        by (rule sum_sadd_cong, auto simp: s m_def)

      have sum_ssub_nzero: "\<Sum>S- p d (\<lambda>k. s k && z (modifies (p ! k))) 
          = \<Sum>S- p d (\<lambda>k. s' k && z' (modifies (p ! k)))" for d
        apply (rule sum_ssub_nzero_cong) using z_at_modifies z s
        by (metis One_nat_def Suc_pred \<open>0 < length p\<close> le_imp_less_Suc m_def)

      have sum_ssub_zero: "\<Sum>S0 p d (\<lambda>k. s k && e - z (modifies (p ! k))) 
          = \<Sum>S0 p d (\<lambda>k. s' k && e - z' (modifies (p ! k)))" for d 
        apply (rule sum_ssub_zero_cong) using z_at_modifies z s
        by (metis One_nat_def Suc_pred \<open>0 < length p\<close> le_imp_less_Suc m_def)

      have "rm_eq_fixes.state_0 p b e z s = rm_eq_fixes.state_0 p b e z' s'"
        using rm_eq_fixes.state_0_def sum_sadd sum_ssub_nzero sum_ssub_zero
              rm_eq_fixes_def local.register_machine_axioms
        using s by auto

      moreover have "rm_eq_fixes.state_d p b e z s = rm_eq_fixes.state_d p b e z' s'"
        using rm_eq_fixes.state_d_def sum_sadd sum_ssub_nzero sum_ssub_zero
              rm_eq_fixes_def local.register_machine_axioms
        using s by auto

      ultimately show ?thesis 
        using rm_eq_fixes_def local.register_machine_axioms 
              rm_eq_fixes.state_relations_from_recursion_def by auto
    qed

    moreover have "rm_eq_fixes.state_unique_equations p b e q s
                 = rm_eq_fixes.state_unique_equations p b e q s'"
      using rm_eq_fixes.state_unique_equations_def 
      rm_eq_fixes_def local.register_machine_axioms rm_eq_fixes.state_mask_def 
      rm_eq_fixes.state_bound_def
      using s by force

    ultimately show ?thesis 
      using rm_eq_fixes_def local.register_machine_axioms rm_eq_fixes.state_equations_def 
      rm_eq_fixes.state_mask_def rm_eq_fixes.state_bound_def rm_eq_fixes.state_m_def
      rm_eq_fixes.state_partial_sum_mask_def using s z by auto
  qed

  moreover have "rm_eq_fixes.mask_equations n c d e f r z = 
                 rm_eq_fixes.mask_equations n c d e f r' z'"
  proof - 
    have "rm_eq_fixes.register_mask n d r = rm_eq_fixes.register_mask n d r'"
      using rm_eq_fixes_def local.register_machine_axioms rm_eq_fixes.register_mask_def r by auto

    moreover have "rm_eq_fixes.zero_indicator_mask n e z = rm_eq_fixes.zero_indicator_mask n e z'"
      using rm_eq_fixes.zero_indicator_mask_def rm_eq_fixes_def local.register_machine_axioms z 
        by auto

    moreover have "rm_eq_fixes.zero_indicator_0_or_1 n c d f r z 
                 = rm_eq_fixes.zero_indicator_0_or_1 n c d f r' z'"
      using rm_eq_fixes_def local.register_machine_axioms rm_eq_fixes.zero_indicator_0_or_1_def 
      using r z by auto

    ultimately show ?thesis 
      using rm_eq_fixes_def local.register_machine_axioms rm_eq_fixes.mask_equations_def by auto
  qed
  
  ultimately show ?thesis
    unfolding all_equations_def by auto
qed
  

end

end