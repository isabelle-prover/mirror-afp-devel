theory RM_Sums_Diophantine imports Equation_Setup "../Diophantine/Register_Machine_Sums"
                                   "../Diophantine/Binary_And"

begin

context register_machine
begin

definition sum_ssub_nzero_of_bit_and  :: "polynomial \<Rightarrow> nat \<Rightarrow> polynomial list \<Rightarrow> polynomial list
                                    \<Rightarrow> relation" 
  ("[_ = \<Sum>S- _ '(_ && _')]") where
  "[x = \<Sum>S- d (s && z)] \<equiv> let x' = push_param x (length p);
                                s' = push_param_list s (length p); 
                                z' = push_param_list z (length p)
                            in [\<exists>length p] [\<forall><length p] (\<lambda>i. [Param i = s'!i && z'!i])
                                                        [\<and>] x' [=] ([\<Sum>S-] p d Param)"

lemma sum_ssub_nzero_of_bit_and_dioph[dioph]:
  fixes s z :: "polynomial list" and d :: nat and x
  shows "is_dioph_rel [x = \<Sum>S- d (s && z)]"
  unfolding sum_ssub_nzero_of_bit_and_def by (auto simp add: dioph)

lemma sum_rsub_nzero_of_bit_and_eval:
  fixes z s :: "polynomial list" and d :: nat and x :: polynomial
  assumes "length s = Suc m" "length z = Suc m" "length p > 0"
  shows "eval [x = \<Sum>S- d (s && z)] a
         \<longleftrightarrow> peval x a = \<Sum>S- p d (\<lambda>k. peval (s!k) a && peval (z!k) a)" (is "?P \<longleftrightarrow> ?Q")
proof -
  have invariance: "\<forall>k<length p. y1 k = y2 k \<Longrightarrow> \<Sum>S- p d y1 = \<Sum>S- p d y2" for y1 y2
    unfolding sum_ssub_nzero.simps apply (intro sum.cong, simp)
    using \<open>length p > 0\<close> by auto (metis Suc_pred le_imp_less_Suc length_greater_0_conv)

  have len_ps: "length s = length p"
    using m_def \<open>length s = Suc m\<close> \<open>length p > 0\<close> by auto
  have len_pz: "length z = length p"
    using m_def \<open>length z = Suc m\<close> \<open>length p > 0\<close> by auto

  show ?thesis
  proof (rule)
    assume ?P
    thus ?Q
      using sum_ssub_nzero_of_bit_and_def \<open>length p > 0\<close> apply (auto simp add: defs push_push)
      using push_push_map_i apply (simp add: push_param_list_def len_ps len_pz)
      unfolding list_eval_def apply (auto simp: assms len_ps len_pz invariance)
      apply (rule sum_ssub_nzero_cong) apply auto
      by (metis (no_types, lifting) One_nat_def assms(1) assms(2)
                le_imp_less_Suc len_ps m_def nth_map)
      
  next
    assume ?Q
    thus ?P
      using sum_ssub_nzero_of_bit_and_def \<open>length p > 0\<close> apply (auto simp add: defs push_push)
      apply (rule exI[of _ "map (\<lambda>k. peval (s ! k) a && peval (z ! k) a) [0..<length p]"], simp)
      using push_push push_push_map_i
      by (simp add: push_param_list_def invariance push_list_eval len_ps len_pz)
  qed
qed

definition sum_ssub_zero_of_bit_and  :: "polynomial \<Rightarrow> nat \<Rightarrow> polynomial list \<Rightarrow> polynomial list
                                    \<Rightarrow> relation" 
  ("[_ = \<Sum>S0 _ '(_ && _')]") where
  "[x = \<Sum>S0 d (s && z)] \<equiv> let x' = push_param x (length p);
                                s' = push_param_list s (length p); 
                                z' = push_param_list z (length p)
                            in [\<exists>length p] [\<forall><length p] (\<lambda>i. [Param i = s'!i && z'!i])
                                                        [\<and>] x' [=] [\<Sum>S0] p d Param"

lemma sum_ssub_zero_of_bit_and_dioph[dioph]:
  fixes s z :: "polynomial list" and d :: nat and x
  shows "is_dioph_rel [x = \<Sum>S0 d (s && z)]"
  unfolding sum_ssub_zero_of_bit_and_def by (auto simp add: dioph)

lemma sum_rsub_zero_of_bit_and_eval:
  fixes z s :: "polynomial list" and d :: nat and x :: polynomial
  assumes "length s = Suc m" "length z = Suc m" "length p > 0"
  shows "eval [x = \<Sum>S0 d (s && z)] a
         \<longleftrightarrow> peval x a = \<Sum>S0 p d (\<lambda>k. peval (s!k) a && peval (z!k) a)" (is "?P \<longleftrightarrow> ?Q")
proof -
  have invariance: "\<forall>k<length p. y1 k = y2 k \<Longrightarrow> \<Sum>S0 p d y1 = \<Sum>S0 p d y2" for y1 y2
    unfolding sum_ssub_zero.simps apply (intro sum.cong, simp)
    using \<open>length p > 0\<close> by auto (metis Suc_pred le_imp_less_Suc length_greater_0_conv)

  have len_ps: "length s = length p"
    using m_def \<open>length s = Suc m\<close> \<open>length p > 0\<close> by auto
  have len_pz: "length z = length p"
    using m_def \<open>length z = Suc m\<close> \<open>length p > 0\<close> by auto

  show ?thesis
  proof (rule)
    assume ?P
    thus ?Q
      using sum_ssub_zero_of_bit_and_def \<open>length p > 0\<close> apply (auto simp add: defs push_push)
      using push_push_map_i apply (simp add: push_param_list_def len_ps len_pz)
      unfolding list_eval_def apply (auto simp: assms len_ps len_pz invariance)
      apply (rule sum_ssub_zero_cong) apply auto
      by (metis (no_types, lifting) One_nat_def assms(1) assms(2)
                le_imp_less_Suc len_ps m_def nth_map)
  next
    assume ?Q
    thus ?P
      using sum_ssub_zero_of_bit_and_def \<open>length p > 0\<close> apply (auto simp add: defs push_push)
      apply (rule exI[of _ "map (\<lambda>k. peval (s ! k) a && peval (z!k) a) [0..<length p]"], simp)
      using push_push push_push_map_i
      by (simp add: push_param_list_def invariance push_list_eval len_ps len_pz)
  qed
qed

end

end