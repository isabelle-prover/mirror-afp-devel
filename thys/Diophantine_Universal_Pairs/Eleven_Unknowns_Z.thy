theory Eleven_Unknowns_Z
  imports "Nine_Unknowns_N_Z/Nine_Unknowns_N_Z" "Three_Squares.Three_Squares"
begin

section \<open>Eleven Unknowns over $\mathbb{Z}$\<close>

context
  fixes P :: "int mpoly"
begin

definition Q_tilde :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "Q_tilde a z\<^sub>1 z\<^sub>2 z\<^sub>3 z\<^sub>4 z\<^sub>5 z\<^sub>6 z\<^sub>7 z\<^sub>8 z\<^sub>9 z\<^sub>1\<^sub>0 z\<^sub>1\<^sub>1 = 
  (combined_variables.Q P) a z\<^sub>1 z\<^sub>2 z\<^sub>3 z\<^sub>4 z\<^sub>5 z\<^sub>6 z\<^sub>7 z\<^sub>8 (z\<^sub>9^2 + z\<^sub>1\<^sub>0^2 + z\<^sub>1\<^sub>1^2 + z\<^sub>1\<^sub>1)"


poly_extract Q_tilde
poly_degree Q_tilde_poly | combined_variables.aux_vars combined_variables.final combined_variables.list_vars
     
lemma Q_tilde_degree_in_X_Y: 
  "Q_tilde_poly_degree = 8352 * combined_variables.Y_poly_degree P 
  + (15568 + (4176 * combined_variables.X_poly_degree P 
              + 48 * coding_variables.\<alpha> (combined_variables.P\<^sub>1 P)))"
proof -
  note Q_tilde_degree_presimplified = Q_tilde_poly_degree_def[simplified Nat.max_nat.right_neutral 
      Nat.max_nat.left_neutral Nat.plus_nat.add_0]
  note A\<^sub>2_poly_degree_alt = combined_variables.A\<^sub>2_poly_degree_def[simplified, simplified 
      Nat.Suc_eq_plus1, simplified Groups.ac_simps(1), unfolded one_add_one, 
      simplified one_plus_numeral, simplified]

  show ?thesis unfolding Q_tilde_degree_presimplified
    combined_variables.S_poly_degree_def[simplified] 
    combined_variables.T_poly_degree_def[simplified]
    combined_variables.R_poly_degree_def[simplified]
    combined_variables.A\<^sub>1_poly_degree_def[simplified]
    combined_variables.A\<^sub>3_poly_degree_def[simplified]
    A\<^sub>2_poly_degree_alt
    by simp
qed

definition delta_P_suitable ("\<delta>\<^sub>s") where 
  "delta_P_suitable \<equiv> total_degree (suitable_for_coding P)"

definition nu_P_suitable ("\<nu>\<^sub>s") where 
  "nu_P_suitable \<equiv> max_vars (suitable_for_coding P)"

definition eta\<^sub>s where
  "eta\<^sub>s \<equiv> 15616 + 116928 * \<delta>\<^sub>s + 116976 * \<delta>\<^sub>s * Suc \<delta>\<^sub>s ^ \<nu>\<^sub>s + 116928 * \<delta>\<^sub>s^2 * Suc \<delta>\<^sub>s ^ \<nu>\<^sub>s"

lemma Q_tilde_degree_eta\<^sub>s: "Q_tilde_poly_degree = eta\<^sub>s"
proof - 
  note X_degree = combined_variables.X_poly_degree_alt[unfolded combined_variables.P\<^sub>1_def 
      coding_variables.\<delta>_def, OF suitable_for_coding_total_degree, 
      folded coding_variables.\<delta>_def, folded combined_variables.P\<^sub>1_def]
  have degree_bound: "coding_variables.\<delta> (combined_variables.P\<^sub>1 P) = delta_P_suitable" 
    unfolding coding_variables.\<delta>_def combined_variables.P\<^sub>1_def delta_P_suitable_def by simp
  have vars: "coding_variables.\<nu> (combined_variables.P\<^sub>1 P) = nu_P_suitable" 
    unfolding coding_variables.\<nu>_def combined_variables.P\<^sub>1_def nu_P_suitable_def by simp
  show ?thesis
  unfolding Q_tilde_degree_in_X_Y combined_variables.Y_poly_degree_def[simplified] X_degree
  unfolding coding_variables.\<alpha>_def coding_variables.n_def
  apply simp
  unfolding vars degree_bound eta\<^sub>s_def
  apply (simp add: algebra_simps)
  using Semiring_Normalization.comm_semiring_1_class.semiring_normalization_rules(29) by metis
qed


definition \<eta> where
  "\<eta> \<nu> \<delta> \<equiv> 15616 + 233856 * \<delta> + 233952 * \<delta> * (2 * \<delta> + 1) ^ (\<nu> + 1)
            + 467712 * \<delta>^2 * (2 * \<delta> + 1) ^ (\<nu> + 1)"

lemma Q_tilde_degree:
  assumes "0 < total_degree P"
  assumes "total_degree P \<le> \<delta>"
  assumes "max_vars P \<le> \<nu>"
  shows "Q_tilde_poly_degree \<le> \<eta> \<nu> \<delta>"
proof -
  have \<nu>: "\<nu>\<^sub>s \<le> \<nu> + 1"
    apply (cases "vars P = {}")
    subgoal 
      by (simp add: fresh_var_def max_vars_of_nonempty nu_P_suitable_def
          suitable_for_coding_degree_vars(2))
    subgoal
      unfolding nu_P_suitable_def
      using suitable_for_coding_max_vars
      by (simp add: assms(3))
    done
  have \<delta>: "\<delta>\<^sub>s \<le> 2 * \<delta>"
    unfolding delta_P_suitable_def
    using suitable_for_coding_total_degree_bound[OF assms(1)] assms(2) by auto
  have \<delta>_power: "Suc \<delta>\<^sub>s ^ \<nu> \<le> Suc (2 * \<delta>) ^ \<nu>"
    by (simp add: \<delta> power_mono)
  hence \<delta>_power2: "Suc \<delta>\<^sub>s ^ \<nu>\<^sub>s \<le> Suc (2 * \<delta>) ^ (\<nu> + 1)"
    using \<nu> power_mono le_trans
    by (smt (verit) Suc_eq_plus1 \<delta> le_SucE mult_Suc mult_le_mono not_less_eq_eq power_Suc
        power_increasing trans_le_add1 trans_le_add2)
  hence \<delta>_power3: "Suc \<delta>\<^sub>s ^ \<nu>\<^sub>s \<le> Suc (2 * \<delta>) ^ \<nu> + 2 * \<delta> * Suc (2 * \<delta>) ^ \<nu>"
    using \<delta>_power2 by (algebra, simp)
  have aux: "\<delta>\<^sub>s * Suc \<delta>\<^sub>s ^ \<nu>\<^sub>s \<le> 2 * (\<delta> * (Suc (2 * \<delta>) ^ \<nu> + 2 * \<delta> * Suc (2 * \<delta>) ^ \<nu>))"
    using \<delta>_power3 mult_le_mono by (metis \<delta> more_arith_simps(11))
  have bound: "Q_tilde_poly_degree \<le> 15616 + 116928 * 2 * \<delta> + 116976 * 2 * \<delta> * Suc (2 * \<delta>) ^ (\<nu> + 1) 
                                    + 116928 * 4 * \<delta>^2 * Suc (2 * \<delta>) ^ (\<nu> + 1)"
    unfolding Q_tilde_degree_eta\<^sub>s eta\<^sub>s_def 
    apply simp
    apply (rule add_mono mult_le_mono, simp add: \<delta> \<nu>)+
    subgoal by (simp add: aux)
    subgoal 
      apply (rule add_mono mult_le_mono power_mono, simp_all add: \<delta> \<nu> \<delta>_power3)
      by (metis \<delta> numeral_Bit0_eq_double power2_eq_square power2_nat_le_eq_le power_mult_distrib)
    done
  thus ?thesis unfolding \<eta>_def by auto
qed

lemma max_vars_Q_tilde: "max_vars Q_tilde_poly \<le> 11"
proof -
  have aux_three_squares: "vars ((Var 9)\<^sup>2 + (Var 10)\<^sup>2 + (Var 11)\<^sup>2 + Var 11) \<subseteq> {9, 10, 11}"
  unfolding power2_eq_square
  by (rule subset_trans[OF vars_add Un_least]
        | rule subset_trans[OF vars_mult Un_least]
        | subst vars_Var; simp)+
  
  show ?thesis
    unfolding Q_tilde_poly_def
    apply (rule le_trans[OF max_vars_poly_subst_list_general])
    apply (simp add: max_vars_def aux_three_squares)
    apply (rule Max.boundedI, auto simp: vars_finite)
    using in_mono[OF aux_three_squares] by fastforce
qed

lemma eleven_unknowns_over_Z:
  fixes A :: "nat set"
  assumes "is_diophantine_over_N_with A P"
  shows "a \<in> A = (\<exists>z\<^sub>1 z\<^sub>2 z\<^sub>3 z\<^sub>4 z\<^sub>5 z\<^sub>6 z\<^sub>7 z\<^sub>8 z\<^sub>9 z\<^sub>1\<^sub>0 z\<^sub>1\<^sub>1. 
    Q_tilde (int a) z\<^sub>1 z\<^sub>2 z\<^sub>3 z\<^sub>4 z\<^sub>5 z\<^sub>6 z\<^sub>7 z\<^sub>8 z\<^sub>9 z\<^sub>1\<^sub>0 z\<^sub>1\<^sub>1 = 0)"
proof -

  have "(\<exists>w1 w2 w3 w4 w5 w6 w7 w8 w9. 
            w9 \<ge> 0 \<and> (combined_variables.Q P) (int a) w1 w2 w3 w4 w5 w6 w7 w8 w9 = 0) 
      = (\<exists>z\<^sub>1 z\<^sub>2 z\<^sub>3 z\<^sub>4 z\<^sub>5 z\<^sub>6 z\<^sub>7 z\<^sub>8 z\<^sub>9 z\<^sub>1\<^sub>0 z\<^sub>1\<^sub>1. 
            Q_tilde (int a) z\<^sub>1 z\<^sub>2 z\<^sub>3 z\<^sub>4 z\<^sub>5 z\<^sub>6 z\<^sub>7 z\<^sub>8 z\<^sub>9 z\<^sub>1\<^sub>0 z\<^sub>1\<^sub>1 = 0)"
  proof (intro iffI)
    assume asm1:"(\<exists>w1 w2 w3 w4 w5 w6 w7 w8 w9. w9 \<ge> 0 \<and>
               (combined_variables.Q P) (int a) w1 w2 w3 w4 w5 w6 w7 w8 w9 = 0)"
    obtain w1 w2 w3 w4 w5 w6 w7 w8 w9 where w_prop:"w9 \<ge> 0 \<and>
               (combined_variables.Q P) (int a) w1 w2 w3 w4 w5 w6 w7 w8 w9 = 0"
      using asm1 by auto
    have w9decomp:"\<exists>u9 u10 u11. w9 = u9^2+u10^2+u11^2+u11" 
      using four_decomposition_int w_prop by presburger
    obtain u9 u10 u11 where u_prop:"w9 = u9^2+u10^2+u11^2+u11" 
      using w9decomp by auto
    have cs1:"Q_tilde (int a) w1 w2 w3 w4 w5 w6 w7 w8 u9 u10 u11 = 0"
      using u_prop Q_tilde_def asm1 w_prop by presburger
    thus "\<exists>z\<^sub>1 z\<^sub>2 z\<^sub>3 z\<^sub>4 z\<^sub>5 z\<^sub>6 z\<^sub>7 z\<^sub>8 z\<^sub>9 z\<^sub>1\<^sub>0 z\<^sub>1\<^sub>1. Q_tilde (int a) z\<^sub>1 z\<^sub>2 z\<^sub>3 z\<^sub>4 z\<^sub>5 z\<^sub>6 z\<^sub>7 z\<^sub>8 z\<^sub>9 z\<^sub>1\<^sub>0 z\<^sub>1\<^sub>1 = 0" by blast
  next
    assume asm2: "\<exists>z\<^sub>1 z\<^sub>2 z\<^sub>3 z\<^sub>4 z\<^sub>5 z\<^sub>6 z\<^sub>7 z\<^sub>8 z\<^sub>9 z\<^sub>1\<^sub>0 z\<^sub>1\<^sub>1. Q_tilde (int a) z\<^sub>1 z\<^sub>2 z\<^sub>3 z\<^sub>4 z\<^sub>5 z\<^sub>6 z\<^sub>7 z\<^sub>8 z\<^sub>9 z\<^sub>1\<^sub>0 z\<^sub>1\<^sub>1 = 0"
    obtain z\<^sub>1 z\<^sub>2 z\<^sub>3 z\<^sub>4 z\<^sub>5 z\<^sub>6 z\<^sub>7 z\<^sub>8 z\<^sub>9 z\<^sub>1\<^sub>0 z\<^sub>1\<^sub>1 where z_prop:
      "Q_tilde (int a) z\<^sub>1 z\<^sub>2 z\<^sub>3 z\<^sub>4 z\<^sub>5 z\<^sub>6 z\<^sub>7 z\<^sub>8 z\<^sub>9 z\<^sub>1\<^sub>0 z\<^sub>1\<^sub>1 = 0" using asm2 by auto

    have cs2_0:
      "(combined_variables.Q P) (int a) z\<^sub>1 z\<^sub>2 z\<^sub>3 z\<^sub>4 z\<^sub>5 z\<^sub>6 z\<^sub>7 z\<^sub>8 (z\<^sub>9^2 + z\<^sub>1\<^sub>0^2 + z\<^sub>1\<^sub>1^2 + z\<^sub>1\<^sub>1) = 0"
      using z_prop Q_tilde_def by simp
    have "z\<^sub>9^2 + z\<^sub>1\<^sub>0^2 + z\<^sub>1\<^sub>1^2 + z\<^sub>1\<^sub>1 \<ge>0" by (meson four_decomposition_int)
    thus cs2:"\<exists>w1 w2 w3 w4 w5 w6 w7 w8 w9. w9 \<ge> 0 \<and>
          (combined_variables.Q P) (int a) w1 w2 w3 w4 w5 w6 w7 w8 w9 = 0" using cs2_0 by blast
  qed

  thus ?thesis
    using theorem_III_new_statement assms by presburger
qed

end 

lemma eleven_unknowns_over_Z_polynomial: 
  fixes A :: "nat set" and P :: "int mpoly"
  assumes "is_diophantine_over_N_with A P"
  shows "a \<in> A = (\<exists>z\<^sub>1 z\<^sub>2 z\<^sub>3 z\<^sub>4 z\<^sub>5 z\<^sub>6 z\<^sub>7 z\<^sub>8 z\<^sub>9 z\<^sub>1\<^sub>0 z\<^sub>1\<^sub>1.
                  insertion ((!) [int a, z\<^sub>1, z\<^sub>2, z\<^sub>3, z\<^sub>4, z\<^sub>5, z\<^sub>6, z\<^sub>7, z\<^sub>8, z\<^sub>9, z\<^sub>1\<^sub>0, z\<^sub>1\<^sub>1]) (Q_tilde_poly P) = 0)"
  unfolding Q_tilde_correct eleven_unknowns_over_Z[of A P a, OF assms(1)] by simp

end