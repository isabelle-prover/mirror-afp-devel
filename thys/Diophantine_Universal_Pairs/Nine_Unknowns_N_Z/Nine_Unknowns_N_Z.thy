theory Nine_Unknowns_N_Z 
  imports "../Coding_Theorem/Coding_Theorem" "../Bridge_Theorem/Bridge_Theorem"
          "../Coding_Theorem/Lemma_2_2" "../Coding_Theorem/Lower_Bounds"
          Nine_Unknowns_N_Z_Definitions Matiyasevich_Polynomial
begin

subsection \<open>Proof of the Nine Unknowns Theorem\<close>

theorem theorem_III_new_statement:
  fixes A :: "nat set"
    and P
  defines "\<phi> a z\<^sub>1 z\<^sub>2 z\<^sub>3 z\<^sub>4 z\<^sub>5 z\<^sub>6 z\<^sub>7 z\<^sub>8 z\<^sub>9 \<equiv> \<lambda>fn. fn (int a) z\<^sub>1 z\<^sub>2 z\<^sub>3 z\<^sub>4 z\<^sub>5 z\<^sub>6 z\<^sub>7 z\<^sub>8 z\<^sub>9"
  assumes "is_diophantine_over_N_with A P"
  shows "a \<in> A = (\<exists>z\<^sub>1 z\<^sub>2 z\<^sub>3 z\<^sub>4 z\<^sub>5 z\<^sub>6 z\<^sub>7 z\<^sub>8 z\<^sub>9. z\<^sub>9 \<ge> 0 \<and>
                  \<phi> a z\<^sub>1 z\<^sub>2 z\<^sub>3 z\<^sub>4 z\<^sub>5 z\<^sub>6 z\<^sub>7 z\<^sub>8 z\<^sub>9 (combined_variables.Q P) = 0)"
    (is "_ = ?Pa_zero")
proof -
  interpret thm3: combined_variables P
    by unfold_locales

  show ?thesis 
proof (rule iffI) (* Indentation is 2 spaces less than usual on purpose! *)  
  assume "a \<in> A"

  then obtain ys\<^sub>0 where ys\<^sub>0_insertion: "insertion (ys\<^sub>0(0 := int a)) P = 0" and 
                        ys\<^sub>0_nonnegative: "is_nonnegative ys\<^sub>0"
    using \<open>is_diophantine_over_N_with A P\<close> unfolding is_diophantine_over_N_with_def by auto

  obtain ys where ys_insertion: "insertion (ys(0 := int a)) (thm3.P\<^sub>1) = 0"
              and ys_nonzero_unknown: "\<exists>i\<in>{1..fresh_var P}. 0 < ys i" 
              and ys_zero: "\<forall>i>fresh_var P. ys i = 0"
              and ys_nonnegative: "is_nonnegative ys"
    unfolding thm3.P\<^sub>1_def
    using suitable_for_coding_exists_positive_unknown[of A P a ys\<^sub>0,
              OF \<open>is_diophantine_over_N_with A P\<close> \<open>a \<in> A\<close> ys\<^sub>0_insertion ys\<^sub>0_nonnegative]
    by auto

  define ys' where "ys' \<equiv> ys(0 := int a)" 

  hence ys': "insertion ys' thm3.P\<^sub>1 = 0"
    using ys_insertion by auto

  have vars_ne: "vars thm3.P\<^sub>1 \<noteq> {}"
    unfolding thm3.P\<^sub>1_def suitable_for_coding_degree_vars
    by auto
  have max_vars_P: "max_vars thm3.P\<^sub>1 = fresh_var P"
    unfolding max_vars_of_nonempty[OF vars_ne] 
    unfolding thm3.P\<^sub>1_def suitable_for_coding_degree_vars
    unfolding fresh_var_def 
    apply simp
    using \<open>max_vars thm3.P\<^sub>1 = Max (vars thm3.P\<^sub>1)\<close> combined_variables.P\<^sub>1_def
      fresh_var_def suitable_for_coding_degree_vars(2) suitable_for_coding_max_vars
    by force

  define ys_max :: int where "ys_max = Max (ys' ` {0..fresh_var P})"
  
  have "ys_max \<ge> 0"
  proof - 
    have "ys_max \<ge> ys' 0"
      unfolding ys_max_def by auto
    thus ?thesis 
      unfolding ys'_def by simp
  qed

  have "ys' i \<le> ys_max" for i
  proof (cases "i \<le> fresh_var P")
    case True
    then show ?thesis
      unfolding ys_max_def ys'_def by auto
  next
    case False
    then show ?thesis
      using ys_zero \<open>ys_max \<ge> 0\<close>
      unfolding ys_max_def ys'_def
      by simp
  qed

  define b\<^sub>0 where "b\<^sub>0 \<equiv> coding_variables.b a"
  have "\<exists>f. f > 0 \<and> is_square (b\<^sub>0 f) \<and> is_power2 (b\<^sub>0 f) \<and> b\<^sub>0 f > ys_max"
    using lemma_2_2_useful
    unfolding b\<^sub>0_def thm3.b_def coding_variables.b_def
    using insertion_mult insertion_add insertion_Var insertion_Const \<open>ys_max \<ge> 0\<close> by auto

  then obtain f where "f > 0" and "is_square (b\<^sub>0 f)" and "is_power2 (b\<^sub>0 f)"
                  and "b\<^sub>0 f > ys_max"
    by auto

interpret coding: coding_theorem thm3.P\<^sub>1 a f
  proof (unfold_locales)
    show "0 \<le> int a" by simp

    show "0 < f"
      using \<open>0 < f\<close> by auto

    show "is_power2 (coding_variables.b (int a) f)"
      using \<open>is_power2 (b\<^sub>0 f)\<close> unfolding b\<^sub>0_def
      unfolding coding_variables.b_def
      by auto

    show "0 < coding_variables.\<delta> thm3.P\<^sub>1"
      unfolding thm3.P\<^sub>1_def coding_variables.\<delta>_def
      using suitable_for_coding_total_degree by auto
  qed

  have p0: "coding.P_coeff (replicate (coding.\<nu> + 1) 0) > 0"
    using suitable_for_coding_coeff0[of P]
    unfolding coding.P_coeff_def thm3.P\<^sub>1_def coding_variables.P_coeff_def
              coding_variables.\<nu>_def
    by simp

  have coding_1: "coding.statement1_strong ys'"
    unfolding coding.statement1_strong_def coding.statement1_weak_def 
  proof (intro conjI allI)
    show "ys' 0 = int a"
      unfolding ys'_def by auto

    show "0 \<le> ys' i" for i
      using ys_nonnegative unfolding is_nonnegative_def ys'_def by auto
    
    show "ys' i < coding.b" for i
      using \<open>b\<^sub>0 f > ys_max\<close> \<open>ys' i \<le> ys_max\<close>
      unfolding b\<^sub>0_def 
      by (auto simp: coding.b_def)

    show "insertion ys' thm3.P\<^sub>1 = 0"
      using ys' by auto 

    show "\<exists>i\<in>{1..coding.\<nu>}. ys' i \<noteq> 0" 
    proof -
      from ys_nonzero_unknown obtain i where "i \<in> {1..fresh_var P}" and ys_i: "ys i > 0" by auto
      hence "ys' i \<noteq> 0" unfolding ys'_def by auto
      thus ?thesis
        using \<open>i \<in> {1..fresh_var P}\<close> \<open>vars thm3.P\<^sub>1 \<noteq> {}\<close>
        unfolding coding.\<nu>_def by (auto simp: max_vars_P)
    qed
  qed

  (* Application of Coding Theorem *)
  hence "\<exists>g. coding.statement2_strong g"
    using coding_theorem.coding_theorem_direct[OF coding.coding_theorem_axioms] by auto
  
  then obtain g :: int where g: "coding.statement2_strong g" by auto

  define b where "b \<equiv> thm3.b a f g 0 0 0 0 0 0 0"
  define X where "X \<equiv> thm3.X a f g 0 0 0 0 0 0 0"
  define Y where "Y \<equiv> thm3.Y a f g 0 0 0 0 0 0 0"

  from g have "g \<ge> b"
    unfolding coding.statement2_strong_def
    unfolding b_def thm3.b_def
    by (auto simp: le_trans coding.b_def)
  from g have "g < coding.\<gamma> * b ^ coding.\<alpha>"
    unfolding coding.statement2_strong_def
    unfolding b_def thm3.b_def
    by (auto simp: le_trans coding.b_def)

  have "is_square b"
    using \<open>is_square (b\<^sub>0 f)\<close>
    unfolding b\<^sub>0_def b_def thm3.b_def
    by auto

  have "is_power2 b"
    using \<open>is_power2 (b\<^sub>0 f)\<close>
    unfolding b\<^sub>0_def b_def thm3.b_def
    by simp

  have 1: "b \<ge> 0"
    using \<open>is_square b\<close> unfolding is_square_def
    by auto

  have "b \<ge> 1"
    using \<open>b\<^sub>0 f > ys_max\<close> \<open>ys_max \<ge> 0\<close>
    unfolding coding.statement1_strong_def b\<^sub>0_def b_def thm3.b_def
    by auto

  have 4: "1 \<le> g"
    using g \<open>b \<ge> 1\<close>
    unfolding coding.statement2_strong_def b_def thm3.b_def 
    by (auto simp: le_trans coding.b_def)
  hence "0 < g" by auto

  (* Application of Bridge Theorem *)
  have "bridge_variables.statement2a b Y X g" 
  proof -
    from \<open>0 < g\<close> have "0 \<le> g" by auto
    have "0 \<le> int a" by auto
    have 2: "b \<le> Y \<and> 2 ^ 8 \<le> Y"
      using coding.lower_bounds[OF \<open>0 \<le> int a\<close> \<open>0 < f\<close> \<open>0 \<le> g\<close> coding.\<delta>_pos p0]
      unfolding b_def Y_def thm3.b_def thm3.Y_def by auto

    have 3: "3 * b \<le> X"
      using coding.lower_bounds[OF \<open>0 \<le> int a\<close> \<open>0 < f\<close> \<open>0 \<le> g\<close> coding.\<delta>_pos p0]
      unfolding b_def X_def thm3.b_def thm3.X_def coding.b_def 
      by (auto simp: coding.b_def)

    have "Y dvd int (2 * nat X choose nat X)" 
    proof - 
      have "coding.Y dvd int (2 * nat (coding.X g) choose nat (coding.X g))"
        using g unfolding coding.statement2_strong_def by auto

      thus ?thesis
        unfolding Y_def thm3.Y_def X_def thm3.X_def by auto 
    qed

    hence statement1: "bridge_variables.statement1 b Y X" 
      unfolding bridge_variables.statement1_def
      using \<open>is_power2 b\<close> by simp

    show ?thesis
      using bridge_variables.theorem_II_1_3[of b Y X g, OF 1 2 3 4 statement1] by auto
  qed

  then obtain h k l w x y where thm2:
    "bridge_variables.d2a l w h x y g Y X \<and>
    bridge_variables.d2b k l w x g Y X \<and>
    bridge_variables.d2c l w h b g Y X \<and>
    bridge_variables.d2e k l w h g Y X \<and>
    b \<le> h \<and> b \<le> k \<and> b \<le> l \<and> b \<le> w \<and> b \<le> x \<and> b \<le> y"
    using bridge_variables.statement2a_def[of b Y X g] by metis

  (* The last slot is for n -- which we will obtain momentarily --,
     but z_0 doesn't actually depend on n *)
  define z\<^sub>0 where "z\<^sub>0 \<equiv> \<lambda>fn. fn (int a) f g h k l w x y (0 :: int) :: int"

  define S where "S \<equiv> z\<^sub>0 thm3.S"
  define T where "T \<equiv> z\<^sub>0 thm3.T"
  define R where "R \<equiv> z\<^sub>0 thm3.R"
  define A\<^sub>1 where "A\<^sub>1 \<equiv> z\<^sub>0 thm3.A\<^sub>1"
  define A\<^sub>2 where "A\<^sub>2 \<equiv> z\<^sub>0 thm3.A\<^sub>2"
  define A\<^sub>3 where "A\<^sub>3 \<equiv> z\<^sub>0 thm3.A\<^sub>3"
  
  define \<gamma>' where
    "\<gamma>' \<equiv> \<lambda>(n :: int) fn. fn A\<^sub>1 A\<^sub>2 A\<^sub>3 S T R n :: int"

  (* Application of the relation combining lemma *)
  have "\<exists>n\<ge>0. \<gamma>' n thm3.M3 = 0"
  proof -
    have thm3_Y: "thm3.Y (int a) f g h k l w x y 0 = Y"
      unfolding thm3.Y_def Y_def ..
    have thm3_X: "thm3.X (int a) f g h k l w x y 0 = X"
      unfolding thm3.X_def X_def ..
    have thm3_b: "thm3.b (int a) f g h k l w x y 0 = b"
      unfolding thm3.b_def b_def ..

    from thm2 have d2a: "bridge_variables.d2a l w h x y g Y X" by simp
    from thm2 have d2b: "bridge_variables.d2b k l w x g Y X" by simp
    from thm2 have d2c: "bridge_variables.d2c l w h b g Y X" by simp
    from thm2 have d2e: "bridge_variables.d2e k l w h g Y X" by simp

    have "S \<noteq> 0"
      unfolding S_def z\<^sub>0_def thm3.S_def bridge_variables.S_def by presburger

    have "S dvd T" 
      using d2c unfolding bridge_variables.d2c_def S_def T_def thm3.S_def thm3.T_def z\<^sub>0_def
      by (simp add: thm3_Y thm3_X thm3_b)

    have "R > 0"
    proof - 
      have "l > 0" using thm2 \<open>b \<ge> 1\<close> by auto
      have "x > 0" using thm2 \<open>b \<ge> 1\<close> by auto

      have "g < thm3.\<mu> (int a) f g h k l w x y 0"
        unfolding thm3.\<mu>_def coding.b_def
        using \<open>g < coding.\<gamma> * b ^ coding.\<alpha>\<close>
        unfolding b_def thm3.b_def .

      show ?thesis 
        using thm3.R_gt_0_necessary_condition[OF \<open>f > 0\<close> \<open>x > 0\<close> \<open>l > 0\<close> \<open>g > 0\<close>
                                                 \<open>g < thm3.\<mu> (int a) f g h k l w x y 0\<close>]
        unfolding R_def z\<^sub>0_def  
        using d2e unfolding X_def Y_def thm3.Y_def thm3.X_def by auto
    qed

    have "is_square A\<^sub>1"
      unfolding A\<^sub>1_def z\<^sub>0_def thm3.A\<^sub>1_def thm3_b 
      using \<open>is_square b\<close>
      by simp
    have "is_square A\<^sub>2"
      unfolding A\<^sub>2_def z\<^sub>0_def thm3.A\<^sub>2_def
      using d2a unfolding bridge_variables.d2a_def thm3.D_def thm3.I_def thm3.F_def
      by (simp add: thm3_Y thm3_X thm3_b)
    have "is_square A\<^sub>3"
      unfolding A\<^sub>3_def z\<^sub>0_def thm3.A\<^sub>3_def
      using d2b unfolding bridge_variables.d2b_def thm3.U_def thm3.V_def thm3.K_def
      by (simp add: thm3_Y thm3_X thm3_b)

    obtain n where n_def: "n\<ge>0 \<and> section5.M3 A\<^sub>1 A\<^sub>2 A\<^sub>3 S T R n = 0"
      using matiyasevich_polynomial.relation_combining[of S T R A\<^sub>1 A\<^sub>2 A\<^sub>3, OF \<open>S \<noteq> 0\<close>]
      using \<open>S dvd T\<close> \<open>R > 0\<close> \<open>is_square A\<^sub>1\<close> \<open>is_square A\<^sub>2\<close> \<open>is_square A\<^sub>3\<close> 
      by auto

    show ?thesis 
      apply (rule exI[of _ n], simp add: n_def)
      unfolding thm3.M3_def \<gamma>'_def apply simp   
      unfolding section5.M3_correct
      by (auto simp: n_def nth0_Cons)
  qed

  then obtain n where insertion_M3: "\<gamma>' n thm3.M3 = 0" and "n\<ge>0"
    by auto

  hence "n \<ge> 0" by auto

  (* Now we can define the final insertion map *)
  define z where "z \<equiv> \<phi> a f g h k l w x y n"

  have insertion_Pa: "z thm3.Q = 0"
  proof -
    have \<gamma>_eq_z_comp_\<sigma>: "\<gamma>' n = z \<circ> thm3.\<sigma>"
      unfolding \<gamma>'_def thm3.\<sigma>_def comp_def z_def \<phi>_def
      unfolding A\<^sub>1_def A\<^sub>2_def A\<^sub>3_def S_def T_def R_def z\<^sub>0_def
      unfolding thm3.A\<^sub>1_def thm3.A\<^sub>2_def thm3.A\<^sub>3_def thm3.S_def thm3.T_def thm3.R_def thm3.m_def
      unfolding thm3.\<mu>_def
      unfolding thm3.L_def thm3.U_def thm3.V_def thm3.A_def thm3.C_def thm3.D_def thm3.F_def 
                thm3.I_def thm3.W_def thm3.K_def
      unfolding thm3.b_def thm3.X_def thm3.Y_def
      ..

    show ?thesis
      unfolding thm3.Q_alt fun_cong[OF \<gamma>_eq_z_comp_\<sigma>[symmetric, unfolded comp_def]]
      using insertion_M3 .
  qed

  show ?Pa_zero 
    using insertion_Pa \<open>n\<ge>0\<close> unfolding z_def by metis
next 
  assume ?Pa_zero

  then obtain f g h k l w x y n where insertion_Q: 
    "\<phi> a f g h k l w x y n thm3.Q = 0" and "n \<ge> 0"
    unfolding thm3.Q_def by auto

  define z where "z \<equiv> \<phi> a f g h k l w x y n"

  define S where "S \<equiv> z thm3.S"
  define T where "T \<equiv> z thm3.T"
  define R where "R \<equiv> z thm3.R"
  define A\<^sub>1 where "A\<^sub>1 \<equiv> z thm3.A\<^sub>1"
  define A\<^sub>2 where "A\<^sub>2 \<equiv> z thm3.A\<^sub>2"
  define A\<^sub>3 where "A\<^sub>3 \<equiv> z thm3.A\<^sub>3"

  (* Application of the relation combining lemma *)
  have "S dvd T" and "0 < R" and "is_square A\<^sub>1" and "is_square A\<^sub>2" and "is_square A\<^sub>3"
  proof - 
    have "S \<noteq> 0"
      unfolding S_def z_def \<phi>_def thm3.S_def bridge_variables.S_def by presburger

    have "section5.M3 A\<^sub>1 A\<^sub>2 A\<^sub>3 S T R n = 0"
      using insertion_Q
      unfolding \<phi>_def thm3.Q_def thm3.M3_def
      apply (simp add: section5.M3_correct nth0_def)
      unfolding A\<^sub>1_def A\<^sub>2_def A\<^sub>3_def S_def T_def R_def z_def \<phi>_def 
      by (auto simp add: thm3.m_def) 

    thus "S dvd T" and "0 < R" and "is_square A\<^sub>1" and "is_square A\<^sub>2" and "is_square A\<^sub>3"
      using matiyasevich_polynomial.relation_combining[of S T R A\<^sub>1 A\<^sub>2 A\<^sub>3, OF \<open>S \<noteq> 0\<close>] \<open>n\<ge>0\<close> 
      unfolding thm3.M3_def \<phi>_def by auto
  qed

  define b where "b \<equiv> thm3.b a f g h k l w x y n"
  define X where "X \<equiv> thm3.X a f g h k l w x y n"
  define Y where "Y \<equiv> thm3.Y a f g h k l w x y n"

  have "b \<ge> 0" 
    using \<open>is_square A\<^sub>1\<close> unfolding A\<^sub>1_def thm3.A\<^sub>1_def thm3.b_def b_def z_def \<phi>_def 
    unfolding is_square_def by auto

  have "thm3.R \<tau> > 0" using \<open>R > 0\<close> unfolding thm3.R_def R_def z_def \<phi>_def by auto
  have "thm3.b \<tau> \<ge> 0" using \<open>b \<ge> 0\<close> unfolding thm3.b_def b_def z_def \<phi>_def by auto

  have "f > 0"
    proof - 
      have "f \<noteq> 0" using \<open>R > 0\<close> unfolding R_def thm3.R_def z_def \<phi>_def by auto

      show ?thesis
      using \<open>b \<ge> 0\<close> unfolding b_def thm3.b_def coding_variables.b_def 
        using \<open>f \<noteq> 0\<close> apply simp
      by (smt (verit) mult_le_cancel_right1 of_nat_less_0_iff)
    qed

  have "g \<ge> 1"
    using thm3.R_gt_0_consequences(1)[OF \<open>thm3.R \<tau> > 0\<close> \<open>thm3.b \<tau> \<ge> 0\<close> \<open>f > 0\<close>] by simp

  have p0: "coding_variables.P_coeff thm3.P\<^sub>1
                (replicate (coding_variables.\<nu> thm3.P\<^sub>1 + 1) 0) > 0"
    using suitable_for_coding_coeff0[of P]
    unfolding thm3.P\<^sub>1_def coding_variables.P_coeff_def coding_variables.\<nu>_def
    by simp

  (* Application of the Bridge Theorem *)
  have "bridge_variables.statement1 b Y X"
  proof - 
    have "g \<ge> 0" using \<open>g \<ge> 1\<close> by auto (* for convenience *)

    have "int a \<ge> 0"
      by auto
    have delta: "coding_variables.\<delta> thm3.P\<^sub>1 > 0"
      by (simp add: suitable_for_coding_total_degree coding_variables.\<delta>_def thm3.P\<^sub>1_def)

    have Y: "b \<le> Y \<and> 2 ^ 8 \<le> Y "
      using coding_variables.lower_bounds(2-3)[OF \<open>int a \<ge> 0\<close> \<open>0 < f\<close> \<open>g \<ge> 0\<close> delta p0]
      unfolding b_def Y_def thm3.b_def thm3.Y_def by auto

    have X: "X \<ge> 3 * b"
      using coding_variables.lower_bounds(1)[OF \<open>int a \<ge> 0\<close> \<open>0 < f\<close> \<open>g \<ge> 0\<close> delta p0]
      unfolding b_def X_def thm3.b_def thm3.X_def by auto

    have "bridge_variables.statement2 b Y X g"
    proof - 
      have "l * x \<noteq> 0"
        using \<open>R > 0\<close> unfolding R_def thm3.R_def z_def \<phi>_def by auto

      have d2a: "bridge_variables.d2a l w h x y g Y X"
        using \<open>is_square A\<^sub>2\<close> 
        unfolding bridge_variables.d2a_def A\<^sub>2_def z_def thm3.A\<^sub>2_def \<phi>_def 
                  thm3.D_def thm3.I_def thm3.F_def Y_def X_def by auto
        
      have d2b: "bridge_variables.d2b k l w x g Y X"
        using \<open>is_square A\<^sub>3\<close> 
        unfolding bridge_variables.d2b_def A\<^sub>3_def z_def thm3.A\<^sub>3_def \<phi>_def
                  thm3.U_def Y_def X_def thm3.V_def thm3.K_def by auto
      
      have d2c: "bridge_variables.d2c l w h b g Y X"
        using \<open>S dvd T\<close> unfolding bridge_variables.d2c_def S_def T_def 
                                  thm3.S_def thm3.T_def z_def \<phi>_def Y_def X_def b_def 
        by auto
      
      have d2f: "bridge_variables.d2f k l w h g Y X"
        using thm3.R_gt_0_consequences(4)[OF \<open>thm3.R \<tau> > 0\<close> \<open>thm3.b \<tau> \<ge> 0\<close> \<open>f > 0\<close>] 
        unfolding X_def Y_def by simp
      
      show ?thesis 
        unfolding bridge_variables.statement2_def
        using \<open>l * x \<noteq> 0\<close> d2a d2b d2c d2f by metis
    qed

    thus ?thesis 
      using bridge_variables.theorem_II_2_1[of b Y X g, OF \<open>b \<ge> 0\<close> Y X \<open>g\<ge>1\<close>] by auto
  qed

  hence "is_power2 b" and Y_dvd: "Y dvd int (2 * nat X choose nat X)"
    unfolding bridge_variables.statement1_def by auto

  interpret coding: coding_theorem thm3.P\<^sub>1 "int a" f
  proof (unfold_locales)
    show "0 \<le> int a" by simp

    show "0 < f" using \<open>f > 0\<close> by auto

    show "is_power2 (coding_variables.b (int a) f)" 
      using \<open>is_power2 b\<close> unfolding b_def thm3.b_def by auto

    show "0 < coding_variables.\<delta> thm3.P\<^sub>1"
      unfolding thm3.P\<^sub>1_def coding_variables.\<delta>_def
      using suitable_for_coding_total_degree by auto
  qed

  have "\<exists>y. coding.statement1_weak y"
  proof - 
    have "0 \<le> g" using \<open>g \<ge> 1\<close> by auto

    have g_bound: "g < 2 * int coding.\<gamma> * coding.b ^ coding.\<alpha>" 
      using thm3.R_gt_0_consequences(2)[OF \<open>thm3.R \<tau> > 0\<close> \<open>thm3.b \<tau> \<ge> 0\<close> \<open>f > 0\<close>] 
      unfolding thm3.\<mu>_def thm3.b_def by auto
      
    have dvd_choose: "coding.Y dvd int (2 * nat (coding.X g) choose nat (coding.X g))"
      using Y_dvd unfolding Y_def X_def thm3.Y_def thm3.X_def by auto

    show ?thesis
      using coding.coding_theorem_reverse[of g] unfolding coding.statement2_weak_def
      using \<open>g\<ge>0\<close> g_bound dvd_choose
      by (metis)
  qed

  then obtain y where y_0: "y 0 = int a"
                  and y_i: "\<forall>i. 0 \<le> y i \<and> y i < coding.b"
                  and insertion_y: "insertion y thm3.P\<^sub>1 = 0"
    unfolding coding.statement1_weak_def by auto

  have "is_nonnegative y"
    using y_i unfolding is_nonnegative_def by auto

  have "insertion (y(0 := int a)) thm3.P\<^sub>1 = 0"
  proof - 
    have y_eq: "(y(0 := int a)) = y"
      using y_0 by auto

    show ?thesis using insertion_y unfolding y_eq by auto
  qed

  hence "\<exists>y\<^sub>0. insertion (y\<^sub>0(0 := int a)) P = 0 \<and> is_nonnegative y\<^sub>0" 
    using suitable_for_coding_diophantine_equivalent \<open>is_nonnegative y\<close>
    unfolding thm3.P\<^sub>1_def by auto 

  thus "a \<in> A"
    using assms(2) unfolding is_diophantine_over_N_with_def by auto
qed

qed

theorem theorem_III:
  fixes A :: "nat set" and P :: "int mpoly"
  assumes "is_diophantine_over_N_with A P"
  shows "a \<in> A = (\<exists>f g h k l w x y n. n \<ge> 0 \<and>
                 insertion ((!) [int a, f, g, h, k, l, w, x, y, n])
                 (combined_variables.Q_poly P) = 0)"
  unfolding combined_variables.Q_correct
  unfolding theorem_III_new_statement[of A P a, OF assms(1)]
  by simp

theorem nine_unknowns_over_Z_and_N: 
  fixes P :: "int mpoly"
  shows "(\<exists>z :: nat \<Rightarrow> int. is_nonnegative z \<and> 
              insertion (z(0 := int a)) P = 0) 
       = (\<exists>f g h k l w x y n. n \<ge> 0 \<and>
              insertion ((!) [int a, f, g, h, k, l, w, x, y, n])
              (combined_variables.Q_poly P) = 0)"
proof - 
  define A where "A \<equiv> {a. \<exists>z. insertion (z(0 := int a)) P = 0 \<and> is_nonnegative z}"

  show ?thesis
    using theorem_III[of A P] unfolding A_def is_diophantine_over_N_with_def 
    by fastforce
qed

end
