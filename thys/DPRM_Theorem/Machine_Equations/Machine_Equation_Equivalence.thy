subsection \<open>Equivalence of register machine and arithmetizing equations\<close>

theory Machine_Equation_Equivalence imports All_Equations
                                            "../Register_Machine/MachineEquations"
                                            "../Register_Machine/MultipleToSingleSteps"

begin

context register_machine
begin

lemma conclusion_4_5: 
  assumes is_val: "is_valid_initial ic p a" 
  and n_def: "n \<equiv> length (snd ic)"
  shows "(\<exists>q. terminates ic p q) = rm_equations a"
proof (rule)
  assume "\<exists>q. terminates ic p q"
  then obtain q::nat where terminates: "terminates ic p q" by auto
  hence "q>0" using terminates_def by auto
  
  have "\<exists>c>1. cells_bounded ic p c"
    using terminate_c_exists terminates is_val is_valid_initial_def by blast
  then obtain c where c: "cells_bounded ic p c \<and> c > 1" by auto
  
  define b where "b \<equiv> B c"
  define d where "d \<equiv> D q c b"
  define e where "e \<equiv> E q b"
  define f where "f \<equiv> F q c b"

  have "c>1" using c by auto

  have "b>1" using c b_def B_def
    using nat_neq_iff by fastforce

  define r where "r \<equiv> RLe ic p b q"
  define s where "s \<equiv> SKe ic p b q"
  define z where "z \<equiv> ZLe ic p b q"

  interpret equations: rm_eq_fixes p n a b c d e f q r z s by unfold_locales
 
  have "equations.mask_equations" 
  proof - 
    have "\<forall>l<n. r l \<preceq> d"
      using lm04_15_register_masking[of "ic" "p" "c" _ "q"] r_def n_def d_def b_def c by auto
    moreover have "\<forall>l<n. z l \<preceq> e"
      using lm04_15_zero_masking z_def n_def e_def b_def c by auto
    moreover have "\<forall>l<n. 2 ^ c * z l = r l + d && f"
      using lm04_20_zero_definition r_def z_def n_def d_def f_def b_def c by auto
    ultimately show ?thesis unfolding equations.mask_equations_def equations.register_mask_def 
      equations.zero_indicator_mask_def equations.zero_indicator_0_or_1_def by auto
  qed

  moreover have "equations.register_equations" 
  proof - 
    have "r 0 = a + b * r 0 + b * \<Sum>R+ p 0 s - b * \<Sum>R- p 0 (\<lambda>k. s k && z 0)"
      using lm04_23_multiple_register1[of "ic" "p" "a" "c" "0" "q"] is_val c terminates `q>0` r_def 
            s_def z_def b_def bitAND_commutes by auto
    moreover have "\<forall>l>0. l < n \<longrightarrow> r l = b * r l + b * \<Sum>R+ p l s - b * \<Sum>R- p l (\<lambda>k. s k && z l)"
      using lm04_22_multiple_register[of "ic" "p" "a" "c" _ "q"]
            b_def c terminates r_def s_def z_def is_val bitAND_commutes n_def `q>0` by auto
    moreover have "l<n \<Longrightarrow> r l < b^q" for l
      proof -
        assume "l<n"
        hence Rlq: "R ic p l q = 0" 
          using terminates terminates_def correct_halt_def R_def n_def by auto
        have c_ineq: "(2::nat)^c \<le> 2 ^ Suc c - Suc 0" using `c>1` by auto
        have "\<forall>t. R ic p l t < 2 ^ c" using c `l<n` n_def by auto
        hence R_bound: " \<forall>t. R ic p l t < 2 ^ Suc c - Suc 0" using c_ineq
          by (metis dual_order.strict_trans linorder_neqE_nat not_less)
        have "(\<Sum>t = 0..q. b ^ t * R ic p l t) = (\<Sum>t = 0..(Suc (q-1)). b ^ t * R ic p l t)"
          using `q>0` by auto
        also have "... = (\<Sum>t = 0..q-1. b ^ t * R ic p l t) + b^q * R ic p l q"
          using Set_Interval.comm_monoid_add_class.sum.atLeast0_atMost_Suc[of _ "q-1"] `q>0` by auto
        also have "... = (\<Sum>t = 0..q-1. b ^ t * R ic p l t)" using Rlq by auto
        also have "... < b ^ q" using b_def R_bound
           base_summation_bound[of "R ic p l" "c" "q-1"] `q>0` by (auto simp: mult.commute)
        finally show ?thesis using r_def RLe_def by auto
      qed
    ultimately show ?thesis unfolding equations.register_equations_def equations.register_0_def
      equations.register_l_def equations.register_bound_def by auto
  qed

  moreover have "equations.state_equations"
  proof - 
    have "equations.state_relations_from_recursion"
    proof -
      have "\<forall>d>0. d\<le>m \<longrightarrow> s d = b*\<Sum>S+ p d (\<lambda>k. s k) + b*\<Sum>S- p d (\<lambda>k. s k && z (modifies (p!k)))
                              + b*\<Sum>S0 p d (\<lambda>k. s k && (e - z (modifies (p!k))))"
        apply (auto simp: s_def z_def)
        using lm04_24_multiple_step_states[of "ic" "p" "a" "c" _ "q"]
              b_def c terminates s_def z_def is_val bitAND_commutes m_def `q>0` e_def E_def by auto
      moreover have "s 0 = 1 + b*\<Sum>S+ p 0 (\<lambda>k. s k) + b*\<Sum>S- p 0 (\<lambda>k. s k && z (modifies (p!k)))
                             + b*\<Sum>S0 p 0 (\<lambda>k. s k && (e - z (modifies (p!k))))"
        using lm04_25_multiple_step_state1[of "ic" "p" "a" "c" _ "q"]
              b_def c terminates s_def z_def is_val bitAND_commutes m_def `q>0` e_def E_def by auto
      ultimately show ?thesis unfolding equations.state_relations_from_recursion_def 
        equations.state_0_def equations.state_d_def equations.state_m_def by auto
    qed

    moreover have "equations.state_unique_equations"
    proof - 
      have "k<m \<longrightarrow> s k < b ^ q" for k
        using state_q_bound is_val terminates \<open>q>0\<close> b_def s_def m_def c by auto
      moreover have "k\<le>m \<longrightarrow> s k \<preceq> e" for k
        using state_mask is_val terminates \<open>q>0\<close> b_def e_def s_def c by auto
      ultimately show ?thesis unfolding equations.state_unique_equations_def 
        equations.state_mask_def equations.state_bound_def by auto
    qed

    moreover have "\<forall>M\<le>m. sum s {..M} \<preceq> e"
      using state_sum_mask is_val terminates \<open>q>0\<close> b_def e_def s_def c `b>1` m_def by auto

    moreover have "s m = b^q"
        using halting_condition_04_27[of "ic" "p" "a" "q" "c"] m_def b_def is_val `q>0` terminates 
              s_def by auto

    ultimately show ?thesis unfolding equations.state_equations_def 
      equations.state_partial_sum_mask_def equations.state_m_def by auto 
  qed

  moreover have "equations.constants_equations"
    unfolding equations.constants_equations_def equations.constant_b_def 
    equations.constant_d_def equations.constant_e_def equations.constant_f_def
    using b_def d_def e_def f_def by auto

  moreover have "equations.miscellaneous_equations"
  proof - 
    have tapelength: "length (snd ic) > 0" 
      using is_val is_valid_initial_def[of "ic" "p" "a"] by auto
    have "R ic p 0 0 = a" using is_val is_valid_initial_def[of "ic" "p" "a"]
      R_def List.hd_conv_nth[of "snd ic"] by auto
    moreover have "R ic p 0 0 < 2^c" using c tapelength by auto
    ultimately have "a < 2^c" by auto
    thus ?thesis unfolding equations.miscellaneous_equations_def equations.c_gt_0_def 
      equations.a_bound_def equations.q_gt_0_def
    using \<open>q > 0\<close> \<open>c > 1\<close> by auto
  qed

  ultimately show "rm_equations a" unfolding rm_equations_def all_equations_def by blast
next
  assume "rm_equations a"

  then obtain q b c d e f r z s where
    reg: "rm_eq_fixes.register_equations p n a b q r z s" and
    state: "rm_eq_fixes.state_equations p b e q z s" and
    mask: "rm_eq_fixes.mask_equations n c d e f r z" and
    const: "rm_eq_fixes.constants_equations b c d e f q" and
    misc: "rm_eq_fixes.miscellaneous_equations a c q"
    unfolding rm_equations_def all_equations_def by auto

  have fx: "rm_eq_fixes p n"
    unfolding rm_eq_fixes_def using local.register_machine_axioms by auto

  have "q>0" using misc fx rm_eq_fixes.miscellaneous_equations_def 
    rm_eq_fixes.q_gt_0_def by auto
  have "b>1" using B_def const rm_eq_fixes.constants_equations_def
    rm_eq_fixes.constant_b_def fx 
    by (metis One_nat_def Zero_not_Suc less_one n_not_Suc_n nat_neq_iff nat_power_eq_Suc_0_iff 
        numeral_2_eq_2 of_nat_0 of_nat_power_eq_of_nat_cancel_iff of_nat_zero_less_power_iff pos2)
  have "n>0" using is_val is_valid_initial_def[of "ic" "p" "a"] n_def by auto
  have "m>0" using m_def is_val is_valid_initial_def[of "ic" "p"] is_valid_def[of "ic" "p"] by auto

  define Seq where "Seq \<equiv> (\<lambda>k t. nth_digit (s k) t b)"
  define Req where "Req \<equiv> (\<lambda>l t. nth_digit (r l) t b)"
  define Zeq where "Zeq \<equiv> (\<lambda>l t. nth_digit (z l) t b)"

  (* Quick and dirty: :\<acute>|  *)
  have mask_old: "mask_equations n r z c d e f" and
       reg_old: "reg_equations p r z s b a (length (snd ic)) q" and
       state_old: "state_equations p s z b e q (length p - 1)" and 
       const_old: "rm_constants q c b d e f a"
    subgoal 
      using mask rm_eq_fixes.mask_equations_def rm_eq_fixes.register_mask_def fx
      mask_equations_def rm_eq_fixes.zero_indicator_0_or_1_def rm_eq_fixes.zero_indicator_mask_def
      by simp
    subgoal 
      using reg state mask const misc using rm_eq_fixes.register_equations_def
      rm_eq_fixes.register_0_def rm_eq_fixes.register_l_def rm_eq_fixes.register_bound_def
      reg_equations_def n_def fx by simp
    subgoal 
      using state fx state_equations_def rm_eq_fixes.state_equations_def
      rm_eq_fixes.state_relations_from_recursion_def rm_eq_fixes.state_0_def rm_eq_fixes.state_m_def
      rm_eq_fixes.state_d_def rm_eq_fixes.state_unique_equations_def rm_eq_fixes.state_mask_def
      rm_eq_fixes.state_bound_def rm_eq_fixes.state_partial_sum_mask_def m_def by simp
    subgoal unfolding rm_constants_def
      using const misc fx rm_eq_fixes.constants_equations_def 
      rm_eq_fixes.miscellaneous_equations_def rm_eq_fixes.constant_b_def rm_eq_fixes.constant_d_def
      rm_eq_fixes.constant_e_def rm_eq_fixes.constant_f_def rm_eq_fixes.c_gt_0_def 
      rm_eq_fixes.q_gt_0_def rm_eq_fixes.a_bound_def by simp
    done

  hence RZS_eq: "l<n \<Longrightarrow> j\<le>m \<Longrightarrow> t\<le>q \<Longrightarrow>
                R ic p l t = Req l t \<and> Z ic p l t = Zeq l t \<and> S ic p j t = Seq j t" for l j t
    using rzs_eq[of "m" "p" "n" "ic" "a" "r" "z"] mask_old reg_old state_old const_old
          m_def n_def is_val `q>0` Seq_def Req_def Zeq_def by auto

  have R_eq: "l<n \<Longrightarrow> t\<le>q \<Longrightarrow> R ic p l t = Req l t" for l t using RZS_eq by auto
  have Z_eq: "l<n \<Longrightarrow> t\<le>q \<Longrightarrow> Z ic p l t = Zeq l t" for l t using RZS_eq by auto
  have S_eq: "j\<le>m \<Longrightarrow> t\<le>q \<Longrightarrow> S ic p j t = Seq j t" for j t using RZS_eq[of "0"] `n>0` by auto

  have  "ishalt (p!m)" using m_def is_val
        is_valid_initial_def[of "ic" "p" "a"] is_valid_def[of "ic" "p"] by auto
  have "Seq m q = 1" using state nth_digit_def Seq_def `b>1` 
    using fx rm_eq_fixes.state_equations_def
             rm_eq_fixes.state_relations_from_recursion_def
             rm_eq_fixes.state_m_def by auto
  hence "S ic p m q = 1" using S_eq by auto
  hence "fst (steps ic p q) = m" using S_def by(cases "fst (steps ic p q) = m"; auto)
  hence qhalt: "ishalt (p ! (fst (steps ic p q)))" using S_def `ishalt (p!m)` by auto

  hence rempty: "snd (steps ic p q) ! l = 0" if "l < n" for l
    unfolding R_def[symmetric] 
    using R_eq[of l q] \<open>l < n\<close> apply auto
    using reg Req_def nth_digit_def  
    using rm_eq_fixes.register_equations_def
          rm_eq_fixes.register_l_def 
          rm_eq_fixes.register_0_def
          rm_eq_fixes.register_bound_def
    by auto (simp add: fx)

  have state_m_0: "t<q \<Longrightarrow> S ic p m t = 0" for t
    proof -
      assume "t<q"
      have "b ^ q div b ^ t = b^(q-t)"
        by (metis \<open>1 < b\<close> \<open>t < q\<close> less_imp_le not_one_le_zero power_diff)
      also have "... mod b = 0" using \<open>1 < b\<close> \<open>t < q\<close> by simp
      finally have mod: "b^q div b^t mod b = 0" by auto
      have "s m = b^q" using state fx rm_eq_fixes.state_equations_def
        rm_eq_fixes.state_m_def 
        rm_eq_fixes.state_relations_from_recursion_def by auto
      hence "Seq m t = 0" using Seq_def nth_digit_def mod by auto
      with S_eq `t < q` show ?thesis by auto
    qed
  have "\<forall>k<m. \<not> ishalt (p!k)"
    using is_val is_valid_initial_def[of "ic" "p" "a"] is_valid_def[of "ic" "p"] m_def by auto
  moreover have "t<q \<longrightarrow> fst (steps ic p t) < length p - 1" for t
    proof (rule ccontr)
      assume asm: "\<not> (t < q \<longrightarrow> fst (steps ic p t) < length p - 1)"
      hence "t<q" by auto
      with asm have "fst (steps ic p t) \<ge> length p - 1" by auto
      moreover have "fst (steps ic p t) \<le> length p - 1"
        using p_contains[of "ic" "p" "a" "t"] is_val by auto
      ultimately have "fst (steps ic p t) = m" using m_def by auto
      hence "S ic p m t = 1" using S_def by auto
      thus "False" using state_m_0[of "t"] `t<q` by auto
    qed
  ultimately have "t<q \<longrightarrow> \<not> ishalt (p ! (fst (steps ic p t)))" for t using m_def by auto
  hence no_early_halt: "t<q \<longrightarrow> \<not> ishalt (p ! (fst (steps ic p t)))" for t using state_m_0 by auto

  have "correct_halt ic p q" using qhalt rempty correct_halt_def n_def by auto
  thus "(\<exists>q. terminates ic p q)" using no_early_halt terminates_def `q>0` by auto
qed

end

end