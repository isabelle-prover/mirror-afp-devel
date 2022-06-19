subsection \<open>Multiple step relations\<close>

subsubsection \<open>Registers\<close>

theory MultipleStepRegister
  imports SingleStepRegister
begin

lemma lm04_22_multiple_register:
  fixes c :: nat
    and l :: register
    and ic :: configuration
    and p :: program
    and q :: nat
    and a :: nat

  defines "b == B c"
      and "m == length p"
      and "n == length (snd ic)"

assumes is_val: "is_valid_initial ic p a"
assumes c_gt_cells: "cells_bounded ic p c"
assumes l: "l < n"
and "0 < l"
and q: "q > 0"

assumes terminate: "terminates ic p q"

assumes c: "c > 1"

  defines "r == RLe ic p b q"
      and "z == ZLe ic p b q"
      and "s == SKe ic p b q"

shows "r l = b * r l
           + b * (\<Sum>R+ p l s)
           - b * (\<Sum>R- p l (\<lambda>k. z l && s k))"
proof -
  have 0: "snd ic ! l = 0" using assms(4, 7) by (cases "ic"; auto simp add: is_valid_initial_def)

  have "b^(Suc t) * (\<Sum>R- p l (\<lambda>k. (Z ic p l t) * S ic p k t)) \<le> b^(Suc t) *  R ic p l t " for t
     proof (cases "t=0")
       case True
       hence "R ic p l 0 = 0" by (auto simp add: 0 R_def)
       thus ?thesis by (auto simp add: True Z_def sum_rsub.simps)
     next
       case False
       define cs where "cs \<equiv> fst (steps ic p t)"
       have sub: "(\<Sum>R- p l (\<lambda>k. Z ic p l t * S ic p k t))
        = (if issub (p!cs) \<and> l = modifies (p!cs) then Z ic p l t else 0)"
         using single_step_sub Z_def R_def is_val l n_def cs_def by auto
       show ?thesis using sub by (auto simp add: sum_rsub.simps R_def Z_def)
     qed

    from this have positive: "b^(Suc t) * (\<Sum>R- p l (\<lambda>k. (Z ic p l t) * S ic p k t))
                    \<le> b^(Suc t) *  R ic p l t
                    + b^(Suc t) * (\<Sum>R+ p l (\<lambda>k. S ic p k t))" for t
      by (auto simp add: Nat.trans_le_add1)

  have commute_add: "(\<Sum>t=0..q-1. \<Sum>R+ p l (\<lambda>k. b^t * S ic p k t))
      = \<Sum>R+ p l (\<lambda>k. \<Sum>t=0..q-1. (b^t * S ic p k t))"
    using sum_radd_commutative[of "p" "l" "\<lambda>k t. b^t * S ic p k t " "q-1"] by auto

  have r_q: "l<n \<longrightarrow> R ic p l q = 0"
    using terminate terminates_def correct_halt_def by (auto simp: n_def R_def)
  hence z_q: "l<n \<longrightarrow> Z ic p l q = 0"
    using terminate terminates_def correct_halt_def by (auto simp: Z_def)
  have "\<forall>k<length p-1. \<not> ishalt (p!k)"
    using is_val is_valid_initial_def[of "ic" "p" "a"] is_valid_def[of "ic" "p"]
          program_includes_halt.simps by blast
  hence s_q: "\<forall>k < length p - 1. S ic p k q = 0"
    using terminate terminates_def correct_halt_def S_def by auto

  from r_q have rq: "(\<Sum>x = 0..q - 1. int b ^ x * int (snd (steps ic p x) ! l)) =
                     (\<Sum>x = 0..q. int b ^ x * int (snd (steps ic p x) ! l))"
    by (auto simp: r_q R_def l;
        smt Suc_pred mult_0_right of_nat_0 of_nat_mult power_mult_distrib q sum.atLeast0_atMost_Suc zero_power)

  have "(\<Sum>t = 0..q - 1. b ^ t * (Z ic p l t * S ic p k t))
              + (b^(Suc (q-1)) * (Z ic p l (Suc (q-1)) * S ic p k (Suc (q-1))))
              = (\<Sum>t = 0..Suc (q-1). b ^ t * (Z ic p l t * S ic p k t)) " for k
    using comm_monoid_add_class.sum.atLeast0_atMost_Suc by auto
  hence zq: "(\<Sum>t = 0..q - 1. b ^ t * (Z ic p l t * S ic p k t))
              = (\<Sum>t = 0..q. b ^ t * (Z ic p l t * S ic p k t)) " for k
    using z_q q l by auto

  have "(if isadd (p ! k) \<and> l = modifies (p ! k) then \<Sum>t = 0..q - Suc 0. b ^ t * S ic p k t else 0)
      = (if isadd (p ! k) \<and> l = modifies (p ! k) then \<Sum>t = 0..q. b ^ t * S ic p k t else 0)" for k
    proof (cases "p!k")
      case (Add x11 x12)
      have sep: "(\<Sum>t = 0..q-1. b ^ t * S ic p k t) + b^q * S ic p k q 
               = (\<Sum>t = 0..(Suc (q-1)). b ^ t * S ic p k t)"
        using comm_monoid_add_class.sum.atLeast0_atMost_Suc[of "\<lambda>t. b^t * S ic p k t" "q-1"] q
        by auto
      have "ishalt (p ! (fst (steps ic p q)))"
        using terminates_halt_state[of "ic" "p"] is_val terminate by auto
      hence "S ic p k q = 0" using Add S_def[of "ic" "p" "k" "q"] by auto
      with sep q have "(\<Sum>t = 0..q - Suc 0. b ^ t * S ic p k t) = (\<Sum>t = 0..q. b ^ t * S ic p k t)"
        by auto
      thus ?thesis by auto
    next
      case (Sub x21 x22 x23)
      then show ?thesis by auto
    next
      case Halt
      then show ?thesis by auto
    qed

    hence add_q: "\<Sum>R+ p l (\<lambda>k. \<Sum>t=0..(q-1). b^t * S ic p k t) 
                = \<Sum>R+ p l (\<lambda>k. \<Sum>t=0..q. b^t * S ic p k t)"
    using sum_radd.simps single_step_add[of "ic" "p" "a" "l" "snd ic"] is_val l n_def by auto

  (* Start *)
  have "r l = (\<Sum>t = 0..q. b^t * R ic p l t)" using r_def RLe_def by auto
  also have "... = R ic p l 0 + (\<Sum>t = 1..q. b^t * R ic p l t)"
    by (auto simp: q comm_monoid_add_class.sum.atLeast_Suc_atMost)
  also have "... = (\<Sum>t \<in> {1..q}. b^t * R ic p l t)"
    by (simp add: R_def 0)
  also have "... = (\<Sum>t \<in> (Suc ` {0..(q-1)}). b^t * R ic p l t)" using q by auto
  also have "... = (sum  ((\<lambda>t. b^t * R ic p l t) \<circ> Suc)) {0..(q-1)}"
    using comm_monoid_add_class.sum.reindex[of "Suc" "{0..(q-1)}" "(\<lambda>t. b^t * R ic p l t)"] by auto
  also have "... = (\<Sum>t = 0..(q-1). b^(Suc t) *(R ic p l t
                                              + (\<Sum>R+ p l (\<lambda>k. S ic p k t))
                                              - (\<Sum>R- p l (\<lambda>k. (Z ic p l t) * S ic p k t))))"
    using lm04_06_one_step_relation_register[of "ic" "p" "a" "l"] is_val l
    by (simp add: n_def m_def)

  also have "... = (\<Sum>t \<in> {0..(q-1)}. b^(Suc t) *  R ic p l t
                                + b^(Suc t) * (\<Sum>R+ p l (\<lambda>k. S ic p k t))
                                - b^(Suc t) * (\<Sum>R- p l (\<lambda>k. (Z ic p l t) * S ic p k t)))"
    by (auto simp add: algebra_simps)

  finally have "int (r l) = (\<Sum>t \<in> {0..(q-1)}. int(
                                  b^(Suc t) *  R ic p l t
                                + b^(Suc t) * (\<Sum>R+ p l (\<lambda>k. S ic p k t))
                                - b^(Suc t) * (\<Sum>R- p l (\<lambda>k. (Z ic p l t) * S ic p k t))))"
    by auto

  also have "... = (\<Sum>t \<in> {0..(q-1)}. int (b^(Suc t) *  R ic p l t)
                                + int (b^(Suc t) * (\<Sum>R+ p l (\<lambda>k. S ic p k t)))
                                - int (b^(Suc t) * (\<Sum>R- p l (\<lambda>k. (Z ic p l t) * S ic p k t))))"
    by (simp only: sum_int positive)

  also have "... = (\<Sum>t \<in> {0..(q-1)}. int (b^(Suc t) *  R ic p l t)
                                + (int (b^(Suc t) * (\<Sum>R+ p l (\<lambda>k. S ic p k t)))
                                -  int (b^(Suc t) * (\<Sum>R- p l (\<lambda>k. (Z ic p l t) * S ic p k t)))))"
    by (simp add: add_diff_eq)

  also have "... = (\<Sum>t \<in> {0..(q-1)}. int( b^(Suc t) *  R ic p l t ))
             + (\<Sum>t \<in> {0..(q-1)}. int( b^(Suc t) * (\<Sum>R+ p l (\<lambda>k. S ic p k t)))
                                - int( b^(Suc t) * (\<Sum>R- p l (\<lambda>k. (Z ic p l t) * S ic p k t ))))"
    by (auto simp only: sum.distrib)

  also have "... = int b * int (\<Sum>t \<in> {0..(q-1)}. b^t *  R ic p l t )
             + int b * (\<Sum>t \<in> {0..(q-1)}. int(b^t * (\<Sum>R+ p l (\<lambda>k. S ic p k t)))
                                        - int(b^t * (\<Sum>R- p l (\<lambda>k. (Z ic p l t) * S ic p k t ))))"
    by (auto simp: sum_distrib_left mult.assoc right_diff_distrib)

  also have "... = int b * int (\<Sum>t \<in> {0..(q-1)}. b^t *  R ic p l t )
             + int b * (\<Sum>t \<in> {0..(q-1)}. int(b^t * (\<Sum>R+ p l (\<lambda>k. S ic p k t))))
             - int b * (\<Sum>t \<in> {0..(q-1)}. int(b^t * (\<Sum>R- p l (\<lambda>k. (Z ic p l t) * S ic p k t))))"
    by (auto simp add: sum.distrib int_distrib(4) sum_subtractf)

  also have "... = int b * int (\<Sum>t \<in> {0..(q-1)}. b^t *  R ic p l t )
             + int b * (\<Sum>t \<in> {0..(q-1)}. int(\<Sum>R+ p l (\<lambda>k. b^t * S ic p k t)))
             - int b * (\<Sum>t \<in> {0..(q-1)}. int(\<Sum>R- p l (\<lambda>k. b^t * (Z ic p l t * S ic p k t))))"
    using sum_radd_distrib sum_rsub_distrib by auto

  also have "... = int b * int (\<Sum>t = 0..q-1. b^t *  R ic p l t)
             + int b * int (\<Sum>t = 0..q-1. \<Sum>R+ p l (\<lambda>k. b^t * S ic p k t))
             - int b * int (\<Sum>t = 0..q-1. \<Sum>R- p l (\<lambda>k. b^t * (Z ic p l t * S ic p k t)))"
    by auto

  also have "... = int b * int (\<Sum>t = 0..q-1. b^t * R ic p l t)
             + int b * int (\<Sum>R+ p l (\<lambda>k. \<Sum>t=0..q-1. b^t * S ic p k t))
            - int b * int (\<Sum>R- p l (\<lambda>k. \<Sum>t=0..q-1. b^t * (Z ic p l t * S ic p k t)))"
    using sum_rsub_commutative[of "p" "l" "\<lambda>k t. b^t * (Z ic p l t * S ic p k t)" "q-1"]
    using sum_radd_commutative[of "p" "l" "\<lambda>k t. b^t * S ic p k t " "q-1"] by auto

  (* extend all sums until q, because values don't change at time q *)
  also have "... = int b * int (\<Sum>t=0..q. b^t * R ic p l t)
             + int b * int (\<Sum>R+ p l (\<lambda>k. \<Sum>t=0..q-1. b^t * S ic p k t))
             - int b * int (\<Sum>R- p l (\<lambda>k. \<Sum>t=0..q-1. b^t * (Z ic p l t * S ic p k t)))"
    by (auto simp: rq R_def; smt One_nat_def rq)

  also have "... = int b * int (\<Sum>t=0..q. b^t * R ic p l t)
             + int b * int (\<Sum>R+ p l (\<lambda>k. \<Sum>t=0..q. b^t * S ic p k t))
             - int b * int (\<Sum>R- p l (\<lambda>k. \<Sum>t=0..q. b^t * (Z ic p l t * S ic p k t)))"
    using zq add_q by auto

  also have "... = int b * int (RLe ic p b q l)
             + int b * int (\<Sum>R+ p l (SKe ic p b q))
             - int b * int (\<Sum>R- p l (\<lambda>k. \<Sum>t=0..q. b^t * (Z ic p l t * S ic p k t)))"
    by (auto simp: RLe_def; metis SKe_def)

  (* prove multiplication turns into bitAND *)
  also have "... = int b * int (RLe ic p b q l)
             + int b * int (\<Sum>R+ p l (SKe ic p b q))
             - int b * int (\<Sum>R- p l (\<lambda>k. ZLe ic p b q l && SKe ic p b q k))"
    using mult_to_bitAND c_gt_cells b_def c by auto

  finally have "int(r l) = int b * int (r l)
             + int b * int (\<Sum>R+ p l s)
             - int b * int (\<Sum>R- p l (\<lambda>k. z l && s k))"
    by (auto simp: r_def s_def z_def)

  hence "r l = b * r l
             + b * \<Sum>R+ p l s
             - b * \<Sum>R- p l (\<lambda>k. z l && s k)"
    using int_ops(5) int_ops(7) nat_int nat_minus_as_int by presburger

  thus ?thesis by simp
qed

lemma lm04_23_multiple_register1:
  fixes c :: nat
    and l :: register
    and ic :: configuration
    and p :: program
    and q :: nat
    and a :: nat

  defines "b == B c"
      and "m == length p"
      and "n == length (snd ic)"

assumes is_val: "is_valid_initial ic p a"
assumes c_gt_cells: "cells_bounded ic p c"
assumes l: "l = 0"
and q: "q > 0"

assumes c: "c > 1"

 assumes terminate: "terminates ic p q"

  defines "r == RLe ic p b q"
      and "z == ZLe ic p b q"
      and "s == SKe ic p b q"

shows "r l = a + b * r l
           + b * (\<Sum>R+ p l s)
           - b * (\<Sum>R- p l (\<lambda>k. z l && s k))"
proof -
  have n: "n > 0" using is_val
    by (auto simp add: is_valid_initial_def n_def)

  have 0: "snd ic ! l = a" 
    using assms by (cases "ic"; auto simp add: is_valid_initial_def List.hd_conv_nth)

  find_theorems "hd ?l = ?l ! 0"

  have bound_fst_ic: "(if fst ic \<le> length p-1 then 1 else 0) \<le> Suc 0" by auto
  have "(if issub (p ! k) \<and> l = modifies (p ! k) then if fst ic = k then 1 else 0 else 0)
      = (if k = fst ic \<and> issub (p ! k) \<and> l = modifies (p ! k) then 1 else 0)" for k by auto
  hence "(if issub (p ! k) \<and> l = modifies (p ! k) then if fst ic = k then Suc 0 else 0 else 0)
             \<le> (if k = fst ic then 1 else 0)" for k
    apply (cases "p!k")
    apply (cases "modifies (p!k)")
    by auto
  hence sub: " (\<Sum>k = 0..length p-1. if issub (p ! k) \<and> l = modifies (p ! k)
           then if fst ic = k then Suc 0 else 0 else 0) \<le> Suc 0"
    using Groups_Big.ordered_comm_monoid_add_class.sum_mono[of "{0..length p-1}"
       "\<lambda>k. (if issub (p ! k) \<and> l = modifies (p ! k) then if fst ic = k then Suc 0 else 0 else 0)"
       "\<lambda>k. (if k = fst ic then 1 else 0)"] bound_fst_ic Orderings.ord_class.ord_eq_le_trans by auto

  have "b^(Suc t) * (\<Sum>R- p l (\<lambda>k. (Z ic p l t) * S ic p k t)) \<le> b^(Suc t) *  R ic p l t " for t
     proof (cases "t=0")
       case True
       hence "a = R ic p l 0" by (auto simp add: 0 R_def)
       thus ?thesis
         apply (cases "a=0")
         subgoal by (auto simp add: True R_def Z_def sum_rsub.simps)
         subgoal
           apply (auto simp add: True R_def Z_def sum_rsub.simps S_def)
           using sub by auto
         done
     next
       case False
       define cs where "cs \<equiv> fst (steps ic p t)"
       have sub: "(\<Sum>R- p l (\<lambda>k. Z ic p l t * S ic p k t))
        = (if issub (p!cs) \<and> l = modifies (p!cs) then Z ic p l t else 0)"
         using single_step_sub Z_def R_def is_val l n_def cs_def n by auto
       show ?thesis using sub by (auto simp add: sum_rsub.simps R_def Z_def)
     qed

    from this have positive: "b^(Suc t) * (\<Sum>R- p l (\<lambda>k. (Z ic p l t) * S ic p k t))
                    \<le> b^(Suc t) *  R ic p l t
                    + b^(Suc t) * (\<Sum>R+ p l (\<lambda>k. S ic p k t))" for t
      by (auto simp add: Nat.trans_le_add1)

  have distrib_add: "\<And>t. b^t * \<Sum>R+ p l (\<lambda>k. S ic p k t) = \<Sum>R+ p l (\<lambda>k. b ^ t * S ic p k t)"
    by (simp add: sum_radd_distrib)
  have distrib_sub: "\<And>t. b^t * \<Sum>R- p l (\<lambda>k. Z ic p l t * S ic p k t)
                     = \<Sum>R- p l (\<lambda>k. b ^ t * (Z ic p l t * S ic p k t))"
    by (simp add: sum_rsub_distrib)

  have commute_add: "(\<Sum>t=0..q-1. \<Sum>R+ p l (\<lambda>k. b^t * S ic p k t))
      = \<Sum>R+ p l (\<lambda>k. \<Sum>t=0..q-1. (b^t * S ic p k t))"
    using sum_radd_commutative[of "p" "l" "\<lambda>k t. b^t * S ic p k t " "q-1"] by auto

  have "length (snd ic) > 0" using is_val is_valid_initial_def[of "ic" "p" "a"] by auto
  hence r_q: "R ic p l q = 0"
    using terminate terminates_def correct_halt_def l by (auto simp: n_def R_def)
  hence z_q: "Z ic p l q = 0"
    using terminate by (auto simp: Z_def)

  have "\<forall>k<length p-1. \<not> ishalt (p!k)"
    using is_val is_valid_initial_def[of "ic" "p" "a"] is_valid_def[of "ic" "p"]
          program_includes_halt.simps by blast
  hence s_q: "\<forall>k < length p - 1. S ic p k q = 0"
    using terminate terminates_def correct_halt_def by (auto simp: S_def)

  from r_q have rq: "(\<Sum>x = 0..q - 1. int b ^ x * int (snd (steps ic p x) ! l)) =
                     (\<Sum>x = 0..q. int b ^ x * int (snd (steps ic p x) ! l))"
    by (auto simp: r_q R_def; smt Suc_pred mult_0_right of_nat_0 of_nat_mult power_mult_distrib q 
        sum.atLeast0_atMost_Suc zero_power)

  have "(\<Sum>t = 0..q - 1. b ^ t * (Z ic p l t * S ic p k t))
              + (b^(Suc (q-1)) * (Z ic p l (Suc (q-1)) * S ic p k (Suc (q-1))))
              = (\<Sum>t = 0..Suc (q-1). b ^ t * (Z ic p l t * S ic p k t)) " for k
    using comm_monoid_add_class.sum.atLeast0_atMost_Suc by auto
  hence zq: "(\<Sum>t = 0..q - 1. b ^ t * (Z ic p l t * S ic p k t))
              = (\<Sum>t = 0..q. b ^ t * (Z ic p l t * S ic p k t)) " for k
    using z_q q by auto

  have "(if isadd (p ! k) \<and> l = modifies (p ! k) then \<Sum>t = 0..q - Suc 0. b ^ t * S ic p k t else 0)
      = (if isadd (p ! k) \<and> l = modifies (p ! k) then \<Sum>t = 0..q. b ^ t * S ic p k t else 0)" for k
    proof (cases "p!k")
      case (Add x11 x12)
      have sep: "(\<Sum>t = 0..q-1. b ^ t * S ic p k t) + b^q * S ic p k q 
               = (\<Sum>t = 0..(Suc (q-1)). b ^ t * S ic p k t)"
        using comm_monoid_add_class.sum.atLeast0_atMost_Suc[of "\<lambda>t. b^t * S ic p k t" "q-1"] q
        by auto
      have "ishalt (p ! (fst (steps ic p q)))"
        using terminates_halt_state[of "ic" "p"] is_val terminate by auto
      hence "S ic p k q = 0" using Add S_def[of "ic" "p" "k" "q"] by auto
      with sep q have "(\<Sum>t = 0..q - Suc 0. b ^ t * S ic p k t) = (\<Sum>t = 0..q. b ^ t * S ic p k t)"
        by auto
      thus ?thesis by auto
    next
      case (Sub x21 x22 x23)
      then show ?thesis by auto
    next
      case Halt
      then show ?thesis by auto
    qed

    hence add_q: "\<Sum>R+ p l (\<lambda>k. \<Sum>t=0..(q-1). b^t * S ic p k t) 
                = \<Sum>R+ p l (\<lambda>k. \<Sum>t=0..q. b^t * S ic p k t)"
    using sum_radd.simps single_step_add[of "ic" "p" "a" "l" "snd ic"] is_val l n_def by auto

  (* Start *)
  have "r l = (\<Sum>t = 0..q. b^t * R ic p l t)" using r_def RLe_def by auto
  also have "... = R ic p l 0 + (\<Sum>t = 1..q. b^t * R ic p l t)"
    by (auto simp: q comm_monoid_add_class.sum.atLeast_Suc_atMost)
  also have "... = a + (\<Sum>t \<in> {1..q}. b^t * R ic p l t)"
    by (simp add: R_def 0)
  also have "... = a + (\<Sum>t = (Suc 0)..(Suc (q-1)). b^t * R ic p l t)" using q by auto
  also have "... = a + (\<Sum>t \<in> (Suc ` {0..(q-1)}). b^t * R ic p l t)" by auto
  also have "... = a + (sum  ((\<lambda>t. b^t * R ic p l t) \<circ> Suc)) {0..(q-1)}"
    using comm_monoid_add_class.sum.reindex[of "Suc" "{0..(q-1)}" "(\<lambda>t. b^t * R ic p l t)"] by auto
  also have "... = a + (\<Sum>t = 0..(q-1). b^(Suc t) * R ic p l (Suc t))" by auto
  also have "... = a + (\<Sum>t = 0..(q-1). b^(Suc t) *(R ic p l t
                                              + (\<Sum>R+ p l (\<lambda>k. S ic p k t))
                                              - (\<Sum>R- p l (\<lambda>k. (Z ic p l t) * S ic p k t))))"
    using lm04_06_one_step_relation_register[of "ic" "p" "a" "l"] is_val n n_def l
    by (auto simp add: n_def m_def)

  also have "... = a + (\<Sum>t \<in> {0..(q-1)}. b^(Suc t) *  R ic p l t
                                + b^(Suc t) * (\<Sum>R+ p l (\<lambda>k. S ic p k t))
                                - b^(Suc t) * (\<Sum>R- p l (\<lambda>k. (Z ic p l t) * S ic p k t)))"
    by (auto simp add: algebra_simps)

  finally have "int (r l) = int a +(\<Sum>t \<in> {0..(q-1)}. int(
                                  b^(Suc t) *  R ic p l t
                                + b^(Suc t) * (\<Sum>R+ p l (\<lambda>k. S ic p k t))
                                - b^(Suc t) * (\<Sum>R- p l (\<lambda>k. (Z ic p l t) * S ic p k t))))"
    by auto

  also have "... = int a + (\<Sum>t \<in> {0..(q-1)}. int (b^(Suc t) *  R ic p l t)
                                + int (b^(Suc t) * (\<Sum>R+ p l (\<lambda>k. S ic p k t)))
                                - int (b^(Suc t) * (\<Sum>R- p l (\<lambda>k. (Z ic p l t) * S ic p k t))))"
    by (simp only: sum_int positive)

  also have "... = int a + (\<Sum>t \<in> {0..(q-1)}. int (b^(Suc t) *  R ic p l t)
                                + (int (b^(Suc t) * (\<Sum>R+ p l (\<lambda>k. S ic p k t)))
                                -  int (b^(Suc t) * (\<Sum>R- p l (\<lambda>k. (Z ic p l t) * S ic p k t)))))"
    by (simp add: add_diff_eq)

  also have "... = int a + (\<Sum>t \<in> {0..(q-1)}. int( b^(Suc t) *  R ic p l t ))
             + (\<Sum>t \<in> {0..(q-1)}. int( b^(Suc t) * (\<Sum>R+ p l (\<lambda>k. S ic p k t)))
                                - int( b^(Suc t) * (\<Sum>R- p l (\<lambda>k. (Z ic p l t) * S ic p k t ))))"
    by (auto simp only: sum.distrib)

  also have "... = int a + int b * int (\<Sum>t \<in> {0..(q-1)}. b^t *  R ic p l t )
             + int b * (\<Sum>t \<in> {0..(q-1)}. int(b^t * (\<Sum>R+ p l (\<lambda>k. S ic p k t)))
                                        - int(b^t * (\<Sum>R- p l (\<lambda>k. (Z ic p l t) * S ic p k t ))))"
    by (auto simp: sum_distrib_left mult.assoc right_diff_distrib)

  also have "... = int a + int b * int (\<Sum>t \<in> {0..(q-1)}. b^t *  R ic p l t )
             + int b * (\<Sum>t \<in> {0..(q-1)}. int(b^t * (\<Sum>R+ p l (\<lambda>k. S ic p k t))))
             - int b * (\<Sum>t \<in> {0..(q-1)}. int(b^t * (\<Sum>R- p l (\<lambda>k. (Z ic p l t) * S ic p k t))))"
    by (auto simp add: sum.distrib int_distrib(4) sum_subtractf)

  also have "... = int a + int b * int (\<Sum>t \<in> {0..(q-1)}. b^t *  R ic p l t )
             + int b * (\<Sum>t \<in> {0..(q-1)}. int(\<Sum>R+ p l (\<lambda>k. b^t * S ic p k t)))
             - int b * (\<Sum>t \<in> {0..(q-1)}. int(\<Sum>R- p l (\<lambda>k. b^t * (Z ic p l t * S ic p k t))))"
    using distrib_add distrib_sub by auto

  also have "... = int a + int b * int (\<Sum>t = 0..q-1. b^t *  R ic p l t)
             + int b * int (\<Sum>t = 0..q-1. \<Sum>R+ p l (\<lambda>k. b^t * S ic p k t))
             - int b * int (\<Sum>t = 0..q-1. \<Sum>R- p l (\<lambda>k. b^t * (Z ic p l t * S ic p k t)))"
    by auto

  also have "... = int a + int b * int (\<Sum>t = 0..q-1. b^t * R ic p l t)
             + int b * int (\<Sum>R+ p l (\<lambda>k. \<Sum>t=0..q-1. b^t * S ic p k t))
            - int b * int (\<Sum>R- p l (\<lambda>k. \<Sum>t=0..q-1. b^t * (Z ic p l t * S ic p k t)))"
    using sum_rsub_commutative[of "p" "l" "\<lambda>k t. b^t * (Z ic p l t * S ic p k t)" "q-1"]
    using sum_radd_commutative[of "p" "l" "\<lambda>k t. b^t * S ic p k t " "q-1"] by auto

  (* extend all sums until q, because values don't change at time q *)
  also have "... = int a + int b * int (\<Sum>t=0..q. b^t * R ic p l t)
             + int b * int (\<Sum>R+ p l (\<lambda>k. \<Sum>t=0..q-1. b^t * S ic p k t))
             - int b * int (\<Sum>R- p l (\<lambda>k. \<Sum>t=0..q-1. b^t * (Z ic p l t * S ic p k t)))"
    by (auto simp: rq R_def; smt One_nat_def rq)

  also have "... = int a + int b * int (\<Sum>t=0..q. b^t * R ic p l t)
             + int b * int (\<Sum>R+ p l (\<lambda>k. \<Sum>t=0..q. b^t * S ic p k t))
             - int b * int (\<Sum>R- p l (\<lambda>k. \<Sum>t=0..q. b^t * (Z ic p l t * S ic p k t)))"
    using zq add_q by auto

  also have "... = int a + int b * int (RLe ic p b q l)
             + int b * int (\<Sum>R+ p l (SKe ic p b q))
             - int b * int (\<Sum>R- p l (\<lambda>k. \<Sum>t=0..q. b^t * (Z ic p l t * S ic p k t)))"
    by (auto simp: RLe_def; metis SKe_def)

  (* prove multiplication turns into bitAND *)
  also have "... = int a + int b * int (RLe ic p b q l)
             + int b * int (\<Sum>R+ p l (SKe ic p b q))
             - int b * int (\<Sum>R- p l (\<lambda>k. ZLe ic p b q l && SKe ic p b q k))"
    using mult_to_bitAND c_gt_cells b_def c by auto

  finally have "int(r l) = int a + int b * int (r l)
             + int b * int (\<Sum>R+ p l s)
             - int b * int (\<Sum>R- p l (\<lambda>k. z l && s k))"
    by (auto simp: r_def s_def z_def)

  hence "r l = a + b * r l
             + b * \<Sum>R+ p l s
             - b * \<Sum>R- p l (\<lambda>k. z l && s k)"
    using int_ops(5) int_ops(7) nat_int nat_minus_as_int by presburger

  thus ?thesis by simp
qed

end
