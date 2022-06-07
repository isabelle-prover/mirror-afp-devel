subsubsection \<open>States\<close>

theory MultipleStepState
  imports SingleStepState
begin

lemma lm04_24_multiple_step_states:
fixes c :: nat
    and l :: register
    and ic :: configuration
    and p :: program
    and q :: nat
    and a :: nat

  defines "b == B c"
      and "m == length p"

assumes is_val: "is_valid_initial ic p a"
assumes c_gt_cells: "cells_bounded ic p c"
assumes d: "d \<le> m-1" and "0 < d"
    and q: "q > 0"

assumes terminate: "terminates ic p q"

assumes c: "c > 1"

  defines "r \<equiv> RLe ic p b q"
      and "z \<equiv> ZLe ic p b q"
      and "s \<equiv> SKe ic p b q"
      and "e \<equiv> \<Sum>t = 0..q. b^t"

shows "s d = b * (\<Sum>S+ p d s)
           + b * (\<Sum>S- p d (\<lambda>k. z (modifies (p!k)) && s k))
           + b * (\<Sum>S0 p d (\<lambda>k. (e - z (modifies (p!k))) && s k))"
proof -
  have "program_includes_halt p"
    using is_val is_valid_initial_def[of "ic" "p" "a"] is_valid_def[of "ic" "p"] by auto

  have halt_term0: "t \<le> q-1 \<longrightarrow> (if ishalt (p!(fst (steps ic p t))) \<and> d = fst (steps ic p t) 
                                    then Suc 0 else 0) = 0" for t 
    using terminate terminates_def by auto

  have single_step: "S ic p d (Suc t) = (\<Sum>S+ p d (\<lambda>k. S ic p k t))
                   + (\<Sum>S- p d (\<lambda>k. Z ic p (modifies (p!k)) t * S ic p k t))
                   + (\<Sum>S0 p d (\<lambda>k. (1 - Z ic p (modifies (p!k)) t) * S ic p k t))
                   + (if ishalt (p!(fst (steps ic p t))) \<and> d = fst (steps ic p t) then Suc 0 else 0)" for t
  using lm04_07_one_step_relation_state[of "ic" "p" "a" "d"] is_val `d>0` d
  by (simp add: m_def)

  have b: "b > 0" using b_def B_def by auto
  have halt: "ishalt (p!fst(steps ic p q))" using terminate terminates_def correct_halt_def by auto
  have add_conditions: "(if isadd (p ! k) \<and> d = goes_to (p ! k)
            then (\<Sum>t = 0..q - Suc 0. b ^ t * S ic p k t) + b ^ q * S ic p k q else 0)
         = (if isadd (p ! k) \<and> d = goes_to (p ! k)
            then \<Sum>t = 0..q - Suc 0. b ^ t * S ic p k t else 0)" for k
    apply (cases "p!k"; cases "d = goes_to (p!k)") using q S_def b halt by auto
  have "b * b ^ (q - Suc 0) = b ^ (q - Suc 0 + Suc 0)" using q
    by (simp add: power_eq_if)
  have "(\<lambda>k. (\<Sum>t = 0..(q-1).       b^t * S ic p k t) + b^(Suc (q-1)) * S ic p k (Suc (q-1)))
      = (\<lambda>k. (\<Sum>t = 0..(Suc (q-1)). b^t * S ic p k t))" by auto
  hence "\<Sum>S+ p d (\<lambda>k. (\<Sum>t = 0..(q-1).       b^t * S ic p k t) + b^q * S ic p k (Suc (q-1)))
       = \<Sum>S+ p d (\<lambda>k.  \<Sum>t = 0..(Suc (q-1)). b^t * S ic p k t)" using q
    by auto
  hence add_q: "\<Sum>S+ p d (\<lambda>k. \<Sum>t = 0..(q-1). b^t * S ic p k t)
              = \<Sum>S+ p d (\<lambda>k. \<Sum>t = 0..q. b^t * S ic p k t)"
    by (auto simp add: sum_sadd.simps q add_conditions)

  have "issub (p!k) \<Longrightarrow> b ^ (Suc (q-1)) * (Z ic p (modifies (p ! k)) (Suc (q-1)) *
        (if fst (steps ic p (Suc (q-1))) = k then Suc 0 else 0)) = 0" for k
    by (auto simp: q halt)
  hence sum_equiv_nzero: "issub (p!k) \<Longrightarrow>
        (\<Sum>t = 0..q-1. b ^ t * (Z ic p (modifies (p ! k)) t *
            (if fst (steps ic p t) = k then Suc 0 else 0)))
      = (\<Sum>t = 0..(Suc (q-1)). b ^ t * (Z ic p (modifies (p ! k)) t *
            (if fst (steps ic p t) = k then Suc 0 else 0)))" for k
    using sum.atLeast0_atMost_Suc[of "\<lambda>t. b ^ t * (Z ic p (modifies (p ! k)) t
                                  * (if fst (steps ic p t) = k then Suc 0 else 0))" "q-1"] by auto
  hence sub_nzero_conditions: "(if issub (p ! k) \<and> d = goes_to (p ! k) then
          \<Sum>t = 0..q - Suc 0. b ^ t * (Z ic p (modifies (p ! k)) t * S ic p k t) else 0)
       = (if issub (p ! k) \<and> d = goes_to (p ! k) then
          \<Sum>t = 0..q. b ^ t * (Z ic p (modifies (p ! k)) t * S ic p k t) else 0)" for k
    apply (cases "issub (p!k)") using q S_def halt b by auto
  have "(\<lambda>k. (\<Sum>t=0..(q-1). b^t * (Z ic p (modifies (p!k)) t * S ic p k t))
                    + b^(Suc (q-1)) * (Z ic p (modifies (p!k)) (Suc (q-1)) * S ic p k (Suc (q-1))))
      = (\<lambda>k. \<Sum>t=0..(Suc (q-1)). b^t * (Z ic p (modifies (p!k)) t * S ic p k t))" by auto
  hence sub_nzero_q: "(\<Sum>S- p d (\<lambda>k. \<Sum>t=0..(q-1). b^t * (Z ic p (modifies (p!k)) t * S ic p k t)))
                   = (\<Sum>S- p d (\<lambda>k. \<Sum>t=0..q. b^t * (Z ic p (modifies (p!k)) t * S ic p k t)))"
    by (auto simp: sum_ssub_nzero.simps q sub_nzero_conditions)

  have "issub (p!k) \<Longrightarrow> b ^ (Suc (q-1)) * ((Suc 0 - Z ic p (modifies (p ! k)) (Suc (q-1)))
          * S ic p k (Suc (q-1))) = 0" for k using q halt S_def by auto
  hence sum_equiv_zero: "issub (p!k) \<Longrightarrow>
         (\<Sum>t = 0..q-1. b ^ t * ((Suc 0 - Z ic p (modifies (p ! k)) t) * S ic p k t))
       = (\<Sum>t = 0..Suc (q-1). b ^ t * ((Suc 0 - Z ic p (modifies (p ! k)) t) * S ic p k t))" for k
    using sum.atLeast0_atMost_Suc[of "\<lambda>t. b ^ t * ((Suc 0 - Z ic p (modifies (p ! k)) t)
                                      * S ic p k t)" "q-1"] by auto
  have "(if issub (p ! k) \<and> d = goes_to_alt (p ! k) then
            \<Sum>t = 0..q - Suc 0. b ^ t * ((Suc 0 - Z ic p (modifies (p ! k)) t) * S ic p k t) else 0)
      = (if issub (p ! k) \<and> d = goes_to_alt (p ! k) then
            \<Sum>t = 0..q. b ^ t * ((Suc 0 - Z ic p (modifies (p ! k)) t) * S ic p k t) else 0)" for k
  apply (cases "issub (p!k)") using sum_equiv_zero[of "k"] q by auto
  hence sub_zero_q: "(\<Sum>S0 p d (\<lambda>k.\<Sum>t=0..q-1. b^t * ((1 - Z ic p (modifies(p!k)) t) * S ic p k t)))
                   = (\<Sum>S0 p d (\<lambda>k.\<Sum>t=0..q. b^t * ((1 - Z ic p (modifies (p!k)) t) * S ic p k t)))"
    using sum_ssub_zero.simps q by auto

  (* Start *)
  have "s d = (\<Sum>t = 0..q. b^t * S ic p d t)" using s_def SKe_def by auto
  also have "... = S ic p d 0 + (\<Sum>t = 1..q. b^t * S ic p d t)"
    by (auto simp: q comm_monoid_add_class.sum.atLeast_Suc_atMost)
  also have "... = (\<Sum>t = 1..q. b^t * S ic p d t)"
    using S_def `d>0` is_val is_valid_initial_def[of "ic" "p" "a"] by auto
  also have "... = (\<Sum>t \<in> (Suc ` {0..(q-1)}). b^t * S ic p d t)" using q by auto
  also have "... = (sum  ((\<lambda>t. b^t * S ic p d t) \<circ> Suc)) {0..(q-1)}"
    using comm_monoid_add_class.sum.reindex[of "Suc" "{0..(q-1)}" "(\<lambda>t. b^t * S ic p d t)"] by auto
  also have "... = (\<Sum>t = 0..(q-1). b^(Suc t) *((\<Sum>S+ p d (\<lambda>k. S ic p k t))
                                 + (\<Sum>S- p d (\<lambda>k. Z ic p (modifies (p!k)) t * S ic p k t))
                                 + (\<Sum>S0 p d (\<lambda>k. (1 - Z ic p (modifies (p!k)) t) * S ic p k t))
                                 + (if ishalt (p!(fst (steps ic p t))) \<and> d = fst (steps ic p t) 
                                    then Suc 0 else 0)))"
    using single_step by auto
  also have "... = (\<Sum>t = 0..(q-1). b^(Suc t) *((\<Sum>S+ p d (\<lambda>k. S ic p k t))
                                 + (\<Sum>S- p d (\<lambda>k. Z ic p (modifies (p!k)) t * S ic p k t))
                                 + (\<Sum>S0 p d (\<lambda>k. (1 - Z ic p (modifies (p!k)) t) * S ic p k t))))"
    using halt_term0 by auto
  also have "... =  (\<Sum>t = 0..(q-1). (b^(Suc t) * (\<Sum>S+ p d (\<lambda>k. S ic p k t))
                      + b^(Suc t) * (\<Sum>S- p d (\<lambda>k. Z ic p (modifies (p!k)) t * S ic p k t))
                      + b^(Suc t) * (\<Sum>S0 p d (\<lambda>k. (1 - Z ic p (modifies (p!k)) t) * S ic p k t))))"
    by (simp add: algebra_simps)
  also have "... = (\<Sum>t = 0..(q-1). (b^(Suc t) * (\<Sum>S+ p d (\<lambda>k. S ic p k t))))
           +(\<Sum>t=0..(q-1). b^(Suc t)*(\<Sum>S- p d (\<lambda>k. Z ic p (modifies (p!k)) t * S ic p k t)))
           +(\<Sum>t=0..(q-1). b^(Suc t)*(\<Sum>S0 p d (\<lambda>k. (1 - Z ic p (modifies (p!k)) t) * S ic p k t)))"
    by (auto simp only: sum.distrib)
  also have "... = b * (\<Sum>t = 0..(q-1). (b^t * (\<Sum>S+ p d (\<lambda>k. S ic p k t))))
           + b*(\<Sum>t=0..(q-1). b^t*(\<Sum>S- p d (\<lambda>k. Z ic p (modifies (p!k)) t * S ic p k t)))
           + b*(\<Sum>t=0..(q-1). b^t*(\<Sum>S0 p d (\<lambda>k. (1 - Z ic p (modifies (p!k)) t) * S ic p k t)))"
    by (auto simp: algebra_simps sum_distrib_left)
  also have "... = b * (\<Sum>t = 0..(q-1). (\<Sum>S+ p d (\<lambda>k. b^t * S ic p k t)))
          + b*(\<Sum>t=0..(q-1). (\<Sum>S- p d (\<lambda>k. b^t * (Z ic p (modifies (p!k)) t * S ic p k t))))
          + b*(\<Sum>t=0..(q-1). (\<Sum>S0 p d (\<lambda>k. b^t * ((1 - Z ic p (modifies (p!k)) t) * S ic p k t))))"
    using sum_sadd_distrib sum_ssub_nzero_distrib sum_ssub_zero_distrib by auto
  also have "... = b * (\<Sum>S+ p d (\<lambda>k. \<Sum>t = 0..(q-1). b^t * S ic p k t))
           + b*(\<Sum>S- p d (\<lambda>k. \<Sum>t=0..(q-1). b^t * (Z ic p (modifies (p!k)) t * S ic p k t)))
           + b*(\<Sum>S0 p d (\<lambda>k. \<Sum>t=0..(q-1). b^t * ((1 - Z ic p (modifies (p!k)) t) * S ic p k t)))"
    using sum_sadd_commutative sum_ssub_nzero_commutative sum_ssub_zero_commutative by auto
  (* extend all sums until q *)
  finally have eq1: "s d = b * (\<Sum>S+ p d (\<lambda>k. \<Sum>t = 0..q. b^t * S ic p k t))
           + b*(\<Sum>S- p d (\<lambda>k. \<Sum>t=0..q. b^t * (Z ic p (modifies (p!k)) t * S ic p k t)))
           + b*(\<Sum>S0 p d (\<lambda>k. \<Sum>t=0..q. b^t * ((1 - Z ic p (modifies (p!k)) t) * S ic p k t)))"
    using add_q sub_nzero_q sub_zero_q by auto
  also have "... = b * (\<Sum>S+ p d (\<lambda>k. s k))
           + b*(\<Sum>S- p d (\<lambda>k. \<Sum>t=0..q. b^t * (Z ic p (modifies (p!k)) t * S ic p k t)))
           + b*(\<Sum>S0 p d (\<lambda>k. \<Sum>t=0..q. b^t * ((1 - Z ic p (modifies (p!k)) t) * S ic p k t)))"
    using SKe_def s_def by auto
  finally have "s d = b * (\<Sum>S+ p d s)
           + b*(\<Sum>S- p d (\<lambda>k. \<Sum>t=0..q. b^t * (Z ic p (modifies (p!k)) t * S ic p k t)))
           + b*(\<Sum>S0 p d (\<lambda>k. \<Sum>t=0..q. b^t * ((1 - Z ic p (modifies (p!k)) t) * S ic p k t)))"
    by auto
  also have "... = b * (\<Sum>S+ p d s)
           + b*(\<Sum>S- p d (\<lambda>k. ZLe ic p b q (modifies (p!k)) && SKe ic p b q k))
           + b*(\<Sum>S0 p d (\<lambda>k. \<Sum>t=0..q. b^t * ((1 - Z ic p (modifies (p!k)) t) * S ic p k t)))"
    using mult_to_bitAND c_gt_cells b_def c by auto
  finally have "s d = b * (\<Sum>S+ p d s)
           + b*(\<Sum>S- p d (\<lambda>k. ZLe ic p b q (modifies (p!k)) && SKe ic p b q k))
           + b*(\<Sum>S0 p d (\<lambda>k. (e - ZLe ic p b q (modifies (p!k))) && SKe ic p b q k))"
    using mult_to_bitAND_state c_gt_cells b_def c e_def by auto
  thus ?thesis using s_def z_def by auto
qed

lemma lm04_25_multiple_step_state1:
fixes c :: nat
    and l :: register
    and ic :: configuration
    and p :: program
    and q :: nat
    and a :: nat

  defines "b == B c"
      and "m == length p"

assumes is_val: "is_valid_initial ic p a"
assumes c_gt_cells: "cells_bounded ic p c"
assumes d: "d=0"
    and q: "q > 0"

assumes terminate: "terminates ic p q"

assumes c: "c > 1"

  defines "r \<equiv> RLe ic p b q"
      and "z \<equiv> ZLe ic p b q"
      and "s \<equiv> SKe ic p b q"
      and "e \<equiv> \<Sum>t = 0..q. b^t"

shows "s d = 1 + b * (\<Sum>S+ p d s)
           + b * (\<Sum>S- p d (\<lambda>k. z (modifies (p!k)) && s k))
           + b * (\<Sum>S0 p d (\<lambda>k. (e - z (modifies (p!k))) && s k))"
proof -
  have "program_includes_halt p"
    using is_val is_valid_initial_def[of "ic" "p" "a"] is_valid_def[of "ic" "p"] by auto
  hence "p \<noteq> []" by auto
  have "\<not> ishalt (p!d)" using d m_def `program_includes_halt p` by auto
  hence "(if ishalt (p ! fst (steps ic p t)) \<and> d = fst (steps ic p t) then Suc 0 else 0) = 0" for t
    by auto
  hence single_step: "\<And>t. S ic p d (Suc t) = (\<Sum>S+ p d (\<lambda>k. S ic p k t))
                   + (\<Sum>S- p d (\<lambda>k. Z ic p (modifies (p!k)) t * S ic p k t))
                   + (\<Sum>S0 p d (\<lambda>k. (1 - Z ic p (modifies (p!k)) t) * S ic p k t))"
  using lm04_07_one_step_relation_state[of "ic" "p" "a" "d"] is_val d `p \<noteq> []` by (simp add: m_def)

  have b: "b > 0" using b_def B_def by auto
  have halt: "ishalt (p!fst(steps ic p q))" using terminate terminates_def correct_halt_def by auto
  have add_conditions: "(if isadd (p ! k) \<and> d = goes_to (p ! k)
            then (\<Sum>t = 0..q - Suc 0. b ^ t * S ic p k t) + b ^ q * S ic p k q else 0)
         = (if isadd (p ! k) \<and> d = goes_to (p ! k)
            then \<Sum>t = 0..q - Suc 0. b ^ t * S ic p k t else 0)" for k
    apply (cases "p!k"; cases "d = goes_to (p!k)") using q S_def b halt by auto
  have "b * b ^ (q - Suc 0) = b ^ (q - Suc 0 + Suc 0)" using q
    by (simp add: power_eq_if)
  have "(\<lambda>k. (\<Sum>t = 0..(q-1).       b^t * S ic p k t) + b^(Suc (q-1)) * S ic p k (Suc (q-1)))
      = (\<lambda>k. (\<Sum>t = 0..(Suc (q-1)). b^t * S ic p k t))" by auto
  hence "\<Sum>S+ p d (\<lambda>k. (\<Sum>t = 0..(q-1).       b^t * S ic p k t) + b^q * S ic p k (Suc (q-1)))
       = \<Sum>S+ p d (\<lambda>k.  \<Sum>t = 0..(Suc (q-1)). b^t * S ic p k t)" using q
    by auto
  hence add_q: "\<Sum>S+ p d (\<lambda>k. \<Sum>t = 0..(q-1). b^t * S ic p k t)
              = \<Sum>S+ p d (\<lambda>k. \<Sum>t = 0..q. b^t * S ic p k t)"
    by (auto simp add: sum_sadd.simps q add_conditions)

  have "issub (p!k) \<Longrightarrow> b ^ (Suc (q-1)) * (Z ic p (modifies (p ! k)) (Suc (q-1)) *
        (if fst (steps ic p (Suc (q-1))) = k then Suc 0 else 0)) = 0" for k
    by (auto simp: q halt)
  hence sum_equiv_nzero: "issub (p!k) \<Longrightarrow>
        (\<Sum>t = 0..q-1. b ^ t * (Z ic p (modifies (p ! k)) t *
            (if fst (steps ic p t) = k then Suc 0 else 0)))
      = (\<Sum>t = 0..(Suc (q-1)). b ^ t * (Z ic p (modifies (p ! k)) t *
            (if fst (steps ic p t) = k then Suc 0 else 0)))" for k
    using sum.atLeast0_atMost_Suc[of "\<lambda>t. b ^ t * (Z ic p (modifies (p ! k)) t
                                  * (if fst (steps ic p t) = k then Suc 0 else 0))" "q-1"] by auto
  hence sub_nzero_conditions: "(if issub (p ! k) \<and> d = goes_to (p ! k) then
          \<Sum>t = 0..q - Suc 0. b ^ t * (Z ic p (modifies (p ! k)) t * S ic p k t) else 0)
       = (if issub (p ! k) \<and> d = goes_to (p ! k) then
          \<Sum>t = 0..q. b ^ t * (Z ic p (modifies (p ! k)) t * S ic p k t) else 0)" for k
    apply (cases "issub (p!k)") using q S_def halt b by auto
  have "(\<lambda>k. (\<Sum>t=0..(q-1). b^t * (Z ic p (modifies (p!k)) t * S ic p k t))
                    + b^(Suc (q-1)) * (Z ic p (modifies (p!k)) (Suc (q-1)) * S ic p k (Suc (q-1))))
      = (\<lambda>k. \<Sum>t=0..(Suc (q-1)). b^t * (Z ic p (modifies (p!k)) t * S ic p k t))" by auto
  hence sub_nzero_q: "(\<Sum>S- p d (\<lambda>k. \<Sum>t=0..(q-1). b^t * (Z ic p (modifies (p!k)) t * S ic p k t)))
                   = (\<Sum>S- p d (\<lambda>k. \<Sum>t=0..q. b^t * (Z ic p (modifies (p!k)) t * S ic p k t)))"
    by (auto simp: sum_ssub_nzero.simps q sub_nzero_conditions)

  have "issub (p!k) \<Longrightarrow> b ^ (Suc (q-1)) * ((Suc 0 - Z ic p (modifies (p ! k)) (Suc (q-1)))
          * S ic p k (Suc (q-1))) = 0" for k using q halt S_def by auto
  hence sum_equiv_zero: "issub (p!k) \<Longrightarrow>
         (\<Sum>t = 0..q-1. b ^ t * ((Suc 0 - Z ic p (modifies (p ! k)) t) * S ic p k t))
       = (\<Sum>t = 0..Suc (q-1). b ^ t * ((Suc 0 - Z ic p (modifies (p ! k)) t) * S ic p k t))" for k
    using sum.atLeast0_atMost_Suc[of "\<lambda>t. b ^ t * ((Suc 0 - Z ic p (modifies (p ! k)) t)
                                      * S ic p k t)" "q-1"] by auto
  have "(if issub (p ! k) \<and> d = goes_to_alt (p ! k) then
            \<Sum>t = 0..q - Suc 0. b ^ t * ((Suc 0 - Z ic p (modifies (p ! k)) t) * S ic p k t) else 0)
      = (if issub (p ! k) \<and> d = goes_to_alt (p ! k) then
            \<Sum>t = 0..q. b ^ t * ((Suc 0 - Z ic p (modifies (p ! k)) t) * S ic p k t) else 0)" for k
  apply (cases "issub (p!k)") using sum_equiv_zero[of "k"] q by auto
  hence sub_zero_q: "(\<Sum>S0 p d (\<lambda>k.\<Sum>t=0..q-1. b^t * ((1 - Z ic p (modifies(p!k)) t) * S ic p k t)))
                   = (\<Sum>S0 p d (\<lambda>k.\<Sum>t=0..q. b^t * ((1 - Z ic p (modifies (p!k)) t) * S ic p k t)))"
    using sum_ssub_zero.simps q by auto

  have S0: "S ic p d 0 = 1" using S_def is_val is_valid_initial_def[of "ic" "p" "a"] d by auto

  (* Start *)
  have "s d = (\<Sum>t = 0..q. b^t * S ic p d t)" using s_def SKe_def by auto
  also have "... = S ic p d 0 + (\<Sum>t = 1..q. b^t * S ic p d t)"
    by (auto simp: q comm_monoid_add_class.sum.atLeast_Suc_atMost)
  also have "... = b^0 * S ic p d 0 + (\<Sum>t = 1..q. b^t * S ic p d t)"
    using S_def is_val is_valid_initial_def[of "ic" "p" "a"] by auto
  also have "... = 1 + (\<Sum>t \<in> (Suc ` {0..(q-1)}). b^t * S ic p d t)" using q S0 by auto
  also have "... = 1 + (sum  ((\<lambda>t. b^t * S ic p d t) \<circ> Suc)) {0..(q-1)}"
    using comm_monoid_add_class.sum.reindex[of "Suc" "{0..(q-1)}" "(\<lambda>t. b^t * S ic p d t)"] by auto
  also have "... = 1 + (\<Sum>t = 0..(q-1). b^(Suc t) *((\<Sum>S+ p d (\<lambda>k. S ic p k t))
                                 + (\<Sum>S- p d (\<lambda>k. Z ic p (modifies (p!k)) t * S ic p k t))
                                 + (\<Sum>S0 p d (\<lambda>k. (1 - Z ic p (modifies (p!k)) t) * S ic p k t))))"
    using single_step by auto
  also have "... = 1 + (\<Sum>t = 0..(q-1). (b^(Suc t) * (\<Sum>S+ p d (\<lambda>k. S ic p k t))
                      + b^(Suc t) * (\<Sum>S- p d (\<lambda>k. Z ic p (modifies (p!k)) t * S ic p k t))
                      + b^(Suc t) * (\<Sum>S0 p d (\<lambda>k. (1 - Z ic p (modifies (p!k)) t) * S ic p k t))))"
    by (simp add: algebra_simps)
  also have "... = 1 + (\<Sum>t = 0..(q-1). (b^(Suc t) * (\<Sum>S+ p d (\<lambda>k. S ic p k t))))
           +(\<Sum>t=0..(q-1). b^(Suc t)*(\<Sum>S- p d (\<lambda>k. Z ic p (modifies (p!k)) t * S ic p k t)))
           +(\<Sum>t=0..(q-1). b^(Suc t)*(\<Sum>S0 p d (\<lambda>k. (1 - Z ic p (modifies (p!k)) t) * S ic p k t)))"
    by (auto simp only: sum.distrib)
  also have "... = 1 + b * (\<Sum>t = 0..(q-1). (b^t * (\<Sum>S+ p d (\<lambda>k. S ic p k t))))
           + b*(\<Sum>t=0..(q-1). b^t*(\<Sum>S- p d (\<lambda>k. Z ic p (modifies (p!k)) t * S ic p k t)))
           + b*(\<Sum>t=0..(q-1). b^t*(\<Sum>S0 p d (\<lambda>k. (1 - Z ic p (modifies (p!k)) t) * S ic p k t)))"
    by (auto simp: algebra_simps sum_distrib_left)
  also have "... = 1 + b * (\<Sum>t = 0..(q-1). (\<Sum>S+ p d (\<lambda>k. b^t * S ic p k t)))
          + b*(\<Sum>t=0..(q-1). (\<Sum>S- p d (\<lambda>k. b^t * (Z ic p (modifies (p!k)) t * S ic p k t))))
          + b*(\<Sum>t=0..(q-1). (\<Sum>S0 p d (\<lambda>k. b^t * ((1 - Z ic p (modifies (p!k)) t) * S ic p k t))))"
    using sum_sadd_distrib sum_ssub_nzero_distrib sum_ssub_zero_distrib by auto
  also have "... = 1 + b * (\<Sum>S+ p d (\<lambda>k. \<Sum>t = 0..(q-1). b^t * S ic p k t))
           + b*(\<Sum>S- p d (\<lambda>k. \<Sum>t=0..(q-1). b^t * (Z ic p (modifies (p!k)) t * S ic p k t)))
           + b*(\<Sum>S0 p d (\<lambda>k. \<Sum>t=0..(q-1). b^t * ((1 - Z ic p (modifies (p!k)) t) * S ic p k t)))"
    using sum_sadd_commutative sum_ssub_nzero_commutative sum_ssub_zero_commutative by auto
  (* extend all sums until q *)
  finally have eq1: "s d = 1 + b * (\<Sum>S+ p d (\<lambda>k. \<Sum>t = 0..q. b^t * S ic p k t))
           + b*(\<Sum>S- p d (\<lambda>k. \<Sum>t=0..q. b^t * (Z ic p (modifies (p!k)) t * S ic p k t)))
           + b*(\<Sum>S0 p d (\<lambda>k. \<Sum>t=0..q. b^t * ((1 - Z ic p (modifies (p!k)) t) * S ic p k t)))"
    using add_q sub_nzero_q sub_zero_q by auto
  also have "... = 1 + b * (\<Sum>S+ p d (\<lambda>k. s k))
           + b*(\<Sum>S- p d (\<lambda>k. \<Sum>t=0..q. b^t * (Z ic p (modifies (p!k)) t * S ic p k t)))
           + b*(\<Sum>S0 p d (\<lambda>k. \<Sum>t=0..q. b^t * ((1 - Z ic p (modifies (p!k)) t) * S ic p k t)))"
    using SKe_def s_def by auto
  finally have "s d = 1 + b * (\<Sum>S+ p d s)
           + b*(\<Sum>S- p d (\<lambda>k. \<Sum>t=0..q. b^t * (Z ic p (modifies (p!k)) t * S ic p k t)))
           + b*(\<Sum>S0 p d (\<lambda>k. \<Sum>t=0..q. b^t * ((1 - Z ic p (modifies (p!k)) t) * S ic p k t)))"
    by auto
  also have "... = 1 + b * (\<Sum>S+ p d s)
           + b*(\<Sum>S- p d (\<lambda>k. ZLe ic p b q (modifies (p!k)) && SKe ic p b q k))
           + b*(\<Sum>S0 p d (\<lambda>k. \<Sum>t=0..q. b^t * ((1 - Z ic p (modifies (p!k)) t) * S ic p k t)))"
    using mult_to_bitAND c_gt_cells b_def c by auto
  finally have "s d = 1 + b * (\<Sum>S+ p d s)
           + b*(\<Sum>S- p d (\<lambda>k. ZLe ic p b q (modifies (p!k)) && SKe ic p b q k))
           + b*(\<Sum>S0 p d (\<lambda>k. (e - ZLe ic p b q (modifies (p!k))) && SKe ic p b q k))"
    using mult_to_bitAND_state c_gt_cells b_def c e_def by auto
  thus ?thesis using s_def z_def by auto
qed

lemma halting_condition_04_27:
fixes c :: nat
  and l :: register
  and ic :: configuration
  and p :: program
  and q :: nat
  and a :: nat

defines "b == B c"
    and "m == length p - 1"

assumes is_val: "is_valid_initial ic p a"
    and q: "q > 0"

assumes terminate: "terminates ic p q"

shows "SKe ic p b q m = b ^ q"
proof -
  have halt: "ishalt (p ! (fst (steps ic p q)))" 
    using terminate terminates_def correct_halt_def by auto
  have "\<forall>k<length p - 1. \<not> ishalt (p!k)" using is_val is_valid_initial_def[of "ic" "p" "a"]
       is_valid_def[of "ic" "p"] program_includes_halt.simps by blast
  hence "ishalt (p!k) \<Longrightarrow> k \<ge> length p - 1" for k using not_le_imp_less by auto
  hence gt: "fst (steps ic p q) \<ge> m" using halt m_def by auto
  have "fst (steps ic p q) \<le> m"
    using p_contains[of "ic" "p" "a" "q"] is_val m_def by auto
  hence q_steps_m: "fst (steps ic p q) = m" using gt by auto
  hence 1: "S ic p m q = 1" using S_def by auto

  have "ishalt (p!m)" using q_steps_m halt  by auto
  have "\<forall>t<q. \<not> ishalt (p ! (fst (steps ic p t)))" using terminate terminates_def by auto
  hence "\<forall>t<q. \<not> (fst (steps ic p t) = m)" using `ishalt (p!m)` by auto
  hence 0: "t \<le> q-1 \<Longrightarrow> S ic p m t = 0" for t using q S_def[of "ic" "p" "m" "t"] by auto

  have "SKe ic p b q m = (\<Sum>t = 0..(Suc (q-1)). b ^ t * S ic p m t)" by (auto simp: q SKe_def)
  also have "... = (\<Sum>t = 0..(q-1). b^t * S ic p m t) + b ^ (Suc (q-1)) * S ic p m (Suc (q-1))"
    by auto
  also have "... = b ^ q" using 0 1 q by auto
  finally show ?thesis by auto
qed

lemma state_q_bound:
fixes c :: nat
  and l :: register
  and ic :: configuration
  and p :: program
  and q :: nat
  and a :: nat

defines "b == B c"
    and "m == length p - 1"

assumes is_val: "is_valid_initial ic p a"
    and q: "q > 0"
    and terminate: "terminates ic p q"
    and c: "c > 0"

assumes "k<m"
                                                                  
shows "SKe ic p b q k < b ^ q"
proof -
  from b_def have "b>1" using B_def apply auto
    by (metis One_nat_def one_less_numeral_iff power_gt1_lemma semiring_norm(76))
  hence b: "b > 2" using c b_def B_def 
    by (smt One_nat_def Suc_le_lessD less_Suc_eq_le less_trans_Suc linorder_neqE_nat
            numeral_2_eq_2 power_Suc0_right power_inject_exp)
  from \<open>k<m\<close> have "\<not> ishalt (p!k)" using is_val
    by (simp add: is_valid_def is_valid_initial_def is_val m_def)
  hence "S ic p k q = 0" using terminate terminates_def correct_halt_def S_def by auto
  hence "SKe ic p b q k = (\<Sum>t = 0..q-1. b ^ t * S ic p k t)" 
    using \<open>q>0\<close> apply (auto cong: sum.cong simp: SKe_def) by (metis (no_types, lifting) Suc_pred 
          add_cancel_right_right mult_0_right sum.atLeast0_atMost_Suc) 
  also have "... \<le> (\<Sum>t = 0..q-1. b^t)" by (auto simp add: S_def gr_implies_not0 sum_mono)
  also have "... < b ^ q"
    using `q>0` sum_bt
    by (metis Suc_diff_1 b)

  finally show ?thesis by auto
qed

end
