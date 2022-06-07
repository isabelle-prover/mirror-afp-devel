subsection \<open>Single step relations\<close>

subsubsection \<open>Registers\<close>

theory SingleStepRegister
  imports RegisterMachineSimulation
begin

lemma single_step_add:
  fixes c :: configuration
    and p :: program
    and l :: register
    and t a :: nat

defines "cs \<equiv> fst (steps c p t)"

assumes is_val: "is_valid_initial c p a"
    and l: "l < length tape"

shows "(\<Sum>R+ p l (\<lambda>k. S c p k t))
        = (if isadd (p!cs) \<and> l = modifies (p!cs) then 1 else 0)"
proof -
  have ic: "c = (0, snd c)" 
    using is_val by (auto simp add: is_valid_initial_def) (metis prod.collapse)

  have add_if: "(\<Sum>k = 0..length p-1. if isadd (p ! k) \<and> modifies (p ! cs) = modifies (p ! k) 
                                      then S c p k t else 0)
              = (\<Sum>k = 0..length p-1. if k=cs then
              if isadd (p ! k) \<and> modifies (p ! cs) = modifies (p ! k) then S c p k t else 0 else 0)"
    apply (rule sum.cong)
    using S_unique cs_def by auto

  have bound: "fst (steps c p t) \<le> length p - 1" using is_val ic p_contains[of "c" "p" "a" "t"]
    by (auto simp add: dual_order.strict_implies_order)

  thus ?thesis using S_unique add_if
    apply (auto simp add: sum_radd.simps add_if S_def cs_def)
    by (smt S_def sum.cong)
qed

lemma single_step_sub:
  fixes c :: configuration
    and p :: program
    and l :: register
    and t a :: nat

defines "cs \<equiv> fst (steps c p t)"

assumes is_val: "is_valid_initial c p a"

shows "(\<Sum>R- p l (\<lambda>k. Z c p l t * S c p k t))
        = (if issub (p!cs) \<and> l = modifies (p!cs) then Z c p l t else 0)"
proof -
  have "fst c = 0" using is_val by (auto simp add: is_valid_initial_def)
  hence ic: "c = (0, snd c)" by (metis prod.collapse)

  have bound: "cs \<le> length p - 1" using is_val ic p_contains[of "c" "p" "a" "t"]
    by (auto simp add: dual_order.strict_implies_order cs_def)

  have sub_if: "(\<Sum>k = 0..length p-1. if issub (p ! k) \<and> modifies (p ! cs) = modifies (p ! k)
                                    then 1 * (if cs = k then (Suc 0) else 0) else 0)
               =(\<Sum>k = 0..length p-1. if k = cs then
                                      (if issub (p ! k) \<and> modifies (p ! cs) = modifies (p ! k)
                                       then (Suc 0) * (if cs = k then (Suc 0) else 0)
                                    else 0) else 0)"
    apply (rule sum.cong) using cs_def by auto

  show ?thesis using bound sub_if
    apply (auto simp add: sum_rsub.simps cs_def Z_def S_def R_def)
    by (metis One_nat_def cs_def)
qed

lemma lm04_06_one_step_relation_register_old:
  fixes l::register
    and ic::configuration
    and p::program

  defines "s \<equiv> fst ic"
      and "tape \<equiv> snd ic"

  defines "m \<equiv> length p"
      and "tape' \<equiv> snd (step ic p)"

  assumes is_val: "is_valid ic p"
      and l: \<open>l < length tape\<close>

  shows "(tape'!l) = (tape!l) + (if isadd (p!s) \<and> l = modifies (p!s) then 1 else 0)
                              - Z ic p l 0 * (if issub (p!s) \<and> l = modifies (p!s) then 1 else 0)"
proof -
  show ?thesis
    using l
    apply (cases \<open>p!s\<close>)
    apply (auto simp: assms(1-4) step_def update_def)
    using nth_digit_0 by (auto simp add: Z_def R_def)
qed

(* [T] 4.6 *)
lemma lm04_06_one_step_relation_register:
  fixes l :: register
    and c :: configuration
    and p :: program
    and t :: nat
    and a :: nat

defines "r \<equiv> R c p"
defines "s \<equiv> S c p"

assumes is_val: "is_valid_initial c p a"
    and l: "l < length (snd c)"

  shows "r l (Suc t) = r l t + (\<Sum>R+ p l (\<lambda>k. s k t))
                             - (\<Sum>R- p l (\<lambda>k. (Z c p l t) * s k t))"
proof -
  define cs where "cs \<equiv> fst (steps c p t)"

  have add: "(\<Sum>R+ p l (\<lambda>k. s k t))
      = (if isadd (p!cs) \<and> l = modifies (p!cs) then 1 else 0)"
    using single_step_add[of "c" "p" "a" "l" "snd c" "t"] is_val l s_def cs_def by auto

  have sub: "(\<Sum>R- p l (\<lambda>k. Z c p l t * s k t))
         = (if issub (p!cs) \<and> l = modifies (p!cs) then Z c p l t else 0)"
    using single_step_sub is_val l s_def cs_def Z_def R_def by auto

  have lhs: "r l (Suc t) = snd (steps c p (Suc t)) ! l"
    by (simp add: r_def R_def del: steps.simps)

  have rhs: "r l t = snd (steps c p t) ! l"
    by (simp add: r_def R_def del: steps.simps)

  have valid_time: "is_valid (steps c p t) p" using steps_is_valid_invar is_val
    by (auto simp add: is_valid_initial_def)

  have l_time: "l < length (snd (steps c p t))" using l steps_tape_length_invar by auto

  from lhs rhs have "r l (Suc t) = r l t + (if isadd (p!cs) \<and> l = modifies (p!cs) then 1 else 0)
                            - (if issub (p!cs) \<and> l = modifies (p!cs) then Z c p l t else 0)"
    using l_time valid_time lm04_06_one_step_relation_register_old steps.simps cs_def nth_digit_0
    Z_def R_def by auto

  thus ?thesis using add sub by simp
qed

end
