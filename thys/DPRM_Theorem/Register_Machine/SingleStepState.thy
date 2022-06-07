subsubsection \<open>States\<close>

theory SingleStepState
  imports RegisterMachineSimulation
begin

lemma lm04_07_one_step_relation_state:
  fixes d :: state
    and c :: configuration
    and p :: program
    and t :: nat
    and a :: nat

defines "r \<equiv> R c p"
defines "s \<equiv> S c p"
defines "z \<equiv> Z c p"
defines "cs \<equiv> fst (steps c p t)"

assumes is_val: "is_valid_initial c p a"
    and "d < length p"

shows "s d (Suc t) = (\<Sum>S+ p d (\<lambda>k. s k t))
                   + (\<Sum>S- p d (\<lambda>k. z (modifies (p!k)) t * s k t))
                   + (\<Sum>S0 p d (\<lambda>k. (1 - z (modifies (p!k)) t) * s k t))
                   + (if ishalt (p!cs) \<and> d = cs then Suc 0 else 0)"
proof -
  have ic: "c = (0, snd c)" 
    using is_val by (auto simp add: is_valid_initial_def) (metis prod.collapse)
  have cs_bound: "cs < length p" using ic is_val p_contains[of "c" "p" "a" "t"] cs_def by auto

  have  "(\<Sum>k = 0..length p-1.
                       if isadd (p ! k) \<and> goes_to (p ! fst (steps c p t)) = goes_to (p ! k)
                        then if fst (steps c p t) = k
                          then Suc 0 else 0 else 0)
        =(\<Sum>k = 0..length p-1.
                       if fst (steps c p t) = k
                         then if isadd (p ! k) \<and> goes_to (p ! fst (steps c p t)) = goes_to (p ! k)
                           then Suc 0 else 0 else 0)"
    apply (rule sum.cong) by auto
  hence add: "(\<Sum>S+ p d (\<lambda>k. s k t)) = (if isadd (p!cs) \<and> d = goes_to (p!cs) then Suc 0 else 0)"
    apply (auto simp add: sum_sadd.simps s_def S_def cs_def)
    using cs_bound cs_def by auto

  have "(\<Sum>k = 0..length p-1.
            if issub (p ! k) \<and> goes_to (p ! fst (steps c p t)) = goes_to (p ! k)
                then z (modifies (p ! k)) t * (if fst (steps c p t) = k then Suc 0 else 0) else 0)
      = (\<Sum>k = 0..length p-1. if k=cs then
            if issub (p ! k) \<and> goes_to (p ! fst (steps c p t)) = goes_to (p ! k)
                then z (modifies (p ! k)) t  else 0 else 0)"
    apply (rule sum.cong)
    using z_def Z_def cs_def by auto
  hence sub_zero: "(\<Sum>S- p d (\<lambda>k. z (modifies (p!k)) t * s k t))
          = (if issub (p!cs) \<and> d = goes_to (p!cs) then z (modifies (p!cs)) t else 0)"
    apply (auto simp add: sum_ssub_nzero.simps s_def S_def cs_def)
    using cs_bound cs_def by auto

  have "(\<Sum>k = 0..length p-1.
        if issub (p ! k) \<and> goes_to_alt (p ! fst (steps c p t)) = goes_to_alt (p ! k)
        then (Suc 0 - z (modifies (p ! k)) t) * (if fst (steps c p t) = k then Suc 0 else 0) else 0)
      = (\<Sum>k = 0..length p-1. if k=cs then
            if issub (p ! k) \<and> goes_to_alt (p ! fst (steps c p t)) = goes_to_alt (p ! k)
            then (Suc 0 - z (modifies (p ! k)) t) else 0 else 0)"
    apply (rule sum.cong) using z_def Z_def cs_def by auto
  hence sub_nzero: "(\<Sum>S0 p d (\<lambda>k. (1 - z (modifies (p!k)) t) * s k t))
          = (if issub (p!cs) \<and> d = goes_to_alt (p!cs) then (1 - z (modifies (p!cs)) t) else 0)"
    apply (auto simp: sum_ssub_zero.simps s_def S_def cs_def)
    using cs_bound cs_def by auto

  have "s d (Suc t) = (if isadd (p!cs) \<and> d = goes_to (p!cs) then Suc 0 else 0)
                + (if issub (p!cs) \<and> d = goes_to (p!cs) then z (modifies (p!cs)) t else 0)
                + (if issub (p!cs) \<and> d = goes_to_alt (p!cs) then (1 - z (modifies (p!cs)) t) else 0)
                + (if ishalt (p!cs) \<and> d = cs then Suc 0 else 0)"
    apply (cases "p!cs")
    by (auto simp: s_def S_def step_def fetch_def cs_def z_def Z_def Z_bounded R_def read_def)

  thus ?thesis using add sub_zero sub_nzero by auto
qed

end
