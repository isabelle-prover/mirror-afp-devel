subsubsection \<open>State 0 equation\<close>

theory State_0_Equation imports "../Register_Machine/MultipleStepState"
                                    RM_Sums_Diophantine "../Diophantine/Binary_And"

begin

context rm_eq_fixes 
begin

  text \<open>Equation 4.24\<close>
  definition state_0 :: "bool" where
    "state_0 \<equiv> s 0 = 1 + b*\<Sum>S+ p 0 s + b*\<Sum>S- p 0 (\<lambda>k. s k && z (modifies (p!k)))
                                             + b*\<Sum>S0 p 0 (\<lambda>k. s k && (e - z (modifies (p!k))))"
  
end

context register_machine 
begin

no_notation ppolynomial.Sum (infixl "\<^bold>+" 65) 
no_notation ppolynomial.NatDiff (infixl "\<^bold>-" 65) 
no_notation ppolynomial.Prod (infixl "\<^bold>*" 70) 


lemma state_0_dioph:
  fixes b e :: polynomial
  fixes z s :: "polynomial list"
  assumes "length z = n" "length s = Suc m"
  defines "DR \<equiv> LARY (\<lambda>ll. rm_eq_fixes.state_0 p (ll!0!0) (ll!0!1)
                            (nth (ll!1)) (nth (ll!2))) [[b, e], z, s]"
  shows "is_dioph_rel DR"
proof -
  let ?N = "2"
  define b' e' z' s' where pushed_def: "b' = push_param b ?N" 
                                       "e' = push_param e ?N"
                                       "z' = map (\<lambda>x. push_param x ?N) z" 
                                       "s' = map (\<lambda>x. push_param x ?N) s"

  define z0 z1 where z_def: "z0 \<equiv> map (\<lambda>i. z' ! modifies (p!i)) [0..<length p]"
                            "z1 \<equiv> map (\<lambda>i. e' [-] z' ! modifies (p!i)) [0..<length p]"

  define param_0_is_sum_sub_nzero_term where 
    "param_0_is_sum_sub_nzero_term \<equiv> [Param 0 = \<Sum>S- 0 (s' && z0)]"

  define param_1_is_sum_sub_zero_term where
    "param_1_is_sum_sub_zero_term \<equiv> [Param 1 = \<Sum>S0 0 (s' && z1)]"
  
  define step_relation where
    "step_relation \<equiv> (s'!0 [=] \<^bold>1 [+] b' [*] ([\<Sum>S+] p 0 (nth s')) 
                                  [+] b' [*] Param 0 [+] b' [*] Param 1)"

  define DS where "DS \<equiv> [\<exists>?N] step_relation 
                          [\<and>] param_0_is_sum_sub_nzero_term 
                          [\<and>] param_1_is_sum_sub_zero_term"

  have "p \<noteq> []" using p_nonempty by auto
  have ps_lengths: "length p = length s"
    using \<open>length s = Suc m\<close> m_def \<open>p \<noteq> []\<close> by auto
  have s_len: "length s > 0"
    using ps_lengths \<open>p \<noteq> []\<close> by auto
  have p_len: "length p > 0"
    using ps_lengths s_len by auto
  have p_len2: "length p = Suc m"
    using ps_lengths \<open>length s = Suc m\<close> by auto
  have len_s': "length s' = Suc m"
    unfolding pushed_def using \<open>length s = Suc m\<close> by auto
  have "length z0 = Suc m"
    unfolding z_def ps_lengths \<open>length s = Suc m\<close> by simp
  have "length z1 = Suc m"
    unfolding z_def ps_lengths \<open>length s = Suc m\<close> by simp

  have modifies_le_n: "k < length p \<Longrightarrow> modifies (p!k) < n" for k
    using  modifies_yields_valid_register \<open>length z = n\<close> by auto

  have "eval DS a = eval DR a" for a
  proof -

    have b'_unfold: "peval b' (push_list a ks) = peval b a" if "length ks = 2" for ks
      using push_push_simp unfolding pushed_def using that by metis

    have s'_0_unfold: "peval (s' ! 0) (push_list a ks) = peval (s ! 0) a" if "length ks = 2" for ks
      unfolding pushed_def using push_push_map_i[of ks 2 0 s a] that unfolding list_eval_def
      \<open>length s > 0\<close> using s_len by auto

    have sum_nzero_unfold: 
      "eval [polynomial.Param 0 = \<Sum>S- 0 (s' && z0)] (push_list a ks) 
      = (peval (polynomial.Param 0) (push_list a ks) 
        = \<Sum>S- p 0 (\<lambda>k. peval (s' ! k) (push_list a ks) && peval (z0 ! k) (push_list a ks)))" for ks
      using sum_rsub_nzero_of_bit_and_eval[of s' z0 "Param 0" 0 "push_list a ks"] 
            \<open>length p > 0\<close> \<open>length s' = Suc m\<close> \<open>length z0 = Suc m\<close> by auto

    have sum_zero_unfold: 
      "eval [polynomial.Param 1 = \<Sum>S0 0 (s' && z1)] (push_list a ks) 
      = (peval (polynomial.Param 1) (push_list a ks)
         = \<Sum>S0 p 0 (\<lambda>k. peval (s' ! k) (push_list a ks) && peval (z1 ! k) (push_list a ks)))" for ks 
      using sum_rsub_zero_of_bit_and_eval[of s' z1 "Param 1" 0 "push_list a ks"]
            \<open>length p > 0\<close> \<open>length s' = Suc m\<close> \<open>length z1 = Suc m\<close> by auto

    have param_0_unfold: "peval (Param 0) (push_list a ks) = ks ! 0" if "length ks = 2" for ks
      unfolding push_list_def using that by auto

    have param_1_unfold: "peval (Param 1) (push_list a ks) = ks ! 1" if "length ks = 2" for ks
      unfolding push_list_def using that by auto

    have sum_sadd_unfold:
      "peval ([\<Sum>S+] p 0 ((!) s')) (push_list a ks) = \<Sum>S+ p 0 (\<lambda>x. peval (s ! x) a)" 
      if "length ks = 2" for ks
      using sum_sadd_polynomial_eval \<open>length p > 0\<close> apply auto
      apply (rule sum_sadd_cong, auto)
      unfolding pushed_def using push_push_map_i[of ks 2 _ s a] that 
      unfolding \<open>length p = length s\<close> list_eval_def 
      by (smt One_nat_def assms le_imp_less_Suc m_def nth_map p_len2)

    have z0_unfold: 
      "peval (s' ! k) (push_list a ks) && peval (z0 ! k) (push_list a ks) 
      = peval (s ! k) a && peval (z ! modifies (p ! k)) a"
      if "length ks = 2" and "k < length p" for k ks
    proof - 
      have map: "map (\<lambda>i. z' ! modifies (p ! i)) [0..<length p] ! k 
            = z' ! modifies (p ! k)"
        unfolding z_def using nth_map[of k "[0..<length p]" "\<lambda>i. z' ! modifies (p ! i)"]
        using \<open>k < length p\<close> by auto

      have s: "peval (map (\<lambda>x. push_param x 2) s ! k) (push_list a ks) = peval (s ! k) a"
        using push_push_map_i[of ks 2 k s] that nth_map[of k s]
        unfolding \<open>length s = Suc m\<close> \<open>length p = Suc m\<close> list_eval_def by auto

      have z: "peval (map (\<lambda>x. push_param x 2) z ! modifies (p ! k)) (push_list a ks)
               = peval (z ! modifies (p ! k)) a"
        using push_push_map_i[of ks 2 "modifies (p!k)" z a] modifies_le_n[of k] that nth_map[of _ z]
        unfolding \<open>length z = n\<close> list_eval_def by auto

      show ?thesis
        unfolding z_def map unfolding pushed_def s z by auto
    qed

    have z1_unfold: 
      "peval (s' ! k) (push_list a ks) && peval (z1 ! k) (push_list a ks)
      = peval (s ! k) a && (peval e a - peval (z ! modifies (p ! k)) a)"
      if "length ks = 2" and "k < length p" for k ks
    proof - 
      have map: 
        "map (\<lambda>i. e' [-] (z' ! (modifies (p ! i)))) [0..<length p] ! k
         = e' [-] (z' ! modifies (p ! k))"
        using nth_map[of k "[0..<length p]" "\<lambda>i. z' ! modifies (p ! i)"]
        using \<open>k < length p\<close> by auto

      have s: "peval (map (\<lambda>x. push_param x 2) s ! k) (push_list a ks) = peval (s ! k) a"
        using push_push_map_i[of ks 2 k s] that nth_map[of k s]
        unfolding \<open>length s = Suc m\<close> \<open>length p = Suc m\<close> list_eval_def by auto

      have z: "peval (push_param e 2) (push_list a ks) 
             - peval (map (\<lambda>x. push_param x 2) z ! modifies (p ! k)) (push_list a ks)
             = peval e a - peval (z ! (modifies (p!k))) a"
        using push_push_simp[of e ks a] unfolding \<open>length ks = 2\<close> apply simp
        using push_push_map_i[of ks 2 "modifies (p!k)" z a] modifies_le_n[of k] that 
              nth_map[of "modifies (p!k)" z "(\<lambda>x. peval x a)"]
        unfolding \<open>length z = n\<close> list_eval_def by auto

      show ?thesis
        unfolding z_def map unfolding pushed_def s using z by auto
    qed

    have z0sum_unfold:
      "(\<Sum>S- p 0 (\<lambda>k. peval (s' ! k) (push_list a ks) && peval (z0 ! k) (push_list a ks)))
      =(\<Sum>S- p 0 (\<lambda>k. peval (s ! k) a && peval (z ! modifies (p ! k)) a))"
      if "length ks = 2" for ks
      apply (rule sum_ssub_nzero_cong) using z0_unfold[of ks] that 
      by (metis \<open>length s = Suc m\<close> le_imp_less_Suc m_def ps_lengths)

    have z1sum_unfold:
      "(\<Sum>S0 p 0 (\<lambda>k. peval (s' ! k) (push_list a ks) && peval (z1 ! k) (push_list a ks)))
      =(\<Sum>S0 p 0 (\<lambda>k. peval (s ! k) a && peval e a - peval (z ! modifies (p ! k)) a))"
      if "length ks = 2" for ks
      apply (rule sum_ssub_zero_cong) using z1_unfold[of ks] that 
      by (metis \<open>length s = Suc m\<close> le_imp_less_Suc m_def ps_lengths) 

    have sum_sadd_map: "\<Sum>S+ p 0 ((!) (map (\<lambda>P. peval P a) s)) = \<Sum>S+ p 0 (\<lambda>x. peval (s ! x) a)"
      apply (rule sum_sadd_cong, auto)
      using nth_map[of _ s "(\<lambda>P. peval P a)"] m_def \<open>length s = Suc m\<close> by auto

    have sum_ssub_nzero_map: 
      "(\<Sum>S- p 0 (\<lambda>k. peval (s ! k) a && peval (z ! modifies (p ! k)) a))
     = (\<Sum>S- p 0 (\<lambda>k. map (\<lambda>P. peval P a) s ! k && map (\<lambda>P. peval P a) z ! modifies (p ! k)))"
    proof -
     have 1: "peval (s ! k) a && peval (z ! modifies (p ! k)) a =
           map (\<lambda>P. peval P a) s ! k && map (\<lambda>P. peval P a) z ! modifies (p ! k) "
           if "k < length p" for k
     proof - 
       have "peval (s ! k) a = map (\<lambda>P. peval P a) s ! k"
       using nth_map that ps_lengths by auto
       moreover have "peval (z ! modifies (p ! k)) a 
                      = map (\<lambda>P. peval P a) z ! modifies (p ! k) "
         using nth_map[of "modifies (p!k)" z "(\<lambda>P. peval P a)"] modifies_le_n[of k] that 
         using \<open>length z = n\<close> by auto
       ultimately show ?thesis by auto
     qed
     show ?thesis apply (rule sum_ssub_nzero_cong, auto)
       using 1 by (metis Suc_le_mono Suc_pred less_eq_Suc_le p_len)
    qed

    have sum_ssub_zero_map: 
      "(\<Sum>S0 p 0 (\<lambda>k. peval (s ! k) a && peval e a - peval (z ! modifies (p ! k)) a))
     = (\<Sum>S0 p 0 (\<lambda>k. map (\<lambda>P. peval P a) s ! k && peval e a 
                                                      - map (\<lambda>P. peval P a) z ! modifies (p ! k)))"
    proof -
     have 1: "peval (s ! k) a && peval e a - peval (z ! modifies (p ! k)) a =
           map (\<lambda>P. peval P a) s ! k && peval e a - map (\<lambda>P. peval P a) z ! modifies (p ! k) "
           if "k < length p" for k
     proof - 
       have "peval (s ! k) a = map (\<lambda>P. peval P a) s ! k"
       using nth_map that ps_lengths by auto
       moreover have "peval (z ! modifies (p ! k)) a 
                      = map (\<lambda>P. peval P a) z ! modifies (p ! k) "
         using nth_map[of "modifies (p!k)" z "(\<lambda>P. peval P a)"] modifies_le_n[of k] that 
         using \<open>length z = n\<close> by auto
       ultimately show ?thesis by auto
     qed
     show ?thesis apply (rule sum_ssub_zero_cong, auto)
       using 1 by (metis Suc_le_mono Suc_pred less_eq_Suc_le p_len)
    qed


    have "eval DS a =
              (\<exists>ks. length ks = 2 \<and>
                  eval (s' ! 0 [=] \<^bold>1 [+] b' [*] ([\<Sum>S+] p 0 (!) s') [+] b' [*] Param 0 
                                     [+] b' [*] Param (Suc 0)) (push_list a ks) 
                \<and> eval [polynomial.Param 0 = \<Sum>S- 0 (s' && z0)] (push_list a ks) 
                \<and> eval [polynomial.Param 1 = \<Sum>S0 0 (s' && z1)] (push_list a ks))"
      unfolding DS_def step_relation_def param_0_is_sum_sub_nzero_term_def
        param_1_is_sum_sub_zero_term_def by (simp add: defs) 

    also have "... = (\<exists>ks. length ks = 2 \<and>
         peval (s' ! 0) (push_list a ks) =
         Suc (peval b' (push_list a ks) * peval ([\<Sum>S+] p 0 ((!) s')) (push_list a ks) +
              peval b' (push_list a ks) * push_list a ks 0 +
              peval b' (push_list a ks) * push_list a ks (Suc 0))
          \<and> (peval (Param 0) (push_list a ks) 
              = \<Sum>S- p 0 (\<lambda>k. peval (s' ! k) (push_list a ks) && peval (z0 ! k) (push_list a ks)))
          \<and> (peval (Param 1) (push_list a ks)
              = \<Sum>S0 p 0 (\<lambda>k. peval (s' ! k) (push_list a ks) && peval (z1 ! k) (push_list a ks))))"
      unfolding sum_nzero_unfold sum_zero_unfold by (simp add: defs ) 

    also have "... = (\<exists>ks. length ks = 2 \<and>
         peval (s ! 0) a =
         Suc (peval b a * peval ([\<Sum>S+] p 0 ((!) s')) (push_list a ks) +
              peval b a * push_list a ks 0 +
              peval b a * push_list a ks (Suc 0))
          \<and> (ks!0
              = \<Sum>S- p 0 (\<lambda>k. peval (s' ! k) (push_list a ks) && peval (z0 ! k) (push_list a ks)))
          \<and> (ks!1
              = \<Sum>S0 p 0 (\<lambda>k. peval (s' ! k) (push_list a ks) && peval (z1 ! k) (push_list a ks))))"
      using b'_unfold s'_0_unfold param_0_unfold param_1_unfold by auto

    also have "... = (\<exists>ks. length ks = 2 \<and>
     peval (s ! 0) a =
         Suc (peval b a * \<Sum>S+ p 0 (\<lambda>x. peval (s ! x) a) +
              peval b a * (ks!0) + peval b a * (ks!1))
      \<and> (ks!0 = \<Sum>S- p 0 (\<lambda>k. peval (s' ! k) (push_list a ks) && peval (z0 ! k) (push_list a ks)))
      \<and> (ks!1 = \<Sum>S0 p 0 (\<lambda>k. peval (s' ! k) (push_list a ks) && peval (z1 ! k) (push_list a ks))))"
      using push_list_def sum_sadd_unfold by auto

    also have "... = (\<exists>ks. length ks = 2 \<and>
     peval (s ! 0) a = Suc (peval b a * \<Sum>S+ p 0 (\<lambda>x. peval (s ! x) a)
                     + peval b a * (ks!0) + peval b a * (ks!1))
      \<and> (ks!0 = \<Sum>S- p 0 (\<lambda>k. peval (s ! k) a && peval (z ! modifies (p ! k)) a))
      \<and> (ks!1 = \<Sum>S0 p 0 (\<lambda>k. peval (s ! k) a && peval e a - peval (z ! modifies (p ! k)) a)))"
      using z0sum_unfold z1sum_unfold by auto

    also have "... = (\<exists>ks. length ks = 2 \<and>
      peval (s ! 0) a 
      = Suc (peval b a * \<Sum>S+ p 0 (\<lambda>x. peval (s ! x) a)
      + peval b a * \<Sum>S- p 0 (\<lambda>k. peval (s ! k) a && peval (z ! modifies (p ! k)) a)
      + peval b a * \<Sum>S0 p 0 (\<lambda>k. peval (s ! k) a && peval e a - peval (z ! modifies (p ! k)) a))
      \<and> (ks!0 = \<Sum>S- p 0 (\<lambda>k. peval (s ! k) a && peval (z ! modifies (p ! k)) a))
      \<and> (ks!1 = \<Sum>S0 p 0 (\<lambda>k. peval (s ! k) a && peval e a - peval (z ! modifies (p ! k)) a)))"
      by auto

    also have "... = (peval (s ! 0) a 
      = Suc (peval b a * \<Sum>S+ p 0 (\<lambda>x. peval (s ! x) a)
      + peval b a * \<Sum>S- p 0 (\<lambda>k. peval (s ! k) a && peval (z ! modifies (p ! k)) a)
      + peval b a * \<Sum>S0 p 0 (\<lambda>k. peval (s ! k) a && peval e a - peval (z ! modifies (p ! k)) a)))"
      apply auto
      apply (rule exI[of _ "[(\<Sum>S- p 0 (\<lambda>k. peval (s ! k) a && peval (z ! modifies (p ! k)) a)), 
              \<Sum>S0 p 0 (\<lambda>k. peval (s ! k) a && peval e a - peval (z ! modifies (p ! k)) a) ]"])
      by auto

    also have "... = (map (\<lambda>P. peval P a) s ! 0 = 
     Suc (peval b a * \<Sum>S+ p 0 ((!) (map (\<lambda>P. peval P a) s))  +
          peval b a * \<Sum>S- p 0 (\<lambda>k. map (\<lambda>P. peval P a) s ! k 
                                && map (\<lambda>P. peval P a) z ! modifies (p ! k))  +
          peval b a *
          \<Sum>S0 p 0 (\<lambda>k. map (\<lambda>P. peval P a) s ! k && peval e a 
                                                    - map (\<lambda>P. peval P a) z ! modifies (p ! k)) ))"
      using nth_map[of _ _ "(\<lambda>P. peval P a)"] \<open>length s > 0\<close> 
      using sum_ssub_zero_map sum_sadd_map sum_ssub_nzero_map by auto

    finally show ?thesis unfolding DR_def using rm_eq_fixes_def local.register_machine_axioms 
      rm_eq_fixes.state_0_def by (simp add: defs)
  qed

  moreover have "is_dioph_rel DS"
    unfolding DS_def param_1_is_sum_sub_zero_term_def param_0_is_sum_sub_nzero_term_def
    step_relation_def by (auto simp add: dioph) 

  ultimately show ?thesis
    by (simp add: is_dioph_rel_def)
qed

end

end