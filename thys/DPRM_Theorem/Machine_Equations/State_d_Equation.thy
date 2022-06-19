subsubsection \<open>State d equation\<close>

theory State_d_Equation imports State_0_Equation

begin

context rm_eq_fixes 
begin
  
  text \<open>Equation 4.25\<close>
  definition state_d :: "bool" where
    "state_d \<equiv> \<forall>d>0. d\<le>m \<longrightarrow> s d = b*\<Sum>S+ p d s + b*\<Sum>S- p d (\<lambda>k. s k && z (modifies (p!k)))
                                                 + b*\<Sum>S0 p d (\<lambda>k. s k && (e - z (modifies (p!k))))"

  text \<open>Combining the two\<close>
  definition state_relations_from_recursion :: "bool" where
    "state_relations_from_recursion \<equiv> state_0 \<and> state_d"

end

context register_machine
begin

lemma state_d_dioph:
  fixes b e :: polynomial
  fixes z s :: "polynomial list"
  assumes "length z = n" "length s = Suc m"
  defines "DR \<equiv> LARY (\<lambda>ll. rm_eq_fixes.state_d p (ll!0!0) (ll!0!1)
                                                  (nth (ll!1)) (nth (ll!2))) 
                      [[b, e], z, s]"
  shows "is_dioph_rel DR"
proof - 

  define d_domain where "d_domain \<equiv> [1..<Suc m]"

  define number_of_ex_vars where "number_of_ex_vars = 2 * m"

  have "length d_domain = m"
    unfolding d_domain_def by auto

  define b' e' z' s' where pushed_def: "b' = push_param b number_of_ex_vars" 
                                       "e' = push_param e number_of_ex_vars"
                                       "z' = map (\<lambda>x. push_param x number_of_ex_vars) z" 
                                       "s' = map (\<lambda>x. push_param x number_of_ex_vars) s"

  note e'_def = \<open>e' = push_param e number_of_ex_vars\<close> 

  define z0 z1 where z_def: "z0 \<equiv> map (\<lambda>i. z' ! modifies (p!i)) [0..<Suc m]"
                            "z1 \<equiv> map (\<lambda>i. e' [-] z' ! modifies (p!i)) [0..<Suc m]"

  define sum_ssub_nzero_param_of_state where
    "sum_ssub_nzero_param_of_state \<equiv> (\<lambda>d. Param (d - Suc 0))"
  write sum_ssub_nzero_param_of_state ("\<Sum>S-'_Param _")

  define sum_ssub_zero_param_of_state where
    "sum_ssub_zero_param_of_state \<equiv> (\<lambda>d. Param (m + d - Suc 0))"
  write sum_ssub_zero_param_of_state ("\<Sum>S0'_Param _")

  define param_is_sum_ssub_nzero_term where 
    "param_is_sum_ssub_nzero_term \<equiv> (\<lambda>d::nat. [(\<Sum>S-_Param d) = \<Sum>S- d (s' && z0)])"

  define param_is_sum_ssub_zero_term where
    "param_is_sum_ssub_zero_term \<equiv> (\<lambda>d. [(\<Sum>S0_Param d) = \<Sum>S0 d (s' && z1)])"

  define params_are_sum_terms where
    "params_are_sum_terms \<equiv> [\<forall> in d_domain] (\<lambda>d. param_is_sum_ssub_nzero_term d 
                                             [\<and>] param_is_sum_ssub_zero_term d)"

  define step_relation where
    "step_relation \<equiv> (\<lambda>d. (s'!d) [=] b' [*] ([\<Sum>S+] p d (nth s')) 
                                    [+] b' [*] (\<Sum>S-_Param d)
                                    [+] b' [*] (\<Sum>S0_Param d))"

  define DS where "DS \<equiv> [\<exists>number_of_ex_vars] (([\<forall> in d_domain] (\<lambda>d. step_relation d)) 
                                               [\<and>] params_are_sum_terms)"

  have "length p > 0"
    using p_nonempty by auto 
  hence "m \<ge> 0"
    unfolding m_def by auto
  have "length s' = Suc m" and "length z0 = Suc m" and "length z1 = Suc m"
    unfolding pushed_def z_def using \<open>length s = Suc m\<close> m_def \<open>length p > 0\<close> by auto

  have "eval DS a = eval DR a" for a
  proof - 

    have b'_unfold: "peval b' (push_list a ks) = peval b a"
      if "length ks = number_of_ex_vars" for ks
      unfolding pushed_def using push_push_simp \<open>length d_domain = m\<close> by (metis that)

    have h0: "k < m \<Longrightarrow> d_domain ! k < Suc m" for k
      unfolding d_domain_def apply simp
      using One_nat_def Suc_pred \<open>0 < length p\<close>  add.commute
                    assms(3) d_domain_def less_diff_conv m_def nth_upt upt_Suc_append
      by (smt \<open>length d_domain = m\<close> less_nat_zero_code list.size(3) upt_Suc)

    have s'_unfold: "peval (s' ! (d_domain ! k)) (push_list a ks)
                   = peval (s ! (d_domain ! k)) a"
      if "length ks = number_of_ex_vars" and "k < m" for k ks
    proof -
      from \<open>k < m\<close> have "d_domain ! k < length s" unfolding \<open>length s = Suc m\<close> 
        using h0 by blast

      have suc_k: "([Suc 0..<Suc m]) ! k = Suc k"
        by (metis Suc_leI Suc_pred add_less_cancel_left diff_Suc_1 le_add_diff_inverse nth_upt 
            zero_less_Suc \<open>k < m\<close>)

      have "peval (map (\<lambda>x. push_param x number_of_ex_vars) s ! (d_domain ! k)) (push_list a ks) 
            = list_eval s a (d_domain ! k)"
        using push_push_map_i[of "ks" "number_of_ex_vars" "d_domain!k" s a] 
        using \<open>length ks = number_of_ex_vars\<close> \<open>k < m\<close> h0 \<open>length s = Suc m\<close> by auto
      also have "... = peval (s ! (d_domain ! k)) a"
        unfolding list_eval_def  
        using nth_map [of "d_domain ! k" s "(\<lambda>x. peval x a)"] \<open>d_domain ! k < length s\<close>
        unfolding d_domain_def using \<open>m \<ge> 0\<close> \<open>k < m\<close> suc_k by auto 

      finally show ?thesis unfolding pushed_def by auto
    qed

    have sum_sadd_unfold: "(\<Sum>S+ p (d_domain ! k) (\<lambda>x. peval (s' ! x) (push_list a ks))) 
                         = (\<Sum>S+ p (d_domain ! k) ((!) (map (\<lambda>P. peval P a) s)))"
      if "length ks = number_of_ex_vars" for k ks
      apply (rule sum_sadd_cong, auto) unfolding pushed_def 
      using push_push_map_i[of ks number_of_ex_vars _ s a] \<open>length ks = number_of_ex_vars\<close>
      unfolding list_eval_def by (simp add: \<open>length s = Suc m\<close> m_def)

    have s: "peval (s' ! ka) (push_list a ks) = map (\<lambda>P. peval P a) s ! ka" 
      if "ka < Suc m" and "length ks = number_of_ex_vars" for ka ks
        unfolding pushed_def 
        using push_push_map_i[of ks number_of_ex_vars ka s a] \<open>length ks = number_of_ex_vars\<close>
        using list_eval_def \<open>length s = Suc m\<close> \<open>ka < Suc m\<close> by auto

    have modifies_valid: "modifies (p ! ka) < length z" if "ka < Suc m" for ka
      using modifies_yields_valid_register that unfolding \<open>length z = n\<close> m_def 
      using p_nonempty by auto

    have sum_ssub_nzero_unfold:
      "(\<Sum>S- p (d_domain ! k) (\<lambda>k. peval (s' ! k) (push_list a ks) 
                              && peval (z0 ! k) (push_list a ks)))
     = (\<Sum>S- p (d_domain ! k) (\<lambda>k. map (\<lambda>P. peval P a) s ! k 
                              && map (\<lambda>P. peval P a) z ! modifies (p ! k)))"
      if "length ks = number_of_ex_vars" for k ks
    proof- 
      have z0: "peval (z0 ! ka) (push_list a ks) = map (\<lambda>P. peval P a) z ! modifies (p ! ka)" 
        if "ka < Suc m" for ka
        unfolding z_def pushed_def 
        using push_push_map_i[of ks number_of_ex_vars "modifies (p!ka)" z a] 
              \<open>length ks = number_of_ex_vars\<close> unfolding list_eval_def 
        using \<open>length z0 = Suc m\<close> \<open>ka < Suc m\<close> modifies_valid \<open>0 < length p\<close> m_def map_nth by force

      show ?thesis apply (rule sum_ssub_nzero_cong) using s z0 le_imp_less_Suc m_def that 
        by presburger
    qed

    have sum_ssub_zero_unfold:
      "(\<Sum>S0 p (d_domain ! k) (\<lambda>k. peval (s' ! k) (push_list a ks) 
                                && peval (z1 ! k) (push_list a ks))) 
     = (\<Sum>S0 p (d_domain ! k) (\<lambda>k. map (\<lambda>P. peval P a) s ! k 
                                && peval e a - map (\<lambda>P. peval P a) z ! modifies (p ! k)))"
      if "length ks = number_of_ex_vars" and "k < Suc m" for k ks
    proof-         

      have map: 
        "map (\<lambda>i. e' [-] (z' ! (modifies (p ! i)))) [0..<Suc m] ! ka
         = e' [-] (z' ! modifies (p ! ka))" if "ka < Suc m" for ka
        using nth_map[of ka "[0..<Suc m]" "\<lambda>i. e' [-] z' ! modifies (p ! i)"] \<open>ka < Suc m\<close>
        by (smt (z3) One_nat_def Suc_pred \<open>0 < length p\<close> \<open>m \<ge> 0\<close> le_trans length_map m_def map_nth 
            nth_map upt_Suc_append zero_le_one)

      have "peval (e' [-] (z' ! modifies (p ! ka))) (push_list a ks)
              = peval e a - map (\<lambda>P. peval P a) z ! modifies (p ! ka)" 
        if "ka < Suc m" for ka
        unfolding z_def pushed_def apply (simp add: defs)
        using push_push_simp \<open>length ks = number_of_ex_vars\<close> apply auto
        using push_push_map_i[of ks number_of_ex_vars "modifies (p!ka)" z a]
              \<open>length ks = number_of_ex_vars\<close> modifies_valid \<open>ka < Suc m\<close>
        unfolding list_eval_def using \<open>length z0 = Suc m\<close> \<open>0 < length p\<close> m_def map_nth by auto

      hence z1: "peval (z1 ! ka) (push_list a ks) 
           = peval e a - map (\<lambda>P. peval P a) z ! modifies (p ! ka)" if "ka < Suc m" for ka
        unfolding z_def using map that by auto

      show ?thesis apply (rule sum_ssub_zero_cong) using s z1 le_imp_less_Suc m_def that 
        by presburger
        
    qed

    define sum_ssub_nzero_map where
      "sum_ssub_nzero_map \<equiv> \<lambda>j. \<Sum>S- p j (\<lambda>k. map (\<lambda>P. peval P a) s ! k 
                                                       && map (\<lambda>P. peval P a) z ! modifies (p ! k))"
    define sum_ssub_zero_map where
      "sum_ssub_zero_map \<equiv> \<lambda>j. \<Sum>S0 p j (\<lambda>k. map (\<lambda>P. peval P a) s ! k 
                               && peval e a - map (\<lambda>P. peval P a) z ! modifies (p ! k)) "

    define ks_ex where 
      "ks_ex \<equiv> map sum_ssub_nzero_map d_domain @ map sum_ssub_zero_map d_domain"

    have "length ks_ex = number_of_ex_vars"
      unfolding ks_ex_def number_of_ex_vars_def using \<open>length d_domain = m\<close> by auto

    have ks_ex1:
      "peval (\<Sum>S-_Param (d_domain ! k)) (push_list a ks_ex)
       = \<Sum>S- p (d_domain ! k) (\<lambda>k. map (\<lambda>P. peval P a) s ! k 
                                 && map (\<lambda>P. peval P a) z ! modifies (p ! k))" 
      if "k < m" for k
    proof - 
      have domain_at_k_bound: 
        "d_domain ! k - Suc 0 < length ks_ex" using that \<open>length ks_ex = number_of_ex_vars\<close>
        unfolding number_of_ex_vars_def using h0 by fastforce

      have "peval (\<Sum>S-_Param (d_domain ! k)) (push_list a ks_ex) = ks_ex ! k"
        unfolding push_list_def sum_ssub_nzero_param_of_state_def using that domain_at_k_bound 
        apply auto
        using One_nat_def Suc_mono d_domain_def diff_Suc_1 nth_upt plus_1_eq_Suc by presburger

      also have "... = \<Sum>S- p (d_domain ! k) (\<lambda>k. map (\<lambda>P. peval P a) s ! k 
                                 && map (\<lambda>P. peval P a) z ! modifies (p ! k))" 
        unfolding ks_ex_def 
        unfolding nth_append[of "map sum_ssub_nzero_map d_domain" "map sum_ssub_zero_map d_domain" k]
        using \<open>length d_domain = m\<close> that unfolding sum_ssub_nzero_map_def by auto
      finally show ?thesis by auto
    qed

    have ks_ex2:
      "peval (\<Sum>S0_Param (d_domain ! k)) (push_list a ks_ex)
          = \<Sum>S0 p (d_domain ! k) (\<lambda>k. map (\<lambda>P. peval P a) s ! k 
                                       && peval e a - map (\<lambda>P. peval P a) z ! modifies (p ! k))"
      if "k < m" for k
    proof - 
      have domain_at_k_bound: 
        "m + d_domain ! k - Suc 0 < length ks_ex" using that \<open>length ks_ex = number_of_ex_vars\<close>
        unfolding number_of_ex_vars_def using h0 by fastforce

      have "d_domain ! k \<ge> 1"
        unfolding d_domain_def \<open>k < m\<close> 
        using m_def p_nonempty that by auto

      hence index_calculation: "(m + d_domain ! k - Suc 0) = k + m"
        unfolding d_domain_def
        by (metis (no_types, lifting) Nat.add_diff_assoc One_nat_def Suc_pred add.commute 
            less_diff_conv m_def nth_upt ordered_cancel_comm_monoid_diff_class.le_imp_diff_is_add 
            p_nonempty that)

      have "peval (\<Sum>S0_Param (d_domain ! k)) (push_list a ks_ex) = ks_ex ! (k + m)"
        unfolding push_list_def sum_ssub_zero_param_of_state_def using that domain_at_k_bound 
        by (auto simp: index_calculation)  

      also have "... = \<Sum>S0 p (d_domain ! k) (\<lambda>k. map (\<lambda>P. peval P a) s ! k 
                                       && peval e a - map (\<lambda>P. peval P a) z ! modifies (p ! k))" 
        unfolding ks_ex_def 
        unfolding nth_append[of "map sum_ssub_nzero_map d_domain" "map sum_ssub_zero_map d_domain"]
        using \<open>length d_domain = m\<close> that unfolding sum_ssub_zero_map_def by auto
      finally show ?thesis by auto
    qed

    have all_quantifier_switch: "(\<forall>k<length d_domain. Property (d_domain ! k)) 
                               = (\<forall>d>0. d \<le> m \<longrightarrow> Property d)" for Property
    proof (rule)
      assume asm: "\<forall>k<length d_domain. Property (d_domain ! k)"
      show "\<forall>d>0. d \<le> m \<longrightarrow> Property d" 
      proof (auto)
        fix d
        assume "d > 0" "d \<le> m"
        hence "d - Suc 0 < length d_domain" 
          by (metis Suc_le_eq Suc_pred \<open>length d_domain = m\<close>)
        hence "Property (d_domain ! (d - Suc 0))"
          using asm by auto
        thus "Property d" 
          unfolding d_domain_def
          by (metis One_nat_def Suc_diff_1 \<open>0 < d\<close> \<open>d \<le> m\<close> le_imp_less_Suc nth_upt plus_1_eq_Suc)
      qed
    next
      assume asm: "\<forall>d>0. d \<le> m \<longrightarrow> Property d"
      show "\<forall>k<length d_domain. Property (d_domain ! k)"
      proof (auto)
        fix k
        assume "k < length d_domain"
        hence "d_domain ! k > 0"
          unfolding d_domain_def 
          by (smt (z3) One_nat_def Suc_leI Suc_pred \<open>0 < length p\<close> \<open>length d_domain = m\<close> 
              add_less_cancel_left d_domain_def diff_is_0_eq' gr_zeroI le_add_diff_inverse 
              less_nat_zero_code less_numeral_extra(1) m_def nth_upt)
        moreover have "d_domain ! k \<le> m"
          unfolding d_domain_def using \<open>k < length d_domain\<close> unfolding \<open>length d_domain = m\<close>
          using d_domain_def h0 less_Suc_eq_le by auto
        ultimately show "Property (d_domain ! k)" 
          using asm by auto
      qed
    qed

    have "peval (s!d) a = map (\<lambda>P. peval P a) s ! d" if "d > 0" and "d \<le> m" for d
      using nth_map[of d s "\<lambda>P. peval P a"] that \<open>length s = Suc m\<close> by simp

    (* Start chain of equivalences *)
    have "eval DS a = (\<exists>ks. number_of_ex_vars = length ks 
          \<and> (\<forall>k<length d_domain. eval (step_relation (d_domain ! k)) (push_list a ks))
          \<and> eval params_are_sum_terms (push_list a ks))"
      unfolding DS_def by (simp add: defs)

    also have "... = (\<exists>ks. number_of_ex_vars = length ks \<and>
         (\<forall>k<m.
             peval (s ! (d_domain ! k)) a =
             peval b a * peval ([\<Sum>S+] p (d_domain ! k) ((!) s')) (push_list a ks) +
             peval b a * peval (\<Sum>S-_Param (d_domain ! k)) (push_list a ks) +
             peval b a * peval (\<Sum>S0_Param (d_domain ! k)) (push_list a ks)) \<and>
         eval params_are_sum_terms (push_list a ks))"
      unfolding step_relation_def \<open>length d_domain = m\<close> 
      using b'_unfold s'_unfold by (auto simp: defs)

    also have "... = (\<exists>ks. number_of_ex_vars = length ks \<and>
         (\<forall>k<m.
             peval (s ! (d_domain ! k)) a =
             peval b a * (\<Sum>S+ p (d_domain ! k) (\<lambda>x. peval (s' ! x) (push_list a ks))) +
             peval b a * (peval (\<Sum>S-_Param (d_domain ! k)) (push_list a ks)) +
             peval b a * (peval (\<Sum>S0_Param (d_domain ! k)) (push_list a ks)))
       \<and> (\<forall>k<m.
             peval (\<Sum>S-_Param (d_domain ! k)) (push_list a ks)
                 = \<Sum>S- p (d_domain ! k) (\<lambda>k. peval (s' ! k) (push_list a ks) 
                                           && peval (z0 ! k) (push_list a ks)) 
          \<and> peval (\<Sum>S0_Param (d_domain ! k)) (push_list a ks) 
                 = \<Sum>S0 p (d_domain ! k) (\<lambda>k. peval (s' ! k) (push_list a ks) 
                                           && peval (z1 ! k) (push_list a ks))))"
      unfolding params_are_sum_terms_def param_is_sum_ssub_nzero_term_def 
        param_is_sum_ssub_zero_term_def apply (simp add: defs)
      using sum_rsub_nzero_of_bit_and_eval[of s' z0] sum_rsub_zero_of_bit_and_eval[of s' z1] 
            \<open>length p > 0\<close> \<open>length s' = Suc m\<close> \<open>length z0 = Suc m\<close> \<open>length z1 = Suc m\<close>
      unfolding \<open>length d_domain = m\<close> by (simp add: defs)
 
    also have "... = (\<exists>ks. number_of_ex_vars = length ks \<and>
         (\<forall>k<m.
             peval (s ! (d_domain ! k)) a =
             peval b a * (\<Sum>S+ p (d_domain ! k) ((!) (map (\<lambda>P. peval P a) s)) )
           + peval b a * (\<Sum>S- p (d_domain ! k) (\<lambda>k. map (\<lambda>P. peval P a) s ! k 
                                  && map (\<lambda>P. peval P a) z ! modifies (p ! k)))
           + peval b a * (\<Sum>S0 p (d_domain ! k) (\<lambda>k. map (\<lambda>P. peval P a) s ! k 
                                  && peval e a - map (\<lambda>P. peval P a) z ! modifies (p ! k))))        
       \<and> (\<forall>k<m.
             peval (\<Sum>S-_Param (d_domain ! k)) (push_list a ks)
                 = \<Sum>S- p (d_domain ! k) (\<lambda>k. map (\<lambda>P. peval P a) s ! k 
                                  && map (\<lambda>P. peval P a) z ! modifies (p ! k))  
           \<and> peval (\<Sum>S0_Param (d_domain ! k)) (push_list a ks) 
                 = \<Sum>S0 p (d_domain ! k) (\<lambda>k. map (\<lambda>P. peval P a) s ! k 
                                  && peval e a - map (\<lambda>P. peval P a) z ! modifies (p ! k))))"
      using sum_sadd_unfold sum_ssub_nzero_unfold sum_ssub_zero_unfold by auto

    also have "... = (\<forall>k<m.
             peval (s ! (d_domain ! k)) a =
             peval b a * (\<Sum>S+ p (d_domain ! k) ((!) (map (\<lambda>P. peval P a) s)) )
           + peval b a * (\<Sum>S- p (d_domain ! k) 
                                (\<lambda>k. map (\<lambda>P. peval P a) s ! k 
                                  && map (\<lambda>P. peval P a) z ! modifies (p ! k)))
           + peval b a * (\<Sum>S0 p (d_domain ! k) 
                                (\<lambda>k. map (\<lambda>P. peval P a) s ! k 
                                  && peval e a - map (\<lambda>P. peval P a) z ! modifies (p ! k))))" 
      apply auto
      apply (rule exI[of _ ks_ex]) 
      using \<open>length ks_ex = number_of_ex_vars\<close> ks_ex1 ks_ex2 by auto

    also have "... = (\<forall>d>0. d \<le> m \<longrightarrow>
           peval (s ! d) a
         = peval b a * \<Sum>S+ p d ((!) (map (\<lambda>P. peval P a) s)) 
         + peval b a * \<Sum>S- p d (\<lambda>k. map (\<lambda>P. peval P a) s ! k 
                                     && map (\<lambda>P. peval P a) z ! modifies (p ! k))  
         + peval b a * \<Sum>S0 p d (\<lambda>k. map (\<lambda>P. peval P a) s ! k 
                                     && peval e a - map (\<lambda>P. peval P a) z ! modifies (p ! k)) )"
      using all_quantifier_switch[of "\<lambda>d. peval (s ! d) a =
           peval b a * \<Sum>S+ p d ((!) (map (\<lambda>P. peval P a) s))  +
           peval b a * \<Sum>S- p d (\<lambda>k. map (\<lambda>P. peval P a) s ! k 
           && map (\<lambda>P. peval P a) z ! modifies (p ! k))  +
           peval b a * \<Sum>S0 p d (\<lambda>k. map (\<lambda>P. peval P a) s ! k 
           && peval e a - map (\<lambda>P. peval P a) z ! modifies (p ! k))"] 
      unfolding \<open>length d_domain = m\<close> by auto

    finally show ?thesis 
      unfolding DR_def 
      using local.register_machine_axioms rm_eq_fixes_def[of p n] rm_eq_fixes.state_d_def[of p n]
      apply (simp add: defs)
      using nth_map[of _ s "\<lambda>P. peval P a"] \<open>length s = Suc m\<close> 
      by auto
  qed

  moreover have "is_dioph_rel DS"
  proof - 
    have "is_dioph_rel (param_is_sum_ssub_nzero_term d [\<and>] param_is_sum_ssub_zero_term d)" for d
      unfolding param_is_sum_ssub_nzero_term_def param_is_sum_ssub_zero_term_def 
      by (auto simp: dioph)
    hence 1: "list_all (is_dioph_rel \<circ> (\<lambda>d. param_is_sum_ssub_nzero_term d 
                                     [\<and>] param_is_sum_ssub_zero_term d)) d_domain"
      by (simp add: list.inducts)

    have "is_dioph_rel (step_relation d)" for d
      unfolding step_relation_def by (auto simp: dioph)
    hence 2: "list_all (is_dioph_rel \<circ> step_relation) d_domain"
      by (simp add: list.inducts)

    show ?thesis 
    unfolding DS_def params_are_sum_terms_def by (auto simp: dioph 1 2)
  qed

  ultimately show ?thesis using is_dioph_rel_def by auto
qed


lemma state_relations_from_recursion_dioph:
  fixes b e :: polynomial
  fixes z s :: "polynomial list"
  assumes "length z = n" "length s = Suc m"
  defines "DR \<equiv> LARY (\<lambda>ll. rm_eq_fixes.state_relations_from_recursion p (ll!0!0) (ll!0!1)
                                                                        (nth (ll!1)) (nth (ll!2))) 
                      [[b, e], z, s]"
  shows "is_dioph_rel DR"
proof - 

  define DS where "DS \<equiv> (LARY (\<lambda>ll. rm_eq_fixes.state_0 p (ll!0!0) (ll!0!1)
                            (nth (ll!1)) (nth (ll!2))) [[b, e], z, s])
                     [\<and>](LARY (\<lambda>ll. rm_eq_fixes.state_d p (ll!0!0) (ll!0!1) (nth (ll!1)) 
                            (nth (ll!2))) [[b, e], z, s])"

  have "eval DS a = eval DR a" for a 
    unfolding DS_def DR_def
    using local.register_machine_axioms rm_eq_fixes_def 
          rm_eq_fixes.state_relations_from_recursion_def 
    using assms by (simp add: defs)

  moreover have "is_dioph_rel DS"
    unfolding DS_def apply (rule and_dioph) using assms state_0_dioph state_d_dioph by blast+

  ultimately show ?thesis using is_dioph_rel_def by auto
qed

end

end
