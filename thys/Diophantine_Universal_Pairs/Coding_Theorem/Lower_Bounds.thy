theory Lower_Bounds
  imports Coding_Theorem_Definitions "../Coding/Lemma_1_8_Coding" "Digit_Expansions.Bits_Digits"
          "HOL-Library.Rewrite" "../Coding/Suitable_For_Coding"
begin

subsection \<open>Lower bounds on the defined variables\<close>

lemma (in coding_variables) defs_non_negative: 
  fixes g :: int
  assumes "a \<ge> 0"
  assumes "f > 0"
  assumes "g \<ge> 0"
  assumes "\<delta> > 0"
  assumes "P_coeff (replicate (\<nu>+1) 0) > 0"
  shows "\<B> > 0" and "N \<ge> 2" and "R g > 0" and "S g \<ge> 0" and "T \<ge> 0" and "N0 \<ge> 1"
proof -
  note simps = eval_def insertion_simps comp_def

  have "\<beta> > 0"
    unfolding \<beta>_def by auto
  hence "\<beta> \<ge> 0"
    by auto
  have b: "b > 2"
    unfolding b_def apply (simp add: assms)
    using assms(1-2) by (smt (verit) mult_le_cancel_right2)
  moreover have "\<B> \<ge> b"
    unfolding \<B>_def
    using \<open>\<delta> > 0\<close> \<open>\<beta> > 0\<close>
    by (smt (verit, del_insts) calculation comp_apply mult_le_cancel_right1 
        of_nat_0_less_iff self_le_power)
  ultimately have "\<B> > 2"
    by auto
  then show BB: "\<B> > 0"
    by auto
  show N0: "N0 \<ge> 1"
    unfolding N0_def
    using \<open>\<B> > 0\<close>
    by (simp add: int_one_le_iff_zero_less)
  show N: "N \<ge> 2"
    using \<open>N0 \<ge> 1\<close> \<open>\<B> > 0\<close>
    unfolding N_def N1_def eval_def
    by simp (smt (z3) mult_pos_pos zero_less_power)
  have m: "(m j) \<ge> 0" for j
    unfolding m_def
    using \<open>\<B> \<ge> b\<close> \<open>\<B> > 2\<close>
    by (auto simp: eval_def)
  have M: "M \<ge> 0"
    unfolding M_def
    using m BB by (simp add: sum_nonneg)
  show "T \<ge> 0"
    unfolding T_def
    using N0 M BB \<open>2 < \<B>\<close> by force

  have "K g \<ge> 0"
  proof - 
    have "2 \<le> int (Suc \<delta>)"
      using \<open>\<delta> > 0\<close> by auto
    have "1 < nat \<B>"
      using \<open>\<B> > 2\<close>
      unfolding \<B>_def eval_def by auto
    hence "\<B> \<ge> 2"
      by auto

    have "even \<beta>"
      by (simp add: \<beta>_def r_pos[OF \<open>\<delta> > 0\<close>])
    have "even \<B>"
      unfolding \<B>_def simps \<beta>_def
      using r_pos[OF \<open>\<delta> > 0\<close>]
      by simp

    have c_bound: "c g > 0"
      unfolding c_def using BB
      by (simp add: add_strict_increasing assms(1) assms(3))

    (* This follows from the definition of \<beta> and r. *)
    have \<delta>_\<L>_bound: "fact \<delta> * \<L> < \<B> - 1"
    proof - 
      have "fact \<delta> * \<L> < fact \<delta> * \<L> * (\<nu> + 3) ^ \<delta> * b ^ \<delta>"
        using \<open>\<delta> > 0\<close> \<L>_pos[OF \<open>\<delta> > 0\<close>] 
        by simp (smt (verit) b eval_def less_1_mult o_apply of_nat_less_0_iff one_less_power)
      hence "fact \<delta> * \<L> < 2 * fact \<delta> * \<L> * (\<nu> + 3) ^ \<delta> * b ^ \<delta> - 1"
        by linarith
      moreover have "2 * fact \<delta> * \<L> * (\<nu> + 3) ^ \<delta> * b ^ \<delta> < 4 ^ r * b ^ \<delta>"
        using \<beta>_lower_bound[unfolded \<beta>_def]
        by (smt (z3) b fact_2 int_eq_iff_numeral less_imp_of_nat_less mult_of_nat_commute 
            numeral_Bit0 of_nat_fact of_nat_power zero_less_power zmult_zless_mono2)
      ultimately show ?thesis
        unfolding \<B>_def \<beta>_def
        by auto
    qed

    have D_bound: "D > 0"
    proof -
      let ?i0 = "replicate (\<nu>+1) 0"
      let ?a0 = "P_coeff ?i0"

      have "?a0 > 0"
        using assms by auto

      have h0: "i\<in>\<delta>_tuples - {replicate (\<nu>+1) 0} \<Longrightarrow> sum_list i > 0" for i
        apply (rule ccontr)
        unfolding \<delta>_tuples_def using replicate_eqI by fastforce

      have h1: "(\<Sum>r=0..(\<delta>+1)^(\<nu>+1)-1. \<B> ^ r) > 0"
        apply (subst sum_pos)
        using \<B>_def BB eval_def by (auto)

      have h2: "D_precoeff ?i0 * P_coeff ?i0 * \<B> ^ D_exponent ?i0
                = fact \<delta> * ?a0 * \<B> ^ ((\<delta>+1)^(\<nu>+1))"
      proof -
        have "(\<Sum>s\<le>\<nu>. ?i0 ! s * Suc \<delta> ^ s) = 0"
          by auto (metis List.nth_replicate le_imp_less_Suc replicate_Suc)
        thus ?thesis
          unfolding D_precoeff_def D_exponent_def
          using \<open>?a0 > 0\<close> apply (simp add: sum_list_replicate)
          by (simp add: mfact_def \<B>_def n_def)
      qed

      have h3: "?i0 \<in> \<delta>_tuples"
        by (simp add: sum_list_replicate \<delta>_tuples_def)

      have h4: "(\<Sum>i\<in>\<delta>_tuples - {?i0}. \<B> ^ D_exponent i) \<le> (\<Sum>r=0..(\<delta>+1)^(\<nu>+1)-1. \<B> ^ r)"
      proof -
        have h41: "D_exponent ` (\<delta>_tuples - {?i0}) \<subseteq> {0..(\<delta>+1)^(\<nu>+1)-1}"
        proof -
          {
            fix x
            assume asm: "x \<in> (\<delta>_tuples - {?i0})"
            hence "length x = Suc \<nu>"
              unfolding \<delta>_tuples_def by simp
            have x_nonzero: "\<exists>s\<le>\<nu>. x ! s > 0"
              apply (rule ccontr)
              using h0[OF asm]
              by (simp add: sum_list_sum_nth \<open>length x = Suc \<nu>\<close>)
            then obtain i where i: "i \<le> \<nu> \<and> x ! i > 0"
              by auto
            have "(\<Sum>s\<le>\<nu>. x ! s * Suc \<delta> ^ s) > 0"
                using x_nonzero by (subst sum_pos2[of _ i], auto simp: i)
          } note a = this

          from a show ?thesis
            unfolding D_exponent_def
            apply (simp add: n_def)
            using diff_le_mono2 by fastforce
        qed

        have "(\<Sum>i\<in>\<delta>_tuples - {?i0}. \<B> ^ D_exponent i) 
              = sum ((^) \<B> \<circ> D_exponent) (\<delta>_tuples - {?i0})"
          by auto
        also have "... = sum ((^) \<B>) (D_exponent ` (\<delta>_tuples - {?i0}))"
          apply (subst sum.reindex)
          using D_exponent_injective'[OF \<open>\<delta> > 0\<close>] by auto
        also have "... \<le> sum ((^) \<B>) {0..(\<delta>+1)^(\<nu>+1)-1}"
          apply (subst sum_mono2)
          using h41 \<open>\<B> \<ge> 2\<close> by auto
        finally show ?thesis
          by auto
      qed

      have "\<bar>D - fact \<delta> * ?a0 * \<B> ^ ((\<delta>+1)^(\<nu>+1))\<bar>
            = \<bar>(\<Sum>i\<in>\<delta>_tuples - {?i0}. D_precoeff i * P_coeff i * \<B> ^ D_exponent i)\<bar>"
        apply (subst abs_eq_iff, rule disjI1)
        unfolding D_def eval_def apply simp
        apply (subst sum.remove[of "\<delta>_tuples" "?i0"])
        using h2 h3  \<open>?a0 > 0\<close> by auto
      also have "... \<le> (\<Sum>i\<in>\<delta>_tuples - {?i0}. \<bar>D_precoeff i * P_coeff i *
                                              \<B> ^ D_exponent i\<bar>)"
        by auto
      also have "... \<le> (\<Sum>i\<in>\<delta>_tuples - {?i0}. \<bar>D_precoeff i\<bar> * \<bar>P_coeff i\<bar> *
                                              \<bar>\<B>\<bar> ^ D_exponent i)"
        apply (rule sum_mono)
        by (auto simp: abs_mult power_abs)
      also have "... \<le> (\<Sum>i\<in>\<delta>_tuples - {?i0}. fact \<delta> * \<bar>P_coeff i\<bar> * \<bar>\<B>\<bar> ^ D_exponent i)"
        apply (rule sum_mono)
        apply (frule h0)
        unfolding \<delta>_tuples_def
        by auto (smt (verit, best) \<B>_def D_precoeff_bound mult_right_mono zero_le_power)
      also have "... \<le> (\<Sum>i\<in>\<delta>_tuples - {?i0}. fact \<delta> * \<L> * \<B> ^ D_exponent i)"
        apply (rule sum_mono)
        using \<B>_def BB eval_def
        by (simp add: \<L>_ge_P_coeff mult_right_mono)
      also have "... = fact \<delta> * \<L> * (\<Sum>i\<in>\<delta>_tuples - {?i0}. \<B> ^ D_exponent i)"
        by (simp add: sum_distrib_left)
      also have "... \<le> fact \<delta> * \<L> * (\<Sum>r=0..(\<delta>+1)^(\<nu>+1)-1. \<B> ^ r)"
        using h4 by (simp add: \<L>_pos[OF \<open>\<delta> > 0\<close>])
      also have "... = (\<Sum>r=0..(\<delta>+1)^(\<nu>+1)-1. fact \<delta> * \<L> * \<B> ^ r)"
        by (simp add: sum_distrib_left)
      also have "... \<le> (\<Sum>r=0..(\<delta>+1)^(\<nu>+1)-1. (\<B> - 1) * \<B> ^ r)"
        apply (rule sum_mono)
        using \<delta>_\<L>_bound h1 \<open>1 < nat \<B>\<close> by fastforce
      also have "... < \<B> ^ ((\<delta>+1)^(\<nu>+1))"
        using series_bound[OF \<open>\<B> \<ge> 2\<close>, of "(\<delta> + 1) ^ (\<nu> + 1) - 1" "\<lambda>x. \<B> - 1"] by auto
      finally have "\<bar>D - fact \<delta> * ?a0 * \<B> ^ ((\<delta>+1)^(\<nu>+1))\<bar> < \<B> ^ ((\<delta>+1)^(\<nu>+1))"
        by auto

      hence "fact \<delta> * ?a0 * \<B> ^ ((\<delta>+1)^(\<nu>+1)) - D < \<B> ^ ((\<delta>+1)^(\<nu>+1))"
        by auto
      hence "D > (fact \<delta> * ?a0 - 1) * \<B> ^ ((\<delta>+1)^(\<nu>+1))"
        by (simp add: int_distrib(3))

      thus ?thesis
        using \<open>?a0 > 0\<close> BB
        unfolding \<B>_def eval_def
        by (smt (verit, ccfv_SIG) fact_gt_zero mult_le_0_iff mult_nonneg_nonneg o_apply zero_le_power)
    qed

    moreover have "(\<Sum>i = 0..(2 * \<delta> + 1) * n \<nu>. of_nat (\<beta> div 2) * b ^ \<delta> * \<B> ^ i) \<ge> 0"
      using BB \<open>\<beta> \<ge> 0\<close> b
      unfolding eval_def
      apply simp
      by (rule sum_nonneg, simp)

    ultimately show ?thesis
      using \<open>\<delta> > 0\<close> c_bound D_bound
      unfolding K_def eval_def
      by auto
  qed

  show "S g \<ge> 0"
    unfolding S_def using N0
    by (simp add: \<open>0 \<le> K g\<close> assms(3))
  
  show "R g > 0"
    unfolding R_def
    using \<open>T \<ge> 0\<close> \<open>S g \<ge> 0\<close> \<open>N \<ge> 2\<close> by auto
qed

lemma (in coding_variables) lower_bounds: 
  fixes g :: int
  assumes "a \<ge> 0"
  assumes "f > 0"
  assumes "g \<ge> 0"
  assumes "\<delta> > 0"
  assumes p0: "P_coeff (replicate (\<nu>+1) 0) > 0"
  shows "X g \<ge> 3 * b" and "Y \<ge> 2^8" and "Y \<ge> b"
proof -
  note nonneg = defs_non_negative[OF assms(1-4)]
  note simps = eval_def insertion_simps comp_def

  have "\<beta> > 0"
    unfolding \<beta>_def by auto
  have "b \<le> \<B>"
    unfolding \<B>_def
    using nonneg[OF p0] \<open>\<delta> > 0\<close> \<open>\<beta> > 0\<close>
    by (smt (verit, del_insts) \<B>_def comp_apply insertion_mult insertion_of_nat insertion_pow
            mult_le_cancel_right1 of_nat_0_less_iff self_le_power)

  from \<open>b \<le> \<B>\<close> have "3 * b \<le> 4 * \<B>"
    using nonneg(1)[OF p0] by auto
  also have "... \<le> N1"
    unfolding N1_def 
    using nonneg[OF p0] by auto
  also have "... \<le> N"
    unfolding N_def 
    using nonneg(2,6)[OF p0] N_def mult_le_cancel_right1 by force
  also have "... \<le> R g"
    unfolding R_def 
    using nonneg(2,4,5)[OF p0]
    using comp_apply mult_le_cancel_right1
    by (smt (verit) insertion_of_int of_int_1)
  also have "... \<le> X g"
    unfolding X_def 
    using nonneg[OF p0] by auto
  finally show "X g \<ge> 3 * b" .

  have "b \<ge> 2"
    unfolding b_def apply (simp add: assms)
    using assms(1-2) by (smt (verit) mult_le_cancel_right2)
  with \<open>b \<le> \<B>\<close> have "\<B> \<ge> 2"
    by auto
  hence "N0 \<ge> 2"
    unfolding N0_def 
    using \<open>\<delta> > 0\<close>
    by auto (smt (verit, del_insts) mult_le_cancel_right2 zero_less_power)
  moreover from \<open>\<B> \<ge> 2\<close> have "N1 \<ge> 2^3"
    unfolding N1_def 
    using \<open>\<delta> > 0\<close>
    by auto (smt (verit, del_insts) mult_le_cancel_right2 zero_less_power)
  ultimately have "N \<ge> 2^4"
    unfolding N_def 
    by (smt (verit, del_insts) mult_left_mono mult_right_mono not_exp_less_eq_0_int
            power3_eq_cube power4_eq_xxxx power_commuting_commutes)
  hence "Y \<ge> (2^4)^2"
    unfolding Y_def 
    unfolding power2_eq_square
    using mult_mono' by fastforce
  then show "Y \<ge> 2^8"
    by auto

  from \<open>b \<le> \<B>\<close> have "b \<le> N0"
    unfolding N0_def 
    using nonneg[OF p0]
    by (smt (verit) add_gr_0 comp_apply self_le_power zero_less_one)
  also have "... \<le> N"
    unfolding N_def 
    using nonneg(6)[OF p0] \<open>2 ^ 3 \<le> N1\<close> by auto
  also have "... \<le> Y"
    unfolding Y_def 
    by (smt (verit) pos2 power2_less_0 self_le_power)
  finally show "Y \<ge> b" .
qed

end