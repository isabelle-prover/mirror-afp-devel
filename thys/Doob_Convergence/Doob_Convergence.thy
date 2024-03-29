(*
  Author:   Ata Keskin, TU München
*)
section \<open>Doob's First Martingale Convergence Theorem\<close>
theory Doob_Convergence
  imports Upcrossing
begin

context nat_finite_filtered_measure
begin

text \<open>Doob's martingale convergence theorem states that, if we have a submartingale where the supremum over the mean of the positive parts is finite, then the limit process exists almost surely and is integrable. 
    Furthermore, the limit process is measurable with respect to the smallest \<open>\<sigma>\<close>-algebra containing all of the \<open>\<sigma>\<close>-algebras in the filtration. 
    The argumentation below is taken mostly from \<^cite>\<open>durrett2019probability\<close>.\<close>

theorem submartingale_convergence_AE:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes "submartingale M F 0 X" 
      and "\<And>n. (\<integral>\<omega>. max 0 (X n \<omega>) \<partial>M) \<le> C"
    obtains X\<^sub>l\<^sub>i\<^sub>m where "AE \<omega> in M. (\<lambda>n. X n \<omega>) \<longlonglongrightarrow> X\<^sub>l\<^sub>i\<^sub>m \<omega>" 
                      "integrable M X\<^sub>l\<^sub>i\<^sub>m" 
                      "X\<^sub>l\<^sub>i\<^sub>m \<in> borel_measurable (F\<^sub>\<infinity>)"
proof -
  interpret submartingale_linorder M F 0 X unfolding submartingale_linorder_def by (rule assms)

  \<comment> \<open>We first show that the number of upcrossings has to be finite using the upcrossing inequality we proved above.\<close>

  have finite_upcrossings: "AE \<omega> in M. upcrossings X a b \<omega> \<noteq> \<infinity>" if "a < b" for a b
  proof -
    have C_nonneg: "C \<ge> 0" using assms(2) by (meson Bochner_Integration.integral_nonneg linorder_not_less max.cobounded1 order_less_le_trans)
    {
      fix n
      have "(\<integral>\<^sup>+\<omega>. max 0 (X n \<omega> - a) \<partial>M) \<le> (\<integral>\<^sup>+\<omega>. max 0 (X n \<omega>) + \<bar>a\<bar> \<partial>M)" by (fastforce intro: nn_integral_mono ennreal_leI)
      also have "... = (\<integral>\<^sup>+\<omega>. max 0 (X n \<omega>) \<partial>M) + \<bar>a\<bar> * emeasure M (space M)" by (simp add: nn_integral_add)
      also have "... = (\<integral>\<omega>. max 0 (X n \<omega>) \<partial>M) + \<bar>a\<bar> * emeasure M (space M)" using integrable by (simp add: nn_integral_eq_integral)
      also have "... \<le> C + \<bar>a\<bar> * emeasure M (space M)" using assms(2) ennreal_leI by simp
      finally have "(\<integral>\<^sup>+\<omega>. max 0 (X n \<omega> - a) \<partial>M) \<le> C + \<bar>a\<bar> * enn2real (emeasure M (space M))" using finite_emeasure_space C_nonneg by (simp add: ennreal_enn2real_if ennreal_mult)
    }
    hence "(SUP N. \<integral>\<^sup>+ x. ennreal (max 0 (X N x - a)) \<partial>M) / (b - a) \<le> ennreal (C + \<bar>a\<bar> * enn2real (emeasure M (space M))) / (b - a)" by (fast intro: divide_right_mono_ennreal Sup_least)
    moreover have "ennreal (C + \<bar>a\<bar> * enn2real (emeasure M (space M))) / (b - a) < \<infinity>" using that C_nonneg by (subst divide_ennreal) auto
    moreover have "integral\<^sup>N M (upcrossings X a b) \<le> (SUP N. \<integral>\<^sup>+ x. ennreal (max 0 (X N x - a)) \<partial>M) / (b - a)"
      using upcrossing_inequality_Sup[OF assms(1), of b a, THEN divide_right_mono_ennreal, of "b - a"]
            ennreal_mult_divide_eq mult.commute[of "ennreal (b - a)"] that by simp
    ultimately show ?thesis using upcrossings_measurable adapted_process_axioms that by (intro nn_integral_noteq_infinite) auto
  qed

  \<comment> \<open>Since the number of upcrossings are finite, limsup and liminf have to agree almost everywhere. To show this we consider the following countable set, which has zero measure.\<close>

  define S where "S = ((\<lambda>(a :: real, b). {\<omega> \<in> space M. liminf (\<lambda>n. ereal (X n \<omega>)) < ereal a \<and> ereal b < limsup (\<lambda>n. ereal (X n \<omega>))}) ` {(a, b) \<in> \<rat> \<times> \<rat>. a < b})"

  have "(0, 1) \<in> {(a :: real, b). (a, b) \<in> \<rat> \<times> \<rat> \<and> a < b}" unfolding Rats_def by simp
  moreover have "countable {(a, b). (a, b) \<in> \<rat> \<times> \<rat> \<and> a < b}" by (blast intro: countable_subset[OF _ countable_SIGMA[OF countable_rat countable_rat]])
  ultimately have from_nat_into_S: "range (from_nat_into S) = S" "from_nat_into S n \<in> S" for n 
    unfolding S_def
    by (auto intro!: range_from_nat_into from_nat_into simp only: Rats_def)
  {
    fix a b :: real
    assume a_less_b: "a < b"
    then obtain N where N: "x \<in> space M - N \<Longrightarrow> upcrossings X a b x \<noteq> \<infinity>" "N \<in> null_sets M" for x using AE_E3[OF finite_upcrossings] by blast
    {
      fix \<omega>
      assume liminf_limsup: "liminf (\<lambda>n. X n \<omega>) < a" "b < limsup (\<lambda>n. X n \<omega>)"
      have "upcrossings X a b \<omega> = \<infinity>"
      proof -
        {
          fix n
          have "\<exists>m. upcrossings_before X a b m \<omega> \<ge> n"
          proof (induction n)
            case 0
            have "Sup {n. upcrossing X a b 0 n \<omega> < 0} = 0" by simp
            then show ?case unfolding upcrossings_before_def by blast
          next
            case (Suc n)
            then obtain m where m: "n \<le> upcrossings_before X a b m \<omega>" by blast
            obtain l where l: "l \<ge> m" "X l \<omega> < a" using liminf_upper_bound[OF liminf_limsup(1), of m] nless_le by auto
            obtain u where u: "u \<ge> l" "X u \<omega> > b" using limsup_lower_bound[OF liminf_limsup(2), of l] nless_le by auto
            show ?case using upcrossings_before_less_exists_upcrossing[OF a_less_b, where ?X=X, OF l u] m by (metis Suc_leI le_neq_implies_less)
          qed
        }
        thus ?thesis unfolding upcrossings_def by (simp add: ennreal_SUP_eq_top)
      qed
    }
    hence "{\<omega> \<in> space M. liminf (\<lambda>n. ereal (X n \<omega>)) < ereal a \<and> ereal b < limsup (\<lambda>n. ereal (X n \<omega>))} \<subseteq> N" using N by blast
    moreover have "{\<omega> \<in> space M. liminf (\<lambda>n. ereal (X n \<omega>)) < ereal a \<and> ereal b < limsup (\<lambda>n. ereal (X n \<omega>))} \<inter> N \<in> null_sets M" by (force intro: null_set_Int1[OF N(2)])
    ultimately have "emeasure M {\<omega> \<in> space M. liminf (\<lambda>n. ereal (X n \<omega>)) < a \<and> b < limsup (\<lambda>n. ereal (X n \<omega>))} = 0" by (simp add: Int_absorb1 Int_commute null_setsD1)  
  }
  hence "emeasure M (from_nat_into S n) = 0" for n using from_nat_into_S(2)[of n] unfolding S_def by force
  moreover have "S \<subseteq> M" unfolding S_def by force
  ultimately have "emeasure M (\<Union> (range (from_nat_into S))) = 0" using from_nat_into_S by (intro emeasure_UN_eq_0) auto
  moreover have "(\<Union> S) = {\<omega> \<in> space M. liminf (\<lambda>n. ereal (X n \<omega>)) \<noteq> limsup (\<lambda>n. ereal (X n \<omega>))}" (is "?L = ?R")
  proof -
    {
      fix \<omega>
      assume asm: "\<omega> \<in> ?L"
      then obtain a b :: real where "a < b" "liminf (\<lambda>n. ereal (X n \<omega>)) < ereal a \<and> ereal b < limsup (\<lambda>n. ereal (X n \<omega>))" unfolding S_def by blast
      hence "liminf (\<lambda>n. ereal (X n \<omega>)) \<noteq> limsup (\<lambda>n. ereal (X n \<omega>))" using ereal_less_le order.asym by fastforce
      hence "\<omega> \<in> ?R" using asm unfolding S_def by blast
    }
    moreover
    {
      fix \<omega>
      assume asm: "\<omega> \<in> ?R"
      hence "liminf (\<lambda>n. ereal (X n \<omega>)) < limsup (\<lambda>n. ereal (X n \<omega>))" using Liminf_le_Limsup[of sequentially] less_eq_ereal_def by auto
      then obtain a' where a': "liminf (\<lambda>n. ereal (X n \<omega>)) < ereal a'" "ereal a' < limsup (\<lambda>n. ereal (X n \<omega>))" using ereal_dense2 by blast
      then obtain b' where b': "ereal a' < ereal b'" "ereal b' < limsup (\<lambda>n. ereal (X n \<omega>))" using ereal_dense2 by blast
      hence "a' < b'" by simp
      then obtain a where a: "a \<in> \<rat>" "a' < a" "a < b'" using Rats_dense_in_real by blast
      then obtain b where b: "b \<in> \<rat>" "a < b" "b < b'" using Rats_dense_in_real by blast
      have "liminf (\<lambda>n. ereal (X n \<omega>)) < ereal a" using a a' le_ereal_less order_less_imp_le by meson
      moreover have "ereal b < limsup (\<lambda>n. ereal (X n \<omega>))" using b b' order_less_imp_le ereal_less_le by meson
      ultimately have "\<omega> \<in> ?L" unfolding S_def using a b asm by blast
    }
    ultimately show ?thesis by blast
  qed
  ultimately have "emeasure M {\<omega> \<in> space M. liminf (\<lambda>n. ereal (X n \<omega>)) \<noteq> limsup (\<lambda>n. ereal (X n \<omega>))} = 0" using from_nat_into_S by argo
  hence liminf_limsup_AE: "AE \<omega> in M. liminf (\<lambda>n. X n \<omega>) = limsup (\<lambda>n. X n \<omega>)" by (intro AE_iff_measurable[THEN iffD2, OF _ refl]) auto
  hence convergent_AE: "AE \<omega> in M. convergent (\<lambda>n. ereal (X n \<omega>))" using convergent_ereal by fastforce

  \<comment> \<open>Hence the limit exists almost everywhere.\<close>

  have bounded_pos_part: "ennreal (\<integral>\<omega>. max 0 (X n \<omega>) \<partial>M) \<le> ennreal C" for n using assms(2) ennreal_leI by blast

  \<comment> \<open>Integral of positive part is \<open>< \<infinity>\<close>.\<close>

  {
    fix \<omega>
    assume asm: "convergent (\<lambda>n. ereal (X n \<omega>))"
    hence "(\<lambda>n. max 0 (ereal (X n \<omega>))) \<longlonglongrightarrow> max 0 (lim (\<lambda>n. ereal (X n \<omega>)))" 
      using convergent_LIMSEQ_iff isCont_tendsto_compose continuous_max continuous_const continuous_ident continuous_at_e2ennreal
      by fast
    hence "(\<lambda>n. e2ennreal (max 0 (ereal (X n \<omega>)))) \<longlonglongrightarrow> e2ennreal (max 0 (lim (\<lambda>n. ereal (X n \<omega>))))" 
      using isCont_tendsto_compose continuous_at_e2ennreal by blast
    moreover have "lim (\<lambda>n. e2ennreal (max 0 (ereal (X n \<omega>)))) = e2ennreal (max 0 (lim (\<lambda>n. ereal (X n \<omega>))))" using limI calculation by blast
    ultimately have "e2ennreal (max 0 (liminf (\<lambda>n. ereal (X n \<omega>)))) = liminf (\<lambda>n. e2ennreal (max 0 (ereal (X n \<omega>))))" using convergent_liminf_cl by (metis asm convergent_def limI)
  }
  hence "(\<integral>\<^sup>+\<omega>. e2ennreal (max 0 (liminf (\<lambda>n. ereal (X n \<omega>)))) \<partial>M) = (\<integral>\<^sup>+\<omega>. liminf (\<lambda>n. e2ennreal (max 0 (ereal (X n \<omega>)))) \<partial>M)" using convergent_AE by (fast intro: nn_integral_cong_AE)
  moreover have "(\<integral>\<^sup>+\<omega>. liminf (\<lambda>n. e2ennreal (max 0 (ereal (X n \<omega>)))) \<partial>M) \<le> liminf (\<lambda>n. (\<integral>\<^sup>+\<omega>. e2ennreal (max 0 (ereal (X n \<omega>))) \<partial>M))" 
    by (intro nn_integral_liminf) auto
  moreover have "(\<integral>\<^sup>+\<omega>. e2ennreal (max 0 (ereal (X n \<omega>))) \<partial>M) = ennreal (\<integral>\<omega>. max 0 (X n \<omega>) \<partial>M)" for n 
    using e2ennreal_ereal ereal_max_0
    by (subst nn_integral_eq_integral[symmetric]) (fastforce intro!: nn_integral_cong integrable | presburger)+
  moreover have liminf_pos_part_finite: "liminf (\<lambda>n. ennreal (\<integral>\<omega>. max 0 (X n \<omega>) \<partial>M)) < \<infinity>" 
    unfolding liminf_SUP_INF 
    using Inf_lower2[OF _ bounded_pos_part] 
    by (intro order.strict_trans1[OF Sup_least, of _ "ennreal C"]) (metis (mono_tags, lifting) atLeast_iff imageE image_eqI order.refl, simp)
  ultimately have pos_part_finite: "(\<integral>\<^sup>+\<omega>. e2ennreal (max 0 (liminf (\<lambda>n. ereal (X n \<omega>)))) \<partial>M) < \<infinity>" by force

  \<comment> \<open>Integral of negative part is \<open>< \<infinity>\<close>.\<close>

  {
    fix \<omega>
    assume asm: "convergent (\<lambda>n. ereal (X n \<omega>))"
    hence "(\<lambda>n. - min 0 (ereal (X n \<omega>))) \<longlonglongrightarrow> - min 0 (lim (\<lambda>n. ereal (X n \<omega>)))" 
      using convergent_LIMSEQ_iff isCont_tendsto_compose continuous_min continuous_const continuous_ident continuous_at_e2ennreal
      by fast
    hence "(\<lambda>n. e2ennreal (- min 0 (ereal (X n \<omega>)))) \<longlonglongrightarrow> e2ennreal (- min 0 (lim (\<lambda>n. ereal (X n \<omega>))))" 
      using isCont_tendsto_compose continuous_at_e2ennreal by blast
    moreover have "lim (\<lambda>n. e2ennreal (- min 0 (ereal (X n \<omega>)))) = e2ennreal (- min 0 (lim (\<lambda>n. ereal (X n \<omega>))))" using limI calculation by blast
    ultimately have "e2ennreal (- min 0 (liminf (\<lambda>n. ereal (X n \<omega>)))) = liminf (\<lambda>n. e2ennreal (- min 0 (ereal (X n \<omega>))))" using convergent_liminf_cl by (metis asm convergent_def limI)
  }
  hence "(\<integral>\<^sup>+\<omega>. e2ennreal (- min 0 (liminf (\<lambda>n. ereal (X n \<omega>)))) \<partial>M) = (\<integral>\<^sup>+\<omega>. liminf (\<lambda>n. e2ennreal (- min 0 (ereal (X n \<omega>)))) \<partial>M)" using convergent_AE by (fast intro: nn_integral_cong_AE)
  moreover have "(\<integral>\<^sup>+\<omega>. liminf (\<lambda>n. e2ennreal (- min 0 (ereal (X n \<omega>)))) \<partial>M) \<le> liminf (\<lambda>n. (\<integral>\<^sup>+\<omega>. e2ennreal (- min 0 (ereal (X n \<omega>))) \<partial>M))" 
    by (intro nn_integral_liminf) auto
  moreover have "(\<integral>\<^sup>+\<omega>. e2ennreal (- min 0 (ereal (X n \<omega>))) \<partial>M) = (\<integral>\<omega>. max 0 (X n \<omega>) \<partial>M) - (\<integral>\<omega>. X n \<omega> \<partial>M)" for n
  proof -
    have *: "(- min 0 c) = max 0 c - c" if "c \<noteq> \<infinity>" for c :: ereal using that by (cases "c \<ge> 0") auto
    hence "(\<integral>\<^sup>+\<omega>. e2ennreal (- min 0 (ereal (X n \<omega>))) \<partial>M) = (\<integral>\<^sup>+\<omega>. e2ennreal (max 0 (ereal (X n \<omega>)) - (ereal (X n \<omega>))) \<partial>M)" by simp
    also have "... = (\<integral>\<^sup>+ \<omega>. ennreal (max 0 (X n \<omega>) - (X n \<omega>)) \<partial>M)" using e2ennreal_ereal ereal_max_0 ereal_minus(1) by (intro nn_integral_cong) presburger
    also have "... = (\<integral>\<omega>. max 0 (X n \<omega>) - (X n \<omega>) \<partial>M)" using integrable by (intro nn_integral_eq_integral) auto 
    finally show ?thesis using Bochner_Integration.integral_diff integrable by simp
  qed
  moreover have "liminf (\<lambda>n. ennreal ((\<integral>\<omega>. max 0 (X n \<omega>) \<partial>M) - (\<integral>\<omega>. X n \<omega> \<partial>M))) < \<infinity>"
  proof -
    {
      fix n A
      assume asm: "ennreal ((\<integral>\<omega>. max 0 (X n \<omega>) \<partial>M) - (\<integral>\<omega>. X n \<omega> \<partial>M)) \<in> A"
      have "(\<integral>\<omega>. X 0 \<omega> \<partial>M) \<le> (\<integral>\<omega>. X n \<omega> \<partial>M)" using set_integral_le[OF sets.top order_refl, of n] space_F by (simp add: integrable set_integral_space)
      hence "(\<integral>\<omega>. max 0 (X n \<omega>) \<partial>M) - (\<integral>\<omega>. X n \<omega> \<partial>M) \<le> C - (\<integral>\<omega>. X 0 \<omega> \<partial>M)" using assms(2)[of n] by argo
      hence "ennreal ((\<integral>\<omega>. max 0 (X n \<omega>) \<partial>M) - (\<integral>\<omega>. X n \<omega> \<partial>M)) \<le> ennreal (C - (\<integral>\<omega>. X 0 \<omega> \<partial>M))" using ennreal_leI by blast
      hence "Inf A \<le> ennreal (C - (\<integral>\<omega>. X 0 \<omega> \<partial>M))" by (rule Inf_lower2[OF asm])
    }
    thus ?thesis 
      unfolding liminf_SUP_INF  
      by (intro order.strict_trans1[OF Sup_least, of _ "ennreal (C - (\<integral>\<omega>. X 0 \<omega> \<partial>M))"]) (metis (no_types, lifting)  atLeast_iff imageE image_eqI order.refl order_trans, simp)
  qed
  ultimately have neg_part_finite: "(\<integral>\<^sup>+ \<omega>. e2ennreal (- (min 0 (liminf (\<lambda>n. ereal (X n \<omega>))))) \<partial>M) < \<infinity>" by simp
  
  \<comment> \<open>Putting it all together now to show that the limit is integrable and \<open>< \<infinity>\<close> a.e.\<close>

  have "e2ennreal \<bar>liminf (\<lambda>n. ereal (X n \<omega>))\<bar> = e2ennreal (max 0 (liminf (\<lambda>n. ereal (X n \<omega>)))) + e2ennreal (- (min 0 (liminf (\<lambda>n. ereal (X n \<omega>)))))" for \<omega>
    unfolding ereal_abs_max_min
    by (simp add: eq_onp_same_args max_def plus_ennreal.abs_eq)
  hence "(\<integral>\<^sup>+ \<omega>. e2ennreal \<bar>liminf (\<lambda>n. ereal (X n \<omega>))\<bar> \<partial>M) = (\<integral>\<^sup>+ \<omega>. e2ennreal (max 0 (liminf (\<lambda>n. ereal (X n \<omega>)))) \<partial>M) + (\<integral>\<^sup>+ \<omega>. e2ennreal (- (min 0 (liminf (\<lambda>n. ereal (X n \<omega>))))) \<partial>M)" by (auto intro: nn_integral_add)
  hence nn_integral_finite: "(\<integral>\<^sup>+ \<omega>. e2ennreal \<bar>liminf (\<lambda>n. ereal (X n \<omega>))\<bar> \<partial>M) \<noteq> \<infinity>" using pos_part_finite neg_part_finite by auto
  hence finite_AE: "AE \<omega> in M. e2ennreal \<bar>liminf (\<lambda>n. ereal (X n \<omega>))\<bar> \<noteq> \<infinity>" by (intro nn_integral_noteq_infinite) auto
  moreover
  {
    fix \<omega>
    assume asm: "liminf (\<lambda>n. X n \<omega>) = limsup (\<lambda>n. X n \<omega>)" "\<bar>liminf (\<lambda>n. ereal (X n \<omega>))\<bar> \<noteq> \<infinity>"
    hence "(\<lambda>n. X n \<omega>) \<longlonglongrightarrow> real_of_ereal (liminf (\<lambda>n. X n \<omega>))" using limsup_le_liminf_real ereal_real' by simp
  }
  ultimately have converges: "AE \<omega> in M. (\<lambda>n. X n \<omega>) \<longlonglongrightarrow> real_of_ereal (liminf (\<lambda>n. X n \<omega>))" using liminf_limsup_AE by fastforce

  {
    fix \<omega>
    assume "e2ennreal \<bar>liminf (\<lambda>n. ereal (X n \<omega>))\<bar> \<noteq> \<infinity>"
    hence "\<bar>liminf (\<lambda>n. ereal (X n \<omega>))\<bar> \<noteq> \<infinity>" by force
    hence "e2ennreal \<bar>liminf (\<lambda>n. ereal (X n \<omega>))\<bar> = ennreal (norm (real_of_ereal (liminf (\<lambda>n. ereal (X n \<omega>)))))" by fastforce
  }
  hence "(\<integral>\<^sup>+ \<omega>. e2ennreal \<bar>liminf (\<lambda>n. ereal (X n \<omega>))\<bar> \<partial>M) = (\<integral>\<^sup>+ \<omega>. ennreal (norm (real_of_ereal (liminf (\<lambda>n. ereal (X n \<omega>))))) \<partial>M)" using finite_AE by (fast intro: nn_integral_cong_AE)  
  hence "(\<integral>\<^sup>+ \<omega>. ennreal (norm (real_of_ereal (liminf (\<lambda>n. ereal (X n \<omega>))))) \<partial>M) < \<infinity>" using nn_integral_finite by (simp add: order_less_le)
  hence "integrable M (\<lambda>\<omega>. real_of_ereal (liminf (\<lambda>n. X n \<omega>)))" by (intro integrableI_bounded) auto
  moreover have "(\<lambda>\<omega>. real_of_ereal (liminf (\<lambda>n. X n \<omega>))) \<in> borel_measurable F\<^sub>\<infinity>" using borel_measurable_liminf[OF F_infinity_measurableI] adapted by measurable
  ultimately show ?thesis using that converges by presburger
qed

\<comment> \<open>We state the theorem again for martingales and supermartingales.\<close>

corollary supermartingale_convergence_AE:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes "supermartingale M F 0 X"
      and "\<And>n. (\<integral>\<omega>. max 0 (- X n \<omega>) \<partial>M) \<le> C"
    obtains X\<^sub>l\<^sub>i\<^sub>m where "AE \<omega> in M. (\<lambda>n. X n \<omega>) \<longlonglongrightarrow> X\<^sub>l\<^sub>i\<^sub>m \<omega>" 
                      "integrable M X\<^sub>l\<^sub>i\<^sub>m" 
                      "X\<^sub>l\<^sub>i\<^sub>m \<in> borel_measurable (F\<^sub>\<infinity>)"
proof -
  obtain Y where *: "AE \<omega> in M. (\<lambda>n. - X n \<omega>) \<longlonglongrightarrow> Y \<omega>" "integrable M Y" "Y \<in> borel_measurable (F\<^sub>\<infinity>)"
    using supermartingale.uminus[OF assms(1), THEN submartingale_convergence_AE] assms(2) by auto
  hence "AE \<omega> in M. (\<lambda>n. X n \<omega>) \<longlonglongrightarrow> (- Y) \<omega>" "integrable M (- Y)" "- Y \<in> borel_measurable (F\<^sub>\<infinity>)" 
    using isCont_tendsto_compose[OF isCont_minus, OF continuous_ident] integrable_minus borel_measurable_uminus unfolding fun_Compl_def by fastforce+
  thus ?thesis using that[of "- Y"] by blast
qed

corollary martingale_convergence_AE:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes "martingale M F 0 X"
      and "\<And>n. (\<integral>\<omega>. \<bar>X n \<omega>\<bar> \<partial>M) \<le> C"
  obtains X\<^sub>l\<^sub>i\<^sub>m where "AE \<omega> in M. (\<lambda>n. X n \<omega>) \<longlonglongrightarrow> X\<^sub>l\<^sub>i\<^sub>m \<omega>" 
                    "integrable M X\<^sub>l\<^sub>i\<^sub>m" 
                    "X\<^sub>l\<^sub>i\<^sub>m \<in> borel_measurable (F\<^sub>\<infinity>)"
proof -
  interpret martingale_linorder M F 0 X unfolding martingale_linorder_def by (rule assms)
  have "max 0 (X n \<omega>) \<le> \<bar>X n \<omega>\<bar>" for n \<omega> by linarith
  hence "(\<integral>\<omega>. max 0 (X n \<omega>) \<partial>M) \<le> C" for n using assms(2)[THEN dual_order.trans, OF integral_mono, OF integrable_max] integrable by fast
  thus ?thesis using that submartingale_convergence_AE[OF submartingale_axioms] by blast
qed

corollary martingale_nonneg_convergence_AE:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes "martingale M F 0 X" "\<And>n. AE \<omega> in M. X n \<omega> \<ge> 0"
  obtains X\<^sub>l\<^sub>i\<^sub>m where "AE \<omega> in M. (\<lambda>n. X n \<omega>) \<longlonglongrightarrow> X\<^sub>l\<^sub>i\<^sub>m \<omega>" 
                    "integrable M X\<^sub>l\<^sub>i\<^sub>m" 
                    "X\<^sub>l\<^sub>i\<^sub>m \<in> borel_measurable (F\<^sub>\<infinity>)"
proof -
  interpret martingale_linorder M F 0 X unfolding martingale_linorder_def by (rule assms)
  have "AE \<omega> in M. max 0 (- X n \<omega>) = 0" for n using assms(2)[of n] by force
  hence "(\<integral>\<omega>. max 0 (- X n \<omega>) \<partial>M) \<le> 0" for n by (simp add: integral_eq_zero_AE)
  thus ?thesis using that supermartingale_convergence_AE[OF supermartingale_axioms] by blast
qed

end

end