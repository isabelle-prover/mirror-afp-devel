(*
 Title: Differential_Privacy_Divergence.thy
 Author: Tetsuya Sato
 Author: Yasuhiko Minamide
*)

theory Differential_Privacy_Divergence
  imports "Comparable_Probability_Measures"
begin

section \<open>Divergence for Differential Privacy\<close>

text\<open> First, we introduce the divergence for differential privacy. \<close>

definition DP_divergence :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> ereal " where
  "DP_divergence M N \<epsilon> = Sup {ereal(measure M A - (exp \<epsilon>) * measure N A) | A::'a set. A \<in> (sets M)}"

lemma DP_divergence_SUP:
  shows "DP_divergence M N \<epsilon> = (\<Squnion> (A::'a set) \<in> (sets M). ereal(measure M A - (exp \<epsilon>) * measure N A))"
  by (auto simp: setcompr_eq_image DP_divergence_def)

subsection \<open>Basic Properties\<close>

subsubsection \<open>Non-negativity\<close>

lemma DP_divergence_nonnegativity:
  shows "0 \<le> DP_divergence M N \<epsilon>"
proof(unfold DP_divergence_SUP, rule Sup_upper2[of 0])
  have "{} \<in> sets M" "(\<lambda>A :: 'a set. ereal (measure M A - exp \<epsilon> * measure N A)) {} = 0"
    by auto
  thus "0 \<in> (\<lambda>A. ereal (measure M A - exp \<epsilon> * measure N A)) ` sets M"
    by force
qed(auto)

subsubsection \<open>Graded predicate\<close>

lemma DP_divergence_forall:
  shows "(\<forall> A \<in> (sets M). (measure M A - (exp \<epsilon>) * measure N A \<le> (\<delta> :: real)))
 \<longleftrightarrow> DP_divergence M N \<epsilon> \<le> (\<delta> :: real)"
  unfolding DP_divergence_SUP by (auto simp: SUP_le_iff)

lemma DP_divergence_leE:
  assumes "DP_divergence M N \<epsilon> \<le> (\<delta> :: real)"
  shows "measure M A \<le> (exp \<epsilon>) * measure N A + (\<delta> :: real)"
proof(cases  "A \<in> (sets M)")
  case True
  then show ?thesis using DP_divergence_forall assms(1) by force
next
  case False (* If "A \<in> (sets M)" then "measure M A = 0" *)
  then have "measure M A = 0 " "0 \<le>  measure N A " "0 \<le> (exp \<epsilon>)"
    using measure_notin_sets by auto
  moreover have "0 \<le> ereal \<delta>"
    using assms DP_divergence_nonnegativity[of M N \<epsilon>] dual_order.trans by blast
  ultimately show ?thesis by auto
qed

lemma DP_divergence_leI:
  assumes "\<And> A. A \<in> (sets M) \<Longrightarrow> measure M A \<le> (exp \<epsilon>) * measure N A + (\<delta> :: real)"
  shows "DP_divergence M N \<epsilon> \<le> (\<delta> :: real)"
  using assms unfolding DP_divergence_def by(intro cSup_least, fastforce+)



subsubsection \<open> \<open>(0,0)\<close>-DP means the equality of distributions \<close>

lemma prob_measure_eqI_le:
  assumes M: "M \<in> space (prob_algebra L)"
    and N: "N \<in> space (prob_algebra L)"
    and le:"\<forall> A \<in> sets M. emeasure M A \<le> emeasure N A"
  shows "M = N"
proof(rule measure_eqI)
  interpret pM: prob_space M
    using actual_prob_space M by auto
  interpret pN: prob_space N
    using actual_prob_space N by auto
  show *: "sets M = sets N"
    using M N space_prob_algebra_sets by blast
  show " \<And>A. A \<in> sets M \<Longrightarrow> emeasure M A = emeasure N A"
  proof (rule ccontr)
    fix A assume A: "A \<in> sets M" and neq:"emeasure M A \<noteq> emeasure N A"
    then have A2: "A \<in> sets N" and A3: "A \<in> sets L"
      using M N space_prob_algebra_sets by blast+
    from neq consider
      "emeasure M A < emeasure N A" | "emeasure M A > emeasure N A"
      by fastforce
    then show False
    proof(cases)
      case 1
      have Ms: "emeasure M (space M - A) = emeasure M (space M) - emeasure M A"
        using A sets.sets_into_space by(subst emeasure_Diff,auto)
      have Ns: "emeasure N (space M - A) = emeasure N (space N) - emeasure N A"
        using A2 sets.sets_into_space sets_eq_imp_space_eq[OF *] by(subst emeasure_Diff,auto)
      have "emeasure M (space M - A) > emeasure N (space M - A)"
        unfolding Ms Ns pM.emeasure_space_1 pN.emeasure_space_1
        by (meson "1" ennreal_mono_minus_cancel ennreal_one_less_top leI less_le_not_le pM.measure_le_1 pN.measure_le_1)
      moreover have "emeasure M (space M - A)\<le> emeasure N (space M - A)"
        using le A by auto
      ultimately show ?thesis
        by auto
    next
      case 2
      from le A have "emeasure M A \<le> emeasure N A"
        by auto
      with 2 show ?thesis
        by auto
    qed
  qed
qed

lemma DP_divergence_zero:
  assumes M: "M \<in> space (prob_algebra L)"
    and N: "N \<in> space (prob_algebra L)"
    and DP0:"DP_divergence M N (0::real) \<le> (0::real)"
  shows "M = N"
proof(intro prob_measure_eqI_le[of M L N] M N ballI)
  interpret comparable_probability_measures L M N
    by(unfold_locales,auto simp: M N)
  interpret pM: prob_space M
    by auto
  interpret pN: prob_space N
    by auto
  fix A assume " A \<in> sets M"
  hence "measure M A - measure N A \<le> 0"
    using DP0[simplified zero_ereal_def] unfolding DP_divergence_forall[symmetric] by auto
  hence "measure M A \<le> measure N A"
    by auto
  thus "emeasure M A \<le> emeasure N A"
    by (simp add: pM.emeasure_eq_measure pN.emeasure_eq_measure)
qed

subsubsection \<open>Conversion from pointwise DP \cite{Prasad803anote} \<close>

(* (cf. [Kasiviswanathan and Smith JPC 2014]) to DP *)

lemma DP_divergence_pointwise:
  assumes M: "M \<in> space (prob_algebra L)"
    and N: "N \<in> space (prob_algebra L)"
    and C: "C \<in> sets M"
    and "\<forall>A\<in>sets M. A \<subseteq> C \<longrightarrow> measure M A \<le> exp \<epsilon> * measure N A"
    and "1 - \<delta> \<le> measure M C"
  shows "DP_divergence M N (\<epsilon>::real) \<le> \<delta>"
proof(rule DP_divergence_leI)
  interpret comparable_probability_measures L M N
    by(unfold_locales, auto simp: assms)
  fix A assume A:"A \<in> sets M"
  define A1 and A2 where "A1 = A \<inter> C" and "A2 = A - C"
  hence A1s[measurable]:"A1 \<in> sets M" and A2s[measurable]:"A2 \<in> sets M" and A1C:"A1 \<subseteq> C" and A12: "A1 \<union> A2 = A"
    unfolding A1_def A2_def using C A by auto
  hence "measure M A1 \<le> (exp \<epsilon>) * measure N A1"
    using assms(4) by blast
  also have "... \<le> (exp \<epsilon>) * measure N A"
    using A1s A2s unfolding A12[symmetric]
    by(subst measure_Union[of N A1 A2]) (auto simp add: finite_measure.emeasure_finite A1_def A2_def)
  finally have 1: "measure M A1 \<le> exp \<epsilon> * measure N A".

  have A2Cc:"A2 \<subseteq> space M - C"
    by (metis A A2_def Diff_mono sets.sets_into_space subset_refl)
  have "measure M A2 \<le> measure M (space M - C)"
    by(intro finite_measure.finite_measure_mono A2Cc Sigma_Algebra.sets.compl_sets C,auto)
  also have "... = measure M (space M) - measure M C"
    using assms(3) finM finite_measure.finite_measure_compl by blast
  also have "...\<le> 1 - (1 - \<delta>)"
    using M actual_prob_space prob_space.axioms assms(5) prob_space.prob_space by force
  also have "... = \<delta>"
    by auto
  finally have 2: "measure M A2 \<le> \<delta>".

  have "measure M A = measure M A1 + measure M A2"
    using A1s A2s unfolding A12[symmetric]
    by(subst measure_Union[of M A1 A2]) (auto simp add: finite_measure.emeasure_finite A1_def A2_def)
  also have "... \<le> exp \<epsilon> * measure N A + \<delta>"
    using 1 2 by auto
  finally show "measure M A \<le> exp \<epsilon> * measure N A + \<delta>" .
qed

subsubsection \<open>(Reverse-) Monotonicity for \<open>\<epsilon>\<close> \<close>

lemma DP_divergence_monotonicity:
  assumes "\<epsilon>1 \<le> \<epsilon>2"
  shows "DP_divergence M N \<epsilon>2 \<le> DP_divergence M N \<epsilon>1"
proof(unfold DP_divergence_SUP, rule SUP_mono)
  fix A assume *: "A \<in> sets M"
  have "ereal (measure M A - exp \<epsilon>2 * measure N A) \<le> ereal (measure M A - exp \<epsilon>1 * measure N A)"
    by (auto simp: assms mult_mono')
  with * show "\<exists>m\<in>sets M. ereal (measure M A - exp \<epsilon>2 * measure N A) \<le> ereal (measure M m - exp \<epsilon>1 * measure N m)"
    by blast
qed

corollary DP_divergence_monotonicity':
  assumes M: "M \<in> space (prob_algebra L)"
    and N: "N \<in> space (prob_algebra L)"
    and "\<epsilon>1 \<le> \<epsilon>2" and "\<delta>1 \<le> \<delta>2"
  shows "DP_divergence M N \<epsilon>1 \<le> \<delta>1 \<Longrightarrow> DP_divergence M N \<epsilon>2 \<le> \<delta>2"
  by (meson DP_divergence_monotonicity M N assms gfp.leq_trans)

subsubsection \<open> Reflexivity \<close>

lemma DP_divergence_reflexivity:
  shows "DP_divergence M M 0 = 0"
proof(unfold DP_divergence_SUP)
  have "\<forall> A \<in>sets M. ereal (measure M A - exp 0 * measure M A) = (0 :: ereal)"
    by auto
  thus "(\<Squnion>A \<in>sets M. ereal (measure M A - exp 0 * measure M A)) = (0 :: ereal)"
    by (metis (no_types, lifting) SUP_ereal_eq_0_iff_nonneg empty_iff order_refl sets.top)
qed

corollary DP_divergence_reflexivity':
  assumes "0 \<le> \<epsilon> "
  shows "DP_divergence M M \<epsilon> = 0"
proof-
  have "DP_divergence M M \<epsilon> \<le> DP_divergence M M 0"
    by(rule DP_divergence_monotonicity, auto simp: assms)
  also have "... = 0"
    by(auto simp: DP_divergence_reflexivity)
  finally have 1: "DP_divergence M M \<epsilon> \<le> 0".
  have 2: "0 \<le> DP_divergence M M \<epsilon>"
    by(auto simp: DP_divergence_nonnegativity[of M M \<epsilon>])
  from 1 2 show ?thesis by auto
qed

subsubsection \<open> Transitivity \<close>

lemma DP_divergence_transitivity:
  assumes  DP1: "DP_divergence M1 M2 \<epsilon>1 \<le> 0"
    and DP2: "DP_divergence M2 M3 \<epsilon>2 \<le> 0"
  shows "DP_divergence M1 M3 (\<epsilon>1+\<epsilon>2) \<le> 0"
  unfolding zero_ereal_def
proof(subst DP_divergence_forall[symmetric],intro ballI)
  fix A assume AM1: " A \<in> sets M1"
  have "measure M1 A \<le> exp \<epsilon>1 * measure M2 A"
    using DP_divergence_leE[OF DP1[simplified zero_ereal_def]] by auto
  also have " ... \<le> exp \<epsilon>1 * exp \<epsilon>2 * measure M3 A"
    using DP_divergence_leE[OF DP2[simplified zero_ereal_def]] by auto
  finally have "measure M1 A \<le> exp (\<epsilon>1 + \<epsilon>2) * measure M3 A"
    unfolding exp_add[of \<epsilon>1 \<epsilon>2, symmetric] by auto
  thus "measure M1 A - exp (\<epsilon>1 + \<epsilon>2) * measure M3 A \<le> 0" by auto
qed

subsubsection \<open> Composability \<close>

proposition DP_divergence_composability:
  assumes M: "M \<in> space (prob_algebra L)"
    and N: "N \<in> space (prob_algebra L)"
    and f: "f \<in> L \<rightarrow>\<^sub>M prob_algebra K"
    and g: "g \<in> L \<rightarrow>\<^sub>M prob_algebra K"
    and div1: "DP_divergence M N \<epsilon>1 \<le> (\<delta>1 :: real)"
    and div2: "\<forall>x \<in> (space L). DP_divergence (f x) (g x) \<epsilon>2 \<le> (\<delta>2 :: real)"
    and "0 \<le> \<epsilon>1" and "0 \<le> \<epsilon>2"
  shows "DP_divergence (M \<bind> f) (N \<bind> g) (\<epsilon>1 + \<epsilon>2) \<le> \<delta>1 + \<delta>2"
proof(subst DP_divergence_forall[THEN sym])
  note [measurable] = f g
  interpret comparable_probability_measures L M N
    by(unfold_locales, auto simp: assms)

  show "\<forall>A\<in>sets (M \<bind> f). measure (M \<bind> f) A - exp (\<epsilon>1 + \<epsilon>2) * measure (N \<bind> g) A \<le> \<delta>1 + \<delta>2"
  proof
    fix "A" assume "A \<in> sets (M \<bind> f)"
    hence AinSetsK: "A \<in> sets K"
      using M f sets_bind' by blast

    have f2[measurable]: "f \<in> sum_measure M N \<rightarrow>\<^sub>M prob_algebra K"
      using setMN_L by measurable
    have g2[measurable]: "g \<in> sum_measure M N \<rightarrow>\<^sub>M prob_algebra K"
      using setMN_L by measurable
    have ess_boundedf[simp]: "ess_bounded (sum_measure M N) (\<lambda>x. measure (f x) A)"
      by (intro probability_kernel_evaluation_ess_bounded[where M = K] AinSetsK f2)
    have ess_boundedg[simp]: "ess_bounded (sum_measure M N) (\<lambda>x. measure (g x) A)"
      by (intro probability_kernel_evaluation_ess_bounded[where M = K] AinSetsK g2)
    have integrablef[simp]: "integrable (sum_measure M N) (\<lambda>x. measure (f x) A)"
      by (auto simp:AinSetsK)
    have integrableg[simp]: "integrable (sum_measure M N) (\<lambda>x. measure (g x) A)"
      by (auto simp: AinSetsK)
    have meas1[measurable_cong]: "measurable L (prob_algebra K) = measurable (sum_measure M N) (prob_algebra K)"
      by(rule measurable_cong_sets, simp_all)
    have f2[measurable]: "f \<in> sum_measure M N \<rightarrow>\<^sub>M prob_algebra K"
      by auto
    have g2[measurable]: "g \<in> sum_measure M N \<rightarrow>\<^sub>M prob_algebra K"
      by auto

    have "\<forall>x\<in> space (sum_measure M N). measure (f x) A - (exp \<epsilon>2) * measure (g x) A \<le> \<delta>2"
    proof
      fix x assume A: "x \<in> space (sum_measure M N)"
      hence A2: "A \<in> sets (f x)"
        by (metis AinSetsK f2 measurable_prob_algebraD subprob_measurableD(2))
      from A have xxx: "DP_divergence (f x) (g x) \<epsilon>2 \<le> \<delta>2"
        using div2 spaceMN_L by auto
      show "measure (f x) A - exp \<epsilon>2* measure (g x) A \<le> \<delta>2"
        using xxx[simplified DP_divergence_forall[THEN sym,rule_format]] A2 by blast
    qed
    hence ineq7: "\<forall>x\<in> space (sum_measure M N). measure (f x) A - \<delta>2 \<le> exp \<epsilon>2 * measure (g x) A "
      by auto

    have "\<forall>x\<in> space (sum_measure M N). measure (f x) A- \<delta>2 \<le> min 1 (exp \<epsilon>2 * measure (g x) A) "
    proof
      fix x assume Ass0: "x \<in> space (sum_measure M N)"
      hence "0 \<le> DP_divergence (f x) (g x) \<epsilon>2"
        using DP_divergence_nonnegativity by auto
      also have "DP_divergence (f x) (g x) \<epsilon>2 \<le> \<delta>2"
        using div2 Ass0 spaceMN_L by auto
      finally have posdelta2: "0 \<le> \<delta>2"by auto
      hence minA: "measure (f x) A - \<delta>2 \<le> 1"
        using evaluations_probabilistic_process(3)[OF f AinSetsK] assms Ass0 spaceMN_L by auto
      have minB: "measure (f x) A - \<delta>2 \<le> exp \<epsilon>2 * measure (g x) A"
        using Ass0 ineq7 by auto
      from minA minB show "measure (f x) A - \<delta>2 \<le> min 1 (exp \<epsilon>2 * measure (g x) A)"
        by auto
    qed
    hence inequalityB: "\<forall>x\<in> space (sum_measure M N). max 0 (measure (f x) A - \<delta>2) \<le> min 1 (exp \<epsilon>2 * measure (g x) A)"
      by auto

    have inequalityC: "\<forall>x\<in> space (sum_measure M N). dM x * max 0 (measure (f x) A - \<delta>2) \<le> dM x * min 1 (exp \<epsilon>2 * measure (g x) A)"
    proof
      fix x assume A0: "x\<in> space (sum_measure M N)"
      with inequalityB have P1: "(max 0 (measure (f x) A - \<delta>2)) \<le> min 1 ((exp \<epsilon>2) * measure (g x) A) "
        by auto
      thus "dM x * max 0 (measure (f x) A - \<delta>2) \<le> dM x * min 1 (exp \<epsilon>2 * measure (g x) A)"
        by(intro mult_left_mono, auto)
    qed

    have "(measure (M \<bind> f) A) - exp (\<epsilon>1 + \<epsilon>2) * (measure (N \<bind> g) A) = (\<integral> x. (dM x) * (measure (f x) A) \<partial>(sum_measure M N)) - (exp (\<epsilon>1 + \<epsilon>2)) * (\<integral> x. (dN x) * (measure (g x) A) \<partial>(sum_measure M N))"
      using AinSetsK dM_bind_integral[OF f2] dN_bind_integral[OF g2] by auto
    also have "... = (\<integral> x. (dM x) * (measure (f x) A) \<partial>(sum_measure M N)) - (\<integral> x. (exp (\<epsilon>1 + \<epsilon>2)) * (dN x) * (measure (g x) A) \<partial>(sum_measure M N)) "
      by (metis (mono_tags, lifting) Bochner_Integration.integral_cong integral_mult_right_zero mult.assoc)
    also have "... = (\<integral> x. (dM x) * (measure (f x) A) - (exp (\<epsilon>1 + \<epsilon>2)) * (dN x) * (measure (g x) A) \<partial>(sum_measure M N)) "
      by(rule Bochner_Integration.integral_diff[THEN sym],auto)
    also have "... = (\<integral> x. (dM x) * (measure (f x) A) - (exp \<epsilon>1) * (exp \<epsilon>2) * (dN x) * (measure (g x) A) \<partial>(sum_measure M N)) "
      by (auto simp: exp_add)
    also have "... \<le> (\<integral> x. (dM x) * (max 0 (measure (f x) A - \<delta>2) + \<delta>2) - (exp \<epsilon>1) * (dN x) * min 1 ((exp \<epsilon>2) * (measure (g x) A)) \<partial>(sum_measure M N)) "
    proof(rule integral_mono)
      fix x assume A0: "x \<in> space (sum_measure M N)"
      have "dM x * measure (f x) A - exp \<epsilon>1 * exp \<epsilon>2 * dN x * measure (g x) A = dM x * ((measure (f x) A - \<delta>2) + \<delta>2)- exp \<epsilon>1 * dN x *(exp \<epsilon>2 * measure (g x) A)"
        by auto
      also have "... \<le> dM x * ((max 0 (measure (f x) A - \<delta>2)) + \<delta>2)- exp \<epsilon>1 * dN x *(exp \<epsilon>2 * measure (g x) A)"
        by(auto simp: mult_left_mono)
      also have "... \<le> dM x * ((max 0 (measure (f x) A - \<delta>2)) + \<delta>2)- exp \<epsilon>1 * dN x * (min 1 (exp \<epsilon>2 * measure (g x) A))"
        by(auto simp: mult_left_mono)
      finally show "dM x * measure (f x) A - exp \<epsilon>1 * exp \<epsilon>2 * dN x * measure (g x) A \<le> dM x * (max 0 (measure (f x) A - \<delta>2) + \<delta>2) - exp \<epsilon>1 * dN x * min 1 (exp \<epsilon>2 * measure (g x) A)".
    qed(auto)
    also have "... = (\<integral> x. (dM x) * (max 0 (measure (f x) A - \<delta>2)) - (exp \<epsilon>1) * (dN x) * min 1 ((exp \<epsilon>2)* (measure (g x) A)) + (dM x) *\<delta>2 \<partial>(sum_measure M N)) "
      by (auto simp: diff_add_eq ring_class.ring_distribs(1))
    also have "... \<le> (\<integral> x. (dM x) * (min 1 ((exp \<epsilon>2)* (measure (g x) A))) - (exp \<epsilon>1) * (dN x) * min 1 ((exp \<epsilon>2)* (measure (g x) A)) + dM x *\<delta>2 \<partial>(sum_measure M N)) "
    proof(rule integral_mono)
      show "integrable (sum_measure M N) (\<lambda>x. dM x * (min 1 ((exp \<epsilon>2) * measure (g x) A)) - exp \<epsilon>1 * dN x * min 1 (exp \<epsilon>2 * measure (g x) A) + dM x * \<delta>2)" by auto
      fix x assume "x \<in> space (sum_measure M N)"
      with inequalityC have "dM x * max 0 (measure (f x) A - \<delta>2) \<le> dM x * (min 1 ((exp \<epsilon>2) * measure (g x) A))"
        by blast
      thus "dM x * max 0 (measure (f x) A - \<delta>2) - exp \<epsilon>1 * dN x * min 1 (exp \<epsilon>2 * measure (g x) A) + dM x * \<delta>2 \<le> dM x * min 1 (exp \<epsilon>2 * measure (g x) A) - exp \<epsilon>1 * dN x * min 1 (exp \<epsilon>2 * measure (g x) A) + dM x * \<delta>2"
        by auto
    qed(auto)
    also have "... =(\<integral> x. ((dM x) - (exp \<epsilon>1) * (dN x)) * min 1 ((exp \<epsilon>2) * (measure (g x) A)) + dM x *\<delta>2 \<partial>(sum_measure M N)) "
      by (auto simp: vector_space_over_itself.scale_left_diff_distrib)
    also have "... =(\<integral> x. ((dM x) - (exp \<epsilon>1) * (dN x)) * min 1 ((exp \<epsilon>2) * (measure (g x) A))\<partial>(sum_measure M N)) +(\<integral> x. dM x *\<delta>2 \<partial>(sum_measure M N)) "
      by(rule Bochner_Integration.integral_add,auto)
    finally have *: "(measure (M \<bind> f) A) - exp (\<epsilon>1 + \<epsilon>2) * (measure (N \<bind> g) A)\<le>(\<integral> x. ((dM x) - (exp \<epsilon>1) * (dN x)) * min 1 ((exp \<epsilon>2)* (measure (g x) A))\<partial>(sum_measure M N)) +(\<integral> x. dM x *\<delta>2 \<partial>(sum_measure M N))".

    have "(\<integral> x. dM x *\<delta>2 \<partial>(sum_measure M N))=(\<integral> x. \<delta>2 \<partial>(density (sum_measure M N) dM))"
      by(rule integral_real_density[THEN sym],auto)
    also have "... =(\<integral> x. \<delta>2 \<partial>(density (sum_measure M N)(ennreal o dM)))"
      by (meson comp_def[THEN sym])
    also have "... =(\<integral> x. \<delta>2 \<partial>M)"
      using dM_density by auto
    also have "... = \<delta>2 * measure M (space M)"
      by auto
    also have "... \<le> \<delta>2"
      using prob_space.prob_space prob_spaceM by fastforce
    finally have **: "(\<integral> x. dM x *\<delta>2 \<partial>(sum_measure M N)) \<le> \<delta>2".

    let ?B = "{x\<in> space (sum_measure M N). 0 \<le> ((dM x) - (exp \<epsilon>1) * (dN x))}"
    have mble10: "?B \<in> sets (sum_measure M N)"
      by measurable

    have "(\<integral> x. ((dM x) - (exp \<epsilon>1) * (dN x)) * min 1 ((exp \<epsilon>2)* (measure (g x) A))\<partial>(sum_measure M N)) \<le> (\<integral> x\<in> ?B. (((dM x) - (exp \<epsilon>1) * (dN x)) * min 1 ((exp \<epsilon>2)* (measure (g x) A)))\<partial>(sum_measure M N))"
    proof(rule integral_drop_negative_part2)
      show "(\<lambda>x. (dM x - exp \<epsilon>1 * dN x) * min 1 (exp \<epsilon>2 * measure (g x) A)) \<in> borel_measurable (sum_measure M N)"
        using integrablef integrableg by measurable
      show "integrable (sum_measure M N) (\<lambda>x. (dM x - exp \<epsilon>1 * dN x) * min 1 (exp \<epsilon>2 * measure (g x) A))"
        by auto
      show "{x \<in> space (sum_measure M N). 0 \<le> dM x - exp \<epsilon>1 * dN x} \<in> sets (sum_measure M N)"
        by measurable
      show "{x \<in> space (sum_measure M N). 0 < (dM x - exp \<epsilon>1 * dN x) * min 1 (exp \<epsilon>2 * measure (g x) A)} \<subseteq> {x \<in> space (sum_measure M N). 0 \<le> dM x - exp \<epsilon>1 * dN x}"
      proof(rule subsetI, safe)
        fix x assume "x \<in> space (sum_measure M N)" and "0 < (dM x - exp \<epsilon>1 * dN x) * min 1 (exp \<epsilon>2 * measure (g x) A)"
        hence "0 < (dM x - exp \<epsilon>1 * dN x) \<and> 0 < min 1 (exp \<epsilon>2 * measure (g x) A)"
          by (metis exp_gt_zero lambda_one min.absorb4 min.order_iff mult_pos_pos vector_space_over_itself.scale_zero_right verit_comp_simplify1(3) zero_less_measure_iff zero_less_mult_pos2)
        thus "0 \<le> dM x - exp \<epsilon>1 * dN x"
          by auto
      qed
      show "{x \<in> space (sum_measure M N). 0 \<le> dM x - exp \<epsilon>1 * dN x} \<subseteq> {x \<in> space (sum_measure M N). 0 \<le> (dM x - exp \<epsilon>1 * dN x) * min 1 (exp \<epsilon>2 * measure (g x) A)}"
        by auto
    qed
    also have "... \<le> (\<integral> x\<in> ?B. ((dM x) - (exp \<epsilon>1) * (dN x)) \<partial>(sum_measure M N))"
      using mble10 by(intro set_integral_mono,unfold set_integrable_def,auto simp: mult_left_le)
    also have "... = (\<integral> x\<in> ?B. (dM x) \<partial>(sum_measure M N)) - (\<integral> x\<in> ?B. ((exp \<epsilon>1) * (dN x)) \<partial>(sum_measure M N))"
      using mble10 by(intro set_integral_diff, auto simp:set_integrable_def)
    also have "... = (\<integral> x\<in> ?B. (dM x) \<partial>(sum_measure M N)) - (exp \<epsilon>1) * (\<integral> x\<in> ?B. (dN x) \<partial>(sum_measure M N))"
      by auto
    also have "... = measure M ?B - (exp \<epsilon>1) * (measure N ?B)"
    proof-
      have "(\<integral> x\<in> ?B. dM x \<partial>(sum_measure M N)) = (\<integral> x. (dM x * indicator ?B x) \<partial> (sum_measure M N))"
        by (auto simp: mult.commute set_lebesgue_integral_def)
      also have "... = (\<integral> x. indicator ?B x \<partial>(density (sum_measure M N) dM))"
        by(rule integral_real_density[THEN sym],measurable)
      also have "... = (\<integral> x. indicator ?B x \<partial>(density (sum_measure M N) (ennreal o dM)))"
        by (metis comp_apply)
      also have "... = (\<integral> x. indicator ?B x *\<^sub>R 1 \<partial>(density (sum_measure M N) (ennreal o dM)))"
        by auto
      also have "... = (\<integral> x\<in> ?B. 1 \<partial>(density (sum_measure M N) (ennreal o dM)))"
        by(auto simp:set_lebesgue_integral_def)
      also have "... = 1 * measure (density (sum_measure M N) (ennreal o dM)) ?B"
			proof(rule set_integral_indicator)
			  show "emeasure (density (sum_measure M N) (ennreal \<circ> dM)) ?B < \<top>"
			    using finite_measure.emeasure_finite[of M ?B,OF finM] diff_gt_0_iff_gt_ennreal by force
			qed(measurable)
			also have "... = 1 * measure M ?B"
			  using dM_density by auto
			finally have eq11: "(\<integral> x\<in> ?B. dM x \<partial>(sum_measure M N)) = measure M ?B"
			  by auto

			have "(\<integral> x\<in> ?B. dN x \<partial>(sum_measure M N)) = (\<integral> x. (dN x * indicator ?B x) \<partial> (sum_measure M N))"
			  by (auto simp: mult.commute set_lebesgue_integral_def)
			also have "... = (\<integral> x. indicator ?B x \<partial>(density (sum_measure M N) dN))"
			  by(rule integral_real_density[THEN sym],measurable)
			also have "... = (\<integral> x. indicator ?B x \<partial>(density (sum_measure M N) (ennreal o dN)))"
			  by (metis comp_apply)
			also have "... = (\<integral> x\<in> ?B. 1 \<partial>(density (sum_measure M N) (ennreal o dN)))"
			  by(auto simp:set_lebesgue_integral_def)
			also have "... = 1 * measure (density (sum_measure M N) (ennreal o dN)) ?B"
			proof(rule set_integral_indicator,measurable)
			  show "emeasure (density (sum_measure M N) (ennreal \<circ> dN)) ?B < \<top>"
			    using finite_measure.emeasure_finite[of N ?B,OF finN] diff_gt_0_iff_gt_ennreal by force
			qed
			also have "... = 1 * measure N ?B"
			  using dN_density by auto
			finally have eq21: "(\<integral> x\<in> ?B. dN x \<partial>(sum_measure M N)) = measure N ?B"
			  by auto

			show ?thesis
			  using eq11 eq21 by auto
		qed
		also have "... \<le> \<delta>1"
		  using div1 DP_divergence_forall mble10 setMN_M by blast
		finally have ***: "(\<integral> x. ((dM x) - (exp \<epsilon>1) * (dN x)) * min 1 ((exp \<epsilon>2)* (measure (g x) A))\<partial>(sum_measure M N)) \<le> \<delta>1".

		show "measure (M \<bind> f) A - exp (\<epsilon>1 + \<epsilon>2) * measure (N \<bind> g) A \<le> \<delta>1 + \<delta>2"
		  using * ** *** by auto
	qed
qed

subsubsection \<open> Post-processing inequality  \<close>

corollary DP_divergence_postprocessing:
  assumes M: "M \<in> space (prob_algebra L)"
    and N: "N \<in> space (prob_algebra L)"
    and f: "f \<in> L \<rightarrow>\<^sub>M (prob_algebra K)"
    and div1: "DP_divergence M N \<epsilon>1 \<le> (\<delta>1 :: real)"
    and "0\<le> \<epsilon>1"
  shows "DP_divergence (bind M f) (bind N f) \<epsilon>1 \<le> \<delta>1"
proof-
  have div2: "\<forall>x \<in> (space L). DP_divergence (f x) (f x) 0 \<le> ereal 0"
  proof
    fix x assume A0: "x \<in> space L"
    have "DP_divergence (f x) (f x) 0 = 0"
      by(rule DP_divergence_reflexivity)
    thus "DP_divergence (f x) (f x) 0 \<le> ereal 0"
      by auto
  qed
  have "DP_divergence (M \<bind> f) (N \<bind> f) (\<epsilon>1 + 0) \<le> ereal (\<delta>1 + 0) "
    by(rule DP_divergence_composability[of M L N f K f \<epsilon>1 \<delta>1 0 0], auto simp: assms div2)
  thus "DP_divergence (M \<bind> f) (N \<bind> f) \<epsilon>1 \<le> ereal \<delta>1"by auto
qed

subsubsection \<open> Law for the strength of the Giry monad \<close>

lemma DP_divergence_strength:
  assumes "M \<in> space (prob_algebra L)"
    and "N \<in> space (prob_algebra L)"
    and "DP_divergence M N \<epsilon>1 \<le> (\<delta>1 :: real)"
    and "0\<le> \<epsilon>1"
    and x:"x \<in> space K"
  shows "DP_divergence ((return K x) \<Otimes>\<^sub>M M) ((return K x) \<Otimes>\<^sub>M N) \<epsilon>1 \<le> \<delta>1"
proof-
  interpret comparable_probability_measures L M N
    by(unfold_locales, auto simp: assms)
  define f where "f = (\<lambda> y. (return (K \<Otimes>\<^sub>M L) (x, y)))"
  have f: "f \<in> L \<rightarrow>\<^sub>M (prob_algebra (K \<Otimes>\<^sub>M L))"
    using assms f_def by force
  have 1:"DP_divergence (bind M f) (bind N f) \<epsilon>1 \<le> \<delta>1"
    using DP_divergence_postprocessing assms f by blast
  moreover have 2:"(return K x) \<Otimes>\<^sub>M M = (M \<bind> f)" 
    by(subst Giry_strength_bind_return[OF M x])(metis f_def return_cong sets_pair_measure_cong sets_return spaceM)
  moreover have 3:"(return K x) \<Otimes>\<^sub>M N = (N \<bind> f) "
    by(subst Giry_strength_bind_return[OF N x])(metis f_def return_cong sets_pair_measure_cong sets_return spaceN)
  ultimately show "DP_divergence ((return K x) \<Otimes>\<^sub>M M) ((return K x) \<Otimes>\<^sub>M N) \<epsilon>1 \<le> \<delta>1"
    by auto
qed

subsubsection \<open> Additivity: law for the double-strength of the Giry monad\<close>

lemma DP_divergence_additivity:
  assumes M: "M \<in> space (prob_algebra L)"
    and N: "N \<in> space (prob_algebra L)"
    and M2: "M2 \<in> space (prob_algebra K)"
    and N2: "N2 \<in> space (prob_algebra K)"
    and div1: "DP_divergence M N \<epsilon>1 \<le> (\<delta>1 :: real)"
    and div2': "DP_divergence M2 N2 \<epsilon>2 \<le> (\<delta>2 :: real)"
    and "0 \<le> \<epsilon>1" and "0 \<le> \<epsilon>2"
  shows "DP_divergence (M \<Otimes>\<^sub>M M2) (N \<Otimes>\<^sub>M N2) (\<epsilon>1 + \<epsilon>2) \<le> \<delta>1 + \<delta>2"
proof-
  interpret comparable_probability_measures L M N
    by(unfold_locales, auto simp: assms)
  interpret c2: comparable_probability_measures K M2 N2
    by(unfold_locales, auto simp: assms)
  have 1: "M \<Otimes>\<^sub>M M2 = M \<bind> (\<lambda>x. M2 \<bind> (\<lambda>y. return (L \<Otimes>\<^sub>M K) (x, y)))"
    by(subst return_cong[of "M \<Otimes>\<^sub>M M2",symmetric])(auto simp: pair_prob_space_def pair_sigma_finite_def assms finite_measure_def prob_space_imp_sigma_finite sets_pair_measure intro!: pair_prob_space.pair_measure_eq_bind )
  have 2: "N \<Otimes>\<^sub>M N2 = N \<bind> (\<lambda>x. N2 \<bind> (\<lambda>y. return (L \<Otimes>\<^sub>M K) (x, y)))"
    by(subst return_cong[of "N \<Otimes>\<^sub>M N2",symmetric])(auto simp: pair_prob_space_def pair_sigma_finite_def assms finite_measure_def prob_space_imp_sigma_finite sets_pair_measure intro!: pair_prob_space.pair_measure_eq_bind )
  have " DP_divergence (M \<Otimes>\<^sub>M M2) (N \<Otimes>\<^sub>M N2) (\<epsilon>1 + \<epsilon>2) = DP_divergence (M \<bind> (\<lambda>x. M2 \<bind> (\<lambda>y. return (L \<Otimes>\<^sub>M K) (x, y)))) (N \<bind> (\<lambda>x. N2 \<bind> (\<lambda>y. return (L \<Otimes>\<^sub>M K) (x, y)))) (\<epsilon>1 + \<epsilon>2)"
    using 1 2 by auto
  also have "... \<le> \<delta>1 + \<delta>2"
  proof(rule DP_divergence_composability[where L = L and K = " (L \<Otimes>\<^sub>M K)"])
    show "(\<lambda>x. M2 \<bind> (\<lambda>y. return (L \<Otimes>\<^sub>M K) (x, y))) \<in> L \<rightarrow>\<^sub>M prob_algebra (L \<Otimes>\<^sub>M K)"
      and "(\<lambda>x. N2 \<bind> (\<lambda>y. return (L \<Otimes>\<^sub>M K) (x, y))) \<in> L \<rightarrow>\<^sub>M prob_algebra (L \<Otimes>\<^sub>M K)"
      by(rule measurable_bind_prob_space2[where N = K],auto simp: assms)+
  qed(auto intro!: DP_divergence_postprocessing[where K = "L \<Otimes>\<^sub>M K"] assms measurable_bind_prob_space2[where N = K])
  finally show ?thesis.
qed

subsection \<open>Hypotehsis testing interpretation\<close>

subsubsection \<open>Privacy region\<close>

definition DP_region_one_side :: "real \<Rightarrow> real \<Rightarrow> (real \<times> real) set" where
  "DP_region_one_side \<epsilon> \<delta> = {(x::real,y::real). (x - exp(\<epsilon>) * y \<le> \<delta>) \<and> 0 \<le> x \<and> x \<le> 1 \<and> 0\<le> y \<and> y \<le> 1} "

lemma DP_divergence_region:
  assumes M: "M \<in> space (prob_algebra L)"
    and N: "N \<in> space (prob_algebra L)"
  shows "(\<forall> A \<in> (sets M). ((measure M A, measure N A) \<in> DP_region_one_side \<epsilon> \<delta>)) \<longleftrightarrow> DP_divergence M N \<epsilon> \<le> (\<delta> :: real)"
proof-
  interpret comparable_probability_measures L M N
    by(unfold_locales,auto simp: assms)
  show ?thesis 
    by(subst DP_divergence_forall[symmetric],unfold  DP_region_one_side_def,auto intro!: prob_space.prob_le_1)
qed

subsubsection \<open>2-generatedness of @{term DP_divergence} \cite{DBLP:journals/corr/abs-1905-09982} \<close>

lemma DP_divergence_2_generated_deterministic:
  assumes M: "M \<in> space (prob_algebra L)"
    and N: "N \<in> space (prob_algebra L)"
    and "0 \<le> \<epsilon>"
  shows "DP_divergence M N \<epsilon> = (\<Squnion> f \<in> L \<rightarrow>\<^sub>M (count_space (UNIV :: bool set)). DP_divergence (distr M (count_space UNIV) f) (distr N (count_space UNIV) f) \<epsilon>)"
proof-
  interpret comparable_probability_measures L M N
    by(unfold_locales,auto simp: assms)
  show ?thesis
  proof(intro SUP_eqI[THEN sym])
    fix f :: "_\<Rightarrow>bool" assume A0: "Measurable.pred L f"
    hence eq1: "distr M (count_space UNIV) f = M \<bind> return (count_space UNIV) \<circ> f"
      by (metis bind_return_distr measurable_cong_sets prob_space.not_empty prob_spaceM spaceM)
    have eq2: "distr N (count_space UNIV) f = N \<bind> return (count_space UNIV) \<circ> f"
      by (metis A0 bind_return_distr measurable_cong_sets prob_space.not_empty prob_spaceN spaceN)
    have "DP_divergence (distr M (count_space UNIV) f) (distr N (count_space UNIV) f) \<epsilon> = DP_divergence (M \<bind> return (count_space UNIV) \<circ> f) (N \<bind> return (count_space UNIV) \<circ> f) \<epsilon>"
      using eq1 eq2 by auto
    also have "... \<le> DP_divergence M N \<epsilon>"
      by(rule ereal_le_real,auto intro!: DP_divergence_postprocessing measurable_comp[where N = "count_space UNIV"] A0 assms measurable_return_prob_space)
    finally show "DP_divergence (distr M (count_space UNIV) f) (distr N (count_space UNIV) f) \<epsilon> \<le> DP_divergence M N \<epsilon>".
  next
    fix y :: ereal assume A0: "(\<And>f. Measurable.pred L f \<Longrightarrow> DP_divergence (distr M (count_space UNIV) f) (distr N (count_space UNIV) f) \<epsilon> \<le> y)"
    show "DP_divergence M N \<epsilon> \<le> y"
      unfolding DP_divergence_def
    proof(subst Sup_le_iff,safe)
      fix i assume A1: "i \<in> sets M"
      hence [measurable]: "Measurable.pred L (\<lambda> x.(x \<in> i))"
        by auto
      have [simp]:"(\<lambda>x. x \<in> i) -` {True} = i"
        by auto
      from A1 A0 have "DP_divergence (distr M (count_space UNIV) (\<lambda> x.(x \<in> i))) (distr N (count_space UNIV) (\<lambda> x.(x \<in> i))) \<epsilon> \<le> y"
        by auto
      hence ineq1: "measure (distr M (count_space UNIV) (\<lambda> x.(x \<in> i))) {True} - exp \<epsilon> * measure (distr N (count_space UNIV) (\<lambda> x.(x \<in> i))) {True} \<le> y"
        using DP_divergence_def[of "(distr M (count_space UNIV) (\<lambda> x.(x \<in> i)))" "(distr N (count_space UNIV) (\<lambda> x.(x \<in> i)))"\<epsilon> ] by (auto simp: Sup_le_iff)
      have eq1: "measure (distr M (count_space UNIV) (\<lambda> x.(x \<in> i))) {True} = measure M i "
        using measure_distr[of "(\<lambda> x.(x \<in> i))"M "(count_space UNIV)" "{True}"] spaceM(1) A1 by auto
      have eq2: "measure (distr N (count_space UNIV) (\<lambda> x.(x \<in> i))) {True} = measure N i "
        using measure_distr[of "(\<lambda> x.(x \<in> i))"N "(count_space UNIV)" "{True}"] spaceN(1) A1 by auto
      from ineq1 show "ereal (measure M i - exp \<epsilon> * measure N i) \<le> y"
        unfolding eq1 eq2 by auto
    qed
  qed
qed

lemma DP_divergence_2_generated:
  assumes M: "M \<in> space (prob_algebra L)"
    and N: "N \<in> space (prob_algebra L)"
  assumes "0 \<le> \<epsilon>"
  shows "DP_divergence M N \<epsilon> = (\<Squnion> f \<in> L \<rightarrow>\<^sub>M (prob_algebra (count_space (UNIV :: bool set))). DP_divergence (M \<bind> f) (N \<bind> f) \<epsilon>)"
proof-
  interpret comparable_probability_measures L M N
    by(unfold_locales,auto simp: assms)
  show ?thesis
  proof(subst DP_divergence_2_generated_deterministic[OF assms],intro order_antisym)
    show "(\<Squnion>f\<in>L \<rightarrow>\<^sub>M prob_algebra (count_space (UNIV :: bool set)). DP_divergence (M \<bind> f) (N \<bind> f) \<epsilon>) \<le> (\<Squnion>f\<in>L \<rightarrow>\<^sub>M count_space (UNIV :: bool set). DP_divergence (distr M (count_space UNIV) f) (distr N (count_space UNIV) f) \<epsilon>)"
    proof(subst SUP_le_iff)
      show "\<forall>i\<in>L \<rightarrow>\<^sub>M prob_algebra (count_space (UNIV :: bool set)). DP_divergence (M \<bind> i) (N \<bind> i) \<epsilon> \<le> (\<Squnion>f\<in>L \<rightarrow>\<^sub>M count_space (UNIV :: bool set). DP_divergence (distr M (count_space UNIV) f) (distr N (count_space UNIV) f) \<epsilon>)"
      proof
        fix i :: "_ \<Rightarrow> bool measure" assume A0: "i \<in> L \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"
        have "DP_divergence (M \<bind> i) (N \<bind> i) \<epsilon> \<le> DP_divergence M N \<epsilon>"
          using DP_divergence_postprocessing A0 assms ereal_le_real by blast
        also have "... = (\<Squnion>f :: 'a \<Rightarrow> bool\<in>L \<rightarrow>\<^sub>M count_space UNIV. DP_divergence (distr M (count_space UNIV) f) (distr N (count_space UNIV) f) \<epsilon>)"
          using DP_divergence_2_generated_deterministic assms by blast
        finally show "DP_divergence (M \<bind> i) (N \<bind> i) \<epsilon> \<le> (\<Squnion>f :: 'a \<Rightarrow> bool\<in>L \<rightarrow>\<^sub>M count_space UNIV. DP_divergence (distr M (count_space UNIV) f) (distr N (count_space UNIV) f) \<epsilon>)".
      qed
    qed
    show "(\<Squnion>f :: 'a \<Rightarrow> bool\<in>L \<rightarrow>\<^sub>M count_space UNIV. DP_divergence (distr M (count_space UNIV) f) (distr N (count_space UNIV) f) \<epsilon>) \<le> (\<Squnion>f :: 'a \<Rightarrow> bool measure\<in>L \<rightarrow>\<^sub>M prob_algebra (count_space UNIV). DP_divergence (M \<bind> f) (N \<bind> f) \<epsilon>)"
    proof(rule SUP_mono)
      fix f :: "_\<Rightarrow>bool" assume A0: "f \<in> L \<rightarrow>\<^sub>M count_space UNIV"
      show "\<exists>m :: 'a \<Rightarrow> bool measure\<in>L \<rightarrow>\<^sub>M prob_algebra (count_space UNIV). DP_divergence (distr M (count_space UNIV) f) (distr N (count_space UNIV) f) \<epsilon> \<le> DP_divergence (M \<bind> m) (N \<bind> m) \<epsilon>"
      proof(unfold Bex_def)
        have "(((return (count_space UNIV)) o f) \<in> L \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)) \<and> (DP_divergence (distr M (count_space UNIV) f) (distr N (count_space UNIV) f) \<epsilon> = DP_divergence (M \<bind>((return (count_space (UNIV :: bool set))) o f)) (N \<bind>((return (count_space (UNIV :: bool set))) o f)) \<epsilon>)"
        proof(safe)
          show "return (count_space UNIV) \<circ> f \<in> L \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"using A0 by auto
          from A0 have eq1: "(distr M (count_space UNIV) f) = M \<bind>((return (count_space (UNIV :: bool set))) o f)"
            by (metis bind_return_distr measurable_return1 prob_space.not_empty return_sets_cong spaceM prob_spaceM)
          from A0 have eq2: "(distr N (count_space UNIV) f) = N \<bind>((return (count_space (UNIV :: bool set))) o f)"
            by (metis bind_return_distr measurable_cong_sets prob_space.not_empty spaceMN_M spaceMN_N spaceN prob_spaceN )
          from eq1 eq2 show "DP_divergence (distr M (count_space UNIV) f) (distr N (count_space UNIV) f) \<epsilon> = DP_divergence (M \<bind> return (count_space UNIV) \<circ> f) (N \<bind> return (count_space UNIV) \<circ> f) \<epsilon>"
            by auto
        qed
        thus "\<exists>x :: 'a \<Rightarrow> bool measure. x \<in> L \<rightarrow>\<^sub>M prob_algebra (count_space UNIV) \<and> DP_divergence (distr M (count_space UNIV) f) (distr N (count_space UNIV) f) \<epsilon> \<le> DP_divergence (M \<bind> x) (N \<bind> x) \<epsilon>"
          by auto
      qed
    qed
  qed
qed

subsection \<open>real version of @{term DP_divergence}\<close>

subsubsection \<open>finiteness\<close>

definition DP_divergence_real :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real " where
  "DP_divergence_real M N \<epsilon> = Sup {(measure M A - (exp \<epsilon>) * measure N A) | A::'a set. A \<in> (sets M)}"

lemma DP_divergence_real_SUP:
  shows "DP_divergence_real M N \<epsilon> = (\<Squnion> (A::'a set) \<in> (sets M). (measure M A - (exp \<epsilon>) * measure N A))"
  by (auto simp: setcompr_eq_image DP_divergence_real_def)

lemma DP_divergence_real_leI:
  assumes "\<And> A. A \<in> (sets M) \<Longrightarrow> measure M A \<le> (exp \<epsilon>) * measure N A + (\<delta> :: real)"
  shows "DP_divergence_real M N \<epsilon> \<le> (\<delta> :: real)"
  using assms unfolding DP_divergence_real_def by(intro cSup_least, fastforce+)

subsubsection \<open>real version of @{term DP_divergence}\<close>

text \<open> If @{term M} and  @{term N} are finite then @{term DP_divergence} and the following version @{term DP_divergence_real} are the same.
 However, if  @{term M} and @{term N} are not finite, @{term "DP_divergence_real M N \<epsilon>"} is not well defined.
 Hence, the latter needs extra assumptions for the finiteness of measures @{term M} and @{term N}.
 For example the following lemmas need a kind of finiteness of@{term M} and @{term N}.\<close>

lemma DP_divergence_is_real:
  assumes M: "M \<in> space (prob_algebra L)"
    and N: "N \<in> space (prob_algebra L)" (*we need them*)
  shows "DP_divergence M N \<epsilon> = DP_divergence_real M N \<epsilon>"
  unfolding DP_divergence_def DP_divergence_real_def
proof(subst ereal_Sup)
  interpret pM: prob_space M
    using M actual_prob_space by auto
  interpret pN: prob_space N
    using N actual_prob_space by auto
  {
    fix A assume "A \<in> (sets M)"
    have "pM.prob A - exp \<epsilon> * pN.prob A \<le> pM.prob A"
      by auto
    also have "... \<le> 1"
      by auto
    finally have 1: "pM.prob A - exp \<epsilon> * pN.prob A \<le> 1".

    have " - exp \<epsilon> \<le> - exp \<epsilon> * pN.prob A"
      by auto
    also have "... \<le> pM.prob A - exp \<epsilon> * pN.prob A"
      by auto
    finally have 2: "- exp \<epsilon> \<le> pM.prob A - exp \<epsilon> * pN.prob A".
    note 1 2
  }note * = this

  hence "\<Squnion> (ereal ` {pM.prob A - exp \<epsilon> * pN.prob A |A. A \<in> pM.events}) \<le> ereal 1"
    unfolding SUP_le_iff by auto
  moreover from * have "ereal (- exp \<epsilon>) \<le> \<Squnion> (ereal ` {pM.prob A - exp \<epsilon> * pN.prob A |A. A \<in> pM.events})"
    by(intro SUP_upper2, auto)
  ultimately show " \<bar>\<Squnion> (ereal ` {pM.prob A - exp \<epsilon> * pN.prob A |A. A \<in> pM.events})\<bar> \<noteq> \<infinity>"
    by auto
  have " {ereal (pM.prob A - exp \<epsilon> * pN.prob A) |A. A \<in> pM.events} = ereal ` {pM.prob A - exp \<epsilon> * pN.prob A |A. A \<in> pM.events}"
    by blast
  thus " \<Squnion> {ereal (pM.prob A - exp \<epsilon> * pN.prob A) |A. A \<in> pM.events} = \<Squnion> (ereal ` {pM.prob A - exp \<epsilon> * pN.prob A |A. A \<in> pM.events})"
    by auto
qed

corollary DP_divergence_real_forall:
  assumes M: "M \<in> space (prob_algebra L)"
    and N: "N \<in> space (prob_algebra L)" (*we need them*)
  shows "(\<forall> A \<in> (sets M). (measure M A - (exp \<epsilon>) * measure N A \<le> (\<delta> :: real))) \<longleftrightarrow> DP_divergence_real M N \<epsilon> \<le> (\<delta> :: real)"
  unfolding DP_divergence_forall DP_divergence_is_real[OF M N] by auto

corollary DP_divergence_real_inequality1:
  assumes M: "M \<in> space (prob_algebra L)"
    and N: "N \<in> space (prob_algebra L)" (*we need them*)
    and "A \<in> (sets M)" and "DP_divergence_real M N \<epsilon> \<le> (\<delta> :: real)"
  shows "measure M A \<le> (exp \<epsilon>) * measure N A + (\<delta> :: real)"
  using DP_divergence_real_forall[OF M N] assms(3) assms(4) by force

end
