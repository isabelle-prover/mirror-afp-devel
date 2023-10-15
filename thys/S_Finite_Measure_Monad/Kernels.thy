(*  Title:   Kernels.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

section \<open> Kernels \<close>
theory Kernels
  imports Lemmas_S_Finite_Measure_Monad
begin

subsection \<open>S-Finite Measures\<close>
locale s_finite_measure =
  fixes M :: "'a measure"
  assumes s_finite_sum: "\<exists>Mi :: nat \<Rightarrow> 'a measure. (\<forall>i. sets (Mi i) = sets M) \<and> (\<forall>i. finite_measure (Mi i)) \<and> (\<forall>A\<in>sets M. M A = (\<Sum>i. Mi i A))"

lemma(in sigma_finite_measure) s_finite_measure: "s_finite_measure M"
proof
  obtain A :: "nat \<Rightarrow> _" where A: "range A \<subseteq> sets M" "\<Union> (range A) = space M" "\<And>i. emeasure M (A i) \<noteq> \<infinity>" "disjoint_family A"
    by(metis sigma_finite_disjoint)
  define Mi where "Mi \<equiv> (\<lambda>i. measure_of (space M) (sets M) (\<lambda>a. M (a \<inter> A i)))"
  have emeasure_Mi:"Mi i a = M (a \<inter> A i)" if "a \<in> sets M" for i a
  proof -
    have "positive (sets (Mi i)) (\<lambda>a. M (a \<inter> A i))" "countably_additive (sets (Mi i)) (\<lambda>a. M (a \<inter> A i))"
      unfolding positive_def countably_additive_def
    proof safe
      fix B :: "nat \<Rightarrow> _"
      assume "range B \<subseteq> sets (Mi i)" "disjoint_family B"
      with A(1) have "range (\<lambda>j. B j \<inter> A i) \<subseteq> sets M" "disjoint_family (\<lambda>j. B j \<inter> A i)"
        by(fastforce simp: Mi_def disjoint_family_on_def)+
      thus "(\<Sum>j. M (B j \<inter> A i)) = M (\<Union> (range B) \<inter> A i)"
        by (metis UN_extend_simps(4) suminf_emeasure)
    qed simp
    from emeasure_measure_of[OF _ _ this] that show ?thesis
      by(auto simp add: Mi_def sets.space_closed)
  qed
  have sets_Mi:"sets (Mi i) = sets M" for i by(simp add: Mi_def)
  show "\<exists>Mi. (\<forall>i. sets (Mi i) = sets M) \<and> (\<forall>i. finite_measure (Mi i)) \<and> (\<forall>A\<in>sets M. emeasure M A = (\<Sum>i. emeasure (Mi i) A))"
  proof(safe intro!: exI[where x=Mi])
    fix i
    show "finite_measure (Mi i)"
      using A by(auto intro!: finite_measureI simp: sets_eq_imp_space_eq[OF sets_Mi] emeasure_Mi)
  next
    fix B
    assume B:"B \<in> sets M"
    with A(1,4) have "range (\<lambda>i. B \<inter> A i) \<subseteq> sets M" "disjoint_family (\<lambda>i. B \<inter> A i)"
      by(auto simp: disjoint_family_on_def)
    then show "M B = (\<Sum>i. (Mi i) B)"
      by(simp add: emeasure_Mi[OF B] suminf_emeasure A(2) B)
  qed(simp_all add: sets_Mi)
qed

lemmas(in finite_measure) s_finite_measure_finite_measure = s_finite_measure

lemmas(in subprob_space) s_finite_measure_subprob = s_finite_measure

lemmas(in prob_space) s_finite_measure_prob = s_finite_measure

sublocale sigma_finite_measure \<subseteq> s_finite_measure
  by(rule s_finite_measure)

lemma s_finite_measureI:
  assumes "\<And>i. sets (Mi i) = sets M" "\<And>i. finite_measure (Mi i)" "\<And>A. A\<in>sets M \<Longrightarrow> M A = (\<Sum>i. Mi i A)"
  shows "s_finite_measure M"
  by standard (use assms in blast)

lemma s_finite_measure_prodI:
  assumes "\<And>i j. sets (Mij i j) = sets M" "\<And>i j. Mij i j (space M) < \<infinity>" "\<And>A. A \<in> sets M \<Longrightarrow> M A = (\<Sum>i. (\<Sum>j. Mij i j A))"
  shows "s_finite_measure M"
proof -
  define Mi' where "Mi' \<equiv> (\<lambda>n. case_prod Mij (prod_decode n))"
  have sets_Mi'[measurable_cong]:"\<And>i. sets (Mi' i) = sets M"
    using assms(1) by(simp add: Mi'_def split_beta')
  have Mi'_finite:"\<And>i. finite_measure (Mi' i)"
    using assms(2) sets_eq_imp_space_eq[OF sets_Mi'[symmetric]] top.not_eq_extremum
    by(fastforce intro!: finite_measureI simp: Mi'_def split_beta')
  show ?thesis
  proof(safe intro!: s_finite_measureI[where Mi=Mi'] sets_Mi' Mi'_finite)
    fix A
    show "A \<in> sets M \<Longrightarrow> M A = (\<Sum>i. Mi' i A)"
      by(simp add: assms(3) suminf_ennreal_2dimen[where f="\<lambda>(x,y). Mij x y A", simplified,OF refl,symmetric] Mi'_def split_beta')
  qed
qed

corollary s_finite_measure_s_finite_sumI:
  assumes "\<And>i. sets (Mi i) = sets M" "\<And>i. s_finite_measure (Mi i)" "\<And>A. A \<in> sets M \<Longrightarrow> M A = (\<Sum>i. Mi i A)"
  shows "s_finite_measure M"
proof -
  from s_finite_measure.s_finite_sum[OF assms(2)]
  obtain Mij where Mij[measurable]: "\<And>i j. sets (Mij i j) = sets M" "\<And>i j. finite_measure (Mij i j)" "\<And>i j A. A \<in> sets M \<Longrightarrow> Mi i A = (\<Sum>j. Mij i j A)"
    by (metis assms(1))
  show ?thesis
    using finite_measure.emeasure_finite[OF Mij(2)]
    by(auto intro!: s_finite_measure_prodI[where Mij = Mij] simp: assms(3) Mij top.not_eq_extremum)
qed

lemma countable_space_s_finite_measure:
  assumes "countable (space M)" "sets M = Pow (space M)"
  shows "s_finite_measure M"
proof -
  define Mi where "Mi \<equiv> (\<lambda>i. measure_of (space M) (sets M) (\<lambda>A. emeasure M (A \<inter> {from_nat_into (space M) i})))"
  have sets_Mi[measurable_cong,simp]: "sets (Mi i) = sets M" for i
    by(auto simp: Mi_def)
  have emeasure_Mi: "emeasure (Mi i) A = emeasure M (A \<inter> {from_nat_into (space M) i})" if [measurable]: "A \<in> sets M" and i:"i \<in> to_nat_on (space M) ` (space M)" for i A
  proof -
    have "from_nat_into (space M) i \<in> space M"
      by (simp add: from_nat_into_def i inv_into_into)
    hence [measurable]: "{from_nat_into (space M) i} \<in> sets M"
      using assms(2) by auto
    have 1:"countably_additive (sets M) (\<lambda>A. emeasure M (A \<inter> {from_nat_into (space M) i}))"
      unfolding countably_additive_def
    proof safe
      fix B :: "nat \<Rightarrow> _"
      assume "range B \<subseteq> sets M" "disjoint_family B"
      then have [measurable]:"\<And>i. B i \<in> sets M" and "disjoint_family (\<lambda>j. B j \<inter> {from_nat_into (space M) i})"
        by(auto simp: disjoint_family_on_def)
      then have "(\<Sum>j. emeasure M (B j \<inter> {from_nat_into (space M) i})) = emeasure M (\<Union> (range (\<lambda>j. B j \<inter> {from_nat_into (space M) i})))"
        by(intro suminf_emeasure) auto
      thus "(\<Sum>j. emeasure M (B j \<inter> {from_nat_into (space M) i})) = emeasure M (\<Union> (range B) \<inter> {from_nat_into (space M) i})"
        by simp
    qed
    have 2:"positive (sets M) (\<lambda>A. emeasure M (A \<inter> {from_nat_into (space M) i}))"
      by(auto simp: positive_def)
    show ?thesis
      by(simp add: Mi_def emeasure_measure_of_sigma[OF sets.sigma_algebra_axioms 2 1])
  qed
  define Mi' where "Mi' \<equiv> (\<lambda>i. if i \<in> to_nat_on (space M) ` (space M) then Mi i else null_measure M)"
  have [measurable_cong, simp]: "sets (Mi' i) = sets M" for i
    by(auto simp: Mi'_def)
  show ?thesis
  proof(rule s_finite_measure_s_finite_sumI[where Mi=Mi'])
    fix A
    assume A[measurable]: "A \<in> sets M"
    show "emeasure M A = (\<Sum>i. emeasure (Mi' i) A)" (is "?lhs = ?rhs")
    proof -
      have "?lhs = (\<integral>\<^sup>+ x. emeasure M {x} \<partial>count_space A)"
        using sets.sets_into_space[OF A] by(auto intro!: emeasure_countable_singleton simp: assms(2) countable_subset[OF _ assms(1)])
      also have "... = (\<integral>\<^sup>+ x. emeasure (Mi (to_nat_on (space M) x)) A \<partial>count_space A)"
      proof(safe intro!: nn_integral_cong)
        fix x
        assume "x \<in> space (count_space A)"
        then have 1:"x \<in> A" by simp
        hence 2:"to_nat_on (space M) x \<in> to_nat_on (space M) ` (space M)"
          using A assms(2) by auto
        have [simp]: "from_nat_into (space M) (to_nat_on (space M) x) = x"
          by (metis 1 2 A assms(1) eq_from_nat_into_iff in_mono sets.sets_into_space)
        show "emeasure M {x} = emeasure (Mi (to_nat_on (space M) x)) A"
          using 1 by(simp add: emeasure_Mi[OF A 2])
      qed
      also have "... = (\<integral>\<^sup>+ x\<in>A. emeasure (Mi (to_nat_on (space M) x)) A \<partial>count_space UNIV)"
        by (simp add: nn_integral_count_space_indicator)
      also have "... = (\<integral>\<^sup>+ i\<in>to_nat_on (space M) ` A. emeasure (Mi i) A \<partial>count_space UNIV)"
        by(rule nn_integral_count_compose_inj[OF inj_on_subset[OF inj_on_to_nat_on[OF assms(1)] sets.sets_into_space[OF A]]])
      also have "... = (\<integral>\<^sup>+ i\<in>to_nat_on (space M) ` A. emeasure (Mi' i) A \<partial>count_space UNIV)"
      proof -
        {
          fix x
          assume "x \<in> A"
          then have "to_nat_on (space M) x \<in> to_nat_on (space M) ` (space M)"
            using sets.sets_into_space[OF A] by auto
          hence "emeasure (Mi (to_nat_on (space M) x)) A = emeasure (Mi' (to_nat_on (space M) x)) A"
            by(auto simp: Mi'_def)
        }
        thus ?thesis
          by(auto intro!: nn_integral_cong simp: indicator_def)
      qed
      also have "... = (\<integral>\<^sup>+ i. emeasure (Mi' i) A \<partial>count_space UNIV)"
      proof -
        { 
          fix i
          assume i:"i \<notin> to_nat_on (space M) ` A"
          have "from_nat_into (space M) i \<notin> A" if "i \<in> to_nat_on (space M) ` (space M)"
            by (metis i image_eqI that to_nat_on_from_nat_into)
          with emeasure_Mi have "emeasure (Mi' i) A = 0"
            by(auto simp: Mi'_def)
        }
        thus ?thesis
          by(auto intro!: nn_integral_cong simp: indicator_def)
      qed
      also have "... = ?rhs"
        by(rule nn_integral_count_space_nat)
      finally show ?thesis .
    qed
  next
    fix i
    show "s_finite_measure (Mi' i)"
    proof -
      {
        fix x
        assume h:"x \<in> space M" "i = to_nat_on (space M) x"
        then have i:"i \<in> to_nat_on (space M) ` space M"
          by blast
        have x: "from_nat_into (space M) i = x"
          using h by (simp add: assms(1))
        consider "M {x} = 0" | "M {x} \<noteq> 0" "M {x} < \<infinity>" | "M {x} = \<infinity>"
          using top.not_eq_extremum by fastforce
        hence "s_finite_measure (Mi (to_nat_on (space M) x))"
        proof cases
          case 1
          then have [simp]:"Mi i = null_measure M"
            by(auto intro!: measure_eqI simp: emeasure_Mi[OF _ i] x Int_insert_right)
          show ?thesis
            by(auto simp: h(2)[symmetric] intro!: finite_measure.s_finite_measure_finite_measure finite_measureI)
        next
          case 2
          then show ?thesis
            unfolding h(2)[symmetric]
            by(auto intro!: finite_measure.s_finite_measure_finite_measure finite_measureI simp: sets_eq_imp_space_eq[OF sets_Mi] emeasure_Mi[OF _ i] x h(1))
        next
          case 3
          show ?thesis
            unfolding h(2)[symmetric] s_finite_measure_def
          proof(safe intro!: exI[where x="\<lambda>j. return M x"] prob_space.finite_measure prob_space_return h(1))
            fix A
            assume "A \<in> sets (Mi i)"
            then have [measurable]: "A \<in> sets M"
              by(simp add: Mi_def)
            thus "emeasure (Mi i) A = (\<Sum>i. emeasure (return M x) A)"
              by(simp add: emeasure_Mi[OF _ i] x) (cases "x \<in> A",auto simp: 3 nn_integral_count_space_nat[symmetric])
          qed(auto simp: Mi_def)
        qed
      }
      thus ?thesis
        by(auto simp: Mi'_def) (auto intro!: finite_measure.s_finite_measure_finite_measure finite_measureI)
    qed
  qed simp
qed

lemma s_finite_measure_subprob_space:
 "s_finite_measure M \<longleftrightarrow> (\<exists>Mi :: nat \<Rightarrow> 'a measure. (\<forall>i. sets (Mi i) = sets M) \<and> (\<forall>i. (Mi i) (space M) \<le> 1) \<and> (\<forall>A\<in>sets M. M A = (\<Sum>i. Mi i A)))"
proof
  assume "\<exists>Mi. (\<forall>i. sets (Mi i) = sets M) \<and> (\<forall>i. emeasure (Mi i) (space M) \<le> 1) \<and> (\<forall>A\<in>sets M. M A = (\<Sum>i. (Mi i) A))"
  then obtain Mi where 1:"\<And>i. sets (Mi i) = sets M" "\<And>i. emeasure (Mi i) (space M) \<le> 1" "(\<forall>A\<in>sets M. M A = (\<Sum>i. (Mi i) A))"
    by auto
  thus "s_finite_measure M"
    by(auto simp: s_finite_measure_def sets_eq_imp_space_eq[OF 1(1)] intro!: finite_measureI exI[where x=Mi])  (metis ennreal_one_less_top linorder_not_le)
next
  assume "s_finite_measure M"
  then obtain Mi' where Mi': "\<And>i. sets (Mi' i) = sets M" "\<And>i. finite_measure (Mi' i)" "\<And>A. A\<in>sets M \<Longrightarrow> M A = (\<Sum>i. Mi' i A)"
    by (metis s_finite_measure.s_finite_sum)
  obtain u where u:"\<And>i. u i < \<infinity>" "\<And>i. Mi' i (space M) = u i"
    using Mi'(2) finite_measure.emeasure_finite top.not_eq_extremum by fastforce
  define Mmn where "Mmn \<equiv> (\<lambda>(m,n). if n < nat \<lceil>enn2real (u m)\<rceil> then scale_measure (1 / ennreal (real_of_int \<lceil>enn2real (u m)\<rceil>)) (Mi' m) else (sigma (space M) (sets M)))"
  have sets_Mmn : "sets (Mmn k) = sets M" for k by(simp add: Mmn_def split_beta Mi')
  have emeasure_Mmn: "(Mmn (m, n)) A = (Mi' m A) / ennreal (real_of_int \<lceil>enn2real (u m)\<rceil>)" if "n < nat \<lceil>enn2real (u m)\<rceil>" "A \<in> sets M" for n m A
    by(auto simp: Mmn_def that ennreal_divide_times)
  have emeasure_Mmn_less1: "(Mmn (m, n)) A \<le> 1" for m n A
  proof (cases "n < nat \<lceil>enn2real (u m)\<rceil> \<and> A \<in> sets M")
    case h:True
    have "(Mi' m) A \<le> ennreal (real_of_int \<lceil>enn2real (u m)\<rceil>)"
      by(rule order.trans[OF emeasure_mono[OF sets.sets_into_space sets.top]]) (insert u(1) h, auto simp: u(2)[symmetric] enn2real_le top.not_eq_extremum sets_eq_imp_space_eq[OF Mi'(1)] Mi'(1))
    with h show ?thesis
      by(simp add: emeasure_Mmn) (metis divide_le_posI_ennreal dual_order.eq_iff ennreal_zero_divide mult.right_neutral not_gr_zero zero_le)
  qed(auto simp: Mmn_def emeasure_sigma emeasure_notin_sets  Mi')
  have Mi'_sum:"Mi' m A = (\<Sum>n. Mmn (m, n) A)" if "A \<in> sets M" for m A
  proof -
    have "(\<Sum>n. Mmn (m, n) A) = (\<Sum>n. Mmn (m, n + nat \<lceil>enn2real (u m)\<rceil>) A) + (\<Sum>n< nat \<lceil>enn2real (u m)\<rceil>. Mmn (m, n) A)"
      by(simp add: suminf_offset[where f="\<lambda>n. Mmn (m, n) A"])
    also have "... = (\<Sum>n< nat \<lceil>enn2real (u m)\<rceil>. Mmn (m, n) A)"
      by(simp add: emeasure_sigma Mmn_def)
    also have "... = (\<Sum>n< nat \<lceil>enn2real (u m)\<rceil>. (Mi' m A) / ennreal (real_of_int \<lceil>enn2real (u m)\<rceil>))"
      by(rule Finite_Cartesian_Product.sum_cong_aux) (auto simp: emeasure_Mmn that)
    also have "... = Mi' m A"
    proof (cases "nat \<lceil>enn2real (u m)\<rceil>")
      case 0
      with u[of m] show ?thesis
        by simp (metis Mi'(1) emeasure_mono enn2real_positive_iff less_le_not_le linorder_less_linear not_less_zero sets.sets_into_space sets.top that)
    next
      case (Suc n')
      then have "ennreal (real_of_int \<lceil>enn2real (u m)\<rceil>) > 0"
        using ennreal_less_zero_iff by fastforce
      with u(1)[of m] have "of_nat (nat \<lceil>enn2real (u m)\<rceil>) / ennreal (real_of_int \<lceil>enn2real (u m)\<rceil>) = 1"
        by (simp add: ennreal_eq_0_iff ennreal_of_nat_eq_real_of_nat)
      thus ?thesis
        by (simp add: ennreal_divide_times[symmetric])
    qed
    finally show ?thesis ..
  qed
  define Mi where "Mi \<equiv> (\<lambda>i. Mmn (prod_decode i))"
  show "\<exists>Mi. (\<forall>i. sets (Mi i) = sets M) \<and> (\<forall>i. emeasure (Mi i) (space M) \<le> 1) \<and> (\<forall>A\<in>sets M. M A = (\<Sum>i. (Mi i) A))"
   by(auto intro!: exI[where x=Mi] simp: Mi_def sets_Mmn suminf_ennreal_2dimen[OF Mi'_sum] Mi'(3)) (metis emeasure_Mmn_less1 prod_decode_aux.cases)
qed

lemma(in s_finite_measure) finite_measures:
  obtains Mi where "\<And>i. sets (Mi i) = sets M" "\<And>i. (Mi i) (space M) \<le> 1" "\<And>A. M A = (\<Sum>i. Mi i A)"
proof -
  obtain Mi where Mi:"\<And>i. sets (Mi i) = sets M" "\<And>i. (Mi i) (space M) \<le> 1" "\<And>A. A \<in> sets M \<Longrightarrow> M A = (\<Sum>i. Mi i A)"
    using s_finite_measure_axioms by(metis s_finite_measure_subprob_space)
  hence "M A = (\<Sum>i. Mi i A)" for A
    by(cases "A \<in> sets M") (auto simp: emeasure_notin_sets)
  with Mi(1,2) show ?thesis
    using that by blast
qed

lemma(in s_finite_measure) finite_measures_ne:
  assumes "space M \<noteq> {}"
  obtains Mi where "\<And>i. sets (Mi i) = sets M" "\<And>i. subprob_space (Mi i)" "\<And>A. M A = (\<Sum>i. Mi i A)"
  by (metis assms finite_measures sets_eq_imp_space_eq subprob_spaceI)

lemma(in s_finite_measure) finite_measures':
  obtains Mi where "\<And>i. sets (Mi i) = sets M" "\<And>i. finite_measure (Mi i)" "\<And>A. M A = (\<Sum>i. Mi i A)"
  by (metis ennreal_top_neq_one finite_measureI finite_measures infinity_ennreal_def sets_eq_imp_space_eq top.extremum_uniqueI)

lemma(in s_finite_measure) s_finite_measure_distr:
  assumes f[measurable]:"f \<in> M \<rightarrow>\<^sub>M N"
  shows "s_finite_measure (distr M N f)"
proof -
  obtain Mi where Mi[measurable_cong]:"\<And>i. sets (Mi i) = sets M" "\<And>i. finite_measure (Mi i)" "\<And>A. M A = (\<Sum>i. Mi i A)"
    by(metis finite_measures')
  show ?thesis
    by(auto intro!: s_finite_measureI[where Mi="(\<lambda>i. distr (Mi i) N f)"] finite_measure.finite_measure_distr[OF Mi(2)] simp: emeasure_distr Mi(3) sets_eq_imp_space_eq[OF Mi(1)])
qed

lemma nn_integral_measure_suminf:
  assumes [measurable_cong]:"\<And>i. sets (Mi i) = sets M" and "\<And>A. A\<in>sets M \<Longrightarrow> M A = (\<Sum>i. Mi i A)" "f \<in> borel_measurable M"
  shows "(\<Sum>i. \<integral>\<^sup>+x. f x \<partial>(Mi i)) = (\<integral>\<^sup>+x. f x \<partial>M)"
  using assms(3)
proof induction
  case (cong f g)
  then show ?case
    by (metis (no_types, lifting) assms(1) nn_integral_cong sets_eq_imp_space_eq suminf_cong)
next
  case (set A)
  then show ?case
    using assms(1,2) by simp
next
  case (mult u c)
  then show ?case
    by(simp add: nn_integral_cmult)
next
  case (add u v)
  then show ?case
    by(simp add: nn_integral_add suminf_add[symmetric])
next
  case ih:(seq U)
  have "(\<Sum>i. integral\<^sup>N (Mi i) (\<Squnion> range U)) = (\<Sum>i. \<integral>\<^sup>+ x. (\<Squnion>j. U j x)  \<partial>(Mi i))"
    by(auto intro!: suminf_cong) (metis SUP_apply)
  also have "... = (\<Sum>i. \<Squnion>j. \<integral>\<^sup>+ x. U j x \<partial>(Mi i))"
    using ih by(auto intro!: suminf_cong nn_integral_monotone_convergence_SUP)
  also have "... = (\<Squnion>j. (\<Sum>i. \<integral>\<^sup>+ x. U j x \<partial>(Mi i)))"
    using ih(3) by(auto intro!: ennreal_suminf_SUP_eq incseq_nn_integral)
  also have "... = (\<Squnion>j. integral\<^sup>N M (U j))"
    by(simp add: ih)
  also have "... = (\<integral>\<^sup>+ x. (\<Squnion>j. U j x) \<partial>M)"
    using ih by(auto intro!: nn_integral_monotone_convergence_SUP[symmetric])
  also have "... = integral\<^sup>N M (\<Squnion> range U)"
    by(metis SUP_apply)
  finally show ?case .
qed

text \<open> A @{term \<open>density M f\<close>} of $s$-finite measure @{term M} and @{term \<open>f \<in> borel_measurable M\<close>} is again s-finite.
       We do not require additional assumption, unlike $\sigma$-finite measures.\<close>
lemma(in s_finite_measure) s_finite_measure_density:
  assumes f[measurable]:"f \<in> borel_measurable M"
    shows "s_finite_measure (density M f)"
proof -
  obtain Mi where Mi[measurable_cong]:"\<And>i. sets (Mi i) = sets M" "\<And>i. finite_measure (Mi i)" "\<And>A. M A = (\<Sum>i. Mi i A)"
    by(metis finite_measures')
  show ?thesis
  proof(rule s_finite_measure_s_finite_sumI[where Mi="\<lambda>i. density (Mi i) f"])
    show "s_finite_measure (density (Mi i) f)" for i
    proof -
      define Mij where "Mij = (\<lambda>j::nat. if j = 0 then density (Mi i) (\<lambda>x. \<infinity> * indicator {x\<in>space M. f x = \<infinity>} x)
                                   else if j = 1 then density (Mi i) (\<lambda>x. f x * indicator {x\<in>space M. f x < \<infinity>} x)
                                   else null_measure M)"
      have sets_Mij[measurable_cong]: "sets (Mij j) = sets M" for j
        by(auto simp: Mij_def Mi)
      have emeasure_Mi:"density (Mi i) f A = (\<Sum>j. Mij j A)" (is "?lhs = ?rhs") if A[measurable]: "A \<in> sets M" for A
      proof -
        have "?lhs = (\<integral>\<^sup>+x \<in> A. f x \<partial>Mi i)"
          by(simp add: emeasure_density)
        also have "... = (\<integral>\<^sup>+x. \<infinity> * indicator {x\<in>space M. f x = \<infinity>} x * indicator A x + f x * indicator {x\<in>space M. f x < \<infinity>} x * indicator A x \<partial>Mi i)"
          by(auto intro!: nn_integral_cong simp: sets_eq_imp_space_eq[OF Mi(1)] indicator_def) (simp add: top.not_eq_extremum)
        also have "... = density (Mi i) (\<lambda>x. \<infinity> * indicator {x\<in>space M. f x = \<infinity>} x) A + density (Mi i) (\<lambda>x. f x * indicator {x\<in>space M. f x < \<infinity>} x) A"
          by(simp add: nn_integral_add emeasure_density)
        also have "... = ?rhs"
          using suminf_finite[of "{..<Suc (Suc 0)}" "\<lambda>j. Mij j A"] by(auto simp: Mij_def)
        finally show ?thesis .
      qed
      show ?thesis
      proof(rule s_finite_measure_s_finite_sumI[OF _ _ emeasure_Mi])
        fix j :: nat
        consider "j = 0" | "j = 1" | "j \<noteq> 0" "j \<noteq> 1" by auto
        then show "s_finite_measure (Mij j)"
        proof cases
          case 1
          have 2:"Mij j A = (\<Sum>k. density (Mi i) (indicator {x\<in>space M. f x = \<top>}) A)" if A[measurable]:"A \<in> sets M" for A
            by(auto simp: Mij_def 1 emeasure_density nn_integral_suminf[symmetric] sets_eq_imp_space_eq[OF Mi(1)] indicator_def  intro!: nn_integral_cong) (simp add: nn_integral_count_space_nat[symmetric])
          show ?thesis
            by(auto simp: s_finite_measure_def 2 Mi(1)[of i] sets_Mij[of j] intro!: exI[where x="\<lambda>k. density (Mi i) (indicator {x\<in>space M. f x = \<infinity>})"] finite_measure.finite_measure_restricted Mi(2))
        next
          case 2
          show ?thesis
            by(auto intro!: sigma_finite_measure.s_finite_measure AE_mono_measure[OF Mi(1)] sum_le_suminf[where I="{i}" and f="\<lambda>i. Mi i _",simplified] simp: sigma_finite_measure.sigma_finite_iff_density_finite[OF finite_measure.sigma_finite_measure[OF Mi(2)[of i]]] le_measure[OF Mi(1)] Mi indicator_def 2 Mij_def) auto
        next
          case 3
          then show ?thesis
            by(auto simp: Mij_def intro!: finite_measure.s_finite_measure_finite_measure finite_measureI)
        qed
      qed(auto simp: sets_Mij Mi)
    qed 
  qed(auto simp: emeasure_density nn_integral_measure_suminf[OF Mi(1,3)] Mi(1))
qed

lemma
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes [measurable_cong]:"\<And>i. sets (Mi i) = sets M" and "\<And>A. A\<in>sets M \<Longrightarrow> M A = (\<Sum>i. Mi i A)" "integrable M f"
  shows lebesgue_integral_measure_suminf:"(\<Sum>i. \<integral>x. f x \<partial>(Mi i)) = (\<integral>x. f x \<partial>M)" (is "?suminf")
    and lebesgue_integral_measure_suminf_summable_norm: "summable (\<lambda>i. norm (\<integral>x. f x \<partial>(Mi i)))" (is "?summable2")
    and lebesgue_integral_measure_suminf_summable_norm_in: "summable (\<lambda>i. \<integral>x. norm (f x) \<partial>(Mi i))" (is "?summable")
proof -
  have Mi:"Mi i \<le> M" for i
    using assms(2) ennreal_suminf_lessD linorder_not_le by(fastforce simp: assms(1) le_measure[OF assms(1)])
  have sum2: "summable (\<lambda>i. norm (\<integral>x. g x \<partial>(Mi i)))" if "summable (\<lambda>i. \<integral>x. norm (g x) \<partial>(Mi i))" for g :: "'a \<Rightarrow> 'b"
  proof(rule summable_suminf_not_top)
    have "(\<Sum>i. ennreal (norm (\<integral>x. g x \<partial>(Mi i)))) \<le> (\<Sum>i. ennreal (\<integral>x. norm (g x) \<partial>(Mi i)))"
      by(auto intro!: suminf_le)
    thus "(\<Sum>i. ennreal (norm (\<integral>x. g x \<partial>(Mi i)))) \<noteq> \<top>"
      by (metis ennreal_suminf_neq_top[OF that] Bochner_Integration.integral_nonneg neq_top_trans norm_ge_zero)
  qed simp    
  have "?suminf \<and> ?summable"
    using assms(3)
  proof induction
    case h[measurable]:(base A c)
    have Mi_fin:"Mi i A < \<infinity>" for i
      by(rule order.strict_trans1[OF _ h(2)], auto simp: le_measureD3[OF Mi assms(1)])
    have 1: "(\<integral>x. (indicat_real A x *\<^sub>R c) \<partial>Mi i) = measure (Mi i) A *\<^sub>R c" for i
      using Mi_fin by simp
    have 2:"summable (\<lambda>i. \<integral>x. norm (indicat_real A x *\<^sub>R c) \<partial>Mi i)"
    proof(rule summable_suminf_not_top)
      show "(\<Sum>i. ennreal (\<integral>x. norm (indicat_real A x *\<^sub>R c) \<partial>Mi i)) \<noteq> \<top>" (is "?l \<noteq> _")
      proof -
        have "?l = (\<Sum>i. Mi i A ) * norm c"
          using Mi_fin by(auto intro!: suminf_cong simp: measure_def enn2real_mult ennreal_mult)
        also have "... = M A * norm c"
          by(simp add: assms(2))
        also have "... \<noteq> \<top>"
          using h(2) by (simp add: ennreal_mult_less_top top.not_eq_extremum)
        finally show ?thesis .
      qed
    qed simp
    have 3: "(\<Sum>i. \<integral>x. indicat_real A x *\<^sub>R c \<partial>Mi i) = (\<integral>x. indicat_real A x *\<^sub>R c \<partial>M)" (is "?l = ?r")
    proof -
      have [simp]: "summable (\<lambda>i. enn2real (Mi i A))"
        using Mi_fin h by(auto intro!: summable_suminf_not_top simp: assms(2)[symmetric])
      have "?l = (\<Sum>i. measure (Mi i) A) *\<^sub>R c"
        by(auto intro!: suminf_cong simp: 1 measure_def suminf_scaleR_left)
      also have "... = ?r"
        using h(2) Mi_fin by(simp add: ennreal_inj[where a="(\<Sum>i. measure (Mi i) A)" and b="measure M A",OF suminf_nonneg measure_nonneg,symmetric,simplified measure_def] measure_def suminf_ennreal2[symmetric] assms(2)[symmetric])
      finally show ?thesis .
    qed
    from 2 3 show ?case by simp
  next
    case ih[measurable]:(add f g)
    have 1:"summable (\<lambda>i. \<integral>x. norm (f x + g x) \<partial>Mi i)"
    proof(rule summable_suminf_not_top)
      show "(\<Sum>i. ennreal (\<integral>x. norm (f x + g x) \<partial>Mi i)) \<noteq> \<top>" (is "?l \<noteq> _")
      proof -
        have "?l = (\<Sum>i. (\<integral>\<^sup>+x. ennreal (norm (f x + g x)) \<partial>Mi i))"
          using ih by(auto intro!: suminf_cong nn_integral_eq_integral[symmetric] integrable_mono_measure[OF assms(1) Mi])
        also have "... \<le> (\<Sum>i. (\<integral>\<^sup>+x. ennreal (norm (f x) + norm (g x)) \<partial>Mi i))"
          by(auto intro!: suminf_le nn_integral_mono norm_triangle_ineq simp del: ennreal_plus)
        also have "... = (\<Sum>i. (\<integral>\<^sup>+x. ennreal (norm (f x)) \<partial>Mi i)) + (\<Sum>i. (\<integral>\<^sup>+x. ennreal (norm (g x)) \<partial>Mi i))"
          by(auto intro!: suminf_cong simp: nn_integral_add suminf_add)
        also have "... = (\<Sum>i. ennreal (\<integral>x. norm (f x) \<partial>Mi i)) + (\<Sum>i. ennreal (\<integral>x. norm (g x) \<partial>Mi i))"
          using ih by(simp add: nn_integral_eq_integral integrable_mono_measure[OF assms(1) Mi])
        also have "... < \<top>"
          using ennreal_suminf_neq_top[OF conjunct2[OF ih(3)]] ennreal_suminf_neq_top[OF conjunct2[OF ih(4)]]
          by (meson Bochner_Integration.integral_nonneg ennreal_add_eq_top norm_ge_zero top.not_eq_extremum)
        finally show ?thesis
          using order.strict_iff_order by blast
      qed
    qed simp
    with ih show ?case
      by(auto simp: Bochner_Integration.integral_add[OF integrable_mono_measure[OF assms(1) Mi ih(1)] integrable_mono_measure[OF assms(1) Mi ih(2)]] suminf_add[symmetric,OF summable_norm_cancel[OF sum2[OF conjunct2[OF ih(3)]]] summable_norm_cancel[OF sum2[OF conjunct2[OF ih(4)]]]])
  next
    case ih[measurable]:(lim f fn)
    have 1:"summable (\<lambda>i. \<integral>x. norm (f x) \<partial>(Mi i))"
    proof(rule summable_suminf_not_top)
      show "(\<Sum>i. ennreal (\<integral>x. norm (f x) \<partial>(Mi i))) \<noteq> \<top>" (is "?lhs \<noteq> _")
      proof -
        have "?lhs = (\<Sum>i. \<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>Mi i)"
          by(auto intro!: suminf_cong nn_integral_eq_integral[symmetric] integrable_mono_measure[OF assms(1) Mi] simp: ih)
        also have "... = (\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>M)"
          by(simp add: nn_integral_measure_suminf[OF assms(1,2)])
        also have "... = ennreal (\<integral> x. norm (f x) \<partial>M)"
          by(auto intro!: nn_integral_eq_integral ih(4))
        also have "... < \<top>" by simp
        finally show "?lhs \<noteq> \<top>"
          using linorder_neq_iff by blast
      qed
    qed simp
    have "(\<Sum>i. \<integral>x. f x \<partial>(Mi i)) = (\<integral>i. \<integral>x. f x \<partial>(Mi i) \<partial>(count_space UNIV))"
      by(rule integral_count_space_nat[symmetric]) (simp add: integrable_count_space_nat_iff sum2[OF 1])
    also have "... = lim (\<lambda>m. \<integral>i. \<integral>x. fn m x \<partial>(Mi i) \<partial>(count_space UNIV))"
    proof(rule limI[OF integral_dominated_convergence[where w="\<lambda>i. 2 * (\<integral>x. norm (f x) \<partial>(Mi i))"],symmetric],auto simp: AE_count_space integrable_count_space_nat_iff 1)
      show "(\<lambda>m. \<integral>x. fn m x \<partial>(Mi i)) \<longlonglongrightarrow> \<integral>x. f x \<partial>(Mi i)" for i
        by(rule integral_dominated_convergence[where w="\<lambda>x. 2 * norm (f x)"],insert ih) (auto intro!: integrable_mono_measure[OF assms(1) Mi] simp: sets_eq_imp_space_eq[OF assms(1)])
    next
      fix i j
      show "norm (\<integral>x. fn j x \<partial>(Mi i)) \<le> 2 * (\<integral>x. norm (f x) \<partial>(Mi i))" (is "?l \<le> ?r")
      proof -
        have "?l \<le> (\<integral>x. norm (fn j x) \<partial>(Mi i))"
          by simp
        also have "... \<le> (\<integral>x. 2 * norm (f x) \<partial>(Mi i))"
          by(rule integral_mono,insert ih) (auto intro!: integrable_mono_measure[OF assms(1) Mi] simp: sets_eq_imp_space_eq[OF assms(1)])
        finally show "?l \<le> ?r" by simp
      qed
    qed
    also have "... = lim (\<lambda>m. (\<Sum>i. \<integral>x. fn m x \<partial>(Mi i)))"
    proof -
      have "(\<integral>i. \<integral>x. fn m x \<partial>(Mi i) \<partial>(count_space UNIV)) = (\<Sum>i. \<integral>x. fn m x \<partial>(Mi i))" for m
        by(auto intro!: integral_count_space_nat sum2 simp: integrable_count_space_nat_iff) (use ih(5) in auto)
      thus ?thesis by simp
    qed
    also have "... = lim (\<lambda>m. \<integral>x. fn m x \<partial>M)"
      by(simp add: ih(5))
    also have "... = (\<integral>x. f x \<partial>M)"
      using ih by(auto intro!: limI[OF integral_dominated_convergence[where w="\<lambda>x. 2 * norm (f x)"]])
    finally show ?case
      using 1 by auto
  qed
  thus ?suminf ?summable ?summable2
    by(simp_all add: sum2)
qed

(* Ported from sigma-finite measure. 
   The following proof is easier than the sigma-finite measure version. *)
lemma (in s_finite_measure) measurable_emeasure_Pair':
  assumes "Q \<in> sets (N \<Otimes>\<^sub>M M)"
  shows "(\<lambda>x. emeasure M (Pair x -` Q)) \<in> borel_measurable N" (is "?s Q \<in> _")
proof -
  obtain Mi where Mi:"\<And>i. sets (Mi i) = sets M" "\<And>i. finite_measure (Mi i)" "\<And>A. M A = (\<Sum>i. Mi i A)"
    by(metis finite_measures')
  show ?thesis
    using Mi(1,2) assms finite_measure.finite_measure_cut_measurable[of "Mi _" Q N]
    by(simp add: Mi(3))
qed

lemma (in s_finite_measure) measurable_emeasure'[measurable (raw)]:
  assumes space: "\<And>x. x \<in> space N \<Longrightarrow> A x \<subseteq> space M"
  assumes A: "{x\<in>space (N \<Otimes>\<^sub>M M). snd x \<in> A (fst x)} \<in> sets (N \<Otimes>\<^sub>M M)"
  shows "(\<lambda>x. emeasure M (A x)) \<in> borel_measurable N"
proof -
  from space have "\<And>x. x \<in> space N \<Longrightarrow> Pair x -` {x \<in> space (N \<Otimes>\<^sub>M M). snd x \<in> A (fst x)} = A x"
    by (auto simp: space_pair_measure)
  with measurable_emeasure_Pair'[OF A] show ?thesis
    by (auto cong: measurable_cong)
qed


lemma(in s_finite_measure) emeasure_pair_measure':
  assumes "X \<in> sets (N \<Otimes>\<^sub>M M)"
  shows "emeasure (N \<Otimes>\<^sub>M M) X = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator X (x, y) \<partial>M \<partial>N)" (is "_ = ?\<mu> X")
proof (rule emeasure_measure_of[OF pair_measure_def])
  show "positive (sets (N \<Otimes>\<^sub>M M)) ?\<mu>"
    by (auto simp: positive_def)
  have eq[simp]: "\<And>A x y. indicator A (x, y) = indicator (Pair x -` A) y"
    by (auto simp: indicator_def)
  show "countably_additive (sets (N \<Otimes>\<^sub>M M)) ?\<mu>"
  proof (rule countably_additiveI)
    fix F :: "nat \<Rightarrow> ('b \<times> 'a) set" assume F: "range F \<subseteq> sets (N \<Otimes>\<^sub>M M)" "disjoint_family F"
    from F have *: "\<And>i. F i \<in> sets (N \<Otimes>\<^sub>M M)" by auto
    moreover have "\<And>x. disjoint_family (\<lambda>i. Pair x -` F i)"
      by (intro disjoint_family_on_bisimulation[OF F(2)]) auto
    moreover have "\<And>x. range (\<lambda>i. Pair x -` F i) \<subseteq> sets M"
      using F by (auto simp: sets_Pair1)
    ultimately show "(\<Sum>n. ?\<mu> (F n)) = ?\<mu> (\<Union>i. F i)"
      by (auto simp add: nn_integral_suminf[symmetric] vimage_UN suminf_emeasure
               intro!: nn_integral_cong nn_integral_indicator[symmetric]) 
  qed
  show "{a \<times> b |a b. a \<in> sets N \<and> b \<in> sets M} \<subseteq> Pow (space N \<times> space M)"
    using sets.space_closed[of N] sets.space_closed[of M] by auto
qed fact

lemma (in s_finite_measure) emeasure_pair_measure_alt':
  assumes X: "X \<in> sets (N \<Otimes>\<^sub>M M)"
  shows "emeasure (N \<Otimes>\<^sub>M M) X = (\<integral>\<^sup>+x. emeasure M (Pair x -` X) \<partial>N)"
proof -
  have [simp]: "\<And>x y. indicator X (x, y) = indicator (Pair x -` X) y"
    by (auto simp: indicator_def)
  show ?thesis
    using X by (auto intro!: nn_integral_cong simp: emeasure_pair_measure' sets_Pair1)
qed

proposition (in s_finite_measure) emeasure_pair_measure_Times':
  assumes A: "A \<in> sets N" and B: "B \<in> sets M"
  shows "emeasure (N \<Otimes>\<^sub>M M) (A \<times> B) = emeasure N A * emeasure M B"
proof -
  have "emeasure (N \<Otimes>\<^sub>M M) (A \<times> B) = (\<integral>\<^sup>+x. emeasure M B * indicator A x \<partial>N)"
    using A B by (auto intro!: nn_integral_cong simp: emeasure_pair_measure_alt')
  also have "\<dots> = emeasure M B * emeasure N A"
    using A by (simp add: nn_integral_cmult_indicator)
  finally show ?thesis
    by (simp add: ac_simps)
qed

lemma(in s_finite_measure) measure_times:
  assumes[measurable]: "A \<in> sets N" "B \<in> sets M"
  shows "measure (N \<Otimes>\<^sub>M M) (A \<times> B) = measure N A * measure M B"
  by(auto simp: measure_def emeasure_pair_measure_Times' enn2real_mult)

lemma pair_measure_s_finite_measure_suminf:
  assumes Mi[measurable_cong]:"\<And>i. sets (Mi i) = sets M" "\<And>i. finite_measure (Mi i)" "\<And>A. M A = (\<Sum>i. Mi i A)"
      and Ni[measurable_cong]:"\<And>i. sets (Ni i) = sets N" "\<And>i. finite_measure (Ni i)" "\<And>A. N A = (\<Sum>i. Ni i A)"
    shows "(M \<Otimes>\<^sub>M N) A = (\<Sum>i j. (Mi i \<Otimes>\<^sub>M Ni j) A)" (is "?lhs = ?rhs")
proof -
  interpret N: s_finite_measure N
    by(auto intro!: s_finite_measureI[where Mi=Mi] s_finite_measureI[where Mi=Ni] assms)
  show ?thesis
  proof(cases "A \<in> sets (M \<Otimes>\<^sub>M N)")
    case [measurable]:True
    show ?thesis
    proof -
      have "?lhs = (\<integral>\<^sup>+x. N (Pair x -` A) \<partial>M)"
        by(simp add: N.emeasure_pair_measure_alt')
      also have "... = (\<Sum>i. \<integral>\<^sup>+x. N (Pair x -` A) \<partial>Mi i)"
        using N.measurable_emeasure_Pair'[of A]
        by(auto intro!: nn_integral_measure_suminf[OF Mi(1,3),symmetric])
      also have "... = (\<Sum>i. \<integral>\<^sup>+x. (\<Sum>j. Ni j (Pair x -` A)) \<partial>Mi i)"
        by(simp add: Ni(3))
      also have "... = (\<Sum>i j. \<integral>\<^sup>+x. Ni j (Pair x -` A) \<partial>Mi i)"
        using  s_finite_measure.measurable_emeasure_Pair'[OF finite_measure.s_finite_measure_finite_measure[OF Ni(2)],of A]
        by(auto simp: nn_integral_suminf intro!: suminf_cong)
      also have "... = ?rhs"
        by(auto intro!: suminf_cong simp: s_finite_measure.emeasure_pair_measure_alt'[OF finite_measure.s_finite_measure_finite_measure[OF Ni(2)]])
      finally show ?thesis .
    qed
  next
    case False
    with Mi(1) Ni(1) show ?thesis
      by(simp add: emeasure_notin_sets)
  qed
qed

lemma pair_measure_s_finite_measure_suminf':
  assumes Mi[measurable_cong]:"\<And>i. sets (Mi i) = sets M" "\<And>i. finite_measure (Mi i)" "\<And>A. M A = (\<Sum>i. Mi i A)"
      and Ni[measurable_cong]:"\<And>i. sets (Ni i) = sets N" "\<And>i. finite_measure (Ni i)" "\<And>A. N A = (\<Sum>i. Ni i A)"
    shows "(M \<Otimes>\<^sub>M N) A = (\<Sum>i j. (Mi j \<Otimes>\<^sub>M Ni i) A)" (is "?lhs = ?rhs")
proof -
  interpret N: s_finite_measure N
    by(auto intro!: s_finite_measureI[where Mi=Mi] s_finite_measureI[where Mi=Ni] assms)
  show ?thesis
  proof(cases "A \<in> sets (M \<Otimes>\<^sub>M N)")
    case [measurable]:True
    show ?thesis
    proof -
      have "?lhs = (\<integral>\<^sup>+x. N (Pair x -` A) \<partial>M)"
        by(simp add: N.emeasure_pair_measure_alt')
      also have "... = (\<integral>\<^sup>+x. (\<Sum>i. Ni i (Pair x -` A)) \<partial>M)"
        by(auto intro!: nn_integral_cong simp: Ni)
      also have "... = (\<Sum>i. (\<integral>\<^sup>+x. Ni i (Pair x -` A) \<partial>M))"
        by(auto intro!: nn_integral_suminf simp: finite_measure.finite_measure_cut_measurable[OF Ni(2)])
      also have "... = (\<Sum>i j. \<integral>\<^sup>+x. Ni i (Pair x -` A) \<partial>Mi j)"
        by(auto intro!: suminf_cong nn_integral_measure_suminf[symmetric] simp: finite_measure.finite_measure_cut_measurable[OF Ni(2)] Mi)
      also have "... = ?rhs"
        by(auto intro!: suminf_cong simp: s_finite_measure.emeasure_pair_measure_alt'[OF finite_measure.s_finite_measure_finite_measure[OF Ni(2)]])
      finally show ?thesis .
    qed
  next
    case False
    with Mi(1) Ni(1) show ?thesis
      by(simp add: emeasure_notin_sets)
  qed
qed

lemma pair_measure_s_finite_measure:
  assumes "s_finite_measure M" and "s_finite_measure N"
  shows "s_finite_measure (M \<Otimes>\<^sub>M N)"
proof -
  obtain Mi where Mi[measurable_cong]:"\<And>i. sets (Mi i) = sets M" "\<And>i. finite_measure (Mi i)" "\<And>A. M A = (\<Sum>i. Mi i A)"
    by(metis s_finite_measure.finite_measures'[OF assms(1)])
  obtain Ni where Ni[measurable_cong]:"\<And>i. sets (Ni i) = sets N" "\<And>i. finite_measure (Ni i)" "\<And>A. N A = (\<Sum>i. Ni i A)"
    by(metis s_finite_measure.finite_measures'[OF assms(2)])
  show ?thesis
  proof(rule s_finite_measure_prodI[where Mij="\<lambda>i j. Mi i \<Otimes>\<^sub>M Ni j"])
    show "emeasure (Mi i \<Otimes>\<^sub>M Ni j) (space (M \<Otimes>\<^sub>M N)) < \<infinity>" for i j
      using finite_measure.emeasure_finite[OF Mi(2)[of i]] finite_measure.emeasure_finite[OF Ni(2)[of j]]
      by(auto simp: sets_eq_imp_space_eq[OF Mi(1)[of i],symmetric] sets_eq_imp_space_eq[OF Ni(1)[of j],symmetric] space_pair_measure s_finite_measure.emeasure_pair_measure_Times'[OF finite_measure.s_finite_measure_finite_measure[OF Ni(2)[of j]]] ennreal_mult_less_top top.not_eq_extremum)
  qed(auto simp: pair_measure_s_finite_measure_suminf Mi Ni)
qed

lemma(in s_finite_measure) borel_measurable_nn_integral_fst':
  assumes [measurable]: "f \<in> borel_measurable (N \<Otimes>\<^sub>M M)"
  shows "(\<lambda>x. \<integral>\<^sup>+ y. f (x, y) \<partial>M) \<in> borel_measurable N"
proof -
  obtain Mi where Mi[measurable_cong]:"\<And>i. sets (Mi i) = sets M" "\<And>i. finite_measure (Mi i)" "\<And>A. M A = (\<Sum>i. Mi i A)"
    by(metis finite_measures')
  show ?thesis
    by(rule measurable_cong[where g="\<lambda>x. \<Sum>i. \<integral>\<^sup>+ y. f (x, y) \<partial>Mi i",THEN iffD2])
      (auto simp: nn_integral_measure_suminf[OF Mi(1,3)] intro!: borel_measurable_suminf_order sigma_finite_measure.borel_measurable_nn_integral_fst[OF finite_measure.sigma_finite_measure[OF Mi(2)]])
qed

lemma (in s_finite_measure) nn_integral_fst':
  assumes f: "f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M)"
  shows "(\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. f (x, y) \<partial>M \<partial>M1) = integral\<^sup>N (M1 \<Otimes>\<^sub>M M) f" (is "?I f = _")
  using f proof induct
  case (cong u v)
  then have "?I u = ?I v"
    by (intro nn_integral_cong) (auto simp: space_pair_measure)
  with cong show ?case
    by (simp cong: nn_integral_cong)
qed (simp_all add: emeasure_pair_measure' nn_integral_cmult nn_integral_add
                   nn_integral_monotone_convergence_SUP measurable_compose_Pair1
                   borel_measurable_nn_integral_fst' nn_integral_mono incseq_def le_fun_def image_comp
              cong: nn_integral_cong)

lemma (in s_finite_measure) borel_measurable_nn_integral'[measurable (raw)]:
  "case_prod f \<in> borel_measurable (N \<Otimes>\<^sub>M M) \<Longrightarrow> (\<lambda>x. \<integral>\<^sup>+ y. f x y \<partial>M) \<in> borel_measurable N"
  using borel_measurable_nn_integral_fst'[of "case_prod f" N] by simp

lemma distr_pair_swap_s_finite:
  assumes "s_finite_measure M1" and "s_finite_measure M2"
  shows "M1 \<Otimes>\<^sub>M M2 = distr (M2 \<Otimes>\<^sub>M M1) (M1 \<Otimes>\<^sub>M M2) (\<lambda>(x, y). (y, x))" (is "?P = ?D")
proof -
  {
    from s_finite_measure.finite_measures'[OF assms(1)] s_finite_measure.finite_measures'[OF assms(2)]
    obtain Mi1 Mi2
      where Mi1:"\<And>i. sets (Mi1 i) = sets M1" "\<And>i. finite_measure (Mi1 i)" "\<And>A. M1 A = (\<Sum>i. Mi1 i A)"
        and Mi2:"\<And>i. sets (Mi2 i) = sets M2" "\<And>i. finite_measure (Mi2 i)" "\<And>A. M2 A = (\<Sum>i. Mi2 i A)"
      by metis
    fix A
    assume A[measurable]:"A \<in> sets (M1 \<Otimes>\<^sub>M M2)"
    have "emeasure (M1 \<Otimes>\<^sub>M M2) A = emeasure (M2 \<Otimes>\<^sub>M M1) ((\<lambda>(x, y). (y, x)) -` A \<inter> space (M2 \<Otimes>\<^sub>M M1))"
    proof -
      { 
        fix i j
        interpret pair_sigma_finite "Mi1 i" "Mi2 j"
          by(auto simp: pair_sigma_finite_def Mi1(2) Mi2(2) finite_measure.sigma_finite_measure)
        have "emeasure (Mi1 i \<Otimes>\<^sub>M Mi2 j) A = emeasure (Mi2 j \<Otimes>\<^sub>M Mi1 i) ((\<lambda>(x, y). (y, x)) -` A \<inter> space (M2 \<Otimes>\<^sub>M M1))"
          using Mi1(1) Mi2(1) by(simp add: arg_cong[OF distr_pair_swap,of emeasure] emeasure_distr sets_eq_imp_space_eq[OF sets_pair_measure_cong[OF Mi2(1) Mi1(1)]])
      }
      thus ?thesis
        by(auto simp: pair_measure_s_finite_measure_suminf'[OF Mi2 Mi1] pair_measure_s_finite_measure_suminf[OF Mi1 Mi2] intro!: suminf_cong)
    qed
  }
  thus ?thesis
    by(auto intro!: measure_eqI simp: emeasure_distr)
qed

proposition nn_integral_snd':
  assumes "s_finite_measure M1" "s_finite_measure M2"
      and f[measurable]: "f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M2)"
    shows "(\<integral>\<^sup>+ y. (\<integral>\<^sup>+ x. f (x, y) \<partial>M1) \<partial>M2) = integral\<^sup>N (M1 \<Otimes>\<^sub>M M2) f"
proof -
  interpret M1: s_finite_measure M1 by fact
  interpret M2: s_finite_measure M2 by fact
  note measurable_pair_swap[OF f]
  from M1.nn_integral_fst'[OF this]
  have "(\<integral>\<^sup>+ y. (\<integral>\<^sup>+ x. f (x, y) \<partial>M1) \<partial>M2) = (\<integral>\<^sup>+ (x, y). f (y, x) \<partial>(M2 \<Otimes>\<^sub>M M1))"
    by simp
  also have "(\<integral>\<^sup>+ (x, y). f (y, x) \<partial>(M2 \<Otimes>\<^sub>M M1)) = integral\<^sup>N (M1 \<Otimes>\<^sub>M M2) f"
    by (subst distr_pair_swap_s_finite[OF assms(1,2)]) (auto simp add: nn_integral_distr intro!: nn_integral_cong)
  finally show ?thesis .
qed

lemma (in s_finite_measure) borel_measurable_lebesgue_integrable'[measurable (raw)]:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes [measurable]: "case_prod f \<in> borel_measurable (N \<Otimes>\<^sub>M M)"
  shows "Measurable.pred N (\<lambda>x. integrable M (f x))"
proof -
  have [simp]: "\<And>x. x \<in> space N \<Longrightarrow> integrable M (f x) \<longleftrightarrow> (\<integral>\<^sup>+y. norm (f x y) \<partial>M) < \<infinity>"
    unfolding integrable_iff_bounded by simp
  show ?thesis
    by (simp cong: measurable_cong)
qed

lemma (in s_finite_measure) measurable_measure'[measurable (raw)]:
  "(\<And>x. x \<in> space N \<Longrightarrow> A x \<subseteq> space M) \<Longrightarrow>
    {x \<in> space (N \<Otimes>\<^sub>M M). snd x \<in> A (fst x)} \<in> sets (N \<Otimes>\<^sub>M M) \<Longrightarrow>
    (\<lambda>x. measure M (A x)) \<in> borel_measurable N"
  unfolding measure_def by (intro measurable_emeasure' borel_measurable_enn2real) auto

proposition (in s_finite_measure) borel_measurable_lebesgue_integral'[measurable (raw)]:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes f[measurable]: "case_prod f \<in> borel_measurable (N \<Otimes>\<^sub>M M)"
  shows "(\<lambda>x. \<integral>y. f x y \<partial>M) \<in> borel_measurable N"
proof -
  from borel_measurable_implies_sequence_metric[OF f, of 0]
  obtain s where s: "\<And>i. simple_function (N \<Otimes>\<^sub>M M) (s i)"
    and "\<forall>x\<in>space (N \<Otimes>\<^sub>M M). (\<lambda>i. s i x) \<longlonglongrightarrow> (case x of (x, y) \<Rightarrow> f x y)"
    and "\<forall>i. \<forall>x\<in>space (N \<Otimes>\<^sub>M M). dist (s i x) 0 \<le> 2 * dist (case x of (x, xa) \<Rightarrow> f x xa) 0"
    by auto
  then have *:
    "\<And>x y. x \<in> space N \<Longrightarrow> y \<in> space M \<Longrightarrow> (\<lambda>i. s i (x, y)) \<longlonglongrightarrow> f x y"
    "\<And>i x y. x \<in> space N \<Longrightarrow> y \<in> space M \<Longrightarrow> norm (s i (x, y)) \<le> 2 * norm (f x y)"
    by (auto simp: space_pair_measure)

  have [measurable]: "\<And>i. s i \<in> borel_measurable (N \<Otimes>\<^sub>M M)"
    by (rule borel_measurable_simple_function) fact

  have "\<And>i. s i \<in> measurable (N \<Otimes>\<^sub>M M) (count_space UNIV)"
    by (rule measurable_simple_function) fact

  define f' where [abs_def]: "f' i x =
    (if integrable M (f x) then Bochner_Integration.simple_bochner_integral M (\<lambda>y. s i (x, y)) else 0)" for i x

  { fix i x assume "x \<in> space N"
    then have "Bochner_Integration.simple_bochner_integral M (\<lambda>y. s i (x, y)) =
      (\<Sum>z\<in>s i ` (space N \<times> space M). measure M {y \<in> space M. s i (x, y) = z} *\<^sub>R z)"
      using s[THEN simple_functionD(1)]
      unfolding simple_bochner_integral_def
      by (intro sum.mono_neutral_cong_left)
         (auto simp: eq_commute space_pair_measure image_iff cong: conj_cong) }
  note eq = this

  show ?thesis
  proof (rule borel_measurable_LIMSEQ_metric)
    fix i show "f' i \<in> borel_measurable N"
      unfolding f'_def by (simp_all add: eq cong: measurable_cong if_cong)
  next
    fix x assume x: "x \<in> space N"
    { assume int_f: "integrable M (f x)"
      have int_2f: "integrable M (\<lambda>y. 2 * norm (f x y))"
        by (intro integrable_norm integrable_mult_right int_f)
      have "(\<lambda>i. integral\<^sup>L M (\<lambda>y. s i (x, y))) \<longlonglongrightarrow> integral\<^sup>L M (f x)"
      proof (rule integral_dominated_convergence)
        from int_f show "f x \<in> borel_measurable M" by auto
        show "\<And>i. (\<lambda>y. s i (x, y)) \<in> borel_measurable M"
          using x by simp
        show "AE xa in M. (\<lambda>i. s i (x, xa)) \<longlonglongrightarrow> f x xa"
          using x * by auto
        show "\<And>i. AE xa in M. norm (s i (x, xa)) \<le> 2 * norm (f x xa)"
          using x * by auto
      qed fact
      moreover
      { fix i
        have "Bochner_Integration.simple_bochner_integrable M (\<lambda>y. s i (x, y))"
        proof (rule simple_bochner_integrableI_bounded)
          have "(\<lambda>y. s i (x, y)) ` space M \<subseteq> s i ` (space N \<times> space M)"
            using x by auto
          then show "simple_function M (\<lambda>y. s i (x, y))"
            using simple_functionD(1)[OF s(1), of i] x
            by (intro simple_function_borel_measurable)
               (auto simp: space_pair_measure dest: finite_subset)
          have "(\<integral>\<^sup>+ y. ennreal (norm (s i (x, y))) \<partial>M) \<le> (\<integral>\<^sup>+ y. 2 * norm (f x y) \<partial>M)"
            using x * by (intro nn_integral_mono) auto
          also have "(\<integral>\<^sup>+ y. 2 * norm (f x y) \<partial>M) < \<infinity>"
            using int_2f unfolding integrable_iff_bounded by simp
          finally show "(\<integral>\<^sup>+ xa. ennreal (norm (s i (x, xa))) \<partial>M) < \<infinity>" .
        qed
        then have "integral\<^sup>L M (\<lambda>y. s i (x, y)) = Bochner_Integration.simple_bochner_integral M (\<lambda>y. s i (x, y))"
          by (rule simple_bochner_integrable_eq_integral[symmetric]) }
      ultimately have "(\<lambda>i. Bochner_Integration.simple_bochner_integral M (\<lambda>y. s i (x, y))) \<longlonglongrightarrow> integral\<^sup>L M (f x)"
        by simp }
    then
    show "(\<lambda>i. f' i x) \<longlonglongrightarrow> integral\<^sup>L M (f x)"
      unfolding f'_def
      by (cases "integrable M (f x)") (simp_all add: not_integrable_integral_eq)
  qed
qed

lemma integrable_product_swap_s_finite:
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes M1:"s_finite_measure M1" and M2:"s_finite_measure M2"
      and "integrable (M1 \<Otimes>\<^sub>M M2) f"
  shows "integrable (M2 \<Otimes>\<^sub>M M1) (\<lambda>(x,y). f (y,x))"
proof -
  have *: "(\<lambda>(x,y). f (y,x)) = (\<lambda>x. f (case x of (x,y)\<Rightarrow>(y,x)))" by (auto simp: fun_eq_iff)
  show ?thesis unfolding *
    by (rule integrable_distr[OF measurable_pair_swap'])
       (simp add: distr_pair_swap_s_finite[OF M1 M2,symmetric] assms)
qed

lemma integrable_product_swap_iff_s_finite:
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes M1:"s_finite_measure M1" and M2:"s_finite_measure M2"
  shows "integrable (M2 \<Otimes>\<^sub>M M1) (\<lambda>(x,y). f (y,x)) \<longleftrightarrow> integrable (M1 \<Otimes>\<^sub>M M2) f"
proof -
  from integrable_product_swap_s_finite[OF M2 M1,of "\<lambda>(x,y). f (y,x)"] integrable_product_swap_s_finite[OF M1 M2,of f]
  show ?thesis by auto
qed

lemma integral_product_swap_s_finite:
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes M1:"s_finite_measure M1" and M2:"s_finite_measure M2"
      and f: "f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M2)"
  shows "(\<integral>(x,y). f (y,x) \<partial>(M2 \<Otimes>\<^sub>M M1)) = integral\<^sup>L (M1 \<Otimes>\<^sub>M M2) f"
proof -
  have *: "(\<lambda>(x,y). f (y,x)) = (\<lambda>x. f (case x of (x,y)\<Rightarrow>(y,x)))" by (auto simp: fun_eq_iff)
  show ?thesis unfolding *
    by (simp add: integral_distr[symmetric, OF measurable_pair_swap' f] distr_pair_swap_s_finite[OF M1 M2,symmetric])
qed

theorem(in s_finite_measure) Fubini_integrable':
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes f[measurable]: "f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M)"
    and integ1: "integrable M1 (\<lambda>x. \<integral> y. norm (f (x, y)) \<partial>M)"
    and integ2: "AE x in M1. integrable M (\<lambda>y. f (x, y))"
  shows "integrable (M1 \<Otimes>\<^sub>M M) f"
proof (rule integrableI_bounded)
  have "(\<integral>\<^sup>+ p. norm (f p) \<partial>(M1 \<Otimes>\<^sub>M M)) = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. norm (f (x, y)) \<partial>M) \<partial>M1)"
    by (simp add: nn_integral_fst'[symmetric])
  also have "\<dots> = (\<integral>\<^sup>+ x. \<bar>\<integral>y. norm (f (x, y)) \<partial>M\<bar> \<partial>M1)"
  proof(rule nn_integral_cong_AE)
    show "AE x in M1. (\<integral>\<^sup>+ y. ennreal (norm (f (x, y))) \<partial>M) = ennreal \<bar>LINT y|M. norm (f (x, y))\<bar>"
      using integ2
    proof eventually_elim
      fix x assume "integrable M (\<lambda>y. f (x, y))"
      then have f: "integrable M (\<lambda>y. norm (f (x, y)))"
        by simp
      then have "(\<integral>\<^sup>+y. ennreal (norm (f (x, y))) \<partial>M) = ennreal (LINT y|M. norm (f (x, y)))"
        by (rule nn_integral_eq_integral) simp
      also have "\<dots> = ennreal \<bar>LINT y|M. norm (f (x, y))\<bar>"
        using f by simp
      finally show "(\<integral>\<^sup>+y. ennreal (norm (f (x, y))) \<partial>M) = ennreal \<bar>LINT y|M. norm (f (x, y))\<bar>" .
    qed
  qed
  also have "\<dots> < \<infinity>"
    using integ1 by (simp add: integrable_iff_bounded integral_nonneg_AE)
  finally show "(\<integral>\<^sup>+ p. norm (f p) \<partial>(M1 \<Otimes>\<^sub>M M)) < \<infinity>" .
qed fact

lemma(in s_finite_measure) emeasure_pair_measure_finite':
  assumes A: "A \<in> sets (M1 \<Otimes>\<^sub>M M)" and finite: "emeasure (M1 \<Otimes>\<^sub>M M) A < \<infinity>"
  shows "AE x in M1. emeasure M {y\<in>space M. (x, y) \<in> A} < \<infinity>"
proof -
  from emeasure_pair_measure_alt'[OF A] finite
  have "(\<integral>\<^sup>+ x. emeasure M (Pair x -` A) \<partial>M1) \<noteq> \<infinity>"
    by simp
  then have "AE x in M1. emeasure M (Pair x -` A) \<noteq> \<infinity>"
    by (rule nn_integral_PInf_AE[rotated]) (intro measurable_emeasure_Pair' A)
  moreover have "\<And>x. x \<in> space M1 \<Longrightarrow> Pair x -` A = {y\<in>space M. (x, y) \<in> A}"
    using sets.sets_into_space[OF A] by (auto simp: space_pair_measure)
  ultimately show ?thesis by (auto simp: less_top)
qed

lemma(in s_finite_measure) AE_integrable_fst''':
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes f[measurable]: "integrable (M1 \<Otimes>\<^sub>M M) f"
  shows "AE x in M1. integrable M (\<lambda>y. f (x, y))"
proof -
  have "(\<integral>\<^sup>+x. (\<integral>\<^sup>+y. norm (f (x, y)) \<partial>M) \<partial>M1) = (\<integral>\<^sup>+x. norm (f x) \<partial>(M1 \<Otimes>\<^sub>M M))"
    by (rule nn_integral_fst') simp
  also have "(\<integral>\<^sup>+x. norm (f x) \<partial>(M1 \<Otimes>\<^sub>M M)) \<noteq> \<infinity>"
    using f unfolding integrable_iff_bounded by simp
  finally have "AE x in M1. (\<integral>\<^sup>+y. norm (f (x, y)) \<partial>M) \<noteq> \<infinity>"
    by (intro nn_integral_PInf_AE borel_measurable_nn_integral')
       (auto simp: measurable_split_conv)
  with AE_space show ?thesis
    by eventually_elim
       (auto simp: integrable_iff_bounded measurable_compose[OF _ borel_measurable_integrable[OF f]] less_top)
qed

lemma(in s_finite_measure) integrable_fst_norm':
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes f[measurable]: "integrable (M1 \<Otimes>\<^sub>M M) f"
  shows "integrable M1 (\<lambda>x. \<integral>y. norm (f (x, y)) \<partial>M)"
  unfolding integrable_iff_bounded
proof
  show "(\<lambda>x. \<integral> y. norm (f (x, y)) \<partial>M) \<in> borel_measurable M1"
    by (rule borel_measurable_lebesgue_integral') simp
  have "(\<integral>\<^sup>+ x. ennreal (norm (\<integral>y. norm (f (x, y)) \<partial>M)) \<partial>M1) = (\<integral>\<^sup>+x. (\<integral>\<^sup>+y. norm (f (x, y)) \<partial>M) \<partial>M1)"
    using AE_integrable_fst'''[OF f] by (auto intro!: nn_integral_cong_AE simp: nn_integral_eq_integral)
  also have "(\<integral>\<^sup>+x. (\<integral>\<^sup>+y. norm (f (x, y)) \<partial>M) \<partial>M1) = (\<integral>\<^sup>+x. norm (f x) \<partial>(M1 \<Otimes>\<^sub>M M))"
    by (rule nn_integral_fst') simp
  also have "(\<integral>\<^sup>+x. norm (f x) \<partial>(M1 \<Otimes>\<^sub>M M)) < \<infinity>"
    using f unfolding integrable_iff_bounded by simp
  finally show "(\<integral>\<^sup>+ x. ennreal (norm (\<integral>y. norm (f (x, y)) \<partial>M)) \<partial>M1) < \<infinity>" .
qed

lemma(in s_finite_measure) integrable_fst''':
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes f[measurable]: "integrable (M1 \<Otimes>\<^sub>M M) f"
  shows "integrable M1 (\<lambda>x. \<integral>y. f (x, y) \<partial>M)"
  by(auto intro!: Bochner_Integration.integrable_bound[OF integrable_fst_norm'[OF f]])

proposition(in s_finite_measure) integral_fst''':
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes f: "integrable (M1 \<Otimes>\<^sub>M M) f"
  shows "(\<integral>x. (\<integral>y. f (x, y) \<partial>M) \<partial>M1) = integral\<^sup>L (M1 \<Otimes>\<^sub>M M) f"
using f proof induct
  case (base A c)
  have A[measurable]: "A \<in> sets (M1 \<Otimes>\<^sub>M M)" by fact

  have eq: "\<And>x y. x \<in> space M1 \<Longrightarrow> indicator A (x, y) = indicator {y\<in>space M. (x, y) \<in> A} y"
    using sets.sets_into_space[OF A] by (auto split: split_indicator simp: space_pair_measure)

  have int_A: "integrable (M1 \<Otimes>\<^sub>M M) (indicator A :: _ \<Rightarrow> real)"
    using base by (rule integrable_real_indicator)
  have "(\<integral> x. \<integral> y. indicator A (x, y) *\<^sub>R c \<partial>M \<partial>M1) = (\<integral>x. measure M {y\<in>space M. (x, y) \<in> A} *\<^sub>R c \<partial>M1)"
  proof (intro integral_cong_AE)
    from AE_integrable_fst'''[OF int_A] AE_space
    show "AE x in M1. (\<integral>y. indicator A (x, y) *\<^sub>R c \<partial>M) = measure M {y\<in>space M. (x, y) \<in> A} *\<^sub>R c"
      by eventually_elim (simp add: eq integrable_indicator_iff)
  qed simp_all
  also have "\<dots> = measure (M1 \<Otimes>\<^sub>M M) A *\<^sub>R c"
  proof (subst integral_scaleR_left)
    have "(\<integral>\<^sup>+x. ennreal (measure M {y \<in> space M. (x, y) \<in> A}) \<partial>M1) =
      (\<integral>\<^sup>+x. emeasure M {y \<in> space M. (x, y) \<in> A} \<partial>M1)"
      using emeasure_pair_measure_finite'[OF base]
      by (intro nn_integral_cong_AE, eventually_elim) (simp add: emeasure_eq_ennreal_measure)
    also have "\<dots> = emeasure (M1 \<Otimes>\<^sub>M M) A"
      using sets.sets_into_space[OF A]
      by (subst emeasure_pair_measure_alt')
         (auto intro!: nn_integral_cong arg_cong[where f="emeasure M"] simp: space_pair_measure)
    finally have *: "(\<integral>\<^sup>+x. ennreal (measure M {y \<in> space M. (x, y) \<in> A}) \<partial>M1) = emeasure (M1 \<Otimes>\<^sub>M M) A" .

    from base * show "integrable M1 (\<lambda>x. measure M {y \<in> space M. (x, y) \<in> A})"
      by (simp add: integrable_iff_bounded)
    then have "(\<integral>x. measure M {y \<in> space M. (x, y) \<in> A} \<partial>M1) =
      (\<integral>\<^sup>+x. ennreal (measure M {y \<in> space M. (x, y) \<in> A}) \<partial>M1)"
      by (rule nn_integral_eq_integral[symmetric]) simp
    also note *
    finally show "(\<integral>x. measure M {y \<in> space M. (x, y) \<in> A} \<partial>M1) *\<^sub>R c = measure (M1 \<Otimes>\<^sub>M M) A *\<^sub>R c"
      using base by (simp add: emeasure_eq_ennreal_measure)
  qed
  also have "\<dots> = (\<integral> a. indicator A a *\<^sub>R c \<partial>(M1 \<Otimes>\<^sub>M M))"
    using base by simp
  finally show ?case .
next
  case (add f g)
  then have [measurable]: "f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M)" "g \<in> borel_measurable (M1 \<Otimes>\<^sub>M M)"
    by auto
  have "(\<integral> x. \<integral> y. f (x, y) + g (x, y) \<partial>M \<partial>M1) =
    (\<integral> x. (\<integral> y. f (x, y) \<partial>M) + (\<integral> y. g (x, y) \<partial>M) \<partial>M1)"
    apply (rule integral_cong_AE)
    apply simp_all
    using AE_integrable_fst'''[OF add(1)] AE_integrable_fst'''[OF add(3)]
    apply eventually_elim
    apply simp
    done
  also have "\<dots> = (\<integral> x. f x \<partial>(M1 \<Otimes>\<^sub>M M)) + (\<integral> x. g x \<partial>(M1 \<Otimes>\<^sub>M M))"
    using integrable_fst'''[OF add(1)] integrable_fst'''[OF add(3)] add(2,4) by simp
  finally show ?case
    using add by simp
next
  case (lim f s)
  then have [measurable]: "f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M)" "\<And>i. s i \<in> borel_measurable (M1 \<Otimes>\<^sub>M M)"
    by auto

  show ?case
  proof (rule LIMSEQ_unique)
    show "(\<lambda>i. integral\<^sup>L (M1 \<Otimes>\<^sub>M M) (s i)) \<longlonglongrightarrow> integral\<^sup>L (M1 \<Otimes>\<^sub>M M) f"
    proof (rule integral_dominated_convergence)
      show "integrable (M1 \<Otimes>\<^sub>M M) (\<lambda>x. 2 * norm (f x))"
        using lim(5) by auto
    qed (insert lim, auto)
    have "(\<lambda>i. \<integral> x. \<integral> y. s i (x, y) \<partial>M \<partial>M1) \<longlonglongrightarrow> \<integral> x. \<integral> y. f (x, y) \<partial>M \<partial>M1"
    proof (rule integral_dominated_convergence)
      have "AE x in M1. \<forall>i. integrable M (\<lambda>y. s i (x, y))"
        unfolding AE_all_countable using AE_integrable_fst'''[OF lim(1)] ..
      with AE_space AE_integrable_fst'''[OF lim(5)]
      show "AE x in M1. (\<lambda>i. \<integral> y. s i (x, y) \<partial>M) \<longlonglongrightarrow> \<integral> y. f (x, y) \<partial>M"
      proof eventually_elim
        fix x assume x: "x \<in> space M1" and
          s: "\<forall>i. integrable M (\<lambda>y. s i (x, y))" and f: "integrable M (\<lambda>y. f (x, y))"
        show "(\<lambda>i. \<integral> y. s i (x, y) \<partial>M) \<longlonglongrightarrow> \<integral> y. f (x, y) \<partial>M"
        proof (rule integral_dominated_convergence)
          show "integrable M (\<lambda>y. 2 * norm (f (x, y)))"
             using f by auto
          show "AE xa in M. (\<lambda>i. s i (x, xa)) \<longlonglongrightarrow> f (x, xa)"
            using x lim(3) by (auto simp: space_pair_measure)
          show "\<And>i. AE xa in M. norm (s i (x, xa)) \<le> 2 * norm (f (x, xa))"
            using x lim(4) by (auto simp: space_pair_measure)
        qed (insert x, measurable)
      qed
      show "integrable M1 (\<lambda>x. (\<integral> y. 2 * norm (f (x, y)) \<partial>M))"
        by (intro integrable_mult_right integrable_norm integrable_fst''' lim)
      fix i show "AE x in M1. norm (\<integral> y. s i (x, y) \<partial>M) \<le> (\<integral> y. 2 * norm (f (x, y)) \<partial>M)"
        using AE_space AE_integrable_fst'''[OF lim(1), of i] AE_integrable_fst'''[OF lim(5)]
      proof eventually_elim
        fix x assume x: "x \<in> space M1"
          and s: "integrable M (\<lambda>y. s i (x, y))" and f: "integrable M (\<lambda>y. f (x, y))"
        from s have "norm (\<integral> y. s i (x, y) \<partial>M) \<le> (\<integral>\<^sup>+y. norm (s i (x, y)) \<partial>M)"
          by (rule integral_norm_bound_ennreal)
        also have "\<dots> \<le> (\<integral>\<^sup>+y. 2 * norm (f (x, y)) \<partial>M)"
          using x lim by (auto intro!: nn_integral_mono simp: space_pair_measure)
        also have "\<dots> = (\<integral>y. 2 * norm (f (x, y)) \<partial>M)"
          using f by (intro nn_integral_eq_integral) auto
        finally show "norm (\<integral> y. s i (x, y) \<partial>M) \<le> (\<integral> y. 2 * norm (f (x, y)) \<partial>M)"
          by simp
      qed
    qed simp_all
    then show "(\<lambda>i. integral\<^sup>L (M1 \<Otimes>\<^sub>M M) (s i)) \<longlonglongrightarrow> \<integral> x. \<integral> y. f (x, y) \<partial>M \<partial>M1"
      using lim by simp
  qed
qed

lemma (in s_finite_measure)
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes f: "integrable (M1 \<Otimes>\<^sub>M M) (case_prod f)"
  shows AE_integrable_fst'': "AE x in M1. integrable M (\<lambda>y. f x y)"
    and integrable_fst'': "integrable M1 (\<lambda>x. \<integral>y. f x y \<partial>M)"
    and integrable_fst_norm: "integrable M1 (\<lambda>x. \<integral>y. norm (f x y) \<partial>M)"
    and integral_fst'': "(\<integral>x. (\<integral>y. f x y \<partial>M) \<partial>M1) = integral\<^sup>L (M1 \<Otimes>\<^sub>M M) (\<lambda>(x, y). f x y)"
  using AE_integrable_fst'''[OF f] integrable_fst'''[OF f] integral_fst'''[OF f] integrable_fst_norm'[OF f] by auto

lemma
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes M1:"s_finite_measure M1" and M2:"s_finite_measure M2"
      and f[measurable]: "integrable (M1 \<Otimes>\<^sub>M M2) (case_prod f)"
  shows AE_integrable_snd_s_finite: "AE y in M2. integrable M1 (\<lambda>x. f x y)" (is "?AE")
    and integrable_snd_s_finite: "integrable M2 (\<lambda>y. \<integral>x. f x y \<partial>M1)" (is "?INT")
    and integrable_snd_norm_s_finite: "integrable M2 (\<lambda>y. \<integral>x. norm (f x y) \<partial>M1)" (is "?INT2")
    and integral_snd_s_finite: "(\<integral>y. (\<integral>x. f x y \<partial>M1) \<partial>M2) = integral\<^sup>L (M1 \<Otimes>\<^sub>M M2) (case_prod f)" (is "?EQ")
proof -
  interpret Q: s_finite_measure M1 by fact
  have Q_int: "integrable (M2 \<Otimes>\<^sub>M M1) (\<lambda>(x, y). f y x)"
    using f unfolding integrable_product_swap_iff_s_finite[OF M1 M2,symmetric] by simp
  show ?AE  using Q.AE_integrable_fst'''[OF Q_int] by simp
  show ?INT using Q.integrable_fst'''[OF Q_int] by simp
  show ?INT2 using Q.integrable_fst_norm[OF Q_int] by simp
  show ?EQ using Q.integral_fst'''[OF Q_int]
    using integral_product_swap_s_finite[OF M1 M2,of "case_prod f"] by simp
qed

proposition Fubini_integral':
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes M1:"s_finite_measure M1" and M2:"s_finite_measure M2"
      and f: "integrable (M1 \<Otimes>\<^sub>M M2) (case_prod f)"
  shows "(\<integral>y. (\<integral>x. f x y \<partial>M1) \<partial>M2) = (\<integral>x. (\<integral>y. f x y \<partial>M2) \<partial>M1)"
  unfolding integral_snd_s_finite[OF assms] s_finite_measure.integral_fst''[OF assms(2,3)] ..

locale product_s_finite =
  fixes M :: "'i \<Rightarrow> 'a measure"
  assumes s_finite_measures: "\<And>i. s_finite_measure (M i)"

sublocale product_s_finite \<subseteq> M?: s_finite_measure "M i" for i
  by (rule s_finite_measures)

locale finite_product_s_finite = product_s_finite M for M :: "'i \<Rightarrow> 'a measure" +
  fixes I :: "'i set"
  assumes finite_index: "finite I"

lemma (in product_s_finite) emeasure_PiM:
  "finite I \<Longrightarrow> (\<And>i. i\<in>I \<Longrightarrow> A i \<in> sets (M i)) \<Longrightarrow> emeasure (PiM I M) (Pi\<^sub>E I A) = (\<Prod>i\<in>I. emeasure (M i) (A i))"
proof (induct I arbitrary: A rule: finite_induct)
  case (insert i I)
  interpret finite_product_s_finite M I by standard fact
  have "finite (insert i I)" using \<open>finite I\<close> by auto
  interpret I': finite_product_s_finite M "insert i I" by standard fact
  let ?h = "(\<lambda>(f, y). f(i := y))"

  let ?P = "distr (Pi\<^sub>M I M \<Otimes>\<^sub>M M i) (Pi\<^sub>M (insert i I) M) ?h"
  let ?\<mu> = "emeasure ?P"
  let ?I = "{j \<in> insert i I. emeasure (M j) (space (M j)) \<noteq> 1}"
  let ?f = "\<lambda>J E j. if j \<in> J then emeasure (M j) (E j) else emeasure (M j) (space (M j))"

  have "emeasure (Pi\<^sub>M (insert i I) M) (prod_emb (insert i I) M (insert i I) (Pi\<^sub>E (insert i I) A)) =
    (\<Prod>i\<in>insert i I. emeasure (M i) (A i))"
  proof (subst emeasure_extend_measure_Pair[OF PiM_def])
    fix J E assume "(J \<noteq> {} \<or> insert i I = {}) \<and> finite J \<and> J \<subseteq> insert i I \<and> E \<in> (\<Pi> j\<in>J. sets (M j))"
    then have J: "J \<noteq> {}" "finite J" "J \<subseteq> insert i I" and E: "\<forall>j\<in>J. E j \<in> sets (M j)" by auto
    let ?p = "prod_emb (insert i I) M J (Pi\<^sub>E J E)"
    let ?p' = "prod_emb I M (J - {i}) (\<Pi>\<^sub>E j\<in>J-{i}. E j)"
    have "?\<mu> ?p =
      emeasure (Pi\<^sub>M I M \<Otimes>\<^sub>M (M i)) (?h -` ?p \<inter> space (Pi\<^sub>M I M \<Otimes>\<^sub>M M i))"
      by (intro emeasure_distr measurable_add_dim sets_PiM_I) fact+
    also have "?h -` ?p \<inter> space (Pi\<^sub>M I M \<Otimes>\<^sub>M M i) = ?p' \<times> (if i \<in> J then E i else space (M i))"
      using J E[rule_format, THEN sets.sets_into_space]
      by (force simp: space_pair_measure space_PiM prod_emb_iff PiE_def Pi_iff split: if_split_asm)
    also have "emeasure (Pi\<^sub>M I M \<Otimes>\<^sub>M (M i)) (?p' \<times> (if i \<in> J then E i else space (M i))) =
      emeasure (Pi\<^sub>M I M) ?p' * emeasure (M i) (if i \<in> J then (E i) else space (M i))"
      using J E by (intro M.emeasure_pair_measure_Times' sets_PiM_I) auto
    also have "?p' = (\<Pi>\<^sub>E j\<in>I. if j \<in> J-{i} then E j else space (M j))"
      using J E[rule_format, THEN sets.sets_into_space]
      by (auto simp: prod_emb_iff PiE_def Pi_iff split: if_split_asm) blast+
    also have "emeasure (Pi\<^sub>M I M) (\<Pi>\<^sub>E j\<in>I. if j \<in> J-{i} then E j else space (M j)) =
      (\<Prod> j\<in>I. if j \<in> J-{i} then emeasure (M j) (E j) else emeasure (M j) (space (M j)))"
      using E by (subst insert) (auto intro!: prod.cong)
    also have "(\<Prod>j\<in>I. if j \<in> J - {i} then emeasure (M j) (E j) else emeasure (M j) (space (M j))) *
       emeasure (M i) (if i \<in> J then E i else space (M i)) = (\<Prod>j\<in>insert i I. ?f J E j)"
      using insert by (auto simp: mult.commute intro!: arg_cong2[where f="(*)"] prod.cong)
    also have "\<dots> = (\<Prod>j\<in>J \<union> ?I. ?f J E j)"
      using insert(1,2) J E by (intro prod.mono_neutral_right) auto
    finally show "?\<mu> ?p = \<dots>" .

    show "prod_emb (insert i I) M J (Pi\<^sub>E J E) \<in> Pow (\<Pi>\<^sub>E i\<in>insert i I. space (M i))"
      using J E[rule_format, THEN sets.sets_into_space] by (auto simp: prod_emb_iff PiE_def)
  next
    show "positive (sets (Pi\<^sub>M (insert i I) M)) ?\<mu>" "countably_additive (sets (Pi\<^sub>M (insert i I) M)) ?\<mu>"
      using emeasure_positive[of ?P] emeasure_countably_additive[of ?P] by simp_all
  next
    show "(insert i I \<noteq> {} \<or> insert i I = {}) \<and> finite (insert i I) \<and>
      insert i I \<subseteq> insert i I \<and> A \<in> (\<Pi> j\<in>insert i I. sets (M j))"
      using insert by auto
  qed (auto intro!: prod.cong)
  with insert show ?case
    by (subst (asm) prod_emb_PiE_same_index) (auto intro!: sets.sets_into_space)
qed simp


lemma (in finite_product_s_finite) measure_times:
  "(\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (M i)) \<Longrightarrow> emeasure (Pi\<^sub>M I M) (Pi\<^sub>E I A) = (\<Prod>i\<in>I. emeasure (M i) (A i))"
  using emeasure_PiM[OF finite_index] by auto

lemma (in product_s_finite) nn_integral_empty:
  "0 \<le> f (\<lambda>k. undefined) \<Longrightarrow> integral\<^sup>N (Pi\<^sub>M {} M) f = f (\<lambda>k. undefined)"
  by (simp add: PiM_empty nn_integral_count_space_finite)

text \<open> Every s-finite measure is represented as the push-forward measure of a $\sigma$-finite measure.\<close>
definition Mi_to_NM :: "(nat \<Rightarrow> 'a measure) \<Rightarrow> 'a measure \<Rightarrow> (nat \<times> 'a) measure" where
"Mi_to_NM Mi M \<equiv> measure_of (space (count_space UNIV \<Otimes>\<^sub>M M)) (sets (count_space UNIV \<Otimes>\<^sub>M M)) (\<lambda>A. \<Sum>i. distr (Mi i) (count_space UNIV \<Otimes>\<^sub>M M) (\<lambda>x. (i,x)) A)"

lemma
  shows sets_Mi_to_NM[measurable_cong,simp]: "sets (Mi_to_NM Mi M) = sets (count_space UNIV \<Otimes>\<^sub>M M)"
    and space_Mi_to_NM[simp]: "space (Mi_to_NM Mi M) = space (count_space UNIV \<Otimes>\<^sub>M M)"
  by(simp_all add: Mi_to_NM_def)

context
  fixes M :: "'a measure" and Mi :: "nat \<Rightarrow> 'a measure"
  assumes sets_Mi[measurable_cong,simp]: "\<And>i. sets (Mi i) = sets M"
      and emeasure_Mi: "\<And>A. A \<in> sets M \<Longrightarrow> M A = (\<Sum>i. Mi i A)"
begin

lemma emeasure_Mi_to_NM:
  assumes [measurable]: "A \<in> sets (count_space UNIV \<Otimes>\<^sub>M M)"
  shows "emeasure (Mi_to_NM Mi M) A = (\<Sum>i. distr (Mi i) (count_space UNIV \<Otimes>\<^sub>M M) (\<lambda>x. (i,x)) A)"
proof(rule emeasure_measure_of[where \<Omega>="space (count_space UNIV \<Otimes>\<^sub>M M)" and A="sets (count_space UNIV \<Otimes>\<^sub>M M)"])
  show "countably_additive (sets (Mi_to_NM Mi M)) (\<lambda>A. \<Sum>i. emeasure (distr (Mi i) (count_space UNIV \<Otimes>\<^sub>M M) (Pair i)) A)"
    unfolding countably_additive_def
  proof safe
    fix A :: "nat \<Rightarrow> (nat \<times> _) set"
    assume "range A \<subseteq> sets (Mi_to_NM Mi M)" and dA:"disjoint_family A"
    hence [measurable]: "\<And>i. A i \<in> sets (count_space UNIV \<Otimes>\<^sub>M M)"
      by auto
    show "(\<Sum>j i. emeasure (distr (Mi i) (count_space UNIV \<Otimes>\<^sub>M M) (Pair i)) (A j)) = (\<Sum>i. emeasure (distr (Mi i) (count_space UNIV \<Otimes>\<^sub>M M) (Pair i)) (\<Union> (range A)))" (is "?lhs = ?rhs")
    proof -
      have "?lhs = (\<Sum>i j. emeasure (distr (Mi i) (count_space UNIV \<Otimes>\<^sub>M M) (Pair i)) (A j))"
        by(auto simp: nn_integral_count_space_nat[symmetric] pair_sigma_finite_def sigma_finite_measure_count_space intro!: pair_sigma_finite.Fubini')
      also have "... = ?rhs"
      proof(rule suminf_cong)
        fix n
        have [simp]:"Pair n -` \<Union> (range A) = (\<Union> (range (\<lambda>j. Pair n -` A j)))"
          by auto
        show " (\<Sum>j. emeasure (distr (Mi n) (count_space UNIV \<Otimes>\<^sub>M M) (Pair n)) (A j)) = emeasure (distr (Mi n) (count_space UNIV \<Otimes>\<^sub>M M) (Pair n)) (\<Union> (range A))"
          using dA by(fastforce intro!: suminf_emeasure simp: disjoint_family_on_def emeasure_distr)
      qed
      finally show ?thesis .
    qed
  qed
qed(auto simp: positive_def sets.space_closed Mi_to_NM_def)

lemma sigma_finite_Mi_to_NM_measure:
  assumes "\<And>i. finite_measure (Mi i)"
  shows "sigma_finite_measure (Mi_to_NM Mi M)"
proof -
  {
    fix n
    assume "emeasure (Mi_to_NM Mi M) ({n} \<times> space M) = \<top>"
    moreover have "emeasure (Mi_to_NM Mi M) ({n} \<times> space M) = emeasure (Mi n) (space M)"
      by(simp add:  emeasure_Mi_to_NM emeasure_distr suminf_offset[of _ "Suc n"])
    ultimately have False
      using finite_measure.finite_emeasure_space[OF assms[of n]] by(auto simp: sets_eq_imp_space_eq[OF sets_Mi])
  }
  thus ?thesis
    by(auto intro!: exI[where x="\<Union>i. {{i} \<times> space M}"] simp: space_pair_measure sigma_finite_measure_def)
qed


lemma distr_Mi_to_NM_M: "distr (Mi_to_NM Mi M) M snd = M"
proof -
  have [simp]:"Pair i -` snd -` A \<inter> Pair i -` space (count_space UNIV \<Otimes>\<^sub>M M) = A" if "A \<in> sets M" for A and i :: nat
    using sets.sets_into_space[OF that] by(auto simp: space_pair_measure)
  show ?thesis
    by(auto intro!: measure_eqI simp: emeasure_distr emeasure_Mi_to_NM emeasure_Mi)
qed

end

context
  fixes \<mu> :: "'a measure"
  assumes standard_borel_ne: "standard_borel_ne \<mu>"
      and s_finite: "s_finite_measure \<mu>"
begin

interpretation \<mu> : s_finite_measure \<mu> by fact

interpretation n_\<mu>: standard_borel_ne "count_space (UNIV :: nat set) \<Otimes>\<^sub>M \<mu>"
  by (simp add: pair_standard_borel_ne standard_borel_ne)

lemma exists_push_forward:
 "\<exists>(\<mu>' :: real measure) f. f \<in> borel \<rightarrow>\<^sub>M \<mu> \<and> sets \<mu>' = sets borel \<and> sigma_finite_measure \<mu>'
                           \<and> distr \<mu>' \<mu> f = \<mu>"
proof -
  obtain \<mu>i where \<mu>i: "\<And>i. sets (\<mu>i i) = sets \<mu>" "\<And>i. finite_measure (\<mu>i i)" "\<And>A. \<mu> A = (\<Sum>i. \<mu>i i A)"
    by(metis \<mu>.finite_measures')
  show ?thesis
  proof(safe intro!: exI[where x="distr (Mi_to_NM \<mu>i \<mu>) borel n_\<mu>.to_real"] exI[where x="snd \<circ> n_\<mu>.from_real"])
    have [simp]:"distr (distr (Mi_to_NM \<mu>i \<mu>) borel n_\<mu>.to_real) (count_space UNIV \<Otimes>\<^sub>M \<mu>) n_\<mu>.from_real = Mi_to_NM \<mu>i \<mu>"
      by(auto simp: distr_distr comp_def intro!:distr_id')
    show "sigma_finite_measure (distr (Mi_to_NM \<mu>i \<mu>) borel n_\<mu>.to_real)"
      by(rule sigma_finite_measure_distr[where N="count_space UNIV \<Otimes>\<^sub>M \<mu>" and f=n_\<mu>.from_real]) (auto intro!: sigma_finite_Mi_to_NM_measure \<mu>i)
  next
    have [simp]: "distr (Mi_to_NM \<mu>i \<mu>) \<mu> (snd \<circ> n_\<mu>.from_real \<circ> n_\<mu>.to_real) =  distr (Mi_to_NM \<mu>i \<mu>) \<mu> snd"
      by(auto intro!: distr_cong[OF refl])
    show "distr (distr (Mi_to_NM \<mu>i \<mu>) borel n_\<mu>.to_real) \<mu> (snd \<circ> n_\<mu>.from_real) = \<mu>"
      by(auto simp: distr_distr distr_Mi_to_NM_M[OF \<mu>i(1,3)])
  qed auto
qed

abbreviation "\<mu>'_and_f \<equiv> (SOME (\<mu>'::real measure,f). f \<in> borel \<rightarrow>\<^sub>M \<mu> \<and> sets \<mu>' = sets borel \<and> sigma_finite_measure \<mu>' \<and> distr \<mu>' \<mu> f = \<mu>)"

definition "sigma_pair_\<mu> \<equiv> fst \<mu>'_and_f"
definition "sigma_pair_f \<equiv> snd \<mu>'_and_f"

lemma
  shows sigma_pair_f_measurable : "sigma_pair_f \<in> borel \<rightarrow>\<^sub>M \<mu>" (is ?g1)
    and sets_sigma_pair_\<mu>: "sets sigma_pair_\<mu> = sets borel" (is ?g2)
    and sigma_finite_sigma_pair_\<mu>: "sigma_finite_measure sigma_pair_\<mu>" (is ?g3)
    and distr_sigma_pair: "distr sigma_pair_\<mu> \<mu> sigma_pair_f = \<mu>" (is ?g4)
proof -
  have "case \<mu>'_and_f of (\<mu>',f) \<Rightarrow> f \<in> borel \<rightarrow>\<^sub>M \<mu> \<and> sets \<mu>' = sets borel \<and> sigma_finite_measure \<mu>' \<and> distr \<mu>' \<mu> f = \<mu>"
    by(rule someI_ex) (use exists_push_forward in auto)
  then show ?g1 ?g2 ?g3 ?g4
    by(auto simp: sigma_pair_\<mu>_def sigma_pair_f_def split_beta)
qed

end

definition s_finite_measure_algebra :: "'a measure \<Rightarrow> 'a measure measure" where
  "s_finite_measure_algebra K =
    (SUP A \<in> sets K. vimage_algebra {M. s_finite_measure M \<and> sets M = sets K} (\<lambda>M. emeasure M A) borel)"

lemma space_s_finite_measure_algebra:
 "space (s_finite_measure_algebra K) = {M. s_finite_measure M \<and> sets M = sets K}"
  by (auto simp add: s_finite_measure_algebra_def space_Sup_eq_UN)

lemma s_finite_measure_algebra_cong: "sets M = sets N \<Longrightarrow> s_finite_measure_algebra M = s_finite_measure_algebra N"
  by (simp add: s_finite_measure_algebra_def)

lemma measurable_emeasure_s_finite_measure_algebra[measurable]:
  "a \<in> sets A \<Longrightarrow> (\<lambda>M. emeasure M a) \<in> borel_measurable (s_finite_measure_algebra A)"
  by (auto intro!: measurable_Sup1 measurable_vimage_algebra1 simp: s_finite_measure_algebra_def)

lemma measurable_measure_s_finite_measure_algebra[measurable]:
  "a \<in> sets A \<Longrightarrow> (\<lambda>M. measure M a) \<in> borel_measurable (s_finite_measure_algebra A)"
  unfolding measure_def by measurable

lemma s_finite_measure_algebra_measurableD:
  assumes N: "N \<in> measurable M (s_finite_measure_algebra S)" and x: "x \<in> space M"
  shows "space (N x) = space S"
    and "sets (N x) = sets S"
    and "measurable (N x) K = measurable S K"
    and "measurable K (N x) = measurable K S"
  using measurable_space[OF N x]
  by (auto simp: space_s_finite_measure_algebra intro!: measurable_cong_sets dest: sets_eq_imp_space_eq)

context
  fixes K M N assumes K: "K \<in> measurable M (s_finite_measure_algebra N)"
begin

lemma s_finite_measure_algebra_kernel: "a \<in> space M \<Longrightarrow> s_finite_measure (K a)"
  using measurable_space[OF K] by (simp add: space_s_finite_measure_algebra)

lemma s_finite_measure_algebra_sets_kernel: "a \<in> space M \<Longrightarrow> sets (K a) = sets N"
  using measurable_space[OF K] by (simp add: space_s_finite_measure_algebra)

lemma measurable_emeasure_kernel_s_finite_measure_algebra[measurable]:
    "A \<in> sets N \<Longrightarrow> (\<lambda>a. emeasure (K a) A) \<in> borel_measurable M"
  using measurable_compose[OF K measurable_emeasure_s_finite_measure_algebra] .

end

lemma measurable_s_finite_measure_algebra:
  "(\<And>a. a \<in> space M \<Longrightarrow> s_finite_measure (K a)) \<Longrightarrow>
  (\<And>a. a \<in> space M \<Longrightarrow> sets (K a) = sets N) \<Longrightarrow>
  (\<And>A. A \<in> sets N \<Longrightarrow> (\<lambda>a. emeasure (K a) A) \<in> borel_measurable M) \<Longrightarrow>
  K \<in> measurable M (s_finite_measure_algebra N)"
  by (auto intro!: measurable_Sup2 measurable_vimage_algebra2 simp: s_finite_measure_algebra_def)

definition bind_kernel :: "'a measure \<Rightarrow> ('a \<Rightarrow> 'b measure) \<Rightarrow> 'b measure" (infixl "\<bind>\<^sub>k" 54) where
"bind_kernel M k = (if space M = {} then count_space {} else
    let Y = k (SOME x. x \<in> space M) in
     measure_of (space Y) (sets Y) (\<lambda>B. \<integral>\<^sup>+x. (k x B) \<partial>M))"

lemma bind_kernel_cong_All:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> f x = g x"
  shows "M \<bind>\<^sub>k f = M \<bind>\<^sub>k g"
proof(cases "space M = {}")
  case 1:False
  have "(SOME x. x \<in> space M) \<in> space M"
    by (rule someI_ex) (use 1 in blast)
  with assms have [simp]:"f (SOME x. x \<in> space M) = g (SOME x. x \<in> space M)" by simp
  have "(\<lambda>B. \<integral>\<^sup>+ x. emeasure (f x) B \<partial>M) = (\<lambda>B. \<integral>\<^sup>+ x. emeasure (g x) B \<partial>M)"
    by standard (auto intro!: nn_integral_cong simp: assms)
  thus ?thesis
    by(auto simp: bind_kernel_def 1)
qed(simp add: bind_kernel_def)

lemma sets_bind_kernel:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> sets (k x) = sets N" "space M \<noteq> {}"
  shows "sets (M \<bind>\<^sub>k k) = sets N"
proof -
  have "sets (k (SOME x. x \<in> space M)) = sets N"
    by(rule someI2_ex) (use assms in auto)
  with sets_eq_imp_space_eq[OF this] show ?thesis
    by(simp add: bind_kernel_def assms(2))
qed

subsection \<open> Measure Kernel \<close>
locale measure_kernel =
  fixes X :: "'a measure" and Y :: "'b measure" and \<kappa> :: "'a \<Rightarrow> 'b measure"
  assumes kernel_sets[measurable_cong]: "\<And>x. x \<in> space X \<Longrightarrow> sets (\<kappa> x) = sets Y"
      and emeasure_measurable[measurable]: "\<And>B. B \<in> sets Y \<Longrightarrow> (\<lambda>x. emeasure (\<kappa> x) B) \<in> borel_measurable X"
      and Y_not_empty: "space X \<noteq> {} \<Longrightarrow> space Y \<noteq> {}"
begin

lemma kernel_space :"\<And>x. x \<in> space X \<Longrightarrow> space (\<kappa> x) = space Y"
  by (meson kernel_sets sets_eq_imp_space_eq)

lemma measure_measurable:
  assumes "B \<in> sets Y"
  shows "(\<lambda>x. measure (\<kappa> x) B) \<in> borel_measurable X"
  using emeasure_measurable[OF assms] by (simp add: Sigma_Algebra.measure_def)

lemma set_nn_integral_measure:
  assumes [measurable_cong]: "sets \<mu> = sets X" and [measurable]: "A \<in> sets X" "B \<in> sets Y"
  defines "\<nu> \<equiv> measure_of (space Y) (sets Y) (\<lambda>B. \<integral>\<^sup>+x\<in>A. (\<kappa> x B) \<partial>\<mu>)"
  shows "\<nu> B = (\<integral>\<^sup>+x\<in>A. (\<kappa> x B) \<partial>\<mu>)"
proof -
  have nu_sets[measurable_cong]: "sets \<nu> = sets Y"
    by(simp add: \<nu>_def)
  have "positive (sets Y) (\<lambda>B. \<integral>\<^sup>+x\<in>A. (\<kappa> x B) \<partial>\<mu>)"
    by(simp add: positive_def)
  moreover have "countably_additive (sets Y) (\<lambda>B. \<integral>\<^sup>+x\<in>A. (\<kappa> x B) \<partial>\<mu>)"
    unfolding countably_additive_def
  proof safe
    fix C :: "nat \<Rightarrow> _"
    assume h:"range C \<subseteq> sets Y" "disjoint_family C"
    thus "(\<Sum>i. \<integral>\<^sup>+x\<in>A. (\<kappa> x) (C i)\<partial>\<mu>) = (\<integral>\<^sup>+x\<in>A. (\<kappa> x) (\<Union> (range C))\<partial>\<mu>)"
      by(auto intro!: nn_integral_cong simp: sets_eq_imp_space_eq[OF assms(1)] kernel_sets suminf_emeasure nn_integral_suminf[symmetric])
  qed
  ultimately show ?thesis
    using \<nu>_def assms(3) emeasure_measure_of_sigma sets.sigma_algebra_axioms by blast
qed

corollary nn_integral_measure:
  assumes "sets \<mu> = sets X" "B \<in> sets Y"
  defines "\<nu> \<equiv> measure_of (space Y) (sets Y) (\<lambda>B. \<integral>\<^sup>+x. (\<kappa> x B) \<partial>\<mu>)"
  shows "\<nu> B = (\<integral>\<^sup>+x. (\<kappa> x B) \<partial>\<mu>)"
  using set_nn_integral_measure[OF assms(1) sets.top assms(2)]
  by(simp add: \<nu>_def sets_eq_imp_space_eq[OF assms(1),symmetric])

lemma distr_measure_kernel:
  assumes [measurable]:"f \<in> Y \<rightarrow>\<^sub>M Z"
  shows "measure_kernel X Z (\<lambda>x. distr (\<kappa> x) Z f)"
  unfolding measure_kernel_def
proof safe
  fix B
  assume B[measurable]: "B \<in> sets Z"
  show "(\<lambda>x. emeasure (distr (\<kappa> x) Z f) B) \<in> borel_measurable X"
    by(rule measurable_cong[where g= "(\<lambda>x. \<kappa> x (f -` B \<inter> space Y))",THEN iffD2]) (auto simp: emeasure_distr sets_eq_imp_space_eq[OF kernel_sets])
next
  show "\<And>x. space Z = {} \<Longrightarrow> x \<in> space X \<Longrightarrow> x \<in> {}"
    by (metis Y_not_empty assms measurable_empty_iff)
qed auto

lemma measure_kernel_comp:
  assumes [measurable]: "f \<in> W \<rightarrow>\<^sub>M X"
  shows "measure_kernel W Y (\<lambda>x. \<kappa> (f x))"
  using measurable_space[OF assms] kernel_sets Y_not_empty
  by(auto simp: measure_kernel_def)

lemma emeasure_bind_kernel:
  assumes "sets \<mu> = sets X" "B \<in> sets Y" "space X \<noteq> {}"
  shows "(\<mu> \<bind>\<^sub>k \<kappa>) B = (\<integral>\<^sup>+x. (\<kappa> x B) \<partial>\<mu>)"
proof -
  have "sets (\<kappa> (SOME x. x \<in> space \<mu>)) = sets Y"
    by(rule someI2_ex) (use assms(3) kernel_sets sets_eq_imp_space_eq[OF assms(1)] in auto)
  with sets_eq_imp_space_eq[OF this] show ?thesis
    by(simp add: bind_kernel_def sets_eq_imp_space_eq[OF assms(1) ]assms(3) nn_integral_measure[OF assms(1,2)])
qed

lemma measure_bind_kernel:
  assumes [measurable_cong]:"sets \<mu> = sets X" and [measurable]:"B \<in> sets Y" "space X \<noteq> {}" "AE x in \<mu>. \<kappa> x B < \<infinity>"
  shows "measure (\<mu> \<bind>\<^sub>k \<kappa>) B = (\<integral>x. measure (\<kappa> x) B \<partial>\<mu>)"
  using assms(4) by(auto simp: emeasure_bind_kernel[OF assms(1-3)] measure_def integral_eq_nn_integral intro!: arg_cong[of _ _ enn2real] nn_integral_cong_AE)

lemma sets_bind_kernel:
  assumes "space X \<noteq> {}" "sets \<mu> = sets X"
  shows "sets (\<mu> \<bind>\<^sub>k \<kappa>) = sets Y"
  using sets_bind_kernel[of \<mu> \<kappa>, OF kernel_sets,simplified sets_eq_imp_space_eq[OF assms(2)]]
  by(auto simp: assms(1))

lemma distr_bind_kernel:
  assumes "space X \<noteq> {}" and [measurable_cong]:"sets \<mu> = sets X" and [measurable]: "f \<in> Y \<rightarrow>\<^sub>M Z"
  shows "distr (\<mu> \<bind>\<^sub>k \<kappa>) Z f = \<mu> \<bind>\<^sub>k (\<lambda>x. distr (\<kappa> x) Z f)"
proof -
  {
    fix A
    assume A[measurable]:"A \<in> sets Z"
    have sets[measurable_cong]:"sets (\<mu> \<bind>\<^sub>k \<kappa>) = sets Y"
      by(rule sets_bind_kernel[OF assms(1,2)])
    have "emeasure (distr (\<mu> \<bind>\<^sub>k \<kappa>) Z f) A = emeasure (\<mu> \<bind>\<^sub>k (\<lambda>x. distr (\<kappa> x) Z f)) A" (is "?lhs = ?rhs")
    proof -
      have "?lhs = (\<integral>\<^sup>+ x. emeasure (\<kappa> x) (f -` A \<inter> space Y) \<partial>\<mu>)"
        by(simp add: emeasure_distr sets_eq_imp_space_eq[OF sets] emeasure_bind_kernel[OF assms(2) _ assms(1)])
      also have "... = (\<integral>\<^sup>+ x. emeasure (distr (\<kappa> x) Z f) A \<partial>\<mu>)"
        by(auto simp: emeasure_distr sets_eq_imp_space_eq[OF assms(2)] sets_eq_imp_space_eq[OF kernel_sets] intro!: nn_integral_cong)
      also have "... = ?rhs"
        by(simp add: measure_kernel.emeasure_bind_kernel[OF distr_measure_kernel[OF assms(3)] assms(2) _ assms(1)])
      finally show ?thesis .
    qed
  }
  thus ?thesis
    by(auto intro!: measure_eqI simp: measure_kernel.sets_bind_kernel[OF distr_measure_kernel[OF assms(3)] assms(1,2)])
qed

lemma bind_kernel_distr:
  assumes [measurable]: "f \<in> W \<rightarrow>\<^sub>M X" and "space W \<noteq> {}"
  shows "distr W X f \<bind>\<^sub>k \<kappa> = W \<bind>\<^sub>k (\<lambda>x. \<kappa> (f x))"
proof -
  have X: "space X \<noteq> {}"
    using measurable_space[OF assms(1)] assms(2) by auto
  show ?thesis
    by(rule measure_eqI, insert X) (auto simp: sets_bind_kernel[OF X] measure_kernel.sets_bind_kernel[OF measure_kernel_comp[OF assms(1)] assms(2) refl] emeasure_bind_kernel nn_integral_distr measure_kernel.emeasure_bind_kernel[OF  measure_kernel_comp[OF assms(1)] refl _ assms(2)])
qed

lemma bind_kernel_return:
  assumes "x \<in> space X"
  shows "return X x \<bind>\<^sub>k \<kappa> = \<kappa> x"
proof -
  have X: "space X \<noteq> {}"
    using assms by auto
  show ?thesis
    by(rule measure_eqI) (auto simp: sets_bind_kernel[OF X sets_return] kernel_sets[OF assms] emeasure_bind_kernel[OF sets_return,simplified,OF _ X] nn_integral_return[OF assms])
qed

lemma kernel_nn_integral_measurable:
  assumes "f \<in> borel_measurable Y"
  shows "(\<lambda>x. \<integral>\<^sup>+ y. f y \<partial>(\<kappa> x)) \<in> borel_measurable X"
  using assms
proof induction
  case (cong f g)
  then show ?case
    by(auto intro!: measurable_cong[where f="\<lambda>x. \<integral>\<^sup>+ y. f y \<partial>(\<kappa> x)" and g= "\<lambda>x. \<integral>\<^sup>+ y. g y \<partial>(\<kappa> x)",THEN iffD2] nn_integral_cong simp: sets_eq_imp_space_eq[OF kernel_sets])
next
  case (set A)
  then show ?case
    by(auto intro!: measurable_cong[where f="\<lambda>x. integral\<^sup>N (\<kappa> x) (indicator A)" and g="\<lambda>x. \<kappa> x A",THEN iffD2])
next
  case (mult u c)
  then show ?case
    by(auto intro!: measurable_cong[where f="\<lambda>x. \<integral>\<^sup>+ y. c * u y \<partial>\<kappa> x" and g="\<lambda>x. c * \<integral>\<^sup>+ y. u y \<partial>\<kappa> x",THEN iffD2] simp: nn_integral_cmult)
next
  case (add u v)
  then show ?case
    by(auto intro!: measurable_cong[where f="\<lambda>x. \<integral>\<^sup>+ y. v y + u y \<partial>\<kappa> x" and g="\<lambda>x. (\<integral>\<^sup>+ y. v y \<partial>\<kappa> x) + (\<integral>\<^sup>+ y. u y \<partial>\<kappa> x)",THEN iffD2] simp: nn_integral_add)
next
  case (seq U)
  then show ?case
    by(intro measurable_cong[where f="\<lambda>x. integral\<^sup>N (\<kappa> x) (\<Squnion> range U)" and g="\<lambda>x. \<Squnion>i. integral\<^sup>N (\<kappa> x) (U i)",THEN iffD2])
      (auto simp: nn_integral_monotone_convergence_SUP[of U,simplified SUP_apply[symmetric]])
qed

lemma bind_kernel_measure_kernel:
  assumes "measure_kernel Y Z k'"
  shows "measure_kernel X Z (\<lambda>x. \<kappa> x \<bind>\<^sub>k k')"
proof(cases "space X = {}")
  case True
  then show ?thesis
    by(auto simp: measure_kernel_def measurable_def)
next
  case X:False
  then have Y: "space Y \<noteq> {}"
    by(simp add: Y_not_empty)
  interpret k': measure_kernel Y Z k' by fact
  show ?thesis
  proof
    fix B
    assume "B \<in> sets Z"
    with k'.emeasure_bind_kernel[OF kernel_sets,of _ B] show "(\<lambda>x. emeasure (\<kappa> x \<bind>\<^sub>k k') B) \<in> borel_measurable X"
      by(auto intro!: measurable_cong[where f="\<lambda>x. emeasure (\<kappa> x \<bind>\<^sub>k k') B" and g="\<lambda>x. \<integral>\<^sup>+ y. emeasure (k' y) B \<partial>\<kappa> x",THEN iffD2] kernel_nn_integral_measurable simp: sets_eq_imp_space_eq[OF kernel_sets] Y)
  qed(use k'.Y_not_empty Y  k'.sets_bind_kernel[OF Y kernel_sets] in auto)
qed

lemma restrict_measure_kernel: "measure_kernel (restrict_space X A) Y \<kappa>"
proof
  fix B
  assume "B \<in> sets Y"
  from emeasure_measurable[OF this] show "(\<lambda>x. emeasure (\<kappa> x) B) \<in> borel_measurable (restrict_space X A)"
    using measurable_restrict_space1 by blast
qed(insert Y_not_empty,auto simp add: space_restrict_space kernel_sets)

end

lemma measure_kernel_cong_sets:
  assumes "sets X = sets X'" "sets Y = sets Y'"
  shows "measure_kernel X Y = measure_kernel X' Y'"
  by standard (simp add: measure_kernel_def measurable_cong_sets[OF assms(1) refl] sets_eq_imp_space_eq[OF assms(1)] assms(2) sets_eq_imp_space_eq[OF assms(2)])

lemma measure_kernel_pair_countble1:
  assumes "countable A" "\<And>i. i \<in> A \<Longrightarrow> measure_kernel X Y (\<lambda>x. k (i,x))"
  shows "measure_kernel (count_space A \<Otimes>\<^sub>M X) Y k"
  using assms by(auto simp: measure_kernel_def space_pair_measure intro!: measurable_pair_measure_countable1)

lemma measure_kernel_empty_trivial:
  assumes "space X = {}"
  shows "measure_kernel X Y k"
  using assms by(auto simp: measure_kernel_def measurable_def)

subsection \<open> Finite Kernel \<close>
locale finite_kernel = measure_kernel +
  assumes finite_measure_spaces: "\<exists>r<\<infinity>. \<forall>x\<in> space X. \<kappa> x (space Y) < r"
begin

lemma finite_measures:
  assumes "x \<in> space X"
  shows "finite_measure (\<kappa> x)"
proof-
  obtain r where "\<kappa> x (space Y) < r"
    using finite_measure_spaces assms by metis
  then show ?thesis
    by(auto intro!: finite_measureI simp: sets_eq_imp_space_eq[OF kernel_sets[OF assms]])
qed

end

lemma finite_kernel_empty_trivial: "space X = {} \<Longrightarrow> finite_kernel X Y f"
  by(auto simp: finite_kernel_def finite_kernel_axioms_def measure_kernel_empty_trivial intro!: exI[where x=1])

lemma finite_kernel_cong_sets:
  assumes "sets X = sets X'" "sets Y = sets Y'"
  shows "finite_kernel X Y = finite_kernel X' Y'"
  by standard (auto simp: measure_kernel_cong_sets[OF assms] finite_kernel_def finite_kernel_axioms_def sets_eq_imp_space_eq[OF assms(1)] sets_eq_imp_space_eq[OF assms(2)])

subsection \<open> Sub-Probability Kernel\<close>
locale subprob_kernel = measure_kernel +
  assumes subprob_spaces: "\<And>x. x \<in> space X \<Longrightarrow> subprob_space (\<kappa> x)"
begin
lemma subprob_space:
 "\<And>x. x \<in> space X \<Longrightarrow> \<kappa> x (space Y) \<le> 1"
  by (simp add: subprob_space.subprob_emeasure_le_1 subprob_spaces)

lemma subprob_measurable[measurable]:
 "\<kappa> \<in> X \<rightarrow>\<^sub>M subprob_algebra Y"
  by(auto intro!: measurable_subprob_algebra_generated[OF sets.sigma_sets_eq[symmetric] sets.Int_stable sets.space_closed] simp: subprob_spaces kernel_sets emeasure_measurable)

lemma finite_kernel: "finite_kernel X Y \<kappa>"
  by(auto simp: finite_kernel_def finite_kernel_axioms_def intro!: measure_kernel_axioms exI[where x=2] order.strict_trans1[OF subprob_space.subprob_emeasure_le_1[OF subprob_spaces]])

sublocale finite_kernel
  by (rule finite_kernel)

end

lemma subprob_kernel_def':
 "subprob_kernel X Y \<kappa> \<longleftrightarrow> \<kappa> \<in> X \<rightarrow>\<^sub>M subprob_algebra Y"
  by(auto simp: subprob_kernel.subprob_measurable subprob_kernel_def subprob_kernel_axioms_def measure_kernel_def measurable_subprob_algebra measurable_empty_iff space_subprob_algebra_empty_iff)
    (auto simp: subprob_measurableD(2) subprob_space_kernel)

lemmas subprob_kernelI = measurable_subprob_algebra[simplified subprob_kernel_def'[symmetric]]

lemma subprob_kernel_cong_sets:
  assumes "sets X = sets X'" "sets Y = sets Y'"
  shows "subprob_kernel X Y = subprob_kernel X' Y'"
  by standard (auto simp: subprob_kernel_def' subprob_algebra_cong[OF assms(2)] measurable_cong_sets[OF assms(1) refl])

lemma subprob_kernel_empty_trivial:
  assumes "space X = {}"
  shows "subprob_kernel X Y k"
  using assms by(auto simp: subprob_kernel_def subprob_kernel_axioms_def intro!: measure_kernel_empty_trivial)

lemma bind_kernel_bind:
  assumes "f \<in> M \<rightarrow>\<^sub>M subprob_algebra N"
  shows "M \<bind>\<^sub>k f = M \<bind> f"
proof(cases "space M = {}")
  case True
  then show ?thesis
    by(simp add: bind_kernel_def bind_def)
next
  case h:False
  interpret subprob_kernel M N f
    using assms(1) by(simp add: subprob_kernel_def')
  show ?thesis
    by(rule measure_eqI,insert sets_kernel[OF assms]) (auto simp: h sets_bind_kernel emeasure_bind_kernel[OF refl _ h] emeasure_bind[OF h assms])
qed

lemma(in measure_kernel) subprob_kernel_sum:
  assumes "\<And>x. x \<in> space X \<Longrightarrow> finite_measure (\<kappa> x)"
  obtains ki where "\<And>i. subprob_kernel X Y (ki i)" "\<And>A x. x \<in> space X \<Longrightarrow> \<kappa> x A = (\<Sum>i. ki i x A)"
proof -
  obtain u where u: "\<And>x. x \<in> space X \<Longrightarrow> u x < \<infinity>" "\<And>x. x \<in> space X \<Longrightarrow> u x = \<kappa> x (space Y)"
    using finite_measure.emeasure_finite[OF assms]
    by (simp add: top.not_eq_extremum)  
  have [measurable]: "u \<in> borel_measurable X"
    by(simp cong: measurable_cong add: u(2))
  define ki where "ki \<equiv> (\<lambda>i x. if i < nat \<lceil>enn2real (u x)\<rceil> then scale_measure  (1 / ennreal (real_of_int \<lceil>enn2real (u x)\<rceil>)) (\<kappa> x) else (sigma (space Y) (sets Y)))"
  have 1:"\<And>i x. x \<in> space X \<Longrightarrow> sets (ki i x) = sets Y"
    by(auto simp: ki_def kernel_sets)
  have "subprob_kernel X Y (ki i)" for i
  proof -
    {
      fix i B
      assume [measurable]: "B \<in> sets Y"
      have "(\<lambda>x. emeasure (ki i x) B) = (\<lambda>x. if i < nat \<lceil>enn2real (u x)\<rceil> then (1 / ennreal (real_of_int \<lceil>enn2real (u x)\<rceil>)) * emeasure (\<kappa> x) B else 0)"
        by(auto simp: ki_def emeasure_sigma)
      also have "... \<in> borel_measurable X"
        by simp
      finally have "(\<lambda>x. emeasure (ki i x) B) \<in> borel_measurable X" .
    }
    moreover {
      fix i x
      assume x:"x \<in> space X"
      have "emeasure (ki i x) (space Y) \<le> 1"
        by(cases "u x = 0",auto simp: ki_def emeasure_sigma u(2)[OF x,symmetric]) (metis u(1)[OF x,simplified] divide_ennreal_def divide_le_posI_ennreal enn2real_le le_of_int_ceiling mult.commute mult.right_neutral not_gr_zero order.strict_iff_not)
      hence "subprob_space (ki i x)"
        using x Y_not_empty by(fastforce intro!: subprob_spaceI simp: sets_eq_imp_space_eq[OF 1[OF x]])
    }
    ultimately show ?thesis
      by(auto simp: subprob_kernel_def measure_kernel_def 1 Y_not_empty subprob_kernel_axioms_def)
  qed
  moreover have "\<kappa> x A = (\<Sum>i. ki i x A)" if x:"x \<in> space X" for x A
  proof (cases "A \<in> sets Y")
    case A[measurable]:True
    have "emeasure (\<kappa> x) A = (\<Sum>i<nat \<lceil>enn2real (u x)\<rceil>. emeasure (ki i x) A)"
    proof(cases "u x = 0")
      case True
      then show ?thesis
        using u(2)[OF that] by simp (metis A emeasure_eq_0 kernel_sets sets.sets_into_space sets.top x)
    next
      case u0:False
      hence "real_of_int \<lceil>enn2real (u x)\<rceil> > 0"
        by (metis enn2real_nonneg ennreal_0 ennreal_enn2real_if infinity_ennreal_def linorder_not_le nat_0_iff nle_le of_int_le_0_iff of_nat_eq_0_iff real_nat_ceiling_ge u(1) x)
      with u(1)[OF x] have "of_nat (nat \<lceil>enn2real (u x)\<rceil>) / ennreal (real_of_int \<lceil>enn2real (u x)\<rceil>) = 1"
        by(simp add: ennreal_eq_0_iff ennreal_of_nat_eq_real_of_nat)
      thus ?thesis
        by(simp add: ki_def ennreal_divide_times[symmetric]  mult.assoc[symmetric])
    qed
    then show ?thesis
      by(auto simp: suminf_offset[of "\<lambda>i. emeasure (ki i x) A" "nat \<lceil>enn2real (u x)\<rceil>"]) (simp add: ki_def emeasure_sigma)
  next
    case False
    then show ?thesis
      using kernel_sets[OF x] 1[OF x]
      by(simp add: emeasure_notin_sets)
  qed
  ultimately show ?thesis
    using that by blast
qed

subsection \<open> Probability Kernel \<close>
locale prob_kernel = measure_kernel +
  assumes prob_spaces: "\<And>x. x \<in> space X \<Longrightarrow> prob_space (\<kappa> x)"
begin

lemma prob_space:
 "\<And>x. x \<in> space X \<Longrightarrow> \<kappa> x (space Y) = 1"
  using kernel_space prob_space.emeasure_space_1 prob_spaces by fastforce

lemma prob_measurable[measurable]:
 "\<kappa> \<in> X \<rightarrow>\<^sub>M prob_algebra Y"
  by(auto intro!: measurable_prob_algebra_generated[OF sets.sigma_sets_eq[symmetric] sets.Int_stable sets.space_closed] simp: prob_spaces kernel_sets emeasure_measurable)

lemma subprob_kernel: "subprob_kernel X Y \<kappa>"
  by (simp add: measurable_prob_algebraD subprob_kernel_def')

sublocale subprob_kernel
  by (simp add: subprob_kernel)

lemma restrict_probability_kernel:
  "prob_kernel (restrict_space X A) Y \<kappa>"
  by(auto simp: prob_kernel_def restrict_measure_kernel prob_kernel_axioms_def space_restrict_space prob_spaces)

end

lemma prob_kernel_def':
 "prob_kernel X Y \<kappa> \<longleftrightarrow> \<kappa> \<in> X \<rightarrow>\<^sub>M prob_algebra Y"
proof
  assume h:"\<kappa> \<in> X \<rightarrow>\<^sub>M prob_algebra Y"
  show "prob_kernel X Y \<kappa>"
    using subprob_measurableD(2)[OF measurable_prob_algebraD[OF h]] measurable_space[OF h] measurable_emeasure_kernel[OF  measurable_prob_algebraD[OF h]]
    by(auto simp: prob_kernel_def measure_kernel_def prob_kernel_axioms_def space_prob_algebra ) (metis prob_space.not_empty sets_eq_imp_space_eq)
qed(auto simp: prob_kernel.prob_measurable prob_kernel_def prob_kernel_axioms_def measure_kernel_def)


lemma bind_kernel_return'':
  assumes "sets M = sets N"
  shows "M \<bind>\<^sub>k return N = M"
proof(cases "space M = {}")
  case True
  then show ?thesis
    by(simp add: bind_kernel_def space_empty[symmetric])
next
  case False
  then have 1: "space N \<noteq> {}"
    by(simp add: sets_eq_imp_space_eq[OF assms])
  interpret prob_kernel N N "return N"
    by(simp add: prob_kernel_def')
  show ?thesis
    by(rule measure_eqI) (auto simp: emeasure_bind_kernel[OF assms _ 1] sets_bind_kernel[OF 1 assms] assms)
qed

subsection\<open> S-Finite Kernel \<close>
locale s_finite_kernel = measure_kernel +
  assumes s_finite_kernel_sum: "\<exists>ki. (\<forall>i. finite_kernel X Y (ki i) \<and> (\<forall>x\<in>space X. \<forall>A\<in>sets Y. \<kappa> x A = (\<Sum>i. ki i x A)))"

lemma s_finite_kernel_subI:
  assumes "\<And>x. x \<in> space X \<Longrightarrow> sets (\<kappa> x) = sets Y" "\<And>i. subprob_kernel X Y (ki i)" "\<And>x A. x \<in> space X \<Longrightarrow> A \<in> sets Y \<Longrightarrow> emeasure (\<kappa> x) A = (\<Sum>i. ki i x A)"
  shows "s_finite_kernel X Y \<kappa>"
proof -
  interpret measure_kernel X Y \<kappa>
  proof
    show "B \<in> sets Y \<Longrightarrow> (\<lambda>x. emeasure (\<kappa> x) B) \<in> borel_measurable X" for B
      using assms(2) by(simp add: assms(3) subprob_kernel_def' cong: measurable_cong)
  next
    show "space X \<noteq> {} \<Longrightarrow> space Y \<noteq> {}"
      using assms(2)[of 0] by(auto simp: subprob_kernel_def measure_kernel_def)
  qed fact
  show ?thesis
    by (auto simp: s_finite_kernel_def measure_kernel_axioms s_finite_kernel_axioms_def assms(2,3) intro!: exI[where x=ki] subprob_kernel.finite_kernel)
qed

context s_finite_kernel
begin

lemma s_finite_kernels_fin:
  obtains ki where "\<And>i. finite_kernel X Y (ki i)" "\<And>x A. x \<in> space X \<Longrightarrow> \<kappa> x A = (\<Sum>i. ki i x A)"
proof -
  obtain ki where ki:"\<And>i. finite_kernel X Y (ki i)" "\<And>x A. x \<in> space X \<Longrightarrow> A \<in> sets Y \<Longrightarrow> \<kappa> x A = (\<Sum>i. ki i x A)"
    by(metis s_finite_kernel_sum)
  hence "\<kappa> x A = (\<Sum>i. ki i x A)" if "x \<in> space X " for x A
    by(cases "A \<in> sets Y", insert that kernel_sets[OF that]) (auto simp: finite_kernel_def measure_kernel_def emeasure_notin_sets)
  with ki show ?thesis
    using that by auto
qed

lemma s_finite_kernels:
  obtains ki where "\<And>i. subprob_kernel X Y (ki i)" "\<And>x A. x \<in> space X \<Longrightarrow> \<kappa> x A = (\<Sum>i. ki i x A)"
proof -
  obtain ki where ki:"\<And>i. finite_kernel X Y (ki i)" "\<And>x A. x \<in> space X \<Longrightarrow> \<kappa> x A = (\<Sum>i. ki i x A)"
    by(metis s_finite_kernels_fin)
  have "\<exists>kij. (\<forall>j. subprob_kernel X Y (kij j)) \<and> (\<forall>x A. x \<in> space X \<longrightarrow> ki i x A = (\<Sum>j. kij j x A))" for i
    using measure_kernel.subprob_kernel_sum[of X Y "ki i", OF _ finite_kernel.finite_measures[OF ki(1)[of i]]] ki(1)[of i] by(metis finite_kernel_def)
  then obtain kij where kij: "\<And>i j. subprob_kernel X Y (kij i j)" "\<And>x A i. x \<in> space X \<Longrightarrow> ki i x A = (\<Sum>j. kij i j x A)"
    by metis
  have "\<And>i. subprob_kernel X Y (case_prod kij (prod_decode i))"
    using kij(1) by(auto simp: split_beta)
  moreover have "x \<in> space X \<Longrightarrow> \<kappa> x A = (\<Sum>i. case_prod kij (prod_decode i) x A)" for x A
    using suminf_ennreal_2dimen[of "\<lambda>i. ki i x A" "\<lambda>(i,j). kij i j x A"]
    by(auto simp: ki(2) kij(2) split_beta')
  ultimately show ?thesis
    using that by fastforce
qed

lemma image_s_finite_measure:
  assumes "x \<in> space X"
  shows "s_finite_measure (\<kappa> x)"
proof -
  obtain ki where ki:"\<And>i. subprob_kernel X Y (ki i)" "\<And>x A. x \<in> space X \<Longrightarrow> \<kappa> x A = (\<Sum>i. ki i x A)"
    by(metis s_finite_kernels)
  show ?thesis
    using ki(1)[simplified subprob_kernel_def'] measurable_space[OF ki(1)[simplified subprob_kernel_def'] assms]
    by(auto intro!: s_finite_measureI[where Mi="\<lambda>i. ki i x"] subprob_space.axioms(1) simp: kernel_sets[OF assms] space_subprob_algebra ki(2)[OF assms])
qed

corollary kernel_measurable_s_finite[measurable]:"\<kappa> \<in> X \<rightarrow>\<^sub>M s_finite_measure_algebra Y"
  by(auto intro!: measurable_s_finite_measure_algebra simp: kernel_sets image_s_finite_measure)

lemma comp_measurable:
  assumes f[measurable]:"f \<in> M \<rightarrow>\<^sub>M X"
  shows "s_finite_kernel M Y (\<lambda>x. \<kappa> (f x))"
proof -
  obtain ki where ki:"\<And>i. subprob_kernel X Y (ki i)" "\<And>x A. x \<in> space X \<Longrightarrow> \<kappa> x A = (\<Sum>i. ki i x A)"
    by(metis s_finite_kernels)
  show ?thesis
    using ki(1) measurable_space[OF f] by(auto intro!: s_finite_kernel_subI[where ki="\<lambda>i x. ki i (f x)"] simp: subprob_kernel_def' ki(2) kernel_sets)
qed

lemma distr_s_finite_kernel:
  assumes f[measurable]: "f \<in> Y \<rightarrow>\<^sub>M Z"
  shows "s_finite_kernel X Z (\<lambda>x. distr (\<kappa> x) Z f)"
proof -
  obtain ki where ki:"\<And>i. subprob_kernel X Y (ki i)" "\<And>x A. x \<in> space X \<Longrightarrow> \<kappa> x A = (\<Sum>i. ki i x A)"
    by(metis s_finite_kernels)
  hence 1:"x \<in> space X \<Longrightarrow> space (ki i x) = space Y" for x i
    by(auto simp: subprob_kernel_def' intro!: subprob_measurableD(1)[of _ X Y])
  have [measurable]:"B \<in> sets Z \<Longrightarrow> (\<lambda>x. emeasure (distr (\<kappa> x) Z f) B) \<in> borel_measurable X" for B
    by(rule measurable_cong[where g="\<lambda>x. \<kappa> x (f -` B \<inter> space Y)", THEN iffD2]) (auto simp: emeasure_distr sets_eq_imp_space_eq[OF kernel_sets])
  show ?thesis
    using ki(1) measurable_distr[OF f] by(auto intro!: s_finite_kernel_subI[where ki="\<lambda>i x. distr (ki i x) Z f"] simp: subprob_kernel_def' emeasure_distr ki(2) sets_eq_imp_space_eq[OF kernel_sets] 1)
qed

lemma comp_s_finite_measure:
  assumes "s_finite_measure \<mu>" and [measurable_cong]: "sets \<mu> = sets X"
  shows "s_finite_measure (\<mu> \<bind>\<^sub>k \<kappa>)"
proof(cases "space X = {}")
  case 1:True
  show ?thesis
    by(auto simp: sets_eq_imp_space_eq[OF assms(2)] 1 bind_kernel_def intro!: finite_measure.s_finite_measure_finite_measure finite_measureI)
next
  case 0:False
  then have 1: "space \<mu> \<noteq> {}"
    by(simp add: sets_eq_imp_space_eq[OF assms(2)])
  have 2: "sets (\<kappa> (SOME x. x \<in> space \<mu>)) = sets Y"
    by(rule someI2_ex, insert 1 kernel_sets) (auto simp: sets_eq_imp_space_eq[OF assms(2)])
  have sets_bind[measurable_cong]: "sets (\<mu> \<bind>\<^sub>k \<kappa>) = sets Y"
    by(simp add: bind_kernel_def 1 sets_eq_imp_space_eq[OF 2] 2)
  obtain \<mu>i where mui[measurable_cong]: "\<And>i. sets (\<mu>i i) = sets X" "\<And>i. (\<mu>i i) (space X) \<le> 1" "\<And>A. \<mu> A = (\<Sum>i. \<mu>i i A)"
    using s_finite_measure.finite_measures[OF assms(1)] assms(2) sets_eq_imp_space_eq[OF assms(2)] by metis
  obtain ki where ki:"\<And>i. subprob_kernel X Y (ki i)" "\<And>x A. x \<in> space X \<Longrightarrow> \<kappa> x A = (\<Sum>i. ki i x A)"
    by(metis s_finite_kernels)
  define Mi where "Mi \<equiv> (\<lambda>n. (\<lambda>(i,j). measure_of (space Y) (sets Y) (\<lambda>A. \<integral>\<^sup>+x. (ki i x A) \<partial>(\<mu>i j))) (prod_decode n))"
  have emeasure:"(\<mu> \<bind>\<^sub>k \<kappa>) A = (\<Sum>i. (Mi i) A)" (is "?lhs = ?rhs") if "A \<in> sets Y" for A
  proof -
    have "?lhs = (\<integral>\<^sup>+x. (\<kappa> x A) \<partial>\<mu>)"
      by(simp add: emeasure_bind_kernel[OF assms(2) that 0])
    also have "... = (\<integral>\<^sup>+x. (\<Sum>i. (ki i x A)) \<partial>\<mu>)"
      by(auto intro!: nn_integral_cong simp: ki sets_eq_imp_space_eq[OF assms(2)])
    also have "... = (\<Sum>i. \<integral>\<^sup>+x. (ki i x A) \<partial>\<mu>)"
      by(auto intro!: nn_integral_suminf) (metis ki(1) assms(2) measurable_cong_sets measure_kernel.emeasure_measurable subprob_kernel_def that)
    also have "... = ?rhs"
      unfolding Mi_def
    proof(rule suminf_ennreal_2dimen[symmetric])
      fix m
      interpret kim: subprob_kernel X Y "ki m"
        by(simp add: ki)
      show "(\<integral>\<^sup>+ x. (ki m x) A \<partial>\<mu>) = (\<Sum>n. emeasure (case (m, n) of (i, j) \<Rightarrow> measure_of (space Y) (sets Y) (\<lambda>A. \<integral>\<^sup>+ x. emeasure (ki i x) A \<partial>\<mu>i j)) A)"
        using kim.emeasure_measurable[OF that] by(simp add: kim.nn_integral_measure[OF mui(1) that] nn_integral_measure_suminf[OF mui(1)[simplified assms(2)[symmetric]] mui(3)])
    qed
    finally show ?thesis .
  qed
  have fin:"finite_measure (Mi i)" for i
  proof(rule prod.exhaust[where y="prod_decode i"])
    fix j1 j2
      interpret kij: subprob_kernel X Y "ki j1"
        by(simp add: ki)
    assume pd:"prod_decode i = (j1, j2)"
    have "Mi i (space (Mi i)) = (\<integral>\<^sup>+x. (ki j1 x (space Y)) \<partial>\<mu>i j2)"
      by(auto simp: Mi_def pd kij.nn_integral_measure[OF mui(1) sets.top])
    also have "... \<le> (\<integral>\<^sup>+x. 1 \<partial>\<mu>i j2)"
      by(intro nn_integral_mono) (metis kij.subprob_space mui(1) sets_eq_imp_space_eq)
    also have "... \<le> 1"
      using mui by (simp add: sets_eq_imp_space_eq[OF mui(1)])
    finally show "finite_measure (Mi i)"
      by (metis ennreal_one_less_top finite_measureI infinity_ennreal_def less_le_not_le)
  qed
  have 3: "sets (Mi i) = sets (\<mu> \<bind>\<^sub>k \<kappa>)" for i
    by(simp add: Mi_def split_beta sets_bind)
  show "s_finite_measure (\<mu> \<bind>\<^sub>k \<kappa>)"
    using emeasure fin 3 by (auto intro!: exI[where x=Mi] simp: s_finite_measure_def sets_bind)
qed

end

lemma s_finite_kernel_empty_trivial:
  assumes "space X = {}"
  shows "s_finite_kernel X Y k"
  using assms by(auto simp: s_finite_kernel_def s_finite_kernel_axioms_def intro!: measure_kernel_empty_trivial finite_kernel_empty_trivial)

lemma s_finite_kernel_def': "s_finite_kernel X Y \<kappa> \<longleftrightarrow> ((\<forall>x. x \<in> space X \<longrightarrow> sets (\<kappa> x) = sets Y) \<and> (\<exists>ki. (\<forall>i. subprob_kernel X Y (ki i)) \<and> (\<forall>x A. x \<in> space X \<longrightarrow> A \<in> sets Y \<longrightarrow> emeasure (\<kappa> x) A = (\<Sum>i. ki i x A))))" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then interpret s_finite_kernel X Y \<kappa> .
  from s_finite_kernels obtain ki where ki:"\<And>i. subprob_kernel X Y (ki i)" "\<And>x A. x \<in> space X \<Longrightarrow> emeasure (\<kappa> x) A = (\<Sum>i. emeasure (ki i x) A)"
    by metis
  thus ?r
    by(auto simp: kernel_sets)
qed(auto intro!: s_finite_kernel_subI)

lemma(in finite_kernel) s_finite_kernel_finite_kernel: "s_finite_kernel X Y \<kappa>"
proof
  consider "space X = {}" | "space X \<noteq> {}" by auto
  then show "\<exists>ki. \<forall>i. finite_kernel X Y (ki i) \<and> (\<forall>x\<in>space X. \<forall>A\<in>sets Y. (\<kappa> x) A = (\<Sum>i. (ki i x) A))"
  proof cases
    case 1
    then show ?thesis
      by(auto simp: finite_kernel_def measure_kernel_def finite_kernel_axioms_def measurable_def intro!: exI[where x=0])
  next
    case 2
    then have y:"space Y \<noteq> {}" by(simp add: Y_not_empty)
    define ki where "ki i \<equiv> case i of 0 \<Rightarrow> \<kappa> | Suc _ \<Rightarrow> (\<lambda>_. sigma (space Y) (sets Y))" for i
    have "finite_kernel X Y (ki i)" for i
      by (cases i, auto simp: ki_def finite_kernel_axioms) (auto simp: emeasure_sigma finite_kernel_def measure_kernel_def finite_kernel_axioms_def y intro!: finite_measureI exI[where x=1])
    moreover have "(\<kappa> x) A = (\<Sum>i. (ki i x) A)" for x A
      by(simp add: suminf_offset[where i="Suc 0" and f="\<lambda>i. ki i x A",simplified],simp add: ki_def emeasure_sigma)
    ultimately show ?thesis by auto
  qed
qed

lemmas(in subprob_kernel) s_finite_kernel_subprob_kernel = s_finite_kernel_finite_kernel
lemmas(in prob_kernel) s_finite_kernel_prob_kernel = s_finite_kernel_subprob_kernel

sublocale finite_kernel \<subseteq> s_finite_kernel
  by(rule s_finite_kernel_finite_kernel)

lemma s_finite_kernel_cong_sets:
  assumes "sets X = sets X'" "sets Y = sets Y'"
  shows "s_finite_kernel X Y = s_finite_kernel X' Y'"
  by standard (simp add: s_finite_kernel_def measurable_cong_sets[OF assms(1) refl] sets_eq_imp_space_eq[OF assms(1)] assms(2) measure_kernel_cong_sets[OF assms] s_finite_kernel_axioms_def finite_kernel_cong_sets[OF assms])

lemma(in s_finite_kernel) s_finite_kernel_cong:
  assumes "\<And>x. x \<in> space X \<Longrightarrow> \<kappa> x = g x"
  shows "s_finite_kernel X Y g"
  using assms s_finite_kernel_axioms by(auto simp: s_finite_kernel_def s_finite_kernel_axioms_def measure_kernel_def cong: measurable_cong)

lemma(in s_finite_measure) s_finite_kernel_const:
  assumes "space M \<noteq> {}"
  shows "s_finite_kernel X M (\<lambda>x. M)"
proof
  obtain Mi where Mi:"\<And>i. sets (Mi i) = sets M" "\<And>i. (Mi i) (space M) \<le> 1" "\<And>A. M A = (\<Sum>i. Mi i A)"
    by(metis finite_measures)
  hence "\<And>i. subprob_kernel X M (\<lambda>x. Mi i)"
    by(auto simp: subprob_kernel_def' space_subprob_algebra sets_eq_imp_space_eq[OF Mi(1)] assms intro!:measurable_const subprob_spaceI)
  thus "\<exists>ki. \<forall>i. finite_kernel X M (ki i) \<and> (\<forall>x\<in>space X. \<forall>A\<in>sets M. M A = (\<Sum>i. (ki i x) A))"
    by(auto intro!: exI[where x="\<lambda>i x. Mi i"] Mi(3) subprob_kernel.finite_kernel)
qed (auto simp: assms)

lemma s_finite_kernel_pair_countble1:
  assumes "countable A" "\<And>i. i \<in> A \<Longrightarrow> s_finite_kernel X Y (\<lambda>x. k (i,x))"
  shows "s_finite_kernel (count_space A \<Otimes>\<^sub>M X) Y k"
proof -
  have "\<exists>ki. (\<forall>j. subprob_kernel X Y (ki j)) \<and> (\<forall>x B. x \<in> space X \<longrightarrow> B \<in> sets Y \<longrightarrow> k (i,x) B = (\<Sum>j. ki j x B))" if "i \<in> A" for i
    using s_finite_kernel.s_finite_kernels[OF assms(2)[OF that]] by metis
  then obtain ki where ki:"\<And>i j. i \<in> A \<Longrightarrow> subprob_kernel X Y (ki i j)" "\<And>i x B. i \<in> A \<Longrightarrow> x \<in> space X \<Longrightarrow> B \<in> sets Y \<Longrightarrow> k (i,x) B = (\<Sum>j. ki i j x B)"
     by metis
  then show ?thesis
    using assms(2) by(auto simp: s_finite_kernel_def' measure_kernel_pair_countble1[OF assms(1)] subprob_kernel_def' space_pair_measure intro!: exI[where x="\<lambda>j (i,x). ki i j x"] measurable_pair_measure_countable1 assms(1))
qed

lemma s_finite_kernel_s_finite_kernel:
  assumes "\<And>i. s_finite_kernel X Y (ki i)" "\<And>x. x \<in> space X \<Longrightarrow> sets (k x) = sets Y" "\<And>x A. x \<in> space X \<Longrightarrow> A \<in> sets Y \<Longrightarrow> emeasure (k x) A = (\<Sum>i. (ki i) x A)"
  shows "s_finite_kernel X Y k"
proof -
  have "\<exists>kij. (\<forall>j. subprob_kernel X Y (kij j)) \<and> (\<forall>x A. x \<in> space X \<longrightarrow> ki i x A = (\<Sum>j. kij j x A))" for i
    using s_finite_kernel.s_finite_kernels[OF assms(1)[of i]] by metis
  then obtain kij where kij:"\<And>i j. subprob_kernel X Y (kij i j)" "\<And>i x A. x \<in> space X \<Longrightarrow> ki i x A = (\<Sum>j. kij i j x A)"
    by metis
  define ki' where "ki' \<equiv> (\<lambda>n. case_prod kij (prod_decode n))"
  have emeasure_sumk':"emeasure (k x) A = (\<Sum>i. emeasure (ki' i x) A)" if x:"x \<in> space X" and A: "A \<in> sets Y" for x A
    by(auto simp: assms(3)[OF that] kij(2)[OF x] ki'_def intro!: suminf_ennreal_2dimen[symmetric])
  have "subprob_kernel X Y (ki' i)" for i
    using kij(1) by(auto simp: ki'_def split_beta')
  thus ?thesis
    by(auto simp: s_finite_kernel_def' measure_kernel_def assms(2) s_finite_kernel_axioms_def emeasure_sumk' intro!: exI[where x=ki'])
qed

lemma s_finite_kernel_finite_sumI:
  assumes [measurable_cong]: "\<And>x. x \<in> space X \<Longrightarrow> sets (\<kappa> x) = sets Y"
      and "\<And>i. i \<in> I \<Longrightarrow> subprob_kernel X Y (ki i)" "\<And>x A. x \<in> space X \<Longrightarrow> A \<in> sets Y \<Longrightarrow> emeasure (\<kappa> x) A = (\<Sum>i\<in>I. ki i x A)" "finite I" "I \<noteq> {}"
    shows "s_finite_kernel X Y \<kappa>"
proof -
  consider "space X = {}" | "space X \<noteq> {}" by auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      by(rule s_finite_kernel_empty_trivial)
  next
    case 2
    then have Y:"space Y \<noteq> {}"
      using assms measure_kernel.Y_not_empty by (fastforce simp: subprob_kernel_def)
    define ki' where "ki' \<equiv> (\<lambda>i x. if i < card I then ki (from_nat_into I i) x else null_measure Y)"
    have [simp]:"subprob_kernel X Y (ki' i)" for i
      by(cases "i < card I") (simp add: ki'_def from_nat_into assms, auto simp: ki'_def subprob_kernel_def measure_kernel_def subprob_kernel_axioms_def Y intro!: subprob_spaceI)
    have [simp]: "(\<Sum>i. emeasure (ki' i x) A) = (\<Sum>i\<in>I. ki i x A)" for x A
      using suminf_finite[of "{..<card I}" "\<lambda>i. (if i < card I then ki (from_nat_into I i) x else null_measure Y) A"]
      by(auto simp: sum.reindex_bij_betw[OF bij_betw_from_nat_into_finite[OF assms(4)],symmetric] ki'_def)
    have [measurable]:"B \<in> sets Y \<Longrightarrow> (\<lambda>x. emeasure (\<kappa> x) B) \<in> borel_measurable X" for B
      using assms(2) by(auto simp: assms(3) subprob_kernel_def' cong: measurable_cong)
    show ?thesis
      by (auto simp: s_finite_kernel_def' intro!: exI[where x=ki'] assms)
  qed
qed

text \<open> Each kernel does not need to be bounded by a uniform upper-bound in the definition of @{term s_finite_kernel} \<close>
lemma s_finite_kernel_finite_bounded_sum:
  assumes [measurable_cong]: "\<And>x. x \<in> space X \<Longrightarrow> sets (\<kappa> x) = sets Y"
      and "\<And>i. measure_kernel X Y (ki i)" "\<And>x A. x \<in> space X \<Longrightarrow> A \<in> sets Y \<Longrightarrow> \<kappa> x A = (\<Sum>i. ki i x A)" "\<And>i x. x \<in> space X \<Longrightarrow> ki i x (space Y) < \<infinity>"
    shows "s_finite_kernel X Y \<kappa>"
proof(cases "space X = {}")
  case True
  then show ?thesis
    by(simp add: s_finite_kernel_empty_trivial)
next
  case X:False
  then have Y: "space Y \<noteq> {}"
    using assms(2)[of 0] by(simp add: measure_kernel_def)
  show ?thesis
  proof(rule s_finite_kernel_s_finite_kernel[where ki=ki,OF _ assms(1) assms(3)])
    fix i
    interpret m: measure_kernel X Y "ki i" by fact
    define kij where "kij \<equiv> (\<lambda>(j :: nat) x. if j < nat \<lceil>enn2real (ki i x (space Y))\<rceil> then scale_measure (1 / ennreal \<lceil>enn2real (ki i x (space Y))\<rceil>) (ki i x) else sigma (space Y) (sets Y))"
    have sets_kij: "sets (kij j x) = sets Y" if "x \<in> space X" for j x
      by(auto simp: m.kernel_sets[OF that] kij_def)
    have emeasure_kij: "ki i x A = (\<Sum>j. kij j x A)" if "x \<in> space X" "A \<in> sets Y" for x A
    proof -
      have "(\<Sum>j. kij j x A) = (\<Sum>j< nat \<lceil>enn2real (ki i x (space Y))\<rceil>. scale_measure (1 / ennreal \<lceil>enn2real (ki i x (space Y))\<rceil>) (ki i x) A)"
        by(simp add: suminf_offset[where i="nat \<lceil>enn2real (ki i x (space Y))\<rceil>" and f="\<lambda>j. kij j x A"], simp add: kij_def emeasure_sigma)
      also have "... = ki i x A"
      proof(cases "nat \<lceil>enn2real (ki i x (space Y))\<rceil>")
        case 0
        then show ?thesis
          by simp (metis assms(4) emeasure_eq_0 enn2real_le ennreal_0 infinity_ennreal_def le_zero_eq linorder_not_le m.kernel_space nle_le sets.sets_into_space sets.top that)
      next
        case (Suc n')
        then have "ennreal (real_of_int \<lceil>enn2real (emeasure (ki i x) (space Y))\<rceil>) > 0"
          using ennreal_less_zero_iff by fastforce
        with assms(4)[OF that(1),of i] have [simp]: "of_nat (nat \<lceil>enn2real (emeasure (ki i x) (space Y))\<rceil>) / ennreal (real_of_int \<lceil>enn2real (emeasure (ki i x) (space Y))\<rceil>) = 1"
          by (simp add: ennreal_eq_0_iff ennreal_of_nat_eq_real_of_nat)
        show ?thesis
          by(simp add: mult.assoc[symmetric] ennreal_times_divide)
      qed
      finally show ?thesis by simp
    qed
    have sk: "subprob_kernel X Y (kij j)" for j
    proof -
      {
        fix B
        assume [measurable]:"B \<in> sets Y"
        have "emeasure (kij j x) B = (if j < nat \<lceil>enn2real (ki i x (space Y))\<rceil> then (ki i x) B / ennreal (real_of_int \<lceil>enn2real (ki i x (space Y))\<rceil>) else 0)" if "x \<in> space X" for x
          by(auto simp: kij_def emeasure_sigma divide_ennreal_def mult.commute)
        hence " (\<lambda>x. emeasure (kij j x) B) \<in> borel_measurable X"
          by(auto simp: kij_def cong: measurable_cong)
      }
      moreover {
        fix x
        assume x:"x \<in> space X"
        have "subprob_space (kij j x)"
        proof -
          have "emeasure (kij j x) (space Y) \<le> 1"
          proof -
            {
              assume 1:"j < nat \<lceil>enn2real (emeasure (ki i x) (space Y))\<rceil>"
              then have "emeasure (ki i x) (space Y) > 0"
                by (metis ceiling_zero enn2real_0 nat_zero_as_int not_gr_zero not_less_zero)
              with assms(4)[OF x] have [simp]:"emeasure (ki i x) (space Y) / emeasure (ki i x) (space Y) = 1"
                by simp
              have [simp]:"emeasure (ki i x) (space Y) / ennreal (real_of_int \<lceil>enn2real (ki i x (space Y))\<rceil>) \<le> 1"
              proof(rule order.trans[where b="emeasure (ki i x) (space Y) / ki i x (space Y)",OF divide_le_posI_ennreal])
                show "0 < ennreal (real_of_int \<lceil>enn2real (ki i x (space Y))\<rceil>)"
                  using 1 assms(4)[OF x] enn2real_positive_iff top.not_eq_extremum by fastforce
              next
                have 1:"ennreal (real_of_int \<lceil>enn2real (ki i x (space Y))\<rceil>) \<ge> ki i x (space Y)"
                  using assms(4)[OF x] enn2real_le by (simp add: linorder_neq_iff)
                have "ennreal (real_of_int \<lceil>enn2real (ki i x (space Y))\<rceil>) / ki i x (space Y) \<ge> 1"
                  by(rule order.trans[OF _ divide_right_mono_ennreal[OF 1,of "ki i x (space Y)"]]) simp
                thus "emeasure (ki i x) (space Y) \<le> ennreal (real_of_int \<lceil>enn2real (ki i x (space Y))\<rceil>) * (emeasure (ki i x) (space Y) / ki i x (space Y))"
                  by (simp add: "1")
              qed simp
              have "1 / ennreal (real_of_int \<lceil>enn2real (emeasure (ki i x) (space Y))\<rceil>) * emeasure (ki i x) (space Y) \<le> 1"
                by (simp add: ennreal_divide_times)
            }
            thus ?thesis
              by(auto simp: kij_def emeasure_sigma)
          qed
          thus ?thesis
            by(auto intro!: subprob_spaceI simp: sets_eq_imp_space_eq[OF sets_kij[OF x,of j]] Y)
        qed
      }
      ultimately show ?thesis
        by(auto simp: subprob_kernel_def measure_kernel_def sets_kij m.Y_not_empty subprob_kernel_axioms_def)
    qed
    show "s_finite_kernel X Y (ki i)"
      by(auto intro!: s_finite_kernel_subI simp: emeasure_kij sk m.kernel_sets)
  qed simp_all
qed

lemma(in measure_kernel) s_finite_kernel_finite_bounded:
  assumes "\<And>x. x \<in> space X \<Longrightarrow> \<kappa> x (space Y) < \<infinity>"
  shows "s_finite_kernel X Y \<kappa>"
proof(cases "space X = {}")
  case True
  then show ?thesis
    by(simp add: s_finite_kernel_empty_trivial)
next
  case False
  then have Y:"space Y \<noteq> {}" by(simp add: Y_not_empty)
  have "measure_kernel X Y (case i of 0 \<Rightarrow> \<kappa> | Suc x \<Rightarrow> \<lambda>x. null_measure Y)" for i
    by(cases i,auto simp: measure_kernel_axioms) (auto simp: measure_kernel_def Y)
  moreover have "\<kappa> x A = (\<Sum>i. emeasure ((case i of 0 \<Rightarrow> \<kappa> | Suc x \<Rightarrow> \<lambda>x. null_measure Y) x) A)" for x A
    by(simp add: suminf_offset[where i="Suc 0"])
  moreover have "x \<in> space X \<Longrightarrow> emeasure ((case i of 0 \<Rightarrow> \<kappa> | Suc x \<Rightarrow> \<lambda>x. null_measure Y) x) (space Y) < \<top>" for x i
    by(cases i) (use assms in auto)
  ultimately show ?thesis
    by(auto intro!: s_finite_kernel_finite_bounded_sum[where ki="\<lambda>i. case i of 0 \<Rightarrow> \<kappa> | Suc _ \<Rightarrow> (\<lambda>x. null_measure Y)" and X=X and Y=Y] simp: kernel_sets)
qed

lemma(in s_finite_kernel) density_s_finite_kernel:
  assumes f[measurable]: "case_prod f \<in> X \<Otimes>\<^sub>M Y \<rightarrow>\<^sub>M borel"
  shows "s_finite_kernel X Y (\<lambda>x. density (\<kappa> x) (f x))"
proof(cases "space X = {}")
  case True
  then show ?thesis
    by(simp add: s_finite_kernel_empty_trivial)
next
  case False
  note Y = Y_not_empty[OF this]
  obtain ki' where ki': "\<And>i. subprob_kernel X Y (ki' i)" "\<And>x A. x \<in> space X \<Longrightarrow> \<kappa> x A = (\<Sum>i. ki' i x A)"
    by(metis s_finite_kernels)
  hence sets_ki'[measurable_cong]:"\<And>x i. x \<in> space X \<Longrightarrow> sets (ki' i x) = sets Y"
    by(auto simp: subprob_kernel_def measure_kernel_def)
  define ki where "ki \<equiv> (\<lambda>i x. density (ki' i x) (f x))"
  have sets_ki: "x \<in> space X \<Longrightarrow> sets (ki i x) = sets Y" for i x
    using ki'(1) by(auto simp: subprob_kernel_def measure_kernel_def ki_def)
  have emeasure_k:"density (\<kappa> x) (f x) A = (\<Sum>i. ki i x A)" if x:"x \<in> space X" and A[measurable]:"A \<in> sets Y" for x A
    using kernel_sets[OF x] x ki'(1) sets_ki'[OF x] by(auto simp: emeasure_density nn_integral_measure_suminf[OF _ ki'(2),of x] ki_def)
  show ?thesis
  proof(rule s_finite_kernel_s_finite_kernel[where ki="ki",OF _ _ emeasure_k])
    fix i
    note nn_integral_measurable_subprob_algebra2[OF _ ki'(1)[of i,simplified subprob_kernel_def'],measurable]
    define kij where "kij \<equiv> (\<lambda>j x. if j = 0 then density (ki' i x) (\<lambda>y. \<infinity> * indicator {y\<in>space Y. f x y = \<infinity>} y)
                                    else if j = (Suc 0) then density (ki' i x) (\<lambda>y. f x y * indicator {y\<in>space Y. f x y < \<infinity>} y)
                                    else null_measure Y)"
    have emeasure_kij: "ki i x A = (\<Sum>j. kij j x A)" (is "?lhs = ?rhs") if x:"x \<in> space X" and [measurable]: "A \<in> sets Y" for x A
    proof -
      have "?lhs = (\<integral>\<^sup>+y\<in>A. f x y \<partial>ki' i x)"
        using sets_ki[OF x,of i] x by(auto simp: ki_def emeasure_density)
      also have "... = (\<integral>\<^sup>+y. (\<infinity> * indicator {y \<in> space Y. f x y = \<infinity>} y * indicator A y + f x y * indicator {y \<in> space Y. f x y < \<infinity>} y * indicator A y) \<partial>ki' i x)"
        by(auto intro!: nn_integral_cong simp: sets_eq_imp_space_eq[OF sets_ki'[OF x]] indicator_def) (simp add: top.not_eq_extremum)
      also have "... = density (ki' i x) (\<lambda>y. \<infinity> * indicator {y\<in>space Y. f x y = \<infinity>} y) A + density (ki' i x) (\<lambda>y. f x y * indicator {y\<in>space Y. f x y < \<infinity>} y) A"
        using sets_ki[OF x,of i] x by(auto simp: ki_def emeasure_density nn_integral_add)
      also have "... = ?rhs"
        using suminf_finite[of "{..<Suc (Suc 0)}" "\<lambda>j. kij j x A"] by(simp add: kij_def)
      finally show ?thesis .
    qed
    have sets_kij[measurable_cong]:"x \<in> space X \<Longrightarrow> sets (kij j x) = sets Y" for j x
      by(auto simp: kij_def sets_ki')
    show "s_finite_kernel X Y (ki i)"
    proof(rule s_finite_kernel_s_finite_kernel[where ki=kij,OF _ _ emeasure_kij])
      fix j
      consider "j = 0" | "j = Suc 0" | "j \<noteq> 0" "j \<noteq> Suc 0" by auto
      then show "s_finite_kernel X Y (kij j)"
      proof cases
        case 1
        have emeasure_ki: "emeasure (kij j x) A = (\<Sum>j. emeasure (density (ki' i x) (indicator {y \<in> space Y. f x y = \<top>})) A)" if x:"x \<in> space X" and [measurable]: "A \<in> sets Y" for x A
          using sets_ki'[OF x] x by(auto simp: 1 kij_def emeasure_density nn_integral_suminf[symmetric] indicator_def intro!: nn_integral_cong) (simp add: nn_integral_count_space_nat[symmetric])
        have [simp]:"subprob_kernel X Y (\<lambda>x. density (ki' i x) (indicator {y \<in> space Y. f x y = \<top>}))"
        proof -
          have [simp]:"x \<in> space X \<Longrightarrow> set_nn_integral (ki' i x) (space Y) (indicator {y \<in> space Y. f x y = \<top>}) \<le> 1" for x
            by(rule order.trans[OF nn_integral_mono[where v="\<lambda>x. 1"]],insert ki'(1)[of i]) (auto simp: indicator_def subprob_kernel_def subprob_kernel_axioms_def intro!: subprob_space.emeasure_space_le_1)
          show ?thesis
            by(auto simp: subprob_kernel_def measure_kernel_def emeasure_density subprob_kernel_axioms_def sets_ki' sets_eq_imp_space_eq[OF sets_ki'] Y cong: measurable_cong intro!: subprob_spaceI)
        qed
        show ?thesis
          by (auto simp: s_finite_kernel_def' sets_kij intro!: exI[where x="\<lambda>k x. density (ki' i x) (indicator {y \<in> space Y. f x y = \<top>})"] simp: emeasure_ki )
      next
        case j:2
        have emeasure_ki: "emeasure (kij j x) A = (\<Sum>k. density (ki' i x) (\<lambda>y. f x y * indicator {y \<in> space Y. of_nat k \<le> f x y \<and> f x y < 1 + of_nat k} y) A)" if x:"x \<in> space X" and [measurable]:"A \<in> sets Y" for x A
        proof -
          have [simp]: "f x y * indicator {y \<in> space Y. f x y < \<top>} y * indicator A y = f x y * (\<Sum>k. indicator {y \<in> space Y. of_nat k \<le> f x y \<and> f x y < 1 + of_nat k} y) * indicator A y" if y:"y \<in> space Y" for y
          proof(cases "f x y < \<top>")
            case f:True
            define l where "l \<equiv> floor (enn2real (f x y))"
            have "nat l \<le> enn2real (f x y)" "enn2real (f x y) < 1 + nat l"
              by (simp_all add: l_def) linarith
            with y have l:"of_nat (nat l) \<le> f x y" "f x y < 1 + of_nat (nat l)"
              using Orderings.order_eq_iff enn2real_positive_iff ennreal_enn2real_if ennreal_of_nat_eq_real_of_nat linorder_not_le of_nat_0_le_iff f by fastforce+
            then have "(\<Sum>j. indicator {y \<in> space Y. of_nat j \<le> f x y \<and> f x y < 1 + of_nat j} y :: ennreal) = (\<Sum>j. if j = nat l then 1 else 0)"
              by(auto intro!: suminf_cong simp: indicator_def y) (metis Suc_leI linorder_neqE_nat linorder_not_less of_nat_Suc of_nat_le_iff order_trans)
            also have "... = 1"
              using suminf_finite[where N="{nat l}" and f="\<lambda>j. if j = nat l then 1 else (0 :: ennreal)"] by simp
            finally show ?thesis
              by(auto, insert f) (auto simp: indicator_def)
          qed(use top.not_eq_extremum in fastforce)
          show ?thesis
            using sets_ki[OF x] sets_ki'[OF x] x by(auto simp: kij_def j emeasure_density nn_integral_suminf[symmetric] sets_eq_imp_space_eq[OF sets_ki'[OF x]] intro!: nn_integral_cong)
        qed
        show ?thesis
        proof(rule s_finite_kernel_finite_bounded_sum[OF sets_kij _ emeasure_ki])
          fix k
          show "measure_kernel X Y (\<lambda>x. density (ki' i x) (\<lambda>y. f x y * indicator {y \<in> space Y. of_nat k \<le> f x y \<and> f x y < 1 + of_nat k} y))"
            using sets_ki'[of _ i] by(auto simp: measure_kernel_def emeasure_density Y cong: measurable_cong)
        next
          fix k x
          assume x:"x \<in>space X"
          have "emeasure (density (ki' i x) (\<lambda>y. f x y * indicator {y \<in> space Y. of_nat k \<le> f x y \<and> f x y < 1 + of_nat k} y)) (space Y) \<le> 1 + of_nat k"
            by(auto simp: emeasure_density x,rule order.trans[OF nn_integral_mono[where v="\<lambda>x. 1 + of_nat k"]]) (insert subprob_kernel.subprob_space[OF ki'(1)[of i] x], auto simp: indicator_def subprob_kernel_def subprob_kernel_axioms_def  sets_eq_imp_space_eq[OF sets_ki'[OF x]] intro!: mult_mono[where d="1 :: ennreal",OF order.refl,simplified])
          also have "... < \<infinity>"
            by (simp add: of_nat_less_top)
          finally show "emeasure (density (ki' i x) (\<lambda>y. f x y * indicator {y \<in> space Y. of_nat k \<le> f x y \<and> f x y < 1 + of_nat k} y)) (space Y) < \<infinity>" .
        qed auto
      next
        case 3
        then show ?thesis
          by(auto simp: kij_def s_finite_kernel_cong_sets[of X X Y,OF _ sets_null_measure[symmetric]] Y intro!: s_finite_measure.s_finite_kernel_const finite_measure.s_finite_measure_finite_measure finite_measureI)
      qed
    qed(auto simp: sets_ki)
  qed(auto simp: kernel_sets)
qed

lemma(in s_finite_kernel) nn_integral_measurable_f:
  assumes [measurable]:"(\<lambda>(x,y). f x y) \<in> borel_measurable (X \<Otimes>\<^sub>M Y)"
  shows "(\<lambda>x. \<integral>\<^sup>+y. f x y \<partial>(\<kappa> x)) \<in> borel_measurable X"
proof -
  obtain \<kappa>i where \<kappa>i:"\<And>i. subprob_kernel X Y (\<kappa>i i)" "\<And>x A. x \<in> space X \<Longrightarrow> \<kappa> x A = (\<Sum>i. \<kappa>i i x A)"
    by(metis s_finite_kernels)
  show ?thesis
  proof(rule measurable_cong[THEN iffD2])
    fix x
    assume "x \<in> space X"
    with \<kappa>i show "(\<integral>\<^sup>+ y. f x y \<partial>\<kappa> x) = (\<Sum>i. \<integral>\<^sup>+ y. f x y \<partial>\<kappa>i i x)"
      by(auto intro!: nn_integral_measure_suminf[symmetric] simp: subprob_kernel_def kernel_sets measure_kernel_def)
  next
    show "(\<lambda>x. \<Sum>i. \<integral>\<^sup>+ y. f x y \<partial>\<kappa>i i x) \<in> borel_measurable X"
      using \<kappa>i(1) nn_integral_measurable_subprob_algebra2[OF assms] by(simp add: subprob_kernel_def' )
  qed
qed

lemma(in s_finite_kernel) nn_integral_measurable_f':
  assumes "f \<in> borel_measurable (X \<Otimes>\<^sub>M Y)"
  shows "(\<lambda>x. \<integral>\<^sup>+y. f (x, y) \<partial>(\<kappa> x)) \<in> borel_measurable X"
  using nn_integral_measurable_f[where f="curry f",simplified,OF assms] by simp

lemma(in s_finite_kernel) bind_kernel_s_finite_kernel':
  assumes "s_finite_kernel (X \<Otimes>\<^sub>M Y) Z (case_prod g)"
  shows "s_finite_kernel X Z (\<lambda>x. \<kappa> x \<bind>\<^sub>k g x)"
proof(cases "space X = {}")
  case True
  then show ?thesis
    by (simp add: s_finite_kernel_empty_trivial)
next
  case X:False
  then have Y:"space Y \<noteq> {}"
    by(simp add: Y_not_empty)
  from s_finite_kernels obtain ki where ki:
  "\<And>i. subprob_kernel X Y (ki i)" "\<And>x A. x \<in> space X \<Longrightarrow> \<kappa> x A = (\<Sum>i. ki i x A)"
    by metis
  interpret g:s_finite_kernel "X \<Otimes>\<^sub>M Y" Z "case_prod g" by fact
  from g.s_finite_kernels[simplified space_pair_measure] obtain gi where gi:
  "\<And>i. subprob_kernel (X \<Otimes>\<^sub>M Y) Z (gi i)" "\<And>x y A. x \<in> space X \<Longrightarrow> y \<in> space Y \<Longrightarrow> g x y A = (\<Sum>i. gi i (x,y) A)"
    by auto metis
  define kgi where "kgi = (\<lambda>i x. case prod_decode i of (i,j) \<Rightarrow> (ki j x \<bind> curry (gi i) x))"
  have emeasure:"emeasure (\<kappa> x \<bind>\<^sub>k g x) A = (\<Sum>i. emeasure (kgi i x) A)" (is "?lhs = ?rhs") if x:"x \<in> space X" and A:"A \<in> sets Z" for x A
  proof -
    interpret gx: s_finite_kernel Y Z "g x"
      using g.comp_measurable[OF measurable_Pair1'[OF x]] by auto
    have "?lhs = (\<integral>\<^sup>+ y. g x y A \<partial>\<kappa> x)"
      using gx.emeasure_bind_kernel[OF kernel_sets[OF x] A]
      by(auto simp: sets_eq_imp_space_eq[OF kernel_sets[OF x]] Y)
    also have "... = (\<integral>\<^sup>+ y. (\<Sum>i. gi i (x, y) A) \<partial>\<kappa> x)"
      by(auto intro!: nn_integral_cong simp: sets_eq_imp_space_eq[OF kernel_sets[OF x]] gi(2)[OF x])
    also have "... = (\<Sum>i. \<integral>\<^sup>+ y. gi i (x, y) A \<partial>\<kappa> x)"
      using gi(1) x A by(auto intro!: nn_integral_suminf simp: subprob_kernel_def')
    also have "... = (\<Sum>i. (\<Sum>j. \<integral>\<^sup>+ y. gi i (x, y) A \<partial>ki j x))"
      by(rule suminf_cong, rule nn_integral_measure_suminf[symmetric], insert kernel_sets[OF x] ki gi(1) x A)
        (auto simp: subprob_kernel_def measure_kernel_def measurable_cong_sets[OF sets_pair_measure_cong[OF refl kernel_sets[OF x]]] intro!: measurable_Pair2[OF _ x])
    also have "... = (\<Sum>i. (\<Sum>j. emeasure (ki j x \<bind> (curry (gi i) x)) A))"
      using sets_eq_imp_space_eq[of "ki _ x" Y] ki(1) x gi(1) measurable_cong_sets[of _ _ "subprob_algebra Z" "subprob_algebra Z", OF sets_pair_measure_cong[of X X Y "ki _ x"]]
      by(auto intro!: suminf_cong emeasure_bind[OF _ _ A,symmetric] measurable_Pair2[OF _ x] simp: curry_def subprob_kernel_def[of X] subprob_kernel_def'[of "X \<Otimes>\<^sub>M Y"]  measure_kernel_def Y)
    also have "... = ?rhs"
      unfolding kgi_def by(rule suminf_ennreal_2dimen[symmetric]) (simp add: curry_def)
    finally show ?thesis .
  qed
  have sets: "sets (\<kappa> x \<bind>\<^sub>k g x) = sets Z" if x:"x \<in> space X" for x
  proof -
    interpret gx: s_finite_kernel Y Z "g x"
      using g.comp_measurable[OF measurable_Pair1'[OF x]] by auto
    show ?thesis
      by(simp add: gx.sets_bind_kernel[OF _ kernel_sets[OF x]] Y)
  qed
  have sk:"subprob_kernel X Z (kgi i)" for i
    using ki(1)[of "snd (prod_decode i)"] gi(1)[of "fst (prod_decode i)"]
    by(auto simp: subprob_kernel_def' kgi_def split_beta' curry_def)
  show ?thesis
    using sk by(auto simp: s_finite_kernel_def' emeasure sets subprob_kernel_def' intro!: exI[where x=kgi] measurable_cong[where g="\<lambda>x. \<Sum>i. emeasure (kgi i x) _" and f="\<lambda>x. emeasure (\<kappa> x \<bind>\<^sub>k g x) _",THEN iffD2])
qed

corollary(in s_finite_kernel) bind_kernel_s_finite_kernel:
  assumes "s_finite_kernel Y Z k'"
  shows "s_finite_kernel X Z (\<lambda>x. \<kappa> x \<bind>\<^sub>k k')"
  by(auto intro!: bind_kernel_s_finite_kernel' s_finite_kernel.comp_measurable[OF assms measurable_snd] simp: split_beta')

lemma(in s_finite_kernel) nn_integral_bind_kernel:
  assumes "f \<in> borel_measurable Y" "sets \<mu> = sets X"
  shows "(\<integral>\<^sup>+ y. f y \<partial>(\<mu> \<bind>\<^sub>k \<kappa>)) = (\<integral>\<^sup>+x. (\<integral>\<^sup>+ y. f y \<partial>(\<kappa> x)) \<partial>\<mu>)"
proof(cases "space X = {}")
  case True
  then show ?thesis
    by(simp add: sets_eq_imp_space_eq[OF assms(2)] bind_kernel_def nn_integral_empty)
next
  case X:False
  then have \<mu>:"space \<mu> \<noteq> {}" by(simp add: sets_eq_imp_space_eq[OF assms(2)])
  note 1[measurable_cong] = assms(2) sets_bind_kernel[OF X assms(2)]
  from assms(1) show ?thesis
  proof induction
    case ih:(cong f g)
    have "(\<integral>\<^sup>+ y. f y \<partial>(\<mu> \<bind>\<^sub>k \<kappa>)) = (\<integral>\<^sup>+ y. g y \<partial>(\<mu> \<bind>\<^sub>k \<kappa>))" "(\<integral>\<^sup>+ x. integral\<^sup>N (\<kappa> x) f \<partial>\<mu>) = (\<integral>\<^sup>+ x. integral\<^sup>N (\<kappa> x) g \<partial>\<mu>)"
      by(auto intro!: nn_integral_cong simp: sets_eq_imp_space_eq[OF 1(2)] sets_eq_imp_space_eq[OF assms(2)] sets_eq_imp_space_eq[OF kernel_sets] ih(3))
    then show ?case
      by(simp add: ih)
  next
    case (set A)
    then show ?case
      by(auto simp: emeasure_bind_kernel[OF 1(1) _ X] sets_eq_imp_space_eq[OF 1(1)] intro!: nn_integral_cong)
  next
    case ih:(mult u c)
    then have "(\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. c * u y \<partial>\<kappa> x \<partial>\<mu>) = (\<integral>\<^sup>+ x. c * \<integral>\<^sup>+ y. u y \<partial>\<kappa> x \<partial>\<mu>)"
      by(auto intro!: nn_integral_cong nn_integral_cmult simp: sets_eq_imp_space_eq[OF 1(1)])
    with ih nn_integral_measurable_f[of "\<lambda>_ y. u y"] show ?case
      by(auto simp: nn_integral_cmult intro!: nn_integral_cong)
  next
    case ih:(add u v)
    then have "(\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. v y + u y \<partial>\<kappa> x \<partial>\<mu>) = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. v y \<partial>\<kappa> x) + (\<integral>\<^sup>+ y. u y \<partial>\<kappa> x) \<partial>\<mu>)"
      by(auto intro!: nn_integral_cong simp: nn_integral_add sets_eq_imp_space_eq[OF 1(1)])
    with ih nn_integral_measurable_f[of "\<lambda>_ y. u y"] nn_integral_measurable_f[of "\<lambda>_ y. v y"] show ?case
      by(simp add: nn_integral_add)
  next
    case ih[measurable]:(seq U)
    show ?case (is "?lhs = ?rhs")
    proof -
      have "?lhs = ((\<Squnion>i. integral\<^sup>N (\<mu> \<bind>\<^sub>k \<kappa>) (U i)))"
        by(rule nn_integral_monotone_convergence_SUP[of U,simplified SUP_apply[of U UNIV,symmetric]]) (use ih in auto)
      also have "... = (\<Squnion>i. \<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. U i y \<partial>\<kappa> x) \<partial>\<mu>)"
        by(simp add: ih)
      also have "... = (\<integral>\<^sup>+ x. (\<Squnion>i. (\<integral>\<^sup>+ y. U i y \<partial>\<kappa> x)) \<partial>\<mu>)"
      proof(rule nn_integral_monotone_convergence_SUP[symmetric])
        show "incseq (\<lambda>i x. \<integral>\<^sup>+ y. U i y \<partial>\<kappa> x)"
          by standard+ (auto intro!: le_funI nn_integral_mono simp:le_funD[OF incseqD[OF ih(3)]])
      qed(use nn_integral_measurable_f[of "\<lambda>_ y. U _ y"] in simp)
      also have "... = ?rhs"
        by(rule nn_integral_cong, rule nn_integral_monotone_convergence_SUP[of U,simplified SUP_apply[of U UNIV,symmetric],OF ih(3),symmetric]) (auto simp: sets_eq_imp_space_eq[OF 1(1)])
      finally show ?thesis .
    qed
  qed
qed

lemma(in s_finite_kernel) bind_kernel_assoc:
  assumes "s_finite_kernel Y Z k'" "sets \<mu> = sets X"
  shows "\<mu> \<bind>\<^sub>k (\<lambda>x. \<kappa> x \<bind>\<^sub>k k') = \<mu> \<bind>\<^sub>k \<kappa> \<bind>\<^sub>k k'"
proof(cases "space X = {}")
  case X:False
  then have \<mu>: "space \<mu> \<noteq> {}" and Y:"space Y \<noteq> {}"
    by(simp_all add: Y_not_empty sets_eq_imp_space_eq[OF assms(2)])
  interpret k':s_finite_kernel Y Z k' by fact
  interpret k'': s_finite_kernel X Z "\<lambda>x. \<kappa> x \<bind>\<^sub>k k'"
    by(rule bind_kernel_s_finite_kernel[OF assms(1)])
  show ?thesis
  proof(rule measure_eqI)
    fix A
    assume "A \<in> sets (\<mu> \<bind>\<^sub>k (\<lambda>x. \<kappa> x \<bind>\<^sub>k k'))"
    then have A[measurable]: "A \<in> sets Z"
      by(simp add: k''.sets_bind_kernel[OF X assms(2)])
    show "emeasure (\<mu> \<bind>\<^sub>k (\<lambda>x. \<kappa> x \<bind>\<^sub>k k')) A = emeasure (\<mu> \<bind>\<^sub>k \<kappa> \<bind>\<^sub>k k') A" (is "?lhs = ?rhs")
    proof -
      have "?lhs = (\<integral>\<^sup>+ x. emeasure (\<kappa> x \<bind>\<^sub>k k') A \<partial>\<mu>)"
        by(rule k''.emeasure_bind_kernel[OF assms(2) A X])
      also have "... = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. k' y A \<partial>\<kappa> x \<partial>\<mu>)"
        using k'.emeasure_bind_kernel[OF kernel_sets A]
        by(auto intro!: nn_integral_cong simp: sets_eq_imp_space_eq[OF assms(2)] sets_eq_imp_space_eq[OF kernel_sets] Y)
      also have "... = (\<integral>\<^sup>+ y. k' y A \<partial>(\<mu> \<bind>\<^sub>k \<kappa>))"
        by(simp add: nn_integral_bind_kernel[OF k'.emeasure_measurable[OF A] assms(2)])
      also have "... = ?rhs"
        by(simp add: k'.emeasure_bind_kernel[OF sets_bind_kernel[OF X assms(2)] A] sets_eq_imp_space_eq[OF sets_bind_kernel[OF X assms(2)]] Y)
      finally show ?thesis .
    qed
  qed(auto simp: k'.sets_bind_kernel[OF Y sets_bind_kernel[OF X assms(2)]] k''.sets_bind_kernel[OF X assms(2)]) 
qed(simp add: bind_kernel_def sets_eq_imp_space_eq[OF assms(2)])

lemma s_finite_kernel_pair_measure:
  assumes "s_finite_kernel X Y k" and "s_finite_kernel X Z k'"
  shows "s_finite_kernel X (Y \<Otimes>\<^sub>M Z) (\<lambda>x. k x \<Otimes>\<^sub>M k' x)"
proof -
  interpret k: s_finite_kernel X Y k by fact
  interpret k': s_finite_kernel X Z k' by fact
  from k.s_finite_kernels k'.s_finite_kernels obtain ki ki'
    where ki:"\<And>i. subprob_kernel X Y (ki i)" "\<And>x A. x \<in> space X \<Longrightarrow> k x A = (\<Sum>i. ki i x A)"
      and ki':"\<And>i. subprob_kernel X Z (ki' i)" "\<And>x A. x \<in> space X \<Longrightarrow> k' x A = (\<Sum>i. ki' i x A)"
    by metis
  then have 1[measurable_cong]: "\<And>x i. x \<in> space X \<Longrightarrow> sets (ki i x) = sets Y" "\<And>x i. x \<in> space X \<Longrightarrow> sets (ki' i x) = sets Z"
    by(auto simp: subprob_kernel_def measure_kernel_def)
  define kki where "kki \<equiv> (\<lambda>i x. (\<lambda>(j,i). ki i x \<Otimes>\<^sub>M ki' j x) (prod_decode i))"
  have kki1: "\<And>i. subprob_kernel X (Y \<Otimes>\<^sub>M Z) (kki i)"
    using ki(1) ki'(1) by(auto simp: subprob_kernel_def' kki_def split_beta intro!: measurable_pair_measure)
  have kki2: "(k x \<Otimes>\<^sub>M k' x) A = (\<Sum>i. (kki i x) A)" (is "?lhs = ?rhs") if x:"x \<in> space X" and A[measurable]: "A \<in> sets (Y \<Otimes>\<^sub>M Z)" for x A
  proof -
    have "?lhs = (\<integral>\<^sup>+ y. \<integral>\<^sup>+ z. indicator A (y, z) \<partial>k' x \<partial>k x)"
      using x by(simp add: s_finite_measure.emeasure_pair_measure'[OF k'.image_s_finite_measure])
    also have "... = (\<integral>\<^sup>+ y. (\<Sum>j. \<integral>\<^sup>+ z. indicator A (y, z) \<partial>ki' j x) \<partial>k x)"
      using ki' x by(auto intro!: nn_integral_cong nn_integral_measure_suminf[symmetric] simp: sets_eq_imp_space_eq[OF k.kernel_sets[OF x]] subprob_kernel_def measure_kernel_def k'.kernel_sets)
    also have "... = (\<Sum>j. \<integral>\<^sup>+ y. \<integral>\<^sup>+ z. indicator A (y, z) \<partial>ki' j x \<partial>k x)"
      using x by(auto intro!: nn_integral_suminf s_finite_measure.borel_measurable_nn_integral_fst' s_finite_kernel.image_s_finite_measure[OF subprob_kernel.s_finite_kernel_subprob_kernel[OF ki'(1)]])
    also have "... = (\<Sum>j. (\<Sum>i. (\<integral>\<^sup>+ y. \<integral>\<^sup>+ z. indicator A (y, z) \<partial>ki' j x \<partial>ki i x)))"
      using x ki by(auto intro!: suminf_cong nn_integral_measure_suminf[symmetric] s_finite_measure.borel_measurable_nn_integral_fst' simp: k.kernel_sets[OF x] subprob_kernel_def measure_kernel_def s_finite_kernel.image_s_finite_measure[OF subprob_kernel.s_finite_kernel_subprob_kernel[OF ki'(1)]])
    also have "... =  (\<Sum>j. (\<Sum>i. (ki i x \<Otimes>\<^sub>M ki' j x) A))"
      using x by(auto simp: s_finite_measure.emeasure_pair_measure'[OF s_finite_kernel.image_s_finite_measure[OF subprob_kernel.s_finite_kernel_subprob_kernel[OF ki'(1)]]])
    also have "... = ?rhs"
      unfolding kki_def by(rule suminf_ennreal_2dimen[symmetric]) auto
    finally show ?thesis .
  qed
  show ?thesis
  proof
    fix B
    assume [measurable]:"B \<in> sets (Y \<Otimes>\<^sub>M Z)"
    show "(\<lambda>x. emeasure (k x \<Otimes>\<^sub>M k' x) B) \<in> borel_measurable X"
      by(rule measurable_cong[where g="\<lambda>x. \<Sum>i. (kki i x) B",THEN iffD2], insert kki1) (auto simp: subprob_kernel_def' kki2)
  qed(auto intro!: exI[where x=kki] simp: subprob_kernel.finite_kernel kki1 kki2 k.kernel_sets k'.kernel_sets space_pair_measure k.Y_not_empty k'.Y_not_empty)
qed

lemma pair_measure_eq_bind_s_finite:
  assumes "s_finite_measure \<mu>" "s_finite_measure \<nu>"
  shows "\<mu> \<Otimes>\<^sub>M \<nu> = \<mu> \<bind>\<^sub>k (\<lambda>x. \<nu> \<bind>\<^sub>k (\<lambda>y. return (\<mu> \<Otimes>\<^sub>M \<nu>) (x,y)))"
proof -
  consider "space \<mu> = {}" | "space \<nu> = {}" | "space \<mu> \<noteq> {}" "space \<nu> \<noteq> {}"
    by auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      by(auto simp: bind_kernel_def space_pair_measure intro!: space_empty)
  next
    case 2
    then have "\<mu> \<bind>\<^sub>k (\<lambda>x. \<nu> \<bind>\<^sub>k (\<lambda>y. return (\<mu> \<Otimes>\<^sub>M \<nu>) (x, y))) = count_space {}"
      by(auto simp: bind_kernel_def space_empty)
    with 2 show ?thesis
      by(auto simp: space_pair_measure intro!: space_empty)
  next
    case 3
    show ?thesis
    proof(intro measure_eqI sets_bind_kernel[OF _ 3(1),symmetric] sets_bind_kernel[OF _ 3(2)])
      fix A
      assume A[measurable]: "A \<in> sets (\<mu> \<Otimes>\<^sub>M \<nu>)"
      show "emeasure (\<mu> \<Otimes>\<^sub>M \<nu>) A = emeasure (\<mu> \<bind>\<^sub>k (\<lambda>x. \<nu> \<bind>\<^sub>k (\<lambda>y. return (\<mu> \<Otimes>\<^sub>M \<nu>) (x, y)))) A" (is "?lhs = ?rhs")
      proof -
        have "?lhs = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. return (\<mu> \<Otimes>\<^sub>M \<nu>) (x, y) A \<partial>\<nu> \<partial>\<mu>)"
          by(simp add: s_finite_measure.emeasure_pair_measure'[OF assms(2)])
        also have "... = (\<integral>\<^sup>+ x. (\<nu> \<bind>\<^sub>k (\<lambda>y. return (\<mu> \<Otimes>\<^sub>M \<nu>) (x,y))) A \<partial>\<mu>)"
          by(auto intro!: nn_integral_cong measure_kernel.emeasure_bind_kernel[OF _ _ A 3(2),symmetric] prob_kernel.axioms(1) simp: prob_kernel_def' simp del: emeasure_return)
        also have "... = ?rhs"
          by(auto intro!: measure_kernel.emeasure_bind_kernel[OF _ _ A 3(1),symmetric] s_finite_kernel.axioms(1) s_finite_kernel.bind_kernel_s_finite_kernel'[where Y=\<nu>] s_finite_measure.s_finite_kernel_const[OF assms(2) 3(2)] prob_kernel.s_finite_kernel_prob_kernel[of "\<mu> \<Otimes>\<^sub>M \<nu>"] simp: prob_kernel_def')
        finally show ?thesis .
      qed
    qed simp
  qed
qed

lemma bind_kernel_rotate_return:
  assumes "s_finite_measure \<mu>" "s_finite_measure \<nu>"
  shows "\<mu> \<bind>\<^sub>k (\<lambda>x. \<nu> \<bind>\<^sub>k (\<lambda>y. return (\<mu> \<Otimes>\<^sub>M \<nu>) (x,y))) = \<nu> \<bind>\<^sub>k (\<lambda>y. \<mu> \<bind>\<^sub>k (\<lambda>x. return (\<mu> \<Otimes>\<^sub>M \<nu>) (x,y)))"
proof -
  consider "space \<mu> = {}" | "space \<nu> = {}" | "space \<mu> \<noteq> {}" "space \<nu> \<noteq> {}"
    by auto
  then show ?thesis
  proof cases
    case 1
    then have "\<nu> \<bind>\<^sub>k (\<lambda>y. \<mu> \<bind>\<^sub>k (\<lambda>x. return (\<mu> \<Otimes>\<^sub>M \<nu>) (x,y))) = count_space {}"
      by(auto simp: bind_kernel_def space_empty)
    then show ?thesis
      by(auto simp: bind_kernel_def space_pair_measure 1 intro!: space_empty)
  next
    case 2
    then have "\<mu> \<bind>\<^sub>k (\<lambda>x. \<nu> \<bind>\<^sub>k (\<lambda>y. return (\<mu> \<Otimes>\<^sub>M \<nu>) (x, y))) = count_space {}"
      by(auto simp: bind_kernel_def space_empty)
    with 2 show ?thesis
      by(auto simp: space_pair_measure bind_kernel_def intro!: space_empty)
  next
    case 3
    show ?thesis
      unfolding pair_measure_eq_bind_s_finite[OF assms,symmetric]
    proof(intro measure_eqI)
      fix A
      assume A[measurable]:"A \<in> sets (\<mu> \<Otimes>\<^sub>M \<nu>)"
      show "emeasure (\<mu> \<Otimes>\<^sub>M \<nu>) A = emeasure (\<nu> \<bind>\<^sub>k (\<lambda>y. \<mu> \<bind>\<^sub>k (\<lambda>x. return (\<mu> \<Otimes>\<^sub>M \<nu>) (x, y)))) A" (is "?lhs = ?rhs")
      proof -
        have "?lhs = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator A (x, y) \<partial>\<nu> \<partial>\<mu>)"
          by(rule s_finite_measure.emeasure_pair_measure'[OF assms(2) A])
        also have "... = (\<integral>\<^sup>+ y. \<integral>\<^sup>+ x. return (\<mu> \<Otimes>\<^sub>M \<nu>) (x, y) A \<partial>\<mu> \<partial>\<nu>)"
          by(simp add: nn_integral_snd'[OF assms] s_finite_measure.nn_integral_fst'[OF assms(2)])
        also have "... = (\<integral>\<^sup>+ y. (\<mu> \<bind>\<^sub>k (\<lambda>x. return (\<mu> \<Otimes>\<^sub>M \<nu>) (x, y))) A \<partial>\<nu>)"
          by(auto intro!: nn_integral_cong measure_kernel.emeasure_bind_kernel[OF _ _  A 3(1),symmetric] prob_kernel.axioms(1) simp add: prob_kernel_def' simp del: emeasure_return)
        also have "... = ?rhs"
          by(auto intro!: measure_kernel.emeasure_bind_kernel[OF _ _  A 3(2),symmetric] s_finite_kernel.axioms(1) s_finite_kernel.bind_kernel_s_finite_kernel'[where Y=\<mu>] s_finite_measure.s_finite_kernel_const[OF assms(1) 3(1)] prob_kernel.s_finite_kernel_prob_kernel[of "\<nu> \<Otimes>\<^sub>M \<mu>"] simp: prob_kernel_def')
        finally show ?thesis .
      qed
    qed(auto intro!: sets_bind_kernel[OF _ 3(2),symmetric] sets_bind_kernel[OF _ 3(1)])
  qed
qed

lemma bind_kernel_rotate':
  assumes "s_finite_measure \<mu>" "s_finite_measure \<nu>" "s_finite_kernel (\<mu> \<Otimes>\<^sub>M \<nu>) Z (case_prod f)"
  shows "\<mu> \<bind>\<^sub>k (\<lambda>x. \<nu> \<bind>\<^sub>k (\<lambda>y. f x y)) = \<nu> \<bind>\<^sub>k (\<lambda>y. \<mu> \<bind>\<^sub>k (\<lambda>x. f x y))" (is "?lhs = ?rhs")
proof -
  interpret sk: s_finite_kernel "\<mu> \<Otimes>\<^sub>M \<nu>" Z "case_prod f" by fact
  consider "space \<mu> = {}" | "space \<nu> = {}" | "space \<mu> \<noteq> {}" "space \<nu> \<noteq> {}"
    by auto
  then show ?thesis
  proof cases
    case 1
    then have "?rhs = count_space {}"
      by(auto simp: bind_kernel_def space_empty)
    then show ?thesis
      by(auto simp: bind_kernel_def space_pair_measure 1 intro!: space_empty)
  next
    case 2
    then show ?thesis
      by(auto simp: space_pair_measure bind_kernel_def intro!: space_empty)
  next
    case 3
    show ?thesis
    proof -
      have "?lhs = \<mu> \<bind>\<^sub>k (\<lambda>x. \<nu> \<bind>\<^sub>k (\<lambda>y. return (\<mu> \<Otimes>\<^sub>M \<nu>) (x, y)) \<bind>\<^sub>k case_prod f)"
        by(auto intro!: bind_kernel_cong_All simp: s_finite_kernel.bind_kernel_assoc[OF prob_kernel.s_finite_kernel_prob_kernel assms(3) refl,of \<nu> "\<lambda>y. return (\<mu> \<Otimes>\<^sub>M \<nu>) (_, y)",simplified prob_kernel_def',symmetric] sk.bind_kernel_return space_pair_measure)
      also have "... = \<mu> \<bind>\<^sub>k (\<lambda>x. \<nu> \<bind>\<^sub>k (\<lambda>y. return (\<mu> \<Otimes>\<^sub>M \<nu>) (x,y))) \<bind>\<^sub>k (case_prod f)"
        by(auto simp: s_finite_kernel.bind_kernel_assoc[OF s_finite_kernel.bind_kernel_s_finite_kernel'[OF s_finite_measure.s_finite_kernel_const[OF assms(2) 3(2),of \<mu>] prob_kernel.s_finite_kernel_prob_kernel,of "\<mu> \<Otimes>\<^sub>M \<nu>" "\<lambda>x y. return (\<mu> \<Otimes>\<^sub>M \<nu>) (x,y)",simplified] assms(3) refl, simplified prob_kernel_def',symmetric])
      also have "... = \<nu> \<bind>\<^sub>k (\<lambda>y. \<mu> \<bind>\<^sub>k (\<lambda>x. return (\<mu> \<Otimes>\<^sub>M \<nu>) (x,y))) \<bind>\<^sub>k (case_prod f)"
        by(simp add: bind_kernel_rotate_return assms)
      also have "... = \<nu> \<bind>\<^sub>k (\<lambda>y. \<mu> \<bind>\<^sub>k (\<lambda>x. return (\<mu> \<Otimes>\<^sub>M \<nu>) (x, y)) \<bind>\<^sub>k case_prod f)"
        by(auto intro!: s_finite_kernel.bind_kernel_assoc[OF _ assms(3),symmetric] s_finite_kernel.bind_kernel_s_finite_kernel'[OF s_finite_measure.s_finite_kernel_const[OF assms(1) 3(1)]] prob_kernel.s_finite_kernel_prob_kernel[of "\<nu> \<Otimes>\<^sub>M \<mu>"] simp: prob_kernel_def')
      also have "... = ?rhs"
        by(auto intro!: bind_kernel_cong_All simp: s_finite_kernel.bind_kernel_assoc[OF prob_kernel.s_finite_kernel_prob_kernel assms(3) refl,of \<mu> "\<lambda>x. return (\<mu> \<Otimes>\<^sub>M \<nu>) (x, _)",simplified prob_kernel_def',symmetric] sk.bind_kernel_return space_pair_measure)
      finally show ?thesis .
    qed
  qed
qed

lemma bind_kernel_rotate:
  assumes "sets \<mu> = sets X" and "sets \<nu> = sets Y"
      and "s_finite_measure \<mu>" "s_finite_measure \<nu>" "s_finite_kernel (X \<Otimes>\<^sub>M Y) Z (\<lambda>(x,y). f x y)"
    shows "\<mu> \<bind>\<^sub>k (\<lambda>x. \<nu> \<bind>\<^sub>k (\<lambda>y. f x y)) = \<nu> \<bind>\<^sub>k (\<lambda>y. \<mu> \<bind>\<^sub>k (\<lambda>x. f x y))"
  by(auto intro!: bind_kernel_rotate' assms simp: s_finite_kernel_cong_sets[OF sets_pair_measure_cong[OF assms(1,2)]])

lemma(in s_finite_kernel) emeasure_measurable':
  assumes A[measurable]: "(SIGMA x:space X. A x) \<in> sets (X \<Otimes>\<^sub>M Y)"
  shows "(\<lambda>x. emeasure (\<kappa> x) (A x)) \<in> borel_measurable X"
proof -
  have **: "A x \<in> sets Y" if "x \<in> space X" for x
  proof -
    have "Pair x -` Sigma (space X) A = A x"
      using that by auto
    with sets_Pair1[OF A, of x] show "A x \<in> sets Y"
      by auto
  qed

  have *: "\<And>x. fst x \<in> space X \<Longrightarrow> snd x \<in> A (fst x) \<longleftrightarrow> x \<in> (SIGMA x:space X. A x)"
    by (auto simp: fun_eq_iff)
  have "(\<lambda>(x, y). indicator (A x) y::ennreal) \<in> borel_measurable (X \<Otimes>\<^sub>M Y)"
    by (measurable,subst measurable_cong[OF *]) (auto simp: space_pair_measure)
  then have "(\<lambda>x. integral\<^sup>N (\<kappa> x) (indicator (A x))) \<in> borel_measurable X"
    by(rule nn_integral_measurable_f)
  moreover have "integral\<^sup>N (\<kappa> x) (indicator (A x)) = emeasure (\<kappa> x) (A x)" if "x \<in> space X" for x
    using **[OF that] kernel_sets[OF that] by(auto intro!: nn_integral_indicator)
  ultimately show "(\<lambda>x. emeasure (\<kappa> x) (A x)) \<in> borel_measurable X"
    by(auto cong: measurable_cong)
qed

lemma(in s_finite_kernel) measure_measurable':
  assumes "(SIGMA x:space X. A x) \<in> sets (X \<Otimes>\<^sub>M Y)"
  shows "(\<lambda>x. measure (\<kappa> x) (A x)) \<in> borel_measurable X"
  using emeasure_measurable'[OF assms] by(simp add: measure_def)

lemma(in s_finite_kernel) AE_pred:
  assumes P[measurable]:"Measurable.pred (X \<Otimes>\<^sub>M Y) (case_prod P)"
  shows "Measurable.pred X (\<lambda>x. AE y in \<kappa> x. P x y)"
proof -
  have [measurable]:"Measurable.pred X (\<lambda>x. emeasure (\<kappa> x) {y \<in> space Y. \<not> P x y} = 0)"
  proof(rule pred_eq_const1[where N=borel],rule emeasure_measurable')
   have "(SIGMA x:space X. {y \<in> space Y. \<not> P x y}) = {xy\<in>space (X \<Otimes>\<^sub>M Y). \<not> P (fst xy) (snd xy)}"
      by (auto simp: space_pair_measure)
    also have "... \<in> sets (X \<Otimes>\<^sub>M Y)"
      by simp
    finally show "(SIGMA x:space X. {y \<in> space Y. \<not> P x y}) \<in> sets (X \<Otimes>\<^sub>M Y)" .
  qed simp
  have "{x \<in> space X. almost_everywhere (\<kappa> x) (P x)} = {x \<in> space X. emeasure (\<kappa> x) {y\<in>space Y. \<not> P x y} = 0}"
  proof safe
    fix x
    assume x:"x \<in> space X"
    show "(AE y in \<kappa> x. P x y) \<Longrightarrow> emeasure (\<kappa> x) {y \<in> space Y. \<not> P x y} = 0"
      using emeasure_eq_0_AE[of "\<lambda>y. \<not> P x y" "\<kappa> x"]
      by(simp add: sets_eq_imp_space_eq[OF kernel_sets[OF x]])
    show "emeasure (\<kappa> x) {y \<in> space Y. \<not> P x y} = 0 \<Longrightarrow> almost_everywhere (\<kappa> x) (P x)"
      using x by(auto intro!: AE_I[where N="{y \<in> space Y. \<not> P x y}"] simp: sets_eq_imp_space_eq[OF kernel_sets[OF x]] kernel_sets[OF x])
  qed
  also have "... \<in> sets X"
    by(simp add: pred_def)
  finally show ?thesis
    by(simp add: pred_def)
qed

lemma(in subprob_kernel) integrable_probability_kernel_pred:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes [measurable]:"(\<lambda>(x,y). f x y) \<in> borel_measurable (X \<Otimes>\<^sub>M Y)"
    shows "Measurable.pred X (\<lambda>x. integrable (\<kappa> x) (f x))"
proof(rule measurable_cong[THEN iffD2])
  show "x \<in> space X \<Longrightarrow> integrable (\<kappa> x) (f x) \<longleftrightarrow> (\<integral>\<^sup>+y. norm (f x y) \<partial>(\<kappa> x)) < \<infinity>" for x
    by(auto simp: integrable_iff_bounded)
next
  have "(\<lambda>(x,y). ennreal (norm (f x y))) \<in> borel_measurable (X \<Otimes>\<^sub>M Y)"
    by measurable
  from nn_integral_measurable_f[OF this]
  show "Measurable.pred X (\<lambda>x. (\<integral>\<^sup>+ y. ennreal (norm (f x y)) \<partial>\<kappa> x) < \<infinity>)"
    by simp
qed

corollary integrable_measurable_subprob':
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes [measurable]:"(\<lambda>(x,y). f x y) \<in> borel_measurable (X \<Otimes>\<^sub>M Y)" "k \<in> X \<rightarrow>\<^sub>M subprob_algebra Y"
  shows "Measurable.pred X (\<lambda>x. integrable (k x) (f x))"
  by(auto intro!: subprob_kernel.integrable_probability_kernel_pred[where Y=Y] simp: subprob_kernel_def')

lemma(in subprob_kernel) integrable_probability_kernel_pred':
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes "f \<in> borel_measurable (X \<Otimes>\<^sub>M Y)"
  shows "Measurable.pred X (\<lambda>x. integrable (\<kappa> x) (curry f x))"
  using integrable_probability_kernel_pred[of "curry f"] assms by auto

lemma(in subprob_kernel) lebesgue_integral_measurable_f_subprob:
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes [measurable]:"f \<in> borel_measurable (X \<Otimes>\<^sub>M Y)"
  shows "(\<lambda>x. \<integral>y. f (x,y) \<partial>(\<kappa> x)) \<in> borel_measurable X"
proof -
  from borel_measurable_implies_sequence_metric[OF assms, of 0]
  obtain s where s: "\<And>i. simple_function (X \<Otimes>\<^sub>M Y) (s i)"
    and "\<forall>x\<in>space (X \<Otimes>\<^sub>M Y). (\<lambda>i. s i x) \<longlonglongrightarrow> f x"
    and "\<forall>i. \<forall>x\<in>space (X \<Otimes>\<^sub>M Y). dist (s i x) 0 \<le> 2 * dist (f x) 0"
    by auto
  then have *:
    "\<And>x y. x \<in> space X \<Longrightarrow> y \<in> space Y \<Longrightarrow> (\<lambda>i. s i (x, y)) \<longlonglongrightarrow> f (x,y)"
    "\<And>i x y. x \<in> space X \<Longrightarrow> y \<in> space Y \<Longrightarrow> norm (s i (x, y)) \<le> 2 * norm (f (x, y))"
    by (auto simp: space_pair_measure)

  have [measurable]: "\<And>i. s i \<in> borel_measurable (X \<Otimes>\<^sub>M Y)"
    by (rule borel_measurable_simple_function) fact

  have s':"\<And>i. s i \<in> X \<Otimes>\<^sub>M Y \<rightarrow>\<^sub>M count_space UNIV"
    by (rule measurable_simple_function) fact

  define f' where [abs_def]: "f' i x =
    (if integrable (\<kappa> x) (curry f x) then Bochner_Integration.simple_bochner_integral (\<kappa> x) (\<lambda>y. s i (x, y)) else 0)" for i x

  have eq: "Bochner_Integration.simple_bochner_integral (\<kappa> x) (\<lambda>y. s i (x, y)) =
      (\<Sum>z\<in>s i ` (space X \<times> space Y). measure (\<kappa> x) {y \<in> space (\<kappa> x). s i (x, y) = z} *\<^sub>R z)" if "x \<in> space X" for x i
  proof -
    have [measurable_cong]: "sets (\<kappa> x) = sets Y" and [simp]: "space (\<kappa> x) = space Y"
      using that  by (simp_all add: kernel_sets kernel_space)
    with that show ?thesis
      using s[THEN simple_functionD(1)]
      unfolding simple_bochner_integral_def
      by (intro sum.mono_neutral_cong_left)
         (auto simp: eq_commute space_pair_measure image_iff cong: conj_cong)
  qed

  show ?thesis
  proof (rule borel_measurable_LIMSEQ_metric)
    fix i
    note [measurable] = integrable_probability_kernel_pred'[OF assms]
    have [measurable]:"(SIGMA x:space X. {y \<in> space Y. s i (x, y) = s i (a, b)}) \<in> sets (X \<Otimes>\<^sub>M Y)" for a b
    proof -
      have "(SIGMA x:space X. {y \<in> space Y. s i (x, y) = s i (a, b)}) = space (X \<Otimes>\<^sub>M Y) \<inter> s i -` {s i (a,b)}"
        by(auto simp: space_pair_measure)
      thus ?thesis
        using s'[of i] by simp
    qed
    show "f' i \<in> borel_measurable X"
      by (auto simp : eq kernel_space f'_def cong: measurable_cong if_cong intro!: borel_measurable_sum measurable_If borel_measurable_scaleR measure_measurable')
  next
    fix x
    assume x:"x \<in> space X"
    have "(\<lambda>i. Bochner_Integration.simple_bochner_integral (\<kappa> x) (\<lambda>y. s i (x, y))) \<longlonglongrightarrow> (\<integral>y. f (x,y) \<partial>(\<kappa> x))" if int_f:"integrable (\<kappa> x) (curry f x)"
    proof -
      have int_2f: "integrable (\<kappa> x) (\<lambda>y. 2 * norm (f (x,y)))"
        using int_f by(auto simp: curry_def)
      have "(\<lambda>i. integral\<^sup>L (\<kappa> x) (\<lambda>y. s i (x, y))) \<longlonglongrightarrow> integral\<^sup>L (\<kappa> x) (curry f x)"
      proof (rule integral_dominated_convergence)
        show "curry f x \<in> borel_measurable (\<kappa> x)"
          using int_f by auto
      next
        show "\<And>i. (\<lambda>y. s i (x, y)) \<in> borel_measurable (\<kappa> x)"
          using x kernel_sets by auto
      next
        show "AE xa in \<kappa> x. (\<lambda>i. s i (x, xa)) \<longlonglongrightarrow> curry f x xa"
          using x *(1) kernel_space by(auto simp: curry_def)
      next
        show "\<And>i. AE xa in \<kappa> x. norm (s i (x, xa)) \<le> 2 * norm (f (x,xa))"
          using x * (2) kernel_space by auto
      qed fact
      moreover have "integral\<^sup>L (\<kappa> x) (\<lambda>y. s i (x, y)) = Bochner_Integration.simple_bochner_integral (\<kappa> x) (\<lambda>y. s i (x, y))" for i
      proof -
        have "Bochner_Integration.simple_bochner_integrable (\<kappa> x) (\<lambda>y. s i (x, y))"
        proof (rule simple_bochner_integrableI_bounded)
         have "(\<lambda>y. s i (x, y)) ` space Y \<subseteq> s i ` (space X \<times> space Y)"
            using x by auto
          then show "simple_function (\<kappa> x) (\<lambda>y. s i (x, y))"
            using simple_functionD(1)[OF s(1), of i] x kernel_space
            by (intro simple_function_borel_measurable) (auto simp: space_pair_measure dest: finite_subset)
        next
          have "(\<integral>\<^sup>+ y. ennreal (norm (s i (x, y))) \<partial>\<kappa> x) \<le> (\<integral>\<^sup>+ y. 2 * norm (f (x,y)) \<partial>\<kappa> x)"
            using x *(2) kernel_space by (intro nn_integral_mono) auto
          also have "... < \<infinity>"
            using int_2f unfolding integrable_iff_bounded by simp
          finally show "(\<integral>\<^sup>+ y. ennreal (norm (s i (x, y))) \<partial>\<kappa> x) < \<infinity>" .
        qed
        then show ?thesis
          by (rule simple_bochner_integrable_eq_integral[symmetric])
      qed
      ultimately show ?thesis
        by(simp add: curry_def)
    qed
    thus "(\<lambda>i. f' i x) \<longlonglongrightarrow> (\<integral>y. f (x,y) \<partial>(\<kappa> x))"
      by (cases "integrable (\<kappa> x) (curry f x)") (simp_all add: f'_def not_integrable_integral_eq curry_def)
  qed
qed

lemma(in s_finite_kernel) integrable_measurable_pred[measurable (raw)]:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes [measurable]:"case_prod f \<in> borel_measurable (X \<Otimes>\<^sub>M Y)"
  shows "Measurable.pred X (\<lambda>x. integrable (\<kappa> x) (f x))"
proof(cases "space X = {}")
  case True
  from space_empty[OF this] show ?thesis
    by simp
next
  case h:False
  obtain ki where ki:"\<And>i. subprob_kernel X Y (ki i)" "\<And>x A. x \<in> space X \<Longrightarrow> \<kappa> x A = (\<Sum>i. ki i x A)"
    using s_finite_kernels by metis
  have [simp]:"integrable (\<kappa> x) (f x) = ((\<Sum>i. \<integral>\<^sup>+ y. ennreal (norm (f x y)) \<partial>ki i x) < \<infinity>)" if "x \<in> space X" for x
    using ki(1) nn_integral_measure_suminf[of "\<lambda>i. ki i x" "\<kappa> x",OF _ ki(2)] that kernel_sets
    by(auto simp: integrable_iff_bounded  subprob_kernel_def measure_kernel_def)
  note [measurable] = nn_integral_measurable_subprob_algebra2
  show ?thesis
    by(rule measurable_cong[where g="\<lambda>x. (\<Sum>i. \<integral>\<^sup>+y. ennreal (norm (f x y)) \<partial>(ki i x)) < \<infinity>",THEN iffD2]) (insert ki(1), auto simp: subprob_kernel_def')
qed

lemma(in s_finite_kernel) integral_measurable_f:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes [measurable]:"case_prod f \<in> borel_measurable (X \<Otimes>\<^sub>M Y)"
  shows "(\<lambda>x. \<integral>y. f x y \<partial>(\<kappa> x)) \<in> borel_measurable X"
proof -
  obtain ki where ki:"\<And>i. subprob_kernel X Y (ki i)" "\<And>x A. x \<in> space X \<Longrightarrow> \<kappa> x A = (\<Sum>i. ki i x A)"
    using s_finite_kernels by metis
  note [measurable] = integral_measurable_subprob_algebra2

  show ?thesis
  proof(rule measurable_cong[where f="(\<lambda>x. if integrable (\<kappa> x) (f x) then (\<Sum>i. \<integral>y. f x y \<partial>(ki i x)) else 0)",THEN iffD1])
    fix x
    assume h:"x \<in> space X"
    {
      assume h':"integrable (\<kappa> x) (f x)"
      have "(\<Sum>i. \<integral>y. f x y \<partial>(ki i x)) = (\<integral>y. f x y \<partial>(\<kappa> x))"
        using lebesgue_integral_measure_suminf[of "\<lambda>i. ki i x" "\<kappa> x",OF _ ki(2) h'] ki(1) kernel_sets[OF h] h
        by(auto simp: subprob_kernel_def measure_kernel_def)
    }
    thus "(if integrable (\<kappa> x) (f x) then (\<Sum>i. \<integral>y. f x y \<partial>(ki i x)) else 0) = (\<integral>y. f x y \<partial>(\<kappa> x))"
      using not_integrable_integral_eq by auto
  qed(insert ki(1), auto simp: subprob_kernel_def')
qed

lemma(in s_finite_kernel) integral_measurable_f':
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes [measurable]:"f \<in> borel_measurable (X \<Otimes>\<^sub>M Y)"
  shows "(\<lambda>x. \<integral>y. f (x,y) \<partial>(\<kappa> x)) \<in> borel_measurable X"
  using integral_measurable_f[of "curry f"] by simp

lemma(in s_finite_kernel)
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes [measurable_cong]: "sets \<mu> = sets X"
      and "integrable (\<mu> \<bind>\<^sub>k \<kappa>) f"
    shows integrable_bind_kernelD1: "integrable \<mu> (\<lambda>x. \<integral>y. norm (f y) \<partial>\<kappa> x)" (is ?g1)
      and integrable_bind_kernelD1': "integrable \<mu> (\<lambda>x. \<integral>y. f y \<partial>\<kappa> x)" (is ?g1')
      and integrable_bind_kernelD2: "AE x in \<mu>. integrable (\<kappa> x) f" (is ?g2)
      and integrable_bind_kernelD3: "space X \<noteq> {} \<Longrightarrow> f \<in> borel_measurable Y" (is "_ \<Longrightarrow> ?g3")
proof -
  show 1:"space X \<noteq> {} \<Longrightarrow> ?g3"
    using assms(2) sets_bind_kernel[OF _ assms(1)] by(simp add: integrable_iff_bounded cong: measurable_cong_sets)
  have "integrable \<mu> (\<lambda>x. \<integral>y. norm (f y) \<partial>\<kappa> x) \<and> integrable \<mu> (\<lambda>x. \<integral>y. f y \<partial>\<kappa> x) \<and> (AE x in \<mu>. integrable (\<kappa> x) f)"
  proof(cases "space X = {}")
    assume ne: "space X \<noteq> {}"
    then have "space \<mu> \<noteq> {}" by(simp add: sets_eq_imp_space_eq[OF assms(1)])
    note h = integral_measurable_f[measurable] sets_bind_kernel[OF ne assms(1),measurable_cong]
    have g2: ?g2
      unfolding integrable_iff_bounded AE_conj_iff
    proof safe
      show "AE x in \<mu>. f \<in> borel_measurable (\<kappa> x)"
        using assms(2) by(auto simp: sets_eq_imp_space_eq[OF assms(1)] measurable_cong_sets[OF kernel_sets])
    next
      note nn_integral_measurable_f[measurable]
      have "AE x in \<mu>. (\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>\<kappa> x) \<noteq> \<infinity>"
        by(rule nn_integral_PInf_AE,insert assms(2)) (auto simp: integrable_iff_bounded nn_integral_bind_kernel[OF _ assms(1)] intro!: )
      thus "AE x in \<mu>. (\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>\<kappa> x) < \<infinity>"
        by (simp add: top.not_eq_extremum)
    qed
    have [simp]:"(\<integral>\<^sup>+ x. \<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>\<kappa> x \<partial>\<mu>) =  (\<integral>\<^sup>+ x. ennreal (\<integral>y. norm (f y) \<partial>\<kappa> x)\<partial>\<mu>)"
      using g2 by(auto intro!: nn_integral_cong_AE simp: nn_integral_eq_integral)
    have g1: ?g1
      using assms(2) by(auto simp: integrable_iff_bounded measurable_cong_sets[OF h(2)] measurable_cong_sets[OF assms(1)] nn_integral_bind_kernel[OF _ assms(1)])
    have ?g1'
      using assms(2) by(auto intro!: Bochner_Integration.integrable_bound[OF g1])
    with g2 g1 show ?thesis
      by auto
  qed(auto simp: space_empty[of \<mu>] sets_eq_imp_space_eq[OF assms(1)] integrable_iff_bounded nn_integral_empty)
  thus ?g1 ?g1' ?g2
    by auto
qed

lemma(in s_finite_kernel)
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes [measurable_cong]: "sets \<mu> = sets X"
      and [measurable]:"AE x in \<mu>. integrable (\<kappa> x) f" "integrable \<mu> (\<lambda>x. \<integral>y. norm (f y) \<partial>\<kappa> x)" "f \<in> borel_measurable Y"
    shows integrable_bind_kernel: "integrable (\<mu> \<bind>\<^sub>k \<kappa>) f"
      and integral_bind_kernel: "(\<integral>y. f y \<partial>(\<mu> \<bind>\<^sub>k \<kappa>)) = (\<integral>x. (\<integral>y. f y\<partial>\<kappa> x)\<partial> \<mu>)" (is ?eq)
proof -
  have "integrable (\<mu> \<bind>\<^sub>k \<kappa>) f \<and> (\<integral>y. f y \<partial>(\<mu> \<bind>\<^sub>k \<kappa>)) = (\<integral>x. (\<integral>y. f y\<partial>\<kappa> x)\<partial> \<mu>)"
  proof(cases "space X = {}")
    assume ne: "space X \<noteq> {}"
    note sets_bind[measurable_cong] = sets_bind_kernel[OF ne assms(1)]
    note h = integral_measurable_f[measurable]
    have 1:"integrable (\<mu> \<bind>\<^sub>k \<kappa>) f"
      unfolding integrable_iff_bounded
    proof
      show "(\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>(\<mu> \<bind>\<^sub>k \<kappa>)) < \<infinity>" (is "?l < _")
      proof -
        have "?l = (\<integral>\<^sup>+ x. ennreal (\<integral>y. norm (f y) \<partial>\<kappa> x)\<partial>\<mu>)"
          using assms(2) by(auto intro!: nn_integral_cong_AE simp: nn_integral_eq_integral simp: nn_integral_bind_kernel[OF _ assms(1)])
        also have "... < \<infinity>"
          using assms(3) by(auto simp: integrable_iff_bounded)
        finally show ?thesis .
      qed
    qed simp
    then have ?eq
    proof induction
      case h[measurable]:(base A c)
      hence 1:"integrable (\<mu> \<bind>\<^sub>k \<kappa>) (indicat_real A)"
        by simp
      have 2:"integrable \<mu> (\<lambda>x. measure (\<kappa> x) A)"
        by(rule Bochner_Integration.integrable_cong[where f="\<lambda>x. Sigma_Algebra.measure (\<kappa> x) (A \<inter> space (\<kappa> x))",THEN iffD1,OF refl])
        (insert h integrable_bind_kernelD1[OF assms(1) 1] sets_eq_imp_space_eq[OF kernel_sets], auto simp: sets_eq_imp_space_eq[OF assms(1)] sets_eq_imp_space_eq[OF kernel_sets] sets_bind)
      have "AE x in \<mu>. emeasure (\<kappa> x) A \<noteq> \<infinity>"
        by(rule nn_integral_PInf_AE,insert h) (auto simp: emeasure_bind_kernel[OF assms(1) _ ne] sets_bind)
      hence 0:"AE x in \<mu>. emeasure (\<kappa> x) A < \<infinity>"
        by (simp add: top.not_eq_extremum)
      have "(\<integral>x. (\<integral>y. indicat_real A y *\<^sub>R c \<partial>\<kappa> x)\<partial> \<mu>) = (\<integral>x. measure (\<kappa> x) A *\<^sub>R c\<partial>\<mu>)"
        using h integrable_bind_kernelD2[OF assms(1) integrable_real_indicator,of A]
        by(auto intro!: integral_cong_AE simp: sets_eq_imp_space_eq[OF kernel_sets] sets_bind sets_eq_imp_space_eq[OF assms(1)])
      also have "... = (\<integral>x. measure (\<kappa> x) A \<partial>\<mu>) *\<^sub>R c"
        using 2 by(auto intro!: integral_scaleR_left)
      finally show ?case
        using h by(auto simp: measure_bind_kernel[OF assms(1) _ ne 0] sets_bind)
    next
      case ih:(add f g)
      show ?case
        using ih(1,2) integrable_bind_kernelD2[OF assms(1) ih(1)] integrable_bind_kernelD2[OF assms(1) ih(2)]
        by(auto simp: ih(3,4) Bochner_Integration.integral_add[OF integrable_bind_kernelD1'[OF assms(1) ih(1)] integrable_bind_kernelD1'[OF assms(1) ih(2)],symmetric] intro!: integral_cong_AE)
    next
      case ih:(lim f fn)
      show ?case (is "?lhs = ?rhs")
      proof -
        have conv: "AE x in \<mu>. (\<lambda>n. \<integral>y. fn n y\<partial>\<kappa> x) \<longlonglongrightarrow> (\<integral>y. f y \<partial>\<kappa> x)"
        proof -
          have conv:"AE x in \<mu>. integrable (\<kappa> x) f \<longrightarrow> (\<lambda>n. \<integral>y. fn n y\<partial>\<kappa> x) \<longlonglongrightarrow> (\<integral>y. f y \<partial>\<kappa> x)"
          proof
            fix x
            assume h:"x \<in> space \<mu>"
            then show "integrable (\<kappa> x) f \<longrightarrow> (\<lambda>n. \<integral>y. fn n y\<partial>\<kappa> x) \<longlonglongrightarrow> (\<integral>y. f y \<partial>\<kappa> x)"
              using ih by(auto intro!: integral_dominated_convergence[where w="\<lambda>x. 2 * norm (f x)"]  simp: sets_eq_imp_space_eq[OF sets_bind] sets_eq_imp_space_eq[OF kernel_sets[OF h[simplified sets_eq_imp_space_eq[OF assms(1)]]]] sets_eq_imp_space_eq[OF assms(1)])
          qed
          with conv integrable_bind_kernelD2[OF assms(1) ih(4)]
          show ?thesis by fastforce
        qed
        have "?lhs = lim (\<lambda>n. \<integral>y. fn n y \<partial>(\<mu> \<bind>\<^sub>k \<kappa>))"
          by(rule limI[OF integral_dominated_convergence[where w="\<lambda>x. 2 * norm (f x)"],symmetric]) (use ih in auto)
        also have "... = lim (\<lambda>n. (\<integral>x. (\<integral>y. fn n y\<partial>\<kappa> x)\<partial> \<mu>))"
          by(simp add: ih)
        also have "... = (\<integral>x. lim (\<lambda>n. \<integral>y. fn n y\<partial>\<kappa> x)\<partial> \<mu>)"
        proof(rule limI[OF integral_dominated_convergence[where w="\<lambda>x. \<integral>y. 2 * norm (f y) \<partial>\<kappa> x"]])
          fix n
          show "AE x in \<mu>. norm (\<integral>y. fn n y\<partial>\<kappa> x) \<le> (\<integral>y. 2 * norm (f y) \<partial>\<kappa> x)"
            by(rule AE_mp[OF integrable_bind_kernelD2[OF assms(1) ih(1),of n] AE_mp[OF integrable_bind_kernelD2[OF assms(1) ih(4)]]],standard+,rule order.trans[OF integral_norm_bound integral_mono[of "\<kappa> _" "\<lambda>y. norm (fn n y)" _,OF _ _ ih(3)[simplified sets_eq_imp_space_eq[OF sets_bind]]]])
              (auto simp: sets_eq_imp_space_eq[OF assms(1)] sets_eq_imp_space_eq[OF kernel_sets])
        qed(use ih integrable_bind_kernelD1[OF assms(1) ih(4)] conv limI in auto,fastforce)
        also have "... = ?rhs"
          using ih conv limI by(auto intro!: integral_cong_AE, blast)
        finally show ?thesis .
      qed
    qed
    with 1 show ?thesis
      by auto
  qed(auto simp: bind_kernel_def space_empty[of \<mu>] sets_eq_imp_space_eq[OF assms(1)] integrable_iff_bounded nn_integral_empty Bochner_Integration.integral_empty)
  thus "integrable (\<mu> \<bind>\<^sub>k \<kappa>) f" ?eq
    by auto
qed

end