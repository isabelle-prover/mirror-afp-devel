(*  Title:   Regular_Measure.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

section  \<open>Regular Measures \<close>
theory Regular_Measure
  imports "HOL-Probability.Probability"
          "Standard_Borel_Spaces.StandardBorel"
          "Urysohn_Locally_Compact_Hausdorff"
begin

context Metric_space
begin

lemma nbh_add: "(\<Union>b\<in>(\<Union>a\<in>A. mball a e). mball b f) \<subseteq> (\<Union>a\<in>A. mball a (e + f))"
proof clarify
  fix a x b
  assume h:"a \<in> A" "b \<in> mball a e" "x \<in> mball b f"
  show "x \<in> (\<Union>a\<in>A. mball a (e + f))"
  proof(rule UN_I[OF h(1)])
    show "x \<in> mball a (e + f)"
      using h triangle by fastforce
  qed
qed

lemma nbh_subset:
  assumes A: "A \<subseteq> M" and e: "e > 0"
  shows "A \<subseteq> (\<Union>a\<in>A. mball a e)"
  using A e by auto

lemma nbh_decseq:
  assumes "decseq an"
  shows "decseq (\<lambda>n. \<Union>a\<in>A. mball a (an n))"
proof(safe intro!: decseq_SucI)
  fix n a b
  assume "a \<in> A" "b \<in> mball a (an (Suc n))"
  with decseq_SucD[OF assms] show "b \<in> (\<Union>c\<in>A. mball c (an n))"
    by(auto intro!: bexI[where x=a] simp: frac_le order_less_le_trans)
qed

lemma nbh_Inter_closure_of:
  assumes A: "A \<noteq> {}" "A \<subseteq> M"
      and an:"\<And>n. an n > 0" "decseq an" "an \<longlonglongrightarrow> 0"
    shows "(\<Inter>n. \<Union>a\<in>A. mball a (an n)) = mtopology closure_of A"
proof safe
  fix x
  assume x:"x \<in> (\<Inter>n. \<Union>a\<in>A. mball a (an n))"
  show "x \<in> mtopology closure_of A"
    unfolding metric_closure_of
  proof safe
    fix r :: real
    assume "0 < r"
    from LIMSEQ_D[OF an(3) this] an(1) obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> an n < r"
      by fastforce
    show "\<exists>y\<in>A. y \<in> mball x r"
    proof(rule ccontr)
      assume "\<not> (\<exists>y\<in>A. y \<in> mball x r)"
      then have 1:"\<forall>y\<in>A. y \<notin> mball x r"
        by auto
      obtain a where a:"a \<in> A" "x \<in> mball a (an N)"
        using x by auto
      with N[of N] have "a \<in> mball x (an N)" "mball x (an N) \<subseteq> mball x r"
        by (auto simp: commute)
      with a(1) 1 show False by auto
    qed
  qed(use x in auto)
next
  fix x n
  assume "x \<in> mtopology closure_of A"
  then have "x \<in> M" "\<forall>r>0. \<exists>y\<in>A. y \<in> mball x r"
    by(auto simp: metric_closure_of)
  with an(1)[of n] obtain y where y:"y \<in> A" "y \<in> mball x (an n)"
    by auto
  thus "x \<in> (\<Union>a\<in>A. mball a (an n))"
    by(auto intro!: bexI[where x=y] simp: commute)
qed

end

lemma(in finite_measure)
  assumes "range A \<subseteq> sets M" "disjoint_family A"
  shows suminf_measure:"(\<Sum>i. measure M (A i)) = measure M (\<Union>i. A i)"
    and summable_measure: "summable (\<lambda>i. measure M (A i))"
  using finite_measure_UNION[OF assms] by(auto dest: sums_unique simp: summable_def)

text \<open>We refer to the lecture note~\cite{probmetric}.\<close>
text \<open>Inner regular and outer regular with abstract topologies.\<close>

definition inner_regular :: "'a topology \<Rightarrow> 'a measure \<Rightarrow> bool" where
"inner_regular X M \<longleftrightarrow> sets M = sets (borel_of X) \<and> (\<forall>A\<in>sets M. M A = (\<Squnion>C\<in>{C. closedin X C \<and> C \<subseteq> A}. M C))"

definition outer_regular :: "'a topology \<Rightarrow> 'a measure \<Rightarrow> bool" where
"outer_regular X M \<longleftrightarrow> sets M = sets (borel_of X) \<and> (\<forall>A\<in>sets M. M A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. M C))"

definition regular_measure :: "'a topology \<Rightarrow> 'a measure \<Rightarrow> bool" where
"regular_measure X M \<longleftrightarrow> inner_regular X M \<and> outer_regular X M"

lemma
  shows inner_reguarI: "sets M = sets (borel_of X) \<Longrightarrow> (\<And>A. A \<in> sets M
      \<Longrightarrow> M A = (\<Squnion>C\<in>{C. closedin X C \<and> C \<subseteq> A}. M C)) \<Longrightarrow> inner_regular X M"
    and inner_reguarD: "inner_regular X M \<Longrightarrow> sets M = sets (borel_of X)"
    "inner_regular X M \<Longrightarrow> A \<in> sets M \<Longrightarrow> M A = (\<Squnion>C\<in>{C. closedin X C \<and> C \<subseteq> A}. M C)"
  by(auto simp: inner_regular_def)

lemma
  shows outer_reguarI: "sets M = sets (borel_of X)
     \<Longrightarrow> (\<And>A. A \<in> sets M \<Longrightarrow> M A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. M C)) \<Longrightarrow> outer_regular X M"
    and outer_reguarD: "outer_regular X M \<Longrightarrow> sets M = sets (borel_of X)"
    "outer_regular X M \<Longrightarrow> A \<in> sets M \<Longrightarrow> M A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. M C)"
  by(auto simp: outer_regular_def)

lemma
  shows regular_measureI: "inner_regular X M \<Longrightarrow> outer_regular X M \<Longrightarrow> regular_measure X M"
    and regular_measureD:
    "regular_measure X M \<Longrightarrow> inner_regular X M" "regular_measure X M \<Longrightarrow> outer_regular X M"
  by(auto simp: regular_measure_def)

lemma inner_regular_finite_measure:
  assumes "finite_measure M"
  shows "inner_regular X M \<longleftrightarrow>
         sets M = sets (borel_of X) \<and> (\<forall>A\<in>sets M. measure M A = (\<Squnion>C\<in>{C. closedin X C \<and> C \<subseteq> A}. measure M C))"
  unfolding inner_regular_def
proof safe
  interpret M: finite_measure M by fact
  fix A
  assume "A \<in> sets M" "\<forall>A\<in>sets M. M A = (\<Squnion>C\<in>{C. closedin X C \<and> C \<subseteq> A}. M C)"
  then have 1:"M A = (\<Squnion>C\<in>{C. closedin X C \<and> C \<subseteq> A}. M C)"
    by blast
  have "ennreal (measure M A) = ennreal (\<Squnion>C\<in>{C. closedin X C \<and> C \<subseteq> A}. measure M C)"
  proof -
    have "ennreal (measure M A) = M A"
      by (simp add: M.emeasure_eq_measure)
    also have "... = (\<Squnion>C\<in>{C. closedin X C \<and> C \<subseteq> A}. M C)"
      by fact
    also have "... = (\<Squnion>C\<in>{C. closedin X C \<and> C \<subseteq> A}. ennreal (measure M C))"
      by (simp add: M.emeasure_eq_measure)
    also have "... = ennreal (\<Squnion>C\<in>{C. closedin X C \<and> C \<subseteq> A}. measure M C)"
      by(intro ennreal_SUP[symmetric]) (use calculation in fastforce)+
    finally show ?thesis .
  qed
  moreover have "(\<Squnion>C\<in>{C. closedin X C \<and> C \<subseteq> A}. measure M C) \<ge> 0"
    by(subst le_cSUP_iff)
      (auto intro!: bdd_aboveI[where M="measure M (space M)"] M.bounded_measure exI[where x="{}"])
  ultimately show "measure M A = (\<Squnion>C\<in>{C. closedin X C \<and> C \<subseteq> A}. measure M C)"
    by simp
next
  interpret M: finite_measure M by fact
  fix A
  assume "A \<in> sets M" "\<forall>A\<in>sets M. measure M A = (\<Squnion>C\<in>{C. closedin X C \<and> C \<subseteq> A}. measure M C)"
  then have 1:"measure M A = (\<Squnion>C\<in>{C. closedin X C \<and> C \<subseteq> A}. measure M C)"
    by blast
  show "M A = (\<Squnion>C\<in>{C. closedin X C \<and> C \<subseteq> A}. M C)"
  proof -
    have "M A = ennreal (measure M A)"
      by(rule M.emeasure_eq_measure)
    also have "... = ennreal (\<Squnion>C\<in>{C. closedin X C \<and> C \<subseteq> A}. measure M C)"
      by (simp add: 1)
    also have "... = (\<Squnion>C\<in>{C. closedin X C \<and> C \<subseteq> A}. ennreal (measure M C))"
      by(intro ennreal_SUP)
        (metis (mono_tags, lifting) M.emeasure_eq_measure M.emeasure_finite SUP_least emeasure_space top.extremum_unique,blast)
    finally show ?thesis
      by (simp add: M.emeasure_eq_measure)
  qed
qed

lemma(in finite_measure)
  shows inner_regularI: "sets M = sets (borel_of X) \<Longrightarrow> (\<And>A. A \<in> sets M
     \<Longrightarrow> measure M A = (\<Squnion>C\<in>{C. closedin X C \<and> C \<subseteq> A}. measure M C)) \<Longrightarrow> inner_regular X M"
    and inner_regularD:
 "inner_regular X M \<Longrightarrow> A \<in> sets M \<Longrightarrow> measure M A = (\<Squnion>C\<in>{C. closedin X C \<and> C \<subseteq> A}. measure M C)"
  by(auto simp: inner_regular_finite_measure finite_measure_axioms)

lemma outer_regular_finite_measure:
  assumes "finite_measure M"
  shows "outer_regular X M \<longleftrightarrow> sets M = sets (borel_of X) \<and> (\<forall>A\<in>sets M. measure M A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. measure M C))"
  unfolding outer_regular_def
proof safe
  interpret M: finite_measure M by fact
  fix A
  assume A:"A \<in> sets M" "\<forall>A\<in>sets M. measure M A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. measure M C)"
     and sets_M: "sets M = sets (borel_of X)"
  then have 1:"measure M A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. measure M C)"
    by blast
  have [simp]:"openin X (space M)"
    by (simp add: sets_M sets_eq_imp_space_eq space_borel_of)
  show "M A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. M C)"
  proof -
    have "enn2ereal (M A) = ereal (measure M A)"
      by (simp add: M.emeasure_eq_measure)
    also have "... = ereal (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. measure M C)"
      by (simp add: 1)
    also have "... = (\<Sqinter> (ereal ` measure M ` {C. openin X C \<and> A \<subseteq> C}))"
      by(intro ereal_Inf') (auto intro!: bdd_belowI[where m=0] exI[where x="space M"] sets.sets_into_space[OF A(1)])
    also have "... = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. enn2ereal (M C))"
      by (metis (no_types, lifting) M.emeasure_eq_measure enn2ereal_ennreal image_cong image_image measure_nonneg)
    also have "... = enn2ereal (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. M C)"
      by (simp add: Inf_ennreal.rep_eq image_image)
    finally show ?thesis
      using enn2ereal_inject by blast
  qed
next
  interpret M: finite_measure M by fact
  fix A
  assume A:"A \<in> sets M" "\<forall>A\<in>sets M. M A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. M C)"
     and sets_M: "sets M = sets (borel_of X)"
  then have 1:"M A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. M C)"
    by blast
  have [simp]:"openin X (space M)"
    by (simp add: sets_M sets_eq_imp_space_eq space_borel_of)
  show "measure M A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. measure M C)"
  proof -
    have "ereal (measure M A) = enn2ereal (M A)"
      by (simp add: M.emeasure_eq_measure)
    also have "... = enn2ereal (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. M C)"
      by(simp add: 1)
    also have "... = (\<Sqinter> (ereal ` measure M ` {C. openin X C \<and> A \<subseteq> C}))"
      by(auto simp: Inf_ennreal.rep_eq image_image M.emeasure_eq_measure)
    also have "... = ereal (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. measure M C)"
      by(intro ereal_Inf'[symmetric]) (auto intro!: bdd_belowI[where m=0] exI[where x="space M"] sets.sets_into_space[OF A(1)])
    finally show ?thesis
      by blast
  qed
qed

lemma(in finite_measure)
  shows outer_regularI: "sets M = sets (borel_of X) \<Longrightarrow> (\<And>A. A \<in> sets M
      \<Longrightarrow> measure M A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. measure M C)) \<Longrightarrow> outer_regular X M"
    and outer_regularD: "outer_regular X M \<Longrightarrow> A \<in> sets M
      \<Longrightarrow> measure M A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. measure M C)"
  by(auto simp: outer_regular_finite_measure finite_measure_axioms)

text \<open>Abstract version of @{thm inner_regular} and @{thm outer_regular}.\<close>
lemma(in finite_measure)
  assumes "metrizable_space X" "sets (borel_of X) = sets M"
    shows inner_regular':"inner_regular X M"
      and outer_regular':"outer_regular X M"
proof -
  let ?Sup = "\<lambda>A. (\<Squnion>C\<in>{C. closedin X C \<and> C \<subseteq> A}. measure M C)"
  let ?Inf = "\<lambda>A. (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. measure M C)"
  {
    fix A
    assume A[measurable]: "A \<in> sets M"
    obtain d where d: "Metric_space (topspace X) d" "Metric_space.mtopology (topspace X) d = X"
      by (metis Metric_space.topspace_mtopology assms(1) metrizable_space_def)
    then interpret d: Metric_space "topspace X" d by simp
    have sets[measurable (raw)]: "\<And>A. openin X A \<Longrightarrow> A \<in> sets M"  "\<And>A. closedin X A \<Longrightarrow> A \<in> sets M"
      "\<And>A. openin d.mtopology A \<Longrightarrow> A \<in> sets M" "\<And>A. closedin d.mtopology A \<Longrightarrow> A \<in> sets M"
      by(auto simp: d assms(2)[symmetric] dest: borel_of_open borel_of_closed)
    have bdd[simp]: "\<And>A. bdd_above (measure M ` {C. closedin X C \<and> C \<subseteq> A})"
      "\<And>A. bdd_below (measure M ` {C. closedin X C \<and> C \<subseteq> A})"
      "\<And>A. bdd_above (measure M ` {C. openin X C \<and> A \<subseteq> C})"
      "\<And>A. bdd_below (measure M ` {C. openin X C \<and> A \<subseteq> C})"
      by(auto intro!: bdd_aboveI[where M="measure M (space M)"] bdd_belowI[where m=0] bounded_measure)
    have ne[simp]: "{C. closedin X C \<and> C \<subseteq> A} \<noteq> {}" "A \<in> sets M \<Longrightarrow> {C. openin X C \<and> A \<subseteq> C} \<noteq> {}" for A
      using sets.sets_into_space[of A M,simplified space_borel_of]
        sets_eq_imp_space_eq[OF assms(2),simplified space_borel_of] by blast+
    have 1:"measure M A \<le> ?Inf A" "measure M A \<ge> ?Sup A"
      using sets.sets_into_space[OF A[simplified assms(2)[symmetric]],simplified space_borel_of]
            openin_topspace closedin_topspace sets.sets_into_space[OF A]
      by(fastforce intro!: le_cInf_iff[where a="measure M A"
                                         and S="measure M ` {C. openin X C \<and> A \<subseteq> C}",THEN iffD2]
                           cSup_le_iff[where a="measure M A"
                                         and S="measure M ` {C. closedin X C \<and> C \<subseteq> A}",THEN iffD2]
                bdd_aboveI[where M="measure M (space M)"] bdd_belowI[where m=0] finite_measure_mono)+
    have setsM: "sigma_sets (topspace X) {U. closedin X U} = sets M"
      using sets_eq_imp_space_eq[OF assms(2)] by(auto simp: assms(2)[symmetric] sets_borel_of_closed)
    have 2:"Int_stable {U. closedin X U}" "{U. closedin X U} \<subseteq> Pow (topspace X)"
      by(auto dest: closedin_subset intro!: Int_stableI)

    have "measure M A \<le> ?Sup A \<and> measure M A \<ge> ?Inf A"
    proof(rule sigma_sets_induct_disjoint[OF 2 A[simplified setsM[symmetric]]])
      fix a
      assume "a \<in> {U. closedin X U}"
      then have a[measurable]: "closedin X a" "a \<in> sets M"
        by(auto simp: assms(2)[symmetric] borel_of_closed)
      show "measure M a \<le> ?Sup a \<and> measure M a \<ge> ?Inf a"
      proof (cases "a = {}")
        case empty:True
        thus ?thesis
          by(auto intro!: cINF_lower[where f="measure M" and x="{}",simplified] bdd_belowI[where m=0]
                    simp: empty)
      next
        case ne:False
        show ?thesis
        proof
          have "measure M a = ?Sup a"
            by(rule cSup_eq_maximum[symmetric],insert a(1),auto intro!: finite_measure_mono)
          thus "measure M a \<le> ?Sup a" by simp
        next
          show "measure M a \<ge> ?Inf a"
          proof -
            have "?Inf a \<le> (\<Sqinter>n. measure M (\<Union>x\<in>a. d.mball x (1 / Suc n)))"
            proof(rule cInf_superset_mono)
              show "range (\<lambda>n. measure M (\<Union>x\<in>a. d.mball x (1 / real (Suc n)))) \<subseteq> measure M ` {C. openin X C \<and> a \<subseteq> C}"
              proof clarify
                fix n
                have "(\<Union>x\<in>a. d.mball x (1 / (1 + real n))) \<in> {C. openin X C \<and> a \<subseteq> C}"
                  using d.openin_mball[simplified d(2)]  closedin_subset[OF a(1)] by auto
                thus "measure M (\<Union>x\<in>a. d.mball x (1 / (Suc n))) \<in> measure M ` {C. openin X C \<and> a \<subseteq> C}"
                  by auto
              qed
            qed auto
            also have "... = measure M a"
            proof -
              have [measurable]: "(\<Union>x\<in>a. d.mball x (1 / (1 + real n))) \<in> sets M" for n
                by(auto simp: assms(2)[symmetric] d.openin_mball[simplified d] intro!: borel_of_open openin_clauses(3))
              have 0:"decseq (\<lambda>n. \<Union>x\<in>a. d.mball x (1 / (1 + real n)))"
                by(rule d.nbh_decseq) (auto intro!: decseq_SucI simp: frac_le)
              have 1:"decseq (\<lambda>n. measure M (\<Union>x\<in>a. d.mball x (1 / (1 + real n))))"
                by(rule decseq_SucI,rule finite_measure_mono) (use decseq_SucD[OF 0] in auto)
              have 2:"(\<lambda>n. measure M (\<Union>x\<in>a. d.mball x (1 / (1 + real n)))) \<longlonglongrightarrow> (\<Sqinter>n. measure M (\<Union>x\<in>a. d.mball x (1 / Suc n)))"
                by(auto intro!: LIMSEQ_decseq_INF[OF _ 1] bdd_belowI[where m=0])
              moreover have "(\<lambda>n. measure M (\<Union>x\<in>a. d.mball x (1 / (1 + real n)))) \<longlonglongrightarrow> measure M a"
              proof -
                have "(\<Inter>n. (\<Union>x\<in>a. d.mball x (1 / (1 + real n)))) = d.mtopology closure_of a"
                  by(rule d.nbh_Inter_closure_of[OF ne])
                    (auto simp: closedin_subset[OF a(1)] frac_le
                      intro!: decseq_SucI LIMSEQ_inverse_real_of_nat[simplified inverse_eq_divide,simplified])
                also have "... = a"
                  by(auto simp: closure_of_eq d a)
                finally have "(\<Inter>n. (\<Union>x\<in>a. d.mball x (1 / (1 + real n)))) = a" .
                moreover have "(\<lambda>n. measure M (\<Union>x\<in>a. d.mball x (1 / (1 + real n))))
                                \<longlonglongrightarrow> measure M (\<Inter>n. (\<Union>x\<in>a. d.mball x (1 / (1 + real n))))"
                  by(auto intro!: finite_Lim_measure_decseq simp: 0)
                ultimately show ?thesis by simp
              qed
              ultimately show ?thesis
                by(auto dest: LIMSEQ_unique)
            qed
            finally show "?Inf a \<le> measure M a" .
          qed
        qed
      qed
    next
      show "measure M {} \<le> ?Sup {} \<and> measure M {} \<ge> ?Inf {}"
        by(auto intro!: cINF_lower[where f="measure M" and x="{}",simplified] bdd_belowI[where m=0])
    next
      fix a
      assume "a \<in> sigma_sets (topspace X) {U. closedin X U}"
        and ih:"measure M a \<le> ?Sup a \<and> measure M a \<ge> ?Inf a"
      then have [measurable]:"a \<in> sets M"
        by(simp add: setsM)
      show "measure M (topspace X - a) \<le> ?Sup (topspace X - a) \<and> measure M (topspace X - a) \<ge> ?Inf (topspace X - a)"
      proof
        show "measure M (topspace X - a) \<le> ?Sup (topspace X - a)"
        proof(safe intro!: le_cSup_iff_less[THEN iffD2])
          fix y
          assume "y < measure M (topspace X - a)"
          then have "measure M a < measure M (space M) - y"
            by(auto simp: sets_eq_imp_space_eq[OF assms(2),simplified space_borel_of] finite_measure_compl)
          then obtain U where U: "openin X U" "a \<subseteq> U" "measure M U \<le> measure M (space M) - y"
            using ih by(auto simp:  cInf_le_iff_less[OF ne(2) bdd(4)])
          show "\<exists>C\<in>{C. closedin X C \<and> C \<subseteq> topspace X - a}. y \<le> Sigma_Algebra.measure M C"
          proof(safe intro!: bexI[where x="topspace X - U"])
            have [arith]:"measure M a \<le> measure M U"
              using U by(auto intro!: finite_measure_mono)
            show "y \<le> measure M (topspace X - U)"
              using U by(auto simp: sets_eq_imp_space_eq[OF assms(2),simplified space_borel_of] finite_measure_compl)
          qed(use U in auto)
        qed auto
      next
        show "?Inf (topspace X - a) \<le> measure M (topspace X - a)"
        proof(rule cInf_le_iff_less[THEN iffD2])
          show "\<forall>y>measure M (topspace X - a). \<exists>C\<in>{C. openin X C \<and> topspace X - a \<subseteq> C}. measure M C \<le> y"
          proof safe
            fix y
            assume "measure M (topspace X - a) < y"
            then have "measure M (space M) - y < measure M a"
              by(auto simp: sets_eq_imp_space_eq[OF assms(2),simplified space_borel_of] finite_measure_compl)
            then obtain C where C: "closedin X C" "C \<subseteq> a" "measure M (space M) - y \<le> measure M C"
              using ih by(auto simp: le_cSup_iff_less[OF ne(1) bdd(1)])
            show "\<exists>C\<in>{C. openin X C \<and> topspace X - a \<subseteq> C}.  measure M C \<le> y"
            proof(safe intro!: bexI[where x="topspace X - C"])
              have [arith]:"measure M C \<le> measure M a"
                using C by(auto intro!: finite_measure_mono)
              show "measure M (topspace X - C) \<le> y"
                using C by(auto simp: sets_eq_imp_space_eq[OF assms(2),simplified space_borel_of] finite_measure_compl)
            qed(use C in auto)
          qed
        qed auto
      qed
    next
      fix a :: "nat \<Rightarrow> _"
      assume h: "disjoint_family a" "range a \<subseteq> sigma_sets (topspace X) {U. closedin X U}"
        and ih: "\<And>i. measure M (a i) \<le> ?Sup (a i) \<and> ?Inf (a i) \<le> measure M (a i)"
      then have a[measurable]: "\<And>i. a i \<in> sets M"
        by(simp add: setsM)
      show "measure M (\<Union>i. a i) \<le> ?Sup (\<Union>i. a i) \<and> ?Inf (\<Union>i. a i) \<le> measure M (\<Union>i. a i)"
      proof
        show "measure M (\<Union>i. a i) \<le> ?Sup (\<Union>i. a i)"
        proof(rule le_cSup_iff_less[THEN iffD2])
          show "\<forall>y< measure M (\<Union> (range a)). \<exists>C\<in>{C. closedin X C \<and> C \<subseteq> \<Union> (range a)}. y \<le> measure M C"
          proof safe
            fix y
            assume "y < measure M (\<Union>i. a i)"
            also have "... = (\<Sum>i. measure M (a i))"
              by(rule suminf_measure[OF _ h(1),symmetric]) auto
            finally obtain N where N: "y < (\<Sum>i<N. measure M (a i))"
              by (meson linorder_not_less measure_nonneg suminf_le_const summableI_nonneg_bounded)
            consider "N = 0" | "N > 0" by auto
            then show "\<exists>C\<in>{C. closedin X C \<and> C \<subseteq> \<Union> (range a)}. y \<le> measure M C"
            proof cases
              case 1
              with N show ?thesis by(auto intro!: exI[where x="{}"])
            next
              case [arith]:2
              define e where "e \<equiv> ((\<Sum>i<N. measure M (a i)) - y) / N"
              have e[arith]: "e > 0"
                using N by(auto simp: e_def)
              hence "\<And>i. measure M (a i) - e < measure M (a i)" by auto
              hence "\<forall>i. \<exists>Ci. closedin X Ci \<and> Ci \<subseteq> a i \<and> measure M (a i) - e \<le> measure M Ci"
                using ih[simplified le_cSup_iff_less[OF ne(1) bdd(1)]] by auto
              then obtain Ci where Ci: "\<And>i. closedin X (Ci i)"
                "\<And>i. Ci i \<subseteq> a i" "\<And>i. measure M (a i) - e \<le> measure M (Ci i)"
                by metis
              with h have Ci_d:"disjoint_family_on Ci {..<N}"
                by(auto simp: disjoint_family_on_def) blast
              show ?thesis
              proof(safe intro!: bexI[where x="\<Union> (Ci ` {..<N})"])
                have "y \<le> (\<Sum>i<N. measure M (a i)) - ((\<Sum>i<N. measure M (a i)) - y)" by auto
                also have "... \<le> (\<Sum>i<N. measure M (a i) - e)"
                  by(auto simp: e_def sum_subtractf)
                also have "... \<le> (\<Sum>i<N. measure M (Ci i))"
                  using Ci by(auto intro!: sum_mono)
                also have "... = measure M (\<Union> (Ci ` {..<N}))"
                  by(rule finite_measure_finite_Union[OF _ _ Ci_d,symmetric]) (use Ci in auto)
                finally show "y \<le> measure M (\<Union> (Ci ` {..<N}))" .
              qed(insert Ci,auto intro!: closedin_Union)
            qed
          qed
        qed auto
      next
        show "?Inf (\<Union>i. a i) \<le> measure M (\<Union>i. a i)"
        proof(rule cInf_le_iff_less[THEN iffD2])
          show "\<forall>y> measure M (\<Union> (range a)). \<exists>C\<in>{C. openin X C \<and> \<Union> (range a) \<subseteq> C}. measure M C \<le> y"
          proof safe
            fix y
            assume 1:"measure M (\<Union>i. a i) < y"
            define en where "en \<equiv> (\<lambda>n. (y - measure M (\<Union>i. a i)) * (1 / 2) ^ (Suc n))"
            with 1 have [arith]:"en n > 0" for n by auto
            hence "measure M (a i) < measure M (a i) + en i" for i by auto
            hence "\<exists>Ui. openin X Ui \<and> a i \<subseteq> Ui \<and> measure M Ui \<le> measure M (a i) + en i" for i
              using ih[of i,simplified cInf_le_iff_less[OF ne(2)[OF \<open>a i \<in> sets M\<close>] bdd(4)]] by auto
            then obtain Ui where Ui: "\<And>i. openin X (Ui i)" "\<And>i. a i \<subseteq> Ui i"
              "\<And>i. measure M (Ui i) \<le> measure M (a i) + en i"
              by metis
            have [simp]: "summable en" "summable (\<lambda>n. measure M (a n))"
              by(auto simp: en_def intro!: summable_measure h)
            hence [simp]: "summable (\<lambda>n. measure M (a n) + en n)"
              by(auto intro!: summable_add)
            have [simp]:"summable (\<lambda>n. measure M (Ui n))"
              using Ui by(auto intro!: summable_comparison_test_ev[OF _ \<open>summable (\<lambda>n. measure M (a n) + en n)\<close>])
            show "\<exists>C\<in>{C. openin X C \<and> \<Union> (range a) \<subseteq> C}. measure M C \<le> y"
            proof(safe intro!: bexI[where x="\<Union>i. Ui i"])
              have "measure M (\<Union>i. Ui i) \<le> (\<Sum>i. measure M (Ui i))"
                using Ui by(auto intro!: finite_measure_subadditive_countably)
              also have "... \<le> (\<Sum>i. measure M (a i) + en i)"
                by(auto intro!: suminf_le Ui)
              also have "... = (\<Sum>i. measure M (a i)) + (\<Sum>i. en i)"
                by(simp add: suminf_add)
              also have "... = measure M (\<Union>i. a i) + (y - measure M (\<Union>i. a i))"
              proof -
                have [simp]:"(\<Sum>i. measure M (a i)) = measure M (\<Union>i. a i)"
                  by(auto intro!: suminf_measure h)
                have "(\<Sum>i. en i) = (y - Sigma_Algebra.measure M (\<Union> (range a))) / 2 * (\<Sum>n. (1 / 2) ^ n)"
                  by(simp only: suminf_mult[of "\<lambda>n. (1 / 2) ^ n :: real",simplified,symmetric]) (simp add: en_def)
                also have "... = (y - measure M (\<Union>i. a i))"
                  by(simp add: suminf_geometric)
                finally show ?thesis by simp
              qed
              finally show "measure M (\<Union>i. Ui i) \<le> y" by simp
            qed(use Ui in auto)
          qed
          show "{C. openin X C \<and> \<Union> (range a) \<subseteq> C} \<noteq> {}"
            using sets.sets_into_space[OF a]
            by(force intro!: exI[where x="topspace X"] simp: sets_eq_imp_space_eq[OF assms(2),simplified space_borel_of])
        qed auto
      qed
    qed
    note 1 this
  }
  with assms(2) show "inner_regular X M" "outer_regular X M"
    by (fastforce intro!: inner_regularI outer_regularI)+
qed

definition tight_on_set :: "'a topology \<Rightarrow> 'a measure set \<Rightarrow> bool" where
"tight_on_set X \<Gamma> \<longleftrightarrow> (\<forall>M\<in>\<Gamma>. finite_measure M \<and> sets (borel_of X) = sets M) \<and>
                      (\<forall>e>0. \<exists>K. compactin X K \<and> (\<forall>M\<in>\<Gamma>. measure M (space M - K) < e))"

abbreviation tight_on :: "'a topology \<Rightarrow> 'a measure \<Rightarrow> bool" where
"tight_on X M \<equiv> tight_on_set X {M}"

lemma tight_on_def:
"tight_on X M \<longleftrightarrow> finite_measure M \<and> sets (borel_of X) = sets M \<and>
                  (\<forall>e>0. \<exists>K. compactin X K \<and> measure M (space M - K) < e)"
  by(auto simp: tight_on_set_def)

lemma tight_on_set_subset: "A \<subseteq> B \<Longrightarrow> tight_on_set X B \<Longrightarrow> tight_on_set X A"
  unfolding tight_on_set_def by blast

lemma tight_on_tight: "tight_on_set euclidean (Mi ` UNIV) \<and> (\<forall>i. real_distribution (Mi i)) \<longleftrightarrow> tight Mi"
proof safe
  assume h:"tight_on_set euclideanreal (range Mi)" "\<forall>i. real_distribution (Mi i)"
  show "tight Mi"
    unfolding tight_def
  proof safe
    fix e :: real
    assume e: "e > 0"
    with h(1) obtain K where K:
     "compact K" "\<And>i. measure (Mi i) (space (Mi i) - K) < e"
      by(auto simp: tight_on_set_def)
    obtain r where r:
      "r > 0" "K \<subseteq> ball 0 r"
      by(metis bounded_subset_ballD[OF compact_imp_bounded[OF K(1)]])
    show "\<exists>a b. a < b \<and> (\<forall>n. 1 - e < measure (Mi n) {a<..b})"
    proof(rule exI[where x="-r"])
      show "\<exists>b>- r. \<forall>n. 1 - e < measure (Mi n) {- r<..b}"
      proof(safe intro!: exI[where x=r])
        fix n
        interpret real_distribution "Mi n"
          using h by simp
        have [measurable]: "K \<in> sets (Mi n)"
          by (simp add: K(1) borel_compact)
        hence "1 - e < prob K"
          using K(2)[of n] by(simp add: prob_compl del: borel_UNIV)
        also have "... \<le> prob {- r<..<r}"
          using r by(auto intro!: finite_measure_mono simp: ball_eq_greaterThanLessThan)
        also have "... \<le> prob {-r<..r}"
          by(auto intro!: finite_measure_mono)
        finally show "1 - e < prob {-r<..r}" .
      qed(use r in auto)
    qed
  qed(use h in simp)
next
  assume h:"tight Mi"
  show "tight_on_set euclideanreal (range Mi)"
    unfolding tight_on_set_def
  proof safe
    fix e :: real
    assume e: "e > 0"
    with h obtain a b where ab: "a < b" "\<And>n. measure (Mi n) {a<..b} > 1 - e"
      by(auto simp: tight_def)
    show "\<exists>K. compactin euclideanreal K \<and> (\<forall>M\<in>range Mi. measure M (space M - K) < e)"
    proof(safe intro!: exI[where x="{a..b}"])
      fix n
      interpret real_distribution "Mi n"
        using h by(auto simp: tight_def)
      have "prob (space (Mi n) - {a..b}) = 1 - prob {a..b}"
        by(rule prob_compl) simp
      also have "... \<le> 1 - prob {a<..b}"
        by(auto intro!: finite_measure_mono)
      also have "... < e"
        using ab(2)[of n] by auto
      finally show "prob (space (Mi n) - {a..b}) < e" .
    qed simp
  qed(insert h,auto simp: borel_of_euclidean tight_def real_distribution_def real_distribution_axioms_def prob_space_def)
qed(auto simp: tight_def)

lemma inner_regular'':
  assumes "metrizable_space X" "tight_on X M"
      and [measurable]:"A \<in> sets M"
    shows "measure M A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. measure M K)" (is "_ = ?rhs")
proof -
  have sets: "sets (borel_of X) = sets M"
    using assms(2) by(simp add: tight_on_def)
  interpret M: finite_measure M
    using assms(2) by(simp add: tight_on_def)
  have "measure M A \<ge> ?rhs"
    using sets.sets_into_space[OF assms(3)]
    by(auto intro!: cSup_le_iff[THEN iffD2] M.finite_measure_mono bdd_aboveI[where M="measure M (space M)"])
  moreover have "measure M A \<le> ?rhs"
  proof -
    have "measure M A - e < ?rhs" if e[arith]: "e > 0" for e
    proof -
      obtain K where K: "compactin X K" "measure M (space M - K) < e"
        using assms(2)[simplified tight_on_def] e by metis
      hence [measurable]: "K \<in> sets M"
        by(auto simp: sets[symmetric]
            intro!: borel_of_closed compactin_imp_closedin[OF metrizable_imp_Hausdorff_space[OF assms(1)]])
      have "measure M A - e < measure M A - measure M (space M - K)"
        using K by auto
      also have "... \<le> measure M (A \<inter> K)"
        by (metis Diff_mono M.finite_measure_Diff' M.finite_measure_mono \<open>K \<in> sets M\<close> assms(3) cancel_ab_semigroup_add_class.diff_right_commute dual_order.refl le_iff_diff_le_0 sets.Diff sets.sets_into_space sets.top)
      also have "... = (\<Squnion>C\<in>{C. closedin X C \<and> C \<subseteq> A \<inter> K}. measure M C)"
        by(rule M.inner_regularD[OF M.inner_regular'[OF assms(1) sets]]) measurable
      also have "... \<le> ?rhs"
      proof(rule cSup_mono)
        show "\<And>b. b \<in> Sigma_Algebra.measure M ` {C. closedin X C \<and> C \<subseteq> A \<inter> K}
               \<Longrightarrow> \<exists>a\<in>Sigma_Algebra.measure M ` {K. compactin X K \<and> K \<subseteq> A}. b \<le> a"
        proof safe
          fix C
          assume "closedin X C" "C \<subseteq> A \<inter> K"
          then show "\<exists>a\<in>Sigma_Algebra.measure M ` {K. compactin X K \<and> K \<subseteq> A}. measure M C \<le> a"
            by(auto intro!: closed_compactin[OF K(1)])
        qed
      qed(auto intro!: bdd_aboveI[where M="measure M (space M)"] M.bounded_measure)
      finally show ?thesis .
    qed
    thus ?thesis
      by (metis (full_types) cancel_ab_semigroup_add_class.diff_right_commute dual_order.refl le_iff_diff_le_0 less_iff_diff_less_0 linorder_not_less)
  qed
  ultimately show ?thesis by simp
qed

lemma(in finite_measure) tight_on_compact_space:
  assumes "metrizable_space X" "compact_space X" "sets (borel_of X) = sets M"
  shows "tight_on X M"
  using assms(1,2)
  by(auto simp: tight_on_def assms finite_measure_axioms sets_eq_imp_space_eq[OF assms(3)[symmetric]]
                compact_space_def space_borel_of
      intro!: exI[where x="space M"])

lemma(in finite_measure) tight_on_finite_space:
  assumes "metrizable_space X" "sets (borel_of X) = sets M" "finite (space M)"
  shows "tight_on X M"
proof -
  from assms(3) have "compact_space X"
    by(auto simp: assms compact_space_def sets_eq_imp_space_eq[OF assms(2)[symmetric]] space_borel_of
          intro!: finite_imp_compactin_eq[THEN iffD2])
  from tight_on_compact_space[OF assms(1) this assms(2)] show ?thesis .
qed

lemma(in finite_measure) tight_on_Polish:
  assumes "Polish_space X" "sets (borel_of X) = sets M"
  shows "tight_on X M"
proof(cases "finite (space M)")
  case True
  then show ?thesis
    by(auto intro!: tight_on_finite_space assms Polish_space_imp_metrizable_space)
next
  case inf:False
  then have inf2: "infinite (topspace X)"
    by(auto simp: sets_eq_imp_space_eq[OF assms(2)[symmetric]] space_borel_of)
  obtain d where d:"Metric_space (topspace X) d" "Metric_space.mtopology (topspace X) d = X"
    "Metric_space.mcomplete (topspace X) d"
    by (metis Metric_space.topspace_mtopology assms(1) completely_metrizable_space_def Polish_space_imp_completely_metrizable_space)
  interpret d: Metric_space "topspace X" d by fact
  have [measurable]:"\<And>a e. d.mball a e \<in> sets M" "\<And>a e. d.mcball a e \<in> sets M"
    using d.openin_mball d.closedin_mcball by(auto simp: assms(2)[symmetric] borel_of_open borel_of_closed d)
  show ?thesis
    unfolding tight_on_def
  proof safe
    fix e :: real
    assume e: "e > 0"
    from assms obtain U where U: "countable U" "dense_in X U"
      by(auto simp: separable_space_def2 Polish_space_def)
    have U_ne: "U \<noteq> {}"
      by (metis U(2) dense_in_nonempty inf2 infinite_imp_nonempty)
    let ?an = "from_nat_into U"
    have an:"\<And>n. ?an n \<in> U"
      by (simp add: U_ne from_nat_into)
    have anU: "(\<Union>n. d.mball (?an n) e') = topspace X" if "e' > 0" for e'
    proof -
      have "(\<Union>n. d.mball (?an n) e') = (\<Union>u\<in>U. d.mball u e')"
        by(auto simp: UN_from_nat_into[OF U(1) U_ne])
      also have "... = topspace X"
        by(rule d.mdense_balls_cover[simplified d,OF U(2) that])
      finally show ?thesis .
    qed
    have "\<exists>n. measure M (\<Union>i\<in>{..<n}. d.mball (?an i) (1 / Suc m)) > measure M (space M) - e * (1 / 2)^Suc m" for m
    proof -
      have 1:"(\<lambda>n. measure M (\<Union>i\<in>{..<n}. d.mball (?an i) (1 / Suc m)))
               \<longlonglongrightarrow> measure M (\<Union>n. \<Union>i\<in>{..<n}. d.mball (?an i) (1 / Suc m))"
        by(rule finite_Lim_measure_incseq) (fastforce simp: incseq_def)+
      have "(\<Union>n. \<Union>i\<in>{..<n}. d.mball (?an i) (1 / Suc m)) = (\<Union>n. d.mball (?an n) (1 / Suc m))" by blast
      also have "... = topspace X"
        by(rule anU) auto
      also have "... = space M"
        by(simp add: sets_eq_imp_space_eq[OF assms(2),simplified space_borel_of])
      finally have "(\<lambda>n. measure M (\<Union>i\<in>{..<n}. d.mball (?an i) (1 / Suc m))) \<longlonglongrightarrow> measure M (space M)"
        using 1 by simp
      moreover have "e * (1 / 2)^Suc m > 0" using e by auto
      ultimately have "\<exists>N. \<forall>n\<ge>N. \<bar>measure M (\<Union>i\<in>{..<n}. d.mball (?an i) (1 / Suc m)) - measure M (space M)\<bar> < e * (1/2)^Suc m"
        unfolding LIMSEQ_def dist_real_def by metis
      then obtain N where "measure M (space M) - measure M (\<Union>i\<in>{..<N}. d.mball (?an i) (1 / Suc m)) < e * (1/2)^Suc m"
        using bounded_measure by auto
      thus ?thesis
        by(auto intro!: exI[where x=N])
    qed
    then obtain n where n: "\<And>m. measure M (\<Union>i\<in>{..<n m}. d.mball (?an i) (1 / Suc m)) > measure M (space M) - e * (1 / 2)^Suc m"
      by metis
    have n': "\<And>m. measure M (\<Union>i\<in>{..<n m}. d.mcball (?an i) (1 / Suc m)) > measure M (space M) - e * (1 / 2)^Suc m"
      by(rule order.strict_trans2[OF n]) (auto intro!: finite_measure_mono)
    define K where "K \<equiv> \<Inter>m. \<Union>k\<in>{..<n m}. d.mcball (?an k) (1 / Suc m)"
    have K_closed: "closedin d.mtopology K"
      by(auto intro!: closedin_Union simp: K_def)
    have K_compact: "compactin d.mtopology K"
    proof -
      have "d.mtotally_bounded K"
        unfolding d.mtotally_bounded_def2
      proof safe
        fix e' :: real
        assume [arith]:"e' > 0"
        then obtain m where m[arith]: "1 / Suc m < e'"
          using nat_approx_posE by blast
        have "K \<subseteq> (\<Union>k\<in>{..<n m}. d.mcball (?an k) (1 / Suc m))"
          by(auto simp: K_def)
        also have "... \<subseteq> (\<Union>k\<in>{..<n m}. d.mball (?an k) e')"
          using m by auto
        finally show "\<exists>Ka. finite Ka \<and> Ka \<subseteq> topspace X \<and> K \<subseteq> (\<Union>x\<in>Ka. d.mball x e')"
          using an dense_in_subset[OF U(2)] by(fastforce intro!: exI[where x="?an ` {..<n m}"])
      qed
      thus ?thesis
        by(simp add: d.mtotally_bounded_eq_compact_closedin[OF d(3) K_closed,simplified])
    qed
    show "\<exists>K. compactin X K \<and> measure M (space M - K) < e"
    proof(safe intro!: exI[where x=K])
      have sum:"summable (\<lambda>m. measure M (space M - (\<Union>k\<in>{..<n m}. d.mcball (?an k) (1 / Suc m))))"
        apply(intro summable_comparison_test_ev[OF _  summable_mult[OF complete_algebra_summable_geometric[where x="1 / 2"]],of _ e] exI[where x=1])
         apply(simp add: eventually_sequentially finite_measure_compl)
         apply(intro exI[where x=1] allI)
        subgoal for l
          using n'[of l] e bounded_measure
          apply(auto intro!: order.strict_implies_order[OF order.strict_trans[where b="e* (1 / 2)^Suc l"]])
          done
        by simp
      have "measure M (space M - K) = measure M (\<Union>m. (space M - (\<Union>k\<in>{..<n m}. d.mcball (?an k) (1 / Suc m))))"
        by(auto simp: K_def)
      also have "... \<le> (\<Sum>m. measure M (space M - (\<Union>k\<in>{..<n m}. d.mcball (?an k) (1 / Suc m))))"
        by(rule finite_measure_subadditive_countably) (use sum in auto)
      also have "... = measure M (space M - (\<Union>k\<in>{..<n 0}. d.mcball (?an k) (1 / Suc 0)))
              + (\<Sum>m. measure M (space M - (\<Union>k\<in>{..<n (Suc m)}. d.mcball (?an k) (1 / Suc (Suc m)))))"
        using suminf_split_initial_segment[OF sum,of 1] by simp
      also have "... < e * (1 / 2)
              + (\<Sum>m. measure M (space M - (\<Union>k\<in>{..<n (Suc m)}. d.mcball (?an k) (1 / Suc (Suc m)))))"
        using n'[of 0] by(simp add: finite_measure_compl)
      also have "... \<le>  e * (1 / 2) + (\<Sum>m. e * (1 / 2) ^ (Suc (Suc m)))"
      proof -
        have "(\<Sum>m. measure M (space M - (\<Union>k\<in>{..<n (Suc m)}. d.mcball (?an k) (1 / Suc (Suc m))))) \<le> (\<Sum>m. e * (1 / 2) ^ (Suc (Suc m)))"
        proof(rule suminf_le)
          fix l
          show "measure M (space M - (\<Union>k<n (Suc l). d.mcball (?an k) (1 / real (Suc (Suc l))))) \<le> e * (1 / 2) ^ Suc (Suc l)"
            using n'[of "Suc l"] by (auto simp: finite_measure_compl)
        qed(use summable_Suc_iff[THEN iffD2,OF sum] in auto)
        thus ?thesis by simp
      qed
      also have "... = e"
        by(simp add: suminf_geometric[of "1 / 2 :: real"] suminf_mult suminf_divide)
      finally show "measure M (space M - K) < e" .
    qed(use K_compact d in auto)
  qed(use finite_measure_axioms assms in auto)
qed

corollary(in finite_measure) inner_regular_Polish:
  assumes "Polish_space X" "sets (borel_of X) = sets M" "A \<in> sets M"
  shows "measure M A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. measure M K)"
  by(auto intro!: tight_on_Polish inner_regular'' simp: assms Polish_space_imp_metrizable_space)

end