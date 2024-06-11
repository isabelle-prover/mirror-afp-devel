(*  Title:   Levy_Prokhorov_Distance.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

section  \<open>The L\'evy-Prokhorov Metric\<close>
theory Levy_Prokhorov_Distance
  imports Lemmas_Levy_Prokhorov "General_Weak_Convergence"
begin

subsection \<open> The L\'evy-Prokhorov Metric\<close>
lemma LPm_ne':
  assumes "finite_measure M" "finite_measure N"
  shows "\<exists>e>0. \<forall>A B C D. measure M A \<le> measure N (B A e) + e \<and> measure N C \<le> measure M (D C e) + e"
proof -
  interpret M: finite_measure M by fact
  interpret N: finite_measure N by fact
  from M.emeasure_real N.emeasure_real obtain m n where mn[arith]:
   "m \<ge> 0" "n \<ge> 0" "M (space M) = ennreal m" "N (space N) = ennreal n"
    by metis
  then have MN:"\<And>A. measure M A \<le> m" "\<And>A. measure N A \<le> n"
    using M.bounded_measure N.bounded_measure measure_eq_emeasure_eq_ennreal by blast+
  show ?thesis
  proof(safe intro!: exI[where x="m+n+1"])
    fix A B C D
    note [arith] = MN(1)[of A] MN(1)[of "D C (m + n + 1)"] MN(2)[of C] MN(2)[of "B A (m + n + 1)"]
    show " measure M A \<le> measure N (B A (m+n+1)) + (m+n+1)" "measure N C \<le> measure M (D C (m+n+1)) + (m+n+1)"
      by(simp_all add: add.commute add_increasing2)
  qed simp
qed

locale Levy_Prokhorov = Metric_space
begin

definition "\<P> \<equiv> {N. sets N = sets (borel_of mtopology) \<and> finite_measure N}"

lemma inP_D:
  assumes "N \<in> \<P>"
  shows "finite_measure N" "sets N = sets (borel_of mtopology)" "space N = M"
  using assms by(auto simp: \<P>_def space_borel_of cong: sets_eq_imp_space_eq)

declare inP_D(2)[measurable_cong]

lemma inP_I: "sets N = sets (borel_of mtopology) \<Longrightarrow> finite_measure N \<Longrightarrow> N \<in> \<P>"
  by(auto simp: \<P>_def)

lemma inP_iff: "N \<in> \<P> \<longleftrightarrow> sets N = sets (borel_of mtopology) \<and> finite_measure N"
  by(simp add: \<P>_def)

lemma M_empty_P:
  assumes "M = {}"
  shows "\<P> = {} \<or> \<P> = {count_space {}}"
proof -
  have "\<And>N. N \<in> \<P> \<Longrightarrow> N = count_space {}"
    by (simp add: assms inP_D(3) space_empty)
  thus ?thesis
    by blast
qed

lemma M_empty_P':
  assumes "M = {}"
  shows "\<P> = {} \<or> \<P> = {null_measure (borel_of mtopology)}"
  by (metis inP_D(2) singletonI space_count_space space_empty space_empty_iff space_null_measure M_empty_P[OF assms])

lemma inP_mweak_conv_fin_all:
  assumes "\<And>i. Ni i \<in> \<P>" "N \<in> \<P>"
  shows "mweak_conv_fin M d Ni N F"
  using assms inP_D by(auto simp: mweak_conv_fin_def Metric_space_axioms mweak_conv_fin_axioms_def)

lemma inP_mweak_conv_fin:
  assumes "\<forall>\<^sub>F i in F. Ni i \<in> \<P>" "N \<in> \<P>"
  shows "mweak_conv_fin M d Ni N F"
  using assms inP_D by(auto simp: mweak_conv_fin_def Metric_space_axioms mweak_conv_fin_axioms_def
      intro!: eventually_mono[OF assms(1)])

definition LPm :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> real" where
"LPm N L \<equiv>
   if N \<in> \<P> \<and> L \<in> \<P> then
     (\<Sqinter> {e. e > 0 \<and> (\<forall>A\<in>sets (borel_of mtopology).
                        measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e \<and>
                        measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e)})
   else 0"

lemma bdd_below_Levy_Prokhorov:
 "bdd_below {e. e > 0 \<and> (\<forall>A\<in>sets (borel_of mtopology).
                              measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e \<and>
                              measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e)}"
  by(auto intro!: bdd_belowI[where m=0])

lemma LPm_ne:
  assumes "N \<in> \<P>" "L \<in> \<P>"
  shows "{e. e > 0 \<and> (\<forall>A\<in>sets (borel_of mtopology).
                          measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e \<and>
                          measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e)}
          \<noteq> {}"
proof -
  from LPm_ne'[OF inP_D(1)[OF assms(1)] inP_D(1)[OF assms(2)]]
  show ?thesis by fastforce
qed

lemma LPm_imp_le:
  assumes "e > 0"
      and "\<And>B. B \<in> sets (borel_of mtopology) \<Longrightarrow> measure L B \<le> measure N (\<Union>a\<in>B. mball a e) + e"
      and "\<And>B. B \<in> sets (borel_of mtopology) \<Longrightarrow> measure N B \<le> measure L (\<Union>a\<in>B. mball a e) + e"
    shows "LPm L N \<le> e"
proof -
  consider "L \<notin> \<P>" | "N \<notin> \<P>" | "L \<in> \<P>" "N \<in> \<P>" by auto
  then show ?thesis
  proof cases
    case 3
    show ?thesis
      by(auto simp add: LPm_def 3 intro!: cINF_lower[where f=id,simplified] assms bdd_belowI[where m=0])
  qed(insert assms,simp_all add: LPm_def)
qed

lemma LPm_le_max_measure: "LPm L N \<le> max (measure L (space L)) (measure N (space N))"
proof -
  consider "N \<notin> \<P>" | "L \<notin> \<P>"
    | "max (measure L (space L)) (measure N (space N)) = 0" "L \<in> \<P>" "N \<in> \<P>"
    | "max (measure L (space L)) (measure N (space N)) > 0" "L \<in> \<P>" "N \<in> \<P>"
    by (metis less_max_iff_disj max.idem zero_less_measure_iff)
  then show ?thesis
  proof cases
    assume h: "L \<in> \<P>" "N \<in> \<P>" "max (measure L (space L)) (measure N (space N)) = 0"
    interpret L: finite_measure L
      using h by(auto dest: inP_D)
    interpret N: finite_measure N
      using h by(auto dest: inP_D)
    have measureL:"\<And>A. measure L A = 0"
      by (metis L.bounded_measure h(3) max.absorb1 max.commute max.left_idem measure_nonneg)
    have measureN:"\<And>A. measure N A = 0"
      by (metis N.bounded_measure h(3) max.absorb1 max.commute max.left_idem measure_nonneg)
    have "\<And>e. e > 0 \<Longrightarrow> LPm L N \<le> e"
      by(auto intro!: LPm_imp_le simp: measureL measureN)
    thus ?thesis
      by(simp add: h(3) field_le_epsilon)
  next
    assume h:"max (measure L (space L)) (measure N (space N)) > 0" (is "?a > 0") "L \<in> \<P>" "N \<in> \<P>"
    interpret L: finite_measure L
      using h by(auto dest: inP_D)
    interpret N: finite_measure N
      using h by(auto dest: inP_D)
    have "\<And>B. B \<in> sets (borel_of mtopology) \<Longrightarrow> measure L B \<le> measure N (\<Union>a\<in>B. mball a ?a) + ?a"
      using L.bounded_measure by(auto intro!: add_increasing max.coboundedI1)
    moreover have "\<And>B. B \<in> sets (borel_of mtopology) \<Longrightarrow> measure N B \<le> measure L (\<Union>a\<in>B. mball a ?a) + ?a"
      using N.bounded_measure by(auto intro!: add_increasing max.coboundedI2)
    ultimately show ?thesis
      by(auto intro!: LPm_imp_le h)
  qed(simp_all add: LPm_def max_def)
qed

lemma LPm_less_then:
  assumes "N \<in> \<P>" and "L \<in> \<P>"
      and "LPm N L < e" "A \<in> sets (borel_of mtopology)"
    shows "measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e" "measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e"
proof -
  have sets_NL: "sets (borel_of mtopology) = sets N" "sets (borel_of mtopology) = sets L"
    using assms by (auto simp: inP_D)
  interpret L: finite_measure L
    by (simp add: assms(2) inP_D)
  interpret N: finite_measure N
    by (simp add: assms(1) inP_D)
  have "\<Sqinter> {e. e > 0 \<and> (\<forall>A\<in>sets (borel_of mtopology).
                            measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e \<and>
                            measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e)} < e"
    using assms by(simp add: LPm_def)
  from cInf_less_iff[THEN iffD1,OF LPm_ne[OF assms(1,2)] bdd_below_Levy_Prokhorov this]
  obtain e' where e':
  "e' > 0" "\<And>A. A \<in> sets (borel_of mtopology) \<Longrightarrow> measure N A \<le> measure L (\<Union>a\<in>A. mball a e') + e'"
  "\<And>A. A \<in> sets (borel_of mtopology) \<Longrightarrow> measure L A \<le> measure N (\<Union>a\<in>A. mball a e') + e'" "e' < e"
    by auto
  have "measure N A \<le> measure L (\<Union>a\<in>A. mball a e') + e'"
    by(auto intro!: e' assms)
  also have "... \<le> measure L (\<Union>a\<in>A. mball a e') + e"
    using e' by auto
  also have "... \<le> measure L (\<Union>a\<in>A. mball a e) + e"
    using sets.sets_into_space[OF assms(4)] mball_subset_concentric[of e' e] e'
    by(auto intro!: L.finite_measure_mono borel_of_open simp: space_borel_of sets_NL(2)[symmetric])
  finally show "measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e" .
  have "measure L A \<le> measure N (\<Union>a\<in>A. mball a e') + e'"
    by(auto intro!: e' assms)
  also have "... \<le> measure N (\<Union>a\<in>A. mball a e') + e"
    using e' by auto
  also have "... \<le> measure N (\<Union>a\<in>A. mball a e) + e"
    using sets.sets_into_space[OF assms(4)] mball_subset_concentric[of e' e] e'
    by(auto intro!: N.finite_measure_mono borel_of_open simp: space_borel_of sets_NL(1)[symmetric])
  finally show "measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e" .
qed

lemma LPm_nonneg:"0 \<le> LPm N L"
  by(auto simp: LPm_def le_cInf_iff[OF LPm_ne bdd_below_Levy_Prokhorov])

lemma LPm_open: "LPm L N = (if L \<in> \<P> \<and> N \<in> \<P> then
                              (\<Sqinter> {e. e > 0 \<and> (\<forall>A\<in>{U. openin mtopology U}.
                                                   measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e \<and>
                                                   measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e)})
                            else 0)"
proof -
  {
    assume LN:"L \<in> \<P>" "N \<in> \<P>"
    then have "finite_measure L" "finite_measure N"
      and sets_MN[measurable_cong]:"sets (borel_of mtopology) = sets L" "sets (borel_of mtopology) = sets N"
      by(auto dest: inP_D)
    interpret L: finite_measure L by fact
    interpret N: finite_measure N by fact
    have "\<Sqinter> {e. 0 < e \<and> (\<forall>A\<in>sets (borel_of mtopology).
            measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e \<and> measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e)} =
          \<Sqinter> {e. 0 < e \<and> (\<forall>A. openin mtopology A \<longrightarrow>
            measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e \<and> measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e)}"
      (is "?lhs = ?rhs")
    proof(rule order.antisym)
      show "?rhs \<le> ?lhs"
        using LPm_ne[OF LN] by(auto intro!: cInf_superset_mono bdd_belowI[where m=0] dest: borel_of_open)
    next
      have ball_sets[measurable]: "\<And>A e. (\<Union>a\<in>A. mball a e) \<in> sets L"  "\<And>A e. (\<Union>a\<in>A. mball a e) \<in> sets N"
        by(auto simp: sets_MN[symmetric])
      show "?lhs \<le> ?rhs"
      proof(safe intro!: cInf_le_iff_less[where f=id,simplified,THEN iffD2])
        have ne:"{e. 0 < e \<and> (\<forall>A. openin mtopology A
                     \<longrightarrow> measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e \<and>
                         measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e)} \<noteq> {}"
          using LPm_ne'[OF L.finite_measure_axioms N.finite_measure_axioms] by fastforce
        fix y
        assume "y > ?rhs"
        from cInf_lessD[OF ne this] obtain x where x: "x < y" "0 < x"
          "\<And>A. openin mtopology A \<Longrightarrow> measure L A \<le> measure N (\<Union>a\<in>A. mball a x) + x"
          "\<And>A. openin mtopology A \<Longrightarrow> measure N A \<le> measure L (\<Union>a\<in>A. mball a x) + x"
          by auto
        define x' where "x' \<equiv> x + (y - x) / 2"
        have x'1: "x' > 0" "x < x'"
          using x(1,2) by(auto simp: x'_def add_pos_pos)
        with mball_subset_concentric[of x x'] have x'2: "measure L A \<le> measure N (\<Union>a\<in>A. mball a x') + x'"
          "measure N A \<le> measure L (\<Union>a\<in>A. mball a x') + x'" if "openin mtopology A" for A
          by(auto intro!: order.trans[OF x(3)[OF that]] order.trans[OF x(4)[OF that]]
                          add_mono N.finite_measure_mono L.finite_measure_mono)
        show "\<exists>i\<in>{e. 0 < e \<and> (\<forall>A\<in>sets (borel_of mtopology).
                                   measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e \<and>
                                   measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e)}. i \<le> y"
        proof(safe intro!: bexI[where x=y])
          fix A
          assume A:"A \<in> sets (borel_of mtopology)"
          then have [measurable]: "A \<in> sets L" "A \<in> sets N"
            by(auto simp: sets_MN[symmetric])
          have "measure L A = \<Sqinter> (measure L ` {C. openin mtopology C \<and> A \<subseteq> C})"
            by(simp add: L.outer_regularD[OF L.outer_regular'[OF metrizable_space_mtopology sets_MN(1)]])
          also have "... \<le> \<Sqinter> {measure N (\<Union>c\<in>C. mball c x') + x' |C. openin mtopology C \<and> A \<subseteq> C}"
            using sets.sets_into_space[OF A]
            by(auto intro!: cInf_mono x'2 bdd_belowI[where m=0] simp: space_borel_of)
          also have "... \<le> measure N (\<Union>a\<in>(\<Union>a\<in>A. mball a ((y-x)/2)). mball a x') + x'"
          proof(safe intro!: cInf_lower bdd_belowI[where m=0])
            have "A \<subseteq> (\<Union>a\<in>A. mball a ((y-x)/2))"
              using x(1) sets.sets_into_space[OF A] by(fastforce simp: space_borel_of)
            thus "\<exists>C. measure N (\<Union>b\<in>(\<Union>a\<in>A. mball a ((y - x) / 2)). mball b x') + x'
                      = measure N (\<Union>c\<in>C. mball c x') + x' \<and> openin mtopology C \<and> A \<subseteq> C"
              by(auto intro!: exI[where x="\<Union>a\<in>A. mball a ((y-x)/2)"])
          qed(use measure_nonneg x'1 in auto)
          also have "... \<le> measure N (\<Union>a\<in>A. mball a ((y-x)/2 + x')) + x'"
            using nbh_add[of x' "(y-x)/2" A] by(auto intro!: N.finite_measure_mono)
          also have "... = measure N (\<Union>a\<in>A. mball a y) + x'"
            by(auto simp: x'_def)
          also have "... \<le>  measure N (\<Union>a\<in>A. mball a y) + y"
            using x(1,2)
            by(auto simp: x'_def intro!: order.trans[OF le_add_same_cancel1[of "x+(y-x)/2" "(y-x)/2",THEN iffD2]])
          finally show "measure L A \<le> measure N (\<Union>a\<in>A. mball a y) + y" .
          have "measure N A = \<Sqinter> (measure N ` {C. openin mtopology C \<and> A \<subseteq> C})"
            by(simp add: N.outer_regularD[OF N.outer_regular'[OF metrizable_space_mtopology  sets_MN(2)]])
          also have "... \<le> \<Sqinter> {measure L (\<Union>c\<in>C. mball c x') + x' |C.  openin mtopology C \<and> A \<subseteq> C}"
            using sets.sets_into_space[OF A]
            by(auto intro!: cInf_mono x'2 bdd_belowI[where m=0] simp: space_borel_of)
          also have "... \<le> measure L (\<Union>a\<in>(\<Union>a\<in>A. mball a ((y-x)/2)). mball a x') + x'"
          proof(safe intro!: cInf_lower bdd_belowI[where m=0])
            have "A \<subseteq> (\<Union>a\<in>A. mball a ((y-x)/2))"
              using x(1) sets.sets_into_space[OF A] by(fastforce simp: space_borel_of)
            thus "\<exists>C. measure L (\<Union>b\<in>\<Union>a\<in>A. mball a ((y - x) / 2). mball b x') + x'
                     = measure L (\<Union>c\<in>C. mball c x') + x' \<and> openin mtopology C \<and> A \<subseteq> C"
              by(auto intro!: exI[where x="\<Union>a\<in>A. mball a ((y-x)/2)"])
          qed(use measure_nonneg x'1 in auto)
          also have "... \<le> measure L (\<Union>a\<in>A. mball a ((y-x)/2 + x')) + x'"
            using nbh_add[of x' "(y-x)/2" A] by(auto intro!: L.finite_measure_mono)
          also have "... = measure L (\<Union>a\<in>A. mball a y) + x'"
            by(auto simp: x'_def)
          also have "... \<le>  measure L (\<Union>a\<in>A. mball a y) + y"
            using x(1,2)
            by(auto simp: x'_def intro!: order.trans[OF le_add_same_cancel1[of "x+(y-x)/2" "(y-x)/2",THEN iffD2]])
          finally show "measure N A \<le> measure L (\<Union>a\<in>A. mball a y) + y" .
        qed(use x in auto)
      qed(insert LPm_ne[OF LN], auto intro!: bdd_belowI[where m=0])
    qed
  }
  thus ?thesis
    by (auto simp: LPm_def)
qed

lemma LPm_closed: "LPm L N = (if L \<in> \<P> \<and> N \<in> \<P> then
                                (\<Sqinter> {e. e > 0 \<and> (\<forall>A\<in>{U. closedin mtopology U}.
                                                    measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e \<and>
                                                    measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e)})
                              else 0)"
proof -
  {
    assume LN:"L \<in> \<P>" "N \<in> \<P>"
    then have "finite_measure L" "finite_measure N"
      and sets_MN[measurable_cong]: "sets (borel_of mtopology) = sets L" "sets (borel_of mtopology) = sets N"
      by(auto dest: inP_D)
    interpret L: finite_measure L by fact
    interpret N: finite_measure N by fact
    have "\<Sqinter> {e. 0 < e \<and> (\<forall>A\<in>sets (borel_of mtopology).
                             measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e \<and>
                             measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e)}
          = \<Sqinter> {e. 0 < e \<and> (\<forall>A. closedin mtopology A \<longrightarrow>
                                 measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e \<and>
                                 measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e)}" (is "?lhs = ?rhs")
    proof(rule order.antisym)
      show "?rhs \<le> ?lhs"
        using LPm_ne[OF LN] by(auto intro!: cInf_superset_mono bdd_belowI[where m=0] dest: borel_of_closed)
    next
      have ball_sets[measurable]: "\<And>A e. (\<Union>a\<in>A. mball a e) \<in> sets L"  "\<And>A e. (\<Union>a\<in>A. mball a e) \<in> sets N"
        by(auto simp: sets_MN[symmetric])
      show "?lhs \<le> ?rhs"
      proof(safe intro!: cInf_le_iff_less[where f=id,simplified,THEN iffD2])
        have ne:"{e. 0 < e \<and> (\<forall>A. closedin mtopology A \<longrightarrow> measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e
                                   \<and> measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e)} \<noteq> {}"
          using LPm_ne'[OF L.finite_measure_axioms N.finite_measure_axioms] by fastforce
        fix y
        assume "y > ?rhs"
        from cInf_lessD[OF ne this] obtain x where x: "x < y" "0 < x"
          "\<And>A. closedin mtopology A \<Longrightarrow> measure L A \<le> measure N (\<Union>a\<in>A. mball a x) + x"
          "\<And>A. closedin mtopology A \<Longrightarrow> measure N A \<le> measure L (\<Union>a\<in>A. mball a x) + x"
          by auto
        define x' where "x' \<equiv> x + (y - x) / 2"
        have x'1: "x' > 0" "x < x'"
          using x(1,2) by(auto simp: x'_def add_pos_pos)
        with mball_subset_concentric[of x x']
        have x'2: "measure L A \<le> measure N (\<Union>a\<in>A. mball a x') + x'" "measure N A \<le> measure L (\<Union>a\<in>A. mball a x') + x'"
          if "closedin mtopology A" for A
          by(auto intro!: order.trans[OF x(3)[OF that]] order.trans[OF x(4)[OF that]]
                          add_mono N.finite_measure_mono L.finite_measure_mono)
        show "\<exists>i\<in>{e. 0 < e \<and> (\<forall>A\<in>sets (borel_of mtopology). measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e \<and>
                                      measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e)}. i \<le> y"
        proof(safe intro!: bexI[where x=y])
          fix A
          assume A:"A \<in> sets (borel_of mtopology)"
          then have [measurable]: "A \<in> sets L" "A \<in> sets N"
            by(auto simp: sets_MN[symmetric])
          have "measure L A = (\<Squnion> (measure L ` {C. closedin mtopology C \<and> C \<subseteq> A}))"
            by(simp add: L.inner_regularD[OF L.inner_regular'[OF metrizable_space_mtopology sets_MN(1)]])
          also have "... \<le> (\<Squnion> {measure N (\<Union>c\<in>C. mball c x') + x' |C. closedin mtopology C \<and> C \<subseteq> A})"
            using sets.sets_into_space[OF A]
            by(auto intro!: cSup_mono x'2 bdd_aboveI[where M="measure N (space N) + x'"] N.bounded_measure
                      simp: space_borel_of)
          also have "... \<le> measure N (\<Union>a\<in>(\<Union>a\<in>A. mball a ((y-x)/2)). mball a x') + x'"
          proof(safe intro!: cSup_le_iff[THEN iffD2] bdd_aboveI[where M="measure N (space N) + x'"])
            fix C
            assume "C \<subseteq> A"
            then have "(\<Union>c\<in>C. mball c x') \<subseteq> (\<Union>b\<in>\<Union>a\<in>A. mball a ((y - x) / 2). mball b x')"
              using x'1(2) x'_def by fastforce
            thus "measure N (\<Union>c\<in>C. mball c x') + x' \<le> measure N (\<Union>b\<in>\<Union>a\<in>A. mball a ((y - x) / 2). mball b x') + x'"
              by (metis N.finite_measure_mono add.commute add_le_cancel_left ball_sets(2))
          qed(auto intro!: N.bounded_measure)
          also have "... \<le> measure N (\<Union>a\<in>A. mball a ((y-x)/2 + x')) + x'"
            using nbh_add[of x' "(y-x)/2" A] by(auto intro!: N.finite_measure_mono)
          also have "... = measure N (\<Union>a\<in>A. mball a y) + x'"
            by(auto simp: x'_def)
          also have "... \<le>  measure N (\<Union>a\<in>A. mball a y) + y"
            using x(1,2)
            by(auto simp: x'_def intro!: order.trans[OF le_add_same_cancel1[of "x+(y-x)/2" "(y-x)/2",THEN iffD2]])
          finally show "measure L A \<le> measure N (\<Union>a\<in>A. mball a y) + y" .
          have "measure N A = \<Squnion> (measure N ` {C. closedin mtopology C \<and> C \<subseteq> A})"
            by(simp add: N.inner_regularD[OF N.inner_regular'[OF metrizable_space_mtopology  sets_MN(2)]])
          also have "... \<le> \<Squnion> {measure L (\<Union>c\<in>C. mball c x') + x' |C.  closedin mtopology C \<and> C \<subseteq> A}"
            using sets.sets_into_space[OF A]
            by(auto intro!: cSup_mono x'2 bdd_aboveI[where M="measure L (space L) + x'"] L.bounded_measure
                      simp: space_borel_of)
          also have "... \<le> measure L (\<Union>a\<in>(\<Union>a\<in>A. mball a ((y-x)/2)). mball a x') + x'"
          proof(safe intro!: cSup_le_iff[THEN iffD2] bdd_aboveI[where M="measure L (space L) + x'"])
            fix C
            assume "C \<subseteq> A"
            then have "(\<Union>c\<in>C. mball c x') \<subseteq> (\<Union>b\<in>\<Union>a\<in>A. mball a ((y - x) / 2). mball b x')"
              using x'1(2) x'_def by fastforce
            thus "measure L (\<Union>c\<in>C. mball c x') + x' \<le> measure L (\<Union>b\<in>\<Union>a\<in>A. mball a ((y - x) / 2). mball b x') + x'"
              by (metis L.finite_measure_mono add.commute add_le_cancel_left ball_sets(1))
          qed(auto intro!: L.bounded_measure)
          also have "... \<le> measure L (\<Union>a\<in>A. mball a ((y-x)/2 + x')) + x'"
            using nbh_add[of x' "(y-x)/2" A] by(auto intro!: L.finite_measure_mono)
          also have "... = measure L (\<Union>a\<in>A. mball a y) + x'"
            by(auto simp: x'_def)
          also have "... \<le>  measure L (\<Union>a\<in>A. mball a y) + y"
            using x(1,2)
            by(auto simp: x'_def intro!: order.trans[OF le_add_same_cancel1[of "x+(y-x)/2" "(y-x)/2",THEN iffD2]])
          finally show "measure N A \<le> measure L (\<Union>a\<in>A. mball a y) + y" .
        qed(use x in auto)
      qed(insert LPm_ne[OF LN], auto intro!:  bdd_belowI[where m=0])
    qed
  }
  thus ?thesis
    by (auto simp: LPm_def)
qed

lemma LPm_compact:
  assumes "separable_space mtopology" mcomplete
  shows "LPm L N = (if L \<in> \<P> \<and> N \<in> \<P> then
                       (\<Sqinter> {e. e > 0 \<and> (\<forall>A\<in>{U. compactin mtopology U}.
                                            measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e \<and>
                                            measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e)})
                    else 0)"
proof -
  {
    assume LN:"L \<in> \<P>" "N \<in> \<P>"
    then have "finite_measure L" "finite_measure N"
      and sets_MN[measurable_cong]: "sets (borel_of mtopology) = sets L" "sets (borel_of mtopology) = sets N"
      by(auto dest: inP_D)
    interpret L: finite_measure L by fact
    interpret N: finite_measure N by fact
    have measureL:"A \<in> sets L \<Longrightarrow> measure L A = (\<Squnion>K\<in>{K. compactin mtopology K \<and> K \<subseteq> A}. measure L K)"
      and measureN: "A \<in> sets N \<Longrightarrow> measure N A = (\<Squnion>K\<in>{K. compactin mtopology K \<and> K \<subseteq> A}. measure N K)" for A
      by(auto intro!: inner_regular'' L.tight_on_Polish N.tight_on_Polish Polish_space_mtopology assms
                simp: sets_MN[symmetric] metrizable_space_mtopology)
    have "\<Sqinter> {e. 0 < e \<and> (\<forall>A\<in>sets (borel_of mtopology).
                               measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e \<and>
                               measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e)}
          = \<Sqinter> {e. 0 < e \<and> (\<forall>A. compactin mtopology A \<longrightarrow>
                                  measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e \<and>
                                  measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e)}" (is "?lhs = ?rhs")
    proof(rule order.antisym)
      show "?rhs \<le> ?lhs"
        using LPm_ne[OF LN] by(auto intro!: cInf_superset_mono bdd_belowI[where m=0]
            dest: borel_of_compact[OF Hausdorff_space_mtopology])
    next
      have ball_sets[measurable]: "\<And>A e. (\<Union>a\<in>A. mball a e) \<in> sets L"  "\<And>A e. (\<Union>a\<in>A. mball a e) \<in> sets N"
        by(auto simp: sets_MN[symmetric])
      show "?lhs \<le> ?rhs"
      proof(safe intro!: cInf_le_iff_less[where f=id,simplified,THEN iffD2])
        have ne:"{e. 0 < e \<and> (\<forall>A. compactin mtopology A \<longrightarrow>
                                      measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e \<and>
                                      measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e)} \<noteq> {}"
          using LPm_ne'[OF L.finite_measure_axioms N.finite_measure_axioms] by fastforce
        fix y
        assume "y > ?rhs"
        from cInf_lessD[OF ne this] obtain x where x: "x < y" "0 < x"
          "\<And>A. compactin mtopology A \<Longrightarrow> measure L A \<le> measure N (\<Union>a\<in>A. mball a x) + x"
          "\<And>A. compactin mtopology A \<Longrightarrow> measure N A \<le> measure L (\<Union>a\<in>A. mball a x) + x"
          by auto
        define x' where "x' \<equiv> x + (y - x) / 2"
        have x'1: "x' > 0" "x < x'"
          using x(1,2) by(auto simp: x'_def add_pos_pos)
        with mball_subset_concentric[of x x']
        have x'2: "measure L A \<le> measure N (\<Union>a\<in>A. mball a x') + x'" "measure N A \<le> measure L (\<Union>a\<in>A. mball a x') + x'"
          if "compactin mtopology A" for A
          by(auto intro!: order.trans[OF x(3)[OF that]] order.trans[OF x(4)[OF that]]
                          add_mono N.finite_measure_mono L.finite_measure_mono)
        show "\<exists>i\<in>{e. 0 < e \<and> (\<forall>A\<in>sets (borel_of mtopology). measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e \<and>
                                     measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e)}. i \<le> y"
        proof(safe intro!: bexI[where x=y])
          fix A
          assume A:"A \<in> sets (borel_of mtopology)"
          then have [measurable]: "A \<in> sets L" "A \<in> sets N"
            by(auto simp: sets_MN[symmetric])
          have "measure L A = (\<Squnion> (measure L ` {C. compactin mtopology C \<and> C \<subseteq> A}))"
            by(simp add: measureL)
          also have "... \<le> (\<Squnion> {measure N (\<Union>c\<in>C. mball c x') + x' |C. compactin mtopology C \<and> C \<subseteq> A})"
            using sets.sets_into_space[OF A]
            by(auto intro!: cSup_mono x'2 bdd_aboveI[where M="measure N (space N) + x'"] N.bounded_measure
                      simp: space_borel_of)
          also have "... \<le> measure N (\<Union>a\<in>(\<Union>a\<in>A. mball a ((y-x)/2)). mball a x') + x'"
          proof(safe intro!: cSup_le_iff[THEN iffD2] bdd_aboveI[where M="measure N (space N) + x'"])
            fix C
            assume "C \<subseteq> A"
            then have "(\<Union>c\<in>C. mball c x') \<subseteq> (\<Union>b\<in>\<Union>a\<in>A. mball a ((y - x) / 2). mball b x')"
              using x'1(2) x'_def by fastforce
            thus "measure N (\<Union>c\<in>C. mball c x') + x' \<le> measure N (\<Union>b\<in>\<Union>a\<in>A. mball a ((y - x) / 2). mball b x') + x'"
              by (metis N.finite_measure_mono add.commute add_le_cancel_left ball_sets(2))
          qed(auto intro!: N.bounded_measure)
          also have "... \<le> measure N (\<Union>a\<in>A. mball a ((y-x)/2 + x')) + x'"
            using nbh_add[of x' "(y-x)/2" A] by(auto intro!: N.finite_measure_mono)
          also have "... = measure N (\<Union>a\<in>A. mball a y) + x'"
            by(auto simp: x'_def)
          also have "... \<le>  measure N (\<Union>a\<in>A. mball a y) + y"
            using x(1,2)
            by(auto simp: x'_def intro!: order.trans[OF le_add_same_cancel1[of "x+(y-x)/2" "(y-x)/2",THEN iffD2]])
          finally show "measure L A \<le> measure N (\<Union>a\<in>A. mball a y) + y" .
          have "measure N A = \<Squnion> (measure N ` {C. compactin mtopology C \<and> C \<subseteq> A})"
            by(simp add: measureN)
          also have "... \<le> \<Squnion> {measure L (\<Union>c\<in>C. mball c x') + x' |C.  compactin mtopology C \<and> C \<subseteq> A}"
            using sets.sets_into_space[OF A]
            by(auto intro!: cSup_mono x'2 bdd_aboveI[where M="measure L (space L) + x'"] L.bounded_measure
                      simp: space_borel_of)
          also have "... \<le> measure L (\<Union>a\<in>(\<Union>a\<in>A. mball a ((y-x)/2)). mball a x') + x'"
          proof(safe intro!: cSup_le_iff[THEN iffD2] bdd_aboveI[where M="measure L (space L) + x'"])
            fix C
            assume "C \<subseteq> A"
            then have "(\<Union>c\<in>C. mball c x') \<subseteq> (\<Union>b\<in>\<Union>a\<in>A. mball a ((y - x) / 2). mball b x')"
              using x'1(2) x'_def by fastforce
            thus "measure L (\<Union>c\<in>C. mball c x') + x' \<le> measure L (\<Union>b\<in>\<Union>a\<in>A. mball a ((y - x) / 2). mball b x') + x'"
              by (metis L.finite_measure_mono add.commute add_le_cancel_left ball_sets(1))
          qed(auto intro!: L.bounded_measure)
          also have "... \<le> measure L (\<Union>a\<in>A. mball a ((y-x)/2 + x')) + x'"
            using nbh_add[of x' "(y-x)/2" A] by(auto intro!: L.finite_measure_mono)
          also have "... = measure L (\<Union>a\<in>A. mball a y) + x'"
            by(auto simp: x'_def)
          also have "... \<le>  measure L (\<Union>a\<in>A. mball a y) + y"
            using x(1,2)
            by(auto simp: x'_def intro!: order.trans[OF le_add_same_cancel1[of "x+(y-x)/2" "(y-x)/2",THEN iffD2]])
          finally show "measure N A \<le> measure L (\<Union>a\<in>A. mball a y) + y" .
        qed(use x in auto)
      qed(insert LPm_ne[OF LN], auto intro!:  bdd_belowI[where m=0])
    qed
  }
  thus ?thesis
    by (auto simp: LPm_def)
qed

sublocale LPm: Metric_space \<P> LPm
proof
  show "0 \<le> LPm M N" for M N
    by(rule LPm_nonneg)
next
  fix L N
  assume MN:"L \<in> \<P>" "N \<in> \<P>"
  interpret L: finite_measure L
    by(rule inP_D(1)[OF MN(1)])
  interpret N: finite_measure N
    by(rule inP_D(1)[OF MN(2)])
  show "LPm L N = 0 \<longleftrightarrow> L = N"
  proof safe
    have [simp]:"{e. 0 < e \<and> (\<forall>A\<in>sets (borel_of mtopology). measure N A \<le> measure N (\<Union>a\<in>A. mball a e) + e)} = {0<..}"
    proof safe
      fix e :: real and A
      assume h':"e > 0" "A \<in> sets (borel_of mtopology)"
      show "measure N A \<le> measure N (\<Union>a\<in>A. mball a e) + e"
        using nbh_sets[of e A] inP_D(2)[OF MN(2)] sets.sets_into_space[OF h'(2)] h'(1)
        by(auto simp: space_borel_of intro!: order.trans[OF N.finite_measure_mono[OF nbh_subset[of A e]]])
    qed
    show "LPm N N = 0"
      by (simp add: LPm_def)
  next
    assume "LPm L N = 0"
    then have h:"\<And>e'. e' > 0 \<Longrightarrow>
           \<exists>a\<in>{e. 0 < e \<and> (\<forall>A\<in>sets (borel_of mtopology).
                     measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e \<and>
                     measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e)}. a < e'"
      using cInf_le_iff[OF LPm_ne[OF MN] bdd_below_Levy_Prokhorov] by (auto simp: MN LPm_def)
    show "L = N"
    proof(rule measure_eqI_generator_eq[where E="{U. closedin mtopology U}" and A="\<lambda>i. M" and \<Omega>=M])
      show "Int_stable {U. closedin mtopology U}"
        by(auto simp: Int_stable_def)
    next
      show "{U. closedin mtopology U} \<subseteq> Pow M"
        using closedin_metric2 by auto
    next
      show "\<And>X. X \<in> {U. closedin mtopology U} \<Longrightarrow> emeasure L X = emeasure N X"
      proof safe
        fix U
        assume "closedin mtopology U"
        then have US: "U \<subseteq> M"
          by (simp add: closedin_def)
        consider "U = {}" | "U \<noteq> {}" by auto
        then have "measure L U = measure N U"
        proof cases
          case U:2
          define an
            where "an \<equiv> rec_nat (SOME e. 0 < e \<and> e < 1 / Suc 0
                                         \<and> (\<forall>A\<in>sets (borel_of mtopology).
                                                measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e
                                              \<and> measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e))
                                 (\<lambda>n an. SOME e. 0 < e \<and> e < an \<and> e < 1 / Suc (Suc n)
                                                 \<and> (\<forall>A\<in>sets (borel_of mtopology).
                                                    measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e \<and>
                                                    measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e))"
          have an_simp: "an 0 = (SOME e. 0 < e \<and> e < 1 / Suc 0
                                        \<and> (\<forall>A\<in>sets (borel_of mtopology).
                                                measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e \<and>
                                                measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e))"
                   "\<And>n. an (Suc n) = (SOME e. 0 < e \<and> e < (an n) \<and> e < 1 / Suc (Suc n) \<and>
                                                (\<forall>A\<in>sets (borel_of mtopology).
                                                    measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e \<and>
                                                    measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e))"
            by(simp_all add: an_def)
          have *:"an 0 > 0 \<and> an 0 < 1 / Suc 0 \<and>
                   (\<forall>A\<in>sets (borel_of mtopology).
                         measure L A \<le> measure N (\<Union>a\<in>A. mball a (an 0)) + (an 0) \<and>
                         measure N A \<le> measure L (\<Union>a\<in>A. mball a (an 0)) + (an 0))"
            by(simp add: an_simp) (rule someI_ex,use h[of 1] in auto)
          moreover have **:"an n > 0" for n
          proof(induction n)
            case ih:(Suc n)
            have "an (Suc n) > 0 \<and> an (Suc n) < an n \<and> an (Suc n) < 1 / Suc (Suc n) \<and>
                   (\<forall>A\<in>sets (borel_of mtopology).
                         measure L A \<le> measure N (\<Union>a\<in>A. mball a (an (Suc n))) + (an (Suc n)) \<and>
                         measure N A \<le> measure L (\<Union>a\<in>A. mball a (an (Suc n))) + (an (Suc n)))"
              by(simp add: an_simp,rule someI_ex) (use h[of "min (an n) (1 / Suc (Suc n))"] ih in auto)
            thus ?case
              by auto
          qed(use * in auto)
          moreover have "an (Suc n) > 0 \<and> an (Suc n) < an n \<and> an (Suc n) < 1 / Suc (Suc n) \<and>
                           (\<forall>A\<in>sets (borel_of mtopology).
                                measure L A \<le> measure N (\<Union>a\<in>A. mball a (an (Suc n))) + (an (Suc n)) \<and>
                                measure N A \<le> measure L (\<Union>a\<in>A. mball a (an (Suc n))) + (an (Suc n)))" for n
            by(simp add: an_simp,rule someI_ex) (use h[of "min (an n) (1 / Suc (Suc n))"] ** in auto)
          ultimately have "an n > 0 \<and> decseq an \<and> an n < 1 / Suc n \<and>
                            (\<forall>A\<in>sets (borel_of mtopology).
                                measure L A \<le> measure N (\<Union>a\<in>A. mball a (an n)) + (an n) \<and>
                                measure N A \<le> measure L (\<Union>a\<in>A. mball a (an n)) + (an n))" for n
            by(cases n) (auto intro!: decseq_SucI order.strict_implies_order)
          hence an:"\<And>n. an n > 0" "decseq an" "\<And>n. an n < 1 / Suc n"
            "\<And>n A. A\<in>sets (borel_of mtopology) \<Longrightarrow> measure L A \<le> measure N (\<Union>a\<in>A. mball a (an n)) + an n"
            "\<And>n A. A\<in>sets (borel_of mtopology) \<Longrightarrow> measure N A \<le> measure L (\<Union>a\<in>A. mball a (an n)) + an n"
            by auto
          hence an_lim: "an \<longlonglongrightarrow> 0"
            by(auto intro!: LIMSEQ_norm_0 simp: less_eq_real_def)
          have 1:"U \<in> sets (borel_of mtopology)"
            by (simp add: \<open>closedin mtopology U\<close> borel_of_closed)
          have Uint:"(\<Inter>i. \<Union>a\<in>U. mball a (an i)) = U"
            by(simp add: nbh_Inter_closure_of[OF U US an(1,2) an_lim] closure_of_closedin[OF \<open>closedin mtopology U\<close>])
          have "(\<lambda>n. measure L (\<Union>a\<in>U. mball a (an n))) \<longlonglongrightarrow> measure L (\<Inter>i. \<Union>a\<in>U. mball a (an i))"
               "(\<lambda>n. measure N (\<Union>a\<in>U. mball a (an n))) \<longlonglongrightarrow> measure N (\<Inter>i. \<Union>a\<in>U. mball a (an i))"
            by(auto intro!: L.finite_Lim_measure_decseq[OF _ nbh_decseq[OF an(2)]]
                            N.finite_Lim_measure_decseq[OF _ nbh_decseq[OF an(2)]] simp: MN)
          hence MN_lim:"(\<lambda>n. measure L (\<Union>a\<in>U. mball a (an n)) + an n) \<longlonglongrightarrow> measure L U"
            "(\<lambda>n. measure N (\<Union>a\<in>U. mball a (an n)) + an n) \<longlonglongrightarrow> measure N U"
            by(auto simp add: Uint intro!: tendsto_add[OF _ an_lim,simplified])
          show ?thesis
          proof(rule order.antisym)
            show "measure L U \<le> measure N U"
              by(rule Lim_bounded2[OF MN_lim(2)],auto simp: an 1)
          next
            show "measure N U \<le> measure L U"
              by(rule Lim_bounded2[OF MN_lim(1)],auto simp: an 1)
          qed
        qed simp
        thus "emeasure L U = emeasure N U"
          by (simp add: L.emeasure_eq_measure N.emeasure_eq_measure)
      qed
    next
      show "range (\<lambda>i. M) \<subseteq> {U. closedin mtopology U}"
        by simp
    qed (simp_all add: MN sets_borel_of_closed inP_D(2))
  qed
next
  fix M N L
  assume MNL[simp]: "M \<in> \<P>" "N \<in> \<P>" "L \<in> \<P>"
  interpret M: finite_measure M
    by(rule inP_D(1)[OF MNL(1)])
  interpret N: finite_measure N
    by(rule inP_D(1)[OF MNL(2)])
  interpret L: finite_measure L
    by(rule inP_D(1)[OF MNL(3)])
  have ne:"{e1 + e2 |e1 e2. 0 < e1 \<and> 0 < e2 \<and>
                        (\<forall>A\<in>sets (borel_of mtopology).
                            measure M A \<le> measure N (\<Union>a\<in>A. mball a e1) + e1 \<and>
                            measure N A \<le> measure M (\<Union>a\<in>A. mball a e1) + e1 \<and>
                            measure N A \<le> measure L (\<Union>a\<in>A. mball a e2) + e2 \<and>
                            measure L A \<le> measure N (\<Union>a\<in>A. mball a e2) + e2)} \<noteq> {}"
    (is "{e1 + e2 | e1 e2. 0 < e1 \<and> 0 < e2 \<and> ?P e1 e2} \<noteq> {}")
    using N.bounded_measure M.bounded_measure L.bounded_measure
    by(auto intro!: exI[where x="max 1 (max (measure M (space M)) (max (measure L (space L)) (measure N (space N))))"]
                    add_increasing[OF measure_nonneg] simp: le_max_iff_disj)
  show "LPm M L \<le> LPm M N + LPm N L" (is "?lhs \<le> ?rhs")
  proof -
    have "?lhs = \<Sqinter> {e. e > 0 \<and> (\<forall>A\<in>sets (borel_of mtopology).
                                   measure M A \<le> measure L (\<Union>a\<in>A. mball a e) + e \<and>
                                   measure L A \<le> measure M (\<Union>a\<in>A. mball a e) + e)}"
      by(auto simp: LPm_def)
    also have "... \<le> \<Sqinter> {e1 + e2 |e1 e2. 0 < e1 \<and> 0 < e2 \<and> ?P e1 e2}" (is "_ \<le> Inf ?B")
    proof(rule cInf_superset_mono)
      show "?B \<subseteq> {e. e > 0 \<and> (\<forall>A\<in>sets (borel_of mtopology).
                                  measure M A \<le> measure L (\<Union>a\<in>A. mball a e) + e \<and>
                                  measure L A \<le> measure M (\<Union>a\<in>A. mball a e) + e)}"
      proof safe
        fix e1 e2 A
        assume "?P e1 e2"
           and A[measurable]: "A \<in> sets (borel_of mtopology)"
        then have mA:
          "\<And>A. A \<in> sets (borel_of mtopology) \<Longrightarrow> measure M A \<le> measure N (\<Union>a\<in>A. mball a e1) + e1"
          "\<And>A. A \<in> sets (borel_of mtopology) \<Longrightarrow> measure N A \<le> measure M (\<Union>a\<in>A. mball a e1) + e1"
          "\<And>A. A \<in> sets (borel_of mtopology) \<Longrightarrow> measure N A \<le> measure L (\<Union>a\<in>A. mball a e2) + e2"
          "\<And>A. A \<in> sets (borel_of mtopology) \<Longrightarrow> measure L A \<le> measure N (\<Union>a\<in>A. mball a e2) + e2"
          by auto
        show "measure M A \<le> measure L (\<Union>a\<in>A. mball a (e1 + e2)) + (e1 + e2)"
        proof -
          have "measure M A \<le> measure N (\<Union>a\<in>A. mball a e1) + e1"
            by(simp add: mA)
          also have "... \<le> measure L (\<Union>a\<in>(\<Union>a\<in>A. mball a e1). mball a e2) + e2 + e1"
            by(simp add: mA(3)[of "\<Union>a\<in>A. mball a e1",simplified])
          also have "... \<le> measure L (\<Union>a\<in>A. mball a (e1 + e2)) + e2 + e1"
            by(simp add: L.finite_measure_mono[OF nbh_add,simplified])
          finally show ?thesis
            by simp
        qed
        show "measure L A \<le> measure M (\<Union>a\<in>A. mball a (e1 + e2)) + (e1 + e2)"
        proof -
          have "measure L A \<le> measure N (\<Union>a\<in>A. mball a e2) + e2"
            by(simp add: mA)
          also have "... \<le> measure M (\<Union>a\<in>(\<Union>a\<in>A. mball a e2). mball a e1) + e1 + e2"
            by(simp add: mA(2)[of "\<Union>a\<in>A. mball a e2",simplified])
          also have "... \<le>  measure M (\<Union>a\<in>A. mball a (e1 + e2)) + e1 + e2"
            by(simp add:  M.finite_measure_mono[OF nbh_add,simplified] add.commute[of e1])
          finally show ?thesis
            by simp
        qed
      qed simp
    qed (use ne bdd_below_Levy_Prokhorov in auto)
    also have "... \<le> ?rhs"
    proof(rule cInf_le_iff_less[where f=id,simplified,THEN iffD2])
      show "\<forall>y>LPm M N + LPm N L. \<exists>i\<in>{e1 + e2 |e1 e2. 0 < e1 \<and> 0 < e2 \<and> ?P e1 e2}. i \<le> y"
      proof safe
        fix e
        assume h:"LPm M N + LPm N L < e"
        define e' where "e' \<equiv> (e - (LPm M N + LPm N L)) / 2"
        have e'[arith]: "e' > 0"
          using h by(auto simp: e'_def)
        have
          "\<And>y. y>LPm M N \<Longrightarrow> \<exists>i\<in>{e. 0 < e \<and> (\<forall>A\<in>sets (borel_of mtopology).
                                              measure M A \<le> measure N (\<Union>a\<in>A. mball a e) + e \<and>
                                              measure N A \<le> measure M (\<Union>a\<in>A. mball a e) + e)}. i \<le> y"
          "\<And>y. y>LPm N L \<Longrightarrow> \<exists>i\<in>{e. 0 < e \<and> (\<forall>A\<in>sets (borel_of mtopology).
                                              measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e \<and>
                                              measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e)}. i \<le> y"
          using cInf_le_iff_less[where f=id,simplified,OF LPm_ne[OF MNL(2,3)],of "LPm N L"]
            cInf_le_iff_less[where f=id,simplified,OF LPm_ne[OF MNL(1,2)],of "LPm M N"]
          by(simp_all add: LPm_def bdd_below_Levy_Prokhorov)
        from this(1)[of "LPm M N + e'"] this(2)[of "LPm N L + e'"] obtain emn enl
          where emn: "emn > 0" "emn \<le> LPm M N + e'"
            "\<And>A. A \<in> sets (borel_of mtopology) \<Longrightarrow> measure M A \<le> measure N (\<Union>a\<in>A. mball a emn) + emn"
            "\<And>A. A \<in> sets (borel_of mtopology) \<Longrightarrow> measure N A \<le> measure M (\<Union>a\<in>A. mball a emn) + emn"
            and enl: "enl > 0" "enl \<le> LPm N L + e'"
            "\<And>A. A \<in> sets (borel_of mtopology) \<Longrightarrow> measure N A \<le> measure L (\<Union>a\<in>A. mball a enl) + enl"
            "\<And>A. A \<in> sets (borel_of mtopology) \<Longrightarrow> measure L A \<le> measure N (\<Union>a\<in>A. mball a enl) + enl"
          by auto
        hence "emn + enl \<le> e"
          by(auto intro!: order.trans[of "emn + enl" "LPm M N + e' + (LPm N L + e')" e])
            (auto simp: e'_def diff_divide_distrib)
        show "\<exists>i\<in>{e1 + e2 |e1 e2. 0 < e1 \<and> 0 < e2 \<and> ?P e1 e2}. i \<le> e"
          apply(rule bexI[where x="emn + enl"])
           apply fact
          apply standard
          apply(rule exI[where x="emn"])
          apply(rule exI[where x="enl"])
          apply(use emn enl in auto)
          done
      qed
    qed(insert ne,auto intro!: bdd_belowI[of _ 0])
    finally show ?thesis .
  qed
qed(simp add: LPm_def, meson)

subsection \<open> Convervence and Weak Convergence \<close>
lemma converge_imp_mweak_conv:
  assumes "limitin LPm.mtopology Ni N F"
  shows "mweak_conv Ni N F"
proof(cases "F = \<bottom>")
  assume F: "F \<noteq> \<bottom>"
  have h: "N \<in> \<P>" "((\<lambda>n. LPm (Ni n) N) \<longlongrightarrow> 0) F" "\<forall>\<^sub>F i in F. Ni i \<in> \<P>"
    using LPm.limitin_metric_dist_null assms(1) by auto
  interpret N: finite_measure N
    using h by(auto simp: inP_D)
  interpret mweak_conv_fin M d Ni N
    by(auto intro!: h inP_mweak_conv_fin assms)
  show ?thesis
    unfolding mweak_conv_eq2
  proof safe
    show "((\<lambda>n. measure (Ni n) M) \<longlongrightarrow> measure N M) F"
      unfolding tendsto_iff dist_real_def
    proof safe
      fix r :: real
      assume r: "0 < r"
      from half_gt_zero[OF this] h(2)
      have 1:"\<forall>\<^sub>F n in F. LPm (Ni n) N < r / 2"
        unfolding tendsto_iff dist_real_def LPm.nonneg by fastforce
      show "\<forall>\<^sub>F n in F. \<bar>measure (Ni n) M - measure N M\<bar> < r"
      proof(safe intro!: eventually_mono[OF eventually_conj[OF h(3) 1]])
        fix n
        assume n: "LPm (Ni n) N < r / 2" "Ni n \<in> \<P>"
        have [simp]:"(\<Union>a\<in>M. mball a (r / 2)) = M"
          using r by auto
        have [measurable]: "M \<in> sets (borel_of mtopology)"
          by(auto intro!: borel_of_open)
        have "measure (Ni n) M \<le> measure N M + r / 2" "measure N M \<le> measure (Ni n) M + r / 2"
          using LPm_less_then[OF _ _ n(1),of M] h(1) n(2)  by auto
        hence "\<bar>measure (Ni n) M -measure N M\<bar> \<le> r / 2"
          by linarith
        also have "... < r"
          using r by auto
        finally show "\<bar>measure (Ni n) M -measure N M\<bar> < r" .
      qed
    qed
  next
    define bn where "bn \<equiv> (\<lambda>n. LPm (Ni n) N)"
    have bn_nonneg:"\<And>n. bn n \<ge> 0"
      by(auto simp: bn_def)
    have bn_tendsto:"(bn \<longlongrightarrow> 0) F"
      using h(2) by(auto simp: bn_def)
    fix A
    assume A:"closedin mtopology A"
    then have A_meas[measurable]:"A \<in> sets (borel_of mtopology)"
      by(simp add: borel_of_closed)
    show "Limsup F (\<lambda>x. measure (Ni x) A) \<le> (measure N A)"
    proof(cases "A = {}")
      assume A_ne:"A \<noteq> {}"
      have bdd:"Limsup F (\<lambda>n. measure (Ni n) A) \<le>(measure N (\<Union>a\<in>A. mball a (2 / Suc m))) + 1 / Suc m" for m
      proof -
        have "Limsup F (\<lambda>n. measure (Ni n) A)
               \<le> Limsup F (\<lambda>n. measure N (\<Union>a\<in>A. mball a (bn n + 1 / Suc m)) + ereal (bn n + 1 / Suc m))"
          by(auto intro!: Limsup_mono eventually_mono[OF h(3)] LPm_less_then(1)[OF _ h(1)] simp: bn_def)
        also have "... \<le> Limsup F (\<lambda>n. measure N (\<Union>a\<in>A. mball a (bn n + 1 / Suc m))) + Limsup F (\<lambda>n. bn n + 1 / Suc m)"
          by(rule ereal_Limsup_add_mono)
        also have "... = Limsup F (\<lambda>n. measure N (\<Union>a\<in>A. mball a (bn n + 1 / Suc m))) + 1 / Suc m"
          using Limsup_add_ereal_right[OF F,of  "1 / Suc m" bn]
          by(simp add: lim_imp_Limsup[OF F tendsto_ereal[OF bn_tendsto]])
        also have "... \<le> ereal (measure N (\<Union>a\<in>A. mball a (2 / Suc m))) + 1 / Suc m"
        proof -
          have "Limsup F (\<lambda>n. measure N (\<Union>a\<in>A. mball a (bn n + 1 / Suc m))) \<le> measure N (\<Union>a\<in>A. mball a (2 / Suc m))"
            using bn_nonneg
            by(fastforce intro!: Limsup_bounded eventuallyI[THEN eventually_mp[OF _ tendstoD[OF bn_tendsto,of "1 / Suc m"]]]
                                 N.finite_measure_mono)
          thus ?thesis
            using add_mono by blast
        qed
        finally show ?thesis by simp
      qed
      have lim:"(\<lambda>m. ereal ((measure N (\<Union>a\<in>A. mball a (2 / Suc m))) + 1 / Suc m)) \<longlonglongrightarrow> measure N A"
      proof(safe intro!: tendsto_ereal[where x="measure N A"] tendsto_add[where b=0,simplified])
        show "(\<lambda>m. measure N (\<Union>a\<in>A. mball a (2 / Suc m))) \<longlonglongrightarrow> measure N A"
        proof -
          have 1:"(\<Inter>m. (\<Union>a\<in>A. mball a (2 / Suc m))) = A"
            using tendsto_mult[OF tendsto_const[of 2] LIMSEQ_Suc[OF lim_inverse_n']] closedin_subset[OF A]
            by(intro nbh_Inter_closure_of[OF A_ne,simplified closure_of_closedin[OF A]] decseq_SucI)
              (auto simp: frac_le)
          have "(\<lambda>m. measure N (\<Union>a\<in>A. mball a (2 / Suc m))) \<longlonglongrightarrow> measure N (\<Inter>m. (\<Union>a\<in>A. mball a (2 / Suc m)))"
            by(auto intro!: N.finite_Lim_measure_decseq nbh_decseq[OF decseq_SucI] simp: frac_le)
          thus ?thesis
            unfolding 1 .
        qed
      qed(rule LIMSEQ_Suc[OF lim_inverse_n'])
      show ?thesis
        using bdd by(auto intro!: Lim_bounded2[OF lim])
    qed(simp add: Limsup_const[OF F])
  qed
next
  show "F = \<bottom> \<Longrightarrow> mweak_conv Ni N F"
    using limitin_topspace[OF assms(1)] by(auto simp: inP_D mweak_conv_def)
qed

lemma mweak_conv_imp_converge:
  assumes "separable_space mtopology"
    and "mweak_conv Ni N F"
  shows "limitin LPm.mtopology Ni N F"
proof -
  have in_P:"\<forall>\<^sub>F i in F. Ni i \<in> \<P>" "N \<in> \<P>"
    using limitin_topspace[OF assms(2)]
    by(fastforce intro!: eventually_mono[OF limitinD[OF assms(2),
    of "topspace (weak_conv_topology mtopology)",OF openin_topspace limitin_topspace[OF assms(2)]]] inP_I)+
  consider "M = {}" | "F = \<bottom>" | "M \<noteq> {}" "F \<noteq> \<bottom>"
    by blast
  thus ?thesis
  proof cases
    case 1
    then have 2:"sets (borel_of mtopology) = {{}}"
      by (metis space_borel_of space_empty_iff topspace_mtopology)
    have "\<forall>\<^sub>F i in F. space (Ni i) = M" "space N = M"
      using inP_D in_P
      by(auto intro!: eventually_mono[OF in_P(1)] cong: sets_eq_imp_space_eq simp: space_borel_of)
    then have "\<forall>\<^sub>F i in F. Ni i = count_space {}" "N = count_space {}"
      using 1 by(auto simp: space_empty eventually_mono)      
    thus ?thesis
      by(auto intro!: limitin_eventually inP_I finite_measureI simp: 2)
  next
    show "F = \<bottom> \<Longrightarrow> limitin LPm.mtopology Ni N F"
      using limitin_topspace[OF assms(2)] by(auto intro!: limitin_trivial inP_I)
  next
    assume M_ne:"M \<noteq> {}" and F:"F \<noteq> \<bottom>"
    show ?thesis
      unfolding LPm.limitin_metric_dist_null dist_real_def tendsto_iff
    proof safe
      interpret mweak_conv_fin M d Ni N F
        by(auto intro!: inP_mweak_conv_fin in_P)
      have M[measurable]: "M \<in> sets N" "\<forall>\<^sub>F i in F. M \<in> sets (Ni i)"
        by(auto simp: sets_N borel_of_open eventually_mono[OF sets_Ni])
      fix r :: real
      assume r[arith]: "0 < r"
      interpret N: finite_measure N
        using in_P by(auto simp: inP_D)
      define r' where "r' \<equiv> r / 5"
      have r'[arith]: "r' \<le> r" "0 < r'"
        by(auto simp: r'_def)
      obtain ai ri where airi: "(\<Union>i. mball (ai i) (ri i)) = M" "(\<Union>i. mcball (ai i) (ri i)) = M"
        "\<And>i::nat. ai i \<in> M" "\<And>i. 0 < ri i" "\<And>i. ri i < r' / 2"
        "\<And>i. measure N (mtopology frontier_of mball (ai i) (ri i)) = 0"
        "\<And>i. measure N (mtopology frontier_of mcball (ai i) (ri i)) = 0"
        using frontier_measure_zero_balls[OF sets_N N.finite_measure_axioms M_ne half_gt_zero[OF r'(2)] assms(1)]
        by blast
      have meas[measurable]: "\<And>a r. mball a r \<in> sets N" "\<forall>\<^sub>F j in F. \<forall>a r. mball a r \<in> sets (Ni j)"
        "\<And>a r. mtopology frontier_of (mball a r) \<in> sets N"
        "\<forall>\<^sub>F j in F. \<forall>a r. mtopology frontier_of (mball a r) \<in> sets (Ni j)"
        by(auto simp: eventually_mono[OF sets_Ni] sets_N borel_of_open closedin_frontier_of borel_of_closed)
      have "\<exists>k. \<forall>l\<ge>k. \<bar>measure N (\<Union>i\<in>{..l}. mball (ai i) (ri i)) - measure N M\<bar> < r'"
      proof -
        have "(\<lambda>j. measure N (\<Union>i\<in>{..j}. mball (ai i) (ri i)))
               \<longlonglongrightarrow> measure N (\<Union> (range (\<lambda>j. \<Union>i\<in>{..j}. mball (ai i) (ri i))))"
          by(rule N.finite_Lim_measure_incseq) (fastforce intro!: monoI)+
        hence "(\<lambda>j. measure N (\<Union>i\<in>{..j}. mball (ai i) (ri i))) \<longlonglongrightarrow> measure N M"
          by (metis UN_UN_flatten UN_atMost_UNIV airi(1))     
        thus ?thesis
          using r' by(auto simp: LIMSEQ_def dist_real_def)
      qed
      then obtain k where k: "measure N M - measure N (\<Union>i\<in>{..k}. mball (ai i) (ri i)) < r'"
        using space_N N.bounded_measure by fastforce
      define \<A> where "\<A> = (\<lambda>J. \<Union>j\<in>J. mball (ai j) (ri j)) ` Pow {..k}"
      have \<A>_fin: "finite \<A>"
        by(auto simp: \<A>_def)
      have \<A>_ne: "\<A> \<noteq> {}"
        by(auto simp: \<A>_def)
      have "\<forall>\<^sub>F n in F. \<bar>measure (Ni n) A - measure N A\<bar> < r'" if "A \<in> \<A>" for A
      proof -
        obtain J where J: "J \<subseteq> {..k}" "A = (\<Union>j\<in>J. mball (ai j) (ri j))"
          using \<open>A \<in> \<A>\<close> by(auto simp: \<A>_def)
        hence J_fin: "finite J"
          using finite_nat_iff_bounded_le by blast      
        have "measure N (mtopology frontier_of A) = measure N (mtopology frontier_of (\<Union>j\<in>J. mball (ai j) (ri j)))"
          by(auto simp: J)
        also have "... \<le> measure N (\<Union> ((frontier_of) mtopology ` (\<lambda>j. mball (ai j) (ri j)) ` J))"
          by(rule N.finite_measure_mono[OF frontier_of_Union_subset]) (use J_fin in auto)
        also have "... \<le> (\<Sum>j\<in>J. measure N (mtopology frontier_of mball (ai j) (ri j)))"
          unfolding image_image by(rule N.finite_measure_subadditive_finite) (use J_fin in auto)
        also have "... = 0"
          by(simp add: airi)
        finally have "measure N (mtopology frontier_of A) = 0"
          by (simp add: measure_le_0_iff)
        moreover have "A \<in> sets N"
          by(auto simp: J(2))
        ultimately show ?thesis
          using mweak_conv_eq4 assms(2) by (fastforce simp: sets_N sets_Ni tendsto_iff dist_real_def)
      qed
      hence filter1:"\<forall>\<^sub>F n in F. \<forall>A \<in> \<A>. \<bar>measure (Ni n) A - measure N A\<bar> < r'"
        by(auto intro!: \<A>_fin eventually_ball_finite)
      have filter2:"\<forall>\<^sub>F n in F. \<bar>measure (Ni n) M - measure N M\<bar> < r'"
        using mweak_conv_imp_limit_space[OF assms(2)] by(auto simp: tendsto_iff dist_real_def)
      show "\<forall>\<^sub>F x in F. \<bar>LPm (Ni x) N - 0\<bar> < r"
      proof(safe intro!: eventually_mono[OF eventually_conj[OF
                          eventually_conj[OF finite_measure_Ni sets_Ni] eventually_conj[OF filter1 filter2]]])
        fix n
        assume n:"\<forall>A\<in>\<A>. \<bar>measure (Ni n) A - measure N A\<bar> < r'" "\<bar>measure (Ni n) M - measure N M\<bar> < r'"
          and sets_Ni[measurable_cong]: "sets (Ni n) = sets (borel_of mtopology)" and "finite_measure (Ni n)"
        then have [measurable]:"\<And>a r. mball a r \<in> sets (Ni n)"
          "\<And>a r. mtopology frontier_of mball a r \<in> sets (Ni n)" "M \<in> sets (Ni n)"
          using meas sets_N by auto
        have space_Ni: "space (Ni n) = M"
          by(simp add: sets_Ni space_borel_of cong: sets_eq_imp_space_eq)
        interpret Ni: finite_measure "Ni n" by fact
        have "LPm (Ni n) N < r"
        proof(safe intro!: order.strict_trans1[OF LPm_imp_le[of "4 * r'"]])
          fix B
          assume "B \<in> sets (borel_of mtopology)"
          hence [measurable]: "B \<in> sets N" "B \<in> sets (Ni n)"
            by(auto simp: sets_N)
          define A where "A \<equiv> \<Union>j\<in>{..k}\<inter>{j. mball (ai j) (ri j) \<inter> B \<noteq> {}}. mball (ai j) (ri j)"
          have A_in: "A \<in> \<A>"
            by(auto simp: \<A>_def A_def)
          have [measurable]: "A \<in> sets N" "A \<in> sets (Ni n)"
            by(auto simp: A_def)
          have 1: "A \<subseteq> (\<Union>a\<in>B. mball a r')"
          proof
            fix x
            assume "x \<in> A"
            then obtain j where j:"j \<le> k" "mball (ai j) (ri j) \<inter> B \<noteq> {}" "x \<in> mball (ai j) (ri j)"
              by(auto simp: A_def)
            then obtain b where b:"b \<in> mball (ai j) (ri j)" "b \<in> B"
              by blast
            have "d b x \<le> d b (ai j) + d (ai j) x"
              using b j by(auto intro!: triangle)
            also have "... < r' / 2 + r' / 2"
              by(rule add_strict_mono, insert b(1) airi(5)[of j] j(3)) (auto simp: commute)
            also have "... = r'" by auto
            finally show "x \<in> (\<Union>a\<in>B. mball a r')"
              using b(1) j(3) by(auto intro!: bexI[where x=b] b simp: mball_def)
          qed
          have 2: "B \<subseteq> A \<union> (M - (\<Union>j\<le>k. mball (ai j) (ri j)))"
          proof -
            have "B = B \<inter> (\<Union>j\<le>k. mball (ai j) (ri j)) \<union> B \<inter> (M - (\<Union>j\<le>k. mball (ai j) (ri j)))"
              using sets.sets_into_space[OF \<open>B \<in> sets N\<close>] by(auto simp: space_N)
            also have "... \<subseteq> A \<union> (M - (\<Union>j\<le>k. mball (ai j) (ri j)))"
              by(auto simp: A_def)
            finally show ?thesis .
          qed
          have 3: "measure N (M - (\<Union>j\<le>k. mball (ai j) (ri j))) < r'"
            using N.finite_measure_compl k space_N by auto
          have 4: "measure (Ni n) (M - (\<Union>j\<le>k. mball (ai j) (ri j))) < 3 * r'"
          proof -
            have "measure (Ni n) (M - (\<Union>j\<le>k. mball (ai j) (ri j)))
                  = measure (Ni n) M - measure (Ni n) (\<Union>j\<le>k. mball (ai j) (ri j))"
              using Ni.finite_measure_compl space_Ni by auto
            also have "... < measure N M + r'- (measure N (\<Union>j\<le>k. mball (ai j) (ri j)) - r')"
              by(rule diff_strict_mono,insert n) (auto simp: abs_diff_less_iff \<A>_def)
            also have "... = measure N (M - (\<Union>j\<le>k. mball (ai j) (ri j))) + 2 * r'"
              using N.finite_measure_compl diff_add_cancel space_N by auto
            finally show ?thesis
              using 3 by auto
          qed
          show "measure (Ni n) B \<le> measure N (\<Union>a\<in>B. mball a (4 * r')) + 4 * r'"
          proof -
            have  "measure (Ni n) B \<le> measure (Ni n) (A \<union> (M - (\<Union>j\<le>k. mball (ai j) (ri j))))"
              by(auto intro!: Ni.finite_measure_mono[OF 2])
            also have "... \<le> measure (Ni n) A + measure (Ni n) (M - (\<Union>j\<le>k. mball (ai j) (ri j)))"
              by(auto intro!: Ni.finite_measure_subadditive)
            also have "... < measure N A + 4 * r'"
              using 4 A_in n by(auto simp: abs_diff_less_iff)
            also have "... \<le> measure N (\<Union>a\<in>B. mball a r') + 4 * r'"
              by(auto intro!: N.finite_measure_mono[OF 1] borel_of_open simp: sets_N)
            also have "... \<le> measure N (\<Union>a\<in>B. mball a (4 * r')) + 4 * r'"
              using mball_subset_concentric[of r' "4 * r'"]
              by(auto intro!: N.finite_measure_mono borel_of_open simp: sets_N)
            finally show ?thesis by simp
          qed
          show "measure N B \<le> measure (Ni n) (\<Union>a\<in>B. mball a (4 * r')) + 4 * r'"
          proof -
            have "measure N B \<le> measure N (A \<union> (M - (\<Union>j\<le>k. mball (ai j) (ri j))))"
              by(auto intro!: N.finite_measure_mono[OF 2])
            also have "... \<le> measure N A + measure N (M - (\<Union>j\<le>k. mball (ai j) (ri j)))"
              by(auto intro!: N.finite_measure_subadditive)
            also have "... < measure (Ni n) A + 2 * r'"
              using 3 A_in n by(auto simp: abs_diff_less_iff)
            also have "... \<le> measure (Ni n) (\<Union>a\<in>B. mball a r') + 2 * r'"
              by(auto intro!: Ni.finite_measure_mono[OF 1] borel_of_open simp: sets_N)
            also have "... \<le> measure (Ni n) (\<Union>a\<in>B. mball a (4 * r')) + 2 * r'"
              using mball_subset_concentric[of r' "4 * r'"]
              by(auto intro!: Ni.finite_measure_mono borel_of_open simp: sets_N)
            finally show ?thesis by simp
          qed
        qed (auto simp: r'_def)
        thus "\<bar>LPm (Ni n) N - 0\<bar> < r"
          by simp
      qed
    qed (use in_P in auto)
  qed
qed

corollary conv_iff_mweak_conv: "separable_space mtopology \<Longrightarrow> limitin LPm.mtopology Ni N F \<longleftrightarrow> mweak_conv Ni N F"
  using converge_imp_mweak_conv mweak_conv_imp_converge by blast

subsection \<open> Separability \<close>
lemma LPm_countable_base:
  assumes ai:"mdense (range ai)"
  shows "LPm.mdense
            ((\<lambda>(k,bi). sum_measure
                        (borel_of mtopology) {..k}
                        (\<lambda>i. scale_measure (ennreal (bi i)) (return (borel_of mtopology) (ai i))))
              ` (SIGMA k:(UNIV :: nat set). ({..k} \<rightarrow>\<^sub>E \<rat> \<inter> {0..})))" (is "LPm.mdense ?D")
proof -
  have sep:"separable_space mtopology"
    using ai by(auto simp: separable_space_def2 intro!: exI[where x="range ai"])
  have ai_in: "\<And>i. ai i \<in> M"
    by (meson ai mdense_def2 range_subsetD)
  hence M_ne:"M \<noteq> {}"
    by blast
  show ?thesis
    unfolding LPm.mdense_def3
  proof
    show goal1:"?D \<subseteq> \<P>"
    proof safe
      fix bi :: "nat \<Rightarrow> real" and k :: nat
      assume h: "bi \<in> {..k} \<rightarrow>\<^sub>E \<rat> \<inter> {0..}"
      show "sum_measure (borel_of mtopology) {..k}
                        (\<lambda>i. scale_measure (ennreal (bi i)) (return (borel_of mtopology) (ai i))) \<in> \<P>"
        by(auto simp: \<P>_def emeasure_sum_measure intro!: finite_measureI)
    qed
    show "\<forall>x\<in>\<P>. \<exists>xn. range xn \<subseteq> ?D  \<and> limitin LPm.mtopology xn x sequentially"
    proof
      fix N
      assume "N \<in> \<P>"
      then have sets_N[measurable_cong]: "sets N = sets (borel_of mtopology)"
        and space_N:"space N = M" and "finite_measure N"
        by(auto simp: \<P>_def space_borel_of cong: sets_eq_imp_space_eq)
      then interpret N: finite_measure N by simp
      have [measurable]:"\<And>a r. mball a r \<in> sets N"
        by(auto simp: sets_N borel_of_open)
      have ai_in'[measurable]: "\<And>i. ai i \<in> space N"
        by(auto simp: ai_in space_N)
      have "(\<lambda>i. measure N (\<Union>j\<le>i. mball (ai j) (1 / Suc m))) \<longlonglongrightarrow> measure N (space N)" for m
      proof -
        have 1:"(\<Union>i. (\<Union>j\<le>i. mball (ai j) (1 / Suc m))) = space N"
          using mdense_balls_cover[OF ai,of "1 / Suc m"] by(auto simp: space_N)
        have "(\<lambda>i. measure N (\<Union>j\<le>i. mball (ai j) (1 / Suc m)))
              \<longlonglongrightarrow> measure N (\<Union>i. (\<Union>j\<le>i. mball (ai j) (1 / Suc m)))"
          by(rule  N.finite_Lim_measure_incseq) (fastforce intro!: monoI)+
        thus ?thesis
          unfolding 1 .
      qed
      hence "\<exists>k. \<forall>i\<ge>k. \<bar>measure N (\<Union>j\<le>i. mball (ai j) (1 / Suc m)) - measure N (space N)\<bar> < 1 / Suc m" for m
        unfolding LIMSEQ_def dist_real_def by fastforce
      then obtain k where
        "\<And>i m. i \<ge> k m \<Longrightarrow> \<bar>measure N (\<Union>j\<le>i. mball (ai j) (1 / Suc m)) - measure N (space N)\<bar> < 1 / Suc m"
        by metis
      hence k: "\<And>m. measure N (space N) - measure N (\<Union>j\<le>k m. mball (ai j) (1 / Suc m)) < 1 / Suc m"
        using N.bounded_measure by auto
      define Ami
        where "Ami \<equiv> (\<lambda>m i. (\<Union>j<Suc i. mball (ai j) (1 / Suc m)) - (\<Union>j<i. mball (ai j) (1 / Suc m)))"
      have Ami_disj: "\<And>m. disjoint_family (Ami m)"
        by(fastforce simp: Ami_def intro!: disjoint_family_Suc)
      have Ami_def': "Ami = (\<lambda>m i. mball (ai i) (1 / Suc m) - (\<Union>j<i. mball (ai j) (1 / Suc m)))"
        by (standard, standard) (auto simp: Ami_def less_Suc_eq)
      have Ami_subs: "Ami m i \<subseteq> mball (ai i) (1 / Suc m)" for m i
        by(auto simp: Ami_def')
      have Ami_un: "(\<Union>i\<le>j. Ami m i) = (\<Union>i\<le>j. mball (ai i) (1 / Suc m))" for m j
      proof
        show "(\<Union>i\<le>j. mball (ai i) (1 / real (Suc m))) \<subseteq> (\<Union>i\<le>j. Ami m i)"
        proof(induction j)
          case 0
          then show ?case
            by(auto simp: Ami_def)
        next
          case ih:(Suc j)
          have "(\<Union>i\<le>Suc j. mball (ai i) (1 / real (Suc m)))
                 = (\<Union>i\<le>j. mball (ai i) (1 / (Suc m))) \<union> mball (ai (Suc j)) (1 / Suc m)"
            by(fastforce simp: le_Suc_eq)
          also have "... = (\<Union>i\<le>j. mball (ai i) (1 / (Suc m))) \<union>
                               (mball (ai (Suc j)) (1 / Suc m) - (\<Union>i<Suc j. mball (ai i) (1 / (Suc m))))"
            by fastforce
          also have "... \<subseteq> (\<Union>i\<le>Suc j. Ami m i)"
          proof -
            have "(mball (ai (Suc j)) (1 / Suc m) - (\<Union>i<Suc j. mball (ai i) (1 / (Suc m))))
                  \<subseteq> (\<Union>i\<le>Suc j. Ami m i)"
              using Ami_def' by blast
            thus ?thesis
              using ih by(fastforce simp: le_Suc_eq)
          qed          
          finally show ?case .
        qed
      qed(use Ami_subs in auto)
      have sets_Ami[measurable]: "\<And>m i. Ami m i \<in> sets N"
        by(auto simp: Ami_def)
      have "\<exists>qmi. qmi \<in>({..k m} \<rightarrow>\<^sub>E \<rat> \<inter> {0..}) \<and> (\<Sum>i\<le>k m. \<bar>measure N (Ami m i) - qmi i\<bar>) < 1 / Suc m" for m
      proof -
        have "\<exists>qmi\<in> \<rat> \<inter> {0..}. measure N (Ami m i) - qmi < 1 / (real (Suc m) * real (Suc (k m))) \<and>
                               qmi \<le> measure N (Ami m i)" if "i \<le> k m" for i
        proof(cases "measure N (Ami m i) = 0")
          case True
          then show ?thesis
            by(auto intro!: bexI[where x=0])
        next
          case False
          hence "max 0 (measure N (Ami m i) - 1 / (real (Suc m) * real (Suc (k m)))) < measure N (Ami m i)"
            by(auto simp: zero_less_measure_iff)
          from of_rat_dense[OF this] obtain q where
            q:"0 < real_of_rat q" "measure N (Ami m i) - 1 / (real (Suc m) * real (Suc (k m))) < real_of_rat q"
            "real_of_rat q < measure N (Ami m i)"
            by auto
          hence "real_of_rat q \<in> \<rat> \<inter> {0..}"
            by auto
          with q(2,3) show ?thesis
            by(auto intro!: bexI[where x="real_of_rat q"])
        qed
        then obtain qmi where qmi:"\<And>i. i \<le> k m \<Longrightarrow> qmi i \<in> \<rat> \<inter> {0..}"
          "\<And>i. i \<le> k m \<Longrightarrow> measure N (Ami m i) - qmi i < 1 / (real (Suc m) * real (Suc (k m)))"
          "\<And>i. i \<le> k m \<Longrightarrow> qmi i \<le> measure N (Ami m i)"
          by metis
        have 2: "(\<Sum>i\<le>k m. \<bar>measure N (Ami m i) - qmi i\<bar>) < 1 / Suc m"
        proof -
          have "\<And>i. i \<le> k m \<Longrightarrow> \<bar>measure N (Ami m i) - qmi i\<bar> < 1 / (real (Suc m) * real (Suc (k m)))"
            using qmi by auto
          hence "(\<Sum>i\<le>k m. \<bar>measure N (Ami m i) - qmi i\<bar>) < (\<Sum>i\<le>k m. 1 / (real (Suc m) * real (Suc (k m))))"
            by(intro sum_strict_mono) auto
          also have "... = 1 / Suc m"
            by auto
          finally show ?thesis .
        qed
        show ?thesis
          using qmi 2 by(intro exI[where x="\<lambda>i\<in>{..k m}. qmi i"]) force
      qed

      hence "\<exists>qmi. \<forall>m. qmi m \<in>({..k m} \<rightarrow>\<^sub>E \<rat> \<inter> {0..}) \<and> (\<Sum>i\<le>k m. \<bar>measure N (Ami m i) - qmi m i\<bar>) < 1 / Suc m"
        by(intro choice) auto
      then obtain qmi where qmi: "\<And>m. qmi m \<in> ({..k m} \<rightarrow>\<^sub>E \<rat> \<inter> {0..})"
        "\<And>m. (\<Sum>i\<le>k m. \<bar>measure N (Ami m i) - qmi m i\<bar>) < 1 / Suc m"
        by blast
      define Ni where "Ni \<equiv> (\<lambda>i. sum_measure N {..k i} (\<lambda>j. scale_measure (qmi i j) (return N (ai j))))"
      have NiD:"Ni i \<in> ?D" for i
        using qmi by(auto simp: Ni_def image_def intro!: exI[where x="k i"] bexI[where x="qmi i"]
                          cong: return_cong[OF sets_N] sum_measure_cong[OF sets_N refl])
      with goal1 have NiP: "\<And>i. Ni i \<in> \<P>" by auto
      hence Nifin: "\<And>i. finite_measure (Ni i)"
        and sets_Ni'[measurable_cong]: "\<And>i. sets (Ni i) = borel_of mtopology"
        by(auto simp: inP_D)
      interpret mweak_conv_fin M d Ni N sequentially
        using NiP \<P>_def \<open>N \<in> \<P>\<close> inP_mweak_conv_fin_all by blast        
      show "\<exists>xn. range xn \<subseteq> ?D  \<and> limitin LPm.mtopology xn N sequentially"
      proof(safe intro!: exI[where x=Ni] mweak_conv_imp_converge sep)
        show "mweak_conv_seq Ni N"
          unfolding mweak_conv_eq1 LIMSEQ_def 
        proof safe
          fix g :: "'a \<Rightarrow> real" and K r :: real
          assume h: "uniformly_continuous_map Self euclidean_metric g" "\<forall>x\<in>M. \<bar>g x\<bar> \<le> K" and r[arith]: "r > 0"
          have [measurable]:"g \<in> borel_measurable N"
            using continuous_map_measurable[OF uniformly_continuous_imp_continuous_map[OF h(1)]]
            by(auto simp: borel_of_euclidean mtopology_of_def cong: measurable_cong_sets sets_N)
          have gK: "\<And>x. x \<in> space N \<Longrightarrow> \<bar>g x\<bar> \<le> K"
            using h(2) by(auto simp: space_N)
          have K_nonneg: "K \<ge> 0"
            using h(2) M_ne by auto
          have "\<exists>m. 2 * K / Suc m < r / 2"
          proof (cases "K = 0")
            assume K:"K \<noteq> 0"
            then have "r / 2 * (1 / (2 * K)) > 0"
              using K_nonneg by auto
            then obtain m where "1 / Suc m < r / 2 * (1 / (2 * K))"
              by (meson nat_approx_posE)
            from mult_strict_right_mono[OF this,of "2 * K"] show ?thesis
              using K K_nonneg by auto
          qed simp
          then obtain m1 where m1: "2 * K / Suc m1 < r / 2" by auto
          obtain \<delta> where \<delta>: "\<delta> > 0"
            "\<And>x y. x \<in> M \<Longrightarrow> y \<in> M \<Longrightarrow> d x y < \<delta> \<Longrightarrow> \<bar>g x - g y\<bar> <  r / 2 * (1 / (1 + measure N (space N)))"
            using conjunct2[OF h(1)[simplified uniformly_continuous_map_def],
                rule_format,of "(r / 2) * (1 / (1 + measure N (space N)))"] measure_nonneg[of N "space N"] r
            unfolding mdist_Self mspace_Self mdist_euclidean_metric dist_real_def by auto
          obtain m2 where m2: "1 / Suc m2 < \<delta> "
            using \<delta>(1) nat_approx_posE by blast
          define m where "m \<equiv> max m1 m2"
          then have m:"1 / Suc m \<le> 1 / real (Suc m1)" "1 / Suc m \<le> 1 / real (Suc m2)"
            by (simp_all add: frac_le)
          show "\<exists>no. \<forall>n\<ge>no. dist (\<integral>x. g x \<partial>Ni n) (\<integral>x. g x \<partial>N) < r"
            unfolding dist_real_def
          proof(safe intro!: exI[where x=m])
            fix n
            assume "n \<ge> m"
            then have n:"1 / Suc n \<le> 1 / real (Suc m)"
              by (simp add: frac_le)
            have int1[measurable]: "integrable (return N (ai j)) g" for j
              unfolding integrable_iff_bounded
            proof safe
              show "(\<integral>\<^sup>+ x. ennreal (norm (g x)) \<partial>return N (ai j)) < \<infinity>"
                by(rule order.strict_trans1[OF nn_integral_mono[where v="\<lambda>x. ennreal K"]])
                  (auto simp:  ai_in' gK intro!: ennreal_leI)
            qed simp
            have int2[measurable]: "\<And>A. A \<in> sets N \<Longrightarrow> integrable N (indicat_real A)"
              using N.fmeasurable_eq_sets fmeasurable_def by blast
            have intg: "integrable N g"
              by(auto intro!: N.integrable_const_bound[where B=K] gK)
            show "\<bar>(\<integral>x. g x \<partial>Ni n) - (\<integral>x. g x \<partial>N)\<bar> < r" (is "?lhs < _")
            proof -
              have "?lhs = \<bar>(\<Sum>i\<le>k n. \<integral>x. g x \<partial>scale_measure (qmi n i) (return N (ai i))) - (\<integral>x. g x \<partial>N)\<bar>"
                by(simp add: Ni_def integral_sum_measure[OF _ integrable_scale_measure[OF int1]])
              also have "... = \<bar>(\<Sum>i\<le>k n. qmi n i * g (ai i)) - (\<integral>x. g x \<partial>N)\<bar>"
              proof -
                {
                  fix i
                  assume i:"i \<le> k n"
                  then have "(\<integral>x. g x \<partial>scale_measure (qmi n i) (return N (ai i))) = qmi n i * g (ai i)"
                    using integral_scale_measure[OF _ int1,of "qmi n i"] qmi(1)[of n] int1
                    by(fastforce simp: integral_return ai_in')
                }
                thus ?thesis
                  by simp
              qed
              also have "... = \<bar>(\<Sum>i\<le>k n. qmi n i * g (ai i)) - (\<Sum>i\<le>k n. measure N (Ami n i) * g (ai i))
                                 + ((\<Sum>i\<le>k n. measure N (Ami n i) * g (ai i)) - (\<integral>x. g x \<partial>N))\<bar>"
                by simp
              also have "... \<le> \<bar>(\<Sum>i\<le>k n. measure N (Ami n i) * g (ai i)) - (\<Sum>i\<le>k n. qmi n i * g (ai i))\<bar>
                                 + \<bar>(\<Sum>i\<le>k n. measure N (Ami n i) * g (ai i)) - (\<integral>x. g x \<partial>N)\<bar>"
                by auto
              also have "... = \<bar>\<Sum>i\<le>k n. (measure N (Ami n i) - qmi n i) * g (ai i)\<bar>
                                + \<bar>(\<Sum>i\<le>k n. measure N (Ami n i) * g (ai i)) - (\<integral>x. g x \<partial>N)\<bar>"
                by(simp add: sum_subtractf left_diff_distrib)
              also have "... \<le> (\<Sum>i\<le>k n. \<bar>(measure N (Ami n i) - qmi n i) * g (ai i)\<bar>)
                                + \<bar>(\<Sum>i\<le>k n. measure N (Ami n i) * g (ai i)) - (\<integral>x. g x \<partial>N)\<bar>"
                by simp
              also have "... = (\<Sum>i\<le>k n. \<bar>measure N (Ami n i) - qmi n i\<bar> * \<bar>g (ai i)\<bar>)
                                + \<bar>(\<Sum>i\<le>k n. measure N (Ami n i) * g (ai i)) - (\<integral>x. g x \<partial>N)\<bar>"
                by (simp add: abs_mult)
              also have "... \<le> (\<Sum>i\<le>k n. \<bar>measure N (Ami n i) - qmi n i\<bar> * K)
                                + \<bar>(\<Sum>i\<le>k n. measure N (Ami n i) * g (ai i)) - (\<integral>x. g x \<partial>N)\<bar>"
                by(auto intro!: sum_mono mult_left_mono gK[OF ai_in'])
              also have "... = (\<Sum>i\<le>k n. \<bar>measure N (Ami n i) - qmi n i\<bar>) * K
                                + \<bar>(\<Sum>i\<le>k n. measure N (Ami n i) * g (ai i)) - (\<integral>x. g x \<partial>N)\<bar>"
                by (simp add: sum_distrib_right)
              also have "... \<le> 1 / Suc n * K + \<bar>(\<Sum>i\<le>k n. measure N (Ami n i) * g (ai i)) - (\<integral>x. g x \<partial>N)\<bar>"
              proof -
                have "(\<Sum>i\<le>k n. \<bar>measure N (Ami n i) - qmi n i\<bar>) * K \<le> 1 / Suc n * K"
                  by(rule mult_right_mono) (use qmi(2)[of n] K_nonneg in auto)
                thus ?thesis by simp
              qed
              also have "... = K / Suc n + \<bar>(\<Sum>i\<le>k n. (\<integral>x. indicator (Ami n i) x * g (ai i) \<partial>N)) - (\<integral>x. g x \<partial>N)\<bar>"
                by auto
              also have "... = K / Suc n + \<bar>(\<integral>x. (\<Sum>i\<le>k n. indicator (Ami n i) x * g (ai i)) \<partial>N) - (\<integral>x. g x \<partial>N)\<bar>"
              proof -
                have "(\<Sum>i\<le>k n. (\<integral>x. indicator (Ami n i) x * g (ai i) \<partial>N))
                       = (\<integral>x. (\<Sum>i\<le>k n. indicator (Ami n i) x * g (ai i)) \<partial>N)"
                  by(rule integral_sum'[symmetric]) (use int2 in auto)
                thus ?thesis
                  by simp
              qed
              also have "... = K / Suc n
                              + \<bar>(\<integral>x. (\<Sum>i\<le>k n. indicat_real (Ami n i) x * g (ai i)) \<partial>N)
                                  - ((\<integral>x. (\<Sum>i\<le>k n. indicat_real (Ami n i) x * g x) \<partial>N)
                                  + (\<integral>x. indicat_real (space N - (\<Union>i\<le>k n. Ami n i)) x *g x \<partial>N))\<bar>"
              proof -
                have *:"indicat_real (\<Union>i\<le>k n. Ami n i) x = (\<Sum>i\<le>k n. indicat_real (Ami n i) x)" for x
                  by(auto intro!: indicator_UN_disjoint Ami_disj disjoint_family_on_mono[OF _ Ami_disj[of n]])
                hence "(\<integral>x. (\<Sum>i\<le>k n. indicat_real (Ami n i) x * g x) \<partial>N)
                        + (\<integral>x. indicat_real (space N - (\<Union>i\<le>k n. Ami n i)) x *g x \<partial>N)
                     = (\<integral>x. indicat_real (\<Union>i\<le>k n. Ami n i) x * g x \<partial>N)
                        + (\<integral>x. indicat_real (space N - (\<Union>i\<le>k n. Ami n i)) x *g x \<partial>N)"
                  by (simp add: sum_distrib_right)
                also have "... = (\<integral>x. indicat_real (\<Union>i\<le>k n. Ami n i) x * g x
                                  + indicat_real (space N - (\<Union>i\<le>k n. Ami n i)) x * g x \<partial>N)"
                  by(rule Bochner_Integration.integral_add[symmetric])
                    (auto intro!: integrable_mult_indicator[where 'b=real,simplified] intg)
                also have "... = (\<integral>x. g x \<partial>N)"
                  by(auto intro!: Bochner_Integration.integral_cong) (auto simp: indicator_def)
                finally show ?thesis by simp
              qed
              also have "... = K / Suc n
                              + \<bar>(\<Sum>i\<le>k n. \<integral>x. indicat_real (Ami n i) x * g (ai i) \<partial>N)
                                  - ((\<Sum>i\<le>k n. \<integral>x.  indicat_real (Ami n i) x * g x \<partial>N)
                                  + (\<integral>x. indicat_real (space N - (\<Union>i\<le>k n. Ami n i)) x *g x \<partial>N))\<bar>"
              proof -
                have *: "(\<integral>x. (\<Sum>i\<le>k n. indicat_real (Ami n i) x * g (ai i)) \<partial>N)
                       = (\<Sum>i\<le>k n. \<integral>x. indicator (Ami n i) x * g (ai i) \<partial>N)"
                  by(rule Bochner_Integration.integral_sum) (use int2 in auto)
                have **: "(\<integral>x. (\<Sum>i\<le>k n. indicat_real (Ami n i) x * g x) \<partial>N)
                        = (\<Sum>i\<le>k n. \<integral>x.  indicat_real (Ami n i) x * g x \<partial>N)"
                  by(rule Bochner_Integration.integral_sum)
                    (auto intro!: integrable_mult_indicator[where 'b=real,simplified] intg)
                show ?thesis
                  unfolding * ** by simp
              qed
              also have "... = K / Suc n
                 + \<bar>(\<Sum>i\<le>k n. (\<integral>x. indicat_real (Ami n i) x * g (ai i) \<partial>N) - (\<integral>x.  indicat_real (Ami n i) x * g x \<partial>N))
                 - (\<integral>x. indicat_real (space N - (\<Union>i\<le>k n. Ami n i)) x * g x \<partial>N)\<bar>"
                by(simp add: sum_subtractf)
              also have "... \<le> K / Suc n
                 + \<bar>(\<Sum>i\<le>k n. (\<integral>x. indicat_real (Ami n i) x * g (ai i) \<partial>N) - (\<integral>x.  indicat_real (Ami n i) x * g x \<partial>N))\<bar>
                 + \<bar>\<integral>x. indicat_real (space N - (\<Union>i\<le>k n. Ami n i)) x * g x \<partial>N\<bar>"
                by linarith
              also have "... \<le> K / Suc n
                               + \<bar>\<Sum>i\<le>k n. (\<integral>x. indicat_real (Ami n i) x * (g (ai i) - g x) \<partial>N)\<bar>
                               + \<bar>\<integral>x. indicat_real (space N - (\<Union>i\<le>k n. Ami n i)) x * g x \<partial>N\<bar>"
              proof -
                have "(\<Sum>i\<le>k n. (\<integral>x. indicat_real (Ami n i) x * g (ai i) \<partial>N) - (\<integral>x.  indicat_real (Ami n i) x * g x \<partial>N)) = (\<Sum>i\<le>k n. (\<integral>x. indicat_real (Ami n i) x * g (ai i) - indicat_real (Ami n i) x * g x \<partial>N))"
                  by(rule Finite_Cartesian_Product.sum_cong_aux[OF Bochner_Integration.integral_diff[symmetric]]) (auto intro!: integrable_mult_indicator[where 'b=real,simplified] intg int2)
                also have "... = (\<Sum>i\<le>k n. (\<integral>x. indicat_real (Ami n i) x * (g (ai i) - g x) \<partial>N))"
                  by(simp add: right_diff_distrib)
                finally show ?thesis by simp
              qed
              also have "... \<le> 1 / Suc n * K + r / 2 + 1 / Suc n * K"
              proof -
                have *:"\<bar>\<Sum>i\<le>k n. (\<integral>x. indicat_real (Ami n i) x * (g (ai i) - g x) \<partial>N)\<bar> \<le> r / 2"
                proof -
                  have "\<bar>\<Sum>i\<le>k n. (\<integral>x. indicat_real (Ami n i) x * (g (ai i) - g x) \<partial>N)\<bar>
                        \<le> (\<Sum>i\<le>k n. \<bar>\<integral>x. indicat_real (Ami n i) x * (g (ai i) - g x) \<partial>N\<bar>)"
                    by(rule sum_abs)
                  also have "... \<le> (\<Sum>i\<le>k n. (\<integral>x. \<bar>indicat_real (Ami n i) x * (g (ai i) - g x)\<bar> \<partial>N))"
                    by(auto intro!: sum_mono)
                  also have "... = (\<Sum>i\<le>k n. (\<integral>x. indicat_real (Ami n i) x * \<bar>(g (ai i) - g x)\<bar> \<partial>N))"
                    by(auto intro!: Finite_Cartesian_Product.sum_cong_aux Bochner_Integration.integral_cong
                              simp: abs_mult)
                  also have "... \<le> (\<Sum>i\<le>k n. (\<integral>x. indicat_real (Ami n i) x * (\<Squnion>y\<in>Ami n i. \<bar>g (ai i) - g y\<bar>) \<partial>N))"
                  proof(rule sum_mono[OF integral_mono])
                    fix i x
                    show "indicat_real (Ami n i) x * \<bar>g (ai i) - g x\<bar>
                          \<le> indicat_real (Ami n i) x * (\<Squnion>y\<in>Ami n i. \<bar>g (ai i) - g y\<bar>)"
                      using gK gK[OF ai_in'[of i]] sets.sets_into_space[OF sets_Ami[of n i]]
                      by(fastforce simp: indicator_def intro!: cSUP_upper bdd_aboveI[where M="2 * K"])
                  qed(auto intro!: integrable_mult_indicator[where 'b=real,simplified] intg int2)
                  also have "... \<le> (\<Sum>i\<le>k n. (\<integral>x. indicat_real (Ami n i) x
                                                   * (r / 2 * (1 / (1 + measure N (space N)))) \<partial>N))"
                  proof(rule sum_mono[OF integral_mono])
                    fix i x
                    show "indicat_real (Ami n i) x * (\<Squnion>y\<in>Ami n i. \<bar>g (ai i) - g y\<bar>)
                          \<le> indicat_real (Ami n i) x * (r / 2 * (1 / (1 + measure N (space N))))"
                    proof -
                      {
                        assume x:"x \<in> Ami n i"
                        have "(\<Squnion>y\<in>Ami n i. \<bar>g (ai i) - g y\<bar>) \<le> r / 2 * (1 / (1 + measure N (space N)))"
                        proof(safe intro!: cSup_le_iff[THEN iffD2])
                          fix y
                          assume y:"y \<in> Ami n i"
                          with Ami_subs[of n i] have "y \<in> mball (ai i) (1 / real (Suc n))"
                            by auto
                          with \<delta>(2) n m m2
                          show "\<bar>g (ai i) - g y\<bar> \<le> r / 2 * (1 / (1 + measure N (space N)))"
                            by fastforce
                        qed(insert x gK gK[OF ai_in'[of i]] sets.sets_into_space[OF sets_Ami[of n i]],
                            fastforce intro!: bdd_aboveI[where M="2*K"])+
                      }
                      thus ?thesis
                        by(auto simp: indicator_def)
                    qed
                  qed(auto intro!: integrable_mult_indicator[where 'b=real,simplified] intg int2)
                  also have "... \<le> (\<Sum>i\<le>k n. measure N (Ami n i)) * (r / 2 * (1 / (1 + measure N (space N))))"
                    by (simp only: sum_distrib_right) auto
                  also have "... = measure N (\<Union>i\<le>k n. (Ami n i)) * (r / 2 * (1 / (1 + measure N (space N))))"
                    by(auto intro!: N.finite_measure_finite_Union[symmetric] disjoint_family_on_mono[OF _ Ami_disj[of n]])
                  also have "... \<le> (r / 2) * (measure N (space N) * (1 / (1 + measure N (space N))))"
                    using r measure_nonneg N.bounded_measure
                    by(auto simp del: times_divide_eq_left times_divide_eq_right intro!: mult_right_mono)
                  also have "... \<le> r / 2"
                    by(intro mult_left_le) (auto simp: divide_le_eq_1 intro!: add_pos_nonneg)
                  finally show ?thesis .
                qed
                have **: "\<bar>\<integral>x. indicat_real (space N - (\<Union>i\<le>k n. Ami n i)) x * g x \<partial>N\<bar> \<le> 1 / Suc n * K"
                proof -
                  have "\<bar>\<integral>x. indicat_real (space N - (\<Union>i\<le>k n. Ami n i)) x * g x \<partial>N\<bar>
                        \<le> (\<integral>x. \<bar>indicat_real (space N - (\<Union>i\<le>k n. Ami n i)) x * g x\<bar> \<partial>N)"
                    by simp
                  also have "... = (\<integral>x. indicat_real (space N - (\<Union>i\<le>k n. Ami n i)) x * \<bar>g x\<bar> \<partial>N)"
                    by(auto intro!: Bochner_Integration.integral_cong simp: abs_mult)
                  also have "... \<le> (\<integral>x. indicat_real (space N - (\<Union>i\<le>k n. Ami n i)) x * K \<partial>N)"
                    by(rule integral_mono,insert gK)
                      (auto intro!: integrable_mult_indicator[where 'b=real,simplified] intg int2
                              simp: ordered_semiring_class.mult_left_mono)
                  also have "... = measure N (space N - (\<Union>i\<le>k n. Ami n i)) * K"
                    by simp
                  also have "... = (measure N (space N) - measure N (\<Union>j\<le>k n. mball (ai j) (1 / real (Suc n)))) * K"
                    unfolding Ami_un by(simp add: N.finite_measure_compl)
                  also have "... \<le> 1 / Suc n * K"
                    by (metis k[of n] K_nonneg less_eq_real_def mult.commute mult_left_mono)
                  finally show ?thesis .
                qed
                show ?thesis
                  using * ** by auto
              qed
              also have "... =  2 * K / Suc n + r / 2"
                by simp
              also have "... \<le> 2 * K / Suc m + r / 2"
                using K_nonneg by (simp add: \<open>m \<le> n\<close> frac_le)
              also have "... \<le> 2 * K / Suc m1 + r / 2"
                using K_nonneg divide_inverse m(1) mult_left_mono by fastforce
              also have "... < r"
                using m1 by auto
              finally show ?thesis .
            qed
          qed
        qed
      qed(use NiD sep in auto)
    qed
  qed
qed

lemma separable_LPm:
  assumes "separable_space mtopology"
  shows "separable_space LPm.mtopology"
proof(cases "M = {}")
  case True
  from M_empty_P[OF this] show ?thesis
    by(intro countable_space_separable_space) auto
next
  case M_ne:False
  then obtain ai :: "nat \<Rightarrow> 'a" where ai:"mdense (range ai)"
    using assms mdense_empty_iff uncountable_def unfolding separable_space_def2 by blast
  have "countable (((\<lambda>(k, bi). sum_measure (borel_of mtopology) {..k}
                                 (\<lambda>i. scale_measure (ennreal (bi i)) (return (borel_of mtopology) (ai i))))
                     ` (SIGMA k:UNIV. {..k} \<rightarrow>\<^sub>E \<rat> \<inter> {0..})))"
    using countable_rat by(auto intro!: countable_PiE)
  thus ?thesis
    using LPm_countable_base[OF ai] by(auto simp: separable_space_def2)
qed

lemma closedin_bounded_measures:
  "closedin LPm.mtopology {N. sets N = sets (borel_of mtopology) \<and> N (space N) \<le> ennreal r}"
  unfolding LPm.metric_closedin_iff_sequentially_closed
proof(intro allI conjI uncurry impI)
  show 1:" {N. sets N = sets (borel_of mtopology) \<and> emeasure N (space N) \<le> ennreal r} \<subseteq> \<P>"
    by(auto intro!: inP_I finite_measureI simp: top.extremum_unique)
  fix Ni N
  assume h:"range Ni \<subseteq> {N. sets N = sets (borel_of mtopology) \<and> emeasure N (space N) \<le> ennreal r}"
    "limitin LPm.mtopology Ni N sequentially"
  then have sets_Ni: "\<And>i. sets (Ni i) = sets (borel_of mtopology)"
    and Nir:"\<And>i. Ni i (space (Ni i)) \<le> ennreal r"
    by auto
  interpret N: finite_measure N
    using limitin_topspace[OF h(2)] unfolding LPm.topspace_mtopology by(simp add: \<P>_def)
  interpret Ni: finite_measure "Ni i" for i
    using 1 h by(auto dest: inP_D)
  have "mweak_conv Ni N sequentially"
    using h 1 sets_Ni Nir by(auto intro!: converge_imp_mweak_conv)
  hence "\<And>f. continuous_map mtopology euclideanreal f
              \<Longrightarrow> (\<exists>B. \<forall>x\<in>M. \<bar>f x\<bar> \<le> B) \<Longrightarrow> (\<lambda>n. \<integral>x. f x \<partial>Ni n) \<longlonglongrightarrow> (\<integral>x. f x \<partial>N)"
    by(simp add: mweak_conv_def)
  from this[of "\<lambda>x. 1"] have "(\<lambda>i. measure (Ni i) (space (Ni i))) \<longlonglongrightarrow> measure N (space N)"
    by auto
  hence "(\<lambda>i. Ni i (space (Ni i))) \<longlonglongrightarrow> N (space N)"
    by (simp add: N.emeasure_eq_measure Ni.emeasure_eq_measure)
  from tendsto_upperbound[OF this,of "ennreal r"]
  show "N \<in> {N. sets N = sets (borel_of mtopology) \<and> emeasure N (space N) \<le> ennreal r}"
    using limitin_topspace[OF h(2)] Nir unfolding LPm.topspace_mtopology
    by(auto simp: \<P>_def)
qed

lemma closedin_subprobs:
  "closedin LPm.mtopology {N. subprob_space N \<and> sets N = sets (borel_of mtopology)}"
  unfolding LPm.metric_closedin_iff_sequentially_closed
proof(intro allI conjI uncurry impI)
  show 1:"{N. subprob_space N \<and> sets N = sets (borel_of mtopology)} \<subseteq> \<P>"
    by(auto intro!: inP_I simp: top.extremum_unique subprob_space_def)
  fix Ni N
  assume h:"range Ni \<subseteq> {N. subprob_space N \<and> sets N = sets (borel_of mtopology)}"
    "limitin LPm.mtopology Ni N sequentially"
  then have sets_Ni: "\<And>i. sets (Ni i) = sets (borel_of mtopology)" and Ni:"\<And>i. subprob_space (Ni i)"
    by auto
  have setsN:"sets N = sets (borel_of mtopology)"
    using limitin_topspace[OF h(2)] unfolding LPm.topspace_mtopology by(auto dest: inP_D)
  interpret N: finite_measure N
    using limitin_topspace[OF h(2)] unfolding LPm.topspace_mtopology by(simp add: \<P>_def)
  interpret Ni: subprob_space "Ni i" for i
    by fact
  have "mweak_conv Ni N sequentially"
    using h 1 sets_Ni Ni by(auto intro!: converge_imp_mweak_conv)
  hence "\<And>f. continuous_map mtopology euclideanreal f \<Longrightarrow> (\<exists>B. \<forall>x\<in>M. \<bar>f x\<bar> \<le> B)
              \<Longrightarrow> (\<lambda>n. \<integral>x. f x \<partial>Ni n) \<longlonglongrightarrow> (\<integral>x. f x \<partial>N)"
    by(simp add: mweak_conv_def)
  from this[of "\<lambda>x. 1"] have "(\<lambda>i. measure (Ni i) (space (Ni i))) \<longlonglongrightarrow> measure N (space N)"
    by auto
  hence "(\<lambda>i. Ni i (space (Ni i))) \<longlonglongrightarrow> N (space N)"
    by (simp add: N.emeasure_eq_measure Ni.emeasure_eq_measure)
  from tendsto_upperbound[OF this,of 1]
  have "emeasure N (space N) \<le> 1"
    using Ni.subprob_emeasure_le_1 by force
  moreover have "space N \<noteq> {}"
    using sets_eq_imp_space_eq[OF setsN] sets_eq_imp_space_eq[OF sets_Ni[of 0]]
    using Ni.subprob_not_empty by fastforce
  ultimately show "N \<in> {N. subprob_space N \<and> sets N = sets (borel_of mtopology)}"
    using limitin_topspace[OF h(2)] unfolding LPm.topspace_mtopology
    by(auto intro!: subprob_spaceI setsN)
qed

lemma closedin_probs: "closedin LPm.mtopology {N. prob_space N \<and> sets N = sets (borel_of mtopology)}"
  unfolding LPm.metric_closedin_iff_sequentially_closed
proof(intro allI conjI uncurry impI)
  show 1:"{N. prob_space N \<and> sets N = sets (borel_of mtopology)} \<subseteq> \<P>"
    by(auto intro!: inP_I simp: top.extremum_unique prob_space_def)
  fix Ni N
  assume h:"range Ni \<subseteq> {N. prob_space N \<and> sets N = sets (borel_of mtopology)}"
    "limitin LPm.mtopology Ni N sequentially"
  then have sets_Ni: "\<And>i. sets (Ni i) = sets (borel_of mtopology)" and Ni:"\<And>i. prob_space (Ni i)"
    by auto
  have setsN:"sets N = sets (borel_of mtopology)"
    using limitin_topspace[OF h(2)] unfolding LPm.topspace_mtopology by(auto dest: inP_D)
  interpret N: finite_measure N
    using limitin_topspace[OF h(2)] unfolding LPm.topspace_mtopology by(simp add: \<P>_def)
  interpret Ni: prob_space "Ni i" for i
    by fact
  have "mweak_conv Ni N sequentially"
    using h 1 sets_Ni Ni by(auto intro!: converge_imp_mweak_conv)
  hence "\<And>f. continuous_map mtopology euclideanreal f \<Longrightarrow> (\<exists>B. \<forall>x\<in>M. \<bar>f x\<bar> \<le> B)
              \<Longrightarrow> (\<lambda>n. \<integral>x. f x \<partial>Ni n) \<longlonglongrightarrow> (\<integral>x. f x \<partial>N)"
    by(simp add: mweak_conv_def)
  from this[of "\<lambda>x. 1"] have "(\<lambda>i. measure (Ni i) (space (Ni i))) \<longlonglongrightarrow> measure N (space N)"
    by auto
  hence "prob_space N"
    by(simp add: Ni.prob_space  LIMSEQ_const_iff N.emeasure_eq_measure prob_spaceI)
  thus "N \<in> {N. prob_space N \<and> sets N = sets (borel_of mtopology)}"
    using limitin_topspace[OF h(2)] unfolding LPm.topspace_mtopology
    by(auto intro!: setsN)
qed

subsection \<open> The L\'evy-Prokhorov Metric and Topology of Weak Convegence\<close>
lemma weak_conv_topology_le_LPm_topology:
  assumes"openin (weak_conv_topology mtopology) S"
  shows "openin LPm.mtopology S"
proof(rule weak_conv_topology_minimal[OF _ _ assms])
  fix f B
  assume f: "continuous_map mtopology euclideanreal f" and B:"\<And>x. x \<in> topspace mtopology \<Longrightarrow> \<bar>f x\<bar> \<le> B"
  show "continuous_map LPm.mtopology euclideanreal (\<lambda>N. \<integral>x. f x \<partial>N)"
    unfolding continuous_map_iff_limit_seq[OF LPm.first_countable_mtopology]
  proof safe
    fix Ni N
    assume "limitin LPm.mtopology Ni N sequentially"
    then have h':"weak_conv_on Ni N sequentially mtopology"
      by(simp add: mtopology_of_def converge_imp_mweak_conv)
    thus "limitin euclideanreal (\<lambda>n. \<integral>x. f x \<partial>Ni n) (\<integral>x. f x \<partial>N) sequentially"
      using f B by(fastforce simp: mweak_conv_seq_def)
  qed
qed(unfold LPm.topspace_mtopology, simp add: \<P>_def)

lemma LPmtopology_eq_weak_conv_topology:
  assumes "separable_space mtopology"
  shows "LPm.mtopology = weak_conv_topology mtopology"
  by(auto intro!: topology_eq_filter inP_I simp: conv_iff_mweak_conv[OF assms] inP_D)

end

corollary
  assumes "metrizable_space X" "separable_space X"
  shows metrizable_weak_conv_topology:"metrizable_space (weak_conv_topology X)"
    and separable_weak_conv_topology:"separable_space (weak_conv_topology X)"
proof -
  obtain d where d:"Metric_space (topspace X) d" "Metric_space.mtopology (topspace X) d = X"
    by (metis Metric_space.topspace_mtopology assms(1) metrizable_space_def)
  then interpret Levy_Prokhorov "topspace X" d
    by(auto simp: Levy_Prokhorov_def)
  show g1:"metrizable_space (weak_conv_topology X)"
    using assms(2) d(2) LPm.metrizable_space_mtopology LPmtopology_eq_weak_conv_topology by simp
  show g2:"separable_space (weak_conv_topology X)"
    using assms(2) d(2) LPmtopology_eq_weak_conv_topology separable_LPm by simp
qed

end