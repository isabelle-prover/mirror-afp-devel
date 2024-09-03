(*  Title:   Coproduct_Measure_Additional.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)
section \<open> Additional Properties \<close>
theory Coproduct_Measure_Additional
  imports "Coproduct_Measure"
          "Standard_Borel_Spaces.StandardBorel"
          "S_Finite_Measure_Monad.Kernels"
          "S_Finite_Measure_Monad.Measure_QuasiBorel_Adjunction"
begin

subsection \<open> S-Finiteness\<close>
lemma s_finite_measure_copair_measure:
  assumes "s_finite_measure M" "s_finite_measure N"
  shows "s_finite_measure (copair_measure M N)"
proof -
  note [measurable] = measurable_vimage_Inl[of _ M N] measurable_vimage_Inr[of _ M N]
  obtain Mi Ni where [measurable_cong]:
    "\<And>i. sets (Mi i) = sets M" "\<And>i. finite_measure (Mi i)" "\<And>A. M A = (\<Sum>i. Mi i A)"
    "\<And>i. sets (Ni i) = sets N" "\<And>i. finite_measure (Ni i)" "\<And>A. N A = (\<Sum>i. Ni i A)"
    by (metis assms(1) assms(2) s_finite_measure.finite_measures')
  thus ?thesis
    by(auto intro!: s_finite_measureI[where Mi="\<lambda>i. Mi i \<Oplus>\<^sub>M Ni i"] finite_measure_copair_measure
              cong: sets_copair_measure_cong simp: emeasure_copair_measure suminf_add)
qed

lemma s_finite_measure_coPiM:
  assumes "countable I" "\<And>i. i \<in> I \<Longrightarrow> s_finite_measure (Mi i)"
  shows "s_finite_measure (coPiM I Mi)"
proof -
  note measurable_Pair_vimage[measurable (raw)]
  consider "finite I" | "infinite I" "countable I"
    using assms by argo
  then show ?thesis
  proof cases
    assume I:"finite I"
    show ?thesis
      by(auto intro!: s_finite_measure_finite_sumI[where Mi="\<lambda>i. distr (Mi i) (coPiM I Mi) (Pair i)"
                                                   and I=I,OF _ s_finite_measure.s_finite_measure_distr[OF assms(2)]]
                simp: emeasure_distr emeasure_coPiM_finite I)
  next
    assume I:"infinite I" "countable I"
    then have [simp]:"\<And>n. from_nat_into I n \<in> I"
      by (simp add: from_nat_into infinite_imp_nonempty)
    show ?thesis
      by(auto intro!: s_finite_measure_s_finite_sumI[where
            Mi="\<lambda>n. distr (Mi (from_nat_into I n)) (coPiM I Mi) (Pair (from_nat_into I n))",
            OF _ s_finite_measure.s_finite_measure_distr[OF assms(2)]]
          simp: emeasure_distr I emeasure_coPiM_countable_infinite' coPair_inverse_space_unit[where I=I])
  qed
qed

subsection \<open> Standardness \<close>
lemma standard_borel_copair_measure:
  assumes "standard_borel M" "standard_borel N"
  shows "standard_borel (M \<Oplus>\<^sub>M N)"
proof -
  obtain A where A[measurable]: "A \<in> sets borel" "A \<subseteq> {0<..<1::real}"
                                "M measurable_isomorphic restrict_space borel A"
    by (meson assms(1) greaterThanLessThan_borel linorder_not_le not_one_le_zero
              standard_borel.isomorphic_subset_real uncountable_open_interval)
  then obtain f f'
    where f[measurable]: "f \<in> M \<rightarrow>\<^sub>M restrict_space borel A"
                         "f' \<in> restrict_space borel A \<rightarrow>\<^sub>M M"
                         "\<And>x. x \<in> space M \<Longrightarrow> f' (f x) = x" "\<And>y. y \<in> A \<Longrightarrow> f (f' y) = y"
    using measurable_isomorphicD[OF A(3)] unfolding space_restrict_space by fastforce
  obtain B where B[measurable]:"B \<in> sets borel" "B \<subseteq> {1<..<2::real}"
                               "N measurable_isomorphic restrict_space borel B"
    by (metis assms(2) greaterThanLessThan_borel linorder_not_le numeral_le_one_iff
              semiring_norm(69) standard_borel.isomorphic_subset_real uncountable_open_interval)
  then obtain g g'
    where g[measurable]: "g \<in> N \<rightarrow>\<^sub>M restrict_space borel B"
                         "g' \<in> restrict_space borel B \<rightarrow>\<^sub>M N"
                         "\<And>x. x \<in> space N \<Longrightarrow> g' (g x) = x"
                         "\<And>y. y \<in> B \<Longrightarrow> g (g' y) = y"
    using measurable_isomorphicD[OF B(3)] unfolding space_restrict_space by fastforce
  have AB:"A \<inter> B = {}"
    using A B by fastforce
  have [measurable]:"f \<in> M \<rightarrow>\<^sub>M restrict_space borel (A \<union> B)"
    using f(1) unfolding measurable_restrict_space2_iff by blast
  have [measurable]:"g \<in> N \<rightarrow>\<^sub>M restrict_space borel (A \<union> B)"
    using g(1) unfolding measurable_restrict_space2_iff by blast

  have iso:"restrict_space borel (A \<union> B) measurable_isomorphic M \<Oplus>\<^sub>M N"
  proof(safe intro!: measurable_isomorphic_byWitness)
    show "case_sum f g \<in> M \<Oplus>\<^sub>M N \<rightarrow>\<^sub>M restrict_space borel (A \<union> B)"
      by(auto intro!: measurable_copair_Inl_Inr)
    show "(\<lambda>r. if r \<in> A then Inl (f' r) else if r \<in> B then Inr (g' r) else undefined)
           \<in> restrict_space borel (A \<union> B) \<rightarrow>\<^sub>M M \<Oplus>\<^sub>M N" (is "?f \<in> _")
    proof -
      have 1:
           "restrict_space (restrict_space borel (A \<union> B)) {r. r \<in> A} = restrict_space borel A"
           "restrict_space (restrict_space borel (A \<union> B)) {r. r \<notin> A} = restrict_space borel B"
           "restrict_space (restrict_space borel B) {x. x \<in> B} = restrict_space borel B"
           "restrict_space (restrict_space borel B) {x. x \<notin> B} = count_space {}"
        using AB by(auto simp: restrict_restrict_space
                      intro!: arg_cong[where f="restrict_space borel"] space_empty)
      have 2:"{r \<in> space (restrict_space borel (A \<union> B)). r \<in> A} = A"
             "{x \<in> space (restrict_space (restrict_space borel (A \<union> B)) {r. r \<notin> A}). x \<in> B} = B"
             "{x \<in> space (restrict_space borel B). x \<in> B} = B"
        using AB by (auto simp: space_restrict_space)
      show ?thesis
        by (intro measurable_If_restrict_space_iff[THEN iffD2] conjI)
           (unfold 1 2, simp_all add: sets_restrict_space_iff)
    qed
    show "\<And>x. x \<in> space (M \<Oplus>\<^sub>M N) \<Longrightarrow> ?f (case_sum f g x) = x"
         "\<And>r. r \<in> space (restrict_space borel (A \<union> B)) \<Longrightarrow> case_sum f g (?f r) = r"
      using measurable_space[OF f(1)] measurable_space[OF g(1)] AB
      by (auto simp: space_copair_measure f g)
  qed
  show ?thesis
    by(auto intro!: standard_borel.measurable_isomorphic_standard[OF _ iso]
                    standard_borel.standard_borel_restrict_space[OF standard_borel_ne.standard_borel])
qed

corollary
  shows standard_borel_ne_copair_measure1: "standard_borel_ne M \<Longrightarrow> standard_borel N \<Longrightarrow> standard_borel_ne (M \<Oplus>\<^sub>M N)"
    and standard_borel_ne_copair_measure2: "standard_borel M \<Longrightarrow> standard_borel_ne N \<Longrightarrow> standard_borel_ne (M \<Oplus>\<^sub>M N)"
    and standard_borel_ne_copair_measure: "standard_borel_ne M \<Longrightarrow> standard_borel_ne N \<Longrightarrow> standard_borel_ne (M \<Oplus>\<^sub>M N)"
  by(auto simp: standard_borel_ne_def standard_borel_ne_axioms_def standard_borel_copair_measure space_copair_measure)

lemma standard_borel_coPiM:
  assumes "countable I" "\<And>i. i \<in> I \<Longrightarrow> standard_borel (Mi i)"
  shows "standard_borel (coPiM I Mi)"
proof -
  let ?I = "{i\<in>I. space (Mi i) \<noteq> {}}"
  have countable_I: "countable ?I"
    using assms by auto
  define I' where "I' \<equiv> to_nat_on ?I ` ?I"
  define Mn where "Mn \<equiv> \<lambda>n. Mi (from_nat_into ?I n)"
  have I':"countable I'" "\<And>n. n \<in> I' \<Longrightarrow> space (Mn n) \<noteq> {}"
          "\<And>n. n \<in> I' \<Longrightarrow> standard_borel_ne (Mn n)"
    using countable_I from_nat_into_to_nat_on[OF countable_I] assms(2)
    by(fastforce simp: I'_def Mn_def standard_borel_ne_def standard_borel_ne_axioms_def
             simp del: from_nat_into_to_nat_on)+
  have iso1:"coPiM I Mi measurable_isomorphic coPiM I' Mn"
  proof(safe intro!: measurable_isomorphic_byWitness[where f="\<lambda>(i,x). (to_nat_on ?I i, x)"
                                                       and g="\<lambda>(n,x). (from_nat_into ?I n, x)"])
    show "(\<lambda>(i, x). (to_nat_on ?I i, x)) \<in> coPiM I Mi \<rightarrow>\<^sub>M coPiM I' Mn"
    proof(rule measurable_coPiM2)
      fix i
      assume i:"i \<in> I"
      show "Pair (to_nat_on ?I i) \<in> Mi i \<rightarrow>\<^sub>M coPiM I' Mn"
      proof(cases "space (Mi i) = {}")
        assume "space (Mi i) \<noteq> {}"
        then show ?thesis
          by(intro measurable_compose[OF _ measurable_Pair_coPiM[where I=I']])
            (use I'_def i countable_I Mn_def in auto)
      qed(simp add: measurable_def)
    qed
    show "(\<lambda>(n,x). (from_nat_into ?I n, x)) \<in> coPiM I' Mn \<rightarrow>\<^sub>M coPiM I Mi"
    proof(rule measurable_coPiM2)
      fix n
      assume "n \<in> I'"
      show "Pair (from_nat_into ?I n) \<in> Mn n \<rightarrow>\<^sub>M coPiM I Mi"
        by (metis (no_types, lifting) Mn_def I'_def \<open>n \<in> I'\<close> emptyE empty_is_image
                  from_nat_into measurable_Pair_coPiM mem_Collect_eq)
    qed
  qed(auto intro!: from_nat_into_to_nat_on to_nat_on_from_nat_into simp: space_coPiM I'_def countable_I)
  have "\<exists>A. A \<in> sets borel \<and> A \<subseteq> {real n<..real n + 1} \<and> Mn n measurable_isomorphic (restrict_space borel A)"
       if n:"n \<in> I'" for n
    using standard_borel.isomorphic_subset_real[OF
        standard_borel_ne.standard_borel[OF I'(3)[OF n] ],of "{real n<..real n + 1}"]
          uncountable_half_open_interval_2[of "real n" "real n + 1"]
    by fastforce
  then obtain An'
    where An': "\<And>n. n \<in> I' \<Longrightarrow> An' n \<in> sets borel"
               "\<And>n. n \<in> I' \<Longrightarrow> An' n \<subseteq> {real n<..real n + 1}"
               "\<And>n. n \<in> I' \<Longrightarrow>  Mn n measurable_isomorphic (restrict_space borel (An' n))"
    by metis
  define An where "An \<equiv> \<lambda>n. if n \<in> I' then An' n else {real n + 1}"
  have An[measurable]: "\<And>n. An n \<in> sets borel"
                       "\<And>n. An n \<subseteq> {real n<..real n + 1}"
                       "\<And>n. n \<in> I' \<Longrightarrow> Mn n measurable_isomorphic (restrict_space borel (An n))"
    using An' by(auto simp: An_def)
  hence disj_An:"disjoint_family An"
    unfolding disjoint_family_on_def
    by safe (metis (no_types, opaque_lifting) greaterThanAtMost_iff less_le nat_less_real_le not_less order_trans subset_eq)
  obtain fn gn'
    where fg:"\<And>n. n \<in> I' \<Longrightarrow> fn n \<in> Mn n \<rightarrow>\<^sub>M restrict_space borel (An n)"
             "\<And>n. n \<in> I' \<Longrightarrow> gn' n \<in> restrict_space borel (An n) \<rightarrow>\<^sub>M Mn n"
             "\<And>n x. n \<in> I' \<Longrightarrow> x \<in> space (Mn n) \<Longrightarrow> gn' n (fn n x) = x"
             "\<And>n r. n \<in> I' \<Longrightarrow> r \<in> space (restrict_space borel (An n)) \<Longrightarrow> fn n (gn' n r) = r"
    using measurable_isomorphicD[OF An(3)] by metis
  define gn where "gn \<equiv> (\<lambda>n r. if r \<in> An n then gn' n r else (SOME x. x \<in> space (Mn n)))"
  have gn_meas[measurable]:"gn n \<in> borel \<rightarrow>\<^sub>M Mn n" if n:"n \<in> I'" for n
    unfolding gn_def by(rule measurable_restrict_space_iff[THEN iffD1,OF _ _ fg(2)[OF n]])
                       (auto simp add: I'(2) some_in_eq that)
  have fg':"\<And>n x. n \<in> I' \<Longrightarrow> x \<in> space (Mn n) \<Longrightarrow> gn n (fn n x) = x"
           "\<And>n r. n \<in> I' \<Longrightarrow> r \<in> An n \<Longrightarrow> fn n (gn n r) = r"
    using fg measurable_space[OF fg(1)] by(auto simp: gn_def)
  have fn[measurable]:"fn n \<in> Mn n \<rightarrow>\<^sub>M restrict_space borel (\<Union>n\<in>I'. An n)" if n:"n \<in> I'" for n
    using measurable_restrict_space2_iff[THEN iffD1,OF fg(1)[OF n]]
    by(auto intro!: measurable_restrict_space2 n)
  let ?f = "\<lambda>(n,x). fn n x" and ?g ="\<lambda>r. (nat \<lceil>r\<rceil> - 1, gn (nat \<lceil>r\<rceil> - 1) r)"
  have iso2:"coPiM I' Mn measurable_isomorphic restrict_space borel (\<Union>n\<in>I'. An n)"
  proof(safe intro!: measurable_isomorphic_byWitness)
    show "?f \<in> coPiM I' Mn \<rightarrow>\<^sub>M restrict_space borel (\<Union>n\<in>I'. An n)"
      by(auto intro!: measurable_coPiM2)
  next
    show "?g \<in> restrict_space borel (\<Union>n\<in>I'. An n) \<rightarrow>\<^sub>M coPiM I' Mn"
    proof(safe intro!: measurable_coPiM1)
      have 1:"restrict_space borel (\<Union> (An ` I')) \<rightarrow>\<^sub>M count_space I'
              = restrict_space borel (\<Union> (An ` I')) \<rightarrow>\<^sub>M restrict_space (count_space UNIV) I'"
        by (simp add: restrict_count_space)
      show "(\<lambda>x. nat \<lceil>x\<rceil> - 1) \<in> restrict_space borel (\<Union> (An ` I')) \<rightarrow>\<^sub>M count_space I'"
        unfolding 1
      proof(safe intro!: measurable_restrict_space3)
        fix n r
        assume n:"n \<in> I'" "r \<in> An n"
        then have "real n < r" "r \<le> real n + 1"
          using An(2) by fastforce+
        thus "nat \<lceil>r\<rceil> - 1 \<in> I'"
          by (metis n(1) add.commute diff_Suc_1 le_SucE nat_ceiling_le_eq not_less of_nat_Suc)
      qed simp
    qed(auto simp: measurable_restrict_space1)
  next
    fix n x
    assume "(n,x)\<in>space (coPiM I' Mn)"
    then have nx:"n \<in> I'" "x \<in> space (Mn n)"
      by(auto simp: space_coPiM)
    have 1:"nat \<lceil>?f (n,x)\<rceil> = n + 1"
      using measurable_space[OF fg(1)[OF nx(1)] nx(2)] An(2)[of n]
      by simp
        (metis add.commute greaterThanAtMost_iff le_SucE nat_ceiling_le_eq not_less of_nat_Suc subset_eq)
    show "?g (?f (n,x)) = (n,x)"
      unfolding 1 using fg'(1)[OF nx] by simp
  next
    fix y
    assume "y \<in> space (restrict_space borel (\<Union> (An ` I')))"
    then obtain n where n: "n \<in> I'" "y \<in> An n"
      by auto
    then have [simp]:"nat \<lceil>y\<rceil> = n + 1"
      using An(2)[of n]
      by simp (metis add.commute greaterThanAtMost_iff le_SucE nat_ceiling_le_eq not_less of_nat_Suc subset_eq)
    show "?f (?g y) = y"
      using fg'(2)[OF n(1)] n(2) by auto
  qed
  have "standard_borel (restrict_space borel (\<Union> (An ` I')))"
    by(auto intro!: standard_borel_ne.standard_borel[THEN standard_borel.standard_borel_restrict_space])
  with iso1 iso2 show ?thesis
    by (meson measurable_isomorphic_sym standard_borel.measurable_isomorphic_standard)
qed

lemma standard_borel_ne_coPiM:
  assumes "countable I" "\<And>i. i \<in> I \<Longrightarrow> standard_borel (Mi i)"
    and "i \<in> I" "space (Mi i) \<noteq> {}"
  shows "standard_borel_ne (coPiM I Mi)"
proof -
  have "space (coPiM I Mi) \<noteq> {}"
    using assms(3) assms(4) space_coPiM by fastforce
  thus ?thesis
    by(auto intro!: standard_borel_coPiM assms simp: standard_borel_ne_def standard_borel_ne_axioms_def)
qed

subsection \<open> Relationships with Quasi-Borel Spaces\<close>
text \<open> Proposition19(3)~\cite{Heunen_2017}\<close>
lemma r_preserve_copair: "measure_to_qbs (copair_measure M N) = measure_to_qbs M \<Oplus>\<^sub>Q measure_to_qbs N"
proof(safe intro!: qbs_eqI)
  fix \<alpha>
  assume "\<alpha> \<in> qbs_Mx (measure_to_qbs (M \<Oplus>\<^sub>M N))"
  then have a[measurable]: "\<alpha> \<in> borel \<rightarrow>\<^sub>M M \<Oplus>\<^sub>M N"
    by(simp add: qbs_Mx_R)
  have s[measurable]: "\<alpha> -` Inr ` space N \<in> sets borel" "\<alpha> -` Inl ` space M \<in> sets borel"
    by(auto intro!: measurable_sets_borel[OF a])
  consider "\<alpha> -` Inl ` space M \<inter> space borel = space borel"
    | "\<alpha> -` Inr ` (space N) \<inter> space borel = space borel"
    | "\<alpha> -` Inl ` space M \<inter> space borel \<subset> space borel"
      "\<alpha> -` Inr ` (space N) \<inter> space borel \<subset> space borel"
    by blast
  then show "\<alpha> \<in> qbs_Mx (measure_to_qbs M \<Oplus>\<^sub>Q measure_to_qbs N)"
  proof cases
    assume 1:"\<alpha> -` Inl ` space M \<inter> space borel = space borel"
    then obtain f' where "f' \<in> borel \<rightarrow>\<^sub>M M" "\<And>x. x \<in> space borel \<Longrightarrow> \<alpha> x = Inl (f' x)"
      using measurable_copair_dest1[OF a] by blast
    thus ?thesis
      using 1 by(auto simp: copair_qbs_Mx copair_qbs_Mx_def qbs_Mx_R
                    intro!: bexI[where x="\<alpha> -` Inr ` space N"] bexI[where x=f'])
  next
    assume 2:"\<alpha> -` Inr ` space N \<inter> space borel = space borel"
    then obtain f' where "f' \<in> borel \<rightarrow>\<^sub>M N" "\<And>x. x \<in> space borel \<Longrightarrow> \<alpha> x = Inr (f' x)"
      using measurable_copair_dest2[OF a] by blast
    thus ?thesis
      using 2 by(auto simp: copair_qbs_Mx copair_qbs_Mx_def qbs_Mx_R
                    intro!: bexI[where x="\<alpha> -` Inr ` space N"] bexI[where x=f'])
  next
    case 3
    then obtain f' f''
      where f[measurable]:"f' \<in> borel \<rightarrow>\<^sub>M M"
                          "f'' \<in> borel \<rightarrow>\<^sub>M N"
                          "\<And>x. x \<in> space borel \<Longrightarrow> x \<in> \<alpha> -` Inl ` space M \<Longrightarrow> \<alpha> x = Inl (f' x)"
                          "\<And>x. x \<in> space borel \<Longrightarrow> x \<notin> \<alpha> -` Inl ` space M \<Longrightarrow> \<alpha> x = Inr (f'' x)"
      using measurable_copair_dest3[OF a] by metis
    moreover have "\<alpha> -` Inl ` space M \<noteq> UNIV" "\<alpha> -` Inl ` space M \<noteq> {}"
      using 3 measurable_space[OF a] by(fastforce simp: space_copair_measure)+ 
    ultimately show ?thesis
      by(auto simp: copair_qbs_Mx copair_qbs_Mx_def qbs_Mx_R simp del: vimage_eq
            intro!: bexI[where x="\<alpha> -` Inl ` space M"] bexI[where x=f'] bexI[where x=f''])
  qed
qed(auto simp: qbs_Mx_R copair_qbs_Mx copair_qbs_Mx_def)

lemma r_preserve_coproduct:
  assumes "countable I"
  shows "measure_to_qbs (coPiM I M) = (\<amalg>\<^sub>Q i\<in>I. measure_to_qbs (M i))"
proof(safe intro!: qbs_eqI)
  fix \<alpha>
  assume h:"\<alpha> \<in> qbs_Mx (measure_to_qbs (coPiM I M))"
  then obtain a g
    where "a \<in> borel \<rightarrow>\<^sub>M count_space I"
          "\<And>i. i \<in> I \<Longrightarrow> space (M i) \<noteq> {} \<Longrightarrow> g i \<in> borel \<rightarrow>\<^sub>M M i"
          "\<alpha> = (\<lambda>x. (a x, g (a x) x))"
    using measurable_coPiM1_elements[OF assms] unfolding qbs_Mx_R by blast
  thus "\<alpha> \<in> qbs_Mx (\<amalg>\<^sub>Q i\<in>I. measure_to_qbs (M i))"
    using qbs_Mx_to_X[OF h]
    by(safe intro!: coPiQ_MxI) (auto simp: qbs_Mx_R qbs_space_R space_coPiM)
next
  fix \<alpha>
  assume "\<alpha> \<in> qbs_Mx (\<amalg>\<^sub>Q i\<in>I. measure_to_qbs (M i))"
  then obtain a g where "a \<in> borel \<rightarrow>\<^sub>M count_space I"
                        "\<And>i. i \<in> range a \<Longrightarrow> g i \<in> borel \<rightarrow>\<^sub>M M i" "\<alpha> = (\<lambda>x. (a x, g (a x) x))"
    unfolding coPiQ_Mx coPiQ_Mx_def qbs_Mx_R by blast
  thus "\<alpha> \<in> qbs_Mx (measure_to_qbs (coPiM I M))"
    by(auto intro!: measurable_coPiM1' simp: qbs_Mx_R assms)
qed

end