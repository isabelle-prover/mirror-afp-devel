section \<open>Signed measures\<close>

text \<open>In this section we define signed measures. These are generalizations of measures that can also 
take negative values but cannot contain both $\infty$ and $-\infty$ in their range.\<close>

subsection \<open>Basic definitions\<close>
theory Hahn_Jordan_Decomposition imports 
  "HOL-Probability.Probability" 
  Hahn_Jordan_Prelims
begin

definition signed_measure::"'a measure \<Rightarrow> ('a set \<Rightarrow> ereal) \<Rightarrow> bool" where
  "signed_measure M \<mu> \<longleftrightarrow> \<mu> {} = 0 \<and> (-\<infinity> \<notin> range \<mu> \<or> \<infinity> \<notin> range \<mu>) \<and> 
  (\<forall>A. range A \<subseteq> sets M \<longrightarrow> disjoint_family A \<longrightarrow> \<Union> (range A) \<in> sets M \<longrightarrow> 
  (\<lambda>i. \<mu> (A i)) sums \<mu> (\<Union> (range A))) \<and>
  (\<forall>A. range A \<subseteq> sets M \<longrightarrow> disjoint_family A \<longrightarrow> \<Union> (range A) \<in> sets M \<longrightarrow> 
  \<bar>\<mu> (\<Union> (range A))\<bar> < \<infinity> \<longrightarrow> summable (\<lambda>i. real_of_ereal \<bar>\<mu> (A i)\<bar>))"

lemma signed_measure_empty:
  assumes "signed_measure M \<mu>"
  shows "\<mu> {} = 0" using assms unfolding signed_measure_def by simp

lemma signed_measure_sums:
  assumes "signed_measure M \<mu>"
    and "range A \<subseteq> M"
    and "disjoint_family A"
    and "\<Union> (range A) \<in> sets M"
  shows "(\<lambda>i. \<mu> (A i)) sums \<mu> (\<Union> (range A))"
  using assms unfolding signed_measure_def by simp

lemma signed_measure_summable:
  assumes "signed_measure M \<mu>"
    and "range A \<subseteq> M"
    and "disjoint_family A"
    and "\<Union> (range A) \<in> sets M"
    and "\<bar>\<mu> (\<Union> (range A))\<bar> < \<infinity>"
  shows "summable (\<lambda>i. real_of_ereal \<bar>\<mu> (A i)\<bar>)"
  using assms unfolding signed_measure_def by simp

lemma signed_measure_inf_sum:
  assumes "signed_measure M \<mu>"
    and "range A \<subseteq> M"
    and "disjoint_family A"
    and "\<Union> (range A) \<in> sets M"
  shows "(\<Sum>i. \<mu> (A i)) = \<mu> (\<Union> (range A))" using sums_unique assms 
    signed_measure_sums by (metis)

lemma signed_measure_abs_convergent:
  assumes "signed_measure M \<mu>"
    and "range A \<subseteq> sets M"
    and "disjoint_family A"
    and "\<Union> (range A) \<in> sets M"
    and "\<bar>\<mu> (\<Union> (range A))\<bar> < \<infinity>"
  shows "summable (\<lambda>i. real_of_ereal \<bar>\<mu> (A i)\<bar>)" using assms 
  unfolding signed_measure_def by simp

lemma signed_measure_additive:
  assumes "signed_measure M \<mu>"
  shows "additive M \<mu>"
proof (auto simp add: additive_def)
  fix x y
  assume x: "x \<in> M" and y: "y \<in> M" and "x \<inter> y = {}"
  hence "disjoint_family (binaryset x y)"
    by (auto simp add: disjoint_family_on_def binaryset_def)
  have "(\<lambda>i. \<mu> ((binaryset x y) i)) sums (\<mu> x + \<mu> y)"  using binaryset_sums 
      signed_measure_empty[of M \<mu>] assms  by simp
  have "range (binaryset x y) = {x, y, {}}" using range_binaryset_eq by simp
  moreover have "{x, y, {}} \<subseteq> M" using x y by auto
  moreover have "x\<union>y \<in> sets M" using x y by simp
  moreover have "(\<Union> (range (binaryset x y))) = x\<union> y"
    by (simp add: calculation(1))
  ultimately have "(\<lambda>i. \<mu> ((binaryset x y) i)) sums \<mu> (x \<union> y)" using assms x y
      signed_measure_empty[of M \<mu>] signed_measure_sums[of M \<mu>]
      \<open>disjoint_family (binaryset x y)\<close> by (metis) 
  then show "\<mu> (x \<union> y) = \<mu> x + \<mu> y" 
    using \<open>(\<lambda>i. \<mu> ((binaryset x y) i)) sums (\<mu> x + \<mu> y)\<close> sums_unique2 by force
qed

lemma signed_measure_add:
  assumes "signed_measure M \<mu>"
    and "a\<in> sets M"
    and "b\<in> sets M"
    and "a\<inter> b = {}"
  shows "\<mu> (a\<union> b) = \<mu> a + \<mu> b" using additiveD[OF signed_measure_additive] 
    assms by auto

lemma signed_measure_disj_sum:
  shows "finite I \<Longrightarrow> signed_measure M \<mu> \<Longrightarrow> disjoint_family_on A I \<Longrightarrow> 
    (\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets M) \<Longrightarrow> \<mu> (\<Union> i\<in> I. A i) = (\<Sum> i\<in> I. \<mu> (A i))"
proof (induct rule:finite_induct)
  case empty
  then show ?case  unfolding signed_measure_def by simp
next
  case (insert x F)
  have "\<mu> (\<Union> (A ` insert x F)) = \<mu> ((\<Union> (A `F)) \<union> A x)" 
    by (simp add: Un_commute)
  also have "... = \<mu> (\<Union> (A `F)) + \<mu> (A x)"
  proof -
    have "(\<Union> (A `F)) \<inter> (A x) = {}" using insert
      by (metis disjoint_family_on_insert inf_commute) 
    moreover have "\<Union> (A `F) \<in> sets M" using insert by auto
    moreover have "A x \<in> sets M" using insert by simp
    ultimately show ?thesis by (meson insert.prems(1) signed_measure_add)
  qed
  also have "... = (\<Sum> i\<in> F. \<mu> (A i)) + \<mu> (A x)" using insert
    by (metis disjoint_family_on_insert insert_iff)
  also have "... = (\<Sum>i\<in>insert x F. \<mu> (A i))"
    by (simp add: add.commute insert.hyps(1) insert.hyps(2)) 
  finally show ?case .
qed

lemma pos_signed_measure_count_additive:
  assumes "signed_measure M \<mu>"
    and "\<forall> E \<in> sets M. 0 \<le> \<mu> E"
  shows "countably_additive (sets M) (\<lambda>A. e2ennreal (\<mu> A))" 
  unfolding countably_additive_def
proof (intro allI impI)
  fix A::"nat \<Rightarrow> 'a set"
  assume "range A \<subseteq> sets M"
    and "disjoint_family A"
    and "\<Union> (range A) \<in> sets M" note Aprops = this
  have eq: "\<And>i. \<mu> (A i) = enn2ereal (e2ennreal (\<mu> (A i)))" 
    using assms enn2ereal_e2ennreal Aprops by simp
  have "(\<lambda>n. \<Sum>i\<le>n. \<mu> (A i)) \<longlonglongrightarrow> \<mu> (\<Union> (range A))" using 
      sums_def_le[of "\<lambda>i. \<mu> (A i)" "\<mu> (\<Union> (range A))"] assms 
      signed_measure_sums[of M] Aprops by simp
  hence "((\<lambda>n. e2ennreal (\<Sum>i\<le>n. \<mu> (A i))) \<longlongrightarrow> 
      e2ennreal (\<mu> (\<Union> (range A)))) sequentially"
    using tendsto_e2ennrealI[of "(\<lambda>n. \<Sum>i\<le>n. \<mu> (A i))" "\<mu> (\<Union> (range A))"] 
    by simp
  moreover have "\<And>n. e2ennreal (\<Sum>i\<le>n. \<mu> (A i)) = (\<Sum>i\<le>n. e2ennreal (\<mu> (A i)))"
    using e2ennreal_finite_sum by (metis enn2ereal_nonneg eq finite_atMost)
  ultimately have "((\<lambda>n. (\<Sum>i\<le>n. e2ennreal (\<mu> (A i)))) \<longlongrightarrow> 
    e2ennreal (\<mu> (\<Union> (range A)))) sequentially" by simp
  hence "(\<lambda>i. e2ennreal (\<mu> (A i))) sums e2ennreal (\<mu> (\<Union> (range A)))" 
    using sums_def_le[of "\<lambda>i. e2ennreal (\<mu> (A i))" "e2ennreal (\<mu> (\<Union> (range A)))"] 
    by simp
  thus "(\<Sum>i. e2ennreal (\<mu> (A i))) = e2ennreal (\<mu> (\<Union> (range A)))" 
    using sums_unique assms by (metis)
qed

lemma signed_measure_minus:
  assumes "signed_measure M \<mu>"
  shows "signed_measure M (\<lambda>A. - \<mu> A)" unfolding signed_measure_def
proof (intro conjI)
  show "- \<mu> {} = 0" using assms unfolding signed_measure_def by simp
  show "- \<infinity> \<notin> range (\<lambda>A. - \<mu> A) \<or> \<infinity> \<notin> range (\<lambda>A. - \<mu> A)" 
  proof (cases "\<infinity> \<in> range \<mu>")
    case True
    hence "-\<infinity> \<notin> range \<mu>" using assms unfolding signed_measure_def by simp
    hence "\<infinity> \<notin> range (\<lambda>A. - \<mu> A)"  using ereal_uminus_eq_reorder by blast
    thus "- \<infinity> \<notin> range (\<lambda>A. - \<mu> A) \<or> \<infinity> \<notin> range (\<lambda>A. - \<mu> A)" by simp
  next
    case False
    hence "-\<infinity> \<notin> range (\<lambda>A. - \<mu> A)"  using ereal_uminus_eq_reorder 
      by (simp add: image_iff)
    thus "- \<infinity> \<notin> range (\<lambda>A. - \<mu> A) \<or> \<infinity> \<notin> range (\<lambda>A. - \<mu> A)" by simp
  qed
  show "\<forall>A. range A \<subseteq> sets M \<longrightarrow> disjoint_family A \<longrightarrow> \<Union> (range A) \<in> sets M \<longrightarrow> 
    \<bar>- \<mu> (\<Union> (range A))\<bar> < \<infinity> \<longrightarrow> summable (\<lambda>i. real_of_ereal \<bar>- \<mu> (A i)\<bar>)" 
  proof (intro allI impI)
    fix A::"nat \<Rightarrow> 'a set"
    assume  "range A \<subseteq> sets M" and "disjoint_family A" and "\<Union> (range A) \<in> sets M"
      and "\<bar>- \<mu> (\<Union> (range A))\<bar> < \<infinity>" 
    thus "summable (\<lambda>i. real_of_ereal \<bar>- \<mu> (A i)\<bar>)" using assms 
      unfolding signed_measure_def by simp
  qed
  show "\<forall>A. range A \<subseteq> sets M \<longrightarrow> disjoint_family A \<longrightarrow> \<Union> (range A) \<in> sets M \<longrightarrow> 
    (\<lambda>i. - \<mu> (A i)) sums - \<mu> (\<Union> (range A))"
  proof -
    {
      fix A::"nat \<Rightarrow> 'a set"
      assume  "range A \<subseteq> sets M" and "disjoint_family A" and 
        "\<Union> (range A) \<in> sets M" note Aprops = this
      have "- \<infinity> \<notin> range (\<lambda>i. \<mu> (A i)) \<or> \<infinity> \<notin> range (\<lambda>i. \<mu> (A i))" 
      proof -
        have "range (\<lambda>i. \<mu> (A i)) \<subseteq> range \<mu>" by auto
        thus ?thesis  using assms unfolding signed_measure_def by auto
      qed
      moreover have "(\<lambda>i. \<mu> (A i)) sums \<mu> (\<Union> (range A))" 
        using signed_measure_sums[of M] Aprops assms by simp
      ultimately have "(\<lambda>i. - \<mu> (A i)) sums - \<mu> (\<Union> (range A))" 
        using sums_minus'[of "\<lambda>i. \<mu> (A i)"] by simp
    }
    thus ?thesis by auto
  qed
qed

locale near_finite_function =
  fixes \<mu>:: "'b set \<Rightarrow> ereal"
  assumes inf_range: "- \<infinity> \<notin> range \<mu> \<or> \<infinity> \<notin> range \<mu>"

lemma (in near_finite_function) finite_subset:
  assumes "\<bar>\<mu> E\<bar> < \<infinity>"
    and "A\<subseteq> E"
    and "\<mu> E = \<mu> A + \<mu> (E - A)"
  shows "\<bar>\<mu> A\<bar> < \<infinity>"
proof (cases "\<infinity> \<in> range \<mu>")
  case False
  show ?thesis
  proof (cases "0 < \<mu> A")
    case True
    hence "\<bar>\<mu> A\<bar> = \<mu> A" by simp
    also have "... < \<infinity>" using False by (metis ereal_less_PInfty rangeI)
    finally show ?thesis .
  next
    case False
    hence "\<bar>\<mu> A\<bar> = -\<mu> A" using not_less_iff_gr_or_eq by fastforce 
    also have "... = \<mu> (E - A) - \<mu> E"
    proof -
      have "\<mu> E = \<mu> A + \<mu> (E - A)" using assms by simp 
      hence "\<mu> E - \<mu> A = \<mu> (E - A)"
        by (metis abs_ereal_uminus assms(1) calculation ereal_diff_add_inverse 
            ereal_infty_less(2)  ereal_minus(5) ereal_minus_less_iff 
            ereal_minus_less_minus ereal_uminus_uminus less_ereal.simps(2) 
            minus_ereal_def  plus_ereal.simps(3))
      thus ?thesis using assms(1) ereal_add_uminus_conv_diff ereal_eq_minus 
        by auto 
    qed
    also have "... \<le> \<mu> (E - A) + \<bar>\<mu> E\<bar>"
      by (metis \<open>- \<mu> A = \<mu> (E - A) - \<mu> E\<close> abs_ereal_less0 abs_ereal_pos 
          ereal_diff_le_self ereal_le_add_mono1 less_eq_ereal_def 
          minus_ereal_def not_le_imp_less)
    also have "... < \<infinity>" using assms \<open>\<infinity> \<notin> range \<mu>\<close>
      by (metis UNIV_I ereal_less_PInfty ereal_plus_eq_PInfty image_eqI) 
    finally show ?thesis .
  qed
next
  case True
  hence "-\<infinity> \<notin> range \<mu>" using inf_range by simp
  hence "-\<infinity> < \<mu> A" by (metis ereal_infty_less(2) rangeI) 
  show ?thesis
  proof (cases "\<mu> A < 0")
    case True
    hence "\<bar>\<mu> A\<bar> = -\<mu> A" using not_less_iff_gr_or_eq by fastforce 
    also have "... < \<infinity>" using \<open>-\<infinity> < \<mu> A\<close> using ereal_uminus_less_reorder 
      by blast 
    finally show ?thesis .
  next
    case False
    hence "\<bar>\<mu> A\<bar> = \<mu> A" by simp
    also have "... = \<mu> E - \<mu> (E - A)"
    proof -
      have "\<mu> E = \<mu> A + \<mu> (E - A)" using assms by simp  
      thus "\<mu> A = \<mu> E - \<mu> (E - A)" by (metis add.right_neutral  assms(1)
            add_diff_eq_ereal calculation ereal_diff_add_eq_diff_diff_swap 
            ereal_diff_add_inverse ereal_infty_less(1) ereal_plus_eq_PInfty 
            ereal_x_minus_x)
    qed
    also have "... \<le> \<bar>\<mu> E\<bar> - \<mu> (E - A)" 
      by (metis \<open>\<bar>\<mu> A\<bar> = \<mu> A\<close> \<open>\<mu> A = \<mu> E - \<mu> (E - A)\<close> abs_ereal_ge0 
          abs_ereal_pos abs_ereal_uminus antisym_conv ereal_0_le_uminus_iff 
          ereal_abs_diff ereal_diff_le_mono_left ereal_diff_le_self le_cases 
          less_eq_ereal_def minus_ereal_def) 
    also have "... < \<infinity>" 
    proof -
      have "-\<infinity> < \<mu> (E - A)" using \<open>-\<infinity> \<notin> range \<mu>\<close> 
        by (metis ereal_infty_less(2) rangeI) 
      hence "- \<mu> (E - A) < \<infinity>" using ereal_uminus_less_reorder by blast
      thus ?thesis using assms by (simp add: ereal_minus_eq_PInfty_iff 
            ereal_uminus_eq_reorder)
    qed
    finally show ?thesis .
  qed
qed

locale signed_measure_space=
  fixes M::"'a measure" and \<mu>
  assumes sgn_meas: "signed_measure M \<mu>"

sublocale signed_measure_space \<subseteq> near_finite_function
proof (unfold_locales)
  show "- \<infinity> \<notin> range \<mu> \<or> \<infinity> \<notin> range \<mu>" using sgn_meas 
    unfolding signed_measure_def by simp
qed

context signed_measure_space
begin
lemma signed_measure_finite_subset:
  assumes "E \<in> sets M"
    and "\<bar>\<mu> E\<bar> < \<infinity>"
    and "A\<in> sets M"
    and "A\<subseteq> E"
  shows "\<bar>\<mu> A\<bar> < \<infinity>"
proof (rule finite_subset)
  show "\<bar>\<mu> E\<bar> < \<infinity>" "A\<subseteq> E" using assms by auto
  show "\<mu> E = \<mu> A + \<mu> (E - A)" using assms 
      sgn_meas signed_measure_add[of M \<mu> A "E - A"]
    by (metis Diff_disjoint Diff_partition sets.Diff)
qed

lemma measure_space_e2ennreal :
  assumes "measure_space (space M) (sets M) m \<and> (\<forall>E \<in> sets M. m E < \<infinity>) \<and> 
    (\<forall>E \<in> sets M. m E \<ge> 0)"
  shows "\<forall>E \<in> sets M. e2ennreal (m E) < \<infinity>"
proof 
  fix E
  assume "E \<in> sets M"
  show "e2ennreal (m E) < \<infinity>"
  proof -
    have "m E < \<infinity>" using assms \<open>E \<in> sets M\<close>
      by blast
    then have "e2ennreal (m E) < \<infinity>" using e2ennreal_less_top
      using \<open>m E < \<infinity>\<close> by auto 
    thus ?thesis by simp
  qed
qed

subsection \<open>Positive and negative subsets\<close>

text \<open>The Hahn decomposition theorem is based on the notions of positive and negative measurable
sets. A measurable set is positive (resp. negative) if all its measurable subsets have a positive
(resp. negative) measure by $\mu$. The decomposition theorem states that any measure space for
a signed measure can be decomposed into a positive and a negative measurable set.\<close>

definition pos_meas_set  where
  "pos_meas_set E \<longleftrightarrow> E \<in> sets M \<and> (\<forall>A \<in> sets M. A \<subseteq> E \<longrightarrow> 0 \<le> \<mu> A)"

definition neg_meas_set  where
  "neg_meas_set E \<longleftrightarrow> E \<in> sets M \<and> (\<forall>A \<in> sets M. A \<subseteq> E \<longrightarrow> \<mu> A \<le> 0)"

lemma pos_meas_setI:
  assumes "E \<in> sets M"
    and "\<And>A. A \<in> sets M \<Longrightarrow> A \<subseteq> E \<Longrightarrow> 0 \<le> \<mu> A"
  shows "pos_meas_set E" unfolding pos_meas_set_def using assms by simp

lemma pos_meas_setD1 :
  assumes "pos_meas_set E"
  shows "E \<in> sets M"
  using assms unfolding pos_meas_set_def
  by simp

lemma neg_meas_setD1 :
  assumes "neg_meas_set E"
  shows "E \<in> sets M" using assms unfolding neg_meas_set_def by simp

lemma neg_meas_setI:
  assumes "E \<in> sets M"
    and "\<And>A. A \<in> sets M \<Longrightarrow> A \<subseteq> E \<Longrightarrow> \<mu> A \<le> 0"
  shows "neg_meas_set E" unfolding neg_meas_set_def using assms by simp

lemma pos_meas_self:
  assumes "pos_meas_set E"
  shows "0 \<le> \<mu> E" using assms unfolding pos_meas_set_def by simp

lemma empty_pos_meas_set:
  shows "pos_meas_set {}"
  by (metis bot.extremum_uniqueI eq_iff pos_meas_set_def sets.empty_sets 
      sgn_meas signed_measure_empty)

lemma empty_neg_meas_set:
  shows "neg_meas_set {}"
  by (metis neg_meas_set_def order_refl sets.empty_sets sgn_meas 
      signed_measure_empty subset_empty)

lemma pos_measure_meas:
  assumes "pos_meas_set E"
    and "A\<subseteq> E"
    and "A\<in> sets M"
  shows "0 \<le> \<mu> A" using assms unfolding pos_meas_set_def by simp

lemma pos_meas_subset:
  assumes "pos_meas_set A"
    and "B\<subseteq> A"
    and "B\<in> sets M"
  shows "pos_meas_set B" using  assms pos_meas_set_def by auto 

lemma neg_meas_subset:
  assumes "neg_meas_set A"
    and "B\<subseteq> A"
    and "B\<in> sets M"
  shows "neg_meas_set B" using  assms neg_meas_set_def by auto 

lemma pos_meas_set_Union:
  assumes "\<And>(i::nat). pos_meas_set (A i)"
    and "\<And>i. A i \<in> sets M"
    and "\<bar>\<mu> (\<Union> i. A i)\<bar> < \<infinity>"
  shows "pos_meas_set (\<Union> i. A i)"
proof (rule pos_meas_setI)
  show "\<Union> (range A) \<in> sets M" using sigma_algebra.countable_UN assms by simp
  obtain B where "disjoint_family B" and "(\<Union>(i::nat). B i) = (\<Union>(i::nat). A i)"
    and "\<And>i. B i \<in> sets M" and "\<And>i. B i \<subseteq> A i" using disj_Union2 assms by auto 
  fix C
  assume "C \<in> sets M" and "C\<subseteq> (\<Union> i. A i)"
  hence "C = C \<inter> (\<Union> i. A i)" by auto
  also have "... = C \<inter> (\<Union> i. B i)" using \<open>(\<Union>i. B i) = (\<Union>i. A i)\<close> by simp
  also have "... = (\<Union> i. C \<inter> B i)" by auto
  finally have "C = (\<Union> i. C \<inter> B i)" .
  hence "\<mu> C = \<mu> (\<Union> i. C \<inter> B i)" by simp
  also have "... = (\<Sum>i. \<mu> (C \<inter> (B i)))"
  proof (rule signed_measure_inf_sum[symmetric])
    show "signed_measure M \<mu>" using sgn_meas by simp
    show "disjoint_family (\<lambda>i. C \<inter> B i)" using \<open>disjoint_family B\<close>
      by (meson Int_iff disjoint_family_subset subset_iff)
    show "range (\<lambda>i. C \<inter> B i) \<subseteq> sets M" using \<open>C\<in> sets M\<close> \<open>\<And>i. B i \<in> sets M\<close> 
      by auto
    show "(\<Union>i. C \<inter> B i) \<in> sets M" using \<open>C = (\<Union> i. C \<inter> B i)\<close> \<open>C\<in> sets M\<close> 
      by simp
  qed
  also have "... \<ge> 0" 
  proof (rule suminf_nonneg)
    show "\<And>n. 0 \<le> \<mu> (C \<inter> B n)"
    proof -
      fix n
      have "C\<inter> B n \<subseteq> A n" using \<open>\<And>i. B i \<subseteq> A i\<close> by auto
      moreover have "C \<inter> B n \<in> sets M" using \<open>C\<in> sets M\<close> \<open>\<And>i. B i \<in> sets M\<close> 
        by simp
      ultimately show "0 \<le> \<mu> (C \<inter> B n)" using assms pos_measure_meas[of "A n"] 
        by simp
    qed
    have "summable (\<lambda>i. real_of_ereal (\<mu> (C \<inter> B i)))"
    proof (rule summable_norm_cancel)
      have "\<And>n. norm (real_of_ereal (\<mu> (C \<inter> B n))) = 
        real_of_ereal \<bar>\<mu> (C \<inter> B n)\<bar>" by simp
      moreover have "summable (\<lambda>i. real_of_ereal \<bar>\<mu> (C \<inter> B i)\<bar>)"
      proof (rule signed_measure_abs_convergent)
        show "signed_measure M \<mu>" using sgn_meas by simp
        show "range (\<lambda>i. C \<inter> B i) \<subseteq> sets M" using \<open>C\<in> sets M\<close> 
            \<open>\<And>i. B i \<in> sets M\<close> by auto
        show "disjoint_family (\<lambda>i. C \<inter> B i)" using \<open>disjoint_family B\<close>
          by (meson Int_iff disjoint_family_subset subset_iff)
        show "(\<Union>i. C \<inter> B i) \<in> sets M" using \<open>C = (\<Union> i. C \<inter> B i)\<close> \<open>C\<in> sets M\<close> 
          by simp
        have "\<bar>\<mu> C\<bar> < \<infinity>"
        proof (rule signed_measure_finite_subset)
          show "(\<Union> i. A i) \<in> sets M" using assms by simp
          show "\<bar>\<mu> (\<Union> (range A))\<bar> < \<infinity>" using assms by simp
          show "C \<in> sets M" using \<open>C \<in> sets M\<close> .
          show "C \<subseteq> \<Union> (range A)" using \<open>C \<subseteq> \<Union> (range A) \<close> .
        qed
        thus "\<bar>\<mu> (\<Union>i. C \<inter> B i)\<bar> < \<infinity>" using \<open>C = (\<Union> i. C \<inter> B i)\<close> by simp
      qed
      ultimately show "summable (\<lambda>n. norm (real_of_ereal (\<mu> (C \<inter> B n))))" 
        by auto
    qed
    thus "summable (\<lambda>i. \<mu> (C \<inter> B i))" by (simp add: \<open>\<And>n. 0 \<le> \<mu> (C \<inter> B n)\<close> 
          summable_ereal_pos)
  qed
  finally show "0 \<le> \<mu> C" .
qed

lemma pos_meas_set_pos_lim:
  assumes "\<And>(i::nat). pos_meas_set (A i)"
    and "\<And>i. A i \<in> sets M"
  shows "0 \<le> \<mu> (\<Union> i. A i)" 
proof -
  obtain B where "disjoint_family B" and "(\<Union>(i::nat). B i) = (\<Union>(i::nat). A i)"
    and "\<And>i. B i \<in> sets M" and "\<And>i. B i \<subseteq> A i" using disj_Union2 assms by auto 
  note Bprops = this
  have sums: "(\<lambda>n. \<mu> (B n)) sums \<mu> (\<Union>i. B i)" 
  proof (rule signed_measure_sums)
    show "signed_measure M \<mu>" using sgn_meas .
    show "range B \<subseteq> sets M" using Bprops by auto
    show "disjoint_family B" using Bprops by simp
    show "\<Union> (range B) \<in> sets M" using Bprops by blast
  qed
  hence "summable (\<lambda>n. \<mu> (B n))" using sums_summable[of "\<lambda>n. \<mu> (B n)"] by simp
  hence "suminf (\<lambda>n. \<mu> (B n)) = \<mu> (\<Union>i. B i)" using sums sums_iff by auto
  thus ?thesis using suminf_nonneg
    by (metis Bprops(2) Bprops(3) Bprops(4) \<open>summable (\<lambda>n. \<mu> (B n))\<close> assms(1) 
        pos_measure_meas)
qed

lemma pos_meas_disj_union:
  assumes "pos_meas_set A"
    and "pos_meas_set B"
    and "A\<inter> B = {}"
  shows "pos_meas_set (A \<union> B)" unfolding pos_meas_set_def
proof (intro conjI ballI impI)
  show "A\<union> B \<in> sets M"
    by (metis assms(1) assms(2) pos_meas_set_def sets.Un)
next
  fix C
  assume "C\<in> sets M" and "C\<subseteq> A\<union> B"
  define DA where "DA = C\<inter> A"
  define DB where "DB = C\<inter> B"
  have "DA\<in> sets M" using DA_def \<open>C \<in> sets M\<close> assms(1) pos_meas_set_def 
    by blast
  have "DB\<in> sets M" using DB_def \<open>C \<in> sets M\<close> assms(2) pos_meas_set_def 
    by blast 
  have "DA \<inter> DB = {}" unfolding DA_def DB_def using assms by auto
  have "C = DA \<union> DB" unfolding DA_def DB_def using \<open>C\<subseteq> A\<union> B\<close> by auto
  have "0 \<le> \<mu> DB" using assms unfolding DB_def pos_meas_set_def
    by (metis  DB_def Int_lower2\<open>DB \<in> sets M\<close>)
  also have "... \<le> \<mu> DA + \<mu> DB" using assms unfolding  pos_meas_set_def
    by (metis DA_def Diff_Diff_Int Diff_subset Int_commute \<open>DA \<in> sets M\<close> 
        ereal_le_add_self2)
  also have "... = \<mu> C" using signed_measure_add sgn_meas \<open>DA \<in> sets M\<close> 
      \<open>DB \<in> sets M\<close> \<open>DA \<inter> DB = {}\<close> \<open>C = DA \<union> DB\<close> by metis
  finally show "0 \<le> \<mu> C" .
qed

lemma pos_meas_set_union:
  assumes "pos_meas_set A"
    and "pos_meas_set B"
  shows "pos_meas_set (A \<union> B)" 
proof -
  define C where "C = B - A"
  have "A\<union> C = A\<union> B" unfolding C_def by auto
  moreover have "pos_meas_set (A\<union> C)" 
  proof (rule pos_meas_disj_union)
    show "pos_meas_set C" unfolding C_def
      by (meson Diff_subset assms(1) assms(2) sets.Diff 
          signed_measure_space.pos_meas_set_def 
          signed_measure_space.pos_meas_subset signed_measure_space_axioms)
    show "pos_meas_set A" using assms by simp
    show "A \<inter> C = {}" unfolding C_def by auto
  qed
  ultimately show ?thesis by simp
qed

lemma neg_meas_disj_union:
  assumes "neg_meas_set A"
    and "neg_meas_set B"
    and "A\<inter> B = {}"
  shows "neg_meas_set (A \<union> B)" unfolding neg_meas_set_def
proof (intro conjI ballI impI)
  show "A\<union> B \<in> sets M"
    by (metis assms(1) assms(2) neg_meas_set_def sets.Un)
next
  fix C
  assume "C\<in> sets M" and "C\<subseteq> A\<union> B"
  define DA where "DA = C\<inter> A"
  define DB where "DB = C\<inter> B"
  have "DA\<in> sets M" using DA_def \<open>C \<in> sets M\<close> assms(1) neg_meas_set_def 
    by blast
  have "DB\<in> sets M" using DB_def \<open>C \<in> sets M\<close> assms(2) neg_meas_set_def 
    by blast 
  have "DA \<inter> DB = {}" unfolding DA_def DB_def using assms by auto
  have "C = DA \<union> DB" unfolding DA_def DB_def using \<open>C\<subseteq> A\<union> B\<close> by auto
  have "\<mu> C = \<mu> DA + \<mu> DB" using signed_measure_add sgn_meas \<open>DA \<in> sets M\<close> 
      \<open>DB \<in> sets M\<close> \<open>DA \<inter> DB = {}\<close> \<open>C = DA \<union> DB\<close> by metis
  also have "... \<le> \<mu> DB" using assms unfolding  neg_meas_set_def
    by (metis DA_def Int_lower2 \<open>DA \<in> sets M\<close> add_decreasing dual_order.refl)
  also have "... \<le> 0" using assms unfolding DB_def neg_meas_set_def
    by (metis  DB_def Int_lower2\<open>DB \<in> sets M\<close>) 
  finally show "\<mu> C \<le> 0" .
qed

lemma neg_meas_set_union:
  assumes "neg_meas_set A"
    and "neg_meas_set B"
  shows "neg_meas_set (A \<union> B)" 
proof -
  define C where "C = B - A"
  have "A\<union> C = A\<union> B" unfolding C_def by auto
  moreover have "neg_meas_set (A\<union> C)" 
  proof (rule neg_meas_disj_union)
    show "neg_meas_set C" unfolding C_def
      by (meson Diff_subset assms(1) assms(2) sets.Diff neg_meas_set_def 
          neg_meas_subset signed_measure_space_axioms)
    show "neg_meas_set A" using assms by simp
    show "A \<inter> C = {}" unfolding C_def by auto
  qed
  ultimately show ?thesis by simp
qed

lemma neg_meas_self :
  assumes "neg_meas_set E"
  shows "\<mu> E \<le> 0" using assms unfolding neg_meas_set_def by simp

lemma pos_meas_set_opp:
  assumes "signed_measure_space.pos_meas_set  M (\<lambda> A. - \<mu> A) A"
  shows "neg_meas_set A"
proof - 
  have m_meas_pos : "signed_measure M  (\<lambda> A. - \<mu> A)"
    using assms signed_measure_space_def 
    by (simp add: sgn_meas signed_measure_minus)
  thus ?thesis
    by (metis assms ereal_0_le_uminus_iff neg_meas_setI 
        signed_measure_space.intro signed_measure_space.pos_meas_set_def) 
qed

lemma neg_meas_set_opp:
  assumes "signed_measure_space.neg_meas_set M (\<lambda> A. - \<mu> A) A"
  shows "pos_meas_set A"
proof -
  have m_meas_neg : "signed_measure M  (\<lambda> A. - \<mu> A)"
    using assms signed_measure_space_def 
    by (simp add: sgn_meas signed_measure_minus)
  thus ?thesis
    by (metis assms ereal_uminus_le_0_iff m_meas_neg pos_meas_setI 
        signed_measure_space.intro signed_measure_space.neg_meas_set_def)
qed
end

lemma signed_measure_inter:
  assumes "signed_measure M \<mu>"
    and "A \<in> sets M"
  shows "signed_measure M (\<lambda>E. \<mu> (E \<inter> A))" unfolding signed_measure_def
proof (intro conjI)
  show "\<mu> ({} \<inter> A) = 0" using assms(1) signed_measure_empty by auto 
  show "- \<infinity> \<notin> range (\<lambda>E. \<mu> (E \<inter> A)) \<or> \<infinity> \<notin> range (\<lambda>E. \<mu> (E \<inter> A))"
  proof (rule ccontr)
    assume "\<not> (- \<infinity> \<notin> range (\<lambda>E. \<mu> (E \<inter> A)) \<or> \<infinity> \<notin> range (\<lambda>E. \<mu> (E \<inter> A)))"
    hence "- \<infinity> \<in> range (\<lambda>E. \<mu> (E \<inter> A)) \<and> \<infinity> \<in> range (\<lambda>E. \<mu> (E \<inter> A))" by simp
    hence "- \<infinity> \<in> range \<mu> \<and> \<infinity> \<in> range \<mu>" by auto
    thus False using assms unfolding signed_measure_def by simp
  qed
  show "\<forall>E. range E \<subseteq> sets M \<longrightarrow> disjoint_family E \<longrightarrow> \<Union> (range E) \<in> sets M \<longrightarrow> 
    (\<lambda>i. \<mu> (E i \<inter> A)) sums \<mu> (\<Union> (range E) \<inter> A)"
  proof (intro allI impI)
    fix E::"nat \<Rightarrow> 'a set"
    assume "range E \<subseteq> sets M" and "disjoint_family E" and "\<Union> (range E) \<in> sets M" 
    note Eprops = this
    define F where "F = (\<lambda>i. E i \<inter> A)"
    have "(\<lambda>i. \<mu> (F i)) sums \<mu> (\<Union> (range F))" 
    proof (rule signed_measure_sums)
      show "signed_measure M \<mu>" using assms by simp
      show "range F \<subseteq> sets M" using Eprops F_def assms by blast
      show "disjoint_family F" using Eprops F_def assms
        by (metis disjoint_family_subset inf.absorb_iff2 inf_commute 
            inf_right_idem)
      show "\<Union> (range F) \<in> sets M" using Eprops assms unfolding F_def
        by (simp add: Eprops assms countable_Un_Int(1) sets.Int)
    qed
    moreover have "\<Union> (range F) = A \<inter> \<Union> (range E)" unfolding F_def by auto   
    ultimately show "(\<lambda>i. \<mu> (E i \<inter> A)) sums \<mu> (\<Union> (range E) \<inter> A)" 
      unfolding F_def by simp
  qed
  show "\<forall>E. range E \<subseteq> sets M \<longrightarrow>
         disjoint_family E \<longrightarrow>
         \<Union> (range E) \<in> sets M \<longrightarrow> \<bar>\<mu> (\<Union> (range E) \<inter> A)\<bar> < \<infinity> \<longrightarrow> 
         summable (\<lambda>i. real_of_ereal \<bar>\<mu> (E i \<inter> A)\<bar>)"
  proof (intro allI impI)
    fix E::"nat \<Rightarrow> 'a set"
    assume "range E \<subseteq> sets M" and "disjoint_family E" and 
      "\<Union> (range E) \<in> sets M" and "\<bar>\<mu> (\<Union> (range E) \<inter> A)\<bar> < \<infinity>" note Eprops = this
    show "summable (\<lambda>i. real_of_ereal \<bar>\<mu> (E i \<inter> A)\<bar>)"
    proof (rule signed_measure_summable)
      show "signed_measure M \<mu>" using assms by simp
      show "range (\<lambda>i. E i \<inter> A) \<subseteq> sets M" using Eprops assms by blast
      show "disjoint_family (\<lambda>i. E i \<inter> A)" using Eprops assms 
          disjoint_family_subset inf.absorb_iff2 inf_commute inf_right_idem 
        by fastforce
      show "(\<Union>i. E i \<inter> A) \<in> sets M" using Eprops assms 
        by (simp add: Eprops assms countable_Un_Int(1) sets.Int)
      show "\<bar>\<mu> (\<Union>i. E i \<inter> A)\<bar> < \<infinity>" using Eprops by auto
    qed
  qed
qed

context signed_measure_space
begin
lemma pos_signed_to_meas_space :
  assumes "pos_meas_set M1"
    and "m1 = (\<lambda>A. \<mu> (A \<inter> M1))"
  shows "measure_space (space M) (sets M) m1" unfolding measure_space_def
proof (intro conjI)
  show "sigma_algebra (space M) (sets M)"
    by (simp add: sets.sigma_algebra_axioms)
  show "positive (sets M) m1" using assms unfolding pos_meas_set_def
    by (metis Sigma_Algebra.positive_def Un_Int_eq(4) 
        e2ennreal_neg neg_meas_self sup_bot_right empty_neg_meas_set)
  show "countably_additive (sets M) m1" 
  proof (rule pos_signed_measure_count_additive)
    show "\<forall>E\<in>sets M. 0 \<le> m1 E" by (metis assms inf.cobounded2 
          pos_meas_set_def sets.Int) 
    show "signed_measure M m1" using assms pos_meas_set_def 
        signed_measure_inter[of M \<mu> M1] sgn_meas by blast
  qed
qed

lemma neg_signed_to_meas_space :
  assumes "neg_meas_set M2" 
    and "m2 = (\<lambda>A. -\<mu> (A \<inter> M2))"
  shows "measure_space (space M) (sets M) m2" unfolding measure_space_def
proof (intro conjI)
  show "sigma_algebra (space M) (sets M)"
    by (simp add: sets.sigma_algebra_axioms)
  show "positive (sets M) m2" using assms unfolding neg_meas_set_def
    by (metis Sigma_Algebra.positive_def e2ennreal_neg ereal_uminus_zero 
        inf.absorb_iff2 inf.orderE inf_bot_right neg_meas_self pos_meas_self 
        empty_neg_meas_set empty_pos_meas_set)
  show "countably_additive (sets M) m2" 
  proof (rule pos_signed_measure_count_additive)
    show "\<forall>E\<in>sets M. 0 \<le> m2 E"
      by (metis assms ereal_uminus_eq_reorder ereal_uminus_le_0_iff 
          inf.cobounded2 neg_meas_set_def sets.Int) 
    have "signed_measure M (\<lambda>A. \<mu> (A \<inter> M2))" using assms neg_meas_set_def
        signed_measure_inter[of M \<mu> M2] sgn_meas by blast
    thus "signed_measure M m2" using signed_measure_minus assms by simp 
  qed
qed

lemma pos_part_meas_nul_neg_set :
  assumes "pos_meas_set M1" 
    and "neg_meas_set M2" 
    and "m1 = (\<lambda>A. \<mu> (A \<inter> M1))"
    and "E \<in> sets M"
    and "E \<subseteq> M2"
  shows "m1 E = 0"
proof -
  have "m1 E \<ge> 0" using assms unfolding pos_meas_set_def
    by (simp add: \<open>E \<in> sets M\<close> sets.Int) 
  have "\<mu> E \<le> 0" using \<open>E \<subseteq> M2\<close> assms unfolding neg_meas_set_def
    using \<open>E \<in> sets M\<close> by blast 
  then have "m1 E \<le> 0" using \<open>\<mu> E \<le> 0\<close> assms
    by (metis Int_Un_eq(1) Un_subset_iff \<open>E \<in> sets M\<close> \<open>E \<subseteq> M2\<close> pos_meas_setD1 
        sets.Int signed_measure_space.neg_meas_set_def 
        signed_measure_space_axioms)
  thus "m1 E = 0" using \<open>m1 E \<ge> 0\<close> \<open>m1 E \<le> 0\<close> by auto
qed

lemma neg_part_meas_nul_pos_set :
  assumes "pos_meas_set M1" 
    and "neg_meas_set M2" 
    and "m2 = (\<lambda>A. -\<mu> (A \<inter> M2))"
    and "E \<in> sets M"
    and "E \<subseteq> M1"
  shows "m2 E = 0"
proof -
  have "m2 E \<ge> 0" using assms unfolding neg_meas_set_def
    by (simp add: \<open>E \<in> sets M\<close> sets.Int) 
  have "\<mu> E \<ge> 0" using  assms unfolding pos_meas_set_def by blast 
  then have "m2 E \<le> 0" using \<open>\<mu> E \<ge> 0\<close> assms
    by (metis \<open>E \<in> sets M\<close> \<open>E \<subseteq> M1\<close> ereal_0_le_uminus_iff ereal_uminus_uminus 
        inf_sup_ord(1) neg_meas_setD1 pos_meas_set_def pos_meas_subset 
        sets.Int)
  thus "m2 E = 0" using \<open>m2 E \<ge> 0\<close> \<open>m2 E \<le> 0\<close> by auto
qed

definition pos_sets where 
  "pos_sets = {A. A \<in> sets M   \<and> pos_meas_set A}"

definition pos_img where 
  "pos_img = {\<mu> A|A. A\<in> pos_sets}"

subsection \<open>Essential uniqueness\<close>

text \<open>In this part, under the assumption that a measure space for a signed measure admits a
decomposition into a positive and a negative set, we prove that this decomposition is
essentially unique; in other words, that if two such decompositions $(P,N)$ and $(X,Y)$ exist, 
then any measurable subset of $(P\triangle X) \cup (N \triangle Y)$ has a null measure.\<close>

definition hahn_space_decomp where
  "hahn_space_decomp M1 M2 \<equiv> (pos_meas_set M1) \<and> (neg_meas_set M2) \<and> 
(space M = M1 \<union> M2) \<and> (M1 \<inter> M2 = {})"

lemma pos_neg_null_set:
  assumes "pos_meas_set A"
    and "neg_meas_set A"
  shows "\<mu> A = 0" using assms pos_meas_self[of A] neg_meas_self[of A] by simp

lemma pos_diff_neg_meas_set:
  assumes "(pos_meas_set M1)" 
    and "(neg_meas_set N2)" 
    and "(space M = N1 \<union> N2)" 
    and "N1 \<in> sets M"
  shows "neg_meas_set ((M1 - N1) \<inter> space M)" using assms neg_meas_subset
  by (metis Diff_subset_conv Int_lower2 pos_meas_setD1 sets.Diff 
      sets.Int_space_eq2)

lemma neg_diff_pos_meas_set:
  assumes "(neg_meas_set M2)" 
    and "(pos_meas_set N1)" 
    and "(space M = N1 \<union> N2)" 
    and "N2 \<in> sets M"
  shows "pos_meas_set ((M2 - N2) \<inter> space M)" 
proof -
  have "(M2 - N2) \<inter> space M \<subseteq> N1" using assms by auto
  thus ?thesis using assms pos_meas_subset neg_meas_setD1 by blast
qed

lemma pos_sym_diff_neg_meas_set:
  assumes "hahn_space_decomp M1 M2"
    and "hahn_space_decomp N1 N2"
  shows "neg_meas_set ((sym_diff M1 N1) \<inter> space M)" using assms 
  unfolding hahn_space_decomp_def
  by (metis Int_Un_distrib2 neg_meas_set_union pos_meas_setD1 
      pos_diff_neg_meas_set) 

lemma neg_sym_diff_pos_meas_set:
  assumes "hahn_space_decomp M1 M2"
    and "hahn_space_decomp N1 N2"
  shows "pos_meas_set ((sym_diff M2 N2) \<inter> space M)" using assms 
    neg_diff_pos_meas_set unfolding hahn_space_decomp_def
  by (metis (no_types, lifting) Int_Un_distrib2 neg_meas_setD1 
      pos_meas_set_union)

lemma pos_meas_set_diff:
  assumes "pos_meas_set A"
    and "B\<in> sets M"
  shows "pos_meas_set ((A - B) \<inter> (space M))" using pos_meas_subset
  by (metis Diff_subset assms(1) assms(2) pos_meas_setD1 sets.Diff 
      sets.Int_space_eq2)

lemma pos_meas_set_sym_diff:
  assumes "pos_meas_set A"
    and "pos_meas_set B"
  shows "pos_meas_set ((sym_diff A B) \<inter> space M)" using pos_meas_set_diff
  by (metis Int_Un_distrib2 assms(1) assms(2) pos_meas_setD1 
      pos_meas_set_union)

lemma neg_meas_set_diff:
  assumes "neg_meas_set A"
    and "B\<in> sets M"
  shows "neg_meas_set ((A - B) \<inter> (space M))" using neg_meas_subset
  by (metis Diff_subset assms(1) assms(2) neg_meas_setD1 sets.Diff 
      sets.Int_space_eq2)

lemma neg_meas_set_sym_diff:
  assumes "neg_meas_set A"
    and "neg_meas_set B"
  shows "neg_meas_set ((sym_diff A B) \<inter> space M)" using neg_meas_set_diff
  by (metis Int_Un_distrib2 assms(1) assms(2) neg_meas_setD1 
      neg_meas_set_union)

lemma hahn_decomp_space_diff:
  assumes "hahn_space_decomp M1 M2"
    and "hahn_space_decomp N1 N2"
  shows "pos_meas_set ((sym_diff M1 N1 \<union> sym_diff M2 N2) \<inter> space M)"
    "neg_meas_set ((sym_diff M1 N1 \<union> sym_diff M2 N2) \<inter> space M)"
proof -
  show "pos_meas_set ((sym_diff M1 N1 \<union> sym_diff M2 N2) \<inter> space M)"
    by (metis Int_Un_distrib2 assms(1) assms(2) hahn_space_decomp_def 
        neg_sym_diff_pos_meas_set pos_meas_set_sym_diff pos_meas_set_union)
  show "neg_meas_set ((sym_diff M1 N1 \<union> sym_diff M2 N2) \<inter> space M)"
    by (metis Int_Un_distrib2 assms(1) assms(2) hahn_space_decomp_def 
        neg_meas_set_sym_diff neg_meas_set_union pos_sym_diff_neg_meas_set)
qed

lemma hahn_decomp_ess_unique:
  assumes "hahn_space_decomp M1 M2"
    and "hahn_space_decomp N1 N2"
    and "C \<subseteq> sym_diff M1 N1 \<union> sym_diff M2 N2"
    and "C\<in> sets M"
  shows "\<mu> C = 0"
proof -
  have "C\<subseteq> (sym_diff M1 N1 \<union> sym_diff M2 N2) \<inter> space M" using assms
    by (simp add: sets.sets_into_space)     
  thus ?thesis using assms hahn_decomp_space_diff pos_neg_null_set
    by (meson neg_meas_subset pos_meas_subset)
qed

section \<open>Existence of a positive subset\<close>

text \<open>The goal of this part is to prove that any measurable set of finite and positive measure must 
contain a positive subset with a strictly positive measure.\<close>

subsection \<open>A sequence of negative subsets\<close>

definition inf_neg where
  "inf_neg A = (if (A \<notin> sets M \<or> pos_meas_set A) then (0::nat) 
  else Inf {n|n. (1::nat) \<le> n \<and> (\<exists>B \<in> sets M. B  \<subseteq> A \<and> \<mu> B < ereal(-1/n))})"

lemma inf_neg_ne:
  assumes "A \<in> sets M"
    and "\<not> pos_meas_set A"
  shows "{n::nat|n. (1::nat) \<le> n \<and> 
  (\<exists>B \<in> sets M. B  \<subseteq> A \<and> \<mu> B < ereal (-1/n))} \<noteq> {}"  
proof -
  define N where "N = {n::nat|n. (1::nat) \<le> n \<and> 
    (\<exists>B \<in> sets M. B  \<subseteq> A \<and> \<mu> B < ereal (-1/n))}"
  have "\<exists>B \<in> sets M. B\<subseteq> A \<and> \<mu> B < 0" using assms unfolding pos_meas_set_def 
    by auto
  from this obtain B where "B\<in> sets M" and "B\<subseteq> A" and "\<mu> B < 0" by auto
  hence "\<exists>n::nat. (1::nat) \<le> n \<and> \<mu> B < ereal (-1/n)" 
  proof (cases "\<mu> B = -\<infinity>")
    case True
    hence "\<mu> B < -1/(2::nat)" by simp
    thus ?thesis using numeral_le_real_of_nat_iff one_le_numeral by blast 
  next
    case False
    hence "real_of_ereal (\<mu> B) < 0" using \<open>\<mu> B < 0\<close>
      by (metis Infty_neq_0(3) ereal_mult_eq_MInfty ereal_zero_mult 
          less_eq_ereal_def less_eq_real_def less_ereal.simps(2) 
          real_of_ereal_eq_0 real_of_ereal_le_0)
    hence "\<exists>n::nat. Suc 0 \<le> n \<and> real_of_ereal (\<mu> B) < -1/n"
    proof -
      define nw where "nw =  Suc (nat (floor (-1/ (real_of_ereal (\<mu> B)))))"
      have "Suc 0 \<le> nw" unfolding nw_def by simp
      have "0 < -1/ (real_of_ereal (\<mu> B))" using \<open>real_of_ereal (\<mu> B) < 0\<close> 
        by simp
      have "-1/ (real_of_ereal (\<mu> B)) < nw" unfolding nw_def by linarith
      hence "1/nw < 1/(-1/ (real_of_ereal (\<mu> B)))" 
        using \<open>0 < -1/ (real_of_ereal (\<mu> B))\<close> by (metis frac_less2 
            le_eq_less_or_eq of_nat_1 of_nat_le_iff zero_less_one)
      also have "... = - (real_of_ereal (\<mu> B))" by simp
      finally have "1/nw < - (real_of_ereal (\<mu> B))" .
      hence "real_of_ereal (\<mu> B) < -1/nw" by simp
      thus ?thesis using \<open>Suc 0 \<le> nw\<close> by auto
    qed
    from this obtain n1::nat where "Suc 0 \<le> n1" 
      and "real_of_ereal (\<mu> B) < -1/n1" by auto
    hence "ereal (real_of_ereal (\<mu> B)) < -1/n1" using real_ereal_leq[of "\<mu> B"] 
        \<open>\<mu> B < 0\<close> by simp
    moreover have "\<mu> B = real_of_ereal (\<mu> B)" using \<open>\<mu> B < 0\<close> False
      by (metis less_ereal.simps(2) real_of_ereal.elims zero_ereal_def)
    ultimately show ?thesis  using \<open>Suc 0 \<le> n1\<close> by auto 
  qed
  from this obtain n0::nat where "(1::nat) \<le> n0" and "\<mu> B < -1/n0" by auto
  hence "n0 \<in> {n::nat|n. (1::nat) \<le> n \<and> 
    (\<exists>B \<in> sets M. B  \<subseteq> A \<and> \<mu> B <  ereal(-1/n))}" 
    using \<open>B\<in> sets M\<close> \<open>B\<subseteq> A\<close> by auto
  thus ?thesis by auto
qed

lemma inf_neg_ge_1:
  assumes "A \<in> sets M"
    and "\<not> pos_meas_set A"
  shows "(1::nat) \<le> inf_neg A"
proof -
  define N where "N = {n::nat|n. (1::nat) \<le> n \<and> 
    (\<exists>B \<in> sets M. B  \<subseteq> A \<and> \<mu> B < ereal (-1/n))}"  
  have "N \<noteq> {}" unfolding N_def using assms inf_neg_ne by auto
  moreover have "\<And>n. n\<in> N \<Longrightarrow> (1::nat) \<le> n" unfolding N_def by simp
  ultimately show "1 \<le> inf_neg A" unfolding inf_neg_def N_def
    using Inf_nat_def1 assms(1) assms(2) by presburger
qed

lemma inf_neg_pos:
  assumes "A \<in> sets M"
    and "\<not> pos_meas_set A"
  shows "\<exists> B \<in> sets M. B\<subseteq> A \<and> \<mu> B < -1/(inf_neg A)"  
proof -
  define N where "N = {n::nat|n. (1::nat) \<le> n \<and> 
    (\<exists>B \<in> sets M. B  \<subseteq> A \<and> \<mu> B < ereal (-1/n))}"  
  have "N \<noteq> {}" unfolding N_def using assms inf_neg_ne by auto
  hence "Inf N \<in> N" using Inf_nat_def1[of N] by simp
  hence "inf_neg A \<in> N" unfolding N_def inf_neg_def using assms by auto
  thus ?thesis unfolding N_def by auto
qed

definition rep_neg where
  "rep_neg A  = (if (A \<notin> sets M \<or> pos_meas_set A) then {} else 
  SOME B. B \<in> sets M \<and> B \<subseteq> A \<and> \<mu> B \<le> ereal (-1 / (inf_neg A)))"

lemma g_rep_neg:
  assumes "A\<in> sets M"
    and "\<not> pos_meas_set A"
  shows "rep_neg A \<in> sets M" "rep_neg A \<subseteq> A"  
    "\<mu> (rep_neg A) \<le> ereal (-1 / (inf_neg A))" 
proof -
  have "\<exists> B. B \<in> sets M \<and> B\<subseteq> A \<and> \<mu> B \<le> -1 / (inf_neg A)" using assms 
      inf_neg_pos[of A] by auto
  from someI_ex[OF this] show "rep_neg A \<in> sets M" "rep_neg A \<subseteq> A"  
    "\<mu> (rep_neg A) \<le> -1 / (inf_neg A)" 
    unfolding rep_neg_def using assms by auto
qed

lemma rep_neg_sets:
  shows "rep_neg A \<in> sets M"
proof (cases "A \<notin> sets M \<or> pos_meas_set A")
  case True
  then show ?thesis unfolding rep_neg_def by simp
next
  case False
  then show ?thesis using g_rep_neg(1) by blast
qed

lemma rep_neg_subset:
  shows "rep_neg A \<subseteq> A"
proof (cases "A \<notin> sets M \<or> pos_meas_set A")
  case True
  then show ?thesis unfolding rep_neg_def by simp
next
  case False
  then show ?thesis using g_rep_neg(2) by blast
qed

lemma rep_neg_less:
  assumes "A\<in> sets M"
    and "\<not> pos_meas_set A"
  shows "\<mu> (rep_neg A) \<le> ereal (-1 / (inf_neg A))" using assms g_rep_neg(3) 
  by simp

lemma rep_neg_leq:
  shows "\<mu> (rep_neg A) \<le> 0"
proof (cases "A \<notin> sets M \<or> pos_meas_set A")
  case True
  hence "rep_neg A = {}" unfolding rep_neg_def by simp
  then show ?thesis using sgn_meas signed_measure_empty by force 
next
  case False
  then show ?thesis using rep_neg_less by (metis le_ereal_le minus_divide_left 
        neg_le_0_iff_le of_nat_0 of_nat_le_iff zero_ereal_def zero_le 
        zero_le_divide_1_iff) 
qed

subsection \<open>Construction of the positive subset\<close>

fun pos_wtn
  where
    pos_wtn_base: "pos_wtn E 0 = E"|
    pos_wtn_step: "pos_wtn E (Suc n) = pos_wtn E n - rep_neg (pos_wtn E n)"

lemma pos_wtn_subset:
  shows "pos_wtn E n \<subseteq> E"
proof (induct n)
  case 0
  then show ?case using pos_wtn_base by simp
next
  case (Suc n)
  hence "rep_neg (pos_wtn E n) \<subseteq> pos_wtn E n" using rep_neg_subset by simp
  then show ?case using Suc by auto
qed

lemma pos_wtn_sets:
  assumes "E\<in> sets M"
  shows "pos_wtn E n \<in> sets M"
proof (induct n)
  case 0
  then show ?case using assms by simp
next
  case (Suc n)
  then show ?case using pos_wtn_step rep_neg_sets by auto
qed

definition neg_wtn where
  "neg_wtn E (n::nat) = rep_neg (pos_wtn E n)"

lemma neg_wtn_neg_meas:
  shows "\<mu> (neg_wtn E n) \<le> 0" unfolding neg_wtn_def using rep_neg_leq by simp

lemma neg_wtn_sets:
  shows "neg_wtn E n \<in> sets M" unfolding neg_wtn_def using rep_neg_sets by simp

lemma neg_wtn_subset:
  shows "neg_wtn E n \<subseteq> E" unfolding neg_wtn_def  
  using pos_wtn_subset[of E n] rep_neg_subset[of "pos_wtn E n"] by simp

lemma neg_wtn_union_subset:
  shows "(\<Union> i \<le> n. neg_wtn E i) \<subseteq> E" using neg_wtn_subset by auto

lemma pos_wtn_Suc:
  shows "pos_wtn E (Suc n) = E - (\<Union> i \<le> n. neg_wtn E i)" unfolding neg_wtn_def
proof (induct n)
  case 0
  then show ?case using pos_wtn_base pos_wtn_step by simp
next
  case (Suc n)
  have "pos_wtn E (Suc (Suc n)) = pos_wtn E (Suc n) - 
    rep_neg (pos_wtn E (Suc n))" 
    using pos_wtn_step by simp
  also have "... = (E - (\<Union> i \<le> n. rep_neg (pos_wtn E i))) - 
    rep_neg (pos_wtn E (Suc n))"
    using Suc by simp
  also have "... = E - (\<Union> i \<le> (Suc n). rep_neg (pos_wtn E i))" 
    using diff_union[of E "\<lambda>i. rep_neg (pos_wtn E i)" n] by auto
  finally show "pos_wtn E (Suc (Suc n)) = 
    E - (\<Union> i \<le> (Suc n). rep_neg (pos_wtn E i))" .
qed

definition pos_sub where
  "pos_sub E = (\<Inter> n. pos_wtn E n)"

lemma pos_sub_sets:
  assumes "E\<in> sets M"
  shows "pos_sub E \<in> sets M" unfolding pos_sub_def using pos_wtn_sets assms 
  by auto

lemma pos_sub_subset:
  shows "pos_sub E \<subseteq> E" unfolding pos_sub_def using pos_wtn_subset by blast

lemma pos_sub_infty:
  assumes "E \<in> sets M"
    and "\<bar>\<mu> E\<bar> < \<infinity>"
  shows "\<bar>\<mu> (pos_sub E)\<bar> < \<infinity>" using signed_measure_finite_subset assms 
    pos_sub_sets pos_sub_subset by simp

lemma neg_wtn_djn:
  shows "disjoint_family (\<lambda>n. neg_wtn E n)" unfolding disjoint_family_on_def
proof -
  {
    fix n 
    fix m::nat
    assume "n < m"
    hence "\<exists>p. m = Suc p" using old.nat.exhaust by auto
    from this obtain p where "m = Suc p" by auto
    have "neg_wtn E m \<subseteq> pos_wtn E m" unfolding neg_wtn_def 
      by (simp add: rep_neg_subset)
    also have "... = E - (\<Union> i \<le> p. neg_wtn E i)" using pos_wtn_Suc \<open>m = Suc p\<close>
      by simp
    finally have "neg_wtn E m \<subseteq> E - (\<Union> i \<le> p. neg_wtn E i)" .
    moreover have "neg_wtn E n \<subseteq> (\<Union> i \<le> p. neg_wtn E i)" using \<open>n < m\<close> 
        \<open>m = Suc p\<close> by (simp add: UN_upper) 
    ultimately have "neg_wtn E n \<inter> neg_wtn E m = {}" by auto
  }
  thus "\<forall>m\<in>UNIV. \<forall>n\<in>UNIV. m \<noteq> n \<longrightarrow> neg_wtn E m \<inter> neg_wtn E n = {}"  
    by (metis inf_commute linorder_neqE_nat) 
qed
end

lemma disjoint_family_imp_on:
  assumes "disjoint_family A"
  shows "disjoint_family_on A S" 
  using assms disjoint_family_on_mono subset_UNIV by blast 

context signed_measure_space
begin
lemma neg_wtn_union_neg_meas:
  shows "\<mu> (\<Union> i \<le> n. neg_wtn E i) \<le> 0" 
proof -
  have "\<mu> (\<Union> i \<le> n. neg_wtn E i) = (\<Sum>i\<in>{.. n}. \<mu> (neg_wtn E i))" 
  proof (rule signed_measure_disj_sum, simp+)
    show "signed_measure M \<mu>" using sgn_meas .
    show "disjoint_family_on (neg_wtn E) {..n}" using neg_wtn_djn 
        disjoint_family_imp_on[of "neg_wtn E"] by simp
    show "\<And>i. i \<in> {..n} \<Longrightarrow> neg_wtn E i \<in> sets M" using neg_wtn_sets by simp
  qed
  also have "... \<le> 0" using neg_wtn_neg_meas by (simp add: sum_nonpos) 
  finally show ?thesis .
qed

lemma pos_wtn_meas_gt:
  assumes "0 < \<mu> E"
    and "E\<in> sets M"
  shows "0 < \<mu> (pos_wtn E n)"
proof (cases "n = 0")
  case True
  then show ?thesis using assms by simp
next
  case False
  hence "\<exists>m. n = Suc m" by (simp add: not0_implies_Suc) 
  from this obtain m where "n = Suc m" by auto
  hence eq: "pos_wtn E n = E - (\<Union> i \<le> m. neg_wtn E i)" using pos_wtn_Suc 
    by simp
  hence "pos_wtn E n \<inter> (\<Union> i \<le> m. neg_wtn E i) = {}" by auto
  moreover have "E = pos_wtn E n \<union> (\<Union> i \<le> m. neg_wtn E i)" 
    using eq neg_wtn_union_subset[of E m] by auto 
  ultimately have "\<mu> E = \<mu> (pos_wtn E n) + \<mu> (\<Union> i \<le> m. neg_wtn E i)" 
    using signed_measure_add[of M \<mu> "pos_wtn E n" "\<Union> i \<le> m. neg_wtn E i"] 
      pos_wtn_sets neg_wtn_sets assms sgn_meas by auto
  hence "0 < \<mu> (pos_wtn E n) + \<mu> (\<Union> i \<le> m. neg_wtn E i)" using assms by simp
  thus ?thesis using neg_wtn_union_neg_meas 
    by (metis add.right_neutral add_mono not_le) 
qed

definition union_wit where
  "union_wit E = (\<Union> n. neg_wtn E n)"

lemma union_wit_sets:
  shows "union_wit E \<in> sets M" unfolding union_wit_def
proof (intro sigma_algebra.countable_nat_UN)
  show "sigma_algebra (space M) (sets M)" 
    by (simp add: sets.sigma_algebra_axioms) 
  show "range (neg_wtn E) \<subseteq> sets M"
  proof -
    {
      fix n
      have "neg_wtn E n \<in> sets M" unfolding neg_wtn_def 
        by (simp add: rep_neg_sets)
    }
    thus ?thesis by auto
  qed
qed

lemma union_wit_subset:
  shows "union_wit E \<subseteq> E"
proof -
  {
    fix n
    have "neg_wtn E n \<subseteq> E" unfolding neg_wtn_def using pos_wtn_subset
        rep_neg_subset[of "pos_wtn E n"] by auto
  }
  thus ?thesis unfolding union_wit_def by auto
qed

lemma pos_sub_diff:
  shows "pos_sub E = E - union_wit E"
proof
  show "pos_sub E \<subseteq> E - union_wit E"
  proof -
    have "pos_sub E \<subseteq> E" using pos_sub_subset by simp
    moreover have "pos_sub E \<inter> union_wit E = {}" 
    proof (rule ccontr)
      assume "pos_sub E \<inter> union_wit E \<noteq> {}"
      hence "\<exists> a. a\<in> pos_sub E \<inter> union_wit E" by auto
      from this obtain a where "a\<in> pos_sub E \<inter> union_wit E" by auto
      hence "a\<in> union_wit E" by simp
      hence "\<exists>n. a \<in> rep_neg (pos_wtn E n)" unfolding union_wit_def neg_wtn_def
        by auto
      from this obtain n where "a \<in> rep_neg (pos_wtn E n)" by auto
      have "a \<in> pos_wtn E (Suc n)" using \<open>a\<in> pos_sub E \<inter> union_wit E\<close> 
        unfolding pos_sub_def by blast
      hence "a\<notin> rep_neg (pos_wtn E n)" using pos_wtn_step by simp
      thus False using \<open>a \<in> rep_neg (pos_wtn E n)\<close> by simp
    qed
    ultimately show ?thesis by auto
  qed
next
  show "E - union_wit E \<subseteq> pos_sub E"
  proof
    fix a
    assume "a \<in> E - union_wit E"
    show "a \<in> pos_sub E" unfolding pos_sub_def
    proof
      fix n
      show "a \<in> pos_wtn E n"
      proof (cases "n = 0")
        case True
        thus ?thesis using pos_wtn_base \<open>a\<in> E - union_wit E\<close> by simp
      next
        case False
        hence "\<exists>m. n = Suc m" by (simp add: not0_implies_Suc) 
        from this obtain m where "n = Suc m" by auto
        have "(\<Union> i \<le> m. rep_neg (pos_wtn E i)) \<subseteq> 
          (\<Union> n. (rep_neg (pos_wtn E n)))" by auto
        hence "a \<in> E - (\<Union> i \<le> m. rep_neg (pos_wtn E i))" 
          using \<open>a \<in> E - union_wit E\<close> unfolding union_wit_def neg_wtn_def 
          by auto
        thus "a\<in> pos_wtn E n" using pos_wtn_Suc \<open>n = Suc m\<close> 
          unfolding neg_wtn_def by simp
      qed
    qed
  qed
qed

definition num_wtn where
  "num_wtn E n = inf_neg (pos_wtn E n)"

lemma num_wtn_geq:
  shows "\<mu> (neg_wtn E n) \<le> ereal (-1/(num_wtn E n))" 
proof (cases "(pos_wtn E n) \<notin> sets M \<or> pos_meas_set (pos_wtn E n)")
  case True
  hence "neg_wtn E n = {}" unfolding neg_wtn_def rep_neg_def by simp
  moreover have "num_wtn E n = 0" using True unfolding num_wtn_def inf_neg_def 
    by simp
  ultimately show ?thesis using sgn_meas signed_measure_empty by force 
next
  case False
  then show ?thesis using g_rep_neg(3)[of "pos_wtn E n"] unfolding neg_wtn_def 
      num_wtn_def by simp
qed

lemma neg_wtn_infty:
  assumes "E \<in> sets M"
    and "\<bar>\<mu> E\<bar> < \<infinity>"
  shows "\<bar>\<mu> (neg_wtn E i)\<bar> < \<infinity>"
proof (rule signed_measure_finite_subset)
  show "E \<in> sets M" "\<bar>\<mu> E\<bar> < \<infinity>" using assms by auto
  show "neg_wtn E i \<in> sets M" 
  proof (cases "pos_wtn E i \<notin> sets M \<or> pos_meas_set (pos_wtn E i)")
    case True
    then show ?thesis unfolding neg_wtn_def rep_neg_def by simp
  next
    case False
    then show ?thesis unfolding neg_wtn_def 
      using g_rep_neg(1)[of "pos_wtn E i"] by simp
  qed
  show "neg_wtn E i \<subseteq> E" unfolding neg_wtn_def using pos_wtn_subset[of E] 
      rep_neg_subset[of "pos_wtn E i"] by auto
qed

lemma union_wit_infty:
  assumes "E \<in> sets M"
    and "\<bar>\<mu> E\<bar> < \<infinity>"
  shows "\<bar>\<mu> (union_wit E)\<bar> < \<infinity>" using union_wit_subset union_wit_sets 
    signed_measure_finite_subset assms unfolding union_wit_def by simp

lemma neg_wtn_summable:
  assumes "E \<in> sets M"
    and "\<bar>\<mu> E\<bar> < \<infinity>"
  shows "summable (\<lambda>i. - real_of_ereal (\<mu> (neg_wtn E i)))"
proof -
  have "signed_measure M \<mu>" using sgn_meas .
  moreover have "range (neg_wtn E) \<subseteq> sets M" unfolding neg_wtn_def 
    using rep_neg_sets by auto
  moreover have "disjoint_family (neg_wtn E)" using neg_wtn_djn by simp
  moreover have "\<Union> (range (neg_wtn E)) \<in> sets M" using union_wit_sets 
    unfolding union_wit_def by simp
  moreover have "\<bar>\<mu> (\<Union> (range (neg_wtn E)))\<bar> < \<infinity>" 
    using union_wit_subset signed_measure_finite_subset union_wit_sets assms
    unfolding union_wit_def by simp
  ultimately have "summable (\<lambda>i. real_of_ereal \<bar>\<mu> (neg_wtn E i)\<bar>)" 
    using signed_measure_abs_convergent[of M ] by simp
  moreover have "\<And>i. \<bar>\<mu> (neg_wtn E i)\<bar> = -(\<mu> (neg_wtn E i))"
  proof -
    fix i
    have "\<mu> (neg_wtn E i) \<le> 0" using rep_neg_leq[of "pos_wtn E i"] 
      unfolding neg_wtn_def .
    thus "\<bar>\<mu> (neg_wtn E i)\<bar> = -\<mu> (neg_wtn E i)" using less_eq_ereal_def by auto 
  qed
  ultimately show ?thesis by simp
qed

lemma inv_num_wtn_summable:
  assumes "E \<in> sets M"
    and "\<bar>\<mu> E\<bar> < \<infinity>"
  shows "summable (\<lambda>n. 1/(num_wtn E n))"
proof (rule summable_bounded)
  show "\<And>i. 0 \<le> 1 / real (num_wtn E i)" by simp
  show "\<And>i. 1 / real (num_wtn E i) \<le> (\<lambda>n. -real_of_ereal (\<mu> (neg_wtn E n))) i"
  proof -
    fix i
    have "\<bar>\<mu> (neg_wtn E i)\<bar> < \<infinity>" using assms neg_wtn_infty by simp
    have "ereal (1/(num_wtn E i)) \<le> -\<mu> (neg_wtn E i)" using num_wtn_geq[of E i] 
        ereal_minus_le_minus by fastforce 
    also have "... = ereal(- real_of_ereal (\<mu> (neg_wtn E i)))" 
      using \<open>\<bar>\<mu> (neg_wtn E i)\<bar> < \<infinity>\<close> ereal_real' by auto
    finally have "ereal (1/(num_wtn E i)) \<le> 
      ereal(- real_of_ereal (\<mu> (neg_wtn E i)))" .
    thus "1 / real (num_wtn E i) \<le> -real_of_ereal (\<mu> (neg_wtn E i))" by simp
  qed
  show "summable (\<lambda>i. - real_of_ereal (\<mu> (neg_wtn E i)))" 
    using assms neg_wtn_summable by simp
qed

lemma inv_num_wtn_shift_summable:
  assumes "E \<in> sets M"
    and "\<bar>\<mu> E\<bar> < \<infinity>"
  shows "summable (\<lambda>n. 1/(num_wtn E n - 1))"
proof (rule sum_shift_denum)
  show "summable (\<lambda>n. 1 / real (num_wtn E n))" using assms inv_num_wtn_summable
    by simp
qed

lemma neg_wtn_meas_sums:
  assumes "E \<in> sets M"
    and "\<bar>\<mu> E\<bar> < \<infinity>"
  shows "(\<lambda>i. - (\<mu> (neg_wtn E i))) sums 
  suminf (\<lambda>i. - real_of_ereal (\<mu> (neg_wtn E i)))"
proof -
  have "(\<lambda>i. ereal (- real_of_ereal (\<mu> (neg_wtn E i)))) sums 
    suminf (\<lambda>i. - real_of_ereal (\<mu> (neg_wtn E i)))"
  proof (rule sums_ereal[THEN iffD2])
    have "summable (\<lambda>i. - real_of_ereal (\<mu> (neg_wtn E i)))" 
      using neg_wtn_summable assms by simp
    thus "(\<lambda>x. - real_of_ereal (\<mu> (neg_wtn E x))) 
      sums (\<Sum>i. - real_of_ereal (\<mu> (neg_wtn E i)))" 
      by auto
  qed
  moreover have "\<And>i. \<mu> (neg_wtn E i) = ereal (real_of_ereal (\<mu> (neg_wtn E i)))"
  proof -
    fix i
    show "\<mu> (neg_wtn E i) = ereal (real_of_ereal (\<mu> (neg_wtn E i)))"
      using assms(1) assms(2) ereal_real' neg_wtn_infty by auto
  qed
  ultimately show ?thesis 
    by (metis (no_types, lifting) sums_cong uminus_ereal.simps(1)) 
qed

lemma neg_wtn_meas_suminf_le:
  assumes "E \<in> sets M"
    and "\<bar>\<mu> E\<bar> < \<infinity>"
  shows "suminf (\<lambda>i. \<mu> (neg_wtn E i)) \<le> - suminf (\<lambda>n. 1/(num_wtn E n))"
proof -
  have "suminf (\<lambda>n. 1/(num_wtn E n)) \<le> 
    suminf (\<lambda>i. -real_of_ereal (\<mu> (neg_wtn E i)))"
  proof (rule suminf_le)
    show "summable (\<lambda>n.  1 / real (num_wtn E n))" using assms 
        inv_num_wtn_summable[of E] 
        summable_minus[of "\<lambda>n. 1 / real (num_wtn E n)"]  by simp 
    show "summable (\<lambda>i. -real_of_ereal (\<mu> (neg_wtn E i)))" 
      using neg_wtn_summable assms
        summable_minus[of "\<lambda>i. real_of_ereal (\<mu> (neg_wtn E i))"] 
      by (simp add: summable_minus_iff) 
    show "\<And>n. 1 / real (num_wtn E n) \<le> -real_of_ereal (\<mu> (neg_wtn E n))"
    proof -
      fix n
      have "\<mu> (neg_wtn E n) \<le> ereal (- 1 / real (num_wtn E n))" 
        using num_wtn_geq by simp
      hence "ereal (1/ real (num_wtn E n)) \<le> - \<mu> (neg_wtn E n)"
        by (metis add.inverse_inverse eq_iff ereal_uminus_le_reorder linear 
            minus_divide_left uminus_ereal.simps(1))
      have "real_of_ereal (ereal (1 / real (num_wtn E n))) \<le> 
        real_of_ereal (- \<mu> (neg_wtn E n))"
      proof (rule real_of_ereal_positive_mono)
        show "0 \<le> ereal (1 / real (num_wtn E n))" by simp
        show "ereal (1 / real (num_wtn E n)) \<le> - \<mu> (neg_wtn E n)" 
          using \<open>ereal (1 / real (num_wtn E n)) \<le> - \<mu> (neg_wtn E n)\<close> .
        show "- \<mu> (neg_wtn E n) \<noteq> \<infinity>" using neg_wtn_infty[of E n] assms by auto
      qed
      thus "(1 / real (num_wtn E n)) \<le> -real_of_ereal ( \<mu> (neg_wtn E n))" 
        by simp
    qed
  qed
  also have "... = - suminf (\<lambda>i. real_of_ereal (\<mu> (neg_wtn E i)))" 
  proof (rule suminf_minus)
    show "summable (\<lambda>n. real_of_ereal (\<mu> (neg_wtn E n)))" 
      using neg_wtn_summable assms
        summable_minus[of "\<lambda>i. real_of_ereal (\<mu> (neg_wtn E i))"] 
      by (simp add: summable_minus_iff) 
  qed
  finally have "suminf (\<lambda>n. 1/(num_wtn E n)) \<le> 
    - suminf (\<lambda>i. real_of_ereal (\<mu> (neg_wtn E i)))" .
  hence a:  "suminf (\<lambda>i. real_of_ereal (\<mu> (neg_wtn E i))) \<le> 
    - suminf (\<lambda>n. 1/(num_wtn E n))" by simp
  show "suminf (\<lambda>i. (\<mu> (neg_wtn E i))) \<le> ereal (-suminf (\<lambda>n. 1/(num_wtn E n)))" 
  proof -
    have sumeq: "suminf (\<lambda>i. ereal (real_of_ereal (\<mu> (neg_wtn E i)))) = 
      suminf (\<lambda>i. (real_of_ereal (\<mu> (neg_wtn E i))))"
    proof (rule sums_suminf_ereal)
      have "summable (\<lambda>i. -real_of_ereal (\<mu> (neg_wtn E i)))" 
        using neg_wtn_summable assms
          summable_minus[of "\<lambda>i. real_of_ereal (\<mu> (neg_wtn E i))"] 
        by (simp add: summable_minus_iff)
      thus "(\<lambda>i. real_of_ereal (\<mu> (neg_wtn E i))) sums 
        (\<Sum>i. real_of_ereal (\<mu> (neg_wtn E i)))" 
        using neg_wtn_summable[of E] assms summable_minus_iff by blast
    qed
    hence "suminf (\<lambda>i. \<mu> (neg_wtn E i)) = 
      suminf (\<lambda>i. (real_of_ereal (\<mu> (neg_wtn E i))))" 
    proof -
      have "\<And>i. ereal (real_of_ereal (\<mu> (neg_wtn E i))) = \<mu> (neg_wtn E i)"
      proof -
        fix i
        show "ereal (real_of_ereal (\<mu> (neg_wtn E i))) = \<mu> (neg_wtn E i)"
          using neg_wtn_infty[of E] assms by (simp add: ereal_real')
      qed
      thus ?thesis using sumeq by auto 
    qed
    thus ?thesis using a by simp
  qed
qed

lemma union_wit_meas_le:
  assumes "E \<in> sets M"
    and "\<bar>\<mu> E\<bar> < \<infinity>"
  shows "\<mu> (union_wit E) \<le> - suminf (\<lambda>n. 1 / real (num_wtn E n))" 
proof -
  have "\<mu> (union_wit E) = \<mu> (\<Union> (range (neg_wtn E)))" unfolding union_wit_def 
    by simp
  also have "... = (\<Sum>i. \<mu> (neg_wtn E i))" 
  proof (rule signed_measure_inf_sum[symmetric])
    show "signed_measure M \<mu>" using sgn_meas .
    show "range (neg_wtn E) \<subseteq> sets M" 
      by (simp add: image_subset_iff neg_wtn_def rep_neg_sets)
    show "disjoint_family (neg_wtn E)" using neg_wtn_djn by simp
    show "\<Union> (range (neg_wtn E)) \<in> sets M" using union_wit_sets 
      unfolding union_wit_def by simp
  qed
  also have "... \<le> - suminf (\<lambda>n. 1 / real (num_wtn E n))" 
    using assms neg_wtn_meas_suminf_le by simp
  finally show ?thesis .
qed

lemma pos_sub_pos_meas:
  assumes "E \<in> sets M"
    and "\<bar>\<mu> E\<bar> < \<infinity>"
    and "0 < \<mu> E"
    and "\<not> pos_meas_set E"
  shows "0 < \<mu> (pos_sub E)"
proof -
  have "0 < \<mu> E" using assms by simp
  also have "... = \<mu> (pos_sub E) + \<mu> (union_wit E)"
  proof -
    have "E = pos_sub E \<union> (union_wit E)" 
      using pos_sub_diff[of E] union_wit_subset by force 
    moreover have "pos_sub E \<inter> union_wit E = {}" 
      using pos_sub_diff by auto
    ultimately show ?thesis 
      using signed_measure_add[of M \<mu> "pos_sub E" "union_wit E"] 
        pos_sub_sets union_wit_sets assms sgn_meas by simp
  qed
  also have "... \<le> \<mu> (pos_sub E) + (- suminf (\<lambda>n. 1 / real (num_wtn E n)))"
  proof -
    have "\<mu> (union_wit E) \<le> - suminf (\<lambda>n. 1 / real (num_wtn E n))" 
      using union_wit_meas_le[of E] assms by simp
    thus ?thesis using union_wit_infty assms using add_left_mono by blast
  qed
  also have "... = \<mu> (pos_sub E) - suminf (\<lambda>n. 1 / real (num_wtn E n))"
    by (simp add: minus_ereal_def) 
  finally have "0 < \<mu> (pos_sub E) - suminf (\<lambda>n. 1 / real (num_wtn E n))" .
  moreover have "0 < suminf (\<lambda>n. 1 / real (num_wtn E n))" 
  proof (rule suminf_pos2)
    show "0 < 1 / real (num_wtn E 0)" 
      using inf_neg_ge_1[of E] assms pos_wtn_base unfolding num_wtn_def by simp
    show "\<And>n. 0 \<le> 1 / real (num_wtn E n)" by simp
    show "summable (\<lambda>n. 1 / real (num_wtn E n))" 
      using assms inv_num_wtn_summable by simp
  qed
  ultimately show ?thesis  using pos_sub_infty assms by fastforce
qed

lemma num_wtn_conv:
  assumes "E \<in> sets M"
    and "\<bar>\<mu> E\<bar> < \<infinity>"
  shows "(\<lambda>n. 1/(num_wtn E n)) \<longlonglongrightarrow> 0"
proof (rule summable_LIMSEQ_zero)
  show "summable (\<lambda>n. 1 / real (num_wtn E n))" 
    using assms inv_num_wtn_summable by simp
qed

lemma num_wtn_shift_conv:
  assumes "E \<in> sets M"
    and "\<bar>\<mu> E\<bar> < \<infinity>"
  shows "(\<lambda>n. 1/(num_wtn E n - 1)) \<longlonglongrightarrow> 0"
proof (rule summable_LIMSEQ_zero)
  show "summable (\<lambda>n. 1 / real (num_wtn E n - 1))" 
    using assms inv_num_wtn_shift_summable by simp
qed

lemma inf_neg_E_set:
  assumes "0 < inf_neg E"
  shows "E \<in> sets M" using assms unfolding inf_neg_def by presburger

lemma inf_neg_pos_meas:
  assumes "0 < inf_neg E"
  shows "\<not> pos_meas_set E" using assms unfolding inf_neg_def by presburger

lemma inf_neg_mem:
  assumes "0 < inf_neg E"
  shows "inf_neg E \<in> {n::nat|n. (1::nat) \<le> n \<and> 
    (\<exists>B \<in> sets M. B  \<subseteq> E \<and> \<mu> B < ereal (-1/n))}"
proof -
  have "E \<in> sets M" using assms unfolding inf_neg_def by presburger
  moreover have "\<not> pos_meas_set E" using assms unfolding inf_neg_def 
    by presburger
  ultimately have "{n::nat|n. (1::nat) \<le> n \<and> 
    (\<exists>B \<in> sets M. B  \<subseteq> E \<and> \<mu> B < ereal (-1/n))} \<noteq> {}" 
    using inf_neg_ne[of E] by simp
  thus ?thesis unfolding inf_neg_def 
    by (meson Inf_nat_def1 \<open>E \<in> sets M\<close> \<open>\<not> pos_meas_set E\<close>)
qed

lemma prec_inf_neg_pos:
  assumes "0 < inf_neg E - 1"
    and "B \<in> sets M"
    and "B\<subseteq> E"
  shows "-1/(inf_neg E - 1) \<le> \<mu> B"
proof (rule ccontr)
  define S where "S = {p::nat|p. (1::nat) \<le> p \<and> 
    (\<exists>B \<in> sets M. B  \<subseteq> E \<and> \<mu> B < ereal (-1/p))}"
  assume "\<not> ereal (- 1 / real (inf_neg E - 1)) \<le> \<mu> B"
  hence "\<mu> B < -1/(inf_neg E - 1)" by auto
  hence "inf_neg E - 1\<in> S" unfolding S_def using assms by auto
  have "Suc 0 < inf_neg E" using assms by simp
  hence "inf_neg E \<in> S" unfolding  S_def using inf_neg_mem[of E] by simp
  hence "S \<noteq> {}" by auto
  have "inf_neg E = Inf S" unfolding S_def inf_neg_def 
    using assms inf_neg_E_set inf_neg_pos_meas by auto
  have  "inf_neg E - 1 < inf_neg E" using assms by simp
  hence "inf_neg E -1 \<notin> S" 
    using cInf_less_iff[of S] \<open>S \<noteq> {}\<close> \<open>inf_neg E = Inf S\<close> by auto
  thus False using \<open>inf_neg E - 1 \<in> S\<close> by simp
qed

lemma pos_wtn_meas_ge:
  assumes "E \<in> sets M"
    and "\<bar>\<mu> E\<bar> < \<infinity>"
    and "C\<in> sets M"
    and "\<And>n. C\<subseteq> pos_wtn E n"
    and "\<And>n. 0 < num_wtn E n"
  shows "\<exists>N. \<forall>n\<ge> N. - 1/ (num_wtn E n - 1) \<le> \<mu> C" 
proof -
  have "\<exists>N. \<forall>n\<ge> N. 1/(num_wtn E n) < 1/2" using num_wtn_conv[of E] 
      conv_0_half[of "\<lambda>n. 1 / real (num_wtn E n)"] assms by simp
  from this obtain N where "\<forall>n\<ge> N. 1/(num_wtn E n) < 1/2" by auto
  {
    fix n
    assume "N \<le> n"
    hence "1/(num_wtn E n) < 1/2" using \<open>\<forall>n\<ge> N. 1/(num_wtn E n) < 1/2\<close> by simp
    have "1/(1/2) < 1/(1/(num_wtn E n))" 
    proof (rule frac_less2, auto)
      show "2 / real (num_wtn E n) < 1" using \<open>1/(num_wtn E n) < 1/2\<close> 
        by linarith
      show "0 < num_wtn E n" unfolding num_wtn_def using inf_neg_ge_1 assms
        by (simp add: num_wtn_def)
    qed
    hence "2 < (num_wtn E n)" by simp
    hence "Suc 0 < num_wtn E n - 1" unfolding num_wtn_def by simp
    hence "- 1/ (num_wtn E n - 1) \<le> \<mu> C" using assms prec_inf_neg_pos 
      unfolding num_wtn_def by simp
  }
  thus ?thesis by auto
qed

lemma pos_sub_pos_meas_subset:
  assumes "E \<in> sets M"
    and "\<bar>\<mu> E\<bar> < \<infinity>"
    and "C\<in> sets M"
    and "C\<subseteq> (pos_sub E)"
    and "\<And>n. 0 < num_wtn E n"
  shows "0 \<le> \<mu> C"
proof -
  have "\<And>n. C \<subseteq> pos_wtn E n" using assms unfolding pos_sub_def by auto
  hence "\<exists>N. \<forall>n\<ge> N. - 1/ (num_wtn E n - 1) \<le> \<mu> C" using  assms  
      pos_wtn_meas_ge[of E C] by simp
  from this obtain N where Nprop: "\<forall>n\<ge> N. - 1/ (num_wtn E n - 1) \<le> \<mu> C" by auto
  show "0 \<le> \<mu> C"
  proof (rule lim_mono)
    show "\<And>n. N \<le> n \<Longrightarrow> - 1/ (num_wtn E n - 1) \<le> (\<lambda>n. \<mu> C) n" 
      using Nprop by simp
    have "(\<lambda>n.  ( 1 / real (num_wtn E n - 1))) \<longlonglongrightarrow> 0" 
      using assms num_wtn_shift_conv[of E] by simp
    hence "(\<lambda>n.  (- 1 / real (num_wtn E n - 1))) \<longlonglongrightarrow> 0" 
      using tendsto_minus[of "\<lambda>n. 1 / real (num_wtn E n - 1)" 0] by simp
    thus "(\<lambda>n. ereal (- 1 / real (num_wtn E n - 1))) \<longlonglongrightarrow> 0" 
      by (simp add: zero_ereal_def) 
    show "(\<lambda>n. \<mu> C) \<longlonglongrightarrow> \<mu> C" by simp
  qed
qed

lemma pos_sub_pos_meas':
  assumes "E \<in> sets M"
    and "\<bar>\<mu> E\<bar> < \<infinity>"
    and "0 < \<mu> E"
    and "\<forall>n. 0 < num_wtn E n"
  shows "0 < \<mu> (pos_sub E)"
proof -
  have "0 < \<mu> E" using assms by simp
  also have "... = \<mu> (pos_sub E) + \<mu> (union_wit E)"
  proof -
    have "E = pos_sub E \<union> (union_wit E)" 
      using pos_sub_diff[of E] union_wit_subset by force 
    moreover have "pos_sub E \<inter> union_wit E = {}" 
      using pos_sub_diff by auto
    ultimately show ?thesis 
      using signed_measure_add[of M \<mu> "pos_sub E" "union_wit E"] 
        pos_sub_sets union_wit_sets assms sgn_meas by simp
  qed
  also have "... \<le> \<mu> (pos_sub E) + (- suminf (\<lambda>n. 1 / real (num_wtn E n)))"
  proof -
    have "\<mu> (union_wit E) \<le> - suminf (\<lambda>n. 1 / real (num_wtn E n))" 
      using union_wit_meas_le[of E] assms by simp
    thus ?thesis using union_wit_infty assms using add_left_mono by blast
  qed
  also have "... = \<mu> (pos_sub E) - suminf (\<lambda>n. 1 / real (num_wtn E n))"
    by (simp add: minus_ereal_def) 
  finally have "0 < \<mu> (pos_sub E) - suminf (\<lambda>n. 1 / real (num_wtn E n))" .
  moreover have "0 < suminf (\<lambda>n. 1 / real (num_wtn E n))" 
  proof (rule suminf_pos2)
    show "0 < 1 / real (num_wtn E 0)" using assms by simp
    show "\<And>n. 0 \<le> 1 / real (num_wtn E n)" by simp
    show "summable (\<lambda>n. 1 / real (num_wtn E n))" 
      using assms inv_num_wtn_summable by simp
  qed
  ultimately show ?thesis  using pos_sub_infty assms by fastforce
qed

text \<open>We obtain the main result of this part on the existence of a positive subset.\<close>

lemma exists_pos_meas_subset:
  assumes "E \<in> sets M"
    and "\<bar>\<mu> E\<bar> < \<infinity>"
    and "0 < \<mu> E"
  shows "\<exists>A. A \<subseteq> E \<and> pos_meas_set A \<and> 0 < \<mu> A"
proof (cases "\<forall>n. 0 < num_wtn E n")
  case True
  have "pos_meas_set (pos_sub E)" 
  proof (rule pos_meas_setI)
    show "pos_sub E \<in> sets M" by (simp add: assms(1) pos_sub_sets) 
    fix A
    assume "A \<in> sets M" and "A\<subseteq> pos_sub E"
    thus "0 \<le> \<mu> A" using assms True pos_sub_pos_meas_subset[of E] by simp
  qed
  moreover have "0 < \<mu> (pos_sub E)" 
    using pos_sub_pos_meas'[of E] True assms by simp
  ultimately show ?thesis using pos_meas_set_def by (metis pos_sub_subset)
next
  case False
  hence "\<exists>n. num_wtn E n = 0" by simp
  from this obtain n where "num_wtn E n = 0" by auto
  hence "pos_wtn E n \<notin> sets M \<or> pos_meas_set (pos_wtn E n)" 
    using inf_neg_ge_1 unfolding num_wtn_def by fastforce
  hence "pos_meas_set (pos_wtn E n)" using assms 
    by (simp add: \<open>E \<in> sets M\<close> pos_wtn_sets) 
  moreover have "0 < \<mu> (pos_wtn E n)" using pos_wtn_meas_gt assms by simp
  ultimately show ?thesis using pos_meas_set_def by (meson pos_wtn_subset)   
qed

section \<open>The Hahn decomposition theorem\<close>

definition seq_meas where
  "seq_meas = (SOME f. incseq f \<and> range f \<subseteq> pos_img  \<and> \<Squnion> pos_img = \<Squnion> range f)"

lemma seq_meas_props:
  shows "incseq seq_meas \<and> range seq_meas \<subseteq> pos_img \<and> 
    \<Squnion> pos_img = \<Squnion> range seq_meas"
proof -
  have ex: "\<exists>f. incseq f \<and> range f \<subseteq> pos_img  \<and> \<Squnion> pos_img = \<Squnion> range f"
  proof (rule Extended_Real.Sup_countable_SUP)
    show "pos_img \<noteq> {}"
    proof -
      have "{} \<in> pos_sets" using empty_pos_meas_set unfolding pos_sets_def 
        by simp
      hence "\<mu> {} \<in> pos_img" unfolding pos_img_def by auto
      thus ?thesis by auto
    qed 
  qed
  let ?V = "SOME f. incseq f \<and> range f \<subseteq> pos_img  \<and> \<Squnion> pos_img = \<Squnion> range f"
  have vprop: "incseq ?V \<and> range ?V \<subseteq> pos_img \<and> \<Squnion> pos_img = \<Squnion> range ?V" 
    using someI_ex[of "\<lambda>f. incseq f \<and> range f \<subseteq> pos_img  \<and> 
      \<Squnion> pos_img = \<Squnion> range f"] ex by blast
  show ?thesis using seq_meas_def vprop by presburger
qed

definition seq_meas_rep where
  "seq_meas_rep n = (SOME A. A\<in> pos_sets \<and> seq_meas n = \<mu> A)"

lemma seq_meas_rep_ex:
  shows "seq_meas_rep n \<in> pos_sets \<and> \<mu> (seq_meas_rep n) = seq_meas n"
proof -
  have ex: "\<exists>A. A \<in> pos_sets \<and> seq_meas n = \<mu> A" using seq_meas_props
    by (smt (z3) UNIV_I image_subset_iff mem_Collect_eq pos_img_def) 
  let ?V = "SOME A. A\<in> pos_sets \<and> seq_meas n = \<mu> A"
  have vprop: "?V\<in> pos_sets \<and> seq_meas n = \<mu> ?V" using 
      someI_ex[of "\<lambda>A. A\<in> pos_sets \<and> seq_meas n = \<mu> A"] using ex by blast
  show ?thesis using seq_meas_rep_def vprop by fastforce 
qed

lemma seq_meas_rep_pos:
  assumes "\<forall>E \<in> sets M. \<mu> E < \<infinity>" 
  shows "pos_meas_set (\<Union> i. seq_meas_rep i)" 
proof (rule pos_meas_set_Union)
  show " \<And>i. pos_meas_set (seq_meas_rep i)" 
    using seq_meas_rep_ex signed_measure_space.pos_sets_def 
      signed_measure_space_axioms by auto
  then show "\<And>i. seq_meas_rep i \<in> sets M"
    by (simp add: pos_meas_setD1)
  show "\<bar>\<mu> (\<Union> (range seq_meas_rep))\<bar> < \<infinity>"
  proof -
    have "(\<Union> (range seq_meas_rep)) \<in> sets M"
    proof (rule sigma_algebra.countable_Union)
      show "sigma_algebra (space M) (sets M)" 
        by (simp add: sets.sigma_algebra_axioms) 
      show "countable (range seq_meas_rep)" by simp
      show "range seq_meas_rep \<subseteq> sets M" 
        by (simp add: \<open>\<And>i. seq_meas_rep i \<in> sets M\<close> image_subset_iff)
    qed
    hence "\<mu> (\<Union> (range seq_meas_rep)) \<ge> 0 " 
      using \<open>\<And>i. pos_meas_set (seq_meas_rep i)\<close> \<open>\<And>i. seq_meas_rep i \<in> sets M\<close> 
        signed_measure_space.pos_meas_set_pos_lim signed_measure_space_axioms 
      by blast
    thus ?thesis using assms \<open>\<Union> (range seq_meas_rep) \<in> sets M\<close> abs_ereal_ge0  
      by simp
  qed   
qed

lemma sup_seq_meas_rep:
  assumes "\<forall>E \<in> sets M. \<mu> E < \<infinity>" 
    and "S = (\<Squnion> pos_img)"
    and "A = (\<Union> i. seq_meas_rep i)"
  shows "\<mu> A = S"
proof -
  have pms: "pos_meas_set (\<Union> i. seq_meas_rep i)" 
    using assms seq_meas_rep_pos by simp
  hence "\<mu> A \<le> S" 
    by (metis (mono_tags, lifting) Sup_upper \<open>S = \<Squnion> pos_img\<close> mem_Collect_eq 
        pos_img_def pos_meas_setD1 pos_sets_def assms(2) assms(3))  
  have "\<forall>n. (\<mu> A = \<mu> (A - seq_meas_rep n) + \<mu> (seq_meas_rep n))"
  proof
    fix n
    have "A = (A - seq_meas_rep n) \<union> seq_meas_rep n " 
      using \<open>A = \<Union> (range seq_meas_rep)\<close> by blast
    hence "\<mu> A = \<mu> ((A - seq_meas_rep n) \<union> seq_meas_rep n)"  by simp
    also have "... = \<mu> (A - seq_meas_rep n) + \<mu> (seq_meas_rep n)" 
    proof (rule signed_measure_add)
      show "signed_measure M \<mu>" using sgn_meas by simp
      show "seq_meas_rep n \<in> sets M"
        using pos_sets_def seq_meas_rep_ex by auto
      then show "A - seq_meas_rep n \<in> sets M"
        by (simp add: assms pms pos_meas_setD1 sets.Diff)
      show "(A - seq_meas_rep n) \<inter> seq_meas_rep n = {}" by auto
    qed
    finally show "\<mu> A = \<mu> (A - seq_meas_rep n) + \<mu> (seq_meas_rep n)".
  qed
  have "\<forall>n. \<mu> A \<ge> \<mu> (seq_meas_rep n)" 
  proof 
    fix n
    have "\<mu> A \<ge> 0" using pms assms unfolding pos_meas_set_def by auto
    have "(A - seq_meas_rep n) \<subseteq> A" by simp
    hence "pos_meas_set (A - seq_meas_rep n)" 
    proof -
      have "(A - seq_meas_rep n) \<in> sets M"
        using pms assms pos_meas_setD1 pos_sets_def seq_meas_rep_ex by auto
      thus ?thesis using pms assms unfolding pos_meas_set_def by auto
    qed
    hence "\<mu> (A - seq_meas_rep n) \<ge> 0" unfolding pos_meas_set_def by auto
    thus "\<mu> (seq_meas_rep n) \<le> \<mu> A" 
      using \<open>\<forall>n. (\<mu> A = \<mu> (A - seq_meas_rep n) + \<mu> (seq_meas_rep n))\<close>
      by (metis ereal_le_add_self2) 
  qed
  hence "\<mu> A \<ge> (\<Squnion> range seq_meas)" by (simp add: Sup_le_iff seq_meas_rep_ex)
  moreover have "S = (\<Squnion> range seq_meas)" 
    using seq_meas_props \<open>S = (\<Squnion> pos_img)\<close> by simp
  ultimately have "\<mu> A \<ge> S" by simp
  thus "\<mu> A = S" using \<open>\<mu> A \<le> S\<close> by simp
qed

lemma seq_meas_rep_compl:
  assumes "\<forall>E \<in> sets M. \<mu> E < \<infinity>"
    and "A = (\<Union> i. seq_meas_rep i)"
  shows "neg_meas_set ((space M) - A)" unfolding neg_meas_set_def
proof (rule ccontr)
  assume asm: "\<not> (space M - A \<in> sets M \<and> 
    (\<forall>Aa\<in>sets M. Aa \<subseteq> space M - A \<longrightarrow> \<mu> Aa \<le> 0))" 
  define S where "S = (\<Squnion> pos_img)"
  have "pos_meas_set A"  using assms seq_meas_rep_pos by simp
  have "\<mu> A = S" using sup_seq_meas_rep assms  S_def by simp
  hence "S < \<infinity>" using assms \<open>pos_meas_set A\<close> pos_meas_setD1 by blast 
  have "(space M - A \<in> sets M)"
    by (simp add: \<open>pos_meas_set A\<close> pos_meas_setD1 sets.compl_sets)
  hence " \<not>(\<forall>Aa\<in>sets M. Aa \<subseteq> space M - A \<longrightarrow> \<mu> Aa \<le> 0)" using asm by blast
  hence "\<exists> E \<in> sets M. E \<subseteq> ((space M) - A) \<and> \<mu> E > 0" 
    by (metis less_eq_ereal_def linear)
  from this obtain E where "E \<in> sets M" and "E \<subseteq> ((space M) - A)" and 
    "\<mu> E > 0" by auto
  have "\<exists> A0 \<subseteq> E. pos_meas_set A0 \<and> \<mu> A0 > 0" 
  proof (rule exists_pos_meas_subset) 
    show "E \<in> sets M" using \<open>E \<in> sets M\<close> by simp
    show "0 < \<mu> E" using \<open>\<mu> E > 0\<close> by simp
    show "\<bar>\<mu> E\<bar> < \<infinity>" 
    proof -
      have "\<mu> E < \<infinity>" using assms \<open>E \<in> sets M\<close> by simp
      moreover have "- \<infinity> < \<mu> E" using \<open>0 < \<mu> E\<close> by simp 
      ultimately show ?thesis
        by (meson ereal_infty_less(1) not_inftyI)
    qed
  qed
  from this obtain A0 where "A0 \<subseteq> E" and "pos_meas_set A0" and " \<mu> A0 > 0" 
    by auto
  have "pos_meas_set (A \<union> A0)" 
    using pos_meas_set_union \<open>pos_meas_set A0\<close> \<open>pos_meas_set A\<close> by simp
  have "\<mu> (A \<union> A0) = \<mu> A + \<mu> A0" 
  proof (rule signed_measure_add)
    show "signed_measure M \<mu>" using sgn_meas by simp
    show "A \<in> sets M" using \<open>pos_meas_set A\<close> 
      unfolding pos_meas_set_def by simp
    show "A0 \<in> sets M" using \<open>pos_meas_set A0\<close> 
      unfolding pos_meas_set_def by simp
    show "(A \<inter> A0) = {}" using \<open>A0 \<subseteq> E\<close> \<open>E \<subseteq> ((space M) - A)\<close> by auto
  qed
  then have "\<mu> (A \<union> A0) > S" 
    using \<open>\<mu> A = S\<close> \<open>\<mu> A0 > 0\<close>
    by (metis \<open>S < \<infinity>\<close> \<open>pos_meas_set (A \<union> A0)\<close> abs_ereal_ge0 ereal_between(2) 
        not_inftyI not_less_iff_gr_or_eq pos_meas_self)
  have "(A \<union> A0) \<in> pos_sets"
  proof -
    have " (A \<union> A0) \<in> sets M" using sigma_algebra.countable_Union
      by (simp add: \<open>pos_meas_set (A \<union> A0)\<close> pos_meas_setD1) 
    moreover have "pos_meas_set (A \<union> A0)" using \<open>pos_meas_set (A \<union> A0)\<close> by simp
    ultimately show ?thesis unfolding pos_sets_def by simp
  qed
  then have "\<mu> (A \<union> A0) \<in> pos_img" unfolding pos_img_def by auto
  show False using \<open>\<mu> (A \<union> A0) > S\<close> \<open>\<mu> (A \<union> A0) \<in> pos_img\<close> \<open>S = (\<Squnion> pos_img)\<close>
    by (metis Sup_upper sup.absorb_iff2 sup.strict_order_iff)
qed

lemma hahn_decomp_finite:
  assumes "\<forall>E \<in> sets M. \<mu> E < \<infinity>"
  shows "\<exists> M1 M2. hahn_space_decomp M1 M2" unfolding hahn_space_decomp_def
proof -
  define S where "S = (\<Squnion> pos_img)"
  define A where "A = (\<Union> i. seq_meas_rep i)" 
  have "pos_meas_set A" unfolding A_def using assms seq_meas_rep_pos by simp
  have "neg_meas_set ((space M) - A)" 
    using seq_meas_rep_compl assms unfolding A_def by simp
  show "\<exists>M1 M2. pos_meas_set M1 \<and> neg_meas_set M2 \<and> space M = M1 \<union> M2 \<and> 
    M1 \<inter> M2 = {}"
  proof (intro exI conjI)
    show "pos_meas_set A" using \<open>pos_meas_set A\<close> .
    show "neg_meas_set (space M - A)" using \<open>neg_meas_set (space M - A)\<close> .
    show "space M = A \<union> (space M - A)"
      by (metis Diff_partition \<open>pos_meas_set A\<close> inf.absorb_iff2 pos_meas_setD1 
          sets.Int_space_eq1) 
    show "A \<inter> (space M - A) = {}" by auto
  qed
qed

theorem hahn_decomposition:
  shows "\<exists> M1 M2. hahn_space_decomp M1 M2"
proof (cases "\<forall>E \<in> sets M. \<mu> E < \<infinity>")
  case True
  thus ?thesis using hahn_decomp_finite by simp
next
  case False
  define m where "m = (\<lambda>A . - \<mu> A)"
  have "\<exists> M1 M2. signed_measure_space.hahn_space_decomp M m M1 M2"
  proof (rule signed_measure_space.hahn_decomp_finite)
    show "signed_measure_space M m" 
      using signed_measure_minus sgn_meas \<open>m = (\<lambda>A . - \<mu> A)\<close>  
      by (unfold_locales, simp)
    show "\<forall>E\<in>sets M. m E < \<infinity>"
    proof
      fix E
      assume "E \<in> sets M"
      show "m E < \<infinity>"
      proof
        show "m E \<noteq> \<infinity>"
        proof (rule ccontr)
          assume "\<not> m E \<noteq> \<infinity>"
          have "m E = \<infinity>"
            using \<open>\<not> m E \<noteq> \<infinity>\<close> by auto 
          have "signed_measure M m"
            using \<open>signed_measure_space M m\<close> signed_measure_space_def by auto
          moreover have "m E = - \<mu> E" using \<open>m = (\<lambda>A . - \<mu> A)\<close> by auto
          then have "\<infinity> \<notin> range m" using \<open>signed_measure M m\<close>
            by (metis (no_types, lifting) False ereal_less_PInfty 
                ereal_uminus_eq_reorder image_iff inf_range m_def rangeI)
          show False using \<open>m E = \<infinity>\<close> \<open>\<infinity> \<notin> range m\<close>
            by (metis rangeI)
        qed
      qed
    qed
  qed
  hence "\<exists> M1 M2. (neg_meas_set M1) \<and> (pos_meas_set M2) \<and> (space M = M1 \<union> M2) \<and>
    (M1 \<inter> M2 = {})" 
    using pos_meas_set_opp neg_meas_set_opp unfolding m_def 
    by (metis sgn_meas signed_measure_minus signed_measure_space_def 
        signed_measure_space.hahn_space_decomp_def)
  thus ?thesis using hahn_space_decomp_def by (metis inf_commute sup_commute)
qed

section \<open>The Jordan decomposition theorem\<close>

definition jordan_decomp where
  "jordan_decomp m1 m2 \<longleftrightarrow> ((measure_space (space M) (sets M) m1) \<and> 
    (measure_space (space M) (sets M) m2) \<and> 
    (\<forall>A\<in> sets M. 0 \<le> m1 A) \<and>
    (\<forall> A\<in> sets M. 0 \<le> m2 A) \<and>
    (\<forall>A \<in> sets M. \<mu> A = (m1 A) - (m2 A)) \<and>
    (\<forall> P N A. hahn_space_decomp P N \<longrightarrow> 
      (A \<in> sets M \<longrightarrow> A \<subseteq> P \<longrightarrow> (m2 A) = 0) \<and> 
      (A \<in> sets M \<longrightarrow> A \<subseteq> N \<longrightarrow> (m1 A) = 0)) \<and>
    ((\<forall>A \<in> sets M. m1 A < \<infinity>) \<or> (\<forall>A \<in> sets M. m2 A < \<infinity>)))"

lemma jordan_decomp_pos_meas:
  assumes "jordan_decomp m1 m2"
    and "hahn_space_decomp P N"
    and "A \<in> sets M"
  shows "m1 A = \<mu> (A \<inter> P)" 
proof -
  have "A\<inter>P \<in> sets M" using assms unfolding hahn_space_decomp_def
    by (simp add: pos_meas_setD1 sets.Int)
  have "A\<inter> N \<in> sets M" using assms unfolding hahn_space_decomp_def
    by (simp add: neg_meas_setD1 sets.Int)
  have "(A \<inter> P) \<inter> (A\<inter> N) = {}" using assms unfolding hahn_space_decomp_def 
    by auto
  have "A = (A \<inter> P) \<union> (A\<inter> N)" using assms unfolding hahn_space_decomp_def
    by (metis Int_Un_distrib sets.Int_space_eq2)
  hence "m1 A = m1 ((A \<inter> P) \<union> (A\<inter> N))" by simp
  also have "... = m1 (A \<inter> P) + m1 (A \<inter> N)" 
    using assms pos_e2ennreal_additive[of M m1] \<open>A\<inter>P \<in> sets M\<close> \<open>A\<inter>N \<in> sets M\<close> 
      \<open>A \<inter> P \<inter> (A \<inter> N) = {}\<close> 
    unfolding jordan_decomp_def additive_def by simp
  also have "... = m1 (A \<inter> P)" using assms unfolding jordan_decomp_def
    by (metis Int_lower2 \<open>A \<inter> N \<in> sets M\<close> add.right_neutral)
  also have "... = m1 (A \<inter> P) - m2 (A \<inter> P)" 
    using assms unfolding jordan_decomp_def
    by (metis Int_subset_iff \<open>A \<inter> P \<in> sets M\<close> ereal_minus(7) 
        local.pos_wtn_base pos_wtn_subset)
  also have "... = \<mu> (A \<inter> P)" using assms \<open>A \<inter> P \<in> sets M\<close> 
    unfolding jordan_decomp_def by simp
  finally show ?thesis .
qed

lemma jordan_decomp_neg_meas:
  assumes "jordan_decomp m1 m2"
    and "hahn_space_decomp P N"
    and "A \<in> sets M"
  shows "m2 A = -\<mu> (A \<inter> N)" 
proof -
  have "A\<inter>P \<in> sets M" using assms unfolding hahn_space_decomp_def
    by (simp add: pos_meas_setD1 sets.Int)
  have "A\<inter> N \<in> sets M" using assms unfolding hahn_space_decomp_def
    by (simp add: neg_meas_setD1 sets.Int)
  have "(A \<inter> P) \<inter> (A\<inter> N) = {}" 
    using assms unfolding hahn_space_decomp_def by auto
  have "A = (A \<inter> P) \<union> (A\<inter> N)" 
    using assms unfolding hahn_space_decomp_def
    by (metis Int_Un_distrib sets.Int_space_eq2)
  hence "m2 A = m2 ((A \<inter> P) \<union> (A\<inter> N))" by simp
  also have "... = m2 (A \<inter> P) + m2 (A \<inter> N)" 
    using pos_e2ennreal_additive[of M m2] assms
      \<open>A\<inter>P \<in> sets M\<close> \<open>A\<inter>N \<in> sets M\<close> \<open>A \<inter> P \<inter> (A \<inter> N) = {}\<close> 
    unfolding jordan_decomp_def additive_def by simp
  also have "... = m2 (A \<inter> N)" using assms unfolding jordan_decomp_def
    by (metis Int_lower2 \<open>A \<inter> P \<in> sets M\<close> add.commute add.right_neutral)
  also have "... = m2 (A \<inter> N) - m1 (A \<inter> N)" 
    using assms unfolding jordan_decomp_def
    by (metis Int_lower2 \<open>A \<inter> N \<in> sets M\<close> ereal_minus(7))
  also have "... = -\<mu> (A \<inter> N)" using assms \<open>A \<inter> P \<in> sets M\<close> 
    unfolding jordan_decomp_def
    by (metis Diff_cancel Diff_eq_empty_iff Int_Un_eq(2) \<open>A \<inter> N \<in> sets M\<close> 
        \<open>m2 (A \<inter> N) = m2 (A \<inter> N) - m1 (A \<inter> N)\<close> ereal_minus(8) 
        ereal_uminus_eq_reorder sup.bounded_iff)
  finally show ?thesis .
qed

lemma pos_inter_neg_0:
  assumes "hahn_space_decomp M1 M2"
    and "hahn_space_decomp P N"
    and "A \<in> sets M"
    and "A \<subseteq> N"
  shows "\<mu> (A \<inter> M1) = 0"
proof -
  have "\<mu> (A \<inter> M1) = \<mu> (A \<inter> ((M1 \<inter> P) \<union> (M1 \<inter> (sym_diff M1 P))))"
    by (metis Diff_subset_conv Int_Un_distrib Un_upper1 inf.orderE)
  also have "... = \<mu> ((A \<inter> (M1 \<inter> P)) \<union> (A \<inter> (M1 \<inter> (sym_diff M1 P))))" 
    by (simp add: Int_Un_distrib) 
  also have "... = \<mu> (A \<inter> (M1 \<inter> P)) + \<mu> (A \<inter> (M1 \<inter> (sym_diff M1 P)))" 
  proof (rule signed_measure_add)
    show "signed_measure M \<mu>" using sgn_meas .
    show "A \<inter> (M1 \<inter> P) \<in> sets M"
      by (meson assms(1) assms(2) assms(3) hahn_space_decomp_def sets.Int 
          signed_measure_space.pos_meas_setD1 signed_measure_space_axioms) 
    show "A \<inter> (M1 \<inter> sym_diff M1 P) \<in> sets M"
      by (meson Diff_subset assms(1) assms(2) assms(3) hahn_space_decomp_def 
          pos_meas_setD1 pos_meas_set_union pos_meas_subset sets.Diff sets.Int)
    show "A \<inter> (M1 \<inter> P) \<inter> (A \<inter> (M1 \<inter> sym_diff M1 P)) = {}" by auto
  qed
  also have "... = \<mu> (A \<inter> (M1 \<inter> (sym_diff M1 P)))"
  proof -
    have "A \<inter> (M1 \<inter> P) = {}" using assms hahn_space_decomp_def by auto
    thus ?thesis using signed_measure_empty[OF sgn_meas] by simp
  qed
  also have "... = 0" 
  proof (rule hahn_decomp_ess_unique[OF assms(1) assms(2)]) 
    show "A \<inter> (M1 \<inter> sym_diff M1 P) \<subseteq> sym_diff M1 P \<union> sym_diff M2 N" by auto
    show "A \<inter> (M1 \<inter> sym_diff M1 P) \<in> sets M" 
    proof -
      have "sym_diff M1 P \<in> sets M" using assms
        by (meson hahn_space_decomp_def sets.Diff sets.Un 
            signed_measure_space.pos_meas_setD1 signed_measure_space_axioms)
      hence "M1 \<inter> sym_diff M1 P \<in> sets M"
        by (meson assms(1) hahn_space_decomp_def pos_meas_setD1 sets.Int)
      thus ?thesis by (simp add: assms sets.Int)
    qed
  qed
  finally show ?thesis .
qed

lemma neg_inter_pos_0:
  assumes "hahn_space_decomp M1 M2"
    and "hahn_space_decomp P N"
    and "A \<in> sets M"
    and "A \<subseteq> P"
  shows "\<mu> (A \<inter> M2) = 0"
proof -
  have "\<mu> (A \<inter> M2) = \<mu> (A \<inter> ((M2 \<inter> N) \<union> (M2 \<inter> (sym_diff M2 N))))"
    by (metis Diff_subset_conv Int_Un_distrib Un_upper1 inf.orderE)
  also have "... = \<mu> ((A \<inter> (M2 \<inter> N)) \<union> (A \<inter> (M2 \<inter> (sym_diff M2 N))))" 
    by (simp add: Int_Un_distrib) 
  also have "... = \<mu> (A \<inter> (M2 \<inter> N)) + \<mu> (A \<inter> (M2 \<inter> (sym_diff M2 N)))" 
  proof (rule signed_measure_add)
    show "signed_measure M \<mu>" using sgn_meas .
    show "A \<inter> (M2 \<inter> N) \<in> sets M"
      by (meson assms(1) assms(2) assms(3) hahn_space_decomp_def sets.Int 
          signed_measure_space.neg_meas_setD1 signed_measure_space_axioms) 
    show "A \<inter> (M2 \<inter> sym_diff M2 N) \<in> sets M"
      by (meson Diff_subset assms(1) assms(2) assms(3) hahn_space_decomp_def 
          neg_meas_setD1 neg_meas_set_union neg_meas_subset sets.Diff sets.Int)
    show "A \<inter> (M2 \<inter> N) \<inter> (A \<inter> (M2 \<inter> sym_diff M2 N)) = {}" by auto
  qed
  also have "... = \<mu> (A \<inter> (M2 \<inter> (sym_diff M2 N)))"
  proof -
    have "A \<inter> (M2 \<inter> N) = {}" using assms hahn_space_decomp_def by auto
    thus ?thesis using signed_measure_empty[OF sgn_meas] by simp
  qed
  also have "... = 0" 
  proof (rule hahn_decomp_ess_unique[OF assms(1) assms(2)]) 
    show "A \<inter> (M2 \<inter> sym_diff M2 N) \<subseteq> sym_diff M1 P \<union> sym_diff M2 N" by auto
    show "A \<inter> (M2 \<inter> sym_diff M2 N) \<in> sets M" 
    proof -
      have "sym_diff M2 N \<in> sets M" using assms
        by (meson hahn_space_decomp_def sets.Diff sets.Un 
            signed_measure_space.neg_meas_setD1 signed_measure_space_axioms)
      hence "M2 \<inter> sym_diff M2 N \<in> sets M"
        by (meson assms(1) hahn_space_decomp_def neg_meas_setD1 sets.Int)
      thus ?thesis by (simp add: assms sets.Int)
    qed
  qed
  finally show ?thesis .
qed

lemma jordan_decomposition :
  shows "\<exists> m1 m2. jordan_decomp m1 m2" 
proof -
  have "\<exists> M1 M2. hahn_space_decomp M1 M2" using hahn_decomposition 
    unfolding hahn_space_decomp_def by simp
  from this obtain M1 M2 where "hahn_space_decomp M1 M2" by auto 
  note Mprops = this
  define m1 where "m1 = (\<lambda>A. \<mu> (A \<inter> M1))"
  define m2 where "m2 = (\<lambda>A. -\<mu> (A \<inter> M2))"  
  show ?thesis unfolding jordan_decomp_def
  proof (intro exI allI impI conjI ballI)
    show "measure_space (space M) (sets M) (\<lambda>x. e2ennreal (m1 x))" 
      using pos_signed_to_meas_space Mprops m1_def 
      unfolding hahn_space_decomp_def by auto
  next
    show "measure_space (space M) (sets M) (\<lambda>x. e2ennreal (m2 x))" 
      using neg_signed_to_meas_space Mprops m2_def 
      unfolding hahn_space_decomp_def by auto
  next
    fix A
    assume "A\<in> sets M"
    thus "0 \<le> m1 A" unfolding m1_def using Mprops 
      unfolding hahn_space_decomp_def 
      by (meson inf_sup_ord(2) pos_meas_setD1 sets.Int 
          signed_measure_space.pos_measure_meas signed_measure_space_axioms)
  next
    fix A 
    assume "A\<in> sets M"
    thus "0 \<le> m2 A" unfolding m2_def using Mprops 
      unfolding hahn_space_decomp_def
      by (metis ereal_0_le_uminus_iff inf_sup_ord(2) neg_meas_self 
          neg_meas_setD1 neg_meas_subset sets.Int)
  next
    fix A
    assume "A \<in> sets M"
    have "\<mu> A = \<mu> ((A \<inter> M1) \<union> (A \<inter> M2))" using Mprops 
      unfolding hahn_space_decomp_def
      by (metis Int_Un_distrib \<open>A \<in> sets M\<close> sets.Int_space_eq2)
    also have "... = \<mu> (A \<inter> M1) + \<mu> (A \<inter> M2)" 
    proof (rule signed_measure_add)
      show "signed_measure M \<mu>" using sgn_meas .
      show "A \<inter> M1 \<in> sets M" using Mprops  \<open>A \<in> sets M\<close> 
        unfolding hahn_space_decomp_def 
        by (simp add: pos_meas_setD1 sets.Int) 
      show "A \<inter> M2 \<in> sets M" using Mprops \<open>A \<in> sets M\<close> 
        unfolding hahn_space_decomp_def
        by (simp add: neg_meas_setD1 sets.Int) 
      show "A \<inter> M1 \<inter> (A \<inter> M2) = {}" using Mprops 
        unfolding hahn_space_decomp_def by auto
    qed
    also have "... = m1 A - m2 A" using m1_def m2_def by simp
    finally show "\<mu> A = m1 A - m2 A" .    
  next
    fix P N A
    assume "hahn_space_decomp P N" and "A \<in> sets M" and "A \<subseteq> N" 
    note hn = this
    have "\<mu> (A \<inter> M1) = 0"
    proof (rule pos_inter_neg_0[OF _ hn])
      show "hahn_space_decomp M1 M2" using Mprops 
        unfolding hahn_space_decomp_def by simp
    qed
    thus "m1 A = 0" unfolding m1_def by simp
  next
    fix P N A
    assume "hahn_space_decomp P N" and "A \<in> sets M" and "A \<subseteq> P" 
    note hp = this
    have "\<mu> (A \<inter> M2) = 0"
    proof (rule neg_inter_pos_0[OF _ hp])
      show "hahn_space_decomp M1 M2" using Mprops 
        unfolding hahn_space_decomp_def by simp
    qed
    thus "m2 A = 0" unfolding m2_def by simp
  next
    show "(\<forall>E\<in>sets M. m1 E < \<infinity>) \<or> (\<forall>E\<in>sets M. m2 E < \<infinity>)"
    proof (cases "\<forall> E \<in> sets M. m1 E < \<infinity>")
      case True
      thus ?thesis by simp
    next
      case False
      have "\<forall> E \<in> sets M. m2 E < \<infinity>"
      proof
        fix E
        assume "E \<in> sets M"
        show "m2 E < \<infinity>"
        proof -
          have "(m2 E) = -\<mu> (E \<inter> M2)" using m2_def by simp        
          also have "... \<noteq> \<infinity>" using False sgn_meas inf_range
            by (metis ereal_less_PInfty ereal_uminus_uminus m1_def rangeI)
          finally have "m2 E \<noteq> \<infinity>" .
          thus ?thesis by (simp add: top.not_eq_extremum)
        qed
      qed
      thus ?thesis by simp
    qed
  qed
qed

lemma jordan_decomposition_unique :
  assumes "jordan_decomp m1 m2" 
    and "jordan_decomp n1 n2"
    and "A \<in> sets M"
  shows "m1 A = n1 A" "m2 A = n2 A"
proof -
  have "\<exists> M1 M2. hahn_space_decomp M1 M2" using hahn_decomposition by simp
  from this obtain M1 M2 where "hahn_space_decomp M1 M2" by auto 
  note mprop = this
  have "m1 A = \<mu> (A \<inter> M1)" using assms jordan_decomp_pos_meas mprop by simp
  also have "... = n1 A" using assms jordan_decomp_pos_meas[of n1] mprop 
    by simp
  finally show "m1 A = n1 A" .
  have "m2 A = -\<mu> (A \<inter> M2)" using assms jordan_decomp_neg_meas mprop by simp
  also have "... = n2 A" using assms jordan_decomp_neg_meas[of n1] mprop 
    by simp
  finally show "m2 A = n2 A" .
qed
end
end

