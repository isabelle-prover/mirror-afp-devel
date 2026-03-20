theory Lebesgue_Stieltjes_Integral
  imports "Wlog.Wlog" Preliminaries_LSI
begin

section \<open>Interval Measure Integral\<close>

subsection \<open>Basic Calculations\<close>

lemma interval_measure_const_null:
  fixes c::real
  shows "interval_measure (\<lambda>_. c) = null_measure lborel"
proof -
  have "\<And>s t. s \<le> t \<Longrightarrow> emeasure (interval_measure (\<lambda>_. c)) {s<..t} = 0"
    using emeasure_interval_measure_Ioc by force
  then show ?thesis by (intro measure_eqI_Ioc; simp)
qed

lemma interval_measure_singleton:
  fixes F :: "real \<Rightarrow> real" and s::real
  assumes "mono F" "\<And>x. continuous (at_right x) F"
  shows "(interval_measure F) {s} = F s - Lim (at_left s) F"
proof -
  let ?dF = "interval_measure F"
  let ?I = "\<lambda>n::nat. {s - 1/(n+1) <..s}"
  have limsn: "(\<lambda>n. s - 1 / (real n + 1)) \<longlonglongrightarrow> s" by real_asymp
  have "{s} = (\<Inter> (range ?I))"
  proof
    have "\<And>n. s \<in> ?I n" by simp
    thus "{s} \<subseteq> (\<Inter> (range ?I))" by simp
    show "(\<Inter> (range ?I)) \<subseteq> {s}"
    proof
      fix x assume "x \<in> (\<Inter> (range ?I))"
      hence x_I: "\<And>n. x \<in> ?I n" by simp
      hence "\<And>n. s - 1 / (real n + 1) < x" by simp
      hence "s \<le> x"
        apply (intro LIMSEQ_le_const2[OF limsn])
        using less_eq_real_def by (intro exI[of _ 0]) simp
      moreover have "x \<le> s" using x_I by simp
      ultimately show "x \<in> {s}" by simp
    qed
  qed
  moreover have "(\<lambda>n. emeasure ?dF (?I n)) \<longlonglongrightarrow> emeasure ?dF (\<Inter> (range ?I))"
  proof (rule Lim_emeasure_decseq)
    show "range ?I \<subseteq> sets ?dF" by (rewrite sets_interval_measure) force
    show "monotone (\<le>) (\<lambda>J K. K \<subseteq> J) ?I"
    proof (rule monotoneI)
      fix m n :: nat assume "m \<le> n"
      hence "s - 1 / (real m + 1) \<le> s - 1 / (real n + 1)"
        by (metis add.commute of_nat_Suc Suc_le_mono diff_left_mono inverse_of_nat_le Suc_not_Zero)
      thus "?I n \<subseteq> ?I m" by force
    qed
    show "\<And>n. emeasure ?dF (?I n) \<noteq> \<infinity>"
      using emeasure_interval_measure_Ioc by (simp add: assms monoD)
  qed
  moreover have "(\<lambda>n. ?dF (?I n)) \<longlonglongrightarrow> F s - Lim (at_left s) F"
  proof -
    have "(F \<longlongrightarrow> Sup (F ` {..<s})) (at_left s)"
      using Lim_left_bound[of UNIV s F "F s"] monoD[OF \<open>mono F\<close>] by simp
    hence "(F \<longlongrightarrow> Lim (at_left s) F) (at_left s)" by (simp add: tendsto_Lim)
    hence "(\<lambda>n::nat. F (s - 1 / (real n + 1))) \<longlonglongrightarrow> Lim (at_left s) F"
      apply (rewrite in asm tendsto_at_iff_sequentially)
      apply (drule spec[of _ "\<lambda>n. s - 1 / (real n + 1)"])
      unfolding comp_def using limsn by simp
    hence "(\<lambda>n::nat. ennreal (F s - F (s - 1 / (real n + 1))))
      \<longlonglongrightarrow> ennreal (F s - Lim (at_left s) F)"
      by (intro tendsto_intros)
    thus ?thesis by (rewrite emeasure_interval_measure_Ioc; simp add: assms monoD)
  qed
  ultimately show ?thesis using LIMSEQ_unique by simp
qed

lemma interval_measure_singleton_continuous:
  fixes F :: "real \<Rightarrow> real" and s::real
  assumes "mono F" "\<And>x. continuous (at_right x) F" "isCont F s"
  shows "(interval_measure F) {s} = 0"
proof -
  have "Lim (at_left s) F = F s"
    using assms continuous_at_imp_continuous_within continuous_within
      tendsto_Lim trivial_limit_at_left_real by blast
  with interval_measure_singleton assms show ?thesis by simp
qed

subsection \<open>Changing the Underlying Function\<close>

lemma einterval_nn_integral_interval_measure_cong:
  fixes F G :: "real \<Rightarrow> real" and h :: "real \<Rightarrow> ennreal" and a b :: ereal
  assumes "mono F" "\<And>x. continuous (at_right x) F" and
    "mono G" "\<And>x. continuous (at_right x) G" and
    "(F - G) constant_on (einterval a b)" and
    "h \<in> borel_measurable borel"
  shows "(\<integral>\<^sup>+x\<in>(einterval a b). h x \<partial>(interval_measure F)) =
    (\<integral>\<^sup>+x\<in>(einterval a b). h x \<partial>(interval_measure G))"
proof -
  let ?IM = interval_measure
  let ?Iab = "einterval a b"
  from assms obtain c where FG_c: "\<And>x. x \<in> ?Iab \<Longrightarrow> F x - G x = c"
    unfolding constant_on_def by force
  have "\<And>s t. a < ereal s \<and> s \<le> t \<and> ereal t < b \<Longrightarrow> emeasure (?IM F) {s<..t} \<noteq> \<infinity>"
    using assms unfolding mono_def by (rewrite emeasure_interval_measure_Ioc; simp)
  moreover have "\<And>s t. a < ereal s \<and> s \<le> t \<and> ereal t < b \<Longrightarrow>
    emeasure (?IM F) {s<..t} = emeasure (?IM G) {s<..t}"
  proof -
    fix s t assume astb: "a < ereal s \<and> s \<le> t \<and> ereal t < b"
    hence "F t - F s = G t - G s"
      using FG_c by (smt (verit) einterval_iff ereal_less_le less_ereal_le)
    thus "emeasure (?IM F) {s<..t} = emeasure (?IM G) {s<..t}"
      using assms astb unfolding mono_def by (rewrite emeasure_interval_measure_Ioc; simp)+
  qed
  ultimately have "restrict_space (?IM F) ?Iab = restrict_space (?IM G) ?Iab"
    by (intro measure_einterval_eqI_Ioc; simp)
  thus ?thesis using nn_integral_restrict_space[THEN sym]
 by (rewrite nn_integral_restrict_space[THEN sym], simp)+ simp
qed

corollary Ioo_nn_integral_interval_measure_cong:
  fixes F G :: "real \<Rightarrow> real" and h :: "real \<Rightarrow> ennreal" and r s :: real
  assumes "mono F" "\<And>x. continuous (at_right x) F" and
    "mono G" "\<And>x. continuous (at_right x) G" and
    "(F - G) constant_on {r<..<s}" and
    "h \<in> borel_measurable borel"
  shows "(\<integral>\<^sup>+x\<in>{r<..<s}. h x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{r<..<s}. h x \<partial>(interval_measure G))"
  using einterval_eq_Icc assms einterval_nn_integral_interval_measure_cong
  by (metis (mono_tags, lifting) nn_integral_cong)

corollary Ioi_nn_integral_interval_measure_cong:
  fixes F G :: "real \<Rightarrow> real" and h :: "real \<Rightarrow> ennreal" and r::real
  assumes "mono F" "\<And>x. continuous (at_right x) F" and
    "mono G" "\<And>x. continuous (at_right x) G" and
    "(F - G) constant_on {r<..}" and
    "h \<in> borel_measurable borel"
  shows "(\<integral>\<^sup>+x\<in>{r<..}. h x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{r<..}. h x \<partial>(interval_measure G))"
  using einterval_eq_Ici assms einterval_nn_integral_interval_measure_cong
  by (metis (mono_tags, lifting) nn_integral_cong)

corollary Iio_nn_integral_interval_measure_cong:
  fixes F G :: "real \<Rightarrow> real" and h :: "real \<Rightarrow> ennreal" and s::real
  assumes "mono F" "\<And>x. continuous (at_right x) F" and
    "mono G" "\<And>x. continuous (at_right x) G" and
    "(F - G) constant_on {..<s}" and
    "h \<in> borel_measurable borel"
  shows "(\<integral>\<^sup>+x\<in>{..<s}. h x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{..<s}. h x \<partial>(interval_measure G))"
  using einterval_eq_Iic assms einterval_nn_integral_interval_measure_cong
  by (metis (mono_tags, lifting) nn_integral_cong)

corollary nn_integral_interval_measure_cong:
  fixes F G :: "real \<Rightarrow> real" and h :: "real \<Rightarrow> ennreal"
  assumes "mono F" "\<And>x. continuous (at_right x) F" and
    "mono G" "\<And>x. continuous (at_right x) G" and
    "(F - G) constant_on UNIV" and
    "h \<in> borel_measurable borel"
  shows "(\<integral>\<^sup>+x. h x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x. h x \<partial>(interval_measure G))"
  using einterval_nn_integral_interval_measure_cong einterval_eq_UNIV assms
  by (metis (mono_tags, lifting) mult_1_right
      indicator_eq_1_iff nn_integral_cong space_interval_measure)

lemma singleton_nn_integral_interval_measure_cong:
  fixes F G :: "real \<Rightarrow> real" and h :: "real \<Rightarrow> ennreal" and s::real
  assumes "mono F" "\<And>x. continuous (at_right x) F" and
    "mono G" "\<And>x. continuous (at_right x) G" and
    "F s - Lim (at_left s) F = G s - Lim (at_left s) G" and
    "h \<in> borel_measurable borel"
  shows "(\<integral>\<^sup>+x\<in>{s}. h x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{s}. h x \<partial>(interval_measure G))"
  using interval_measure_singleton assms by (rewrite nn_integral_indicator_singleton; simp)

lemma singleton_const_nn_integral_interval_measure_cong:
  fixes F G :: "real \<Rightarrow> real" and h :: "real \<Rightarrow> ennreal" and r s :: real
  assumes "mono F" "\<And>x. continuous (at_right x) F" and
    "mono G" "\<And>x. continuous (at_right x) G" and
    "(F - G) constant_on {r<..s}" and "r < s" and
    "h \<in> borel_measurable borel"
  shows "(\<integral>\<^sup>+x\<in>{s}. h x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{s}. h x \<partial>(interval_measure G))"
proof -
  have [simp]: "{..<s} \<inter> {r<..} = {r<..<s}" using assms by force
  have [simp]: "at s within {r<..<s} \<noteq> bot"
    using at_within_Ioo_at_left assms trivial_limit_at_left_real by metis
  from assms obtain c::real where FGc: "\<And>x. x \<in> {r<..s} \<Longrightarrow> F x - G x = c"
    unfolding constant_on_def by force
  have "Lim (at s within {r<..<s}) F = Sup (F ` {r<..<s})"
  proof -
    have "(F \<longlongrightarrow> Sup (F ` ({..<s} \<inter> {r<..}))) (at s within {..<s} \<inter> {r<..})"
      apply (rule Lim_left_bound[where I="{r<..}" and K="F s"])
      using assms monoD by force+
    thus ?thesis by (intro tendsto_Lim; simp)
  qed
  moreover have "Lim (at s within {r<..<s}) G = Sup (G ` {r<..<s})"
  proof -
    have "(G \<longlongrightarrow> Sup (G ` ({..<s} \<inter> {r<..}))) (at s within {..<s} \<inter> {r<..})"
      apply (rule Lim_left_bound[where I="{r<..}" and K="G s"])
      using assms monoD by force+
    thus ?thesis by (intro tendsto_Lim; simp)
  qed
  moreover have "Sup (F ` {r<..<s}) = c + Sup (G ` {r<..<s})"
  proof -
    have "bdd_above (G ` {r<..<s})" using assms by (metis bdd_above_Ioo bdd_above_image_mono)
    moreover have "\<And>x. x \<in> {r<..<s} \<Longrightarrow> F x = c + G x" using FGc by force
    ultimately show ?thesis using FGc assms by (rewrite Sup_add_eq[THEN sym]; simp)
  qed
  ultimately have "Lim (at_left s) F - Lim (at_left s) G = c"
    using at_within_Ioo_at_left assms by force
  hence "F s - Lim (at_left s) F = G s - Lim (at_left s) G" using FGc assms by fastforce
  thus ?thesis by (intro singleton_nn_integral_interval_measure_cong; simp add: assms)
qed

lemma Ioc_nn_integral_interval_measure_cong:
  fixes F G :: "real \<Rightarrow> real" and h :: "real \<Rightarrow> ennreal" and r s :: real
  assumes "mono F" "\<And>x. continuous (at_right x) F" and
    "mono G" "\<And>x. continuous (at_right x) G" and
    "(F - G) constant_on {r<..s}" and
    "h \<in> borel_measurable borel"
  shows "(\<integral>\<^sup>+x\<in>{r<..s}. h x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{r<..s}. h x \<partial>(interval_measure G))"
proof -
  let ?IM = interval_measure
  show ?thesis
  proof (cases \<open>r < s\<close>)
    case True
    hence [simp]: "insert s {r<..<s} = {r<..s}" by force
    have "(\<integral>\<^sup>+x\<in>{r<..<s}. h x \<partial>(?IM F)) = (\<integral>\<^sup>+x\<in>{r<..<s}. h x \<partial>(?IM G))"
    proof -
      have "{r<..<s} = einterval (ereal r) (ereal s)" by simp
      moreover have "(F - G) constant_on (einterval (ereal r) (ereal s))"
      proof -
        have "(einterval (ereal r) (ereal s)) \<subseteq> {r<..s}" by force
        with assms constant_on_subset show ?thesis by simp
      qed
      ultimately show ?thesis using assms einterval_nn_integral_interval_measure_cong by presburger
    qed
    moreover have "(\<integral>\<^sup>+x\<in>{s}. h x \<partial>(?IM F)) = (\<integral>\<^sup>+x\<in>{s}. h x \<partial>(?IM G))"
      by (rule singleton_const_nn_integral_interval_measure_cong[where r=r]; simp add: assms True)
    ultimately have "(\<integral>\<^sup>+x\<in>{r<..<s}. h x \<partial>(?IM F)) + (\<integral>\<^sup>+x\<in>{s}. h x \<partial>(?IM F)) =
      (\<integral>\<^sup>+x\<in>{r<..<s}. h x \<partial>(?IM G)) + (\<integral>\<^sup>+x\<in>{s}. h x \<partial>(?IM G))"
      by simp
    moreover have
      "\<And>H. (\<integral>\<^sup>+x\<in>{r<..<s}. h x \<partial>(?IM H)) + (\<integral>\<^sup>+x\<in>{s}. h x \<partial>(?IM H)) = (\<integral>\<^sup>+x\<in>{r<..s}. h x \<partial>(?IM H))"
      by (rewrite nn_integral_disjoint_pair[THEN sym]; measurable; simp add: assms)
    ultimately show ?thesis by simp
  next
    case False
    hence "{r<..s} = {}" using greaterThanAtMost_empty_iff by simp
    thus ?thesis by simp
  qed
qed

lemma Iic_nn_integral_interval_measure_cong:
  fixes F G :: "real \<Rightarrow> real" and h :: "real \<Rightarrow> ennreal" and s::real
  assumes "mono F" "\<And>x. continuous (at_right x) F" and
    "mono G" "\<And>x. continuous (at_right x) G" and
    "(F - G) constant_on {..s}" and
    "h \<in> borel_measurable borel"
  shows "(\<integral>\<^sup>+x\<in>{..s}. h x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{..s}. h x \<partial>(interval_measure G))"
proof -
  let ?IM = interval_measure
  have [simp]: "insert s {..<s} = {..s}" by force
  have "(\<integral>\<^sup>+x\<in>{..<s}. h x \<partial>(?IM F)) = (\<integral>\<^sup>+x\<in>{..<s}. h x \<partial>(?IM G))"
  proof -
    have "{..<s} = einterval (-\<infinity>) (ereal s)" by simp
    moreover have "(F - G) constant_on (einterval (-\<infinity>) (ereal s))"
    proof -
      have "(einterval (-\<infinity>) (ereal s)) \<subseteq> {..s}" by force
      with assms constant_on_subset show ?thesis by simp
    qed
    ultimately show ?thesis using assms einterval_nn_integral_interval_measure_cong by presburger
  qed
  moreover have "(\<integral>\<^sup>+x\<in>{s}. h x \<partial>(?IM F)) = (\<integral>\<^sup>+x\<in>{s}. h x \<partial>(?IM G))"
  proof -
    have "(F - G) constant_on {s-1 <..s}"
      using assms constant_on_subset by (metis atMost_iff greaterThanAtMost_iff subset_eq)
    thus ?thesis
      by (intro singleton_const_nn_integral_interval_measure_cong[where r="s-1"]; simp add: assms)
  qed
  ultimately have "(\<integral>\<^sup>+x\<in>{..<s}. h x \<partial>(?IM F)) + (\<integral>\<^sup>+x\<in>{s}. h x \<partial>(?IM F)) =
      (\<integral>\<^sup>+x\<in>{..<s}. h x \<partial>(?IM G)) + (\<integral>\<^sup>+x\<in>{s}. h x \<partial>(?IM G))"
    by simp
  moreover have
    "\<And>H. (\<integral>\<^sup>+x\<in>{..<s}. h x \<partial>(?IM H)) + (\<integral>\<^sup>+x\<in>{s}. h x \<partial>(?IM H)) = (\<integral>\<^sup>+x\<in>{..s}. h x \<partial>(?IM H))"
    by (rewrite nn_integral_disjoint_pair[THEN sym]; measurable; simp add: assms)
  ultimately show ?thesis by simp
qed

lemma Ico_nn_integral_interval_measure_cong:
  fixes F G :: "real \<Rightarrow> real" and h :: "real \<Rightarrow> ennreal" and r s :: real
  assumes "mono F" "\<And>x. continuous (at_right x) F" and
    "mono G" "\<And>x. continuous (at_right x) G" and
    "(F - G) constant_on {r<..<s}" and
    "F r - Lim (at_left r) F = G r - Lim (at_left r) G" and
    "h \<in> borel_measurable borel"
  shows "(\<integral>\<^sup>+x\<in>{r..<s}. h x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{r..<s}. h x \<partial>(interval_measure G))"
proof -
  let ?IM = interval_measure
  show ?thesis
  proof (cases \<open>r < s\<close>)
    case True
    hence [simp]: "insert r {r<..<s} = {r..<s}" by force
    have "\<And>H. (\<integral>\<^sup>+x\<in>{r..<s}. h x \<partial>(?IM H)) = (\<integral>\<^sup>+x\<in>{r}. h x \<partial>(?IM H)) + (\<integral>\<^sup>+x\<in>{r<..<s}. h x \<partial>(?IM H))"
      by (rewrite nn_integral_disjoint_pair[THEN sym]; measurable; simp add: assms)
    moreover have "(\<integral>\<^sup>+x\<in>{r}. h x \<partial>(?IM F)) = (\<integral>\<^sup>+x\<in>{r}. h x \<partial>(?IM G))"
      by (rewrite singleton_nn_integral_interval_measure_cong; measurable; simp add: assms) 
    moreover have "(\<integral>\<^sup>+x\<in>{r<..<s}. h x \<partial>(?IM F)) = (\<integral>\<^sup>+x\<in>{r<..<s}. h x \<partial>(?IM G))"
      apply (rewrite einterval_eq_Icc[THEN sym])+
      by (rewrite einterval_nn_integral_interval_measure_cong; measurable; simp add: assms)
    ultimately show ?thesis by simp
  next
    case False
    thus ?thesis by simp
  qed
qed

corollary Ico_Cont_nn_integral_interval_measure_cong:
  fixes F G :: "real \<Rightarrow> real" and h :: "real \<Rightarrow> ennreal" and r s :: real
  assumes "mono F" "\<And>x. continuous (at_right x) F" and
    "mono G" "\<And>x. continuous (at_right x) G" and
    "(F - G) constant_on {r<..<s}" and
    "isCont F r" "isCont G r" and
    "h \<in> borel_measurable borel"
  shows "(\<integral>\<^sup>+x\<in>{r..<s}. h x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{r..<s}. h x \<partial>(interval_measure G))"
proof -
  from assms have "F r - Lim (at_left r) F = G r - Lim (at_left r) G"
    by (metis add_0 continuous_at_imp_continuous_at_within continuous_within
      eq_diff_eq tendsto_Lim trivial_limit_at_left_real)
  thus ?thesis
  using assms by (intro Ico_nn_integral_interval_measure_cong; simp)
qed

lemma Ici_nn_integral_interval_measure_cong:
  fixes F G :: "real \<Rightarrow> real" and h :: "real \<Rightarrow> ennreal" and r::real
  assumes "mono F" "\<And>x. continuous (at_right x) F" and
    "mono G" "\<And>x. continuous (at_right x) G" and
    "(F - G) constant_on {r<..}" and
    "F r - Lim (at_left r) F = G r - Lim (at_left r) G" and
    "h \<in> borel_measurable borel"
  shows "(\<integral>\<^sup>+x\<in>{r..}. h x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{r..}. h x \<partial>(interval_measure G))"
proof -
  let ?IM = interval_measure
  have [simp]: "insert r {r<..} = {r..}" by force
  have "\<And>H. (\<integral>\<^sup>+x\<in>{r..}. h x \<partial>(?IM H)) = (\<integral>\<^sup>+x\<in>{r}. h x \<partial>(?IM H)) + (\<integral>\<^sup>+x\<in>{r<..}. h x \<partial>(?IM H))"
    by (rewrite nn_integral_disjoint_pair[THEN sym]; measurable; simp add: assms)
  moreover have "(\<integral>\<^sup>+x\<in>{r}. h x \<partial>(?IM F)) = (\<integral>\<^sup>+x\<in>{r}. h x \<partial>(?IM G))"
    by (rewrite singleton_nn_integral_interval_measure_cong; measurable; simp add: assms)
  moreover have "(\<integral>\<^sup>+x\<in>{r<..}. h x \<partial>(?IM F)) = (\<integral>\<^sup>+x\<in>{r<..}. h x \<partial>(?IM G))"
    apply (rewrite einterval_eq_Ici[THEN sym])+
    by (rewrite einterval_nn_integral_interval_measure_cong; measurable; simp add: assms)
  ultimately show ?thesis by simp
qed

corollary Ici_Cont_nn_integral_interval_measure_cong:
  fixes F G :: "real \<Rightarrow> real" and h :: "real \<Rightarrow> ennreal" and r::real
  assumes "mono F" "\<And>x. continuous (at_right x) F" and
    "mono G" "\<And>x. continuous (at_right x) G" and
    "(F - G) constant_on {r<..}" and
    "isCont F r" "isCont G r" and
    "h \<in> borel_measurable borel"
  shows "(\<integral>\<^sup>+x\<in>{r..}. h x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{r..}. h x \<partial>(interval_measure G))"
proof -
  from assms have "F r - Lim (at_left r) F = G r - Lim (at_left r) G"
    by (metis continuous_at_imp_continuous_within continuous_within
        tendsto_Lim trivial_limit_at_left_real diff_self)
  thus ?thesis
  using assms by (intro Ici_nn_integral_interval_measure_cong; simp)
qed

lemma Icc_nn_integral_interval_measure_cong:
  fixes F G :: "real \<Rightarrow> real" and h :: "real \<Rightarrow> ennreal" and r s :: real
  assumes "mono F" "\<And>x. continuous (at_right x) F" and
    "mono G" "\<And>x. continuous (at_right x) G" and
    "(F - G) constant_on {r<..s}" and
    "F r - Lim (at_left r) F = G r - Lim (at_left r) G" and
    "h \<in> borel_measurable borel"
  shows "(\<integral>\<^sup>+x\<in>{r..s}. h x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{r..s}. h x \<partial>(interval_measure G))"
proof -
  let ?IM = interval_measure
  show ?thesis
  proof (cases \<open>r \<le> s\<close>)
    case True
    hence [simp]: "insert r {r<..s} = {r..s}" by force
    have "\<And>H. (\<integral>\<^sup>+x\<in>{r..s}. h x \<partial>(?IM H)) = (\<integral>\<^sup>+x\<in>{r}. h x \<partial>(?IM H)) + (\<integral>\<^sup>+x\<in>{r<..s}. h x \<partial>(?IM H))"
      by (rewrite nn_integral_disjoint_pair[THEN sym]; measurable; simp add: assms)
    moreover have "(\<integral>\<^sup>+x\<in>{r}. h x \<partial>(?IM F)) = (\<integral>\<^sup>+x\<in>{r}. h x \<partial>(?IM G))"
      by (rewrite singleton_nn_integral_interval_measure_cong; measurable; simp add: assms) 
    moreover have "(\<integral>\<^sup>+x\<in>{r<..s}. h x \<partial>(?IM F)) = (\<integral>\<^sup>+x\<in>{r<..s}. h x \<partial>(?IM G))"
      by (rewrite Ioc_nn_integral_interval_measure_cong; measurable; simp add: assms)
    ultimately show ?thesis by simp
  next
    case False
    thus ?thesis by simp
  qed
qed

corollary Icc_Cont_nn_integral_interval_measure_cong:
  fixes F G :: "real \<Rightarrow> real" and h :: "real \<Rightarrow> ennreal" and r s :: real
  assumes "mono F" "\<And>x. continuous (at_right x) F" and
    "mono G" "\<And>x. continuous (at_right x) G" and
    "(F - G) constant_on {r<..s}" and
    "isCont F r" "isCont G r" and
    "h \<in> borel_measurable borel"
  shows "(\<integral>\<^sup>+x\<in>{r..s}. h x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{r..s}. h x \<partial>(interval_measure G))"
proof -
  from assms have "F r - Lim (at_left r) F = G r - Lim (at_left r) G"
    by (metis add_0 continuous_at_imp_continuous_at_within continuous_within
        eq_diff_eq tendsto_Lim trivial_limit_at_left_real)
  thus ?thesis
    using assms by (intro Icc_nn_integral_interval_measure_cong; simp)
qed

subsection \<open>Restricting the Integral\<close>

lemma nn_integral_interval_measure_Ici:
  fixes F :: "real \<Rightarrow> real" and  g :: "real \<Rightarrow> ennreal" and r::real
  assumes "mono F" "\<And>x. continuous (at_right x) F" "g \<in> borel_measurable borel" and
    "F constant_on {..<r}"
  shows "(\<integral>\<^sup>+x. g x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{r..}. g x \<partial>(interval_measure F))"
proof -
  let ?IMF = "interval_measure F"
  have "{..<r} \<union> {r..} = UNIV" by auto
  moreover have "{..<r} \<inter> {r..} = {}" by auto
  ultimately have "(\<integral>\<^sup>+x. g x \<partial>?IMF) = (\<integral>\<^sup>+x\<in>{..<r}. g x \<partial>?IMF) + (\<integral>\<^sup>+x\<in>{r..}. g x \<partial>?IMF)"
    using assms by (rewrite nn_integral_disjoint_pair[THEN sym]; simp)
  also have "(\<integral>\<^sup>+x\<in>{..<r}. g x \<partial>?IMF) = 0"
    using assms interval_measure_const_null mono_on_const
    by (rewrite Iio_nn_integral_interval_measure_cong[where G="\<lambda>_.0"]; simp add: fun_diff_def)
  finally show ?thesis by simp
qed

lemma nn_integral_interval_measure_Ioi:
  fixes F :: "real \<Rightarrow> real" and  g :: "real \<Rightarrow> ennreal" and r::real
  assumes "mono F" "\<And>x. continuous (at_right x) F" "g \<in> borel_measurable borel" and
    "F constant_on {..<r}" "isCont F r"
  shows "(\<integral>\<^sup>+x. g x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{r<..}. g x \<partial>(interval_measure F))"
proof -
  let ?IMF = "interval_measure F"
  have [simp]: "insert r {r<..} = {r..}" by force
  have "(\<integral>\<^sup>+x. g x \<partial>?IMF) = (\<integral>\<^sup>+x\<in>{r..}. g x \<partial>?IMF)"
    by (rule nn_integral_interval_measure_Ici; simp add: assms)
  also have "\<dots> = (\<integral>\<^sup>+x\<in>{r}. g x \<partial>?IMF) + (\<integral>\<^sup>+x\<in>{r<..}. g x \<partial>?IMF)"
    using assms by (rewrite nn_integral_disjoint_pair[THEN sym]; simp)
  also have "(\<integral>\<^sup>+x\<in>{r}. g x \<partial>?IMF) = 0" using assms interval_measure_singleton_continuous by simp
  finally show ?thesis by simp
qed

lemma nn_integral_interval_measure_Iic:
  fixes F :: "real \<Rightarrow> real" and  g :: "real \<Rightarrow> ennreal" and s::real
  assumes "mono F" "\<And>x. continuous (at_right x) F" "g \<in> borel_measurable borel" and
    "F constant_on {s<..}"
  shows "(\<integral>\<^sup>+x. g x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{..s}. g x \<partial>(interval_measure F))"
proof -
  let ?IMF = "interval_measure F"
  have "{..s} \<union> {s<..} = UNIV" by auto
  moreover have "{..s} \<inter> {s<..} = {}" by auto
  ultimately have "(\<integral>\<^sup>+x. g x \<partial>?IMF) = (\<integral>\<^sup>+x\<in>{..s}. g x \<partial>?IMF) + (\<integral>\<^sup>+x\<in>{s<..}. g x \<partial>?IMF)"
    using assms by (rewrite nn_integral_disjoint_pair[THEN sym]; simp)
  also have "(\<integral>\<^sup>+x\<in>{s<..}. g x \<partial>?IMF) = 0"
    using assms interval_measure_const_null mono_on_const
    by (rewrite Ioi_nn_integral_interval_measure_cong[where G="\<lambda>_.0"]; simp add: fun_diff_def)
  finally show ?thesis by simp
qed

lemma nn_integral_interval_measure_Iio:
  fixes F :: "real \<Rightarrow> real" and  g :: "real \<Rightarrow> ennreal" and s::real
  assumes "mono F" "\<And>x. continuous (at_right x) F" "g \<in> borel_measurable borel" and
    "F constant_on {s<..}" "isCont F s"
  shows "(\<integral>\<^sup>+x. g x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{..<s}. g x \<partial>(interval_measure F))"
proof -
  let ?IMF = "interval_measure F"
  have [simp]: "insert s {..<s} = {..s}" by force
  have "(\<integral>\<^sup>+x. g x \<partial>?IMF) = (\<integral>\<^sup>+x\<in>{..s}. g x \<partial>?IMF)"
    by (rule nn_integral_interval_measure_Iic; simp add: assms)
  also have "\<dots> = (\<integral>\<^sup>+x\<in>{s}. g x \<partial>?IMF) + (\<integral>\<^sup>+x\<in>{..<s}. g x \<partial>?IMF)"
    using assms by (rewrite nn_integral_disjoint_pair[THEN sym]; simp)
  also have "(\<integral>\<^sup>+x\<in>{s}. g x \<partial>?IMF) = 0"
    using assms interval_measure_singleton_continuous by simp
  finally show ?thesis by simp
qed

lemma nn_integral_interval_measure_Icc:
  fixes F :: "real \<Rightarrow> real" and  g :: "real \<Rightarrow> ennreal" and r s :: real
  assumes "mono F" "\<And>x. continuous (at_right x) F" "g \<in> borel_measurable borel" and
    "F constant_on {..<r}" "F constant_on {s<..}"
  shows "(\<integral>\<^sup>+x. g x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{r..s}. g x \<partial>(interval_measure F))"
proof -
  let ?IMF = "interval_measure F"
  show ?thesis
  proof (cases \<open>r \<le> s\<close>)
    case True
    have "(\<integral>\<^sup>+x. g x \<partial>?IMF) = (\<integral>\<^sup>+x\<in>{r..}. g x \<partial>?IMF)"
      by (rule nn_integral_interval_measure_Ici; simp add: assms)
    also have "\<dots> = (\<integral>\<^sup>+x\<in>{r..s}. g x \<partial>?IMF)"
    proof -
      have "{r..} = {r..s} \<union> {s<..}" using assms using True by force
      moreover have "{r..s} \<inter> {s<..} = {}" by auto
      ultimately have "(\<integral>\<^sup>+x\<in>{r..}. g x \<partial>?IMF) = (\<integral>\<^sup>+x\<in>{r..s}. g x \<partial>?IMF) + (\<integral>\<^sup>+x\<in>{s<..}. g x \<partial>?IMF)"
        using assms by (rewrite nn_integral_disjoint_pair[THEN sym]; simp)
      also have "(\<integral>\<^sup>+x\<in>{s<..}. g x \<partial>?IMF) = 0"
        using assms interval_measure_const_null mono_on_const
        by (rewrite Ioi_nn_integral_interval_measure_cong[where G="\<lambda>_.0"]; simp add: fun_diff_def)
      finally show ?thesis by simp
    qed
    finally show ?thesis .
  next
    case False
    hence [simp]: "{s<..} \<union> {..<r} = UNIV" and [simp]: "{r<..s} = {}" using False by force+
    have "F constant_on ({s<..} \<union> {..<r})" using assms constant_on_Un False by force
    hence [simp]: "F constant_on UNIV" by simp
    hence [simp]: "isCont F r"
      by (metis (no_types, lifting) ext UNIV_I constant_on_def continuous_const)
    have "(\<integral>\<^sup>+x. g x \<partial>?IMF) = 0"
      by (rewrite nn_integral_interval_measure_cong[where G="\<lambda>_.0"];
          simp add: fun_diff_def interval_measure_const_null mono_on_const assms)
    also have "\<dots> = (\<integral>\<^sup>+x\<in>{r..s}. g x \<partial>?IMF)"
      by (rewrite Icc_Cont_nn_integral_interval_measure_cong[where G="\<lambda>_.0"];
          simp add: assms fun_diff_def interval_measure_const_null mono_on_const)
    finally show ?thesis .
  qed
qed

lemma nn_integral_interval_measure_Ioc:
  fixes F :: "real \<Rightarrow> real" and  g :: "real \<Rightarrow> ennreal" and r s :: real
  assumes "mono F" "\<And>x. continuous (at_right x) F" "g \<in> borel_measurable borel" and
    "F constant_on {..<r}" "F constant_on {s<..}" "isCont F r"f
  shows "(\<integral>\<^sup>+x. g x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{r<..s}. g x \<partial>(interval_measure F))"
proof -
  let ?IMF = "interval_measure F"
  show ?thesis
  proof (cases \<open>r \<le> s\<close>)
    case True
    hence [simp]: "insert r {r<..s} = {r..s}" by force
    have "(\<integral>\<^sup>+x. g x \<partial>?IMF) = (\<integral>\<^sup>+x\<in>{r..s}. g x \<partial>?IMF)"
      by (rule nn_integral_interval_measure_Icc; simp add: assms)
    also have "\<dots> = (\<integral>\<^sup>+x\<in>{r}. g x \<partial>?IMF) + (\<integral>\<^sup>+x\<in>{r<..s}. g x \<partial>?IMF)"
      using assms by (rewrite nn_integral_disjoint_pair[THEN sym]; simp)
    also have "\<dots> = (\<integral>\<^sup>+x\<in>{r<..s}. g x \<partial>?IMF)"
      using assms interval_measure_singleton_continuous by simp
    finally show ?thesis .
  next
    case False
    hence "F constant_on ({s<..} \<union> {..<r})" by (intro constant_on_Un; simp add: assms)
    moreover have "{s<..} \<union> {..<r} = UNIV" using False by force
    ultimately have [simp]: "F constant_on UNIV" by simp
    hence [simp]: "F constant_on {r<..s}" using constant_on_subset by blast
    have "(\<integral>\<^sup>+x. g x \<partial>?IMF) = 0"
      by (rewrite nn_integral_interval_measure_cong[where G="\<lambda>_.0"];
          simp add: fun_diff_def interval_measure_const_null mono_on_const assms)
    also have "\<dots> = (\<integral>\<^sup>+x\<in>{r<..s}. g x \<partial>?IMF)"
      by (rewrite Ioc_nn_integral_interval_measure_cong[where G="\<lambda>_.0"];
          simp add: assms fun_diff_def interval_measure_const_null mono_on_const)
    finally show ?thesis .
  qed
qed

lemma nn_integral_interval_measure_Ico:
  fixes F :: "real \<Rightarrow> real" and  g :: "real \<Rightarrow> ennreal" and r s :: real
  assumes "mono F" "\<And>x. continuous (at_right x) F" "g \<in> borel_measurable borel"
    "F constant_on {..<r}" "F constant_on {s<..}" "isCont F s"
  shows "(\<integral>\<^sup>+x. g x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{r..<s}. g x \<partial>(interval_measure F))"
proof -
  let ?IMF = "interval_measure F"
  show ?thesis
  proof (cases \<open>r \<le> s\<close>)
    case True
    hence [simp]: "insert s {r..<s} = {r..s}" by force
    have "(\<integral>\<^sup>+x. g x \<partial>?IMF) = (\<integral>\<^sup>+x\<in>{r..s}. g x \<partial>?IMF)"
      by (rule nn_integral_interval_measure_Icc; simp add: assms)
    also have "\<dots> = (\<integral>\<^sup>+x\<in>{r..<s}. g x \<partial>?IMF) + (\<integral>\<^sup>+x\<in>{s}. g x \<partial>?IMF)"
      using assms by (rewrite nn_integral_disjoint_pair[THEN sym]; simp)
    also have "\<dots> = (\<integral>\<^sup>+x\<in>{r..<s}. g x \<partial>?IMF)"
      using interval_measure_singleton_continuous assms by simp
    finally show ?thesis .
  next
    case False
    hence "F constant_on ({s<..} \<union> {..<r})" by (intro constant_on_Un; simp add: assms)
    moreover have "{s<..} \<union> {..<r} = UNIV" using False by force
    ultimately have [simp]: "F constant_on UNIV" by simp
    hence [simp]: "isCont F r"
      by (metis (no_types, lifting) ext UNIV_I constant_on_def continuous_const)
    have [simp]: "F constant_on {r<..<s}" using constant_on_subset[of F UNIV] by simp
    have "(\<integral>\<^sup>+x. g x \<partial>?IMF) = 0"
      by (rewrite nn_integral_interval_measure_cong[where G="\<lambda>_.0"];
          simp add: fun_diff_def interval_measure_const_null mono_on_const assms)
    also have "\<dots> = (\<integral>\<^sup>+x\<in>{r..<s}. g x \<partial>?IMF)"
      by (rewrite Ico_Cont_nn_integral_interval_measure_cong[where G="\<lambda>_.0"];
          simp add: assms fun_diff_def interval_measure_const_null mono_on_const)
    finally show ?thesis .
  qed
qed

lemma nn_integral_interval_measure_Ioo:
  fixes F :: "real \<Rightarrow> real" and  g :: "real \<Rightarrow> ennreal" and r s :: real
  assumes "mono F" "\<And>x. continuous (at_right x) F" "g \<in> borel_measurable borel" and
    "F constant_on {..<r}" "F constant_on {s<..}" "isCont F r" "isCont F s"
  shows "(\<integral>\<^sup>+x. g x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{r<..<s}. g x \<partial>(interval_measure F))"
proof -
  let ?IMF = "interval_measure F"
  show ?thesis
  proof (cases \<open>r < s\<close>)
    case True
    hence [simp]: "insert r {r<..<s} = {r..<s}" using assms by force
    have "(\<integral>\<^sup>+x. g x \<partial>?IMF) = (\<integral>\<^sup>+x\<in>{r..<s}. g x \<partial>?IMF)"
      using assms by (intro nn_integral_interval_measure_Ico; simp)
    also have "\<dots> = (\<integral>\<^sup>+x\<in>{r}. g x \<partial>?IMF) + (\<integral>\<^sup>+x\<in>{r<..<s}. g x \<partial>?IMF)"
      using assms by (rewrite nn_integral_disjoint_pair[THEN sym]; simp)
    also have "\<dots> = (\<integral>\<^sup>+x\<in>{r<..<s}. g x \<partial>?IMF)"
      using assms interval_measure_singleton_continuous by simp
    finally show ?thesis .
  next
    case False
    hence "{..r} \<inter> {s..} \<noteq> {}" by auto
    moreover have "F constant_on {..r}"
    proof -
      from assms obtain y where Fy: "\<And>x. x \<in> {..<r} \<Longrightarrow> F x = y" unfolding constant_on_def by blast
      have "(F \<longlongrightarrow> F r) (at_left r)" using assms continuous_within filterlim_at_split by blast
      hence "((\<lambda>_. y) \<longlongrightarrow> F r) (at_left r)"
        by (rewrite tendsto_cong; simp add: eventually_at_left_field lt_ex Fy)
      moreover have "((\<lambda>_. y) \<longlongrightarrow> y) (at_left r)" by (rule tendsto_const)
      ultimately have "F r = y" by (intro tendsto_unique; auto)
      with assms show ?thesis
        unfolding constant_on_def using Fy less_eq_real_def by (intro exI[of _ y]) auto
    qed
    moreover have "F constant_on {s..}"
    proof -
      from assms obtain y where Fy: "\<And>x. x \<in> {s<..} \<Longrightarrow> F x = y" unfolding constant_on_def by blast
      have "(F \<longlongrightarrow> F s) (at_right s)" using assms continuous_within filterlim_at_split by blast
      hence "((\<lambda>_. y) \<longlongrightarrow> F s) (at_right s)"
        by (rewrite tendsto_cong; simp add: eventually_at_right_field gt_ex Fy)
      moreover have "((\<lambda>_. y) \<longlongrightarrow> y) (at_right r)" by (rule tendsto_const)
      ultimately have "F s = y" by (intro tendsto_unique; auto)
      with assms show ?thesis
        unfolding constant_on_def using Fy less_eq_real_def by (intro exI[of _ y]) auto
    qed
    ultimately have "F constant_on {..r} \<union> {s..}" by (intro constant_on_Un; simp)
    moreover have "{..r} \<union> {s..} = UNIV" using False by auto
    ultimately have [simp]: "F constant_on UNIV" by simp
    hence [simp]: "F constant_on {r<..<s}" using constant_on_subset by blast
    hence "(\<integral>\<^sup>+t. g t \<partial>?IMF) = 0"
      by (rewrite nn_integral_interval_measure_cong[where G="\<lambda>_.0"];
          simp add: fun_diff_def interval_measure_const_null mono_on_const assms)
    also have "\<dots> = (\<integral>\<^sup>+t\<in>{r<..<s}. g t \<partial>?IMF)"
      by (rewrite Ioo_nn_integral_interval_measure_cong[where G="\<lambda>_.0"];
          simp add: assms fun_diff_def interval_measure_const_null mono_on_const)
    finally show ?thesis .
  qed
qed

subsection \<open>Calculation by the Derivative\<close>

proposition set_nn_integral_interval_measure_deriv:
  fixes F :: "real \<Rightarrow> real" and g :: "real \<Rightarrow> ennreal" and a b :: ereal and A :: "real set"
  assumes "mono F" "\<And>x. continuous (at_right x) F" "F differentiable_on (einterval a b)" and
    g_msr: "g \<in> borel_measurable lborel" and
    "A \<in> sets borel" "A \<subseteq> einterval a b"
  shows "(\<integral>\<^sup>+x\<in>A. g x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>A. g x * deriv F x \<partial>lborel)"
proof -

  let ?Iab = "einterval a b"
  let ?IM = interval_measure

  wlog "A = ?Iab" generalizing A g keeping g_msr
  proof -
    from assms have "indicator A \<in> borel_measurable lborel" by measurable
    with assms have gA_msr: "(\<lambda>x. g x * indicator A x) \<in> borel_measurable lborel" by measurable
    have "(\<integral>\<^sup>+x\<in>A. g x \<partial>(?IM F)) = (\<integral>\<^sup>+x\<in>?Iab. g x * indicator A x \<partial>(?IM F))"
      using assms by (simp add: mult_ac mult_indicator_subset)
    also have "\<dots> = (\<integral>\<^sup>+x\<in>?Iab. g x * indicator A x * deriv F x \<partial>lborel)"
      using hypothesis gA_msr by simp
    also have "\<dots> = (\<integral>\<^sup>+x\<in>?Iab. g x * deriv F x * indicator A x \<partial>lborel)"
      using mult.commute mult.assoc by (metis (no_types, lifting))
    also have "\<dots> = (\<integral>\<^sup>+x\<in>A. g x * deriv F x \<partial>lborel)" 
      using assms by (simp add: mult.assoc mult_indicator_subset)
    finally show ?thesis .
  qed

  hence A_I: "A = ?Iab" by simp
  thus ?thesis
  proof (cases \<open>a < b\<close>)
    case True
    let ?dFIab = "\<lambda>x. deriv F x * indicator ?Iab x"
    have dFsmsr: "set_borel_measurable borel (?Iab) (deriv F)"
      by (rule deriv_measurable_real; simp add: assms borel_measurable_mono)
    hence [measurable]: "(\<lambda>x. ennreal (?dFIab x)) \<in> borel_measurable borel"
      using assms unfolding set_borel_measurable_def by (rewrite mult.commute) simp
    have IMFst: "\<And>s t. a < ereal s \<and> s \<le> t \<and> ereal t < b \<Longrightarrow> emeasure (?IM F) {s<..t} = F t - F s"
      using assms monoD by (rewrite emeasure_interval_measure_Ioc; force)
    moreover have "\<And>s t. a < ereal s \<and> s \<le> t \<and> ereal t < b \<Longrightarrow>
      emeasure (?IM F) {s<..t} = emeasure (density lborel ?dFIab) {s<..t}"
    proof -
      fix s t :: real
      assume asm: "a < ereal s \<and> s \<le> t \<and> ereal t < b"
      hence "emeasure (?IM F) {s<..t} =  F t - F s" by (rule IMFst)
      also have "\<dots> = \<integral>\<^sup>+x. ennreal (?dFIab x) * indicator {s..t} x \<partial>lborel"
      proof -
        have [simp]: "\<And>x. x \<in> {s..t} \<Longrightarrow> x \<in> ?Iab"
          using asm einterval_iff ereal_less_le less_ereal_le by force
        hence [simp]: "\<And>x. s \<le> x \<and> x \<le> t \<Longrightarrow> F differentiable at x within ?Iab"
          by (intro differentiable_onD; simp add: assms)
        have "\<And>x. x \<in> {s..t} \<Longrightarrow> DERIV F x :> deriv F x"
          apply (rewrite DERIV_deriv_iff_real_differentiable)
          by (rewrite at_within_open[where S="?Iab", THEN sym]; simp)
        moreover hence "\<And>x. x \<in> {s..t} \<Longrightarrow> 0 \<le> deriv F x"
          using assms mono_imp_mono_on mono_on_imp_deriv_nonneg by (metis UNIV_I interior_UNIV)
        moreover have "(\<lambda>x. deriv F x * indicator ?Iab x) \<in> borel_measurable borel"
          using dFsmsr unfolding set_borel_measurable_def by (simp add: mult.commute)
        ultimately show ?thesis by (rewrite nn_integral_FTC_Icc; simp add: asm)
      qed
      also have "\<dots> = \<integral>\<^sup>+x. ennreal (?dFIab x) * indicator {s<..t} x \<partial>lborel"
      proof -
        have "sym_diff {s..t} {s<..t} = {s}" using asm by force
        thus ?thesis by (intro nn_integral_null_delta) auto
      qed
      also have "\<dots> = emeasure (density lborel ?dFIab) {s<..t}"
        by (rewrite emeasure_density; simp add: assms True)
      finally show "emeasure (?IM F) {s<..t} = emeasure (density lborel ?dFIab) {s<..t}" .
    qed
    ultimately have IMdsty:
      "restrict_space (?IM F) ?Iab = restrict_space (density lborel ?dFIab) ?Iab"
      by (intro measure_einterval_eqI_Ioc; simp)
    show ?thesis
    proof -
      have "(\<integral>\<^sup>+x\<in>?Iab. g x \<partial>(?IM F)) = (\<integral>\<^sup>+x. g x \<partial>(restrict_space (?IM F) ?Iab))"
        by (rewrite nn_integral_restrict_space[THEN sym]; simp)
      also have "\<dots> = (\<integral>\<^sup>+x. g x \<partial>(restrict_space (density lborel ?dFIab) ?Iab))"
        using IMdsty by simp
      also have "\<dots> = (\<integral>\<^sup>+x. g x * indicator ?Iab x \<partial>(density lborel ?dFIab))"
        by (rewrite nn_integral_restrict_space; simp)
      also have "\<dots> =
        (\<integral>\<^sup>+x. ennreal (deriv F x * indicator ?Iab x) * (g x * indicator ?Iab x) \<partial>lborel)"
        using g_msr by (rewrite nn_integral_density; simp)
      also have "\<dots> = (\<integral>\<^sup>+x\<in>?Iab. g x * ennreal (deriv F x) \<partial>lborel)"
        by (rule nn_integral_cong) (simp add: mult.left_commute indicator_times_eq_if)
      finally show ?thesis using A_I by simp
  qed
  next
    case False
    hence "einterval a b = {}" using einterval_empty by simp
    hence "A = {}" using assms A_I by simp
    thus ?thesis by simp
  qed

qed

corollary nn_integral_interval_measure_deriv:
  fixes F :: "real \<Rightarrow> real" and g :: "real \<Rightarrow> ennreal"
  assumes "mono F" "\<And>x. continuous (at_right x) F" "F differentiable_on UNIV" and
    "g \<in> borel_measurable lborel"
  shows "(\<integral>\<^sup>+x. g x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x. g x * deriv F x \<partial>lborel)"
  using set_nn_integral_interval_measure_deriv einterval_eq_UNIV indicator_UNIV assms
  by (metis (mono_tags, lifting) mult.right_neutral nn_integral_cong
      space_in_borel verit_eq_simplify(6))

corollary Ioi_nn_integral_interval_measure_deriv:
  fixes F :: "real \<Rightarrow> real" and g :: "real \<Rightarrow> ennreal" and r::real
  assumes "mono F" "\<And>x. continuous (at_right x) F" "F differentiable_on {r<..}" and
    "g \<in> borel_measurable lborel"
  shows "(\<integral>\<^sup>+x\<in>{r<..}. g x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{r<..}. g x * deriv F x \<partial>lborel)"
proof -
  let ?I = einterval
  let ?IMF = "interval_measure F"
  have "(\<integral>\<^sup>+x\<in>{r<..}. g x \<partial>?IMF) = (\<integral>\<^sup>+x\<in>(?I (ereal r) \<infinity>). g x \<partial>?IMF)" by simp
  also have "\<dots> = (\<integral>\<^sup>+x\<in>(?I (ereal r) \<infinity>). g x * ennreal (deriv F x) \<partial>lborel)"
    using assms by (rewrite set_nn_integral_interval_measure_deriv[of _ "ereal r" \<infinity>]; simp)
  also have "\<dots> = (\<integral>\<^sup>+x\<in>{r<..}. g x * ennreal (deriv F x) \<partial>lborel)" by simp
  finally show ?thesis .
qed

corollary Iio_nn_integral_interval_measure_deriv:
  fixes F :: "real \<Rightarrow> real" and g :: "real \<Rightarrow> ennreal" and s::real
  assumes "mono F" "\<And>x. continuous (at_right x) F" "F differentiable_on {..<s}" and
    "g \<in> borel_measurable lborel"
  shows "(\<integral>\<^sup>+x\<in>{..<s}. g x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{..<s}. g x * deriv F x \<partial>lborel)"
proof -
  let ?I = einterval
  let ?IMF = "interval_measure F"
  have "(\<integral>\<^sup>+x\<in>{..<s}. g x \<partial>?IMF) = (\<integral>\<^sup>+x\<in>(?I (-\<infinity>) (ereal s)). g x \<partial>?IMF)" by simp
  also have "\<dots> = (\<integral>\<^sup>+x\<in>(?I (-\<infinity>) (ereal s)). g x * ennreal (deriv F x) \<partial>lborel)"
    using assms by (rewrite set_nn_integral_interval_measure_deriv[of _ "-\<infinity>" "ereal s"]; simp)
  also have "\<dots> = (\<integral>\<^sup>+x\<in>{..<s}. g x * deriv F x \<partial>lborel)" by simp
  finally show ?thesis .
qed

corollary Ioo_nn_integral_interval_measure_deriv:
  fixes F :: "real \<Rightarrow> real" and g :: "real \<Rightarrow> ennreal" and r s :: real
  assumes "mono F" "\<And>x. continuous (at_right x) F" "F differentiable_on {r<..<s}" and
    "g \<in> borel_measurable lborel"
  shows "(\<integral>\<^sup>+x\<in>{r<..<s}. g x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{r<..<s}. g x * deriv F x \<partial>lborel)"
proof -
  let ?I = einterval
  let ?IMF = "interval_measure F"
  have "(\<integral>\<^sup>+x\<in>{r<..<s}. g x \<partial>?IMF) = (\<integral>\<^sup>+x\<in>(?I (ereal r) (ereal s)). g x \<partial>?IMF)" by simp
  also have "\<dots> = (\<integral>\<^sup>+x\<in>(?I (ereal r) (ereal s)). g x * ennreal (deriv F x) \<partial>lborel)"
    using assms by (rewrite set_nn_integral_interval_measure_deriv[of _ "ereal r" "ereal s"]; simp)
  also have "\<dots> = (\<integral>\<^sup>+x\<in>{r<..<s}. g x * deriv F x \<partial>lborel)" by simp
  finally show ?thesis .
qed

lemma set_nn_integral_finite_nondifferentiable_interval_measure_deriv:
  fixes F :: "real \<Rightarrow> real" and g :: "real \<Rightarrow> ennreal" and a b :: ereal and S :: "real set"
  assumes "mono F" "\<And>x. continuous (at_right x) F" "g \<in> borel_measurable lborel" and
    cont: "continuous_on (einterval a b) F" and
    diff: "F differentiable_on einterval a b - S" and
    fin: "finite S"
  shows "(\<integral>\<^sup>+x \<in> einterval a b. g x \<partial>(interval_measure F)) =
    (\<integral>\<^sup>+x \<in> einterval a b. g x * deriv F x \<partial>lborel)"
  using fin cont diff
proof (induction S arbitrary: a b rule: finite_psubset_induct)

  let ?I = einterval
  let ?IMF = "interval_measure F"

  have [measurable]: "F \<in> borel_measurable borel"
    using assms borel_measurable_mono by blast

  case IH: (psubset S)
  thus ?case
  proof (cases S)
    case emptyI
    thus ?thesis using assms set_nn_integral_interval_measure_deriv IH by simp
  next
    case (insertI S' s)
    hence Ss: "S - {s} \<subset> S \<and> finite (S - {s})" by force+
    have [simp]: "?I a (ereal s) \<inter> ?I (ereal s) b = {}" using einterval_iff by force
    show ?thesis
    proof (cases \<open>s \<in> ?I a b\<close>)

      case True

      hence [simp]: "a < b" using einterval_iff by force
      from True have Iabs: "?I a b - {s} = ?I a (ereal s) \<union> ?I (ereal s) b"
        by (rule einterval_split)
      hence [simp]: "?I a (ereal s) \<subseteq> ?I a b" and [simp]: "?I (ereal s) b \<subseteq> ?I a b" by auto

      have "F piecewise_differentiable_on ?I a b"
        using IH unfolding differentiable_on_def piecewise_differentiable_on_def
        by (metis DiffE at_within_open finite_imp_closed open_Diff open_einterval)
      hence [measurable]: "set_borel_measurable borel (?I a b) (deriv F)"
        by (rule piecewise_differentiable_on_deriv_measurable_real; simp add: assms)
      hence [measurable]: "\<And>A. A \<subseteq> ?I a b \<Longrightarrow> A \<in> sets borel \<Longrightarrow>
        (\<lambda>x. g x * ennreal (deriv F x) * indicator A x) \<in> borel_measurable borel"
      proof -
        fix A assume "A \<subseteq> ?I a b" and "A \<in> sets borel"
        hence "set_borel_measurable borel A (deriv F)"
          using set_borel_measurable_subset[of _ "?I a b" _ A] by measurable
        hence "(\<lambda>x. ennreal (deriv F x) * indicator A x) \<in> borel_measurable borel"
          apply (rewrite mult.commute, rewrite indicator_mult_ennreal)
          unfolding set_borel_measurable_def by simp
        thus "(\<lambda>x. g x * ennreal (deriv F x) * indicator A x) \<in> borel_measurable borel"
          using assms measurable_lborel1 by (rewrite mult.assoc; simp)
      qed

      let ?Sl = "S \<inter> ?I a (ereal s)"
      have "?Sl \<subset> S \<and> finite ?Sl" using Ss einterval_iff by force+
      moreover have "continuous_on (?I a (ereal s)) F"
        using IH True
        by (smt (verit) at_within_open order.strict_trans
            continuous_on_eq_continuous_within einterval_iff open_einterval)
      moreover have "F differentiable_on ?I a (ereal s) - ?Sl"
        apply (rule differentiable_on_subset[of _ "?I a b - S"], simp add: IH)
        using True einterval_iff ereal_less_le by fastforce
      ultimately have
        Il: "(\<integral>\<^sup>+x \<in> ?I a (ereal s). g x \<partial>?IMF) =
          (\<integral>\<^sup>+x \<in> ?I a (ereal s). g x * ennreal (deriv F x) \<partial>lborel)"
        using IH assms by simp

      let ?Sr = "S \<inter> ?I (ereal s) b"
      have "?Sr \<subset> S \<and> finite ?Sr" using Ss einterval_iff by force+
      moreover have "continuous_on (?I (ereal s) b) F" using IH True
        by (smt (verit) at_within_open order.strict_trans
            continuous_on_eq_continuous_within einterval_iff open_einterval)
      moreover have "F differentiable_on ?I (ereal s) b - ?Sr"
        apply (rule differentiable_on_subset[of _ "?I a b - S"], simp add: IH)
        using True einterval_iff order.strict_trans by fastforce
      ultimately have
        Ir: "(\<integral>\<^sup>+x \<in> ?I (ereal s) b. g x \<partial>?IMF) =
          (\<integral>\<^sup>+x \<in> ?I (ereal s) b. g x * ennreal (deriv F x) \<partial>lborel)"
        using IH assms by simp

      have "isCont F s"
        using True IH by (metis at_within_open continuous_on_eq_continuous_within open_einterval)
      hence "emeasure ?IMF {s} = ennreal (deriv F s) * emeasure lborel {s}"
        using assms by (rewrite interval_measure_singleton_continuous; simp)
      hence Is: "(\<integral>\<^sup>+x\<in>{s}. g x \<partial>?IMF) = (\<integral>\<^sup>+x\<in>{s}. g x * deriv F x \<partial>lborel)"
        by (rewrite nn_integral_indicator_singleton; simp)

      show ?thesis
      proof -
        have [simp]: "insert s (?I a b) = ?I a b" using insert_absorb True by force
        have "(\<integral>\<^sup>+x \<in> ?I a b. g x \<partial>?IMF) = (\<integral>\<^sup>+x \<in> ?I a b - {s}. g x \<partial>?IMF) + (\<integral>\<^sup>+x\<in>{s}. g x \<partial>?IMF)"
          using True assms by (rewrite nn_integral_disjoint_pair[THEN sym]; simp)
        also have "\<dots> = (\<integral>\<^sup>+x \<in> ?I a (ereal s). g x \<partial>?IMF) +
          (\<integral>\<^sup>+x \<in> ?I (ereal s) b. g x \<partial>?IMF) + (\<integral>\<^sup>+x\<in>{s}. g x \<partial>?IMF)"
          using True assms Iabs by (rewrite in "\<hole> + _" nn_integral_disjoint_pair[THEN sym]; simp)
        also have "\<dots> = (\<integral>\<^sup>+x \<in> ?I a (ereal s). g x * ennreal (deriv F x) \<partial>lborel) +
          (\<integral>\<^sup>+x \<in> ?I (ereal s) b. g x * ennreal (deriv F x) \<partial>lborel) +
          (\<integral>\<^sup>+x\<in>{s}. g x * ennreal (deriv F x) \<partial>lborel)"
          using Il Ir Is by simp
        also have "\<dots> = (\<integral>\<^sup>+x \<in> ?I a b - {s}. g x * ennreal (deriv F x) \<partial>lborel) +
          (\<integral>\<^sup>+x\<in>{s}. g x * ennreal (deriv F x) \<partial>lborel)"
          by (rewrite nn_integral_disjoint_pair2[THEN sym]; simp add: Iabs)
        also have "\<dots> = (\<integral>\<^sup>+x \<in> ?I a b. g x * ennreal (deriv F x) \<partial>lborel)"
          by (rewrite nn_integral_disjoint_pair2[THEN sym]; simp add: True)
        finally show ?thesis .
      qed

    next

      case False
      hence "?I a b - S = ?I a b - (S - {s})" by blast
      with IH have "F differentiable_on ?I a b - (S - {s})" by simp
      then show ?thesis using assms IH Ss by simp

    qed
  qed
qed

proposition set_nn_integral_piecewise_differentiable_interval_measure_deriv:
  fixes F :: "real \<Rightarrow> real" and g :: "real \<Rightarrow> ennreal" and a b :: ereal
  assumes "mono F" "\<And>x. continuous (at_right x) F" "F piecewise_differentiable_on (einterval a b)"
    "g \<in> borel_measurable lborel"
  shows "(\<integral>\<^sup>+x \<in> einterval a b. g x \<partial>(interval_measure F)) =
    (\<integral>\<^sup>+x \<in> einterval a b. g x * deriv F x \<partial>lborel)"
proof -
  let ?Iab = "einterval a b"
  from assms have "continuous_on ?Iab F" by (intro piecewise_differentiable_on_imp_continuous_on)
  moreover from assms obtain S where "finite S" and "\<And>x. x \<in> ?Iab - S \<Longrightarrow> F differentiable (at x)"
    unfolding piecewise_differentiable_on_def by (metis DiffE at_within_open open_einterval)
  moreover hence "F differentiable_on ?Iab - S"
    using differentiable_at_imp_differentiable_on by blast
  ultimately show ?thesis
    using assms by (intro set_nn_integral_finite_nondifferentiable_interval_measure_deriv) simp
qed

corollary nn_integral_piecewise_differentiable_interval_measure_deriv:
  fixes F :: "real \<Rightarrow> real" and g :: "real \<Rightarrow> ennreal"
  assumes "mono F" "\<And>x. continuous (at_right x) F" "F piecewise_differentiable_on UNIV"
    "g \<in> borel_measurable lborel"
  shows "(\<integral>\<^sup>+x. g x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x. g x * deriv F x \<partial>lborel)"
  using set_nn_integral_piecewise_differentiable_interval_measure_deriv
    einterval_eq_UNIV indicator_UNIV assms
  by (metis (mono_tags, lifting) mult.right_neutral nn_integral_cong)

corollary Ioi_nn_integral_piecewise_differentiable_interval_measure_deriv:
  fixes F :: "real \<Rightarrow> real" and g :: "real \<Rightarrow> ennreal" and r::real
  assumes "mono F" "\<And>x. continuous (at_right x) F" "F piecewise_differentiable_on {r<..}"
    "g \<in> borel_measurable lborel"
  shows "(\<integral>\<^sup>+x\<in>{r<..}. g x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{r<..}. g x * deriv F x \<partial>lborel)"
  using set_nn_integral_piecewise_differentiable_interval_measure_deriv assms
  by (metis (mono_tags, lifting) einterval_eq_Ici nn_integral_cong)

corollary Iio_nn_integral_piecewise_differentiable_interval_measure_deriv:
  fixes F :: "real \<Rightarrow> real" and g :: "real \<Rightarrow> ennreal" and s::real
  assumes "mono F" "\<And>x. continuous (at_right x) F" "F piecewise_differentiable_on {..<s}"
    "g \<in> borel_measurable lborel"
  shows "(\<integral>\<^sup>+x\<in>{..<s}. g x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{..<s}. g x * deriv F x \<partial>lborel)"
  using set_nn_integral_piecewise_differentiable_interval_measure_deriv assms
  by (metis (mono_tags, lifting) einterval_eq_Iic nn_integral_cong)

corollary Ioo_nn_integral_piecewise_differentiable_interval_measure_deriv:
  fixes F :: "real \<Rightarrow> real" and g :: "real \<Rightarrow> ennreal" and r s :: real
  assumes "mono F" "\<And>x. continuous (at_right x) F" "F piecewise_differentiable_on {r<..<s}"
    "g \<in> borel_measurable lborel"
  shows "(\<integral>\<^sup>+x\<in>{r<..<s}. g x \<partial>(interval_measure F)) = (\<integral>\<^sup>+x\<in>{r<..<s}. g x * deriv F x \<partial>lborel)"
  using set_nn_integral_piecewise_differentiable_interval_measure_deriv assms
  by (metis (mono_tags, lifting) einterval_eq_Icc nn_integral_cong)

end
