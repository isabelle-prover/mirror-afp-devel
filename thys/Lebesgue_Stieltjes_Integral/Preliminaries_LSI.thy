theory Preliminaries_LSI
  imports "HOL-Library.Rewrite" "HOL-Analysis.Analysis"
begin

context order_topology
begin

lemma
  assumes "a < b" 
  shows at_within_Ioo_at_right: "at a within {a<..<b} = at_right a" and
    at_within_Ioo_at_left: "at b within {a<..<b} = at_left b"
    using assms at_within_nhd
    apply (metis inf.right_idem open_lessThan greaterThanLessThan_eq lessThan_iff)
  using assms at_within_nhd
  by (smt (verit, ccfv_SIG) inf.idem inf_aci
      greaterThanLessThan_def greaterThan_iff open_greaterThan)

end

(* subsubsection \<open>Intersection\<close> in Set_Interval.thy *)
lemma Int_atLeastAtMost_Unbounded[simp]: "{a..} Int {..b} = {a..b}"
  by auto

lemma Int_greaterThanAtMost_Unbounded[simp]: "{a<..} Int {..b} = {a<..b}"
  by auto

lemma Int_atLeastLessThan_Unbounded[simp]: "{a..} Int {..<b} = {a..<b}"
  by auto

lemma Int_greaterThanLessThan_Unbounded[simp]: "{a<..} Int {..<b} = {a<..<b}"
  by auto

(* supplementary lemmas in Abstract_Topology_2.thy *)

lemma constant_on_empty[simp]: "f constant_on {}"
  by (simp add: constant_on_def)

lemma constant_on_Un:
  assumes "f constant_on A" "f constant_on B" "A \<inter> B \<noteq> {}"
  shows "f constant_on A \<union> B"
proof -
  from assms obtain c where "c \<in> A \<inter> B" by auto
  with assms have "\<And>x. x \<in> A \<union> B \<Longrightarrow> f x = f c" unfolding constant_on_def by auto
  thus ?thesis unfolding constant_on_def by simp
qed

(* analogue for lemma differentiable_transform_within *)
lemma differentiable_transform_open:
  assumes "f differentiable (at x)"
    and "x \<in> s"
    and "open s"
    and "\<And>x'. x'\<in>s \<Longrightarrow> f x' = g x'"
  shows "g differentiable (at x)"
  using assms has_derivative_transform_within_open at_within_open unfolding differentiable_def
  by blast

lemma differentiable_eq_field_differentiable_real:
  fixes f :: "real \<Rightarrow> real"
  shows "f differentiable F \<longleftrightarrow> f field_differentiable F"
  unfolding field_differentiable_def differentiable_def has_real_derivative
  using has_real_derivative_iff by presburger

lemma differentiable_on_eq_field_differentiable_real:
  fixes f :: "real \<Rightarrow> real"
  shows "f differentiable_on s \<longleftrightarrow> (\<forall>x\<in>s. f field_differentiable (at x within s))"
  unfolding differentiable_on_def using differentiable_eq_field_differentiable_real by simp

lemma set_borel_measurable_UNIV[simp]:
  fixes f :: "'a :: real_vector \<Rightarrow> real"
  shows "set_borel_measurable M UNIV f \<longleftrightarrow> f \<in> borel_measurable M"
  unfolding set_borel_measurable_def by simp

lemma deriv_measurable_real:
  fixes f :: "real \<Rightarrow> real"
  assumes "f differentiable_on S" "open S" "f \<in> borel_measurable borel"
  shows "set_borel_measurable borel S (deriv f)"
proof -
  have "\<And>x. x \<in> S \<Longrightarrow> deriv f x = lim (\<lambda>i. (f (x + 1 / Suc i) - f x) / (1 / Suc i))"
  proof -
    fix x assume x_S: "x \<in> S"
    hence "f field_differentiable (at x within S)"
      using differentiable_on_eq_field_differentiable_real assms by simp
    hence "(f has_field_derivative deriv f x) (at x)"
      using assms DERIV_deriv_iff_field_differentiable x_S at_within_open by force
    hence "(\<lambda>h. (f (x+h) - f x) / h) \<midarrow>0\<rightarrow> deriv f x" using DERIV_def by auto
    hence "\<forall>d. (\<forall>i. d i \<in> UNIV-{0::real}) \<longrightarrow> d \<longlonglongrightarrow> 0 \<longrightarrow>
      ((\<lambda>h. (f (x+h) - f x) / h) \<circ> d) \<longlonglongrightarrow> deriv f x"
      using tendsto_at_iff_sequentially by blast
    moreover have "\<forall>i. 1 / Suc i \<in> UNIV - {0::real}" by simp
    moreover have "(\<lambda>i. 1 / Suc i) \<longlonglongrightarrow> 0" using LIMSEQ_Suc lim_const_over_n by blast
    ultimately have "((\<lambda>h. (f (x+h) - f x) / h) \<circ> (\<lambda>i. 1 / Suc i)) \<longlonglongrightarrow> deriv f x" by auto
    thus "deriv f x = lim (\<lambda>i. (f (x + 1 / Suc i) - f x) / (1 / Suc i))"
      unfolding comp_def by (simp add: limI)
  qed
  moreover have "(\<lambda>x. indicator S x * lim (\<lambda>i. (f (x + 1 / Suc i) - f x) / (1 / Suc i)))
    \<in> borel_measurable borel"
    using assms by (measurable, simp, measurable)
  ultimately show ?thesis
    unfolding set_borel_measurable_def real_scaleR_def
    by (smt (verit) indicator_simps measurable_cong mult_eq_0_iff)
qed

corollary deriv_measurable_real_UNIV:
  fixes f :: "real \<Rightarrow> real"
  assumes "f differentiable_on UNIV" "f \<in> borel_measurable borel"
  shows "deriv f \<in> borel_measurable borel"
  using deriv_measurable_real[where S=UNIV] assms by simp

lemma piecewise_differentiable_on_deriv_measurable_real:
  fixes f :: "real \<Rightarrow> real"
  assumes "f piecewise_differentiable_on S" "open S" "f \<in> borel_measurable borel"
  shows "set_borel_measurable borel S (deriv f)"
proof -
  from assms obtain T where fin: "finite T" and
    diff: "\<And>x. x \<in> S - T \<Longrightarrow> f differentiable at x within S"
    unfolding piecewise_differentiable_on_def by blast
  with assms have "open (S - T)" using finite_imp_closed by blast
  moreover hence "f differentiable_on (S - T)"
    unfolding differentiable_on_def using assms by (metis Diff_iff at_within_open diff)
  ultimately have "set_borel_measurable borel (S - T) (deriv f)"
    by (intro deriv_measurable_real; simp add: assms)
  thus ?thesis
    unfolding set_borel_measurable_def real_scaleR_def
    by (rule measurable_discrete_difference[where X=T])
      (simp_all add: countable_finite fin indicator_diff)

qed

corollary piecewise_differentiable_on_deriv_measurable_real_UNIV:
  fixes f :: "real \<Rightarrow> real"
  assumes "f piecewise_differentiable_on UNIV" "f \<in> borel_measurable borel"
  shows "(deriv f) \<in> borel_measurable borel"
  using piecewise_differentiable_on_deriv_measurable_real[where S=UNIV] assms by simp

lemma einterval_empty:
  fixes a b :: ereal
  assumes "a \<ge> b"
  shows "einterval a b = {}"
  using assms einterval_iff by auto

lemma einterval_split:
  fixes a b :: ereal and s::real
  assumes "s \<in> einterval a b"
  shows "einterval a b - {s} = einterval a s \<union> einterval s b"
proof
  show "einterval a b - {s} \<subseteq> einterval a (ereal s) \<union> einterval (ereal s) b"
    using assms einterval_iff by auto
  show "einterval a (ereal s) \<union> einterval (ereal s) b \<subseteq> einterval a b - {s}"
    using assms einterval_iff
    by (smt (verit, ccfv_threshold) Diff_iff Diff_insert_absorb Un_iff
        order.strict_trans less_ereal.simps subsetI)
qed

(* analogue for lemma einterval_Icc_approximation *)
lemma einterval_Ioc_approximation:
  fixes a b :: ereal
  assumes "a < b"
  obtains u l :: "nat \<Rightarrow> real" where
    "einterval a b = (\<Union>i. {l i <.. u i})"
    "incseq u" "decseq l" "\<And>i. l i < u i" "\<And>i. a < l i" "\<And>i. u i < b"
    "l \<longlonglongrightarrow> a" "u \<longlonglongrightarrow> b"
proof -
  from assms obtain u l :: "nat \<Rightarrow> real" where
    "einterval a b = (\<Union>i. {l i .. u i})"
    "incseq u" "decseq l" "\<And>i. l i < u i" "\<And>i. a < ereal (l i)" "\<And>i. ereal (u i) < b"
    "(\<lambda>i. ereal (l i)) \<longlonglongrightarrow> a" "(\<lambda>i. ereal (u i)) \<longlonglongrightarrow> b"
    using einterval_Icc_approximation by (smt (verit) Sup.SUP_cong)
  moreover have "(\<Union>i. {l i .. u i}) = (\<Union>i. {l i <.. u i})"
  proof
    show "(\<Union>i. {l i .. u i}) \<subseteq> (\<Union>i. {l i <.. u i})"
    proof
      fix x assume "x \<in> (\<Union>i. {l i .. u i})"
      from this obtain i where xi: "x \<in> {l i .. u i}" by blast
      obtain j where "j \<ge> i" "l j < l i"
      proof (cases \<open>a = -\<infinity>\<close>)
        case True
        with \<open>(\<lambda>i. ereal (l i)) \<longlonglongrightarrow> a\<close> obtain k where "l k \<le> ereal (l i - 1)"
          using Lim_MInfty by (meson nle_le)
        hence "l k < l i" by simp
        hence "l (max i k + 1) < l i"
          using \<open>decseq l\<close> by (smt (verit, del_insts) decseq_def le_add1 max.cobounded2)
        moreover have "max i k + 1 \<ge> i" by simp
        ultimately show ?thesis using that by simp
      next
        case False
        with assms obtain ar where aar: "a = ereal ar" using less_ereal.simps by (metis ereal_cases)
        with \<open>(\<lambda>i. ereal (l i)) \<longlonglongrightarrow> a\<close> have "l \<longlonglongrightarrow> ar" by auto
        moreover have "0 < l i - ar" using \<open>\<And>i. a < ereal (l i)\<close> aar by simp
        ultimately obtain k where "\<And>h. h \<ge> k \<Longrightarrow> norm (l h - ar) < l i - ar"
          using LIMSEQ_D by blast
        hence "\<And>h. h \<ge> k \<Longrightarrow> l h < l i" by force
        hence "l (max i k + 1) < l i" by simp
        moreover have "max i k + 1 \<ge> i" by simp
        ultimately show ?thesis using that by simp
      qed
      hence "x \<in> {l j <.. u j}" using xi assms \<open>incseq u\<close> monoD by fastforce
      thus "x \<in> (\<Union>i. {l i <.. u i})" by blast
    qed
  next
    have "\<And>i. {l i <.. u i} \<subseteq> {l i .. u i}" by force
    thus "(\<Union>i. {l i <.. u i}) \<subseteq> (\<Union>i. {l i .. u i})" by blast
  qed
  ultimately show ?thesis using that by simp
qed

(* Analogue for "measure_eqI_lessThan" in the "Lebesgue_Measure" Theory *)
lemma measure_eqI_Ioc:
  fixes M N :: "real measure"
  assumes sets: "sets M = sets borel" "sets N = sets borel"
  assumes fin: "\<And>a b. a \<le> b \<Longrightarrow> emeasure M {a<..b} < \<infinity>"
  assumes eq: "\<And>a b. a \<le> b \<Longrightarrow> emeasure M {a<..b} = emeasure N {a<..b}"
  shows "M = N"
proof (rule measure_eqI_generator_eq_countable)
  let ?Ioc = "\<lambda>(a::real,b::real). {a<..b}" let ?E = "range ?Ioc"
  show "Int_stable ?E" using Int_stable_def Int_greaterThanAtMost by force
  show "?E \<subseteq> Pow UNIV" "sets M = sigma_sets UNIV ?E" "sets N = sigma_sets UNIV ?E"
    unfolding sets by (auto simp add: borel_sigma_sets_Ioc)
  show "\<And>I. I \<in> ?E \<Longrightarrow> emeasure M I = emeasure N I"
  proof -
    fix I assume "I \<in> ?E"
    then obtain a b where "I = {a<..b}" by auto
    thus "emeasure M I = emeasure N I" by (smt (verit, best) eq greaterThanAtMost_empty)
  qed
  show "?Ioc ` (Rats \<times> Rats) \<subseteq> ?E" "(\<Union>i\<in>(Rats\<times>Rats). ?Ioc i) = UNIV"
    using Rats_no_bot_less Rats_no_top_le by auto
  show "countable (?Ioc ` (Rats \<times> Rats))" using countable_rat by blast
  show "\<And>I. I \<in> ?Ioc ` (Rats \<times> Rats) \<Longrightarrow> emeasure M I \<noteq> \<infinity>"
  proof -
    fix I assume "I \<in> ?Ioc ` (Rats \<times> Rats)"
    then obtain a b where "(a,b) \<in> (Rats \<times> Rats)" "I = {a<..b}" by blast
    thus "emeasure M I \<noteq> \<infinity>" by (smt (verit, best) Ioc_inj fin order.strict_implies_not_eq)
  qed
qed

lemma measure_einterval_eqI_Ioc:
  fixes M N :: "real measure" and a b :: ereal
  assumes Mborel: "sets M = sets borel" and Nborel: "sets N = sets borel" and
    "\<And>s t. a < ereal s \<and> s \<le> t \<and> ereal t < b \<Longrightarrow> emeasure M {s<..t} \<noteq> \<infinity>" and
    "\<And>s t. a < ereal s \<and> s \<le> t \<and> ereal t < b \<Longrightarrow> emeasure M {s<..t} = emeasure N {s<..t}"
  shows "restrict_space M (einterval a b) = restrict_space N (einterval a b)"
proof (cases \<open>a < b\<close>)

  case ab: True

  let ?Iab = "einterval a b"
  let ?Iocs = "{{s<..t} | s t :: real. a < ereal s \<and> s \<le> t \<and> ereal t < b}"

  have Iocs_Iab: "?Iocs \<subseteq> Pow ?Iab"
    by safe (metis einterval_iff greaterThanAtMost_iff ereal_less_le le_ereal_less less_eq_ereal_def)

  obtain u l :: "nat \<Rightarrow> real" where
    Iab_Un: "?Iab = (\<Union>i. {l i <.. u i})" and
    lu: "\<And>i. l i < u i" and al: "\<And>i. a < l i" and ub: "\<And>i. u i < b"
  using einterval_Ioc_approximation ab by (smt (verit) Inf.INF_cong)

  let ?Iocn = "\<lambda>n::nat. {l n <.. u n}"

  have Iabsigma: "\<And>L :: real measure. sets L = sets borel \<Longrightarrow>
    sets (restrict_space L ?Iab) = sigma_sets ?Iab ?Iocs"
  proof -
    fix L :: "real measure" assume asm: "sets L = sets borel"
    have "sets (restrict_space L ?Iab) = (inter ?Iab) ` sigma_sets UNIV (range (\<lambda>(s,t) \<Rightarrow> {s<..t}))"
      by (rewrite sets_restrict_space, rewrite asm, rewrite borel_sigma_sets_Ioc) simp
    also have "\<dots> = sigma_sets ?Iab ((inter ?Iab) ` {{s<..t} | s t. True})"
      apply (rewrite restricted_sigma)
        apply (metis Pow_UNIV borel_einterval borel_sigma_sets_Ioc sets_measure_of top_greatest)
      unfolding image_def by simp_all
    also have "\<dots> = sigma_sets ?Iab ?Iocs"
    proof
      have "(inter ?Iab) ` {{s<..t} | s t. True} \<subseteq> sigma_sets ?Iab ?Iocs"
      proof
        fix A assume "A \<in> (inter ?Iab) ` {{s<..t} | s t. True}"
        from this obtain s t where Aabst: "A = ?Iab \<inter> {s<..t}" by blast
        also have "\<dots> = (\<Union>n. {l n <.. u n} \<inter> {s<..t})" using Aabst Iab_Un UN_simps by force
        also have "\<dots> = (\<Union>n. {max (l n) s <.. min (u n) t})" by simp
        moreover have
          "\<And>n. {max (l n) s <.. min (u n) t} \<in> sigma_sets ?Iab ?Iocs"
        proof -
          fix n
          show "{max (l n) s <.. min (u n) t} \<in> sigma_sets ?Iab ?Iocs"
          proof (cases \<open>max (l n) s \<le> min (u n) t\<close>)
            case True
            moreover have "a < ereal (max (l n) s)" using al by (metis less_ereal_le max_def)
            moreover have "ereal (min (u n) t) < b" using ub by (smt (verit) ereal_less_le)
            ultimately have "{max (l n) s <.. min (u n) t} \<in> ?Iocs" by blast
            thus ?thesis ..
          next
            case False
            hence "{max (l n) s <.. min (u n) t} = {}" by auto
            thus ?thesis by (metis sigma_sets.Empty)
          qed
        qed
        ultimately show "A \<in> sigma_sets ?Iab ?Iocs" by (simp add: sigma_sets.Union)
      qed
      thus "sigma_sets ?Iab ((inter ?Iab) ` {{s<..t} | s t. True}) \<subseteq> sigma_sets ?Iab ?Iocs"
        by (rule sigma_sets_mono)
    next
      have "?Iocs \<subseteq> sigma_sets ?Iab ((inter ?Iab) ` {{s<..t} | s t. True})"
      proof
        fix A assume "A \<in> ?Iocs"
        from this obtain s t where "a < ereal s \<and> s \<le> t \<and> ereal t < b" and "A = {s<..t}" by blast
        hence "A = ?Iab \<inter> {s<..t}" using Iocs_Iab by blast
        hence "A \<in> (inter ?Iab) ` {{s<..t} | s t. True}" by auto
        thus "A \<in> sigma_sets ?Iab ((inter ?Iab) ` {{s<..t} | s t. True})" by blast
      qed
      thus "sigma_sets ?Iab ?Iocs \<subseteq> sigma_sets ?Iab ((inter ?Iab) ` {{s<..t} | s t. True})"
        by (rule sigma_sets_mono)
    qed
    finally show "sets (restrict_space L ?Iab) = sigma_sets ?Iab ?Iocs" .
  qed

  have "Int_stable ?Iocs"
  proof (rule Int_stableI)
    fix A B assume "A \<in> ?Iocs" "B \<in> ?Iocs"
    from this obtain sA tA sB tB where
      asA: "a < ereal sA" and sAtA: "sA \<le> tA" and tAb: "ereal tA < b" and "A = {sA <.. tA}" and
      asB: "a < ereal sB" and sBtB: "sB \<le> tB" and eBb: "ereal tB < b" and "B = {sB <.. tB}"
      by blast
    hence AB: "A \<inter> B = {max sA sB <.. min tA tB}" using Int_greaterThanAtMost by blast
    thus "A \<inter> B \<in> ?Iocs"
    proof (cases \<open>max sA sB \<le> min tA tB\<close>)
      case True
      moreover have "a < ereal (max sA sB)" "ereal (min tA tB) < b"
        using asA tAb asB eBb by linarith+
      ultimately show ?thesis using AB by blast
    next
      case False
      hence "A \<inter> B = {}" using AB by force
      thus "A \<inter> B \<in> ?Iocs" using asA less_ereal_le sAtA tAb by fastforce
    qed
  qed
  moreover note Iocs_Iab
  moreover have "\<And>A. A \<in> ?Iocs \<Longrightarrow>
    emeasure (restrict_space M ?Iab) A = emeasure (restrict_space N ?Iab) A"
  proof -
    fix A assume asm: "A \<in> ?Iocs"
    hence [simp]: "A \<subseteq> ?Iab" using Iocs_Iab by blast
    have "emeasure (restrict_space M ?Iab) A = emeasure M A"
      by (rewrite emeasure_restrict_space; simp add: assms)
    also have "\<dots> = emeasure N A" using assms asm by force
    also have "\<dots> = emeasure (restrict_space N ?Iab) A"
      by (rewrite emeasure_restrict_space; simp add: assms)
    finally show "emeasure (restrict_space M ?Iab) A = emeasure (restrict_space N ?Iab) A" .
  qed
  moreover have "sets (restrict_space M ?Iab) = sigma_sets ?Iab ?Iocs" using Iabsigma assms by simp
  moreover have "sets (restrict_space N ?Iab) = sigma_sets ?Iab ?Iocs" using Iabsigma assms by simp
  moreover have rngIocn: "range ?Iocn \<subseteq> ?Iocs"
    using al lu ub by (smt (verit) image_subset_iff mem_Collect_eq)
  moreover have "(\<Union>n. ?Iocn n) = ?Iab" using Iab_Un by simp
  moreover have "\<And>n. emeasure (restrict_space M ?Iab) (?Iocn n) \<noteq> \<infinity>"
  proof -
    fix n::nat
    have "{l n <.. u n} \<subseteq> ?Iab" using Iab_Un by blast
    moreover have "emeasure M {l n <.. u n} \<noteq> \<infinity>" using assms al lu ub less_imp_le by metis
    ultimately show "emeasure (restrict_space M ?Iab) (?Iocn n) \<noteq> \<infinity>"
      by (rewrite emeasure_restrict_space; simp add: assms)
  qed
  ultimately show "restrict_space M ?Iab = restrict_space N ?Iab"
    by (rule measure_eqI_generator_eq[where A="?Iocn"]; simp)

next

  case False
  hence "einterval a b = {}" using einterval_empty by simp
  thus ?thesis by (metis sets.empty_sets space_empty_eq_bot space_restrict_space2)

qed

lemma nn_integral_disjoint_pair2:
  assumes "B \<in> sets M" "C \<in> sets M" "B \<inter> C = {}" and
    [measurable]: "(\<lambda>x. f x * indicator B x) \<in> borel_measurable M" and
    [measurable]: "(\<lambda>x. f x * indicator C x) \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+x \<in> B \<union> C. f x \<partial>M) = (\<integral>\<^sup>+x \<in> B. f x \<partial>M) + (\<integral>\<^sup>+x \<in> C. f x \<partial>M)"
proof -
  have [measurable]: "(\<lambda>x. f x * indicator (B \<union> C) x) \<in> borel_measurable M"
    using assms apply (rewrite indicator_add[THEN sym], simp)
    apply (rewrite distrib_left) by simp
  have "(\<integral>\<^sup>+x \<in> B \<union> C. f x \<partial>M) = (\<integral>\<^sup>+x \<in> B \<union> C. f x * indicator (B \<union> C) x \<partial>M)"
    by (metis indicator_simps mult_1_right mult_eq_0_iff)
  also have "\<dots> = (\<integral>\<^sup>+x\<in>B. f x * indicator (B \<union> C) x \<partial>M) + (\<integral>\<^sup>+x\<in>C. f x * indicator (B \<union> C) x \<partial>M)"
    using assms by (rewrite nn_integral_disjoint_pair; simp)
  moreover have "(\<integral>\<^sup>+x\<in>B. f x * indicator (B \<union> C) x \<partial>M) = (\<integral>\<^sup>+x\<in>B. f x \<partial>M)"
    by (metis (mono_tags, lifting) indicator_inter_arith inf_sup_absorb mult.assoc mult.commute)
  moreover have "(\<integral>\<^sup>+x\<in>C. f x * indicator (B \<union> C) x \<partial>M) = (\<integral>\<^sup>+x\<in>C. f x \<partial>M)"
    by (metis (no_types, lifting) indicator_inter_arith inf_sup_absorb mult.commute
        mult.left_commute sup_commute)
  ultimately show ?thesis by simp
qed

lemma set_nn_integral_interval_measure_bounded_finite:
  fixes F :: "real \<Rightarrow> real" and h :: "real \<Rightarrow> ennreal" and A :: "real set" and M::real
  assumes "bounded A" "\<And>x. x \<in> A \<Longrightarrow> h x \<le> M" "A \<in> sets borel" and
    "mono F" "\<And>x. continuous (at_right x) F"
  shows "(\<integral>\<^sup>+x\<in>A. h x \<partial>(interval_measure F)) < \<infinity>"
proof -
  let ?IMF = "interval_measure F"
  obtain a where a_ub: "\<And>x. x \<in> A \<Longrightarrow> \<bar>x\<bar> \<le> a"
    using bounded_iff assms by force
  define c where "c \<equiv> \<bar>a\<bar> + 1"
  have [simp]: "c > 0"
    unfolding c_def by auto
  have Ac: "A \<subseteq> {-c<..c}"
    using a_ub c_def by force
  have "(\<integral>\<^sup>+x\<in>A. h x \<partial>?IMF) \<le> (\<integral>\<^sup>+x\<in>A. M \<partial>?IMF)"
    using nn_set_integral_mono assms by (simp add: indicator_def nn_integral_mono)
  also have "\<dots> \<le> (\<integral>\<^sup>+x\<in>{-c<..c}. M \<partial>?IMF)"
    using nn_set_integral_set_mono Ac by force
  also have "\<dots> = M * emeasure ?IMF {-c<..c}"
    by (rewrite nn_integral_cmult_indicator; simp)
  also have "\<dots> \<le> \<bar>M\<bar> * emeasure ?IMF {-c<..c}"
    using abs_ge_self by (simp add: mult_right_mono)
  also have "emeasure ?IMF {-c<..c} = F c - F (-c)"
    by (simp add: emeasure_interval_measure_Ioc_eq ennreal_eq_0_iff monoD assms)
  finally have "(\<integral>\<^sup>+x\<in>A. h x \<partial>?IMF) \<le> \<bar>M\<bar> * (F c - F (-c))"
    by (simp add: ennreal_mult')
  then show ?thesis
    by (simp add: le_less_trans)
qed

end
