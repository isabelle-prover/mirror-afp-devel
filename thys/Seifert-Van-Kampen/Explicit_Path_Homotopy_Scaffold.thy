theory Explicit_Path_Homotopy_Scaffold
  imports "HOL-Analysis.Homotopy"
begin

section \<open>Explicit-topology paths and homotopies\<close>

text \<open>
  HOL-Analysis already provides paths and homotopies for subsets of a type. For
  the pushout-oriented development, however, it is convenient to work directly
  with arbitrary topologies. This theory therefore rephrases the basic path and
  homotopy notions in explicit-topology form.
\<close>

definition loopin_space ::
  "'a topology \<Rightarrow> 'a \<Rightarrow> (real \<Rightarrow> 'a) set"
where
  "loopin_space X x = {p. pathin X p \<and> p 0 = x \<and> p 1 = x}"

definition homotopic_pathsin ::
  "'a topology \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "homotopic_pathsin X p q \<equiv>
     homotopic_with (\<lambda>r. r 0 = p 0 \<and> r 1 = p 1) (top_of_set {0..1}) X p q"

definition homotopic_loopsin ::
  "'a topology \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "homotopic_loopsin X p q \<equiv>
     homotopic_with (\<lambda>r. r 1 = r 0) (top_of_set {0..1}) X p q"

definition reversepathin :: "(real \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> 'a"
where
  "reversepathin p = (\<lambda>t. p (1 - t))"

definition joinpathin :: "(real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> 'a"
where
  "joinpathin p q = (\<lambda>t. if t \<le> 1 / 2 then p (2 * t) else q (2 * t - 1))"

definition subpathin :: "real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> 'a"
where
  "subpathin u v p = (\<lambda>t. p ((v - u) * t + u))"

lemma reversepathin_eq_reversepath [simp]:
  "reversepathin p = reversepath p"
  unfolding reversepathin_def reversepath_def by simp

lemma reversepathin_reversepathin [simp]:
  "reversepathin (reversepathin p) = p"
  unfolding reversepathin_def by (rule ext) simp

lemma joinpathin_eq_joinpaths [simp]:
  "joinpathin p q = p +++ q"
  unfolding joinpathin_def joinpaths_def by simp

lemma subpathin_image:
  "subpathin u v p ` {0..1} = p ` closed_segment u v"
  by (simp add: subpathin_def image_image closed_segment_real_eq algebra_simps)

lemma subpathin_image_eq:
  assumes "u \<le> v"
  shows "subpathin u v p ` {0..1} = p ` {u..v}"
  using assms by (simp add: subpathin_image closed_segment_eq_real_ivl)

lemma subpathin_0_1 [simp]:
  "subpathin 0 1 p = p"
  unfolding subpathin_def by (rule ext) simp

lemma joinpathin_subpathin_middle [simp]:
  "joinpathin (subpathin 0 (1 / 2) p) (subpathin (1 / 2) 1 p) = p"
  unfolding joinpathin_def subpathin_def
  by (rule ext) (auto simp: field_simps)

lemma continuous_map_top01_id:
  "continuous_map (top_of_set {0..1}) euclideanreal id"
  by (rule continuous_map_into_fulltopology[OF continuous_map_id])

lemma loopin_spaceI:
  assumes "pathin X p"
    and "p 0 = x"
    and "p 1 = x"
  shows "p \<in> loopin_space X x"
  using assms unfolding loopin_space_def by blast

lemma loopin_spaceE:
  assumes "p \<in> loopin_space X x"
  obtains "pathin X p" "p 0 = x" "p 1 = x"
  using assms unfolding loopin_space_def by blast

lemma constant_loopin_in_space:
  assumes "x \<in> topspace X"
  shows "(\<lambda>_. x) \<in> loopin_space X x"
  using assms unfolding loopin_space_def by auto

lemma pathin_image_subset_topspace:
  assumes "pathin X p"
  shows "p ` {0..1} \<subseteq> topspace X"
proof -
  have "p \<in> {0..1} \<rightarrow> topspace X"
    using assms by (rule path_image_subset_topspace)
  then show ?thesis
    by auto
qed

lemma pathin_reversepathin:
  assumes "pathin X p"
  shows "pathin X (reversepathin p)"
proof -
  have rev_cont: "continuous_map (top_of_set {0..1}) (top_of_set {0..1}) (\<lambda>t::real. 1 - t)"
    by (intro continuous_map_into_subtopology continuous_intros) auto
  have "continuous_map (top_of_set {0..1}) X (p \<circ> (\<lambda>t::real. 1 - t))"
    using rev_cont assms unfolding pathin_def by (rule continuous_map_compose)
  then show ?thesis
    unfolding pathin_def reversepathin_def by (simp add: o_def)
qed

lemma pathin_joinpathin:
  assumes p: "pathin X p"
    and q: "pathin X q"
    and pq: "p 1 = q 0"
  shows "pathin X (joinpathin p q)"
proof -
  let ?T01 = "subtopology euclideanreal {0..1}"
  have p_cont: "continuous_map ?T01 X p"
    using p unfolding pathin_def .
  have q_cont: "continuous_map ?T01 X q"
    using q unfolding pathin_def .
  have left_scale_eu:
    "continuous_map (subtopology ?T01 {x \<in> topspace ?T01. 2 * x \<le> 1}) euclideanreal (\<lambda>x::real. 2 * x)"
  proof -
    have "continuous_map ?T01 euclideanreal (\<lambda>x::real. 2 * x)"
      by (simp add: continuous_map_iff_continuous continuous_intros)
    then show ?thesis
      by (rule continuous_map_from_subtopology)
  qed
  have left_scale_range:
    "(\<lambda>x::real. 2 * x) \<in> topspace (subtopology ?T01 {x \<in> topspace ?T01. 2 * x \<le> 1}) \<rightarrow> {0..1}"
  proof
    fix x :: real
    assume x_in: "x \<in> topspace (subtopology ?T01 {x \<in> topspace ?T01. 2 * x \<le> 1})"
    then have x01: "x \<in> {0..1}" and x_half: "2 * x \<le> 1"
      by auto
    from x01 have x_ge0: "0 \<le> x"
      by auto
    have lower: "0 \<le> 2 * x"
      using x_ge0 by linarith
    show "2 * x \<in> {0..1}"
      using lower x_half by simp
  qed
  have left_scale_cont:
    "continuous_map (subtopology ?T01 {x \<in> topspace ?T01. 2 * x \<le> 1}) ?T01 (\<lambda>x::real. 2 * x)"
    by (rule continuous_map_into_subtopology[OF left_scale_eu left_scale_range])
  have left_cont_comp:
    "continuous_map (subtopology ?T01 {x \<in> topspace ?T01. 2 * x \<le> 1}) X
      (p \<circ> (\<lambda>x::real. 2 * x))"
    by (rule continuous_map_compose[OF left_scale_cont p_cont])
  have left_eq:
    "(p \<circ> (\<lambda>x::real. 2 * x)) = (\<lambda>x::real. p (2 * x))"
    by (auto simp: fun_eq_iff o_def)
  from left_cont_comp have left_cont:
    "continuous_map (subtopology ?T01 {x \<in> topspace ?T01. 2 * x \<le> 1}) X (\<lambda>x::real. p (2 * x))"
    by (simp only: left_eq)
  have right_shift_eu:
    "continuous_map (subtopology ?T01 {x \<in> topspace ?T01. 1 \<le> 2 * x}) euclideanreal (\<lambda>x::real. 2 * x - 1)"
  proof -
    have "continuous_map ?T01 euclideanreal (\<lambda>x::real. 2 * x - 1)"
      by (simp add: continuous_map_iff_continuous continuous_intros)
    then show ?thesis
      by (rule continuous_map_from_subtopology)
  qed
  have right_shift_range:
    "(\<lambda>x::real. 2 * x - 1) \<in> topspace (subtopology ?T01 {x \<in> topspace ?T01. 1 \<le> 2 * x}) \<rightarrow> {0..1}"
  proof
    fix x :: real
    assume x_in: "x \<in> topspace (subtopology ?T01 {x \<in> topspace ?T01. 1 \<le> 2 * x})"
    then have x01: "x \<in> {0..1}" and x_half: "1 \<le> 2 * x"
      by auto
    from x01 have x_le1: "x \<le> 1"
      by auto
    have lower: "0 \<le> 2 * x - 1"
      using x_half by linarith
    have upper: "2 * x - 1 \<le> 1"
      using x_le1 by linarith
    show "2 * x - 1 \<in> {0..1}"
      using lower upper by simp
  qed
  have right_shift_cont:
    "continuous_map (subtopology ?T01 {x \<in> topspace ?T01. 1 \<le> 2 * x}) ?T01 (\<lambda>x::real. 2 * x - 1)"
    by (rule continuous_map_into_subtopology[OF right_shift_eu right_shift_range])
  have right_cont_comp:
    "continuous_map (subtopology ?T01 {x \<in> topspace ?T01. 1 \<le> 2 * x}) X
      (q \<circ> (\<lambda>x::real. 2 * x - 1))"
    by (rule continuous_map_compose[OF right_shift_cont q_cont])
  have right_eq:
    "(q \<circ> (\<lambda>x::real. 2 * x - 1)) = (\<lambda>x::real. q (2 * x - 1))"
    by (auto simp: fun_eq_iff o_def)
  from right_cont_comp have right_cont:
    "continuous_map (subtopology ?T01 {x \<in> topspace ?T01. 1 \<le> 2 * x}) X (\<lambda>x::real. q (2 * x - 1))"
    by (simp only: right_eq)
  have cont_if:
    "continuous_map ?T01 X (\<lambda>x::real. if 2 * x \<le> 1 then p (2 * x) else q (2 * x - 1))"
  proof (rule continuous_map_cases_le[where p = "\<lambda>x::real. 2 * x" and q = "\<lambda>_. 1"])
    show "continuous_map ?T01 euclideanreal (\<lambda>x::real. 2 * x)"
      by (simp add: continuous_map_iff_continuous continuous_intros)
    show "continuous_map ?T01 euclideanreal (\<lambda>_. 1)"
      by simp
    show "continuous_map (subtopology ?T01 {x \<in> topspace ?T01. 2 * x \<le> 1}) X (\<lambda>x::real. p (2 * x))"
      by (rule left_cont)
    show "continuous_map (subtopology ?T01 {x \<in> topspace ?T01. 1 \<le> 2 * x}) X (\<lambda>x::real. q (2 * x - 1))"
      by (rule right_cont)
    show "p (2 * x) = q (2 * x - 1)"
      if "x \<in> topspace ?T01" "(\<lambda>x::real. 2 * x) x = (\<lambda>_. 1) x" for x
      using pq that by simp
  qed
  have cont_join: "continuous_map ?T01 X (joinpathin p q)"
  proof (rule continuous_map_eq[OF cont_if])
    fix x :: real
    assume x_in: "x \<in> topspace ?T01"
    show "(\<lambda>x::real. if 2 * x \<le> 1 then p (2 * x) else q (2 * x - 1)) x = joinpathin p q x"
      using x_in by (simp add: joinpathin_def field_simps)
  qed
  show ?thesis
    using cont_join unfolding pathin_def .
qed

lemma pathin_subpathin:
  assumes p: "pathin X p"
    and u: "u \<in> {0..1}"
    and v: "v \<in> {0..1}"
  shows "pathin X (subpathin u v p)"
proof -  
  have aff_cont:
    "continuous_map (top_of_set {0..1}) (top_of_set {0..1}) (\<lambda>t::real. (v - u) * t + u)"
  proof -
    have aff_cont_eu:
      "continuous_map (top_of_set {0..1}) euclideanreal (\<lambda>t::real. (v - u) * t + u)"
      by (simp add: continuous_map_iff_continuous continuous_intros)
    have aff_range:
      "(\<lambda>t::real. (v - u) * t + u) \<in> topspace (top_of_set {0..1}) \<rightarrow> {0..1}"
    proof
      fix x :: real
      assume x_in: "x \<in> topspace (top_of_set {0..1})"
      have x01: "x \<in> {0..1}"
        using x_in by simp
      have nonneg: "0 \<le> x * v + (1 - x) * u"
        using u v x01 by (intro add_nonneg_nonneg mult_nonneg_nonneg) auto
      moreover have le1: "x * v + (1 - x) * u \<le> 1"
        using u v x01 by (intro convex_bound_le) auto
      ultimately show "((v - u) * x + u) \<in> {0..1}"
        by (simp add: algebra_simps)
    qed
    show ?thesis
      using aff_cont_eu aff_range by (auto simp: continuous_map_in_subtopology)
  qed
  have "continuous_map (top_of_set {0..1}) X (p \<circ> (\<lambda>t::real. (v - u) * t + u))"
    using aff_cont p unfolding pathin_def by (rule continuous_map_compose)
  then show ?thesis
    unfolding pathin_def subpathin_def by (simp add: o_def)
qed

lemma pathin_subdivision_open_cover:
  assumes p: "pathin X p"
    and cover: "p ` {0..1} \<subseteq> \<Union>\<U>"
    and openU: "\<And>U. U \<in> \<U> \<Longrightarrow> openin X U"
  shows "\<exists>n::nat. 0 < n \<and>
      (\<forall>i<n. \<exists>U\<in>\<U>.
        subpathin (real i / real n) (real (Suc i) / real n) p ` {0..1} \<subseteq> U)"
proof -
  have U_nonempty: "\<U> \<noteq> {}"
  proof
    assume "\<U> = {}"
    moreover have "p 0 \<in> p ` {0..1}"
      by auto
    ultimately show False
      using cover by auto
  qed
  define W where
    "W U = (SOME T. open T \<and> {t \<in> {0..1}. p t \<in> U} = {0..1} \<inter> T)" for U
  have pre_open: "openin (top_of_set {0..1}) {t \<in> {0..1}. p t \<in> U}" if U_in: "U \<in> \<U>" for U
    using p openU[OF U_in]
    unfolding pathin_def continuous_map_def
    by auto
  have W_spec:
      "open (W U)"
      "{t \<in> {0..1}. p t \<in> U} = {0..1} \<inter> W U"
    if U_in: "U \<in> \<U>" for U
  proof -
    from pre_open[OF U_in] obtain T where
        T_open: "open T"
        and T_eq: "{t \<in> {0..1}. p t \<in> U} = {0..1} \<inter> T"
      by (auto simp: openin_open)
    have "open (W U) \<and> {t \<in> {0..1}. p t \<in> U} = {0..1} \<inter> W U"
      unfolding W_def
      by (rule someI_ex) (use T_open T_eq in blast)
    then show "open (W U)" "{t \<in> {0..1}. p t \<in> U} = {0..1} \<inter> W U"
      by auto
  qed
  have interval_cover: "{0..1} \<subseteq> \<Union>(W ` \<U>)"
  proof
    fix t :: real
    assume t_in: "t \<in> {0..1}"
    have "p t \<in> p ` {0..1}"
      using t_in by blast
    then obtain U where U_in: "U \<in> \<U>" and pU: "p t \<in> U"
      using cover by blast
    have "{t \<in> {0..1}. p t \<in> U} = {0..1} \<inter> W U"
      by (rule W_spec(2)[OF U_in])
    then have "t \<in> W U"
      using t_in pU by auto
    then show "t \<in> \<Union>(W ` \<U>)"
      using U_in by blast
  qed
  have open_W_image: "open B" if "B \<in> W ` \<U>" for B
  proof -
    from that obtain U where U_in: "U \<in> \<U>" and B_eq: "B = W U"
      by blast
    show "open B"
      unfolding B_eq by (rule W_spec(1)[OF U_in])
  qed
  have W_nonempty: "W ` \<U> \<noteq> {}"
    using U_nonempty by auto
  have compact01: "compact ({0..1::real})"
    by (rule compact_Icc)
  from Lebesgue_number_lemma[OF compact01 W_nonempty interval_cover open_W_image]
  obtain \<delta> where \<delta>_pos: "0 < \<delta>"
    and \<delta>_cover:
      "\<And>T. T \<subseteq> {0..1} \<Longrightarrow> diameter T < \<delta> \<Longrightarrow> \<exists>B\<in>W ` \<U>. T \<subseteq> B"
    by blast
  obtain m where m: "inverse (of_nat (Suc m)) < \<delta>"
    using reals_Archimedean[OF \<delta>_pos] by blast
  let ?n = "Suc m"
  have segment_cover:
    "\<exists>U\<in>\<U>. subpathin (real i / real ?n) (real (Suc i) / real ?n) p ` {0..1} \<subseteq> U"
    if i_lt: "i < ?n" for i
  proof -
    let ?a = "real i / real ?n"
    let ?b = "real (Suc i) / real ?n"
    let ?T = "{?a..?b}"
    have a01: "?a \<in> {0..1}"
      using i_lt by auto
    have b01: "?b \<in> {0..1}"
      using i_lt by auto
    have ab: "?a \<le> ?b"
      using i_lt by (simp add: field_simps)
    have T_subset: "?T \<subseteq> {0..1}"
      using a01 b01 by auto
    have "diameter ?T = ?b - ?a"
      using ab by simp
    also have "\<dots> = 1 / real ?n"
      by (simp add: field_simps)
    also have "\<dots> < \<delta>"
      using m by (simp add: divide_inverse)
    finally have T_small: "diameter ?T < \<delta>" .
    from \<delta>_cover[OF T_subset T_small] obtain B where
        B_in: "B \<in> W ` \<U>"
        and T_B: "?T \<subseteq> B"
      by blast
    obtain U where U_in: "U \<in> \<U>" and B_eq: "B = W U"
      using B_in by blast
    have pre_eq: "{t \<in> {0..1}. p t \<in> U} = {0..1} \<inter> W U"
      by (rule W_spec(2)[OF U_in])
    have subpath_subset: "subpathin ?a ?b p ` {0..1} \<subseteq> U"
    proof
      fix x
      assume x_in: "x \<in> subpathin ?a ?b p ` {0..1}"
      then obtain t where t_in: "t \<in> {0..1}" and x_eq: "x = subpathin ?a ?b p t"
        by blast
      have s_in_T: "((?b - ?a) * t + ?a) \<in> ?T"
      proof -
        from t_in have t_ge0: "0 \<le> t" and t_le1: "t \<le> 1"
          by auto
        have diff_nonneg: "0 \<le> ?b - ?a"
          using ab by linarith
        have term_nonneg: "0 \<le> (?b - ?a) * t"
          by (rule mult_nonneg_nonneg[OF diff_nonneg t_ge0])
        have term_le: "(?b - ?a) * t \<le> (?b - ?a) * 1"
          using t_le1 diff_nonneg by (rule mult_left_mono)
        have lower: "?a \<le> (?b - ?a) * t + ?a"
          using term_nonneg by linarith
        have upper: "(?b - ?a) * t + ?a \<le> ?b"
          using term_le by simp
        show ?thesis
          using lower upper by simp
      qed
      have s_in_unit: "((?b - ?a) * t + ?a) \<in> {0..1}"
        using s_in_T T_subset by blast
      have s_in_W: "((?b - ?a) * t + ?a) \<in> W U"
        using s_in_T T_B B_eq by auto
      have "((?b - ?a) * t + ?a) \<in> {t \<in> {0..1}. p t \<in> U}"
        using s_in_unit s_in_W pre_eq by auto
      then show "x \<in> U"
        using x_eq by (simp add: subpathin_def)
    qed
    then show ?thesis
      using U_in by blast
  qed
  show ?thesis
    by (rule exI[of _ ?n]) (use segment_cover in auto)
qed

lemma loopin_space_joinpathin:
  assumes p: "p \<in> loopin_space X x"
    and q: "q \<in> loopin_space X x"
  shows "joinpathin p q \<in> loopin_space X x"
proof -
  from p obtain p_in where p_in: "pathin X p" "p 0 = x" "p 1 = x"
    by (rule loopin_spaceE)
  from q obtain q_in where q_in: "pathin X q" "q 0 = x" "q 1 = x"
    by (rule loopin_spaceE)
  have "pathin X (joinpathin p q)"
    by (rule pathin_joinpathin[OF p_in(1) q_in(1)]) (simp add: p_in q_in)
  moreover have "joinpathin p q 0 = x" "joinpathin p q 1 = x"
    by (simp_all add: joinpathin_def p_in q_in)
  ultimately show ?thesis
    by (rule loopin_spaceI)
qed

lemma homotopic_pathsin_top_of_set [simp]:
  "homotopic_pathsin (top_of_set S) p q \<longleftrightarrow> homotopic_paths S p q"
  unfolding homotopic_pathsin_def homotopic_paths_def
  by (simp add: pathstart_def pathfinish_def)

lemma homotopic_loopsin_top_of_set [simp]:
  "homotopic_loopsin (top_of_set S) p q \<longleftrightarrow> homotopic_loops S p q"
  unfolding homotopic_loopsin_def homotopic_loops_def
  by (simp add: pathstart_def pathfinish_def)

lemma homotopic_pathsin_imp_pathin:
  assumes "homotopic_pathsin X p q"
  shows "pathin X p" "pathin X q"
  using assms unfolding homotopic_pathsin_def pathin_def
  by (auto dest: homotopic_with_imp_continuous_maps)

lemma homotopic_pathsin_imp_endpoints:
  assumes "homotopic_pathsin X p q"
  shows "q 0 = p 0" "q 1 = p 1"
  using assms unfolding homotopic_pathsin_def
  by (auto dest: homotopic_with_imp_property)

lemma homotopic_pathsin_refl [simp]:
  "homotopic_pathsin X p p \<longleftrightarrow> pathin X p"
  unfolding homotopic_pathsin_def pathin_def
  by (simp add: homotopic_with_refl)

lemma homotopic_pathsin_sym:
  assumes "homotopic_pathsin X p q"
  shows "homotopic_pathsin X q p"
proof -
  have "q 0 = p 0" "q 1 = p 1"
    using assms by (rule homotopic_pathsin_imp_endpoints)+
  with assms show ?thesis
    unfolding homotopic_pathsin_def
    by (simp add: homotopic_with_sym)
qed

lemma homotopic_pathsin_trans:
  assumes "homotopic_pathsin X p q"
    and "homotopic_pathsin X q r"
  shows "homotopic_pathsin X p r"
proof -
  have q: "q 0 = p 0" "q 1 = p 1"
    using assms(1) by (rule homotopic_pathsin_imp_endpoints)+
  have pq: "homotopic_with (\<lambda>s. s 0 = p 0 \<and> s 1 = p 1) (top_of_set {0..1}) X p q"
    using assms(1) unfolding homotopic_pathsin_def .
  have qr: "homotopic_with (\<lambda>s. s 0 = p 0 \<and> s 1 = p 1) (top_of_set {0..1}) X q r"
    using assms(2) q unfolding homotopic_pathsin_def by simp
  from pq qr show ?thesis
    unfolding homotopic_pathsin_def by (rule homotopic_with_trans)
qed

lemma homotopic_pathsin_eq:
  assumes "pathin X p"
    and "\<And>t. t \<in> {0..1} \<Longrightarrow> p t = q t"
  shows "homotopic_pathsin X p q"
proof -
  have "continuous_map (top_of_set {0..1}) X p"
    using assms(1) unfolding pathin_def by simp
  moreover have "\<forall>x\<in>topspace (top_of_set {0..1}). p x = q x"
    using assms(2) by simp
  ultimately show ?thesis
    unfolding homotopic_pathsin_def
     by (intro homotopic_with_equal) auto
qed

lemma continuous_map_homotopic_joinpathin_lemma:
  fixes p q :: "real \<Rightarrow> real \<Rightarrow> 'a"
  assumes p:
      "continuous_map (prod_topology (top_of_set {0..1}) (top_of_set {0..1})) X
        (\<lambda>y. p (fst y) (snd y))"
    and q:
      "continuous_map (prod_topology (top_of_set {0..1}) (top_of_set {0..1})) X
        (\<lambda>y. q (fst y) (snd y))"
    and pq: "\<And>t. t \<in> {0..1} \<Longrightarrow> p t 1 = q t 0"
  shows
    "continuous_map (prod_topology (top_of_set {0..1}) (top_of_set {0..1})) X
      (\<lambda>y. joinpathin (p (fst y)) (q (fst y)) (snd y))"
proof -
  let ?T01 = "subtopology euclideanreal {0..1}"
  let ?A = "prod_topology ?T01 ?T01"
  have sect:
    "(\<lambda>t. p (fst t) (2 * snd t)) = (\<lambda>y. p (fst y) (snd y)) \<circ> (\<lambda>y. (fst y, 2 * snd y))"
    "(\<lambda>t. q (fst t) (2 * snd t - 1)) = (\<lambda>y. q (fst y) (snd y)) \<circ> (\<lambda>y. (fst y, 2 * snd y - 1))"
    by force+
  show ?thesis
    unfolding joinpathin_def
  proof (rule continuous_map_cases_le)
    show "continuous_map ?A euclideanreal snd"
      by (rule continuous_map_into_fulltopology[OF continuous_map_snd])
    show "continuous_map ?A euclideanreal (\<lambda>_. 1 / 2)"
      by simp
    have left_pair_cont:
      "continuous_map (subtopology ?A {y \<in> topspace ?A. snd y \<le> 1 / 2}) ?A
        (\<lambda>t. (fst t, 2 * snd t))"
  proof (rule continuous_map_pairedI)
      show "continuous_map (subtopology ?A {y \<in> topspace ?A. snd y \<le> 1 / 2}) ?T01 fst"
        by (rule continuous_map_from_subtopology[OF continuous_map_fst])
      show "continuous_map (subtopology ?A {y \<in> topspace ?A. snd y \<le> 1 / 2}) ?T01 (\<lambda>t. 2 * snd t)"
      proof -
        have snd_cont:
          "continuous_map (subtopology ?A {y \<in> topspace ?A. snd y \<le> 1 / 2}) euclideanreal snd"
          by (rule continuous_map_into_fulltopology[OF continuous_map_subtopology_snd])
        have scale_cont:
          "continuous_map (subtopology ?A {y \<in> topspace ?A. snd y \<le> 1 / 2}) euclideanreal
            (\<lambda>t. 2 * snd t)"
          using snd_cont by (intro continuous_intros)
        have scale_range:
          "(\<lambda>t. 2 * snd t) \<in>
            topspace (subtopology ?A {y \<in> topspace ?A. snd y \<le> 1 / 2}) \<rightarrow> {0..1}"
        proof
          fix t :: "real \<times> real"
          assume t_in: "t \<in> topspace (subtopology ?A {y \<in> topspace ?A. snd y \<le> 1 / 2})"
          then have tA: "t \<in> topspace ?A" and t_half: "snd t \<le> 1 / 2"
            by auto
          have snd01: "snd t \<in> {0..1}"
            using tA by (auto simp: topspace_prod_topology)
          from snd01 have snd_ge0: "0 \<le> snd t" and snd_le1: "snd t \<le> 1"
            by auto
          have lower: "0 \<le> 2 * (snd t :: real)"
            using snd_ge0 by linarith
          have upper: "2 * (snd t :: real) \<le> 1"
            using t_half by linarith
          have bounds: "0 \<le> 2 * (snd t :: real) \<and> 2 * (snd t :: real) \<le> 1"
            using lower upper by blast
          show "2 * (snd t :: real) \<in> {0..1}"
          proof -
            from bounds have lower': "0 \<le> 2 * (snd t :: real)" and upper': "2 * (snd t :: real) \<le> 1"
              by auto
            show ?thesis
              using lower' upper' by (auto simp: atLeastAtMost_iff)
          qed
        qed
        show ?thesis
          by (rule continuous_map_into_subtopology[OF scale_cont scale_range])
      qed
    qed
    have left_comp:
      "continuous_map (subtopology ?A {y \<in> topspace ?A. snd y \<le> 1 / 2}) X
        (((\<lambda>y. p (fst y) (snd y)) \<circ> (\<lambda>y. (fst y, 2 * snd y))))"
      by (rule continuous_map_compose[OF left_pair_cont p])
    show "continuous_map (subtopology ?A {y \<in> topspace ?A. snd y \<le> 1 / 2}) X
            (\<lambda>t. p (fst t) (2 * snd t))"
      using left_comp by (simp add: o_def)
    have right_pair_cont:
      "continuous_map (subtopology ?A {y \<in> topspace ?A. 1 / 2 \<le> snd y}) ?A
        (\<lambda>t. (fst t, 2 * snd t - 1))"
  proof (rule continuous_map_pairedI)
      show "continuous_map (subtopology ?A {y \<in> topspace ?A. 1 / 2 \<le> snd y}) ?T01 fst"
        by (rule continuous_map_from_subtopology[OF continuous_map_fst])
      show "continuous_map (subtopology ?A {y \<in> topspace ?A. 1 / 2 \<le> snd y}) ?T01 (\<lambda>t. 2 * (snd t :: real) - 1)"
      proof -
        have snd_cont:
          "continuous_map (subtopology ?A {y \<in> topspace ?A. 1 / 2 \<le> snd y}) euclideanreal snd"
          by (rule continuous_map_into_fulltopology[OF continuous_map_subtopology_snd])
        have affine_cont:
          "continuous_map (subtopology ?A {y \<in> topspace ?A. 1 / 2 \<le> snd y}) euclideanreal
            (\<lambda>t. 2 * (snd t :: real) - 1)"
          using snd_cont by (intro continuous_intros)
        have affine_range:
          "(\<lambda>t. 2 * (snd t :: real) - 1) \<in>
            topspace (subtopology ?A {y \<in> topspace ?A. 1 / 2 \<le> snd y}) \<rightarrow> {0..1}"
        proof
          fix t :: "real \<times> real"
          assume t_in: "t \<in> topspace (subtopology ?A {y \<in> topspace ?A. 1 / 2 \<le> snd y})"
          then have tA: "t \<in> topspace ?A" and t_half: "1 / 2 \<le> snd t"
            by auto
          have snd01: "snd t \<in> {0..1}"
            using tA by (auto simp: topspace_prod_topology)
          from snd01 have snd_ge0: "0 \<le> snd t" and snd_le1: "snd t \<le> 1"
            by auto
          have lower: "0 \<le> 2 * (snd t :: real) - 1"
            using t_half by linarith
          have upper: "2 * (snd t :: real) - 1 \<le> 1"
            using snd_le1 by linarith
          show "2 * (snd t :: real) - 1 \<in> {0..1}"
            using lower upper by (auto simp: atLeastAtMost_iff)
        qed
        show ?thesis
          by (rule continuous_map_into_subtopology[OF affine_cont affine_range])
      qed
    qed
    have right_comp:
      "continuous_map (subtopology ?A {y \<in> topspace ?A. 1 / 2 \<le> snd y}) X
        (((\<lambda>y. q (fst y) (snd y)) \<circ> (\<lambda>y. (fst y, 2 * snd y - 1))))"
      by (rule continuous_map_compose[OF right_pair_cont q])
    show "continuous_map (subtopology ?A {y \<in> topspace ?A. 1 / 2 \<le> snd y}) X
            (\<lambda>t. q (fst t) (2 * snd t - 1))"
      using right_comp by (simp add: o_def)
    show "p (fst y) (2 * snd y) = q (fst y) (2 * snd y - 1)"
      if "y \<in> topspace ?A" "snd y = 1 / 2" for y
    proof -
      have fst01: "fst y \<in> {0..1}"
        using that(1) by (auto simp: topspace_prod_topology)
      have mid1: "2 * snd y = 1"
        using that(2) by simp
      have mid0: "2 * snd y - 1 = 0"
        using that(2) by simp
      have "p (fst y) 1 = q (fst y) 0"
        by (rule pq[OF fst01])
      then show ?thesis
        using mid1 mid0 by simp
    qed
  qed
qed

lemma homotopic_pathsin_continuous_image:
  assumes pq: "homotopic_pathsin X p q"
    and h: "continuous_map X Y f"
  shows "homotopic_pathsin Y (f \<circ> p) (f \<circ> q)"
proof -
  have pq': "homotopic_with (\<lambda>r. r 0 = p 0 \<and> r 1 = p 1) (top_of_set {0..1}) X p q"
    using pq unfolding homotopic_pathsin_def .
  show ?thesis
    unfolding homotopic_pathsin_def
     by (rule homotopic_with_compose_continuous_map_left[OF pq' h]) simp
qed

lemma homotopic_pathsin_reversepathin_D:
  assumes "homotopic_pathsin X p q"
  shows "homotopic_pathsin X (reversepathin p) (reversepathin q)"
proof -
  have rev_cont: "continuous_map (top_of_set {0..1}) (top_of_set {0..1}) (\<lambda>t::real. 1 - t)"
    by (intro continuous_map_into_subtopology continuous_intros) auto
  have pq':
    "homotopic_with (\<lambda>r. r 0 = p 0 \<and> r 1 = p 1) (top_of_set {0..1}) X p q"
    using assms unfolding homotopic_pathsin_def .
  have "homotopic_with (\<lambda>r. r 0 = reversepathin p 0 \<and> r 1 = reversepathin p 1)
      (top_of_set {0..1}) X (p \<circ> (\<lambda>t::real. 1 - t)) (q \<circ> (\<lambda>t::real. 1 - t))"
  proof (rule homotopic_with_compose_continuous_map_right[OF pq' rev_cont])
    fix j :: "real \<Rightarrow> 'a"
    assume j_end: "j 0 = p 0 \<and> j 1 = p 1"
    show "(\<lambda>r. r 0 = reversepathin p 0 \<and> r 1 = reversepathin p 1)
        (j \<circ> (\<lambda>t::real. 1 - t))"
      using j_end by (simp add: reversepathin_def)
  qed
  then show ?thesis
    unfolding homotopic_pathsin_def reversepathin_def o_def .
qed

lemma homotopic_pathsin_reversepathin:
  "homotopic_pathsin X (reversepathin p) (reversepathin q) \<longleftrightarrow> homotopic_pathsin X p q"
  using homotopic_pathsin_reversepathin_D by force

lemma homotopic_pathsin_joinpathin:
  assumes pp': "homotopic_pathsin X p p'"
    and qq': "homotopic_pathsin X q q'"
    and pq: "p 1 = q 0"
  shows "homotopic_pathsin X (joinpathin p q) (joinpathin p' q')"
proof -
  let ?T01 = "subtopology euclideanreal {0..1}"
  let ?A = "prod_topology ?T01 ?T01"
  obtain h1 :: "real \<times> real \<Rightarrow> 'a" where
      h1_cont: "continuous_map (prod_topology (top_of_set {0..1}) (top_of_set {0..1})) X h1"
    and h1_0: "\<forall>x. h1 (0, x) = p x"
    and h1_1: "\<forall>x. h1 (1, x) = p' x"
    and h1_prop: "\<forall>t\<in>{0..1}. h1 (t, 0) = p 0 \<and> h1 (t, 1) = p 1"
    using pp' unfolding homotopic_pathsin_def homotopic_with_def by auto
  obtain h2 :: "real \<times> real \<Rightarrow> 'a" where
      h2_cont: "continuous_map (prod_topology (top_of_set {0..1}) (top_of_set {0..1})) X h2"
    and h2_0: "\<forall>x. h2 (0, x) = q x"
    and h2_1: "\<forall>x. h2 (1, x) = q' x"
    and h2_prop: "\<forall>t\<in>{0..1}. h2 (t, 0) = q 0 \<and> h2 (t, 1) = q 1"
    using qq' unfolding homotopic_pathsin_def homotopic_with_def by auto
  define k1 where "k1 t x = h1 (t, x)" for t x
  define k2 where "k2 t x = h2 (t, x)" for t x
  have k1_cont: "continuous_map ?A X (\<lambda>y. k1 (fst y) (snd y))"
  proof -
    have "(\<lambda>y. k1 (fst y) (snd y)) = h1"
      unfolding k1_def by (auto simp: fun_eq_iff)
    then show ?thesis
      using h1_cont by simp
  qed
  have k2_cont: "continuous_map ?A X (\<lambda>y. k2 (fst y) (snd y))"
  proof -
    have "(\<lambda>y. k2 (fst y) (snd y)) = h2"
      unfolding k2_def by (auto simp: fun_eq_iff)
    then show ?thesis
      using h2_cont by simp
  qed
  have k1_0: "\<forall>x. k1 0 x = p x"
    unfolding k1_def using h1_0 by simp
  have k1_1: "\<forall>x. k1 1 x = p' x"
    unfolding k1_def using h1_1 by simp
  have k2_0: "\<forall>x. k2 0 x = q x"
    unfolding k2_def using h2_0 by simp
  have k2_1: "\<forall>x. k2 1 x = q' x"
    unfolding k2_def using h2_1 by simp
  have k1_prop: "\<forall>t\<in>{0..1}. k1 t 0 = p 0 \<and> k1 t 1 = p 1"
    unfolding k1_def using h1_prop by simp
  have k2_prop: "\<forall>t\<in>{0..1}. k2 t 0 = q 0 \<and> k2 t 1 = q 1"
    unfolding k2_def using h2_prop by simp
  have mid_eq: "k1 t 1 = k2 t 0" if "t \<in> {0..1}" for t
    using k1_prop[rule_format, OF that] k2_prop[rule_format, OF that] pq by auto
  show ?thesis
    unfolding homotopic_pathsin_def homotopic_with_def
  proof (rule exI[where x = "\<lambda>y. joinpathin (k1 (fst y)) (k2 (fst y)) (snd y)"], intro conjI)
    show "continuous_map ?A X (\<lambda>y. joinpathin (k1 (fst y)) (k2 (fst y)) (snd y))"
      by (rule continuous_map_homotopic_joinpathin_lemma[OF k1_cont k2_cont]) (rule mid_eq)
    show "\<forall>x::real. (\<lambda>y. joinpathin (k1 (fst y)) (k2 (fst y)) (snd y)) (0, x) = joinpathin p q x"
    proof
      fix x :: real
      show "(\<lambda>y. joinpathin (k1 (fst y)) (k2 (fst y)) (snd y)) (0, x) = joinpathin p q x"
        using k1_0 k2_0 by (cases "x \<le> 1 / 2") (auto simp: joinpathin_def)
    qed
    show "\<forall>x::real. (\<lambda>y. joinpathin (k1 (fst y)) (k2 (fst y)) (snd y)) (1, x) = joinpathin p' q' x"
    proof
      fix x :: real
      show "(\<lambda>y. joinpathin (k1 (fst y)) (k2 (fst y)) (snd y)) (1, x) = joinpathin p' q' x"
        using k1_1 k2_1 by (cases "x \<le> 1 / 2") (auto simp: joinpathin_def)
    qed
    show "\<forall>t\<in>{0..1}. (\<lambda>r. r 0 = joinpathin p q 0 \<and> r 1 = joinpathin p q 1)
          (\<lambda>x. (\<lambda>y. joinpathin (k1 (fst y)) (k2 (fst y)) (snd y)) (t, x))"
    proof
      fix t :: real
      assume t: "t \<in> {0..1}"
      have k1t0: "k1 t 0 = p 0"
        using k1_prop[rule_format, OF t] by auto
      have k2t1: "k2 t 1 = q 1"
        using k2_prop[rule_format, OF t] by auto
      show "(\<lambda>r. r 0 = joinpathin p q 0 \<and> r 1 = joinpathin p q 1)
            (\<lambda>x. (\<lambda>y. joinpathin (k1 (fst y)) (k2 (fst y)) (snd y)) (t, x))"
        using k1t0 k2t1 by (simp add: joinpathin_def)
    qed
  qed
qed

lemma homotopic_pathsin_reparametrize:
  assumes p: "pathin X p"
    and contf: "continuous_map (top_of_set {0..1}) (top_of_set {0..1}) f"
    and f01: "f \<in> {0..1} \<rightarrow> {0..1}"
    and [simp]: "f 0 = 0" "f 1 = 1"
    and q: "\<And>t. t \<in> {0..1} \<Longrightarrow> q t = p (f t)"
  shows "homotopic_pathsin X p q"
proof -
  have pf: "pathin X (p \<circ> f)"
    using contf p unfolding pathin_def by (rule continuous_map_compose)
  have qf': "homotopic_pathsin X (p \<circ> f) q"
    using pf q by (intro homotopic_pathsin_eq) auto
  have qf: "homotopic_pathsin X q (p \<circ> f)"
    by (rule homotopic_pathsin_sym[OF qf'])
  have fp: "homotopic_pathsin X (p \<circ> f) p"
    unfolding homotopic_pathsin_def homotopic_with_def
  proof (rule exI[where x = "p \<circ> (\<lambda>y. (1 - fst y) * ((f \<circ> snd) y) + fst y * snd y)"], intro conjI)
    have snd_cont:
      "continuous_map (prod_topology (top_of_set {0..1}) (top_of_set {0..1}))
        (top_of_set {0..1}) snd"
      by (rule continuous_map_snd)
    have fst_cont:
      "continuous_map (prod_topology (top_of_set {0..1}) (top_of_set {0..1}))
        (top_of_set {0..1}) fst"
      by (rule continuous_map_fst)
    have fsnd_cont:
      "continuous_map (prod_topology (top_of_set {0..1}) (top_of_set {0..1}))
        (top_of_set {0..1}) (f \<circ> snd)"
      by (rule continuous_map_compose[OF snd_cont contf])
    have param_cont_eu:
      "continuous_map (prod_topology (top_of_set {0..1}) (top_of_set {0..1})) euclideanreal
        (\<lambda>y. (1 - fst y) * ((f \<circ> snd) y) + fst y * snd y)"
      using fst_cont snd_cont fsnd_cont
      by (intro continuous_intros
          continuous_map_into_fulltopology[OF fst_cont]
          continuous_map_into_fulltopology[OF snd_cont]
          continuous_map_into_fulltopology[OF fsnd_cont])
    have param_range:
      "(\<lambda>y. (1 - fst y) * ((f \<circ> snd) y) + fst y * snd y) \<in>
        topspace (prod_topology (top_of_set {0..1}) (top_of_set {0..1})) \<rightarrow> {0..1}"
    proof
      fix y :: "real \<times> real"
      assume y_in: "y \<in> topspace (prod_topology (top_of_set {0..1}) (top_of_set {0..1}))"
      have fst01: "fst y \<in> {0..1}" and snd01: "snd y \<in> {0..1}"
        using y_in by (auto simp: topspace_prod_topology)
      have fsnd01: "f (snd y) \<in> {0..1}"
        using f01 snd01 by auto
      have nonneg: "0 \<le> (1 - fst y) * (f (snd y)) + fst y * snd y"
        using fst01 snd01 fsnd01 by (intro add_nonneg_nonneg mult_nonneg_nonneg) auto
      moreover have le1: "(1 - fst y) * (f (snd y)) + fst y * snd y \<le> 1"
        using fst01 snd01 fsnd01 by (intro convex_bound_le) auto
      ultimately show "((1 - fst y) * ((f \<circ> snd) y) + fst y * snd y) \<in> {0..1}"
        by simp
    qed
    have param_cont:
      "continuous_map (prod_topology (top_of_set {0..1}) (top_of_set {0..1}))
        (top_of_set {0..1}) (\<lambda>y. (1 - fst y) * ((f \<circ> snd) y) + fst y * snd y)"
      using param_cont_eu param_range by (simp add: continuous_map_in_subtopology)
    show "continuous_map
            (prod_topology (top_of_set {0..1}) (top_of_set {0..1})) X
            (p \<circ> (\<lambda>y. (1 - fst y) * ((f \<circ> snd) y) + fst y * snd y))"
      using p unfolding pathin_def by (rule continuous_map_compose[OF param_cont])
    show "\<forall>x::real. (p \<circ> (\<lambda>y. (1 - fst y) * ((f \<circ> snd) y) + fst y * snd y)) (0, x) = (p \<circ> f) x"
    proof
      fix x :: real
      show "(p \<circ> (\<lambda>y. (1 - fst y) * ((f \<circ> snd) y) + fst y * snd y)) (0, x) = (p \<circ> f) x"
        by (simp add: o_def algebra_simps)
    qed
    show "\<forall>x::real. (p \<circ> (\<lambda>y. (1 - fst y) * ((f \<circ> snd) y) + fst y * snd y)) (1, x) = p x"
    proof
      fix x :: real
      show "(p \<circ> (\<lambda>y. (1 - fst y) * ((f \<circ> snd) y) + fst y * snd y)) (1, x) = p x"
        by (simp add: o_def algebra_simps)
    qed
    show "\<forall>t\<in>{0..1}. (\<lambda>r. r 0 = (p \<circ> f) 0 \<and> r 1 = (p \<circ> f) 1)
          (\<lambda>x. (p \<circ> (\<lambda>y. (1 - fst y) * ((f \<circ> snd) y) + fst y * snd y)) (t, x))"
    proof
      fix t :: real
      assume t: "t \<in> {0..1}"
      show "(\<lambda>r. r 0 = (p \<circ> f) 0 \<and> r 1 = (p \<circ> f) 1)
          (\<lambda>x::real. (p \<circ> (\<lambda>y. (1 - fst y) * ((f \<circ> snd) y) + fst y * snd y)) (t, x))"
      proof -
        have end0: "(\<lambda>x::real. (p \<circ> (\<lambda>y. (1 - fst y) * ((f \<circ> snd) y) + fst y * snd y)) (t, x)) 0 = (p \<circ> f) 0"
          by (simp add: o_def algebra_simps)
        have end1: "(\<lambda>x::real. (p \<circ> (\<lambda>y. (1 - fst y) * ((f \<circ> snd) y) + fst y * snd y)) (t, x)) 1 = (p \<circ> f) 1"
          by (simp add: o_def algebra_simps)
        from end0 end1 show ?thesis
          by (simp add: o_def)
      qed
    qed
  qed
  have "homotopic_pathsin X q p"
    by (rule homotopic_pathsin_trans[OF qf fp])
  then show ?thesis
    by (rule homotopic_pathsin_sym)
qed

lemma homotopic_pathsin_rid_const:
  assumes p: "pathin X p"
  shows "homotopic_pathsin X (joinpathin p (\<lambda>_. p 1)) p"
proof -
  have contf: "continuous_map (top_of_set {0..1}) (top_of_set {0..1})
                 (\<lambda>t::real. if t \<le> 1 / 2 then 2 * t else 1)"
  proof (rule continuous_map_into_subtopology)
    show "continuous_map (top_of_set {0..1}) euclideanreal
            (\<lambda>t::real. if t \<le> 1 / 2 then 2 * t else 1)"
    proof (rule continuous_map_cases_le[where p = "\<lambda>t::real. t" and q = "\<lambda>_. 1 / 2"])
      show "continuous_map (top_of_set {0..1}) euclideanreal (\<lambda>t::real. t)"
        by (simp add: continuous_map_iff_continuous)
      show "continuous_map (top_of_set {0..1}) euclideanreal (\<lambda>_. 1 / 2)"
        by simp
      show "continuous_map (subtopology (top_of_set {0..1}) {x \<in> topspace (top_of_set {0..1}). x \<le> 1 / 2})
              euclideanreal (\<lambda>t::real. 2 * t)"
      proof -
        have "continuous_map (top_of_set {0..1}) euclideanreal (\<lambda>t::real. 2 * t)"
          by (simp add: continuous_map_iff_continuous continuous_intros)
        then show ?thesis
          by (rule continuous_map_from_subtopology)
      qed
      show "continuous_map (subtopology (top_of_set {0..1}) {x \<in> topspace (top_of_set {0..1}). 1 / 2 \<le> x})
              euclideanreal (\<lambda>_::real. 1)"
        by simp
      show "2 * x = (1::real)" if "x \<in> topspace (top_of_set {0..1})" "x = 1 / 2" for x
        using that by simp
    qed
    show "(\<lambda>t::real. if t \<le> 1 / 2 then 2 * t else 1) \<in> topspace (top_of_set {0..1}) \<rightarrow> {0..1}"
      by auto
  qed
  show ?thesis
    apply (rule homotopic_pathsin_sym)
    apply (rule homotopic_pathsin_reparametrize[where f = "\<lambda>t::real. if t \<le> 1 / 2 then 2 * t else 1"])
    using p contf
    apply (auto simp: joinpathin_def)
    done
qed

lemma homotopic_pathsin_lid_const:
  assumes p: "pathin X p"
  shows "homotopic_pathsin X (joinpathin (\<lambda>_. p 0) p) p"
proof -
  have contf: "continuous_map (top_of_set {0..1}) (top_of_set {0..1})
                 (\<lambda>t::real. if t \<le> 1 / 2 then 0 else 2 * t - 1)"
  proof (rule continuous_map_into_subtopology)
    show "continuous_map (top_of_set {0..1}) euclideanreal
            (\<lambda>t::real. if t \<le> 1 / 2 then 0 else 2 * t - 1)"
    proof (rule continuous_map_cases_le[where p = "\<lambda>t::real. t" and q = "\<lambda>_. 1 / 2"])
      show "continuous_map (top_of_set {0..1}) euclideanreal (\<lambda>t::real. t)"
        by (simp add: continuous_map_iff_continuous)
      show "continuous_map (top_of_set {0..1}) euclideanreal (\<lambda>_. 1 / 2)"
        by simp
      show "continuous_map (subtopology (top_of_set {0..1}) {x \<in> topspace (top_of_set {0..1}). x \<le> 1 / 2})
              euclideanreal (\<lambda>_::real. 0)"
        by simp
      show "continuous_map (subtopology (top_of_set {0..1}) {x \<in> topspace (top_of_set {0..1}). 1 / 2 \<le> x})
              euclideanreal (\<lambda>t::real. 2 * t - 1)"
      proof -
        have "continuous_map (top_of_set {0..1}) euclideanreal (\<lambda>t::real. 2 * t - 1)"
          by (simp add: continuous_map_iff_continuous continuous_intros)
        then show ?thesis
          by (rule continuous_map_from_subtopology)
      qed
      show "(0::real) = 2 * x - 1" if "x \<in> topspace (top_of_set {0..1})" "x = 1 / 2" for x
        using that by simp
    qed
    show "(\<lambda>t::real. if t \<le> 1 / 2 then 0 else 2 * t - 1) \<in> topspace (top_of_set {0..1}) \<rightarrow> {0..1}"
      by auto
  qed
  show ?thesis
    apply (rule homotopic_pathsin_sym)
    apply (rule homotopic_pathsin_reparametrize[where f = "\<lambda>t::real. if t \<le> 1 / 2 then 0 else 2 * t - 1"])
    using p contf
    apply (auto simp: joinpathin_def)
    done
qed

lemma homotopic_pathsin_assoc:
  assumes p: "pathin X p"
    and q: "pathin X q"
    and r: "pathin X r"
    and pq: "p 1 = q 0"
    and qr: "q 1 = r 0"
  shows "homotopic_pathsin X (joinpathin p (joinpathin q r)) (joinpathin (joinpathin p q) r)"
proof -
  let ?f = "\<lambda>t::real. if t \<le> 1 / 2 then inverse 2 * t else if t \<le> 3 / 4 then t - 1 / 4 else 2 * t - 1"
  have contf_on: "continuous_on {0..1} ?f"
  proof (rule continuous_on_cases_1)
    show "continuous_on {t \<in> {0..1}. t \<le> 1 / 2} (\<lambda>t::real. inverse 2 * t)"
      by (intro continuous_intros)
    show "continuous_on {t \<in> {0..1}. 1 / 2 \<le> t}
            (\<lambda>t::real. if t \<le> 3 / 4 then t - 1 / 4 else 2 * t - 1)"
    proof (rule continuous_on_cases_1)
      show "continuous_on {t \<in> {t \<in> {0..1}. 1 / 2 \<le> t}. t \<le> 3 / 4} (\<lambda>t::real. t - 1 / 4)"
        by (intro continuous_intros)
      show "continuous_on {t \<in> {t \<in> {0..1}. 1 / 2 \<le> t}. 3 / 4 \<le> t} (\<lambda>t::real. 2 * t - 1)"
        by (intro continuous_intros)
      show "(3 / 4::real) \<in> {t \<in> {0..1}. (1 / 2::real) \<le> t} \<Longrightarrow>
          (3 / 4::real) - 1 / 4 = 2 * (3 / 4) - 1"
        by simp
    qed
    show "(1 / 2::real) \<in> {0..1} \<Longrightarrow>
        inverse 2 * (1 / 2::real) =
          (if (1 / 2::real) \<le> 3 / 4 then 1 / 2 - 1 / 4 else 2 * (1 / 2) - 1)"
      by simp
  qed
  have contf_eu: "continuous_map (top_of_set {0..1}) euclideanreal ?f"
    using contf_on by simp
  have contf:
    "continuous_map (top_of_set {0..1}) (top_of_set {0..1}) ?f"
    using contf_eu by (rule continuous_map_into_subtopology) auto
  have join_pq: "pathin X (joinpathin p q)"
    by (rule pathin_joinpathin[OF p q pq])
  have join_qr: "pathin X (joinpathin q r)"
    by (rule pathin_joinpathin[OF q r qr])
  have join_pq_end: "joinpathin p q 1 = r 0"
    using qr by (simp add: joinpathin_def)
  have join_pq_r: "pathin X (joinpathin (joinpathin p q) r)"
    by (rule pathin_joinpathin[OF join_pq r join_pq_end])
  have join_pq_r_expanded:
    "pathin X (\<lambda>t. if t * 2 \<le> 1
        then if 2 * t * 2 \<le> 1 then p (2 * (2 * t)) else q (2 * (2 * t) - 1)
        else r (2 * t - 1))"
    using join_pq_r by (simp add: joinpathin_def)
  show ?thesis
    apply (rule homotopic_pathsin_sym)
    apply (rule homotopic_pathsin_reparametrize[
        where f = ?f])
    using contf join_pq_r_expanded join_pq_r join_pq r qr join_qr p q pq
    apply (auto simp: joinpathin_def field_simps algebra_simps)
    apply (rule arg_cong[where f = q])
    apply (simp add: field_simps)
    done
qed

lemma homotopic_pathsin_rinv_const:
  assumes p: "pathin X p"
  shows "homotopic_pathsin X (joinpathin p (reversepathin p)) (\<lambda>_. p 0)"
proof -
  let ?T01 = "subtopology euclideanreal {0..1}"
  let ?A = "prod_topology ?T01 ?T01"
  let ?h =
    "\<lambda>y. if snd y \<le> 1 / 2
      then p (fst y * (2 * snd y))
      else p (fst y * (1 - (2 * snd y - 1)))"
  have p_cont: "continuous_map ?T01 X p"
    using p unfolding pathin_def .
  have h_cont: "continuous_map ?A X ?h"
  proof (rule continuous_map_cases_le)
    show "continuous_map ?A euclideanreal snd"
      by (rule continuous_map_into_fulltopology[OF continuous_map_snd])
    show "continuous_map ?A euclideanreal (\<lambda>_. 1 / 2)"
      by simp
    have left_param_cont_eu:
      "continuous_map (subtopology ?A {y \<in> topspace ?A. snd y \<le> 1 / 2}) euclideanreal
        (\<lambda>t. fst t * (2 * snd t))"
      by (intro continuous_intros
          continuous_map_into_fulltopology[OF continuous_map_subtopology_fst]
          continuous_map_into_fulltopology[OF continuous_map_subtopology_snd])
    have left_param_cont:
      "continuous_map (subtopology ?A {y \<in> topspace ?A. snd y \<le> 1 / 2}) ?T01
        (\<lambda>t. fst t * (2 * snd t))"
    proof -
      have left_param_range:
        "(\<lambda>t. fst t * (2 * snd t)) \<in>
          topspace (subtopology ?A {y \<in> topspace ?A. snd y \<le> 1 / 2}) \<rightarrow> {0..1}"
      proof
        fix t :: "real \<times> real"
        assume t_in: "t \<in> topspace (subtopology ?A {y \<in> topspace ?A. snd y \<le> 1 / 2})"
        then have tA: "t \<in> topspace ?A" and t_half: "snd t \<le> 1 / 2"
          by auto
        have fst01: "fst t \<in> {0..1}" and snd01: "snd t \<in> {0..1}"
          using tA by (auto simp: topspace_prod_topology)
        from snd01 have snd_ge0: "0 \<le> snd t" and snd_le1: "snd t \<le> 1"
          by auto
        have scale01: "2 * (snd t :: real) \<in> {0..1}"
        proof -
          have lower: "0 \<le> 2 * (snd t :: real)"
            using snd_ge0 by linarith
          have upper: "2 * (snd t :: real) \<le> 1"
            using t_half by linarith
          show "2 * (snd t :: real) \<in> {0..1}"
            using lower upper by auto
        qed
        show "fst t * (2 * (snd t :: real)) \<in> {0..1}"
        proof - 
          from fst01 have fst_ge0: "0 \<le> fst t" and fst_le1: "fst t \<le> 1"
            by auto
          from scale01 have scale_ge0: "0 \<le> 2 * (snd t :: real)" and scale_le1: "2 * (snd t :: real) \<le> 1"
            by auto
          have lower: "0 \<le> fst t * (2 * (snd t :: real))"
            by (rule mult_nonneg_nonneg[OF fst_ge0 scale_ge0])
          have upper: "fst t * (2 * (snd t :: real)) \<le> 1"
            by (rule mult_le_one[OF fst_le1 scale_ge0 scale_le1])
          have bounds:
            "0 \<le> fst t * (2 * (snd t :: real)) \<and> fst t * (2 * (snd t :: real)) \<le> 1"
            using lower upper by blast
          show "fst t * (2 * (snd t :: real)) \<in> {0..1}"
          proof -
            from bounds have lower': "0 \<le> fst t * (2 * (snd t :: real))"
              and upper': "fst t * (2 * (snd t :: real)) \<le> 1"
              by auto
            show ?thesis
              using lower' upper' by (auto simp: atLeastAtMost_iff)
          qed
        qed
      qed
      show ?thesis
        by (rule continuous_map_into_subtopology[OF left_param_cont_eu left_param_range])
    qed
    show "continuous_map (subtopology ?A {y \<in> topspace ?A. snd y \<le> 1 / 2}) X
            (\<lambda>t. p (fst t * (2 * snd t)))"
    proof -
      have left_comp:
        "continuous_map (subtopology ?A {y \<in> topspace ?A. snd y \<le> 1 / 2}) X
          (p \<circ> (\<lambda>t. fst t * (2 * snd t)))"
        by (rule continuous_map_compose[OF left_param_cont p_cont])
      have left_eq: "(\<lambda>t. p (fst t * (2 * snd t))) = p \<circ> (\<lambda>t. fst t * (2 * snd t))"
        by (auto simp: fun_eq_iff)
      show ?thesis
        using left_comp left_eq by simp
    qed
    have right_param_cont_eu:
      "continuous_map (subtopology ?A {y \<in> topspace ?A. 1 / 2 \<le> snd y}) euclideanreal
        (\<lambda>t. fst t * (1 - (2 * snd t - 1)))"
      by (intro continuous_intros
          continuous_map_into_fulltopology[OF continuous_map_subtopology_fst]
          continuous_map_into_fulltopology[OF continuous_map_subtopology_snd])
    have right_param_cont:
      "continuous_map (subtopology ?A {y \<in> topspace ?A. 1 / 2 \<le> snd y}) ?T01
        (\<lambda>t. fst t * (1 - (2 * snd t - 1)))"
    proof -
      have right_param_range:
        "(\<lambda>t. fst t * (1 - (2 * snd t - 1))) \<in>
          topspace (subtopology ?A {y \<in> topspace ?A. 1 / 2 \<le> snd y}) \<rightarrow> {0..1}"
      proof
        fix t :: "real \<times> real"
        assume t_in: "t \<in> topspace (subtopology ?A {y \<in> topspace ?A. 1 / 2 \<le> snd y})"
        then have tA: "t \<in> topspace ?A" and t_half: "1 / 2 \<le> snd t"
          by auto
        have fst01: "fst t \<in> {0..1}" and snd01: "snd t \<in> {0..1}"
          using tA by (auto simp: topspace_prod_topology)
        from snd01 have snd_ge0: "0 \<le> snd t" and snd_le1: "snd t \<le> 1"
          by auto
        have scale01: "1 - (2 * (snd t :: real) - 1) \<in> {0..1}"
        proof -
          have lower: "0 \<le> 1 - (2 * (snd t :: real) - 1)"
            using snd_le1 by linarith
          have upper: "1 - (2 * (snd t :: real) - 1) \<le> 1"
            using t_half by linarith
          show "1 - (2 * (snd t :: real) - 1) \<in> {0..1}"
            using lower upper by force
        qed
        show "fst t * (1 - (2 * (snd t :: real) - 1)) \<in> {0..1}"
        proof - 
          from fst01 have fst_ge0: "0 \<le> fst t" and fst_le1: "fst t \<le> 1"
            by auto
          from scale01 have scale_ge0: "0 \<le> 1 - (2 * (snd t :: real) - 1)"
            and scale_le1: "1 - (2 * (snd t :: real) - 1) \<le> 1"
            by auto
          have lower: "0 \<le> fst t * (1 - (2 * (snd t :: real) - 1))"
            by (rule mult_nonneg_nonneg[OF fst_ge0 scale_ge0])
          have upper: "fst t * (1 - (2 * (snd t :: real) - 1)) \<le> 1"
            by (rule mult_le_one[OF fst_le1 scale_ge0 scale_le1])
          show "fst t * (1 - (2 * (snd t :: real) - 1)) \<in> {0..1}"
            using lower upper by force
        qed
      qed
      show ?thesis
        using right_param_cont_eu right_param_range by (simp add: continuous_map_in_subtopology)
    qed
    show "continuous_map (subtopology ?A {y \<in> topspace ?A. 1 / 2 \<le> snd y}) X
            (\<lambda>t. p (fst t * (1 - (2 * snd t - 1))))"
    proof -
      have right_comp:
        "continuous_map (subtopology ?A {y \<in> topspace ?A. 1 / 2 \<le> snd y}) X
          (p \<circ> (\<lambda>t. fst t * (1 - (2 * snd t - 1))))"
        by (rule continuous_map_compose[OF right_param_cont p_cont])
      have right_eq:
        "(\<lambda>t. p (fst t * (1 - (2 * snd t - 1)))) =
          p \<circ> (\<lambda>t. fst t * (1 - (2 * snd t - 1)))"
        by (auto simp: fun_eq_iff)
      show ?thesis
        using right_comp right_eq by simp
    qed
    show "p (fst y * (2 * snd y)) = p (fst y * (1 - (2 * snd y - 1)))"
      if "y \<in> topspace ?A" "snd y = 1 / 2" for y
    proof -
      have mid1: "2 * snd y = (1::real)"
        using that(2) by simp
      have mid0: "2 * snd y - 1 = (0::real)"
        using that(2) by simp
      show ?thesis
        using mid1 mid0 by simp
    qed
  qed
  have hom_const_join: "homotopic_pathsin X (\<lambda>_. p 0) (joinpathin p (reversepathin p))"
    unfolding homotopic_pathsin_def homotopic_with_def
  proof (rule exI[where x = ?h], intro conjI)
    show "continuous_map ?A X ?h"
      by (rule h_cont)
    show "\<forall>x::real. ?h (0, x) = (\<lambda>_. p 0) x"
      by simp
    show "\<forall>x::real. ?h (1, x) = joinpathin p (reversepathin p) x"
      by (auto simp: joinpathin_def reversepathin_def)
    show "\<forall>t\<in>{0..1}. (\<lambda>r. r 0 = p 0 \<and> r 1 = p 0) (\<lambda>x. ?h (t, x))"
      by simp
  qed
  show ?thesis
    by (rule homotopic_pathsin_sym[OF hom_const_join])
qed

lemma homotopic_pathsin_linv_const:
  assumes p: "pathin X p"
  shows "homotopic_pathsin X (joinpathin (reversepathin p) p) (\<lambda>_. p 1)"
proof -
  have "homotopic_pathsin X (joinpathin (reversepathin p) (reversepathin (reversepathin p)))
      (\<lambda>_. reversepathin p 0)"
    using pathin_reversepathin[OF p] by (rule homotopic_pathsin_rinv_const)
  then show ?thesis
    by (simp add: reversepathin_def)
qed

lemma homotopic_loopsin_imp_pathin:
  assumes "homotopic_loopsin X p q"
  shows "pathin X p" "pathin X q"
  using assms unfolding homotopic_loopsin_def pathin_def
  by (auto dest: homotopic_with_imp_continuous_maps)

lemma homotopic_loopsin_imp_loop:
  assumes "homotopic_loopsin X p q"
  shows "p 1 = p 0" "q 1 = q 0"
  using assms unfolding homotopic_loopsin_def
  by (auto dest: homotopic_with_imp_property)

lemma homotopic_loopsin_refl [simp]:
  "homotopic_loopsin X p p \<longleftrightarrow> pathin X p \<and> p 1 = p 0"
  unfolding homotopic_loopsin_def pathin_def
  by (simp add: homotopic_with_refl)

lemma homotopic_loopsin_sym:
  assumes "homotopic_loopsin X p q"
  shows "homotopic_loopsin X q p"
  using assms unfolding homotopic_loopsin_def
  by (simp add: homotopic_with_sym)

lemma homotopic_loopsin_trans:
  assumes "homotopic_loopsin X p q"
    and "homotopic_loopsin X q r"
  shows "homotopic_loopsin X p r"
  using assms unfolding homotopic_loopsin_def
  by (blast intro: homotopic_with_trans)

lemma loopin_space_reversepathin:
  assumes "p \<in> loopin_space X x"
  shows "reversepathin p \<in> loopin_space X x"
proof -
  from assms obtain p_in where p_in: "pathin X p" "p 0 = x" "p 1 = x"
    by (rule loopin_spaceE)
  have path_rev: "pathin X (reversepathin p)"
    using p_in(1) by (rule pathin_reversepathin)
  have start_rev: "reversepathin p 0 = x"
    using p_in(3) by (simp add: reversepathin_def)
  have finish_rev: "reversepathin p 1 = x"
    using p_in(2) by (simp add: reversepathin_def)
  show ?thesis
    unfolding loopin_space_def using path_rev start_rev finish_rev by blast
qed

end
