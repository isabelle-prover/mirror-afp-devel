(*  Title:   Space_of_Continuous_Maps.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

subsection  \<open>Example: The Metric Space of Continuous Functions\<close>
theory Space_of_Continuous_Maps
  imports "StandardBorel"
begin

definition cmaps :: "['a topology, 'b topology] \<Rightarrow> ('a \<Rightarrow> 'b) set" where
"cmaps X Y \<equiv> {f. f \<in> extensional (topspace X) \<and> continuous_map X Y f}"

definition cmaps_dist :: "['a topology, 'b topology, 'b \<Rightarrow> 'b \<Rightarrow> real, 'a \<Rightarrow> 'b, 'a \<Rightarrow> 'b] \<Rightarrow> real" where
"cmaps_dist X Y d f g \<equiv> if f \<in> cmaps X Y \<and> g \<in> cmaps X Y \<and> topspace X \<noteq> {} then (\<Squnion> {d (f x) (g x) |x. x \<in> topspace X}) else 0"

lemma cmaps_X_empty:
  assumes "topspace X = {}"
  shows "cmaps X Y = {\<lambda>x. undefined}"
  by(auto simp: cmaps_def assms simp flip: null_topspace_iff_trivial)

lemma cmaps_Y_empty:
  assumes "topspace X \<noteq> {}" "topspace Y = {}"
  shows "cmaps X Y = {}"
  by(auto simp: cmaps_def assms continuous_map_def Pi_def simp flip: null_topspace_iff_trivial)

lemma cmaps_dist_X_empty:
  assumes "topspace X = {}"
  shows "cmaps_dist X = (\<lambda>Y d f g. 0)"
  by standard+ (auto simp: cmaps_dist_def assms)

lemma cmaps_dist_Y_empty:
  assumes "topspace X \<noteq> {}" "topspace Y = {}"
  shows "cmaps_dist X Y = (\<lambda>d f g. 0)"
  by standard+ (auto simp: cmaps_dist_def assms cmaps_Y_empty)

subsubsection \<open>Definition\<close>
context metric_set
begin

context
  fixes K and X :: "'b topology"
  assumes m_bounded :"\<And>x y. dist x y \<le> K"
begin

lemma cm_dest:
  shows "\<And>f x. f \<in> (cmaps X mtopology) \<Longrightarrow> x \<in> topspace X \<Longrightarrow> f x \<in> S"
    and "\<And>f x. f \<in> (cmaps X mtopology) \<Longrightarrow> x \<notin> topspace X \<Longrightarrow> f x = undefined"
    and "\<And>f. f \<in> (cmaps X mtopology) \<Longrightarrow> continuous_map X mtopology f"
  using continuous_map_image_subset_topspace[of X mtopology,simplified mtopology_topspace]
  by(auto simp: cmaps_def extensional_def)

lemma cmaps_dist_bdd_above[simp]: "bdd_above {dist (f x) (g x) |x. x \<in> A}"
  using m_bounded by(auto intro!: bdd_aboveI[where M=K])

lemma cmaps_metric_set: "metric_set (cmaps X mtopology) (cmaps_dist X mtopology dist)"
proof(cases "topspace X = {}")
  case True
  then show ?thesis
    by(simp add: singleton_metric cmaps_X_empty cmaps_dist_X_empty)
next
  case h:False
  then have nen[simp]:"{dist (f x) (g x)|x. x \<in> topspace X} \<noteq> {}" for f g
    by auto
  show ?thesis
  proof
    show "(cmaps_dist X mtopology dist) f g \<ge> 0" for f g
      by(auto simp: cmaps_dist_def dist_geq0 intro!: cSup_upper2[where x="dist _ _"]
              simp flip: null_topspace_iff_trivial)
  next
    fix f g
    assume "f \<notin> (cmaps X mtopology)"
    then show "(cmaps_dist X mtopology dist) f g = 0"
      by(simp add: cmaps_dist_def)
  next
    show "(cmaps_dist X mtopology dist) f g = (cmaps_dist X mtopology dist) g f" for f g
      by(simp add: cmaps_dist_def dist_sym)
  next
    fix f g
    assume fg:"f \<in> (cmaps X mtopology)" "g \<in> (cmaps X mtopology)"
    show "f = g \<longleftrightarrow> (cmaps_dist X mtopology dist) f g = 0"
    proof safe
      have "{dist (g x) (g x) |x. x \<in> topspace X} = {0}"
        using h by fastforce
      thus "(cmaps_dist X mtopology dist) g g = 0"
        by(simp add: cmaps_dist_def)
    next
      assume "(cmaps_dist X mtopology dist) f g = 0"
      with fg h have "\<Squnion> {dist (f x) (g x)|x. x \<in> topspace X} \<le> 0"
        by(auto simp: cmaps_dist_def)
      hence "\<And>x. x \<in> topspace X \<Longrightarrow> dist (f x) (g x) \<le> 0"
        by(auto simp: cSup_le_iff[OF nen])
      from antisym[OF this dist_geq0] have fgeq:"\<And>x. x \<in> topspace X \<Longrightarrow> f x = g x"
        using dist_0[OF cm_dest(1)[OF fg(1)] cm_dest(1)[OF fg(2)]] by auto
      show "f = g"
      proof
        fix x
        show "f x = g x"
          by(cases "x \<in> topspace X",insert fg) (auto simp: cm_dest fgeq)
      qed
    qed
  next
    fix f g h
    assume fgh: "f \<in> (cmaps X mtopology)" "g \<in> (cmaps X mtopology)" "h \<in> (cmaps X mtopology)"
    show "(cmaps_dist X mtopology dist) f h \<le> (cmaps_dist X mtopology dist) f g + (cmaps_dist X mtopology dist) g h" (is "?lhs \<le> ?rhs")
    proof -
      have bdd1:"bdd_above {dist (f x) (g x) + dist (g x) (h x) | x. x \<in> topspace X}"
        using add_mono[OF m_bounded m_bounded] by(auto simp: bdd_above_def intro!: exI[where x="K + K"])
      have nen1:"{dist (f x) (g x) + dist (g x) (h x) |x. x \<in> topspace X} \<noteq> {}"
        using h by auto
      have "?lhs \<le> (\<Squnion> {dist (f x) (g x) + dist (g x) (h x)|x. x \<in> topspace X})"
      proof -
        {
          fix x
          assume "x \<in> topspace X"
          hence "\<exists>z. (\<exists>x. z = dist (f x) (g x) + dist (g x) (h x) \<and> x \<in> topspace X) \<and> dist (f x) (h x) \<le> z"
            by(auto intro!: exI[where x="dist (f x) (g x) + dist (g x) (h x)"] exI[where x=x] dist_tr cm_dest fgh)
        }
        thus ?thesis
          by(auto simp: cmaps_dist_def fgh h intro!: cSup_mono bdd1 simp flip: null_topspace_iff_trivial)
      qed
      also have "... \<le> ?rhs"
        by(auto simp: cSup_le_iff[OF nen1 bdd1] cmaps_dist_def fgh h intro!: add_mono cSup_upper)
      finally show ?thesis .
    qed
  qed
qed

end

end

subsubsection \<open>Topology of Uniform Convergence\<close>
locale topology_of_uniform_convergence_c = complete_metric_set + compact_metrizable X for X
  + fixes K
assumes d_bounded: "\<And>x y. dist x y \<le> K"
begin

lemmas cm_dist_bdd_above[simp] = cmaps_dist_bdd_above[OF d_bounded]

abbreviation "cm \<equiv> cmaps X mtopology"
abbreviation "cm_dist \<equiv> cmaps_dist X mtopology dist"

lemma cm_complete_metric_set: "complete_metric_set cm cm_dist"
proof -
  interpret m: metric_set cm cm_dist
    by(auto intro!: cmaps_metric_set d_bounded)
  show ?thesis
  proof
    obtain dx where dx: "compact_metric_set (topspace X) dx" "metric_set.mtopology (topspace X) dx = X"
      by(rule compact_metric)
    interpret dx: compact_metric_set "topspace X" dx
      by fact
    fix fn
    assume h:"m.Cauchy_inS fn"
    note fn_cm = m.Cauchy_inS_dest1[OF this]
    have c:"\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. \<forall>x\<in>topspace X. dist (fn n x) (fn m x) < e" if e:"e > 0" for e
    proof -
      obtain N where N:"\<And>n m. n \<ge> N \<Longrightarrow> m \<ge> N \<Longrightarrow> cm_dist (fn n) (fn m) < e"
        by(metis e h m.Cauchy_inS_def)
      show ?thesis
      proof(safe intro!: exI[where x=N])
        fix n m x
        assume nmx: "n \<ge> N" "m \<ge> N" "x \<in> topspace X"
        then have "dist (fn n x) (fn m x) \<le> cm_dist (fn n) (fn m)"
          using fn_cm by(auto simp: cmaps_dist_def intro!: cSup_upper)
        also have "... < e"
          by(auto intro!: N nmx)
        finally show "dist (fn n x) (fn m x) < e" .
      qed
    qed
    have "convergent_inS (\<lambda>n. fn n x)" if x:"x \<in> topspace X" for x
      by (rule convergence,auto simp: Cauchy_inS_def,insert c x fn_cm)
         (auto simp: cmaps_def continuous_map_def mtopology_topspace, blast, meson)
    then obtain f where f:"\<And>x. x \<in> topspace X \<Longrightarrow> converge_to_inS (\<lambda>n. fn n x) (f x)"
      by(auto simp: convergent_inS_def) metis
    define f' where "f' \<equiv> (\<lambda>x\<in>topspace X. f x)"
    have f':"\<And>x. x \<in> topspace X \<Longrightarrow> converge_to_inS (\<lambda>n. fn n x) (f' x)"
      using f by(auto simp: f'_def)
    have cu:"converges_uniformly (topspace X) S dist fn f'"
      unfolding converges_uniformly_def[OF dx.metric_set_axioms metric_set_axioms]
    proof safe
      fix e :: real
      assume e:"0 < e"
      obtain N where N: "\<And>n m x. n\<ge>N \<Longrightarrow> m\<ge>N \<Longrightarrow> x\<in>topspace X \<Longrightarrow> dist (fn n x) (fn m x) < e / 2"
        by(metis c[OF half_gt_zero[OF e]])
      show "\<exists>N. \<forall>n\<ge>N. \<forall>x\<in>topspace X. dist (fn n x) (f' x) < e"
      proof(rule ccontr)
        assume "\<nexists>N. \<forall>n\<ge>N. \<forall>x\<in>topspace X. dist (fn n x) (f' x) < e"
        with N obtain n x where nx: "n \<ge> N" "x \<in> topspace X" "e \<le> dist (fn n x) (f' x)"
          by (meson linorder_le_less_linear)
        from f'[OF this(2)] half_gt_zero[OF e]
        obtain N' where N':"\<And>n. n \<ge> N' \<Longrightarrow> dist (fn n x) (f' x) < e / 2"
          by(metis converge_to_inS_def2)
        define N0 where "N0 \<equiv> max N N'"
        have N0 : "N0 \<ge> N" "N0 \<ge> N'" by(auto simp: N0_def)
        have "e \<le> dist (fn n x) (f' x)" by fact
        also have "... \<le> dist (fn n x) (fn N0 x) + dist (fn N0 x) (f' x)"
          using f'[OF nx(2)] by(auto intro!: dist_tr simp: converge_to_inS_def)
        also have "... < e"
          using N[OF nx(1) N0(1) nx(2)] N'[OF N0(2)] by auto
        finally show False ..
      qed
    qed(use f' converge_to_inS_def in auto)
    show "m.convergent_inS fn"
      unfolding m.convergent_inS_def m.converge_to_inS_def2
    proof(safe intro!: exI[where x=f'])
      have "continuous_map dx.mtopology mtopology f'"
        using fn_cm by(auto intro!: converges_uniformly_continuous[OF dx.metric_set_axioms metric_set_axioms _ cu] simp: cmaps_def,auto simp:  dx)
      thus f'_cm:"f' \<in> cm"
        by(auto simp: cmaps_def dx f'_def)
      fix e :: real
      assume e:"0 < e"
      obtain N where N:"\<And>n x. n \<ge> N \<Longrightarrow> x \<in> topspace X \<Longrightarrow> dist (fn n x) (f' x) < e / 2"
        by(metis half_gt_zero[OF e] cu[simplified converges_uniformly_def[OF dx.metric_set_axioms metric_set_axioms]])
      show "\<exists>N. \<forall>n\<ge>N. cm_dist (fn n) f' < e"
      proof(safe intro!: exI[where x=N])
        fix n
        assume n:"N \<le> n"
        have "cm_dist (fn n) f' \<le> e / 2"
        proof(cases "topspace X = {}")
          case True
          then show ?thesis
            by(auto simp: order.strict_implies_order[OF e] cmaps_X_empty cmaps_dist_X_empty)
        next
          case False
          then have 1:"{dist (fn n x) (f' x) |x. x \<in> topspace X} \<noteq> {}" by auto
          hence "cm_dist (fn n) f' = (\<Squnion> {dist (fn n x) (f' x) |x. x \<in> topspace X})"
            by(auto simp: f'_cm fn_cm cmaps_dist_def)
          also have "... \<le> e / 2"
            by(simp only: cSup_le_iff[OF 1,simplified]) (insert N[OF n], auto intro!: order.strict_implies_order)
          finally show ?thesis .
        qed
        also have "... < e"
          using e by simp
        finally show "cm_dist (fn n) f' < e" .
      qed
    qed(use fn_cm in auto)
  qed
qed

end

locale topology_of_uniform_convergence = polish_metric_set + compact_metrizable X for X
  + fixes K
assumes d_bounded: "\<And>x y. dist x y \<le> K"
begin

sublocale topology_of_uniform_convergence_c
  by (simp add: compact_metrizable_axioms complete_metric_set_axioms d_bounded topology_of_uniform_convergence_c_axioms_def topology_of_uniform_convergence_c_def)

lemma cm_polish_metric_set: "polish_metric_set cm cm_dist"
proof -
  consider "topspace X = {}" | "topspace X \<noteq> {}" "S = {}" | "topspace X \<noteq> {}" "S \<noteq> {}" by auto
  thus ?thesis
  proof cases
    case 1
    then show ?thesis
      by(simp add: singleton_metric_polish cmaps_X_empty cmaps_dist_X_empty)
  next
    case 2
    then show ?thesis
      by(simp add: empty_metric_polish cmaps_Y_empty[of _ mtopology,simplified mtopology_topspace] cmaps_dist_Y_empty[of _ mtopology,simplified mtopology_topspace])
  next
    case XS_nem:3
    interpret m: complete_metric_set cm cm_dist
      by(rule cm_complete_metric_set)
    show ?thesis
    proof
      obtain dx where dx: "compact_metric_set (topspace X) dx" "metric_set.mtopology (topspace X) dx = X"
        by(rule compact_metric)
      interpret dx: compact_metric_set "topspace X" dx
        by fact
      have "\<exists>B. finite B \<and> B \<subseteq> topspace X \<and> topspace X = (\<Union>a\<in>B. dx.open_ball a (1 / Suc m))" for m
        using dx.totally_boundedSD[OF dx.totally_bounded,of "1 / Suc m"] by fastforce 
      then obtain Xm where Xm: "\<And>m. finite (Xm m)" "\<And>m. (Xm m) \<subseteq> topspace X" "\<And>m. topspace X = (\<Union>a\<in>Xm m. dx.open_ball a (1 / Suc m))"
        by metis
      have Xm_nem:"\<And>m. (Xm m) \<noteq> {}"
        using XS_nem Xm(3) by fastforce
      define xmk where "xmk \<equiv> (\<lambda>m. from_nat_into (Xm m))"
      define km where "km \<equiv> (\<lambda>m. card (Xm m))"
      have km_pos:"km m > 0" for m
        by(simp add: km_def card_gt_0_iff Xm Xm_nem)
      have xmk_bij: "bij_betw (xmk m) {..<km m} (Xm m)" for m
        using bij_betw_from_nat_into_finite[OF Xm(1)] by(simp add: km_def xmk_def)
      have xmk_into: "xmk m i \<in> Xm m" for m i
        by (simp add: Xm_nem from_nat_into xmk_def)
      have "\<exists>U. countable U \<and> \<Union> U = S \<and> (\<forall>u\<in>U. diam u < 1 / (Suc l))" for l
        by(rule Lindelof_diam) auto
      then obtain U where U: "\<And>l. countable (U l)" "\<And>l. (\<Union> (U l)) = S" "\<And>l u. u \<in> U l \<Longrightarrow> diam u < 1 / Suc l"
        by metis
      have Ul_nem: "U l \<noteq> {}" for l
        using XS_nem U(2) by auto
      define uli where "uli \<equiv> (\<lambda>l. from_nat_into (U l))"
      have uli_into:"uli l i \<in> U l" for l i
        by (simp add: Ul_nem from_nat_into uli_def)
      hence uli_diam: "diam (uli l i) < 1 / Suc l" for l i
        using U(3) by auto
      have uli_un:"S = (\<Union>i. uli l i)" for l
        by(auto simp: range_from_nat_into[OF Ul_nem[of l] U(1)] uli_def U)
      define Cmn where "Cmn \<equiv> (\<lambda>m n. {f \<in> cm. \<forall>x\<in>topspace X. \<forall>y\<in>topspace X. dx x y < 1 / (Suc m) \<longrightarrow> dist (f x) (f y) < 1 / Suc n})"
      define fmnls where "fmnls \<equiv> (\<lambda>m n l s. SOME f. f \<in> Cmn m n \<and> (\<forall>j<km m. f (xmk m j) \<in> uli l (s j)))"
      define Dmnl where "Dmnl \<equiv> (\<lambda>m n l. {fmnls m n l s |s. s \<in> {..<km m} \<rightarrow>\<^sub>E UNIV \<and> (\<exists>f \<in> Cmn m n. (\<forall>j<km m. f (xmk m j) \<in> uli l (s j))) })"
      have in_Dmnl: "fmnls m n l s \<in> Dmnl m n l" if "s\<in>{..<km m} \<rightarrow>\<^sub>E UNIV" "f\<in> Cmn m n" "\<forall>j<km m. f (xmk m j) \<in> uli l (s j)"for m n l s f
        using Dmnl_def that by blast
      define Dmn where "Dmn \<equiv> (\<lambda>m n. \<Union>l. Dmnl m n l)"
      have Dmn_subset: "Dmn m n \<subseteq> Cmn m n" for m n
      proof -
        have "Dmnl m n l \<subseteq> Cmn m n" for l
          by(auto simp: Dmnl_def fmnls_def someI[of "\<lambda>f. f \<in> Cmn m n \<and> (\<forall>j<km m. f (xmk m j) \<in> uli l (_ j))"])
        thus ?thesis by(auto simp: Dmn_def)
      qed
      have c_Dmn: "countable (Dmn m n)" for m n
      proof -
        have "countable (Dmnl m n l)" for l
        proof -
          have 1:"Dmnl m n l \<subseteq> (\<lambda>s. fmnls m n l s) ` ({..<km m} \<rightarrow>\<^sub>E UNIV)"
            by(auto simp: Dmnl_def)
          have "countable ..."
            by(auto intro!: countable_PiE)
          with 1 show ?thesis
            using countable_subset by blast
        qed
        thus ?thesis
          by(auto simp: Dmn_def)
      qed
      have claim: "\<exists>g\<in>Dmn m n. \<forall>y\<in>Xm m. dist (f y) (g y) < e" if f:"f \<in> Cmn m n" and e:"e > 0" for f m n e
      proof -
        obtain l where l:"1 / Suc l < e"
          using e nat_approx_posE by blast
        define s where "s \<equiv> (\<lambda>i\<in>{..<km m}. SOME j. f (xmk m i) \<in> uli l j)"
        have s1:"s\<in>{..<km m} \<rightarrow>\<^sub>E UNIV" by(simp add: s_def)
        have s2:"\<forall>i<km m. f (xmk m i) \<in> uli l (s i)"
        proof -
          fix i
          have "f (xmk m i) \<in> uli l (SOME j. f (xmk m i) \<in> uli l j)" for i
          proof(rule someI_ex)
            have "xmk m i \<in> topspace X"
              using Xm(2) xmk_into by auto
            hence "f (xmk m i) \<in> S"
              using f by(auto simp: Cmn_def cmaps_def continuous_map_def mtopology_topspace)
            thus "\<exists>x. f (xmk m i) \<in> uli l x"
              using uli_un by auto
          qed
          thus ?thesis
            by (auto simp: s_def)
        qed
        have fmnls:"fmnls m n l s \<in> Cmn m n \<and> (\<forall>j<km m. fmnls m n l s (xmk m j) \<in> uli l (s j))"
          by(simp add: fmnls_def,rule someI[where x=f],auto simp: s2 f)
        show "\<exists>g\<in>Dmn m n. \<forall>y\<in>Xm m. dist (f y) (g y) < e"
        proof(safe intro!: bexI[where x="fmnls m n l s"])
          fix y
          assume y:"y \<in> Xm m"
          then obtain i where i:"i < km m" "xmk m i = y"
            by (meson xmk_bij[of m] bij_betw_iff_bijections lessThan_iff)
          have "f y \<in> uli l (s i)" "fmnls m n l s y \<in> uli l (s i)"
            using i(1) s2 fmnls by(auto simp: i(2)[symmetric])
          moreover have "f y \<in> S" "fmnls m n l s y \<in> S"
            using f fmnls y Xm(2)[of m] by(auto simp: Cmn_def cmaps_def continuous_map_def mtopology_topspace)
          ultimately have "ennreal (dist (f y) (fmnls m n l s y)) \<le> diam (uli l (s i))"
            by(auto intro!: diam_is_sup)
          also have "... < ennreal (1 / Suc l)"
            by(rule uli_diam)
          also have "... < ennreal e"
            using l e by(auto intro!: ennreal_lessI)
          finally show "dist (f y) (fmnls m n l s y) < e"
            by(simp add: ennreal_less_iff[OF dist_geq0])
        qed(use in_Dmnl[OF s1 f s2] Dmn_def in auto)
      qed

      show "\<exists>U. countable U \<and> m.dense_set U"
        unfolding m.dense_set_def2
      proof(safe intro!: exI[where x="\<Union>n. (\<Union>m. Dmn m n)"])
        fix f and e :: real
        assume h:"f \<in> cm" "0 < e"
        then obtain n where n:"1 / Suc n < e / 4"
          by (metis zero_less_divide_iff zero_less_numeral nat_approx_posE)
        have "\<exists>m. \<forall>l\<ge> m. f \<in> Cmn l n"
        proof -
          have "uniform_continuous_map (topspace X) dx S dist f"
            using h by(auto intro!: dx.continuous_map_is_uniform[OF metric_set_axioms] simp: cmaps_def dx)
          then obtain d where d:"d > 0" "\<And>x y. x\<in>topspace X \<Longrightarrow> y\<in>topspace X \<Longrightarrow> dx x y < d \<Longrightarrow> dist (f x) (f y) < 1 / (Suc n)"
            by(auto simp: uniform_continuous_map_def[OF dx.metric_set_axioms metric_set_axioms]) (metis less_add_same_cancel2 linorder_neqE_linordered_idom of_nat_Suc of_nat_less_0_iff zero_less_divide_1_iff zero_less_one)
          then obtain m where m:"1 / Suc m < d"
            using nat_approx_posE by blast
          have l: "l \<ge> m \<Longrightarrow> 1 / Suc l \<le> 1 / Suc m" for l
            by (simp add: frac_le)
          show ?thesis
            using d(2)[OF _ _ order.strict_trans[OF _ order.strict_trans1[OF l m]]]  by(auto simp: Cmn_def h)
        qed
        then obtain m where m:"f \<in> Cmn m n" by auto
        obtain g where g:"g\<in>Dmn m n" "\<And>y. y\<in>Xm m \<Longrightarrow> dist (f y) (g y) < e / 4"
          by (metis claim[OF m] h(2) zero_less_divide_iff zero_less_numeral)
        have "\<exists>n m. \<exists>g\<in>Dmn m n. cm_dist f g < e"
        proof(rule exI[where x=n])
          show "\<exists>m. \<exists>g\<in>Dmn m n. cm_dist f g < e"
          proof(intro exI[where x=m] bexI[OF _ g(1)])
            have g_cm:"g \<in> cm"
              using g(1) Dmn_subset[of m n] by(auto simp: Cmn_def)
            hence "cm_dist f g = (\<Squnion> {dist (f x) (g x) |x. x \<in> topspace X})"
              by(auto simp: cmaps_dist_def h XS_nem simp flip: null_topspace_iff_trivial)
            also have "... \<le> 3 * e / 4"
            proof -
              have 1:"{dist (f x) (g x) |x. x \<in> topspace X} \<noteq> {}"
                using XS_nem by auto
              have 2:"dist (f x) (g x) \<le> 3 * e / 4" if x:"x \<in> topspace X" for x
              proof -
                obtain y where y:"y \<in> Xm m" "x \<in> dx.open_ball y (1 / real (Suc m))"
                  using Xm(3) x by auto
                hence ytop:"y \<in> topspace X"
                  using Xm(2) by auto
                have "dist (f x) (g x) \<le> dist (f x) (f y) + dist (f y) (g x)"
                  using x g_cm h(1) ytop by(auto intro!: dist_tr simp: cmaps_def continuous_map_def mtopology_topspace)
                also have "... \<le> dist (f x) (f y) + dist (f y) (g y) + dist (g y) (g x)"
                  using x g_cm h(1) ytop by(auto intro!: dist_tr simp: cmaps_def continuous_map_def mtopology_topspace)
                also have "... \<le> e / 4 + e / 4 + e / 4"
                proof -
                  have dxy: "dx x y < 1 / Suc m" "dx y x < 1 / Suc m"
                    using dx.open_ballD[OF y(2)] by(auto simp: dx.dist_sym)
                  hence "dist (f x) (f y) < 1 / (Suc n)" "dist (g y) (g x) < 1 / (Suc n)"
                    using m x ytop g Dmn_subset[of m n] by(auto simp: Cmn_def)
                  hence "dist (f x) (f y) < e / 4" "dist (g y) (g x) < e / 4"
                    using n by auto
                  thus ?thesis
                    using g(2)[OF y(1)] by auto
                qed
                finally show "dist (f x) (g x) \<le> 3 * e / 4" by simp
              qed
              show ?thesis
                using 2 by(auto simp only: cSup_le_iff[OF 1,simplified])
            qed
            also have "... < e"
              using h by auto
            finally show "cm_dist f g < e" .
          qed
        qed
        thus "\<exists>y\<in>\<Union>n m. Dmn m n. cm_dist f y < e"
          by auto
      qed(use Dmn_subset c_Dmn Cmn_def in auto)
    qed
  qed
qed

end


end