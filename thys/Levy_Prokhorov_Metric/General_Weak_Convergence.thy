(*  Title:   General_Weak_Convergence.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

section \<open> General Weak Convergence \<close>
theory General_Weak_Convergence
  imports Lemmas_Levy_Prokhorov
          "Riesz_Representation.Regular_Measure"
begin

text \<open> We formalize the notion of weak convergence and equivalent conditions.
       The formalization of weak convergence in HOL-Probability is restricted to
       probability measures on real numbers.
       Our formalization is generalized to finite measures on any metric spaces. \<close>

subsection \<open> Topology of Weak Convegence\<close>
definition weak_conv_topology :: "'a topology \<Rightarrow> 'a measure topology" where
"weak_conv_topology X \<equiv>
  topology_generated_by
    (\<Union>f\<in>{f. continuous_map X euclideanreal f \<and> (\<exists>B. \<forall>x\<in>topspace X. \<bar>f x\<bar> \<le> B)}.
       Collect (openin (pullback_topology {N. sets N = sets (borel_of X) \<and> finite_measure N}
                                          (\<lambda>N. \<integral>x. f x \<partial>N) euclideanreal)))"

lemma topspace_weak_conv_topology[simp]:
 "topspace (weak_conv_topology X) = {N. sets N = sets (borel_of X) \<and> finite_measure N}"
  unfolding weak_conv_topology_def openin_pullback_topology
  by(auto intro!: exI[where x="\<lambda>x. 1"] exI[where x=1]) blast

lemma openin_weak_conv_topology_base:
  assumes f:"continuous_map X euclideanreal f" and B:"\<And>x. x \<in> topspace X \<Longrightarrow> \<bar>f x\<bar> \<le> B"
    and U:"open U"
  shows "openin (weak_conv_topology X) ((\<lambda>N. \<integral>x. f x \<partial>N) -` U
                                         \<inter> {N. sets N = sets (borel_of X) \<and> finite_measure N})"
  using assms
  by(fastforce simp: weak_conv_topology_def openin_topology_generated_by_iff openin_pullback_topology
      intro!: Basis)

lemma continuous_map_weak_conv_topology:
  assumes f:"continuous_map X euclideanreal f" and B:"\<And>x. x \<in> topspace X \<Longrightarrow> \<bar>f x\<bar> \<le> B"
  shows "continuous_map (weak_conv_topology X) euclideanreal (\<lambda>N. \<integral>x. f x \<partial>N)"
  using openin_weak_conv_topology_base[OF assms]
  by(auto simp: continuous_map_def Collect_conj_eq Int_commute Int_left_commute vimage_def)

lemma weak_conv_topology_minimal:
  assumes "topspace Y = {N. sets N = sets (borel_of X) \<and> finite_measure N}"
    and "\<And>f B. continuous_map X euclideanreal f
                \<Longrightarrow> (\<And>x. x \<in> topspace X \<Longrightarrow> \<bar>f x\<bar> \<le> B) \<Longrightarrow> continuous_map Y euclideanreal (\<lambda>N. \<integral>x. f x \<partial>N)"
  shows "openin (weak_conv_topology X) U \<Longrightarrow> openin Y U"
  unfolding weak_conv_topology_def openin_topology_generated_by_iff
proof (induct rule: generate_topology_on.induct)
  case h:(Basis s)
  then obtain f B where f: "continuous_map X euclidean f" "\<And>x. x\<in>topspace X \<Longrightarrow> \<bar>f x\<bar> \<le> B"
    "openin (pullback_topology {N. sets N = sets (borel_of X) \<and> finite_measure N} (\<lambda>N. \<integral>x. f x \<partial>N) euclideanreal) s"
    by blast
  then obtain u where u:
    "open u" "s = (\<lambda>N. \<integral>x. f x \<partial>N) -`u \<inter> {N. sets N = sets (borel_of X) \<and> finite_measure N}"
    unfolding openin_pullback_topology by auto
  with assms(2)[OF f(1,2)]
  show ?case
    using assms(1) continuous_map_open by fastforce
qed auto

lemma weak_conv_topology_continuous_map_integral:
  assumes "continuous_map X euclideanreal f" "\<And>x. x \<in> topspace X \<Longrightarrow> \<bar>f x\<bar> \<le> B"
  shows "continuous_map (weak_conv_topology X) euclideanreal (\<lambda>N. \<integral>x. f x \<partial>N)"
  unfolding continuous_map
proof safe
  fix U
  assume "openin euclideanreal U"
  then show "openin (weak_conv_topology X) {N \<in> topspace (weak_conv_topology X). (\<integral>x. f x \<partial>N) \<in> U}"
    unfolding weak_conv_topology_def openin_topology_generated_by_iff using assms
    by(auto intro!: Basis exI[where x=U] exI[where x=f] exI[where x=B] simp: openin_pullback_topology) blast
qed simp

subsection \<open>Weak Convergence\<close>
abbreviation weak_conv_on :: "('a \<Rightarrow> 'b measure) \<Rightarrow> 'b measure \<Rightarrow> 'a filter \<Rightarrow> 'b topology \<Rightarrow> bool"
   ( "'((_)/ \<Rightarrow>\<^sub>W\<^sub>C (_)') (_)/ on (_)" [56, 55] 55) where
"weak_conv_on Ni N F X \<equiv> limitin (weak_conv_topology X) Ni N F"

abbreviation weak_conv_on_seq :: "(nat \<Rightarrow> 'b measure) \<Rightarrow> 'b measure \<Rightarrow> 'b topology \<Rightarrow> bool"
   ( "'((_)/ \<Rightarrow>\<^sub>W\<^sub>C (_)') on (_)" [56, 55] 55) where
"weak_conv_on_seq Ni N X \<equiv> weak_conv_on Ni N sequentially X"

subsection \<open> Limit in Topology of Weak Convegence \<close>
lemma weak_conv_on_def:
 "weak_conv_on Ni N F X \<longleftrightarrow>
   (\<forall>\<^sub>F i in F. sets (Ni i) = sets (borel_of X) \<and> finite_measure (Ni i)) \<and> sets N = sets (borel_of X)
       \<and> finite_measure N
       \<and> (\<forall>f. continuous_map X euclideanreal f \<longrightarrow> (\<exists>B. \<forall>x\<in>topspace X. \<bar>f x\<bar> \<le> B)
               \<longrightarrow> ((\<lambda>i. \<integral>x. f x \<partial>Ni i) \<longlongrightarrow> (\<integral>x. f x \<partial>N)) F)"
proof safe
  assume h:"weak_conv_on Ni N F X"
  then have 1:"sets N = sets (borel_of X)" "finite_measure N"
    using limitin_topspace by fastforce+
  then show "\<And>x. x \<in> sets N \<Longrightarrow> x \<in> sets (borel_of X)" "\<And>x. x \<in> sets (borel_of X) \<Longrightarrow> x \<in> sets N"
    "finite_measure N"
    by auto
  show 2:"\<forall>\<^sub>F i in F. sets (Ni i) = sets (borel_of X) \<and> finite_measure (Ni i)"
    using h by(cases "F = \<bottom>") (auto simp: limitin_def)
  fix f B
  assume f:"continuous_map X euclideanreal f" and B:"\<forall>x\<in>topspace X. \<bar>f x\<bar> \<le> B"
  show "((\<lambda>n. \<integral>x. f x \<partial>Ni n) \<longlongrightarrow> (\<integral>x. f x \<partial>N)) F"
    unfolding tendsto_iff
  proof safe
    fix r :: real
    assume [arith]:"r > 0"
    then have "openin
                  (weak_conv_topology X)
                  ((\<lambda>N. \<integral>x. f x \<partial>N) -` (ball (\<integral>x. f x \<partial>N) r)
                    \<inter> {N. sets N = sets (borel_of X) \<and> finite_measure N})" (is "openin _ ?U")
      using f B by(auto intro!: openin_weak_conv_topology_base)
    moreover have "N \<in> ?U"
      using h by (simp add: 1)
    ultimately have NnU:"\<forall>\<^sub>F n in F. Ni n \<in> ?U"
      using h limitinD by fastforce
    show "\<forall>\<^sub>F n in F. dist (\<integral>x. f x \<partial>Ni n) (\<integral>x. f x \<partial>N) < r"
      by(auto intro!: eventuallyI[THEN eventually_mp[OF _ NnU]] simp: dist_real_def)
  qed
next
  assume h: "\<forall>\<^sub>F i in F. sets (Ni i) = sets (borel_of X) \<and> finite_measure (Ni i)"
             "sets N = sets (borel_of X)"
            "finite_measure N"
            "\<forall>f. continuous_map X euclideanreal f \<longrightarrow> (\<exists>B. \<forall>x\<in>topspace X. \<bar>f x\<bar> \<le> B)
                 \<longrightarrow> ((\<lambda>n. \<integral>x. f x \<partial>Ni n) \<longlongrightarrow> (\<integral>x. f x \<partial>N)) F"
  show "(Ni \<Rightarrow>\<^sub>W\<^sub>C N) F on X "
    unfolding limitin_def
  proof safe
    show "N \<in> topspace (weak_conv_topology X)"
      using h by auto
    fix U
    assume h':"openin (weak_conv_topology X) U" "N \<in> U"
    show "\<forall>\<^sub>F x in F. Ni x \<in> U"
      using h'[simplified weak_conv_topology_def openin_topology_generated_by_iff]
    proof induction
      case Empty
      then show ?case
        by simp
    next
      case (Int a b)
      then show ?case
        by (simp add: eventually_conj_iff)
    next
      case (UN K)
      then show ?case
        using UnionI eventually_mono by fastforce
    next
      case s:(Basis s)
      then obtain f where f: "continuous_map X euclidean f" "\<exists>B. \<forall>x\<in>topspace X. \<bar>f x\<bar> \<le> B"
        "openin (pullback_topology {N. sets N = sets (borel_of X) \<and>
         finite_measure N} (\<lambda>N. \<integral>x. f x \<partial>N) euclideanreal) s"
        by blast
      then obtain u where u:
        "open u" "s = (\<lambda>N. \<integral>x. f x \<partial>N) -`u \<inter> {N. sets N = sets (borel_of X) \<and> finite_measure N}"
        unfolding openin_pullback_topology by auto
      have "(\<integral>x. f x \<partial>N) \<in> u"
        using u s by blast
      moreover have "((\<lambda>n. \<integral>x. f x \<partial>Ni n) \<longlongrightarrow> (\<integral>x. f x \<partial>N)) F"
        using f h by blast
      ultimately have 1:"\<forall>\<^sub>F n in F.  (\<integral>x. f x \<partial>(Ni n)) \<in> u"
        by (simp add: tendsto_def u(1))
      show ?case
        by(auto intro!: eventuallyI[THEN eventually_mp[OF _ eventually_conj[OF 1 h(1)]]] simp: u(2))
    qed
  qed
qed

lemma weak_conv_on_def':
  assumes "\<And>i. sets (Ni i) = sets (borel_of X)" and "\<And>i. finite_measure (Ni i)"
    and "sets N = sets (borel_of X)" and "finite_measure N"
  shows "weak_conv_on Ni N F X
         \<longleftrightarrow> (\<forall>f. continuous_map X euclideanreal f \<longrightarrow> (\<exists>B. \<forall>x\<in>topspace X. \<bar>f x\<bar> \<le> B)
                   \<longrightarrow> ((\<lambda>i. \<integral>x. f x \<partial>Ni i) \<longlongrightarrow> (\<integral>x. f x \<partial>N)) F)"
  using assms by(auto simp: weak_conv_on_def)

lemmas weak_conv_seq_def = weak_conv_on_def[where F=sequentially]

lemma weak_conv_on_const:
  "(\<And>i. Ni i = N) \<Longrightarrow> sets N = sets (borel_of X)
   \<Longrightarrow> finite_measure N \<Longrightarrow> weak_conv_on Ni N F X"
  by(auto simp: weak_conv_on_def)

lemmas weak_conv_on_seq_const = weak_conv_on_const[where F=sequentially]

context Metric_space
begin

abbreviation "mweak_conv \<equiv> (\<lambda>Ni N F. weak_conv_on Ni N F mtopology)"
abbreviation "mweak_conv_seq \<equiv> \<lambda>Ni N. mweak_conv Ni N sequentially"

lemmas mweak_conv_def = weak_conv_on_def[where X=mtopology,simplified]
lemmas mweak_conv_seq_def = weak_conv_seq_def[where X=mtopology,simplified]

end

subsection \<open>The Portmanteau Theorem\<close>
locale mweak_conv_fin = Metric_space +
  fixes Ni :: "'b \<Rightarrow> 'a measure" and N :: "'a measure" and F
  assumes sets_Ni:"\<forall>\<^sub>F i in F. sets (Ni i) = sets (borel_of mtopology)"
      and sets_N[measurable_cong]: "sets N = sets (borel_of mtopology)"
      and finite_measure_Ni: "\<forall>\<^sub>F i in F. finite_measure (Ni i)"
      and finite_measure_N: "finite_measure N"
begin

interpretation N: finite_measure N
  by(simp add: finite_measure_N)

lemma space_N: "space N = M"
  using sets_eq_imp_space_eq[OF sets_N] by(auto simp: space_borel_of)

lemma space_Ni: "\<forall>\<^sub>F i in F. space (Ni i) = M"
  by(rule eventually_mp[OF _ sets_Ni]) (auto simp: space_borel_of cong: sets_eq_imp_space_eq)

lemma eventually_Ni: "\<forall>\<^sub>F i in F. space (Ni i) = M \<and> sets (Ni i) = sets (borel_of mtopology) \<and> finite_measure (Ni i)"
  by(intro eventually_conj space_Ni sets_Ni finite_measure_Ni)

lemma measure_converge_bounded':
  assumes "((\<lambda>n. measure (Ni n) M) \<longlongrightarrow> measure N M) F"
  obtains K where "\<And>A. \<forall>\<^sub>F x in F. measure (Ni x) A \<le> K" "\<And>A. measure N A \<le> K"
proof -
  have "measure N A \<le> measure N M + 1" for A
    using N.bounded_measure[of A] by(simp add: space_N)
  moreover have "\<forall>\<^sub>F x in F. measure (Ni x) A \<le> measure N M + 1" for A
  proof(rule eventuallyI[THEN eventually_mp[OF _ eventually_conj[OF eventually_Ni tendstoD[OF assms,of 1]]]])
    fix x
    show "(space (Ni x) = M \<and> sets (Ni x) = sets (borel_of mtopology) \<and> finite_measure (Ni x)) \<and>
          dist (measure (Ni x) M) (measure N M) < 1 \<longrightarrow> measure (Ni x) A \<le> measure N M + 1"
      using finite_measure.bounded_measure[of "Ni x" A]
      by(auto intro!: eventuallyI[THEN eventually_mp[OF _ tendstoD[OF assms,of 1]]] simp: dist_real_def)
  qed simp
  ultimately show ?thesis
    using that by blast
qed

lemma
  assumes "F \<noteq> \<bottom>" "\<forall>\<^sub>F x in F. measure (Ni x) A \<le> K" "measure N A \<le> K"
  shows Liminf_measure_bounded: "Liminf F (\<lambda>i. measure (Ni i) A) < \<infinity>" "0 \<le> Liminf F (\<lambda>i. measure (Ni i) A)"
  and Limsup_measure_bounded: "Limsup F (\<lambda>i. measure (Ni i) A) < \<infinity>" "0 \<le> Limsup F (\<lambda>i. measure (Ni i) A)"
proof -
  have "Liminf F (\<lambda>i. measure (Ni i) A) \<le> K" "Limsup F (\<lambda>i. measure (Ni i) A) \<le> K"
    using assms by(auto intro!: Liminf_le Limsup_bounded)
  thus "Liminf F (\<lambda>i. measure (Ni i) A) < \<infinity>" "Limsup F (\<lambda>i. measure (Ni i) A) < \<infinity>"
    by auto
  show "0 \<le> Liminf F (\<lambda>i. measure (Ni i) A)" "0 \<le> Limsup F (\<lambda>i. measure (Ni i) A)"
    by(auto intro!: le_Limsup Liminf_bounded assms)
qed

lemma mweak_conv1:
  fixes f:: "'a \<Rightarrow> real"
  assumes "mweak_conv Ni N F"
    and "uniformly_continuous_map Self euclidean_metric f"
  shows "(\<exists>B. \<forall>x\<in>M. \<bar>f x\<bar> \<le> B) \<Longrightarrow> ((\<lambda>n. integral\<^sup>L (Ni n) f) \<longlongrightarrow> integral\<^sup>L N f) F"
  using uniformly_continuous_imp_continuous_map[OF assms(2)] assms(1) by(auto simp: mweak_conv_def mtopology_of_def)

lemma mweak_conv2:
  assumes "\<And>f:: 'a \<Rightarrow> real. uniformly_continuous_map Self euclidean_metric f \<Longrightarrow> (\<exists>B. \<forall>x\<in>M. \<bar>f x\<bar> \<le> B)
           \<Longrightarrow> ((\<lambda>n. integral\<^sup>L (Ni n) f) \<longlongrightarrow> integral\<^sup>L N f) F"
    and "closedin mtopology A"
  shows "Limsup F (\<lambda>x. ereal (measure (Ni x) A)) \<le> ereal (measure N A)"
proof -
  consider "A = {}" | "F = \<bottom>" | "A \<noteq> {}" "F \<noteq> \<bottom>"
    by blast
  then show ?thesis
  proof cases
    assume "A = {}"
    then show ?thesis
      using Limsup_obtain linorder_not_less by fastforce
  next
    assume A_ne: "A \<noteq> {}" and F: "F \<noteq> \<bottom>"
    have A[measurable]: "A \<in> sets N" "\<forall>\<^sub>F i in F. A \<in> sets (Ni i)"
      using borel_of_closed[OF assms(2)] by(auto simp: sets_N eventually_mp[OF _ sets_Ni])
    have "((\<lambda>n. measure (Ni n) M) \<longlongrightarrow> measure N M) F"
    proof -
      have 1:"((\<lambda>n. measure (Ni n) (space (Ni n))) \<longlongrightarrow> measure N M) F"
        using assms(1)[of "\<lambda>x. 1"] by(auto simp: space_N)
      show ?thesis
        by(rule tendsto_cong[THEN iffD1,OF eventually_mp[OF _ space_Ni] 1]) simp
    qed
    then obtain K where K: "\<And>A. \<forall>\<^sub>F x in F. measure (Ni x) A \<le> K" "\<And>A. measure N A \<le> K"
      using measure_converge_bounded' by auto
    define Um where "Um \<equiv> (\<lambda>m. \<Union>a\<in>A. mball a (1 / Suc m))"
    have Um_open: "openin mtopology (Um m)" for m
      by(auto simp: Um_def)
    hence Um_m[measurable]: "\<And>m. Um m \<in> sets N" "\<And>m. \<forall>\<^sub>F i in F. Um m \<in> sets (Ni i)"
      by(auto simp: sets_N intro!: borel_of_open eventually_mono[OF sets_Ni])
    have A_Um: "A \<subseteq> Um m" for m
      using closedin_subset[OF assms(2)] by(fastforce simp: Um_def)
    have "\<exists>fm:: _ \<Rightarrow> real.  (\<forall>x. fm x \<ge> 0) \<and> (\<forall>x. fm x \<le> 1) \<and> (\<forall>x\<in>M - Um m. fm x = 0) \<and> (\<forall>x\<in>A. fm x = 1) \<and>
                            uniformly_continuous_map Self euclidean_metric fm" for m
    proof -
      have 1: "closedin mtopology (M - Um m)"
        using Um_open[of m] by(auto simp: closedin_def Diff_Diff_Int Int_absorb1)
      have 2: "A \<inter> (M - Um m) = {}"
        using A_Um[of m] by blast
      have 3: "1 / Suc m \<le> d x y" if "x \<in> A" "y \<in> M - Um m" for x y
      proof(rule ccontr)
        assume "\<not> 1 / real (Suc m) \<le> d x y"
        then have "d x y < 1 / (1 + real m)" by simp
        thus False
          using that closedin_subset[OF assms(2)] by(auto simp: Um_def)
      qed
      show ?thesis
        by (metis Urysohn_lemma_uniform[of Self,simplified mtopology_of_def,simplified,OF assms(2) 1 2 3,simplified] Diff_iff)
    qed
    then obtain fm :: "nat \<Rightarrow> _ \<Rightarrow> real" where fm: "\<And>m x. fm m x \<ge> 0" "\<And>m x. fm m x \<le> 1"
      "\<And>m x. x \<in> A \<Longrightarrow> fm m x = 1" "\<And>m x. x \<in> M \<Longrightarrow> x \<notin> Um m \<Longrightarrow> fm m x = 0"
      "\<And>m. uniformly_continuous_map Self euclidean_metric (fm m)"
      by (metis Diff_iff)
    have fm_m[measurable]: "\<And>m. \<forall>\<^sub>F i in F. fm m \<in> borel_measurable (Ni i)" "\<And>m. fm m \<in> borel_measurable N"
      using continuous_map_measurable[OF uniformly_continuous_imp_continuous_map[OF fm(5)]]
      by(auto simp: borel_of_euclidean mtopology_of_def eventually_mono[OF sets_Ni])
    have int_bounded:"\<forall>\<^sub>F n in F. (\<integral>x. fm m x \<partial>Ni n) \<le> K" for m
    proof(rule eventually_mono)
      show "\<forall>\<^sub>F n in F. space (Ni n) = M \<and> finite_measure (Ni n) \<and> fm m \<in> borel_measurable (Ni n) \<and>
                       (\<integral>x. fm m x \<partial>Ni n) \<le> (\<integral>x. 1 \<partial>Ni n) \<and> (\<integral>x. 1 \<partial>Ni n) \<le> K"
      proof(intro eventually_conj)
        show "\<forall>\<^sub>F n in F. (\<integral>x. fm m x \<partial>Ni n) \<le> (\<integral>x. 1 \<partial>Ni n)"
        proof(rule eventually_mono)
          show "\<forall>\<^sub>F n in F. space (Ni n) = M \<and> finite_measure (Ni n) \<and> fm m \<in> borel_measurable (Ni n)"
            by(intro eventually_conj space_Ni finite_measure_Ni fm_m)
          show "space (Ni n) = M \<and> finite_measure (Ni n) \<and> fm m \<in> borel_measurable (Ni n)
                \<Longrightarrow> (\<integral>x. fm m x \<partial>Ni n) \<le> (\<integral>x. 1 \<partial>Ni n)" for n
            by(rule integral_mono, insert fm) (auto intro!: finite_measure.integrable_const_bound[where B=1])
        qed
        show "\<forall>\<^sub>F n in F. (\<integral>x. 1 \<partial>Ni n) \<le> K"
          by(rule eventually_mono[OF eventually_conj[OF K(1)[of M] space_Ni]]) simp
      qed(auto simp: space_Ni finite_measure_Ni fm_m)
    qed simp
    have 1: "Limsup F (\<lambda>n. measure (Ni n) A) \<le> measure N (Um m)" for m
    proof -
      have "Limsup F (\<lambda>n. measure (Ni n) A) = Limsup F (\<lambda>n. \<integral>x. indicat_real A x \<partial>Ni n)"
        by(intro Limsup_eq[OF eventually_mono[OF A(2)]]) simp
      also have "... \<le> Limsup F (\<lambda>n. \<integral>x. fm m x \<partial>Ni n)"
      proof(safe intro!: eventuallyI[THEN Limsup_mono[OF eventually_mp[OF _ eventually_conj[OF fm_m(1)[of m]
                  eventually_conj[OF finite_measure_Ni eventually_conj[OF A(2) int_bounded[of m]]]]]]])
        fix n
        assume h:"(\<integral>x. fm m x \<partial>Ni n) \<le> K" "A \<in> sets (Ni n)" "finite_measure (Ni n)" "fm m \<in> borel_measurable (Ni n)"
        with fm show "ereal (\<integral>x. indicat_real A x \<partial>Ni n) \<le> ereal (\<integral>x. fm m x \<partial>Ni n)"
          by(auto intro!: Limsup_mono integral_mono finite_measure.integrable_const_bound[where B=1]
              simp del: Bochner_Integration.integral_indicator) (auto simp: indicator_def)
      qed
      also have "... = (\<integral>x. fm m x \<partial>N)"
        using fm by(auto intro!: lim_imp_Limsup[OF F tendsto_ereal[OF assms(1)[OF fm(5)[of m]]]] exI[where x=1])
      also have "... \<le> (\<integral>x. indicat_real (Um m) x \<partial>N)"
        unfolding ereal_less_eq(3) by(rule integral_mono, insert fm(4)[of _ m] fm(1,2))
          (auto intro!: N.integrable_const_bound[where B=1],auto simp: indicator_def space_N)
      also have "... = measure N (Um m)"
        by simp
      finally show ?thesis .
    qed
    have 2: "(\<lambda>n. measure N (Um n)) \<longlonglongrightarrow> measure N A"
    proof -
      have [simp]: "(\<Inter> (range Um)) = A"
        unfolding Um_def
        by(rule nbh_Inter_closure_of[OF A_ne _ _ _ LIMSEQ_Suc,simplified closure_of_closedin[OF assms(2)]],
           insert sets.sets_into_space[OF A(1)])
         (auto intro!: decseq_SucI simp: frac_le space_N lim_1_over_n)
      have [simp]: "monotone (\<le>) (\<lambda>x y. y \<subseteq> x) Um"
        unfolding Um_def by(rule nbh_decseq) (auto intro!: decseq_SucI simp: frac_le)
      have "(\<lambda>n. measure N (Um n)) \<longlonglongrightarrow> measure N (\<Inter> (range Um))"
        by(rule N.finite_Lim_measure_decseq) auto
      thus ?thesis by simp
    qed
    show ?thesis
      using 1 by(auto intro!: Lim_bounded2[OF tendsto_ereal[OF 2]])
  qed simp
qed

lemma mweak_conv3:
  assumes "\<And>A. closedin mtopology A \<Longrightarrow> Limsup F (\<lambda>n. measure (Ni n) A) \<le> measure N A"
      and "((\<lambda>n. measure (Ni n) M) \<longlongrightarrow> measure N M) F"
      and "openin mtopology U"
    shows "measure N U \<le> Liminf F (\<lambda>n. measure (Ni n) U)"
proof(cases "F = \<bottom>")
  assume F: "F \<noteq> \<bottom>"
  obtain K where K: "\<And>A. \<forall>\<^sub>F x in F. measure (Ni x) A \<le> K" "\<And>A. measure N M \<le> K"
    using measure_converge_bounded'[OF assms(2)] by metis
  have U[measurable]: "U \<in> sets N" "\<forall>\<^sub>F i in F. U \<in> sets (Ni i)"
    by(auto simp: sets_N borel_of_open assms eventually_mono[OF sets_Ni])
  have "ereal (measure N U) = measure N M - measure N (M - U)"
    by(simp add: N.finite_measure_compl[simplified space_N])
  also have "... \<le> measure N M - Limsup F (\<lambda>n. measure (Ni n) (M - U))"
    using assms(1)[OF openin_closedin[THEN iffD1,OF _ assms(3)]] openin_subset[OF assms(3)]
    by (metis ereal_le_real ereal_minus(1) ereal_minus_mono topspace_mtopology) 
  also have "... = measure N M + Liminf F (\<lambda>n. - ereal (measure (Ni n) (M - U)))"
    by (metis ereal_Liminf_uminus minus_ereal_def)
  also have "...  = Liminf F (\<lambda>n. measure (Ni n) M) + Liminf F (\<lambda>n. - measure (Ni n) (M - U))"
    using tendsto_iff_Liminf_eq_Limsup[OF F,THEN iffD1,OF tendsto_ereal[OF assms(2)]] by simp
  also have "... \<le> Liminf F (\<lambda>n. ereal (measure (Ni n) M) + ereal (- measure (Ni n) (M - U)))"
    by(rule ereal_Liminf_add_mono) (use Liminf_measure_bounded[OF F K] in auto)
  also have "... = Liminf F (\<lambda>n. measure (Ni n) U)"
    by(auto intro!: Liminf_eq eventually_mono[OF eventually_conj[OF U(2) eventually_conj[OF space_Ni finite_measure_Ni]]]
        simp: finite_measure.finite_measure_compl)
  finally show ?thesis .
qed simp

lemma mweak_conv3':
  assumes "\<And>U. openin mtopology U \<Longrightarrow> measure N U \<le> Liminf F (\<lambda>n. measure (Ni n) U)"
      and "((\<lambda>n. measure (Ni n) M) \<longlongrightarrow> measure N M) F"
      and "closedin mtopology A"
    shows "Limsup F (\<lambda>n. measure (Ni n) A) \<le> measure N A"
proof(cases "F = \<bottom>")
  assume F: "F \<noteq> \<bottom>"
  have A[measurable]: "A \<in> sets N""\<forall>\<^sub>F i in F. A \<in> sets (Ni i)"
    by(auto simp: sets_N borel_of_closed assms eventually_mono[OF sets_Ni])
  have "Limsup F (\<lambda>n. measure (Ni n) A) = Limsup F (\<lambda>n. ereal (measure (Ni n) M) + ereal (- measure (Ni n) (M - A)))"
    by(auto intro!: Limsup_eq eventually_mono[OF eventually_conj[OF A(2) eventually_conj[OF space_Ni finite_measure_Ni]]]
        simp: finite_measure.finite_measure_compl)
  also have "... \<le> Limsup F (\<lambda>n. measure (Ni n) M) + Limsup F (\<lambda>n. - measure (Ni n) (M - A))"
    by(rule ereal_Limsup_add_mono)
  also have "... =  Limsup F (\<lambda>n. measure (Ni n) M) + Limsup F (\<lambda>n. - ereal ( measure (Ni n) (M - A)))"
    by simp
  also have "... = Limsup F (\<lambda>n. measure (Ni n) M) - Liminf F (\<lambda>n. measure (Ni n) (M - A))"
    unfolding ereal_Limsup_uminus using minus_ereal_def by presburger 
  also have "... = measure N M - Liminf F (\<lambda>n. measure (Ni n) (M - A))"
    by(simp add: lim_imp_Limsup[OF F tendsto_ereal[OF assms(2)]])
  also have "... \<le> measure N M - measure N (M - A)"
    using assms(1)[OF openin_diff[OF openin_topspace assms(3)]] closedin_subset[OF assms(3)]
    by (metis assms(1,3) ereal_le_real ereal_minus(1) ereal_minus_mono open_in_mspace openin_diff) 
  also have "... = measure N A"
    by(simp add: N.finite_measure_compl[simplified space_N])
  finally show ?thesis .
qed simp

lemma mweak_conv4:
  assumes "\<And>A. closedin mtopology A \<Longrightarrow> Limsup F (\<lambda>n. measure (Ni n) A) \<le> measure N A"
      and "\<And>U. openin mtopology U \<Longrightarrow> measure N U \<le> Liminf F (\<lambda>n. measure (Ni n) U)"
      and [measurable]: "A \<in> sets (borel_of mtopology)"
      and "measure N (mtopology frontier_of A) = 0"
    shows "((\<lambda>n. measure (Ni n) A) \<longlongrightarrow> measure N A) F"
proof(cases "F = \<bottom>")
  assume F: "F \<noteq> \<bottom>"
  have [measurable]: "A \<in> sets N" "mtopology closure_of A \<in> sets N" "mtopology interior_of A \<in> sets N"
    "mtopology frontier_of A \<in> sets N"
    and A: "\<forall>\<^sub>F i in F. A \<in> sets (Ni i)" "\<forall>\<^sub>F i in F. mtopology closure_of A \<in> sets (Ni i)"
    "\<forall>\<^sub>F i in F. mtopology interior_of A \<in> sets (Ni i)" "\<forall>\<^sub>F i in F. mtopology frontier_of A \<in> sets (Ni i)"
    by(auto simp: sets_N borel_of_open borel_of_closed closedin_frontier_of eventually_mono[OF sets_Ni])
  have "Limsup F (\<lambda>n. measure (Ni n) A) \<le> Limsup F (\<lambda>n. measure (Ni n) (mtopology closure_of A))"
    using sets.sets_into_space[OF assms(3)]
    by(fastforce intro!: Limsup_mono finite_measure.finite_measure_mono[OF _ closure_of_subset]
        eventually_mono[OF eventually_conj[OF finite_measure_Ni A(2)]] simp: space_borel_of)
  also have "... \<le> measure N (mtopology closure_of A)"
    by(auto intro!: assms(1))
  also have "... \<le> measure N (A \<union> (mtopology frontier_of A))"
    using closure_of_subset[of A mtopology] sets.sets_into_space[OF assms(3)] interior_of_subset[of mtopology A]
    by(auto simp: space_borel_of interior_of_union_frontier_of[symmetric]
        simp del: interior_of_union_frontier_of intro!: N.finite_measure_mono)
  also have "... \<le> measure N A + measure N (mtopology frontier_of A)"
    by(simp add: N.finite_measure_subadditive)
  also have "... = measure N A" by(simp add: assms)
  finally have 1: "Limsup F (\<lambda>n. measure (Ni n) A) \<le> measure N A" .
  have "ereal (measure N A) = measure N A - measure N (mtopology frontier_of A)"
    by(simp add: assms)
  also have "... \<le> measure N (A - mtopology frontier_of A)"
    by(auto simp: N.finite_measure_Diff' intro!: N.finite_measure_mono)
  also have "... \<le> measure N (mtopology interior_of A)"
    using closure_of_subset[OF sets.sets_into_space[OF assms(3),simplified space_borel_of]]
    by(auto intro!: N.finite_measure_mono simp: frontier_of_def)
  also have "... \<le> Liminf F (\<lambda>n. measure (Ni n) (mtopology interior_of A))"
    by(auto intro!: assms)
  also have "... \<le> Liminf F (\<lambda>n. measure (Ni n) A)"
    by(fastforce intro!: Liminf_mono finite_measure.finite_measure_mono interior_of_subset
        eventually_mono[OF eventually_conj[OF finite_measure_Ni A(1)]])
  finally have 2: "measure N A \<le> Liminf F (\<lambda>n. measure (Ni n) A)" .
  have "Liminf F (\<lambda>n. measure (Ni n) A) = measure N A \<and> Limsup F (\<lambda>n. measure (Ni n) A) = measure N A"
    using 1 2 order.trans[OF 2 Liminf_le_Limsup[OF F]] order.trans[OF Liminf_le_Limsup[OF F] 1] antisym
    by blast
  thus ?thesis
    by (metis F lim_ereal tendsto_Limsup)
qed simp

lemma mweak_conv5:
  assumes "\<And>A. A \<in> sets (borel_of mtopology) \<Longrightarrow> measure N (mtopology frontier_of A) = 0
                \<Longrightarrow> ((\<lambda>n. measure (Ni n) A) \<longlongrightarrow> measure N A) F"
  shows "mweak_conv Ni N F"
proof(cases "F = \<bottom>")
  assume F: "F \<noteq> \<bottom>"
  show ?thesis
    unfolding mweak_conv_def
  proof safe
    fix f B
    assume h:"continuous_map mtopology euclideanreal f" "\<forall>x\<in>M. \<bar>f x\<bar> \<le> B"
    have "((\<lambda>n. measure (Ni n) M) \<longlongrightarrow> measure N M) F"
      using frontier_of_topspace[of mtopology] by(auto intro!: assms borel_of_open)
    then obtain K where K: "\<And>A. \<forall>\<^sub>F x in F. measure (Ni x) A \<le> K" "\<And>A. measure N A \<le> K"
      using measure_converge_bounded' by metis
    from continuous_map_measurable[OF h(1)]
    have f[measurable]:"f \<in> borel_measurable N" "\<forall>\<^sub>F i in F. f \<in> borel_measurable (Ni i)"
      by(auto cong: measurable_cong_sets simp: sets_N borel_of_euclidean intro!: eventually_mono[OF sets_Ni])
    have f_int[simp]: "integrable N f" "\<forall>\<^sub>F i in F. integrable (Ni i) f"
      using h by(auto intro!: N.integrable_const_bound[where B=B] finite_measure.integrable_const_bound[where B=B]
          eventually_mono[OF eventually_conj[OF eventually_conj[OF space_Ni f(2)] finite_measure_Ni]] simp: space_N)
    show "((\<lambda>n. \<integral>x. f x \<partial>Ni n) \<longlongrightarrow> (\<integral>x. f x \<partial>N)) F"
    proof(cases "B > 0")
      case False
      with h(2) have 1:"\<And>x. x \<in> space N \<Longrightarrow> f x = 0" "\<forall>\<^sub>F i in F. \<forall>x. x \<in> space (Ni i) \<longrightarrow> f x = 0"
        by (fastforce simp: space_N intro!: eventually_mono[OF space_Ni])+
      thus ?thesis
        by(auto cong: Bochner_Integration.integral_cong
            intro!: tendsto_cong[where g="\<lambda>x. 0" and f="(\<lambda>n. \<integral>x. f x \<partial>Ni n)",THEN iffD2] eventually_mono[OF 1(2)])
    next
      case B[arith]:True
      show ?thesis
      proof(cases "K > 0")
        case False
        then have 1:"measure N A = 0" "\<forall>\<^sub>F x in F. measure (Ni x) M = 0" for A
          using K(2)[of A] measure_nonneg[of _ A] measure_le_0_iff
          by(fastforce intro!: eventuallyI[THEN eventually_mp[OF _ K(1)[of M]]])+
        hence "N = null_measure (borel_of mtopology)"
          by(auto intro!: measure_eqI simp: sets_N N.emeasure_eq_measure)
        moreover have "\<forall>\<^sub>F x in F. Ni x = null_measure (borel_of mtopology)"
          using order.trans[where c=0,OF finite_measure.bounded_measure]
          by(intro eventually_mono[OF eventually_conj[OF eventually_conj[OF space_Ni eventually_conj[OF finite_measure_Ni sets_Ni]] 1(2)]] measure_eqI)
            (auto simp: finite_measure.emeasure_eq_measure measure_le_0_iff)
        ultimately show ?thesis
          by (simp add: eventually_mono tendsto_eventually)
      next
        case [arith]:True
        show ?thesis
          unfolding tendsto_iff LIMSEQ_def dist_real_def
        proof safe
          fix r :: real
          assume r[arith]: "r > 0"
          define \<nu> where "\<nu> \<equiv> distr N borel f"
          have sets_nu[measurable_cong, simp]: "sets \<nu> = sets borel"
            by(simp add: \<nu>_def)
          interpret \<nu>: finite_measure \<nu>
            by(auto simp: \<nu>_def N.finite_measure_distr)
          have "(1 / 6) * (r / K) * (1 / B) > 0"
            by auto        
          from nat_approx_posE[OF this]
          obtain N' where N': "1 / (Suc N') < (1 / 6) * (r / K) * (1 / B)"
            by auto
          from mult_strict_right_mono[OF this B] have N'':"B / (Suc N') <  (1 / 6) * (r / K)"
            by auto
          have "\<exists>tn \<in> {B / Suc N' * (real n - 1) - B<..<B / Suc N' * real n - B}. measure \<nu> {tn} = 0" for n
          proof(rule ccontr)
            assume "\<not> (\<exists>tn \<in> {B / Suc N' * (real n - 1) - B<..<B / Suc N' * real n - B}. measure \<nu> {tn} = 0)"
            then have "{B / Suc N' * (real n - 1) - B<..<B / Suc N' * real n - B} \<subseteq> {x. measure \<nu> {x} \<noteq> 0}"
              by auto
            moreover have "uncountable {B / Suc N' * (real n - 1) - B<..<B / Suc N' * real n - B}"
              unfolding uncountable_open_interval right_diff_distrib by auto
            ultimately show False
              using \<nu>.countable_support by(meson countable_subset)
          qed
          then obtain tn where tn: "\<And>n. B / Suc N' * (real n - 1) - B < tn n" "\<And>n. tn n < B / Suc N' * real n - B"
            "\<And>n. measure \<nu> {tn n} = 0"
            by (metis greaterThanLessThan_iff)
          have t0: "tn 0 < - B"
            using tn(2)[of 0] by simp
          have tN: "B < tn (Suc (2 * (Suc N')))" 
          proof -
            have "B * (2 + 2 * real N') / (1 + real N') = 2 * B"
              by(auto simp: divide_eq_eq)
            with tn(1)[of "Suc (2 * (Suc N'))"] show ?thesis
              by simp
          qed
          define Aj where "Aj \<equiv> (\<lambda>j. f -` {tn j..<tn (Suc j)} \<inter> M)"
          have sets_Aj[measurable]: "\<And>j. Aj j \<in> sets N" "\<forall>\<^sub>F i in F.  \<forall>j. Aj j \<in> sets (Ni i)"
            using measurable_sets[OF f(1)]
            by(auto simp: Aj_def space_N intro!: eventually_mono[OF eventually_conj[OF space_Ni f(2)]])
          have m_f: "measure N (mtopology frontier_of (Aj j)) = 0" for j
          proof -
            have "measure N (mtopology frontier_of (Aj j)) = measure N (mtopology closure_of (Aj j) - mtopology interior_of (Aj j))"
              by(simp add: frontier_of_def)
            also have "... \<le> measure \<nu> {tn j, tn (Suc j)}"
            proof -
              have [simp]: "{x \<in> M. tn j \<le> f x \<and> f x \<le> tn (Suc j)} = f -` {tn j..tn (Suc j)} \<inter> M"
                "{x \<in> M. tn j < f x \<and> f x < tn (Suc j)} =  f -` {tn j<..<tn (Suc j)} \<inter> M"
                by auto
              have "mtopology closure_of (Aj j) \<subseteq>  f -` {tn j..tn (Suc j)} \<inter> M"
                by(rule closure_of_minimal,insert closedin_continuous_map_preimage[OF h(1),of "{tn j..tn (Suc j)}"])
                  (auto simp: Aj_def)
              moreover have "f -` {tn j<..<tn (Suc j)} \<inter> M \<subseteq> mtopology interior_of (Aj j)"
                by(rule interior_of_maximal,insert openin_continuous_map_preimage[OF h(1),of "{tn j<..<tn (Suc j)}"])
                  (auto simp: Aj_def)
              ultimately have "mtopology closure_of (Aj j) - mtopology interior_of (Aj j) \<subseteq> f -` {tn j,tn (Suc j)} \<inter> M"
                by(fastforce dest: contra_subsetD)
              with closedin_subset[OF closedin_closure_of,of mtopology "Aj j"] show ?thesis
                by(auto simp: \<nu>_def measure_distr intro!: N.finite_measure_mono) (auto simp: space_N)
            qed
            also have "... \<le> measure \<nu> {tn j} + measure \<nu> {tn (Suc j)}"
              using \<nu>.finite_measure_subadditive[of "{tn (Suc j)}" "{tn j}"] by auto
            also have "... = 0"
              by(simp add: tn)
            finally show ?thesis
              by (simp add: measure_le_0_iff)
          qed
          hence conv:"((\<lambda>n. measure (Ni n) (Aj j)) \<longlongrightarrow> measure N (Aj j)) F" for j
            by(auto intro!: assms simp: sets_N[symmetric] sets_Ni)
          have fil1:"\<forall>\<^sub>F n in F. \<bar>tn j\<bar> * \<bar>measure (Ni n) (Aj j) - measure N (Aj j)\<bar> < r / (3 * (Suc (Suc (2 * Suc N'))))" for j
          proof(cases "\<bar>tn j\<bar> = 0")
            case pos:False
            then have "r / (3 * (Suc (Suc (2 * Suc N')))) * (1 / \<bar>tn j\<bar>) > 0"
              by auto
            with conv[of j]
            have 1:"\<forall>\<^sub>F n in F. \<bar>measure (Ni n) (Aj j) - measure N (Aj j)\<bar>
                                 < r / (3 * (Suc (Suc (2 * Suc N')))) * (1 / \<bar>tn j\<bar>)"
              unfolding tendsto_iff dist_real_def by metis
            have "\<forall>\<^sub>F n in F. \<bar>tn j\<bar> * \<bar>measure (Ni n) (Aj j) - measure N (Aj j)\<bar> < r / (3 * (Suc (Suc (2 * Suc N'))))"
            proof(rule eventuallyI[THEN eventually_mp[OF _ 1]])
              show "\<bar>measure (Ni n) (Aj j) - measure N (Aj j)\<bar> < r / real (3 * Suc (Suc (2 * Suc N'))) * (1 / \<bar>tn j\<bar>)
                    \<longrightarrow> \<bar>tn j\<bar> * \<bar>measure (Ni n) (Aj j) - measure N (Aj j)\<bar> < r / real (3 * Suc (Suc (2 * Suc N')))" for n          
                using mult_less_cancel_right_pos[of "\<bar>tn j\<bar>" "\<bar>measure (Ni n) (Aj j) - measure N (Aj j)\<bar>"
                    "r / real (3 * Suc (Suc (2 * Suc N'))) * (1 / \<bar>tn j\<bar>)"] pos by(simp add: mult.commute)
            qed
            thus ?thesis by auto
          qed auto
          hence fil1:"\<forall>\<^sub>F n in F. \<forall>j\<in>{..Suc (2 * Suc N')}. \<bar>tn j\<bar> * \<bar>measure (Ni n) (Aj j) - measure N (Aj j)\<bar>
                                                           < r / (3 * (Suc (Suc (2 * Suc N'))))"
            by(auto intro!: eventually_ball_finite)
          have tn_strictmono: "strict_mono tn"
            unfolding strict_mono_Suc_iff
          proof safe
            fix n
            show "tn n < tn (Suc n)"
              using tn(1)[of "Suc n"] tn(2)[of n] by auto
          qed
          from strict_mono_less[OF this] have Aj_disj: "disjoint_family Aj"
            by(auto simp: disjoint_family_on_def Aj_def) (metis linorder_not_le not_less_eq order_less_le order_less_trans)
          have Aj_un: "M = (\<Union>i\<in>{..Suc (2 * Suc N')}. Aj i)"
          proof
            show "M \<subseteq> \<Union> (Aj ` {..Suc (2 * Suc N')})"
            proof
              fix x
              assume x:"x \<in> M"
              with h(2) tN t0 have h':"tn 0 < f x" "f x < tn (Suc (2 * Suc N'))"
                by fastforce+
              define n where "n \<equiv> LEAST n. f x < tn (Suc n)"
              have "f x < tn (Suc n)"
                unfolding n_def by(rule LeastI_ex) (use h' in auto)
              moreover have "tn n \<le> f x"
                by (metis Least_le Suc_n_not_le_n h'(1) less_eq_real_def linorder_not_less n_def not0_implies_Suc)
              moreover have "n \<le> 2 * Suc N'"
                unfolding n_def by(rule Least_le) (use h' in auto)
              ultimately show "x \<in> \<Union> (Aj ` {..Suc (2 * Suc N')})"
                by(auto simp: Aj_def x)
            qed
          qed(auto simp: Aj_def)
          define h where "h \<equiv> (\<lambda>x. \<Sum>i\<le>Suc (2 * (Suc N')). tn i * indicat_real (Aj i) x)"
          have h[measurable]: "h \<in> borel_measurable N" "\<forall>\<^sub>F i in F. h \<in> borel_measurable (Ni i)"
            by(auto simp: h_def simp del: sum.atMost_Suc sum_mult_indicator intro!: borel_measurable_sum eventually_mono[OF sets_Aj(2)])
          have h_f: "h x \<le> f x" if "x \<in> M" for x
          proof -
            from that disjoint_family_onD[OF Aj_disj]
            obtain n where n: "x \<in> Aj n" "n \<le> Suc (2 * Suc N')" "\<And>m. m \<noteq> n \<Longrightarrow> x \<notin> Aj m"
              by(auto simp: Aj_un)
            have "h x = (\<Sum>i\<le>Suc (2 * (Suc N')). if i = n then tn i else 0)"
              unfolding h_def by(rule Finite_Cartesian_Product.sum_cong_aux) (use n in auto)
            also have "... = tn n"
              using n by auto
            also have "... \<le> f x"
              using n(1) by(auto simp: Aj_def)
            finally show ?thesis .
          qed
          have f_h: "f x < h x + (1 / 3) * (r / enn2real K)" if "x \<in> M" for x
          proof -
            from that disjoint_family_onD[OF Aj_disj]
            obtain n where n: "x \<in> Aj n" "n \<le> Suc (2 * Suc N')" "\<And>m. m \<noteq> n \<Longrightarrow> x \<notin> Aj m"
              by(auto simp: Aj_un)
            have "h x = (\<Sum>i\<le>Suc (2 * (Suc N')). if i = n then tn i else 0)"
              unfolding h_def by(rule Finite_Cartesian_Product.sum_cong_aux) (use n in auto)
            also have "... = tn n"
              using n by auto
            finally have hx: "h x = tn n" .
            have "f x < tn (Suc n)"
              using n by(auto simp: Aj_def)
            hence "f x - tn n < tn (Suc n) - tn n" by auto
            also have "... < B / real (Suc N') * real (Suc n) - (B / real (Suc N') * (real n - 1))"
              using tn(1)[of n] tn(2)[of "Suc n"] by auto
            also have "... = 2 * B / real (Suc N')"
              by(auto simp: diff_divide_distrib[symmetric]) (simp add: ring_distribs(1) right_diff_distrib)
            also have "... < (1 / 3) * (r / enn2real K)"
              using N'' by auto
            finally show ?thesis
              using hx by simp
          qed
          with h_f have fh:"\<And>x. x \<in> M \<Longrightarrow> \<bar>f x - h x\<bar> <  (1 / 3) * (r / enn2real K)"
            by fastforce
          have h_bounded: "\<bar>h x\<bar> \<le> (\<Sum>i\<le>Suc (2 * (Suc N')). \<bar>tn i\<bar>)" for x
            unfolding h_def by(rule order.trans[OF sum_abs[of "\<lambda>i. tn i * indicat_real (Aj i) x"
                    "{..Suc (2 * (Suc N'))}"] sum_mono]) (auto simp: indicator_def)
          hence h_int[simp]: "integrable N h" "\<forall>\<^sub>F i in F. integrable (Ni i) h"
            by(auto intro!: N.integrable_const_bound[where B="\<Sum>i\<le>Suc (2 * (Suc N')). \<bar>tn i\<bar>"]
                finite_measure.integrable_const_bound[where B="\<Sum>i\<le>Suc (2 * (Suc N')). \<bar>tn i\<bar>"]
                eventually_mono[OF eventually_conj[OF finite_measure_Ni h(2)]])
          show "\<forall>\<^sub>F n in F. \<bar>(\<integral>x. f x \<partial>Ni n) - (\<integral>x. f x \<partial>N)\<bar> < r"
          proof(safe intro!: eventually_mono[OF eventually_conj[OF K(1)[of M]
                                eventually_conj[OF eventually_conj[OF fil1 h_int(2)]
                                   eventually_conj[OF f_int(2)
                                      eventually_conj[OF eventually_conj[OF finite_measure_Ni space_Ni]
                                                         sets_Aj(2)]]]]])
            fix n
            assume n:"\<forall>j\<in>{..Suc (2 * Suc N')}.
              \<bar>tn j\<bar> * \<bar>measure (Ni n) (Aj j) - measure N (Aj j)\<bar> < r / real (3 * Suc (Suc (2 * Suc N')))"
                     "measure (Ni n) (space (Ni n)) \<le> K"
               and h_intn[simp]:"integrable (Ni n) h" and f_intn[simp]:"integrable (Ni n) f"
               and sets_Aj2[measurable]:"\<forall>j. Aj j \<in> sets (Ni n)"
               and space_Ni:"M = space (Ni n)"
               and "finite_measure (Ni n)"
            interpret Ni: finite_measure "(Ni n)" by fact
            have "\<bar>(\<integral>x. f x \<partial>Ni n) - (\<integral>x. f x \<partial>N)\<bar>
                   = \<bar>(\<integral>x. f x - h x \<partial>Ni n) + ((\<integral>x. h x \<partial>Ni n) - (\<integral>x. h x \<partial>N)) - (\<integral>x. f x - h x \<partial>N)\<bar>"
              by(simp add: Bochner_Integration.integral_diff[OF f_int(1) h_int(1)] Bochner_Integration.integral_diff[OF f_intn h_intn])
            also have "... \<le> \<bar>\<integral>x. f x - h x \<partial>Ni n\<bar> + \<bar>(\<integral>x. h x \<partial>Ni n) - (\<integral>x. h x \<partial>N)\<bar> + \<bar>\<integral>x. f x - h x \<partial>N\<bar>"
              by linarith
            also have "... \<le> (\<integral>x. \<bar>f x - h x\<bar> \<partial>Ni n) + \<bar>(\<integral>x. h x \<partial>Ni n) - (\<integral>x. h x \<partial>N)\<bar> + (\<integral>x. \<bar>f x - h x\<bar> \<partial>N)"
              using integral_abs_bound by (simp add: add_mono del: f_int f_intn)
            also have "... \<le> r / 3 + \<bar>(\<integral>x. h x \<partial>Ni n) - (\<integral>x. h x \<partial>N)\<bar> + r / 3"
            proof -
              have "(\<integral>x. \<bar>f x - h x\<bar> \<partial>Ni n) \<le> (\<integral>x. (1 / 3) * (r / enn2real K) \<partial>Ni n)"
                by(rule integral_mono) (insert fh, auto simp: space_Ni order.strict_implies_order)
              also have "... = measure (Ni n) (space (Ni n)) / K * (r / 3)"
                by auto
              also have "... \<le> r / 3"
                by(rule mult_left_le_one_le) (use n space_Ni in auto)
              finally have 1:"(\<integral>x. \<bar>f x - h x\<bar> \<partial>Ni n) \<le> r / 3" .
              have "(\<integral>x. \<bar>f x - h x\<bar> \<partial>N) \<le> (\<integral>x. (1 / 3) * (r / K) \<partial>N)"
                by(rule integral_mono) (insert fh, auto simp: space_N order.strict_implies_order)
              also have "... = measure N (space N) / enn2real K * (r / 3)"
                by auto
              also have "... \<le> r / 3"
                by(rule mult_left_le_one_le) (use K space_N in auto)
              finally show ?thesis
                using 1 by auto
            qed
            also have "... < r"
            proof -
              have "\<bar>(\<integral>x. h x \<partial>Ni n) - (\<integral>x. h x \<partial>N)\<bar>
                    = \<bar>(\<integral>x. (\<Sum>i\<le>Suc (2 * (Suc N')). tn i * indicat_real (Aj i) x) \<partial>Ni n)
                       - (\<integral>x. (\<Sum>i\<le>Suc (2 * (Suc N')). tn i * indicat_real (Aj i) x) \<partial>N)\<bar>"
                by(simp add: h_def)
              also have "... = \<bar>(\<Sum>i\<le>Suc (2 * (Suc N')). (\<integral>x. tn i * indicat_real (Aj i) x \<partial>Ni n))
                                - (\<Sum>i\<le>Suc (2 * (Suc N')). (\<integral>x. tn i * indicat_real (Aj i) x \<partial>N))\<bar>"
              proof -
                have 1: "(\<integral>x. (\<Sum>i\<le>Suc (2 * (Suc N')). tn i * indicat_real (Aj i) x) \<partial>Ni n)
                          = (\<Sum>i\<le>Suc (2 * (Suc N')). (\<integral>x. tn i * indicat_real (Aj i) x \<partial>Ni n))"
                  by(rule Bochner_Integration.integral_sum) (use integrable_real_mult_indicator sets_Aj2 in blast) 
                have 2: "(\<integral>x. (\<Sum>i\<le>Suc (2 * (Suc N')). tn i * indicat_real (Aj i) x) \<partial>N)
                          = (\<Sum>i\<le>Suc (2 * (Suc N')). (\<integral>x. tn i * indicat_real (Aj i) x \<partial>N))"
                  by(rule Bochner_Integration.integral_sum) (use integrable_real_mult_indicator sets_Aj(1) in blast) 
                show ?thesis
                  by(simp only: 1 2)
              qed
              also have "... = \<bar>(\<Sum>i\<le>Suc (2 * (Suc N')). tn i * measure (Ni n) (Aj i))
                                - (\<Sum>i\<le>Suc (2 * (Suc N')). tn i * measure N (Aj i))\<bar>"
                by simp
              also have "... = \<bar>\<Sum>i\<le>Suc (2 * (Suc N')). tn i * (measure (Ni n) (Aj i) - measure N (Aj i))\<bar>"
                by(auto simp: sum_subtractf right_diff_distrib)
              also have "... \<le> (\<Sum>i\<le>Suc (2 * (Suc N')). \<bar>tn i * (measure (Ni n) (Aj i) - measure N (Aj i))\<bar>)"
                by(rule sum_abs)
              also have "... \<le> (\<Sum>i\<le>Suc (2 * (Suc N')). \<bar>tn i\<bar> * \<bar>(measure (Ni n) (Aj i) - measure N (Aj i))\<bar>)"
                by(simp add: abs_mult)
              also have "... < (\<Sum>i\<le>Suc (2 * (Suc N')). r / (3 * (Suc (Suc (2 * Suc N')))))"
                by(rule sum_strict_mono) (use n in auto)
              also have "... = real (Suc (Suc (2 * Suc N'))) * (1 / (Suc (Suc (2 * Suc N'))) * (r / 3))"
                by auto
              also have "... = r / 3"
                unfolding mult.assoc[symmetric] by simp
              finally show ?thesis by auto
            qed
            finally show "\<bar>(\<integral>x. f x \<partial>Ni n) - (\<integral>x. f x \<partial>N)\<bar> < r" .
          qed
        qed
      qed
    qed
  qed(auto simp: sets_N finite_measure_N intro!: eventually_mono[OF eventually_Ni])
qed (simp add: mweak_conv_def sets_Ni sets_N finite_measure_N)

lemma mweak_conv_eq: "mweak_conv Ni N F
 \<longleftrightarrow> (\<forall>f::'a \<Rightarrow> real. continuous_map mtopology euclidean f \<longrightarrow> (\<exists>B. \<forall>x\<in>M. \<bar>f x\<bar> \<le> B)
                      \<longrightarrow> ((\<lambda>n. \<integral>x. f x \<partial>Ni n) \<longlongrightarrow> (\<integral>x. f x \<partial>N)) F)"
  by(auto simp: sets_N mweak_conv_def finite_measure_N
        intro!: eventually_mono[OF eventually_conj[OF finite_measure_Ni sets_Ni]])

lemma mweak_conv_eq1: "mweak_conv Ni N F
 \<longleftrightarrow> (\<forall>f::'a \<Rightarrow> real. uniformly_continuous_map Self euclidean_metric f \<longrightarrow> (\<exists>B. \<forall>x\<in>M. \<bar>f x\<bar> \<le> B)
                      \<longrightarrow> ((\<lambda>n. \<integral>x. f x \<partial>Ni n) \<longlongrightarrow> (\<integral>x. f x \<partial>N)) F)"
proof
  assume h:"\<forall>f::'a \<Rightarrow> real. uniformly_continuous_map Self euclidean_metric f \<longrightarrow> (\<exists>B. \<forall>x\<in>M. \<bar>f x\<bar> \<le> B)
                            \<longrightarrow> ((\<lambda>n. \<integral>x. f x \<partial>Ni n) \<longlongrightarrow> (\<integral>x. f x \<partial>N)) F"
  have 1:"((\<lambda>n. measure (Ni n) M) \<longlongrightarrow> measure N M) F"
  proof -
    have 1:"((\<lambda>n. measure (Ni n) (space (Ni n))) \<longlongrightarrow> measure N M) F"
      using h[rule_format,OF uniformly_continuous_map_const[THEN iffD2,of _ 1]]
      by(auto simp: space_N)
    show ?thesis
      by(auto intro!: tendsto_cong[THEN iffD1,OF _ 1] eventually_mono[OF space_Ni])
  qed
  have "\<And>A. closedin mtopology A \<Longrightarrow> Limsup F (\<lambda>n. measure (Ni n) A) \<le> measure N A"
   and "\<And>U. openin mtopology U \<Longrightarrow> measure N U \<le> Liminf F (\<lambda>n. measure (Ni n) U)"
    using mweak_conv2[OF h[rule_format]] mweak_conv3[OF _ 1] by auto
  hence "\<And>A. A \<in> sets (borel_of mtopology) \<Longrightarrow> measure N (mtopology frontier_of A) = 0 
             \<Longrightarrow> ((\<lambda>n. measure (Ni n) A) \<longlongrightarrow> measure N A) F"
    using mweak_conv4 by auto
  with mweak_conv5 show "mweak_conv Ni N F" by auto
qed(use mweak_conv1 in auto)

lemma mweak_conv_eq2: "mweak_conv Ni N F
 \<longleftrightarrow> ((\<lambda>n. measure (Ni n) M) \<longlongrightarrow> measure N M) F \<and> (\<forall>A. closedin mtopology A
       \<longrightarrow> Limsup F (\<lambda>n. measure (Ni n) A) \<le> measure N A)"
proof safe
  assume "mweak_conv Ni N F"
  note h = this[simplified mweak_conv_eq1]
  show 1:"((\<lambda>n. measure (Ni n) M) \<longlongrightarrow> measure N M) F"
  proof -
    have 1:"((\<lambda>n. measure (Ni n) (space (Ni n))) \<longlongrightarrow> measure N M) F"
      using h[rule_format,OF uniformly_continuous_map_const[THEN iffD2,of _ 1]]
      by(auto simp: space_N)
    show ?thesis
      by(auto intro!: tendsto_cong[THEN iffD1,OF _ 1] eventually_mono[OF space_Ni])
  qed
  show "\<And>A. closedin mtopology A \<Longrightarrow> Limsup F (\<lambda>n. measure (Ni n) A) \<le> measure N A"
    using mweak_conv2[OF h[rule_format]] by auto
next
  assume h: "((\<lambda>n. measure (Ni n) M) \<longlongrightarrow> measure N M) F"
    "\<forall>A. closedin mtopology A \<longrightarrow> Limsup F (\<lambda>n. measure (Ni n) A) \<le> measure N A"
  then have "\<And>A. closedin mtopology A \<Longrightarrow> Limsup F (\<lambda>n. measure (Ni n) A) \<le> measure N A"
   and "\<And>U. openin mtopology U \<Longrightarrow> measure N U \<le> Liminf F (\<lambda>n. measure (Ni n) U)"
    using mweak_conv3 by auto
  hence "\<And>A. A \<in> sets (borel_of mtopology) \<Longrightarrow> measure N (mtopology frontier_of A) = 0
          \<Longrightarrow> ((\<lambda>n. measure (Ni n) A) \<longlongrightarrow> measure N A) F"
    using mweak_conv4 by auto
  with mweak_conv5 show "mweak_conv Ni N F" by auto
qed

lemma mweak_conv_eq3: "mweak_conv Ni N F
 \<longleftrightarrow> ((\<lambda>n. measure (Ni n) M) \<longlongrightarrow> measure N M) F \<and>
     (\<forall>U. openin mtopology U \<longrightarrow> measure N U \<le> Liminf F (\<lambda>n. measure (Ni n) U))"
proof safe
  assume "mweak_conv Ni N F"
  note h = this[simplified mweak_conv_eq1]
  show 1:"((\<lambda>n. measure (Ni n) M) \<longlongrightarrow> measure N M) F"
  proof -
    have 1:"((\<lambda>n. measure (Ni n) (space (Ni n))) \<longlongrightarrow> measure N M) F"
      using h[rule_format,OF uniformly_continuous_map_const[THEN iffD2,of _ 1]]
      by(auto simp: space_N)
    show ?thesis
      by(auto intro!: tendsto_cong[THEN iffD1,OF _ 1] eventually_mono[OF space_Ni])
  qed
  show "\<And>U. openin mtopology U \<Longrightarrow> measure N U \<le> Liminf F (\<lambda>n. measure (Ni n) U)"
    using mweak_conv2[OF h[rule_format]] mweak_conv3[OF _ 1] by auto
next
  assume h: "((\<lambda>n. measure (Ni n) M) \<longlongrightarrow> measure N M) F"
    "\<forall>U. openin mtopology U \<longrightarrow> measure N U \<le> Liminf F (\<lambda>n. measure (Ni n) U)"
  then have "\<And>A. closedin mtopology A \<Longrightarrow> Limsup F (\<lambda>n. measure (Ni n) A) \<le> measure N A"
   and "\<And>U. openin mtopology U \<Longrightarrow> measure N U \<le> Liminf F (\<lambda>n. measure (Ni n) U)"
    using mweak_conv3' by auto
  hence "\<And>A. A \<in> sets (borel_of mtopology) \<Longrightarrow> measure N (mtopology frontier_of A) = 0
              \<Longrightarrow> ((\<lambda>n. measure (Ni n) A) \<longlongrightarrow> measure N A) F"
    using mweak_conv4 by auto
  with mweak_conv5 show "mweak_conv Ni N F" by auto
qed

lemma mweak_conv_eq4: "mweak_conv Ni N F
 \<longleftrightarrow> (\<forall>A \<in> sets (borel_of mtopology). measure N (mtopology frontier_of A) = 0
                                      \<longrightarrow> ((\<lambda>n. measure (Ni n) A) \<longlongrightarrow> measure N A) F)"
proof safe
  assume "mweak_conv Ni N F"
  note h = this[simplified mweak_conv_eq1]
  have 1:"((\<lambda>n. measure (Ni n) M) \<longlongrightarrow> measure N M) F"
  proof -
    have 1:"((\<lambda>n. measure (Ni n) (space (Ni n))) \<longlongrightarrow> measure N M) F"
      using h[rule_format,OF uniformly_continuous_map_const[THEN iffD2,of _ 1]]
      by(auto simp: space_N)
    show ?thesis
      by(auto intro!: tendsto_cong[THEN iffD1,OF _ 1] eventually_mono[OF space_Ni])
  qed
  have "\<And>A. closedin mtopology A \<Longrightarrow> Limsup F (\<lambda>n. measure (Ni n) A) \<le> measure N A"
   and "\<And>U. openin mtopology U \<Longrightarrow> measure N U \<le> Liminf F (\<lambda>n. measure (Ni n) U)"
    using mweak_conv2[OF h[rule_format]] mweak_conv3[OF _ 1] by auto
  thus "\<And>A. A \<in> sets (borel_of mtopology) \<Longrightarrow> measure N (mtopology frontier_of A) = 0
             \<Longrightarrow> ((\<lambda>n. measure (Ni n) A) \<longlongrightarrow> measure N A) F"
    using mweak_conv4 by auto
qed(use mweak_conv5 in auto)

corollary mweak_conv_imp_limit_space:
  assumes "mweak_conv Ni N F"
  shows "((\<lambda>i. measure (Ni i) M) \<longlongrightarrow> measure N M) F"
  using assms by(simp add: mweak_conv_eq3)

end

lemma
  assumes "metrizable_space X"
    and "\<forall>\<^sub>F i in F. sets (Ni i) = sets (borel_of X)" "\<forall>\<^sub>F i in F. finite_measure (Ni i)"
    and "sets N = sets (borel_of X)" "finite_measure N"
  shows weak_conv_on_eq1:
    "weak_conv_on Ni N F X
      \<longleftrightarrow> ((\<lambda>n. measure (Ni n) (topspace X)) \<longlongrightarrow> measure N (topspace X)) F
        \<and> (\<forall>A. closedin X A \<longrightarrow> Limsup F (\<lambda>n. measure (Ni n) A) \<le> measure N A)" (is ?eq1)
    and weak_conv_on_eq2:
    "weak_conv_on Ni N F X
      \<longleftrightarrow> ((\<lambda>n. measure (Ni n) (topspace X)) \<longlongrightarrow> measure N (topspace X)) F
           \<and> (\<forall>U. openin X U \<longrightarrow> measure N U \<le> Liminf F (\<lambda>n. measure (Ni n) U))" (is ?eq2)
    and weak_conv_on_eq3:
    "weak_conv_on Ni N F X
      \<longleftrightarrow> (\<forall>A \<in> sets (borel_of X). measure N (X frontier_of A) = 0
           \<longrightarrow> ((\<lambda>n. measure (Ni n) A) \<longlongrightarrow> measure N A) F)" (is ?eq3)
proof -
  obtain d where d: "Metric_space (topspace X) d" "Metric_space.mtopology (topspace X) d = X"
    by (metis Metric_space.topspace_mtopology assms(1) metrizable_space_def)
  then interpret mweak_conv_fin "topspace X" d Ni N
    by(auto simp: mweak_conv_fin_def mweak_conv_fin_axioms_def assms)  
  show ?eq1 ?eq2 ?eq3
    using mweak_conv_eq2 mweak_conv_eq3 mweak_conv_eq4 unfolding d(2) by blast+
qed

end