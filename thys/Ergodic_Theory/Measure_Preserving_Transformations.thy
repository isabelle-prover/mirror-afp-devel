(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr 
    License: BSD
*)

theory Measure_Preserving_Transformations
imports SG_Library_Complement
begin

section{*Measure preserving or quasi-preserving maps*}

text{*Ergodic theory in general is the study of the properties of measure preserving or
quasi-preserving dynamical systems. In this section, we introduce the basic definitions
in this respect.*}

subsection {*The different classes of transformations*}

definition
  "quasi_measure_preserving M N \<equiv> {f\<in> measurable M N. (\<forall> A \<in> sets N. emeasure N A = 0 \<longleftrightarrow> emeasure M (f-`A \<inter> space M) = 0)}"

lemma id_quasi_measure_preserving:
  "(\<lambda>x. x) \<in> quasi_measure_preserving M M"
unfolding quasi_measure_preserving_def by auto

lemma quasi_measure_preserving_composition:
  assumes "f \<in> quasi_measure_preserving M N"
          "g \<in> quasi_measure_preserving N P"
  shows "(\<lambda>x. g(f x)) \<in> quasi_measure_preserving M P"
unfolding quasi_measure_preserving_def
proof
  have f_meas: "f \<in> measurable M N" using assms(1) quasi_measure_preserving_def by blast
  have g_meas: "g \<in> measurable N P" using assms(2) quasi_measure_preserving_def by blast
  then have a: "(\<lambda>x. g (f x)) \<in> measurable M P" using f_meas g_meas measurable_compose by blast

  {
    fix C
    assume C_meas: "C \<in> sets P"
    def B \<equiv> "g-`C \<inter> space N"
    have B_meas: "B \<in> sets N" using g_meas measurable_def C_meas B_def by simp
    have *: "emeasure N B = 0 \<longleftrightarrow> emeasure P C = 0" using C_meas B_def assms(2) quasi_measure_preserving_def by blast

    def A \<equiv> "f-`B \<inter> space M"
    have "A \<in> sets M" using f_meas measurable_def B_meas A_def by simp
    have "emeasure M A = 0 \<longleftrightarrow> emeasure N B = 0" using B_meas A_def assms(1) * quasi_measure_preserving_def by blast

    then have "emeasure P C = 0 \<longleftrightarrow> emeasure M A = 0" using * by simp
    moreover have "A = (\<lambda>x. g(f x))-`C \<inter> space M"
      by (auto simp add: A_def B_def) (meson f_meas measurable_space)
    ultimately have "emeasure P C = 0 \<longleftrightarrow> emeasure M ((\<lambda>x. g(f x))-`C \<inter> space M) = 0" by simp
  }
  then show " (\<lambda>x. g (f x)) \<in> measurable M P
      \<and> (\<forall>A\<in>sets P. (emeasure P A = 0) = (emeasure M ((\<lambda>x. g (f x)) -` A \<inter> space M) = 0))"
    using a by auto
qed

lemma quasi_measure_preserving_comp:
  assumes "f \<in> quasi_measure_preserving M N"
          "g \<in> quasi_measure_preserving N P"
  shows "g o f \<in> quasi_measure_preserving M P"
unfolding o_def using assms quasi_measure_preserving_composition by blast

definition
  "measure_preserving M N \<equiv> {f \<in> measurable M N. (\<forall> A \<in> sets N. emeasure M (f-`A \<inter> space M) = emeasure N A)}"

lemma measure_preserving_eq_distr:
  assumes "f \<in> measure_preserving M N"
  shows "distr M N f = N"
proof -
  let ?N2 = "distr M N f"
  have "sets ?N2 = sets N" by simp
  moreover have "\<And>A. A \<in> sets N \<Longrightarrow> emeasure ?N2 A = emeasure N A"
  proof -
    fix A
    assume "A \<in> sets N"
    have "emeasure ?N2 A = emeasure M (f-`A \<inter> space M)"
      using `A \<in> sets N` assms emeasure_distr measure_preserving_def by blast
    thus "emeasure ?N2 A = emeasure N A"
      using `A \<in> sets N` assms measure_preserving_def by auto
  qed
  ultimately show ?thesis by (metis measure_eqI)
qed

lemma measure_preserving_preserves_nn_integral:
  assumes "T \<in> measure_preserving M N"
          "f \<in> borel_measurable N"
          "\<And>x. f x \<ge> 0"
  shows "(\<integral>\<^sup>+x. f x \<partial>N) = (\<integral>\<^sup>+x. f (T x) \<partial>M)"
proof -
  have a: "T \<in> measurable M N" using assms(1) measure_preserving_def by blast
  have "(\<integral>\<^sup>+x. f (T x) \<partial>M) = (\<integral>\<^sup>+y. f y \<partial>distr M N T)"
    using nn_integral_distr[of "T", of "M", of "N", of "f", OF a, OF assms(2)] by simp
  also have "... = (\<integral>\<^sup>+y. f y \<partial>N)" using measure_preserving_eq_distr[OF assms(1)] by simp
  finally show ?thesis by simp
qed

lemma measure_preserving_preserves_integral:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "T \<in> measure_preserving M N" and
       [measurable]: "integrable N f"
  shows "integrable M (\<lambda>x. f(T x))" "(\<integral>x. f x \<partial>N) = (\<integral>x. f (T x) \<partial>M)"
proof -
  have a [measurable]: "T \<in> measurable M N" using assms(1) measure_preserving_def by blast
  have b [measurable]: "f \<in> borel_measurable N" by simp
  have "distr M N T = N" using measure_preserving_eq_distr[OF assms(1)] by simp
  then have "integrable (distr M N T) f" using assms(2) by simp
  then show "integrable M (\<lambda>x. f(T x))" using integrable_distr_eq[OF a b] by simp

  have "(\<integral>x. f (T x) \<partial>M) = (\<integral>y. f y \<partial>distr M N T)" using integral_distr[OF a b] by simp
  then show "(\<integral>x. f x \<partial>N) = (\<integral>x. f (T x) \<partial>M)" using `distr M N T = N` by simp
qed

lemma id_measure_preserving:
  "(\<lambda>x. x) \<in> measure_preserving M M"
unfolding measure_preserving_def by auto

lemma measure_preserving_is_quasi_measure_preserving:
  "measure_preserving M N \<subseteq> quasi_measure_preserving M N"
unfolding measure_preserving_def quasi_measure_preserving_def by auto

lemma measure_preserving_composition:
  assumes "f \<in> measure_preserving M N"
          "g \<in> measure_preserving N P"
  shows "(\<lambda>x. g(f x)) \<in> measure_preserving M P"
proof (auto simp add: measure_preserving_def)
  have f: "f \<in> measurable M N" using assms(1) measure_preserving_def by blast
  have g: "g \<in> measurable N P" using assms(2) measure_preserving_def by blast
  show "(\<lambda>x. g (f x)) \<in> measurable M P" using f g measurable_compose by blast

  {
    fix C
    assume Cs: "C \<in> sets P"
    def B \<equiv> "g-`C \<inter> space N"
    have Bs: "B \<in> sets N" using g measurable_def Cs B_def by simp
    have *: "emeasure N B = emeasure P C" using Cs B_def assms(2) measure_preserving_def by blast

    def A \<equiv> "f-`B \<inter> space M"
    have "A \<in> sets M" using f measurable_def Bs A_def by simp
    have "emeasure M A = emeasure N B" using Bs A_def assms(1) measure_preserving_def by blast

    hence "emeasure M A = emeasure P C" using * by simp
    moreover have "A = (\<lambda>x. g(f x))-`C \<inter> space M"
      by (auto simp add: A_def B_def) (meson f measurable_space)
    ultimately have "emeasure M ((\<lambda>x. g(f x))-`C \<inter> space M) = emeasure P C" by simp
  }
  thus "\<And>A. A \<in> sets P \<Longrightarrow> emeasure M ((\<lambda>x. g (f x)) -` A \<inter> space M) = emeasure P A" by simp
qed

lemma measure_preserving_comp:
  assumes "f \<in> measure_preserving M N"
          "g \<in> measure_preserving N P"
  shows "g o f \<in> measure_preserving M P"
unfolding o_def using measure_preserving_composition assms by blast

lemma prob_space_invariant:
  assumes "f \<in> measure_preserving M N"
          "prob_space N"
  shows "prob_space M"
proof -
  have "f \<in> measurable M N" using assms measure_preserving_def by blast
  hence "f-`(space N) \<inter> space M = space M" by (meson Int_absorb1 measurable_space subsetI vimageI)
  hence "emeasure M (space M) = emeasure N (space N)" by (metis (mono_tags, lifting) assms(1) measure_preserving_def mem_Collect_eq sets.top)
  hence "emeasure M (space M) = 1" using assms(2) by (simp add: prob_space.emeasure_space_1)
  thus "prob_space M" by (simp add: prob_spaceI)
qed

locale qmpt = sigma_finite_measure +
  fixes T
  assumes Tqm: "T \<in> quasi_measure_preserving M M"

locale mpt = qmpt +
  assumes Tm: "T\<in> measure_preserving M M"

locale fmpt = mpt + finite_measure

locale pmpt = fmpt + prob_space

lemma qmpt_I:
  assumes "sigma_finite_measure M"
          "T \<in> measurable M M"
          "\<And>A. A \<in> sets M \<Longrightarrow> ((T-`A \<inter> space M) \<in> null_sets M) \<longleftrightarrow>  (A \<in> null_sets M)"
  shows "qmpt M T"
unfolding qmpt_def qmpt_axioms_def quasi_measure_preserving_def
by (auto simp add: assms) (meson assms(2) assms(3) measurable_sets null_setsD1 null_setsI)+

lemma mpt_I:
  assumes "sigma_finite_measure M"
          "T \<in> measurable M M"
          "\<And>A. A \<in> sets M \<Longrightarrow> emeasure M (T-`A \<inter> space M) = emeasure M A"
  shows "mpt M T"
unfolding mpt_def qmpt_def mpt_axioms_def qmpt_axioms_def quasi_measure_preserving_def measure_preserving_def
by (auto simp add: assms)

lemma fmpt_I:
  assumes "finite_measure M"
          "T \<in> measurable M M"
          "\<And>A. A \<in> sets M \<Longrightarrow> emeasure M (T-`A \<inter> space M) = emeasure M A"
  shows "fmpt M T"
unfolding fmpt_def mpt_def qmpt_def mpt_axioms_def qmpt_axioms_def quasi_measure_preserving_def measure_preserving_def
apply (auto simp add: assms) using assms(1) finite_measure_def by auto

lemma pmpt_I:
  assumes "prob_space M"
          "T \<in> measurable M M"
          "\<And>A. A \<in> sets M \<Longrightarrow> emeasure M (T-`A \<inter> space M) = emeasure M A"
  shows "pmpt M T"
unfolding pmpt_def fmpt_def mpt_def qmpt_def mpt_axioms_def qmpt_axioms_def quasi_measure_preserving_def measure_preserving_def
by (auto simp add: assms prob_space_imp_sigma_finite prob_space.finite_measure)



subsection {*Examples*}

lemma fmpt_null_space:
  assumes "emeasure M (space M) = 0"
          "T \<in> measurable M M"
  shows "fmpt M T"
by (rule fmpt_I, auto simp add: assms finite_measureI, metis assms(1) emeasure_le_0_iff emeasure_space)

lemma fmpt_empty_space:
  assumes "space M = {}"
  shows "fmpt M T"
by (rule fmpt_null_space, auto simp add: assms measurable_empty_iff)

text{*Translations are measure-preserving*}

lemma mpt_translation:
  fixes c :: "'a::euclidean_space"
  shows "mpt lborel (\<lambda>x. x + c)"
proof (rule mpt_I, auto simp add: lborel.sigma_finite_measure_axioms)
  fix A::"'a set" assume [measurable]: "A \<in> sets borel"
  have "emeasure lborel ((\<lambda>x. x + c) -` A) = emeasure lborel ((op+c)-`A)" by (meson add.commute)
  also have "... =  emeasure lborel ((op+c)-`A \<inter> space lborel)" by simp
  also have "... = emeasure (distr lborel borel (op + c)) A" by (rule emeasure_distr[symmetric], auto)
  also have "... = emeasure lborel A" using lborel_distr_plus2[of c] by simp
  finally show "emeasure lborel ((\<lambda>x. x + c) -` A) = emeasure lborel A" by simp
qed

text{*Skew products are fibered maps of the form $(x,y)\mapsto (Tx, U(x,y))$. If the base map
and the fiber maps all are measure preserving, so is the skew product.*}

lemma mpt_skew_product:
  assumes "mpt M T"
          "\<forall>x \<in> space M. mpt N (U x)" and
      [measurable]: "(\<lambda>(x,y). U x y) \<in> measurable (M \<Otimes>\<^sub>M N) N"
  shows "mpt (M \<Otimes>\<^sub>M N) (\<lambda>(x,y). (T x, U x y))"
proof (cases)
  assume "space M = {}"
  then have "space (M \<Otimes>\<^sub>M N) = {}" by (simp add: space_pair_measure)
  with fmpt_empty_space[OF this] show ?thesis by (simp add: fmpt.axioms(1))
next
  assume "\<not>(space M = {})"
  show ?thesis
  proof (rule mpt_I)
    have "sigma_finite_measure M" using assms(1) unfolding mpt_def qmpt_def by auto
    moreover have "sigma_finite_measure N" using assms(2) `\<not>(space M = {})` unfolding mpt_def qmpt_def by auto
    ultimately show "sigma_finite_measure (M \<Otimes>\<^sub>M N)" by (simp add: sigma_finite_pair_measure)

    have [measurable]: "T \<in> measurable M M" using assms(1) unfolding mpt_def qmpt_def qmpt_axioms_def quasi_measure_preserving_def by auto
    show [measurable]: "(\<lambda>(x, y). (T x, U x y)) \<in> measurable (M \<Otimes>\<^sub>M N) (M \<Otimes>\<^sub>M N)" by auto
    have "T \<in> measure_preserving M M" using assms(1) by (simp add: mpt.Tm)

    fix A assume [measurable]: "A \<in> sets (M \<Otimes>\<^sub>M N)"
    then have [measurable]: "(\<lambda> (x,y). (indicator A (x,y))::ereal ) \<in> borel_measurable (M \<Otimes>\<^sub>M N)" by auto
    then have [measurable]: "(\<lambda>x. \<integral>\<^sup>+ y. indicator A (x, y) \<partial>N) \<in> borel_measurable M"
      using \<open>sigma_finite_measure N\<close>  sigma_finite_measure.borel_measurable_nn_integral by blast

    def B \<equiv> "(\<lambda>(x, y). (T x, U x y)) -` A \<inter> space (M \<Otimes>\<^sub>M N)"
    then have [measurable]: "B \<in> sets (M \<Otimes>\<^sub>M N)" by auto

    {
      fix x assume "x \<in> space M"
      then have "T x \<in> space M" by (meson \<open>T \<in> measurable M M\<close> \<open>x \<in> space M\<close> measurable_space)
      then have 1: "(\<lambda>y. (indicator A (T x, y))::ereal) \<in> borel_measurable N" using `A \<in> sets (M \<Otimes>\<^sub>M N)` by auto
      have 2: "\<And>y. ((indicator B (x, y))::ereal) = indicator A (T x, U x y) * indicator (space M) x * indicator (space N) y"
        unfolding B_def by (simp add: indicator_def space_pair_measure)
      have 3: "U x \<in> measure_preserving N N" using assms(2) `x \<in> space M` by (simp add: mpt.Tm)

      have "(\<integral>\<^sup>+y. indicator B (x,y) \<partial>N) =  (\<integral>\<^sup>+y. indicator A (T x, U x y) \<partial>N)"
         apply (rule nn_integral_cong_strong) using 2 by (auto simp add: indicator_def `x \<in> space M`)
      also have "... = (\<integral>\<^sup>+y. indicator A (T x, y) \<partial>N)"
        by (rule measure_preserving_preserves_nn_integral[OF 3, symmetric], metis 1, simp add: indicator_def)
      finally have "(\<integral>\<^sup>+y. indicator B (x,y) \<partial>N) = (\<integral>\<^sup>+y. indicator A (T x, y) \<partial>N)" by simp
    } note * = this

    have "emeasure (M \<Otimes>\<^sub>M N) B = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+y. indicator B (x,y) \<partial>N) \<partial>M)"
      using \<open>B \<in> sets (M \<Otimes>\<^sub>M N)\<close> \<open>sigma_finite_measure N\<close> sigma_finite_measure.emeasure_pair_measure by fastforce
    also have "... =  (\<integral>\<^sup>+ x. (\<integral>\<^sup>+y. indicator A (T x, y) \<partial>N) \<partial>M)"
      by (rule nn_integral_cong_strong, auto simp add: *)
    also have "... =  (\<integral>\<^sup>+ x. (\<integral>\<^sup>+y. indicator A (x, y) \<partial>N) \<partial>M)"
      by (rule measure_preserving_preserves_nn_integral[OF `T \<in> measure_preserving M M`, symmetric], auto simp add: nn_integral_nonneg)
    also have "... = emeasure (M \<Otimes>\<^sub>M N) A"
      by (simp add: \<open>sigma_finite_measure N\<close> sigma_finite_measure.emeasure_pair_measure)
    finally show "emeasure (M \<Otimes>\<^sub>M N) ((\<lambda>(x, y). (T x, U x y)) -` A \<inter> space (M \<Otimes>\<^sub>M N)) = emeasure (M \<Otimes>\<^sub>M N) A"
      unfolding B_def by simp
  qed
qed

lemma mpt_skew_product_real:
  fixes f::"'a \<Rightarrow> real"
  assumes "mpt M T" and [measurable]: "f \<in> borel_measurable M"
  shows "mpt (M \<Otimes>\<^sub>M lborel) (\<lambda>(x,y). (T x, y + f x))"
by (rule mpt_skew_product, auto simp add: mpt_translation assms(1))


subsection {*Preimages restricted to $space M$*}

context qmpt begin

text{*One is all the time lead to take the preimages of sets, and restrict them to
\verb+space M+ where the dynamics is living. We introduce a shortcut for this notion.
Note however that I did probably not introduce enough lemmas about it, so in
many proofs it is necessary to unfold the definition... It would be nice to add enough lemmas
so that one would never need to come back to the usual preimage.*}

definition vimage_restr :: "('a => 'a) => 'a set => 'a set" (infixr "--`" 90)
where
  "f --` A \<equiv> f-` (A \<inter> space M)  \<inter> space M"

lemma vrestr_intersec [simp]:
  "f--` (A \<inter> B) = (f--`A) \<inter> (f--` B)"
using vimage_restr_def by auto

lemma vrestr_union [simp]:
  "f--` (A \<union> B) = f--`A \<union> f--`B"
using vimage_restr_def by auto

lemma vrestr_difference [simp]:
  "f--`(A-B) = f--`A - f--`B"
using vimage_restr_def by auto

lemma vrestr_inclusion:
  "A \<subseteq> B \<Longrightarrow> f--`A \<subseteq> f--`B"
using vimage_restr_def by auto

lemma vrestr_Union [simp]:
  "f --` (\<Union>A) = (\<Union>X\<in>A. f --` X)"
using vimage_restr_def by auto

lemma vrestr_UN [simp]:
  "f --` (\<Union>x\<in>A. B x) = (\<Union>x\<in>A. f --` B x)"
using vimage_restr_def by auto

lemma vrestr_Inter [simp]:
  assumes "A \<noteq> {}"
  shows "f --` (\<Inter>A) = (\<Inter>X\<in>A. f --` X)"
using vimage_restr_def assms by auto

lemma vrestr_INT [simp]:
  assumes "A \<noteq> {}"
  shows "f --` (\<Inter>x\<in>A. B x) = (\<Inter>x\<in>A. f --` B x)"
using vimage_restr_def assms by auto

lemma vrestr_empty [simp]:
  "f--`{} = {}"
using vimage_restr_def by auto

lemma vrestr_sym_diff [simp]:
  "f--`(A \<Delta> B) = (f--`A) \<Delta> (f--`B)"
by auto

lemma vrestr_image:
  assumes "x \<in> f--`A"
  shows "x \<in> space M" "f x \<in> space M" "f x \<in> A"
using assms unfolding vimage_restr_def by auto

lemma vrestr_intersec_in_space:
  assumes "A \<in> sets M" "B \<in> sets M"
  shows "A \<inter> f--`B = A \<inter> f-`B"
unfolding vimage_restr_def using assms sets.sets_into_space by auto

lemma vrestr_compose:
  assumes "g \<in> measurable M M"
  shows "(\<lambda> x. f(g x))--` A = g--` (f--` A)"
proof -
  def B \<equiv> "A \<inter> space M"
  have "(\<lambda> x. f(g x))--` A = (\<lambda> x. f(g x)) -` B \<inter> space M"
    using B_def vimage_restr_def by blast
  moreover have " (\<lambda> x. f(g x)) -` B \<inter> space M = g-` (f-` B \<inter> space M) \<inter> space M"
    using measurable_space[OF `g \<in> measurable M M`] by auto
  moreover have "g-` (f-` B \<inter> space M) \<inter> space M = g--` (f--` A)"
    using B_def vimage_restr_def by simp
  ultimately show ?thesis by auto
qed

lemma vrestr_comp:
  assumes "g \<in> measurable M M"
  shows "(f o g)--` A = g--` (f--` A)"
proof -
  have "f o g = (\<lambda> x. f(g x))" by auto
  hence "(f o g)--` A = (\<lambda> x. f(g x))--` A" by auto
  moreover have "(\<lambda> x. f(g x))--` A = g--` (f--` A)" using vrestr_compose assms by auto
  ultimately show ?thesis by simp
qed

lemma vrestr_of_set:
  assumes "g \<in> measurable M M"
  shows "A \<in> sets M \<Longrightarrow> g--`A = g-`A \<inter> space M"
by (simp add: vimage_restr_def)

lemma vrestr_meas [measurable (raw)]:
  assumes "g \<in> measurable M M"
          "A \<in> sets M"
  shows "g--`A \<in> sets M"
using assms vimage_restr_def by auto

lemma vrestr_same_emeasure_f:
  assumes "f \<in> measure_preserving M M"
          "A \<in> sets M"
  shows "emeasure M (f--`A) = emeasure M A"
by (metis (mono_tags, lifting) assms measure_preserving_def mem_Collect_eq sets.Int_space_eq2 vimage_restr_def)

lemma vrestr_same_measure_f:
  assumes "f \<in> measure_preserving M M"
          "A \<in> sets M"
  shows "measure M (f--`A) = measure M A"
proof -
  have "measure M (f--`A) = real_of_ereal (emeasure M  (f--`A))" by (simp add: Sigma_Algebra.measure_def)
  also have "... = real_of_ereal (emeasure M A)" using vrestr_same_emeasure_f[OF assms] by simp
  also have "... = measure M A"  by (simp add: Sigma_Algebra.measure_def)
  finally show "measure M (f--` A) = measure M A" by simp
qed



subsection {*Basic properties of qmpt*}

lemma T_meas [measurable (raw)]:
  "T \<in> measurable M M"
using Tqm quasi_measure_preserving_def by blast

lemma Tn_quasi_measure_preserving:
  "T^^n \<in> quasi_measure_preserving M M"
proof (induction n)
    case 0
    show ?case using id_quasi_measure_preserving by simp
  next
    case (Suc n)
    thus ?case using Tqm quasi_measure_preserving_comp by (metis funpow_Suc_right)
qed

lemma Tn_meas [measurable (raw)]:
 "T^^n \<in> measurable M M"
using Tn_quasi_measure_preserving quasi_measure_preserving_def by auto

lemma T_vrestr_meas [measurable]:
  assumes "A \<in> sets M"
  shows "T--` A \<in> sets M"
        "(T^^n)--` A \<in> sets M"
by (auto simp add: vrestr_meas assms)

lemma T_vrestr_intersec_meas:
  assumes "A \<in> sets M" "B \<in> sets M"
  shows "A \<inter> T-`B \<in> sets M"
        "A \<inter> (T^^n)-`B \<in> sets M"
apply (metis vrestr_intersec_in_space T_vrestr_meas(1) assms sets.Int)
apply (metis vrestr_intersec_in_space T_vrestr_meas(2) assms sets.Int)
done

lemma T_vrestr_0 [simp]:
  assumes "A \<in> sets M"
  shows "(T^^0)--`A = A"
using vimage_restr_def sets.sets_into_space[OF assms] by auto

lemma T_vrestr_composed:
  assumes "A \<in> sets M"
  shows "(T^^n)--` (T^^m)--` A = (T^^(n+m))--` A"
        "T--` (T^^m)--` A = (T^^(m+1))--` A"
        "(T^^m)--` T--` A = (T^^(m+1))--` A"
proof -
  show "(T^^n)--` (T^^m)--` A = (T^^(n+m))--` A"
    by (simp add: Tn_meas funpow_add add.commute vrestr_comp)
  show "T--` (T^^m)--` A = (T^^(m+1))--` A"
    by (metis Suc_eq_plus1 T_meas funpow_Suc_right vrestr_comp)
  show "(T^^m)--` T--` A = (T^^(m+1))--` A"
    by (simp add: Tn_meas vrestr_comp)
qed

lemma T_spaceM_stable:
  assumes "x \<in> space M"
   shows "T x \<in> space M"
         "(T^^n) x \<in> space M"
proof -
  show "T x \<in> space M" by (meson measurable_space T_meas measurable_def assms)
  show "(T^^n) x \<in> space M" by (meson measurable_space Tn_meas measurable_def assms)
qed

lemma T_quasi_preserves:
  assumes "A \<in> sets M"
   shows "emeasure M A = 0 \<longleftrightarrow> emeasure M (T--` A) = 0"
         "emeasure M A = 0 \<longleftrightarrow> emeasure M ((T^^n)--` A) = 0"
proof -
  have "(T--`A) = T-`A \<inter> space M" by (rule vrestr_of_set[OF T_meas, OF assms])
  then show "emeasure M A = 0 \<longleftrightarrow> emeasure M (T--` A) = 0" using Tqm quasi_measure_preserving_def assms by fastforce
  have "((T^^n)--`A) = (T^^n)-`A \<inter> space M" by (rule vrestr_of_set[OF Tn_meas, OF assms])
  then show "emeasure M A = 0 \<longleftrightarrow> emeasure M ((T^^n)--` A) = 0"
    using Tn_quasi_measure_preserving quasi_measure_preserving_def assms by fastforce
qed

lemma T_quasi_preserves_null:
  assumes "A \<in> sets M"
   shows "A \<in> null_sets M \<longleftrightarrow> T--` A \<in> null_sets M"
         "A \<in> null_sets M \<longleftrightarrow> (T^^n)--` A \<in> null_sets M"
apply (metis T_vrestr_meas(1)[OF assms] null_setsD1 null_setsI assms T_quasi_preserves(1)[OF assms])
apply (metis T_vrestr_meas(2)[OF assms] null_setsD1 null_setsI assms T_quasi_preserves(2)[OF assms])
done

lemma T_quasi_preserves_null2:
  assumes "A \<in> null_sets M"
   shows "T--` A \<in> null_sets M"
         "(T^^n)--` A \<in> null_sets M"
using T_quasi_preserves_null[OF null_setsD2[OF assms]] assms by auto

lemma T_composition_borel [measurable]:
  assumes "f \<in> borel_measurable M"
   shows "(\<lambda>x. f(T x)) \<in> borel_measurable M" "(\<lambda>x. f((T^^k) x)) \<in> borel_measurable M"
using T_meas Tn_meas assms measurable_compose by auto

lemma T_AE_iterates:
  assumes "AE x in M. P x"
  shows "AE x in M. \<forall>n. P ((T^^n) x)"
proof -
  obtain N where N: "\<And>x. x \<in> space M - N \<Longrightarrow> P x"  "N \<in> null_sets M" using AE_E3[OF assms]  by blast
  def A \<equiv> "\<Union>n. (T^^n)--`N"
  have "(T^^n)--`N \<in> null_sets M" for n using T_quasi_preserves_null2(2)[OF N(2)].
  then have "A \<in> null_sets M" unfolding A_def by auto
  moreover have "\<And>x. x \<in> space M - A \<Longrightarrow> \<forall>n. P ((T^^n) x)"
  proof 
    fix x n
    assume "x \<in> space M - A"
    then have "x \<in> (space M - (T^^n)--`N)" unfolding A_def by auto
    then have "(T^^n) x \<in> space M - N" by (auto simp add: N(2) T_spaceM_stable(2) null_setsD2 vrestr_of_set)
    then show "P((T^^n) x)" using N(1) by auto
  qed
  ultimately show ?thesis unfolding eventually_ae_filter by blast
qed

lemma qmpt_power:
  "qmpt M (T^^n)"
proof
  show "T^^n \<in> quasi_measure_preserving M M " by (simp add: Tn_quasi_measure_preserving)
qed

end

subsection {*Basic properties of mpt*}

context mpt
begin

lemma Tn_measure_preserving:
  "T^^n \<in> measure_preserving M M"
proof (induction n)
    case (Suc n)
    thus ?case using Tm measure_preserving_comp by (metis funpow_Suc_right)
qed (simp add: id_measure_preserving)

lemma T_integral_preserving:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "integrable M f"
  shows "integrable M (\<lambda>x. f(T x))" "(\<integral>x. f(T x) \<partial>M) = (\<integral>x. f x \<partial>M)"
using measure_preserving_preserves_integral[OF Tm assms] by auto

lemma Tn_integral_preserving:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "integrable M f"
  shows "integrable M (\<lambda>x. f((T^^n) x))" "(\<integral>x. f((T^^n) x) \<partial>M) = (\<integral>x. f x \<partial>M)"
using measure_preserving_preserves_integral[OF  Tn_measure_preserving assms] by auto

lemma T_nn_integral_preserving:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes "\<And>x. f x \<ge> 0" "f \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+x. f(T x) \<partial>M) = (\<integral>\<^sup>+x. f x \<partial>M)"
using measure_preserving_preserves_nn_integral[OF Tm assms(2) assms(1)] by auto

lemma Tn_nn_integral_preserving:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes "\<And>x. f x \<ge> 0" "f \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+x. f((T^^n) x) \<partial>M) = (\<integral>\<^sup>+x. f x \<partial>M)"
using measure_preserving_preserves_nn_integral[OF Tn_measure_preserving assms(2) assms(1)] by auto

lemma mpt_power:
  "mpt M (T^^n)"
proof
  show "T^^n \<in> quasi_measure_preserving M M " by (simp add: Tn_quasi_measure_preserving)
  show "T^^n \<in> measure_preserving M M" by (simp add: Tn_measure_preserving)
qed

lemma T_vrestr_same_emeasure:
  assumes "A \<in> sets M"
  shows "emeasure M (T--` A) = emeasure M A"
        "emeasure M ((T ^^ n)--`A) = emeasure M A"
by (auto simp add: vrestr_same_emeasure_f Tm Tn_measure_preserving assms)

lemma  T_vrestr_same_measure:
  assumes "A \<in> sets M"
  shows "measure M (T--` A) = measure M A"
        "measure M ((T ^^ n)--`A) = measure M A"
by (auto simp add: vrestr_same_measure_f Tm Tn_measure_preserving assms)

lemma (in fmpt) fmpt_power:
  "fmpt M (T^^n)"
proof
  show "T^^n \<in> quasi_measure_preserving M M " by (simp add: Tn_quasi_measure_preserving)
  show "T^^n \<in> measure_preserving M M" by (simp add: Tn_measure_preserving)
qed

end


subsection {*Birkhoff sums*}

text{*Birkhoff sums, obtained by summing a function along the orbit of a map, are basic objects
to be understood in ergodic theory.*}

context qmpt
begin

definition birkhoff_sum::"('a \<Rightarrow> 'b::comm_monoid_add) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'b"
  where "birkhoff_sum f n x = (\<Sum>i\<in>{..<n}. f((T^^i)x))"

text{*I did not find a way to prove a lemma applying simultaneously in \verb+real+ and \verb+ereal+
and \verb+nat+, so I give three separate statements about measurability.*}

lemma birkhoff_sum_meas [measurable]:
  fixes f::"'a \<Rightarrow> real"
  assumes [measurable]: "f \<in> borel_measurable M"
  shows "birkhoff_sum f n \<in> borel_measurable M"
proof -
  def F \<equiv> "\<lambda>i x.  f((T^^i)x)"
  have "\<And>i. F i \<in> borel_measurable M" using assms F_def by auto
  then have "(\<lambda>x. (\<Sum>i<n. F i x)) \<in> borel_measurable M" by measurable
  then have "(\<lambda>x. birkhoff_sum f n x) \<in> borel_measurable M" unfolding birkhoff_sum_def F_def by auto
  then show ?thesis by simp
qed

lemma birkhoff_sum_meas_ereal [measurable]:
  fixes f::"'a \<Rightarrow> ereal"
  assumes "f \<in> borel_measurable M"
  shows "birkhoff_sum f n \<in> borel_measurable M"
proof -
  def F \<equiv> "\<lambda>i x.  f((T^^i)x)"
  have "\<And>i. F i \<in> borel_measurable M" using assms F_def by auto
  then have "(\<lambda>x. (\<Sum>i<n. F i x)) \<in> borel_measurable M" by measurable
  then have "(\<lambda>x. birkhoff_sum f n x) \<in> borel_measurable M" unfolding birkhoff_sum_def F_def by auto
  then show ?thesis by simp
qed

lemma birkhoff_sum_meas_nat [measurable]:
  fixes f::"'a \<Rightarrow> nat"
  assumes [measurable]: "f \<in> measurable M (count_space UNIV)"
  shows "birkhoff_sum f n \<in> measurable M (count_space UNIV)"
proof -
  def g \<equiv> "\<lambda>x. real(f x)"
  have [measurable]: "g \<in> borel_measurable M" unfolding g_def using assms by auto
  have [measurable]: "birkhoff_sum g n \<in> borel_measurable M" by auto
  have "\<And>x. real(birkhoff_sum f n x) = birkhoff_sum g n x"
    unfolding g_def birkhoff_sum_def by auto
  then have "(\<lambda>x. real(birkhoff_sum f n x)) \<in> borel_measurable M" by simp
  then show ?thesis by (rule measurable_real_imp_nat[of "birkhoff_sum f n", of M])
qed

lemma birkhoff_sum_1 [simp]:
  "birkhoff_sum f 0 x = 0"
  "birkhoff_sum f 1 x = f x"
  "birkhoff_sum f (Suc 0) x = f x"
unfolding birkhoff_sum_def by auto

lemma birkhoff_sum_cocycle:
  "birkhoff_sum f (n+m) x = birkhoff_sum f n x + birkhoff_sum f m ((T^^n)x)"
proof -
  have "(\<Sum>i<m. f ((T ^^ i) ((T ^^ n) x))) =  (\<Sum>i<m. f ((T ^^ (i+n)) x))" by (simp add: funpow_add)
  also have "... =  (\<Sum>j\<in>{n..< m+n}. f ((T ^^j) x))"
    using atLeast0LessThan setsum_shift_bounds_nat_ivl[where ?f="\<lambda>j. f((T^^j)x)" and ?k=n and ?m=0 and ?n=m, symmetric]
          add.commute add.left_neutral  by auto
  finally have *: "birkhoff_sum f m ((T^^n)x) = (\<Sum>j\<in>{n..< m+n}. f ((T ^^j) x))" unfolding birkhoff_sum_def by auto
  have "birkhoff_sum f (n+m) x = (\<Sum>i<n. f((T^^i)x)) + (\<Sum>i\<in>{n..<m+n}. f((T^^i)x))"
    unfolding birkhoff_sum_def by (metis add.commute add.right_neutral atLeast0LessThan le_add2 setsum_add_nat_ivl)
  also have "... = birkhoff_sum f n x + (\<Sum>i\<in>{n..<m+n}. f((T^^i)x))" unfolding birkhoff_sum_def by simp
  finally show ?thesis using * by simp
qed

lemma birkhoff_sum_mono:
  fixes f g::"_ \<Rightarrow> real"
  assumes "\<And>x. f x \<le> g x"
  shows "birkhoff_sum f n x \<le> birkhoff_sum g n x"
unfolding birkhoff_sum_def by (simp add: assms setsum_mono)

lemma birkhoff_sum_abs:
  fixes f::"_ \<Rightarrow> 'b::real_normed_vector"
  shows "norm(birkhoff_sum f n x) \<le> birkhoff_sum (\<lambda>x. norm(f x)) n x"
unfolding birkhoff_sum_def using norm_setsum by auto

lemma birkhoff_sum_add:
  "birkhoff_sum (\<lambda>x. f x + g x) n x = birkhoff_sum f n x + birkhoff_sum g n x"
unfolding birkhoff_sum_def by (simp add: setsum.distrib)

lemma birkhoff_sum_diff:
  fixes f g::"_ \<Rightarrow> real"
  shows "birkhoff_sum (\<lambda>x. f x - g x) n x = birkhoff_sum f n x - birkhoff_sum g n x"
unfolding birkhoff_sum_def by (simp add: setsum_subtractf)

lemma birkhoff_sum_cmult:
  fixes f::"_ \<Rightarrow> real"
  shows "birkhoff_sum (\<lambda>x. c * f x) n x = c * birkhoff_sum f n x"
unfolding birkhoff_sum_def by (simp add: setsum_right_distrib)

lemma skew_product_real_iterates:
  fixes f::"'a \<Rightarrow> real"
  shows "((\<lambda>(x,y). (T x, y + f x))^^n) (x,y) = ((T^^n) x, y + birkhoff_sum f n x)"
apply (induction n)
apply (auto)
apply (metis (no_types, lifting) Suc_eq_plus1 birkhoff_sum_cocycle qmpt.birkhoff_sum_1(2) qmpt_axioms)
done

end

lemma (in mpt) birkhoff_sum_integral:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes [measurable]: "integrable M f"
  shows "integrable M (birkhoff_sum f n)" "(\<integral>x. birkhoff_sum f n x \<partial>M) =  n *\<^sub>R (\<integral>x. f x \<partial>M)"
proof -
  have a: "\<And>k. integrable M (\<lambda>x. f((T^^k) x))"
    using  Tn_integral_preserving(1) assms by blast
  then have "integrable M (\<lambda>x. \<Sum>k\<in>{..<n}. f((T^^k) x))" by simp
  then have "integrable M (\<lambda>x. birkhoff_sum f n x)" unfolding birkhoff_sum_def by auto
  then show "integrable M (birkhoff_sum f n)" by simp

  have b: "\<And>k. (\<integral>x. f((T^^k)x) \<partial>M) = (\<integral>x. f x \<partial>M)"
    using  Tn_integral_preserving(2) assms by blast
  have "(\<integral>x. birkhoff_sum f n x \<partial>M) = (\<integral>x. (\<Sum>k\<in>{..<n}. f((T^^k) x)) \<partial>M)"
    unfolding birkhoff_sum_def by blast
  also have "... =  (\<Sum>k\<in>{..<n}.  (\<integral>x. f((T^^k) x) \<partial>M))"
    by (rule integral_setsum, simp add: a)
  also have "... =  (\<Sum>k\<in>{..<n}.  (\<integral>x. f x \<partial>M))" using b by simp
  also have "... = n *\<^sub>R (\<integral>x. f x \<partial>M)" by (simp add: setsum_constant_scaleR)
  finally show "(\<integral>x. birkhoff_sum f n x \<partial>M) =  n *\<^sub>R (\<integral>x. f x \<partial>M)" by simp
qed


lemma (in mpt) birkhoff_sum_nn_integral:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes [measurable]: "f \<in> borel_measurable M" and pos: "\<And>x. f x \<ge> 0"
  shows "(\<integral>\<^sup>+x. birkhoff_sum f n x \<partial>M) =  n * (\<integral>\<^sup>+x. f x \<partial>M)"
proof -
  have [measurable]: "\<And>k. (\<lambda>x. f((T^^k)x)) \<in> borel_measurable M" by simp
  have posk: "\<And>k x.  f((T^^k)x) \<ge> 0" using pos by simp
  have b: "\<And>k. (\<integral>\<^sup>+x. f((T^^k)x) \<partial>M) = (\<integral>\<^sup>+x. f x \<partial>M)"
    using  Tn_nn_integral_preserving assms by blast
  have "(\<integral>\<^sup>+x. birkhoff_sum f n x \<partial>M) = (\<integral>\<^sup>+x. (\<Sum>k\<in>{..<n}. f((T^^k) x)) \<partial>M)"
    unfolding birkhoff_sum_def by blast
  also have "... =  (\<Sum>k\<in>{..<n}.  (\<integral>\<^sup>+x. f((T^^k) x) \<partial>M))"
    by (rule nn_integral_setsum, auto simp add: posk)
  also have "... =  (\<Sum>k\<in>{..<n}.  (\<integral>\<^sup>+x. f x \<partial>M))" using b by simp
  also have "... = n * (\<integral>\<^sup>+x. f x \<partial>M)" by (simp add: setsum_constant_ereal mult.commute)
  finally show "(\<integral>\<^sup>+x. birkhoff_sum f n x \<partial>M) =  n * (\<integral>\<^sup>+x. f x \<partial>M)" by simp
qed

end