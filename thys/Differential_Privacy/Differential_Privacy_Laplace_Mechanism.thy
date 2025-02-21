(*
 Title:Differential_Privacy_Laplace_Mechanism.thy
 Author: Tetsuya Sato
*)

theory Differential_Privacy_Laplace_Mechanism
  imports"Differential_Privacy_Divergence"
    "Laplace_Distribution"
begin

section \<open>Laplace mechanism \<close>

subsection \<open>Laplace mechanism as a noise-adding mechanism\<close>

subsubsection \<open>Laplace distribution with scale \<open>b\<close> and average \<open>\<mu>\<close>\<close>

definition Lap_dist :: "real \<Rightarrow> real \<Rightarrow> real measure" where
  "Lap_dist b \<mu> = (if b \<le> 0 then return borel \<mu> else density lborel (laplace_density b \<mu>))"

lemma shows prob_space_Lap_dist[simp,intro]: "prob_space (Lap_dist b x)"
  and subprob_space_Lap_dist[simp,intro]: "subprob_space (Lap_dist b x)"
  and sets_Lap_dist[measurable_cong]: "sets (Lap_dist b x) = sets borel"
  and space_Lap_dist: "space (Lap_dist \<epsilon> x) = UNIV"
  using prob_space_laplacian_density prob_space_return[of x borel] prob_space_imp_subprob_space sets_eq_imp_space_eq Lap_dist_def
  by(cases "b \<le> 0",auto)

(*
Future work:
lemma measurable_Lap_dist'[measurable]:
 shows "(\<lambda>(b,\<mu>). Lap_dist b \<mu>) \<in> borel \<Otimes>\<^sub>M borel \<rightarrow>\<^sub>M prob_algebra borel"
 unfolding Lap_dist_def case_prod_beta proof(subst measurable_If_restrict_space_iff)
 show "{x \<in> space (borel \<Otimes>\<^sub>M borel). fst x \<le> 0} \<in> sets (borel \<Otimes>\<^sub>M borel)"
*)

lemma measurable_Lap_dist[measurable]:
  shows "Lap_dist b \<in> borel \<rightarrow>\<^sub>M prob_algebra borel"
proof(cases"b \<le> 0")
  case True
  then show ?thesis unfolding Lap_dist_def by auto
next
  case False
  thus ?thesis
  proof(intro measurable_prob_algebraI)
    show " \<And>x. x \<in> space borel \<Longrightarrow> prob_space (Lap_dist b x)"
      by auto
    show "Lap_dist b \<in> borel \<rightarrow>\<^sub>M subprob_algebra borel"
    proof(rule measurable_subprob_algebra_generated[where \<Omega>=UNIV and G="(range (\<lambda> a :: real. {..a}))"])
      show pow1: "(range (\<lambda> a :: real. {..a})) \<subseteq> Pow UNIV"
        by auto
      show "sets borel = sigma_sets UNIV (range (\<lambda> a :: real. {..a}))"
        using borel_eq_atMost by (metis pow1 sets_measure_of)
      show "Int_stable (range (\<lambda> a :: real. {..a}))"
        by(subst Int_stable_def,auto)
      show "\<And>a. a \<in> space borel \<Longrightarrow> subprob_space (Lap_dist b a)"
        by (auto simp: prob_space_imp_subprob_space)
      show "\<And>a. a \<in> space borel \<Longrightarrow> sets (Lap_dist b a) = sets borel"
        by (auto simp: sets_Lap_dist)
      show "\<And>A. A \<in> range atMost \<Longrightarrow> (\<lambda>a. emeasure (Lap_dist b a) A) \<in> borel \<rightarrow>\<^sub>M borel"
      proof(safe,unfold Lap_dist_def)
        fix x :: real assume "x \<in> UNIV"
        have "(\<lambda>a :: real. emeasure (density lborel (\<lambda>x :: real. ennreal (laplace_density b a x))) {..x}) = (\<lambda>a. laplace_CDF b a x)"
          using emeasure_laplace_density False by auto
        also have "... \<in> borel \<rightarrow>\<^sub>M borel"
          using borel_measurable_laplace_CDF2 by auto
        finally show "(\<lambda>a :: real. emeasure (if b \<le> (0 :: real) then return borel a else density lborel (\<lambda>x :: real. ennreal (laplace_density b a x))) {..x}) \<in> borel \<rightarrow>\<^sub>M borel"
          using False by auto
      qed
      have "(\<lambda>a. emeasure (Lap_dist b a) UNIV) = (\<lambda>a. 1)"
        using Lap_dist_def emeasure_laplace_density_mass_1 by auto
      thus "(\<lambda>a. emeasure (Lap_dist b a) UNIV) \<in> borel \<rightarrow>\<^sub>M borel"
        by auto
    qed
  qed
qed

lemma Lap_dist_space_prob_algebra[simp,measurable]:
  shows "(Lap_dist b x) \<in> space (prob_algebra borel)"
  by (metis iso_tuple_UNIV_I measurable_Lap_dist measurable_space space_borel)

lemma Lap_dist_space_subprob_algebra[simp,measurable]:
  shows "(Lap_dist b x) \<in> space (subprob_algebra borel)"
  by (metis UNIV_I measurable_Lap_dist measurable_prob_algebraD measurable_space space_borel)

subsubsection \<open> The Laplace distribution with scale \<open>b\<close> and average \<open>0\<close>\<close>

definition "Lap_dist0 b \<equiv> Lap_dist b 0 "

text \<open> Actually @{term "Lap_dist b" } is a noise-addition of Laplace distribution with scale \<open>b\<close> and average \<open>0\<close>.\<close>

lemma shows prob_space_Lap_dist0[simp,intro,measurable]: "prob_space (Lap_dist0 b)"
  and subprob_space_Lap_dist0[simp,intro,measurable]: "subprob_space (Lap_dist0 b)"
  and sets_Lap_dist0[measurable_cong]: "sets (Lap_dist0 b) = sets borel"
  and space_Lap_dist0: "space (Lap_dist0 b) = UNIV"
  and Lap_dist0_space_prob_algebra[simp,measurable]: "(Lap_dist0 b) \<in> space (prob_algebra borel)"
  and Lap_dist0_space_subprob_algebra[simp,measurable]: "(Lap_dist0 b) \<in> space (subprob_algebra borel)"
  unfolding Lap_dist0_def by(auto simp:sets_Lap_dist space_Lap_dist)


lemma Lap_dist_def2:
  shows "(Lap_dist b x) = do{r \<leftarrow> Lap_dist0 b; return borel (x + r)}"
proof-
  show " Lap_dist b x = Lap_dist0 b \<bind> (\<lambda>r. return borel (x + r))"
  proof(cases"b \<le> 0")
    case True
    hence " Lap_dist b x = return borel x"
      by(auto simp: Lap_dist_def)
    also have "... = return borel 0 \<bind> (\<lambda>r. return borel (x + r))"
      by(subst bind_return, measurable)
    also have "... = do{r \<leftarrow> Lap_dist0 b; return borel (x + r)}"
      by(auto simp: Lap_dist0_def Lap_dist_def True)
    finally show ?thesis.
  next
    case False
    hence "(Lap_dist b x) = density lborel (laplace_density b x)"
      by(auto simp: Lap_dist_def)
    also have "... = density ( distr lborel borel ((+) x)) (laplace_density b x) "
      by(auto simp: Lebesgue_Measure.lborel_distr_plus[of x])
    also have "... = (density lborel (laplace_density b 0)) \<bind> (\<lambda>r. return borel (x + r))"
    proof(subst bind_return_distr')
      show " density (distr lborel borel ((+) x)) (\<lambda>xa. ennreal (laplace_density b x xa)) =
 distr (density lborel (\<lambda>x. ennreal (laplace_density b 0 x))) borel ((+) x)"
      proof(subst density_distr)
        show "distr (density lborel (\<lambda>xa. ennreal (laplace_density b x (x + xa)))) borel ((+) x) =
 distr (density lborel (\<lambda>x. ennreal (laplace_density b 0 x))) borel ((+) x)"
          using laplace_density_shift[of b "0::real" x ] by (auto simp: add.commute)
      qed(auto)
    qed(auto)
    also have "... = do{r \<leftarrow> Lap_dist0 b; return borel (x + r)}"
      by(auto simp: Lap_dist_def Lap_dist0_def False)
    finally show ?thesis.
  qed
qed

corollary Lap_dist_shift:
  shows "(Lap_dist b (x + y)) = do{r \<leftarrow> Lap_dist b x; return borel (y + r)}"
  unfolding Lap_dist_def2
  by(subst bind_assoc[where N = borel and R = borel],auto simp: bind_return[where N = borel] Lap_dist0_def ac_simps)

subsubsection \<open>Differential Privacy of Laplace noise addition \<close>

proposition DP_divergence_Lap_dist':
  assumes "b > 0"
    and "\<bar> x - y \<bar> \<le> r"
  shows "DP_divergence (Lap_dist b x) (Lap_dist b y) (r / b) \<le> (0 :: real)"
proof(cases"r = 0")
  case True
  hence 0:"x = y"
    using assms(2) by auto
  have "DP_divergence (Lap_dist b x) (Lap_dist b y) (r / b) \<le> (0 :: real)"
    by (auto simp: DP_divergence_reflexivity True 0)
  thus ?thesis by argo
next
  case False
  hence posr: "r > 0"using assms(2) by auto
  show "DP_divergence (Lap_dist b x) (Lap_dist b y) (r / b) \<le> ereal 0"
  proof(intro DP_divergence_leI,unfold Lap_dist_def)
    fix A :: "real set" assume " A \<in> sets (if b \<le> 0 then return borel x else density lborel (\<lambda>s. ennreal (laplace_density b x s))) "
    hence A[measurable]: "A \<in> sets borel"
      using assms by (metis (mono_tags, lifting) sets_density sets_lborel sets_return)
    have pos[simp]: "b > 0"
      using posr assms by auto
    hence nonneg[simp]: "b \<ge> 0"
      by argo
    have "Sigma_Algebra.measure (if b \<le> 0 then return borel x else density lborel (\<lambda>xa. ennreal (laplace_density b x xa))) A =
 (Sigma_Algebra.emeasure (density lborel (\<lambda>xa. ennreal (laplace_density b x xa))) A)"
      using pos by(split if_split, intro conjI impI, linarith) (metis emeasure_eq_ennreal_measure emeasure_laplace_density_mass_1 emeasure_mono ennreal_one_less_top leD pos sets_density sets_lborel space_in_borel top_greatest)
    also have "... = (\<integral>\<^sup>+ z. ennreal (laplace_density b x z) * indicator A z \<partial>lborel)"
      by(rule emeasure_density,auto intro: A)
    also have "... \<le> (\<integral>\<^sup>+ z. (exp (r / b)) * ennreal (laplace_density b y z) * indicator A z \<partial>lborel)"
    proof(rule nn_integral_mono)
      fix z :: real assume z: "z \<in>space lborel"
      have 0: "-\<bar>z - x\<bar> \<le> r - \<bar>z - y\<bar>"
        using assms(2) posr by auto
      hence 1: " exp (- \<bar>z - x\<bar> / b ) \<le>exp (( r - \<bar>z - y \<bar>)/ b) "
        by(subst exp_le_cancel_iff, intro divide_right_mono, auto)
      have "ennreal (laplace_density b x z) = exp (- \<bar>z - x\<bar> / b ) / (2 * b)"
        by(auto simp: laplace_density_def z)
      also have "... \<le> exp (( r - \<bar>z - y \<bar>) / b ) / (2 * b)"
      proof(subst ennreal_le_iff)
        show "0 \<le> exp ((r - \<bar>z - y\<bar>) / b) / (2 * b)"
          by auto
        show " exp (- \<bar>z - x\<bar> / b) / (2 * b) \<le> exp ((r - \<bar>z - y\<bar>) / b) / (2 * b)"
          by(subst divide_right_mono, rule 1,auto)
      qed
      also have "... = exp (- \<bar>z - y \<bar>/ b + r / b ) / (2 * b)"
        by argo
      also have "... = (exp (- \<bar>z - y \<bar>/ b) * exp ( r / b )) / (2 * b)"
        using exp_add[of "- \<bar>z - y \<bar>/ b" " r / b"] by auto
      also have "... = exp ( r / b) * (exp (- \<bar>z - y \<bar>/ b)) / (2 * b)"
        by argo
      also have "... = exp (r / b) * (laplace_density b y z)"
        by(auto simp: laplace_density_def)
      finally have "ennreal (laplace_density b x z) \<le> ennreal (exp (r / b) * laplace_density b y z)" .

      thus "ennreal (laplace_density b x z) * indicator A z \<le> ennreal (exp (r / b)) * ennreal (laplace_density b y z) * indicator A z"
        by (simp add: ennreal_mult' mult_right_mono)
    qed
    also have "... = (\<integral>\<^sup>+ z. (exp (r / b)) * ( ennreal (laplace_density b y z) * indicator A z) \<partial>lborel)"
      by (auto simp: mult.assoc)
    also have "... = (exp (r / b)) * (\<integral>\<^sup>+ z. ennreal (laplace_density b y z) * indicator A z \<partial>lborel)"
      by(rule nn_integral_cmult, auto)
    also have "... = (exp (r / b)) * (Sigma_Algebra.emeasure (density lborel (\<lambda>xa. ennreal (laplace_density b y xa))) A)"
      by(subst emeasure_density,auto intro: A)
    also have "... = ennreal (exp (r / b)) * ennreal (Sigma_Algebra.measure (if b \<le> 0 then return borel y else density lborel (\<lambda>xa. ennreal (laplace_density b y xa))) A)"
      using pos by(split if_split, intro conjI impI, linarith)(metis emeasure_eq_ennreal_measure emeasure_laplace_density_mass_1 emeasure_mono ennreal_one_less_top leD pos sets_density sets_lborel space_in_borel top_greatest)
    also have "... = (exp (r / b)) * (Sigma_Algebra.measure (if b \<le> 0 then return borel y else density lborel (\<lambda>xa. ennreal (laplace_density b y xa))) A)"
      by (auto simp: ennreal_mult'')
    finally show "measure (if b \<le> 0 then return borel x else density lborel (\<lambda>xa. ennreal (laplace_density b x xa))) A
 \<le> exp (r / b) * measure (if b \<le> 0 then return borel y else density lborel (\<lambda>x. ennreal (laplace_density b y x))) A + 0"
      by auto
  qed
qed

corollary DP_divergence_Lap_dist'_eps:
  assumes "\<epsilon> > 0"
    and "\<bar> x - y \<bar> \<le> r"
  shows "DP_divergence (Lap_dist (r / \<epsilon>) x) (Lap_dist (r / \<epsilon>) y) \<epsilon> \<le> (0 :: real)"
proof(cases "r = 0")
  case True
  with assms have 1: "x = y" and 2: " (r / \<epsilon>) = 0"
    by auto
  thus ?thesis
    unfolding 1 2 using DP_divergence_reflexivity'[of \<epsilon>  "Lap_dist 0 y" ] assms by auto
next
  case False
  with assms have 0: "0 < r" and 1: "0 < (r / \<epsilon>)"
    by auto
  show ?thesis
    using 0 DP_divergence_Lap_dist'[OF 1 assms(2)] by auto
qed

corollary DP_divergence_Lap_dist_eps:
  assumes "\<epsilon> > 0"
    and "\<bar> x - y \<bar> \<le> 1"
  shows "DP_divergence (Lap_dist (1 / \<epsilon>) x) (Lap_dist (1 / \<epsilon>) y) \<epsilon> \<le> (0 :: real)"
  using DP_divergence_Lap_dist'_eps[of \<epsilon> x y 1] assms by auto

end