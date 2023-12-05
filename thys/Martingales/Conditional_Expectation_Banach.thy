(*  Author:     Ata Keskin, TU München 
*)

theory Conditional_Expectation_Banach
  imports "HOL-Probability.Conditional_Expectation" "HOL-Probability.Independent_Family" Bochner_Integration_Supplement
begin

section \<open>Conditional Expectation in Banach Spaces\<close>

text \<open>While constructing the conditional expectation operator, we have come up with the following approach, which is based on the construction in \cite{Hytoenen_2016}. 
      Both our approach, and the one in \cite{Hytoenen_2016} are based on showing that the conditional expectation is a contraction on some dense subspace of the space of functions \<open>L\<^sup>1(E)\<close>.
      In our approach, we start by constructing the conditional expectation explicitly for simple functions. 
      Then we show that the conditional expectation is a contraction on simple functions, i.e. \<open>\<parallel>E(s|F)(x)\<parallel> \<le> E(\<parallel>s(x)\<parallel>|F)\<close> for \<open>\<mu>\<close>-almost all \<open>x \<in> \<Omega>\<close> with \<open>s : \<Omega> \<rightarrow> E\<close> simple and integrable. 
      Using this, we can show that the conditional expectation of a convergent sequence of simple functions is again convergent. 
      Finally, we show that this limit exhibits the properties of a conditional expectation. 
      This approach has the benefit of being straightforward and easy to implement, since we could make use of the existing formalization for real-valued functions.
      To use the construction in \cite{Hytoenen_2016} we need more tools from functional analysis, which Isabelle/HOL currently does not have.\<close>

text \<open>Before we can talk about 'the' conditional expectation, we must define what it means for a function to have a conditional expectation.\<close>

definition has_cond_exp :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b::{real_normed_vector, second_countable_topology}) \<Rightarrow> bool" where 
  "has_cond_exp M F f g = ((\<forall>A \<in> sets F. (\<integral> x \<in> A. f x \<partial>M) = (\<integral> x \<in> A. g x \<partial>M))
                        \<and> integrable M f 
                        \<and> integrable M g 
                        \<and> g \<in> borel_measurable F)"

text \<open>This predicate precisely characterizes what it means for a function \<^term>\<open>f\<close> to have a conditional expectation \<^term>\<open>g\<close>,
      with respect to the measure \<^term>\<open>M\<close> and the sub-\<open>\<sigma>\<close>-algebra \<^term>\<open>F\<close>.\<close>

lemma has_cond_expI':
  assumes "\<And>A. A \<in> sets F \<Longrightarrow> (\<integral> x \<in> A. f x \<partial>M) = (\<integral> x \<in> A. g x \<partial>M)"
          "integrable M f"
          "integrable M g"
          "g \<in> borel_measurable F"
  shows "has_cond_exp M F f g"
  using assms unfolding has_cond_exp_def by simp

lemma has_cond_expD:
  assumes "has_cond_exp M F f g"
  shows "\<And>A. A \<in> sets F \<Longrightarrow> (\<integral> x \<in> A. f x \<partial>M) = (\<integral> x \<in> A. g x \<partial>M)"
        "integrable M f"
        "integrable M g"
        "g \<in> borel_measurable F"
  using assms unfolding has_cond_exp_def by simp+

text \<open>Now we can use Hilbert’s \<open>\<some>\<close>-operator to define the conditional expectation, if it exists.\<close>

definition cond_exp :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b::{banach, second_countable_topology})" where
  "cond_exp M F f = (if \<exists>g. has_cond_exp M F f g then (SOME g. has_cond_exp M F f g) else (\<lambda>_. 0))"

lemma borel_measurable_cond_exp[measurable]: "cond_exp M F f \<in> borel_measurable F" 
  by (metis cond_exp_def someI has_cond_exp_def borel_measurable_const)

lemma integrable_cond_exp[intro]: "integrable M (cond_exp M F f)" 
  by (metis cond_exp_def has_cond_expD(3) integrable_zero someI)

lemma set_integrable_cond_exp[intro]:
  assumes "A \<in> sets M"
  shows "set_integrable M A (cond_exp M F f)" using integrable_mult_indicator[OF assms integrable_cond_exp, of F f] by (auto simp add: set_integrable_def intro!: integrable_mult_indicator[OF assms integrable_cond_exp])

lemma has_cond_exp_self: 
  assumes "integrable M f"
  shows "has_cond_exp M (vimage_algebra (space M) f borel) f f"
  using assms by (auto intro!: has_cond_expI' measurable_vimage_algebra1)

lemma has_cond_exp_sets_cong:
  assumes "sets F = sets G"
  shows "has_cond_exp M F = has_cond_exp M G"
  using assms unfolding has_cond_exp_def by force

lemma cond_exp_sets_cong:
  assumes "sets F = sets G"
  shows "AE x in M. cond_exp M F f x = cond_exp M G f x"
  by (intro AE_I2, simp add: cond_exp_def has_cond_exp_sets_cong[OF assms, of M])

context sigma_finite_subalgebra
begin

lemma borel_measurable_cond_exp'[measurable]: "cond_exp M F f \<in> borel_measurable M"
  by (metis cond_exp_def someI has_cond_exp_def borel_measurable_const subalg measurable_from_subalg)

lemma cond_exp_null: 
  assumes "\<nexists>g. has_cond_exp M F f g" 
  shows "cond_exp M F f = (\<lambda>_. 0)"
  unfolding cond_exp_def using assms by argo

text \<open>We state the tower property of the conditional expectation in terms of the predicate \<^term>\<open>has_cond_exp\<close>.\<close>

lemma has_cond_exp_nested_subalg:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes "subalgebra G F" "has_cond_exp M F f h" "has_cond_exp M G f h'"
  shows "has_cond_exp M F h' h"
  by (intro has_cond_expI') (metis assms has_cond_expD in_mono subalgebra_def)+

text \<open>The following lemma shows that the conditional expectation is unique as an element of L1, given that it exists.\<close>

lemma has_cond_exp_charact:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes "has_cond_exp M F f g"
  shows "has_cond_exp M F f (cond_exp M F f)"
        "AE x in M. cond_exp M F f x = g x"
proof -
  show cond_exp: "has_cond_exp M F f (cond_exp M F f)" using assms someI cond_exp_def by metis
  let ?MF = "restr_to_subalg M F"
  interpret sigma_finite_measure ?MF by (rule sigma_fin_subalg)
  {
    fix A assume "A \<in> sets ?MF"
    then have [measurable]: "A \<in> sets F" using sets_restr_to_subalg[OF subalg] by simp
    have "(\<integral>x \<in> A. g x \<partial>?MF) = (\<integral>x \<in> A. g x \<partial>M)" using assms subalg by (auto simp add: integral_subalgebra2 set_lebesgue_integral_def dest!: has_cond_expD)
    also have "... = (\<integral>x \<in> A. cond_exp M F f x \<partial>M)" using assms cond_exp by (simp add: has_cond_exp_def)
    also have "... = (\<integral>x \<in> A. cond_exp M F f x \<partial>?MF)" using subalg by (auto simp add: integral_subalgebra2 set_lebesgue_integral_def)
    finally have "(\<integral>x \<in> A. g x \<partial>?MF) = (\<integral>x \<in> A. cond_exp M F f x \<partial>?MF)" by simp
  }
  hence "AE x in ?MF. cond_exp M F f x = g x" using cond_exp assms subalg by (intro density_unique_banach, auto dest: has_cond_expD intro!: integrable_in_subalg)
  then show "AE x in M. cond_exp M F f x = g x" using AE_restr_to_subalg[OF subalg] by simp
qed

corollary cond_exp_charact:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes "\<And>A. A \<in> sets F \<Longrightarrow> (\<integral> x \<in> A. f x \<partial>M) = (\<integral> x \<in> A. g x \<partial>M)"
          "integrable M f"
          "integrable M g"
          "g \<in> borel_measurable F"
    shows "AE x in M. cond_exp M F f x = g x"
  by (intro has_cond_exp_charact has_cond_expI' assms) auto

text \<open>Identity on F-measurable functions:\<close>

text \<open>If an integrable function \<^term>\<open>f\<close> is already \<^term>\<open>F\<close>-measurable, then \<^term>\<open>cond_exp M F f = f\<close> \<open>\<mu>\<close>-a.e.
      This is a corollary of the lemma on the characterization of \<^term>\<open>cond_exp\<close>.\<close>
corollary cond_exp_F_meas[intro, simp]:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes "integrable M f"
          "f \<in> borel_measurable F"
    shows "AE x in M. cond_exp M F f x = f x"
  by (rule cond_exp_charact, auto intro: assms)

text \<open>Congruence\<close>

lemma has_cond_exp_cong:
  assumes "integrable M f" "\<And>x. x \<in> space M \<Longrightarrow> f x = g x" "has_cond_exp M F g h"
  shows "has_cond_exp M F f h"
proof (intro has_cond_expI'[OF _ assms(1)])
  fix A assume asm: "A \<in> sets F"
  hence "set_lebesgue_integral M A f = set_lebesgue_integral M A g" by (intro set_lebesgue_integral_cong) (meson assms(2) subalg in_mono subalgebra_def sets.sets_into_space subalgebra_def subsetD)+
  thus "set_lebesgue_integral M A f = set_lebesgue_integral M A h" using asm assms(3) by (simp add: has_cond_exp_def)
qed (auto simp add: has_cond_expD[OF assms(3)])

lemma cond_exp_cong:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "integrable M f" "integrable M g" "\<And>x. x \<in> space M \<Longrightarrow> f x = g x"
  shows "AE x in M. cond_exp M F f x = cond_exp M F g x"
proof (cases "\<exists>h. has_cond_exp M F f h")
  case True
  then obtain h where h: "has_cond_exp M F f h" "has_cond_exp M F g h" using has_cond_exp_cong assms by metis 
  show ?thesis using h[THEN has_cond_exp_charact(2)] by fastforce
next
  case False
  moreover have "\<nexists>h. has_cond_exp M F g h" using False has_cond_exp_cong assms by auto
  ultimately show ?thesis unfolding cond_exp_def by auto
qed

lemma has_cond_exp_cong_AE:
  assumes "integrable M f" "AE x in M. f x = g x" "has_cond_exp M F g h"
  shows "has_cond_exp M F f h"
  using assms(1,2) subalg subalgebra_def subset_iff 
  by (intro has_cond_expI', subst set_lebesgue_integral_cong_AE[OF _ assms(1)[THEN borel_measurable_integrable] borel_measurable_integrable(1)[OF has_cond_expD(2)[OF assms(3)]]]) 
     (fast intro: has_cond_expD[OF assms(3)] integrable_cong_AE_imp[OF _ _ AE_symmetric])+

lemma has_cond_exp_cong_AE':
  assumes "h \<in> borel_measurable F" "AE x in M. h x = h' x" "has_cond_exp M F f h'"
  shows "has_cond_exp M F f h"
  using assms(1, 2) subalg subalgebra_def subset_iff
  using AE_restr_to_subalg2[OF subalg assms(2)] measurable_from_subalg
  by (intro has_cond_expI' , subst set_lebesgue_integral_cong_AE[OF _ measurable_from_subalg(1,1)[OF subalg], OF _ assms(1) has_cond_expD(4)[OF assms(3)]])
     (fast intro: has_cond_expD[OF assms(3)] integrable_cong_AE_imp[OF _ _ AE_symmetric])+

lemma cond_exp_cong_AE:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "integrable M f" "integrable M g" "AE x in M. f x = g x"
  shows "AE x in M. cond_exp M F f x = cond_exp M F g x"
proof (cases "\<exists>h. has_cond_exp M F f h")
  case True
  then obtain h where h: "has_cond_exp M F f h" "has_cond_exp M F g h" using has_cond_exp_cong_AE assms by (metis (mono_tags, lifting) eventually_mono)
  show ?thesis using h[THEN has_cond_exp_charact(2)] by fastforce
next
  case False
  moreover have "\<nexists>h. has_cond_exp M F g h" using False has_cond_exp_cong_AE assms by auto
  ultimately show ?thesis unfolding cond_exp_def by auto
qed

text \<open>The conditional expectation operator on the reals, \<^term>\<open>real_cond_exp\<close>, satisfies the conditions of the conditional expectation as we have defined it.\<close>
lemma has_cond_exp_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes "integrable M f"
  shows "has_cond_exp M F f (real_cond_exp M F f)"
  by (intro has_cond_expI', auto intro!: real_cond_exp_intA assms)

lemma cond_exp_real[intro]:
  fixes f :: "'a \<Rightarrow> real"
  assumes "integrable M f"
  shows "AE x in M. cond_exp M F f x = real_cond_exp M F f x" 
  using has_cond_exp_charact has_cond_exp_real assms by blast

lemma cond_exp_cmult:
  fixes f :: "'a \<Rightarrow> real"
  assumes "integrable M f"
  shows "AE x in M. cond_exp M F (\<lambda>x. c * f x) x = c * cond_exp M F f x"
  using real_cond_exp_cmult[OF assms(1), of c] assms(1)[THEN cond_exp_real] assms(1)[THEN integrable_mult_right, THEN cond_exp_real, of c] by fastforce

subsection \<open>Existence\<close>

text \<open>Showing the existence is a bit involved. Specifically, what we aim to show is that \<^term>\<open>has_cond_exp M F f (cond_exp M F f)\<close> holds for any Bochner-integrable \<^term>\<open>f\<close>.
      We will employ the standard machinery of measure theory. First, we will prove existence for indicator functions. 
      Then we will extend our proof by linearity to simple functions. 
      Finally we use a limiting argument to show that the conditional expectation exists for all Bochner-integrable functions.\<close>

text \<open>Indicator functions\<close>

lemma has_cond_exp_indicator:
  assumes "A \<in> sets M" "emeasure M A < \<infinity>"
  shows "has_cond_exp M F (\<lambda>x. indicat_real A x *\<^sub>R y) (\<lambda>x. real_cond_exp M F (indicator A) x *\<^sub>R y)"
proof (intro has_cond_expI', goal_cases)
  case (1 B)
  have "\<integral>x\<in>B. (indicat_real A x *\<^sub>R y) \<partial>M  = (\<integral>x\<in>B. indicat_real A x \<partial>M) *\<^sub>R y" using assms by (intro set_integral_scaleR_left, meson 1 in_mono subalg subalgebra_def, blast)
  also have "... = (\<integral>x\<in>B. real_cond_exp M F (indicator A) x \<partial>M) *\<^sub>R y" using 1 assms by (subst real_cond_exp_intA, auto)
  also have "... = \<integral>x\<in>B. (real_cond_exp M F (indicator A) x *\<^sub>R y) \<partial>M" using assms by (intro set_integral_scaleR_left[symmetric], meson 1 in_mono subalg subalgebra_def, blast)
  finally show ?case .
next
  case 2
  show ?case using integrable_scaleR_left integrable_real_indicator assms by blast
next
  case 3
  show ?case using assms by (intro integrable_scaleR_left, intro real_cond_exp_int, blast+)
next
  case 4
  show ?case by (intro borel_measurable_scaleR, intro Conditional_Expectation.borel_measurable_cond_exp, simp)
qed

lemma cond_exp_indicator[intro]:
  fixes y :: "'b::{second_countable_topology,banach}"
  assumes [measurable]: "A \<in> sets M" "emeasure M A < \<infinity>"
  shows "AE x in M. cond_exp M F (\<lambda>x. indicat_real A x *\<^sub>R y) x = cond_exp M F (indicator A) x *\<^sub>R y"
proof -
  have "AE x in M. cond_exp M F (\<lambda>x. indicat_real A x *\<^sub>R y) x = real_cond_exp M F (indicator A) x *\<^sub>R y" using has_cond_exp_indicator[OF assms] has_cond_exp_charact by blast
  thus ?thesis using cond_exp_real[OF integrable_real_indicator, OF assms] by fastforce
qed

text \<open>Addition\<close>

lemma has_cond_exp_add:
  fixes f g :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "has_cond_exp M F f f'" "has_cond_exp M F g g'"
  shows "has_cond_exp M F (\<lambda>x. f x + g x) (\<lambda>x. f' x + g' x)"
proof (intro has_cond_expI', goal_cases)
  case (1 A)
  have "\<integral>x\<in>A. (f x + g x)\<partial>M = (\<integral>x\<in>A. f x \<partial>M) + (\<integral>x\<in>A. g x \<partial>M)" using assms[THEN has_cond_expD(2)] subalg 1 by (intro set_integral_add(2), auto simp add: subalgebra_def set_integrable_def intro: integrable_mult_indicator)
  also have "... = (\<integral>x\<in>A. f' x \<partial>M) + (\<integral>x\<in>A. g' x \<partial>M)" using assms[THEN has_cond_expD(1)[OF _ 1]] by argo
  also have "... = \<integral>x\<in>A. (f' x + g' x)\<partial>M" using assms[THEN has_cond_expD(3)] subalg 1 by (intro set_integral_add(2)[symmetric], auto simp add: subalgebra_def set_integrable_def intro: integrable_mult_indicator)
  finally show ?case .
next
  case 2
  show ?case by (metis Bochner_Integration.integrable_add assms has_cond_expD(2))
next
  case 3
  show ?case by (metis Bochner_Integration.integrable_add assms has_cond_expD(3))
next
  case 4
  show ?case using assms borel_measurable_add has_cond_expD(4) by blast
qed

lemma has_cond_exp_scaleR_right:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "has_cond_exp M F f f'"
  shows "has_cond_exp M F (\<lambda>x. c *\<^sub>R f x) (\<lambda>x. c *\<^sub>R f' x)"
  using has_cond_expD[OF assms] by (intro has_cond_expI', auto)

lemma cond_exp_scaleR_right:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "integrable M f"
  shows "AE x in M. cond_exp M F (\<lambda>x. c *\<^sub>R f x) x = c *\<^sub>R cond_exp M F f x"
proof (cases "\<exists>f'. has_cond_exp M F f f'")
  case True
  then show ?thesis using assms has_cond_exp_charact has_cond_exp_scaleR_right by metis
next
  case False
  show ?thesis
  proof (cases "c = 0")
    case True
    then show ?thesis by simp
  next
    case c_nonzero: False
    have "\<nexists>f'. has_cond_exp M F (\<lambda>x. c *\<^sub>R f x) f'"
    proof (standard, goal_cases)
      case 1
      then obtain f' where f': "has_cond_exp M F (\<lambda>x. c *\<^sub>R f x) f'" by blast
      have "has_cond_exp M F f (\<lambda>x. inverse c *\<^sub>R f' x)" using has_cond_expD[OF f'] divideR_right[OF c_nonzero] assms by (intro has_cond_expI', auto)
      then show ?case using False by blast
    qed
    then show ?thesis using cond_exp_null[OF False] cond_exp_null by force
  qed 
qed

lemma cond_exp_uminus:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "integrable M f"
  shows "AE x in M. cond_exp M F (\<lambda>x. - f x) x = - cond_exp M F f x"
  using cond_exp_scaleR_right[OF assms, of "-1"] by force

text \<open>Together with the induction scheme \<open>integrable_simple_function_induct\<close>, we can show that the conditional expectation of an integrable simple function exists.\<close>

corollary has_cond_exp_simple:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "simple_function M f" "emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity>"
  shows "has_cond_exp M F f (cond_exp M F f)"
  using assms
proof (induction rule: integrable_simple_function_induct)
  case (cong f g)
  then show ?case using has_cond_exp_cong by (metis (no_types, opaque_lifting) Bochner_Integration.integrable_cong has_cond_expD(2) has_cond_exp_charact(1))
next
  case (indicator A y)
  then show ?case using has_cond_exp_charact[OF has_cond_exp_indicator] by fast
next
  case (add u v)
  then show ?case using has_cond_exp_add has_cond_exp_charact(1) by blast
qed

text \<open>Now comes the most difficult part. Given a convergent sequence of integrable simple functions \<^term>\<open>\<lambda>n. s n\<close>, 
      we must show that the sequence \<^term>\<open>\<lambda>n. cond_exp M F (s n)\<close> is also convergent. Furthermore, we must show that this limit satisfies the properties of a conditional expectation. 
      Unfortunately, we will only be able to show that this sequence convergences in the L1-norm. 
      Luckily, this is enough to show that the operator \<^term>\<open>cond_exp M F\<close> preserves limits as a function from L1 to L1.\<close>

text \<open>In anticipation of this result, we show that the conditional expectation operator is a contraction for simple functions.
      We first reformulate the lemma \<open>real_cond_exp_abs\<close>, which shows the statement for real-valued functions, using our definitions. 
      Then we show the statement for simple functions via induction.\<close>

lemma cond_exp_contraction_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes integrable[measurable]: "integrable M f"
  shows "AE x in M. norm (cond_exp M F f x) \<le> cond_exp M F (\<lambda>x. norm (f x)) x"
proof-
  have int: "integrable M (\<lambda>x. norm (f x))" using assms by blast
  have *: "AE x in M. 0 \<le> cond_exp M F (\<lambda>x. norm (f x)) x" using cond_exp_real[THEN AE_symmetric, OF integrable_norm[OF integrable]] real_cond_exp_ge_c[OF integrable_norm[OF integrable], of 0] norm_ge_zero by fastforce
  have **: "A \<in> sets F \<Longrightarrow> \<integral>x\<in>A. \<bar>f x\<bar> \<partial>M = \<integral>x\<in>A. real_cond_exp M F (\<lambda>x. norm (f x)) x \<partial>M" for A unfolding real_norm_def using assms integrable_abs real_cond_exp_intA by blast
  
  have norm_int: "A \<in> sets F \<Longrightarrow> (\<integral>x\<in>A. \<bar>f x\<bar> \<partial>M) = (\<integral>\<^sup>+x\<in>A. \<bar>f x\<bar> \<partial>M)" for A using assms by (intro nn_set_integral_eq_set_integral[symmetric], blast, fastforce) (meson subalg subalgebra_def subsetD)
  
  have "AE x in M. real_cond_exp M F (\<lambda>x. norm (f x)) x \<ge> 0" using int real_cond_exp_ge_c by force
  hence cond_exp_norm_int: "A \<in> sets F \<Longrightarrow> (\<integral>x\<in>A. real_cond_exp M F (\<lambda>x. norm (f x)) x \<partial>M) = (\<integral>\<^sup>+x\<in>A. real_cond_exp M F (\<lambda>x. norm (f x)) x \<partial>M)" for A using assms by (intro nn_set_integral_eq_set_integral[symmetric], blast, fastforce) (meson subalg subalgebra_def subsetD)
  
  have "A \<in> sets F \<Longrightarrow> \<integral>\<^sup>+x\<in>A. \<bar>f x\<bar>\<partial>M = \<integral>\<^sup>+x\<in>A. real_cond_exp M F (\<lambda>x. norm (f x)) x \<partial>M" for A using ** norm_int cond_exp_norm_int by (auto simp add: nn_integral_set_ennreal)
  moreover have "(\<lambda>x. ennreal \<bar>f x\<bar>) \<in> borel_measurable M" by measurable
  moreover have "(\<lambda>x. ennreal (real_cond_exp M F (\<lambda>x. norm (f x)) x)) \<in> borel_measurable F" by measurable
  ultimately have "AE x in M. nn_cond_exp M F (\<lambda>x. ennreal \<bar>f x\<bar>) x = real_cond_exp M F (\<lambda>x. norm (f x)) x" by (intro nn_cond_exp_charact[THEN AE_symmetric], auto)
  hence "AE x in M. nn_cond_exp M F (\<lambda>x. ennreal \<bar>f x\<bar>) x \<le> cond_exp M F (\<lambda>x. norm (f x)) x" using cond_exp_real[OF int] by force
  moreover have "AE x in M. \<bar>real_cond_exp M F f x\<bar> = norm (cond_exp M F f x)" unfolding real_norm_def using cond_exp_real[OF assms] * by force
  ultimately have "AE x in M. ennreal (norm (cond_exp M F f x)) \<le> cond_exp M F (\<lambda>x. norm (f x)) x" using real_cond_exp_abs[OF assms[THEN borel_measurable_integrable]] by fastforce
  hence "AE x in M. enn2real (ennreal (norm (cond_exp M F f x))) \<le> enn2real (cond_exp M F (\<lambda>x. norm (f x)) x)" using ennreal_le_iff2 by force
  thus ?thesis using * by fastforce
qed

lemma cond_exp_contraction_simple:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes "simple_function M f" "emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity>"
  shows "AE x in M. norm (cond_exp M F f x) \<le> cond_exp M F (\<lambda>x. norm (f x)) x"
  using assms
proof (induction rule: integrable_simple_function_induct)
  case (cong f g)
  hence ae: "AE x in M. f x = g x" by blast
  hence "AE x in M. cond_exp M F f x = cond_exp M F g x" using cong has_cond_exp_simple by (subst cond_exp_cong_AE) (auto intro!: has_cond_expD(2))
  hence "AE x in M. norm (cond_exp M F f x) = norm (cond_exp M F g x)" by force
  moreover have "AE x in M. cond_exp M F (\<lambda>x. norm (f x)) x = cond_exp M F (\<lambda>x. norm (g x)) x"  using ae cong has_cond_exp_simple by (subst cond_exp_cong_AE) (auto dest: has_cond_expD)
  ultimately show ?case using cong(6) by fastforce
next
  case (indicator A y)
  hence "AE x in M. cond_exp M F (\<lambda>a. indicator A a *\<^sub>R y) x = cond_exp M F (indicator A) x *\<^sub>R y" by blast
  hence *: "AE x in M. norm (cond_exp M F (\<lambda>a. indicat_real A a *\<^sub>R y) x) \<le> norm y * cond_exp M F (\<lambda>x. norm (indicat_real A x)) x" using cond_exp_contraction_real[OF integrable_real_indicator, OF indicator] by fastforce

  have "AE x in M. norm y * cond_exp M F (\<lambda>x. norm (indicat_real A x)) x = norm y * real_cond_exp M F (\<lambda>x. norm (indicat_real A x)) x" using cond_exp_real[OF integrable_real_indicator, OF indicator] by fastforce
  moreover have "AE x in M. cond_exp M F (\<lambda>x. norm y * norm (indicat_real A x)) x = real_cond_exp M F (\<lambda>x. norm y * norm (indicat_real A x)) x" using indicator by (intro cond_exp_real, auto)
  ultimately have "AE x in M. norm y * cond_exp M F (\<lambda>x. norm (indicat_real A x)) x = cond_exp M F (\<lambda>x. norm y * norm (indicat_real A x)) x" using real_cond_exp_cmult[of "\<lambda>x. norm (indicat_real A x)" "norm y"] indicator by fastforce
  moreover have "(\<lambda>x. norm y * norm (indicat_real A x)) = (\<lambda>x. norm (indicat_real A x *\<^sub>R y))" by force
  ultimately show ?case using * by force
next
  case (add u v)
  have "AE x in M. norm (cond_exp M F (\<lambda>a. u a + v a) x) = norm (cond_exp M F u x + cond_exp M F v x)" using has_cond_exp_charact(2)[OF has_cond_exp_add, OF has_cond_exp_simple(1,1), OF add(1,2,3,4)] by fastforce
  moreover have "AE x in M. norm (cond_exp M F u x + cond_exp M F v x) \<le> norm (cond_exp M F u x) + norm (cond_exp M F v x)" using norm_triangle_ineq by blast
  moreover have "AE x in M. norm (cond_exp M F u x) + norm (cond_exp M F v x) \<le> cond_exp M F (\<lambda>x. norm (u x)) x + cond_exp M F (\<lambda>x. norm (v x)) x" using add(6,7) by fastforce
  moreover have "AE x in M. cond_exp M F (\<lambda>x. norm (u x)) x + cond_exp M F (\<lambda>x. norm (v x)) x = cond_exp M F (\<lambda>x. norm (u x) + norm (v x)) x" using integrable_simple_function[OF add(1,2)] integrable_simple_function[OF add(3,4)] by (intro has_cond_exp_charact(2)[OF has_cond_exp_add[OF has_cond_exp_charact(1,1)], THEN AE_symmetric], auto intro: has_cond_exp_real)
  moreover have "AE x in M. cond_exp M F (\<lambda>x. norm (u x) + norm (v x)) x = cond_exp M F (\<lambda>x. norm (u x + v x)) x" using add(5) integrable_simple_function[OF add(1,2)] integrable_simple_function[OF add(3,4)] by (intro cond_exp_cong, auto)
  ultimately show ?case by force
qed

lemma has_cond_exp_simple_lim:
    fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes integrable[measurable]: "integrable M f"
      and "\<And>i. simple_function M (s i)"
      and "\<And>i. emeasure M {y \<in> space M. s i y \<noteq> 0} \<noteq> \<infinity>"
      and "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. s i x) \<longlonglongrightarrow> f x"
      and "\<And>x i. x \<in> space M \<Longrightarrow> norm (s i x) \<le> 2 * norm (f x)"
  obtains r 
  where "strict_mono r" "has_cond_exp M F f (\<lambda>x. lim (\<lambda>i. cond_exp M F (s (r i)) x))" 
        "AE x in M. convergent (\<lambda>i. cond_exp M F (s (r i)) x)"
proof -
  have [measurable]: "(s i) \<in> borel_measurable M" for i using assms(2) by (simp add: borel_measurable_simple_function)
  have integrable_s: "integrable M (\<lambda>x. s i x)" for i using assms integrable_simple_function by blast
  have integrable_4f: "integrable M (\<lambda>x. 4 * norm (f x))" using assms(1) by simp
  have integrable_2f: "integrable M (\<lambda>x. 2 * norm (f x))" using assms(1) by simp
  have integrable_2_cond_exp_norm_f: "integrable M (\<lambda>x. 2 * cond_exp M F (\<lambda>x. norm (f x)) x)" by fast

  have "emeasure M {y \<in> space M. s i y - s j y \<noteq> 0} \<le>  emeasure M {y \<in> space M. s i y \<noteq> 0} + emeasure M {y \<in> space M. s j y \<noteq> 0}" for i j using simple_functionD(2)[OF assms(2)] by (intro order_trans[OF emeasure_mono emeasure_subadditive], auto)
  hence fin_sup: "emeasure M {y \<in> space M. s i y - s j y \<noteq> 0} \<noteq> \<infinity>" for i j using assms(3) by (metis (mono_tags) ennreal_add_eq_top linorder_not_less top.not_eq_extremum infinity_ennreal_def)

  have "emeasure M {y \<in> space M. norm (s i y - s j y) \<noteq> 0} \<le>  emeasure M {y \<in> space M. s i y \<noteq> 0} + emeasure M {y \<in> space M. s j y \<noteq> 0}" for i j using simple_functionD(2)[OF assms(2)] by (intro order_trans[OF emeasure_mono emeasure_subadditive], auto)
  hence fin_sup_norm: "emeasure M {y \<in> space M. norm (s i y - s j y) \<noteq> 0} \<noteq> \<infinity>" for i j using assms(3) by (metis (mono_tags) ennreal_add_eq_top linorder_not_less top.not_eq_extremum infinity_ennreal_def)

  have Cauchy: "Cauchy (\<lambda>n. s n x)" if "x \<in> space M" for x using assms(4) LIMSEQ_imp_Cauchy that by blast
  hence bounded_range_s: "bounded (range (\<lambda>n. s n x))" if "x \<in> space M" for x using that cauchy_imp_bounded by fast

  text \<open>Since the sequence \<^term>\<open>(\<lambda>n. s n x)\<close> is Cauchy for almost all \<^term>\<open>x\<close>, we know that the diameter tends to zero almost everywhere.\<close>
  text \<open>Dominated convergence tells us that the integral of the diameter also converges to zero.\<close>
  have "AE x in M. (\<lambda>n. diameter {s i x | i. n \<le> i}) \<longlonglongrightarrow> 0" using Cauchy cauchy_iff_diameter_tends_to_zero_and_bounded by fast
  moreover have "(\<lambda>x. diameter {s i x |i. n \<le> i}) \<in> borel_measurable M" for n using bounded_range_s borel_measurable_diameter by measurable
  moreover have "AE x in M. norm (diameter {s i x |i. n \<le> i}) \<le> 4 * norm (f x)" for n
  proof - 
    {
      fix x assume x: "x \<in> space M"
      have "diameter {s i x |i. n \<le> i} \<le> 2 * norm (f x) + 2 * norm (f x)" by (intro diameter_le, blast, subst dist_norm[symmetric], intro dist_triangle3[THEN order_trans, of 0], intro add_mono) (auto intro: assms(5)[OF x])
      hence "norm (diameter {s i x |i. n \<le> i}) \<le> 4 * norm (f x)" using diameter_ge_0[OF bounded_subset[OF bounded_range_s], OF x, of "{s i x |i. n \<le> i}"] by force
    }
    thus ?thesis by fast
  qed
  ultimately have diameter_tendsto_zero: "(\<lambda>n. LINT x|M. diameter {s i x | i. n \<le> i}) \<longlonglongrightarrow> 0" by (intro integral_dominated_convergence[OF borel_measurable_const[of 0] _ integrable_4f, simplified]) (fast+)
  
  have diameter_integrable: "integrable M (\<lambda>x. diameter {s i x | i. n \<le> i})" for n using assms(1,5) 
    by (intro integrable_bound_diameter[OF bounded_range_s integrable_2f], auto)

  have dist_integrable: "integrable M (\<lambda>x. dist (s i x) (s j x))" for i j  using assms(5) dist_triangle3[of "s i _" _ 0, THEN order_trans, OF add_mono, of _ "2 * norm (f _)"]
    by (intro Bochner_Integration.integrable_bound[OF integrable_4f]) fastforce+

  text \<open>Since \<^term>\<open>cond_exp M F\<close> is a contraction for simple functions, the following sequence of integral values is also Cauchy.\<close>
  text \<open>This follows, since the distance between the terms of this sequence are always less than or equal to the diameter, which itself converges to zero.\<close>
  text \<open>Hence, we obtain a subsequence which is Cauchy almost everywhere.\<close>
  have "\<exists>N. \<forall>i\<ge>N. \<forall>j\<ge>N. LINT x|M. norm (cond_exp M F (s i) x - cond_exp M F (s j) x) < e" if e_pos: "e > 0" for e
  proof -
    obtain N where *: "LINT x|M. diameter {s i x | i. n \<le> i} < e" if "n \<ge> N" for n using that order_tendsto_iff[THEN iffD1, OF diameter_tendsto_zero, unfolded eventually_sequentially] e_pos by presburger
    {
      fix i j x assume asm: "i \<ge> N" "j \<ge> N" "x \<in> space M"
      have "case_prod dist ` ({s i x |i. N \<le> i} \<times> {s i x |i. N \<le> i}) = case_prod (\<lambda>i j. dist (s i x) (s j x)) ` ({N..} \<times> {N..})" by fast
      hence "diameter {s i x | i. N \<le> i} = (SUP (i, j) \<in> {N..} \<times> {N..}. dist (s i x) (s j x))" unfolding diameter_def by auto
      moreover have "(SUP (i, j) \<in> {N..} \<times> {N..}. dist (s i x) (s j x)) \<ge> dist (s i x) (s j x)" using asm bounded_imp_bdd_above[OF bounded_imp_dist_bounded, OF bounded_range_s] by (intro cSup_upper, auto)
      ultimately have "diameter {s i x | i. N \<le> i} \<ge> dist (s i x) (s j x)" by presburger
    }
    hence "LINT x|M. dist (s i x) (s j x) < e" if "i \<ge> N" "j \<ge> N" for i j using that * by (intro integral_mono[OF dist_integrable diameter_integrable, THEN order.strict_trans1], blast+)
    moreover have "LINT x|M. norm (cond_exp M F (s i) x - cond_exp M F (s j) x) \<le> LINT x|M. dist (s i x) (s j x)" for i j
    proof -
      have "LINT x|M. norm (cond_exp M F (s i) x - cond_exp M F (s j) x) = LINT x|M. norm (cond_exp M F (s i) x + - 1 *\<^sub>R cond_exp M F (s j) x)" unfolding dist_norm by simp
      also have "... = LINT x|M. norm (cond_exp M F (\<lambda>x. s i x - s j x) x)" using has_cond_exp_charact(2)[OF has_cond_exp_add[OF _ has_cond_exp_scaleR_right, OF has_cond_exp_charact(1,1), OF has_cond_exp_simple(1,1)[OF assms(2,3)]], THEN AE_symmetric, of i "-1" j] by (intro integral_cong_AE) force+      
      also have "... \<le> LINT x|M. cond_exp M F (\<lambda>x. norm (s i x - s j x)) x" using cond_exp_contraction_simple[OF _ fin_sup, of i j] integrable_cond_exp assms(2) by (intro integral_mono_AE, fast+)
      also have "... = LINT x|M. norm (s i x - s j x)" unfolding set_integral_space(1)[OF integrable_cond_exp, symmetric] set_integral_space[OF dist_integrable[unfolded dist_norm], symmetric] by (intro has_cond_expD(1)[OF has_cond_exp_simple[OF _ fin_sup_norm], symmetric]) (metis assms(2) simple_function_compose1 simple_function_diff, metis sets.top subalg subalgebra_def)
      finally show ?thesis unfolding dist_norm .  
    qed
    ultimately show ?thesis using order.strict_trans1 by meson
  qed
  then obtain r where strict_mono_r: "strict_mono r" and AE_Cauchy: "AE x in M. Cauchy (\<lambda>i. cond_exp M F (s (r i)) x)"
    by (rule cauchy_L1_AE_cauchy_subseq[OF integrable_cond_exp], auto)
  hence ae_lim_cond_exp: "AE x in M. (\<lambda>n. cond_exp M F (s (r n)) x) \<longlonglongrightarrow> lim (\<lambda>n. cond_exp M F (s (r n)) x)" using Cauchy_convergent_iff convergent_LIMSEQ_iff by fastforce

  text \<open>Now that we have a candidate for the conditional expectation, we must show that it actually has the required properties.\<close>

  text \<open>Dominated convergence shows that this limit is indeed integrable.\<close>
  text \<open>Here, we again use the fact that conditional expectation is a contraction on simple functions.\<close>
  have cond_exp_bounded: "AE x in M. norm (cond_exp M F (s (r n)) x) \<le> cond_exp M F (\<lambda>x. 2 * norm (f x)) x" for n
  proof -
    have "AE x in M. norm (cond_exp M F (s (r n)) x) \<le> cond_exp M F (\<lambda>x. norm (s (r n) x)) x" by (rule cond_exp_contraction_simple[OF assms(2,3)])
    moreover have "AE x in M. real_cond_exp M F (\<lambda>x. norm (s (r n) x)) x \<le> real_cond_exp M F (\<lambda>x. 2 * norm (f x)) x" using integrable_s integrable_2f assms(5) by (intro real_cond_exp_mono, auto) 
    ultimately show ?thesis using cond_exp_real[OF integrable_norm, OF integrable_s, of "r n"] cond_exp_real[OF integrable_2f] by force
  qed
  have lim_integrable: "integrable M (\<lambda>x. lim (\<lambda>i. cond_exp M F (s (r i)) x))" by (intro integrable_dominated_convergence[OF _ borel_measurable_cond_exp' integrable_cond_exp ae_lim_cond_exp cond_exp_bounded], simp)

  text \<open>Moreover, we can use the DCT twice to show that the conditional expectation property holds, i.e. the value of the integral of the candidate, agrees with \<^term>\<open>f\<close> on sets \<^term>\<open>A \<in> F\<close>.\<close>
  {
    fix A assume A_in_sets_F: "A \<in> sets F"
    have "AE x in M. norm (indicator A x *\<^sub>R cond_exp M F (s (r n)) x) \<le> cond_exp M F (\<lambda>x. 2 * norm (f x)) x" for n
    proof -
      have "AE x in M. norm (indicator A x *\<^sub>R cond_exp M F (s (r n)) x) \<le> norm (cond_exp M F (s (r n)) x)" unfolding indicator_def by simp
      thus ?thesis using cond_exp_bounded[of n] by force
    qed
    hence lim_cond_exp_int: "(\<lambda>n. LINT x:A|M. cond_exp M F (s (r n)) x) \<longlonglongrightarrow> LINT x:A|M. lim (\<lambda>n. cond_exp M F (s (r n)) x)" 
      using ae_lim_cond_exp measurable_from_subalg[OF subalg borel_measurable_indicator, OF A_in_sets_F] cond_exp_bounded
      unfolding set_lebesgue_integral_def
      by (intro integral_dominated_convergence[OF borel_measurable_scaleR borel_measurable_scaleR integrable_cond_exp]) (fastforce simp add: tendsto_scaleR)+

    have "AE x in M. norm (indicator A x *\<^sub>R s (r n) x) \<le> 2 * norm (f x)" for n
    proof -
      have "AE x in M. norm (indicator A x *\<^sub>R s (r n) x) \<le> norm (s (r n) x)" unfolding indicator_def by simp
      thus ?thesis using assms(5)[of _ "r n"] by fastforce
    qed
    hence lim_s_int: "(\<lambda>n. LINT x:A|M. s (r n) x) \<longlonglongrightarrow> LINT x:A|M. f x"
      using measurable_from_subalg[OF subalg borel_measurable_indicator, OF A_in_sets_F] LIMSEQ_subseq_LIMSEQ[OF assms(4) strict_mono_r] assms(5)
      unfolding set_lebesgue_integral_def comp_def
      by (intro integral_dominated_convergence[OF borel_measurable_scaleR borel_measurable_scaleR integrable_2f]) (fastforce simp add: tendsto_scaleR)+

    have "LINT x:A|M. lim (\<lambda>n. cond_exp M F (s (r n)) x) = lim (\<lambda>n. LINT x:A|M. cond_exp M F (s (r n)) x)" using limI[OF lim_cond_exp_int] by argo
    also have "... = lim (\<lambda>n. LINT x:A|M. s (r n) x)" using has_cond_expD(1)[OF has_cond_exp_simple[OF assms(2,3)] A_in_sets_F, symmetric] by presburger
    also have "... = LINT x:A|M. f x" using limI[OF lim_s_int] by argo
    finally have "LINT x:A|M. lim (\<lambda>n. cond_exp M F (s (r n)) x) = LINT x:A|M. f x" .
  }
  text \<open>Putting it all together, we have the statement we are looking for.\<close>
  hence "has_cond_exp M F f (\<lambda>x. lim (\<lambda>i. cond_exp M F (s (r i)) x))" using assms(1) lim_integrable by (intro has_cond_expI', auto) 
  thus thesis using AE_Cauchy Cauchy_convergent strict_mono_r by (auto intro!: that)
qed

text \<open>Now, we can show that the conditional expectation is well-defined for all integrable functions.\<close>
corollary has_cond_expI:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "integrable M f"
  shows "has_cond_exp M F f (cond_exp M F f)"
proof -
  obtain s where s_is: "\<And>i. simple_function M (s i)" "\<And>i. emeasure M {y \<in> space M. s i y \<noteq> 0} \<noteq> \<infinity>" "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. s i x) \<longlonglongrightarrow> f x" "\<And>x i. x \<in> space M \<Longrightarrow> norm (s i x) \<le> 2 * norm (f x)" using integrable_implies_simple_function_sequence[OF assms] by blast
  show ?thesis using has_cond_exp_simple_lim[OF assms s_is] has_cond_exp_charact(1) by metis
qed

subsection \<open>Properties\<close>

text \<open>The defining property of the conditional expectation now always holds, given that the function \<^term>\<open>f\<close> is integrable.\<close>

lemma cond_exp_set_integral:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "integrable M f" "A \<in> sets F"
  shows "(\<integral> x \<in> A. f x \<partial>M) = (\<integral> x \<in> A. cond_exp M F f x \<partial>M)"
  using has_cond_expD(1)[OF has_cond_expI, OF assms] by argo

(* Tower Property *)

text \<open>The following property of the conditional expectation is called the "Tower Property".\<close>

lemma cond_exp_nested_subalg:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "integrable M f" "subalgebra M G" "subalgebra G F"
  shows "AE \<xi> in M. cond_exp M F f \<xi> = cond_exp M F (cond_exp M G f) \<xi>"
  using has_cond_expI assms sigma_finite_subalgebra_def by (auto intro!: has_cond_exp_nested_subalg[THEN has_cond_exp_charact(2), THEN AE_symmetric] sigma_finite_subalgebra.has_cond_expI[OF sigma_finite_subalgebra.intro[OF assms(2)]] nested_subalg_is_sigma_finite)

(* Linearity *)

text \<open>The conditional expectation is linear.\<close>

lemma cond_exp_add:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "integrable M f" "integrable M g"
  shows "AE x in M. cond_exp M F (\<lambda>x. f x + g x) x = cond_exp M F f x + cond_exp M F g x"
  using has_cond_exp_add[OF has_cond_expI(1,1), OF assms, THEN has_cond_exp_charact(2)] .

lemma cond_exp_diff:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes "integrable M f" "integrable M g"
  shows "AE x in M. cond_exp M F (\<lambda>x. f x - g x) x = cond_exp M F f x - cond_exp M F g x"
  using has_cond_exp_add[OF _ has_cond_exp_scaleR_right, OF has_cond_expI(1,1), OF assms, THEN has_cond_exp_charact(2), of "-1"] by simp

lemma cond_exp_diff':
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes "integrable M f" "integrable M g"
  shows "AE x in M. cond_exp M F (f - g) x = cond_exp M F f x - cond_exp M F g x"
  unfolding fun_diff_def using assms by (rule cond_exp_diff)

lemma cond_exp_scaleR_left:
  fixes f :: "'a \<Rightarrow> real"
  assumes "integrable M f"
  shows "AE x in M. cond_exp M F (\<lambda>x. f x *\<^sub>R c) x = cond_exp M F f x *\<^sub>R c" 
  using cond_exp_set_integral[OF assms] subalg assms unfolding subalgebra_def
  by (intro cond_exp_charact,
      subst set_integral_scaleR_left, blast, intro assms, 
      subst set_integral_scaleR_left, blast, intro integrable_cond_exp)
      auto

text \<open>The conditional expectation operator is a contraction, i.e. a bounded linear operator with operator norm less than or equal to 1.\<close>
text \<open>To show this we first obtain a subsequence \<^term>\<open>\<lambda>x. (\<lambda>i. s (r i) x)\<close>, such that \<^term>\<open>(\<lambda>i. cond_exp M F (s (r i)) x)\<close> converges to \<^term>\<open>cond_exp M F f x\<close> a.e. 
      Afterwards, we obtain a sub-subsequence \<^term>\<open>\<lambda>x. (\<lambda>i. s (r (r' i)) x)\<close>, such that  \<^term>\<open>(\<lambda>i. cond_exp M F (\<lambda>x. norm (s (r i))) x)\<close> converges to \<^term>\<open>cond_exp M F (\<lambda>x. norm (f x)) x\<close> a.e.
      Finally, we show that the inequality holds by showing that the terms of the subsequences obey the inequality and the fact that a subsequence of a convergent sequence converges to the same limit.\<close>

lemma cond_exp_contraction:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes "integrable M f"
  shows "AE x in M. norm (cond_exp M F f x) \<le> cond_exp M F (\<lambda>x. norm (f x)) x" 
proof -
  obtain s where s: "\<And>i. simple_function M (s i)" "\<And>i. emeasure M {y \<in> space M. s i y \<noteq> 0} \<noteq> \<infinity>" "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. s i x) \<longlonglongrightarrow> f x" "\<And>i x. x \<in> space M \<Longrightarrow> norm (s i x) \<le> 2 * norm (f x)" 
    by (blast intro: integrable_implies_simple_function_sequence[OF assms])

  obtain r where r: "strict_mono r" and "has_cond_exp M F f (\<lambda>x. lim (\<lambda>i. cond_exp M F (s (r i)) x))" "AE x in M. (\<lambda>i. cond_exp M F (s (r i)) x) \<longlonglongrightarrow> lim (\<lambda>i. cond_exp M F (s (r i)) x)"
    using has_cond_exp_simple_lim[OF assms s] unfolding convergent_LIMSEQ_iff by blast
  hence r_tendsto: "AE x in M. (\<lambda>i. cond_exp M F (s (r i)) x) \<longlonglongrightarrow> cond_exp M F f x" using has_cond_exp_charact(2) by force

  have norm_s_r: "\<And>i. simple_function M (\<lambda>x. norm (s (r i) x))" "\<And>i. emeasure M {y \<in> space M. norm (s (r i) y) \<noteq> 0} \<noteq> \<infinity>" "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. norm (s (r i) x)) \<longlonglongrightarrow> norm (f x)" "\<And>i x. x \<in> space M \<Longrightarrow> norm (norm (s (r i) x)) \<le> 2 * norm (norm (f x))" 
    using s by (auto intro: LIMSEQ_subseq_LIMSEQ[OF tendsto_norm r, unfolded comp_def] simple_function_compose1) 
  
  obtain r' where r': "strict_mono r'" and "has_cond_exp M F (\<lambda>x. norm (f x)) (\<lambda>x. lim (\<lambda>i. cond_exp M F (\<lambda>x. norm (s (r (r' i)) x)) x))" "AE x in M. (\<lambda>i. cond_exp M F (\<lambda>x. norm (s (r (r' i)) x)) x) \<longlonglongrightarrow> lim (\<lambda>i. cond_exp M F (\<lambda>x. norm (s (r (r' i)) x)) x)" using has_cond_exp_simple_lim[OF integrable_norm norm_s_r, OF assms] unfolding convergent_LIMSEQ_iff by blast
  hence r'_tendsto: "AE x in M. (\<lambda>i. cond_exp M F (\<lambda>x. norm (s (r (r' i)) x)) x) \<longlonglongrightarrow> cond_exp M F (\<lambda>x. norm (f x)) x" using has_cond_exp_charact(2) by force

  have "AE x in M. \<forall>i. norm (cond_exp M F (s (r (r' i))) x) \<le> cond_exp M F (\<lambda>x. norm (s (r (r' i)) x)) x" using s by (auto intro: cond_exp_contraction_simple simp add: AE_all_countable)
  moreover have "AE x in M. (\<lambda>i. norm (cond_exp M F (s (r (r' i))) x)) \<longlonglongrightarrow> norm (cond_exp M F f x)" using r_tendsto LIMSEQ_subseq_LIMSEQ[OF tendsto_norm r', unfolded comp_def] by fast
  ultimately show ?thesis using LIMSEQ_le r'_tendsto by fast
qed

text \<open>The following lemmas are called "pulling out whats known". We first show the statement for real-valued functions using the lemma \<open>real_cond_exp_intg\<close>, which is already present.
      We then show it for arbitrary \<^term>\<open>g\<close> using the lecture notes of Gordan Zitkovic for the course "Theory of Probability I" \cite{Zitkovic_2015}.\<close>

lemma cond_exp_measurable_mult:
  fixes f g :: "'a \<Rightarrow> real"
  assumes [measurable]: "integrable M (\<lambda>x. f x * g x)" "integrable M g" "f \<in> borel_measurable F" 
  shows "integrable M (\<lambda>x. f x * cond_exp M F g x)"
        "AE x in M. cond_exp M F (\<lambda>x. f x * g x) x = f x * cond_exp M F g x"
proof-
  show integrable: "integrable M (\<lambda>x. f x * cond_exp M F g x)" using cond_exp_real[OF assms(2)] by (intro integrable_cong_AE_imp[OF real_cond_exp_intg(1), OF assms(1,3) assms(2)[THEN borel_measurable_integrable]] measurable_from_subalg[OF subalg]) auto
  interpret sigma_finite_measure "restr_to_subalg M F" by (rule sigma_fin_subalg)
  {
    fix A assume asm: "A \<in> sets F"
    hence asm': "A \<in> sets M" using subalg by (fastforce simp add: subalgebra_def)
    have "set_lebesgue_integral M A (cond_exp M F (\<lambda>x. f x * g x)) = set_lebesgue_integral M A (\<lambda>x. f x * g x)" by (simp add: cond_exp_set_integral[OF assms(1) asm])
    also have "... = set_lebesgue_integral M A (\<lambda>x. f x * real_cond_exp M F g x)" using borel_measurable_times[OF borel_measurable_indicator[OF asm] assms(3)] borel_measurable_integrable[OF assms(2)] integrable_mult_indicator[OF asm' assms(1)] by (fastforce simp add: set_lebesgue_integral_def mult.assoc[symmetric] intro: real_cond_exp_intg(2)[symmetric])
    also have "... = set_lebesgue_integral M A (\<lambda>x. f x * cond_exp M F g x)" using cond_exp_real[OF assms(2)] asm' borel_measurable_cond_exp' borel_measurable_cond_exp2 measurable_from_subalg[OF subalg assms(3)] by (auto simp add: set_lebesgue_integral_def intro: integral_cong_AE)
    finally have "set_lebesgue_integral M A (cond_exp M F (\<lambda>x. f x * g x)) = \<integral>x\<in>A. (f x * cond_exp M F g x)\<partial>M" .
  }
  hence "AE x in restr_to_subalg M F. cond_exp M F (\<lambda>x. f x * g x) x = f x * cond_exp M F g x" by (intro density_unique_banach integrable_cond_exp integrable integrable_in_subalg subalg, measurable, simp add: set_lebesgue_integral_def integral_subalgebra2[OF subalg] sets_restr_to_subalg[OF subalg])
  thus "AE x in M. cond_exp M F (\<lambda>x. f x * g x) x = f x * cond_exp M F g x" by (rule AE_restr_to_subalg[OF subalg])
qed

lemma cond_exp_measurable_scaleR:
  fixes f :: "'a \<Rightarrow> real" and g :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes [measurable]: "integrable M (\<lambda>x. f x *\<^sub>R g x)" "integrable M g" "f \<in> borel_measurable F"
  shows "integrable M (\<lambda>x. f x *\<^sub>R cond_exp M F g x)"
        "AE x in M. cond_exp M F (\<lambda>x. f x *\<^sub>R g x) x = f x *\<^sub>R cond_exp M F g x"
proof -
  let ?F = "restr_to_subalg M F"
  have subalg': "subalgebra M (restr_to_subalg M F)" by (metis sets_eq_imp_space_eq sets_restr_to_subalg subalg subalgebra_def)
  {
    fix z assume asm[measurable]: "integrable M (\<lambda>x. z x *\<^sub>R g x)" "z \<in> borel_measurable ?F"
    hence asm'[measurable]: "z \<in> borel_measurable F" using measurable_in_subalg' subalg by blast
    have "integrable M (\<lambda>x. z x *\<^sub>R cond_exp M F g x)" "LINT x|M. z x *\<^sub>R g x = LINT x|M. z x *\<^sub>R cond_exp M F g x"
    proof -
      obtain s where s_is: "\<And>i. simple_function ?F (s i)" "\<And>x. x \<in> space ?F \<Longrightarrow> (\<lambda>i. s i x) \<longlonglongrightarrow> z x" "\<And>i x. x \<in> space ?F \<Longrightarrow> norm (s i x) \<le> 2 * norm (z x)" using borel_measurable_implies_sequence_metric[OF asm(2), of 0] by force

      text \<open>We need to apply the dominated convergence theorem twice, therefore we need to show the following prerequisites.\<close>

      have s_scaleR_g_tendsto: "AE x in M. (\<lambda>i. s i x *\<^sub>R g x) \<longlonglongrightarrow> z x *\<^sub>R g x" using s_is(2) by (simp add: space_restr_to_subalg tendsto_scaleR)
      have s_scaleR_cond_exp_g_tendsto: "AE x in ?F. (\<lambda>i. s i x *\<^sub>R cond_exp M F g x) \<longlonglongrightarrow> z x *\<^sub>R cond_exp M F g x" using s_is(2) by (simp add: tendsto_scaleR)

      have s_scaleR_g_meas: "(\<lambda>x. s i x *\<^sub>R g x) \<in> borel_measurable M" for i using s_is(1)[THEN borel_measurable_simple_function, THEN subalg'[THEN measurable_from_subalg]] by simp
      have s_scaleR_cond_exp_g_meas: "(\<lambda>x. s i x *\<^sub>R cond_exp M F g x) \<in> borel_measurable ?F" for i using s_is(1)[THEN borel_measurable_simple_function] measurable_in_subalg[OF subalg borel_measurable_cond_exp] by (fastforce intro: borel_measurable_scaleR)

      have s_scaleR_g_AE_bdd: "AE x in M. norm (s i x *\<^sub>R g x) \<le> 2 * norm (z x *\<^sub>R g x)" for i using s_is(3) by (fastforce simp add: space_restr_to_subalg mult.assoc[symmetric] mult_right_mono)
      {
        fix i
        have asm: "integrable M (\<lambda>x. norm (z x) * norm (g x))" using asm(1)[THEN integrable_norm] by simp
        have "AE x in ?F. norm (s i x *\<^sub>R cond_exp M F g x) \<le> 2 * norm (z x) * norm (cond_exp M F g x)" using s_is(3) by (fastforce simp add: mult_mono)
        moreover have "AE x in ?F. norm (z x) * cond_exp M F (\<lambda>x. norm (g x)) x = cond_exp M F (\<lambda>x. norm (z x) * norm (g x)) x" by (rule cond_exp_measurable_mult(2)[THEN AE_symmetric, OF asm integrable_norm, OF assms(2), THEN AE_restr_to_subalg2[OF subalg]], auto)
        ultimately have "AE x in ?F. norm (s i x *\<^sub>R cond_exp M F g x) \<le> 2 * cond_exp M F (\<lambda>x. norm (z x *\<^sub>R g x)) x" using cond_exp_contraction[OF assms(2), THEN AE_restr_to_subalg2[OF subalg]] order_trans[OF _ mult_mono] by fastforce
      }
      note s_scaleR_cond_exp_g_AE_bdd = this

      text \<open>In the following section we need to pay attention to which measures we are using for integration. The rhs is F-measurable while the lhs is only M-measurable.\<close>

      {
        fix i
        have s_meas_M[measurable]: "s i \<in> borel_measurable M" by (meson borel_measurable_simple_function measurable_from_subalg s_is(1) subalg')
        have s_meas_F[measurable]: "s i \<in> borel_measurable F" by (meson borel_measurable_simple_function measurable_in_subalg' s_is(1) subalg)

        have s_scaleR_eq: "s i x *\<^sub>R h x = (\<Sum>y\<in>s i ` space M. (indicator (s i -` {y} \<inter> space M) x *\<^sub>R y) *\<^sub>R h x)" if "x \<in> space M" for x and h :: "'a \<Rightarrow> 'b" using simple_function_indicator_representation[OF s_is(1), of x i] that unfolding space_restr_to_subalg scaleR_left.sum[of _ _ "h x", symmetric] by presburger
        
        have "LINT x|M. s i x *\<^sub>R g x = LINT x|M. (\<Sum>y\<in>s i ` space M. indicator (s i -` {y} \<inter> space M) x *\<^sub>R y *\<^sub>R g x)" using s_scaleR_eq by (intro Bochner_Integration.integral_cong) auto
        also have "... = (\<Sum>y\<in>s i ` space M. LINT x|M. indicator (s i -` {y} \<inter> space M) x *\<^sub>R y *\<^sub>R g x)" by (intro Bochner_Integration.integral_sum integrable_mult_indicator[OF _ integrable_scaleR_right] assms(2)) simp
        also have "... = (\<Sum>y\<in>s i ` space M.  y *\<^sub>R set_lebesgue_integral M (s i -` {y} \<inter> space M) g)" by (simp only: set_lebesgue_integral_def[symmetric]) simp
        also have "... = (\<Sum>y\<in>s i ` space M.  y *\<^sub>R set_lebesgue_integral M (s i -` {y} \<inter> space M) (cond_exp M F g))" using assms(2) subalg borel_measurable_vimage[OF s_meas_F] by (subst cond_exp_set_integral, auto simp add: subalgebra_def) 
        also have "... = (\<Sum>y\<in>s i ` space M. LINT x|M. indicator (s i -` {y} \<inter> space M) x *\<^sub>R y *\<^sub>R cond_exp M F g x)" by (simp only: set_lebesgue_integral_def[symmetric]) simp
        also have "... = LINT x|M. (\<Sum>y\<in>s i ` space M. indicator (s i -` {y} \<inter> space M) x *\<^sub>R y *\<^sub>R cond_exp M F g x)" by (intro Bochner_Integration.integral_sum[symmetric] integrable_mult_indicator[OF _ integrable_scaleR_right]) auto
        also have "... = LINT x|M. s i x *\<^sub>R cond_exp M F g x" using s_scaleR_eq by (intro Bochner_Integration.integral_cong) auto
        finally have "LINT x|M. s i x *\<^sub>R g x = LINT x|?F. s i x *\<^sub>R cond_exp M F g x" by (simp add: integral_subalgebra2[OF subalg])
      }
      note integral_s_eq = this

      text \<open>Now we just plug in the results we obtained into DCT, and use the fact that limits are unique.\<close>

      show "integrable M (\<lambda>x. z x *\<^sub>R cond_exp M F g x)" using s_scaleR_cond_exp_g_meas asm(2) borel_measurable_cond_exp' by (intro integrable_from_subalg[OF subalg] integrable_cond_exp integrable_dominated_convergence[OF _ _ _ s_scaleR_cond_exp_g_tendsto s_scaleR_cond_exp_g_AE_bdd]) (auto intro: measurable_from_subalg[OF subalg] integrable_in_subalg measurable_in_subalg subalg)
         
      have "(\<lambda>i. LINT x|M. s i x *\<^sub>R g x) \<longlonglongrightarrow> LINT x|M. z x *\<^sub>R g x" using s_scaleR_g_meas asm(1)[THEN integrable_norm] asm' borel_measurable_cond_exp' by (intro integral_dominated_convergence[OF _ _ _ s_scaleR_g_tendsto s_scaleR_g_AE_bdd]) (auto intro: measurable_from_subalg[OF subalg])
      moreover have "(\<lambda>i. LINT x|?F. s i x *\<^sub>R cond_exp M F g x) \<longlonglongrightarrow> LINT x|?F. z x *\<^sub>R cond_exp M F g x" using s_scaleR_cond_exp_g_meas asm(2) borel_measurable_cond_exp' by (intro integral_dominated_convergence[OF _ _ _ s_scaleR_cond_exp_g_tendsto s_scaleR_cond_exp_g_AE_bdd]) (auto intro: measurable_from_subalg[OF subalg] integrable_in_subalg measurable_in_subalg subalg)
      ultimately show "LINT x|M. z x *\<^sub>R g x = LINT x|M. z x *\<^sub>R cond_exp M F g x" using integral_s_eq using subalg by (simp add: LIMSEQ_unique integral_subalgebra2)
    qed
  }
  note * = this

  text \<open>The main statement now follows with \<^term>\<open>z = (\<lambda>x. indicator A x * f x)\<close>.\<close>
  show "integrable M (\<lambda>x. f x *\<^sub>R cond_exp M F g x)" using * assms measurable_in_subalg[OF subalg] by blast

  {
    fix A assume asm: "A \<in> F"
    hence "integrable M (\<lambda>x. indicat_real A x *\<^sub>R f x *\<^sub>R g x)" using subalg by (fastforce simp add: subalgebra_def intro!: integrable_mult_indicator assms(1))
    hence "set_lebesgue_integral M A (\<lambda>x. f x *\<^sub>R g x) = set_lebesgue_integral M A (\<lambda>x. f x *\<^sub>R cond_exp M F g x)" unfolding set_lebesgue_integral_def using asm by (auto intro!: * measurable_in_subalg[OF subalg])
  }
  thus "AE x in M. cond_exp M F (\<lambda>x. f x *\<^sub>R g x) x = f x *\<^sub>R cond_exp M F g x" using borel_measurable_cond_exp by (intro cond_exp_charact, auto intro!: * assms measurable_in_subalg[OF subalg])
qed

lemma cond_exp_sum [intro, simp]:
  fixes f :: "'t \<Rightarrow> 'a \<Rightarrow> 'b :: {second_countable_topology,banach}"
  assumes [measurable]: "\<And>i. integrable M (f i)"
  shows "AE x in M. cond_exp M F (\<lambda>x. \<Sum>i\<in>I. f i x) x = (\<Sum>i\<in>I. cond_exp M F (f i) x)"
proof (rule has_cond_exp_charact, intro has_cond_expI')
  fix A assume [measurable]: "A \<in> sets F"
  then have A_meas [measurable]: "A \<in> sets M" by (meson subsetD subalg subalgebra_def)

  have "(\<integral>x\<in>A. (\<Sum>i\<in>I. f i x)\<partial>M) = (\<integral>x. (\<Sum>i\<in>I. indicator A x *\<^sub>R f i x)\<partial>M)" unfolding set_lebesgue_integral_def by (simp add: scaleR_sum_right)
  also have "... = (\<Sum>i\<in>I. (\<integral>x. indicator A x *\<^sub>R f i x \<partial>M))" using assms by (auto intro!: Bochner_Integration.integral_sum integrable_mult_indicator)
  also have "... = (\<Sum>i\<in>I. (\<integral>x. indicator A x *\<^sub>R cond_exp M F (f i) x \<partial>M))" using cond_exp_set_integral[OF assms] by (simp add: set_lebesgue_integral_def)
  also have "... = (\<integral>x. (\<Sum>i\<in>I. indicator A x *\<^sub>R cond_exp M F (f i) x)\<partial>M)" using assms by (auto intro!: Bochner_Integration.integral_sum[symmetric] integrable_mult_indicator)
  also have "... = (\<integral>x\<in>A. (\<Sum>i\<in>I. cond_exp M F (f i) x)\<partial>M)" unfolding set_lebesgue_integral_def by (simp add: scaleR_sum_right)
  finally show "(\<integral>x\<in>A. (\<Sum>i\<in>I. f i x)\<partial>M) = (\<integral>x\<in>A. (\<Sum>i\<in>I. cond_exp M F (f i) x)\<partial>M)" by auto
qed (auto simp add: assms integrable_cond_exp)

subsection \<open>Linearly Ordered Banach Spaces\<close>

text \<open>In this subsection we show monotonicity results concerning the conditional expectation operator.\<close>

lemma cond_exp_gr_c:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f"  "AE x in M. f x > c"
  shows "AE x in M. cond_exp M F f x > c"
proof -
  define X where "X = {x \<in> space M. cond_exp M F f x \<le> c}"
  have [measurable]: "X \<in> sets F" unfolding X_def by measurable (metis sets.top subalg subalgebra_def)
  hence X_in_M: "X \<in> sets M" using sets_restr_to_subalg subalg subalgebra_def by blast
  have "emeasure M X = 0"
  proof (rule ccontr)
    assume "emeasure M X \<noteq> 0"
    have "emeasure (restr_to_subalg M F) X = emeasure M X" by (simp add: emeasure_restr_to_subalg subalg)
    hence "emeasure (restr_to_subalg M F) X > 0" using \<open>\<not>(emeasure M X) = 0\<close> gr_zeroI by auto
    then obtain A where A: "A \<in> sets (restr_to_subalg M F)" "A \<subseteq> X" "emeasure (restr_to_subalg M F) A > 0" "emeasure (restr_to_subalg M F) A < \<infinity>"
      using sigma_fin_subalg by (metis emeasure_notin_sets ennreal_0 infinity_ennreal_def le_less_linear neq_top_trans not_gr_zero order_refl sigma_finite_measure.approx_PInf_emeasure_with_finite)
    hence [simp]: "A \<in> sets F" using subalg sets_restr_to_subalg by blast
    hence A_in_sets_M[simp]: "A \<in> sets M" using sets_restr_to_subalg subalg subalgebra_def by blast
    have [simp]: "set_integrable M A (\<lambda>x. c)" using A subalg by (auto simp add: set_integrable_def emeasure_restr_to_subalg) 
    have [simp]: "set_integrable M A f" unfolding set_integrable_def by (rule integrable_mult_indicator, auto simp add: assms(1))
    have "AE x in M. indicator A x *\<^sub>R c = indicator A x *\<^sub>R f x"
    proof (rule integral_eq_mono_AE_eq_AE)
      have "(\<integral>x\<in>A. c \<partial>M) \<le> (\<integral>x\<in>A. f x \<partial>M)" using assms(2) by (intro set_integral_mono_AE_banach) auto
      moreover
      {
        have "(\<integral>x\<in>A. f x \<partial>M) = (\<integral>x\<in>A. cond_exp M F f x \<partial>M)" by (rule cond_exp_set_integral, auto simp add: assms)
        also have "... \<le> (\<integral>x\<in>A. c \<partial>M)" using A by (auto intro!: set_integral_mono_banach simp add: X_def)
        finally have "(\<integral>x\<in>A. f x \<partial>M) \<le> (\<integral>x\<in>A. c \<partial>M)" by simp
      }
      ultimately show "LINT x|M. indicator A x *\<^sub>R c = LINT x|M. indicator A x *\<^sub>R f x" unfolding set_lebesgue_integral_def by simp
      show "AE x in M. indicator A x *\<^sub>R c \<le> indicator A x *\<^sub>R f x" using assms by (auto simp add: X_def indicator_def)
    qed (auto simp add: set_integrable_def[symmetric])
    hence "AE x\<in>A in M. c = f x" by auto
    hence "AE x\<in>A in M. False" using assms(2) by auto
    hence "A \<in> null_sets M" using AE_iff_null_sets A_in_sets_M by metis
    thus False using A(3) by (simp add: emeasure_restr_to_subalg null_setsD1 subalg)
  qed
  thus ?thesis using AE_iff_null_sets[OF X_in_M] unfolding X_def by auto
qed

corollary cond_exp_less_c:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f" "AE x in M. f x < c"
  shows "AE x in M. cond_exp M F f x < c"
proof -
  have "AE x in M. cond_exp M F f x = - cond_exp M F (\<lambda>x. - f x) x" using cond_exp_uminus[OF assms(1)] by auto
  moreover have "AE x in M. cond_exp M F (\<lambda>x. - f x) x > - c"  using assms by (intro cond_exp_gr_c) auto
  ultimately show ?thesis by (force simp add: minus_less_iff)
qed

lemma cond_exp_mono_strict:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f" "integrable M g" "AE x in M. f x < g x"
  shows "AE x in M. cond_exp M F f x < cond_exp M F g x"
  using cond_exp_less_c[OF Bochner_Integration.integrable_diff, OF assms(1,2), of 0] 
        cond_exp_diff[OF assms(1,2)] assms(3) by auto

lemma cond_exp_ge_c:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes [measurable]: "integrable M f"                                                               
      and "AE x in M. f x \<ge> c"
  shows "AE x in M. cond_exp M F f x \<ge> c"
proof -
  let ?F = "restr_to_subalg M F"
  interpret sigma_finite_measure "restr_to_subalg M F" using sigma_fin_subalg by auto
  { 
    fix A assume asm: "A \<in> sets ?F" "0 < measure ?F A"
    have [simp]: "sets ?F = sets F" "measure ?F A = measure M A" using asm by (auto simp add: measure_def sets_restr_to_subalg[OF subalg] emeasure_restr_to_subalg[OF subalg])
    have M_A: "emeasure M A < \<infinity>" using measure_zero_top asm by (force simp add: top.not_eq_extremum)
    hence F_A: "emeasure ?F A < \<infinity>" using asm(1) emeasure_restr_to_subalg subalg by fastforce
    have "set_lebesgue_integral M A (\<lambda>_. c) \<le> set_lebesgue_integral M A f" using assms asm M_A subalg by (intro set_integral_mono_AE_banach, auto simp add: set_integrable_def integrable_mult_indicator subalgebra_def sets_restr_to_subalg)
    also have "... = set_lebesgue_integral M A (cond_exp M F f)" using cond_exp_set_integral[OF assms(1)] asm by auto
    also have "... = set_lebesgue_integral ?F A (cond_exp M F f)" unfolding set_lebesgue_integral_def using asm borel_measurable_cond_exp by (intro integral_subalgebra2[OF subalg, symmetric], simp)
    finally have "(1 / measure ?F A) *\<^sub>R set_lebesgue_integral ?F A (cond_exp M F f) \<in> {c..}" using asm subalg M_A by (auto simp add: set_integral_const subalgebra_def intro!: pos_divideR_le_eq[THEN iffD1]) 
  }
  thus ?thesis using AE_restr_to_subalg[OF subalg] averaging_theorem[OF integrable_in_subalg closed_atLeast, OF subalg borel_measurable_cond_exp integrable_cond_exp] by auto
qed

corollary cond_exp_le_c:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f"
      and "AE x in M. f x \<le> c"
  shows "AE x in M. cond_exp M F f x \<le> c"
proof -
  have "AE x in M. cond_exp M F f x = - cond_exp M F (\<lambda>x. - f x) x" using cond_exp_uminus[OF assms(1)] by force
  moreover have "AE x in M. cond_exp M F (\<lambda>x. - f x) x \<ge> - c" using assms by (intro cond_exp_ge_c) auto
  ultimately show ?thesis by (force simp add: minus_le_iff)
qed

corollary cond_exp_mono:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f" "integrable M g" "AE x in M. f x \<le> g x"
  shows "AE x in M. cond_exp M F f x \<le> cond_exp M F g x"
  using cond_exp_le_c[OF Bochner_Integration.integrable_diff, OF assms(1,2), of 0] 
        cond_exp_diff[OF assms(1,2)] assms(3) by auto
                                      
corollary cond_exp_min:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f" "integrable M g"
  shows "AE \<xi> in M. cond_exp M F (\<lambda>x. min (f x) (g x)) \<xi> \<le> min (cond_exp M F f \<xi>) (cond_exp M F g \<xi>)"
proof -
  have "AE \<xi> in M. cond_exp M F (\<lambda>x. min (f x) (g x)) \<xi> \<le> cond_exp M F f \<xi>" by (intro cond_exp_mono integrable_min assms, simp)
  moreover have "AE \<xi> in M. cond_exp M F (\<lambda>x. min (f x) (g x)) \<xi> \<le> cond_exp M F g \<xi>" by (intro cond_exp_mono integrable_min assms, simp)
  ultimately show "AE \<xi> in M. cond_exp M F (\<lambda>x. min (f x) (g x)) \<xi> \<le> min (cond_exp M F f \<xi>) (cond_exp M F g \<xi>)" by fastforce
qed

corollary cond_exp_max:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f" "integrable M g"
  shows "AE \<xi> in M. cond_exp M F (\<lambda>x. max (f x) (g x)) \<xi> \<ge> max (cond_exp M F f \<xi>) (cond_exp M F g \<xi>)"
proof -
  have "AE \<xi> in M. cond_exp M F (\<lambda>x. max (f x) (g x)) \<xi> \<ge> cond_exp M F f \<xi>" by (intro cond_exp_mono integrable_max assms, simp)
  moreover have "AE \<xi> in M. cond_exp M F (\<lambda>x. max (f x) (g x)) \<xi> \<ge> cond_exp M F g \<xi>" by (intro cond_exp_mono integrable_max assms, simp)
  ultimately show "AE \<xi> in M. cond_exp M F (\<lambda>x. max (f x) (g x)) \<xi> \<ge> max (cond_exp M F f \<xi>) (cond_exp M F g \<xi>)" by fastforce
qed

corollary cond_exp_inf:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector, lattice}"
  assumes "integrable M f" "integrable M g"
  shows "AE \<xi> in M. cond_exp M F (\<lambda>x. inf (f x) (g x)) \<xi> \<le> inf (cond_exp M F f \<xi>) (cond_exp M F g \<xi>)"
  unfolding inf_min using assms by (rule cond_exp_min)

corollary cond_exp_sup:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector, lattice}"
  assumes "integrable M f" "integrable M g"
  shows "AE \<xi> in M. cond_exp M F (\<lambda>x. sup (f x) (g x)) \<xi> \<ge> sup (cond_exp M F f \<xi>) (cond_exp M F g \<xi>)"
  unfolding sup_max using assms by (rule cond_exp_max)

end

subsection \<open>Probability Spaces\<close>

lemma (in prob_space) sigma_finite_subalgebra_restr_to_subalg:
  assumes "subalgebra M F"
  shows "sigma_finite_subalgebra M F"
proof (intro sigma_finite_subalgebra.intro)
  interpret F: prob_space "restr_to_subalg M F" using assms prob_space_restr_to_subalg prob_space_axioms by blast
  show "sigma_finite_measure (restr_to_subalg M F)" by (rule F.sigma_finite_measure_axioms)
qed (rule assms)

lemma (in prob_space) cond_exp_trivial:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes "integrable M f"
  shows "AE x in M. cond_exp M (sigma (space M) {}) f x = expectation f"
proof -
  interpret sigma_finite_subalgebra M "sigma (space M) {}" by (auto intro: sigma_finite_subalgebra_restr_to_subalg simp add: subalgebra_def sigma_sets_empty_eq)
  show ?thesis using assms by (intro cond_exp_charact) (auto simp add: sigma_sets_empty_eq set_lebesgue_integral_def prob_space cong: Bochner_Integration.integral_cong)
qed

text \<open>The following lemma shows that independent \<open>\<sigma>\<close>-algebras don't matter for the conditional expectation. The proof is adapted from \cite{Zitkovic_2015}.\<close>

lemma (in prob_space) cond_exp_indep_subalgebra:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, real_normed_field}"
  assumes subalgebra: "subalgebra M F" "subalgebra M G"
      and independent: "indep_set G (sigma (space M) (F \<union> vimage_algebra (space M) f borel))"
  assumes [measurable]: "integrable M f"
  shows "AE x in M. cond_exp M (sigma (space M) (F \<union> G)) f x = cond_exp M F f x"
proof -
  interpret Un_sigma: sigma_finite_subalgebra M "sigma (space M) (F \<union> G)" using assms(1,2) by (auto intro!: sigma_finite_subalgebra_restr_to_subalg sets.sigma_sets_subset simp add: subalgebra_def space_measure_of_conv sets_measure_of_conv)
  interpret sigma_finite_subalgebra M F using assms by (auto intro: sigma_finite_subalgebra_restr_to_subalg)
  {
    fix A
    assume asm: "A \<in> sigma (space M) {a \<inter> b | a b. a \<in> F \<and> b \<in> G}"
    have in_events: "sigma_sets (space M) {a \<inter> b |a b. a \<in> sets F \<and> b \<in> sets G} \<subseteq> events" using subalgebra by (intro sets.sigma_sets_subset, auto simp add: subalgebra_def)
    have "Int_stable {a \<inter> b | a b. a \<in> F \<and> b \<in> G}"
    proof -
      {
        fix af bf ag bg
        assume F: "af \<in> F" "bf \<in> F" and G: "ag \<in> G" "bg \<in> G"
        have "af \<inter> bf \<in> F" by (intro sets.Int F)
        moreover have "ag \<inter> bg \<in> G" by (intro sets.Int G)
        ultimately have "\<exists>a b. af \<inter> ag \<inter> (bf \<inter> bg) = a \<inter> b \<and> a \<in> sets F \<and> b \<in> sets G" by (metis inf_assoc inf_left_commute)
      }
      thus ?thesis by (force intro!: Int_stableI)
    qed
    moreover have "{a \<inter> b | a b. a \<in> F \<and> b \<in> G} \<subseteq> Pow (space M)" using subalgebra by (force simp add: subalgebra_def dest: sets.sets_into_space)
    moreover have "A \<in> sigma_sets (space M) {a \<inter> b | a b. a \<in> F \<and> b \<in> G}" using calculation asm by force
    ultimately have "set_lebesgue_integral M A f = set_lebesgue_integral M A (cond_exp M F f)"
    proof (induction rule: sigma_sets_induct_disjoint)
      case (basic A)
      then obtain a b where A: "A = a \<inter> b" "a \<in> F" "b \<in> G" by blast

      hence events[measurable]: "a \<in> events" "b \<in> events" using subalgebra by (auto simp add: subalgebra_def)

      have [simp]: "sigma_sets (space M) {indicator b -` A \<inter> space M |A. A \<in> borel} \<subseteq> G"
        using borel_measurable_indicator[OF A(3), THEN measurable_sets] sets.top subalgebra
        by (intro sets.sigma_sets_subset') (fastforce simp add: subalgebra_def)+

      have Un_in_sigma: "F \<union> vimage_algebra (space M) f borel \<subseteq> sigma (space M) (F \<union> vimage_algebra (space M) f borel)" by (metis equalityE le_supI sets.space_closed sigma_le_sets space_vimage_algebra subalg subalgebra_def)

      have [intro]: "indep_var borel (indicator b) borel (\<lambda>\<omega>. indicator a \<omega> *\<^sub>R f \<omega>)"
      proof -
        have [simp]: "sigma_sets (space M) {(\<lambda>\<omega>. indicator a \<omega> *\<^sub>R f \<omega>) -` A \<inter> space M |A. A \<in> borel} \<subseteq> sigma (space M) (F \<union> vimage_algebra (space M) f borel)"
        proof -
          have *: "(\<lambda>\<omega>. indicator a \<omega> *\<^sub>R f \<omega>) \<in> borel_measurable (sigma (space M) (F \<union> vimage_algebra (space M) f borel))"
            using borel_measurable_indicator[OF A(2), THEN measurable_sets, OF borel_open] subalgebra
            by (intro borel_measurable_scaleR borel_measurableI Un_in_sigma[THEN subsetD])
               (auto simp add: space_measure_of_conv subalgebra_def sets_vimage_algebra2)
          thus ?thesis using measurable_sets[OF *] by (intro sets.sigma_sets_subset', auto simp add: space_measure_of_conv)
        qed
        have "indep_set (sigma_sets (space M) {indicator b -` A \<inter> space M |A. A \<in> borel}) (sigma_sets (space M) {(\<lambda>\<omega>. indicator a \<omega> *\<^sub>R f \<omega>) -` A \<inter> space M |A. A \<in> borel})" 
          using independent unfolding indep_set_def by (rule indep_sets_mono_sets, auto split: bool.split)
        thus ?thesis by (subst indep_var_eq, auto intro!: borel_measurable_scaleR)
      qed

      have [intro]: "indep_var borel (indicator b) borel (\<lambda>\<omega>. indicat_real a \<omega> *\<^sub>R cond_exp M F f \<omega>)"
      proof -
        have [simp]:"sigma_sets (space M) {(\<lambda>\<omega>. indicator a \<omega> *\<^sub>R cond_exp M F f \<omega>) -` A \<inter> space M |A. A \<in> borel} \<subseteq> sigma (space M) (F \<union> vimage_algebra (space M) f borel)"
        proof -
          have *: "(\<lambda>\<omega>. indicator a \<omega> *\<^sub>R cond_exp M F f \<omega>) \<in> borel_measurable (sigma (space M) (F \<union> vimage_algebra (space M) f borel))"
            using borel_measurable_indicator[OF A(2), THEN measurable_sets, OF borel_open] subalgebra 
                  borel_measurable_cond_exp[THEN measurable_sets, OF borel_open, of _ M F f]
            by (intro borel_measurable_scaleR borel_measurableI Un_in_sigma[THEN subsetD])
               (auto simp add: space_measure_of_conv subalgebra_def)
          thus ?thesis using measurable_sets[OF *] by (intro sets.sigma_sets_subset', auto simp add: space_measure_of_conv)
        qed
        have "indep_set (sigma_sets (space M) {indicator b -` A \<inter> space M |A. A \<in> borel}) (sigma_sets (space M) {(\<lambda>\<omega>. indicator a \<omega> *\<^sub>R cond_exp M F f \<omega>) -` A \<inter> space M |A. A \<in> borel})" 
          using independent unfolding indep_set_def by (rule indep_sets_mono_sets, auto split: bool.split)
        thus ?thesis by (subst indep_var_eq, auto intro!: borel_measurable_scaleR)
      qed
  
      have "set_lebesgue_integral M A f = (LINT x|M. indicator b x * (indicator a x *\<^sub>R f x))"
        unfolding set_lebesgue_integral_def A indicator_inter_arith 
        by (intro Bochner_Integration.integral_cong, auto simp add: scaleR_scaleR[symmetric] indicator_times_eq_if(1))
      also have "... = (LINT x|M. indicator b x) * (LINT x|M. indicator a x *\<^sub>R f x)" 
        by (intro indep_var_lebesgue_integral
                  Bochner_Integration.integrable_bound[OF integrable_const[of "1 :: 'b"] borel_measurable_indicator]
                  integrable_mult_indicator[OF _ assms(4)], blast) (auto simp add: indicator_def)
        also have "... = (LINT x|M. indicator b x) * (LINT x|M. indicator a x *\<^sub>R cond_exp M F f x)" 
          using cond_exp_set_integral[OF assms(4) A(2)] unfolding set_lebesgue_integral_def by argo
        also have "... = (LINT x|M. indicator b x * (indicator a x *\<^sub>R cond_exp M F f x))"
        by (intro indep_var_lebesgue_integral[symmetric]
                  Bochner_Integration.integrable_bound[OF integrable_const[of "1 :: 'b"] borel_measurable_indicator]
                  integrable_mult_indicator[OF _ integrable_cond_exp], blast) (auto simp add: indicator_def)
      also have "... = set_lebesgue_integral M A (cond_exp M F f)" 
        unfolding set_lebesgue_integral_def A indicator_inter_arith 
        by (intro Bochner_Integration.integral_cong, auto simp add: scaleR_scaleR[symmetric] indicator_times_eq_if(1))
      finally show ?case .
    next
      case empty
      then show ?case unfolding set_lebesgue_integral_def by simp
    next
      case (compl A)
      have A_in_space: "A \<subseteq> space M" using compl using in_events sets.sets_into_space by blast
      have "set_lebesgue_integral M (space M - A) f = set_lebesgue_integral M (space M - A \<union> A) f - set_lebesgue_integral M A f"
        using compl(1) in_events
        by (subst set_integral_Un[of "space M - A" A], blast)
           (simp | intro integrable_mult_indicator[folded set_integrable_def, OF _ assms(4)], fast)+
      also have "... = set_lebesgue_integral M (space M - A \<union> A) (cond_exp M F f) - set_lebesgue_integral M A (cond_exp M F f)" 
        using cond_exp_set_integral[OF assms(4) sets.top] compl subalgebra by (simp add: subalgebra_def Un_absorb2[OF A_in_space])
      also have "... = set_lebesgue_integral M (space M - A) (cond_exp M F f)"
        using compl(1) in_events
        by (subst set_integral_Un[of "space M - A" A], blast)
           (simp | intro integrable_mult_indicator[folded set_integrable_def, OF _ integrable_cond_exp], fast)+
      finally show ?case .
    next
      case (union A)
      have "set_lebesgue_integral M (\<Union> (range A)) f = (\<Sum>i. set_lebesgue_integral M (A i) f)" 
        using union in_events
        by (intro lebesgue_integral_countable_add) (auto simp add: disjoint_family_onD intro!: integrable_mult_indicator[folded set_integrable_def, OF _ assms(4)]) 
      also have "... = (\<Sum>i. set_lebesgue_integral M (A i) (cond_exp M F f))" using union by presburger
      also have "... = set_lebesgue_integral M (\<Union> (range A)) (cond_exp M F f)"
        using union in_events
        by (intro lebesgue_integral_countable_add[symmetric]) (auto simp add: disjoint_family_onD intro!: integrable_mult_indicator[folded set_integrable_def, OF _ integrable_cond_exp]) 
      finally show ?case .
    qed
  }
  moreover have "sigma (space M) {a \<inter> b | a b. a \<in> F \<and> b \<in> G} = sigma (space M) (F \<union> G)"
  proof -
    have "sigma_sets (space M) {a \<inter> b |a b. a \<in> sets F \<and> b \<in> sets G} = sigma_sets (space M) (sets F \<union> sets G)"
    proof -
      {
        fix a b assume asm: "a \<in> F" "b \<in> G"
        hence "a \<inter> b \<in> sigma_sets (space M) (F \<union> G)" using subalgebra unfolding Int_range_binary by (intro sigma_sets_Inter[OF _ binary_in_sigma_sets]) (force simp add: subalgebra_def dest: sets.sets_into_space)+
      }
      moreover
      {
        fix a
        assume "a \<in> sets F"
        hence "a \<in> sigma_sets (space M) {a \<inter> b |a b. a \<in> sets F \<and> b \<in> sets G}"
          using subalgebra sets.top[of G] sets.sets_into_space[of _ F] 
          by (intro sigma_sets.Basic, auto simp add: subalgebra_def)
      }
      moreover
      {
        fix a assume "a \<in> sets F \<or> a \<in> sets G" "a \<notin> sets F"
        hence "a \<in> sets G" by blast
        hence "a \<in> sigma_sets (space M) {a \<inter> b |a b. a \<in> sets F \<and> b \<in> sets G}" 
          using subalgebra sets.top[of F] sets.sets_into_space[of _ G] 
          by (intro sigma_sets.Basic, auto simp add: subalgebra_def)
      }
      ultimately show ?thesis by (intro sigma_sets_eqI) auto
    qed
    thus ?thesis using subalgebra by (intro sigma_eqI) (force simp add: subalgebra_def dest: sets.sets_into_space)+
  qed
  moreover have "(cond_exp M F f) \<in> borel_measurable (sigma (space M) (sets F \<union> sets G))"
  proof -
    have "F \<subseteq> sigma (space M) (F \<union> G)" by (metis Un_least Un_upper1 measure_of_of_measure sets.space_closed sets_measure_of sigma_sets_subseteq subalg subalgebra(2) subalgebra_def)
    thus ?thesis using borel_measurable_cond_exp[THEN measurable_sets, OF borel_open, of _ M F f] subalgebra by (intro borel_measurableI, force simp only: space_measure_of_conv subalgebra_def)
  qed
  ultimately show ?thesis using assms(4) integrable_cond_exp by (intro Un_sigma.cond_exp_charact) presburger+
qed

text \<open>If a random variable is independent of a \<open>\<sigma>\<close>-algebra \<^term>\<open>F\<close>, its conditional expectation \<^term>\<open>cond_exp M F f\<close> is just its expectation.\<close>

lemma (in prob_space) cond_exp_indep:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, real_normed_field}"
  assumes subalgebra: "subalgebra M F"
      and independent: "indep_set F (vimage_algebra (space M) f borel)"
      and integrable: "integrable M f"
  shows "AE x in M. cond_exp M F f x = expectation f"
proof -
  have "indep_set F (sigma (space M) (sigma (space M) {} \<union> (vimage_algebra (space M) f borel)))"
    using independent unfolding indep_set_def 
    by (rule indep_sets_mono_sets, simp add: bool.split) 
       (metis bot.extremum dual_order.refl sets.sets_measure_of_eq sets.sigma_sets_subset' sets_vimage_algebra_space space_vimage_algebra sup.absorb_iff2)
  hence cond_exp_indep: "AE x in M. cond_exp M (sigma (space M) (sigma (space M) {} \<union> F)) f x = expectation f"
    using cond_exp_indep_subalgebra[OF _ subalgebra _ integrable, of "sigma (space M) {}"] cond_exp_trivial[OF integrable]
    by (auto simp add: subalgebra_def sigma_sets_empty_eq)
  have "sets (sigma (space M) (sigma (space M) {} \<union> F)) = F"
    using subalgebra sets.top[of F] unfolding subalgebra_def 
    by (simp add: sigma_sets_empty_eq, subst insert_absorb[of "space M" F], blast) 
       (metis insert_absorb[OF sets.empty_sets] sets.sets_measure_of_eq)
  hence "AE x in M. cond_exp M (sigma (space M) (sigma (space M) {} \<union> F)) f x = cond_exp M F f x" by (rule cond_exp_sets_cong)
  thus ?thesis using cond_exp_indep by force
qed

end