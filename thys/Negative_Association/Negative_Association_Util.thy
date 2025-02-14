section \<open>Preliminary Definitions and Lemmas\<close>

theory Negative_Association_Util
  imports
    Concentration_Inequalities.Concentration_Inequalities_Preliminary
    Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
begin

(* From Joe Watt *)
abbreviation (input) flip :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c\<close> where
  \<open>flip f x y \<equiv> f y x\<close>

text \<open>Additional introduction rules for boundedness:\<close>

(*
  Note to editors: I will move these to (in afp-devel)
  Concentration_Inequalities.Concentration_Inequalities_Preliminary
*)

lemma bounded_const_min:
  fixes f :: "'a \<Rightarrow> real"
  assumes "bdd_below (f ` M)"
  shows "bounded ((\<lambda>x. min c (f x)) ` M)"
proof -
  obtain h where "\<And>x. x \<in> M \<Longrightarrow> f x \<ge> h" using assms(1) unfolding bdd_below_def by auto
  thus ?thesis by (intro boundedI[where B="max \<bar>c\<bar> \<bar>-h\<bar>"]) force
qed

lemma bounded_prod:
  fixes f :: "'i \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> bounded (f i ` T)"
  shows "bounded ((\<lambda>x. (\<Prod> i \<in> I. f i x)) ` T)"
  using assms by (induction I) (auto intro:bounded_mult_comp bounded_const)

lemma bounded_vec_mult_comp:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "bounded (f ` T)" "bounded (g ` T)"
  shows "bounded ((\<lambda>x. (f x) *\<^sub>R (g x)) ` T)"
  using bounded_mult_comp[OF assms] by simp

lemma bounded_max:
  fixes f :: "'a \<Rightarrow> real"
  assumes "bounded ((\<lambda>x. f x) ` T)"
  shows "bounded ((\<lambda>x. max c (f x)) ` T)"
proof -
  obtain m where "norm (f x) \<le> m" if "x \<in> T" for x
    using assms unfolding bounded_iff by auto

  thus ?thesis by (intro boundedI[where B="max m c"]) fastforce
qed

lemma bounded_of_bool: "bounded (range of_bool)" by auto

lemma bounded_range_imp:
  assumes "bounded (range f)"
  shows "bounded ((\<lambda>\<omega>. f (h \<omega>)) ` S)"
  by (intro bounded_subset[OF assms]) auto

text \<open>The following allows to state integrability and conditions about the integral simultaneously,
e.g. @{term "has_int_that M f (\<lambda>x. x \<le> c)"} says f is integrable on M and the integral smaller or
equal to @{term "c"}.\<close>

definition has_int_that where
  "has_int_that M f P = (integrable M f \<and> (P (\<integral>\<omega>. f \<omega> \<partial>M)))"

lemma true_eq_iff: "P \<Longrightarrow> True = P" by auto
lemma le_trans: "y \<le> z \<Longrightarrow> x \<le> y \<longrightarrow> x \<le> (z :: 'a :: order)" by auto

lemma has_int_that_mono:
  assumes "\<And>x. P x \<longrightarrow> Q x"
  shows "has_int_that M f P \<le> has_int_that M f Q"
  using assms unfolding has_int_that_def by auto

lemma has_int_thatD:
  assumes "has_int_that M f P"
  shows "integrable M f" "P (integral\<^sup>L M f)"
  using assms has_int_that_def by auto

text \<open>This is useful to specify which components a functional depends on.\<close>

definition depends_on :: "(('a \<Rightarrow> 'b) \<Rightarrow> 'c) \<Rightarrow> 'a set \<Rightarrow> bool"
  where "depends_on f I = (\<forall>x y. restrict x I = restrict y I \<longrightarrow> f x = f y)"

lemma depends_onI:
  assumes "\<And>x.  f x = f (\<lambda>i. if i \<in> I then (x i) else undefined)"
  shows "depends_on f I"
proof -
  have "f x = f y" if "restrict x I = restrict y I" for x y
  proof -
    have "f x = f (restrict x I)" using assms unfolding restrict_def by simp
    also have "... = f (restrict y I)" using that by simp
    also have "... = f y" using assms unfolding restrict_def by simp
    finally show ?thesis by simp
  qed
  thus ?thesis unfolding depends_on_def by blast
qed

lemma depends_on_comp:
  assumes "depends_on f I"
  shows "depends_on (g \<circ> f) I"
  using assms unfolding depends_on_def by (metis o_apply)

lemma depends_on_comp_2:
  assumes "depends_on f I"
  shows "depends_on (\<lambda>x. g (f x)) I"
  using assms unfolding depends_on_def by metis

lemma depends_onD:
  assumes "depends_on f I"
  shows "f \<omega> = f (\<lambda>i\<in>I. (\<omega> i))"
  using assms unfolding depends_on_def by (metis extensional_restrict restrict_extensional)

lemma depends_onD2:
  assumes "depends_on f I" "restrict x I = restrict y I"
  shows "f x = f y"
  using assms unfolding depends_on_def by metis

lemma depends_on_empty:
  assumes "depends_on f {}"
  shows "f \<omega> = f undefined"
  by (intro depends_onD2[OF assms]) auto

lemma depends_on_mono:
  assumes "I \<subseteq> J" "depends_on f I"
  shows "depends_on f J"
  using assms unfolding depends_on_def by (metis restrict_restrict Int_absorb1)

abbreviation "square_integrable M f \<equiv> integrable M ((power2 :: real \<Rightarrow> real) \<circ> f)"

text \<open>There are many results in the field of negative association, where a statement is true
for simultaneously monotone or anti-monotone functions. With the below construction, we introduce
a mechanism where we can parameterize on the direction of a relation:\<close>

datatype RelDirection = Fwd | Rev

definition dir_le :: "RelDirection \<Rightarrow> (('d::order) \<Rightarrow> ('d :: order) \<Rightarrow> bool)"  (infixl "\<le>\<ge>\<index>" 60)
  where "dir_le \<eta> = (if \<eta> = Fwd then (\<le>) else (\<ge>))"

lemma dir_le[simp]:
  "(\<le>\<ge>\<^bsub>Fwd\<^esub>) = (\<le>)"
  "(\<le>\<ge>\<^bsub>Rev\<^esub>) = (\<ge>)"
  by (auto simp:dir_le_def)

definition dir_sign :: "RelDirection \<Rightarrow> 'a::{one,uminus}" ("\<plusminus>\<index>")
  where "dir_sign \<eta> = (if \<eta> = Fwd then 1 else (-1))"

lemma dir_le_refl: "x \<le>\<ge>\<^bsub>\<eta>\<^esub> x"
  by (cases \<eta>) auto

lemma dir_sign[simp]:
  "(\<plusminus>\<^bsub>Fwd\<^esub>) = (1)"
  "(\<plusminus>\<^bsub>Rev\<^esub>) = (-1)"
  by (auto simp:dir_sign_def)

lemma conv_rel_to_sign:
  fixes f :: "'a::order \<Rightarrow> real"
  shows "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) f = mono ((*)(\<plusminus>\<^bsub>\<eta>\<^esub>) \<circ> f)"
  by (cases "\<eta>") (simp_all add:monotone_def)

instantiation RelDirection :: times
begin
definition times_RelDirection :: "RelDirection \<Rightarrow> RelDirection \<Rightarrow> RelDirection" where
  times_RelDirection_def: "times_RelDirection x y = (if x = y then Fwd else Rev)"

instance by standard
end

lemmas rel_dir_mult[simp] = times_RelDirection_def

lemma dir_mult_hom: "(\<plusminus>\<^bsub>\<sigma> * \<tau>\<^esub>) = (\<plusminus>\<^bsub>\<sigma>\<^esub>) * ((\<plusminus>\<^bsub>\<tau>\<^esub>)::real)"
  unfolding dir_sign_def times_RelDirection_def by (cases \<sigma>,auto intro:RelDirection.exhaust)

text \<open>Additional lemmas about clamp for the specific case on reals.\<close>

lemma clamp_eqI2:
  assumes "x \<in> {a..b::real}"
  shows "x = clamp a b x"
  using assms unfolding clamp_def by simp

lemma clamp_eqI:
  assumes "\<bar>x\<bar> \<le> (a::real)"
  shows "x = clamp (-a) a x"
  using assms by (intro clamp_eqI2) auto

lemma clamp_real_def:
  fixes x :: real
  shows "clamp a b x = max a (min x b)"
proof -
  consider (i) "x < a" | (ii) "x \<ge> a" "x \<le> b" | (iii) "x > b" by linarith
  thus ?thesis unfolding clamp_def by (cases) auto
qed

lemma clamp_range:
  assumes "a \<le> b"
  shows "\<And>x. clamp a b x \<ge> a" "\<And>x. clamp a b x \<le> b" "range (clamp a b) \<subseteq> {a..b::real}"
  using assms by (auto simp: clamp_real_def)

lemma clamp_abs_le:
  assumes "a \<ge> (0::real)"
  shows "\<bar>clamp (-a) a x\<bar> \<le> \<bar>x\<bar>"
  using assms unfolding clamp_real_def by simp

lemma bounded_clamp:
  fixes a b :: real
  shows "bounded ((clamp a b \<circ> f) ` S)"
proof (cases "a \<le> b")
  case True
  show ?thesis using clamp_range[OF True] bounded_closed_interval bounded_subset
    by (metis image_comp image_mono subset_UNIV)
next
  case False
  hence "clamp a b (f x) = a" for x unfolding clamp_def by (simp add: max_def)
  hence "(clamp a b \<circ> f) ` S \<subseteq> {a..a}" by auto
  thus ?thesis using bounded_subset bounded_closed_interval by metis
qed

lemma bounded_clamp_alt:
  fixes a b :: real
  shows "bounded ((\<lambda>x. clamp a b (f x)) ` S)"
  using bounded_clamp by (auto simp:comp_def)

lemma clamp_borel[measurable]:
  fixes a b :: "'a::{euclidean_space,second_countable_topology}"
  shows "clamp a b \<in> borel_measurable borel"
  unfolding clamp_def by measurable

lemma monotone_clamp:
  assumes "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) f"
  shows "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) (\<lambda>\<omega>. clamp a (b::real) (f \<omega>))"
  using assms unfolding monotone_def clamp_real_def by (cases \<eta>) force+

text \<open>This part introduces the term @{term "KL_div"} as the Kullback-Leibler divergence between a
pair of Bernoulli random variables. The expression is useful to express some of the Chernoff bounds
more concisely~\cite[Th.~1]{impagliazzo2010}.\<close>

lemma radon_nikodym_pmf:
  assumes "set_pmf p \<subseteq> set_pmf q"
  defines "f \<equiv> (\<lambda>x. ennreal (pmf p x / pmf q x))"
  shows
    "AE x in measure_pmf q. RN_deriv q p x = f x" (is "?R1")
    "AE x in measure_pmf p. RN_deriv q p x = f x" (is "?R2")
proof -
  have "pmf p x = 0" if "pmf q x = 0" for x
    using assms(1) that by (meson pmf_eq_0_set_pmf subset_iff)
  hence a:"(pmf q x * (pmf p x / pmf q x)) = pmf p x" for x by simp
  have "emeasure (density q f) A = emeasure p A" (is "?L = ?R") for A
  proof -
    have "?L = set_nn_integral (measure_pmf q) A f"
      by (subst emeasure_density) auto
    also have "\<dots> =  (\<integral>\<^sup>+ x\<in>A. ennreal (pmf q x) * f x \<partial>count_space UNIV)"
      by (simp add: ac_simps nn_integral_measure_pmf)
    also have "\<dots> = (\<integral>\<^sup>+x\<in>A. ennreal (pmf p x) \<partial>count_space UNIV)"
      using a unfolding f_def by (subst ennreal_mult'[symmetric]) simp_all
    also have "\<dots> = emeasure (bind_pmf p return_pmf) A"
      unfolding emeasure_bind_pmf nn_integral_measure_pmf by simp
    also have "\<dots> = ?R" by simp
    finally show ?thesis by simp
  qed
  hence "density (measure_pmf q) f = measure_pmf p" by (intro measure_eqI) auto
  hence "AE x in measure_pmf q. f x = RN_deriv q p x" by (intro measure_pmf.RN_deriv_unique) simp
  thus ?R1 unfolding AE_measure_pmf_iff by auto
  thus ?R2 using assms unfolding AE_measure_pmf_iff by auto
qed

lemma KL_divergence_pmf:
  assumes "set_pmf q \<subseteq> set_pmf p"
  shows "KL_divergence b (measure_pmf p) (measure_pmf q) = (\<integral>x. log b (pmf q x / pmf p x) \<partial>q)"
  unfolding KL_divergence_def entropy_density_def
  by (intro integral_cong_AE AE_mp[OF radon_nikodym_pmf(2)[OF assms(1)] AE_I2]) auto

definition KL_div :: "real \<Rightarrow> real \<Rightarrow> real" where
  "KL_div p q = KL_divergence (exp 1) (bernoulli_pmf q) (bernoulli_pmf p)"

lemma KL_div_eq:
  assumes "q \<in> {0<..<1}" "p \<in> {0..1}"
  shows "KL_div p q = p * ln (p/q) + (1-p) * ln ((1-p)/(1-q))" (is "?L = ?R")
proof -
  have "set_pmf (bernoulli_pmf p) \<subseteq> set_pmf (bernoulli_pmf q)"
    using assms(1) set_pmf_bernoulli by auto
  hence "?L = (\<integral>x. ln (pmf (bernoulli_pmf p) x / pmf (bernoulli_pmf q) x) \<partial>bernoulli_pmf p)"
    unfolding KL_div_def by (subst KL_divergence_pmf) (simp_all add:log_ln[symmetric])
  also have "\<dots> = ?R"
    using assms(1,2) by (subst integral_bernoulli_pmf) auto
  finally show ?thesis by simp
qed

lemma KL_div_swap:
  assumes "q \<in> {0<..<1}" "p \<in> {0..1}"
  shows "KL_div p q = KL_div (1-p) (1-q)"
  using assms by (subst (1 2) KL_div_eq) auto

text \<open>A few results about independent random variables:\<close>

lemma (in prob_space) indep_vars_const:
  assumes "\<And>i. i \<in> I \<Longrightarrow> c i \<in> space (N i)"
  shows "indep_vars N (\<lambda>i _. c i) I"
proof -
  have rv: " random_variable (N i) (\<lambda>_. c i)" if "i \<in> I" for i  using assms[OF that] by simp
  have b:"indep_sets (\<lambda>i. {space M, {}}) I"
  proof (intro indep_setsI, goal_cases)
    case (1 i) thus ?case by simp
  next
    case (2 A J)
    show ?case
    proof (cases "\<forall>j \<in> J. A j = space M")
      case True thus ?thesis using 2(1) by (simp add:prob_space)
    next
      case False
      then obtain i where i:"A i = {}" "i \<in> J" using 2 by auto
      hence "prob (\<Inter> (A ` J)) = prob {}" by (intro arg_cong[where f="prob"]) auto
      also have "\<dots> = 0" by simp
      also have "\<dots> =  (\<Prod>j\<in>J. prob (A j))"
        using i by (intro prod_zero[symmetric] 2 bexI[where x="i"]) auto
      finally show ?thesis by simp
    qed
  qed
  have "{(\<lambda>_. c i) -` A \<inter> space M |A. A \<in> sets (N i)} = {space M, {}}" (is "?L = ?R") if "i \<in> I" for i
  proof
    show "?L \<subseteq> ?R" by auto
  next
    have "(\<lambda>A. (\<lambda>_. c i) -` A \<inter> space M) {} = {}" "{} \<in> N i" by auto
    hence "{} \<in> ?L" unfolding image_Collect[symmetric] by blast
    moreover have "(\<lambda>A. (\<lambda>_. c i) -` A \<inter> space M) (space (N i)) = space M" "space (N i) \<in> N i"
      using assms[OF that] by auto
    hence "space M \<in> ?L" unfolding image_Collect[symmetric] by blast
    ultimately show "?R \<subseteq> ?L" by simp
  qed
  hence "indep_sets (\<lambda>i. {(\<lambda>_. c i) -` A \<inter> space M |A. A \<in> sets (N i)}) I"
    using iffD2[OF indep_sets_cong b] b by simp
  thus ?thesis unfolding indep_vars_def2 by (intro conjI rv ballI)
qed

lemma indep_vars_map_pmf:
  assumes "prob_space.indep_vars (measure_pmf p) (\<lambda>_. discrete) (\<lambda>i. X i \<circ> f) I"
  shows  "prob_space.indep_vars (map_pmf f p) (\<lambda>_. discrete) X I"
  using assms unfolding map_pmf_rep_eq by (intro measure_pmf.indep_vars_distr) auto

lemma indep_var_pair_pmf:
  fixes x y :: "'a pmf"
  shows "prob_space.indep_var (pair_pmf x y) discrete fst discrete snd"
proof -
  have split_bool_univ: "UNIV = insert True {False}" by auto

  have pair_prod: "pair_pmf x y = map_pmf (\<lambda>\<omega>. (\<omega> True, \<omega> False)) (prod_pmf UNIV (case_bool x y))"
    unfolding split_bool_univ by (subst Pi_pmf_insert)
      (simp_all add:map_pmf_comp Pi_pmf_singleton pair_map_pmf2 case_prod_beta)

  have case_bool_eq: "case_bool discrete discrete = (\<lambda>_. discrete)"
    by (intro ext) (simp add: bool.case_eq_if)

  have "prob_space.indep_vars (prod_pmf UNIV (case_bool x y)) (\<lambda>_. discrete) (\<lambda>i \<omega>. \<omega> i) UNIV"
    by (intro indep_vars_Pi_pmf) auto
  moreover have "(\<lambda>i. (case_bool fst snd i) \<circ> (\<lambda>\<omega>. ((\<omega> True)::'a, \<omega> False))) = (\<lambda>i \<omega>. \<omega> i)"
    by (auto intro!:ext split:bool.splits)
  ultimately show ?thesis
    unfolding prob_space.indep_var_def[OF prob_space_measure_pmf] pair_prod case_bool_eq
    by (intro indep_vars_map_pmf) simp
qed

lemma measure_pair_pmf: "measure (pair_pmf p q) (A \<times> B) = measure p A * measure q B" (is "?L = ?R")
proof -
  have "?L = measure (pair_pmf p q) ((A \<inter> set_pmf p) \<times> (B \<inter> set_pmf q))"
    by (intro measure_eq_AE AE_pmfI) auto
  also have "\<dots> = measure p (A \<inter> set_pmf p) * measure q (B \<inter> set_pmf q)"
    by (intro measure_pmf_prob_product) auto
  also have "\<dots> = ?R" by (intro arg_cong2[where f="(*)"] measure_eq_AE AE_pmfI) auto
  finally show ?thesis by simp
qed

instance bool :: second_countable_topology
proof
  show "\<exists>B::bool set set. countable B \<and> open = generate_topology B"
    by (intro exI[of _ "range lessThan \<union> range greaterThan"]) (auto simp: open_bool_def)
qed

end