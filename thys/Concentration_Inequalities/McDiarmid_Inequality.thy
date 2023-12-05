section \<open>McDiarmid's inequality\<close>

text \<open>In this section we verify McDiarmid's inequality \cite[Lemma 1.2]{mcdiarmid1989}. In the
source and also further sources sometimes refer to the result as the ``independent bounded
differences'' inequality.\<close>

theory McDiarmid_Inequality
  imports Concentration_Inequalities_Preliminary
begin

lemma Collect_restr_cong:
  assumes "A = B"
  assumes "\<And>x. x \<in> A \<Longrightarrow> P x = Q x"
  shows "{x \<in> A. P x} = {x \<in> B. Q x}"
  using assms by auto

lemma ineq_chain:
  fixes h :: "nat \<Rightarrow> real"
  assumes "\<And>i. i < n \<Longrightarrow> h (i+1) \<le> h i"
  shows "h n \<le> h 0"
  using assms by (induction n) force+

lemma restrict_subset_eq:
  assumes "A \<subseteq> B"
  assumes "restrict f B = restrict g B"
  shows "restrict f A = restrict g A"
  using assms unfolding restrict_def by (meson subsetD)

text \<open>Bochner Integral version of Hoeffding's Lemma using
  @{thm [source] interval_bounded_random_variable.Hoeffdings_lemma_nn_integral_0}\<close>

lemma (in prob_space) Hoeffdings_lemma_bochner:
  assumes "l > 0" and E0: "expectation f = 0"
  assumes "random_variable borel f"
  assumes "AE x in M. f x \<in> {a..b::real}"
  shows   "expectation (\<lambda>x. exp (l * f x)) \<le> exp (l\<^sup>2 * (b - a)\<^sup>2 / 8)" (is "?L \<le> ?R")
proof -
  interpret interval_bounded_random_variable M f a b
    using assms by (unfold_locales) auto

  have "integrable M (\<lambda>x. exp (l * f x))"
    using assms(1,3,4) by (intro integrable_const_bound[where B="exp (l * b)"]) simp_all

  hence "ennreal (?L) = (\<integral>\<^sup>+ x. exp (l * f x) \<partial>M)"
    by (intro nn_integral_eq_integral[symmetric]) auto
  also have "... \<le> ennreal (?R)"
    by (intro Hoeffdings_lemma_nn_integral_0 assms)
  finally have 0:"ennreal (?L) \<le> ennreal ?R"
    by simp
  show ?thesis
  proof (cases "?L \<ge> 0")
    case True
    thus ?thesis using 0 by simp
  next
    case False
    hence "?L \<le> 0" by simp
    also have "... \<le> ?R" by simp
    finally show ?thesis by simp
  qed
qed

lemma (in prob_space) Hoeffdings_lemma_bochner_2:
  assumes "l > 0" and E0: "expectation f = 0"
  assumes "random_variable borel f"
  assumes "\<And>x y. {x,y} \<subseteq> space M \<Longrightarrow> \<bar>f x - f y\<bar> \<le> (c::real)"
  shows   "expectation (\<lambda>x. exp (l * f x)) \<le> exp (l^2 * c^2 / 8)" (is "?L \<le> ?R")
proof -
  define a :: real where "a = (INF x \<in> space M. f x)"
  define b :: real where "b = a+c"

  obtain \<omega> where \<omega>:"\<omega> \<in> space M" using not_empty by auto
  hence 0:"f ` space M \<noteq> {}" by auto
  have 1: "c = b - a" unfolding b_def by simp

  have "bdd_below (f ` space M)"
    using \<omega> assms(4) unfolding abs_le_iff
    by (intro bdd_belowI[where m="f \<omega> - c"]) (auto simp add:algebra_simps)
  hence "f x \<ge> a" if "x \<in> space M" for x unfolding a_def by (intro cINF_lower that)
  moreover have "f x \<le> b" if x_space: "x \<in> space M" for x
  proof (rule ccontr)
    assume "\<not>(f x \<le> b)"
    hence a:"f x > a + c" unfolding b_def by simp
    have "f y \<ge> f x - c" if "y \<in> space M" for y
      using that x_space assms(4) unfolding abs_le_iff by (simp add:algebra_simps)
    hence "f x - c \<le> a" unfolding a_def using cInf_greatest[OF 0] by auto
    thus "False" using a by simp
  qed
  ultimately have "f x \<in> {a..b}" if "x \<in> space M" for x using that by auto
  hence "AE x in M. f x \<in> {a..b}" by simp
  thus ?thesis unfolding 1 by (intro Hoeffdings_lemma_bochner assms(1,2,3))
qed

lemma (in prob_space) Hoeffdings_lemma_bochner_3:
  assumes "expectation f = 0"
  assumes "random_variable borel f"
  assumes "\<And>x y. {x,y} \<subseteq> space M \<Longrightarrow> \<bar>f x - f y\<bar> \<le> (c::real)"
  shows   "expectation (\<lambda>x. exp (l * f x)) \<le> exp (l^2 * c^2 / 8)" (is "?L \<le> ?R")
proof -
  consider (a) "l > 0" | (b) "l = 0" | (c) "l < 0"
    by argo
  then show ?thesis
  proof (cases)
    case a thus ?thesis by (intro Hoeffdings_lemma_bochner_2 assms) auto
  next
    case b thus ?thesis by simp
  next
    case c
    have "?L = expectation (\<lambda>x. exp ((-l) * (-f x)))" by simp
    also have "... \<le> exp ((-l)^2 * c\<^sup>2/8)" using c assms by (intro Hoeffdings_lemma_bochner_2) auto
    also have "... = ?R" by simp
    finally show ?thesis by simp
  qed
qed

text \<open>Version of @{thm [source] product_sigma_finite.product_integral_singleton} without the
condition that @{term "M i"} has to be sigma finite for all @{term "i"}:\<close>

lemma product_integral_singleton:
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes "sigma_finite_measure (M i)"
  assumes "f \<in> borel_measurable (M i)"
  shows "(\<integral>x. f (x i) \<partial>(PiM {i} M)) = (\<integral>x. f x \<partial>(M i))" (is "?L = ?R")
proof -
  define M' where "M' j = (if j=i then M i else count_space {undefined})" for j

  interpret product_sigma_finite "M'"
    using assms(1) unfolding product_sigma_finite_def M'_def
    by (auto intro!:sigma_finite_measure_count_space_finite)

  have "?L = \<integral>x. f (x i) \<partial>(PiM {i} M')"
    by (intro Bochner_Integration.integral_cong PiM_cong) (simp_all add:M'_def)
  also have "... = (\<integral>x. f x \<partial>(M' i))"
    using assms(2) by (intro product_integral_singleton) (simp add:M'_def)
  also have "... = ?R"
    by (intro Bochner_Integration.integral_cong PiM_cong) (simp_all add:M'_def)
  finally show ?thesis by simp
qed

text \<open>Version of @{thm [source] product_sigma_finite.product_integral_fold} without the
condition that @{term "M i"} has to be sigma finite for all @{term "i"}:\<close>

lemma product_integral_fold:
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes "\<And>i. i \<in> I \<union> J \<Longrightarrow> sigma_finite_measure (M i)"
  assumes "I \<inter> J = {}"
  assumes "finite I"
  assumes "finite J"
  assumes "integrable (PiM (I \<union> J) M) f"
  shows "(\<integral>x. f x \<partial>PiM (I \<union> J) M) = (\<integral>x. (\<integral>y. f (merge I J(x,y)) \<partial>PiM J M) \<partial>PiM I M)" (is "?L = ?R")
    and "integrable (PiM I M) (\<lambda>x. (\<integral>y. f (merge I J(x,y)) \<partial>PiM J M))" (is "?I")
    and "AE x in PiM I M. integrable (PiM J M) (\<lambda>y. f (merge I J(x,y)))" (is "?T")
proof -
  define M' where "M' i = (if i \<in> I \<union> J then M i else count_space {undefined})" for i

  interpret product_sigma_finite "M'"
    using assms(1) unfolding product_sigma_finite_def M'_def
    by (auto intro!:sigma_finite_measure_count_space_finite)

  interpret pair_sigma_finite "Pi\<^sub>M I M'" "Pi\<^sub>M J M'"
    using assms(3,4) sigma_finite unfolding pair_sigma_finite_def by blast

  have 0: "integrable (Pi\<^sub>M (I \<union> J) M') f = integrable (Pi\<^sub>M (I \<union> J) M) f"
    by (intro Bochner_Integration.integrable_cong PiM_cong) (simp_all add:M'_def)

  have "?L = (\<integral>x. f x \<partial>PiM (I \<union> J) M')"
    by (intro Bochner_Integration.integral_cong PiM_cong) (simp_all add:M'_def)
  also have "... = (\<integral>x. (\<integral>y. f (merge I J (x,y)) \<partial>PiM J M') \<partial>PiM I M')"
    using assms(5) by (intro product_integral_fold assms(2,3,4)) (simp add:0)
  also have "... = ?R"
    by (intro Bochner_Integration.integral_cong PiM_cong) (simp_all add:M'_def)
  finally show "?L = ?R" by simp

  have "integrable (Pi\<^sub>M (I \<union> J) M') f = integrable (PiM I M' \<Otimes>\<^sub>M PiM J M') (\<lambda>x. f (merge I J x))"
    using assms(5) apply (subst distr_merge[OF assms(2,3,4),symmetric])
    by (intro integrable_distr_eq) (simp_all add:0[symmetric])
  hence 1:"integrable (PiM I M' \<Otimes>\<^sub>M PiM J M') (\<lambda>x. f (merge I J x))"
    using assms(5) 0 by simp

  hence "integrable (PiM I M') (\<lambda>x. (\<integral>y. f (merge I J(x,y)) \<partial>PiM J M'))" (is "?I'")
    by (intro integrable_fst') auto
  moreover have "?I' = ?I"
    by (intro Bochner_Integration.integrable_cong PiM_cong ext Bochner_Integration.integral_cong)
     (simp_all add:M'_def)
  ultimately show "?I"
    by simp

  have "AE x in Pi\<^sub>M I M'. integrable (Pi\<^sub>M J M') (\<lambda>y. f (merge I J (x, y)))" (is "?T'")
    by (intro AE_integrable_fst'[OF 1])
  moreover have "?T' = ?T"
    by (intro arg_cong2[where f="almost_everywhere"] PiM_cong ext Bochner_Integration.integrable_cong)
     (simp_all add:M'_def)
  ultimately show  "?T"
    by simp
qed

lemma product_integral_insert:
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes "\<And>k. k \<in> {i} \<union> J \<Longrightarrow> sigma_finite_measure (M k)"
  assumes "i \<notin> J"
  assumes "finite J"
  assumes "integrable (PiM (insert i J) M) f"
  shows "(\<integral>x. f x \<partial>PiM (insert i J) M) = (\<integral>x. (\<integral>y. f (y(i := x)) \<partial>PiM J M) \<partial>M i)" (is "?L = ?R")
proof -
  note meas_cong = iffD1[OF measurable_cong]

  have "integrable (PiM {i} M) (\<lambda>x. (\<integral>y. f (merge {i} J (x,y)) \<partial>PiM J M))"
    using assms by (intro product_integral_fold) auto
  hence 0:"(\<lambda>x. (\<integral>y. f (merge {i} J (x,y)) \<partial>PiM J M)) \<in> borel_measurable (PiM {i} M)"
    using borel_measurable_integrable by simp
  have 1:"(\<lambda>x. (\<integral>y. f (y(i := (x i))) \<partial>PiM J M)) \<in> borel_measurable (PiM {i} M)"
    by (intro meas_cong[OF _ 0] Bochner_Integration.integral_cong arg_cong[where f="f"])
     (auto simp add:space_PiM merge_def fun_upd_def PiE_def extensional_def)
  have "(\<lambda>x. (\<integral>y. f (y(i := (\<lambda>i\<in>{i}. x) i)) \<partial>PiM J M)) \<in> borel_measurable (M i)"
    by (intro measurable_compose[OF _ 1, where f="(\<lambda>x. (\<lambda>i\<in>{i}. x))"] measurable_restrict) auto
  hence 2:"(\<lambda>x. (\<integral>y. f (y(i := x )) \<partial>PiM J M)) \<in> borel_measurable (M i)" by simp

  have "?L = (\<integral>x. f x \<partial>PiM ({i} \<union> J) M)" by simp
  also have "... = (\<integral>x. (\<integral>y. f (merge {i} J (x,y)) \<partial>PiM J M) \<partial>PiM {i} M)"
    using assms(2,4) by (intro product_integral_fold assms(1,3)) auto
  also have "... = (\<integral>x. (\<integral>y. f (y(i := (x i))) \<partial>PiM J M) \<partial>PiM {i} M)"
    by (intro Bochner_Integration.integral_cong refl arg_cong[where f="f"])
     (auto simp add:space_PiM merge_def fun_upd_def PiE_def extensional_def)
  also have "... = ?R"
    using assms(1,4) by (intro product_integral_singleton assms(1) 2) auto
  finally show ?thesis by simp
qed

lemma product_integral_insert_rev:
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes "\<And>k. k \<in> {i} \<union> J \<Longrightarrow> sigma_finite_measure (M k)"
  assumes "i \<notin> J"
  assumes "finite J"
  assumes "integrable (PiM (insert i J) M) f"
  shows "(\<integral>x. f x \<partial>PiM (insert i J) M) = (\<integral>y. (\<integral>x. f (y(i := x)) \<partial>M i) \<partial>PiM J M)" (is "?L = ?R")
proof -
  have "?L = (\<integral>x. f x \<partial>PiM (J \<union> {i}) M)" by simp
  also have "... = (\<integral>x. (\<integral>y. f (merge J {i} (x,y)) \<partial>PiM {i} M) \<partial>PiM J M)"
    using assms(2,4) by (intro product_integral_fold assms(1,3)) auto
  also have "... = (\<integral>x. (\<integral>y. f (x(i := (y i))) \<partial>PiM {i} M) \<partial>PiM J M)"
    unfolding merge_singleton[OF assms(2)]
    by (intro Bochner_Integration.integral_cong refl arg_cong[where f="f"])
     (metis PiE_restrict assms(2) restrict_upd space_PiM)
  also have "... = ?R"
    using assms(1,4) by (intro Bochner_Integration.integral_cong product_integral_singleton) auto
  finally show ?thesis by simp
qed

lemma merge_empty[simp]:
  "merge {} I (y,x) = restrict x I"
  "merge I {} (y,x) = restrict y I"
  unfolding merge_def restrict_def by auto

lemma merge_cong:
  assumes "restrict x1 I = restrict x2 I"
  assumes "restrict y1 J = restrict y2 J"
  shows "merge I J (x1,y1) = merge I J (x2,y2)"
  using assms unfolding merge_def restrict_def
  by (intro ext) (smt (verit, best) case_prod_conv)

lemma restrict_merge:
  "restrict (merge I J x) K = merge (I \<inter> K) (J \<inter> K) x"
  unfolding restrict_def merge_def by (intro ext) (auto simp:case_prod_beta)

lemma map_prod_measurable:
  assumes "f \<in> M \<rightarrow>\<^sub>M M'"
  assumes "g \<in> N \<rightarrow>\<^sub>M N'"
  shows "map_prod f g \<in> M \<Otimes>\<^sub>M N \<rightarrow>\<^sub>M M' \<Otimes>\<^sub>M N'"
  using assms by (subst measurable_pair_iff) simp

lemma mc_diarmid_inequality_aux:
  fixes f :: "(nat \<Rightarrow> 'a) \<Rightarrow> real"
  fixes n :: nat
  assumes "\<And>i. i < n \<Longrightarrow> prob_space (M i)"
  assumes "\<And>i x y. i<n \<Longrightarrow> {x,y} \<subseteq> space (PiM {..<n} M) \<Longrightarrow> (\<forall>j\<in>{..<n}-{i}. x j=y j) \<Longrightarrow> \<bar>f x-f y\<bar>\<le>c i"
  assumes f_meas: "f \<in> borel_measurable (PiM {..<n} M)" and \<epsilon>_gt_0: "\<epsilon> >0"
  shows "\<P>(\<omega> in PiM {..<n} M. f \<omega> - (\<integral>\<xi>. f \<xi> \<partial>PiM {..<n} M) \<ge> \<epsilon>) \<le> exp (-(2*\<epsilon>^2)/(\<Sum>i<n. (c i)^2))"
    (is "?L \<le> ?R")
proof -
  define h where "h k = (\<lambda>\<xi>. (\<integral>\<omega>. f (merge {..<k} {k..<n} (\<xi>, \<omega>)) \<partial>PiM {k..<n} M))" for k

  define t :: real where "t = 4 * \<epsilon> / (\<Sum>i<n. (c i)^2)"

  define V where "V i \<xi> = h (Suc i) \<xi> - h i \<xi>" for i \<xi>

  obtain x0 where x0:"x0 \<in> space (PiM {..<n} M)"
    using prob_space.not_empty[OF prob_space_PiM] assms(1) by fastforce

  have delta: "\<bar>f x - f y\<bar> \<le> c i" if "i < n"
    "x \<in> PiE {..<n} (\<lambda>i. space (M i))" "y \<in> PiE {..<n} (\<lambda>i. space (M i))"
    "restrict x ({..<n}-{i}) = restrict y ({..<n}-{i})"
  for x y i
  proof (rule assms(2)[OF that(1)], goal_cases)
    case 1
    then show ?case using that(2,3) unfolding space_PiM by auto
  next
    case 2
    then show ?case using that(4) by (intro ballI) (metis restrict_apply')
  qed

  have c_ge_0: "c j \<ge> 0" if "j < n" for j
  proof -
    have "0 \<le> \<bar>f x0 - f x0\<bar>" by simp
    also have "... \<le> c j" using x0 unfolding space_PiM by (intro delta that) auto
    finally show ?thesis by simp
  qed
  hence sum_c_ge_0: "(\<Sum>i<n. (c i)^2) \<ge> 0" by (meson sum_nonneg zero_le_power2)

  hence t_ge_0: "t \<ge> 0" using \<epsilon>_gt_0 unfolding t_def by simp

  note borel_rules =
    borel_measurable_sum measurable_compose[OF _ borel_measurable_exp]
    borel_measurable_times

  note int_rules =
    prob_space_PiM assms(1) borel_rules
    prob_space.integrable_bounded bounded_intros
  have h_n: "h n \<xi> = f \<xi>" if "\<xi> \<in> space (PiM {..<n} M)" for \<xi>
  proof -
    have "h n \<xi> = (\<integral>\<omega>. f (\<lambda>i\<in>{..<n}. \<xi> i) \<partial>PiM {} M)"
      unfolding h_def using leD
      by (intro Bochner_Integration.integral_cong PiM_cong arg_cong[where f="f"] restrict_cong)
       auto
    also have "... = f (restrict \<xi> {..<n})"
      unfolding PiM_empty by simp
    also have "... = f \<xi>"
      using that unfolding space_PiM PiE_def
      by (simp add: extensional_restrict)
    finally show ?thesis
      by simp
  qed

  have h_0: "h 0 \<xi> = (\<integral>\<omega>. f \<omega> \<partial>PiM {..<n} M)" for \<xi>
    unfolding h_def by (intro Bochner_Integration.integral_cong PiM_cong refl)
     (simp_all add:space_PiM atLeast0LessThan)

  have h_cong: "h j \<omega> = h j \<xi>" if "restrict \<omega> {..<j} = restrict \<xi> {..<j}" for j \<omega> \<xi>
    using that unfolding h_def
    by (intro Bochner_Integration.integral_cong refl arg_cong[where f="f"] merge_cong) auto

  have h_meas: "h i \<in> borel_measurable (PiM I M)" if "i \<le> n" "{..<i} \<subseteq> I" for i I
  proof -
    have 0: "{..<n} = {..<i} \<union> {i..<n}"
      using that(1) by auto

    have 1: "merge {..<i} {i..<n} = merge {..<i} {i..<n} \<circ> map_prod (\<lambda>x. restrict x {..<i}) id"
      unfolding merge_def map_prod_def restrict_def comp_def
      by (intro ext) (auto simp:case_prod_beta')

    have "merge {..<i} {i..<n} \<in> Pi\<^sub>M I M \<Otimes>\<^sub>M Pi\<^sub>M {i..<n} M \<rightarrow>\<^sub>M Pi\<^sub>M {..<n} M"
      unfolding 0 by (subst 1) (intro measurable_comp[OF _ measurable_merge] map_prod_measurable
          measurable_ident measurable_restrict_subset that(2))
    hence "(\<lambda>x. f (merge {..<i} {i..<n} x)) \<in> borel_measurable (Pi\<^sub>M I M \<Otimes>\<^sub>M Pi\<^sub>M {i..<n} M)"
      by (intro measurable_compose[OF _ f_meas])
    thus ?thesis
      unfolding h_def by (intro sigma_finite_measure.borel_measurable_lebesgue_integral
            prob_space_imp_sigma_finite prob_space_PiM assms(1)) (auto simp:case_prod_beta')
  qed

  have merge_space_aux:"merge {..<j} {j..<n} u \<in> (\<Pi>\<^sub>E i\<in>{..<n}. space (M i))"
    if "j \<le> n" "fst u \<in> Pi {..<j} (\<lambda>i. space (M i))" "snd u \<in> Pi {j..<n} (\<lambda>i. space (M i))"
    for u  j
  proof -
    have "merge {..<j} {j..<n} (fst u, snd u) \<in> (PiE ({..<j} \<union> {j..<n}) (\<lambda>i. space (M i)))"
      using that by (intro iffD2[OF PiE_cancel_merge]) auto
    also have "... =  (\<Pi>\<^sub>E i\<in>{..<n}. space (M i))"
      using that by (intro arg_cong2[where f="PiE"] refl) auto
    finally show ?thesis by simp
  qed

  have merge_space:"merge {..<j} {j..<n} (u, v) \<in> (\<Pi>\<^sub>E i\<in>{..<n}. space (M i))"
    if "j \<le> n" "u \<in> PiE {..<j} (\<lambda>i. space (M i))" "v \<in> PiE {j..<n} (\<lambda>i. space (M i))"
    for u v j
    using that by (intro merge_space_aux) (simp_all add:PiE_def)

  have delta': "\<bar>f x - f y\<bar> \<le> (\<Sum>i<n. c i)"
    if "x \<in> PiE {..<n} (\<lambda>i. space (M i))" "y \<in> PiE {..<n} (\<lambda>i. space (M i))" for x y
  proof -
    define m where "m i = merge {..<i} {i..<n} (x,y)" for i

    have 0: "z \<in> Pi I (\<lambda>i. space (M i))" if "z \<in> PiE {..<n} (\<lambda>i. space (M i))"
       "I \<subseteq> {..<n}" for z I
      using that unfolding PiE_def by auto

    have 3: "{..<Suc i} \<inter> ({..<n} - {i}) = {..<i}"
      "{Suc i..<n} \<inter> ({..<n} - {i}) = {Suc i..<n}"
      "{..<i} \<inter> ({..<n} - {i}) = {..<i}"
      "{i..<n} \<inter> ({..<n} - {i}) = {Suc i..<n}"
      if "i < n" for i
      using that by auto

    have "\<bar>f x - f y\<bar> = \<bar>f (m n) - f(m 0)\<bar>"
      using that unfolding m_def by (simp add:atLeast0LessThan)
    also have "... = \<bar>\<Sum>i < n. f (m (Suc i)) - f (m i)\<bar>"
      by (subst sum_lessThan_telescope) simp
    also have "... \<le> (\<Sum>i < n. \<bar>f (m (Suc i)) - f (m i)\<bar>)"
      by simp
    also have "... \<le> (\<Sum>i < n. c i)"
      using that unfolding m_def by (intro delta sum_mono merge_space_aux 0 subsetI)
       (simp_all add:restrict_merge 3)
    finally show ?thesis
      by simp
  qed

  have "norm (f x) \<le> norm (f x0) + sum c {..<n}" if "x \<in> space (Pi\<^sub>M {..<n} M)" for x
  proof -
    have "\<bar>f x - f x0\<bar> \<le> sum c {..<n}"
      using x0 that unfolding space_PiM by (intro delta') auto
    thus ?thesis
      by simp
  qed
  hence f_bounded: "bounded (f ` space (PiM {..<n} M))"
    by (intro boundedI[where B="norm (f x0) + (\<Sum>i<n. c i)"]) auto

  have f_merge_bounded:
    "bounded ((\<lambda>\<omega>. (f (merge {..<j} {j..<n} (u, \<omega>)))) ` space (Pi\<^sub>M {j..<n} M))"
    if "j \<le> n" "u \<in> PiE {..<j} (\<lambda>i. space (M i))" for u j
  proof -
    have "(\<lambda>\<omega>. merge {..<j} {j..<n} (u, \<omega>)) ` space (Pi\<^sub>M {j..<n} M) \<subseteq> space (Pi\<^sub>M {..<n} M)"
      using that  unfolding space_PiM
      by (intro image_subsetI merge_space) auto
    thus ?thesis
      by (subst image_image[of "f",symmetric]) (intro bounded_subset[OF f_bounded] image_mono)
  qed

  have f_merge_meas_aux:
    "(\<lambda>\<omega>. f (merge {..<j} {j..<n} (u, \<omega>))) \<in> borel_measurable (Pi\<^sub>M {j..<n} M)"
    if "j \<le> n" "u \<in> Pi {..<j} (\<lambda>i. space (M i))" for j u
  proof -

    have 0: "{..<n} = {..<j } \<union> {j ..<n}"
      using that(1) by auto

    have 1: "merge {..<j} {j..<n} (u,\<omega>) = merge {..<j} {j..<n} (restrict u {..<j},\<omega>)" for \<omega>
      by (intro merge_cong) auto

    have "(\<lambda>\<omega>. merge {..<j} {j..<n} (u, \<omega>)) \<in> Pi\<^sub>M {j..<n} M \<rightarrow>\<^sub>M Pi\<^sub>M {..<n} M"
      using that unfolding 0 1
      by (intro measurable_compose[OF _ measurable_merge] measurable_Pair1')
       (simp add:space_PiM)
    thus ?thesis
      by (intro measurable_compose[OF _ f_meas])
  qed

  have f_merge_meas: "(\<lambda>\<omega>. f (merge {..<j} {j..<n} (u, \<omega>))) \<in> borel_measurable (Pi\<^sub>M {j..<n} M)"
    if "j \<le> n" "u \<in> PiE {..<j} (\<lambda>i. space (M i))" for j u
    using that unfolding PiE_def by (intro f_merge_meas_aux) auto

  have h_bounded: "bounded (h i ` space (PiM I M))"
    if h_bounded_assms: "i \<le> n" "{..<i} \<subseteq> I" for i I
  proof -
    have "merge {..<i} {i..<n} x \<in> space (Pi\<^sub>M {..<n} M)"
      if "x \<in> (\<Pi>\<^sub>E i\<in>I. space (M i)) \<times> (\<Pi>\<^sub>E i\<in>{i..<n}. space (M i))" for x
      using that h_bounded_assms unfolding space_PiM by (intro merge_space_aux)
        (auto simp: PiE_def mem_Times_iff)
    hence "bounded ((\<lambda>x. f (merge {..<i} {i..<n} x)) `
      ((\<Pi>\<^sub>E i\<in>I. space (M i)) \<times> (\<Pi>\<^sub>E i\<in>{i..<n}. space (M i))))"
      by (subst image_image[of "f",symmetric])
       (intro bounded_subset[OF f_bounded] image_mono image_subsetI)
    thus ?thesis
      using that unfolding h_def
      by (intro prob_space.finite_measure finite_measure.bounded_int int_rules)
        (auto simp:space_PiM PiE_def)
  qed

  have V_bounded: "bounded (V i ` space (PiM I M))"
    if "i < n" "{..<i+1} \<subseteq> I" for i I
    using that unfolding V_def by (intro bounded_intros h_bounded) auto

  have V_upd_bounded: "bounded ((\<lambda>x. V j (\<xi>(j := x))) ` space (M j))"
    if V_upd_bounded_assms: "\<xi> \<in> space (Pi\<^sub>M {..<j} M)" "j < n" for j \<xi>
  proof -
    have "\<xi>(j := v) \<in> space (Pi\<^sub>M {..<j + 1} M)" if "v \<in> space (M j)" for v
      using V_upd_bounded_assms that unfolding space_PiM PiE_def extensional_def Pi_def by auto
    thus ?thesis
        using that unfolding image_image[of "V j" "(\<lambda>x. (\<xi>(j := x)))",symmetric]
        by (intro bounded_subset[OF V_bounded[of "j" "{..<j+1}"]] that image_mono) auto
  qed

  have h_step: "h j \<omega> = \<integral>\<tau>. h (j+1) (\<omega>(j := \<tau>)) \<partial> M j" (is "?L1 = ?R1")
    if "\<omega> \<in> space (PiM {..<j} M)" "j < n" for j \<omega>
  proof -
    have 0: "(\<lambda>x. f (merge {..<j} {j..<n} (\<omega>, x))) \<in> borel_measurable (Pi\<^sub>M {j..<n} M)"
      using that unfolding space_PiM by (intro f_merge_meas) auto

    have 1: "insert j {Suc j..<n} = {j..<n}"
      using that by auto

    have 2: "bounded ((\<lambda>x.(f (merge {..<j} {j..<n} (\<omega>, x)))) ` space (Pi\<^sub>M {j..<n} M))"
      using that by (intro f_merge_bounded) (simp_all add: space_PiM)

    have "?L1 = (\<integral>\<xi>. f (merge {..<j} {j..<n} (\<omega>, \<xi>)) \<partial>PiM (insert j {j+1..<n}) M)"
      unfolding h_def using that by (intro Bochner_Integration.integral_cong refl PiM_cong) auto
    also have "...=(\<integral>\<tau>.(\<integral>\<xi>. f (merge {..<j} {j..<n} (\<omega>, (\<xi>(j := \<tau>)))) \<partial>PiM {j+1..<n} M)\<partial>M j)"
      using that(1,2) 0 1 2 by (intro product_integral_insert prob_space_imp_sigma_finite assms(1)
          int_rules f_merge_meas) (simp_all)
    also have "... = ?R1"
      using that(2) unfolding h_def
      by (intro Bochner_Integration.integral_cong arg_cong[where f="f"] ext) (auto simp:merge_def)
    finally show ?thesis
      by simp
  qed

  have V_meas: "V i \<in> borel_measurable (PiM I M)" if "i < n" "{..<i+1} \<subseteq> I" for i I
    unfolding V_def using that by (intro borel_measurable_diff h_meas) auto

  have V_upd_meas: "(\<lambda>x. V j (\<xi>(j := x))) \<in> borel_measurable (M j)"
    if "j < n" "\<xi> \<in> space (Pi\<^sub>M {..<j} M)" for j \<xi>
    using that by (intro measurable_compose[OF _ V_meas[where I="insert j {..<j}"]]
          measurable_component_update) auto

  have V_cong:
    "V j \<omega> = V j \<xi>" if "restrict \<omega> {..<(j+1)} = restrict \<xi> {..<(j+1)}" for j \<omega> \<xi>
    using that restrict_subset_eq[OF _ that] unfolding V_def
    by (intro arg_cong2[where f="(-)"] h_cong) simp_all

  have exp_V: "(\<integral>\<omega>. V j (\<xi>(j := \<omega>)) \<partial>M j) = 0" (is "?L1 = 0")
    if "j < n" "\<xi> \<in> space (PiM {..<j} M)" for j \<xi>
  proof -

    have "fun_upd \<xi> j ` space (M j) \<subseteq> space (Pi\<^sub>M (insert j {..<j}) M)"
      using that unfolding space_PiM by (intro image_subsetI PiE_fun_upd) auto
    hence 0:"bounded ((\<lambda>x. h (Suc j) (\<xi>(j := x))) ` space (M j))"
      unfolding image_image[of "h (Suc j)" "\<lambda>x. \<xi>(j := x)",symmetric] using that
      by (intro bounded_subset[OF h_bounded[where i="j+1" and I="{..<j+1}"]] image_mono)
        (auto simp:lessThan_Suc)

    have 1:"(\<lambda>x. h (Suc j) (\<xi>(j := x))) \<in> borel_measurable (M j)"
      using h_meas that by (intro measurable_compose[OF _ h_meas[where I="insert j {..<j}"]]
          measurable_component_update) auto

    have "?L1 =(\<integral>\<omega>. h (Suc j) (\<xi>(j := \<omega>)) - h j \<xi> \<partial>M j)"
      unfolding V_def
      by (intro Bochner_Integration.integral_cong arg_cong2[where f="(-)"] refl h_cong) auto
    also have "... = (\<integral>\<omega>. h (Suc j) (\<xi>(j := \<omega>)) \<partial>M j) - (\<integral>\<omega>. h j \<xi> \<partial>M j)"
      using that by (intro Bochner_Integration.integral_diff int_rules 0 1) auto
    also have "... = 0"
      using that(1) assms(1) prob_space.prob_space unfolding h_step[OF that(2,1)] by auto
    finally show ?thesis
      by simp
  qed

  have var_V: "\<bar>V j x - V j y\<bar> \<le> c j" (is "?L1 \<le> ?R1")
    if var_V_assms: "j < n" "{x,y} \<subseteq> space (PiM {..<j+1} M)"
       "restrict x {..<j} = restrict y {..<j}"  for x y j
  proof -
    have x_ran: "x \<in> PiE {..<j+1} (\<lambda>i. space (M i))" and y_ran: "y \<in> PiE {..<j+1} (\<lambda>i. space (M i))"
      using that(2) by (simp_all add:space_PiM)

    have 0: "j+1 \<le> n"
      using that by simp

    have "?L1 = \<bar>h (Suc j) x - h j y - (h (Suc j) y - h j y)\<bar>"
      unfolding V_def by (intro arg_cong[where f="abs"] arg_cong2[where f="(-)"] refl h_cong that)
    also have "... = \<bar>h (j+1) x - h (j+1) y\<bar>"
      by simp
    also have "... =
      \<bar>(\<integral>\<omega>. f(merge {..<j+1} {j+1..<n} (x,\<omega>))-f(merge {..<j+1} {j+1..<n} (y,\<omega>)) \<partial>PiM {j+1..<n} M)\<bar>"
      using that unfolding h_def by (intro arg_cong[where f="abs"] f_merge_meas[OF 0] x_ran
          Bochner_Integration.integral_diff[symmetric] int_rules f_merge_bounded[OF 0] y_ran) auto
    also have "... \<le>
      (\<integral>\<omega>. \<bar>f(merge {..<j+1} {j+1..<n} (x,\<omega>))-f(merge {..<j+1} {j+1..<n} (y,\<omega>))\<bar> \<partial>PiM {j+1..<n} M)"
      by (intro integral_abs_bound)
    also have "... \<le> (\<integral>\<omega>. c j \<partial>PiM {j+1..<n} M)"
    proof (intro Bochner_Integration.integral_mono' delta int_rules c_ge_0 ballI merge_space 0)
      fix \<omega> assume "\<omega> \<in> space (Pi\<^sub>M {j + 1..<n} M)"
      have "{..<j + 1} \<inter> ({..<n} - {j}) = {..<j}"
        using that by auto
      thus "restrict (merge {..<j+1} {j+1..<n} (x, \<omega>)) ({..<n}-{j}) =
            restrict (merge {..<j+1} {j+1..<n} (y, \<omega>)) ({..<n}-{j})"
        using that(1,3) less_antisym unfolding restrict_merge by (intro merge_cong refl) auto
    qed (simp_all add: space_PiM that(1) x_ran[simplified] y_ran[simplified])
    also have "... = c j"
      by (auto intro!:prob_space.prob_space prob_space_PiM assms(1))
    finally show ?thesis by simp
  qed

  have "f \<xi> - (\<integral>\<omega>. f \<omega> \<partial>(PiM {..<n} M)) = (\<Sum>i < n. V i \<xi>)" if "\<xi> \<in> space (PiM {..<n} M)" for \<xi>
    using that unfolding V_def by (subst sum_lessThan_telescope) (simp add: h_0 h_n)
  hence "?L = \<P>(\<xi> in PiM {..<n} M. (\<Sum>i < n. V i \<xi>) \<ge> \<epsilon>)"
    by (intro arg_cong2[where f="measure"] refl Collect_restr_cong arg_cong2[where f="(\<le>)"]) auto
  also have "... \<le> \<P>(\<xi> in PiM {..<n} M. exp( t * (\<Sum>i < n. V i \<xi>) ) \<ge> exp (t * \<epsilon>))"
  proof (intro finite_measure.finite_measure_mono subsetI prob_space.finite_measure int_rules)
    show "{\<xi> \<in> space (Pi\<^sub>M {..<n} M). exp (t * \<epsilon>) \<le> exp (t * (\<Sum>i<n. V i \<xi>))} \<in> sets (Pi\<^sub>M {..<n} M)"
      using V_meas by measurable
  qed  (auto intro!:mult_left_mono[OF _ t_ge_0])
  also have "... \<le> (\<integral>\<xi>. exp(t*(\<Sum>i < n. V i \<xi>)) \<partial>PiM {..<n} M)/ exp (t*\<epsilon>)"
    by (intro integral_Markov_inequality_measure[where A="{}"] int_rules V_bounded V_meas) auto
  also have "... = exp(t^2 * (\<Sum>i\<in>{n..<n}. c i^2)/8-t*\<epsilon>)*(\<integral>\<xi>. exp(t*(\<Sum>i < n. V i \<xi>)) \<partial>PiM {..<n} M)"
    by (simp add:exp_minus inverse_eq_divide)
  also have "... \<le> exp(t^2 * (\<Sum>i\<in>{0..<n}. c i^2)/8-t*\<epsilon>)*(\<integral>\<xi>. exp(t*(\<Sum>i < 0. V i \<xi>)) \<partial>PiM {..<0} M)"
  proof (rule ineq_chain)
    fix j assume a:"j < n"
    let ?L1 = "exp (t\<^sup>2*(\<Sum>i=j+1..<n. (c i)\<^sup>2)/8-t*\<epsilon>)"
    let ?L2 = "?L1 * (\<integral>\<xi>. exp (t * (\<Sum>i<j+1. V i \<xi>)) \<partial>PiM {..<j+1} M)"

    note V_upd_meas = V_upd_meas[OF a]

    have "?L2 = ?L1 * (\<integral>\<xi>. exp (t * (\<Sum>i<j. V i \<xi>)) * exp(t * V j \<xi>) \<partial>PiM (insert j {..<j}) M)"
      by (simp add:algebra_simps exp_add lessThan_Suc)
    also have "... = ?L1 *
      (\<integral>\<xi>. (\<integral>\<omega>. exp (t * (\<Sum>i<j. V i (\<xi>(j := \<omega>)))) * exp(t * V j (\<xi>(j := \<omega>))) \<partial>M j) \<partial>PiM {..<j} M)"
      using a by (intro product_integral_insert_rev arg_cong2[where f="(*)"] int_rules
          prob_space_imp_sigma_finite V_bounded V_meas) auto
    also have "... =?L1*(\<integral>\<xi>.(\<integral>\<omega>. exp (t*(\<Sum>i<j. V i \<xi>))*exp(t*V j (\<xi>(j := \<omega>))) \<partial>M j) \<partial>PiM {..<j} M)"
      by (intro arg_cong2[where f="(*)"] Bochner_Integration.integral_cong
          arg_cong[where f="exp"] sum.cong V_cong restrict_fupd) auto
    also have "... =?L1*(\<integral>\<xi>. exp (t*(\<Sum>i<j. V i \<xi>))*(\<integral>\<omega>. exp(t*V j (\<xi>(j := \<omega>))) \<partial>M j) \<partial>PiM {..<j} M)"
      using a by (intro arg_cong2[where f="(*)"] Bochner_Integration.integral_cong refl
          Bochner_Integration.integral_mult_right V_upd_meas V_upd_bounded int_rules) auto
    also have "... \<le> ?L1 * \<integral>\<xi>. exp (t*(\<Sum>i<j. V i \<xi>))* exp (t^2 * c j^2/8) \<partial>PiM {..<j} M"
    proof (intro mult_left_mono integral_mono')
      fix \<xi> assume c:"\<xi> \<in> space (Pi\<^sub>M {..<j} M)"
      hence b:"\<xi> \<in> PiE {..<j} (\<lambda>i. space (M i))"
        unfolding space_PiM by simp
      moreover have "\<xi>(j := v) \<in> PiE {..<j+1} (\<lambda>i. space (M i))" if "v \<in> space (M j)" for v
        using b that unfolding PiE_def extensional_def Pi_def by auto
      ultimately show "LINT \<omega>|M j. exp (t * V j (\<xi>(j := \<omega>))) \<le> exp (t\<^sup>2 * (c j)\<^sup>2 / 8)"
        using V_upd_meas[OF c]
        by (intro prob_space.Hoeffdings_lemma_bochner_3 exp_V var_V a int_rules)
          (auto simp: space_PiM)
    next
      show "integrable (Pi\<^sub>M {..<j} M) (\<lambda>x. exp (t * (\<Sum>i<j. V i x)) * exp (t\<^sup>2 * (c j)\<^sup>2 / 8))"
        using a by (intro int_rules V_bounded V_meas) auto
    qed auto
    also have "... = ?L1 * ((\<integral>\<xi>. exp (t*(\<Sum>i<j. V i \<xi>)) \<partial>PiM {..<j} M) * exp (t^2 * c j^2/8))"
    proof (subst Bochner_Integration.integral_mult_left)
      show "integrable (Pi\<^sub>M {..<j} M) (\<lambda>\<xi>. exp (t * (\<Sum>i<j. V i \<xi>)))"
        using a by (intro int_rules V_bounded V_meas) auto
    qed auto
    also have "... =
      exp (t\<^sup>2*(\<Sum>i\<in>insert j {j+1..<n}. (c i)\<^sup>2)/8-t*\<epsilon>) * (\<integral>\<xi>. exp (t * (\<Sum>i<j. V i \<xi>))\<partial>PiM {..<j} M)"
      by (simp_all add:exp_add[symmetric] field_simps)
    also have "...=exp (t\<^sup>2*(\<Sum>i=j..<n. (c i)\<^sup>2)/8-t*\<epsilon>) * (\<integral>\<xi>. exp (t * (\<Sum>i<j. V i \<xi>))\<partial>PiM {..<j} M)"
      using a by (intro arg_cong2[where f="(*)"] arg_cong[where f="exp"] refl arg_cong2
          [where f="(-)"] arg_cong2[where f="(/)"] sum.cong) auto
    finally show "?L2\<le>exp(t\<^sup>2*(\<Sum>i=j..<n. (c i)\<^sup>2)/8-t*\<epsilon>)*(\<integral>\<xi>. exp (t*(\<Sum>i<j. V i \<xi>))\<partial>PiM {..<j} M)"
      by simp
  qed
  also have "... = exp(t^2 * (\<Sum>i<n. c i^2)/8-t*\<epsilon>)" by (simp add:PiM_empty atLeast0LessThan)
  also have "... = exp(t * ((t * (\<Sum>i<n. c i^2)/8)-\<epsilon>))" by (simp add:algebra_simps power2_eq_square)
  also have "... = exp(t * (-\<epsilon>/2))" using sum_c_ge_0 by (auto simp add:divide_simps t_def)
  also have "... = ?R" unfolding t_def by (simp add:field_simps power2_eq_square)
  finally show ?thesis by simp
qed

theorem mc_diarmid_inequality_distr:
  fixes f :: "('i \<Rightarrow> 'a) \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (M i)"
  assumes "\<And>i x y. i \<in> I \<Longrightarrow> {x,y} \<subseteq> space (PiM I M) \<Longrightarrow> (\<forall>j\<in>I-{i}. x j=y j) \<Longrightarrow> \<bar>f x-f y\<bar>\<le>c i"
  assumes f_meas: "f \<in> borel_measurable (PiM I M)" and \<epsilon>_gt_0: "\<epsilon> > 0"
  shows "\<P>(\<omega> in PiM I M. f \<omega> - (\<integral>\<xi>. f \<xi> \<partial>PiM I M) \<ge> \<epsilon>) \<le> exp (-(2*\<epsilon>^2)/(\<Sum>i\<in>I. (c i)^2))"
    (is "?L \<le> ?R")
proof -
  define n where "n = card I"
  let ?q = "from_nat_into I"
  let ?r = "to_nat_on I"
  let ?f = "(\<lambda>\<xi>. f (\<lambda>i\<in>I. \<xi> (?r i)))"

  have q: "bij_betw ?q {..<n} I" unfolding n_def by (intro bij_betw_from_nat_into_finite assms(1))
  have r: "bij_betw ?r I {..<n}" unfolding n_def by (intro to_nat_on_finite assms(1))

  have [simp]: "?q (?r x) = x" if "x \<in> I" for x
    by (intro from_nat_into_to_nat_on that countable_finite assms(1))

  have [simp]: "?r (?q x) = x" if "x < n" for x
    using bij_betw_imp_surj_on[OF r] that by (intro to_nat_on_from_nat_into) auto

  have a: "\<And>i. i \<in> {..<n} \<Longrightarrow> prob_space ((M \<circ> ?q) i)"
    unfolding comp_def by (intro assms(2) bij_betw_apply[OF q])

  have b:"PiM I M = PiM I (\<lambda>i. (M \<circ> ?q) (?r i))" by (intro PiM_cong) (simp_all add:comp_def)
  also have "... = distr (PiM {..<n} (M \<circ> ?q)) (PiM I (\<lambda>i. (M \<circ> ?q) (?r i))) (\<lambda>\<omega>. \<lambda>n\<in>I. \<omega> (?r n))"
    using r unfolding bij_betw_def by (intro distr_PiM_reindex[symmetric] a) auto
  finally have c: "PiM I M = distr (PiM{..<n}(M\<circ>?q)) (PiM I (\<lambda>i.(M\<circ>?q)(?r i))) (\<lambda>\<omega>. \<lambda>n\<in>I. \<omega> (?r n))"
    by simp

  have d: "(\<lambda>n\<in>I. x (?r n)) \<in> space (Pi\<^sub>M I M)" if 4:"x \<in> space (Pi\<^sub>M {..<n} (M \<circ> ?q))" for x
  proof -
    have "x (?r i) \<in> space (M i)" if "i \<in> I" for i
    proof -
      have "?r i \<in> {..<n}" using bij_betw_apply[OF r] that by simp
      hence "x (?r i) \<in> space ((M \<circ> ?q) (?r i))" using that 4 PiE_mem unfolding space_PiM by blast
      thus ?thesis using that unfolding comp_def by simp
    qed
    thus ?thesis unfolding space_PiM PiE_def by auto
  qed

  have "?L = \<P>(\<omega> in PiM {..<n} (M \<circ> ?q). ?f \<omega> - (\<integral>\<xi>. f \<xi> \<partial>PiM I M) \<ge> \<epsilon>)"
  proof (subst c, subst measure_distr, goal_cases)
    case 1 thus ?case
      by (intro measurable_restrict measurable_component_singleton bij_betw_apply[OF r])
  next
    case 2 thus ?case unfolding b[symmetric] by (intro measurable_sets_Collect[OF f_meas]) auto
  next
    case 3 thus ?case using d by (intro arg_cong2[where f="measure"] refl) (auto simp:vimage_def)
  qed
  also have "... = \<P>(\<omega> in PiM {..<n} (M \<circ> ?q). ?f \<omega> - (\<integral>\<xi>. ?f \<xi> \<partial>PiM {..<n} (M \<circ> ?q)) \<ge> \<epsilon>)"
  proof (subst c, subst integral_distr, goal_cases)
    case (1 \<omega>) thus ?case
      by (intro measurable_restrict measurable_component_singleton bij_betw_apply[OF r])
  next
    case (2 \<omega>) thus ?case unfolding b[symmetric] by (rule f_meas)
  next
    case 3 thus ?case by simp
  qed
  also have "... \<le> exp (-(2*\<epsilon>^2)/(\<Sum>i<n. (c (?q i))^2))"
  proof (intro mc_diarmid_inequality_aux \<epsilon>_gt_0, goal_cases)
    case (1 i) thus ?case by (intro a) auto
  next
    case (2 i x y)
    have "x (?r j) = y (?r j)" if "j \<in> I - {?q i}" for j
    proof -
      have "?r j \<in> {..<n} - {i}" using that bij_betw_apply[OF r] by auto
      thus ?thesis using 2 by simp
    qed
    hence "\<forall>j\<in>I - {?q i}. (\<lambda>i\<in>I. x (?r i)) j = (\<lambda>i\<in>I. y (?r i)) j" by auto
    thus ?case using 2 d by (intro assms(3) bij_betw_apply[OF q]) auto
  next
    case 3
    have "(\<lambda>x. x (?r i)) \<in> Pi\<^sub>M {..<n} (M \<circ> ?q) \<rightarrow>\<^sub>M M i" if "i \<in> I" for i
    proof -
      have 0:"M i = (M \<circ> ?q) (?r i)" using that by (simp add: comp_def)
      show ?thesis unfolding 0 by (intro measurable_component_singleton bij_betw_apply[OF r] that)
    qed
    thus ?case by (intro measurable_compose[OF _ f_meas] measurable_restrict)
  qed
  also have "... = ?R" by (subst sum.reindex_bij_betw[OF q]) simp
  finally show ?thesis by simp
qed

lemma (in prob_space) mc_diarmid_inequality_classic:
  fixes f :: "('i \<Rightarrow> 'a) \<Rightarrow> real"
  assumes "finite I"
  assumes "indep_vars N X I"
  assumes "\<And>i x y. i \<in> I \<Longrightarrow> {x,y} \<subseteq> space (PiM I N) \<Longrightarrow> (\<forall>j\<in>I-{i}. x j=y j) \<Longrightarrow> \<bar>f x-f y\<bar>\<le>c i"
  assumes f_meas: "f \<in> borel_measurable (PiM I N)" and \<epsilon>_gt_0: "\<epsilon> > 0"
  shows "\<P>(\<omega> in M. f (\<lambda>i\<in>I. X i \<omega>) - (\<integral>\<xi>. f (\<lambda>i\<in>I. X i \<xi>) \<partial>M) \<ge> \<epsilon>) \<le> exp (-(2*\<epsilon>^2)/(\<Sum>i\<in>I. (c i)^2))"
    (is "?L \<le> ?R")
proof -
  note indep_imp = iffD1[OF indep_vars_iff_distr_eq_PiM'']
  let ?O = "\<lambda>i. distr M (N i) (X i)"
  have a:"distr M (Pi\<^sub>M I N) (\<lambda>x. \<lambda>i\<in>I. X i x) = Pi\<^sub>M I ?O"
    using assms(2) unfolding indep_vars_def by (intro indep_imp[OF _ assms(2)]) auto

  have b: "space (PiM I ?O) = space (PiM I N)"
    by (metis (no_types, lifting) a space_distr)

  have "(\<lambda>i\<in>I. X i \<omega>) \<in> space (Pi\<^sub>M I N)" if "\<omega> \<in> space M" for \<omega>
    using assms(2) that unfolding indep_vars_def measurable_def space_PiM by auto

  hence "?L = \<P>(\<omega> in M. (\<lambda>i\<in>I. X i \<omega>)\<in> space (Pi\<^sub>M I N)\<and> f (\<lambda>i\<in>I. X i \<omega>)-(\<integral>\<xi>. f (\<lambda>i\<in>I. X i \<xi>) \<partial>M)\<ge>\<epsilon>)"
    by (intro arg_cong2[where f="measure"] Collect_restr_cong refl) auto
  also have "... = \<P>(\<omega> in distr M (Pi\<^sub>M I N) (\<lambda>x. \<lambda>i\<in>I. X i x). f \<omega> - (\<integral>\<xi>. f (\<lambda>i\<in>I. X i \<xi>) \<partial>M) \<ge> \<epsilon>)"
  proof (subst measure_distr, goal_cases)
    case 1 thus ?case using assms(2) unfolding indep_vars_def by (intro measurable_restrict) auto
  next
    case 2 thus ?case unfolding space_distr by (intro measurable_sets_Collect[OF f_meas]) auto
  next
    case 3 thus ?case by (simp_all add:Int_def conj_commute)
  qed
  also have "... = \<P>(\<omega> in PiM I ?O. f \<omega> - (\<integral>\<xi>. f (\<lambda>i\<in>I. X i \<xi>) \<partial>M) \<ge> \<epsilon>)"
    unfolding a by simp
  also have "... = \<P>(\<omega> in PiM I ?O. f \<omega> - (\<integral>\<xi>. f \<xi> \<partial> distr M (Pi\<^sub>M I N) (\<lambda>x. \<lambda>i\<in>I. X i x)) \<ge> \<epsilon>)"
  proof (subst integral_distr[OF _ f_meas], goal_cases)
    case (1 \<omega>) thus ?case using assms(2) unfolding indep_vars_def by (intro measurable_restrict)auto
  next
    case 2 thus ?case by simp
  qed
  also have "... = \<P>(\<omega> in PiM I ?O. f \<omega> - (\<integral>\<xi>. f \<xi> \<partial> Pi\<^sub>M I ?O) \<ge> \<epsilon>)" unfolding a by simp
  also have "... \<le> ?R"
    using f_meas assms(2) b unfolding indep_vars_def
    by (intro mc_diarmid_inequality_distr prob_space_distr assms(1) \<epsilon>_gt_0 assms(3)) auto
  finally show ?thesis by simp
qed

end