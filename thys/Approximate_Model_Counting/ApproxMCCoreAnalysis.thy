section \<open> ApproxMCCore analysis \<close>

text \<open>
  This section analyzes ApproxMCCore with respect to a universal hash family.
  The proof follows Lemmas 1 and 2 from Chakraborty et al.~\cite{DBLP:conf/ijcai/ChakrabortyMV16}.
  \<close>
theory ApproxMCCoreAnalysis imports
  ApproxMCCore
begin

(* Slicing after a family *)
definition Hslice :: "nat \<Rightarrow>
  ('a assg \<Rightarrow> 'b \<Rightarrow> nat assg) \<Rightarrow> ('a assg \<Rightarrow> 'b \<Rightarrow> nat assg)"
  where "Hslice i H = (\<lambda>w s. aslice i (H w s))"

context prob_space
begin

lemma indep_vars_prefix:
  assumes "indep_vars (\<lambda>_. count_space UNIV) H J"
  shows "indep_vars (\<lambda>_. count_space UNIV) (Hslice i H) J"
proof -
  have "indep_vars (\<lambda>_. count_space UNIV) (\<lambda>y. (\<lambda>x. aslice i x) \<circ> H y) J"
    by (auto intro!: indep_vars_compose[OF assms(1)])
  thus ?thesis
    unfolding o_def Hslice_def
    by auto
qed

lemma assg_nonempty_dom:
  shows "
  (\<lambda>x. if x < i then Some True else None) \<in>
    {\<alpha>::nat assg. dom \<alpha> = {0..<i}}"
  by (auto split: if_splits)

lemma card_dom_ran_nat_assg:
  shows "card {\<alpha>::nat assg. dom \<alpha> = {0..<n}} = 2^n"
proof -
  have *: " {\<alpha>::nat assg. dom \<alpha> = {0..<n}} =
    {w. dom w = {0..<n} \<and> ran w \<subseteq> {True,False}}"
    by auto
  have "finite {0..<n}" by auto
  from card_dom_ran[OF this]
  have "card {w. dom w = {0..<n} \<and> ran w \<subseteq> {True,False}} =
    card {True,False} ^ card {0..<n}" .
  thus ?thesis
    unfolding *
    by (auto simp add: numeral_2_eq_2)
qed

lemma card_nat_assg_le:
  assumes "i \<le> n"
  shows "card {\<alpha>::nat assg. dom \<alpha> = {0..<n}} =
    2^(n-i) * card {\<alpha>::nat assg. dom \<alpha> = {0..<i}}"
  unfolding card_dom_ran_nat_assg
  by (metis assms le_add_diff_inverse mult.commute power_add)

lemma empty_nat_assg_slice_notin:
  assumes "i \<le> n"
  assumes "dom \<beta> \<noteq> {0..<i}"
  shows"{\<alpha>::nat assg. dom \<alpha> = {0..<n} \<and> aslice i \<alpha> = \<beta>} = {}"
proof (intro equals0I)
  fix x
  assume "x \<in> {\<alpha>. dom \<alpha> = {0..<n} \<and> aslice i \<alpha> = \<beta>}"
  then have "dom \<beta> = {0..<i}"
    unfolding aslice_def
    using assms(1) by force
  thus False using assms(2) by blast
qed

lemma restrict_map_dom:
  shows "\<alpha> |` dom \<alpha> = \<alpha>"
  unfolding restrict_map_def fun_eq_iff
  by (simp add: domIff)

lemma aslice_refl:
  assumes "dom \<alpha> = {..<i}"
  shows "aslice i \<alpha> = \<alpha>"
  unfolding aslice_def assms[symmetric]
  using restrict_map_dom by auto

lemma bij_betw_with_inverse:
  assumes "f ` A \<subseteq> B"
  assumes "\<And>x. x \<in> A \<Longrightarrow> g (f x) = x"
  assumes "g ` B \<subseteq> A"
  assumes "\<And>x. x \<in> B \<Longrightarrow> f (g x) = x"
  shows "bij_betw f A B"
proof -
  have "inj_on f A"
    by (metis assms(2) inj_onI)

  thus ?thesis
    unfolding bij_betw_def
    using assms
    by (metis image_subset_iff subsetI subset_antisym)
qed

lemma card_nat_assg_slice:
  assumes "i \<le> n"
  assumes "dom \<beta> = {0..<i}"
  shows"card {\<alpha>::nat assg. dom \<alpha> = {0..<n} \<and> aslice i \<alpha> = \<beta>} =
    2 ^ (n-i)"
proof -
  have "dom \<alpha> = {0..<i} \<and> aslice i \<alpha> = \<beta> \<longleftrightarrow> \<alpha> = \<beta>" for \<alpha>
    using aslice_refl
    by (metis assms(2) lessThan_atLeast0)
  then have r2:
    "{\<alpha>::nat assg. dom \<alpha> = {0..<i} \<and> aslice i \<alpha> = \<beta>} = {\<beta>}"
    by simp

  define f where "f =
    (\<lambda>(\<alpha>::nat assg,\<beta>::nat assg) j.
    if j < i then \<beta> j else \<alpha> (j-i))"
  let ?lhs = "({\<alpha>. dom \<alpha> = {0..<n - i}} \<times>
      {\<alpha>. dom \<alpha> = {0..<i} \<and> aslice i \<alpha> = \<beta>})"
  let ?rhs = "{\<alpha>::nat assg. dom \<alpha> = {0..<n} \<and> aslice i \<alpha> = \<beta>}"

  define finv where "finv =
    (\<lambda>fab::nat assg.
      ((\<lambda>j. fab (j + i)),
        fab |` {..<i})
    )"
  have 11: "\<And>x. dom (f x) = {j. if j < i then j \<in> dom (snd x) else j - i \<in> dom (fst x)}"
    unfolding f_def
      by (auto simp add: fun_eq_iff split: if_splits)
  have 1: " f ` ?lhs  \<subseteq> ?rhs"
  proof standard
    fix x
    assume x: "x \<in> f ` ({\<alpha>. dom \<alpha> = {0..<n - i}} \<times> {\<alpha>. dom \<alpha> = {0..<i} \<and> aslice i \<alpha> = \<beta>})"
    obtain a b where ab: "dom a = {0..<n - i}" "dom b = {0..<i}"
      "x = f (a,b)"
      using x by blast
    have 1: "dom x = {0..<n}"
      unfolding ab 11 using assms(1)
      by (auto simp add: ab)
    have 2: "aslice i x = \<beta>"
      using x unfolding f_def
      by (auto simp add: aslice_def restrict_map_def split: if_splits)
    show " x \<in> {\<alpha>. dom \<alpha> = {0..<n} \<and> aslice i \<alpha> = \<beta>}"
      using 1 2 by blast
  qed

  have " dom a = {0..<n - i} \<Longrightarrow>
       dom b = {0..<i} \<Longrightarrow>
       \<forall>x. aslice i b x = \<beta> x \<Longrightarrow>
       \<not> x < i \<Longrightarrow> None = b x" for a b :: "nat assg" and x
    by (metis atLeastLessThan_iff domIff)
  then have 2: "\<And>x. x \<in> ?lhs \<Longrightarrow> finv (f x) = x"
    unfolding finv_def f_def
    by (clarsimp simp add: fun_eq_iff restrict_map_def)

  have 31: "\<And>fab x y.
       dom fab = {0..<n} \<Longrightarrow>
       \<beta> = aslice i fab \<Longrightarrow>
       fab (x + i) = Some y \<Longrightarrow>
       x < n - i" 
    by (metis atLeastLessThan_iff domI less_diff_conv)
  also have "\<And>fab x.
       dom fab = {0..<n} \<Longrightarrow>
       \<beta> = aslice i fab \<Longrightarrow>
       x < i \<Longrightarrow> \<exists>y. fab x = Some y"
    by (metis assms(1) domD dual_order.trans lessThan_atLeast0 lessThan_iff linorder_not_less)
  ultimately have 3: "finv ` ?rhs \<subseteq> ?lhs"
    unfolding finv_def
    by (auto simp add: aslice_def split: if_splits)

  have 4: "\<And>x. x \<in> ?rhs \<Longrightarrow> f (finv x) = x"
    unfolding finv_def f_def
    by (auto simp add: fun_eq_iff restrict_map_def)

  have "bij_betw f ?lhs ?rhs"
    by (auto intro: bij_betw_with_inverse[OF 1 2 3 4])

  from bij_betw_same_card[OF this]
  have
  "card {\<alpha>::nat assg. dom \<alpha> = {0..<n} \<and> aslice i \<alpha> = \<beta>} =
   card ({\<alpha>::nat assg. dom \<alpha> = {0..<n-i}} \<times>
        {\<alpha>::nat assg. dom \<alpha> = {0..<i} \<and> aslice i \<alpha> = \<beta>})"
    by auto
  moreover have "... = 2^(n-i)"
    using r2 card_dom_ran_nat_assg
    by (simp add: card_cartesian_product)

  ultimately show ?thesis by auto
qed

lemma finite_dom:
  assumes "finite V"
  shows "finite {w :: 'a \<rightharpoonup> bool. dom w = V}"
proof -
  have *: "{w :: 'a \<rightharpoonup> bool. dom w = V} =
    {w. dom w = V \<and> ran w \<subseteq> {True,False}}"
    by auto
  show ?thesis unfolding *
    apply (intro finite_set_of_finite_maps)
    using assms by auto
qed

(* TODO: generalizable to any finite output alphabet instead of just booleans *)
lemma universal_prefix_family_from_hash:
  assumes M: "M = measure_pmf p"
  assumes kH: "k_universal k H D {\<alpha>::nat assg. dom \<alpha> = {0..<n}}"
  assumes i: "i \<le> n"
  shows "k_universal k (Hslice i H) D {\<alpha>. dom \<alpha> = {0..<i}}"
proof -
  have "k_wise_indep_vars k (\<lambda>_. count_space UNIV) H D"
    using kH unfolding k_universal_def
    by auto
  then have 1: "k_wise_indep_vars k (\<lambda>_. count_space UNIV) (Hslice i H) D"
    unfolding k_wise_indep_vars_def
    using indep_vars_prefix
    by auto

  have fdom: "finite {\<alpha>::nat assg. dom \<alpha> = {0..<i}}"
    using measure_pmf.finite_dom by blast
  have nempty: "{\<alpha>::nat assg. dom \<alpha> = {0..<i}} \<noteq> {}"
    using assg_nonempty_dom
    by (metis empty_iff)
  have 2: "x \<in> D \<Longrightarrow>
    uniform_on (Hslice i H x) {\<alpha>. dom \<alpha> = {0..<i}}" for x
  proof -
    assume "x \<in> D"
    then have unif: "uniform_on (H x) {\<alpha>. dom \<alpha> = {0..<n}}"
      by (metis kH k_universal_def)
    show "uniform_on (Hslice i H x) {\<alpha>. dom \<alpha> = {0..<i}}"
    proof (intro uniform_onI[OF M fdom nempty])
      fix \<beta>
      have *: "{\<omega> \<in> space M. H x \<omega> \<in> {\<alpha>. aslice i \<alpha> = \<beta>}} =
        {\<omega>. Hslice i H x \<omega> = \<beta>}"
        unfolding Hslice_def
        by (auto simp add: M)

      have "{\<alpha>::nat assg. dom \<alpha> = {0..<n}} \<inter> {\<alpha>.  aslice i \<alpha> = \<beta>} =
        {\<alpha>::nat assg. dom \<alpha> = {0..<n} \<and> aslice i \<alpha> = \<beta>}"
        by auto

      then have "(card ({\<alpha>::nat assg. dom \<alpha> = {0..<n}} \<inter> {\<alpha>.  aslice i \<alpha> = \<beta>}))
        = (if dom \<beta> = {0..<i} then 2^(n-i) else 0)"
       using card_nat_assg_slice[OF i]
       by (simp add: empty_nat_assg_slice_notin i)

     then have **: "real (card ({\<alpha>::nat assg. dom \<alpha> = {0..<n}} \<inter> {\<alpha>.  aslice i \<alpha> = \<beta>}))
        = indicat_real {\<alpha>. dom \<alpha> = {0..<i}} \<beta>  * 2^(n-i)"
       by simp

      from uniform_onD[OF unif, of "{\<alpha>. aslice i \<alpha> = \<beta>}"]
      have "prob {\<omega>. Hslice i H x \<omega> = \<beta>} =
        real (card ({\<alpha>. dom \<alpha> = {0..<n}} \<inter> {\<alpha>. aslice i \<alpha> = \<beta>})) /
        real (card {\<alpha>::nat assg. dom \<alpha> = {0..<n}})"
        unfolding * by auto
      moreover have "... =
        indicat_real {\<alpha>. dom \<alpha> = {0..<i}} \<beta>  * 2^(n-i) /
        real (card {\<alpha>::nat assg. dom \<alpha> = {0..<n}})"
        unfolding ** by auto
      moreover have "... = indicat_real {\<alpha>. dom \<alpha> = {0..<i}} \<beta> * 2^(n-i) / 2^n"
        by (simp add: card_dom_ran_nat_assg)
      moreover have "... = indicat_real {\<alpha>. dom \<alpha> = {0..<i}} \<beta> / 2^i"
        by (simp add: i power_diff)
      moreover have "... =  indicat_real {\<alpha>. dom \<alpha> = {0..<i}} \<beta> / real ((2^i)::nat)" by auto
      moreover have "... =  indicat_real {\<alpha>. dom \<alpha> = {0..<i}} \<beta> / real (card {\<alpha>::nat assg. dom \<alpha> = {0..<i}})"
        using card_dom_ran_nat_assg
        by auto
      ultimately show "prob {\<omega>. Hslice i H x \<omega> = \<beta>} =
         indicat_real {\<alpha>. dom \<alpha> = {0..<i}} \<beta> /
         real (card {\<alpha>::nat assg. dom \<alpha> = {0..<i}})"
        by presburger
    qed
  qed
  show ?thesis
    unfolding k_universal_def
    using 1 2
    by blast
qed

end

context ApproxMCCore
begin

definition pivot :: "real"
  where "pivot = 9.84 * ( 1 + 1 / \<epsilon> )^2"

context
  assumes thresh: "thresh \<ge> (1 + \<epsilon> / (1 + \<epsilon>)) * pivot"
begin

lemma aux_1:
  assumes fin:"finite (set_pmf p)"
  assumes \<sigma>: "\<sigma> > 0"
  assumes exp: "\<mu> i = measure_pmf.expectation p Y"
  assumes var: "\<sigma>^2 = measure_pmf.variance p Y"
  assumes var_bound: "\<sigma>^2 \<le> \<mu> i"
  shows "
    measure_pmf.prob p {y. \<bar> Y y - \<mu> i \<bar> \<ge> \<epsilon> / (1 + \<epsilon>) * \<mu> i }
    \<le> (1 + \<epsilon>)^2 / (\<epsilon>^2 * \<mu> i) "
proof -
  have pvar: "measure_pmf.variance p Y > 0"
    using var \<sigma>
    by (metis zero_less_power)
  have kmu: "\<epsilon> * (\<mu> i) / ((1 + \<epsilon>) * \<sigma>) > 0"
    using \<sigma> pvar var var_bound
    using \<epsilon> by auto
  have mupos: "\<mu> i > 0"
    using pvar var var_bound by linarith
  from spec_chebyshev_inequality [OF fin pvar kmu]
  have "measure_pmf.prob p
    {y. (Y y - measure_pmf.expectation p Y)^2 \<ge>
       (\<epsilon> * (\<mu> i) / ((1 + \<epsilon>) * \<sigma>))^2 * measure_pmf.variance p Y} \<le> 1 / (\<epsilon> * (\<mu> i) / ((1 + \<epsilon>) * \<sigma>))^2"
    by simp
  then have ineq1:"measure_pmf.prob p
    {y. (Y y - \<mu> i)^2 \<ge>
       (\<epsilon> * (\<mu> i) / ((1 + \<epsilon>) * \<sigma>))^2 * \<sigma>^2} \<le> 1 / (\<epsilon> * (\<mu> i) / ((1 + \<epsilon>) * \<sigma>))^2"
    using exp var by simp
  have "(\<lambda>y. (Y y - \<mu> i)^2 \<ge> (\<epsilon> * (\<mu> i) / ((1 + \<epsilon>) * \<sigma>))^2 * \<sigma>^2)
        = (\<lambda>y. (Y y - \<mu> i)^2 \<ge> (\<epsilon> * (\<mu> i) / ((1 + \<epsilon>) * \<sigma>) * \<sigma> )^2)"
    by (metis power_mult_distrib)
  moreover have "... = (\<lambda>y. \<bar> Y y - \<mu> i \<bar> \<ge> \<epsilon> * (\<mu> i) / ((1 + \<epsilon>) * \<sigma>) * \<sigma>)"
  proof -
    have "0 \<le> \<epsilon> * \<mu> i / (1 + \<epsilon>)"
      by (simp add: \<epsilon> less_eq_real_def mupos zero_compare_simps(1))
    then show ?thesis
      apply clarsimp
      by (metis abs_le_square_iff abs_of_nonneg)
  qed
  moreover have "... = (\<lambda>y. \<bar> Y y - \<mu> i \<bar> \<ge> \<epsilon> * (\<mu> i) / (1 + \<epsilon>))"
    using \<sigma> by auto
  ultimately have simp1:"(\<lambda>y. (Y y - \<mu> i)^2 \<ge> (\<epsilon> * (\<mu> i) / ((1 + \<epsilon>) * \<sigma>))^2 * \<sigma>^2)
                  = (\<lambda>y. \<bar> Y y - \<mu> i \<bar> \<ge> \<epsilon> / (1 + \<epsilon>) * (\<mu> i))"
    by auto

  have "\<sigma>^2/(\<mu> i)^2 \<le> (\<mu> i)/(\<mu> i)^2"
    using var_bound \<mu>_gt_zero
    by (simp add: divide_right_mono)
  moreover have "... = 1 / (\<mu> i)"
    by (simp add: power2_eq_square)
  ultimately have simp2: "\<sigma>^2/(\<mu> i)^2 \<le> 1 / (\<mu> i)" by auto

  have "measure_pmf.prob p {y. \<bar> Y y - \<mu> i \<bar> \<ge> \<epsilon> / (1 + \<epsilon>) * (\<mu> i)}
        \<le> 1 / (\<epsilon> * (\<mu> i) / ((1 + \<epsilon>) * \<sigma>))^2"
    using ineq1 simp1
    by auto
  moreover have "... = (1 + \<epsilon>)^2 / \<epsilon>^2 * \<sigma>^2/(\<mu> i)^2"
    by (simp add: power_divide power_mult_distrib)
  moreover have "... \<le> (1 + \<epsilon>)^2 / \<epsilon>^2 * (1 / (\<mu> i))"
    using simp2
    by (smt (verit, best) \<epsilon> divide_pos_pos mult_left_mono times_divide_eq_right zero_less_power)
  ultimately have "measure_pmf.prob p {y. \<bar> Y y - \<mu> i \<bar> \<ge> \<epsilon> / (1 + \<epsilon>) * (\<mu> i)}
                    \<le> (1 + \<epsilon>)^2 / (\<epsilon>^2 * (\<mu> i))"
    by auto
  thus ?thesis by auto
qed

(* Lem 1.1 in IJCAI'16 paper *)
lemma analysis_1_1:
  assumes p: "finite (set_pmf p)"
  assumes ind: "prob_space.k_universal (measure_pmf p) 2 H
    {\<alpha>::'a assg. dom \<alpha> = S}
    {\<alpha>::nat assg. dom \<alpha> = {0..<card S - 1}}"
  assumes i: "i \<le> card S - 1"
  shows "
    measure_pmf.prob p
    {s. \<bar> card_slice ((\<lambda>w. H w s)) i - \<mu> i \<bar> \<ge> \<epsilon> / (1 + \<epsilon>) * \<mu> i}
    \<le> (1 + \<epsilon>)^2 / (\<epsilon>^2 * \<mu> i)"
proof -

  (* The variance for i-th slice *)
  define var where "var =
      (\<lambda>i. measure_pmf.variance p
        (\<lambda>s. real (card (proj S W \<inter>
          {w. Hslice i H w s = aslice i \<alpha>}))))"

  from prob_space.universal_prefix_family_from_hash[OF _ _ ind]
  have hf: "prob_space.k_universal (measure_pmf p) 2
   (Hslice i H) {\<alpha>::'a assg. dom \<alpha> = S} {\<alpha>. dom \<alpha> = {0..<i}}"
    using prob_space_measure_pmf
    using i ind prob_space.universal_prefix_family_from_hash
    by blast

  have pSW: "proj S W \<subseteq> {\<alpha>. dom \<alpha> = S}"
    unfolding proj_def restr_def by (auto split:if_splits)

  have ain: "aslice i \<alpha> \<in> {\<alpha>. dom \<alpha> = {0..<i}}" using \<alpha>
    unfolding aslice_def using i by auto

  from k_universal_expectation_eq[OF p hf finite_proj_S pSW ain]
  have exp:"measure_pmf.expectation p
   (\<lambda>s. real (card (proj S W \<inter>
                     {w. Hslice i H w s = aslice i \<alpha>}))) =
    real (card (proj S W)) /
    real (card {\<alpha>::nat assg. dom \<alpha> = {0..<i}})" .

  have exp_mu:"real (card (proj S W)) /
    real (card {\<alpha>::nat assg. dom \<alpha> = {0..<i}}) = \<mu> i"
    unfolding \<mu>_def
    by (simp add: measure_pmf.card_dom_ran_nat_assg)

  have "proj S W \<inter>
               {w. Hslice i H w s = aslice i \<alpha>} =
    proj S W \<inter> {w. hslice i (\<lambda>w. H w s) w =  aslice i \<alpha>}" for s
    unfolding proj_def Hslice_def hslice_def
    by auto
  then have extend_card_slice:
    "\<And>s. (card (proj S W \<inter> {w. Hslice i H w s = aslice i \<alpha>})) =
    card_slice ((\<lambda>w. H w s)) i"
    unfolding card_slice_def by auto

  have mu_exp:" \<mu> i = measure_pmf.expectation p
   (\<lambda>s. real (card (proj S W \<inter> {w. Hslice i H w s = aslice i \<alpha>})))"
    using exp exp_mu by auto

  from two_universal_variance_bound[OF p hf finite_proj_S pSW ain]
  have "
    var i \<le>
    measure_pmf.expectation p
      (\<lambda>s. real (card (proj S W \<inter>
                        {w. Hslice i H w s = aslice i \<alpha>})))"
    unfolding var_def  .
  then have var_bound: "var i \<le> \<mu> i" using exp exp_mu
    by linarith

  have "var i \<ge> 0" unfolding var_def by auto
  then have "var i > 0 \<or>  var i = 0" by auto
  moreover {
    assume "var i = 0"

    then have 1: "
      measure_pmf.expectation p
        (\<lambda>s. (card_slice (\<lambda>w. H w s) i - \<mu> i)^2) = 0"
      unfolding var_def extend_card_slice mu_exp by auto

    have 2: "measure_pmf.expectation p
        (\<lambda>s. (card_slice (\<lambda>w. H w s) i - \<mu> i)^2) =
      sum (\<lambda>s. (card_slice (\<lambda>w. H w s) i - \<mu> i)^2 * pmf p s) (set_pmf p)"
      using assms by (auto intro!: integral_measure_pmf_real)

    have "\<forall>x \<in> set_pmf p. (card_slice (\<lambda>w. H w x) i - \<mu> i)^2 * pmf p x = 0"
      apply (subst sum_nonneg_eq_0_iff[symmetric])
      using 1 2 p by auto
    then have *: "\<And>x. x \<in> set_pmf p \<Longrightarrow> (card_slice (\<lambda>w. H w x) i - \<mu> i)^2 = 0"
      by (meson mult_eq_0_iff set_pmf_iff)

    have **: "(1 + \<epsilon>)^2 / (\<epsilon>^2 * \<mu> i) > 0"
      using \<mu>_gt_zero \<epsilon> by auto
    have "\<epsilon> / (1 + \<epsilon>) * \<mu> i > 0"
      using \<mu>_gt_zero \<epsilon> by auto
    then have "\<And>s. s \<in> set_pmf p \<Longrightarrow> \<bar> card_slice ((\<lambda>w. H w s)) i - \<mu> i \<bar> < \<epsilon> / (1 + \<epsilon>) * \<mu> i"
      using * by auto
    then have "
    measure_pmf.prob p
    {s. \<bar> card_slice ((\<lambda>w. H w s)) i - \<mu> i \<bar> \<ge> \<epsilon> / (1 + \<epsilon>) * \<mu> i } = 0"
      apply (subst measure_pmf_zero_iff)
      using linorder_not_less by auto
    then have "
    measure_pmf.prob p
      {s. \<bar> card_slice ((\<lambda>w. H w s)) i - \<mu> i \<bar> \<ge> \<epsilon> / (1 + \<epsilon>) * \<mu> i }
      \<le> (1 + \<epsilon>)^2 / (\<epsilon>^2 * \<mu> i)"
      using ** by auto
  }
  moreover {
    define sigma where "sigma = sqrt(var i)"
    assume "var i > 0"

    then have sigma_gt_0: "sigma > 0"
      unfolding sigma_def by simp

    have extend_sigma: "sigma^2 = measure_pmf.variance p
        (\<lambda>s. real (card (proj S W \<inter>
        {w. Hslice i H w s = aslice i \<alpha>})))"
      unfolding sigma_def var_def
      using less_eq_real_def local.var_def real_sqrt_pow2 sigma_def sigma_gt_0
      by fastforce

    have sigma_bound: "sigma^2 \<le> \<mu> i"
      using var_bound sigma_gt_0
      using sigma_def by force

    from aux_1[OF p sigma_gt_0 mu_exp extend_sigma sigma_bound]
    have "
      measure_pmf.prob p
      {s. \<bar> card_slice ((\<lambda>w. H w s)) i - \<mu> i \<bar> \<ge> \<epsilon> / (1 + \<epsilon>) * \<mu> i }
      \<le> (1 + \<epsilon>)^2 / (\<epsilon>^2 * \<mu> i)"
      using extend_card_slice by auto
  }

  ultimately show ?thesis by auto
qed

(* Lem 1.2 in IJCAI'16 paper *)
lemma analysis_1_2:
  assumes p: "finite (set_pmf p)"
  assumes ind: "prob_space.k_universal (measure_pmf p) 2 H
    {\<alpha>::'a assg. dom \<alpha> = S}
    {\<alpha>::nat assg. dom \<alpha> = {0..<card S - 1}}"
  assumes i: "i \<le> card S - 1"
  assumes \<beta>: "\<beta> \<le> 1"
  shows "measure_pmf.prob p
    {s. real(card_slice ((\<lambda>w. H w s)) i) \<le> \<beta> * \<mu> i }
    \<le> 1 / (1 + (1 - \<beta>)^2 * \<mu> i)"
proof -
  have *: "(\<And>s. (0::real) \<le> card_slice ((\<lambda>w. H w s)) i)"
    by simp
  from spec_paley_zygmund_inequality[OF p * \<beta>]
  have paley_zigmund:
    "(measure_pmf.variance p (\<lambda>s. real(card_slice ((\<lambda>w. H w s)) i) )
    + (1-\<beta>)^2 * (measure_pmf.expectation p (\<lambda>s. card_slice ((\<lambda>w. H w s)) i))^2) *
    measure_pmf.prob p {s. real(card_slice ((\<lambda>w. H w s)) i) > \<beta> * measure_pmf.expectation p (\<lambda>s. real(card_slice ((\<lambda>w. H w s)) i) )} \<ge>
    (1-\<beta>)^2 * (measure_pmf.expectation p (\<lambda>s. real(card_slice ((\<lambda>w. H w s)) i) ))^2"
    by auto
  define var where "var = (\<lambda>i. measure_pmf.variance p
      (\<lambda>s. real (card (proj S W \<inter>
      {w. Hslice i H w s = aslice i \<alpha>}))))"

  from prob_space.universal_prefix_family_from_hash[OF _ _ ind]
  have hf: "prob_space.k_universal (measure_pmf p) 2
   (Hslice i H) {\<alpha>::'a assg. dom \<alpha> = S} {\<alpha>. dom \<alpha> = {0..<i}}"
    using prob_space_measure_pmf
    using i ind prob_space.universal_prefix_family_from_hash
    by blast

  have pSW: "proj S W \<subseteq> {\<alpha>. dom \<alpha> = S}"
    unfolding proj_def restr_def
    by (auto split:if_splits)

  have ain: "aslice i \<alpha> \<in> {\<alpha>. dom \<alpha> = {0..<i}}" using \<alpha>
    unfolding aslice_def using i by auto

  from k_universal_expectation_eq[OF p hf finite_proj_S pSW ain]
  have exp:"measure_pmf.expectation p
   (\<lambda>s. real (card (proj S W \<inter>
                     {w. Hslice i H w s = aslice i \<alpha>}))) =
    real (card (proj S W)) /
    real (card {\<alpha>::nat assg. dom \<alpha> = {0..<i}})" .

  have exp_mu:"real (card (proj S W)) /
    real (card {\<alpha>::nat assg. dom \<alpha> = {0..<i}}) = \<mu> i"
    unfolding \<mu>_def
    by (simp add: measure_pmf.card_dom_ran_nat_assg)

  have "proj S W \<inter>
               {w. Hslice i H w s = aslice i \<alpha>} =
    proj S W \<inter> {w. hslice i (\<lambda>w. H w s) w =  aslice i \<alpha>}" for s
    unfolding proj_def Hslice_def hslice_def
    by auto

  then have extend_card_slice:"\<And>s. (card (proj S W \<inter>
                     {w. Hslice i H w s = aslice i \<alpha>})) =
    card_slice ((\<lambda>w. H w s)) i"
    unfolding card_slice_def by auto

  have mu_exp:" \<mu> i = measure_pmf.expectation p
   (\<lambda>s. real (card (proj S W \<inter>
                     {w. Hslice i H w s = aslice i \<alpha>})))"
    using exp exp_mu by auto

  from two_universal_variance_bound[OF p hf finite_proj_S pSW ain]
  have "
    var i \<le>
    measure_pmf.expectation p
      (\<lambda>s. real (card (proj S W \<inter>
                        {w. Hslice i H w s = aslice i \<alpha>})))"
    unfolding var_def  .
  then have var_bound: "var i \<le> \<mu> i" using exp exp_mu
    by linarith

  have pos_mu: "\<mu> i > 0"
    unfolding \<mu>_def
    by (simp add: card_proj_witnesses)

  have comp: "measure_pmf.prob p
      {s. \<beta> * \<mu> i < real (card_slice (\<lambda>w. H w s) i)} =
    (1 - measure_pmf.prob p {s. real(card_slice ((\<lambda>w. H w s)) i) \<le> \<beta> * \<mu> i})"
    apply (subst measure_pmf.prob_compl[symmetric])
    by (auto intro!: arg_cong[where f = "measure_pmf.prob p"])

  have extend_var_bound: "measure_pmf.variance p (\<lambda>s. card_slice ((\<lambda>w. H w s)) i) \<le> \<mu> i"
    using var_bound
    unfolding var_def
    by (simp add: extend_card_slice)
  then have
    "(measure_pmf.variance p (\<lambda>s. real(card_slice ((\<lambda>w. H w s)) i))
      + (1-\<beta>)^2 * (measure_pmf.expectation p (\<lambda>s. real(card_slice ((\<lambda>w. H w s)) i) ) )^2)
      * measure_pmf.prob p {s. real(card_slice ((\<lambda>w. H w s)) i) > \<beta> * measure_pmf.expectation p (\<lambda>s. real(card_slice ((\<lambda>w. H w s)) i) )} \<le>
    (\<mu> i + (1-\<beta>)^2 * (measure_pmf.expectation p ( \<lambda>s. real(card_slice ((\<lambda>w. H w s)) i) ) )^2)
    * measure_pmf.prob p
          {s. real(card_slice ((\<lambda>w. H w s)) i) > \<beta> * measure_pmf.expectation p (\<lambda>s. real(card_slice ((\<lambda>w. H w s)) i) )}"
    by (auto intro!: mult_right_mono)
  moreover have
    "... \<le> (\<mu> i + (1-\<beta>)^2 * (measure_pmf.expectation p ( \<lambda>s. real(card_slice ((\<lambda>w. H w s)) i) ) )^2)
    * measure_pmf.prob p
          {s. real(card_slice ((\<lambda>w. H w s)) i) > \<beta> * measure_pmf.expectation p (\<lambda>s. real(card_slice ((\<lambda>w. H w s)) i) )}"
    by fastforce
  ultimately have
    "(\<mu> i + (1-\<beta>)^2 * (\<mu> i)^2) * measure_pmf.prob p {s. real(card_slice ((\<lambda>w. H w s)) i) > \<beta> * \<mu> i} \<ge> (1-\<beta>)^2 * (\<mu> i)^2"
    unfolding mu_exp extend_card_slice
    using paley_zigmund by linarith
  then have
    "(1 + (1-\<beta>)^2 * (\<mu> i)) * (\<mu> i) * measure_pmf.prob p {s. real(card_slice ((\<lambda>w. H w s)) i) > \<beta> * \<mu> i} \<ge> (1-\<beta>)^2 * (\<mu> i) * (\<mu> i)"
    by (smt (verit) left_diff_distrib' more_arith_simps(11) mult_cancel_right mult_cancel_right2 power2_eq_square)
  then have
    "(1 + (1-\<beta>)^2 * (\<mu> i)) * measure_pmf.prob p {s. real(card_slice ((\<lambda>w. H w s)) i) > \<beta> * \<mu> i} \<ge> (1-\<beta>)^2 * (\<mu> i)"
    using pos_mu by force
  then have
    "(1 + (1-\<beta>)^2 * (\<mu> i)) * (1 - measure_pmf.prob p {s. real(card_slice ((\<lambda>w. H w s)) i) \<le> \<beta> * \<mu> i}) \<ge> (1-\<beta>)^2 * (\<mu> i)"
    using comp by auto
  then have
    "(1 + (1-\<beta>)^2 * (\<mu> i)) - (1 + (1-\<beta>)^2 * (\<mu> i)) * measure_pmf.prob p {s. real(card_slice ((\<lambda>w. H w s)) i) \<le> \<beta> * \<mu> i} \<ge> (1-\<beta>)^2 * (\<mu> i)"
    by (simp add: right_diff_distrib)
  then have
    "(1 + (1-\<beta>)^2 * (\<mu> i)) * measure_pmf.prob p {s. real(card_slice ((\<lambda>w. H w s)) i) \<le> \<beta> * \<mu> i} \<le> 1"
    by simp
  thus ?thesis by (smt (verit, best) mult_nonneg_nonneg nonzero_mult_div_cancel_left pos_mu real_divide_pos_left zero_le_power2)
qed

lemma shift_\<mu>:
  assumes "k \<le> i"
  shows"\<mu> i * 2^k = \<mu> (i-k)"
  unfolding \<mu>_def
  by (auto simp add: assms power_diff)

(* Lem 2.1 in IJCAI'16 paper *)
lemma analysis_2_1:
  assumes p: "finite (set_pmf p)"
  assumes ind: "prob_space.k_universal (measure_pmf p) 2 H
    {\<alpha>::'a assg. dom \<alpha> = S}
    {\<alpha>::nat assg. dom \<alpha> = {0..<card S - 1}}"
  assumes \<epsilon>_up: "\<epsilon> \<le> 1"
  shows "
    measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (T (mstar-3))
      \<le> 1 / 62.5"
proof -
  have "1 + 1 / \<epsilon> > 0"
    by (simp add: \<epsilon> pos_add_strict)
  then have pos_pivot: "pivot > 0"
    unfolding pivot_def
    by simp

  have "mstar \<ge> 4 \<or> mstar < 4" by auto
  moreover {
    assume "mstar < 4"
    then have " measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (T (mstar-3))
      \<le> 1 / 62.5"
      by (auto simp add: T0_empty)
  }
  moreover {
    assume lo_mstar: "mstar \<ge> 4"

    have extend_mu3: "\<mu> (mstar-1) * 2^2 = \<mu> (mstar-3)"
      apply (subst shift_\<mu>)
      subgoal using lo_mstar by linarith
      using numeral_3_eq_3
      using Suc_1 diff_Suc_eq_diff_pred numeral_nat(7) by presburger

    have ******: "1 + \<epsilon> / (1 + \<epsilon>) \<le> 3 / 2"
      using \<epsilon> assms(3) by auto
    have mu_mstar_3_gt_zero: "\<mu> (mstar - 3) / 4 > 0"
      using \<mu>_gt_zero by simp

    from mstar_prop(1)
    have "thresh < \<mu> (mstar - 1) *2^2 / 4 * (1 + \<epsilon> / (1 + \<epsilon>))"
      by auto
    also have "... = \<mu> (mstar - 3) / 4 * (1 + \<epsilon> / (1 + \<epsilon>))"
      unfolding extend_mu3 by auto
    also have "... \<le> \<mu> (mstar - 3) / 4 * (3 / 2)"
      apply (intro mult_left_mono)
      using ****** mu_mstar_3_gt_zero by auto
    also have "... = 3 / 8 * \<mu> (mstar - 3)"
      by auto
    finally have thresh2mu: "thresh < 3 / 8 * \<mu> (mstar - 3)" .

    have "1 + \<epsilon> / (1 + \<epsilon>) > 0"
      by (simp add: add_nonneg_pos \<epsilon>)
    then have "\<mu> (mstar-1) > pivot" (* pivot = thresh / (1 + \<epsilon>/(1+\<epsilon>)) *)
      using mstar_prop(1) thresh
      by (smt (verit) nonzero_mult_div_cancel_right real_divide_pos_left)
    then have lo_mu_mstar_3: "\<mu> (mstar-3) > 4*pivot"
      using extend_mu3
      by simp

    have mstar_3: "mstar-3 \<le> card S - 1"
      using lo_mstar
      using diff_le_self dual_order.trans mstar_prop(3) by blast

    have *: "(5 / 8)^2 = ((25 / 64)::real)"
      by (auto simp add: field_simps)
    have **: " 1 + 25/64 * 4*pivot \<le> 1+ 25 / 64 * \<mu> (mstar - 3) "
      using lo_mu_mstar_3
      by auto

    have "1 + 1/\<epsilon> \<ge> 2"
      by (simp add: \<epsilon> assms(3))
    then have "(1 + 1/\<epsilon>)^2 \<ge> 2^2"
      by (smt (verit) power_mono)
    then have ***: " 1 + 25/64 * 4 * 4*9.84 \<le> 1+ 25 / 64 * 4*pivot"
      unfolding pivot_def
      by auto
    have ****: "1 + 25/64 * 4 * 4*9.84 > (0::real)"
      by simp

    have "measure_pmf.prob p
     {s. real (card_slice (\<lambda>w. H w s) (mstar - 3)) \<le>
        3 / 8 * \<mu> (mstar - 3)}
      \<le> 1 / (1 + (1 - 3 / 8)\<^sup>2 * \<mu> (mstar - 3))"
      apply(intro analysis_1_2[OF p ind mstar_3])
      by auto
    also have "... = 1 / (1 + (5 / 8)^2 * \<mu> (mstar-3))"
      by simp
    also have "... = 1 / (1 + 25 / 64 * \<mu> (mstar-3))"
      unfolding * by auto
    also have "... \<le> 1 / (1+ 25/64 * 4*pivot)"
      using **
      by (metis Groups.add_ac(2) add_sign_intros(3) divide_nonneg_nonneg frac_le mult_right_mono mult_zero_left of_nat_0_le_iff of_nat_numeral order_le_less pos_pivot zero_less_one)
    also have "... \<le> 1 / (1+ 25/64 * 4 * 4*9.84)"
      using *** ****
      by (smt (verit) frac_le)
    also have "... \<le> 1 / 62.5"
      by simp
    finally have *****: "measure_pmf.prob p
     {s. real (card_slice (\<lambda>w. H w s) (mstar - 3)) \<le> 3 / 8 * \<mu> (mstar - 3)} \<le> 1 / 62.5"
      by auto

    have "measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (T (mstar-3))
        = measure_pmf.prob p {s. real (card_slice (\<lambda>w. H w s) (mstar - 3)) < thresh}"
      unfolding T_def
      by auto
    also have "... \<le> measure_pmf.prob p
     {s. real (card_slice (\<lambda>w. H w s) (mstar - 3)) \<le> 3 / 8 * \<mu> (mstar - 3)}"
      using thresh2mu by (auto intro!: measure_pmf.finite_measure_mono)
    also have "... \<le> 1 / 62.5"
      using *****
      by auto
    finally have "measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (T (mstar-3)) \<le> 1 / 62.5" .
  }

  ultimately show ?thesis by auto
qed

(* Alternative Lem 2.1 in IJCAI'16 paper without bound on epsilon *)
lemma analysis_2_1':
  assumes p: "finite (set_pmf p)"
  assumes ind: "prob_space.k_universal (measure_pmf p) 2 H
    {\<alpha>::'a assg. dom \<alpha> = S}
    {\<alpha>::nat assg. dom \<alpha> = {0..<card S - 1}}"
  shows "
    measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (T (mstar-3))
      \<le> 1 / 10.84"
proof -
  have "1 + 1 / \<epsilon> > 0"
    by (simp add: \<epsilon> pos_add_strict)
  then have pos_pivot: "pivot > 0"
    unfolding pivot_def
    by simp

  have "mstar \<ge> 4 \<or> mstar < 4" by auto
  moreover {
    assume "mstar < 4"
    then have " measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (T (mstar-3))
      \<le> 1 / 10.84"
      by (auto simp add: T0_empty)
  }
  moreover {
    assume lo_mstar: "mstar \<ge> 4"

    have extend_mu3: "\<mu> (mstar-1) * 2^2 = \<mu> (mstar-3)"
      apply (subst shift_\<mu>)
      subgoal using lo_mstar semiring_norm(87) by linarith
      using diff_Suc_eq_diff_pred eval_nat_numeral(3) by presburger

    have "\<epsilon> / (1 + \<epsilon>) < 1"
      using \<epsilon> by auto
    then have ******: "1 + \<epsilon> / (1 + \<epsilon>) < 2"
      using \<epsilon> by auto
    have mu_mstar_3_gt_zero: "\<mu> (mstar - 3) / 4 > 0"
      using \<mu>_gt_zero by simp

    from mstar_prop(1)
    have "thresh < \<mu> (mstar - 1) * (1 + \<epsilon> / (1 + \<epsilon>))"
      by auto
    also have "... = \<mu> (mstar - 1) *2^2 / 4 * (1 + \<epsilon> / (1 + \<epsilon>))"
      by auto
    also have "... = \<mu> (mstar - 3) / 4 * (1 + \<epsilon> / (1 + \<epsilon>))"
      unfolding extend_mu3 by auto
    also have "... < \<mu> (mstar - 3) / 4 * 2"
      apply (intro mult_strict_left_mono)
      using ****** mu_mstar_3_gt_zero by auto
    also have "... = 1 / 2 * \<mu> (mstar - 3)"
      by auto
    finally have thresh2mu: "thresh < 1 / 2 * \<mu> (mstar - 3)" .

    have "1 + \<epsilon> / (1 + \<epsilon>) > 0"
      by (simp add: add_nonneg_pos \<epsilon>)
    then have "\<mu> (mstar-1) * 4 > 4*pivot"
      using mstar_prop(1) thresh
      by (smt (verit) nonzero_mult_div_cancel_right real_divide_pos_left)
    then have lo_mu_mstar_3: "\<mu> (mstar-3) > 4*pivot"
      using extend_mu3
      by simp

    have mstar_3: "mstar-3 \<le> card S - 1"
      using lo_mstar
      using diff_le_self dual_order.trans mstar_prop(3) by blast

    have *: "(1 / 2)^2 = ((1 / 4)::real)"
      by (auto simp add: field_simps)
    have **: " 1 + 1/4 * 4*pivot \<le> 1+ 1/4 * \<mu> (mstar - 3) "
      using lo_mu_mstar_3
      by auto

    have "(1 + 1/\<epsilon>)^2 > 1^2"
      by (simp add: \<epsilon>)
    then have ***: " 1 + 1/4 * 4*9.84 \<le> 1+ 1/4 * 4 *pivot"
      unfolding pivot_def by auto
    have ****: "1 + 1/4 * 4 * 9.84 > (0::real)"
      by simp

    have "measure_pmf.prob p
     {s. real (card_slice (\<lambda>w. H w s) (mstar - 3)) \<le>
        1 / 2 * \<mu> (mstar - 3)}
      \<le> 1 / (1 + (1 - 1 / 2)\<^sup>2 * \<mu> (mstar - 3))"
      apply(intro analysis_1_2[OF p ind mstar_3])
      by auto
    also have "... = 1 / (1 + 1 / 4 * \<mu> (mstar-3))"
      using * by force
    also have "... \<le> 1 / (1+ 1/4 * 4*pivot)"
      using **
      by (simp add: add_nonneg_pos frac_le pos_pivot)
    also have "... \<le> 1 / (1+ 1/4 * 4 *9.84)"
      using *** ****
      by (smt (verit) frac_le)
    also have "... \<le> 1 / 10.84"
      by simp
    finally have *****: "measure_pmf.prob p
     {s. real (card_slice (\<lambda>w. H w s) (mstar - 3)) \<le> 1/2 * \<mu> (mstar - 3)} \<le> 1 / 10.84" .

    have "measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (T (mstar-3))
        = measure_pmf.prob p {s. real (card_slice (\<lambda>w. H w s) (mstar - 3)) < thresh}"
      unfolding T_def
      by auto
    also have "... \<le> measure_pmf.prob p
     {s. real (card_slice (\<lambda>w. H w s) (mstar - 3)) \<le> 1 / 2 * \<mu> (mstar - 3)}"
      using thresh2mu by (auto intro!: measure_pmf.finite_measure_mono)
    also have "... \<le> 1 /  10.84"
      using *****
      by auto
    finally have "measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (T (mstar-3)) \<le> 1 /  10.84" .
  }

  ultimately show ?thesis by auto
qed

(* Lem 2.2 in IJCAI'16 paper *)
lemma analysis_2_2:
  assumes p: "finite (set_pmf p)"
  assumes ind: "prob_space.k_universal (measure_pmf p) 2 H
    {\<alpha>::'a assg. dom \<alpha> = S}
    {\<alpha>::nat assg. dom \<alpha> = {0..<card S - 1}}"
  shows "
    measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L (mstar-2)) \<le> 1 / 20.68"
proof -
  have epos: "1 + 1 / \<epsilon> > 0"
    by (simp add: \<epsilon> pos_add_strict)
  then have pos_pivot: "pivot > 0"
    unfolding pivot_def
    by simp

  have "mstar \<ge> 3 \<or> mstar < 3" by auto
  moreover {
    assume "mstar < 3"
    then have " measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L (mstar-2))
          \<le> 1 / 20.68"
      by (auto simp add: L0_empty)
  }
  moreover {
    assume lo_mstar: "mstar \<ge> 3"

    have extend_mu2: "\<mu> (mstar-1) * 2^1 = \<mu> (mstar-2)"
      apply (subst shift_\<mu>)
      subgoal using lo_mstar by linarith
      by (metis diff_diff_left one_add_one)

    have "1 + \<epsilon> / (1 + \<epsilon>) > 0"
      by (simp add: add_nonneg_pos \<epsilon>)
    then have "\<mu> (mstar-1) > pivot"
      using mstar_prop(1) thresh
      by (smt (verit) nonzero_mult_div_cancel_right real_divide_pos_left)
    then have lo_mu_mstar_2: "\<mu> (mstar-2) > 2*pivot"
      using extend_mu2
      by simp

    have mstar_2: "mstar-2 \<le> card S - 1"
      using lo_mstar
      using diff_le_self dual_order.trans mstar_prop(3) by blast

    have beta:"1/(1+\<epsilon>) \<le> (1::real)"
      using \<epsilon> by auto
    have pos: "(1 / (1 + 1/\<epsilon>))\<^sup>2 > 0"
      using epos by auto
    then have *: "1 + (1 / (1 + 1/\<epsilon>))\<^sup>2 * 2*pivot \<le> 1 + (1 / (1 + 1/\<epsilon>))\<^sup>2 * \<mu> (mstar - 2)"
      using lo_mu_mstar_2
      by auto

    have "1 - 1/(1+\<epsilon>) = 1 / (1 + 1/\<epsilon>)"
      by (smt (verit, ccfv_threshold) \<epsilon> conjugate_exponent_def conjugate_exponent_real(1))
    then have **: "(1 - 1/(1+\<epsilon>))^2 = (1 / (1 + 1/\<epsilon>))^2"
      by simp
    have ***: "1 + (1 / (1 + 1/\<epsilon>))\<^sup>2 * 2 * 9.84 * ( 1 + 1/\<epsilon> )^2
            = 1 + (1 / (1 + 1/\<epsilon>))\<^sup>2 * ( 1 + 1/\<epsilon> )^2 *  2 * 9.84"
      by (simp add: mult.commute)
    have ****: "(1 / (1 + 1/\<epsilon>))\<^sup>2 * ( 1 + 1/\<epsilon> )^2 = 1"
      using pos
      by (simp add: power_one_over)

    from analysis_1_2[OF p ind mstar_2 beta]
    have "measure_pmf.prob p
      {s. real (card_slice (\<lambda>w. H w s) (mstar - 2)) \<le> 1/(1+\<epsilon>) * \<mu> (mstar - 2)}
        \<le> 1 / (1 + (1 - 1/(1+\<epsilon>))\<^sup>2 * \<mu> (mstar - 2))"
      by auto
    also have "... = 1 / (1 + (1 / (1 + 1/\<epsilon>))\<^sup>2 * \<mu> (mstar - 2))"
      unfolding ** by auto
    also have "... \<le> 1 / (1 + (1 / (1 + 1/\<epsilon>))\<^sup>2 * 2 * pivot)"
      using *
      by (smt (verit) epos divide_pos_pos frac_le pivot_def pos_prod_le zero_less_power)
    also have "... = 1 / (1 + (1 / (1 + 1/\<epsilon>))\<^sup>2 * 2 * 9.84 * ( 1 + 1/\<epsilon> )^2)"
      unfolding pivot_def by auto
    also have "... = 1 / 20.68"
      unfolding *** **** by auto
    finally have *****: "measure_pmf.prob p
     {s. real (card_slice (\<lambda>w. H w s) (mstar - 2)) \<le> 1/(1+\<epsilon>) * \<mu> (mstar - 2)} \<le> 1 / 20.68" .

    have "measure_pmf.prob p
     {s. real (card_slice (\<lambda>w. H w s) (mstar - 2)) < 1/(1+\<epsilon>) * \<mu> (mstar - 2)}
        \<le> measure_pmf.prob p {s. real (card_slice (\<lambda>w. H w s) (mstar - 2)) \<le> 1/(1+\<epsilon>) * \<mu> (mstar - 2)}"
      by (auto intro!: measure_pmf.finite_measure_mono)
    then have ******: "measure_pmf.prob p
     {s. real (card_slice (\<lambda>w. H w s) (mstar - 2)) < 1/(1+\<epsilon>) * \<mu> (mstar - 2)}
          \<le> 1 / 20.68"
      using ***** by auto

    have "measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L (mstar-2))
        = measure_pmf.prob p
     {s. real (card_slice (\<lambda>w. H w s) (mstar - 2)) < 1/(1+\<epsilon>) * \<mu> (mstar - 2)}"
      unfolding L_def
      by auto
    also have "... \<le> 1 / 20.68"
      using ****** by auto
    finally have "measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L (mstar-2)) \<le> 1 / 20.68" .
  }

  ultimately show ?thesis by auto
qed

(* Lem 2.3 in IJCAI'16 paper *)
lemma analysis_2_3:
  assumes p: "finite (set_pmf p)"
  assumes ind: "prob_space.k_universal (measure_pmf p) 2 H
    {\<alpha>::'a assg. dom \<alpha> = S}
    {\<alpha>::nat assg. dom \<alpha> = {0..<card S - 1}}"
  shows "
    measure_pmf.prob
    (map_pmf (\<lambda>s w. H w s) p) (L (mstar-1)) \<le> 1 / 10.84"
proof -
  have epos: "1 + 1 / \<epsilon> > 0"
    by (simp add: \<epsilon> pos_add_strict)
  then have pos_pivot: "pivot > 0"
    unfolding pivot_def
    by simp

  have "mstar \<ge> 2 \<or> mstar < 2" by auto
  moreover {
    assume "mstar < 2"
    then have " measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L (mstar-2))
          \<le> 1 / 10.84"
      by (auto simp add: L0_empty)
  }
  moreover {
    assume lo_mstar: "mstar \<ge> 2"

    have "1 + \<epsilon> / (1 + \<epsilon>) > 0"
      by (simp add: add_nonneg_pos \<epsilon>)
    then have lo_mu_mstar_1: "\<mu> (mstar-1) > pivot"
      using mstar_prop(1) using thresh
      by (smt (verit) nonzero_mult_div_cancel_right real_divide_pos_left)

    have mstar_1: "mstar-1 \<le> card S - 1"
      using lo_mstar diff_le_self dual_order.trans mstar_prop(3) by blast

    have beta: "1/(1+\<epsilon>) \<le> (1::real)"
      using \<epsilon> by auto
    have "(1 / (1 + 1/\<epsilon>))\<^sup>2 > 0"
      using epos by auto
    then have *: "1 + (1 / (1 + 1/\<epsilon>))\<^sup>2 * pivot \<le> 1 + (1 / (1 + 1/\<epsilon>))\<^sup>2 * \<mu> (mstar - 1)"
      using lo_mu_mstar_1
      by auto

    have "1 - 1/(1+\<epsilon>) = 1 / (1 + 1/\<epsilon>)"
      by (smt (verit, ccfv_threshold) \<epsilon> conjugate_exponent_def conjugate_exponent_real(1))
    then have **: "(1 - 1/(1+\<epsilon>))^2 = (1 / (1 + 1/\<epsilon>))^2"
      by simp
    have ***: "1 + (1 / (1 + 1/\<epsilon>))\<^sup>2 * 9.84 * ( 1 + 1/\<epsilon> )^2
            = 1 + (1 / (1 + 1/\<epsilon>))\<^sup>2 * ( 1 + 1/\<epsilon> )^2 * 9.84"
      by (simp add: mult.commute)
    have ****: "(1 / (1 + 1/\<epsilon>))\<^sup>2 * ( 1 + 1/\<epsilon> )^2 = 1"
      by (metis (mono_tags, opaque_lifting) \<open>0 < 1 + 1 / \<epsilon>\<close> div_by_1 divide_divide_eq_right divide_self_if less_irrefl mult.commute power_mult_distrib power_one)

    from analysis_1_2[OF p ind mstar_1 beta]
    have "measure_pmf.prob p
     {s. real (card_slice (\<lambda>w. H w s) (mstar - 1)) \<le> 1/(1+\<epsilon>) * \<mu> (mstar - 1)}
    \<le> 1 / (1 + (1 - 1/(1+\<epsilon>))\<^sup>2 * \<mu> (mstar - 1))"
      by auto
    moreover have "... = 1 / (1 + (1 / (1 + 1/\<epsilon>))\<^sup>2 * \<mu> (mstar - 1))"
      unfolding ** by auto
    moreover have "... \<le> 1 / (1 + (1 / (1 + 1/\<epsilon>))\<^sup>2 * pivot)"
      using *
      by (smt (verit) \<open>0 < (1 / (1 + 1 / \<epsilon>))\<^sup>2\<close> frac_le pos_pivot zero_le_mult_iff)
    moreover have "... = 1 / (1 + (1 / (1 + 1/\<epsilon>))\<^sup>2 * 9.84 * ( 1 + 1/\<epsilon> )^2)"
      unfolding pivot_def by auto
    moreover have "... = 1 / (1 + (1 / (1 + 1/\<epsilon>))\<^sup>2 * ( 1 + 1/\<epsilon> )^2 * 9.84)"
      unfolding *** by auto
    moreover have "... = 1 / (1 + 9.84)"
      unfolding **** by auto
    moreover have "... = 1 / 10.84"
      by auto
    ultimately have *****: "measure_pmf.prob p
     {s. real (card_slice (\<lambda>w. H w s) (mstar - 1)) \<le> 1/(1+\<epsilon>) * \<mu> (mstar - 1)} \<le> 1 / 10.84"
      by linarith
    have "measure_pmf.prob p
      {s. real (card_slice (\<lambda>w. H w s) (mstar - 1)) < 1/(1+\<epsilon>) * \<mu> (mstar - 1)}
        \<le> measure_pmf.prob p
     {s. real (card_slice (\<lambda>w. H w s) (mstar - 1)) \<le> 1/(1+\<epsilon>) * \<mu> (mstar - 1)}"
      by (auto intro!: measure_pmf.finite_measure_mono)
    then have ******: "measure_pmf.prob p
      {s. real (card_slice (\<lambda>w. H w s) (mstar - 1)) < 1/(1+\<epsilon>) * \<mu> (mstar - 1)}
          \<le> 1 / 10.84"
      using ***** by auto

    have "measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L (mstar-1))
        = measure_pmf.prob p
     {s. real (card_slice (\<lambda>w. H w s) (mstar - 1)) < 1/(1+\<epsilon>) * \<mu> (mstar - 1)}"
      unfolding L_def
      by auto
    moreover have "... \<le> 1 / 10.84"
      using ****** by auto
    ultimately have "measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L (mstar-1)) \<le> 1 / 10.84"
      by auto
  }

  ultimately show ?thesis by auto
qed

(* Lem 2.4 in IJCAI'16 paper *)
lemma analysis_2_4:
  assumes p: "finite (set_pmf p)"
  assumes ind: "prob_space.k_universal (measure_pmf p) 2 H
    {\<alpha>::'a assg. dom \<alpha> = S}
    {\<alpha>::nat assg. dom \<alpha> = {0..<card S - 1}}"
  shows "
    measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L mstar \<union> U mstar) \<le> 1 / 4.92"
proof -
  have "1 + 1 / \<epsilon> > 0"
    by (simp add: \<epsilon> pos_add_strict)
  then have pos_pivot: "pivot > 0"
    unfolding pivot_def
    by simp

  have "mstar \<ge> 1 \<or> mstar < 1" by auto
  moreover {
    assume "mstar < 1"
    have LU0_empty: "L mstar \<union> U mstar = {}"
      using L0_empty U0_empty
      using \<open>mstar < 1\<close> less_one by auto
    then have "measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L mstar \<union> U mstar)
          \<le> 1 / 4.92"
      by auto
  }
  moreover {
    assume lo_mstar: "mstar \<ge> 1"
    have extend_mu: "\<mu> mstar * 2^1 = \<mu> (mstar-1)"
      using lo_mstar
      apply (subst shift_\<mu>)
      by auto

    have "1 + \<epsilon> / (1 + \<epsilon>) > 0"
      by (simp add: add_nonneg_pos \<epsilon>)
    then have "\<mu> (mstar-1) > pivot"
      using mstar_prop(1) thresh
      by (smt (verit) nonzero_mult_div_cancel_right real_divide_pos_left)
    then have lo_mu_star: "\<mu> mstar > pivot / 2"
      using extend_mu
      by auto

    have mstar: "mstar \<le> card S - 1"
      using lo_mstar
      using diff_le_self dual_order.trans mstar_prop(3) by blast

    have "\<epsilon>*(1+1/\<epsilon>) = 1+\<epsilon>"
      by (smt (verit) \<epsilon> add_divide_eq_if_simps(1) divide_cancel_right divide_self_if nonzero_mult_div_cancel_left)
    then have *: "9.84 * \<epsilon>^2*(1+1/\<epsilon>)^2 / 2 = 9.84 * (1+\<epsilon>)^2 / 2"
      by (metis (mono_tags, opaque_lifting) more_arith_simps(11) power_mult_distrib)

    have "\<epsilon>^2 * \<mu> mstar \<ge> \<epsilon>^2 * pivot / 2"
      using lo_mu_star
      by (metis less_eq_real_def ordered_comm_semiring_class.comm_mult_left_mono times_divide_eq_right zero_le_power2)
    then have **: "\<epsilon>^2 * \<mu> mstar \<ge> 9.84 * (1+\<epsilon>)^2 / 2"
      unfolding pivot_def using * by auto

    from analysis_1_1[OF p ind mstar]
    have "measure_pmf.prob p
      {s. \<bar> card_slice ((\<lambda>w. H w s)) mstar - \<mu> mstar \<bar> \<ge> \<epsilon> / (1 + \<epsilon>) * \<mu> mstar }
          \<le> (1 + \<epsilon>)^2 / (\<epsilon>^2 * \<mu> mstar)"
      by auto
    also have "... \<le> (1 + \<epsilon>)^2 / (9.84 * (1+\<epsilon>)^2 / 2)"
      using **
      by (smt (verit) divide_cancel_left divide_le_0_iff frac_le pos_prod_le power2_less_0 zero_eq_power2)
    also have "... = (1 + \<epsilon>)^2 / (4.92 * (1+\<epsilon>)^2)"
      by simp
    also have "... = 1 / 4.92"
      using \<epsilon> by simp
    finally have *******: "measure_pmf.prob p
      {s. \<bar> card_slice ((\<lambda>w. H w s)) mstar - \<mu> mstar \<bar> \<ge> \<epsilon> / (1 + \<epsilon>) * \<mu> mstar }
          \<le> 1 / 4.92" .

    have "\<mu> mstar / (1 + \<epsilon>) - \<mu> mstar = \<mu> mstar * (1 / (1+\<epsilon>) - 1)"
      by (simp add: right_diff_distrib')
    also have "... = \<mu> mstar * (- \<epsilon> / (1+\<epsilon>))"
      by (smt (verit) \<epsilon> add_divide_distrib div_self minus_divide_left)
    finally have ***: "\<mu> mstar / (1 + \<epsilon>) - \<mu> mstar = \<mu> mstar * (- \<epsilon> / (1+\<epsilon>))" .

    have "{h. real (card_slice h mstar) \<le> \<mu> mstar / (1 + \<epsilon>)}
        = {h. real (card_slice h mstar) - \<mu> mstar \<le> \<mu> mstar / (1 + \<epsilon>) - \<mu> mstar}"
      by auto
    also have "... = {h. real (card_slice h mstar) - \<mu> mstar \<le> \<mu> mstar * (- \<epsilon> / (1+\<epsilon>))}"
      using *** by auto
    finally have ****: "
      {h. real (card_slice h mstar) \<le> \<mu> mstar / (1 + \<epsilon>)} =
      {h. real (card_slice h mstar) - \<mu> mstar \<le> \<mu> mstar * (- \<epsilon> / (1+\<epsilon>))}" .

    have "L mstar
            = {h. real (card_slice h mstar) < \<mu> mstar / (1 + \<epsilon>)}"
      unfolding L_def by auto
    also have "...\<subseteq> {h. real (card_slice h mstar) \<le> \<mu> mstar / (1 + \<epsilon>)}"
      by auto
    also have "... = {h. real (card_slice h mstar) - \<mu> mstar \<le> \<mu> mstar * (- \<epsilon> / (1+\<epsilon>))}"
      unfolding **** by auto
    finally have extend_L: "L mstar \<subseteq> {h. real (card_slice h mstar) - \<mu> mstar \<le> \<mu> mstar * (- \<epsilon> / (1+\<epsilon>))}" .

    have *****: "\<mu> mstar * (1 + \<epsilon> / (1+\<epsilon>)) - \<mu> mstar = \<mu> mstar * (\<epsilon> / (1+\<epsilon>))"
      by (metis (no_types, opaque_lifting) add.commute diff_add_cancel group_cancel.sub1 mult.right_neutral right_diff_distrib')

    have ******: "U mstar = {h. real (card_slice h mstar) \<ge> \<mu> mstar * (1 + \<epsilon> / (1+\<epsilon>))}"
      unfolding U_def by auto
    have "{h. real (card_slice h mstar) \<ge> \<mu> mstar * (1 + \<epsilon> / (1+\<epsilon>))}
          = {h. real (card_slice h mstar) - \<mu> mstar \<ge> \<mu> mstar * (1 + \<epsilon> / (1+\<epsilon>)) - \<mu> mstar}"
      by auto
    also have "... = {h. real (card_slice h mstar) - \<mu> mstar \<ge> \<mu> mstar * (\<epsilon> / (1+\<epsilon>))}"
      unfolding ***** by auto
    finally have extend_U: "U mstar = {h. real (card_slice h mstar) - \<mu> mstar \<ge> \<mu> mstar * (\<epsilon> / (1+\<epsilon>))}"
      using ****** by auto

    have "L mstar \<union> U mstar \<subseteq>
                    {h. real (card_slice h mstar) - \<mu> mstar \<le> \<mu> mstar * (- \<epsilon> / (1+\<epsilon>))}
                  \<union> {h. real (card_slice h mstar) - \<mu> mstar \<ge> \<mu> mstar * (\<epsilon> / (1+\<epsilon>))}"
      unfolding extend_U
      using extend_L
      by auto
    also have "... = {h. \<bar> real (card_slice h mstar) - \<mu> mstar \<bar> \<ge> \<mu> mstar * (\<epsilon> / (1+\<epsilon>))}"
      by auto
    finally have extend_LU: "L mstar \<union> U mstar \<subseteq> {h. \<bar> real (card_slice h mstar) - \<mu> mstar \<bar> \<ge> \<mu> mstar * (\<epsilon> / (1+\<epsilon>))}" .

    have "measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L mstar \<union> U mstar)
        \<le> measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) {h. \<bar> real (card_slice h mstar) - \<mu> mstar \<bar> \<ge> \<mu> mstar * (\<epsilon> / (1+\<epsilon>))}"
      using extend_LU
      by (auto intro!: measure_pmf.finite_measure_mono)
    also have "... = measure_pmf.prob p
      {s. \<bar> real (card_slice (\<lambda>w. H w s) mstar) - \<mu> mstar \<bar> \<ge> \<epsilon> / (1 + \<epsilon>) * \<mu> mstar }"
      by (simp add: mult.commute)
    also have "... \<le> 1 / 4.92"
      using ******* by auto
    finally have "measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L mstar \<union> U mstar) \<le> 1 / 4.92" .
  }

  ultimately show ?thesis by auto
qed

(* Lem 3 in IJCAI'16 paper *)
lemma analysis_3:
  assumes p: "finite (set_pmf p)"
  assumes ind: "prob_space.k_universal (measure_pmf p) 2 H
    {\<alpha>::'a assg. dom \<alpha> = S}
    {\<alpha>::nat assg. dom \<alpha> = {0..<card S - 1}}"
  assumes \<epsilon>_up: "\<epsilon> \<le> 1"
  shows "
    measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p)
    approxcore_fail \<le> 0.36"
proof -
  have "measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) approxcore_fail
    \<le> measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p)
   (T (mstar-3) \<union>
    L (mstar-2) \<union>
    L (mstar-1) \<union>
    (L mstar \<union> U mstar))"
    using failure_bound
    by (auto intro!: measure_pmf.finite_measure_mono)

  moreover have "... \<le>
      measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (T (mstar-3) \<union> L (mstar-2) \<union> L (mstar-1))
    + measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L mstar \<union> U mstar)"
    by (auto intro!: measure_pmf.finite_measure_subadditive)
  moreover have "... \<le>
      measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (T (mstar-3) \<union> L (mstar-2))
    + measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L (mstar-1))
    + measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L mstar \<union> U mstar)"
    by (auto intro!: measure_pmf.finite_measure_subadditive)
  moreover have "... \<le>
      measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (T (mstar-3))
    + measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L (mstar-2))
    + measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L (mstar-1))
    + measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L mstar \<union> U mstar)"
    by (auto intro!: measure_pmf.finite_measure_subadditive)
  moreover have "... \<le> 1/62.5 + 1/20.68 + 1/10.84 + 1/4.92"
    using analysis_2_1[OF p ind \<epsilon>_up]
    using analysis_2_2[OF p ind]
    using analysis_2_3[OF p ind]
    using analysis_2_4[OF p ind]
    by auto
  ultimately show ?thesis by force
qed

(* Alternative Lem 3 in IJCAI'16 paper without bound on epsilon *)
lemma analysis_3':
  assumes p: "finite (set_pmf p)"
  assumes ind: "prob_space.k_universal (measure_pmf p) 2 H
    {\<alpha>::'a assg. dom \<alpha> = S}
    {\<alpha>::nat assg. dom \<alpha> = {0..<card S - 1}}"
  shows "
    measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p)
    approxcore_fail \<le> 0.44"
proof -
  have "measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) approxcore_fail
    \<le> measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p)
   (T (mstar-3) \<union>
    L (mstar-2) \<union>
    L (mstar-1) \<union>
    (L mstar \<union> U mstar))"
    using failure_bound
    by (auto intro!: measure_pmf.finite_measure_mono)

  moreover have "... \<le>
      measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (T (mstar-3) \<union> L (mstar-2) \<union> L (mstar-1))
    + measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L mstar \<union> U mstar)"
    by (auto intro!: measure_pmf.finite_measure_subadditive)
  moreover have "... \<le>
      measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (T (mstar-3) \<union> L (mstar-2))
    + measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L (mstar-1))
    + measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L mstar \<union> U mstar)"
    by (auto intro!: measure_pmf.finite_measure_subadditive)
  moreover have "... \<le>
      measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (T (mstar-3))
    + measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L (mstar-2))
    + measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L (mstar-1))
    + measure_pmf.prob (map_pmf (\<lambda>s w. H w s) p) (L mstar \<union> U mstar)"
    by (auto intro!: measure_pmf.finite_measure_subadditive)
  moreover have "... \<le> 1/10.84 + 1/20.68 + 1/10.84 + 1/4.92"
    using analysis_2_1'[OF p ind]
    using analysis_2_2[OF p ind]
    using analysis_2_3[OF p ind]
    using analysis_2_4[OF p ind]
    by auto
  ultimately show ?thesis by auto
qed
end

end

end
