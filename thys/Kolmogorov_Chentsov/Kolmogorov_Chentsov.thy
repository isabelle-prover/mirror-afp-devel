(* Title:      Kolmogorov_Chentsov/Kolmogorov_Chentsov.thy
   Author:     Christian Pardillo Laursen, University of York
*)

section "The Kolomgorov-Chentsov theorem"

theory Kolmogorov_Chentsov
  imports Stochastic_Processes Holder_Continuous Dyadic_Interval Measure_Convergence
begin

subsection "Supporting lemmas"

text \<open> The main contribution of this file is the Kolmogorov-Chentsov theorem: given a stochastic
  process that satisfies some continuity properties, we can construct a H{\"o}lder continuous modification.
  We first prove some auxiliary lemmas before moving on to the main construction. \<close>

text \<open> Klenke 5.11: Markov inequality. Compare with @{thm nn_integral_Markov_inequality} \<close>

lemma nn_integral_Markov_inequality_extended:
  fixes f :: "real \<Rightarrow> ennreal" and \<epsilon> :: real and X :: "'a \<Rightarrow> real"
  assumes mono: "mono_on (range X \<union> {0<..}) f"
    and finite: "\<And>x. f x < \<infinity>"
    and e: "\<epsilon> > 0" "f \<epsilon> > 0"
    and [measurable]: "X \<in> borel_measurable M"
  shows "emeasure M {p \<in> space M. (X p) \<ge> \<epsilon>} \<le> (\<integral>\<^sup>+ x. f (X x) \<partial>M) / f \<epsilon>"
proof -
  have f_eq: "f = (\<lambda>x. ennreal (enn2real (f x)))"
    using finite by simp
  have "mono_on (range X) (\<lambda>x. enn2real (f x))"
    apply (intro mono_onI)
    using mono[THEN mono_onD] finite by (simp add: enn2real_mono)
  then have "f \<in> borel_measurable (restrict_space borel (range X))"
    apply (subst f_eq)
    apply (intro measurable_compose[where f="\<lambda>x. enn2real (f x)" and g=ennreal])
    using borel_measurable_mono_on_fnc apply blast
    apply simp
    done
  then have "(\<lambda>x. f (X x)) \<in> borel_measurable M"
    apply (intro measurable_compose[where g=f and f=X and N="restrict_space borel (range X)"])
     apply (simp_all add: measurable_restrict_space2)
    done
  then have "{x \<in> space M. f (X x) \<ge> f \<epsilon>} \<in> sets M"
    by measurable
  then have "f \<epsilon> * emeasure M {x \<in> space M. X x \<ge> \<epsilon>} \<le> (\<integral>\<^sup>+x\<in>{x \<in> space M. f \<epsilon> \<le> f (X x)}. f \<epsilon> \<partial>M)"
    apply (simp add: nn_integral_cmult_indicator)
    using e mono_onD[OF mono] zero_le apply (blast intro: mult_left_mono emeasure_mono)
    done
  also have "... \<le> (\<integral>\<^sup>+x\<in>{x \<in> space M. f \<epsilon> \<le> f (X x)}. f (X x) \<partial>M)"
    apply (rule nn_integral_mono)
    subgoal for x
      apply (cases "f \<epsilon> \<le> f (X x)")
      using ennreal_leI by auto
    done
  also have "... \<le> \<integral>\<^sup>+ x. f (X x) \<partial>M"
    by (simp add: nn_integral_mono indicator_def)
  finally have "emeasure M {p \<in> space M. \<epsilon> \<le> X p} * f \<epsilon> / f \<epsilon> \<le> (\<integral>\<^sup>+ x. f (X x) \<partial>M) / f \<epsilon>"
    by (simp add: divide_right_mono_ennreal field_simps)
  then show ?thesis
    using mult_divide_eq_ennreal finite[of "\<epsilon>"] e(2) by simp
qed

lemma nn_integral_Markov_inequality_extended_rnv:
  fixes f :: "real \<Rightarrow> real" and \<epsilon> :: real and X :: "'a \<Rightarrow> 'b :: real_normed_vector"
  assumes [measurable]: "X \<in> borel_measurable M"
    and mono: "mono_on {0..} f"
    and e: "\<epsilon> > 0" "f \<epsilon> > 0"
  shows "emeasure M {p \<in> space M. norm (X p) \<ge> \<epsilon>} \<le> (\<integral>\<^sup>+ x. f (norm (X x)) \<partial>M) / f \<epsilon>"
  apply (rule nn_integral_Markov_inequality_extended)
  using mono ennreal_leI unfolding mono_on_def apply force
     apply (simp_all add: e)
  done

subsection "Kolmogorov-Chentsov"
text \<open> Klenke theorem 21.6 - Kolmorogov-Chentsov \<close>

locale Kolmogorov_Chentsov = 
  fixes X :: "(real, 'a, 'b :: polish_space) stochastic_process"
    and a b C \<gamma> :: real
  assumes index[simp]: "proc_index X = {0..}"
    and target_borel[simp]: "proc_target X = borel"
    and gt_0: "a > 0" "b > 0" "C > 0"
    and b_leq_a: "b \<le> a"
    and gamma: "\<gamma> \<in> {0<..<b/a}"
    and expectation: "\<And>s t. \<lbrakk>s \<ge> 0; t \<ge> 0\<rbrakk> \<Longrightarrow>
          (\<integral>\<^sup>+ x. dist (X t x) (X s x) powr a \<partial>proc_source X) \<le> C * dist t s powr (1+b)"
begin

lemma gamma_0_1[simp]:"\<gamma> \<in> {0<..1}"
  using gt_0 b_leq_a gamma
  by (metis divide_less_eq_1_pos divide_self greaterThanAtMost_iff 
      greaterThanLessThan_iff nless_le order_less_trans)

lemma gamma_gt_0[simp]: "\<gamma> > 0"
  using gamma greaterThanLessThan_iff by blast

lemma gamma_le_1[simp]: "\<gamma> \<le> 1"
  using gamma_0_1 by auto

abbreviation "source \<equiv> proc_source X"

lemma X_borel_measurable[measurable]: "X t \<in> borel_measurable source" for t
  by (metis random_process target_borel)

lemma markov: "\<P>(x in source. \<epsilon> \<le> dist (X t x) (X s x)) \<le> (C * dist t s powr (1 + b)) / \<epsilon> powr a"
  if "s \<ge> 0" "t \<ge> 0" "\<epsilon> > 0" for s t \<epsilon>
proof -
  let ?inc = "\<lambda>x. dist (X t x) (X s x) powr a"
  have "emeasure source {x \<in> space source. \<epsilon> \<le> dist (X t x) (X s x)}
   \<le> integral\<^sup>N source ?inc / \<epsilon> powr a"
    apply (rule nn_integral_Markov_inequality_extended)
    using that(1,2) apply measurable
    subgoal using gt_0(1) imageE powr_mono2 by (auto intro: mono_onI)
    using that apply simp_all
    done
  also have "... \<le> (C * dist t s powr (1 + b)) / ennreal (\<epsilon> powr a)"
    apply (rule divide_right_mono_ennreal)
    using expectation[OF that(1,2)] ennreal_leI by simp
  finally have "emeasure source {x \<in> space source. \<epsilon> \<le> dist (X t x) (X s x)}
     \<le> (C * dist t s powr (1 + b)) / \<epsilon> powr a"
    using that(3) divide_ennreal gt_0(3) by simp
  moreover have "C * dist t s powr (1 + b) / \<epsilon> powr a \<ge> 0"
    using gt_0(3) by auto
  ultimately show ?thesis
    by (simp add: proc_source.emeasure_eq_measure)
qed

lemma conv_in_prob:
  assumes "t \<ge> 0"
  shows "tendsto_measure (proc_source X) X (X t) (at t within {0..})"
proof -
  {
    fix p \<epsilon> :: real assume "0 < p" "0 < \<epsilon>"
    let ?q = "(p * \<epsilon> powr a / C) powr (1/(1+b))"
    have "0 < ?q"
      using \<open>0 < p\<close> gt_0(3) \<open>0 < \<epsilon>\<close> by simp
    have p_eq: "p = (C * ?q powr (1 + b)) / \<epsilon> powr a"
      using gt_0 \<open>0 < ?q\<close> \<open>0 < p\<close> by (simp add: field_simps powr_powr)
    have "0 < dist r t \<and> dist r t < ?q \<longrightarrow> dist \<P>(x in source. \<epsilon> \<le> dist (X t x) (X r x)) 0 \<le> p"
      if "r \<in> {0..}" for r
    proof safe
      assume "0 < dist r t" "dist r t < ?q"
      have "0 \<le> r"
        using that by auto
      from \<open>dist r t < ?q\<close> have "C * dist r t powr (1 + b) / \<epsilon> powr a \<le> p"
        apply (subst p_eq)
        using gt_0(2) gt_0(3) apply (simp add: divide_le_cancel powr_mono2)
        done
      then show "dist \<P>(x in source. \<epsilon> \<le> dist (process X t x) (process X r x)) 0 \<le> p"
        using markov[OF \<open>0 \<le> r\<close> assms \<open>0 < \<epsilon>\<close>] by (simp add: dist_commute)
    qed
    then have "\<exists>d>0. \<forall>r\<in>{0..}. 0 < dist r t \<and> dist r t < d \<longrightarrow>
                dist \<P>(x in source. \<epsilon> \<le> dist (X r x) (X t x)) 0 \<le> p"
      apply (intro exI[where x="?q"])
      apply (subst(3) dist_commute)
      using \<open>0 < p\<close> gt_0(3) \<open>0 < \<epsilon>\<close> dist_commute by fastforce
  } then show ?thesis
    by (simp add: finite_measure.tendsto_measure_leq, safe, intro Lim_withinI)
qed

lemma conv_in_prob_finite:
  assumes "t \<ge> 0"
  shows "tendsto_measure (proc_source X) X (X t) (at t within {0..T})"
proof -
  have "at t within {0..T} \<le> at t within {0..}"
    by (simp add: at_le)
  then show ?thesis
    apply (rule tendsto_measure_mono)
    using assms by (rule conv_in_prob)
qed

lemma incr: "\<P>(x in source. 2 powr (- \<gamma> * n) \<le> dist (X ((k - 1) * 2 powr - n) x) (X (k * 2 powr - n) x))
         \<le> C * 2 powr (-n * (1+b-a*\<gamma>))"
  if "k \<ge> 1" "n \<ge> 0" for k n
proof -
  have "\<P>(x in source. 2 powr (- \<gamma> * n) \<le> dist (X ((k - 1) * 2 powr - n) x) (X (k * 2 powr - n) x))
       \<le> C * dist ((k - 1) * 2 powr - n) (k * 2 powr - n) powr (1 + b) / (2 powr (- \<gamma> * n)) powr a"
    using that by (auto intro: markov)
  also have "... = C * 2 powr (- n - b * n) / 2 powr (- \<gamma> * n * a)"
    by (auto simp: dist_real_def powr_powr field_simps)
  also have "... =  C * 2 powr (-n * (1+b-a*\<gamma>))"
    by (simp add: field_simps powr_add[symmetric])
  finally show ?thesis .
qed

end

text \<open> In order to construct the modification of $X$, it suffices to construct a modification of $X$ 
  on $\{0..T\}$ for all finite $T$, from which we construct the modification on $\{0..\}$ via a countable
  union. \<close>

locale Kolmogorov_Chentsov_finite = Kolmogorov_Chentsov +
  fixes T :: real
  assumes zero_le_T: "0 < T"
begin

text \<open> $A_n$ will characterise the set of states with increments that exceed the bounds required for
  H{\"o}lder continuity. As $n \longrightarrow \infty$, this approaches the set of states for which $X$ is not
  H{\"o}lder continuous. We define $N$ as this limit, and show that $N$ is a null set. On $\omega \in \Omega - N$,
  we show that $X(\omega)$ is H{\"o}lder continuous (and therefore uniformly continuious) on the dyadic
   rationals, and construct a modification by taking the continuous extension on the reals. \<close>

definition "A \<equiv> \<lambda>n. if 2 ^ n * T < 1 then space source else 
  {x \<in> space source. 
    Max {dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x)
       | k. k \<in> {1..\<lfloor>2^n * T\<rfloor>}} \<ge> 2 powr (-\<gamma> * real n)}"

abbreviation "B \<equiv> \<lambda>n. (\<Union>m. A (m + n))"

abbreviation "N \<equiv> \<Inter>(range B)"

lemma A_geq: "2 ^ n * T \<ge> 1 \<Longrightarrow> A n = {x \<in> space source. 
    Max {dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x)
   | k. k \<in> {1..\<lfloor>2^n * T\<rfloor>}} \<ge> 2 powr (-\<gamma> * real n)}" for n
  by (simp add: A_def)

lemma A_measurable[measurable]: "A n \<in> sets source"
  unfolding A_def apply (cases "2 ^ n * T < 1")
   apply simp
  apply (simp only: if_False)
  apply measurable
  done

lemma emeasure_A_leq:
  fixes n :: nat
  assumes [simp]: "2^n * T \<ge> 1"
  shows "emeasure source (A n) \<le> C * T * 2 powr (- n * (b - a * \<gamma>))"
proof -
  have nonempty: "{1..\<lfloor>2^n * T\<rfloor>} \<noteq> {}"
    using assms by fastforce
  have finite: "finite {1..\<lfloor>2^n * T\<rfloor>}"
    by simp
  have "emeasure source (A n) \<le> emeasure source (\<Union>k \<in> {1..\<lfloor>2^n * T\<rfloor>}.
    {x\<in>space source. dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x) \<ge> 2 powr (- \<gamma> * real n)})"
    (is "emeasure source (A n) \<le> emeasure source ?R")
  proof (rule emeasure_mono, intro subsetI)
    fix x assume *: "x \<in> A n"
    from * have in_space: "x \<in> space source"
      using A_measurable sets.sets_into_space by blast
    from * have "2 powr (- \<gamma> * real n) \<le> Max {dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x) |k. k \<in> {1..\<lfloor>2 ^ n * T\<rfloor>}}"
      using A_geq assms by blast
    then have "\<exists>k \<in> {1..\<lfloor>2 ^ n * T\<rfloor>}. 2 powr (- \<gamma> * real n) \<le> dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x)"
      apply (simp only: setcompr_eq_image)
      apply (rule Max_finite_image_ex[where P="\<lambda>x. 2 powr (- \<gamma> * real n) \<le> x", OF finite nonempty])
      apply (metis Collect_mem_eq)
      done
    then show "x \<in> ?R"
      using in_space by simp
  next
    show "?R \<in> sets source"
      by measurable
  qed
  also have "... \<le> (\<Sum>k\<in>{1..\<lfloor>2^n * T\<rfloor>}. emeasure source 
  {x\<in>space source. dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x) \<ge> 2 powr (- \<gamma> * real n)})"
    apply (rule emeasure_subadditive_finite)
     apply blast
    apply (subst image_subset_iff)
    apply (intro ballI)
    apply measurable
    done
  also have "... \<le> C * 2 powr (- n * (1 + b - a * \<gamma>)) * (card {1..\<lfloor>2 ^ n * T\<rfloor>})"
  proof -
    {
      fix k assume "k \<in> {1..\<lfloor>2 ^ n * T\<rfloor>}"
      then have "real_of_int k \<ge> 1"
        by presburger
      then have "\<P>(x in source. 2 powr (- \<gamma> * real n) \<le> dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x))
               \<le> C * 2 powr (-(real n) * (1+b-a*\<gamma>))"
        using incr gamma by force
    } note X = this
    then have "sum (\<lambda>k. \<P>(x in source. 2 powr (- \<gamma> * real n) \<le> dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x))) 
                      {1..\<lfloor>2 ^ n * T\<rfloor>} \<le> of_nat (card {1..\<lfloor>2 ^ n * T\<rfloor>}) * (C * 2 powr (-(real n) * (1+b-a*\<gamma>)))"
      by (fact sum_bounded_above)
    then show ?thesis
      using ennreal_leI by (auto simp: proc_source.emeasure_eq_measure mult.commute)
  qed
  also have "... \<le> C * 2 powr (- n * (1 + b - a * \<gamma>)) * \<lfloor>2 ^ n * T\<rfloor>"
    using nonempty zle_iff_zadd by force
  also have "... \<le> C * 2 powr (- n * (1+b - a * \<gamma>)) * 2^n * T"
    by (simp add:ennreal_leI gt_0(3))
  also have "... = C * 1/(2^n) * 2 powr (- n * (b - a * \<gamma>)) * 2^n * T"
    apply (intro ennreal_cong)
    apply (simp add: scale_left_imp_eq field_simps)
    by (smt (verit) powr_add powr_realpow)
  also have "... = C * T * 2 powr (- n * (b - a * \<gamma>))"
    by (simp add: field_simps)
  finally show ?thesis .
qed

lemma measure_A_leq: 
  assumes "2^n * T \<ge> 1"
  shows "measure source (A n) \<le> C * T * 2 powr (- n * (b - a * \<gamma>))"
  apply (intro measure_leq_emeasure_ennreal)
  subgoal using gt_0(3) zero_le_T by auto
  using emeasure_A_leq apply (simp add: A_geq assms)
  done

lemma summable_A: "summable (\<lambda>m. measure source (A m))"
proof -
  have "b - a * \<gamma> > 0"
    by (metis diff_gt_0_iff_gt gamma greaterThanLessThan_iff gt_0(1) mult.commute pos_less_divide_eq)
  have 1: "2 powr (- real x * (b - a * \<gamma>)) = (1 / 2 powr (b - a * \<gamma>)) ^ x" for x
    apply (cases "x = 0")
    by (simp_all add: field_simps powr_add[symmetric] powr_realpow[symmetric] powr_powr)
  have 2: "summable (\<lambda>n. 2 powr (- n * (b - a * \<gamma>)))" (is "summable ?C")
  proof -
    have "summable (\<lambda>n. (1 / 2 powr (b - a * \<gamma>)) ^ n)"
      using \<open>b - a * \<gamma> > 0\<close> by auto
    then show "summable (\<lambda>x. 2 powr (- real x * (b - a * \<gamma>)))"
      using 1 by simp
  qed
  from zero_le_T obtain N where "2^N * T \<ge> 1"
    by (metis dual_order.order_iff_strict mult.commute one_less_numeral_iff pos_divide_le_eq
        power_one_over reals_power_lt_ex semiring_norm(76) zero_less_numeral zero_less_power)
  then have "\<And>n. n \<ge> N \<Longrightarrow> 2^n * T \<ge> 1" 
    by (smt (verit, best) \<open>0 < T\<close> mult_right_mono power_increasing_iff)
  then have "\<And>n. n \<ge> N \<Longrightarrow> norm (measure source (A n)) \<le> C * T * 2 powr (- n * (b - a * \<gamma>))"
    using measure_A_leq by simp
  moreover have "summable (\<lambda>n. C * T * 2 powr (- n * (b - a * \<gamma>)))"
    using 2 summable_mult by simp
  ultimately show ?thesis
    using summable_comparison_test' by fast
qed

lemma lim_B: "(\<lambda>n. measure source (B n)) \<longlonglongrightarrow> 0"
proof -        
  have measure_B_le: "measure source (B n) \<le> (\<Sum>m. measure source (A (m + n)))" for n
    apply (rule proc_source.finite_measure_subadditive_countably)
     subgoal by auto
    apply (subst summable_iff_shift)
    using summable_A by blast
  have lim_A: "(\<lambda>n. (\<Sum>m. measure source (A (m + n)))) \<longlonglongrightarrow> 0"
    by (fact suminf_exist_split2[OF summable_A])
  have "convergent (\<lambda>n. measure source (B n))"
  proof (intro Bseq_monoseq_convergent)
    show "Bseq (\<lambda>n. Sigma_Algebra.measure source (\<Union>m. A (m + n)))"
      apply (rule BseqI'[where K="measure source (\<Union> (range A))"])
      apply (auto intro!: proc_source.finite_measure_mono)
      done
    show "monoseq (\<lambda>n. Sigma_Algebra.measure source (\<Union>m. A (m + n)))"
      apply (intro decseq_imp_monoseq[unfolded decseq_def] allI impI proc_source.finite_measure_mono)
       apply (simp_all add: Union_add_subset)
      done
  qed
  then obtain L where lim_B: "(\<lambda>n. measure source (B n)) \<longlonglongrightarrow> L"
    unfolding convergent_def by auto
  then have "L \<ge> 0"
    by (simp add: LIMSEQ_le_const)
  moreover have "L \<le> 0"
    using measure_B_le by (simp add: LIMSEQ_le[OF lim_B lim_A])
  ultimately show ?thesis
    using lim_B by simp
qed

lemma N_null: "N \<in> null_sets source"
proof -
  have "(\<lambda>n. measure source (B n)) \<longlonglongrightarrow> measure source N"
    apply (rule proc_source.finite_Lim_measure_decseq)
    using A_measurable apply fast
    apply (intro monotoneI, simp add: Union_add_subset)
    done
  then have "measure source N = 0"
    using lim_B LIMSEQ_unique by blast
  then show ?thesis
    by (auto simp add: emeasure_eq_ennreal_measure)
qed

lemma notin_N_index:
  assumes "\<omega> \<in> space source - N"
  obtains n\<^sub>0 where "\<omega> \<notin> (\<Union>n. A (n + n\<^sub>0))"
  using assms by blast

context
  fixes \<omega>
  assumes \<omega>: "\<omega> \<in> space source - N"
begin

definition "n\<^sub>0 \<equiv> SOME m. \<omega> \<notin> (\<Union>n. A (n + m)) \<and> m > 0"

lemma
  shows n_zero: "\<omega> \<notin> (\<Union>n. A (n + n\<^sub>0))"
    and n_zero_nonzero: "n\<^sub>0 > 0"
proof -
  have "\<exists>m. \<omega> \<notin> (\<Union>n. A (n + m))"
    using \<omega> by blast
  then have "\<exists>m. \<omega> \<notin> (\<Union>n. A (n + m)) \<and> m > 0"
    by (metis (no_types, lifting) UNIV_I UN_iff add.comm_neutral not_gr_zero zero_less_Suc)
  then have "\<omega> \<notin> (\<Union>n. A (n + n\<^sub>0)) \<and> n\<^sub>0 > 0"
    unfolding n\<^sub>0_def by (rule someI_ex)
  then show "\<omega> \<notin> (\<Union>n. A (n + n\<^sub>0))" "n\<^sub>0 > 0"
    by blast+
qed

lemma nzero_ge: "\<And>n. n \<ge> n\<^sub>0 \<Longrightarrow> 2^n * T \<ge> 1"
proof (rule ccontr)
  fix n assume "n\<^sub>0 \<le> n" "\<not> 1 \<le> 2 ^ n * T"
  then have "A n = space source"
    unfolding A_def by simp
  then have "space source \<subseteq> (\<Union>m. A (m + n))"
    by (smt (verit, del_insts) UNIV_I UN_upper add_0)
  also have "(\<Union>m. A (m + n)) \<subseteq> (\<Union>m. A (m + n\<^sub>0))"
    by (simp add: Union_add_subset \<open>n\<^sub>0 \<le> n\<close>)
  finally show False
    using \<omega> n_zero by blast
qed

lemma omega_notin: "\<And>n. n \<ge> n\<^sub>0 \<Longrightarrow> \<omega> \<notin> A n"
  by (metis n_zero UNIV_I UN_iff add.commute le_Suc_ex)

text \<open>Klenke 21.7\<close>

lemma X_dyadic_incr:
  assumes "k \<in> {1..\<lfloor>2^n * T\<rfloor>}" "n \<ge> n\<^sub>0"
  shows "dist (X ((real_of_int k-1)/2^n) \<omega>) (X (real_of_int k/2^n) \<omega>) < 2 powr (- \<gamma> * n)"
proof -
  have "finite {1..\<lfloor>2^n * T\<rfloor>}" "{1..\<lfloor>2^n * T\<rfloor>} \<noteq> {}"
    using assms nzero_ge by blast+
  then have fin_nonempty: "finite {dist (X (real_of_int (k - 1) * 2 powr - real n) \<omega>) (X (real_of_int k * 2 powr - real n) \<omega>) |k.
             k \<in> {1..\<lfloor>2 ^ n * T\<rfloor>}}" "{dist (X (real_of_int (k - 1) * 2 powr - real n) \<omega>) (X (real_of_int k * 2 powr - real n) \<omega>) |k.
             k \<in> {1..\<lfloor>2 ^ n * T\<rfloor>}} \<noteq> {}"
    by fastforce+
  have "2 powr (- \<gamma> * real n)
     > Max {dist (X (real_of_int (k - 1) * 2 powr - real n) \<omega>) (X (real_of_int k * 2 powr - real n) \<omega>) |k.
             k \<in> {1..\<lfloor>2 ^ n * T\<rfloor>}}"
    using nzero_ge[OF assms(2)] omega_notin[OF assms(2)] \<omega> A_def by auto
  then have "2 powr (- \<gamma> * real n) > dist (X (real_of_int (k - 1) * 2 powr - real n) \<omega>) (X (real_of_int k * 2 powr - real n) \<omega>)"
    using Max_less_iff[OF fin_nonempty] assms(1) by blast
  then show ?thesis
    by (simp, smt (verit, ccfv_threshold) divide_powr_uminus powr_realpow)
qed

text \<open> Klenke (21.8) \<close>

lemma dist_dyadic_mn:
  assumes mn: "n\<^sub>0 \<le> n" "n \<le> m"
    and t_dyadic: "t \<in> dyadic_interval_step m 0 T"
    and u_dyadic_n: "u \<in> dyadic_interval_step n 0 T"
    and ut: "u \<le> t" "t - u < 2/2^n"
  shows "dist (X u \<omega>) (X t \<omega>) \<le> 2 powr (- \<gamma> * n) / (1 - 2 powr - \<gamma>)"
proof -
  have u_dyadic: "u \<in> dyadic_interval_step m 0 T"
    using mn(2) dyadic_interval_step_subset u_dyadic_n by fast
  have "0 < n"
    using mn(1) n_zero_nonzero by linarith
  then have "t - u < 1"
    by (smt (verit) ut(2) One_nat_def Suc_le_eq divide_le_eq_1_pos power_increasing power_one_right)
  obtain b_tu k_tu where tu_exp: "dyadic_expansion (t-u) m b_tu k_tu"
    using dyadic_expansion_ex dyadic_interval_minus[OF u_dyadic t_dyadic \<open>u \<le> t\<close>] by blast
  then have "k_tu = 0"
    using dyadic_expansion_floor[OF tu_exp] \<open>t - u < 1\<close> \<open>u \<le> t\<close> by linarith
  have b_tu_0_1: "b_tu ! i \<in> {0,1}" if "i \<in> {0..m-1}" for i
    using dyadic_expansionD(1,2)[OF tu_exp] that
    by (metis Suc_pred' \<open>0 < n\<close> atLeastAtMost_iff le_imp_less_Suc le_trans less_eq_Suc_le mn(2) nth_mem subsetD)
  text \<open> And hence $b_i (t - u) = b_i (s-u) = 0$ for $i < n$. \<close>
  have b_t_zero: "b_tu ! i = 0" if "i+1 < n" for i
  proof (rule ccontr)
    assume "b_tu ! i \<noteq> 0"
    then have "b_tu ! i = 1"
      by (smt (verit) add_lessD1 dyadic_expansionD(1,2) insertE mn(2) nth_mem order_less_le_trans
          singletonD subset_iff that tu_exp)
    then have "t - u \<ge> (real_of_int 0) + 1/2^(i+1)"
      apply (intro dyadic_expansion_nth_geq)
      using tu_exp \<open>k_tu = 0\<close> apply blast
       apply (metis One_nat_def Suc_eq_plus1 Suc_le_mono atLeastAtMost_iff le_trans less_Suc_eq linorder_not_le mn(2) nat_less_le that zero_order(1))
      apply simp
      done
    moreover have "1/2^(n-1) \<le> 1/(2^(i+1) :: real)"
      apply (intro divide_left_mono)
        apply (metis that Suc_eq_plus1 Suc_leI less_diff_conv power_increasing power_one_right two_realpow_ge_one)
      by simp_all
    ultimately have "t - u \<ge> 1 / 2 ^ (n - 1)"
      by linarith
    then show False
      using \<open>t - u < 2/2^n\<close> \<open>n > 0\<close> by (auto simp: power_diff)
  qed
  define t' where "t' \<equiv> \<lambda>l. (u + (\<Sum>i = n..l. b_tu!(i-1) / 2 ^ i))"
  have "t' (n-1) = u"
    unfolding t'_def using \<open>n > 0\<close> by simp
  have "t' m = t"
  proof -
    have b_tu_eq_0: "(\<Sum> i = 1..n-1. b_tu!(i-1) / 2 ^ i) = 0"
      by (subst sum_nonneg_eq_0_iff, auto simp add: sum_nonneg_eq_0_iff b_t_zero)
    have "t - u = (\<Sum>i = 1..m. b_tu!(i-1) / 2 ^ i)"
      using tu_exp[THEN dyadic_expansionD(3)] \<open>k_tu = 0\<close> by linarith
    also have "... = (\<Sum>i = 1..n-1. b_tu!(i-1) / 2 ^ i) + (\<Sum>i = n..m. b_tu!(i-1) / 2 ^ i)"
    proof -
      have 1: "{1..m} = {1..n-1} \<union> {n..m}"
        using \<open>n > 0\<close> mn(2) by fastforce
      show ?thesis
        by (subst 1, auto simp: sum.union_disjoint)
    qed
    finally have "t-u = (\<Sum>i = n..m. b_tu!(i-1) / 2 ^ i)"
      using b_tu_eq_0 by algebra
    then show ?thesis
      unfolding t'_def by argo
  qed
  have t_pos: "t' l \<ge> 0" if \<open>l \<in> {n..m}\<close> for l
    unfolding t'_def apply (rule add_nonneg_nonneg)
    using dyadic_step_geq u_dyadic apply blast
    by (simp add: sum_nonneg)
  have t'_Suc: "t' (Suc l) = t' l + b_tu ! l / 2^(Suc l)" if "l \<in>{n-1..m-1}" for l
    unfolding t'_def by (simp add: b_t_zero)
  have le_add_diff: "b \<le> c - a \<Longrightarrow> a + b \<le> c" for a b c :: real
    by argo
  have t'_leq: "t' l \<le> t" if \<open>l \<in> {n..m}\<close> for l
    unfolding t'_def apply (intro le_add_diff)
    apply (simp only: tu_exp[THEN dyadic_expansionD(3)] \<open>k_tu = 0\<close> of_int_0 add_0)
    apply (rule sum_mono2)
    using \<open>0 < n\<close> that by auto
  have t'_dyadic: "t' l \<in> dyadic_interval_step l 0 T" if "l \<in> {n..m}" for l
    using that
  proof (induct l rule: atLeastAtMost_induct)
    case base
    consider "b_tu ! (n - 1) = 0" | "b_tu ! (n-1) = 1"
      using dyadic_expansion_frac_range[OF tu_exp(1), of n] \<open>0 < n\<close> mn(2) by auto
    then show ?case
      apply cases
      using \<open>0 < n\<close> t'_def apply simp
      using u_dyadic_n apply blast
      apply (rule dyadic_interval_step_memI)
        apply (simp add: t'_def)
      using u_dyadic_n
        apply (metis add_divide_distrib dyadic_interval_step_iff of_int_1 of_int_add)
       apply (simp add: mn(2) t_pos)
      by (meson t'_leq[OF that] atLeastAtMost_iff dual_order.refl dual_order.trans dyadic_step_leq mn(2) t'_leq t_dyadic)
  next
    case (Suc l)
    then have t'_dyadic_Suc: "t' l \<in> dyadic_interval_step (Suc l) 0 T"
      using dyadic_interval_step_mono le_SucI by blast
    from Suc have "l \<in> {0..m-1}"
      by force
    then consider "b_tu!l = 0" | "b_tu!l = 1"
      using b_tu_0_1 by fastforce
    then obtain k :: int where k: "t' l + (b_tu ! l) / 2 ^ Suc l = k / 2 ^ Suc l"
      apply cases
      subgoal using dyadic_interval_step_iff t'_dyadic_Suc by auto
      by (metis add.commute add_divide_distrib dyadic_as_natural of_int_of_nat_eq of_nat_1 of_nat_Suc t'_dyadic_Suc)
    have "t' (Suc l) \<le> t"
      by (meson Suc atLeastAtMost_iff le_SucI less_eq_Suc_le t'_leq)
    with Suc(1,2) show ?case
      apply (subst t'_Suc)
       apply (metis Suc_leD Suc_pred' \<open>0 < n\<close> atLeastAtMost_iff less_Suc_eq_le mn(2) order_less_le_trans)
      apply (intro dyadic_interval_step_memI)
        apply (rule exI[where x=k])
      using k apply blast
      using dyadic_step_geq t'_dyadic_Suc apply force
      apply (subst t'_Suc[symmetric])
       apply force
      using dyadic_step_leq order_trans t_dyadic by blast
  qed
  have "dist (X (t' (n-1)) \<omega>) (X (t' m) \<omega>) \<le> (\<Sum> l=Suc (n-1)..m. dist (X (t' l) \<omega>) (X (t' (l-1)) \<omega>))"
    apply (rule triangle_ineq_sum)
    using diff_le_self dual_order.trans mn(2) by blast
  also have "... = (\<Sum> l=n..m. dist (X (t' l) \<omega>) (X (t' (l-1)) \<omega>))"
    using Suc_diff_1 \<open>0 < n\<close> by presburger
  also have "... \<le> (\<Sum> l=n..m. 2 powr (-\<gamma> * l))"
  proof (rule sum_mono)
    fix l assume *: "l \<in> {n..m}"
    then have "l \<in> {n-1..m}"
      by (metis atLeastAtMost_iff less_imp_diff_less linorder_not_less order_le_less)
    from * have [simp]: "0 < l"
      using \<open>0 < n\<close> by fastforce
    from \<open>l \<in> {n..m}\<close> have "b_tu ! (l-1) \<in> {0, 1}"
      apply (intro dyadic_expansion_frac_range)
       apply (rule tu_exp)
      using \<open>n > 0\<close> by simp
    then consider (zero) "b_tu ! (l-1) = 0" | (one) "b_tu ! (l-1) = 1"
      by fast
    then show "dist (X (t' l) \<omega>) (X (t' (l - 1)) \<omega>) \<le> 2 powr (- \<gamma> * l)"
    proof cases
      case zero
      have "{n..l} = insert l {n..l-1}"
        using \<open>0 < n\<close> \<open>l \<in> {n..m}\<close> by auto
      then have "sum f {n..l} = sum f {n..l-1} + f l" for f :: "nat \<Rightarrow> real"
        by (metis (no_types, opaque_lifting) Groups.add_ac(3) Suc_le_eq Suc_pred' \<open>0 < n\<close> atLeastAtMost_iff finite_atLeastAtMost group_cancel.rule0 linorder_not_le nle_le sum.insert zero_diff zero_less_diff)
      then have "t' l = t' (l-1)"
        unfolding t'_def using zero by simp
      then show ?thesis
        by simp
    next
      case one
      then have [simp]: "b_tu ! (l - Suc 0) = 1"
        by simp
      obtain k where k: "k \<ge> 0" "k \<le> \<lfloor>2^l * T\<rfloor>" "t' l = k/2^l"
        using t'_dyadic \<open>l \<in> {n..m}\<close> dyadic_interval_step_iff by force
      have "t' (l-1) \<in> dyadic_interval_step l 0 T"
      proof (cases "l = n")
        case True
        then have "t' (l-1) = u"
          using \<open>t' (n - 1) = u\<close> by presburger
        then show "t' (l-1) \<in> dyadic_interval_step l 0 T"
          using True u_dyadic_n by blast
      next
        case False
        then have "l-1 \<in> {n..m}"
          by (metis "*" Suc_eq_plus1 add_leD2 atLeastAtMost_iff diff_le_self dual_order.trans
              le_antisym not_less_eq_eq ordered_cancel_comm_monoid_diff_class.le_diff_conv2)
        then show "t' (l-1) \<in> dyadic_interval_step l 0 T"
          using t'_dyadic dyadic_interval_step_subset diff_le_self by blast
      qed
      then obtain k' where k': "k' \<ge> 0" "k' \<le> \<lfloor>2^l * T\<rfloor>" "t' (l-1) = k'/2^l"
        using dyadic_interval_step_iff by auto
      then have t'_k: "t' (l-1) = (k-1) / 2^l"
      proof -
        have "t' l = t' (l-1) + real (b_tu ! (l-1)) / 2 ^ l"
          using t'_Suc[of "l-1"] apply simp
          using "*" diff_le_mono by presburger
        then have "k / 2^l = t' (l-1) + 1/2^l"
          by (simp add: k(3))
        then show ?thesis
          by (simp add: diff_divide_distrib)
      qed
      then have "k \<ge> 1"
        using k'(1) k'(3) by auto
      then show ?thesis
        apply (simp only: k(3) t'_k)
        apply (subst dist_commute)
        apply (intro less_imp_le)
        apply (simp only: of_int_diff of_int_1)
        apply (rule X_dyadic_incr[of k l])
        using k(2) apply presburger
        using \<open>l \<in> {n..m}\<close> mn(1) by auto
    qed
  qed
  also have "... = (\<Sum> l=n..m. (2 powr -\<gamma>) ^ l)"
    apply (intro sum.cong; simp add: field_simps)
    by (smt (verit, ccfv_SIG) powr_powr[symmetric] mult_minus_left powr_gt_zero powr_realpow)
  also have "... \<le> 2 powr (-\<gamma> * n) / (1 - 2 powr -\<gamma>)"
    apply (subst sum_gp)
    using \<open>m \<ge> n\<close> apply (simp add: field_simps)
    apply safe
    using gamma_gt_0 apply force
    apply (rule divide_right_mono)
     apply (simp only: minus_mult_left)
     apply (subst powr_powr[symmetric])
     apply (subst powr_realpow[symmetric]; simp)+
    by (metis diff_ge_0_iff_ge gamma_gt_0 less_eq_real_def
        neg_le_0_iff_le one_le_numeral powr_mono powr_nonneg_iff powr_zero_eq_one)
  finally show "dist (X u \<omega>) (X t \<omega>) \<le> 2 powr (- \<gamma> * real n) / (1 - 2 powr - \<gamma>)"
    using \<open>t' (n - 1) = u\<close> \<open>t' m = t\<close> by blast
qed

lemma dist_dyadic_fixed:
  assumes mn: "n\<^sub>0 \<le> n" "n \<le> m"
    and s_dyadic: "s \<in> dyadic_interval_step m 0 T"
    and t_dyadic: "t \<in> dyadic_interval_step m 0 T"
    and st: "s \<le> t" "t - s \<le> 1/2^n"
  shows "dist (X t \<omega>) (X s \<omega>) \<le> 2 * 2 powr (- \<gamma> * n) / (1 - 2 powr - \<gamma>)"
proof -
  have "n > 0"
    using mn(1) n_zero_nonzero by linarith
  define u where "u \<equiv> \<lfloor>2^n * s\<rfloor> / 2^n"
  have "u = Max (dyadic_interval_step n 0 s)"
    unfolding u_def using  dyadic_interval_step_Max[symmetric] dyadic_step_geq[OF s_dyadic]
    by blast
  then have u_dyadic_n: "u \<in> dyadic_interval_step n 0 T"
    using dyadic_interval_step_mem dyadic_step_geq dyadic_step_leq s_dyadic u_def by force
  text \<open> Then, $u \leq s < u + 2^{-n}$ and $u \leq t < u + 2^{1-n}$\<close>
  have "u \<le> s"
    unfolding u_def using floor_pow2_leq by blast
  have "s < u + 1/2^n"
    unfolding u_def apply (simp add: field_simps)
    using floor_le_iff apply linarith
    done
  then have "s - u < 2/2^n"
    using \<open>u \<le> s\<close> by auto
  then have dist_us: "dist (X u \<omega>) (X s \<omega>) \<le> 2 powr (- \<gamma> * real n) / (1 - 2 powr - \<gamma>)"
    by (rule dist_dyadic_mn[OF mn s_dyadic u_dyadic_n \<open>u \<le> s\<close>]) 
  have "u \<le> t"
    using \<open>u \<le> s\<close> st(1) by linarith
  have "t < u + 2/2^n"
    using \<open>s <u + 1/2^n\<close> st(2) by force
  then have "t - u < 2/2^n"
    by force
  then have "dist (X u \<omega>) (X t \<omega>) \<le> 2 powr (- \<gamma> * real n) / (1 - 2 powr - \<gamma>)"
    by (rule dist_dyadic_mn[OF mn t_dyadic u_dyadic_n \<open>u \<le> t\<close>])
  then show "dist (X t \<omega>) (X s \<omega>) \<le> 2 * (2 powr (-\<gamma> * n)) / (1 - 2 powr - \<gamma>)"
    using dist_us by metric
qed

definition "C\<^sub>0 \<equiv> 2 * 2 powr \<gamma> / (1 - 2 powr - \<gamma>)"

lemma C_zero_ge[simp]: "C\<^sub>0 > 0"
  by (smt (verit, ccfv_SIG) C\<^sub>0_def divide_pos_pos gamma_gt_0 powr_eq_one_iff powr_less_mono)

text \<open> Klenke (21.9) \<close>
text \<open> Let $s, t \in D$ with $|s-t| \leq \frac{1}{2^n_0}$. By choosing the minimal $n \geq n_0$ such
  that $|t-s| \geq 2^{-n}$, we obtain by @{thm dist_dyadic_fixed}:
  \[|X_t(\omega) - X_s(\omega)| \leq C_0 |t-s|^\gamma\]\<close>

lemma dist_dyadic:
  assumes t: "t \<in> dyadic_interval 0 T"
    and s: "s \<in> dyadic_interval 0 T"
    and st_dist: "dist t s \<le> 1 / 2 ^ n\<^sub>0"
  shows  "dist (X t \<omega>) (X s \<omega>) \<le> C\<^sub>0 * (dist t s) powr \<gamma>"
proof (cases "s = t")
  case True
  then show ?thesis by simp
next
  case False
  define n where "n \<equiv> LEAST n. dist t s \<ge> 1/2^n"
  have "dist t s > 0"
    using False by simp
  then have "\<exists>n. dist t s \<ge> 1 / 2^n"
    by (metis less_eq_real_def one_less_numeral_iff power_one_over reals_power_lt_ex semiring_norm(76))
  then have "dist t s \<ge> 1/2^n"
    unfolding n_def by (meson LeastI_ex)
  then have "n \<ge> n\<^sub>0"
    using order_trans[OF \<open>dist t s \<ge> 1/2^n\<close> st_dist]
    by (simp add: field_simps)
  have "dist t s \<le> 1/2^(n-1)"
  proof -
    have "n-1 < (LEAST n. dist t s \<ge> 1/2^n)"
      using \<open>n\<^sub>0 \<le> n\<close> n_zero_nonzero n_def by fastforce
    then have "\<not> (dist t s \<ge> 1/2^(n-1))"
      by (rule not_less_Least)
    then show ?thesis
      by auto
  qed
  obtain m where m: "m \<ge> n" "s \<in> dyadic_interval_step m 0 T" "t \<in> dyadic_interval_step m 0 T"
    by (metis dyadic_interval_step_mono linorder_not_le mem_dyadic_interval order.asym s t)
  from \<open>n \<ge> n\<^sub>0\<close> consider (eq) "n = n\<^sub>0" | (gt) "n > n\<^sub>0"
    using less_eq_real_def by linarith
  then show ?thesis
  proof cases
    case eq
    consider "t \<le> s" | "s \<le> t"
      by fastforce
    then have "dist (X t \<omega>) (X s \<omega>) \<le> 2 * 2 powr (- \<gamma> * n) / (1 - 2 powr - \<gamma>)"
      apply cases
       apply (subst dist_commute)
       apply (rule dist_dyadic_fixed[OF \<open>n \<ge> n\<^sub>0\<close> m(1,3,2)])
        apply simp
      using dist_real_def eq st_dist apply force
      apply (rule dist_dyadic_fixed[OF \<open>n \<ge> n\<^sub>0\<close> m])
       apply simp
      using dist_real_def eq st_dist apply force
      done
    also have "... \<le> C\<^sub>0 * 2 powr (- \<gamma> * n)"
      unfolding C\<^sub>0_def apply (simp add: field_simps)
      apply (intro divide_right_mono mult_left_mono)
        apply (simp add: less_eq_real_def)
       apply simp
      by (smt (verit) gamma_gt_0 powr_le_cancel_iff powr_zero_eq_one)
    also have "... = C\<^sub>0 * (1/2^n) powr \<gamma>"
      by (smt (verit, del_insts) powr_minus_divide powr_powr powr_powr_swap powr_realpow)
    also have "... \<le> C\<^sub>0 * (dist t s) powr \<gamma>"
      using \<open>1 / 2 ^ n \<le> dist t s\<close> eq st_dist by auto
    finally show ?thesis .
  next
    case gt
    consider "t \<le> s" | "s \<le> t"
      by fastforce
    then have "dist (X t \<omega>) (X s \<omega>) \<le> 2 * 2 powr (- \<gamma> * (n-1)) / (1 - 2 powr - \<gamma>)"
      apply cases
       apply (subst dist_commute)
       apply (rule dist_dyadic_fixed[where m=m])
            prefer 7 apply (rule dist_dyadic_fixed[where m=m])
      using gt m apply simp_all
      using \<open>dist t s \<le> 1 / 2 ^ (n - 1)\<close> dist_real_def apply force+
      done
    also have "... \<le> C\<^sub>0 * 2 powr (- \<gamma> * n)"
      unfolding C\<^sub>0_def apply simp
      apply (intro divide_right_mono)
       apply (simp add: powr_add[symmetric])
       apply (metis One_nat_def Suc_leI dual_order.refl gt less_imp_Suc_add minus_diff_eq mult.right_neutral of_nat_1 of_nat_diff right_diff_distrib zero_less_Suc)
      by (metis gamma_gt_0 ge_iff_diff_ge_0 less_eq_real_def neg_le_0_iff_le one_le_numeral powr_mono powr_zero_eq_one zero_neq_numeral)
    also have "... = C\<^sub>0 * (1/2^n) powr \<gamma>"
      by (smt (verit, best) powr_minus_divide powr_powr powr_powr_swap powr_realpow)
    also have "C\<^sub>0 * (1/2^n) powr \<gamma> \<le> C\<^sub>0 * dist t s powr \<gamma>"
      apply (rule mult_left_mono)
      using \<open>1 / 2 ^ n \<le> dist t s\<close> less_eq_real_def powr_mono2 apply force
      using C_zero_ge by linarith
    finally show ?thesis .
  qed
qed

(* The extra power of 2 makes the issues with dyadics disappear in holder_dyadic, since we divide
  by a power of 2 *)
definition "K \<equiv> C\<^sub>0 * (2^nat \<lceil>2^n\<^sub>0 * T\<rceil>) powr (1 - \<gamma>)"

lemma C\<^sub>0_le_K: "C\<^sub>0 \<le> K"
  unfolding K_def using nzero_ge[of n\<^sub>0] ge_one_powr_ge_zero by force

lemma K_pos: "0 < K"
  using C\<^sub>0_le_K C_zero_ge by linarith

text \<open> Klenke (21.10) \<close>
lemma X_dyadic_le_K':
  assumes dyadic: "s \<in> dyadic_interval 0 T" "t \<in> dyadic_interval 0 T" 
    and st: "s \<le> t"
  shows "dist (X s \<omega>) (X t \<omega>) \<le> K * dist s t powr \<gamma>"
proof (cases "dist s t \<le> 1 / 2^n\<^sub>0")
  case True
  then have "C\<^sub>0 * dist t s powr \<gamma> \<le> K * dist t s powr \<gamma>"
    by (simp add: C\<^sub>0_le_K powr_def)
  then show ?thesis
    using dist_dyadic[OF assms(1,2) True] by (simp add: dist_commute)
next
  case False
  define n :: nat where "n \<equiv> nat \<lceil>2^n\<^sub>0 * T\<rceil>"
  have "dist s t / n \<le> 1/2^n\<^sub>0"
    apply (simp add: n_def field_simps)
    by (smt (verit, best) dyadic dist_real_def divide_le_eq_1 dyadics_geq dyadics_leq
        mem_dyadic_interval mult_mono of_nat_eq_0_iff of_nat_le_0_iff real_nat_ceiling_ge zero_le_power)
  have dist_st: "dist s t / 2^n \<le> 1/2^n\<^sub>0"
    apply (rule order_trans[where y="dist s t / n"])
     apply (rule divide_left_mono; simp?)
     apply (simp add: n_def zero_le_T)
    apply (fact \<open>dist s t / n \<le> 1/2^n\<^sub>0\<close>)
    done
  define f where "f \<equiv> \<lambda>i::nat. (s + (t-s) * i/2^n)"
  have f_inc: "f k = f (k - 1) + (t - s) / 2^n" if "k > 0" for k
  proof -
    have "f (Suc k) = f k + (t - s) / 2^n" for k
      by (simp add: f_def field_simps)
    then show ?thesis
      by (metis Suc_pred' that)
  qed
  have f_inc_le: "dist (f i) (f (i - 1)) \<le> 1 / 2 ^ n\<^sub>0" for i
  proof (cases "i=0")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis
      using f_inc dist_real_def dist_st st by auto
  qed
  have f_ge_s: "\<And>i. i \<le> 2^n \<Longrightarrow> f i \<ge> s"
    unfolding f_def using st by auto
  have f_le_t: "\<And>i. i \<le> 2^n \<Longrightarrow> f i \<le> t"
    by (smt (verit, del_insts) f_def st divide_le_eq_1 mult_less_cancel_left1 of_nat_1 of_nat_add
        of_nat_le_iff of_nat_power one_add_one times_divide_eq_right zero_less_power)
  have f_dyadic: "f i \<in> dyadic_interval 0 T" if "i \<le> 2^n" for i
  proof (rule mem_dyadic_intervalI)
    have "f i \<le> T"
    proof -
      have "f i \<le> s + t - s"
        using f_le_t[OF that] by simp
      also have "... \<le> T"
        using dyadic(2) dyadics_leq by simp
      finally show ?thesis .
    qed
    obtain m where "s \<in> dyadic_interval_step m 0 T" "t \<in> dyadic_interval_step m 0 T"
      by (metis dyadic dyadic_interval_step_mono mem_dyadic_interval nle_le)
    then obtain ks kt where ks: "s = real ks / 2^m" and kt: "t = real kt / 2^m"
      using dyadic_as_natural by metis
    then have "ks \<le> kt"
      using st by (simp add: divide_le_cancel)
    from ks kt have "ks = 2^m * s" "kt = 2^m * t"
      by simp_all
    from ks kt have "f i = (ks / 2^m) + (kt / 2^m - ks / 2^m) * i / 2^n"
      unfolding f_def by auto
    also have "... = (ks * (2^n - i) + kt * i) / 2^(m+n)"
      using \<open>ks \<le> kt\<close> apply (simp add: right_diff_distrib field_simps power_add)
      by (metis distrib_left le_add_diff_inverse mult.commute of_nat_add of_nat_numeral of_nat_power that)
    finally have "f i \<in> dyadic_interval_step (m+n) 0 T"
      apply (intro dyadic_interval_step_memI)
        apply (rule exI[where x="int (ks * (2^n - i) + kt * i)"])
        prefer 3 apply (rule \<open>f i \<le> T\<close>)
      by simp_all
    then show "\<exists>n. f i \<in> dyadic_interval_step n 0 T"
      by blast
  qed
  have "dist (X s \<omega>) (X t \<omega>) \<le> (\<Sum> i=1..2^n. dist (X (f i) \<omega>) (X (f (i-1)) \<omega>))"
  proof -
    have "f 0 = s"
      unfolding f_def by (simp add: field_simps)
    moreover have "f (2^n) = t"
      unfolding f_def by (simp add: field_simps)
    moreover have "dist (X (f 0) \<omega>) (X (f (2^n)) \<omega>) \<le> (\<Sum> i=Suc 0..2^n. dist (X (f i) \<omega>) (X (f (i-1)) \<omega>))"
      by (rule triangle_ineq_sum, simp)
    ultimately show ?thesis
      by simp
  qed
  also have "... \<le> (\<Sum> i=1..2^n::nat. C\<^sub>0 * (dist (f i) (f (i-1))) powr \<gamma>)"
    apply (rule sum_mono)
    apply (intro dist_dyadic f_dyadic)
      apply fastforce
     apply fastforce
    using f_inc_le .
  also have "... \<le> (\<Sum> i=1..2^n::nat. C\<^sub>0 * (dist t s / 2^n) powr \<gamma>)"
    apply (rule sum_mono)
    using f_inc by (simp add: dist_real_def)
  also have "... \<le> 2^n * C\<^sub>0 * (dist t s / 2^n) powr \<gamma>"
    by (subst sum_constant, force)
  also have "... \<le> K * dist t s powr \<gamma>"
    unfolding K_def n_def apply (simp add: powr_divide field_simps)
    apply (rule mult_left_mono)
     apply (smt (verit, ccfv_threshold) powr_add powr_one zero_le_power)
    by simp
  finally show ?thesis
    by (metis dist_commute)
qed

lemma X_dyadic_le_K:
  assumes "s \<in> dyadic_interval 0 T"
    and "t \<in> dyadic_interval 0 T"
  shows "dist (X s \<omega>) (X t \<omega>) \<le> K * dist s t powr \<gamma>"
  by (metis nle_le assms X_dyadic_le_K' dist_commute)

corollary holder_dyadic: "\<gamma>-holder_on (dyadic_interval 0 T) (\<lambda>t. X t \<omega>)"
  apply (intro holder_onI[OF gamma_0_1] exI[where x=K])
  using K_pos X_dyadic_le_K by force

lemma uniformly_continuous_dyadic: "uniformly_continuous_on (dyadic_interval 0 T) (\<lambda>t. X t \<omega>)"
  using holder_dyadic by (fact holder_uniform_continuous)

lemma Lim_exists: "\<exists>L. ((\<lambda>s. X s \<omega>) \<longlongrightarrow> L) (at t within (dyadic_interval 0 T))"
  if "t \<in> {0..T}"
  apply (rule uniformly_continuous_on_extension_at_closure[where x = t])
  using that dyadic_interval_dense uniformly_continuous_dyadic apply fast
  using that apply (simp add: dyadic_interval_dense)
  by blast

lemma Lim_unique: "\<exists>!L. ((\<lambda>s. X s \<omega>) \<longlongrightarrow> L) (at t within (dyadic_interval 0 T))" 
  if "t \<in> {0..T}"
  by (metis that Lim_exists dyadic_interval_islimpt tendsto_Lim trivial_limit_within zero_le_T)

definition "L \<equiv> (\<lambda>t. (Lim (at t within dyadic_interval 0 T) (\<lambda>s. X s \<omega>)))"

lemma X_tendsto_L:
  assumes "t \<in> {0..T}"
  shows "((\<lambda>s. X s \<omega>) \<longlongrightarrow> L t) (at t within (dyadic_interval 0 T))"
proof -
  have "at t within dyadic_interval 0 T \<noteq> \<bottom>"
    by (simp add: trivial_limit_within dyadic_interval_islimpt[OF zero_le_T assms])
  moreover obtain L' where L': "((\<lambda>s. X s \<omega>) \<longlongrightarrow> L') (at t within (dyadic_interval 0 T))"
    using Lim_exists[OF assms] by blast
  ultimately have "L t = L'"
    unfolding L_def by (rule tendsto_Lim)
  then show ?thesis
    using L' by blast
qed

lemma L_dist_K:
  assumes s: "s \<in> {0..T}"
    and t: "t \<in> {0..T}"
  shows "dist (L s) (L t) \<le> K * dist s t powr \<gamma>"
proof (cases "s = t")
  case True
  then show ?thesis by simp
next
  case False
  let ?F = "\<lambda>x. at x within dyadic_interval 0 T"
  have "(?F s \<times>\<^sub>F ?F t) \<noteq> \<bottom>"
    by (meson dyadic_interval_islimpt prod_filter_eq_bot s t trivial_limit_within zero_le_T)
  moreover have "((\<lambda>x. K * dist (fst x) (snd x) powr \<gamma>) \<longlongrightarrow> K * dist s t powr \<gamma>) (?F s \<times>\<^sub>F ?F t)"
    apply (rule tendsto_mult_left)
    apply (rule tendsto_powr)
    using tendsto_dist_prod apply blast
     apply simp
    using False by simp
  moreover have "((\<lambda>x. dist (X (fst x) \<omega>) (X (snd x) \<omega>)) \<longlongrightarrow> dist (L s) (L t)) (?F s \<times>\<^sub>F ?F t)"
    using X_tendsto_L t s tendsto_dist_prod by blast
  moreover have "\<forall>\<^sub>F x in ?F s \<times>\<^sub>F ?F t. dist (process X (fst x) \<omega>) (process X (snd x) \<omega>) 
                                     \<le> K * dist (fst x) (snd x) powr \<gamma>"
    apply (rule eventually_prodI'[where P = "\<lambda>x. x \<in> dyadic_interval 0 T"
          and Q = "\<lambda>x. x \<in> dyadic_interval 0 T"])
    using eventually_at_topological apply blast
    using eventually_at_topological apply blast
    using X_dyadic_le_K by simp    
  ultimately show ?thesis
    by (rule tendsto_le)
qed

corollary L_holder: "\<gamma>-holder_on {0..T} L"
  using K_pos L_dist_K by (auto intro!: holder_onI[OF gamma_0_1] exI[where x=K])

corollary L_local_holder: "local_holder_on \<gamma> {0..T} L"
  using holder_implies_local_holder[OF L_holder] by blast

lemma X_dyadic_eq_L:
  assumes "t \<in> dyadic_interval 0 T"
  shows "X t \<omega> = L t"
proof -
  have "((\<lambda>x. X x \<omega>) \<longlongrightarrow> X t \<omega>) (at t within dyadic_interval 0 T)"
    using continuous_within[symmetric] uniformly_continuous_dyadic uniformly_continuous_imp_continuous
      continuous_on_eq_continuous_within assms by fast
  then show ?thesis
    by (metis L_def assms dyadic_interval_islimpt dyadic_interval_subset_interval subsetD
        tendsto_Lim trivial_limit_within zero_le_T)
qed
end

definition default :: 'b where "default = (SOME x. True)"

definition X_tilde :: "real \<Rightarrow> 'a \<Rightarrow> 'b" where
  "X_tilde \<equiv> (\<lambda>t \<omega>. if \<omega> \<in> N then default else (Lim (at t within dyadic_interval 0 T) (\<lambda>s. X s \<omega>)))"

lemma X_tilde_not_N_Lim:
  assumes "\<omega> \<in> space source - N"
  shows "X_tilde t \<omega> = Lim (at t within dyadic_interval 0 T) (\<lambda>s. X s \<omega>)"
  using assms X_tilde_def by auto

lemma X_tilde_not_N_L:
  assumes "\<omega> \<in> space source - N"
  shows "X_tilde t \<omega> = L \<omega> t"
  using assms X_tilde_def L_def[OF assms] by auto

lemma local_holder_X_tilde: "local_holder_on \<gamma> {0..T} (\<lambda>t. X_tilde t \<omega>)"
  if "\<omega> \<in> space source" for \<omega>
proof (cases "\<omega> \<in> N")
  case True
  then show ?thesis
    unfolding X_tilde_def using local_holder_const by fastforce
next
  case False
  then have 1: "\<omega> \<in> space source - N"
    using that by blast
  show ?thesis
    using L_local_holder[OF 1] X_tilde_not_N_L[OF 1]
    by (simp only: False if_False)
qed

corollary X_tilde_eq_L_AE: "AE \<omega> in source. X_tilde t \<omega> = L \<omega> t"
  apply (rule AE_I[where N=N])
    apply (smt (verit, del_insts) X_tilde_def Diff_iff L_def mem_Collect_eq subsetI)
  using N_null apply blast+
  done

corollary X_tilde_eq_Lim_AE:
  "AE \<omega> in source. X_tilde t \<omega> = Lim (at t within dyadic_interval 0 T) (\<lambda>s. X s \<omega>)"
  apply (rule AE_I[where N=N])
    apply (smt (verit, del_insts) X_tilde_def Diff_iff L_def mem_Collect_eq subsetI)
  using N_null apply blast+
  done

lemma X_tilde_tendsto_AE: "t \<in> {0..T} \<Longrightarrow> tendsto_AE source X (X_tilde t) (at t within dyadic_interval 0 T)"
  apply (unfold tendsto_AE_def)
  apply (rule AE_I3[where N=N])
   apply (subst X_tilde_not_N_Lim, argo)
  unfolding t2_space_class.Lim_def apply (rule the1I2)
  using Lim_unique apply presburger
   apply blast
  using N_null by blast

end

context Kolmogorov_Chentsov_finite
begin

text \<open> By (21.5) @{thm conv_in_prob_finite} and (21.11) @{thm L_def}, $P[X \neq \tilde{X}] = 0$\<close>

lemma X_tilde_measurable[measurable]:
  assumes "t \<in> {0..T}"
  shows "X_tilde t \<in> borel_measurable source"
proof -
  let ?Lim = "(\<lambda>\<omega>. Lim (at t within dyadic_interval 0 T) (\<lambda>s. process X s \<omega>))"
  have "?Lim \<in> borel_measurable (restrict_space source (space source - N))"
    unfolding X_tilde_def apply measurable
    using measurable_id measurable_restrict_space1 apply blast
    using assms Lim_exists space_restrict_space apply simp
    using assms dyadic_interval_islimpt trivial_limit_within zero_le_T by blast
  then have "(\<lambda>\<omega>. if \<omega> \<in> space source - N then ?Lim \<omega> else default) \<in> borel_measurable source"
    by (subst measurable_restrict_space_iff[symmetric]; simp)
  then show ?thesis
    apply (subst measurable_cong[where g="(\<lambda>\<omega>. if \<omega> \<in> space source - N then ?Lim \<omega> else default)"])
    unfolding X_tilde_def by auto
qed

lemma X_eq_X_tilde_AE: "AE \<omega> in source. X t \<omega> = X_tilde t \<omega>" if "t \<in> {0..T}" for t
  apply (rule sigma_finite_measure.tendsto_measure_at_within_eq_AE[where f="process X" and S="dyadic_interval 0 T"])
  using proc_source.sigma_finite_measure_axioms apply blast
  using X_borel_measurable apply blast
      apply measurable
  using X_tilde_def apply simp
  using that apply simp
  using tendsto_measure_mono[OF at_le[OF dyadic_interval_subset_interval] conv_in_prob_finite] that
    apply force
  using X_borel_measurable X_tilde_measurable X_tilde_tendsto_AE measure_conv_imp_AE_at_within that apply blast
  using dyadic_interval_islimpt that trivial_limit_within zero_le_T by blast

lemma X_tilde_modification: "modification (restrict_index X {0..T})
   (prob_space.process_of source (proc_target X) {0..T} X_tilde default)"
  apply (intro modificationI compatibleI)
     apply simp_all
  apply (subst restrict_index_source)
  apply (auto simp: X_eq_X_tilde_AE)
  done
end

text \<open> We have now shown that we can construct a modification of $X$ for any interval $\{0..T\}$. We want
  to extend this result to construct a modification on the interval $\{0..\}$ - this can be constructed
  by gluing together all modifications with natural-valued T which results in a countable union of
  modifications, which itself is a modification. \<close>

context Kolmogorov_Chentsov
begin

lemma Kolmogorov_Chentsov_finite: "T > 0 \<Longrightarrow> Kolmogorov_Chentsov_finite X a b C \<gamma> T"
  by (simp add: Kolmogorov_Chentsov_axioms Kolmogorov_Chentsov_finite.intro Kolmogorov_Chentsov_finite_axioms_def)

definition "Mod \<equiv> \<lambda>T. SOME Y. modification (restrict_index X {0..T}) Y \<and> 
    (\<forall>x\<in>space source. local_holder_on \<gamma> {0..T} (\<lambda>t. Y t x))"

lemma Mod: "modification (restrict_index X {0..T}) (Mod T)"
  "(\<forall>x\<in>space source. local_holder_on \<gamma> {0..T} (\<lambda>t. (Mod T) t x)) " if "0 < T" for T
proof -
  interpret Kolmogorov_Chentsov_finite X a b C \<gamma> T
    using that by (simp add: Kolmogorov_Chentsov_finite)
  have "modification (restrict_index X {0..T}) (Mod T) \<and> 
    (\<forall>x\<in>space source. local_holder_on \<gamma> {0..T} (\<lambda>t. (Mod T) t x))"
    unfolding Mod_def apply (rule someI_ex)
    apply (rule exI[where x="prob_space.process_of source (proc_target X) {0..T} X_tilde default"])    
    apply safe
     apply (fact X_tilde_modification)
    apply (subst local_holder_on_cong[OF refl refl])
    using local_holder_X_tilde X_tilde_measurable apply (auto cong: local_holder_on_cong)
    done
  then show "modification (restrict_index X {0..T}) (Mod T)"
    "(\<forall>x\<in>space source. local_holder_on \<gamma> {0..T} (\<lambda>t. (Mod T) t x)) " 
    by blast+
qed

lemma compatible_Mod: "compatible (restrict_index X {0..T}) (Mod T)" if "0 < T" for T
  using Mod that modificationD(1) by blast

lemma Mod_source[simp]: "proc_source (Mod T) = source"  if "0 < T" for T
  by (metis compatible_Mod compatible_source restrict_index_source that)

lemma Mod_target: "sets (proc_target (Mod T)) = sets (proc_target X)"  if "0 < T" for T
  by (metis compatible_Mod[OF that] compatible_target restrict_index_target)

lemma Mod_index[simp]: "0 < T \<Longrightarrow> proc_index (Mod T) = {0..T}"
  using compatible_Mod[THEN compatible_index] by simp

lemma indistinguishable_mod:
  "indistinguishable (restrict_index (Mod S) {0..min S T}) (restrict_index (Mod T) {0..min S T})"
  if "S > 0" "T > 0" for S T
proof -
  have *: "modification (restrict_index (Mod S) {0..min S T}) (restrict_index (Mod T) {0..min S T})"
  proof -
    have "modification (restrict_index X {0..min S T}) (restrict_index (Mod S) {0..min S T})"
      apply (cases "S \<le> T")
      using Mod(1)[OF that(1)] apply clarsimp
       apply (metis modification_restrict_index order_refl restrict_index_index restrict_index_override)
      using Mod(1)[OF that(2)] apply clarsimp
      by (metis (mono_tags, opaque_lifting) \<open>modification (restrict_index X {0..S}) (Mod S)\<close> atLeastatMost_subset_iff modification_restrict_index nle_le restrict_index_index restrict_index_override)
    moreover have "modification (restrict_index X {0..min S T}) (restrict_index (Mod T) {0..min S T})"
      apply (cases "S \<le> T")
      using Mod(1)[OF that(1)] apply clarsimp
       apply (metis Mod(1) atLeastatMost_subset_iff modification_restrict_index order.refl restrict_index_index restrict_index_override that(2))
      using Mod(1)[OF that(2)] apply clarsimp
      by (metis (mono_tags, opaque_lifting) atLeastatMost_subset_iff modification_restrict_index nle_le restrict_index_index restrict_index_override)
    ultimately show ?thesis
      using modification_sym modification_trans by metis
  qed
  then show ?thesis
  proof (rule modification_continuous_indistinguishable,
      goal_cases _ continuous_S continuous_T)
    show "\<exists>Ta>0. proc_index (restrict_index (Mod S) {0..min S T}) = {0..Ta}"
      by (metis that min_def restrict_index_index)
  next
    case (continuous_S)
    have "\<forall>x \<in> space source. continuous_on {0..S} (\<lambda>t. (Mod S) t x)"
      using Mod[OF that(1)] local_holder_imp_continuous by blast
    then have "\<forall>x \<in> space source. continuous_on {0..min S T} (\<lambda>t. (Mod S) t x)"
      using continuous_on_subset by fastforce
    then show ?case
      by (auto simp: that(1))
  next
    case (continuous_T)
    have "\<forall>x \<in> space source. continuous_on {0..T} (\<lambda>t. (Mod T) t x)"
      using Mod[OF that(2)] local_holder_imp_continuous by fast
    then have 2: "\<forall>x \<in> space source. continuous_on {0..min S T} (\<lambda>t. (Mod T) t x)"
      using continuous_on_subset by fastforce
    then show ?case
      by (auto simp: that(2))
  qed
qed

definition "N S T \<equiv> SOME N. N \<in> null_sets source \<and> {\<omega> \<in> space source. \<exists>t \<in> {0..min S T}. (Mod S) t \<omega> \<noteq> (Mod T) t \<omega>} \<subseteq> N" 

lemma N:
  assumes "S > 0" "T > 0"
  shows "N S T \<in> null_sets source \<and> {\<omega> \<in> space source. \<exists>t \<in> {0..min S T}. (Mod S) t \<omega> \<noteq> (Mod T) t \<omega>} \<subseteq> N S T"
proof -
  have ex: "\<forall>S > 0. \<forall>T > 0. \<exists>N. N \<in> null_sets source \<and> {\<omega> \<in> space source. \<exists>t \<in> {0..min S T}.
   (Mod S) t \<omega> \<noteq> (Mod T) t \<omega>} \<subseteq> N"
    apply (fold Bex_def)
    using indistinguishable_mod[THEN indistinguishable_null_ex] by simp
  show ?thesis
    unfolding N_def apply (rule someI_ex)
    using ex assms by blast
qed

definition N_inf where "N_inf \<equiv> (\<Union>S \<in> \<nat> - {0}. (\<Union> T \<in> \<nat> - {0}. N S T))"

lemma N_inf_null: "N_inf \<in> null_sets source"
  unfolding N_inf_def
  apply (intro null_sets_UN')
    apply (rule countable_Diff)
    apply (simp add: Nats_def)+
  using N by force

lemma Mod_eq_N_inf: "(Mod S) t \<omega> = (Mod T) t \<omega>"
  if "\<omega> \<in> space source - N_inf" "t \<in> {0..min S T}" "S \<in> \<nat> - {0}" "T \<in> \<nat> - {0}" for \<omega> t S T
proof -
  have "\<omega> \<in> space source - N S T"
    using that(1,3,4) unfolding N_inf_def by blast
  moreover have "S > 0" "T > 0"
    using that(2,3,4) by auto
  ultimately have "\<omega> \<in> {\<omega> \<in> space source. \<forall>t \<in>{0..min S T}. (Mod S) t \<omega> = (Mod T) t \<omega>}"
    using N by auto
  then show ?thesis
    using that(2) by blast
qed

definition default :: 'b where "default = (SOME x. True)"

definition "X_mod \<equiv> \<lambda>t \<omega>. if \<omega> \<in> space source - N_inf then (Mod \<lfloor>t+1\<rfloor>) t \<omega> else default"

definition "X_mod_process \<equiv> prob_space.process_of source (proc_target X) {0..} X_mod default" 

lemma Mod_measurable[measurable]: "\<forall>t\<in>{0..}. X_mod t \<in> source \<rightarrow>\<^sub>M proc_target X"
proof (intro ballI)
  fix t :: real assume "t \<in> {0..}"
  then have "0 < \<lfloor>t + 1\<rfloor>"
    by force
  then show "X_mod t \<in> source \<rightarrow>\<^sub>M proc_target X"
    unfolding X_mod_def apply measurable
      apply (subst measurable_cong_sets[where M'= "proc_source (Mod \<lfloor>t + 1\<rfloor>)" and N' = "proc_target (Mod \<lfloor>t + 1\<rfloor>)"])
    using Mod_source \<open>0 < \<lfloor>t + 1\<rfloor>\<close> apply presburger
    using Mod_target \<open>0 < \<lfloor>t + 1\<rfloor>\<close> apply presburger
      apply (meson random_process)
     apply simp
    apply (metis N_inf_null Int_def null_setsD2 sets.Int_space_eq1 sets.compl_sets)
    done
qed

lemma modification_X_mod_process: "modification X X_mod_process"
proof (intro modificationI ballI)
  show "compatible X X_mod_process"
    apply (intro compatibleI)
    unfolding X_mod_process_def
      apply (subst proc_source.source_process_of)
    using Mod_measurable proc_source.prob_space_axioms apply auto
    done
  fix t assume "t \<in> proc_index X"
  then have "t \<in> {0..}"
    by simp
  then have "real_of_int \<lfloor>t\<rfloor> + 1 > 0"
    by (simp add: add.commute add_pos_nonneg)
  then have "\<exists>N \<in> null_sets source. \<forall>\<omega> \<in> space source - N. 
      X t \<omega> = (prob_space.process_of source (proc_target X) {0..} X_mod default) t \<omega>"
  proof -
    have 1: "(prob_space.process_of source (proc_target X) {0..} X_mod default) t \<omega> = (Mod (real_of_int \<lfloor>t\<rfloor> + 1)) t \<omega>"
      if "\<omega> \<in> space source - N_inf" for \<omega>
      apply (subst proc_source.process_process_of)
        apply measurable
      unfolding X_mod_def using that \<open>t \<in> {0..}\<close> apply simp
      done
    have "\<exists>N \<in> null_sets source. \<forall>\<omega> \<in> space source - N. X t \<omega> = (Mod (real_of_int \<lfloor>t\<rfloor> + 1)) t \<omega>"
    proof -
      obtain N where "{x \<in> space source. (restrict_index X {0..real_of_int \<lfloor>t\<rfloor> + 1}) t x \<noteq> (Mod (real_of_int \<lfloor>t\<rfloor> + 1)) t x} \<subseteq> N \<and>
    N \<in> null_sets (proc_source (restrict_index X {0..(real_of_int \<lfloor>t\<rfloor> + 1)}))"
        using Mod(1)[OF \<open>real_of_int \<lfloor>t\<rfloor> + 1 > 0\<close>, THEN modification_null_set, of t]
        using \<open>t \<in> {0..}\<close> by fastforce
      then show ?thesis
        by (smt (verit, ccfv_threshold) DiffE mem_Collect_eq restrict_index_process restrict_index_source subset_eq)
    qed
    then obtain N where "N \<in> null_sets source" "\<forall>\<omega> \<in> space source - N. X t \<omega> = (Mod (real_of_int \<lfloor>t\<rfloor> + 1)) t \<omega>"
      by blast
    then show ?thesis
      apply (intro bexI[where x="N \<union> N_inf"])
       apply (metis 1 DiffE DiffI UnCI)
      using N_inf_null by blast
  qed
  then show "AE x in source. X t x = X_mod_process t x"
    by (smt (verit, del_insts) X_mod_process_def DiffI eventually_ae_filter mem_Collect_eq subsetI)
qed

lemma local_holder_X_mod: "local_holder_on \<gamma> {0..} (\<lambda>t. X_mod t \<omega>)" for \<omega>
proof (cases "\<omega> \<in> space source - N_inf")
  case False
  then show ?thesis
    apply (simp only: X_mod_def)
    apply (metis local_holder_const gamma_0_1)
    done
next
  case True
  then have \<omega>: "\<omega> \<in> space source" "\<omega> \<notin> N_inf"
    by simp_all
  then show ?thesis
  proof (intro local_holder_ballI[OF gamma_0_1] ballI)
    fix t::real assume "t \<in> {0..}"
    then have "real_of_int \<lfloor>t\<rfloor> + 1 > 0"
      using floor_le_iff by force
    have "t < real_of_int \<lfloor>t\<rfloor> + 1"
      by simp
    then have "local_holder_on \<gamma> {0..real_of_int \<lfloor>t\<rfloor> + 1} (\<lambda>s. Mod (real_of_int \<lfloor>t\<rfloor> + 1) s \<omega>)"
      using Mod(2) \<omega>(1) \<open>real_of_int \<lfloor>t\<rfloor> + 1 > 0\<close> by blast
    then obtain \<epsilon> C where eC: "\<epsilon> > 0" "C \<ge> 0" "\<And>r s. r \<in> ball t \<epsilon> \<inter> {0..real_of_int \<lfloor>t\<rfloor> + 1} \<Longrightarrow>
       s \<in> ball t \<epsilon> \<inter> {0..real_of_int \<lfloor>t\<rfloor> + 1} \<Longrightarrow>
       dist (Mod (real_of_int \<lfloor>t\<rfloor> + 1) r \<omega>) (Mod (real_of_int \<lfloor>t\<rfloor> + 1) s \<omega>) \<le> C * dist r s powr \<gamma>"
      apply -
      apply (erule local_holder_onE)
        apply (rule gamma_0_1)
      using \<open>t \<in> {0..}\<close> \<open>t < real_of_int \<lfloor>t\<rfloor> + 1\<close> apply fastforce
      apply blast
      done
    define \<epsilon>' where "\<epsilon>' = min \<epsilon> (if frac t = 0 then 1/2 else 1 - frac t)"
    have e': "\<epsilon>' \<le> \<epsilon> \<and> \<epsilon>' > 0 \<and> ball t \<epsilon>' \<inter> {0..} \<subseteq> {0..real_of_int \<lfloor>t\<rfloor> + 1}"
      unfolding \<epsilon>'_def apply (simp add: eC(1))
      apply safe
        apply (simp_all add: eC(1) dist_real_def frac_lt_1 frac_floor)
       apply argo+
      done
    {
      fix r s
      assume r:  "r \<in> ball t \<epsilon>' \<inter> {0..}"
      assume s:  "s \<in> ball t \<epsilon>' \<inter> {0..}"

      then have rs_ball: "r \<in> ball t \<epsilon> \<inter> {0..real_of_int \<lfloor>t\<rfloor> + 1}"
        "s \<in> ball t \<epsilon> \<inter> {0..real_of_int \<lfloor>t\<rfloor> + 1}"
        using e' r s by auto
      then have "r \<in> {0..min (real_of_int \<lfloor>t\<rfloor> + 1) (real_of_int \<lfloor>r + 1\<rfloor>)}"
        by auto
      then have "(Mod (real_of_int \<lfloor>t\<rfloor> + 1)) r \<omega> = X_mod r \<omega>"
        unfolding X_mod_def apply (simp only: True if_True)
        apply (intro Mod_eq_N_inf[OF True])
          apply simp
        using \<open>t \<in> {0..}\<close> by auto
           (metis (no_types, opaque_lifting) floor_in_Nats Nats_1 Nats_add Nats_cases 
            of_int_of_nat_eq of_nat_in_Nats, linarith)+
      moreover have "(Mod (real_of_int \<lfloor>t\<rfloor> + 1)) s \<omega> = X_mod s \<omega>"
        unfolding X_mod_def apply (simp only: True if_True)
        apply (intro Mod_eq_N_inf[OF True])
        using \<open>s \<in> ball t \<epsilon> \<inter> {0..real_of_int \<lfloor>t\<rfloor> + 1}\<close> apply simp
        using \<open>t \<in> {0..}\<close> apply safe
           apply (metis (no_types, opaque_lifting) floor_in_Nats Nats_1 Nats_add Nats_cases of_int_of_nat_eq of_nat_in_Nats)
          apply linarith
         apply (smt (verit) Int_iff Nats_1 Nats_add Nats_altdef1 atLeast_iff mem_Collect_eq s zero_le_floor)
        apply (metis Int_iff atLeast_iff floor_correct linorder_not_less one_add_floor s)
        done
      ultimately have "dist (X_mod r \<omega>) (X_mod s \<omega>) \<le> C * dist r s powr \<gamma>"
        using eC(3)[OF rs_ball] by simp
    }
    then show "\<exists>\<epsilon>>0. \<exists>C\<ge>0. \<forall>r\<in>ball t \<epsilon> \<inter> {0..}. \<forall>s\<in>ball t \<epsilon> \<inter> {0..}. dist (X_mod r \<omega>) (X_mod s \<omega>) \<le> C * dist r s powr \<gamma>"
      using e' eC(2) by blast
  qed
qed

lemma local_holder_X_mod_process: "local_holder_on \<gamma> {0..} (\<lambda>t. X_mod_process t \<omega>)" for \<omega>
  unfolding X_mod_process_def
  by (smt (verit, best) Mod_measurable UNIV_I local_holder_X_mod local_holder_on_cong
      proc_source.process_process_of space_borel target_borel)

theorem continuous_modification:
  "\<exists>X'. modification X X' \<and> (\<forall>\<omega>. local_holder_on \<gamma> {0..} (\<lambda>t. X' t \<omega>))"
  apply (rule exI[where x=X_mod_process])
  using local_holder_X_mod_process modification_X_mod_process by auto
end

theorem Kolmogorov_Chentsov:
  fixes X :: "(real, 'a, 'b :: polish_space) stochastic_process"
    and a b C \<gamma> :: real
  assumes index[simp]: "proc_index X = {0..}"
    and target_borel[simp]: "proc_target X = borel"
    and gt_0: "a > 0" "b > 0" "C > 0"
    and b_leq_a: "b \<le> a"
    and gamma: "\<gamma> \<in> {0<..<b/a}"
    and expectation: "\<And>s t. \<lbrakk>s \<ge> 0; t \<ge> 0\<rbrakk> \<Longrightarrow>
          (\<integral>\<^sup>+ x. dist (X t x) (X s x) powr a \<partial>proc_source X) \<le> C * dist t s powr (1+b)"
  shows "\<exists>X'. modification X X' \<and> (\<forall>\<omega>. local_holder_on \<gamma> {0..} (\<lambda>t. X' t \<omega>))"
  using Kolmogorov_Chentsov.continuous_modification Kolmogorov_Chentsov.intro[OF assms]
  by blast
end
