section \<open>Completions of Normed Vector Spaces\<close>

theory Inner_Completion
imports
  Complex_Bounded_Operators.Complex_Inner_Product
  Gromov_Hyperbolicity.Metric_Completion
begin


subsection \<open>Helper lemmas\<close>

lemma Cauchy_norm_bounded:
  assumes "Cauchy X"
  shows "\<exists>B. \<forall>n. norm (X n) < B"
  by (meson cauchy_imp_bounded assms bounded_normE_less rangeI)

lemma convergent_Cauchy_norm:
  fixes u v::"nat \<Rightarrow> ('a::real_normed_vector)"
  assumes "Cauchy u"
  shows "convergent (\<lambda>n. norm (u n))"
  unfolding norm_conv_dist using convergent_Cauchy_dist assms convergent_Cauchy convergent_const
  by blast

lemma Cauchy_norm_if_Cauchy:
  assumes "Cauchy u"
  shows "Cauchy (\<lambda>n. norm (u n))"
  unfolding norm_conv_dist
  using assms convergent_Cauchy convergent_Cauchy_norm by auto

lemma lim_ge: "convergent f \<Longrightarrow> (\<And>n. f n \<ge> x) \<Longrightarrow> lim f \<ge> x"
  for x :: "'a::linorder_topology"
  using LIMSEQ_le_const[of f "lim f" x] by (simp add: convergent_LIMSEQ_iff)

lemma
  assumes "convergent u"
  shows lim_Re: "lim (\<lambda>n. Re (u n)) = Re (lim (\<lambda>n. u n))"
    and lim_Im: "lim (\<lambda>n. Im (u n)) = Im (lim (\<lambda>n. u n))"
  by (intro limI tendsto_Re tendsto_Im, simp add: assms[unfolded convergent_LIMSEQ_iff])+

lemma Cauchy_sum:
  fixes x1 x2 :: "nat\<Rightarrow>'a::real_normed_vector"
  assumes "Cauchy x1" "Cauchy x2"
  shows "Cauchy (x1+x2)"
proof (unfold Cauchy_def[of "x+y" for x y], intro allI impI)
  fix e::real
  assume "0 < e"
  then
  obtain M1 M3
    where M: "\<forall>m\<ge>M1. \<forall>n\<ge>M1. dist ((x1) m) ((x1) n) < e/2"
             "\<forall>m\<ge>M3. \<forall>n\<ge>M3. dist ((x2) m) ((x2) n) < e/2"
    using zero_less_divide_iff zero_less_numeral
    by (metis Cauchy_def assms)
  let ?M = "if M1\<ge>M3 then M1 else M3"
  { fix m n assume "m\<ge>?M" "n\<ge>?M"
    hence mn: "m\<ge>M1" "n\<ge>M1" "m\<ge>M3" "n\<ge>M3" by presburger+
    have "norm (x1 n - x1 m) + norm (x2 m - x2 n) < e"
      using M mn unfolding dist_norm by fastforce
    hence "norm ((x1 + x2) m - (x1 + x2) n) < e"
      unfolding plus_fun_apply 
      by (metis add.commute add_diff_eq diff_diff_eq norm_minus_commute norm_triangle_lt)
    hence "dist ((x1 + x2) m) ((x1 + x2) n) < e"
      unfolding dist_norm by blast }
  thus "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist ((x1 + x2) m) ((x1 + x2) n) < e"
    by blast
qed


subsection \<open>The Cauchy completion of a normed vector space is a Banach space.\<close>

instantiation metric_completion :: (real_normed_vector) scaleR
begin
lift_definition scaleR_metric_completion :: "real \<Rightarrow> 'a metric_completion \<Rightarrow> 'a metric_completion"
  is "\<lambda>r x. \<lambda>n. (scaleR r) (x n)"
  using bounded_linear.Cauchy bounded_linear_scaleR_right tendsto_mult_right_zero
  by (auto simp add: scaleR_diff_right[symmetric] dist_norm)
instance by standard
end

instantiation metric_completion :: (real_normed_vector) real_vector
begin

lift_definition uminus_metric_completion :: "'a metric_completion \<Rightarrow> 'a metric_completion"
  is uminus
  by (simp add: Cauchy_def dist_minus)

lift_definition zero_metric_completion :: "'a metric_completion"
  is "\<lambda>n. 0"
  by (simp add: Cauchy_def)

lift_definition plus_metric_completion ::
    "'a metric_completion \<Rightarrow> 'a metric_completion \<Rightarrow> 'a metric_completion"
  is plus
proof (intro conjI; elim conjE)
  fix x1 x2 x3 x4 :: "nat \<Rightarrow> 'a"
  assume cauchy: "Cauchy x1" "Cauchy x2" "Cauchy x3" "Cauchy x4"
  assume dist_conv: "(\<lambda>n. dist (x1 n) (x2 n)) \<longlonglongrightarrow> 0" "(\<lambda>n. dist (x3 n) (x4 n)) \<longlonglongrightarrow> 0"
  show cauchy_sum: "Cauchy (x1 + x3)" "Cauchy (x2 + x4)"
    using Cauchy_sum cauchy by auto
  show "(\<lambda>n. dist ((x1 + x3) n) ((x2 + x4) n)) \<longlonglongrightarrow> 0"
  proof -
    have dist_conv_add: "(\<lambda>n. dist (x1 n) (x2 n) + dist (x3 n) (x4 n)) \<longlonglongrightarrow> 0"
      using dist_conv tendsto_add by fastforce
    show ?thesis
      apply (rule tendsto_sandwich[of "\<lambda>_. 0" _ _ "\<lambda>n. dist (x1 n) (x2 n) + dist (x3 n) (x4 n)"])
      using dist_conv_add by (auto simp: dist_triangle_add)
  qed
qed

definition minus_metric_completion ::
    "'a metric_completion \<Rightarrow> 'a metric_completion \<Rightarrow> 'a metric_completion"
    where "minus_metric_completion a b \<equiv> a + (-b)"

instance
  apply intro_classes
  subgoal by (transfer, simp add: Cauchy_sum Groups.add_ac)
  subgoal by (transfer, simp add: Groups.add_ac Cauchy_sum)
  subgoal apply transfer by (transfer, simp add: plus_fun_def)
  subgoal by (transfer, simp add: Cauchy_def)
  subgoal by (simp add: minus_metric_completion_def)
  subgoal apply (transfer, auto)
    subgoal using Cauchy_sum bounded_linear.Cauchy
        bounded_linear_scaleR_right by fastforce
    subgoal by (simp add: Cauchy_sum bounded_linear.Cauchy bounded_linear_scaleR_right)
    subgoal by (simp add: scaleR_add_right)
    done
  subgoal apply (transfer, auto)
    using bounded_linear.Cauchy bounded_linear_scaleR_right apply blast
    using bounded_linear.Cauchy bounded_linear_scaleR_right apply (metis Cauchy_sum)
    using dist_self scaleR_add_left by (metis (mono_tags, lifting) LIMSEQ_def)
  subgoal by (transfer, simp add: bounded_linear.Cauchy bounded_linear_scaleR_right)
  subgoal by (transfer, simp)
  done
end


instantiation metric_completion :: (complex_normed_vector) scaleC
begin
lift_definition scaleC_metric_completion :: "complex \<Rightarrow> 'a metric_completion \<Rightarrow> 'a metric_completion"
  is "\<lambda>c x. \<lambda>n. (scaleC c) (x n)"
  using bounded_clinear.Cauchy bounded_clinear_scaleC_right tendsto_mult_right_zero
  by (auto simp add: scaleC_diff_right[symmetric] dist_norm)
instance
  apply intro_classes
  unfolding scaleR_metric_completion_def scaleC_metric_completion_def
  by (simp add: scaleR_scaleC)
end

instance metric_completion :: (complex_normed_vector) complex_vector
  apply intro_classes
  subgoal apply (transfer, auto)
    subgoal using Inner_Completion.Cauchy_sum bounded_clinear.Cauchy
        bounded_clinear_scaleC_right by fastforce
    subgoal by (simp add: Cauchy_sum bounded_clinear.Cauchy bounded_clinear_scaleC_right)
    subgoal by (simp add: scaleC_add_right)
    done
  subgoal apply (transfer, auto)
    using bounded_clinear.Cauchy bounded_clinear_scaleC_right apply blast
    using bounded_clinear.Cauchy bounded_clinear_scaleC_right apply (metis Cauchy_sum)
    using dist_self scaleC_add_left by (metis (mono_tags, lifting) LIMSEQ_def)
  subgoal by (transfer, simp add: bounded_clinear.Cauchy bounded_clinear_scaleC_right)
  subgoal by (transfer, simp)
  done

instantiation metric_completion :: (real_normed_vector) banach
begin

lift_definition norm_metric_completion :: "'a metric_completion \<Rightarrow> real"
  is "\<lambda>X. lim (\<lambda>n. norm (X n))"
  unfolding dist_norm
  apply (rule convergent_add_null(2))
  subgoal using convergent_Cauchy_dist zero_metric_completion.rsp by force
  using Lim_null_comparison eventually_sequentially norm_triangle_ineq3
  by (metis (mono_tags, lifting) real_norm_def)

definition sgn_metric_completion :: "'a metric_completion \<Rightarrow> 'a metric_completion"
  where "sgn_metric_completion x = x /\<^sub>R norm x"

lemma metric_completion_triangle_ineq:
  fixes x y :: "'a metric_completion"
  shows "norm (x + y) \<le> norm x + norm y"
proof -
  have 1: "lim (\<lambda>n. norm (x n + y n)) \<le> lim (\<lambda>n. norm (x n)) + lim (\<lambda>n. norm (y n))"
    if cauchy: "Cauchy x" "Cauchy y"
    for x y :: "nat \<Rightarrow> 'a"
  proof -
    have lim_norm_sum_distrib: "lim (\<lambda>n. norm (x n) + norm (y n)) =
        lim (\<lambda>n. norm (x n)) + lim (\<lambda>n. norm (y n))"
      apply (intro limI)
      apply (rule tendsto_add)
      using cauchy convergent_Cauchy_dist convergent_LIMSEQ_iff zero_metric_completion.rsp
      by fastforce+
    have conv_norm_plus: "convergent (\<lambda>n. norm (x n + y n))"
      apply (simp only: norm_conv_dist)
      apply (intro convergent_Cauchy_dist)
      apply (metis (no_types, lifting) ext Cauchy_sum cauchy(1,2) plus_fun_apply)
      by (simp add: zero_metric_completion.rsp)
    have conv_plus_norm: "convergent (\<lambda>n. norm (x n) + norm (y n))"
      apply (rule convergent_add)
      apply (simp_all only: norm_conv_dist)
      apply (rule convergent_Cauchy_dist[OF cauchy(1) zero_metric_completion.rsp[THEN conjunct1]])
      by (rule convergent_Cauchy_dist[OF cauchy(2) zero_metric_completion.rsp[THEN conjunct1]])
    thus ?thesis
      apply (simp flip: lim_norm_sum_distrib)
      apply (rule lim_mono[of _ "(\<lambda>n. norm (x n + y n))" "(\<lambda>n. norm (x n) + norm (y n))"])
      using conv_norm_plus conv_plus_norm
      by (simp_all add: norm_triangle_ineq convergent_LIMSEQ_iff[symmetric])
  qed
  show ?thesis
    apply transfer
    using 1 by auto
qed

instance
  apply intro_classes \<comment> \<open>Remember to unfold non-lifted definitions before transferring!\<close>
  unfolding minus_metric_completion_def sgn_metric_completion_def
  subgoal by (transfer, simp add: dist_norm)
  subgoal apply (transfer, auto)
    using bounded_linear.Cauchy bounded_linear_scaleR_right by blast
  subgoal apply (transfer, auto)
    subgoal using zero_metric_completion.rsp by blast
    subgoal using convergent_Cauchy_dist convergent_LIMSEQ_iff zero_metric_completion.rsp by force
    subgoal by (simp add: tendsto_Lim)
    done
  subgoal using metric_completion_triangle_ineq .
  subgoal
    apply (transfer, auto)
    apply (intro limI)
    apply (rule tendsto_mult)
     apply blast
    apply (simp only: convergent_LIMSEQ_iff[symmetric] norm_conv_dist)
    apply (rule convergent_Cauchy_dist)
    using zero_metric_completion.rsp by simp_all
  done
end


instance metric_completion :: (complex_normed_vector) cbanach
  apply intro_classes
  apply (transfer, auto)
  apply (intro limI)
  apply (rule tendsto_mult)
   apply blast
  apply (simp only: convergent_LIMSEQ_iff[symmetric] norm_conv_dist)
  apply (rule convergent_Cauchy_dist)
  using zero_metric_completion.rsp by simp_all



subsection \<open>The Cauchy completion of an inner product space is a Hilbert space.\<close>

instantiation metric_completion :: (complex_inner) chilbert_space
begin

lift_definition cinner_metric_completion ::
    "'a metric_completion \<Rightarrow> 'a metric_completion \<Rightarrow> complex"
  is "\<lambda>x y. lim (\<lambda>n. cinner (x n) (y n))"
proof (elim conjE)
  fix x1 x2 x3 x4 :: "nat \<Rightarrow> 'a"
  assume cauchy: "Cauchy x1" "Cauchy x2" "Cauchy x3" "Cauchy x4"
    and dist_conv: "(\<lambda>n. dist (x1 n) (x2 n)) \<longlonglongrightarrow> 0"
      "(\<lambda>n. dist (x3 n) (x4 n)) \<longlonglongrightarrow> 0"

  have 1: "(\<lambda>x. cmod ((x1 x - x2 x) \<bullet>\<^sub>C x3 x)) \<longlonglongrightarrow> 0"
    if cauchy: "Cauchy x1" "Cauchy x2" "Cauchy x3"
      and dist_conv: "(\<lambda>n. dist (x1 n) (x2 n)) \<longlonglongrightarrow> 0"
    for x1 x2 x3 :: "nat \<Rightarrow> 'a"
  proof -
    obtain B where B: "\<forall>n. norm (x3 n) < B"
      using Cauchy_norm_bounded[OF cauchy(3)] by blast
    have *: "(\<lambda>n. norm (x1 n - x2 n) * B) \<longlonglongrightarrow> 0"
      apply (rule tendsto_mult[where a=0 and b=B, simplified])
      by (metis (no_types, lifting) ext dist_conv dist_norm) simp
    have norm_mult_tendsto_0: "(\<lambda>n. norm (x1 n - x2 n) * norm (x3 n)) \<longlonglongrightarrow> 0"
      apply (rule tendsto_sandwich[where f="\<lambda>n. 0" and h="\<lambda>n. norm (x1 n - x2 n) * B"])
      using * B by (simp_all add: less_imp_le mult_left_mono)
    show ?thesis
      apply (rule tendsto_sandwich[where f="\<lambda>n. 0" and h="\<lambda>n. norm (x1 n - x2 n) * norm (x3 n)"])
      by (simp_all add: Cauchy_Schwarz_ineq2 norm_mult_tendsto_0)
  qed

  have 2: "(\<lambda>n. x1 n \<bullet>\<^sub>C x3 n - x2 n \<bullet>\<^sub>C x4 n) \<longlonglongrightarrow> 0"
  proof -
    have *: "x1 n \<bullet>\<^sub>C x3 n - x2 n \<bullet>\<^sub>C x4 n =
        (x1 n - x2 n) \<bullet>\<^sub>C x3 n + x2 n \<bullet>\<^sub>C (x3 n - x4 n)" for n
      by (simp add: cinner_simps(3,4))
    show ?thesis
      apply (simp only: *)
      apply (rule tendsto_add[of _ 0 _ _ 0, simplified]; rule tendsto_norm_zero_cancel)
       apply (rule 1[OF cauchy(1-3) dist_conv(1)])
      apply (subst complex_mod_cnj[symmetric])
      apply (subst cinner_commute[symmetric])
      by (rule 1[OF cauchy(3,4,2) dist_conv(2)])
  qed

  show "lim (\<lambda>n. x1 n \<bullet>\<^sub>C x3 n) = lim (\<lambda>n. x2 n \<bullet>\<^sub>C x4 n)"
    apply (intro convergent_add_null(2))
    using 2 by (simp_all add: Cauchy_cinner_Cauchy cauchy(2,4) complex_Cauchy_convergent)
qed


instance
proof (intro_classes; transfer; elim conjE)
  have conv_cinner_self: "convergent (\<lambda>n. x n \<bullet>\<^sub>C x n)"
    if "Cauchy x" for x :: "nat \<Rightarrow> 'a"
    using Cauchy_cinner_Cauchy Cauchy_convergent_iff that by blast

  fix x :: "nat \<Rightarrow> 'a"
  assume x: "Cauchy x"
  note conv_xx = conv_cinner_self[OF x]

  have "0 \<le> Re (lim (\<lambda>n. x n \<bullet>\<^sub>C x n))"
    unfolding lim_Re[symmetric, OF conv_xx]
    apply (rule lim_ge)
    using cinner_ge_zero less_eq_complex_def
    by (auto simp add: Cauchy_Re Cauchy_cinner_Cauchy real_Cauchy_convergent x)
  moreover have "Im (lim (\<lambda>n. x n \<bullet>\<^sub>C x n)) = 0"
    by (simp add: lim_Im[symmetric, OF conv_xx])
  ultimately show "0 \<le> lim (\<lambda>n. x n \<bullet>\<^sub>C x n)"
    by (simp add: less_eq_complex_def)

  show "lim (\<lambda>n. norm (x n)) = sqrt (cmod (lim (\<lambda>n. x n \<bullet>\<^sub>C x n)))"
    apply (intro limI)
    apply (rule tendsto_real_sqrt[
          where f="\<lambda>n. cmod (x n \<bullet>\<^sub>C x n)" for x n,
          folded norm_eq_sqrt_cinner])
    using Cauchy_cinner_Cauchy convergent_eq_Cauchy limI tendsto_norm x by fastforce

  show "(lim (\<lambda>n. x n \<bullet>\<^sub>C x n) = 0) =
         (Cauchy x \<and> Cauchy (\<lambda>n. 0::'a) \<and> (\<lambda>n. dist (x n) 0) \<longlonglongrightarrow> 0)"
  proof -
    have Cauchy_0: "Cauchy (\<lambda>n. 0::'a)"
      using zero_metric_completion.rsp by simp
    { assume lim_cinner_self: "lim (\<lambda>n. x n \<bullet>\<^sub>C x n) = 0"
      \<comment> \<open>Notice convergence @{thm conv_cinner_self} is proved completely independently!\<close>
      have tendsto_cinner_self: "(\<lambda>n. cmod (x n \<bullet>\<^sub>C x n)) \<longlonglongrightarrow> 0"
        using lim_cinner_self conv_xx unfolding convergent_LIMSEQ_iff
        by (simp add: tendsto_norm_zero)
      have "(\<lambda>n. norm (x n)) \<longlonglongrightarrow> 0"
        unfolding norm_eq_sqrt_cinner[of "x n" for n]
        apply (rule tendsto_real_sqrt[of _ 0, simplified])
        using tendsto_cinner_self . }
    note t0_if_inner_t0 = this
    { assume "(\<lambda>n. norm (x n)) \<longlonglongrightarrow> 0"
      hence "lim (\<lambda>n. x n \<bullet>\<^sub>C x n) = 0"
        apply (intro limI)
        using tendsto_cinner tendsto_norm_zero_cancel by fastforce }
    note inner_t0_if_t0 = this
    show ?thesis
      using t0_if_inner_t0 inner_t0_if_t0 x Cauchy_0 by auto 
  qed

  fix y :: "nat \<Rightarrow> 'a" assume y: "Cauchy y"

  show "lim (\<lambda>n. x n \<bullet>\<^sub>C y n) = cnj (lim (\<lambda>n. y n \<bullet>\<^sub>C x n))"
    apply (intro limI)
    unfolding lim_cnj[of "\<lambda>n. x n \<bullet>\<^sub>C y n" for x y, unfolded cinner_commute', of _ _ _ sequentially]
    using Cauchy_cinner_Cauchy convergent_eq_Cauchy limI x y by blast

  { fix r :: complex
    have "lim (\<lambda>n. cnj r * (x n \<bullet>\<^sub>C y n)) = cnj r * lim (\<lambda>n. x n \<bullet>\<^sub>C y n)"
      apply (intro limI tendsto_mult)
      using Cauchy_cinner_Cauchy convergent_eq_Cauchy limI x y by blast+
    thus "lim (\<lambda>n. r *\<^sub>C x n \<bullet>\<^sub>C y n) = cnj r * lim (\<lambda>n. x n \<bullet>\<^sub>C y n)" by simp }

  fix z :: "nat \<Rightarrow> 'a" assume z: "Cauchy z"
  show "lim (\<lambda>n. ((x + y) n) \<bullet>\<^sub>C z n) = lim (\<lambda>n. x n \<bullet>\<^sub>C z n) + lim (\<lambda>n. y n \<bullet>\<^sub>C z n)"
    apply (simp only: cinner_add_left plus_fun_def)
    apply (intro limI tendsto_add)
    using Cauchy_cinner_Cauchy convergent_eq_Cauchy limI x y z by blast+
qed
end



subsection \<open>The embedding \<^term>\<open>to_metric_completion\<close>\<close>

text \<open>And now we get all sorts of metric lemmas for inner products,
  e.g. an isometry (see @{thm to_metric_completion_isometry}) into
  a dense subset (see @{thm to_metric_completion_dense'}) of a \<^class>\<open>chilbert_space\<close>.
  This isometry is (complex-)linear, and preserves norms and inner products.\<close>
lemma to_metric_completion_linear: "linear to_metric_completion" (is \<open>linear ?g\<close>)
  and to_metric_completion_clinear: "clinear to_metric_completion" (is \<open>clinear ?f\<close>)
proof -
  note plus_abs_mc = plus_metric_completion.abs_eq
        [symmetric, of "\<lambda>n. b1" "\<lambda>n. b2" for b1 b2, simplified, unfolded plus_fun_def]
  have "\<And>r b. ?g (r *\<^sub>R b) = r *\<^sub>R ?g b" "\<And>r b. ?f (r *\<^sub>C b) = r *\<^sub>C ?f b"
    unfolding to_metric_completion_def
    by (simp_all add: Cauchy_def scaleR_metric_completion.abs_eq scaleC_metric_completion.abs_eq)
  moreover have "\<And>b1 b2. ?g (b1 + b2) = ?g b1 + ?g b2" "\<And>b1 b2. ?f (b1 + b2) = ?f b1 + ?f b2"
    unfolding to_metric_completion_def
    by (rule plus_abs_mc; simp add: Cauchy_def)+
  ultimately show "linear ?g" "clinear ?f"
    by unfold_locales (auto)
qed

lemma to_metric_completion_norm:
  shows "norm (to_metric_completion c) = norm c"
  unfolding to_metric_completion_def
  apply (rule norm_metric_completion.abs_eq[of "\<lambda>n. c", simplified])
  by (simp add: Cauchy_def)

lemma to_metric_completion_bounded_clinear:
  shows "bounded_clinear to_metric_completion"
  apply unfold_locales
  apply (simp add: linear_add to_metric_completion_linear)
  apply (simp add: complex_vector.linear_scale to_metric_completion_clinear)
  by (metis mult.right_neutral norm_imp_pos_and_ge to_metric_completion_norm)

lemma to_metric_completion_cinner:
    "(to_metric_completion c) \<bullet>\<^sub>C (to_metric_completion d) = c \<bullet>\<^sub>C d"
  unfolding to_metric_completion_def
  apply (rule cinner_metric_completion.abs_eq[of "\<lambda>n. b1" "\<lambda>n. b2" for b1 b2, simplified])
  by (simp_all add: Cauchy_def)

end
