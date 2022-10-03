section \<open>\<open>Extra_Operator_Norm\<close> -- Additional facts bout the operator norm\<close>

theory Extra_Operator_Norm
  imports "HOL-Analysis.Operator_Norm"
    Extra_General
    "HOL-Analysis.Bounded_Linear_Function"
    Extra_Vector_Spaces
begin


text \<open>This theorem complements \<^theory>\<open>HOL-Analysis.Operator_Norm\<close>
      additional useful facts about operator norms.\<close>

lemma onorm_sphere:
  fixes f :: "'a::{real_normed_vector, not_singleton} \<Rightarrow> 'b::real_normed_vector"
  assumes a1: "bounded_linear f"
  shows \<open>onorm f = Sup {norm (f x) | x. norm x = 1}\<close>
proof(cases \<open>f = (\<lambda> _. 0)\<close>)
  case True
  have \<open>(UNIV::'a set) \<noteq> {0}\<close>
    by simp
  hence \<open>\<exists>x::'a. norm x = 1\<close>
    using  ex_norm1
    by blast
  have \<open>norm (f x) = 0\<close>
    for x
    by (simp add: True)
  hence \<open>{norm (f x) | x. norm x = 1} = {0}\<close>
    using \<open>\<exists>x. norm x = 1\<close> by auto
  hence v1: \<open>Sup {norm (f x) | x. norm x = 1} = 0\<close>
    by simp
  have \<open>onorm f = 0\<close>
    by (simp add: True onorm_eq_0)
  thus ?thesis using v1 by simp
next
  case False
  have \<open>y \<in> {norm (f x) |x. norm x = 1} \<union> {0}\<close>
    if "y \<in> {norm (f x) / norm x |x. True}"
    for y
  proof(cases \<open>y = 0\<close>)
    case True
    thus ?thesis
      by simp
  next
    case False
    have \<open>\<exists> x. y = norm (f x) / norm x\<close>
      using \<open>y \<in> {norm (f x) / norm x |x. True}\<close> by auto
    then obtain x where \<open>y = norm (f x) / norm x\<close>
      by blast
    hence \<open>y = \<bar>(1/norm x)\<bar> * norm ( f x )\<close>
      by simp
    hence \<open>y = norm ( (1/norm x) *\<^sub>R f x )\<close>
      by simp
    hence \<open>y = norm ( f ((1/norm x) *\<^sub>R x) )\<close>
      apply (subst linear_cmul[of f])
      by (simp_all add: assms bounded_linear.linear)
    moreover have \<open>norm ((1/norm x) *\<^sub>R x) = 1\<close>
      using False \<open>y = norm (f x) / norm x\<close> by auto
    ultimately have \<open>y \<in> {norm (f x) |x. norm x = 1}\<close>
      by blast
    thus ?thesis by blast
  qed
  moreover have "y \<in> {norm (f x) / norm x |x. True}"
    if \<open>y \<in> {norm (f x) |x. norm x = 1} \<union> {0}\<close>
    for y
  proof(cases \<open>y = 0\<close>)
    case True
    thus ?thesis
      by auto
  next
    case False
    hence \<open>y \<notin> {0}\<close>
      by simp
    hence \<open>y \<in> {norm (f x) |x. norm x = 1}\<close>
      using that by auto
    hence \<open>\<exists> x. norm x = 1 \<and> y = norm (f x)\<close>
      by auto
    then obtain x where \<open>norm x = 1\<close> and \<open>y = norm (f x)\<close>
      by auto
    have \<open>y = norm (f x) / norm x\<close> using  \<open>norm x = 1\<close>  \<open>y = norm (f x)\<close>
      by simp
    thus ?thesis
      by auto
  qed
  ultimately have \<open>{norm (f x) / norm x |x. True} = {norm (f x) |x. norm x = 1} \<union> {0}\<close>
    by blast
  hence \<open>Sup {norm (f x) / norm x |x. True} = Sup ({norm (f x) |x. norm x = 1} \<union> {0})\<close>
    by simp
  moreover have \<open>Sup {norm (f x) |x. norm x = 1} \<ge> 0\<close>
  proof-
    have \<open>\<exists> x::'a. norm x = 1\<close>
      by (metis (full_types) False assms linear_simps(3) norm_sgn)
    then obtain x::'a where \<open>norm x = 1\<close>
      by blast
    have \<open>norm (f x) \<ge> 0\<close>
      by simp
    hence \<open>\<exists> x::'a. norm x = 1 \<and> norm (f x) \<ge> 0\<close>
      using \<open>norm x = 1\<close> by blast
    hence \<open>\<exists> y \<in> {norm (f x) |x. norm x = 1}. y \<ge> 0\<close>
      by blast
    then obtain y::real where \<open>y \<in> {norm (f x) |x. norm x = 1}\<close>
      and \<open>y \<ge> 0\<close>
      by auto
    have \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close>
      using \<open>y \<in> {norm (f x) |x. norm x = 1}\<close> by blast
    moreover have \<open>bdd_above {norm (f x) |x. norm x = 1}\<close>
      using bdd_above_norm_f
      by (metis (mono_tags, lifting) a1)
    ultimately have \<open>y \<le> Sup {norm (f x) |x. norm x = 1}\<close>
      using \<open>y \<in> {norm (f x) |x. norm x = 1}\<close>
      by (simp add: cSup_upper)
    thus ?thesis using \<open>y \<ge> 0\<close> by simp
  qed
  moreover have \<open>Sup ({norm (f x) |x. norm x = 1} \<union> {0}) = Sup {norm (f x) |x. norm x = 1}\<close>
  proof-
    have \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close>
      by (simp add: assms(1) ex_norm1)
    moreover have \<open>bdd_above {norm (f x) |x. norm x = 1}\<close>
      using a1 bdd_above_norm_f by force
    have \<open>{0::real} \<noteq> {}\<close>
      by simp
    moreover have \<open>bdd_above {0::real}\<close>
      by simp
    ultimately have \<open>Sup ({norm (f x) |x. norm x = 1} \<union> {(0::real)})
             = max (Sup {norm (f x) |x. norm x = 1}) (Sup {0::real})\<close>
      by (metis (lifting) \<open>0 \<le> Sup {norm (f x) |x. norm x = 1}\<close> \<open>bdd_above {0}\<close> \<open>bdd_above {norm (f x) |x. norm x = 1}\<close> \<open>{0} \<noteq> {}\<close> \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close> cSup_singleton cSup_union_distrib max.absorb_iff1 sup.absorb_iff1)
    moreover have \<open>Sup {(0::real)} = (0::real)\<close>
      by simp
    moreover have \<open>Sup {norm (f x) |x. norm x = 1} \<ge> 0\<close>
      by (simp add: \<open>0 \<le> Sup {norm (f x) |x. norm x = 1}\<close>)
    ultimately show ?thesis
      by simp
  qed
  moreover have \<open>Sup ( {norm (f x) |x. norm x = 1} \<union> {0})
           = max (Sup {norm (f x) |x. norm x = 1}) (Sup {0}) \<close>
    using calculation(2) calculation(3) by auto
  ultimately have w1: "Sup {norm (f x) / norm x | x. True} = Sup {norm (f x) | x. norm x = 1}"
    by simp

  have \<open>(SUP x. norm (f x) / (norm x)) = Sup {norm (f x) / norm x | x. True}\<close>
    by (simp add: full_SetCompr_eq)
  also have \<open>... = Sup {norm (f x) | x. norm x = 1}\<close>
    using w1 by auto
  ultimately  have \<open>(SUP x. norm (f x) / (norm x)) = Sup {norm (f x) | x. norm x = 1}\<close>
    by linarith
  thus ?thesis unfolding onorm_def by blast
qed

lemma onormI:
  assumes "\<And>x. norm (f x) \<le> b * norm x"
    and "x \<noteq> 0" and "norm (f x) = b * norm x"
  shows "onorm f = b"
  apply (unfold onorm_def, rule cSup_eq_maximum)
   apply (smt (verit) UNIV_I assms(2) assms(3) image_iff nonzero_mult_div_cancel_right norm_eq_zero)
  by (smt (verit, del_insts) assms(1) assms(2) divide_nonneg_nonpos norm_ge_zero norm_le_zero_iff pos_divide_le_eq rangeE zero_le_mult_iff)

end
