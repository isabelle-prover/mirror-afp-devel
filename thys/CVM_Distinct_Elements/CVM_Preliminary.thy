section \<open>Preliminary Definitions and Results\<close>

theory CVM_Preliminary
  imports "HOL-Probability.SPMF"
begin

lemma bounded_finite:
  assumes \<open>finite S\<close>
  shows \<open>bounded (f ` S)\<close>
  using assms by (intro finite_imp_bounded) auto

lemma of_bool_power:
  assumes \<open>y > 0\<close>
  shows \<open>(of_bool x::real) ^ (y::nat) = of_bool x\<close>
  by (simp add: assms)

lemma card_filter_mono:
  assumes \<open>finite S\<close>
  shows \<open>card (Set.filter p S) \<le> card S\<close>
  by (intro card_mono assms) auto

fun foldM ::
  \<open>('a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'd list \<Rightarrow> 'b \<Rightarrow> 'c\<close> where
  \<open>foldM _ return' _ [] val = return' val\<close> |
  \<open>foldM bind' return' f (x # xs) val =
    bind' (f x val) (foldM bind' return' f xs)\<close>

abbreviation foldM_pmf ::
  \<open>('a \<Rightarrow> 'b \<Rightarrow> 'b pmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b pmf\<close> where
  \<open>foldM_pmf \<equiv> foldM bind_pmf return_pmf\<close>

lemma foldM_pmf_snoc: \<open>foldM_pmf f (xs@[y]) val = bind_pmf (foldM_pmf f xs val) (f y)\<close>
  by (induction xs arbitrary:val)
    (simp_all add: bind_return_pmf bind_return_pmf' bind_assoc_pmf cong:bind_pmf_cong)

abbreviation foldM_spmf
  :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'b spmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b spmf\<close> where
  \<open>foldM_spmf \<equiv> foldM bind_spmf return_spmf\<close>

lemma foldM_spmf_snoc: \<open>foldM_spmf f (xs@[y]) val = bind_spmf (foldM_spmf f xs val) (f y)\<close>
  by (induction xs arbitrary:val) (simp_all cong:bind_spmf_cong)

abbreviation \<open>prob_fail \<equiv> (\<lambda>x. pmf x None)\<close>

abbreviation \<open>fail_spmf \<equiv> return_pmf None\<close>

abbreviation fails_or_satisfies :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool\<close> where
  \<open>fails_or_satisfies \<equiv> case_option True\<close>

lemma prob_fail_foldM_spmf_le :
  fixes
    p :: real and
    P :: \<open>'b \<Rightarrow> bool\<close> and
    f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'b spmf\<close>
  assumes
    \<open>\<And> x y z. P y \<Longrightarrow> z \<in> set_spmf (f x y) \<Longrightarrow> P z\<close>
    \<open>\<And> x val. P val \<Longrightarrow> prob_fail (f x val) \<le> p\<close>
    \<open>P val\<close>
  shows \<open>prob_fail (foldM_spmf f xs val) \<le> real (length xs) * p\<close>
using assms(3) proof (induction xs arbitrary: val)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)

  have p_ge_0: \<open>p \<ge> 0\<close> using Cons(2) assms(2) order_trans[OF pmf_nonneg] by metis

  let ?val' = \<open>f x val\<close>
  let ?\<mu>' = \<open>measure_spmf ?val'\<close>

  have
    \<open>prob_fail (foldM_spmf f (x # xs) val) =
      prob_fail ?val' + \<integral> val'. prob_fail (foldM_spmf f xs val') \<partial> ?\<mu>'\<close>
    by (simp add: pmf_bind_spmf_None)
  also have \<open>\<dots> \<le> p + \<integral> _. length xs * p \<partial> ?\<mu>'\<close>
    using assms(1)[OF Cons(2)]
    by (intro add_mono integral_mono_AE iffD2[OF AE_measure_spmf_iff] ballI assms(2) Cons
         measure_spmf.integrable_const measure_spmf.integrable_const_bound[where B=\<open>1\<close>])
     (simp_all add:pmf_le_1)
  also have \<open>\<dots> \<le> p + weight_spmf (f x val)* length xs * p\<close>
    by simp
  also have \<open>\<dots> \<le> p + 1 * real (length xs) * p\<close>
    by (intro add_mono mult_right_mono p_ge_0 weight_spmf_le_1) simp_all
  finally show ?case by (simp add: algebra_simps)
qed

lemma foldM_spmf_of_pmf_eq :
  shows \<open>foldM_spmf (\<lambda>x y. spmf_of_pmf (f x y)) xs = spmf_of_pmf \<circ> foldM_pmf f xs\<close>
  (is ?thesis_0)
    and \<open>foldM_spmf (\<lambda>x y. spmf_of_pmf (f x y)) xs val = spmf_of_pmf (foldM_pmf f xs val)\<close>
  (is ?thesis_1)
proof -
  show ?thesis_0
    by (induction xs) (simp_all add: spmf_of_pmf_bind)

  then show ?thesis_1 by simp
qed

end