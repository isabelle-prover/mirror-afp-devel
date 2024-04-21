section \<open>Additional results about PMFs\<close>

theory Finite_Fields_More_PMF
  imports "HOL-Probability.Probability_Mass_Function"
begin

lemma powr_mono_rev:
  fixes x :: real
  assumes "a \<le> b" and  "x > 0" "x \<le> 1"
  shows "x powr b \<le> x powr a"
proof -
  have "x powr b = (1/x) powr (-b)" using assms by (simp add: powr_divide powr_minus_divide)
  also have "... \<le> (1/x) powr (-a)" using assms by (intro powr_mono) auto
  also have "... = x powr a" using assms by (simp add: powr_divide powr_minus_divide)
  finally show ?thesis by simp
qed

lemma integral_bind_pmf:
  fixes f :: "_ \<Rightarrow> real"
  assumes "bounded (f ` set_pmf (bind_pmf p q))"
  shows "(\<integral>x. f x \<partial>bind_pmf p q) = (\<integral>x. \<integral>y. f y \<partial>q x \<partial>p)" (is "?L = ?R")
proof -
  obtain M where a:"\<bar>f x\<bar> \<le> M" if "x \<in> set_pmf (bind_pmf p q)" for x
    using assms(1) unfolding bounded_iff by auto
  define clamp where "clamp x = (if \<bar>x\<bar> > M then 0 else x) " for x

  obtain x where "x \<in> set_pmf (bind_pmf p q)" using set_pmf_not_empty by fast
  hence M_ge_0: "M \<ge> 0" using a by fastforce

  have a:"\<And>x y. x \<in> set_pmf p \<Longrightarrow> y \<in> set_pmf (q x) \<Longrightarrow> \<not>\<bar>f y\<bar> > M"
    using a by fastforce
  hence "(\<integral>x. f x \<partial>bind_pmf p q) = (\<integral>x. clamp (f x) \<partial>bind_pmf p q)"
    unfolding clamp_def by (intro integral_cong_AE AE_pmfI) auto
  also have "... =  (\<integral>x. \<integral>y. clamp (f y) \<partial>q x \<partial>p)" unfolding measure_pmf_bind 
    by (subst integral_bind[where K="count_space UNIV" and B'="1" and B="M"])
      (simp_all add:measure_subprob clamp_def M_ge_0)
  also have "... = ?R" unfolding clamp_def using a by (intro integral_cong_AE AE_pmfI) simp_all
  finally show ?thesis by simp
qed

lemma measure_bind_pmf:
  "measure (bind_pmf m f) s = (\<integral>x. measure (f x) s \<partial>m)" (is "?L = ?R")
proof -
  have "?L = (\<integral>x. indicator s x \<partial>bind_pmf m f)" by simp
  also have "... = (\<integral>x. (\<integral>y. indicator s y \<partial>f x) \<partial>m)"
    by (intro integral_bind_pmf) (auto intro!:boundedI)
  also have "... = ?R" by simp
  finally show ?thesis by simp
qed

end