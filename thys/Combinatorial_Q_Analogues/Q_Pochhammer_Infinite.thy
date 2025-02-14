section \<open>The infinite $q$-Pochhammer symbol $(a; q)_\infty$\<close>
theory Q_Pochhammer_Infinite
imports
  More_Infinite_Products
  Q_Analogues
begin

subsection \<open>Definition and basic properties\<close>

definition qpochhammer_inf :: "'a :: {real_normed_field, banach, heine_borel} \<Rightarrow> 'a \<Rightarrow> 'a" where
  "qpochhammer_inf a q = prodinf (\<lambda>k. 1 - a * q ^ k)"

bundle qpochhammer_inf_notation
begin
notation qpochhammer_inf ("'(_ ; _')\<^sub>\<infinity>")
end

bundle no_qpochhammer_inf_notation
begin
no_notation qpochhammer_inf ("'(_ ; _')\<^sub>\<infinity>")
end


lemma qpochhammer_inf_0_left [simp]: "qpochhammer_inf 0 q = 1"
  by (simp add: qpochhammer_inf_def)

lemma qpochhammer_inf_0_right [simp]: "qpochhammer_inf a 0 = 1 - a"
proof -
  have "qpochhammer_inf a 0 = (\<Prod>k\<le>0. 1 - a * 0 ^ k)"
    unfolding qpochhammer_inf_def by (rule prodinf_finite) auto
  also have "\<dots> = 1 - a"
    by simp
  finally show ?thesis .
qed

lemma abs_convergent_qpochhammer_inf:
  fixes a q :: "'a :: {real_normed_div_algebra, banach}"
  assumes "norm q < 1"
  shows   "abs_convergent_prod (\<lambda>n. 1 - a * q ^ n)"
proof (rule summable_imp_abs_convergent_prod)
  show "summable (\<lambda>n. norm (1 - a * q ^ n - 1))"
    using assms by (auto simp: norm_power norm_mult)
qed

lemma convergent_qpochhammer_inf:
  fixes a q :: "'a :: {real_normed_field, banach}"
  assumes "norm q < 1"
  shows   "convergent_prod (\<lambda>n. 1 - a * q ^ n)"
  using abs_convergent_qpochhammer_inf[OF assms] abs_convergent_prod_imp_convergent_prod by blast

lemma has_prod_qpochhammer_inf:
  "norm q < 1 \<Longrightarrow> (\<lambda>n. 1 - a * q ^ n) has_prod qpochhammer_inf a q"
  using convergent_qpochhammer_inf unfolding qpochhammer_inf_def
  by (intro convergent_prod_has_prod)

text \<open>
  We now also see that the infinite $q$-Pochhammer symbol $(a; q)_\infty$ really is
  the limit of $(a; q)_n$ for $n\to\infty$:
\<close>
lemma qpochhammer_tendsto_qpochhammer_inf:
  assumes q: "norm q < 1"
  shows   "(\<lambda>n. qpochhammer (int n) t q) \<longlonglongrightarrow> qpochhammer_inf t q"
  using has_prod_imp_tendsto'[OF has_prod_qpochhammer_inf[OF q, of t]]
  by (simp add: qpochhammer_def)

lemma qpochhammer_inf_of_real:
  assumes "\<bar>q\<bar> < 1"
  shows   "qpochhammer_inf (of_real a) (of_real q) = of_real (qpochhammer_inf a q)"
proof -
  have "(\<lambda>n. of_real (1 - a * q ^ n) :: 'a) has_prod of_real (qpochhammer_inf a q)"
    unfolding has_prod_of_real_iff by (rule has_prod_qpochhammer_inf) (use assms in auto)
  also have "(\<lambda>n. of_real (1 - a * q ^ n) :: 'a) = (\<lambda>n. 1 - of_real a * of_real q ^ n)"
    by simp
  finally have "\<dots> has_prod of_real (qpochhammer_inf a q)" .
  moreover have "(\<lambda>n. 1 - of_real a * of_real q ^ n :: 'a) has_prod 
                   qpochhammer_inf (of_real a) (of_real q)"
    by (rule has_prod_qpochhammer_inf) (use assms in auto)
  ultimately show ?thesis
    using has_prod_unique2 by blast
qed

lemma qpochhammer_inf_zero_iff:
  assumes q: "norm q < 1"
  shows   "qpochhammer_inf a q = 0 \<longleftrightarrow> (\<exists>n. a * q ^ n = 1)"
proof -
  have "(\<lambda>n. 1 - a * q ^ n) has_prod qpochhammer_inf a q"
    using has_prod_qpochhammer_inf[OF q] by simp
  hence "qpochhammer_inf a q = 0 \<longleftrightarrow> (\<exists>n. a * q ^ n = 1)"
    by (subst has_prod_eq_0_iff) auto
  thus ?thesis .
qed

lemma qpochhammer_inf_nonzero:
  assumes "norm q < 1" "norm a < 1"
  shows   "qpochhammer_inf a q \<noteq> 0"
proof
  assume "qpochhammer_inf a q = 0"
  then obtain n where n: "a * q ^ n = 1"
    using assms by (subst (asm) qpochhammer_inf_zero_iff) auto
  have "norm (q ^ n) * norm a \<le> 1 * norm a"
    unfolding norm_power using assms by (intro mult_right_mono power_le_one) auto
  also have "\<dots>  < 1"
    using assms by simp
  finally have "norm (a * q ^ n) < 1"
    by (simp add: norm_mult mult.commute)
  with n show False
    by auto
qed


lemma qpochhammer_inf_pos:
  assumes "\<bar>q\<bar> < 1" "\<bar>a\<bar> < (1::real)"
  shows   "qpochhammer_inf a q > 0"
  using has_prod_qpochhammer_inf
proof (rule has_prod_pos)
  fix n :: nat
  have "\<bar>a * q ^ n\<bar> = \<bar>a\<bar> * \<bar>q\<bar> ^ n"
    by (simp add: abs_mult power_abs)
  also have "\<bar>a\<bar> * \<bar>q\<bar> ^ n \<le> \<bar>a\<bar> * 1 ^ n"
    by (intro mult_left_mono power_mono) (use assms in auto)
  also have "\<dots> < 1"
    using assms by simp
  finally show "0 < 1 - a * q ^ n"
    by simp
qed (use assms in auto)

lemma qpochhammer_inf_nonneg:
  assumes "\<bar>q\<bar> < 1" "\<bar>a\<bar> \<le> (1::real)"
  shows   "qpochhammer_inf a q \<ge> 0"
  using has_prod_qpochhammer_inf
proof (rule has_prod_nonneg)
  fix n :: nat
  have "\<bar>a * q ^ n\<bar> = \<bar>a\<bar> * \<bar>q\<bar> ^ n"
    by (simp add: abs_mult power_abs)
  also have "\<bar>a\<bar> * \<bar>q\<bar> ^ n \<le> \<bar>a\<bar> * 1 ^ n"
    by (intro mult_left_mono power_mono) (use assms in auto)
  also have "\<dots> \<le>1"
    using assms by simp
  finally show "0 \<le> 1 - a * q ^ n"
    by simp
qed (use assms in auto)


subsection \<open>Uniform convergence and its consequences\<close>

context
  fixes P :: "nat \<Rightarrow> 'a :: {real_normed_field, banach, heine_borel} \<Rightarrow> 'a \<Rightarrow> 'a"
  defines "P \<equiv> (\<lambda>N a q. \<Prod>n<N. 1 - a * q ^ n)"
begin 

lemma uniformly_convergent_qpochhammer_inf_aux:
  assumes r: "0 \<le> ra" "0 \<le> rq" "rq < 1"
  shows   "uniformly_convergent_on (cball 0 ra \<times> cball 0 rq) (\<lambda>n (a,q). P n a q)"
  unfolding P_def case_prod_unfold
proof (rule uniformly_convergent_on_prod')
  show "uniformly_convergent_on (cball 0 ra \<times> cball 0 rq)
          (\<lambda>N aq. \<Sum>n<N. norm (1 - fst aq * snd aq ^ n - 1 :: 'a))"
  proof (intro Weierstrass_m_test'_ev always_eventually allI ballI)
    show "summable (\<lambda>n. ra * rq ^ n)" using r
      by (intro summable_mult summable_geometric) auto
  next
    fix n :: nat and aq :: "'a \<times> 'a"
    assume "aq \<in> cball 0 ra \<times> cball 0 rq"
    then obtain a q where [simp]: "aq = (a, q)" and aq: "norm a \<le> ra" "norm q \<le> rq"
      by (cases aq) auto
    have "norm (norm (1 - a * q ^ n - 1)) = norm a * norm q ^ n"
      by (simp add: norm_mult norm_power)
    also have "\<dots> \<le> ra * rq ^ n"
      using aq r by (intro mult_mono power_mono) auto
    finally show "norm (norm (1 - fst aq * snd aq ^ n - 1)) \<le> ra * rq ^ n"
      by simp
  qed
qed (auto intro!: continuous_intros compact_Times) 

lemma uniformly_convergent_qpochhammer_inf:
  assumes "compact A" "A \<subseteq> UNIV \<times> ball 0 1"
  shows   "uniformly_convergent_on A (\<lambda>n (a,q). P n a q)"
proof (cases "A = {}")
  case False
  obtain rq where rq: "rq \<ge> 0" "rq < 1" "\<And>a q. (a, q) \<in> A \<Longrightarrow> norm q \<le> rq"
  proof -
    from \<open>compact A\<close> have "compact (norm ` snd ` A)"
      by (intro compact_continuous_image continuous_intros)
    hence "Sup (norm ` snd ` A) \<in> norm ` snd ` A"
      by (intro closed_contains_Sup bounded_imp_bdd_above compact_imp_bounded compact_imp_closed)
         (use \<open>A \<noteq> {}\<close> in auto)
    then obtain aq0 where aq0: "aq0 \<in> A" "norm (snd aq0) = Sup (norm ` snd ` A)"
      by auto
    show ?thesis
    proof (rule that[of "norm (snd aq0)"])
      show "norm (snd aq0) \<ge> 0" and "norm (snd aq0) < 1"
        using assms(2) aq0(1) by auto
    next
      fix a q assume "(a, q) \<in> A"
      hence "norm q \<le> Sup (norm ` snd ` A)"
        by (intro cSup_upper bounded_imp_bdd_above compact_imp_bounded assms
              compact_continuous_image continuous_intros) force
      with aq0 show "norm q \<le> norm (snd aq0)"
        by simp
    qed
  qed

  obtain ra where ra: "ra \<ge> 0" "\<And>a q. (a, q) \<in> A \<Longrightarrow> norm a \<le> ra"
  proof -
    have "bounded (fst ` A)"
      by (intro compact_imp_bounded compact_continuous_image continuous_intros assms)
    then obtain ra where ra: "norm a \<le> ra" if "a \<in> fst ` A" for a
      unfolding bounded_iff by blast
    from \<open>A \<noteq> {}\<close> obtain aq0 where "aq0 \<in> A"
      by blast
    have "0 \<le> norm (fst aq0)"
      by simp
    also have "fst aq0 \<in> fst ` A"
      using \<open>aq0 \<in> A\<close> by blast
    with ra[of "fst aq0"] and \<open>A \<noteq> {}\<close> have "norm (fst aq0) \<le> ra"
      by simp
    finally show ?thesis
      using that[of ra] ra by fastforce
  qed

  have "uniformly_convergent_on (cball 0 ra \<times> cball 0 rq) (\<lambda>n (a,q). P n a q)"
    by (intro uniformly_convergent_qpochhammer_inf_aux) (use ra rq in auto)
  thus ?thesis
    by (rule uniformly_convergent_on_subset) (use ra rq in auto)
qed auto

lemma uniform_limit_qpochhammer_inf:
  assumes "compact A" "A \<subseteq> UNIV \<times> ball 0 1"
  shows   "uniform_limit A (\<lambda>n (a,q). P n a q) (\<lambda>(a,q). qpochhammer_inf a q) at_top"
proof -
  obtain g where g: "uniform_limit A (\<lambda>n (a,q). P n a q) g at_top"
    using uniformly_convergent_qpochhammer_inf[OF assms(1,2)]
    by (auto simp: uniformly_convergent_on_def)
  also have "?this \<longleftrightarrow> uniform_limit A (\<lambda>n (a,q). P n a q) (\<lambda>(a,q). qpochhammer_inf a q) at_top"
  proof (intro uniform_limit_cong)
    fix aq :: "'a \<times> 'a"
    assume "aq \<in> A"
    then obtain a q where [simp]: "aq = (a, q)" and aq: "(a, q) \<in> A"
      by (cases aq) auto
    from aq and assms have q: "norm q < 1"
      by auto
    have "(\<lambda>n. case aq of (a, q) \<Rightarrow> P n a q) \<longlonglongrightarrow> g aq"
      by (rule tendsto_uniform_limitI[OF g]) fact
    hence "(\<lambda>n. case aq of (a, q) \<Rightarrow> P (Suc n) a q) \<longlonglongrightarrow> g aq"
      by (rule filterlim_compose) (rule filterlim_Suc)
    moreover have "(\<lambda>n. case aq of (a, q) \<Rightarrow> P (Suc n) a q) \<longlonglongrightarrow> qpochhammer_inf a q"
      using convergent_prod_LIMSEQ[OF convergent_qpochhammer_inf[of q a]] aq q
      unfolding P_def lessThan_Suc_atMost
      by (simp add: qpochhammer_inf_def)
    ultimately show "g aq = (case aq of (a, q) \<Rightarrow> qpochhammer_inf a q)"
      using tendsto_unique by force
  qed auto
  finally show ?thesis .
qed

lemma continuous_on_qpochhammer_inf [continuous_intros]:
  fixes a q :: "'b :: topological_space \<Rightarrow> 'a"
  assumes [continuous_intros]: "continuous_on A a" "continuous_on A q"
  assumes "\<And>x. x \<in> A \<Longrightarrow> norm (q x) < 1"
  shows   "continuous_on A (\<lambda>x. qpochhammer_inf (a x) (q x))"
proof -
  have *: "continuous_on (cball 0 ra \<times> cball 0 rq) (\<lambda>(a,q). qpochhammer_inf a q :: 'a)"
    if r: "0 \<le> ra" "0 \<le> rq" "rq < 1" for ra rq :: real
  proof (rule uniform_limit_theorem)
    show "uniform_limit (cball 0 ra \<times> cball 0 rq) (\<lambda>n (a,q). P n a q)
            (\<lambda>(a,q). qpochhammer_inf a q) at_top"
      by (rule uniform_limit_qpochhammer_inf) (use r in \<open>auto simp: compact_Times\<close>)
  qed (auto intro!: always_eventually intro!: continuous_intros simp: P_def case_prod_unfold)

  have **: "isCont (\<lambda>(a,q). qpochhammer_inf a q) (a, q)" if q: "norm q < 1" for a q :: 'a
  proof -
    obtain R where R: "norm q < R" "R < 1"
      using dense q by blast
    with norm_ge_zero[of q] have "R \<ge> 0"
      by linarith
    have "continuous_on (cball 0 (norm a + 1) \<times> cball 0 R) (\<lambda>(a,q). qpochhammer_inf a q :: 'a)"
      by (rule *) (use R \<open>R \<ge> 0\<close> in auto)
    hence "continuous_on (ball 0 (norm a + 1) \<times> ball 0 R) (\<lambda>(a,q). qpochhammer_inf a q :: 'a)"
      by (rule continuous_on_subset) auto
    moreover have "(a, q) \<in> ball 0 (norm a + 1) \<times> ball 0 R"
      using q R by auto
    ultimately show ?thesis
      by (subst (asm) continuous_on_eq_continuous_at) (auto simp: open_Times)
  qed
  hence ***: "continuous_on ((\<lambda>x. (a x, q x)) ` A) (\<lambda>(a,q). qpochhammer_inf a q)"
    using assms(3) by (intro continuous_at_imp_continuous_on) auto
  have "continuous_on A ((\<lambda>(a,q). qpochhammer_inf a q) \<circ> (\<lambda>x. (a x, q x)))"
    by (rule continuous_on_compose[OF _ ***]) (intro continuous_intros)
  thus ?thesis
    by (simp add: o_def)
qed

lemma continuous_qpochhammer_inf [continuous_intros]:
  fixes a q :: "'b :: t2_space \<Rightarrow> 'a"
  assumes "continuous (at x within A) a" "continuous (at x within A) q" "norm (q x) < 1"
  shows   "continuous (at x within A) (\<lambda>x. qpochhammer_inf (a x) (q x))"
proof -
  have "continuous_on (UNIV \<times> ball 0 1) (\<lambda>x. qpochhammer_inf (fst x) (snd x) :: 'a)"
    by (intro continuous_intros) auto
  moreover have "(a x, q x) \<in> UNIV \<times> ball 0 1"
    using assms(3) by auto
  ultimately have "isCont (\<lambda>x. qpochhammer_inf (fst x) (snd x)) (a x, q x)"
    by (simp add: continuous_on_eq_continuous_at open_Times)
  hence "continuous (at (a x, q x) within (\<lambda>x. (a x, q x)) ` A) 
           (\<lambda>x. qpochhammer_inf (fst x) (snd x))"
    using continuous_at_imp_continuous_at_within by blast
  hence "continuous (at x within A) ((\<lambda>x. qpochhammer_inf (fst x) (snd x)) \<circ> (\<lambda>x. (a x, q x)))"
    by (intro continuous_intros assms)
  thus ?thesis
    by (simp add: o_def)
qed

lemma tendsto_qpochhammer_inf [tendsto_intros]:
  fixes a q :: "'b \<Rightarrow> 'a"
  assumes "(a \<longlongrightarrow> a0) F" "(q \<longlongrightarrow> q0) F" "norm q0 < 1"
  shows   "((\<lambda>x. qpochhammer_inf (a x) (q x)) \<longlongrightarrow> qpochhammer_inf a0 q0) F"
proof -
  define f where "f = (\<lambda>x. qpochhammer_inf (fst x) (snd x) :: 'a)"
  have "((\<lambda>x. f (a x, q x)) \<longlongrightarrow> f (a0, q0)) F"
  proof (rule isCont_tendsto_compose[of _ f])
    show "isCont f (a0, q0)"
      using assms(3) by (auto simp: f_def intro!: continuous_intros)
    show "((\<lambda>x. (a x, q x)) \<longlongrightarrow> (a0, q0)) F "
      by (intro tendsto_intros assms)
  qed
  thus ?thesis
    by (simp add: f_def)
qed

end

context
  fixes P :: "nat \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex"
  defines "P \<equiv> (\<lambda>N a q. \<Prod>n<N. 1 - a * q ^ n)"
begin

lemma holomorphic_qpochhammer_inf [holomorphic_intros]:
  assumes [holomorphic_intros]: "a holomorphic_on A" "q holomorphic_on A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> norm (q x) < 1" "open A"
  shows   "(\<lambda>x. qpochhammer_inf (a x) (q x)) holomorphic_on A"
proof (rule holomorphic_uniform_sequence)
  fix x assume x: "x \<in> A"
  then obtain r where r: "r > 0" "cball x r \<subseteq> A"
    using \<open>open A\<close> unfolding open_contains_cball by blast
  have *: "compact ((\<lambda>x. (a x, q x)) ` cball x r)" using r
    by (intro compact_continuous_image continuous_intros)
       (auto intro!: holomorphic_on_imp_continuous_on[OF holomorphic_on_subset] holomorphic_intros)
  have "uniform_limit ((\<lambda>x. (a x, q x)) ` cball x r) (\<lambda>n (a,q). P n a q) (\<lambda>(a,q). qpochhammer_inf a q) at_top"
    unfolding P_def
    by (rule uniform_limit_qpochhammer_inf[OF *]) (use r assms(3) in \<open>auto simp: compact_Times\<close>)
  hence "uniform_limit (cball x r) (\<lambda>n x. case (a x, q x) of (a, q) \<Rightarrow> P n a q)
           (\<lambda>x. case (a x, q x) of (a, q) \<Rightarrow> qpochhammer_inf a q) at_top"
    by (rule uniform_limit_compose') auto
  thus "\<exists>d>0. cball x d \<subseteq> A \<and> uniform_limit (cball x d)
            (\<lambda>n x. case (a x, q x) of (a, q) \<Rightarrow> P n a q)
            (\<lambda>x. qpochhammer_inf (a x) (q x)) sequentially"
    using r by fast
qed (use \<open>open A\<close> in \<open>auto intro!: holomorphic_intros simp: P_def\<close>)

lemma analytic_qpochhammer_inf [analytic_intros]:
  assumes [analytic_intros]: "a analytic_on A" "q analytic_on A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> norm (q x) < 1"
  shows   "(\<lambda>x. qpochhammer_inf (a x) (q x)) analytic_on A"
proof -
  from assms(1) obtain A1 where A1: "open A1" "A \<subseteq> A1" "a holomorphic_on A1"
    by (auto simp: analytic_on_holomorphic)
  from assms(2) obtain A2 where A2: "open A2" "A \<subseteq> A2" "q holomorphic_on A2"
    by (auto simp: analytic_on_holomorphic)
  have "continuous_on A2 q"
    by (rule holomorphic_on_imp_continuous_on) fact
  hence "open (q -` ball 0 1 \<inter> A2)"
    using A2 by (subst (asm) continuous_on_open_vimage) auto
  define A' where "A' = (q -` ball 0 1 \<inter> A2) \<inter> A1"
  have "open A'"
    unfolding A'_def by (rule open_Int) fact+

  note [holomorphic_intros] = holomorphic_on_subset[OF A1(3)] holomorphic_on_subset[OF A2(3)]
  have "(\<lambda>x. qpochhammer_inf (a x) (q x)) holomorphic_on A'"
    using \<open>open A'\<close> by (intro holomorphic_intros) (auto simp: A'_def)
  moreover have "A \<subseteq> A'"
    using A1(2) A2(2) assms(3) unfolding A'_def by auto
  ultimately show ?thesis
    using analytic_on_holomorphic \<open>open A'\<close> by blast
qed  

lemma meromorphic_qpochhammer_inf [meromorphic_intros]:
  assumes [analytic_intros]: "a analytic_on A" "q analytic_on A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> norm (q x) < 1"
  shows   "(\<lambda>x. qpochhammer_inf (a x) (q x)) meromorphic_on A"
  by (rule analytic_on_imp_meromorphic_on) (use assms(3) in \<open>auto intro!: analytic_intros\<close>)

end


subsection \<open>Bounds for $(a; q)_n$ and $\binom{n}{k}_q$ in terms of $(a; q)_\infty$\<close>

lemma qpochhammer_le_qpochhammer_inf:
  assumes "q \<ge> 0" "q < 1" "a \<le> 0"
  shows   "qpochhammer (int k) a q \<le> qpochhammer_inf a (q::real)"
  unfolding qpochhammer_nonneg_def qpochhammer_inf_def
proof (rule prod_le_prodinf)
  show "(\<lambda>k. 1 - a * q ^ k) has_prod qpochhammer_inf a q"
    by (rule has_prod_qpochhammer_inf) (use assms in auto)
next
  fix i :: nat
  have *: "a * q ^ i \<le> 0"
    by (rule mult_nonpos_nonneg) (use assms in auto)
  show "1 - a * q ^ i \<ge> 0"  "1 \<le> 1 - a * q ^ i"
    using * by simp_all
qed

lemma qpochhammer_ge_qpochhammer_inf:
  assumes "q \<ge> 0" "q < 1" "a \<ge> 0" "a \<le> 1"
  shows   "qpochhammer (int k) a q \<ge> qpochhammer_inf a (q::real)"
  unfolding qpochhammer_nonneg_def qpochhammer_inf_def
proof (rule prod_ge_prodinf)
  show "(\<lambda>k. 1 - a * q ^ k) has_prod qpochhammer_inf a q"
    by (rule has_prod_qpochhammer_inf) (use assms in auto)
next
  fix i :: nat
  have "a * q ^ i \<le> 1 * 1 ^ i"
    using assms by (intro mult_mono power_mono) auto
  thus "1 - a * q ^ i \<ge> 0"
    by auto
  show "1 - a * q ^ i \<le> 1"
    using assms by auto
qed  

lemma norm_qbinomial_le_qpochhammer_inf_strong:
  fixes q :: "'a :: {real_normed_field}"
  assumes q: "norm q < 1"
  shows   "norm (qbinomial q n k) \<le>
             qpochhammer_inf (-(norm q ^ (n + 1 - k))) (norm q) /
             qpochhammer_inf (norm q) (norm q)"
proof (cases "k \<le> n")
  case k: True
  have "norm (qbinomial q n k ) =
          norm (qpochhammer (int k) (q ^ (n + 1 - k)) q) /
          norm (qpochhammer (int k) q q)"
    using q k by (subst qbinomial_conv_qpochhammer') (simp_all add: norm_divide)
  also have "\<dots> \<le> qpochhammer (int k) (-norm (q ^ (n + 1 - k))) (norm q) /
                  qpochhammer (int k) (norm q) (norm q)"
    by (intro frac_le norm_qpochhammer_nonneg_le_qpochhammer norm_qpochhammer_nonneg_ge_qpochhammer
                 qpochhammer_nonneg qpochhammer_pos)
       (use assms in \<open>auto intro: order.trans[OF _ norm_ge_zero]\<close>)
  also have "\<dots> \<le> qpochhammer_inf (-(norm (q ^ (n+1-k)))) (norm q) / qpochhammer_inf (norm q) (norm q)"
    by (intro frac_le qpochhammer_le_qpochhammer_inf qpochhammer_ge_qpochhammer_inf
              qpochhammer_inf_pos qpochhammer_inf_nonneg)
       (use assms in \<open>auto simp: norm_power power_le_one_iff simp del: power_Suc\<close>)
  finally show ?thesis
    by (simp_all add: norm_power)
qed (use q in \<open>auto intro!: divide_nonneg_nonneg qpochhammer_inf_nonneg\<close>)

lemma norm_qbinomial_le_qpochhammer_inf:
  fixes q :: "'a :: {real_normed_field}"
  assumes q: "norm q < 1"
  shows   "norm (qbinomial q n k) \<le>
             qpochhammer_inf (-norm q) (norm q) / qpochhammer_inf (norm q) (norm q)"
proof (cases "k \<le> n")
  case True
  have "norm (qbinomial q n k) \<le>
          qpochhammer_inf (-(norm q ^ (n + 1 - k))) (norm q) /
          qpochhammer_inf (norm q) (norm q)"
    by (rule norm_qbinomial_le_qpochhammer_inf_strong) (use q in auto)
  also have "\<dots> \<le> qpochhammer_inf (-norm q) (norm q) / qpochhammer_inf (norm q) (norm q)"
  proof (rule divide_right_mono)
    show "qpochhammer_inf (- (norm q ^ (n + 1 - k))) (norm q) \<le> qpochhammer_inf (- norm q) (norm q)"
    proof (intro has_prod_le[OF has_prod_qpochhammer_inf has_prod_qpochhammer_inf] conjI)
      fix i :: nat
      have "norm q ^ (n + 1 - k + i) \<le> norm q ^ (Suc i)"
        by (intro power_decreasing) (use assms True in simp_all)
      thus "1 - - (norm q ^ (n + 1 - k)) * norm q ^ i \<le> 1 - - norm q * norm q ^ i"
        by (simp_all add: power_add)
    qed (use assms in auto)
  qed (use assms in \<open>auto intro!: qpochhammer_inf_nonneg\<close>)
  finally show ?thesis .
qed (use q in \<open>auto intro!: divide_nonneg_nonneg qpochhammer_inf_nonneg\<close>)



subsection \<open>Limits of the $q$-binomial coefficients\<close>

text \<open>
  The following limit is Fact~7.7 in Andrews \& Eriksson~\<^cite>\<open>andrews2004\<close>.
\<close>
lemma tendsto_qbinomial1:
  fixes q :: "'a :: {real_normed_field, banach, heine_borel}"
  assumes q: "norm q < 1"
  shows   "(\<lambda>n. qbinomial q n m) \<longlonglongrightarrow> 1 / qpochhammer m q q"
proof -
  have not_one: "q ^ k \<noteq> 1" if "k > 0" for k :: nat
    using q_power_neq_1[of q k] that q by simp
  have [simp]: "q \<noteq> 1"
    using q by auto

  define P where "P = (\<lambda>n. qpochhammer (int n) q q)"
  have [simp]: "qpochhammer_inf q q \<noteq> 0"
    using q by (auto simp: qpochhammer_inf_zero_iff not_one simp flip: power_Suc)
  have [simp]: "P m \<noteq> 0"
  proof
    assume "P m = 0"
    then obtain k where k: "q * q powi k = 1" "k \<in> {0..<int m}"
      by (auto simp: P_def qpochhammer_eq_0_iff power_int_add)
    show False
      by (use k not_one[of "Suc (nat k)"] in \<open>auto simp: power_int_add power_int_def\<close>)
  qed

  have [tendsto_intros]: "(\<lambda>n. P (h n)) \<longlonglongrightarrow> qpochhammer_inf q q" 
    if h: "filterlim h at_top at_top" for h :: "nat \<Rightarrow> nat"
    unfolding P_def using filterlim_compose[OF qpochhammer_tendsto_qpochhammer_inf[OF q] h, of q] .
  have "(\<lambda>n. P n / (P m * P (n - m))) \<longlonglongrightarrow> 1 / P m"
    by (auto intro!: tendsto_eq_intros filterlim_ident filterlim_minus_const_nat_at_top)
  also have "(\<forall>\<^sub>F n in at_top. P n / (P m * P (n - m)) = qbinomial q n m)"
    using eventually_ge_at_top[of m]
    by eventually_elim (auto simp: qbinomial_conv_qpochhammer P_def not_one of_nat_diff)
  hence "(\<lambda>n. P n / (P m * P (n - m))) \<longlonglongrightarrow> 1 / P m \<longleftrightarrow>
         (\<lambda>n. qbinomial q n m) \<longlonglongrightarrow> 1 / P m" 
    by (intro filterlim_cong) auto
  finally show "(\<lambda>n. qbinomial q n m) \<longlonglongrightarrow> 1 / qpochhammer m q q"
    unfolding P_def .
qed
  
text \<open>
  The following limit is a slightly stronger version of Fact~7.8 in 
  Andrews \& Eriksson~\<^cite>\<open>andrews2004\<close>. Their version has $f(n) = rn + c_1$ and 
  $g(n) = sn + c_2$ with $r > s$.
\<close>
lemma tendsto_qbinomial2:
  fixes q :: "'a :: {real_normed_field, banach, heine_borel}"
  assumes q: "norm q < 1"
  assumes lim_fg: "filterlim (\<lambda>n. f n - g n) at_top F"
  assumes lim_g: "filterlim g at_top F"
  shows   "((\<lambda>n. qbinomial q (f n) (g n)) \<longlongrightarrow> 1 / qpochhammer_inf q q) F"
proof -
  have not_one: "q ^ k \<noteq> 1" if "k > 0" for k :: nat
    using q_power_neq_1[of q k] that q by simp
  have [simp]: "q \<noteq> 1"
    using q by auto

  define P where "P = (\<lambda>n. qpochhammer (int n) q q)"
  have [simp]: "qpochhammer_inf q q \<noteq> 0"
    using q by (auto simp: qpochhammer_inf_zero_iff not_one simp flip: power_Suc)
  have lim_f: "filterlim f at_top F"
    using lim_fg by (rule filterlim_at_top_mono) auto

  have fg: "eventually (\<lambda>n. f n \<ge> g n) F"
  proof -
    have "eventually (\<lambda>n. f n - g n > 0) F"
      using lim_fg by (metis eventually_gt_at_top filterlim_iff)
    thus ?thesis
      by eventually_elim auto
  qed
  from lim_g and fg have lim_f: "filterlim f at_top F"
    using filterlim_at_top_mono by blast

  have [tendsto_intros]: "((\<lambda>n. P (h n)) \<longlongrightarrow> qpochhammer_inf q q) F"
    if h: "filterlim h at_top F" for h
    unfolding P_def using filterlim_compose[OF qpochhammer_tendsto_qpochhammer_inf[OF q] h, of q] .
  have "((\<lambda>n. P (f n) / (P (g n) * P (f n - g n))) \<longlongrightarrow> 1 / qpochhammer_inf q q) F"
    by (auto intro!: tendsto_eq_intros lim_f lim_g lim_fg)
  also from fg have "(\<forall>\<^sub>F n in F. P (f n) / (P (g n) * P (f n - g n)) = qbinomial q (f n) (g n))"
    by eventually_elim
       (auto simp: qbinomial_qfact not_one of_nat_diff qfact_conv_qpochhammer
                   power_int_minus power_int_diff P_def field_simps)
  hence "((\<lambda>n. P (f n) / (P (g n) * P (f n - g n))) \<longlongrightarrow> 1 / qpochhammer_inf q q) F \<longleftrightarrow>
         ((\<lambda>n. qbinomial q (f n) (g n)) \<longlongrightarrow> 1 / qpochhammer_inf q q) F"
    by (intro filterlim_cong) auto
  finally show "((\<lambda>n. qbinomial q (f n) (g n)) \<longlongrightarrow> 1 / qpochhammer_inf q q) F" .
qed


subsection \<open>Useful identities\<close>

text \<open>
  The following lemmas give a recurrence for the infinite $q$-Pochhammer symbol similar to
  the one for the ``normal'' Pochhammer symbol.
\<close>
lemma qpochhammer_inf_mult_power_q:
  assumes "norm q < 1"
  shows   "qpochhammer_inf a q = qpochhammer (int n) a q * qpochhammer_inf (a * q ^ n) q"
proof -
  have "(\<lambda>n. 1 - a * q ^ n) has_prod qpochhammer_inf a q"
    by (rule has_prod_qpochhammer_inf) (use assms in auto)
  hence "convergent_prod (\<lambda>n. 1 - a * q ^ n)"
    by (simp add: has_prod_iff)
  hence "(\<lambda>n. 1 - a * q ^ n) has_prod
          ((\<Prod>k<n. 1 - a * q ^ k) * (\<Prod>k. 1 - a * q ^ (k + n)))"
    by (intro has_prod_ignore_initial_segment')
  also have "(\<Prod>k. 1 - a * q ^ (k + n)) = (\<Prod>k. 1 - (a * q ^ n) * q ^ k)"
    by (simp add: power_add mult_ac)
  also have "(\<lambda>k. 1 - (a * q ^ n) * q ^ k) has_prod qpochhammer_inf (a * q ^ n) q"
    by (rule has_prod_qpochhammer_inf) (use assms in auto)
  hence "(\<Prod>k. 1 - (a * q ^ n) * q ^ k) = qpochhammer_inf (a * q ^ n) q"
    by (simp add: qpochhammer_inf_def)
  finally show ?thesis
    by (simp add: qpochhammer_inf_def has_prod_iff qpochhammer_nonneg_def)
qed

text \<open>
  One can express the finite $q$-Pochhammer symbol in terms of the infinite one:
  \[(a; q)_n = \frac{(a; q)_\infty}{(a; q^n)_\infty}\]
\<close>
lemma qpochhammer_conv_qpochhammer_inf_nonneg:
  assumes "norm q < 1" "\<And>m. m \<ge> n \<Longrightarrow> a * q ^ m \<noteq> 1"
  shows   "qpochhammer (int n) a q = qpochhammer_inf a q / qpochhammer_inf (a * q ^ n) q"
proof (cases "qpochhammer_inf (a * q ^ n) q = 0")
  case False
  thus ?thesis
    by (subst qpochhammer_inf_mult_power_q[OF assms(1), of _ n]) 
      (auto simp: qpochhammer_inf_zero_iff)
next
  case True
  with assms obtain k where "a * q ^ (n + k) = 1"
    by (auto simp: qpochhammer_inf_zero_iff power_add mult_ac)
  moreover have "n + k \<ge> n"
    by auto
  ultimately have "\<exists>m\<ge>n+k. a * q ^ m = 1"
    by blast
  with assms have False
    by auto
  thus ?thesis ..
qed

lemma qpochhammer_conv_qpochhammer_inf:
  fixes q a :: "'a :: {real_normed_field, banach, heine_borel}"
  assumes q: "norm q < 1" "n < 0 \<longrightarrow> q \<noteq> 0"
  assumes not_one: "\<And>k. int k \<ge> n \<Longrightarrow> a * q ^ k \<noteq> 1"
  shows "qpochhammer n a q = qpochhammer_inf a q / qpochhammer_inf (a * q powi n) q"
proof (cases "n \<ge> 0")
  case n: True
  define m where "m = nat n"
  have n_eq: "n = int m"
    using n by (auto simp: m_def)
  show ?thesis unfolding n_eq
    by (subst qpochhammer_conv_qpochhammer_inf_nonneg) (use q not_one in \<open>auto simp: n_eq\<close>)
next
  case n: False
  define m where "m = nat (-n)"
  have n_eq: "n = -int m" and m: "m > 0"
    using n by (auto simp: m_def)
  have nz: "qpochhammer_inf a q \<noteq> 0"
    using q not_one n by (auto simp: qpochhammer_inf_zero_iff)
  have "qpochhammer n a q = 1 / qpochhammer (int m) (a / q ^ m) q"
    using \<open>m > 0\<close> by (simp add: n_eq qpochhammer_minus)
  also have "\<dots> = qpochhammer_inf a q / qpochhammer_inf (a / q ^ m) q"
    using qpochhammer_inf_mult_power_q[OF q(1), of "a / q ^ m" m] nz q n
    by (auto simp: divide_simps)
  also have "a / q ^ m = a * q powi n"
    by (simp add: n_eq power_int_minus field_simps)
  finally show "qpochhammer n a q = qpochhammer_inf a q / qpochhammer_inf (a * q powi n) q" .
qed

lemma qpochhammer_inf_divide_power_q:
  assumes "norm q < 1" and [simp]: "q \<noteq> 0"
  shows   "qpochhammer_inf (a / q ^ n) q = (\<Prod>k = 1..n. 1 - a / q ^ k) * qpochhammer_inf a q"
proof -
  have "qpochhammer_inf (a / q ^ n) q =
          qpochhammer (int n) (a / q ^ n) q * qpochhammer_inf (a / q^n * q^n) q"
    using assms(1) by (rule qpochhammer_inf_mult_power_q)
  also have "qpochhammer (int n) (a / q ^ n) q = (\<Prod>k<n. 1 - a / q ^ (n - k))"
    unfolding qpochhammer_nonneg_def by (intro prod.cong) (auto simp: power_diff)
  also have "\<dots> = (\<Prod>k=1..n. 1 - a / q ^ k)"
    by (intro prod.reindex_bij_witness[of _ "\<lambda>k. n - k" "\<lambda>k. n - k"]) auto
  finally show ?thesis
    by simp
qed

lemma qpochhammer_inf_mult_q:
  assumes "norm q < 1"
  shows   "qpochhammer_inf a q = (1 - a) * qpochhammer_inf (a * q) q"
  using qpochhammer_inf_mult_power_q[OF assms, of a 1] by simp

lemma qpochhammer_inf_divide_q:
  assumes "norm q < 1" "q \<noteq> 0"
  shows   "qpochhammer_inf (a / q) q = (1 - a / q) *  qpochhammer_inf a q"
  using qpochhammer_inf_divide_power_q[of q a 1] assms by simp


text \<open>
  The following lemma allows combining a product of several $q$-Pochhammer symbols into one
  by grouping factors:
  \[(a; q^m)_\infty\, (aq; q^m)_\infty\, \cdots\, (aq^{m-1}; q^m)_\infty = (a; q)_\infty\]
\<close>
lemma prod_qpochhammer_group:
  assumes "norm q < 1" and "m > 0"
  shows   "(\<Prod>i<m. qpochhammer_inf (a * q^i) (q^m)) = qpochhammer_inf a q"
proof (rule has_prod_unique2)
  show "(\<lambda>n. (\<Prod>i<m. 1 - a * q^i * (q^m) ^ n)) has_prod (\<Prod>i<m. qpochhammer_inf (a * q^i) (q^m))"
    by (intro has_prod_prod has_prod_qpochhammer_inf)
       (use assms in \<open>auto simp: norm_power power_less_one_iff\<close>)
next
  have "(\<lambda>n. 1 - a * q ^ n) has_prod qpochhammer_inf a q"
    by (rule has_prod_qpochhammer_inf) (use assms in auto)
  hence "(\<lambda>n. \<Prod>i=n*m..<n*m+m. 1 - a * q^i) has_prod qpochhammer_inf a q"
    by (rule has_prod_group) (use assms in auto)
  also have "(\<lambda>n. \<Prod>i=n*m..<n*m+m. 1 - a * q^i) = (\<lambda>n. \<Prod>i<m. 1 - a * q ^ i * (q ^ m) ^ n)"
  proof
    fix n :: nat
    have "(\<Prod>i=n*m..<n*m+m. 1 - a * q^i) = (\<Prod>i<m. 1 - a * q^(n*m + i))"
      by (intro prod.reindex_bij_witness[of _ "\<lambda>i. i + n * m" "\<lambda>i. i - n * m"]) auto
    thus "(\<Prod>i=n*m..<n*m+m. 1 - a * q^i) = (\<Prod>i<m. 1 - a * q ^ i * (q ^ m) ^ n)"
      by (simp add: power_add mult_ac flip: power_mult)
  qed
  finally show "(\<lambda>n. (\<Prod>i<m. 1 - a * q^i * (q^m) ^ n)) has_prod qpochhammer_inf a q" .
qed

text \<open>
  A product of two $q$-Pochhammer symbols $(\pm a; q)_\infty$ can be combined into
  a single $q$-Pochhammer symbol:
\<close>
lemma qpochhammer_inf_square:
  assumes q: "norm q < 1"
  shows   "qpochhammer_inf a q * qpochhammer_inf (-a) q = qpochhammer_inf (a^2) (q^2)"
          (is "?lhs = ?rhs")
proof -
  have "(\<lambda>n. (1 - a * q ^ n) * (1 - (-a) * q ^ n)) has_prod
          (qpochhammer_inf a q * qpochhammer_inf (-a) q)"
    by (intro has_prod_qpochhammer_inf has_prod_mult) (use q in auto)
  also have "(\<lambda>n. (1 - a * q ^ n) * (1 - (-a) * q ^ n)) = (\<lambda>n. (1 - a ^ 2 * (q ^ 2) ^ n))"
    by (auto simp: fun_eq_iff algebra_simps power2_eq_square simp flip: power_add mult_2)
  finally have "(\<lambda>n. (1 - a ^ 2 * (q ^ 2) ^ n)) has_prod ?lhs" .
  moreover have "(\<lambda>n. (1 - a ^ 2 * (q ^ 2) ^ n)) has_prod qpochhammer_inf (a^2) (q^2)"
    by (intro has_prod_qpochhammer_inf) (use assms in \<open>auto simp: norm_power power_less_one_iff\<close>)
  ultimately show ?thesis
    using has_prod_unique2 by blast
qed


subsection \<open>Two series expansions by Euler\<close>

text \<open>
  The following two theorems and their proofs are taken from Bellman~\cite{bellman1961}[\S 40].
  He credits them, in their original form, to Euler. One could also deduce these relatively
  easily from the infinite version of the $q$-binomial theorem (which we will prove later),
  but the proves given by Bellman are so nice that I do not want to omit them from here.

  The first theorem states that for any complex $x,t$ with $|x|<1$, we have:
  \[(t; x)_\infty = \prod_{k=0}^\infty (1 - tx^k) = 
      \sum_{n=0}^\infty \frac{x^{n(n-1)/2} t^n}{(x-1) \cdots (x^n-1)}\]
  This tells us the power series expansion for $f_x(t) = (t; x)_\infty$.
\<close>
lemma
  fixes x :: complex
  assumes x: "norm x < 1"
  shows sums_qpochhammer_inf_complex:
          "(\<lambda>n. x^(n*(n-1) div 2) * t^n / (\<Prod>k=1..n. x^k - 1)) sums qpochhammer_inf t x"
    and has_fps_expansion_qpochhammer_inf_complex:
          "(\<lambda>t. qpochhammer_inf t x) has_fps_expansion
             Abs_fps (\<lambda>n. x^(n*(n-1) div 2) / (\<Prod>k=1..n. x^k - 1))"
proof -
  text \<open>
    For a fixed $x$, we define $f(t) = (t; x)_\infty$ and note that $f$ satisfies the
    functional equation $f(t) = (1-t) f(tx)$.
  \<close>
  define f where "f = (\<lambda>t. qpochhammer_inf t x)"
  have f_eq: "f t = (1 - t) * f (t * x)" for t
    unfolding f_def using qpochhammer_inf_mult_q[of x t] x by simp
  define F where "F = fps_expansion f 0"
  define a where "a = fps_nth F"
  have ana: "f analytic_on UNIV"
    unfolding f_def by (intro analytic_intros) (use x in auto)

  text \<open>
    We note that $f$ is entire and therefore has a Maclaurin expansion, say
    $f(t) = \sum_{n=0}^\infty a_n x^n$.
  \<close>
  have F: "f has_fps_expansion F"
    unfolding F_def by (intro analytic_at_imp_has_fps_expansion_0 analytic_on_subset[OF ana]) auto
  have "fps_conv_radius F \<ge> \<infinity>"
    unfolding F_def by (rule conv_radius_fps_expansion) (auto intro!: analytic_imp_holomorphic ana)
  hence [simp]: "fps_conv_radius F = \<infinity>"
    by simp
  have F_sums: "(\<lambda>n. fps_nth F n * t ^ n) sums f t" for t
  proof -
    have "(\<lambda>n. fps_nth F n * t ^ n) sums eval_fps F t"
      using sums_eval_fps[of t F] by simp
    also have "eval_fps F t = f t"
      by (rule has_fps_expansion_imp_eval_fps_eq[OF F, of _ "norm t + 1"])
         (auto intro!: analytic_imp_holomorphic analytic_on_subset[OF ana])
    finally show ?thesis .
  qed

  have F_eq: "F = (1 - fps_X) * (F oo (fps_const x * fps_X))"
  proof -
    have "(\<lambda>t. (1 - t) * (f \<circ> (\<lambda>t. t * x)) t) has_fps_expansion 
            (fps_const 1 - fps_X) * (F oo (fps_X * fps_const x))"
      by (intro fps_expansion_intros F) auto
    also have "\<dots> = (1 - fps_X) * (F oo (fps_const x * fps_X))"
      by (simp add: mult_ac)
    also have "(\<lambda>t. (1 - t) * (f \<circ> (\<lambda>t. t * x)) t) = f"
      unfolding o_def by (intro ext f_eq [symmetric])
    finally show "F = (1 - fps_X) * (F oo (fps_const x * fps_X))"
      using F fps_expansion_unique_complex by blast
  qed

  have a_0 [simp]: "a 0 = 1"
    using has_fps_expansion_imp_0_eq_fps_nth_0[OF F] by (simp add: a_def f_def)

  text \<open>
    Applying the functional equation to the Maclaurin series, we obtain a recurrence
    for the coefficients $a_n$, namely $a_{n+1} = \frac{a_n x^n}{x^{n+1} - 1}$.
  \<close>
  have a_rec: "(x ^ Suc n - 1) * a (Suc n) = x ^ n * a n" for n
  proof -
    have "a (Suc n) = fps_nth F (Suc n)"
      by (simp add: a_def)
    also have "F = (F oo (fps_const x * fps_X)) - fps_X * (F oo (fps_const x * fps_X))"
      by (subst F_eq) (simp_all add: algebra_simps)
    also have "fps_nth \<dots> (Suc n) = x ^ Suc n * a (Suc n) - x ^ n * a n"
      by (simp add: fps_compose_linear a_def)
    finally show "(x ^ Suc n - 1) * a (Suc n) = x ^ n * a n"
      by (simp add: algebra_simps)
  qed

  define tri where "tri = (\<lambda>n::nat. n * (n-1) div 2)"
  have not_one: "x ^ k \<noteq> 1" if k: "k > 0" for k :: nat
  proof -
    have "norm (x ^ k) < 1"
      using x k by (simp add: norm_power power_less_one_iff)
    thus ?thesis
      by auto
  qed

  text \<open>
    The recurrence is easily solved and we get 
    $a_n = x^{n(n-1)/2}{(x-1)(x^2-1)\cdots(x^n - 1)}$.
  \<close>
  have a_sol: "(\<Prod>k=1..n. (x^k - 1)) * a n = x ^ tri n" for n
  proof (induction n)
    case 0
    thus ?case
      by (simp add: tri_def)
  next
    case (Suc n)
    have "(\<Prod>k=1..Suc n. (x^k - 1)) * a (Suc n) =
          (\<Prod>k=1..n. x ^ k - 1) * ((x ^ Suc n - 1) * a (Suc n))"
      by (simp add: a_rec mult_ac)
    also have "\<dots> = (\<Prod>k = 1..n. x ^ k - 1) * a n * x ^ n"
      by (subst a_rec) simp_all
    also have "(\<Prod>k=1..n. x ^ k - 1) * a n = x ^ tri n"
      by (subst Suc.IH) auto
    also have "x ^ tri n * x ^ n = x ^ (tri n + (2*n) div 2)"
      by (simp add: power_add)
    also have "tri n + (2*n) div 2 = tri (Suc n)"
      unfolding tri_def
      by (subst div_plus_div_distrib_dvd_left [symmetric]) (auto simp: algebra_simps)
    finally show ?case .
  qed

  have a_sol': "a n = x ^ tri n / (\<Prod>k=1..n. (x ^ k - 1))" for n
    using not_one a_sol[of n] by (simp add: divide_simps mult_ac)

  show "(\<lambda>n. x ^ tri n * t ^ n / (\<Prod>k=1..n. x ^ k - 1)) sums f t"
    using F_sums[of t] a_sol' by (simp add: a_def)

  have "F = Abs_fps (\<lambda>n. x^(n*(n-1) div 2) / (\<Prod>k=1..n. x^k - 1))"
    by (rule fps_ext) (simp add: a_sol'[unfolded a_def] tri_def)
  thus "f has_fps_expansion Abs_fps (\<lambda>n. x^(n*(n-1) div 2) / (\<Prod>k=1..n. x^k - 1))"
    using F by simp
qed

lemma sums_qpochhammer_inf_real:
  assumes "\<bar>x\<bar> < (1 :: real)"
  shows   "(\<lambda>n. x^(n*(n-1) div 2) * t^n / (\<Prod>k=1..n. x^k - 1)) sums qpochhammer_inf t x"
proof -
  have "(\<lambda>n. complex_of_real x ^ (n*(n-1) div 2) * of_real t ^ n / (\<Prod>k=1..n. of_real x ^ k - 1)) 
          sums qpochhammer_inf (of_real t) (of_real x)" (is "?f sums ?S")
    by (intro sums_qpochhammer_inf_complex) (use assms in auto)
  also have "?f = (\<lambda>n. complex_of_real (x ^ (n*(n-1) div 2) * t ^ n / (\<Prod>k=1..n. x ^ k - 1)))"
    by simp
  also have "qpochhammer_inf (of_real t) (of_real x) = complex_of_real (qpochhammer_inf t x)"
    by (rule qpochhammer_inf_of_real) fact
  finally show ?thesis
    by (subst (asm) sums_of_real_iff)
qed

lemma norm_summable_qpochhammer_inf:
  fixes x t :: "'a :: {real_normed_field}"
  assumes "norm x < 1"
  shows   "summable (\<lambda>n. norm (x^(n*(n-1) div 2) * t ^ n / (\<Prod>k=1..n. x^k - 1)))"
proof -
  have "norm x < 1"
    using assms by simp
  then obtain r where "norm x < r" "r < 1"
    using dense by blast
  hence r: "0 < r" "norm x < r" "r < 1"
    using le_less_trans[of 0 "norm x" r] by auto
  define R where "R = Max {2, norm t, r + 1}"
  have R: "r < R" "norm t \<le> R" "R > 1"
    unfolding R_def by auto

  show ?thesis
  proof (rule summable_comparison_test_bigo)
    show "summable (\<lambda>n. norm ((1/2::real) ^ n))"
      unfolding norm_power norm_divide by (rule summable_geometric) (use r in auto)
  next
    have "(\<lambda>n. norm (x ^ (n * (n - 1) div 2) * t ^ n / (\<Prod>k = 1..n. x ^ k - 1))) \<in> 
            O(\<lambda>n. r^(n*(n-1) div 2) * R ^ n / (1 - r) ^ n)"
    proof (rule bigoI[of _ 1], intro always_eventually allI)
      fix n :: nat
      have "norm (norm (x^(n*(n-1) div 2) * t ^ n / (\<Prod>k=1..n. x^k - 1))) =
              norm x ^ (n * (n - 1) div 2) * norm t ^ n / (\<Prod>k=1..n. norm (1 - x ^ k))"
        by (simp add: norm_power norm_mult norm_divide norm_minus_commute abs_prod flip: prod_norm)
      also have "\<dots> \<le> norm x ^ (n * (n - 1) div 2) * norm t ^ n / (\<Prod>k=1..n. 1 - norm x)"
      proof (intro divide_left_mono mult_pos_pos prod_pos prod_mono conjI mult_nonneg_nonneg)
        fix k :: nat assume k: "k \<in> {1..n}"
        have "norm x ^ k \<le> norm x ^ 1"
          by (intro power_decreasing) (use assms k in auto)
        hence "1 - norm x \<le> norm (1::'a) - norm (x ^ k)"
          by (simp add: norm_power)
        also have "\<dots> \<le> norm (1 - x ^ k)"
          by norm
        finally show "1 - norm x \<le> norm (1 - x ^ k)" .
        have "0 < 1 - norm x"
          using assms by simp
        also have "\<dots> \<le> norm (1 - x ^ k)"
          by fact
        finally show "norm (1 - x ^ k) > 0" .
      qed (use assms in auto)
      also have "(\<Prod>k=1..n. 1 - norm x) = (1 - norm x) ^ n"
        by simp
      also have "norm x ^ (n*(n-1) div 2) * norm t ^ n / (1 - norm x) ^ n \<le> 
                 r ^ (n*(n-1) div 2) * R ^ n / (1 - r) ^ n"
        by (intro frac_le mult_mono power_mono) (use r R in auto)
      also have "\<dots> \<le> abs (r^(n*(n-1) div 2) * R ^ n / (1 - r) ^ n)"
        by linarith
      finally show "norm (norm (x ^ (n * (n - 1) div 2) * t ^ n / (\<Prod>k = 1..n. x ^ k - 1)))
                     \<le> 1 * norm (r ^ (n * (n - 1) div 2) * R ^ n / (1 - r) ^ n)"
        by simp
    qed
    also have "(\<lambda>n. r ^ (n*(n-1) div 2) * R ^ n / (1 - r) ^ n) \<in> O(\<lambda>n. (1/2) ^ n)"
      using r R by real_asymp
    finally show "(\<lambda>n. norm (x ^ (n * (n - 1) div 2) * t ^ n / (\<Prod>k = 1..n. x ^ k - 1))) \<in> 
                    O(\<lambda>n. (1/2) ^ n)" .
  qed
qed



text \<open>
  The second theorem states that for any complex $x,t$ with $|x|<1$, $|t|<1$, we have:
  \[\frac{1}{(t; x)_\infty} = \prod_{k=0}^\infty \frac{1}{1 - tx^k} = 
      \sum_{n=0}^\infty \frac{t^n}{(1-x)\cdots(1-x^n)}\]
  This gives us the multiplicative inverse of the power series from the previous theorem.
\<close>
lemma
  fixes x :: complex
  assumes x: "norm x < 1" and t: "norm t < 1"
  shows sums_inverse_qpochhammer_inf_complex:
          "(\<lambda>n. t^n / (\<Prod>k=1..n. 1 - x^k)) sums inverse (qpochhammer_inf t x)"
    and has_fps_expansion_inverse_qpochhammer_inf_complex:
          "(\<lambda>t. inverse (qpochhammer_inf t x)) has_fps_expansion
             Abs_fps (\<lambda>n. 1 / (\<Prod>k=1..n. 1 - x^k))"
proof -
  text \<open>
    The proof is very similar to the one before, except that our function is now
    $g(x) = 1 / (t; x)_\infty$ with the functional equation is $g(tx) = (1-t)g(t)$.
  \<close>
  define f where "f = (\<lambda>t. qpochhammer_inf t x)"
  define g where "g = (\<lambda>t. inverse (f t))"
  have f_nz: "f t \<noteq> 0" if t: "norm t < 1" for t
  proof
    assume "f t = 0"
    then obtain n where "t * x ^ n = 1"
      using x by (auto simp: qpochhammer_inf_zero_iff f_def mult_ac)
    have "norm (t * x ^ n) = norm t * norm (x ^ n)"
      by (simp add: norm_mult)
    also have "\<dots> \<le> norm t * 1"
      using x by (intro mult_left_mono) (auto simp: norm_power power_le_one_iff)
    also have "norm t < 1"
      using t by simp
    finally show False
      using \<open>t * x ^ n = 1\<close> by simp
  qed

  have mult_less_1: "a * b < 1" if "0 \<le> a" "a < 1" "b \<le> 1" for a b :: real
  proof -
    have "a * b \<le> a * 1"
      by (rule mult_left_mono) (use that in auto)
    also have "a < 1"
      by fact
    finally show ?thesis
      by simp
  qed

  have g_eq: "g (t * x) = (1 - t) * g(t)" if t: "norm t < 1" for t
  proof -
    have "f t = (1 - t) * f (t * x)"
      using qpochhammer_inf_mult_q[of x t] x
      by (simp add: algebra_simps power2_eq_square f_def)
    moreover have "norm (t * x) < 1"
      using t x by (simp add: norm_mult mult_less_1)
    ultimately show ?thesis
      using t by (simp add: g_def field_simps f_nz)
  qed


  define G where "G = fps_expansion g 0"
  define a where "a = fps_nth G"
  have [analytic_intros]: "f analytic_on A" for A
    unfolding f_def by (intro analytic_intros) (use x in auto)
  have ana: "g analytic_on ball 0 1" unfolding g_def 
    by (intro analytic_intros)
       (use x in \<open>auto simp: qpochhammer_inf_zero_iff f_nz\<close>)
  have G: "g has_fps_expansion G" unfolding G_def
    by (intro analytic_at_imp_has_fps_expansion_0 analytic_on_subset[OF ana]) auto
  have "fps_conv_radius G \<ge> 1"
    unfolding G_def 
    by (rule conv_radius_fps_expansion) 
       (auto intro!: analytic_imp_holomorphic ana analytic_on_subset[OF ana])
  
  have G_sums: "(\<lambda>n. fps_nth G n * t ^ n) sums g t" if t: "norm t < 1" for t
  proof -
    have "ereal (norm t) < 1"
      using t by simp
    also have "\<dots> \<le> fps_conv_radius G"
      by fact
    finally have "(\<lambda>n. fps_nth G n * t ^ n) sums eval_fps G t"
      using sums_eval_fps[of t G] by simp
    also have "eval_fps G t = g t"
      by (rule has_fps_expansion_imp_eval_fps_eq[OF G, of _ 1])
         (auto intro!: analytic_imp_holomorphic analytic_on_subset[OF ana] t)
    finally show ?thesis .
  qed

  have G_eq: "(G oo (fps_const x * fps_X)) - (1 - fps_X) * G = 0"
  proof -
    define G' where "G' = (G oo (fps_const x * fps_X)) - (1 - fps_X) * G"
    have "(\<lambda>t. (g \<circ> (\<lambda>t. t * x)) t - (1 - t) * g t) has_fps_expansion G'"
      unfolding G'_def by (subst mult.commute, intro fps_expansion_intros G) auto
    also have "eventually (\<lambda>t. t \<in> ball 0 1) (nhds (0::complex))"
      by (intro eventually_nhds_in_open) auto
    hence "eventually (\<lambda>t. (g \<circ> (\<lambda>t. t * x)) t - (1 - t) * g t = 0) (nhds 0)"
      unfolding o_def by eventually_elim (subst g_eq, auto)
    hence "(\<lambda>t. (g \<circ> (\<lambda>t. t * x)) t - (1 - t) * g t) has_fps_expansion G' \<longleftrightarrow>
           (\<lambda>t. 0) has_fps_expansion G'"
      by (intro has_fps_expansion_cong refl)
    finally have "G' = 0"
      by (rule fps_expansion_unique_complex) auto
    thus ?thesis
      unfolding G'_def .
  qed

  have not_one: "x ^ k \<noteq> 1" if k: "k > 0" for k :: nat
  proof -
    have "norm (x ^ k) < 1"
      using x k by (simp add: norm_power power_less_one_iff)
    thus ?thesis
      by auto
  qed

  have a_rec: " a (Suc m) = a m / (1 - x ^ Suc m)" for m
  proof -
    have "0 = fps_nth ((G oo (fps_const x * fps_X)) - (1 - fps_X) * G) (Suc m)"
      by (subst G_eq) simp_all
    also have "\<dots> = (x ^ Suc m - 1) * a (Suc m) + a m"
      by (simp add: ring_distribs fps_compose_linear a_def)
    finally show ?thesis
      using not_one[of "Suc m"] by (simp add: field_simps)
  qed

  have a_0: "a 0 = 1"
    using has_fps_expansion_imp_0_eq_fps_nth_0[OF G] by (simp add: a_def f_def g_def)
  have a_sol: "a n = 1 / (\<Prod>k=1..n. (1 - x^k))" for n
    by (induction n) (simp_all add: a_0 a_rec)

  show "(\<lambda>n. t^n / (\<Prod>k=1..n. 1 - x ^ k)) sums (inverse (qpochhammer_inf t x))"
    using G_sums[of t] t by (simp add: a_sol[unfolded a_def] f_def g_def)

  have "G = Abs_fps (\<lambda>n. 1 / (\<Prod>k=1..n. 1 - x^k))"
    by (rule fps_ext) (simp add: a_sol[unfolded a_def])
  thus "g has_fps_expansion Abs_fps (\<lambda>n. 1 / (\<Prod>k=1..n. 1 - x^k))"
    using G by simp
qed

lemma sums_inverse_qpochhammer_inf_real:
  assumes "\<bar>x\<bar> < (1 :: real)" "\<bar>t\<bar> < 1"
  shows   "(\<lambda>n. t^n / (\<Prod>k=1..n. 1 - x^k)) sums inverse (qpochhammer_inf t x)"
proof -
  have "(\<lambda>n. complex_of_real t ^ n / (\<Prod>k=1..n. 1 - of_real x ^ k)) 
          sums inverse (qpochhammer_inf (of_real t) (of_real x))" (is "?f sums ?S")
    by (intro sums_inverse_qpochhammer_inf_complex) (use assms in auto)
  also have "?f = (\<lambda>n. complex_of_real (t ^ n / (\<Prod>k=1..n. 1 - x ^ k)))"
    by simp
  also have "inverse (qpochhammer_inf (of_real t) (of_real x)) = 
             complex_of_real (inverse (qpochhammer_inf t x))"
    by (subst qpochhammer_inf_of_real) (use assms in auto)
  finally show ?thesis
    by (subst (asm) sums_of_real_iff)
qed

lemma norm_summable_inverse_qpochhammer_inf:
  fixes x t :: "'a :: {real_normed_field}"
  assumes "norm x < 1" "norm t < 1"
  shows   "summable (\<lambda>n. norm (t ^ n / (\<Prod>k=1..n. 1 - x^k)))"
proof (rule summable_comparison_test)
  show "summable (\<lambda>n. norm t ^ n / (\<Prod>k=1..n. 1 - norm x ^ k))"
    by (rule sums_summable, rule sums_inverse_qpochhammer_inf_real) (use assms in auto)
next
  show "\<exists>N. \<forall>n\<ge>N. norm (norm (t ^ n / (\<Prod>k = 1..n. 1 - x ^ k))) \<le> 
                  norm t ^ n / (\<Prod>k = 1..n. 1 - norm x ^ k)"
  proof (intro exI[of _ 0] allI impI)
    fix n :: nat
    have "norm (norm (t ^ n / (\<Prod>k=1..n. 1 - x ^ k))) = norm t ^ n / (\<Prod>k=1..n. norm (1 - x ^ k))"
      by (simp add: norm_mult norm_power norm_divide abs_prod flip:prod_norm)
    also have "\<dots> \<le> norm t ^ n / (\<Prod>k=1..n. 1 - norm x ^ k)"
    proof (intro divide_left_mono mult_pos_pos prod_pos prod_mono)
      fix k assume k: "k \<in> {1..n}"
      have *: "0 < norm (1::'a) - norm (x ^ k)"
        using assms k by (simp add: norm_power power_less_one_iff)
      also have "\<dots> \<le> norm (1 - x ^ k)"
        by norm
      finally show "norm (1 - x ^ k) > 0" .
      from * show "1 - norm x ^ k > 0"
        by (simp add: norm_power)
      have "norm (1::'a) - norm (x ^ k) \<le> norm (1 - x ^ k)"
        by norm
      thus "0 \<le> 1 - norm x ^ k \<and> 1 - norm x ^ k \<le> norm (1 - x ^ k)"
        using assms by (auto simp: norm_power power_le_one_iff)
    qed auto
    finally show "norm (norm (t ^ n / (\<Prod>k = 1..n. 1 - x ^ k)))
                  \<le> norm t ^ n / (\<Prod>k = 1..n. 1 - norm x ^ k)" .
  qed
qed


subsection \<open>Euler's function\<close>

text \<open>
  Euler's $\phi$ function is closely related to the Dedekind $\eta$ function and the Jacobi
  $\vartheta$ nullwert functions. The $q$-Pochhammer symbol gives us a simple and convenient
  way to define it.
\<close>
definition euler_phi :: "'a :: {real_normed_field, banach, heine_borel} \<Rightarrow> 'a" where
  "euler_phi q = qpochhammer_inf q q"

lemma euler_phi_0 [simp]: "euler_phi 0 = 1"
  by (simp add: euler_phi_def)

lemma abs_convergent_euler_phi:
  assumes "(q :: 'a :: real_normed_div_algebra) \<in> ball 0 1"
  shows   "abs_convergent_prod (\<lambda>n. 1 - q ^ Suc n)"
proof (rule summable_imp_abs_convergent_prod)
  show "summable (\<lambda>n. norm (1 - q ^ Suc n - 1))"
    using assms by (subst summable_Suc_iff) (auto simp: norm_power)
qed

lemma convergent_euler_phi:
  assumes "(q :: 'a :: {real_normed_field, banach}) \<in> ball 0 1"
  shows   "convergent_prod (\<lambda>n. 1 - q ^ Suc n)"
  using abs_convergent_euler_phi[OF assms] abs_convergent_prod_imp_convergent_prod by blast

lemma has_prod_euler_phi:
  "norm q < 1 \<Longrightarrow> (\<lambda>n. 1 - q ^ Suc n) has_prod euler_phi q"
  using has_prod_qpochhammer_inf[of q q] by (simp add: euler_phi_def)

lemma euler_phi_nonzero [simp]:
  assumes x: "x \<in> ball 0 1"
  shows   "euler_phi x \<noteq> 0"
  using assms by (simp add: euler_phi_def qpochhammer_inf_nonzero)

lemma holomorphic_euler_phi [holomorphic_intros]:
  assumes [holomorphic_intros]: "f holomorphic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (f z) < 1"
  shows   "(\<lambda>z. euler_phi (f z)) holomorphic_on A"
proof -
  have *: "euler_phi holomorphic_on ball 0 1"
    unfolding euler_phi_def by (intro holomorphic_intros) auto
  show ?thesis
    by (rule holomorphic_on_compose_gen[OF assms(1) *, unfolded o_def]) (use assms(2) in auto)
qed

lemma analytic_euler_phi [analytic_intros]:
  assumes [analytic_intros]: "f analytic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (f z) < 1"
  shows   "(\<lambda>z. euler_phi (f z)) analytic_on A"
  using assms(2) by (auto intro!: analytic_intros simp: euler_phi_def)

lemma meromorphic_on_euler_phi [meromorphic_intros]:
  "f analytic_on A \<Longrightarrow> (\<And>z. z \<in> A \<Longrightarrow> norm (f z) < 1) \<Longrightarrow> (\<lambda>z. euler_phi (f z)) meromorphic_on A"
  unfolding euler_phi_def by (intro meromorphic_intros)

lemma continuous_on_euler_phi [continuous_intros]:
  assumes "continuous_on A f" "\<And>z. z \<in> A \<Longrightarrow> norm (f z) < 1"
  shows   "continuous_on A (\<lambda>z. euler_phi (f z))"
  using assms unfolding euler_phi_def by (intro continuous_intros) auto

lemma continuous_euler_phi [continuous_intros]:
  fixes a q :: "'b :: t2_space \<Rightarrow> 'a :: {real_normed_field, banach, heine_borel}"
  assumes "continuous (at x within A) f" "norm (f x) < 1"
  shows   "continuous (at x within A) (\<lambda>x. euler_phi (f x))"
  unfolding euler_phi_def by (intro continuous_intros assms)

lemma tendsto_euler_phi [tendsto_intros]:
  assumes [tendsto_intros]: "(f \<longlongrightarrow> c) F" and "norm c < 1"
  shows   "((\<lambda>x. euler_phi (f x)) \<longlongrightarrow> euler_phi c) F"
  unfolding euler_phi_def using assms by (auto intro!: tendsto_intros)

end