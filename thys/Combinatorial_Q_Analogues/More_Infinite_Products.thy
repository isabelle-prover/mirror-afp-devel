subsection \<open>Additional facts about infinite products\<close>
theory More_Infinite_Products
  imports "HOL-Analysis.Analysis"
begin

(* These three facts about actually about products, but we do need them *)
lemma uniform_limit_singleton: "uniform_limit {x} f g F \<longleftrightarrow> ((\<lambda>n. f n x) \<longlongrightarrow> g x) F"
  by (simp add: uniform_limit_iff tendsto_iff)

lemma uniformly_convergent_on_singleton:
  "uniformly_convergent_on {x} f \<longleftrightarrow> convergent (\<lambda>n. f n x)"
  by (auto simp: uniformly_convergent_on_def uniform_limit_singleton convergent_def)

lemma uniformly_convergent_on_subset:
  assumes "uniformly_convergent_on A f" "B \<subseteq> A"
  shows   "uniformly_convergent_on B f"
  using assms by (meson uniform_limit_on_subset uniformly_convergent_on_def)



(* very general theorems about infinite products *)
lemma raw_has_prod_imp_nonzero:
  assumes "raw_has_prod f N P" "n \<ge> N"
  shows   "f n \<noteq> 0"
proof
  assume "f n = 0"
  from assms(1) have lim: "(\<lambda>m. (\<Prod>k\<le>m. f (k + N))) \<longlonglongrightarrow> P" and "P \<noteq> 0"
    unfolding raw_has_prod_def by blast+
  have "eventually (\<lambda>m. m \<ge> n - N) at_top"
    by (rule eventually_ge_at_top)
  hence "eventually (\<lambda>m. (\<Prod>k\<le>m. f (k + N)) = 0) at_top"
  proof eventually_elim
    case (elim m)
    have "f ((n - N) + N) = 0" "n - N \<in> {..m}" "finite {..m}"
      using \<open>n \<ge> N\<close> \<open>f n = 0\<close> elim by auto
    thus "(\<Prod>k\<le>m. f (k + N)) = 0"
      using prod_zero[of "{..m}" "\<lambda>k. f (k + N)"] by blast
  qed
  with lim have "P = 0"
    by (simp add: LIMSEQ_const_iff tendsto_cong)
  thus False
    using \<open>P \<noteq> 0\<close> by contradiction
qed

lemma has_prod_imp_tendsto:
  fixes f :: "nat \<Rightarrow> 'a :: {semidom, t2_space}"
  assumes "f has_prod P"
  shows   "(\<lambda>n. \<Prod>k\<le>n. f k) \<longlonglongrightarrow> P"
proof (cases "P = 0")
  case False
  with assms show ?thesis
    by (auto simp: has_prod_def raw_has_prod_def)
next
  case True
  with assms obtain N P' where "f N = 0" "raw_has_prod f (Suc N) P'"
    by (auto simp: has_prod_def)
  thus ?thesis
    using LIMSEQ_prod_0 True \<open>f N = 0\<close> by blast
qed

lemma has_prod_imp_tendsto':
  fixes f :: "nat \<Rightarrow> 'a :: {semidom, t2_space}"
  assumes "f has_prod P"
  shows   "(\<lambda>n. \<Prod>k<n. f k) \<longlonglongrightarrow> P"
  using has_prod_imp_tendsto[OF assms] LIMSEQ_lessThan_iff_atMost by blast

lemma convergent_prod_tendsto_imp_has_prod:
  fixes f :: "nat \<Rightarrow> 'a :: real_normed_field"
  assumes "convergent_prod f" "(\<lambda>n. (\<Prod>i\<le>n. f i)) \<longlonglongrightarrow> P"
  shows   "f has_prod P"
  using assms by (metis convergent_prod_imp_has_prod has_prod_imp_tendsto limI)

(*
  grouping factors into chunks of the same size

  Only one direction; other direction requires "real_normed_field" (see below).
  Not sure if real_normed_field is really necessary, but I don't see how else to do it.
*)
lemma has_prod_group_nonzero: 
  fixes f :: "nat \<Rightarrow> 'a :: {semidom, t2_space}"
  assumes "f has_prod P" "k > 0" "P \<noteq> 0"
  shows   "(\<lambda>n. (\<Prod>i\<in>{n*k..<n*k+k}. f i)) has_prod P"
proof -
  have "(\<lambda>n. \<Prod>k<n. f k) \<longlonglongrightarrow> P"
    using assms(1) by (intro has_prod_imp_tendsto')
  hence "(\<lambda>n. \<Prod>k<n*k. f k) \<longlonglongrightarrow> P"
    by (rule filterlim_compose) (use \<open>k > 0\<close> in real_asymp)
  also have "(\<lambda>n. \<Prod>k<n*k. f k) = (\<lambda>n. \<Prod>m<n. prod f {m*k..<m*k+k})"
    by (subst prod.nat_group [symmetric]) auto
  finally have "(\<lambda>n. \<Prod>m\<le>n. prod f {m*k..<m*k+k}) \<longlonglongrightarrow> P"
    by (subst (asm) LIMSEQ_lessThan_iff_atMost)
  hence "raw_has_prod (\<lambda>n. prod f {n*k..<n*k+k}) 0 P"
    using \<open>P \<noteq> 0\<close> by (auto simp: raw_has_prod_def)
  thus ?thesis
    by (auto simp: has_prod_def)
qed

lemma has_prod_group:
  fixes f :: "nat \<Rightarrow> 'a :: real_normed_field"
  assumes "f has_prod P" "k > 0"
  shows   "(\<lambda>n. (\<Prod>i\<in>{n*k..<n*k+k}. f i)) has_prod P"
proof (rule convergent_prod_tendsto_imp_has_prod)
  have "(\<lambda>n. \<Prod>k<n. f k) \<longlonglongrightarrow> P"
    using assms(1) by (intro has_prod_imp_tendsto')
  hence "(\<lambda>n. \<Prod>k<n*k. f k) \<longlonglongrightarrow> P"
    by (rule filterlim_compose) (use \<open>k > 0\<close> in real_asymp)
  also have "(\<lambda>n. \<Prod>k<n*k. f k) = (\<lambda>n. \<Prod>m<n. prod f {m*k..<m*k+k})"
    by (subst prod.nat_group [symmetric]) auto
  finally show "(\<lambda>n. \<Prod>m\<le>n. prod f {m*k..<m*k+k}) \<longlonglongrightarrow> P"
    by (subst (asm) LIMSEQ_lessThan_iff_atMost)
next
  from assms obtain N P' where prod1: "raw_has_prod f N P'"
    by (auto simp: has_prod_def)
  define N' where "N' = nat \<lceil>real N / real k\<rceil>"
  have "k * N' \<ge> N"
  proof -
    have "(real N / real k * real k) \<le> real (N' * k)"
      unfolding N'_def of_nat_mult by (intro mult_right_mono) (use \<open>k > 0\<close> in auto)
    also have "real N / real k * real k = real N"
      using \<open>k > 0\<close> by simp
    finally show ?thesis
      by (simp only: mult.commute of_nat_le_iff)
  qed

  obtain P'' where prod2: "raw_has_prod f (k * N') P''"
    using prod1 \<open>k * N' \<ge> N\<close> by (rule raw_has_prod_ignore_initial_segment)
  hence "P'' \<noteq> 0"
    by (auto simp: raw_has_prod_def)
  from prod2 have "raw_has_prod (\<lambda>n. f (n + k * N')) 0 P''"
    by (simp add: raw_has_prod_def)
  hence "(\<lambda>n. f (n + k * N')) has_prod P''"
    by (auto simp: has_prod_def)
  hence "(\<lambda>n. \<Prod>i=n*k..<n*k+k. f (i + k * N')) has_prod P''"
    by (rule has_prod_group_nonzero) fact+
  hence "convergent_prod (\<lambda>n. \<Prod>i=n*k..<n*k+k. f (i + k * N'))"
    using has_prod_iff by blast
  also have "(\<lambda>n. \<Prod>i=n*k..<n*k+k. f (i + k * N')) = (\<lambda>n. \<Prod>i=(n+N')*k..<(n+N')*k+k. f i)"
  proof
    fix n :: nat
    show "(\<Prod>i=n*k..<n*k+k. f (i + k * N')) = (\<Prod>i=(n+N')*k..<(n+N')*k+k. f i)"
      by (rule prod.reindex_bij_witness[of _ "\<lambda>n. n - k*N'" "\<lambda>n. n + k*N'"])
         (auto simp: algebra_simps)
  qed
  also have "convergent_prod \<dots> \<longleftrightarrow> convergent_prod (\<lambda>n. (\<Prod>i=n*k..<n*k+k. f i))"
    by (rule convergent_prod_iff_shift)
  finally show "convergent_prod (\<lambda>n. prod f {n * k..<n * k + k})" .
qed


(* non-negativity, positivity, monotonicity of infinite products (on the reals)
   coud perhaps be generalised to other types; not sure if it's worth it. *)
lemma has_prod_nonneg:
  assumes "f has_prod P" "\<And>n. f n \<ge> (0::real)"
  shows   "P \<ge> 0"
proof (rule tendsto_le)
  show "((\<lambda>n. \<Prod>i\<le>n. f i)) \<longlonglongrightarrow> P"
    using assms(1) by (rule has_prod_imp_tendsto)
  show "(\<lambda>n. 0::real) \<longlonglongrightarrow> 0"
    by auto
qed (use assms in \<open>auto intro!: always_eventually prod_nonneg\<close>)

lemma has_prod_pos:
  assumes "f has_prod P" "\<And>n. f n > (0::real)"
  shows   "P > 0"
proof -
  have "P \<ge> 0"
    by (rule has_prod_nonneg[OF assms(1)]) (auto intro!: less_imp_le assms(2))
  moreover have "f n \<noteq> 0" for n
    using assms(2)[of n] by auto
  hence "P \<noteq> 0"
    using has_prod_0_iff[of f] assms by auto
  ultimately show ?thesis
    by linarith
qed

lemma prod_ge_prodinf: 
  fixes f :: "nat \<Rightarrow> 'a::{linordered_idom,linorder_topology}"
  assumes "f has_prod a" "\<And>i. 0 \<le> f i" "\<And>i. i \<ge> n \<Longrightarrow> f i \<le> 1"
  shows "prod f {..<n} \<ge> prodinf f"
proof (rule has_prod_le; (intro conjI)?)
  show "f has_prod prodinf f"
    using assms(1) has_prod_unique by blast
  show "(\<lambda>r. if r \<in> {..<n} then f r else 1) has_prod prod f {..<n}"
    by (rule has_prod_If_finite_set) auto
next
  fix i 
  show "f i \<ge> 0"
    by (rule assms)
  show "f i \<le> (if i \<in> {..<n} then f i else 1)"
    using assms(3)[of i] by auto
qed

lemma has_prod_less:
  fixes F G :: real
  assumes less: "f m < g m"
  assumes f: "f has_prod F" and g: "g has_prod G"
  assumes pos: "\<And>n. 0 < f n" and le: "\<And>n. f n \<le> g n"
  shows   "F < G"
proof -
  define F' G' where "F' = (\<Prod>n<Suc m. f n)" and "G' = (\<Prod>n<Suc m. g n)"
  have [simp]: "f n \<noteq> 0" "g n \<noteq> 0" for n
    using pos[of n] le[of n] by auto
  have [simp]: "F' \<noteq> 0" "G' \<noteq> 0"
    by (auto simp: F'_def G'_def)
  have f': "(\<lambda>n. f (n + Suc m)) has_prod (F / F')"
    unfolding F'_def using f
    by (intro has_prod_split_initial_segment) auto
  have g': "(\<lambda>n. g (n + Suc m)) has_prod (G / G')"
    unfolding G'_def using g
    by (intro has_prod_split_initial_segment) auto
  have "F' * (F / F') < G' * (F / F')"
  proof (rule mult_strict_right_mono)
    show "F' < G'"
      unfolding F'_def G'_def
      by (rule prod_mono_strict[of m])
         (auto intro: le less_imp_le[OF pos] less_le_trans[OF pos le] less)
    show "F / F' > 0"
      using f' by (rule has_prod_pos) (use pos in auto)
  qed
  also have "\<dots> \<le> G' * (G / G')"
  proof (rule mult_left_mono)
    show "F / F' \<le> G / G'"
      using f' g' by (rule has_prod_le) (auto intro: less_imp_le[OF pos] le)
    show "G' \<ge> 0"
      unfolding G'_def by (intro prod_nonneg order.trans[OF less_imp_le[OF pos] le])
  qed
  finally show ?thesis
    by simp
qed




(* convergence criteria; especially uniform convergence of infinite products *)

text \<open>
  Cauchy's criterion for the convergence of infinite products, adapted to proving
  uniform convergence: let $f_k(x)$ be a sequence of functions such that

    \<^enum> $f_k(x)$ has uniformly bounded partial products, i.e.\ there exists a constant \<open>C\<close>
      such that $\prod_{k=0}^m f_k(x) \leq C$ for all $m$ and $x\in A$.

    \<^enum> For any $\varepsilon > 0$ there exists a number $M \in \mathbb{N}$ such that, for any
      $m, n \geq M$ and all $x\in A$ we have $|(\prod_{k=m}^n f_k(x)) - 1| < \varepsilon$

  Then $\prod_{k=0}^n f_k(x)$ converges to $\prod_{k=0}^\infty f_k(x)$ uniformly for all
  $x \in A$.
\<close>
lemma uniformly_convergent_prod_Cauchy:
  fixes f :: "nat \<Rightarrow> 'a :: topological_space \<Rightarrow> 'b :: {real_normed_div_algebra, comm_ring_1, banach}"
  assumes C: "\<And>x m. x \<in> A \<Longrightarrow> norm (\<Prod>k<m. f k x) \<le> C"
  assumes "\<And>e. e > 0 \<Longrightarrow> \<exists>M. \<forall>x\<in>A. \<forall>m\<ge>M. \<forall>n\<ge>m. dist (\<Prod>k=m..n. f k x) 1 < e"
  shows   "uniformly_convergent_on A (\<lambda>N x. \<Prod>n<N. f n x)"
proof (rule Cauchy_uniformly_convergent, rule uniformly_Cauchy_onI')
  fix \<epsilon> :: real assume \<epsilon>: "\<epsilon> > 0"
  define C' where "C' = max C 1"
  have C': "C' > 0"
    by (auto simp: C'_def)
  define \<delta> where "\<delta> = Min {2 / 3 * \<epsilon> / C', 1 / 2}"
  from \<epsilon> have "\<delta> > 0"
    using \<open>C' > 0\<close> by (auto simp: \<delta>_def)
  obtain M where M: "\<And>x m n. x \<in> A \<Longrightarrow> m \<ge> M \<Longrightarrow> n \<ge> m \<Longrightarrow> dist (\<Prod>k=m..n. f k x) 1 < \<delta>"
    using \<open>\<delta> > 0\<close> assms by fast

  show "\<exists>M. \<forall>x\<in>A. \<forall>m\<ge>M. \<forall>n>m. dist (\<Prod>k<m. f k x) (\<Prod>k<n. f k x) < \<epsilon>"
  proof (rule exI, intro ballI allI impI)
    fix x m n
    assume x: "x \<in> A" and mn: "M + 1 \<le> m" "m < n"
    show "dist (\<Prod>k<m. f k x) (\<Prod>k<n. f k x) < \<epsilon>"
    proof (cases "\<exists>k<m. f k x = 0")
      case True
      hence "(\<Prod>k<m. f k x) = 0" and "(\<Prod>k<n. f k x) = 0"
        using mn x by (auto intro!: prod_zero)
      thus ?thesis
        using \<epsilon> by simp
    next
      case False
      have *: "{..<n} = {..<m} \<union> {m..n-1}"
        using mn by auto
      have "dist (\<Prod>k<m. f k x) (\<Prod>k<n. f k x) = norm ((\<Prod>k<m. f k x) * ((\<Prod>k=m..n-1. f k x) - 1))"
        unfolding * by (subst prod.union_disjoint)
                       (use mn in \<open>auto simp: dist_norm algebra_simps norm_minus_commute\<close>)
      also have "\<dots> = (\<Prod>k<m. norm (f k x)) * dist (\<Prod>k=m..n-1. f k x) 1"
        by (simp add: norm_mult dist_norm prod_norm)
      also have "\<dots> < (\<Prod>k<m. norm (f k x)) * (2 / 3 * \<epsilon> / C')"
      proof (rule mult_strict_left_mono)
        show "dist (\<Prod>k = m..n - 1. f k x) 1 < 2 / 3 * \<epsilon> / C'"
          using M[of x m "n-1"] x mn unfolding \<delta>_def by fastforce
      qed (use False in \<open>auto intro!: prod_pos\<close>)
      also have "(\<Prod>k<m. norm (f k x)) = (\<Prod>k<M. norm (f k x)) * norm (\<Prod>k=M..<m. (f k x))"
      proof -
        have *: "{..<m} = {..<M} \<union> {M..<m}"
          using mn by auto
        show ?thesis
          unfolding * using mn by (subst prod.union_disjoint) (auto simp: prod_norm)
      qed
      also have "norm (\<Prod>k=M..<m. (f k x)) \<le> 3 / 2"
      proof -
        have "dist (\<Prod>k=M..m-1. f k x) 1 < \<delta>"
          using M[of x M "m-1"] x mn \<open>\<delta> > 0\<close> by auto
        also have "\<dots> \<le> 1 / 2"
          by (simp add: \<delta>_def)
        also have "{M..m-1} = {M..<m}"
          using mn by auto
        finally have "norm (\<Prod>k=M..<m. f k x) \<le> norm (1 :: 'b) + 1 / 2"
          by norm
        thus ?thesis
          by simp
      qed
      hence "(\<Prod>k<M. norm (f k x)) * norm (\<Prod>k = M..<m. f k x) * (2 / 3 * \<epsilon> / C') \<le>
             (\<Prod>k<M. norm (f k x)) * (3 / 2) * (2 / 3 * \<epsilon> / C')"
        using \<epsilon> C' by (intro mult_left_mono mult_right_mono prod_nonneg) auto
      also have "\<dots> \<le> C' * (3 / 2) * (2 / 3 * \<epsilon> / C')"
      proof (intro mult_right_mono)
        have "(\<Prod>k<M. norm (f k x)) \<le> C"
          using C[of x M] x by (simp add: prod_norm)
        also have "\<dots> \<le> C'"
          by (simp add: C'_def)
        finally show "(\<Prod>k<M. norm (f k x)) \<le> C'" .
      qed (use \<epsilon> C' in auto)
      finally show "dist (\<Prod>k<m. f k x) (\<Prod>k<n. f k x) < \<epsilon>"
        using \<open>C' > 0\<close> by (simp add: field_simps)
    qed
  qed
qed

text \<open>
  By instantiating the set $A$ in this result with a singleton set, we obtain the ``normal''
  Cauchy criterion for infinite products:
\<close>
lemma convergent_prod_Cauchy_sufficient:
  fixes f :: "nat \<Rightarrow> 'b :: {real_normed_div_algebra, comm_ring_1, banach}"
  assumes "\<And>e. e > 0 \<Longrightarrow> \<exists>M. \<forall>m n. M \<le> m \<longrightarrow> m \<le> n \<longrightarrow> dist (\<Prod>k=m..n. f k) 1 < e"
  shows   "convergent_prod f"
proof -
  obtain M where M: "\<And>m n. m \<ge> M \<Longrightarrow> n \<ge> m \<Longrightarrow> dist (prod f {m..n}) 1 < 1 / 2"
    using assms(1)[of "1 / 2"] by auto
  have nz: "f m \<noteq> 0" if "m \<ge> M" for m
    using M[of m m] that by auto

  have M': "dist (prod (\<lambda>k. f (k + M)) {m..<n}) 1 < 1 / 2" for m n
  proof (cases "m < n")
    case True
    have "dist (prod f {m+M..n-1+M}) 1 < 1 / 2"
      by (rule M) (use True in auto)
    also have "prod f {m+M..n-1+M} = prod (\<lambda>k. f (k + M)) {m..<n}"
      by (rule prod.reindex_bij_witness[of _ "\<lambda>k. k + M" "\<lambda>k. k - M"]) (use True in auto)
    finally show ?thesis .
  qed auto 

  have "uniformly_convergent_on {0::'b} (\<lambda>N x. \<Prod>n<N. f (n + M))"
  proof (rule uniformly_convergent_prod_Cauchy)
    fix m :: nat
    have "norm (\<Prod>k=0..<m. f (k + M)) < norm (1 :: 'b) + 1 / 2"
      using M'[of 0 m] by norm
    thus "norm (\<Prod>k<m. f (k + M)) \<le> 3 / 2"
      by (simp add: atLeast0LessThan)
  next
    fix e :: real assume e: "e > 0"
    obtain M' where M': "\<And>m n. M' \<le> m \<longrightarrow> m \<le> n \<longrightarrow> dist (\<Prod>k=m..n. f k) 1 < e"
      using assms e by blast
    show "\<exists>M'. \<forall>x\<in>{0}. \<forall>m\<ge>M'. \<forall>n\<ge>m. dist (\<Prod>k=m..n. f (k + M)) 1 < e"
    proof (rule exI[of _ M'], intro ballI impI allI)
      fix m n :: nat assume "M' \<le> m" "m \<le> n"
      thus "dist (\<Prod>k=m..n. f (k + M)) 1 < e"
        using M' by (metis add.commute add_left_mono prod.shift_bounds_cl_nat_ivl trans_le_add1)
    qed
  qed
  hence "convergent (\<lambda>N. \<Prod>n<N. f (n + M))"
    by (rule uniformly_convergent_imp_convergent[of _ _ 0]) auto
  then obtain L where L: "(\<lambda>N. \<Prod>n<N. f (n + M)) \<longlonglongrightarrow> L"
    unfolding convergent_def by blast

  show ?thesis
    unfolding convergent_prod_altdef
  proof (rule exI[of _ M], rule exI[of _ L], intro conjI)
    show "\<forall>n\<ge>M. f n \<noteq> 0"
      using nz by auto
  next
    show "(\<lambda>n. \<Prod>i\<le>n. f (i + M)) \<longlonglongrightarrow> L"
      using LIMSEQ_Suc[OF L] by (subst (asm) lessThan_Suc_atMost)
  next
    have "norm L \<ge> 1 / 2"
    proof (rule tendsto_lowerbound)
      show "(\<lambda>n. norm (\<Prod>i<n. f (i + M))) \<longlonglongrightarrow> norm L"
        by (intro tendsto_intros L)
      show "\<forall>\<^sub>F n in sequentially. 1 / 2 \<le> norm (\<Prod>i<n. f (i + M))"
      proof (intro always_eventually allI)
        fix m :: nat
        have "norm (\<Prod>k=0..<m. f (k + M)) \<ge> norm (1 :: 'b) - 1 / 2"
          using M'[of 0 m] by norm
        thus "norm (\<Prod>k<m. f (k + M)) \<ge> 1 / 2"
          by (simp add: atLeast0LessThan)
      qed
    qed auto
    thus "L \<noteq> 0"
      by auto
  qed
qed


text \<open>
  We now prove that the Cauchy criterion for pointwise convergence is both necessary
  and sufficient.
\<close>
lemma convergent_prod_Cauchy_necessary:
  fixes f :: "nat \<Rightarrow> 'b :: {real_normed_field, banach}"
  assumes "convergent_prod f" "e > 0"
  shows   "\<exists>M. \<forall>m n. M \<le> m \<longrightarrow> m \<le> n \<longrightarrow> dist (\<Prod>k=m..n. f k) 1 < e"
proof -
  have *: "\<exists>M. \<forall>m n. M \<le> m \<longrightarrow> m \<le> n \<longrightarrow> dist (\<Prod>k=m..n. f k) 1 < e"
    if f: "convergent_prod f" "0 \<notin> range f" and e: "e > 0"
    for f :: "nat \<Rightarrow> 'b" and e :: real
  proof -
    have *: "(\<lambda>n. norm (\<Prod>k<n. f k)) \<longlonglongrightarrow> norm (\<Prod>k. f k)"
      using has_prod_imp_tendsto' f(1) by (intro tendsto_norm) blast
    from f(1,2) have [simp]: "(\<Prod>k. f k) \<noteq> 0"
      using prodinf_nonzero by fastforce
    obtain M' where M': "norm (\<Prod>k<m. f k) > norm (\<Prod>k. f k) / 2" if "m \<ge> M'" for m
      using order_tendstoD(1)[OF *, of "norm (\<Prod>k. f k) / 2"]
      by (auto simp: eventually_at_top_linorder)
    define M where "M = Min (insert (norm (\<Prod>k. f k) / 2) ((\<lambda>m. norm (\<Prod>k<m. f k)) ` {..<M'}))"
    have "M > 0"
      unfolding M_def using f(2) by (subst Min_gr_iff) auto
    have norm_ge: "norm (\<Prod>k<m. f k) \<ge> M" for m
    proof (cases "m \<ge> M'")
      case True
      have "M \<le> norm (\<Prod>k. f k) / 2"
        unfolding M_def by (intro Min.coboundedI) auto
      also from True have "norm (\<Prod>k<m. f k) > norm (\<Prod>k. f k) / 2"
        by (intro M')
      finally show ?thesis by linarith
    next
      case False
      thus ?thesis
        unfolding M_def
        by (intro Min.coboundedI) auto
    qed

    have "convergent (\<lambda>n. \<Prod>k<n. f k)"
      using f(1) convergent_def has_prod_imp_tendsto' by blast
    hence "Cauchy (\<lambda>n. \<Prod>k<n. f k)"
      by (rule convergent_Cauchy)
    moreover have "e * M > 0"
      using e \<open>M > 0\<close> by auto
    ultimately obtain N where N: "dist (\<Prod>k<m. f k) (\<Prod>k<n. f k) < e * M" if "m \<ge> N" "n \<ge> N" for m n
      unfolding Cauchy_def by fast

    show "\<exists>M. \<forall>m n. M \<le> m \<longrightarrow> m \<le> n \<longrightarrow> dist (prod f {m..n}) 1 < e"
    proof (rule exI[of _ N], intro allI impI, goal_cases)
      case (1 m n)
      have "dist (\<Prod>k<m. f k) (\<Prod>k<Suc n. f k) < e * M"
        by (rule N) (use 1 in auto)
      also have "dist (\<Prod>k<m. f k) (\<Prod>k<Suc n. f k) = norm ((\<Prod>k<Suc n. f k) - (\<Prod>k<m. f k))"
        by (simp add: dist_norm norm_minus_commute)
      also have "(\<Prod>k<Suc n. f k) = (\<Prod>k\<in>{..<m}\<union>{m..n}. f k)"
        using 1 by (intro prod.cong) auto
      also have "\<dots> = (\<Prod>k\<in>{..<m}. f k) * (\<Prod>k\<in>{m..n}. f k)"
        by (subst prod.union_disjoint) auto
      also have "\<dots> - (\<Prod>k<m. f k) = (\<Prod>k<m. f k) * ((\<Prod>k\<in>{m..n}. f k) - 1)"
        by (simp add: algebra_simps)
      finally have "norm (prod f {m..n} - 1) < e * M / norm (prod f {..<m})"
        using f(2) by (auto simp add: norm_mult divide_simps mult_ac)
      also have "\<dots> \<le> e * M / M"
        using e \<open>M > 0\<close> f(2) by (intro divide_left_mono norm_ge mult_pos_pos) auto
      also have "\<dots> = e"
        using \<open>M > 0\<close> by simp
      finally show ?case
        by (simp add: dist_norm)
    qed
  qed

  obtain M where M: "f m \<noteq> 0" if "m \<ge> M" for m
    using convergent_prod_imp_ev_nonzero[OF assms(1)]
    by (auto simp: eventually_at_top_linorder)

  have "\<exists>M'. \<forall>m n. M' \<le> m \<longrightarrow> m \<le> n \<longrightarrow> dist (\<Prod>k=m..n. f (k + M)) 1 < e"
    by (rule *) (use assms M in auto)
  then obtain M' where M': "dist (\<Prod>k=m..n. f (k + M)) 1 < e" if "M' \<le> m" "m \<le> n" for m n
    by blast

  show "\<exists>M. \<forall>m n. M \<le> m \<longrightarrow> m \<le> n \<longrightarrow> dist (prod f {m..n}) 1 < e"
  proof (rule exI[of _ "M + M'"], safe, goal_cases)
    case (1 m n)
    have "dist (\<Prod>k=m-M..n-M. f (k + M)) 1 < e"
      by (rule M') (use 1 in auto)
    also have "(\<Prod>k=m-M..n-M. f (k + M)) = (\<Prod>k=m..n. f k)"
      using 1 by (intro prod.reindex_bij_witness[of _ "\<lambda>k. k - M" "\<lambda>k. k + M"]) auto
    finally show ?case .
  qed
qed

lemma convergent_prod_Cauchy_iff:
  fixes f :: "nat \<Rightarrow> 'b :: {real_normed_field, banach}"
  shows "convergent_prod f \<longleftrightarrow> (\<forall>e>0. \<exists>M. \<forall>m n. M \<le> m \<longrightarrow> m \<le> n \<longrightarrow> dist (\<Prod>k=m..n. f k) 1 < e)"
  using convergent_prod_Cauchy_necessary[of f] convergent_prod_Cauchy_sufficient[of f]
  by blast

(* Note by Manuel: this is already in the library but with an unnecessarily constrained type.
   I generalised the argument from 'b to 'a :: topological_space *)
lemma uniform_limit_suminf:
  fixes f:: "nat \<Rightarrow> 'a :: topological_space \<Rightarrow> 'b::{metric_space, comm_monoid_add}"
  assumes "uniformly_convergent_on X (\<lambda>n x. \<Sum>k<n. f k x)" 
  shows "uniform_limit X (\<lambda>n x. \<Sum>k<n. f k x) (\<lambda>x. \<Sum>k. f k x) sequentially"
proof -
  obtain S where S: "uniform_limit X (\<lambda>n x. \<Sum>k<n. f k x) S sequentially"
    using assms uniformly_convergent_on_def by blast
  then have "(\<Sum>k. f k x) = S x" if "x \<in> X" for x
    using that sums_iff sums_def by (blast intro: tendsto_uniform_limitI [OF S])
  with S show ?thesis
    by (simp cong: uniform_limit_cong')
qed

lemma uniformly_convergent_on_prod:
  fixes f :: "nat \<Rightarrow> 'a :: topological_space \<Rightarrow> 'b :: {real_normed_div_algebra, comm_ring_1, banach}"
  assumes cont: "\<And>n. continuous_on A (f n)"
  assumes A: "compact A"
  assumes conv_sum: "uniformly_convergent_on A (\<lambda>N x. \<Sum>n<N. norm (f n x))"
  shows   "uniformly_convergent_on A (\<lambda>N x. \<Prod>n<N. 1 + f n x)"
proof -
  have lim: "uniform_limit A (\<lambda>n x. \<Sum>k<n. norm (f k x)) (\<lambda>x. \<Sum>k. norm (f k x)) sequentially"
    by (rule uniform_limit_suminf) fact
  have cont': "\<forall>\<^sub>F n in sequentially. continuous_on A (\<lambda>x. \<Sum>k<n. norm (f k x))"
    using cont by (auto intro!: continuous_intros always_eventually cont)
  have "continuous_on A (\<lambda>x. \<Sum>k. norm (f k x))"
    by (rule uniform_limit_theorem[OF cont' lim]) auto
  hence "compact ((\<lambda>x. \<Sum>k. norm (f k x)) ` A)"
    by (intro compact_continuous_image A)
  hence "bounded ((\<lambda>x. \<Sum>k. norm (f k x)) ` A)"
    by (rule compact_imp_bounded)
  then obtain C where C: "norm (\<Sum>k. norm (f k x)) \<le> C" if "x \<in> A" for x
    unfolding bounded_iff by blast
  show ?thesis
  proof (rule uniformly_convergent_prod_Cauchy)
    fix x :: 'a and m :: nat
    assume x: "x \<in> A"
    have "norm (\<Prod>k<m. 1 + f k x) = (\<Prod>k<m. norm (1 + f k x))"
      by (simp add: prod_norm)
    also have "\<dots> \<le> (\<Prod>k<m. norm (1 :: 'b) + norm (f k x))"
      by (intro prod_mono) norm
    also have "\<dots> = (\<Prod>k<m. 1 + norm (f k x))"
      by simp
    also have "\<dots> \<le> exp (\<Sum>k<m. norm (f k x))"
      by (rule prod_le_exp_sum) auto
    also have "(\<Sum>k<m. norm (f k x)) \<le> (\<Sum>k. norm (f k x))"
    proof (rule sum_le_suminf)
      have "(\<lambda>n. \<Sum>k<n. norm (f k x)) \<longlonglongrightarrow> (\<Sum>k. norm (f k x))"
        by (rule tendsto_uniform_limitI[OF lim]) fact
      thus "summable (\<lambda>k. norm (f k x))"
        using sums_def sums_iff by blast
    qed auto
    also have "exp (\<Sum>k. norm (f k x)) \<le> exp (norm (\<Sum>k. norm (f k x)))"
      by simp
    also have "norm (\<Sum>k. norm (f k x)) \<le> C"
      by (rule C) fact
    finally show "norm (\<Prod>k<m. 1 + f k x) \<le> exp C"
      by - simp_all
  next
    fix \<epsilon> :: real assume \<epsilon>: "\<epsilon> > 0"
    have "uniformly_Cauchy_on A (\<lambda>N x. \<Sum>n<N. norm (f n x))"
      by (rule uniformly_convergent_Cauchy) fact
    moreover have "ln (1 + \<epsilon>) > 0"
      using \<epsilon> by simp
    ultimately obtain M where M: "\<And>m n x. x \<in> A \<Longrightarrow> M \<le> m \<Longrightarrow> M \<le> n \<Longrightarrow>
        dist (\<Sum>k<m. norm (f k x)) (\<Sum>k<n. norm (f k x)) < ln (1 + \<epsilon>)"
      using \<epsilon> unfolding uniformly_Cauchy_on_def by metis
  
    show "\<exists>M. \<forall>x\<in>A. \<forall>m\<ge>M. \<forall>n\<ge>m. dist (\<Prod>k = m..n. 1 + f k x) 1 < \<epsilon>"
    proof (rule exI, intro ballI allI impI)
      fix x m n
      assume x: "x \<in> A" and mn: "M \<le> m" "m \<le> n"
      have "dist (\<Sum>k<m. norm (f k x)) (\<Sum>k<Suc n. norm (f k x)) < ln (1 + \<epsilon>)"
        by (rule M) (use x mn in auto)
      also have "dist (\<Sum>k<m. norm (f k x)) (\<Sum>k<Suc n. norm (f k x)) =
                 \<bar>\<Sum>k\<in>{..<Suc n}-{..<m}. norm (f k x)\<bar>"
        using mn by (subst sum_diff) (auto simp: dist_norm)
      also have "{..<Suc n}-{..<m} = {m..n}"
        using mn by auto
      also have "\<bar>\<Sum>k=m..n. norm (f k x)\<bar> = (\<Sum>k=m..n. norm (f k x))"
        by (intro abs_of_nonneg sum_nonneg) auto
      finally have *: "(\<Sum>k=m..n. norm (f k x)) < ln (1 + \<epsilon>)" .
  
      have "dist (\<Prod>k=m..n. 1 + f k x) 1 = norm ((\<Prod>k=m..n. 1 + f k x) - 1)"
        by (simp add: dist_norm)
      also have "norm ((\<Prod>k=m..n. 1 + f k x) - 1) \<le> (\<Prod>n=m..n. 1 + norm (f n x)) - 1"
        by (rule norm_prod_minus1_le_prod_minus1)
      also have "(\<Prod>n=m..n. 1 + norm (f n x)) \<le> exp (\<Sum>k=m..n. norm (f k x))"
        by (rule prod_le_exp_sum) auto
      also note *
      finally show "dist (\<Prod>k = m..n. 1 + f k x) 1 < \<epsilon>"
        using \<epsilon> by - simp_all
    qed
  qed
qed

lemma uniformly_convergent_on_prod':
  fixes f :: "nat \<Rightarrow> 'a :: topological_space \<Rightarrow> 'b :: {real_normed_div_algebra, comm_ring_1, banach}"
  assumes cont: "\<And>n. continuous_on A (f n)"
  assumes A: "compact A"
  assumes conv_sum: "uniformly_convergent_on A (\<lambda>N x. \<Sum>n<N. norm (f n x - 1))"
  shows "uniformly_convergent_on A (\<lambda>N x. \<Prod>n<N. f n x)"
proof -
  have "uniformly_convergent_on A (\<lambda>N x. \<Prod>n<N. 1 + (f n x - 1))"
    by (rule uniformly_convergent_on_prod) (use assms in \<open>auto intro!: continuous_intros\<close>)
  thus ?thesis
    by simp
qed

end