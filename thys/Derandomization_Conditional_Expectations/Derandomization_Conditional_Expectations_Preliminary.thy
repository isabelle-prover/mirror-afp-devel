section \<open>Some Preliminary Results\<close>

theory Derandomization_Conditional_Expectations_Preliminary
  imports
    "HOL-Combinatorics.Multiset_Permutations"
    Distributed_Distinct_Elements.Pseudorandom_Combinators
    Undirected_Graph_Theory.Undirected_Graphs_Root
begin

hide_const (open) Congruence.partition
hide_fact (open) SN_Orders.of_nat_mono

subsection \<open>On Probability Theory\<close> 

lemma map_pmf_of_set_bij_betw_2:
  assumes "bij_betw (\<lambda>x. (f x, g x)) A (B\<times>C)" "A \<noteq> {}" "finite A"
  shows "map_pmf f (pmf_of_set A) = pmf_of_set B" (is "?L = ?R")
proof -
  have "B \<times> C \<noteq> {}" using assms(1,2) unfolding bij_betw_def by auto 
  hence 0: "B \<noteq> {}" "C \<noteq> {}" by auto 
  have "finite (B \<times> C)"
    unfolding bij_betw_imp_surj_on[OF assms(1), symmetric] by (intro finite_imageI assms(3))
  hence 1: "finite B" "finite C"
    using 0 finite_cartesian_productD1 finite_cartesian_productD2 by auto

  have "?L = map_pmf fst (map_pmf (\<lambda>x. (f x, g x)) (pmf_of_set A))"
    unfolding map_pmf_comp by simp
  also have "... = map_pmf fst (pmf_of_set (B \<times> C))"
    by (intro arg_cong2[where f="map_pmf"] map_pmf_of_set_bij_betw assms refl)
  also have "... = pmf_of_set B"
    using 0 1 by (subst pmf_of_set_prod_eq) (auto simp add:map_fst_pair_pmf)
  finally show ?thesis by simp
qed

lemma integral_bind_pmf:
  fixes f :: "_ \<Rightarrow> real"
  assumes "\<And>x. x \<in> set_pmf (bind_pmf p q) \<Longrightarrow> \<bar>f x\<bar> \<le> M"
  shows "(\<integral>x. f x \<partial>bind_pmf p q) = (\<integral>x. \<integral>y. f y \<partial>q x \<partial>p)" (is "?L = ?R")
proof -
  define clamp where "clamp x = (if \<bar>x\<bar> > M then 0 else x) " for x

  obtain x where "x \<in> set_pmf (bind_pmf p q)" using set_pmf_not_empty by fast
  hence M_ge_0: "M \<ge> 0" using assms by fastforce

  have a:"\<And>x y. x \<in> set_pmf p \<Longrightarrow> y \<in> set_pmf (q x) \<Longrightarrow> \<not>\<bar>f y\<bar> > M"
    using assms by fastforce
  hence "(\<integral>x. f x \<partial>bind_pmf p q) = (\<integral>x. clamp (f x) \<partial>bind_pmf p q)"
    unfolding clamp_def by (intro integral_cong_AE AE_pmfI) auto
  also have "... =  (\<integral>x. \<integral>y. clamp (f y) \<partial>q x \<partial>p)" unfolding measure_pmf_bind 
    by (subst integral_bind[where K="count_space UNIV" and B'="1" and B="M"])
      (simp_all add:measure_subprob clamp_def M_ge_0)
  also have "... = ?R" unfolding clamp_def using a by (intro integral_cong_AE AE_pmfI) simp_all
  finally show ?thesis by simp
qed

lemma pmf_of_set_un:
  fixes A B  :: "'x set"
  assumes "A \<union> B \<noteq> {}" "A \<inter> B = {}" "finite (A \<union> B)"
  defines "p \<equiv> real (card A) / real (card A + card B)"
  shows "pmf_of_set (A \<union> B) = do {c \<leftarrow> bernoulli_pmf p; pmf_of_set (if c then A else B)}"
    (is "?L = ?R")
proof (rule pmf_eqI)
  fix x :: 'x
  have p_range: "0 \<le> p" "p \<le> 1" unfolding p_def by (auto simp: divide_le_eq)
  have "card A + card B > 0" using assms(1,2,3) by auto
  hence a: "1-p = real (card B) / real (card A + card B)"
    unfolding p_def by (auto simp:divide_simps) 
  have b:" of_bool (x \<in> T) = pmf (pmf_of_set T) x * real (card T)" if "finite T" for T
    using that by (cases "T \<noteq> {}") auto

  have "pmf ?L x = indicator (A \<union> B) x / card (A \<union> B)" using assms by simp
  also have "... = (of_bool (x\<in>A)  + of_bool (x\<in>B)) /(card A+card B)" using assms(1-3)
    by (intro arg_cong2[where f="(/)"] arg_cong[where f="real"] card_Un_disjoint) auto
  also have "... = (pmf (pmf_of_set A) x * card A + pmf (pmf_of_set B) x * card B) /(card A+card B) "
    using assms(3) by (intro arg_cong2[where f="(/)"]  arg_cong2[where f="(+)"] refl b) auto
  also have "... = pmf (pmf_of_set A) x * p + pmf (pmf_of_set B) x * (1 - p)"
    unfolding a unfolding p_def by (simp add:divide_simps)
  also have "... = pmf ?R x" using p_range by (simp add:pmf_bind)
  finally show "pmf ?L x = pmf ?R x" by simp
qed

text \<open>If the expectation of a discrete random variable is larger or equal to @{term "c"}, there 
will be at least one point at which the random variable is larger or equal to @{term "c"}.\<close>

lemma exists_point_above_expectation:
  assumes "integrable (measure_pmf M) f"
  assumes "measure_pmf.expectation M f \<ge> (c::real)"
  shows "\<exists>x \<in> set_pmf M. f x \<ge> c"
proof (rule ccontr)
  assume "\<not> (\<exists>x\<in>set_pmf M. c \<le> f x)"
  hence "AE x in M. f x < c" by (intro AE_pmfI) auto 
  thus "False" using measure_pmf.expectation_less[OF assms(1)] assms(2) not_less by auto
qed

subsection \<open>On Convexity\<close>

text \<open>A translation rule for convexity.\<close>
lemma convex_on_shift:
  fixes f :: "('b :: real_vector) \<Rightarrow> real"
  assumes "convex_on S f" "convex S"
  shows "convex_on {x. x + a \<in> S} (\<lambda>x. f (x+a))"
proof -
  have "f (((1 - t) *\<^sub>R x + t *\<^sub>R y) + a) \<le>  (1-t) * f (x+a) + t * f (y+a)" (is "?L \<le> ?R")
    if "0 < t" "t < 1" "x \<in> {x. x + a \<in> S}" "y \<in> {x. x + a \<in> S}" for x y t
  proof -
    have "?L = f ((1-t) *\<^sub>R (x+a) + t *\<^sub>R (y+a))" by (simp add:algebra_simps)
    also have "... \<le> (1-t) * f (x+a) + t * f (y+a)" using that by (intro convex_onD[OF assms(1)]) auto
    finally show ?thesis by auto
  qed
  moreover have "{x. x + a \<in> S} = (\<lambda>x. x - a) ` S" by (auto simp:image_iff algebra_simps)
  hence "convex {x. x + a \<in> S}" using assms(2) by auto
  ultimately show ?thesis using assms by (intro convex_onI) auto
qed

subsection \<open>On @{term "subseq"} and  @{term "strict_subseq"}\<close>

lemma strict_subseq_imp_shorter: "strict_subseq x y \<Longrightarrow> length x < length y"
  unfolding strict_subseq_def by (meson linorder_neqE_nat not_subseq_length subseq_same_length)

lemma subseq_distinct: "subseq x y \<Longrightarrow> distinct y \<Longrightarrow> distinct x"
  by (metis distinct_nthsI subseq_conv_nths)

lemma strict_subseq_imp_distinct: "strict_subseq x y \<Longrightarrow> distinct y \<Longrightarrow> distinct x"
  using subseq_distinct unfolding strict_subseq_def by auto

lemma subseq_set: "subseq xs ys \<Longrightarrow> set xs \<subseteq> set ys"
  unfolding strict_subseq_def by (metis set_nths_subset subseq_conv_nths)

lemma strict_subseq_set: "strict_subseq x y \<Longrightarrow> set x \<subseteq> set y"
  unfolding strict_subseq_def by (intro subseq_set) simp

lemma subseq_induct:
  assumes "\<And>ys. (\<And>zs. strict_subseq zs ys \<Longrightarrow> P zs) \<Longrightarrow> P ys"
  shows "P xs"
proof (induction "length xs" arbitrary:xs rule: nat_less_induct)
  case 1
  have "P ys" if "strict_subseq ys xs" for ys 
  proof -
    have "length ys < length xs" using strict_subseq_imp_shorter that by auto
    thus "P ys" using 1 by simp
  qed
  thus ?case using assms by blast
qed

lemma subseq_induct':
  assumes "P []"
  assumes "\<And>y ys. (\<And>zs. strict_subseq zs (y#ys) \<Longrightarrow> P zs) \<Longrightarrow> P (y#ys)"
  shows "P xs"
proof (induction xs rule: subseq_induct)
  case (1 ys)
  show ?case 
  proof (cases ys)
    case Nil thus ?thesis using assms(1) by simp
  next
    case (Cons ysh yst)
    show ?thesis using 1 unfolding Cons by (rule assms(2)) auto
  qed
qed

lemma strict_subseq_remove1:
  assumes "w \<in> set x"
  shows "strict_subseq (remove1 w x) x"
proof -
  have "subseq (remove1 w x) x" by (induction x) auto
  moreover have "remove1 w x \<noteq> x" using assms by (simp add: remove1_split)
  ultimately show ?thesis unfolding strict_subseq_def by auto
qed

subsection \<open>On Random Permutations\<close>

lemma filter_permutations_of_set_pmf:
  assumes "finite S"
  shows "map_pmf (filter P) (pmf_of_set (permutations_of_set S)) = 
  pmf_of_set (permutations_of_set {x \<in> S. P x})" (is "?L = ?R")
proof -
  have "?L = map_pmf fst (map_pmf (partition P) (pmf_of_set (permutations_of_set S)))"
    by (simp add:map_pmf_comp)
  also have "... = map_pmf fst (pair_pmf ?R (pmf_of_set (permutations_of_set {x \<in> S. \<not> P x})))"
    by (simp add:partition_random_permutations[OF assms(1)])
  also have "... = ?R" by (simp add:map_fst_pair_pmf)
  finally show ?thesis by simp
qed

lemma permutations_of_set_prefix:
  assumes "finite S" "v \<in> S"
  shows "measure (pmf_of_set (permutations_of_set S)) {xs. prefix [v] xs} = 1/real (card S)" 
    (is "?L = ?R")
proof -
  have S_ne: "S \<noteq> {}" using assms(2) by auto
  have "?L = (\<integral>vs. indicator {vs. prefix [v] vs} vs \<partial>pmf_of_set (permutations_of_set S))" by simp
  also have "... = (\<integral>h. of_bool (v = h) \<partial>pmf_of_set S)"
    unfolding random_permutation_of_set[OF assms(1) S_ne] 
    apply (subst integral_bind_pmf[where M="1"], simp)
    apply (subst integral_bind_pmf[where M="1"], simp)
    by (simp add:indicator_def)
  also have  "... = (\<integral>h. indicator {v} h \<partial>pmf_of_set S)" by (simp add:indicator_def eq_commute)
  also have "... = measure (pmf_of_set S) {v}" by simp
  also have "... = 1/card S" using assms(1,2) S_ne by (subst measure_pmf_of_set)  auto
  finally show ?thesis by simp
qed

text \<open>@{term "cond_perm"} returns all permutations of a set starting with specific prefix.\<close>

definition cond_perm where "cond_perm V p = (@) p ` permutations_of_set (V - set p)"

context fin_sgraph
begin

lemma perm_non_empty_finite:
  "permutations_of_set V \<noteq> {}" "finite (permutations_of_set V)"
proof -
  have "0 < card (permutations_of_set V)" using finV by (subst card_permutations_of_set) auto
  thus "permutations_of_set V \<noteq> {}" "finite (permutations_of_set V)" using card_gt_0_iff by blast+
qed

lemma cond_perm_non_empty_finite:
  "cond_perm V p \<noteq> {}" "finite (cond_perm V p)"
proof -
  have "0 < card (permutations_of_set (V - set p))"
    using finV by (subst card_permutations_of_set) auto
  also have "... = card (cond_perm V p)"
    unfolding cond_perm_def by (intro card_image[symmetric] inj_onI) auto
  finally have "card (cond_perm V p) > 0" by simp
  thus "cond_perm V p \<noteq> {}" "finite (cond_perm V p)" using card_ge_0_finite by auto
qed

lemma cond_perm_alt: 
  assumes "distinct p" "set p \<subseteq> V"
  shows "cond_perm V p = {xs \<in> permutations_of_set V. prefix p xs}"
proof -
  have "p@xs \<in> permutations_of_set V" if "xs \<in> permutations_of_set (V-set p)" for xs
    using permutations_of_setD[OF that] assms by (intro permutations_of_setI) auto
  moreover have "xs \<in> cond_perm V p" if "xs \<in> permutations_of_set V" and a:"prefix p xs" for xs
  proof -
    obtain ys where xs_def:"xs = p@ys" using a prefixE by auto
    have 0:"distinct (p@ys)" "set (p@ys) = V"
      using permutations_of_setD[OF that(1)] unfolding xs_def by auto
    hence "set ys = V - set p" by auto
    moreover have "distinct ys" using 0 by auto
    ultimately have "ys \<in> permutations_of_set (V - set p)" by (intro permutations_of_setI)
    thus ?thesis unfolding cond_perm_def xs_def by simp
  qed
  ultimately show ?thesis by (auto simp:cond_perm_def)
qed

lemma cond_permD:
  assumes "distinct p" "set p \<subseteq> V" "xs \<in> cond_perm V p"
  shows "distinct xs" "set xs = V"
  using assms(3) permutations_of_setD unfolding cond_perm_alt[OF assms(1,2)] by auto

subsection \<open>On Finite Simple Graphs\<close>

lemma degree_sum: "(\<Sum>v \<in> V. degree v) = 2 * card E" (is "?L = ?R")
proof -
  have "?L = (\<Sum>v \<in> V. (\<Sum>e \<in> E. of_bool(v \<in> e)))"
    using fin_edges finV unfolding alt_degree_def incident_edges_def vincident_def
    by (simp add:of_bool_def sum.If_cases Int_def)
  also have "... = (\<Sum>e \<in> E. card (e \<inter> V))"
    using fin_edges finV by (subst sum.swap) (simp add:of_bool_def sum.If_cases Int_commute)
  also have "... = (\<Sum>e \<in> E. card e)"
    using wellformed by (intro sum.cong arg_cong[where f="card"] Int_absorb2) auto
  also have "... = 2*card E" using two_edges by simp
  finally show ?thesis by simp
qed

text \<open>The environment of a set of nodes is the union of it with its neighborhood.\<close>

definition environment where "environment S = S \<union> {v. \<exists>s \<in> S. vert_adj v s}" 

lemma finite_environment:
  assumes "finite S"
  shows "finite (environment S)"
proof -
  have "environment S \<subseteq> S \<union> V" unfolding environment_def using vert_adj_imp_inV by auto
  thus ?thesis using assms finite_Un finV finite_subset by auto
qed

lemma environment_mono: "S \<subseteq> T \<Longrightarrow> environment S \<subseteq> environment T"
  unfolding environment_def by auto

lemma environment_sym: "x \<in> environment {y} \<longleftrightarrow> y \<in> environment {x}"
  unfolding environment_def vert_adj_def by (auto simp:insert_commute)

lemma environment_self: "S \<subseteq> environment S" unfolding environment_def by auto

lemma environment_sym_2: "A \<inter> environment B = {} \<longleftrightarrow> B \<inter> environment A = {}"
proof -
  have "False" if "B \<inter> environment A = {}" "x \<in> A \<inter> environment B" for x A B
  proof (cases "x \<in> B")
    case True thus ?thesis using that environment_self by auto
  next
    case False
    hence "x \<in> {x. \<exists>v \<in> B. vert_adj x v}" using that(2) unfolding environment_def by auto
    then obtain v where v_def: "v \<in> B" "x \<in> environment {v}" unfolding environment_def by auto
    have "v \<in> environment A" using environment_mono that(2) environment_sym v_def(2) by blast
    then show ?thesis using v_def(1) that(1) by auto
  qed
  thus ?thesis by auto
qed

lemma environment_range: "S \<subseteq> V \<Longrightarrow> environment S \<subseteq> V"
  unfolding environment_def using vert_adj_imp_inV by auto

lemma environment_union: "environment (S \<union> T) = environment S \<union> environment T"
  unfolding environment_def by auto

lemma card_environment: "card (environment {v}) = 1 + degree v" (is "?L = ?R")
proof -
  have "?L = card (insert v {x. {x, v} \<in> E})" unfolding environment_def vert_adj_def by simp
  also have "... = Suc (card {x. {x, v} \<in> E})"
    by (intro card_insert_disjoint finite_subset[OF _ finV])
      (auto simp:singleton_not_edge wellformed_alt_fst)
  also have "... = Suc (card (neighborhood v))" unfolding neighborhood_def vert_adj_def
    by (intro arg_cong[where f="\<lambda>x. Suc (card x)"])
      (auto simp:wellformed_alt_fst insert_commute) 
  also have "... = Suc (degree v)"
    unfolding alt_degree_def card_incident_sedges_neighborhood by simp
  finally show ?thesis by simp
qed

end

end
