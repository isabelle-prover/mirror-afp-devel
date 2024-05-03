section \<open>Method of Pessimistic Estimators: Independent Sets\<close> 

text \<open>A generalization of the the method of conditional expectations is the method of pessimistic
estimators. Where the conditional expectations are conservatively approximated. The following 
example is such a case.

Starting with a probabilistic proof of Caro-Wei's
theorem~\cite[Section: The Probabilistic Lens: Tur\'{a}n's theorem]{alon2000}, this section
constructs a deterministic algorithm that finds such a set.\<close>

theory Derandomization_Conditional_Expectations_Independent_Set
  imports Derandomization_Conditional_Expectations_Cut
begin

hide_fact (open) Henstock_Kurzweil_Integration.integral_sum

text \<open>The following represents a greedy algorithm that walks through the vertices in a given
order and adds it to a result set, if and only if it preserves independence of the set.\<close> 

fun indep_set :: "'a list \<Rightarrow> 'a set set \<Rightarrow> 'a list"
  where 
    "indep_set [] E = []" |
    "indep_set (v#vt) E = v#indep_set (filter (\<lambda>w. {v,w} \<notin> E) vt) E"

context fin_sgraph 
begin

lemma indep_set_range: "subseq (indep_set p E) p"
proof (induction p rule:subseq_induct')
  case 1 thus ?case by simp
next
  case (2 ph pt)
  have "subseq (filter (\<lambda>w. {ph, w} \<notin> E) pt) pt" by simp
  also have "strict_subseq ... (ph#pt)" unfolding strict_subseq_def by auto
  finally have "strict_subseq (filter (\<lambda>w. {ph, w} \<notin> E) pt) (ph # pt)" by simp
  hence "subseq (indep_set (ph # pt) E) (ph#filter (\<lambda>w. {ph, w} \<notin> E) pt)"
    unfolding indep_set.simps by (intro 2 subseq_Cons2)
  also have "subseq ... (ph#pt)" by simp
  finally show ?case by simp
qed

lemma is_independent_set_insert:
  assumes "is_independent_set A" "x \<in> V - environment A"
  shows "is_independent_set (insert x A)"
  using assms unfolding is_independent_alt vert_adj_def environment_def
  by (simp add:insert_commute singleton_not_edge) 

text \<open>Correctness properties of @{term "indep_set"}:\<close>

theorem indep_set_correct:
  assumes "distinct p" "set p \<subseteq> V"
  shows "distinct (indep_set p E)" "set (indep_set p E) \<subseteq> V" "is_independent_set (set (indep_set p E))"
proof -
  show "distinct (indep_set p E)" using indep_set_range assms(1) subseq_distinct by auto
  show "set (indep_set p E) \<subseteq> V" using indep_set_range assms(2) 
    by (metis (full_types) list_emb_set subset_code(1))

  show "is_independent_set (set (indep_set p E))"
    using assms(1,2)
  proof (induction p rule:subseq_induct')
    case 1
    then show ?case by (auto simp add:is_independent_set_def all_edges_def)
  next
    case (2 y ys)
    have "subseq (filter (\<lambda>w. {y, w} \<notin> E) ys) ys" by simp
    also have "strict_subseq ... (y#ys)" by (simp add: list_emb_Cons strict_subseq_def)
    finally have "strict_subseq (filter (\<lambda>w. {y, w} \<notin> E) ys) (y # ys)" by simp
    moreover have "False" if "y\<in>environment (set (indep_set (filter (\<lambda>w. {y, w} \<notin> E) ys) E))" 
    proof -
      have "y \<in> environment (set (filter (\<lambda>w. {y,w} \<notin> E) ys))"
        using that environment_mono subseq_set[OF indep_set_range] by blast
      hence "\<exists>z \<in> (set (filter (\<lambda>w. {y,w} \<notin> E) ys)). {z,y} \<in> E "
        using 2(2) unfolding environment_def vert_adj_def by simp
      then show ?thesis by (simp add:insert_commute)
    qed
    ultimately have "is_independent_set (insert y (set (indep_set (filter (\<lambda>w. {y, w} \<notin> E) ys) E)))" 
      using 2(2,3) by (intro is_independent_set_insert 2) auto
    thus ?case by simp
  qed
qed

text \<open>While for an individual call of @{term "indep_set"} it is not possible to derive a non-trivial
bound on the size of the resulting independent set, it is possible to estimate its performance
on average, i.e., with respect to a random choice on the order it visits the vertices.
This will be derived in the following:\<close>

definition is_first where 
  "is_first v p = prefix [v] (filter (\<lambda>y. y \<in> environment {v}) p)"

lemma is_first_subseq:
  assumes "is_first v p" "distinct p" "subseq q p" "v \<in> set q"
  shows "is_first v q"
proof -
  let ?f = "(\<lambda>y. y \<in> environment {v})"

  obtain q1 q2 where q_def: "q = q1@v#q2" using assms(4) by (meson split_list)
  obtain p1 p2 where p_def: "p = p1@p2" "subseq q1 p1" "subseq (v#q2) p2"
    using assms(3) list_emb_appendD unfolding q_def by blast

  have "v \<in> set p2" using p_def(3) list_emb_set by force
  hence 0:"v \<notin> set p1" using assms(2) unfolding p_def(1) by auto
  have "filter ?f p1 = []"
  proof (cases "filter ?f p1")
    case Nil thus ?thesis by simp
  next
    case (Cons p1h p2h)
    hence "p1h = v" using assms(1) unfolding is_first_def p_def(1) by simp
    hence "False" using 0 Cons by (metis filter_eq_ConsD in_set_conv_decomp)
    then show ?thesis by simp
  qed
  hence "filter ?f q1 = []" using p_def(2) by (metis (full_types) filter_empty_conv list_emb_set)
  moreover have "v \<in> environment {v}" unfolding environment_def by simp
  ultimately show ?thesis unfolding q_def is_first_def by simp
qed

lemma is_first_imp_in_set:
  assumes "is_first v p"
  shows "v \<in> set p"
proof -
  have "v \<in> set (filter (\<lambda>y. y \<in> environment {v}) p)"
    using assms unfolding is_first_def by (meson prefix_imp_subseq subseq_singleton_left)
  thus ?thesis by simp
qed

text \<open>Let us observe that a node, which comes first in the ordering of the vertices with
respect to its neighbors, will definitely be in the independent set. (This is only a sufficient
condition, but not a necessary condition.)\<close>

lemma set_indep_set:
  assumes "distinct p" "set p \<subseteq> V" "is_first v p"
  shows "v \<in> set (indep_set p E)"
  using assms
proof (induction p rule:subseq_induct)
  case (1 ys)
  hence i:"v \<in> set (indep_set zs E)" if "is_first v zs" "strict_subseq zs ys" for zs
    using strict_subseq_imp_distinct strict_subseq_set that by (intro 1(1)) blast+

  define ysh yst where ysht_def: "ysh = hd ys" "yst = tl ys"
  have split_ys: "ys = ysh#yst" if "ys \<noteq> []" using that unfolding ysht_def by auto

  consider (a) "ys = []" | (b) "ys \<noteq> []" "hd ys = v" | (c) "ys \<noteq> []" "hd ys \<noteq> v" by auto
  then show ?case
  proof (cases)
    case a then show ?thesis using 1(4) by (simp add:is_first_def)
  next
    case b then show ?thesis unfolding split_ys[OF b(1)] by simp 
  next
    case c
    have 0:"subseq (filter (\<lambda>w. {ysh, w} \<notin> E) yst) ys" unfolding split_ys[OF c(1)] by auto
    have "v \<in> set ys" using 1(4) is_first_imp_in_set by auto
    hence "v \<in> set yst" using c unfolding split_ys[OF c(1)] by simp
    moreover have "ysh \<noteq> v" using c(2) split_ys[OF c(1)] by simp    
    hence "ysh \<notin> environment {v}" using 1(4) unfolding is_first_def split_ys[OF c(1)] by auto
    hence "{ysh,v} \<notin> E" unfolding environment_def vert_adj_def by auto
    ultimately have "v \<in> set (filter (\<lambda>w. {ysh, w} \<notin> E) yst)" by simp
    hence "is_first v (filter (\<lambda>w. {ysh, w} \<notin> E) yst)" by (intro is_first_subseq[OF 1(4)] 0 1(2))
    moreover have "length yst < length ys" using split_ys[OF c(1)] by auto
    hence "length (filter (\<lambda>w. {ysh, w} \<notin> E) yst) < length ys"
      using length_filter_le dual_order.strict_trans2 by blast
    hence "filter (\<lambda>w. {ysh, w} \<notin> E) yst \<noteq> ys" by auto
    hence "strict_subseq (filter (\<lambda>w. {ysh, w} \<notin> E) yst) ys"
      using 0 unfolding strict_subseq_def by auto
    ultimately have "v \<in> set (indep_set (filter (\<lambda>w. {ysh, w} \<notin> E) yst) E)" by (intro i) 
    then show ?thesis unfolding split_ys[OF c(1)] by simp
  qed
qed

text \<open>Using the above we can establish the following lower-bound on the expected size of an
independent set obtained by @{term "indep_set"}:\<close>

theorem exp_indep_set:
  defines "\<Omega> \<equiv> pmf_of_set (permutations_of_set V)"
  shows "(\<integral>vs. real (length (indep_set vs E)) \<partial>\<Omega>) \<ge> (\<Sum>v \<in> V. 1 / (degree v + 1::real))"
    (is "?L \<ge> ?R")
proof -
  let ?perm = "(\<lambda>x. pmf_of_set (permutations_of_set x))"
  have a:"finite (set_pmf \<Omega>)" unfolding \<Omega>_def using perm_non_empty_finite by simp
  have b:"distinct y" "set y \<subseteq> V" if "y \<in> set_pmf \<Omega>" for y 
    using that perm_non_empty_finite permutations_of_setD unfolding \<Omega>_def by auto

  have "?R = (\<Sum>v\<in>V. 1 / real (card (environment {v})))" unfolding card_environment by simp
  also have "... = (\<Sum>v\<in>V. measure (?perm (environment {v})) {vs. prefix[v] vs})"
    using finite_environment environment_self by (intro sum.cong permutations_of_set_prefix[symmetric]) auto 
  also have "... = (\<Sum> v \<in> V. (\<integral>vs. indicator {vs. prefix [v] vs} vs \<partial>?perm (environment {v}\<inter>V)))"
    using Int_absorb2[OF environment_range] by (intro sum.cong refl) simp
  also have "...=(\<Sum>v\<in>V.(\<integral>vs. of_bool(prefix[v]vs) \<partial>map_pmf (filter (\<lambda>x. x \<in> environment {v})) \<Omega>))"
    unfolding \<Omega>_def filter_permutations_of_set_pmf[OF finV]
    by (intro sum.cong arg_cong2[where f="measure_pmf.expectation"])
      (simp_all add:Int_def conj_commute of_bool_def indicator_def)
  also have "... = (\<Sum>v \<in> V. (\<integral>vs. of_bool(is_first v vs) \<partial>\<Omega>))"
    unfolding is_first_def by (intro sum.cong) simp_all
  also have "... = (\<integral>vs. (\<Sum>v \<in> V. of_bool(is_first v vs)) \<partial>\<Omega>)"
    by (intro integral_sum[symmetric] integrable_measure_pmf_finite[OF a])
  also have "... \<le> (\<integral>vs. real (card (set (indep_set vs E))) \<partial>\<Omega>)"
    using finV b by (intro integral_mono_AE AE_pmfI integrable_measure_pmf_finite[OF a])
     (auto intro!:card_mono set_indep_set)
 also have "... \<le> ?L"
   by (intro integral_mono_AE AE_pmfI integrable_measure_pmf_finite[OF a] of_nat_mono card_length)
  finally show ?thesis by simp
qed

text \<open>The function @{term "\<lambda>(x::real). 1 / (x+1)"} is convex.\<close>
lemma inverse_x_plus_1_convex: "convex_on {-1<..} (\<lambda>x. 1 / (x+1::real))"
proof -
  have "convex_on {x. x + 1 \<in> {0<..}} (\<lambda>x. inverse (x+1::real))"
    by (intro convex_on_shift[OF convex_on_inverse]) auto
  moreover have "{x. (0::real) < x + 1} = {-1<..}" by (auto simp:algebra_simps)
  ultimately show ?thesis by (simp add:inverse_eq_divide)
qed

lemma caro_wei_aux: "card V / (2*card E / card V + 1) \<le> (\<Sum>v \<in> V. 1/ (degree v+1))"
proof -
  have "card V / (2*card E / card V + 1) = card V* (1 / (((2*card E)::real) / card V + 1))" by simp
  also have "... = card V* (1 / ((\<Sum>v \<in> V. (1 / real (card V)) *\<^sub>R degree v) + 1))"
    unfolding degree_sum[symmetric] by (simp add:sum_divide_distrib)
  also have "... \<le> card V * (\<Sum>v \<in> V. (1 / card V) * (1/ (degree v+(1::real))))"
  proof (cases "V = {}")
    case True thus ?thesis by simp
  next
    case False thus ?thesis 
      using finV by (intro mult_left_mono convex_on_sum[OF _ _ inverse_x_plus_1_convex] finV) auto
  qed
  also have "... = (\<Sum>v \<in> V. 1/ (degree v+1))" 
    using finV unfolding sum_distrib_left by (intro sum.cong refl) auto
  finally show ?thesis by simp
qed

text \<open>A corollary of the @{thm [source] exp_indep_set} is Caro-Wei's theorem:\<close>

corollary caro_wei:
  "\<exists>S \<subseteq> V. is_independent_set S \<and> card S \<ge> card V / (2*card E / card V + 1)"
proof -
  let ?\<Omega> = "pmf_of_set (permutations_of_set V)"
  let ?w = "real (card V) / (real (2*card E) / card V + 1)"

  have a:"finite (set_pmf ?\<Omega>)" using perm_non_empty_finite by simp

  have "(\<integral>vs. real (length (indep_set vs E)) \<partial>?\<Omega>) \<ge> ?w"
    using exp_indep_set caro_wei_aux by simp
  then obtain vs where vs_def: "vs \<in> set_pmf ?\<Omega>" "real (length (indep_set vs E)) \<ge> ?w" 
    using exists_point_above_expectation integrable_measure_pmf_finite[OF a] by blast
  define S where "S = set (indep_set vs E)"

  have vs_range: "distinct vs" "set vs \<subseteq> V"
    using vs_def(1) perm_non_empty_finite permutations_of_setD by auto

  have b:"S \<subseteq> V" "is_independent_set S" and c: "distinct (indep_set vs E)"
    unfolding S_def using indep_set_correct[OF vs_range] by auto

  have "real (card S) = length (indep_set vs E)" using c distinct_card unfolding S_def by auto
  also have "... \<ge> ?w" using vs_def(2) by auto
  finally have "real (card S) \<ge> ?w" by simp
  thus ?thesis using b c by auto
qed

end

text \<open>After establishing the above result, we may ask the question, whether there is a practical
algorithm to find such a set. This is where the method of conditional expectations comes to stage.

We are tasked with finding an ordering of the vertices, for which the above algorithm would
return an above-average independent set. This is possible, because we can compute the conditional
expectation of 

@{term "(\<integral>vs. (\<Sum>v \<in> V. of_bool(is_first v vs)::real) \<partial>pmf_of_set (permutations_of_set V))"}

when we restrict to permutations starting with a given prefix. The latter term is a pessimistic
estimator for the size of the independent set for the given ordering (as discussed above.)

It then is possible to obtain a deterministic algorithm that obtains an ordering by incrementally
choosing vertices, that maximize the conditional expectation.

The resulting algorithm looks as follows:\<close>

function derandomized_indep_set :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a set set \<Rightarrow> 'a list"
  where
    "derandomized_indep_set [] p E = indep_set p E" |
    "derandomized_indep_set (vh#vt) p E = (
      let node_deg = (\<lambda>v. real (card {e \<in> E. v \<in> e}));
          is_indep = (\<lambda>v. list_all (\<lambda>w. {v,w} \<notin> E) p);
          env = (\<lambda>v. filter is_indep (v#filter (\<lambda>w. {v,w} \<in> E) (vh#vt)));
          cost = (\<lambda>v.  (\<Sum>w \<leftarrow> env v. 1 /(node_deg w+1) ) - of_bool(is_indep v));
          w = arg_min_list cost (vh#vt)
      in derandomized_indep_set (remove1 w (vh#vt)) (p@[w]) E)"
  by pat_completeness auto

termination 
proof (relation "Wellfounded.measure (\<lambda>x. length(fst x))")
  fix cost :: "'a \<Rightarrow> real" and w vh :: 'a and p vt :: "'a list" and E :: "'a set set" 
  define v where "v = vh#vt"
  assume "w = arg_min_list cost (vh # vt)" 
  hence "w \<in> set v" unfolding v_def using arg_min_list_in by blast
  thus "((remove1 w v, p @ [w], E), v, p, E) \<in> Wellfounded.measure (\<lambda>x. length (fst x))"
    unfolding in_measure by (simp add:length_remove1) (simp add: v_def)
qed auto

context fin_sgraph
begin

lemma is_first_append_1:
  assumes "v \<notin> environment (set p)"
  shows "is_first v (p@q) = is_first v q"
proof -
  have "environment {v} \<inter> set p = {}" using environment_sym_2 assms by auto
  hence "filter (\<lambda>y. y \<in> environment {v}) p = []" unfolding filter_empty_conv by auto
  thus ?thesis unfolding is_first_def by simp
qed

lemma is_first_append_2:
  assumes "v \<in> environment (set p)"
  shows "is_first v (p@q) = is_first v p"
proof -
  obtain u where "u \<in> set p" "v \<in> environment {u}"
    using assms unfolding environment_def by auto
  hence "filter (\<lambda>y. y \<in> environment {v}) p \<noteq> []"
    using environment_sym unfolding filter_empty_conv by meson 
  thus ?thesis unfolding is_first_def by (cases "filter (\<lambda>y. y \<in> environment {v}) p") auto
qed

text \<open>The conditional expectation of the pessimistic estimator for a given prefix of the ordering
of the vertices.\<close>

definition p_estimator where
  "p_estimator p = (\<integral>vs. (\<Sum>v \<in> V. of_bool(is_first v vs))  \<partial>pmf_of_set (cond_perm V p))"

lemma p_estimator_split:
  assumes "V - set p \<noteq> {}" 
  shows "p_estimator p = (\<Sum>v\<in>V-set p. p_estimator (p@[v])) / real (card (V-set p))" (is "?L = ?R")
proof -
  let ?q = "\<lambda>x. pmf_of_set (permutations_of_set (V-set p-{x}))"
  have 0:"finite (V - set p)" "V - set p \<noteq> {}" using finV assms by auto

  have "?L = (\<integral>vs. (\<Sum>v\<in>V. of_bool (is_first v (p@vs))) \<partial>pmf_of_set (permutations_of_set (V-set p)))"
    using finV unfolding p_estimator_def cond_perm_def 
    by (subst map_pmf_of_set_inj[symmetric]) (auto intro:inj_onI)
  also have "...=(\<Sum>x\<in>V-set p.(\<integral>vs.(\<Sum>v\<in>V. of_bool(is_first v(p@x#vs)))\<partial>?q x))/real(card (V-set p))"
    using 0 unfolding random_permutation_of_set[OF 0] by (subst pmf_expectation_bind_pmf_of_set)
     (simp_all add:map_pmf_def[symmetric] inverse_eq_divide sum_divide_distrib)
  also have "... = (\<Sum>x\<in>V-set p. p_estimator (p@[x])) /real(card (V-set p))"
    using finV Diff_insert unfolding p_estimator_def cond_perm_def 
    by (subst map_pmf_of_set_inj[symmetric]) (auto intro:inj_onI simp flip:Diff_insert)
  finally show ?thesis by simp
qed

text \<open>The fact that the pessimistic estimator can be computed efficiently is the reason we can 
apply this method:\<close>

lemma p_estimator:
  assumes "distinct p" "set p \<subseteq> V"
  defines "P \<equiv> {v. is_first v p}"
  defines "R \<equiv> V - environment (set p)"
  shows "p_estimator p = card P + (\<Sum>v\<in>R. 1/(degree v +1::real))"
    (is "?L = ?R")
proof -
  let ?p = "pmf_of_set (cond_perm V p)"
  let ?q = "pmf_of_set (permutations_of_set (V - set p))"
  define Q where "Q = environment (set p) - P"

  have "P \<subseteq> V" using assms(2) is_first_imp_in_set unfolding P_def by auto
  moreover have "environment (set p) \<subseteq> V" using environment_range assms(2) by auto
  ultimately have V_split: "V = P \<union> Q \<union> R" unfolding R_def Q_def by auto

  have "P \<subseteq> environment (set p)" using environment_def P_def is_first_imp_in_set by auto
  hence 0: "(P \<union> Q) \<inter> R = {}"  "P \<inter> Q = {}" unfolding R_def Q_def by auto

  have 1: "finite P" "finite R" "finite (P \<union> Q)" using V_split finV by auto

  have a: "is_first v (p@vs)" if "v \<in> P" for v vs
    using that unfolding P_def is_first_def by auto

  have b: "\<not>is_first v (p@vs)" if "v \<in> Q" for v vs
    using that unfolding Q_def P_def by (subst is_first_append_2) auto

  have c: "(\<integral>vs. of_bool (is_first v (p@vs)) \<partial>?q) = 1 / (degree v + 1::real)" (is "?L1 = ?R1")
    if v_range:"v \<in> R" for v
  proof -
    have "set p \<inter> environment {v} = {}" using that environment_sym_2 unfolding R_def by auto 
    moreover have "environment {v} \<subseteq> V"
      using v_range unfolding R_def by (intro  environment_range) auto
    ultimately have d:"{x\<in>V-set p. x\<in>environment{v}} = environment{v}" by auto

    have "?L1 = (\<integral>vs. indicator {vs. is_first v (p@vs)} vs \<partial>?q)" by (simp add:indicator_def)
    also have "... = measure ?q {vs. is_first v (p@vs)}" by simp
    also have "... = measure ?q {vs. is_first v vs}" 
      using that unfolding R_def
      by (intro arg_cong2[where f="measure"] Collect_cong is_first_append_1) auto
    also have "... = measure (map_pmf (filter (\<lambda>x. x \<in> environment {v})) ?q) {vs. prefix [v] vs}"
      unfolding is_first_def by simp
    also have "... = 
      measure (pmf_of_set (permutations_of_set {x\<in>V-set p. x\<in>environment{v}})) {vs. prefix [v] vs}"
      using finV by (subst filter_permutations_of_set_pmf) auto
    also have "... = 1 / real (card (environment {v}))" unfolding d 
      using finite_environment environment_self by (subst permutations_of_set_prefix) auto
    also have "... = ?R1" unfolding card_environment by simp 
    finally show ?thesis by simp
  qed

  have "?L = (\<integral>vs. real (\<Sum>v \<in> V. of_bool (is_first v vs)) \<partial> ?p)"
    unfolding p_estimator_def using cond_perm_non_empty_finite cond_permD[OF assms(1,2)]
    by (intro integral_cong_AE AE_pmfI arg_cong[where f="real"]) auto 
  also have "... = (\<integral>vs. (\<Sum>v \<in> V. of_bool (is_first v vs)) \<partial> ?p)" by simp
  also have "... = (\<Sum>v \<in> V. (\<integral>vs. of_bool (is_first v vs) \<partial> ?p))" 
    by (intro integral_sum finite_measure.integrable_const_bound[where B="1"] AE_pmfI) auto
  also have "... = (\<Sum>v \<in> V. (\<integral>vs. of_bool (is_first v vs) \<partial>map_pmf ((@) p) ?q))" 
    unfolding cond_perm_def by (subst map_pmf_of_set_inj) (auto intro:inj_onI finV)
  also have "... = (\<Sum>v \<in> V. (\<integral>vs. of_bool (is_first v (p@vs)) \<partial>?q))" by simp
  also have "... = real (card P) + (\<Sum>v \<in> R. (\<integral>vs. of_bool (is_first v (p@vs)) \<partial>?q))"
    unfolding V_split using 0 1 a b by (simp add: sum.union_disjoint)
  also have "... = ?R" by (simp add:c cong:sum.cong)
  finally show ?thesis by simp
qed

lemma p_estimator_step:
  assumes "distinct (p@[v])" "set (p@[v]) \<subseteq> V"
  shows "p_estimator (p@[v]) - p_estimator p = of_bool(environment {v} \<inter> set p = {})
    - (\<Sum>w\<in>environment {v}-environment(set p). 1 / (degree w+1::real))"
proof -
  let ?d = "\<lambda>v. 1/(degree v + 1::real)"
  let ?e = "\<lambda>x. environment x"
  define \<tau> :: nat where "\<tau> = of_bool(environment {v} \<inter> set p = {})"
  have real_tau: "of_bool(environment {v} \<inter> set p = {}) = real \<tau>" unfolding \<tau>_def by simp
  have v_range: "v \<in> V" using assms(2) by auto

  have 3: "finite (set (p@[v]))" by simp
  have 4: "is_first w (p @ [v]) \<longleftrightarrow> is_first w p" if "w \<noteq> v" for w 
    using that unfolding is_first_def by auto
  have 7:"v \<notin> set p" using assms(1) by simp
  hence 5:"w \<noteq> v" if "is_first w p" for w using is_first_imp_in_set[OF that] by auto

  have "environment {v} \<inter> set p = {} \<longleftrightarrow> is_first v (p@[v])" (is "?L1 \<longleftrightarrow> ?R1")
  proof 
    assume ?L1
    hence "x \<notin> environment {v}" if "x \<in> set p" for x using that by auto
    moreover have "v \<in> environment {v}" unfolding environment_def by auto 
    ultimately show ?R1 unfolding is_first_def by (simp add:filter_empty_conv) 
  next
    assume ?R1
    moreover have "v \<notin> set p" using assms(1) by auto
    hence "\<not>prefix [v] (filter (\<lambda>y. y \<in> environment {v}) p)"  
      by (meson filter_is_subset prefix_imp_subseq subseq_singleton_left subset_code(1))
    ultimately have "filter (\<lambda>y. y \<in> environment {v}) p = []"
      unfolding is_first_def filter_append by (cases "filter (\<lambda>y. y \<in> environment {v}) p") auto
    thus ?L1 unfolding filter_empty_conv by auto
  qed
  hence 6: "\<tau> = of_bool (is_first v (p@[v]))" unfolding \<tau>_def by simp

  have "card {w. is_first w(p@[v])}=card {w. is_first w(p@[v])\<and>w\<noteq>v}+card {w. is_first v(p@[v])\<and>w=v}"
    using is_first_imp_in_set by (subst card_Un_disjoint[symmetric]) 
      (auto intro:finite_subset[OF _ 3] arg_cong[where f="card"])
  also have "... = card {w. is_first w p \<and>w\<noteq>v} + of_bool (is_first v (p@[v]))" 
    using 4 by (intro arg_cong2[where f="(+)"] arg_cong[where f="card"] Collect_cong) auto
  also have "... = card {w. is_first w p} + \<tau>"
    using 5 6 by (intro arg_cong2[where f="(+)"] arg_cong[where f="card"] Collect_cong) auto
  finally have 2:"card {w. is_first w (p@[v])} = card {w. is_first w p} + \<tau>" by simp

  have "?e {v} \<subseteq> V" using v_range environment_range by auto
  hence "V-?e (set (p@[v])) \<union> (?e {v}-?e (set p)) = V - ?e (set p)"
    unfolding set_append environment_union by auto
  moreover have "?e {v} \<subseteq> ?e (set (p@[v]))" unfolding environment_def by auto
  hence "(V-?e (set (p@[v]))) \<inter> (?e {v}-?e (set p)) = {}" by blast
  moreover have "finite (?e {v})" by (intro finite_environment) auto
  ultimately have 3: 
    "(\<Sum>v\<in>V-?e (set (p@[v])). ?d v)+ (\<Sum>v\<in>?e {v}-?e (set p). ?d v) = (\<Sum>v\<in>V-?e (set p). ?d v)"
    using finV by (subst sum.union_disjoint[symmetric]) auto 

  show ?thesis 
    using assms 2 3 unfolding real_tau by (subst (1 2) p_estimator) auto
qed

lemma derandomized_indep_set_correct_aux:
  assumes "p1@p2 \<in> permutations_of_set V"
  shows "distinct (derandomized_indep_set p1 p2 E) \<and> 
    is_independent_set (set (derandomized_indep_set p1 p2 E))"
  using assms
proof (induction p1 arbitrary: p2 rule:subseq_induct')
  case 1
  hence "distinct (indep_set p2 E) \<and> is_independent_set (set (indep_set p2 E))"
    using permutations_of_setD by (intro conjI indep_set_correct) auto
  thus ?case by simp
next
  case (2 p1h p1t)
  define p1 where "p1 = p1h#p1t"
  define node_deg where "node_deg = (\<lambda>v. real (card {e \<in> E. v \<in> e}))"
  define is_indep where "is_indep = (\<lambda>v. list_all (\<lambda>w. {v,w} \<notin> E) p2)"
  define env where "env = (\<lambda>v. filter is_indep (v#filter (\<lambda>w. {v,w} \<in> E) (p1h#p1t)))"
  define cost where "cost = (\<lambda>v. (\<Sum>w \<leftarrow> env v. 1 /(node_deg w+1) ) - of_bool(is_indep v))"
  define w where "w = arg_min_list cost p1"
  have w_set: "w \<in> set p1" unfolding w_def p1_def using arg_min_list_in by blast
  have perm: "p1@p2 \<in> permutations_of_set V" using 2(2) p1_def by auto
  have dist: "distinct p1" "distinct p2" "set p1 \<inter> set p2 = {}" "set p1 \<union> set p2 = V"
    "set p1 = V - set p2" using permutations_of_setD[OF perm] by auto

  have a: "set (remove1 w p1 @ p2 @ [w]) = V" using w_set dist(4) by (auto simp:set_remove1_eq[OF dist(1)])

  have b: "distinct (remove1 w p1 @ p2 @ [w])" using dist(1,2,3) w_set by auto
  have c: "strict_subseq (remove1 w p1) p1" by (intro strict_subseq_remove1 w_set)

  have "distinct (derandomized_indep_set (remove1 w (p1h # p1t)) (p2 @ [w]) E) \<and>
    is_independent_set (set (derandomized_indep_set (remove1 w (p1h # p1t)) (p2 @ [w]) E))"
    using a b c unfolding p1_def by (intro 2 permutations_of_setI) simp_all
  thus ?case
    unfolding p1_def derandomized_indep_set.simps node_deg_def[symmetric] is_indep_def[symmetric]
    by (simp del:remove1.simps add:Let_def cost_def p1_def env_def w_def)
qed

lemma derandomized_indep_set_length_aux:
  assumes "p1@p2 \<in> permutations_of_set V"
  shows "length (derandomized_indep_set p1 p2 E) \<ge> p_estimator p2"
  using assms
proof (induction p1 arbitrary: p2 rule:subseq_induct')
  case 1
  have a:"set p2 - environment (set p2) = {}" using environment_self by auto
  have "p_estimator p2 = card {v. is_first v p2}"
    using permutations_of_setD[OF 1] by (subst p_estimator) (auto simp:a)
  also have "... \<le> card (set (indep_set p2 E))"
    using permutations_of_setD[OF 1] set_indep_set by (intro of_nat_mono card_mono) auto
  also have "... \<le> length (indep_set p2 E)" using card_length by auto
  also have "... = length (derandomized_indep_set [] p2 E)" using 1 by simp
  finally show ?case by simp
next
  case (2 p1h p1t)
  define p1 where "p1 = p1h#p1t"
  define node_deg where "node_deg = (\<lambda>v. real (card {e \<in> E. v \<in> e}))"
  define is_indep where "is_indep = (\<lambda>v. list_all (\<lambda>w. {v,w} \<notin> E) p2)"
  define env where "env = (\<lambda>v. filter is_indep (v#filter (\<lambda>w. {v,w} \<in> E) (p1h#p1t)))"
  define cost where "cost = (\<lambda>v. (\<Sum>w \<leftarrow> env v. 1 /(node_deg w+1) ) - of_bool(is_indep v))"
  define w where "w = arg_min_list cost p1"

  let ?e = "environment"
  have perm: "p1@p2 \<in> permutations_of_set V" using 2(2) p1_def by auto
  have dist: "distinct p1" "distinct p2" "set p1 \<inter> set p2 = {}" "set p1 \<union> set p2 = V"
    "set p1 = V - set p2" "set p2 = V - set p1"
    using permutations_of_setD[OF perm] by auto

  have w_set: "w \<in> set p1" unfolding w_def p1_def using arg_min_list_in by blast
  have v_notin_p2: "v \<notin> set p2" if "v \<in> set p1" for v using dist(5) that by auto

  have is_indep: "is_indep v = (environment {v} \<inter> set p2 = {})" if "v \<in> set p1" for v
    unfolding is_indep_def list_all_iff environment_def vert_adj_def using v_notin_p2[OF that]
    by (auto simp add:insert_commute)

  have cost_correct: "cost v = p_estimator p2 - p_estimator (p2@[v])" 
   (is "?L = ?R") if "v \<in> set p1" for v
  proof -
    have "set (env v) = {x \<in> {v} \<union> {x \<in> set p1. {v, x} \<in> E}. is_indep x}"
      unfolding env_def p1_def[symmetric] by auto
    also have "... = {x \<in> environment {v} \<inter> set p1. is_indep x}"
      using that unfolding environment_def vert_adj_def by (auto simp:insert_commute)
    also have "... = {x \<in> environment {v} \<inter> set p1. set p2 \<inter> environment {x}  = {}}"
      using is_indep by auto
    also have "... = environment {v} \<inter> set p1 - environment (set p2)"
      by (subst environment_sym_2) auto
    also have "... = environment {v} \<inter> (V - set p2) - environment (set p2)"
      using environment_range dist(1-4) that 
      by (intro arg_cong2[where f="(-)"] arg_cong2[where f="(\<inter>)"] refl) auto
    also have "... = environment {v} \<inter> V - set p2 - environment (set p2)" by auto
    also have "... = environment {v} \<inter> V - environment (set p2)" using environment_self by auto
    also have "... = environment {v} - environment (set p2)" 
      using that dist(4) by (intro arg_cong2[where f="(-)"] refl Int_absorb2 environment_range) auto
    finally have env_v: "set (env v) = environment {v} - environment (set p2)" by simp

    have "{v,v} \<notin> E" by (simp add: singleton_not_edge)
    hence "v \<notin> set (filter (\<lambda>w. {v, w} \<in> E) p1)" by simp
    hence "distinct (v # filter (\<lambda>w. {v, w} \<in> E) p1)" using dist(1) by simp
    hence dist_env_v: "distinct (env v)"
      unfolding env_def p1_def[symmetric] using distinct_filter by blast

    have "?L = (\<Sum>w\<leftarrow>env v. 1 / (node_deg w + 1)) - of_bool (is_indep v)"
      unfolding cost_def by simp
    also have "... = (\<Sum>w\<leftarrow>env v. 1 / (node_deg w + 1)) - of_bool(environment {v} \<inter> set p2 = {})"
      by (simp add: is_indep[OF that]) 
    also have "... = (\<Sum>w\<leftarrow>env v. 1 / (degree w + 1)) - of_bool(environment {v} \<inter> set p2 = {})"
      unfolding node_deg_def alt_degree_def incident_edges_def vincident_def by (simp add:ac_simps)
    also have "... = (\<Sum>v\<in>?e {v}-?e (set p2). 1/(degree v+1))-of_bool(?e {v} \<inter> set p2 = {})"
      by (subst sum_list_distinct_conv_sum_set[OF dist_env_v]) (simp add:env_v)
    also have "... = - (of_bool(?e {v}\<inter>set p2={})-(\<Sum>v\<in>?e {v}-?e (set p2). 1/(degree v+1)))"
      by (simp add:algebra_simps)
    also have "... = - (p_estimator (p2@[v]) - p_estimator (p2))"
      using that dist(2-4) by (intro arg_cong[where f="\<lambda>x. -x"] p_estimator_step[symmetric]) auto 
    also have "... = ?R" by (simp add:algebra_simps)
    finally show ?thesis by simp
  qed

  have p1_ne: "p1 \<noteq> []" using p1_def by simp

  have "card (set p1) * Min (cost ` set p1) = (\<Sum>v \<in> set p1. Min (cost ` set p1))" by simp
  also have "... \<le> (\<Sum>v \<in> set p1. cost v)" by (intro sum_mono) simp
  also have "... = (\<Sum>v \<in> set p1. p_estimator p2 - p_estimator (p2@[v]))"
    by (intro sum.cong cost_correct refl)
  also have "... = (\<Sum>v \<in> V-set p2. p_estimator p2 - p_estimator (p2@[v]))"
    using dist(1-4) by (intro sum.cong) auto
  also have "... = card (V-set p2) * p_estimator p2 -  (\<Sum>v \<in> V-set p2. p_estimator (p2@[v]))"
    unfolding sum_subtractf by simp
  also have "... = 0" using dist(5)[symmetric] p1_ne by (subst p_estimator_split) auto
  finally have "Min (cost ` set p1) \<le> 0" using p1_ne by (simp add: mult_le_0_iff)
  hence cost_w_nonpos: "cost w \<le> 0" unfolding w_def f_arg_min_list_f[OF p1_ne] by argo 

  have a: "set (remove1 w p1 @ p2 @ [w]) = V"
    using w_set dist(4) by (auto simp:set_remove1_eq[OF dist(1)])

  have b: "distinct (remove1 w p1 @ p2 @ [w])" 
    using dist(1,2,3) v_notin_p2[OF w_set] by auto

  have c: "strict_subseq (remove1 w p1) p1" by (intro strict_subseq_remove1 w_set)

  have "p_estimator p2 \<le> p_estimator p2 - cost w" using cost_w_nonpos by simp
  also have "... = p_estimator (p2@[w])" unfolding cost_correct[OF w_set] by simp
  also have "... \<le> length (derandomized_indep_set (remove1 w p1) (p2@[w]) E)" 
    using c by (intro 2 a b permutations_of_setI) (auto simp:p1_def)
  also have "... = real (length (derandomized_indep_set p1 p2 E))"
    unfolding p1_def derandomized_indep_set.simps node_deg_def[symmetric] is_indep_def[symmetric]
    by (simp del:remove1.simps add:Let_def cost_def p1_def env_def w_def)
  finally show ?case by (simp add:p1_def)
qed

text \<open>The main result of this section the algorithm @{term "derandomized_indep_set"} obtains
an independent set meeting the Caro-Wei bound in polynomial time.\<close>

theorem derandomized_indep_set:
  assumes "p \<in> permutations_of_set V"
  shows 
    "is_independent_set (set (derandomized_indep_set p [] E))" 
    "distinct (derandomized_indep_set p [] E)"
    "length (derandomized_indep_set p [] E) \<ge> (\<Sum>v \<in> V. 1/ (degree v+1))"
    "length (derandomized_indep_set p [] E) \<ge> card V / (2*card E / card V + 1)"
proof -
  let ?res = "derandomized_indep_set p [] E"
  show "is_independent_set (set ?res)" using assms derandomized_indep_set_correct_aux by auto
  show "distinct ?res" using assms derandomized_indep_set_correct_aux by auto

  have "(\<Sum>v \<in> V. 1/ (degree v+1)) \<le> p_estimator []"
    by (subst p_estimator) (simp_all add:environment_def is_first_def ac_simps)
  also have "... \<le> length ?res" using assms derandomized_indep_set_length_aux by auto
  finally show a:  "(\<Sum>v \<in> V. 1/ (degree v+1)) \<le> length ?res" by auto
  thus "card V / (2*card E / card V + 1) \<le> length ?res" using caro_wei_aux by simp
qed

end

end
