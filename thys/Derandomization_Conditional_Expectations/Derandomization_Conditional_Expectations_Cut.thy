section \<open>Method of Conditional Expectations: Large Cuts\<close>

text \<open>The following is an example of the application of the method of conditional
expectations~\cite{jukna2001,alon2000} to construct an approximation algorithm that finds a cut of
an undirected graph cutting at least half of the edges. This is also the example that 
Vadhan~\cite[Section 3.4.2]{vadhan2012} uses to introduce the 
``Method of Conditional Expectations''.\<close>

theory Derandomization_Conditional_Expectations_Cut
  imports Derandomization_Conditional_Expectations_Preliminary
begin

context fin_sgraph
begin

definition cut_size where "cut_size C = card {e \<in> E. e \<inter> C \<noteq> {} \<and> e - C \<noteq> {}}"

lemma eval_cond_edge:
  assumes "L \<subseteq> U" "finite U" "e \<in> E"
  shows "(\<integral>C. of_bool (e\<inter>C\<noteq>{} \<and> e-C\<noteq>{}) \<partial>pmf_of_set {C. L\<subseteq>C\<and>C\<subseteq>U}) = 
    ((if e \<subseteq> -U \<union> L then of_bool(e \<inter> L \<noteq>{} \<and> e \<inter> -U \<noteq>{} )::real else 1/2))"
    (is "?L = ?R")
proof -
  obtain e1 e2 where e_def: "e = {e1,e2}" "e1 \<noteq> e2" using two_edges[OF assms(3)]
    by (meson card_2_iff)

  let ?sing_iff = "(\<lambda>x e. (if x then {e} else {}))"

  define R1 where "R1 = (if e1 \<in> L then {True} else (if e1 \<in> U - L then {False,True} else {False}))"
  define R2 where "R2 = (if e2 \<in> L then {True} else (if e2 \<in> U - L then {False,True} else {False}))"

  have bij: "bij_betw (\<lambda>x. ((e1 \<in> x,e2 \<in>x),x-{e1,e2})) {C. L \<subseteq> C \<and> C \<subseteq> U} 
    ((R1 \<times> R2) \<times> {C. L-{e1,e2} \<subseteq> C \<and> C \<subseteq> U-{e1,e2}})"
    unfolding R1_def R2_def using e_def(2) assms(1)
    by (intro bij_betwI[where g="(\<lambda>((a,b),x). x \<union> ?sing_iff a e1 \<union> ?sing_iff b e2)"]) 
     (auto split:if_split_asm)  (* SLOW *)

  have r: "map_pmf (\<lambda>x. (e1 \<in> x, e2 \<in> x)) (pmf_of_set {C. L \<subseteq> C \<and> C \<subseteq> U}) = pmf_of_set (R1 \<times> R2)"
    using assms(1,2) map_pmf_of_set_bij_betw_2[OF bij] by auto

  have "?L = \<integral>C. of_bool ((e1 \<in> C) \<noteq> (e2 \<in> C)) \<partial>(pmf_of_set {C. L \<subseteq> C \<and> C \<subseteq> U})"
    unfolding e_def(1) using e_def(2) by (intro integral_cong_AE AE_pmfI) auto
  also have "... = \<integral>x. of_bool(fst x \<noteq> snd x) \<partial>pmf_of_set (R1 \<times> R2)"
    unfolding r[symmetric] by simp
  also have "... = (if {e1,e2} \<subseteq> -U \<union> L then of_bool({e1,e2} \<inter> L \<noteq>{}\<and>{e1,e2} \<inter>- U \<noteq>{} ) else 1/2)"
    unfolding R1_def R2_def e_def(1) using e_def(2) assms(1)
    by (auto simp add:integral_pmf_of_set split:if_split_asm)
  also have "... = ?R" unfolding e_def by simp
  finally show ?thesis by simp
qed

text \<open>If every vertex is selected independently with probability $\frac{1}{2}$ into the cut, it is
easy to deduce that an edge will be cut with probability $\frac{1}{2}$ as well. Thus the expected cut size will be
@{term "real (card E) / 2"}.\<close>

lemma exp_cut_size:
  "(\<integral>C. real (cut_size C) \<partial>pmf_of_set (Pow V)) = real (card E) / 2" (is "?L = ?R")
proof -
  have a:"False" if "x \<in> E" "x \<subseteq> -V" for x
  proof -
    have "x = {}" using wellformed[OF that(1)] that(2) by auto
    thus "False" using two_edges[OF that(1)] by simp
  qed

  have "?L = (\<integral>C. (\<Sum>e \<in> E. of_bool (e \<inter> C \<noteq> {} \<and> e - C \<noteq> {})) \<partial>pmf_of_set (Pow V))"
    using fin_edges by (simp_all add:of_bool_def cut_size_def sum.If_cases Int_def)
  also have "... = (\<Sum>e \<in> E. (\<integral>C. of_bool (e \<inter> C \<noteq> {} \<and> e - C \<noteq> {}) \<partial>pmf_of_set (Pow V)))"
    using finV by (intro Bochner_Integration.integral_sum integrable_measure_pmf_finite) 
     (simp add: Pow_not_empty)
  also have "... = (\<Sum>e \<in> E. (\<integral>C. of_bool (e\<inter>C\<noteq>{} \<and> e - C \<noteq> {}) \<partial>pmf_of_set {C. {} \<subseteq> C \<and> C \<subseteq> V}))"
    unfolding Pow_def by simp
  also have "... = (\<Sum>e \<in> E.  (if e \<subseteq> - V \<union> {} then of_bool (e \<inter> {} \<noteq>{}\<and>e \<inter>-V \<noteq>{}) else 1 / 2))"
    by (intro sum.cong eval_cond_edge finV) auto
  also have "... = (\<Sum>e \<in> E. 1/2)" using a by (intro sum.cong) auto
  also have "... = ?R" by simp
  finally show ?thesis by simp
qed

text \<open>For the above it is easy to show that there exists a cut, cutting at least half of the edges.\<close>

lemma exists_cut: "\<exists>C \<subseteq> V. real (cut_size C) \<ge> card E/2"
proof -
  have "\<exists>x\<in>set_pmf (pmf_of_set (Pow V)). card E / 2 \<le> cut_size x" using finV exp_cut_size[symmetric]
    by (intro exists_point_above_expectation integrable_measure_pmf_finite)(auto simp:Pow_not_empty)
  moreover have "set_pmf (pmf_of_set (Pow V)) = Pow V"
    using finV Pow_not_empty by (intro set_pmf_of_set) auto
  ultimately show ?thesis by auto
qed

end

text \<open>However the above is just an existence proof, but it doesn't provide a method to construct
such a cut efficiently. Here, we can apply the method of conditional expectations.

This works because, we can not only compute the expectation of the number of cut edges, when
all vertices are chosen at random, but also conditional expectations, when some of the edges
are fixed. The idea of the algorithm, is to choose the assignment of vertices into the cut
based on which option maximizes the conditional expectation. The latter can be done incrementally for each vertex.

This results in the following efficient algorithm:\<close>

fun derandomized_max_cut :: "'a list \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set" where 
  "derandomized_max_cut [] R _ _ = R" |
  "derandomized_max_cut (v#vs) R B E = 
    (if card {e \<in> E. v \<in> e \<and> e \<inter> R \<noteq> {}} \<ge> card {e \<in> E. v \<in> e \<and> e \<inter> B \<noteq> {}} then
      derandomized_max_cut vs R (B \<union> {v}) E
    else
      derandomized_max_cut vs (R \<union> {v}) B E
    )"

context fin_sgraph
begin

text \<open>The term @{term cond_exp} is the conditional expectation, when some of the edges are selected
into the cut, and some are selected to be outside the cut, while the remaining vertices are chosen
randomly.\<close>

definition cond_exp where "cond_exp R B = (\<integral>C. real (cut_size C) \<partial>pmf_of_set {C. R \<subseteq> C \<and> C \<subseteq> V-B})"

text \<open>The following is the crucial property of conditional expectations, the average of choosing
a vertex in/out is the same as not fixing that vertex. This means that at least one choice will
not decrease the conditional expectation.\<close>

lemma cond_exp_split:
  assumes "R \<subseteq> V" "B \<subseteq> V" "R \<inter> B = {}" "v \<in> V -R-B"
  shows "cond_exp R B = (cond_exp (R \<union> {v}) B + cond_exp R (B \<union> {v}))/2" (is "?L = ?R")
proof -
  let ?A = "{C. R\<union>{v}\<subseteq>C\<and>C\<subseteq>V-B}"
  let ?B = "{C. R\<subseteq>C\<and>C\<subseteq>V-(B\<union>{v})}"
  define p where "p = real (card ?A) / (card ?A + card ?B)"

  have a: "{C. R\<subseteq>C\<and>C\<subseteq>V-B} = ?A \<union> ?B" using assms by auto
  have b: "?A \<inter> ?B = {}" using assms by auto
  have c: "finite (?A \<union> ?B)" using finV by auto
  have "R \<union>{v} \<subseteq> V-B" using assms by auto
  hence g: "?A \<noteq> {}" by auto
  hence d: "?A \<union> ?B \<noteq> {}" by simp
  have e: "real (cut_size x) \<le> real (card E)" for x
    unfolding cut_size_def by (intro of_nat_mono card_mono fin_edges) auto

  have "card ?A = card ?B" using assms(1-4) 
    by (intro bij_betw_same_card[where f="\<lambda>x. x - {v}"] bij_betwI[where g="insert v"]) auto
  moreover have "card ?A > 0" using g c card_gt_0_iff by auto 
  ultimately have p_val: "p = 1/2" unfolding p_def by auto
  have "?L = (\<integral>b.(\<integral>C. real (cut_size C) \<partial>pmf_of_set (if b then ?A else ?B)) \<partial>bernoulli_pmf p)"
    using e unfolding cond_exp_def a pmf_of_set_un[OF d b c] p_def
    by (subst integral_bind_pmf[where M="card E"]) auto 
  also have "... = ((\<integral>C. real(cut_size C) \<partial>pmf_of_set ?A)+(\<integral>C. real(cut_size C) \<partial>pmf_of_set ?B))/2"
    unfolding p_val by (subst integral_bernoulli_pmf) simp_all
  also have "... = ?R" unfolding cond_exp_def by simp
  finally show ?thesis by simp
qed

lemma cond_exp_cut_size:
  assumes "R \<subseteq> V" "B \<subseteq> V" "R \<inter> B = {}"
  shows "cond_exp R B = real (card {e\<in>E. e\<inter>R\<noteq>{}\<and>e\<inter>B\<noteq>{}}) + real (card {e\<in>E. e\<inter>V-R-B\<noteq>{}}) / 2" 
    (is "?L = ?R")
proof -
  have a:"finite {C. R \<subseteq> C \<and> C \<subseteq> V - B} " "{C. R \<subseteq> C \<and> C \<subseteq> V - B} \<noteq> {}" using finV assms by auto 

  have b:"e \<subseteq> -V \<union> B \<union> R" if cthat: "e \<in> E" "e \<inter> R \<noteq> {}" "e \<inter> B \<noteq> {}" for e
  proof -
    obtain e1 where e1: "e1 \<in> e \<inter> R" using cthat(2) by auto
    obtain e2 where e2: "e2 \<in> e \<inter> B" using cthat(3) by auto
    have "e1 \<noteq> e2" using e1 e2 assms(3) by auto
    hence "card {e1,e2} = 2" by auto
    hence "e = {e1,e2}" using two_edges[OF cthat(1)] e1 e2 
      by (intro card_seteq[symmetric]) (auto intro!:card_ge_0_finite) 
    thus ?thesis using e1 e2 by simp
  qed

  have "?L = (\<integral>C. (\<Sum>e \<in> E. of_bool (e \<inter> C \<noteq> {} \<and> e - C \<noteq> {})) \<partial>pmf_of_set {C. R \<subseteq> C \<and> C \<subseteq> V-B})"
    unfolding cond_exp_def using fin_edges 
    by (simp_all add:of_bool_def cut_size_def sum.If_cases Int_def)
  also have "... = (\<Sum>e \<in> E. (\<integral>C. of_bool (e\<inter>C \<noteq> {} \<and> e-C \<noteq> {}) \<partial>pmf_of_set {C. R\<subseteq>C \<and> C\<subseteq>V-B}))"
    using a by (intro Bochner_Integration.integral_sum integrable_measure_pmf_finite) auto
  also have "... = (\<Sum>e \<in> E. ((if e \<subseteq> -(V-B) \<union> R then of_bool(e\<inter>R\<noteq>{}\<and>e\<inter>-(V-B)\<noteq>{})::real else 1/2)))"
    using finV assms(1,3) by (intro sum.cong eval_cond_edge) auto
  also have "... = real (card {e\<in>E. e\<subseteq>-V\<union>B\<union>R\<and>e\<inter>R\<noteq>{}\<and>e\<inter>-(V-B)\<noteq>{}}) + real (card {e\<in>E. \<not> e \<subseteq>-V\<union>B\<union> R}) / 2"
    using fin_edges by (simp add: sum.If_cases of_bool_def Int_def)
  also have "... = ?R" using wellformed assms b
    by (intro arg_cong[where f="card"] arg_cong2[where f="(+)"] arg_cong[where f="real"] 
        arg_cong2[where f="(/)"] refl Collect_cong order_antisym) auto
  finally show ?thesis by simp
qed

text \<open>Indeed the algorithm returns a cut with the promised approximation guarantee.\<close>

theorem derandomized_max_cut:
  assumes "vs \<in> permutations_of_set V"
  defines "C \<equiv> derandomized_max_cut vs {} {} E"
  shows "C \<subseteq> V" "2 * cut_size C \<ge> card E"
proof -
  define R :: "'a set" where "R = {}"
  define B :: "'a set" where "B = {}"
  have a:"cut_size (derandomized_max_cut vs R B E) \<ge> cond_exp R B \<and>
      (derandomized_max_cut vs R B E) \<subseteq> V"
    if "distinct vs" "set vs \<inter> R = {}" "set vs \<inter> B = {}" "R \<inter> B = {}" "\<Union>{set vs,R,B}= V" 
    using that
  proof (induction vs arbitrary: R B)
    case Nil
    have "cond_exp R B = real (card {e\<in>E. e\<inter>R\<noteq>{}\<and>e\<inter>B\<noteq>{}}) + real (card {e\<in>E. e\<inter>V-R-B \<noteq> {}}) / 2"
      using Nil by (intro cond_exp_cut_size) auto
    also have "... = real (card {e\<in>E. e\<inter>R\<noteq>{}\<and>e\<inter>B\<noteq>{}})+real (card ({}::'a set set ))/2" using Nil
      by (intro arg_cong[where f="card"] arg_cong2[where f="(+)"]  arg_cong2[where f="(/)"] 
          arg_cong[where f="real"]) auto
    also have "... = real (card {e\<in>E. e\<inter>R\<noteq>{}\<and>e\<inter>B\<noteq>{}})" by simp
    also have "... = real (cut_size R)" using Nil wellformed unfolding cut_size_def
      by (intro arg_cong[where f="card"] arg_cong2[where f="(+)"] arg_cong[where f="real"]) auto
    finally have "cond_exp R B = real (cut_size R)" by simp
    thus ?case using Nil by auto 
  next
    case (Cons vh vt)
    let ?NB = "{e \<in> E. vh \<in> e \<and> e \<inter> B \<noteq> {}}"
    let ?NR = "{e \<in> E. vh \<in> e \<and> e \<inter> R \<noteq> {}}"
    define t where "t = real (card {e \<in> E. e \<inter> V - R - (B \<union> {vh}) \<noteq> {}}) / 2"
    have t_alt: "t = real (card {e \<in> E. e \<inter> V - (R \<union> {vh}) - B \<noteq> {}}) / 2"
      unfolding t_def by (intro arg_cong[where f="\<lambda>x. real (card x) /2"]) auto

    have "cond_exp R (B\<union>{vh})-card ?NR = real(card {e\<in>E. e\<inter>R\<noteq>{}\<and>e\<inter>(B\<union>{vh})\<noteq>{}})-(card ?NR)+t"
      using Cons(2-6) unfolding t_def by (subst cond_exp_cut_size) auto
    also have "... = real(card {e\<in>E. e\<inter>R\<noteq>{}\<and>e\<inter>(B\<union>{vh})\<noteq>{}}-card ?NR)+t"
      using fin_edges by (intro of_nat_diff[symmetric] arg_cong2[where f="(+)"] card_mono) auto
    also have "... = real(card ({e\<in>E. e\<inter>R\<noteq>{}\<and>e\<inter>(B\<union>{vh})\<noteq>{}}- ?NR))+t"
      using fin_edges by (intro arg_cong[where f="(\<lambda>x. real x+t)"] card_Diff_subset[symmetric]) auto
    also have "... = real(card ({e\<in>E. e\<inter>(R\<union>{vh})\<noteq>{}\<and>e\<inter>B\<noteq>{}}- ?NB))+t"
      by (intro arg_cong[where f="(\<lambda>x. real (card x) + t)"] ) auto
    also have "... = real(card {e\<in>E. e\<inter>(R\<union>{vh})\<noteq>{}\<and>e\<inter>B\<noteq>{}}-card ?NB)+t"
      using fin_edges by (intro arg_cong[where f="(\<lambda>x. real x+t)"] card_Diff_subset) auto
    also have "... = real(card {e\<in>E. e\<inter>(R\<union>{vh})\<noteq>{}\<and>e\<inter>B\<noteq>{}})-(card ?NB)+t"
      using fin_edges by (intro of_nat_diff arg_cong2[where f="(+)"] card_mono) auto
    also have "... = cond_exp (R\<union>{vh}) B -card ?NB"
      using Cons(2-6) unfolding t_alt by (subst cond_exp_cut_size) auto
    finally have d:"cond_exp R (B\<union>{vh}) - cond_exp (R\<union>{vh}) B = real (card ?NR) - card ?NB" 
      by (simp add:ac_simps)

    have split: "cond_exp R B = (cond_exp (R \<union> {vh}) B + cond_exp R (B \<union> {vh})) / 2"
      using Cons(2-6) by (intro cond_exp_split) auto

    have dvt: "distinct vt" using Cons(2) by simp
    show ?case 
    proof (cases "card ?NR \<ge> card ?NB")
      case True
      have 0:"set vt\<inter>R={}" "set vt\<inter>(B\<union>{vh})={}" "R\<inter>(B\<union>{vh})={}" "\<Union>{set vt,R,B\<union>{vh}}=V"
        using Cons(2-6) by auto

      have "cond_exp R B \<le> cond_exp R (B \<union> {vh})" unfolding split using d True by simp
      thus ?thesis using True Cons(1)[OF dvt 0] by simp
    next
      case False
      have 0:"set vt\<inter>(R\<union>{vh})={}" "set vt\<inter>B={}" "(R\<union>{vh})\<inter>B={}" "\<Union>{set vt,R\<union>{vh},B}=V"
        using Cons(2-6) by auto
      have "cond_exp R B \<le> cond_exp (R \<union> {vh}) B" unfolding split using d False by simp
      thus ?thesis using False Cons(1)[OF dvt 0] by simp
    qed
  qed
  moreover have "e \<inter> V \<noteq> {}" if "e \<in> E" for e 
    using Int_absorb2[OF wellformed[OF that]] two_edges[OF that] by auto
  hence "{e \<in> E. e \<inter> V \<noteq> {}} = E"  by auto
  hence "cond_exp {} {} = graph_size /2" by (subst cond_exp_cut_size) auto
  ultimately show "C \<subseteq> V" "2 * cut_size C \<ge> card E"
    unfolding C_def R_def B_def using permutations_of_setD[OF assms(1)] by auto
qed

end

end
