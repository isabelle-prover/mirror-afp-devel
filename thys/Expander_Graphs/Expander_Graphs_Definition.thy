section \<open>Definitions\label{sec:definitions}\<close>

text \<open>This section introduces regular graphs as a sublocale in the graph theory developed by
Lars Noschinski~\cite{Graph_Theory-AFP} and introduces various expansion coefficients.\<close> 

theory Expander_Graphs_Definition
  imports 
    Graph_Theory.Digraph_Isomorphism
    "HOL-Analysis.L2_Norm" 
    Extra_Congruence_Method
    Expander_Graphs_Multiset_Extras
    Jordan_Normal_Form.Conjugate
    Interpolation_Polynomials_HOL_Algebra.Interpolation_Polynomial_Cardinalities
begin

unbundle intro_cong_syntax

definition arcs_betw where "arcs_betw G u v = {a. a \<in> arcs G \<and> head G a = v \<and> tail G a = u}"

text \<open>The following is a stronger notion than the notion of symmetry defined in 
@{theory "Graph_Theory.Digraph"}, it requires that the number of edges from @{term "v"} to 
@{term "w"} must be equal to the number of edges from @{term "w"} to @{term "v"} for any pair of 
vertices @{term "v"} @{term "w \<in> verts G"}.\<close>

definition symmetric_multi_graph where "symmetric_multi_graph G =
  (fin_digraph G \<and> (\<forall>v w. {v, w} \<subseteq> verts G \<longrightarrow> card (arcs_betw G w v) = card (arcs_betw G v w)))"

lemma symmetric_multi_graphI:
  assumes "fin_digraph G"
  assumes "bij_betw f (arcs G) (arcs G)"
  assumes "\<And>e. e \<in> arcs G \<Longrightarrow> head G (f e) = tail G e \<and> tail G (f e) = head G e"
  shows "symmetric_multi_graph G"
proof -
  have "card (arcs_betw G w v) = card (arcs_betw G v w)"
    (is "?L = ?R") if "v \<in> verts G" "w \<in> verts G" for v w
  proof -
    have a:"f x \<in> arcs G" if "x \<in> arcs G" for x
      using assms(2) that unfolding bij_betw_def by auto
    have b:"\<exists>y. y \<in> arcs G \<and> f y = x" if "x \<in> arcs G" for x
      using bij_betw_imp_surj_on[OF assms(2)] that by force

    have "inj_on f (arcs G)" 
      using assms(2) unfolding bij_betw_def by simp
    hence "inj_on f {e \<in> arcs G. head G e = v \<and> tail G e = w}"
      by (rule inj_on_subset, auto)
    hence "?L = card (f ` {e \<in> arcs G. head G e = v \<and> tail G e = w})"
      unfolding arcs_betw_def
      by (intro card_image[symmetric])
    also have "... = ?R"
      unfolding arcs_betw_def using a b assms(3)
      by (intro arg_cong[where f="card"] order_antisym image_subsetI subsetI) fastforce+ 
    finally show ?thesis by simp
  qed
  thus ?thesis 
    using assms(1) unfolding symmetric_multi_graph_def by simp
qed

lemma symmetric_multi_graphD2:
  assumes "symmetric_multi_graph G"
  shows "fin_digraph G"
  using assms unfolding symmetric_multi_graph_def by simp 

lemma symmetric_multi_graphD:
  assumes "symmetric_multi_graph G"
  shows "card {e \<in> arcs G. head G e=v \<and> tail G e=w} = card {e \<in> arcs G. head G e=w \<and> tail G e=v}" 
    (is "card ?L = card ?R")
proof (cases "v \<in> verts G \<and> w \<in> verts G")
  case True
  then show ?thesis 
  using assms unfolding symmetric_multi_graph_def arcs_betw_def by simp 
next
  case False
  interpret fin_digraph G
    using symmetric_multi_graphD2[OF assms(1)] by simp
  have 0:"?L = {}" "?R = {}"
    using False wellformed by auto
  show ?thesis unfolding 0 by simp
qed

lemma symmetric_multi_graphD3:
  assumes "symmetric_multi_graph G"
  shows
    "card {e\<in>arcs G. tail G e=v \<and> head G e=w}=card {e\<in>arcs G. tail G e=w\<and>head G e=v}" 
  using symmetric_multi_graphD[OF assms] by (simp add:conj.commute)

lemma symmetric_multi_graphD4:
  assumes "symmetric_multi_graph G"
  shows "card (arcs_betw G v w) = card (arcs_betw G w v)" 
  using symmetric_multi_graphD[OF assms] unfolding arcs_betw_def by simp

lemma symmetric_degree_eq:
  assumes "symmetric_multi_graph G"
  assumes "v \<in> verts G"
  shows "out_degree G v = in_degree G v" (is "?L = ?R")
proof -
  interpret fin_digraph "G" 
    using assms(1) symmetric_multi_graph_def by auto

  have "?L = card {e \<in> arcs G. tail G e = v}"
    unfolding out_degree_def out_arcs_def by simp
  also have "... = card (\<Union>w \<in> verts G. {e \<in> arcs G. head G e = w \<and> tail G e = v})"
    by (intro arg_cong[where f="card"]) (auto simp add:set_eq_iff)
  also have "... = (\<Sum>w \<in> verts G. card {e \<in> arcs G. head G e = w \<and> tail G e = v})"
    by (intro card_UN_disjoint) auto
  also have "... = (\<Sum>w \<in> verts G. card {e \<in> arcs G. head G e = v \<and> tail G e = w})"
    by (intro sum.cong refl symmetric_multi_graphD assms)
  also have "... = card (\<Union>w \<in> verts G. {e \<in> arcs G. head G e = v \<and> tail G e = w})"
    by (intro card_UN_disjoint[symmetric]) auto
  also have "... = card (in_arcs G v)"
    by (intro arg_cong[where f="card"]) (auto simp add:set_eq_iff) 
  also have "... = ?R" 
    unfolding in_degree_def by simp
  finally show ?thesis by simp
qed

definition edges where "edges G = image_mset (arc_to_ends G) (mset_set (arcs G))"

lemma (in fin_digraph) count_edges:
  "count (edges G) (u,v) = card (arcs_betw G u v)" (is "?L = ?R")
proof -
  have "?L = card {x \<in> arcs G. arc_to_ends G x = (u, v)}"
    unfolding edges_def count_mset_exp image_mset_filter_mset_swap[symmetric] by simp
  also have "... = ?R"
    unfolding arcs_betw_def arc_to_ends_def
    by (intro arg_cong[where f="card"]) auto
  finally show ?thesis by simp
qed

lemma (in fin_digraph) count_edges_sym:
  assumes "symmetric_multi_graph G"
  shows "count (edges G) (v, w) = count (edges G) (w, v)" 
  unfolding count_edges using symmetric_multi_graphD4[OF assms]  by simp

lemma (in fin_digraph) edges_sym:
  assumes "symmetric_multi_graph G"
  shows "{# (y,x). (x,y) \<in># (edges G) #} = edges G" 
proof -
  have "count {#(y, x). (x, y) \<in># edges G#} x = count (edges G) x" (is "?L = ?R") for x
  proof -
    have "?L = count (edges G) (snd x, fst x)"
      unfolding count_mset_exp
      by (simp add:image_mset_filter_mset_swap[symmetric] case_prod_beta prod_eq_iff ac_simps)
    also have "... = count (edges G) (fst x, snd x)"
      unfolding count_edges_sym[OF assms] by simp
    also have "... = count (edges G) x" by simp
    finally show ?thesis by simp
  qed

  thus ?thesis
    by (intro multiset_eqI) simp
qed

definition "vertices_from G v = {# snd e | e \<in># edges G. fst e = v #}"
definition "vertices_to G v = {# fst e | e \<in># edges G. snd e = v #}"

context fin_digraph
begin

lemma edge_set: 
  assumes "x \<in># edges G"
  shows "fst x \<in> verts G" "snd x \<in> verts G"
  using assms unfolding edges_def arc_to_ends_def by auto

lemma  verts_from_alt:
  "vertices_from G v = image_mset (head G) (mset_set (out_arcs G v))"
proof -
  have "{#x \<in># mset_set (arcs G). tail G x = v#} = mset_set {a \<in> arcs G. tail G a = v}"
    by (intro filter_mset_mset_set) simp
  thus ?thesis
    unfolding vertices_from_def out_arcs_def edges_def arc_to_ends_def
    by (simp add:image_mset.compositionality image_mset_filter_mset_swap[symmetric] comp_def)
qed

lemma verts_to_alt:
  "vertices_to G v = image_mset (tail G) (mset_set (in_arcs G v))"
proof -
  have "{#x \<in># mset_set (arcs G). head G x = v#} = mset_set {a \<in> arcs G. head G a = v}"
    by (intro filter_mset_mset_set) simp
  thus ?thesis
    unfolding vertices_to_def in_arcs_def edges_def arc_to_ends_def
    by (simp add:image_mset.compositionality image_mset_filter_mset_swap[symmetric] comp_def)
qed

lemma set_mset_vertices_from:
  "set_mset (vertices_from G x) \<subseteq> verts G"
  unfolding vertices_from_def using edge_set by auto

lemma set_mset_vertices_to:
  "set_mset (vertices_to G x) \<subseteq> verts G"
  unfolding vertices_to_def using edge_set by auto

end

text \<open>A symmetric multigraph is regular if every node has the same degree. This is the context
in which the expansion conditions are introduced.\<close>

locale regular_graph = fin_digraph +
  assumes sym: "symmetric_multi_graph G"
  assumes verts_non_empty: "verts G \<noteq> {}"
  assumes arcs_non_empty: "arcs G \<noteq> {}"
  assumes reg': "\<And>v w. v \<in> verts G \<Longrightarrow> w \<in> verts G \<Longrightarrow> out_degree G v = out_degree G w"
begin

definition d where "d = out_degree G (SOME v. v \<in> verts G)"

lemmas count_sym = count_edges_sym[OF sym]

lemma reg: 
  assumes "v \<in> verts G"
  shows "out_degree G v = d" "in_degree G v = d"
proof -
  define w where "w = (SOME v. v \<in> verts G)"
  have "w \<in> verts G"
    unfolding w_def using assms(1) by (rule someI)
  hence "out_degree G v = out_degree G w"
    by (intro reg' assms(1))
  also have "... = d"
    unfolding d_def w_def by simp
  finally show a:"out_degree G v = d" by simp

  show "in_degree G v = d"
    using a symmetric_degree_eq[OF sym assms(1)] by simp
qed

definition n where "n = card (verts G)"

lemma n_gt_0: "n > 0"
  unfolding n_def using verts_non_empty by auto

lemma d_gt_0: "d > 0"
proof -
  obtain a where a:"a \<in> arcs G"
    using arcs_non_empty by auto
  hence "a \<in> in_arcs G (head G a) "
    unfolding in_arcs_def by simp
  hence "0 < in_degree G (head G a)"
    unfolding in_degree_def card_gt_0_iff by blast
  also have "... = d"
    using a by (intro reg) simp
  finally show ?thesis by simp
qed

definition g_inner :: "('a \<Rightarrow> ('c :: conjugatable_field)) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> 'c" 
  where "g_inner f g = (\<Sum>x \<in> verts G. (f x) * conjugate (g x))"

lemma conjugate_divide[simp]:
  fixes x y :: "'c :: conjugatable_field"
  shows "conjugate (x / y) = conjugate x / conjugate y"
proof (cases "y = 0")
  case True
  then show ?thesis by simp
next
  case False
  have "conjugate (x/y) * conjugate y = conjugate x"
    using False by (simp add:conjugate_dist_mul[symmetric])
  thus ?thesis
    by (simp add:divide_simps)
qed

lemma g_inner_simps:
  "g_inner (\<lambda>x. 0) g = 0" 
  "g_inner f (\<lambda>x. 0) = 0" 
  "g_inner (\<lambda>x. c * f x) g = c * g_inner f g" 
  "g_inner f (\<lambda>x. c * g x) = conjugate c * g_inner f g" 
  "g_inner (\<lambda>x. f x - g x) h = g_inner f h - g_inner g h" 
  "g_inner (\<lambda>x. f x + g x) h = g_inner f h + g_inner g h" 
  "g_inner f (\<lambda>x. g x + h x) = g_inner f g + g_inner f h" 
  "g_inner f (\<lambda>x. g x / c) = g_inner f g / conjugate c" 
  "g_inner (\<lambda>x. f x / c) g = g_inner f g / c" 
  unfolding g_inner_def 
  by (auto simp add:sum.distrib algebra_simps sum_distrib_left sum_subtractf sum_divide_distrib 
      conjugate_dist_mul conjugate_dist_add)

definition "g_norm f = sqrt (g_inner f f)"

lemma g_norm_eq: "g_norm f = L2_set f (verts G)"
  unfolding g_norm_def g_inner_def L2_set_def
  by (intro arg_cong[where f="sqrt"] sum.cong refl) (simp add:power2_eq_square)

lemma g_inner_cauchy_schwartz:
  fixes f g :: "'a \<Rightarrow> real"
  shows "\<bar>g_inner f g\<bar> \<le> g_norm f * g_norm g"
proof -
  have "\<bar>g_inner f g\<bar> \<le> (\<Sum>v \<in> verts G. \<bar>f v * g v\<bar>)" 
    unfolding g_inner_def conjugate_real_def by (intro sum_abs)
  also have "... \<le> g_norm f * g_norm g"
    unfolding g_norm_eq abs_mult by (intro L2_set_mult_ineq)
  finally show ?thesis by simp
qed

lemma g_inner_cong:
  assumes "\<And>x. x \<in> verts G \<Longrightarrow> f1 x = f2 x"
  assumes "\<And>x. x \<in> verts G \<Longrightarrow> g1 x = g2 x"
  shows "g_inner f1 g1 = g_inner f2 g2"
  unfolding g_inner_def using assms
  by (intro sum.cong refl) auto

lemma g_norm_cong:
  assumes "\<And>x. x \<in> verts G \<Longrightarrow> f x = g x"
  shows "g_norm f = g_norm g"
  unfolding g_norm_def 
  by (intro arg_cong[where f="sqrt"] g_inner_cong assms)

lemma g_norm_nonneg: "g_norm f \<ge> 0" 
  unfolding g_norm_def g_inner_def
  by (intro real_sqrt_ge_zero sum_nonneg) auto

lemma g_norm_sq:
  "g_norm f^2 = g_inner f f" 
  using g_norm_nonneg g_norm_def by simp

definition g_step :: "('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real)"
  where "g_step f v = (\<Sum>x \<in> in_arcs G v. f (tail G x) / real d)"

lemma g_step_simps:
  "g_step (\<lambda>x. f x + g x) y = g_step f y + g_step g y"
  "g_step (\<lambda>x. f x / c) y = g_step f y / c"
  unfolding g_step_def sum_divide_distrib[symmetric] using finite_in_arcs d_gt_0
  by (auto intro:sum.cong simp add:sum.distrib field_simps sum_distrib_left sum_subtractf)

lemma g_inner_step_eq:
  "g_inner f (g_step f) = (\<Sum>a \<in> arcs G. f (head G a) * f (tail G a)) / d" (is "?L = ?R")
proof -
  have "?L = (\<Sum>v\<in>verts G. f v * (\<Sum>a\<in>in_arcs G v. f (tail G a) / d))"
    unfolding g_inner_def g_step_def by simp
  also have "... = (\<Sum>v\<in>verts G. (\<Sum>a\<in>in_arcs G v. f v * f (tail G a) / d))"
    by (subst sum_distrib_left) simp
  also have "... =  (\<Sum>v\<in>verts G. (\<Sum>a\<in>in_arcs G v. f (head G a) * f (tail G a) / d))"
    unfolding in_arcs_def by (intro sum.cong refl) simp
  also have "... = (\<Sum>a \<in> (\<Union> (in_arcs G ` verts G)). f (head G a) * f (tail G a) / d)"
    using finite_verts by (intro sum.UNION_disjoint[symmetric] ballI) 
      (auto simp add:in_arcs_def)
  also have "... = (\<Sum>a \<in> arcs G. f (head G a) * f (tail G a) / d)"
    unfolding in_arcs_def using wellformed by (intro sum.cong) auto
  also have "... = ?R"
    by (intro sum_divide_distrib[symmetric])
  finally show ?thesis by simp
qed

definition \<Lambda>_test 
  where "\<Lambda>_test = {f. g_norm f^2 \<noteq> 0 \<and> g_inner f (\<lambda>_. 1) = 0}"

lemma \<Lambda>_test_ne: 
  assumes "n > 1"
  shows "\<Lambda>_test \<noteq> {}"
proof -
  obtain v where v_def: "v \<in> verts G" using verts_non_empty by auto
  have "False" if "\<And>w. w \<in> verts G \<Longrightarrow> w = v"
  proof -
    have "verts G = {v}" using that v_def 
      by (intro iffD2[OF set_eq_iff] allI) blast
    thus False
      using assms n_def by simp
  qed
  then obtain w where w_def: "w \<in> verts G" "v \<noteq> w" 
    by auto
  define f where "f x= (if x = v then 1 else (if x = w then (-1) else (0::real)))" for x

  have "g_norm f^2 = (\<Sum>x\<in>verts G. (if x = v then 1 else if x = w then - 1 else 0)\<^sup>2)"
    unfolding g_norm_sq g_inner_def conjugate_real_def power2_eq_square[symmetric] 
    by (simp add:f_def)
  also have "... = (\<Sum>x \<in> {v,w}. (if x = v then 1 else if x = w then -1 else 0)\<^sup>2)"
    using v_def(1) w_def(1) by (intro sum.mono_neutral_cong refl) auto
  also have "... = (\<Sum>x \<in> {v,w}. (if x = v then 1 else - 1)\<^sup>2)"
    by (intro sum.cong) auto
  also have "... = 2"
    using w_def(2) by (simp add:if_distrib if_distribR sum.If_cases)
  finally have "g_norm f^2 = 2" by simp
  hence "g_norm f \<noteq> 0" by auto

  moreover have "g_inner f (\<lambda>_.1) = 0"
    unfolding g_inner_def f_def using v_def w_def by (simp add:sum.If_cases)
  ultimately have "f \<in> \<Lambda>_test"
    unfolding \<Lambda>_test_def by simp
  thus ?thesis by auto
qed

lemma \<Lambda>_test_empty: 
  assumes "n = 1"
  shows "\<Lambda>_test = {}"
proof -
  obtain v where v_def: "verts G = {v}"
    using assms card_1_singletonE unfolding n_def by auto
  have "False" if "f \<in> \<Lambda>_test" for f
  proof -
    have "0 = (g_inner f (\<lambda>_.1))^2"
      using that \<Lambda>_test_def by simp
    also have "... = (f v)^2"
      unfolding g_inner_def v_def by simp
    also have "... = g_norm f^2"
      unfolding g_norm_sq g_inner_def v_def 
      by (simp add:power2_eq_square)
    also have "... \<noteq> 0"
      using that \<Lambda>_test_def by simp
    finally show "False" by simp
  qed
  thus ?thesis by auto
qed

text \<open>The following are variational definitions for the maxiumum of the spectrum (resp. maximum 
modulus of the spectrum) of the stochastic matrix (excluding the Perron eigenvalue $1$). Note that
both values can still obtain the value one $1$ (if the multiplicity of the eigenvalue $1$ is larger
than $1$ in the stochastic matrix, or in the modulus case if $-1$ is an eigenvalue).

The definition relies on the supremum of the Rayleigh-Quotient for vectors orthogonal to the
stationary distribution). In Section~\ref{sec:expander_eigenvalues}, the equivalence of this
value with the algebraic definition will be shown. The definition here has the advantage
that it is (obviously) independent of the matrix representation (ordering of the vertices) used.\<close>

definition \<Lambda>\<^sub>2 :: real
  where "\<Lambda>\<^sub>2 = (if n > 1 then (SUP f \<in> \<Lambda>_test. g_inner f (g_step f)/g_inner f f) else 0)"

definition \<Lambda>\<^sub>a :: real
  where "\<Lambda>\<^sub>a = (if n > 1 then (SUP f \<in> \<Lambda>_test. \<bar>g_inner f (g_step f)\<bar>/g_inner f f) else 0)"

lemma sum_arcs_tail:
  fixes f :: "'a \<Rightarrow> ('c :: semiring_1)"
  shows "(\<Sum>a \<in> arcs G. f (tail G a)) = of_nat d * (\<Sum>v \<in> verts G. f v)" (is "?L = ?R")
proof -
  have "?L = (\<Sum>a\<in>(\<Union>(out_arcs G ` verts G)). f (tail G a))"
    by (intro sum.cong) auto
  also have "... =  (\<Sum>v \<in> verts G. (\<Sum>a \<in> out_arcs G v. f (tail G a)))"
    by (intro sum.UNION_disjoint) auto
  also have "... = (\<Sum>v \<in> verts G. of_nat (out_degree G v) * f v)"
    unfolding out_degree_def by simp
  also have "... = (\<Sum>v \<in> verts G. of_nat d * f v)"
    by (intro sum.cong arg_cong2[where f="(*)"] arg_cong[where f="of_nat"] reg) auto
  also have "... = ?R" by (simp add:sum_distrib_left)
  finally show ?thesis by simp
qed

lemma sum_arcs_head:
  fixes f :: "'a \<Rightarrow> ('c :: semiring_1)"
  shows "(\<Sum>a \<in> arcs G. f (head G a)) = of_nat d * (\<Sum>v \<in> verts G. f v)" (is "?L = ?R")
proof -
  have "?L = (\<Sum>a\<in>(\<Union>(in_arcs G ` verts G)). f (head G a))"
    by (intro sum.cong) auto
  also have "... =  (\<Sum>v \<in> verts G. (\<Sum>a \<in> in_arcs G v. f (head G a)))"
    by (intro sum.UNION_disjoint) auto
  also have "... = (\<Sum>v \<in> verts G. of_nat (in_degree G v) * f v)"
    unfolding in_degree_def by simp
  also have "... = (\<Sum>v \<in> verts G. of_nat d * f v)"
    by (intro sum.cong arg_cong2[where f="(*)"] arg_cong[where f="of_nat"] reg) auto
  also have "... = ?R" by (simp add:sum_distrib_left)
  finally show ?thesis by simp
qed

lemma bdd_above_aux:
  "\<bar>\<Sum>a\<in>arcs G. f(head G a)*f(tail G a)\<bar> \<le> d* g_norm f^2" (is "?L \<le> ?R")
proof -
  have "(\<Sum>a\<in>arcs G. f (head G a)^2) =  d * g_norm f^2"
    unfolding sum_arcs_head[where f="\<lambda>x. f x^2"] g_norm_sq g_inner_def
    by (simp add:power2_eq_square)
  hence 0:"L2_set (\<lambda>a. f (head G a)) (arcs G) \<le> sqrt (d * g_norm f^2)" 
    using g_norm_nonneg unfolding L2_set_def by simp

  have "(\<Sum>a\<in>arcs G. f (tail G a)^2) = d * g_norm f^2"
    unfolding sum_arcs_tail[where f="\<lambda>x. f x^2"] sum_distrib_left[symmetric] g_norm_sq g_inner_def
    by (simp add:power2_eq_square)
  hence 1:"L2_set (\<lambda>a. f (tail G a)) (arcs G) \<le> sqrt (d * g_norm f^2)" 
    unfolding L2_set_def by simp

  have "?L \<le> (\<Sum>a \<in> arcs G. \<bar>f (head G a)\<bar> * \<bar>f(tail G a)\<bar>)"
    unfolding abs_mult[symmetric] by (intro divide_right_mono sum_abs) 
  also have "... \<le> (L2_set (\<lambda>a. f (head G a)) (arcs G) * L2_set (\<lambda>a. f (tail G a)) (arcs G))"
    by (intro L2_set_mult_ineq) 
  also have "... \<le> (sqrt (d * g_norm f^2) * sqrt (d * g_norm f^2))"
    by (intro mult_mono 0 1) auto
  also have "... = d * g_norm f^2"
    using d_gt_0 g_norm_nonneg by simp
  finally show ?thesis by simp
qed

lemma bdd_above_aux_2: 
  assumes "f \<in> \<Lambda>_test"
  shows "\<bar>g_inner f (g_step f)\<bar> / g_inner f f \<le> 1"
proof -
  have 0:"g_inner f f > 0" 
    using assms unfolding \<Lambda>_test_def g_norm_sq[symmetric] by auto

  have "\<bar>g_inner f (g_step f)\<bar> = \<bar>\<Sum>a\<in>arcs G. f (head G a) * f (tail G a)\<bar> / real d"
    unfolding g_inner_step_eq by simp
  also have "... \<le> d * g_norm f^2 / d"
    by (intro divide_right_mono bdd_above_aux assms) auto
  also have "... = g_inner f f"
    using d_gt_0 unfolding g_norm_sq by simp
  finally have "\<bar>g_inner f (g_step f)\<bar> \<le> g_inner f f" 
    by simp

  thus ?thesis
    using 0 by simp
qed

lemma bdd_above_aux_3: 
  assumes "f \<in> \<Lambda>_test"
  shows "g_inner f (g_step f) / g_inner f f \<le> 1" (is "?L \<le> ?R")
proof -
  have "?L \<le> \<bar>g_inner f (g_step f)\<bar> / g_inner f f"
    unfolding g_norm_sq[symmetric]
    by (intro divide_right_mono) auto
  also have "... \<le> 1"
    using bdd_above_aux_2[OF assms] by simp
  finally show ?thesis by simp
qed

lemma bdd_above_\<Lambda>: "bdd_above ((\<lambda>f. \<bar>g_inner f (g_step f)\<bar> / g_inner f f) ` \<Lambda>_test)"
  using bdd_above_aux_2
  by (intro bdd_aboveI[where M="1"])  auto

lemma bdd_above_\<Lambda>\<^sub>2: "bdd_above ((\<lambda>f. g_inner f (g_step f) / g_inner f f) ` \<Lambda>_test)"
  using bdd_above_aux_3
  by (intro bdd_aboveI[where M="1"])  auto

lemma \<Lambda>_le_1: "\<Lambda>\<^sub>a \<le> 1"
proof (cases "n > 1")
  case True
  have "(SUP f\<in>\<Lambda>_test. \<bar>g_inner f (g_step f)\<bar> / g_inner f f) \<le> 1" 
    using bdd_above_aux_2 \<Lambda>_test_ne[OF True] by (intro cSup_least) auto
  thus "\<Lambda>\<^sub>a \<le> 1"
    unfolding \<Lambda>\<^sub>a_def using True by simp
next
  case False
  thus ?thesis unfolding \<Lambda>\<^sub>a_def by simp
qed

lemma \<Lambda>\<^sub>2_le_1: "\<Lambda>\<^sub>2 \<le> 1"
proof (cases "n > 1")
  case True
  have "(SUP f\<in>\<Lambda>_test. g_inner f (g_step f) / g_inner f f) \<le> 1" 
    using bdd_above_aux_3 \<Lambda>_test_ne[OF True] by (intro cSup_least) auto
  thus "\<Lambda>\<^sub>2 \<le> 1"
    unfolding \<Lambda>\<^sub>2_def using True by simp
next
  case False
  thus ?thesis unfolding \<Lambda>\<^sub>2_def by simp
qed

lemma \<Lambda>_ge_0: "\<Lambda>\<^sub>a \<ge> 0"
proof (cases "n > 1")
  case True
  obtain f where f_def: "f \<in> \<Lambda>_test" 
    using \<Lambda>_test_ne[OF True] by auto
  have "0 \<le> \<bar>g_inner f (g_step f)\<bar> / g_inner f f"
    unfolding g_norm_sq[symmetric] by (intro divide_nonneg_nonneg) auto
  also have "... \<le> (SUP f\<in>\<Lambda>_test. \<bar>g_inner f (g_step f)\<bar> / g_inner f f)"
    using f_def by (intro cSup_upper bdd_above_\<Lambda>) auto
  finally have "(SUP f\<in>\<Lambda>_test. \<bar>g_inner f (g_step f)\<bar> / g_inner f f) \<ge> 0"
    by simp
  thus ?thesis
    unfolding \<Lambda>\<^sub>a_def using True by simp
next
  case False
  thus ?thesis unfolding \<Lambda>\<^sub>a_def by simp
qed

lemma os_expanderI:
  assumes "n > 1"
  assumes "\<And>f. g_inner f (\<lambda>_. 1)=0 \<Longrightarrow> g_inner f (g_step f) \<le> C*g_norm f^2" 
  shows "\<Lambda>\<^sub>2 \<le> C"
proof -
  have "g_inner f (g_step f) / g_inner f f \<le> C" if "f \<in> \<Lambda>_test" for f
  proof -
    have "g_inner f (g_step f) \<le> C*g_inner f f"
      using that \<Lambda>_test_def assms(2) unfolding g_norm_sq by auto
    moreover have "g_inner f f > 0"
      using that unfolding \<Lambda>_test_def g_norm_sq[symmetric] by auto
    ultimately show ?thesis 
      by (simp add:divide_simps)
  qed
  hence "(SUP f\<in>\<Lambda>_test. g_inner f (g_step f) / g_inner f f) \<le> C"
    using \<Lambda>_test_ne[OF assms(1)] by (intro cSup_least) auto
  thus ?thesis
    unfolding \<Lambda>\<^sub>2_def using assms by simp
qed

lemma os_expanderD:
  assumes "g_inner f (\<lambda>_. 1) = 0"
  shows "g_inner f (g_step f) \<le> \<Lambda>\<^sub>2 * g_norm f^2"  (is "?L \<le> ?R")
proof (cases "g_norm f \<noteq> 0")
  case True

  have 0:"f \<in> \<Lambda>_test"
    unfolding \<Lambda>_test_def using assms True by auto

  hence 1:"n > 1" 
    using \<Lambda>_test_empty n_gt_0 by fastforce

  have "g_inner f (g_step f)/ g_norm f^2 = g_inner f (g_step f)/g_inner f f" 
    unfolding g_norm_sq by simp
  also have "... \<le> (SUP f\<in>\<Lambda>_test. g_inner f (g_step f) / g_inner f f)"
    by (intro cSup_upper bdd_above_\<Lambda>\<^sub>2 imageI 0) 
  also have "... = \<Lambda>\<^sub>2"
    using 1 unfolding \<Lambda>\<^sub>2_def by simp
  finally have "g_inner f (g_step f)/ g_norm f^2 \<le> \<Lambda>\<^sub>2" by simp
  thus ?thesis 
    using True by (simp add:divide_simps)
next
  case False
  hence "g_inner f f = 0"
    unfolding g_norm_sq[symmetric] by simp
  hence 0:"\<And>v. v \<in> verts G \<Longrightarrow> f v = 0"
    unfolding g_inner_def by (subst (asm) sum_nonneg_eq_0_iff) auto
  hence "?L = 0"
    unfolding g_step_def g_inner_def by simp 
  also have "... \<le> \<Lambda>\<^sub>2 * g_norm f^2"
    using False by simp
  finally show ?thesis by simp
qed

lemma expander_intro_1:
  assumes "C \<ge> 0"
  assumes "\<And>f. g_inner f (\<lambda>_. 1)=0 \<Longrightarrow> \<bar>g_inner f (g_step f)\<bar> \<le> C*g_norm f^2" 
  shows "\<Lambda>\<^sub>a \<le> C"
proof (cases "n > 1")
  case True
  have "\<bar>g_inner f (g_step f)\<bar> / g_inner f f \<le> C" if "f \<in> \<Lambda>_test" for f
  proof -
    have "\<bar>g_inner f (g_step f)\<bar> \<le> C*g_inner f f"
      using that \<Lambda>_test_def assms(2) unfolding g_norm_sq by auto
    moreover have "g_inner f f > 0"
      using that unfolding \<Lambda>_test_def g_norm_sq[symmetric] by auto
    ultimately show ?thesis 
      by (simp add:divide_simps)
  qed

  hence "(SUP f\<in>\<Lambda>_test. \<bar>g_inner f (g_step f)\<bar> / g_inner f f) \<le> C" 
    using \<Lambda>_test_ne[OF True] by (intro cSup_least) auto
  thus ?thesis using True unfolding \<Lambda>\<^sub>a_def by auto
next
  case False
  then show ?thesis using assms unfolding \<Lambda>\<^sub>a_def by simp
qed

lemma expander_intro:
  assumes "C \<ge> 0"
  assumes "\<And>f. g_inner f (\<lambda>_. 1)=0 \<Longrightarrow> \<bar>\<Sum>a \<in> arcs G. f(head G a) * f(tail G a)\<bar> \<le> C*g_norm f^2" 
  shows "\<Lambda>\<^sub>a \<le> C/d"
proof -
  have "\<bar>g_inner f (g_step f)\<bar> \<le> C / real d * (g_norm f)\<^sup>2" (is "?L \<le> ?R") 
    if "g_inner f (\<lambda>_. 1) = 0" for f
  proof -
    have "?L = \<bar>\<Sum>a\<in>arcs G. f (head G a) * f (tail G a)\<bar> / real d"
      unfolding g_inner_step_eq by simp
    also have "... \<le> C*g_norm f^2 / real d"
      by (intro divide_right_mono assms(2)[OF that]) auto
    also have "... = ?R" by simp
    finally show ?thesis by simp
  qed
  thus ?thesis
    by (intro expander_intro_1 divide_nonneg_nonneg assms) auto
qed

lemma expansionD1:
  assumes "g_inner f (\<lambda>_. 1) = 0"
  shows "\<bar>g_inner f (g_step f)\<bar> \<le> \<Lambda>\<^sub>a * g_norm f^2"  (is "?L \<le> ?R")
proof (cases "g_norm f \<noteq> 0")
  case True

  have 0:"f \<in> \<Lambda>_test"
    unfolding \<Lambda>_test_def using assms True by auto

  hence 1:"n > 1" 
    using \<Lambda>_test_empty n_gt_0 by fastforce

  have "\<bar>g_inner f (g_step f)\<bar>/ g_norm f^2 = \<bar>g_inner f (g_step f)\<bar>/g_inner f f" 
    unfolding g_norm_sq by simp
  also have "... \<le> (SUP f\<in>\<Lambda>_test. \<bar>g_inner f (g_step f)\<bar> / g_inner f f)"
    by (intro cSup_upper bdd_above_\<Lambda> imageI 0) 
  also have "... = \<Lambda>\<^sub>a"
    using 1 unfolding \<Lambda>\<^sub>a_def by simp
  finally have "\<bar>g_inner f (g_step f)\<bar>/ g_norm f^2 \<le> \<Lambda>\<^sub>a" by simp
  thus ?thesis 
    using True by (simp add:divide_simps)
next
  case False
  hence "g_inner f f = 0"
    unfolding g_norm_sq[symmetric] by simp
  hence 0:"\<And>v. v \<in> verts G \<Longrightarrow> f v = 0"
    unfolding g_inner_def by (subst (asm) sum_nonneg_eq_0_iff) auto
  hence "?L = 0"
    unfolding g_step_def g_inner_def by simp 
  also have "... \<le> \<Lambda>\<^sub>a * g_norm f^2"
    using False by simp
  finally show ?thesis by simp
qed

lemma expansionD:
  assumes "g_inner f (\<lambda>_. 1) = 0"
  shows "\<bar>\<Sum>a \<in> arcs G. f (head G a) * f (tail G a)\<bar> \<le> d * \<Lambda>\<^sub>a * g_norm f^2"  (is "?L \<le> ?R")
proof -
  have "?L = \<bar>g_inner f (g_step f) * d\<bar>"
    unfolding g_inner_step_eq using d_gt_0 by simp
  also have "... \<le> \<bar>g_inner f (g_step f)\<bar> * d"
    by (simp add:abs_mult)
  also have "... \<le> (\<Lambda>\<^sub>a * g_norm f^2) * d"
    by (intro expansionD1 mult_right_mono assms(1)) auto
  also have "... = ?R" by simp
  finally show ?thesis by simp
qed

definition edges_betw where "edges_betw S T = {a \<in> arcs G. tail G a \<in> S \<and> head G a \<in> T}"

text \<open>This parameter is the edge expansion. It is usually denoted by the symbol $h$ or $h(G)$ in
text books. Contrary to the previous definitions it doesn't have a spectral theoretic counter
part.\<close>

definition \<Lambda>\<^sub>e where "\<Lambda>\<^sub>e = (if n > 1 then
  (MIN S\<in>{S. S\<subseteq>verts G\<and>2*card S\<le>n\<and>S\<noteq>{}}. real (card (edges_betw S (-S)))/card S) else 0)"

lemma edge_expansionD:
  assumes "S \<subseteq> verts G" "2*card S \<le> n"
  shows "\<Lambda>\<^sub>e * card S \<le> real (card (edges_betw S (-S)))"
proof (cases "S \<noteq> {}")
  case True
  moreover have "finite S" 
    using finite_subset[OF assms(1)] by simp
  ultimately have "card S > 0" by auto
  hence 1: "real (card S) > 0" by simp
  hence 2: "n > 1" using assms(2) by simp

  let ?St = "{S. S \<subseteq> verts G \<and> 2 * card S \<le> n \<and> S \<noteq> {}}"

  have 0: "finite ?St"
    by (rule finite_subset[where B="Pow (verts G)"]) auto
  have "\<Lambda>\<^sub>e = (MIN S\<in>?St. real (card (edges_betw S (-S)))/card S)"
    using 2 unfolding \<Lambda>\<^sub>e_def by simp

  also have "... \<le> real (card (edges_betw S (-S))) / card S"
    using assms True by (intro Min_le finite_imageI imageI) auto
  finally have "\<Lambda>\<^sub>e \<le> real (card (edges_betw S (-S))) / card S" by simp
  thus ?thesis using 1 by (simp add:divide_simps)
next
  case False
  hence "card S = 0" by simp
  thus ?thesis by simp
qed

lemma edge_expansionI:
  fixes \<alpha> :: real
  assumes "n > 1"
  assumes "\<And>S. S \<subseteq> verts G \<Longrightarrow> 2*card S \<le> n \<Longrightarrow> S \<noteq> {} \<Longrightarrow> card (edges_betw S (-S)) \<ge> \<alpha> * card S" 
  shows "\<Lambda>\<^sub>e \<ge> \<alpha>"
proof -
  define St where "St = {S. S \<subseteq> verts G \<and> 2*card S \<le> n \<and> S \<noteq> {}}"
  have 0: "finite St"
    unfolding St_def
    by (rule finite_subset[where B="Pow (verts G)"]) auto 

  obtain v where v_def: "v \<in> verts G" using verts_non_empty by auto 

  have "{v} \<in> St" 
    using assms v_def unfolding St_def n_def by auto
  hence 1: "St \<noteq> {}" by auto

  have 2: "\<alpha> \<le> real (card (edges_betw S (- S))) / real (card S)" if "S \<in> St" for S 
  proof -
    have "real (card (edges_betw S (- S)))  \<ge> \<alpha> * card S" 
      using assms(2) that unfolding St_def by simp
    moreover have "finite S" 
      using that unfolding St_def
      by (intro finite_subset[OF _ finite_verts]) auto
    hence "card S > 0" 
      using that unfolding St_def by auto
    ultimately show ?thesis 
      by (simp add:divide_simps)
  qed

  have "\<alpha> \<le> (MIN S\<in>St. real (card (edges_betw S (- S))) / real (card S))"
    using 0 1 2
    by (intro Min.boundedI finite_imageI) auto

  thus ?thesis
    unfolding \<Lambda>\<^sub>e_def St_def[symmetric] using assms by auto 
qed

end

lemma regular_graphI:
  assumes "symmetric_multi_graph G"
  assumes "verts G \<noteq> {}" "d > 0"
  assumes "\<And>v. v \<in> verts G \<Longrightarrow> out_degree G v = d"
  shows "regular_graph G"
proof -
  obtain v where v_def: "v \<in> verts G"
    using assms(2) by auto
  have "arcs G \<noteq> {}" 
  proof (rule ccontr)
    assume "\<not>arcs G \<noteq> {}"
    hence "arcs G = {}" by simp
    hence "out_degree G v = 0"
      unfolding out_degree_def out_arcs_def by simp
    hence "d = 0"
      using v_def assms(4) by simp
    thus False
      using assms(3) by simp
  qed

  thus ?thesis
    using assms symmetric_multi_graphD2[OF assms(1)]
    unfolding regular_graph_def regular_graph_axioms_def
    by simp
qed

text \<open>The following theorems verify that a graph isomorphisms preserve symmetry, regularity and all
the expansion coefficients.\<close>

lemma (in fin_digraph) symmetric_graph_iso:
  assumes "digraph_iso G H"
  assumes "symmetric_multi_graph G"
  shows "symmetric_multi_graph H"
proof -
  obtain h where hom_iso: "digraph_isomorphism h" and H_alt: "H = app_iso h G"
    using assms unfolding digraph_iso_def by auto

  have 0:"fin_digraph H"
    unfolding H_alt
    by (intro fin_digraphI_app_iso hom_iso)

  interpret H:fin_digraph H
    using 0 by auto

  have 1:"arcs_betw H (iso_verts h v) (iso_verts h w) = iso_arcs h ` arcs_betw G v w"
    (is "?L = ?R") if "v \<in> verts G" "w \<in> verts G" for v w
  proof -
    have "?L = {a \<in> iso_arcs h ` arcs G. iso_head h a=iso_verts h w \<and> iso_tail h a=iso_verts h v}"
      unfolding arcs_betw_def H_alt arcs_app_iso head_app_iso tail_app_iso by simp
    also have "... = {a. (\<exists>b \<in> arcs G. a = iso_arcs h b \<and> iso_verts h (head G b) = iso_verts h w \<and> 
      iso_verts h (tail G b) = iso_verts h v)}"
      using iso_verts_head[OF hom_iso] iso_verts_tail[OF hom_iso] by auto
    also have "... = {a. (\<exists>b \<in> arcs G. a = iso_arcs h b \<and> head G b = w \<and> tail G b = v)}" 
      using that iso_verts_eq_iff[OF hom_iso] by auto
    also have "... = ?R"
      unfolding arcs_betw_def by (auto simp add:image_iff set_eq_iff)
    finally show ?thesis by simp
  qed

  have "card (arcs_betw H w v) = card (arcs_betw H v w)" (is "?L = ?R") 
    if v_range: "v \<in> verts H" and w_range: "w \<in> verts H" for v w
  proof -
    obtain v' where v': "v = iso_verts h v'" "v' \<in> verts G"
      using that v_range verts_app_iso unfolding H_alt by auto
    obtain w' where w': "w = iso_verts h w'" "w' \<in> verts G"
      using that w_range verts_app_iso unfolding H_alt by auto
    have "?L = card (arcs_betw H (iso_verts h w') (iso_verts h v'))"
      unfolding v' w' by simp
    also have "... = card (iso_arcs h ` arcs_betw G w' v')"
      by (intro arg_cong[where f="card"] 1 v' w')
    also have "... = card (arcs_betw G w' v')"
      using iso_arcs_eq_iff[OF hom_iso] unfolding arcs_betw_def
      by (intro card_image inj_onI) auto
    also have "... = card (arcs_betw G v' w')"
      by (intro symmetric_multi_graphD4 assms(2)) 
    also have "... = card (iso_arcs h ` arcs_betw G v' w')"
      using iso_arcs_eq_iff[OF hom_iso] unfolding arcs_betw_def
      by (intro card_image[symmetric] inj_onI) auto
    also have "... = card (arcs_betw H (iso_verts h v') (iso_verts h w'))"
      by (intro arg_cong[where f="card"] 1[symmetric] v' w')
    also have "... = ?R"
      unfolding v' w' by simp
    finally show ?thesis by simp
  qed

  thus ?thesis
    using 0 unfolding symmetric_multi_graph_def by auto
qed

lemma (in regular_graph)
  assumes "digraph_iso G H"
  shows regular_graph_iso: "regular_graph H" 
    and regular_graph_iso_size: "regular_graph.n H = n"
    and regular_graph_iso_degree: "regular_graph.d H = d"
    and regular_graph_iso_expansion_le:  "regular_graph.\<Lambda>\<^sub>a H \<le> \<Lambda>\<^sub>a"
    and regular_graph_iso_os_expansion_le: "regular_graph.\<Lambda>\<^sub>2 H \<le> \<Lambda>\<^sub>2"
    and regular_graph_iso_edge_expansion_ge: "regular_graph.\<Lambda>\<^sub>e H \<ge> \<Lambda>\<^sub>e"
proof -
  obtain h where hom_iso: "digraph_isomorphism h" and H_alt: "H = app_iso h G"
    using assms unfolding digraph_iso_def by auto

  have 0:"symmetric_multi_graph H"
    by (intro symmetric_graph_iso[OF assms(1)] sym)

  have 1:"verts H \<noteq> {}" 
    unfolding H_alt verts_app_iso using verts_non_empty by simp

  then obtain h_wit where h_wit: "h_wit \<in> verts H"
    by auto

  have 3:"out_degree H v = d" if v_range: "v \<in> verts H" for v
  proof -
    obtain v' where v': "v = iso_verts h v'" "v' \<in> verts G"
      using that v_range verts_app_iso unfolding H_alt by auto
    have "out_degree H v = out_degree G v'"
      unfolding v' H_alt by (intro out_degree_app_iso_eq[OF hom_iso] v')
    also have "... = d"
      by (intro reg v')
    finally  show ?thesis by simp
  qed

  thus 2:"regular_graph H"
    by (intro regular_graphI[where d="d"] 0 d_gt_0 1) auto
  interpret H:"regular_graph" H
    using 2 by auto

  have "H.n = card (iso_verts h ` verts G)"
    unfolding H.n_def unfolding H_alt verts_app_iso by simp
  also have "... = card (verts G)"
    by (intro card_image digraph_isomorphism_inj_on_verts hom_iso) 
  also have "... = n"
    unfolding n_def by simp
  finally show n_eq: "H.n = n" by simp

  have "H.d = out_degree H h_wit"
    by (intro H.reg[symmetric] h_wit)
  also have "... = d"
    by (intro 3 h_wit)
  finally show 4:"H.d = d" by simp

  have "bij_betw (iso_verts h) (verts G) (verts H)" 
    unfolding H_alt using hom_iso 
    by (simp add: bij_betw_def digraph_isomorphism_inj_on_verts)

  hence g_inner_conv: 
    "H.g_inner f g = g_inner (\<lambda>x. f (iso_verts h x)) (\<lambda>x. g (iso_verts h x))" 
    for f g :: "'c \<Rightarrow> real" 
    unfolding g_inner_def H.g_inner_def by (intro sum.reindex_bij_betw[symmetric])

  have g_step_conv:
    "H.g_step f (iso_verts h x) = g_step (\<lambda>x. f (iso_verts h x)) x" if "x \<in> verts G"
    for f :: "'c \<Rightarrow> real" and x 
  proof -
    have "inj_on (iso_arcs h) (in_arcs G x)" 
      using inj_on_subset[OF digraph_isomorphism_inj_on_arcs[OF hom_iso]] 
      by (simp add:in_arcs_def)
    moreover have "in_arcs H (iso_verts h x) = iso_arcs h ` in_arcs G x"
      unfolding H_alt by (intro in_arcs_app_iso_eq[OF hom_iso] that) 
    moreover have "tail H (iso_arcs h a) = iso_verts h (tail G a)" if "a \<in> in_arcs G x" for a 
      unfolding H_alt using that by (simp add: hom_iso iso_verts_tail)
    ultimately show ?thesis
      unfolding g_step_def H.g_step_def 
      by (intro_cong "[\<sigma>\<^sub>2(/), \<sigma>\<^sub>1 f, \<sigma>\<^sub>1 of_nat]" more: 4 sum.reindex_cong[where l="iso_arcs h"])
  qed

  show "H.\<Lambda>\<^sub>a \<le> \<Lambda>\<^sub>a"
    using expansionD1 by (intro H.expander_intro_1 \<Lambda>_ge_0) 
      (simp add:g_inner_conv g_step_conv H.g_norm_sq g_norm_sq cong:g_inner_cong)

  show "H.\<Lambda>\<^sub>2 \<le> \<Lambda>\<^sub>2"
  proof (cases "n > 1")
    case True
    hence "H.n  > 1"
      by (simp add:n_eq)
    thus ?thesis
      using os_expanderD by (intro H.os_expanderI) 
        (simp_all add:g_inner_conv g_step_conv H.g_norm_sq g_norm_sq cong:g_inner_cong)
  next 
    case False
    thus ?thesis
      unfolding H.\<Lambda>\<^sub>2_def \<Lambda>\<^sub>2_def by (simp add:n_eq)
  qed

  show "H.\<Lambda>\<^sub>e \<ge> \<Lambda>\<^sub>e"
  proof (cases "n > 1")
    case True
    hence n_gt_1: "H.n  > 1"
      by (simp add:n_eq)
    have "\<Lambda>\<^sub>e * real (card S) \<le> real (card (H.edges_betw S (- S)))" 
      if "S \<subseteq> verts H" "2 * card S \<le> H.n" "S \<noteq> {}" for S 
    proof -
      define T where "T = iso_verts h -` S \<inter> verts G"
      have 4:"card T = card S"
        using that(1) unfolding T_def H_alt verts_app_iso
        by (intro card_vimage_inj_on digraph_isomorphism_inj_on_verts[OF hom_iso]) auto

      have "card (H.edges_betw S (-S))=card {a\<in>iso_arcs h`arcs G. iso_tail h a\<in>S\<and>iso_head h a\<in> -S}"
        unfolding H.edges_betw_def unfolding H_alt tail_app_iso head_app_iso arcs_app_iso
        by simp
      also have "...=
        card(iso_arcs h` {a \<in> arcs G. iso_tail h (iso_arcs h a)\<in>S\<and> iso_head h (iso_arcs h a)\<in>-S})"
        by (intro arg_cong[where f="card"]) auto
      also have "... = card {a \<in> arcs G. iso_tail h (iso_arcs h a)\<in>S\<and> iso_head h (iso_arcs h a)\<in>-S}"
        by (intro card_image inj_on_subset[OF digraph_isomorphism_inj_on_arcs[OF hom_iso]]) auto
      also have "... = card {a \<in> arcs G. iso_verts h (tail G a) \<in> S \<and> iso_verts h (head G a) \<in> -S}"
        by (intro restr_Collect_cong arg_cong[where f="card"])
         (simp add: iso_verts_tail[OF hom_iso] iso_verts_head[OF hom_iso])
      also have "... = card {a \<in> arcs G. tail G a \<in> T \<and> head G a \<in> -T }"
        unfolding T_def by (intro_cong "[\<sigma>\<^sub>1(card),\<sigma>\<^sub>2 (\<and>)]" more: restr_Collect_cong) auto
      also have "... = card (edges_betw T (-T))"
        unfolding edges_betw_def by simp
      finally have 5:"card (edges_betw T (-T)) = card (H.edges_betw S (-S))" 
        by simp

      have 6: "T \<subseteq> verts G" unfolding T_def by simp

      have "\<Lambda>\<^sub>e * real (card S) = \<Lambda>\<^sub>e * real (card T)"
        unfolding 4 by simp
      also have "... \<le> real (card (edges_betw T (-T)))"
        using that(2) by (intro edge_expansionD 6) (simp add:4 n_eq)
      also have "... = real (card (H.edges_betw S (-S)))"
        unfolding 5 by simp
      finally show ?thesis by simp
    qed

    thus ?thesis
      by (intro H.edge_expansionI n_gt_1) auto
  next
    case False
    thus ?thesis
      unfolding H.\<Lambda>\<^sub>e_def \<Lambda>\<^sub>e_def by (simp add:n_eq)
  qed

qed

lemma (in regular_graph)
  assumes "digraph_iso G H"
  shows regular_graph_iso_expansion: "regular_graph.\<Lambda>\<^sub>a H = \<Lambda>\<^sub>a"
    and regular_graph_iso_os_expansion: "regular_graph.\<Lambda>\<^sub>2 H = \<Lambda>\<^sub>2"
    and regular_graph_iso_edge_expansion: "regular_graph.\<Lambda>\<^sub>e H = \<Lambda>\<^sub>e"
proof -
  interpret H:"regular_graph" "H"
    by (intro regular_graph_iso assms)

  have iso:"digraph_iso H G"
    using digraph_iso_swap assms wf_digraph_axioms by blast

  hence "\<Lambda>\<^sub>a \<le> H.\<Lambda>\<^sub>a"
    by (intro H.regular_graph_iso_expansion_le)
  moreover have "H.\<Lambda>\<^sub>a \<le> \<Lambda>\<^sub>a"
    using regular_graph_iso_expansion_le[OF assms] by auto
  ultimately show "H.\<Lambda>\<^sub>a = \<Lambda>\<^sub>a"
    by auto

  have "\<Lambda>\<^sub>2 \<le> H.\<Lambda>\<^sub>2" using iso
    by (intro H.regular_graph_iso_os_expansion_le)
  moreover have "H.\<Lambda>\<^sub>2 \<le> \<Lambda>\<^sub>2"
    using regular_graph_iso_os_expansion_le[OF assms] by auto
  ultimately show "H.\<Lambda>\<^sub>2 = \<Lambda>\<^sub>2"
    by auto

  have "\<Lambda>\<^sub>e \<ge> H.\<Lambda>\<^sub>e" using iso
    by (intro H.regular_graph_iso_edge_expansion_ge)
  moreover have "H.\<Lambda>\<^sub>e \<ge> \<Lambda>\<^sub>e"
    using regular_graph_iso_edge_expansion_ge[OF assms] by auto
  ultimately show "H.\<Lambda>\<^sub>e = \<Lambda>\<^sub>e"
    by auto
qed

unbundle no_intro_cong_syntax

end
