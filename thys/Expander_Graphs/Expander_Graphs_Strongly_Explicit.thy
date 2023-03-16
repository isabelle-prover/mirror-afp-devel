section \<open>Strongly Explicit Expander Graphs\label{sec:see}\<close>

text \<open>In some applications, representing an expander graph using a data structure (for example
as an adjacency lists) would be prohibitive. For such cases strongly explicit expander graphs (SEE) 
are relevant. These are expander graphs, which can be represented implicitly using a function that 
computes for each vertex its neighbors in space and time logarithmic w.r.t. to the size of the 
graph. An application can for example sample a random walk, from a SEE using such a function 
efficiently. An example of such a graph is the Margulis construction from 
Section~\ref{sec:margulis}. This section presents the latter as a SEE but also shows that two graph
operations that preserve the SEE property, in particular the graph power construction from 
Section~\ref{sec:graph_power} and a compression scheme introduced by 
Murtagh et al.~\cite[Theorem~20]{murtagh2019}. Combining all of the above it is possible to construct 
strongly explicit expander graphs of \emph{every size} and spectral gap, which is formalized in 
Subsection~\ref{sec:see_standard}.\<close>

theory Expander_Graphs_Strongly_Explicit
  imports Expander_Graphs_Power_Construction Expander_Graphs_MGG
begin

unbundle intro_cong_syntax
no_notation Digraph.dominates ("_ \<rightarrow>\<index> _" [100,100] 40)

record strongly_explicit_expander =
  see_size :: nat
  see_degree :: nat
  see_step :: "nat \<Rightarrow> nat \<Rightarrow> nat"

definition graph_of :: "strongly_explicit_expander \<Rightarrow> (nat, (nat,nat) arc) pre_digraph"
  where "graph_of e = 
    \<lparr> verts = {..<see_size e}, 
      arcs = (\<lambda>(v, i). Arc v (see_step e i v) i) ` ({..<see_size e} \<times> {..<see_degree e}),
      tail = arc_tail,
      head = arc_head \<rparr>"

definition "is_expander e \<Lambda>\<^sub>a \<longleftrightarrow>
  regular_graph (graph_of e) \<and> regular_graph.\<Lambda>\<^sub>a (graph_of e) \<le> \<Lambda>\<^sub>a"

lemma is_expander_mono:
  assumes "is_expander e a" "a \<le> b"
  shows "is_expander e b"
  using assms unfolding is_expander_def by auto

lemma graph_of_finI:
  assumes "see_step e \<in> ({..<see_degree e} \<rightarrow> ({..<see_size e} \<rightarrow> {..<see_size e}))"
  shows "fin_digraph (graph_of e)"
proof -
  let ?G = "graph_of e"

  have "head ?G a \<in> verts ?G \<and> tail ?G a \<in> verts ?G" if "a \<in> arcs ?G" for a 
    using assms that unfolding graph_of_def by (auto simp add:Pi_def)

  hence 0: "wf_digraph ?G"
    unfolding wf_digraph_def by auto

  have 1: "finite (verts ?G)" 
    unfolding graph_of_def by simp

  have 2: "finite (arcs ?G)" 
    unfolding graph_of_def by simp
  show ?thesis
    using 0 1 2 unfolding fin_digraph_def fin_digraph_axioms_def by  auto
qed

lemma edges_graph_of:
  "edges(graph_of e)={#(v,see_step e i v). (v,i)\<in>#mset_set ({..<see_size e}\<times>{..<see_degree e})#}"
proof -
  have 0:"mset_set ((\<lambda>(v, i). Arc v (see_step e i v) i) ` ({..<see_size e} \<times> {..<see_degree e}))
    = {# Arc v (see_step e i v) i. (v,i) \<in># mset_set ( {..<see_size e} \<times> {..<see_degree e})#}"
    by (intro image_mset_mset_set[symmetric] inj_onI) auto

  have "edges (graph_of e) = 
    {#(fst p, see_step e (snd p) (fst p)). p \<in># mset_set ({..<see_size e} \<times> {..<see_degree e})#}"
    unfolding edges_def graph_of_def arc_to_ends_def using 0 
    by (simp add:image_mset.compositionality comp_def case_prod_beta)
  also have "... = {#(v, see_step e i v). (v,i) \<in># mset_set ({..<see_size e} \<times> {..<see_degree e})#}"
    by (intro image_mset_cong) auto
  finally show ?thesis by simp
qed

lemma out_degree_see:
  assumes "v \<in> verts (graph_of e)"
  shows "out_degree (graph_of e) v = see_degree e" (is "?L = ?R")
proof -
  let ?d = "see_degree e"
  let ?n = "see_size e"
  have 0: "v < ?n" 
    using assms unfolding graph_of_def by simp

  have "?L = card {a. (\<exists>x\<in>{..<?n}. \<exists>y\<in>{..<?d}. a = Arc x (see_step e y x) y) \<and> arc_tail a = v}"
    unfolding out_degree_def out_arcs_def graph_of_def by (simp add:image_iff)
  also have "... = card {a. (\<exists>y\<in>{..<?d}. a = Arc v (see_step e y v) y)}"
    using 0 by (intro arg_cong[where f="card"]) auto
  also have "... = card ((\<lambda>y. Arc v (see_step e y v) y) ` {..<?d})"
    by (intro arg_cong[where f="card"] iffD2[OF set_eq_iff]) (simp add:image_iff)
  also have "... = card {..<?d}"
    by (intro card_image inj_onI) auto
  also have "... = ?d" by simp
  finally show ?thesis by simp
qed

lemma card_arc_walks_see:
  assumes "fin_digraph (graph_of e)"
  shows "card (arc_walks (graph_of e) n) = see_degree e^n * see_size e" (is "?L = ?R")
proof -
  let ?G = "graph_of e"
  interpret fin_digraph ?G
    using assms by auto
  have "?L = card (\<Union>v \<in> verts ?G. {x. fst x = v \<and> is_arc_walk ?G v (snd x) \<and> length (snd x) = n})"
    unfolding arc_walks_def by (intro arg_cong[where f="card"]) auto
  also have "... = (\<Sum>v \<in> verts ?G. card {x. fst x=v\<and>is_arc_walk ?G v (snd x)\<and>length (snd x) = n})"
    using is_arc_walk_set[where G="?G"]
    by (intro card_UN_disjoint ballI finite_cartesian_product subsetI finite_lists_length_eq
        finite_subset[where B="verts ?G \<times> {x. set x \<subseteq> arcs ?G \<and> length x = n}"]) force+
  also have "... = (\<Sum>v \<in> verts ?G. out_degree (graph_power ?G n) v)"
    unfolding out_degree_def graph_power_def out_arcs_def arc_walks_def 
    by (intro sum.cong arg_cong[where f="card"]) auto
  also have "... = (\<Sum>v \<in> verts ?G. see_degree e^n)"
    by (intro sum.cong graph_power_out_degree' out_degree_see refl) (simp_all add: graph_power_def)
  also have "... = ?R"
    by (simp add:graph_of_def)
  finally show ?thesis by simp
qed

lemma regular_graph_degree_eq_see_degree:
  assumes "regular_graph (graph_of e)"
  shows "regular_graph.d (graph_of e) = see_degree e" (is "?L = ?R")
proof -
  interpret regular_graph "graph_of e"
    using assms(1) by simp
  obtain v where v_set: "v \<in> verts (graph_of e)"
    using verts_non_empty by auto
  hence "?L = out_degree (graph_of e) v" 
    using v_set reg by auto
  also have "... = see_degree e"
    by (intro out_degree_see v_set)
  finally show ?thesis by simp
qed

text \<open>The following introduces the compression scheme, described in \cite[Theorem 20]{murtagh2019}.\<close>

fun see_compress :: "nat \<Rightarrow> strongly_explicit_expander \<Rightarrow> strongly_explicit_expander"
  where "see_compress m e = 
    \<lparr> see_size = m, see_degree = see_degree e * 2
    , see_step = (\<lambda>k v. 
      if k < see_degree e 
        then (see_step e k v) mod m 
        else (if v+m < see_size e then (see_step e (k-see_degree e) (v+m)) mod m else v)) \<rparr>"

lemma edges_of_compress:
  fixes e m
  assumes "2*m \<ge> see_size e" "m \<le> see_size e"
  defines "A \<equiv> {# (x mod m, y mod m). (x,y) \<in># edges (graph_of e)#}"
  defines "B \<equiv> repeat_mset (see_degree e) {# (x,x). x \<in># (mset_set {see_size e - m..<m})#}"
  shows "edges (graph_of (see_compress m e)) = A + B" (is "?L = ?R")
proof -
  let ?d = "see_degree e"
  let ?c = "see_step (see_compress m e)"
  let ?n = "see_size e"
  let ?s = "see_step e"

  have 7:"m \<le> v \<Longrightarrow> v < ?n \<Longrightarrow> v - m = v mod m" for v
    using assms by (simp add: le_mod_geq)

  let ?M = "mset_set ({..<m}\<times>{..<2*?d})"
  define M1 where "M1 = mset_set ({..<m} \<times> {..<?d})"
  define M2 where "M2 = mset_set ({..<?n-m} \<times> {?d..<2*?d})"
  define M3 where "M3 = mset_set ({?n-m..<m} \<times> {?d..<2*?d})"

  have "M2 = mset_set ((\<lambda>(x,y). (x-m,y+?d)) ` ({m..<?n} \<times> {..<?d}))"
    using assms(2) unfolding M2_def map_prod_def[symmetric] atLeast0LessThan[symmetric] 
    by (intro arg_cong[where f="mset_set"] map_prod_surj_on[symmetric])
      (simp_all add:  image_minus_const_atLeastLessThan_nat mult_2)
  also have "... = image_mset (\<lambda>(x,y). (x-m,y+?d)) (mset_set ({m..<?n} \<times> {..<?d}))"
    by (intro image_mset_mset_set[symmetric] inj_onI) auto
  finally have M2_eq: "M2 = image_mset (\<lambda>(x,y). (x-m,y+?d)) (mset_set ({m..<?n} \<times> {..<?d}))"
    by simp

  have "?M = mset_set ({..<m}\<times>{..<?d} \<union> {..<?n-m}\<times>{?d..<2*?d} \<union> {?n-m..<m}\<times>{?d..<2*?d})"
    using assms(1,2) by (intro arg_cong[where f="mset_set"]) auto
  also have "... = mset_set ({..<m}\<times>{..<?d} \<union> {..<?n-m}\<times>{?d..<2*?d}) + M3"
    unfolding M3_def by (intro mset_set_Union) auto
  also have "... = M1 + M2 + M3"
    unfolding M1_def M2_def
    by (intro arg_cong2[where f="(+)"] mset_set_Union) auto
  finally have 0:"mset_set ({..<m} \<times> {..<2*?d}) = M1 + M2 + M3" by simp

  have 1:"{#(v,?c i v). (v,i)\<in>#M1#}={#(v mod m,?s i v mod m). (v,i)\<in>#mset_set ({..<m}\<times>{..<?d})#}"
    unfolding M1_def by (intro image_mset_cong) auto

  have "{#(v,?c i v).(v,i)\<in>#M2#}={#(fst x-m,?c(snd x+?d)(fst x-m)).x\<in>#mset_set({m..<?n}\<times>{..<?d})#}"
    unfolding M2_eq 
    by (simp add:image_mset.compositionality comp_def case_prod_beta del:see_compress.simps)
  also have "... = {#(v - m,?s i v mod m). (v,i)\<in>#mset_set ({m..<?n}\<times>{..<?d})#}"
    by (intro image_mset_cong) auto 
  also have "... = {#(v mod m,?s i v mod m). (v,i)\<in>#mset_set ({m..<?n}\<times>{..<?d})#}"
    using 7 by (intro image_mset_cong) auto 
  finally have 2:
    "{#(v,?c i v). (v,i)\<in>#M2#}={#(v mod m,?s i v mod m). (v,i)\<in>#mset_set ({m..<?n}\<times>{..<?d})#}"
    by simp

  have "{#(v,?c i v). (v,i)\<in>#M3#} = {#(v,v). (v,i) \<in>#  mset_set ({?n-m..<m} \<times> {?d..<2*?d})#}"
    unfolding M3_def by (intro image_mset_cong) auto
  also have "... = concat_mset {#{#(x, x). xa \<in># mset_set {?d..<2 * ?d}#}. x \<in># mset_set {?n - m..<m}#}"
    by (subst mset_prod_eq) (auto simp:image_mset.compositionality image_concat_mset comp_def)
  also have "... = concat_mset {#replicate_mset ?d (x, x). x \<in># mset_set {?n - m..<m}#}"
    unfolding image_mset_const_eq by simp
  also have "... = B"
    unfolding B_def repeat_image_concat_mset by simp
  finally have 3:"{#(v,?c i v). (v,i)\<in>#M3#}=B" by simp

  have "A = {#(fst x mod m, ?s (snd x) (fst x) mod m). x \<in># mset_set ({..<?n} \<times> {..<?d})#}"
    unfolding A_def edges_graph_of by (simp add:image_mset.compositionality comp_def case_prod_beta)
  also have "... = {#(v mod m,?s i v mod m). (v,i)\<in>#mset_set({..<?n}\<times>{..<?d})#}"
    by (intro image_mset_cong) auto
  finally have 4: "A = {#(v mod m,?s i v mod m). (v,i)\<in>#mset_set({..<?n}\<times>{..<?d})#}"
    by simp

  have "?L = {# (v, ?c i v). (v,i) \<in># ?M #}"
    unfolding edges_graph_of by (simp add:ac_simps)
  also have "... = {#(v,?c i v). (v,i)\<in>#M1#}+{#(v,?c i v). (v,i)\<in>#M2#}+{#(v,?c i v). (v,i)\<in>#M3#}"
    unfolding 0 image_mset_union by simp
  also have "...={#(v mod m,?s i v mod m). (v,i)\<in>#mset_set({..<m}\<times>{..<?d}\<union>{m..<?n}\<times>{..<?d})#}+B"
    unfolding 1 2 3 image_mset_union[symmetric]
    by (intro_cong "[\<sigma>\<^sub>2 (+), \<sigma>\<^sub>2 image_mset]" more: mset_set_Union[symmetric]) auto
  also have "...={#(v mod m,?s i v mod m). (v,i)\<in>#mset_set({..<?n}\<times>{..<?d})#}+B"
    using assms(2) by (intro_cong "[\<sigma>\<^sub>2 (+), \<sigma>\<^sub>2 image_mset, \<sigma>\<^sub>1 mset_set]") auto
  also have "... = A + B"
    unfolding 4 by simp
  finally show ?thesis by simp
qed

lemma see_compress_sym:
  assumes "2*m \<ge> see_size e" "m \<le> see_size e"
  assumes "symmetric_multi_graph (graph_of e)"
  shows "symmetric_multi_graph (graph_of (see_compress m e))"
proof -
  let ?c = "see_compress m e"
  let ?d = "see_degree e"
  let ?G = "graph_of e"
  let ?H = "graph_of (see_compress m e)"

  interpret G:"fin_digraph" "?G"
    by (intro symmetric_multi_graphD2[OF assms(3)]) 
  interpret H:"fin_digraph" "?H"
    by (intro graph_of_finI) simp

  have deg_compres: "see_degree ?c = 2 * see_degree e"
    by simp

  have 1: "card (arcs_betw ?H v w) = card (arcs_betw ?H w v)" (is "?L = ?R") 
    if "v \<in> verts ?H" "w \<in> verts ?H" for v w 
  proof -
    define b where "b =count {#(x, x). x \<in># mset_set {see_size e - m..<m}#} (v, w)"

    have b_alt_def: "b = count {#(x, x). x \<in># mset_set {see_size e - m..<m}#} (w, v)"
      unfolding b_def count_mset_exp
      by (simp add:case_prod_beta image_mset_filter_mset_swap[symmetric] ac_simps)

    have "?L = count (edges ?H) (v,w)"
      unfolding H.count_edges by simp
    also have "... = count {#(x mod m, y mod m). (x, y) \<in># edges (graph_of e)#} (v, w) + ?d * b"
      unfolding edges_of_compress[OF assms(1,2)] b_def by simp
    also have "... = count {#(snd e mod m, fst e mod m). e \<in># edges (graph_of e)#} (v, w) + ?d * b"
      by (subst G.edges_sym[OF assms(3),symmetric])
        (simp add:image_mset.compositionality comp_def case_prod_beta)
    also have "... = count {#(x mod m, y mod m). (x,y) \<in># edges (graph_of e)#} (w, v) + ?d * b"
      unfolding count_mset_exp 
      by (simp add:image_mset_filter_mset_swap[symmetric] ac_simps case_prod_beta)
    also have "... = count (edges ?H) (w,v)"
      unfolding edges_of_compress[OF assms(1,2)] b_alt_def by simp
    also have "... = ?R" 
      unfolding H.count_edges by simp
    finally show ?thesis by simp
  qed

  show ?thesis
    using 1 H.fin_digraph_axioms
    unfolding symmetric_multi_graph_def by auto
qed

lemma see_compress:
  assumes "is_expander e \<Lambda>\<^sub>a"
  assumes "2*m \<ge> see_size e" "m \<le> see_size e"
  shows "is_expander (see_compress m e) (\<Lambda>\<^sub>a/2 + 1/2)"
proof -
  let ?H = "graph_of (see_compress m e)"
  let ?G = "graph_of e"
  let ?d = "see_degree e"
  let ?n = "see_size e"

  interpret G:regular_graph "graph_of e" 
    using assms(1) is_expander_def by simp

  have d_eq: "?d = G.d"
    using regular_graph_degree_eq_see_degree[OF G.regular_graph_axioms] by simp

  have n_eq: "G.n = ?n"
    unfolding G.n_def by (simp add:graph_of_def)

  have n_gt_1: "?n > 0"
    using G.n_gt_0 n_eq by auto

  have "symmetric_multi_graph (graph_of (see_compress m e))"
    by (intro see_compress_sym assms(2,3) G.sym)
  moreover have "see_size e > 0" 
    using G.verts_non_empty unfolding graph_of_def by auto
  hence "m > 0" using assms(2) by simp
  hence "verts (graph_of (see_compress m e)) \<noteq> {}" 
    unfolding graph_of_def by auto
  moreover have 1:"0 < see_degree e" 
    using d_eq G.d_gt_0 by auto
  hence "0 < see_degree (see_compress m e)" by simp
  ultimately have 0:"regular_graph ?H"
    by (intro regular_graphI[where d="see_degree (see_compress m e)"] out_degree_see) auto
  interpret H:regular_graph ?H
    using 0 by auto

  have "\<bar>\<Sum>a\<in>arcs ?H. f (head ?H a) * f (tail ?H a)\<bar> \<le> (real G.d * G.\<Lambda>\<^sub>a + G.d) * (H.g_norm f)\<^sup>2" 
    (is "?L \<le> ?R") if "H.g_inner f (\<lambda>_. 1) = 0" for f
  proof -
    define f' where "f' x = f (x mod m)" for x
    let ?L1 = "G.g_norm f'^2 + \<bar>\<Sum>x=?n-m..<m. f x^2\<bar>"
    let ?L2 = "G.g_inner f' (\<lambda>_.1)^2/ G.n + \<bar>\<Sum>x=?n-m..<m. f x^2\<bar>"

    have "?L1 = (\<Sum>x<?n. f (x mod m)^2) + \<bar>\<Sum>x=?n-m..<m. f x^2\<bar>"
      unfolding G.g_norm_sq G.g_inner_def f'_def by (simp add:graph_of_def power2_eq_square)
    also have "... = (\<Sum>x\<in>{0..<m} \<union> {m..<?n}. f (x mod m)^2) + (\<Sum>x=?n-m..<m. f x^2)" 
      using assms(3) by (intro_cong "[\<sigma>\<^sub>2 (+)]" more:sum.cong abs_of_nonneg sum_nonneg) auto
    also have "...=(\<Sum>x=0..<m. f (x mod m)^2) + (\<Sum>x=m..<?n. f (x mod m)^2) + (\<Sum>x=?n-m..<m. f x^2)"
      by (intro_cong "[\<sigma>\<^sub>2 (+)]" more:sum.union_disjoint) auto
    also have "...  = (\<Sum>x=0..<m. f (x mod m)^2) + (\<Sum>x=0..<?n-m. f x^2) + (\<Sum>x=?n-m..<m. f x^2)"
      using assms(2,3)
      by (intro_cong "[\<sigma>\<^sub>2 (+)]" more: sum.reindex_bij_betw bij_betwI[where g="(\<lambda>x. x+m)"])
       (auto simp add:le_mod_geq)
    also have "... = (\<Sum>x=0..<m. f x^2) + (\<Sum>x=0..<?n-m. f x^2) + (\<Sum>x=?n-m..<m. f x^2)"
      by (intro sum.cong arg_cong2[where f="(+)"]) auto
    also have "... = (\<Sum>x=0..<m. f x^2) + ((\<Sum>x=0..<?n-m. f x^2) + (\<Sum>x=?n-m..<m. f x^2))"
      by simp
    also have "... = (\<Sum>x=0..<m. f x^2) + (\<Sum>x\<in>{0..<?n-m}\<union>{?n-m..<m}. f x^2)"
      by (intro sum.union_disjoint[symmetric] arg_cong2[where f="(+)"]) auto
    also have "... = (\<Sum>x<m. f x^2) + (\<Sum>x<m. f x^2)"
      using assms(2,3) by (intro arg_cong2[where f="(+)"] sum.cong) auto
    also have " ... = 2 * H.g_norm f^2"
      unfolding mult_2 H.g_norm_sq H.g_inner_def by (simp add:graph_of_def power2_eq_square)
    finally have 2:"?L1 = 2 * H.g_norm f^2" by simp

    have "?L2 = (\<Sum>x\<in>{..<m}\<union>{m..<?n}. f (x mod m))^2/G.n + (\<Sum>x=?n-m..<m. f x^2)"
      unfolding G.g_inner_def f'_def using assms(2,3)
      by (intro_cong "[\<sigma>\<^sub>2 (+), \<sigma>\<^sub>2 (/), \<sigma>\<^sub>2 (power)]" more: sum.cong abs_of_nonneg sum_nonneg)
       (auto simp add:graph_of_def)
    also have "...=((\<Sum>x<m. f (x mod m))+(\<Sum>x=m..<?n. f (x mod m)))^2/G.n + (\<Sum>x=?n-m..<m. f x^2)"
      by (intro_cong "[\<sigma>\<^sub>2 (+), \<sigma>\<^sub>2 (/), \<sigma>\<^sub>2 (power)]" more:sum.union_disjoint) auto
    also have "...=((\<Sum>x<m. f (x mod m))+(\<Sum>x=0..<?n-m. f x))^2/G.n + (\<Sum>x=?n-m..<m. f x^2)"
      using assms(2,3) by (intro_cong "[\<sigma>\<^sub>2 (+), \<sigma>\<^sub>2 (/), \<sigma>\<^sub>2 (power)]" 
          more:sum.reindex_bij_betw bij_betwI[where g="(\<lambda>x. x+m)"]) (auto simp add:le_mod_geq)
    also have "...=(H.g_inner f (\<lambda>_. 1) +(\<Sum>x<?n-m. f x))^2/G.n + (\<Sum>x=?n-m..<m. f x^2)"
      unfolding H.g_inner_def
      by (intro_cong "[\<sigma>\<^sub>2 (+), \<sigma>\<^sub>2 (/), \<sigma>\<^sub>2 (power)]" more: sum.cong) (auto simp:graph_of_def) 
    also have "...=(\<Sum>x<?n-m. f x)^2/G.n + (\<Sum>x=?n-m..<m. f x^2)"
      unfolding that by simp
    also have "...\<le> (\<Sum>x<?n-m. \<bar>f x\<bar> * \<bar>1\<bar>)^2/G.n + (\<Sum>x=?n-m..<m. f x^2)"
      by (intro add_mono divide_right_mono iffD1[OF abs_le_square_iff]) auto
    also have "... \<le> (L2_set f {..<?n-m} * L2_set (\<lambda>_. 1) {..<?n-m})^2/G.n + (\<Sum>x=?n-m..<m. f x^2)"
      by (intro add_mono divide_right_mono power_mono L2_set_mult_ineq sum_nonneg) auto
    also have "... = ((\<Sum>x <?n-m. f x^2) * (?n-m))/G.n + (\<Sum>x=?n-m..<m. f x^2)"
      unfolding power_mult_distrib L2_set_def real_sqrt_mult
      by (intro_cong "[\<sigma>\<^sub>2 (+), \<sigma>\<^sub>2 (/),\<sigma>\<^sub>2 (*)]" more:real_sqrt_pow2 sum_nonneg) auto
    also have "... = (\<Sum>x <?n-m. f x^2) * ((?n-m)/?n) + (\<Sum>x=?n-m..<m. f x^2)"
      unfolding n_eq by simp
    also have "... \<le> (\<Sum>x <?n-m. f x^2) * 1 + (\<Sum>x=?n-m..<m. f x^2)"
      using assms(3) n_gt_1 by (intro mult_left_mono add_mono sum_nonneg) auto
    also have "... = (\<Sum>x\<in>{..<?n-m}\<union>{?n-m..<m}. f x^2)"
      unfolding mult_1_right by (intro sum.union_disjoint[symmetric]) auto
    also have "... = H.g_norm f^2"
      using assms(2,3) unfolding H.g_norm_sq H.g_inner_def 
      by (intro sum.cong) (auto simp add:graph_of_def power2_eq_square)
    finally have 3:"?L2 \<le> H.g_norm f^2" by simp

    have "?L = \<bar>\<Sum>(u, v)\<in>#edges ?H. f v * f u\<bar>"
      unfolding edges_def arc_to_ends_def sum_unfold_sum_mset 
      by (simp add:image_mset.compositionality comp_def del:see_compress.simps)
    also have "...=\<bar>(\<Sum>x \<in># edges ?G.f(snd x mod m)*f(fst x mod m))+(\<Sum>x=?n-m..<m.?d*(f x^2))\<bar>"
      unfolding edges_of_compress[OF assms(2,3)]  sum_unfold_sum_mset 
      by (simp add:image_mset.compositionality sum_mset_repeat comp_def 
          case_prod_beta power2_eq_square del:see_compress.simps)
    also have "...=\<bar>(\<Sum>(u,v) \<in># edges ?G.f(u mod m)*f(v mod m))+(\<Sum>x=?n-m..<m.?d*(f x^2))\<bar>"
      by (intro_cong "[\<sigma>\<^sub>1 abs, \<sigma>\<^sub>2 (+), \<sigma>\<^sub>1 sum_mset]" more:image_mset_cong)
       (simp_all add:case_prod_beta)
    also have "... \<le> \<bar>\<Sum>(u,v) \<in># edges ?G.f(u mod m)*f(v mod m)\<bar>+\<bar>\<Sum>x=?n-m..<m.?d*(f x^2)\<bar> "
      by (intro abs_triangle_ineq)
    also have "... = ?d * (\<bar>\<Sum>(u,v) \<in># edges ?G.f(v mod m)*f(u mod m)\<bar>/G.d+\<bar>\<Sum>x=?n-m..<m.(f x^2)\<bar>)"
      unfolding d_eq using G.d_gt_0 
      by (simp add:divide_simps ac_simps sum_distrib_left[symmetric] abs_mult)
    also have "... = ?d * (\<bar>G.g_inner f' (G.g_step f')\<bar> + \<bar>\<Sum>x=?n-m..<m. f x^2\<bar>)" 
      unfolding G.g_inner_step_eq sum_unfold_sum_mset edges_def arc_to_ends_def f'_def
      by (simp add:image_mset.compositionality comp_def del:see_compress.simps)
    also have "...\<le> ?d * ((G.\<Lambda>\<^sub>a * G.g_norm f'^2 + (1-G.\<Lambda>\<^sub>a)*G.g_inner f' (\<lambda>_.1)^2/ G.n)
      + \<bar>\<Sum>x=?n-m..<m. f x^2\<bar>)"
      by (intro add_mono G.expansionD3 mult_left_mono) auto
    also have "... = ?d * (G.\<Lambda>\<^sub>a * ?L1 + (1 - G.\<Lambda>\<^sub>a) * ?L2)"
      by (simp add:algebra_simps)
    also have "... \<le> ?d * (G.\<Lambda>\<^sub>a * (2 * H.g_norm f^2) + (1-G.\<Lambda>\<^sub>a) * H.g_norm f^2)"
      unfolding 2 using G.\<Lambda>_ge_0 G.\<Lambda>_le_1 by (intro mult_left_mono add_mono 3) auto
    also have "... = ?R"
      unfolding d_eq[symmetric] by (simp add:algebra_simps)
    finally show ?thesis by simp
  qed

  hence "H.\<Lambda>\<^sub>a \<le> (G.d*G.\<Lambda>\<^sub>a+G.d)/H.d"
    using G.d_gt_0 G.\<Lambda>_ge_0 by (intro H.expander_intro) (auto simp del:see_compress.simps)
  also have "... = (see_degree e * G.\<Lambda>\<^sub>a + see_degree e) / (2* see_degree e)"
    unfolding d_eq[symmetric] regular_graph_degree_eq_see_degree[OF H.regular_graph_axioms]
    by simp
  also have "... = G.\<Lambda>\<^sub>a/2 + 1/2"
    using 1 by (simp add:field_simps)
  also have "... \<le> \<Lambda>\<^sub>a/2 + 1/2"
    using assms(1) unfolding is_expander_def by simp
  finally have "H.\<Lambda>\<^sub>a \<le> \<Lambda>\<^sub>a/2 + 1/2" by simp
  thus ?thesis unfolding is_expander_def using 0 by simp
qed

text \<open>The graph power of a strongly explicit expander graph is itself a strongly explicit expander
graph.\<close>

fun to_digits :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list"
  where 
    "to_digits _ 0 _ = []" |
    "to_digits b (Suc l) k = (k mod b)# to_digits b l (k div b)"

fun from_digits :: "nat \<Rightarrow> nat list \<Rightarrow> nat"
  where
    "from_digits b [] = 0" |
    "from_digits b (x#xs) = x + b * from_digits b xs"

lemma to_from_digits:
  assumes "length xs = n" "set xs \<subseteq> {..<b}"
  shows "to_digits b n (from_digits b xs) = xs"
proof -
  have "to_digits b (length xs) (from_digits b xs) = xs"
    using assms(2) by (induction xs, auto) 
  thus ?thesis unfolding assms(1) by auto
qed

lemma from_digits_range:
  assumes "length xs = n" "set xs \<subseteq> {..<b}"
  shows "from_digits b xs < b^n"
proof (cases "b > 0")
  case True
  have "from_digits b xs \<le> b^length xs - 1"
    using assms(2) 
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    have "from_digits b (a # xs) =  a + b * from_digits b xs"
      by simp
    also have "... \<le> (b-1) + b * from_digits b xs"
      using Cons by (intro add_mono) auto
    also have "... \<le> (b-1) + b * (b^length xs-1)"
      using Cons(2) by (intro add_mono mult_left_mono Cons(1)) auto
    also have "... = b^length (a#xs) - 1"
      using True by (simp add:algebra_simps)
    finally show "from_digits b (a # xs) \<le> b^length (a#xs) - 1" by simp 
  qed
  also have "... < b^n"
    using True assms(1) by simp
  finally show ?thesis by simp
next 
  case False
  hence "b = 0" by simp
  hence "xs = []"
    using assms(2) by simp
  thus ?thesis using assms(1) by simp
qed

lemma from_digits_inj:
  "inj_on (from_digits b) {xs. set xs \<subseteq> {..<b} \<and> length xs = n}"
  by (intro inj_on_inverseI[where g="to_digits b n"] to_from_digits) auto
  
fun see_power :: "nat \<Rightarrow> strongly_explicit_expander \<Rightarrow> strongly_explicit_expander"
  where "see_power l e =
    \<lparr> see_size = see_size e, see_degree = see_degree e^l
    , see_step = (\<lambda>k v. foldl (\<lambda>y x. see_step e x y) v (to_digits (see_degree e) l k)) \<rparr>"

lemma graph_power_iso_see_power:
  assumes "fin_digraph (graph_of e)"
  shows "digraph_iso (graph_power (graph_of e) n) (graph_of (see_power n e))"
proof -
  let ?G = "graph_of e"
  let ?P = "graph_power (graph_of e) n"
  let ?H = "graph_of (see_power n e)"
  let ?d = "see_degree e"
  let ?n = "see_size e"

  interpret fin_digraph "(graph_of e)"
    using assms by auto

  interpret P:fin_digraph ?P
    by (intro graph_power_fin)

  define \<phi> where 
    "\<phi> = (\<lambda>(u,v). Arc u (arc_walk_head ?G (u, v)) (from_digits ?d (map arc_label v)))"

  define iso where "iso = 
    \<lparr> iso_verts = id, iso_arcs = \<phi>, iso_head = arc_head, iso_tail = arc_tail \<rparr>" 

  have "xs = ys" if "length xs = length ys" "map arc_label xs = map arc_label ys" 
    "is_arc_walk ?G u xs \<and> is_arc_walk ?G u ys \<and> u \<in> verts ?G" for xs ys u
    using that
  proof (induction xs ys arbitrary: u rule:list_induct2)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs y ys)
    have "arc_label x = arc_label y" "u \<in> verts ?G" "x \<in> out_arcs ?G u" "y \<in> out_arcs ?G u"
      using Cons by auto
    hence a:"x = y" 
      unfolding graph_of_def by auto
    moreover have "head ?G y \<in> verts ?G" using Cons by auto
    ultimately have "xs = ys" 
      using Cons(3,4) by (intro Cons(2)[of "head ?G y"]) auto
    thus ?case using a by auto
  qed
  hence 5:"inj_on (\<lambda>(u,v). (u, map arc_label v)) (arc_walks ?G n)"
    unfolding arc_walks_def by (intro inj_onI) auto
  have 3:"set (map arc_label (snd xs)) \<subseteq> {..<?d}" "length (snd xs) = n" 
    if "xs \<in> arc_walks ?G n" for xs
  proof -
    show "length (snd xs) = n"
      using subsetD[OF is_arc_walk_set[where G="?G"]] that unfolding arc_walks_def by auto
    have "set (snd xs) \<subseteq> arcs ?G"
      using subsetD[OF is_arc_walk_set[where G="?G"]] that unfolding arc_walks_def by auto
    thus "set (map arc_label (snd xs)) \<subseteq> {..<?d}"
      unfolding graph_of_def by auto
  qed

  hence 7:"inj_on (\<lambda>(u,v). (u, from_digits ?d (map arc_label v))) (arc_walks ?G n)"
    using inj_onD[OF 5] inj_onD[OF from_digits_inj] by (intro inj_onI) auto

  hence "inj_on \<phi> (arc_walks ?G n)"
    unfolding inj_on_def \<phi>_def by auto
  hence "inj_on (iso_arcs iso) (arcs (graph_power (graph_of e) n))" 
    unfolding iso_def graph_power_def by simp
  moreover have "inj_on (iso_verts iso) (verts (graph_power (graph_of e) n))" 
    unfolding iso_def by simp
  moreover have 
    "iso_verts iso (tail ?P a) = iso_tail iso (iso_arcs iso a)"
    "iso_verts iso (head ?P a) = iso_head iso (iso_arcs iso a)" if "a \<in> arcs ?P" for a 
    unfolding \<phi>_def iso_def graph_power_def by (simp_all add:case_prod_beta)
  ultimately have 0:"P.digraph_isomorphism iso"
    unfolding P.digraph_isomorphism_def by (intro conjI ballI P.wf_digraph_axioms) auto 

  have "card((\<lambda>(u, v).(u,from_digits ?d (map arc_label v)))`arc_walks ?G n)=card(arc_walks ?G n)"
    by (intro card_image 7)
  also have "... = ?d^n * ?n"
    by (intro card_arc_walks_see fin_digraph_axioms) 
  finally have "card((\<lambda>(u, v).(u,from_digits ?d (map arc_label v)))`arc_walks ?G n) = ?d^n * ?n"
    by simp
  moreover have "fst v \<in> {..<?n}" if "v \<in> arc_walks ?G n" for v
    using that unfolding arc_walks_def graph_of_def by auto
  moreover have "from_digits ?d (map arc_label (snd v)) < ?d ^ n" if "v \<in> arc_walks ?G n" for v
    using 3[OF that] by (intro from_digits_range) auto

  ultimately have 2: 
    "{..<?n}\<times>{..<?d^n} = (\<lambda>(u,v). (u, from_digits ?d (map arc_label v))) ` arc_walks ?G n" 
    by (intro card_subset_eq[symmetric]) auto

  have "foldl (\<lambda>y x. see_step e x y) u (map arc_label w) = arc_walk_head ?G (u,w)" 
    if "is_arc_walk ?G u w" "u \<in> verts ?G" for u w 
    using that
  proof (induction w rule:rev_induct)
    case Nil
    then show ?case by (simp add:arc_walk_head_def)
  next
    case (snoc x xs)
    hence "x \<in> arcs ?G" by (simp add:is_arc_walk_snoc) 
    hence "see_step e (arc_label x) (tail ?G x) = (head ?G x)"  
      unfolding graph_of_def by (auto simp add:image_iff)
    also have "... = arc_walk_head (graph_of e) (u, xs @ [x])"
      unfolding arc_walk_head_def by simp
    finally have "see_step e (arc_label x) (tail ?G x) =  arc_walk_head (graph_of e) (u, xs @ [x])"
      by simp
    thus ?case using snoc by (simp add:is_arc_walk_snoc)
  qed

  hence 4: "foldl (\<lambda>y x. see_step e x y) (fst x) (map arc_label (snd x)) = arc_walk_head ?G x" 
    if "x \<in> arc_walks (graph_of e) n" for x 
    using that unfolding arc_walks_def by (simp add:case_prod_beta)

  have "arcs ?H = (\<lambda>(v, i). Arc v (see_step (see_power n e) i v) i) ` ({..<?n}\<times>{..<?d^n})"
    unfolding graph_of_def by simp 
  also have "... = (\<lambda>(v,w). Arc v (see_step (see_power n e) (from_digits ?d (map arc_label w)) v) 
    (from_digits ?d (map arc_label w))) ` arc_walks ?G n"
    unfolding 2 image_image by (simp del:see_power.simps add: case_prod_beta comp_def)
  also have "... = (\<lambda>(v,w). Arc v (foldl (\<lambda>y x. see_step e x y) v (map arc_label w)) 
    (from_digits ?d (map arc_label w))) ` arc_walks ?G n"
    using 3  by (intro image_cong refl) (simp add:case_prod_beta to_from_digits)
  also have "... = \<phi> ` arc_walks ?G n"
    unfolding \<phi>_def using 4 by (simp add:case_prod_beta) 
  also have "... = iso_arcs iso ` arcs ?P"
    unfolding iso_def graph_power_def by simp
  finally have "arcs ?H = iso_arcs iso ` arcs ?P"
    by simp
  moreover have "verts ?H = iso_verts iso ` verts ?P"
    unfolding iso_def graph_of_def graph_power_def by simp
  moreover have "tail ?H = iso_tail iso"
    unfolding iso_def graph_of_def by simp
  moreover have "head ?H = iso_head iso"
    unfolding iso_def graph_of_def by simp
  ultimately have 1:"?H = app_iso iso ?P"
    unfolding app_iso_def  
    by (intro pre_digraph.equality) (simp_all del:see_power.simps)

  show ?thesis 
    using 0 1 unfolding digraph_iso_def by auto
qed

lemma see_power:
  assumes "is_expander e \<Lambda>\<^sub>a"
  shows "is_expander (see_power n e) (\<Lambda>\<^sub>a^n)"
proof -
  interpret G: "regular_graph" "graph_of e" 
    using assms unfolding is_expander_def by auto

  interpret H:"regular_graph" "graph_power (graph_of e) n"
    by (intro G.graph_power_regular)

  have 0:"digraph_iso (graph_power (graph_of e) n) (graph_of (see_power n e))"
    by (intro graph_power_iso_see_power) auto 

  have "regular_graph.\<Lambda>\<^sub>a (graph_of (see_power n e)) = H.\<Lambda>\<^sub>a"
    using H.regular_graph_iso_expansion[OF 0] by auto
  also have "... \<le> G.\<Lambda>\<^sub>a^n"
    by (intro G.graph_power_expansion)
  also have "... \<le> \<Lambda>\<^sub>a^n"
    using assms(1) unfolding is_expander_def
    by (intro power_mono G.\<Lambda>_ge_0)  auto
  finally have "regular_graph.\<Lambda>\<^sub>a (graph_of (see_power n e)) \<le> \<Lambda>\<^sub>a^n"
    by simp
  moreover have "regular_graph (graph_of (see_power n e))"
    using H.regular_graph_iso[OF 0] by auto
  ultimately show ?thesis
    unfolding is_expander_def by auto
qed

text \<open>The Margulis Construction from Section~\ref{sec:margulis} is a strongly explicit expander
graph.\<close>

definition mgg_vert :: "nat \<Rightarrow> nat \<Rightarrow> (int \<times> int)"
  where "mgg_vert n x = (x mod n, x div n)"

definition mgg_vert_inv :: "nat \<Rightarrow> (int \<times> int) \<Rightarrow> nat"
  where "mgg_vert_inv n x = nat (fst x) + nat (snd x) * n"

lemma mgg_vert_inv:
  assumes "n > 0" "x \<in> {0..<int n}\<times>{0..<int n}"
  shows "mgg_vert n (mgg_vert_inv n x) = x"
  using assms unfolding mgg_vert_def mgg_vert_inv_def by auto

definition mgg_arc :: "nat \<Rightarrow> (nat \<times> int)"
  where "mgg_arc k = (k mod 4, if k \<ge> 4 then (-1) else 1)"

definition mgg_arc_inv :: "(nat \<times> int) \<Rightarrow> nat"
  where "mgg_arc_inv x = (nat (fst x) + 4 * of_bool (snd x < 0))"

lemma mgg_arc_inv:
  assumes  "x \<in> {..<4}\<times>{-1,1}"
  shows "mgg_arc (mgg_arc_inv x) = x"
  using assms unfolding mgg_arc_def mgg_arc_inv_def by auto

definition see_mgg :: "nat \<Rightarrow> strongly_explicit_expander" where
  "see_mgg n = \<lparr> see_size = n^2, see_degree = 8, 
    see_step = (\<lambda>i v. mgg_vert_inv n (mgg_graph_step n (mgg_vert n v) (mgg_arc i))) \<rparr>"

lemma mgg_graph_iso:
  assumes "n > 0"
  shows "digraph_iso (mgg_graph n) (graph_of (see_mgg n))"
proof -
  let ?v = "mgg_vert n" let ?vi = "mgg_vert_inv n"
  let ?a = "mgg_arc" let ?ai = "mgg_arc_inv"
  let ?G = "graph_of (see_mgg n)" let ?s = "mgg_graph_step n"

  define \<phi> where "\<phi> a = Arc (?vi (arc_tail a)) (?vi (arc_head a)) (?ai (arc_label a))" for a

  define iso where "iso = 
    \<lparr> iso_verts = mgg_vert_inv n, iso_arcs = \<phi>, iso_head = arc_head, iso_tail = arc_tail \<rparr>" 

  interpret M: margulis_gaber_galil n
    using assms by unfold_locales

  have inj_vi: "inj_on ?vi (verts M.G)"
    unfolding mgg_graph_def mgg_vert_inv_def
    by (intro inj_on_inverseI[where g="mgg_vert n"]) (auto simp:mgg_vert_def)
  have "card (?vi ` verts M.G) = card (verts M.G)"
    by (intro card_image inj_vi)
  moreover have "card (verts M.G) = n\<^sup>2"
    unfolding mgg_graph_def by (auto simp:power2_eq_square)
  moreover have "mgg_vert_inv n x \<in> {..<n\<^sup>2}" if "x \<in> verts M.G" for x 
  proof -
    have "mgg_vert_inv n x = nat (fst x) + nat (snd x) * n"
      unfolding mgg_vert_inv_def by simp
    also have "... \<le> (n-1) + (n-1) * n"
      using that unfolding mgg_graph_def
      by (intro add_mono mult_right_mono) auto
    also have "... = n * n - 1" using assms by (simp add:algebra_simps)
    also have "... < n^2"
      using assms by (simp add: power2_eq_square)
    finally have "mgg_vert_inv n x < n^2" by simp
    thus ?thesis by simp
  qed
  ultimately have 0:"{..<n^2} = ?vi ` verts M.G"
    by (intro card_subset_eq[symmetric] image_subsetI) auto

  have inj_ai: "inj_on ?ai ({..<4} \<times> {-1,1})"
    unfolding mgg_arc_inv_def by (intro inj_onI) auto
  have "card (?ai ` ({..<4} \<times> {- 1, 1})) = card ({..<4::nat} \<times> {-1,1::int})"
    by (intro card_image inj_ai)
  hence 1:"{..<8} = ?ai ` ({..<4} \<times> {-1,1})"
    by (intro card_subset_eq[symmetric] image_subsetI) (auto simp add:mgg_arc_inv_def)

  have "arcs ?G = (\<lambda>(v, i). Arc v (?vi (?s (?v v) (?a i))) i) ` ({..<n\<^sup>2} \<times> {..<8})"
    by (simp add:see_mgg_def graph_of_def) 
  also have "... = (\<lambda>(v, i). Arc (?vi v) (?vi (?s (?v (?vi v)) (?a (?ai i)))) (?ai i)) ` 
    (verts M.G \<times> ({..<4} \<times> {-1,1}))"
    unfolding 0 1 mgg_arc_inv by (auto simp add:image_iff)
  also have "... = (\<lambda>(v, i). Arc (?vi v) (?vi (?s v i)) (?ai i)) ` (verts M.G \<times> ({..<4} \<times> {-1,1}))"
    using mgg_vert_inv[OF assms] mgg_arc_inv unfolding mgg_graph_def by (intro image_cong) auto
  also have "... = (\<phi> \<circ> (\<lambda>(t, l). Arc t (?s t l) l)) ` (verts M.G \<times> ({..<4} \<times> {-1,1}))" 
    unfolding \<phi>_def by (intro image_cong refl) ( simp add:comp_def case_prod_beta )
  also have "... = \<phi> ` arcs M.G" 
    unfolding mgg_graph_def by (simp add:image_image)
  also have "... = iso_arcs iso ` arcs (mgg_graph n)"
    unfolding iso_def by simp
  finally have "arcs (graph_of (see_mgg n)) = iso_arcs iso ` arcs (mgg_graph n)" 
    by simp
  moreover have "verts ?G = iso_verts iso ` verts (mgg_graph n)"
    unfolding iso_def graph_of_def see_mgg_def using 0 by simp 
  moreover have "tail ?G = iso_tail iso"
    unfolding iso_def graph_of_def by simp
  moreover have "head ?G = iso_head iso"
    unfolding iso_def graph_of_def by simp
  ultimately have 0:"?G = app_iso iso (mgg_graph n)" 
    unfolding app_iso_def   by (intro pre_digraph.equality) simp_all

  have "inj_on \<phi> (arcs M.G)"
  proof (rule inj_onI)
    fix x y assume assms': "x \<in> arcs M.G" "y \<in> arcs M.G" "\<phi> x = \<phi> y"

    have "?vi (head M.G x) = ?vi (head M.G y)"
      using assms'(3) unfolding \<phi>_def mgg_graph_def by auto
    hence "head M.G x = head M.G y"
      using assms'(1,2) by (intro inj_onD[OF inj_vi]) auto
    hence "arc_head x = arc_head y"
      unfolding mgg_graph_def by simp

    moreover have "?vi (tail M.G x) = ?vi (tail M.G y)"
      using assms'(3) unfolding \<phi>_def mgg_graph_def by auto
    hence "tail M.G x = tail M.G y"
      using assms'(1,2) by (intro inj_onD[OF inj_vi]) auto
    hence "arc_tail x = arc_tail y"
      unfolding mgg_graph_def by simp

    moreover have "?ai (arc_label x) = ?ai (arc_label y)"
      using assms'(3) unfolding \<phi>_def by auto
    hence "arc_label x = arc_label y"
      using assms'(1,2) unfolding mgg_graph_def
      by (intro inj_onD[OF inj_ai]) (auto simp del:mgg_graph_step.simps)

    ultimately show "x = y"
      by (intro arc.expand) auto
  qed
  hence "inj_on (iso_arcs iso) (arcs M.G)" 
    unfolding iso_def by simp
  moreover have "inj_on (iso_verts iso) (verts M.G)" 
    using inj_vi unfolding iso_def by simp
  moreover have 
    "iso_verts iso (tail M.G a) = iso_tail iso (iso_arcs iso a)" 
    "iso_verts iso (head M.G a) = iso_head iso (iso_arcs iso a)"  if "a \<in> arcs M.G" for a
    unfolding iso_def \<phi>_def mgg_graph_def by auto
  ultimately have 1:"M.digraph_isomorphism iso"
    unfolding M.digraph_isomorphism_def by (intro conjI ballI M.wf_digraph_axioms) auto

  show ?thesis unfolding digraph_iso_def using 0 1 by auto
qed

lemma see_mgg:
  assumes "n > 0"
  shows "is_expander (see_mgg n) (5* sqrt 2 / 8)"
proof -
  interpret G: "margulis_gaber_galil" "n" 
    using assms by unfold_locales auto

  note 0 = mgg_graph_iso[OF assms]

  have "regular_graph.\<Lambda>\<^sub>a (graph_of (see_mgg n)) = G.\<Lambda>\<^sub>a"
    using G.regular_graph_iso_expansion[OF 0] by auto
  also have "... \<le> (5* sqrt 2 / 8)"
    using G.mgg_numerical_radius unfolding G.MGG_bound_def by simp
  finally have "regular_graph.\<Lambda>\<^sub>a (graph_of (see_mgg n)) \<le> (5* sqrt 2 / 8)"
    by simp
  moreover have "regular_graph (graph_of (see_mgg n))"
    using G.regular_graph_iso[OF 0] by auto
  ultimately show ?thesis
    unfolding is_expander_def by auto
qed

text \<open>Using all of the above it is possible to construct strongly explicit expanders of every 
size and spectral gap with asymptotically optimal degree.\<close>

definition see_standard_aux 
  where "see_standard_aux n = see_compress n (see_mgg (nat \<lceil>sqrt n\<rceil>))"

lemma see_standard_aux:
  assumes "n > 0"
  shows 
    "is_expander (see_standard_aux n) ((8+5 * sqrt 2) / 16)" (is "?A")
    "see_degree (see_standard_aux n) = 16" (is "?B")
    "see_size (see_standard_aux n) = n" (is "?C")
proof -
  have 2:"sqrt (real n) > -1"
    by (rule less_le_trans[where y="0"]) auto

  have 0:"real n \<le> of_int \<lceil>sqrt (real n)\<rceil>^2" 
    by (simp add:sqrt_le_D)

  consider (a) "n = 1" | (b) "n \<ge> 2 \<and> n \<le> 4" | (c) "n \<ge> 5 \<and> n \<le> 9" | (d) "n \<ge> 10" 
    using assms by linarith
  hence 1:"of_int \<lceil>sqrt (real n)\<rceil>^2 \<le> 2 * real n" 
  proof (cases)
    case a then show ?thesis by simp
  next
    case b
    hence "real_of_int \<lceil>sqrt (real n)\<rceil>^2 \<le> of_int \<lceil>sqrt (real 4)\<rceil>^2"
      using 2
      by (intro power_mono iffD2[OF of_int_le_iff] ceiling_mono iffD2[OF real_sqrt_le_iff]) auto
    also have "... = 2 * real 2" by simp
    also have "... \<le> 2 * real n"
      using b by (intro mult_left_mono) auto
    finally show ?thesis by simp
  next
    case c
    hence "real_of_int \<lceil>sqrt (real n)\<rceil>^2 \<le> of_int \<lceil>sqrt (real 9)\<rceil>^2"
      using 2
      by (intro power_mono iffD2[OF of_int_le_iff] ceiling_mono iffD2[OF real_sqrt_le_iff]) auto
    also have "... = 9" by simp
    also have "... \<le> 2 * real 5" by simp
    also have "... \<le> 2 * real n"
      using c by (intro mult_left_mono) auto
    finally show ?thesis by simp
  next
    case d
    have "real_of_int \<lceil>sqrt (real n)\<rceil>^2 \<le> (sqrt (real n)+1)^2"
      using 2 by (intro power_mono) auto
    also have "... = real n + sqrt (4 * real n + 0) + 1"
      using real_sqrt_pow2 by (simp add:power2_eq_square algebra_simps real_sqrt_mult)
    also have "... \<le> real n + sqrt (4 * real n + (real n * (real n - 6) + 1)) + 1"
      using d by (intro add_mono iffD2[OF real_sqrt_le_iff]) auto
    also have "... = real n + sqrt ((real n-1)^2) + 1"
      by (intro_cong "[\<sigma>\<^sub>2 (+), \<sigma>\<^sub>1 sqrt]") (auto simp add:power2_eq_square algebra_simps)
    also have "... = 2 * real n"
      using d by simp
    finally show ?thesis by simp
  qed

  have "real (nat \<lceil>sqrt (real n)\<rceil>^2) = of_int \<lceil>sqrt (real n)\<rceil>^2"
    unfolding of_nat_power using 2 by (simp add:not_less)
  also have "... \<in> {real n..2 * real n}" 
    using 0 1 by auto
  also have "... = {real n..real (2*n)}" by simp
  finally have "real (nat \<lceil>sqrt (real n)\<rceil>^2) \<in> {real n..real (2*n)}" by simp
  hence "nat \<lceil>sqrt (real n)\<rceil>^2 \<in> {n..2*n}" by (simp del:of_nat_mult)
  hence "see_size (see_mgg (nat \<lceil>sqrt (real n)\<rceil>)) \<in> {n..2*n}"
    by (simp add:see_mgg_def)
  moreover have "sqrt (real n) > 0" using assms by simp
  hence "0 < nat \<lceil>sqrt (real n)\<rceil>" by simp
  ultimately have "is_expander (see_standard_aux n) ((5* sqrt 2 / 8)/2 + 1/2)"
    unfolding see_standard_aux_def by (intro see_compress see_mgg) auto
  thus ?A 
    by (auto simp add:field_simps)
  show ?B 
    unfolding see_standard_aux_def by (simp add:see_mgg_def)
  show ?C 
    unfolding see_standard_aux_def by simp
qed

definition see_standard_power
  where "see_standard_power x  = (if x \<le> (0::real) then 0 else nat \<lceil>ln x / ln 0.95\<rceil>)"

lemma see_standard_power:
  assumes "\<Lambda>\<^sub>a > 0"
  shows "0.95^(see_standard_power \<Lambda>\<^sub>a) \<le> \<Lambda>\<^sub>a" (is "?L \<le> ?R")
proof (cases "\<Lambda>\<^sub>a \<le> 1")
  case True
  hence "0 \<le> ln \<Lambda>\<^sub>a / ln 0.95" 
    using assms by (intro divide_nonpos_neg) auto
  hence 1:"0 \<le> \<lceil>ln \<Lambda>\<^sub>a / ln 0.95\<rceil>" 
    by simp
  have "?L = 0.95^nat \<lceil>ln \<Lambda>\<^sub>a / ln 0.95\<rceil>"
    using assms unfolding see_standard_power_def by simp
  also have "... = 0.95 powr (of_nat (nat (\<lceil>ln \<Lambda>\<^sub>a / ln 0.95\<rceil>)))"
    by (subst powr_realpow) auto 
  also have "... = 0.95 powr \<lceil>ln \<Lambda>\<^sub>a / ln 0.95\<rceil>"
    using 1 by (subst of_nat_nat) auto
  also have "... \<le> 0.95 powr (ln \<Lambda>\<^sub>a / ln 0.95)"
    by (intro powr_mono_rev) auto
  also have "... = ?R"
    using assms unfolding powr_def by simp
  finally show ?thesis by simp
next
  case False
  hence "ln \<Lambda>\<^sub>a / ln 0.95 \<le> 0"
    by (subst neg_divide_le_eq) auto
  hence "see_standard_power \<Lambda>\<^sub>a = 0"
    unfolding see_standard_power_def by simp
  then show ?thesis using False by simp
qed

lemma see_standard_power_eval[code]: 
  "see_standard_power x = (if x \<le> 0 \<or> x \<ge> 1 then 0 else (1+see_standard_power (x/0.95)))"
proof (cases "x \<le> 0 \<or> x \<ge> 1")
  case True
  have "ln x / ln (19 / 20) \<le> 0" if "x > 0"
  proof -
    have "x \<ge> 1" using that True by auto
    thus ?thesis
      by (intro divide_nonneg_neg) auto
  qed
  then show ?thesis using True unfolding see_standard_power_def by simp
next
  case False
  hence x_range: "x > 0" "x < 1" by auto

  have "ln (x / 0.95) < ln (1/0.95)" 
    using x_range by (intro iffD2[OF ln_less_cancel_iff]) auto
  also have "... = - ln 0.95" 
    by (subst ln_div) auto
  finally have "ln (x / 0.95) < - ln 0.95" by simp
  hence 0: "-1 < ln (x / 0.95) / ln 0.95"
    by (subst neg_less_divide_eq)  auto

  have "see_standard_power x = nat \<lceil>ln x / ln 0.95\<rceil>"
    using x_range unfolding see_standard_power_def by simp  
  also have "... = nat \<lceil>ln (x/0.95) / ln 0.95 + 1\<rceil>"
    by (subst ln_div[OF x_range(1)]) (simp_all add:field_simps )
  also have "... = nat (\<lceil>ln (x/0.95) / ln 0.95\<rceil>+1)"
    by (intro arg_cong[where f="nat"]) simp
  also have "... = 1 + nat \<lceil>ln (x/0.95) / ln 0.95\<rceil>"
    using 0 by (subst nat_add_distrib) auto
  also have "... = (if x \<le> 0 \<or> 1 \<le> x then 0 else 1 + see_standard_power (x/0.95))"
    unfolding see_standard_power_def using x_range by auto
  finally show ?thesis by simp
qed

definition see_standard :: "nat \<Rightarrow> real \<Rightarrow> strongly_explicit_expander"
  where "see_standard n \<Lambda>\<^sub>a = see_power (see_standard_power \<Lambda>\<^sub>a) (see_standard_aux n)"

theorem see_standard:
  assumes "n > 0" "\<Lambda>\<^sub>a > 0"
  shows "is_expander (see_standard n \<Lambda>\<^sub>a) \<Lambda>\<^sub>a"
    and "see_size (see_standard n \<Lambda>\<^sub>a) = n"
    and "see_degree (see_standard n \<Lambda>\<^sub>a) = 16 ^ (nat \<lceil>ln \<Lambda>\<^sub>a / ln 0.95\<rceil>)" (is "?C")
proof -
  have 0:"is_expander (see_standard_aux n) 0.95"
    by (intro see_standard_aux(1)[OF assms(1)] is_expander_mono[where a="(8+5 * sqrt 2) / 16"])
     (approximation 10)

  show "is_expander (see_standard n \<Lambda>\<^sub>a) \<Lambda>\<^sub>a"
    unfolding see_standard_def 
    by (intro see_power 0 is_expander_mono[where a="0.95^(see_standard_power \<Lambda>\<^sub>a)"]
      see_standard_power assms(2))
  show "see_size (see_standard n \<Lambda>\<^sub>a) = n"
    unfolding see_standard_def using see_standard_aux[OF assms(1)] by simp

  have "see_degree (see_standard n \<Lambda>\<^sub>a) = 16 ^ (see_standard_power \<Lambda>\<^sub>a)"
    unfolding see_standard_def using see_standard_aux[OF assms(1)] by simp 
  also have "... = 16 ^ (nat \<lceil>ln \<Lambda>\<^sub>a / ln 0.95\<rceil>)"
    unfolding see_standard_power_def using assms(2) by simp
  finally show ?C by simp
qed

fun see_sample_walk :: "strongly_explicit_expander \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list"
  where 
    "see_sample_walk e 0 x = [x]" |
    "see_sample_walk e (Suc l) x = (let w = see_sample_walk e l (x div (see_degree e)) in 
      w@[see_step e (x mod (see_degree e)) (last w)])"

theorem see_sample_walk:
  fixes e l
  assumes "fin_digraph (graph_of e)"
  defines "r \<equiv> see_size e * see_degree e ^l" 
  shows "{# see_sample_walk e l k. k \<in># mset_set {..<r} #} = walks' (graph_of e) l"
  unfolding r_def
proof (induction l)
  case 0
  then show ?case unfolding graph_of_def by simp
next
  case (Suc l)
  interpret fin_digraph "graph_of e"
    using assms(1) by auto

  let ?d = "see_degree e"
  let ?n = "see_size e"
  let ?w = "see_sample_walk e"
  let ?G = "graph_of e"
  define r where "r = ?n * ?d^l" 

  have 1: "{i * ?d..<(i + 1) * ?d} \<inter> {j * ?d..<(j + 1) * ?d} = {}" if "i \<noteq> j" for i j
    using that index_div_eq by blast

  have 2:"vertices_from ?G x = {# see_step e i x. i \<in># mset_set {..<?d}#}" (is "?L = ?R") 
    if "x \<in> verts ?G" for x
  proof -
    have "x < ?n" 
      using that unfolding graph_of_def by simp
    hence 1:"out_arcs ?G x = (\<lambda>i. Arc x (see_step e i x) i) ` {..<?d}"
      unfolding out_arcs_def graph_of_def by (auto simp add:image_iff set_eq_iff)
    
    have "?L = {# arc_head a. a \<in># mset_set (out_arcs ?G x) #}"
      unfolding verts_from_alt by (simp add:graph_of_def)
    also have "... = {# arc_head a. a \<in># {# Arc x (see_step e i x) i. i \<in># mset_set {..<?d}#}#} " 
      unfolding 1 
      by (intro arg_cong2[where f= "image_mset"] image_mset_mset_set[symmetric] inj_onI) auto
    also have "... = ?R"
      by (simp add:image_mset.compositionality comp_def)
    finally show ?thesis by simp
  qed

  have "card (\<Union>w<r. {w * ?d..<(w + 1) *?d}) = (\<Sum>w < r. card {w * ?d..<(w + 1) *?d})"
    using 1 by (intro card_UN_disjoint) auto
  also have "... = r * ?d" by simp
  finally have "card (\<Union>w<r. {w * ?d..<(w + 1) *?d}) = card {..<?d * r}" by simp
  moreover  have "?d + z * ?d \<le> ?d * r" if "z < r" for z 
  proof - 
    have "?d + z * ?d = ?d * (z + 1)" by simp
    also have "... \<le> ?d * r" 
      using that by (intro mult_left_mono) auto
    finally show ?thesis by simp
  qed
  ultimately have 0: "(\<Union>w<r. {w * ?d..<(w + 1) *?d}) = {..<?d * r}"
    using order_less_le_trans by (intro card_subset_eq subsetI) auto 

  have "{# ?w (l+1) k. k \<in># mset_set {..<?n * ?d^(l+1)} #} = {#?w (l+1) k. k \<in># mset_set {..<?d * r}#}"
    unfolding r_def by (simp add:ac_simps)
  also have "... = {# ?w (l+1) x. x \<in># mset_set (\<Union>w<r. {w * ?d..<(w + 1) * ?d})#}"
    unfolding 0 by simp
  also have "... = image_mset (?w (l+1)) (concat_mset
     (image_mset (mset_set \<circ> (\<lambda>w. {w * ?d..<(w + 1) * ?d})) (mset_set {..<r})))"
    by (intro arg_cong2[where f="image_mset"] concat_disjoint_union_mset refl 1) auto
  also have "... = concat_mset{#{#?w (l+1) i. i\<in>#mset_set {w*?d..<(w+1)*?d}#}. w\<in>#mset_set {..<r}#}"
    by (simp add:image_concat_mset image_mset.compositionality comp_def del:see_sample_walk.simps)
  also have "...=concat_mset {#{#?w(l+1)i. i\<in>#mset_set ((+)(w*?d)`{..<?d})#}. w\<in>#mset_set {..<r}#}"
    by (intro_cong "[\<sigma>\<^sub>1 concat_mset, \<sigma>\<^sub>2 image_mset, \<sigma>\<^sub>1 mset_set]" more:ext)
     (simp add:  atLeast0LessThan[symmetric])
  also have "... = concat_mset 
    {#{#?w (l+1) i. i\<in>#image_mset ((+) (w*?d)) (mset_set {..<?d})#}. w\<in>#mset_set {..<r}#}"
    by (intro_cong "[\<sigma>\<^sub>1 concat_mset, \<sigma>\<^sub>2 image_mset]" more:image_mset_cong 
        image_mset_mset_set[symmetric] inj_onI) auto
  also have "... = concat_mset {#{#?w (l+1) (w*?d+i).i\<in>#mset_set {..<?d}#}. w\<in>#mset_set {..<r}#}"
    by (simp add:image_mset.compositionality comp_def del:see_sample_walk.simps)
  also have "... = concat_mset 
    {#{#?w l w@[see_step e i (last (?w l w))].i\<in>#mset_set {..<?d}#}.w\<in>#mset_set {..<r}#}"
    by (intro_cong "[\<sigma>\<^sub>1 concat_mset]" more:image_mset_cong) (simp add:Let_def)
  also have "... = concat_mset {#{#w@[see_step e i (last w)].i\<in>#mset_set {..<?d}#}.w\<in>#walks' ?G l#}"
    unfolding r_def Suc[symmetric] image_mset.compositionality comp_def by simp
  also have "... = concat_mset 
    {#{#w@[x].x\<in>#{# see_step e i (last w). i\<in>#mset_set {..<?d}#}#}. w \<in># walks' ?G l#}"
    unfolding image_mset.compositionality comp_def by simp
  also have "... = concat_mset {#{#w@[x].x\<in>#vertices_from ?G (last w)#}. w \<in># walks' ?G l#}"
    using last_in_set set_walks_2(1,2)
    by (intro_cong "[\<sigma>\<^sub>1 concat_mset, \<sigma>\<^sub>2 image_mset]" more:image_mset_cong 2[symmetric]) blast
  also have "... = walks' (graph_of e) (l+1)"
    by (simp add:image_mset.compositionality comp_def)
  finally show ?case by simp 
qed

unbundle no_intro_cong_syntax

end
