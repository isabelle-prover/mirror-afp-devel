section \<open>Graph Powers\label{sec:graph_power}\<close>

theory Expander_Graphs_Power_Construction
  imports 
    Expander_Graphs_Walks
    Graph_Theory.Arc_Walk
begin

unbundle intro_cong_syntax

fun is_arc_walk :: "('a, 'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> bool"
  where 
    "is_arc_walk G _ [] = True" |
    "is_arc_walk G y (x#xs) = (is_arc_walk G (head G x) xs \<and> tail G x = y \<and> x \<in> arcs G)"

definition arc_walk_head :: "('a, 'b) pre_digraph \<Rightarrow> ('a \<times> 'b list) \<Rightarrow> 'a" 
  where
    "arc_walk_head G x = (if snd x = [] then fst x else head G (last (snd x)))"

lemma is_arc_walk_snoc:
  "is_arc_walk G y (xs@[x]) \<longleftrightarrow> is_arc_walk G y xs \<and> x \<in> out_arcs G (arc_walk_head G (y,xs))"
  by (induction xs arbitrary: y, simp_all add:ac_simps arc_walk_head_def)

lemma is_arc_walk_set:
  assumes "is_arc_walk G u w" 
  shows "set w \<subseteq> arcs G"
  using assms by (induction w arbitrary: u, auto)

lemma (in wf_digraph) awalk_is_arc_walk:
  assumes "u \<in> verts G"
  shows "is_arc_walk G u w \<longleftrightarrow> awalk u w (awlast u w)"
  using assms unfolding awalk_def by (induction w arbitrary: u, auto)

definition arc_walks :: "('a, 'b) pre_digraph \<Rightarrow> nat \<Rightarrow> ('a \<times> 'b list) set"
  where
    "arc_walks G l = {(u,w). u \<in> verts G \<and> is_arc_walk G u w \<and> length w = l}"

lemma arc_walks_len:
  assumes "x \<in> arc_walks G l" 
  shows "length (snd x) = l"
  using assms unfolding arc_walks_def by auto

lemma (in wf_digraph) awhd_of_arc_walk:
  assumes "w \<in> arc_walks G l"
  shows "awhd (fst w) (snd w) = fst w"
  using assms unfolding arc_walks_def awalk_verts_def 
  by (cases "snd w", auto)

lemma (in wf_digraph) awlast_of_arc_walk:
  assumes "w \<in> arc_walks G l"
  shows "awlast (fst w) (snd w) = arc_walk_head G w"
  unfolding awalk_verts_conv arc_walk_head_def by simp

lemma (in wf_digraph) arc_walk_head_wellformed:
  assumes "w \<in> arc_walks G l"
  shows "arc_walk_head G w \<in> verts G"
proof (cases "snd w = []")
  case True
  then show ?thesis 
    using assms unfolding arc_walks_def arc_walk_head_def by auto
next
  case False
  have 0:"is_arc_walk G (fst w) (snd w)" using assms unfolding arc_walks_def by auto
  have "last (snd w) \<in> set (snd w)"
    using False last_in_set by auto
  also have "... \<subseteq> arcs G"
    by (intro is_arc_walk_set[OF 0])
  finally have "last (snd w) \<in> arcs G" by simp
  thus ?thesis unfolding arc_walk_head_def using False by simp
qed

lemma (in wf_digraph) arc_walk_tail_wellformed:
  assumes "w \<in> arc_walks G l"
  shows "fst w \<in> verts G"
  using assms unfolding arc_walks_def by auto

lemma (in fin_digraph) arc_walks_fin: 
  "finite (arc_walks G l)"
proof -
  have 0:"finite (verts G \<times> {w. set w \<subseteq> arcs G \<and> length w = l})"
    by (intro finite_cartesian_product finite_lists_length_eq) auto
  show "finite (arc_walks G l)"
    unfolding arc_walks_def using is_arc_walk_set[where G="G"]
    by (intro finite_subset[OF _ 0] subsetI) auto
qed

lemma (in wf_digraph) awalk_verts_unfold:
  assumes "w \<in> arc_walks G l"
  shows "awalk_verts (fst w) (snd w) = fst w#map (head G) (snd w)" (is "?L = ?R")
proof -
  obtain u v where w_def: "w = (u,v)" by fastforce

  have "awalk u v (awlast u v)"
    using assms unfolding w_def arc_walks_def
    by (intro iffD1[OF awalk_is_arc_walk]) auto
  hence cas: "cas u v (awlast u v)"
    unfolding awalk_def by simp

  have 0: "tail G (hd v) = u" if "v \<noteq> []"
    using cas that by (cases v) auto

  have "?L = awalk_verts u v"
    unfolding w_def by simp
  also have "... = (if v = [] then [u] else tail G (hd v) # map (head G) v)"
    by (intro awalk_verts_conv'[OF cas])
  also have "... = u# map (head G) v"
    using 0 by simp
  also have "... = ?R"
    unfolding w_def by simp
  finally show ?thesis by simp
qed

lemma (in fin_digraph) arc_walks_map_walks': 
  "walks' G l = image_mset (case_prod awalk_verts) (mset_set (arc_walks G l))"
proof (induction l)
  case 0
  let ?g = "\<lambda>x. fst x#map (head G) (snd x)"

  have "walks' G 0 = {#[x]. x \<in># mset_set (verts G)#}"
    by simp
  also have "... = image_mset ?g (image_mset (\<lambda>x. (x,[])) (mset_set (verts G)))"
    unfolding image_mset.compositionality by (simp add:comp_def)
  also have "... = image_mset ?g (mset_set ((\<lambda>x. (x,[])) ` verts G))"
    by (intro arg_cong2[where f="image_mset"] image_mset_mset_set inj_onI) auto
  also have "... = image_mset ?g (mset_set ({(u, w). u \<in> verts G \<and> w = []}))"
    by (intro_cong "[\<sigma>\<^sub>2 image_mset]") auto
  also have "... = image_mset ?g (mset_set (arc_walks G 0))"
    unfolding arc_walks_def by (intro_cong "[\<sigma>\<^sub>2 image_mset,\<sigma>\<^sub>1 mset_set]") auto
  also have "... = image_mset (case_prod awalk_verts) (mset_set (arc_walks G 0))"
    using arc_walks_fin by (intro image_mset_cong) (simp add:case_prod_beta awalk_verts_unfold)
  finally show ?case by simp
next
  case (Suc l)
  let ?f = "\<lambda>(u,w) a. (u,w@[a])"
  let ?g = "\<lambda>x. fst x#map (head G) (snd x)"

  have "arc_walks G (l+1) = case_prod ?f ` {(x,y). ?f x y \<in> arc_walks G (l+1)}"
    using arc_walks_len[where G="G" and l="Suc l", THEN iffD1[OF length_Suc_conv_rev]]
    by force
  also have "... = case_prod ?f ` {(x,y). x \<in> arc_walks G l \<and> y \<in> out_arcs G (arc_walk_head G x)}"
    unfolding arc_walks_def using is_arc_walk_snoc[where G="G"]
    by (intro_cong "[\<sigma>\<^sub>2 image]")  auto
  also have "... = (\<Union>w \<in> arc_walks G l. ?f w ` out_arcs G (arc_walk_head G w))"
    by (auto simp add:image_iff)
  finally have 0:"arc_walks G (l+1) = (\<Union>w \<in> arc_walks G l. ?f w ` out_arcs G (arc_walk_head G w))"
    by simp

  have "mset_set (arc_walks G (l+1)) = concat_mset (image_mset (mset_set \<circ> 
    (\<lambda>w. ?f w ` out_arcs G (arc_walk_head G w))) (mset_set (arc_walks G l)))"
    unfolding 0 by (intro concat_disjoint_union_mset arc_walks_fin finite_imageI) auto 
  also have "... = concat_mset {# mset_set (?f x ` out_arcs G (arc_walk_head G x)). 
    x\<in>#mset_set(arc_walks G l)#}"
    by (simp add:comp_def case_prod_beta) 
  also have "... = concat_mset {# {# ?f x y. y \<in># mset_set (out_arcs G (arc_walk_head G x))#}. 
    x \<in># mset_set (arc_walks G l)#}"
    by (intro_cong "[\<sigma>\<^sub>1 concat_mset]" more:image_mset_cong image_mset_mset_set[symmetric] inj_onI)
     auto
  finally have 1:"mset_set (arc_walks G (l+1)) = concat_mset 
    {# {# ?f x y. y \<in># mset_set (out_arcs G (arc_walk_head G x))#}. x \<in># mset_set (arc_walks G l)#}"
    by simp

  have "walks' G (l+1)=concat_mset {#{#w @ [z]. z\<in># vertices_from G (last w)#}. w \<in># walks' G l#}"
    by simp
  also have "... = concat_mset {#
      {#awalk_verts (fst x) (snd x) @ [z]. z \<in># vertices_from G (awlast (fst x) (snd x))#}. 
      x \<in># mset_set (arc_walks G l)#}"
    unfolding Suc by (simp add:image_mset.compositionality comp_def case_prod_beta)
  also have "... = concat_mset {#
      {#?g x @ [z]. z \<in># vertices_from G (awlast (fst x) (snd x))#}. 
      x \<in># mset_set (arc_walks G l)#}"
    using arc_walks_fin 
    by (intro_cong "[\<sigma>\<^sub>1 concat_mset]" more:image_mset_cong) (auto simp: awalk_verts_unfold)
  also have "... = concat_mset {# {#?g x @ [z]. z \<in># vertices_from G (arc_walk_head G x)#}. 
      x \<in># mset_set (arc_walks G l)#}"
    using arc_walks_fin awlast_of_arc_walk
    by (intro_cong "[\<sigma>\<^sub>1 concat_mset, \<sigma>\<^sub>2 image_mset]" more: image_mset_cong) auto
  also have "... = (concat_mset {# {# ?g (fst x, snd x@[y]). 
    y \<in># mset_set (out_arcs G (arc_walk_head G x))#}. x \<in># mset_set (arc_walks G l)#})"
    unfolding verts_from_alt by (simp add:image_mset.compositionality comp_def)
  also have "... = image_mset ?g (concat_mset {# {# ?f x y. 
    y \<in># mset_set (out_arcs G (arc_walk_head G x))#}. x \<in># mset_set (arc_walks G l)#})"
    unfolding image_concat_mset
    by (auto simp add:comp_def case_prod_beta image_mset.compositionality) 
  also have "... = image_mset ?g (mset_set (arc_walks G (l+1)))"
    unfolding 1 by simp
  also have "... = image_mset (case_prod awalk_verts) (mset_set (arc_walks G (l+1)))"
    using arc_walks_fin by (intro image_mset_cong) (simp add:case_prod_beta awalk_verts_unfold)
  finally show ?case by simp
qed

lemma (in fin_digraph) arc_walks_map_walks: 
  "walks G (l+1) = image_mset (case_prod awalk_verts) (mset_set (arc_walks G l))"
  using arc_walks_map_walks' unfolding walks_def by simp

lemma (in wf_digraph)
  assumes "awalk u a v " "length a = l" "l > 0"
  shows awalk_ends: "tail G (hd a) = u" "head G (last a) = v"
proof -
  have 0:"cas u a v" 
    using assms unfolding awalk_def by simp
  have 1: "a \<noteq> []" using assms(2,3) by auto

  show "tail G (hd a) = u"
    using 0 unfolding cas_simp[OF 1] by auto

  show "head G (last a) = v"
    using 1 0 by (induction a arbitrary:u rule:list_nonempty_induct) auto 
qed

definition graph_power :: "('a, 'b) pre_digraph \<Rightarrow> nat \<Rightarrow> ('a, ('a \<times> 'b list)) pre_digraph"
  where "graph_power G l =
    \<lparr> verts = verts G, arcs = arc_walks G l, tail = fst, head = arc_walk_head G \<rparr>"

lemma (in wf_digraph) graph_power_wf: 
  "wf_digraph (graph_power G l)"
proof -
  have "tail (graph_power G l) a \<in> verts (graph_power G l)"
       "head (graph_power G l) a \<in> verts (graph_power G l)" 
       if "a \<in> arcs (graph_power G l)" for a
    using that arc_walk_head_wellformed arc_walk_tail_wellformed
    unfolding graph_power_def by simp_all
  thus ?thesis 
    unfolding wf_digraph_def by auto
qed

lemma (in fin_digraph) graph_power_fin: 
  "fin_digraph (graph_power G l)"
proof -
  interpret H:wf_digraph "graph_power G l" 
    using graph_power_wf by auto

  have "finite (arcs (graph_power G l))" 
    using arc_walks_fin
    unfolding graph_power_def by simp

  moreover have "finite (verts (graph_power G l))" 
    unfolding graph_power_def by simp
  ultimately show ?thesis
    by unfold_locales auto
qed

lemma (in fin_digraph) graph_power_count_edges:
  fixes l v w
  defines "S \<equiv> {x. length x=l+1\<and>set x\<subseteq>verts G\<and>hd x=v\<and>last x=w}"
  shows "count (edges (graph_power G l)) (v,w) = (\<Sum>x \<in> S.(\<Prod>i<l. count(edges G)(x!i,x!(i+1))))"
    (is "?L = ?R")
proof -
  interpret H:fin_digraph "graph_power G l" 
    using graph_power_fin by auto

  have 0:"finite {x. set x \<subseteq> verts G \<and> length x = l+1}"
    by (intro finite_lists_length_eq) auto
  have fin_S: "finite S"
    unfolding S_def by (intro finite_subset[OF _ 0]) auto

  have "?L = size {#x \<in># mset_set (arc_walks G l). fst x = v \<and> arc_walk_head G x = w#}"
    unfolding graph_power_def edges_def arc_to_ends_def 
    by (simp add:count_mset_exp image_mset_filter_mset_swap[symmetric])
  also have "... = size 
    {#x \<in># mset_set (arc_walks G l). awhd (fst x) (snd x) = v \<and> awlast (fst x) (snd x) = w#}"
    using awlast_of_arc_walk awhd_of_arc_walk arc_walks_fin
    by (intro arg_cong[where f="size"] filter_mset_cong refl) simp
  also have "... = size {#x \<in># walks G (l+1). hd x = v \<and> last x = w#}"
    unfolding arc_walks_map_walks 
    by (simp add:image_mset_filter_mset_swap[symmetric] case_prod_beta)
  also have "...=size{#x\<in># walks G (l+1).x \<in> S#}"
    unfolding S_def using set_walks_3
    by (intro arg_cong[where f="size"] filter_mset_cong refl) auto
  also have "...=sum (count (walks G (l+1))) S"
    by (intro sum_count_2[symmetric] fin_S) 
  also have "...=(\<Sum>x\<in>S.(\<Prod>i<l+1-1. count (edges G) (x!i,x!(i+1))))"
    unfolding S_def
    by (intro sum.cong refl count_walks) auto
  also have "...=?R"
    by simp
  finally show ?thesis by simp
qed

lemma (in fin_digraph) graph_power_sym_aux:
  assumes "symmetric_multi_graph G"
  assumes "v \<in> verts (graph_power G l)"  "w \<in> verts (graph_power G l)"
  shows "card (arcs_betw (graph_power G l) v w) = card (arcs_betw (graph_power G l) w v)" 
    (is "?L = ?R")
proof -
  interpret H:fin_digraph "graph_power G l" 
    using graph_power_fin by auto

  define S where "S v w = {x. length x=l+1 \<and> set x \<subseteq> verts G \<and> hd x = v \<and> last x = w}" for v w

  have 0: "bij_betw rev (S w v) (S v w)"
    unfolding S_def by (intro bij_betwI[where g="rev"]) (auto simp add:hd_rev last_rev) 

  have 1: "bij_betw ((-) (l - 1)) {..<l} {..<l}"
    by (intro bij_betwI[where g="\<lambda>x. (l-1-x)"]) auto

  have "?L = count (edges (graph_power G l)) (v, w)"
    unfolding H.count_edges by simp
  also have "... = (\<Sum>x \<in> S v w. (\<Prod>i<l. count (edges G) (x!i,x!(i+1))))"
    unfolding S_def graph_power_count_edges by simp
  also have "... = (\<Sum>x \<in> S w v. (\<Prod>i<l. count (edges G) (rev x!i,rev x!(i+1))))"
    by (intro sum.reindex_bij_betw[symmetric] 0) 
  also have "... = (\<Sum>x \<in> S w v. (\<Prod>i<l. count (edges G) (x!((l-1-i)+1),x!(l-1-i))))"
    unfolding S_def by (intro sum.cong refl prod.cong) (simp_all add: rev_nth Suc_diff_Suc) 
  also have "... = (\<Sum>x \<in> S w v. (\<Prod>i<l. count (edges G) (x!(i+1),x!i)))"
    by (intro sum.cong prod.reindex_bij_betw refl 1)
  also have "... = (\<Sum>x \<in> S w v. (\<Prod>i<l. count (edges G) (x!i,x!(i+1))))"
    by (intro sum.cong prod.cong count_edges_sym[OF assms(1)] refl)
  also have "... = count (edges (graph_power G l)) (w, v)"
    unfolding S_def graph_power_count_edges by simp
  also have "... = ?R"
    unfolding H.count_edges by simp
  finally show ?thesis by simp
qed

lemma (in fin_digraph) graph_power_sym:
  assumes "symmetric_multi_graph G"
  shows "symmetric_multi_graph (graph_power G l)"
proof -
  interpret H:fin_digraph "graph_power G l" 
    using graph_power_fin by auto

  show ?thesis
    using graph_power_sym_aux[OF assms]
    unfolding symmetric_multi_graph_def by auto
qed

lemma  (in fin_digraph) graph_power_out_degree':
  assumes reg: "\<And>v. v \<in> verts G \<Longrightarrow> out_degree G v = d"
  assumes "v \<in> verts (graph_power G l)"
  shows "out_degree (graph_power G l) v = d ^ l"  (is "?L = ?R")
proof -
  interpret H:fin_digraph "graph_power G l" 
    using graph_power_fin by auto

  have v_vert: "v \<in> verts G"
    using assms unfolding graph_power_def by simp

  have "?L = size (vertices_from (graph_power G l) v)"
    unfolding out_degree_def H.verts_from_alt by simp
  also have "... = size ({# e \<in># edges (graph_power G l). fst e = v #})"
    unfolding vertices_from_def by simp
  also have "... = size {#w \<in># mset_set (arc_walks G l). fst w = v#}"
    unfolding graph_power_def edges_def arc_to_ends_def 
    by (simp add:count_mset_exp image_mset_filter_mset_swap[symmetric])
  also have "... = size {#w \<in># mset_set (arc_walks G l). awhd (fst w) (snd w) = v#}"
    using awlast_of_arc_walk awhd_of_arc_walk arc_walks_fin
    by (intro arg_cong[where f="size"] filter_mset_cong refl) simp
  also have "... = size {#x \<in># walks' G l. hd x = v #}"
    unfolding arc_walks_map_walks' 
    by (simp add:image_mset_filter_mset_swap[symmetric] case_prod_beta)
  also have "... = d^l"
  proof (induction l)
    case 0
    have "size {#x \<in># walks' G 0. hd x = v#} = card {x. x = v \<and> x \<in> verts G}"
      by (simp add:image_mset_filter_mset_swap[symmetric])
    also have "... = card {v}"
      using v_vert by (intro arg_cong[where f="card"]) auto
    also have "... = d^0" by simp
    finally show ?case by simp
  next
    case (Suc l)
    have "size {#x \<in># walks' G (Suc l). hd x = v#} =
      (\<Sum>x\<in>#walks' G l. size {#y \<in># vertices_from G (last x). hd (x @ [y]) = v#})"
      by (simp add:size_concat_mset image_mset_filter_mset_swap[symmetric] 
          filter_concat_mset image_mset.compositionality comp_def)
    also have "... = (\<Sum>x\<in>#walks' G l. size {#y \<in># vertices_from G (last x). hd x = v#})"
      using set_walks_2 
      by (intro_cong "[\<sigma>\<^sub>1 sum_mset, \<sigma>\<^sub>1 size]" more:image_mset_cong filter_mset_cong) auto
    also have "... = (\<Sum>x\<in>#walks' G l. (if hd x = v then out_degree G (last x) else 0))"
      unfolding verts_from_alt out_degree_def
      by (simp add:filter_mset_const if_distribR if_distrib cong:if_cong)
    also have "... = (\<Sum>x\<in>#walks' G l. d * of_bool (hd x = v))"
      using set_walks_2[where l="l"] last_in_set
      by (intro arg_cong[where f="sum_mset"] image_mset_cong) (auto intro!:reg)
    also have "... = d * (\<Sum>x\<in>#walks' G l. of_bool (hd x = v))" 
      by (simp add:sum_mset_distrib_left image_mset.compositionality comp_def)
    also have "... = d * (size {#x \<in># walks' G l. hd x = v#})"
      by (simp add:size_filter_mset_conv)
    also have "... = d * d ^ l"
      using Suc by simp
    also have "... = d^Suc l"
      by simp
    finally show ?case by simp
  qed 

  finally show ?thesis by simp
qed

lemma  (in regular_graph) graph_power_out_degree:
  assumes "v \<in> verts (graph_power G l)"
  shows "out_degree (graph_power G l) v = d ^ l"  (is "?L = ?R")
  by (intro graph_power_out_degree' assms reg) auto

lemma (in regular_graph) graph_power_regular: 
  "regular_graph (graph_power G l)"
proof -
  interpret H:fin_digraph "graph_power G l" 
    using graph_power_fin by auto

  have "verts (graph_power G l) \<noteq> {}"
    using verts_non_empty unfolding graph_power_def by simp

  moreover have "0 < d^l"
    using d_gt_0 by simp

  ultimately show ?thesis
    using graph_power_out_degree
    by (intro regular_graphI[where d="d^l"] graph_power_sym sym)
qed

lemma (in regular_graph) graph_power_degree: 
  "regular_graph.d (graph_power G l) = d^l" (is "?L = ?R")
proof -
  interpret H:regular_graph "graph_power G l" 
    using graph_power_regular by auto
  obtain v where v_set: "v \<in> verts (graph_power G l)"
    using H.verts_non_empty by auto
  hence "?L = out_degree (graph_power G l) v" 
    using v_set H.reg by auto
  also have "... =?R"
    by (intro graph_power_out_degree[OF v_set]) 
  finally show ?thesis by simp
qed

lemma (in regular_graph) graph_power_step:
  assumes "x \<in> verts G"
  shows "regular_graph.g_step (graph_power G l) f x = (g_step^^l) f x"
  using assms
proof (induction l arbitrary: x)
  case 0
  let ?H = "graph_power G 0"
  interpret H:regular_graph "?H"
    using graph_power_regular by auto
  have "regular_graph.g_step (graph_power G 0) f x = H.g_step f x"
    by simp
  have "H.g_step f x = (\<Sum>x\<in>in_arcs ?H x. f (tail ?H x))"
    unfolding H.g_step_def graph_power_degree by simp
  also have "... = (\<Sum>v\<in>{e \<in> arc_walks G 0. arc_walk_head G e = x}. f (fst v))"
    unfolding in_arcs_def graph_power_def by (simp add:case_prod_beta)
  also have "... = (\<Sum>v\<in>{x}. f v)"
    unfolding arc_walks_def using 0
    by (intro sum.reindex_bij_betw bij_betwI[where g="(\<lambda>x. (x,[]))"])
      (auto simp add:arc_walk_head_def)
  also have "... = f x"
    by simp
  also have "... = (g_step^^0) f x"
    by simp
  finally show ?case by simp
next
  case (Suc l)
  let ?H = "graph_power G l"
  interpret H:regular_graph "?H"
    using graph_power_regular by auto
  let ?HS = "graph_power G (l+1)"
  interpret HS:regular_graph "?HS"
    using graph_power_regular by auto

  let ?bij = "(\<lambda>(x,(y1,y2)). (y1,y2@[x]))"
  let ?bijr = "(\<lambda>(y1,y2). (last y2, (y1,butlast y2)))"

  define S where "S = {y. fst y \<in> in_arcs G x \<and> snd y \<in> in_arcs ?H (tail G (fst y))}"

  have "S = {(u,v). u \<in> arcs G \<and> head G u = x \<and> v \<in> arc_walks G l \<and> arc_walk_head G v = tail G u}"
    unfolding S_def graph_power_def in_arcs_def by auto
  also have "... = {(u,v). (fst v,snd v@[u]) \<in> arc_walks G (l+1) \<and> arc_walk_head G (fst v,snd v@[u]) = x}"
    unfolding arc_walks_def by (intro iffD2[OF set_eq_iff] allI) 
      (auto simp add: is_arc_walk_snoc case_prod_beta arc_walk_head_def)
  also have "... = {(u,v). (fst v,snd v@[u]) \<in> in_arcs ?HS x}"
    unfolding in_arcs_def graph_power_def by auto
  finally have S_alt: "S = {(u,v). (fst v,snd v@[u]) \<in> in_arcs ?HS x}" by simp

  have len_in_arcs: "a \<in> in_arcs ?HS x \<Longrightarrow> snd a \<noteq> []" for a
    unfolding in_arcs_def graph_power_def arc_walks_def by auto

  have 0:"bij_betw ?bij S (in_arcs ?HS x)"
    unfolding S_alt using len_in_arcs
    by (intro bij_betwI[where g="?bijr"]) auto

  have "HS.g_step f x = (\<Sum>y\<in>in_arcs ?HS x. f (tail ?HS y)/ d^(l+1))"
    unfolding HS.g_step_def graph_power_degree by simp
  also have "... = (\<Sum>y\<in>in_arcs ?HS x. f (fst y)/ d^(l+1))"
    unfolding graph_power_def by simp
  also have "... = (\<Sum>y \<in> S. f (fst (?bij y))/ d^(l+1))" 
    by (intro sum.reindex_bij_betw[symmetric] 0)
  also have "... = (\<Sum>y \<in> S. f (fst (snd y))/ d^(l+1))" 
    by (intro_cong "[\<sigma>\<^sub>2 (/),\<sigma>\<^sub>1 f]" more: sum.cong) (simp add:case_prod_beta)
  also have "...=(\<Sum>y\<in>(\<Union>a\<in>in_arcs G x. (Pair a)`in_arcs ?H (tail G a)). f (fst (snd y))/ d^(l+1))" 
    unfolding S_def by (intro sum.cong) auto
  also have "...=(\<Sum>a\<in>in_arcs G x. (\<Sum>y\<in>(Pair a)`in_arcs ?H (tail G a). f (fst (snd y))/ d^(l+1)))"
    by (intro sum.UNION_disjoint) auto
  also have "... = (\<Sum>a \<in> in_arcs G x. (\<Sum>b \<in> in_arcs ?H (tail G a). f (fst b) / d^(l+1)))" 
    by (intro sum.cong sum.reindex_bij_betw) (auto simp add:bij_betw_def inj_on_def image_iff)
  also have "... = (\<Sum>a \<in> in_arcs G x. (\<Sum>b \<in> in_arcs ?H (tail G a). f (tail ?H b) / d^l)/d)" 
    unfolding graph_power_def
    by (simp add:sum_divide_distrib algebra_simps)
  also have "... = (\<Sum>a \<in> in_arcs G x. H.g_step f (tail G a)/ d)" 
    unfolding H.g_step_def graph_power_degree by simp
  also have "... = (\<Sum>a \<in> in_arcs G x. (g_step^^l) f (tail G a)/ d)"
    by (intro sum.cong refl arg_cong2[where f="(/)"] Suc) auto
  also have "... = g_step ((g_step^^l) f) x"
    unfolding g_step_def by simp
  also have "... = (g_step^^(l+1)) f x"
    by simp
  finally show ?case by simp
qed

lemma (in regular_graph) graph_power_expansion:
  "regular_graph.\<Lambda>\<^sub>a (graph_power G l) \<le> \<Lambda>\<^sub>a^l"
proof -
  interpret H:regular_graph "graph_power G l" 
    using graph_power_regular by auto

  have "\<bar>H.g_inner f (H.g_step f)\<bar> \<le> \<Lambda>\<^sub>a ^ l * (H.g_norm f)\<^sup>2" (is "?L \<le> ?R")
    if "H.g_inner f (\<lambda>_. 1) = 0"  for f
  proof -
    have "g_inner f (\<lambda>_. 1) = H.g_inner f (\<lambda>_.1)"
      unfolding g_inner_def H.g_inner_def
      by (intro sum.cong) (auto simp add:graph_power_def)
    also have "... = 0" using that by simp
    finally have 1:"g_inner f (\<lambda>_. 1) = 0" by simp

    have 2: "g_inner ((g_step^^l) f) (\<lambda>_. 1) = 0" for l
      using g_step_remains_orth 1 by (induction l, auto)

    have 0: "g_norm ((g_step^^l) f) \<le> \<Lambda>\<^sub>a ^ l * g_norm f"
    proof (induction l)
      case 0
      then show ?case by simp
    next
      case (Suc l)
      have "g_norm ((g_step ^^ Suc l) f) = g_norm (g_step ((g_step ^^ l) f))"
        by simp
      also have "... \<le> \<Lambda>\<^sub>a * g_norm (((g_step ^^ l) f))"
        by (intro expansionD2 2)
      also have "... \<le> \<Lambda>\<^sub>a * (\<Lambda>\<^sub>a^l * g_norm f)"
        by (intro mult_left_mono \<Lambda>_ge_0 Suc)
      also have "... = \<Lambda>\<^sub>a^(l+1) * g_norm f" by simp
      finally show ?case by simp
    qed

    have "?L = \<bar>g_inner f (H.g_step f)\<bar>"
      unfolding H.g_inner_def g_inner_def 
      by (intro_cong "[\<sigma>\<^sub>1 abs]" more:sum.cong) (auto simp add:graph_power_def)
    also have "... = \<bar>g_inner f ((g_step^^l) f)\<bar>"
      by (intro_cong "[\<sigma>\<^sub>1 abs]" more:g_inner_cong graph_power_step) auto
    also have "... \<le> g_norm f * g_norm ((g_step^^l) f)"
      by (intro g_inner_cauchy_schwartz)
    also have "... \<le> g_norm f * (\<Lambda>\<^sub>a ^ l * g_norm f)"
      by (intro mult_left_mono 0 g_norm_nonneg) 
    also have "... = \<Lambda>\<^sub>a ^ l * g_norm f^2"
      by (simp add:power2_eq_square)
    also have "... = ?R" 
      unfolding g_norm_sq H.g_norm_sq g_inner_def H.g_inner_def
      by (intro_cong "[\<sigma>\<^sub>2 (*)]" more:sum.cong) (auto simp add:graph_power_def)
    finally show ?thesis by simp
  qed
  moreover have " 0 \<le> \<Lambda>\<^sub>a ^ l" 
    using \<Lambda>_ge_0 by simp

  ultimately show ?thesis
    by (intro H.expander_intro_1) auto 
qed

unbundle no_intro_cong_syntax

end