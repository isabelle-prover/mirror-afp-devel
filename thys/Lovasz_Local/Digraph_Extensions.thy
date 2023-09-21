(* Theory: Digraph_Extensions
   Author: Chelsea Edmonds *)

section \<open>Digraph extensions\<close>
text \<open>Extensions to the existing library for directed graphs, basically neighborhood \<close>

theory Digraph_Extensions 
  imports 
    Graph_Theory.Digraph 
    Graph_Theory.Pair_Digraph
begin

definition (in pre_digraph) neighborhood :: "'a \<Rightarrow> 'a set" where
"neighborhood  u \<equiv> {v \<in> verts G . dominates G u v}"

lemma (in wf_digraph) neighborhood_wf: "neighborhood v \<subseteq> verts G"
  unfolding neighborhood_def by auto

lemma (in pair_pre_digraph) neighborhood_alt: 
"neighborhood u = {v \<in> pverts G . (u, v) \<in> parcs G}"
  unfolding neighborhood_def by simp

lemma (in fin_digraph) neighborhood_finite: "finite (neighborhood v)"
  using neighborhood_wf finite_subset finite_verts by fast

lemma (in wf_digraph) neighborhood_edge_iff:  "y \<in> neighborhood x \<longleftrightarrow> (x, y) \<in> arcs_ends G"
  unfolding neighborhood_def using in_arcs_imp_in_arcs_ends by auto

lemma (in loopfree_digraph) neighborhood_self_not: "v \<notin> (neighborhood v)"
  unfolding neighborhood_def using adj_not_same by auto

lemma (in nomulti_digraph) inj_on_head_out_arcs: "inj_on (head G) (out_arcs G u)"
proof (intro inj_onI)
  fix x y assume xin: "x \<in> out_arcs G u" and yin: "y \<in> out_arcs G u" and heq: "head G x = head G y"
  then have "tail G x = u" "tail G y = u"
    using out_arcs_def by auto
  then have "arc_to_ends G x = arc_to_ends G y" 
    unfolding arc_to_ends_def  heq by auto
  then show " x = y" using no_multi_arcs xin yin by simp
qed

lemma (in nomulti_digraph) out_degree_neighborhood: "out_degree G u = card (neighborhood u)"
proof -
  let ?f = "\<lambda> e. head G e"
  have "bij_betw ?f (out_arcs G u) (neighborhood u)"
  proof (intro bij_betw_imageI)
    show "inj_on (head G) (out_arcs G u)" using inj_on_head_out_arcs by simp
    show "head G ` out_arcs G u = neighborhood u" 
      unfolding neighborhood_def using in_arcs_imp_in_arcs_ends by auto
  qed
  then show ?thesis unfolding out_degree_def
    by (simp add: bij_betw_same_card) 
qed

lemma (in digraph) neighborhood_empty_iff: "out_degree G u = 0 \<longleftrightarrow> neighborhood u = {}"
  using out_degree_neighborhood neighborhood_finite by auto

end