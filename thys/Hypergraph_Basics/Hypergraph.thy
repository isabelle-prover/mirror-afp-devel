(* Theory: Hypergraph
   Author: Chelsea Edmonds *)

section \<open>Basic Hypergraphs \<close>

text \<open>Converting Design theory to hypergraph notation. Hypergraphs have technically already
been formalised\<close>

theory Hypergraph
  imports 
    "Design_Theory.Block_Designs" 
    "Design_Theory.Sub_Designs" 
    "Fishers_Inequality.Design_Extras"
begin

lemma is_singleton_image: 
  "is_singleton C \<Longrightarrow> is_singleton (f ` C)"
  by (metis image_empty image_insert is_singletonE is_singletonI)

lemma bij_betw_singleton_image: 
  assumes "bij_betw f A B"
  assumes "C \<subseteq> A"
  shows "is_singleton C \<longleftrightarrow> is_singleton (f ` C)"
proof (intro iffI)
  show " is_singleton C \<Longrightarrow> is_singleton (f ` C)" by (rule is_singleton_image)
  show "is_singleton (f ` C) \<Longrightarrow> is_singleton C " using assms is_singleton_image
    by (metis bij_betw_def inv_into_image_cancel)
qed

lemma image_singleton: 
  assumes "A \<noteq> {}"
  assumes "\<And> x. x \<in> A \<Longrightarrow> f x = c"
  shows "f ` A = {c}"
  using assms(1) assms(2) by blast

type_synonym colour = nat

type_synonym 'a hyp_edge = "'a set"

type_synonym 'a hyp_graph = "('a set) \<times> ('a hyp_edge multiset)"

abbreviation hyp_edges :: "'a hyp_graph \<Rightarrow> 'a hyp_edge multiset" where
  "hyp_edges H \<equiv> snd H"

abbreviation hyp_verts :: "'a hyp_graph \<Rightarrow> 'a set" where
  "hyp_verts H \<equiv> fst H"

locale hypersystem = incidence_system "vertices :: 'a set" "edges :: 'a hyp_edge multiset" 
  for "vertices" ("\<V>") and "edges" ("E") 

begin

text\<open>Basic definitions using hypergraph language\<close>

abbreviation horder :: "nat" where
"horder \<equiv> card (\<V>)"

definition hdegree :: "'a \<Rightarrow> nat" where
"hdegree v \<equiv> size {#e \<in># E . v \<in> e #}"

lemma hdegree_rep_num: "hdegree v = point_replication_number E v"
  unfolding hdegree_def point_replication_number_def by simp

definition hdegree_set :: "'a set \<Rightarrow> nat" where
"hdegree_set vs \<equiv> size {#e \<in># E. vs \<subseteq> e#}"

lemma hdegree_set_points_index: "hdegree_set vs = points_index E vs"
  unfolding hdegree_set_def points_index_def by simp

definition hvert_adjacent :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
"hvert_adjacent v1 v2 \<equiv> \<exists> e . e \<in># E \<and> v1 \<in> e \<and> v2 \<in> e \<and> v1 \<in> \<V> \<and> v2 \<in> \<V>"

definition hedge_adjacent :: "'a hyp_edge \<Rightarrow> 'a hyp_edge \<Rightarrow> bool" where
"hedge_adjacent e1 e2 \<equiv> e1 \<inter> e2 \<noteq> {} \<and> e1 \<in># E \<and> e2 \<in># E"

lemma edge_adjacent_alt_def: "e1 \<in># E \<Longrightarrow> e2 \<in># E \<Longrightarrow> \<exists> x . x \<in> \<V> \<and> x \<in> e1 \<and> x \<in> e2 \<Longrightarrow> 
    hedge_adjacent e1 e2"
  unfolding hedge_adjacent_def by auto

definition hneighborhood :: "'a \<Rightarrow> 'a set" where
"hneighborhood x \<equiv> {v \<in> \<V> . hvert_adjacent x v}"

definition hmax_degree :: "nat" where
"hmax_degree \<equiv> Max {hdegree v | v. v \<in> \<V>}"

definition hrank :: "nat" where
"hrank \<equiv> Max {card e | e . e \<in># E}"

definition hcorank :: "nat" where
"hcorank = Min {card e | e . e \<in># E}"

definition hedge_neighbourhood :: "'a \<Rightarrow> 'a hyp_edge multiset" where
"hedge_neighbourhood x \<equiv> {# e \<in># E . x \<in> e #}"

lemma degree_alt_neigbourhood: "hdegree x = size (hedge_neighbourhood x)"
  using hedge_neighbourhood_def by (simp add: hdegree_def) 

definition hinduced_edges:: "'a set \<Rightarrow> 'a hyp_edge multiset" where
"hinduced_edges V' = {#e \<in># E . e \<subseteq> V'#}"

end

text\<open>Sublocale for rewriting definition purposes rather than inheritance\<close>
sublocale hypersystem \<subseteq> incidence_system \<V> E
  rewrites "point_replication_number E v = hdegree v" and "points_index E vs = hdegree_set vs"
  by (unfold_locales) (simp_all add: hdegree_rep_num hdegree_set_points_index)

text \<open>Reverse sublocale to establish equality \<close>
sublocale incidence_system \<subseteq> hypersystem \<V> \<B>
  rewrites "hdegree v = point_replication_number \<B> v" and "hdegree_set vs = points_index \<B> vs"
proof (unfold_locales)
  interpret hs: hypersystem \<V> \<B> by (unfold_locales)
  show "hs.hdegree v = \<B> rep v" using hs.hdegree_rep_num by simp
  show " hs.hdegree_set vs = \<B> index vs" using hs.hdegree_set_points_index by simp
qed

text\<open>Missing design identified in the design theory hierarchy \<close>
locale inf_design = incidence_system + 
  assumes blocks_nempty: "bl \<in># \<B> \<Longrightarrow> bl \<noteq> {}"

sublocale design \<subseteq> inf_design
  by unfold_locales (simp add: blocks_nempty)

locale fin_hypersystem = hypersystem + finite_incidence_system \<V> E

sublocale finite_incidence_system \<subseteq> fin_hypersystem \<V> \<B>
  by unfold_locales

locale hypergraph = hypersystem + inf_design \<V> E

sublocale inf_design \<subseteq> hypergraph \<V> \<B>
  by unfold_locales (simp add: wellformed)

locale fin_hypergraph = hypergraph + fin_hypersystem

sublocale design \<subseteq> fin_hypergraph \<V> \<B>
  by unfold_locales

sublocale fin_hypergraph \<subseteq> design \<V> E
  using blocks_nempty by (unfold_locales) simp

subsection \<open>Sub hypergraphs\<close>
text \<open>Sub hypergraphs and related concepts (spanning hypergraphs etc)\<close>

locale sub_hypergraph = sub: hypergraph \<V>H EH + orig: hypergraph "\<V> :: 'a set" E + 
  sub_set_system \<V>H EH \<V> E for \<V>H EH \<V> E 

locale spanning_hypergraph = sub_hypergraph + 
  assumes "\<V> = \<V>H"

lemma spanning_hypergraphI:  "sub_hypergraph VH EH V E \<Longrightarrow> V = VH \<Longrightarrow> spanning_hypergraph VH EH V E"
  using spanning_hypergraph_def spanning_hypergraph_axioms_def by blast

context hypergraph
begin

definition is_subhypergraph :: "'a hyp_graph \<Rightarrow> bool" where
"is_subhypergraph H \<equiv> sub_hypergraph (hyp_verts H) (hyp_edges H) \<V> E"

lemma is_subhypergraphI: 
  assumes "(hyp_verts H \<subseteq> \<V>)"
  assumes "(hyp_edges H \<subseteq># E)"
  assumes "hypergraph (hyp_verts H) (hyp_edges H)"
  shows "is_subhypergraph H"
  unfolding is_subhypergraph_def 
proof -
  interpret h: hypergraph "hyp_verts H" "hyp_edges H"
    using assms(3) by simp
  show "sub_hypergraph (hyp_verts H) (hyp_edges H) \<V> E"
    by (unfold_locales) (simp_all add: assms)
qed

definition hypergraph_decomposition :: "'a hyp_graph multiset \<Rightarrow> bool" where
"hypergraph_decomposition S \<equiv> (\<forall> h \<in># S . is_subhypergraph  h) \<and> 
  partition_on_mset E {#hyp_edges h . h \<in># S#}"

definition is_spanning_subhypergraph :: "'a hyp_graph \<Rightarrow> bool" where
"is_spanning_subhypergraph H \<equiv> spanning_hypergraph (hyp_verts H) (hyp_edges H) \<V> E"

lemma is_spanning_subhypergraphI: "is_subhypergraph H \<Longrightarrow> (hyp_verts H) = \<V> \<Longrightarrow> 
    is_spanning_subhypergraph H"
  unfolding is_subhypergraph_def is_spanning_subhypergraph_def using spanning_hypergraphI by blast

lemma spanning_subhypergraphI:  "(hyp_verts H) = \<V> \<Longrightarrow> (hyp_edges H) \<subseteq># E \<Longrightarrow>
  hypergraph (hyp_verts H) (hyp_edges H) \<Longrightarrow> is_spanning_subhypergraph H"
  using is_spanning_subhypergraphI by (simp add: is_subhypergraphI)

end
end