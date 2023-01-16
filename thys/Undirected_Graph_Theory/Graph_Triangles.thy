(* Theory: Graph_Triangles.thy 
   Author: Chelsea Edmonds *)

section \<open> Triangles in Graph \<close>
text \<open> Triangles are an important tool in graph theory. This theory presents a number of basic 
definitions/lemmas which are useful for general reasoning using triangles. The definitions and lemmas
in this theory are adapted from previous less general work in \<^cite>\<open>"edmonds_szemeredis"\<close> and \<^cite>\<open>"edmonds_roths"\<close>\<close>
theory Graph_Triangles imports Undirected_Graph_Basics
      "HOL-Combinatorics.Multiset_Permutations"
begin

text \<open> Triangles don't make as much sense in a loop context, hence we restrict this to simple graphs \<close>
context sgraph
begin

definition triangle_in_graph :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where 
"triangle_in_graph x y z \<equiv> ({x,y} \<in> E) \<and> ({y,z} \<in> E) \<and> ({x,z} \<in>E)"

lemma triangle_in_graph_edge_empty: "E = {} \<Longrightarrow> \<not> triangle_in_graph x y z"
  using triangle_in_graph_def by auto

definition triangle_triples where
"triangle_triples X Y Z \<equiv> {(x,y,z) \<in> X \<times> Y \<times> Z. triangle_in_graph x y z }"

definition 
  "unique_triangles 
    \<equiv> \<forall>e \<in> E. \<exists>!T. \<exists>x y z. T = {x,y,z} \<and> triangle_in_graph x y z  \<and> e \<subseteq> T"

definition triangle_set :: "'a set set"
  where "triangle_set \<equiv> { {x,y,z} | x y z. triangle_in_graph x y z}"

subsection \<open>Preliminaries on Triangles in Graphs\<close>

lemma card_triangle_triples_rotate: "card (triangle_triples X Y Z) = card (triangle_triples Y Z X)"
proof -
  have "triangle_triples Y Z X = (\<lambda>(x,y,z). (y,z,x)) ` triangle_triples X Y Z"
    by (auto simp: triangle_triples_def case_prod_unfold image_iff insert_commute triangle_in_graph_def)
  moreover have "inj_on (\<lambda>(x, y, z). (y, z, x)) (triangle_triples X Y Z)"
    by (auto simp: inj_on_def)
  ultimately show ?thesis
    by (simp add: card_image)
qed

lemma triangle_commu1:
  assumes "triangle_in_graph x y z"
  shows "triangle_in_graph y x z"
  using assms triangle_in_graph_def by (auto simp add: insert_commute)

lemma triangle_vertices_distinct1:
  assumes tri: "triangle_in_graph x y z"
  shows "x \<noteq> y"
proof (rule ccontr)
  assume a: "\<not> x \<noteq> y"
  have "card {x, y} = 2" using tri triangle_in_graph_def
    using wellformed by (simp add: two_edges) 
  thus False using a by simp
qed

lemma triangle_vertices_distinct2: 
  assumes "triangle_in_graph x y z"
  shows "y \<noteq> z"
  by (metis assms triangle_vertices_distinct1 triangle_in_graph_def) 

lemma triangle_vertices_distinct3: 
  assumes "triangle_in_graph x y z"
  shows "z \<noteq> x"
  by (metis assms triangle_vertices_distinct1 triangle_in_graph_def) 

lemma triangle_in_graph_edge_point: "triangle_in_graph x y z \<longleftrightarrow> {y, z} \<in> E \<and> vert_adj x y \<and> vert_adj x z"
  by (auto simp add: triangle_in_graph_def vert_adj_def)

lemma edge_vertices_not_equal: 
  assumes "{x,y} \<in> E"
  shows "x \<noteq> y"
  using assms two_edges by fastforce 

lemma edge_btw_vertices_not_equal: 
  assumes "(x, y) \<in> all_edges_between X Y"
  shows "x \<noteq> y"
  using edge_vertices_not_equal all_edges_between_def
  by (metis all_edges_betw_D3 assms) 

lemma mk_triangle_from_ss_edges: 
assumes "(x, y) \<in> all_edges_between X Y" and "(x, z) \<in> all_edges_between X Z" and "(y, z) \<in> all_edges_between Y Z" 
shows "(triangle_in_graph x y z)"
  by (meson all_edges_betw_D3 assms triangle_in_graph_def)

lemma triangle_in_graph_verts: 
  assumes "triangle_in_graph x y z "
  shows "x \<in> V" "y \<in> V" "z\<in> V"
proof -
  show "x \<in> V" using triangle_in_graph_def wellformed_alt_fst assms by blast
  show "y \<in> V" using triangle_in_graph_def wellformed_alt_snd assms by blast
  show "z \<in> V" using triangle_in_graph_def wellformed_alt_snd assms by blast
qed

lemma convert_triangle_rep_ss: 
  assumes "X \<subseteq> V" and "Y \<subseteq> V" and "Z \<subseteq> V"
  shows "mk_triangle_set ` {(x, y, z) \<in> X \<times> Y \<times> Z . (triangle_in_graph x y z)} \<subseteq> triangle_set"
  by (auto simp add: subsetI triangle_set_def) (auto)

lemma (in fin_sgraph) finite_triangle_set:  "finite (triangle_set)"
proof -
  have "triangle_set  \<subseteq> Pow V"
  using insert_iff wellformed triangle_in_graph_def triangle_set_def by auto
  then show ?thesis
    by (meson finV finite_Pow_iff infinite_super)
qed

lemma card_triangle_3: 
  assumes "t \<in> triangle_set" 
  shows "card t = 3"
  using assms by (auto simp: triangle_set_def edge_vertices_not_equal triangle_in_graph_def)

lemma triangle_set_power_set_ss: "triangle_set \<subseteq> Pow V"
  by (auto simp add: triangle_set_def triangle_in_graph_def wellformed_alt_fst wellformed_alt_snd)

lemma triangle_in_graph_ss: 
  assumes "E' \<subseteq> E" 
  assumes "sgraph.triangle_in_graph E' x y z"
  shows "triangle_in_graph x y z"
proof -
  interpret gnew: sgraph V E' 
    apply (unfold_locales)
    using assms wellformed two_edges by auto
  have "{x, y} \<in> E" using assms gnew.triangle_in_graph_def by auto 
  have "{y, z} \<in> E" using assms gnew.triangle_in_graph_def by auto 
  have "{x, z} \<in> E" using assms gnew.triangle_in_graph_def by auto 
  thus ?thesis
    by (simp add: \<open>{x, y} \<in> E\<close> \<open>{y, z} \<in> E\<close> triangle_in_graph_def) 
qed

lemma triangle_set_graph_edge_ss: 
  assumes "E' \<subseteq> E" 
  shows "(sgraph.triangle_set E') \<subseteq> (triangle_set)"
proof (intro subsetI)
  interpret gnew: sgraph V E' 
    using assms wellformed two_edges by (unfold_locales) auto
  fix t assume "t \<in> gnew.triangle_set" 
  then obtain x y z where "t = {x,y,z}" and "gnew.triangle_in_graph x y z"
    using gnew.triangle_set_def assms mem_Collect_eq by auto
  then have "triangle_in_graph x y z" using assms triangle_in_graph_ss by simp
  thus "t \<in> triangle_set" using triangle_set_def assms
    using \<open>t = {x,y,z}\<close> by auto 
qed

lemma (in fin_sgraph) triangle_set_graph_edge_ss_bound: 
  assumes "E' \<subseteq> E" 
  shows "card (triangle_set) \<ge> card (sgraph.triangle_set E')"
  using triangle_set_graph_edge_ss finite_triangle_set
  by (simp add: assms card_mono)

end

locale triangle_free_graph = sgraph + 
  assumes tri_free: "\<not>(\<exists> x y z. triangle_in_graph x y z)"

lemma triangle_free_graph_empty: "E = {} \<Longrightarrow> triangle_free_graph V E"
  apply (unfold_locales, simp_all)
  using sgraph.triangle_in_graph_edge_empty
  by (metis Int_absorb all_edges_disjoint complete_sgraph) 

context fin_sgraph
begin

text \<open>Converting between ordered and unordered triples for reasoning on cardinality\<close>
lemma card_convert_triangle_rep:
  assumes "X \<subseteq> V" and "Y \<subseteq> V" and "Z \<subseteq> V"
  shows "card (triangle_set) \<ge> 1/6 * card {(x, y, z) \<in> X \<times> Y \<times> Z . (triangle_in_graph x y z)}"
         (is  "_ \<ge> 1/6 * card ?TT")
proof -
  define tofl where "tofl \<equiv> \<lambda>l::'a list. (hd l, hd(tl l), hd(tl(tl l)))"
  have in_tofl: "(x, y, z) \<in> tofl ` permutations_of_set {x,y,z}" if "x\<noteq>y" "y\<noteq>z" "x\<noteq>z" for x y z
  proof -
    have "distinct[x,y,z]"
      using that by simp
    then show ?thesis
      unfolding tofl_def image_iff
      by (smt (verit, best) list.sel(1) list.sel(3) list.simps(15) permutations_of_setI set_empty)
  qed
  have "?TT \<subseteq> {(x, y, z). (triangle_in_graph x y z)}"
    by auto
  also have "\<dots> \<subseteq> (\<Union>t \<in> triangle_set. tofl ` permutations_of_set t)"
  proof (clarsimp simp: triangle_set_def)
    fix u v w
    assume t: "triangle_in_graph u v w"
    then have "(u, v, w) \<in> tofl ` permutations_of_set {u,v,w}"
      by (metis in_tofl triangle_commu1 triangle_vertices_distinct1 triangle_vertices_distinct2)
    with t show "\<exists>t. (\<exists>x y z. t = {x, y, z} \<and> triangle_in_graph x y z) \<and> (u, v, w) \<in> tofl ` permutations_of_set t"
      by blast
  qed
  finally have "?TT \<subseteq> (\<Union>t \<in> triangle_set. tofl ` permutations_of_set t)" .
  then have "card ?TT \<le> card(\<Union>t \<in> triangle_set. tofl ` permutations_of_set t)" 
    by (intro card_mono finite_UN_I finite_triangle_set) (auto simp: assms)
  also have "\<dots> \<le> (\<Sum>t \<in> triangle_set. card (tofl ` permutations_of_set t))"
    using card_UN_le finV finite_triangle_set wellformed by blast
  also have "\<dots> \<le> (\<Sum>t \<in> triangle_set. card (permutations_of_set t))"
    by (meson card_image_le finite_permutations_of_set sum_mono)
  also have "\<dots> \<le> (\<Sum>t \<in> triangle_set. fact 3)"
    by(rule sum_mono) (metis card.infinite card_permutations_of_set card_triangle_3 eq_refl nat.simps(3) numeral_3_eq_3)
  also have "\<dots> = 6 * card (triangle_set)"
    by (simp add: eval_nat_numeral)
  finally have "card ?TT \<le> 6 * card (triangle_set)" .
  then show ?thesis
    by (simp add: divide_simps)
qed

lemma card_convert_triangle_rep_bound: 
  fixes t :: real
  assumes "card {(x, y, z) \<in> X \<times> Y \<times> Z . (triangle_in_graph x y z)} \<ge> t"
  assumes "X \<subseteq> V" and "Y \<subseteq> V" and "Z \<subseteq> V" 
  shows "card (triangle_set) \<ge> 1/6 *t"
proof -
  define t' where "t' \<equiv> card {(x, y, z) \<in> X \<times> Y \<times> Z . (triangle_in_graph x y z)}"
  have "t' \<ge> t" using assms t'_def by simp
  then have tgt: "1/6 * t' \<ge> 1/6 * t" by simp
  have "card (triangle_set) \<ge> 1/6 *t'" using t'_def card_convert_triangle_rep assms by simp
  thus ?thesis using tgt by linarith
qed
end
end