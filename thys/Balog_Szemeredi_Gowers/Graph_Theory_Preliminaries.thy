section\<open>Background material for the graph-theoretic aspects of the main proof\<close>
text \<open>This section includes a number of lemmas on project specific definitions for graph theory, 
building on the general undirected graph theory library \cite{Undirected_Graph_Theory-AFP} \<close>

(*
  Session: Balog_Szemeredi_Gowers
  Title:   Graph_Theory_Preliminaries.thy
  Authors: Angeliki Koutsoukou-Argyraki, Mantas Bakšys, and Chelsea Edmonds
  Affiliation: University of Cambridge
  Date: August 2022.
*)

theory Graph_Theory_Preliminaries
  imports 
    Miscellaneous_Lemmas
    Undirected_Graph_Theory.Bipartite_Graphs
    Undirected_Graph_Theory.Connectivity
    Random_Graph_Subgraph_Threshold.Ugraph_Misc
begin

subsection\<open>On graphs with loops\<close>

context ulgraph

begin

definition degree_normalized:: "'a \<Rightarrow> 'a set \<Rightarrow> real" where 
  "degree_normalized v S \<equiv> card (neighbors_ss v S) / (card S)"

lemma degree_normalized_le_1: "degree_normalized x S \<le> 1"

proof(cases "finite S")
  assume hA: "finite S"
  then have "card (neighbors_ss x S) \<le> card S" using neighbors_ss_def card_mono hA 
    by fastforce
  then show ?thesis using degree_normalized_def divide_le_eq_1
    by (metis antisym_conv3 of_nat_le_iff of_nat_less_0_iff)
next
  case False
  then show ?thesis using degree_normalized_def by auto
qed

end

subsection\<open>On bipartite graphs \<close>


context bipartite_graph
begin

(* codegree counts the number of paths between two vertices, including loops *)
definition codegree:: "'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "codegree v u \<equiv> card {x \<in> V . vert_adj v x \<and> vert_adj u x}"

lemma codegree_neighbors: "codegree v u = card (neighborhood v \<inter> neighborhood u)"
  unfolding codegree_def neighborhood_def 

proof -
  have "{x \<in> V. vert_adj v x \<and> vert_adj u x} = {va \<in> V. vert_adj v va} \<inter> {v \<in> V. vert_adj u v}"
    by blast
  thus "card {x \<in> V. vert_adj v x \<and> vert_adj u x} = card ({va \<in> V. vert_adj v va} \<inter> {v \<in> V. vert_adj u v})"
    by auto
qed

lemma codegree_sym: "codegree v u = codegree u v"
  by (simp add: Int_commute codegree_neighbors) 

definition codegree_normalized:: "'a \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> real" where 
  "codegree_normalized v u S \<equiv> codegree v u / card S"

lemma codegree_normalized_altX: 
  assumes "x \<in> X" and "x' \<in> X"
  shows "codegree_normalized x x' Y = card (neighbors_ss x Y \<inter> neighbors_ss x' Y) / card Y"

proof -
  have "((neighbors_ss x Y) \<inter> (neighbors_ss x' Y)) = neighborhood x \<inter> neighborhood x'"
    using neighbors_ss_eq_neighborhoodX assms by auto
  then show ?thesis unfolding codegree_normalized_def
    using codegree_def codegree_neighbors by presburger 
qed

lemma codegree_normalized_altY: 
  assumes "y \<in> Y" and "y' \<in> Y"
  shows "codegree_normalized y y' X = card (neighbors_ss y X \<inter> neighbors_ss y' X) / card X"

proof -
  have "neighbors_ss y X \<inter> neighbors_ss y' X = neighborhood y \<inter> neighborhood y'"
    using neighbors_ss_eq_neighborhoodY assms by auto
  then show ?thesis unfolding codegree_normalized_def
    using codegree_def codegree_neighbors by presburger 
qed

lemma codegree_normalized_sym: "codegree_normalized u v S = codegree_normalized v u S"
  unfolding codegree_normalized_def using codegree_sym by simp

definition bad_pair:: " 'a \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> real \<Rightarrow> bool" where 
  "bad_pair v u S c \<equiv> codegree_normalized v u S < c"

lemma bad_pair_sym: 
  assumes "bad_pair v u S c" shows "bad_pair u v S c"
  using assms bad_pair_def codegree_normalized_def
  by (simp add: codegree_normalized_sym)

definition bad_pair_set:: "'a set \<Rightarrow> 'a set \<Rightarrow> real \<Rightarrow> ('a \<times> 'a) set" where 
  "bad_pair_set S T c  \<equiv> {(u, v) \<in> S \<times> S. bad_pair u v T c}"

lemma bad_pair_set_ss: "bad_pair_set S T c \<subseteq> S \<times> S"
  by (auto simp add: bad_pair_set_def)

lemma bad_pair_set_filter_alt: 
  "bad_pair_set S T c = Set.filter (\<lambda> p . bad_pair (fst p) (snd p) T c) (S \<times> S)" 
  using bad_pair_set_def by auto

lemma bad_pair_set_finite: 
  assumes "finite S"
  shows "finite (bad_pair_set S T c)"
proof -
  have "finite (S \<times> S)" using finite_cartesian_product assms by blast
  thus ?thesis using bad_pair_set_filter_alt finite_filter by auto
qed

lemma codegree_is_path_length_two:
  "codegree x x' = card {p . connecting_path x x' p \<and> walk_length p = 2}" 
  unfolding codegree_def 
proof-
  define f:: "'a list \<Rightarrow> 'a" where "f = (\<lambda> p. p!1)"
  have f_inj: "inj_on f {p . connecting_path x x' p \<and> walk_length p = 2}"
    unfolding f_def 
  proof (intro inj_onI, simp del: One_nat_def)
    fix a b assume ha: "connecting_path x x' a \<and> walk_length a = 2" and 
      hb: "connecting_path x x' b \<and> walk_length b = 2" and 1: "a!1 = b!1"
    then have len: "length a = 3" "length b = 3" using walk_length_conv by auto
    show "a = b" using list2_middle_singleton 1 len list_middle_eq ha hb connecting_path_def len by metis 
  qed
  have f_image: "f ` {p . connecting_path x x' p \<and> walk_length p = 2} = 
    {xa \<in> V. vert_adj x xa \<and> vert_adj x' xa}"
  proof(intro subset_antisym)
    show "f ` {p. connecting_path x x' p \<and> walk_length p = 2}
    \<subseteq> {xa \<in> V. vert_adj x xa \<and> vert_adj x' xa}"
    proof (intro subsetI)
      fix a assume "a \<in> f ` {p. connecting_path x x' p \<and> walk_length p = 2}"
      then obtain p where ha: "p!1 = a" and hp: "connecting_path x x' p" and hpl: "length p = 3" 
        using f_def walk_length_conv by auto
      have "p ! 0 = x" using hd_conv_nth[of p] hpl hp connecting_path_def by fastforce 
      then have va1: "vert_adj x a" using is_walk_index[of 0 p] hp connecting_path_def is_gen_path_def 
          vert_adj_def ha hpl by auto
      have "p ! 2 = x'" using last_conv_nth[of p] hpl hp connecting_path_def by fastforce
      then have "vert_adj a x'" using is_walk_index[of 1 p] hp connecting_path_def is_gen_path_def 
          vert_adj_def ha hpl by (metis One_nat_def le0 lessI numeral_3_eq_3 one_add_one)
      then show "a \<in> {a \<in> V. vert_adj x a \<and> vert_adj x' a}" 
        using va1 vert_adj_sym by (simp add: vert_adj_imp_inV)
    qed
    show "{xa \<in> V. vert_adj x xa \<and> vert_adj x' xa}
      \<subseteq> f ` {p. connecting_path x x' p \<and> walk_length p = 2}"
    proof (intro subsetI)
      fix a assume ha: "a \<in> {xa \<in> V. vert_adj x xa \<and> vert_adj x' xa}"
      then have "a \<in> V" and "x \<in> V" and "x' \<in> V" and "vert_adj x a" and "vert_adj x' a"
        using vert_adj_imp_inV by auto
      then have "is_gen_path [x, a, x']" 
        using is_walk_def vert_adj_def vert_adj_sym ha singleton_not_edge is_gen_path_def by auto (* Slow *)
      then have "connecting_path x x' [x, a, x']"
        unfolding connecting_path_def vert_adj_def hd_conv_nth last_conv_nth by simp
      moreover have "walk_length [x, a, x'] = 2" using walk_length_conv by simp
      ultimately show "a \<in> f ` {p. connecting_path x x' p \<and> walk_length p = 2}" using f_def by force
    qed
  qed
  then show "card {xa \<in> V. vert_adj x xa \<and> vert_adj x' xa} =
    card {p. connecting_path x x' p \<and> walk_length p = 2}" 
    using f_inj card_image by fastforce
qed

lemma codegree_bipartite_eq: 
  "\<forall> x \<in> X. \<forall> x' \<in> X. codegree x x' = card {y \<in> Y. vert_adj x y \<and> vert_adj x' y}"
  unfolding codegree_def using vert_adj_imp_inV X_vert_adj_Y
  by (metis (no_types, lifting) Collect_cong)

lemma (in fin_bipartite_graph) bipartite_deg_square_eq:
  "\<forall> y \<in> Y. (\<Sum> x' \<in> X. \<Sum> x \<in> X. indicator {z. vert_adj x z \<and> vert_adj x' z} y) = (degree y)^2"
proof
  have hX: "finite X" by (simp add: partitions_finite(1))
  fix y assume hy: "y \<in> Y"
  have 1: "\<forall> x' \<in> X. \<forall> x \<in> X. indicator {z. vert_adj x z \<and> vert_adj x' z} y = 
    indicator ({z. vert_adj x' z} \<inter> {z. vert_adj x z}) y"
    by (metis (mono_tags, lifting) Int_Collect indicator_simps(1) indicator_simps(2) mem_Collect_eq)
  have 2: "\<forall> x' \<in> X. \<forall> x \<in> X. (indicator ({z. vert_adj x' z} \<inter> {z. vert_adj x z}) y:: nat) =
    indicator {z. vert_adj x' z} y * indicator {z. vert_adj x z} y" using indicator_inter_arith 
    by auto
  have "(\<Sum> x' \<in> X. \<Sum> x \<in> X. (indicator {z. vert_adj x z \<and> vert_adj x' z} y:: nat)) = 
    (\<Sum> x' \<in> X. \<Sum> x \<in> X. indicator ({z. vert_adj x' z} \<inter> {z. vert_adj x z}) y)" 
    using 1 sum.cong by (metis (no_types, lifting))
  also have "... = (\<Sum> x' \<in> X. \<Sum> x \<in> X. indicator {z. vert_adj x' z} y *
    indicator {z. vert_adj x z} y)" using 2 sum.cong by auto
  also have "... = sum (\<lambda> x. indicator {z. vert_adj x z} y) X * sum (\<lambda> x. indicator {z. vert_adj x z} y) X" 
    using sum_product[of "(\<lambda> x. (indicator {z. vert_adj x z} y:: nat))" "X" 
      "(\<lambda> x. indicator {z. vert_adj x z} y)" "X"] by auto
  finally have 3: "(\<Sum> x' \<in> X. \<Sum> x \<in> X. (indicator {z. vert_adj x z \<and> vert_adj x' z} y:: nat)) = 
    (sum (\<lambda> x. indicator {z. vert_adj x z} y) X) ^ 2" using power2_eq_square
    by (metis (no_types, lifting))
  have "\<forall> x \<in> X. indicator {z. vert_adj x z} y = indicator {x. vert_adj x y} x"
    by (simp add: indicator_def)
  from this have "(sum (\<lambda> x. indicator {z. vert_adj x z} y) X) = sum (\<lambda> x. indicator {x. vert_adj x y} x) X"
    using sum.cong by fastforce
  also have "... = card ({x \<in> X. vert_adj x y})" using sum_indicator_eq_card hX
    by (metis Collect_conj_eq Collect_mem_eq)
  finally show "(\<Sum>x'\<in>X. \<Sum>x\<in>X. indicator {z. vert_adj x z \<and> vert_adj x' z} y) = (degree y)^2" 
    using 3 hy degree_neighbors_ssY neighbors_ss_def vert_adj_sym by presburger 
qed

lemma (in fin_bipartite_graph) codegree_degree:          
  "(\<Sum> x' \<in> X. \<Sum> x \<in> X. (codegree x x')) = (\<Sum> y \<in> Y. (degree y)^2)"

proof-
  have hX: "finite X" and hY: "finite Y"
    by (simp_all add: partitions_finite)
  have "\<forall> x' \<in> X. \<forall> x \<in> X. {z \<in> V. vert_adj x z \<and> vert_adj x' z} = Y \<inter> {z. vert_adj x z \<and> vert_adj x' z}"
    using XY_union X_vert_adj_Y by fastforce
  from this have "(\<Sum> x' \<in> X. \<Sum> x \<in> X. (codegree x x')) = (\<Sum> x' \<in> X. \<Sum> x \<in> X. card (Y \<inter> {z. vert_adj x z \<and> vert_adj x' z}))"
    using codegree_def sum.cong by auto 
  also have "... = (\<Sum> x' \<in> X. \<Sum> x \<in> X. \<Sum> y \<in> Y. indicator {z. vert_adj x z \<and> vert_adj x' z} y)" 
    using sum_indicator_eq_card hY by fastforce
  also have "... =  (\<Sum> x' \<in> X. \<Sum> y \<in> Y. (\<Sum> x \<in> X. indicator {z. vert_adj x z \<and> vert_adj x' z} y))"
    using sum.swap by (metis (no_types))
  also have "... = (\<Sum> y \<in> Y. \<Sum> x' \<in> X. (\<Sum> x \<in> X. indicator {z. vert_adj x z \<and> vert_adj x' z} y))" 
    using sum.swap by fastforce
  also have "... = (\<Sum> y \<in> Y. (degree y)^2)" using bipartite_deg_square_eq sum.cong by force
  finally show ?thesis by simp
qed

lemma (in fin_bipartite_graph) sum_degree_normalized_X_density:
  "(\<Sum> x \<in> X. degree_normalized x Y) / card X = edge_density X Y"
  by (smt (z3) card_all_edges_betw_neighbor card_edges_between_set degree_normalized_def
    divide_divide_eq_left' density_simp of_nat_mult of_nat_sum partitions_finite(1) 
    partitions_finite(2) sum.cong sum_left_div_distrib)

lemma (in fin_bipartite_graph) sum_degree_normalized_Y_density:
  "(\<Sum> y \<in> Y. degree_normalized y X) / card Y = edge_density X Y"
  using bipartite_sym fin_bipartite_graph.sum_degree_normalized_X_density fin_bipartite_graph_def 
    fin_graph_system_axioms edge_density_commute by fastforce

end
end