theory Bipartite_Graphs imports Undirected_Graph_Walks
begin

section \<open>Bipartite Graphs \<close>

text \<open>An introductory library for reasoning on bipartite graphs.\<close>

subsection \<open>Bipartite Set Up \<close>
text \<open>All "edges", i.e. pairs, between any two sets \<close>
definition all_bi_edges :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a edge set" where
"all_bi_edges X Y \<equiv> mk_edge ` (X \<times> Y)"

lemma all_bi_edges_alt: 
  assumes "X \<inter> Y = {}"
  shows "all_bi_edges X Y = {e . card e = 2 \<and> e \<inter> X \<noteq> {} \<and> e \<inter> Y \<noteq> {}}"
  unfolding all_bi_edges_def 
proof (intro subset_antisym subsetI)
  fix e assume "e \<in> mk_edge ` (X \<times> Y)"
  then obtain v1 v2 where "e = { v1, v2}" and  "v1 \<in> X" and "v2 \<in> Y"
    by auto
  then show "e \<in> {e. card e = 2 \<and> e \<inter> X \<noteq> {} \<and> e \<inter> Y \<noteq> {}}" using assms
    using card_2_iff by blast 
next 
  fix e' assume assm: "e' \<in> {e. card e = 2 \<and> e \<inter> X \<noteq> {} \<and> e \<inter> Y \<noteq> {}}"
  then obtain v1 where v1in: "v1 \<in> e'" and "v1 \<in> X"
    by blast
  moreover obtain v2 where v2in: "v2 \<in> e'" and "v2 \<in> Y" using assm by blast
  then have ne: "v1 \<noteq> v2"
    using assms calculation(2) by blast 
  have "card e' = 2" using assm by blast
  have "{v1, v2} \<subseteq> e'" using v1in v2in by blast
  then have "e' = {v1, v2}" using assm v1in v2in
    by (metis (no_types, opaque_lifting) \<open>card e' = 2\<close> card_2_iff' insertCI ne subsetI subset_antisym) 
  then show "e' \<in> mk_edge ` (X \<times> Y)"
    by (simp add: \<open>v2 \<in> Y\<close> calculation(2) in_mk_edge_img) 
qed

lemma all_bi_edges_alt2:  "all_bi_edges X Y = {{x, y} | x y. x \<in> X \<and> y \<in> Y }"
  unfolding all_bi_edges_def 
proof (intro subset_antisym subsetI)
  fix x assume "x \<in> mk_edge ` (X \<times> Y)"
  then obtain a b where "(a, b) \<in> (X \<times> Y)" and xeq: "x = mk_edge (a, b) " by blast
  then show "x \<in> {{x, y} |x y. x \<in> X \<and> y \<in> Y}"
    by auto 
next
  fix x assume "x \<in> {{x, y} |x y. x \<in> X \<and> y \<in> Y}"
  then obtain a b where xeq: "x = {a, b}" and "a \<in> X" and "b \<in> Y"
    by blast
  then have "(a, b) \<in> (X \<times> Y)" by auto
  then show "x \<in> mk_edge ` (X \<times> Y)"  using in_mk_edge_img xeq by metis 
qed

lemma all_bi_edges_wf: "e \<in> all_bi_edges X Y \<Longrightarrow> e \<subseteq> X \<union> Y" 
  by (auto simp add: all_bi_edges_alt2)

lemma all_bi_edges_2: "X \<inter> Y = {} \<Longrightarrow> e \<in> all_bi_edges X Y \<Longrightarrow> card e = 2" 
  using card_2_iff by (auto simp add: all_bi_edges_alt2)

lemma all_bi_edges_main: "X \<inter> Y = {} \<Longrightarrow> all_bi_edges X Y \<subseteq> all_edges (X \<union> Y)"
  unfolding  all_edges_def using all_bi_edges_wf all_bi_edges_2 by blast  

lemma all_bi_edges_finite: "finite X \<Longrightarrow> finite Y \<Longrightarrow> finite (all_bi_edges X Y)"
  by (simp add: all_bi_edges_def)

lemma all_bi_edges_not_ssX: "X \<inter> Y = {} \<Longrightarrow> e \<in> all_bi_edges X Y \<Longrightarrow> \<not> e \<subseteq> X"
  by (auto simp add: all_bi_edges_alt)

lemma all_bi_edges_sym: "all_bi_edges X Y = all_bi_edges Y X"
  by (auto simp add: all_bi_edges_alt2)

lemma all_bi_edges_not_ssY: "X \<inter> Y = {} \<Longrightarrow> e \<in> all_bi_edges X Y \<Longrightarrow> \<not> e \<subseteq> Y"
  by (auto simp add: all_bi_edges_alt)

lemma card_all_bi_edges: 
  assumes "finite X" "finite Y"
  assumes "X \<inter> Y = {}"
  shows "card (all_bi_edges X Y) = card X * card Y"
proof -
  have "card (all_bi_edges X Y) = card (X \<times> Y)"
    unfolding all_bi_edges_def using inj_on_mk_edge assms card_image by blast 
  thus ?thesis using card_cartesian_product by auto
qed

lemma (in sgraph) all_edges_between_bi_subset: "mk_edge ` all_edges_between X Y \<subseteq> all_bi_edges X Y"
  by (auto simp: all_edges_between_def all_bi_edges_def)

subsection \<open> Bipartite Graph Locale \<close>

text \<open>For reasoning purposes, it is useful to explicitly label the two sets of vertices as X and Y. 
These are parameters in the locale\<close>

locale bipartite_graph = graph_system + 
  fixes X Y :: "'a set"
  assumes partition: "partition_on V {X, Y}"
  assumes ne: "X \<noteq> Y"
  assumes edge_betw: "e \<in> E \<Longrightarrow> e \<in> all_bi_edges X Y"
begin

lemma part_intersect_empty: "X \<inter> Y = {}"
  using partition_onD2 partition disjointD ne
  by blast

lemma X_not_empty: "X \<noteq> {}"
  using partition partition_onD3 by auto

lemma Y_not_empty: "Y \<noteq> {}"
  using partition partition_onD3 by auto

lemma XY_union: "X \<union> Y = V"
  using partition partition_onD1 by auto

lemma card_edges_two: "e \<in> E \<Longrightarrow> card e = 2"
  using edge_betw all_bi_edges_alt part_intersect_empty by auto 

lemma partitions_ss: "X \<subseteq> V" "Y \<subseteq> V"
  using XY_union by auto

end

text \<open> By definition, we say an edge must be between X and Y, i.e. contains two vertices \<close>
sublocale bipartite_graph \<subseteq> sgraph
  using card_edges_two by (unfold_locales)

context bipartite_graph
begin

abbreviation "density \<equiv> edge_density X Y"

lemma bipartite_sym: "bipartite_graph V E Y X"
  using partition ne edge_betw all_bi_edges_sym 
  by (unfold_locales) (auto simp add: insert_commute)

lemma X_verts_not_adj: 
  assumes "x1 \<in> X" "x2 \<in> X"
  shows "\<not> vert_adj x1 x2"
proof (rule ccontr, simp add: vert_adj_def)
  assume "{x1, x2} \<in> E"
  then have "\<not> {x1, x2} \<subseteq> X" 
    using all_bi_edges_not_ssX edge_betw part_intersect_empty by auto 
  then show False using assms by auto
qed

lemma Y_verts_not_adj: 
  assumes "y1 \<in> Y" "y2 \<in> Y"
  shows "\<not> vert_adj y1 y2"
proof -
  interpret sym: bipartite_graph V E Y X using bipartite_sym by simp
  show ?thesis using sym.X_verts_not_adj
    by (simp add: assms(1) assms(2)) 
qed

lemma X_vert_adj_Y: "x \<in>X \<Longrightarrow> vert_adj x y \<Longrightarrow> y \<in> Y"
  using X_verts_not_adj XY_union vert_adj_imp_inV by blast 

lemma Y_vert_adj_X: "y \<in>Y \<Longrightarrow> vert_adj y x \<Longrightarrow> x \<in> X"
  using Y_verts_not_adj XY_union vert_adj_imp_inV by blast 

lemma neighbors_ss_eq_neighborhoodX: "v \<in> X \<Longrightarrow> neighborhood v = neighbors_ss v Y"
  unfolding neighborhood_def neighbors_ss_def 
  by(auto simp add: X_vert_adj_Y vert_adj_imp_inV)

lemma neighbors_ss_eq_neighborhoodY: "v \<in> Y \<Longrightarrow> neighborhood v = neighbors_ss v X"
  unfolding neighborhood_def neighbors_ss_def 
  by(auto simp add: Y_vert_adj_X vert_adj_imp_inV)

lemma neighborhood_subset_oppX: "v \<in> X \<Longrightarrow> neighborhood v \<subseteq> Y"
  using neighbors_ss_eq_neighborhoodX neighbors_ss_def by auto

lemma neighborhood_subset_oppY: "v \<in> Y \<Longrightarrow> neighborhood v \<subseteq> X"
  using neighbors_ss_eq_neighborhoodY neighbors_ss_def by auto

lemma degree_neighbors_ssX: "v \<in> X \<Longrightarrow> degree v = card (neighbors_ss v Y)"
  using neighbors_ss_eq_neighborhoodX alt_deg_neighborhood by auto

lemma degree_neighbors_ssY: "v \<in> Y \<Longrightarrow> degree v = card (neighbors_ss v X)"
  using neighbors_ss_eq_neighborhoodY alt_deg_neighborhood by auto

definition is_bicomplete:: "bool" where
"is_bicomplete \<equiv> E = all_bi_edges X Y"

lemma edge_betw_indiv: 
  assumes "e \<in> E"
  obtains x y where "x \<in> X \<and> y \<in> Y \<and> e = {x, y}"
proof -
  have "e \<in> {{x, y} | x y. x \<in> X \<and> y \<in> Y }"
    using edge_betw all_bi_edges_alt2 assms by blast
  thus ?thesis
    using that by auto
qed

lemma edges_between_equals_edge_set: "mk_edge ` (all_edges_between X Y) = E"
  by (simp add: all_edges_between_set, intro subset_antisym subsetI, auto) (metis edge_betw_indiv)

text \<open> Lemmas for reasoning on walks and paths in a bipartite graph \<close>
lemma walk_alternates:
  assumes "is_walk w"
  assumes "Suc i < length w" "i \<ge> 0"
  shows "w ! i \<in> X \<longleftrightarrow> w ! (i + 1) \<in> Y"
proof -
  have "{w ! i, w ! (i +1)} \<in> E" using is_walk_index assms by auto
  then show ?thesis
    using X_vert_adj_Y not_vert_adj Y_vert_adj_X vert_adj_sym by blast 
qed

text \<open>A useful reasoning pattern to mimic "wlog" statements for properties that are symmetric
is to interpret the symmetric bipartite graph and then directly apply the lemma proven earlier\<close>
lemma walk_alternates_sym: 
  assumes "is_walk w"
  assumes "Suc i < length w" "i \<ge> 0"
  shows "w ! i \<in> Y \<longleftrightarrow> w ! (i + 1) \<in> X"
proof -
  interpret sym: bipartite_graph V E Y X using bipartite_sym by simp
  show ?thesis using sym.walk_alternates assms by simp
qed

lemma walk_length_even: 
  assumes "is_walk w"
  assumes "hd w \<in> X" and "last w \<in> X"
  shows "even (walk_length w)"
  using assms 
proof (induct "length w" arbitrary: w rule: nat_induct2)
  case 0
  then show ?case by (auto simp add: is_walk_def)
next
  case 1
  then have "walk_length w = 0" using walk_length_conv by auto
  then show ?case by simp
next
  case (step n)
  then show ?case proof (cases "n = 0")
    case True
    then have "length w = 2" using step by simp
    then have "hd w \<in> X \<Longrightarrow> last w \<in> Y" using walk_alternates hd_conv_nth last_conv_nth
      by (metis add_0 add_diff_cancel_right' less_2_cases_iff list.size(3) nat_1_add_1 step.prems(1) 
          zero_le zero_neq_numeral)
    then show ?thesis
      using part_intersect_empty step.prems(2) step.prems(3) by blast 
  next
    case False
    have IH: "(\<And>w. n = length w \<Longrightarrow> is_walk w \<Longrightarrow> hd w \<in> X \<Longrightarrow> last w \<in> X \<Longrightarrow> even (walk_length w))" 
      using step by simp
    obtain w1 w2 where weq: "w = w1@w2" and w1: "w1 = take n w" and w2: "w2 = drop n w"
      by simp
    then have ne: "w1 \<noteq> []" using False is_walk_not_empty2 step.prems(1) by fastforce 
    then have w1_walk: "is_walk w1" using w1 is_walk_take False
      by (metis nat_le_linear neq0_conv step.prems(1) take_all) 
    have hdw1: "hd w1 \<in> X" using step ne weq by auto
    then have w1n: "length w1 = n" using step length_take w1 by auto
    then have "length w2 = 2" using step length_drop
      by (simp add: w2) 
    have "last w = w ! (n + 1)" using step last_conv_nth is_walk_not_empty
      by (metis add.left_commute diff_add_inverse nat_1_add_1) 
    then have "w ! n \<in> Y" using step by (simp add: walk_alternates_sym) 
    then have "w ! (n - 1) \<in> X" using False walk_alternates step by simp
    then have "last w1 \<in> X" using step last_conv_nth[of w1] ne w1n
      by (metis last_list_update list_update_id take_update_swap w1) 
    then have "even (walk_length w1)" using w1_walk w1n hdw1 IH[of w1] by simp
    then have "even (walk_length w1 + 2)" by simp
    then show ?thesis using walk_length_conv weq step
      by (simp add: False w1n) 
  qed
qed

lemma walk_length_even_sym: 
  assumes "is_walk w"
  assumes "hd w \<in> Y" 
  assumes "last w \<in> Y"
  shows "even (walk_length w)"
proof -
  interpret sym: bipartite_graph V E Y X using bipartite_sym by simp
  show ?thesis using sym.walk_length_even assms by auto
qed

lemma walk_length_odd: 
  assumes "is_walk w"
  assumes "hd w \<in> X" and "last w \<in> Y"
  shows "odd (walk_length w)"
  using assms 
proof (cases "length w \<ge> 2")
  case True
  then have hdin: "hd (tl w) \<in> Y" using walk_alternates hd_conv_nth
    by (metis (mono_tags, lifting) Suc_1 Suc_less_eq2 assms(1) assms(2) is_walk_not_empty2 is_walk_tl 
        le_neq_implies_less le_numeral_extra(3) length_greater_0_conv less_Suc_eq nth_tl 
        numeral_1_eq_Suc_0 numerals(1) plus_nat.add_0) 
  have w: "is_walk (tl w)" using assms True is_walk_tl by auto
  have last: "last (tl w) \<in> Y" using assms(3) by (simp add: is_walk_not_empty last_tl w) 
  then have ev: "even (walk_length (tl w))" using hdin w  walk_length_even_sym[of "tl w"] by auto
  then have "walk_length w = walk_length (tl w) + 1" using True walk_length_conv by auto
  then show ?thesis using ev by simp
next
  case False
  have "length w \<noteq> 0" using is_walk_not_empty assms by simp
  then have "length w = 1" using False by linarith
  then have "hd w = last w"
    using \<open>length w \<noteq> 0\<close> hd_conv_nth last_conv_nth by fastforce 
  then have "hd w \<in> X \<Longrightarrow> last w \<notin> Y" using part_intersect_empty by auto 
  then show ?thesis using assms by simp
qed

lemma walk_length_odd_sym: 
  assumes "is_walk w"
  assumes "hd w \<in> Y" and "last w \<in> X"
  shows "odd (walk_length w)"
proof -
  interpret sym: bipartite_graph V E Y X using bipartite_sym by simp
  show ?thesis using assms sym.walk_length_odd by simp
qed

lemma walk_length_even_iff: 
  assumes "is_walk w"
  shows "even (walk_length w) \<longleftrightarrow> (hd w \<in> X \<and> last w \<in> X) \<or> (hd w \<in> Y \<and> last w \<in> Y)"
proof (intro iffI)
  assume ev: "even (walk_length w)"
  show "hd w \<in> X \<and> last w \<in> X \<or> hd w \<in> Y \<and> last w \<in> Y"
  proof (rule ccontr)
    assume "\<not> ((hd w \<in> X \<and> last w \<in> X) \<or> (hd w \<in> Y \<and> last w \<in> Y))"
    then have "(hd w \<notin> X \<or> last w \<notin> X) \<and> (hd w \<notin> Y \<or> last w \<notin> Y)" by simp
    then have "(hd w \<in> Y \<or> last w \<in> Y) \<and> (hd w \<in> X \<or> last w \<in> X)" using part_intersect_empty
      using XY_union assms is_walk_wf_hd is_walk_wf_last by auto 
    then have split: "(hd w \<in> X \<and> last w \<in> Y) \<or> (hd w \<in> Y \<and> last w \<in> X)" 
      using part_intersect_empty by auto
    have o1: "(hd w \<in> X \<and> last w \<in> Y) \<Longrightarrow> odd (walk_length w)" using walk_length_odd assms by auto
    have "(hd w \<in> Y \<and> last w \<in> X) \<Longrightarrow> odd (walk_length w)" using walk_length_odd_sym assms by auto
    then show False using split ev o1 by auto
  qed
next 
  show "(hd w \<in> X \<and> last w \<in> X) \<or> (hd w \<in> Y \<and> last w \<in> Y) \<Longrightarrow> even (walk_length w)" 
    using walk_length_even walk_length_even_sym assms by auto
qed

lemma walk_length_odd_iff: 
  assumes "is_walk w"
  shows "odd (walk_length w) \<longleftrightarrow> (hd w \<in> X \<and> last w \<in> Y) \<or> (hd w \<in> Y \<and> last w \<in> X)"
proof (intro iffI)
  assume o: "odd (walk_length w)"
  show "(hd w \<in> X \<and> last w \<in> Y) \<or> (hd w \<in> Y \<and> last w \<in> X)"
  proof (rule ccontr)
    assume "\<not> ((hd w \<in> X \<and> last w \<in> Y) \<or> (hd w \<in> Y \<and> last w \<in> X))"
    then have "(hd w \<notin> X \<or> last w \<notin> Y) \<and> (hd w \<notin> Y \<or> last w \<notin> X)" by simp
    then have "(hd w \<in> Y \<or> last w \<in> X) \<and> (hd w \<in> X \<or> last w \<in> Y)" using part_intersect_empty
      using XY_union assms is_walk_wf_hd is_walk_wf_last by auto 
    then have split: "(hd w \<in> X \<and> last w \<in> X) \<or> (hd w \<in> Y \<and> last w \<in> Y)" 
      using part_intersect_empty by auto
    have e1: "(hd w \<in> X \<and> last w \<in> X) \<Longrightarrow> even (walk_length w)" using walk_length_even assms by auto
    have "(hd w \<in> Y \<and> last w \<in> Y) \<Longrightarrow> even (walk_length w)" using walk_length_even_sym assms by auto
    then show False using split o e1 by auto
  qed
next 
  show "(hd w \<in> X \<and> last w \<in> Y) \<or> (hd w \<in> Y \<and> last w \<in> X) \<Longrightarrow> odd (walk_length w)" 
    using walk_length_odd walk_length_odd_sym assms by auto
qed

text \<open> Classic basic theorem that a bipartite graph must not have any cycles with an odd length \<close>
lemma no_odd_cycles:
  assumes "is_walk w"
  assumes "odd (walk_length w)"
  shows "\<not> is_cycle w"
proof -
  have "(hd w \<in> X \<and> last w \<in> Y) \<or> (hd w \<in> Y \<and> last w \<in> X)" using assms walk_length_odd_iff by auto
  then have "hd w \<noteq> last w" using part_intersect_empty by auto
  thus ?thesis using is_cycle_def is_closed_walk_def by simp
qed

end

text \<open> A few properties rely on cardinality definitions that require the vertex sets to be finite \<close>

locale fin_bipartite_graph = bipartite_graph + fin_graph_system
begin

lemma fin_bipartite_sym: "fin_bipartite_graph V E Y X"
  by (intro_locales) (simp add: bipartite_sym bipartite_graph.axioms(2)) 

lemma partitions_finite: "finite X" "finite Y"
  using partitions_ss finite_subset finV by auto

lemma card_edges_between_set: "card (all_edges_between X Y) = card E"
proof -
  have "card (all_edges_between X Y) = card (mk_edge ` (all_edges_between X Y))"
    using inj_on_mk_edge using partitions_finite card_image
    by (metis inj_on_mk_edge part_intersect_empty)
  then show ?thesis by (simp add: edges_between_equals_edge_set)
qed

lemma density_simp: "density = card (E) / ((card X) * (card Y))"
  unfolding edge_density_def using card_edges_between_set by auto

lemma edge_size_degree_sumY: "card E = (\<Sum>y \<in> Y . degree y)"
proof -
  have "(\<Sum>y \<in> Y . degree y) = (\<Sum>y \<in> Y . card(neighbors_ss y X))"
    using degree_neighbors_ssY by (simp)
  also have "... = card (all_edges_between X Y)"
    using card_all_edges_betw_neighbor
    by (metis card_all_edges_between_commute partitions_finite(1) partitions_finite(2)) 
  finally show ?thesis
    by (simp add: card_edges_between_set) 
qed

lemma edge_size_degree_sumX: "card E = (\<Sum>y \<in> X . degree y)"
proof -
  interpret sym: fin_bipartite_graph V E Y X 
    using fin_bipartite_sym by simp
  show ?thesis using sym.edge_size_degree_sumY by simp
qed

end
end