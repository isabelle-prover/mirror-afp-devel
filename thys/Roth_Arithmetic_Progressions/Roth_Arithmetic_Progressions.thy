section\<open>Roth's Theorem on Arithmetic Progressions\<close>

theory Roth_Arithmetic_Progressions
  imports Szemeredi_Regularity.Szemeredi
      "Random_Graph_Subgraph_Threshold.Subgraph_Threshold"
      "Ergodic_Theory.Asymptotic_Density"
      "HOL-Library.Ramsey" "HOL-Library.Nat_Bijection"

begin

subsection \<open>Miscellaneous Preliminaries\<close>

lemma sum_prod_le_prod_sum:
  fixes a :: "'a \<Rightarrow> 'b::linordered_idom"
  assumes "\<And>i. i \<in> I \<Longrightarrow> a i \<ge> 0 \<and> b i \<ge> 0"
  shows "(\<Sum>i\<in>I. \<Sum>j\<in>I. a i * b j) \<le> (\<Sum>i\<in>I. a i) * (\<Sum>i\<in>I. b i)"
  using assms
  by (induction I rule: infinite_finite_induct) (auto simp add: algebra_simps sum.distrib sum_distrib_left)

lemma real_mult_gt_cube: "A \<ge> (X ::real) \<Longrightarrow> B \<ge> X \<Longrightarrow> C \<ge> X \<Longrightarrow> X \<ge> 0 \<Longrightarrow> A * B * C \<ge> X^3"
  by (simp add: mult_mono' power3_eq_cube)

lemma triple_sigma_rewrite_card: 
  assumes "finite X" "finite Y" "finite Z"
  shows "card {(x,y,z) . x \<in> X \<and> (y,z) \<in> Y \<times> Z \<and> P x y z} = (\<Sum>x\<in> X . card {(y,z) \<in> Y \<times> Z. P x y z})"
proof -
  define W where "W \<equiv> \<lambda>x. {(y,z) \<in> Y \<times> Z. P x y z}"
  have "W x \<subseteq> Y \<times> Z" for x
    by (auto simp: W_def)
  then have [simp]: "finite (W x)" for x
    by (meson assms finite_SigmaI infinite_super)
  have eq: "{(x,y,z) . x \<in> X \<and> (y,z) \<in> Y \<times> Z \<and> P x y z} = (\<Union>x\<in>X. \<Union>(y,z)\<in>W x. {(x,y,z)})"
    by (auto simp: W_def)
  show ?thesis
    unfolding eq by (simp add: disjoint_iff assms card_UN_disjoint) (simp add: W_def)
qed

lemma all_edges_between_mono1:
  "Y \<subseteq> Z \<Longrightarrow> all_edges_between Y X G \<subseteq> all_edges_between Z X G"
  by (auto simp: all_edges_between_def)

lemma all_edges_between_mono2:
  "Y \<subseteq> Z \<Longrightarrow> all_edges_between X Y G \<subseteq> all_edges_between X Z G"
  by (auto simp: all_edges_between_def)

lemma uwellformed_alt_fst: 
  assumes "uwellformed G" "{x, y} \<in> uedges G"
  shows "x \<in> uverts G"
  using uwellformed_def assms by simp

lemma uwellformed_alt_snd: 
  assumes "uwellformed G" "{x, y} \<in> uedges G"
  shows "y \<in> uverts G"
  using uwellformed_def assms by simp

lemma all_edges_between_subset_times: "all_edges_between X Y G \<subseteq> (X \<inter> \<Union>(uedges G)) \<times> (Y \<inter> \<Union>(uedges G))"
  by (auto simp: all_edges_between_def)

lemma finite_all_edges_between':
  assumes "finite (uverts G)" "uwellformed G"
  shows "finite (all_edges_between X Y G)"
proof -
  have "finite (\<Union>(uedges G))"
    by (meson Pow_iff all_edges_subset_Pow assms finite_Sup subsetD wellformed_all_edges)
  with all_edges_between_subset_times show ?thesis
    by (metis finite_Int finite_SigmaI finite_subset)
qed

lemma all_edges_between_E_diff: 
  "all_edges_between X Y (V,E-E') = all_edges_between X Y (V,E) - all_edges_between X Y (V,E')"
  by (auto simp: all_edges_between_def)

lemma all_edges_between_E_Un: 
  "all_edges_between X Y (V,E\<union>E') = all_edges_between X Y (V,E) \<union> all_edges_between X Y (V,E')"
  by (auto simp: all_edges_between_def)

lemma all_edges_between_E_UN:
  "all_edges_between X Y (V, \<Union>i\<in>I. E i) = (\<Union>i\<in>I. all_edges_between X Y (V,E i))"
  by (auto simp: all_edges_between_def)

lemma all_edges_preserved: "\<lbrakk>all_edges_between A B G' = all_edges_between A B G; X \<subseteq> A; Y \<subseteq> B\<rbrakk>
    \<Longrightarrow> all_edges_between X Y G' = all_edges_between X Y G"
  by (auto simp: all_edges_between_def)

lemma subgraph_edge_wf:
  assumes "uwellformed G" "uverts H = uverts G" "uedges H \<subseteq> uedges G"
  shows "uwellformed H"
  by (metis assms subsetD uwellformed_def)


subsection \<open>Preliminaries on Neighbors in Graphs\<close>

definition neighbor_in_graph::  " uvert \<Rightarrow> uvert \<Rightarrow> ugraph \<Rightarrow>  bool"
  where "neighbor_in_graph x y G \<equiv> (x \<in> (uverts G) \<and> y \<in> (uverts G) \<and> {x,y} \<in> (uedges G))"

definition neighbors :: "uvert \<Rightarrow> ugraph \<Rightarrow> uvert set" where
  "neighbors x G  \<equiv> {y \<in> uverts G . neighbor_in_graph x y G}"

definition neighbors_ss:: "uvert \<Rightarrow> uvert set \<Rightarrow> ugraph \<Rightarrow> uvert set" where
  "neighbors_ss x Y G \<equiv> {y \<in> Y . neighbor_in_graph x y G}"

lemma all_edges_betw_sigma_neighbor: 
"uwellformed G \<Longrightarrow> all_edges_between X Y G = (SIGMA x:X. neighbors_ss x Y G)"
  by (auto simp add: all_edges_between_def neighbors_ss_def neighbor_in_graph_def 
      uwellformed_alt_fst uwellformed_alt_snd)

lemma card_all_edges_betw_neighbor: 
  assumes "finite X" "finite Y" "uwellformed G"
  shows "card (all_edges_between X Y G) = (\<Sum>x\<in>X. card (neighbors_ss x Y G))"
  using all_edges_betw_sigma_neighbor assms by (simp add: neighbors_ss_def)


subsection \<open>Preliminaries on Triangles in Graphs\<close>

definition triangle_in_graph:: "uvert \<Rightarrow> uvert \<Rightarrow> uvert \<Rightarrow> ugraph \<Rightarrow> bool"
  where "triangle_in_graph x y z G 
         \<equiv> ({x,y} \<in> uedges G) \<and> ({y,z} \<in> uedges G) \<and> ({x,z} \<in> uedges G)"

definition triangle_triples
  where "triangle_triples X Y Z G \<equiv> {(x,y,z) \<in> X \<times> Y \<times> Z. triangle_in_graph x y z G}"

lemma triangle_commu1:
  assumes "triangle_in_graph x y z G"
  shows "triangle_in_graph y x z G"
  using assms triangle_in_graph_def by (auto simp add: insert_commute)

lemma triangle_vertices_distinct1:
  assumes wf: "uwellformed G"
  assumes tri: "triangle_in_graph x y z G"
  shows "x \<noteq> y"
proof (rule ccontr)
  assume a: "\<not> x \<noteq> y"
  have "card {x, y} = 2" using tri wf triangle_in_graph_def
    using uwellformed_def by blast 
  thus False using a by simp
qed

lemma triangle_vertices_distinct2: 
  assumes "uwellformed G" "triangle_in_graph x y z G"
  shows "y \<noteq> z"
  by (metis assms triangle_vertices_distinct1 triangle_in_graph_def) 

lemma triangle_in_graph_edge_point: 
  assumes "uwellformed G"
  shows "triangle_in_graph x y z G \<longleftrightarrow> {y, z} \<in> uedges G \<and> neighbor_in_graph x y G \<and> neighbor_in_graph x z G"
  by (auto simp add: triangle_in_graph_def neighbor_in_graph_def assms uwellformed_alt_fst uwellformed_alt_snd)

definition 
  "unique_triangles G 
    \<equiv> \<forall>e \<in> uedges G. \<exists>!T. \<exists>x y z. T = {x,y,z} \<and> triangle_in_graph x y z G \<and> e \<subseteq> T"

definition triangle_free_graph:: "ugraph \<Rightarrow> bool"
  where "triangle_free_graph G \<equiv> \<not>(\<exists> x y z. triangle_in_graph x y z G )"

lemma triangle_free_graph_empty: "uedges G = {} \<Longrightarrow> triangle_free_graph G"
  by (simp add: triangle_free_graph_def triangle_in_graph_def)

lemma edge_vertices_not_equal: 
  assumes "uwellformed G" "{x,y} \<in> uedges G"
  shows "x \<noteq> y"
  using assms triangle_in_graph_def triangle_vertices_distinct1 by blast

lemma triangle_in_graph_verts: 
  assumes "uwellformed G" "triangle_in_graph x y z G"
  shows "x \<in> uverts G" "y \<in> uverts G" "z\<in> uverts G"
proof -
  have 1: "{x, y} \<in> uedges G" using triangle_in_graph_def
    using assms(2) by auto 
  then show "x \<in> uverts G" using uwellformed_alt_fst assms by blast
  then show "y \<in> uverts G" using 1 uwellformed_alt_snd assms by blast
  have "{x, z} \<in> uedges G" using triangle_in_graph_def assms(2) by auto
  then show "z \<in> uverts G" using uwellformed_alt_snd assms by blast
qed

  
definition triangle_set :: "ugraph \<Rightarrow> uvert set set"
  where "triangle_set G \<equiv> { {x,y,z} | x y z. triangle_in_graph x y z G}"

fun mk_triangle_set :: "(uvert \<times> uvert \<times> uvert) \<Rightarrow> uvert set" 
  where "mk_triangle_set (x,y,z) = {x,y,z}"

lemma finite_triangle_set:
  assumes fin: "finite (uverts G)" and wf: "uwellformed G"
  shows "finite (triangle_set G)"
proof -
  have "triangle_set G \<subseteq> Pow (uverts G)"
    using PowI local.wf triangle_in_graph_def triangle_set_def uwellformed_def by auto
  then show ?thesis
    by (meson fin finite_Pow_iff infinite_super)
qed

lemma card_triangle_3: 
  assumes "t \<in> triangle_set G" "uwellformed G"
  shows "card t = 3"
  using assms by (auto simp: triangle_set_def edge_vertices_not_equal triangle_in_graph_def)

lemma triangle_set_power_set_ss: "uwellformed G \<Longrightarrow> triangle_set G \<subseteq> Pow (uverts G)"
  by (auto simp add: triangle_set_def triangle_in_graph_def uwellformed_alt_fst uwellformed_alt_snd)

lemma triangle_in_graph_ss: 
  assumes "uedges Gnew \<subseteq> uedges G" 
  assumes "triangle_in_graph x y z Gnew"
  shows "triangle_in_graph x y z G"
using assms triangle_in_graph_def by auto 

lemma triangle_set_graph_edge_ss: 
  assumes "uedges Gnew \<subseteq> uedges G" 
  assumes "uverts Gnew = uverts G"
  shows "triangle_set Gnew \<subseteq> triangle_set G"
  using assms unfolding triangle_set_def by (blast intro: triangle_in_graph_ss)

lemma triangle_set_graph_edge_ss_bound: 
  fixes G :: "ugraph" and Gnew :: "ugraph"
  assumes "uwellformed G" "finite (uverts G)" "uedges Gnew \<subseteq> uedges G" "uverts Gnew = uverts G"
  shows "card (triangle_set G) \<ge> card (triangle_set Gnew)"
  by (simp add: assms card_mono finite_triangle_set triangle_set_graph_edge_ss)


subsection \<open>The Triangle Counting Lemma and the Triangle Removal Lemma\<close>

text\<open>We begin with some more auxiliary material to be used in the main lemmas.\<close>

lemma regular_pair_neighbor_bound: 
  fixes \<epsilon>::real
  assumes finG: "finite (uverts G)"
  assumes xss: "X \<subseteq> uverts G" and yss: "Y \<subseteq> uverts G" and "card X > 0"
    and wf: "uwellformed G"
    and eg0: "\<epsilon> > 0" and "\<epsilon>-regular_pair X Y G" and ed: "edge_density X Y G \<ge> 2*\<epsilon>"
  defines "X' \<equiv> {x \<in> X. card (neighbors_ss x Y G) < (edge_density X Y G - \<epsilon>) * card (Y)}"
  shows "card X' < \<epsilon> * card X" 
    (is "card (?X') < \<epsilon> * _")
proof (cases "?X' = {}")
  case False \<comment>\<open>Following Gowers's proof - more in depth with reasoning on contradiction\<close>
  let ?rxy = "1/(card X' * card Y)" 
  show ?thesis 
  proof (rule ccontr)
    assume "\<not> (card (X') <  \<epsilon> * card X) " 
    then have a: "(card(X') \<ge>  \<epsilon> * card X) " by simp
    have fin: "finite X" "finite Y" using assms finite_subset by auto
    have ebound: "\<epsilon> \<le> 1/2"
      by (metis ed edge_density_le1 le_divide_eq_numeral1(1) mult.commute order_trans)
    have finx: "finite X'" using fin X'_def by simp 
    have "\<And> x. x \<in> X'\<Longrightarrow> (card (neighbors_ss x Y G)) < (edge_density X Y G - \<epsilon>) * (card Y)"
      unfolding X'_def by blast 
    then have "(\<Sum>x\<in>X'. card (neighbors_ss x Y G)) < (\<Sum>x\<in>X'. ((edge_density X Y G - \<epsilon>) * (card Y)))"
      using False sum_strict_mono X'_def
      by (smt (verit, del_insts) finx of_nat_sum)
    then have upper: "(\<Sum>x\<in>X'. card (neighbors_ss x Y G)) < (card X') * ((edge_density X Y G - \<epsilon>) * (card Y))"
      by (simp add: sum_bounded_above)
    have yge0: "card Y > 0"
      by (metis gr0I mult_eq_0_iff of_nat_0 of_nat_less_0_iff upper)
    have "?rxy > 0"
      using card_0_eq finx False yge0 X'_def by fastforce 
    then have upper2: "?rxy * (\<Sum>x\<in>X'. card (neighbors_ss x Y G)) < ?rxy * (card X') * ((edge_density X Y G - \<epsilon>) * (card Y))"
      by (smt (verit) mult.assoc mult_le_cancel_left upper)
    have "?rxy * (card X') * ((edge_density X Y G - \<epsilon>) * (card Y)) = edge_density X Y G - \<epsilon>"
      using False X'_def finx by force
    with \<open>\<epsilon> > 0\<close> upper2 have con: "edge_density X Y G - ?rxy * (\<Sum>x\<in>X'. card (neighbors_ss x Y G)) > \<epsilon>" 
      by linarith
    have "\<bar>edge_density X Y G - ?rxy * (\<Sum>x\<in>X'. card (neighbors_ss x Y G))\<bar> 
        = \<bar>?rxy * (card (all_edges_between X' Y G)) - edge_density X Y G\<bar>"
      using card_all_edges_betw_neighbor fin wf by (simp add: X'_def)
    also have "... = \<bar>edge_density X' Y G - edge_density X Y G\<bar>"
      by (simp add: edge_density_def)
    also have "... \<le> \<epsilon>"
      using assms ebound yge0 a by (force simp add: X'_def regular_pair_def)
    finally show False using con by linarith
  qed 
qed (simp add: \<open>card X > 0\<close> eg0)

lemma neighbor_set_meets_e_reg_cond:
  fixes \<epsilon>::real 
  assumes "edge_density X Y G \<ge> 2*\<epsilon>"
  and "card (neighbors_ss x Y G) \<ge> (edge_density X Y G - \<epsilon>) * card Y"
shows "card (neighbors_ss x Y G) \<ge> \<epsilon> * card (Y)"
  by (smt (verit) assms mult_right_mono of_nat_0_le_iff)

lemma all_edges_btwn_neighbor_sets_lower_bound: 
  fixes \<epsilon>::real 
  assumes rp2: "\<epsilon>-regular_pair Y Z G"
    and ed1: "edge_density X Y G  \<ge> 2*\<epsilon>" and ed2: "edge_density X Z G  \<ge> 2*\<epsilon>" 
    and cond1: "card (neighbors_ss x Y G) \<ge> (edge_density X Y G - \<epsilon>) * card Y"
    and cond2: "card (neighbors_ss x Z G) \<ge> (edge_density X Z G - \<epsilon>) * card Z"
  shows "card (all_edges_between (neighbors_ss x Y G) (neighbors_ss x Z G) G) 
      \<ge> (edge_density Y Z G - \<epsilon>) * card (neighbors_ss x Y G) * card (neighbors_ss x Z G)"
    (is "card (all_edges_between ?Y' ?Z' G) \<ge> (edge_density Y Z G - \<epsilon>) * card ?Y' * card ?Z'")
proof -
  have yss': "?Y' \<subseteq> Y" using neighbors_ss_def by simp
  have zss': "?Z' \<subseteq> Z" using neighbors_ss_def by simp
  have min_sizeY: "card ?Y' \<ge> \<epsilon> * card Y"
    using cond1 ed1 neighbor_set_meets_e_reg_cond by blast 
  have min_sizeZ: "card ?Z' \<ge> \<epsilon> * card Z"
    using cond2 ed2 neighbor_set_meets_e_reg_cond by blast 
  then have "\<bar> edge_density ?Y' ?Z' G - edge_density Y Z G \<bar> \<le> \<epsilon>"
    using min_sizeY yss' zss' assms by (force simp add: regular_pair_def)
  then have "edge_density Y Z G - \<epsilon> \<le> (card (all_edges_between ?Y' ?Z' G)/(card ?Y' * card ?Z'))" 
    using edge_density_def by simp
  then have "(card ?Y' * card ?Z') * (edge_density Y Z G - \<epsilon>) \<le> (card (all_edges_between ?Y' ?Z' G))"
    by (fastforce simp: divide_simps mult.commute simp flip: of_nat_mult split: if_split_asm)
  then show ?thesis
    by (metis (no_types, lifting) mult.assoc mult_of_nat_commute of_nat_mult) 
qed


text\<open>We are now ready to show the Triangle Counting Lemma:\<close>

theorem triangle_counting_lemma:
  fixes \<epsilon>::real 
  assumes xss: "X \<subseteq> uverts G" and yss: "Y \<subseteq> uverts G" and zss: "Z \<subseteq> uverts G" and en0: "\<epsilon> > 0"
    and finG: "finite (uverts G)" and wf: "uwellformed G"    
    and rp1: "\<epsilon>-regular_pair X Y G" and rp2: "\<epsilon>-regular_pair Y Z G" and rp3: "\<epsilon>-regular_pair X Z G"
    and ed1: "edge_density X Y G \<ge> 2*\<epsilon>" and ed2: "edge_density X Z G \<ge> 2*\<epsilon>" and ed3: "edge_density Y Z G \<ge> 2*\<epsilon>"
  shows "card (triangle_triples X Y Z G)
        \<ge> (1-2*\<epsilon>) * (edge_density X Y G - \<epsilon>) * (edge_density X Z G - \<epsilon>) * (edge_density Y Z G - \<epsilon>)*
           card X * card Y * card Z" 
proof -
  let ?T_all = "{(x,y,z) \<in> X \<times> Y \<times> Z. (triangle_in_graph x y z G)}"
  let ?ediff = "\<lambda>X Y. edge_density X Y G - \<epsilon>"
  define XF where "XF \<equiv> \<lambda>Y. {x \<in> X. card(neighbors_ss x Y G) < ?ediff X Y * card Y}"
  have fin: "finite X" "finite Y" "finite Z" using finG rev_finite_subset xss yss zss by auto
  then have "card X > 0"
    using card_0_eq ed1 edge_density_def en0  by fastforce
  
  text\<open> Obtain a subset of @{term X} where all elements meet minimum numbers for neighborhood size
in @{term Y} and @{term Z}.\<close>
  
  define X2 where "X2 \<equiv> X - (XF Y \<union> XF Z)"
  have xss: "X2 \<subseteq> X" and finx2: "finite X2"
    by (auto simp add: X2_def fin)
  
  text \<open>Reasoning on the minimum size of @{term X2}:\<close>
  have part1: "(XF Y \<union> XF Z) \<union> X2 = X"
    by (auto simp: XF_def X2_def)
  have card_XFY: "card (XF Y) <  \<epsilon> * card X" 
    using regular_pair_neighbor_bound assms \<open>card X > 0\<close> by (simp add: XF_def)
  
  text\<open> We now repeat the same argument as above to the regular pair @{term X} @{term Z} in @{term G}.\<close>
  have card_XFZ: "card (XF Z) < \<epsilon> * card X"
    using regular_pair_neighbor_bound assms \<open>card X > 0\<close> by (simp add: XF_def)
  have "card (XF Y \<union> XF Z) \<le> 2 * \<epsilon> * (card X)"
    by (smt (verit) card_XFY card_XFZ card_Un_le comm_semiring_class.distrib of_nat_add of_nat_mono)
  then have "card X2 \<ge> card X - 2 * \<epsilon> * card X" 
    using part1 by (smt (verit, del_insts) card_Un_le of_nat_add of_nat_mono) 
  then have minx2: "card X2 \<ge> (1 - 2 * \<epsilon>) * card X"
    by (metis mult.commute mult_cancel_left2 right_diff_distrib)
  
  text \<open>Reasoning on the minimum number of edges between neighborhoods of @{term X} in @{term Y} 
and @{term Z}.\<close>
 
  have edyzgt0: "?ediff Y Z > 0" and edxygt0: "?ediff X Y > 0" 
    using ed1 ed3 \<open>\<epsilon> > 0\<close> by linarith+
  have card_y_bound: "card (neighbors_ss x Y G) \<ge> ?ediff X Y * card Y"
    and card_z_bound: "card (neighbors_ss x Z G) \<ge> ?ediff X Z * card Z"
    if "x \<in> X2" for x
    using that by (auto simp: XF_def X2_def)
  have card_y_bound': 
          "(\<Sum>x\<in> X2. ?ediff Y Z * (card (neighbors_ss x Y G)) * (card (neighbors_ss x Z G))) \<ge>
           (\<Sum>x\<in> X2. ?ediff Y Z * ?ediff X Y * (card Y) * (card (neighbors_ss x Z G)))" 
      by (rule sum_mono) (smt (verit, best) mult.left_commute card_y_bound edyzgt0 mult.commute mult_right_mono of_nat_0_le_iff)
  have card_z_bound': 
         "(\<Sum>x\<in> X2. ?ediff Y Z * ?ediff X Y * (card Y) * (card (neighbors_ss x Z G))) \<ge>
          (\<Sum>x\<in> X2. ?ediff Y Z * ?ediff X Y * (card Y) * ?ediff X Z * (card Z))" 
      using card_z_bound mult_left_mono edxygt0 edyzgt0 by (fastforce intro!: sum_mono)
  have eq_set: "\<And>x. {(y,z). y \<in> Y \<and> z \<in> Z \<and> {y, z} \<in> uedges G \<and> neighbor_in_graph x y G \<and> neighbor_in_graph x z G } = 
                     {(y,z). y \<in> (neighbors_ss x Y G) \<and> z \<in> (neighbors_ss x Z G) \<and> {y, z} \<in> uedges G }"
    by (auto simp: neighbors_ss_def)
  have "card ?T_all = (\<Sum>x\<in> X . card {(y,z) \<in> Y \<times> Z. triangle_in_graph x y z G})"
    using triple_sigma_rewrite_card fin by force  
  also have "\<dots> = (\<Sum>x\<in> X . card {(y,z). y \<in> Y \<and> z \<in> Z \<and> {y, z} \<in> uedges G \<and> neighbor_in_graph x y G \<and> neighbor_in_graph x z G })"
    using triangle_in_graph_edge_point assms by auto
  also have "... = (\<Sum>x \<in> X. card (all_edges_between (neighbors_ss x Y G) (neighbors_ss x Z G) G))"
    using all_edges_between_def eq_set by presburger
  finally have l: "card ?T_all \<ge> (\<Sum>x\<in> X2 . card (all_edges_between (neighbors_ss x Y G) (neighbors_ss x Z G) G))"
    by (simp add: fin xss sum_mono2)
  have "(\<Sum>x\<in> X2. ?ediff Y Z * (card (neighbors_ss x Y G)) * (card (neighbors_ss x Z G))) \<le> 
        (\<Sum>x\<in> X2. real (card (all_edges_between (neighbors_ss x Y G) (neighbors_ss x Z G) G)))"
        (is "sum ?F _ \<le> sum ?G _")
  proof (rule sum_mono)
    show  "\<And>x. x \<in> X2 \<Longrightarrow> ?F x \<le> ?G x"
      using all_edges_btwn_neighbor_sets_lower_bound card_y_bound card_z_bound ed1 ed2 rp2 by blast
  qed
  then have "card ?T_all \<ge> card X2 * ?ediff Y Z * ?ediff X Y * card Y * ?ediff X Z * card Z" 
    using card_z_bound' card_y_bound' l of_nat_le_iff [symmetric, where 'a=real] by force
  then have "real (card ?T_all) \<ge> ((1 - 2 * \<epsilon>) * card X) * ?ediff Y Z * 
      ?ediff X Y * (card Y) * ?ediff X Z * (card Z)"
    by (smt (verit, best) ed2 edxygt0 edyzgt0 en0 minx2 mult_right_mono of_nat_0_le_iff)
  then show ?thesis by (simp add: triangle_triples_def mult.commute mult.left_commute) 
qed


definition regular_graph :: "real \<Rightarrow> uvert set set \<Rightarrow> ugraph \<Rightarrow> bool"  
           ("_-regular'_graph" [999]1000)
  where "\<epsilon>-regular_graph P G \<equiv> \<forall>R S. R\<in>P \<longrightarrow> S\<in>P \<longrightarrow> \<epsilon>-regular_pair R S G" for \<epsilon>::real

text \<open>A minimum density, but empty edge sets are excluded.\<close>

definition edge_dense :: "nat set \<Rightarrow> nat set \<Rightarrow> ugraph \<Rightarrow> real \<Rightarrow> bool"
  where "edge_dense X Y G \<epsilon> \<equiv> all_edges_between X Y G = {} \<or> edge_density X Y G \<ge> \<epsilon>"

definition dense_graph :: "uvert set set \<Rightarrow> ugraph \<Rightarrow> real \<Rightarrow> bool"
  where "dense_graph P G \<epsilon> \<equiv> \<forall>R S. R\<in>P \<longrightarrow> S\<in>P \<longrightarrow> edge_dense R S G \<epsilon>" for \<epsilon>::real

definition decent :: "nat set \<Rightarrow> nat set \<Rightarrow> ugraph \<Rightarrow> real \<Rightarrow> bool"
  where "decent X Y G \<eta> \<equiv> all_edges_between X Y G = {} \<or> (card X \<ge> \<eta> \<and> card Y \<ge> \<eta>)" for \<eta>::real

definition decent_graph :: "uvert set set \<Rightarrow> ugraph \<Rightarrow> real \<Rightarrow> bool"
  where "decent_graph P G \<eta> \<equiv> \<forall>R S. R\<in>P \<longrightarrow> S\<in>P \<longrightarrow> decent R S G \<eta>" 

text \<open>The proof of the triangle counting lemma requires ordered triples. For each unordered triple 
there are six permutations, hence the factor of $1/6$ here.\<close>

lemma card_convert_triangle_rep:
  fixes G :: "ugraph" 
  assumes "X \<subseteq> uverts G" and "Y \<subseteq> uverts G" and "Z \<subseteq> uverts G" and fin: "finite (uverts G)" 
and wf: "uwellformed G"
  shows "card (triangle_set G) \<ge> 1/6 * card {(x,y,z) \<in> X \<times> Y \<times> Z . (triangle_in_graph x y z G)}"
         (is  "_ \<ge> 1/6 * card ?TT")
proof -
  define tofl where "tofl \<equiv> \<lambda>l::nat list. (hd l, hd(tl l), hd(tl(tl l)))"
  have in_tofl: "(x,y,z) \<in> tofl ` permutations_of_set {x,y,z}" if "x\<noteq>y" "y\<noteq>z" "x\<noteq>z" for x y z
  proof -
    have "distinct[x,y,z]"
      using that by simp
    then show ?thesis
      unfolding tofl_def image_iff 
      by (smt (verit, best) list.sel(1) list.sel(3) set_simps permutations_of_setI set_empty)
  qed
  have "?TT \<subseteq> {(x,y,z). (triangle_in_graph x y z G)}"
    by auto
  also have "\<dots> \<subseteq> (\<Union>t \<in> triangle_set G. tofl ` permutations_of_set t)"
    using edge_vertices_not_equal [OF wf] in_tofl 
    by (clarsimp simp add: triangle_set_def triangle_in_graph_def) metis
  finally have "?TT \<subseteq> (\<Union>t \<in> triangle_set G. tofl ` permutations_of_set t)" .
  then have "card ?TT \<le> card(\<Union>t \<in> triangle_set G. tofl ` permutations_of_set t)" 
    by (intro card_mono finite_UN_I finite_triangle_set) (auto simp: assms)
  also have "\<dots> \<le> (\<Sum>t \<in> triangle_set G. card (tofl ` permutations_of_set t))"
    using card_UN_le fin finite_triangle_set local.wf by blast
  also have "\<dots> \<le> (\<Sum>t \<in> triangle_set G. card (permutations_of_set t))"
    by (meson card_image_le finite_permutations_of_set sum_mono)
  also have "\<dots> \<le> (\<Sum>t \<in> triangle_set G. fact 3)"
    by (rule sum_mono) (metis card.infinite card_permutations_of_set card_triangle_3 eq_refl local.wf nat.case numeral_3_eq_3)
  also have "\<dots> = 6 * card (triangle_set G)"
    by (simp add: eval_nat_numeral)
  finally have "card ?TT \<le> 6 * card (triangle_set G)" .
  then show ?thesis
    by (simp add: divide_simps)
qed

lemma card_convert_triangle_rep_bound: 
  fixes G :: "ugraph" and t :: real
  assumes "X \<subseteq> uverts G" and "Y \<subseteq> uverts G" and "Z \<subseteq> uverts G" and fin: "finite (uverts G)" 
and wf: "uwellformed G"
  assumes "card {(x,y,z) \<in> X \<times> Y \<times> Z . (triangle_in_graph x y z G)} \<ge> t"
  shows "card (triangle_set G) \<ge> 1/6 *t"
proof -
  define t' where "t' \<equiv> card {(x,y,z) \<in> X \<times> Y \<times> Z . (triangle_in_graph x y z G)}"
  have "t' \<ge> t" using assms t'_def by simp
  then have tgt: "1/6 * t' \<ge> 1/6 * t" by simp
  have "card (triangle_set G) \<ge> 1/6 *t'" using t'_def card_convert_triangle_rep assms by simp
  thus ?thesis using tgt by linarith
qed

lemma edge_density_eq0:
  assumes "all_edges_between A B G = {}" and "X \<subseteq> A" "Y \<subseteq> B"
  shows "edge_density X Y G = 0"
proof -
  have "all_edges_between X Y G = {}"
    by (metis all_edges_between_mono1 all_edges_between_mono2 assms subset_empty)
  then show ?thesis
    by (auto simp: edge_density_def)
qed

text\<open>The following is the Triangle Removal Lemma.\<close>

theorem triangle_removal_lemma:
  fixes \<epsilon> :: real
  assumes egt: "\<epsilon> > 0"
  shows "\<exists>\<delta>::real > 0. \<forall>G. card(uverts G) > 0 \<longrightarrow> uwellformed G \<longrightarrow> 
          card (triangle_set G) \<le> \<delta> * card(uverts G) ^ 3 \<longrightarrow>
          (\<exists>G'. triangle_free_graph G' \<and> uverts G' = uverts G \<and> uedges G' \<subseteq> uedges G \<and> 
          card (uedges G - uedges G') \<le> \<epsilon> * (card (uverts G))\<^sup>2)"
    (is "\<exists>\<delta>::real > 0. \<forall>G. _ \<longrightarrow> _ \<longrightarrow> _ \<longrightarrow> (\<exists>Gnew. ?\<Phi> G Gnew)")
proof (cases "\<epsilon> < 1")
  case False
  show ?thesis
  proof (intro exI conjI strip)
    fix G
    define Gnew where "Gnew \<equiv> ((uverts G), {}::uedge set)"
    assume G: "uwellformed G" "card(uverts G) > 0"
    then show "triangle_free_graph Gnew" "uverts Gnew = uverts G" "uedges Gnew \<subseteq> uedges G"
      by (auto simp: Gnew_def triangle_free_graph_empty)
    have "real (card (uedges G)) \<le> (card (uverts G))\<^sup>2"
      by (meson G card_gt_0_iff max_edges_graph of_nat_le_iff)
    also have "\<dots> \<le> \<epsilon> * (card (uverts G))\<^sup>2"
      using False mult_le_cancel_right1 by fastforce
    finally show "real (card (uedges G - uedges Gnew)) \<le> \<epsilon> * ((card (uverts G))\<^sup>2)"
      by (simp add: Gnew_def)
  qed (rule zero_less_one)
next
  case True
  have e4gt: "\<epsilon>/4 > 0" using \<open>\<epsilon> > 0\<close> by auto
  then obtain M0 where 
    M0: "\<And>G. card (uverts G) > 0 \<Longrightarrow> \<exists>P. regular_partition (\<epsilon>/4) G P \<and> card P \<le> M0" 
    and "M0>0"
    by (metis Szemeredi_Regularity_Lemma le0 neq0_conv not_le not_numeral_le_zero)
  define D0 where "D0 \<equiv> 1/6 *(1-(\<epsilon>/2))*((\<epsilon>/4)^3)*((\<epsilon> /(4*M0))^3)"
  have "D0 > 0" 
    using \<open>0 < \<epsilon>\<close> \<open>\<epsilon> < 1\<close> \<open>M0 > 0\<close> by (simp add: D0_def zero_less_mult_iff)
  then obtain \<delta>:: "real" where \<delta>: "0 < \<delta>" "\<delta> < D0"
    by (meson dense)
  show ?thesis
  proof (rule exI, intro conjI strip)
    fix G
    assume "card(uverts G) > 0" and wf: "uwellformed G"
    then have fin: "finite (uverts G)"
      by (simp add: card_gt_0_iff)
    
    text\<open>Assume that, for a yet to be determined $\delta$, we have:\<close>
    assume ineq: "real (card (triangle_set G)) \<le> \<delta> * card (uverts G) ^ 3"
    
    text\<open>Step 1: Partition: Using Szemer\'{e}di's Regularity Lemma, we get an $\epsilon/4$ partition. \<close>
    let ?n = "card (uverts G)"
    have vne: "uverts G \<noteq> {}"
      using \<open>0 < card (uverts G)\<close> by force 
    then have ngt0: "?n > 0"
      by (simp add: fin card_gt_0_iff)
    with M0 obtain P where M: "regular_partition (\<epsilon>/4) G P" and "card P \<le> M0"
      by blast
    define M where "M \<equiv> card P"
    have "finite P"
      by (meson M fin finite_elements regular_partition_def)
    with M0 have "M > 0"
      unfolding M_def
      by (metis M card_gt_0_iff partition_onD1 partition_on_empty regular_partition_def vne)
    let ?e4M = "\<epsilon> / (4 * real M)"
    define D where "D \<equiv> 1/6 *(1-(\<epsilon>/2)) * ((\<epsilon>/4)^3) * ?e4M^3"
    have "D > 0" 
      using \<open>0 < \<epsilon>\<close> \<open>\<epsilon> < 1\<close> \<open>M > 0\<close> by (simp add: D_def zero_less_mult_iff)
    have "D0 \<le> D"
      unfolding D0_def D_def using \<open>0 < \<epsilon>\<close> \<open>\<epsilon> < 1\<close> \<open>card P \<le> M0\<close> \<open>M > 0\<close>
      by (intro mult_mono) (auto simp: frac_le M_def)
    have fin_part: "finite_graph_partition (uverts G) P M"
      using M unfolding regular_partition_def finite_graph_partition_def
      by (metis M_def \<open>0 < M\<close> card_gt_0_iff)
    then have fin_P: "finite R" and card_P_gt0: "card R > 0" if "R\<in>P" for R
      using fin finite_graph_partition_finite finite_graph_partition_gt0 that by auto
    have card_P_le: "card R \<le> ?n" if "R\<in>P" for R
      by (meson card_mono fin fin_part finite_graph_partition_subset that)
    have P_disjnt: "\<And>R S. \<lbrakk>R \<noteq> S; R \<in> P; S \<in> P\<rbrakk> \<Longrightarrow> R \<inter> S = {}"
      using fin_part
      by (metis disjnt_def finite_graph_partition_def insert_absorb pairwise_insert partition_on_def) 
    have sum_card_P: "(\<Sum>R\<in>P. card R) = ?n"
      using card_finite_graph_partition fin fin_part by meson
    
    text\<open>Step 2. Cleaning. For each ordered pair of parts $(P_i,P_j)$, remove all edges between 
      $P_i$ and $P_j$ if (a) it is an irregular pair, (b) its edge density ${} < \epsilon/2$, 
      (c) either $P_i$ or $P_j$ is small (${}\le(\epsilon/4M)n$)
    Process (a) removes at most $(\epsilon/4)n^2$ edges. 
    Process (b) removes at most $(\epsilon/2)n^2$ edges.
    Process (c) removes at most $(\epsilon/4)n^2$ edges. 
   The remaining graph is triangle-free for some choice of $\delta$. \<close>
    
    define edge where "edge \<equiv> \<lambda>R S. mk_uedge ` (all_edges_between R S G)"
    have edge_commute: "edge R S = edge S R" for R S
      by (force simp add: edge_def all_edges_between_swap [of S] split: prod.split)
    have card_edge_le_card: "card (edge R S) \<le> card (all_edges_between R S G)" for R S
      by (simp add: card_image_le edge_def fin finite_all_edges_between' local.wf)
    have card_edge_le: "card (edge R S) \<le> card R * card S" if "R\<in>P" "S\<in>P" for R S
      by (meson card_edge_le_card fin_P le_trans max_all_edges_between that)
    
    text \<open>Obtain the set of edges meeting condition (a).\<close>
    
    define irreg_pairs where "irreg_pairs \<equiv> {(R,S). R \<in> P \<and> S \<in> P \<and> \<not> (\<epsilon>/4)-regular_pair R S G}"
    define Ea where "Ea \<equiv> (\<Union>(R,S) \<in> irreg_pairs. edge R S)"
    
    text \<open>Obtain the set of edges meeting condition (b).\<close>
    
    define low_density_pairs
      where "low_density_pairs \<equiv> {(R,S). R \<in> P \<and> S \<in> P \<and> \<not> edge_dense R S G (\<epsilon>/2)}"
    define Eb where "Eb \<equiv> (\<Union>(i,j) \<in> low_density_pairs. edge i j)"
    
    text \<open>Obtain the set of edges meeting condition (c).\<close>
    
    define small where "small \<equiv> \<lambda>R. R \<in> P \<and> card R \<le> ?e4M * ?n"
    let ?SMALL = "Collect small"
    define small_pairs where "small_pairs \<equiv> {(R,S). R \<in> P \<and> S \<in> P \<and> (small R \<or> small S)}"
    define Ec where "Ec \<equiv> (\<Union>R \<in> ?SMALL. \<Union>S \<in> P. edge R S)"
    have Ec_def': "Ec = (\<Union>(i,j) \<in> small_pairs. edge i j)"
      by (force simp: edge_commute small_pairs_def small_def Ec_def)
    have eabound: "card Ea \<le> (\<epsilon>/4) * ?n^2"  \<comment>\<open>Count the edge bound for @{term Ea}\<close>
    proof - 
      have \<section>: "\<And>R S. \<lbrakk>R \<in> P; S \<in> P\<rbrakk> \<Longrightarrow> card (edge R S) \<le> card R * card S"
        unfolding edge_def
        by (meson card_image_le fin_P finite_all_edges_between max_all_edges_between order_trans)
      have "irreg_pairs \<subseteq> P \<times> P"
        by (auto simp: irreg_pairs_def)
      then have "finite irreg_pairs"
        by (meson \<open>finite P\<close> finite_SigmaI finite_subset)
      have "card Ea \<le> (\<Sum>(R,S)\<in>irreg_pairs. card (edge R S))"
        by (simp add: Ea_def card_UN_le [OF \<open>finite irreg_pairs\<close>] case_prod_unfold)
      also have "\<dots> \<le> (\<Sum>(R,S) \<in> {(R,S). R\<in>P \<and> S\<in>P \<and> \<not> (\<epsilon>/4)-regular_pair R S G}. card R * card S)"
        unfolding irreg_pairs_def using \<section> by (force intro: sum_mono)
      also have "\<dots> = (\<Sum>(R,S) \<in> irregular_set (\<epsilon>/4) G P. card R * card S)"
        by (simp add: irregular_set_def)
      finally have "card Ea \<le> (\<Sum>(R,S) \<in> irregular_set (\<epsilon>/4) G P. card R * card S)" .
      with M show ?thesis
        unfolding regular_partition_def by linarith 
    qed
    have ebbound: "card Eb \<le> (\<epsilon>/2) * (?n^2)"  \<comment>\<open>Count the edge bound for @{term Eb}.\<close>
    proof -
      have \<section>: "\<And>R S. \<lbrakk>R \<in> P; S \<in> P; \<not> edge_dense R S G (\<epsilon> / 2)\<rbrakk>
           \<Longrightarrow> real (card (edge R S)) * 2 \<le> \<epsilon> * real (card R) * real (card S)"
        by (simp add: divide_simps edge_dense_def edge_density_def card_P_gt0) 
           (smt (verit, best) card_edge_le_card of_nat_le_iff mult.assoc)
      have subs: "low_density_pairs \<subseteq> P \<times> P"
        by (auto simp: low_density_pairs_def)
      then have "finite low_density_pairs"
        by (metis \<open>finite P\<close> finite_SigmaI finite_subset)
      have "real (card Eb) \<le> (\<Sum>(i,j)\<in>low_density_pairs. real (card (edge i j)))"
        unfolding Eb_def 
        by (smt (verit, ccfv_SIG) \<open>finite low_density_pairs\<close> card_UN_le of_nat_mono of_nat_sum 
 case_prod_unfold sum_mono)
      also have "\<dots> \<le> (\<Sum>(R,S)\<in>low_density_pairs. \<epsilon>/2 * card R * card S)"
        unfolding low_density_pairs_def by (force intro: sum_mono \<section>)
      also have "\<dots> \<le> (\<Sum>(R,S)\<in>P \<times> P. \<epsilon>/2 * card R * card S)"
        using subs \<open>\<epsilon> > 0\<close> by (intro sum_mono2) (auto simp: \<open>finite P\<close>)
      also have "\<dots> = \<epsilon>/2 * (\<Sum>(R,S)\<in>P \<times> P. card R * card S)"
        by (simp add: sum_distrib_left case_prod_unfold mult_ac)
      also have "\<dots> \<le> (\<epsilon>/2) * (?n^2)"
        using \<open>\<epsilon>>0\<close> sum_prod_le_prod_sum 
        by (simp add: power2_eq_square sum_product flip: sum.cartesian_product sum_card_P)
      finally show ?thesis .
    qed
    have ecbound: "card Ec \<le> (\<epsilon>/4) * (?n^2)"  \<comment>\<open>Count the edge bound for @{term Ec}.\<close>
    proof - 
      have edge_bound: "(card (edge R S)) \<le> ?e4M * ?n^2"
        if "S \<in> P" "small R" for R S
      proof -
        have "real (card R) \<le> \<epsilon> * ?n / (4 * real M)"
          using that by (simp add: small_def)
        with card_P_le [OF \<open>S\<in>P\<close>]
        have *: "real (card R) * real (card S) \<le> \<epsilon> * card (uverts G) / (4 * real M) * ?n"
          by (meson mult_mono of_nat_0_le_iff of_nat_mono order.trans)
        also have "\<dots> = ?e4M * ?n^2"
          by (simp add: power2_eq_square)
        finally show ?thesis
          by (smt (verit) card_edge_le of_nat_mono of_nat_mult small_def that)
      qed
      have subs: "?SMALL \<subseteq> P"
        by (auto simp: small_def)
      then obtain card_sp: "card (?SMALL) \<le> M" and "finite ?SMALL"
        using M_def \<open>finite P\<close> card_mono by (metis finite_subset)
      have "real (card Ec) \<le> (\<Sum>R \<in> ?SMALL. real (card (\<Union>S \<in> P. edge R S)))"
        unfolding Ec_def
        by (smt (verit, ccfv_SIG) \<open>finite ?SMALL\<close> card_UN_le of_nat_mono of_nat_sum case_prod_unfold sum_mono)
      also have "\<dots> \<le> (\<Sum>R \<in> ?SMALL. ?e4M * ?n^2)"
      proof (intro sum_mono)
        fix R assume i: "R \<in> Collect small"
        then have "R\<in>P" and card_Pi: "card R \<le> ?e4M * ?n"
          by (auto simp: small_def)
        let ?UE = "\<Union>(edge R ` (P))"
        have *: "real (card ?UE) \<le> real (card R * ?n)" 
        proof -
          have "?UE \<subseteq> mk_uedge ` (all_edges_between R (uverts G) G)"
            apply (simp add: edge_def UN_subset_iff Ball_def)
            by (meson all_edges_between_mono2 fin_part finite_graph_partition_subset image_mono)
          then have "card ?UE \<le> card (all_edges_between R (uverts G) G)"
            by (meson card_image_le card_mono fin finite_all_edges_between' finite_imageI wf le_trans)
          then show ?thesis
            by (meson of_nat_mono fin fin_P max_all_edges_between order.trans \<open>R\<in>P\<close>)
        qed
        also have "\<dots> \<le> ?e4M * real (?n\<^sup>2)"
          using card_Pi \<open>M > 0\<close> \<open>?n > 0\<close> by (force simp add: divide_simps power2_eq_square)
        finally show "real (card ?UE) \<le> ?e4M * real (?n\<^sup>2)" .
      qed
      also have "\<dots> \<le> card ?SMALL * (?e4M * ?n^2)"
        by simp
      also have "\<dots> \<le> M * (?e4M * ?n^2)"
        using egt by (intro mult_right_mono) (auto simp add: card_sp)
      also have "\<dots> \<le> (\<epsilon>/4) * (?n^2)"
        using \<open>M > 0\<close> by simp
      finally show ?thesis .
    qed
    \<comment>\<open>total count\<close>
    have prev1: "card (Ea \<union> Eb \<union> Ec) \<le> card (Ea \<union> Eb) + card Ec" by (simp add: card_Un_le)
    also have "\<dots> \<le> card Ea + card Eb + card Ec" by (simp add: card_Un_le)
    also have prev: "\<dots> \<le> (\<epsilon>/4)*(?n^2) + (\<epsilon>/2)*(?n^2) + (\<epsilon>/4)*(?n^2)"
      using eabound ebbound ecbound by linarith 
    finally have cutedgesbound: "card (Ea \<union> Eb \<union> Ec) \<le> \<epsilon> * (?n^2)" by simp

    define Gnew where "Gnew \<equiv> (uverts G, uedges G - (Ea \<union> Eb \<union> Ec))"
    show "\<exists>Gnew. ?\<Phi> G Gnew"
    proof (intro exI conjI)
      show verts: "uverts Gnew = uverts G" by (simp add: Gnew_def)
      have diffedges: "(Ea \<union> Eb \<union> Ec) \<subseteq> uedges G" 
        by (auto simp: Ea_def Eb_def Ec_def all_edges_between_def edge_def)
      then show edges: "uedges Gnew \<subseteq> uedges G"  
        by (simp add: Gnew_def)
      then have "uedges G - (uedges Gnew) = uedges G \<inter> (Ea \<union> Eb \<union> Ec) " 
        by (simp add: Gnew_def Diff_Diff_Int) 
      then have "uedges G - (uedges Gnew) = (Ea \<union> Eb \<union> Ec)" using diffedges
        by (simp add: Int_absorb1) 
      then have cardbound: "card (uedges G - uedges Gnew) \<le> \<epsilon> * (?n^2)" 
        using cutedgesbound by simp
      have graph_partition_new: "finite_graph_partition (uverts Gnew) P M" using verts
        by (simp add: fin_part) 
      have new_wf: "uwellformed Gnew" using subgraph_edge_wf verts edges wf by simp
      have new_fin: "finite (uverts Gnew)" using verts fin by simp
      
      text\<open> The notes by Bell and Grodzicki are quite useful for understanding the lines below.
         See pg 4 in the middle after the summary of the min edge counts.\<close>
      
      have irreg_pairs_swap: "(R,S) \<in> irreg_pairs \<longleftrightarrow> (S, R) \<in> irreg_pairs" for R S
        by (auto simp: irreg_pairs_def regular_pair_commute)
      have low_density_pairs_swap: "(R,S) \<in> low_density_pairs \<longleftrightarrow> (S,R) \<in> low_density_pairs" for R S
        by (simp add: low_density_pairs_def edge_density_commute edge_dense_def)
           (use all_edges_between_swap in blast)
      have small_pairs_swap: "(R,S) \<in> small_pairs \<longleftrightarrow> (S,R) \<in> small_pairs" for R S
        by (auto simp: small_pairs_def)

      have all_edges_if: 
        "all_edges_between R S Gnew 
         = (if (R,S) \<in> irreg_pairs \<union> low_density_pairs \<union> small_pairs then {} 
            else all_edges_between R S G)" 
        (is "?lhs = ?rhs")
        if ij: "R \<in> P" "S \<in> P" for R S
      proof
        show "?lhs \<subseteq> ?rhs"
          using that fin_part unfolding Gnew_def Ea_def Eb_def Ec_def'
          apply (simp add: all_edges_between_E_diff all_edges_between_E_Un all_edges_between_E_UN)
          apply (auto simp: edge_def in_mk_uedge_img_iff all_edges_between_def)
          done
      next
        have Ea: "all_edges_between R S (V, Ea) = {}"  
          if "(R,S) \<notin> irreg_pairs" for V
          using ij that P_disjnt
          by (auto simp: Ea_def doubleton_eq_iff edge_def all_edges_between_def irreg_pairs_def; 
              metis regular_pair_commute disjoint_iff_not_equal)
        have Eb: "all_edges_between R S (V, Eb) = {}"  
          if "(R,S) \<notin> low_density_pairs" for V
          using ij that  
          apply (auto simp: Eb_def edge_def all_edges_between_def low_density_pairs_def edge_dense_def)
           apply metis
          by (metis IntI P_disjnt doubleton_eq_iff edge_density_commute equals0D)
        have Ec: "all_edges_between R S (V, Ec) = {}"
          if "(R,S) \<notin> small_pairs" for V
          using ij that 
          by (auto simp: Ec_def' doubleton_eq_iff edge_def all_edges_between_def small_pairs_def;
              metis P_disjnt disjoint_iff)
        show "?rhs \<subseteq> ?lhs"
          by (auto simp add: Gnew_def Ea Eb Ec all_edges_between_E_diff all_edges_between_E_Un)
      qed

      have rp: "(\<epsilon>/4)-regular_pair R S Gnew" if ij: "R \<in> P" "S \<in> P" for R S
      proof (cases "(R,S) \<in> irreg_pairs")
        case False
        have ed: "edge_density X Y Gnew =
            (if (R,S) \<in> irreg_pairs \<union> low_density_pairs \<union> small_pairs then 0
             else edge_density X Y G)" 
          if "X \<subseteq> R" "Y \<subseteq> S" for X Y
          using all_edges_if that ij False 
          by (smt (verit) all_edges_preserved edge_density_eq0 edge_density_def) 
        show ?thesis
          using that False \<open>\<epsilon> > 0\<close>
          by (auto simp add: irreg_pairs_def regular_pair_def less_le ed)
      next
        case True
        then have ed: "edge_density X Y Gnew = 0"  if "X \<subseteq> R" "Y \<subseteq> S" for X Y
          by (meson edge_density_eq0 all_edges_if that \<open>R \<in> P\<close> \<open>S \<in> P\<close> UnCI)
        with egt that show ?thesis
          by (auto simp: regular_pair_def ed)
      qed
      then have reg_pairs: "(\<epsilon>/4)-regular_graph P Gnew"
        by (meson regular_graph_def)

      have "edge_dense R S Gnew (\<epsilon>/2)" 
        if "R \<in> P" "S \<in> P" for R S
      proof (cases "(R,S) \<in> low_density_pairs")
        case False
        have ed: "edge_density R S Gnew =
            (if (R,S) \<in> irreg_pairs \<union> low_density_pairs \<union> small_pairs then 0
             else edge_density R S G)" 
          using all_edges_if that that by (simp add: edge_density_def)
        with that \<open>\<epsilon> > 0\<close> False show ?thesis
          by (auto simp: low_density_pairs_def edge_dense_def all_edges_if)
      next
        case True
        then have "edge_density R S Gnew = 0" 
          by (simp add: all_edges_if edge_density_def that)
        with \<open>\<epsilon> > 0\<close> that show ?thesis
          by (simp add: True all_edges_if edge_dense_def)
      qed
      then have density_bound: "dense_graph P Gnew (\<epsilon>/2)"
        by (meson dense_graph_def)

      have min_subset_size: "decent_graph P Gnew (?e4M * ?n)"
        using \<open>\<epsilon> > 0\<close> 
        by (auto simp: decent_graph_def small_pairs_def small_def decent_def all_edges_if)
      show "triangle_free_graph Gnew"
      proof (rule ccontr) 
        assume non: "\<not>?thesis"
        then obtain x y z where trig_ex: "triangle_in_graph x y z Gnew" 
          using triangle_free_graph_def non by auto
        then have xin: "x \<in> (uverts Gnew)" and yin: "y \<in> (uverts Gnew)" and zin: "z \<in> (uverts Gnew)" 
          using triangle_in_graph_verts new_wf by auto
        then obtain R S T where xinp: "x \<in> R" and ilt: "R\<in>P" and yinp: "y \<in> S" and jlt: "S\<in>P"
                          and zinp: "z \<in> T" and klt: "T\<in>P" 
          by (metis graph_partition_new xin Union_iff finite_graph_partition_equals)
        then have finitesubsets: "finite R" "finite S" "finite T"
          using new_fin fin_part finite_graph_partition_finite fin by auto
        have subsets: "R \<subseteq> uverts Gnew" "S \<subseteq> uverts Gnew" "T \<subseteq> uverts Gnew" 
          using finite_graph_partition_subset ilt jlt klt graph_partition_new by auto
        have min_sizes: "card R \<ge> ?e4M*?n" "card S \<ge> ?e4M*?n" "card T \<ge> ?e4M*?n"
          using trig_ex min_subset_size xinp yinp zinp ilt jlt klt
          by (auto simp: triangle_in_graph_def decent_graph_def decent_def all_edges_between_def)
        have min_dens: "edge_density R S Gnew \<ge> \<epsilon>/2" "edge_density R T Gnew \<ge> \<epsilon>/2" "edge_density S T Gnew \<ge> \<epsilon>/2" 
          using density_bound ilt jlt klt xinp yinp zinp trig_ex 
          by (auto simp: dense_graph_def edge_dense_def all_edges_between_def triangle_in_graph_def)
        then have min_dens_diff: 
          "edge_density R S Gnew - \<epsilon>/4 \<ge> \<epsilon>/4" "edge_density R T Gnew - \<epsilon>/4 \<ge> \<epsilon>/4" "edge_density S T Gnew - \<epsilon>/4 \<ge> \<epsilon>/4" 
          by auto
        have mincard0: "(card R) * (card S) * (card T) \<ge> 0" by simp
        have gtcube: "((edge_density R S Gnew) - \<epsilon>/4)*((edge_density R T Gnew) - \<epsilon>/4) *((edge_density S T Gnew) - \<epsilon>/4) \<ge> (\<epsilon>/4)^3"
          using min_dens_diff e4gt real_mult_gt_cube by auto 
        then have c1: "((edge_density R S Gnew) - \<epsilon>/4)*((edge_density R T Gnew) - \<epsilon>/4) *((edge_density S T Gnew) - \<epsilon>/4) \<ge> 0"
          by (smt (verit) e4gt zero_less_power) 
        have "?e4M * ?n \<ge> 0"
          using egt by force
        then have "card R * card S * card T \<ge> (?e4M * ?n)^3"
          by (metis min_sizes of_nat_mult real_mult_gt_cube)
        then have cardgtbound:"card R * card S * card T \<ge> ?e4M^ 3 * ?n^3"
          by (metis of_nat_power power_mult_distrib)

        have "(1-\<epsilon>/2) * (\<epsilon>/4)^3 * (\<epsilon>/(4*M))^3 * ?n^3 \<le> (1-\<epsilon>/2) * (\<epsilon>/4)^3 * card R * card S * card T"
          using cardgtbound ordered_comm_semiring_class.comm_mult_left_mono True e4gt by fastforce
        also have "... \<le> (1-2*(\<epsilon>/4)) * (edge_density R S Gnew - \<epsilon>/4) * (edge_density R T Gnew - \<epsilon>/4) 
                        * (edge_density S T Gnew - \<epsilon>/4) * card R * card S * card T"
          using gtcube c1 \<open>\<epsilon> < 1\<close> mincard0 by (simp add: mult.commute mult.left_commute mult_left_mono)
        also have "... \<le> card (triangle_triples R S T Gnew)"
          by (smt (verit, best) e4gt ilt jlt klt min_dens_diff new_fin new_wf rp subsets triangle_counting_lemma)
        finally have "card (triangle_set Gnew) \<ge> D * ?n^3"
          using card_convert_triangle_rep_bound new_wf new_fin subsets 
          by (auto simp: triangle_triples_def D_def)
        then have g_tset_bound: "card (triangle_set G) \<ge> D * ?n^3" 
          using triangle_set_graph_edge_ss_bound by (smt (verit) edges fin local.wf of_nat_mono verts)
        have "card (triangle_set G) > \<delta> * ?n^3" 
        proof -
          have "?n^3 > 0"
            by (simp add: \<open>uverts G \<noteq> {}\<close> card_gt_0_iff fin)
          with \<delta> \<open>D0 \<le> D\<close> have "D * ?n^3 > \<delta> * ?n^3"
            by force
          thus "card (triangle_set G) > \<delta> * ?n ^3" 
            using g_tset_bound unfolding D_def by linarith 
        qed
        thus False
          using ineq by linarith
      qed
      show "real (card (uedges G - uedges Gnew)) \<le> \<epsilon> * real ((card (uverts G))\<^sup>2)"
        using cardbound edges verts by blast 
    qed
  qed (rule \<open>0 < \<delta>\<close>)
qed

subsection \<open>Roth's Theorem\<close>

text\<open>We will first need the following corollary of the Triangle Removal Lemma.\<close>

text \<open>See \<^url>\<open>https://en.wikipedia.org/wiki/Ruzsa--Szemerédi_problem\<close>.
Suggested by Yaël Dillies
\<close>
corollary Diamond_free:
  fixes \<epsilon> :: real 
  assumes "0 < \<epsilon>"
  shows "\<exists>N>0. \<forall>G. card(uverts G) > N \<longrightarrow> uwellformed G \<longrightarrow> unique_triangles G \<longrightarrow>
          card (uedges G) \<le> \<epsilon> * (card (uverts G))\<^sup>2"
proof -
  have "\<epsilon>/3 > 0"
    using assms by auto
  then obtain \<delta>::real where "\<delta> > 0"
    and \<delta>: "\<And>G. \<lbrakk>card(uverts G) > 0; uwellformed G; card (triangle_set G) \<le> \<delta> * card(uverts G) ^ 3\<rbrakk> 
                \<Longrightarrow> \<exists>G'. triangle_free_graph G' \<and> uverts G' = uverts G \<and> (uedges G' \<subseteq> uedges G) \<and> 
                         card (uedges G - uedges G') \<le> \<epsilon>/3 * (card (uverts G))\<^sup>2"
    using triangle_removal_lemma by metis
  obtain N::nat where N: "real N \<ge> 1 / (3*\<delta>)"
    by (meson real_arch_simple)
  show ?thesis
  proof (intro exI conjI strip)
    show "N > 0"
      using N \<open>0 < \<delta>\<close> zero_less_iff_neq_zero by fastforce
    fix G 
    let ?n = "card (uverts G)"
    assume G_gt_N: "N < ?n"
      and wf: "uwellformed G"
      and uniq: "unique_triangles G"
    have G_ne: "?n > 0"
      using G_gt_N by linarith
    let ?TWO = "(\<lambda>t. [t]\<^bsup>2\<^esup>)"
    have tri_nsets_2: "[{x,y,z}]\<^bsup>2\<^esup> = {{x,y},{y,z},{x,z}}" if "triangle_in_graph x y z G" for x y z
      using that unfolding nsets_def triangle_in_graph_def card_2_iff doubleton_eq_iff
      by (blast dest!: edge_vertices_not_equal [OF wf])
    have tri_nsets_3: "{{x,y},{y,z},{x,z}} \<in> [uedges G]\<^bsup>3\<^esup>" if "triangle_in_graph x y z G" for x y z
      using that by (simp add: nsets_def card_3_iff triangle_in_graph_def) 
                    (metis doubleton_eq_iff edge_vertices_not_equal [OF wf])
    have sub: "?TWO ` triangle_set G \<subseteq> [uedges G]\<^bsup>3\<^esup>"
      using tri_nsets_2 tri_nsets_3 triangle_set_def by auto
    have "\<And>i. i \<in> triangle_set G \<Longrightarrow> ?TWO i \<noteq> {}"
      using tri_nsets_2 triangle_set_def by auto
    moreover have dfam: "disjoint_family_on ?TWO (triangle_set G)"
      using sub [unfolded image_subset_iff] uniq
      unfolding disjoint_family_on_def triangle_set_def nsets_def unique_triangles_def
      by (smt (verit) disjoint_iff_not_equal insert_subset mem_Collect_eq mk_disjoint_insert )  
    ultimately have inj: "inj_on ?TWO (triangle_set G)"
      by (simp add: disjoint_family_on_iff_disjoint_image)
    have \<section>: "\<exists>T\<in>triangle_set G. e \<in> [T]\<^bsup>2\<^esup>" if "e \<in> uedges G" for e
      using uniq [unfolded unique_triangles_def] that local.wf
      apply (simp add: triangle_set_def triangle_in_graph_def nsets_def uwellformed_def)
      by (metis (mono_tags, lifting) finite.emptyI finite.insertI finite_subset)
    with sub have "\<Union>(?TWO ` triangle_set G) = uedges G"
      by (auto simp: image_subset_iff nsets_def)
    then have "card (\<Union>(?TWO ` triangle_set G)) = card (uedges G)"
      by simp
    moreover have "card (\<Union>(?TWO ` triangle_set G)) = 3 * card (triangle_set G)"
    proof (subst card_UN_disjoint' [OF dfam])
      show "finite ([i]\<^bsup>2\<^esup>)" if "i \<in> triangle_set G" for i 
        using that tri_nsets_2 triangle_set_def by fastforce
      show "finite (triangle_set G)"
        by (meson G_ne card_gt_0_iff local.wf finite_triangle_set)
      have "card ([i]\<^bsup>2\<^esup>) = 3" if "i \<in> triangle_set G" for i
        using that wf nsets_def tri_nsets_2 tri_nsets_3 triangle_set_def by fastforce
      then show "(\<Sum>i\<in>triangle_set G. card ([i]\<^bsup>2\<^esup>)) = 3 * card (triangle_set G)"
        by simp
    qed
    ultimately have 3: "3 * card (triangle_set G) = card (uedges G)" 
      by auto
    have "card (uedges G) \<le> card (all_edges(uverts G))"
      by (meson G_ne all_edges_finite card_gt_0_iff card_mono local.wf wellformed_all_edges)
    also have "\<dots> = ?n choose 2"
      by (metis G_ne card_all_edges card_eq_0_iff not_less0)
    also have "\<dots> \<le> ?n\<^sup>2"
      by (metis binomial_eq_0_iff binomial_le_pow linorder_not_le zero_le)
    finally have "card (uedges G) \<le> ?n\<^sup>2" .
    with 3 have "card (triangle_set G) \<le> ?n\<^sup>2 / 3" by linarith
    also have "\<dots> \<le> \<delta> * ?n ^ 3"
    proof -
      have "1 \<le> 3 * \<delta> * N"
        using N \<open>\<delta> > 0\<close> by (simp add: field_simps)
      also have "\<dots> \<le> 3 * \<delta> * ?n"
        using G_gt_N \<open>0 < \<delta>\<close> by force
      finally have "1 * ?n^2 \<le> (3 * \<delta> * ?n) * ?n^2"
        by (simp add: G_ne)
      then show ?thesis
        by (simp add: eval_nat_numeral mult_ac)
    qed
    finally have "card (triangle_set G) \<le> \<delta> * ?n ^ 3" .
    then obtain Gnew where Gnew: "triangle_free_graph Gnew" "uverts Gnew = uverts G" 
      "uedges Gnew \<subseteq> uedges G" and card_edge_diff: "card (uedges G - uedges Gnew) \<le> \<epsilon>/3 * ?n\<^sup>2"
      using G_ne \<delta> local.wf by meson
    
    text\<open>Deleting an edge removes at most one triangle from the graph by assumption,
         so the number of edges removed in this process is at least the number of triangles.\<close>
    
    obtain TF where TF: "\<And>e. e \<in> uedges G \<Longrightarrow> \<exists>x y z. TF e = {x,y,z} \<and> triangle_in_graph x y z G \<and> e \<subseteq> TF e"
      using uniq unfolding unique_triangles_def by metis
    have False
      if non: "\<And>e. e \<in> uedges G - uedges Gnew \<Longrightarrow> {x,y,z} \<noteq> TF e"
        and tri: "triangle_in_graph x y z G" for x y z
    proof -
      have "\<not> triangle_in_graph x y z Gnew"
        using Gnew triangle_free_graph_def by blast
      with tri obtain e where eG: "e \<in> uedges G - uedges Gnew" and esub: "e \<subseteq> {x,y,z}"
        using insert_commute triangle_in_graph_def by auto
      then show False
        by (metis DiffD1 TF tri uniq unique_triangles_def non [OF eG])
    qed
    then have "triangle_set G \<subseteq> TF ` (uedges G - uedges Gnew)"
      unfolding triangle_set_def by blast
    moreover have "finite (uedges G - uedges Gnew)"
      by (meson G_ne card_gt_0_iff finite_Diff finite_graph_def wf wellformed_finite)
    ultimately have "card (triangle_set G) \<le> card (uedges G - uedges Gnew)"
      by (meson surj_card_le)
    then show "card (uedges G) \<le> \<epsilon> * ?n\<^sup>2"
      using 3 card_edge_diff by linarith
  qed
qed

text\<open>We are now ready to proceed to the proof of Roth's Theorem for Arithmetic Progressions. \<close>

definition progression3 :: "'a::comm_monoid_add \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "progression3 k d \<equiv> {k, k+d, k+d+d}"

lemma p3_int_iff: "progression3 (int k) (int d) \<subseteq> int ` A \<longleftrightarrow> progression3 k d \<subseteq> A"
  apply (simp add: progression3_def image_iff)
  by (smt (verit, best) int_plus of_nat_eq_iff)

text\<open>We assume that a set of naturals $A \subseteq \{...<N \}$ does not have any arithmetic progression. 
We will then show that @{term A} is of cardinality $o(N)$.\<close>

lemma RothArithmeticProgressions_aux:
  fixes \<epsilon>::real
  assumes "\<epsilon> > 0"
  obtains M where "\<forall>N \<ge> M. \<forall>A \<subseteq> {..<N}. (\<nexists>k d. d>0 \<and> progression3 k d \<subseteq> A) \<longrightarrow> card A < \<epsilon> * real N"
proof -
  obtain L where "L>0"
    and L: "\<And>G. \<lbrakk>card(uverts G) > L; uwellformed G; unique_triangles G\<rbrakk> 
                \<Longrightarrow> card (uedges G) \<le> \<epsilon>/12 * (card (uverts G))\<^sup>2"
    by (metis assms Diamond_free less_divide_eq_numeral1(1) mult_eq_0_iff)
  show thesis
  proof (intro strip that)
    fix N A
    assume "L \<le> N" and A: "A \<subseteq> {..<N}"
      and non: "\<nexists>k d. 0 < d \<and> progression3 k d \<subseteq> A"
    then have "N > 0" using \<open>0 < L\<close> by linarith
    define M where "M \<equiv> Suc (2*N)"
    have M_mod_bound[simp]: "x mod M < M" for x
      by (simp add: M_def)
    have "odd M" "M>0" "N<M" by (auto simp: M_def)
    have "coprime M (Suc N)"
      unfolding M_def
      by (metis add_2_eq_Suc coprime_Suc_right_nat coprime_mult_right_iff mult_Suc_right)
    then have cop: "coprime M (1 + int N)"
      by (metis coprime_int_iff of_nat_Suc)
    have A_sub_M: "int ` A \<subseteq> {..<M}"
      using A by (force simp: M_def)
    have non_img_A: "\<nexists>k d. d > 0 \<and> progression3 k d \<subseteq> int ` A"
      by (metis imageE insert_subset non p3_int_iff pos_int_cases progression3_def)
    
    text\<open>Construct a tripartite graph @{term G} whose three parts are copies of @{text"\<int>/M\<int>"}.\<close>
    
    define part_of where "part_of \<equiv> \<lambda>\<xi>. (\<lambda>i. prod_encode (\<xi>,i)) ` {..<M}"
    define label_of_part where "label_of_part \<equiv> \<lambda>p. fst (prod_decode p)"
    define from_part where "from_part \<equiv> \<lambda>p. snd (prod_decode p)"
    have enc_iff [simp]: "prod_encode (a,i) \<in> part_of a' \<longleftrightarrow> a'=a \<and> i<M" for a a' i
      using \<open>0 < M\<close> by (clarsimp simp: part_of_def image_iff Bex_def) presburger
    have part_of_M: "p \<in> part_of a \<Longrightarrow> from_part p < M" for a p
      using from_part_def part_of_def by fastforce
    have disjnt_part_of: "a \<noteq> b \<Longrightarrow> disjnt (part_of a) (part_of b)" for a b
      by (auto simp: part_of_def disjnt_iff)
    have from_enc [simp]: "from_part (prod_encode (a,i)) = i" for a i
      by (simp add: from_part_def)
    have finpart [iff]: "finite (part_of a)" for a
      by (simp add: part_of_def \<open>0 < M\<close>)
    have cardpart [simp]: "card (part_of a) = M" for a
      using \<open>0 < M\<close>
      by (simp add: part_of_def eq_nat_nat_iff inj_on_def card_image)
    let ?X = "part_of 0"
    let ?Y = "part_of (Suc 0)"
    let ?Z = "part_of (Suc (Suc 0))"
    define diff where "diff \<equiv> \<lambda>a b. (int a - int b) mod (int M)"
    have inj_on_diff: "inj_on (\<lambda>x. diff x a) {..<M}" for a
      apply (clarsimp simp: diff_def inj_on_def)
      by (metis diff_add_cancel mod_add_left_eq mod_less nat_int of_nat_mod)
    have eq_mod_M: "(x - y) mod int M = (x' - y) mod int M \<Longrightarrow> x mod int M = x' mod int M" for x x' y
      by (simp add: mod_eq_dvd_iff)

    have diff_invert: "diff y x = int a \<longleftrightarrow> y = (x + a) mod M" if "y < M" "a\<in>A" for x y a
    proof -
      have "a < M"
        using A \<open>N < M\<close> that by auto
      show ?thesis
      proof
        assume "diff y x = int a"
        with that \<open>a<M\<close> have "int y = int (x+a) mod int M"
          by (smt (verit) diff_def eq_mod_M mod_less of_nat_add zmod_int)
        with that show "y = (x + a) mod M"
          by (metis nat_int zmod_int)
      qed (simp add: \<open>a < M\<close> diff_def mod_diff_left_eq zmod_int)
    qed

    define diff2 where "diff2 \<equiv> \<lambda>a b. ((int a - int b) * int(Suc N)) mod (int M)"
    have inj_on_diff2: "inj_on (\<lambda>x. diff2 x a) {..<M}" for a
      apply (clarsimp simp: diff2_def inj_on_def)
      by (metis eq_mod_M mult_mod_cancel_right [OF _ cop] int_int_eq mod_less zmod_int)
    have [simp]: "(1 + int N) mod int M = 1 + int N"
      using M_def \<open>0 < N\<close> by auto
    have diff2_by2: "(diff2 a b * 2) mod M = diff a b" for a b
    proof -
      have "int M dvd ((int a - int b) * int M)"
        by simp
      then have "int M dvd ((int a - int b) * int (Suc N) * 2 - (int a - int b))"
        by (auto simp: M_def algebra_simps)
      then show ?thesis
        by (metis diff2_def diff_def mod_eq_dvd_iff mod_mult_left_eq)
    qed
    have diff2_invert: "diff2 (((x + a) mod M + a) mod M) x = int a" if "a\<in>A" for x a
    proof -
      have 1: "((x + a) mod M + a) mod M = (x + 2*a) mod M"
        by (metis group_cancel.add1 mod_add_left_eq mult_2)
      have "(int ((x + 2*a) mod M) - int x) * (1 + int N) mod int M 
             = (int (x + 2*a) - int x) * (1 + int N) mod int M"
        by (metis mod_diff_left_eq mod_mult_cong of_nat_mod)
      also have "\<dots> = int (a * (Suc M)) mod int M"
        by (simp add: algebra_simps M_def)
      also have "\<dots> = int a mod int M"
        by simp
      also have "\<dots> = int a"
        using A M_def subsetD that by auto
      finally show ?thesis
        using that by (auto simp: 1 diff2_def)
    qed

    define Edges where "Edges \<equiv> \<lambda>X Y df. {{x,y}| x y. x \<in> X \<and> y \<in> Y \<and> df(from_part y) (from_part x) \<in> int ` A}"
    have Edges_subset: "Edges X Y df \<subseteq> Pow (X \<union> Y)" for X Y df
      by (auto simp: Edges_def)
    define XY where "XY \<equiv> Edges ?X ?Y diff"
    define YZ where "YZ \<equiv> Edges ?Y ?Z diff"
    define XZ where "XZ \<equiv> Edges ?X ?Z diff2"
    obtain [simp]: "finite XY" "finite YZ" "finite XZ"
      using Edges_subset unfolding XY_def YZ_def XZ_def
      by (metis finite_Pow_iff finite_UnI finite_subset finpart)
    define G where "G \<equiv> (?X \<union> ?Y \<union> ?Z, XY \<union> YZ \<union> XZ)"
    have finG: "finite (uverts G)" and cardG: "card (uverts G) = 3*M"
      by (simp_all add: G_def card_Un_disjnt disjnt_part_of)
    then have "card(uverts G) > L"
      using M_def \<open>L \<le> N\<close> by linarith 
    have "uwellformed G"
      by (fastforce simp: card_insert_if part_of_def G_def XY_def YZ_def XZ_def Edges_def uwellformed_def)
    have [simp]: "{prod_encode (\<xi>,x), prod_encode (\<xi>,y)} \<notin> XY"  
                 "{prod_encode (\<xi>,x), prod_encode (\<xi>,y)} \<notin> YZ"
                 "{prod_encode (\<xi>,x), prod_encode (\<xi>,y)} \<notin> XZ" for x y \<xi>
      by (auto simp: XY_def YZ_def XZ_def Edges_def doubleton_eq_iff)
    have label_ne_XY [simp]: "label_of_part p \<noteq> label_of_part q" if "{p,q} \<in> XY" for p q
      using that by (auto simp add: XY_def part_of_def Edges_def doubleton_eq_iff label_of_part_def)
    then have [simp]: "{p} \<notin> XY" for p
      by (metis insert_absorb2)
    have label_ne_YZ [simp]: "label_of_part p \<noteq> label_of_part q" if "{p,q} \<in> YZ" for p q
      using that by (auto simp add: YZ_def part_of_def Edges_def doubleton_eq_iff label_of_part_def)
    then have [simp]: "{p} \<notin> YZ" for p
      by (metis insert_absorb2)
    have label_ne_XZ [simp]: "label_of_part p \<noteq> label_of_part q" if "{p,q} \<in> XZ" for p q
      using that by (auto simp add: XZ_def part_of_def Edges_def doubleton_eq_iff label_of_part_def)
    then have [simp]: "{p} \<notin> XZ" for p
      by (metis insert_absorb2)
    have label012: "label_of_part v < 3" if "v \<in> uverts G" for v
      using that by (auto simp add: G_def eval_nat_numeral part_of_def label_of_part_def)

    have Edges_distinct: "\<And>p q r \<xi> \<zeta> \<gamma> \<beta> df df'. \<lbrakk>{p,q} \<in> Edges (part_of \<xi>) (part_of \<zeta>) df;
           {q,r} \<in> Edges (part_of \<xi>) (part_of \<zeta>) df;
           {p,r} \<in> Edges (part_of \<gamma>) (part_of \<beta>) df'; \<xi> \<noteq> \<zeta>; \<gamma> \<noteq> \<beta>\<rbrakk> \<Longrightarrow> False"
      apply (auto simp: disjnt_iff Edges_def doubleton_eq_iff conj_disj_distribR ex_disj_distrib)
      apply (metis disjnt_iff disjnt_part_of)+
      done
    have uniq: "\<exists>i<M. \<exists>d\<in>A. \<exists>x \<in> {p,q,r}. \<exists>y \<in> {p,q,r}. \<exists>z \<in> {p,q,r}. 
                   x = prod_encode(0, i)
                 \<and> y = prod_encode(1, (i+d) mod M)
                 \<and> z = prod_encode(2, (i+d+d) mod M)"
      if T: "triangle_in_graph p q r G" for p q r
    proof -
      obtain x y z where xy: "{x,y} \<in> XY" and yz: "{y,z} \<in> YZ" and xz: "{x,z} \<in> XZ"
        and x: "x \<in> {p,q,r}" and y: "y \<in> {p,q,r}" and z: "z \<in> {p,q,r}"
        using T apply (simp add: triangle_in_graph_def G_def XY_def YZ_def XZ_def)
        by (smt (verit, ccfv_SIG) Edges_distinct Zero_not_Suc insert_commute n_not_Suc_n)
      then have "x \<in> ?X" "y \<in> ?Y" "z \<in> ?Z"
        by (auto simp: XY_def YZ_def XZ_def Edges_def doubleton_eq_iff; metis disjnt_iff disjnt_part_of)+
      then obtain i j k where i: "x = prod_encode(0,i)" and j: "y = prod_encode(1,j)" 
        and k: "z = prod_encode(2,k)"
        by (metis One_nat_def Suc_1 enc_iff prod_decode_aux.cases prod_decode_inverse)
      obtain a1 where "a1 \<in> A" and a1: "(int j - int i) mod int M = int a1"
        using xy \<open>x \<in> ?X\<close> i j by (auto simp add: XY_def Edges_def doubleton_eq_iff diff_def)
      obtain a3 where "a3 \<in> A" and a3: "(int k - int j) mod int M = int a3"
        using yz \<open>x \<in> ?X\<close> j k by (auto simp add: YZ_def Edges_def doubleton_eq_iff diff_def)
      obtain a2 where "a2 \<in> A" and a2: "(int k - int i) mod int M = int (a2 * 2) mod int M"
        using xz \<open>x \<in> ?X\<close> i k apply (auto simp add: XZ_def Edges_def doubleton_eq_iff)
        by (metis diff2_by2 diff_def int_plus mult_2_right)
      obtain "a1<N" "a2<N" "a3<N"
        using A \<open>a1 \<in> A\<close> \<open>a2 \<in> A\<close> \<open>a3 \<in> A\<close> by blast
      then obtain "a1+a3 < M" "a2 * 2 < M"
        by (simp add: M_def)
      then have "int (a2 * 2) = int (a2 * 2) mod M"
        by force
      also have "\<dots> = int (a1 + a3) mod int M"
        using a1 a2 a3 by (smt (verit, del_insts) int_plus mod_add_eq)
      also have "\<dots> = int (a1+a3)"
        using \<open>a1 + a3 < M\<close> by force
      finally have "a2*2 = a1+a3"
        by presburger
      then obtain equal: "a3 - a2 = a2 - a1" "a2 - a3 = a1 - a2"
        by (metis Nat.diff_cancel diff_cancel2 mult_2_right)
      with \<open>a1 \<in> A\<close> \<open>a2 \<in> A\<close> \<open>a3 \<in> A\<close> have "progression3 a1 (a2 - a1) \<subseteq> A"
        apply (clarsimp simp: progression3_def)
        by (metis diff_is_0_eq' le_add_diff_inverse nle_le)
      with non equal have "a2 = a1"
        unfolding progression3_def
        by (metis \<open>a2 \<in> A\<close> \<open>a3 \<in> A\<close> add.right_neutral diff_is_0_eq insert_subset 
            le_add_diff_inverse not_gr_zero)
      then have "a3 = a2"
        using \<open>a2 * 2 = a1 + a3\<close> by force
      have k_minus_j: "(int k - int j) mod int M = int a1"
        by (simp add: \<open>a2 = a1\<close> \<open>a3 = a2\<close> a3)
      have i_to_j: "j mod M = (i+a1) mod M"
        by (metis a1 add_diff_cancel_left' add_diff_eq mod_add_right_eq nat_int of_nat_add of_nat_mod)
      have j_to_k: "k mod M = (j+a1) mod M"
        by (metis \<open>a2 = a1\<close> \<open>a3 = a2\<close> a3 add_diff_cancel_left' add_diff_eq mod_add_right_eq 
            nat_int of_nat_add of_nat_mod)
      have "i<M"
        using \<open>x \<in> ?X\<close> i by simp
      then show ?thesis
        using i j k x y z \<open>a1 \<in> A\<close>
        by (metis \<open>y \<in> ?Y\<close> \<open>z \<in>?Z\<close> enc_iff i_to_j j_to_k mod_add_left_eq mod_less)
    qed

    text\<open>Every edge of the graph G lies in exactly one triangle.\<close>
    have "unique_triangles G"
      unfolding unique_triangles_def
    proof (intro strip)
      fix e
      assume "e \<in> uedges G"
      then consider "e \<in> XY" | "e \<in> YZ" | "e \<in> XZ"
        using G_def by fastforce
      then show "\<exists>!T. \<exists>x y z. T = {x, y, z} \<and> triangle_in_graph x y z G \<and> e \<subseteq> T"
      proof cases
        case 1
        then obtain i j a where eeq: "e = {prod_encode(0,i), prod_encode(1,j)}"
          and "i<M" and "j<M"
          and df: "diff j i = int a" and "a \<in> A"
          by (auto simp: XY_def Edges_def part_of_def)
        let ?x = "prod_encode (0, i)"
        let ?y = "prod_encode (1, j)"
        let ?z = "prod_encode (2, (j+a) mod M)"
        have yeq: "j = (i+a) mod M"
          using diff_invert using \<open>a \<in> A\<close> df \<open>j<M\<close> by blast
        with \<open>a \<in> A\<close> \<open>j<M\<close> have "{?y,?z} \<in> YZ"
          by (fastforce simp: YZ_def Edges_def image_iff diff_invert)
        moreover have "{?x,?z} \<in> XZ"
          using \<open>a \<in> A\<close> by (fastforce simp: XZ_def Edges_def yeq diff2_invert \<open>i<M\<close>)
        ultimately have T: "triangle_in_graph ?x ?y ?z G"
          using \<open>e \<in> uedges G\<close> by (force simp add: G_def eeq triangle_in_graph_def)
        show ?thesis
        proof (intro ex1I)
          show "\<exists>x y z. {?x,?y,?z} = {x, y, z} \<and> triangle_in_graph x y z G \<and> e \<subseteq> {?x,?y,?z}"
            using T eeq by blast
          fix T
          assume "\<exists>p q r. T = {p, q, r} \<and> triangle_in_graph p q r G \<and> e \<subseteq> T"
          then obtain p q r where Teq: "T = {p,q,r}"
            and tri: "triangle_in_graph p q r G" and "e \<subseteq> T"
            by blast
          with uniq
          obtain i' a' x y z where "i'<M" "a' \<in> A"  
                 and x: "x \<in> {p,q,r}" and y: "y \<in> {p,q,r}" and z: "z \<in> {p,q,r}"
                 and xeq: "x = prod_encode(0, i')"
                 and yeq: "y = prod_encode(1, (i'+a') mod M)"
                 and zeq: "z = prod_encode(2, (i'+a'+a') mod M)"
            by metis
          then have sets_eq: "{x,y,z} = {p,q,r}" by auto
          with Teq \<open>e \<subseteq> T\<close> have esub': "e \<subseteq> {x,y,z}" by blast
          have "a' < M"
            using A \<open>N < M\<close> \<open>a' \<in> A\<close> by auto
          obtain "?x \<in> e" "?y \<in> e" using eeq by force
          then have "x = ?x"
            using esub' eeq yeq zeq by simp
          then have "y = ?y"
            using esub' eeq zeq by simp
          obtain eq': "i' = i" "(i'+a') mod M = j"
            using \<open>x = ?x\<close> xeq using \<open>y =?y\<close> yeq by auto
          then have "diff (i'+a') i' = int a'"
            by (simp add: diff_def \<open>a' < M\<close>)
          then have "a' = a"
            by (metis eq' df diff_def mod_diff_left_eq nat_int zmod_int)
          then have "z = ?z"
            by (metis \<open>y = ?y\<close> mod_add_left_eq prod_encode_eq snd_conv yeq zeq)
          then show "T = {?x,?y,?z}"
            using Teq \<open>x = ?x\<close> \<open>y = ?y\<close> sets_eq by presburger
        qed
      next
        case 2
        then obtain j k a where eeq: "e = {prod_encode(1,j), prod_encode(2,k)}"
          and "j<M" "k<M"
          and df: "diff k j = int a" and "a \<in> A"
          by (auto simp: YZ_def Edges_def part_of_def numeral_2_eq_2)
        let ?x = "prod_encode (0, (M+j-a) mod M)"
        let ?y = "prod_encode (1, j)"
        let ?z = "prod_encode (2, k)"
        have zeq: "k = (j+a) mod M"
          using diff_invert using \<open>a \<in> A\<close> df \<open>k<M\<close> by blast
        with \<open>a \<in> A\<close> \<open>k<M\<close> have "{?x,?z} \<in> XZ"
          unfolding XZ_def Edges_def image_iff
          apply (clarsimp simp: mod_add_left_eq doubleton_eq_iff conj_disj_distribR ex_disj_distrib)
          apply (smt (verit, ccfv_threshold) A \<open>N < M\<close> diff2_invert le_add_diff_inverse2 lessThan_iff 
                     linorder_not_less mod_add_left_eq  mod_add_self1 not_add_less1 order.strict_trans subsetD)
          done
        moreover 
        have "a < N" using A \<open>a \<in> A\<close> by blast
        with \<open>N < M\<close> have "((M + j - a) mod M + a) mod M = j mod M"
          by (simp add: mod_add_left_eq)
        then have "{?x,?y} \<in> XY"
          using \<open>a \<in> A\<close> \<open>j<M\<close> unfolding XY_def Edges_def
          by (force simp add: zeq image_iff diff_invert  doubleton_eq_iff ex_disj_distrib)
        ultimately have T: "triangle_in_graph ?x ?y ?z G"
          using \<open>e \<in> uedges G\<close> by (auto simp: G_def eeq triangle_in_graph_def)
        show ?thesis
        proof (intro ex1I)
          show "\<exists>x y z. {?x,?y,?z} = {x, y, z} \<and> triangle_in_graph x y z G \<and> e \<subseteq> {?x,?y,?z}"
            using T eeq by blast
          fix T
          assume "\<exists>p q r. T = {p, q, r} \<and> triangle_in_graph p q r G \<and> e \<subseteq> T"
          then obtain p q r where Teq: "T = {p,q,r}" and tri: "triangle_in_graph p q r G" and "e \<subseteq> T"
            by blast
          with uniq
          obtain i' a' x y z where "i'<M" "a' \<in> A"  
                 and x: "x \<in> {p,q,r}" and y: "y \<in> {p,q,r}" and z: "z \<in> {p,q,r}"
                 and xeq: "x = prod_encode(0, i')"
                 and yeq: "y = prod_encode(1, (i'+a') mod M)"
                 and zeq: "z = prod_encode(2, (i'+a'+a') mod M)"
            by metis
          then have sets_eq: "{x,y,z} = {p,q,r}" by auto
          with Teq \<open>e \<subseteq> T\<close> have esub': "e \<subseteq> {x,y,z}" by blast
          have "a' < M"
            using A \<open>N < M\<close> \<open>a' \<in> A\<close> by auto
          obtain "?y \<in> e" "?z \<in> e"
            using eeq by force
          then have "y = ?y"
            using esub' eeq xeq zeq by simp
          then have "z = ?z"
            using esub' eeq xeq by simp
          obtain eq': "(i'+a') mod M = j" "(i'+a'+a') mod M = k"
            using \<open>y = ?y\<close> yeq using \<open>z =?z\<close> zeq by auto
          then have "diff (i'+a'+a') (i'+a') = int a'"
            by (simp add: diff_def \<open>a' < M\<close>)
          then have "a' = a"
            by (metis M_mod_bound \<open>a' \<in> A\<close> df diff_invert eq' mod_add_eq mod_if of_nat_eq_iff)
          have "(M + ((i'+a') mod M) - a') mod M = (M + (i' + a') - a') mod M"
            by (metis Nat.add_diff_assoc2 \<open>a' < M\<close> less_imp_le_nat mod_add_right_eq)
          with \<open>i' < M\<close> have "(M + ((i'+a') mod M) - a') mod M = i'"
            by force
          with \<open>a' = a\<close> eq' have "(M + j - a) mod M = i'"
            by force
          with xeq have "x = ?x" by blast
          then show "T = {?x,?y,?z}"
            using Teq \<open>z = ?z\<close> \<open>y = ?y\<close> sets_eq by presburger
        qed
      next
        case 3
        then obtain i k a where eeq: "e = {prod_encode(0,i), prod_encode(2,k)}"
          and "i<M" and "k<M"
          and df: "diff2 k i = int a" and "a \<in> A"
          by (auto simp: XZ_def Edges_def part_of_def eval_nat_numeral)
        let ?x = "prod_encode (0, i)"
        let ?y = "prod_encode (1, (i+a) mod M)"
        let ?z = "prod_encode (2, k)"
        have keq: "k = (i+a+a) mod M"
          using diff2_invert [OF \<open>a \<in> A\<close>, of i] df \<open>k<M\<close> using inj_on_diff2 [of i]
          by (simp add: inj_on_def Ball_def mod_add_left_eq)
        with \<open>a \<in> A\<close>  have "{?x,?y} \<in> XY"
          using \<open>a \<in> A\<close> \<open>i<M\<close> \<open>k<M\<close> apply (auto simp: XY_def Edges_def)
          by (metis M_mod_bound diff_invert enc_iff from_enc imageI)
        moreover have "{?y,?z} \<in> YZ"
          apply (auto simp: YZ_def Edges_def image_iff eval_nat_numeral)
          by (metis M_mod_bound \<open>a \<in> A\<close> diff_invert enc_iff from_enc mod_add_left_eq keq)
        ultimately have T: "triangle_in_graph ?x ?y ?z G"
          using \<open>e \<in> uedges G\<close> by (force simp add: G_def eeq triangle_in_graph_def)
        show ?thesis
        proof (intro ex1I)
          show "\<exists>x y z. {?x,?y,?z} = {x, y, z} \<and> triangle_in_graph x y z G \<and> e \<subseteq> {?x,?y,?z}"
            using T eeq by blast
          fix T
          assume "\<exists>p q r. T = {p, q, r} \<and> triangle_in_graph p q r G \<and> e \<subseteq> T"
          then obtain p q r where Teq: "T = {p,q,r}" and tri: "triangle_in_graph p q r G" and "e \<subseteq> T"
            by blast
          with uniq obtain i' a' x y z where "i'<M" "a' \<in> A"  
                 and x: "x \<in> {p,q,r}" and y: "y \<in> {p,q,r}" and z: "z \<in> {p,q,r}"
                 and xeq: "x = prod_encode(0, i')"
                 and yeq: "y = prod_encode(1, (i'+a') mod M)"
                 and zeq: "z = prod_encode(2, (i'+a'+a') mod M)"
            by metis
          then have sets_eq: "{x,y,z} = {p,q,r}" by auto
          with Teq \<open>e \<subseteq> T\<close> have esub': "e \<subseteq> {x,y,z}" by blast
          have "a' < M"
            using A \<open>N < M\<close> \<open>a' \<in> A\<close> by auto
          obtain "?x \<in> e" "?z \<in> e" using eeq by force
          then have "x = ?x"
            using esub' eeq yeq zeq by simp
          then have "z = ?z"
            using esub' eeq yeq by simp
          obtain eq': "i' = i" "(i'+a'+a') mod M = k"
            using \<open>x = ?x\<close> xeq using \<open>z =?z\<close> zeq by auto
          then have "diff (i'+a') i' = int a'"
            by (simp add: diff_def \<open>a' < M\<close>)
          then have "a' = a"
            by (metis \<open>a' \<in> A\<close> add.commute df diff2_invert eq' mod_add_right_eq nat_int)
          then have "y = ?y"
            by (metis \<open>x = ?x\<close> prod_encode_eq snd_conv yeq xeq)
          then show "T = {?x,?y,?z}"
            using Teq \<open>x = ?x\<close> \<open>z = ?z\<close> sets_eq by presburger
        qed
      qed
    qed
    have *: "card (uedges G) \<le> \<epsilon>/12 * (card (uverts G))\<^sup>2"
      using L \<open>L < card (uverts G)\<close> \<open>unique_triangles G\<close> \<open>uwellformed G\<close> by blast

    have diff_cancel: "\<exists>j<M. diff j i = int a" if "a \<in> A" for i a
      using M_mod_bound diff_invert that by blast
    have diff2_cancel: "\<exists>j<M. diff2 j i = int a" if "a \<in> A" for i a
      using M_mod_bound diff2_invert that by blast

    have card_Edges: "card (Edges (part_of \<xi>) (part_of \<zeta>) df) = M * card A" (is "card ?E = _")
      if "\<xi> \<noteq> \<zeta>" and df_cancel: "\<forall>a\<in>A. \<forall>i<M. \<exists>j<M. df j i = int a" 
                 and df_inj: "\<forall>a. inj_on (\<lambda>x. df x a) {..<M}"  for \<xi> \<zeta> df
    proof -
      define R where "R \<equiv> \<lambda>\<xi> Y df u p. \<exists>x y i a. u = {x,y} \<and> p = (i,a) \<and> x = prod_encode (\<xi>,i) 
                                          \<and> y \<in> Y \<and> a \<in> A \<and> df(from_part y) (from_part x) = int a"
      have R_uniq: "\<lbrakk>R \<xi> (part_of \<zeta>) df u p; R \<xi> (part_of \<zeta>) df u p'; \<xi> \<noteq> \<zeta>\<rbrakk> \<Longrightarrow> p' = p" for u p p' \<xi> \<zeta> df
        by (auto simp add: R_def doubleton_eq_iff)
      define f where "f \<equiv> \<lambda>\<xi> Y df u. @p. R \<xi> Y df u p"
      have f_if_R: "f \<xi> (part_of \<zeta>) df u = p" if "R \<xi> (part_of \<zeta>) df u p" "\<xi> \<noteq> \<zeta>" for u p \<xi> \<zeta> df
        using R_uniq f_def that by blast
      have "bij_betw (f \<xi> (part_of \<zeta>) df) ?E ({..<M} \<times> A)"
        unfolding bij_betw_def inj_on_def
      proof (intro conjI strip)
        fix u u'
        assume "u \<in> ?E" and "u' \<in> ?E" 
          and eq: "f \<xi> (part_of \<zeta>) df u = f \<xi> (part_of \<zeta>) df u'"
        obtain x y a where u: "u = {x,y}" "x \<in> part_of \<xi>" "y \<in> part_of \<zeta>" "a \<in> A" 
          and df: "df (from_part y) (from_part x) = int a"
          using \<open>u \<in> ?E\<close> by (force simp add: Edges_def image_iff)
        then obtain i where i: "x = prod_encode (\<xi>,i)"
          using part_of_def by blast
        with u df R_def f_if_R that have fu: "f \<xi> (part_of \<zeta>) df u = (i,a)"
          by blast
        obtain x' y' a' where u': "u' = {x',y'}" "x' \<in> part_of \<xi>" "y' \<in> part_of \<zeta>" "a'\<in>A" 
           and df': "df (from_part y') (from_part x') = int a'"
          using \<open>u' \<in> ?E\<close> by (force simp add: Edges_def image_iff)
        then obtain i' where i': "x' = prod_encode (\<xi>,i')"
          using part_of_def by blast
        with u' df' R_def f_if_R that have fu': "f \<xi> (part_of \<zeta>) df u' = (i',a')" 
          by blast
        have "i'=i" "a' = a"
          using fu fu' eq by auto
        with i i' have "x = x'"
          by meson
        moreover have "from_part y = from_part y'"
          using df df' \<open>x = x'\<close> \<open>a' = a\<close> df_inj u'(3) u(3) 
          by (clarsimp simp add: inj_on_def) (metis part_of_M lessThan_iff)
        ultimately show "u = u'"
          using u u' by (metis enc_iff from_part_def prod.collapse prod_decode_inverse)
      next
        have "f \<xi> (part_of \<zeta>) df ` ?E \<subseteq> {..<M} \<times> A"
        proof (clarsimp simp: Edges_def)
          fix i a x y b
          assume "x \<in> part_of \<xi>" "y \<in> part_of \<zeta>" "df (from_part y) (from_part x) = int b"
            "b \<in> A" and feq: "(i, a) = f \<xi> (part_of \<zeta>) df {x, y}"
          then have "R \<xi> (part_of \<zeta>) df {x,y} (from_part x, b)"
            by (auto simp: R_def doubleton_eq_iff part_of_def)
          then have "(from_part x, b) = (i, a)"
            by (simp add: f_if_R feq from_part_def that)
          then show "i < M \<and> a \<in> A"
            using \<open>x \<in> part_of \<xi>\<close> \<open>b \<in> A\<close> part_of_M by fastforce
        qed
        moreover have "{..<M} \<times> A \<subseteq> f \<xi> (part_of \<zeta>) df ` ?E"
        proof clarsimp
          fix i a assume "a \<in> A" and "i < M"
          then obtain j where "j<M" and j: "df j i = int a"
            using df_cancel by metis
          then have fj: "f \<xi> (part_of \<zeta>) df {prod_encode (\<xi>, i), prod_encode (\<zeta>, j)} = (i,a)"
            by (metis R_def \<open>a \<in> A\<close> enc_iff f_if_R from_enc \<open>\<xi> \<noteq> \<zeta>\<close>)
          then have "{prod_encode (\<xi>,i), prod_encode (\<zeta>, j mod M)} \<in> Edges (part_of \<xi>) (part_of \<zeta>) df"
            apply (clarsimp simp: Edges_def doubleton_eq_iff)
            by (metis \<open>a \<in> A\<close> \<open>i < M\<close> \<open>j < M\<close> enc_iff from_enc image_eqI j mod_if)
          then show "(i,a) \<in> f \<xi> (part_of \<zeta>) df ` Edges (part_of \<xi>) (part_of \<zeta>) df"
            using \<open>j < M\<close> fj image_iff by fastforce
        qed
        ultimately show "f \<xi> (part_of \<zeta>) df ` ?E = {..<M} \<times> A" by blast
      qed
      then show ?thesis
        by (simp add: bij_betw_same_card card_cartesian_product)
    qed
    have [simp]: "disjnt XY YZ" "disjnt XY XZ" "disjnt YZ XZ"
      using disjnt_part_of unfolding XY_def YZ_def XZ_def Edges_def disjnt_def 
      by (clarsimp simp add: disjoint_iff doubleton_eq_iff, meson disjnt_iff n_not_Suc_n nat.discI)+
    have [simp]: "card XY = M * card A" "card YZ = M * card A"
      by (simp_all add: XY_def YZ_def card_Edges diff_cancel inj_on_diff)
    have [simp]: "card XZ = M * card A"
      by (simp_all add: XZ_def card_Edges diff2_cancel inj_on_diff2)
    have "card (uedges G) = 3 * M * card A"
      by (simp add: G_def card_Un_disjnt)
    then have "card A \<le> \<epsilon> * (real M / 4)"
      using * \<open>0 < M\<close> by (simp add: cardG power2_eq_square)
    also have "\<dots> < \<epsilon> * N"
      using \<open>N>0\<close> by (simp add: M_def assms)
    finally show "card A < \<epsilon> * N" .
  qed
qed

text\<open>We finally present the main statement formulated using the upper asymptotic density condition.\<close>

theorem RothArithmeticProgressions:
  assumes "upper_asymptotic_density A > 0"
  shows "\<exists>k d. d>0 \<and> progression3 k d \<subseteq> A"
proof (rule ccontr)
  assume non: "\<nexists>k d. 0 < d \<and> progression3 k d \<subseteq> A"
  obtain M where X: "\<forall>N \<ge> M. \<forall>A' \<subseteq> {..<N}. (\<nexists>k d. d>0 \<and> progression3 k d \<subseteq> A') 
                          \<longrightarrow> card A' < upper_asymptotic_density A / 2 * real N"
    by (metis half_gt_zero RothArithmeticProgressions_aux assms)
  then have "\<forall>N \<ge> M. card (A \<inter> {..<N}) < upper_asymptotic_density A / 2 * N"
    by (meson order_trans inf_le1 inf_le2 non)
  then have "upper_asymptotic_density A \<le> upper_asymptotic_density A / 2"
    by (force simp add: eventually_sequentially less_eq_real_def intro!: upper_asymptotic_densityI)
  with assms show False by linarith
qed

end



