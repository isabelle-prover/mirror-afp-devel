theory Turan
  imports
    "Girth_Chromatic.Ugraphs"
    "Random_Graph_Subgraph_Threshold.Ugraph_Lemmas"
begin

section \<open>Basic facts on graphs\<close>

lemma wellformed_uverts_0 :
  assumes "uwellformed G" and "uverts G = {}"
  shows "card (uedges G) = 0" using assms
  by (metis uwellformed_def card.empty ex_in_conv zero_neq_numeral)

lemma finite_verts_edges :
  assumes "uwellformed G" and "finite (uverts G)"
  shows "finite (uedges G)"
proof -
  have sub_pow: "uwellformed G \<Longrightarrow> uedges G \<subseteq> {S. S \<subseteq> uverts G}"
    by (cases G, auto simp add: uwellformed_def)
  then have "finite {S. S \<subseteq> uverts G}" using assms
    by auto
  with sub_pow assms show "finite (uedges G)"
    using finite_subset by blast
qed

lemma ugraph_max_edges :
  assumes "uwellformed G" and "card (uverts G) = n" and "finite (uverts G)"
  shows "card (uedges G) \<le> n * (n-1)/2"
  using assms wellformed_all_edges [OF assms(1)] card_all_edges [OF assms(3)] Binomial.choose_two [of "card(uverts G)"]
  by (smt (verit, del_insts) all_edges_finite card_mono dbl_simps(3) dbl_simps(5) div_times_less_eq_dividend le_divide_eq_numeral1(1) le_square nat_mult_1_right numerals(1) of_nat_1 of_nat_diff of_nat_mono of_nat_mult of_nat_numeral right_diff_distrib')

lemma subgraph_verts_finite : "\<lbrakk> finite (uverts G); subgraph G' G \<rbrakk> \<Longrightarrow> finite (uverts G')"
  using rev_finite_subset subgraph_def by auto

section \<open>Cliques\<close>

text \<open>In this section a straightforward definition of cliques for simple, undirected graphs is introduced.
Besides fundamental facts about cliques, also more specialized lemmata are proved in subsequent subsections.\<close>

definition uclique :: "ugraph \<Rightarrow> ugraph \<Rightarrow> nat \<Rightarrow> bool" where
  "uclique C G p \<equiv> p = card (uverts C) \<and> subgraph C G \<and> C = complete (uverts C)"

lemma clique_any_edge :
  assumes "uclique C G p" and "x \<in> uverts C" and "y \<in> uverts C" and "x \<noteq> y"
  shows "{x,y} \<in> uedges G"
  using assms
  apply (simp add: uclique_def complete_def all_edges_def subgraph_def)
  by (smt (verit, best) SigmaI fst_conv image_iff mem_Collect_eq mk_uedge.simps snd_conv subset_eq)

lemma clique_exists : "\<exists> C p. uclique C G p \<and> p \<le> card (uverts G)"
  using bex_imageD card.empty emptyE gr_implies_not0 le_neq_implies_less
  by (auto simp add: uclique_def complete_def subgraph_def all_edges_def)

lemma clique_exists1 :
  assumes "uverts G \<noteq> {}" and "finite (uverts G)"
  shows "\<exists> C p. uclique C G p \<and> 0 < p \<and>  p \<le> card (uverts G)"
proof -
  obtain x where x: "x \<in> uverts G"
    using assms
    by auto
  show ?thesis
    apply (rule exI [of _ "({x},{})"], rule exI [of _ 1])
    using x assms(2)
    by (simp add: uclique_def subgraph_def complete_def all_edges_def Suc_leI assms(1) card_gt_0_iff)
qed

lemma clique_max_size : "uclique C G p \<Longrightarrow> finite (uverts G) \<Longrightarrow>  p \<le> card (uverts G)"
  by (auto simp add: uclique_def subgraph_def Finite_Set.card_mono)

lemma clique_exists_gt0 :
  assumes "finite (uverts G)" "card (uverts G) > 0"
  shows "\<exists> C p. uclique C G p \<and> p \<le> card (uverts G) \<and> (\<forall>C q. uclique C G q \<longrightarrow> q \<le> p)"
proof -
  have 1: "finite (uverts G) \<Longrightarrow> finite {p. \<exists>C. uclique C G p}"
    using clique_max_size
    by (smt (verit, best) finite_nat_set_iff_bounded_le mem_Collect_eq)
  have 2: "\<And>A::nat set. finite A \<Longrightarrow> \<exists>x. x\<in>A \<Longrightarrow> \<exists>x\<in>A.\<forall>y\<in>A. y \<le> x"
    using Max_ge Max_in by blast
  have "\<exists>C p. uclique C G p \<and> (\<forall>C q. uclique C G q \<longrightarrow> q \<le> p)"
    using 2 [OF 1 [OF \<open>finite (uverts G)\<close>]] clique_exists [of G]
    by (smt (z3) mem_Collect_eq)
  then show ?thesis
    using \<open>finite (uverts G)\<close> clique_max_size
    by blast
qed

text \<open>If there exists a $(p+1)$-clique @{term C} in a graph @{term G}
      then we can obtain a $p$-clique in @{term G} by removing an arbitrary vertex from @{term C}\<close>

lemma clique_size_jumpfree :
  assumes "finite (uverts G)" and "uwellformed G"
    and "uclique C G (p+1)"
  shows "\<exists>C'. uclique C' G p"
proof -
  have "card(uverts G) > p"
    using assms by (simp add: uclique_def subgraph_def card_mono less_eq_Suc_le)
  obtain x where x: "x \<in> uverts C"
    using assms by (fastforce simp add: uclique_def)
  have "mk_uedge ` {uv \<in> uverts C \<times> uverts C. fst uv \<noteq> snd uv} - {A \<in> uedges C. x \<in> A} =
    mk_uedge ` {uv \<in> (uverts C - {x}) \<times> (uverts C - {x}). fst uv \<noteq> snd uv}"
  proof -
    have "\<And>y. y \<in> mk_uedge ` {uv \<in> uverts C \<times> uverts C. fst uv \<noteq> snd uv} - {A \<in> uedges C. x \<in> A} \<Longrightarrow>
          y \<in> mk_uedge ` {uv \<in> (uverts C - {x}) \<times> (uverts C - {x}). fst uv \<noteq> snd uv}"
      using assms(3)
      apply (simp add: uclique_def complete_def all_edges_def)
      by (smt (z3) DiffI SigmaE SigmaI image_iff insertCI mem_Collect_eq mk_uedge.simps singleton_iff snd_conv)
    moreover have "\<And>y. y \<in> mk_uedge ` {uv \<in> (uverts C - {x}) \<times> (uverts C - {x}). fst uv \<noteq> snd uv}
                  \<Longrightarrow> y \<in> mk_uedge ` {uv \<in> uverts C \<times> uverts C. fst uv \<noteq> snd uv} - {A \<in> uedges C. x \<in> A}"
      apply (simp add: uclique_def complete_def all_edges_def)
      by (smt (z3) DiffE SigmaE SigmaI image_iff insert_iff mem_Collect_eq mk_uedge.simps singleton_iff)
    ultimately show ?thesis
      by blast
  qed
  then have 1: "(uverts C - {x}, uedges C - {A \<in> uedges C. x \<in> A}) = Ugraph_Lemmas.complete (uverts C - {x})"
    using assms(3)
    apply (simp add: uclique_def complete_def all_edges_def)
    by (metis (no_types, lifting) snd_eqD)
  show ?thesis
    apply (rule exI [of _ "C -- x"])
    using assms x
    apply (simp add: uclique_def remove_vertex_def subgraph_def)
    apply (simp add: 1)
    by (auto simp add: complete_def all_edges_def)
qed

text \<open>The next lemma generalises the lemma @{thm [source] clique_size_jumpfree} to a proof of
 the existence of a clique of any size smaller than the size of the original clique.\<close>

lemma clique_size_decr :
  assumes "finite (uverts G)" and "uwellformed G"
    and "uclique C G p"
  shows "q \<le> p \<Longrightarrow> \<exists>C. uclique C G q" using assms
proof (induction q rule: measure_induct [of "\<lambda>x. p - x"])
  case (1 x)
  then show ?case
  proof (cases "x = p")
    case True
    then show ?thesis
      using \<open>uclique C G p\<close>
      by blast
  next
    case False
    with 1(2) have "x < p"
      by auto
    from \<open>x < p\<close> have "p - Suc x < p - x"
      by auto
    then show ?thesis
      using 1(1) assms(1,2,3) \<open>x < p\<close>
      using clique_size_jumpfree [OF \<open>finite (uverts G)\<close> \<open>uwellformed G\<close> _]
      by (metis "1.prems"(4) add.commute linorder_not_le not_less_eq plus_1_eq_Suc)
  qed
qed

text \<open>With this lemma we can easily derive by contradiction that
      if there is no $p$-clique then there cannot exist a clique of a size greater than @{term p}\<close>

corollary clique_size_neg_max :
  assumes "finite (uverts G)" and "uwellformed G"
    and "\<not>(\<exists>C. uclique C G p)"
  shows "\<forall>C q. uclique C G q \<longrightarrow> q < p"
proof (rule ccontr)
  assume 1: "\<not> (\<forall>C q. uclique C G q \<longrightarrow> q < p)"
  show False
  proof -
    obtain C q where C: "uclique C G q"
      and q: "q \<ge> p"
      using 1 linorder_not_less
      by blast
    show ?thesis
      using assms(3) q clique_size_decr [OF \<open>finite (uverts G)\<close> \<open>uwellformed G\<close> C ]
      using order_less_imp_le by blast
  qed
qed

corollary clique_complete :
  assumes "finite V" and "x \<le> card V"
  shows "\<exists>C. uclique C (complete V) x"
proof -
  have "uclique (complete V) (complete V) (card V)"
    by (simp add: uclique_def complete_def subgraph_def)
  then show ?thesis
    using clique_size_decr [OF _ complete_wellformed [of V] _ assms(2)] assms(1)
    by (simp add: complete_def)
qed

lemma subgraph_clique :
  assumes "uwellformed G" "subgraph C G" "C = complete (uverts C)"
  shows "{e \<in> uedges G. e \<subseteq> uverts C} = uedges C"
proof -
  from assms complete_wellformed [of "uverts C"] have "uedges C \<subseteq> {e \<in> uedges G. e \<subseteq> uverts C}"
    by (auto simp add: subgraph_def uwellformed_def)
  moreover from assms(1) complete_wellformed [of "uverts C"] have "{e \<in> uedges G. e \<subseteq> uverts C} \<subseteq> uedges C"
    apply (simp add: subgraph_def uwellformed_def complete_def card_2_iff all_edges_def)
    using assms(3)[unfolded complete_def all_edges_def] in_mk_uedge_img 
    by (smt (verit, ccfv_threshold) SigmaI fst_conv insert_subset mem_Collect_eq snd_conv subsetI)
  ultimately show ?thesis
    by auto
qed

text \<open>Next, we prove that in a graph @{term G} with a $p$-clique @{term C} and some vertex @{term v} outside of this clique,
there exists a $(p+1)$-clique in @{term G} if @{term v} is connected to all nodes in @{term C}.
The next lemma is an abstracted version that does not explicitly mention cliques:
If a vertex @{term n} has as many edges to a set of nodes @{term N} as there are nodes in @{term N}
then @{term n} is connected to all vertices in @{term N}.\<close>

lemma card_edges_nodes_all_edges :
  fixes G :: "ugraph" and  N :: "nat set" and E :: "nat set set" and n :: nat
  assumes "uwellformed G"
    and "finite N"
    and "N \<subseteq> uverts G" and "E \<subseteq> uedges G"
    and "n \<in> uverts G" and "n \<notin> N"
    and "\<forall>e \<in> E. \<exists>x \<in> N. {n,x} = e"
    and "card E = card N"
  shows "\<forall>x \<in> N. {n,x} \<in> E"
proof (rule ccontr)
  assume "\<not>(\<forall>x \<in> N. {n,x} \<in> E)"
  show False
  proof -
    obtain x where x: "x \<in> N" and e: "{n,x} \<notin> E"
      using \<open>\<not>(\<forall>x \<in> N. {n,x} \<in> E)\<close>
      by auto
    have "E \<subseteq> (\<lambda>y. {n,y}) ` (N - {x})"
      using Set.image_diff_subset \<open>\<forall>e \<in> E. \<exists>x \<in> N. {n,x} = e\<close> x e
      by auto
    then show ?thesis
      using \<open>finite N\<close> \<open>card E = card N\<close> x
      using surj_card_le [of "N - {x}" E "(\<lambda>y. {n,y})"]
      by (simp, metis card_gt_0_iff diff_less emptyE lessI linorder_not_le)
  qed
qed

subsection \<open>Partitioning edges along a clique\<close>

text \<open>Tur\'{a}n's proof partitions the edges of a graph into three partitions for a $(p-1)$-clique @{term C}:
All edges within @{term C}, all edges outside of @{term C}, and all edges between a vertex in @{term C} and a
vertex not in @{term C}.

We prove a generalized lemma that partitions the edges along some arbitrary set of vertices
which does not necessarily need to induce a clique.
Furthermore, in Tur\'{a}n's graph theorem we only argue about the cardinality of the partitions
so that we restrict this proof to showing that
the sum of the cardinalities of the partitions is equal to number of all edges.\<close>

lemma graph_partition_edges_card :
  assumes "finite (uverts G)" and "uwellformed G" and "A \<subseteq> (uverts G)"
  shows "card (uedges G) = card {e \<in> uedges G. e \<subseteq> A} + card {e \<in> uedges G.  e \<subseteq> uverts G - A} + card {e \<in> uedges G. e \<inter> A \<noteq> {} \<and> e \<inter> (uverts G - A) \<noteq> {}}"
  using assms
proof -
  have "uedges G = {e \<in> uedges G. e \<subseteq> A} \<union> {e \<in> uedges G.  e \<subseteq> (uverts G) - A} \<union> {e \<in> uedges G. e \<inter> A \<noteq> {} \<and> e \<inter> ((uverts G) - A) \<noteq> {}}"
    using assms uwellformed_def
    by blast
  moreover have "{e \<in> uedges G. e \<subseteq> A} \<inter> {e \<in> uedges G.  e \<subseteq> uverts G - A} = {}"
    using assms uwellformed_def
    by (smt (verit, ccfv_SIG) Diff_disjoint Int_subset_iff card.empty disjoint_iff mem_Collect_eq nat.simps(3) nat_1_add_1 plus_1_eq_Suc prod.sel(2) subset_empty)
  moreover have "({e \<in> uedges G. e \<subseteq> A} \<union> {e \<in> uedges G.  e \<subseteq> uverts G - A}) \<inter> {e \<in> uedges G. e \<inter> A \<noteq> {} \<and> e \<inter> (uverts G - A) \<noteq> {}} = {}"
    by blast
  moreover have "finite {e \<in> uedges G. e \<subseteq> A}" using assms
    by (simp add: finite_subset)
  moreover have "finite {e \<in> uedges G.  e \<subseteq> uverts G - A}" using assms
    by (simp add: finite_subset)
  moreover have "finite {e \<in> uedges G. e \<inter> A \<noteq> {} \<and> e \<inter> (uverts G - A) \<noteq> {}}"
    using assms finite_verts_edges
    by auto
  ultimately show ?thesis
    using assms Finite_Set.card_Un_disjoint
    by (smt (verit, best) finite_UnI)
qed

text \<open>Now, we turn to the problem of calculating the cardinalities of these partitions
when they are induced by the biggest clique in the graph.

First, we consider the number of edges in a $p$-clique.\<close>

lemma clique_edges_inside :
  assumes G1: "uwellformed G" and G2: "finite (uverts G)"
    and p: "p \<le> card (uverts G)" and n: "n = card(uverts G)"
    and C: "uclique C G p"
  shows "card {e \<in> uedges G. e \<subseteq> uverts C} = p * (p-1) / 2"
proof -
  have "2 dvd (card (uverts C) * (p - 1))"
    using C uclique_def
    by auto
  have "2 = real 2"
    by simp
  then show ?thesis
    using C uclique_def [of C G p] complete_def [of "uverts C"]
    using subgraph_clique [OF G1, of C] subgraph_verts_finite [OF assms(2), of C]
    using Real.real_of_nat_div [OF \<open>2 dvd (card (uverts C) * (p - 1))\<close>] Binomial.choose_two [of " card (uverts G)"]
    by (smt (verit, del_insts) One_nat_def approximation_preproc_nat(5) card_all_edges diff_self_eq_0 eq_imp_le left_diff_distrib' left_diff_distrib' linorder_not_less mult_le_mono2 n_choose_2_nat not_gr0 not_less_eq_eq of_nat_1 of_nat_diff snd_eqD)
qed

text \<open>Next, we turn to the number of edges that connect a node inside of the biggest clique with
a node outside of said clique. For that we start by calculating a bound for the number of
edges from one single node outside of the clique into the clique.\<close>

lemma clique_edges_inside_to_node_outside :
  assumes "uwellformed G" and "finite (uverts G)"
  assumes "0 < p" and "p \<le> card (uverts G)"
  assumes "uclique C G p" and "(\<forall>C p'. uclique C G p' \<longrightarrow> p' \<le> p)"
  assumes y: "y \<in> uverts G - uverts C"
  shows "card {{x,y}| x. x \<in> uverts C \<and> {x,y} \<in> uedges G} \<le> p - 1"
proof (rule ccontr)
  txt \<open>For effective proof automation we use a local function definition to compute this
       set of edges into the clique from any node @{term y}:\<close>
  define S where "S \<equiv> \<lambda>y. {{x,y}| x. x \<in> uverts C \<and> {x,y} \<in> uedges G}"
  assume "\<not> card {{x, y} |x. x \<in> uverts C \<and> {x, y} \<in> uedges G} \<le> p - 1"
  then have Sy: "card (S y) > p - 1"
    using S_def y by auto
  have "uclique ({y} \<union> (uverts C),S y \<union> uedges C) G (Suc p)"
  proof -
    have "card ({y} \<union> uverts C) = Suc p"
      using assms(3,5,7) uclique_def
      by (metis DiffD2 card_gt_0_iff card_insert_disjoint insert_is_Un)
    moreover have "subgraph ({y} \<union> uverts C, (S y) \<union> uedges C) G"
      using assms(5,7)
      by (auto simp add: uclique_def subgraph_def S_def)
    moreover have "({y} \<union> (uverts C),(S y) \<union> uedges C) = complete ({y} \<union> (uverts C))"
    proof -
      have "(S y) \<union> uedges C \<subseteq> all_edges ({y} \<union> (uverts C))"
        using y assms(5) S_def all_edges_def uclique_def complete_def
        by (simp, smt (z3) SigmaE SigmaI fst_conv image_iff in_mk_uedge_img insertCI mem_Collect_eq snd_conv subsetI)
      moreover have "all_edges ({y} \<union> (uverts C)) \<subseteq> (S y) \<union> uedges C"
      proof -
        have "\<forall>x\<in>uverts C. {y, x} \<in> S y"
        proof -
          have "card (S y) = card (uverts C)"
            using Sy assms(2,3,5,7) S_def uclique_def card_gt_0_iff
            using Finite_Set.surj_card_le [of "uverts C" "S y" "\<lambda>x. {x, y}"]
            by (smt (verit, del_insts) Suc_leI Suc_pred' image_iff le_antisym mem_Collect_eq subsetI)
          then show ?thesis
            using card_edges_nodes_all_edges [OF assms(1), of "uverts C" "S y" y] assms(1,2,5,7) S_def uclique_def
            by (smt (verit, ccfv_threshold) DiffE insert_commute mem_Collect_eq subgraph_def subgraph_verts_finite subsetI)
        qed
        then show ?thesis
          using assms(5) all_edges_def S_def uclique_def complete_def mk_uedge.simps in_mk_uedge_img
          by (smt (z3) insert_commute SigmaI fst_conv mem_Collect_eq snd_conv SigmaE UnCI image_iff insert_iff insert_is_Un subsetI)
      qed
      ultimately show ?thesis
        by (auto simp add: complete_def)
    qed
    ultimately show ?thesis
      by (simp add: uclique_def complete_def)
  qed
  then show False
    using assms(6)
    by fastforce
qed

text \<open>Now, that we have this upper bound for the number of edges from a single vertex into the largest clique
      we can calculate the upper bound for all such vertices and edges:\<close>

lemma clique_edges_inside_to_outside :
  assumes G1: "uwellformed G" and G2: "finite (uverts G)"
    and p0: "0 < p" and pn: "p \<le> card (uverts G)" and "card(uverts G) = n"
    and C: "uclique C G p" and C_max: "(\<forall>C p'. uclique C G p' \<longrightarrow> p' \<le> p)"
  shows "card {e \<in> uedges G. e \<inter> uverts C \<noteq> {} \<and> e \<inter> (uverts G - uverts C) \<noteq> {}} \<le> (p - 1) * (n - p)"
proof -
  define S where "S \<equiv> \<lambda>y. {{x,y}| x. x \<in> uverts C \<and> {x,y} \<in> uedges G}"
  have "card (uverts G - uverts C) = n - p"
    using pn C \<open>card(uverts G) = n\<close> G2
    apply (simp add: uclique_def)
    by (meson card_Diff_subset subgraph_def subgraph_verts_finite)
  moreover have "{e \<in> uedges G. e \<inter> uverts C \<noteq> {} \<and> e \<inter> (uverts G - uverts C) \<noteq> {}} = {{x,y}| x y. x \<in> uverts C \<and> y \<in> (uverts G - uverts C) \<and> {x,y} \<in> uedges G}"
  proof -
    have "e \<in> {e \<in> uedges G. e \<inter> uverts C \<noteq> {} \<and> e \<inter> (uverts G - uverts C) \<noteq> {}}
          \<Longrightarrow> \<exists>x y. e = {x,y} \<and> x \<in> uverts C \<and> y \<in> uverts G - uverts C" for e
      using G1
      apply (simp add: uwellformed_def)
      by (smt (z3) DiffD2 card_2_iff disjoint_iff_not_equal insert_Diff insert_Diff_if insert_iff)
    then show ?thesis
      by auto
  qed
  moreover have "card {{x,y}| x y. x \<in> uverts C \<and> y \<in> (uverts G - uverts C) \<and> {x,y} \<in> uedges G} \<le> card (uverts G - uverts C) * (p-1)"
  proof -
    have "card {{x,y}| x y. x \<in> uverts C \<and> y \<in> (uverts G - uverts C) \<and> {x,y} \<in> uedges G}
           \<le> (\<Sum>y \<in> (uverts G - uverts C). card (S y))"
    proof -
      have "finite (uverts G - uverts C)"
        using \<open>finite (uverts G)\<close> by auto
      have "{{x,y}| x y. x \<in> uverts C \<and> y \<in> (uverts G - uverts C) \<and> {x,y} \<in> uedges G}
           = (\<Union>y \<in> (uverts G - uverts C). {{x,y}| x. x \<in> uverts C \<and> {x,y} \<in> uedges G})"
        by auto
      then show ?thesis
        using Groups_Big.card_UN_le [OF \<open>finite (uverts G - uverts C)\<close>,
            of "\<lambda>y. {{x, y} |x. x \<in> uverts C \<and> {x, y} \<in> uedges G}"]
        using S_def
        by auto
    qed
    moreover have "(\<Sum>y\<in>uverts G - uverts C. card (S y)) \<le> card (uverts G - uverts C) * (p-1)"
    proof -
      have "card (S y) \<le> p - 1" if y: "y \<in> uverts G - uverts C" for y
        using clique_edges_inside_to_node_outside [OF assms(1,2,3,4) C C_max y] S_def y
        by simp
      then show ?thesis
        by (metis id_apply of_nat_eq_id sum_bounded_above)
    qed
    ultimately show ?thesis
      using order_trans
      by blast
  qed
  ultimately show ?thesis
    by (smt (verit, ccfv_SIG) mult.commute)
qed

text \<open>Lastly, we need to argue about the number of edges which are located entirely outside of
the greatest clique. Note that this is in the inductive step case in the overarching proof
of  Tur\'{a}n's graph theorem. That is why we have access to the inductive hypothesis as an
assumption in the following lemma:\<close>

lemma clique_edges_outside :
  assumes "uwellformed G" and "finite (uverts G)"
    and p2: "2 \<le> p" and pn: "p \<le> card (uverts G)" and n: "n = card(uverts G)"
    and C: "uclique C G (p-1)" and C_max: "(\<forall>C q. uclique C G q \<longrightarrow> q \<le> p-1)"
    and IH: "\<And>G y. y < n \<Longrightarrow> finite (uverts G) \<Longrightarrow> uwellformed G \<Longrightarrow> \<forall>C p'. uclique C G p' \<longrightarrow> p' < p
              \<Longrightarrow> 2 \<le> p \<Longrightarrow> card (uverts G) = y \<Longrightarrow> real (card (uedges G)) \<le> (1 - 1 / real (p - 1)) * real (y\<^sup>2) / 2"
  shows "card {e \<in> uedges G. e \<subseteq> uverts G - uverts C} \<le> (1 - 1 / (p-1)) * (n - p + 1) ^ 2 / 2"
proof -
  have "n - card (uverts C) < n"
    using C pn p2 n
    by (metis Suc_pred' diff_less less_2_cases_iff linorder_not_less not_gr0 uclique_def)
  have GC1: "finite (uverts (uverts G - uverts C, {e \<in> uedges G. e \<subseteq> uverts G - uverts C}))"
    using assms(2)
    by simp
  have GC2: "uwellformed (uverts G - uverts C, {e \<in> uedges G. e \<subseteq> uverts G - uverts C})"
    using assms(1)
    by (auto simp add: uwellformed_def)
  have GC3: "\<forall>C' p'. uclique C' (uverts G - uverts C, {e \<in> uedges G. e \<subseteq> uverts G - uverts C}) p' \<longrightarrow> p' < p"
  proof (rule ccontr)
    assume "\<not>(\<forall>C' p'. uclique C' (uverts G - uverts C, {e \<in> uedges G. e \<subseteq> uverts G - uverts C}) p' \<longrightarrow> p' < p)"
    then obtain C' p' where C': "uclique C' (uverts G - uverts C, {e \<in> uedges G. e \<subseteq> uverts G - uverts C}) p'" and p': "p' \<ge> p"
      by auto
    then have "uclique C' G p'"
      using uclique_def subgraph_def
      by auto
    then show False
      using p' p2 C_max
      by fastforce
  qed
  have GC4: "card (uverts (uverts G - uverts C,{e \<in> uedges G. e \<subseteq> uverts G - uverts C})) = n - card (uverts C)"
    using C n assms(2) uclique_def subgraph_def
    by (simp, meson card_Diff_subset infinite_super)
  show ?thesis
    using C GC3 IH [OF \<open>n - card (uverts C) < n\<close> GC1 GC2 GC3 \<open>2 \<le> p\<close> GC4] assms(2) n uclique_def
    by (simp, smt (verit, best) C One_nat_def Suc_1 Suc_leD clique_max_size of_nat_1 of_nat_diff p2)
qed

subsection \<open>Extending the size of the biggest clique\<close> text_raw \<open>\label{sec:extend_clique}\<close>

text \<open>In this section, we want to prove that we can add edges to a graph so that we augment the biggest clique
to some greater clique with a specific number of vertices. For that, we need the following lemma:
When too many edges have been added to a graph so that there exists a $(p+1)$-clique
then we can remove at least one of the added edges while also retaining a p-clique\<close>

lemma clique_union_size_decr :
  assumes "finite (uverts G)" and "uwellformed (uverts G, uedges G \<union> E)"
    and "uclique C (uverts G, uedges G \<union> E) (p+1)"
    and "card E \<ge> 1"
  shows "\<exists>C' E'. card E' < card E \<and> uclique C' (uverts G, uedges G \<union> E') p \<and> uwellformed (uverts G, uedges G \<union> E')"
proof (cases "\<exists>x \<in> uverts C. \<exists>e \<in> E. x \<in> e")
  case True
  then obtain x where x1: "x \<in> uverts C" and x2: "\<exists>e \<in> E. x \<in> e"
    by auto
  show ?thesis
  proof (rule exI [of _ "C -- x"], rule exI [of _ "{e \<in> E. x \<notin> e}"])
    have "card {e \<in> E. x \<notin> e} < card E"
      using x2 assms(4)
      by (smt (verit) One_nat_def card.infinite diff_is_0_eq mem_Collect_eq minus_nat.diff_0 not_less_eq psubset_card_mono psubset_eq subset_eq)
    moreover have "uclique (C -- x) (uverts G, uedges G \<union> {e \<in> E. x \<notin> e}) p"
    proof -
      have "p = card (uverts (C -- x))"
        using x1 assms(3)
        by (auto simp add: uclique_def remove_vertex_def)
      moreover have "subgraph (C -- x) (uverts G, uedges G \<union> {e \<in> E. x \<notin> e})"
        using assms(3)
        by (auto simp add: uclique_def subgraph_def remove_vertex_def)
      moreover have "C -- x = Ugraph_Lemmas.complete (uverts (C -- x))"
      proof -
        have 1: "\<And>y. y \<in> mk_uedge ` {uv \<in> uverts C \<times> uverts C. fst uv \<noteq> snd uv} - {A \<in> uedges C. x \<in> A} \<Longrightarrow>
            y \<in> mk_uedge ` {uv \<in> (uverts C - {x}) \<times> (uverts C - {x}). fst uv \<noteq> snd uv}"
          by (smt (z3) DiffE DiffI SigmaE SigmaI Ugraph_Lemmas.complete_def all_edges_def assms(3) empty_iff image_iff insert_iff mem_Collect_eq mk_uedge.simps snd_conv uclique_def)
        have 2: "\<And>y. y \<in> mk_uedge ` {uv \<in> (uverts C - {x}) \<times> (uverts C - {x}). fst uv \<noteq> snd uv} \<Longrightarrow>
            y \<in> mk_uedge ` {uv \<in> uverts C \<times> uverts C. fst uv \<noteq> snd uv} - {A \<in> uedges C. x \<in> A}"
          by (smt (z3) DiffE DiffI SigmaE SigmaI image_iff insert_iff mem_Collect_eq mk_uedge.simps singleton_iff)
        show ?thesis
          using assms(3)
          apply (simp add: remove_vertex_def complete_def all_edges_def uclique_def)
          using 1 2
          by (smt (verit, ccfv_SIG) split_pairs subset_antisym subset_eq)
      qed
      ultimately show ?thesis
        by (simp add: uclique_def)
    qed
    moreover have "uwellformed (uverts G, uedges G \<union> {e \<in> E. x \<notin> e})"
      using assms(2)
      by (auto simp add: uwellformed_def)
    ultimately show "card {e \<in> E. x \<notin> e} < card E \<and>
    uclique (C -- x) (uverts G, uedges G \<union> {e \<in> E. x \<notin> e}) p \<and>
    uwellformed (uverts G, uedges G \<union> {e \<in> E. x \<notin> e})"
      by auto
  qed
next
  case False
  then have "\<And>x. x \<in> uedges C \<Longrightarrow> x \<notin> E"
    using assms(2)
    by (metis assms(3) card_2_iff' complete_wellformed uclique_def uwellformed_def)
  then have "uclique C G (p+1)"
    using assms(3)
    by (auto simp add: uclique_def subgraph_def uwellformed_def)
  show ?thesis
    using assms(2,4) clique_size_jumpfree [OF assms(1) _ \<open>uclique C G (p+1)\<close>]
    apply (simp add: uwellformed_def)
    by (metis Suc_le_eq UnCI Un_empty_right card.empty prod.exhaust_sel)
qed

text \<open>We use this preceding lemma to prove the next result. In this lemma we assume that we have
added too many edges. The goal is then to remove some of the new edges appropriately so
that it is indeed guaranteed that there is no bigger clique.

Two proofs of this lemma will be described in the following.
Both fundamentally come down to the same core idea:
In essence, both proofs apply the well-ordering principle.
In the first proof we do so immediately by obtaining the minimum of a set:\<close>

lemma clique_union_make_greatest :
  fixes p n :: nat
  assumes "finite (uverts G)" and "uwellformed G"
    and "uwellformed (uverts G, uedges G \<union> E)" and "card(uverts G) \<ge> p"
    and "uclique C (uverts G, uedges G \<union> E) p"
    and "\<forall>C' q'. uclique C' G q' \<longrightarrow> q' < p" and "1 \<le> card E"
  shows "\<exists>C' E'. uwellformed (uverts G, uedges G \<union> E')
        \<and> (uclique C' (uverts G, uedges G \<union> E') p)
        \<and> (\<forall>C'' q'. uclique C'' (uverts G, uedges G \<union> E') q' \<longrightarrow> q' \<le> p)"
  using assms
proof  (induction "card E" arbitrary: C E rule: less_induct)
  case (less E)
  then show ?case
  proof (cases "\<exists>A. uclique A (uverts G, uedges G \<union> E) (p+1)")
    case True
    then obtain A where A: "uclique A (uverts G, uedges G \<union> E) (p+1)"
      by auto
    obtain C' E' where E'1: "card E' < card E"
      and E'2: "uclique C' (uverts G, uedges G \<union> E') p"
      and E'3: "uwellformed (uverts G, uedges G \<union> E')"
      and E'4: "1 \<le> card E'"
      using less(7)
      using clique_union_size_decr [OF assms(1) \<open>uwellformed (uverts G, uedges G \<union> E)\<close> A less(8)]
      by (metis One_nat_def Suc_le_eq Un_empty_right card_gt_0_iff finite_Un finite_verts_edges fst_conv less.prems(1) less_not_refl prod.collapse snd_conv)
    show ?thesis
      using less(1) [OF E'1 assms(1,2) E'3 less(5) E'2 less(7) E'4]
      using E'1 less(8)
      by (meson less_or_eq_imp_le order_le_less_trans)
  next
    case False
    show ?thesis
      apply (rule exI [of _ C], rule exI [of _ E])
      using clique_size_neg_max [OF _ less(4) False]
      using less(2,4,6)
      by fastforce
  qed
qed

text \<open>In this second, alternative proof the well-ordering principle is used through complete induction.\<close>

lemma clique_union_make_greatest_alt :
  fixes p n :: nat
  assumes "finite (uverts G)" and "uwellformed G"
    and "uwellformed (uverts G, uedges G \<union> E)" and "card(uverts G) \<ge> p"
    and "uclique C (uverts G, uedges G \<union> E) p"
    and "\<forall>C' q'. uclique C' G q' \<longrightarrow> q' < p" and "1 \<le> card E"
  shows "\<exists>C' E'. uwellformed (uverts G, uedges G \<union> E')
        \<and> (uclique C' (uverts G, uedges G \<union> E') p)
        \<and> (\<forall>C'' q'. uclique C'' (uverts G, uedges G \<union> E') q' \<longrightarrow> q' \<le> p)"
proof -
  define P where "P \<equiv> \<lambda>E. uwellformed (uverts G, uedges G \<union> E) \<and> (\<exists>C. uclique C (uverts G, uedges G \<union> E) p)"
  have "finite {y. \<exists>E. P E \<and> card E = y}"
  proof -
    have "\<And>E. P E \<Longrightarrow> E \<subseteq> Pow (uverts G)"
      by (auto simp add: P_def uwellformed_def)
    then have "finite {E. P E}"
      using assms(1)
      by (metis Collect_mono Pow_def finite_Pow_iff rev_finite_subset)
    then show ?thesis
      by simp
  qed
  obtain F where F1: "P F"
    and F2: "card F = Min {y. \<exists>E. P E \<and> card E = y}"
    and F3: "card F > 0"
    using assms(1,3,4,5,6) Min_in \<open>finite {y. \<exists>E. P E \<and> card E = y}\<close> P_def CollectD Collect_empty_eq
    by (smt (verit, ccfv_threshold) Un_empty_right card_gt_0_iff finite_Un finite_verts_edges fst_conv le_refl linorder_not_le prod.collapse snd_conv)
  have "p > 0"
    using assms(6) clique_exists bot_nat_0.not_eq_extremum
    by blast
  then show ?thesis
  proof (cases "\<exists>C. uclique C (uverts G, uedges G \<union> F) (p + 1)")
    case True
    then obtain F' where F'1 : "P F'" and F'2: "card F' < card F"
      using F1 F2 F3 clique_union_size_decr [OF assms(1), of F _ p] P_def
      by (smt (verit) One_nat_def Suc_eq_plus1 Suc_leI add_2_eq_Suc' assms(1) clique_size_jumpfree fst_conv)
    then show ?thesis
      using F2 \<open>finite {y. \<exists>F. P F \<and> card F = y}\<close> Min_gr_iff
      by fastforce
  next
    case False
    then show ?thesis
      using clique_size_neg_max [OF _ _ False]
      using assms(1) F1 P_def
      by (smt (verit, ccfv_SIG) Suc_eq_plus1 Suc_leI fst_conv linorder_not_le)
  qed
qed

text \<open>Finally, with this lemma we can turn to this section's main challenge of increasing the
greatest clique size of a graph by adding edges.\<close>

lemma clique_add_edges_max :
  fixes p :: nat
  assumes "finite (uverts G)"
    and "uwellformed G" and "card(uverts G) > p"
    and "\<exists>C. uclique C G p" and "(\<forall>C q'. uclique C G q' \<longrightarrow> q' \<le> p)"
    and "q \<le> card(uverts G)" and "p \<le> q"
  shows "\<exists>E. uwellformed (uverts G, uedges G \<union> E) \<and> (\<exists>C. uclique C (uverts G, uedges G \<union> E) q)
        \<and> (\<forall>C q'. uclique C (uverts G, uedges G \<union> E) q' \<longrightarrow> q' \<le> q)"
proof (cases "p < q")
  case True
  then show ?thesis
  proof -
    have "\<exists>E. uwellformed (uverts G, uedges G \<union> E) \<and> (\<exists>C. uclique C (uverts G, uedges G \<union> E) q) \<and> card E \<ge> 1"
      apply (rule exI [of _ "all_edges (uverts G)"])
      using Set.Un_absorb1 [OF wellformed_all_edges [OF assms(2)]]
      using complete_wellformed [of "uverts G"] clique_complete [OF assms(1,6)]
      using all_edges_def assms(1,5)
      apply (simp add: complete_def)
      by (metis Suc_leI True Un_empty_right all_edges_finite card_gt_0_iff linorder_not_less prod.collapse)
    then obtain E C where E1: "uwellformed (uverts G, uedges G \<union> E)"
      and E2: "uclique C (uverts G, uedges G \<union> E) q"
      and E3: "card E \<ge> 1"
      by auto
    show ?thesis
      using clique_union_make_greatest [OF assms(1,2) E1 assms(6) E2 _ E3] assms(5) True
      using order_le_less_trans
      by blast
  qed
next
  case False
  show ?thesis
    apply (rule exI [of _ "{}"])
    using False assms(2,4,5,7)
    by simp
qed

section \<open>Properties of the upper edge bound\<close>

text \<open>In this section we prove results about the upper edge bound in Tur\'{a}n's theorem.
The first lemma proves that upper bounds of the sizes of the partitions sum up exactly to the overall upper bound.\<close>

lemma turan_sum_eq :
  fixes n p :: nat
  assumes "p \<ge> 2" and "p \<le> n"
  shows "(p-1) * (p-2) / 2 + (1 - 1 / (p-1)) * (n - p + 1) ^ 2 / 2 + (p - 2) * (n - p + 1) = (1 - 1 / (p-1)) * n^2 / 2"
proof -
  have "a * (a-1) / 2 + (1 - 1 / a) * (n - a) ^ 2 / 2 + (a - 1) * (n - a)  = (1 - 1 / a) * n^2 / 2"
    if a1: "a \<ge> 1" and a2: "n \<ge> a"
    for a :: nat
  proof -
    have "a\<^sup>2 + (n - a)\<^sup>2 + a * (n - a) * 2 = n\<^sup>2"
      using a2
      apply (simp flip: Groups.ab_semigroup_mult_class.mult.commute [of 2 "a * (n - a)"])
      apply (simp add: Semiring_Normalization.comm_semiring_1_class.semiring_normalization_rules(18) [of 2 a "(n - a)"])
      by (simp flip: Power.comm_semiring_1_class.power2_sum [of a "n-a"])
    then have "((a - 1) / a) * (a ^ 2 + (n - a) ^ 2 + a * (n - a) * 2) = ((a - 1) / a) * n^2"
      by presburger
    then have "(((a - 1) / a) * a ^ 2 + ((a - 1) / a) * (n - a) ^ 2 + ((a - 1) / a) * a * (n - a) * 2) = ..."
      using Rings.semiring_class.distrib_left [of "(a - 1) / a" "a\<^sup>2 + (n - a)\<^sup>2" "a * (n - a) * 2"]
      using Rings.semiring_class.distrib_left [of "(a - 1) / a" "a\<^sup>2" "(n - a)\<^sup>2"]
      by auto
    moreover have "((a - 1) / a) * a ^ 2 = a * (a-1)"
      by (simp add: power2_eq_square)
    ultimately have "a * (a-1) + ((a - 1) / a) * (n - a) ^ 2 + (a - 1) * (n - a) * 2  = ((a - 1) / a) * n^2"
      using a1 a2
      by auto
    moreover have "1 - 1 / a = (a - 1) / a"
      by (smt (verit, del_insts) One_nat_def Suc_pred diff_divide_distrib diff_is_0_eq of_nat_1 of_nat_diff of_nat_le_0_iff of_nat_le_iff of_nat_less_iff right_inverse_eq that)
    ultimately have "a * (a-1) + (1 - 1 / a) * (n - a) ^ 2 + (a - 1) * (n - a) * 2  = (1 - 1 / a) * n^2"
      by simp
    then show ?thesis
      by simp
  qed
  moreover have "p - 1 \<ge> 1"
    using \<open>p \<ge> 2\<close> by auto
  moreover have "n \<ge> p - 1"
    using assms(2) by auto
  ultimately show ?thesis
    by (smt (verit) assms Nat.add_diff_assoc2 Nat.diff_diff_right diff_diff_left le_eq_less_or_eq less_Suc_eq_le linorder_not_less nat_1_add_1 plus_1_eq_Suc)
qed

text \<open>The next fact proves that the upper bound of edges is monotonically increasing with the size of the biggest clique.\<close>

lemma turan_mono :
  fixes n p q :: nat
  assumes "0 < q" and "q < p" and "p \<le> n"
  shows "(1 - 1 / q) * n^2 / 2 \<le> (1 - 1 / (p-1)) * n^2 / 2"
  using assms
  by (simp add: Extended_Nonnegative_Real.divide_right_mono_ennreal Real.inverse_of_nat_le)

section \<open>Tur\'{a}n's Graph Theorem\<close>

text \<open>In this section we turn to the direct adaptation of Tur\'{a}n's original proof as presented by Aigner and Ziegler \cite{Aigner2018}\<close>

theorem turan :
  fixes p n :: nat
  assumes "finite (uverts G)"
    and "uwellformed G" and "\<forall>C p'. uclique C G p' \<longrightarrow> p' < p" and "p \<ge> 2" and "card(uverts G) = n"
  shows "card (uedges G) \<le> (1 - 1 / (p-1)) * n^2 / 2" using assms
proof (induction n arbitrary: G rule: less_induct)
  case (less n)
  then show ?case
  proof (cases "n < p")
    case True
    show ?thesis
    proof (cases "n")
      case 0
      with less True show ?thesis
        by (auto simp add: wellformed_uverts_0)
    next
      case (Suc n')
      with True have "(1 - 1 / real n) \<le> (1 - 1 / real (p - 1))"
        by (metis diff_Suc_1 diff_left_mono inverse_of_nat_le less_Suc_eq_le linorder_not_less list_decode.cases not_add_less1 plus_1_eq_Suc)
      moreover have "real (card (uedges G)) \<le> (1 - 1 / real n) * real (n\<^sup>2) / 2"
        using ugraph_max_edges [OF less(3,6,2)]
        by (smt (verit, ccfv_SIG) left_diff_distrib mult.right_neutral mult_of_nat_commute nonzero_mult_div_cancel_left of_nat_1 of_nat_mult power2_eq_square times_divide_eq_left)
      ultimately show ?thesis
        using Rings.ordered_semiring_class.mult_right_mono divide_less_eq_numeral1(1) le_less_trans linorder_not_less of_nat_0_le_iff
        by (smt (verit, ccfv_threshold) divide_nonneg_nonneg times_divide_eq_right)
    qed
  next
    case False
    show ?thesis
    proof -
      obtain C q where C: "uclique C G q"
        and C_max: "(\<forall>C q'. uclique C G q' \<longrightarrow> q' \<le> q)"
        and q: "q < card (uverts G)"
        using clique_exists_gt0 [OF \<open>finite (uverts G)\<close>] False \<open>p \<ge> 2\<close> less.prems(1,3,5)
        by (metis card.empty card_gt_0_iff le_eq_less_or_eq order_less_le_trans pos2)
      obtain E C' where E: "uwellformed (uverts G, uedges G \<union> E)"
        and C': "(uclique C' (uverts G, uedges G \<union> E) (p-1))"
        and C'_max: "(\<forall>C q'. uclique C (uverts G, uedges G \<union> E) q' \<longrightarrow> q' \<le> p-1)"
        using clique_add_edges_max [OF \<open>finite (uverts G)\<close> \<open>uwellformed G\<close> q _ C_max, of "p-1"]
        using C less(4) less(5) False \<open>card (uverts G) = n\<close>
        by (smt (verit) One_nat_def Suc_leD Suc_pred less_Suc_eq_le linorder_not_less order_less_le_trans pos2)
      have "card {e \<in> uedges G \<union> E. e \<subseteq> uverts C'} = (p-1) * (p-2) / 2"
        using clique_edges_inside [OF E _ _ _ C'] False less(2) less.prems(4) C'
        by (smt (verit, del_insts) Collect_cong Suc_1 add_leD1 clique_max_size fst_conv of_nat_1 of_nat_add of_nat_diff of_nat_mult plus_1_eq_Suc snd_conv)
      moreover have "card {e \<in> uedges G \<union> E. e \<subseteq> uverts G - uverts C'} \<le> (1 - 1 / (p-1)) * (n - p + 1) ^ 2 / 2"
      proof -
        have "real(card{e \<in> uedges (uverts G, uedges G \<union> E). e \<subseteq> uverts (uverts G, uedges G \<union> E) - uverts C'})
              \<le> (1 - 1 / (real p - 1)) * (real n - real p + 1)\<^sup>2 / 2"
          using clique_edges_outside [OF E _ less(5) _ _ C' C'_max, of n] linorder_class.leI [OF False] less(1,2,6)
          by (metis (no_types, lifting) fst_conv)
        then show ?thesis
          by (simp, smt (verit, best) False One_nat_def Suc_1 Suc_leD add.commute leI less.prems(4) of_nat_1 of_nat_diff)
      qed
      moreover have "card {e \<in> uedges G \<union> E. e \<inter> uverts C' \<noteq> {} \<and> e \<inter> (uverts G - uverts C') \<noteq> {}} \<le> (p - 2) * (n - p + 1)"
        using clique_edges_inside_to_outside [OF E _ _ _ _ C' C'_max, of  n] less(2,5,6)
        by (simp, metis (no_types, lifting) C' False Nat.add_diff_assoc Nat.add_diff_assoc2 One_nat_def Suc_1 clique_max_size fst_conv leI mult_Suc_right plus_1_eq_Suc)
      ultimately have "real (card (uedges G \<union> E)) \<le> (1 - 1 / real (p - 1)) * real (n\<^sup>2) / 2"
        using graph_partition_edges_card [OF _ E, of "uverts C'"]
        using less(2) turan_sum_eq [OF \<open>2 \<le> p\<close>, of n] False C' uclique_def subgraph_def
        by (smt (verit) Collect_cong fst_eqD linorder_not_le of_nat_add of_nat_mono snd_eqD)
      then show ?thesis
        using less(2) E finite_verts_edges Finite_Set.card_mono [OF _ Set.Un_upper1 [of "uedges G" E]]
        by force
    qed
  qed
qed

section \<open>A simplified proof of Tur\'{a}n's Graph Theorem\<close>

text \<open>In this section we discuss a simplified proof of Tur\'{a}n's Graph Theorem which uses an idea put forward by the author:
Instead of increasing the size of the biggest clique it is also possible to use the fact that
the expression in Tur\'{a}n's graph theorem is monotonically increasing in the size of the biggest clique (Lemma @{thm [source] turan_mono}).
Hence, it suffices to prove the upper bound for the actual biggest clique size in the graph.
Afterwards, the monotonicity provides the desired inequality.

The simplifications in the proof are annotated accordingly.\<close>

theorem turan' :
  fixes p n :: nat
  assumes "finite (uverts G)"
    and "uwellformed G" and "\<forall>C p'. uclique C G p' \<longrightarrow> p' < p" and "p \<ge> 2" and "card(uverts G) = n"
  shows "card (uedges G) \<le> (1 - 1 / (p-1)) * n^2 / 2" using assms
proof (induction n arbitrary: p G rule: less_induct)
  txt \<open>In the simplified proof we also need to generalize over the biggest clique size @{term p}
       so that we can leverage the induction hypothesis in the proof
       for the already pre-existing biggest clique size which might be smaller than @{term "p-1"}.\<close>
  case (less n)
  then show ?case
  proof (cases "n < p")
    case True
    show ?thesis
    proof (cases "n")
      case 0
      with less True show ?thesis
        by (auto simp add: wellformed_uverts_0)
    next
      case (Suc n')
      with True have "(1 - 1 / real n) \<le> (1 - 1 / real (p - 1))"
        by (metis diff_Suc_1 diff_left_mono inverse_of_nat_le less_Suc_eq_le linorder_not_less list_decode.cases not_add_less1 plus_1_eq_Suc)
      moreover have "real (card (uedges G)) \<le> (1 - 1 / real n) * real (n\<^sup>2) / 2"
        using ugraph_max_edges [OF less(3,6,2)]
        by (smt (verit, ccfv_SIG) left_diff_distrib mult.right_neutral mult_of_nat_commute nonzero_mult_div_cancel_left of_nat_1 of_nat_mult power2_eq_square times_divide_eq_left)
      ultimately show ?thesis
        using Rings.ordered_semiring_class.mult_right_mono divide_less_eq_numeral1(1) le_less_trans linorder_not_less of_nat_0_le_iff
        by (smt (verit, ccfv_threshold) divide_nonneg_nonneg times_divide_eq_right)
    qed
  next
    case False
    show ?thesis
    proof -
      from False \<open>p \<ge> 2\<close>
      obtain C q where C: "uclique C G q"
        and C_max: "(\<forall>C q'. uclique C G q' \<longrightarrow> q' \<le> q)"
        and q1: "q < card (uverts G)" and q2: "0 < q"
        and pq: "q < p"
        using clique_exists_gt0 [OF \<open>finite (uverts G)\<close>] clique_exists1 less.prems(1,3,5)
        by (metis card.empty card_gt_0_iff le_eq_less_or_eq order_less_le_trans pos2)
      txt \<open>In the unsimplified proof we extend this existing greatest clique C to a clique of size @{term "p-1"}.
           This part is made superfluous in the simplified proof.
           In particular, also Section \ref{sec:extend_clique} is unneeded for this simplified proof.
           From here on the proof is analogous to the unsimplified proof
           with the potentially smaller clique of size @{term q} in place of the extended clique.\<close>
      have "card {e \<in> uedges G. e \<subseteq> uverts C} = q * (q-1) / 2"
        using clique_edges_inside [OF less(3,2) _ _ C] q1 less(6)
        by auto
      moreover have "card {e \<in> uedges G. e \<subseteq> uverts G - uverts C} \<le> (1 - 1 / q) * (n - q) ^ 2 / 2"
      proof -
        have "real (card {e \<in> uedges G. e \<subseteq> uverts G - uverts C})
              \<le> (1 - 1 / (real (q + 1) - 1)) * (real n - real (q + 1) + 1)\<^sup>2 / 2"
          using clique_edges_outside [OF less(3,2) _ _ , of "q+1" n C] C C_max q1 q2 linorder_class.leI [OF False] less(1,6)
          by (smt (verit, ccfv_threshold) Suc_1 Suc_eq_plus1 Suc_leI diff_add_inverse2 zero_less_diff)
        then show ?thesis
          using  less.prems(5) q1
          by (simp add: of_nat_diff)
      qed
      moreover have "card {e \<in> uedges G. e \<inter> uverts C \<noteq> {} \<and> e \<inter> (uverts G - uverts C) \<noteq> {}} \<le> (q - 1) * (n - q)"
        using clique_edges_inside_to_outside [OF less(3,2) q2 _ less(6) C C_max] q1
        by simp
      ultimately have "real (card (uedges G)) \<le> (1 - 1 / real q) * real (n\<^sup>2) / 2"
        using graph_partition_edges_card [OF less(2,3), of "uverts C"]
        using C uclique_def subgraph_def q1 q2 less.prems(5) turan_sum_eq [of "Suc q" n]
        by (smt (verit) Nat.add_diff_assoc Suc_1 Suc_le_eq Suc_le_mono add.commute add.right_neutral diff_Suc_1 diff_Suc_Suc of_nat_add of_nat_mono plus_1_eq_Suc)
      then show ?thesis
        txt \<open>The final statement can then easily be derived with the monotonicity (Lemma @{thm [source] turan_mono}).\<close>
        using turan_mono [OF q2 pq, of n] False
        by linarith
    qed
  qed
qed

end
