theory Foldes_Hammer
  imports "Undirected_Graph_Theory.Undirected_Graphs_Root"
begin

context fin_sgraph
begin

definition is_clique :: "'a set \<Rightarrow> bool" where
  "is_clique C \<longleftrightarrow> C \<subseteq> V \<and> induced_edges C = all_edges C"

definition cliques :: "'a set set" where
  "cliques = {C. is_clique C}"

definition maximum_clique :: "'a set \<Rightarrow> bool" where
  "maximum_clique K \<longleftrightarrow> K \<in> cliques \<and> (\<forall>C\<in>cliques. card C \<le> card K)"

definition outside_edge_count :: "'a set \<Rightarrow> nat" where
  "outside_edge_count K = card (induced_edges (V - K))"

definition is_split_partition :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_split_partition C I \<longleftrightarrow> C \<inter> I = {} \<and> C \<union> I = V \<and> is_clique C \<and> is_independent_set I"

definition is_split_graph :: bool where
  "is_split_graph \<longleftrightarrow> (\<exists>C I. is_split_partition C I)"

definition induces_2K2 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "induces_2K2 a b c d \<longleftrightarrow>
     distinct [a, b, c, d] \<and>
     vert_adj a b \<and> vert_adj c d \<and>
     \<not> vert_adj a c \<and> \<not> vert_adj a d \<and> \<not> vert_adj b c \<and> \<not> vert_adj b d"

definition induces_C4 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "induces_C4 a b c d \<longleftrightarrow>
     distinct [a, b, c, d] \<and>
     vert_adj a b \<and> vert_adj b c \<and> vert_adj c d \<and> vert_adj d a \<and>
     \<not> vert_adj a c \<and> \<not> vert_adj b d"

definition induces_C5 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "induces_C5 a b c d e \<longleftrightarrow>
     distinct [a, b, c, d, e] \<and>
     vert_adj a b \<and> vert_adj b c \<and> vert_adj c d \<and> vert_adj d e \<and> vert_adj e a \<and>
     \<not> vert_adj a c \<and> \<not> vert_adj a d \<and> \<not> vert_adj b d \<and> \<not> vert_adj b e \<and> \<not> vert_adj c e"

definition has_induced_2K2 :: bool where
  "has_induced_2K2 \<longleftrightarrow> (\<exists>a b c d. induces_2K2 a b c d)"

definition has_induced_C4 :: bool where
  "has_induced_C4 \<longleftrightarrow> (\<exists>a b c d. induces_C4 a b c d)"

definition has_induced_C5 :: bool where
  "has_induced_C5 \<longleftrightarrow> (\<exists>a b c d e. induces_C5 a b c d e)"

definition foldes_hammer_free :: bool where
  "foldes_hammer_free \<longleftrightarrow> \<not> has_induced_2K2 \<and> \<not> has_induced_C4 \<and> \<not> has_induced_C5"

lemma is_clique_alt:
  "is_clique C \<longleftrightarrow> C \<subseteq> V \<and> (\<forall>u\<in>C. \<forall>v\<in>C. u \<noteq> v \<longrightarrow> vert_adj u v)"
proof
  assume H: "is_clique C"
  then have "C \<subseteq> V" by (simp add: is_clique_def)
  moreover have "\<forall>u\<in>C. \<forall>v\<in>C. u \<noteq> v \<longrightarrow> vert_adj u v"
  proof (intro ballI impI)
    fix u v
    assume uC: "u \<in> C" and vC: "v \<in> C" and uv: "u \<noteq> v"
    from H have eq: "induced_edges C = all_edges C"
      by (simp add: is_clique_def)
    have "{u, v} \<in> all_edges C"
      using uC vC uv by (auto simp: all_edges_alt)
    with eq have "{u, v} \<in> induced_edges C" by simp
    then show "vert_adj u v"
      by (auto simp: induced_edges_def vert_adj_def)
  qed
  ultimately show "C \<subseteq> V \<and> (\<forall>u\<in>C. \<forall>v\<in>C. u \<noteq> v \<longrightarrow> vert_adj u v)"
    by simp
next
  assume H: "C \<subseteq> V \<and> (\<forall>u\<in>C. \<forall>v\<in>C. u \<noteq> v \<longrightarrow> vert_adj u v)"
  then have Csub: "C \<subseteq> V"
    and adj: "\<forall>u\<in>C. \<forall>v\<in>C. u \<noteq> v \<longrightarrow> vert_adj u v"
    by auto
  have "induced_edges C = all_edges C"
  proof (rule subset_antisym)
    show "induced_edges C \<subseteq> all_edges C"
      using induced_edges_alt by auto
  next
    show "all_edges C \<subseteq> induced_edges C"
    proof
      fix e
      assume eC: "e \<in> all_edges C"
      then obtain u v where e: "e = {u, v}" and uC: "u \<in> C" and vC: "v \<in> C" and uv: "u \<noteq> v"
        by (auto simp: all_edges_alt)
      from adj uC vC uv have "vert_adj u v" by blast
      then have "e \<in> E"
        by (simp add: e vert_adj_def)
      moreover from eC have "e \<subseteq> C"
        by (auto simp: all_edges_def)
      ultimately show "e \<in> induced_edges C"
        by (simp add: induced_edges_def)
    qed
  qed
  with Csub show "is_clique C"
    by (simp add: is_clique_def)
qed

lemma clique_pair_adj:
  assumes "is_clique C" "u \<in> C" "v \<in> C" "u \<noteq> v"
  shows "vert_adj u v"
  using assms by (auto simp: is_clique_alt)

lemma clique_mono:
  assumes "is_clique C" "D \<subseteq> C"
  shows "is_clique D"
  using assms by (auto simp: is_clique_alt)

lemma vert_adj_neq:
  assumes "vert_adj u v"
  shows "u \<noteq> v"
proof
  assume uv_eq: "u = v"
  from assms have card2: "card {u, v} = 2"
    unfolding vert_adj_def using two_edges by blast
  from uv_eq have "card {u, v} = 1"
    by simp
  with card2 show False
    by simp
qed

lemma empty_clique: "is_clique {}"
  by (simp add: is_clique_alt)

lemma singleton_clique:
  assumes "v \<in> V"
  shows "is_clique {v}"
  using assms by (auto simp: is_clique_alt)

lemma finite_cliques: "finite cliques"
proof -
  have "cliques \<subseteq> Pow V"
    by (auto simp: cliques_def is_clique_def)
  moreover have "finite (Pow V)"
    using finV by simp
  ultimately show ?thesis
    by (rule finite_subset)
qed

lemma cliques_nonempty: "{} \<in> cliques"
  by (simp add: cliques_def empty_clique)

lemma maximum_clique_exists:
  obtains K where "maximum_clique K"
proof -
  have fin: "finite (card ` cliques)"
    using finite_cliques by simp
  have ne: "card ` cliques \<noteq> {}"
    using cliques_nonempty by auto
  let ?m = "Max (card ` cliques)"
  have m_in: "?m \<in> card ` cliques"
    using Max_in[OF fin ne] .
  then obtain K where K_in: "K \<in> cliques" and K_card: "card K = ?m"
    by auto
  have maxK: "\<forall>C\<in>cliques. card C \<le> card K"
  proof
    fix C
    assume C_in: "C \<in> cliques"
    then have "card C \<in> card ` cliques"
      by auto
    then have "card C \<le> ?m"
      using Max_ge[OF fin] by blast
    then show "card C \<le> card K"
      by (simp add: K_card)
  qed
  have "maximum_clique K"
    using K_in maxK by (simp add: maximum_clique_def)
  then show ?thesis
    using that by blast
qed

lemma maximum_clique_finite:
  assumes "maximum_clique K"
  shows "finite K"
  using assms finV finite_subset
  by (auto simp: maximum_clique_def cliques_def is_clique_def)

lemma finite_induced_edges_subset_V:
  assumes "S \<subseteq> V"
  shows "finite (induced_edges S)"
proof -
  have finS: "finite S"
    using assms finV finite_subset by blast
  have "induced_edges S \<subseteq> Pow S"
    by (auto simp: induced_edges_def)
  moreover have "finite (Pow S)"
    using finS by simp
  ultimately show ?thesis
    by (rule finite_subset)
qed

lemma obtain_best_clique:
  obtains K where "maximum_clique K"
    and "\<forall>L. maximum_clique L \<longrightarrow> outside_edge_count K \<le> outside_edge_count L"
proof -
  let ?M = "{K. maximum_clique K}"
  have finM: "finite ?M"
  proof (rule finite_subset[of ?M cliques])
    show "?M \<subseteq> cliques"
      by (auto simp: maximum_clique_def)
    show "finite cliques"
      using finite_cliques .
  qed
  have neM: "?M \<noteq> {}"
    using maximum_clique_exists by blast
  have finImg: "finite (outside_edge_count ` ?M)"
    using finM by simp
  have neImg: "outside_edge_count ` ?M \<noteq> {}"
    using neM by auto
  let ?m = "Min (outside_edge_count ` ?M)"
  have mIn: "?m \<in> outside_edge_count ` ?M"
    using Min_in[OF finImg neImg] .
  then obtain K where Kmax: "maximum_clique K" and Kmin: "outside_edge_count K = ?m"
    by auto
  have Kbest: "\<forall>L. maximum_clique L \<longrightarrow> outside_edge_count K \<le> outside_edge_count L"
    using Kmin finImg neImg
    by (simp add: Min_le)
  show ?thesis
    using that Kmax Kbest by blast
qed

lemma insert_clique_if_all_adj:
  assumes C: "is_clique C"
    and vV: "v \<in> V"
    and vnot: "v \<notin> C"
    and adj: "\<forall>u\<in>C. vert_adj u v"
  shows "is_clique (insert v C)"
proof -
  from C have Csub: "C \<subseteq> V"
    and Cadj: "\<forall>u\<in>C. \<forall>w\<in>C. u \<noteq> w \<longrightarrow> vert_adj u w"
    by (auto simp: is_clique_alt)
  have "insert v C \<subseteq> V"
    using Csub vV by auto
  moreover have "\<forall>u\<in>insert v C. \<forall>w\<in>insert v C. u \<noteq> w \<longrightarrow> vert_adj u w"
  proof (intro ballI impI)
    fix u w
    assume uin: "u \<in> insert v C" and win: "w \<in> insert v C" and uw: "u \<noteq> w"
    show "vert_adj u w"
    proof (cases "u = v")
      case u_eq_v: True
      with win vnot uw have "w \<in> C" by auto
      then have "vert_adj w v"
        using adj by simp
      then show ?thesis
        using u_eq_v by (simp add: vert_adj_sym)
    next
      case u_ne_v: False
      show ?thesis
      proof (cases "w = v")
        case w_eq_v: True
        with uin vnot uw u_ne_v have "u \<in> C" by auto
        then have "vert_adj u v"
          using adj by simp
        then show ?thesis
          using w_eq_v by simp
      next
        case w_ne_v: False
        from uin win u_ne_v w_ne_v have "u \<in> C" "w \<in> C" by auto
        with Cadj uw show ?thesis by blast
      qed
    qed
  qed
  ultimately show ?thesis
    by (simp add: is_clique_alt)
qed

lemma maximum_clique_outside_has_nonneighbor:
  assumes maxK: "maximum_clique K"
    and vV: "v \<in> V"
    and vnot: "v \<notin> K"
  shows "\<exists>u\<in>K. \<not> vert_adj u v"
proof (rule ccontr)
  assume neg: "\<not> (\<exists>u\<in>K. \<not> vert_adj u v)"
  then have all_adj: "\<forall>u\<in>K. vert_adj u v"
    by auto
  from maxK have K_clique: "is_clique K"
    by (auto simp: maximum_clique_def cliques_def)
  have ins_clique: "is_clique (insert v K)"
    using insert_clique_if_all_adj[OF K_clique vV vnot all_adj] .
  then have ins_in: "insert v K \<in> cliques"
    by (simp add: cliques_def)
  from maxK have bound: "\<forall>C\<in>cliques. card C \<le> card K"
    by (auto simp: maximum_clique_def)
  from maxK have Ksub: "K \<subseteq> V"
    by (auto simp: maximum_clique_def cliques_def is_clique_def)
  then have finK: "finite K"
    using finV finite_subset by blast
  from ins_in bound have "card (insert v K) \<le> card K"
    by blast
  with finK vnot show False
    by simp
qed

lemma split_graph_alt:
  "is_split_graph \<longleftrightarrow> (\<exists>C. is_clique C \<and> is_independent_set (V - C))"
proof
  assume H: "is_split_graph"
  then obtain C I where sp: "is_split_partition C I"
    by (auto simp: is_split_graph_def)
  then have "I = V - C"
    by (auto simp: is_split_partition_def is_clique_def)
  with sp show "\<exists>C. is_clique C \<and> is_independent_set (V - C)"
    by (auto simp: is_split_partition_def)
next
  assume H: "\<exists>C. is_clique C \<and> is_independent_set (V - C)"
  then obtain C where C: "is_clique C" "is_independent_set (V - C)"
    by blast
  have "is_split_partition C (V - C)"
    using C by (auto simp: is_split_partition_def is_clique_def)
  then show "is_split_graph"
    by (auto simp: is_split_graph_def)
qed

lemma independent_pair_not_adj:
  assumes "is_independent_set I" "u \<in> I" "v \<in> I"
  shows "\<not> vert_adj u v"
  using assms by (auto simp: is_independent_alt)

lemma split_partition_edge_hits_clique:
  assumes sp: "is_split_partition C I"
    and uv: "vert_adj u v"
  shows "u \<in> C \<or> v \<in> C"
proof (rule ccontr)
  assume notC: "\<not> (u \<in> C \<or> v \<in> C)"
  from uv have uV: "u \<in> V" and vV: "v \<in> V"
    using vert_adj_imp_inV by auto
  from sp uV vV notC have uI: "u \<in> I" and vI: "v \<in> I"
    by (auto simp: is_split_partition_def)
  from sp have indep: "is_independent_set I"
    by (simp add: is_split_partition_def)
  from independent_pair_not_adj[OF indep uI vI] uv show False
    by contradiction
qed

lemma split_partition_nonedge_not_both_clique:
  assumes sp: "is_split_partition C I"
    and uV: "u \<in> V"
    and vV: "v \<in> V"
    and uv: "u \<noteq> v"
    and not_adj: "\<not> vert_adj u v"
  shows "\<not> (u \<in> C \<and> v \<in> C)"
proof
  assume uvC: "u \<in> C \<and> v \<in> C"
  then have uC: "u \<in> C" and vC: "v \<in> C"
    by auto
  from sp have clique: "is_clique C"
    by (simp add: is_split_partition_def)
  from clique_pair_adj[OF clique uC vC uv] not_adj show False
    by contradiction
qed

lemma induces_2K2_inV:
  assumes "induces_2K2 a b c d"
  shows "a \<in> V" "b \<in> V" "c \<in> V" "d \<in> V"
  using assms vert_adj_imp_inV by (auto simp: induces_2K2_def)

lemma induces_C4_inV:
  assumes "induces_C4 a b c d"
  shows "a \<in> V" "b \<in> V" "c \<in> V" "d \<in> V"
  using assms vert_adj_imp_inV by (auto simp: induces_C4_def)

lemma induces_C5_inV:
  assumes "induces_C5 a b c d e"
  shows "a \<in> V" "b \<in> V" "c \<in> V" "d \<in> V" "e \<in> V"
  using assms vert_adj_imp_inV by (auto simp: induces_C5_def)

lemma split_partition_forbids_2K2:
  assumes sp: "is_split_partition C I"
    and H: "induces_2K2 a b c d"
  shows False
proof -
  from H have ab: "vert_adj a b" and cd: "vert_adj c d"
    and aV: "a \<in> V" and bV: "b \<in> V" and cV: "c \<in> V" and dV: "d \<in> V"
    and ac: "a \<noteq> c" and ad: "a \<noteq> d" and bc: "b \<noteq> c" and bd: "b \<noteq> d"
    and nac: "\<not> vert_adj a c" and nad: "\<not> vert_adj a d" and nbc: "\<not> vert_adj b c" and nbd: "\<not> vert_adj b d"
    using induces_2K2_inV[OF H] by (auto simp: induces_2K2_def)
  have "a \<in> C \<or> b \<in> C"
    using split_partition_edge_hits_clique[OF sp ab] .
  moreover have "c \<in> C \<or> d \<in> C"
    using split_partition_edge_hits_clique[OF sp cd] .
  moreover have "\<not> (a \<in> C \<and> c \<in> C)"
    using split_partition_nonedge_not_both_clique[OF sp aV cV ac nac] .
  moreover have "\<not> (a \<in> C \<and> d \<in> C)"
    using split_partition_nonedge_not_both_clique[OF sp aV dV ad nad] .
  moreover have "\<not> (b \<in> C \<and> c \<in> C)"
    using split_partition_nonedge_not_both_clique[OF sp bV cV bc nbc] .
  moreover have "\<not> (b \<in> C \<and> d \<in> C)"
    using split_partition_nonedge_not_both_clique[OF sp bV dV bd nbd] .
  ultimately show False
    by blast
qed

lemma split_partition_forbids_C4:
  assumes sp: "is_split_partition C I"
    and H: "induces_C4 a b c d"
  shows False
proof -
  from H have ab: "vert_adj a b" and bc: "vert_adj b c" and cd: "vert_adj c d" and da: "vert_adj d a"
    and aV: "a \<in> V" and bV: "b \<in> V" and cV: "c \<in> V" and dV: "d \<in> V"
    and ac: "a \<noteq> c" and bd: "b \<noteq> d"
    and nac: "\<not> vert_adj a c" and nbd: "\<not> vert_adj b d"
    using induces_C4_inV[OF H] by (auto simp: induces_C4_def)
  have "a \<in> C \<or> b \<in> C"
    using split_partition_edge_hits_clique[OF sp ab] .
  moreover have "b \<in> C \<or> c \<in> C"
    using split_partition_edge_hits_clique[OF sp bc] .
  moreover have "c \<in> C \<or> d \<in> C"
    using split_partition_edge_hits_clique[OF sp cd] .
  moreover have "d \<in> C \<or> a \<in> C"
    using split_partition_edge_hits_clique[OF sp da] .
  moreover have "\<not> (a \<in> C \<and> c \<in> C)"
    using split_partition_nonedge_not_both_clique[OF sp aV cV ac nac] .
  moreover have "\<not> (b \<in> C \<and> d \<in> C)"
    using split_partition_nonedge_not_both_clique[OF sp bV dV bd nbd] .
  ultimately show False
    by blast
qed

lemma split_partition_forbids_C5:
  assumes sp: "is_split_partition C I"
    and H: "induces_C5 a b c d e"
  shows False
proof -
  from H have ab: "vert_adj a b" and bc: "vert_adj b c" and cd: "vert_adj c d" and de: "vert_adj d e" and ea: "vert_adj e a"
    and aV: "a \<in> V" and bV: "b \<in> V" and cV: "c \<in> V" and dV: "d \<in> V" and eV: "e \<in> V"
    and ac: "a \<noteq> c" and ad: "a \<noteq> d" and bd: "b \<noteq> d" and be: "b \<noteq> e" and ce: "c \<noteq> e"
    and nac: "\<not> vert_adj a c" and nad: "\<not> vert_adj a d" and nbd: "\<not> vert_adj b d" and nbe: "\<not> vert_adj b e" and nce: "\<not> vert_adj c e"
    using induces_C5_inV[OF H] by (auto simp: induces_C5_def)
  have "a \<in> C \<or> b \<in> C"
    using split_partition_edge_hits_clique[OF sp ab] .
  moreover have "b \<in> C \<or> c \<in> C"
    using split_partition_edge_hits_clique[OF sp bc] .
  moreover have "c \<in> C \<or> d \<in> C"
    using split_partition_edge_hits_clique[OF sp cd] .
  moreover have "d \<in> C \<or> e \<in> C"
    using split_partition_edge_hits_clique[OF sp de] .
  moreover have "e \<in> C \<or> a \<in> C"
    using split_partition_edge_hits_clique[OF sp ea] .
  moreover have "\<not> (a \<in> C \<and> c \<in> C)"
    using split_partition_nonedge_not_both_clique[OF sp aV cV ac nac] .
  moreover have "\<not> (a \<in> C \<and> d \<in> C)"
    using split_partition_nonedge_not_both_clique[OF sp aV dV ad nad] .
  moreover have "\<not> (b \<in> C \<and> d \<in> C)"
    using split_partition_nonedge_not_both_clique[OF sp bV dV bd nbd] .
  moreover have "\<not> (b \<in> C \<and> e \<in> C)"
    using split_partition_nonedge_not_both_clique[OF sp bV eV be nbe] .
  moreover have "\<not> (c \<in> C \<and> e \<in> C)"
    using split_partition_nonedge_not_both_clique[OF sp cV eV ce nce] .
  ultimately show False
    by blast
qed

lemma split_graph_imp_foldes_hammer_free:
  assumes "is_split_graph"
  shows "foldes_hammer_free"
proof -
  obtain C I where sp: "is_split_partition C I"
    using assms by (auto simp: is_split_graph_def)
  have "\<not> has_induced_2K2"
    using sp split_partition_forbids_2K2 by (auto simp: has_induced_2K2_def)
  moreover have "\<not> has_induced_C4"
    using sp split_partition_forbids_C4 by (auto simp: has_induced_C4_def)
  moreover have "\<not> has_induced_C5"
    using sp split_partition_forbids_C5 by (auto simp: has_induced_C5_def)
  ultimately show ?thesis
    by (simp add: foldes_hammer_free_def)
qed

lemma outside_adjacent_nonneighbor_sets_nested:
  assumes fh: "foldes_hammer_free"
    and Kmax: "maximum_clique K"
    and uO: "u \<in> V - K"
    and vO: "v \<in> V - K"
    and uv: "vert_adj u v"
  shows "{x\<in>K. \<not> vert_adj x u} \<subseteq> {x\<in>K. \<not> vert_adj x v} \<or>
         {x\<in>K. \<not> vert_adj x v} \<subseteq> {x\<in>K. \<not> vert_adj x u}"
proof (rule ccontr)
  let ?A = "{x\<in>K. \<not> vert_adj x u}"
  let ?B = "{x\<in>K. \<not> vert_adj x v}"
  assume not_nested: "\<not> (?A \<subseteq> ?B \<or> ?B \<subseteq> ?A)"
  then obtain a b where aA: "a \<in> ?A" and aB: "a \<notin> ?B" and bB: "b \<in> ?B" and bA: "b \<notin> ?A"
    by blast
  have aK: "a \<in> K" and aNu: "\<not> vert_adj a u"
    using aA by auto
  have bK: "b \<in> K" and bNv: "\<not> vert_adj b v"
    using bB by auto
  have av: "vert_adj a v"
    using aB aK by auto
  have bu: "vert_adj b u"
    using bA bK by auto
  have ab_ne: "a \<noteq> b"
    using aA bA by auto
  have uv_ne: "u \<noteq> v"
    using vert_adj_neq[OF uv] .
  have Kclq: "is_clique K"
    using Kmax by (auto simp: maximum_clique_def cliques_def)
  have ab: "vert_adj a b"
    using clique_pair_adj[OF Kclq aK bK ab_ne] .
  have vu: "vert_adj v u"
    using uv by (simp add: vert_adj_sym)
  have ub: "vert_adj u b"
    using bu by (simp add: vert_adj_sym)
  have ba: "vert_adj b a"
    using ab by (simp add: vert_adj_sym)
  have vNb: "\<not> vert_adj v b"
    using bNv by (simp add: vert_adj_sym)
  have dist: "distinct [a, v, u, b]"
    using aK bK uO vO ab_ne uv_ne by auto
  have "induces_C4 a v u b"
    using dist av vu ub ba aNu vNb
    by (simp add: induces_C4_def)
  then have "has_induced_C4"
    by (auto simp: has_induced_C4_def)
  with fh show False
    by (simp add: foldes_hammer_free_def)
qed

lemma outside_adjacent_smaller_nonneighbor_set_singleton:
  assumes fh: "foldes_hammer_free"
    and Kmax: "maximum_clique K"
    and uO: "u \<in> V - K"
    and vO: "v \<in> V - K"
    and uv: "vert_adj u v"
    and AB: "{x\<in>K. \<not> vert_adj x u} \<subseteq> {x\<in>K. \<not> vert_adj x v}"
  obtains a where "{x\<in>K. \<not> vert_adj x u} = {a}" and "a \<in> K" and "\<not> vert_adj a u" and "\<not> vert_adj a v"
proof -
  have uV: "u \<in> V" and unotK: "u \<notin> K"
    using uO by auto
  obtain a where aK: "a \<in> K" and aNu: "\<not> vert_adj a u"
    using maximum_clique_outside_has_nonneighbor[OF Kmax uV unotK] by blast
  have aA: "a \<in> {x\<in>K. \<not> vert_adj x u}"
    using aK aNu by auto
  have aB: "a \<in> {x\<in>K. \<not> vert_adj x v}"
    using AB aA by blast
  have aNv: "\<not> vert_adj a v"
    using aB by auto
  have Aeq: "{x\<in>K. \<not> vert_adj x u} = {a}"
  proof (rule subset_antisym)
    show "{x\<in>K. \<not> vert_adj x u} \<subseteq> {a}"
    proof
      fix b
      assume bA: "b \<in> {x\<in>K. \<not> vert_adj x u}"
      show "b \<in> {a}"
      proof (rule ccontr)
        assume bneq: "b \<notin> {a}"
        then have ab_ne: "a \<noteq> b"
          by auto
        have bK: "b \<in> K" and bNu: "\<not> vert_adj b u"
          using bA by auto
        have bB: "b \<in> {x\<in>K. \<not> vert_adj x v}"
          using AB bA by blast
        have bNv: "\<not> vert_adj b v"
          using bB by auto
        have uv_ne: "u \<noteq> v"
          using vert_adj_neq[OF uv] .
        have Kclq: "is_clique K"
          using Kmax by (auto simp: maximum_clique_def cliques_def)
        have ab: "vert_adj a b"
          using clique_pair_adj[OF Kclq aK bK ab_ne] .
        have dist: "distinct [a, b, u, v]"
          using aK bK uO vO ab_ne uv_ne by auto
        have "induces_2K2 a b u v"
          using dist ab uv aNu aNv bNu bNv
          by (simp add: induces_2K2_def)
        then have "has_induced_2K2"
          by (auto simp: has_induced_2K2_def)
        with fh show False
          by (simp add: foldes_hammer_free_def)
      qed
    qed
  next
    show "{a} \<subseteq> {x\<in>K. \<not> vert_adj x u}"
      using aK aNu by auto
  qed
  show thesis
    using that Aeq aK aNu aNv by blast
qed

lemma orient_outside_edge_for_swap:
  assumes fh: "foldes_hammer_free"
    and Kmax: "maximum_clique K"
    and uO: "u \<in> V - K"
    and vO: "v \<in> V - K"
    and uv: "vert_adj u v"
  obtains u' v' a where
      "{u', v'} = {u, v}"
    and "u' \<in> V - K"
    and "v' \<in> V - K"
    and "vert_adj u' v'"
    and "{x\<in>K. \<not> vert_adj x u'} = {a}"
    and "a \<in> K"
    and "\<not> vert_adj a u'"
    and "\<not> vert_adj a v'"
proof -
  have nested:
    "{x\<in>K. \<not> vert_adj x u} \<subseteq> {x\<in>K. \<not> vert_adj x v} \<or>
     {x\<in>K. \<not> vert_adj x v} \<subseteq> {x\<in>K. \<not> vert_adj x u}"
    using outside_adjacent_nonneighbor_sets_nested[OF fh Kmax uO vO uv] .
  then show thesis
  proof
    assume AB: "{x\<in>K. \<not> vert_adj x u} \<subseteq> {x\<in>K. \<not> vert_adj x v}"
    obtain a where Aeq: "{x\<in>K. \<not> vert_adj x u} = {a}" and aK: "a \<in> K"
      and aNu: "\<not> vert_adj a u" and aNv: "\<not> vert_adj a v"
      using outside_adjacent_smaller_nonneighbor_set_singleton[OF fh Kmax uO vO uv AB] by blast
    show thesis
      using that[of u v a] uO vO uv Aeq aK aNu aNv by simp
  next
    assume BA: "{x\<in>K. \<not> vert_adj x v} \<subseteq> {x\<in>K. \<not> vert_adj x u}"
    have vu: "vert_adj v u"
      using uv by (simp add: vert_adj_sym)
    obtain a where Beq: "{x\<in>K. \<not> vert_adj x v} = {a}" and aK: "a \<in> K"
      and aNv: "\<not> vert_adj a v" and aNu: "\<not> vert_adj a u"
      using outside_adjacent_smaller_nonneighbor_set_singleton[OF fh Kmax vO uO vu BA] by blast
    show thesis
      using that[of v u a] vO uO vu Beq aK aNv aNu by auto
  qed
qed

lemma replace_unique_nonneighbor_maximum_clique:
  assumes Kmax: "maximum_clique K"
    and uO: "u \<in> V - K"
    and Au: "{x\<in>K. \<not> vert_adj x u} = {a}"
  shows "maximum_clique (insert u (K - {a}))"
proof -
  have Kclq: "is_clique K"
    using Kmax by (auto simp: maximum_clique_def cliques_def)
  have aK: "a \<in> K" and aNu: "\<not> vert_adj a u"
    using Au by auto
  have uV: "u \<in> V" and unotK: "u \<notin> K"
    using uO by auto
  have Ksub: "K - {a} \<subseteq> K"
    by auto
  have Kminclq: "is_clique (K - {a})"
    using clique_mono[OF Kclq Ksub] .
  have uadj: "\<forall>x\<in>K - {a}. vert_adj x u"
  proof
    fix x
    assume xK: "x \<in> K - {a}"
    have xK0: "x \<in> K" and xnea: "x \<noteq> a"
      using xK by auto
    have "x \<notin> {x\<in>K. \<not> vert_adj x u}"
      using Au xnea by auto
    then show "vert_adj x u"
      using xK0 by auto
  qed
  have newclq: "is_clique (insert u (K - {a}))"
    using insert_clique_if_all_adj[OF Kminclq uV] unotK uadj by auto
  have finK: "finite K"
    using maximum_clique_finite[OF Kmax] .
  have newcard: "card (insert u (K - {a})) = card K"
  proof -
    have u_not_Ka: "u \<notin> K - {a}"
      using unotK by auto
    have "card (insert u (K - {a})) = Suc (card (K - {a}))"
      using finK u_not_Ka by simp
    also have "... = Suc (card K - 1)"
      using finK aK by simp
    also have "... = card K"
    proof -
      have "K \<noteq> {}"
        using aK by auto
      have "0 < card K"
        using finK \<open>K \<noteq> {}\<close> by (simp add: card_gt_0_iff)
      then show ?thesis
        by arith
    qed
    finally show ?thesis .
  qed
  have newin: "insert u (K - {a}) \<in> cliques"
    using newclq by (simp add: cliques_def)
  have newbound: "\<forall>C\<in>cliques. card C \<le> card (insert u (K - {a}))"
  proof
    fix C
    assume Cin: "C \<in> cliques"
    from Kmax have "\<forall>C\<in>cliques. card C \<le> card K"
      by (simp add: maximum_clique_def)
    then show "card C \<le> card (insert u (K - {a}))"
      using Cin newcard by simp
  qed
  show ?thesis
    using newin newbound by (simp add: maximum_clique_def)
qed

lemma replacement_edge_transfer:
  assumes fh: "foldes_hammer_free"
    and Kmax: "maximum_clique K"
    and uO: "u \<in> V - K"
    and vO: "v \<in> V - K"
    and uv: "vert_adj u v"
    and Au: "{x\<in>K. \<not> vert_adj x u} = {a}"
    and aNv: "\<not> vert_adj a v"
    and zO: "z \<in> V - K"
    and zne: "z \<noteq> u"
    and az: "vert_adj a z"
  shows "vert_adj u z"
proof (rule ccontr)
  assume uz: "\<not> vert_adj u z"
  have aK: "a \<in> K" and aNu: "\<not> vert_adj a u"
    using Au by auto
  have uv_ne: "u \<noteq> v"
    using vert_adj_neq[OF uv] .
  have vz: "vert_adj v z"
  proof (rule ccontr)
    assume vz_not: "\<not> vert_adj v z"
    have zv_ne: "z \<noteq> v"
      using az aNv by auto
    have dist: "distinct [a, z, u, v]"
      using aK uO vO zO uv_ne zne az zv_ne by auto
    have zNu: "\<not> vert_adj z u"
      using uz by (simp add: vert_adj_sym)
    have zNv: "\<not> vert_adj z v"
      using vz_not by (simp add: vert_adj_sym)
    have "induces_2K2 a z u v"
      using dist az uv aNu aNv zNu zNv
      by (simp add: induces_2K2_def)
    then have "has_induced_2K2"
      by (auto simp: has_induced_2K2_def)
    with fh show False
      by (simp add: foldes_hammer_free_def)
  qed
  have zv: "vert_adj z v"
    using vz by (simp add: vert_adj_sym)
  have nested:
    "{x\<in>K. \<not> vert_adj x z} \<subseteq> {x\<in>K. \<not> vert_adj x v} \<or>
     {x\<in>K. \<not> vert_adj x v} \<subseteq> {x\<in>K. \<not> vert_adj x z}"
    using outside_adjacent_nonneighbor_sets_nested[OF fh Kmax zO vO zv] .
  have zV: "z \<in> V" and znotK: "z \<notin> K"
    using zO by auto
  obtain c where cK: "c \<in> K" and cNz: "\<not> vert_adj c z"
    using maximum_clique_outside_has_nonneighbor[OF Kmax zV znotK] by blast
  have CsubB: "{x\<in>K. \<not> vert_adj x z} \<subseteq> {x\<in>K. \<not> vert_adj x v}"
  proof -
    from nested show ?thesis
    proof
      assume h: "{x\<in>K. \<not> vert_adj x z} \<subseteq> {x\<in>K. \<not> vert_adj x v}"
      show ?thesis by fact
    next
      assume h: "{x\<in>K. \<not> vert_adj x v} \<subseteq> {x\<in>K. \<not> vert_adj x z}"
      have "a \<in> {x\<in>K. \<not> vert_adj x z}"
        using h aK aNv by auto
      then have aNz: "\<not> vert_adj a z"
        by auto
      then have False
        using az by contradiction
      then show ?thesis
        by blast
    qed
  qed
  have cNv: "\<not> vert_adj c v"
    using CsubB cK cNz by auto
  have ca_ne: "c \<noteq> a"
    using az cK cNz by auto
  have cu: "vert_adj c u"
  proof -
    have "c \<notin> {x\<in>K. \<not> vert_adj x u}"
      using Au ca_ne by auto
    then show ?thesis
      using cK by auto
  qed
  have Kclq: "is_clique K"
    using Kmax by (auto simp: maximum_clique_def cliques_def)
  have ac: "vert_adj a c"
    using clique_pair_adj[OF Kclq aK cK ca_ne[symmetric]] .
  have zv: "vert_adj z v"
    using vz by (simp add: vert_adj_sym)
  have vu: "vert_adj v u"
    using uv by (simp add: vert_adj_sym)
  have uc: "vert_adj u c"
    using cu by (simp add: vert_adj_sym)
  have ca: "vert_adj c a"
    using ac by (simp add: vert_adj_sym)
  have zNu: "\<not> vert_adj z u"
    using uz by (simp add: vert_adj_sym)
  have zNc: "\<not> vert_adj z c"
    using cNz by (simp add: vert_adj_sym)
  have vNc: "\<not> vert_adj v c"
    using cNv by (simp add: vert_adj_sym)
  have dist: "distinct [a, z, v, u, c]"
    using aK cK uO vO zO uv_ne zne az ca_ne aNv by auto
  have "induces_C5 a z v u c"
    using dist az zv vu uc ca aNv aNu zNu zNc vNc
    by (simp add: induces_C5_def)
  then have "has_induced_C5"
    unfolding has_induced_C5_def by blast
  with fh show False
    by (simp add: foldes_hammer_free_def)
qed

lemma outside_set_after_swap:
  assumes uO: "u \<in> V - K"
    and aV: "a \<in> V"
    and aK: "a \<in> K"
  shows "V - insert u (K - {a}) = insert a ((V - K) - {u})"
  using assms by auto

lemma swap_outside_edges_inj:
  assumes uO: "u \<in> V - K"
    and aK: "a \<in> K"
  shows "inj_on (%e. if a \<in> e then insert u (e - {a}) else e)
      (induced_edges (V - insert u (K - {a})))"
proof (rule inj_onI)
  let ?I' = "V - insert u (K - {a})"
  let ?f = "%e. if a \<in> e then insert u (e - {a}) else e"
  fix e1 e2
  assume e1I: "e1 \<in> induced_edges ?I'"
    and e2I: "e2 \<in> induced_edges ?I'"
    and eq: "?f e1 = ?f e2"
  have u_not_I': "u \<notin> ?I'"
    using uO by auto
  have e1ss: "e1 \<subseteq> ?I'" and e2ss: "e2 \<subseteq> ?I'"
    using e1I e2I by (auto simp: induced_edges_def)
  show "e1 = e2"
  proof (cases "a \<in> e1")
    case False
    then have f1: "?f e1 = e1"
      by simp
    show ?thesis
    proof (cases "a \<in> e2")
      case False
      with eq f1 show ?thesis
        by simp
    next
      case True
      then have "u \<in> ?f e2"
        by simp
      then have "u \<in> e1"
        using eq f1 by simp
      with e1ss u_not_I' show ?thesis
        by blast
    qed
  next
    case e1_has_a: True
    show ?thesis
    proof (cases "a \<in> e2")
      case False
      then have f2: "?f e2 = e2"
        by simp
      have "u \<in> ?f e1"
        using e1_has_a by simp
      then have "u \<in> e2"
        using eq f2 by simp
      with e2ss u_not_I' show ?thesis
        by blast
    next
      case e2_has_a: True
      have u_not_e1: "u \<notin> e1 - {a}" and u_not_e2: "u \<notin> e2 - {a}"
        using e1ss e2ss u_not_I' by blast+
      have "insert u (e1 - {a}) = insert u (e2 - {a})"
        using eq e1_has_a e2_has_a by simp
      then have diff_eq: "e1 - {a} = e2 - {a}"
      proof -
        have "(insert u (e1 - {a})) - {u} = (insert u (e2 - {a})) - {u}"
          using \<open>insert u (e1 - {a}) = insert u (e2 - {a})\<close> by simp
        then show ?thesis
          using u_not_e1 u_not_e2 by auto
      qed
      have "e1 = insert a (e1 - {a})"
        using e1_has_a by blast
      moreover have "e2 = insert a (e2 - {a})"
        using e2_has_a by blast
      ultimately show ?thesis
        using diff_eq by simp
    qed
  qed
qed

lemma swap_outside_edges_image_subset:
  assumes fh: "foldes_hammer_free"
    and Kmax: "maximum_clique K"
    and uO: "u \<in> V - K"
    and vO: "v \<in> V - K"
    and uv: "vert_adj u v"
    and Au: "{x\<in>K. \<not> vert_adj x u} = {a}"
    and aNv: "\<not> vert_adj a v"
  shows "(%e. if a \<in> e then insert u (e - {a}) else e) `
      induced_edges (V - insert u (K - {a}))
      \<subseteq> induced_edges (V - K)"
proof
  let ?I = "V - K"
  let ?I' = "V - insert u (K - {a})"
  let ?f = "%e. if a \<in> e then insert u (e - {a}) else e"
  have aK: "a \<in> K"
    using Au by auto
  have aV: "a \<in> V"
    using Kmax aK by (auto simp: maximum_clique_def cliques_def is_clique_def)
  have Ieq: "?I' = insert a (?I - {u})"
    using outside_set_after_swap[OF uO aV aK] .
  fix x
  assume xin: "x \<in> ?f ` induced_edges ?I'"
  then obtain e where eI: "e \<in> induced_edges ?I'" and xeq: "x = ?f e"
    by blast
  have ess: "e \<subseteq> ?I'" and eE: "e \<in> E"
    using eI by (auto simp: induced_edges_def)
  show "x \<in> induced_edges ?I"
  proof (cases "a \<in> e")
    case False
    then have xeqe: "x = e"
      using xeq by simp
    have "e \<subseteq> ?I"
    proof
      fix y
      assume "y \<in> e"
      with ess False show "y \<in> ?I"
        by (auto simp: Ieq)
    qed
    with eE xeqe show ?thesis
      by (auto simp: induced_edges_def)
  next
    case True
    from eE have ecard: "card e = 2"
      using two_edges by auto
    from True ecard obtain z where e: "e = {a, z}" and zne: "z \<noteq> a"
      by (auto simp: card_2_iff)
    have zI: "z \<in> ?I - {u}"
      using ess True e zne by (auto simp: Ieq)
    then have zO: "z \<in> V - K" and zne_u: "z \<noteq> u"
      by auto
    have az: "vert_adj a z"
      using eE e by (simp add: vert_adj_def)
    have uz: "vert_adj u z"
      using replacement_edge_transfer[OF fh Kmax uO vO uv Au aNv zO zne_u az] .
    have xeqz: "x = {u, z}"
      using xeq True e zne by simp
    have uzE: "{u, z} \<in> E"
      using uz by (simp add: vert_adj_def)
    have uz_sub: "{u, z} \<subseteq> ?I"
      using uO zO by auto
    show ?thesis
      using xeqz uzE uz_sub by (auto simp: induced_edges_def)
  qed
qed

lemma swap_outside_edges_missing_uv:
  assumes uO: "u \<in> V - K"
    and vO: "v \<in> V - K"
    and uv: "vert_adj u v"
    and aK: "a \<in> K"
    and aNv: "\<not> vert_adj a v"
  shows "{u, v} \<in> induced_edges (V - K)"
    and "{u, v} \<notin> (%e. if a \<in> e then insert u (e - {a}) else e) `
      induced_edges (V - insert u (K - {a}))"
proof -
  have uv_in: "{u, v} \<in> induced_edges (V - K)"
    using uO vO uv by (auto simp: induced_edges_def vert_adj_def)
  show "{u, v} \<in> induced_edges (V - K)"
    using uv_in .
  show "{u, v} \<notin> (%e. if a \<in> e then insert u (e - {a}) else e) `
      induced_edges (V - insert u (K - {a}))"
  proof
    let ?I' = "V - insert u (K - {a})"
    let ?f = "%e. if a \<in> e then insert u (e - {a}) else e"
    assume img: "{u, v} \<in> ?f ` induced_edges ?I'"
    then obtain e where eI: "e \<in> induced_edges ?I'" and eq: "{u, v} = ?f e"
      by blast
    have u_not_I': "u \<notin> ?I'"
      using uO by auto
    have ess: "e \<subseteq> ?I'" and eE: "e \<in> E"
      using eI by (auto simp: induced_edges_def)
    have uv_ne: "u \<noteq> v"
      using vert_adj_neq[OF uv] .
    show False
    proof (cases "a \<in> e")
      case False
      then have "{u, v} = e"
        using eq by simp
      then have "u \<in> e"
        by auto
      with ess u_not_I' show False
        by blast
    next
      case True
      from eE have ecard: "card e = 2"
        using two_edges by auto
      from True ecard obtain z where e: "e = {a, z}" and zne: "z \<noteq> a"
        by (auto simp: card_2_iff)
      have zI': "z \<in> ?I'"
        using ess True e zne by auto
      then have zne_u: "z \<noteq> u"
        using u_not_I' by auto
      have "{u, v} = {u, z}"
        using eq True e zne by simp
      then have zeqv: "z = v"
        using uv_ne zne_u by auto
      have "vert_adj a z"
        using eE e by (simp add: vert_adj_def)
      with aNv zeqv show False
        by simp
    qed
  qed
qed

lemma outside_edge_count_swap_strict:
  assumes fh: "foldes_hammer_free"
    and Kmax: "maximum_clique K"
    and uO: "u \<in> V - K"
    and vO: "v \<in> V - K"
    and uv: "vert_adj u v"
    and Au: "{x\<in>K. \<not> vert_adj x u} = {a}"
    and aNv: "\<not> vert_adj a v"
  shows "outside_edge_count (insert u (K - {a})) < outside_edge_count K"
proof -
  let ?I = "V - K"
  let ?I' = "V - insert u (K - {a})"
  let ?f = "%e. if a \<in> e then insert u (e - {a}) else e"
  have aK: "a \<in> K"
    using Au by auto
  have inj: "inj_on ?f (induced_edges ?I')"
    using swap_outside_edges_inj[OF uO aK] .
  have imgsub: "?f ` induced_edges ?I' \<subseteq> induced_edges ?I"
    using swap_outside_edges_image_subset[OF fh Kmax uO vO uv Au aNv] .
  have uv_in: "{u, v} \<in> induced_edges ?I"
    using swap_outside_edges_missing_uv[OF uO vO uv aK aNv] by blast
  have uv_not_img: "{u, v} \<notin> ?f ` induced_edges ?I'"
    using swap_outside_edges_missing_uv[OF uO vO uv aK aNv] by blast
  have psub: "?f ` induced_edges ?I' \<subset> induced_edges ?I"
    using imgsub uv_in uv_not_img by blast
  have finI': "finite (induced_edges ?I')"
    by (rule finite_induced_edges_subset_V) auto
  have finI: "finite (induced_edges ?I)"
    by (rule finite_induced_edges_subset_V) auto
  have card_img: "card (?f ` induced_edges ?I') = card (induced_edges ?I')"
    by (rule card_image[OF inj])
  have "card (induced_edges ?I') = card (?f ` induced_edges ?I')"
    using card_img by simp
  also have "... < card (induced_edges ?I)"
    using finI psub by (rule psubset_card_mono)
  finally show ?thesis
    by (simp add: outside_edge_count_def)
qed

theorem foldes_hammer_converse:
  assumes fh: "foldes_hammer_free"
  shows "is_split_graph"
proof -
  obtain K where Kmax: "maximum_clique K"
    and Kbest: "\<forall>L. maximum_clique L \<longrightarrow> outside_edge_count K \<le> outside_edge_count L"
    using obtain_best_clique by blast
  have Kclq: "is_clique K"
    using Kmax by (auto simp: maximum_clique_def cliques_def)
  have indep: "is_independent_set (V - K)"
  proof (rule ccontr)
    assume not_indep: "\<not> is_independent_set (V - K)"
    then obtain u v where uO: "u \<in> V - K" and vO: "v \<in> V - K" and uv: "vert_adj u v"
      by (auto simp: is_independent_alt)
    obtain u' v' a where uvset: "{u', v'} = {u, v}"
      and u'O: "u' \<in> V - K" and v'O: "v' \<in> V - K" and uv': "vert_adj u' v'"
      and Au': "{x\<in>K. \<not> vert_adj x u'} = {a}"
      and aK: "a \<in> K" and aNu': "\<not> vert_adj a u'" and aNv': "\<not> vert_adj a v'"
      using orient_outside_edge_for_swap[OF fh Kmax uO vO uv] by blast
    let ?K' = "insert u' (K - {a})"
    have K'max: "maximum_clique ?K'"
      using replace_unique_nonneighbor_maximum_clique[OF Kmax u'O Au'] .
    have dec: "outside_edge_count ?K' < outside_edge_count K"
      using outside_edge_count_swap_strict[OF fh Kmax u'O v'O uv' Au' aNv'] .
    have "outside_edge_count K \<le> outside_edge_count ?K'"
      using Kbest K'max by blast
    with dec show False
      by simp
  qed
  show ?thesis
    using Kclq indep by (auto simp: split_graph_alt)
qed

theorem foldes_hammer:
  "is_split_graph \<longleftrightarrow> foldes_hammer_free"
  using foldes_hammer_converse split_graph_imp_foldes_hammer_free by blast

end

end
