(* Author: Bernhard Stöckl *)

theory Directed_Tree_Additions
  imports "Graph_Additions" "Shortest_Path_Tree"
begin

section \<open>Directed Tree Additions\<close>

context directed_tree
begin

lemma reachable1_not_reverse: "x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y \<Longrightarrow> \<not> y \<rightarrow>\<^sup>+\<^bsub>T\<^esub> x"
  by (metis awalk_Nil_iff reachable1_awalk reachable1_in_verts(2) trancl_trans unique_awalk_All)

lemma in_arcs_root: "in_arcs T root = {}"
  using in_degree_root_zero by (auto simp: in_degree_def in_arcs_finite root_in_T)

lemma dominated_not_root: "u \<rightarrow>\<^bsub>T\<^esub> v \<Longrightarrow> v \<noteq> root"
  using adj_in_verts(1) reachable1_not_reverse reachable_from_root by blast

lemma dominated_notin_awalk: "\<lbrakk>u \<rightarrow>\<^bsub>T\<^esub> v; awalk r p u\<rbrakk> \<Longrightarrow> v \<notin> set (awalk_verts r p)"
  using awalk_verts_reachable_to reachable1_not_reverse by blast

lemma apath_if_awalk: "awalk r p v \<Longrightarrow> apath r p v"
  using apath_def awalk_cyc_decompE' closed_w_imp_cycle cycle_free by blast

lemma awalk_verts_arc1_app: "tail T e \<in> set (awalk_verts r (p1@e#p2))"
  using awalk_verts_arc1 by auto

lemma apath_over_inarc_if_dominated:
  assumes "u \<rightarrow>\<^bsub>T\<^esub> v"
  shows "\<exists>p. apath root p v \<and> u \<in> set (awalk_verts root p)"
proof -
  obtain p where p_def: "awalk root p u" using assms unique_awalk by force
  obtain e where e_def: "e \<in> arcs T" "tail T e = u" "head T e = v" using assms by blast
  then have "awalk root (p@[e]) v" using p_def arc_implies_awalk by auto
  then show ?thesis using apath_if_awalk e_def(2) awalk_verts_arc1_app by blast
qed

end

locale finite_directed_tree = directed_tree + fin_digraph T

text \<open>
  Undirected, connected graphs are acyclic iff the number of edges is |verts| - 1. Since undirected
  graphs are modelled as bidirected graphs the number of edges is doubled.
\<close>

locale undirected_tree = graph +
  assumes connected: "connected G"
      and acyclic: "card (arcs G) \<le> 2 * (card (verts G) - 1)"

subsection \<open>Directed Trees of Connected Trees\<close>

subsubsection \<open>Tranformation using BFS\<close>

text \<open>
  Assumes existence of a conversion function (like BFS) that contains all reachable vertices.
\<close>

locale bfs_tree = directed_tree T root + subgraph T G for G T root +
  assumes root_in_G: "root \<in> verts G"
      and all_reachables: "verts T = {v. root \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v}"
begin

lemma dom_in_G: "u \<rightarrow>\<^bsub>T\<^esub> v \<Longrightarrow> u \<rightarrow>\<^bsub>G\<^esub> v"
  by (simp add: G.adj_mono sub_G)

lemma tailT_eq_tailG: "tail T = tail G"
  using sub_G by (simp add: Digraph_Component.subgraph_def compatible_def)

lemma headT_eq_headG: "head T = head G"
  using sub_G by (simp add: Digraph_Component.subgraph_def compatible_def)

lemma verts_T_subset_G: "verts T \<subseteq> verts G"
  by (metis awalk_sub_imp_awalk G.awalk_last_in_verts subsetI unique_awalk)

lemma reachable_verts_G_subset_T:
  "\<forall>x\<in>verts G. root \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x \<Longrightarrow> verts T \<supseteq> verts G"
  using all_reachables by (simp add: subset_eq)

lemma reachable_verts_G_eq_T: "\<forall>x\<in>verts G. root \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x \<Longrightarrow> verts T = verts G"
  by (simp add: reachable_verts_G_subset_T set_eq_subset verts_T_subset_G)

lemma connected_verts_G_eq_T:
  assumes "graph G" and "connected G"
  shows "verts T = verts G"
proof -
  have "root \<in> verts G" using root_in_G by fast
  then have "\<forall>x\<in>verts G. root \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x" using graph.connected_iff_reachable assms(1,2) by blast
  then show ?thesis using reachable_verts_G_eq_T by blast
qed

lemma Suc_card_if_fin: "fin_digraph G \<Longrightarrow> \<exists>n. Suc n = card (verts G)"
  using root_in_G card_0_eq not0_implies_Suc[of "card (verts G)"] fin_digraph.finite_verts by force

corollary Suc_card_if_graph: "graph G \<Longrightarrow> \<exists>n. Suc n = card (verts G)"
  using Suc_card_if_fin graph.axioms(1) digraph.axioms(1) by blast

lemma con_Suc_card_arcs_eq_card_verts:
  "\<lbrakk>graph G; connected G\<rbrakk> \<Longrightarrow> Suc (card (arcs T)) = card (verts G)"
  using Suc_card_arcs_eq_card_verts connected_verts_G_eq_T Suc_card_if_graph by fastforce

lemma reverse_arc_in_G:
  assumes "graph G" and "e1 \<in> arcs T"
  shows "\<exists>e2 \<in> arcs G. head G e2 = tail G e1 \<and> head G e1 = tail G e2"
proof -
  interpret graph G using assms(1) .
  have "e1 \<in> arcs G" using assms(2) sub_G by blast
  then show ?thesis using sym_arcs symmetric_conv by fastforce
qed

lemma reverse_arc_notin_T:
  assumes "e1 \<in> arcs T" and "head G e2 = tail G e1" and "head G e1 = tail G e2"
  shows "e2 \<notin> arcs T"
proof
  assume asm: "e2 \<in> arcs T"
  then have "tail T e2 \<rightarrow>\<^bsub>T\<^esub> head T e2" by (simp add: in_arcs_imp_in_arcs_ends)
  then have "head G e1 \<rightarrow>\<^bsub>T\<^esub> tail G e1"
    using assms(2,3) sub_G by(simp add: Digraph_Component.subgraph_def compatible_def)
  moreover have "tail G e1 \<rightarrow>\<^bsub>T\<^esub> head G e1"
    using assms(1) sub_G
    by(simp add: Digraph_Component.subgraph_def compatible_def in_arcs_imp_in_arcs_ends)
  ultimately show False using reachable1_not_reverse by blast
qed

lemma reverse_arc_in_G_only:
  assumes "graph G" and "e1 \<in> arcs T"
  shows "\<exists>e2 \<in> arcs G. head G e2 = tail G e1 \<and> head G e1 = tail G e2 \<and> e2 \<notin> arcs T"
  using reverse_arc_in_G reverse_arc_notin_T assms by blast

lemma no_multi_T_G:
  assumes "e1 \<in> arcs T" and "e2 \<in> arcs T" and "e1 \<noteq> e2"
  shows "head G e1 \<noteq> head G e2 \<or> tail G e1 \<noteq> tail G e2"
  using nomulti.no_multi_arcs assms sub_G
  by(auto simp: Digraph_Component.subgraph_def compatible_def arc_to_ends_def)

lemma T_arcs_compl_fin:
  assumes "fin_digraph G" and "es \<subseteq> arcs T"
  shows "finite {e2\<in> arcs G. (\<exists>e1 \<in> es. head G e2 = tail G e1 \<and> head G e1 = tail G e2)}"
  using assms fin_digraph.finite_arcs by fastforce

corollary T_arcs_compl_fin':
  assumes "graph G" and "es \<subseteq> arcs T"
  shows "finite {e2\<in> arcs G. (\<exists>e1 \<in> es. head G e2 = tail G e1 \<and> head G e1 = tail G e2)}"
  using assms T_arcs_compl_fin graph.axioms(1) digraph.axioms(1) by blast

lemma fin_verts_T: "fin_digraph G \<Longrightarrow> finite (verts T)"
  using fin_digraph.finite_verts finite_subset verts_T_subset_G by auto

corollary fin_verts_T': "graph G \<Longrightarrow> finite (verts T)"
  using fin_verts_T graph.axioms(1) digraph.axioms(1) by blast

lemma fin_arcs_T: "fin_digraph G \<Longrightarrow> finite (arcs T)"
  using fin_verts_T verts_finite_imp_arcs_finite by auto

corollary fin_arcs_T': "graph G \<Longrightarrow> finite (arcs T)"
  using fin_arcs_T graph.axioms(1) digraph.axioms(1) by blast

lemma T_arcs_compl_card_eq:
  assumes "graph G" and "es \<subseteq> arcs T"
  shows "card {e2\<in> arcs G. (\<exists>e1 \<in> es. head G e2 = tail G e1 \<and> head G e1 = tail G e2)} = card es"
  using finite_subset[OF assms(2) fin_arcs_T'[OF assms(1)]] assms
proof(induction es rule: finite_induct)
  case (insert e1 es)
  let ?ees = "{e2 \<in> arcs G. \<exists>e1\<in>insert e1 es. head G e2 = tail G e1 \<and> head G e1 = tail G e2}"
  let ?es = "{e2 \<in> arcs G. \<exists>e1\<in>es. head G e2 = tail G e1 \<and> head G e1 = tail G e2}"
  obtain e2 where e2_def: "e2 \<in> arcs G" "head G e2 = tail G e1" "head G e1 = tail G e2"
    using reverse_arc_in_G_only insert.prems by blast
  then have e2_notin: "e2 \<notin> {e2 \<in> arcs G. \<exists>e1\<in>es. head G e2 = tail G e1 \<and> head G e1 = tail G e2}"
    using insert.hyps(2) insert.prems(2) no_multi_T_G by fastforce
  have "\<forall>e3 \<in> arcs G. e2 = e3 \<or> head G e3 \<noteq> head G e2 \<or> tail G e3 \<noteq> tail G e2"
    using e2_def(1) nomulti_digraph.no_multi_alt digraph.axioms(3) graph.axioms(1) insert.prems(1)
    by fast
  then have "?ees = insert e2 ?es" using e2_def by auto
  moreover have "finite ?es" using insert.prems T_arcs_compl_fin' by simp
  ultimately have "card ?ees = Suc (card ?es)" using e2_notin by simp
  then show ?case using insert by force
qed(simp)

lemma arcs_graph_G_ge_2vertsT:
  assumes "graph G"
  shows "card (arcs G) \<ge> 2 * (card (verts T) - 1)"
proof -
  let ?compl = "{e2\<in> arcs G. (\<exists>e1 \<in> arcs T. head G e2 = tail G e1 \<and> head G e1 = tail G e2)}"
  interpret graph G by (rule assms)
  have "\<forall>e1 \<in> arcs T. \<exists>e2 \<in> arcs G. head G e2 = tail G e1 \<and> head G e1 = tail G e2"
    using reverse_arc_in_G_only assms by blast
  have fin1: "finite ?compl" by simp
  have "?compl \<inter> arcs T = {}" using reverse_arc_notin_T by blast
  then have "card (?compl \<union> arcs T) = card ?compl + card (arcs T)"
    using card_Un_disjoint[OF fin1 fin_arcs_T'] by blast
  moreover have "?compl \<union> arcs T \<subseteq> arcs G" using sub_G by blast
  moreover have "finite (arcs G)" by simp
  ultimately have "card ?compl + card (arcs T) \<le> card (arcs G)"
    using card_mono[of "arcs G" "?compl \<union> arcs T"] by presburger
  moreover have "card (arcs T) = (card (verts T) - 1)"
    using Suc_card_arcs_eq_card_verts assms by (simp add: fin_verts_T')
  ultimately show ?thesis using T_arcs_compl_card_eq by fastforce
qed

lemma arcs_graph_G_ge_2vertsG:
  "\<lbrakk>graph G; connected G\<rbrakk> \<Longrightarrow> card (arcs G) \<ge> 2 * (card (verts G) - 1)"
  using arcs_graph_G_ge_2vertsT connected_verts_G_eq_T by simp

lemma arcs_undir_G_eq_2vertsG:
  "\<lbrakk>undirected_tree G\<rbrakk> \<Longrightarrow> card (arcs G) = 2 * (card (verts G) - 1)"
  using arcs_graph_G_ge_2vertsG undirected_tree.acyclic undirected_tree.axioms(1)
    undirected_tree.connected by fastforce

lemma undir_arcs_compl_un_eq_arcs:
  assumes "undirected_tree G"
  shows "{e2\<in> arcs G. (\<exists>e1 \<in> arcs T. head G e2 = tail G e1 \<and> head G e1 = tail G e2)} \<union> arcs T
        = arcs G"
proof -
  let ?compl = "{e2\<in> arcs G. (\<exists>e1 \<in> arcs T. head G e2 = tail G e1 \<and> head G e1 = tail G e2)}"
  interpret undirected_tree G using assms(1) undirected_tree.axioms(1) by fast
  have "?compl \<inter> arcs T = {}" using reverse_arc_notin_T by blast
  then have 0: "card (?compl \<union> arcs T) = card ?compl + card (arcs T)"
    by (simp add: card_Un_disjoint fin_arcs_T' graph_axioms)
  have "card (arcs T) = (card (verts T) - 1)"
    using Suc_card_arcs_eq_card_verts by (simp add: fin_verts_T' graph_axioms)
  then have "card ?compl + card (arcs T) = 2 * (card (verts G) - 1)"
    using T_arcs_compl_card_eq connected_verts_G_eq_T connected by fastforce
  moreover have "card (arcs G) = 2 * (card (verts G) - 1)"
    using assms arcs_undir_G_eq_2vertsG by blast
  moreover have "?compl \<union> arcs T \<subseteq> arcs G" using sub_G by blast
  ultimately show ?thesis by (simp add: 0 card_subset_eq)
qed

lemma split_fst_nonelem:
  "\<lbrakk>\<not>set xs \<subseteq> X; set xs \<subseteq> Y\<rbrakk> \<Longrightarrow> \<exists>x ys zs. ys@x#zs=xs \<and> x \<notin> X \<and> x \<in> Y \<and> set ys \<subseteq> X"
proof(induction xs)
  case (Cons x xs)
  then show ?case
  proof(cases "x \<in> X")
    case True
    then obtain z ys zs where ys_def: "ys@z#zs=xs" "z \<notin> X" "z \<in> Y" "set ys \<subseteq> X" using Cons by auto
    then have "set (x#ys) \<subseteq> X" using True by simp
    then show ?thesis using ys_def(1-3) append_Cons by fast
  next
    case False
    then show ?thesis using Cons.prems(2) by fastforce
  qed
qed(simp)

lemma source_no_inarc_T: "head G e = root \<Longrightarrow> e \<notin> arcs T"
  using in_arcs_root sub_G by (auto simp: Digraph_Component.subgraph_def compatible_def)

lemma source_all_outarcs_T:
  "\<lbrakk>undirected_tree G; tail G e = root; e \<in> arcs G\<rbrakk> \<Longrightarrow> e \<in> arcs T"
  using source_no_inarc_T undir_arcs_compl_un_eq_arcs by blast

lemma cas_G_T: "G.cas = cas"
  using sub_G compatible_cas by fastforce

lemma awalk_G_T: "u \<in> verts T \<Longrightarrow> set p \<subseteq> arcs T \<Longrightarrow> G.awalk u p = awalk u p"
  using cas_G_T awalk_def G.awalk_def sub_G by fastforce

corollary awalk_G_T_root: "set p \<subseteq> arcs T \<Longrightarrow> G.awalk root p = awalk root p"
  using awalk_G_T root_in_T by blast

lemma awalk_verts_G_T: "G.awalk_verts = awalk_verts"
  using sub_G compatible_awalk_verts by blast

lemma apath_sub_imp_apath: "apath u p v \<Longrightarrow> G.apath u p v"
  by (simp add: G.apath_def apath_def awalk_sub_imp_awalk awalk_verts_G_T)

lemma outarc_inT_if_head_not_inarc:
  assumes "undirected_tree G"
      and "tail G e2 = v" and "e2 \<in> arcs G" and "head G e2 \<noteq> u" and "u \<rightarrow>\<^bsub>T\<^esub> v"
    shows "e2 \<in> arcs T"
proof (rule ccontr)
  let ?compl = "{e2\<in> arcs G. (\<exists>e1 \<in> arcs T. head G e2 = tail G e1 \<and> head G e1 = tail G e2)}"
  assume "e2 \<notin> arcs T"
  then have "e2 \<in> ?compl" using assms(3) undir_arcs_compl_un_eq_arcs[OF assms(1)] by blast
  then obtain e1 where e1_def: "e1 \<in> arcs T" "head G e2 = tail T e1" "head T e1 = v"
    using sub_G assms(2) by (auto simp: Digraph_Component.subgraph_def compatible_def)
  obtain e where "e \<in> arcs T" "tail T e = u" "head T e = v" using assms(5) by blast
  then show False using two_in_arcs_contr e1_def assms(4) by blast
qed

corollary reverse_arc_if_out_arc_undir:
  "\<lbrakk>undirected_tree G; tail G e2 = v; e2 \<in> arcs G; e2 \<notin> arcs T; u \<rightarrow>\<^bsub>T\<^esub> v\<rbrakk> \<Longrightarrow> head G e2 = u"
  using outarc_inT_if_head_not_inarc by blast

lemma undir_path_in_dir:
  assumes "undirected_tree G" "G.apath root p v"
  shows "set p \<subseteq> arcs T"
proof (rule ccontr)
  assume asm: "\<not>set p \<subseteq> arcs T"
  have "set p \<subseteq> arcs G" using assms(2) G.apath_def G.awalk_def by fast
  then obtain e p1 p2 where e_def: "p1 @ e # p2 = p" "e \<notin> arcs T" "e \<in> arcs G" "set p1 \<subseteq> arcs T"
    using split_fst_nonelem[OF asm, of "arcs G"] by auto
  show False
  proof(cases "p1=[]")
    case True
    then have "tail G e = root" using assms(2) e_def(1) G.apath_Cons_iff by auto
    then show ?thesis using source_all_outarcs_T[OF assms(1)] e_def(2,3) by blast
  next
    case False
    then have awalk_G: "G.awalk root (p1 @ e # p2) v"
      using assms(2) pre_digraph.apath_def e_def(1) by fast
    then have "G.awalk root p1 (tail G e)" by force
    then have awalk_p1T: "awalk root p1 (tail T e)"
      using e_def(4) sub_G cas_G_T root_in_T
      by (simp add: Digraph_Component.subgraph_def pre_digraph.awalk_def compatible_def)
    then have "root \<rightarrow>\<^sup>+\<^bsub>T\<^esub> tail T e" using False reachable1_awalkI by auto
    then obtain u where u_def: "u \<rightarrow>\<^bsub>T\<^esub> tail T e" using tranclD2 by metis
    have "tail T e = tail G e"
      using sub_G by (simp add: Digraph_Component.subgraph_def compatible_def)
    then have hd_e_u: "head G e = u"
      using reverse_arc_if_out_arc_undir[OF assms(1)] u_def e_def(2,3) by simp
    have "head T (last p1) = tail T e" using False awalk_p1T awalk_verts_conv by fastforce
    then have "tail T (last p1) = u"
      using False u_def e_def(4) two_in_arcs_contr last_in_set by fastforce
    then have 0: "tail G (last p1) = u"
      using sub_G by (simp add: Digraph_Component.subgraph_def compatible_def)
    obtain ps where "ps @ [last p1] = p1" using False append_butlast_last_id by auto
    then have ps_def: "ps @ [last p1] @ e # p2 = p" using e_def by auto
    then have awalk_G: "G.awalk root (ps @ [last p1] @ e # p2) v"
      using assms(2) by (simp add: pre_digraph.apath_def)
    have "\<not>(distinct (G.awalk_verts root p))"
      using G.not_distinct_if_head_eq_tail[OF 0 hd_e_u awalk_G] ps_def by simp
    then show ?thesis using assms(2) G.apath_def by blast
  qed
qed

lemma source_reach_all: "\<lbrakk>graph G; connected G; v \<in> verts G\<rbrakk> \<Longrightarrow> root \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  by (simp add: graph.connected_iff_reachable root_in_G)

lemma apath_if_in_verts: "\<lbrakk>graph G; connected G; v \<in> verts G\<rbrakk> \<Longrightarrow> \<exists>p. G.apath root p v"
  using G.reachable_apath by (simp add: graph.connected_iff_reachable root_in_G)

lemma undir_unique_awalk: "\<lbrakk>undirected_tree G; v \<in> verts G\<rbrakk> \<Longrightarrow> \<exists>!p. G.apath root p v"
  using undir_path_in_dir apath_if_in_verts awalk_G_T_root Suc_card_if_graph
  by (metis G.awalkI_apath unique_awalk_All undirected_tree.axioms(1) undirected_tree.connected)

lemma apath_in_dir_if_apath_G:
  assumes "undirected_tree G" "G.apath root p v"
  shows "apath root p v"
  using undir_path_in_dir[OF assms] assms(2) G.awalkI_apath apath_if_awalk awalk_G_T_root by force

end

locale bfs_locale =
  fixes bfs :: "('a, 'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> ('a, 'b) pre_digraph"
  assumes bfs_correct: "\<lbrakk>wf_digraph G; r \<in> verts G; bfs G r = T\<rbrakk> \<Longrightarrow> bfs_tree G T r"

locale undir_tree_todir = undirected_tree G + bfs_locale bfs
  for G :: "('a, 'b) pre_digraph"
  and bfs :: "('a, 'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> ('a, 'b) pre_digraph"
begin

abbreviation dir_tree_r :: "'a \<Rightarrow> ('a, 'b) pre_digraph" where
  "dir_tree_r \<equiv> bfs G"

lemma directed_tree_r: "r \<in> verts G \<Longrightarrow> directed_tree (dir_tree_r r) r"
  using bfs_correct bfs_tree.axioms(1) wf_digraph_axioms by fast

lemma bfs_dir_tree_r: "r \<in> verts G \<Longrightarrow> bfs_tree G (dir_tree_r r) r"
  using bfs_correct wf_digraph_axioms by blast

lemma dir_tree_r_dom_in_G: "r \<in> verts G \<Longrightarrow> u \<rightarrow>\<^bsub>dir_tree_r r\<^esub> v \<Longrightarrow> u \<rightarrow>\<^bsub>G\<^esub> v "
  using bfs_dir_tree_r bfs_tree.dom_in_G by fast

lemma verts_nempty: "verts G \<noteq> {}"
  using connected connected_iff_reachable by auto

lemma card_gt0: "card (verts G) > 0"
  using verts_nempty by auto

lemma Suc_card_1_eq_card[intro]: "Suc (card (verts G) - 1) = card (verts G)"
  using card_gt0 by simp

lemma verts_dir_tree_r_eq[simp]: "r \<in> verts G \<Longrightarrow> verts (dir_tree_r r) = verts G"
  using bfs_tree.connected_verts_G_eq_T[OF bfs_dir_tree_r graph_axioms connected] by blast

lemma tail_dir_tree_r_eq: "r \<in> verts G \<Longrightarrow> tail (dir_tree_r r) e = tail G e"
  using bfs_tree.tailT_eq_tailG[OF bfs_dir_tree_r] by simp

lemma head_dir_tree_r_eq: "r \<in> verts G \<Longrightarrow> head (dir_tree_r r) e = head G e"
  using bfs_tree.headT_eq_headG[OF bfs_dir_tree_r] by simp

lemma awalk_verts_G_T: "r \<in> verts G \<Longrightarrow> awalk_verts = pre_digraph.awalk_verts (dir_tree_r r)"
  using bfs_tree.awalk_verts_G_T bfs_dir_tree_r by fastforce

lemma dir_tree_r_all_reach: "\<lbrakk>r \<in> verts G; v \<in> verts G\<rbrakk> \<Longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>dir_tree_r r\<^esub> v"
  using directed_tree.reachable_from_root directed_tree_r verts_dir_tree_r_eq by fast

lemma fin_verts_dir_tree_r_eq: "r \<in> verts G \<Longrightarrow> finite (verts (dir_tree_r r))"
  using verts_dir_tree_r_eq by auto

lemma fin_arcs_dir_tree_r_eq: "r \<in> verts G \<Longrightarrow> finite (arcs (dir_tree_r r))"
  using fin_verts_dir_tree_r_eq directed_tree.verts_finite_imp_arcs_finite directed_tree_r
  by fast

lemma fin_directed_tree_r: "r \<in> verts G \<Longrightarrow> finite_directed_tree (dir_tree_r r) r"
  unfolding finite_directed_tree_def fin_digraph_def fin_digraph_axioms_def
  using directed_tree.axioms(1)  directed_tree_r fin_arcs_dir_tree_r_eq  verts_dir_tree_r_eq
  by force

lemma arcs_eq_2verts: "card (arcs G) = 2 * (card (verts G) - 1)"
  using bfs_tree.arcs_undir_G_eq_2vertsG[OF bfs_dir_tree_r undirected_tree_axioms] card_gt0
  by fastforce

lemma arcs_compl_un_eq_arcs:
  "r \<in> verts G \<Longrightarrow>
    {e2 \<in> arcs G. \<exists>e1\<in>arcs (dir_tree_r r). head G e2 = tail G e1 \<and> head G e1 = tail G e2}
      \<union> arcs (dir_tree_r r) = arcs G"
  using bfs_tree.undir_arcs_compl_un_eq_arcs[OF bfs_dir_tree_r undirected_tree_axioms] by blast

lemma unique_apath: "\<lbrakk>u \<in> verts G; v \<in> verts G\<rbrakk> \<Longrightarrow> \<exists>!p. apath u p v"
  using bfs_tree.undir_unique_awalk[OF bfs_dir_tree_r undirected_tree_axioms] by blast

lemma apath_in_dir_if_apath_G: "apath r p v \<Longrightarrow> pre_digraph.apath (dir_tree_r r) r p v"
  using bfs_tree.apath_in_dir_if_apath_G bfs_dir_tree_r undirected_tree_axioms awalkI_apath
  by fast

lemma apath_verts_sub_awalk:
  "\<lbrakk>apath u p1 v; awalk u p2 v\<rbrakk> \<Longrightarrow> set (awalk_verts u p1) \<subseteq> set (awalk_verts u p2)"
  using unique_apath_verts_sub_awalk unique_apath by blast

lemma dir_tree_arc1_in_apath:
  assumes "u \<rightarrow>\<^bsub>dir_tree_r r\<^esub> v" and "r \<in> verts G"
  shows "\<exists>p. apath r p v \<and> u \<in> set (awalk_verts r p)"
  using directed_tree.apath_over_inarc_if_dominated[OF directed_tree_r[OF assms(2)] assms(1)]
    bfs_tree.apath_sub_imp_apath bfs_dir_tree_r[OF assms(2)] bfs_tree.awalk_verts_G_T
  by fastforce

lemma dir_tree_arc1_in_awalk:
  "\<lbrakk>u \<rightarrow>\<^bsub>dir_tree_r r\<^esub> v; r \<in> verts G; awalk r p v\<rbrakk> \<Longrightarrow> u \<in> set (awalk_verts r p)"
  using dir_tree_arc1_in_apath apath_verts_sub_awalk by blast

end

subsubsection \<open>Tranformation using PSP-Trees\<close>

(* Alternative to bfs_tree *)

text \<open>
  Assumes existence of a conversion function that contains the n nearest nodes. This sections proves
  that such a generated tree contains all vertices in a connected graph.
\<close>

locale find_psp_tree_locale =
  fixes find_psp_tree :: "('a, 'b) pre_digraph \<Rightarrow> ('b \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('a, 'b) pre_digraph"
  assumes find_psp_tree: "\<lbrakk>r \<in> verts G; find_psp_tree G w r n = T\<rbrakk> \<Longrightarrow> psp_tree G T w r n"

context psp_tree
begin

lemma dom_in_G: "u \<rightarrow>\<^bsub>T\<^esub> v \<Longrightarrow> u \<rightarrow>\<^bsub>G\<^esub> v"
  by (simp add: G.adj_mono sub_G)

lemma tailT_eq_tailG: "tail T = tail G"
  using sub_G by (simp add: Digraph_Component.subgraph_def compatible_def)

lemma headT_eq_headG: "head T = head G"
  using sub_G by (simp add: Digraph_Component.subgraph_def compatible_def)

lemma verts_T_subset_G: "verts T \<subseteq> verts G"
  by (metis awalk_sub_imp_awalk G.awalk_last_in_verts subsetI unique_awalk)

lemma reachable_verts_G_subset_T:
  assumes "fin_digraph G"
      and "\<forall>x\<in>verts G. source \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x"
      and "Suc n = card (verts G)"
    shows "verts T \<supseteq> verts G"
proof(cases "card (verts G)")
  case 0
  have "finite (verts G)" using fin_digraph.finite_verts graph_def assms(1) by blast
  then show ?thesis using assms(3) 0 by simp
next
  case (Suc n)
  then have r_in_G: "source \<in> verts G" using source_in_G assms by blast
  show ?thesis
  proof(cases "n=0")
    case True
    then have "card (verts G) = 1" using assms(3) Suc by auto
    then have "verts G = {source}" using mem_card1_singleton r_in_G by fast
    then show ?thesis
      using ex_sp_eq_dia in_sccs_verts_conv_reachable insert_not_empty G.reachable_in_verts(1)
      by (metis G.reachable_mono non_empty reachable_refl sccs_verts_subsets singleton_iff sub_G)
  next
    case False
    then obtain n' where n'_def[simp]: "n' = n - 1 \<and> n \<noteq> n'" by simp
    show ?thesis
    proof(rule ccontr)
      assume "\<not>(verts T \<supseteq> verts G)"
      then have strict_sub: "verts T \<subset> verts G" using psp_tree_axioms verts_T_subset_G by fast
      then obtain x where x_def: "x \<notin> verts T \<and> x \<in> verts G" by blast
      then have x_reach: "source \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x" using assms(2) by simp
      have "finite (verts G)" using fin_digraph.finite_verts graph_def assms(1) by blast
      with strict_sub have T_lt_G: "card (verts T) < card (verts G)" by (simp add: psubset_card_mono)
      then have T_le_n: "card (verts T) \<le> n" using Suc assms(3) by simp
      have "G.n_nearest_verts w source n (verts T)"
        using Suc assms(3) partial by simp
      then have 1: "G.n_nearest_verts w source (Suc n') (verts T)" using n'_def by simp
      then obtain U where U_def[simp]: "U \<subseteq> verts T \<and> G.n_nearest_verts w source n' U"
        using Zero_not_Suc diff_Suc_1 equalityE G.nnvs_ind_cases subset_insertI by metis
      then show "False"
      proof(cases "G.unvisited_verts source U \<noteq> {}")
        case True
        then have "card U \<ge> Suc n'" using U_def fin_digraph.nnvs_card_ge_n assms(1) by fast
        then have U_Suc_n': "card U = Suc n'" using 1 U_def G.nnvs_card_le_n by force
        have "G.nearest_vert w source U \<in> G.unvisited_verts source U"
          using True assms(1) by (simp add: fin_digraph.nearest_vert_unvis)
        then have "G.nearest_vert w source U \<notin> U" using G.unvisited_verts_def by simp
        then have U_ins_Suc2_n': "card (insert (G.nearest_vert w source U) U) = Suc (Suc n')"
          using U_Suc_n' card_Suc_eq by blast
        have "card (verts T) \<le> Suc n'" using T_le_n by simp
        moreover have "card U \<le> card (verts T)" by (simp add: card_mono)
        ultimately have T_Suc_n': "card (verts T) = Suc n'" using U_Suc_n' by simp
        then have U_eq_T: "U = verts T" by (simp add: U_Suc_n' card_seteq)
        have "card (insert (G.nearest_vert w source U) U) = card (verts T)"
          using True U_eq_T U_ins_Suc2_n' 1 by (metis fin_digraph.nnvs_card_eq_n assms(1))
        then show ?thesis using T_Suc_n' U_ins_Suc2_n' by linarith
      next
        case False
        have "x \<notin> U" using x_def U_def by blast
        then have "G.unvisited_verts source U \<noteq> {}"
          using G.unvisited_verts_def x_def x_reach by blast
        then show ?thesis using False by simp
      qed
    qed
  qed
qed

lemma reachable_verts_G_eq_T:
  "\<lbrakk>fin_digraph G; \<forall>x\<in>verts G. source \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x; Suc n = card (verts G)\<rbrakk> \<Longrightarrow> verts T = verts G"
  by (simp add: reachable_verts_G_subset_T set_eq_subset verts_T_subset_G)

lemma connected_verts_G_eq_T:
  assumes "graph G"
      and "connected G"
      and "Suc n = card (verts G)"
    shows "verts T = verts G"
proof -
  have 0: "fin_digraph G" using assms(1) graph.axioms(1) digraph.axioms(1) by blast
  have "source \<in> verts G" using source_in_G by fast
  then have "\<forall>x\<in>verts G. source \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x" using graph.connected_iff_reachable assms(1,2) by blast
  then show ?thesis using assms(3) reachable_verts_G_eq_T 0 by blast
qed

lemma con_Suc_card_arcs_eq_card_verts:
  assumes "graph G"
      and "connected G"
      and "Suc n = card (verts G)"
    shows "Suc (card (arcs T)) = card (verts G)"
  using Suc_card_arcs_eq_card_verts connected_verts_G_eq_T assms by fastforce

lemma reverse_arc_in_G:
  assumes "graph G" and "e1 \<in> arcs T"
  shows "\<exists>e2 \<in> arcs G. head G e2 = tail G e1 \<and> head G e1 = tail G e2"
proof -
  interpret graph G using assms(1) .
  have "e1 \<in> arcs G" using assms(2) sub_G by blast
  then show ?thesis using sym_arcs symmetric_conv by fastforce
qed

lemma reverse_arc_notin_T:
  assumes "e1 \<in> arcs T" and "head G e2 = tail G e1" and "head G e1 = tail G e2"
  shows "e2 \<notin> arcs T"
proof
  assume asm: "e2 \<in> arcs T"
  then have "tail T e2 \<rightarrow>\<^bsub>T\<^esub> head T e2" by (simp add: in_arcs_imp_in_arcs_ends)
  then have "head G e1 \<rightarrow>\<^bsub>T\<^esub> tail G e1"
    using assms(2,3) sub_G by(simp add: Digraph_Component.subgraph_def compatible_def)
  moreover have "tail G e1 \<rightarrow>\<^bsub>T\<^esub> head G e1"
    using assms(1) sub_G
    by(simp add: Digraph_Component.subgraph_def compatible_def in_arcs_imp_in_arcs_ends)
  ultimately show False using reachable1_not_reverse by blast
qed

lemma reverse_arc_in_G_only:
  assumes "graph G" and "e1 \<in> arcs T"
  shows "\<exists>e2 \<in> arcs G. head G e2 = tail G e1 \<and> head G e1 = tail G e2 \<and> e2 \<notin> arcs T"
  using reverse_arc_in_G reverse_arc_notin_T assms by blast

lemma no_multi_T_G:
  assumes "e1 \<in> arcs T" and "e2 \<in> arcs T" and "e1 \<noteq> e2"
  shows "head G e1 \<noteq> head G e2 \<or> tail G e1 \<noteq> tail G e2"
  using nomulti.no_multi_arcs assms sub_G
  by(auto simp: Digraph_Component.subgraph_def compatible_def arc_to_ends_def)

lemma T_arcs_compl_fin:
  assumes "fin_digraph G" and "es \<subseteq> arcs T"
  shows "finite {e2\<in> arcs G. (\<exists>e1 \<in> es. head G e2 = tail G e1 \<and> head G e1 = tail G e2)}"
  using assms fin_digraph.finite_arcs by fastforce

corollary T_arcs_compl_fin':
  assumes "graph G" and "es \<subseteq> arcs T"
  shows "finite {e2\<in> arcs G. (\<exists>e1 \<in> es. head G e2 = tail G e1 \<and> head G e1 = tail G e2)}"
  using assms T_arcs_compl_fin graph.axioms(1) digraph.axioms(1) by blast

lemma T_arcs_compl_card_eq:
  assumes "graph G" and "es \<subseteq> arcs T"
  shows "card {e2\<in> arcs G. (\<exists>e1 \<in> es. head G e2 = tail G e1 \<and> head G e1 = tail G e2)} = card es"
using finite_subset[OF assms(2) finite_arcs] assms proof(induction es rule: finite_induct)
  case (insert e1 es)
  let ?ees = "{e2 \<in> arcs G. \<exists>e1\<in>insert e1 es. head G e2 = tail G e1 \<and> head G e1 = tail G e2}"
  let ?es = "{e2 \<in> arcs G. \<exists>e1\<in>es. head G e2 = tail G e1 \<and> head G e1 = tail G e2}"
  obtain e2 where e2_def: "e2 \<in> arcs G" "head G e2 = tail G e1" "head G e1 = tail G e2"
    using reverse_arc_in_G_only insert.prems by blast
  then have e2_notin: "e2 \<notin> {e2 \<in> arcs G. \<exists>e1\<in>es. head G e2 = tail G e1 \<and> head G e1 = tail G e2}"
    using insert.hyps(2) insert.prems(2) no_multi_T_G by fastforce
  have "\<forall>e3 \<in> arcs G. e2 = e3 \<or> head G e3 \<noteq> head G e2 \<or> tail G e3 \<noteq> tail G e2"
    using e2_def(1) nomulti_digraph.no_multi_alt digraph.axioms(3) graph.axioms(1) insert.prems(1)
    by fast
  then have "?ees = insert e2 ?es" using e2_def by auto
  moreover have "finite ?es" using insert.prems T_arcs_compl_fin' by simp
  ultimately have "card ?ees = Suc (card ?es)" using e2_notin by simp
  then show ?case using insert by force
qed(simp)

lemma arcs_graph_G_ge_2vertsT:
  assumes "graph G"
  shows "card (arcs G) \<ge> 2 * (card (verts T) - 1)"
proof -
  let ?compl = "{e2\<in> arcs G. (\<exists>e1 \<in> arcs T. head G e2 = tail G e1 \<and> head G e1 = tail G e2)}"
  interpret graph G by (rule assms)
  have "\<forall>e1 \<in> arcs T. \<exists>e2 \<in> arcs G. head G e2 = tail G e1 \<and> head G e1 = tail G e2"
    using reverse_arc_in_G_only assms by blast
  have "?compl \<inter> arcs T = {}" using reverse_arc_notin_T by blast
  then have "card (?compl \<union> arcs T) = card ?compl + card (arcs T)" by (simp add: card_Un_disjoint)
  moreover have "?compl \<union> arcs T \<subseteq> arcs G" using sub_G by blast
  moreover have "finite (arcs G)" by simp
  ultimately have "card ?compl + card (arcs T) \<le> card (arcs G)"
    using card_mono[of "arcs G" "?compl \<union> arcs T"] by presburger
  moreover have "card (arcs T) = (card (verts T) - 1)"
    using Suc_card_arcs_eq_card_verts assms by fastforce
  ultimately show ?thesis using T_arcs_compl_card_eq by fastforce
qed

lemma arcs_graph_G_ge_2vertsG:
  "\<lbrakk>graph G; connected G; Suc n = card (verts G)\<rbrakk> \<Longrightarrow> card (arcs G) \<ge> 2 * (card (verts G) - 1)"
  using arcs_graph_G_ge_2vertsT connected_verts_G_eq_T by simp

lemma arcs_undir_G_eq_2vertsG:
  "\<lbrakk>undirected_tree G; Suc n = card (verts G)\<rbrakk> \<Longrightarrow> card (arcs G) = 2 * (card (verts G) - 1)"
  using arcs_graph_G_ge_2vertsG undirected_tree.acyclic undirected_tree.axioms(1)
    undirected_tree.connected by fastforce

lemma undir_arcs_compl_un_eq_arcs:
  assumes "undirected_tree G" and "Suc n = card (verts G)"
  shows "{e2\<in> arcs G. (\<exists>e1 \<in> arcs T. head G e2 = tail G e1 \<and> head G e1 = tail G e2)} \<union> arcs T
        = arcs G"
proof -
  let ?compl = "{e2\<in> arcs G. (\<exists>e1 \<in> arcs T. head G e2 = tail G e1 \<and> head G e1 = tail G e2)}"
  interpret undirected_tree G using assms(1) undirected_tree.axioms(1) by fast
  have "?compl \<inter> arcs T = {}" using reverse_arc_notin_T by blast
  then have 0: "card (?compl \<union> arcs T) = card ?compl + card (arcs T)"
    by (simp add: card_Un_disjoint)
  have "card (arcs T) = (card (verts T) - 1)" using Suc_card_arcs_eq_card_verts assms by fastforce
  then have "card ?compl + card (arcs T) = 2 * (card (verts G) - 1)"
    using T_arcs_compl_card_eq connected_verts_G_eq_T connected assms(2) by fastforce
  moreover have "card (arcs G) = 2 * (card (verts G) - 1)"
    using assms arcs_undir_G_eq_2vertsG by blast
  moreover have "?compl \<union> arcs T \<subseteq> arcs G" using sub_G by blast
  ultimately show ?thesis by (simp add: 0 card_subset_eq)
qed

lemma split_fst_nonelem:
  "\<lbrakk>\<not>set xs \<subseteq> X; set xs \<subseteq> Y\<rbrakk> \<Longrightarrow> \<exists>x ys zs. ys@x#zs=xs \<and> x \<notin> X \<and> x \<in> Y \<and> set ys \<subseteq> X"
proof(induction xs)
  case (Cons x xs)
  then show ?case
  proof(cases "x \<in> X")
    case True
    then obtain z ys zs where ys_def: "ys@z#zs=xs" "z \<notin> X" "z \<in> Y" "set ys \<subseteq> X" using Cons by auto
    then have "set (x#ys) \<subseteq> X" using True by simp
    then show ?thesis using ys_def(1-3) append_Cons by fast
  next
    case False
    then show ?thesis using Cons.prems(2) by fastforce
  qed
qed(simp)

lemma source_no_inarc_T: "head G e = source \<Longrightarrow> e \<notin> arcs T"
  using in_arcs_root sub_G by (auto simp: Digraph_Component.subgraph_def compatible_def)

lemma source_all_outarcs_T:
  "\<lbrakk>undirected_tree G; Suc n = card (verts G); tail G e = source; e \<in> arcs G\<rbrakk> \<Longrightarrow> e \<in> arcs T"
  using source_no_inarc_T undir_arcs_compl_un_eq_arcs by blast

lemma cas_G_T: "G.cas = cas"
  using sub_G compatible_cas by fastforce

lemma awalk_G_T: "u \<in> verts T \<Longrightarrow> set p \<subseteq> arcs T \<Longrightarrow> G.awalk u p = awalk u p"
  using cas_G_T awalk_def G.awalk_def sub_G by fastforce

corollary awalk_G_T_root: "set p \<subseteq> arcs T \<Longrightarrow> G.awalk source p = awalk source p"
  using awalk_G_T root_in_T by blast

lemma awalk_verts_G_T: "G.awalk_verts = awalk_verts"
  using sub_G compatible_awalk_verts by blast

lemma apath_sub_imp_apath: "apath u p v \<Longrightarrow> G.apath u p v"
  by (simp add: G.apath_def apath_def awalk_sub_imp_awalk awalk_verts_G_T)

lemma outarc_inT_if_head_not_inarc:
  assumes "undirected_tree G" and "Suc n = card (verts G)"
      and "tail G e2 = v" and "e2 \<in> arcs G" and "head G e2 \<noteq> u" and "u \<rightarrow>\<^bsub>T\<^esub> v"
    shows "e2 \<in> arcs T"
proof (rule ccontr)
  let ?compl = "{e2\<in> arcs G. (\<exists>e1 \<in> arcs T. head G e2 = tail G e1 \<and> head G e1 = tail G e2)}"
  assume "e2 \<notin> arcs T"
  then have "e2 \<in> ?compl" using assms(4) undir_arcs_compl_un_eq_arcs[OF assms(1-2)] by blast
  then obtain e1 where e1_def: "e1 \<in> arcs T" "head G e2 = tail T e1" "head T e1 = v"
    using sub_G assms(3) by (auto simp: Digraph_Component.subgraph_def compatible_def)
  obtain e where "e \<in> arcs T" "tail T e = u" "head T e = v" using assms(6) by blast
  then show False using two_in_arcs_contr e1_def assms(5) by blast
qed

corollary reverse_arc_if_out_arc_undir:
  "\<lbrakk>undirected_tree G; Suc n = card (verts G); tail G e2 = v; e2 \<in> arcs G; e2 \<notin> arcs T; u \<rightarrow>\<^bsub>T\<^esub> v\<rbrakk>
    \<Longrightarrow> head G e2 = u"
  using outarc_inT_if_head_not_inarc by blast

lemma undir_path_in_dir:
  assumes "undirected_tree G" "Suc n = card (verts G)" "G.apath source p v"
  shows "set p \<subseteq> arcs T"
proof (rule ccontr)
  assume asm: "\<not>set p \<subseteq> arcs T"
  have "set p \<subseteq> arcs G" using assms(3) G.apath_def G.awalk_def by fast
  then obtain e p1 p2 where e_def: "p1 @ e # p2 = p" "e \<notin> arcs T" "e \<in> arcs G" "set p1 \<subseteq> arcs T"
    using split_fst_nonelem[OF asm, of "arcs G"] by auto
  show False
  proof(cases "p1=[]")
    case True
    then have "tail G e = source" using assms(3) e_def(1) G.apath_Cons_iff by auto
    then show ?thesis using source_all_outarcs_T[OF assms(1-2)] e_def(2,3) by blast
  next
    case False
    then have awalk_G: "G.awalk source (p1 @ e # p2) v"
      using assms(3) pre_digraph.apath_def e_def(1) by fast
    then have "G.awalk source p1 (tail G e)" by force
    then have awalk_p1T: "awalk source p1 (tail T e)"
      using e_def(4) sub_G cas_G_T root_in_T
      by (simp add: Digraph_Component.subgraph_def pre_digraph.awalk_def compatible_def)
    then have "source \<rightarrow>\<^sup>+\<^bsub>T\<^esub> tail T e" using False reachable1_awalkI by auto
    then obtain u where u_def: "u \<rightarrow>\<^bsub>T\<^esub> tail T e" using tranclD2 by metis
    have "tail T e = tail G e"
      using sub_G by (simp add: Digraph_Component.subgraph_def compatible_def)
    then have hd_e_u: "head G e = u"
      using reverse_arc_if_out_arc_undir[OF assms(1-2)] u_def e_def(2,3) by simp
    have "head T (last p1) = tail T e" using False awalk_p1T awalk_verts_conv by fastforce
    then have "tail T (last p1) = u"
      using False u_def e_def(4) two_in_arcs_contr last_in_set by fastforce
    then have 0: "tail G (last p1) = u"
      using sub_G by (simp add: Digraph_Component.subgraph_def compatible_def)
    obtain ps where "ps @ [last p1] = p1" using False append_butlast_last_id by auto
    then have ps_def: "ps @ [last p1] @ e # p2 = p" using e_def by auto
    then have awalk_G: "G.awalk source (ps @ [last p1] @ e # p2) v"
      using assms(3) by (simp add: pre_digraph.apath_def)
    have "\<not>(distinct (G.awalk_verts source p))"
      using G.not_distinct_if_head_eq_tail[OF 0 hd_e_u awalk_G] ps_def by simp
    then show ?thesis using assms(3) G.apath_def by blast
  qed
qed

lemma source_reach_all: "\<lbrakk>graph G; connected G; v \<in> verts G\<rbrakk> \<Longrightarrow> source \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  by (simp add: graph.connected_iff_reachable source_in_G)

lemma apath_if_in_verts: "\<lbrakk>graph G; connected G; v \<in> verts G\<rbrakk> \<Longrightarrow> \<exists>p. G.apath source p v"
  using G.reachable_apath by (simp add: graph.connected_iff_reachable source_in_G)

lemma undir_unique_awalk:
  "\<lbrakk>undirected_tree G; Suc n = card (verts G); v \<in> verts G\<rbrakk> \<Longrightarrow> \<exists>!p. G.apath source p v"
  using undir_path_in_dir apath_if_in_verts awalk_G_T_root
  by (metis G.awalkI_apath unique_awalk_All undirected_tree.axioms(1) undirected_tree.connected)

lemma apath_in_dir_if_apath_G:
  assumes "undirected_tree G" "Suc n = card (verts G)" "G.apath source p v"
  shows "apath source p v"
  using undir_path_in_dir[OF assms] assms(3) G.awalkI_apath apath_if_awalk awalk_G_T_root by force

end

locale undir_tree_todir_psp = undirected_tree G + find_psp_tree_locale to_psp
  for G :: "('a, 'b) pre_digraph"
  and to_psp :: "('a, 'b) pre_digraph \<Rightarrow> ('b \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('a, 'b) pre_digraph"
begin

abbreviation dir_tree_r :: "'a \<Rightarrow> ('a, 'b) pre_digraph" where
  "dir_tree_r r \<equiv> to_psp G (\<lambda>_. 1) r (Finite_Set.card (verts G) - 1)"

lemma directed_tree_r: "r \<in> verts G \<Longrightarrow> directed_tree (dir_tree_r r) r"
  using find_psp_tree psp_tree.axioms(1) by fast

lemma psp_dir_tree_r:
  "r \<in> verts G \<Longrightarrow> psp_tree G (dir_tree_r r) (\<lambda>_. 1) r (Finite_Set.card (verts G) - 1)"
  using find_psp_tree by blast

lemma dir_tree_r_dom_in_G: "r \<in> verts G \<Longrightarrow> u \<rightarrow>\<^bsub>dir_tree_r r\<^esub> v \<Longrightarrow> u \<rightarrow>\<^bsub>G\<^esub> v "
  using psp_tree.dom_in_G psp_dir_tree_r by fast

lemma verts_nempty: "verts G \<noteq> {}"
  using connected connected_iff_reachable by auto

lemma card_gt0: "card (verts G) > 0"
  using verts_nempty by auto

lemma Suc_card_1_eq_card[intro]: "Suc (card (verts G) - 1) = card (verts G)"
  using card_gt0 by simp

lemma verts_dir_tree_r_eq[simp]: "r \<in> verts G \<Longrightarrow> verts (dir_tree_r r) = verts G"
  using psp_tree.connected_verts_G_eq_T[OF psp_dir_tree_r graph_axioms connected] by blast

lemma tail_dir_tree_r_eq: "r \<in> verts G \<Longrightarrow> tail (dir_tree_r r) e = tail G e"
  using psp_tree.tailT_eq_tailG[OF psp_dir_tree_r] by simp

lemma head_dir_tree_r_eq: "r \<in> verts G \<Longrightarrow> head (dir_tree_r r) e = head G e"
  using psp_tree.headT_eq_headG[OF psp_dir_tree_r] by simp

lemma awalk_verts_G_T: "r \<in> verts G \<Longrightarrow> awalk_verts = pre_digraph.awalk_verts (dir_tree_r r)"
  using psp_tree.awalk_verts_G_T psp_dir_tree_r by fastforce

lemma dir_tree_r_all_reach: "\<lbrakk>r \<in> verts G; v \<in> verts G\<rbrakk> \<Longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>dir_tree_r r\<^esub> v"
  using directed_tree.reachable_from_root directed_tree_r verts_dir_tree_r_eq by fast

lemma fin_verts_dir_tree_r_eq: "r \<in> verts G \<Longrightarrow> finite (verts (dir_tree_r r))"
  using verts_dir_tree_r_eq by auto

lemma fin_arcs_dir_tree_r_eq: "r \<in> verts G \<Longrightarrow> finite (arcs (dir_tree_r r))"
  using fin_verts_dir_tree_r_eq directed_tree.verts_finite_imp_arcs_finite directed_tree_r
  by fast

lemma fin_directed_tree_r: "r \<in> verts G \<Longrightarrow> finite_directed_tree (dir_tree_r r) r"
  unfolding finite_directed_tree_def fin_digraph_def fin_digraph_axioms_def
  using directed_tree.axioms(1)  directed_tree_r fin_arcs_dir_tree_r_eq  verts_dir_tree_r_eq
  by force

lemma arcs_eq_2verts: "card (arcs G) = 2 * (card (verts G) - 1)"
  using psp_tree.arcs_undir_G_eq_2vertsG[OF psp_dir_tree_r undirected_tree_axioms] card_gt0
  by fastforce

lemma arcs_compl_un_eq_arcs:
  "r \<in> verts G \<Longrightarrow>
    {e2 \<in> arcs G. \<exists>e1\<in>arcs (dir_tree_r r). head G e2 = tail G e1 \<and> head G e1 = tail G e2}
      \<union> arcs (dir_tree_r r) = arcs G"
  using psp_tree.undir_arcs_compl_un_eq_arcs[OF psp_dir_tree_r undirected_tree_axioms] by blast

lemma unique_apath: "\<lbrakk>u \<in> verts G; v \<in> verts G\<rbrakk> \<Longrightarrow> \<exists>!p. apath u p v"
  using psp_tree.undir_unique_awalk[OF psp_dir_tree_r undirected_tree_axioms] by blast

lemma apath_in_dir_if_apath_G: "apath r p v \<Longrightarrow> pre_digraph.apath (dir_tree_r r) r p v"
  using psp_tree.apath_in_dir_if_apath_G psp_dir_tree_r undirected_tree_axioms awalkI_apath
  by fast

lemma apath_verts_sub_awalk:
  "\<lbrakk>apath u p1 v; awalk u p2 v\<rbrakk> \<Longrightarrow> set (awalk_verts u p1) \<subseteq> set (awalk_verts u p2)"
  using unique_apath_verts_sub_awalk unique_apath by blast

lemma dir_tree_arc1_in_apath:
  assumes "u \<rightarrow>\<^bsub>dir_tree_r r\<^esub> v" and "r \<in> verts G"
  shows "\<exists>p. apath r p v \<and> u \<in> set (awalk_verts r p)"
  using directed_tree.apath_over_inarc_if_dominated[OF directed_tree_r[OF assms(2)] assms(1)]
    psp_tree.apath_sub_imp_apath psp_dir_tree_r[OF assms(2)] psp_tree.awalk_verts_G_T
  by fastforce

lemma dir_tree_arc1_in_awalk:
  "\<lbrakk>u \<rightarrow>\<^bsub>dir_tree_r r\<^esub> v; r \<in> verts G; awalk r p v\<rbrakk> \<Longrightarrow> u \<in> set (awalk_verts r p)"
  using dir_tree_arc1_in_apath apath_verts_sub_awalk by blast

end

subsection \<open>Additions for Induction on Directed Trees\<close>

lemma fin_dir_tree_single:
  "finite_directed_tree \<lparr>verts = {r}, arcs = {}, tail = t, head = h\<rparr> r"
  by unfold_locales (fastforce simp: pre_digraph.cas.simps(1) pre_digraph.awalk_def)+

corollary dir_tree_single: "directed_tree \<lparr>verts = {r}, arcs = {}, tail = t, head = h\<rparr> r"
  by (simp add: fin_dir_tree_single finite_directed_tree.axioms(1))

lemma split_list_not_last: "\<lbrakk>y \<in> set xs; y \<noteq> last xs\<rbrakk> \<Longrightarrow> \<exists>as bs. as @ y # bs = xs \<and> bs \<noteq> []"
  using split_list by fastforce

lemma split_last_eq: "\<lbrakk>as @ y # bs = xs; bs \<noteq> []\<rbrakk> \<Longrightarrow> last bs = last xs"
  by auto

lemma split_list_last_sep: "\<lbrakk>y \<in> set xs; y \<noteq> last xs\<rbrakk> \<Longrightarrow> \<exists>as bs. as @ y # bs @ [last xs] = xs"
  using split_list_not_last[of y xs] split_last_eq append_butlast_last_id by metis

context directed_tree
begin

lemma root_if_all_reach: "\<forall>v \<in> verts T. x \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v \<Longrightarrow> x = root"
proof(rule ccontr)
  assume assms: "\<forall>v \<in> verts T. x \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v" "x \<noteq> root"
  then have "x \<rightarrow>\<^sup>*\<^bsub>T\<^esub> root" by (simp add: root_in_T)
  then have "\<exists>x. x \<rightarrow>\<^bsub>T\<^esub> root" using assms(2) by (auto elim: trancl.cases)
  then show False using dominated_not_root by blast
qed

lemma add_leaf_cas_preserv:
  fixes u v a
  defines "T' \<equiv> \<lparr>verts = verts T \<union> {v}, arcs = arcs T \<union> {a},
                tail = (tail T)(a := u), head = (head T)(a := v)\<rparr>"
  assumes "a \<notin> arcs T" and "set p \<subseteq> arcs T" and "cas x p y"
  shows "pre_digraph.cas T' x p y"
using assms proof(induction p arbitrary: x)
  case (Cons p ps)
  then have "tail T' p = x" by auto
  moreover have "pre_digraph.cas T' (head T' p) ps y" using Cons by force
  ultimately show ?case using pre_digraph.cas.simps(2) by fast
qed(simp add: pre_digraph.cas.simps(1))

lemma add_leaf_awalk_preserv:
  fixes u v a
  defines "T' \<equiv> \<lparr>verts = verts T \<union> {v}, arcs = arcs T \<union> {a},
                tail = (tail T)(a := u), head = (head T)(a := v)\<rparr>"
  assumes "a \<notin> arcs T" and "awalk x p y"
  shows "pre_digraph.awalk T' x p y"
  using assms add_leaf_cas_preserv unfolding pre_digraph.awalk_def by auto

lemma add_leaf_awalk_T:
  fixes u v a
  defines "T' \<equiv> \<lparr>verts = verts T \<union> {v}, arcs = arcs T \<union> {a},
                tail = (tail T)(a := u), head = (head T)(a := v)\<rparr>"
  assumes "a \<notin> arcs T" and "x \<in> verts T"
  shows "\<exists>p. pre_digraph.awalk T' root p x"
  using add_leaf_awalk_preserv assms unique_awalk[of x] by blast

lemma (in pre_digraph) cas_append_if:
  "\<lbrakk>cas x ps u; tail G p = u; head G p = v\<rbrakk> \<Longrightarrow> cas x (ps@[p]) v"
  using cas_append_iff[of x ps] by (metis append.right_neutral cas.simps)

lemma add_leaf_awalk_T_new:
  fixes u v a
  defines "T' \<equiv> \<lparr>verts = verts T \<union> {v}, arcs = arcs T \<union> {a},
                tail = (tail T)(a := u), head = (head T)(a := v)\<rparr>"
  assumes "a \<notin> arcs T" and "u \<in> verts T"
  shows "\<exists>p. pre_digraph.awalk T' root p v"
proof -
  obtain ps where ps_def: "root \<in> verts T'" "set ps \<subseteq> arcs T'" "pre_digraph.cas T' root ps u"
    using add_leaf_awalk_T assms unfolding pre_digraph.awalk_def by blast
  have "pre_digraph.cas T' root (ps@[a]) v"
    using pre_digraph.cas_append_if[OF ps_def(3)] assms(1) by simp
  moreover have "set (ps@[a]) \<subseteq> arcs T'" using ps_def(2) assms(1) by simp
  ultimately show ?thesis using ps_def(1) unfolding pre_digraph.awalk_def by blast
qed

lemma add_leaf_cas_orig:
  fixes u v a
  defines "T' \<equiv> \<lparr>verts = verts T \<union> {v}, arcs = arcs T \<union> {a},
                tail = (tail T)(a := u), head = (head T)(a := v)\<rparr>"
  assumes "a \<notin> arcs T" and "set p \<subseteq> arcs T" and "pre_digraph.cas T' x p y"
  shows "cas x p y"
using assms proof(induction p arbitrary: x)
  case (Cons p ps)
  then have "tail T' p = x" using pre_digraph.cas.simps(2) by fast
  then have "tail T p = x" using Cons.prems(1,2) Cons.hyps(2) by auto
  moreover have "head T' p = head T p" using Cons.prems(1,2) Cons.hyps(2) by auto
  moreover have "pre_digraph.cas T' (head T' p) ps y"
    using Cons.prems(3) pre_digraph.cas.simps(2) by fast
  ultimately show ?case using Cons by simp
qed(simp add: pre_digraph.cas.simps(1))

lemma add_leaf_awalk_orig_aux:
  fixes u v a
  defines "T' \<equiv> \<lparr>verts = verts T \<union> {v}, arcs = arcs T \<union> {a},
                tail = (tail T)(a := u), head = (head T)(a := v)\<rparr>"
  assumes "a \<notin> arcs T" and "x \<in> verts T" and "set p \<subseteq> arcs T" and "pre_digraph.awalk T' x p y"
  shows "awalk x p y"
  using assms add_leaf_cas_orig unfolding pre_digraph.awalk_def by blast

lemma add_leaf_cas_xT_if_yT:
  fixes u v a
  defines "T' \<equiv> \<lparr>verts = verts T \<union> {v}, arcs = arcs T \<union> {a},
                tail = (tail T)(a := u), head = (head T)(a := v)\<rparr>"
  assumes "u \<in> verts T" and "y \<in> verts T" and "set p \<subseteq> arcs T'" and "pre_digraph.cas T' x p y"
  shows "x \<in> verts T"
  using assms by (induction p arbitrary: x) (auto simp: pre_digraph.cas.simps)

lemma add_leaf_cas_xT_arcsT_if_yT:
  fixes u v a
  defines "T' \<equiv> \<lparr>verts = verts T \<union> {v}, arcs = arcs T \<union> {a},
                tail = (tail T)(a := u), head = (head T)(a := v)\<rparr>"
  assumes "v \<notin> verts T" and "y \<in> verts T" and "set p \<subseteq> arcs T'" and "pre_digraph.cas T' x p y"
  shows "set p \<subseteq> arcs T" and "x \<in> verts T"
  using assms by (induction p arbitrary: x) (auto simp: pre_digraph.cas.simps)

lemma add_leaf_awalk_orig:
  fixes u v a
  defines "T' \<equiv> \<lparr>verts = verts T \<union> {v}, arcs = arcs T \<union> {a},
                tail = (tail T)(a := u), head = (head T)(a := v)\<rparr>"
  assumes "a \<notin> arcs T" and "v \<notin> verts T" and "y \<in> verts T" and "pre_digraph.awalk T' x p y"
  shows "awalk x p y"
proof -
  have 0: "x \<in> verts T" "set p \<subseteq> arcs T"
    using assms add_leaf_cas_xT_arcsT_if_yT unfolding pre_digraph.awalk_def by blast+
  then show ?thesis using add_leaf_awalk_orig_aux assms by blast
qed

lemma add_leaf_awalk_orig_unique:
  fixes u v a
  defines "T' \<equiv> \<lparr>verts = verts T \<union> {v}, arcs = arcs T \<union> {a},
                tail = (tail T)(a := u), head = (head T)(a := v)\<rparr>"
  assumes "a \<notin> arcs T" and "v \<notin> verts T" and "y \<in> verts T"
      and "pre_digraph.awalk T' root ps y" and "pre_digraph.awalk T' root es y"
    shows "es = ps"
  using add_leaf_awalk_orig[OF assms(2,3)] assms(1,4,5,6) unique_awalk by fastforce

lemma add_leaf_awalk_new_split':
  fixes u v a
  defines "T' \<equiv> \<lparr>verts = verts T \<union> {v}, arcs = arcs T \<union> {a},
                tail = (tail T)(a := u), head = (head T)(a := v)\<rparr>"
  assumes "v \<notin> verts T" and "p \<noteq> []" and "pre_digraph.awalk T' x p v"
  shows "\<exists>as. as @ [a] = p"
using assms proof(induction p arbitrary: x)
  case (Cons p ps)
  then show ?case
  proof(cases "ps = []")
    case True
    then have "head T' p = v"
      using Cons.prems(3) by (simp add: pre_digraph.awalk_def pre_digraph.cas.simps)
    then have "head T p = v \<or> p = a" using Cons.hyps(2) by auto
    moreover have "p \<in> arcs T \<or> p = a"
      using Cons.hyps(2) Cons.prems(3) by (auto simp: pre_digraph.awalk_def)
    ultimately show ?thesis using Cons.prems(1) head_in_verts True by blast
  next
    case False
    then have "pre_digraph.cas T' (head T' p) ps v"
      using Cons.prems(3) by (simp add: pre_digraph.awalk_def pre_digraph.cas.simps)
    then have "pre_digraph.awalk T' (head T' p) ps v"
      using Cons.hyps(2) Cons.prems(3) unfolding pre_digraph.awalk_def by auto
    then obtain as where "as @ [a] = ps" using Cons False by blast
    then show ?thesis by auto
  qed
qed(simp)

lemma add_leaf_awalk_new_split:
  fixes u v a
  defines "T' \<equiv> \<lparr>verts = verts T \<union> {v}, arcs = arcs T \<union> {a},
                tail = (tail T)(a := u), head = (head T)(a := v)\<rparr>"
  assumes "v \<notin> verts T" and "u \<in> verts T" and "p \<noteq> []" and "pre_digraph.awalk T' x p v"
  shows "\<exists>as. as @ [a] = p \<and> pre_digraph.awalk T' x as u"
using assms proof(induction p arbitrary: x)
  case (Cons p ps)
  then show ?case
  proof(cases "ps = []")
    case True
    then have "head T' p = v"
      using Cons.prems(4) by (simp add: pre_digraph.awalk_def pre_digraph.cas.simps)
    then have "head T p = v \<or> p = a" using Cons.hyps(2) by auto
    moreover have "p \<in> arcs T \<or> p = a"
      using Cons.hyps(2) Cons.prems(4) by (auto simp: pre_digraph.awalk_def)
    ultimately have "p = a" using Cons.prems(1) by auto
    then have "[] @ [a] = p # ps" using True by auto
    have "tail T' p = u" using Cons.hyps(2) \<open>p = a\<close> by simp
    then have "u = x"
      using Cons.prems(4) by (simp add: pre_digraph.awalk_def pre_digraph.cas.simps(2))
    then have "pre_digraph.awalk T' x [] u"
      using Cons.hyps(2) Cons.prems(2) by (simp add: pre_digraph.awalk_def pre_digraph.cas.simps)
    then show ?thesis using \<open>[] @ [a] = p # ps\<close> by blast
  next
    case False
    then have "pre_digraph.cas T' (head T' p) ps v"
      using Cons.prems(4) by (simp add: pre_digraph.awalk_def pre_digraph.cas.simps)
    then have "pre_digraph.awalk T' (head T' p) ps v"
      using Cons.hyps(2) Cons.prems(4) unfolding pre_digraph.awalk_def by auto
    then obtain as where as_def: "as @ [a] = ps" "pre_digraph.awalk T' (head T' p) as u"
      using Cons False by blast
    then have "x \<in> verts T'" "set (p#as) \<subseteq> arcs T'" "tail T' p = x"
      using Cons.prems(4) by (auto simp: pre_digraph.awalk_def pre_digraph.cas.simps)
    then have "pre_digraph.cas T' x (p#as) u"
      using as_def(2) pre_digraph.cas.simps(2) unfolding pre_digraph.awalk_def by fast
    then have "pre_digraph.awalk T' x (p#as) u"
      using \<open>x \<in> verts T'\<close> \<open>set (p#as) \<subseteq> arcs T'\<close> by (simp add: pre_digraph.awalk_def)
    then show ?thesis using as_def(1) by auto
  qed
qed(simp)

lemma add_leaf_awalk_new_unique:
  fixes u v a
  defines "T' \<equiv> \<lparr>verts = verts T \<union> {v}, arcs = arcs T \<union> {a},
                tail = (tail T)(a := u), head = (head T)(a := v)\<rparr>"
  assumes "a \<notin> arcs T" and "u \<in> verts T" and "v \<notin> verts T"
      and "pre_digraph.awalk T' root ps v" and "pre_digraph.awalk T' root es v"
    shows "es = ps"
proof -
  have "root \<noteq> v" using \<open>v \<notin> verts T\<close> root_in_T by blast
  then have "ps \<noteq> []" "es \<noteq> []"
    using assms(5,6) root_in_T pre_digraph.awalk_def pre_digraph.cas.simps(1) by fast+
  then obtain as where as_def: "as @ [a] = ps" "pre_digraph.awalk T' root as u"
    using add_leaf_awalk_new_split assms(1,3-5) by blast
  obtain bs where bs_def: "bs @ [a] = es" "pre_digraph.awalk T' root bs u"
    using \<open>es \<noteq> []\<close> add_leaf_awalk_new_split assms(1,3,4,6) by blast
  then show ?thesis using as_def assms(1-4) add_leaf_awalk_orig_unique by blast
qed

lemma add_leaf_awalk_unique:
  fixes u v a
  defines "T' \<equiv> \<lparr>verts = verts T \<union> {v}, arcs = arcs T \<union> {a},
                tail = (tail T)(a := u), head = (head T)(a := v)\<rparr>"
  assumes "a \<notin> arcs T" and "u \<in> verts T" and "v \<notin> verts T" and "x \<in> verts T'"
  shows "\<exists>!p. pre_digraph.awalk T' root p x"
  using assms add_leaf_awalk_T add_leaf_awalk_T_new
  by (auto simp: add_leaf_awalk_new_unique add_leaf_awalk_orig_unique)

lemma add_leaf_dir_tree:
  "\<lbrakk>a \<notin> arcs T; u \<in> verts T; v \<notin> verts T\<rbrakk>
    \<Longrightarrow> directed_tree \<lparr>verts = verts T \<union> {v}, arcs = arcs T \<union> {a},
                      tail = (tail T)(a := u), head = (head T)(a := v)\<rparr> root"
  using add_leaf_awalk_unique by unfold_locales (auto simp: root_in_T)

lemma add_leaf_dom_preserv:
  "\<lbrakk>a \<notin> arcs T; x \<rightarrow>\<^bsub>T\<^esub> y\<rbrakk>
    \<Longrightarrow> x \<rightarrow>\<^bsub>\<lparr>verts = verts T \<union> {v}, arcs = arcs T \<union> {a},
              tail = (tail T)(a := u), head = (head T)(a := v)\<rparr>\<^esub> y"
  unfolding arcs_ends_def arc_to_ends_def by force

end


subsection \<open>Branching Points in Directed Trees\<close>

text \<open>Proofs that show the existence of a last branching point given it is not a chain.\<close>

context directed_tree
begin

lemma add_leaf_is_leaf:
  assumes "T' = \<lparr>verts = V, arcs = A, tail = t, head = h\<rparr>"
      and "T = \<lparr>verts = V \<union> {v}, arcs = A \<union> {a}, tail = t(a := u), head = h(a := v)\<rparr>"
      and "u \<in> V"
      and "v \<notin> V"
      and "a \<notin> A"
      and "directed_tree T' root'"
    shows "leaf v"
proof -
  have 0: "wf_digraph T" by (simp add: wf_digraph_axioms)
  have 1: "wf_digraph T'" using assms(6) directed_tree.axioms(1) by fast
  then have "\<forall>a\<in>arcs T. tail T a \<noteq> v"
    by (metis Un_insert_right assms(1-4) fun_upd_apply insert_iff
        pre_digraph.select_convs(1-3) sup_bot_right wf_digraph.tail_in_verts)
  then have "out_arcs T v = {}" using in_out_arcs_conv by fast
  moreover have "v \<in> verts T" using assms(2) by simp
  ultimately show ?thesis by (simp add: leaf_def)
qed

lemma reachable_via_child_impl_same:
  assumes "x \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v" and "y \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v" and "u \<rightarrow>\<^bsub>T\<^esub> x" and "u \<rightarrow>\<^bsub>T\<^esub> y"
  shows "x = y"
proof (rule ccontr)
  assume asm: "x \<noteq> y"
  obtain p1 where p1_def: "awalk x p1 v" using assms(1) reachable_awalk by auto
  then obtain e1 where e1_def: "awalk u (e1#p1) v" using assms(3) awalk_Cons_iff by blast
  obtain p2 where p2_def: "awalk y p2 v" using assms(2) reachable_awalk by auto
  then obtain e2 where e2_def: "awalk u (e2#p2) v" using assms(4) awalk_Cons_iff by blast
  then have "e1#p1 \<noteq> e2#p2" using asm awalk_ends p1_def p2_def by blast
  then show False using e1_def e2_def unique_awalk_All by auto
qed

lemma new_leaf_last_in_orig_if_arcs_in_orig:
  assumes "x \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y"
      and "T = \<lparr>verts = V \<union> {v}, arcs = A \<union> {a}, tail = t(a := u), head = h(a := v)\<rparr>"
      and "T' = \<lparr>verts = V, arcs = A, tail = t, head = h\<rparr>"
      and "x \<in> V"
      and "y \<in> V"
      and "u \<in> V"
      and "v \<notin> V"
      and "a \<notin> A"
      and "a1\<in>arcs T' \<and> a2\<in>arcs T' \<and> a1\<noteq>a2 \<and> t a1 = y \<and> t a2 = y"
      and "finite (arcs T)"
      and "\<lbrakk>\<exists>a\<in>wf_digraph.branching_points T'. x \<rightarrow>\<^sup>*\<^bsub>T'\<^esub> a; directed_tree T' r\<rbrakk>
            \<Longrightarrow> \<exists>a\<in>wf_digraph.last_branching_points T'. x \<rightarrow>\<^sup>*\<^bsub>T'\<^esub> a"
      and "directed_tree T' r"
    shows "\<exists>y'\<in> last_branching_points. x \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y'"
proof -
  have 1: "wf_digraph T'" using directed_tree.axioms(1) assms(12) by fast
  have "a1\<in>arcs T' \<and> a2\<in>arcs T' \<and> a1\<noteq>a2 \<and> tail T' a1 = y \<and> tail T' a2 = y"
    using assms(3,9) by simp
  then have branching_point: "y \<in> wf_digraph.branching_points T'"
    using wf_digraph.branching_points_def 1 by blast
  then have "x \<rightarrow>\<^sup>*\<^bsub>T'\<^esub> y" using assms(1-8,10) 1 new_leaf_same_reachables_orig by blast
  then have "\<exists>a \<in> wf_digraph.branching_points T'. x \<rightarrow>\<^sup>*\<^bsub>T'\<^esub> a" using branching_point by blast
  then obtain a where a_def[simp]: "a\<in>wf_digraph.last_branching_points T' \<and> x \<rightarrow>\<^sup>*\<^bsub>T'\<^esub> a"
    using assms(11,12) by blast
  then have 2: "a\<in>wf_digraph.last_branching_points T' \<and> x \<rightarrow>\<^sup>*\<^bsub>T\<^esub> a"
    using new_leaf_same_reachables_new assms(2-4,6-8) 1
    by (metis branch_if_leaf_added new_leaf_no_branch wf_digraph.last_branch_is_branch)
  have 3: "\<forall>y. a \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y \<longrightarrow> a\<noteq>y" using reachable1_not_reverse by blast
  have "a \<in> verts T'"
    using a_def 1 by (simp add: wf_digraph.branch_in_verts wf_digraph.last_branch_is_branch)
  then show ?thesis
    using new_leaf_last_branch_exists_preserv 1 2 3 assms(2,3,6-8,10)
    by (metis pre_digraph.select_convs(1,2))
qed

lemma finite_branch_impl_last_branch:
  assumes "finite (verts T)"
      and "\<exists>y\<in>branching_points. x \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y"
      and "directed_tree T r"
  shows "\<exists>z\<in>last_branching_points. x \<rightarrow>\<^sup>*\<^bsub>T\<^esub> z"
using assms proof(induction arbitrary: r rule: finite_directed_tree_induct)
  case (single_vert t h root)
  let ?T = "\<lparr>verts = {root}, arcs = {}, tail = t, head = h\<rparr>"
  have "directed_tree ?T r" using single_vert by simp
  then have 0: "wf_digraph ?T" using directed_tree.axioms(1) by fast
  obtain y where y_def[simp]: "y \<in> wf_digraph.branching_points ?T \<and> x \<rightarrow>\<^sup>*\<^bsub>?T\<^esub> y"
    using single_vert by blast
  have "y = root"
    by (metis y_def empty_iff insert_iff pre_digraph.select_convs(1) reachable_in_vertsE)
  then have "\<not>(\<exists>x \<in> verts ?T. x\<noteq>y)" by simp
  then have "\<not>(\<exists>x \<in> wf_digraph.branching_points ?T. x\<noteq>y)"
    using 0 wf_digraph.branch_in_verts by fast
  then have "y \<in> wf_digraph.last_branching_points ?T"
    using wf_digraph.last_branching_points_def 0 by fastforce
  then show ?case by force
next
  case (add_leaf T' V A t h u root a v)
  let ?T = "\<lparr>verts = V \<union> {v}, arcs = A \<union> {a}, tail = t(a := u), head = h(a := v)\<rparr>"
  have 0: "wf_digraph ?T" using add_leaf.prems(2) directed_tree.axioms(1) by fast
  have 1: "wf_digraph T'" using add_leaf.hyps(3) directed_tree.axioms(1) by fast
  have 2: "finite (arcs ?T)"
    using directed_tree.verts_finite_imp_arcs_finite add_leaf.hyps(1-3) by fastforce
  obtain y where y_def[simp]: "y \<in> wf_digraph.branching_points ?T \<and> x \<rightarrow>\<^sup>*\<^bsub>?T\<^esub> y"
    using add_leaf.prems by blast
  then obtain a1 a2 where a12: "a1\<in>arcs ?T \<and> a2\<in>arcs ?T \<and> a1\<noteq>a2 \<and> tail ?T a1 = y \<and> tail ?T a2 = y"
    using wf_digraph.branching_points_def 0 by blast
  then have y_not_v: "y \<noteq> v"
    using Un_insert_right add_leaf.hyps(1,3,5) directed_tree.axioms(1) fun_upd_apply insert_iff
    by (metis pre_digraph.select_convs(1-3) sup_bot_right wf_digraph.tail_in_verts)
  have "y \<in> verts ?T"
    using y_def wf_digraph.branch_in_verts 0 by fast
  then have y_in_T: "y \<in> verts T'" using y_not_v add_leaf.hyps(1) by simp
  have "x \<in> verts ?T" using add_leaf.prems(1) reachable_in_vertsE by force
  have leaf_v: "pre_digraph.leaf ?T v"
    using directed_tree.add_leaf_is_leaf[of ?T] add_leaf.hyps(1,3-6) add_leaf.prems(2) by blast
  then have "out_degree ?T v = 0"
    using add_leaf.prems(2) directed_tree.leaf_out_degree_zero by fast
  then have "x \<noteq> v"
    using y_not_v y_def 0 Diff_empty add_leaf directed_tree.verts_finite_imp_arcs_finite
      select_convs(1) wf_digraph.out_degree_0_only_self by fastforce
  then have x_in_T': "x \<in> verts T'" using \<open>x \<in> verts ?T\<close> add_leaf.hyps(1) by auto
  show ?case
  proof(cases "a1=a \<or> a2=a")
    case True
    then have "y = u" using a12 by fastforce
    show ?thesis
    proof(cases "\<exists>y'\<in>wf_digraph.branching_points ?T. y \<noteq> y' \<and> y \<rightarrow>\<^sup>*\<^bsub>?T\<^esub> y'")
      case True
      then obtain y' where y'_def: "y'\<in>wf_digraph.branching_points ?T \<and> y \<noteq> y' \<and> y \<rightarrow>\<^sup>*\<^bsub>?T\<^esub> y'"
        by blast
      then obtain a1 a2 where a12: "a1\<in>arcs ?T \<and> a2\<in>arcs ?T \<and> a1\<noteq>a2 \<and> tail ?T a1 = y' \<and> tail ?T a2 = y'"
        using wf_digraph.branching_points_def 0 by blast
      then have "y' \<noteq> u" using \<open>y=u\<close> y'_def by blast
      moreover have "tail ?T a = u" by simp
      ultimately have "a1\<noteq>a \<and> a2\<noteq>a" using \<open>y=u\<close> a12 by fastforce
      then have 3: "a1\<in>arcs T' \<and> a2\<in>arcs T' \<and> a1\<noteq>a2 \<and> t a1 = y' \<and> t a2 = y'"
        using a12 add_leaf.hyps(1) by simp
      then have branching_point: "y' \<in> wf_digraph.branching_points T'"
        using wf_digraph.branching_points_def 1 add_leaf.hyps(1) by fastforce
      have y'_in_T: "y' \<in> verts T'" by (simp add: 1 branching_point wf_digraph.branch_in_verts)
      have "x \<rightarrow>\<^sup>*\<^bsub>?T\<^esub> y'" using y_def y'_def wf_digraph.reachable_trans 0 by fast
      then show ?thesis
        using directed_tree.new_leaf_last_in_orig_if_arcs_in_orig[of ?T r x y']
          add_leaf.prems(2) 2 3 add_leaf.IH add_leaf.hyps(1,3-6) x_in_T' y'_in_T by simp
    next
      case False
      then show ?thesis using wf_digraph.last_branching_points_def y_def 0 by fast
    qed
  next
    case False
    then have "a1\<in>arcs ?T \<and> a2\<in>arcs ?T \<and> a1\<noteq>a2 \<and> t a1 = y \<and> t a2 = y"
      using a12 by simp
    then have 3: "a1\<in>arcs T' \<and> a2\<in>arcs T' \<and> a1\<noteq>a2 \<and> t a1 = y \<and> t a2 = y"
      using False a12 add_leaf.hyps(1) by auto
    have "x \<rightarrow>\<^sup>*\<^bsub>?T\<^esub> y" using y_def by simp
    then show ?thesis
      using directed_tree.new_leaf_last_in_orig_if_arcs_in_orig[of ?T r x y]
        add_leaf.prems(2) 2 3 add_leaf.IH add_leaf.hyps(1,3-6) x_in_T' y_in_T by simp
  qed
qed

lemma subgraph_no_last_branch_chain:
  assumes "subgraph C T"
      and "finite (verts T)"
      and "verts C \<subseteq> verts T - {x. \<exists>y\<in>last_branching_points. x \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y}"
    shows "wf_digraph.is_chain C"
  using assms finite_branch_impl_last_branch subgraph_no_branch_chain last_branch_is_branch
  by (smt (verit, ccfv_SIG) Collect_cong directed_tree_axioms)

lemma reach_from_last_in_chain:
  assumes "\<exists>y \<in> last_branching_points. y \<rightarrow>\<^sup>+\<^bsub>T\<^esub> x"
  shows "x \<in> verts T - {x. \<exists>y\<in>last_branching_points. x \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y}"
  using assms last_branch_alt reachable1_not_reverse reachable1_reachable reachable1_reachable_trans
  by (smt (verit, del_insts) Diff_iff last_branch_is_branch mem_Collect_eq reachable1_in_verts(2))

text \<open>Directed Trees don't have merging points.\<close>

lemma merging_empty: "merging_points = {}"
  using two_in_arcs_contr merging_points_def by auto

lemma subgraph_no_last_merge_chain:
  assumes "subgraph C T"
  shows "wf_digraph.is_chain' C"
proof (rule ccontr)
  assume asm: "\<not>wf_digraph.is_chain' C"
  have "wf_digraph C" using assms(1) Digraph_Component.subgraph_def subgraph.sub_G by auto
  then obtain x where x_def: "x \<in> wf_digraph.merging_points C"
    using wf_digraph.is_chain'_def asm by blast
  then have "x \<in> merging_points" using assms(1) merge_in_supergraph by simp
  then show False using merging_empty by simp
qed

subsection \<open>Converting to Trees of Lists\<close>

definition to_list_tree :: "('a list, 'b) pre_digraph" where
  "to_list_tree =
    \<lparr>verts = (\<lambda>x. [x]) ` verts T, arcs = arcs T, tail = (\<lambda>x. [tail T x]), head =  (\<lambda>x. [head T x])\<rparr>"

lemma to_list_tree_union_verts_eq: "\<Union>(set ` verts to_list_tree) = verts T"
  using to_list_tree_def by simp

lemma to_list_tree_cas: "cas u p v \<longleftrightarrow> pre_digraph.cas to_list_tree [u] p [v]"
  by(induction p arbitrary: u) (auto simp: Arc_Walk.pre_digraph.cas.simps to_list_tree_def)

lemma to_list_tree_awalk: "awalk u p v \<longleftrightarrow>  pre_digraph.awalk to_list_tree [u] p [v]"
  unfolding pre_digraph.awalk_def using to_list_tree_cas to_list_tree_def by auto

lemma to_list_tree_awalk_if_in_verts:
  assumes "v \<in> verts to_list_tree"
  shows "\<exists>p. pre_digraph.awalk to_list_tree [root] p v"
proof -
  have "root \<in> verts T" using root_in_T by blast
  obtain v' where 0: "v = [v']" using to_list_tree_def assms(1) by auto
  then have "v' \<in> verts T" using assms to_list_tree_def by auto
  then obtain p' where "awalk root p' v'" using unique_awalk by blast
  then show ?thesis using to_list_tree_awalk 0 by auto
qed

lemma to_list_tree_root_awalk_unique:
  assumes "v \<in> verts to_list_tree"
      and "pre_digraph.awalk to_list_tree [root] p v"
      and "pre_digraph.awalk to_list_tree [root] y v"
  shows "p = y"
proof (rule ccontr)
  assume "p \<noteq> y"
  obtain v' where v'_def: "v = [v']" using to_list_tree_def assms(1) by auto
  then have "v' \<in> verts T" using assms(1) to_list_tree_def by auto
  show False using to_list_tree_awalk assms \<open>p \<noteq> y\<close> assms(2,3) unique_awalk v'_def by blast
qed

lemma to_list_tree_directed_tree: "directed_tree to_list_tree [root]"
  apply(unfold_locales)
     apply(auto simp: to_list_tree_def root_in_T)[3]
  by(auto intro: to_list_tree_awalk_if_in_verts to_list_tree_root_awalk_unique)

lemma to_list_tree_disjoint_verts:
  "\<lbrakk>u \<in> verts to_list_tree; v \<in> verts to_list_tree; u\<noteq>v\<rbrakk> \<Longrightarrow> set u \<inter> set v = {}"
  unfolding to_list_tree_def by auto

lemma to_list_tree_nempty: "v \<in> verts to_list_tree \<Longrightarrow> v \<noteq> []"
  unfolding to_list_tree_def by auto

lemma to_list_tree_single: "v \<in> verts to_list_tree \<Longrightarrow> \<exists>x. v = [x] \<and> x \<in> verts T"
  unfolding to_list_tree_def by auto

lemma to_list_tree_dom_iff: "x \<rightarrow>\<^bsub>T\<^esub> y \<longleftrightarrow> [x] \<rightarrow>\<^bsub>to_list_tree\<^esub> [y]"
  unfolding to_list_tree_def arcs_ends_def arc_to_ends_def by auto

end

locale fin_list_directed_tree = finite_directed_tree T for T :: "('a list,'b) pre_digraph" +
  assumes disjoint_verts: "\<lbrakk>u \<in> verts T; v \<in> verts T; u \<noteq> v\<rbrakk> \<Longrightarrow> set u \<inter> set v = {}"
      and nempty_verts: "v \<in> verts T \<Longrightarrow> v \<noteq> []"

context finite_directed_tree
begin

lemma to_list_tree_fin_digraph: "fin_digraph to_list_tree"
  by (unfold_locales) (auto simp: to_list_tree_def)

lemma to_list_tree_finite_directed_tree: "finite_directed_tree to_list_tree [root]"
  by (simp add: finite_directed_tree_def to_list_tree_fin_digraph to_list_tree_directed_tree)

lemma to_list_tree_fin_list_directed_tree: "fin_list_directed_tree [root] to_list_tree"
  apply(simp add: fin_list_directed_tree_def to_list_tree_finite_directed_tree)
  apply(unfold_locales)
  by (auto simp: to_list_tree_disjoint_verts to_list_tree_nempty)

end

end