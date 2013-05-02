(* Title:  Digraph_Component.thy
   Author: Lars Noschinski, TU München
*)

theory Digraph_Component
imports
  Digraph
  Arc_Walk
  Pair_Digraph
begin

section {* Components of (Symmetric) Digraphs *}

definition compatible :: "('a,'b) pre_digraph \<Rightarrow> ('a,'b) pre_digraph \<Rightarrow> bool" where
  "compatible G H \<equiv> tail G = tail H \<and> head G = head H"

definition subgraph :: "('a,'b) pre_digraph \<Rightarrow> ('a,'b) pre_digraph \<Rightarrow> bool" where
  "subgraph H G \<equiv> verts H \<subseteq> verts G \<and> arcs H \<subseteq> arcs G \<and> wf_digraph H \<and> compatible G H"

definition induced_subgraph :: "('a,'b) pre_digraph \<Rightarrow> ('a,'b) pre_digraph \<Rightarrow> bool" where
  "induced_subgraph H G \<equiv> subgraph H G \<and> arcs H = {e \<in> arcs G. tail G e \<in> verts H \<and> head G e \<in> verts H}"

definition spanning :: "('a,'b) pre_digraph \<Rightarrow> ('a,'b) pre_digraph \<Rightarrow> bool" where
  "spanning H G \<equiv> subgraph H G \<and> verts G = verts H"

definition strongly_connected :: "('a,'b) pre_digraph \<Rightarrow> bool" where
  "strongly_connected G \<equiv> \<forall>u \<in> verts G. \<forall>v \<in> verts G. u \<rightarrow>\<^isup>*\<^bsub>G\<^esub> v"


text {*
  The following function computes underlying symmetric graph of a digraph
  and removes parallel arcs.
*}

definition mk_symmetric :: "('a,'b) pre_digraph \<Rightarrow> 'a pair_pre_digraph" where
  "mk_symmetric G \<equiv> \<lparr> pverts = verts G, parcs = \<Union>e\<in>arcs G. {(tail G e, head G e), (head G e, tail G e)}\<rparr>"

definition connected :: "('a,'b) pre_digraph \<Rightarrow> bool" where
  "connected G \<equiv> strongly_connected (mk_symmetric G)"

definition forest :: "('a,'b) pre_digraph \<Rightarrow> bool" where
  "forest G \<equiv> \<not>(\<exists>p. pre_digraph.cycle G p)"

definition tree :: "('a,'b) pre_digraph \<Rightarrow> bool" where
  "tree G \<equiv> connected G \<and> forest G"

definition spanning_tree :: "('a,'b) pre_digraph \<Rightarrow> ('a,'b) pre_digraph \<Rightarrow> bool" where
  "spanning_tree H G \<equiv> tree H \<and> spanning H G"

definition scc :: "('a,'b) pre_digraph \<Rightarrow> ('a,'b) pre_digraph \<Rightarrow> bool" where
  "scc H G \<equiv> induced_subgraph H G \<and> strongly_connected H
    \<and> \<not>(\<exists>H'. induced_subgraph H' G
      \<and> strongly_connected H' \<and> verts H \<subset> verts H')"

definition union :: "('a,'b) pre_digraph \<Rightarrow> ('a,'b) pre_digraph \<Rightarrow> ('a,'b) pre_digraph" where
  "union G H \<equiv> \<lparr> verts = verts G \<union> verts H, arcs = arcs G \<union> arcs H, tail = tail G, head = head G\<rparr>"

definition Union :: "('a,'b) pre_digraph set \<Rightarrow> ('a,'b) pre_digraph" where
  "Union gs = \<lparr> verts = (\<Union>G \<in> gs. verts G), arcs = (\<Union>G \<in> gs. arcs G),
    tail = tail (SOME G. G \<in> gs) , head = head (SOME G. G \<in> gs)  \<rparr>"



subsection {* Compatible Graphs *}

lemma compatible_tail:
  assumes "compatible G H" shows "tail G = tail H"
  using assms by (simp add: fun_eq_iff compatible_def)

lemma compatible_head:
  assumes "compatible G H" shows "head G = head H"
  using assms by (simp add: fun_eq_iff compatible_def)

lemma compatible_cas:
  assumes "compatible G H" shows "pre_digraph.cas G = pre_digraph.cas H"
proof (unfold fun_eq_iff, intro allI)
  fix u es v show "pre_digraph.cas G u es v = pre_digraph.cas H u es v"
    using assms
    by (induct es arbitrary: u)
       (simp_all add: pre_digraph.cas.simps compatible_head compatible_tail)
qed

lemma compatible_awalk_verts:
  assumes "compatible G H" shows "pre_digraph.awalk_verts G = pre_digraph.awalk_verts H"
proof (unfold fun_eq_iff, intro allI)
  fix u es show "pre_digraph.awalk_verts G u es = pre_digraph.awalk_verts H u es"
    using assms
    by (induct es arbitrary: u)
       (simp_all add: pre_digraph.awalk_verts.simps compatible_head compatible_tail)
qed

lemma compatibleI_with_proj[intro]:
  shows "compatible (with_proj G) (with_proj H)"
  by (auto simp: compatible_def)



subsection {* Basic lemmas *}

lemma (in graph) graph_symmetric:
  shows "(u,v) \<in> arcs_ends G \<Longrightarrow> (v,u) \<in> arcs_ends G"
  using assms sym_arcs by (auto simp add: symmetric_def sym_def)

lemma strongly_connectedI[intro]:
  assumes "\<And>u v. u \<in> verts G \<Longrightarrow> v \<in> verts G \<Longrightarrow> u \<rightarrow>\<^isup>*\<^bsub>G\<^esub> v"
  shows "strongly_connected G"
using assms by (simp add: strongly_connected_def)

lemma strongly_connectedE[elim]:
  assumes "strongly_connected G"
  assumes "(\<And>u v. u \<in> verts G \<and> v \<in> verts G \<Longrightarrow> u \<rightarrow>\<^isup>*\<^bsub>G\<^esub> v) \<Longrightarrow> P"
  shows "P"
using assms by (auto simp add: strongly_connected_def)

lemma subgraph_imp_subverts:
  assumes "subgraph H G"
  shows "verts H \<subseteq> verts G"
using assms by (simp add: subgraph_def)

lemma induced_imp_subgraph:
  assumes "induced_subgraph H G"
  shows "subgraph H G"
using assms by (simp add: induced_subgraph_def)

lemma scc_imp_induced:
  assumes "scc c G"
  shows "induced_subgraph c G"
using assms by (simp add: scc_def)

lemma spanning_tree_imp_tree[dest]:
  assumes "spanning_tree H G"
  shows "tree H"
using assms by (simp add: spanning_tree_def)

lemma tree_imp_connected[dest]:
  assumes "tree G"
  shows "connected G"
using assms by (simp add: tree_def)

lemma spanning_treeI[intro]:
  assumes "spanning H G"
  assumes "tree H"
  shows "spanning_tree H G"
using assms by (simp add: spanning_tree_def)

lemma spanning_treeE[elim]:
  assumes "spanning_tree H G"
  assumes "tree H \<and> spanning H G \<Longrightarrow> P"
  shows "P"
using assms by (simp add: spanning_tree_def)

lemma spanningE[elim]:
  assumes "spanning H G"
  assumes "subgraph H G \<and> verts G = verts H \<Longrightarrow> P"
  shows "P"
using assms by (simp add: spanning_def)

lemma sccI[intro]:
  assumes "induced_subgraph c G"
  assumes "strongly_connected c"
  assumes "\<not>(\<exists>c'. induced_subgraph c' G \<and> strongly_connected c' \<and>
    verts c \<subset> verts c')"
  shows "scc c G"
using assms by (auto simp add: scc_def)

lemma sccE[elim]:
  assumes "scc c G"
  assumes "induced_subgraph c G \<Longrightarrow> strongly_connected c \<Longrightarrow> \<not> (\<exists>d.
    induced_subgraph d G \<and> strongly_connected d \<and> verts c \<subset> verts d) \<Longrightarrow> P"
  shows "P"
using assms by (auto simp add: scc_def)

lemma subgraphI:
  assumes "verts H \<subseteq> verts G"
  assumes "arcs H \<subseteq> arcs G"
  assumes "compatible G H"
  assumes "wf_digraph H"
  shows "subgraph H G"
using assms by (auto simp add: subgraph_def)

lemma (in wf_digraph) subgraphI_rev[intro]:
  assumes "verts G \<subseteq> verts H" "arcs G \<subseteq> arcs H" "compatible H G" shows "subgraph G H"
  using assms by (rule subgraphI) unfold_locales

lemma subgraphE[elim]:
  assumes "subgraph H G"
  assumes "\<lbrakk>verts H \<subseteq> verts G; arcs H \<subseteq> arcs G; compatible G H; wf_digraph H\<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by (simp add: subgraph_def)

lemma induced_subgraphI[intro]:
  assumes "subgraph H G"
  assumes "arcs H = {e \<in> arcs G. tail G e \<in> verts H \<and> head G e \<in> verts H}"
  shows "induced_subgraph H G"
using assms unfolding induced_subgraph_def by safe

lemma induced_subgraphE[elim]:
  assumes "induced_subgraph H G"
  assumes "\<lbrakk>subgraph H G; arcs H = {e \<in> arcs G. tail G e \<in> verts H \<and> head G e \<in> verts H}\<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by (auto simp add: induced_subgraph_def)

lemma graph_union_case:
  assumes "u \<in> verts (union G H)"
  obtains (in_l) "u \<in> verts G" | (in_r) "u \<in> verts H"
using assms by (auto simp: union_def)

lemma pverts_mk_symmetric[simp]: "pverts (mk_symmetric G) = verts G"
  and parcs_mk_symmetric:
    "parcs (mk_symmetric G) = (\<Union>e\<in>arcs G. {(tail G e, head G e), (head G e, tail G e)})"
  by (auto simp: mk_symmetric_def arcs_ends_conv image_UN)

lemma arcs_ends_mono:
  assumes "subgraph H G"
  shows "arcs_ends H \<subseteq> arcs_ends G"
  using assms by (auto simp add: subgraph_def arcs_ends_conv compatible_tail compatible_head)



subsection {* The underlying symmetric graph of a digraph *}

lemma (in wf_digraph) wellformed_mk_symmetric[intro]: "pair_wf_digraph (mk_symmetric G)"
  by unfold_locales (auto simp: parcs_mk_symmetric)

lemma (in pseudo_digraph) pair_pseudo_digraph_mk_symmetric[intro]: "pair_pseudo_digraph (mk_symmetric G)"
proof -
  have "finite ((\<lambda>(a,b). (b,a)) ` arcs_ends G)" (is "finite ?X") by (auto simp: arcs_ends_conv)
  also have "?X = {(a, b). (b, a) \<in> arcs_ends G}" by auto
  finally have X: "finite ..." .
  then show ?thesis
    by unfold_locales (auto simp: mk_symmetric_def arcs_ends_conv)
qed

lemma (in digraph) digraph_mk_symmetric[intro]: "pair_digraph (mk_symmetric G)"
proof -
  have "finite ((\<lambda>(a,b). (b,a)) ` arcs_ends G)" (is "finite ?X") by (auto simp: arcs_ends_conv)
  also have "?X = {(a, b). (b, a) \<in> arcs_ends G}" by auto
  finally have "finite ..." .
  then show ?thesis
    by unfold_locales (auto simp: mk_symmetric_def arc_to_ends_def dest: no_loops)
qed

lemma (in wf_digraph) reachable_mk_symmetricI:
  assumes "u \<rightarrow>\<^isup>* v" shows "u \<rightarrow>\<^isup>*\<^bsub>mk_symmetric G\<^esub> v"
proof -
  have "arcs_ends G \<subseteq> parcs (mk_symmetric G)"
       "(u, v) \<in> rtrancl_on (pverts (mk_symmetric G)) (arcs_ends G)"
    using assms unfolding reachable_def by (auto simp: parcs_mk_symmetric)
  then show ?thesis unfolding reachable_def by (auto intro: rtrancl_on_mono)
qed

lemma (in wf_digraph) adj_mk_symmetric_eq:
  "symmetric G \<Longrightarrow> parcs (mk_symmetric G) = arcs_ends G"
  by (auto simp: parcs_mk_symmetric in_arcs_imp_in_arcs_ends arcs_ends_symmetric)

lemma (in wf_digraph) reachable_mk_symmetric_eq:
  assumes "symmetric G" shows "u \<rightarrow>\<^isup>*\<^bsub>mk_symmetric G\<^esub> v \<longleftrightarrow> u \<rightarrow>\<^isup>* v" (is "?L \<longleftrightarrow> ?R")
  using adj_mk_symmetric_eq[OF assms] unfolding reachable_def by auto

lemma (in wf_digraph) mk_symmetric_awalk_imp_awalk:
  assumes sym: "symmetric G"
  assumes walk: "pre_digraph.awalk (mk_symmetric G) u p v"
  obtains q where "awalk u q v"
proof -
  interpret S: pair_wf_digraph "mk_symmetric G" ..
  from walk have "u \<rightarrow>\<^isup>*\<^bsub>mk_symmetric G\<^esub> v"
    by (simp only: S.reachable_awalk) rule
  then have "u \<rightarrow>\<^isup>* v" by (simp only: reachable_mk_symmetric_eq[OF sym])
  then show ?thesis by (auto simp: reachable_awalk intro: that)
qed

lemma symmetric_mk_symmetric:
  "symmetric (mk_symmetric G)"
  by (auto simp: symmetric_def parcs_mk_symmetric intro: symI)



subsection {* Subgraphs and Induced Subgraphs *}

text {*
  The @{term digraph} and @{term pseudo_digraph} properties are preserved under
  the (inverse) subgraph relation
*}
lemma (in pseudo_digraph) pseudo_digraph_subgraph:
  assumes "subgraph H G" shows "pseudo_digraph H"
proof (intro_locales)
  from assms show "wf_digraph H" by auto

  have HG: "arcs H \<subseteq> arcs G" "verts H \<subseteq> verts G"
    using assms by auto
  then have "finite (verts H)" "finite (arcs H)"
    using finite_verts finite_arcs by (blast intro: finite_subset)+
  then show "pseudo_digraph_axioms H"
    by unfold_locales
qed

lemma (in digraph) digraph_subgraph:
  assumes "subgraph H G" shows "digraph H"
proof
  fix e assume e: "e \<in> arcs H"
  with assms show "tail H e \<in> verts H" "head H e \<in> verts H"
    by (auto simp: subgraph_def intro: wf_digraph.wellformed)
  from e and assms have "e \<in> arcs H \<inter> arcs G" by auto
  with assms show "tail H e \<noteq> head H e"
    using no_loops by (auto simp: subgraph_def compatible_def arc_to_ends_def)
next
  have "arcs H \<subseteq> arcs G" "verts H \<subseteq> verts G" using assms by auto
  then show "finite (arcs H)" "finite (verts H)"
    using finite_verts finite_arcs by (blast intro: finite_subset)+
next
  fix e1 e2 assume "e1 \<in> arcs H" "e2 \<in> arcs H"
    and eq: "arc_to_ends H e1 = arc_to_ends H e2"
  with assms have "e1 \<in> arcs H \<inter> arcs G" "e2 \<in> arcs H \<inter> arcs G"
    by auto
  with eq show "e1 = e2"
    using no_multi_arcs assms
    by (auto simp: subgraph_def compatible_def arc_to_ends_def)
qed

lemma (in pre_digraph) adj_mono:
  assumes "u \<rightarrow>\<^bsub>H\<^esub> v" "subgraph H G"
  shows "u \<rightarrow> v"
  using assms by (blast dest: arcs_ends_mono)

lemma (in pre_digraph) reachable_mono:
  assumes walk: "u \<rightarrow>\<^isup>*\<^bsub>H\<^esub> v" and sub: "subgraph H G"
  shows "u \<rightarrow>\<^isup>* v"
proof -
  have "verts H \<subseteq> verts G" using sub by auto
  with assms show ?thesis
    unfolding reachable_def by (metis arcs_ends_mono rtrancl_on_mono)
qed


text {*
  Arc walks and paths are preserved under the subgraph relation.
*}
lemma (in wf_digraph) subgraph_awalk_imp_awalk:
  assumes walk: "pre_digraph.awalk H u p v"
  assumes sub: "subgraph H G"
  shows "awalk u p v"
  using assms by (auto simp: pre_digraph.awalk_def compatible_cas)

lemma (in wf_digraph) subgraph_apath_imp_apath:
  assumes path: "pre_digraph.apath H u p v"
  assumes sub: "subgraph H G"
  shows "apath u p v"
  using assms unfolding pre_digraph.apath_def
  by (auto intro: subgraph_awalk_imp_awalk simp: compatible_awalk_verts)

lemma subgraph_mk_symmetric:
  assumes "subgraph H G"
  shows "subgraph (mk_symmetric H) (mk_symmetric G)"
proof (rule subgraphI)
  let ?wpms = "\<lambda>G. mk_symmetric G"
  from assms have "compatible G H" by auto
  with assms
  show "verts (?wpms H)  \<subseteq> verts (?wpms G)"
    and "arcs (?wpms H) \<subseteq> arcs (?wpms G)"
    by (auto simp: parcs_mk_symmetric compatible_head compatible_tail)
  show "compatible (?wpms G) (?wpms H)" by rule
  interpret G: pair_wf_digraph "mk_symmetric H"
    using assms by (auto intro: wf_digraph.wellformed_mk_symmetric)
  show "wf_digraph (?wpms H)"
    by unfold_locales
qed

lemma (in pseudo_digraph) subgraph_in_degree:
  assumes "subgraph H G"
  shows "in_degree H v \<le> in_degree G v"
proof -
  have "finite (in_arcs G v)" by auto
  moreover
  have "in_arcs H v \<subseteq> in_arcs G v"
    using assms by (auto simp: subgraph_def in_arcs_def compatible_head compatible_tail)
  ultimately
  show ?thesis unfolding in_degree_def by (rule card_mono)
qed

lemma (in wf_digraph) subgraph_cycle:
  assumes "subgraph H G" "pre_digraph.cycle H p " shows "cycle p"
proof -
  from assms have "compatible G H" by auto
  with assms show ?thesis
    by (auto simp: pre_digraph.cycle_def compatible_awalk_verts intro: subgraph_awalk_imp_awalk)
qed



subsection {* Induced subgraphs *}

lemma wf_digraphI_induced:
  assumes "induced_subgraph H G"
  shows "wf_digraph H"
proof -
  from assms have "compatible G H" by auto
  with assms show ?thesis by unfold_locales (auto simp: compatible_tail compatible_head)
qed

lemma (in digraph) digraphI_induced:
  assumes "induced_subgraph H G"
  shows "digraph H"
proof -
  interpret W: wf_digraph H using assms by (rule wf_digraphI_induced)
  from assms have "compatible G H" by auto
  from assms have arcs: "arcs H \<subseteq> arcs G" by blast
  show ?thesis
  proof
    from assms have "verts H \<subseteq> verts G" by blast
    then show "finite (verts H)" using finite_verts by (rule finite_subset)
  next
    from arcs show "finite (arcs H)" using finite_arcs by (rule finite_subset)
  next
    fix e assume "e \<in> arcs H"
    with arcs `compatible G H` show "tail H e \<noteq> head H e"
      by (auto dest: no_loops simp: compatible_tail[symmetric] compatible_head[symmetric])
  next
    fix e1 e2 assume "e1 \<in> arcs H" "e2 \<in> arcs H" and ate: "arc_to_ends H e1 = arc_to_ends H e2"
    with arcs `compatible G H` show "e1 = e2" using ate
      by (auto intro: no_multi_arcs simp: compatible_tail[symmetric] compatible_head[symmetric] arc_to_ends_def)
  qed
qed

text {* Computes the subgraph of @{term G} induced by @{term vs} *}
definition induce_subgraph :: "('a,'b) pre_digraph \<Rightarrow> 'a set \<Rightarrow> ('a,'b) pre_digraph" (infix "\<restriction>" 67) where
  "G \<restriction> vs = \<lparr> verts = vs, arcs = {e \<in> arcs G. tail G e \<in> vs \<and> head G e \<in> vs},
    tail = tail G, head = head G \<rparr>"

lemma induce_subgraph_verts[simp]:
 "verts (G \<restriction> vs) = vs"
by (auto simp add: induce_subgraph_def)

lemma induce_subgraph_arcs[simp]:
 "arcs (G \<restriction> vs) = {e \<in> arcs G. tail G e \<in> vs \<and> head G e \<in> vs}"
by (auto simp add: induce_subgraph_def)

lemma induce_subgraph_tail[simp]:
  "tail (G \<restriction> vs) = tail G"
by (auto simp: induce_subgraph_def)

lemma induce_subgraph_head[simp]:
  "head (G \<restriction> vs) = head G"
by (auto simp: induce_subgraph_def)

lemma induced_induce[intro]:
  assumes "vs \<subseteq> verts G"
  shows "induced_subgraph (G \<restriction> vs) G"
using assms
by (intro subgraphI induced_subgraphI)
   (auto simp: arc_to_ends_def induce_subgraph_def wf_digraph_def compatible_def)

lemma (in wf_digraph) wellformed_induce_subgraph[intro]:
  "wf_digraph (G \<restriction> vs)"
  by unfold_locales auto

lemma induced_graph_imp_symmetric:
  assumes "symmetric G"
  assumes "induced_subgraph H G"
  shows "symmetric H"
proof (unfold symmetric_conv, safe)
  from assms have "compatible G H" by auto

  fix e1 assume "e1 \<in> arcs H"
  then obtain e2 where "tail G e1 = head G e2"  "head G e1 = tail G e2" "e2 \<in> arcs G"
    using assms by (auto simp add: symmetric_conv)
  moreover
  then have "e2 \<in> arcs H"
    using assms and `e1 \<in> arcs H` by auto
  ultimately
  show "\<exists>e2\<in>arcs H. tail H e1 = head H e2 \<and> head H e1 = tail H e2"
    using assms `e1 \<in> arcs H` `compatible G H`
    by (auto simp: compatible_head compatible_tail)
qed

lemma (in graph) induced_graph_imp_graph:
  assumes "induced_subgraph H G"
  shows "graph H"
proof (rule digraph.graphI)
  from assms show "digraph H"
    by (blast intro: digraphI_induced)
next
  show "symmetric H"
    using assms sym_arcs by (auto intro: induced_graph_imp_symmetric)
qed

lemma (in wf_digraph) induce_reachable_preserves_paths:
  assumes "u \<rightarrow>\<^isup>*\<^bsub>G\<^esub> v"
  shows "u \<rightarrow>\<^isup>*\<^bsub>G \<restriction> {w. u \<rightarrow>\<^isup>*\<^bsub>G\<^esub> w}\<^esub> v"
  using assms
proof induct
  case base then show ?case by (auto simp: reachable_def)
next
  case (step u w)
  interpret iG: wf_digraph "G \<restriction> {w. u \<rightarrow>\<^isup>*\<^bsub>G\<^esub> w}"
    by (rule wellformed_induce_subgraph)
  from `u \<rightarrow> w` have "u \<rightarrow>\<^bsub>G \<restriction> {wa. u \<rightarrow>\<^isup>*\<^bsub>G\<^esub> wa}\<^esub> w"
    by (auto simp: arcs_ends_conv reachable_def intro: wellformed rtrancl_on_into_rtrancl_on)
  then have "u \<rightarrow>\<^isup>*\<^bsub>G \<restriction> {wa. u \<rightarrow>\<^isup>*\<^bsub>G\<^esub> wa}\<^esub> w"
    by (rule iG.reachable_adjI)
  moreover
  from step have "{x. w \<rightarrow>\<^isup>* x} \<subseteq> {x. u \<rightarrow>\<^isup>* x}"
    by (auto intro: adj_reachable_trans)
  then have "subgraph (G \<restriction> {wa. w \<rightarrow>\<^isup>* wa}) (G \<restriction> {wa. u \<rightarrow>\<^isup>* wa})"
    by (intro subgraphI) (auto simp: arcs_ends_conv compatible_def)
  then have "w \<rightarrow>\<^isup>*\<^bsub>G \<restriction> {wa. u \<rightarrow>\<^isup>* wa}\<^esub> v"
    by (rule iG.reachable_mono[rotated]) fact
  ultimately show ?case by (rule iG.reachable_trans)
qed



subsection {* Unions of Graphs *}

lemma wellformed_union:
  assumes "wf_digraph G" "wf_digraph H" "compatible G H"
  shows "wf_digraph (union G H)"
  using assms
  by unfold_locales
     (auto simp: union_def compatible_tail compatible_head dest: wf_digraph.wellformed)

lemma subgraph_union[intro]:
  assumes "subgraph H1 G" "compatible H1 G"
  assumes "subgraph H2 G" "compatible H2 G"
  shows "subgraph (union H1 H2) G"
proof -
  from assms have "wf_digraph (union H1 H2)"
    by (auto intro: wellformed_union simp: compatible_def)
  with assms show ?thesis
    by (auto simp add: subgraph_def union_def arc_to_ends_def compatible_def)
qed

lemma union_pseudo_digraph:
  assumes "pseudo_digraph G" "pseudo_digraph H" "compatible G H"
  shows "pseudo_digraph (union G H)"
proof intro_locales
  interpret G: pseudo_digraph G by (rule assms)
  interpret H: pseudo_digraph H by (rule assms)
  show "wf_digraph (union G H)" using assms
    by (intro wellformed_union) intro_locales
  show "pseudo_digraph_axioms (union G H)"
    using assms by unfold_locales (auto simp: union_def)
qed

lemma subgraphs_of_union:
  assumes "wf_digraph G" "wf_digraph G'" "compatible G G'"
  shows "subgraph G (union G G')"
    and "subgraph G' (union G G')"
using assms by (auto simp: union_def subgraph_def compatible_def)



subsection {* Connected and Strongly Connected Graphs*}

lemma connected_conv:
  shows "connected G \<longleftrightarrow> (\<forall>u \<in> verts G. \<forall>v \<in> verts G. (u,v) \<in> rtrancl_on (verts G) ((arcs_ends G)\<^sup>s))"
proof -
  have "symcl (arcs_ends G) = parcs (mk_symmetric G)"
    by (auto simp: parcs_mk_symmetric symcl_def arcs_ends_conv)
  then show ?thesis by (auto simp: connected_def strongly_connected_def reachable_def)
qed

lemma (in wf_digraph) strongly_connected_spanning_imp_strongly_connected:
  assumes "spanning H G"
  assumes "strongly_connected H"
  shows "strongly_connected G"
proof (unfold strongly_connected_def, (rule ballI)+)
  fix u v assume "u \<in> verts G" and "v \<in> verts G"
  then have "u \<rightarrow>\<^isup>*\<^bsub>H\<^esub> v" "subgraph H G"
    using assms by (auto simp add: strongly_connected_def)
  then show "u \<rightarrow>\<^isup>* v" by (rule reachable_mono)
qed

lemma (in wf_digraph) symmetric_connected_imp_strongly_connected:
  assumes "symmetric G" "connected G"
  shows "strongly_connected G"
proof
  from `connected G`
  have sc_mks: "strongly_connected (mk_symmetric G)"
    unfolding connected_def by simp

  fix u v assume "u \<in> verts G" "v \<in> verts G"
  with sc_mks have "u \<rightarrow>\<^isup>*\<^bsub>mk_symmetric G\<^esub> v"
    unfolding strongly_connected_def by auto
  then show "u \<rightarrow>\<^isup>* v" using assms by (simp only: reachable_mk_symmetric_eq)
qed

lemma (in wf_digraph) connected_spanning_imp_connected:
  assumes "spanning H G"
  assumes "connected H"
  shows "connected G"
proof (unfold connected_def strongly_connected_def, intro ballI)
  fix u v
  assume "u \<in> verts (mk_symmetric G)" and "v \<in> verts (mk_symmetric G)"
  then have "u \<in> pverts (mk_symmetric H)" and "v \<in> pverts (mk_symmetric H)"
    using `spanning H G` by (auto simp: mk_symmetric_def)
  with `connected H`
  have "u \<rightarrow>\<^isup>*\<^bsub>with_proj (mk_symmetric H)\<^esub> v" "subgraph (mk_symmetric H) (mk_symmetric G)"
    using `spanning H G` unfolding connected_def
    by (auto simp: spanning_def dest: subgraph_mk_symmetric)
  then show "u \<rightarrow>\<^isup>*\<^bsub>mk_symmetric G\<^esub> v" by (rule pre_digraph.reachable_mono)
qed

lemma (in wf_digraph) spanning_tree_imp_connected:
  assumes "spanning_tree H G"
  shows "connected G"
using assms by (auto intro: connected_spanning_imp_connected)

lemma (in graph) induce_reachable_is_scc:
  assumes "u \<in> verts G"
  shows "scc (G \<restriction> {v. u \<rightarrow>\<^isup>* v}) G"
proof -
  let ?c = "(G \<restriction> {v. u \<rightarrow>\<^isup>* v})"
  have isub_c: "induced_subgraph ?c G"
    by (auto elim: reachable_in_vertsE)
  then interpret c: digraph ?c by (rule digraphI_induced)

  have sym_c: "symmetric (G \<restriction> {v. u \<rightarrow>\<^isup>* v})"
    using sym_arcs isub_c by (rule induced_graph_imp_symmetric)

  note `induced_subgraph ?c G`
  moreover
  have "strongly_connected ?c"
  proof (rule strongly_connectedI)
    fix v w assume l_assms: "v \<in> verts ?c" "w \<in> verts ?c"
    have "u \<rightarrow>\<^isup>*\<^bsub>G \<restriction> {v. u \<rightarrow>\<^isup>* v}\<^esub> v"
      using l_assms by (intro induce_reachable_preserves_paths) auto
    then have "v \<rightarrow>\<^isup>*\<^bsub>G \<restriction> {v. u \<rightarrow>\<^isup>* v}\<^esub> u" by (rule symmetric_reachable[OF sym_c])
    also have "u \<rightarrow>\<^isup>*\<^bsub>G \<restriction> {v. u \<rightarrow>\<^isup>* v}\<^esub> w"
      using l_assms by (intro induce_reachable_preserves_paths) auto
    finally show "v \<rightarrow>\<^isup>*\<^bsub>G \<restriction> {v. u \<rightarrow>\<^isup>* v}\<^esub> w" .
  qed
  moreover
  have "\<not>(\<exists>d. induced_subgraph d G \<and> strongly_connected d \<and>
    verts ?c \<subset> verts d)"
  proof
    assume "\<exists>d. induced_subgraph d G \<and> strongly_connected d \<and>
      verts ?c \<subset> verts d"
    then obtain d where "induced_subgraph d G" "strongly_connected d"
      "verts ?c \<subset> verts d" by auto
    then obtain v where "v \<in> verts d" and "v \<notin> verts ?c"
      by auto

    have "u \<in> verts ?c" using `u \<in> verts G` by auto
    then have "u \<in> verts d" using `verts ?c \<subset> verts d` by auto 
    then have "u \<rightarrow>\<^isup>*\<^bsub>d\<^esub> v"
      using `strongly_connected d` `u \<in> verts d` `v \<in> verts d` by auto
    then have "u \<rightarrow>\<^isup>* v"
      using `induced_subgraph d G`
      by (auto intro: pre_digraph.reachable_mono)
    then have "v \<in> verts ?c" by (auto simp: reachable_awalk)
    then show False using `v \<notin> verts ?c` by auto
  qed
  ultimately show ?thesis unfolding scc_def by auto   
qed

lemma induced_eq_verts_imp_eq:
  assumes "induced_subgraph G H"
  assumes "induced_subgraph G' H"
  assumes "verts G = verts G'"
  shows "G = G'"
  using assms by (auto simp: induced_subgraph_def subgraph_def compatible_def)

lemma scc_subset_imp_eq:
  assumes "scc c G"
  assumes "scc d G"
  assumes "verts c \<subseteq> verts d"
  shows "c = d"
using assms by (blast intro: induced_eq_verts_imp_eq)

lemma (in wf_digraph) strongly_connected_imp_induce_subgraph_strongly_connected:
  assumes subg: "subgraph H G"
  assumes sc: "strongly_connected H"
  shows "strongly_connected (G \<restriction> (verts H))"
proof -
  let ?is_H = "G \<restriction> (verts H)"

  interpret H: wf_digraph H
    using subg by (rule subgraphE)
  interpret GrH: wf_digraph "?is_H"
    by (rule wellformed_induce_subgraph)

  have "verts H \<subseteq> verts G" using assms by auto

  have "subgraph H (G \<restriction> verts H)"
    unfolding induce_subgraph_def using subg
    by (auto simp: subgraph_def compatible_def)
  then show ?thesis
    using induced_induce[OF `verts H \<subseteq> verts G`]
      and sc GrH.strongly_connected_spanning_imp_strongly_connected
    unfolding spanning_def by auto
qed

lemma (in wf_digraph) connectedI:
  assumes "\<And>u v. u \<in> verts G \<Longrightarrow> v \<in> verts G \<Longrightarrow> u \<rightarrow>\<^isup>*\<^bsub>mk_symmetric G\<^esub> v"
  shows "connected G"
  using assms by (auto simp: connected_def)

lemma (in wf_digraph) connected_awalkE:
  assumes "connected G" "u \<in> verts G" "v \<in> verts G"
  obtains p where "pre_digraph.awalk (mk_symmetric G) u p v"
proof -
  interpret sG: pair_wf_digraph "mk_symmetric G" ..
  from assms have "u \<rightarrow>\<^isup>*\<^bsub>mk_symmetric G\<^esub> v" by (auto simp: connected_def)
  then obtain p where "sG.awalk u p v" by (auto simp: sG.reachable_awalk)
  then show ?thesis ..
qed



subsection {* Components *}

lemma (in graph) exists_scc:
  shows "\<exists>c. scc c G"
proof cases
  assume "verts G = {}"
  moreover then have "arcs G = {}" by (metis all_not_in_conv head_in_verts)
  ultimately have "scc G G"
    by (auto simp: scc_def induced_subgraph_def subgraph_def compatible_def) unfold_locales
  then show ?thesis ..
next
  assume "verts G \<noteq> {}"
  then obtain u where "u \<in> verts G" by auto
  then show ?thesis by (blast dest: induce_reachable_is_scc)
qed

theorem (in graph) graph_is_union_sccs:
  shows "Union {c. scc c G} = G"
proof -
  have "(\<Union>c \<in> {c. scc c G}. verts c) = verts G"
    using assms by (auto intro:  induce_reachable_is_scc)
  moreover
  have "(\<Union>c \<in> {c. scc c G}. arcs c) = arcs G"
  proof
    show "(\<Union>c \<in> {c. scc c G}. arcs c) \<subseteq> arcs G"
      by safe (metis sccE induced_imp_subgraph subgraphE subsetD)
    show "arcs G \<subseteq> (\<Union>c \<in> {c. scc c G}. arcs c)"
    proof (safe)
      fix e assume "e \<in> arcs G"
      def a \<equiv> "tail G e" and b \<equiv> "head G e"
      note a_def[simp] b_def[simp]

      have "e \<in> (\<Union>x \<in> {c. scc c G}. arcs x)"
      proof cases
        assume "\<exists>x. scc x G \<and> {a,b } \<subseteq> verts x"
        then obtain c where "scc c G" and "{a,b} \<subseteq> verts c"
          by auto
        then have "e \<in> {e \<in> arcs G. tail G e \<in> verts c
          \<and> head G e \<in> verts c}" using `e \<in> arcs G` by auto
        then have "e \<in> arcs c" using `scc c G` by blast
        then show ?thesis using `scc c G` by auto
      next
        assume l_assm: "\<not>(\<exists>x. scc x G \<and> {a,b} \<subseteq> verts x)"

        have "a \<rightarrow>\<^isup>* b" using `e \<in> arcs G` 
          by (metis a_def b_def reachable_adjI in_arcs_imp_in_arcs_ends)
        then have "{a,b} \<subseteq> verts (G \<restriction> {v. a \<rightarrow>\<^isup>* v})" "a \<in> verts G"
          by (auto elim: reachable_in_vertsE)
        moreover
        have "scc (G \<restriction> {v. a \<rightarrow>\<^isup>* v}) G"
          using `a \<in> verts G` by (auto intro: induce_reachable_is_scc)
        ultimately
        have False using l_assm by blast
        then show ?thesis by simp
      qed
      then show "e \<in> (\<Union>c \<in> {c. scc c G}. arcs c)" by auto
    qed
  qed
  moreover
  { obtain c where scc: "scc c G" using exists_scc ..
    { fix c assume "scc c G"
      then have "compatible G c" by (auto simp: scc_def)
      then have "tail c = tail G" "head c = head G" by (auto simp: compatible_def) }
    note ends = this
    from scc ends(1) have t: "tail (SOME c. scc c G) = tail G"
      by (rule someI2[where a=c])
    from scc ends(2) have h: "head (SOME c. scc c G) = head G"
      by (rule someI2[where a=c])
    note t h }
  moreover
  ultimately show ?thesis
    by (auto simp add: Union_def)
qed

lemma (in graph) scc_for_vert_ex:
  assumes "u \<in> verts G"
  shows "\<exists>c. scc c G \<and> u \<in> verts c"
using assms by (auto intro: induce_reachable_is_scc)

lemma strongly_connected_non_disj:
  assumes wf: "wf_digraph G" "wf_digraph H" "compatible G H"
  assumes sc: "strongly_connected G" "strongly_connected H"
  assumes not_disj: "verts G \<inter> verts H \<noteq> {}"
  shows "strongly_connected (union G H)"
proof
  let ?x = "union G H"
  fix u v w assume "u \<in> verts ?x" and "v \<in> verts ?x"
  obtain w where w_in_both: "w \<in> verts G" "w \<in> verts H"
    using not_disj by auto

  interpret x: wf_digraph ?x
    by (rule wellformed_union) fact+
  have subg: "subgraph G ?x" "subgraph H ?x"
    by (rule subgraphs_of_union[OF _ _ ], fact+)+
  have reach_uw: "u \<rightarrow>\<^isup>*\<^bsub>?x\<^esub> w"
    using `u \<in> verts ?x` subg w_in_both sc
    by (cases rule: graph_union_case) (auto intro: pre_digraph.reachable_mono)
  also have reach_wv: "w \<rightarrow>\<^isup>*\<^bsub>?x\<^esub> v"
    using `v \<in> verts ?x` subg w_in_both sc
    by (cases rule: graph_union_case) (auto intro: pre_digraph.reachable_mono)
  finally (x.reachable_trans) show "u \<rightarrow>\<^isup>*\<^bsub>?x\<^esub> v" .
qed

lemma (in wf_digraph) scc_disj:
  assumes scc: "scc c G" "scc d G"
  assumes "c \<noteq> d"
  shows "verts c \<inter> verts d = {}"
proof (rule ccontr)
  assume contr: "\<not>?thesis"

  let ?x = "union c d"

  have comp1: "compatible G c" "compatible G d"
    using scc by (auto simp: scc_def)
  then have comp: "compatible c d" by (auto simp: compatible_def)

  have wf: "wf_digraph c" "wf_digraph d"
    and sc: "strongly_connected c" "strongly_connected d"
    using scc by (auto intro: scc_imp_induced)
  have "compatible c d"
    using comp by (auto simp: scc_def compatible_def)
  from wf comp sc have union_conn: "strongly_connected ?x"
    using contr by (rule strongly_connected_non_disj)

  have sg: "subgraph ?x G"
    using scc comp1 by (intro subgraph_union) (auto simp: compatible_def)
  have "wf_digraph ?x" by (rule wellformed_union) fact+
  with sg union_conn
  have induce_subgraph_conn: "strongly_connected (G \<restriction> verts ?x)"
      "induced_subgraph (G \<restriction> verts ?x) G"
    by (auto intro: strongly_connected_imp_induce_subgraph_strongly_connected )

  from assms have "\<not>verts c \<subseteq> verts d" and "\<not> verts d \<subseteq> verts c"
    by (metis scc_subset_imp_eq)+
  then have psub: "verts c \<subset> verts ?x"
    by (auto simp: union_def)
  then show False using induce_subgraph_conn
    by (metis `scc c G` sccE induce_subgraph_verts)
qed

end
