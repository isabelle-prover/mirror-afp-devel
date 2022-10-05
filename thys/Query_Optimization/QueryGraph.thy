(* Author: Bernhard Stöckl *)

theory QueryGraph
  imports Complex_Main "Graph_Additions" "Selectivities" "JoinTree"
begin

section \<open>Query Graphs\<close>

locale query_graph = graph +
  fixes sel :: "'b weight_fun"
  fixes cf :: "'a \<Rightarrow> real"
  assumes sel_sym: "\<lbrakk>tail G e\<^sub>1 = head G e\<^sub>2; head G e\<^sub>1 = tail G e\<^sub>2\<rbrakk> \<Longrightarrow> sel e\<^sub>1 = sel e\<^sub>2"
      and not_arc_sel_1: "e \<notin> arcs G \<Longrightarrow> sel e = 1"
      and sel_pos: "sel e > 0"
      and sel_leq_1: "sel e \<le> 1"
      and pos_cards: "x \<in> verts G \<Longrightarrow> cf x > 0"

begin

subsection \<open>Function for Join Trees and Selectivities\<close>

definition matching_sel :: "'a selectivity \<Rightarrow> bool" where
  "matching_sel f = (\<forall>x y.
      (\<exists>e. (tail G e) = x \<and> (head G e) = y \<and> f x y = sel e)
    \<or> ((\<nexists>e. (tail G e) = x \<and> (head G e) = y) \<and> f x y = 1))"

definition match_sel :: "'a selectivity" where
  "match_sel x y =
    (if \<exists>e \<in> arcs G. (tail G e) = x \<and> (head G e) = y
    then sel (THE e. e \<in> arcs G \<and> (tail G e) = x \<and> (head G e) = y) else 1)"

definition matching_rels :: "'a joinTree \<Rightarrow> bool" where
  "matching_rels t = (relations t \<subseteq> verts G)"

definition remove_sel :: "'a \<Rightarrow> 'b weight_fun" where
  "remove_sel x = (\<lambda>b. if b\<in>{a \<in> arcs G. tail G a = x \<or> head G a = x} then 1 else sel b)"

definition valid_tree :: "'a joinTree \<Rightarrow> bool" where
  "valid_tree t = (relations t = verts G \<and> distinct_relations t)"

fun no_cross_products :: "'a joinTree \<Rightarrow> bool" where
  "no_cross_products (Relation rel) = True"
| "no_cross_products (Join l r) = ((\<exists>x\<in>relations l. \<exists>y\<in>relations r. x \<rightarrow>\<^bsub>G\<^esub> y)
    \<and> no_cross_products l \<and> no_cross_products r)"

subsection "Proofs"

text \<open>
  Proofs that a query graph satisifies basic properties of join trees and selectivities.
\<close>

lemma sel_less_arc: "sel x < 1 \<Longrightarrow> x \<in> arcs G"
  using not_arc_sel_1 by force

lemma joinTree_card_pos: "matching_rels t \<Longrightarrow> pos_rel_cards cf t"
  by(induction t) (auto simp: pos_cards pos_rel_cards_def matching_rels_def)

lemma symmetric_arcs: "x\<in>arcs G \<Longrightarrow> \<exists>y. head G x = tail G y \<and> tail G x = head G y"
  using sym_arcs symmetric_conv by fast

lemma arc_ends_eq_impl_sel_eq: "head G x = head G y \<Longrightarrow> tail G x = tail G y \<Longrightarrow> sel x = sel y"
  using sel_sym symmetric_arcs not_arc_sel_1 by metis

lemma arc_ends_eq_impl_arc_eq:
  "\<lbrakk>e1 \<in> arcs G; e2 \<in> arcs G; head G e1 = head G e2; tail G e1 = tail G e2\<rbrakk> \<Longrightarrow> e1 = e2"
  using no_multi_alt by blast

lemma matching_sel_simp_if_not1:
  "\<lbrakk>matching_sel sf; sf x y \<noteq> 1\<rbrakk> \<Longrightarrow> \<exists>e \<in> arcs G. tail G e = x \<and> head G e = y \<and> sf x y = sel e"
  using not_arc_sel_1 unfolding matching_sel_def by fastforce

lemma matching_sel_simp_if_arc:
  "\<lbrakk>matching_sel sf; e \<in> arcs G\<rbrakk> \<Longrightarrow> sf (tail G e) (head G e) = sel e"
  unfolding matching_sel_def by (metis arc_ends_eq_impl_sel_eq)

lemma matching_sel1_if_no_arc: "matching_sel sf \<Longrightarrow> \<not>(x \<rightarrow>\<^bsub>G\<^esub> y \<or> y \<rightarrow>\<^bsub>G\<^esub> x) \<Longrightarrow> sf x y = 1"
  using not_arc_sel_1 unfolding arcs_ends_def arc_to_ends_def matching_sel_def image_iff by metis

lemma matching_sel_alt_aux1:
  "matching_sel f
    \<Longrightarrow> (\<forall>x y. (\<exists>e \<in> arcs G. (tail G e) = x \<and> (head G e) = y \<and> f x y = sel e)
            \<or> ((\<nexists>e. e \<in> arcs G \<and> (tail G e) = x \<and> (head G e) = y) \<and> f x y = 1))"
  by (metis matching_sel_def arc_ends_eq_impl_sel_eq not_arc_sel_1)

lemma matching_sel_alt_aux2:
  "(\<forall>x y.(\<exists>e \<in> arcs G. (tail G e) = x \<and> (head G e) = y \<and> f x y = sel e)
      \<or> ((\<nexists>e. e \<in> arcs G \<and> (tail G e) = x \<and> (head G e) = y) \<and> f x y = 1))
    \<Longrightarrow> matching_sel f"
  by (fastforce simp: not_arc_sel_1 matching_sel_def)

lemma matching_sel_alt:
  "matching_sel f
    = (\<forall>x y. (\<exists>e \<in> arcs G. (tail G e) = x \<and> (head G e) = y \<and> f x y = sel e)
          \<or> ((\<nexists>e. e \<in> arcs G \<and> (tail G e) = x \<and> (head G e) = y) \<and> f x y = 1))"
  using matching_sel_alt_aux1 matching_sel_alt_aux2 by blast

lemma matching_sel_symm:
  assumes "matching_sel f"
  shows "sel_symm f"
  unfolding sel_symm_def
proof (standard, standard)
  fix x y
  show "f x y = f y x"
  proof(cases "\<exists>e\<in>arcs G. (head G e) = x \<and> (tail G e) = y")
    case True
    then show ?thesis using assms symmetric_arcs sel_sym unfolding matching_sel_def by metis
  next
    case False
    then show ?thesis by (metis assms symmetric_arcs matching_sel_def not_arc_sel_1 sel_sym)
  qed
qed

lemma matching_sel_reasonable: "matching_sel f \<Longrightarrow> sel_reasonable f"
  using sel_reasonable_def matching_sel_def sel_pos sel_leq_1
  by (metis le_numeral_extra(4) less_numeral_extra(1))

lemma matching_reasonable_cards:
  "\<lbrakk>matching_sel f; matching_rels t\<rbrakk> \<Longrightarrow> reasonable_cards cf f t"
  by (simp add: joinTree_card_pos matching_sel_reasonable pos_sel_reason_impl_reason)

lemma matching_sel_unique_aux:
  assumes "matching_sel f" "matching_sel g"
  shows "f x y = g x y"
proof(cases "\<exists>e. tail G e = x \<and> head G e = y")
  case True
  then show ?thesis
    using assms arc_ends_eq_impl_sel_eq unfolding matching_sel_def by metis
next
  case False
  then show ?thesis using assms unfolding matching_sel_def by fastforce
qed

lemma matching_sel_unique: "\<lbrakk>matching_sel f; matching_sel g\<rbrakk> \<Longrightarrow> f = g"
  using matching_sel_unique_aux by blast

lemma match_sel_matching[intro]: "matching_sel match_sel"
  unfolding matching_sel_alt
proof(standard,standard)
  fix x y
  show "(\<exists>e\<in>arcs G. tail G e = x \<and> head G e = y \<and> match_sel x y = sel e) \<or>
          ((\<nexists>e. e \<in> arcs G \<and> tail G e = x \<and> head G e = y) \<and> match_sel x y = 1)"
  proof(cases "\<exists>e \<in> arcs G. tail G e = x \<and> head G e = y")
    case True
    then obtain e where e_def: "e \<in> arcs G" "tail G e = x" "head G e = y" by blast
    then have "match_sel x y = sel (THE e. e \<in> arcs G \<and> tail G e = x \<and> head G e = y)"
      unfolding match_sel_def by auto
    moreover have "(THE e. e \<in> arcs G \<and> tail G e = x \<and> head G e = y) = e"
      using e_def arc_ends_eq_impl_arc_eq by blast
    ultimately show ?thesis using e_def by blast
  next
    case False
    then show ?thesis unfolding match_sel_def by auto
  qed
qed

corollary match_sel_unique: "matching_sel f \<Longrightarrow> f = match_sel"
  using matching_sel_unique by blast

corollary match_sel1_if_no_arc: "\<not>(x \<rightarrow>\<^bsub>G\<^esub> y \<or> y \<rightarrow>\<^bsub>G\<^esub> x) \<Longrightarrow> match_sel x y = 1"
  using matching_sel1_if_no_arc by blast

corollary match_sel_symm[intro]: "sel_symm match_sel"
  using matching_sel_symm by blast

corollary match_sel_reasonable[intro]: "sel_reasonable match_sel"
  using matching_sel_reasonable by blast

corollary match_reasonable_cards: "matching_rels t \<Longrightarrow> reasonable_cards cf match_sel t"
  using matching_reasonable_cards by blast

lemma matching_rels_trans: "matching_rels (Join l r) = (matching_rels l \<and> matching_rels r)"
  using matching_rels_def by simp

lemma first_node_in_verts_if_rels_eq_verts: "relations t = verts G \<Longrightarrow> first_node t \<in> verts G"
  unfolding first_node_eq_hd using inorder_eq_set hd_in_set[OF inorder_nempty] by fast

lemma first_node_in_verts_if_valid: "valid_tree t \<Longrightarrow> first_node t \<in> verts G"
  using first_node_in_verts_if_rels_eq_verts valid_tree_def by simp

lemma dominates_sym: "(x \<rightarrow>\<^bsub>G\<^esub> y) \<longleftrightarrow> (y \<rightarrow>\<^bsub>G\<^esub> x)"
  using graph_symmetric by blast

lemma no_cross_mirror_eq: "no_cross_products (mirror t) = no_cross_products t"
  using graph_symmetric by(induction t) auto

lemma no_cross_create_ldeep_rev_app:
  "\<lbrakk>ys\<noteq>[]; no_cross_products (create_ldeep_rev (xs@ys))\<rbrakk> \<Longrightarrow> no_cross_products (create_ldeep_rev ys)"
proof(induction "xs@ys" arbitrary: xs rule: create_ldeep_rev.induct)
  case (2 x)
  then show ?case by (metis append_eq_Cons_conv append_is_Nil_conv)
next
  case (3 x y zs)
  then show ?case
  proof(cases xs)
    case Nil
    then show ?thesis using "3.prems"(2) by simp
  next
    case (Cons x' xs')
    have "no_cross_products (Join (create_ldeep_rev (y#zs)) (Relation x))"
      using "3.hyps"(2) "3.prems"(2) create_ldeep_rev.simps(3)[of x y zs] by simp
    then have "no_cross_products (create_ldeep_rev (y#zs))" by simp
    then show ?thesis using "3.hyps" "3.prems"(1) Cons by simp
  qed
qed(simp)

lemma no_cross_create_ldeep_app:
  "\<lbrakk>xs\<noteq>[]; no_cross_products (create_ldeep (xs@ys))\<rbrakk> \<Longrightarrow> no_cross_products (create_ldeep xs)"
  by (simp add: create_ldeep_def no_cross_create_ldeep_rev_app)

lemma matching_rels_if_no_cross: "\<lbrakk>\<forall>r. t \<noteq> Relation r; no_cross_products t\<rbrakk> \<Longrightarrow> matching_rels t"
  unfolding matching_rels_def by(induction t) fastforce+

lemma no_cross_awalk:
  "\<lbrakk>matching_rels t; no_cross_products t; x \<in> relations t; y \<in> relations t\<rbrakk>
    \<Longrightarrow> \<exists>p. awalk x p y \<and> set (awalk_verts x p) \<subseteq> relations t"
proof(induction t arbitrary: x y)
  case (Relation rel)
  then have "x \<in> verts G" using matching_rels_def by blast
  then have "awalk x [] x" by (simp add: awalk_Nil_iff)
  then show ?case using Relation(3,4) by force
next
  case (Join l r)
  then consider "x \<in> relations l" "y \<in> relations l" | "x \<in> relations r" "y \<in> relations l"
    | "x \<in> relations l" "y \<in> relations r" | "x \<in> relations r" "y \<in> relations r"
    by force
  then show ?case
  proof(cases)
    case 1
    then show ?thesis using Join.IH(1)[of x y] Join.prems(1,2) matching_rels_trans by auto
  next
    case 2
    then obtain x' y' e where e_def:
        "x' \<in> relations r" "y' \<in> relations l" "tail G e = y'" "head G e = x'" "e \<in> arcs G"
      using Join.prems(2) by auto
    then obtain e2 where e2_def: "tail G e2 = x'" "head G e2 = y'" "e2 \<in> arcs G"
      using symmetric_conv by force
    obtain p1 where p1_def: "awalk y' p1 y \<and> set (awalk_verts y' p1) \<subseteq> relations l"
      using Join.IH(1) Join.prems(1,2) 2(2) matching_rels_trans e_def(2) by fastforce
    obtain p2 where p2_def: "awalk x p2 x' \<and> set (awalk_verts x p2) \<subseteq> relations r"
      using Join.IH(2) Join.prems(1,2) 2(1) matching_rels_trans e_def(1) by fastforce
    have "awalk x (p2@[e2]@p1) y"
      using e2_def p1_def p2_def awalk_appendI arc_implies_awalk by blast
    moreover from this have "set (awalk_verts x (p2@[e2]@p1)) \<subseteq> relations (Join l r)"
      using p1_def p2_def awalk_verts_append3 by auto
    ultimately show ?thesis by blast
  next
    case 3
    then obtain x' y' e where e_def:
        "x' \<in> relations l" "y' \<in> relations r" "tail G e = x'" "head G e = y'" "e \<in> arcs G"
      using Join.prems(2) by auto
    obtain p1 where p1_def: "awalk y' p1 y \<and> set (awalk_verts y' p1) \<subseteq> relations r"
      using Join.IH(2) Join.prems(1,2) 3(2) matching_rels_trans e_def(2) by fastforce
    obtain p2 where p2_def: "awalk x p2 x' \<and> set (awalk_verts x p2) \<subseteq> relations l"
      using Join.IH(1) Join.prems(1,2) 3(1) matching_rels_trans e_def(1) by fastforce
    have "awalk x (p2@[e]@p1) y"
      using e_def(3-5) p1_def p2_def awalk_appendI arc_implies_awalk by blast
    moreover from this have "set (awalk_verts x (p2@[e]@p1)) \<subseteq> relations (Join l r)"
      using p1_def p2_def awalk_verts_append3 by auto
    ultimately show ?thesis by blast
  next
    case 4
    then show ?thesis using Join.IH(2)[of x y] Join.prems(1,2) matching_rels_trans by auto
  qed
qed

lemma no_cross_apath:
  "\<lbrakk>matching_rels t; no_cross_products t; x \<in> relations t; y \<in> relations t\<rbrakk>
    \<Longrightarrow> \<exists>p. apath x p y \<and> set (awalk_verts x p) \<subseteq> relations t"
  using no_cross_awalk apath_awalk_to_apath awalk_to_apath_verts_subset by blast

lemma no_cross_reachable:
  "\<lbrakk>matching_rels t; no_cross_products t; x \<in> relations t; y \<in> relations t\<rbrakk> \<Longrightarrow> x \<rightarrow>\<^sup>* y"
  using no_cross_awalk reachable_awalk by blast

corollary reachable_if_no_cross:
  "\<lbrakk>\<exists>t. relations t = verts G \<and> no_cross_products t; x \<in> verts G; y \<in> verts G\<rbrakk> \<Longrightarrow> x \<rightarrow>\<^sup>* y"
  using no_cross_reachable matching_rels_def by blast

lemma remove_sel_sym:
  "\<lbrakk>tail G e\<^sub>1 = head G e\<^sub>2; head G e\<^sub>1 = tail G e\<^sub>2\<rbrakk> \<Longrightarrow> (remove_sel x) e\<^sub>1 = (remove_sel x) e\<^sub>2"
  by(metis (no_types, lifting) mem_Collect_eq not_arc_sel_1 remove_sel_def sel_sym)+

lemma remove_sel_1: "e \<notin> arcs G \<Longrightarrow> (remove_sel x) e = 1"
  apply(cases "e\<in>{a \<in> arcs G. tail G a = x \<or> head G a = x}")
  by(auto simp: not_arc_sel_1 sel_sym remove_sel_def)

lemma del_vert_remove_sel_1:
  assumes "e \<notin> arcs ((del_vert x))"
  shows "(remove_sel x) e = 1"
proof(cases "e\<in>{a \<in> arcs G. tail G a = x \<or> head G a = x}")
  case True
  then show ?thesis by (simp add: remove_sel_def)
next
  case False
  then have "e \<notin> arcs G" using assms arcs_del_vert by simp
  then show ?thesis using remove_sel_def not_arc_sel_1 by simp
qed

lemma remove_sel_pos: "remove_sel x e > 0"
  by(cases "e\<in>{a \<in> arcs G. tail G a = x \<or> head G a = x}") (auto simp: remove_sel_def sel_pos)

lemma remove_sel_leq_1: "remove_sel x e \<le> 1"
  by(cases "e\<in>{a \<in> arcs G. tail G a = x \<or> head G a = x}") (auto simp: remove_sel_def sel_leq_1)

lemma del_vert_pos_cards: "x \<in> verts (del_vert y) \<Longrightarrow> cf x > 0"
  by(cases "x=y") (auto simp: remove_sel_def del_vert_def pos_cards)

lemma del_vert_remove_sel_query_graph:
  "query_graph G sel cf \<Longrightarrow> query_graph (del_vert x) (remove_sel x) cf"
  by (simp add: del_vert_pos_cards del_vert_remove_sel_1 graph_del_vert remove_sel_sym
      remove_sel_leq_1 remove_sel_pos query_graph.intro graph_axioms head_del_vert
      query_graph_axioms_def tail_del_vert)

lemma finite_nempty_set_min:
  assumes "xs \<noteq> {}" and "finite xs"
  shows "\<exists>x. min_degree xs x"
proof -
  have "finite xs" using assms(2) by simp
  then show ?thesis
  using assms proof (induction "xs" rule: finite_induct)
    case empty
    then show ?case by simp
  next
    case ind: (insert x xs)
    then show ?case
    proof(cases xs)
      case emptyI
      then show ?thesis by (metis order_refl singletonD singletonI)
    next
      case (insertI xs' x')
      then have "\<exists>a. min_degree xs a" using ind by simp
      then show ?thesis
        using ind by (metis order_trans insert_iff le_cases)
    qed
  qed
qed

lemma no_cross_reachable_graph':
  "\<lbrakk>\<exists>t. relations t = verts G \<and> no_cross_products t; x\<in>verts G; y\<in>verts G\<rbrakk>
    \<Longrightarrow> x \<rightarrow>\<^sup>*\<^bsub>mk_symmetric G\<^esub> y"
  by (simp add: reachable_mk_symmetricI reachable_if_no_cross)

lemma verts_nempty_if_tree: "\<exists>t. relations t \<subseteq> verts G \<Longrightarrow> verts G \<noteq> {}"
  using relations_nempty by fast

lemma connected_if_tree: "\<exists>t. relations t = verts G \<and> no_cross_products t \<Longrightarrow> connected G"
  using no_cross_reachable_graph' connected_def strongly_connected_def verts_nempty_if_tree
  by fastforce

end

locale nempty_query_graph = query_graph +
  assumes non_empty: "verts G \<noteq> {}"

subsection \<open>Pair Query Graph\<close>

text \<open>Alternative definition based on pair graphs\<close>

locale pair_query_graph = pair_graph +
  fixes sel :: "('a \<times> 'a) weight_fun"
  fixes cf :: "'a \<Rightarrow> real"
  assumes sel_sym: "\<lbrakk>tail G e\<^sub>1 = head G e\<^sub>2; head G e\<^sub>1 = tail G e\<^sub>2\<rbrakk> \<Longrightarrow> sel e\<^sub>1 = sel e\<^sub>2"
      and not_arc_sel_1: "e \<notin> parcs G \<Longrightarrow> sel e = 1"
      and sel_pos: "sel e > 0"
      and sel_leq_1: "sel e \<le> 1"
      and pos_cards: "x \<in> pverts G \<Longrightarrow> cf x > 0"

sublocale pair_query_graph \<subseteq> query_graph
  by(unfold_locales) (auto simp: sel_sym not_arc_sel_1 sel_pos sel_leq_1 pos_cards)

context pair_query_graph
begin

lemma "matching_sel f \<longleftrightarrow> (\<forall>x y. sel (x,y) = f x y)"
  using matching_sel_def sel_sym by fastforce

end

end