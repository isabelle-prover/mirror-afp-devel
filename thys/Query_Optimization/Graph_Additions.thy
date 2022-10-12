(* Author: Bernhard Stöckl *)

theory Graph_Additions
  imports Complex_Main "Graph_Theory.Graph_Theory" "Shortest_Path_Tree"
begin

lemma two_elems_card_ge_2: "finite xs \<Longrightarrow> x \<in> xs \<and> y \<in> xs \<and> x\<noteq>y \<Longrightarrow> Finite_Set.card xs \<ge> 2"
  using card_gt_0_iff mk_disjoint_insert not_less_eq_eq by fastforce

section \<open>Graph Extensions\<close>

context wf_digraph
begin

lemma awalk_dom_if_uneq: "\<lbrakk>u\<noteq>v; awalk u p v\<rbrakk> \<Longrightarrow> \<exists>x. x \<rightarrow>\<^bsub>G\<^esub> v"
  using reachable_awalk[of u v] awalk_ends[of u p v] converse_reachable_induct by blast

lemma awalk_verts_dom_if_uneq: "\<lbrakk>u\<noteq>v; awalk u p v\<rbrakk> \<Longrightarrow> \<exists>x. x \<rightarrow>\<^bsub>G\<^esub> v \<and> x \<in> set (awalk_verts u p)"
 proof(induction p arbitrary: u)
  case Nil
  then show ?case using awalk_def by simp
next
  case (Cons p ps)
  then show ?case
    using awalk_Cons_iff[of u p ps v] awalk_verts.simps(2)[of u p ps] awalk_verts_non_Nil
    by (metis in_arcs_imp_in_arcs_ends list.sel(1) list.set_intros(2) list.set_sel(1))
qed

lemma awalk_verts_append_distinct:
  "\<lbrakk>\<exists>v. awalk r (p1@p2) v; distinct (awalk_verts r (p1@p2))\<rbrakk> \<Longrightarrow> distinct (awalk_verts r p1)"
  using awalk_verts_append by auto

lemma not_distinct_if_head_eq_tail:
  assumes "tail G p = u" and "head G e = u" and "awalk r (ps@[p]@e#p2) v"
  shows "\<not>(distinct (awalk_verts r (ps@[p]@e#p2)))"
using assms proof(induction ps arbitrary: r)
  case Nil
  then have "u \<in> set (awalk_verts (head G p) (e#p2))"
    by (metis append.left_neutral append_Cons awalk_Cons_iff awalk_verts_arc2 list.set_intros(1))
  then show ?case by (simp add: Nil(1))
next
  case (Cons p ps)
  then show ?case using awalk_Cons_iff by auto
qed

lemma awalk_verts_subset_if_p_sub:
  "\<lbrakk>awalk u p1 v; awalk u p2 v; set p1 \<subseteq> set p2\<rbrakk>
    \<Longrightarrow> set (awalk_verts u p1) \<subseteq> set (awalk_verts u p2)"
  using awalk_verts_conv by fastforce

lemma awalk_to_apath_verts_subset:
  "awalk u p v \<Longrightarrow> set (awalk_verts u (awalk_to_apath p)) \<subseteq> set (awalk_verts u p)"
  using awalk_verts_subset_if_p_sub awalk_to_apath_subset apath_awalk_to_apath awalkI_apath
  by blast

lemma unique_apath_verts_in_awalk:
  "\<lbrakk>x \<in> set (awalk_verts u p1); apath u p1 v; awalk u p2 v; \<exists>!p. apath u p v\<rbrakk>
    \<Longrightarrow> x \<in> set (awalk_verts u p2)"
  using apath_awalk_to_apath awalk_to_apath_verts_subset by blast

lemma unique_apath_verts_sub_awalk:
  "\<lbrakk>apath u p v; awalk u q v; \<exists>!p. apath u p v\<rbrakk> \<Longrightarrow> set (awalk_verts u p) \<subseteq> set (awalk_verts u q)"
  using unique_apath_verts_in_awalk by blast

lemma awalk_verts_append3:
  "\<lbrakk>awalk u (p@e#q) r; awalk v q r\<rbrakk> \<Longrightarrow> awalk_verts u (p@e#q) = awalk_verts u p @ awalk_verts v q"
  using awalk_verts_conv by fastforce

lemma verts_reachable_connected:
  "verts G \<noteq> {} \<Longrightarrow> (\<forall>x\<in>verts G. \<forall>y\<in>verts G. x \<rightarrow>\<^sup>* y) \<Longrightarrow> connected G"
  by (simp add: connected_def strongly_connected_def reachable_mk_symmetricI)

lemma out_degree_0_no_arcs:
  assumes "out_degree G v = 0" and "finite (arcs G)"
  shows "\<forall>y. (v,y) \<notin> arcs_ends G"
proof (rule ccontr)
  assume "\<not>(\<forall>y. (v,y) \<notin> arcs_ends G)"
  then obtain y where y_def: "(v,y) \<in> arcs_ends G" by blast
  then obtain a where a_def: "a \<in> arcs G \<and> tail G a = v \<and> head G a = y" by auto
  then have "a \<in> {e \<in> arcs G. tail G e = v}" by simp
  then have "Finite_Set.card {e \<in> arcs G. tail G e = v} > 0" using assms(2) card_gt_0_iff by force
  then show False using assms(1) by (metis less_nat_zero_code out_arcs_def out_degree_def)
qed

lemma out_degree_0_only_self: "finite (arcs G) \<Longrightarrow> out_degree G v = 0 \<Longrightarrow> v \<rightarrow>\<^sup>* x \<Longrightarrow> x = v"
  using converse_reachable_cases out_degree_0_no_arcs by force

lemma not_elem_no_out_arcs: "v \<notin> verts G \<Longrightarrow> out_arcs G v = {}"
  by auto

lemma not_elem_no_in_arcs: "v \<notin> verts G \<Longrightarrow> in_arcs G v = {}"
  by auto

lemma not_elem_out_0: "v \<notin> verts G \<Longrightarrow> out_degree G v = 0"
  unfolding out_degree_def using not_elem_no_out_arcs by simp

lemma not_elem_in_0: "v \<notin> verts G \<Longrightarrow> in_degree G v = 0"
  unfolding in_degree_def using not_elem_no_in_arcs by simp

lemma new_vert_only_no_arcs:
  assumes "G = \<lparr>verts = V \<union> {v}, arcs = A, tail = t, head = h\<rparr>"
      and "G' = \<lparr>verts = V, arcs = A, tail = t, head = h\<rparr>"
      and "wf_digraph G'"
      and "v \<notin> V"
      and "finite (arcs G)"
    shows "\<forall>u. (v,u) \<notin> arcs_ends G"
proof -
  have "out_degree G' v = 0" using assms(2-4) wf_digraph.not_elem_out_0 by fastforce
  then have "out_degree G v = 0" unfolding out_degree_def out_arcs_def using assms(1,2) by simp
  then show ?thesis using assms(5) out_degree_0_no_arcs by blast
qed

lemma new_leaf_out_sets_eq:
  assumes "G = \<lparr>verts = V \<union> {v}, arcs = A \<union> {a}, tail = t(a := u), head = h(a := v)\<rparr>"
      and "G' = \<lparr>verts = V, arcs = A, tail = t, head = h\<rparr>"
      and "u \<in> V"
      and "v \<notin> V"
      and "a \<notin> A"
    shows "{e \<in> arcs G. tail G e = v} = {e \<in> arcs G'. tail G' e = v}"
  using assms by auto

lemma new_leaf_out_0:
  assumes "G = \<lparr>verts = V \<union> {v}, arcs = A \<union> {a}, tail = t(a := u), head = h(a := v)\<rparr>"
      and "G' = \<lparr>verts = V, arcs = A, tail = t, head = h\<rparr>"
      and "wf_digraph G'"
      and "u \<in> V"
      and "v \<notin> V"
      and "a \<notin> A"
    shows "out_degree G v = 0"
proof -
  have "tail G a = u" using assms(1) by simp
  then have 0: "{e \<in> arcs G. tail G e = v} = {e \<in> arcs G'. tail G' e = v}"
    using new_leaf_out_sets_eq assms(1,2,4-6) by blast
  have "out_degree G' v = 0" using assms(2,3,5) wf_digraph.not_elem_out_0 by fastforce
  then show ?thesis unfolding out_degree_def out_arcs_def using 0 by simp
qed

lemma new_leaf_no_arcs:
  assumes "G = \<lparr>verts = V \<union> {v}, arcs = A \<union> {a}, tail = t(a := u), head = h(a := v)\<rparr>"
      and "G' = \<lparr>verts = V, arcs = A, tail = t, head = h\<rparr>"
      and "wf_digraph G'"
      and "u \<in> V"
      and "v \<notin> V"
      and "a \<notin> A"
      and "finite (arcs G)"
    shows "\<forall>u. (v,u) \<notin> arcs_ends G"
  using new_leaf_out_0 assms out_degree_0_no_arcs by presburger

lemma tail_and_head_eq_impl_cas:
  assumes "cas x p y"
      and "\<forall>x \<in> set p. tail G x = tail G' x"
      and "\<forall>x \<in> set p. head G x = head G' x"
    shows "pre_digraph.cas G' x p y"
using assms proof(induction p arbitrary: x y)
  case Nil
  show ?case using pre_digraph.cas.simps(1) Nil(1) by fastforce
next
  case (Cons p ps)
  have 0: "tail G' p = x" using Cons.prems(1,2) by simp
  have "cas (head G p) ps y" using Cons.prems(1) by simp
  then have "pre_digraph.cas G' (head G' p) ps y" using Cons.IH Cons.prems(2,3) by simp
  then show ?case using 0 by (simp add: pre_digraph.cas.simps(2))
qed

lemma new_leaf_same_reachables_orig:
  assumes "x \<rightarrow>\<^sup>*\<^bsub>G\<^esub> y"
      and "G = \<lparr>verts = V \<union> {v}, arcs = A \<union> {a}, tail = t(a := u), head = h(a := v)\<rparr>"
      and "G' = \<lparr>verts = V, arcs = A, tail = t, head = h\<rparr>"
      and "wf_digraph G'"
      and "x \<in> V"
      and "u \<in> V"
      and "v \<notin> V"
      and "y \<noteq> v"
      and "a \<notin> A"
      and "finite (arcs G)"
    shows "x \<rightarrow>\<^sup>*\<^bsub>G'\<^esub> y"
proof -
  obtain p where p_def: "awalk x p y" using reachable_awalk assms(1) by auto
  then have 0: "set p \<subseteq> arcs G" by blast
  have v_0: "out_degree G v = 0" using new_leaf_out_0 assms by presburger
  have a_notin_p: "a \<notin> set p"
  proof
    assume asm: "a \<in> set p"
    have "head G a = v" using assms(2) by simp
    then have "\<exists>p' p''. p'@p''=p \<and> awalk x p' v"
      using asm awalk_decomp awalk_verts_arc2 p_def by metis
    then obtain p' p'' where p'_def: "p'@p''=p \<and> awalk x p' v" by blast
    then have "awalk v p'' y" using p_def by auto
    then have "v \<rightarrow>\<^sup>* y" using reachable_awalk by auto
    then have "v = y" using out_degree_0_only_self assms(10) v_0 by blast
    then show False using assms(8) by simp
  qed
  then have 1: "set p \<subseteq> arcs G'" using assms(2,3) 0 by auto
  have "\<forall>x \<in> set p. tail G x = tail G' x" using assms(2,3) a_notin_p by simp
  moreover have "\<forall>x \<in> set p. head G x = head G' x" using assms(2,3) a_notin_p by simp
  ultimately have "pre_digraph.cas G' x p y" using tail_and_head_eq_impl_cas p_def by blast
  then have "pre_digraph.awalk G' x p y" unfolding pre_digraph.awalk_def using assms(3,5) 1 by simp
  then show ?thesis using assms(4) wf_digraph.reachable_awalkI by fast
qed

lemma new_leaf_same_reachables_new:
  assumes "x \<rightarrow>\<^sup>*\<^bsub>G'\<^esub> y"
      and "G = \<lparr>verts = V \<union> {v}, arcs = A \<union> {a}, tail = t(a := u), head = h(a := v)\<rparr>"
      and "G' = \<lparr>verts = V, arcs = A, tail = t, head = h\<rparr>"
      and "wf_digraph G'"
      and "x \<in> V"
      and "u \<in> V"
      and "v \<notin> V"
      and "y \<noteq> v"
      and "a \<notin> A"
    shows "x \<rightarrow>\<^sup>*\<^bsub>G\<^esub> y"
proof -
  obtain p where p_def: "pre_digraph.awalk G' x p y"
    using wf_digraph.reachable_awalk assms(1,4) by fast
  then have 0: "set p \<subseteq> arcs G'" by (meson pre_digraph.awalk_def)
  then have a_notin_p: "a \<notin> set p" using assms(3,9) by auto
  have 1: "set p \<subseteq> arcs G" using assms(2,3) 0 by auto
  have "\<forall>x \<in> set p. tail G x = tail G' x" using assms(2,3) a_notin_p by simp
  moreover have "\<forall>x \<in> set p. head G x = head G' x" using assms(2,3) a_notin_p by simp
  moreover have "pre_digraph.cas G' x p y" using p_def pre_digraph.awalk_def by fast
  ultimately have "cas x p y" using assms(4) wf_digraph.tail_and_head_eq_impl_cas by fastforce
  then have "awalk x p y" unfolding awalk_def using assms(2,5) 1 by simp
  then show ?thesis using reachable_awalkI by simp
qed

lemma new_leaf_reach_impl_parent:
  assumes "y \<rightarrow>\<^sup>* v"
      and "G = \<lparr>verts = V \<union> {v}, arcs = A \<union> {a}, tail = t(a := u), head = h(a := v)\<rparr>"
      and "G' = \<lparr>verts = V, arcs = A, tail = t, head = h\<rparr>"
      and "wf_digraph G'"
      and "y \<in> V"
      and "v \<notin> V"
    shows "y \<rightarrow>\<^sup>* u"
proof -
  have "\<forall>a \<in> A. h a \<noteq> v"
    using assms(3,4,6) wf_digraph.head_in_verts by (metis pre_digraph.select_convs(1,2,4))
  then have 0: "\<forall>x. (x,v) \<in> arcs_ends G \<longrightarrow> x = u" using assms(2) by fastforce
  have "v \<noteq> y" using assms(5,6) by blast
  then have "y \<rightarrow>\<^sup>+ v" using assms(1) by blast
  then have "\<exists>x. y \<rightarrow>\<^sup>*x \<and> x \<rightarrow>\<^bsub>G\<^esub> v"
    by (meson reachable1_in_verts(1) reachable_conv' tranclD2)
  then obtain x where "y \<rightarrow>\<^sup>* x \<and> x \<rightarrow>\<^bsub>G\<^esub> v" by blast
  then show ?thesis using 0 by blast
qed

end

context graph
begin

abbreviation min_degree :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "min_degree xs x \<equiv> x\<in>xs \<and> (\<forall>y\<in>xs. out_degree G x \<le> out_degree G y)"

lemma graph_del_vert_sym: "sym (arcs_ends (del_vert x))"
  by (smt (z3) wf_digraph_del_vert mem_Collect_eq reachableE sym_digraph_axioms_def arcs_del_vert
      symmetric_conv symI wf_digraph.in_arcs_imp_in_arcs_ends head_del_vert sym_arcs tail_del_vert)

lemma graph_del_vert: "graph (del_vert x)"
  apply(standard)
  by (auto simp: arcs_del_vert2 tail_del_vert head_del_vert verts_del_vert
            no_loops ends_del_vert no_multi_arcs symmetric_def graph_del_vert_sym)

lemma connected_iff_reachable:
  "connected G \<longleftrightarrow> ((\<forall>x\<in>verts G. \<forall>y\<in>verts G. x \<rightarrow>\<^sup>* y) \<and> verts G \<noteq> {})"
  using symmetric_connected_imp_strongly_connected strongly_connected_def verts_reachable_connected
  by(blast)

end

context nomulti_digraph
begin

lemma no_multi_alt:
  "\<lbrakk>e1 \<in> arcs G; e2 \<in> arcs G; e1 \<noteq> e2\<rbrakk> \<Longrightarrow> head G e1 \<noteq> head G e2 \<or> tail G e1 \<noteq> tail G e2"
  using no_multi_arcs by(auto simp: arc_to_ends_def)

end

subsection \<open>Vertices with Multiple Outgoing Arcs\<close>

context wf_digraph
begin

definition branching_points :: "'a set" where
  "branching_points = {x. \<exists>y\<in>arcs G. \<exists>z\<in>arcs G. y\<noteq>z \<and> tail G y = x \<and> tail G z = x}"

definition is_chain :: "bool" where
  "is_chain = (branching_points = {})"

definition last_branching_points :: "'a set" where
  "last_branching_points = {x. (x\<in>branching_points \<and> \<not>(\<exists>y \<in> branching_points. y\<noteq>x \<and> x \<rightarrow>\<^sup>* y))}"

lemma branch_in_verts: "x \<in> branching_points \<Longrightarrow> x \<in> verts G"
  unfolding branching_points_def by auto

lemma last_branch_is_branch:
  "(y\<in>last_branching_points \<Longrightarrow> y\<in>branching_points)"
  unfolding last_branching_points_def by blast

lemma last_branch_alt: "x \<in> last_branching_points \<Longrightarrow> (\<forall>z. x \<rightarrow>\<^sup>* z \<and> z\<noteq>x \<longrightarrow> z \<notin> branching_points)"
  unfolding last_branching_points_def by blast

lemma braching_points_alt:
  assumes "finite (arcs G)"
  shows "x \<in> branching_points \<longleftrightarrow> out_degree G x \<ge> 2" (is "?P \<longleftrightarrow> ?Q")
proof
  assume "?P"
  then obtain a1 a2 where "a1\<in>arcs G \<and> a2\<in>arcs G \<and> a1\<noteq>a2 \<and> tail G a1 = x \<and> tail G a2 = x"
    using branching_points_def by auto
  then have 0: "a1 \<in> out_arcs G x \<and> a2 \<in> out_arcs G x \<and> a1\<noteq>a2" by simp
  have "finite (out_arcs G x)" by (simp add: assms out_arcs_def)
  then show "?Q" unfolding out_degree_def using 0 two_elems_card_ge_2 by fast
next
  assume 0: "?Q"
  have "finite (out_arcs G x)" by (simp add: assms out_arcs_def)
  then have "\<exists>a1 a2. a1 \<in> (out_arcs G x) \<and> a2 \<in> (out_arcs G x) \<and> a1\<noteq>a2"
    using 0 out_degree_def by (metis Suc_n_not_le_n card_le_Suc0_iff_eq le_trans numeral_2_eq_2)
  then show "?P" unfolding branching_points_def by auto
qed

lemma branch_in_supergraph:
  assumes "subgraph C G"
      and "x \<in> wf_digraph.branching_points C"
    shows "x \<in> branching_points"
proof -
  have 0: "wf_digraph C" using assms(1) Digraph_Component.subgraph_def subgraph.sub_G by auto
  have 1: "wf_digraph G" using assms(1) subgraph.sub_G by auto
  obtain y z where arcs_C: "y\<in>arcs C \<and> z\<in>arcs C \<and> y\<noteq>z \<and> tail C y = x \<and> tail C z = x"
    using assms(2) wf_digraph.branching_points_def 0 by blast
  then have "y\<in>arcs G \<and> z\<in>arcs G \<and> y\<noteq>z \<and> tail C y = x \<and> tail C z = x"
    using assms(1) subgraph.sub_G by blast
  then have "y\<in>arcs G \<and> z\<in>arcs G \<and> y\<noteq>z \<and> tail G y = x \<and> tail G z = x"
    using assms(1) subgraph.sub_G compatible_def by force
  then show ?thesis using branching_points_def assms(1) subgraph.sub_G by blast
qed

lemma subgraph_no_branch_chain:
  assumes "subgraph C G"
      and "verts C \<subseteq> verts G - {x. \<exists>y\<in>branching_points. x \<rightarrow>\<^sup>*\<^bsub>G\<^esub> y}"
    shows "wf_digraph.is_chain C"
proof (rule ccontr)
  assume asm: "\<not>wf_digraph.is_chain C"
  let ?rem = "{x. \<exists>y\<in>branching_points. x \<rightarrow>\<^sup>*\<^bsub>G\<^esub> y}"
  have "wf_digraph C" using assms(1) Digraph_Component.subgraph_def subgraph.sub_G by auto
  then obtain x where x_def[simp]: "x \<in> wf_digraph.branching_points C"
    using wf_digraph.is_chain_def asm by blast
  then have "x \<in> branching_points" using assms(1) branch_in_supergraph by simp
  moreover from this have "x \<in> verts G" using branch_in_verts by simp
  moreover from this have "x \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x" by simp
  ultimately have "x \<in> ?rem" by blast
  then show False using assms(2) \<open>wf_digraph C\<close> subsetD wf_digraph.branch_in_verts by fastforce
qed

lemma branch_if_leaf_added:
  assumes "x\<in>wf_digraph.branching_points G'"
      and "G = \<lparr>verts = V \<union> {v}, arcs = A \<union> {a}, tail = t(a := u), head = h(a := v)\<rparr>"
      and "G' = \<lparr>verts = V, arcs = A, tail = t, head = h\<rparr>"
      and "wf_digraph G'"
      and "a \<notin> A"
    shows "x \<in> branching_points"
proof -
  obtain a1 a2 where a12: "a1\<in>arcs G' \<and> a2\<in>arcs G' \<and> a1\<noteq>a2 \<and> tail G' a1 = x \<and> tail G' a2 = x"
    using wf_digraph.branching_points_def assms(1,4) by blast
  then have "a1 \<noteq> a \<and> a2 \<noteq> a" using assms(3,5) by auto
  then have 0: "tail G a1 = tail G' a1 \<and> tail G a2 = tail G' a2" using assms(2,3) by simp
  have "a1\<in>arcs G \<and> a2\<in>arcs G \<and> a1\<noteq>a2 \<and> a1\<noteq>a2 \<and> tail G' a1 = x \<and> tail G' a2 = x"
    using assms(2,3) a12 by simp
  then have "a1\<in>arcs G \<and> a2\<in>arcs G \<and> a1\<noteq>a2 \<and> tail G a1 = x \<and> tail G a2 = x"
    using 0 by simp
  then show ?thesis unfolding branching_points_def by blast
qed

lemma new_leaf_no_branch:
  assumes "G = \<lparr>verts = V \<union> {v}, arcs = A \<union> {a}, tail = t(a := u), head = h(a := v)\<rparr>"
      and "G' = \<lparr>verts = V, arcs = A, tail = t, head = h\<rparr>"
      and "wf_digraph G'"
      and "u \<in> V"
      and "v \<notin> V"
      and "a \<notin> A"
    shows "v \<notin> branching_points"
proof -
  have "v \<noteq> u" using assms(4,5) by fast
  have "\<forall>a\<in>arcs G'. tail G' a \<noteq> v"
    using assms(2,3,5) pre_digraph.select_convs(1) wf_digraph_def by fast
  moreover have "\<forall>x \<in> arcs G'. tail G x = tail G' x" using assms(1,2,6) by simp
  ultimately have "\<forall>a\<in>arcs G'. tail G a \<noteq> v" by simp
  then have "\<forall>a\<in>arcs G. tail G a \<noteq> v"
    using assms(1,2,6) Un_iff pre_digraph.select_convs(2) singletonD \<open>v \<noteq> u\<close> by simp
  then show ?thesis unfolding branching_points_def by blast
qed

lemma new_leaf_not_reach_last_branch:
  assumes "y\<in>wf_digraph.last_branching_points G'"
      and "\<not> y \<rightarrow>\<^sup>* u"
      and "G = \<lparr>verts = V \<union> {v}, arcs = A \<union> {a}, tail = t(a := u), head = h(a := v)\<rparr>"
      and "G' = \<lparr>verts = V, arcs = A, tail = t, head = h\<rparr>"
      and "wf_digraph G'"
      and "y \<in> V"
      and "u \<in> V"
      and "v \<notin> V"
      and "a \<notin> A"
      and "finite (arcs G)"
    shows "\<not>(\<exists>z \<in> branching_points. z\<noteq>y \<and> y \<rightarrow>\<^sup>* z)"
proof
  assume "\<exists>z \<in> branching_points. z\<noteq>y \<and> y \<rightarrow>\<^sup>* z"
  then obtain z where z_def: "z \<in> branching_points \<and> z\<noteq>y \<and> y \<rightarrow>\<^sup>* z" by blast
  then have "z \<noteq> u" using assms(2) by blast
  then obtain a1 a2 where a12: "a1\<in>arcs G \<and> a2\<in>arcs G \<and> a1\<noteq>a2 \<and> tail G a1 = z \<and> tail G a2 = z"
    using branching_points_def z_def by blast
  then have 0: "a1 \<noteq> a \<and> a2 \<noteq> a" using assms(3) \<open>z\<noteq>u\<close> by fastforce
  then have 1: "tail G a1 = tail G' a1 \<and> tail G a2 = tail G' a2" using assms(3,4) by simp
  have "a1\<in>arcs G' \<and> a2\<in>arcs G' \<and> a1\<noteq>a2 \<and> tail G a1 = z \<and> tail G a2 = z"
    using assms(3,4) a12 0 by simp
  then have "a1\<in>arcs G' \<and> a2\<in>arcs G' \<and> a1\<noteq>a2 \<and> tail G' a1 = z \<and> tail G' a2 = z"
    using 1 by simp
  then have 2: "z \<in> wf_digraph.branching_points G'"
    using wf_digraph.branching_points_def assms(5) by auto
  have "z \<noteq> v" using assms(2,3,4,5,6,8) z_def new_leaf_reach_impl_parent by blast
  then have "y \<rightarrow>\<^sup>*\<^bsub>G'\<^esub>  z" using new_leaf_same_reachables_orig z_def assms by blast
  then have "\<exists>z\<in>wf_digraph.branching_points G'. z\<noteq>y \<and> y \<rightarrow>\<^sup>*\<^bsub>G'\<^esub> z" using 2 z_def by blast
  then have "y \<notin> wf_digraph.last_branching_points G'"
    using wf_digraph.last_branching_points_def assms(5) by blast
  then show False using assms(1) by simp
qed

lemma new_leaf_parent_nbranch_in_orig:
  assumes "y\<in>branching_points"
      and "y \<noteq> u"
      and "G = \<lparr>verts = V \<union> {v}, arcs = A \<union> {a}, tail = t(a := u), head = h(a := v)\<rparr>"
      and "G' = \<lparr>verts = V, arcs = A, tail = t, head = h\<rparr>"
      and "wf_digraph G'"
    shows "y\<in>wf_digraph.branching_points G'"
proof -
  obtain a1 a2 where a12: "a1\<in>arcs G \<and> a2\<in>arcs G \<and> a1\<noteq>a2 \<and> tail G a1 = y \<and> tail G a2 = y"
    using branching_points_def assms(1) by blast
  then have 0: "a1 \<noteq> a \<and> a2 \<noteq> a" using assms(2,3) by fastforce
  then have 1: "tail G a1 = tail G' a1 \<and> tail G a2 = tail G' a2" using assms(3,4) by simp
  have "a1\<in>arcs G' \<and> a2\<in>arcs G' \<and> a1\<noteq>a2 \<and> tail G a1 = y \<and> tail G a2 = y"
    using assms(3,4) a12 0 by auto
  then have "a1\<in>arcs G' \<and> a2\<in>arcs G' \<and> a1\<noteq>a2 \<and> tail G' a1 = y \<and> tail G' a2 = y"
    using 1 by simp
  then show ?thesis using assms(5) wf_digraph.branching_points_def by auto
qed

lemma new_leaf_last_branch_exists_preserv:
  assumes "y\<in>wf_digraph.last_branching_points G'"
      and "x \<rightarrow>\<^sup>* y"
      and "G = \<lparr>verts = V \<union> {v}, arcs = A \<union> {a}, tail = t(a := u), head = h(a := v)\<rparr>"
      and "G' = \<lparr>verts = V, arcs = A, tail = t, head = h\<rparr>"
      and "wf_digraph G'"
      and "y \<in> V"
      and "u \<in> V"
      and "v \<notin> V"
      and "a \<notin> A"
      and "finite (arcs G)"
      and "\<forall>x. y \<rightarrow>\<^sup>+ x \<longrightarrow> y\<noteq>x"
    obtains y' where "y'\<in>last_branching_points \<and> x \<rightarrow>\<^sup>* y'"
proof (cases "y \<rightarrow>\<^sup>* u")
  case True
  have "y \<in> wf_digraph.branching_points G'"
    using assms(1,5) wf_digraph.last_branch_is_branch by fast
  then have y_branch: "y \<in> branching_points" using branch_if_leaf_added assms(3-5,9) by blast
  have v_nbranch: "v \<notin> branching_points" using new_leaf_no_branch assms(3-5,7-9) by blast
  then show ?thesis
  proof(cases "u \<in> branching_points")
    case True
    have "\<not>(\<exists>z \<in> branching_points. z\<noteq>u \<and> u \<rightarrow>\<^sup>* z)"
    proof
      assume "\<exists>z \<in> branching_points. z\<noteq>u \<and> u \<rightarrow>\<^sup>* z"
      then obtain z where z_def: "z \<in> branching_points \<and> z\<noteq>u \<and> u \<rightarrow>\<^sup>* z" by blast
      then have "z \<noteq> v" using v_nbranch by blast
      then have "u \<rightarrow>\<^sup>*\<^bsub>G'\<^esub> z"
        using new_leaf_same_reachables_orig assms(3-5,7-10) z_def by blast
      moreover have "y \<rightarrow>\<^sup>*\<^bsub>G'\<^esub> u"
        using new_leaf_same_reachables_orig \<open>y \<rightarrow>\<^sup>* u\<close> assms(3-10) by blast
      ultimately have 0: "y \<rightarrow>\<^sup>*\<^bsub>G'\<^esub> z"
        using assms(5) wf_digraph.reachable_trans by fast
      have "y \<rightarrow>\<^sup>+ z"
        using \<open>y \<rightarrow>\<^sup>* u\<close> z_def reachable_reachable1_trans reachable_neq_reachable1 by blast
      then have "y \<noteq> z" using assms(11) by simp
      have "z \<in> wf_digraph.branching_points G'"
        using z_def new_leaf_parent_nbranch_in_orig assms(3-5) by blast
      then have "y \<notin> wf_digraph.last_branching_points G'"
        using 0 assms(5) wf_digraph.last_branch_alt \<open>y \<noteq> z\<close> by fast
      then show False using assms(1) by simp
    qed
    then have "u \<in> last_branching_points" unfolding last_branching_points_def using True by blast
    then show ?thesis using assms(2) \<open>y \<rightarrow>\<^sup>* u\<close> reachable_trans that by blast
  next
    case False
    have "\<not>(\<exists>z \<in> branching_points. z\<noteq>y \<and> y \<rightarrow>\<^sup>* z)"
    proof
      assume "\<exists>z \<in> branching_points. z\<noteq>y \<and> y \<rightarrow>\<^sup>* z"
      then obtain z where z_def: "z \<in> branching_points \<and> z\<noteq>y \<and> y \<rightarrow>\<^sup>* z" by blast
      then have "z \<noteq> v" using v_nbranch by blast
      then have 0: "y \<rightarrow>\<^sup>*\<^bsub>G'\<^esub> z"
        using new_leaf_same_reachables_orig assms(3-10) z_def by blast
      have "z \<noteq> u" using False z_def by blast
      then have "z \<in> wf_digraph.branching_points G'"
        using z_def new_leaf_parent_nbranch_in_orig assms(3-5) by blast
      then have "y \<notin> wf_digraph.last_branching_points G'"
        using 0 z_def assms(5) wf_digraph.last_branch_alt by fast
      then show False using assms(1) by simp
    qed
    then have "y \<in> last_branching_points" using last_branching_points_def y_branch by simp
    then show ?thesis using assms(2) that by blast
  qed
next
  case False
  have "y \<in> wf_digraph.branching_points G'"
    using assms(1,5) wf_digraph.last_branch_is_branch by fast
  then have "y \<in> branching_points" using branch_if_leaf_added assms(3-5,9) by blast
  moreover have "\<not>(\<exists>z \<in> branching_points. z\<noteq>y \<and> y \<rightarrow>\<^sup>* z)"
    using new_leaf_not_reach_last_branch assms(1,3-10) False by blast
  ultimately have "y \<in> last_branching_points" unfolding last_branching_points_def by blast
  then show ?thesis using assms(2) that by blast
qed

end

subsection \<open>Vertices with Multiple Incoming Arcs\<close>

context wf_digraph
begin

definition merging_points :: "'a set" where
  "merging_points = {x. \<exists>y\<in>arcs G. \<exists>z\<in>arcs G. y\<noteq>z \<and> head G y = x \<and> head G z = x}"

definition is_chain' :: "bool" where
  "is_chain' = (merging_points = {})"

definition last_merging_points :: "'a set" where
  "last_merging_points = {x. (x\<in>merging_points \<and> \<not>(\<exists>y \<in> merging_points. y\<noteq>x \<and> x \<rightarrow>\<^sup>* y))}"

lemma merge_in_verts: "x \<in> merging_points \<Longrightarrow> x \<in> verts G"
  unfolding merging_points_def by auto

lemma last_merge_is_merge:
  "(y\<in>last_merging_points \<Longrightarrow> y\<in>merging_points)"
  unfolding last_merging_points_def by blast

lemma last_merge_alt: "x \<in> last_merging_points \<Longrightarrow> (\<forall>z. x \<rightarrow>\<^sup>* z \<and> z\<noteq>x \<longrightarrow> z \<notin> merging_points)"
  unfolding last_merging_points_def using reachable_in_verts(2) by blast

lemma merge_in_supergraph:
  assumes "subgraph C G"
      and "x \<in> wf_digraph.merging_points C"
    shows "x \<in> merging_points"
proof -
  have 0: "wf_digraph C" using assms(1) Digraph_Component.subgraph_def subgraph.sub_G by auto
  have 1: "wf_digraph G" using assms(1) subgraph.sub_G by auto
  obtain y z where arcs_C: "y\<in>arcs C \<and> z\<in>arcs C \<and> y\<noteq>z \<and> head C y = x \<and> head C z = x"
    using assms(2) wf_digraph.merging_points_def 0 by blast
  then have "y\<in>arcs G \<and> z\<in>arcs G \<and> y\<noteq>z \<and> head C y = x \<and> head C z = x"
    using assms(1) subgraph.sub_G by blast
  then have "y\<in>arcs G \<and> z\<in>arcs G \<and> y\<noteq>z \<and> head G y = x \<and> head G z = x"
    using assms(1) subgraph.sub_G compatible_def by force
  then show ?thesis using merging_points_def assms(1) subgraph.sub_G by blast
qed

lemma subgraph_no_merge_chain:
  assumes "subgraph C G"
      and "verts C \<subseteq> verts G - {x. \<exists>y\<in>merging_points. x \<rightarrow>\<^sup>*\<^bsub>G\<^esub> y}"
    shows "wf_digraph.is_chain' C"
proof (rule ccontr)
  assume asm: "\<not>wf_digraph.is_chain' C"
  let ?rem = "{x. \<exists>y\<in>merging_points. x \<rightarrow>\<^sup>*\<^bsub>G\<^esub> y}"
  have "wf_digraph C" using assms(1) Digraph_Component.subgraph_def subgraph.sub_G by auto
  then obtain x where x_def[simp]: "x \<in> wf_digraph.merging_points C"
    using wf_digraph.is_chain'_def asm by blast
  then have "x \<in> merging_points" using assms(1) merge_in_supergraph by simp
  moreover from this have "x \<in> verts G" using merge_in_verts by simp
  moreover from this have "x \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x" by simp
  ultimately have "x \<in> ?rem" by blast
  then show False using assms(2) \<open>wf_digraph C\<close> subsetD wf_digraph.merge_in_verts by fastforce
qed

end

end