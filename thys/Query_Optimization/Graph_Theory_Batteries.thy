theory Graph_Theory_Batteries
  imports "Graph_Theory.Graph_Theory"
begin

text \<open>This theory collects some useful lemmas which extend the graph library.\<close>

lemma (in wf_digraph) sp_non_neg_if_w_non_neg:
  assumes w_non_neg: "\<forall>e \<in> arcs G. w e \<ge> 0"
  shows "\<mu> w u v \<ge> 0"
proof(cases "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v")
  case True
  have *: "awalk u p v \<Longrightarrow> awalk_cost w p \<ge> 0" for p
    by (simp add: pos_cost_pos_awalk_cost w_non_neg)
  then show ?thesis unfolding \<mu>_def
    by (metis (mono_tags, lifting) INF_less_iff ereal_less_eq(5) mem_Collect_eq not_less)
next
  case False
  then show ?thesis by (simp add: shortest_path_inf)
qed


lemma (in wf_digraph) sp_to_self_if_w_non_neg:
  assumes w_non_neg: "\<forall>e \<in> arcs G. w e \<ge> 0" and "u \<in> verts G"
  shows "\<mu> w u u = 0"
proof -
  have "awalk u [] u" and "awalk_cost w [] = 0"
    by (auto simp: assms(2) awalk_Nil_iff)
  moreover
  have "\<mu> w u u \<ge> 0" by (simp add: sp_non_neg_if_w_non_neg w_non_neg)
  ultimately show "\<mu> w u u = 0"
    by (metis antisym ereal_eq_0(2) min_cost_le_walk_cost)
qed

lemma (in fin_digraph) reachable_verts_finite: "finite {x. u \<rightarrow>\<^sup>* x}"
  using finite_verts
  by (metis finite_subset mem_Collect_eq reachable_in_vertsE subsetI)

lemma (in wf_digraph) awalk_not_distinct:
  assumes "finite (verts G)" and "awalk u p v" and "length p \<ge> card (verts G)"
  shows "\<not> distinct (awalk_verts u p)"
proof -
  have *: "length (awalk_verts u p) > length p"
    by (induction p arbitrary: u) auto

  show ?thesis
  proof(cases "length p = 0")
    case True
    with assms show ?thesis unfolding awalk_def by simp
  next
    case False
    with assms * have "length (awalk_verts u p) > card (verts G)"
      by auto
    moreover
    have "set (awalk_verts u p) \<subseteq> verts G" using assms(2) by blast
    ultimately show ?thesis using assms(1)
      by (induction p arbitrary: u)
         (auto, metis card_subset_eq distinct_card less_antisym)
  qed
qed

lemma (in wf_digraph) awalk_del_vert:
  "\<lbrakk> awalk u p v; x \<notin> set (awalk_verts u p) \<rbrakk> \<Longrightarrow> pre_digraph.awalk (del_vert x) u p v"
proof(induction p arbitrary: u)
  case Nil
  then have "set (awalk_verts u []) = {u}" by auto
  with Nil have "x \<noteq> u" by simp
  moreover
  from Nil have "u = v" unfolding awalk_def by auto
  ultimately show ?case using Nil
    by (simp add: awalk_hd_in_verts pre_digraph.verts_del_vert
        wf_digraph.awalk_Nil_iff wf_digraph_del_vert)
next
  case (Cons a p)
  then obtain u' where u': "pre_digraph.awalk (del_vert x) u' p v"
    using awalk_Cons_iff by auto
  moreover
  from Cons.prems have "head G a \<noteq> x"
    using hd_in_awalk_verts(1) awalk_Cons_iff by auto
  ultimately show ?case using Cons
    by (auto simp: awalk_Cons_iff head_del_vert pre_digraph.del_vert_simps(2)
        tail_del_vert wf_digraph.awalk_Cons_iff wf_digraph_del_vert)
qed

text \<open>This is an alternative formulation of @{thm pre_digraph.arcs_del_vert}.\<close>
lemma (in pre_digraph) arcs_del_vert2:
  "arcs (del_vert v) = arcs G - in_arcs G v - out_arcs G v"
  using arcs_del_vert by force

lemma (in wf_digraph) strongly_con_imp_reachable_eq_verts:
  "\<lbrakk> r \<in> verts G; strongly_connected G \<rbrakk> \<Longrightarrow> {x. r \<rightarrow>\<^sup>* x} = verts G"
  unfolding strongly_connected_def using reachable_in_verts(2) by blast

lemma (in wf_digraph) strongly_con_imp_sp_finite:
  "\<lbrakk> u \<in> verts G; v \<in> verts G; strongly_connected G \<rbrakk> \<Longrightarrow> \<mu> w u v < \<infinity>"
  unfolding strongly_connected_def using \<mu>_reach_conv by auto

text \<open>This is an alternative formulation of @{thm fin_digraph.min_cost_awalk} with different
  assumptions.\<close>
lemma (in fin_digraph) min_cost_awalk2:
  assumes "\<mu> w a b \<noteq> \<infinity>" "\<mu> w a b \<noteq> -\<infinity>"
  shows "\<exists>p. apath a p b \<and> \<mu> w a b = awalk_cost w p"
proof -
  from assms have "a \<rightarrow>\<^sup>* b" using \<mu>_reach_conv by auto
  then show ?thesis using no_neg_cyc_reach_imp_path
    using assms(2) neg_cycle_imp_inf_\<mu> by blast
qed

lemma (in fin_digraph) sp_triangle:
  assumes "a \<in> verts G" "b \<in> verts G" "c \<in> verts G"
      and w_non_neg: "\<forall>e \<in> arcs G. w e \<ge> 0"
    shows "\<mu> w a c \<le> \<mu> w a b + \<mu> w b c"
proof(rule ccontr)
  assume "\<not> \<mu> w a c \<le> \<mu> w a b + \<mu> w b c"
  then have *: "\<mu> w a c > \<mu> w a b + \<mu> w b c"
    using not_less by blast
  consider (minf) "\<mu> w a c = -\<infinity>" | (pinf) "\<mu> w a c = \<infinity>"
    | (fin) "\<mu> w a c \<noteq> -\<infinity> \<and> \<mu> w a c \<noteq> \<infinity>" by auto
  then show "False"
  proof(cases)
    case minf
    with * show ?thesis by auto
  next
    case pinf
    with * have "\<mu> w a b < \<infinity>" "\<mu> w b c < \<infinity>"
      by auto
    then have "a \<rightarrow>\<^sup>* b" "b \<rightarrow>\<^sup>* c" using \<mu>_reach_conv by auto
    then have "a \<rightarrow>\<^sup>* c" using reachable_trans by blast
    then have "\<mu> w a c \<noteq> \<infinity>" using \<mu>_reach_conv by auto
    with pinf show ?thesis by simp
  next
    case fin
    with * have "\<mu> w a b \<noteq> \<infinity>" "\<mu> w b c \<noteq> \<infinity>" by auto
    moreover
    from fin * have "\<mu> w a b \<noteq> -\<infinity>" "\<mu> w b c \<noteq> -\<infinity>"
      using w_non_neg sp_non_neg_if_w_non_neg by auto
    ultimately have
      "\<exists>p. awalk a p b \<and> awalk_cost w p = \<mu> w a b"
      "\<exists>p. awalk b p c \<and> awalk_cost w p = \<mu> w b c"
      using min_cost_awalk2 by (fastforce intro: awalkI_apath)+
    then obtain p1 p2 where
        "awalk a p1 b" "awalk_cost w p1 = \<mu> w a b" and
        "awalk b p2 c" "awalk_cost w p2 = \<mu> w b c" by blast
    then have "awalk a (p1@p2) c \<and> awalk_cost w (p1@p2) = \<mu> w a b + \<mu> w b c"
      by (auto intro: awalk_appendI) (metis plus_ereal.simps(1))
    then show ?thesis using min_cost_le_walk_cost
      by (metis \<open>\<not> \<mu> w a c \<le> \<mu> w a b + \<mu> w b c\<close>)
  qed
qed

end