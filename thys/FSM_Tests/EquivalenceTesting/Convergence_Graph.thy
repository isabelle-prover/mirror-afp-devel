section \<open>Convergence Graphs\<close>

text \<open>This theory introduces the invariants required for the initialisation, insertion, lookup, and
      merge operations on convergence graphs.\<close>

theory Convergence_Graph
imports Convergence "../Prefix_Tree"
begin


lemma after_distinguishes_diverge :
  assumes "observable M1"
  and     "observable M2"
  and     "minimal M1"
  and     "minimal M2"
  and     "\<alpha> \<in> L M1"
  and     "\<beta> \<in> L M1"
  and     "\<gamma> \<in> set (after T1 \<alpha>) \<inter> set (after T1 \<beta>)"
  and     "distinguishes M1 (after_initial M1 \<alpha>) (after_initial M1 \<beta>) \<gamma>"
  and     "L M1 \<inter> set T1 = L M2 \<inter> set T1"
shows "\<not>converge M2 \<alpha> \<beta>"
proof 
  have "\<gamma> \<noteq> []" 
    using assms(5,6,8)
    by (metis after_distinguishes_language append_Nil2 assms(1)) 
  then have "\<alpha> \<in> set T1" and "\<beta> \<in> set T1"
    using assms(7) after_set_Cons[of \<gamma>]
    by auto

  assume "converge M2 \<alpha> \<beta>"
  moreover have "\<alpha> \<in> L M2"
    using assms(5,9) \<open>\<alpha> \<in> set T1\<close> by blast
  moreover have "\<beta> \<in> L M2"
    using assms(6,9) \<open>\<beta> \<in> set T1\<close> by blast
  ultimately have "(after_initial M2 \<alpha>) = (after_initial M2 \<beta>)"
    using convergence_minimal[OF assms(4,2)]
    by blast
  then have "\<alpha>@\<gamma> \<in> L M2 = (\<beta>@\<gamma> \<in> L M2)"
    using \<open>converge M2 \<alpha> \<beta>\<close> assms(2) converge_append_language_iff by blast
  moreover have "(\<alpha>@\<gamma> \<in> L M1) \<noteq> (\<beta>@\<gamma> \<in> L M1)"
    using after_distinguishes_language[OF assms(1,5,6,8)] .
  moreover have "\<alpha>@\<gamma> \<in> set T1" and "\<beta>@\<gamma> \<in> set T1"
    using assms(7) unfolding after_set
    by (metis IntE append_Nil2 assms(5) assms(6) calculation(2) insertE mem_Collect_eq)+
  ultimately show False
    using assms(9)
    by blast
qed


subsection \<open>Required Invariants on Convergence Graphs\<close>

definition convergence_graph_lookup_invar :: "('a,'b,'c) fsm \<Rightarrow> ('e,'b,'c) fsm \<Rightarrow>
                                               ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow>
                                               'd \<Rightarrow>
                                               bool"
  where 
  "convergence_graph_lookup_invar M1 M2 cg_lookup G = (\<forall> \<alpha> .  \<alpha> \<in> L M1 \<longrightarrow> \<alpha> \<in> L M2 \<longrightarrow> \<alpha> \<in> list.set (cg_lookup G \<alpha>) \<and> (\<forall> \<beta> . \<beta> \<in> list.set (cg_lookup G \<alpha>) \<longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>))"

lemma convergence_graph_lookup_invar_simp:
  assumes "convergence_graph_lookup_invar M1 M2 cg_lookup G"
  and     "\<alpha> \<in> L M1" and "\<alpha> \<in> L M2"
  and     "\<beta> \<in> list.set (cg_lookup G \<alpha>)"
shows "converge M1 \<alpha> \<beta>" and "converge M2 \<alpha> \<beta>"
  using assms unfolding convergence_graph_lookup_invar_def by blast+


definition convergence_graph_initial_invar :: "('a,'b,'c) fsm \<Rightarrow> ('e,'b,'c) fsm \<Rightarrow>
                                               ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow>
                                               (('a,'b,'c) fsm \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> 'd) \<Rightarrow>
                                               bool"
  where
  "convergence_graph_initial_invar M1 M2 cg_lookup cg_initial = (\<forall> T . (L M1 \<inter> set T = (L M2 \<inter> set T)) \<longrightarrow> finite_tree T \<longrightarrow> convergence_graph_lookup_invar M1 M2 cg_lookup (cg_initial M1 T))"

definition convergence_graph_insert_invar :: "('a,'b,'c) fsm \<Rightarrow> ('e,'b,'c) fsm \<Rightarrow>
                                              ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow>
                                              ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow>
                                              bool" 
  where
  "convergence_graph_insert_invar M1 M2 cg_lookup cg_insert = (\<forall> G \<gamma> . \<gamma> \<in> L M1 \<longrightarrow> \<gamma> \<in> L M2 \<longrightarrow> convergence_graph_lookup_invar M1 M2 cg_lookup G \<longrightarrow> convergence_graph_lookup_invar M1 M2 cg_lookup (cg_insert G \<gamma>))"

definition convergence_graph_merge_invar :: "('a,'b,'c) fsm \<Rightarrow> ('e,'b,'c) fsm \<Rightarrow>
                                       ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow>
                                       ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow>
                                       bool" 
  where
  "convergence_graph_merge_invar M1 M2 cg_lookup cg_merge = (\<forall> G \<gamma> \<gamma>'. converge M1 \<gamma> \<gamma>' \<longrightarrow> converge M2 \<gamma> \<gamma>' \<longrightarrow> convergence_graph_lookup_invar M1 M2 cg_lookup G \<longrightarrow> convergence_graph_lookup_invar M1 M2 cg_lookup (cg_merge G \<gamma> \<gamma>'))"


end