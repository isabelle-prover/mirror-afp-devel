theory Reachable_Nodes imports Bit_Vector_Framework begin

\<comment> \<open>We define an analysis for collecting the reachable nodes in a program graph.
    First we define it analysis, and then we encode it into Datalog using our
    Bit-Vector Framework locale. We also prove the encoding correct. \<close>


section \<open>Reachable Nodes\<close>

\<comment> \<open>For each node calculates to which nodes the execution may reach in the future\<close>

fun nodes_on_edge :: "('n,'v) edge \<Rightarrow> 'n set" where
  "nodes_on_edge (q1, \<alpha>, q2) = {q1, q2}"

definition node_on_edge_list :: "('n,'v) edge list \<Rightarrow> 'n \<Rightarrow> bool" where
  "node_on_edge_list \<pi> q = (\<exists>\<pi>1 \<pi>2 e. \<pi> = \<pi>1 @ [e] @ \<pi>2 \<and> q \<in> nodes_on_edge e)"

definition nodes_on_path :: "'n list \<times> 'v action list \<Rightarrow> 'n set" where
  "nodes_on_path \<pi> = {q. node_on_edge_list (LTS.transition_list \<pi>) q}"

locale analysis_RN = finite_program_graph pg
  for pg :: "('n::finite,'v::finite action) program_graph" 
begin

interpretation LTS edges .

definition analysis_dom_RN :: "'n set" where
  "analysis_dom_RN = UNIV"

fun kill_set_RN :: "('n,'v action) edge \<Rightarrow> 'n set" where
  "kill_set_RN (q\<^sub>o, \<alpha>, q\<^sub>s) = {}"

fun gen_set_RN :: "('n,'v action) edge \<Rightarrow> 'n set" where
  "gen_set_RN (q\<^sub>o, \<alpha>, q\<^sub>s) = {q\<^sub>o}"

definition d_init_RN :: "'n set" where
  "d_init_RN = {end}"

interpretation bw_may: analysis_BV_backward_may pg analysis_dom_RN kill_set_RN gen_set_RN d_init_RN
  using analysis_BV_backward_may.intro[of pg analysis_dom_RN kill_set_RN gen_set_RN d_init_RN]
    analysis_BV_backward_may_axioms_def[of pg analysis_dom_RN] finite_program_graph_axioms 
    finite_program_graph_axioms finite_program_graph_def[of pg] analysis_dom_RN_def by auto

lemma node_on_edge_list_S_hat_edge_list:
  assumes "ts \<in> transition_list_path"
  assumes "trans_tl (last ts) = end"
  assumes "node_on_edge_list ts q"
  shows "q \<in> bw_may.S_hat_edge_list ts d_init_RN"
  using assms
proof (induction rule: LTS.transition_list_path.induct[OF assms(1)])
  case (1 q' l q'')
  then show ?case
    by (simp add: d_init_RN_def Cons_eq_append_conv bw_may.S_hat_def node_on_edge_list_def)
next
  case (2 q' l q'' l' q''' ts)
  from 2(6) obtain \<pi>1 \<pi>2 e where 
    "(q', l, q'') # (q'', l', q''') # ts = \<pi>1 @ [e] @ \<pi>2"
    "q \<in> nodes_on_edge e"
    unfolding node_on_edge_list_def by auto
  then have "e = (q', l, q'') \<or> e \<in> set ((q'', l', q''') # ts)"
    by (metis (no_types, lifting) append_Cons hd_append in_set_conv_decomp list.sel(1) list.sel(3) tl_append2)
  then show ?case
  proof 
    assume "e = (q', l, q'')"
    then have "q = q' \<or> q = q''"
      using \<open>q \<in> nodes_on_edge e\<close> by auto
    then show ?case
    proof 
      assume "q = q'"
      then show ?case
        unfolding bw_may.S_hat_edge_list.simps bw_may.S_hat_def by auto
    next
      assume "q = q''"
      then have "q \<in> bw_may.S_hat_edge_list ((q'', l', q''') # ts) d_init_RN"
        using "2.IH" "2.hyps"(2) "2.prems"(2) node_on_edge_list_def by fastforce
      then show ?case
        unfolding bw_may.S_hat_edge_list.simps bw_may.S_hat_def by auto
    qed
  next
    assume "e \<in> set ((q'', l', q''') # ts)"
    then have "q \<in> bw_may.S_hat_edge_list ((q'', l', q''') # ts) d_init_RN"
      by (metis "2.IH" "2.hyps"(2) "2.prems"(2) \<open>q \<in> nodes_on_edge e\<close> append_Cons append_Nil in_set_conv_decomp last.simps list.distinct(1) node_on_edge_list_def)
    then show ?case
      unfolding bw_may.S_hat_edge_list.simps bw_may.S_hat_def by auto
  qed
qed

 
lemma S_hat_edge_list_node_on_edge_list:
  assumes "\<pi> \<noteq> []"
  assumes "trans_tl (last \<pi>) = end"
  assumes "q \<in> bw_may.S_hat_edge_list \<pi> d_init_RN"
  shows "node_on_edge_list \<pi> q"
  using assms 
proof (induction \<pi>)
  case Nil
  then show ?case
    by auto
next
  case (Cons e \<pi>)
  from Cons(4) have 
    "q \<in> bw_may.S_hat_edge_list \<pi> d_init_RN - kill_set_RN e \<or>
     q \<in> gen_set_RN e"
    using bw_may.S_hat_def by auto
  then show ?case
  proof 
    assume q_Shat: "q \<in> bw_may.S_hat_edge_list \<pi> d_init_RN - kill_set_RN e"
    have "\<pi> \<noteq> [] \<or> \<pi> = []"
      by auto
    then show ?thesis
    proof
      assume "\<pi> \<noteq> []"
      then show "node_on_edge_list (e # \<pi>) q"
        using Cons(1,3)
        by (metis Diff_iff q_Shat append_Cons last.simps node_on_edge_list_def)
    next
      assume "\<pi> = []"
      then show "node_on_edge_list (e # \<pi>) q"
        using d_init_RN_def q_Shat
        by (metis Cons.prems(2) Diff_empty append.left_neutral append_Cons bw_may.S_hat_edge_list.simps(1) insertI1 insert_commute kill_set_RN.elims last_ConsL nodes_on_edge.elims node_on_edge_list_def singleton_iff trans_tl.simps)   
 qed
  next
    assume "q \<in> gen_set_RN e"
    then show ?thesis
      unfolding node_on_edge_list_def
      by (metis append.left_neutral append_Cons empty_iff gen_set_RN.elims insert_iff nodes_on_edge.simps)
  qed
qed

lemma node_on_edge_list_UNIV_S_hat_edge_list:
  assumes "\<pi> \<in> transition_list_path"
  assumes "\<pi> \<noteq> []"
  assumes "trans_tl (last \<pi>) = end"
  shows "{q. node_on_edge_list \<pi> q} = bw_may.S_hat_edge_list \<pi> d_init_RN"
  using assms node_on_edge_list_S_hat_edge_list S_hat_edge_list_node_on_edge_list by auto

lemma nodes_singleton_if_path_with_word_empty':
  assumes "(ss, w) \<in> path_with_word"
  assumes "w = []"
  shows "\<exists>l. ss = [l]"
using assms proof (induction rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 s)
  then show ?case
    by auto
next
  case (2 s' ss w s l)
  then show ?case
    by auto
qed

lemma nodes_singleton_if_path_with_word_empty:
  assumes "(ss, []) \<in> path_with_word"
  shows "\<exists>l. ss = [l]"
  using nodes_singleton_if_path_with_word_empty' assms by auto

lemma path_with_word_append_last:
  assumes "(ss,w) \<in> path_with_word"
  assumes "w \<noteq> []"
  shows "last (transition_list (s # ss, l # w)) = last (transition_list (ss, w))"
  using assms proof (induction rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 s')
  then show ?case
    by auto
next
  case (2 s'' ss w s' l)
  then show ?case
    by auto
qed

lemma last_trans_tl:
  assumes "(ss,w) \<in> path_with_word"
  assumes "w \<noteq> []"
  shows "last ss = trans_tl (last (LTS.transition_list (ss,w)))"
using assms proof (induction rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 s)
  then show ?case
    by auto
next
  case (2 s' ss w s l)
  show ?case
  proof (cases "w = []")
    case True
    then have "ss = []"
      using 2 nodes_singleton_if_path_with_word_empty by auto
    then show ?thesis
      using True 2 
      by auto
  next
    case False
    from 2 have "(s' # ss, w) \<in> path_with_word"
      by auto
    moreover
    have "w \<noteq> []"
      using False by auto
    ultimately
    have "last (s' # ss) = trans_tl (last (transition_list (s' # ss, w)))"
      using 2 by auto
    moreover
    have "last (transition_list (s' # ss, w)) =
        last (transition_list (s # s' # ss, l # w))"
      using path_with_word_append_last[of "s' # ss" w s l] \<open>w \<noteq> []\<close>
      using \<open>(s' # ss, w) \<in> LTS.path_with_word edges\<close> by auto
    ultimately
    show ?thesis
      by auto
  qed
qed

lemma nodes_tail_empty_if_path_with_word_empty:
  assumes "(ss,w) \<in> path_with_word"
  assumes "w \<noteq> []"
  shows "transition_list (ss,w) \<noteq> []"
using assms proof (induction rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 s)
  then show ?case by auto
next
  case (2 s' ss w s l)
  then show ?case
    by auto
qed

lemma empty_transition_list_if_empty_word:
  assumes "\<pi> \<in> path_with_word"
  assumes "snd \<pi> \<noteq> []"
  shows "transition_list \<pi> \<noteq> []"
  using assms nodes_tail_empty_if_path_with_word_empty by (cases \<pi>) auto

lemma two_nodes_if_nonempty_word:
  assumes "(ss, w) \<in> path_with_word"
  assumes "w \<noteq> []"
  shows "\<exists>s' s'' ss'. ss = s' # s'' # ss'"
using assms 
proof (induction rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 s)
  then show ?case 
    by auto
next
  case (2 s' ss w s l)
  then show ?case 
    by auto
qed

lemma path_with_word_empty_word:
  assumes "(ss', w) \<in> path_with_word"
  assumes "ss' = s' # ss"
  assumes "w = []"
  shows "ss = []"
using assms 
proof (induction rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 s)
  then show ?case 
    by auto
next
  case (2 s' ss w s l)
  then show ?case 
    by auto
qed

lemma transition_list_path_if_path_with_word:
  assumes "(ss,w) \<in> path_with_word"
  assumes "w \<noteq> []"
  shows "transition_list (ss,w) \<in> transition_list_path"
  using assms 
proof (induction rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 s)
  then show ?case
    by auto
next
  case (2 s' ss w s l)
  then show ?case
  proof (cases "w = []")
    case True
    then have s_empt: "ss = []"
      using 2(1) path_with_word_empty_word by blast 

    from 2 have "[(s, l, s')] \<in> transition_list_path"
      using LTS.transition_list_path.intros(1)[of s l s' edges] by auto
    then show ?thesis
      using True s_empt by auto
  next
    case False
    then obtain l' w' where w_eql: "w = l' # w'"
      by (cases w) auto
    obtain s'' ss' where ss_eql: "ss = s'' # ss'"
      using 2(1) False two_nodes_if_nonempty_word[of "s' #ss" w] by auto
    have "(s, l, s') \<in> edges"
      using 2 by auto
    moreover
    have "(s', l', s'') # transition_list (s'' # ss', w') \<in> transition_list_path"
      using 2 w_eql ss_eql by auto
    ultimately
    have "(s, l, s') # (s', l', s'') # transition_list (s'' # ss', w')
            \<in> transition_list_path"
      by (rule LTS.transition_list_path.intros(2)[of s l s'])
    then show ?thesis
      unfolding ss_eql w_eql by simp
  qed
qed

lemma nodes_on_path_S_hat_path:
  assumes "\<pi> \<in> path_with_word"
  assumes "snd \<pi> \<noteq> []"
  assumes "last (fst \<pi>) = end"
  shows "nodes_on_path \<pi> = bw_may.S_hat_path \<pi> d_init_RN"
proof -
  have "trans_tl (last (LTS.transition_list \<pi>)) = end"
    using assms(1,2,3) last_trans_tl[of "fst \<pi>" "snd \<pi>"] by auto
  moreover
  have "LTS.transition_list \<pi> \<noteq> []"
    using assms(1,2) empty_transition_list_if_empty_word using assms by auto
  moreover
  have "(LTS.transition_list \<pi>) \<in> transition_list_path"
    using assms(1) assms(2) transition_list_path_if_path_with_word[of "fst \<pi>" "snd \<pi>"] 
    by auto
  ultimately
  show ?thesis
    by (simp add: bw_may.S_hat_path_def node_on_edge_list_UNIV_S_hat_edge_list nodes_on_path_def)
qed

definition summarizes_RN where
  "summarizes_RN \<rho> \<longleftrightarrow> (\<forall>\<pi> d. \<pi> \<in> path_with_word_to end \<longrightarrow> d \<in> nodes_on_path \<pi> \<longrightarrow> 
                         \<rho> \<Turnstile>\<^sub>l\<^sub>h may\<langle>[Cst\<^sub>N (start_of \<pi>), Cst\<^sub>E d]\<rangle>.)"

theorem RN_sound:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t bw_may.ana_pg_bw_may s_BV"
  shows "summarizes_RN \<rho>"
proof -
  from assms have summary: "bw_may.summarizes_bw_may \<rho>"
    using bw_may.sound_ana_pg_bw_may[of \<rho>] by auto
  {
    fix \<pi> d
    assume \<pi>_path_to_end: "\<pi> \<in> path_with_word_to end"
    assume d_on_path: "d \<in> nodes_on_path \<pi>"
    have \<pi>_path: "\<pi> \<in> LTS.path_with_word edges"
      using \<pi>_path_to_end edges_def edges_def by auto
    have \<pi>_end: "end_of \<pi> = end"
      using \<pi>_path_to_end end_def end_def by fastforce
    then have "last (fst \<pi>) = end"
      using end_def end_def end_of_def by auto
    then have "d \<in> bw_may.S_hat_path \<pi> d_init_RN"
      using \<pi>_path_to_end d_on_path nodes_on_path_S_hat_path[of \<pi>] Nil_is_append_conv list.discI 
        mem_Collect_eq node_on_edge_list_def nodes_on_path_def prod.exhaust_sel 
        transition_list.simps(2) nodes_singleton_if_path_with_word_empty
      by (metis (mono_tags, lifting))
    then have "\<rho> \<Turnstile>\<^sub>l\<^sub>h may\<langle>[Cst\<^sub>N (start_of \<pi>), Cst\<^sub>E d]\<rangle>."
      using \<pi>_path \<pi>_end summary unfolding bw_may.summarizes_bw_may_def mem_Collect_eq by metis
  }

  then show ?thesis
    unfolding summarizes_RN_def by auto
qed

end

end
