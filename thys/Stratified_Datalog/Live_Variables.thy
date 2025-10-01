theory Live_Variables imports Reaching_Definitions begin

\<comment> \<open>We encode the Live Variables analysis into Datalog. First we define the analysis, then
    we encode it into Datalog using our Bit-Vector Framework locale. We also prove 
    the encoding correct. \<close>


section \<open>Live Variables Analysis\<close>

fun use_action :: "'v action \<Rightarrow> 'v set" where
  "use_action (x ::= a) = fv_arith a"
| "use_action (Bool b) = fv_boolean b"
| "use_action Skip = {}"

fun use_edge :: "('n,'v action) edge \<Rightarrow> 'v set" where
  "use_edge (q1, \<alpha>, q2) = use_action \<alpha>"

definition use_edge_list :: "('n,'v action) edge list \<Rightarrow> 'v \<Rightarrow> bool" where
  "use_edge_list \<pi> x = (\<exists>\<pi>1 \<pi>2 e. \<pi> = \<pi>1 @ [e] @ \<pi>2 \<and> 
                                  x \<in> use_edge e \<and> 
                                  (\<not>(\<exists>e' \<in> set \<pi>1. x \<in> def_edge e')))"

definition use_path :: "'n list \<times> 'v action list \<Rightarrow> 'v set" where
  "use_path \<pi> = {x. use_edge_list (LTS.transition_list \<pi>) x}"

locale analysis_LV = finite_program_graph pg
  for pg :: "('n::finite,'v::finite action) program_graph" 
begin

interpretation LTS edges .

definition analysis_dom_LV :: "'v set" where
  "analysis_dom_LV = UNIV"

fun kill_set_LV :: "('n,'v action) edge \<Rightarrow> 'v set" where
  "kill_set_LV (q\<^sub>o, x ::= a, q\<^sub>s) = {x}"
| "kill_set_LV (q\<^sub>o, Bool b, q\<^sub>s) = {}"
| "kill_set_LV (v, Skip, vc) = {}"

fun gen_set_LV :: "('n,'v action) edge \<Rightarrow> 'v set" where
  "gen_set_LV (q\<^sub>o, x ::= a, q\<^sub>s) = fv_arith a"
| "gen_set_LV (q\<^sub>o, Bool b, q\<^sub>s) = fv_boolean b"
| "gen_set_LV (v, Skip, vc) = {}"

definition d_init_LV :: "'v set" where
  "d_init_LV = {}"

interpretation bw_may: analysis_BV_backward_may pg analysis_dom_LV kill_set_LV gen_set_LV d_init_LV
  using analysis_BV_backward_may.intro analysis_LV_axioms analysis_LV_def analysis_dom_LV_def 
    finite_UNIV subset_UNIV analysis_BV_backward_may_axioms_def finite_program_graph_def by metis

lemma use_edge_list_S_hat_edge_list: 
  assumes "use_edge_list \<pi> x"
  shows "x \<in> bw_may.S_hat_edge_list \<pi> d_init_LV"
  using assms
proof (induction \<pi>)
  case Nil
  then have False 
    unfolding use_edge_list_def by auto
  then show ?case
    by metis
next
  case (Cons e \<pi>)
  note Cons_inner = Cons
  from Cons(2) have "\<exists>\<pi>1 \<pi>2 e'. e # \<pi> = \<pi>1 @ [e'] @ \<pi>2 \<and> 
                                x \<in> use_edge e' \<and> 
                                \<not> (\<exists>e''\<in>set \<pi>1. x \<in> def_edge e'')"
    unfolding use_edge_list_def by auto
  then obtain \<pi>1 \<pi>2 e' where \<pi>1_\<pi>2_e'_p:
    "e # \<pi> = \<pi>1 @ [e'] @ \<pi>2"
    "x \<in> use_edge e'"
    "\<not>(\<exists>e''\<in>set \<pi>1. x \<in> def_edge e'')"
    by auto
  then show ?case
  proof (cases \<pi>1)
    case Nil
    have "e = e'"
      using \<pi>1_\<pi>2_e'_p(1) Nil by auto
    then have x_used_a: "x \<in> use_edge e"
      using \<pi>1_\<pi>2_e'_p(2) by auto
    obtain p \<alpha> q where a_split: "e = (p, \<alpha>, q)"
      by (cases e)
    show ?thesis
      using x_used_a bw_may.S_hat_def a_split by (cases \<alpha>) auto
  next
    case (Cons hd_\<pi>1 tl_\<pi>1)
    obtain p \<alpha> q where e_split: "e' = (p, \<alpha>, q)"
      by (cases e')
    have "(\<pi> = tl_\<pi>1 @ (p, \<alpha>, q) # \<pi>2) \<and> x \<in> use_action \<alpha> \<and> (\<forall>e'\<in>set tl_\<pi>1. x \<notin> def_edge e')"
      using Cons \<pi>1_\<pi>2_e'_p e_split by auto
    then have "use_edge_list \<pi> x"
      unfolding use_edge_list_def by force
    then have x_in_S_hat_\<pi>: "x \<in> bw_may.S_hat_edge_list \<pi> d_init_LV"
      using Cons_inner by auto
    have "e \<in> set \<pi>1"
      using \<pi>1_\<pi>2_e'_p(1) Cons(1) by auto
    then have x_not_def_a: "\<not>x \<in> def_edge e"
      using \<pi>1_\<pi>2_e'_p(3) by auto

    obtain p' \<alpha>' q' where a_split: "e = (p', \<alpha>', q')"
      by (cases e)

    show ?thesis
    proof (cases "x \<in> kill_set_LV e")
      case True
      show ?thesis
        using True a_split x_not_def_a by (cases \<alpha>'; force)
    next
      case False
      then show ?thesis
        by (simp add: bw_may.S_hat_def x_in_S_hat_\<pi>)
    qed
  qed
qed

lemma S_hat_edge_list_use_edge_list:
  assumes "x \<in> bw_may.S_hat_edge_list \<pi> d_init_LV"
  shows "use_edge_list \<pi> x"
  using assms 
proof (induction \<pi>)
  case Nil
  then have False
    using d_init_LV_def by auto
  then show ?case
    by metis
next
  case (Cons e \<pi>)
  from Cons(2) have "x \<in> bw_may.S_hat_edge_list \<pi> d_init_LV - kill_set_LV e \<union> gen_set_LV e"
    unfolding bw_may.S_hat_edge_list.simps unfolding bw_may.S_hat_def by auto
  then show ?case
  proof
    assume a: "x \<in> bw_may.S_hat_edge_list \<pi> d_init_LV - kill_set_LV e"
    then have "x \<in> bw_may.S_hat_edge_list \<pi> d_init_LV"
      by auto
    then have "use_edge_list \<pi> x"
      using Cons by auto
    then have "\<exists>\<pi>1 \<pi>2 e'. \<pi> = \<pi>1 @ [e'] @ \<pi>2 \<and> x \<in> use_edge e' \<and> \<not>(\<exists>e''\<in>set \<pi>1. x \<in> def_edge e'')"
      unfolding use_edge_list_def by auto
    then obtain \<pi>1 \<pi>2 e' where \<pi>1_\<pi>2_e'_p:
      "\<pi> = \<pi>1 @ [e'] @ \<pi>2"
      "x \<in> use_edge e'"
      "\<not>(\<exists>e''\<in>set \<pi>1. x \<in> def_edge e'')"
      by auto
    obtain q1 \<alpha> q2 where e_split: "e = (q1, \<alpha>, q2)"
      by (cases e) auto
    from a have "x \<notin> kill_set_LV e"
      by auto
    then have x_not_killed: "x \<notin> kill_set_LV (q1, \<alpha>, q2)"
      using e_split by auto
    have "use_edge_list ((q1, \<alpha>, q2) # \<pi>) x"
    proof (cases \<alpha>)
      case (Asg y exp)
      then have "x \<notin> kill_set_LV (q1, y ::= exp, q2)"
        using x_not_killed by auto
      then have x_not_y: "x \<noteq> y"
        by auto
      have "(q1, y ::= exp, q2) # \<pi> = ((q1, y ::= exp, q2) # \<pi>1) @ [e'] @ \<pi>2"
        using \<pi>1_\<pi>2_e'_p by force
      moreover
      have "\<not> (\<exists>e'\<in>set ((q1, y ::= exp, q2) # \<pi>1). x \<in> def_edge e')"
        using \<pi>1_\<pi>2_e'_p x_not_y by force
      ultimately
      have "use_edge_list ((q1, y ::= exp, q2) # \<pi>) x"
        unfolding use_edge_list_def using \<pi>1_\<pi>2_e'_p x_not_y by metis
      then show ?thesis
        by (simp add: Asg)
    next
      case (Bool b)
      have "(q1, Bool b, q2) # \<pi> = ((q1, Bool b, q2) # \<pi>1) @ [e'] @ \<pi>2"
        using \<pi>1_\<pi>2_e'_p unfolding use_edge_list_def by auto
      moreover
      have "\<not> (\<exists>e'\<in>set ((q1, Bool b, q2) # \<pi>1). x \<in> def_edge e')"
        using \<pi>1_\<pi>2_e'_p unfolding use_edge_list_def by auto
      ultimately
      have "use_edge_list ((q1, Bool b, q2) # \<pi>) x"
        unfolding use_edge_list_def using \<pi>1_\<pi>2_e'_p by metis
      then show ?thesis
        using Bool by auto
    next
      case Skip
      have "(q1, Skip, q2) # \<pi> = ((q1, Skip, q2) # \<pi>1) @ [e'] @ \<pi>2"
        using \<pi>1_\<pi>2_e'_p unfolding use_edge_list_def by auto
      moreover
      have "\<not> (\<exists>e'\<in>set ((q1, Skip, q2) # \<pi>1). x \<in> def_edge e')"
        using \<pi>1_\<pi>2_e'_p unfolding use_edge_list_def by auto
      ultimately
      have "use_edge_list ((q1, Skip, q2) # \<pi>) x"
        unfolding use_edge_list_def using \<pi>1_\<pi>2_e'_p by metis
      then show ?thesis
        using Skip by auto
    qed
    then show "use_edge_list (e # \<pi>) x"
      using e_split by auto
  next
    assume a: "x \<in> gen_set_LV e"
    obtain p \<alpha> q where a_split: "e = (p, \<alpha>, q)"
      by (cases e)
    have "use_edge_list ((p, \<alpha>, q) # \<pi>) x"
      using a a_split unfolding use_edge_list_def by (cases \<alpha>; force)
    then show "use_edge_list (e # \<pi>) x"
      using a_split by auto
  qed
qed

lemma use_edge_list_set_S_hat_edge_list: 
  "{x. use_edge_list \<pi> x} = bw_may.S_hat_edge_list \<pi> d_init_LV"
  using use_edge_list_S_hat_edge_list S_hat_edge_list_use_edge_list by auto

lemma use_path_S_hat_path: "use_path \<pi> = bw_may.S_hat_path \<pi> d_init_LV"
  by (simp add: use_edge_list_set_S_hat_edge_list bw_may.S_hat_path_def use_path_def)

definition summarizes_LV :: "(pred, ('n,'v action,'v) cst) pred_val \<Rightarrow> bool" where
  "summarizes_LV \<rho> \<longleftrightarrow> (\<forall>\<pi> d. \<pi> \<in> path_with_word_to end \<longrightarrow> d \<in> use_path \<pi> \<longrightarrow> 
                         \<rho> \<Turnstile>\<^sub>l\<^sub>h may\<langle>[Cst\<^sub>N (start_of \<pi>), Cst\<^sub>E d]\<rangle>.)"

theorem LV_sound:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t bw_may.ana_pg_bw_may s_BV"
  shows "summarizes_LV \<rho>"
proof -
  from assms have "bw_may.summarizes_bw_may \<rho>"
    using bw_may.sound_ana_pg_bw_may[of \<rho>] by auto
  then show ?thesis
    unfolding summarizes_LV_def bw_may.summarizes_bw_may_def edges_def edges_def
      end_def end_def use_path_S_hat_path by blast
qed

end

end
