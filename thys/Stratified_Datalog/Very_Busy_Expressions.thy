theory Very_Busy_Expressions imports Available_Expressions begin

\<comment> \<open>We encode the Very Busy Expressions analysis into Datalog. First we define the analysis, then
    we encode it into Datalog using our Bit-Vector Framework locale. We also prove 
    the encoding correct. \<close>

section \<open>Very Busy Expressions\<close>

definition vbexp_edge_list :: "('n,'v action) edge list \<Rightarrow> 'v arith \<Rightarrow> bool" where
  "vbexp_edge_list \<pi> a = (\<exists>\<pi>1 \<pi>2 e. \<pi> = \<pi>1 @ [e] @ \<pi>2 \<and> a \<in> aexp_edge e \<and> (\<forall>e' \<in> set \<pi>1. fv_arith a \<inter> def_edge e' = {}))"

definition vbexp_path :: "'n list \<times> 'v action list \<Rightarrow> 'v arith set" where
  "vbexp_path \<pi> = {a. vbexp_edge_list (LTS.transition_list \<pi>) a}"

locale analysis_VB = finite_program_graph pg 
  for pg :: "('n::finite,'v::finite action) program_graph"
begin

interpretation LTS edges .

definition analysis_dom_VB :: "'v arith set" where
  "analysis_dom_VB = aexp_pg pg"

lemma finite_analysis_dom_VB: "finite analysis_dom_VB"
proof -
  have "finite (\<Union> (aexp_edge ` edges))"
    by (metis aexp_edge.elims finite_UN finite_aexp_edge finite_program_graph_axioms 
        finite_program_graph_def)
  then show ?thesis
    unfolding analysis_dom_VB_def edges_def by auto
qed
 
fun kill_set_VB :: "('n,'v action) edge \<Rightarrow> 'v arith set" where
  "kill_set_VB (q\<^sub>o, x ::= a, q\<^sub>s) = {a'. x \<in> fv_arith a'}"
| "kill_set_VB (q\<^sub>o, Bool b, q\<^sub>s) = {}"
| "kill_set_VB (v, Skip, vc) = {}"

fun gen_set_VB :: "('n,'v action) edge \<Rightarrow> 'v arith set" where
  "gen_set_VB (q\<^sub>o, x ::= a, q\<^sub>s) = ae_arith a"
| "gen_set_VB (q\<^sub>o, Bool b, q\<^sub>s) = ae_boolean b"
| "gen_set_VB (v, Skip, vc) = {}"

definition d_init_VB :: "'v arith set" where
  "d_init_VB = {}"

interpretation bw_must: analysis_BV_backward_must pg analysis_dom_VB kill_set_VB gen_set_VB d_init_VB
  using analysis_VB_axioms analysis_VB_def
  by (metis analysis_BV_backward_must_axioms_def analysis_BV_backward_must_def bot.extremum 
      d_init_VB_def finite_analysis_dom_VB)

lemma aexp_edge_list_S_hat_edge_list: 
  assumes "a \<in> aexp_edge (q, \<alpha>, q')"
  assumes "fv_arith a \<inter> def_edge (q, \<alpha>, q') = {}"
  shows "a \<in> bw_must.S_hat (q, \<alpha>, q') R"
  using assms unfolding bw_must.S_hat_def by (cases \<alpha>) auto

lemma empty_inter_fv_arith_def_edge:
  assumes "vbexp_edge_list (e # \<pi>) a"
  shows "fv_arith a \<inter> def_edge e = {} \<or> a \<in> aexp_edge e"
proof -
  from assms(1) obtain \<pi>1 \<pi>2 e' where \<pi>1_\<pi>2_e'_p:
    "e # \<pi> = \<pi>1 @ [e'] @ \<pi>2"
    "a \<in> aexp_edge e'"
    "(\<forall>e''\<in>set \<pi>1. fv_arith a \<inter> def_edge e'' = {})"
    unfolding vbexp_edge_list_def by auto
  from this(1) have "e \<in> set (\<pi>1 @ [e'])"
    by (metis append_self_conv2 hd_append2 list.sel(1) list.set_sel(1) snoc_eq_iff_butlast) 
  then have "e \<in> set \<pi>1 \<or> e = e'"
    by auto
  then show "fv_arith a \<inter> def_edge e = {} \<or> a \<in> aexp_edge e"
  proof
    assume "e \<in> set \<pi>1"
    then have "fv_arith a \<inter> def_edge e = {}" 
      using \<pi>1_\<pi>2_e'_p(3) by auto
    then show "fv_arith a \<inter> def_edge e = {} \<or> a \<in> aexp_edge e" 
       by auto
  next
    assume "e = e'"
    then have "a \<in> aexp_edge e"
      using \<pi>1_\<pi>2_e'_p(2) by auto 
    then show "fv_arith a \<inter> def_edge e = {}  \<or> a \<in> aexp_edge e"
      by auto 
  qed
qed

lemma vbexp_edge_list_Cons:
  assumes "vbexp_edge_list (e # \<pi>) a"
  shows "vbexp_edge_list \<pi> a \<or> a \<in> aexp_edge e"
proof -
  from assms(1) obtain \<pi>1 \<pi>2 e' where \<pi>1_\<pi>2_e'_p:
    "e # \<pi> = \<pi>1 @ [e'] @ \<pi>2"
    "a \<in> aexp_edge e'"
    "(\<forall>e''\<in>set \<pi>1. fv_arith a \<inter> def_edge e'' = {})"
    unfolding vbexp_edge_list_def by auto
  from this(1) have "e \<in> set (\<pi>1 @ [e'])"
    by (metis append_assoc hd_append2 list.sel(1) list.set_sel(1) snoc_eq_iff_butlast)
  then have "e = e' \<or> e \<in> set \<pi>1"
    by auto
  then show ?thesis
  proof
    assume "e = e'"
    then have "a \<in> aexp_edge e"
      using \<pi>1_\<pi>2_e'_p by auto
    then show ?thesis 
      by auto
  next
    assume "e \<in> set \<pi>1"
    then have "\<pi> = tl \<pi>1 @ [e'] @ \<pi>2"
      using \<pi>1_\<pi>2_e'_p by (metis equals0D list.sel(3) set_empty tl_append2) 
    moreover
    have "a \<in> aexp_edge e'"
      by (simp add: \<pi>1_\<pi>2_e'_p(2))
    moreover
    have "(\<forall>e''\<in> set (tl \<pi>1). fv_arith a \<inter> def_edge e'' = {})"
      by (metis \<pi>1_\<pi>2_e'_p(3) list.set_sel(2) tl_Nil)
    ultimately
    have "vbexp_edge_list \<pi> a"
      unfolding vbexp_edge_list_def by metis
    then show ?thesis
      by auto
  qed
qed

lemma gen_set_VB_is_aexp_edge:
  "a \<in> gen_set_VB e \<longleftrightarrow> a \<in> aexp_edge e"
proof -
  obtain q \<alpha> q' where e_split: "e = (q, \<alpha>, q')"
    by (cases e)
  then show ?thesis
    by (cases \<alpha>) auto
qed

lemma empty_inter_fv_arith_def_edge'':
  "a \<notin> kill_set_VB e \<longleftrightarrow> fv_arith a \<inter> def_edge e = {}"
proof -
  obtain q \<alpha> q' where e_split: "e = (q, \<alpha>, q')"
    by (cases e)
  then show ?thesis
    by (cases \<alpha>) auto
qed

lemma S_hat_edge_list_aexp_edge_list: 
  assumes "a \<in> bw_must.S_hat_edge_list \<pi> d_init_VB"
  shows "vbexp_edge_list \<pi> a"
  using assms
proof (induction \<pi>)
  case Nil
  then show ?case 
    unfolding d_init_VB_def by auto
next
  case (Cons e \<pi>)
  from Cons(2) have "a \<in> (bw_must.S_hat_edge_list \<pi> d_init_VB - kill_set_VB e) \<or> a \<in> gen_set_VB e"
    using bw_must.S_hat_def by auto
  then show ?case
  proof 
    assume a_S_hat: "a \<in> bw_must.S_hat_edge_list \<pi> d_init_VB - kill_set_VB e"
    then have "vbexp_edge_list \<pi> a"
      using Cons by auto
    moreover
    from a_S_hat have "a \<notin> kill_set_VB e"
      by auto
    then have "fv_arith a \<inter> def_edge e = {}"
      using empty_inter_fv_arith_def_edge'' by auto
    ultimately show "vbexp_edge_list (e # \<pi>) a"
      unfolding vbexp_edge_list_def by (metis Cons_eq_appendI set_ConsD)
  next
    assume a_gen: "a \<in> gen_set_VB e"
    then have "a \<in> aexp_edge e"
      using gen_set_VB_is_aexp_edge by auto
    then show "vbexp_edge_list (e # \<pi>) a"
      unfolding vbexp_edge_list_def by (metis append_Cons append_Nil empty_iff empty_set)
  qed
qed

lemma aexp_edge_list_S_hat_edge_list': 
  assumes "vbexp_edge_list \<pi> a"
  shows "a \<in> bw_must.S_hat_edge_list \<pi> d_init_VB"
  using assms
proof (induction \<pi>)
  case Nil
  then have False 
    unfolding vbexp_edge_list_def by auto
  then show ?case
    by metis
next
  case (Cons e \<pi>)
  have fvae: "fv_arith a \<inter> def_edge e = {} \<or> a \<in> aexp_edge e"
    using Cons(2) empty_inter_fv_arith_def_edge by force

  have "vbexp_edge_list \<pi> a \<or> a \<in> aexp_edge e"
    using Cons(2)
    by (simp add: vbexp_edge_list_Cons)
  then show ?case
  proof
    assume "vbexp_edge_list \<pi> a"
    then have "a \<in> bw_must.S_hat_edge_list \<pi> d_init_VB"
      using Cons by auto
    moreover
    have "a \<notin> kill_set_VB e \<or> a \<in> gen_set_VB e"
      using fvae empty_inter_fv_arith_def_edge'' gen_set_VB_is_aexp_edge by auto
    ultimately
    show ?case
      using bw_must.S_hat_def by auto
  next
    assume "a \<in> aexp_edge e"
    then have "a \<in> gen_set_VB e"
      using fvae empty_inter_fv_arith_def_edge'' gen_set_VB_is_aexp_edge by auto
    then show ?case
      using bw_must.S_hat_def by auto
  qed
qed

lemma vbexp_edge_list_S_hat_edge_list_iff: 
  "vbexp_edge_list \<pi> a \<longleftrightarrow> a \<in> bw_must.S_hat_edge_list \<pi> d_init_VB"
  using S_hat_edge_list_aexp_edge_list aexp_edge_list_S_hat_edge_list' by blast

lemma vbexp_path_S_hat_path_iff: 
  "a \<in> vbexp_path \<pi> \<longleftrightarrow> a \<in> bw_must.S_hat_path \<pi> d_init_VB"
  by (simp add: bw_must.S_hat_path_def vbexp_edge_list_S_hat_edge_list_iff vbexp_path_def)

definition summarizes_VB where
  "summarizes_VB \<rho> \<longleftrightarrow>
     (\<forall>q d.
         \<rho> \<Turnstile>\<^sub>l\<^sub>h must\<langle>[q, d]\<rangle>. \<longrightarrow>
          (\<forall>\<pi>. \<pi> \<in> path_with_word_from_to (the_Node\<^sub>i\<^sub>d q) end \<longrightarrow> the_Elem\<^sub>i\<^sub>d d \<in> vbexp_path \<pi>))"

theorem VB_sound:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (bw_must.ana_pg_bw_must) s_BV"
  shows "summarizes_VB \<rho>"
proof -
  from assms have "bw_must.summarizes_bw_must \<rho>"
    using bw_must.sound_ana_pg_bw_must by auto
  then show ?thesis
    unfolding summarizes_VB_def bw_must.summarizes_bw_must_def edges_def edges_def
      end_def end_def vbexp_path_S_hat_path_iff start_def start_def by force
qed

end

end
