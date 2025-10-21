theory Available_Expressions imports Reaching_Definitions begin

\<comment> \<open>We encode the Available Expressions analysis into Datalog. First we define the analysis, then
    we encode it into Datalog using our Bit-Vector Framework locale. We also prove 
    the encoding correct. \<close>

section \<open>Available Expressions\<close>

fun ae_arith :: "'v arith \<Rightarrow> 'v arith set" where
  "ae_arith (Integer i) = {}"
| "ae_arith (Arith_Var v) = {}"
| "ae_arith (Arith_Op a1 opr a2) = ae_arith a1 \<union> ae_arith a1 \<union> {Arith_Op a1 opr a2}"
| "ae_arith (Minus a) = ae_arith a"

lemma finite_ae_arith: "finite (ae_arith a)"
  by (induction a) auto

fun ae_boolean :: "'v boolean \<Rightarrow> 'v arith set" where
  "ae_boolean true = {}"
| "ae_boolean false = {}"
| "ae_boolean (Rel_Op a1 opr a2) = ae_arith a1 \<union> ae_arith a2"
| "ae_boolean (Bool_Op b1 opr b2) = ae_boolean b1 \<union> ae_boolean b2"
| "ae_boolean (Neg b) = ae_boolean b"

lemma finite_ae_boolean: "finite (ae_boolean b)"
  using finite_ae_arith by (induction b) auto

fun aexp_action :: "'v action \<Rightarrow> 'v arith set" where
  "aexp_action (x ::= a) = ae_arith a"
| "aexp_action (Bool b) = ae_boolean b"
| "aexp_action Skip = {}"

lemma finite_aexp_action: "finite (aexp_action \<alpha>)"
  using finite_ae_arith finite_ae_boolean by (cases \<alpha>) auto

fun aexp_edge :: "('n,'v action) edge \<Rightarrow> 'v arith set" where
  "aexp_edge (q1, \<alpha>, q2) = aexp_action \<alpha>"

lemma finite_aexp_edge: "finite (aexp_edge (q1, \<alpha>, q2))"
  using finite_aexp_action by auto

fun aexp_pg :: "('n,'v action) program_graph \<Rightarrow> 'v arith set" where
  "aexp_pg pg = \<Union>(aexp_edge ` (fst pg))"

definition aexp_edge_list :: "('n,'v action) edge list \<Rightarrow> 'v arith \<Rightarrow> bool" where
  "aexp_edge_list \<pi> a = (\<exists>\<pi>1 \<pi>2 e. \<pi> = \<pi>1 @ [e] @ \<pi>2 \<and> a \<in> aexp_edge e \<and> (\<forall>e' \<in> set ([e] @ \<pi>2). fv_arith a \<inter> def_edge e' = {}))"

definition aexp_path :: "'n list \<times> 'v action list \<Rightarrow> 'v arith set" where
  "aexp_path \<pi> = {a. aexp_edge_list (transition_list \<pi>) a}"


locale analysis_AE = finite_program_graph pg 
  for pg :: "('n::finite,'v::finite action) program_graph"
begin

interpretation LTS edges .

definition analysis_dom_AE :: "'v arith set" where
  "analysis_dom_AE = aexp_pg pg"

lemma finite_analysis_dom_AE: "finite analysis_dom_AE"
proof -
  have "finite (\<Union> (aexp_edge ` edges))"
    by (metis aexp_edge.elims finite_UN finite_aexp_edge finite_program_graph_axioms 
        finite_program_graph_def)
  then show ?thesis
    unfolding analysis_dom_AE_def using edges_def by force 
qed

fun kill_set_AE :: "('n,'v action) edge \<Rightarrow> 'v arith set" where
  "kill_set_AE (q\<^sub>o, x ::= a, q\<^sub>s) = {a'. x \<in> fv_arith a'}"
| "kill_set_AE (q\<^sub>o, Bool b, q\<^sub>s) = {}"
| "kill_set_AE (v, Skip, vc) = {}"

fun gen_set_AE :: "('n,'v action) edge \<Rightarrow> 'v arith set" where
  "gen_set_AE (q\<^sub>o, x ::= a, q\<^sub>s) = {a'. a' \<in> ae_arith a \<and> x \<notin> fv_arith a'}"
| "gen_set_AE (q\<^sub>o, Bool b, q\<^sub>s) = ae_boolean b"
| "gen_set_AE (v, Skip, vc) = {}"

definition d_init_AE :: "'v arith set" where
  "d_init_AE = {}"

interpretation fw_must: analysis_BV_forward_must pg analysis_dom_AE kill_set_AE gen_set_AE d_init_AE
  using analysis_BV_forward_must.intro analysis_AE_axioms analysis_AE_def
    d_init_AE_def empty_subsetI finite_analysis_dom_AE analysis_BV_forward_must_axioms.intro
  by metis

lemma aexp_edge_list_S_hat_edge_list: 
  assumes "a \<in> aexp_edge (q, \<alpha>, q')"
  assumes "fv_arith a \<inter> def_edge (q, \<alpha>, q') = {}"
  shows "a \<in> fw_must.S_hat (q, \<alpha>, q') R"
  using assms unfolding fw_must.S_hat_def by (cases \<alpha>) auto

lemma empty_inter_fv_arith_def_edge:
  assumes "aexp_edge_list (\<pi> @ [e]) a"
  shows "fv_arith a \<inter> def_edge e = {}"
proof -
  from assms(1) obtain \<pi>1 \<pi>2 e' where \<pi>1_\<pi>2_e'_p:
    "\<pi> @ [e] = \<pi>1 @ [e'] @ \<pi>2" 
    "a \<in> aexp_edge e'"
    "(\<forall>e''\<in>set ([e'] @ \<pi>2). fv_arith a \<inter> def_edge e'' = {})"
    unfolding aexp_edge_list_def by auto
  from this(1) have "e \<in> set ([e'] @ \<pi>2)"
    by (metis append_is_Nil_conv last_appendR last_in_set snoc_eq_iff_butlast) 
  then show "fv_arith a \<inter> def_edge e = {}"
    using \<pi>1_\<pi>2_e'_p(3) by auto
qed

lemma aexp_edge_list_append_singleton:
  assumes "aexp_edge_list (\<pi> @ [e]) a"
  shows "aexp_edge_list \<pi> a \<or> a \<in> aexp_edge e"
proof -
  from assms(1) obtain \<pi>1 \<pi>2 e' where \<pi>1_\<pi>2_e'_p:
    "\<pi> @ [e] = \<pi>1 @ [e'] @ \<pi>2" 
    "a \<in> aexp_edge e'"
    "(\<forall>e''\<in>set ([e'] @ \<pi>2). fv_arith a \<inter> def_edge e'' = {})"
    unfolding aexp_edge_list_def by auto
  from this(1) have "e \<in> set ([e'] @ \<pi>2)"
    by (metis append_is_Nil_conv last_appendR last_in_set snoc_eq_iff_butlast)
  then have "e = e' \<or> e \<in> set \<pi>2"
    by auto
  then show ?thesis
  proof
    assume "e = e'"
    then have "a \<in> aexp_edge e"
      using \<pi>1_\<pi>2_e'_p by auto
    then show ?thesis 
      by auto
  next
    assume "e \<in> set \<pi>2"
    then have "\<pi> = \<pi>1 @ [e'] @ (butlast \<pi>2)"
      by (metis \<pi>1_\<pi>2_e'_p(1) append_is_Nil_conv butlast_append butlast_snoc 
          in_set_conv_decomp_first)
    moreover
    have "a \<in> aexp_edge e'"
      by (simp add: \<pi>1_\<pi>2_e'_p(2))
    moreover
    have "(\<forall>e''\<in>set ([e'] @ butlast \<pi>2). fv_arith a \<inter> def_edge e'' = {})"
      by (metis \<pi>1_\<pi>2_e'_p(3) butlast.simps(1) butlast_append in_set_butlastD)
    ultimately
    have "aexp_edge_list \<pi> a"
      unfolding aexp_edge_list_def by blast
    then show ?thesis
      by auto
  qed
qed

lemma gen_set_AE_subset_aexp_edge:
  assumes "a \<in> gen_set_AE e"
  shows "a \<in> aexp_edge e"
proof -
  obtain q \<alpha> q' where "e = (q, \<alpha>, q')"
    by (cases e)
  then show ?thesis
    using assms by (cases \<alpha>) auto
qed

lemma empty_inter_fv_arith_def_edge':
  assumes "a \<in> gen_set_AE e"
  shows "fv_arith a \<inter> def_edge e = {}"
proof -
  obtain q \<alpha> q' where "e = (q, \<alpha>, q')"
    by (cases e)
  then show ?thesis
    using assms by (cases \<alpha>) auto
qed

lemma empty_inter_fv_arith_def_edge'':
  assumes "a \<notin> kill_set_AE e"
  shows "fv_arith a \<inter> def_edge e = {}"
proof -
  obtain q \<alpha> q' where "e = (q, \<alpha>, q')"
    by (cases e)
  then show ?thesis
    using assms by (cases \<alpha>) auto
qed

lemma S_hat_edge_list_aexp_edge_list: 
  assumes "a \<in> fw_must.S_hat_edge_list \<pi> d_init_AE"
  shows "aexp_edge_list \<pi> a"
  using assms 
proof (induction \<pi> rule: rev_induct)
  case Nil
  then show ?case 
    unfolding d_init_AE_def by auto
next
  case (snoc e \<pi>)
  from snoc(2) have "a \<in> (fw_must.S_hat_edge_list \<pi> d_init_AE - kill_set_AE e) \<or> a \<in> gen_set_AE e"
    using fw_must.S_hat_def by auto
  then show ?case
  proof 
    assume a_S_hat: "a \<in> fw_must.S_hat_edge_list \<pi> d_init_AE - kill_set_AE e"
    then have "aexp_edge_list \<pi> a"
      using snoc by auto
    moreover
    from a_S_hat have "a \<notin> kill_set_AE e"
      by auto
    then have "fv_arith a \<inter> def_edge e = {}"
      using empty_inter_fv_arith_def_edge'' by auto
    ultimately show "aexp_edge_list (\<pi> @ [e]) a"
      unfolding aexp_edge_list_def by force
  next
    assume a_gen: "a \<in> gen_set_AE e"
    then have "a \<in> aexp_edge e"
      using gen_set_AE_subset_aexp_edge by auto
    moreover
    from a_gen have "(fv_arith a \<inter> def_edge e = {})"
      using empty_inter_fv_arith_def_edge' by auto
    ultimately
    show "aexp_edge_list (\<pi> @ [e]) a"
      unfolding aexp_edge_list_def
      by (metis append_Nil2 empty_iff empty_set insert_iff list.set(2)) 
  qed
qed

lemma not_kill_set_AE_iff_fv_arith_def_edge_disjoint:
  "fv_arith a \<inter> def_edge e = {} \<longleftrightarrow> a \<notin> kill_set_AE e"
proof -
  obtain q \<alpha> q' where e_split: "e = (q, \<alpha>, q')"
    by (cases e)
  then show ?thesis
     by (cases \<alpha>) auto
qed

lemma gen_set_AE_AE_iff_fv_arith_def_edge_disjoint_and_aexp_edge:
  "a \<in> aexp_edge e \<and> fv_arith a \<inter> def_edge e = {} \<longleftrightarrow> a \<in> gen_set_AE e"
proof -
  obtain q \<alpha> q' where e_split: "e = (q, \<alpha>, q')"
    by (cases e)
  then show ?thesis
    by (cases \<alpha>) auto
qed

lemma aexp_edge_list_S_hat_edge_list': 
  assumes "aexp_edge_list \<pi> a"
  shows "a \<in> fw_must.S_hat_edge_list \<pi> d_init_AE"
  using assms
proof (induction \<pi> rule: rev_induct)
  case Nil
  then have False 
    unfolding aexp_edge_list_def by auto
  then show ?case
    by metis
next
  case (snoc e \<pi>)
  have fvae: "fv_arith a \<inter> def_edge e = {}"
    using snoc(2) empty_inter_fv_arith_def_edge by metis

  have "aexp_edge_list \<pi> a \<or> a \<in> aexp_edge e"
    using snoc(2)
    by (simp add: aexp_edge_list_append_singleton)
  then show ?case
  proof
    assume "aexp_edge_list \<pi> a"
    then have "a \<in> fw_must.S_hat_edge_list \<pi> d_init_AE"
      using snoc by auto
    moreover
    have "a \<notin> kill_set_AE e"
      using fvae not_kill_set_AE_iff_fv_arith_def_edge_disjoint by auto
    ultimately
    show ?case
      using fw_must.S_hat_def by auto
  next
    assume "a \<in> aexp_edge e"
    then have "a \<in> gen_set_AE e"
      using fvae gen_set_AE_AE_iff_fv_arith_def_edge_disjoint_and_aexp_edge by metis
    then show ?case
      using fw_must.S_hat_def by auto
  qed
qed

lemma aexp_edge_list_S_hat_edge_list_iff: 
  "aexp_edge_list \<pi> a \<longleftrightarrow> a \<in> fw_must.S_hat_edge_list \<pi> d_init_AE"
  using S_hat_edge_list_aexp_edge_list aexp_edge_list_S_hat_edge_list' by blast

lemma aexp_path_S_hat_path_iff: 
  "a \<in> aexp_path \<pi> \<longleftrightarrow> a \<in> fw_must.S_hat_path \<pi> d_init_AE"
  using S_hat_edge_list_aexp_edge_list aexp_edge_list_S_hat_edge_list' aexp_path_def fw_must.S_hat_path_def by blast

definition summarizes_AE :: "(pred, ('n, 'a, 'v arith) cst) pred_val \<Rightarrow> bool" where
   "summarizes_AE \<rho> \<longleftrightarrow>
     (\<forall>q d.
         \<rho> \<Turnstile>\<^sub>l\<^sub>h must\<langle>[q, d]\<rangle>. \<longrightarrow>
          (\<forall>\<pi>. \<pi> \<in> path_with_word_from_to start (the_Node\<^sub>i\<^sub>d q) \<longrightarrow> (the_Elem\<^sub>i\<^sub>d d) \<in> aexp_path \<pi>))"

theorem AE_sound:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (fw_must.ana_pg_fw_must) s_BV"
  shows "summarizes_AE \<rho>"
proof -
  from assms have "fw_must.summarizes_fw_must \<rho>"
    using fw_must.sound_ana_pg_fw_must by auto
  then show ?thesis
    unfolding summarizes_AE_def fw_must.summarizes_fw_must_def edges_def edges_def
      end_def end_def aexp_path_S_hat_path_iff start_def start_def by force
qed

end

end
