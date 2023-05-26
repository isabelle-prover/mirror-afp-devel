theory Tree_Automata_Derivation_Split
  imports Regular_Tree_Relations.Tree_Automata
    Ground_MCtxt
begin

lemma ta_der'_inf_mctxt:
  assumes "t |\<in>| ta_der' \<A> s"
  shows "fst (split_vars t) \<le> (mctxt_of_term s)" using assms
proof (induct s arbitrary: t)
  case (Fun f ts) then show ?case
    by (cases t) (auto simp: comp_def less_eq_mctxt_prime intro: less_eq_mctxt'.intros)
qed (auto simp: ta_der'.simps)

lemma ta_der'_poss_subt_at_ta_der':
  assumes "t |\<in>| ta_der' \<A> s" and "p \<in> poss t"
  shows "t |_ p |\<in>| ta_der' \<A> (s |_ p)" using assms
  by (induct s arbitrary: t p) (auto simp: ta_der'.simps, blast+)

lemma ta_der'_varposs_to_ta_der:
  assumes "t |\<in>| ta_der' \<A> s" and "p \<in> varposs t"
  shows "the_Var (t |_ p) |\<in>| ta_der \<A> (s |_ p)" using assms
  by (induct s arbitrary: t p) (auto simp: ta_der'.simps, blast+)

definition "ta_der'_target_mctxt t \<equiv> fst (split_vars t)"
definition "ta_der'_target_args t \<equiv>  snd (split_vars t)"
definition "ta_der'_source_args t s \<equiv> unfill_holes (fst (split_vars t)) s"

lemmas ta_der'_mctxt_simps = ta_der'_target_mctxt_def ta_der'_target_args_def ta_der'_source_args_def

lemma ta_der'_target_mctxt_funas [simp]:
  "funas_mctxt (ta_der'_target_mctxt u) = funas_term u"
  by (auto simp: ta_der'_target_mctxt_def)

lemma ta_der'_target_mctxt_ground [simp]:
  "ground_mctxt (ta_der'_target_mctxt t)"
  by (auto simp: ta_der'_target_mctxt_def)

lemma ta_der'_source_args_ground:
  "t |\<in>| ta_der' \<A> s \<Longrightarrow> ground s \<Longrightarrow> \<forall> u \<in> set (ta_der'_source_args t s). ground u"
  by (metis fill_unfill_holes ground_fill_holes length_unfill_holes ta_der'_inf_mctxt ta_der'_mctxt_simps)

lemma ta_der'_source_args_term_of_gterm:
  "t |\<in>| ta_der' \<A> (term_of_gterm s) \<Longrightarrow> \<forall> u \<in> set (ta_der'_source_args t (term_of_gterm s)). ground u"
  by (intro ta_der'_source_args_ground) auto

lemma ta_der'_source_args_length: 
  "t |\<in>| ta_der' \<A> s \<Longrightarrow> num_holes (ta_der'_target_mctxt t) = length (ta_der'_source_args t s)"
  by (auto simp: ta_der'_mctxt_simps ta_der'_inf_mctxt)

lemma ta_der'_target_args_length: 
  "num_holes (ta_der'_target_mctxt t) = length (ta_der'_target_args t)"
  by (auto simp: ta_der'_mctxt_simps split_vars_num_holes)

lemma ta_der'_target_args_vars_term_conv:
  "vars_term t = set (ta_der'_target_args t)"
  by (auto simp: ta_der'_target_args_def split_vars_vars_term_list)

lemma ta_der'_target_args_vars_term_list_conv:
  "ta_der'_target_args t = vars_term_list t"
  by (auto simp: ta_der'_target_args_def split_vars_vars_term_list)


lemma mctxt_args_ta_der':
  assumes "num_holes C = length qs" "num_holes C = length ss" 
    and "\<forall> i < length ss. qs ! i |\<in>| ta_der \<A> (ss ! i)"
  shows "(fill_holes C (map Var qs)) |\<in>| ta_der' \<A> (fill_holes C ss)" using assms
proof (induct rule: fill_holes_induct2)
  case MHole then show ?case
    by (cases ss; cases qs) (auto simp: ta_der_to_ta_der')
next
  case (MFun f ts) then show ?case
    by (simp add: partition_by_nth_nth(1, 2))
qed auto

\<comment> \<open>Splitting derivation into multihole context containing the remaining function symbols and
  the states, where each state is reached via the automata\<close>
lemma ta_der'_mctxt_structure:
  assumes "t |\<in>| ta_der' \<A> s"
  shows "t = fill_holes (ta_der'_target_mctxt t) (map Var (ta_der'_target_args t))" (is "?G1")
    "s = fill_holes (ta_der'_target_mctxt t) (ta_der'_source_args t s)" (is "?G2")
    "num_holes (ta_der'_target_mctxt t) = length (ta_der'_source_args t s) \<and>
     length (ta_der'_source_args t s) = length (ta_der'_target_args t)" (is "?G3")
    "i < length (ta_der'_source_args t s) \<Longrightarrow> ta_der'_target_args t ! i |\<in>| ta_der \<A> (ta_der'_source_args t s ! i)"
proof -
  let ?C = "ta_der'_target_mctxt t" let ?ss = "ta_der'_source_args t s"
  let ?qs = "ta_der'_target_args t"
  have t_split: "?G1" by (auto simp: ta_der'_mctxt_simps split_vars_fill_holes)
  have s_split: "?G2" by (auto simp: ta_der'_mctxt_simps ta_der'_inf_mctxt[OF assms]
     intro!: fill_unfill_holes[symmetric])
  have len: "num_holes ?C = length ?ss" "length ?ss = length ?qs" using assms
    by (auto simp: ta_der'_mctxt_simps split_vars_num_holes ta_der'_inf_mctxt)
  have "i < length (ta_der'_target_args t) \<Longrightarrow>
       ta_der'_target_args t ! i |\<in>| ta_der \<A> (ta_der'_source_args t s ! i)" for i
    using ta_der'_poss_subt_at_ta_der'[OF assms, of "varposs_list t ! i"]
    unfolding ta_der'_mctxt_simps split_vars_vars_term_list length_map 
    by (auto simp: unfill_holes_to_subst_at_hole_poss[OF ta_der'_inf_mctxt[OF assms]]
       simp flip: varposs_list_to_var_term_list[of i t, unfolded varposs_list_var_terms_length])
       (metis assms hole_poss_split_vars_varposs_list nth_map nth_mem
        ta_der'_varposs_to_ta_der ta_der_to_ta_der' varposs_eq_varposs_list varposs_list_var_terms_length)
  then show ?G1 ?G2 ?G3 "i < length (ta_der'_source_args t s) \<Longrightarrow>
       ta_der'_target_args t ! i |\<in>| ta_der \<A> (ta_der'_source_args t s ! i)" using len t_split s_split
    by (simp_all add: ta_der'_mctxt_simps)
qed

lemma ta_der'_ground_mctxt_structure:
  assumes "t |\<in>| ta_der' \<A> (term_of_gterm s)"
  shows "t = fill_holes (ta_der'_target_mctxt t) (map Var (ta_der'_target_args t))"
    "term_of_gterm s = fill_holes (ta_der'_target_mctxt t) (ta_der'_source_args t (term_of_gterm s))"
    "num_holes (ta_der'_target_mctxt t) =  length (ta_der'_source_args t (term_of_gterm s)) \<and>
     length (ta_der'_source_args t (term_of_gterm s)) = length (ta_der'_target_args t)"
    "i < length (ta_der'_target_args t) \<Longrightarrow> ta_der'_target_args t ! i |\<in>| ta_der \<A> (ta_der'_source_args t (term_of_gterm s) ! i)"
  using ta_der'_mctxt_structure[OF assms]
  by force+


\<comment> \<open>Splitting derivation into context containing the remaining function symbols and state\<close>

definition "ta_der'_gctxt t \<equiv> gctxt_of_gmctxt (gmctxt_of_mctxt (fst (split_vars t)))"
abbreviation "ta_der'_ctxt t \<equiv> ctxt_of_gctxt (ta_der'_gctxt t)"
definition "ta_der'_source_ctxt_arg t s \<equiv> hd (unfill_holes (fst (split_vars t)) s)"

abbreviation "ta_der'_source_gctxt_arg t s \<equiv> gterm_of_term (ta_der'_source_ctxt_arg t (term_of_gterm s))"

lemma ta_der'_ctxt_structure:
  assumes "t |\<in>| ta_der' \<A> s" "vars_term_list t = [q]"
  shows "t = (ta_der'_ctxt t)\<langle>Var q\<rangle>" (is "?G1")
    "s = (ta_der'_ctxt t)\<langle>ta_der'_source_ctxt_arg t s\<rangle>" (is "?G2")
    "ground_ctxt (ta_der'_ctxt t)" (is "?G3")
    "q |\<in>| ta_der \<A> (ta_der'_source_ctxt_arg t s)" (is "?G4")
proof -
  have *: "length xs = Suc 0 \<Longrightarrow> xs = [hd xs]" for xs
    by (metis length_0_conv length_Suc_conv list.sel(1))
  have [simp]: "length (snd (split_vars t)) = Suc 0" using assms(2) ta_der'_inf_mctxt[OF assms(1)]
    by (auto simp: split_vars_vars_term_list)
  have [simp]: "num_gholes (gmctxt_of_mctxt (fst (split_vars t))) = Suc 0" using assms(2)
    by (simp add: split_vars_num_holes split_vars_vars_term_list)
  have [simp]: "ta_der'_source_args t s = [ta_der'_source_ctxt_arg t s]"
    using assms(2) ta_der'_inf_mctxt[OF assms(1)]
    by (auto simp: ta_der'_source_args_def ta_der'_source_ctxt_arg_def split_vars_num_holes intro!: *)
  have t_split: ?G1 using assms(2)
    by (auto simp: ta_der'_gctxt_def split_vars_fill_holes
      split_vars_vars_term_list simp flip: ctxt_of_gctxt_gctxt_of_gmctxt_apply)
  have s_split: ?G2 using ta_der'_mctxt_structure[OF assms(1)] assms(2)
    by (auto simp: ta_der'_gctxt_def ta_der'_target_mctxt_def
          simp flip: ctxt_of_gctxt_gctxt_of_gmctxt_apply)
  from ta_der'_mctxt_structure[OF assms(1)] have ?G4
    by (auto simp: ta_der'_target_args_def assms(2) split_vars_vars_term_list)
  moreover have ?G3 unfolding ta_der'_gctxt_def by auto
  ultimately show ?G1 ?G2 ?G3 ?G4 using t_split s_split
    by force+
qed


lemma ta_der'_ground_ctxt_structure:
  assumes "t |\<in>| ta_der' \<A> (term_of_gterm s)" "vars_term_list t = [q]"
  shows "t = (ta_der'_ctxt t)\<langle>Var q\<rangle>"
    "s = (ta_der'_gctxt t)\<langle>ta_der'_source_gctxt_arg t s\<rangle>\<^sub>G"
    "ground (ta_der'_source_ctxt_arg t (term_of_gterm s))"
    "q |\<in>| ta_der \<A> (ta_der'_source_ctxt_arg t (term_of_gterm s))"
  using ta_der'_ctxt_structure[OF assms] term_of_gterm_ctxt_apply
  by force+

subsection \<open>Sufficient condition for splitting the reachability relation induced by a tree automaton\<close>

locale derivation_split =
  fixes A :: "('q, 'f) ta" and \<A> and \<B>
  assumes rule_split: "rules A = rules \<A> |\<union>| rules \<B>"
    and eps_split: "eps A = eps \<A> |\<union>| eps \<B>"
    and B_target_states: "rule_target_states (rules \<B>) |\<union>| (snd |`| (eps \<B>)) |\<inter>|
      (rule_arg_states (rules \<A>) |\<union>| (fst |`| (eps \<A>))) = {||}"
begin

abbreviation "\<Delta>\<^sub>A \<equiv> rules \<A>"
abbreviation "\<Delta>\<^sub>\<E>\<^sub>A \<equiv> eps \<A>"
abbreviation "\<Delta>\<^sub>B \<equiv> rules \<B>"
abbreviation "\<Delta>\<^sub>\<E>\<^sub>B \<equiv> eps \<B>"

abbreviation "\<Q>\<^sub>A \<equiv> \<Q> \<A>"
definition "\<Q>\<^sub>B \<equiv> rule_target_states \<Delta>\<^sub>B |\<union>| (snd |`| \<Delta>\<^sub>\<E>\<^sub>B)"
lemmas B_target_states' = B_target_states[folded \<Q>\<^sub>B_def]

lemma states_split [simp]: "\<Q> A = \<Q> \<A> |\<union>| \<Q> \<B>"
  by (auto simp add: \<Q>_def rule_split eps_split)

lemma A_args_states_not_B:
  "TA_rule f qs q |\<in>| \<Delta>\<^sub>A \<Longrightarrow> p |\<in>| fset_of_list qs \<Longrightarrow> p |\<notin>| \<Q>\<^sub>B"
  using B_target_states
  by (force simp add: \<Q>\<^sub>B_def)

lemma rule_statesD:
  "r |\<in>| \<Delta>\<^sub>A \<Longrightarrow> r_rhs r |\<in>| \<Q>\<^sub>A"
  "r |\<in>| \<Delta>\<^sub>B \<Longrightarrow> r_rhs r |\<in>| \<Q>\<^sub>B"
  "r |\<in>| \<Delta>\<^sub>A \<Longrightarrow> p |\<in>| fset_of_list (r_lhs_states r) \<Longrightarrow> p |\<in>| \<Q>\<^sub>A"
  "TA_rule f qs q |\<in>| \<Delta>\<^sub>A \<Longrightarrow> q |\<in>| \<Q>\<^sub>A"
  "TA_rule f qs q |\<in>| \<Delta>\<^sub>B \<Longrightarrow> q |\<in>| \<Q>\<^sub>B"
  "TA_rule f qs q |\<in>| \<Delta>\<^sub>A \<Longrightarrow> p |\<in>| fset_of_list qs \<Longrightarrow> p |\<in>| \<Q>\<^sub>A"
  by (auto simp: rule_statesD \<Q>\<^sub>B_def rev_image_eqI)

lemma eps_states_dest:
  "(p, q) |\<in>| \<Delta>\<^sub>\<E>\<^sub>A \<Longrightarrow> p |\<in>| \<Q>\<^sub>A"
  "(p, q) |\<in>| \<Delta>\<^sub>\<E>\<^sub>A \<Longrightarrow> q |\<in>| \<Q>\<^sub>A"
  "(p, q) |\<in>| \<Delta>\<^sub>\<E>\<^sub>A|\<^sup>+| \<Longrightarrow> p |\<in>| \<Q>\<^sub>A"
  "(p, q) |\<in>| \<Delta>\<^sub>\<E>\<^sub>A|\<^sup>+| \<Longrightarrow> q |\<in>| \<Q>\<^sub>A"
  "(p, q) |\<in>| \<Delta>\<^sub>\<E>\<^sub>B \<Longrightarrow> q |\<in>| \<Q>\<^sub>B"
  "(p, q) |\<in>| \<Delta>\<^sub>\<E>\<^sub>B|\<^sup>+| \<Longrightarrow> q |\<in>| \<Q>\<^sub>B"
  by (auto simp: eps_dest_all \<Q>\<^sub>B_def rev_image_eqI elim: ftranclE)

lemma transcl_eps_simp:
  "(eps A)|\<^sup>+| = \<Delta>\<^sub>\<E>\<^sub>A|\<^sup>+| |\<union>| \<Delta>\<^sub>\<E>\<^sub>B|\<^sup>+| |\<union>| (\<Delta>\<^sub>\<E>\<^sub>A|\<^sup>+| |O| \<Delta>\<^sub>\<E>\<^sub>B|\<^sup>+|)"
proof -
  have "\<Delta>\<^sub>\<E>\<^sub>B |O| \<Delta>\<^sub>\<E>\<^sub>A = {||}" using B_target_states'
    by (metis eps_states_dest(5) ex_fin_conv fimageI finterI frelcompE fst_conv inf_sup_distrib1 sup_eq_bot_iff)
  from ftrancl_Un2_separatorE[OF this] show ?thesis
    unfolding eps_split by auto
qed

lemma B_rule_eps_A_False:
  "f qs \<rightarrow> q |\<in>| \<Delta>\<^sub>B \<Longrightarrow> (q, p) |\<in>| \<Delta>\<^sub>\<E>\<^sub>A|\<^sup>+| \<Longrightarrow> False"
  using B_target_states unfolding \<Q>\<^sub>B_def
  by (metis B_target_states' equalsffemptyD fimage_eqI finter_iff fst_conv ftranclD funion_iff local.rule_statesD(5))

lemma to_A_rule_set:
  assumes "TA_rule f qs q |\<in>| rules A" and "q = p \<or> (q, p) |\<in>| (eps A)|\<^sup>+|" and "p |\<notin>| \<Q>\<^sub>B"
  shows "TA_rule f qs q |\<in>| \<Delta>\<^sub>A" "q = p \<or> (q, p) |\<in>| \<Delta>\<^sub>\<E>\<^sub>A|\<^sup>+|" using assms
  unfolding transcl_eps_simp rule_split
  by (auto dest: rule_statesD eps_states_dest dest: B_rule_eps_A_False)

lemma to_B_rule_set:
  assumes "TA_rule f qs q |\<in>| rules A" and "q |\<notin>| \<Q>\<^sub>A"
  shows "TA_rule f qs q |\<in>| \<Delta>\<^sub>B" using assms
  unfolding transcl_eps_simp rule_split
  by (auto dest: rule_statesD eps_states_dest)


declare fsubsetI[rule del]
lemma ta_der_monos:
  "ta_der \<A> t |\<subseteq>| ta_der A t" "ta_der \<B> t |\<subseteq>| ta_der A t"
  by (auto simp: sup.coboundedI1 rule_split eps_split intro!: ta_der_mono)
declare fsubsetI[intro!]


lemma ta_der_from_\<Delta>\<^sub>A:
  assumes "q |\<in>| ta_der A (term_of_gterm t)" and "q |\<notin>| \<Q>\<^sub>B"
  shows "q |\<in>| ta_der \<A> (term_of_gterm t)" using assms
proof (induct rule: ta_der_gterm_induct)
  case (GFun f ts ps p q)
  have "i < length ts \<Longrightarrow> ps ! i |\<notin>| \<Q>\<^sub>B" for i using GFun A_args_states_not_B
    by (metis fnth_mem to_A_rule_set(1))
  then show ?case using GFun(2, 5) to_A_rule_set[OF GFun(1, 3, 6)]
    by (auto simp: transcl_eps_simp)
qed

lemma ta_state:
  assumes "q |\<in>| ta_der A (term_of_gterm s)"
  shows "q |\<in>| \<Q>\<^sub>A \<or> q |\<in>| \<Q>\<^sub>B" using assms
  by (cases s) (auto simp: rule_split transcl_eps_simp dest: rule_statesD eps_states_dest)

(* Main lemmas *)

lemma ta_der_split:
  assumes "q |\<in>| ta_der A (term_of_gterm s)" and "q |\<in>| \<Q>\<^sub>B"
  shows "\<exists> t. t |\<in>| ta_der' \<A> (term_of_gterm s) \<and> q |\<in>| ta_der \<B> t"
    (is "\<exists>t . ?P s q t") using assms
proof (induct rule: ta_der_gterm_induct)
  case (GFun f ts ps p q)
  {fix i assume ass: "i < length ts"
    then have "\<exists> t. t |\<in>| ta_der' \<A> (term_of_gterm (ts ! i)) \<and> ps ! i |\<in>| ta_der \<B> t"
    proof (cases "ps ! i |\<notin>| \<Q>\<^sub>B")
      case True then show ?thesis
        using ta_state GFun(2, 4) ta_der_from_\<Delta>\<^sub>A[of "ps ! i" "ts ! i"] ass
        by (intro exI[of _ "Var (ps ! i)"]) (auto simp: ta_der_to_ta_der' \<Q>\<^sub>B_def)
    next
      case False
      then have "ps ! i |\<in>| \<Q>\<^sub>B" using ta_state[OF GFun(4)[OF ass]]
        by auto 
      from GFun(5)[OF ass this] show ?thesis .
    qed}
  then obtain h where IH:
    "\<forall> i < length ts. h i |\<in>| ta_der' \<A> (term_of_gterm (ts ! i))"
    "\<forall> i < length ts. ps ! i |\<in>| ta_der \<B> (h i)"
    using GFun(1 - 4) choice_nat[of "length ts" "\<lambda> t i. ?P (ts ! i) (ps ! i) t"]
    by blast
  from GFun(1) consider (A) "f ps \<rightarrow> p |\<in>| \<Delta>\<^sub>A" | (B) "f ps \<rightarrow> p |\<in>| \<Delta>\<^sub>B" by (auto simp: rule_split)
  then show ?case
  proof cases
    case A then obtain q' where eps_sp: "p = q' \<or> (p, q') |\<in>| \<Delta>\<^sub>\<E>\<^sub>A|\<^sup>+|"
      "q' = q \<or> (q', q) |\<in>| \<Delta>\<^sub>\<E>\<^sub>B|\<^sup>+|" using GFun(3, 6)
      by (auto simp: transcl_eps_simp dest: eps_states_dest)
    from GFun(4)[THEN ta_der_from_\<Delta>\<^sub>A] A GFun(2, 4)
    have reach_fst: "p |\<in>| ta_der \<A> (term_of_gterm (GFun f ts))"
      using A_args_states_not_B by auto
    then have "q' |\<in>| ta_der \<A> (term_of_gterm (GFun f ts))" using eps_sp
      by (meson ta_der_trancl_eps)
    then show ?thesis using eps_sp(2)
      by (intro exI[of _ "Var q'"]) (auto simp flip: ta_der_to_ta_der' simp del: ta_der'_simps)
  next
    case B
    then have "p = q \<or> (p, q) |\<in>| \<Delta>\<^sub>\<E>\<^sub>B|\<^sup>+|" using GFun(3)
      by (auto simp: transcl_eps_simp dest: B_rule_eps_A_False)
    then show ?thesis using GFun(2, 4, 6) IH B
      by (auto intro!: exI[of _ "Fun f (map h [0 ..< length ts])"] exI[of _ ps])
  qed
qed


lemma ta_der'_split:
  assumes "t |\<in>| ta_der' A (term_of_gterm s)"
  shows "\<exists> u. u |\<in>| ta_der' \<A> (term_of_gterm s) \<and> t |\<in>| ta_der' \<B> u"
    (is "\<exists> u. ?P s t u") using assms
proof (induct s arbitrary: t)
  case (GFun f ts) show ?case
  proof (cases t)
    case [simp]: (Var q)
    have "q |\<in>| ta_der A (term_of_gterm (GFun f ts))" using GFun(2)
      by (auto simp flip: ta_der_to_ta_der')
    from ta_der_split[OF this] ta_der_from_\<Delta>\<^sub>A[OF this] ta_state[OF this]
    show ?thesis unfolding Var
      by (metis ta_der'_refl ta_der_to_ta_der')
  next
    case [simp]: (Fun g ss)
    obtain h where IH:
      "\<forall> i < length ts. h i |\<in>| ta_der' \<A> (term_of_gterm (ts ! i))"
      "\<forall> i < length ts. ss ! i |\<in>| ta_der' \<B> (h i)"
      using GFun choice_nat[of "length ts" "\<lambda> t i. ?P (ts ! i) (ss ! i) t"]
      by auto
    then show ?thesis using GFun(2)
      by (auto intro!: exI[of _ "Fun f (map h [0..<length ts])"])
  qed
qed

(* TODO rewrite using ta_der'_mctxt_structure *)
lemma ta_der_to_mcxtx:
  assumes "q |\<in>| ta_der A (term_of_gterm s)" and "q |\<in>| \<Q>\<^sub>B"
  shows "\<exists> C ss qs. length qs = length ss \<and> num_holes C = length ss \<and>
    (\<forall> i < length ss. qs ! i |\<in>| ta_der \<A> (term_of_gterm (ss ! i))) \<and>
    q |\<in>| ta_der \<B> (fill_holes C (map Var qs)) \<and>
    ground_mctxt C \<and> fill_holes C (map term_of_gterm ss) = term_of_gterm s"
    (is "\<exists>C ss qs. ?P s q C ss qs")
proof -
  from ta_der_split[OF assms] obtain t where
    wit: "t |\<in>| ta_der' \<A> (term_of_gterm s)" "q |\<in>| ta_der \<B> t" by auto
  let ?C = "fst (split_vars t)" let ?ss = "map (gsubt_at s) (varposs_list t)"
  let ?qs = "snd (split_vars t)"
  have poss [simp]:"i < length (varposs_list t) \<Longrightarrow> varposs_list t ! i \<in> gposs s" for i
    by (metis nth_mem ta_der'_poss[OF wit(1)] poss_gposs_conv subset_eq varposs_eq_varposs_list
        varposs_imp_poss varposs_list_var_terms_length)
  have len: "num_holes ?C = length ?ss" "length ?ss = length ?qs"
    by (simp_all add: split_vars_num_holes split_vars_vars_term_list varposs_list_var_terms_length)
  from unfill_holes_to_subst_at_hole_poss[OF ta_der'_inf_mctxt[OF wit(1)]]
  have "unfill_holes (fst (split_vars t)) (term_of_gterm s) = map (term_of_gterm \<circ> gsubt_at s) (varposs_list t)"
    by (auto simp: comp_def hole_poss_split_vars_varposs_list
        dest: in_set_idx intro!: nth_equalityI term_of_gterm_gsubt)
  from fill_unfill_holes[OF ta_der'_inf_mctxt[OF wit(1)]] this
  have rep: "fill_holes ?C (map term_of_gterm ?ss) = term_of_gterm s"
    by simp
  have reach_int: "i < length ?ss \<Longrightarrow> ?qs ! i |\<in>| ta_der \<A> (term_of_gterm (?ss ! i))" for i
    using wit(1) ta_der'_varposs_to_ta_der
    unfolding split_vars_vars_term_list length_map
    unfolding varposs_list_to_var_term_list[symmetric]
    by (metis nth_map nth_mem poss term_of_gterm_gsubt varposs_eq_varposs_list)
  have reach_end: "q |\<in>| ta_der \<B> (fill_holes ?C (map Var ?qs))" using wit
    using split_vars_fill_holes[of ?C t "map Var ?qs"]
    by auto
  show ?thesis using len rep reach_end reach_int
    by (metis split_vars_ground')
qed

lemma ta_der_to_gmcxtx:
  assumes "q |\<in>| ta_der A (term_of_gterm s)" and "q |\<in>| \<Q>\<^sub>B"
  shows "\<exists> C ss qs qs'. length qs' = length qs \<and> length qs = length ss \<and> num_gholes C = length ss \<and>
    (\<forall> i < length ss. qs ! i |\<in>| ta_der \<A> (term_of_gterm (ss ! i))) \<and>
    q |\<in>| ta_der \<B> (fill_holes (mctxt_of_gmctxt C) (map Var qs')) \<and>
    fill_gholes C ss = s"
  using ta_der_to_mcxtx[OF assms]
  by (metis gmctxt_of_mctxt_inv ground_gmctxt_of_gterm_of_term num_gholes_gmctxt_of_mctxt term_of_gterm_inv)

(* Reconstuction *)

lemma mctxt_const_to_ta_der:
  assumes "num_holes C = length ss" "length ss = length qs"
    and "\<forall> i < length qs. qs ! i |\<in>| ta_der \<A> (ss ! i)"
    and "q |\<in>| ta_der \<B> (fill_holes C (map Var qs))"
  shows "q |\<in>| ta_der A (fill_holes C ss)"
proof -
  have mid: "fill_holes C (map Var qs) |\<in>| ta_der' A (fill_holes C ss)"
    using assms(1 - 3) ta_der_monos(1)
    by (intro mctxt_args_ta_der') auto
  then show ?thesis using assms(1, 2) ta_der_monos(2)[THEN fsubsetD, OF assms(4)]
    using ta_der'_trans
    by (simp add: ta_der'_ta_der)
qed

lemma ctxt_const_to_ta_der:
  assumes "q |\<in>| ta_der \<A> s"
    and "p |\<in>| ta_der \<B> C\<langle>Var q\<rangle>"
  shows "p |\<in>| ta_der A C\<langle>s\<rangle>" using assms
  by (meson fin_mono ta_der_ctxt ta_der_monos(1) ta_der_monos(2))

lemma gctxt_const_to_ta_der:
  assumes "q |\<in>| ta_der \<A> (term_of_gterm s)"
    and "p |\<in>| ta_der \<B> (ctxt_of_gctxt C)\<langle>Var q\<rangle>"
  shows "p |\<in>| ta_der A (term_of_gterm C\<langle>s\<rangle>\<^sub>G)" using assms
  by (metis ctxt_const_to_ta_der ctxt_of_gctxt_inv ground_ctxt_of_gctxt ground_gctxt_of_ctxt_apply_gterm)

end
end