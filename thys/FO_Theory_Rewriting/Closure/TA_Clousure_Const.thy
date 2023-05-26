section \<open>(Multihole)Context closure of recognized tree languages\<close>

theory TA_Clousure_Const
  imports Tree_Automata_Derivation_Split
begin


subsection \<open>Tree Automata closure constructions\<close>
declare ta_union_def [simp]
subsubsection \<open>Reflexive closure over a given signature\<close>

definition "reflcl_rules \<F> q \<equiv> (\<lambda> (f, n). TA_rule f (replicate n q) q) |`| \<F>"
definition "refl_ta \<F> q = TA (reflcl_rules \<F> q) {||}"

definition gen_reflcl_automaton :: "('f \<times> nat) fset \<Rightarrow> ('q, 'f) ta \<Rightarrow> 'q \<Rightarrow> ('q, 'f) ta" where
  "gen_reflcl_automaton \<F> \<A> q = ta_union \<A> (refl_ta \<F> q)"

definition "reflcl_automaton \<F> \<A> = (let \<B> = fmap_states_ta Some \<A> in
   gen_reflcl_automaton \<F> \<B> None)"

definition "reflcl_reg \<F> \<A> = Reg (finsert None (Some |`| fin \<A>)) (reflcl_automaton \<F> (ta \<A>))"

subsubsection \<open>Multihole context closure over a given signature\<close>

definition "refl_over_states_ta Q \<F> \<A> q = TA (reflcl_rules \<F> q) ((\<lambda> p. (p, q)) |`| (Q |\<inter>| \<Q> \<A>))"

definition gen_parallel_closure_automaton :: "'q fset \<Rightarrow> ('f \<times> nat) fset \<Rightarrow> ('q, 'f) ta \<Rightarrow> 'q \<Rightarrow> ('q, 'f) ta" where
  "gen_parallel_closure_automaton Q \<F> \<A> q = ta_union \<A> (refl_over_states_ta Q \<F> \<A> q)"

definition parallel_closure_reg where
  "parallel_closure_reg \<F> \<A> = (let \<B> = fmap_states_reg Some \<A> in
   Reg {|None|} (gen_parallel_closure_automaton (fin \<B>) \<F> (ta \<B>) None))"

subsubsection \<open>Context closure of regular tree language\<close>

definition "semantic_path_rules \<F> q\<^sub>c q\<^sub>i q\<^sub>f \<equiv> 
  |\<Union>| ((\<lambda> (f, n). fset_of_list (map (\<lambda> i. TA_rule f ((replicate n q\<^sub>c)[i := q\<^sub>i]) q\<^sub>f) [0..< n])) |`| \<F>)"

definition "reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f \<equiv>
  TA (reflcl_rules \<F> q\<^sub>c |\<union>| semantic_path_rules \<F> q\<^sub>c q\<^sub>f q\<^sub>f) ((\<lambda> p. (p, q\<^sub>f)) |`| Q)"

definition "gen_ctxt_closure_automaton Q \<F> \<A> q\<^sub>c q\<^sub>f = ta_union \<A> (reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f)"

definition "gen_ctxt_closure_reg \<F> \<A> q\<^sub>c q\<^sub>f =
   Reg {|q\<^sub>f|} (gen_ctxt_closure_automaton (fin \<A>) \<F> (ta \<A>) q\<^sub>c q\<^sub>f)"

definition "ctxt_closure_reg \<F> \<A> =
  (let \<B> = fmap_states_reg Inl (reg_Restr_Q\<^sub>f \<A>) in
  gen_ctxt_closure_reg \<F> \<B> (Inr False) (Inr True))"


subsubsection \<open>Not empty context closure of regular tree language\<close>

datatype cl_states = cl_state | tr_state | fin_state | fin_clstate

definition "reflcl_over_nhole_ctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f \<equiv>
  TA (reflcl_rules \<F> q\<^sub>c |\<union>| semantic_path_rules \<F> q\<^sub>c q\<^sub>i q\<^sub>f |\<union>| semantic_path_rules \<F> q\<^sub>c q\<^sub>f q\<^sub>f) ((\<lambda> p. (p, q\<^sub>i)) |`| Q)"

definition "gen_nhole_ctxt_closure_automaton Q \<F> \<A> q\<^sub>c q\<^sub>i q\<^sub>f =
   ta_union \<A> (reflcl_over_nhole_ctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f)"

definition "gen_nhole_ctxt_closure_reg \<F> \<A> q\<^sub>c q\<^sub>i q\<^sub>f =
    Reg {|q\<^sub>f|} (gen_nhole_ctxt_closure_automaton (fin \<A>) \<F> (ta \<A>) q\<^sub>c q\<^sub>i q\<^sub>f)"

definition "nhole_ctxt_closure_reg \<F> \<A> =
  (let \<B> = fmap_states_reg Inl (reg_Restr_Q\<^sub>f \<A>) in
  (gen_nhole_ctxt_closure_reg \<F> \<B> (Inr cl_state) (Inr tr_state) (Inr fin_state)))"

subsubsection \<open>Non empty multihole context closure of regular tree language\<close>

abbreviation "add_eps \<A> e \<equiv> TA (rules \<A>) (eps \<A> |\<union>| e)"
definition "reflcl_over_nhole_mctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f \<equiv>
  add_eps (reflcl_over_nhole_ctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f) {|(q\<^sub>i, q\<^sub>c)|}"

definition "gen_nhole_mctxt_closure_automaton Q \<F> \<A> q\<^sub>c q\<^sub>i q\<^sub>f =
   ta_union \<A> (reflcl_over_nhole_mctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f)"

definition "gen_nhole_mctxt_closure_reg \<F> \<A> q\<^sub>c q\<^sub>i q\<^sub>f = 
   Reg {|q\<^sub>f|} (gen_nhole_mctxt_closure_automaton (fin \<A>) \<F> (ta \<A>) q\<^sub>c q\<^sub>i q\<^sub>f)"

definition "nhole_mctxt_closure_reg \<F> \<A> =
  (let \<B> = fmap_states_reg Inl (reg_Restr_Q\<^sub>f \<A>) in
  (gen_nhole_mctxt_closure_reg \<F> \<B> (Inr cl_state) (Inr tr_state) (Inr fin_state)))"

subsubsection \<open>Not empty multihole context closure of regular tree language\<close>

definition "gen_mctxt_closure_reg \<F> \<A> q\<^sub>c q\<^sub>i q\<^sub>f =
   Reg {|q\<^sub>f, q\<^sub>i|} (gen_nhole_mctxt_closure_automaton (fin \<A>) \<F> (ta \<A>) q\<^sub>c q\<^sub>i q\<^sub>f)"

definition "mctxt_closure_reg \<F> \<A> =
  (let \<B> = fmap_states_reg Inl (reg_Restr_Q\<^sub>f \<A>) in
  (gen_mctxt_closure_reg \<F> \<B> (Inr cl_state) (Inr tr_state) (Inr fin_state)))"


subsubsection \<open>Multihole context closure of regular tree language\<close>

definition "nhole_mctxt_reflcl_reg \<F> \<A> =
  reg_union (nhole_mctxt_closure_reg \<F> \<A>) (Reg {|fin_clstate|} (refl_ta \<F> (fin_clstate)))"

subsubsection \<open>Lemmas about @{const ta_der'}\<close>

lemma ta_det'_ground_id:
  "t |\<in>| ta_der' \<A> s \<Longrightarrow> ground t \<Longrightarrow> t = s"
  by (induct s arbitrary: t) (auto simp add: ta_der'.simps nth_equalityI)

lemma ta_det'_vars_term_id:
  "t |\<in>| ta_der' \<A> s \<Longrightarrow> vars_term t \<inter> fset (\<Q> \<A>) = {} \<Longrightarrow> t = s"
proof (induct s arbitrary: t)
  case (Fun f ss)
  from Fun(2-) obtain ts where [simp]: "t = Fun f ts" and len: "length ts = length ss"
    by (cases t) (auto dest: rule_statesD eps_dest_all)
  from Fun(1)[OF nth_mem, of i "ts ! i" for i] show ?case using Fun(2-) len
    by (auto simp add: ta_der'.simps Union_disjoint
        dest: rule_statesD eps_dest_all intro!: nth_equalityI)
qed (auto simp add: ta_der'.simps dest: rule_statesD eps_dest_all)

lemma fresh_states_ta_der'_pres:
  assumes st: "q \<in> vars_term s" "q |\<notin>| \<Q> \<A>"
    and reach: "t |\<in>| ta_der' \<A> s"
  shows "q \<in> vars_term t" using reach st(1)
proof (induct s arbitrary: t)
  case (Var x)
  then show ?case using assms(2)
    by (cases t) (auto simp: ta_der'.simps dest: eps_trancl_statesD)
next
  case (Fun f ss)
  from Fun(3) obtain i where w: "i < length ss" "q \<in> vars_term (ss ! i)" by (auto simp: in_set_conv_nth)
  have "i < length (args t) \<and> q \<in> vars_term (args t ! i)" using Fun(2) w assms(2) Fun(1)[OF nth_mem[OF w(1)] _ w(2)]
    using rule_statesD(3) ta_der_to_ta_der'
    by (auto simp: ta_der'.simps dest: rule_statesD(3)) fastforce+
  then show ?case by (cases t) auto
qed

lemma ta_der'_states:
  "t |\<in>| ta_der' \<A> s \<Longrightarrow> vars_term t \<subseteq> vars_term s \<union> fset (\<Q> \<A>)"
proof (induct s arbitrary: t)
  case (Var x) then show ?case
    by (auto simp: ta_der'.simps dest: eps_dest_all)
next
  case (Fun f ts) then show ?case
    by (auto simp: ta_der'.simps rule_statesD dest: eps_dest_all)
       (metis (no_types, opaque_lifting) Un_iff in_set_conv_nth subsetD)
qed

lemma ta_der'_gterm_states:
  "t |\<in>| ta_der' \<A> (term_of_gterm s) \<Longrightarrow> vars_term t \<subseteq> fset (\<Q> \<A>)"
  using ta_der'_states[of t \<A> "term_of_gterm s"]
  by auto

lemma ta_der'_Var_funas:
  "Var q |\<in>| ta_der' \<A> s \<Longrightarrow> funas_term s \<subseteq> fset (ta_sig \<A>)"
  by (auto simp: less_eq_fset.rep_eq ffunas_term.rep_eq dest!: ta_der_term_sig ta_der'_to_ta_der)


lemma ta_sig_fsubsetI:
  assumes "\<And> r. r |\<in>| rules \<A> \<Longrightarrow> (r_root r, length (r_lhs_states r)) |\<in>| \<F>"
  shows "ta_sig \<A> |\<subseteq>| \<F>" using assms
  by (auto simp: ta_sig_def)

subsubsection \<open>Signature induced by @{const refl_ta} and @{const refl_over_states_ta}\<close>

lemma refl_ta_sig [simp]:
  "ta_sig (refl_ta \<F> q) = \<F>"
  "ta_sig (refl_over_states_ta  Q \<F> \<A> q ) = \<F>"
  by (auto simp: ta_sig_def refl_ta_def reflcl_rules_def refl_over_states_ta_def image_iff Bex_def)

subsubsection \<open>Correctness of @{const refl_ta}, @{const gen_reflcl_automaton}, and @{const reflcl_automaton}\<close>

lemma refl_ta_eps [simp]: "eps (refl_ta \<F> q) = {||}"
  by (auto simp: refl_ta_def)

lemma refl_ta_sound:
  "s \<in> \<T>\<^sub>G (fset \<F>) \<Longrightarrow> q |\<in>| ta_der (refl_ta \<F> q) (term_of_gterm s)"
  by (induct rule: \<T>\<^sub>G.induct) (auto simp: refl_ta_def reflcl_rules_def
      image_iff Bex_def)

lemma reflcl_rules_args:
  "length ps = n \<Longrightarrow> f ps \<rightarrow> p |\<in>| reflcl_rules \<F> q \<Longrightarrow> ps = replicate n q"
  by (auto simp: reflcl_rules_def)

lemma \<Q>_refl_ta:
  "\<Q> (refl_ta \<F> q) |\<subseteq>| {|q|}"
  by (auto simp: \<Q>_def refl_ta_def rule_states_def reflcl_rules_def fset_of_list_elem)

lemma refl_ta_complete1:
  "Var p |\<in>| ta_der' (refl_ta \<F> q) s \<Longrightarrow> p \<noteq> q \<Longrightarrow> s = Var p"
  by (cases s) (auto simp: ta_der'.simps refl_ta_def reflcl_rules_def)

lemma refl_ta_complete2:
  "Var q |\<in>| ta_der' (refl_ta \<F> q) s \<Longrightarrow> funas_term s \<subseteq> fset \<F> \<and> vars_term s \<subseteq> {q}"
  unfolding ta_der_to_ta_der'[symmetric]
  using ta_der_term_sig[of q "refl_ta \<F> q" s] ta_der_states'[of q "refl_ta \<F> q" s]
  using fsubsetD[OF \<Q>_refl_ta[of \<F> q]]
  by (auto simp: ffunas_term.rep_eq)
     (metis Term.term.simps(17) fresh_states_ta_der'_pres singletonD ta_der_to_ta_der')

lemma gen_reflcl_lang:
  assumes "q |\<notin>| \<Q> \<A>"
  shows "gta_lang (finsert q Q) (gen_reflcl_automaton \<F> \<A> q) = gta_lang Q \<A> \<union> \<T>\<^sub>G (fset \<F>)"
    (is "?Ls = ?Rs")
proof -
  let ?A = "gen_reflcl_automaton \<F> \<A> q"
  interpret sq: derivation_split ?A "\<A>" "refl_ta \<F> q"
    using assms unfolding derivation_split_def
    by (auto simp: gen_reflcl_automaton_def refl_ta_def reflcl_rules_def \<Q>_def)
  show ?thesis
  proof
    {fix s assume "s \<in> ?Ls" then obtain p u where
        seq: "u |\<in>| ta_der' \<A> (term_of_gterm s)" "Var p |\<in>| ta_der' (refl_ta \<F> q) u" and
        fin: "p |\<in>| finsert q Q"
        by (auto simp: ta_der_to_ta_der' elim!: gta_langE dest!: sq.ta_der'_split)
      have "vars_term u \<subseteq> {q} \<Longrightarrow> u = term_of_gterm s" using assms
        by (intro ta_det'_vars_term_id[OF seq(1)]) auto
      then have "s \<in> ?Rs" using assms fin seq funas_term_of_gterm_conv
        using refl_ta_complete1[OF seq(2)]
        by (cases "p = q") (auto simp: ta_der_to_ta_der' \<T>\<^sub>G_funas_gterm_conv dest!: refl_ta_complete2)}
    then show "?Ls \<subseteq> gta_lang Q \<A> \<union> \<T>\<^sub>G (fset \<F>)" by blast
  next
    show "gta_lang Q \<A> \<union> \<T>\<^sub>G (fset \<F>) \<subseteq> ?Ls"
      using sq.ta_der_monos unfolding gta_lang_def gta_der_def
      by (auto dest: refl_ta_sound)
  qed
qed

lemma reflcl_lang:
  "gta_lang (finsert None (Some |`| Q)) (reflcl_automaton \<F> \<A>) = gta_lang Q \<A> \<union> \<T>\<^sub>G (fset \<F>)"
proof -
  have st: "None |\<notin>| \<Q> (fmap_states_ta Some \<A>)" by auto
  have "gta_lang Q \<A> = gta_lang (Some |`| Q) (fmap_states_ta Some \<A>)"
    by (simp add: finj_Some fmap_states_ta_lang2)
  then show ?thesis
    unfolding reflcl_automaton_def Let_def gen_reflcl_lang[OF st, of "Some |`| Q" \<F>]
    by simp
qed

lemma \<L>_reflcl_reg:
  "\<L> (reflcl_reg \<F> \<A>) = \<L> \<A> \<union>  \<T>\<^sub>G (fset \<F>)"
  by (simp add: \<L>_def reflcl_lang reflcl_reg_def )

subsubsection \<open>Correctness of @{const gen_parallel_closure_automaton} and @{const parallel_closure_reg}\<close>

lemma set_list_subset_nth_conv:
  "set xs \<subseteq> A \<Longrightarrow> i < length xs \<Longrightarrow> xs ! i \<in> A"
  by (metis in_set_conv_nth subset_code(1))

lemma ground_gmctxt_of_mctxt_fill_holes':
  "num_holes C = length ss \<Longrightarrow> ground_mctxt C \<Longrightarrow> \<forall>s\<in>set ss. ground s \<Longrightarrow>
   fill_gholes (gmctxt_of_mctxt C) (map gterm_of_term ss) = gterm_of_term (fill_holes C ss)"
  using ground_gmctxt_of_mctxt_fill_holes
  by (metis term_of_gterm_inv)


lemma refl_over_states_ta_eps_trancl [simp]:
  "(eps (refl_over_states_ta Q \<F> \<A> q))|\<^sup>+| = eps (refl_over_states_ta Q \<F> \<A> q)"
proof (intro fequalityI fsubsetI)
  fix x assume "x |\<in>| (eps (refl_over_states_ta Q \<F> \<A> q))|\<^sup>+|"
  hence "(fst x, snd x) |\<in>| (eps (refl_over_states_ta Q \<F> \<A> q))|\<^sup>+|"
    by (metis prod.exhaust_sel)
  thus "x |\<in>| eps (refl_over_states_ta Q \<F> \<A> q)"
    by (rule ftranclE) (auto simp add: refl_over_states_ta_def image_iff Bex_def dest: ftranclD)
next
  fix x assume "x |\<in>| eps (refl_over_states_ta Q \<F> \<A> q)"
  thus "x |\<in>| (eps (refl_over_states_ta Q \<F> \<A> q))|\<^sup>+|"
    by (metis fr_into_trancl prod.exhaust_sel)
qed

lemma refl_over_states_ta_epsD:
  "(p, q) |\<in>| (eps (refl_over_states_ta Q \<F> \<A> q)) \<Longrightarrow> p |\<in>| Q"
  by (auto simp: refl_over_states_ta_def)

lemma refl_over_states_ta_vars_term:
  "q |\<in>| ta_der (refl_over_states_ta Q \<F> \<A> q) u \<Longrightarrow> vars_term u \<subseteq> insert q (fset Q)"
proof (induct u)
  case (Fun f ts)
  from Fun(2) reflcl_rules_args[of _ "length ts" f _ \<F> q]
  have "i < length ts \<Longrightarrow> q |\<in>| ta_der (refl_over_states_ta Q \<F> \<A> q) (ts ! i)" for i
    by (fastforce simp: refl_over_states_ta_def)
  then have "i < length ts \<Longrightarrow> x \<in> vars_term (ts ! i) \<Longrightarrow> x = q \<or> x |\<in>| Q" for i x
    using Fun(1)[OF nth_mem, of i]
    by (meson insert_iff subsetD)
  then show ?case by (fastforce simp: in_set_conv_nth)
qed (auto dest: refl_over_states_ta_epsD)

lemmas refl_over_states_ta_vars_term' =
  refl_over_states_ta_vars_term[unfolded ta_der_to_ta_der' ta_der'_target_args_vars_term_conv,
    THEN set_list_subset_nth_conv, unfolded finsert.rep_eq[symmetric]]

lemma refl_over_states_ta_sound:
  "funas_term u \<subseteq> fset \<F> \<Longrightarrow> vars_term u \<subseteq> insert q (fset (Q |\<inter>| \<Q> \<A>)) \<Longrightarrow> q |\<in>| ta_der (refl_over_states_ta Q \<F> \<A> q) u"
proof (induct u)
  case (Fun f ts)
  have reach: "i < length ts \<Longrightarrow> q |\<in>| ta_der (refl_over_states_ta Q \<F> \<A> q) (ts ! i)" for i
    using Fun(2-) by (intro Fun(1)[OF nth_mem]) (auto simp: SUP_le_iff)
  from Fun(2) have "TA_rule f (replicate (length ts) q) q |\<in>| rules (refl_over_states_ta Q \<F> \<A> q)"
    by (auto simp: refl_over_states_ta_def reflcl_rules_def fimage_iff fBex_def)
  then show ?case using reach
    by force
qed (auto simp: refl_over_states_ta_def)

lemma gen_parallelcl_lang:
  fixes \<A> :: "('q, 'f) ta"
  assumes "q |\<notin>| \<Q> \<A>"
  shows "gta_lang {|q|} (gen_parallel_closure_automaton Q \<F> \<A> q) =
    {fill_gholes C ss | C ss. num_gholes C = length ss \<and> funas_gmctxt C \<subseteq> (fset \<F>) \<and> (\<forall> i < length ss. ss ! i \<in> gta_lang Q \<A>)}"
    (is "?Ls = ?Rs")
proof -
  let ?A = "gen_parallel_closure_automaton Q \<F> \<A> q" let ?B = "refl_over_states_ta Q \<F> \<A> q"
  interpret sq: derivation_split "?A" "\<A>" "?B"
    using assms unfolding derivation_split_def
    by (auto simp: gen_parallel_closure_automaton_def refl_over_states_ta_def \<Q>_def reflcl_rules_def)
  {fix s assume "s \<in> ?Ls" then obtain u where
      seq: "u |\<in>| ta_der' \<A> (term_of_gterm s)" "Var q |\<in>| ta_der'?B u" and
      fin: "q |\<in>| finsert q Q"
      by (auto simp: ta_der_to_ta_der' elim!: gta_langE dest!: sq.ta_der'_split)
    let ?w = "\<lambda> i. ta_der'_source_args u (term_of_gterm s) ! i"
    have "s \<in> ?Rs" using seq(1) ta_der'_Var_funas[OF seq(2)] fin
      using ground_ta_der_statesD[of "?w i" "ta_der'_target_args u ! i" \<A> for i] assms
      using refl_over_states_ta_vars_term'[OF seq(2)]
      using ta_der'_ground_mctxt_structure[OF seq(1)]
      by (force simp: ground_gmctxt_of_mctxt_fill_holes' ta_der'_source_args_term_of_gterm
          intro!: exI[of _ "gmctxt_of_mctxt (ta_der'_target_mctxt u)"]
          exI[of _ "map gterm_of_term (ta_der'_source_args u (term_of_gterm s))"]
          gta_langI[of "ta_der'_target_args u ! i" Q \<A>
            "gterm_of_term (?w i)" for i])}
  then have ls: "?Ls \<subseteq> ?Rs" by blast
  {fix t assume "t \<in> ?Rs"
    then obtain C ss where len: "num_gholes C = length ss" and
      gr_fun: "funas_gmctxt C \<subseteq> fset \<F>" and
      reachA: "\<forall> i < length ss. ss ! i \<in> gta_lang Q \<A>" and
      const: "t = fill_gholes C ss" by auto
    from reachA obtain qs where "length ss = length qs" "\<forall> i < length qs. qs ! i |\<in>| Q |\<inter>| \<Q> \<A>"
      "\<forall> i < length qs. qs ! i |\<in>| ta_der \<A> ((map term_of_gterm ss) ! i)"
      using Ex_list_of_length_P[of "length ss" "\<lambda> q i. q |\<in>| ta_der \<A> (term_of_gterm (ss ! i)) \<and> q |\<in>| Q"]
      by (metis (full_types) finterI gta_langE gterm_ta_der_states length_map map_nth_eq_conv)
    then have "q |\<in>| ta_der ?A (fill_holes (mctxt_of_gmctxt C) (map term_of_gterm ss))"
      using reachA len gr_fun
      by (intro sq.mctxt_const_to_ta_der[of "mctxt_of_gmctxt C" "map term_of_gterm ss" qs q])
        (auto simp: funas_mctxt_of_gmctxt_conv
          dest!: in_set_idx intro!: refl_over_states_ta_sound)
    then have "t \<in> ?Ls" unfolding const
      by (simp add: fill_holes_mctxt_of_gmctxt_to_fill_gholes gta_langI len)}
  then show ?thesis using ls by blast
qed

lemma parallelcl_gmctxt_lang:
  fixes \<A> :: "('q, 'f) reg"
  shows "\<L> (parallel_closure_reg \<F> \<A>) =
    {fill_gholes C ss |
      C ss. num_gholes C = length ss \<and> funas_gmctxt C \<subseteq> fset \<F> \<and> (\<forall> i < length ss. ss ! i \<in> \<L> \<A>)}"
proof -
  have *: "gta_lang (fin (fmap_states_reg Some \<A>)) (fmap_states_ta Some (ta \<A>)) = gta_lang (fin \<A>) (ta \<A>)"
    by (simp add: finj_Some fmap_states_reg_def fmap_states_ta_lang2)
  have " None |\<notin>| \<Q> (fmap_states_ta Some (ta \<A>))" by auto
  from gen_parallelcl_lang[OF this, of "fin (fmap_states_reg Some \<A>)" \<F>] show ?thesis
    unfolding \<L>_def parallel_closure_reg_def Let_def * fmap_states_reg_def
    by (simp add: finj_Some fmap_states_ta_lang2)
qed

lemma parallelcl_mctxt_lang:
  shows "\<L> (parallel_closure_reg \<F> \<A>) =
    {(gterm_of_term :: ('f, 'q option) term \<Rightarrow> 'f gterm) (fill_holes C (map term_of_gterm ss)) |
      C ss. num_holes C = length ss \<and> ground_mctxt C \<and> funas_mctxt C \<subseteq> fset \<F> \<and> (\<forall> i < length ss. ss ! i \<in> \<L> \<A>)}"
  by (auto simp: parallelcl_gmctxt_lang) (metis funas_gmctxt_of_mctxt num_gholes_gmctxt_of_mctxt
      ground_gmctxt_of_gterm_of_term funas_mctxt_of_gmctxt_conv
      ground_mctxt_of_gmctxt mctxt_of_gmctxt_fill_holes num_holes_mctxt_of_gmctxt)+ 

subsubsection \<open>Correctness of @{const gen_ctxt_closure_reg} and @{const ctxt_closure_reg}\<close>

lemma semantic_path_rules_rhs:
  "r |\<in>| semantic_path_rules Q q\<^sub>c q\<^sub>i q\<^sub>f \<Longrightarrow> r_rhs r = q\<^sub>f"
  by (auto simp: semantic_path_rules_def)

lemma reflcl_over_single_ta_transl [simp]:
  "(eps (reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f))|\<^sup>+| = eps (reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f)"
proof (intro fequalityI fsubsetI)
  fix x assume "x |\<in>| (eps (reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f))|\<^sup>+|"
  hence "(fst x, snd x) |\<in>| (eps (reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f))|\<^sup>+|"
    by simp
  thus "x |\<in>| eps (reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f)"
    by (smt (verit, ccfv_threshold) fimageE ftranclD ftranclE prod.collapse
        reflcl_over_single_ta_def snd_conv ta.sel(2))
next
  show "\<And>x. x |\<in>| eps (reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f) \<Longrightarrow>
    x |\<in>| (eps (reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f))|\<^sup>+|"
    by auto
qed

lemma reflcl_over_single_ta_epsD:
  "(p, q\<^sub>f) |\<in>| eps (reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f) \<Longrightarrow> p |\<in>| Q"
  "(p, q) |\<in>| eps (reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f) \<Longrightarrow> q = q\<^sub>f"
  by (auto simp: reflcl_over_single_ta_def)

lemma reflcl_over_single_ta_rules_split:
  "r |\<in>| rules (reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f) \<Longrightarrow>
     r |\<in>| reflcl_rules \<F> q\<^sub>c \<or> r |\<in>| semantic_path_rules \<F> q\<^sub>c q\<^sub>f q\<^sub>f"
  by (auto simp: reflcl_over_single_ta_def)

lemma reflcl_over_single_ta_rules_semantic_path_rulesI:
  "r |\<in>| semantic_path_rules \<F> q\<^sub>c q\<^sub>f q\<^sub>f \<Longrightarrow> r |\<in>| rules (reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f)"
  by (auto simp: reflcl_over_single_ta_def)

lemma semantic_path_rules_fmember [intro]:
  "TA_rule f qs q |\<in>| semantic_path_rules \<F> q\<^sub>c q\<^sub>i q\<^sub>f \<longleftrightarrow> (\<exists> n i. (f, n) |\<in>| \<F> \<and> i < n \<and> q = q\<^sub>f \<and>
    (qs = (replicate n q\<^sub>c)[i := q\<^sub>i]))" (is "?Ls \<longleftrightarrow> ?Rs")
  by (force simp: semantic_path_rules_def fBex_def fimage_iff fset_of_list_elem)

lemma semantic_path_rules_fmemberD:
  "r |\<in>| semantic_path_rules \<F> q\<^sub>c q\<^sub>i q\<^sub>f \<Longrightarrow> (\<exists> n i. (r_root r, n) |\<in>| \<F> \<and> i < n \<and> r_rhs r = q\<^sub>f \<and>
    (r_lhs_states r = (replicate n q\<^sub>c)[i := q\<^sub>i]))"
  by (cases r) (simp add: semantic_path_rules_fmember) 


lemma reflcl_over_single_ta_vars_term_q\<^sub>c:
  "q\<^sub>c \<noteq> q\<^sub>f \<Longrightarrow> q\<^sub>c |\<in>| ta_der (reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f) u \<Longrightarrow>
    vars_term_list u = replicate (length (vars_term_list u)) q\<^sub>c"
proof (induct u)
  case (Fun f ts)
  have "i < length ts \<Longrightarrow> q\<^sub>c |\<in>| ta_der (reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f) (ts ! i)" for i using Fun(2, 3)
    by (auto dest!: reflcl_over_single_ta_rules_split reflcl_over_single_ta_epsD
        reflcl_rules_args semantic_path_rules_rhs)
  then have "i < length (concat (map vars_term_list ts)) \<Longrightarrow> concat (map vars_term_list ts) ! i = q\<^sub>c" for i
    using Fun(1)[OF nth_mem Fun(2)]
    by (metis (no_types, lifting) length_map nth_concat_split nth_map nth_replicate)
  then show ?case using Fun(1)[OF nth_mem Fun(2)]
    by (auto intro: nth_equalityI)
qed (auto dest: reflcl_over_single_ta_epsD)

lemma reflcl_over_single_ta_vars_term:
  "q\<^sub>c |\<notin>| Q \<Longrightarrow> q\<^sub>c \<noteq> q\<^sub>f \<Longrightarrow> q\<^sub>f |\<in>| ta_der (reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f) u \<Longrightarrow>
   length (vars_term_list u) = n \<Longrightarrow> (\<exists> i q. i < n \<and> q |\<in>| finsert q\<^sub>f Q \<and> vars_term_list u = (replicate n q\<^sub>c)[i := q])"
proof (induct u arbitrary: n)
  case (Var x) then show ?case
    by (intro exI[of _ 0] exI[of _ x]) (auto dest: reflcl_over_single_ta_epsD(1))
next
  case (Fun f ts)
  from Fun(2, 3, 4) obtain qs where rule: "TA_rule f qs q\<^sub>f |\<in>| semantic_path_rules \<F> q\<^sub>c q\<^sub>f q\<^sub>f"
    "length qs = length ts" "\<forall> i < length ts. qs ! i |\<in>| ta_der (reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f) (ts ! i)"
    using semantic_path_rules_rhs reflcl_over_single_ta_epsD
    by (fastforce simp: reflcl_rules_def dest!: reflcl_over_single_ta_rules_split)
  from rule(1, 2) obtain i where states: "i < length ts" "qs = (replicate (length ts) q\<^sub>c)[i := q\<^sub>f]"
    by (auto simp: semantic_path_rules_fmember)
  then have qc: "j < length ts \<Longrightarrow> j \<noteq> i \<Longrightarrow> vars_term_list (ts ! j) = replicate (length (vars_term_list (ts ! j))) q\<^sub>c" for j
    using reflcl_over_single_ta_vars_term_q\<^sub>c[OF Fun(3)] rule
    by force
  from Fun(1)[OF nth_mem, of i] Fun(2, 3) rule states obtain k q where
    qf: "k <  length (vars_term_list (ts ! i))" "q |\<in>| finsert q\<^sub>f Q"
    "vars_term_list (ts ! i) = (replicate (length (vars_term_list (ts ! i))) q\<^sub>c)[k := q]"
    by (auto simp: nth_list_update split: if_splits)
  let ?l = "sum_list (map length (take i (map vars_term_list ts))) + k"
  show ?case using qc qf rule(2) Fun(5) states(1)
    apply (intro exI[of _ ?l] exI[of _ q])
    apply (auto simp: concat_nth_length nth_list_update elim!: nth_concat_split' intro!: nth_equalityI)
       apply (metis length_replicate nth_list_update_eq nth_list_update_neq nth_replicate)+
    done
qed

lemma refl_ta_reflcl_over_single_ta_mono:
  "q |\<in>| ta_der (refl_ta \<F> q) t \<Longrightarrow> q |\<in>| ta_der (reflcl_over_single_ta Q \<F> q q\<^sub>f) t"
  by (intro ta_der_el_mono[where ?\<B> = "reflcl_over_single_ta Q \<F> q q\<^sub>f"])
    (auto simp: refl_ta_def reflcl_over_single_ta_def)

lemma reflcl_over_single_ta_sound:
  assumes "funas_gctxt C \<subseteq> fset \<F>" "q |\<in>| Q"
  shows "q\<^sub>f |\<in>| ta_der (reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f) (ctxt_of_gctxt C)\<langle>Var q\<rangle>" using assms(1)
proof (induct C)
  case GHole then show ?case using assms(2)
    by (auto simp add: reflcl_over_single_ta_def)
next
  case (GMore f ss C ts)
  let ?i = "length ss" let ?n = "Suc (length ss + length ts)"
  from GMore have "(f, ?n) |\<in>| \<F>" by auto
  then have "f ((replicate ?n q\<^sub>c)[?i := q\<^sub>f]) \<rightarrow> q\<^sub>f |\<in>| rules (reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f)"
    using semantic_path_rules_fmember[of f "(replicate ?n q\<^sub>c)[?i := q\<^sub>f]" q\<^sub>f \<F> q\<^sub>c q\<^sub>f q\<^sub>f]
    using less_add_Suc1
    by (intro reflcl_over_single_ta_rules_semantic_path_rulesI) blast
  moreover from GMore(2) have "i < length ss \<Longrightarrow> q\<^sub>c |\<in>| ta_der (reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f) (term_of_gterm (ss ! i))" for i
    by (intro refl_ta_reflcl_over_single_ta_mono refl_ta_sound) (auto simp: SUP_le_iff \<T>\<^sub>G_funas_gterm_conv)
  moreover from GMore(2) have "i < length ts \<Longrightarrow> q\<^sub>c |\<in>| ta_der (reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f) (term_of_gterm (ts ! i))" for i
    by (intro refl_ta_reflcl_over_single_ta_mono refl_ta_sound) (auto simp: SUP_le_iff \<T>\<^sub>G_funas_gterm_conv)
  moreover from GMore have "q\<^sub>f |\<in>| ta_der (reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f) (ctxt_of_gctxt C)\<langle>Var q\<rangle>" by auto
  ultimately show ?case
    by (auto simp: nth_append_Cons simp del: replicate.simps intro!: exI[of _ "(replicate ?n q\<^sub>c)[?i := q\<^sub>f]"] exI[of _ q\<^sub>f])
qed

lemma reflcl_over_single_ta_sig: "ta_sig (reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f) |\<subseteq>| \<F>"
  by (intro ta_sig_fsubsetI)
    (auto simp: reflcl_rules_def dest!: semantic_path_rules_fmemberD reflcl_over_single_ta_rules_split)

lemma gen_gctxtcl_lang:
  assumes "q\<^sub>c |\<notin>| \<Q> \<A>" and "q\<^sub>f |\<notin>| \<Q> \<A>" and "q\<^sub>c |\<notin>| Q" and "q\<^sub>c \<noteq> q\<^sub>f"
  shows "gta_lang {|q\<^sub>f|} (gen_ctxt_closure_automaton Q \<F> \<A> q\<^sub>c q\<^sub>f) =
    {C\<langle>s\<rangle>\<^sub>G | C s. funas_gctxt C \<subseteq> fset \<F> \<and> s \<in> gta_lang Q \<A>}"
    (is "?Ls = ?Rs")
proof -
  let ?A = "gen_ctxt_closure_automaton Q \<F> \<A> q\<^sub>c q\<^sub>f" let ?B = "reflcl_over_single_ta Q \<F> q\<^sub>c q\<^sub>f"
  interpret sq: derivation_split ?A \<A> ?B
    using assms unfolding derivation_split_def
    by (auto simp: gen_ctxt_closure_automaton_def reflcl_over_single_ta_def \<Q>_def reflcl_rules_def
        dest!: semantic_path_rules_rhs)
  {fix s assume "s \<in> ?Ls" then obtain u where
      seq: "u |\<in>| ta_der' \<A> (term_of_gterm s)" "Var q\<^sub>f |\<in>| ta_der'?B u" using sq.ta_der'_split
      by (force simp: ta_der_to_ta_der' elim!: gta_langE)
    have "q\<^sub>c \<notin> vars_term u" "q\<^sub>f \<notin> vars_term u"
      using subsetD[OF ta_der'_gterm_states[OF seq(1)]] assms(1, 2)
      by (auto simp flip: set_vars_term_list)
    then obtain q where vars: "vars_term_list u = [q]" and fin: "q |\<in>| Q" unfolding set_vars_term_list[symmetric]
      using reflcl_over_single_ta_vars_term[unfolded ta_der_to_ta_der', OF assms(3, 4) seq(2), of "length (vars_term_list u)"]
      by (metis (no_types, lifting) finsertE in_set_conv_nth length_0_conv length_Suc_conv
          length_replicate lessI less_Suc_eq_0_disj nth_Cons_0 nth_list_update nth_replicate zero_less_Suc)
    have "s \<in> ?Rs" using fin ta_der'_ground_ctxt_structure[OF seq(1) vars]
      using ta_der'_Var_funas[OF seq(2), THEN subset_trans, OF reflcl_over_single_ta_sig[unfolded less_eq_fset.rep_eq]]
      by (auto intro!: exI[of _ "ta_der'_gctxt u"] exI[of _ "ta_der'_source_gctxt_arg u s"])
        (metis Un_iff funas_ctxt_apply funas_ctxt_of_gctxt_conv subset_eq)
  }
  then have ls: "?Ls \<subseteq> ?Rs" by blast
  {fix t assume "t \<in> ?Rs"
    then obtain C s where gr_fun: "funas_gctxt C \<subseteq> fset \<F>" and reachA: "s \<in> gta_lang Q \<A>" and
      const: "t = C\<langle>s\<rangle>\<^sub>G" by auto
    from reachA obtain q where der_A: "q |\<in>| Q |\<inter>| \<Q> \<A>" "q |\<in>| ta_der \<A> (term_of_gterm s)"
      by auto
    have "q\<^sub>f |\<in>| ta_der ?B (ctxt_of_gctxt C)\<langle>Var q\<rangle>" using gr_fun der_A(1)
      using reflcl_over_single_ta_sound[OF gr_fun]
      by force
    then have "t \<in> ?Ls" unfolding const
      by (meson der_A(2) finsertI1 gta_langI sq.gctxt_const_to_ta_der)}
  then show ?thesis using ls by blast
qed

lemma gen_gctxt_closure_sound:
  fixes \<A> :: "('q, 'f) reg"
  assumes "q\<^sub>c |\<notin>| \<Q>\<^sub>r \<A>" and "q\<^sub>f |\<notin>| \<Q>\<^sub>r \<A>" and "q\<^sub>c |\<notin>| fin \<A>" and "q\<^sub>c \<noteq> q\<^sub>f"
  shows "\<L> (gen_ctxt_closure_reg \<F> \<A> q\<^sub>c q\<^sub>f) = {C\<langle>s\<rangle>\<^sub>G | C s. funas_gctxt C \<subseteq> fset \<F> \<and> s \<in> \<L> \<A>}"
  using gen_gctxtcl_lang[OF assms] unfolding \<L>_def
  by (simp add: gen_ctxt_closure_reg_def)

lemma gen_ctxt_closure_sound:
  fixes \<A> :: "('q, 'f) reg"
  assumes "q\<^sub>c |\<notin>| \<Q>\<^sub>r \<A>" and "q\<^sub>f |\<notin>| \<Q>\<^sub>r \<A>" and "q\<^sub>c |\<notin>| fin \<A>" and "q\<^sub>c \<noteq> q\<^sub>f"
  shows "\<L> (gen_ctxt_closure_reg \<F> \<A> q\<^sub>c q\<^sub>f) =
    {(gterm_of_term :: ('f, 'q) term \<Rightarrow> 'f gterm) C\<langle>term_of_gterm s\<rangle> | C s. ground_ctxt C \<and> funas_ctxt C \<subseteq> fset \<F> \<and> s \<in> \<L> \<A>}"
  unfolding gen_gctxt_closure_sound[OF assms]
  by (metis (no_types, opaque_lifting) ctxt_of_gctxt_apply funas_ctxt_of_gctxt_conv gctxt_of_ctxt_inv ground_ctxt_of_gctxt)

lemma gctxt_closure_lang:
  shows "\<L> (ctxt_closure_reg \<F> \<A>) =
    { C\<langle>s\<rangle>\<^sub>G | C s. funas_gctxt C \<subseteq> fset \<F> \<and> s \<in> \<L> \<A>}"
proof -
  let ?B = "fmap_states_reg Inl (reg_Restr_Q\<^sub>f \<A>)"
  have ts: "Inr False |\<notin>| \<Q>\<^sub>r ?B" "Inr True |\<notin>| \<Q>\<^sub>r ?B" "Inr False |\<notin>| fin (fmap_states_reg Inl (reg_Restr_Q\<^sub>f \<A>))"
    by (auto simp: fmap_states_reg_def fmap_states_ta_def' \<Q>_def rule_states_def) 
  from gen_gctxt_closure_sound[OF ts] show ?thesis 
    by (simp add: ctxt_closure_reg_def)
qed

lemma ctxt_closure_lang:
  shows "\<L> (ctxt_closure_reg \<F> \<A>) =
    {(gterm_of_term :: ('f, 'q + bool) term \<Rightarrow> 'f gterm) C\<langle>term_of_gterm s\<rangle> |
      C s. ground_ctxt C \<and> funas_ctxt C \<subseteq> fset \<F> \<and> s \<in> \<L> \<A>}"
  unfolding gctxt_closure_lang
  by (metis (mono_tags, opaque_lifting) ctxt_of_gctxt_inv funas_gctxt_of_ctxt
      ground_ctxt_of_gctxt ground_gctxt_of_ctxt_apply_gterm term_of_gterm_inv)


subsubsection \<open>Correctness of @{const gen_nhole_ctxt_closure_automaton} and @{const nhole_ctxt_closure_reg}\<close>

lemma reflcl_over_nhole_ctxt_ta_vars_term_q\<^sub>c:
  "q\<^sub>c \<noteq> q\<^sub>f \<Longrightarrow> q\<^sub>c \<noteq> q\<^sub>i \<Longrightarrow> q\<^sub>c |\<in>| ta_der (reflcl_over_nhole_ctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f) u \<Longrightarrow>
    vars_term_list u = replicate (length (vars_term_list u)) q\<^sub>c"
proof (induct u)
  case (Fun f ts)
  have "i < length ts \<Longrightarrow> q\<^sub>c |\<in>| ta_der (reflcl_over_nhole_ctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f) (ts ! i)" for i using Fun(2, 3, 4)
    by (auto simp: reflcl_over_nhole_ctxt_ta_def dest!: ftranclD2 reflcl_rules_args semantic_path_rules_rhs)
  then have "i < length (concat (map vars_term_list ts)) \<Longrightarrow> concat (map vars_term_list ts) ! i = q\<^sub>c" for i
    using Fun(1)[OF nth_mem Fun(2, 3)]
    by (metis (no_types, lifting) length_map map_nth_eq_conv nth_concat_split' nth_replicate)
  then show ?case using Fun(1)[OF nth_mem Fun(2)]
    by (auto intro: nth_equalityI)
qed (auto simp: reflcl_over_nhole_ctxt_ta_def dest: ftranclD2)

lemma reflcl_over_nhole_ctxt_ta_vars_term_Var:
  assumes disj: "q\<^sub>c |\<notin>| Q" "q\<^sub>f |\<notin>| Q" "q\<^sub>c \<noteq> q\<^sub>f" "q\<^sub>i \<noteq> q\<^sub>f" "q\<^sub>c \<noteq> q\<^sub>i"
    and reach: "q\<^sub>i |\<in>| ta_der (reflcl_over_nhole_ctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f) u"
  shows "(\<exists> q. q |\<in>| finsert q\<^sub>i Q \<and>  u = Var q)" using assms
  by (cases u) (fastforce simp: reflcl_over_nhole_ctxt_ta_def reflcl_rules_def dest: ftranclD semantic_path_rules_rhs)+

lemma reflcl_over_nhole_ctxt_ta_vars_term:
  assumes disj: "q\<^sub>c |\<notin>| Q" "q\<^sub>f |\<notin>| Q" "q\<^sub>c \<noteq> q\<^sub>f" "q\<^sub>i \<noteq> q\<^sub>f" "q\<^sub>c \<noteq> q\<^sub>i"
    and reach: "q\<^sub>f |\<in>| ta_der (reflcl_over_nhole_ctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f) u"
  shows "(\<exists> i q. i < length (vars_term_list u) \<and> q |\<in>| {|q\<^sub>i, q\<^sub>f|} |\<union>| Q \<and> vars_term_list u = (replicate (length (vars_term_list u)) q\<^sub>c)[i := q])"
  using assms
proof (induct u)
  case (Var q) then show ?case
    by (intro exI[of _ 0] exI[of _ q]) (auto simp: reflcl_over_nhole_ctxt_ta_def dest: ftranclD2)
next
  case (Fun f ts)
  from Fun(2 - 7) obtain q qs where rule: "TA_rule f qs q\<^sub>f |\<in>| semantic_path_rules \<F> q\<^sub>c q q\<^sub>f" "q = q\<^sub>i \<or> q = q\<^sub>f"
    "length qs = length ts" "\<forall> i < length ts. qs ! i |\<in>| ta_der (reflcl_over_nhole_ctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f) (ts ! i)"
    by (auto simp: reflcl_over_nhole_ctxt_ta_def reflcl_rules_def dest: ftranclD2)
  from rule(1- 3) obtain i where states: "i < length ts" "qs = (replicate (length ts) q\<^sub>c)[i := q]"
    by (auto simp: semantic_path_rules_fmember)
  then have qc: "j < length ts \<Longrightarrow> j \<noteq> i \<Longrightarrow> vars_term_list (ts ! j) = replicate (length (vars_term_list (ts ! j))) q\<^sub>c" for j
    using reflcl_over_nhole_ctxt_ta_vars_term_q\<^sub>c[OF Fun(4, 6)] rule
    by force
  from rule states have "q |\<in>| ta_der (reflcl_over_nhole_ctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f) (ts ! i)"
    by auto
  from this Fun(1)[OF nth_mem, of i, OF _ Fun(2 - 6)] rule(2) states(1) obtain k q' where
    qf: "k < length (vars_term_list (ts ! i))" "q' |\<in>| {|q\<^sub>i, q\<^sub>f|} |\<union>| Q "
    "vars_term_list (ts ! i) = (replicate (length (vars_term_list (ts ! i))) q\<^sub>c)[k :=  q']"
    using reflcl_over_nhole_ctxt_ta_vars_term_Var[OF Fun(2 - 6), of \<F> "ts ! i"]
    by (auto simp: nth_list_update split: if_splits) blast
  let ?l = "sum_list (map length (take i (map vars_term_list ts))) + k"
  show ?case using qc qf rule(3) states(1)
    apply (intro exI[of _ ?l] exI[of _  q'])
    apply (auto 0 0 simp: concat_nth_length nth_list_update elim!: nth_concat_split' intro!: nth_equalityI)
         apply (metis length_replicate nth_list_update_eq nth_list_update_neq nth_replicate)+
    done
qed

lemma reflcl_over_nhole_ctxt_ta_mono:
  "q |\<in>| ta_der (refl_ta \<F> q) t \<Longrightarrow> q |\<in>| ta_der (reflcl_over_nhole_ctxt_ta Q \<F> q q\<^sub>i q\<^sub>f) t"
  by (intro ta_der_el_mono[where ?\<B> = "reflcl_over_nhole_ctxt_ta Q \<F> q q\<^sub>i q\<^sub>f"])
    (auto simp: refl_ta_def reflcl_over_nhole_ctxt_ta_def)


lemma reflcl_over_nhole_ctxt_ta_sound:
  assumes "funas_gctxt C \<subseteq> fset \<F>" "C \<noteq> GHole" "q |\<in>| Q" 
  shows "q\<^sub>f |\<in>| ta_der (reflcl_over_nhole_ctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f) (ctxt_of_gctxt C)\<langle>Var q\<rangle>" using assms(1, 2)
proof (induct C)
  case GHole then show ?case using assms(2)
    by (auto simp add: reflcl_over_single_ta_def)
next
  case (GMore f ss C ts) note IH = this
  let ?i = "length ss" let ?n = "Suc (length ss + length ts)"
  from GMore have funas: "(f, ?n) |\<in>| \<F>" by auto
  from GMore(2) have args_ss: "i < length ss \<Longrightarrow> q\<^sub>c |\<in>| ta_der (reflcl_over_nhole_ctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f) (term_of_gterm (ss ! i))" for i
    by (intro reflcl_over_nhole_ctxt_ta_mono refl_ta_sound) (auto simp: SUP_le_iff \<T>\<^sub>G_funas_gterm_conv)
  from GMore(2) have args_ts: "i < length ts \<Longrightarrow> q\<^sub>c |\<in>| ta_der (reflcl_over_nhole_ctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f) (term_of_gterm (ts ! i))" for i
    by (intro reflcl_over_nhole_ctxt_ta_mono refl_ta_sound) (auto simp: SUP_le_iff \<T>\<^sub>G_funas_gterm_conv)
  note args = this
  show ?case
  proof (cases C)
    case [simp]: GHole
    from funas have "f ((replicate ?n q\<^sub>c)[?i := q\<^sub>i]) \<rightarrow> q\<^sub>f |\<in>| rules (reflcl_over_nhole_ctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f)"
      using semantic_path_rules_fmember[of f "(replicate ?n q\<^sub>c)[?i := q\<^sub>i]" q\<^sub>f \<F> q\<^sub>c q\<^sub>i q\<^sub>f]
      unfolding reflcl_over_nhole_ctxt_ta_def
      by (metis funionCI less_add_Suc1 ta.sel(1))
    moreover have "q\<^sub>i |\<in>| ta_der (reflcl_over_nhole_ctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f) (ctxt_of_gctxt C)\<langle>Var q\<rangle>"
      using assms(3) by (auto simp: reflcl_over_nhole_ctxt_ta_def)
    ultimately show ?thesis using args_ss args_ts
      by (auto simp: nth_append_Cons simp del: replicate.simps intro!: exI[of _ "(replicate ?n q\<^sub>c)[?i := q\<^sub>i]"] exI[of _ q\<^sub>f])
  next
    case (GMore x21 x22 x23 x24)
    then have "q\<^sub>f |\<in>| ta_der (reflcl_over_nhole_ctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f) (ctxt_of_gctxt C)\<langle>Var q\<rangle>"
      using IH(1, 2) by auto
    moreover from funas have "f ((replicate ?n q\<^sub>c)[?i := q\<^sub>f]) \<rightarrow> q\<^sub>f |\<in>| rules (reflcl_over_nhole_ctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f)"
      using semantic_path_rules_fmember[of f "(replicate ?n q\<^sub>c)[?i := q\<^sub>f]" q\<^sub>f \<F> q\<^sub>c q\<^sub>f q\<^sub>f]
      unfolding reflcl_over_nhole_ctxt_ta_def
      by (metis funionI2 less_add_Suc1 ta.sel(1))
    ultimately show ?thesis using args_ss args_ts
      by (auto simp: nth_append_Cons simp del: replicate.simps intro!: exI[of _ "(replicate ?n q\<^sub>c)[?i := q\<^sub>f]"] exI[of _ q\<^sub>f])
  qed
qed

lemma reflcl_over_nhole_ctxt_ta_sig: "ta_sig (reflcl_over_nhole_ctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f) |\<subseteq>| \<F>"
  by (intro ta_sig_fsubsetI)
    (auto simp: reflcl_over_nhole_ctxt_ta_def reflcl_rules_def dest!: semantic_path_rules_fmemberD)

lemma gen_nhole_gctxt_closure_lang:
  assumes "q\<^sub>c |\<notin>| \<Q> \<A>" "q\<^sub>i |\<notin>| \<Q> \<A>" "q\<^sub>f |\<notin>| \<Q> \<A>"
    and "q\<^sub>c |\<notin>| Q" "q\<^sub>f |\<notin>| Q"
    and "q\<^sub>c \<noteq> q\<^sub>i" "q\<^sub>c \<noteq> q\<^sub>f" "q\<^sub>i \<noteq> q\<^sub>f"
  shows "gta_lang {|q\<^sub>f|} (gen_nhole_ctxt_closure_automaton Q \<F> \<A> q\<^sub>c q\<^sub>i q\<^sub>f) =
    {C\<langle>s\<rangle>\<^sub>G | C s. C \<noteq> GHole \<and> funas_gctxt C \<subseteq> fset \<F> \<and> s \<in> gta_lang Q \<A>}"
    (is "?Ls = ?Rs")
proof -
  let ?A = "gen_nhole_ctxt_closure_automaton Q \<F> \<A> q\<^sub>c q\<^sub>i q\<^sub>f" let ?B = "reflcl_over_nhole_ctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f"
  interpret sq: derivation_split ?A \<A> ?B
    using assms unfolding derivation_split_def
    by (auto simp: gen_nhole_ctxt_closure_automaton_def reflcl_over_nhole_ctxt_ta_def \<Q>_def reflcl_rules_def
        dest!: semantic_path_rules_rhs)
  {fix s assume "s \<in> ?Ls" then obtain u where
      seq: "u |\<in>| ta_der' \<A> (term_of_gterm s)" "Var q\<^sub>f |\<in>| ta_der'?B u" using sq.ta_der'_split
      by (force simp: ta_der_to_ta_der' elim!: gta_langE)
    have "q\<^sub>c \<notin> vars_term u" "q\<^sub>i \<notin> vars_term u" "q\<^sub>f \<notin> vars_term u"
      using subsetD[OF ta_der'_gterm_states[OF seq(1)]] assms(1 - 3)
      by (auto simp flip: set_vars_term_list)
    then obtain q where vars: "vars_term_list u = [q]" and fin: "q |\<in>| Q"
      unfolding set_vars_term_list[symmetric]
      using reflcl_over_nhole_ctxt_ta_vars_term[unfolded ta_der_to_ta_der', OF assms(4, 5, 7 - 8, 6) seq(2)]
      by (metis (no_types, opaque_lifting) finsert_iff funion_commute funion_finsert_right
          length_greater_0_conv lessI list.size(3) list_update_code(2) not0_implies_Suc
          nth_list_update_neq nth_mem nth_replicate replicate_Suc replicate_empty sup_bot.right_neutral)
    from seq(2) have "ta_der'_gctxt u \<noteq> GHole" using ta_der'_ground_ctxt_structure(1)[OF seq(1) vars]
      using fin assms(4, 5, 8) by (auto simp: reflcl_over_nhole_ctxt_ta_def dest!: ftranclD2)
    then have "s \<in> ?Rs" using fin ta_der'_ground_ctxt_structure[OF seq(1) vars] seq(2)
      using ta_der'_Var_funas[OF seq(2), THEN subset_trans, OF reflcl_over_nhole_ctxt_ta_sig[unfolded less_eq_fset.rep_eq]]
      by (auto intro!: exI[of _ "ta_der'_gctxt u"] exI[of _ "ta_der'_source_gctxt_arg u s"])
        (metis Un_iff funas_ctxt_apply funas_ctxt_of_gctxt_conv in_mono)}
  then have ls: "?Ls \<subseteq> ?Rs" by blast
  {fix t assume "t \<in> ?Rs"
    then obtain C s where gr_fun: "funas_gctxt C \<subseteq> fset \<F>" "C \<noteq> GHole" and reachA: "s \<in> gta_lang Q \<A>" and
      const: "t = C\<langle>s\<rangle>\<^sub>G" by auto
    from reachA obtain q where der_A: "q |\<in>| Q |\<inter>| \<Q> \<A>" "q |\<in>| ta_der \<A> (term_of_gterm s)"
      by auto
    have "q\<^sub>f |\<in>| ta_der ?B (ctxt_of_gctxt C)\<langle>Var q\<rangle>" using gr_fun der_A(1)
      using reflcl_over_nhole_ctxt_ta_sound[OF gr_fun]
      by force
    then have "t \<in> ?Ls" unfolding const
      by (meson der_A(2) finsertI1 gta_langI sq.gctxt_const_to_ta_der)}
  then show ?thesis using ls by blast
qed

lemma gen_nhole_gctxt_closure_sound:
  assumes "q\<^sub>c |\<notin>| \<Q>\<^sub>r \<A>" "q\<^sub>i |\<notin>| \<Q>\<^sub>r \<A>" "q\<^sub>f |\<notin>| \<Q>\<^sub>r \<A>"
    and "q\<^sub>c |\<notin>| (fin \<A>)" "q\<^sub>f |\<notin>| (fin \<A>)"
    and "q\<^sub>c \<noteq> q\<^sub>i" "q\<^sub>c \<noteq> q\<^sub>f" "q\<^sub>i \<noteq> q\<^sub>f"
  shows "\<L> (gen_nhole_ctxt_closure_reg \<F> \<A> q\<^sub>c q\<^sub>i q\<^sub>f) =
    { C\<langle>s\<rangle>\<^sub>G | C s. C \<noteq> GHole \<and> funas_gctxt C \<subseteq> fset \<F> \<and> s \<in> \<L> \<A>}"
  using gen_nhole_gctxt_closure_lang[OF assms] unfolding \<L>_def
  by (auto simp: gen_nhole_ctxt_closure_reg_def)


lemma nhole_ctxtcl_lang:
  "\<L> (nhole_ctxt_closure_reg \<F> \<A>) =
    { C\<langle>s\<rangle>\<^sub>G | C s. C \<noteq> GHole \<and> funas_gctxt C \<subseteq> fset \<F> \<and> s \<in> \<L> \<A>}"
proof -
  let ?B = "fmap_states_reg (Inl :: 'b \<Rightarrow> 'b + cl_states) (reg_Restr_Q\<^sub>f \<A>)"
  have ts: "Inr cl_state |\<notin>| \<Q>\<^sub>r ?B" "Inr tr_state |\<notin>| \<Q>\<^sub>r ?B" "Inr fin_state |\<notin>| \<Q>\<^sub>r ?B"
    by (auto simp: fmap_states_reg_def)
  then have "Inr cl_state |\<notin>| fin (fmap_states_reg Inl (reg_Restr_Q\<^sub>f \<A>))"
    "Inr fin_state |\<notin>| fin (fmap_states_reg Inl (reg_Restr_Q\<^sub>f \<A>))"
    using finj_Inl_Inr(1) fmap_states_reg_Restr_Q\<^sub>f_fin by blast+
  from gen_nhole_gctxt_closure_sound[OF ts this] show ?thesis
    by (simp add: nhole_ctxt_closure_reg_def Let_def)
qed


subsubsection \<open>Correctness of @{const gen_nhole_mctxt_closure_automaton}\<close>

lemmas reflcl_over_nhole_mctxt_ta_simp = reflcl_over_nhole_mctxt_ta_def reflcl_over_nhole_ctxt_ta_def

lemma reflcl_rules_rhsD:
  "f ps \<rightarrow> q |\<in>| reflcl_rules \<F> q\<^sub>c \<Longrightarrow> q = q\<^sub>c"
  by (auto simp: reflcl_rules_def)

lemma reflcl_over_nhole_mctxt_ta_vars_term:
  assumes "q |\<in>| ta_der (reflcl_over_nhole_mctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f) t"
   and "q\<^sub>c |\<notin>| Q" "q \<noteq> q\<^sub>c" "q\<^sub>f \<noteq> q\<^sub>c" "q\<^sub>i \<noteq> q\<^sub>c"
  shows "vars_term t \<noteq> {}" using assms
proof (induction t arbitrary: q)
  case (Fun f ts)
  let ?A = "reflcl_over_nhole_mctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f"
  from Fun(2) obtain p ps where rule: "TA_rule f ps p |\<in>| rules ?A"
    "length ps = length ts" "\<forall> i < length ts. ps ! i |\<in>| ta_der ?A (ts ! i)"
    "p = q \<or> (p, q) |\<in>| (eps ?A)|\<^sup>+|"
    by force
  from rule(1, 4) Fun(3-) have "p \<noteq> q\<^sub>c"
    by (auto simp: reflcl_over_nhole_mctxt_ta_simp dest: ftranclD)
  then have "\<exists> i < length ts. ps ! i \<noteq> q\<^sub>c" using rule(1, 2) Fun(4-)
    using semantic_path_rules_fmemberD
    by (force simp: reflcl_over_nhole_mctxt_ta_simp dest: reflcl_rules_rhsD)
  then show ?case using Fun(1)[OF nth_mem _ Fun(3) _ Fun(5, 6)] rule(2, 3)
    by fastforce
qed auto

lemma reflcl_over_nhole_mctxt_ta_Fun:
  assumes "q\<^sub>f |\<in>| ta_der (reflcl_over_nhole_mctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f) t" "t \<noteq> Var q\<^sub>f"
    and  "q\<^sub>f \<noteq> q\<^sub>c" "q\<^sub>f \<noteq> q\<^sub>i"
  shows "is_Fun t" using assms
  by (cases t) (auto simp: reflcl_over_nhole_mctxt_ta_simp dest: ftranclD2)

lemma rule_states_reflcl_rulesD:
  "p |\<in>| rule_states (reflcl_rules \<F> q) \<Longrightarrow> p = q"
  by (auto simp: reflcl_rules_def rule_states_def fset_of_list_elem)

lemma rule_states_semantic_path_rulesD:
  "p |\<in>| rule_states (semantic_path_rules \<F> q\<^sub>c q\<^sub>i q\<^sub>f) \<Longrightarrow> p = q\<^sub>c \<or> p = q\<^sub>i \<or> p = q\<^sub>f"
  by (auto simp: rule_states_def dest!: semantic_path_rules_fmemberD)
    (metis in_fset_conv_nth length_list_update length_replicate nth_list_update nth_replicate)

lemma \<Q>_reflcl_over_nhole_mctxt_ta:
  "\<Q> (reflcl_over_nhole_mctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f) |\<subseteq>| Q |\<union>| {|q\<^sub>c, q\<^sub>i, q\<^sub>f|}"
  by (auto 0 0 simp: eps_states_def reflcl_over_nhole_mctxt_ta_simp \<Q>_def
      dest!: rule_states_reflcl_rulesD rule_states_semantic_path_rulesD)

lemma reflcl_over_nhole_mctxt_ta_vars_term_subset_eq:
  assumes "q |\<in>| ta_der (reflcl_over_nhole_mctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f) t" "q = q\<^sub>f \<or> q = q\<^sub>i"
  shows "vars_term t \<subseteq> {q\<^sub>c, q\<^sub>i, q\<^sub>f} \<union> fset Q"
  using fresh_states_ta_der'_pres[OF _ _ assms(1)[unfolded ta_der_to_ta_der']] assms(2)
  using fsubsetD[OF \<Q>_reflcl_over_nhole_mctxt_ta[of Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f]]
  by auto

lemma sig_reflcl_over_nhole_mctxt_ta [simp]:
  "ta_sig (reflcl_over_nhole_mctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f) = \<F>"
  by (force simp: reflcl_over_nhole_mctxt_ta_simp reflcl_rules_def
      dest!: semantic_path_rules_fmemberD intro!: ta_sig_fsubsetI)

lemma reflcl_over_nhole_mctxt_ta_aux_sound:
  assumes "funas_term t \<subseteq> fset \<F>" "vars_term t \<subseteq> fset Q"
  shows "q\<^sub>c |\<in>| ta_der (reflcl_over_nhole_mctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f) t" using assms
proof (induct t)
  case (Var x)
  then show ?case
    by (auto simp: reflcl_over_nhole_mctxt_ta_simp fimage_iff)
     (meson finsertI1 finsertI2 fr_into_trancl ftrancl_into_trancl rev_fimage_eqI)
next
  case (Fun f ts)
  from Fun(2) have "TA_rule f (replicate (length ts) q\<^sub>c) q\<^sub>c |\<in>| rules (reflcl_over_nhole_mctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f)"
    by (auto simp: reflcl_over_nhole_mctxt_ta_simp reflcl_rules_def fimage_iff fBall_def
             split: prod.splits)
  then show ?case using Fun(1)[OF nth_mem] Fun(2-)
    by (auto simp: SUP_le_iff) (metis length_replicate nth_replicate)
qed

lemma reflcl_over_nhole_mctxt_ta_sound:
  assumes "funas_term t \<subseteq> fset \<F>" "vars_term t \<subseteq> fset Q" "vars_term t \<noteq> {}"
  shows "(is_Var t \<longrightarrow> q\<^sub>i |\<in>| ta_der (reflcl_over_nhole_mctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f) t) \<and>
    (is_Fun t \<longrightarrow> q\<^sub>f |\<in>| ta_der (reflcl_over_nhole_mctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f) t)" using assms
proof (induct t)
  case (Fun f ts)
  let ?A = "reflcl_over_nhole_mctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f"
  from Fun(4) obtain i where vars: "i < length ts" "vars_term (ts ! i) \<noteq> {}"
    by (metis SUP_le_iff in_set_conv_nth subset_empty term.set(4))
  consider (v) "is_Var (ts ! i)" | (f) "is_Fun (ts ! i)" by blast
  then show ?case
  proof cases
    case v
    from v Fun(1)[OF nth_mem[OF vars(1)]] have "q\<^sub>i |\<in>| ta_der ?A (ts ! i)"
      using vars Fun(2-) by (auto simp: SUP_le_iff)
    moreover have "f (replicate (length ts) q\<^sub>c)[i := q\<^sub>i] \<rightarrow> q\<^sub>f |\<in>| rules ?A"
      using Fun(2) vars(1)
      by (auto simp: reflcl_over_nhole_mctxt_ta_simp semantic_path_rules_fmember)
    moreover have "j < length ts \<Longrightarrow> q\<^sub>c |\<in>| ta_der ?A (ts ! j)" for j using Fun(2-)
      by (intro reflcl_over_nhole_mctxt_ta_aux_sound) (auto simp: SUP_le_iff)
    ultimately show ?thesis using vars
      by auto (metis length_list_update length_replicate nth_list_update nth_replicate)
  next
    case f
    from f Fun(1)[OF nth_mem[OF vars(1)]] have "q\<^sub>f |\<in>| ta_der ?A (ts ! i)"
      using vars Fun(2-) by (auto simp: SUP_le_iff)
    moreover have "f (replicate (length ts) q\<^sub>c)[i := q\<^sub>f] \<rightarrow> q\<^sub>f |\<in>| rules ?A"
      using Fun(2) vars(1)
      by (auto simp: reflcl_over_nhole_mctxt_ta_simp semantic_path_rules_fmember)
    moreover have "j < length ts \<Longrightarrow> q\<^sub>c |\<in>| ta_der ?A (ts ! j)" for j using Fun(2-)
      by (intro reflcl_over_nhole_mctxt_ta_aux_sound) (auto simp: SUP_le_iff)
    ultimately show ?thesis using vars
      by auto (metis length_list_update length_replicate nth_list_update nth_replicate) 
  qed
qed (auto simp: reflcl_over_nhole_mctxt_ta_simp dest!: ftranclD2)


lemma gen_nhole_gmctxt_closure_lang:
  assumes "q\<^sub>c |\<notin>| \<Q> \<A>" and "q\<^sub>i |\<notin>| \<Q> \<A>" "q\<^sub>f |\<notin>| \<Q> \<A>"
    and "q\<^sub>c |\<notin>| Q" "q\<^sub>f \<noteq> q\<^sub>c" "q\<^sub>f \<noteq> q\<^sub>i" "q\<^sub>i \<noteq> q\<^sub>c"
  shows "gta_lang {|q\<^sub>f|} (gen_nhole_mctxt_closure_automaton Q \<F> \<A> q\<^sub>c q\<^sub>i q\<^sub>f) =
    { fill_gholes C ss |
      C ss. 0 < num_gholes C \<and> num_gholes C = length ss \<and> C \<noteq> GMHole \<and>
      funas_gmctxt C \<subseteq> fset \<F> \<and> (\<forall> i < length ss. ss ! i \<in> gta_lang Q \<A>)}"
    (is "?Ls = ?Rs")
proof -
  let ?A = "gen_nhole_mctxt_closure_automaton Q \<F> \<A> q\<^sub>c q\<^sub>i q\<^sub>f" let ?B = "reflcl_over_nhole_mctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f"
  interpret sq: derivation_split "?A" "\<A>" "?B"
    using assms unfolding derivation_split_def
    by (auto simp: gen_nhole_mctxt_closure_automaton_def reflcl_over_nhole_mctxt_ta_def
        reflcl_over_nhole_ctxt_ta_def \<Q>_def reflcl_rules_def dest!: semantic_path_rules_rhs)
  {fix s assume "s \<in> ?Ls" then obtain u where
      seq: "u |\<in>| ta_der' \<A> (term_of_gterm s)" "Var q\<^sub>f |\<in>| ta_der'?B u"
      by (auto simp: ta_der_to_ta_der' elim!: gta_langE dest!: sq.ta_der'_split)
    note der = seq(2)[unfolded ta_der_to_ta_der'[symmetric]]
    have "vars_term u \<subseteq> fset Q" "vars_term u \<noteq> {}"
      using ta_der'_gterm_states[OF seq(1)] assms(1 - 3)
      using reflcl_over_nhole_mctxt_ta_vars_term[OF der assms(4) assms(5) assms(5) assms(7)]
      using reflcl_over_nhole_mctxt_ta_vars_term_subset_eq[OF der]
      by (metis Un_insert_left insert_is_Un subset_iff subset_insert)+
    then have vars: "\<not> ground u" "i < length (ta_der'_target_args u) \<Longrightarrow> ta_der'_target_args u ! i |\<in>| Q" for i
      by (auto simp: ta_der'_target_args_def split_vars_vars_term_list
          set_list_subset_nth_conv simp flip: set_vars_term_list)
    have hole: "ta_der'_target_mctxt u \<noteq> MHole" using vars assms(3-)
      using reflcl_over_nhole_mctxt_ta_Fun[OF der]
      using ta_der'_mctxt_structure(1, 3)[OF seq(1)]
      by auto (metis fill_holes_MHole gterm_ta_der_states length_map lessI map_nth_eq_conv seq(1) ta_der_to_ta_der' term.disc(1))
    let ?w = "\<lambda> i. ta_der'_source_args u (term_of_gterm s) ! i"
    have "s \<in> ?Rs" using seq(1) ta_der'_Var_funas[OF seq(2)]
      using ground_ta_der_statesD[of "?w i" "ta_der'_target_args u ! i" \<A> for i] assms vars
      using ta_der'_ground_mctxt_structure[OF seq(1)] hole
      by (force simp: ground_gmctxt_of_mctxt_fill_holes' ta_der'_source_args_term_of_gterm
          intro!: exI[of _ "gmctxt_of_mctxt (ta_der'_target_mctxt u)"]
          exI[of _ "map gterm_of_term (ta_der'_source_args u (term_of_gterm s))"]
          gta_langI[of "ta_der'_target_args u ! i" Q \<A>
            "gterm_of_term (?w i)" for i])}
  then have ls: "?Ls \<subseteq> ?Rs" by blast
  {fix t assume "t \<in> ?Rs"
    then obtain C ss where len: "0 < num_gholes C" "num_gholes C = length ss" "C \<noteq> GMHole" and
      gr_fun: "funas_gmctxt C \<subseteq> fset \<F>" and
      reachA: "\<forall> i < length ss. ss ! i \<in> gta_lang Q \<A>" and
      const: "t = fill_gholes C ss" by auto
    from reachA obtain qs where states: "length ss = length qs" "\<forall> i < length qs. qs ! i |\<in>| Q |\<inter>| \<Q> \<A>"
      "\<forall> i < length qs. qs ! i |\<in>| ta_der \<A> ((map term_of_gterm ss) ! i)"
      using Ex_list_of_length_P[of "length ss" "\<lambda> q i. q |\<in>| ta_der \<A> (term_of_gterm (ss ! i)) \<and> q |\<in>| Q"]
      by (metis (full_types) finterI gta_langE gterm_ta_der_states length_map map_nth_eq_conv)
    have [simp]: "is_Fun (fill_holes (mctxt_of_gmctxt C) (map Var qs)) \<longleftrightarrow> True"
      "is_Var (fill_holes (mctxt_of_gmctxt C) (map Var qs)) \<longleftrightarrow> False"
      using len(3) by (cases C, auto)+
    have "q\<^sub>f |\<in>| ta_der ?A (fill_holes (mctxt_of_gmctxt C) (map term_of_gterm ss))"
      using reachA len gr_fun states
      using reflcl_over_nhole_mctxt_ta_sound[of "fill_holes (mctxt_of_gmctxt C) (map Var qs)"]
      by (intro sq.mctxt_const_to_ta_der[of "mctxt_of_gmctxt C" "map term_of_gterm ss" qs q\<^sub>f])
        (auto simp: funas_mctxt_of_gmctxt_conv set_list_subset_eq_nth_conv
          dest!: in_set_idx)
    then have "t \<in> ?Ls" unfolding const
      by (simp add: fill_holes_mctxt_of_gmctxt_to_fill_gholes gta_langI len)}
  then show ?thesis using ls by blast
qed

lemma nhole_gmctxt_closure_lang:
  "\<L> (nhole_mctxt_closure_reg \<F> \<A>) =
    { fill_gholes C ss | C ss. num_gholes C = length ss \<and> 0 < num_gholes C \<and> C \<noteq> GMHole \<and>
      funas_gmctxt C \<subseteq> fset \<F> \<and> (\<forall> i < length ss. ss ! i \<in> \<L> \<A>)}"
  (is "?Ls = ?Rs")
proof -
  let ?B = "fmap_states_reg (Inl :: 'b \<Rightarrow> 'b + cl_states) (reg_Restr_Q\<^sub>f \<A>)"
  have ts: "Inr cl_state |\<notin>| \<Q>\<^sub>r ?B" "Inr tr_state |\<notin>| \<Q>\<^sub>r ?B" "Inr fin_state |\<notin>| \<Q>\<^sub>r ?B"
    "Inr cl_state |\<notin>| fin ?B"
    by (auto simp: fmap_states_reg_def)
  have [simp]: "gta_lang (fin (fmap_states_reg Inl (reg_Restr_Q\<^sub>f \<A>))) (ta (fmap_states_reg Inl (reg_Restr_Q\<^sub>f \<A>)))
    = gta_lang (fin \<A>) (ta \<A>)"
    by (metis \<L>_def \<L>_fmap_states_reg_Inl_Inr(1) reg_Rest_fin_states) 
  from gen_nhole_gmctxt_closure_lang[OF ts] show ?thesis 
    by (auto simp add: nhole_mctxt_closure_reg_def gen_nhole_mctxt_closure_reg_def Let_def \<L>_def)
qed

subsubsection \<open>Correctness of @{const gen_mctxt_closure_reg} and @{const mctxt_closure_reg}\<close>

lemma gen_gmctxt_closure_lang:
  assumes "q\<^sub>c |\<notin>| \<Q> \<A>" and "q\<^sub>i |\<notin>| \<Q> \<A>" "q\<^sub>f |\<notin>| \<Q> \<A>"
    and disj: "q\<^sub>c |\<notin>| Q" "q\<^sub>f \<noteq> q\<^sub>c" "q\<^sub>f \<noteq> q\<^sub>i" "q\<^sub>i \<noteq> q\<^sub>c"
  shows "gta_lang {|q\<^sub>f, q\<^sub>i|} (gen_nhole_mctxt_closure_automaton Q \<F> \<A> q\<^sub>c q\<^sub>i q\<^sub>f) =
    { fill_gholes C ss |
      C ss. 0 < num_gholes C \<and> num_gholes C = length ss \<and>
      funas_gmctxt C \<subseteq> fset \<F> \<and> (\<forall> i < length ss. ss ! i \<in> gta_lang Q \<A>)}"
    (is "?Ls = ?Rs")
proof -
  let ?A = "gen_nhole_mctxt_closure_automaton Q \<F> \<A> q\<^sub>c q\<^sub>i q\<^sub>f" let ?B = "reflcl_over_nhole_mctxt_ta Q \<F> q\<^sub>c q\<^sub>i q\<^sub>f"
  interpret sq: derivation_split "?A" "\<A>" "?B"
    using assms unfolding derivation_split_def
    by (auto simp: gen_nhole_mctxt_closure_automaton_def reflcl_over_nhole_mctxt_ta_def
        reflcl_over_nhole_ctxt_ta_def \<Q>_def reflcl_rules_def dest!: semantic_path_rules_rhs)
  {fix s assume "s \<in> ?Ls" then obtain u q where
      seq: "u |\<in>| ta_der' \<A> (term_of_gterm s)" "Var q |\<in>| ta_der'?B u" "q = q\<^sub>f \<or> q = q\<^sub>i"
      by (auto simp: ta_der_to_ta_der' elim!: gta_langE dest!: sq.ta_der'_split)
    have "vars_term u \<subseteq> fset Q" "vars_term u \<noteq> {}"
      using ta_der'_gterm_states[OF seq(1)] assms seq(3)
      using reflcl_over_nhole_mctxt_ta_vars_term[OF seq(2)[unfolded ta_der_to_ta_der'[symmetric]] disj(1) _ disj(2, 4)]
      using reflcl_over_nhole_mctxt_ta_vars_term_subset_eq[OF seq(2)[unfolded ta_der_to_ta_der'[symmetric]] seq(3)]
      by (metis Un_insert_left subsetD subset_insert sup_bot_left)+
    then have vars: "\<not> ground u" "i < length (ta_der'_target_args u) \<Longrightarrow> ta_der'_target_args u ! i |\<in>| Q" for i
      by (auto simp: ta_der'_target_args_def split_vars_vars_term_list
          set_list_subset_nth_conv simp flip: set_vars_term_list)
    let ?w = "\<lambda> i. ta_der'_source_args u (term_of_gterm s) ! i"
    have "s \<in> ?Rs" using seq(1) ta_der'_Var_funas[OF seq(2)]
      using ground_ta_der_statesD[of "?w i" "ta_der'_target_args u ! i" \<A> for i] assms vars
      using ta_der'_ground_mctxt_structure[OF seq(1)]
      by (force simp: ground_gmctxt_of_mctxt_fill_holes' ta_der'_source_args_term_of_gterm
          intro!: exI[of _ "gmctxt_of_mctxt (ta_der'_target_mctxt u)"]
          exI[of _ "map gterm_of_term (ta_der'_source_args u (term_of_gterm s))"]
          gta_langI[of "ta_der'_target_args u ! i" Q \<A>
            "gterm_of_term (?w i)" for i])}
  then have "?Ls \<subseteq> ?Rs" by blast
  moreover
  {fix t assume "t \<in> ?Rs"
    then obtain C ss where len: "0 < num_gholes C" "num_gholes C = length ss" and
      gr_fun: "funas_gmctxt C \<subseteq> fset \<F>" and
      reachA: "\<forall> i < length ss. ss ! i \<in> gta_lang Q \<A>" and
      const: "t = fill_gholes C ss" by auto
    from const have const': "term_of_gterm t = fill_holes (mctxt_of_gmctxt C) (map term_of_gterm ss)"
      by (simp add: fill_holes_mctxt_of_gmctxt_to_fill_gholes len(2))
    from reachA obtain qs where states: "length ss = length qs" "\<forall> i < length qs. qs ! i |\<in>| Q |\<inter>| \<Q> \<A>"
      "\<forall> i < length qs. qs ! i |\<in>| ta_der \<A> ((map term_of_gterm ss) ! i)"
      using Ex_list_of_length_P[of "length ss" "\<lambda> q i. q |\<in>| ta_der \<A> (term_of_gterm (ss ! i)) \<and> q |\<in>| Q"]
      by (metis (full_types) finterI gta_langE gterm_ta_der_states length_map map_nth_eq_conv)
    have "C = GMHole \<Longrightarrow> is_Var (fill_holes (mctxt_of_gmctxt C) (map Var qs)) = True" using len states(1)
      by (metis fill_holes_MHole length_map mctxt_of_gmctxt.simps(1) nth_map num_gholes.simps(1) term.disc(1))
    then have hole: "C = GMHole \<Longrightarrow> q\<^sub>i |\<in>| ta_der ?A (fill_holes (mctxt_of_gmctxt C) (map term_of_gterm ss))"
      using reachA len gr_fun states len
      using reflcl_over_nhole_mctxt_ta_sound[of "fill_holes (mctxt_of_gmctxt C) (map Var qs)"]
      by (intro sq.mctxt_const_to_ta_der[of "mctxt_of_gmctxt C" "map term_of_gterm ss" qs q\<^sub>i])
         (auto simp: funas_mctxt_of_gmctxt_conv set_list_subset_eq_nth_conv
          dest!: in_set_idx)
    have "C \<noteq> GMHole \<Longrightarrow> is_Fun (fill_holes (mctxt_of_gmctxt C) (map Var qs)) = True"
      by (cases C) auto
    then have "C \<noteq> GMHole \<Longrightarrow> q\<^sub>f |\<in>| ta_der ?A (fill_holes (mctxt_of_gmctxt C) (map term_of_gterm ss))"
      using reachA len gr_fun states
      using reflcl_over_nhole_mctxt_ta_sound[of "fill_holes (mctxt_of_gmctxt C) (map Var qs)"]
      by (intro sq.mctxt_const_to_ta_der[of "mctxt_of_gmctxt C" "map term_of_gterm ss" qs q\<^sub>f])
         (auto simp: funas_mctxt_of_gmctxt_conv set_list_subset_eq_nth_conv
          dest!: in_set_idx)
    then have "t \<in> ?Ls" using hole const' unfolding gta_lang_def gta_der_def
      by (metis (mono_tags, lifting) fempty_iff finsert_iff finterI mem_Collect_eq)}
  ultimately show ?thesis
    by (meson subsetI subset_antisym) 
qed


lemma gmctxt_closure_lang:
  "\<L> (mctxt_closure_reg \<F> \<A>) =
    { fill_gholes C ss | C ss. num_gholes C = length ss \<and> 0 < num_gholes C \<and>
      funas_gmctxt C \<subseteq> fset \<F> \<and> (\<forall> i < length ss. ss ! i \<in> \<L> \<A>)}"
  (is "?Ls = ?Rs")
proof -
  let ?B = "fmap_states_reg (Inl :: 'b \<Rightarrow> 'b + cl_states) (reg_Restr_Q\<^sub>f \<A>)"
  have ts: "Inr cl_state |\<notin>| \<Q>\<^sub>r ?B" "Inr tr_state |\<notin>| \<Q>\<^sub>r ?B" "Inr fin_state |\<notin>| \<Q>\<^sub>r ?B"
    "Inr cl_state |\<notin>| fin ?B"
    by (auto simp: fmap_states_reg_def)
  have [simp]: "gta_lang (fin (fmap_states_reg Inl (reg_Restr_Q\<^sub>f \<A>))) (ta (fmap_states_reg Inl (reg_Restr_Q\<^sub>f \<A>)))
    = gta_lang (fin \<A>) (ta \<A>)"
    by (metis \<L>_def \<L>_fmap_states_reg_Inl_Inr(1) reg_Rest_fin_states) 
  from gen_gmctxt_closure_lang[OF ts] show ?thesis
    by (auto simp add: mctxt_closure_reg_def gen_mctxt_closure_reg_def Let_def \<L>_def)
qed


subsubsection \<open>Correctness of @{const nhole_mctxt_reflcl_reg}\<close>

lemma nhole_mctxt_reflcl_lang:
  "\<L> (nhole_mctxt_reflcl_reg \<F> \<A>) = \<L> (nhole_mctxt_closure_reg \<F> \<A>) \<union> \<T>\<^sub>G (fset \<F>)"
proof -
  let ?refl = "Reg {|fin_clstate|} (refl_ta \<F> (fin_clstate))"
  {fix t assume "t \<in> \<L> ?refl" then have "t \<in> \<T>\<^sub>G (fset \<F>)"
      using reg_funas by fastforce}
  moreover
  {fix t assume "t \<in> \<T>\<^sub>G (fset \<F>)" then have "t \<in> \<L> ?refl"
      by (simp add: \<L>_def gta_langI refl_ta_sound)}
  ultimately have *: "\<L> ?refl = \<T>\<^sub>G (fset \<F>)"
    by blast
  show ?thesis unfolding nhole_mctxt_reflcl_reg_def \<L>_union * by simp
qed
declare ta_union_def [simp del]
end