theory GTT_RRn
  imports Regular_Tree_Relations.GTT
    TA_Clousure_Const
    Context_RR2
    Lift_Root_Step
begin                 


section \<open>Connecting regular tree languages to set/relation specifications\<close>
abbreviation ggtt_lang where
  "ggtt_lang F G \<equiv> map_both gterm_of_term ` (Restr (gtt_lang_terms G) {t. funas_term t \<subseteq> fset F})"

lemma ground_mctxt_map_vars_mctxt [simp]:
  "ground_mctxt (map_vars_mctxt f C) = ground_mctxt C"
  by (induct C) auto

lemma root_single_automaton:
  assumes "RR2_spec \<A> R"
  shows "RR2_spec \<A> (lift_root_step \<F> PRoot ESingle R)"
  using assms unfolding RR2_spec_def
  by (auto simp: lift_root_step.simps)

lemma root_strictparallel_automaton:
  assumes "RR2_spec \<A> R"
  shows "RR2_spec \<A> (lift_root_step \<F> PRoot EStrictParallel R)"
  using assms unfolding RR2_spec_def
  by (auto simp: lift_root_step.simps)

lemma reflcl_automaton:
  assumes "RR2_spec \<A> R"
  shows "RR2_spec (reflcl_reg (lift_sig_RR2 |`| \<F>) \<A>) (lift_root_step (fset \<F>) PRoot EParallel R)"
   unfolding RR2_spec_def \<L>_reflcl_reg
   unfolding lift_root_step.simps \<T>\<^sub>G_equivalent_def assms[unfolded RR2_spec_def]
   by (auto simp flip: \<T>\<^sub>G_equivalent_def)

lemma parallel_closure_automaton:
  assumes "RR2_spec \<A> R"
  shows "RR2_spec (parallel_closure_reg (lift_sig_RR2 |`| \<F>) \<A>) (lift_root_step (fset \<F>) PAny EParallel R)"
  unfolding RR2_spec_def parallelcl_gmctxt_lang lift_root_step.simps
  unfolding gmctxtex_onp_gpair_set_conv assms[unfolded RR2_spec_def]
  by (intro RR2_gmctxt_cl_to_gmctxt) auto

lemma ctxt_closure_automaton:
  assumes "RR2_spec \<A> R"
  shows "RR2_spec (ctxt_closure_reg (lift_sig_RR2 |`| \<F>) \<A>) (lift_root_step (fset \<F>) PAny ESingle R)"
  unfolding RR2_spec_def gctxt_closure_lang lift_root_step.simps
  unfolding gctxtex_onp_gpair_set_conv assms[unfolded RR2_spec_def]
  by (intro RR2_gctxt_cl_to_gctxt) auto

lemma mctxt_closure_automaton:
  assumes "RR2_spec \<A> R"
  shows "RR2_spec (mctxt_closure_reg (lift_sig_RR2 |`| \<F>) \<A>) (lift_root_step (fset \<F>) PAny EStrictParallel R)"
  unfolding RR2_spec_def gmctxt_closure_lang lift_root_step.simps
  unfolding gmctxtex_onp_gpair_set_conv assms[unfolded RR2_spec_def] conj_assoc
  by (intro RR2_gmctxt_cl_to_gmctxt[where ?P = "\<lambda> C. 0 < num_gholes C \<and> funas_gmctxt C \<subseteq> fset (lift_sig_RR2 |`| \<F>)" and
       ?R = "\<lambda> C. 0 < num_gholes C \<and> funas_gmctxt C \<subseteq> fset \<F>", unfolded conj_assoc]) auto

lemma nhole_ctxt_closure_automaton:
  assumes "RR2_spec \<A> R"
  shows "RR2_spec (nhole_ctxt_closure_reg (lift_sig_RR2 |`| \<F>) \<A>) (lift_root_step (fset \<F>) PNonRoot ESingle R)"
  unfolding RR2_spec_def nhole_ctxtcl_lang lift_root_step.simps
  unfolding gctxtex_onp_gpair_set_conv assms[unfolded RR2_spec_def]
  by (intro RR2_gctxt_cl_to_gctxt[where
    ?P = "\<lambda> C. C \<noteq> \<box>\<^sub>G \<and> funas_gctxt C \<subseteq> fset (lift_sig_RR2 |`| \<F>)", unfolded conj_assoc]) auto

lemma nhole_mctxt_closure_automaton:
  assumes "RR2_spec \<A> R"
  shows "RR2_spec (nhole_mctxt_closure_reg (lift_sig_RR2 |`| \<F>) \<A>) (lift_root_step (fset \<F>) PNonRoot EStrictParallel R)"
  unfolding RR2_spec_def nhole_gmctxt_closure_lang lift_root_step.simps
  unfolding gmctxtex_onp_gpair_set_conv assms[unfolded RR2_spec_def]
  by (intro RR2_gmctxt_cl_to_gmctxt[where
    ?P = "\<lambda> C. 0 < num_gholes C \<and> C \<noteq> GMHole \<and> funas_gmctxt C \<subseteq> fset (lift_sig_RR2 |`| \<F>)", unfolded conj_assoc])
    auto

lemma nhole_mctxt_reflcl_automaton:
  assumes "RR2_spec \<A> R"
  shows "RR2_spec (nhole_mctxt_reflcl_reg (lift_sig_RR2 |`| \<F>) \<A>) (lift_root_step (fset \<F>) PNonRoot EParallel R)"
  using nhole_mctxt_closure_automaton[OF assms, of \<F>]
  unfolding RR2_spec_def lift_root_step_Parallel_conv nhole_mctxt_reflcl_lang
  by (auto simp flip: \<T>\<^sub>G_equivalent_def)

definition GTT_to_RR2_root :: "('q, 'f) gtt \<Rightarrow> (_, 'f option \<times> 'f option) ta" where
  "GTT_to_RR2_root \<G> = pair_automaton (fst \<G>) (snd \<G>)"

definition GTT_to_RR2_root_reg where
  "GTT_to_RR2_root_reg \<G> = Reg (map_both Some |`| fId_on (gtt_states \<G>)) (GTT_to_RR2_root \<G>)"

lemma GTT_to_RR2_root:
  "RR2_spec (GTT_to_RR2_root_reg \<G>) (agtt_lang \<G>)"
proof -
  { fix s assume "s \<in> \<L> (GTT_to_RR2_root_reg \<G>)"
    then obtain q where q: "q |\<in>| fin (GTT_to_RR2_root_reg \<G>)" "q |\<in>| ta_der (GTT_to_RR2_root \<G>) (term_of_gterm s)"
      by (auto simp: \<L>_def gta_lang_def GTT_to_RR2_root_reg_def gta_der_def)
    then obtain q' where [simp]: "q = (Some q', Some q')" using q(1) by (auto simp: GTT_to_RR2_root_reg_def)
    have "\<exists>t u q. s = gpair t u \<and> q |\<in>| ta_der (fst \<G>) (term_of_gterm t) \<and> q |\<in>| ta_der (snd \<G>) (term_of_gterm u)"
      using fsubsetD[OF ta_der_mono' q(2), of "pair_automaton (fst \<G>) (snd \<G>)"]
      by (auto simp: GTT_to_RR2_root_def dest!: from_ta_der_pair_automaton(4))
  } moreover
  { fix t u q assume q: "q |\<in>| ta_der (fst \<G>) (term_of_gterm t)" "q |\<in>| ta_der (snd \<G>) (term_of_gterm u)"
    have "lift_fun q |\<in>| map_both Some |`| fId_on (\<Q> (fst \<G>) |\<union>| \<Q> (snd \<G>))"
      using q[THEN fsubsetD[OF ground_ta_der_states[OF  ground_term_of_gterm]]]
      by (auto simp: fimage_iff fBex_def)
    then have "gpair t u \<in> \<L> (GTT_to_RR2_root_reg \<G>)" using q
      using fsubsetD[OF ta_der_mono to_ta_der_pair_automaton(3)[OF q], of "GTT_to_RR2_root \<G>"]
      by (auto simp: \<L>_def GTT_to_RR2_root_def gta_lang_def image_def gtt_states_def
        gta_der_def GTT_to_RR2_root_reg_def)
  } ultimately show ?thesis by (auto simp: RR2_spec_def agtt_lang_def \<L>_def gta_der_def)
qed

lemma swap_GTT_to_RR2_root:
  "gpair s t \<in> \<L> (GTT_to_RR2_root_reg (prod.swap \<G>)) \<longleftrightarrow>
   gpair t s \<in> \<L> (GTT_to_RR2_root_reg \<G>)"
  by (auto simp: GTT_to_RR2_root[unfolded RR2_spec_def] agtt_lang_def)

lemma funas_mctxt_map_vars_mctxt [simp]:
  "funas_mctxt (map_vars_mctxt f C) = funas_mctxt C"
  by (induct C) auto

definition GTT_to_RR2_reg  :: "('f \<times> nat) fset \<Rightarrow> ('q, 'f) gtt \<Rightarrow> (_, 'f option \<times> 'f option) reg" where
  "GTT_to_RR2_reg F G = parallel_closure_reg (lift_sig_RR2 |`| F) (GTT_to_RR2_root_reg G)"

lemma agtt_lang_syms:
  "gtt_syms \<G> |\<subseteq>| \<F> \<Longrightarrow> agtt_lang \<G> \<subseteq> {t. funas_gterm t \<subseteq> fset \<F>} \<times> {t. funas_gterm t \<subseteq> fset \<F>}"
  by (auto simp: agtt_lang_def gta_der_def funas_term_of_gterm_conv)
     (metis ffunas_gterm.rep_eq fin_mono ta_der_gterm_sig)+


lemma gtt_lang_from_agtt_lang:
  "gtt_lang \<G> = lift_root_step UNIV PAny EParallel (agtt_lang \<G>)"
  unfolding lift_root_step.simps agtt_lang_def
  by (auto simp: lift_root_step.simps agtt_lang_def gmctxt_cl_gmctxtex_onp_conv)

lemma GTT_to_RR2:
  assumes "gtt_syms \<G> |\<subseteq>| \<F>"
  shows "RR2_spec (GTT_to_RR2_reg \<F> \<G>) (ggtt_lang \<F> \<G>)"
proof -
  have *: "snd ` (X \<times> X) = X" for X by auto
  show ?thesis unfolding gtt_lang_from_agtt_lang GTT_to_RR2_reg_def RR2_spec_def
    parallel_closure_automaton[OF GTT_to_RR2_root, of \<F> \<G>, unfolded RR2_spec_def]
  proof (intro arg_cong[where f = "\<lambda>X. {gpair t u |t u. (t,u) \<in> X}"] equalityI subrelI, goal_cases)
    case (1 s t) then show ?case
      using subsetD[OF equalityD2[OF gtt_lang_from_agtt_lang], of "(s, t)" \<G>]
      by (intro rev_image_eqI[of "(term_of_gterm s, term_of_gterm t)"])
         (auto simp: funas_term_of_gterm_conv subsetD[OF lift_root_step_mono]
           dest: subsetD[OF lift_root_step_sig[unfolded \<T>\<^sub>G_equivalent_def, OF agtt_lang_syms[OF assms]]])
  next
    case (2 s t)
    from image_mono[OF agtt_lang_syms[OF assms], of snd, unfolded *]
    have *: "snd ` agtt_lang \<G> \<subseteq> gterms UNIV" by auto
    show ?case using 2
      by (auto intro!: lift_root_step_sig_transfer[unfolded \<T>\<^sub>G_equivalent_def, OF _ *, of _ _ _ "fset \<F>"]
        simp: funas_gterm_gterm_of_term funas_term_of_gterm_conv)
  qed
qed


end
