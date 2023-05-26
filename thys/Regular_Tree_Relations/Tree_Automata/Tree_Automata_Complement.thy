theory Tree_Automata_Complement
  imports Tree_Automata_Det
begin

subsection \<open>Complement closure of regular languages\<close>

definition partially_completely_defined_on where
  "partially_completely_defined_on \<A> \<F> \<longleftrightarrow>
    (\<forall> t. funas_gterm t \<subseteq> fset \<F> \<longleftrightarrow> (\<exists> q. q |\<in>| ta_der \<A> (term_of_gterm t)))"

definition sig_ta where
  "sig_ta \<F> = TA ((\<lambda> (f, n). TA_rule f (replicate n ()) ()) |`| \<F>) {||}"

lemma sig_ta_rules_fmember:
  "TA_rule f qs q |\<in>| rules (sig_ta \<F>) \<longleftrightarrow> (\<exists> n. (f, n) |\<in>| \<F> \<and> qs = replicate n () \<and> q = ())"
  by (auto simp: sig_ta_def fimage_iff fBex_def)

lemma sig_ta_completely_defined:
  "partially_completely_defined_on (sig_ta \<F>) \<F>"
proof -
  {fix t assume "funas_gterm t \<subseteq> fset \<F>"
    then have "() |\<in>| ta_der (sig_ta \<F>) (term_of_gterm t)"
    proof (induct t)
      case (GFun f ts)
      then show ?case
        by (auto simp: sig_ta_rules_fmember SUP_le_iff
                 intro!: exI[of _ "replicate (length ts) ()"])
    qed}
  moreover
  {fix t q assume "q |\<in>| ta_der (sig_ta \<F>) (term_of_gterm t)"
    then have "funas_gterm t \<subseteq> fset \<F>"
    proof (induct rule: ta_der_gterm_induct)
      case (GFun f ts ps p q)
      from GFun(1 - 4) GFun(5)[THEN subsetD] show ?case
        by (auto simp: sig_ta_rules_fmember dest!: in_set_idx)
      qed}
  ultimately show ?thesis
    unfolding partially_completely_defined_on_def
    by blast
qed

lemma ta_der_fsubset_sig_ta_completely:
  assumes "ta_subset (sig_ta \<F>) \<A>" "ta_sig \<A> |\<subseteq>| \<F>"
  shows "partially_completely_defined_on \<A> \<F>"
proof -
  have "ta_der (sig_ta \<F>) t |\<subseteq>| ta_der \<A> t" for t
    using assms by (simp add: ta_der_mono')
  then show ?thesis using sig_ta_completely_defined assms(2)
    by (auto simp: partially_completely_defined_on_def)
       (metis ffunas_gterm.rep_eq fin_mono ta_der_gterm_sig)
qed

lemma completely_definied_ps_taI:
  "partially_completely_defined_on \<A> \<F> \<Longrightarrow> partially_completely_defined_on (ps_ta \<A>) \<F>"
  unfolding partially_completely_defined_on_def
  using ps_rules_not_empty_reach[of \<A>]
  using fsubsetD[OF ps_rules_sound[of _ \<A>]] ps_rules_complete[of _ \<A>]
  by (metis FSet_Lex_Wrapper.collapse fsubsetI fsubset_fempty)

lemma completely_definied_ta_union1I:
  "partially_completely_defined_on \<A> \<F> \<Longrightarrow> ta_sig \<B> |\<subseteq>| \<F> \<Longrightarrow> \<Q> \<A> |\<inter>| \<Q> \<B> = {||} \<Longrightarrow>
     partially_completely_defined_on (ta_union \<A> \<B>) \<F>"
  unfolding partially_completely_defined_on_def
  using ta_union_der_disj_states'[of \<A> \<B>]
  by (auto simp: ta_union_der_disj_states)
     (metis ffunas_gterm.rep_eq fsubset_trans less_eq_fset.rep_eq ta_der_gterm_sig)

lemma completely_definied_fmaps_statesI:
  "partially_completely_defined_on \<A> \<F> \<Longrightarrow> finj_on f (\<Q> \<A>) \<Longrightarrow> partially_completely_defined_on (fmap_states_ta f \<A>) \<F>"
  unfolding partially_completely_defined_on_def
  using fsubsetD[OF ta_der_fmap_states_ta_mono2, of f \<A>]
  using ta_der_to_fmap_states_der[of _ \<A> _ f]
  by (auto simp: fimage_iff fBex_def) fastforce+

lemma det_completely_defined_complement:
  assumes "partially_completely_defined_on \<A> \<F>" "ta_det \<A>"
  shows "gta_lang (\<Q> \<A> |-| Q) \<A> = \<T>\<^sub>G (fset \<F>) - gta_lang Q \<A>" (is "?Ls = ?Rs")
proof -
  {fix t assume "t \<in> ?Ls"
    then obtain p where p: "p |\<in>| \<Q> \<A>" "p |\<notin>| Q" "p |\<in>| ta_der \<A> (term_of_gterm t)"
      by auto
    from ta_detE[OF assms(2) p(3)] have "\<forall> q. q |\<in>| ta_der \<A> (term_of_gterm t) \<longrightarrow> q = p"
      by blast
    moreover have "funas_gterm t \<subseteq> fset \<F>"
      using p(3) assms(1) unfolding partially_completely_defined_on_def
      by (auto simp: less_eq_fset.rep_eq ffunas_gterm.rep_eq)
    ultimately have "t \<in> ?Rs" using p(2)
      by (auto simp: \<T>\<^sub>G_equivalent_def)}
  moreover
  {fix t assume "t \<in> ?Rs"
    then have f: "funas_gterm t \<subseteq> fset \<F>" "\<forall> q. q |\<in>| ta_der \<A> (term_of_gterm t) \<longrightarrow> q |\<notin>| Q"
      by (auto simp: \<T>\<^sub>G_equivalent_def)
    from f(1) obtain p where "p |\<in>| ta_der \<A> (term_of_gterm t)" using assms(1)
      by (force simp: partially_completely_defined_on_def)
    then have "t \<in> ?Ls" using f(2)
      by (auto simp: gterm_ta_der_states intro: gta_langI[of p])}
  ultimately show ?thesis by blast
qed

lemma ta_der_gterm_sig_fset:
  "q |\<in>| ta_der \<A> (term_of_gterm t) \<Longrightarrow> funas_gterm t \<subseteq> fset (ta_sig \<A>)"
  using ta_der_gterm_sig
  by (metis ffunas_gterm.rep_eq less_eq_fset.rep_eq)

definition filter_ta_sig where
  "filter_ta_sig \<F> \<A> = TA (ffilter (\<lambda> r. (r_root r, length (r_lhs_states r)) |\<in>| \<F>) (rules \<A>)) (eps \<A>)"

definition filter_ta_reg where
  "filter_ta_reg \<F> R = Reg (fin R) (filter_ta_sig \<F> (ta R))"

lemma filter_ta_sig:
  "ta_sig (filter_ta_sig \<F> \<A>) |\<subseteq>| \<F>"
  by (auto simp: ta_sig_def filter_ta_sig_def)

lemma filter_ta_sig_lang:
  "gta_lang Q (filter_ta_sig \<F> \<A>) = gta_lang Q \<A> \<inter> \<T>\<^sub>G (fset \<F>)" (is "?Ls = ?Rs")
proof -
  let ?A = "filter_ta_sig \<F> \<A>"
  {fix t assume "t \<in> ?Ls"
    then obtain q where q: "q |\<in>| Q" "q |\<in>| ta_der ?A (term_of_gterm t)"
      by auto
    then have "funas_gterm t \<subseteq> fset \<F>"
      using subset_trans[OF ta_der_gterm_sig_fset[OF q(2)] filter_ta_sig[unfolded less_eq_fset.rep_eq]]
      by blast
    then have "t \<in> ?Rs" using q
      by (auto simp: \<T>\<^sub>G_equivalent_def filter_ta_sig_def
                 intro!: gta_langI[of q] ta_der_el_mono[where ?q = q and \<B> = \<A> and \<A> = ?A])}
  moreover
  {fix t assume ass: "t \<in> ?Rs"
    then have funas: "funas_gterm t \<subseteq> fset \<F>"
      by (auto simp: \<T>\<^sub>G_equivalent_def)
    from ass obtain p where p: "p |\<in>| Q" "p |\<in>| ta_der \<A> (term_of_gterm t)"
      by auto
    from this(2) funas have "p |\<in>| ta_der ?A (term_of_gterm t)"
    proof (induct rule: ta_der_gterm_induct)
      case (GFun f ts ps p q)
      then show ?case
        by (auto simp: filter_ta_sig_def SUP_le_iff intro!: exI[of _ ps] exI[of _ p])
    qed
    then have "t \<in> ?Ls" using p(1) by auto}
  ultimately show ?thesis by blast
qed

lemma \<L>_filter_ta_reg:
  "\<L> (filter_ta_reg \<F> \<A>) = \<L> \<A> \<inter> \<T>\<^sub>G (fset \<F>)"
  using filter_ta_sig_lang
  by (auto simp: \<L>_def filter_ta_reg_def)

definition sig_ta_reg where
  "sig_ta_reg \<F> = Reg {||} (sig_ta \<F>)"

lemma \<L>_sig_ta_reg:
  "\<L> (sig_ta_reg \<F>) = {}"
  by (auto simp: \<L>_def sig_ta_reg_def)

definition complement_reg where
  "complement_reg R \<F> = (let \<A> = ps_reg (reg_union (sig_ta_reg \<F>) R) in
    Reg (\<Q>\<^sub>r \<A> |-| fin \<A>) (ta \<A>))"

lemma \<L>_complement_reg:
  assumes "ta_sig (ta \<A>) |\<subseteq>| \<F>"
  shows "\<L> (complement_reg \<A> \<F>) = \<T>\<^sub>G (fset \<F>) - \<L> \<A>"
proof -
  have "\<L> (complement_reg \<A> \<F>) = \<T>\<^sub>G (fset \<F>) - \<L> (ps_reg (reg_union (sig_ta_reg \<F>) \<A>))"
  unfolding \<L>_def complement_reg_def using assms
  by (auto simp: complement_reg_def Let_def ps_reg_def reg_union_def sig_ta_reg_def
                 sig_ta_completely_defined finj_Inl_Inr
           intro!: det_completely_defined_complement completely_definied_ps_taI
                   completely_definied_ta_union1I completely_definied_fmaps_statesI)
  then show ?thesis
    by (auto simp: \<L>_ps_reg \<L>_union \<L>_sig_ta_reg)
qed

lemma \<L>_complement_filter_reg:
   "\<L> (complement_reg (filter_ta_reg \<F> \<A>) \<F>) = \<T>\<^sub>G (fset \<F>) - \<L> \<A>"
proof -
  have *: "ta_sig (ta (filter_ta_reg \<F> \<A>)) |\<subseteq>| \<F>"
    by (auto simp: filter_ta_reg_def filter_ta_sig)
  show ?thesis unfolding \<L>_complement_reg[OF *] \<L>_filter_ta_reg
    by blast
qed

definition difference_reg where
  "difference_reg R L = (let F = ta_sig (ta R) in
     reg_intersect R (trim_reg (complement_reg (filter_ta_reg F L) F)))"

lemma \<L>_difference_reg:
  "\<L> (difference_reg R L) = \<L> R - \<L> L" (is "?Ls = ?Rs")
  unfolding difference_reg_def Let_def \<L>_trim \<L>_intersect \<L>_complement_filter_reg
  using reg_funas by blast

end