theory Tree_Automata_Det
imports         
  Tree_Automata
begin

subsection \<open>Powerset Construction for Tree Automata\<close>

text \<open>
The idea to treat states and transitions separately is from arXiv:1511.03595. Some parts of
the implementation are also based on that paper. (The Algorithm corresponds roughly to the one
in "Step 5")
\<close>

text \<open>Abstract Definitions and Correctness Proof\<close>

definition ps_reachable_statesp where
  "ps_reachable_statesp \<A> f ps = (\<lambda> q'. \<exists> qs q. TA_rule f qs q |\<in>| rules \<A> \<and> list_all2 (|\<in>|) qs ps \<and>
    (q = q' \<or> (q,q') |\<in>| (eps \<A>)|\<^sup>+|))"

lemma ps_reachable_statespE:
  assumes "ps_reachable_statesp \<A> f qs q"
  obtains ps p where "TA_rule f ps p |\<in>| rules \<A>" "list_all2 (|\<in>|) ps qs" "(p = q \<or> (p, q) |\<in>| (eps \<A>)|\<^sup>+|)"
  using assms unfolding ps_reachable_statesp_def
  by auto

lemma ps_reachable_statesp_\<Q>:
  "ps_reachable_statesp \<A> f ps q \<Longrightarrow> q |\<in>| \<Q> \<A>"
  by (auto simp: ps_reachable_statesp_def simp flip: dest: rule_statesD eps_trancl_statesD)

lemma finite_Collect_ps_statep [simp]:
  "finite (Collect (ps_reachable_statesp \<A> f ps))" (is "finite ?S")
  by (intro finite_subset[of ?S "fset (\<Q> \<A>)"])
     (auto simp: ps_reachable_statesp_\<Q>)
lemmas finite_Collect_ps_statep_unfolded [simp] = finite_Collect_ps_statep[unfolded ps_reachable_statesp_def, simplified]

definition "ps_reachable_states \<A> f ps \<equiv> fCollect (ps_reachable_statesp \<A> f ps)"

lemmas ps_reachable_states_simp = ps_reachable_statesp_def ps_reachable_states_def

lemma ps_reachable_states_fmember:
  "q' |\<in>| ps_reachable_states \<A> f ps \<longleftrightarrow> (\<exists> qs q. TA_rule f qs q |\<in>| rules \<A> \<and>
     list_all2 (|\<in>|) qs ps \<and> (q = q' \<or> (q, q') |\<in>| (eps \<A>)|\<^sup>+|))"
  by (auto simp: ps_reachable_states_simp)

lemma ps_reachable_statesI:
  assumes "TA_rule f ps p |\<in>| rules \<A>" "list_all2 (|\<in>|) ps qs" "(p = q \<or> (p, q) |\<in>| (eps \<A>)|\<^sup>+|)"
  shows "p |\<in>| ps_reachable_states \<A> f qs"
  using assms unfolding ps_reachable_states_simp
  by auto

lemma ps_reachable_states_sig:
  "ps_reachable_states \<A> f ps \<noteq> {||} \<Longrightarrow> (f, length ps) |\<in>| ta_sig \<A>"
  by (auto simp: ps_reachable_states_simp ta_sig_def image_iff intro!: bexI dest!: list_all2_lengthD)

text \<open>
A set of "powerset states" is complete if it is sufficient to capture all (non)deterministic
derivations.
\<close>

definition ps_states_complete_it :: "('a, 'b) ta \<Rightarrow> 'a FSet_Lex_Wrapper fset \<Rightarrow> 'a FSet_Lex_Wrapper fset \<Rightarrow> bool"
  where "ps_states_complete_it \<A> Q Qnext \<equiv>
  \<forall>f ps. fset_of_list ps |\<subseteq>| Q \<and> ps_reachable_states \<A> f (map ex ps) \<noteq> {||} \<longrightarrow> Wrapp (ps_reachable_states \<A> f (map ex ps)) |\<in>| Qnext"

lemma ps_states_complete_itD:
  "ps_states_complete_it \<A> Q Qnext \<Longrightarrow> fset_of_list ps |\<subseteq>| Q \<Longrightarrow>
     ps_reachable_states \<A> f (map ex ps) \<noteq> {||} \<Longrightarrow> Wrapp (ps_reachable_states \<A> f (map ex ps)) |\<in>| Qnext"
  unfolding ps_states_complete_it_def by blast

abbreviation "ps_states_complete \<A> Q \<equiv> ps_states_complete_it \<A> Q Q"

text \<open>The least complete set of states\<close>
inductive_set ps_states_set for \<A> where
  "\<forall> p \<in> set ps. p \<in> ps_states_set \<A> \<Longrightarrow> ps_reachable_states \<A> f (map ex ps) \<noteq> {||} \<Longrightarrow>
    Wrapp (ps_reachable_states \<A> f (map ex ps)) \<in> ps_states_set \<A>"

lemma ps_states_Pow:
  "ps_states_set \<A> \<subseteq> fset (Wrapp |`| fPow (\<Q> \<A>))"
proof -
  {fix q assume "q \<in> ps_states_set \<A>" then have "q \<in> fset (Wrapp |`| fPow (\<Q> \<A>))"
      by induct (auto simp: ps_reachable_statesp_\<Q> ps_reachable_states_def image_iff)}
  then show ?thesis by blast
qed

context
includes fset.lifting
begin
lift_definition ps_states  :: "('a, 'b) ta \<Rightarrow> 'a FSet_Lex_Wrapper fset" is ps_states_set
  by (auto intro: finite_subset[OF ps_states_Pow])

lemma ps_states: "ps_states \<A> |\<subseteq>| Wrapp |`| fPow (\<Q> \<A>)" using ps_states_Pow
  by (simp add: ps_states_Pow less_eq_fset.rep_eq ps_states.rep_eq)

lemmas ps_states_cases = ps_states_set.cases[Transfer.transferred]
lemmas ps_states_induct = ps_states_set.induct[Transfer.transferred]
lemmas ps_states_simps = ps_states_set.simps[Transfer.transferred]
lemmas ps_states_intros= ps_states_set.intros[Transfer.transferred]
end

lemma ps_states_complete:
  "ps_states_complete \<A> (ps_states \<A>)"
  unfolding ps_states_complete_it_def
  by (auto intro: ps_states_intros)

lemma ps_states_least_complete:
  assumes "ps_states_complete_it \<A> Q Qnext" "Qnext |\<subseteq>| Q"
    shows "ps_states \<A> |\<subseteq>| Q"
proof standard
  fix q assume ass: "q |\<in>| ps_states \<A>" then show "q |\<in>| Q"
    using ps_states_complete_itD[OF assms(1)] fsubsetD[OF assms(2)]
    by (induct rule: ps_states_induct[of _ \<A>]) (fastforce intro: ass)+
qed

definition ps_rulesp :: "('a, 'b) ta \<Rightarrow> 'a FSet_Lex_Wrapper fset \<Rightarrow> ('a FSet_Lex_Wrapper, 'b) ta_rule \<Rightarrow> bool" where
  "ps_rulesp \<A> Q = (\<lambda> r. \<exists> f ps p. r = TA_rule f ps (Wrapp p) \<and> fset_of_list ps |\<subseteq>| Q \<and>
     p = ps_reachable_states \<A> f (map ex ps) \<and> p \<noteq> {||})"

definition "ps_rules" where
  "ps_rules \<A> Q \<equiv> fCollect (ps_rulesp \<A> Q)"

lemma finite_ps_rulesp [simp]:
  "finite (Collect (ps_rulesp \<A> Q))" (is "finite ?S")
proof -
  let ?Q = "fset (Wrapp |`| fPow (\<Q> \<A>) |\<union>| Q)" let ?sig = "fset (ta_sig \<A>)"
  define args where "args \<equiv> \<Union> (f,n) \<in> ?sig. {qs| qs. set qs \<subseteq> ?Q \<and> length qs = n}"
  define bound where "bound \<equiv> \<Union>(f,_) \<in> ?sig. \<Union>q \<in> ?Q. \<Union>qs \<in> args. {TA_rule f qs q}"
  have finite: "finite ?Q" "finite ?sig" by (auto intro: finite_subset)
  then have "finite args" using finite_lists_length_eq[OF \<open>finite ?Q\<close>]
    by (force simp: args_def)
  with finite have "finite bound" unfolding bound_def by (auto simp only: finite_UN)
  moreover have "Collect (ps_rulesp \<A> Q) \<subseteq> bound"
  proof standard
    fix r assume *: "r \<in> Collect (ps_rulesp \<A> Q)"
    obtain f ps p where r[simp]: "r = TA_rule f ps p" by (cases r)
    from * obtain qs q where "TA_rule f qs q |\<in>| rules \<A>" and len: "length ps = length qs"
      unfolding ps_rulesp_def ps_reachable_states_simp
      using list_all2_lengthD by fastforce 
    from this have sym: "(f, length qs) \<in> ?sig"
      by auto
    moreover from * have "set ps \<subseteq> ?Q" unfolding ps_rulesp_def
      by (auto simp flip: fset_of_list_elem simp: ps_reachable_statesp_def)
    ultimately have ps: "ps \<in> args"
      by (auto simp only: args_def UN_iff intro!: bexI[of _ "(f, length qs)"] len)  
    from * have "p \<in> ?Q" unfolding ps_rulesp_def ps_reachable_states_def
      using ps_reachable_statesp_\<Q>
      by (fastforce simp add: image_iff)
    with ps sym show "r \<in> bound"
      by (auto simp only: r bound_def UN_iff intro!: bexI[of _ "(f, length qs)"] bexI[of _ "p"] bexI[of _ "ps"])
  qed
  ultimately show ?thesis by (blast intro: finite_subset)
qed

lemmas finite_ps_rulesp_unfolded = finite_ps_rulesp[unfolded ps_rulesp_def, simplified]

lemmas ps_rulesI [intro!] = fCollect_memberI[OF finite_ps_rulesp]

lemma ps_rules_states:
  "rule_states (fCollect (ps_rulesp \<A> Q)) |\<subseteq>| (Wrapp |`| fPow (\<Q> \<A>) |\<union>| Q)"
  by (auto simp: ps_rulesp_def rule_states_def ps_reachable_states_def ps_reachable_statesp_\<Q>) blast

definition ps_ta :: "('q, 'f) ta \<Rightarrow> ('q FSet_Lex_Wrapper, 'f) ta" where
  "ps_ta \<A> = (let Q = ps_states \<A> in
    TA (ps_rules \<A> Q) {||})"

definition ps_ta_Q\<^sub>f :: "'q fset \<Rightarrow> ('q, 'f) ta \<Rightarrow> 'q FSet_Lex_Wrapper fset" where
  "ps_ta_Q\<^sub>f Q \<A> = (let Q' = ps_states \<A> in
    ffilter (\<lambda> S. Q |\<inter>| (ex S) \<noteq> {||}) Q')"

lemma ps_rules_sound:
  assumes "p |\<in>| ta_der (ps_ta \<A>) (term_of_gterm t)"
  shows "ex p |\<subseteq>| ta_der \<A> (term_of_gterm t)" using assms
proof (induction rule: ta_der_gterm_induct)
  case (GFun f ts ps p q)
  then have IH: "\<forall>i < length ts. ex (ps ! i) |\<subseteq>| gta_der \<A> (ts ! i)" unfolding gta_der_def by auto
  show ?case
  proof standard
    fix r assume "r |\<in>| ex q"
    with GFun(1 - 3) obtain qs q' where "TA_rule f qs q' |\<in>| rules \<A>"
      "q' = r \<or> (q', r) |\<in>| (eps \<A>)|\<^sup>+|" "list_all2 (|\<in>|) qs (map ex ps)" 
      by (auto simp: Let_def ps_ta_def ps_rulesp_def ps_reachable_states_simp ps_rules_def)
    then show "r |\<in>| ta_der \<A> (term_of_gterm (GFun f ts))"
      using GFun(2) IH unfolding gta_der_def
      by (force dest!: fsubsetD intro!: exI[of _ q'] exI[of _ qs] simp: list_all2_conv_all_nth)
  qed
qed

lemma ps_ta_nt_empty_set:
  "TA_rule f qs (Wrapp {||}) |\<in>| rules (ps_ta \<A>) \<Longrightarrow> False"
  by (auto simp: ps_ta_def ps_rulesp_def ps_rules_def)

lemma ps_rules_not_empty_reach:
  assumes "Wrapp {||} |\<in>| ta_der (ps_ta \<A>) (term_of_gterm t)"
  shows False using assms
proof (induction t)
  case (GFun f ts)
  then show ?case using ps_ta_nt_empty_set[of f _ \<A>]
    by (auto simp: ps_ta_def)
qed

lemma ps_rules_complete:
  assumes "q |\<in>| ta_der \<A> (term_of_gterm t)"
  shows "\<exists>p. q |\<in>| ex p \<and> p |\<in>| ta_der (ps_ta \<A>) (term_of_gterm t) \<and> p |\<in>| ps_states \<A>" using assms
proof (induction  rule: ta_der_gterm_induct)
  let ?P = "\<lambda>t q p. q |\<in>| ex p \<and> p |\<in>| ta_der (ps_ta \<A>) (term_of_gterm t) \<and> p |\<in>| ps_states \<A>"
  case (GFun f ts ps p q)
  then have "\<forall>i. \<exists>p. i < length ts \<longrightarrow> ?P (ts ! i) (ps ! i) p" by auto
  with choice[OF this] obtain psf where ps: "\<forall>i < length ts. ?P (ts ! i) (ps ! i) (psf i)" by auto
  define qs where "qs = map psf [0 ..< length ts]"
  let ?p = "ps_reachable_states \<A> f (map ex qs)"
  from ps have in_Q: "fset_of_list qs |\<subseteq>| ps_states \<A>"
    by (auto simp: qs_def fset_of_list_elem)
  from ps GFun(2) have all: "list_all2 (|\<in>|) ps (map ex qs)"
    by (auto simp: list_all2_conv_all_nth qs_def)
  then have in_p: "q |\<in>| ?p" using GFun(1, 3)
    unfolding ps_reachable_statesp_def ps_reachable_states_def by auto
  then have rule: "TA_rule f qs (Wrapp ?p) |\<in>| ps_rules \<A> (ps_states \<A>)" using in_Q unfolding ps_rules_def
    by (intro ps_rulesI) (auto simp: ps_rulesp_def)
  from in_Q in_p have "Wrapp ?p |\<in>| (ps_states \<A>)"
    by (auto intro!: ps_states_complete[unfolded ps_states_complete_it_def, rule_format])
  with in_p ps rule show ?case
    by (auto intro!: exI[of _ "Wrapp ?p"] exI[of _ qs] simp: ps_ta_def qs_def)
qed

lemma ps_ta_eps[simp]: "eps (ps_ta \<A>) = {||}" by (auto simp: Let_def ps_ta_def)

lemma ps_ta_det[iff]: "ta_det (ps_ta \<A>)" by (auto simp: Let_def ps_ta_def ta_det_def ps_rulesp_def ps_rules_def)

lemma ps_gta_lang:
  "gta_lang (ps_ta_Q\<^sub>f Q \<A>) (ps_ta \<A>) = gta_lang Q \<A>" (is "?R = ?L")
proof standard
  show "?L \<subseteq> ?R" proof standard
    fix t assume "t \<in> ?L"
    then obtain q where q_res: "q |\<in>| ta_der \<A> (term_of_gterm t)" and q_final: "q |\<in>| Q"
      by auto
    from ps_rules_complete[OF q_res] obtain p where
      "p |\<in>| ps_states \<A>" "q |\<in>| ex p" "p |\<in>| ta_der (ps_ta \<A>) (term_of_gterm t)"
      by auto
    moreover with q_final have "p |\<in>| ps_ta_Q\<^sub>f Q \<A>"
      by (auto simp: ps_ta_Q\<^sub>f_def)
    ultimately show "t \<in> ?R" by auto
  qed
  show "?R \<subseteq> ?L" proof standard
    fix t assume "t \<in> ?R"
    then obtain p where
      p_res: "p |\<in>| ta_der (ps_ta \<A>) (term_of_gterm t)" and p_final: "p |\<in>| ps_ta_Q\<^sub>f Q \<A>"
      by (auto simp: ta_lang_def)
    from ps_rules_sound[OF p_res] have "ex p |\<subseteq>| ta_der \<A> (term_of_gterm t)"
      by auto
    moreover from p_final obtain q where "q |\<in>| ex p" "q |\<in>| Q" by (auto simp:  ps_ta_Q\<^sub>f_def)
    ultimately show "t \<in> ?L" by auto
  qed
qed

definition ps_reg where
  "ps_reg R = Reg (ps_ta_Q\<^sub>f (fin R) (ta R)) (ps_ta (ta R))"

lemma \<L>_ps_reg:
  "\<L> (ps_reg R) = \<L> R"
  by (auto simp: \<L>_def ps_gta_lang ps_reg_def)

lemma ps_ta_states: "\<Q> (ps_ta \<A>) |\<subseteq>| Wrapp |`| fPow (\<Q> \<A>)"
  using ps_rules_states ps_states unfolding ps_ta_def \<Q>_def
  by (auto simp: Let_def ps_rules_def) force

lemma ps_ta_states': "ex |`| \<Q> (ps_ta \<A>) |\<subseteq>| fPow (\<Q> \<A>)"
  using ps_ta_states[of \<A>]
  by fastforce

end
