theory NF
  imports
    Saturation
    Bot_Terms
    Regular_Tree_Relations.Tree_Automata
begin

subsection \<open>Recognizing normal forms of left linear TRSs\<close>

interpretation lift_total: semilattice_closure_partial_operator "\<lambda> x y. (x, y) \<in> mergeP" "(\<up>)" "\<lambda> x y. x \<le>\<^sub>b y" Bot
  apply unfold_locales apply (auto simp: merge_refl merge_symmetric merge_terms_assoc merge_terms_idem merge_bot_args_bless_eq_merge)
  using merge_dist apply blast
  using megeP_ass apply blast
  using merge_terms_commutative apply blast
  apply (metis bless_eq_mergeP bless_eq_trans merge_bot_args_bless_eq_merge merge_dist merge_symmetric merge_terms_commutative)
  apply (metis merge_bot_args_bless_eq_merge merge_symmetric merge_terms_commutative)
  using bless_eq_closued_under_supremum bless_eq_trans bless_eq_anti_sym
  by blast+

abbreviation "psubt_lhs_bot R \<equiv> {t\<^sup>\<bottom> | s t. s \<in> R \<and> s \<rhd> t}"
abbreviation "closure S \<equiv> lift_total.cl.pred_closure S"

definition states where
  "states R = insert Bot (closure (psubt_lhs_bot R))"

lemma psubt_mono:
  "R \<subseteq> S \<Longrightarrow> psubt_lhs_bot R \<subseteq> psubt_lhs_bot S" by auto

lemma states_mono:
  "R \<subseteq> S \<Longrightarrow> states R \<subseteq> states S"
  unfolding states_def using lift_total.cl.closure_mono[OF psubt_mono[of R S]]
  by auto

lemma finite_lhs_subt [simp, intro]:
  assumes "finite R"
  shows "finite (psubt_lhs_bot R)"
proof -
  have conv: "psubt_lhs_bot R = term_to_bot_term ` {t | s t . s \<in> R \<and> s \<rhd> t}" by auto
  from assms have "finite {t | s t . s \<in> R \<and> s \<rhd> t}"
    by (simp add: finite_strict_subterms) 
  then show ?thesis using conv by auto
qed

lemma states_ref_closure:
  "states R \<subseteq> insert Bot (closure (psubt_lhs_bot R))"
  unfolding states_def by auto

lemma finite_R_finite_states [simp, intro]:
  "finite R \<Longrightarrow> finite (states R)"
  using finite_lhs_subt states_ref_closure
  using lift_total.cl.finite_S_finite_closure finite_subset
  by fastforce

abbreviation "lift_sup_small s S \<equiv> lift_total.supremum (lift_total.smaller_subset (Some s) (Some ` S))"
abbreviation "bound_max s S \<equiv> the (lift_sup_small s S)"

lemma bound_max_state_set:
  assumes "finite R"
  shows "bound_max t (psubt_lhs_bot R) \<in> states R"
  using lift_total.supremum_neut_or_in_closure[OF finite_lhs_subt[OF assms], of t]
  unfolding states_def by auto

context
includes fset.lifting
begin
lift_definition fstates :: "('a, 'b) term fset \<Rightarrow> 'a bot_term fset" is states
  by simp

lemma bound_max_state_fset:
  "bound_max t (psubt_lhs_bot (fset R)) |\<in>| fstates R"
  using bound_max_state_set[of "fset R" t]
  using fstates.rep_eq by fastforce

end

definition nf_rules where
  "nf_rules R \<F> = {|TA_rule f qs q | f qs q. (f, length qs) |\<in>| \<F> \<and> fset_of_list qs |\<subseteq>| fstates R \<and>
      \<not>(\<exists> l |\<in>| R. l\<^sup>\<bottom> \<le>\<^sub>b BFun f qs) \<and> q = bound_max (BFun f qs) (psubt_lhs_bot (fset R))|}"

lemma nf_rules_fmember:
  "TA_rule f qs q |\<in>| nf_rules R \<F> \<longleftrightarrow> (f, length qs) |\<in>| \<F> \<and> fset_of_list qs |\<subseteq>| fstates R \<and>
    \<not>(\<exists> l |\<in>| R. l\<^sup>\<bottom> \<le>\<^sub>b BFun f qs) \<and> q = bound_max (BFun f qs) (psubt_lhs_bot (fset R))"
proof -
  let ?subP = "\<lambda> n qs. fset_of_list qs |\<subseteq>| fstates R \<and> length qs = n"
  let ?sub = "\<lambda> n. Collect (?subP n)"
  have *: "finite (?sub n)" for n
    using finite_lists_length_eq[of "fset (fstates R)" n]
    by (simp add: less_eq_fset.rep_eq fset_of_list.rep_eq)
  {fix f n assume mem: "(f, n) \<in> fset \<F>"
    have **: "{f} \<times> (?sub n) = {(f, qs) |qs. ?subP n qs}" by auto
    from mem have "finite {(f, qs) |qs. ?subP n qs}" using *
      using finite_cartesian_product[OF _ *[of n], of "{f}"] unfolding ** by simp}
  then have *: "finite (\<Union> (f, n) \<in> fset \<F> . {(f, qs) | qs. ?subP n qs})" by auto
  have **: "(\<Union> (f, n) \<in> fset \<F> . {(f, qs) | qs. ?subP n qs}) = {(f, qs) | f qs. (f, length qs) |\<in>| \<F> \<and> ?subP (length qs) qs}"
    by auto
  have *: "finite ({(f, qs) | f qs. (f, length qs) |\<in>| \<F> \<and> ?subP (length qs) qs} \<times> fset (fstates R))"
    using * unfolding ** by (intro finite_cartesian_product) auto
  have **: "{TA_rule f qs q | f qs q. (f, length qs) |\<in>| \<F> \<and> fset_of_list qs |\<subseteq>| fstates R \<and> q |\<in>| fstates R} =
    (\<lambda> ((f, qs), q). TA_rule f qs q) ` ({(f, qs) | f qs. (f, length qs) |\<in>| \<F> \<and> ?subP (length qs) qs} \<times> fset (fstates R))"
    by (auto simp: image_def split!: prod.splits) 
  have f: "finite {TA_rule f qs q | f qs q. (f, length qs) |\<in>| \<F> \<and> fset_of_list qs |\<subseteq>| fstates R \<and> q |\<in>| fstates R}"
    unfolding ** using * by auto
  show ?thesis
    by (auto simp: nf_rules_def bound_max_state_fset intro!: finite_subset[OF _ f])
qed

definition nf_ta where
  "nf_ta R \<F> = TA (nf_rules R \<F>) {||}"

definition nf_reg where
  "nf_reg R \<F> = Reg (fstates R) (nf_ta R \<F>)"

lemma bound_max_sound:
  assumes "finite R"
  shows "bound_max t (psubt_lhs_bot R) \<le>\<^sub>b t"
  using assms lift_total.lift_ord.supremum_smaller_subset[of "Some ` psubt_lhs_bot R" "Some t"]
  by auto (metis (no_types, lifting) lift_less_eq_total.elims(2) option.sel option.simps(3))

lemma Bot_in_filter:
  "Bot \<in> Set.filter (\<lambda>s. s \<le>\<^sub>b t) (states R)"
  by (auto simp: Set.filter_def states_def)

lemma bound_max_exists:
  "\<exists> p. p = bound_max t (psubt_lhs_bot R)"
  by blast

lemma bound_max_unique:
  assumes "p = bound_max t (psubt_lhs_bot R)" and "q = bound_max t (psubt_lhs_bot R)"
  shows "p = q" using assms by force

lemma nf_rule_to_bound_max:
  "f qs \<rightarrow> q |\<in>| nf_rules R \<F> \<Longrightarrow> q = bound_max (BFun f qs) (psubt_lhs_bot (fset R))"
  by (auto simp: nf_rules_fmember)

lemma nf_rules_unique:
  assumes "f qs \<rightarrow> q |\<in>| nf_rules R \<F>" and "f qs \<rightarrow> q' |\<in>| nf_rules R \<F>"
  shows "q = q'" using assms unfolding nf_rules_def
  using nf_rule_to_bound_max[OF assms(1)]  nf_rule_to_bound_max[OF assms(2)]
  using bound_max_unique by blast

lemma nf_ta_det:
  shows "ta_det (nf_ta R \<F>)"
  by (auto simp add: ta_det_def nf_ta_def nf_rules_unique)

lemma term_instance_of_reach_state:
  assumes "q |\<in>| ta_der (nf_ta R \<F>) (adapt_vars t)" and "ground t"
  shows "q \<le>\<^sub>b t\<^sup>\<bottom>" using assms(1, 2)
proof(induct t arbitrary: q)
  case (Fun f ts)
  from Fun(2) obtain qs where wit: "f qs \<rightarrow> q |\<in>| nf_rules R \<F>" "length qs = length ts"
    "\<forall> i < length ts. qs ! i |\<in>| ta_der (nf_ta R \<F>) (adapt_vars (ts ! i))"
    by (auto simp add: nf_ta_def)
  then have "BFun f qs \<le>\<^sub>b Fun f ts\<^sup>\<bottom>" using Fun(1)[OF nth_mem, of i "qs !i" for i] using Fun(3)
    by auto
  then show ?case using bless_eq_trans wit(1) bound_max_sound[of "fset R"]
    by (auto simp: nf_rules_fmember)
qed auto


lemma [simp]: "i < length ss  \<Longrightarrow> l \<rhd> Fun f ss \<Longrightarrow> l \<rhd> ss ! i"
  by (meson nth_mem subterm.dual_order.strict_trans supt.arg)

lemma subt_less_eq_res_less_eq:
  assumes ground: "ground t" and "l |\<in>| R" and "l \<rhd> s" and "s\<^sup>\<bottom> \<le>\<^sub>b t\<^sup>\<bottom>"
    and "q |\<in>| ta_der (nf_ta R \<F>) (adapt_vars t)"
  shows "s\<^sup>\<bottom> \<le>\<^sub>b q" using assms(2-)
proof (induction t arbitrary: q s)
  case (Var x)
  then show ?case using lift_total.anti_sym by fastforce
next
  case (Fun f ts) note IN = this
  from IN obtain qs where rule: "f qs \<rightarrow> q |\<in>| nf_rules R \<F>" and
    reach: "length qs = length ts" "\<forall> i < length ts. qs ! i |\<in>| ta_der (nf_ta R \<F>) (adapt_vars (ts ! i))"
    by (auto simp add: nf_ta_def)
  have q: "lift_sup_small (BFun f qs) (psubt_lhs_bot (fset R)) = Some q"
    using nf_rule_to_bound_max[OF rule] 
    using lift_total.supremum_smaller_exists_unique[OF finite_lhs_subt, of "fset R" "BFun f qs"]
    by simp (metis option.collapse option.distinct(1))
  have subst: "s\<^sup>\<bottom> \<le>\<^sub>b BFun f qs" using IN(1)[OF nth_mem, of i "term.args s ! i" "qs ! i" for i] IN(2-) reach
    by (cases s) (auto elim!: bless_eq.cases)
  have "s\<^sup>\<bottom> \<in> psubt_lhs_bot (fset R)" using Fun(2 - 4)
    by auto
  then have "lift_total.lifted_less_eq (Some (s\<^sup>\<bottom>)) (lift_sup_small (BFun f qs) (psubt_lhs_bot (fset R)))"
    using subst
    by (intro lift_total.lift_ord.supremum_sound)
     (auto simp: lift_total.lift_ord.smaller_subset_def)
  then show ?case using subst q finite_lhs_subt
    by auto
qed

lemma ta_nf_sound1:
  assumes ground: "ground t" and lhs: "l |\<in>| R" and inst: "l\<^sup>\<bottom> \<le>\<^sub>b t\<^sup>\<bottom>"
  shows "ta_der (nf_ta R \<F>) (adapt_vars t) = {||}"
proof (rule ccontr)
  assume ass: "ta_der (nf_ta R \<F>) (adapt_vars t) \<noteq> {||}"
  show False proof (cases t)
    case [simp]: (Fun f ts) from ass
    obtain q qs where fin: "q |\<in>| ta_der (nf_ta R \<F>) (adapt_vars (Fun f ts))" and
      rule: "(f qs \<rightarrow> q) |\<in>| rules (nf_ta R \<F>)" "length qs = length ts" and
      reach: "\<forall> i < length ts. qs ! i |\<in>| ta_der (nf_ta R \<F>) (adapt_vars (ts ! i))"
      by (auto simp add: nf_ta_def) blast
    have "l\<^sup>\<bottom> \<le>\<^sub>b  BFun f qs" using reach assms(1) inst rule(2)
      using subt_less_eq_res_less_eq[OF _ lhs, of "ts ! i" "term.args l ! i" "qs ! i" \<F> for i]
        by (cases l) (auto elim!: bless_eq.cases intro!: bless_eq.step)
    then show ?thesis using lhs rule by (auto simp: nf_ta_def nf_rules_def)
  qed (metis ground ground.simps(1))
qed

lemma ta_nf_tr_to_state:
  assumes "ground t" and "q |\<in>| ta_der (nf_ta R \<F>) (adapt_vars t)"
  shows "q |\<in>| fstates R" using assms bound_max_state_fset
  by (cases t) (auto simp: states_def nf_ta_def nf_rules_def)

lemma ta_nf_sound2:
  assumes linear: "\<forall> l |\<in>| R. linear_term l"
    and "ground (t :: ('f, 'v) term)" and "funas_term t \<subseteq> fset \<F>"
    and NF: "\<And> l s. l |\<in>| R \<Longrightarrow> t \<unrhd> s \<Longrightarrow> \<not> l\<^sup>\<bottom> \<le>\<^sub>b s\<^sup>\<bottom>"
  shows "\<exists> q. q |\<in>| ta_der (nf_ta R \<F>) (adapt_vars t)" using assms(2 - 4)
proof (induct t)
  case (Fun f ts)
  have sub: "\<And> i. i < length ts \<Longrightarrow> (\<And>l s. l |\<in>| R \<Longrightarrow> ts ! i \<unrhd> s \<Longrightarrow> \<not> l\<^sup>\<bottom> \<le>\<^sub>b s\<^sup>\<bottom>) " using Fun(4) nth_mem by blast
  from Fun(1)[OF nth_mem] this Fun(2, 3) obtain qs where
    reach: "(\<forall> i < length ts. qs ! i |\<in>| ta_der (nf_ta R \<F>) (adapt_vars (ts ! i)))" and len: "length qs = length ts"
    using Ex_list_of_length_P[of "length ts" "\<lambda> x i. x |\<in>| (ta_der (nf_ta R \<F>) (adapt_vars (ts ! i)))"]
    by auto (meson UN_subset_iff nth_mem)
  have nt_inst: "\<not> (\<exists> s |\<in>| R. s\<^sup>\<bottom> \<le>\<^sub>b BFun f qs)"
  proof (rule ccontr, simp)
    assume ass: "\<exists> s |\<in>| R. s\<^sup>\<bottom> \<le>\<^sub>b BFun f qs"
    from term_instance_of_reach_state[of "qs ! i" R \<F> "ts ! i" for i] reach Fun(2) len
    have "BFun f qs \<le>\<^sub>b Fun f ts\<^sup>\<bottom>" by auto
    then show False using ass Fun(4) bless_eq_trans by blast
  qed
  obtain q where "q = bound_max (BFun f qs) (psubt_lhs_bot (fset R))" by blast
  then have "f qs \<rightarrow> q |\<in>| rules (nf_ta R \<F>)" using Fun(2 - 4)
    using ta_nf_tr_to_state[of "ts ! i" "qs ! i" R \<F> for i] len nt_inst reach
    by (auto simp: nf_ta_def nf_rules_fmember)
       (metis (no_types, lifting) in_fset_idx nth_mem)
  then show ?case using reach len by auto
qed auto

lemma ta_nf_lang_sound:
  assumes "l |\<in>| R"
  shows "C\<langle>l \<cdot> \<sigma>\<rangle> \<notin> ta_lang (fstates R) (nf_ta R \<F>)"
proof (rule ccontr, simp del: ta_lang_to_gta_lang)
  assume *: "C\<langle>l \<cdot> \<sigma>\<rangle> \<in> ta_lang (fstates R) (nf_ta R \<F>)"
  then have cgr:"ground (C\<langle>l\<cdot>\<sigma>\<rangle>)" unfolding ta_lang_def by force
  then have gr: "ground (l \<cdot> \<sigma>)" by simp
  then have  "l\<^sup>\<bottom> \<le>\<^sub>b (l \<cdot> \<sigma>)\<^sup>\<bottom>" using instance_to_bless_eq by blast 
  from ta_nf_sound1[OF gr assms(1) this] have res: "ta_der (nf_ta R \<F>) (adapt_vars (l \<cdot> \<sigma>)) = {||}" .
  from ta_langE * obtain q where "q |\<in>| ta_der (nf_ta R \<F>) (adapt_vars (C\<langle>l\<cdot>\<sigma>\<rangle>))"
    by (metis adapt_vars_adapt_vars)
  with ta_der_ctxt_decompose[OF this[unfolded adapt_vars_ctxt]] res
  show False by blast
qed

lemma ta_nf_lang_complete:
  assumes linear: "\<forall> l |\<in>| R. linear_term l"
      and ground: "ground (t :: ('f, 'v) term)" and sig: "funas_term t \<subseteq> fset \<F>"
      and nf: "\<And>C \<sigma> l. l |\<in>| R \<Longrightarrow> C\<langle>l\<cdot>\<sigma>\<rangle> \<noteq> t"
    shows "t \<in> ta_lang (fstates R) (nf_ta R \<F>)"
proof -
  from nf have "\<And> l s. l |\<in>| R \<Longrightarrow> t \<unrhd> s \<Longrightarrow> \<not> l\<^sup>\<bottom> \<le>\<^sub>b s\<^sup>\<bottom>"
    using bless_eq_to_instance linear by blast
  from ta_nf_sound2[OF linear ground sig] this
  obtain q where "q |\<in>| ta_der (nf_ta R \<F>) (adapt_vars t)" by blast
  from this ta_nf_tr_to_state[OF ground this] ground show ?thesis
    by (intro ta_langI) (auto simp add: nf_ta_def)
qed

lemma ta_nf_\<L>_complete:
  assumes linear: "\<forall> l |\<in>| R. linear_term l"
      and sig: "funas_gterm t \<subseteq> fset \<F>"
      and nf: "\<And>C \<sigma> l. l |\<in>| R \<Longrightarrow> C\<langle>l\<cdot>\<sigma>\<rangle> \<noteq> (term_of_gterm t)"
    shows "t \<in> \<L> (nf_reg R \<F>)"
  using ta_nf_lang_complete[of R "term_of_gterm t" \<F>] assms
  by (force simp: \<L>_def nf_reg_def funas_term_of_gterm_conv)

lemma nf_ta_funas:
  assumes "ground t" "q |\<in>| ta_der (nf_ta R \<F>) t"
  shows "funas_term t \<subseteq> fset \<F>" using assms
proof (induct t arbitrary: q)
  case (Fun f ts)
  from Fun(2-) have "(f, length ts) |\<in>| \<F>"
    by (auto simp: nf_ta_def nf_rules_def)
  then show ?case using Fun
    apply simp
    by (smt (verit) Union_least image_iff in_set_idx)
qed auto

lemma gta_lang_nf_ta_funas:
  assumes "t \<in> \<L> (nf_reg R \<F>)"
  shows "funas_gterm t \<subseteq> fset \<F>" using assms nf_ta_funas[of "term_of_gterm t" _ R \<F>]
  unfolding nf_reg_def \<L>_def
  by (auto simp: funas_term_of_gterm_conv)

end
