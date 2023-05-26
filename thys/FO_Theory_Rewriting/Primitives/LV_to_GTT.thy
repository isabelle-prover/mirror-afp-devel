section \<open>Primitive constructions\<close>

theory LV_to_GTT
  imports Regular_Tree_Relations.Pair_Automaton   
    Bot_Terms 
    Rewriting
begin

subsection \<open>Recognizing subterms of linear terms\<close>
(* Pattern recognizer automaton *)
abbreviation ffunas_terms where
  "ffunas_terms R \<equiv> |\<Union>| (ffunas_term |`| R)"

definition "states R \<equiv> {t\<^sup>\<bottom> | s t. s \<in> R \<and> s \<unrhd> t}"

lemma states_conv:
  "states R = term_to_bot_term ` (\<Union> s \<in> R. subterms s)"
  unfolding states_def set_all_subteq_subterms
  by auto

lemma finite_states:
  assumes "finite R" shows "finite (states R)"
proof -
  have conv: "states R = term_to_bot_term ` (\<Union> s \<in> R. {t | t. s \<unrhd> t})"
    unfolding states_def by auto
  from assms have "finite (\<Union> s \<in> R. {t | t. s \<unrhd> t})"
    by (intro finite_UN_I2 finite_imageI) (simp add: finite_subterms)+
  then show ?thesis using conv by auto
qed

lemma root_bot_diff:
  "root_bot ` (R - {Bot}) = (root_bot ` R) - {None}"
  using root_bot.elims by auto

lemma root_bot_states_root_subterms:
  "the ` (root_bot ` (states R - {Bot})) = the ` (root ` (\<Union> s \<in> R. subterms s) - {None})"
  unfolding states_conv root_bot_diff
  unfolding image_comp
  by simp

context
includes fset.lifting
begin

lift_definition fstates :: "('f, 'v) term fset \<Rightarrow> 'f bot_term fset" is states
  by (simp add: finite_states)

lift_definition fsubterms :: "('f, 'v) term \<Rightarrow> ('f, 'v) term fset" is subterms
  by (simp add: finite_subterms_fun)

lemmas fsubterms [code] = subterms.simps[Transfer.transferred]

lift_definition ffunas_trs :: "(('f, 'v) term \<times> ('f, 'v) term) fset \<Rightarrow> ('f \<times> nat) fset" is funas_trs
  by (simp add: finite_funas_trs)

lemma fstates_def':
  "t |\<in>| fstates R \<longleftrightarrow> (\<exists> s u. s |\<in>| R \<and> s \<unrhd> u \<and> u\<^sup>\<bottom> = t)"
  by transfer (auto simp: states_def)

lemma fstates_fmemberE [elim!]:
  assumes "t |\<in>| fstates R"
  obtains s u where "s |\<in>| R \<and> s \<unrhd> u \<and> u\<^sup>\<bottom> = t"
  using assms unfolding fstates_def'
  by blast

lemma fstates_fmemberI [intro]:
  "s |\<in>| R \<Longrightarrow> s \<unrhd> u \<Longrightarrow> u\<^sup>\<bottom> |\<in>| fstates R"
  unfolding fstates_def' by blast

lemmas froot_bot_states_root_subterms = root_bot_states_root_subterms[Transfer.transferred]
lemmas root_fsubsterms_ffunas_term_fset = root_substerms_funas_term_set[Transfer.transferred]


lemma fstates[code]:
  "fstates R = term_to_bot_term |`| ( |\<Union>| (fsubterms |`| R))"
  by transfer (auto simp: states_conv)

end

definition ta_rule_sig where 
  "ta_rule_sig = (\<lambda> r. (r_root r, length (r_lhs_states r)))"

primrec term_to_ta_rule where
 "term_to_ta_rule (BFun f ts) = TA_rule f ts (BFun f ts)"

lemma ta_rule_sig_term_to_ta_rule_root:
  "t \<noteq> Bot \<Longrightarrow> ta_rule_sig (term_to_ta_rule t) = the (root_bot t)"
  by (cases t) (auto simp: ta_rule_sig_def)

lemma ta_rule_sig_term_to_ta_rule_root_set:
  assumes "Bot |\<notin>| R"
  shows "ta_rule_sig |`| (term_to_ta_rule |`| R) = the |`| (root_bot |`| R)"
proof -
  {fix x assume "x |\<in>| R" then have "ta_rule_sig (term_to_ta_rule x) = the (root_bot x)"
      using ta_rule_sig_term_to_ta_rule_root[of x] assms
      by auto}
  then show ?thesis
    by (force simp: fimage_iff)
qed

definition pattern_automaton_rules where
  "pattern_automaton_rules \<F> R =
    (let states = (fstates R) - {|Bot|} in
    term_to_ta_rule |`| states |\<union>| (\<lambda> (f, n). TA_rule f (replicate n Bot) Bot) |`| \<F>)"

lemma pattern_automaton_rules_BotD:
  assumes "TA_rule f ss Bot |\<in>| pattern_automaton_rules \<F> R"
  shows "TA_rule f ss Bot |\<in>| (\<lambda> (f, n). TA_rule f (replicate n Bot) Bot) |`| \<F>" using assms
  by (auto simp: pattern_automaton_rules_def)
     (metis ta_rule.inject term_to_bot_term.elims term_to_ta_rule.simps)

lemma pattern_automaton_rules_FunD:
  assumes "TA_rule f ss (BFun g ts) |\<in>| pattern_automaton_rules \<F> R"
  shows "g = f \<and> ts = ss \<and>
     TA_rule f ss (BFun g ts) |\<in>| term_to_ta_rule |`| ((fstates R) - {|Bot|})" using assms
  apply (auto simp: pattern_automaton_rules_def)
  apply (metis bot_term.exhaust ta_rule.inject term_to_ta_rule.simps)
  by (metis (no_types, lifting) ta_rule.inject term_to_bot_term.elims term_to_ta_rule.simps)


definition pattern_automaton where
  "pattern_automaton \<F> R = TA (pattern_automaton_rules \<F> R) {||}"

lemma ta_sig_pattern_automaton [simp]:
  "ta_sig (pattern_automaton \<F> R) = \<F> |\<union>| ffunas_terms R"
proof -
  let ?r = "ta_rule_sig"
  have *:"Bot |\<notin>| (fstates R) - {|Bot|}" by simp
  have f: "\<F> = ?r |`| ((\<lambda> (f, n). TA_rule f (replicate n Bot) Bot) |`| \<F>)"
    by (auto simp: image_iff Bex_def ta_rule_sig_def split!: prod.splits)
  moreover have "ffunas_terms R = ?r |`| (term_to_ta_rule |`| ((fstates R) - {|Bot|}))"
    unfolding ta_rule_sig_term_to_ta_rule_root_set[OF *]
    unfolding froot_bot_states_root_subterms root_fsubsterms_ffunas_term_fset
    by simp
  ultimately show ?thesis unfolding pattern_automaton_def ta_sig_def
    unfolding ta_rule_sig_def pattern_automaton_rules_def
    by (simp add: fimage_funion comp_def) blast
qed

lemma terms_reach_Bot:
  assumes "ffunas_gterm t |\<subseteq>| \<F>"
  shows "Bot |\<in>| ta_der (pattern_automaton \<F> R) (term_of_gterm t)" using assms
proof (induct t)
  case (GFun f ts)
  have [simp]: "s \<in> set ts \<Longrightarrow> ffunas_gterm s |\<subseteq>| \<F>" for s using GFun(2)
    using in_set_idx by fastforce
  from GFun show ?case
    by (auto simp: pattern_automaton_def pattern_automaton_rules_def rev_fimage_eqI
             intro!: exI[of _ "replicate (length ts) Bot"])
qed

lemma pattern_automaton_reach_smaller_term:
  assumes "l |\<in>| R" "l \<unrhd> s" "s\<^sup>\<bottom> \<le>\<^sub>b (term_of_gterm t)\<^sup>\<bottom>" "ffunas_gterm t |\<subseteq>| \<F>"
  shows "s\<^sup>\<bottom> |\<in>| ta_der (pattern_automaton \<F> R) (term_of_gterm t)" using assms(2-)
proof (induct t arbitrary: s)
  case (GFun f ts) show ?case
  proof (cases s)
    case (Var x)
    then show ?thesis using terms_reach_Bot[OF GFun(4)]
      by (auto simp del: ta_der_Fun)
  next
    case [simp]: (Fun g ss)
    let ?ss = "map term_to_bot_term ss"
    have [simp]: "s \<in> set ts \<Longrightarrow> ffunas_gterm s |\<subseteq>| \<F>" for s using GFun(4)
      using in_set_idx by fastforce
    from GFun(3) have s: "g = f" "length ss = length ts" by auto
    from GFun(2) s(2) assms(1) have rule: "TA_rule f ?ss (BFun f ?ss) |\<in>| pattern_automaton_rules \<F> R"
      by (auto simp: s(1) pattern_automaton_rules_def image_iff Bex_def)
    {fix i assume bound: "i < length ts"
      then have sub: "l \<unrhd> ss ! i" using GFun(2) arg_subteq[OF nth_mem, of i ss f]
        unfolding Fun s(1) using s(2) by (metis subterm.order.trans)
      have "ss ! i\<^sup>\<bottom> \<le>\<^sub>b (term_of_gterm (ts ! i):: ('a, 'c) term)\<^sup>\<bottom>" using GFun(3) bound s(2)
        by (auto simp: s elim!: bless_eq.cases)
      from GFun(1)[OF nth_mem sub this] bound
      have "ss ! i\<^sup>\<bottom> |\<in>| ta_der (pattern_automaton \<F> R) (term_of_gterm (ts ! i))"
        by auto}
    then show ?thesis using GFun(2-) s(2) rule
      by (auto simp: s(1) pattern_automaton_def intro!: exI[of _ ?ss] exI[of _ "BFun f ?ss"])
  qed
qed

lemma bot_term_of_gterm_conv:
  "term_of_gterm s\<^sup>\<bottom> = term_of_gterm s\<^sup>\<bottom>"
  by (induct s) auto

lemma pattern_automaton_ground_instance_reach:
  assumes "l |\<in>| R" "l \<cdot> \<sigma> = (term_of_gterm t)" "ffunas_gterm t |\<subseteq>| \<F>"
  shows "l\<^sup>\<bottom> |\<in>| ta_der (pattern_automaton \<F> R) (term_of_gterm t)"
proof -
  let ?t = "(term_of_gterm t) :: ('a, 'a bot_term) term"
  from instance_to_bless_eq[OF assms(2)] have sm: "l\<^sup>\<bottom> \<le>\<^sub>b ?t\<^sup>\<bottom>"
    using bot_term_of_gterm_conv by metis
  show ?thesis using pattern_automaton_reach_smaller_term[OF assms(1) _ sm] assms(3-)
    by auto
qed

lemma pattern_automaton_reach_smallet_term:
  assumes "l\<^sup>\<bottom> |\<in>| ta_der (pattern_automaton \<F> R) t" "ground t"
  shows "l\<^sup>\<bottom> \<le>\<^sub>b t\<^sup>\<bottom>" using assms
proof (induct t arbitrary: l)
  case (Fun f ts) note IH = this show ?case
  proof (cases l)
    case (Fun g ss)
    let ?ss = "map term_to_bot_term ss"
    from IH(2) have rule: "g = f" "length ss = length ts"
      "TA_rule f ?ss (BFun f ?ss) |\<in>| rules (pattern_automaton \<F> R)"
        by (auto simp: Fun pattern_automaton_def dest: pattern_automaton_rules_FunD)
    {fix i assume "i < length ts" 
      then have "ss ! i\<^sup>\<bottom> \<le>\<^sub>b ts ! i\<^sup>\<bottom>" using IH(2, 3) rule(2)
        by (intro IH(1)) (auto simp: Fun pattern_automaton_def dest: pattern_automaton_rules_FunD)}
    then show ?thesis using rule(2)
      by (auto simp: Fun rule(1))  
  qed auto
qed auto

subsection \<open>Recognizing root step relation of LV-TRSs\<close>

definition lv_trs :: "('f, 'v) trs \<Rightarrow> bool" where
  "lv_trs R \<equiv> \<forall>(l, r) \<in> R. linear_term l \<and> linear_term r \<and> (vars_term l \<inter> vars_term r = {})"

lemma subst_unification:
   assumes "vars_term s \<inter> vars_term t = {}"
   obtains \<mu> where "s \<cdot> \<sigma> = s \<cdot> \<mu>" "t \<cdot> \<tau> = t \<cdot> \<mu>"
   using assms
   by (auto intro!: that[of "\<lambda>x. if x \<in> vars_term s then \<sigma> x else \<tau> x"] simp: term_subst_eq_conv)

lemma lv_trs_subst_unification:
  assumes "lv_trs R" "(l, r) \<in> R" "s = l \<cdot> \<sigma>" "t = r \<cdot> \<tau>"
  obtains \<mu> where "s = l \<cdot> \<mu> \<and> t = r \<cdot> \<mu>"
  using assms subst_unification[of l r \<sigma> \<tau>]
  unfolding lv_trs_def
  by (force split!: prod.splits)

definition Rel\<^sub>f where
  "Rel\<^sub>f R = map_both term_to_bot_term |`| R"

definition root_pair_automaton where
  "root_pair_automaton \<F> R = (pattern_automaton \<F> (fst |`| R),
     pattern_automaton \<F> (snd |`| R))"

definition agtt_grrstep where
  "agtt_grrstep \<R> \<F> = pair_at_to_agtt' (root_pair_automaton \<F> \<R>) (Rel\<^sub>f \<R>)"

lemma agtt_grrstep_eps_trancl [simp]:
  "(eps (fst (agtt_grrstep \<R> \<F>)))|\<^sup>+| = eps (fst (agtt_grrstep \<R> \<F>))"
  "(eps (snd (agtt_grrstep \<R> \<F>))) = {||}"
  by (auto simp add: agtt_grrstep_def pair_at_to_agtt'_def
     pair_at_to_agtt_def Let_def root_pair_automaton_def pattern_automaton_def
     fmap_states_ta_def intro!: frelcomp_empty_ftrancl_simp)

lemma root_pair_automaton_grrstep:
  fixes R :: "('f, 'v) rule fset"
  assumes "lv_trs (fset R)" "ffunas_trs R |\<subseteq>| \<F>"
  shows "pair_at_lang (root_pair_automaton \<F> R) (Rel\<^sub>f R) = Restr (grrstep (fset R)) (\<T>\<^sub>G (fset \<F>))" (is "?Ls = ?Rs")
proof
  let ?t_o_g = "term_of_gterm :: 'f gterm \<Rightarrow> ('f, 'v) Term.term"
  have [simp]: "\<F> |\<union>| |\<Union>| ((ffunas_term \<circ> fst) |`| R) = \<F>"
    "\<F> |\<union>| |\<Union>| ((ffunas_term \<circ> snd) |`| R) = \<F>" using assms(2)
    by (force simp: less_eq_fset.rep_eq ffunas_trs.rep_eq funas_trs_def ffunas_term.rep_eq ffUnion.rep_eq)+
  {fix s t assume "(s, t) \<in> ?Ls"
    from pair_at_langE[OF this] obtain p q where st: "(q, p) |\<in>| Rel\<^sub>f R"
      "q |\<in>| gta_der (fst (root_pair_automaton \<F> R)) s" "p |\<in>| gta_der (snd (root_pair_automaton \<F> R)) t"
      by blast
    from st(1) obtain l r where tm: "q = l\<^sup>\<bottom>" "p = r\<^sup>\<bottom>" "(l, r) |\<in>| R" unfolding Rel\<^sub>f_def
      using assms(1) by auto
    have sm: "l\<^sup>\<bottom> \<le>\<^sub>b (?t_o_g s)\<^sup>\<bottom>" "r\<^sup>\<bottom> \<le>\<^sub>b (?t_o_g t)\<^sup>\<bottom>"
      using pattern_automaton_reach_smallet_term[of l \<F> "fst |`| R" "term_of_gterm s"]
      using pattern_automaton_reach_smallet_term[of r \<F> "snd |`| R" "term_of_gterm t"]
      using st(2, 3) tm(3) unfolding tm
      by (auto simp: gta_der_def root_pair_automaton_def) (smt bot_term_of_gterm_conv)+
    have "linear_term l" "linear_term r" using tm(3) assms(1)
      by (auto simp: lv_trs_def)
    then obtain \<sigma> \<tau> where "l \<cdot> \<sigma> = ?t_o_g s" "r \<cdot> \<tau> = ?t_o_g t" using sm
      by (auto dest!: bless_eq_to_instance)
    then obtain \<mu> where subst: "l \<cdot> \<mu> = ?t_o_g s" "r \<cdot> \<mu> = ?t_o_g t"
      using lv_trs_subst_unification[OF assms(1) tm(3), of "?t_o_g s" \<sigma> "?t_o_g t" \<tau>]
      by metis
    moreover have "s \<in> \<T>\<^sub>G (fset \<F>)" "t \<in> \<T>\<^sub>G (fset \<F>)" using st(2-) assms
      using ta_der_gterm_sig[of q "pattern_automaton \<F> (fst |`| R)" s]
      using ta_der_gterm_sig[of p "pattern_automaton \<F> (snd |`| R)" t]
      by (auto simp: gta_der_def root_pair_automaton_def \<T>\<^sub>G_equivalent_def less_eq_fset.rep_eq ffunas_gterm.rep_eq)
    ultimately have "(s, t) \<in> ?Rs" using tm(3)
      by (auto simp: grrstep_def rrstep_def') metis}
  then show "?Ls \<subseteq> ?Rs" by auto
next
  let ?t_o_g = "term_of_gterm :: 'f gterm \<Rightarrow> ('f, 'v) Term.term"
  {fix s t assume "(s, t) \<in> ?Rs"
    then obtain \<sigma> l r where st: "(l, r) |\<in>| R" "l \<cdot> \<sigma> = ?t_o_g s" "r \<cdot> \<sigma> = ?t_o_g t" "s \<in> \<T>\<^sub>G (fset \<F>)" "t \<in> \<T>\<^sub>G (fset \<F>)"
      by (auto simp: grrstep_def rrstep_def')
    have funas: "ffunas_gterm s |\<subseteq>| \<F>" "ffunas_gterm t |\<subseteq>| \<F>" using st(4, 5)
      by (auto simp: \<T>\<^sub>G_equivalent_def)
         (metis ffunas_gterm.rep_eq subsetD)+
    from st(1) have "(l\<^sup>\<bottom>, r\<^sup>\<bottom>) |\<in>| Rel\<^sub>f R" unfolding Rel\<^sub>f_def using assms(1)
      by (auto simp: fimage_iff fBex_def)
    then have "(s, t) \<in> ?Ls" using st
      using pattern_automaton_ground_instance_reach[of l "fst |`| R" \<sigma>, OF _ _ funas(1)]
      using pattern_automaton_ground_instance_reach[of r "snd |`| R" \<sigma>, OF _ _ funas(2)]
      by (auto simp: \<T>\<^sub>G_equivalent_def image_iff Bex_def root_pair_automaton_def gta_der_def pair_at_lang_def)}
  then show "?Rs \<subseteq> ?Ls" by auto
qed


lemma agtt_grrstep:
  fixes R :: "('f, 'v) rule fset"
  assumes "lv_trs (fset R)" "ffunas_trs R |\<subseteq>| \<F>"
  shows "agtt_lang (agtt_grrstep R \<F>) = Restr (grrstep (fset R)) (\<T>\<^sub>G (fset \<F>))"
  using root_pair_automaton_grrstep[OF assms] unfolding pair_at_agtt_cost agtt_grrstep_def
  by simp

(* Results for set as input *)
lemma root_pair_automaton_grrstep_set:
  fixes R :: "('f, 'v) rule set"
  assumes "finite R" "finite \<F>" "lv_trs R" "funas_trs R \<subseteq> \<F>"
  shows "pair_at_lang (root_pair_automaton (Abs_fset \<F>) (Abs_fset R)) (Rel\<^sub>f (Abs_fset R)) = Restr (grrstep R) (\<T>\<^sub>G \<F>)"
proof -
  from assms(1, 2, 4) have "ffunas_trs (Abs_fset R) |\<subseteq>| Abs_fset \<F>"
    by (auto simp add: Abs_fset_inverse ffunas_trs.rep_eq subset_eq)
  from root_pair_automaton_grrstep[OF _ this] assms
  show ?thesis
    by (auto simp: Abs_fset_inverse)
qed

lemma agtt_grrstep_set:
  fixes R :: "('f, 'v) rule set"
  assumes "finite R" "finite \<F>" "lv_trs R" "funas_trs R \<subseteq> \<F>"
  shows "agtt_lang (agtt_grrstep (Abs_fset R) (Abs_fset \<F>)) = Restr (grrstep R) (\<T>\<^sub>G \<F>)"
  using root_pair_automaton_grrstep_set[OF assms] unfolding pair_at_agtt_cost agtt_grrstep_def
  by simp

end
