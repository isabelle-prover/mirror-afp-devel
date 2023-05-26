theory Tree_Automata_Abstract_Impl
  imports Tree_Automata_Det Horn_Fset
begin

section \<open>Computing state derivation\<close>

lemma ta_der_Var_code [code]:
  "ta_der \<A> (Var q) = finsert q ((eps \<A>)|\<^sup>+| |``| {|q|})"
  by (auto)

lemma ta_der_Fun_code [code]:
  "ta_der \<A> (Fun f ts) =
     (let args = map (ta_der \<A>) ts in
      let P = (\<lambda> r. case r of TA_rule g ps p \<Rightarrow> f = g \<and> list_all2 fmember ps args) in
      let S = r_rhs |`| ffilter P (rules \<A>) in
         S |\<union>| (eps \<A>)|\<^sup>+| |``| S)" (is "?Ls = ?Rs")
proof
  {fix q assume "q |\<in>| ?Ls" then have "q |\<in>| ?Rs"
      apply (simp add: Let_def fImage_iff fBex_def image_iff)
      by (smt (verit, ccfv_threshold) IntI length_map list_all2_conv_all_nth mem_Collect_eq nth_map
          ta_rule.case ta_rule.sel(3))
    }
  then show "?Ls |\<subseteq>| ?Rs" by blast
next
  {fix q assume "q |\<in>| ?Rs" then have "q |\<in>| ?Ls"
      apply (auto simp: Let_def ffmember_filter fimage_iff fBex_def list_all2_conv_all_nth fImage_iff
                  split!: ta_rule.splits)
      apply (metis ta_rule.collapse)
      apply blast
      done}
  then show "?Rs |\<subseteq>| ?Ls" by blast
qed

definition eps_free_automata where
  "eps_free_automata epscl \<A> =
  (let ruleps = (\<lambda> r. finsert (r_rhs r) (epscl |``| {|r_rhs r|})) in
   let rules = (\<lambda> r. (\<lambda> q. TA_rule (r_root r) (r_lhs_states r) q) |`| (ruleps r)) |`| (rules \<A>) in
   TA ( |\<Union>| rules) {||})"

lemma eps_free [code]:
  "eps_free \<A> = eps_free_automata ((eps \<A>)|\<^sup>+|) \<A>"
  apply (intro TA_equalityI)
   apply (auto simp: eps_free_def eps_free_rulep_def eps_free_automata_def)
  using fBex_def apply fastforce
  apply (metis ta_rule.exhaust_sel)+
  done


lemma eps_of_eps_free_automata [simp]:
  "eps (eps_free_automata S \<A>) = {||}"
  by (auto simp add: eps_free_automata_def)

lemma eps_free_automata_empty [simp]:
  "eps \<A> = {||} \<Longrightarrow> eps_free_automata {||} \<A> = \<A>"
  by (auto simp add: eps_free_automata_def intro!: TA_equalityI)

section \<open>Computing the restriction of tree automata to state set\<close>

lemma ta_restrict [code]:
  "ta_restrict \<A> Q =
     (let rules =  ffilter (\<lambda> r. case r of TA_rule f ps p \<Rightarrow> fset_of_list ps |\<subseteq>| Q \<and> p |\<in>| Q) (rules \<A>) in
      let eps = ffilter (\<lambda> r. case r of (p, q) \<Rightarrow> p |\<in>| Q \<and> q |\<in>| Q) (eps \<A>) in
      TA rules eps)"
  by (auto simp: Let_def ta_restrict_def split!: ta_rule.splits intro: finite_subset[OF _ finite_Collect_ta_rule])


section \<open>Computing the epsilon transition for the product automaton\<close>

lemma prod_eps[code_unfold]:
  "fCollect (prod_epsLp \<A> \<B>) = (\<lambda> ((p, q), r). ((p, r), (q, r))) |`| (eps \<A> |\<times>| \<Q> \<B>)"
  "fCollect (prod_epsRp \<A> \<B>) = (\<lambda> ((p, q), r). ((r, p), (r, q))) |`| (eps \<B> |\<times>| \<Q> \<A>)"
  by (auto simp: finite_prod_epsLp prod_epsLp_def finite_prod_epsRp prod_epsRp_def image_iff
      fSigma.rep_eq) force+

section \<open>Computing reachability\<close>

inductive_set ta_reach for \<A> where
   rule [intro]: "f qs \<rightarrow> q |\<in>| rules \<A> \<Longrightarrow> \<forall> i < length qs. qs ! i \<in> ta_reach \<A> \<Longrightarrow> q \<in> ta_reach \<A>"
 |  eps [intro]: "q \<in> ta_reach \<A> \<Longrightarrow> (q, r) |\<in>| eps \<A> \<Longrightarrow> r \<in> ta_reach \<A>"


lemma ta_reach_eps_transI:
  assumes "(p, q) |\<in>| (eps \<A>)|\<^sup>+|" "p \<in> ta_reach \<A>"
  shows "q \<in> ta_reach \<A>" using assms
  by (induct rule: ftrancl_induct) auto

lemma ta_reach_ground_term_der:
  assumes "q \<in> ta_reach \<A>"
  shows "\<exists> t. ground t \<and> q |\<in>| ta_der \<A> t" using assms
proof (induct)
  case (rule f qs q)
  then obtain ts where "length ts = length qs"
    "\<forall> i < length qs. ground (ts ! i)"
    "\<forall> i < length qs. qs ! i |\<in>| ta_der \<A> (ts ! i)"
    using Ex_list_of_length_P[of "length qs" "\<lambda> t i. ground t \<and> qs ! i |\<in>| ta_der \<A> t"]
    by auto
  then show ?case using rule(1)
    by (auto dest!: in_set_idx intro!: exI[of _ "Fun f ts"]) blast
qed (auto, meson ta_der_eps)

lemma ground_term_der_ta_reach:
  assumes "ground t" "q |\<in>| ta_der \<A> t"
  shows "q \<in> ta_reach \<A>" using assms(2, 1)
  by (induct rule: ta_der_induct) (auto simp add: rule ta_reach_eps_transI)

lemma ta_reach_reachable:
  "ta_reach \<A> = fset (ta_reachable \<A>)"
  using ta_reach_ground_term_der[of _ \<A>]
  using ground_term_der_ta_reach[of _ _ \<A>]
  unfolding ta_reachable_def
  by auto


subsection \<open>Horn setup for reachable states\<close>
definition "reach_rules \<A> =
  {qs \<rightarrow>\<^sub>h q | f qs q. TA_rule f qs q |\<in>| rules \<A>} \<union>
  {[q] \<rightarrow>\<^sub>h r | q r. (q, r) |\<in>| eps \<A>}"

locale reach_horn =
  fixes \<A> :: "('q, 'f) ta"
begin

sublocale horn "reach_rules \<A>" .

lemma reach_infer0: "infer0 = {q | f q. TA_rule f [] q |\<in>| rules \<A>}"
  by (auto simp: horn.infer0_def reach_rules_def)

lemma reach_infer1:
  "infer1 p X = {r | f qs r. TA_rule f qs r |\<in>| rules \<A> \<and> p \<in> set qs \<and> set qs \<subseteq> insert p X} \<union>
   {r | r. (p, r) |\<in>| eps \<A>}"
  unfolding reach_rules_def
  by (auto simp: horn.infer1_def simp flip: ex_simps(1))

lemma reach_sound:
  "ta_reach \<A> = saturate"
proof (intro set_eqI iffI, goal_cases lr rl)
  case (lr x) obtain p where x: "p = ta_reach \<A>" by auto
  show ?case using lr unfolding x
  proof (induct)
    case (rule f qs q)
    then show ?case
      by (intro infer[of qs q]) (auto simp: reach_rules_def dest: in_set_idx)
  next
    case (eps q r)
    then show ?case
      by (intro infer[of "[q]" r]) (auto simp: reach_rules_def)
  qed
next
  case (rl x)
  then show ?case
    by (induct) (auto simp: reach_rules_def)
qed
end

subsection \<open>Computing productivity\<close>

text \<open>First, use an alternative definition of productivity\<close>

inductive_set ta_productive_ind :: "'q fset \<Rightarrow> ('q,'f) ta \<Rightarrow> 'q set" for P and \<A> :: "('q,'f) ta" where
  basic [intro]: "q |\<in>| P \<Longrightarrow> q \<in> ta_productive_ind P \<A>"
| eps [intro]: "(p, q) |\<in>| (eps \<A>)|\<^sup>+| \<Longrightarrow> q \<in> ta_productive_ind P \<A> \<Longrightarrow> p \<in> ta_productive_ind P \<A>"
| rule: "TA_rule f qs q |\<in>| rules \<A> \<Longrightarrow> q \<in> ta_productive_ind P \<A> \<Longrightarrow> q' \<in> set qs \<Longrightarrow> q' \<in> ta_productive_ind P \<A>"

lemma ta_productive_ind:
  "ta_productive_ind P \<A> = fset (ta_productive P \<A>)" (is "?LS = ?RS")
proof -
  {fix q assume "q \<in> ?LS" then have "q \<in> ?RS"
      by (induct) (auto dest: ta_prod_epsD intro: ta_productive_setI,
         metis (full_types) in_set_conv_nth rule_reachable_ctxt_exist ta_productiveI')}
  moreover
  {fix q assume "q \<in> ?RS" note * = this
    from ta_productiveE[OF *] obtain r C where
      reach : "r |\<in>| ta_der \<A> C\<langle>Var q\<rangle>" and f: "r |\<in>| P" by auto
    from f have "r \<in> ta_productive_ind P \<A>" "r |\<in>| ta_productive P \<A>"
      by (auto intro: ta_productive_setI)
    then have "q \<in> ?LS" using reach
    proof (induct C arbitrary: q r)
      case (More f ss C ts)
      from iffD1 ta_der_Fun[THEN iffD1, OF More(4)[unfolded ctxt_apply_term.simps]] obtain ps p where
        inv: "f ps \<rightarrow> p |\<in>| rules \<A>" "p = r \<or> (p, r) |\<in>| (eps \<A>)|\<^sup>+|" "length ps = length (ss @ C\<langle>Var q\<rangle> # ts)"
             "ps ! length ss |\<in>| ta_der \<A> C\<langle>Var q\<rangle>"
        by (auto simp: nth_append_Cons split: if_splits)
      then have "p \<in> ta_productive_ind P \<A> \<Longrightarrow> p |\<in>| ta_der \<A> C\<langle>Var q\<rangle> \<Longrightarrow> q \<in> ta_productive_ind P \<A>" for p
        using More(1) calculation by auto
      note [intro!] = this[of "ps ! length ss"]
      show ?case using More(2) inv
        by (auto simp: nth_append_Cons ta_productive_ind.rule)
           (metis less_add_Suc1 nth_mem ta_productive_ind.simps)
    qed (auto intro: ta_productive_setI)
  }
  ultimately show ?thesis by auto
qed


subsubsection \<open>Horn setup for productive states\<close>

definition "productive_rules P \<A> = {[] \<rightarrow>\<^sub>h q | q. q |\<in>| P} \<union>
  {[r] \<rightarrow>\<^sub>h q | q r. (q, r) |\<in>| eps \<A>} \<union>
  {[q] \<rightarrow>\<^sub>h r | f qs q r. TA_rule f qs q |\<in>| rules \<A> \<and> r \<in> set qs}"

locale productive_horn =
  fixes \<A> :: "('q, 'f) ta" and P :: "'q fset"
begin

sublocale horn "productive_rules P \<A>" .

lemma productive_infer0: "infer0 = fset P"
  by (auto simp: productive_rules_def horn.infer0_def)

lemma productive_infer1:
  "infer1 p X = {r | r. (r, p) |\<in>| eps \<A>} \<union>
    {r | f qs r. TA_rule f qs p |\<in>| rules \<A> \<and> r \<in> set qs}"
  unfolding productive_rules_def horn_infer1_union
  by (auto simp add: horn.infer1_def)
     (metis insertCI list.set(1) list.simps(15) singletonD subsetI)

lemma productive_sound:
  "ta_productive_ind P \<A> = saturate"
proof (intro set_eqI iffI, goal_cases lr rl)
  case (lr p) then show ?case using lr
  proof (induct)
    case (basic q)
    then show ?case
      by (intro infer[of "[]" q]) (auto simp: productive_rules_def)
  next
    case (eps p q) then show ?case
    proof (induct rule: ftrancl_induct)
      case (Base p q)
      then show ?case using infer[of "[q]" p]
        by (auto simp: productive_rules_def)
    next
      case (Step p q r)
      then show ?case using infer[of "[r]" q]
        by (auto simp: productive_rules_def)
    qed
  next
    case (rule f qs q p)
    then show ?case
      by (intro infer[of "[q]" p]) (auto simp: productive_rules_def)
  qed
next
  case (rl p)
  then show ?case
    by (induct) (auto simp: productive_rules_def ta_productive_ind.rule)
qed
end

subsection \<open>Horn setup for power set construction states\<close>

lemma prod_list_exists:
  assumes "fst p \<in> set qs" "set qs \<subseteq> insert (fst p) (fst ` X)"
  obtains as where "p \<in> set as" "map fst as = qs" "set as \<subseteq> insert p X"
proof -
  from assms have "qs \<in> lists (fst ` (insert p X))" by blast
  then obtain ts where ts: "map fst ts = qs" "ts \<in> lists (insert p X)"
    by (metis image_iff lists_image)
  then obtain i where mem: "i < length qs" "qs ! i = fst p" using assms(1)
    by (metis in_set_idx)
  from ts have p: "ts[i := p] \<in> lists (insert p X)"
    using set_update_subset_insert by fastforce
  then have "p \<in> set (ts[i := p])" "map fst (ts[i := p]) = qs" "set (ts[i := p]) \<subseteq> insert p X"
    using mem ts(1)
    by (auto simp add: nth_list_update set_update_memI intro!: nth_equalityI)
  then show ?thesis using that
    by blast
qed

definition "ps_states_rules \<A> = {rs \<rightarrow>\<^sub>h (Wrapp q) | rs f q.
    q = ps_reachable_states \<A> f (map ex rs) \<and> q \<noteq> {||}}"

locale ps_states_horn =
  fixes \<A> :: "('q, 'f) ta"
begin

sublocale horn "ps_states_rules \<A>" .

lemma ps_construction_infer0: "infer0 =
  {Wrapp q | f q. q = ps_reachable_states \<A> f [] \<and> q \<noteq> {||}}"
    by (auto simp: ps_states_rules_def horn.infer0_def)

lemma ps_construction_infer1:
  "infer1 p X = {Wrapp q | f qs q. q = ps_reachable_states \<A> f (map ex qs) \<and> q \<noteq> {||} \<and>
   p \<in> set qs \<and> set qs \<subseteq> insert p X}"
  unfolding ps_states_rules_def horn_infer1_union
  by (auto simp add: horn.infer1_def ps_reachable_states_def comp_def elim!: prod_list_exists) 

lemma ps_states_sound:
  "ps_states_set \<A> = saturate"
proof (intro set_eqI iffI, goal_cases lr rl)
  case (lr p) then show ?case using lr
  proof (induct)
    case (1 ps f)
    then have "ps \<rightarrow>\<^sub>h (Wrapp (ps_reachable_states \<A> f (map ex ps))) \<in> ps_states_rules \<A>"
      by (auto simp: ps_states_rules_def)
    then show ?case using horn.saturate.simps 1
      by fastforce
  qed
next
  case (rl p)
  then obtain q where "q \<in> saturate" "q = p" by blast
  then show ?case
    by (induct arbitrary: p)
       (auto simp: ps_states_rules_def intro!: ps_states_set.intros)
qed

end

definition ps_reachable_states_cont where
  "ps_reachable_states_cont \<Delta> \<Delta>\<^sub>\<epsilon> f ps =
   (let R = ffilter (\<lambda> r. case r of TA_rule g qs q \<Rightarrow> f = g \<and> list_all2 (|\<in>|) qs ps) \<Delta> in
    let S = r_rhs |`| R in
    S |\<union>| \<Delta>\<^sub>\<epsilon>|\<^sup>+| |``| S)"

lemma ps_reachable_states [code]:
  "ps_reachable_states (TA \<Delta> \<Delta>\<^sub>\<epsilon>) f ps = ps_reachable_states_cont \<Delta> \<Delta>\<^sub>\<epsilon> f ps"
  by (auto simp: ps_reachable_states_fmember ps_reachable_states_cont_def Let_def fimage_iff fBex_def
           split!: ta_rule.splits) force+

definition ps_rules_cont where
 "ps_rules_cont \<A> Q =
   (let sig = ta_sig \<A> in
    let qss = (\<lambda> (f, n). (f, n, fset_of_list (List.n_lists n (sorted_list_of_fset Q)))) |`| sig in
    let res = (\<lambda> (f, n, Qs). (\<lambda> qs. TA_rule f qs (Wrapp (ps_reachable_states \<A> f (map ex qs)))) |`| Qs) |`| qss in
      ffilter (\<lambda> r. ex (r_rhs r) \<noteq> {||}) ( |\<Union>| res))"

lemma ps_rules [code]:
  "ps_rules \<A> Q = ps_rules_cont \<A> Q"
  using ps_reachable_states_sig finite_ps_rulesp_unfolded[of Q \<A>]
  unfolding ps_rules_cont_def
  apply (auto simp: fset_of_list_elem ps_rules_def fin_mono ps_rulesp_def
    image_iff set_n_lists split!: prod.splits dest!: in_set_idx)
  by fastforce+

end