theory GTT_Transitive_Closure
  imports GTT_Compose
begin

subsection \<open>GTT closure under transitivity\<close>

inductive_set \<Delta>_trancl_set :: "('q, 'f) ta \<Rightarrow> ('q, 'f) ta \<Rightarrow> ('q \<times> 'q) set" for A B where
  \<Delta>_set_cong: "TA_rule f ps p |\<in>| rules A \<Longrightarrow> TA_rule f qs q |\<in>| rules B \<Longrightarrow> length ps = length qs \<Longrightarrow>
   (\<And>i. i < length qs \<Longrightarrow> (ps ! i, qs ! i) \<in> \<Delta>_trancl_set A B) \<Longrightarrow> (p, q) \<in> \<Delta>_trancl_set A B"
| \<Delta>_set_eps1: "(p, p') |\<in>| eps A \<Longrightarrow> (p, q) \<in> \<Delta>_trancl_set A B \<Longrightarrow> (p', q) \<in> \<Delta>_trancl_set A B"
| \<Delta>_set_eps2: "(q, q') |\<in>| eps B \<Longrightarrow> (p, q) \<in> \<Delta>_trancl_set A B \<Longrightarrow> (p, q') \<in> \<Delta>_trancl_set A B"
| \<Delta>_set_trans: "(p, q) \<in> \<Delta>_trancl_set A B \<Longrightarrow> (q, r) \<in> \<Delta>_trancl_set A B \<Longrightarrow> (p, r) \<in> \<Delta>_trancl_set A B"

lemma \<Delta>_trancl_set_states: "\<Delta>_trancl_set \<A> \<B> \<subseteq> fset (\<Q> \<A> |\<times>| \<Q> \<B>)"
proof -
  {fix p q assume "(p, q) \<in> \<Delta>_trancl_set \<A> \<B>" then have "(p, q) \<in> fset (\<Q> \<A> |\<times>| \<Q> \<B>)"
      by (induct) (auto dest: rule_statesD eps_statesD)}
  then show ?thesis by auto
qed

lemma finite_\<Delta>_trancl_set [simp]: "finite (\<Delta>_trancl_set \<A> \<B>)"
  using finite_subset[OF \<Delta>_trancl_set_states]
  by simp

context
includes fset.lifting
begin
lift_definition \<Delta>_trancl :: "('q, 'f) ta \<Rightarrow> ('q, 'f) ta \<Rightarrow> ('q \<times> 'q) fset" is \<Delta>_trancl_set by simp
lemmas \<Delta>_trancl_cong = \<Delta>_set_cong [Transfer.transferred]
lemmas \<Delta>_trancl_eps1 = \<Delta>_set_eps1 [Transfer.transferred]
lemmas \<Delta>_trancl_eps2 = \<Delta>_set_eps2 [Transfer.transferred]
lemmas \<Delta>_trancl_cases = \<Delta>_trancl_set.cases[Transfer.transferred]
lemmas \<Delta>_trancl_induct [consumes 1, case_names \<Delta>_cong \<Delta>_eps1 \<Delta>_eps2 \<Delta>_trans] = \<Delta>_trancl_set.induct[Transfer.transferred]
lemmas \<Delta>_trancl_intros = \<Delta>_trancl_set.intros[Transfer.transferred]
lemmas \<Delta>_trancl_simps = \<Delta>_trancl_set.simps[Transfer.transferred]
end


lemma \<Delta>_trancl_cl [simp]:
  "(\<Delta>_trancl A B)|\<^sup>+| = \<Delta>_trancl A B"
proof -
  {fix s t assume "(s, t) |\<in>| (\<Delta>_trancl A B)|\<^sup>+|" then have "(s, t) |\<in>| \<Delta>_trancl A B"
      by (induct rule: ftrancl_induct) (auto intro: \<Delta>_trancl_intros)}
  then show ?thesis by auto
qed

lemma \<Delta>_trancl_states: "\<Delta>_trancl \<A> \<B> |\<subseteq>| (\<Q> \<A> |\<times>| \<Q> \<B>)"
  using \<Delta>_trancl_set_states
  by (metis \<Delta>_trancl.rep_eq fSigma_cong less_eq_fset.rep_eq)

definition GTT_trancl where
  "GTT_trancl G =
    (let \<Delta> = \<Delta>_trancl (snd G) (fst G) in
    (TA (rules (fst G)) (eps (fst G) |\<union>| \<Delta>),
                   TA (rules (snd G)) (eps (snd G) |\<union>| (\<Delta>|\<inverse>|))))"

lemma \<Delta>_trancl_inv:
  "(\<Delta>_trancl A B)|\<inverse>| = \<Delta>_trancl B A"
proof -
  have [dest]: "(p, q) |\<in>| \<Delta>_trancl A B \<Longrightarrow> (q, p) |\<in>| \<Delta>_trancl B A" for p q A B
    by (induct rule: \<Delta>_trancl_induct) (auto intro: \<Delta>_trancl_intros)
  show ?thesis by auto
qed

lemma gtt_states_GTT_trancl:
  "gtt_states (GTT_trancl G) |\<subseteq>| gtt_states G"
  unfolding GTT_trancl_def
  by (auto simp: gtt_states_def \<Q>_def \<Delta>_trancl_inv dest!: fsubsetD[OF \<Delta>_trancl_states])

lemma gtt_syms_GTT_trancl:
  "gtt_syms (GTT_trancl G) = gtt_syms G"
  by (auto simp: GTT_trancl_def ta_sig_def \<Delta>_trancl_inv)

lemma GTT_trancl_base:
  "gtt_lang G \<subseteq> gtt_lang (GTT_trancl G)"
  using gtt_lang_mono[of G "GTT_trancl G"] by (auto simp: \<Delta>_trancl_inv GTT_trancl_def)

lemma GTT_trancl_trans:
  "gtt_lang (GTT_comp (GTT_trancl G) (GTT_trancl G)) \<subseteq> gtt_lang (GTT_trancl G)"
proof -
  have [dest]: "(p, q) |\<in>| \<Delta>\<^sub>\<epsilon> (TA (rules A) (eps A |\<union>| (\<Delta>_trancl B A)))
    (TA (rules B) (eps B |\<union>| (\<Delta>_trancl A B))) \<Longrightarrow> (p, q) |\<in>| \<Delta>_trancl A B" for p q A B
    by (induct rule: \<Delta>\<^sub>\<epsilon>_induct) (auto intro: \<Delta>_trancl_intros simp: \<Delta>_trancl_inv[of B A, symmetric])
  show ?thesis
    by (intro gtt_lang_mono[of "GTT_comp (GTT_trancl G) (GTT_trancl G)" "GTT_trancl G"])
       (auto simp: GTT_comp_def GTT_trancl_def \<Delta>_trancl_inv)
qed

lemma agtt_lang_base:
  "agtt_lang G \<subseteq> agtt_lang (GTT_trancl G)"
  by (rule agtt_lang_mono) (auto simp: GTT_trancl_def \<Delta>_trancl_inv)


lemma \<Delta>\<^sub>\<epsilon>_tr_incl:
  "\<Delta>\<^sub>\<epsilon> (TA (rules A) (eps A |\<union>| \<Delta>_trancl B A)) (TA (rules B)  (eps B |\<union>| \<Delta>_trancl A B)) = \<Delta>_trancl A B"
   (is "?LS = ?RS")
proof -
  {fix p q assume "(p, q) |\<in>| ?LS" then have "(p, q) |\<in>| ?RS"
      by (induct rule: \<Delta>\<^sub>\<epsilon>_induct)
         (auto simp: \<Delta>_trancl_inv[of B A, symmetric] intro: \<Delta>_trancl_intros)}
  moreover
  {fix p q assume "(p, q) |\<in>| ?RS" then have "(p, q) |\<in>| ?LS"
      by (induct rule: \<Delta>_trancl_induct)
        (auto simp: \<Delta>_trancl_inv[of B A, symmetric] intro: \<Delta>\<^sub>\<epsilon>_intros)}
  ultimately show ?thesis
    by auto
qed


lemma agtt_lang_trans:
  "gcomp_rel UNIV (agtt_lang (GTT_trancl G)) (agtt_lang (GTT_trancl G)) \<subseteq> agtt_lang (GTT_trancl G)"
proof -
  have [intro!, dest]: "(p, q) |\<in>| \<Delta>\<^sub>\<epsilon> (TA (rules A) (eps A |\<union>| (\<Delta>_trancl B A)))
    (TA (rules B) (eps B |\<union>| (\<Delta>_trancl A B))) \<Longrightarrow> (p, q) |\<in>| \<Delta>_trancl A B" for p q A B
    by (induct rule: \<Delta>\<^sub>\<epsilon>_induct) (auto intro: \<Delta>_trancl_intros simp: \<Delta>_trancl_inv[of B A, symmetric])
  show ?thesis
    by (rule subset_trans[OF gtt_comp_acomplete agtt_lang_mono])
       (auto simp: GTT_comp_def GTT_trancl_def \<Delta>_trancl_inv)
qed

lemma GTT_trancl_acomplete:
  "gtrancl_rel UNIV (agtt_lang G) \<subseteq> agtt_lang (GTT_trancl G)"
  unfolding gtrancl_rel_def
  using agtt_lang_base[of G] gmctxt_cl_mono_rel[OF agtt_lang_base[of G], of UNIV]
  using agtt_lang_trans[of G]
  unfolding gcomp_rel_def
  by (intro kleene_trancl_induct) blast+

lemma Restr_rtrancl_gtt_lang_eq_trancl_gtt_lang:
  "(gtt_lang G)\<^sup>* = (gtt_lang G)\<^sup>+"
  by (auto simp: rtrancl_trancl_reflcl simp del: reflcl_trancl dest: tranclD tranclD2 intro: gmctxt_cl_refl)

lemma GTT_trancl_complete:
  "(gtt_lang G)\<^sup>+ \<subseteq> gtt_lang (GTT_trancl G)"
  using GTT_trancl_base subset_trans[OF gtt_comp_lang_complete GTT_trancl_trans]
  by (metis trancl_id trancl_mono_set trans_O_iff)

lemma trancl_gtt_lang_arg_closed:
  assumes "length ss = length ts" "\<forall>i < length ts. (ss ! i, ts ! i) \<in> (gtt_lang \<G>)\<^sup>+"
  shows "(GFun f ss, GFun f ts) \<in> (gtt_lang \<G>)\<^sup>+" (is "?e \<in> _")
proof -
  have "all_ctxt_closed UNIV ((gtt_lang \<G>)\<^sup>+)" by (intro all_ctxt_closed_trancl) auto
  from all_ctxt_closedD[OF this _ assms] show ?thesis
    by auto
qed

lemma \<Delta>_trancl_sound:
  assumes "(p, q) |\<in>| \<Delta>_trancl A B"
  obtains s t where "(s, t) \<in> (gtt_lang (B, A))\<^sup>+" "p |\<in>| gta_der A s" "q |\<in>| gta_der B t"
  using assms
proof (induct arbitrary: thesis rule: \<Delta>_trancl_induct)
  case (\<Delta>_cong f ps p qs q)
  have "\<exists>si ti. (si, ti) \<in> (gtt_lang (B, A))\<^sup>+ \<and> ps ! i |\<in>| gta_der A (si) \<and>
      qs ! i |\<in>| gta_der B (ti)" if "i < length qs" for i
    using \<Delta>_cong(5)[OF that] by metis
  then obtain ss ts where
    "\<And>i. i < length qs \<Longrightarrow> (ss i, ts i) \<in> (gtt_lang (B, A))\<^sup>+ \<and> ps ! i |\<in>| gta_der A (ss i) \<and> qs ! i |\<in>| gta_der B (ts i)" by metis
  then show ?case using \<Delta>_cong(1-5)
    by (intro \<Delta>_cong(6)[of "GFun f (map ss [0..<length ps])" "GFun f (map ts [0..<length qs])"])
       (auto simp: gta_der_def intro!: trancl_gtt_lang_arg_closed)
next
  case (\<Delta>_eps1 p p' q) then show ?case
    by (metis gta_der_def ta_der_eps)
next
  case (\<Delta>_eps2 q q' p) then show ?case
    by (metis gta_der_def ta_der_eps)
next
  case (\<Delta>_trans p q r)
  obtain s1 t1 where "(s1, t1) \<in> (gtt_lang (B, A))\<^sup>+" "p |\<in>| gta_der A s1" "q |\<in>| gta_der B t1"
    using \<Delta>_trans(2) .note 1 = this
  obtain s2 t2 where "(s2, t2) \<in> (gtt_lang (B, A))\<^sup>+" "q |\<in>| gta_der A s2" "r |\<in>| gta_der B t2"
    using \<Delta>_trans(4) . note 2 = this
  have "(t1, s2) \<in> gtt_lang (B, A)" using 1(1,3) 2(1,2)
    by (auto simp: Restr_rtrancl_gtt_lang_eq_trancl_gtt_lang[symmetric] gtt_lang_join)
  then have "(s1, t2) \<in> (gtt_lang (B, A))\<^sup>+" using 1(1) 2(1)
    by (meson trancl.trancl_into_trancl trancl_trans)
  then show ?case using 1(2) 2(3) by (auto intro: \<Delta>_trans(5)[of s1 t2])
qed

lemma GTT_trancl_sound_aux:
  assumes "p |\<in>| gta_der (TA (rules A) (eps A |\<union>| (\<Delta>_trancl B A))) s"
  shows "\<exists>t. (s, t) \<in> (gtt_lang (A, B))\<^sup>+ \<and> p |\<in>| gta_der A t"
  using assms
proof (induct s arbitrary: p)
  case (GFun f ss)
  let ?eps = "eps A |\<union>| \<Delta>_trancl B A"
  obtain qs q where q: "TA_rule f qs q |\<in>| rules A" "q = p \<or> (q, p) |\<in>| ?eps|\<^sup>+|" "length qs = length ss"
   "\<And>i. i < length ss \<Longrightarrow> qs ! i |\<in>| gta_der (TA (rules A) ?eps) (ss ! i)"
    using GFun(2) by (auto simp: gta_der_def)
  have "\<And>i. i < length ss \<Longrightarrow> \<exists>ti. (ss ! i, ti) \<in> (gtt_lang (A, B))\<^sup>+ \<and> qs ! i |\<in>| gta_der A (ti)"
    using GFun(1)[OF nth_mem q(4)] unfolding gta_der_def by fastforce
  then obtain ts where ts: "\<And>i. i < length ss \<Longrightarrow> (ss ! i, ts i) \<in> (gtt_lang (A, B))\<^sup>+ \<and> qs ! i |\<in>| gta_der A (ts i)"
    by metis
  then have q': "q |\<in>| gta_der A (GFun f (map ts [0..<length ss]))"
    "(GFun f ss, GFun f (map ts [0..<length ss])) \<in> (gtt_lang (A, B))\<^sup>+" using q(1, 3)
    by (auto simp: gta_der_def intro!: exI[of _ qs] exI[of _ q] trancl_gtt_lang_arg_closed)
  {fix p q u assume ass: "(p, q) |\<in>| \<Delta>_trancl B A" "(GFun f ss, u) \<in> (gtt_lang (A, B))\<^sup>+ \<and> p |\<in>| gta_der A u"
    from \<Delta>_trancl_sound[OF this(1)] obtain s t
      where "(s, t) \<in> (gtt_lang (A, B))\<^sup>+" "p |\<in>| gta_der B s" "q |\<in>| gta_der A t" . note st = this
    have "(u, s) \<in> gtt_lang (A, B)" using st conjunct2[OF ass(2)]
      by (auto simp: Restr_rtrancl_gtt_lang_eq_trancl_gtt_lang[symmetric] gtt_lang_join)
    then have "(GFun f ss, t) \<in> (gtt_lang (A, B))\<^sup>+"
      using ass st(1) by (meson trancl_into_trancl2 trancl_trans)
    then have "\<exists> s t. (GFun f ss, t) \<in> (gtt_lang (A, B))\<^sup>+ \<and> q |\<in>| gta_der A t" using st by blast}
  note trancl_step = this
  show ?case
  proof (cases "q = p")
    case True
    then show ?thesis using ts q(1, 3)
      by (auto simp: gta_der_def intro!: exI[of _"GFun f (map ts [0..< length ss])"] trancl_gtt_lang_arg_closed) blast
  next
    case False
    then have "(q, p) |\<in>| ?eps|\<^sup>+|" using q(2) by simp
    then show ?thesis using q(1) q'
    proof (induct rule: ftrancl_induct)
      case (Base q p) from Base(1) show ?case
      proof
        assume "(q, p) |\<in>| eps A" then show ?thesis using Base(2) ts q(3)
          by (auto simp: gta_der_def intro!: exI[of _"GFun f (map ts [0..< length ss])"]
                         trancl_gtt_lang_arg_closed exI[of _ qs] exI[of _ q])
      next
        assume "(q, p) |\<in>| (\<Delta>_trancl B A)"
        then have "(q, p) |\<in>| \<Delta>_trancl B A" by simp       
        from trancl_step[OF this] show ?thesis using Base(3, 4)
          by auto
      qed
    next
      case (Step p q r)
      from Step(2, 4-) obtain s' where s': "(GFun f ss, s') \<in> (gtt_lang (A, B))\<^sup>+ \<and> q |\<in>| gta_der A s'" by auto
      show ?case using Step(3)
      proof
        assume "(q, r) |\<in>| eps A" then show ?thesis using s'
          by (auto simp: gta_der_def ta_der_eps intro!: exI[of _ s'])
      next
        assume "(q, r) |\<in>| \<Delta>_trancl B A"
        then have "(q, r) |\<in>| \<Delta>_trancl B A" by simp       
        from trancl_step[OF this] show ?thesis using s' by auto
      qed
    qed
  qed
qed

lemma GTT_trancl_asound:
  "agtt_lang (GTT_trancl G) \<subseteq> gtrancl_rel UNIV (agtt_lang G)"
proof (intro subrelI, goal_cases LR)
  case (LR s t)
  then obtain s' q t' where *: "(s, s') \<in> (gtt_lang G)\<^sup>+"
    "q |\<in>| gta_der (fst G) s'" "q |\<in>| gta_der (snd G) t'" "(t', t) \<in> (gtt_lang G)\<^sup>+"
    by (auto simp: agtt_lang_def GTT_trancl_def trancl_converse \<Delta>_trancl_inv
      simp flip: gtt_lang_swap[of "fst G" "snd G", unfolded prod.collapse agtt_lang_def, simplified]
      dest!: GTT_trancl_sound_aux)
  then have "(s', t') \<in> agtt_lang G" using *(2,3)
    by (auto simp: agtt_lang_def)
  then show ?case using *(1,4) unfolding gtrancl_rel_def
    by auto
qed

lemma GTT_trancl_sound:
  "gtt_lang (GTT_trancl G) \<subseteq> (gtt_lang G)\<^sup>+"
proof -
  note [dest] = GTT_trancl_sound_aux
  have "gtt_accept (GTT_trancl G) s t \<Longrightarrow> (s, t) \<in> (gtt_lang G)\<^sup>+" for s t unfolding gtt_accept_def
  proof (induct rule: gmctxt_cl.induct)
    case (base s t)
    from base obtain q where join: "q |\<in>| gta_der (fst (GTT_trancl G)) s" "q |\<in>| gta_der (snd (GTT_trancl G)) t"
      by (auto simp: agtt_lang_def)
    obtain s' where "(s, s') \<in> (gtt_lang G)\<^sup>+" "q |\<in>| gta_der (fst G) s'" using base join
      by (auto simp: GTT_trancl_def \<Delta>_trancl_inv agtt_lang_def)
    moreover obtain t' where "(t', t) \<in> (gtt_lang G)\<^sup>+" "q |\<in>| gta_der (snd G) t'" using join
      by (auto simp: GTT_trancl_def gtt_lang_swap[of "fst G" "snd G", symmetric] trancl_converse \<Delta>_trancl_inv)
    moreover have "(s', t') \<in> gtt_lang G" using calculation
      by (auto simp: Restr_rtrancl_gtt_lang_eq_trancl_gtt_lang[symmetric] gtt_lang_join)
    ultimately show "(s, t) \<in> (gtt_lang G)\<^sup>+" by (meson trancl.trancl_into_trancl trancl_trans)
  qed (auto intro!: trancl_gtt_lang_arg_closed)
  then show ?thesis by (auto simp: gtt_accept_def)
qed

lemma GTT_trancl_alang:
  "agtt_lang (GTT_trancl G) = gtrancl_rel UNIV (agtt_lang G)"
  using GTT_trancl_asound GTT_trancl_acomplete by blast

lemma GTT_trancl_lang:
  "gtt_lang (GTT_trancl G) = (gtt_lang G)\<^sup>+"
  using GTT_trancl_sound GTT_trancl_complete by blast

end