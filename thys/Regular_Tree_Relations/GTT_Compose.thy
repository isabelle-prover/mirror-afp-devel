theory GTT_Compose
  imports GTT
begin

subsection \<open>GTT closure under composition\<close>

inductive_set \<Delta>\<^sub>\<epsilon>_set :: "('q, 'f) ta \<Rightarrow> ('q, 'f) ta \<Rightarrow> ('q \<times> 'q) set" for \<A> \<B> where
  \<Delta>\<^sub>\<epsilon>_set_cong: "TA_rule f ps p |\<in>| rules \<A> \<Longrightarrow> TA_rule f qs q |\<in>| rules \<B> \<Longrightarrow> length ps = length qs \<Longrightarrow>
   (\<And>i. i < length qs \<Longrightarrow> (ps ! i, qs ! i) \<in> \<Delta>\<^sub>\<epsilon>_set \<A> \<B>) \<Longrightarrow> (p, q) \<in> \<Delta>\<^sub>\<epsilon>_set \<A> \<B>"
| \<Delta>\<^sub>\<epsilon>_set_eps1: "(p, p') |\<in>| eps \<A> \<Longrightarrow> (p, q) \<in> \<Delta>\<^sub>\<epsilon>_set \<A> \<B> \<Longrightarrow> (p', q) \<in> \<Delta>\<^sub>\<epsilon>_set \<A> \<B>"
| \<Delta>\<^sub>\<epsilon>_set_eps2: "(q, q') |\<in>| eps \<B> \<Longrightarrow> (p, q) \<in> \<Delta>\<^sub>\<epsilon>_set \<A> \<B> \<Longrightarrow> (p, q') \<in> \<Delta>\<^sub>\<epsilon>_set \<A> \<B>"

lemma \<Delta>\<^sub>\<epsilon>_states: "\<Delta>\<^sub>\<epsilon>_set \<A> \<B> \<subseteq> fset (\<Q> \<A> |\<times>| \<Q> \<B>)"
proof -
  {fix p q assume "(p, q) \<in> \<Delta>\<^sub>\<epsilon>_set \<A> \<B>" then have "(p, q) \<in> fset (\<Q> \<A> |\<times>| \<Q> \<B>)"
      by (induct) (auto dest: rule_statesD eps_statesD)}
  then show ?thesis by auto
qed

lemma finite_\<Delta>\<^sub>\<epsilon> [simp]: "finite (\<Delta>\<^sub>\<epsilon>_set \<A> \<B>)"
  using finite_subset[OF \<Delta>\<^sub>\<epsilon>_states]
  by simp

context
includes fset.lifting
begin
lift_definition \<Delta>\<^sub>\<epsilon> :: "('q, 'f) ta \<Rightarrow> ('q, 'f) ta \<Rightarrow> ('q \<times> 'q) fset" is \<Delta>\<^sub>\<epsilon>_set by simp
lemmas \<Delta>\<^sub>\<epsilon>_cong = \<Delta>\<^sub>\<epsilon>_set_cong [Transfer.transferred]
lemmas \<Delta>\<^sub>\<epsilon>_eps1 = \<Delta>\<^sub>\<epsilon>_set_eps1 [Transfer.transferred]
lemmas \<Delta>\<^sub>\<epsilon>_eps2 = \<Delta>\<^sub>\<epsilon>_set_eps2 [Transfer.transferred]
lemmas \<Delta>\<^sub>\<epsilon>_cases = \<Delta>\<^sub>\<epsilon>_set.cases[Transfer.transferred]
lemmas \<Delta>\<^sub>\<epsilon>_induct [consumes 1, case_names \<Delta>\<^sub>\<epsilon>_cong \<Delta>\<^sub>\<epsilon>_eps1  \<Delta>\<^sub>\<epsilon>_eps2] = \<Delta>\<^sub>\<epsilon>_set.induct[Transfer.transferred]
lemmas \<Delta>\<^sub>\<epsilon>_intros = \<Delta>\<^sub>\<epsilon>_set.intros[Transfer.transferred]
lemmas \<Delta>\<^sub>\<epsilon>_simps = \<Delta>\<^sub>\<epsilon>_set.simps[Transfer.transferred]
end

lemma finite_alt_def [simp]:
  "finite {(\<alpha>, \<beta>). (\<exists>t. ground t \<and> \<alpha> |\<in>| ta_der \<A> t \<and> \<beta> |\<in>| ta_der \<B> t)}" (is "finite ?S")
  by (auto dest: ground_ta_der_states[THEN fsubsetD]
           intro!: finite_subset[of ?S "fset (\<Q> \<A> |\<times>| \<Q> \<B>)"])

lemma \<Delta>\<^sub>\<epsilon>_def':
  "\<Delta>\<^sub>\<epsilon> \<A> \<B> = {|(\<alpha>, \<beta>). (\<exists>t. ground t \<and> \<alpha> |\<in>| ta_der \<A> t \<and> \<beta> |\<in>| ta_der \<B> t)|}"
proof (intro fset_eqI iffI, goal_cases lr rl)
  case (lr x) obtain p q where x [simp]: "x = (p, q)" by (cases x)
  have "\<exists>t. ground t \<and> p |\<in>| ta_der \<A> t \<and> q |\<in>| ta_der \<B> t" using lr unfolding x
  proof (induct rule: \<Delta>\<^sub>\<epsilon>_induct)
    case (\<Delta>\<^sub>\<epsilon>_cong f ps p qs q)
    obtain ts where ts: "ground (ts i) \<and> ps ! i |\<in>| ta_der \<A> (ts i) \<and> qs ! i |\<in>| ta_der \<B> (ts i)"
      if "i < length qs" for i using \<Delta>\<^sub>\<epsilon>_cong(5) by metis
    then show ?case using \<Delta>\<^sub>\<epsilon>_cong(1-3)
      by (auto intro!: exI[of _ "Fun f (map ts [0..<length qs])"]) blast+
  qed (meson ta_der_eps)+
  then show ?case by auto
next
  case (rl x) obtain p q where x [simp]: "x = (p, q)" by (cases x)
  obtain t where "ground t" "p |\<in>| ta_der \<A> t" "q |\<in>| ta_der \<B> t" using rl by auto
  then show ?case unfolding x
  proof (induct t arbitrary: p q)
    case (Fun f ts)
    obtain p' ps where p': "TA_rule f ps p' |\<in>| rules \<A>" "p' = p \<or> (p', p) |\<in>| (eps \<A>)|\<^sup>+|" "length ps = length ts"
      "\<And>i. i < length ts \<Longrightarrow> ps ! i |\<in>| ta_der \<A> (ts ! i)" using Fun(3) by auto
    obtain q' qs where q': "f qs \<rightarrow> q' |\<in>| rules \<B>" "q' = q \<or> (q', q) |\<in>| (eps \<B>)|\<^sup>+|" "length qs = length ts"
      "\<And>i. i < length ts \<Longrightarrow> qs ! i |\<in>| ta_der \<B> (ts ! i)" using Fun(4) by auto
    have st: "(p', q') |\<in>| \<Delta>\<^sub>\<epsilon> \<A> \<B>"
      using Fun(1)[OF nth_mem _ p'(4) q'(4)] Fun(2) p'(3) q'(3)
      by (intro \<Delta>\<^sub>\<epsilon>_cong[OF p'(1) q'(1)]) auto
    {assume "(p', p) |\<in>| (eps \<A>)|\<^sup>+|" then have "(p, q') |\<in>| \<Delta>\<^sub>\<epsilon> \<A> \<B>" using st
        by (induct rule: ftrancl_induct) (auto intro: \<Delta>\<^sub>\<epsilon>_eps1)}
    from st this p'(2) have st: "(p, q') |\<in>| \<Delta>\<^sub>\<epsilon> \<A> \<B>" by auto
   {assume "(q', q) |\<in>| (eps \<B>)|\<^sup>+|" then have "(p, q) |\<in>| \<Delta>\<^sub>\<epsilon> \<A> \<B>" using st
        by (induct rule: ftrancl_induct) (auto intro: \<Delta>\<^sub>\<epsilon>_eps2)}
    from st this q'(2) show "(p, q) |\<in>| \<Delta>\<^sub>\<epsilon> \<A> \<B>" by auto
  qed auto
qed

lemma \<Delta>\<^sub>\<epsilon>_fmember:
  "(p, q) |\<in>| \<Delta>\<^sub>\<epsilon> \<A> \<B> \<longleftrightarrow> (\<exists>t. ground t \<and> p |\<in>| ta_der \<A> t \<and> q |\<in>| ta_der \<B> t)"
  by (auto simp: \<Delta>\<^sub>\<epsilon>_def')

definition GTT_comp :: "('q, 'f) gtt \<Rightarrow> ('q, 'f) gtt \<Rightarrow> ('q, 'f) gtt" where
  "GTT_comp \<G>\<^sub>1 \<G>\<^sub>2 =
    (let \<Delta> = \<Delta>\<^sub>\<epsilon> (snd \<G>\<^sub>1) (fst \<G>\<^sub>2) in
    (TA (gtt_rules (fst \<G>\<^sub>1, fst \<G>\<^sub>2)) (eps (fst \<G>\<^sub>1) |\<union>| eps (fst \<G>\<^sub>2) |\<union>| \<Delta>),
     TA (gtt_rules (snd \<G>\<^sub>1, snd \<G>\<^sub>2)) (eps (snd \<G>\<^sub>1) |\<union>| eps (snd \<G>\<^sub>2) |\<union>| (\<Delta>|\<inverse>|))))"

lemma gtt_syms_GTT_comp:
  "gtt_syms (GTT_comp A B) = gtt_syms A |\<union>| gtt_syms B"
  by (auto simp: GTT_comp_def ta_sig_def Let_def)

lemma \<Delta>\<^sub>\<epsilon>_statesD:
  "(p, q) |\<in>| \<Delta>\<^sub>\<epsilon> \<A> \<B> \<Longrightarrow> p |\<in>| \<Q> \<A>"
  "(p, q) |\<in>| \<Delta>\<^sub>\<epsilon> \<A> \<B> \<Longrightarrow> q |\<in>| \<Q> \<B>"
  using subsetD[OF \<Delta>\<^sub>\<epsilon>_states, of "(p, q)" \<A> \<B>]
  by (auto simp flip: \<Delta>\<^sub>\<epsilon>.rep_eq)

lemma \<Delta>\<^sub>\<epsilon>_statesD':
  "q |\<in>| eps_states (\<Delta>\<^sub>\<epsilon> \<A> \<B>) \<Longrightarrow> q |\<in>| \<Q> \<A> |\<union>| \<Q> \<B>"
  by (auto simp: eps_states_def dest: \<Delta>\<^sub>\<epsilon>_statesD)

lemma \<Delta>\<^sub>\<epsilon>_swap:
  "prod.swap p |\<in>| \<Delta>\<^sub>\<epsilon> \<A> \<B> \<longleftrightarrow> p |\<in>| \<Delta>\<^sub>\<epsilon> \<B> \<A>"
  by (auto simp: \<Delta>\<^sub>\<epsilon>_def')

lemma \<Delta>\<^sub>\<epsilon>_inverse [simp]:
  "(\<Delta>\<^sub>\<epsilon> \<A> \<B>)|\<inverse>| = \<Delta>\<^sub>\<epsilon> \<B> \<A>"
  by (auto simp: \<Delta>\<^sub>\<epsilon>_def')


lemma gtt_states_comp_union:
  "gtt_states (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2) |\<subseteq>| gtt_states \<G>\<^sub>1 |\<union>| gtt_states \<G>\<^sub>2"
proof (intro fsubsetI, goal_cases lr)
  case (lr q) then show ?case
    by (auto simp: GTT_comp_def gtt_states_def \<Q>_def dest: \<Delta>\<^sub>\<epsilon>_statesD')
qed

lemma GTT_comp_swap [simp]:
  "GTT_comp (prod.swap \<G>\<^sub>2) (prod.swap \<G>\<^sub>1) = prod.swap (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)"
  by (simp add: GTT_comp_def ac_simps)

lemma gtt_comp_complete_semi:
  assumes s: "q |\<in>| gta_der (fst \<G>\<^sub>1) s" and u: "q |\<in>| gta_der (snd \<G>\<^sub>1) u" and ut: "gtt_accept \<G>\<^sub>2 u t"
  shows "q |\<in>| gta_der (fst (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)) s" "q |\<in>| gta_der (snd (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)) t"
proof (goal_cases L R)
  let ?\<G> = "GTT_comp \<G>\<^sub>1 \<G>\<^sub>2"
  have  sub1l: "rules (fst \<G>\<^sub>1) |\<subseteq>| rules (fst ?\<G>)" "eps (fst \<G>\<^sub>1) |\<subseteq>| eps (fst ?\<G>)"
    and sub1r: "rules (snd \<G>\<^sub>1) |\<subseteq>| rules (snd ?\<G>)" "eps (snd \<G>\<^sub>1) |\<subseteq>| eps (snd ?\<G>)" 
    and sub2r: "rules (snd \<G>\<^sub>2) |\<subseteq>| rules (snd ?\<G>)" "eps (snd \<G>\<^sub>2) |\<subseteq>| eps (snd ?\<G>)"
    by (auto simp: GTT_comp_def)
  { case L then show ?case using s ta_der_mono[OF sub1l]
      by (auto simp: gta_der_def)
  next
    case R then show ?case using ut u unfolding gtt_accept_def
    proof (induct arbitrary: q s)
      case (base s t)
      from base(1) obtain p where p: "p |\<in>| gta_der (fst \<G>\<^sub>2) s" "p |\<in>| gta_der (snd \<G>\<^sub>2) t"
        by (auto simp: agtt_lang_def)
      then have "(p, q) |\<in>| eps (snd (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2))"
        using \<Delta>\<^sub>\<epsilon>_fmember[of p q "fst \<G>\<^sub>2" "snd \<G>\<^sub>1"] base(2)
        by (auto simp: GTT_comp_def gta_der_def)
      from ta_der_eps[OF this] show ?case using p ta_der_mono[OF sub2r]
        by (auto simp add: gta_der_def)
    next
      case (step ss ts f)
      from step(1, 4) obtain ps p where "TA_rule f ps p |\<in>| rules (snd \<G>\<^sub>1)" "p = q \<or> (p, q) |\<in>| (eps (snd \<G>\<^sub>1))|\<^sup>+|"
        "length ps = length ts" "\<And>i. i < length ts \<Longrightarrow> ps ! i |\<in>| gta_der (snd \<G>\<^sub>1) (ss ! i)"
        unfolding gta_der_def by auto
      then show ?case using step(1, 2) sub1r(1) ftrancl_mono[OF _ sub1r(2)]
        by (auto simp: gta_der_def intro!: exI[of _ p] exI[of _ ps])
    qed}
qed

lemmas gtt_comp_complete_semi' = gtt_comp_complete_semi[of _ "prod.swap \<G>\<^sub>2" _ _ "prod.swap \<G>\<^sub>1" for \<G>\<^sub>1 \<G>\<^sub>2,
  unfolded fst_swap snd_swap GTT_comp_swap gtt_accept_swap]

lemma gtt_comp_acomplete:
  "gcomp_rel UNIV (agtt_lang \<G>\<^sub>1) (agtt_lang \<G>\<^sub>2) \<subseteq> agtt_lang (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)"
proof (intro subrelI, goal_cases LR)
  case (LR s t)
  then consider
      q u where "q |\<in>| gta_der (fst \<G>\<^sub>1) s" "q |\<in>| gta_der (snd \<G>\<^sub>1) u" "gtt_accept \<G>\<^sub>2 u t"
    | q u where "q |\<in>| gta_der (snd \<G>\<^sub>2) t" "q |\<in>| gta_der (fst \<G>\<^sub>2) u" "gtt_accept \<G>\<^sub>1 s u"
    by (auto simp: gcomp_rel_def gtt_accept_def elim!: agtt_langE)
  then show ?case
  proof (cases)
    case 1 show ?thesis using gtt_comp_complete_semi[OF 1]
      by (auto simp: agtt_lang_def gta_der_def)
  next
    case 2 show ?thesis using gtt_comp_complete_semi'[OF 2]
      by (auto simp: agtt_lang_def gta_der_def)
  qed
qed

lemma \<Delta>\<^sub>\<epsilon>_steps_from_\<G>\<^sub>2:
  assumes "(q, q') |\<in>| (eps (fst (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)))|\<^sup>+|" "q |\<in>| gtt_states \<G>\<^sub>2"
    "gtt_states \<G>\<^sub>1 |\<inter>| gtt_states \<G>\<^sub>2 = {||}"
  shows "(q, q') |\<in>| (eps (fst \<G>\<^sub>2))|\<^sup>+| \<and> q' |\<in>| gtt_states \<G>\<^sub>2"
  using assms(1-2)
proof (induct rule: converse_ftrancl_induct)
  case (Base y)
  then show ?case using assms(3)
    by (fastforce simp: GTT_comp_def gtt_states_def dest: eps_statesD \<Delta>\<^sub>\<epsilon>_statesD(1))
next
  case (Step q p)
  have "(q, p) |\<in>| (eps (fst \<G>\<^sub>2))|\<^sup>+|" "p |\<in>| gtt_states \<G>\<^sub>2"
    using Step(1, 4) assms(3)
    by (auto simp: GTT_comp_def gtt_states_def dest: eps_statesD \<Delta>\<^sub>\<epsilon>_statesD(1))
  then show ?case using Step(3)
    by (auto intro: ftrancl_trans)
qed

lemma \<Delta>\<^sub>\<epsilon>_steps_from_\<G>\<^sub>1:
  assumes "(p, r) |\<in>| (eps (fst (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)))|\<^sup>+|" "p |\<in>| gtt_states \<G>\<^sub>1"
    "gtt_states \<G>\<^sub>1 |\<inter>| gtt_states \<G>\<^sub>2 = {||}"
  obtains "r |\<in>| gtt_states \<G>\<^sub>1" "(p, r) |\<in>| (eps (fst \<G>\<^sub>1))|\<^sup>+|"
  | q p' where "r |\<in>| gtt_states \<G>\<^sub>2" "p = p' \<or> (p, p') |\<in>| (eps (fst \<G>\<^sub>1))|\<^sup>+|" "(p', q) |\<in>| \<Delta>\<^sub>\<epsilon> (snd \<G>\<^sub>1) (fst \<G>\<^sub>2)"
    "q = r \<or> (q, r) |\<in>| (eps (fst \<G>\<^sub>2))|\<^sup>+|"
  using assms(1,2)
proof (induct arbitrary: thesis rule: converse_ftrancl_induct)
  case (Base p)
  from Base(1) consider (a) "(p, r) |\<in>| eps (fst \<G>\<^sub>1)" | (b) "(p, r) |\<in>| eps (fst \<G>\<^sub>2)" |
    (c) "(p, r) |\<in>| (\<Delta>\<^sub>\<epsilon> (snd \<G>\<^sub>1) (fst \<G>\<^sub>2))"
    by (auto simp: GTT_comp_def)
  then show ?case using assms(3) Base
    by cases (auto simp: GTT_comp_def gtt_states_def dest: eps_statesD \<Delta>\<^sub>\<epsilon>_statesD)
next
  case (Step q p)
  consider "(q, p) |\<in>| (eps (fst \<G>\<^sub>1))|\<^sup>+|" "p |\<in>| gtt_states \<G>\<^sub>1"
    | "(q, p) |\<in>| \<Delta>\<^sub>\<epsilon> (snd \<G>\<^sub>1) (fst \<G>\<^sub>2)" "p |\<in>| gtt_states \<G>\<^sub>2" using assms(3) Step(1, 6)
    by (auto simp: GTT_comp_def gtt_states_def dest: eps_statesD \<Delta>\<^sub>\<epsilon>_statesD)
  then show ?case
  proof (cases)
    case 1 note a = 1 show ?thesis
    proof (cases rule: Step(3))
      case (2 p' q)
      then show ?thesis using assms a
        by (auto intro: Step(5) ftrancl_trans)
    qed (auto simp: a(2) intro: Step(4) ftrancl_trans[OF a(1)])
  next
    case 2 show ?thesis using \<Delta>\<^sub>\<epsilon>_steps_from_\<G>\<^sub>2[OF Step(2) 2(2) assms(3)] Step(5)[OF _ _ 2(1)] by auto
  qed
qed

lemma \<Delta>\<^sub>\<epsilon>_steps_from_\<G>\<^sub>1_\<G>\<^sub>2:
  assumes "(q, q') |\<in>| (eps (fst (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)))|\<^sup>+|" "q |\<in>| gtt_states \<G>\<^sub>1 |\<union>| gtt_states \<G>\<^sub>2"
    "gtt_states \<G>\<^sub>1 |\<inter>| gtt_states \<G>\<^sub>2 = {||}"
  obtains "q |\<in>| gtt_states \<G>\<^sub>1" "q' |\<in>| gtt_states \<G>\<^sub>1" "(q, q') |\<in>| (eps (fst \<G>\<^sub>1))|\<^sup>+|"
  | p p' where "q |\<in>| gtt_states \<G>\<^sub>1" "q' |\<in>| gtt_states \<G>\<^sub>2" "q = p \<or> (q, p) |\<in>| (eps (fst \<G>\<^sub>1))|\<^sup>+|"
    "(p, p') |\<in>| \<Delta>\<^sub>\<epsilon> (snd \<G>\<^sub>1) (fst \<G>\<^sub>2)" "p' = q' \<or> (p', q') |\<in>| (eps (fst \<G>\<^sub>2))|\<^sup>+|"
  | "q |\<in>| gtt_states \<G>\<^sub>2" "(q, q') |\<in>| (eps (fst \<G>\<^sub>2))|\<^sup>+| \<and> q' |\<in>| gtt_states \<G>\<^sub>2"
  using assms \<Delta>\<^sub>\<epsilon>_steps_from_\<G>\<^sub>1 \<Delta>\<^sub>\<epsilon>_steps_from_\<G>\<^sub>2
  by (metis funion_iff)

lemma GTT_comp_eps_fst_statesD:
  "(p, q) |\<in>| eps (fst (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)) \<Longrightarrow> p |\<in>| gtt_states \<G>\<^sub>1 |\<union>| gtt_states \<G>\<^sub>2"
  "(p, q) |\<in>| eps (fst (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)) \<Longrightarrow> q |\<in>| gtt_states \<G>\<^sub>1 |\<union>| gtt_states \<G>\<^sub>2"
  by (auto simp: GTT_comp_def gtt_states_def dest: eps_statesD \<Delta>\<^sub>\<epsilon>_statesD)

lemma GTT_comp_eps_ftrancl_fst_statesD:
  "(p, q) |\<in>| (eps (fst (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)))|\<^sup>+| \<Longrightarrow> p |\<in>| gtt_states \<G>\<^sub>1 |\<union>| gtt_states \<G>\<^sub>2"
  "(p, q) |\<in>| (eps (fst (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)))|\<^sup>+| \<Longrightarrow> q |\<in>| gtt_states \<G>\<^sub>1 |\<union>| gtt_states \<G>\<^sub>2"
  using GTT_comp_eps_fst_statesD[of _ _ \<G>\<^sub>1 \<G>\<^sub>2]
  by (meson converse_ftranclE ftranclE)+

lemma GTT_comp_first:
  assumes "q |\<in>| ta_der (fst (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)) t" "q |\<in>| gtt_states \<G>\<^sub>1"
    "gtt_states \<G>\<^sub>1 |\<inter>| gtt_states \<G>\<^sub>2 = {||}"
  shows "q |\<in>| ta_der (fst \<G>\<^sub>1) t"
  using assms(1,2)
proof (induct t arbitrary: q)
  case (Var q')
  have "q \<noteq> q' \<Longrightarrow> q' |\<in>| gtt_states \<G>\<^sub>1 |\<union>| gtt_states \<G>\<^sub>2" using Var
    by (auto dest: GTT_comp_eps_ftrancl_fst_statesD)
  then show ?case using Var assms(3)
    by (auto elim: \<Delta>\<^sub>\<epsilon>_steps_from_\<G>\<^sub>1_\<G>\<^sub>2)
next
  case (Fun f ts)
  obtain q' qs where q': "TA_rule f qs q' |\<in>| rules (fst (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2))"
    "q' = q \<or> (q', q) |\<in>| (eps (fst (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)))|\<^sup>+|" "length qs = length ts"
    "\<And>i. i < length ts \<Longrightarrow> qs ! i |\<in>| ta_der (fst (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)) (ts ! i)"
    using Fun(2) by auto
  have "q' |\<in>| gtt_states \<G>\<^sub>1 |\<union>| gtt_states \<G>\<^sub>2" using q'(1)
    by (auto simp: GTT_comp_def gtt_states_def dest: rule_statesD)
  then have st: "q' |\<in>| gtt_states \<G>\<^sub>1" and eps:"q' = q \<or> (q', q) |\<in>| (eps (fst \<G>\<^sub>1))|\<^sup>+|"
    using q'(2) Fun(3) assms(3)
    by (auto elim!: \<Delta>\<^sub>\<epsilon>_steps_from_\<G>\<^sub>1_\<G>\<^sub>2)
  from st have rule: "TA_rule f qs q' |\<in>| rules (fst \<G>\<^sub>1)" using assms(3) q'(1)
    by (auto simp: GTT_comp_def gtt_states_def dest: rule_statesD)
  have "i < length ts \<Longrightarrow> qs ! i |\<in>| ta_der (fst \<G>\<^sub>1) (ts ! i)" for i
    using rule q'(3, 4)
    by (intro Fun(1)[OF nth_mem]) (auto simp: gtt_states_def dest!: rule_statesD(4))
  then show ?case using q'(3) rule eps
    by auto
qed

lemma GTT_comp_second:
  assumes "gtt_states \<G>\<^sub>1 |\<inter>| gtt_states \<G>\<^sub>2 = {||}" "q |\<in>| gtt_states \<G>\<^sub>2"
    "q |\<in>| ta_der (snd (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)) t"
  shows "q |\<in>| ta_der (snd \<G>\<^sub>2) t"
  using assms GTT_comp_first[of q "prod.swap \<G>\<^sub>2" "prod.swap \<G>\<^sub>1"]
  by (auto simp: gtt_states_def)

lemma gtt_comp_sound_semi:
  fixes \<G>\<^sub>1 \<G>\<^sub>2 :: "('f, 'q) gtt"
  assumes as2: "gtt_states \<G>\<^sub>1 |\<inter>| gtt_states \<G>\<^sub>2 = {||}"
  and 1: "q |\<in>| gta_der (fst (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)) s" "q |\<in>| gta_der (snd (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)) t" "q |\<in>| gtt_states \<G>\<^sub>1"
  shows "\<exists>u. q |\<in>| gta_der (snd \<G>\<^sub>1) u \<and> gtt_accept \<G>\<^sub>2 u t" using 1(2,3) unfolding gta_der_def
proof (induct rule: ta_der_gterm_induct)
  case (GFun f ts ps p q)
  show ?case
  proof (cases "p |\<in>| gtt_states \<G>\<^sub>1")
    case True
    then have *: "TA_rule f ps p |\<in>| rules (snd \<G>\<^sub>1)" using GFun(1, 6) as2
      by (auto simp: GTT_comp_def gtt_states_def dest: rule_statesD)
    moreover have st: "i < length ps \<Longrightarrow> ps ! i |\<in>| gtt_states \<G>\<^sub>1" for i using *
      by (force simp: gtt_states_def dest: rule_statesD)
    moreover have "i < length ps \<Longrightarrow> \<exists>u. ps ! i |\<in>| ta_der (snd \<G>\<^sub>1) (term_of_gterm u) \<and> gtt_accept \<G>\<^sub>2 u (ts ! i)" for i
      using st GFun(2) by (intro GFun(5)) simp
    then obtain us where
      "\<And>i. i < length ps \<Longrightarrow> ps ! i |\<in>| ta_der (snd \<G>\<^sub>1) (term_of_gterm (us i)) \<and> gtt_accept \<G>\<^sub>2 (us i) (ts ! i)"
      by metis
    moreover have "p = q \<or> (p, q) |\<in>| (eps (snd \<G>\<^sub>1))|\<^sup>+|" using GFun(3, 6) True as2
      by (auto simp: gtt_states_def  elim!: \<Delta>\<^sub>\<epsilon>_steps_from_\<G>\<^sub>1_\<G>\<^sub>2[of p q "prod.swap \<G>\<^sub>2" "prod.swap \<G>\<^sub>1", simplified])
    ultimately show ?thesis using GFun(2)
      by (intro exI[of _ "GFun f (map us [0..<length ts])"])
         (auto simp: gtt_accept_def intro!: exI[of _ ps] exI[of _ p])
  next
    case False note nt_st = this
    then have False: "p \<noteq> q" using GFun(6) by auto
    then have eps: "(p, q) |\<in>| (eps (snd (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)))|\<^sup>+|" using GFun(3) by simp
    show ?thesis using \<Delta>\<^sub>\<epsilon>_steps_from_\<G>\<^sub>1_\<G>\<^sub>2[of p q "prod.swap \<G>\<^sub>2" "prod.swap \<G>\<^sub>1", simplified, OF eps]
    proof (cases, goal_cases)
      case 1 then show ?case using False GFun(3)
        by (metis GTT_comp_eps_ftrancl_fst_statesD(1) GTT_comp_swap fst_swap funion_iff)
    next
      case 2 then show ?case using as2 by (auto simp: gtt_states_def)
    next
      case 3 then show ?case using as2 GFun(6) by (auto simp: gtt_states_def)
    next
      case (4 r p')
      have meet: "r |\<in>| ta_der (snd (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)) (Fun f (map term_of_gterm ts))"
        using GFun(1 - 4) 4(3) False
        by (auto simp: GTT_comp_def in_ftrancl_UnI intro!: exI[ of _ ps] exI[ of _ p])
      then obtain u where wit: "ground u" "p' |\<in>| ta_der (snd \<G>\<^sub>1) u" "r |\<in>| ta_der (fst \<G>\<^sub>2) u"
        using 4(4-) unfolding \<Delta>\<^sub>\<epsilon>_def' by blast
      from wit(1, 3) have "gtt_accept \<G>\<^sub>2 (gterm_of_term u) (GFun f ts)"
        using GTT_comp_second[OF as2 _ meet] unfolding gtt_accept_def
        by (intro gmctxt_cl.base agtt_langI[of r])
           (auto simp add: gta_der_def gtt_states_def simp del: ta_der_Fun dest: ground_ta_der_states)
      then show ?case using 4(5) wit(1, 2)
        by (intro exI[of _ "gterm_of_term u"]) (auto simp add: ta_der_trancl_eps)
    next
      case 5
      then show ?case using nt_st as2
        by (simp add: gtt_states_def)  
    qed
  qed
qed

lemma gtt_comp_asound:
  assumes "gtt_states \<G>\<^sub>1 |\<inter>| gtt_states \<G>\<^sub>2 = {||}"
  shows "agtt_lang (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2) \<subseteq> gcomp_rel UNIV (agtt_lang \<G>\<^sub>1) (agtt_lang \<G>\<^sub>2)"
proof (intro subrelI, goal_cases LR)
  case (LR s t)
  obtain q where q: "q |\<in>| gta_der (fst (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)) s" "q |\<in>| gta_der (snd (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)) t"
    using LR by (auto simp: agtt_lang_def)
  { (* prepare symmetric cases: q |\<in>| gtt_states \<G>\<^sub>1 and q |\<in>| gtt_states \<G>\<^sub>2 *)
    fix \<G>\<^sub>1 \<G>\<^sub>2 s t assume as2: "gtt_states \<G>\<^sub>1 |\<inter>| gtt_states \<G>\<^sub>2 = {||}"
      and 1: "q |\<in>| ta_der (fst (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)) (term_of_gterm s)"
        "q |\<in>| ta_der (snd (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)) (term_of_gterm t)" "q |\<in>| gtt_states \<G>\<^sub>1"
    note st = GTT_comp_first[OF 1(1,3) as2]
    obtain u where u: "q |\<in>| ta_der (snd \<G>\<^sub>1) (term_of_gterm u)" "gtt_accept \<G>\<^sub>2 u t"
      using gtt_comp_sound_semi[OF as2 1[folded gta_der_def]] by (auto simp: gta_der_def)
    have "(s, u) \<in> agtt_lang \<G>\<^sub>1" using st u(1)
      by (auto simp: agtt_lang_def gta_der_def)
    moreover have "(u, t) \<in> gtt_lang \<G>\<^sub>2" using u(2)
      by (auto simp: gtt_accept_def)
    ultimately have "(s, t) \<in> agtt_lang \<G>\<^sub>1 O gmctxt_cl UNIV (agtt_lang \<G>\<^sub>2)"
      by auto}
  note base = this
  consider "q |\<in>| gtt_states \<G>\<^sub>1" | "q |\<in>| gtt_states \<G>\<^sub>2" | "q |\<notin>| gtt_states \<G>\<^sub>1 |\<union>| gtt_states \<G>\<^sub>2" by blast
  then show ?case using q assms
  proof (cases, goal_cases)
    case 1 then show ?case using base[of \<G>\<^sub>1 \<G>\<^sub>2 s t]
      by (auto simp: gcomp_rel_def gta_der_def)
  next
    case 2 then show ?case using base[of "prod.swap \<G>\<^sub>2" "prod.swap \<G>\<^sub>1" t s, THEN converseI]
      by (auto simp: gcomp_rel_def converse_relcomp converse_agtt_lang gta_der_def gtt_states_def)
         (simp add: finter_commute funion_commute gtt_lang_swap prod.swap_def)+
  next
    case 3 then show ?case using fsubsetD[OF gtt_states_comp_union[of \<G>\<^sub>1 \<G>\<^sub>2], of q]
      by (auto simp: gta_der_def gtt_states_def)
  qed
qed

lemma gtt_comp_lang_complete:
  shows "gtt_lang \<G>\<^sub>1 O gtt_lang \<G>\<^sub>2 \<subseteq> gtt_lang (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2)"
  using gmctxt_cl_mono_rel[OF gtt_comp_acomplete, of UNIV \<G>\<^sub>1 \<G>\<^sub>2]
  by (simp only: gcomp_rel[symmetric])

lemma gtt_comp_alang:
  assumes "gtt_states \<G>\<^sub>1 |\<inter>| gtt_states \<G>\<^sub>2 = {||}"
  shows "agtt_lang (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2) = gcomp_rel UNIV (agtt_lang \<G>\<^sub>1) (agtt_lang \<G>\<^sub>2)"
  by (intro equalityI gtt_comp_asound[OF assms] gtt_comp_acomplete)

lemma gtt_comp_lang:
  assumes "gtt_states \<G>\<^sub>1 |\<inter>| gtt_states \<G>\<^sub>2 = {||}"
  shows "gtt_lang (GTT_comp \<G>\<^sub>1 \<G>\<^sub>2) = gtt_lang \<G>\<^sub>1 O gtt_lang \<G>\<^sub>2"
  by (simp only: arg_cong[OF gtt_comp_alang[OF assms], of "gmctxt_cl UNIV"] gcomp_rel)

abbreviation GTT_comp' where
  "GTT_comp' \<G>\<^sub>1 \<G>\<^sub>2 \<equiv> GTT_comp (fmap_states_gtt Inl \<G>\<^sub>1) (fmap_states_gtt Inr \<G>\<^sub>2)"

lemma gtt_comp'_alang:
  shows "agtt_lang (GTT_comp' \<G>\<^sub>1 \<G>\<^sub>2) = gcomp_rel UNIV (agtt_lang \<G>\<^sub>1) (agtt_lang \<G>\<^sub>2)"
proof -
  have [simp]: "finj_on Inl (gtt_states \<G>\<^sub>1)" "finj_on Inr (gtt_states \<G>\<^sub>2)"
    by (auto simp add: finj_on.rep_eq)
  then show ?thesis                                        
    by (subst gtt_comp_alang) (auto simp: agtt_lang_fmap_states_gtt)
qed

end