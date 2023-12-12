theory P_Automata imports Labeled_Transition_Systems.LTS begin


section \<open>Automata\<close>


subsection \<open>P-Automaton locale\<close>

locale P_Automaton = LTS transition_relation 
  for transition_relation :: "('state::finite, 'label) transition set" +
  fixes Init :: "'ctr_loc::enum \<Rightarrow> 'state"
    and finals :: "'state set"
begin

definition initials :: "'state set" where
  "initials \<equiv> Init ` UNIV"

lemma initials_list:
  "initials = set (map Init Enum.enum)"
  using enum_UNIV unfolding initials_def by force

definition accepts_aut :: "'ctr_loc \<Rightarrow> 'label list \<Rightarrow> bool" where
  "accepts_aut \<equiv> \<lambda>p w. (\<exists>q \<in> finals. (Init p, w, q) \<in> trans_star)"

definition lang_aut :: "('ctr_loc * 'label list) set" where
  "lang_aut = {(p,w). accepts_aut p w}"

definition nonempty where
  "nonempty \<longleftrightarrow> lang_aut \<noteq> {}"

lemma nonempty_alt: 
  "nonempty \<longleftrightarrow> (\<exists>p. \<exists>q \<in> finals. \<exists>w. (Init p, w, q) \<in> trans_star)"
  unfolding lang_aut_def nonempty_def accepts_aut_def by auto

typedef 'a mark_state = "{(Q :: 'a set, I). I \<subseteq> Q}"
  by auto
setup_lifting type_definition_mark_state
lift_definition get_visited :: "'a mark_state \<Rightarrow> 'a set" is fst .
lift_definition get_next :: "'a mark_state \<Rightarrow> 'a set" is snd .
lift_definition make_mark_state :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a mark_state" is "\<lambda>Q J. (Q \<union> J, J)" by auto
lemma get_next_get_visited: "get_next ms \<subseteq> get_visited ms"
  by transfer auto
lemma get_next_set_next[simp]: "get_next (make_mark_state Q J) = J"
  by transfer auto
lemma get_visited_set_next[simp]: "get_visited (make_mark_state Q J) = Q \<union> J"
  by transfer auto

function mark where
  "mark ms \<longleftrightarrow>
     (let Q = get_visited ms; I = get_next ms in
     if I \<inter> finals \<noteq> {} then True
     else let J = (\<Union>(q,w,q')\<in>transition_relation. if q \<in> I \<and> q' \<notin> Q then {q'} else {}) in
       if J = {} then False else mark (make_mark_state Q J))"
  by auto
termination by (relation "measure (\<lambda>ms. card (UNIV :: 'a set) - card (get_visited ms :: 'a set))")
    (fastforce intro!: diff_less_mono2 psubset_card_mono split: if_splits)+

declare mark.simps[simp del]

lemma trapped_transitions: "(p, w, q) \<in> trans_star \<Longrightarrow>
  \<forall>p \<in> Q. (\<forall>\<gamma> q. (p, \<gamma>, q) \<in> transition_relation \<longrightarrow> q \<in> Q) \<Longrightarrow>
  p \<in> Q \<Longrightarrow> q \<in> Q"
  by (induct p w q rule: trans_star.induct) auto

lemma mark_complete: "(p, w, q) \<in> trans_star \<Longrightarrow> (get_visited ms - get_next ms) \<inter> finals = {} \<Longrightarrow>
  \<forall>p \<in> get_visited ms - get_next ms. \<forall>q \<gamma>. (p, \<gamma>, q) \<in> transition_relation \<longrightarrow> q \<in> get_visited ms \<Longrightarrow>
  p \<in> get_visited ms \<Longrightarrow> q \<in> finals \<Longrightarrow> mark ms"
proof (induct p w q arbitrary: ms rule: trans_star.induct)
  case (trans_star_refl p)
  then show ?case by (subst mark.simps) (auto simp: Let_def)
next
  case step: (trans_star_step p \<gamma> q' w q)
  define J where "J \<equiv> \<Union>(q, w, q')\<in>transition_relation. if q \<in> get_next ms \<and> q' \<notin> get_visited ms then {q'} else {}"
  show ?case
  proof (cases "J = {}")
    case True
    then have "q' \<in> get_visited ms"
      by (smt (z3) DiffI Diff_disjoint Int_iff J_def SUP_bot_conv(2) case_prod_conv insertI1 
          step.hyps(1) step.prems(2) step.prems(3))
    with True show ?thesis
      using step(1,2,4,5,7)
      by (subst mark.simps)
        (auto 10 0 intro!: step(3) elim!: set_mp[of _ "get_next ms"] simp: split_beta J_def
          dest: trapped_transitions[of q' w q "get_visited ms"])
  next
    case False
    then have [simp]: "get_visited ms \<union> J - J = get_visited ms"
      by (auto simp: J_def split: if_splits)
    then have "p \<in> get_visited ms \<Longrightarrow> (p, \<gamma>, q) \<in> transition_relation \<Longrightarrow> q \<notin> get_visited ms \<Longrightarrow> q \<in> J" for p \<gamma> q
      using step(5)
      by (cases "p \<in> get_next ms") 
        (auto simp only: J_def simp_thms if_True if_False intro!: UN_I[of "(p, \<gamma>, q)"])
    with False show ?thesis
      using step(1,4,5,6,7)
      by (subst mark.simps)
        (auto 0 2 simp add: Let_def J_def[symmetric] disj_commute
        intro!: step(3)[of "make_mark_state (get_visited ms) J"])
  qed
qed


lemma mark_sound: "mark ms \<Longrightarrow> (\<exists>p \<in> get_next ms. \<exists>q \<in> finals. \<exists>w. (p, w, q) \<in> trans_star)"
  by (induct ms rule: mark.induct)
    (subst (asm) (2) mark.simps, fastforce dest: trans_star_step simp: Let_def split: if_splits)

lemma nonempty_code[code]: "nonempty = mark (make_mark_state {} (set (map Init Enum.enum)))"
  using mark_complete[of _ _ _ "make_mark_state {} initials"]
        mark_sound[of "make_mark_state {} initials"] nonempty_alt 
  unfolding initials_def initials_list[symmetric] by auto


end


subsection \<open>Intersection P-Automaton locale\<close>

locale Intersection_P_Automaton = 
  A1: P_Automaton ts1 Init finals1 +
  A2: P_Automaton ts2 Init finals2
  for ts1 :: "('state :: finite, 'label) transition set" 
    and Init :: "'ctr_loc :: enum \<Rightarrow> 'state" 
    and finals1 :: "'state set" 
    and ts2 :: "('state, 'label) transition set" 
    and finals2 :: "'state set" 
begin

sublocale pa: P_Automaton "inters ts1 ts2" "(\<lambda>p. (Init p, Init p))" "inters_finals finals1 finals2"
  .

definition accepts_aut_inters where
  "accepts_aut_inters p w = pa.accepts_aut p w"

definition lang_aut_inters :: "('ctr_loc * 'label list) set" where
  "lang_aut_inters = {(p,w). accepts_aut_inters p w}"

lemma trans_star_inter:
  assumes "(p1, w, p2) \<in> A1.trans_star"
  assumes "(q1, w, q2) \<in> A2.trans_star"
  shows "((p1,q1), w :: 'label list, (p2,q2)) \<in> pa.trans_star"
  using assms
proof (induction w arbitrary: p1 q1)
  case (Cons \<alpha> w1')
  obtain p' where p'_p: "(p1, \<alpha>, p') \<in> ts1 \<and> (p', w1', p2) \<in> A1.trans_star"
    using Cons by (metis LTS.trans_star_cons) 
  obtain q' where q'_p: "(q1, \<alpha>, q') \<in> ts2 \<and>(q', w1', q2) \<in> A2.trans_star"
    using Cons by (metis LTS.trans_star_cons) 
  have ind: "((p', q'), w1', p2, q2) \<in> pa.trans_star"
  proof -
    have "Suc (length w1') = length (\<alpha>#w1')"
      by auto
    moreover
    have "(p', w1', p2) \<in> A1.trans_star"
      using p'_p by simp
    moreover
    have "(q', w1', q2) \<in> A2.trans_star"
      using q'_p by simp
    ultimately
    show "((p', q'), w1', p2, q2) \<in> pa.trans_star"
      using Cons(1) by auto
  qed
  moreover
  have "((p1, q1), \<alpha>, (p', q')) \<in> (inters ts1 ts2)"
    by (simp add: inters_def p'_p q'_p)
  ultimately
  have "((p1, q1), \<alpha>#w1', p2, q2) \<in> pa.trans_star"
    by (meson LTS.trans_star.trans_star_step)
  moreover
  have "length ((\<alpha>#w1')) > 0"
    by auto
  moreover
  have "hd ((\<alpha>#w1')) = \<alpha>"
    by auto
  ultimately
  show ?case
    by force
next
  case Nil
  then show ?case
    by (metis LTS.trans_star.trans_star_refl LTS.trans_star_empty)
qed

lemma inters_trans_star1:
  assumes "(p1q2, w :: 'label list, p2q2) \<in> pa.trans_star"
  shows "(fst p1q2, w, fst p2q2) \<in> A1.trans_star"
  using assms 
proof (induction rule: LTS.trans_star.induct[OF assms(1)])
  case (1 p)
  then show ?case
    by (simp add: LTS.trans_star.trans_star_refl) 
next
  case (2 p \<gamma> q' w q)
  then have ind: "(fst q', w, fst q) \<in> A1.trans_star"
    by auto
  from 2(1) have "(p, \<gamma>, q') \<in> 
                     {((p1, q1), \<alpha>, p2, q2) |p1 q1 \<alpha> p2 q2. (p1, \<alpha>, p2) \<in> ts1 \<and> (q1, \<alpha>, q2) \<in> ts2}"
    unfolding inters_def by auto
  then have "\<exists>p1 q1. p = (p1, q1) \<and> (\<exists>p2 q2. q' = (p2, q2) \<and> (p1, \<gamma>, p2) \<in> ts1 \<and> (q1, \<gamma>, q2) \<in> ts2)"
    by simp
  then obtain p1 q1 where "p = (p1, q1) \<and> (\<exists>p2 q2. q' = (p2, q2) \<and> (p1, \<gamma>, p2) \<in> ts1 \<and> (q1, \<gamma>, q2) \<in> ts2)"
    by auto
  then show ?case
    using LTS.trans_star.trans_star_step ind by fastforce
qed

lemma inters_trans_star:
  assumes "(p1q2, w :: 'label list, p2q2) \<in> pa.trans_star"
  shows "(snd p1q2, w, snd p2q2) \<in> A2.trans_star"
  using assms 
proof (induction rule: LTS.trans_star.induct[OF assms(1)])
  case (1 p)
  then show ?case
    by (simp add: LTS.trans_star.trans_star_refl) 
next
  case (2 p \<gamma> q' w q)
  then have ind: "(snd q', w, snd q) \<in> A2.trans_star"
    by auto
  from 2(1) have "(p, \<gamma>, q') \<in> 
                     {((p1, q1), \<alpha>, p2, q2) |p1 q1 \<alpha> p2 q2. (p1, \<alpha>, p2) \<in> ts1 \<and> (q1, \<alpha>, q2) \<in> ts2}"
    unfolding inters_def by auto
  then have "\<exists>p1 q1. p = (p1, q1) \<and> (\<exists>p2 q2. q' = (p2, q2) \<and> (p1, \<gamma>, p2) \<in> ts1 \<and> (q1, \<gamma>, q2) \<in> ts2)"
    by simp
  then obtain p1 q1 where "p = (p1, q1) \<and> (\<exists>p2 q2. q' = (p2, q2) \<and> (p1, \<gamma>, p2) \<in> ts1 \<and> (q1, \<gamma>, q2) \<in> ts2)"
    by auto
  then show ?case
    using LTS.trans_star.trans_star_step ind by fastforce
qed

lemma inters_trans_star_iff:
  "((p1,q2), w :: 'label list, (p2,q2)) \<in> pa.trans_star \<longleftrightarrow> (p1, w, p2) \<in> A1.trans_star \<and> (q2, w, q2) \<in> A2.trans_star"
  by (metis fst_conv inters_trans_star inters_trans_star1 snd_conv trans_star_inter)

lemma inters_accept_iff: "accepts_aut_inters p w \<longleftrightarrow> A1.accepts_aut p w \<and> A2.accepts_aut p w"
proof
  assume "accepts_aut_inters p w"
  then show "A1.accepts_aut p w \<and> A2.accepts_aut p w"
    unfolding accepts_aut_inters_def A1.accepts_aut_def A2.accepts_aut_def pa.accepts_aut_def 
    unfolding inters_finals_def 
    using inters_trans_star_iff[of _ _ w _ ]
    using SigmaE fst_conv inters_trans_star inters_trans_star1 snd_conv
    by (metis (no_types, lifting))
next
  assume a: "A1.accepts_aut p w \<and> A2.accepts_aut p w"
  then have "(\<exists>q\<in>finals1. (Init p, w, q) \<in> A1.trans_star) \<and> 
             (\<exists>q\<in>finals2. (Init p, w, q) \<in> A2.trans_star)" 
    unfolding A1.accepts_aut_def A2.accepts_aut_def by auto
  then show "accepts_aut_inters p w"
    unfolding accepts_aut_inters_def pa.accepts_aut_def inters_finals_def
    by (auto simp: P_Automaton.accepts_aut_def intro: trans_star_inter)
qed

lemma lang_aut_alt: 
  "pa.lang_aut = {(p, w). (p, w) \<in> lang_aut_inters}"
  unfolding pa.lang_aut_def lang_aut_inters_def accepts_aut_inters_def pa.accepts_aut_def
  by auto

lemma inters_lang: "lang_aut_inters = A1.lang_aut \<inter> A2.lang_aut"
  unfolding lang_aut_inters_def A1.lang_aut_def A2.lang_aut_def using inters_accept_iff by auto

end


section \<open>Automata with epsilon\<close>


subsection \<open>P-Automaton with epsilon locale\<close>

locale P_Automaton_\<epsilon> = LTS_\<epsilon> transition_relation for transition_relation :: "('state::finite, 'label option) transition set" +
  fixes finals :: "'state set" and Init :: "'ctr_loc :: enum \<Rightarrow> 'state"
begin

definition accepts_aut_\<epsilon> :: "'ctr_loc \<Rightarrow> 'label list \<Rightarrow> bool" where
  "accepts_aut_\<epsilon> \<equiv> \<lambda>p w. (\<exists>q \<in> finals. (Init p, w, q) \<in> trans_star_\<epsilon>)"

definition lang_aut_\<epsilon> :: "('ctr_loc * 'label list) set" where
  "lang_aut_\<epsilon> = {(p,w). accepts_aut_\<epsilon> p w}"

definition nonempty_\<epsilon> where
  "nonempty_\<epsilon> \<longleftrightarrow> lang_aut_\<epsilon> \<noteq> {}"

end


subsection \<open>Intersection P-Automaton with epsilon locale\<close>

locale Intersection_P_Automaton_\<epsilon> = 
  A1: P_Automaton_\<epsilon> ts1 finals1 Init +
  A2: P_Automaton_\<epsilon> ts2 finals2 Init
  for ts1 :: "('state :: finite, 'label option) transition set" 
    and finals1 :: "'state set" 
    and Init :: "'ctr_loc :: enum \<Rightarrow> 'state"
    and ts2 :: "('state, 'label option) transition set" 
    and finals2 :: "'state set" 
begin

abbreviation \<epsilon> :: "'label option" where
  "\<epsilon> == None"

sublocale pa: P_Automaton_\<epsilon> "inters_\<epsilon> ts1 ts2" "inters_finals finals1 finals2" "(\<lambda>p. (Init p, Init p))"
  .

definition accepts_aut_inters_\<epsilon> where
  "accepts_aut_inters_\<epsilon> p w = pa.accepts_aut_\<epsilon> p w"

definition lang_aut_inters_\<epsilon> :: "('ctr_loc * 'label list) set" where
  "lang_aut_inters_\<epsilon> = {(p,w). accepts_aut_inters_\<epsilon> p w}"


lemma trans_star_trans_star_\<epsilon>_inter:
  assumes "LTS_\<epsilon>.\<epsilon>_exp w1 w"
  assumes "LTS_\<epsilon>.\<epsilon>_exp w2 w"
  assumes "(p1, w1, p2) \<in> A1.trans_star"
  assumes "(q1, w2, q2) \<in> A2.trans_star"
  shows "((p1,q1), w :: 'label list, (p2,q2)) \<in> pa.trans_star_\<epsilon>"
  using assms
proof (induction "length w1 + length w2" arbitrary: w1 w2 w p1 q1 rule: less_induct)
  case less
  then show ?case
  proof (cases "\<exists>\<alpha> w1' w2' \<beta>. w1=Some \<alpha>#w1' \<and> w2=Some \<beta>#w2'")
    case True
    from True obtain \<alpha> \<beta> w1' w2' where True'':
      "w1=Some \<alpha>#w1'"
      "w2=Some \<beta>#w2'"
      by auto
    have "\<alpha> = \<beta>"
      by (metis True''(1) True''(2) LTS_\<epsilon>.\<epsilon>_exp_Some_hd less.prems(1) less.prems(2))
    then have True':   
      "w1=Some \<alpha>#w1'"
      "w2=Some \<alpha>#w2'"
      using True'' by auto
    define w' where "w' = tl w"
    obtain p' where p'_p: "(p1, Some \<alpha>, p') \<in> ts1 \<and> (p', w1', p2) \<in> A1.trans_star"
      using less True'(1) by (metis LTS_\<epsilon>.trans_star_cons_\<epsilon>)
    obtain q' where q'_p: "(q1, Some \<alpha>, q') \<in> ts2 \<and>(q', w2', q2) \<in> A2.trans_star"
      using less True'(2) by (metis LTS_\<epsilon>.trans_star_cons_\<epsilon>) 
    have ind: "((p', q'), w', p2, q2) \<in> pa.trans_star_\<epsilon>"
    proof -
      have "length w1' + length w2' < length w1 + length w2"
        using True'(1) True'(2) by simp
      moreover
      have "LTS_\<epsilon>.\<epsilon>_exp w1' w'"
        by (metis (no_types) LTS_\<epsilon>.\<epsilon>_exp_def less(2) True'(1) list.map(2) list.sel(3) 
            option.simps(3) removeAll.simps(2) w'_def)
      moreover
      have "LTS_\<epsilon>.\<epsilon>_exp w2' w'"
        by (metis (no_types) LTS_\<epsilon>.\<epsilon>_exp_def less(3) True'(2) list.map(2) list.sel(3)
            option.simps(3) removeAll.simps(2) w'_def)
      moreover
      have "(p', w1', p2) \<in> A1.trans_star"
        using p'_p by simp
      moreover
      have "(q', w2', q2) \<in> A2.trans_star"
        using q'_p by simp
      ultimately
      show "((p', q'), w', p2, q2) \<in> pa.trans_star_\<epsilon>"
        using less(1)[of w1' w2' w' p' q'] by auto
    qed
    moreover
    have "((p1, q1), Some \<alpha>, (p', q')) \<in> (inters_\<epsilon> ts1 ts2)"
      by (simp add: inters_\<epsilon>_def p'_p q'_p)
    ultimately
    have "((p1, q1), \<alpha>#w', p2, q2) \<in> pa.trans_star_\<epsilon>"
      by (meson LTS_\<epsilon>.trans_star_\<epsilon>.trans_star_\<epsilon>_step_\<gamma>)
    moreover
    have "length w > 0"
      using less(3) True' LTS_\<epsilon>.\<epsilon>_exp_Some_length by metis
    moreover
    have "hd w = \<alpha>"
      using less(3) True' LTS_\<epsilon>.\<epsilon>_exp_Some_hd by metis
    ultimately
    show ?thesis
      using w'_def by force
  next
    case False
    note False_outer_outer_outer_outer = False
    show ?thesis 
    proof (cases "w1 = [] \<and> w2 = []")
      case True
      then have same: "p1 = p2 \<and> q1 = q2"
        by (metis LTS.trans_star_empty less.prems(3) less.prems(4))
      have "w = []"
        using True less(2) LTS_\<epsilon>.exp_empty_empty by auto
      then show ?thesis
        using less True
        by (simp add: LTS_\<epsilon>.trans_star_\<epsilon>.trans_star_\<epsilon>_refl same)
    next
      case False
      note False_outer_outer_outer = False
      show ?thesis
      proof (cases "\<exists>w1'. w1=\<epsilon>#w1'")
        case True (* Adapted from above. Maybe they can be merged. *)
        then obtain w1' where True':
          "w1=\<epsilon>#w1'"
          by auto
        obtain p' where p'_p: "(p1, \<epsilon>, p') \<in> ts1 \<and> (p', w1', p2) \<in> A1.trans_star"
          using less True'(1) by (metis LTS_\<epsilon>.trans_star_cons_\<epsilon>)
        have q'_p: "(q1, w2, q2) \<in> A2.trans_star"
          using less by metis
        have ind: "((p', q1), w, p2, q2) \<in> pa.trans_star_\<epsilon>"
        proof -
          have "length w1' + length w2 < length w1 + length w2"
            using True'(1) by simp
          moreover
          have "LTS_\<epsilon>.\<epsilon>_exp w1' w"
            by (metis (no_types) LTS_\<epsilon>.\<epsilon>_exp_def less(2) True'(1) removeAll.simps(2))
          moreover
          have "LTS_\<epsilon>.\<epsilon>_exp w2 w"
            by (metis (no_types) less(3))
          moreover
          have "(p', w1', p2) \<in> A1.trans_star"
            using p'_p by simp
          moreover
          have "(q1, w2, q2) \<in> A2.trans_star"
            using q'_p by simp
          ultimately
          show "((p', q1), w, p2, q2) \<in> pa.trans_star_\<epsilon>"
            using less(1)[of w1' w2 w p' q1] by auto
        qed
        moreover
        have "((p1, q1), \<epsilon>, (p', q1)) \<in> (inters_\<epsilon> ts1 ts2)"
          by (simp add: inters_\<epsilon>_def p'_p q'_p)
        ultimately
        have "((p1, q1), w, p2, q2) \<in> pa.trans_star_\<epsilon>"
          using LTS_\<epsilon>.trans_star_\<epsilon>.simps by fastforce
        then
        show ?thesis
           by force
      next
        case False
        note False_outer_outer = False
        then show ?thesis
        proof (cases "\<exists>w2'. w2 = \<epsilon> # w2'")
          case True (* Adapted from above. Maybe they can be merged. *)
          then obtain w2' where True':
            "w2=\<epsilon>#w2'"
            by auto
          have p'_p: "(p1, w1, p2) \<in> A1.trans_star"
            using less by (metis)
          obtain q' where q'_p: "(q1, \<epsilon>, q') \<in> ts2 \<and>(q', w2', q2) \<in> A2.trans_star"
            using less True'(1) by (metis LTS_\<epsilon>.trans_star_cons_\<epsilon>) 
          have ind: "((p1, q'), w, p2, q2) \<in> pa.trans_star_\<epsilon>"
          proof -
            have "length w1 + length w2' < length w1 + length w2"
              using True'(1) True'(1) by simp
            moreover
            have "LTS_\<epsilon>.\<epsilon>_exp w1 w"
              by (metis (no_types) less(2))
            moreover
            have "LTS_\<epsilon>.\<epsilon>_exp w2' w"
              by (metis (no_types) LTS_\<epsilon>.\<epsilon>_exp_def less(3) True'(1) removeAll.simps(2))
            moreover
            have "(p1, w1, p2) \<in> A1.trans_star"
              using p'_p by simp
            moreover
            have "(q', w2', q2) \<in> A2.trans_star"
              using q'_p by simp
            ultimately
            show "((p1, q'), w, p2, q2) \<in> pa.trans_star_\<epsilon>"
              using less(1)[of w1 w2' w p1 q'] by auto
          qed
          moreover
          have "((p1, q1), \<epsilon>, (p1, q')) \<in> inters_\<epsilon> ts1 ts2"
            by (simp add: inters_\<epsilon>_def p'_p q'_p)
          ultimately
          have "((p1, q1), w, p2, q2) \<in> pa.trans_star_\<epsilon>"
            using LTS_\<epsilon>.trans_star_\<epsilon>.simps by fastforce
          then
          show ?thesis
            by force
        next
          case False
          then have "(w1 = [] \<and> (\<exists>\<alpha> w2'. w2 = Some \<alpha> # w2')) \<or> ((\<exists>\<alpha> w1'. w1 = Some \<alpha> # w1') \<and> w2 = [])"
            using False_outer_outer False_outer_outer_outer False_outer_outer_outer_outer
            by (metis neq_Nil_conv option.exhaust_sel)
          then show ?thesis
            by (metis LTS_\<epsilon>.\<epsilon>_exp_def LTS_\<epsilon>.\<epsilon>_exp_Some_length less.prems(1) less.prems(2) 
                less_numeral_extra(3) list.simps(8) list.size(3) removeAll.simps(1))
        qed
      qed
    qed
  qed
qed

lemma trans_star_\<epsilon>_inter:
  assumes "(p1, w :: 'label list, p2) \<in> A1.trans_star_\<epsilon>"
  assumes "(q1, w, q2) \<in> A2.trans_star_\<epsilon>"
  shows "((p1, q1), w, (p2, q2)) \<in> pa.trans_star_\<epsilon>"
proof -
  have "\<exists>w1'. LTS_\<epsilon>.\<epsilon>_exp w1' w \<and> (p1, w1', p2) \<in> A1.trans_star"
    using assms by (simp add: LTS_\<epsilon>.trans_star_\<epsilon>_\<epsilon>_exp_trans_star)
  then obtain w1' where "LTS_\<epsilon>.\<epsilon>_exp w1' w \<and> (p1, w1', p2) \<in> A1.trans_star"
    by auto
  moreover
  have "\<exists>w2'. LTS_\<epsilon>.\<epsilon>_exp w2' w \<and> (q1, w2', q2) \<in> A2.trans_star"
    using assms by (simp add: LTS_\<epsilon>.trans_star_\<epsilon>_\<epsilon>_exp_trans_star)
  then obtain w2' where "LTS_\<epsilon>.\<epsilon>_exp w2' w \<and> (q1, w2', q2) \<in> A2.trans_star"
    by auto
  ultimately
  show ?thesis
    using trans_star_trans_star_\<epsilon>_inter by metis
qed

lemma inters_trans_star_\<epsilon>1:
  assumes "(p1q2, w :: 'label list, p2q2) \<in> pa.trans_star_\<epsilon>"
  shows "(fst p1q2, w, fst p2q2) \<in> A1.trans_star_\<epsilon>"
  using assms 
proof (induction rule: LTS_\<epsilon>.trans_star_\<epsilon>.induct[OF assms(1)])
  case (1 p)
  then show ?case
    by (simp add: LTS_\<epsilon>.trans_star_\<epsilon>.trans_star_\<epsilon>_refl)
next
  case (2 p \<gamma> q' w q)
  then have ind: "(fst q', w, fst q) \<in> A1.trans_star_\<epsilon>"
    by auto
  from 2(1) have "(p, Some \<gamma>, q') \<in> 
                     {((p1, q1), \<alpha>, p2, q2) |p1 q1 \<alpha> p2 q2. (p1, \<alpha>, p2) \<in> ts1 \<and> (q1, \<alpha>, q2) \<in> ts2} \<union> 
                     {((p1, q1), \<epsilon>, p2, q1) |p1 p2 q1. (p1, \<epsilon>, p2) \<in> ts1} \<union>
                     {((p1, q1), \<epsilon>, p1, q2) |p1 q1 q2. (q1, \<epsilon>, q2) \<in> ts1}"
    unfolding inters_\<epsilon>_def by auto
  moreover                
  {
    assume "(p, Some \<gamma>, q') \<in> {((p1, q1), \<alpha>, p2, q2) |p1 q1 \<alpha> p2 q2. (p1, \<alpha>, p2) \<in> ts1 \<and> (q1, \<alpha>, q2) \<in> ts2}"
    then have "\<exists>p1 q1. p = (p1, q1) \<and> (\<exists>p2 q2. q' = (p2, q2) \<and> (p1, Some \<gamma>, p2) \<in> ts1 \<and> (q1, Some \<gamma>, q2) \<in> ts2)"
      by simp
    then obtain p1 q1 where "p = (p1, q1) \<and> (\<exists>p2 q2. q' = (p2, q2) \<and> (p1, Some \<gamma>, p2) \<in> ts1 \<and> (q1, Some \<gamma>, q2) \<in> ts2)"
      by auto
    then have ?case
      using LTS_\<epsilon>.trans_star_\<epsilon>.trans_star_\<epsilon>_step_\<gamma> ind by fastforce
  }
  moreover
  {
    assume "(p, Some \<gamma>, q') \<in> {((p1, q1), \<epsilon>, p2, q1) |p1 p2 q1. (p1, \<epsilon>, p2) \<in> ts1}"
    then have ?case
      by auto
  }
  moreover
  {
    assume "(p, Some \<gamma>, q') \<in> {((p1, q1), \<epsilon>, p1, q2) |p1 q1 q2. (q1, \<epsilon>, q2) \<in> ts1}"
    then have ?case
      by auto
  }  
  ultimately 
  show ?case 
    by auto
next
  case (3 p q' w q)
  then have ind: "(fst q', w, fst q) \<in> A1.trans_star_\<epsilon>"
    by auto
  from 3(1) have "(p, \<epsilon>, q') \<in>
                     {((p1, q1), \<alpha>, (p2, q2)) | p1 q1 \<alpha> p2 q2. (p1, \<alpha>, p2) \<in> ts1 \<and> (q1, \<alpha>, q2) \<in> ts2} \<union>
                     {((p1, q1), \<epsilon>, (p2, q1)) | p1 p2 q1. (p1, \<epsilon>, p2) \<in> ts1} \<union>
                     {((p1, q1), \<epsilon>, (p1, q2)) | p1 q1 q2. (q1, \<epsilon>, q2) \<in> ts2}"
    unfolding inters_\<epsilon>_def by auto
  moreover                
  {
    assume "(p, \<epsilon>, q') \<in> {((p1, q1), \<alpha>, p2, q2) |p1 q1 \<alpha> p2 q2. (p1, \<alpha>, p2) \<in> ts1 \<and> (q1, \<alpha>, q2) \<in> ts2}"
    then have "\<exists>p1 q1. p = (p1, q1) \<and> (\<exists>p2 q2. q' = (p2, q2) \<and> (p1, \<epsilon>, p2) \<in> ts1 \<and> (q1, \<epsilon>, q2) \<in> ts2)"
      by simp
    then obtain p1 q1 where "p = (p1, q1) \<and> (\<exists>p2 q2. q' = (p2, q2) \<and> (p1, \<epsilon>, p2) \<in> ts1 \<and> (q1, \<epsilon>, q2) \<in> ts2)"
      by auto
    then have ?case
      using LTS_\<epsilon>.trans_star_\<epsilon>.trans_star_\<epsilon>_step_\<epsilon> ind by fastforce
  }
  moreover
  {
    assume "(p, \<epsilon>, q') \<in> {((p1, q1), \<epsilon>, p2, q1) |p1 p2 q1. (p1, \<epsilon>, p2) \<in> ts1}"
    then have "\<exists>p1 p2 q1. p = (p1, q1) \<and> q' = (p2, q1) \<and> (p1, \<epsilon>, p2) \<in> ts1"
      by auto
    then obtain p1 p2 q1 where "p = (p1, q1) \<and> q' = (p2, q1) \<and> (p1, \<epsilon>, p2) \<in> ts1"
      by auto
    then have ?case
      using LTS_\<epsilon>.trans_star_\<epsilon>.trans_star_\<epsilon>_step_\<epsilon> ind by fastforce
  }
  moreover
  {
    assume "(p, \<epsilon>, q') \<in> {((p1, q1), \<epsilon>, p1, q2) |p1 q1 q2. (q1, \<epsilon>, q2) \<in> ts2}"
    then have "\<exists>p1 q1 q2. p = (p1, q1) \<and> q' = (p1, q2) \<and> (q1, \<epsilon>, q2) \<in> ts2"
      by auto
    then obtain p1 q1 q2 where "p = (p1, q1) \<and> q' = (p1, q2) \<and> (q1, \<epsilon>, q2) \<in> ts2"
      by auto
    then have ?case
      using LTS_\<epsilon>.trans_star_\<epsilon>.trans_star_\<epsilon>_step_\<epsilon> ind by fastforce
  }  
  ultimately 
  show ?case 
    by auto
qed

lemma inters_trans_star_\<epsilon>:
  assumes "(p1q2, w :: 'label list, p2q2) \<in> pa.trans_star_\<epsilon>"
  shows "(snd p1q2, w, snd p2q2) \<in> A2.trans_star_\<epsilon>"
  using assms 
proof (induction rule: LTS_\<epsilon>.trans_star_\<epsilon>.induct[OF assms(1)])
  case (1 p)
  then show ?case
    by (simp add: LTS_\<epsilon>.trans_star_\<epsilon>.trans_star_\<epsilon>_refl) 
next
  case (2 p \<gamma> q' w q)
  then have ind: "(snd q', w, snd q) \<in> A2.trans_star_\<epsilon>"
    by auto
  from 2(1) have "(p, Some \<gamma>, q') \<in> 
                     {((p1, q1), \<alpha>, p2, q2) |p1 q1 \<alpha> p2 q2. (p1, \<alpha>, p2) \<in> ts1 \<and> (q1, \<alpha>, q2) \<in> ts2} \<union> 
                     {((p1, q1), \<epsilon>, p2, q1) |p1 p2 q1. (p1, \<epsilon>, p2) \<in> ts1} \<union>
                     {((p1, q1), \<epsilon>, p1, q2) |p1 q1 q2. (q1, \<epsilon>, q2) \<in> ts2}"
    unfolding inters_\<epsilon>_def by auto
  moreover                
  {
    assume "(p, Some \<gamma>, q') \<in> {((p1, q1), \<alpha>, p2, q2) |p1 q1 \<alpha> p2 q2. (p1, \<alpha>, p2) \<in> ts1 \<and> (q1, \<alpha>, q2) \<in> ts2}"
    then have "\<exists>p1 q1. p = (p1, q1) \<and> (\<exists>p2 q2. q' = (p2, q2) \<and> (p1, Some \<gamma>, p2) \<in> ts1 \<and> (q1, Some \<gamma>, q2) \<in> ts2)"
      by simp
    then obtain p1 q1 where "p = (p1, q1) \<and> (\<exists>p2 q2. q' = (p2, q2) \<and> (p1, Some \<gamma>, p2) \<in> ts1 \<and> (q1, Some \<gamma>, q2) \<in> ts2)"
      by auto
    then have ?case
      using LTS_\<epsilon>.trans_star_\<epsilon>.trans_star_\<epsilon>_step_\<gamma> ind by fastforce
  }
  moreover
  {
    assume "(p, Some \<gamma>, q') \<in> {((p1, q1), \<epsilon>, p2, q1) |p1 p2 q1. (p1, \<epsilon>, p2) \<in> ts1}"
    then have ?case
      by auto
  }
  moreover
  {
    assume "(p, Some \<gamma>, q') \<in> {((p1, q1), \<epsilon>, p1, q2) |p1 q1 q2. (q1, \<epsilon>, q2) \<in> ts2}"
    then have ?case
      by auto
  }  
  ultimately 
  show ?case 
    by auto
next
  case (3 p q' w q)
  then have ind: "(snd q', w, snd q) \<in> A2.trans_star_\<epsilon>"
    by auto
  from 3(1) have "(p, \<epsilon>, q') \<in>
                     {((p1, q1), \<alpha>, (p2, q2)) | p1 q1 \<alpha> p2 q2. (p1, \<alpha>, p2) \<in> ts1 \<and> (q1, \<alpha>, q2) \<in> ts2} \<union>
                     {((p1, q1), \<epsilon>, (p2, q1)) | p1 p2 q1. (p1, \<epsilon>, p2) \<in> ts1} \<union>
                     {((p1, q1), \<epsilon>, (p1, q2)) | p1 q1 q2. (q1, \<epsilon>, q2) \<in> ts2}"
    unfolding inters_\<epsilon>_def by auto
  moreover                
  {
    assume "(p, \<epsilon>, q') \<in> {((p1, q1), \<alpha>, p2, q2) |p1 q1 \<alpha> p2 q2. (p1, \<alpha>, p2) \<in> ts1 \<and> (q1, \<alpha>, q2) \<in> ts2}"
    then have "\<exists>p1 q1. p = (p1, q1) \<and> (\<exists>p2 q2. q' = (p2, q2) \<and> (p1, \<epsilon>, p2) \<in> ts1 \<and> (q1, \<epsilon>, q2) \<in> ts2)"
      by simp
    then obtain p1 q1 where "p = (p1, q1) \<and> (\<exists>p2 q2. q' = (p2, q2) \<and> (p1, \<epsilon>, p2) \<in> ts1 \<and> (q1, \<epsilon>, q2) \<in> ts2)"
      by auto
    then have ?case
      using LTS_\<epsilon>.trans_star_\<epsilon>.trans_star_\<epsilon>_step_\<epsilon> ind by fastforce
  }
  moreover
  {
    assume "(p, \<epsilon>, q') \<in> {((p1, q1), \<epsilon>, p2, q1) |p1 p2 q1. (p1, \<epsilon>, p2) \<in> ts1}"
    then have "\<exists>p1 p2 q1. p = (p1, q1) \<and> q' = (p2, q1) \<and> (p1, \<epsilon>, p2) \<in> ts1"
      by auto
    then obtain p1 p2 q1 where "p = (p1, q1) \<and> q' = (p2, q1) \<and> (p1, \<epsilon>, p2) \<in> ts1"
      by auto
    then have ?case
      using LTS_\<epsilon>.trans_star_\<epsilon>.trans_star_\<epsilon>_step_\<epsilon> ind by fastforce
  }
  moreover
  {
    assume "(p, \<epsilon>, q') \<in> {((p1, q1), \<epsilon>, p1, q2) |p1 q1 q2. (q1, \<epsilon>, q2) \<in> ts2}"
    then have "\<exists>p1 q1 q2. p = (p1, q1) \<and> q' = (p1, q2) \<and> (q1, \<epsilon>, q2) \<in> ts2"
      by auto
    then obtain p1 q1 q2 where "p = (p1, q1) \<and> q' = (p1, q2) \<and> (q1, \<epsilon>, q2) \<in> ts2"
      by auto
    then have ?case
      using LTS_\<epsilon>.trans_star_\<epsilon>.trans_star_\<epsilon>_step_\<epsilon> ind by fastforce
  }
  ultimately
  show ?case
    by auto
qed

lemma inters_trans_star_\<epsilon>_iff:
  "((p1,q2), w :: 'label list, (p2,q2)) \<in> pa.trans_star_\<epsilon> \<longleftrightarrow> 
   (p1, w, p2) \<in> A1.trans_star_\<epsilon> \<and> (q2, w, q2) \<in> A2.trans_star_\<epsilon>"
  by (metis fst_conv inters_trans_star_\<epsilon> inters_trans_star_\<epsilon>1 snd_conv trans_star_\<epsilon>_inter)

lemma inters_\<epsilon>_accept_\<epsilon>_iff: 
  "accepts_aut_inters_\<epsilon> p w \<longleftrightarrow> A1.accepts_aut_\<epsilon> p w \<and> A2.accepts_aut_\<epsilon> p w"
proof
  assume "accepts_aut_inters_\<epsilon> p w"
  then show "A1.accepts_aut_\<epsilon> p w \<and> A2.accepts_aut_\<epsilon> p w"
    unfolding accepts_aut_inters_\<epsilon>_def A1.accepts_aut_\<epsilon>_def A2.accepts_aut_\<epsilon>_def pa.accepts_aut_\<epsilon>_def 
    unfolding inters_finals_def 
    using inters_trans_star_\<epsilon>_iff[of _ _ w _ ]
    using SigmaE fst_conv inters_trans_star_\<epsilon> inters_trans_star_\<epsilon>1 snd_conv
    by (metis (no_types, lifting))
next
  assume a: "A1.accepts_aut_\<epsilon> p w \<and> A2.accepts_aut_\<epsilon> p w"
  then have "(\<exists>q\<in>finals1. (Init p, w, q) \<in> A1.trans_star_\<epsilon>) \<and> 
             (\<exists>q\<in>finals2. (Init p, w, q) \<in> LTS_\<epsilon>.trans_star_\<epsilon> ts2)" 
    unfolding A1.accepts_aut_\<epsilon>_def A2.accepts_aut_\<epsilon>_def by auto
  then show "accepts_aut_inters_\<epsilon> p w"
    unfolding accepts_aut_inters_\<epsilon>_def pa.accepts_aut_\<epsilon>_def inters_finals_def
    by (auto simp: P_Automaton_\<epsilon>.accepts_aut_\<epsilon>_def intro: trans_star_\<epsilon>_inter)
qed

lemma inters_\<epsilon>_lang_\<epsilon>: "lang_aut_inters_\<epsilon> = A1.lang_aut_\<epsilon> \<inter> A2.lang_aut_\<epsilon>"
  unfolding lang_aut_inters_\<epsilon>_def P_Automaton_\<epsilon>.lang_aut_\<epsilon>_def using inters_\<epsilon>_accept_\<epsilon>_iff by auto

end

end
