(*  Title:      JinjaThreads/Framework/FWBisimulation.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Bisimulation relations for the multithreaded semantics } *}

theory FWBisimulation imports
  FWProgressAux
  Bisimulation
  FWLifting
begin

subsection {* Definitions *}

primrec nta_bisim :: "('t \<Rightarrow> ('x1 \<times> 'm1, 'x2 \<times> 'm2) bisim) \<Rightarrow> (('t,'x1,'m1) new_thread_action, ('t,'x2,'m2) new_thread_action) bisim"
  where
  [code del]: "nta_bisim bisim (NewThread t x m) ta = (\<exists>x' m'. ta = NewThread t x' m' \<and> bisim t (x, m) (x', m'))"
| "nta_bisim bisim NewThreadFail ta = (ta = NewThreadFail)"
| "nta_bisim bisim (ThreadExists t) ta = (ta = ThreadExists t)"

lemma nta_bisim_1_code [code]:
  "nta_bisim bisim (NewThread t x m) ta = (case ta of NewThread t' x' m' \<Rightarrow> t = t' \<and> bisim t (x, m) (x', m') | _ \<Rightarrow> False)"
by(auto split: new_thread_action.split)
  
lemma nta_bisim_simps_sym [simp]:
  "nta_bisim bisim ta (NewThread t x m) = (\<exists>x' m'. ta = NewThread t x' m' \<and> bisim t (x', m') (x, m))"
  "nta_bisim bisim ta NewThreadFail = (ta = NewThreadFail)"
  "nta_bisim bisim ta (ThreadExists t) = (ta = ThreadExists t)"
by(cases ta, auto)+

definition ta_bisim :: "('t \<Rightarrow> ('x1 \<times> 'm1, 'x2 \<times> 'm2) bisim) \<Rightarrow> (('l,'t,'x1,'m1,'w,'o) thread_action, ('l,'t,'x2,'m2,'w,'o) thread_action) bisim"
where
  "ta_bisim bisim ta1 ta2 \<equiv>
  \<lbrace> ta1 \<rbrace>\<^bsub>l\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>l\<^esub> \<and> \<lbrace> ta1 \<rbrace>\<^bsub>w\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>w\<^esub> \<and> \<lbrace> ta1 \<rbrace>\<^bsub>c\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>c\<^esub> \<and> \<lbrace> ta1 \<rbrace>\<^bsub>o\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>o\<^esub> \<and> list_all2 (nta_bisim bisim) \<lbrace> ta1 \<rbrace>\<^bsub>t\<^esub> \<lbrace> ta2 \<rbrace>\<^bsub>t\<^esub>"

lemma ta_bisim_empty [iff]: "ta_bisim bisim \<epsilon> \<epsilon>"
by(auto simp add: ta_bisim_def)

lemma ta_bisim_\<epsilon> [simp]:
  "ta_bisim b \<epsilon> ta' \<longleftrightarrow> ta' = \<epsilon>" "ta_bisim b ta \<epsilon> \<longleftrightarrow> ta = \<epsilon>"
apply(cases ta', fastsimp simp add: ta_bisim_def)
apply(cases ta, fastsimp simp add: ta_bisim_def)
done

lemma nta_bisim_mono:
  assumes major: "nta_bisim bisim ta ta'"
  and mono: "\<And>t s1 s2. bisim t s1 s2 \<Longrightarrow> bisim' t s1 s2"
  shows "nta_bisim bisim' ta ta'"
using major by(cases ta)(auto intro: mono)

lemma ta_bisim_mono:
  assumes major: "ta_bisim bisim ta1 ta2"
  and mono: "\<And>t s1 s2. bisim t s1 s2 \<Longrightarrow> bisim' t s1 s2"
  shows "ta_bisim bisim' ta1 ta2"
using major
by(auto simp add: ta_bisim_def elim!: list_all2_mono nta_bisim_mono intro: mono)

lemma nta_bisim_flip [flip_simps]:
  "nta_bisim (\<lambda>t. flip (bisim t)) = flip (nta_bisim bisim)"
by(auto simp add: expand_fun_eq flip_simps nta_bisim_def new_thread_action_case_def[symmetric] split: new_thread_action.splits)

lemma ta_bisim_flip [flip_simps]:
  "ta_bisim (\<lambda>t. flip (bisim t)) = flip (ta_bisim bisim)"
by(auto simp add: expand_fun_eq flip_simps ta_bisim_def)

lemma ta_bisim_observable_ta_of [simp]:
  "ta_bisim bisim (observable_ta_of ta obs) (observable_ta_of ta' obs) = ta_bisim bisim ta ta'"
by(cases ta, cases ta')(simp add: observable_ta_of_def ta_bisim_def)

context multithreaded_base begin

definition can_Notified :: "'t \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool"
where "can_Notified t x m \<longleftrightarrow> (\<exists>x'. t \<turnstile> \<langle>x, m\<rangle> -\<epsilon>\<lbrace>\<^bsub>c\<^esub> Notified \<rbrace>\<rightarrow> \<langle>x', m\<rangle>)"

definition can_Interrupted :: "'t \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool"
where "can_Interrupted t x m \<longleftrightarrow> (\<exists>x'. t \<turnstile> \<langle>x, m\<rangle> -\<epsilon>\<lbrace>\<^bsub>c\<^esub> Interrupted \<rbrace>\<rightarrow> \<langle>x', m\<rangle>)"

end

locale FWbisimulation_base =
  r1!: multithreaded_base final1 r1 +
  r2!: multithreaded_base final2 r2 
  for final1 :: "'x1 \<Rightarrow> bool"
  and r1 :: "('l,'t,'x1,'m1,'w,'o) semantics" ("_ \<turnstile> _ -1-_\<rightarrow> _" [50, 0, 0, 50] 80)
  and final2 :: "'x2 \<Rightarrow> bool"
  and r2 :: "('l,'t,'x2,'m2,'w,'o) semantics" ("_ \<turnstile> _ -2-_\<rightarrow> _" [50, 0, 0, 50] 80) +
  fixes bisim :: "'t \<Rightarrow> ('x1 \<times> 'm1, 'x2 \<times> 'm2) bisim" ("_ \<turnstile> _/ \<approx> _" [50, 50, 50] 60)
  and bisim_wait :: "('x1, 'x2) bisim" ("_/ \<approx>w _" [50, 50] 60)
begin

notation r1.redT_syntax1 ("_ -1-_\<triangleright>_\<rightarrow> _" [50,0,0,50] 80)
notation r2.redT_syntax1 ("_ -2-_\<triangleright>_\<rightarrow> _" [50,0,0,50] 80)

notation r1.RedT ("_ -1-\<triangleright>_\<rightarrow>* _" [50,0,50] 80)
notation r2.RedT ("_ -2-\<triangleright>_\<rightarrow>* _" [50,0,50] 80)

notation r1.must_sync ("_ \<turnstile> \<langle>_,/ _\<rangle>/ \<wrong>1" [50,0,0] 81)
notation r2.must_sync ("_ \<turnstile> \<langle>_,/ _\<rangle>/ \<wrong>2" [50,0,0] 81)

notation r1.can_sync  ("_ \<turnstile> \<langle>_,/ _\<rangle>/ _/ \<wrong>1" [50,0,0,0] 81)
notation r2.can_sync  ("_ \<turnstile> \<langle>_,/ _\<rangle>/ _/ \<wrong>2" [50,0,0,0] 81)

abbreviation ta_bisim_bisim_syntax ("_/ \<sim>m _" [50, 50] 60)
where "ta1 \<sim>m ta2 \<equiv> ta_bisim bisim ta1 ta2"

lemma observable_ta_of_empty_ta_bisim_conv:
  "observable_ta_of \<epsilon> obs \<sim>m ta \<longleftrightarrow> ta = observable_ta_of \<epsilon> obs"
by(cases ta)(auto simp add: observable_ta_of_def ta_bisim_def)

lemma ta_bisim_observable_ta_of_empty_conv:
  "ta \<sim>m observable_ta_of \<epsilon> obs \<longleftrightarrow> ta = observable_ta_of \<epsilon> obs"
by(cases ta)(auto simp add: observable_ta_of_def ta_bisim_def)

definition tbisim :: "bool \<Rightarrow> 't \<Rightarrow> ('x1 \<times> 'l released_locks) option \<Rightarrow> 'm1 \<Rightarrow> ('x2 \<times> 'l released_locks) option \<Rightarrow> 'm2 \<Rightarrow> bool" where
  "tbisim nw t ts1 m1 ts2 m2 \<longleftrightarrow>
  (case ts1 of None \<Rightarrow> ts2 = None
       | \<lfloor>(x1, ln)\<rfloor> \<Rightarrow> (\<exists>x2. ts2 = \<lfloor>(x2, ln)\<rfloor> \<and> t \<turnstile> (x1, m1) \<approx> (x2, m2) \<and> (nw \<or> x1 \<approx>w x2)))"

lemma tbisim_NoneI: "tbisim w t None m None m'"
by(simp add: tbisim_def)

lemma tbisim_SomeI:
  "\<lbrakk> t \<turnstile> (x, m) \<approx> (x', m'); nw \<or> x \<approx>w x' \<rbrakk> \<Longrightarrow> tbisim nw t (Some (x, ln)) m (Some (x', ln)) m'"
by(simp add: tbisim_def)

lemma tbisim_cases[consumes 1, case_names None Some]:
  assumes major: "tbisim nw t ts1 m1 ts2 m2"
  obtains "ts1 = None" "ts2 = None"
        | x ln x' where "ts1 = \<lfloor>(x, ln)\<rfloor>" "ts2 = \<lfloor>(x', ln)\<rfloor>" "t \<turnstile> (x, m1) \<approx> (x', m2)" "nw \<or> x \<approx>w x'"
using major that
by(auto simp add: tbisim_def)

definition mbisim :: "(('l,'t,'x1,'m1,'w) state, ('l,'t,'x2,'m2,'w) state) bisim" ("_ \<approx>m _" [50, 50] 60)
where
  "s1 \<approx>m s2 \<equiv> 
  finite (dom (thr s1)) \<and> locks s1 = locks s2 \<and> wset s1 = wset s2 \<and> wset_thread_ok (wset s1) (thr s1) \<and>
  (\<forall>t. tbisim (wset s2 t = None) t (thr s1 t) (shr s1) (thr s2 t) (shr s2))"

lemma mbisim_thrNone_eq: "s1 \<approx>m s2 \<Longrightarrow> thr s1 t = None \<longleftrightarrow> thr s2 t = None"
unfolding mbisim_def tbisim_def
apply(clarify)
apply(erule allE[where x=t])
apply(clarsimp)
done

lemma mbisim_thrD1:
  "\<lbrakk> s1 \<approx>m s2; thr s1 t = \<lfloor>(x, ln)\<rfloor> \<rbrakk>
  \<Longrightarrow> \<exists>x'. thr s2 t = \<lfloor>(x', ln)\<rfloor> \<and> t \<turnstile> (x, shr s1) \<approx> (x', shr s2) \<and> (wset s1 t = None \<or> x \<approx>w x')"
by(fastsimp simp add: mbisim_def tbisim_def)

lemma mbisim_thrD2:
  "\<lbrakk> s1 \<approx>m s2; thr s2 t = \<lfloor>(x, ln)\<rfloor> \<rbrakk>
  \<Longrightarrow> \<exists>x'. thr s1 t = \<lfloor>(x', ln)\<rfloor> \<and> t \<turnstile> (x', shr s1) \<approx> (x, shr s2) \<and> (wset s2 t = None \<or> x' \<approx>w x)"
by(frule mbisim_thrNone_eq[where t=t])(cases "thr s1 t",(fastsimp simp add: mbisim_def tbisim_def)+)

lemma mbisim_dom_eq: "s1 \<approx>m s2 \<Longrightarrow> dom (thr s1) = dom (thr s2)"
apply(clarsimp simp add: dom_def Collect_def expand_fun_eq simp del: not_None_eq)
apply(erule mbisim_thrNone_eq)
done

lemma mbisim_wset_thread_ok1:
  "s1 \<approx>m s2 \<Longrightarrow> wset_thread_ok (wset s1) (thr s1)"
by(clarsimp simp add: mbisim_def)

lemma mbisim_wset_thread_ok2:
  assumes "s1 \<approx>m s2"
  shows "wset_thread_ok (wset s2) (thr s2)"
using assms
apply(clarsimp simp add: mbisim_def)
apply(auto intro!: wset_thread_okI simp add: mbisim_thrNone_eq[OF assms, THEN sym] dest: wset_thread_okD)
done

lemma mbisimI:
  "\<lbrakk> finite (dom (thr s1)); locks s1 = locks s2; wset s1 = wset s2; wset_thread_ok (wset s1) (thr s1);
     \<And>t. thr s1 t = None \<Longrightarrow> thr s2 t = None;
     \<And>t x1 ln. thr s1 t = \<lfloor>(x1, ln)\<rfloor> \<Longrightarrow> \<exists>x2. thr s2 t = \<lfloor>(x2, ln)\<rfloor> \<and> t \<turnstile> (x1, shr s1) \<approx> (x2, shr s2) \<and> (wset s2 t = None \<or> x1 \<approx>w x2) \<rbrakk>
  \<Longrightarrow> s1 \<approx>m s2"
by(fastsimp simp add: mbisim_def tbisim_def)

lemma mbisimI2:
  "\<lbrakk> finite (dom (thr s2)); locks s1 = locks s2; wset s1 = wset s2; wset_thread_ok (wset s2) (thr s2);
     \<And>t. thr s2 t = None \<Longrightarrow> thr s1 t = None;
     \<And>t x2 ln. thr s2 t = \<lfloor>(x2, ln)\<rfloor> \<Longrightarrow> \<exists>x1. thr s1 t = \<lfloor>(x1, ln)\<rfloor> \<and> t \<turnstile> (x1, shr s1) \<approx> (x2, shr s2) \<and> (wset s2 t = None \<or> x1 \<approx>w x2) \<rbrakk>
  \<Longrightarrow> s1 \<approx>m s2"
apply(auto simp add: mbisim_def tbisim_def)
   prefer 2
   apply(rule wset_thread_okI)
   apply(case_tac "thr s2 t")
   apply(auto dest!: wset_thread_okD)[2]
   apply fastsimp
  apply(erule back_subst[where P=finite])
  apply(clarsimp simp add: dom_def Collect_def expand_fun_eq simp del: not_None_eq)
  apply(rename_tac t)
apply(case_tac [!] "thr s2 t")
by fastsimp+

lemma mbisim_finite1:
  "s1 \<approx>m s2 \<Longrightarrow> finite (dom (thr s1))"
by(simp add: mbisim_def)

lemma mbisim_finite2:
  "s1 \<approx>m s2 \<Longrightarrow> finite (dom (thr s2))"
by(frule mbisim_finite1)(simp add: mbisim_dom_eq)

definition mta_bisim :: "('t \<times> ('l,'t,'x1,'m1,'w,('l,'o) observable list) thread_action,
                       't \<times> ('l,'t,'x2,'m2,'w,('l,'o) observable list) thread_action) bisim"
  ("_/ \<sim>T _" [50, 50] 60)
where "tta1 \<sim>T tta2 \<equiv> fst tta1 = fst tta2 \<and> snd tta1 \<sim>m snd tta2"

lemma mta_bisim_conv [simp]: "(t, ta1) \<sim>T (t', ta2) \<longleftrightarrow> t = t' \<and> ta1 \<sim>m ta2"
by(simp add: mta_bisim_def)

definition bisim_inv :: "bool" where
  "bisim_inv \<equiv> (\<forall>s1 ta1 s1' s2 t. t \<turnstile> s1 \<approx> s2 \<longrightarrow> t \<turnstile> s1 -1-ta1\<rightarrow> s1' \<longrightarrow> (\<exists>s2'. t \<turnstile> s1' \<approx> s2')) \<and>
               (\<forall>s2 ta2 s2' s1 t. t \<turnstile> s1 \<approx> s2 \<longrightarrow> t \<turnstile> s2 -2-ta2\<rightarrow> s2' \<longrightarrow> (\<exists>s1'. t \<turnstile> s1' \<approx> s2'))"

lemma bisim_invI:
  "\<lbrakk> \<And>s1 ta1 s1' s2 t. \<lbrakk> t \<turnstile> s1 \<approx> s2; t \<turnstile> s1 -1-ta1\<rightarrow> s1' \<rbrakk> \<Longrightarrow> \<exists>s2'. t \<turnstile> s1' \<approx> s2';
     \<And>s2 ta2 s2' s1 t. \<lbrakk> t \<turnstile> s1 \<approx> s2; t \<turnstile> s2 -2-ta2\<rightarrow> s2' \<rbrakk> \<Longrightarrow> \<exists>s1'. t \<turnstile> s1' \<approx> s2' \<rbrakk>
  \<Longrightarrow> bisim_inv"
by(auto simp add: bisim_inv_def)

lemma bisim_invD1:
  "\<lbrakk> bisim_inv; t \<turnstile> s1 \<approx> s2; t \<turnstile> s1 -1-ta1\<rightarrow> s1' \<rbrakk> \<Longrightarrow> \<exists>s2'. t \<turnstile> s1' \<approx> s2'"
unfolding bisim_inv_def by blast

lemma bisim_invD2:
  "\<lbrakk> bisim_inv; t \<turnstile> s1 \<approx> s2; t \<turnstile> s2 -2-ta2\<rightarrow> s2' \<rbrakk> \<Longrightarrow> \<exists>s1'. t \<turnstile> s1' \<approx> s2'"
unfolding bisim_inv_def by blast

lemma thread_oks_bisim_inv:
  "\<lbrakk> \<forall>t. ts1 t = None \<longleftrightarrow> ts2 t = None; list_all2 (nta_bisim bisim) tas1 tas2 \<rbrakk>
  \<Longrightarrow> thread_oks ts1 tas1 \<longleftrightarrow> thread_oks ts2 tas2"
proof(induct tas2 arbitrary: tas1 ts1 ts2)
  case Nil thus ?case by(simp)
next
  case (Cons ta2 TAS2 tas1 TS1 TS2)
  note IH = `\<And>ts1 tas1 ts2. \<lbrakk> \<forall>t. ts1 t = None \<longleftrightarrow> ts2 t = None; list_all2 (nta_bisim bisim) tas1 TAS2 \<rbrakk>
             \<Longrightarrow> thread_oks ts1 tas1 \<longleftrightarrow> thread_oks ts2 TAS2`
  note eqNone = `\<forall>t. TS1 t = None \<longleftrightarrow> TS2 t = None`[rule_format]
  hence fti: "free_thread_id TS1 = free_thread_id TS2" by(auto simp add: free_thread_id_def)
  from `list_all2 (nta_bisim bisim) tas1 (ta2 # TAS2)`
  obtain ta1 TAS1 where "tas1 = ta1 # TAS1" "nta_bisim bisim ta1 ta2" "list_all2 (nta_bisim bisim) TAS1 TAS2"
    by(auto simp add: list_all2_Cons2)
  moreover
  { fix t
    from `nta_bisim bisim ta1 ta2` have "redT_updT' TS1 ta1 t = None \<longleftrightarrow> redT_updT' TS2 ta2 t = None"
      by(cases ta1, auto split: split_if_asm simp add: eqNone) }
  ultimately have "thread_oks (redT_updT' TS1 ta1) TAS1 \<longleftrightarrow> thread_oks (redT_updT' TS2 ta2) TAS2"
    by -(rule IH, auto)
  moreover from `nta_bisim bisim ta1 ta2` fti have "thread_ok TS1 ta1 = thread_ok TS2 ta2" by(cases ta1, auto)
  ultimately show ?case using `tas1 = ta1 # TAS1` by auto
qed

lemma redT_updT_nta_bisim_inv:
  "\<lbrakk> nta_bisim bisim ta1 ta2; ts1 T = None \<longleftrightarrow> ts2 T = None \<rbrakk> \<Longrightarrow> redT_updT ts1 ta1 T = None \<longleftrightarrow> redT_updT ts2 ta2 T = None"
by(cases ta1, auto)

lemma redT_updTs_nta_bisim_inv:
  "\<lbrakk> list_all2 (nta_bisim bisim) tas1 tas2; ts1 T = None \<longleftrightarrow> ts2 T = None \<rbrakk>
  \<Longrightarrow> redT_updTs ts1 tas1 T = None \<longleftrightarrow> redT_updTs ts2 tas2 T = None"
proof(induct tas1 arbitrary: tas2 ts1 ts2)
  case Nil thus ?case by(simp)
next
  case (Cons TA1 TAS1 tas2 TS1 TS2)
  note IH = `\<And>tas2 ts1 ts2. \<lbrakk>list_all2 (nta_bisim bisim) TAS1 tas2; (ts1 T = None) = (ts2 T = None)\<rbrakk>
            \<Longrightarrow> (redT_updTs ts1 TAS1 T = None) = (redT_updTs ts2 tas2 T = None)`
  from `list_all2 (nta_bisim bisim) (TA1 # TAS1) tas2`
  obtain TA2 TAS2 where "tas2 = TA2 # TAS2" "nta_bisim bisim TA1 TA2" "list_all2 (nta_bisim bisim) TAS1 TAS2"
    by(auto simp add: list_all2_Cons1)
  from `nta_bisim bisim TA1 TA2` `(TS1 T = None) = (TS2 T = None)`
  have "redT_updT TS1 TA1 T = None \<longleftrightarrow> redT_updT TS2 TA2 T = None"
    by(rule redT_updT_nta_bisim_inv)
  with IH[OF `list_all2 (nta_bisim bisim) TAS1 TAS2`, of "redT_updT TS1 TA1" "redT_updT TS2 TA2"] `tas2 = TA2 # TAS2`
  show ?case by simp
qed

end

lemma tbisim_flip [flip_simps]:
  "FWbisimulation_base.tbisim (\<lambda>t. flip (bisim t)) (flip bisim_wait) w t ts2 m2 ts1 m1 =
   FWbisimulation_base.tbisim bisim bisim_wait w t ts1 m1 ts2 m2"
unfolding FWbisimulation_base.tbisim_def flip_simps by auto

lemma mbisim_flip [flip_simps]:
  "FWbisimulation_base.mbisim (\<lambda>t. flip (bisim t)) (flip bisim_wait) s2 s1 =
   FWbisimulation_base.mbisim bisim bisim_wait s1 s2"
apply(rule iffI)
 apply(frule FWbisimulation_base.mbisim_dom_eq)
 apply(frule FWbisimulation_base.mbisim_wset_thread_ok2)
 apply(fastsimp simp add: FWbisimulation_base.mbisim_def flip_simps)
apply(frule FWbisimulation_base.mbisim_dom_eq)
apply(frule FWbisimulation_base.mbisim_wset_thread_ok2)
apply(fastsimp simp add: FWbisimulation_base.mbisim_def flip_simps)
done

lemma mta_bisim_flip [flip_simps]:
  "FWbisimulation_base.mta_bisim (\<lambda>t. flip (bisim t)) = flip (FWbisimulation_base.mta_bisim bisim)"
by(auto simp add: expand_fun_eq flip_simps FWbisimulation_base.mta_bisim_def)

lemma flip_const [simp]: "flip (\<lambda>a b. c) = (\<lambda>a b. c)"
by(rule flip_def)

lemma mbisim_K_flip [flip_simps]:
  "FWbisimulation_base.mbisim (\<lambda>t. flip (bisim t)) (\<lambda>x1 x2. c) s1 s2 = 
   FWbisimulation_base.mbisim bisim (\<lambda>x1 x2. c) s2 s1"
using mbisim_flip[of bisim "\<lambda>x1 x2. c" s1 s2]
unfolding flip_const . 

locale FWbisimulation_base_aux = FWbisimulation_base +
  r1!: multithreaded final1 r1 +
  r2!: multithreaded final2 r2 +
  constrains final1 :: "'x1 \<Rightarrow> bool"
  and r1 :: "('l,'t,'x1,'m1,'w, 'o) semantics"
  and final2 :: "'x2 \<Rightarrow> bool"
  and r2 :: "('l,'t,'x2,'m2,'w, 'o) semantics"
  and bisim :: "'t \<Rightarrow> ('x1 \<times> 'm1, 'x2 \<times> 'm2) bisim"
  and bisim_wait :: "('x1, 'x2) bisim"
begin

lemma FWbisimulation_base_aux_flip:
  "FWbisimulation_base_aux r2 r1"
by(unfold_locales)

end

lemma FWbisimulation_base_aux_flip_simps [flip_simps]:
  "FWbisimulation_base_aux r2 r1 = FWbisimulation_base_aux r1 r2"
by(blast intro: FWbisimulation_base_aux.FWbisimulation_base_aux_flip)

sublocale FWbisimulation_base_aux < mthr!: bisimulation_final_base r1.redT r2.redT mbisim mta_bisim r1.mfinal r2.mfinal
.

subsection {* The multithreaded semantics with internal actions *}

types
  ('l,'t,'x,'m,'w,'o) \<tau>moves =
    "'x \<times> 'm \<Rightarrow> ('l,'t,'x,'m,'w,'o list) thread_action \<Rightarrow> 'x \<times> 'm \<Rightarrow> bool"

text {* pretty printing for @{text "\<tau>moves"} *}
print_translation {*
  let
    fun tr' [(Const (@{type_syntax "*"}, _) $ x1 $ m1),
             (Const (@{type_syntax "fun"}, _) $
               (Const (@{type_syntax "*"}, _) $ 
                 (Const (@{type_syntax "finfun"}, _) $ l $ 
                   (Const (@{type_syntax "list"}, _) $ Const (@{type_syntax "lock_action"}, _))) $
                 (Const (@{type_syntax "*"},_) $ 
                   (Const (@{type_syntax "list"}, _) $ (Const (@{type_syntax "new_thread_action"}, _) $ t1 $ x2 $ m2)) $
                   (Const (@{type_syntax "*"}, _) $ 
                     (Const (@{type_syntax "list"}, _) $ (Const (@{type_syntax "conditional_action"}, _) $ t2)) $
                     (Const (@{type_syntax "*"}, _) $ 
                       (Const (@{type_syntax "list"}, _) $ (Const (@{type_syntax "wait_set_action"}, _) $ t3 $ w)) $
                       (Const (@{type_syntax "list"}, _) $ o1))))) $
               (Const (@{type_syntax "fun"}, _) $ 
                 (Const (@{type_syntax "*"}, _) $ x3 $ m3) $
                 (Const (@{type_syntax "bool"}, _))))] =
      if x1 = x2 andalso x1 = x3 andalso m1 = m2 andalso m1 = m3 andalso t1 = t2 andalso t2 = t3
      then Syntax.const (@{type_syntax "\<tau>moves"}) $ l $ t1 $ x1 $ m1 $ w $ o1
      else raise Match;
  in [(@{type_syntax "fun"},tr')]
  end
*}
(* typ "('l,'t,'x,'m,'w,'o) \<tau>moves" *)

locale \<tau>multithreaded = multithreaded_base +
  constrains final :: "'x \<Rightarrow> bool"
  and r :: "('l,'t,'x,'m,'w,'o) semantics"
  fixes \<tau>move :: "('l,'t,'x,'m,'w,'o) \<tau>moves"

sublocale \<tau>multithreaded < \<tau>trsys "r t" \<tau>move for t
.

context \<tau>multithreaded begin

inductive m\<tau>move :: "(('l,'t,'x,'m,'w) state, 't \<times> ('l,'t,'x,'m,'w,('l,'o) observable list) thread_action) trsys"
where
  "\<lbrakk> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; thr s' t = \<lfloor>(x', ln')\<rfloor>; \<tau>move (x, shr s) ta (x', shr s') \<rbrakk>
  \<Longrightarrow> m\<tau>move s (t, observable_ta_of ta []) s'"

end

sublocale \<tau>multithreaded < mthr!: \<tau>trsys redT m\<tau>move .

context \<tau>multithreaded begin

abbreviation \<tau>mredT :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> bool"
where "\<tau>mredT == mthr.silent_move"

end

lemma (in multithreaded_base) \<tau>rtrancl3p_redT_thread_not_disappear:
  assumes "\<tau>trsys.\<tau>rtrancl3p redT \<tau>move s ttas s'" "thr s t \<noteq> None"
  shows "thr s' t \<noteq> None"
proof -
  interpret T: \<tau>trsys redT \<tau>move .
  show ?thesis
  proof
    assume "thr s' t = None"
    with `\<tau>trsys.\<tau>rtrancl3p redT \<tau>move s ttas s'` have "thr s t = None"
      by(induct rule: T.\<tau>rtrancl3p.induct)(auto simp add: split_paired_all dest: redT_thread_not_disappear)
    with `thr s t \<noteq> None` show False by contradiction
  qed
qed

lemma m\<tau>move_False: "\<tau>multithreaded.m\<tau>move (\<lambda>s ta s'. False) = (\<lambda>s ta s'. False)"
by(auto intro!: ext elim: \<tau>multithreaded.m\<tau>move.cases)

locale \<tau>multithreaded_wf =
  \<tau>multithreaded _ _ \<tau>move +
  final_thread_wf final r
  for \<tau>move :: "('l,'t,'x,'m,'w,'o) \<tau>moves" +
  fixes wfs :: "'t \<Rightarrow> 'x \<times> 'm \<Rightarrow> bool"
  assumes \<tau>move_heap: "\<lbrakk> wfs t (x, m); t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); \<tau>move (x, m) ta (x', m') \<rbrakk> \<Longrightarrow> m = m'"
  assumes silent_tl: "\<tau>move s ta s' \<Longrightarrow> ta = \<epsilon>"
begin

lemma m\<tau>move_silentD: "m\<tau>move s (t, ta) s' \<Longrightarrow> ta = (\<lambda>\<^isup>f [], [], [], [], [])"
by(auto elim!: m\<tau>move.cases dest: silent_tl simp add: observable_ta_of_def)

lemma \<tau>mredT_thread_preserved:
  "\<tau>mredT s s' \<Longrightarrow> thr s t = None \<longleftrightarrow> thr s' t = None"
by(auto simp add: mthr.silent_move_iff observable_ta_of_def
        elim!: redT.cases dest!: m\<tau>move_silentD redTWs_thr_None split: split_if_asm)

lemma \<tau>mRedT_thread_preserved:
  "\<tau>mredT^** s s' \<Longrightarrow> thr s t = None \<longleftrightarrow> thr s' t = None"
by(induct rule: rtranclp.induct)(auto dest: \<tau>mredT_thread_preserved[where t=t])

lemma \<tau>mtRedT_thread_preserved:
  "\<tau>mredT^++ s s' \<Longrightarrow> thr s t = None \<longleftrightarrow> thr s' t = None"
by(induct rule: tranclp.induct)(auto dest: \<tau>mredT_thread_preserved[where t=t])

lemma \<tau>mredT_add_thread_inv:
  assumes \<tau>red: "\<tau>mredT s s'" and tst: "thr s t = None"
  shows "\<tau>mredT (locks s, ((thr s)(t \<mapsto> xln), shr s), wset s) (locks s', ((thr s')(t \<mapsto> xln), shr s'), wset s')"
proof -
  obtain ls ts m ws where s: "s = (ls, (ts, m), ws)" by(cases s) auto
  obtain ls' ts' m' ws' where s': "s' = (ls', (ts', m'), ws')" by(cases s') auto
  from \<tau>red s s' obtain t' where red: "(ls, (ts, m), ws) -t'\<triangleright>(\<lambda>\<^isup>f [], [], [], [], [])\<rightarrow> (ls', (ts', m'), ws')"
    and \<tau>: "m\<tau>move (ls, (ts, m), ws) (t', \<lambda>\<^isup>f [], [], [], [], []) (ls', (ts', m'), ws')"
    by(auto simp add: mthr.silent_move_iff dest: m\<tau>move_silentD)
  from red have "(ls, (ts(t \<mapsto> xln), m), ws) -t'\<triangleright>observable_ta_of \<epsilon> []\<rightarrow> (ls', (ts'(t \<mapsto> xln), m'), ws')"
  proof(cases rule: redT_elims)
    case (normal x x' ta' m') with tst s show ?thesis
      by(cases ta')(rule redT_normal, auto simp add: fun_upd_twist observable_ta_of_def elim!: rtrancl3p_cases)
  next
    case acquire with tst s have False by auto
    thus ?thesis ..
  qed
  moreover from red tst s have tt': "t \<noteq> t'" by(cases) auto
  have "(\<lambda>t''. (ts(t \<mapsto> xln)) t'' \<noteq> None \<and> (ts(t \<mapsto> xln)) t'' \<noteq> (ts'(t \<mapsto> xln)) t'') =
        (\<lambda>t''. ts t'' \<noteq> None \<and> ts t'' \<noteq> ts' t'')" using tst s by(auto simp add: expand_fun_eq)
  with \<tau> tst tt' have "m\<tau>move (ls, (ts(t \<mapsto> xln), m), ws) (t', observable_ta_of \<epsilon> []) (ls', (ts'(t \<mapsto> xln), m'), ws')"
    by cases(rule m\<tau>move.intros, auto simp add: observable_ta_of_def)
  ultimately show ?thesis unfolding s s' by auto
qed

lemma \<tau>mRedT_add_thread_inv:
  "\<lbrakk> \<tau>mredT^** s s'; thr s t = None \<rbrakk>
  \<Longrightarrow> \<tau>mredT^** (locks s, ((thr s)(t \<mapsto> xln), shr s), wset s) (locks s', ((thr s')(t \<mapsto> xln), shr s'), wset s')"
apply(induct rule: rtranclp_induct)
apply(blast dest: \<tau>mRedT_thread_preserved[where t=t] \<tau>mredT_add_thread_inv[where xln=xln] intro: rtranclp.rtrancl_into_rtrancl)+
done

lemma \<tau>mtRed_add_thread_inv:
  "\<lbrakk> \<tau>mredT^++ s s'; thr s t = None \<rbrakk>
  \<Longrightarrow> \<tau>mredT^++ (locks s, ((thr s)(t \<mapsto> xln), shr s), wset s) (locks s', ((thr s')(t \<mapsto> xln), shr s'), wset s')"
apply(induct rule: tranclp_induct)
apply(blast dest: \<tau>mtRedT_thread_preserved[where t=t] \<tau>mredT_add_thread_inv[where xln=xln] intro: tranclp.trancl_into_trancl)+
done

definition wfs_inv :: "bool" where
  "wfs_inv \<equiv> (\<forall>s ta s' t. wfs t s \<longrightarrow> t \<turnstile> s -ta\<rightarrow> s' \<longrightarrow> wfs t s')"

lemma wfs_invI:
  "(\<And>s ta s' t. \<lbrakk> wfs t s; t \<turnstile> s -ta\<rightarrow> s' \<rbrakk> \<Longrightarrow> wfs t s')
  \<Longrightarrow> wfs_inv"
by(auto simp add: wfs_inv_def)

lemma wfs_invD:
  "\<lbrakk> wfs_inv; wfs t s; t \<turnstile> s -ta\<rightarrow> s' \<rbrakk> \<Longrightarrow> wfs t s'"
unfolding wfs_inv_def by blast

lemma wfs_inv_\<tau>s_inv:
  assumes inv: "wfs_inv" and wfs: "wfs t s"
  and red: "silent_moves t s s'"
  shows "wfs t s'"
using red wfs
by(induct rule: rtranclp_induct)(fastsimp elim: wfs_invD[OF inv])+

lemma wfs_inv_trancl_inv:
  assumes inv: "wfs_inv" and wfs: "wfs t s"
  and red: "silent_movet t s s'"
  shows "wfs t s'"
using red wfs
by(induct rule: tranclp_induct)(fastsimp simp add: silent_move_iff elim: wfs_invD[OF inv])+


declare split_paired_Ex [simp del]

lemma silent_move_into_RedT_\<tau>_inv:
  assumes move: "silent_move t (x, shr s) (x', m')"
  and wfs: "wfs t (x, shr s)"
  and state: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "wset s t = None"
  shows "\<tau>mredT s (redT_upd s t \<epsilon> x' m')"
proof -
  from move obtain red: "t \<turnstile> (x, shr s) -\<epsilon>\<rightarrow> (x', m')" and \<tau>: "\<tau>move (x, shr s) \<epsilon> (x', m')"
    by(auto simp add: silent_move_iff dest: silent_tl)
  from red state have "s -t\<triangleright>observable_ta_of \<epsilon> []\<rightarrow> redT_upd s t \<epsilon> x' m'"
    by -(rule redT_normal, auto simp add: redT_updLns_def redT_updLs_def o_def finfun_Diag_const2)
  moreover from \<tau> red state have "m\<tau>move s (t, observable_ta_of \<epsilon> []) (redT_upd s t \<epsilon> x' m')"
    by -(rule m\<tau>move.intros, auto dest: \<tau>move_heap[OF wfs] simp add: redT_updLns_def o_def finfun_Diag_const2)
  ultimately show ?thesis by auto
qed

lemma silent_moves_into_RedT_\<tau>_inv:
  assumes inv: "wfs_inv"
  and major: "silent_moves t (x, shr s) (x', m')"
  and bisim: "wfs t (x, shr s)"
  and state: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "wset s t = None"
  shows "\<tau>mredT^** s (redT_upd s t \<epsilon> x' m')"
using major bisim
proof(induct rule: rtranclp_induct2)
  case refl with state show ?case
    by(cases s)(auto simp add: redT_updLs_def redT_updLns_def fun_upd_idem o_def finfun_Diag_const2)
next
  case (step x' m' x'' m'')
  note IH = `wfs t (x, shr s) \<Longrightarrow> \<tau>mredT^** s (redT_upd s t \<epsilon> x' m')`
  from `wfs t (x, shr s)` `silent_moves t (x, shr s) (x', m')`
  have wfs': "wfs t (x', m')" by(rule wfs_inv_\<tau>s_inv[OF inv])
  with `silent_move t (x', m') (x'', m'')` state
  have "\<tau>mredT (redT_upd s t (\<epsilon> :: ('l,'t,'x,'m,'w,'o list) thread_action) x' m') 
               (redT_upd (redT_upd s t (\<epsilon> :: ('l,'t,'x,'m,'w,'o list) thread_action) x' m') t \<epsilon> x'' m'')"
    by -(rule silent_move_into_RedT_\<tau>_inv, auto simp add: redT_updLns_def redT_updLs_def o_def finfun_Diag_const2)
  hence "\<tau>mredT (redT_upd s t \<epsilon> x' m') (redT_upd s t \<epsilon> x'' m'')"
    by(simp add: redT_updLns_def)
  with IH[OF `wfs t (x, shr s)`] show ?case ..
qed

lemma red_rtrancl_\<tau>_heapD_inv:
  assumes inv: "wfs_inv"
  shows "\<lbrakk> silent_moves t s s'; wfs t s \<rbrakk> \<Longrightarrow> snd s' = snd s"
proof(induct rule: rtranclp_induct)
  case base show ?case ..
next
  case (step s' s'')
  thus ?case by(cases s, cases s', cases s'')(auto dest: \<tau>move_heap  wfs_inv_\<tau>s_inv[OF inv])
qed

lemma red_trancl_\<tau>_heapD_inv:
  assumes inv: "wfs_inv"
  shows "\<lbrakk> silent_movet t s s'; wfs t s \<rbrakk> \<Longrightarrow> snd s' = snd s"
proof(induct rule: tranclp_induct)
  case (base s') thus ?case by(cases s')(cases s, auto simp add: silent_move_iff dest: \<tau>move_heap)
next
  case (step s' s'')
  thus ?case by(cases s, cases s', cases s'')(auto simp add: silent_move_iff dest: \<tau>move_heap wfs_inv_trancl_inv[OF inv])
qed

lemma red_trancl_\<tau>_into_RedT_\<tau>_inv:
  assumes inv: "wfs_inv"
  and major: "silent_movet t (x, shr s) (x', m')"
  and bisim: "wfs t (x, shr s)"
  and state: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "wset s t = None"
  shows "\<tau>mredT^++ s (redT_upd s t (\<epsilon> :: ('l, 't, 'x, 'm, 'w, 'o list) thread_action) x' m')"
using major bisim
proof(induct rule: tranclp_induct2)
  case (base x' m')
  thus ?case using state
    by -(rule tranclp.r_into_trancl, rule silent_move_into_RedT_\<tau>_inv, auto)
next
  case (step x' m' x'' m'')
  hence "\<tau>mredT^++ s (redT_upd s t (\<epsilon> :: ('l, 't, 'x, 'm, 'w, 'o list) thread_action) x' m')" by blast
  moreover from `wfs t (x, shr s)` `silent_movet t (x, shr s) (x', m')`
  have wfs': "wfs t (x', m')" by(rule wfs_inv_trancl_inv[OF inv])
  with `silent_move t (x', m') (x'', m'')` state
  have "\<tau>mredT (redT_upd s t (\<epsilon> :: ('l,'t,'x,'m,'w,'o list) thread_action) x' m') 
               (redT_upd (redT_upd s t (\<epsilon> :: ('l,'t,'x,'m,'w,'o list) thread_action) x' m') t \<epsilon> x'' m'')"
    by -(rule silent_move_into_RedT_\<tau>_inv, auto simp add: redT_updLns_def redT_updLs_def o_def finfun_Diag_const2)
  hence "\<tau>mredT (redT_upd s t \<epsilon> x' m') (redT_upd s t \<epsilon> x'' m'')"
    by(simp add: redT_updLns_def)
  ultimately show ?case ..
qed

lemma \<tau>diverge_into_\<tau>mredT:
  assumes "wfs_inv"
  and "\<tau>diverge t (x, shr s)"
  and "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "wset s t = None"
  and "wfs t (x, shr s)"
  shows "mthr.\<tau>diverge s"
proof -
  from assms have "\<exists>x. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> wfs t (x, shr s) \<and> \<tau>diverge t (x, shr s) \<and> wset s t = None" by blast
  thus ?thesis
  proof(coinduct)
    case (\<tau>diverge s)
    then obtain x where tst: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" and "\<tau>diverge t (x, shr s)" 
      and "wset s t = None" and "wfs t (x, shr s)" by blast
    from `\<tau>diverge t (x, shr s)` obtain x' m' where "silent_move t (x, shr s) (x', m')" 
      and "\<tau>diverge t (x', m')" by cases auto
    from `silent_move t (x, shr s) (x', m')` `wfs t (x, shr s)` tst `wset s t = None`
    have "\<tau>mredT s (redT_upd s t \<epsilon> x' m')" by(rule silent_move_into_RedT_\<tau>_inv)
    moreover have "thr (redT_upd s t \<epsilon> x' m') t = \<lfloor>(x', no_wait_locks)\<rfloor>"
      using tst by(auto simp add: redT_updLns_def redT_updLs_def o_def finfun_Diag_const2)
    moreover have "wset (redT_upd s t \<epsilon> x' m') t = None" using `wset s t = None` by simp
    moreover from `wfs t (x, shr s)` `silent_move t (x, shr s) (x', m')`
    have "wfs t (x', shr (redT_upd s t \<epsilon> x' m'))" by(auto intro: wfs_invD[OF `wfs_inv`])
    moreover from `\<tau>diverge t (x', m')` have "\<tau>diverge t (x', shr (redT_upd s t \<epsilon> x' m'))" by simp
    ultimately show ?case using `\<tau>diverge t (x', m')` by blast
  qed
qed

lemma \<tau>diverge_\<tau>mredTD:
  assumes wfs_inv
  and div: "mthr.\<tau>diverge s"
  and fin: "finite (dom (thr s))"
  and wfs: "ts_ok (\<lambda>t x m. wfs t (x, m)) (thr s) (shr s)" (is "?wfs s")
  shows "\<exists>t x. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> wset s t = None \<and> \<tau>diverge t (x, shr s)"
using fin div wfs 
proof(induct A\<equiv>"dom (thr s)" arbitrary: s rule: finite_induct)
  case empty
  from `mthr.\<tau>diverge s` obtain s' where "\<tau>mredT s s'" by cases auto
  with `{} = dom (thr s)`[symmetric] have False by(auto elim!: mthr.silent_move.cases redT.cases)
  thus ?case ..
next
  case (insert t A)
  note IH = `\<And>s. \<lbrakk> A = dom (thr s); mthr.\<tau>diverge s; ?wfs s \<rbrakk>
             \<Longrightarrow> \<exists>t x. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> wset s t = None \<and> \<tau>diverge t (x, shr s)`
  from `insert t A = dom (thr s)`
  obtain x ln where tst: "thr s t = \<lfloor>(x, ln)\<rfloor>" by(fastsimp simp add: dom_def)
  def s' == "(locks s, ((thr s)(t := None), shr s), wset s)"
  show ?case
  proof(cases "ln = no_wait_locks \<and> \<tau>diverge t (x, shr s) \<and> wset s t = None")
    case True
    with tst show ?thesis by blast
  next
    case False
    def xm == "(x, shr s)"
    def xm' == "(x, shr s)"
    have "A = dom (thr s')" using `t \<notin> A` `insert t A = dom (thr s)`
      unfolding s'_def by auto
    moreover { 
      from xm'_def tst `mthr.\<tau>diverge s` False `?wfs s`
      have "\<exists>s x. thr s t = \<lfloor>(x, ln)\<rfloor> \<and> (ln \<noteq> no_wait_locks \<or> wset s t \<noteq> None \<or> \<not> \<tau>diverge t xm') \<and>
                  s' = (locks s, ((thr s)(t := None), shr s), wset s) \<and> xm = (x, shr s) \<and> 
                  mthr.\<tau>diverge s \<and> silent_moves t xm' xm \<and> ?wfs s"
        unfolding s'_def xm_def by blast
      moreover
      from False have "wfP (if \<tau>diverge t xm' then (\<lambda>s s'. False) else flip (silent_move_from t xm'))"
        using \<tau>diverge_neq_wfP_silent_move_from[of t "(x, shr s)"] unfolding xm'_def by(auto)
      ultimately have "mthr.\<tau>diverge s'"
      proof(coinduct s' xm rule: mthr.\<tau>diverge_trancl_measure_coinduct)
        case (\<tau>diverge s' xm)
        then obtain s x where tst: "thr s t = \<lfloor>(x, ln)\<rfloor>"
	  and blocked: "ln \<noteq> no_wait_locks \<or> wset s t \<noteq> None \<or> \<not> \<tau>diverge t xm'"
	  and s'_def: "s' = (locks s, ((thr s)(t := None), shr s), wset s)"
	  and xm_def: "xm = (x, shr s)"
	  and xmxm': "silent_moves t xm' (x, shr s)"
	  and "?wfs s" and "mthr.\<tau>diverge s" by blast
        from `mthr.\<tau>diverge s` obtain s'' where "\<tau>mredT s s''" "mthr.\<tau>diverge s''" by cases auto
        from `\<tau>mredT s s''` obtain t' ta where "s -t'\<triangleright>ta\<rightarrow> s''" and "m\<tau>move s (t', ta) s''" by auto
        then obtain x' ta' x'' m'' obs where red: "t' \<turnstile> \<langle>x', shr s\<rangle> -ta'\<rightarrow> \<langle>x'', m''\<rangle>"
	  and ta: "ta = observable_ta_of ta' obs"
	  and tst': "thr s t' = \<lfloor>(x', no_wait_locks)\<rfloor>" 
	  and wst': "wset s t' = None"
          and s'': "redTWs t' \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> (redT_upd s t' ta x'' m'') obs s''"
	  by cases(fastsimp elim: m\<tau>move.cases)+
        from `m\<tau>move s (t', ta) s''` ta have [simp]: "ta' = \<epsilon>" "obs = []"
	  by(auto elim!: m\<tau>move.cases dest!: silent_tl)
        hence s'': "s'' = redT_upd s t' ta x'' m''" using s'' by(auto elim: rtrancl3p_cases)
        from `?wfs s` tst' have "wfs t' (x', shr s)" by(auto dest: ts_okD)
        from `m\<tau>move s (t', ta) s''` tst' ta s''
        have "\<tau>move (x', shr s) \<epsilon> (x'', m'')" by(auto elim: m\<tau>move.cases)
        show ?case
        proof(cases "t' = t")
	  case False
	  with tst' wst' have "thr s' t' = \<lfloor>(x', no_wait_locks)\<rfloor>"
	    "wset s' t' = None" "shr s' = shr s" unfolding s'_def by auto
	  with red ta have "s' -t'\<triangleright>observable_ta_of \<epsilon> obs\<rightarrow> redT_upd s' t' ta x'' m''"
	    by -(rule redT_normal, auto)
	  moreover from `\<tau>move (x', shr s) \<epsilon> (x'', m'')` `thr s' t' = \<lfloor>(x', no_wait_locks)\<rfloor>` `shr s' = shr s`
	  have "m\<tau>move s' (t', ta) (redT_upd s' t' ta x'' m'')"
	    unfolding ta `obs = []` by -(rule m\<tau>move.intros, auto)
	  ultimately have "\<tau>mredT s' (redT_upd s' t' ta x'' m'')"
	    unfolding ta `ta' = \<epsilon>` by(rule mthr.silent_move.intros)
	  hence "\<tau>mredT^++ s' (redT_upd s' t' ta x'' m'')" ..
	  moreover have "thr s'' t = \<lfloor>(x, ln)\<rfloor>"
	    using ta tst `t' \<noteq> t` unfolding s'' by simp
	  moreover from `wfs t' (x', shr s)` `\<tau>move (x', shr s) \<epsilon> (x'', m'')` red
	  have [simp]: "m'' = shr s" by(auto dest: \<tau>move_heap)
	  hence "shr s = shr s''" by(simp add: s'')
	  have "ln \<noteq> no_wait_locks \<or> wset s'' t \<noteq> None \<or> \<not> \<tau>diverge t xm'"
	    using blocked ta unfolding s'' by auto
	  moreover have "redT_upd s' t' ta x'' m'' = (locks s'', ((thr s'')(t := None), shr s''), wset s'')"
	    unfolding s'_def tst s'' using `t' \<noteq> t` ta by(auto intro: ext)
	  moreover from `wfs_inv` red `wfs t' (x', shr s)` have "wfs t' (x'', shr s)" by(auto dest: wfs_invD)
	  with `?wfs s` have "?wfs s''" unfolding s'' ta
	    by(auto intro!: ts_okI dest: ts_okD split: split_if_asm)
	  ultimately show ?thesis using `mthr.\<tau>diverge s''` xmxm'
	    unfolding `shr s = shr s''` by blast
        next
	  case True
	  with tst tst' wst' blocked have "\<not> \<tau>diverge t xm'"
	    and [simp]: "x' = x" by auto
	  moreover from red `\<tau>move (x', shr s) \<epsilon> (x'', m'')` True
	  have "silent_move t (x, shr s) (x'', m'')" by auto
	  with xmxm' have "silent_move_from t xm' (x, shr s) (x'', m'')"
	    by(rule silent_move_fromI)
	  ultimately have "(if \<tau>diverge t xm' then \<lambda>s s'. False else flip (silent_move_from t xm')) (x'', m'') xm"
	    by(auto simp add: flip_conv xm_def)
	  moreover have "thr s'' t = \<lfloor>(x'', ln)\<rfloor>" using ta tst True 
	    unfolding s'' by(auto simp add: redT_updLns_def)
	  moreover from `wfs t' (x', shr s)` `\<tau>move (x', shr s) \<epsilon> (x'', m'')` red
	  have [simp]: "m'' = shr s" by(auto dest: \<tau>move_heap)
	  hence "shr s = shr s''" by(simp add: s'')
	  have "s' = (locks s'', ((thr s'')(t := None), shr s''), wset s'')"
	    using True unfolding s'_def s'' ta by(auto intro: ext)
	  moreover have "(x'', m'') = (x'', shr s'')" unfolding s'' by auto
	  moreover from `wfs_inv` red `wfs t' (x', shr s)` have "wfs t' (x'', shr s)" by(auto dest: wfs_invD)
	  with `?wfs s` have "?wfs s''" unfolding s'' ta
	    by(auto intro!: ts_okI dest: ts_okD split: split_if_asm)
	  moreover from xmxm' `silent_move t (x, shr s) (x'', m'')`
	  have "silent_moves t xm' (x'', shr s'')"
	    unfolding `m'' = shr s` `shr s = shr s''` by auto
	  ultimately show ?thesis using `\<not> \<tau>diverge t xm'` `mthr.\<tau>diverge s''` by blast
        qed
      qed }
    moreover from `?wfs s` have "?wfs s'"
      unfolding s'_def by(auto intro!: ts_okI split: split_if_asm dest: ts_okD)
    ultimately have "\<exists>t x. thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> wset s' t = None \<and> \<tau>diverge t (x, shr s')" by(rule IH)
    then obtain t' x' where "thr s' t' = \<lfloor>(x', no_wait_locks)\<rfloor>"
      and "wset s' t' = None" and "\<tau>diverge t' (x', shr s')" by blast
    moreover with False have "t' \<noteq> t" by(auto simp add: s'_def)
    ultimately have "thr s t' = \<lfloor>(x', no_wait_locks)\<rfloor>" "wset s t' = None" "\<tau>diverge t' (x', shr s)"
      unfolding s'_def by auto
    thus ?thesis by blast
  qed
qed

lemma \<tau>mredT_preserves_final_thread:
  "\<lbrakk> \<tau>mredT s s'; final_thread s t \<rbrakk> \<Longrightarrow> final_thread s' t"
by(auto elim: mthr.silent_move.cases intro: redT_preserves_final_thread)

lemma \<tau>mRedT_preserves_final_thread:
  "\<lbrakk> \<tau>mredT^** s s'; final_thread s t \<rbrakk> \<Longrightarrow> final_thread s' t"
by(induct rule: rtranclp.induct)(blast intro: \<tau>mredT_preserves_final_thread)+

end

locale multithreaded_base_measure = multithreaded_base +
  constrains final :: "'x \<Rightarrow> bool"
  and r :: "('l,'t,'x,'m,'w,'o) semantics"
  fixes \<mu> :: "('x \<times> 'm) \<Rightarrow> ('x \<times> 'm) \<Rightarrow> bool"
begin

inductive m\<mu>t :: "'m \<Rightarrow> ('l,'t,'x) thread_info \<Rightarrow> ('l,'t,'x) thread_info \<Rightarrow> bool"
for m and ts and ts'
where
  m\<mu>tI:
  "\<lbrakk> finite (dom ts); ts t = \<lfloor>(x, ln)\<rfloor>; ts' t = \<lfloor>(x', ln')\<rfloor>; \<mu> (x, m) (x', m); \<And>t'. t' \<noteq> t \<Longrightarrow> ts t' = ts' t' \<rbrakk>
  \<Longrightarrow> m\<mu>t m ts ts'"

definition m\<mu> :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> bool"
where "m\<mu> s s' \<longleftrightarrow> shr s = shr s' \<and> m\<mu>t (shr s) (thr s) (thr s')"

lemma m\<mu>t_thr_dom_eq: "m\<mu>t m ts ts' \<Longrightarrow> dom ts = dom ts'"
apply(erule m\<mu>t.cases)
apply(rule equalityI)
 apply(rule subsetI)
 apply(case_tac "xa = t")
  apply(auto)[2]
apply(rule subsetI)
apply(case_tac "xa = t")
apply auto
done

lemma m\<mu>_finite_thrD:
  assumes "m\<mu>t m ts ts'"
  shows "finite (dom ts)" "finite (dom ts')"
using assms
by(simp_all add: m\<mu>t_thr_dom_eq[symmetric])(auto elim: m\<mu>t.cases)

end

locale multithreaded_base_measure_wf = multithreaded_base_measure +
  constrains final :: "'x \<Rightarrow> bool"
  and r :: "('l,'t,'x,'m,'w,'o) semantics"
  and \<mu> :: "('x \<times> 'm) \<Rightarrow> ('x \<times> 'm) \<Rightarrow> bool"
  assumes wf_\<mu>: "wfP \<mu>"
begin

lemma wf_m\<mu>t: "wfP (m\<mu>t m)"
unfolding wfP_eq_minimal
proof(intro strip)
  fix Q :: "('l,'t,'x) thread_info \<Rightarrow> bool" and ts
  assume "ts \<in> Q"
  show "\<exists>z\<in>Q. \<forall>y. m\<mu>t m y z \<longrightarrow> y \<notin> Q"
  proof(cases "finite (dom ts)")
    case False
    hence "\<forall>y. m\<mu>t m y ts \<longrightarrow> y \<notin> Q" by(auto dest: m\<mu>_finite_thrD)
    thus ?thesis using `ts \<in> Q` by blast
  next
    case True
    thus ?thesis using `ts \<in> Q`
    proof(induct A\<equiv>"dom ts" arbitrary: ts Q rule: finite_induct)
      case empty
      hence "dom ts = {}" by simp
      with `ts \<in> Q` show ?case by(auto elim: m\<mu>t.cases)
    next
      case (insert t A)
      note IH = `\<And>ts Q. \<lbrakk>A = dom ts; ts \<in> Q\<rbrakk> \<Longrightarrow> \<exists>z\<in>Q. \<forall>y. m\<mu>t m y z \<longrightarrow> y \<notin> Q`
      def Q' == "{ts. ts t = None \<and> (\<exists>xln. ts(t \<mapsto> xln) \<in> Q)}"
      let ?ts' = "ts(t := None)"
      from `insert t A = dom ts` `t \<notin> A` have "A = dom ?ts'" by auto
      moreover from `insert t A = dom ts` obtain xln where "ts t = \<lfloor>xln\<rfloor>" by(cases "ts t") auto
      hence "ts(t \<mapsto> xln) = ts" by(auto simp add: expand_fun_eq)
      with `ts \<in> Q` have "ts(t \<mapsto> xln) \<in> Q" by(auto)
      hence "?ts' \<in> Q'" unfolding Q'_def by(auto simp del: split_paired_Ex)
      ultimately have "\<exists>z\<in>Q'. \<forall>y. m\<mu>t m y z \<longrightarrow> y \<notin> Q'" by(rule IH)
      then obtain ts' where "ts' \<in> Q'" 
	and min: "\<And>ts''. m\<mu>t m ts'' ts' \<Longrightarrow> ts'' \<notin> Q'" by blast
      from `ts' \<in> Q'` obtain x' ln' where "ts' t = None" "ts'(t \<mapsto> (x', ln')) \<in> Q"
	unfolding Q'_def by auto
      def Q'' == "{(x, m)|x. \<exists>ln. ts'(t \<mapsto> (x, ln)) \<in> Q}"
      from `ts'(t \<mapsto> (x', ln')) \<in> Q` have "(x', m) \<in> Q''" unfolding Q''_def by blast
      hence "\<exists>xm''\<in>Q''. \<forall>xm'''. \<mu> xm''' xm'' \<longrightarrow> xm''' \<notin> Q''" by(rule wf_\<mu>[unfolded wfP_eq_minimal, rule_format])
      then obtain xm'' where "xm'' \<in> Q''" and min': "\<And>xm'''. \<mu> xm''' xm'' \<Longrightarrow> xm''' \<notin> Q''" by blast
      from `xm'' \<in> Q''` obtain x'' ln'' where "xm'' = (x'', m)" "ts'(t \<mapsto> (x'', ln'')) \<in> Q" unfolding Q''_def by blast
      moreover {
	fix ts''
	assume "m\<mu>t m ts'' (ts'(t \<mapsto> (x'', ln'')))"
	then obtain T X'' LN'' X' LN'
	  where "finite (dom ts'')" "ts'' T = \<lfloor>(X'', LN'')\<rfloor>" 
	  and "(ts'(t \<mapsto> (x'', ln''))) T = \<lfloor>(X', LN')\<rfloor>" "\<mu> (X'', m) (X', m)"
	  and eq: "\<And>t'. t' \<noteq> T \<Longrightarrow> ts'' t' = (ts'(t \<mapsto> (x'', ln''))) t'" by(cases) blast
	have "ts'' \<notin> Q"
	proof(cases "T = t")
	  case True
	  from True `(ts'(t \<mapsto> (x'', ln''))) T = \<lfloor>(X', LN')\<rfloor>` have "X' = x''" by simp
	  with `\<mu> (X'', m) (X', m)` have "(X'', m) \<notin> Q''" by(auto dest: min'[unfolded `xm'' = (x'', m)`])
	  hence "\<forall>ln. ts'(t \<mapsto> (X'', ln)) \<notin> Q" by(simp add: Q''_def)
	  moreover from `ts' t = None` eq True
	  have "ts''(t := None) = ts'" by(auto simp add: expand_fun_eq)
	  with `ts'' T = \<lfloor>(X'', LN'')\<rfloor>` True
	  have ts'': "ts'' = ts'(t \<mapsto> (X'', LN''))" by(auto intro!: ext)
	  ultimately show ?thesis by blast
	next
	  case False
	  from `finite (dom ts'')` have "finite (dom (ts''(t := None)))" by simp
	  moreover from `ts'' T = \<lfloor>(X'', LN'')\<rfloor>` False
	  have "(ts''(t := None)) T = \<lfloor>(X'', LN'')\<rfloor>" by simp
	  moreover from `(ts'(t \<mapsto> (x'', ln''))) T = \<lfloor>(X', LN')\<rfloor>` False
	  have "ts' T = \<lfloor>(X', LN')\<rfloor>" by simp
	  ultimately have "m\<mu>t m (ts''(t := None)) ts'" using `\<mu> (X'', m) (X', m)`
	  proof(rule m\<mu>tI)
	    fix t'
	    assume "t' \<noteq> T"
	    with eq[OF False[symmetric]] eq[OF this] `ts' t = None`
	    show "(ts''(t := None)) t' = ts' t'" by auto
	  qed
	  hence "ts''(t := None) \<notin> Q'" by(rule min)
	  thus ?thesis
	  proof(rule contrapos_nn)
	    assume "ts'' \<in> Q"
	    from eq[OF False[symmetric]] have "ts'' t = \<lfloor>(x'', ln'')\<rfloor>" by simp
	    hence ts'': "ts''(t \<mapsto> (x'', ln'')) = ts''" by(auto simp add: expand_fun_eq)
	    from `ts'' \<in> Q` have "ts''(t \<mapsto> (x'', ln'')) \<in> Q" unfolding ts'' .
	    thus "ts''(t := None) \<in> Q'" unfolding Q'_def by auto
	  qed
	qed
      }
      ultimately show ?case by blast
    qed
  qed
qed

lemma wf_m\<mu>: "wfP m\<mu>"
proof -
  have "wf (inv_image (same_fst (\<lambda>m. True) (\<lambda>m (ts, ts'). m\<mu>t m ts ts')) (\<lambda>s. (shr s, thr s)))"
    by(rule wf_inv_image)(rule wf_same_fst, rule wf_m\<mu>t[unfolded wfP_def Collect_def])
  also have "inv_image (same_fst (\<lambda>m. True) (\<lambda>m (ts, ts'). m\<mu>t m ts ts')) (\<lambda>s. (shr s, thr s)) = (\<lambda>(s, s'). m\<mu> s s')"
    by(auto simp add: m\<mu>_def same_fst_def)(auto simp add: mem_def)
  finally show ?thesis by(simp add: wfP_def Collect_def)
qed

end

subsection {* Lifting for delay bisimulations *}

locale FWdelay_bisimulation_base =
  FWbisimulation_base _ _ _ r2 bisim bisim_wait +
  r1!: \<tau>multithreaded final1 r1 \<tau>move1 +
  r2!: \<tau>multithreaded final2 r2 \<tau>move2 
  for r2 :: "('l,'t,'x2,'m2,'w,'o) semantics" ("_ \<turnstile> _ -2-_\<rightarrow> _" [50,0,0,50] 80)
  and bisim :: "'t \<Rightarrow> ('x1 \<times> 'm1, 'x2 \<times> 'm2) bisim" ("_ \<turnstile> _/ \<approx> _" [50, 50, 50] 60)
  and bisim_wait :: "('x1, 'x2) bisim" ("_/ \<approx>w _" [50, 50] 60)
  and \<tau>move1 :: "('l,'t,'x1,'m1,'w,'o) \<tau>moves"
  and \<tau>move2 :: "('l,'t,'x2,'m2,'w,'o) \<tau>moves"
begin

abbreviation \<tau>mred1 :: "('l,'t,'x1,'m1,'w) state \<Rightarrow> ('l,'t,'x1,'m1,'w) state \<Rightarrow> bool"
where "\<tau>mred1 \<equiv> r1.\<tau>mredT"

abbreviation \<tau>mred2 :: "('l,'t,'x2,'m2,'w) state \<Rightarrow> ('l,'t,'x2,'m2,'w) state \<Rightarrow> bool"
where "\<tau>mred2 \<equiv> r2.\<tau>mredT"

abbreviation m\<tau>move1 :: "(('l,'t,'x1,'m1,'w) state, 't \<times> ('l,'t,'x1,'m1,'w,('l,'o) observable list) thread_action) trsys"
where "m\<tau>move1 \<equiv> r1.m\<tau>move"

abbreviation m\<tau>move2 :: "(('l,'t,'x2,'m2,'w) state, 't \<times> ('l,'t,'x2,'m2,'w,('l,'o) observable list) thread_action) trsys"
where "m\<tau>move2 \<equiv> r2.m\<tau>move"

abbreviation \<tau>mRed1 :: "('l,'t,'x1,'m1,'w) state \<Rightarrow> ('l,'t,'x1,'m1,'w) state \<Rightarrow> bool"
where "\<tau>mRed1 \<equiv> \<tau>mred1^**"

abbreviation \<tau>mRed2 :: "('l,'t,'x2,'m2,'w) state \<Rightarrow> ('l,'t,'x2,'m2,'w) state \<Rightarrow> bool"
where "\<tau>mRed2 \<equiv> \<tau>mred2^**"

abbreviation \<tau>mtRed1 :: "('l,'t,'x1,'m1,'w) state \<Rightarrow> ('l,'t,'x1,'m1,'w) state \<Rightarrow> bool"
where "\<tau>mtRed1 \<equiv> \<tau>mred1^++"

abbreviation \<tau>mtRed2 :: "('l,'t,'x2,'m2,'w) state \<Rightarrow> ('l,'t,'x2,'m2,'w) state \<Rightarrow> bool"
where "\<tau>mtRed2 \<equiv> \<tau>mred2^++"

lemma bisim_inv_\<tau>s1_inv:
  assumes inv: "bisim_inv"
  and bisim: "t \<turnstile> s1 \<approx> s2"
  and red: "r1.silent_moves t s1 s1'"
  obtains s2' where "t \<turnstile> s1' \<approx> s2'"
proof(atomize_elim)
  from red bisim show "\<exists>s2'. t \<turnstile> s1' \<approx> s2'"
    by(induct rule: rtranclp_induct)(fastsimp elim: bisim_invD1[OF inv])+
qed

lemma bisim_inv_\<tau>s2_inv:
  assumes inv: "bisim_inv"
  and bisim: "t \<turnstile> s1 \<approx> s2"
  and red: "r2.silent_moves t s2 s2'"
  obtains s1' where "t \<turnstile> s1' \<approx> s2'"
proof(atomize_elim)
  from red bisim show "\<exists>s1'. t \<turnstile> s1' \<approx> s2'"
    by(induct rule: rtranclp_induct)(fastsimp elim: bisim_invD2[OF inv])+
qed

primrec activate_cond_action1 :: "('l,'t,'x1,'m1,'w) state \<Rightarrow> ('l,'t,'x2,'m2,'w) state \<Rightarrow> 
                                 't conditional_action \<Rightarrow> ('l,'t,'x1,'m1,'w) state"
where
  "activate_cond_action1 s1 s2 (Join t) =
   (case thr s1 t of None \<Rightarrow> s1
            | \<lfloor>(x1, ln1)\<rfloor> \<Rightarrow> (case thr s2 t of None \<Rightarrow> s1
                                     | \<lfloor>(x2, ln2)\<rfloor> \<Rightarrow> 
  if final2 x2 \<and> ln2 = no_wait_locks
  then redT_upd s1 t (\<epsilon> :: ('l,'t,'x1,'m1,'w,'o list) thread_action)
                (SOME x1'. r1.silent_moves t (x1, shr s1) (x1', shr s1) \<and> final1 x1' \<and> 
                           t \<turnstile> (x1', shr s1) \<approx> (x2, shr s2))
                (shr s1)
  else s1))"
| "activate_cond_action1 s1 s2 Notified = s1"
| "activate_cond_action1 s1 s2 Interrupted = s1"

primrec activate_cond_actions1 :: "('l,'t,'x1,'m1,'w) state \<Rightarrow> ('l,'t,'x2,'m2,'w) state
                                  \<Rightarrow> ('t conditional_action) list \<Rightarrow> ('l,'t,'x1,'m1,'w) state"
where
  "activate_cond_actions1 s1 s2 [] = s1"
| "activate_cond_actions1 s1 s2 (ct # cts) = activate_cond_actions1 (activate_cond_action1 s1 s2 ct) s2 cts"

primrec activate_cond_action2 :: "('l,'t,'x1,'m1,'w) state \<Rightarrow> ('l,'t,'x2,'m2,'w) state \<Rightarrow> 
                                 't conditional_action \<Rightarrow> ('l,'t,'x2,'m2,'w) state"
where
 "activate_cond_action2 s1 s2 (Join t) =
   (case thr s2 t of None \<Rightarrow> s2
            | \<lfloor>(x2, ln2)\<rfloor> \<Rightarrow> (case thr s1 t of None \<Rightarrow> s2
                                     | \<lfloor>(x1, ln1)\<rfloor> \<Rightarrow> 
  if final1 x1 \<and> ln1 = no_wait_locks
  then redT_upd s2 t (\<epsilon> :: ('l,'t,'x2,'m2,'w,'o list) thread_action)
                (SOME x2'. r2.silent_moves t (x2, shr s2) (x2', shr s2) \<and> final2 x2' \<and>
                           t \<turnstile> (x1, shr s1) \<approx> (x2', shr s2))
                (shr s2)
  else s2))"
| "activate_cond_action2 s1 s2 Notified = s2"
| "activate_cond_action2 s1 s2 Interrupted = s2"

primrec activate_cond_actions2 :: "('l,'t,'x1,'m1,'w) state \<Rightarrow> ('l,'t,'x2,'m2,'w) state \<Rightarrow>
                                  ('t conditional_action) list \<Rightarrow> ('l,'t,'x2,'m2,'w) state"
where
  "activate_cond_actions2 s1 s2 [] = s2"
| "activate_cond_actions2 s1 s2 (ct # cts) = activate_cond_actions2 s1 (activate_cond_action2 s1 s2 ct) cts"

end

lemma activate_cond_action1_flip [flip_simps]:
  "FWdelay_bisimulation_base.activate_cond_action1 final2 r2 final1 (\<lambda>t. flip (bisim t)) \<tau>move2 s2 s1 =
   FWdelay_bisimulation_base.activate_cond_action2 final1 final2 r2 bisim \<tau>move2 s1 s2"
apply(rule ext)
apply(case_tac x)
apply(simp_all only: FWdelay_bisimulation_base.activate_cond_action1.simps 
                     FWdelay_bisimulation_base.activate_cond_action2.simps flip_simps)
done

lemma activate_cond_actions1_flip [flip_simps]:
  "FWdelay_bisimulation_base.activate_cond_actions1 final2 r2 final1 (\<lambda>t. flip (bisim t)) \<tau>move2 s2 s1 =
   FWdelay_bisimulation_base.activate_cond_actions2 final1 final2 r2 bisim \<tau>move2 s1 s2"
  (is "?lhs = ?rhs")
proof(rule ext)
  fix xs
  show "?lhs xs = ?rhs xs"
    by(induct xs arbitrary: s2)
      (simp_all only: FWdelay_bisimulation_base.activate_cond_actions1.simps
                      FWdelay_bisimulation_base.activate_cond_actions2.simps flip_simps)
qed

lemma activate_cond_action2_flip [flip_simps]:
  "FWdelay_bisimulation_base.activate_cond_action2 final2 final1 r1 (\<lambda>t. flip (bisim t)) \<tau>move1 s2 s1 =
   FWdelay_bisimulation_base.activate_cond_action1 final1 r1 final2 bisim \<tau>move1 s1 s2"
apply(rule ext)
apply(case_tac x)
apply(simp_all only: FWdelay_bisimulation_base.activate_cond_action1.simps 
                     FWdelay_bisimulation_base.activate_cond_action2.simps flip_simps)
done

lemma activate_cond_actions2_flip [flip_simps]:
  "FWdelay_bisimulation_base.activate_cond_actions2 final2 final1 r1 (\<lambda>t. flip (bisim t)) \<tau>move1 s2 s1 =
   FWdelay_bisimulation_base.activate_cond_actions1 final1 r1 final2 bisim \<tau>move1 s1 s2"
  (is "?lhs = ?rhs")
proof(rule ext)
  fix xs
  show "?lhs xs = ?rhs xs"
    by(induct xs arbitrary: s1)
      (simp_all only: FWdelay_bisimulation_base.activate_cond_actions1.simps 
                      FWdelay_bisimulation_base.activate_cond_actions2.simps flip_simps)
qed
  
context FWdelay_bisimulation_base begin

lemma shr_activate_cond_action1 [simp]: "shr (activate_cond_action1 s1 s2 ct) = shr s1"
by(cases ct) simp_all

lemma shr_activate_cond_actions1 [simp]: "shr (activate_cond_actions1 s1 s2 cts) = shr s1"
by(induct cts arbitrary: s1) auto

lemma shr_activate_cond_action2 [simp]: "shr (activate_cond_action2 s1 s2 ct) = shr s2"
by(cases ct) simp_all

lemma shr_activate_cond_actions2 [simp]: "shr (activate_cond_actions2 s1 s2 cts) = shr s2"
by(induct cts arbitrary: s2) auto

lemma locks_activate_cond_action1 [simp]: "locks (activate_cond_action1 s1 s2 ct) = locks s1"
by(cases ct) simp_all

lemma locks_activate_cond_actions1 [simp]: "locks (activate_cond_actions1 s1 s2 cts) = locks s1"
by(induct cts arbitrary: s1) auto

lemma locks_activate_cond_action2 [simp]: "locks (activate_cond_action2 s1 s2 ct) = locks s2"
by(cases ct) simp_all

lemma locks_activate_cond_actions2 [simp]: "locks (activate_cond_actions2 s1 s2 cts) = locks s2"
by(induct cts arbitrary: s2) auto

lemma wset_activate_cond_action1 [simp]: "wset (activate_cond_action1 s1 s2 ct) = wset s1"
by(cases ct) simp_all

lemma wset_activate_cond_actions1 [simp]: "wset (activate_cond_actions1 s1 s2 cts) = wset s1"
by(induct cts arbitrary: s1) auto

lemma wset_activate_cond_action2 [simp]: "wset (activate_cond_action2 s1 s2 ct) = wset s2"
by(cases ct) simp_all

lemma wset_activate_cond_actions2 [simp]: "wset (activate_cond_actions2 s1 s2 cts) = wset s2"
by(induct cts arbitrary: s2) auto

end

locale FWdelay_bisimulation_lift_aux =
  FWdelay_bisimulation_base _ _ _ _ _ _ \<tau>move1 \<tau>move2 +
  r1!: \<tau>multithreaded_wf final1 r1 \<tau>move1 "\<lambda>t s1. \<exists>s2. t \<turnstile> s1 \<approx> s2" +
  r2!: \<tau>multithreaded_wf final2 r2 \<tau>move2 "\<lambda>t s2. \<exists>s1. t \<turnstile> s1 \<approx> s2"
  for \<tau>move1 :: "('l,'t,'x1,'m1,'w,'o) \<tau>moves"
  and \<tau>move2 :: "('l,'t,'x2,'m2,'w,'o) \<tau>moves"
begin

lemma FWdelay_bisimulation_lift_aux_flip:
  "FWdelay_bisimulation_lift_aux final2 r2 final1 r1 (\<lambda>t. flip (bisim t)) \<tau>move2 \<tau>move1"
apply(rule FWdelay_bisimulation_lift_aux.intro)
apply(unfold flip_simps)
apply(rule r2.\<tau>multithreaded_wf_axioms r1.\<tau>multithreaded_wf_axioms)+
done

end

lemma FWdelay_bisimulation_lift_aux_flip_simps [flip_simps]:
  "FWdelay_bisimulation_lift_aux final2 r2 final1 r1 (\<lambda>t. flip (bisim t)) \<tau>move2 \<tau>move1 =
   FWdelay_bisimulation_lift_aux final1 r1 final2 r2 bisim \<tau>move1 \<tau>move2"
by(auto dest: FWdelay_bisimulation_lift_aux.FWdelay_bisimulation_lift_aux_flip simp only: flip_flip)

context FWdelay_bisimulation_lift_aux begin

lemma cond_actions_ok_\<tau>mred1_inv:
  assumes red: "\<tau>mred1 s1 s1'"
  and ct: "r1.cond_action_ok s1 t ct"
  shows "r1.cond_action_ok s1' t ct"
using ct
proof(cases ct)
  case (Join t')
  show ?thesis using red ct
  proof(cases "thr s1 t'")
    case None with red ct Join show ?thesis
      by(fastsimp elim!: r1.mthr.silent_move.cases r1.redT.cases r1.m\<tau>move.cases rtrancl3p_cases 
                  dest: r1.silent_tl split: split_if_asm)
  next
    case (Some a) with red ct Join show ?thesis
      by(fastsimp elim!: r1.mthr.silent_move.cases r1.redT.cases r1.m\<tau>move.cases rtrancl3p_cases
                  dest: r1.silent_tl r1.final_no_red split: split_if_asm)
  qed
qed simp_all

lemma cond_actions_ok_\<tau>mred2_inv:
  "\<lbrakk> \<tau>mred2 s2 s2'; r2.cond_action_ok s2 t ct \<rbrakk> \<Longrightarrow> r2.cond_action_ok s2' t ct"
using FWdelay_bisimulation_lift_aux.cond_actions_ok_\<tau>mred1_inv[OF FWdelay_bisimulation_lift_aux_flip] .

lemma cond_actions_ok_\<tau>mRed1_inv:
  "\<lbrakk> \<tau>mRed1 s1 s1'; r1.cond_action_ok s1 t ct \<rbrakk> \<Longrightarrow> r1.cond_action_ok s1' t ct"
by(induct rule: rtranclp_induct)(blast intro: cond_actions_ok_\<tau>mred1_inv)+

lemma cond_actions_ok_\<tau>mRed2_inv:
  "\<lbrakk> \<tau>mRed2 s2 s2'; r2.cond_action_ok s2 t ct \<rbrakk> \<Longrightarrow> r2.cond_action_ok s2' t ct"
by(rule FWdelay_bisimulation_lift_aux.cond_actions_ok_\<tau>mRed1_inv[OF FWdelay_bisimulation_lift_aux_flip])

end

locale FWdelay_bisimulation_lift =
  FWdelay_bisimulation_lift_aux +
  constrains final1 :: "'x1 \<Rightarrow> bool"
  and r1 :: "('l, 't, 'x1, 'm1, 'w, 'o) semantics"
  and final2 :: "'x2 \<Rightarrow> bool"
  and r2 :: "('l, 't, 'x2, 'm2, 'w, 'o) semantics"
  and bisim :: "'t \<Rightarrow> ('x1 \<times> 'm1, 'x2 \<times> 'm2) bisim"
  and bisim_wait :: "('x1, 'x2) bisim"
  and \<tau>move1 :: "('l, 't, 'x1, 'm1, 'w, 'o) \<tau>moves" 
  and \<tau>move2 :: "('l, 't, 'x2, 'm2, 'w, 'o) \<tau>moves"
  assumes \<tau>inv_locale: "\<tau>inv (r1 t) (r2 t) (bisim t) (ta_bisim bisim) \<tau>move1 \<tau>move2"

sublocale FWdelay_bisimulation_lift < \<tau>inv "r1 t" "r2 t" "bisim t" "ta_bisim bisim" \<tau>move1 \<tau>move2 for t
by(rule \<tau>inv_locale)

context FWdelay_bisimulation_lift begin

lemma FWdelay_bisimulation_lift_flip:
  "FWdelay_bisimulation_lift final2 r2 final1 r1 (\<lambda>t. flip (bisim t)) \<tau>move2 \<tau>move1"
apply(rule FWdelay_bisimulation_lift.intro)
 apply(rule FWdelay_bisimulation_lift_aux_flip)
apply(rule FWdelay_bisimulation_lift_axioms.intro)
apply(unfold flip_simps)
apply(unfold_locales)
done

end

lemma FWdelay_bisimulation_lift_flip_simps [flip_simps]:
  "FWdelay_bisimulation_lift final2 r2 final1 r1 (\<lambda>t. flip (bisim t)) \<tau>move2 \<tau>move1 =
   FWdelay_bisimulation_lift final1 r1 final2 r2 bisim \<tau>move1 \<tau>move2"
by(auto dest: FWdelay_bisimulation_lift.FWdelay_bisimulation_lift_flip simp only: flip_flip)

context FWdelay_bisimulation_lift begin

lemma \<tau>inv_lift: "\<tau>inv r1.redT r2.redT mbisim mta_bisim m\<tau>move1 m\<tau>move2"
proof
  fix s1 s2 tl1 s1' tl2 s2'
  assume "s1 \<approx>m s2" "s1' \<approx>m s2'" "tl1 \<sim>T tl2" "r1.redT s1 tl1 s1'" "r2.redT s2 tl2 s2'"
  moreover obtain t ta1 where tl1: "tl1 = (t, ta1)" by(cases tl1)
  moreover obtain t' ta2 where tl2: "tl2 = (t', ta2)" by(cases tl2)
  moreover obtain ls1 ts1 ws1 m1 where s1: "s1 = (ls1, (ts1, m1), ws1)" by(cases s1) auto
  moreover obtain ls2 ts2 ws2 m2 where s2: "s2 = (ls2, (ts2, m2), ws2)" by(cases s2) auto
  moreover obtain ls1' ts1' ws1' m1' where s1': "s1' = (ls1', (ts1', m1'), ws1')" by(cases s1') auto
  moreover obtain ls2' ts2' ws2' m2' where s2': "s2' = (ls2', (ts2', m2'), ws2')" by(cases s2') auto
  ultimately have mbisim: "(ls1, (ts1, m1), ws1) \<approx>m (ls2, (ts2, m2), ws2)"
    and mbisim': "(ls1', (ts1', m1'), ws1') \<approx>m (ls2', (ts2', m2'), ws2')"
    and mred1: "(ls1, (ts1, m1), ws1) -1-t\<triangleright>ta1\<rightarrow> (ls1', (ts1', m1'), ws1')"
    and mred2: "(ls2, (ts2, m2), ws2) -2-t\<triangleright>ta2\<rightarrow> (ls2', (ts2', m2'), ws2')"
    and tasim: "ta1 \<sim>m ta2" and tt': "t' = t" by simp_all
  from mbisim have ls: "ls1 = ls2" and ws: "ws1 = ws2"
    and tbisim: "\<And>t. tbisim (ws2 t = None) t (ts1 t) m1 (ts2 t) m2" by(simp_all add: mbisim_def)
  from mbisim' have ls': "ls1' = ls2'" and ws': "ws1' = ws2'"
    and tbisim': "\<And>t. tbisim (ws2' t = None) t (ts1' t) m1' (ts2' t) m2'" by(simp_all add: mbisim_def)
  from mred1 r1.redT_thread_not_disappear[OF mred1]
  obtain x1 ln1 x1' ln1' where tst1: "ts1 t = \<lfloor>(x1, ln1)\<rfloor>"
    and tst1': "ts1' t = \<lfloor>(x1', ln1')\<rfloor>" and ws1t: "ws1 t = None"
    by(fastsimp elim!: r1.redT.cases)
  from mred2 r2.redT_thread_not_disappear[OF mred2]
  obtain x2 ln2 x2' ln2' where tst2: "ts2 t = \<lfloor>(x2, ln2)\<rfloor>"
    and tst2': "ts2' t = \<lfloor>(x2', ln2')\<rfloor>" by(fastsimp elim!: r2.redT.cases)
  from tbisim[of t] tst1 tst2 ws1t ws have bisim: "t \<turnstile> (x1, m1) \<approx> (x2, m2)"
    and ln: "ln1 = ln2" by(auto simp add: tbisim_def)
  from tbisim'[of t] tst1' tst2' have bisim': "t \<turnstile> (x1', m1') \<approx> (x2', m2')"
    and ln': "ln1' = ln2'" by(auto simp add: tbisim_def)
  show "m\<tau>move1 s1 tl1 s1' = m\<tau>move2 s2 tl2 s2'" unfolding s1 s2 s1' s2' tt' tl1 tl2
  proof -
    show "m\<tau>move1 (ls1, (ts1, m1), ws1) (t, ta1) (ls1', (ts1', m1'), ws1') =
          m\<tau>move2 (ls2, (ts2, m2), ws2) (t, ta2) (ls2', (ts2', m2'), ws2')"
      (is "?lhs = ?rhs")
    proof
      assume m\<tau>: ?lhs
      with tst1 tst1' obtain ta1' where [simp]: "ta1 = observable_ta_of ta1' []"
	and \<tau>1: "\<tau>move1 (x1, m1) ta1' (x1', m1')" 
	and ln1: "ln1 = no_wait_locks" by(fastsimp elim!: r1.m\<tau>move.cases)
      from \<tau>1 have "ta1' = \<epsilon>" by(rule r1.silent_tl)
      with mred1 \<tau>1 tst1 tst1' ln1 have red1: "t \<turnstile> (x1, m1) -1-ta1'\<rightarrow> (x1', m1')"
	by(auto elim!: r1.redT.cases rtrancl3p_cases)
      from tasim `ta1' = \<epsilon>` have [simp]: "ta2 = observable_ta_of \<epsilon> []"
        by(simp add: observable_ta_of_empty_ta_bisim_conv)
      with mred2 ln1 ln tst2 tst2' have red2: "t \<turnstile> (x2, m2) -2-\<epsilon>\<rightarrow> (x2', m2')"
	by(fastsimp elim!: r2.redT.cases rtrancl3p_cases)
      from \<tau>1 \<tau>inv[OF bisim red1 red2] bisim' tasim
      have \<tau>2: "\<tau>move2 (x2, m2) \<epsilon> (x2', m2')" by simp
      with tst2 tst2' ln ln1 show ?rhs
        unfolding `ta2 = observable_ta_of \<epsilon> []`
        by -(rule r2.m\<tau>move.intros, auto)
    next
      assume m\<tau>: ?rhs
      with tst2 tst2' obtain ta2' where [simp]: "ta2 = observable_ta_of ta2' []"
	and \<tau>2: "\<tau>move2 (x2, m2) ta2' (x2', m2')" 
	and ln2: "ln2 = no_wait_locks" by(fastsimp elim!: r2.m\<tau>move.cases)
      from \<tau>2 have "ta2' = \<epsilon>" by(rule r2.silent_tl)
      with mred2 \<tau>2 tst2 tst2' ln2 have red2: "t \<turnstile> (x2, m2) -2-ta2'\<rightarrow> (x2', m2')"
	by(auto elim!: r2.redT.cases rtrancl3p_cases)
      from tasim `ta2' = \<epsilon>` have [simp]: "ta1 = observable_ta_of \<epsilon> []"
        by(simp add: ta_bisim_observable_ta_of_empty_conv)
      with mred1 ln2 ln tst1 tst1' have red1: "t \<turnstile> (x1, m1) -1-\<epsilon>\<rightarrow> (x1', m1')"
	by(fastsimp elim!: r1.redT.cases rtrancl3p_cases)
      from \<tau>2 \<tau>inv[OF bisim red1 red2] bisim' tasim
      have \<tau>1: "\<tau>move1 (x1, m1) \<epsilon> (x1', m1')" by auto
      with tst1 tst1' ln ln2 show ?lhs unfolding `ta1 = observable_ta_of \<epsilon> []`
        by-(rule r1.m\<tau>move.intros, auto)
    qed
  qed
qed

end

sublocale FWdelay_bisimulation_lift < mthr!: \<tau>inv r1.redT r2.redT mbisim mta_bisim m\<tau>move1 m\<tau>move2
by(rule \<tau>inv_lift)

locale FWdelay_bisimulation_final_base =
  FWdelay_bisimulation_lift_aux +
  constrains final1 :: "'x1 \<Rightarrow> bool"
  and r1 :: "('l,'t,'x1,'m1,'w, 'o) semantics"
  and final2 :: "'x2 \<Rightarrow> bool"
  and r2 :: "('l,'t,'x2,'m2,'w, 'o) semantics"
  and bisim :: "'t \<Rightarrow> ('x1 \<times> 'm1, 'x2 \<times> 'm2) bisim"
  and bisim_wait :: "('x1, 'x2) bisim"
  and \<tau>move1 :: "('l,'t,'x1,'m1,'w, 'o) \<tau>moves"
  and \<tau>move2 :: "('l,'t,'x2,'m2,'w, 'o) \<tau>moves"
  assumes delay_bisim_locale:
  "delay_bisimulation_final_base (r1 t) (r2 t) (bisim t) \<tau>move1 \<tau>move2 (\<lambda>(x1, m). final1 x1) (\<lambda>(x2, m). final2 x2)"

sublocale FWdelay_bisimulation_final_base <
  delay_bisimulation_final_base "r1 t" "r2 t" "bisim t" "ta_bisim bisim" \<tau>move1 \<tau>move2
                                "\<lambda>(x1, m). final1 x1" "\<lambda>(x2, m). final2 x2" 
  for t
by(rule delay_bisim_locale)

context FWdelay_bisimulation_final_base begin

lemma FWdelay_bisimulation_final_base_flip:
  "FWdelay_bisimulation_final_base final2 r2 final1 r1 (\<lambda>t. flip (bisim t)) \<tau>move2 \<tau>move1"
apply(rule FWdelay_bisimulation_final_base.intro)
 apply(rule FWdelay_bisimulation_lift_aux_flip)
apply(rule FWdelay_bisimulation_final_base_axioms.intro)
apply(rule delay_bisimulation_final_base_flip)
done

end

lemma FWdelay_bisimulation_final_base_flip_simps [flip_simps]:
  "FWdelay_bisimulation_final_base final2 r2 final1 r1 (\<lambda>t. flip (bisim t)) \<tau>move2 \<tau>move1 =
   FWdelay_bisimulation_final_base final1 r1 final2 r2 bisim \<tau>move1 \<tau>move2"
by(auto dest: FWdelay_bisimulation_final_base.FWdelay_bisimulation_final_base_flip simp only: flip_flip)

context FWdelay_bisimulation_final_base begin

lemma bisim_inv_wfs_inv1:
  "bisim_inv \<Longrightarrow> r1.wfs_inv"
by(blast intro: r1.wfs_invI bisim_invD1)

lemma bisim_inv_wfs_inv2:
  "bisim_inv \<Longrightarrow> r2.wfs_inv"
by(blast intro: r2.wfs_invI bisim_invD2)

lemma cond_actions_ok_bisim_ex_\<tau>1_inv:
  fixes ls ts1 m1 ws ts2 m2 ct
  defines "s1' \<equiv> activate_cond_action1 (ls, (ts1, m1), ws) (ls, (ts2, m2), ws) ct"
  assumes inv: "r1.wfs_inv"
  and mbisim: "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (ts1 t') m1 (ts2 t') m2"
  and ts1t: "ts1 t = \<lfloor>xln\<rfloor>"
  and ts2t: "ts2 t = \<lfloor>xln'\<rfloor>"
  and ct: "r2.cond_action_ok (ls, (ts2, m2), ws) t ct"
  shows "\<tau>mRed1 (ls, (ts1, m1), ws) s1'"
  and "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (thr s1' t') m1 (ts2 t') m2"
  and "r1.cond_action_ok s1' t ct"
  and "thr s1' t = \<lfloor>xln\<rfloor>"
proof -
  have "\<tau>mRed1 (ls, (ts1, m1), ws) s1' \<and>
        (\<forall>t'. t' \<noteq> t \<longrightarrow> tbisim (ws t' = None) t' (thr s1' t') m1 (ts2 t') m2) \<and>
        r1.cond_action_ok s1' t ct \<and> thr s1' t = \<lfloor>xln\<rfloor>"
    using ct
  proof(cases ct)
    case (Join t')
    show ?thesis 
    proof(cases "ts1 t'")
      case None
      with mbisim ts1t have "t \<noteq> t'" by auto
      moreover from None Join have "s1' = (ls, (ts1, m1), ws)" by(simp add: s1'_def)
      ultimately show ?thesis using mbisim Join ct None ts1t by(simp add: tbisim_def)
    next
      case (Some xln)
      moreover obtain x1 ln where "xln = (x1, ln)" by(cases xln)
      ultimately have ts1t': "ts1 t' = \<lfloor>(x1, ln)\<rfloor>" by simp
      from Join ct Some ts2t have tt': "t' \<noteq> t" by auto
      from mbisim[OF tt'] ts1t' obtain x2 where ts2t': "ts2 t' = \<lfloor>(x2, ln)\<rfloor>" 
	and bisim: "t' \<turnstile> (x1, m1) \<approx> (x2, m2)" by(auto simp add: tbisim_def)
      from ct Join ts2t' have final2: "final2 x2" and ln: "ln = no_wait_locks"
      and wst': "ws t' = None" by simp_all
      let ?x1' = "SOME x. r1.silent_moves t' (x1, m1) (x, m1) \<and> final1 x \<and> t' \<turnstile> (x, m1) \<approx> (x2, m2)"
      { from final2_simulation[OF bisim] final2 obtain x1' m1' 
	  where "r1.silent_moves t' (x1, m1) (x1', m1')" and "t' \<turnstile> (x1', m1') \<approx> (x2, m2)"
	  and "final1 x1'" by auto
	moreover hence "m1' = m1" using inv bisim by(auto dest: r1.red_rtrancl_\<tau>_heapD_inv)
	ultimately have "\<exists>x. r1.silent_moves t' (x1, m1) (x, m1) \<and> final1 x \<and> t' \<turnstile> (x, m1) \<approx> (x2, m2)"
          by blast }
      from someI_ex[OF this] have red1: "r1.silent_moves t' (x1, m1) (?x1', m1)"
	and final1: "final1 ?x1'" and bisim': "t' \<turnstile> (?x1', m1) \<approx> (x2, m2)" by blast+
      let ?S1' = "redT_upd (ls, (ts1, m1), ws) t' (\<epsilon> :: ('l,'t,'x1,'m1,'w,'o list) thread_action) ?x1' m1"
      from r1.silent_moves_into_RedT_\<tau>_inv[where ?s="(ls, (ts1, m1), ws)" and t=t', simplified, OF inv red1]
        bisim ts1t' ln wst'
      have Red1: "\<tau>mRed1 (ls, (ts1, m1), ws) ?S1'" by auto
      moreover from Join ln ts1t' final1 wst' tt'
      have ct': "r1.cond_action_ok ?S1' t ct" by(auto intro: finfun_ext)
      { fix t''
	assume "t \<noteq> t''"
	with Join mbisim[OF this[symmetric]] bisim' ts1t' ts2t' wst' s1'_def
	have "tbisim (ws t'' = None) t'' (thr s1' t'') m1 (ts2 t'') m2"
	  by(auto simp add: tbisim_def redT_updLns_def o_def finfun_Diag_const2) }
      moreover from Join ts1t' ts2t' final2 ln have "s1' = ?S1'" by(simp add: s1'_def)
      ultimately show ?thesis using Red1 ct' ts1t' tt' ts1t by(auto)
    qed
  qed simp_all
  thus "\<tau>mRed1 (ls, (ts1, m1), ws) s1'"
    and "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (thr s1' t') m1 (ts2 t') m2"
    and "r1.cond_action_ok s1' t ct"
    and "thr s1' t = \<lfloor>xln\<rfloor>" by blast+
qed

lemma cond_actions_oks_bisim_ex_\<tau>1_inv:
  fixes ls ts1 m1 ws ts2 m2 cts
  defines "s1' \<equiv> activate_cond_actions1 (ls, (ts1, m1), ws) (ls, (ts2, m2), ws) cts"
  assumes inv: "r1.wfs_inv"
  and tbisim: "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (ts1 t') m1 (ts2 t') m2"
  and ts1t: "ts1 t = \<lfloor>xln\<rfloor>"
  and ts2t: "ts2 t = \<lfloor>xln'\<rfloor>"
  and ct: "r2.cond_action_oks (ls, (ts2, m2), ws) t cts"
  shows "\<tau>mRed1 (ls, (ts1, m1), ws) s1'" 
  and "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (thr s1' t') m1 (ts2 t') m2"
  and "r1.cond_action_oks s1' t cts"
  and "thr s1' t = \<lfloor>xln\<rfloor>"
using tbisim ts1t ct unfolding s1'_def
proof(induct cts arbitrary: ts1)
  case (Cons ct cts)
  note IH1 = `\<And>ts1. \<lbrakk>\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (ts1 t') m1 (ts2 t') m2; ts1 t = \<lfloor>xln\<rfloor>;
                    r2.cond_action_oks (ls, (ts2, m2), ws) t cts\<rbrakk>
              \<Longrightarrow> \<tau>mred1\<^sup>*\<^sup>* (ls, (ts1, m1), ws) (activate_cond_actions1 (ls, (ts1, m1), ws) (ls, (ts2, m2), ws) cts)`
  note IH2 = `\<And>t' ts1. \<lbrakk>t' \<noteq> t; \<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (ts1 t') m1 (ts2 t') m2; ts1 t = \<lfloor>xln\<rfloor>;
                        r2.cond_action_oks (ls, (ts2, m2), ws) t cts\<rbrakk>
           \<Longrightarrow> tbisim (ws t' = None) t' (thr (activate_cond_actions1 (ls, (ts1, m1), ws) (ls, (ts2, m2), ws) cts) t') m1 (ts2 t') m2`
  note IH3 = `\<And>ts1. \<lbrakk>\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (ts1 t') m1 (ts2 t') m2; ts1 t = \<lfloor>xln\<rfloor>;
                     r2.cond_action_oks (ls, (ts2, m2), ws) t cts\<rbrakk>
              \<Longrightarrow> r1.cond_action_oks (activate_cond_actions1 (ls, (ts1, m1), ws) (ls, (ts2, m2), ws) cts) t cts`
  note IH4 = `\<And>ts1. \<lbrakk>\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (ts1 t') m1 (ts2 t') m2; ts1 t = \<lfloor>xln\<rfloor>;
                     r2.cond_action_oks (ls, (ts2, m2), ws) t cts\<rbrakk>
              \<Longrightarrow> thr (activate_cond_actions1 (ls, (ts1, m1), ws) (ls, (ts2, m2), ws) cts) t = \<lfloor>xln\<rfloor>`
  { fix ts1
    assume tbisim: "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (ts1 t') m1 (ts2 t') m2"
      and ts1t: "ts1 t = \<lfloor>xln\<rfloor>"
      and ct: "r2.cond_action_oks (ls, (ts2, m2), ws) t (ct # cts)"
    from ct have 1: "r2.cond_action_ok (ls, (ts2, m2), ws) t ct"
      and 2: "r2.cond_action_oks (ls, (ts2, m2), ws) t cts" by auto
    let ?s1' = "activate_cond_action1 (ls, (ts1, m1), ws) (ls, (ts2, m2), ws) ct"
    from cond_actions_ok_bisim_ex_\<tau>1_inv[OF inv tbisim, OF _ ts1t ts2t 1]
    have tbisim': "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (thr ?s1' t') m1 (ts2 t') m2"
      and red: "\<tau>mRed1 (ls, (ts1, m1), ws) ?s1'" and ct': "r1.cond_action_ok ?s1' t ct" 
      and ts1't: "thr ?s1' t = \<lfloor>xln\<rfloor>" by blast+
    let ?s1'' = "activate_cond_actions1 ?s1' (ls, (ts2, m2), ws) cts"
    have "locks ?s1' = ls" "shr ?s1' = m1" "wset ?s1' = ws" by simp_all
    hence s1': "(ls, (thr ?s1', m1), ws) = ?s1'"
      by(cases "?s1'") auto
    from IH1[OF tbisim', OF _ ts1't 2] s1' have red': "\<tau>mRed1 ?s1' ?s1''" by simp
    with red show "\<tau>mRed1 (ls, (ts1, m1), ws) (activate_cond_actions1 (ls, (ts1, m1), ws) (ls, (ts2, m2), ws) (ct # cts))"
      by auto
    { fix t'
      assume t't: "t' \<noteq> t"
      from IH2[OF t't tbisim', OF _ ts1't 2] s1'
      show "tbisim (ws t' = None) t' (thr (activate_cond_actions1 (ls, (ts1, m1), ws) (ls, (ts2, m2), ws) (ct # cts)) t') m1 (ts2 t') m2"
	by auto }
    from red' ct' have "r1.cond_action_ok ?s1'' t ct" by(rule cond_actions_ok_\<tau>mRed1_inv)
    with IH3[OF tbisim', OF _ ts1't 2] s1'
    show "r1.cond_action_oks (activate_cond_actions1 (ls, (ts1, m1), ws) (ls, (ts2, m2), ws) (ct # cts)) t (ct # cts)"
      by auto
    from ts1't IH4[OF tbisim', OF _ ts1't 2] s1'
    show "thr (activate_cond_actions1 (ls, (ts1, m1), ws) (ls, (ts2, m2), ws) (ct # cts)) t = \<lfloor>xln\<rfloor>" by auto }
qed(auto)

lemma cond_actions_ok_bisim_ex_\<tau>2_inv:
  fixes ls ts1 m1 ws ts2 m2 ct
  defines "s2' \<equiv> activate_cond_action2 (ls, (ts1, m1), ws) (ls, (ts2, m2), ws) ct"
  assumes inv: "r2.wfs_inv"
  and mbisim: "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (ts1 t') m1 (ts2 t') m2"
  and ts1t: "ts1 t = \<lfloor>xln\<rfloor>"
  and ts2t: "ts2 t = \<lfloor>xln'\<rfloor>"
  and ct: "r1.cond_action_ok (ls, (ts1, m1), ws) t ct"
  shows "\<tau>mRed2 (ls, (ts2, m2), ws) s2'"
  and "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (ts1 t') m1 (thr s2' t') m2"
  and "r2.cond_action_ok s2' t ct"
  and "thr s2' t = \<lfloor>xln'\<rfloor>"
unfolding s2'_def
by(blast intro: FWdelay_bisimulation_final_base.cond_actions_ok_bisim_ex_\<tau>1_inv[OF FWdelay_bisimulation_final_base_flip, where bisim_wait = "flip bisim_wait", unfolded flip_simps, OF inv mbisim _ _ ct, OF _ ts2t ts1t])+

lemma cond_actions_oks_bisim_ex_\<tau>2_inv:
  fixes ls ts1 m1 ws ts2 m2 cts
  defines "s2' \<equiv> activate_cond_actions2 (ls, (ts1, m1), ws) (ls, (ts2, m2), ws) cts"
  assumes inv: "r2.wfs_inv"
  and tbisim: "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (ts1 t') m1 (ts2 t') m2"
  and ts1t: "ts1 t = \<lfloor>xln\<rfloor>"
  and ts2t: "ts2 t = \<lfloor>xln'\<rfloor>"
  and ct: "r1.cond_action_oks (ls, (ts1, m1), ws) t cts"
  shows "\<tau>mRed2 (ls, (ts2, m2), ws) s2'"
  and "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (ts1 t') m1 (thr s2' t') m2"
  and "r2.cond_action_oks s2' t cts"
  and "thr s2' t = \<lfloor>xln'\<rfloor>"
unfolding s2'_def
by(blast intro: FWdelay_bisimulation_final_base.cond_actions_oks_bisim_ex_\<tau>1_inv[OF FWdelay_bisimulation_final_base_flip, where bisim_wait = "flip bisim_wait", unfolded flip_simps, OF inv tbisim _ _ ct, OF _ ts2t ts1t])+

lemma mfinal1_inv_simulation:
  assumes "r2.wfs_inv" and "s1 \<approx>m s2" 
  shows "\<exists>s2'. r2.mthr.silent_moves s2 s2' \<and> s1 \<approx>m s2' \<and> (\<forall>t. r1.final_thread s1 t \<longrightarrow> r2.final_thread s2' t) \<and> shr s2' = shr s2"
proof -
  from `s1 \<approx>m s2` have "finite (dom (thr s1))" by(auto dest: mbisim_finite1)
  moreover have "{t. r1.final_thread s1 t} \<subseteq> dom (thr s1)" by(auto simp add: r1.final_thread_def)
  ultimately have "finite {t. r1.final_thread s1 t}" by(blast intro: finite_subset)
  thus ?thesis using `s1 \<approx>m s2`
  proof(induct A\<equiv>"{t. r1.final_thread s1 t}" arbitrary: s1 s2 rule: finite_induct)
    case empty
    from `{} = {t. r1.final_thread s1 t}`[symmetric] have "\<forall>t. \<not> r1.final_thread s1 t" by(auto)
    with `s1 \<approx>m s2` show ?case by blast
  next
    case (insert t A)
    def s1' == "(locks s1, ((thr s1)(t := None), shr s1), wset s1)"
    def s2' == "(locks s2, ((thr s2)(t := None), shr s2), wset s2)"
    from `t \<notin> A` `insert t A = {t. r1.final_thread s1 t}` have "A = {t. r1.final_thread s1' t}"
      unfolding s1'_def by(auto simp add: r1.final_thread_def)
    moreover from `insert t A = {t. r1.final_thread s1 t}` have "r1.final_thread s1 t" by auto
    hence "wset s1 t = None" by(auto simp add: r1.final_thread_def)
    with `s1 \<approx>m s2` have "s1' \<approx>m s2'" unfolding s1'_def s2'_def
      by(auto simp add: mbisim_def intro: tbisim_NoneI intro!: wset_thread_okI dest: wset_thread_okD split: split_if_asm)
    ultimately have "\<exists>s2''. r2.mthr.silent_moves s2' s2'' \<and> s1' \<approx>m s2'' \<and> (\<forall>t. r1.final_thread s1' t \<longrightarrow> r2.final_thread s2'' t) \<and> shr s2'' = shr s2'" by(rule insert)
    then obtain s2'' where reds: "r2.mthr.silent_moves s2' s2''" 
      and "s1' \<approx>m s2''" and fin: "\<And>t. r1.final_thread s1' t \<Longrightarrow> r2.final_thread s2'' t" and "shr s2'' = shr s2'" by blast
    have "thr s2' t = None" unfolding s2'_def by simp
    with `r2.mthr.silent_moves s2' s2''`
    have "r2.mthr.silent_moves (locks s2', (thr s2'(t \<mapsto> the (thr s2 t)), shr s2'), wset s2')
      (locks s2'', (thr s2''(t \<mapsto> the (thr s2 t)), shr s2''), wset s2'')"
      by(rule r2.\<tau>mRedT_add_thread_inv)
    also let ?s2'' = "(locks s2, (thr s2''(t \<mapsto> the (thr s2 t)), shr s2), wset s2)"
    from `shr s2'' = shr s2'` `s1' \<approx>m s2''` `s1 \<approx>m s2`
    have "(locks s2'', (thr s2''(t \<mapsto> the (thr s2 t)), shr s2''), wset s2'') = ?s2''"
      unfolding s2'_def s1'_def by(simp add: mbisim_def)
    also from `s1 \<approx>m s2` have "dom (thr s1) = dom (thr s2)" by(rule mbisim_dom_eq)
    with `insert t A = {t. r1.final_thread s1 t}` have "t \<in> dom (thr s2)" by(force simp add: r1.final_thread_def)
    then obtain x2 ln where tst2: "thr s2 t = \<lfloor>(x2, ln)\<rfloor>" by auto
    hence "(locks s2', (thr s2'(t \<mapsto> the (thr s2 t)), shr s2'), wset s2') = s2"
      unfolding s2'_def by(cases s2)(auto intro!: ext)
    also from `s1 \<approx>m s2` tst2 obtain x1
      where tst1: "thr s1 t = \<lfloor>(x1, ln)\<rfloor>"
      and bisim: "t \<turnstile> (x1, shr s1) \<approx> (x2, shr s2)" by(auto dest: mbisim_thrD2)
    from `shr s2'' = shr s2'` have "shr ?s2'' = shr s2" by(simp add: s2'_def)
    from `insert t A = {t. r1.final_thread s1 t}` tst1
    have final: "final1 x1" "ln = no_wait_locks" "wset s1 t = None" by(auto simp add: r1.final_thread_def)
    with final1_simulation[OF bisim] `shr ?s2'' = shr s2` obtain x2' m2'
      where red: "r2.silent_moves t (x2, shr ?s2'') (x2', m2')"
      and bisim': "t \<turnstile> (x1, shr s1) \<approx> (x2', m2')" and "final2 x2'" by auto
    from `wset s1 t = None` `s1 \<approx>m s2` have "wset s2 t = None" by(simp add: mbisim_def) 
    with bisim r2.silent_moves_into_RedT_\<tau>_inv[OF `r2.wfs_inv` red] tst2 `ln = no_wait_locks`
    have "r2.mthr.silent_moves ?s2'' (redT_upd ?s2'' t \<epsilon> x2' m2')" unfolding s2'_def by auto
    also (rtranclp_trans)
    from bisim r2.red_rtrancl_\<tau>_heapD_inv[OF `r2.wfs_inv` red] have "m2' = shr s2" by auto
    hence "s1 \<approx>m (redT_upd ?s2'' t \<epsilon> x2' m2')"
      using `s1' \<approx>m s2''` `s1 \<approx>m s2` tst1 tst2 `shr ?s2'' = shr s2` bisim' `shr s2'' = shr s2'` `wset s2 t = None`
      unfolding s1'_def s2'_def by(auto simp add: mbisim_def redT_updLns_def split: split_if_asm intro: tbisim_SomeI)
    moreover { 
      fix t'
      assume "r1.final_thread s1 t'"
      with fin[of t'] `final2 x2'` tst2 `ln = no_wait_locks` `wset s2 t = None` `s1' \<approx>m s2''` `s1 \<approx>m s2`
      have "r2.final_thread (redT_upd ?s2'' t \<epsilon> x2' m2') t'" unfolding s1'_def
	by(auto split: split_if_asm
                simp add: r2.final_thread_def r1.final_thread_def redT_updLns_def finfun_Diag_const2 o_def mbisim_def)
    }
    moreover have "shr (redT_upd ?s2'' t \<epsilon> x2' m2') = shr s2" using `m2' = shr s2` by simp
    ultimately show ?case by blast
  qed
qed

lemma mfinal2_inv_simulation:
  "\<lbrakk> r1.wfs_inv; s1 \<approx>m s2 \<rbrakk>
  \<Longrightarrow> \<exists>s1'. r1.mthr.silent_moves s1 s1' \<and> s1' \<approx>m s2 \<and> (\<forall>t. r2.final_thread s2 t \<longrightarrow> r1.final_thread s1' t) \<and> shr s1' = shr s1"
using FWdelay_bisimulation_final_base.mfinal1_inv_simulation[OF FWdelay_bisimulation_final_base_flip, where bisim_wait="flip bisim_wait"]
by(unfold flip_simps)

lemma mfinal1_simulation:
  assumes "r2.wfs_inv" and "s1 \<approx>m s2" and "r1.mfinal s1"
  shows "\<exists>s2'. r2.mthr.silent_moves s2 s2' \<and> s1 \<approx>m s2' \<and> r2.mfinal s2' \<and> shr s2' = shr s2"
proof -
  from mfinal1_inv_simulation[OF `r2.wfs_inv` `s1 \<approx>m s2`]
  obtain s2' where 1: "r2.mthr.silent_moves s2 s2'" "s1 \<approx>m s2'" "shr s2' = shr s2"
    and fin: "\<And>t. r1.final_thread s1 t \<Longrightarrow> r2.final_thread s2' t" by blast
  have "r2.mfinal s2'"
  proof(rule r2.mfinalI)
    fix t x2 ln
    assume "thr s2' t = \<lfloor>(x2, ln)\<rfloor>"
    with `s1 \<approx>m s2'` obtain x1 where "thr s1 t = \<lfloor>(x1, ln)\<rfloor>" "t \<turnstile> (x1, shr s1) \<approx> (x2, shr s2')"
      by(auto dest: mbisim_thrD2)
    from `thr s1 t = \<lfloor>(x1, ln)\<rfloor>` `r1.mfinal s1` have "r1.final_thread s1 t"
      by(auto elim!: r1.mfinalE simp add: r1.final_thread_def)
    hence "r2.final_thread s2' t" by(rule fin)
    thus "final2 x2 \<and> ln = no_wait_locks \<and> wset s2' t = None"
      using `thr s2' t = \<lfloor>(x2, ln)\<rfloor>` by(auto simp add: r2.final_thread_def)
  qed
  with 1 show ?thesis by blast
qed
    
lemma mfinal2_simulation:
  "\<lbrakk> r1.wfs_inv; s1 \<approx>m s2; r2.mfinal s2 \<rbrakk>
  \<Longrightarrow> \<exists>s1'. r1.mthr.silent_moves s1 s1' \<and> s1' \<approx>m s2 \<and> r1.mfinal s1' \<and> shr s1' = shr s1"
using FWdelay_bisimulation_final_base.mfinal1_simulation[OF FWdelay_bisimulation_final_base_flip, where bisim_wait = "flip bisim_wait"]
by(unfold flip_simps)

end

locale FWdelay_bisimulation_obs =
  FWdelay_bisimulation_final_base _ _ _ _ _ _ \<tau>move1 \<tau>move2
  for \<tau>move1 :: "('l,'t,'x1,'m1,'w, 'o) \<tau>moves"
  and \<tau>move2 :: "('l,'t,'x2,'m2,'w, 'o) \<tau>moves" +
  assumes delay_bisimulation_obs_locale: "delay_bisimulation_obs (r1 t) (r2 t) (bisim t) (ta_bisim bisim) \<tau>move1 \<tau>move2"
  and bisim_inv_red_other:
   "\<lbrakk> t' \<turnstile> (x, m1) \<approx> (xx, m2); t \<turnstile> (x1, m1) \<approx> (x2, m2); 
      r1.silent_moves t (x1, m1) (x1', m1);
      t \<turnstile> (x1', m1) -1-ta1\<rightarrow> (x1'', m1'); \<not> \<tau>move1 (x1', m1) ta1 (x1'', m1');
      r2.silent_moves t (x2, m2) (x2', m2);
      t \<turnstile> (x2', m2) -2-ta2\<rightarrow> (x2'', m2'); \<not> \<tau>move2 (x2', m2) ta2 (x2'', m2');
      t \<turnstile> (x1'', m1') \<approx> (x2'', m2'); ta_bisim bisim ta1 ta2 \<rbrakk>
   \<Longrightarrow> t' \<turnstile> (x, m1') \<approx> (xx, m2')"
  and bisim_waitI:
   "\<lbrakk> t \<turnstile> (x1, m1) \<approx> (x2, m2); r1.silent_moves t (x1, m1) (x1', m1);
      t \<turnstile> (x1', m1) -1-ta1\<rightarrow> (x1'', m1'); \<not> \<tau>move1 (x1', m1) ta1 (x1'', m1');
      r2.silent_moves t (x2, m2) (x2', m2);
      t \<turnstile> (x2', m2) -2-ta2\<rightarrow> (x2'', m2'); \<not> \<tau>move2 (x2', m2) ta2 (x2'', m2');
      t \<turnstile> (x1'', m1') \<approx> (x2'', m2'); ta_bisim bisim ta1 ta2;
      Suspend w \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub>; Suspend w \<in> set \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub> \<rbrakk>
   \<Longrightarrow> x1'' \<approx>w x2''"
  and simulation_Notified1:
    "\<lbrakk> t \<turnstile> (x1, m1) \<approx> (x2, m2); x1 \<approx>w x2; t \<turnstile> (x1, m1) -1-\<epsilon>\<lbrace>\<^bsub>c\<^esub> Notified\<rbrace>\<rightarrow> (x1', m1) \<rbrakk>
    \<Longrightarrow> \<exists>x2'. t \<turnstile> (x2, m2) -2-\<epsilon>\<lbrace>\<^bsub>c\<^esub> Notified\<rbrace>\<rightarrow> (x2', m2) \<and> t \<turnstile> (x1', m1) \<approx> (x2', m2)"
  and simulation_Notified2:
    "\<lbrakk> t \<turnstile> (x1, m1) \<approx> (x2, m2); x1 \<approx>w x2; t \<turnstile> (x2, m2) -2-\<epsilon>\<lbrace>\<^bsub>c\<^esub> Notified\<rbrace>\<rightarrow> (x2', m2) \<rbrakk>
    \<Longrightarrow> \<exists>x1'. t \<turnstile> (x1, m1) -1-\<epsilon>\<lbrace>\<^bsub>c\<^esub> Notified\<rbrace>\<rightarrow> (x1', m1) \<and> t \<turnstile> (x1', m1) \<approx> (x2', m2)"
  and simulation_Interrupted1:
    "\<lbrakk> t \<turnstile> (x1, m1) \<approx> (x2, m2); x1 \<approx>w x2; t \<turnstile> (x1, m1) -1-ta1\<rightarrow> (x1', m1'); is_Interrupted_ta ta1 \<rbrakk>
    \<Longrightarrow> \<exists>x2' m2' ta2. t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2') \<and> t \<turnstile> (x1', m1') \<approx> (x2', m2') \<and> ta_bisim bisim ta1 ta2"
  and simulation_Interrupted2:
    "\<lbrakk> t \<turnstile> (x1, m1) \<approx> (x2, m2); x1 \<approx>w x2; t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2'); is_Interrupted_ta ta2 \<rbrakk>
    \<Longrightarrow> \<exists>x1' m1' ta1. t \<turnstile> (x1, m1) -1-ta1\<rightarrow> (x1', m1') \<and> t \<turnstile> (x1', m1') \<approx> (x2', m2') \<and> ta_bisim bisim ta1 ta2"

sublocale FWdelay_bisimulation_obs <
  delay_bisimulation_obs "r1 t" "r2 t" "bisim t" "ta_bisim bisim" \<tau>move1 \<tau>move2 for t
by(rule delay_bisimulation_obs_locale)

context FWdelay_bisimulation_obs begin

lemma FWdelay_bisimulation_obs_flip:
  "FWdelay_bisimulation_obs final2 r2 final1 r1 (\<lambda>t. flip (bisim t)) (flip bisim_wait) \<tau>move2 \<tau>move1"
apply(rule FWdelay_bisimulation_obs.intro)
 apply(rule FWdelay_bisimulation_final_base_flip)
apply(rule FWdelay_bisimulation_obs_axioms.intro)
      apply(unfold flip_simps)
      apply(rule delay_bisimulation_obs_axioms)
     apply(erule (9) bisim_inv_red_other)
    apply(erule (10) bisim_waitI)
   apply(erule (2) simulation_Notified2)
  apply(erule (2) simulation_Notified1)
 apply(erule (3) simulation_Interrupted2)
apply(erule (3) simulation_Interrupted1)
done

end

lemma FWdelay_bisimulation_obs_flip_simps [flip_simps]:
  "FWdelay_bisimulation_obs final2 r2 final1 r1 (\<lambda>t. flip (bisim t)) (flip bisim_wait) \<tau>move2 \<tau>move1 = 
   FWdelay_bisimulation_obs final1 r1 final2 r2 bisim bisim_wait \<tau>move1 \<tau>move2"
by(auto dest: FWdelay_bisimulation_obs.FWdelay_bisimulation_obs_flip simp only: flip_flip)

lemma ta_bisim_is_Interrupted_ta_eq: -- "Move to above"
  "ta_bisim bisim ta1 ta2 \<Longrightarrow> is_Interrupted_ta ta1 \<longleftrightarrow> is_Interrupted_ta ta2"
by(auto simp add: is_Interrupted_ta_def ta_bisim_def)

context FWdelay_bisimulation_obs begin

lemma redTW_simulation1_not_Suspend:
  assumes "r1.redTW t wa s1 obs s1'"
  and mbisim: "s1 \<approx>m s2"
  and Suspend: "\<And>w. wa \<noteq> Suspend w"
  shows "\<exists>s2'. r2.redTW t wa s2 obs s2' \<and> s1' \<approx>m s2'"
proof -
  obtain ls1 ts1 m1 ws1 where s1: "s1 = (ls1, (ts1, m1), ws1)" by(cases s1) auto
  obtain ls2 ts2 m2 ws2 where s2: "s2 = (ls2, (ts2, m2), ws2)" by(cases s2) auto
  obtain ls1' ts1' m1' ws1' where s1': "s1' = (ls1', (ts1', m1'), ws1')" by(cases s1') auto
  from mbisim s1 s2 have [simp]: "ws2 = ws1" "ls2 = ls1" by(simp_all add: mbisim_def)
  from `r1.redTW t wa s1 obs s1'`
  have "\<exists>ls2' ts2' m2' ws2'. r2.redTW t wa (ls2, (ts2, m2), ws2) obs (ls2', (ts2', m2'), ws2') \<and>
                             (ls1', (ts1', m1'), ws1') \<approx>m (ls2', (ts2', m2'), ws2')"
  proof cases
    case redTW_Suspend with Suspend show ?thesis by fastsimp
  next
    case redTW_NotifyNone
    with mbisim s1 s2 s1' show ?thesis
      by(fastsimp intro: r2.redTW_NotifyNone simp add: mbisim_def)
  next
    case (redTW_NotifySome t' w x1')
    with s1 s1' have [simp]: "ls1' = ls1" "m1' = m1" "wa = Notify w" "ws1' = ws1(t' := None)" "obs = []"
      and ts1': "ts1' = ts1(t' := Option.map (\<lambda>(x, ln). (x1', ln)) (ts1 t'))"
      and red: "\<And>x ln. ts1 t' = \<lfloor>(x, ln)\<rfloor> \<Longrightarrow> t' \<turnstile> (x, m1) -1-\<epsilon>\<lbrace>\<^bsub>c\<^esub>Notified\<rbrace>\<rightarrow> (x1', m1)"
      and wst: "ws1 t' = \<lfloor>w\<rfloor>" by auto
    show ?thesis
    proof(cases "ts1 t'")
      case None
      with mbisim_thrNone_eq[OF mbisim, of t'] s1 s2 have "ts2 t' = None" by simp
      hence "r2.redTW t wa (ls2, (ts2, m2), ws2) obs (ls2, (ts2, m2), ws2(t' := None))"
        using wst by(fastsimp intro: r2.redTW_NotifySome ext)
      moreover have "(ls1', (ts1', m1'), ws1') \<approx>m (ls2, (ts2, m2), ws2(t' := None))"
        using ts1' mbisim s1 s2 None `ts2 t' = None`
        by(auto simp add: mbisim_def intro: tbisim_NoneI wset_thread_ok_upd_None)
      ultimately show ?thesis by(auto simp add: s1 s2 s1')
    next
      case (Some a)
      then obtain x1 ln where ts1t: "ts1 t' = \<lfloor>(x1, ln)\<rfloor>" by(cases a) auto
      from mbisim_thrD1[OF mbisim, simplified thr_conv s1, OF ts1t] wst s2
      obtain x2 where ts2t: "ts2 t' = \<lfloor>(x2, ln)\<rfloor>"
        and bisim: "t' \<turnstile> (x1, m1) \<approx> (x2, m2)"
        and bisimw: "x1 \<approx>w x2" by auto
      from ts1t have red1: "t' \<turnstile> (x1, m1) -1-\<epsilon>\<lbrace>\<^bsub>c\<^esub>Notified\<rbrace>\<rightarrow> (x1', m1)" by(rule red)
      from simulation_Notified1[OF bisim bisimw red1]
      obtain x2' where red2: "t' \<turnstile> (x2, m2) -2-\<epsilon>\<lbrace>\<^bsub>c\<^esub>Notified\<rbrace>\<rightarrow> (x2', m2)"
        and bisim': "t' \<turnstile> (x1', m1) \<approx> (x2', m2)" by blast
      from ts2t red2 wst have "r2.redTW t wa (ls2, (ts2, m2), ws2) obs (ls2, (ts2(t' \<mapsto> (x2', ln)), m2), ws2(t' := None))"
        by(auto intro: r2.redTW_NotifySome)
      moreover have "(ls1', (ts1', m1'), ws1') \<approx>m (ls2, (ts2(t' \<mapsto> (x2', ln)), m2), ws2(t' := None))"
        using ts1' ts1t mbisim s1 s2 bisim'
        by(auto simp add: mbisim_def intro: tbisim_SomeI wset_thread_ok_upd_Some)
      ultimately show ?thesis by auto
    qed
  next
    case (redTW_NotifyAll w x1')
    with s1 s1' s2 have [simp]: "ls1' = ls1" "m1' = m1" "wa = NotifyAll w"
      and ws1': "ws1' = (\<lambda>t'. if ws1 t' = \<lfloor>w\<rfloor> then None else ws1 t')"
      and ts1': "ts1' = (\<lambda>t'. if ws1 t' = \<lfloor>w\<rfloor> then Option.map (\<lambda>(x, ln). (x1' t', ln)) (ts1 t') else ts1 t')"
      and reds: "\<And>t' x1 ln. \<lbrakk> ws1 t' = \<lfloor>w\<rfloor>; ts1 t' = \<lfloor>(x1, ln)\<rfloor> \<rbrakk> \<Longrightarrow> t' \<turnstile> (x1, m1) -1-\<epsilon>\<lbrace>\<^bsub>c\<^esub>Notified\<rbrace>\<rightarrow> (x1' t', m1)"
      by(auto cong: if_cong)
    let ?x2' = "\<lambda>t'. SOME x'. t' \<turnstile> (fst (the (ts2 t')), m2) -2-\<epsilon>\<lbrace>\<^bsub>c\<^esub>Notified\<rbrace>\<rightarrow> (x', m2) \<and> t' \<turnstile> (x1' t', m1) \<approx> (x', m2)"
    let ?ts2' = "\<lambda>t'. if ws1 t' = \<lfloor>w\<rfloor> then Option.map (\<lambda>(x, ln). (?x2' t', ln)) (ts2 t') else ts2 t'"
    let ?s2' = "(ls2, (?ts2', m2), ws1')"
    { fix t' x2 ln
      assume ws1t': "ws1 t' = \<lfloor>w\<rfloor>"
        and ts2t': "ts2 t' = \<lfloor>(x2, ln)\<rfloor>"
      with mbisim_thrD2[OF mbisim, of t' x2 ln] s2 s1
      obtain x1 where "ts1 t' = \<lfloor>(x1, ln)\<rfloor>" 
        and bisim: "t' \<turnstile> (x1, m1) \<approx> (x2, m2)"
        and bisimw: "x1 \<approx>w x2" by auto
      let ?P = "\<lambda>x'. t' \<turnstile> (x2, m2) -2-\<epsilon>\<lbrace>\<^bsub>c\<^esub> Notified\<rbrace>\<rightarrow> (x', m2) \<and> t' \<turnstile> (x1' t', m1) \<approx> (x', m2)"
      from ws1t' `ts1 t' = \<lfloor>(x1, ln)\<rfloor>` have "t' \<turnstile> (x1, m1) -1-\<epsilon>\<lbrace>\<^bsub>c\<^esub>Notified\<rbrace>\<rightarrow> (x1' t', m1)" by(rule reds)
      with bisim bisimw have "\<exists>x2'. ?P x2'" by(rule simulation_Notified1)
      hence "?P (Eps ?P)" by(rule someI_ex) }
    note reds2 = this
    hence "r2.redTW t wa s2 obs ?s2'" unfolding `wa = NotifyAll w` `obs = []`
      by -(rule r2.redTW_NotifyAll[where x'="?x2'"], simp_all add: s2 ws1' expand_fun_eq cong: if_cong)
    moreover {
      have "dom ts1' = dom ts1" unfolding ts1' by(auto split: split_if_asm)
      moreover from mbisim_wset_thread_ok1[OF mbisim]
      have "wset_thread_ok ws1' ts1'" unfolding ts1' ws1' s1
        by(fastsimp intro!: wset_thread_okI dest: wset_thread_okD)
      ultimately have "(ls1, (ts1', m1), ws1') \<approx>m ?s2'" using mbisim mbisim_thrNone_eq[OF mbisim] reds2
        unfolding ts1' ws1' s1 s1' s2 by(fastsimp simp add: mbisim_def tbisim_def)
    }
    ultimately show ?thesis unfolding s2 by auto
  next
    case redTW_InterruptNone
    thus ?thesis using mbisim unfolding s1 s2 s1'
      by(fastsimp intro: r2.redTW_InterruptNone)
  next
    case (redTW_InterruptWait t' w M1' ta1 x1')
    with s1 s1' have [simp]: "ws1' = ws1(t' := None)" "ls1' = ls1" "wa = Interrupt t'" "ws1 t' = \<lfloor>w\<rfloor>"
      and obs: "obs = observable_of \<lbrace>ta1\<rbrace>\<^bsub>o\<^esub>"
      and ts1': "ts1' = ts1(t' := Option.map (\<lambda>(x, ln). (x1', ln)) (ts1 t'))"
      and red: "case ts1 t' of None \<Rightarrow> m1' = m1 \<and> ta1 = \<epsilon>\<lbrace>\<^bsub>c\<^esub>Interrupted\<rbrace> | \<lfloor>(x1, ln)\<rfloor> \<Rightarrow> t' \<turnstile> (x1, m1) -1-ta1\<rightarrow> (x1', m1')"
      and ta1: "is_Interrupted_ta ta1"
      by auto
    show ?thesis
    proof(cases "ts1 t'")
      case None
      with obs red have obs: "obs = observable_of \<lbrace>\<epsilon>\<lbrace>\<^bsub>c\<^esub>Interrupted\<rbrace> :: ('l,'t,'x2,'m2,'w,'o list) thread_action\<rbrace>\<^bsub>o\<^esub>"
        by(simp add: ta_upd_simps)
      from None mbisim_thrNone_eq[OF mbisim, of t'] s1 s2
      have "ts2 t' = None" by auto
      hence "r2.redTW t wa s2 obs (ls1, (ts2, m2), ws1')"
        using s2 ta1 unfolding obs `wa = Interrupt t'`
        by -(rule r2.redTW_InterruptWait, auto simp add: expand_fun_eq is_Interrupted_ta_def ta_upd_simps)
      moreover from None red have "m1' = m1" by simp
      with mbisim s1 s2 s1' ts1' None `ts2 t' = None`
      have "s1' \<approx>m (ls1, (ts2, m2), ws1')"
        by(auto simp add: mbisim_def intro: tbisim_NoneI wset_thread_ok_upd_None)
      ultimately show ?thesis unfolding s2 s1' by blast
    next
      case (Some a)
      then obtain x1 ln where ts1t': "ts1 t' = \<lfloor>(x1, ln)\<rfloor>" by(cases a) auto
      with mbisim_thrD1[OF mbisim, of t' x1 ln] s1 s2 obtain x2 where ts2t': "ts2 t' = \<lfloor>(x2, ln)\<rfloor>"
        and bisim: "t' \<turnstile> (x1, m1) \<approx> (x2, m2)" and bisimw: "x1 \<approx>w x2" by auto
      from ts1t' red have red1: "t' \<turnstile> (x1, m1) -1-ta1\<rightarrow> (x1', m1')" by simp
      from simulation_Interrupted1[OF bisim bisimw red1 ta1]
      obtain x2' m2' ta2 where red2: "t' \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2')"
        and bisim': "t' \<turnstile> (x1', m1') \<approx> (x2', m2')" 
        and tbisim: "ta1 \<sim>m ta2" by blast
      let ?s2' = "(ls2, (ts2(t' \<mapsto> (x2', ln)), m2'), ws2(t' := None))"
      from tbisim ta1 have ta2: "is_Interrupted_ta ta2" by(simp add: ta_bisim_is_Interrupted_ta_eq)
      with ts2t' red2 have "r2.redTW t wa (ls2, (ts2, m2), ws2) (observable_of \<lbrace>ta2\<rbrace>\<^bsub>o\<^esub>) ?s2'"
        by(auto intro: r2.redTW_InterruptWait)
      moreover have "s1' \<approx>m ?s2'"
      proof(rule mbisimI)
        from mbisim s1 s1' show "finite (dom (thr s1'))" "locks s1' = locks ?s2'" "wset s1' = wset ?s2'"
          by(auto simp add: mbisim_def ts1')
      next
        fix t
        assume "thr s1' t = None"
        with mbisim_thrNone_eq[OF mbisim, of t] s1' s1 s2 ts1' ts1t' show "thr ?s2' t = None" by auto
      next
        fix t x1 ln
        assume ts1't: "thr s1' t = \<lfloor>(x1, ln)\<rfloor>"
        show "\<exists>x2. thr ?s2' t = \<lfloor>(x2, ln)\<rfloor> \<and> t \<turnstile> (x1, shr s1') \<approx> (x2, shr ?s2') \<and> (wset ?s2' t = None \<or> x1 \<approx>w x2)"
        proof(cases "t = t'")
          case True
          thus ?thesis using bisim' ts1t' ts1't s1' ts1' by auto
        next
          case False
          with ts1't s1' ts1' have "ts1 t = \<lfloor>(x1, ln)\<rfloor>" by simp
          with mbisim_thrD1[OF mbisim, of t x1 ln] s1 s2 obtain x2
            where "ts2 t = \<lfloor>(x2, ln)\<rfloor>" and bisim12: "t \<turnstile> (x1, m1) \<approx> (x2, m2)"
            and bisimw12: "ws1 t = None \<or> x1 \<approx>w x2" by auto
          from bisim_inv_red_other[OF bisim12 bisim rtranclp.rtrancl_refl red1 _ rtranclp.rtrancl_refl red2 _ bisim' tbisim]
          have "t \<turnstile> (x1, m1') \<approx> (x2, m2')" using ta1 ta2
            by(fastsimp dest: r1.silent_tl r2.silent_tl simp add: is_Interrupted_ta_def)
          with bisim12 bisimw12 show ?thesis using False `ts1 t = \<lfloor>(x1, ln)\<rfloor>` `ts2 t = \<lfloor>(x2, ln)\<rfloor>` s1' by auto
        qed
      next
        from mbisim_wset_thread_ok1[OF mbisim] ts1t'
        show "wset_thread_ok (wset s1') (thr s1')" unfolding s1 s1' ts1'
          by(auto intro: wset_thread_ok_upd_Some)
      qed
      moreover from obs tbisim have "obs = observable_of \<lbrace>ta2\<rbrace>\<^bsub>o\<^esub>" by(simp add: ta_bisim_def)
      ultimately show ?thesis unfolding s1' by blast
    qed
  qed
  thus ?thesis unfolding s2 s1' by blast
qed

lemma redTW_simulation2_not_Suspend:
  "\<lbrakk> r2.redTW t wa s2 obs s2'; s1 \<approx>m s2; \<And>w. wa \<noteq> Suspend w \<rbrakk> \<Longrightarrow> \<exists>s1'. r1.redTW t wa s1 obs s1' \<and> s1' \<approx>m s2'"
using FWdelay_bisimulation_obs.redTW_simulation1_not_Suspend[OF FWdelay_bisimulation_obs_flip]
unfolding flip_simps .

lemma redTWs_simulation1_not_Suspend:
  assumes "r1.redTWs t was s1 obs s1'"
  and "s1 \<approx>m s2"
  and "\<And>w. Suspend w \<notin> set was"
  shows "\<exists>s2'. r2.redTWs t was s2 obs s2' \<and> s1' \<approx>m s2'"
using assms
proof(induct rule: r1.redTWs_converse_induct)
  case Nil thus ?case by(auto)
next
  case (snoc was wa obs obs' s1 s1' s1'')
  then obtain s2' where reds: "r2.redTWs t was s2 obs s2'" 
    and "s1' \<approx>m s2'" by auto
  from redTW_simulation1_not_Suspend[OF `r1.redTW t wa s1' obs' s1''` `s1' \<approx>m s2'`] `\<And>w. Suspend w \<notin> set (was @ [wa])`
  obtain s2'' where "r2.redTW t wa s2' obs' s2''" "s1'' \<approx>m s2''" by fastsimp
  with reds show ?case by(auto intro: r2.redTWs_snocI)
qed

lemma redTWs_simulation2_not_Suspend:
  "\<lbrakk> r2.redTWs t was s2 obs s2'; s1 \<approx>m s2; \<And>w. Suspend w \<notin> set was \<rbrakk> 
  \<Longrightarrow> \<exists>s1'. r1.redTWs t was s1 obs s1' \<and> s1' \<approx>m s2'"
using FWdelay_bisimulation_obs.redTWs_simulation1_not_Suspend[OF FWdelay_bisimulation_obs_flip]
unfolding flip_simps .

lemma redTWs_simulation1:
  assumes redTWs: "r1.redTWs t was s1 obs s1'"
  and mbisim: "s1 \<approx>m s2"
  and Suspend:
  "\<And>w. Suspend w \<in> set was
  \<Longrightarrow> Suspend w \<notin> set (butlast was) \<and> wset s1 t = None \<and> 
     (\<exists>x1 x2 ln1 ln2. thr s1 t = \<lfloor>(x1, ln1)\<rfloor> \<and> thr s2 t = \<lfloor>(x2, ln2)\<rfloor> \<and> x1 \<approx>w x2)"
  shows "\<exists>s2'. r2.redTWs t was s2 obs s2' \<and> s1' \<approx>m s2'"
proof(cases "\<exists>w. Suspend w \<in> set was")
  case False
  hence "\<And>w. Suspend w \<notin> set was" by simp
  with redTWs mbisim show ?thesis by(rule redTWs_simulation1_not_Suspend)
next
  case True
  then obtain w where "Suspend w \<in> set was" ..
  with Suspend obtain was' x1 ln1 x2 ln2 where was: "was = was' @ [Suspend w]"
    and Suspend': "\<And>w. Suspend w \<notin> set was'"
    and bisimw: "x1 \<approx>w x2"
    and ts1t: "thr s1 t = \<lfloor>(x1, ln1)\<rfloor>"
    and ts2t: "thr s2 t = \<lfloor>(x2, ln2)\<rfloor>"
    and ws1t: "wset s1 t = None"
    by(cases was rule: rev_cases) fastsimp+
  from redTWs[unfolded was] obtain S1' obs' obs''
    where redTWs': "r1.redTWs t was' s1 obs' S1'"
    and redTW: "r1.redTW t (Suspend w) S1' obs'' s1'"
    and obs: "obs = obs' @ obs''"
    by(auto dest: r1.redTWs_snocD)
  from redTW have [simp]: "obs'' = []" by(auto elim: r1.redTW_cases)
  from redTWs_simulation1_not_Suspend[OF redTWs' mbisim Suspend']
  obtain s2' where redTWs2: "r2.redTWs t was' s2 obs' s2'"
    and mbisim': "S1' \<approx>m s2'" by blast
  let ?s2' = "(locks s2', (thr s2', shr s2'), wset s2'(t \<mapsto> w))"
  have "r2.redTW t (Suspend w) s2' [] ?s2'" by(rule r2.redTW_Suspend refl)+
  with redTWs2 have "r2.redTWs t was s2 (obs' @ []) ?s2'" unfolding was by(rule r2.redTWs_snocI)
  moreover from mbisim ws1t have ws2t: "wset s2 t = None" by(simp add: mbisim_def)
  from r1.redTWs_thr_same_not_Suspend[OF redTWs' Suspend' ws1t]
    r2.redTWs_thr_same_not_Suspend[OF redTWs2 Suspend' this]
    mbisim' ts1t ts2t bisimw redTW
  have "s1' \<approx>m ?s2'"
    by(auto elim!: r1.redTW_cases simp add: mbisim_def intro!: wset_thread_okI dest: wset_thread_okD)
      (fastsimp simp add: tbisim_def)
  ultimately show ?thesis unfolding obs `obs'' = []` by blast
qed

lemma redTWs_simulation2:
  "\<lbrakk> r2.redTWs t was s2 obs s2'; s1 \<approx>m s2;
    \<And>w. Suspend w \<in> set was \<Longrightarrow> Suspend w \<notin> set (butlast was) \<and> wset s2 t = None \<and> 
                               (\<exists>x1 x2 ln1 ln2. thr s1 t = \<lfloor>(x1, ln)\<rfloor> \<and> thr s2 t = \<lfloor>(x2, ln2)\<rfloor> \<and> x1 \<approx>w x2) \<rbrakk>
  \<Longrightarrow> \<exists>s1'. r1.redTWs t was s1 obs s1' \<and> s1' \<approx>m s2'"
using FWdelay_bisimulation_obs.redTWs_simulation1[OF FWdelay_bisimulation_obs_flip, of t was s2 obs s2' s1]
unfolding flip_simps by blast

theorem mbisim_simulation1:
  assumes inv: "r2.wfs_inv" and mbisim: "mbisim s1 s2" and "\<not> m\<tau>move1 s1 tl1 s1'" "r1.redT s1 tl1 s1'"
  shows "\<exists>s2' s2'' tl2. r2.mthr.silent_moves s2 s2' \<and> r2.redT s2' tl2 s2'' \<and>
                        \<not> m\<tau>move2 s2' tl2 s2'' \<and> mbisim s1' s2'' \<and> mta_bisim tl1 tl2"
proof -
  from assms obtain t TA where tl1 [simp]: "tl1 = (t, TA)" and redT: "s1 -1-t\<triangleright>TA\<rightarrow> s1'"
    and m\<tau>: "\<not> m\<tau>move1 s1 (t, TA) s1'" by(cases tl1) fastsimp
  obtain ls1 ts1 m1 ws1 where [simp]: "s1 = (ls1, (ts1, m1), ws1)" by(cases s1, auto)
  obtain ls1' ts1' m1' ws1' where [simp]: "s1' = (ls1', (ts1', m1'), ws1')" by(cases s1', auto)
  obtain ls2 ts2 m2 ws2 where [simp]: "s2 = (ls2, (ts2, m2), ws2)" by(cases s2, auto)
  from mbisim have [simp]: "ls2 = ls1" "ws2 = ws1" "finite (dom ts1)" by(auto simp add: mbisim_def)
  from redT show ?thesis
  proof cases
    case (redT_normal x1 ta1 x1' M1' obs)
    hence [simp]: "TA = observable_ta_of ta1 obs"
      and red: "t \<turnstile> (x1, m1) -1-ta1\<rightarrow> (x1', M1')" and tst: "ts1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>"
      and wst: "ws1 t = None" and aoe: "r1.actions_ok s1 t ta1"
      and s1': "r1.redTWs t \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub> (redT_upd s1 t ta1 x1' M1') obs s1'" by auto
    from mbisim tst obtain x2 where tst': "ts2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>"
      and bisim: "t \<turnstile> (x1, m1) \<approx> (x2, m2)" by(auto dest: mbisim_thrD1)
    from m\<tau> have \<tau>: "\<not> \<tau>move1 (x1, m1) ta1 (x1', M1')"
    proof(rule contrapos_nn)
      assume \<tau>: "\<tau>move1 (x1, m1) ta1 (x1', M1')"
      moreover hence [simp]: "ta1 = \<epsilon>" by(rule r1.silent_tl)
      moreover have [simp]: "M1' = m1" by(rule r1.\<tau>move_heap[OF exI, OF bisim red \<tau>, symmetric])
      ultimately show "m\<tau>move1 s1 (t, TA) s1'" using s1' tst s1'
        by(clarsimp simp add: redT_updLs_def o_def simp del: observable_ta_of_empty_Nil)(rule r1.m\<tau>move.intros, auto elim: rtrancl3p_cases)
    qed
    from simulation1[OF bisim red this] obtain x2' M2' x2'' M2'' ta2
      where red21: "r2.silent_moves t (x2, m2) (x2', M2')"
      and red22: "t \<turnstile> (x2', M2') -2-ta2\<rightarrow> (x2'', M2'')" and \<tau>2: "\<not> \<tau>move2 (x2', M2') ta2 (x2'', M2'')"
      and bisim': "t \<turnstile> (x1', M1') \<approx> (x2'', M2'')"
      and tasim: "ta_bisim bisim ta1 ta2" by auto
    let ?s2' = "redT_upd s2 t (\<epsilon> :: ('l,'t,'x2,'m2,'w,'o list) thread_action) x2' M2'"
    let ?S2' = "activate_cond_actions2 s1 ?s2' \<lbrace>ta2\<rbrace>\<^bsub>c\<^esub>"
    let ?s2'' = "redT_upd ?S2' t ta2 x2'' M2''"
    from red21 tst' wst bisim have "\<tau>mRed2 s2 ?s2'"
      by -(rule r2.silent_moves_into_RedT_\<tau>_inv[OF inv], auto)
    also from red21 bisim have [simp]: "M2' = m2" by(auto dest: r2.red_rtrancl_\<tau>_heapD_inv[OF inv])
    from tasim have [simp]: "\<lbrace> ta1 \<rbrace>\<^bsub>l\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>l\<^esub>" "\<lbrace> ta1 \<rbrace>\<^bsub>w\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>w\<^esub>" "\<lbrace> ta1 \<rbrace>\<^bsub>c\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>c\<^esub>"
      and nta: "list_all2 (nta_bisim bisim) \<lbrace> ta1 \<rbrace>\<^bsub>t\<^esub> \<lbrace> ta2 \<rbrace>\<^bsub>t\<^esub>" by(auto simp add: ta_bisim_def)
    from mbisim have tbisim: "\<And>t. tbisim (ws1 t = None) t (ts1 t) m1 (ts2 t) m2" by(simp add: mbisim_def)
    hence tbisim': "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws1 t' = None) t' (ts1 t') m1 (thr ?s2' t') m2" by(auto)
    from aoe have cao1: "r1.cond_action_oks (ls1, (ts1, m1), ws1) t \<lbrace>ta2\<rbrace>\<^bsub>c\<^esub>" by auto
    from tst' have "thr ?s2' t = \<lfloor>(x2', no_wait_locks)\<rfloor>" by(auto simp add: redT_updLns_def o_def finfun_Diag_const2)
    from cond_actions_oks_bisim_ex_\<tau>2_inv[OF inv tbisim', OF _ tst this cao1]
    have red21': "\<tau>mRed2 ?s2' ?S2'" and tbisim'': "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws1 t' = None) t' (ts1 t') m1 (thr ?S2' t') m2"
      and cao2: "r2.cond_action_oks ?S2' t \<lbrace>ta2\<rbrace>\<^bsub>c\<^esub>" and tst'': "thr ?S2' t = \<lfloor>(x2', no_wait_locks)\<rfloor>"
      by(auto simp del: fun_upd_apply)
    note red21' also (rtranclp_trans)
    from tbisim'' tst'' tst have "\<forall>t'. ts1 t' = None \<longleftrightarrow> thr ?S2' t' = None" by(force simp add: tbisim_def)
    from aoe thread_oks_bisim_inv[OF this nta] have "thread_oks (thr ?S2') \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub>" by simp
    with cao2 aoe have aoe': "r2.actions_ok ?S2' t ta2" by auto

    let ?s1' = "redT_upd s1 t ta1 x1' M1'"

    have "mbisim ?s1' ?s2''"
    proof(rule mbisimI)
      from s1' show "locks ?s1' = locks ?s2''" by(auto simp add: redT_updLs_def o_def)
    next
      from s1' show "wset ?s1' = wset ?s2''" by auto
    next
      fix T assume tsT: "thr ?s1' T = None"
      moreover from mbisim_thrNone_eq[OF mbisim, of T]
      have "(thr s1 T = None) = (thr ?s2' T = None)" using tst tst' by(auto)
      with tbisim''[of T] tst tst'' have "(thr s1 T = None) = (thr ?S2' T = None)" by(auto simp add: tbisim_def)
      hence "(redT_updTs (thr s1) \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub> T = None) = (redT_updTs (thr ?S2') \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub> T = None)"
	by(rule redT_updTs_nta_bisim_inv[OF nta])
      ultimately show "thr ?s2'' T = None" using s1' by(auto simp add: redT_updLns_def)
    next
      fix T X1 LN
      assume tsT: "thr ?s1' T = \<lfloor>(X1, LN)\<rfloor>"
      show "\<exists>x2. thr ?s2'' T = \<lfloor>(x2, LN)\<rfloor> \<and> T \<turnstile> (X1, shr ?s1') \<approx> (x2, shr ?s2'') \<and> (wset ?s2'' T = None \<or> X1 \<approx>w x2)"
      proof(cases "thr s1 T")
	case None
	with tst have "T \<noteq> t" by auto
	from mbisim_thrNone_eq[OF mbisim] None have "thr s2 T = None" by(simp)
	with tst' have tsT': "thr ?s2' T = None" by(auto)
	from None `T \<noteq> t` tsT aoe s1' obtain M1
	  where ntset: "NewThread T X1 M1 \<in> set \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub>" and [simp]: "LN = no_wait_locks"
	  by(auto dest!: redT_updTs_new_thread)
	from ntset obtain tas1 tas1' where "\<lbrace>ta1\<rbrace>\<^bsub>t\<^esub> = tas1 @ NewThread T X1 M1 # tas1'"
	  by(auto simp add: in_set_conv_decomp)
	with nta	obtain tas2 X2 M2 tas2' where "\<lbrace>ta2\<rbrace>\<^bsub>t\<^esub> = tas2 @ NewThread T X2 M2 # tas2'"
	  "length tas2 = length tas2" "length tas1' = length tas2'" and Bisim: "T \<turnstile> (X1, M1) \<approx> (X2, M2)"
	  by(auto simp add: list_all2_append1 list_all2_Cons1, blast intro: sym)
	hence ntset': "NewThread T X2 M2 \<in> set \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub>" by auto
	with tsT' `T \<noteq> t` aoe' have "thr ?s2'' T = \<lfloor>(X2, no_wait_locks)\<rfloor>"
	  by(auto intro: redT_updTs_new_thread_ts)
	moreover from ntset' red22 have "M2'' = M2" by(auto dest: r2.new_thread_memory)
	moreover from ntset red have "M1 = M1'"
          by(auto dest: r1.new_thread_memory)
        moreover from mbisim_wset_thread_ok1[OF mbisim] None
        have "wset s1 T = None" by(rule wset_thread_okD)
	ultimately show ?thesis using Bisim `T \<noteq> t` by auto
      next
	case (Some a)
	show ?thesis
	proof(cases "t = T")
	  case True
	  with s1' tst tsT have "X1 = x1'" "LN = redT_updLns (locks s1) t no_wait_locks \<lbrace>ta1\<rbrace>\<^bsub>l\<^esub>" by(auto)
	  with True bisim' tst'' wst show ?thesis by(auto simp add: redT_updLns_def)
	next
	  case False
	  with s1' Some aoe tsT have "thr s1 T = \<lfloor>(X1, LN)\<rfloor>" by(auto dest: redT_updTs_Some)
	  with tbisim''[of T] False obtain X2 
	    where tsT': "thr ?S2' T = \<lfloor>(X2, LN)\<rfloor>" and Bisim: "T \<turnstile> (X1, m1) \<approx> (X2, m2)"
            and bisimw: "ws1 T = None \<or> X1 \<approx>w X2" by(auto simp add: tbisim_def)
	  with aoe' False have "thr ?s2'' T = \<lfloor>(X2, LN)\<rfloor>" by(simp add: redT_updTs_Some)
	  moreover from bisim_inv_red_other[OF Bisim bisim _ red \<tau> _ _ _ bisim' tasim, of x2'] red21 red22 \<tau>2
	  have "T \<turnstile> (X1, M1') \<approx> (X2, M2'')" by auto
	  ultimately show ?thesis using False bisimw by(auto)
	qed
      qed
    next
      from s1' show "finite (dom (thr ?s1'))"
	by(auto simp add: redT_updTs_finite_dom_inv)
    next
      from mbisim_wset_thread_ok1[OF mbisim] tst show "wset_thread_ok (wset ?s1') (thr ?s1')"
        by(fastsimp intro!: wset_thread_okI split: split_if_asm dest: redT_updTs_None wset_thread_okD)
    qed
    with s1' have "\<exists>s2'. r2.redTWs t \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub> ?s2'' obs  s2' \<and> s1' \<approx>m s2'"
    proof(rule redTWs_simulation1, intro conjI)
      fix w
      assume Suspend: "Suspend w \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub>"
      from red show "Suspend w \<notin> set (butlast \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub>)" by(rule r1.ta_Suspend_last)
      from wst show "wset (redT_upd s1 t ta1 x1' M1') t = None" by simp
      from tasim Suspend have "Suspend w \<in> set \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub>" by(simp add: ta_bisim_def)
      from bisim_waitI[OF bisim rtranclp.rtrancl_refl red \<tau> _ _ _ bisim' tasim Suspend this, of x2'] red21 red22 \<tau>2
      have "x1' \<approx>w x2''" by auto
      thus "\<exists>x1 x2 ln1 ln2. thr ?s1' t = \<lfloor>(x1, ln1)\<rfloor> \<and> thr ?s2'' t = \<lfloor>(x2, ln2)\<rfloor> \<and> x1 \<approx>w x2" by simp
    qed
    then obtain s2'' where "r2.redTWs t \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub> ?s2'' obs s2''" "s1' \<approx>m s2''" by blast
    from red22 tst'' wst aoe' `r2.redTWs t \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub> ?s2'' obs s2''`
    have "?S2' -2-t\<triangleright>observable_ta_of ta2 obs\<rightarrow> s2''"
      by -(rule r2.redT.redT_normal, auto simp add: redT_updLns_def)
    moreover from \<tau>2 have "\<not> m\<tau>move2 ?S2' (t, observable_ta_of ta2 obs) s2''"
    proof(rule contrapos_nn)
      assume m\<tau>: "m\<tau>move2 ?S2' (t, observable_ta_of ta2 obs) s2''"
      thus "\<tau>move2 (x2', M2') ta2 (x2'', M2'')" using tst'' tst' `r2.redTWs t \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub> ?s2'' obs s2''`
        by cases(auto, frule r2.silent_tl, auto simp add: redT_updLns_def finfun_Diag_const2 o_def dest: sym elim: rtrancl3p_cases)
    qed
    ultimately show ?thesis using tasim `s1' \<approx>m s2''` unfolding tl1 by fastsimp
  next
    case (redT_acquire x1 ln n)
    hence [simp]: "TA = (\<lambda>\<^isup>f [], [], [], [], [ReacquireLocks ln])"
      and tst: "thr s1 t = \<lfloor>(x1, ln)\<rfloor>" and wst: "wset s1 t = None"
      and maa: "may_acquire_all (locks s1) t ln" and ln: "0 < ln\<^sub>f n"
      and s1': "s1' = (acquire_all ls1 t ln, (ts1(t \<mapsto> (x1, no_wait_locks)), m1), ws1)" by auto
    from tst mbisim obtain x2 where tst': "ts2 t = \<lfloor>(x2, ln)\<rfloor>" 
      and bisim: "t \<turnstile> (x1, m1) \<approx> (x2, m2)" by(auto dest: mbisim_thrD1)
    let ?s2' = "(acquire_all ls1 t ln, (ts2(t \<mapsto> (x2, no_wait_locks)), m2), ws1)"
    from tst' wst maa ln have "s2 -2-t\<triangleright>(\<lambda>\<^isup>f [], [], [], [], [ReacquireLocks ln])\<rightarrow> ?s2'"
      by-(rule r2.redT.redT_acquire, auto)
    moreover from tst' ln have "\<not> m\<tau>move2 s2 (t, (\<lambda>\<^isup>f [], [], [], [], [ReacquireLocks ln])) ?s2'"
      by(auto simp add: acquire_all_def expand_fun_eq elim!: r2.m\<tau>move.cases)
    moreover have "mbisim s1' ?s2'"
    proof(rule mbisimI)
      from s1' show "locks s1' = locks ?s2'" by auto
    next
      from s1' show "wset s1' = wset ?s2'" by auto
    next
      fix t' assume "thr s1' t' = None"
      with s1' have "thr s1 t' = None" by(auto split: split_if_asm)
      with mbisim_thrNone_eq[OF mbisim] have "ts2 t' = None" by simp
      with tst' show "thr ?s2' t' = None" by auto
    next
      fix t' X1 LN
      assume ts't: "thr s1' t' = \<lfloor>(X1, LN)\<rfloor>"
      show "\<exists>x2. thr ?s2' t' = \<lfloor>(x2, LN)\<rfloor> \<and> t' \<turnstile> (X1, shr s1') \<approx> (x2, shr ?s2') \<and> (wset ?s2' t' = None \<or> X1 \<approx>w x2)"
      proof(cases "t' = t")
	case True
	with s1' tst ts't have [simp]: "X1 = x1" "LN = no_wait_locks" by simp_all
	with bisim tst True s1' wst show ?thesis by(auto)
      next
	case False
	with ts't s1' have "ts1 t' = \<lfloor>(X1, LN)\<rfloor>" by auto
	with mbisim obtain X2 where "ts2 t' = \<lfloor>(X2, LN)\<rfloor>" "t' \<turnstile> (X1, m1) \<approx> (X2, m2)" "wset ?s2' t' = None \<or> X1 \<approx>w X2"
	  by(auto dest: mbisim_thrD1)
	with False s1' show ?thesis by auto
      qed
    next
      from s1' show "finite (dom (thr s1'))" by auto
    next
      from mbisim_wset_thread_ok1[OF mbisim]
      show "wset_thread_ok (wset s1') (thr s1')" using s1' by(auto intro: wset_thread_ok_upd)
    qed
    moreover have "(t, \<lambda>\<^isup>f [], [], [], [], [ReacquireLocks ln]) \<sim>T (t, \<lambda>\<^isup>f [], [], [], [], [ReacquireLocks ln])"
      by(simp add: ta_bisim_def)
    ultimately show ?thesis by fastsimp
  qed
qed

theorem mbisim_simulation2:
  "\<lbrakk> r1.wfs_inv; mbisim s1 s2; r2.redT s2 tl2 s2'; \<not> m\<tau>move2 s2 tl2 s2' \<rbrakk>
  \<Longrightarrow> \<exists>s1' s1'' tl1. r1.mthr.silent_moves s1 s1' \<and> r1.redT s1' tl1 s1'' \<and> \<not> m\<tau>move1 s1' tl1 s1'' \<and>
                    mbisim s1'' s2' \<and> mta_bisim tl1 tl2"
using FWdelay_bisimulation_obs.mbisim_simulation1[OF FWdelay_bisimulation_obs_flip]
unfolding flip_simps .

end

locale FWdelay_bisimulation_diverge =
  FWdelay_bisimulation_obs _ _ _ _ _ _ \<tau>move1 \<tau>move2
  for \<tau>move1 :: "('l,'t,'x1,'m1,'w,'o) \<tau>moves"
  and \<tau>move2 :: "('l,'t,'x2,'m2,'w,'o) \<tau>moves" +
  assumes delay_bisimulation_diverge_locale: "delay_bisimulation_diverge (r1 t) (r2 t) (bisim t) (ta_bisim bisim) \<tau>move1 \<tau>move2"

sublocale FWdelay_bisimulation_diverge <
  delay_bisimulation_diverge "r1 t" "r2 t" "bisim t" "ta_bisim bisim" \<tau>move1 \<tau>move2 for t
by(rule delay_bisimulation_diverge_locale)

context FWdelay_bisimulation_diverge begin

lemma FWdelay_bisimulation_diverge_flip:
  "FWdelay_bisimulation_diverge final2 r2 final1 r1 (\<lambda>t. flip (bisim t)) (flip bisim_wait) \<tau>move2 \<tau>move1"
apply(rule FWdelay_bisimulation_diverge.intro)
 apply(rule FWdelay_bisimulation_obs_flip)
apply(rule FWdelay_bisimulation_diverge_axioms.intro)
apply(unfold flip_simps)
apply(rule delay_bisimulation_diverge_axioms)
done

end

lemma FWdelay_bisimulation_diverge_flip_simps [flip_simps]:
  "FWdelay_bisimulation_diverge final2 r2 final1 r1 (\<lambda>t. flip (bisim t)) (flip bisim_wait) \<tau>move2 \<tau>move1 = 
   FWdelay_bisimulation_diverge final1 r1 final2 r2 bisim bisim_wait \<tau>move1 \<tau>move2"
by(auto dest: FWdelay_bisimulation_diverge.FWdelay_bisimulation_diverge_flip simp only: flip_flip)

context FWdelay_bisimulation_diverge begin

lemma bisim_inv1:
  assumes bisim: "t \<turnstile> s1 \<approx> s2"
  and red: "t \<turnstile> s1 -1-ta1\<rightarrow> s1'"
  obtains s2' where "t \<turnstile> s1' \<approx> s2'"
proof(atomize_elim)
  show "\<exists>s2'. t \<turnstile> s1' \<approx> s2'"
  proof(cases "\<tau>move1 s1 ta1 s1'")
    case True
    with red have "r1.silent_move t s1 s1'" by auto
    from simulation_silent1[OF bisim this]
    show ?thesis by auto
  next
    case False
    from simulation1[OF bisim red False] show ?thesis by auto
  qed
qed

lemma bisim_inv2:
  assumes "t \<turnstile> s1 \<approx> s2" "t \<turnstile> s2 -2-ta2\<rightarrow> s2'"
  obtains s1' where "t \<turnstile> s1' \<approx> s2'"
using assms FWdelay_bisimulation_diverge.bisim_inv1[OF FWdelay_bisimulation_diverge_flip]
unfolding flip_simps by blast

lemma bisim_inv: "bisim_inv"
by(blast intro!: bisim_invI elim: bisim_inv1 bisim_inv2)

lemma bisim_inv_\<tau>s1:
  assumes "t \<turnstile> s1 \<approx> s2" and "r1.silent_moves t s1 s1'"
  obtains s2' where "t \<turnstile> s1' \<approx> s2'"
using assms by(rule bisim_inv_\<tau>s1_inv[OF bisim_inv])

lemma bisim_inv_\<tau>s2:
  assumes "t \<turnstile> s1 \<approx> s2" and "r2.silent_moves t s2 s2'"
  obtains s1' where "t \<turnstile> s1' \<approx> s2'"
using assms by(rule bisim_inv_\<tau>s2_inv[OF bisim_inv])

lemma wfs1_inv [simp, intro!]: "r1.wfs_inv"
by(rule r1.wfs_invI)(auto elim: bisim_inv1)

lemma wfs2_inv [simp, intro!]: "r2.wfs_inv"
by(rule r2.wfs_invI)(auto elim: bisim_inv2)

lemma mbisim_imp_ts_ok_wfs1:
  "s1 \<approx>m s2 \<Longrightarrow> ts_ok (\<lambda>t x m. \<exists>s2. t \<turnstile> (x, m) \<approx> s2) (thr s1) (shr s1)"
by(fastsimp intro: ts_okI dest: mbisim_thrD1)

lemma mbisim_imp_ts_ok_wfs2:
  "s1 \<approx>m s2 \<Longrightarrow> ts_ok (\<lambda>t x m. \<exists>s1. t \<turnstile> s1 \<approx> (x, m)) (thr s2) (shr s2)"
by(fastsimp intro: ts_okI dest: mbisim_thrD2)

lemma red1_rtrancl_\<tau>_into_RedT_\<tau>:
  assumes "r1.silent_moves t (x1, shr s1) (x1', m1')" "t \<turnstile> (x1, shr s1) \<approx> (x2, m2)"
  and "thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>" "wset s1 t = None"
  shows "\<tau>mRed1 s1 (redT_upd s1 t \<epsilon> x1' m1')"
using assms by(blast intro: r1.silent_moves_into_RedT_\<tau>_inv[OF wfs1_inv])

lemma red2_rtrancl_\<tau>_into_RedT_\<tau>:
  assumes "r2.silent_moves t (x2, shr s2) (x2', m2')"
  and "t \<turnstile> (x1, m1) \<approx> (x2, shr s2)" "thr s2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>" "wset s2 t = None"
  shows "\<tau>mRed2 s2 (redT_upd s2 t \<epsilon> x2' m2')"
using assms by(blast intro: r2.silent_moves_into_RedT_\<tau>_inv[OF wfs2_inv])

lemma red1_rtrancl_\<tau>_heapD:
  "\<lbrakk> r1.silent_moves t s1 s1'; t \<turnstile> s1 \<approx> s2 \<rbrakk> \<Longrightarrow> snd s1' = snd s1"
by(blast intro: r1.red_rtrancl_\<tau>_heapD_inv[OF wfs1_inv])

lemma red2_rtrancl_\<tau>_heapD:
  "\<lbrakk> r2.silent_moves t s2 s2'; t \<turnstile> s1 \<approx> s2 \<rbrakk> \<Longrightarrow> snd s2' = snd s2"
by(blast intro: r2.red_rtrancl_\<tau>_heapD_inv[OF wfs2_inv])

lemma mbisim_simulation_silent1:
  assumes m\<tau>': "r1.mthr.silent_move s1 s1'" and mbisim: "s1 \<approx>m s2"
  shows "\<exists>s2'. r2.mthr.silent_moves s2 s2' \<and> s1' \<approx>m s2'"
proof -
  from m\<tau>' obtain tl1 where m\<tau>: "m\<tau>move1 s1 tl1 s1'" "r1.redT s1 tl1 s1'" by auto
  obtain ls1 ts1 m1 ws1 where [simp]: "s1 = (ls1, (ts1, m1), ws1)" by(cases s1, auto)
  obtain ls1' ts1' m1' ws1' where [simp]: "s1' = (ls1', (ts1', m1'), ws1')" by(cases s1', auto)
  obtain ls2 ts2 m2 ws2 where [simp]: "s2 = (ls2, (ts2, m2), ws2)" by(cases s2, auto)
  from m\<tau> obtain t where "tl1 = (t, \<epsilon>)" by(auto elim!: r1.m\<tau>move.cases dest: r1.silent_tl)
  with m\<tau> have m\<tau>: "m\<tau>move1 s1 (t, \<epsilon>) s1'"
    and redT1: "s1 -1-t\<triangleright>observable_ta_of \<epsilon> []\<rightarrow> s1'" by simp_all
  from m\<tau> obtain x x' ln' where tst: "ts1 t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    and ts't: "ts1' t = \<lfloor>(x', ln')\<rfloor>" and \<tau>: "\<tau>move1 (x, m1) \<epsilon> (x', m1')"
    by(fastsimp elim: r1.m\<tau>move.cases)
  from mbisim have [simp]: "ls2 = ls1" "ws2 = ws1" "finite (dom ts1)" by(auto simp add: mbisim_def)
  from redT1 show ?thesis
  proof cases
    case (redT_normal x1 TA x1' M' obs)
    with tst ts't have [simp]: "TA = \<epsilon>" "x = x1" "x' = x1'" "obs = []"
      and red: "t \<turnstile> (x1, m1) -1-\<epsilon>\<rightarrow> (x1', M')"
      and tst: "thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>"
      and wst: "wset s1 t = None"
      and s1': "s1' = redT_upd s1 t \<epsilon> x1' M'" by(auto)
    from s1' tst have [simp]: "ls1' = ls1" "ws1' = ws1" "M' = m1'" "ts1' = ts1(t \<mapsto> (x1', no_wait_locks))"
      by(auto simp add: redT_updLs_def redT_updLns_def o_def)
    from mbisim tst obtain x2 where tst': "ts2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>"
      and bisim: "t \<turnstile> (x1, m1) \<approx> (x2, m2)" by(auto dest: mbisim_thrD1)
    from r1.\<tau>move_heap[OF exI, OF bisim red] \<tau> have [simp]: "m1 = M'" by simp
    from red \<tau> have "r1.silent_move t (x1, m1) (x1', M')" by auto
    from simulation_silent1[OF bisim this]
    obtain x2' m2' where red: "r2.silent_moves t (x2, m2) (x2', m2')"
      and bisim': "t \<turnstile> (x1', m1) \<approx> (x2', m2')" by auto
    from red bisim have [simp]: "m2' = m2" 
      by(auto dest: red2_rtrancl_\<tau>_heapD)
    from red tst' wst bisim have "\<tau>mRed2 s2 (redT_upd s2 t \<epsilon> x2' m2')"
      by -(rule red2_rtrancl_\<tau>_into_RedT_\<tau>, auto)
    moreover have "mbisim s1' (redT_upd s2 t \<epsilon> x2' m2')"
    proof(rule mbisimI)
      show "locks s1' = locks (redT_upd s2 t \<epsilon> x2' m2')" by(auto simp add: redT_updLs_def o_def)
    next
      show "wset s1' = wset (redT_upd s2 t \<epsilon> x2' m2')" by auto
    next
      fix t'
      assume "thr s1' t' = None"
      hence "ts1 t' = None" by(auto split: split_if_asm)
      with mbisim_thrNone_eq[OF mbisim] have "ts2 t' = None" by simp
      with tst' show "thr (redT_upd s2 t \<epsilon> x2' m2') t' = None" by auto
    next
      fix t' X1 LN
      assume ts't': "thr s1' t' = \<lfloor>(X1, LN)\<rfloor>"
      show "\<exists>x2. thr (redT_upd s2 t \<epsilon> x2' m2') t' = \<lfloor>(x2, LN)\<rfloor> \<and> t' \<turnstile> (X1, shr s1') \<approx> (x2, shr (redT_upd s2 t \<epsilon> x2' m2')) \<and> (wset (redT_upd s2 t \<epsilon> x2' m2') t' = None \<or> X1 \<approx>w x2)"
      proof(cases "t' = t")
	case True
	note this[simp]
	with s1' tst ts't' have [simp]: "X1 = x1'" "LN = no_wait_locks"
	  by(simp_all)(auto simp add: redT_updLns_def o_def finfun_Diag_const2)
	with bisim' tst' wst show ?thesis by(auto simp add: redT_updLns_def o_def finfun_Diag_const2)
      next
	case False
	with ts't' have "ts1 t' = \<lfloor>(X1, LN)\<rfloor>" by auto
	with mbisim obtain X2 where "ts2 t' = \<lfloor>(X2, LN)\<rfloor>" "t' \<turnstile> (X1, m1) \<approx> (X2, m2)" "ws1 t' = None \<or> X1 \<approx>w X2"
	  by(auto dest: mbisim_thrD1)
	with False show ?thesis by auto
      qed
    next
      show "finite (dom (thr s1'))" by simp
    next
      from mbisim_wset_thread_ok1[OF mbisim]
      show "wset_thread_ok (wset s1') (thr s1')" by(auto intro: wset_thread_ok_upd)
    qed
    ultimately show ?thesis by(auto)
  next
    case redT_acquire
    with tst have False by auto
    thus ?thesis ..
  qed
qed

lemma mbisim_simulation_silent2:
  "\<lbrakk> mbisim s1 s2; r2.mthr.silent_move s2 s2' \<rbrakk>
  \<Longrightarrow> \<exists>s1'. r1.mthr.silent_moves s1 s1' \<and> mbisim s1' s2'"
using FWdelay_bisimulation_diverge.mbisim_simulation_silent1[OF FWdelay_bisimulation_diverge_flip]
unfolding flip_simps .

lemma mbisim_simulation1:
  assumes mbisim: "mbisim s1 s2" and "\<not> m\<tau>move1 s1 tl1 s1'" "r1.redT s1 tl1 s1'"
  shows "\<exists>s2' s2'' tl2. r2.mthr.silent_moves s2 s2' \<and> r2.redT s2' tl2 s2'' \<and>
                        \<not> m\<tau>move2 s2' tl2 s2'' \<and> mbisim s1' s2'' \<and> mta_bisim tl1 tl2"
using mbisim_simulation1[OF bisim_inv_wfs_inv2[OF bisim_inv]] assms .

lemma mbisim_simulation2:
  "\<lbrakk> mbisim s1 s2; r2.redT s2 tl2 s2'; \<not> m\<tau>move2 s2 tl2 s2' \<rbrakk>
  \<Longrightarrow> \<exists>s1' s1'' tl1. r1.mthr.silent_moves s1 s1' \<and> r1.redT s1' tl1 s1'' \<and> \<not> m\<tau>move1 s1' tl1 s1'' \<and>
                    mbisim s1'' s2' \<and> mta_bisim tl1 tl2"
using FWdelay_bisimulation_diverge.mbisim_simulation1[OF FWdelay_bisimulation_diverge_flip]
unfolding flip_simps .

lemma m\<tau>diverge_simulation1:
  assumes "s1 \<approx>m s2"
  and "r1.mthr.\<tau>diverge s1"
  shows "r2.mthr.\<tau>diverge s2"
proof -
  from `s1 \<approx>m s2` have "finite (dom (thr s1))" "ts_ok (\<lambda>t x m. \<exists>s2. t \<turnstile> (x, m) \<approx> s2) (thr s1) (shr s1)"
    by(rule mbisim_finite1 mbisim_imp_ts_ok_wfs1)+
  from r1.\<tau>diverge_\<tau>mredTD[OF wfs1_inv `r1.mthr.\<tau>diverge s1` this]
  obtain t x where "thr s1 t = \<lfloor>(x, no_wait_locks)\<rfloor>" "wset s1 t = None" "r1.\<tau>diverge t (x, shr s1)" by blast
  from `s1 \<approx>m s2` `thr s1 t = \<lfloor>(x, no_wait_locks)\<rfloor>` obtain x'
    where "thr s2 t = \<lfloor>(x', no_wait_locks)\<rfloor>" "t \<turnstile> (x, shr s1) \<approx> (x', shr s2)"
    by(auto dest: mbisim_thrD1)
  from `s1 \<approx>m s2` `wset s1 t = None` have "wset s2 t = None" by(simp add: mbisim_def)
  from `t \<turnstile> (x, shr s1) \<approx> (x', shr s2)` `r1.\<tau>diverge t (x, shr s1)`
  have "r2.\<tau>diverge t (x', shr s2)" by(simp add: \<tau>diverge_bisim_inv)
  with wfs2_inv show ?thesis using `thr s2 t = \<lfloor>(x', no_wait_locks)\<rfloor>` `wset s2 t = None`
    by(rule r2.\<tau>diverge_into_\<tau>mredT)(blast intro: `t \<turnstile> (x, shr s1) \<approx> (x', shr s2)`)
qed

lemma \<tau>diverge_mbisim_inv:
  "s1 \<approx>m s2 \<Longrightarrow> r1.mthr.\<tau>diverge s1 \<longleftrightarrow> r2.mthr.\<tau>diverge s2"
apply(rule iffI)
 apply(erule (1) m\<tau>diverge_simulation1)
by(rule FWdelay_bisimulation_diverge.m\<tau>diverge_simulation1[OF FWdelay_bisimulation_diverge_flip, unfolded flip_simps])

lemma mbisim_delay_bisimulation:
  "delay_bisimulation_diverge r1.redT r2.redT mbisim mta_bisim m\<tau>move1 m\<tau>move2"
apply(unfold_locales)
apply(rule mbisim_simulation1 mbisim_simulation2 mbisim_simulation_silent1 mbisim_simulation_silent2 \<tau>diverge_mbisim_inv|assumption)+
done

theorem mdelay_bisimulation_final_base:
  "delay_bisimulation_final_base r1.redT r2.redT mbisim m\<tau>move1 m\<tau>move2 r1.mfinal r2.mfinal"
apply(unfold_locales)
apply(blast dest: mfinal1_simulation[OF bisim_inv_wfs_inv2[OF bisim_inv]] mfinal2_simulation[OF bisim_inv_wfs_inv1[OF bisim_inv]])+
done

end

sublocale FWdelay_bisimulation_diverge < mthr!: delay_bisimulation_diverge r1.redT r2.redT mbisim mta_bisim m\<tau>move1 m\<tau>move2
by(rule mbisim_delay_bisimulation)

sublocale FWdelay_bisimulation_diverge <
  mthr!: delay_bisimulation_final_base r1.redT r2.redT mbisim mta_bisim m\<tau>move1 m\<tau>move2 r1.mfinal r2.mfinal
by(rule mdelay_bisimulation_final_base)

sublocale FWdelay_bisimulation_diverge <
  mthr!: delay_bisimulation_diverge_final r1.redT r2.redT mbisim mta_bisim m\<tau>move1 m\<tau>move2 r1.mfinal r2.mfinal
by(unfold_locales)

locale FWdelay_bisimulation_measure =
  FWdelay_bisimulation_obs _ _ _ _ _ _ \<tau>move1 \<tau>move2 +
  r1!: multithreaded_base_measure final1 r1 "\<mu>1^++" +
  r2!: multithreaded_base_measure final2 r2 "\<mu>2^++"
  for \<tau>move1 :: "('l,'t,'x1,'m1,'w, 'o) \<tau>moves"
  and \<tau>move2 :: "('l,'t,'x2,'m2,'w, 'o) \<tau>moves" 
  and \<mu>1 :: "('x1 \<times> 'm1) \<Rightarrow> ('x1 \<times> 'm1) \<Rightarrow> bool"
  and \<mu>2 :: "('x2 \<times> 'm2) \<Rightarrow> ('x2 \<times> 'm2) \<Rightarrow> bool" +
  assumes delay_bisimulation_measure_locale:
  "delay_bisimulation_measure (r1 t) (r2 t) (bisim t) (ta_bisim bisim) \<tau>move1 \<tau>move2 \<mu>1 \<mu>2"

sublocale FWdelay_bisimulation_measure <
  delay_bisimulation_measure "r1 t" "r2 t" "bisim t" "ta_bisim bisim" \<tau>move1 \<tau>move2 \<mu>1 \<mu>2 for t
by(rule delay_bisimulation_measure_locale)

sublocale FWdelay_bisimulation_measure < r1!: multithreaded_base_measure_wf final1 r1 "\<mu>1^++"
proof
  show "wfP \<mu>1\<^sup>+\<^sup>+" by(rule wfP_trancl)(rule wf_\<mu>1)
qed

sublocale FWdelay_bisimulation_measure < r2!: multithreaded_base_measure_wf final2 r2 "\<mu>2^++"
proof
  show "wfP \<mu>2\<^sup>+\<^sup>+" by(rule wfP_trancl)(rule wf_\<mu>2)
qed

context FWdelay_bisimulation_measure begin

lemma FWdelay_bisimulation_measure_flip:
  "FWdelay_bisimulation_measure final2 r2 final1 r1 (\<lambda>t. flip (bisim t)) (flip bisim_wait) \<tau>move2 \<tau>move1 \<mu>2 \<mu>1"
apply(rule FWdelay_bisimulation_measure.intro)
 apply(rule FWdelay_bisimulation_obs_flip)
apply(rule FWdelay_bisimulation_measure_axioms.intro)
apply(unfold flip_simps)
apply(rule delay_bisimulation_measure_axioms)
done

end

lemma FWdelay_bisimulation_measure_flip_simps [flip_simps]:
  "FWdelay_bisimulation_measure final2 r2 final1 r1 (\<lambda>t. flip (bisim t)) (flip bisim_wait) \<tau>move2 \<tau>move1 \<mu>2 \<mu>1 =
   FWdelay_bisimulation_measure final1 r1 final2 r2 bisim bisim_wait \<tau>move1 \<tau>move2 \<mu>1 \<mu>2"
by(auto dest: FWdelay_bisimulation_measure.FWdelay_bisimulation_measure_flip simp only: flip_flip)

context FWdelay_bisimulation_measure begin

lemma bisim_inv1:
  assumes bisim: "t \<turnstile> s1 \<approx> s2"
  and red: "t \<turnstile> s1 -1-ta1\<rightarrow> s1'"
  obtains s2' where "t \<turnstile> s1' \<approx> s2'"
proof(atomize_elim)
  show "\<exists>s2'. t \<turnstile> s1' \<approx> s2'"
  proof(cases "\<tau>move1 s1 ta1 s1'")
    case True
    with red have "r1.silent_move t s1 s1'" by auto
    from simulation_silent1[OF bisim this]
    show ?thesis by auto
  next
    case False
    from simulation1[OF bisim red False] show ?thesis by auto
  qed
qed

lemma bisim_inv2:
  assumes bisim: "t \<turnstile> s1 \<approx> s2"
  and red: "t \<turnstile> s2 -2-ta2\<rightarrow> s2'"
  obtains s1' where "t \<turnstile> s1' \<approx> s2'"
using assms FWdelay_bisimulation_measure.bisim_inv1[OF FWdelay_bisimulation_measure_flip]
unfolding flip_simps by blast

lemma bisim_inv: "bisim_inv"
by(blast intro!: bisim_invI elim: bisim_inv1 bisim_inv2)

lemma bisim_inv_\<tau>s1:
  assumes "t \<turnstile> s1 \<approx> s2" and "r1.silent_moves t s1 s1'"
  obtains s2' where "t \<turnstile> s1' \<approx> s2'"
using assms by(rule bisim_inv_\<tau>s1_inv[OF bisim_inv])

lemma bisim_inv_\<tau>s2:
  assumes "t \<turnstile> s1 \<approx> s2" and "r2.silent_moves t s2 s2'"
  obtains s1' where "t \<turnstile> s1' \<approx> s2'"
using assms by(rule bisim_inv_\<tau>s2_inv[OF bisim_inv])

lemma wfs1_inv [simp, intro!]: "r1.wfs_inv"
by(rule r1.wfs_invI)(auto elim: bisim_inv1)

lemma wfs2_inv [simp, intro!]: "r2.wfs_inv"
by(rule r2.wfs_invI)(auto elim: bisim_inv2)

lemma red1_trancl_\<tau>_heapD:
  "\<lbrakk> r1.silent_movet t s1 s1'; t \<turnstile> s1 \<approx> s2 \<rbrakk> \<Longrightarrow> snd s1' = snd s1"
by(blast intro: r1.red_trancl_\<tau>_heapD_inv[OF wfs1_inv])

lemma red2_trancl_\<tau>_heapD:
  "\<lbrakk> r2.silent_movet t s2 s2'; t \<turnstile> s1 \<approx> s2 \<rbrakk> \<Longrightarrow> snd s2' = snd s2"
by(blast intro: r2.red_trancl_\<tau>_heapD_inv[OF wfs2_inv])

lemma red1_trancl_\<tau>_into_RedT_\<tau>_inv:
  "\<lbrakk> r1.silent_movet t (x, shr s) (x', m'); t \<turnstile> (x, shr s) \<approx> xm; thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; wset s t = None \<rbrakk>
  \<Longrightarrow> \<tau>mred1^++ s (redT_upd s t (\<epsilon> :: ('l,'t,'x1,'m1,'w,'o list) thread_action) x' m')"
by(blast intro: r1.red_trancl_\<tau>_into_RedT_\<tau>_inv[OF wfs1_inv])

lemma red2_trancl_\<tau>_into_RedT_\<tau>_inv:
  "\<lbrakk> r2.silent_movet t (x, shr s) (x', m'); t \<turnstile> xm \<approx> (x, shr s); thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; wset s t = None \<rbrakk>
  \<Longrightarrow> \<tau>mred2^++ s (redT_upd s t (\<epsilon> :: ('l,'t,'x2,'m2,'w,'o list) thread_action) x' m')"
by(blast intro: r2.red_trancl_\<tau>_into_RedT_\<tau>_inv[OF wfs2_inv])

lemma mbisim_simulation_silent1_measure:
  assumes "r1.mthr.silent_move s1 s1'" and mbisim: "s1 \<approx>m s2"
  shows "s1' \<approx>m s2 \<and> r1.m\<mu>^++ s1' s1 \<or> (\<exists>s2'. r2.mthr.silent_move^++ s2 s2' \<and> s1' \<approx>m s2')"
proof -
  from assms obtain tl1 where m\<tau>: "m\<tau>move1 s1 tl1 s1'" "r1.redT s1 tl1 s1'" by(auto simp add: r1.mthr.silent_move_iff)
  obtain ls1 ts1 m1 ws1 where [simp]: "s1 = (ls1, (ts1, m1), ws1)" by(cases s1, auto)
  obtain ls1' ts1' m1' ws1' where [simp]: "s1' = (ls1', (ts1', m1'), ws1')" by(cases s1', auto)
  obtain ls2 ts2 m2 ws2 where [simp]: "s2 = (ls2, (ts2, m2), ws2)" by(cases s2, auto)
  from m\<tau> obtain t where "tl1 = (t, \<epsilon>)" by(auto elim!: r1.m\<tau>move.cases dest: r1.silent_tl)
  with m\<tau> have m\<tau>: "m\<tau>move1 s1 (t, observable_ta_of \<epsilon> []) s1'" and redT1: "s1 -1-t\<triangleright>observable_ta_of \<epsilon> []\<rightarrow> s1'"
    by simp_all
  from m\<tau> obtain x x' ln' where tst: "ts1 t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    and ts't: "ts1' t = \<lfloor>(x', ln')\<rfloor>" and \<tau>: "\<tau>move1 (x, m1) \<epsilon> (x', m1')"
    by(fastsimp elim: r1.m\<tau>move.cases)
  from mbisim have [simp]: "ls2 = ls1" "ws2 = ws1" "finite (dom ts1)" by(auto simp add: mbisim_def)
  from redT1 show ?thesis
  proof cases
    case (redT_normal x1 TA x1' M' obs)
    with tst ts't have [simp]: "TA = \<epsilon>" "x = x1" "x' = x1'" "obs = []"
      and red: "t \<turnstile> (x1, m1) -1-\<epsilon>\<rightarrow> (x1', M')"
      and tst: "thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>"
      and wst: "wset s1 t = None"
      and s1': "s1' = redT_upd s1 t \<epsilon> x1' M'" by(auto)
    from s1' tst have [simp]: "ls1' = ls1" "ws1' = ws1" "M' = m1'" "ts1' = ts1(t \<mapsto> (x1', no_wait_locks))"
      by(auto simp add: redT_updLs_def redT_updLns_def o_def)
    from mbisim tst obtain x2 where tst': "ts2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>"
      and bisim: "t \<turnstile> (x1, m1) \<approx> (x2, m2)" by(auto dest: mbisim_thrD1)
    from r1.\<tau>move_heap[OF exI, OF bisim red] \<tau> have [simp]: "m1 = M'" by simp
    from red \<tau> have "r1.silent_move t (x1, m1) (x1', m1')" by(auto simp add: r1.silent_move_iff)
    with bisim
    have "t \<turnstile> (x1', M') \<approx> (x2, m2) \<and> \<mu>1\<^sup>+\<^sup>+ (x1', M') (x1, m1) \<or> (\<exists>s2'. r2.silent_movet t (x2, m2) s2' \<and> t \<turnstile> (x1', M') \<approx> s2')"
      by(simp)(rule simulation_silent1)
    thus ?thesis
    proof
      assume "t \<turnstile> (x1', M') \<approx> (x2, m2) \<and> \<mu>1\<^sup>+\<^sup>+ (x1', M') (x1, m1)"
      then obtain bisim': "t \<turnstile> (x1', M') \<approx> (x2, m2)" and \<mu>1: "\<mu>1\<^sup>+\<^sup>+ (x1', M') (x1, m1)" ..
      have "s1' \<approx>m s2"
      proof(rule mbisimI)
	show "locks s1' = locks s2" "wset s1' = wset s2" by(auto)
      next
	fix t
	assume "thr s1' t = None"
	hence "ts1 t = None" by(auto split: split_if_asm)
	with mbisim_thrNone_eq[OF mbisim, of t] show "thr s2 t = None" by simp
      next
	fix t' X1 LN
	assume ts't': "thr s1' t' = \<lfloor>(X1, LN)\<rfloor>"
	show "\<exists>x2. thr s2 t' = \<lfloor>(x2, LN)\<rfloor> \<and> t' \<turnstile> (X1, shr s1') \<approx> (x2, shr s2) \<and> (wset s2 t' = None \<or> X1 \<approx>w x2)"
	proof(cases "t' = t")
	  case True
	  note this[simp]
	  with s1' tst ts't' have [simp]: "X1 = x1'" "LN = no_wait_locks"
	    by(simp_all)(auto simp add: redT_updLns_def o_def finfun_Diag_const2)
	  with bisim' tst' wst show ?thesis by(auto)
	next
	  case False
	  with ts't' have "ts1 t' = \<lfloor>(X1, LN)\<rfloor>" by auto
	  with mbisim obtain X2 where "ts2 t' = \<lfloor>(X2, LN)\<rfloor>" "t' \<turnstile> (X1, m1) \<approx> (X2, m2)" "wset s2 t' = None \<or> X1 \<approx>w X2"
	    by(auto dest: mbisim_thrD1)
	  with False show ?thesis by auto
	qed
      next
        from mbisim_wset_thread_ok1[OF mbisim]
        show "wset_thread_ok (wset s1') (thr s1')" by(auto intro: wset_thread_ok_upd)
      qed simp
      moreover have "r1.m\<mu>t m1' (ts1(t \<mapsto> (x1', no_wait_locks))) ts1"
      proof
	show "finite (dom (ts1(t \<mapsto> (x1', no_wait_locks))))" by simp
      next
	show "(ts1(t \<mapsto> (x1', no_wait_locks))) t = \<lfloor>(x1', no_wait_locks)\<rfloor>" by simp
      next
	from tst show "ts1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>" by simp
      next
	from \<mu>1 show "\<mu>1^++ (x1', m1') (x1, m1')" by auto
      qed auto
      hence "r1.m\<mu> s1' s1" by(auto simp add: r1.m\<mu>_def)
      ultimately show ?thesis by blast
    next
      assume "\<exists>s2'. r2.silent_movet t (x2, m2) s2' \<and> t \<turnstile> (x1', M') \<approx> s2'"
      then obtain x2' m2' where red: "r2.silent_movet t (x2, m2) (x2', m2')"
	and bisim': "t \<turnstile> (x1', m1) \<approx> (x2', m2')" by auto
      from red bisim have [simp]: "m2' = m2"
	by(auto dest: red2_trancl_\<tau>_heapD)
      from red tst' wst bisim have "\<tau>mred2^++ s2 (redT_upd s2 t (\<epsilon> :: ('l,'t,'x2,'m2,'w,'o list) thread_action) x2' m2')"
	by -(rule red2_trancl_\<tau>_into_RedT_\<tau>_inv, auto)
      moreover have "mbisim s1' (redT_upd s2 t (\<epsilon> :: ('l,'t,'x2,'m2,'w,'o list) thread_action) x2' m2')"
      proof(rule mbisimI)
	show "locks s1' = locks (redT_upd s2 t \<epsilon> x2' m2')" by(auto simp add: redT_updLs_def o_def)
      next
	show "wset s1' = wset (redT_upd s2 t \<epsilon> x2' m2')" by auto
      next
	fix t'
	assume "thr s1' t' = None"
	hence "ts1 t' = None" by(auto split: split_if_asm)
	with mbisim_thrNone_eq[OF mbisim] have "ts2 t' = None" by simp
	with tst' show "thr (redT_upd s2 t \<epsilon> x2' m2') t' = None" by auto
      next
	fix t' X1 LN
	assume ts't': "thr s1' t' = \<lfloor>(X1, LN)\<rfloor>"
	show "\<exists>x2. thr (redT_upd s2 t \<epsilon> x2' m2') t' = \<lfloor>(x2, LN)\<rfloor> \<and> t' \<turnstile> (X1, shr s1') \<approx> (x2, shr (redT_upd s2 t \<epsilon> x2' m2')) \<and> (wset (redT_upd s2 t \<epsilon> x2' m2') t' = None \<or> X1 \<approx>w x2)"
	proof(cases "t' = t")
	  case True
	  note this[simp]
	  with s1' tst ts't' have [simp]: "X1 = x1'" "LN = no_wait_locks"
	    by(simp_all)(auto simp add: redT_updLns_def o_def finfun_Diag_const2)
	  with bisim' tst' wst show ?thesis by(auto simp add: redT_updLns_def o_def finfun_Diag_const2)
	next
	  case False
	  with ts't' have "ts1 t' = \<lfloor>(X1, LN)\<rfloor>" by auto
	  with mbisim obtain X2 where "ts2 t' = \<lfloor>(X2, LN)\<rfloor>" "t' \<turnstile> (X1, m1)  \<approx> (X2, m2)" "ws1 t' = None \<or> X1 \<approx>w X2"
	    by(auto dest: mbisim_thrD1)
	  with False show ?thesis by auto
	qed
      next
	show "finite (dom (thr s1'))" by simp
      next
        from mbisim_wset_thread_ok1[OF mbisim]
        show "wset_thread_ok (wset s1') (thr s1')"
          by(auto intro: wset_thread_ok_upd)
      qed
      ultimately show ?thesis by(auto)
    qed
  next
    case redT_acquire
    with tst have False by(auto simp add: expand_fun_eq)
    thus ?thesis ..
  qed
qed

lemma mbisim_simulation_silent2_measure:
  "\<lbrakk> s1 \<approx>m s2; r2.mthr.silent_move s2 s2' \<rbrakk>
  \<Longrightarrow> s1 \<approx>m s2' \<and> r2.m\<mu>^++ s2' s2 \<or> (\<exists>s1'. r1.mthr.silent_move^++ s1 s1' \<and> s1' \<approx>m s2')"
using FWdelay_bisimulation_measure.mbisim_simulation_silent1_measure[OF FWdelay_bisimulation_measure_flip]
unfolding flip_simps .

theorem mbisim_delay_bisimulation_measure:
  "delay_bisimulation_measure r1.redT r2.redT mbisim mta_bisim m\<tau>move1 m\<tau>move2 r1.m\<mu> r2.m\<mu>"
by(unfold_locales)(rule mbisim_simulation_silent1_measure mbisim_simulation_silent2_measure mbisim_simulation1[OF bisim_inv_wfs_inv2[OF bisim_inv]] mbisim_simulation2[OF bisim_inv_wfs_inv1[OF bisim_inv]] r1.wf_m\<mu> r2.wf_m\<mu>|assumption)+

end

sublocale FWdelay_bisimulation_measure <
  mthr!: delay_bisimulation_measure r1.redT r2.redT mbisim mta_bisim m\<tau>move1 m\<tau>move2 r1.m\<mu> r2.m\<mu>
by(rule mbisim_delay_bisimulation_measure)

subsection {* Strong bisimulation as corollary *}

locale Notified_shr_unchanged =
  multithreaded_base + 
  constrains final :: "'x \<Rightarrow> bool"
  and r :: "('l,'t,'x,'m,'w,'o) semantics"
  assumes Notified_shr: "t \<turnstile> (x1, m1) -\<epsilon>\<lbrace>\<^bsub>c\<^esub> Notified \<rbrace>\<rightarrow> (x1', m1') \<Longrightarrow> m1' = m1"

locale FWbisimulation = FWbisimulation_base _ _ _ r2 bisim "\<lambda>x1 x2. True" +
  r1!: final_thread_wf final1 r1 +
  r2!: final_thread_wf final2 r2 +
  r1!: Notified_shr_unchanged final1 r1 +
  r2!: Notified_shr_unchanged final2 r2 
  for r2 :: "('l,'t,'x2,'m2,'w,'o) semantics" ("_ \<turnstile> _ -2-_\<rightarrow> _" [50,0,0,50] 80)
  and bisim :: "'t \<Rightarrow> ('x1 \<times> 'm1, 'x2 \<times> 'm2) bisim" ("_ \<turnstile> _/ \<approx> _" [50, 50, 50] 60) +
  assumes bisimulation_locale: "bisimulation (r1 t) (r2 t) (bisim t) (ta_bisim bisim)"
  and bisim_final: "t \<turnstile> (x1, m1) \<approx> (x2, m2) \<Longrightarrow> final1 x1 \<longleftrightarrow> final2 x2"
  and bisim_inv_red_other:
   "\<lbrakk> t' \<turnstile> (x, m1) \<approx> (xx, m2); t \<turnstile> (x1, m1) \<approx> (x2, m2); 
      t \<turnstile> (x1, m1) -1-ta1\<rightarrow> (x1', m1'); t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2'); 
      t \<turnstile> (x1', m1') \<approx> (x2', m2'); ta_bisim bisim ta1 ta2 \<rbrakk>
   \<Longrightarrow> t' \<turnstile> (x, m1') \<approx> (xx, m2')"

sublocale FWbisimulation < bisimulation "r1 t" "r2 t" "bisim t" "ta_bisim bisim" for t
by(rule bisimulation_locale)

sublocale FWbisimulation <
  FWdelay_bisimulation_diverge final1 r1 final2 r2 bisim "\<lambda>x1 x2. True" "\<lambda>s ta s'. False" "\<lambda>s ta s'. False"
proof -
  interpret biw: bisimulation_into_delay "r1 t" "r2 t" "bisim t" "ta_bisim bisim" "\<lambda>s ta s'. False" "\<lambda>s ta s'. False"
    for t
    by(unfold_locales) simp
  show "FWdelay_bisimulation_diverge final1 r1 final2 r2 bisim (\<lambda>x1 x2. True) (\<lambda>s ta s'. False) (\<lambda>s ta s'. False)"
  proof(unfold_locales)
    fix t' x m1 xx m2 x1 x2 t x1' ta1 x1'' m1' x2' ta2 x2'' m2'
    assume bisim: "t' \<turnstile> (x, m1) \<approx> (xx, m2)" and bisim12: "t \<turnstile> (x1, m1) \<approx> (x2, m2)"
      and \<tau>1: "\<tau>trsys.silent_moves (r1 t) (\<lambda>s ta s'. False) (x1, m1) (x1', m1)" 
      and red1: "t \<turnstile> (x1', m1) -1-ta1\<rightarrow> (x1'', m1')"
      and \<tau>2: "\<tau>trsys.silent_moves (r2 t) (\<lambda>s ta s'. False) (x2, m2) (x2', m2)"
      and red2: "t \<turnstile> (x2', m2) -2-ta2\<rightarrow> (x2'', m2')"
      and bisim12': "t \<turnstile> (x1'', m1') \<approx> (x2'', m2')" and tasim: "ta1 \<sim>m ta2"
    from \<tau>1 \<tau>2 have [simp]: "x1' = x1" "x2' = x2" by(simp_all add: rtranclp_False \<tau>moves_False)
    from bisim12 bisim_inv_red_other[OF bisim _ red1 red2 bisim12' tasim]
    show "t' \<turnstile> (x, m1') \<approx> (xx, m2')" by simp
  next
    fix t x1 m1 x2 m2 x1'
    assume "t \<turnstile> (x1, m1) \<approx> (x2, m2)"
      and "t \<turnstile> (x1, m1) -1-\<epsilon>\<lbrace>\<^bsub>c\<^esub>Notified\<rbrace>\<rightarrow> (x1', m1)"
    from simulation1[OF this] show "\<exists>x2'. t \<turnstile> (x2, m2) -2-\<epsilon>\<lbrace>\<^bsub>c\<^esub>Notified\<rbrace>\<rightarrow> (x2', m2) \<and> t \<turnstile> (x1', m1) \<approx> (x2', m2)"
      by(auto simp add: ta_bisim_def ta_upd_simps dest: simulation1 r2.Notified_shr[simplified])
  next
    fix t x1 m1 x2 m2 x2'
    assume "t \<turnstile> (x1, m1) \<approx> (x2, m2)"
      and "t \<turnstile> (x2, m2) -2-\<epsilon>\<lbrace>\<^bsub>c\<^esub>Notified\<rbrace>\<rightarrow> (x2', m2)"
    from simulation2[OF this] show "\<exists>x1'. t \<turnstile> (x1, m1) -1-\<epsilon>\<lbrace>\<^bsub>c\<^esub>Notified\<rbrace>\<rightarrow> (x1', m1) \<and> t \<turnstile> (x1', m1) \<approx> (x2', m2)"
      by(auto simp add: ta_bisim_def ta_upd_simps dest: simulation2 r1.Notified_shr[simplified])
  next
    fix t x1 m1 x2 m2 ta1 x1' m1'
    assume bisim: "t \<turnstile> (x1, m1) \<approx> (x2, m2)"
      and red: "t \<turnstile> (x1, m1) -1-ta1\<rightarrow> (x1', m1')" 
    from simulation1[OF bisim red]
    show "\<exists>x2' m2' ta2. t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2') \<and> t \<turnstile> (x1', m1') \<approx> (x2', m2') \<and> ta1 \<sim>m ta2" by(auto)
  next
    fix t x1 m1 x2 m2 ta2 x2' m2'
    assume "t \<turnstile> (x1, m1) \<approx> (x2, m2)" "t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2')"
    from simulation2[OF this]
    show "\<exists>x1' m1' ta1. t \<turnstile> (x1, m1) -1-ta1\<rightarrow> (x1', m1') \<and> t \<turnstile> (x1', m1') \<approx> (x2', m2') \<and> ta1 \<sim>m ta2"
      by(auto)
  qed(fastsimp simp add: bisim_final)+
qed

context FWbisimulation begin

lemma FWbisimulation_flip: "FWbisimulation final2 r2 final1 r1 (\<lambda>t. flip (bisim t))"
apply(rule FWbisimulation.intro)
    apply(rule r2.final_thread_wf_axioms)
   apply(rule r1.final_thread_wf_axioms)
  apply(rule r2.Notified_shr_unchanged_axioms)
 apply(rule r1.Notified_shr_unchanged_axioms)
apply(rule FWbisimulation_axioms.intro)
   apply(unfold flip_simps)
   apply(rule bisimulation_axioms)
 apply(erule bisim_final[symmetric])
by(rule bisim_inv_red_other)

end

lemma FWbisimulation_flip_simps [flip_simps]:
  "FWbisimulation final2 r2 final1 r1 (\<lambda>t. flip (bisim t)) = FWbisimulation final1 r1 final2 r2 bisim"
by(auto dest: FWbisimulation.FWbisimulation_flip simp only: flip_flip)

context FWbisimulation begin

text {*
  The notation for mbisim is lost because @{term "bisim_wait"} is instantiated to @{term "\<lambda>x1 x2. True"}.
  This reintroduces the syntax, but it does not work for displaying. This would require a new abbreviation.
*}
notation mbisim ("_ \<approx>m _" [50, 50] 60)

theorem mbisim_bisimulation:
  "bisimulation r1.redT r2.redT mbisim mta_bisim"
proof
  fix s1 s2 tta1 s1'
  assume mbisim: "s1 \<approx>m s2" and "r1.redT s1 tta1 s1'"
  from mthr.simulation1[OF this]
  show "\<exists>s2' tta2. r2.redT s2 tta2 s2' \<and> s1' \<approx>m s2' \<and> tta1 \<sim>T tta2"
    by(auto simp add: \<tau>moves_False m\<tau>move_False)
next
  fix s2 s1 tta2 s2'
  assume "s1 \<approx>m s2" and "r2.redT s2 tta2 s2'"
  from mthr.simulation2[OF this]
  show "\<exists>s1' tta1. r1.redT s1 tta1 s1' \<and> s1' \<approx>m s2' \<and> tta1 \<sim>T tta2"
    by(auto simp add: \<tau>moves_False m\<tau>move_False)
qed

lemma mbisim_wset_eq:
  "s1 \<approx>m s2 \<Longrightarrow> wset s1 = wset s2"
by(simp add: mbisim_def)

lemma mbisim_mfinal:
  "s1 \<approx>m s2 \<Longrightarrow> r1.mfinal s1 \<longleftrightarrow> r2.mfinal s2"
apply(auto intro!: r2.mfinalI r1.mfinalI dest: mbisim_thrD2 mbisim_thrD1 bisim_final elim: r1.mfinalE r2.mfinalE)
apply(frule (1) mbisim_thrD2, drule mbisim_wset_eq, auto elim: r1.mfinalE)
apply(frule (1) mbisim_thrD1, drule mbisim_wset_eq, auto elim: r2.mfinalE)
done

end

sublocale FWbisimulation < mthr!: bisimulation r1.redT r2.redT mbisim mta_bisim
by(rule mbisim_bisimulation)

sublocale FWbisimulation < mthr!: bisimulation_final r1.redT r2.redT mbisim mta_bisim r1.mfinal r2.mfinal
by(unfold_locales)(rule mbisim_mfinal)

sublocale FWdelay_bisimulation_measure < FWdelay_bisimulation_diverge
by(unfold_locales)

end