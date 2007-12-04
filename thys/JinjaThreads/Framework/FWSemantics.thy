(*  Title:      JinjaThreads/Framework/FWSemantics.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{The multithreaded semantics} *}

theory FWSemantics imports FWWellform begin

(* Update functions for the wait sets in the multithreaded state *)

fun redT_updW :: "('w,'t) wait_sets \<Rightarrow> 't \<Rightarrow> 'w wait_set_action \<Rightarrow> ('w,'t) wait_sets"
where
  "redT_updW ws t (Notify w) = (if (\<exists>t. ws t = \<lfloor>w\<rfloor>) then ws((SOME t. ws t = \<lfloor>w\<rfloor>) := None) else ws)"
| "redT_updW ws t (NotifyAll w) = (\<lambda>t. if ws t = \<lfloor>w\<rfloor> then None else ws t)"
| "redT_updW ws t (Suspend w) = ws(t \<mapsto> w)"

fun redT_updWs :: "('w,'t) wait_sets \<Rightarrow> 't \<Rightarrow> 'w wait_set_action list \<Rightarrow> ('w,'t) wait_sets"
where
  "redT_updWs ws t [] = ws"
| "redT_updWs ws t (wa#was) = redT_updWs (redT_updW ws t wa) t was"

lemma redT_updWs_append [simp]:
  "redT_updWs ws t (was @ was') = redT_updWs (redT_updWs ws t was) t was'"
by(induct was arbitrary: ws, auto)

definition
  redT_upd :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w) thread_action \<Rightarrow> ('l,'t,'x,'m,'w) state"
where
  "redT_upd lstsmws t ta \<equiv>
   (redT_updLs (locks lstsmws) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>,
    (redT_updTs (thr lstsmws) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>, shr lstsmws),
    redT_updWs (wset lstsmws) t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>)"

declare redT_upd_def[simp]


locale multithreaded =
  fixes r :: "('l,'t,'x,'m,'w) semantics"
begin

abbreviation
  r_sytnax1 :: "'x \<times> 'm \<Rightarrow> ('l,'t,'x,'m,'w) thread_action \<Rightarrow> 'x \<times> 'm \<Rightarrow> bool" ("_ -_\<rightarrow> _" [50,0,50] 80)
where
  "s -ta\<rightarrow> s' \<equiv> (s, ta, s') \<in> r"

abbreviation
  r_syntax2 :: "'x \<Rightarrow> 'm \<Rightarrow> ('l,'t,'x,'m,'w) thread_action \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool" ("\<langle>_, _\<rangle> -_\<rightarrow> \<langle>_, _\<rangle>" [0,0,0,0,0] 80)
where
  "\<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<equiv> (x, m) -ta\<rightarrow> (x', m')"

inductive_set
  redT :: "(('l,'t,'x,'m,'w) state \<times> ('t \<times> ('l,'t,'x,'m,'w) thread_action) \<times> ('l,'t,'x,'m,'w) state) set"
where
  "\<lbrakk> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>;
     thr s t = \<lfloor>x\<rfloor>; wset s t = None;
     lock_ok_las (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>; thread_oks (thr s) m' \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>;
     s' = redT_upd (locks s, ((thr s)(t \<mapsto> x'), m'), wset s) t ta\<rbrakk>
  \<Longrightarrow> (s, (t, ta), s') \<in> redT"

abbreviation
  redT_syntax1 :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w) thread_action \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> bool" ("_ -_\<triangleright>_\<rightarrow> _" [50,0,0,50] 80)
where
  "s -t\<triangleright>ta\<rightarrow> s' \<equiv> (s, (t,ta), s') \<in> redT"

abbreviation
  redT_syntax2 :: "('l,'t) locks \<Rightarrow> ('t,'x) thread_info \<times> 'm \<Rightarrow> ('w,'t) wait_sets
                   \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w) thread_action
                   \<Rightarrow> ('l,'t) locks \<Rightarrow> ('t,'x) thread_info \<times> 'm \<Rightarrow> ('w,'t) wait_sets \<Rightarrow> bool" ("\<langle>_, _, _\<rangle> -_\<triangleright>_\<rightarrow> \<langle>_, _, _\<rangle>" [0,0,0,0,0,0,0,0] 80)
where
  "\<langle>ls, tsm, ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', tsm', ws'\<rangle> \<equiv> (ls, tsm, ws) -t\<triangleright>ta\<rightarrow> (ls', tsm', ws')"


definition
  RedT :: "(('l,'t,'x,'m,'w) state \<times> ('t \<times> ('l,'t,'x,'m,'w) thread_action) list \<times> ('l,'t,'x,'m,'w) state) set"
where
  "RedT \<equiv> stepify redT"

abbreviation
  RedT_syntax1 :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('t \<times> ('l,'t,'x,'m,'w) thread_action) list \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> bool" ("_ -\<triangleright>_\<rightarrow>* _" [50,0,50] 80)
where
  "s -\<triangleright>ttas\<rightarrow>* s' \<equiv> (s, ttas, s') \<in> RedT"

abbreviation
  RedT_syntax2 :: "('l,'t) locks \<Rightarrow> ('t,'x) thread_info \<times> 'm \<Rightarrow> ('w,'t) wait_sets
                   \<Rightarrow> ('t \<times> ('l,'t,'x,'m,'w) thread_action) list 
                   \<Rightarrow> ('l,'t) locks \<Rightarrow> ('t,'x) thread_info \<times> 'm \<Rightarrow> ('w,'t) wait_sets \<Rightarrow> bool" ("\<langle>_, _, _\<rangle> -\<triangleright>_\<rightarrow>* \<langle>_, _, _\<rangle>" [0,0,0,0,0,0,0] 80)
where
  "\<langle>ls, tsm, ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', tsm', ws'\<rangle> \<equiv> ((ls, tsm, ws), ttas, ls', tsm', ws') \<in> RedT"

lemma RedTI:
  "x \<in> stepify redT \<Longrightarrow> x \<in> RedT"
by(simp add: RedT_def)

lemma RedTE:
  "\<lbrakk> x \<in> RedT; x \<in> stepify redT \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by(auto simp add: RedT_def)

lemma RedTD:
  "x \<in> RedT \<Longrightarrow> x \<in> stepify redT"
by(simp add: RedT_def)

lemma RedT_induct [consumes 1, case_names refl step]:
  "\<lbrakk> s -\<triangleright>ttas\<rightarrow>* s';
     \<And>s. P s [] s;
     \<And>s ttas s' t ta s''. \<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; P s ttas s'; s' -t\<triangleright>ta\<rightarrow> s'' \<rbrakk> \<Longrightarrow> P s (ttas @ [(t, ta)]) s''\<rbrakk>
  \<Longrightarrow> P s ttas s'"
by(auto intro: stepify.induct simp add: RedT_def)


lemma RedT_induct4 [consumes 1, case_names refl step]:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>;
     \<And>ls ts m ws. P ls ts m ws [] ls ts m ws;
     \<And>ls ts m ws ttas ls' ts' m' ws' t ta ls'' ts'' m'' ws''.
       \<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>; 
         P ls ts m ws ttas ls' ts' m' ws';
         \<langle>ls', (ts', m'), ws'\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls'', (ts'', m''), ws''\<rangle> \<rbrakk> 
       \<Longrightarrow> P ls ts m ws (ttas @ [(t, ta)]) ls'' ts'' m'' ws'' \<rbrakk>
  \<Longrightarrow> P ls ts m ws ttas ls' ts' m' ws'"
apply(unfold RedT_def)
apply(erule stepify_induct4')
by(auto)

lemma RedT_lift_preserveD:
  assumes Red: "s -\<triangleright>ttas\<rightarrow>* s'"
  and preserve: "\<And>s t tas s'. \<lbrakk> s -t\<triangleright>tas\<rightarrow> s'; P s \<rbrakk> \<Longrightarrow> P s'"
  and P: "P s"
  shows "P s'"
proof -
  from Red P show ?thesis
    apply(induct rule: RedT_induct)
    by(auto intro: preserve)
qed

lemma RedT_lift_preserveD4:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>; 
     \<And>ls ts m ws t ta ls' ts' m' ws'. \<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; P ls ts m ws \<rbrakk> \<Longrightarrow> P ls' ts' m' ws';
     P ls ts m ws \<rbrakk>
  \<Longrightarrow> P ls' ts' m' ws'"
apply(drule RedT_lift_preserveD[where P="(\<lambda>(ls, (ts, m), ws). P ls ts m ws)"])
by(auto)

lemma redT_has_locks_inv:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; t \<noteq> t' \<rbrakk> \<Longrightarrow>
  has_locks (ls l) t' = has_locks (ls' l) t'"
apply(auto elim!: redT.cases intro: redT_updLs_has_locks[THEN sym])
done

lemma redT_has_lock_inv:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; t \<noteq> t' \<rbrakk>
  \<Longrightarrow> has_lock (ls' l) t' = has_lock (ls l) t'"
by(auto simp add: has_lock_has_locks_conv redT_has_locks_inv intro: ext )

lemma redT_ts_Some_inv:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; t \<noteq> t'; ts t' = \<lfloor>x\<rfloor> \<rbrakk> \<Longrightarrow> ts' t' = \<lfloor>x\<rfloor>"
by(auto elim!: redT.cases simp: redT_updTs_upd[THEN sym] intro: redT_updTs_Some)

lemma redT_new_thread_common:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; NewThread t' x m'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> m'' = m'"
by(auto elim!: redT.cases elim: thread_oks_commonD[THEN sym])

lemma redT_new_thread:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t'\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; ts' t = \<lfloor>x\<rfloor>; ts t = None \<rbrakk> \<Longrightarrow> NewThread t x m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
by(auto elim!: redT.cases intro!: redT_updTs_new_thread simp add: thread_oks_upd)

lemma redT_thread_not_disappear:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; ts' t' = None\<rbrakk> \<Longrightarrow> ts t' = None"
apply(erule redT.cases, clarsimp)
apply(simp only: redT_updTs_upd[THEN sym], simp split: if_splits)
by(erule redT_updTs_None)

lemma RedT_thread_not_disappear:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>; ts' t' = None\<rbrakk> \<Longrightarrow> ts t' = None"
apply(erule contrapos_pp[where Q="ts' t' = None"])
apply(drule RedT_lift_preserveD4[where P="\<lambda>ls ts m ws. ts t' \<noteq> None"])
apply(erule_tac Q="tsa t' = None" in contrapos_nn)
apply(erule redT_thread_not_disappear)
apply(auto)
done

lemma redT_new_thread_ts_Some:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; NewThread t' x m'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> ts' t' = \<lfloor>x\<rfloor>"
apply(erule redT.cases, clarsimp)
apply(simp only: redT_updTs_upd[THEN sym])
apply(auto dest: thread_oks_new_thread elim: redT_updTs_new_thread_ts)
done

lemma RedT_new_thread_ts_not_None:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>;
     NewThread t x m'' \<in> set (\<down>map (thr_a \<circ> snd) ttas\<down>) \<rbrakk>
   \<Longrightarrow> ts' t \<noteq> None"
proof(induct rule: RedT_induct4)
  case refl thus ?case by simp
next
  case (step LS TS M WS TTAS LS' TS' M' WS' T TA LS'' TS'' M'' WS'')
  note Red = `\<langle>LS, (TS, M), WS\<rangle> -\<triangleright>TTAS\<rightarrow>* \<langle>LS', (TS', M'), WS'\<rangle>`
  note IH = `NewThread t x m'' \<in> set (\<down>map (thr_a \<circ> snd) TTAS\<down>) \<Longrightarrow> TS' t \<noteq> None`
  note red = `\<langle>LS', (TS', M'), WS'\<rangle> -T\<triangleright>TA\<rightarrow> \<langle>LS'', (TS'', M''), WS''\<rangle>`
  note ins = `NewThread t x m'' \<in> set (\<down>map (thr_a \<circ> snd) (TTAS @ [(T, TA)])\<down>)`
  show ?case
  proof(cases "NewThread t x m'' \<in> set \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>")
    case True
    moreover
    with red have "m'' = M''" 
      by(auto elim: redT_new_thread_common) 
    ultimately show ?thesis using red
      by(auto dest!: redT_new_thread_ts_Some)
  next
    case False
    hence "NewThread t x m'' \<in> set (\<down>map (thr_a \<circ> snd) TTAS\<down>)" using ins by(auto)
    hence "TS' t \<noteq> None" by -(rule IH)
    with red show ?thesis
      by -(erule contrapos_nn, erule redT_thread_not_disappear)
  qed
qed


lemma redT_preserves_lock_thread_ok:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; lock_thread_ok ls ts \<rbrakk> \<Longrightarrow> lock_thread_ok ls' ts'"
apply(auto elim!: redT.cases intro!: redT_upds_preserves_lock_thread_ok lock_thread_ok_upd thread_oks_upd[THEN iffD2])
done

lemma RedT_preserves_lock_thread_ok:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>; lock_thread_ok ls ts \<rbrakk> \<Longrightarrow> lock_thread_ok ls' ts'"
apply(erule RedT_lift_preserveD4)
by(erule redT_preserves_lock_thread_ok)

lemma RedT_newThread_unique:
  assumes red: "\<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>"
  and ts't: "ts' t = \<lfloor>x\<rfloor>"
  and tst: "ts t = None"
  shows "\<exists>!n. n < length ttas \<and> (\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd (ttas!n))))"
using prems
proof(induct arbitrary: x rule: RedT_induct4)
  case refl thus ?case by auto
next
  case (step LS TS M WS TTAS LS' TS' M' WS' T TA LS'' TS'' M'' WS'' X)
  note RedT = `\<langle>LS, (TS, M), WS\<rangle> -\<triangleright>TTAS\<rightarrow>* \<langle>LS', (TS', M'), WS'\<rangle>`
  note IH = `\<And>x. \<lbrakk>TS' t = \<lfloor>x\<rfloor>; TS t = None\<rbrakk> \<Longrightarrow> \<exists>!n. n < length TTAS \<and> (\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd (TTAS ! n))))`
  note red = `\<langle>LS', (TS', M'), WS'\<rangle> -T\<triangleright>TA\<rightarrow> \<langle>LS'', (TS'', M''), WS''\<rangle>`
  note ts''t = `TS'' t = \<lfloor>X\<rfloor>`
  note tst = `TS t = None`
  show ?case
  proof(cases "TS' t")
    case None
    note ts't = `TS' t = None`
    with ts''t red have ta: "NewThread t X M'' \<in> set \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>"
      by - (rule redT_new_thread)
    show ?thesis
    proof(rule ex1I)
      show "length TTAS < length (TTAS @ [(T, TA)]) \<and>
	    (\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd ((TTAS @ [(T, TA)]) ! length TTAS))))"
	using ta by auto
    next
      fix n'
      assume "n' < length (TTAS @ [(T, TA)]) \<and>
	      (\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd ((TTAS @ [(T, TA)]) ! n'))))"
      hence n'l: "n' < length (TTAS @ [(T, TA)])" 
	and blubb: "\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd ((TTAS @ [(T, TA)]) ! n')))" 
	by auto
      from blubb obtain m' x'
	where e'x': "NewThread t x' m' \<in> set (thr_a (snd ((TTAS @ [(T, TA)]) ! n')))"
	by blast
      { assume "n' < length TTAS"
	with e'x' have "NewThread t x' m' \<in> set (\<down>map (thr_a \<circ> snd) TTAS\<down>)"
	  apply(simp add: nth_append)
	  apply(erule_tac x="TTAS ! n'" in bexI)
	  by auto
	hence "TS' t \<noteq> None" using RedT by -(erule RedT_new_thread_ts_not_None)
	with ts't have False by simp }
      thus "n' = length TTAS" using n'l by(simp, arith)
    qed
  next
    fix x
    assume e'x': "TS' t = \<lfloor>x\<rfloor>"
    with tst have "\<exists>!n. n < length TTAS \<and> (\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd (TTAS ! n))))"
      by -(rule IH)
    then obtain n
      where nl: "n < length TTAS"
      and exe'x': "\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd (TTAS ! n)))"
      and unique: "\<forall>n'. n' < length TTAS \<and> (\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd (TTAS ! n')))) \<longrightarrow> n' = n"
      by(blast elim: ex1E)
    show ?thesis
    proof(rule ex1I)
      show "n < length (TTAS @ [(T, TA)]) \<and>
	    (\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd ((TTAS @ [(T, TA)]) ! n))))"
	using nl exe'x' by(simp add: nth_append)
    next
      fix n'
      assume "n' < length (TTAS @ [(T, TA)]) \<and>
	      (\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd ((TTAS @ [(T, TA)]) ! n'))))"
      hence n'l: "n' < length (TTAS @ [(T, TA)])"
	and ex'e'x': "\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd ((TTAS @ [(T, TA)]) ! n')))"
	by auto
      { assume "n' = length TTAS"
	with ex'e'x' have "\<exists>x' m'. NewThread t x' m' \<in> set \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>"
	  by(auto simp add: nth_append)
	then obtain m'' x''
	  where "NewThread t x'' m'' \<in> set \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>" by blast
	with red have "TS' t = None"
	  apply -
	  apply(erule redT.cases, clarsimp)
	  by(erule thread_oks_new_thread)
	with e'x' have False by auto }
      moreover
      { assume "n' < length TTAS"
	moreover
	with ex'e'x' have "\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd (TTAS ! n')))"
	  by(simp add: nth_append)
	ultimately have "n' = n" using unique by(force) }
      ultimately show "n' = n" using n'l apply(auto) by(arith)
    qed
  qed
qed

end (* locale multithreaded *)

end 
