(*  Title:      JinjaThreads/J/TypeSafeThreaded.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Type safety for the multithreaded case} *}

theory TypeSafeThreaded
imports TypeSafe ProgressThreaded
begin

lemma red_def_ass_new_thread:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t'' (e'', x'') c'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> \<D> e'' \<lfloor>dom x''\<rfloor>"
apply(induct rule: red.induct)
apply(auto)
apply(simp add: hyper_isin_def)
done

lemma lifting_wf_def_ass: "wf_J_prog P \<Longrightarrow> lifting_wf (mred P) (\<lambda>(e, x) m. \<D> e \<lfloor>dom x\<rfloor>)"
apply(unfold_locales)
apply(auto dest: red_preserves_defass red_def_ass_new_thread)
done

lemmas redT_preserves_defass = lifting_wf.redT_preserves[OF lifting_wf_def_ass]

lemmas RedT_preserves_defass = lifting_wf.RedT_preserves[OF lifting_wf_def_ass]

definition sconf_subject_ok :: "J_prog \<Rightarrow> (env \<times> ty) \<Rightarrow> expr \<Rightarrow> heap \<Rightarrow> locals \<Rightarrow> bool" where
  "sconf_subject_ok P ET e h l \<equiv> P,fst ET \<turnstile> (h, l) \<surd> \<and> subject_ok P ET e h"

abbreviation
  sconf_subject_ts_ok :: "J_prog \<Rightarrow> (thread_id \<rightharpoonup> (env \<times> ty)) \<Rightarrow> (thread_id,expr \<times> locals) thread_info \<Rightarrow> heap \<Rightarrow> bool"
where
  "sconf_subject_ts_ok \<equiv> \<lambda>P. ts_inv (\<lambda>ET (e, x) m. sconf_subject_ok P ET e m x)"

lemma red_sconf_subject_newthread_aux:
  assumes wf: "wf_J_prog P"
  and red: "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  and ta: "NewThread t'' (e'', x'') (hp s') \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  and wt: "P,E,hp s \<turnstile> e : T"
  and sconf: "P,(E::env) \<turnstile> s \<surd>"
  shows "\<exists>E T. P,E,hp s \<turnstile> e'' : T \<and> P,hp s \<turnstile> x'' (:\<le>) E"
proof -
  from prems have isclassThread: "is_class P Thread"
    by(auto intro!: NewThread_is_class_Thread)
  from red ta wt show ?thesis
  proof(induct arbitrary: E T rule: red.induct)
    prefer 38
    case (RedNewThread s a C fs t E T)
    have wt: "P,E,hp s \<turnstile> addr a\<bullet>start([]) : T" .
    have hpsa: "hp s a = \<lfloor>Obj C fs\<rfloor>" .
    have PCThread: "P \<turnstile> C \<preceq>\<^sup>* Thread" .
    note `NewThread t'' (e'', x'') (hp s) \<in> set \<lbrace>\<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThread t (Var this\<bullet>run([]), [this \<mapsto> Addr a]) (hp s)\<rbrace>\<rbrace>\<^bsub>t\<^esub>`
    hence NT: "NewThread t (Var this\<bullet>run([]), [this \<mapsto> Addr a]) (hp s)  = NewThread t'' (e'', x'') (hp s)" by simp
    have "\<exists>D body. P \<turnstile> C sees run: []\<rightarrow>Void = ([], body) in D"
      by(rule sub_Thread_sees_run[OF wf PCThread isclassThread])
    hence "(P,[this \<mapsto> Class C],hp s \<turnstile> Var this\<bullet>run([]) : Void)"
      by(auto intro: WTrtCall WTrtVar)
    moreover have "(P,hp s \<turnstile> [this \<mapsto> Addr a] (:\<le>) [this \<mapsto> Class C])" using hpsa
      by(simp add: lconf_def)
    ultimately show ?case using NT
      apply(clarsimp)
      apply(rule_tac x="[this \<mapsto> Class C]" in exI)
      apply(clarsimp)
      by(rule_tac x="Void" in exI)
  qed(fastsimp simp add: list_all2_append1 list_all2_Cons1)+
qed

lemma red_preserve_welltype:
  "\<lbrakk> P \<turnstile> \<langle>e, (h, x)\<rangle> -ta\<rightarrow> \<langle>e', (h', x')\<rangle>; P,E,h \<turnstile> e'' : T \<rbrakk> \<Longrightarrow> P,E,h' \<turnstile> e'' : T"
apply(auto elim: WTrt_hext_mono red_hext_incr)
done

lemma red_sconf_subject_newthread:
  "\<lbrakk> P \<turnstile> \<langle>e,(h, x)\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>;
     NewThread t'' (e'', x'') h' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>;
     P,E,h \<turnstile> e : T; wf_J_prog P; P,E \<turnstile> (h, x) \<surd> \<rbrakk> 
  \<Longrightarrow> \<exists>E T. P,E,h' \<turnstile> e'' : T \<and> P,h' \<turnstile> x'' (:\<le>) E"
apply(frule red_sconf_subject_newthread_aux)
    apply(assumption)
   apply(fastsimp)
  apply(fastsimp)
 apply(assumption)
apply(clarify)
apply(rule_tac x="Ea" in exI)
apply(rule_tac x="Ta" in exI)
apply(auto elim: red_preserve_welltype)
apply(drule red_hext_incr)
by(erule lconf_hext)

lemma lifting_inv_sconf_subject_ok:
  "wf_J_prog P \<Longrightarrow> lifting_inv (mred P) (\<lambda>(e, x) m. \<D> e \<lfloor>dom x\<rfloor>) (\<lambda>ET (e, x) m. sconf_subject_ok P ET e m x)"
apply(auto simp: lifting_inv_def intro: lifting_wf_def_ass)
apply(unfold_locales)
  apply(auto simp add: subject_ok_def sconf_subject_ok_def sconf_def)
       apply(fastsimp dest: red_preserves_hconf)
      apply(fastsimp dest: red_preserves_lconf)
     apply(drule subject_reduction, assumption)
       apply(simp add: sconf_def)
      apply(simp)
     apply(fastsimp elim: widen_trans)
    apply(fastsimp dest: red_preserves_hconf)
   apply(frule red_sconf_subject_newthread)
       apply(fastsimp)
      apply(fastsimp)
     apply(assumption)
    apply(simp add: sconf_def)
   apply(fastsimp dest: red_preserves_hconf)
  apply(fastsimp dest: red_preserves_hconf)
 apply(drule red_hext_incr)
 apply(erule lconf_hext, assumption)
apply(rule_tac x="T'a" in exI)
apply(clarsimp)
by(erule red_preserve_welltype)

lemmas redT_invariant_sconf_subject = lifting_inv.redT_invariant[OF lifting_inv_sconf_subject_ok]

lemmas RedT_invariant_sconf_subject = lifting_inv.RedT_invariant[OF lifting_inv_sconf_subject_ok]


lemma sconf_subject_es_ok_wt_es_ok:
  "sconf_subject_ts_ok P Es es c \<Longrightarrow> wt_ts_ok P es c"
apply(rule ts_okI)
apply(drule ts_invD, assumption)
apply(auto simp add: subject_ok_def sconf_subject_ok_def)
done


lemmas RedT_preserves_es_inv_ok = multithreaded.RedT_preserves_ts_inv_ok[where r="mred P"]

corollary TypeSafetyT:
  assumes wf: "wf_J_prog P"
  and sconf_subject: "sconf_subject_ts_ok P Es ts m"
  and defass: "def_ass_ts_ok ts m"
  and lock: "lock_ok ls ts"
  and addr: "addr_es_ok ts m"
  and RedT: "P \<turnstile> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>"
  and esinv: "ts_inv_ok ts Es"
  and nored: "\<not> (\<exists>t ta ts'' ls'' ws'' m''. P \<turnstile> \<langle>ls', (ts', m'), ws'\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls'', (ts'', m''), ws''\<rangle>)"
  shows "let Es' = upd_invs Es (\<lambda>ET (e, x) m. sconf_subject_ok P ET e m x) (\<down>map (thr_a \<circ> snd) (ttas::(nat \<times> (nat \<Rightarrow> lock_action list) \<times> (nat, char list exp \<times> (char list \<rightharpoonup> val), nat \<rightharpoonup> heapobj) new_thread_action list \<times> nat wait_set_action list) list)\<down>) in
         (\<forall>t e'. \<exists>x'. ts' t = \<lfloor>(e', x')\<rfloor> \<longrightarrow>
                   (\<exists>v. e' = Val v \<and> (\<exists>E T. Es' t = \<lfloor>(E, T)\<rfloor> \<and> P,m' \<turnstile> v :\<le> T))
                 \<or> (\<exists>a. e' = Throw a \<and> a \<in> dom m')
                 \<or> t \<in> progress.deadlocked (mred P) final_expr (ls', (ts', m'), ws') \<and> (\<exists>E T. Es' t = \<lfloor>(E, T)\<rfloor> \<and> (\<exists>T'. P,E,m' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T)))
         \<and> Es \<unlhd> Es'"
proof -
  let ?Es' = "upd_invs Es (\<lambda>ET (e, x) m. sconf_subject_ok P ET e m x) (\<down>map (thr_a \<circ> snd) ttas\<down>)"
  from RedT have defass': "def_ass_ts_ok ts' m'"
    by(rule RedT_preserves_defass[OF wf _ defass])
  from RedT lock addr wf have lock': "lock_ok ls' ts'"
    by (auto intro: RedT_preserves_lock_ok wf_prog_wwf_prog)
  from RedT addr wf have addr': "addr_es_ok ts' m'"
    apply-
    apply(rule RedT_preserves_addr_ok)
    by(erule wf_prog_wwf_prog)
  from RedT sconf_subject wf defass
  have sconf_subject': "sconf_subject_ts_ok P ?Es' ts' m'"
    by-(rule RedT_invariant_sconf_subject)
  { fix t e' x'
    assume es't: "ts' t = \<lfloor>(e', x')\<rfloor>"
    from sconf_subject' es't obtain E T where ET: "?Es' t = \<lfloor>(E, T)\<rfloor>" by(auto dest!: ts_invD)
    { assume "\<exists>v. e' = Val v"
      then obtain v where v: "e' = Val v" by blast
      with sconf_subject' ET es't have "P,m' \<turnstile> v :\<le> T"
	apply -
	apply(drule ts_invD, assumption)
	by(clarsimp simp add: subject_ok_def sconf_subject_ok_def conf_def)
      with ET v have "\<exists>v. e' = Val v \<and> (\<exists>E T. ?Es' t = \<lfloor>(E, T)\<rfloor> \<and> P,m' \<turnstile> v :\<le> T)" by blast }
    moreover
    { assume "\<exists>a. e' = Throw a"
      then obtain a where a: "e' = Throw a" by blast
      with sconf_subject' ET es't have "\<exists>T'. P,E,m' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T"
	apply -
	apply(drule ts_invD, assumption)
	by(clarsimp simp add: subject_ok_def sconf_subject_ok_def)
      then obtain T' where "P,E,m' \<turnstile> e' : T'" and "P \<turnstile> T' \<le> T" by blast
      with a have "a \<in> dom m'" by(auto)
      with a have "\<exists>a. e' = Throw a \<and> a \<in> dom m'" by blast }
    moreover
    { assume nfine': "\<not> final e'"
      with nored sconf_subject' wf have "t \<in> progress.deadlocked (mred P) final_expr (ls', (ts', m'), ws') \<and> (\<exists>E T. ?Es' t = \<lfloor>(E, T)\<rfloor> \<and> (\<exists>T'. P,E,m' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T))"
	apply -
	apply(rule conjI)
	 apply(erule contrapos_np)
	 apply(drule red_progressT[OF wf_prog_wwf_prog, where s="(ls', (ts', m'), ws')"])
  	         apply(rule sconf_subject_es_ok_wt_es_ok, simp)
		apply(simp, rule defass')
	       apply(simp, rule addr')
	      apply(simp, rule lock')
	     apply(simp, rule es't)
	    apply(rule nfine')
	   apply(assumption)
	  apply(simp)
	  apply(drule ts_invD)
	   apply(rule es't)
	  apply(clarsimp simp add: sconf_def sconf_subject_ok_def)
	 apply(drule ts_invD)
	  apply(rule es't)
	 apply(fastsimp)
	apply(drule ts_invD)
	 apply(rule es't)
	apply(fastsimp simp add: subject_ok_def sconf_subject_ok_def)
	done 
    }
    ultimately have "(\<exists>v. e' = Val v \<and> (\<exists>E T. ?Es' t = \<lfloor>(E, T)\<rfloor> \<and> P,m' \<turnstile> v :\<le> T))
                   \<or> (\<exists>a. e' = Throw a \<and> a \<in> dom m')
                   \<or> t \<in> progress.deadlocked (mred P) final_expr (ls', (ts', m'), ws') \<and> (\<exists>E T. ?Es' t = \<lfloor>(E, T)\<rfloor> \<and> (\<exists>T'. P,E,m' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T))"
      by(auto simp add: final_def) }
  moreover
  have "Es \<unlhd> ?Es'" using esinv RedT by -(erule multithreaded.RedT_upd_inv_ext)
  ultimately show ?thesis 
    by(simp)
qed



end
