(*  Title:      JinjaThreads/Compiler/Correctness1Threaded.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Unlocking a sync block never fails} *}

theory Correctness1Threaded imports 
  J0J1Bisim
begin

definition lock_oks1 :: "(addr,thread_id) locks \<Rightarrow> (addr,thread_id,(('a,'b) exp \<times> 'c) \<times> (('a,'b) exp \<times> 'c) list) thread_info \<Rightarrow> bool" where
  "lock_oks1 ls ts \<equiv> \<forall>t. (case (ts t) of None    \<Rightarrow> (\<forall>l. has_locks (ls\<^sub>f l) t = 0)
                            | \<lfloor>((ex, exs), ln)\<rfloor> \<Rightarrow> (\<forall>l. has_locks (ls\<^sub>f l) t + ln\<^sub>f l = expr_lockss (map fst (ex # exs)) l))"

primrec el_loc_ok :: "expr1 \<Rightarrow> locals1 \<Rightarrow> bool"
  and els_loc_ok :: "expr1 list \<Rightarrow> locals1 \<Rightarrow> bool"
where
  "el_loc_ok (new C) xs \<longleftrightarrow> True"
| "el_loc_ok (newA T\<lfloor>e\<rceil>) xs \<longleftrightarrow> el_loc_ok e xs"
| "el_loc_ok (Cast T e) xs \<longleftrightarrow> el_loc_ok e xs"
| "el_loc_ok (e instanceof T) xs \<longleftrightarrow> el_loc_ok e xs"
| "el_loc_ok (e\<guillemotleft>bop\<guillemotright>e') xs \<longleftrightarrow> el_loc_ok e xs \<and> el_loc_ok e' xs"
| "el_loc_ok (Var V) xs \<longleftrightarrow> True"
| "el_loc_ok (Val v) xs \<longleftrightarrow> True"
| "el_loc_ok (V := e) xs \<longleftrightarrow> el_loc_ok e xs"
| "el_loc_ok (a\<lfloor>i\<rceil>) xs \<longleftrightarrow> el_loc_ok a xs \<and> el_loc_ok i xs"
| "el_loc_ok (a\<lfloor>i\<rceil> := e) xs \<longleftrightarrow> el_loc_ok a xs \<and> el_loc_ok i xs \<and> el_loc_ok e xs"
| "el_loc_ok (a\<bullet>length) xs \<longleftrightarrow> el_loc_ok a xs"
| "el_loc_ok (e\<bullet>F{D}) xs \<longleftrightarrow> el_loc_ok e xs"
| "el_loc_ok (e\<bullet>F{D} := e') xs \<longleftrightarrow> el_loc_ok e xs \<and> el_loc_ok e' xs"
| "el_loc_ok (e\<bullet>M(ps)) xs \<longleftrightarrow> el_loc_ok e xs \<and> els_loc_ok ps xs"
| "el_loc_ok {V:T=vo; e} xs \<longleftrightarrow> (case vo of None \<Rightarrow> el_loc_ok e xs | \<lfloor>v\<rfloor> \<Rightarrow> el_loc_ok e (xs[V := v]))"
| "el_loc_ok (sync\<^bsub>V\<^esub>(e) e') xs \<longleftrightarrow> el_loc_ok e xs \<and> el_loc_ok e' xs \<and> unmod e' V"
| "el_loc_ok (insync\<^bsub>V\<^esub>(a) e) xs \<longleftrightarrow> xs ! V = Addr a \<and> el_loc_ok e xs \<and> unmod e V"
| "el_loc_ok (e;;e') xs \<longleftrightarrow> el_loc_ok e xs \<and> el_loc_ok e' xs"
| "el_loc_ok (if (b) e else e') xs \<longleftrightarrow> el_loc_ok b xs \<and> el_loc_ok e xs \<and> el_loc_ok e' xs"
| "el_loc_ok (while (b) c) xs \<longleftrightarrow> el_loc_ok b xs \<and> el_loc_ok c xs"
| "el_loc_ok (throw e) xs \<longleftrightarrow> el_loc_ok e xs"
| "el_loc_ok (try e catch(C V) e') xs \<longleftrightarrow> el_loc_ok e xs \<and> el_loc_ok e' xs"

| "els_loc_ok [] xs \<longleftrightarrow> True"
| "els_loc_ok (e # es) xs \<longleftrightarrow> el_loc_ok e xs \<and> els_loc_ok es xs"

lemma el_loc_okI: "\<lbrakk> \<not> contains_insync e; syncvars e; \<B> e n \<rbrakk> \<Longrightarrow> el_loc_ok e xs"
  and els_loc_okI: "\<lbrakk> \<not> contains_insyncs es; syncvarss es; \<B>s es n \<rbrakk> \<Longrightarrow> els_loc_ok es xs"
by(induct e and es arbitrary: xs n and xs n)(auto intro: fv_B_unmod)

lemma el_loc_ok_compE1: "\<lbrakk> \<not> contains_insync e; fv e \<subseteq> set Vs \<rbrakk> \<Longrightarrow> el_loc_ok (compE1 Vs e) xs"
  and els_loc_ok_compEs1: "\<lbrakk> \<not> contains_insyncs es; fvs es \<subseteq> set Vs \<rbrakk> \<Longrightarrow> els_loc_ok (compEs1 Vs es) xs"
by(auto intro: el_loc_okI els_loc_okI syncvars_compE1 syncvarss_compEs1 \<B> \<B>s simp del: compEs1_conv_map)

lemma shows el_loc_ok_not_contains_insync_local_change:
  "\<lbrakk> \<not> contains_insync e; el_loc_ok e xs \<rbrakk> \<Longrightarrow> el_loc_ok e xs'"
  and els_loc_ok_not_contains_insyncs_local_change:
  "\<lbrakk> \<not> contains_insyncs es; els_loc_ok es xs \<rbrakk> \<Longrightarrow> els_loc_ok es xs'"
by(induct e and es arbitrary: xs xs' and xs xs')(fastsimp)+

lemma el_loc_ok_update: "\<lbrakk> \<B> e n; V < n \<rbrakk> \<Longrightarrow> el_loc_ok e (xs[V := v]) = el_loc_ok e xs"
  and els_loc_ok_update: "\<lbrakk> \<B>s es n; V < n \<rbrakk> \<Longrightarrow> els_loc_ok es (xs[V := v]) = els_loc_ok es xs"
apply(induct e and es arbitrary: n xs and n xs) 
apply(auto simp add: list_update_swap)
done

lemma els_loc_ok_map_Val [simp]:
  "els_loc_ok (map Val vs) xs"
by(induct vs) auto

lemma els_loc_ok_map_Val_append [simp]:
  "els_loc_ok (map Val vs @ es) xs = els_loc_ok es xs"
by(induct vs) auto

lemma el_loc_ok_extRet2J [simp]:
  "el_loc_ok e xs \<Longrightarrow> el_loc_ok (extRet2J e va) xs"
by(cases va) auto

definition el_loc_ok1 :: "((nat, nat) exp \<times> val list) \<times> ((nat, nat) exp \<times> val list) list \<Rightarrow> bool"
  where "el_loc_ok1 = (\<lambda>((e, xs), exs). el_loc_ok e xs \<and> sync_ok e \<and> (\<forall>(e,xs)\<in>set exs. el_loc_ok e xs \<and> sync_ok e))"

lemma el_loc_ok1_simps:
  "el_loc_ok1 ((e, xs), exs) = (el_loc_ok e xs \<and> sync_ok e \<and> (\<forall>(e,xs)\<in>set exs. el_loc_ok e xs \<and> sync_ok e))"
by(simp add: el_loc_ok1_def)

lemma el_loc_ok_blocks1 [simp]:
   "el_loc_ok (blocks1 n Ts body) xs = el_loc_ok body xs"
by(induct n Ts body rule: blocks1.induct) auto

lemma sync_oks_blocks1 [simp]: "sync_ok (blocks1 n Ts e) = sync_ok e"
by(induct n Ts e rule: blocks1.induct) auto

lemma assumes fin: "final e'"
  shows el_loc_ok_inline_call: "el_loc_ok e xs \<Longrightarrow> el_loc_ok (inline_call e' e) xs"
  and els_loc_ok_inline_calls: "els_loc_ok es xs \<Longrightarrow> els_loc_ok (inline_calls e' es) xs"
apply(induct e and es arbitrary: xs and xs)
apply(insert fin)
apply(auto simp add: unmod_inline_call)
done

lemma assumes "sync_ok e'"
  shows sync_ok_inline_call: "sync_ok e \<Longrightarrow> sync_ok (inline_call e' e)"
  and sync_oks_inline_calls: "sync_oks es \<Longrightarrow> sync_oks (inline_calls e' es)"
apply(induct e and es)
apply(insert `sync_ok e'`)
apply auto
done

lemma bisim_sync_ok:
  "bisim Vs e e' xs \<Longrightarrow> sync_ok e"
  "bisim Vs e e' xs \<Longrightarrow> sync_ok e'"

  and bisims_sync_oks:
  "bisims Vs es es' xs \<Longrightarrow> sync_oks es"
  "bisims Vs es es' xs \<Longrightarrow> sync_oks es'"
apply(induct rule: bisim_bisims.inducts)
apply(auto intro: not_contains_insync_sync_ok not_contains_insyncs_sync_oks simp del: compEs1_conv_map)
done  

lemma assumes "final e'"
  shows expr_locks_inline_call_final:
  "expr_locks (inline_call e' e) = expr_locks e"
  and expr_lockss_inline_calls_final:
  "expr_lockss (inline_calls e' es) = expr_lockss es"
apply(induct e and es)
apply(insert `final e'`)
apply(auto simp add: is_vals_conv intro: ext)
done

lemma lock_oks1I:
  "\<lbrakk> \<And>t l. ts t = None \<Longrightarrow> has_locks (ls\<^sub>f l) t = 0;
     \<And>t e x exs ln l. ts t = \<lfloor>(((e, x), exs), ln)\<rfloor> \<Longrightarrow> has_locks (ls\<^sub>f l) t + ln\<^sub>f l= expr_locks e l + expr_lockss (map fst exs) l \<rbrakk>
  \<Longrightarrow> lock_oks1 ls ts"
apply(fastsimp simp add: lock_oks1_def)
done

lemma lock_oks1E:
  "\<lbrakk> lock_oks1 ls ts;
     \<forall>t. ts t = None \<longrightarrow> (\<forall>l. has_locks (ls\<^sub>f l) t = 0) \<Longrightarrow> Q;
     \<forall>t e x exs ln. ts t = \<lfloor>(((e, x), exs), ln)\<rfloor> \<longrightarrow> (\<forall>l. has_locks (ls\<^sub>f l) t + ln\<^sub>f l = expr_locks e l + expr_lockss (map fst exs) l) \<Longrightarrow> Q \<rbrakk>
  \<Longrightarrow> Q"
by(fastsimp simp add: lock_oks1_def)

lemma lock_oks1D1:
  "\<lbrakk> lock_oks1 ls ts; ts t = None \<rbrakk> \<Longrightarrow> \<forall>l. has_locks (ls\<^sub>f l) t = 0"
apply(simp add: lock_oks1_def)
apply(erule_tac x="t" in allE)
apply(auto)
done

lemma lock_oks1D2:
  "\<lbrakk> lock_oks1 ls ts; ts t = \<lfloor>(((e, x), exs), ln)\<rfloor> \<rbrakk> 
  \<Longrightarrow> \<forall>l. has_locks (ls\<^sub>f l) t + ln\<^sub>f l = expr_locks e l + expr_lockss (map fst exs) l"
apply(fastsimp simp add: lock_oks1_def)
done

lemma lock_oks1_thr_updI:
  "\<lbrakk> lock_oks1 ls ts; ts t = \<lfloor>(((e, xs), exs), ln)\<rfloor>;
     \<forall>l. expr_locks e l + expr_lockss (map fst exs) l = expr_locks e' l + expr_lockss (map fst exs') l \<rbrakk>
  \<Longrightarrow> lock_oks1 ls (ts(t \<mapsto> (((e', xs'), exs'), ln)))"
by(rule lock_oks1I)(auto split: split_if_asm dest: lock_oks1D2 lock_oks1D1)


definition mbisim_Red1'_Red1 :: "((addr,addr,(expr1 \<times> locals1) \<times> (expr1 \<times> locals1) list,'heap,addr) state, 
                               (addr,addr,(expr1 \<times> locals1) \<times> (expr1 \<times> locals1) list,'heap,addr) state) bisim"
where "mbisim_Red1'_Red1 s1 s2 = (s1 = s2 \<and> lock_oks1 (locks s1) (thr s1) \<and> ts_ok (\<lambda>t exexs h. el_loc_ok1 exexs) (thr s1) (shr s1))"

lemma sync_ok_blocks:
  "\<lbrakk> length vs = length pns; length Ts = length pns\<rbrakk>
  \<Longrightarrow> sync_ok (blocks pns Ts vs body) = sync_ok body"
by(induct pns Ts vs body rule: blocks.induct) auto

context J1_heap_base begin

lemma red_IUF_expr_locks: 
  "\<lbrakk> P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; el_loc_ok e (lcl s); IUF e ta e'; \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l = [UnlockFail] \<rbrakk> \<Longrightarrow> expr_locks e l > 0"
  and reds_IUFs_expr_lockss:
  "\<lbrakk> P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; els_loc_ok es (lcl s); IUFs es ta es'; \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l = [UnlockFail] \<rbrakk> \<Longrightarrow> expr_lockss es l > 0"
apply(induct arbitrary: n and n rule: red1_reds1.inducts)
apply(fastsimp simp add: finfun_upd_apply split: split_if_asm)+
done

lemma shows red1_preserves_el_loc_ok:
  "\<lbrakk> P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e; el_loc_ok e (lcl s) \<rbrakk> \<Longrightarrow> el_loc_ok e' (lcl s')"

  and reds1_preserves_els_loc_ok:
  "\<lbrakk> P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; sync_oks es; els_loc_ok es (lcl s) \<rbrakk> \<Longrightarrow> els_loc_ok es' (lcl s')"
proof(induct rule: red1_reds1.inducts)
  case (Synchronized1Red2 e s ta e' s' V a)
  from `el_loc_ok (insync\<^bsub>V\<^esub> (a) e) (lcl s)`
  have "el_loc_ok e (lcl s)" "unmod e V" "lcl s ! V = Addr a" by auto
  from `sync_ok (insync\<^bsub>V\<^esub> (a) e)` have "sync_ok e" by simp
  hence "el_loc_ok e' (lcl s')"
    using `el_loc_ok e (lcl s)`
    by(rule Synchronized1Red2)
  moreover from `P,t \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>` `unmod e V` have "unmod e' V"
    by(rule red1_unmod_preserved)
  moreover from red1_preserves_unmod[OF `P,t \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>` `unmod e V`] `lcl s ! V = Addr a`
  have "lcl s' ! V = Addr a" by simp
  ultimately show ?case by auto
qed(auto elim: el_loc_ok_not_contains_insync_local_change els_loc_ok_not_contains_insyncs_local_change)

lemma red1_preserves_sync_ok: "\<lbrakk> P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e \<rbrakk> \<Longrightarrow> sync_ok e'"
  and reds1_preserves_sync_oks: "\<lbrakk> P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; sync_oks es \<rbrakk> \<Longrightarrow> sync_oks es'"
by(induct rule: red1_reds1.inducts)(auto elim: not_contains_insync_sync_ok)

lemma Red1_preserves_el_loc_ok1:
  assumes wf: "wf_J1_prog P"
  shows "\<lbrakk> P,t \<turnstile>1 \<langle>ex/exs,m\<rangle> -ta\<rightarrow> \<langle>ex'/exs',m'\<rangle>; el_loc_ok1 (ex, exs) \<rbrakk>  \<Longrightarrow> el_loc_ok1 (ex', exs')"
apply(erule Red1.cases)
  apply(auto simp add: el_loc_ok1_def dest: red1_preserves_el_loc_ok red1_preserves_sync_ok intro: el_loc_ok_inline_call sync_ok_inline_call)
 apply(fastsimp dest!: sees_wf_mdecl[OF wf] simp add: wf_mdecl_def intro!: el_loc_okI dest: WT1_not_contains_insync intro: not_contains_insync_sync_ok)+
done 

lemma assumes wf: "wf_J1_prog P"
  shows red1_el_loc_ok1_new_thread:
  "\<lbrakk> P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t' (C, M, a) h \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> el_loc_ok1 (({0:Class (fst (method P C M))=None; snd (snd (snd (method P C M)))}, xs), [])"

  and reds1_el_loc_ok1_new_thread:
  "\<lbrakk> P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t' (C, M, a) h \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> el_loc_ok1 (({0:Class (fst (method P C M))=None; snd (snd (snd (method P C M)))}, xs), [])"
proof(induct rule: red1_reds1.inducts)
  case Red1CallExternal thus ?case
    apply(auto dest!: red_external_new_thread_sees[OF wf] simp add: el_loc_ok1_simps)
    apply(auto dest!: sees_wf_mdecl[OF wf] WT1_not_contains_insync simp add: wf_mdecl_def intro!: el_loc_okI not_contains_insync_sync_ok)
    done
qed auto

lemma Red1_el_loc_ok1_new_thread:
  assumes wf: "wf_J1_prog P"
  shows "\<lbrakk> P,t \<turnstile>1 \<langle>ex/exs,m\<rangle> -ta\<rightarrow> \<langle>ex'/exs',m'\<rangle>; NewThread t' exexs m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
         \<Longrightarrow> el_loc_ok1 exexs"
by(erule Red1.cases)(fastsimp elim: red1_el_loc_ok1_new_thread[OF wf] simp add: ta_upd_simps)+

lemma Red1'_el_loc_ok: 
  assumes wf: "wf_J1_prog P"
  shows "lifting_wf (mred1' P) (\<lambda>t exexs h. el_loc_ok1 exexs)"
by(unfold_locales)(auto elim: Red1_preserves_el_loc_ok1[OF wf] Red1_el_loc_ok1_new_thread[OF wf])

lemma Red1_el_loc_ok: 
  assumes wf: "wf_J1_prog P"
  shows "lifting_wf (mred1 P) (\<lambda>t exexs h. el_loc_ok1 exexs)"
by(unfold_locales)(auto elim: Red1_preserves_el_loc_ok1[OF wf] Red1_el_loc_ok1_new_thread[OF wf])

lemma redTW1_eq_1': "Red1_mthr.redTW P t wa s obs s' \<longleftrightarrow> Red1'_mthr.redTW P t wa s obs s'"
using ta_upd_simps[simp]
proof(intro iffI)
  assume "multithreaded_base.redTW (mred1 P) t wa s obs s'"
  thus "multithreaded_base.redTW (mred1' P) t wa s obs s'"
  proof cases
    case redTW_NotifySome thus ?thesis
      by(auto intro!: Red1'_mthr.redTW.redTW_NotifySome)(fastsimp simp add: IUFL_def dest: IUF_taD)
  next
    case (redTW_NotifyAll w x') thus ?thesis
      by(auto intro!: Red1'_mthr.redTW.redTW_NotifyAll[where x'=x'])(fastsimp simp add: IUFL_def dest: IUF_taD)+
  next
    case redTW_InterruptWait thus ?thesis
      by(safe intro!: Red1'_mthr.redTW.redTW_InterruptWait)(auto simp add: IUFL_def is_Interrupted_ta_def, fastsimp dest: IUF_taD)
  qed(auto intro: Red1'_mthr.redTW.intros)
next
  assume "multithreaded_base.redTW (mred1' P) t wa s obs s'"
  thus "multithreaded_base.redTW (mred1 P) t wa s obs s'"
  proof cases
    case redTW_NotifySome thus ?thesis by(auto intro!: Red1_mthr.redTW.redTW_NotifySome)
  next
    case (redTW_NotifyAll w x') thus ?thesis
      by(fastsimp intro!: Red1_mthr.redTW.redTW_NotifyAll[where x'=x'])
  qed(fastsimp intro: Red1_mthr.redTW.intros)+
qed

lemma redTWs1_eq_1': "Red1_mthr.redTWs P t was s obs s' \<longleftrightarrow> Red1'_mthr.redTWs P t was s obs s'"
proof
  assume "Red1_mthr.redTWs P t was s obs s'"
  thus "Red1'_mthr.redTWs P t was s obs s'"
    by(induct rule: Red1_mthr.redTWs_converse_induct)(auto simp add: redTW1_eq_1' intro: Red1'_mthr.redTWs_snocI)
next
  assume "Red1'_mthr.redTWs P t was s obs s'"
  thus "Red1_mthr.redTWs P t was s obs s'"
    by(induct rule: Red1'_mthr.redTWs_converse_induct)(auto simp add: redTW1_eq_1' intro: Red1_mthr.redTWs_snocI)
qed

lemma Red1_mthr_eq_Red1_mthr':
  assumes lok: "lock_oks1 (locks s) (thr s)"
  and elo: "ts_ok (\<lambda>t exexs h. el_loc_ok1 exexs) (thr s) (shr s)"
  shows "Red1_mthr.redT P s = Red1'_mthr.redT P s"
proof(intro ext)
  fix tta s'
  show "Red1_mthr.redT P s tta s' = Red1'_mthr.redT P s tta s'" (is "?lhs = ?rhs")
  proof
    assume "?lhs" thus ?rhs
    proof cases
      case (redT_normal t x ta x' m' obs)
      note [simp] = `tta = (t, observable_ta_of ta obs)`
      note thrS = `thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>`
      note aoe = `Red1_mthr.actions_ok s t ta` 
      obtain ex exs where x [simp]: "x = (ex, exs)" by(cases x)
      obtain ex' exs' where x' [simp]: "x' = (ex', exs')" by(cases x')
      from `mred1 P t (x, shr s) ta (x', m')`
      have red: "P,t \<turnstile>1 \<langle>ex/exs,shr s\<rangle> -ta\<rightarrow> \<langle>ex'/exs',m'\<rangle>" by simp
      moreover have "\<not> IUFL ex exs ta ex' exs'"
      proof
	assume "IUFL ex exs ta ex' exs'"
	hence "exs = exs'" and IUF: "IUF (fst ex) ta (fst ex')" by(auto simp add: IUFL_def)
	with red obtain ta'
	  where "P,t \<turnstile>1 \<langle>fst ex, (shr s, snd ex)\<rangle> -ta'\<rightarrow> \<langle>fst ex', (m', snd ex')\<rangle>" 
	  and ta': "ta = extTA2J1 P ta'" by(fastsimp elim!: Red1.cases)
	moreover from elo thrS have "el_loc_ok1 (ex, exs)" by(auto dest: ts_okD)
	hence "el_loc_ok (fst ex) (snd ex)" by(simp add: el_loc_ok1_def split_beta)
	moreover from IUF have "IUF (fst ex) ta' (fst ex')" using ta'
	  by(cases ex)(cases ex', clarsimp)
	moreover from IUF obtain l where ta: "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>" by(auto dest: IUF_taD)
	with ta' have "ta' = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>" by(cases ta')(auto simp add: ta_upd_simps)
	ultimately have "expr_locks (fst ex) l > 0"
	  by(cases ex, cases ex')(erule red_IUF_expr_locks, auto)
	moreover from aoe have "lock_actions_ok ((locks s)\<^sub>f l) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l)"
	  by(auto simp add: lock_ok_las_def)
	with ta have "has_locks ((locks s)\<^sub>f l) t = 0" by simp
	with lok thrS have "expr_lockss (map fst (ex # exs)) l = 0"
	  apply(cases ex)
	  apply(auto simp add: lock_oks1_def)
	  apply fastsimp+
	  done
	hence "expr_locks (fst ex) l = 0" by simp
	ultimately show False by simp
      qed
      ultimately have "mred1' P t (x, shr s) ta (x', m')" by simp
      moreover note thrS `wset s t = None` aoe
      moreover from `Red1_mthr.redTWs P t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> (redT_upd s t ta x' m') obs s'`
      have "Red1'_mthr.redTWs P t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> (redT_upd s t ta x' m') obs s'" by(simp add: redTWs1_eq_1')
      ultimately have "Red1'_mthr.redT P s (t, observable_ta_of ta obs) s'"
	by(rule Red1'_mthr.redT.redT_normal)
      thus ?thesis unfolding `tta = (t, observable_ta_of ta obs)` .
    next
      case (redT_acquire t x ln n)
      from `thr s t = \<lfloor>(x, ln)\<rfloor>` `wset s t = None` `may_acquire_all (locks s) t ln`
	`0 < ln\<^sub>f n` `s' = (acquire_all (locks s) t ln, (thr s(t \<mapsto> (x, no_wait_locks)), shr s), wset s)`
      show ?thesis unfolding `tta = (t, \<lambda>\<^isup>f [], [], [], [], [ReacquireLocks ln])`
	by(rule Red1'_mthr.redT_acquire)
    qed
  next
    assume ?rhs thus ?lhs
    proof(cases)
      case (redT_normal t x ta x' m' obs)
      from `mred1' P t (x, shr s) ta (x', m')` have "mred1 P t (x, shr s) ta (x', m')"
	by(auto simp add: split_beta)
      moreover note `thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>` `wset s t = None` `Red1_mthr.actions_ok s t ta`
      moreover from `Red1'_mthr.redTWs P t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> (redT_upd s t ta x' m') obs s'`
      have "Red1_mthr.redTWs P t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> (redT_upd s t ta x' m') obs s'" by(simp add: redTWs1_eq_1')
      ultimately show ?thesis unfolding `tta = (t, observable_ta_of ta obs)`
	by(rule Red1_mthr.redT.redT_normal)
    next
      case (redT_acquire t x ln n)
      from `thr s t = \<lfloor>(x, ln)\<rfloor>` `wset s t = None` `may_acquire_all (locks s) t ln`
	`0 < ln\<^sub>f n` `s' = (acquire_all (locks s) t ln, (thr s(t \<mapsto> (x, no_wait_locks)), shr s), wset s)`
      show ?thesis unfolding `tta = (t, \<lambda>\<^isup>f [], [], [], [], [ReacquireLocks ln])`
	by(rule Red1_mthr.redT_acquire)
    qed
  qed
qed

lemma assumes wf: "wf_J1_prog P"
  shows expr_locks_new_thread1:
  "\<lbrakk> P,t \<turnstile>1 \<langle>e,s\<rangle> -TA\<rightarrow> \<langle>e',s'\<rangle>; NewThread t' (ex, exs) h \<in> set (map (convert_new_thread_action (extNTA2J1 P)) \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>) \<rbrakk>
  \<Longrightarrow> expr_lockss (map fst (ex # exs)) = (\<lambda>ad. 0)"
  and expr_lockss_new_thread1:
  "\<lbrakk> P,t \<turnstile>1 \<langle>es,s\<rangle> [-TA\<rightarrow>] \<langle>es',s'\<rangle>; NewThread t' (ex, exs) h \<in> set (map (convert_new_thread_action (extNTA2J1 P)) \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>) \<rbrakk>
  \<Longrightarrow> expr_lockss (map fst (ex # exs)) = (\<lambda>ad. 0)"
proof(induct rule: red1_reds1.inducts)
  case (Red1CallExternal s a T M vs ta va h' e' s')
  then obtain C fs ad where subThread: "P \<turnstile> C \<preceq>\<^sup>* Thread" and ext: "extNTA2J1 P (C, run, ad) = (ex, exs)"
    by(fastsimp dest: red_external_new_thread_sub_thread)
  from sub_Thread_sees_run[OF wf subThread] obtain D body
    where sees: "P \<turnstile> C sees run: []\<rightarrow>Void = body in D" by auto
  from sees_wf_mdecl[OF wf this] obtain T where "P,[Class D] \<turnstile>1 body :: T"
    by(auto simp add: wf_mdecl_def)
  hence "\<not> contains_insync body" by(rule WT1_not_contains_insync)
  hence "expr_locks body = (\<lambda>ad. 0)" by(auto simp add: contains_insync_conv expand_fun_eq)
  with sees ext show ?case by(auto)
qed auto

lemma assumes wf: "wf_J1_prog P"
  shows red1_update_expr_locks:
  "\<lbrakk> P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e; el_loc_ok e (lcl s); \<not> IUF e ta e' \<rbrakk>
  \<Longrightarrow> upd_expr_locks (int o expr_locks e) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int o expr_locks e'"

  and reds1_update_expr_lockss:
  "\<lbrakk> P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; sync_oks es; els_loc_ok es (lcl s); \<not> IUFs es ta es' \<rbrakk>
  \<Longrightarrow> upd_expr_locks (int o expr_lockss es) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int o expr_lockss es'"
proof -
  have "\<lbrakk> P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e; el_loc_ok e (lcl s); \<not> IUF e ta e' \<rbrakk> 
       \<Longrightarrow> upd_expr_locks (\<lambda>ad. 0) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = (\<lambda>ad. (int o expr_locks e') ad - (int o expr_locks e) ad)"
    and "\<lbrakk> P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; sync_oks es; els_loc_ok es (lcl s); \<not> IUFs es ta es' \<rbrakk>
       \<Longrightarrow> upd_expr_locks (\<lambda>ad. 0) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = (\<lambda>ad. (int o expr_lockss es') ad - (int o expr_lockss es) ad)"
  proof(induct rule: red1_reds1.inducts)
    case Red1CallExternal thus ?case
      by(auto simp add: expand_fun_eq contains_insync_conv contains_insyncs_conv finfun_upd_apply elim!: red_external.cases)
  qed(fastsimp simp add: expand_fun_eq contains_insync_conv contains_insyncs_conv finfun_upd_apply intro: ext)+
  hence "\<lbrakk> P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e; el_loc_ok e (lcl s); \<not> IUF e ta e' \<rbrakk>
        \<Longrightarrow> upd_expr_locks (\<lambda>ad. 0 + (int \<circ> expr_locks e) ad) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int \<circ> expr_locks e'"
    and "\<lbrakk> P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; sync_oks es; els_loc_ok es (lcl s); \<not> IUFs es ta es' \<rbrakk>
        \<Longrightarrow> upd_expr_locks (\<lambda>ad. 0 + (int \<circ> expr_lockss es) ad) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int \<circ> expr_lockss es'"
    by(fastsimp intro: ext simp only: upd_expr_locks_add)+
  thus "\<lbrakk> P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e; el_loc_ok e (lcl s); \<not> IUF e ta e'  \<rbrakk>
        \<Longrightarrow> upd_expr_locks (int o expr_locks e) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int o expr_locks e'"
    and "\<lbrakk> P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; sync_oks es; els_loc_ok es (lcl s); \<not> IUFs es ta es' \<rbrakk>
        \<Longrightarrow> upd_expr_locks (int o expr_lockss es) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int o expr_lockss es'"
    by(auto simp add: o_def)
qed

lemma Red1'_redTW_preserves_lock_oks1:
  assumes wf: "wf_J1_prog P"
  and "Red1'_mthr.redTW P t wa s obs s'"
  and "lock_oks1 (locks s) (thr s)"
  and "ts_ok (\<lambda>t exexs h. el_loc_ok1 exexs) (thr s) (shr s)"
  shows "lock_oks1 (locks s') (thr s')"
using assms
apply(auto elim!: Red1'_mthr.redTW.cases simp add: Option.map_def fun_upd_idem ta_upd_simps)
  apply(erule (1) lock_oks1_thr_updI)
  apply(erule Red1.cases)
    apply(drule (1) ts_okD)
    apply(clarsimp simp add: el_loc_ok1_def)
    apply(drule (2) red1_update_expr_locks, simp)
     apply(fastsimp dest: IUF_taD simp add: ta_upd_simps)
    apply(simp add: o_def expand_fun_eq)
   apply fastsimp
  apply fastsimp
 prefer 2
 apply(erule (1) lock_oks1_thr_updI)
 apply(drule (1) ts_okD)
 apply(clarsimp simp add: el_loc_ok1_def)
 apply(erule Red1.cases)
   apply(clarsimp simp add: ta_upd_simps is_Interrupted_ta_def)
   apply(drule (2) red1_update_expr_locks, simp)
    apply(fastsimp dest: IUF_taD simp add: ta_upd_simps)
   apply(simp add: o_def expand_fun_eq)
  apply(fastsimp simp add: is_Interrupted_ta_def)
 apply(fastsimp simp add: is_Interrupted_ta_def)
apply(rule lock_oks1I)
 apply(auto split: split_if_asm dest: lock_oks1D1 lock_oks1D2)
apply(erule allE, erule (1) impE)
apply clarsimp
apply(drule (1) lock_oks1D2)
apply(drule (1) ts_okD)
apply(clarsimp simp add: el_loc_ok1_def)
apply(erule Red1.cases)
  apply clarsimp
  apply(drule (2) red1_update_expr_locks, simp)
   apply(fastsimp dest: IUF_taD simp add: ta_upd_simps)
  apply(simp add: o_def expand_fun_eq)
 apply simp_all
done

lemma Red1'_redTWs_preserves_lock_oks1:
  assumes wf: "wf_J1_prog P"
  and rest: "Red1'_mthr.redTWs P t was s obs s'" "lock_oks1 (locks s) (thr s)"
            "ts_ok (\<lambda>t exexs h. el_loc_ok1 exexs) (thr s) (shr s)"
  shows "lock_oks1 (locks s') (thr s')"
using rest
by(induct rule: Red1'_mthr.redTWs_converse_induct)(auto dest: Red1'_redTW_preserves_lock_oks1[OF wf] lifting_wf.redTWs_preserves[OF Red1'_el_loc_ok[OF wf]])

lemma Red1'_preserves_lock_oks:
  assumes wf: "wf_J1_prog P"
  and Red: "Red1'_mthr.redT P s1 ta1 s1'"
  and loks: "lock_oks1 (locks s1) (thr s1)"
  and sync: "ts_ok (\<lambda>t exexs h. el_loc_ok1 exexs) (thr s1) (shr s1)"
  shows "lock_oks1 (locks s1') (thr s1')"
using Red
proof(cases rule: Red1'_mthr.redT.cases)
  case (redT_normal t x ta x' m' obs)
  note [simp] = `ta1 = (t, observable_ta_of ta obs)`
  obtain ex exs where x: "x = (ex, exs)" by (cases x)
  obtain ex' exs' where x': "x' = (ex', exs')" by (cases x')
  note thrst = `thr s1 t = \<lfloor>(x, no_wait_locks)\<rfloor>`
  note wst = `wset s1 t = None`
  note aoe = `Red1_mthr.actions_ok s1 t ta`
  from `mred1' P t (x, shr s1) ta (x', m')`
  have red: "P,t \<turnstile>1 \<langle>ex/exs,shr s1\<rangle> -ta\<rightarrow> \<langle>ex'/exs',m'\<rangle>"
    and IUF: "\<not> IUFL ex exs ta ex' exs'" unfolding x x' by simp_all
  note `Red1'_mthr.redTWs P t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> (redT_upd s1 t ta x' m') obs s1'`
  moreover from red
  have "lock_oks1 (locks (redT_upd s1 t ta x' m')) (thr (redT_upd s1 t ta x' m'))"
  proof cases
    case (red1Red e x TA e' x')
    note [simp] = `ex = (e, x)` `ta = extTA2J1 P TA` `ex' = (e', x')` `exs' = exs`
      and red = `P,t \<turnstile>1 \<langle>e,(shr s1, x)\<rangle> -TA\<rightarrow> \<langle>e',(m', x')\<rangle>`
    { fix t'
      assume None: "(redT_updTs (thr s1) (map (convert_new_thread_action (extNTA2J1 P)) \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>)(t \<mapsto> (((e', x'), exs), redT_updLns (locks s1) t (snd (the (thr s1 t))) \<lbrace>TA\<rbrace>\<^bsub>l\<^esub>))) t' = None"
      { fix l
	from aoe have "lock_actions_ok ((locks s1)\<^sub>f l) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l)" by(auto simp add: lock_ok_las_def)
	with None have "has_locks ((redT_updLs (locks s1) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>)\<^sub>f l) t' = has_locks ((locks s1)\<^sub>f l) t'"
	  by(auto split: split_if_asm)
	also from loks None have "has_locks ((locks s1)\<^sub>f l) t' = 0" unfolding lock_oks1_def
	  by(force split: split_if_asm dest!: redT_updTs_None)
	finally have "has_locks (upd_locks ((locks s1)\<^sub>f l) t (\<lbrace>TA\<rbrace>\<^bsub>l\<^esub>\<^sub>f l)) t' = 0" by simp }
      hence "\<forall>l. has_locks (upd_locks ((locks s1)\<^sub>f l) t (\<lbrace>TA\<rbrace>\<^bsub>l\<^esub>\<^sub>f l)) t' = 0" .. }
    moreover {
      fix t' eX eXS LN
      assume Some: "(redT_updTs (thr s1) (map (convert_new_thread_action (extNTA2J1 P)) \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>)(t \<mapsto> (((e', x'), exs), redT_updLns (locks s1) t (snd (the (thr s1 t))) \<lbrace>TA\<rbrace>\<^bsub>l\<^esub>))) t' = \<lfloor>((eX, eXS), LN)\<rfloor>"
      { fix l
	from aoe have lao: "lock_actions_ok ((locks s1)\<^sub>f l) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l)" by(auto simp add: lock_ok_las_def)
	have "has_locks ((redT_updLs (locks s1) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>)\<^sub>f l) t' + LN\<^sub>f l = expr_lockss (map fst (eX # eXS)) l"
	proof(cases "t = t'")
	  case True
	  from loks thrst x
	  have "has_locks ((locks s1)\<^sub>f l) t = expr_locks e l + expr_lockss (map fst exs) l"
	    by(force simp add: lock_oks1_def)
	  hence "lock_expr_locks_ok ((locks s1)\<^sub>f l) t 0 (int (expr_locks e l + expr_lockss (map fst exs) l))"
	    by(simp add: lock_expr_locks_ok_def)
	  with lao have "lock_expr_locks_ok (upd_locks ((locks s1)\<^sub>f l) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l)) t (upd_threadRs 0 ((locks s1)\<^sub>f l) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l))
 (upd_expr_lock_actions (int (expr_locks e l + expr_lockss (map fst exs) l)) (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l))"
	    by(rule upd_locks_upd_expr_lock_preserve_lock_expr_locks_ok)
	  moreover from sync thrst x have "sync_ok e" "el_loc_ok e x"
	    unfolding el_loc_ok1_def by(auto dest: ts_okD)
	  with red1_update_expr_locks[OF wf red] IUF
	  have "upd_expr_locks (int \<circ> expr_locks e) \<lbrace>TA\<rbrace>\<^bsub>l\<^esub> = int \<circ> expr_locks e'" by(simp add: IUFL_def)
	  hence "upd_expr_lock_actions (int (expr_locks e l)) (\<lbrace>TA\<rbrace>\<^bsub>l\<^esub>\<^sub>f l) = int (expr_locks e' l)"
	    by(simp add: upd_expr_locks_def expand_fun_eq)
	  ultimately show ?thesis using lao Some thrst x True
            by(auto simp add: lock_expr_locks_ok_def upd_expr_locks_def)
	next
	  case False
	  from aoe have tok: "thread_oks (thr s1) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" by auto
	  show ?thesis
	  proof(cases "thr s1 t' = None")
	    case True
	    with Some tok False obtain m 
	      where nt: "NewThread t' (eX, eXS) m \<in> set (map (convert_new_thread_action (extNTA2J1 P)) \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>)"
	      and [simp]: "LN = no_wait_locks" by(auto dest: redT_updTs_new_thread)
	    note expr_locks_new_thread1[OF wf red nt]
	    moreover from loks True have "has_locks ((locks s1)\<^sub>f l) t' = 0"
	      by(force simp add: lock_oks1_def)
	    ultimately show ?thesis using lao False by simp
	  next
	    case False
	    with Some `t \<noteq> t'` tok 
	    have "thr s1 t' = \<lfloor>((eX, eXS), LN)\<rfloor>" by(fastsimp dest: redT_updTs_Some[OF _ tok])
	    with loks tok lao `t \<noteq> t'` show ?thesis by(cases eX)(auto simp add: lock_oks1_def)
	  qed
	qed }
      hence "\<forall>l. has_locks ((redT_updLs (locks s1) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>)\<^sub>f l) t' + LN\<^sub>f l = expr_lockss (map fst (eX # eXS)) l" .. }
    ultimately show ?thesis unfolding lock_oks1_def x' by(clarsimp simp del: fun_upd_apply)
  next
    case (red1Call e a M vs C Ts T body D x)
    from wf `P \<turnstile> C sees M: Ts\<rightarrow>T = body in D`
    obtain T' where "P,Class D # Ts \<turnstile>1 body :: T'"
      by(auto simp add: wf_mdecl_def dest!: sees_wf_mdecl)
    hence "expr_locks (blocks1 0 (Class D#Ts) body) = (\<lambda>l. 0)"
      by(auto simp add: expr_locks_blocks1 contains_insync_conv expand_fun_eq dest!: WT1_not_contains_insync)
    thus ?thesis using red1Call thrst loks
      unfolding lock_oks1_def x' x
      by auto force+
  next
    case (red1Return e' x' e x)
    thus ?thesis using thrst loks
      unfolding lock_oks1_def x' x
      apply auto
       apply(erule_tac x=ta in allE)
       apply(erule conjE)
       apply(erule disjE)
        apply clarsimp
       apply clarsimp
      apply(erule_tac x=t in allE)
      apply(erule conjE)
      apply(erule disjE)
       apply(force simp add: expr_locks_inline_call_final add_ac)
      apply(fastsimp simp add: expr_locks_inline_call_final)
      done
  qed
  moreover from sync `mred1' P t (x, shr s1) ta (x', m')` thrst aoe
  have "ts_ok (\<lambda>t exexs h. el_loc_ok1 exexs) (thr (redT_upd s1 t ta x' m')) (shr (redT_upd s1 t ta x' m'))"
    by(auto intro: lifting_wf.redT_updTs_preserves[OF Red1'_el_loc_ok[OF wf]])
  ultimately show ?thesis
    by(rule Red1'_redTWs_preserves_lock_oks1[OF wf])
next
  case (redT_acquire t x ln n)
  thus ?thesis using loks unfolding lock_oks1_def
    apply auto
     apply force
    apply(case_tac "ln\<^sub>f l::nat")
     apply simp
     apply(erule allE)
     apply(erule conjE)
     apply(erule allE)+
     apply(erule (1) impE)
     apply(erule_tac x=l in allE)
     apply fastsimp
    apply(erule may_acquire_allE)
    apply(erule allE)
    apply(erule_tac x=l in allE)
    apply(erule impE)
     apply simp
    apply(simp only: has_locks_acquire_locks_conv)
    apply(erule conjE)
    apply(erule allE)+
    apply(erule (1) impE)
    apply(erule_tac x=l in allE)
    apply simp
    done
qed

lemma Red1'_Red1_bisimulation:
  assumes wf: "wf_J1_prog P"
  shows "bisimulation (Red1'_mthr.redT P) (Red1_mthr.redT P) mbisim_Red1'_Red1 op ="
proof
  fix s1 s2 tl1 s1'
  assume "mbisim_Red1'_Red1 s1 s2" and "Red1'_mthr.redT P s1 tl1 s1'"
  thus "\<exists>s2' tl2. Red1_mthr.redT P s2 tl2 s2' \<and> mbisim_Red1'_Red1 s1' s2' \<and> tl1 = tl2"
    by(cases tl1)(auto simp add: mbisim_Red1'_Red1_def Red1_mthr_eq_Red1_mthr' simp del: split_paired_Ex elim: Red1'_preserves_lock_oks[OF wf] lifting_wf.redT_preserves[OF Red1'_el_loc_ok, OF wf])
next
  fix s1 s2 tl2 s2'
  assume "mbisim_Red1'_Red1 s1 s2" "Red1_mthr.redT P s2 tl2 s2'"
  thus "\<exists>s1' tl1. Red1'_mthr.redT P s1 tl1 s1' \<and> mbisim_Red1'_Red1 s1' s2' \<and> tl1 = tl2"
    by(cases tl2)(auto simp add: mbisim_Red1'_Red1_def Red1_mthr_eq_Red1_mthr' simp del: split_paired_Ex elim: Red1'_preserves_lock_oks[OF wf] lifting_wf.redT_preserves[OF Red1'_el_loc_ok, OF wf])
qed

lemma bisim_J1_J1_start:
  assumes wf: "wf_J1_prog P"
  and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T=body in C"
  and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts"
  shows "mbisim_Red1'_Red1 (J1_start_state P C M vs) (J1_start_state P C M vs)"
proof -
  let ?e = "blocks1 0 (Class C#Ts) body"
  let ?xs = "Null # vs @ replicate (max_vars body) undefined"

  from sees_wf_mdecl[OF wf sees] obtain T'
    where B: "\<B> body (Suc (length Ts))"
    and wt: "P,Class C # Ts \<turnstile>1 body :: T'"
    and da: "\<D> body \<lfloor>{..length Ts}\<rfloor>"
    and sv: "syncvars body"
    by(auto simp add: wf_mdecl_def)

  from wt have "expr_locks ?e = (\<lambda>_. 0)" by(auto intro: WT1_expr_locks)
  thus ?thesis using da sees sv B
    unfolding start_state_def
    by(fastsimp simp add: mbisim_Red1'_Red1_def lock_oks1_def el_loc_ok1_def contains_insync_conv intro!: ts_okI expr_locks_sync_ok split: split_if_asm intro: el_loc_okI)
qed

lemma Red1'_Red1_bisim_into_weak:
  assumes wf: "wf_J1_prog P"
  shows "bisimulation_into_delay (Red1'_mthr.redT P) (Red1_mthr.redT P) mbisim_Red1'_Red1 (op =) (Red1'_mthr.m\<tau>move P) (Red1_mthr.m\<tau>move P)"
proof -
  interpret b: bisimulation "Red1'_mthr.redT P" "Red1_mthr.redT P" "mbisim_Red1'_Red1" "op ="
    by(rule Red1'_Red1_bisimulation[OF wf])
  show ?thesis by(unfold_locales)(simp add: mbisim_Red1'_Red1_def)
qed

end

end