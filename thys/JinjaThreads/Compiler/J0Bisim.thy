(*  Title:      JinjaThreads/Compiler/J0Bisim.thy
    Author:     Andreas Lochbihler
*)

header {* Bisimulation proof for between Jinja small step semantics with and without callstacks for single threads *}

theory J0Bisim imports J0 "../Framework/FWBisimulation" "../J/JWellForm" "../J/Threaded" "../Common/ExternalCallWF" begin

fun fold_exs :: "J_prog \<Rightarrow> heap \<Rightarrow> expr \<times> locals \<Rightarrow> (expr \<times> locals) list \<Rightarrow> expr \<times> locals" where
  "fold_exs P h ex [] = ex"
| "fold_exs P h ex (ex' # exs) =
  (let (a, M, vs) = the (call (fst ex'));
       C = case the (h a) of (Obj C fs) \<Rightarrow> C | _ \<Rightarrow> arbitrary;
       D = fst (method P C M)
   in fold_exs P h (inline_call {this:Class D=snd ex this; fst ex}\<^bsub>True\<^esub> (fst ex'), snd ex') exs)"

lemma fold_exs_append [simp]:
  "fold_exs P h ex (exs @ exs') = fold_exs P h (fold_exs P h ex exs) exs'"
by(induct exs arbitrary: ex, auto simp add: split_beta)

fun fv_ok :: "(expr \<times> locals) list \<Rightarrow> bool" where
  "fv_ok [] = True"
| "fv_ok (ex # exs) = (fv (fst ex) \<subseteq> dom (snd ex) \<and> fv_ok exs)"

lemma red0_preserves_fv_ok:
  assumes wwf: "wwf_J_prog P"
  shows "\<lbrakk>P \<turnstile>0 \<langle>ex / exs, h\<rangle> -ta\<rightarrow> \<langle>ex' / exs', h'\<rangle>; fv_ok (ex # exs) \<rbrakk> \<Longrightarrow> fv_ok (ex' # exs')"
proof(induct rule: red0.cases)
  case (red0Red e ha x taa e' h'a x' exsa)
  thus ?case by(auto del: subsetI dest: red_fv_ok[OF wwf])
next
  case (red0Call e a M vs ha C fs Ts T pns body D x exsa)
  thus ?case by(auto dest!: sees_wf_mdecl[OF wwf] simp add: wf_mdecl_def)
next
  case (red0Return e aMvs e' x' x exsa ha)
  from fv_inline_call[OF `call e = \<lfloor>aMvs\<rfloor>`, of e'] `final e'`
  have "fv (inline_call e' e) \<subseteq> fv e" by(auto del: subsetI elim!: final.cases)
  with red0Return show ?case by auto
qed

fun this_ok :: "locals list \<Rightarrow> bool" where
  "this_ok [] = True"
| "this_ok (x#xs) = (((xs = [] \<and> x = empty) \<or> (\<exists>v. x = [this \<mapsto> v])) \<and> this_ok xs)"

fun is_call_list :: "heap \<Rightarrow> ('a,'b) exp list \<Rightarrow> bool"
where
  "is_call_list h [] = True"
| "is_call_list h (e # es) = ((\<exists>a M vs. call e = \<lfloor>(a, M, vs)\<rfloor> \<and> h a \<noteq> None) \<and> is_call_list h es)"

lemma is_call_list_append [simp]:
  "is_call_list h (es @ es') \<longleftrightarrow> is_call_list h es \<and> is_call_list h es'"
by(induct es, auto)

inductive  wf_state :: "heap \<Rightarrow> expr \<times> locals \<Rightarrow> (expr \<times> locals) list \<Rightarrow> bool"
  for h :: heap and ex :: "expr \<times> locals" and exs :: "(expr \<times> locals) list"
  where "\<lbrakk> fv_ok (ex # exs); this_ok (map snd (ex # exs)); is_call_list h (map fst exs) \<rbrakk> \<Longrightarrow> wf_state h ex exs"


declare wf_state.intros [intro!]
declare wf_state.cases [elim!]

lemma wf_state_iff:
  "wf_state h ex exs \<longleftrightarrow> fv_ok (ex # exs) \<and> this_ok (map snd (ex # exs)) \<and> is_call_list h (map fst exs)"
by(blast)

lemma is_call_list_hext_mono: "\<lbrakk> is_call_list h es; hext h h' \<rbrakk> \<Longrightarrow> is_call_list h' es"
by(induct es)(auto dest: hext_objarrD)

lemma red0_preserves_wf_state:
  assumes "wwf_J_prog P"
  and red: "P \<turnstile>0 \<langle>ex / exs, h\<rangle> -ta\<rightarrow> \<langle>ex' / exs', h'\<rangle>"
  shows "wf_state h ex exs \<Longrightarrow> wf_state h' ex' exs'"
proof(erule wf_state.cases)
  assume fv: "fv_ok (ex # exs)"
    and to: "this_ok (map snd (ex # exs))"
    and icl: "is_call_list h (map fst exs)"
  show ?thesis
  proof(rule wf_state.intros)
    from red fv show "fv_ok (ex' # exs')"
      by(rule red0_preserves_fv_ok[OF `wwf_J_prog P`])
  next
    from red show "this_ok (map snd (ex' # exs'))"
    proof(induct rule: red0.cases)
      case (red0Red e h X ta e' h' X' exs)
      hence red': "extTA2J0 P,P \<turnstile> \<langle>fst ex, (h, snd ex)\<rangle> -ta\<rightarrow> \<langle>fst ex', (h', snd ex')\<rangle>" by(auto)
      hence "dom (snd ex') \<subseteq> dom (snd ex) \<union> fv (fst ex)"
	by(auto dest: red_dom_lcl del: subsetI)
      moreover from red' have "dom (snd ex) \<subseteq> dom (snd ex')"
	by(auto dest: red_lcl_incr del: subsetI)
      ultimately show ?case using fv to red0Red
	by(auto dest!: subset_singletonD simp add: dom_eq_empty_conv dom_eq_singleton_conv)
    next
      case (red0Call e a M vs ha C fs Ts T pns body D x exsa)
      thus ?case using to fv by(auto)
    next
      case (red0Return e v x' x exsa ha)
      thus ?case using fv to by(auto)
    qed
  next
    from red show "is_call_list h' (map fst exs')"
    proof(induct rule: red0.cases)
      case (red0Red e h X ta e' h' X' exs)
      hence "hext h h'" by(auto dest: red_hext_incr)
      with icl red0Red show ?case by(auto intro: is_call_list_hext_mono)
    next
      case red0Call with icl show ?case by simp
    next
      case red0Return with icl show ?case by simp
    qed
  qed
qed

inductive bisim_red_red0 :: "J_prog \<Rightarrow> (expr \<times> locals) \<times> heap \<Rightarrow> ((expr \<times> locals) \<times> (expr \<times> locals) list) \<times> heap \<Rightarrow> bool"
  for P :: J_prog
  where
  "\<lbrakk> fold_exs P h ex exs = (e, x); wf_state h ex exs; noRetBlocks (fst ex # map fst exs) \<rbrakk>
  \<Longrightarrow> bisim_red_red0 P ((e, x), h) ((ex, exs), h)"

declare bisim_red_red0.intros[intro]

definition new_thread_bisim0 :: "J_prog \<Rightarrow> (expr \<times> locals) \<times> heap \<Rightarrow> ((expr\<times>locals) \<times> (expr\<times>locals) list) \<times> heap \<Rightarrow> bool"
where
  "new_thread_bisim0 P \<equiv> (\<lambda>((e, xs), h) (((e', xs'), exs'), h'). h = h' \<and> (\<exists>D a body C M T. e = {this:Class D=\<lfloor>Addr a\<rfloor>; body}\<^bsub>True\<^esub> \<and> xs = empty \<and> typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>Class C\<rfloor> \<and> P \<turnstile> C sees M:[]\<rightarrow>T=([], body) in D \<and> e' = body \<and> xs' = [this \<mapsto> Addr a] \<and> exs' = [(addr a\<bullet>M([]), empty)]))"

abbreviation ta_bisim0 :: "J_prog \<Rightarrow> J_thread_action \<Rightarrow> J0_thread_action \<Rightarrow> bool"
where "ta_bisim0 P \<equiv> ta_bisim (new_thread_bisim0 P)"

lemma new_thread_bisim0_extNTA2J_extNTA2J0:
  assumes wf: "wwf_J_prog P"
  and red: "P \<turnstile> \<langle>a'\<bullet>M'(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  and nt: "NewThread t (C, M, a) m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  and ha': "h a' \<noteq> None"
  shows "new_thread_bisim0 P (extNTA2J P (C, M, a), m) (extNTA2J0 P (C, M, a), m)"
proof -
  from red nt have [simp]: "m = h'" by(rule red_ext_new_thread_heap)
  from red_external_new_thread_sees[OF wf red nt, OF ha']
  obtain fs T pns body D where h'a: "h' a = \<lfloor>Obj C fs\<rfloor>"
    and sees: "P \<turnstile> C sees M: []\<rightarrow>T = (pns, body) in D" by auto
  from sees_wf_mdecl[OF wf sees] have [simp]: "pns = []" by(simp add: wf_mdecl_def)
  from red nt h'a sees
  show ?thesis by(auto simp add: new_thread_bisim0_def)
qed

lemma ta_bisim0_extNTA2J_extNTA2J0:
  "\<lbrakk> wwf_J_prog P; P \<turnstile> \<langle>a'\<bullet>M'(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; h a' \<noteq> None \<rbrakk>
  \<Longrightarrow> ta_bisim0 P (extTA2J P ta) (extTA2J0 P ta)"
apply(auto simp add: ta_bisim_def intro!: list_all2_all_nthI)
apply(case_tac "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> ! n")
apply(fastsimp simp add: in_set_conv_nth dest: new_thread_bisim0_extNTA2J_extNTA2J0)+
done


lemma assumes wf: "wwf_J_prog P"
  shows red_red0_tabisim0:
  "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> \<exists>ta'. extTA2J0 P,P \<turnstile> \<langle>e, s\<rangle> -ta'\<rightarrow> \<langle>e', s'\<rangle> \<and> ta_bisim0 P ta ta'"
  and reds_reds0_tabisim0:
  "P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> \<exists>ta'. extTA2J0 P,P \<turnstile> \<langle>es, s\<rangle> [-ta'\<rightarrow>] \<langle>es', s'\<rangle> \<and> ta_bisim0 P ta ta'"
proof(induct rule: red_reds.inducts)
  case (RedCallExternal s a T M vs ta va h' ta' e' s')
  note red = `P \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>`
  note T = `typeof\<^bsub>hp s\<^esub> (Addr a) = \<lfloor>T\<rfloor>`
  from T `is_external_call P T M (length vs)` red
  have "extTA2J0 P,P \<turnstile> \<langle>addr a\<bullet>M(map Val vs),s\<rangle> -extTA2J0 P ta\<rightarrow> \<langle>e',(h', lcl s)\<rangle>"
    by(rule red_reds.RedCallExternal)(simp_all add: `e' = extRet2J va`)
  moreover from `ta' = extTA2J P ta` T red wf
  have "ta_bisim0 P ta' (extTA2J0 P ta)" by(auto intro: ta_bisim0_extNTA2J_extNTA2J0)
  ultimately show ?case unfolding `s' = (h', lcl s)` by blast
next
  case RedTryFail thus ?case by(force intro: red_reds.RedTryFail)
qed(fastsimp intro: red_reds.intros simp add: ta_bisim_def)+

lemma assumes wf: "wwf_J_prog P"
  shows red0_red_tabisim0:
  "extTA2J0 P,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> \<exists>ta'. P \<turnstile> \<langle>e, s\<rangle> -ta'\<rightarrow> \<langle>e', s'\<rangle> \<and> ta_bisim0 P ta' ta"
  and reds0_reds_tabisim0:
  "extTA2J0 P,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> \<exists>ta'. P \<turnstile> \<langle>es, s\<rangle> [-ta'\<rightarrow>] \<langle>es', s'\<rangle> \<and> ta_bisim0 P ta' ta"
proof(induct rule: red_reds.inducts)
  case (RedCallExternal s a T M vs ta va h' ta' e' s')
  note red = `P \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>`
  note T = `typeof\<^bsub>hp s\<^esub> (Addr a) = \<lfloor>T\<rfloor>`
  from T `is_external_call P T M (length vs)` red
  have "P \<turnstile> \<langle>addr a\<bullet>M(map Val vs),s\<rangle> -extTA2J P ta\<rightarrow> \<langle>e',(h', lcl s)\<rangle>"
    by(rule red_reds.RedCallExternal)(simp_all add: `e' = extRet2J va`)
  moreover from `ta' = extTA2J0 P ta` T red wf
  have "ta_bisim0 P (extTA2J P ta) ta'" by(auto intro: ta_bisim0_extNTA2J_extNTA2J0)
  ultimately show ?case unfolding `s' = (h', lcl s)` by blast
next
  case RedTryFail thus ?case by(force intro: red_reds.RedTryFail)
qed(fastsimp intro: red_reds.intros simp add: ta_bisim_def)+


lemma red_inline_call_red:
  assumes red: "P \<turnstile> \<langle>e, (h, [this \<mapsto> v])\<rangle> -ta\<rightarrow> \<langle>e', (h', [this \<mapsto> v'])\<rangle>"
  shows "call E = \<lfloor>aMvs\<rfloor> \<Longrightarrow> P \<turnstile> \<langle>inline_call {this:T=\<lfloor>v\<rfloor>; e}\<^bsub>cr\<^esub> E, (h, x)\<rangle> -ta\<rightarrow> \<langle>inline_call {this:T=\<lfloor>v'\<rfloor>; e'}\<^bsub>cr\<^esub> E, (h', x)\<rangle>"
  (is "_ \<Longrightarrow> ?concl E x")

  and
  "calls Es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> P \<turnstile> \<langle>inline_calls {this:T=\<lfloor>v\<rfloor>; e}\<^bsub>cr\<^esub> Es, (h, x)\<rangle> [-ta\<rightarrow>] \<langle>inline_calls {this:T=\<lfloor>v'\<rfloor>; e'}\<^bsub>cr\<^esub> Es, (h', x)\<rangle>"
  (is "_ \<Longrightarrow> ?concls Es x")
proof(induct E and Es arbitrary: x and x)
  case (Call obj M pns x)
  note IHobj = `\<And>x. call obj = \<lfloor>aMvs\<rfloor> \<Longrightarrow> ?concl obj x`
  note IHpns = `\<And>x. calls pns = \<lfloor>aMvs\<rfloor> \<Longrightarrow> ?concls pns x`
  obtain a M' vs where [simp]: "aMvs = (a, M', vs)" by(cases aMvs, auto)
  from `call (obj\<bullet>M(pns)) = \<lfloor>aMvs\<rfloor>` have "call (obj\<bullet>M(pns)) = \<lfloor>(a, M', vs)\<rfloor>" by simp
  thus ?case
  proof(induct rule: call_callE)
    case CallObj
    with IHobj[of x] show ?case by(fastsimp intro: red_reds.CallObj)
  next
    case (CallParams v'')
    with IHpns[of x] show ?case by(fastsimp intro: red_reds.CallParams)
  next
    case Call
    from red have "P \<turnstile> \<langle>e,(h, x(this \<mapsto> v))\<rangle> -ta\<rightarrow> \<langle>e',(h', x(this \<mapsto> v'))\<rangle>"
      by(auto dest: red_lcl_add[where ?l0.0=x])
    with Call show ?case by(fastsimp dest: BlockRed)
  qed
next
  case (Block V T' vo exp cr x)
  note IH = `\<And>x. call exp = \<lfloor>aMvs\<rfloor> \<Longrightarrow> ?concl exp x`
  from IH[of "x(V := vo)"] `call {V:T'=vo; exp}\<^bsub>cr\<^esub> = \<lfloor>aMvs\<rfloor>`
  show ?case by(clarsimp simp del: fun_upd_apply)(drule BlockRed[where cr=cr], auto)
next
  case (Cons_exp exp exps x)
  show ?case
  proof(cases "is_val exp")
    case True
    with `calls (exp # exps) = \<lfloor>aMvs\<rfloor>` have "calls exps = \<lfloor>aMvs\<rfloor>" by auto
    with `calls exps = \<lfloor>aMvs\<rfloor> \<Longrightarrow> ?concls exps x` True
    show ?thesis by(fastsimp intro: ListRed2)
  next
    case False
    with `calls (exp # exps) = \<lfloor>aMvs\<rfloor>` have "call exp = \<lfloor>aMvs\<rfloor>" by auto
    with `call exp = \<lfloor>aMvs\<rfloor> \<Longrightarrow> ?concl exp x`
    show ?thesis by(fastsimp intro: ListRed1)
  qed
qed(fastsimp intro: red_reds.intros)+


lemma is_call_red_inline_call:
  assumes wf_prog: "wf_prog wfmd P"
  and "P \<turnstile> C sees M:Us\<rightarrow>U = (pns, body) in D" "length vs = length pns" "length Us = length pns"
  shows "\<lbrakk> call e = \<lfloor>(a, M, vs)\<rfloor>; hp s a = \<lfloor>Obj C fs\<rfloor> \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>inline_call ({this:Class D=\<lfloor>Addr a\<rfloor>; blocks (pns, Us, vs, body) }\<^bsub>True\<^esub>) e, s\<rangle>"
  (is "_ \<Longrightarrow> _ \<Longrightarrow> ?red e s")
  and "\<lbrakk> calls es = \<lfloor>(a, M, vs)\<rfloor>; hp s a = \<lfloor>Obj C fs\<rfloor> \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>es, s\<rangle> [-\<epsilon>\<rightarrow>] \<langle>inline_calls ({this:Class D=\<lfloor>Addr a\<rfloor>; blocks (pns, Us, vs, body) }\<^bsub>True\<^esub>) es, s\<rangle>"
  (is "_ \<Longrightarrow> _ \<Longrightarrow> ?reds es s")
proof(induct e and es arbitrary: s and s)
  case (Call obj M' params s)
  note IHObj = `\<And>s. \<lbrakk>call obj = \<lfloor>(a, M, vs)\<rfloor>; hp s a = \<lfloor>Obj C fs\<rfloor> \<rbrakk> \<Longrightarrow> ?red obj s`
  note IHParams = `\<And>s. \<lbrakk> calls params = \<lfloor>(a, M, vs)\<rfloor>; hp s a = \<lfloor>Obj C fs\<rfloor> \<rbrakk> \<Longrightarrow> ?reds params s`
  from `call (obj\<bullet>M'(params)) = \<lfloor>(a, M, vs)\<rfloor>`
  show ?case
  proof(induct rule: call_callE)
    case CallObj
    from IHObj[OF CallObj] `hp s a = \<lfloor>Obj C fs\<rfloor>` have "?red obj s" by blast
    moreover from CallObj have "\<not> is_val obj" by auto
    ultimately show ?case by(auto intro: red_reds.CallObj)
  next
    case (CallParams v)
    from IHParams[OF `calls params = \<lfloor>(a, M, vs)\<rfloor>`] `hp s a = \<lfloor>Obj C fs\<rfloor>` have "?reds params s" by blast
    moreover from CallParams have "\<not> is_vals params" by auto
    ultimately show ?case using `obj = Val v` by(auto intro: red_reds.CallParams)
  next
    case Call
    from `P \<turnstile> C sees M:Us\<rightarrow>U = (pns, body) in D` have "\<not> is_external_call P (Class C) M (length vs)"
      by(auto dest: external_call_not_sees_method[OF wf_prog])
    from Call RedCall[where s=s, simplified, OF `hp s a = \<lfloor>Obj C fs\<rfloor>` this `P \<turnstile> C sees M:Us\<rightarrow>U = (pns, body) in D` `length vs = length pns` `length Us = length pns`] 
    show ?thesis by(simp)
  qed
next
  case (Block V ty vo exp cr s)
  note IH = `\<And>s. \<lbrakk>call exp = \<lfloor>(a, M, vs)\<rfloor>; hp s a = \<lfloor>Obj C fs\<rfloor> \<rbrakk> \<Longrightarrow> ?red exp s`
  from `call {V:ty=vo; exp}\<^bsub>cr\<^esub> = \<lfloor>(a, M, vs)\<rfloor>` IH[of "(hp s, (lcl s)(V := vo))"] `hp s a = \<lfloor>Obj C fs\<rfloor>`
  show ?case by(cases s, simp del: fun_upd_apply)(drule red_reds.BlockRed, simp)
qed(fastsimp intro: red_reds.intros)+

lemma inline_call_Val:
  assumes final: "final e'"
  shows "call e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> P \<turnstile> \<langle>inline_call {this:T=vo; e'}\<^bsub>cr\<^esub> e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>inline_call e' e, s\<rangle>"
  and  "calls es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> P \<turnstile> \<langle>inline_calls {this:T=vo; e'}\<^bsub>cr\<^esub> es, s\<rangle> [-\<epsilon>\<rightarrow>] \<langle>inline_calls e' es, s\<rangle>"
proof(induct e and es arbitrary: s and s)
  case (Call obj M params s)
  with final show ?case
    by(cases s, auto intro: red_reds.intros elim!: final.cases)
next
  case (Block V ty Vo exp cr' s)
  note IH = `\<And>s. call exp = \<lfloor>aMvs\<rfloor> \<Longrightarrow> P \<turnstile> \<langle>inline_call {this:T=vo; e'}\<^bsub>cr\<^esub> exp, s\<rangle> -\<epsilon>\<rightarrow> \<langle>inline_call e' exp,s\<rangle>`
  from IH[of "(hp s, (lcl s)(V := Vo))"] `call {V:ty=Vo; exp}\<^bsub>cr'\<^esub> = \<lfloor>aMvs\<rfloor>` show ?case
    by(cases s, auto dest: BlockRed)
qed(fastsimp intro: red_reds.intros)+


lemma red_inline_call_red':
  assumes fv: "fv ee \<subseteq> {this}"
  and eefin: "\<not> final ee"
  shows "\<lbrakk> call E = \<lfloor>aMvs\<rfloor>; P \<turnstile> \<langle>inline_call {this:T=\<lfloor>v\<rfloor>; ee}\<^bsub>cr\<^esub> E, (h, x)\<rangle> -ta\<rightarrow> \<langle>E', (h', x')\<rangle> \<rbrakk> 
         \<Longrightarrow> \<exists>ee' v'. inline_call {this:T=\<lfloor>v'\<rfloor>; ee'}\<^bsub>cr\<^esub> E = E' \<and> P \<turnstile> \<langle>ee, (h, [this \<mapsto> v])\<rangle> -ta\<rightarrow> \<langle>ee', (h', [this \<mapsto> v'])\<rangle> \<and> x = x'"
  (is "\<lbrakk> _; _ \<rbrakk> \<Longrightarrow> ?concl E E' x x'")
  and   "\<lbrakk> calls Es = \<lfloor>aMvs\<rfloor>; P \<turnstile> \<langle>inline_calls {this:T=\<lfloor>v\<rfloor>; ee}\<^bsub>cr\<^esub> Es, (h, x)\<rangle> [-ta\<rightarrow>] \<langle>Es', (h', x')\<rangle> \<rbrakk> 
         \<Longrightarrow> \<exists>ee' v'. inline_calls {this:T=\<lfloor>v'\<rfloor>; ee'}\<^bsub>cr\<^esub> Es = Es' \<and> P \<turnstile> \<langle>ee, (h, [this \<mapsto> v])\<rangle> -ta\<rightarrow> \<langle>ee', (h', [this \<mapsto> v'])\<rangle> \<and> x = x'"
  (is "\<lbrakk> _; _ \<rbrakk> \<Longrightarrow> ?concls Es Es' x x'")
proof(induct E and Es arbitrary: E' x x' and Es' x x')
  case new thus ?case by simp
next
  case (newArray T exp E' x x')
  thus ?case by(auto elim!: red_cases)
next
  case Cast thus ?case by(auto elim!:red_cases) 
next
  case Val thus ?case by simp
next
  case Var thus ?case by simp
next
  case (LAss V exp E' x x')
  thus ?case by(auto elim!: red_cases)
next
  case (BinOp exp1 bop exp2 E' x x')
  thus ?case by(auto elim!: red_cases split: split_if_asm)
next
  case (AAcc a i E' x x')
  thus ?case by(auto elim!: red_cases split: split_if_asm)
next
  case AAss thus ?case by(auto elim!: red_cases split: split_if_asm)
next
  case ALen thus ?case by(auto elim!: red_cases split: split_if_asm)
next
  case FAcc thus ?case by(auto elim!: red_cases)
next
  case FAss thus ?case by(auto elim!: red_cases split: split_if_asm)
next
  case (Call obj M pns E' x x')
  note IHobj = `\<And>x E' x'. \<lbrakk>call obj = \<lfloor>aMvs\<rfloor>; P \<turnstile> \<langle>inline_call {this:T=\<lfloor>v\<rfloor>; ee}\<^bsub>cr\<^esub> obj,(h, x)\<rangle> -ta\<rightarrow> \<langle>E',(h', x')\<rangle>\<rbrakk>
                \<Longrightarrow> ?concl obj E' x x'`
  note IHpns = `\<And>Es' x x'. \<lbrakk>calls pns = \<lfloor>aMvs\<rfloor>; P \<turnstile> \<langle>inline_calls {this:T=\<lfloor>v\<rfloor>; ee}\<^bsub>cr\<^esub> pns,(h, x)\<rangle> [-ta\<rightarrow>] \<langle>Es',(h', x')\<rangle>\<rbrakk>
               \<Longrightarrow> ?concls pns Es' x x'`
  note red = `P \<turnstile> \<langle>inline_call {this:T=\<lfloor>v\<rfloor>; ee}\<^bsub>cr\<^esub> (obj\<bullet>M(pns)),(h, x)\<rangle> -ta\<rightarrow>  \<langle>E',(h', x')\<rangle>`
  obtain a M' vs where [simp]: "aMvs = (a, M', vs)" by(cases aMvs, auto)
  from `call (obj\<bullet>M(pns)) = \<lfloor>aMvs\<rfloor>` have "call (obj\<bullet>M(pns)) = \<lfloor>(a,M',vs)\<rfloor>" by simp
  thus ?case
  proof(induct rule: call_callE)
    case CallObj
    hence "\<not> is_val obj" by auto
    with red CallObj obtain obj' where "E' = obj'\<bullet>M(pns)" 
      and red': "P \<turnstile> \<langle>inline_call {this:T=\<lfloor>v\<rfloor>; ee}\<^bsub>cr\<^esub> obj,(h, x)\<rangle> -ta\<rightarrow> \<langle>obj',(h', x')\<rangle>"
      by(auto elim!: red_cases)
    from IHobj[OF _ red'] CallObj obtain ee' v' 
      where "inline_call {this:T=\<lfloor>v'\<rfloor>; ee'}\<^bsub>cr\<^esub> obj = obj'" "x = x'"
      and "P \<turnstile> \<langle>ee,(h, [this \<mapsto> v])\<rangle> -ta\<rightarrow> \<langle>ee',(h', [this \<mapsto> v'])\<rangle>" by(auto simp del: fun_upd_apply)
    with `E' = obj'\<bullet>M(pns)` CallObj red' show ?case by(fastsimp simp del: fun_upd_apply)
  next
    case (CallParams v'')
    hence "\<not> is_vals pns" by auto
    with red CallParams obtain pns' where "E' = obj\<bullet>M(pns')" 
      and red': "P \<turnstile> \<langle>inline_calls {this:T=\<lfloor>v\<rfloor>; ee}\<^bsub>cr\<^esub> pns,(h, x)\<rangle> [-ta\<rightarrow>] \<langle>pns',(h', x')\<rangle>"
      by(auto elim!: red_cases)
    from IHpns[OF _ red'] CallParams obtain ee' v' 
      where "inline_calls {this:T=\<lfloor>v'\<rfloor>; ee'}\<^bsub>cr\<^esub> pns = pns'" "x = x'"
      and "P \<turnstile> \<langle>ee,(h, [this \<mapsto> v])\<rangle> -ta\<rightarrow> \<langle>ee',(h', [this \<mapsto> v'])\<rangle>" by(auto simp del: fun_upd_apply)
    with `E' = obj\<bullet>M(pns')` CallParams red'
    show ?case by(fastsimp simp del: fun_upd_apply)
  next
    case Call
    with red have red': "P \<turnstile> \<langle>{this:T=\<lfloor>v\<rfloor>; ee}\<^bsub>cr\<^esub>,(h, x)\<rangle> -ta\<rightarrow> \<langle>E',(h', x')\<rangle>" by(auto)
    with eefin obtain ee' x'' v' where "E' = {this:T=\<lfloor>v'\<rfloor>; ee'}\<^bsub>cr\<^esub>"
	and red': "P \<turnstile> \<langle>ee,(h, x(this \<mapsto> v))\<rangle> -ta\<rightarrow> \<langle>ee',(h', x'')\<rangle>" 
	and x': "x' = fun_upd x'' this (x this)"
	and v': "x'' this = \<lfloor>v'\<rfloor>"
      apply -
      apply(auto elim!: red_cases final.cases)
      apply(frule red_lcl_incr)
      apply(clarsimp)
      apply(blast)
      done
    from red' fv have "\<And>V. V \<noteq> this \<Longrightarrow> x'' V = x V"
      by(auto dest: red_notfree_unchanged)
    with x' have "x' = x" by(auto intro: ext)
    moreover from red_lcl_sub[OF red' fv]
    have "P \<turnstile> \<langle>ee,(h, [this \<mapsto> v])\<rangle> -ta\<rightarrow> \<langle>ee',(h', x''|`{this})\<rangle>" by(simp)
    moreover then obtain v'' where "x''|`{this} = [this \<mapsto> v'']"
      by -(drule red_lcl_incr,auto simp add: restrict_map_def expand_fun_eq)
    moreover with v' have "v' = v''"
      apply(simp add: expand_fun_eq)
      apply(erule_tac x="this" in allE)
      apply(simp)
      done
    ultimately show ?thesis using Call v' `E' = {this:T=\<lfloor>v'\<rfloor>; ee'}\<^bsub>cr\<^esub>`
      by(simp del: fun_upd_apply)
  qed
next
  case (Block V ty vo exp cr' E' x x')
  note IH = `\<And>x E' x'. \<lbrakk>call exp = \<lfloor>aMvs\<rfloor>; P \<turnstile> \<langle>inline_call {this:T=\<lfloor>v\<rfloor>; ee}\<^bsub>cr\<^esub> exp,(h, x)\<rangle> -ta\<rightarrow> \<langle>E',(h', x')\<rangle>\<rbrakk>
            \<Longrightarrow> ?concl exp E' x x'`
  from `call {V:ty=vo; exp}\<^bsub>cr'\<^esub> = \<lfloor>aMvs\<rfloor>` have ic: "call exp = \<lfloor>aMvs\<rfloor>" by simp
  note red = `P \<turnstile> \<langle>inline_call {this:T=\<lfloor>v\<rfloor>; ee}\<^bsub>cr\<^esub> {V:ty=vo; exp}\<^bsub>cr'\<^esub>,(h, x)\<rangle> -ta\<rightarrow> \<langle>E',(h', x')\<rangle>`
  hence "P \<turnstile> \<langle>{V:ty=vo; inline_call {this:T=\<lfloor>v\<rfloor>; ee}\<^bsub>cr\<^esub> exp}\<^bsub>cr'\<^esub>,(h, x)\<rangle> -ta\<rightarrow> \<langle>E',(h', x')\<rangle>" by simp
  with ic obtain exp' x'' where "E' = {V:ty=x'' V; exp'}\<^bsub>cr'\<^esub>"
    and red': "P \<turnstile> \<langle>inline_call {this:T=\<lfloor>v\<rfloor>; ee}\<^bsub>cr\<^esub> exp,(h, fun_upd x V vo)\<rangle> -ta\<rightarrow> \<langle>exp',(h', x'')\<rangle>"
    and "x' = fun_upd x'' V (x V)"
    by -(erule red.cases,auto dest: inline_call_eq_Val)
  from IH[OF ic red'] obtain ee' v' 
    where icl: "inline_call {this:T=\<lfloor>v'\<rfloor>; ee'}\<^bsub>cr\<^esub> exp = exp'" "x'' = fun_upd x V vo "
    and red'': "P \<turnstile> \<langle>ee,(h, [this \<mapsto> v])\<rangle> -ta\<rightarrow> \<langle>ee',(h', [this \<mapsto> v'])\<rangle>" by blast
  from `x'' = fun_upd x V vo` have "x'' V = vo" by(simp add: expand_fun_eq)
  with icl red'' `E' = {V:ty=x'' V; exp'}\<^bsub>cr'\<^esub>` `x' = fun_upd x'' V (x V)` red'
  show ?case by(auto simp del: fun_upd_apply)
next
  case Synchronized thus ?case by(auto elim!: red_cases)
next
  case InSynchronized thus ?case by(auto elim!: red_cases)
next
  case (Seq exp1 exp2 E' x x')
  thus ?case by(auto elim!: red_cases)
next
  case Cond thus ?case by(auto elim!: red_cases)
next
  case While thus ?case by simp
next
  case (throw exp E' x x')
  thus ?case by(auto elim!: red_cases)
next
  case (TryCatch exp1 C V exp2 E' x x')
  thus ?case by(auto elim!: red_cases)
next
  case Nil_exp thus ?case by simp
next
  case (Cons_exp exp list Es' x x')
  thus ?case by(auto elim!: reds_cases split: split_if_asm)
qed


lemma red_inline_call_Block_final:
  assumes e''fin: "final e''"
  shows "\<lbrakk> P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; call e = \<lfloor>aMvs\<rfloor> \<rbrakk>
         \<Longrightarrow> e' = inline_call e'' e \<and> s = s' \<and> ta = \<epsilon>"
  and   "\<lbrakk> P \<turnstile> \<langle>inline_calls {V':T=vo; e''}\<^bsub>cr\<^esub> es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; calls es = \<lfloor>aMvs\<rfloor> \<rbrakk>
         \<Longrightarrow> es' = inline_calls e'' es \<and> s = s' \<and> ta = \<epsilon>"
proof(induct e and es arbitrary: e' s s' and es' s s')
  case (BinOp exp1 bop exp2 e' s s')
  note IH1 = `\<And>e' s s'. \<lbrakk>P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp1,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; call exp1 = \<lfloor>aMvs\<rfloor>\<rbrakk>
           \<Longrightarrow> e' = inline_call e'' exp1 \<and> s = s' \<and> ta = \<epsilon>`
  note IH2 = `\<And>e' s s'. \<lbrakk>P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp2,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; call exp2 = \<lfloor>aMvs\<rfloor>\<rbrakk>
           \<Longrightarrow> e' = inline_call e'' exp2 \<and> s = s' \<and> ta = \<epsilon>`
  note red = `P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> (exp1 \<guillemotleft>bop\<guillemotright> exp2),s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>` 
  note ic = `call (exp1 \<guillemotleft>bop\<guillemotright> exp2) = \<lfloor>aMvs\<rfloor>`
  show ?case
  proof(cases "is_val exp1")
    case True
    with red ic obtain exp2'
      where "e' = exp1 \<guillemotleft>bop\<guillemotright> exp2'" "P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp2,s\<rangle> -ta\<rightarrow> \<langle>exp2',s'\<rangle>"
      by(auto elim!: red_cases)
    with True ic IH2[of s exp2' s'] show ?thesis by(auto)
  next
    case False
    with red ic obtain exp1' 
      where "e' = exp1' \<guillemotleft>bop\<guillemotright> exp2" "P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp1,s\<rangle> -ta\<rightarrow> \<langle>exp1',s'\<rangle>"
      by(auto elim!: red_cases)
    with False ic IH1[of s exp1' s'] show ?thesis by(auto)
  qed
next
  case (AAcc exp1 exp2 e' s s')
  note IH1 = `\<And>e' s s'. \<lbrakk>P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp1,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; call exp1 = \<lfloor>aMvs\<rfloor>\<rbrakk>
           \<Longrightarrow> e' = inline_call e'' exp1 \<and> s = s' \<and> ta = \<epsilon>`
  note IH2 = `\<And>e' s s'. \<lbrakk>P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp2,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; call exp2 = \<lfloor>aMvs\<rfloor>\<rbrakk>
           \<Longrightarrow> e' = inline_call e'' exp2 \<and> s = s' \<and> ta = \<epsilon>`
  note red = `P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> (exp1\<lfloor>exp2\<rceil>),s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note ic = `call (exp1\<lfloor>exp2\<rceil>) = \<lfloor>aMvs\<rfloor>`
  show ?case
  proof(cases "is_val exp1")
    case True
    with red ic obtain exp2'
      where "e' = exp1\<lfloor>exp2'\<rceil>" "P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp2,s\<rangle> -ta\<rightarrow> \<langle>exp2',s'\<rangle>"
      by(auto elim!: red_cases)
    with True ic IH2[of s exp2' s'] show ?thesis by(auto)
  next
    case False
    with red ic obtain exp1'
      where "e' = exp1'\<lfloor>exp2\<rceil>" "P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp1,s\<rangle> -ta\<rightarrow> \<langle>exp1',s'\<rangle>"
      by(auto elim!: red_cases)
    with False ic IH1[of s exp1' s'] show ?thesis by(auto)
  qed
next
  case (AAss exp1 exp2 exp3 e' s s')
  note IH1 = `\<And>e' s s'. \<lbrakk>P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp1,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; call exp1 = \<lfloor>aMvs\<rfloor>\<rbrakk>
           \<Longrightarrow> e' = inline_call e'' exp1 \<and> s = s' \<and> ta = \<epsilon>`
  note IH2 = `\<And>e' s s'. \<lbrakk>P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp2,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; call exp2 = \<lfloor>aMvs\<rfloor>\<rbrakk>
           \<Longrightarrow> e' = inline_call e'' exp2 \<and> s = s' \<and> ta = \<epsilon>`
  note IH3 = `\<And>e' s s'. \<lbrakk>P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp3,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; call exp3 = \<lfloor>aMvs\<rfloor>\<rbrakk>
           \<Longrightarrow> e' = inline_call e'' exp3 \<and> s = s' \<and> ta = \<epsilon>`
  note red = `P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> (exp1\<lfloor>exp2\<rceil> := exp3),s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note ic = `call (exp1\<lfloor>exp2\<rceil> := exp3) = \<lfloor>aMvs\<rfloor>`
  show ?case
  proof(cases "is_val exp1")
    case True
    show ?thesis
    proof(cases "is_val exp2")
      case True
      with red ic `is_val exp1` obtain exp3'
	where "e' = exp1\<lfloor>exp2\<rceil> := exp3'" "P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp3,s\<rangle> -ta\<rightarrow> \<langle>exp3',s'\<rangle>"
	by(auto elim!: red_cases)
      with True `is_val exp1` ic IH3[of s exp3' s'] show ?thesis by(auto)
    next
      case False
      with red ic True obtain exp2'
	where "e' = exp1\<lfloor>exp2'\<rceil> := exp3" "P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp2,s\<rangle> -ta\<rightarrow> \<langle>exp2',s'\<rangle>"
	by(auto elim!: red_cases)
      with True False ic IH2[of s exp2' s'] show ?thesis by(auto)
    qed
  next
    case False
    with red ic obtain exp1'
      where "e' = exp1'\<lfloor>exp2\<rceil> := exp3" "P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp1,s\<rangle> -ta\<rightarrow> \<langle>exp1',s'\<rangle>"
      by(auto elim!: red_cases)
    with False ic IH1[of s exp1' s'] show ?thesis by(auto)
  qed
next
  case (FAss exp1 F D exp2 e' s s')
  note IH1 = `\<And>e' s s'. \<lbrakk>P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp1,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; call exp1 = \<lfloor>aMvs\<rfloor>\<rbrakk>
           \<Longrightarrow> e' = inline_call e'' exp1 \<and> s = s' \<and> ta = \<epsilon>`
  note IH2 = `\<And>e' s s'. \<lbrakk>P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp2,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; call exp2 = \<lfloor>aMvs\<rfloor>\<rbrakk>
           \<Longrightarrow> e' = inline_call e'' exp2 \<and> s = s' \<and> ta = \<epsilon>`
  note red = `P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> (exp1\<bullet>F{D} := exp2),s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note ic = `call (exp1\<bullet>F{D} := exp2) = \<lfloor>aMvs\<rfloor>`
  show ?case
  proof(cases "is_val exp1")
    case True
    with red ic obtain exp2'
      where "e' = exp1\<bullet>F{D} := exp2'" "P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp2,s\<rangle> -ta\<rightarrow> \<langle>exp2',s'\<rangle>"
      by(auto elim!: red_cases)
    with True ic IH2[of s exp2' s'] show ?thesis by(auto)
  next
    case False
    with red ic obtain exp1'
      where "e' = exp1'\<bullet>F{D} := exp2" "P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp1,s\<rangle> -ta\<rightarrow> \<langle>exp1',s'\<rangle>"
      by(auto elim!: red_cases)
    with False ic IH1[of s exp1' s'] show ?thesis by(auto)
  qed
next
  case (Call obj M pns e' s s')
  note IHobj = `\<And>e' s s'. \<lbrakk>P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> obj,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; call obj = \<lfloor>aMvs\<rfloor>\<rbrakk> 
             \<Longrightarrow> e' = inline_call e'' obj \<and> s = s' \<and> ta = \<epsilon>`
  note IHparams = `\<And>es' s s'. \<lbrakk> P \<turnstile> \<langle>inline_calls {V':T=vo; e''}\<^bsub>cr\<^esub> pns,s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>; calls pns = \<lfloor>aMvs\<rfloor> \<rbrakk>
             \<Longrightarrow> es' = inline_calls e'' pns \<and> s = s' \<and> ta = \<epsilon>`
  note red = `P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> (obj\<bullet>M(pns)),s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  obtain a M' vs where [simp]: "aMvs = (a, M', vs)" by(cases aMvs, auto)
  from `call (obj\<bullet>M(pns)) = \<lfloor>aMvs\<rfloor>` have "call (obj\<bullet>M(pns)) = \<lfloor>(a, M', vs)\<rfloor>" by simp
  thus ?case
  proof(induct rule: call_callE)
    case CallObj
    moreover hence "inline_call e'' (obj\<bullet>M(pns))= inline_call e'' obj\<bullet>M(pns)" by auto
    moreover with red CallObj
    obtain obj' where "P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> obj, s\<rangle> -ta\<rightarrow> \<langle>obj', s'\<rangle>" "e' = obj'\<bullet>M(pns)"
      by -(auto split: split_if_asm elim!: red_cases)
    ultimately show ?thesis by(auto split: split_if_asm dest: IHobj)
  next
    case (CallParams v')
    moreover hence "inline_call (Val v) (obj\<bullet>M(pns))= obj\<bullet>M(inline_calls (Val v) pns)" by auto
    moreover with red CallParams
    obtain pns' where "P \<turnstile> \<langle>inline_calls {V':T=vo; e''}\<^bsub>cr\<^esub> pns, s\<rangle> [-ta\<rightarrow>] \<langle>pns', s'\<rangle>" "e' = obj\<bullet>M(pns')"
      by -(auto elim!: red_cases split: split_if_asm )
    ultimately show ?thesis by(auto split: split_if_asm dest: IHparams)
  next
    case Call
    with red e''fin show ?thesis by(fastsimp elim: red_cases)
  qed
next
  case (Synchronized V exp1 exp2 e' s s')
  note IH1 = `\<And>e' s s'. \<lbrakk>P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp1,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; call exp1 = \<lfloor>aMvs\<rfloor>\<rbrakk>
           \<Longrightarrow> e' = inline_call e'' exp1 \<and> s = s' \<and> ta = \<epsilon>`
  from `call (sync\<^bsub>V\<^esub> (exp1) exp2) = \<lfloor>aMvs\<rfloor>` have "call exp1 = \<lfloor>aMvs\<rfloor>" by simp
  with `P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> (sync\<^bsub>V\<^esub> (exp1) exp2),s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  obtain exp1' where "e' = sync\<^bsub>V\<^esub> (exp1') exp2" "P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp1,s\<rangle> -ta\<rightarrow> \<langle>exp1',s'\<rangle>"
    by(auto elim!: red_cases)
  with IH1[of s exp1' s'] `call exp1 = \<lfloor>aMvs\<rfloor>` show ?case by(auto)
next
  case (Seq exp1 exp2 e' s s')
  with e''fin show ?case by(cases s, cases s', auto elim!: red_cases final.cases)
next
  case (Cond exp1 exp2 exp3 e' s s')
  note IH1 = `\<And>e' s s'. \<lbrakk>P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp1,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; call exp1 = \<lfloor>aMvs\<rfloor>\<rbrakk>
           \<Longrightarrow> e' = inline_call e'' exp1 \<and> s = s' \<and> ta = \<epsilon>`
  from `call (if (exp1) exp2 else exp3) = \<lfloor>aMvs\<rfloor>` have "call exp1 = \<lfloor>aMvs\<rfloor>" by simp
  moreover with `P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> (if (exp1) exp2 else exp3),s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
    obtain exp1' where "e' = if (exp1') exp2 else exp3" "P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp1,s\<rangle> -ta\<rightarrow> \<langle>exp1',s'\<rangle>"
    by(auto elim!: red_cases)
  ultimately show ?case using IH1[of s exp1' s'] by auto
next
  case (TryCatch exp1 C V exp2 e' s s')
  with e''fin show ?case by(cases s, cases s', auto elim!: red_cases final.cases)
next
  case (Cons_exp exp list es' s s')
  note IH1 = `\<And>e' s s'. \<lbrakk>P \<turnstile> \<langle>inline_call {V':T=vo; e''}\<^bsub>cr\<^esub> exp,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; call exp = \<lfloor>aMvs\<rfloor> \<rbrakk>
           \<Longrightarrow> e' = inline_call e'' exp \<and> s = s' \<and> ta = \<epsilon>`
  note IH2 = `\<And>es' s s'. \<lbrakk>P \<turnstile> \<langle>inline_calls {V':T=vo; e''}\<^bsub>cr\<^esub> list,s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>; calls list = \<lfloor>aMvs\<rfloor> \<rbrakk>
           \<Longrightarrow> es' = inline_calls e'' list \<and> s = s' \<and> ta = \<epsilon>`
  note red = `P \<turnstile> \<langle>inline_calls {V':T=vo; e''}\<^bsub>cr\<^esub> (exp # list),s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>`
  then obtain exp' list' where es': "es' = exp' # list'"
    by(auto elim!: reds_cases split: split_if_asm) 
  show ?case
  proof(cases "is_val exp")
    case False
    with IH1[of s exp' s'] red es' e''fin `calls (exp # list) = \<lfloor>aMvs\<rfloor>`
    have "exp' = inline_call e'' exp \<and> s = s' \<and> list = list' \<and> ta = \<epsilon>"
      by-(auto elim!: reds_cases final.cases split: split_if_asm )
    with False es' `calls (exp # list) = \<lfloor>aMvs\<rfloor>` show ?thesis by(fastsimp simp del: fun_upd_apply)
  next
    case True
    with IH2[of s list' s'] red es' `calls (exp # list) = \<lfloor>aMvs\<rfloor>`
    have "list' = inline_calls e'' list \<and> s = s' \<and> exp = exp' \<and> ta = \<epsilon>"
      by-(auto elim!: reds_cases split: split_if_asm)
    with True es' `calls (exp # list) = \<lfloor>aMvs\<rfloor>`
    show ?thesis by(fastsimp simp del: fun_upd_apply)
  qed
qed(insert e''fin, (fastsimp elim!: red_cases)+)

lemma assumes wf: "wwf_J_prog P"
  and sees: "P \<turnstile> C sees M:Us\<rightarrow>U = (pns, body) in D"
  shows is_call_red_inline_callD:
        "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; call e = \<lfloor>(a, M, vs)\<rfloor>; hp s a = \<lfloor>Obj C fs\<rfloor>; \<not> synthesized_call P (hp s) (a, M, vs) \<rbrakk>
        \<Longrightarrow> e' = inline_call {this:Class D=\<lfloor>Addr a\<rfloor>; blocks (pns, Us, vs, body)}\<^bsub>True\<^esub> e"
  and is_calls_reds_inline_callsD:
        "\<lbrakk> P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; calls es = \<lfloor>(a, M, vs)\<rfloor>; hp s a = \<lfloor>Obj C fs\<rfloor>; \<not> synthesized_call P (hp s) (a, M, vs) \<rbrakk>
        \<Longrightarrow> es' = inline_calls {this:Class D=\<lfloor>Addr a\<rfloor>; blocks (pns, Us, vs, body)}\<^bsub>True\<^esub> es"
proof(induct rule: red_reds.inducts)
  case (RedCall s a' C' fs' M' Us' U' pns' body' D' vs')
  with sees show ?case by(auto dest: sees_method_fun)
next
  case RedCallExternal
  with sees show ?case by(auto dest: external_call_not_sees_method[OF wf])
next
  case (BlockRed e h x V vo ta e' h' x' T cr')
  from `call {V:T=vo; e}\<^bsub>cr'\<^esub> = \<lfloor>(a, M, vs)\<rfloor>` have "call e = \<lfloor>(a, M, vs)\<rfloor>" by simp
  with `P \<turnstile> \<langle>e,(h, x(V := vo))\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>` `\<not> synthesized_call P (hp (h, x)) (a, M, vs)`
  have "x(V := vo) = x'" by(auto dest: is_call_red_state_unchanged)
  hence "x' V = vo" by auto
  with BlockRed show ?case by(simp)
qed(fastsimp split: split_if_asm)+



lemma red_fold_exs:
  assumes wwf: "wwf_J_prog P"
  shows
  "\<lbrakk> P \<turnstile> \<langle>e,(h, x)\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>; wf_state h (e, x) exs \<rbrakk>
  \<Longrightarrow>  P \<turnstile> \<langle>fst (fold_exs P h (e, x) exs), (h, snd (fold_exs P h (e, x) exs))\<rangle> -ta\<rightarrow> \<langle>fst (fold_exs P h' (e', x') exs), (h', snd (fold_exs P h' (e', x') exs))\<rangle>"
  (is "_ \<Longrightarrow> _ \<Longrightarrow> ?concl e x e' x' exs")
proof(induct exs arbitrary: e e' x x')
  case Nil thus ?case by simp
next
  case (Cons ex exs e e' x x')
  note IH = `\<And>e x e' x'. \<lbrakk> P \<turnstile> \<langle>e,(h, x)\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>; wf_state h (e, x) exs \<rbrakk> 
          \<Longrightarrow> ?concl e x e' x' exs`
  note wfs = `wf_state h (e, x) (ex # exs)`
  hence icl: "is_call_list h (map fst (ex # exs))" by auto
  note red = `P \<turnstile> \<langle>e,(h, x)\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>`
  from icl obtain a M vs arrobj 
    where call: "call (fst ex) = \<lfloor>(a, M, vs)\<rfloor>" 
    and arrobj: "h a = \<lfloor>arrobj\<rfloor>" by(auto)
  moreover
  let ?T = "Class (fst (method P (case arrobj of (Obj C fs) \<Rightarrow> C | _ \<Rightarrow> arbitrary) M))"
  from wfs obtain v where x: "x = [this \<mapsto> v]" by(auto)
  moreover with wfs have "fv e \<subseteq> {this}" by(auto)
  from red have "dom x' \<subseteq> dom x \<union> fv e"
    by(auto dest!: red_dom_lcl del: subsetI)
  with x `fv e \<subseteq> {this}` have "dom x' \<subseteq> {this}" by(auto)
  with x red have "dom x' = {this}" by(auto dest: red_lcl_incr)
  then obtain v' where x': "x' = [this \<mapsto> v']" by(auto simp add: dom_eq_singleton_conv)
  ultimately 
  have red': "P \<turnstile> \<langle>inline_call {this:?T=\<lfloor>v\<rfloor>; e}\<^bsub>True\<^esub> (fst ex),(h, snd ex)\<rangle> 
              -ta\<rightarrow> \<langle>inline_call {this:?T=\<lfloor>v'\<rfloor>; e'}\<^bsub>True\<^esub> (fst ex),(h', snd ex)\<rangle>"
    using red by(auto intro: red_inline_call_red(1))
  moreover from wfs have "fv (fst ex) \<subseteq> {this}" by(auto del: subsetI)
  from call have "fv (inline_call {this:?T=\<lfloor>v\<rfloor>; e}\<^bsub>True\<^esub> (fst ex)) \<subseteq> fv (fst ex) \<union> fv ({this:?T=\<lfloor>v\<rfloor>; e}\<^bsub>True\<^esub>)"
    by(rule fv_inline_call)
  with `fv e \<subseteq> {this}` have "fv (inline_call {this:?T=\<lfloor>v\<rfloor>; e}\<^bsub>True\<^esub> (fst ex)) \<subseteq> fv (fst ex)" by(auto)
  with wfs have "wf_state h (inline_call {this:?T=\<lfloor>v\<rfloor>; e}\<^bsub>True\<^esub> (fst ex), snd ex) exs" by(auto del: subsetI)
  ultimately have "?concl (inline_call {this:?T=\<lfloor>v\<rfloor>; e}\<^bsub>True\<^esub> (fst ex)) (snd ex) (inline_call {this:?T=\<lfloor>v'\<rfloor>; e'}\<^bsub>True\<^esub> (fst ex)) (snd ex) exs"
    by(rule IH)
  moreover from red have "hext h h'" by(auto dest: red_hext_incr)
  with arrobj obtain arrobj' where arrobj': "h' a = \<lfloor>arrobj'\<rfloor>" by(auto dest: hext_objarrD)
  with `hext h h'` arrobj 
  have "(case arrobj of (Obj C fs) \<Rightarrow> C | _ \<Rightarrow> arbitrary) = (case arrobj' of (Obj C fs) \<Rightarrow> C | _ \<Rightarrow> arbitrary)"
  proof(cases arrobj)
    case Obj with `hext h h'` arrobj arrobj'
    show ?thesis by(auto dest!: hext_objD)
  next
    case Arr with `hext h h'` arrobj arrobj'
    show ?thesis by(auto dest!: hext_arrD)
  qed
  ultimately show ?case using call arrobj arrobj' x x' by(simp)
qed

lemma red_fold_exs':
  assumes wwf: "wwf_J_prog P"
  shows
  "\<lbrakk> P \<turnstile> \<langle>fst (fold_exs P h ex exs), (h, snd (fold_exs P h ex exs))\<rangle> -ta\<rightarrow> \<langle>e', (h', x')\<rangle>;
     wf_state h ex exs; \<not> final (fst ex) \<rbrakk>
  \<Longrightarrow> \<exists>ex'. fold_exs P h' ex' exs = (e', x') \<and> P \<turnstile> \<langle>fst ex, (h, snd ex)\<rangle> -ta\<rightarrow> \<langle>fst ex', (h', snd ex')\<rangle>"
  (is "\<lbrakk> ?red ex exs; _; _ \<rbrakk> \<Longrightarrow> ?concl ex exs")
proof(induct exs arbitrary: ex)
  case Nil thus ?case by(auto)
next
  case (Cons Ex exs ex)
  note IH = `\<And>ex. \<lbrakk> ?red ex exs; wf_state h ex exs; \<not> final (fst ex) \<rbrakk> \<Longrightarrow> ?concl ex exs`
  obtain e x where [simp]: "Ex = (e, x)" by(cases Ex, auto)
  from `wf_state h ex (Ex # exs)` have wfs: "wf_state h ex ((e, x) # exs)" by simp
  note nfin = `\<not> final (fst ex)`
  from `?red ex (Ex # exs)` have red: "?red ex ((e, x) # exs)" by simp
  from wfs have icl: "is_call_list h (e # map fst exs)" by auto
  then obtain a M vs arrobj 
    where call: "call e = \<lfloor>(a, M, vs)\<rfloor>"
    and arrobj: "h a = \<lfloor>arrobj\<rfloor>" by auto
  moreover
  let ?T = "Class (fst (method P (case arrobj of (Obj C fs) \<Rightarrow> C | _ \<Rightarrow> arbitrary) M))"
  from wfs obtain v where x: "snd ex = [this \<mapsto> v]" by(auto)
  with red arrobj call have red': "?red (inline_call {this:?T=\<lfloor>v\<rfloor>; fst ex}\<^bsub>True\<^esub> e, x) exs" by(simp)
  moreover from wfs have "fv (fst ex) \<subseteq> {this}" "fv e \<subseteq> {this}" by(auto del: subsetI)
  from call have "fv (inline_call {this:?T=\<lfloor>v\<rfloor>; fst ex}\<^bsub>True\<^esub> e) \<subseteq> fv e \<union> fv ({this:?T=\<lfloor>v\<rfloor>; fst ex}\<^bsub>True\<^esub>)"
    by(rule fv_inline_call)
  with `fv (fst ex) \<subseteq> {this}`
  have "fv (inline_call {this:?T=\<lfloor>v\<rfloor>; fst ex}\<^bsub>True\<^esub> e) \<subseteq> fv e" by(auto)
  with wfs have "wf_state h (inline_call {this:?T=\<lfloor>v\<rfloor>; fst ex}\<^bsub>True\<^esub> e, x) exs" by(auto del: subsetI)
  moreover from call have "\<not> final (inline_call {this:?T=\<lfloor>v\<rfloor>; fst ex}\<^bsub>True\<^esub> e)"
    by(auto elim!: final.cases)
  ultimately have "?concl (inline_call {this:?T=\<lfloor>v\<rfloor>; fst ex}\<^bsub>True\<^esub> e, x) exs"
    by-(rule IH, auto)
  then obtain ex' where fold: "fold_exs P h' ex' exs = (e', x')" 
    and "P \<turnstile> \<langle>fst (inline_call {this:?T=\<lfloor>v\<rfloor>; fst ex}\<^bsub>True\<^esub> e, x), (h, snd (inline_call {this:?T=\<lfloor>v\<rfloor>; fst ex}\<^bsub>True\<^esub> e, x))\<rangle> -ta\<rightarrow> \<langle>fst ex',(h', snd ex')\<rangle>" by blast
  moreover obtain e'' x'' where [simp]: "ex' = (e'', x'')" by(cases ex', auto)
  ultimately have red': "P \<turnstile> \<langle>inline_call {this:?T=\<lfloor>v\<rfloor>; fst ex}\<^bsub>True\<^esub> e, (h, x)\<rangle> -ta\<rightarrow> \<langle>e'',(h', x'')\<rangle>" by simp
  from red_inline_call_red'(1)[OF `fv (fst ex) \<subseteq> {this}` nfin call red']
  obtain e''' v' where inline: "inline_call {this:?T=\<lfloor>v'\<rfloor>; e'''}\<^bsub>True\<^esub> e = e''"
    and red'': "P \<turnstile> \<langle>fst ex,(h, [this \<mapsto> v])\<rangle> -ta\<rightarrow> \<langle>e''',(h', [this \<mapsto> v'])\<rangle>"
    and x'': "x = x''" by blast
  moreover
  from red'' have "hext h h'" by(auto dest: red_hext_incr)
  with arrobj obtain arrobj' where arrobj': "h' a = \<lfloor>arrobj'\<rfloor>" by(auto dest: hext_objarrD)
  with `hext h h'` arrobj 
  have "(case arrobj of (Obj C fs) \<Rightarrow> C | _ \<Rightarrow> arbitrary) = (case arrobj' of (Obj C fs) \<Rightarrow> C | _ \<Rightarrow> arbitrary)"
  proof(cases arrobj)
    case Obj with `hext h h'` arrobj arrobj'
    show ?thesis by(auto dest!: hext_objD)
  next
    case Arr with `hext h h'` arrobj arrobj'
    show ?thesis by(auto dest!: hext_arrD)
  qed
  ultimately show ?case using call x fold inline arrobj' arrobj
    by -(rule_tac x="(e''', [this \<mapsto> v'])" in exI, simp del: fun_upd_apply, simp)
qed

lemma red0_return_inline_call:
  "P \<turnstile>0 \<langle>(e, x)/(e'', x'')#exs, h\<rangle> -\<epsilon>\<rightarrow> \<langle>(e', x')/exs, h'\<rangle> 
   \<Longrightarrow> P \<turnstile> \<langle>inline_call {this:T=vo; e}\<^bsub>True\<^esub> e'', (h, x'')\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h', x')\<rangle>"
by(auto intro: inline_call_Val elim!: red0.cases)

lemma new_thread_bisim0_bisim_red_red0:
  assumes wf: "wf_J_prog P"
  and ntb: "new_thread_bisim0 P exs exs'"
  shows "bisim_red_red0 P exs exs'"
using ntb
apply(cases exs, cases exs')
apply(auto simp add: new_thread_bisim0_def)
apply(auto split: heapobj.split_asm)
apply(frule sees_wf_mdecl[OF wf_prog_wwf_prog[OF wf]])
apply(frule sees_wf_mdecl[OF wf])
apply(rule bisim_red_red0.intros)
  apply simp
 apply(rule wf_state.intros)
   apply(simp add: wf_mdecl_def)
  apply fastsimp
 apply simp
apply(auto simp add: wf_mdecl_def intro: WT_noRetBlock)
done

lemma ta_bisim0_bisim_red_red0:
  assumes wf: "wf_J_prog P"
  shows "ta_bisim0 P ta ta' \<Longrightarrow> ta_bisim (bisim_red_red0 P) ta ta'"
by(fastsimp simp add: ta_bisim_def elim: list_all2_mono nta_bisim_mono intro: new_thread_bisim0_bisim_red_red0[OF wf])

lemma assumes nrb: "noRetBlock e"
  shows noRetBlock_inline_call: "noRetBlock e' \<Longrightarrow> noRetBlock (inline_call e e')"
  and noRetBlocks_inline_calls: "noRetBlocks es' \<Longrightarrow> noRetBlocks (inline_calls e es')"
by(induct e' and es')(auto intro: nrb)

lemma noRetBlock_extRet2J [simp]: "noRetBlock (extRet2J va)"
by(cases va) simp_all

lemma assumes wf: "wf_prog wfmd P"
  shows no_call_red_preserves_noRetBlock:
  "\<lbrakk> extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<forall>aMvs. call e = \<lfloor>aMvs\<rfloor> \<longrightarrow> synthesized_call P (hp s) aMvs; noRetBlock e \<rbrakk> \<Longrightarrow> noRetBlock e'"
  and no_calls_reds_preserves_noRetBlocks:
  "\<lbrakk> extTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; \<forall>aMvs. calls es = \<lfloor>aMvs\<rfloor> \<longrightarrow> synthesized_call P (hp s) aMvs; noRetBlocks es \<rbrakk> \<Longrightarrow> noRetBlocks es'"
proof(induct rule: red_reds.inducts)
  case RedCall thus ?case
    by(auto dest: external_call_not_sees_method[OF wf] simp add: synthesized_call_conv)
qed(auto split: split_if_asm)

abbreviation mred0 :: "J_prog \<Rightarrow> (addr,addr,(expr \<times> locals) \<times> (expr \<times> locals) list,heap,addr) semantics"
where "mred0 P \<equiv> (\<lambda>((ex, exs), h) ta ((ex', exs'), h'). red0 P ex exs h ta ex' exs' h')"

lemma bisimulation_red_red0:
  assumes wf: "wf_J_prog P" 
  shows "bisimulation (mred P) (mred0 P) (bisim_red_red0 P) (ta_bisim (bisim_red_red0 P))"
proof(unfold_locales)
  fix s1 s2 ta s1'
  assume "bisim_red_red0 P s1 s2" "mred P s1 ta s1'"
  moreover obtain e1 h1 x1 where "s1 = ((e1, x1), h1)" by(cases s1, auto)
  moreover obtain e1' h1' x1' where "s1' = ((e1', x1'), h1')" by(cases s1', auto)
  moreover obtain ex exs h2 where "s2 = ((ex, exs), h2)" by(cases s2, auto)
  ultimately have bisim: "bisim_red_red0 P ((e1, x1), h1) ((ex, exs), h2)"
    and red: "P \<turnstile> \<langle>e1, (h1, x1)\<rangle> -ta\<rightarrow> \<langle>e1', (h1', x1')\<rangle>" by auto
  hence hext: "hext h1 h1'" by(auto dest: red_hext_incr)
  note wwf = wf_prog_wwf_prog[OF wf]
  from bisim have heap: "h1 = h2"
    and fold: "(e1, x1) = fold_exs P h2 ex exs"
    and wf_state: "wf_state h2 ex exs"
    and nrbs: "noRetBlocks (map fst exs)"
    and nrb: "noRetBlock (fst ex)"
    by(auto elim!: bisim_red_red0.cases del: wf_state.cases)
  have "\<exists>ta' ex' exs' h2'. ta_bisim (bisim_red_red0 P) ta ta' \<and> P \<turnstile>0 \<langle>ex/exs,h2\<rangle> -ta'\<rightarrow> \<langle>ex'/exs',h2'\<rangle> \<and>
                           bisim_red_red0 P ((e1', x1'), h1') ((ex', exs'), h2')"
  proof(cases "final (fst ex)")
    case False
    from red_fold_exs'[OF wwf _ wf_state False, folded fold, simplified fst_conv snd_conv, OF red[unfolded heap]]
    obtain ex' where fold': "fold_exs P h1' ex' exs = (e1', x1')"
      and red': "P \<turnstile> \<langle>fst ex,(h2, snd ex)\<rangle> -ta\<rightarrow> \<langle>fst ex',(h1', snd ex')\<rangle>" by(auto)
    show ?thesis
    proof(cases "\<forall>aMvs. call (fst ex) = \<lfloor>aMvs\<rfloor> \<longrightarrow> synthesized_call P h2 aMvs")
      case True
      with red_red0_tabisim0[OF wwf red'] obtain ta'
	where red': "extTA2J0 P,P \<turnstile> \<langle>fst ex,(h2, snd ex)\<rangle> -ta'\<rightarrow> \<langle>fst ex',(h1', snd ex')\<rangle>"
	and tab': "ta_bisim0 P ta ta'" by blast
      from wf tab' have tab: "ta_bisim (bisim_red_red0 P) ta ta'" by(rule ta_bisim0_bisim_red_red0)
      from red' True have "P \<turnstile>0 \<langle>(fst ex, snd ex) / exs, h2\<rangle> -ta'\<rightarrow> \<langle>(fst ex', snd ex') / exs, h1'\<rangle>" by(rule red0.red0Red)
      hence red'': "P \<turnstile>0 \<langle>ex / exs, h2\<rangle> -ta'\<rightarrow> \<langle>ex' / exs, h1'\<rangle>" by simp
      with wf_state have "wf_state h1' ex' exs" by-(rule red0_preserves_wf_state[OF wwf])
      moreover from red' True nrb have "noRetBlock (fst ex')" by(auto intro: no_call_red_preserves_noRetBlock[OF wf])
      ultimately have "bisim_red_red0 P ((e1', x1'), h1') ((ex', exs), h1')" using fold' nrbs
	by(auto intro: bisim_red_red0.intros)
      with red'' tab show ?thesis unfolding hp_def fst_conv by(blast)
    next
      case False
      then obtain a M vs where call: "call (fst ex) = \<lfloor>(a, M, vs)\<rfloor>"
	and notsynth: "\<not> synthesized_call P h2 (a, M, vs)" by auto
      with called_methodD[OF red' call] obtain C fs D Us U pns body
	where "h1' = h2"
	and ha: "h2 a = \<lfloor>Obj C fs\<rfloor>"
	and sees: "P \<turnstile> C sees M: Us\<rightarrow>U = (pns, body) in D"
	and length: "length vs = length pns" "length Us = length pns"
	by(auto, blast)
      with call notsynth
      have "P \<turnstile>0 \<langle>(fst ex, snd ex)/exs,h2\<rangle> -\<epsilon>\<rightarrow> \<langle>(blocks (pns, Us, vs, body), [this \<mapsto> Addr a])/(fst ex, snd ex) # exs,h2\<rangle>"
	by -(rule red0.red0Call)
      hence red'': "P \<turnstile>0 \<langle>ex/exs,h2\<rangle> -\<epsilon>\<rightarrow> \<langle>(blocks (pns, Us, vs, body), [this \<mapsto> Addr a])/ex # exs,h2\<rangle>" by simp
      let ?ex' = "(blocks (pns, Us, vs, body), [this \<mapsto> Addr a])"
      from red' call notsynth have "h2 = h1'" "snd ex' = snd ex" "ta = \<epsilon>"
	by(auto dest: is_call_red_state_unchanged)
      moreover
      from ha is_call_red_inline_callD[OF wwf sees red' call] notsynth
      have "fst ex' = inline_call {this:Class D=\<lfloor>Addr a\<rfloor>; blocks (pns, Us, vs, body)}\<^bsub>True\<^esub> (fst ex)" by(simp)
      with fold' sees ha `h1' = h2` `snd ex' = snd ex` call
      have "fold_exs P h1' ?ex' (ex # exs) = (e1', x1')"
	by(cases ex')(simp)
      moreover from wf_state red'' have "wf_state h2 ?ex' (ex # exs)"
	by -(rule red0_preserves_wf_state[OF wwf])
      moreover from sees have "noRetBlock body"
	by(auto dest!: sees_wf_mdecl[OF wf] simp add: wf_mdecl_def intro: WT_noRetBlock)
      ultimately have "bisim_red_red0 P ((e1', x1'), h1') ((?ex', ex # exs), h1')" 
	using nrb nrbs length call ha by(auto simp add: noRetBlock_blocks)
      with red'' `ta = \<epsilon>` `h1' = h2` show ?thesis by(fastsimp)
    qed
  next
    case True
    { assume "exs = []"
      with fold red True have False by(auto elim!: final.cases) }
    then obtain e x Exs where exs: "exs = (e, x) # Exs" by(cases exs, auto)
    with wf_state obtain a M vs arrobj
      where call: "call e = \<lfloor>(a, M, vs)\<rfloor>"
      and ha: "h2 a = \<lfloor>arrobj\<rfloor>" by(fastsimp)
    let ?T = "Class (fst (method P (case arrobj of (Obj C fs) \<Rightarrow> C | _ \<Rightarrow> arbitrary) M))"
    from call ha fold[symmetric] exs heap
    have fold': "fold_exs P h1 (inline_call {this:?T=snd ex this; fst ex}\<^bsub>True\<^esub> e, x) Exs = (e1, x1)"
      (is "?fold = _") by(simp)
    with red have red': "P \<turnstile> \<langle>fst ?fold, (h1, snd ?fold)\<rangle> -ta\<rightarrow> \<langle>e1', (h1', x1')\<rangle>" by simp
    moreover 
    from call have "fv (inline_call {this:?T=snd ex this; fst ex}\<^bsub>True\<^esub> e) \<subseteq> fv e \<union> fv {this:?T=snd ex this; fst ex}\<^bsub>True\<^esub>"
      by-(rule fv_inline_call)
    with True have "fv (inline_call {this:?T=snd ex this; fst ex}\<^bsub>True\<^esub> e) \<subseteq> fv e" by(auto del: subsetI)
    with wf_state exs have "wf_state h2 (inline_call {this:?T=snd ex this; fst ex}\<^bsub>True\<^esub> e, x) Exs"
      by(auto del: subsetI)
    moreover from call have "\<not> final (inline_call {this:?T=snd ex this; fst ex}\<^bsub>True\<^esub> e)"
      by(auto elim!: final.cases)
    ultimately obtain e' x' 
      where fold'': "fold_exs P h1' (e', x') Exs = (e1', x1')"
      and red: "P \<turnstile> \<langle>inline_call {this:?T=snd ex this; fst ex}\<^bsub>True\<^esub> e, (h1, x)\<rangle> -ta\<rightarrow> \<langle>e',(h1', x')\<rangle>"
      using red_fold_exs'[OF wwf red'] heap exs by(auto)
    from red_inline_call_Block_final(1)[OF True red call]
    have "e' = inline_call (fst ex) e" "h1 = h1'" "x = x'" "ta = \<epsilon>" by auto
    hence "fold_exs P h1' (inline_call (fst ex) e, x) Exs = (e1', x1')" 
      using fold''[symmetric] by(simp)
    moreover  from exs `h1 = h1'` call True
    have red'': "P \<turnstile>0 \<langle>ex / exs, h1\<rangle> -\<epsilon>\<rightarrow> \<langle>(inline_call (fst ex) e, x)/Exs, h1'\<rangle>"
      by(cases ex, auto intro: red0Return)
    moreover with wf_state heap have "wf_state h1' (inline_call (fst ex) e, x) Exs"
      by-(drule red0_preserves_wf_state[OF wwf], simp)
    moreover from nrb nrbs exs have "noRetBlock (inline_call (fst ex) e)" by(auto intro: noRetBlock_inline_call)
    ultimately have "bisim_red_red0 P ((e1', x1'), h1') (((inline_call (fst ex) e, x), Exs), h1')"
      using heap `h1 = h1'` exs nrbs by(auto)
    with red'' `ta = \<epsilon>` `h1 = h1'` heap show ?thesis by(fastsimp)
  qed
  thus "\<exists>s2' ta2. mred0 P s2 ta2 s2' \<and> bisim_red_red0 P s1' s2' \<and> ta_bisim (bisim_red_red0 P) ta ta2"
    unfolding `s1 = ((e1, x1), h1)` `s1' = ((e1', x1'), h1')` `s2 = ((ex, exs), h2)` by auto blast
next
  fix s1 s2 ta' s2'
  assume "bisim_red_red0 P s1 s2" "mred0 P s2 ta' s2'"
  moreover obtain e1 h1 x1 where "s1 = ((e1, x1), h1)" by(cases s1, auto)
  moreover obtain ex exs h2 where "s2 = ((ex, exs), h2)" by(cases s2, auto)
  moreover obtain ex' exs' h2' where "s2' = ((ex', exs'), h2')" by(cases s2', auto)
  ultimately have bisim: "bisim_red_red0 P ((e1, x1), h1) ((ex, exs), h2)"
    and red: "P \<turnstile>0 \<langle>ex/exs, h2\<rangle> -ta'\<rightarrow> \<langle>ex'/exs', h2'\<rangle>" by(auto)
  from bisim have heap: "h2 = h1"
    and fold: "(e1, x1) = fold_exs P h1 ex exs"
    and wf_state: "wf_state h2 ex exs"
    and nrb: "noRetBlock (fst ex)"
    and nrbs: "noRetBlocks (map fst exs)"
    by(auto elim!: bisim_red_red0.cases del: wf_state.cases)
  note wwf = wf_prog_wwf_prog[OF wf]
  from red wf_state have wf_state': "wf_state h2' ex' exs'"
    by(rule red0_preserves_wf_state[OF wwf])
  from red have "\<exists>ta e1' h1' x1'. ta_bisim (bisim_red_red0 P) ta ta' \<and> 
                                 P \<turnstile> \<langle>e1, (h1, x1)\<rangle> -ta\<rightarrow> \<langle>e1', (h1', x1')\<rangle> \<and>
                                 bisim_red_red0 P ((e1', x1'), h1') ((ex', exs'), h2')"
  proof(induct rule: red0.cases)
    case (red0Red e'' h'' x'' ta'' e''' h''' x''' exs'')
    hence red': "extTA2J0 P,P \<turnstile> \<langle>fst ex, (h2, snd ex)\<rangle> -ta''\<rightarrow> \<langle>fst ex', (h2', snd ex')\<rangle>" by(auto)
    from red0_red_tabisim0[OF wwf red'] obtain ta'''
      where red': "P \<turnstile> \<langle>fst ex,(h2, snd ex)\<rangle> -ta'''\<rightarrow> \<langle>fst ex',(h2', snd ex')\<rangle>"
      and tab: "ta_bisim0 P ta''' ta''" by blast
    from heap red_fold_exs[OF wwf red', simplified, OF wf_state]
    have "P \<turnstile> \<langle>fst (fold_exs P h1 ex exs), (h1, snd (fold_exs P h1 ex exs))\<rangle>
          -ta'''\<rightarrow> \<langle>fst (fold_exs P h2' ex' exs),(h2', snd (fold_exs P h2' ex' exs))\<rangle>" by simp
    with fold[symmetric]
    have "P \<turnstile> \<langle>e1, (h1, x1)\<rangle> -ta'''\<rightarrow> \<langle>fst (fold_exs P h2' ex' exs), (h2', snd (fold_exs P h2' ex' exs))\<rangle>" by(simp)
    moreover from wf tab have "ta_bisim (bisim_red_red0 P) ta''' ta'"
      unfolding `ta' = ta''` by(rule ta_bisim0_bisim_red_red0)
    moreover from red' `\<forall>aMvs. call e'' = \<lfloor>aMvs\<rfloor> \<longrightarrow> synthesized_call P h'' aMvs` nrb `ex = (e'', x'')` `h2 = h''`
    have "noRetBlock (fst ex')" by(auto intro: no_call_red_preserves_noRetBlock[OF wf])
    hence "bisim_red_red0 P ((fst (fold_exs P h2' ex' exs), snd (fold_exs P h2' ex' exs)), h2') ((ex', exs), h2')"
      using red0Red wf_state' nrb nrbs unfolding `h2' = h'''` by -(rule bisim_red_red0.intros, auto)
    ultimately show ?thesis using `exs = exs''` `exs' = exs''` by(fastsimp)
  next
    case (red0Call e a M vs h C fs Us U pns body D x exs'')
    note sees = `P \<turnstile> C sees M: Us\<rightarrow>U = (pns, body) in D`
    note ha = `h a = \<lfloor>Obj C fs\<rfloor>`
    note call = `call e = \<lfloor>(a, M, vs)\<rfloor>`
    note length = `length vs = length pns` `length Us = length pns`
    from is_call_red_inline_call(1)[OF wf sees length call, of "(h, x)"] ha
    have red': "P \<turnstile> \<langle>e,(h, x)\<rangle> -\<epsilon>\<rightarrow> \<langle>inline_call ({this:Class D=\<lfloor>Addr a\<rfloor>; blocks (pns, Us, vs, body)}\<^bsub>True\<^esub>) e, (h, x)\<rangle>" by auto 
    let ?inline = "inline_call ({this:Class D=\<lfloor>Addr a\<rfloor>; blocks (pns, Us, vs, body)}\<^bsub>True\<^esub>) e"
    from red_fold_exs[OF wwf red', of exs] wf_state `ex = (e, x)` heap `h2 = h` `h2' = h`
    have "P \<turnstile> \<langle>fst (fold_exs P h (e, x) exs), (h, snd (fold_exs P h (e, x) exs))\<rangle> 
          -\<epsilon>\<rightarrow> \<langle>fst (fold_exs P h (?inline, x) exs), (h, snd (fold_exs P h (?inline, x) exs))\<rangle>" by auto
    with sees ha call `exs' = (e, x) # exs''` `ex' = (blocks (pns, Us, vs, body), [this \<mapsto> Addr a])` `exs = exs''`
    have "P \<turnstile> \<langle>fst (fold_exs P h (e, x) exs), (h, snd (fold_exs P h (e, x) exs))\<rangle> 
          -\<epsilon>\<rightarrow> \<langle>fst (fold_exs P h ex' exs'), (h, snd (fold_exs P h ex' exs'))\<rangle>" by(simp)
    moreover from sees have nrbbody: "noRetBlock body"
	by(auto dest!: sees_wf_mdecl[OF wf] simp add: wf_mdecl_def intro: WT_noRetBlock)
    from red0Call fold have fold': "fold_exs P h ex' exs' = fold_exs P h (?inline, x) exs" by(simp)
    with wf_state' heap `h2 = h` `h2' = h` `exs' = (e, x) # exs''` `exs = exs''` `ex = (e, x)` call ha nrb nrbs
      `ex' = (blocks (pns, Us, vs, body), [this \<mapsto> Addr a])` length nrbbody
    have "bisim_red_red0 P ((fst (fold_exs P h ex' exs'), snd (fold_exs P h ex' exs')), h2') ((ex', exs'), h2')"
      by -(rule bisim_red_red0.intros, auto simp add: noRetBlock_blocks)
    ultimately show ?thesis using `ta' = \<epsilon>` `h2 = h` heap `h2' = h` `ex = (e, x)`
      `ex' = (blocks (pns, Us, vs, body), [this \<mapsto> Addr a])`
      unfolding fold[symmetric, simplified `ex = (e, x)` `h2 = h1`[symmetric] `h2 = h`] fst_conv snd_conv
      apply -
      apply(rule_tac x="\<epsilon>" in exI)
      apply(rule_tac x="fst (fold_exs P h ex' exs')" in exI)
      apply(rule_tac x="h" in exI)
      apply(rule_tac x="snd (fold_exs P h ex' exs')" in exI)
      by(auto)
  next
    case (red0Return e aMvs e' x' x exs'' h)
    obtain a M vs where [simp]: "aMvs = (a, M, vs)" by(cases aMvs, auto)
    with `call e = \<lfloor>aMvs\<rfloor>` have call: "call e = \<lfloor>(a, M, vs)\<rfloor>" by simp
    note fin = `final e'`
    from call wf_state `exs = (e, x) # exs''` heap `h2 = h`
    obtain arrobj where arrobj: "h a = \<lfloor>arrobj\<rfloor>" by auto
    let ?T = "Class (fst (method P (case arrobj of (Obj C fs) \<Rightarrow> C | _ \<Rightarrow> arbitrary) M))"
    from `exs = (e, x) # exs''` call arrobj `exs' = exs''` `ex = (e', x')`
    have fold': "fold_exs P h ex exs = fold_exs P h (inline_call {this:?T=x' this; e'}\<^bsub>True\<^esub> e, x) exs'" by(simp)
    from red0Return red fin
    have "P \<turnstile> \<langle>inline_call {this:?T=x' this; e'}\<^bsub>True\<^esub> e, (h, x)\<rangle> -\<epsilon>\<rightarrow> \<langle>inline_call e' e, (h, x)\<rangle>"
      by -(rule red0_return_inline_call, fastsimp)
    moreover from call have "fv (inline_call {this:?T=x' this; e'}\<^bsub>True\<^esub> e) \<subseteq> fv e \<union> fv {this:?T=x' this; e'}\<^bsub>True\<^esub>"
      by(rule fv_inline_call)
    with wf_state red0Return have "fv (inline_call {this:?T=x' this; e'}\<^bsub>True\<^esub> e) \<subseteq> fv e" by(auto del: subsetI)
    with wf_state red0Return have "wf_state h (inline_call {this:?T=x' this; e'}\<^bsub>True\<^esub> e, x) exs''" by(auto del: subsetI)
    ultimately have "P \<turnstile> \<langle>fst (fold_exs P h (inline_call {this:?T=x' this; e'}\<^bsub>True\<^esub> e, x) exs''), (h, snd (fold_exs P h (inline_call {this:?T=x' this; e'}\<^bsub>True\<^esub> e, x) exs''))\<rangle> -\<epsilon>\<rightarrow> \<langle>fst (fold_exs P h (inline_call e' e, x) exs''), (h, snd (fold_exs P h (inline_call e' e, x) exs''))\<rangle>"
      by(rule red_fold_exs[OF wwf])
    hence "P \<turnstile> \<langle>fst (fold_exs P h ex exs), (h, snd (fold_exs P h ex exs))\<rangle> -\<epsilon>\<rightarrow> \<langle>fst (fold_exs P h (inline_call e' e, x) exs'), (h, snd (fold_exs P h (inline_call e' e, x) exs'))\<rangle>"
      using `h2 = h` `h2' = h` `ex = (e', x')` `ex' = (inline_call e' e, x)` `exs = (e, x) # exs''` `exs' = exs''` heap
      unfolding fold' by simp
    moreover from nrbs `ex' = (inline_call e' e, x)` `final e'` `exs = (e, x) # exs''`
    have "noRetBlock (fst ex')" by(auto intro: noRetBlock_inline_call elim!: final.cases)
    with red0Return wf_state' heap call arrobj nrbs
    have "bisim_red_red0 P ((fst (fold_exs P h (inline_call e' e, x) exs'), snd (fold_exs P h (inline_call e' e, x) exs')), h) ((ex', exs'), h)"
      by-(rule bisim_red_red0.intros, auto)
    ultimately show ?thesis using `ta' = \<epsilon>` fold[symmetric] `h2 = h` heap `h2' = h`
      apply -
      apply(rule_tac x="\<epsilon>" in exI)
      apply(rule_tac x="fst (fold_exs P h (inline_call e' e, x) exs')" in exI)
      apply(rule_tac x="h" in exI)
      apply(rule_tac x="snd (fold_exs P h (inline_call e' e, x) exs')" in exI)
      by(simp)
  qed
  thus "\<exists>s1' ta1. mred P s1 ta1 s1' \<and> bisim_red_red0 P s1' s2' \<and> ta_bisim (bisim_red_red0 P) ta1 ta'"
    unfolding `s1 = ((e1, x1), h1)` `s2 = ((ex, exs), h2)` `s2' = ((ex', exs'), h2')` by auto blast
qed

end