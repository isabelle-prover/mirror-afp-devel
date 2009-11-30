(*  Title:      JinjaThreads/Compiler/J0Bisim.thy
    Author:     Andreas Lochbihler
*)

header {*
  \isaheader{Bisimulation proof for between Jinja small step semantics with and without callstacks for single threads}
*}

theory J0Bisim imports J0 "../J/JWellForm" "../J/Threaded" "../Common/ExternalCallWF" begin

primrec fold_es :: "expr \<Rightarrow> expr list \<Rightarrow> expr" where
  "fold_es e [] = e"
| "fold_es e (e' # es) = fold_es (inline_call e e') es"

lemma fold_es_append [simp]:
  "fold_es e (es @ es') = fold_es (fold_es e es) es'"
by(induct es arbitrary: e, auto)

lemma fold_es_conv_foldl:
  "fold_es e es = foldl inline_call e es"
by(induct es arbitrary: e) simp_all

definition is_call :: "('a, 'b) exp \<Rightarrow> bool"
where "is_call e = (call e \<noteq> None)"

inductive  wf_state :: "expr \<Rightarrow> expr list \<Rightarrow> bool"
  for e :: "expr" and es :: "expr list"
  where
  "\<lbrakk> fvs (e # es) = {}; list_all is_call es; 
    final (last (e # es)) \<or> (\<exists>v M vs. last (e # es) = Val v\<bullet>M(map Val vs)); es = [] \<Longrightarrow> final e  \<rbrakk>
   \<Longrightarrow> wf_state e es"

declare wf_state.intros [intro!]
declare wf_state.cases [elim!]

lemma wf_state_iff [code]:
  "wf_state e es \<longleftrightarrow> fvs (e # es) = {} \<and> list_all is_call es \<and> (final (last (e # es)) \<or> (\<exists>v M vs. last (e # es) = Val v\<bullet>M(map Val vs))) \<and> (es = [] \<longrightarrow> final e)"
by(blast)

lemma red0_preserves_wf_state:
  assumes wf: "wwf_J_prog P"
  and red: "P \<turnstile>0 \<langle>e / es, h\<rangle> -ta\<rightarrow> \<langle>e' / es', h'\<rangle>"
  and wf_state: "wf_state e es"
  shows "wf_state e' es'"
using wf_state
proof(cases)
  assume "fvs (e # es) = {}" and icl: "list_all is_call es"
    and tb: "final (last (e # es)) \<or> (\<exists>v M vs. last (e # es) = Val v\<bullet>M(map Val vs))"
    and esNil: "es = [] \<Longrightarrow> final e"
  hence fv: "fv e = {}" "fvs es = {}" by auto
  show ?thesis
  proof
    from red show "fvs (e' # es') = {}"
    proof cases
      case (red0Red E H ta E' H' xs' ES)
      hence [simp]: "ES = es" "es' = es" "E = e" "E' = e'" "H = h" "H' = h'"
	and red: "extTA2J0 P,P \<turnstile> \<langle>e,(h, empty)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>" by auto
      from red_fv_subset[OF wf red] fv have "fv e' = {}" by auto
      with fv show ?thesis by simp
    next
      case (red0Call E a M vs H C fs Ts T pns body D ES)
      hence [simp]: "E = e" "ES = es" "H = h" "ta = \<epsilon>"
	"e' = blocks (this#pns, Class D#Ts, Addr a#vs, body)"
	"es' = e # es" "h' = h"
	and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D" by auto
      from sees_wf_mdecl[OF wf sees]
      have "fv body \<subseteq> insert this (set pns)" "length Ts = length pns" by(simp_all add: wf_mdecl_def)
      thus ?thesis using fv `length vs = length pns` by auto
    next
      case (red0Return E' E ES H)
      with icl have "is_call E" by simp
      then obtain aMvs where "call E = \<lfloor>aMvs\<rfloor>" by(auto simp add: is_call_def)
      with fv_inline_call[OF this, of E'] red0Return
      show ?thesis using fv by auto
    qed
  next
    from red icl show "list_all is_call es'"
      by cases(simp_all add: is_call_def)
  next
    from red icl tb show "final (last (e' # es')) \<or> (\<exists>v M vs. last (e' # es') = Val v\<bullet>M(map Val vs))"
    proof cases
      case red0Return with tb icl show ?thesis
	by(fastsimp elim!: final.cases simp add: is_call_def)
    next
      case red0Red thus ?thesis using tb esNil by auto
    next
      case red0Call
      with tb show ?thesis by(auto)
    qed
  next
    assume [simp]: "es' = []"
    from red esNil tb icl show "final e'"
      by cases(auto simp add: is_call_def)
  qed
qed

inductive bisim_red_red0 :: "(expr \<times> locals) \<times> heap \<Rightarrow> (expr \<times> expr list) \<times> heap \<Rightarrow> bool"
  where
  "\<lbrakk> e' = fold_es e es; wf_state e es \<rbrakk>
  \<Longrightarrow> bisim_red_red0 ((e', empty), h) ((e, es), h)"

declare bisim_red_red0.intros[intro]

abbreviation ta_bisim0 :: "J_thread_action \<Rightarrow> J0_thread_action \<Rightarrow> bool"
where "ta_bisim0 \<equiv> ta_bisim bisim_red_red0"

lemma new_thread_bisim0_extNTA2J_extNTA2J0:
  assumes wf: "wwf_J_prog P"
  and red: "P \<turnstile> \<langle>a'\<bullet>M'(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  and nt: "NewThread t CMa m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  and ha': "h a' \<noteq> None"
  shows "bisim_red_red0 (extNTA2J P CMa, m) (extNTA2J0 P CMa, m)"
proof -
  obtain C M a where CMa [simp]: "CMa = (C, M, a)" by(cases CMa)
  from red nt have [simp]: "m = h'" by(rule red_ext_new_thread_heap)
  from red_external_new_thread_sees[OF wf red nt[unfolded CMa], OF ha']
  obtain fs T pns body D where h'a: "h' a = \<lfloor>Obj C fs\<rfloor>"
    and sees: "P \<turnstile> C sees M: []\<rightarrow>T = (pns, body) in D" by auto
  from sees_wf_mdecl[OF wf sees] have "fv body \<subseteq> {this}" by(auto simp add: wf_mdecl_def)
  with red nt h'a sees show ?thesis by(fastsimp simp add: is_call_def intro: bisim_red_red0.intros)
qed

lemma obs_a_extTA2J_eq_obs_a_extTA2J0 [simp]: "\<lbrace>extTA2J P ta\<rbrace>\<^bsub>o\<^esub> = \<lbrace>extTA2J0 P ta\<rbrace>\<^bsub>o\<^esub>"
by(cases ta) simp

lemma ta_bisim0_extNTA2J_extNTA2J0:
  "\<lbrakk> wwf_J_prog P; P \<turnstile> \<langle>a'\<bullet>M'(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; h a' \<noteq> None \<rbrakk>
  \<Longrightarrow> ta_bisim0 (extTA2J P ta) (extTA2J0 P ta)"
apply(auto simp add: ta_bisim_def intro!: list_all2_all_nthI)
apply(case_tac "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> ! n")
apply(simp_all)
apply(erule (1) new_thread_bisim0_extNTA2J_extNTA2J0)
apply(auto simp add: in_set_conv_nth)
done

lemma assumes wf: "wwf_J_prog P"
  shows red_red0_tabisim0:
  "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> \<exists>ta'. extTA2J0 P,P \<turnstile> \<langle>e, s\<rangle> -ta'\<rightarrow> \<langle>e', s'\<rangle> \<and> ta_bisim0 ta ta'"
  and reds_reds0_tabisim0:
  "P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> \<exists>ta'. extTA2J0 P,P \<turnstile> \<langle>es, s\<rangle> [-ta'\<rightarrow>] \<langle>es', s'\<rangle> \<and> ta_bisim0 ta ta'"
proof(induct rule: red_reds.inducts)
  case (RedCallExternal s a T M vs ta va h' ta' e' s')
  note red = `P \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>`
  note T = `typeof\<^bsub>hp s\<^esub> (Addr a) = \<lfloor>T\<rfloor>`
  from T `is_external_call P T M` red
  have "extTA2J0 P,P \<turnstile> \<langle>addr a\<bullet>M(map Val vs),s\<rangle> -extTA2J0 P ta\<rightarrow> \<langle>e',(h', lcl s)\<rangle>"
    by(rule red_reds.RedCallExternal)(simp_all add: `e' = extRet2J va`)
  moreover from `ta' = extTA2J P ta` T red wf
  have "ta_bisim0 ta' (extTA2J0 P ta)" by(auto intro: ta_bisim0_extNTA2J_extNTA2J0)
  ultimately show ?case unfolding `s' = (h', lcl s)` by blast
next
  case RedTryFail thus ?case by(force intro: red_reds.RedTryFail)
qed(fastsimp intro: red_reds.intros simp add: ta_bisim_def)+

lemma assumes wf: "wwf_J_prog P"
  shows red0_red_tabisim0:
  "extTA2J0 P,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> \<exists>ta'. P \<turnstile> \<langle>e, s\<rangle> -ta'\<rightarrow> \<langle>e', s'\<rangle> \<and> ta_bisim0 ta' ta"
  and reds0_reds_tabisim0:
  "extTA2J0 P,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> \<exists>ta'. P \<turnstile> \<langle>es, s\<rangle> [-ta'\<rightarrow>] \<langle>es', s'\<rangle> \<and> ta_bisim0 ta' ta"
proof(induct rule: red_reds.inducts)
  case (RedCallExternal s a T M vs ta va h' ta' e' s')
  note red = `P \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>`
  note T = `typeof\<^bsub>hp s\<^esub> (Addr a) = \<lfloor>T\<rfloor>`
  from T `is_external_call P T M` red
  have "P \<turnstile> \<langle>addr a\<bullet>M(map Val vs),s\<rangle> -extTA2J P ta\<rightarrow> \<langle>e',(h', lcl s)\<rangle>"
    by(rule red_reds.RedCallExternal)(simp_all add: `e' = extRet2J va`)
  moreover from `ta' = extTA2J0 P ta` T red wf
  have "ta_bisim0 (extTA2J P ta) ta'" by(auto intro: ta_bisim0_extNTA2J_extNTA2J0)
  ultimately show ?case unfolding `s' = (h', lcl s)` by blast
next
  case RedTryFail thus ?case by(force intro: red_reds.RedTryFail)
qed(fastsimp intro: red_reds.intros simp add: ta_bisim_def)+

lemma red_inline_call_red:
  assumes red: "P \<turnstile> \<langle>e, (h, empty)\<rangle> -ta\<rightarrow> \<langle>e', (h', empty)\<rangle>"
  shows "call E = \<lfloor>aMvs\<rfloor> \<Longrightarrow> P \<turnstile> \<langle>inline_call e E, (h, x)\<rangle> -ta\<rightarrow> \<langle>inline_call e' E, (h', x)\<rangle>"
  (is "_ \<Longrightarrow> ?concl E x")

  and
  "calls Es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> P \<turnstile> \<langle>inline_calls e Es, (h, x)\<rangle> [-ta\<rightarrow>] \<langle>inline_calls e' Es, (h', x)\<rangle>"
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
    from red_lcl_add[OF red, where ?l0.0=x]
    have "P \<turnstile> \<langle>e,(h, x)\<rangle> -ta\<rightarrow> \<langle>e', (h', x)\<rangle>" by simp
    with Call show ?case by(fastsimp dest: BlockRed)
  qed
next
  case (Block V T' vo exp x)
  note IH = `\<And>x. call exp = \<lfloor>aMvs\<rfloor> \<Longrightarrow> ?concl exp x`
  from IH[of "x(V := vo)"] `call {V:T'=vo; exp} = \<lfloor>aMvs\<rfloor>`
  show ?case by(clarsimp simp del: fun_upd_apply)(drule BlockRed, auto)
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
  shows "\<lbrakk> call e = \<lfloor>(a, M, vs)\<rfloor>; hp s a = \<lfloor>Obj C fs\<rfloor> \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>inline_call (blocks (this#pns, Class D#Us, Addr a#vs, body)) e, s\<rangle>"
  (is "_ \<Longrightarrow> _ \<Longrightarrow> ?red e s")
  and "\<lbrakk> calls es = \<lfloor>(a, M, vs)\<rfloor>; hp s a = \<lfloor>Obj C fs\<rfloor> \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>es, s\<rangle> [-\<epsilon>\<rightarrow>] \<langle>inline_calls (blocks (this#pns, Class D#Us, Addr a#vs, body)) es, s\<rangle>"
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
    from `P \<turnstile> C sees M:Us\<rightarrow>U = (pns, body) in D` have "\<not> is_external_call P (Class C) M"
      by(auto dest: external_call_not_sees_method[OF wf_prog])
    from Call RedCall[where s=s, simplified, OF `hp s a = \<lfloor>Obj C fs\<rfloor>` this `P \<turnstile> C sees M:Us\<rightarrow>U = (pns, body) in D` `length vs = length pns` `length Us = length pns`] 
    show ?thesis by(simp)
  qed
next
  case (Block V ty vo exp s)
  note IH = `\<And>s. \<lbrakk>call exp = \<lfloor>(a, M, vs)\<rfloor>; hp s a = \<lfloor>Obj C fs\<rfloor> \<rbrakk> \<Longrightarrow> ?red exp s`
  from `call {V:ty=vo; exp} = \<lfloor>(a, M, vs)\<rfloor>` IH[of "(hp s, (lcl s)(V := vo))"] `hp s a = \<lfloor>Obj C fs\<rfloor>`
  show ?case by(cases s, simp del: fun_upd_apply)(drule red_reds.BlockRed, simp)
qed(fastsimp intro: red_reds.intros)+


lemma red_inline_call_red':
  assumes fv: "fv ee = {}"
  and eefin: "\<not> final ee"
  shows "\<lbrakk> call E = \<lfloor>aMvs\<rfloor>; P \<turnstile> \<langle>inline_call ee E, (h, x)\<rangle> -ta\<rightarrow> \<langle>E', (h', x')\<rangle> \<rbrakk> 
         \<Longrightarrow> \<exists>ee'. E' = inline_call ee' E \<and> P \<turnstile> \<langle>ee, (h, empty)\<rangle> -ta\<rightarrow> \<langle>ee', (h', empty)\<rangle> \<and> x = x'"
  (is "\<lbrakk> _; _ \<rbrakk> \<Longrightarrow> ?concl E E' x x'")
  and   "\<lbrakk> calls Es = \<lfloor>aMvs\<rfloor>; P \<turnstile> \<langle>inline_calls ee Es, (h, x)\<rangle> [-ta\<rightarrow>] \<langle>Es', (h', x')\<rangle> \<rbrakk> 
         \<Longrightarrow> \<exists>ee'. Es' = inline_calls ee' Es \<and> P \<turnstile> \<langle>ee, (h, empty)\<rangle> -ta\<rightarrow> \<langle>ee', (h', empty)\<rangle> \<and> x = x'"
  (is "\<lbrakk> _; _ \<rbrakk> \<Longrightarrow> ?concls Es Es' x x'")
proof(induct E and Es arbitrary: E' x x' and Es' x x')
  case new thus ?case by simp
next
  case (newArray T exp E' x x')
  thus ?case using eefin by(auto elim!: red_cases)
next
  case Cast thus ?case using eefin by(auto elim!:red_cases) 
next
  case Val thus ?case by simp
next
  case Var thus ?case by simp
next
  case LAss
  thus ?case using eefin by(auto elim!: red_cases)
next
  case BinOp
  thus ?case using eefin by(auto elim!: red_cases split: split_if_asm)
next
  case AAcc
  thus ?case using eefin by(auto elim!: red_cases split: split_if_asm)
next
  case AAss thus ?case using eefin by(auto elim!: red_cases split: split_if_asm)
next
  case ALen thus ?case using eefin by(auto elim!: red_cases split: split_if_asm)
next
  case FAcc thus ?case using eefin by(auto elim!: red_cases)
next
  case FAss thus ?case using eefin by(auto elim!: red_cases split: split_if_asm)
next
  case (Call obj M pns E' x x')
  note IHobj = `\<And>x E' x'. \<lbrakk>call obj = \<lfloor>aMvs\<rfloor>; P \<turnstile> \<langle>inline_call ee obj,(h, x)\<rangle> -ta\<rightarrow> \<langle>E',(h', x')\<rangle>\<rbrakk>
                \<Longrightarrow> ?concl obj E' x x'`
  note IHpns = `\<And>Es' x x'. \<lbrakk>calls pns = \<lfloor>aMvs\<rfloor>; P \<turnstile> \<langle>inline_calls ee pns,(h, x)\<rangle> [-ta\<rightarrow>] \<langle>Es',(h', x')\<rangle>\<rbrakk>
               \<Longrightarrow> ?concls pns Es' x x'`
  note red = `P \<turnstile> \<langle>inline_call ee (obj\<bullet>M(pns)),(h, x)\<rangle> -ta\<rightarrow>  \<langle>E',(h', x')\<rangle>`
  obtain a M' vs where [simp]: "aMvs = (a, M', vs)" by(cases aMvs, auto)
  from `call (obj\<bullet>M(pns)) = \<lfloor>aMvs\<rfloor>` have "call (obj\<bullet>M(pns)) = \<lfloor>(a,M',vs)\<rfloor>" by simp
  thus ?case
  proof(cases rule: call_callE)
    case CallObj
    hence "\<not> is_val obj" by auto
    with red CallObj eefin obtain obj' where "E' = obj'\<bullet>M(pns)" 
      and red': "P \<turnstile> \<langle>inline_call ee obj,(h, x)\<rangle> -ta\<rightarrow> \<langle>obj',(h', x')\<rangle>"
      by(auto elim!: red_cases)
    from IHobj[OF _ red'] CallObj obtain ee' 
      where "inline_call ee' obj = obj'" "x = x'"
      and "P \<turnstile> \<langle>ee,(h, empty)\<rangle> -ta\<rightarrow> \<langle>ee',(h', empty)\<rangle>" by(auto simp del: fun_upd_apply)
    with `E' = obj'\<bullet>M(pns)` CallObj red' show ?thesis by(fastsimp simp del: fun_upd_apply)
  next
    case (CallParams v'')
    hence "\<not> is_vals pns" by auto
    with red CallParams eefin obtain pns' where "E' = obj\<bullet>M(pns')" 
      and red': "P \<turnstile> \<langle>inline_calls ee pns,(h, x)\<rangle> [-ta\<rightarrow>] \<langle>pns',(h', x')\<rangle>"
      by(auto elim!: red_cases)
    from IHpns[OF _ red'] CallParams obtain ee' 
      where "inline_calls ee' pns = pns'" "x = x'"
      and "P \<turnstile> \<langle>ee,(h, empty)\<rangle> -ta\<rightarrow> \<langle>ee',(h', empty)\<rangle>"
      by(auto simp del: fun_upd_apply)
    with `E' = obj\<bullet>M(pns')` CallParams red' `\<not> is_vals pns`
    show ?thesis by(auto simp del: fun_upd_apply)
  next
    case Call
    with red have red': "P \<turnstile> \<langle>ee,(h, x)\<rangle> -ta\<rightarrow> \<langle>E',(h', x')\<rangle>" by(auto)
    from red_lcl_sub[OF red', of "{}"] fv
    have "P \<turnstile> \<langle>ee,(h, empty)\<rangle> -ta\<rightarrow> \<langle>E',(h', empty)\<rangle>" by simp
    moreover have "x' = x"
    proof(rule ext)
      fix V
      from red_notfree_unchanged[OF red', of V] fv
      show "x' V = x V" by simp
    qed
    ultimately show ?thesis using Call by simp
  qed
next
  case (Block V ty voo exp E' x x')
  note IH = `\<And>x E' x'. \<lbrakk>call exp = \<lfloor>aMvs\<rfloor>; P \<turnstile> \<langle>inline_call ee exp,(h, x)\<rangle> -ta\<rightarrow> \<langle>E',(h', x')\<rangle>\<rbrakk>
            \<Longrightarrow> ?concl exp E' x x'`
  from `call {V:ty=voo; exp} = \<lfloor>aMvs\<rfloor>` have ic: "call exp = \<lfloor>aMvs\<rfloor>" by simp
  note red = `P \<turnstile> \<langle>inline_call ee {V:ty=voo; exp},(h, x)\<rangle> -ta\<rightarrow> \<langle>E',(h', x')\<rangle>`
  hence "P \<turnstile> \<langle>{V:ty=voo; inline_call ee exp},(h, x)\<rangle> -ta\<rightarrow> \<langle>E',(h', x')\<rangle>" by simp
  with ic eefin obtain exp' x'' where "E' = {V:ty=x'' V; exp'}"
    and red': "P \<turnstile> \<langle>inline_call ee exp,(h, fun_upd x V voo)\<rangle> -ta\<rightarrow> \<langle>exp',(h', x'')\<rangle>"
    and "x' = fun_upd x'' V (x V)"
    by -(erule red.cases,auto dest: inline_call_eq_Val)
  from IH[OF ic red'] obtain ee' vo' 
    where icl: "inline_call ee' exp = exp'" "x'' = fun_upd x V voo"
    and red'': "P \<turnstile> \<langle>ee,(h, empty)\<rangle> -ta\<rightarrow> \<langle>ee',(h', empty)\<rangle>" by blast
  from `x'' = fun_upd x V voo` have "x'' V = voo" by(simp add: expand_fun_eq)
  with icl red'' `E' = {V:ty=x'' V; exp'}` `x' = fun_upd x'' V (x V)` red'
  show ?case by(auto simp del: fun_upd_apply)
next
  case Synchronized thus ?case using eefin by(auto elim!: red_cases)
next
  case InSynchronized thus ?case using eefin by(auto elim!: red_cases)
next
  case Seq 
  thus ?case using eefin by(auto elim!: red_cases)
next
  case Cond thus ?case using eefin by(auto elim!: red_cases)
next
  case While thus ?case by simp
next
  case throw
  thus ?case using eefin by(auto elim!: red_cases)
next
  case TryCatch
  thus ?case using eefin by(auto elim!: red_cases)
next
  case Nil_exp thus ?case by simp
next
  case Cons_exp
  thus ?case using eefin by(auto elim!: reds_cases split: split_if_asm)
qed

lemma assumes wf: "wwf_J_prog P"
  and sees: "P \<turnstile> C sees M:Us\<rightarrow>U = (pns, body) in D"
  shows is_call_red_inline_callD:
        "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; call e = \<lfloor>(a, M, vs)\<rfloor>; hp s a = \<lfloor>Obj C fs\<rfloor>; \<not> synthesized_call P (hp s) (a, M, vs) \<rbrakk>
        \<Longrightarrow> e' = inline_call (blocks (this#pns, Class D#Us, Addr a#vs, body)) e"
  and is_calls_reds_inline_callsD:
        "\<lbrakk> P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; calls es = \<lfloor>(a, M, vs)\<rfloor>; hp s a = \<lfloor>Obj C fs\<rfloor>; \<not> synthesized_call P (hp s) (a, M, vs) \<rbrakk>
        \<Longrightarrow> es' = inline_calls (blocks (this#pns, Class D#Us, Addr a#vs, body)) es"
proof(induct rule: red_reds.inducts)
  case (RedCall s a' C' fs' M' Us' U' pns' body' D' vs')
  with sees show ?case by(auto dest: sees_method_fun)
next
  case RedCallExternal
  with sees show ?case by(auto dest: external_call_not_sees_method[OF wf])
next
  case (BlockRed e h x V vo ta e' h' x' T)
  from `call {V:T=vo; e} = \<lfloor>(a, M, vs)\<rfloor>` have "call e = \<lfloor>(a, M, vs)\<rfloor>" by simp
  with `P \<turnstile> \<langle>e,(h, x(V := vo))\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>` `\<not> synthesized_call P (hp (h, x)) (a, M, vs)`
  have "x(V := vo) = x'" by(auto dest: is_call_red_state_unchanged)
  hence "x' V = vo" by auto
  with BlockRed show ?case by(simp)
qed(fastsimp split: split_if_asm)+

lemma red_fold_exs:
  "\<lbrakk> P \<turnstile> \<langle>e,(h, empty)\<rangle> -ta\<rightarrow> \<langle>e',(h', empty)\<rangle>; fvs (e # es) = {}; list_all is_call es \<rbrakk>
  \<Longrightarrow>  P \<turnstile> \<langle>fold_es e es, (h, empty)\<rangle> -ta\<rightarrow> \<langle>fold_es e' es, (h', empty)\<rangle>"
  (is "\<lbrakk> _; _; _ \<rbrakk> \<Longrightarrow> ?concl e e' es")
proof(induct es arbitrary: e e')
  case Nil thus ?case by simp
next
  case (Cons E es)
  note IH = `\<And>e e'. \<lbrakk> P \<turnstile> \<langle>e,(h, empty)\<rangle> -ta\<rightarrow> \<langle>e',(h', empty)\<rangle>;
                      fvs (e # es) = {}; list_all is_call es \<rbrakk>
          \<Longrightarrow> ?concl e e' es`
  note icl = `list_all is_call (E # es)`
  note fvs = `fvs (e # E # es) = {}`
  note red = `P \<turnstile> \<langle>e,(h, empty)\<rangle> -ta\<rightarrow> \<langle>e',(h', empty)\<rangle>`
  from icl obtain a M vs arrobj where call: "call E = \<lfloor>(a, M, vs)\<rfloor>" 
    by(auto simp add: is_call_def)
  from red call have "P \<turnstile> \<langle>inline_call e E,(h, empty)\<rangle> -ta\<rightarrow> \<langle>inline_call e' E,(h', empty)\<rangle>"
    by(rule red_inline_call_red)
  hence "P \<turnstile> \<langle>fold_es (inline_call e E) es,(h, empty)\<rangle> -ta\<rightarrow>  \<langle>fold_es (inline_call e' E) es,(h', empty)\<rangle>"
  proof(rule IH)
    from fvs have "fv E = {}" "fv e = {}" by auto
    with fv_inline_call[OF call, of e]
    have "fv (inline_call e E) = {}" by auto
    thus "fvs (inline_call e E # es) = {}" using fvs by auto
  next
    from icl show "list_all is_call es" by simp
  qed
  thus ?case by simp
qed

lemma red_fold_exs':
  "\<lbrakk> P \<turnstile> \<langle>fold_es e es, (h, empty)\<rangle> -ta\<rightarrow> \<langle>e', (h', x')\<rangle>; 
    fvs (e # es) = {}; list_all is_call es;
    \<not> final e \<rbrakk>
  \<Longrightarrow> \<exists>E'. e' = fold_es E' es \<and> P \<turnstile> \<langle>e, (h, empty)\<rangle> -ta\<rightarrow> \<langle>E', (h', empty)\<rangle>"
  (is "\<lbrakk> ?red e es; _; _; _ \<rbrakk> \<Longrightarrow> ?concl e es")
proof(induct es arbitrary: e)
  case Nil
  note red = `P \<turnstile> \<langle>fold_es e [],(h, empty)\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>`
  hence red': "P \<turnstile> \<langle>e,(h, empty)\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>" by simp
  from red_dom_lcl[OF red'] `fvs [e] = {}`
  have "dom x' = {}" by safe auto
  hence [simp]: "x' = empty" by simp
  with red' show ?case by auto
next
  case (Cons E es)
  note IH = `\<And>e. \<lbrakk> P \<turnstile> \<langle>fold_es e es,(h, empty)\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>;
                   fvs (e # es) = {}; list_all is_call es; \<not> final e \<rbrakk>
            \<Longrightarrow> \<exists>E'. e' = fold_es E' es \<and> P \<turnstile> \<langle>e,(h, empty)\<rangle> -ta\<rightarrow> \<langle>E',(h', empty)\<rangle>`
  note red = `P \<turnstile> \<langle>fold_es e (E # es),(h, empty)\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>`
  note fvs = `fvs (e # E # es) = {}`
  note icl = `list_all is_call (E # es)`
  note nfin = `\<not> final e`
  from fvs have "fv e = {}" by simp
  from icl obtain a M vs where call: "call E = \<lfloor>(a, M, vs)\<rfloor>" by(auto simp add: is_call_def)
  from red have "P \<turnstile> \<langle>fold_es (inline_call e E) es,(h, empty)\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>" by simp
  hence "\<exists>E'. e' = fold_es E' es \<and> P \<turnstile> \<langle>inline_call e E,(h, empty)\<rangle> -ta\<rightarrow> \<langle>E',(h', empty)\<rangle>"
  proof(rule IH)
    from fvs fv_inline_call[OF call, of e]
    show "fvs (inline_call e E # es) = {}" by simp
  next
    from icl show "list_all is_call es" by simp
  next
    from nfin call show "\<not> final (inline_call e E)" by(auto elim!: final.cases)
  qed
  then obtain E' where e': "e' = fold_es E' es" 
    and red': "P \<turnstile> \<langle>inline_call e E,(h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>E',(h', empty)\<rangle>" by blast
  from fvs red_inline_call_red'(1)[OF _ nfin `call E = \<lfloor>(a, M, vs)\<rfloor>` red']
  obtain e' where "E' = inline_call e' E" "P \<turnstile> \<langle>e,(h, empty)\<rangle> -ta\<rightarrow> \<langle>e',(h', empty)\<rangle>" by auto
  thus ?case using e' by auto
qed

lemma fv_fold_es: "list_all is_call es \<Longrightarrow> fv (fold_es e es) \<subseteq> fvs (e # es)"
by(induct es arbitrary: e) (auto simp add: is_call_def dest: fv_inline_call)

lemma \<tau>Red0r_inline_call_not_final:
  "\<exists>e' es'. \<tau>Red0r P h (e, es) (e', es') \<and> (final e' \<longrightarrow> es' = []) \<and> fold_es e es = fold_es e' es'"
proof(induct es arbitrary: e)
  case Nil thus ?case by blast
next
  case (Cons e es E)
  show ?case
  proof(cases "final E")
    case True
    hence "\<tau>Red0 P h (E, e # es) (inline_call E e, es)" by(auto intro: red0Return)
    moreover from Cons[of "inline_call E e"] obtain e' es'
      where "\<tau>Red0r P h (inline_call E e, es) (e', es')" "final e' \<longrightarrow> es' = []"
      "fold_es (inline_call E e) es = fold_es e' es'" by blast
    ultimately show ?thesis unfolding fold_es.simps by(blast intro: converse_rtranclp_into_rtranclp)
  next
    case False thus ?thesis by blast
  qed
qed

lemma \<tau>Red0_preserves_wf_state:
  "\<lbrakk> wwf_J_prog P; \<tau>Red0 P h (e, es) (e', es'); wf_state e es \<rbrakk> \<Longrightarrow> wf_state e' es'"
by(auto del: wf_state.intros wf_state.cases intro: red0_preserves_wf_state)

lemma \<tau>Red0r_preserves_wf_state:
  assumes wf: "wwf_J_prog P"
  shows "\<lbrakk> \<tau>Red0r P h (e, es) (e', es'); wf_state e es \<rbrakk> \<Longrightarrow> wf_state e' es'"
by(induct rule: rtranclp_induct2)(blast intro: \<tau>Red0_preserves_wf_state[OF wf] del: wf_state.intros wf_state.cases)+

lemma \<tau>Red0t_preserves_wf_state:
  assumes wf: "wwf_J_prog P"
  shows "\<lbrakk> \<tau>Red0t P h (e, es) (e', es'); wf_state e es \<rbrakk> \<Longrightarrow> wf_state e' es'"
by(induct rule: tranclp_induct2)(blast intro: \<tau>Red0_preserves_wf_state[OF wf] del: wf_state.intros wf_state.cases)+

lemma assumes nfin: "\<not> final e'"
 shows inline_call_\<tau>move0_inv: "call e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> \<tau>move0 P h (inline_call e' e) = \<tau>move0 P h e'"
  and inline_calls_\<tau>moves0_inv: "calls es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> \<tau>moves0 P h (inline_calls e' es) = \<tau>move0 P h e'"
apply(induct e and es)
apply(insert nfin)
apply simp_all
apply auto
done

lemma fold_es_\<tau>move0_inv:
  "\<lbrakk> list_all is_call es; \<not> final e \<rbrakk> \<Longrightarrow> \<tau>move0 P h (fold_es e es) = \<tau>move0 P h e"
proof(induct es arbitrary: e)
  case Nil thus ?case by clarsimp
next
  case (Cons e es e'')
  note IH = `\<And>e. \<lbrakk> list_all is_call es; \<not> final e \<rbrakk> \<Longrightarrow> \<tau>move0 P h (fold_es e es) = \<tau>move0 P h e`
  from `list_all is_call (e # es)` obtain aMvs where calls: "list_all is_call es"
    and call: "call e = \<lfloor>aMvs\<rfloor>" by(auto simp add: is_call_def)
  note calls moreover
  from `\<not> final e''` call have "\<not> final (inline_call e'' e)" by(auto simp add: final_iff)
  ultimately have "\<tau>move0 P h (fold_es (inline_call e'' e) es) = \<tau>move0 P h (inline_call e'' e)" by(rule IH)
  also from call `\<not> final e''` have "\<dots> = \<tau>move0 P h e''" by(auto simp add: inline_call_\<tau>move0_inv)
  finally show ?case by simp
qed

lemma \<tau>Red0r_into_silent_moves:
  "\<tau>Red0r P h (e, es) (e', es') \<Longrightarrow> red0_\<tau>mthr.silent_moves P ((e, es), h) ((e', es'), h)"
by(induct rule: rtranclp_induct2)(fastsimp intro: \<tau>trsys.silent_move.intros elim!: rtranclp.rtrancl_into_rtrancl)+

lemma \<tau>Red0t_into_silent_movet:
  "\<tau>Red0t P h (e, es) (e', es') \<Longrightarrow> red0_\<tau>mthr.silent_movet P ((e, es), h) ((e', es'), h)"
by(induct rule: tranclp_induct2)(fastsimp intro: \<tau>trsys.silent_move.intros tranclp.r_into_trancl elim!: tranclp.trancl_into_trancl)+

lemma weak_bisimulation_measure_red_red0:
  assumes wf: "wwf_J_prog P"
  shows "delay_bisimulation_measure (mred P) (mred0 P) bisim_red_red0 ta_bisim0 (\<tau>MOVE P) (\<tau>MOVE0 P) (\<lambda>e e'. False) (\<lambda>((e, es), h) ((e, es'), h). length es < length es')"
proof
  show "wfP (\<lambda>e e'. False)" by auto
next
  have "wf {(x :: nat, y). x < y}" by(rule wf_less)
  hence "wf (inv_image {(x :: nat, y). x < y} (length o snd o fst))" by(rule wf_inv_image)
  also have "inv_image {(x :: nat, y). x < y} (length o snd o fst) = {(x, y). (\<lambda>((e, es), h) ((e, es'), h). length es < length es') x y}" by auto
  finally show "wfP (\<lambda>((e, es), h) ((e, es'), h). length es < length es')"
    unfolding wfP_def .
next
  fix s1 s2 s1'
  assume "bisim_red_red0 s1 s2" and "red_\<tau>mthr.silent_move P s1 s1'"
  moreover obtain e1 h1 x1 where s1: "s1 = ((e1, x1), h1)" by(cases s1, auto)
  moreover obtain e1' h1' x1' where s1': "s1' = ((e1', x1'), h1')" by(cases s1', auto)
  moreover obtain e es h2 where s2: "s2 = ((e, es), h2)" by(cases s2, auto)
  ultimately have bisim: "bisim_red_red0 ((e1, x1), h1) ((e, es), h2)"
    and red: "P \<turnstile> \<langle>e1, (h1, x1)\<rangle> -\<epsilon>\<rightarrow> \<langle>e1', (h1', x1')\<rangle>" 
    and \<tau>: "\<tau>move0 P h1 e1" by(auto elim: \<tau>trsys.silent_move.cases)
  from bisim have heap: "h1 = h2"
    and fold: "e1 = fold_es e es"
    and x1: "x1 = empty"
    and wf_state: "wf_state e es"
    by(auto elim!: bisim_red_red0.cases del: wf_state.cases)
  from \<tau>Red0r_inline_call_not_final[of P h1 e es]
  obtain e' es' where red1: "\<tau>Red0r P h1 (e, es) (e', es')"
    and "final e' \<Longrightarrow> es' = []" and feq: "fold_es e es = fold_es e' es'" by blast
  have nfin: "\<not> final e'"
  proof
    assume fin: "final e'"
    hence "es' = []" by(rule `final e' \<Longrightarrow> es' = []`)
    with fold fin feq have "final e1" by simp
    with red show False by auto
  qed
  from red1 wf_state have wf_state': "wf_state e' es'" by(rule \<tau>Red0r_preserves_wf_state[OF wf])
  hence fv: "fvs (e' # es') = {}" and icl: "list_all is_call es'"
    and bor: "final (last (e' # es')) \<or> (\<exists>v M vs. last (e' # es') = Val v\<bullet>M(map Val vs))"
    and esNil: "es' = [] \<Longrightarrow> final e'" by auto
  from red_fold_exs'[OF red[unfolded fold x1 feq] fv icl nfin]
  obtain E' where e1': "e1' = fold_es E' es'" 
    and red': "P \<turnstile> \<langle>e',(h1, empty)\<rangle> -\<epsilon>\<rightarrow> \<langle>E',(h1', empty)\<rangle>" by auto
  from fv fv_fold_es[OF icl, of e'] fold feq have "fv e1 = {}" by(auto)
  with red_dom_lcl[OF red] x1 have x1': "x1' = empty" by simp
  from red_red0_tabisim0[OF wf red']
  have red'': "extTA2J0 P,P \<turnstile> \<langle>e',(h1, Map.empty)\<rangle> -\<epsilon>\<rightarrow> \<langle>E',(h1', empty)\<rangle>" by simp
  show "bisim_red_red0 s1' s2 \<and> (\<lambda>e e'. False)^++ s1' s1 \<or>
        (\<exists>s2'. red0_\<tau>mthr.silent_movet P s2 s2' \<and> bisim_red_red0 s1' s2')"
  proof(cases "\<forall>aMvs. call e' = \<lfloor>aMvs\<rfloor> \<longrightarrow> synthesized_call P h1 aMvs")
    case True
    with red'' have "P \<turnstile>0 \<langle>e'/es', h1\<rangle> -\<epsilon>\<rightarrow> \<langle>E'/es', h1'\<rangle>" by(rule red0Red)
    moreover from red \<tau> have [simp]: "h1' = h1" by(auto dest: \<tau>move0_heap_unchanged)
    moreover from \<tau> fold feq icl nfin have "\<tau>move0 P h1 e'" by(simp add: fold_es_\<tau>move0_inv)
    ultimately have "\<tau>Red0 P h1 (e', es') (E', es')" using `\<tau>move0 P h1 e'` by auto
    with red1 have "\<tau>Red0t P h1 (e, es) (E', es')" by(rule rtranclp_into_tranclp1)
    moreover hence "wf_state E' es'" using wf_state by(rule \<tau>Red0t_preserves_wf_state[OF wf])
    hence "bisim_red_red0 ((e1', x1'), h1) ((E', es'), h1)" unfolding x1' e1' by(auto del: wf_state.cases)
    ultimately show ?thesis using s1 s1' s2 heap by simp(blast intro:  \<tau>Red0t_into_silent_movet)
  next
    case False
    then obtain a M vs where call: "call e' = \<lfloor>(a, M, vs)\<rfloor>"
      and notsynth: "\<not> synthesized_call P h1 (a, M, vs)" by auto
    from notsynth called_methodD[OF red'' call] obtain C fs D Us U pns body
      where "h1' = h1"
      and ha: "h1 a = \<lfloor>Obj C fs\<rfloor>"
      and sees: "P \<turnstile> C sees M: Us\<rightarrow>U = (pns, body) in D"
      and length: "length vs = length pns" "length Us = length pns"
      by(auto, blast)
    with notsynth have nec: "\<not> is_external_call P (Class C) M" by(simp add: synthesized_call_def)
    let ?e = "blocks (this#pns, Class D#Us, Addr a#vs, body)"
    from call ha nec have "P \<turnstile>0 \<langle>e'/es',h1\<rangle> -\<epsilon>\<rightarrow> \<langle>?e/e' # es',h1\<rangle>"
      using sees length by(rule red0Call)
    moreover from \<tau> fold feq icl nfin False have "\<tau>move0 P h1 e'" by(simp add: fold_es_\<tau>move0_inv)
    ultimately have "\<tau>Red0 P h1 (e', es') (?e, e' # es')" by auto
    with red1 have "\<tau>Red0t P h1 (e, es) (?e, e' # es')" by(rule rtranclp_into_tranclp1)
    moreover {
      from `P \<turnstile>0 \<langle>e'/es',h1\<rangle> -\<epsilon>\<rightarrow> \<langle>?e/e' # es',h1\<rangle>` have "wf_state ?e (e' # es')"
	using wf_state' by(rule red0_preserves_wf_state[OF wf])
      moreover from is_call_red_inline_callD[OF wf sees red' call, of fs] ha notsynth
      have "E' = inline_call ?e e'" by auto
      ultimately have "bisim_red_red0 s1' ((?e, e' # es'), h1')" unfolding s1' e1' x1'
	by(auto del: wf_state.cases wf_state.intros) }
    moreover from red' call notsynth have "h1 = h1'"
      by(auto dest: is_call_red_state_unchanged)
    ultimately show ?thesis unfolding heap x1' x1 s2 s1' `h1' = h1`
      by(blast intro: \<tau>Red0t_into_silent_movet)
  qed
next
  fix s1 s2 s2'
  assume "bisim_red_red0 s1 s2" and "red0_\<tau>mthr.silent_move P s2 s2'"
  moreover obtain e1 h1 x1 where s1: "s1 = ((e1, x1), h1)" by(cases s1, auto)
  moreover obtain e' es' h2' where s2': "s2' = ((e', es'), h2')" by(cases s2', auto)
  moreover obtain e es h2 where s2: "s2 = ((e, es), h2)" by(cases s2, auto)
  ultimately have bisim: "bisim_red_red0 ((e1, x1), h1) ((e, es), h2)"
    and red: "P \<turnstile>0 \<langle>e/es, h2\<rangle> -\<epsilon>\<rightarrow> \<langle>e'/es', h2'\<rangle>" 
    and \<tau>: "\<tau>move0 P h2 e \<or> final e" by(auto elim: \<tau>trsys.silent_move.cases)
  from bisim have heap: "h1 = h2"
    and fold: "e1 = fold_es e es"
    and x1: "x1 = empty"
    and wf_state: "wf_state e es"
    by(auto elim!: bisim_red_red0.cases del: wf_state.cases)
  from red wf_state have wf_state': "wf_state e' es'" by(rule red0_preserves_wf_state[OF wf])
  from red show "bisim_red_red0 s1 s2' \<and> (\<lambda>((e, es), h) ((e, es'), h). length es < length es')\<^sup>+\<^sup>+ s2' s2 \<or>
        (\<exists>s1'. red_\<tau>mthr.silent_movet P s1 s1' \<and> bisim_red_red0 s1' s2')"
  proof cases
    case (red0Red E H TA E' H' xs' ES)
    hence [simp]: "es' = es"
      and "extTA2J0 P,P \<turnstile> \<langle>e, (h2, empty)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h2', xs')\<rangle>" by auto
    from red0_red_tabisim0[OF wf this(2)] have red': "P \<turnstile> \<langle>e,(h2, empty)\<rangle> -\<epsilon>\<rightarrow> \<langle>e',(h2', xs')\<rangle>" by auto
    moreover from wf_state have "fv e = {}" by auto
    with red_dom_lcl[OF red'] red_fv_subset[OF wf red'] have "xs' = empty" by auto
    ultimately have "P \<turnstile> \<langle>e,(h2, empty)\<rangle> -\<epsilon>\<rightarrow> \<langle>e',(h2', empty)\<rangle>" by simp
    with wf_state have "P \<turnstile> \<langle>fold_es e es,(h2, empty)\<rangle> -\<epsilon>\<rightarrow> \<langle>fold_es e' es,(h2', empty)\<rangle>"
      by -(erule red_fold_exs, auto)
    moreover from red' have "\<not> final e" by auto
    with \<tau> wf_state fold have "\<tau>move0 P h2 e1" by(auto simp add: fold_es_\<tau>move0_inv)
    ultimately have "red_\<tau>mthr.silent_movet P s1 ((fold_es e' es, empty), h2')" using s1 fold \<tau> x1 heap
      by(auto intro: \<tau>trsys.silent_move.intros)
    moreover from wf_state' have "bisim_red_red0 ((fold_es e' es, empty), h2') s2'" unfolding s2'
      by(auto del: wf_state.cases wf_state.intros)
    ultimately show ?thesis by blast
  next
    case (red0Call E a M vs h C fs Ts T pns body D ES)
    hence [simp]: "es' = e # es" "h2' = h2" "e' = blocks (this # pns, Class D # Ts, Addr a # vs, body)"
      and call: "call e = \<lfloor>(a, M, vs)\<rfloor>"
      and ha: "h2 a = \<lfloor>Obj C fs\<rfloor>"
      and nec: "\<not> is_external_call P (Class C) M"
      and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D"
      and len: "length vs = length pns" "length Ts = length pns" by auto
    from is_call_red_inline_call(1)[OF wf sees len call, of "(h2, empty)" fs] ha
    have "P \<turnstile> \<langle>e,(h2, empty)\<rangle> -\<epsilon>\<rightarrow> \<langle>inline_call e' e, (h2, empty)\<rangle>" by simp
    with wf_state have "P \<turnstile> \<langle>fold_es e es, (h2, empty)\<rangle> -\<epsilon>\<rightarrow> \<langle>fold_es (inline_call e' e) es, (h2, empty)\<rangle>"
      by -(erule red_fold_exs, auto)
    moreover from call nec ha wf_state \<tau> have "\<tau>move0 P h2 (fold_es e es)"
      by(subst fold_es_\<tau>move0_inv)  auto
    hence "\<tau>MOVE P ((fold_es e es, empty), h2) \<epsilon> ((fold_es (inline_call e' e) es, empty), h2)" by auto
    moreover from wf_state'
    have "bisim_red_red0 ((fold_es (inline_call e' e) es, empty), h2) ((e', es'), h2')"
      by(auto del: wf_state.intros wf_state.cases)
    ultimately show ?thesis unfolding s1 s2 s2' fold heap x1 by(fastsimp)
  next
    case (red0Return e'a E ES H)
    hence [simp]: "es = E # es'" "e' = inline_call e E" "h2' = h2" by auto
    from fold wf_state'
    have "bisim_red_red0 ((e1, empty), h1) ((inline_call e E, es'), h2)" unfolding heap
      by(auto del: wf_state.intros wf_state.cases)
    thus ?thesis using s1 s2' s2 x1 by auto
  qed
next
  fix s1 s2 ta1 s1'
  assume "bisim_red_red0 s1 s2" and "mred P s1 ta1 s1'" and "\<not> \<tau>MOVE P s1 ta1 s1'"
  moreover obtain e1 h1 x1 where s1: "s1 = ((e1, x1), h1)" by(cases s1, auto)
  moreover obtain e1' h1' x1' where s1': "s1' = ((e1', x1'), h1')" by(cases s1', auto)
  moreover obtain e es h2 where s2: "s2 = ((e, es), h2)" by(cases s2, auto)
  ultimately have bisim: "bisim_red_red0 ((e1, x1), h1) ((e, es), h2)"
    and red: "P \<turnstile> \<langle>e1, (h1, x1)\<rangle> -ta1\<rightarrow> \<langle>e1', (h1', x1')\<rangle>" 
    and \<tau>: "\<not> \<tau>move0 P h1 e1" by(auto dest: red_\<tau>_taD)
  from bisim have heap: "h1 = h2"
    and fold: "e1 = fold_es e es"
    and x1: "x1 = empty"
    and wf_state: "wf_state e es"
    by(auto elim!: bisim_red_red0.cases del: wf_state.cases)
  from \<tau>Red0r_inline_call_not_final[of P h1 e es]
  obtain e' es' where red1: "\<tau>Red0r P h1 (e, es) (e', es')"
    and "final e' \<Longrightarrow> es' = []" and feq: "fold_es e es = fold_es e' es'" by blast
  hence red1': "red0_\<tau>mthr.silent_moves P ((e, es), h2) ((e', es'), h2)"
    unfolding heap by -(rule \<tau>Red0r_into_silent_moves)
  have nfin: "\<not> final e'"
  proof
    assume fin: "final e'"
    hence "es' = []" by(rule `final e' \<Longrightarrow> es' = []`)
    with fold fin feq have "final e1" by simp
    with red show False by auto
  qed
  from red1 wf_state have wf_state': "wf_state e' es'" by(rule \<tau>Red0r_preserves_wf_state[OF wf])
  hence fv: "fvs (e' # es') = {}" and icl: "list_all is_call es'"
    and bor: "final (last (e' # es')) \<or> (\<exists>v M vs. last (e' # es') = Val v\<bullet>M(map Val vs))"
    and esNil: "es' = [] \<Longrightarrow> final e'" by auto
  from red_fold_exs'[OF red[unfolded fold x1 feq] fv icl nfin]
  obtain E' where e1': "e1' = fold_es E' es'" 
    and red': "P \<turnstile> \<langle>e',(h1, empty)\<rangle> -ta1\<rightarrow> \<langle>E',(h1', empty)\<rangle>" by auto
  from fv fv_fold_es[OF icl, of e'] fold feq have "fv e1 = {}" by(auto)
  with red_dom_lcl[OF red] x1 have x1': "x1' = empty" by simp
  from red_red0_tabisim0[OF wf red'] obtain ta2
    where red'': "extTA2J0 P,P \<turnstile> \<langle>e',(h1, Map.empty)\<rangle> -ta2\<rightarrow> \<langle>E',(h1', empty)\<rangle>"
    and tasim: "ta_bisim0 ta1 ta2" by auto
  from \<tau> fold feq icl nfin have "\<not> \<tau>move0 P h1 e'" by(simp add: fold_es_\<tau>move0_inv)
  hence "\<forall>aMvs. call e' = \<lfloor>aMvs\<rfloor> \<longrightarrow> synthesized_call P h1 aMvs"
    by(auto simp add: \<tau>move0_callD)
  with red'' have red''': "P \<turnstile>0 \<langle>e'/es', h1\<rangle> -ta2\<rightarrow> \<langle>E'/es', h1'\<rangle>" by(rule red0Red)
  moreover from \<tau> fold feq icl nfin have "\<not> \<tau>move0 P h1 e'" by(simp add: fold_es_\<tau>move0_inv)
  hence "\<not> \<tau>MOVE0 P ((e', es'), h1) ta2 ((E', es'), h1')" using nfin by auto
  moreover from red''' wf_state' have "wf_state E' es'" by(rule red0_preserves_wf_state[OF wf])
  hence "bisim_red_red0 s1' ((E', es'), h1')" unfolding s1' e1' x1'
    by(auto del: wf_state.intros wf_state.cases)
  ultimately show "\<exists>s2' s2'' ta2. red0_\<tau>mthr.silent_moves P s2 s2' \<and> mred0 P s2' ta2 s2'' \<and>
                       \<not> \<tau>MOVE0 P s2' ta2 s2'' \<and> bisim_red_red0 s1' s2'' \<and> ta_bisim0 ta1 ta2"
    using tasim red1' heap unfolding s1' s2 by -(rule exI conjI|assumption|auto)+
next
  fix s1 s2 ta2 s2'
  assume "bisim_red_red0 s1 s2" and "mred0 P s2 ta2 s2'" "\<not> \<tau>MOVE0 P s2 ta2 s2'"
  moreover obtain e1 h1 x1 where s1: "s1 = ((e1, x1), h1)" by(cases s1, auto)
  moreover obtain e' es' h2' where s2': "s2' = ((e', es'), h2')" by(cases s2', auto)
  moreover obtain e es h2 where s2: "s2 = ((e, es), h2)" by(cases s2, auto)
  ultimately have bisim: "bisim_red_red0 ((e1, x1), h1) ((e, es), h2)"
    and red: "P \<turnstile>0 \<langle>e/es, h2\<rangle> -ta2\<rightarrow> \<langle>e'/es', h2'\<rangle>" 
    and \<tau>: "\<not> \<tau>move0 P h2 e \<and> \<not> final e \<or> ta2 \<noteq> \<epsilon>" by auto
  from red \<tau> have \<tau>: "\<not> \<tau>move0 P h2 e" and nfin: "\<not> final e" by(cases, auto dest: red_\<tau>_taD)+
  from bisim have heap: "h1 = h2" and fold: "e1 = fold_es e es"
    and x1: "x1 = empty" and wf_state: "wf_state e es"
    by(auto elim!: bisim_red_red0.cases del: wf_state.cases)
  from red wf_state have wf_state': "wf_state e' es'" by(rule red0_preserves_wf_state[OF wf])
  from red show "\<exists>s1' s1'' ta1. red_\<tau>mthr.silent_moves P s1 s1' \<and> mred P s1' ta1 s1'' \<and>
                                \<not> \<tau>MOVE P s1' ta1 s1'' \<and> bisim_red_red0 s1'' s2' \<and> ta_bisim0 ta1 ta2"
  proof(cases)
    case (red0Red E H TA E' H' xs' ES)
    hence [simp]: "es' = es"
      and "extTA2J0 P,P \<turnstile> \<langle>e, (h2, empty)\<rangle> -ta2\<rightarrow> \<langle>e', (h2', xs')\<rangle>" by auto
    from red0_red_tabisim0[OF wf this(2)] obtain ta1
      where red': "P \<turnstile> \<langle>e,(h2, empty)\<rangle> -ta1\<rightarrow> \<langle>e',(h2', xs')\<rangle>"
      and tasim: "ta_bisim0 ta1 ta2" by auto
    moreover from wf_state have "fv e = {}" by auto
    with red_dom_lcl[OF red'] red_fv_subset[OF wf red'] have "xs' = empty" by auto
    ultimately have "P \<turnstile> \<langle>e,(h2, empty)\<rangle> -ta1\<rightarrow> \<langle>e',(h2', empty)\<rangle>" by simp
    with wf_state have "P \<turnstile> \<langle>fold_es e es,(h2, empty)\<rangle> -ta1\<rightarrow> \<langle>fold_es e' es,(h2', empty)\<rangle>"
      by -(erule red_fold_exs, auto)
    moreover from \<tau> wf_state fold nfin have "\<not> \<tau>move0 P h2 e1" by(auto simp add: fold_es_\<tau>move0_inv)
    hence "\<not> \<tau>MOVE P ((fold_es e es, empty), h2) ta1 ((fold_es e' es, empty), h2')" unfolding fold by auto
    moreover from wf_state' have "bisim_red_red0 ((fold_es e' es, empty), h2') s2'" unfolding s2'
      by(auto del: wf_state.cases wf_state.intros)
    ultimately show ?thesis unfolding heap s1 s2 s2' fold x1
      using tasim by(fastsimp intro!: exI rtranclp.rtrancl_refl)
  next
    case red0Call
    with \<tau> have False by(auto simp add: \<tau>move0_callD synthesized_call_def)
    thus ?thesis ..
  next
    case red0Return with nfin show ?thesis by simp
  qed
qed

end