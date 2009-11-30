(*  Title:      JinjaThreads/Compiler/J0.thy
    Author:     Andreas Lochbihler
*)

header {*
  \chapter{Compilation}\label{cha:comp}
  \isaheader{The JinjaThreads source language with explicit call stacks}
*}
theory J0 imports
  "../J/WWellForm"
  "../J/WellType"
  "../J/Threaded" 
  "../Framework/FWBisimulation" 
begin

declare widen_refT [elim]

consts
  call :: "('a,'b) exp \<Rightarrow> (addr \<times> mname \<times> val list) option"
  calls :: "('a,'b) exp list \<Rightarrow> (addr \<times> mname \<times> val list) option"

primrec
  "call (new C) = None"
  "call (newA T\<lfloor>e\<rceil>) = call e"
  "call (Cast C e) = call e"
  "call (Val v) = None"
  "call (Var V) = None"
  "call (V:=e) = call e"
  "call (e \<guillemotleft>bop\<guillemotright> e') = (if is_val e then call e' else call e)"
  "call (a\<lfloor>i\<rceil>) = (if is_val a then call i else call a)"
  "call (AAss a i e) = (if is_val a then (if is_val i then call e else call i) else call a)"
  "call (a\<bullet>length) = call a"
  "call (e\<bullet>F{D}) = call e"
  "call (FAss e F D e') = (if is_val e then call e' else call e)"
  "call (e\<bullet>M(es)) = (if is_val e then
                     (if is_vals es \<and> is_addr e then \<lfloor>(THE a. e = addr a, M, THE vs. es = map Val vs)\<rfloor> else calls es) 
                     else call e)"
  "call ({V:T=vo; e}) = call e"
  "call (sync\<^bsub>V\<^esub> (o') e) = call o'"
  "call (insync\<^bsub>V\<^esub> (a) e) = call e"
  "call (e;;e') = call e"
  "call (if (e) e1 else e2) = call e"
  "call (while(b) e) = None"
  "call (throw e) = call e"
  "call (try e1 catch(C V) e2) = call e1"

  "calls [] = None"
  "calls (e#es) = (if is_val e then calls es else call e)"

declare domIff[iff, simp del]

lemma calls_append [simp]:
  "calls (es @ es') = (if calls es = None \<and> is_vals es then calls es' else calls es)"
apply(induct es, auto)
done

lemma call_callE [consumes 1, case_names CallObj CallParams Call]:
  "\<lbrakk> call (obj\<bullet>M(pns)) = \<lfloor>(a, M', vs)\<rfloor>;
     call obj = \<lfloor>(a, M', vs)\<rfloor> \<Longrightarrow> thesis; 
     \<And>v. \<lbrakk> obj = Val v; calls pns = \<lfloor>(a, M', vs)\<rfloor> \<rbrakk> \<Longrightarrow> thesis;
     \<lbrakk> obj = addr a; pns = map Val vs; M = M' \<rbrakk> \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
by(auto split: split_if_asm simp add: is_vals_conv)

lemma calls_conv:
  "calls es = \<lfloor>aMvs\<rfloor> \<longleftrightarrow> (\<exists>vs e es'. es = map Val vs @ e # es' \<and> call e = \<lfloor>aMvs\<rfloor>)"
proof(induct es)
  case Nil thus ?case by simp
next
  case (Cons e es)
  note IH = `(calls es = \<lfloor>aMvs\<rfloor>) = (\<exists>vs e es'. es = map Val vs @ e # es' \<and> call e = \<lfloor>aMvs\<rfloor>)`
  show ?case
  proof(cases "is_val e")
    case True
    then obtain v where e: "e = Val v" by auto
    hence "calls (e # es) = calls es" by(auto)
    moreover from e
    have "(calls es = \<lfloor>aMvs\<rfloor>) = (\<exists>vs e' es'. e # es = map Val (v # vs) @ e' # es' \<and> call e' = \<lfloor>aMvs\<rfloor>)"
      unfolding IH by(auto)
    also from e have "\<dots> = (\<exists>vs e' es'. e # es = map Val vs @ e' # es' \<and> call e' = \<lfloor>aMvs\<rfloor>)"
      apply(auto simp add: Cons_eq_append_conv)
      apply(rule_tac x="v # vs" in exI)
      by(clarsimp)
    finally show ?thesis .
  next
    case False
    show ?thesis
    proof(rule iffI)
      assume "calls (e # es) = \<lfloor>aMvs\<rfloor>"
      with False have "call e = \<lfloor>aMvs\<rfloor>" by(auto)
      hence "e # es = map Val [] @ e # es" "call e = \<lfloor>aMvs\<rfloor>" by auto
      thus "\<exists>vs e' es'. e # es = map Val vs @ e' # es' \<and> call e' = \<lfloor>aMvs\<rfloor>" by blast
    next
      assume "\<exists>vs e' es'. e # es = map Val vs @ e' # es' \<and> call e' = \<lfloor>aMvs\<rfloor>"
      then obtain vs e' es' where "e # es = map Val vs @ e' # es'" "call e' = \<lfloor>aMvs\<rfloor>" by(blast)
      moreover
      with False have "vs = []" 
	by-(erule contrapos_np, auto simp add: neq_Nil_conv)
      ultimately show "calls (e # es) = \<lfloor>aMvs\<rfloor>" by(auto)
    qed
  qed
qed

lemma calls_map_Val [simp]:
  "calls (map Val vs) = None"
by(induct vs, auto)

lemma call_not_is_val [dest]: "call e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> \<not> is_val e"
by(cases e, auto)

lemma is_calls_not_is_vals [dest]: "calls es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> \<not> is_vals es"
by(induct es, auto)


consts
  inline_call :: "('a,'b) exp \<Rightarrow> ('a,'b) exp \<Rightarrow> ('a,'b) exp"
  inline_calls :: "('a,'b) exp \<Rightarrow> ('a,'b) exp list \<Rightarrow> ('a,'b) exp list"

primrec
  "inline_call f (new C) = new C"
  "inline_call f (newA T\<lfloor>e\<rceil>) = newA T\<lfloor>inline_call f e\<rceil>"
  "inline_call f (Cast C e) = Cast C (inline_call f e)"
  "inline_call f (Val v) = Val v"
  "inline_call f (Var V) = Var V"
  "inline_call f (V:=e) = V := inline_call f e"
  "inline_call f (e \<guillemotleft>bop\<guillemotright> e') = (if is_val e then (e \<guillemotleft>bop\<guillemotright> inline_call f e') else (inline_call f e \<guillemotleft>bop\<guillemotright> e'))"
  "inline_call f (a\<lfloor>i\<rceil>) = (if is_val a then a\<lfloor>inline_call f i\<rceil> else (inline_call f a)\<lfloor>i\<rceil>)"
  "inline_call f (AAss a i e) = (if is_val a then if is_val i then AAss a i (inline_call f e) else AAss a (inline_call f i) e else AAss (inline_call f a) i e)"
  "inline_call f (a\<bullet>length) = inline_call f a\<bullet>length"
  "inline_call f (e\<bullet>F{D}) = inline_call f e\<bullet>F{D}"
  "inline_call f (FAss e F D e') = (if is_val e then FAss e F D (inline_call f e') else FAss (inline_call f e) F D e')"
  "inline_call f (e\<bullet>M(es)) = (if is_val e then if is_vals es \<and> is_addr e then f else e\<bullet>M(inline_calls f es) else inline_call f e\<bullet>M(es))"
  "inline_call f ({V:T=vo; e}) = {V:T=vo; inline_call f e}"
  "inline_call f (sync\<^bsub>V\<^esub> (o') e) = sync\<^bsub>V\<^esub> (inline_call f o') e"
  "inline_call f (insync\<^bsub>V\<^esub> (a) e) = insync\<^bsub>V\<^esub> (a) (inline_call f e)"
  "inline_call f (e;;e') = inline_call f e;;e'"
  "inline_call f (if (b) e else e') = (if (inline_call f b) e else e')"
  "inline_call f (while (b) e) = while (b) e"
  "inline_call f (throw e) = throw (inline_call f e)"
  "inline_call f (try e1 catch(C V) e2) = try inline_call f e1 catch(C V) e2"

  "inline_calls f [] = []"
  "inline_calls f (e#es) = (if is_val e then e # inline_calls f es else inline_call f e # es)"

lemma inline_calls_map_Val_append [simp]:
  "inline_calls f (map Val vs @ es) = map Val vs @ inline_calls f es"
by(induct vs, auto)

lemma inline_call_eq_Val_aux:
  "inline_call e E = Val v \<Longrightarrow> call E = \<lfloor>aMvs\<rfloor> \<Longrightarrow> e = Val v"
by(induct E)(auto split: split_if_asm)

lemmas inline_call_eq_Val [dest] = inline_call_eq_Val_aux inline_call_eq_Val_aux[OF sym, THEN sym]

lemma inline_calls_eq_empty [simp]: "inline_calls e es = [] \<longleftrightarrow> es = []"
by(cases es, auto)

lemma inline_calls_map_Val [simp]: "inline_calls e (map Val vs) = map Val vs"
by(induct vs) auto

lemma  fixes E :: "('a,'b) exp" and Es :: "('a,'b) exp list"
  shows inline_call_eq_Throw [dest]: "inline_call e E = Throw a \<Longrightarrow> call E = \<lfloor>aMvs\<rfloor> \<Longrightarrow> e = Throw a \<or> e = addr a"
  and True
by(induct E and Es)(fastsimp split:split_if_asm)+

lemma Throw_eq_inline_call_eq [dest]:
  "inline_call e E = Throw a \<Longrightarrow> call E = \<lfloor>aMvs\<rfloor> \<Longrightarrow> Throw a = e \<or> addr a = e"
by(auto dest: inline_call_eq_Throw[OF sym])

lemma is_vals_inline_calls [dest]:
  "\<lbrakk> is_vals (inline_calls e es); calls es = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> is_val e"
by(induct es, auto split: split_if_asm)

lemma [dest]: "\<lbrakk> inline_calls e es = map Val vs; calls es = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> is_val e"
              "\<lbrakk> map Val vs = inline_calls e es; calls es = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> is_val e"
by(fastsimp intro!: is_vals_inline_calls del: is_val.intros simp add: is_vals_conv elim: sym)+

lemma inline_calls_eq_Val_Throw [dest]:
  "\<lbrakk> inline_calls e es = map Val vs @ Throw a # es'; calls es = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> e = Throw a \<or> is_val e"
apply(induct es arbitrary: vs a es')
apply(auto simp add: Cons_eq_append_conv split: split_if_asm)
done

lemma Val_Throw_eq_inline_calls [dest]:
  "\<lbrakk> map Val vs @ Throw a # es' = inline_calls e es; calls es = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> Throw a = e \<or> is_val e"
by(auto dest: inline_calls_eq_Val_Throw[OF sym])

declare option.split [split del] split_if_asm [split]  split_if [split del]

lemma call_inline_call [simp]:
  "call e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> call (inline_call {v:T=vo; e'} e) = call e'"
  "calls es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> calls (inline_calls {v:T=vo;e'} es) = call e'"
apply(induct e and es)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp split: split_if)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp split: split_if)
apply(clarsimp)
 apply(fastsimp split: split_if)
apply(fastsimp split: split_if)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp split: split_if)
apply(fastsimp split: split_if)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp split: split_if)
done

declare option.split [split] split_if [split] split_if_asm [split del]

lemma fv_inline_call: "call e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> fv (inline_call e' e) \<subseteq> fv e \<union> fv e'"
  and fvs_inline_calls: "calls es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> fvs (inline_calls e' es) \<subseteq> fvs es \<union> fv e'"
by(induct e and es)(fastsimp split: split_if_asm)+

lemma contains_insync_inline_call_conv:
  "contains_insync (inline_call e e') \<longleftrightarrow> contains_insync e \<and> call e' \<noteq> None \<or> contains_insync e'"
  and contains_insyncs_inline_calls_conv:
   "contains_insyncs (inline_calls e es') \<longleftrightarrow> contains_insync e \<and> calls es' \<noteq> None \<or> contains_insyncs es'"
by(induct e' and es')(auto split: split_if_asm simp add: is_vals_conv)

lemma contains_insync_inline_call [simp]:
  "call e' = \<lfloor>aMvs\<rfloor> \<Longrightarrow> contains_insync (inline_call e e') \<longleftrightarrow> contains_insync e \<or> contains_insync e'"
  and contains_insyncs_inline_calls [simp]:
  "calls es' = \<lfloor>aMvs\<rfloor> \<Longrightarrow> contains_insyncs (inline_calls e es') \<longleftrightarrow> contains_insync e \<or> contains_insyncs es'"
by(simp_all add: contains_insync_inline_call_conv contains_insyncs_inline_calls_conv)


definition synthesized_call :: "'m prog \<Rightarrow> heap \<Rightarrow> (addr \<times> mname \<times> val list) \<Rightarrow> bool"
where "synthesized_call P h = (\<lambda>(a, M, vs). \<exists>T. typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>T\<rfloor> \<and> is_external_call P T M)"

lemma synthesized_call_conv:
  "synthesized_call P h (a, M, vs) = (\<exists>T. typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>T\<rfloor> \<and> is_external_call P T M)"
by(simp add: synthesized_call_def)

types
  J0_thread_action = "(addr,thread_id,expr \<times> expr list,heap,addr,obs_event option) thread_action"

translations
  "J0_thread_action" <= (type) "(nat,nat,expr \<times> expr list,heap,nat,obs_event option) thread_action"

definition extNTA2J0 :: "J_prog \<Rightarrow> (cname \<times> mname \<times> addr) \<Rightarrow> (expr \<times> expr list)"
where
  "extNTA2J0 P = (\<lambda>(C, M, a). let (D, _, _, _, body) = method P C M
                               in ({this:Class D=\<lfloor>Addr a\<rfloor>; body}, [addr a\<bullet>M([])]))"

lemma extNTA2J0_iff [simp]:
  "extNTA2J0 P (C, M, a) = 
   ({this:Class (fst (method P C M))=\<lfloor>Addr a\<rfloor>; snd (snd (snd (snd (method P C M))))}, [addr a\<bullet>M([])])"
by(simp add: extNTA2J0_def split_def)

abbreviation extTA2J0 :: "J_prog \<Rightarrow> external_thread_action \<Rightarrow> J0_thread_action"
where "extTA2J0 P \<equiv> convert_extTA (extNTA2J0 P)"

inductive red0 :: "J_prog \<Rightarrow> expr \<Rightarrow> expr list \<Rightarrow> heap \<Rightarrow>
                           J0_thread_action \<Rightarrow> expr \<Rightarrow> expr list \<Rightarrow> heap \<Rightarrow> bool"
                ("_ \<turnstile>0 ((1\<langle>_'/_,/_\<rangle>) -_\<rightarrow>/ (1\<langle>_'/_,/_\<rangle>))" [51,0,0,0,0,0,0,0] 81)
for P ::J_prog
where

  red0Red:
  "\<lbrakk> extTA2J0 P,P \<turnstile> \<langle>e, (h, empty)\<rangle> -ta\<rightarrow> \<langle>e', (h', xs')\<rangle>;
     \<forall>aMvs. call e = \<lfloor>aMvs\<rfloor> \<longrightarrow> synthesized_call P h aMvs \<rbrakk>
  \<Longrightarrow> P \<turnstile>0 \<langle>e/es, h\<rangle> -ta\<rightarrow> \<langle>e'/es, h'\<rangle>"

| red0Call:
  "\<lbrakk> call e = \<lfloor>(a, M, vs)\<rfloor>; h a = \<lfloor>Obj C fs\<rfloor>; \<not> is_external_call P (Class C) M; P \<turnstile> C sees M:Ts\<rightarrow>T = (pns, body) in D; 
     size vs = size pns; size Ts = size pns \<rbrakk>
  \<Longrightarrow> P \<turnstile>0 \<langle>e/es, h\<rangle> -\<epsilon>\<rightarrow> \<langle>blocks(this#pns, Class D#Ts, Addr a#vs, body)/e#es, h\<rangle>"

| red0Return:
  "final e' \<Longrightarrow> P \<turnstile>0 \<langle>e'/e#es, h\<rangle> -\<epsilon>\<rightarrow> \<langle>inline_call e' e/es, h\<rangle>"

lemma fv_extRet2J [simp]: "fv (extRet2J va) = {}"
by(cases va) simp_all

lemma assumes wf: "wwf_J_prog P"
  shows red_fv_subset: "extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> fv e' \<subseteq> fv e"
  and reds_fvs_subset: "extTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> fvs es' \<subseteq> fvs es"
proof(induct rule: red_reds.inducts)
  case (RedCall s a C fs M Ts T pns body D vs)
  hence "fv body \<subseteq> {this} \<union> set pns"
    using wf by(fastsimp dest!:sees_wf_mdecl simp:wf_mdecl_def)
  with RedCall show ?case by fastsimp
qed(fastsimp)+

declare domIff[iff del]

lemma assumes wwf: "wwf_J_prog P"
  shows red_fv_ok: "\<lbrakk> extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; fv e \<subseteq> dom (lcl s) \<rbrakk> \<Longrightarrow> fv e' \<subseteq> dom (lcl s')"
  and reds_fvs_ok: "\<lbrakk> extTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; fvs es \<subseteq> dom (lcl s) \<rbrakk> \<Longrightarrow> fvs es' \<subseteq> dom (lcl s')"
proof(induct rule: red_reds.inducts)
  case (RedCall s a C fs M Ts T pns body D vs)
  from `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D` have "wwf_J_mdecl P D (M,Ts,t,pns,body)"
    by(auto dest!: sees_wf_mdecl[OF wwf] simp add: wf_mdecl_def)
  with RedCall show ?case by(auto)
next
  case (BlockRed e h x V vo ta e' h' x' T)
  note red = `extTA,P \<turnstile> \<langle>e,(h, x(V := vo))\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>`
  hence "fv e' \<subseteq> fv e" by(auto dest: red_fv_subset[OF wwf] del: subsetI)
  moreover from ` fv {V:T=vo; e} \<subseteq> dom (lcl (h, x))`
  have "fv e - {V} \<subseteq> dom x" by(simp)
  ultimately have "fv e' - {V} \<subseteq> dom x - {V}" by(auto)
  moreover from red have "dom (x(V := vo)) \<subseteq> dom x'"
    by(auto dest: red_lcl_incr del: subsetI)
  ultimately have "fv e' - {V} \<subseteq> dom x' - {V}"
    by(auto split: split_if_asm)
  thus ?case by(auto simp del: fun_upd_apply)
qed(fastsimp dest: red_lcl_incr del: subsetI)+


lemma is_call_red_state_unchanged: 
  "\<lbrakk> extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; call e = \<lfloor>aMvs\<rfloor>; \<not> synthesized_call P (hp s) aMvs \<rbrakk> \<Longrightarrow> s' = s \<and> ta = \<epsilon>"

  and is_calls_reds_state_unchanged:
  "\<lbrakk> extTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; calls es = \<lfloor>aMvs\<rfloor>; \<not> synthesized_call P (hp s) aMvs \<rbrakk> \<Longrightarrow> s' = s \<and> ta = \<epsilon>"
apply(induct rule: red_reds.inducts)
apply(fastsimp split: split_if_asm simp add: synthesized_call_def)+
done


lemma called_methodD:
        "\<lbrakk> extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; call e = \<lfloor>(a, M, vs)\<rfloor>; \<not> synthesized_call P (hp s) (a, M, vs) \<rbrakk> 
         \<Longrightarrow> \<exists>C fs D Us U pns body. hp s' = hp s \<and> hp s a = \<lfloor>Obj C fs\<rfloor> \<and> P \<turnstile> C sees M: Us\<rightarrow>U = (pns, body) in D \<and>
                                   length vs = length pns \<and> length Us = length pns"
        (is "\<lbrakk> _; _; _ \<rbrakk> \<Longrightarrow>  ?concl")

  and called_methodsD:
        "\<lbrakk> extTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; calls es = \<lfloor>(a, M, vs)\<rfloor>; \<not> synthesized_call P (hp s) (a, M, vs) \<rbrakk> 
         \<Longrightarrow> \<exists>C fs D Us U pns body. hp s' = hp s \<and> hp s a = \<lfloor>Obj C fs\<rfloor> \<and> P \<turnstile> C sees M: Us\<rightarrow>U = (pns, body) in D \<and>
                                   length vs = length pns \<and> length Us = length pns"
        (is "\<lbrakk> _; _; _ \<rbrakk> \<Longrightarrow>  ?concl")
apply(induct rule: red_reds.inducts)
apply(auto split: split_if_asm simp add: synthesized_call_def)
apply(fastsimp)
done

abbreviation mred0 :: "J_prog \<Rightarrow> (addr,addr,expr \<times> expr list,heap,addr,obs_event) semantics"
where "mred0 P \<equiv> (\<lambda>((e, es), h) ta ((e', es'), h'). red0 P e es h ta e' es' h')"

section {* Silent moves *}

primrec  \<tau>move0 :: "'m prog \<Rightarrow> heap \<Rightarrow> ('a, 'b) exp \<Rightarrow> bool"
  and \<tau>moves0 :: "'m prog \<Rightarrow> heap \<Rightarrow> ('a, 'b) exp list \<Rightarrow> bool"
where
  "\<tau>move0 P h (new C) \<longleftrightarrow> False"
| "\<tau>move0 P h (newA T\<lfloor>e\<rceil>) \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a)"
| "\<tau>move0 P h (Cast U e) \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v)"
| "\<tau>move0 P h (e \<guillemotleft>bop\<guillemotright> e') \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v \<and>
   (\<tau>move0 P h e' \<or> (\<exists>a. e' = Throw a) \<or> (\<exists>v. e' = Val v)))"
| "\<tau>move0 P h (Val v) \<longleftrightarrow> False"
| "\<tau>move0 P h (Var V) \<longleftrightarrow> True"
| "\<tau>move0 P h (V := e) \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v)"
| "\<tau>move0 P h (a\<lfloor>i\<rceil>) \<longleftrightarrow> \<tau>move0 P h a \<or> (\<exists>ad. a = Throw ad) \<or> (\<exists>v. a = Val v \<and> (\<tau>move0 P h i \<or> (\<exists>a. i = Throw a)))"
| "\<tau>move0 P h (AAss a i e) \<longleftrightarrow> \<tau>move0 P h a \<or> (\<exists>ad. a = Throw ad) \<or> (\<exists>v. a = Val v \<and> 
   (\<tau>move0 P h i \<or> (\<exists>a. i = Throw a) \<or> (\<exists>v. i = Val v \<and> (\<tau>move0 P h e \<or> (\<exists>a. e = Throw a)))))"
| "\<tau>move0 P h (a\<bullet>length) \<longleftrightarrow> \<tau>move0 P h a \<or> (\<exists>ad. a = Throw ad)"
| "\<tau>move0 P h (e\<bullet>F{D}) \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a)"
| "\<tau>move0 P h (FAss e F D e') \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v \<and> (\<tau>move0 P h e' \<or> (\<exists>a. e' = Throw a)))"
| "\<tau>move0 P h (e\<bullet>M(es)) \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v \<and>
   ((\<tau>moves0 P h es \<or> (\<exists>vs a es'. es = map Val vs @ Throw a # es')) \<or> 
    (\<exists>vs. es = map Val vs \<and> (v = Null \<or> (\<forall>T. typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor> \<longrightarrow> \<not> is_external_call P T M)))))"
| "\<tau>move0 P h ({V:T=vo; e}) \<longleftrightarrow> \<tau>move0 P h e \<or> ((\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v))"
| "\<tau>move0 P h (sync\<^bsub>V'\<^esub>(e) e') \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a)"
| "\<tau>move0 P h (insync\<^bsub>V'\<^esub>(ad) e) \<longleftrightarrow> \<tau>move0 P h e"
| "\<tau>move0 P h (e;;e') \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v)"
| "\<tau>move0 P h (if (e) e' else e'') \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v)"
| "\<tau>move0 P h (while (e) e') = True"
| "\<tau>move0 P h (throw e) \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a) \<or> e = null"
| "\<tau>move0 P h (try e catch(C V) e') \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v)"

| "\<tau>moves0 P h [] \<longleftrightarrow> False"
| "\<tau>moves0 P h (e # es) \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>v. e = Val v \<and> \<tau>moves0 P h es)"

lemma \<tau>move0_\<tau>moves0_intros:
  fixes e e1 e2 e' :: "('a, 'b) exp" and es :: "('a, 'b) exp list"
  shows \<tau>move0NewArray: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (newA T\<lfloor>e\<rceil>)"
  and \<tau>move0Cast: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (Cast U e)"
  and \<tau>move0CastRed: "\<tau>move0 P h (Cast U (Val v))"
  and \<tau>move0BinOp1: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (e\<guillemotleft>bop\<guillemotright>e')"
  and \<tau>move0BinOp2: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (Val v\<guillemotleft>bop\<guillemotright>e)"
  and \<tau>move0BinOp: "\<tau>move0 P h (Val v\<guillemotleft>bop\<guillemotright>Val v')"
  and \<tau>move0Var: "\<tau>move0 P h (Var V)"
  and \<tau>move0LAss: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (V := e)"
  and \<tau>move0LAssRed: "\<tau>move0 P h (V := Val v)"
  and \<tau>move0AAcc1: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (e\<lfloor>e'\<rceil>)"
  and \<tau>move0AAcc2: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (Val v\<lfloor>e\<rceil>)"
  and \<tau>move0AAss1: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (e\<lfloor>e1\<rceil> := e2)"
  and \<tau>move0AAss2: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (Val v\<lfloor>e\<rceil> := e')"
  and \<tau>move0AAss3: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (Val v\<lfloor>Val v'\<rceil> := e)"
  and \<tau>move0ALength: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (e\<bullet>length)"
  and \<tau>move0FAcc: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (e\<bullet>F{D})"
  and \<tau>move0FAss1: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (FAss e F D e')"
  and \<tau>move0FAss2: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (Val v\<bullet>F{D} := e)"
  and \<tau>move0CallObj: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (e\<bullet>M(es))"
  and \<tau>move0CallParams: "\<tau>moves0 P h es \<Longrightarrow> \<tau>move0 P h (Val v\<bullet>M(es))"
  and \<tau>move0Call: "(\<And>T. typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor> \<Longrightarrow> \<not> is_external_call P T M) \<Longrightarrow> \<tau>move0 P h (Val v\<bullet>M(map Val vs))"
  and \<tau>move0Block: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h {V:T=vo; e}"
  and \<tau>move0BlockRed: "\<tau>move0 P h {V:T=vo; Val v}"
  and \<tau>move0Sync: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (sync\<^bsub>V'\<^esub> (e) e')"
  and \<tau>move0InSync: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (insync\<^bsub>V'\<^esub> (a) e)"
  and \<tau>move0Seq: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (e;;e')"
  and \<tau>move0SeqRed: "\<tau>move0 P h (Val v;; e')"
  and \<tau>move0Cond: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (if (e) e1 else e2)"
  and \<tau>move0CondRed: "\<tau>move0 P h (if (Val v) e1 else e2)"
  and \<tau>move0WhileRed: "\<tau>move0 P h (while (e) e')"
  and \<tau>move0Throw: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (throw e)"
  and \<tau>move0ThrowNull: "\<tau>move0 P h (throw null)"
  and \<tau>move0Try: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (try e catch(C V) e')"
  and \<tau>move0TryRed: "\<tau>move0 P h (try Val v catch(C V) e)"
  and \<tau>move0TryThrow: "\<tau>move0 P h (try Throw a catch(C V) e)"
  and \<tau>move0NewArrayThrow: "\<tau>move0 P h (newA T\<lfloor>Throw a\<rceil>)"
  and \<tau>move0CastThrow: "\<tau>move0 P h (Cast T (Throw a))"
  and \<tau>move0BinOpThrow1: "\<tau>move0 P h (Throw a \<guillemotleft>bop\<guillemotright> e')"
  and \<tau>move0BinOpThrow2: "\<tau>move0 P h (Val v \<guillemotleft>bop\<guillemotright> Throw a)"
  and \<tau>move0LAssThrow: "\<tau>move0 P h (V:=(Throw a))"
  and \<tau>move0AAccThrow1: "\<tau>move0 P h (Throw a\<lfloor>e\<rceil>)"
  and \<tau>move0AAccThrow2: "\<tau>move0 P h (Val v\<lfloor>Throw a\<rceil>)"
  and \<tau>move0AAssThrow1: "\<tau>move0 P h (AAss (Throw a) e e')"
  and \<tau>move0AAssThrow2: "\<tau>move0 P h (AAss (Val v) (Throw a) e')"
  and \<tau>move0AAssThrow3: "\<tau>move0 P h (AAss (Val v) (Val v') (Throw a))"
  and \<tau>move0ALengthThrow: "\<tau>move0 P h (Throw a\<bullet>length)"
  and \<tau>move0FAccThrow: "\<tau>move0 P h (Throw a\<bullet>F{D})"
  and \<tau>move0FAssThrow1: "\<tau>move0 P h (Throw a\<bullet>F{D} := e)"
  and \<tau>move0FAssThrow2: "\<tau>move0 P h (FAss (Val v) F D (Throw a))"
  and \<tau>move0CallThrowObj: "\<tau>move0 P h (Throw a\<bullet>M(es))"
  and \<tau>move0CallThrowParams: "\<tau>move0 P h (Val v\<bullet>M(map Val vs @ Throw a # es))"
  and \<tau>move0BlockThrow: "\<tau>move0 P h {V:T=vo; Throw a}"
  and \<tau>move0SyncThrow: "\<tau>move0 P h (sync\<^bsub>V'\<^esub> (Throw a) e)"
  and \<tau>move0SeqThrow: "\<tau>move0 P h (Throw a;;e)"
  and \<tau>move0CondThrow: "\<tau>move0 P h (if (Throw a) e1 else e2)"
  and \<tau>move0ThrowThrow: "\<tau>move0 P h (throw (Throw a))"

  and \<tau>moves0Hd: "\<tau>move0 P h e \<Longrightarrow> \<tau>moves0 P h (e # es)"
  and \<tau>moves0Tl: "\<tau>moves0 P h es \<Longrightarrow> \<tau>moves0 P h (Val v # es)"
apply auto
done

lemma \<tau>moves0_map_Val [iff]:
  "\<not> \<tau>moves0 P h (map Val vs)"
by(induct vs) auto

lemma \<tau>moves0_map_Val_append [simp]:
  "\<tau>moves0 P h (map Val vs @ es) = \<tau>moves0 P h es"
by(induct vs)(auto)

lemma no_reds_map_Val_Throw [simp]:
  "extTA,P \<turnstile> \<langle>map Val vs @ Throw a # es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> = False"
by(induct vs arbitrary: es')(auto elim: reds.cases)

lemma red_\<tau>_taD: "\<lbrakk> extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<tau>move0 P (hp s) e \<rbrakk> \<Longrightarrow> ta = \<epsilon>"
  and reds_\<tau>_taD: "\<lbrakk> extTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; \<tau>moves0 P (hp s) es \<rbrakk> \<Longrightarrow> ta = \<epsilon>"
apply(induct rule: red_reds.inducts)
apply(fastsimp simp add: map_eq_append_conv)+
done

lemma \<tau>move0_heap_unchanged: "\<lbrakk> extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<tau>move0 P (hp s) e \<rbrakk> \<Longrightarrow> hp s' = hp s"
  and \<tau>moves0_heap_unchanged: "\<lbrakk> extTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; \<tau>moves0 P (hp s) es \<rbrakk> \<Longrightarrow> hp s' = hp s"
apply(induct rule: red_reds.inducts)
apply(auto)
apply(fastsimp simp add: map_eq_append_conv)
done

primrec \<tau>Move0 :: "'m prog \<Rightarrow> heap \<Rightarrow> (expr \<times> expr list) \<Rightarrow> bool"
where
  "\<tau>Move0 P h (e, exs) = (\<tau>move0 P h e \<or> final e)"

lemma \<tau>Move0_iff:
  "\<tau>Move0 P h ees \<longleftrightarrow> (let (e, _) = ees in \<tau>move0 P h e \<or> final e)"
by(cases ees)(simp)

definition no_call :: "'m prog \<Rightarrow> heap \<Rightarrow> ('a, 'b) exp \<Rightarrow> bool"
where "no_call P h e = (\<forall>aMvs. call e = \<lfloor>aMvs\<rfloor> \<longrightarrow> synthesized_call P h aMvs)"

definition no_calls :: "'m prog \<Rightarrow> heap \<Rightarrow> ('a, 'b) exp list \<Rightarrow> bool"
where "no_calls P h es = (\<forall>aMvs. calls es = \<lfloor>aMvs\<rfloor> \<longrightarrow> synthesized_call P h aMvs)"

lemma no_call_simps [simp]:
  "no_call P h (new C) = True"
  "no_call P h (newA T\<lfloor>e\<rceil>) = no_call P h e"
  "no_call P h (Cast T e) = no_call P h e"
  "no_call P h (Val v) = True"
  "no_call P h (Var V) = True"
  "no_call P h (V := e) = no_call P h e"
  "no_call P h (e \<guillemotleft>bop\<guillemotright> e') = (if is_val e then no_call P h e' else no_call P h e)"
  "no_call P h (a\<lfloor>i\<rceil>) = (if is_val a then no_call P h i else no_call P h a)"
  "no_call P h (AAss a i e) = (if is_val a then (if is_val i then no_call P h e else no_call P h i) else no_call P h a)"
  "no_call P h (a\<bullet>length) = no_call P h a"
  "no_call P h (e\<bullet>F{D}) = no_call P h e"
  "no_call P h (FAss e F D e') = (if is_val e then no_call P h e' else no_call P h e)"
  "no_call P h (e\<bullet>M(es)) = (if is_val e then (if is_vals es \<and> is_addr e then synthesized_call P h (THE a. e = addr a, M, THE vs. es = map Val vs) else no_calls P h es) else no_call P h e)"
  "no_call P h ({V:T=vo; e}) = no_call P h e"
  "no_call P h (sync\<^bsub>V'\<^esub> (e) e') = no_call P h e"
  "no_call P h (insync\<^bsub>V'\<^esub> (ad) e) = no_call P h e"
  "no_call P h (e;;e') = no_call P h e"
  "no_call P h (if (e) e1 else e2) = no_call P h e"
  "no_call P h (while(e) e') = True"
  "no_call P h (throw e) = no_call P h e"
  "no_call P h (try e catch(C V) e') = no_call P h e"
by(auto simp add: no_call_def no_calls_def)

lemma no_calls_simps [simp]:
  "no_calls P h [] = True"
  "no_calls P h (e # es) = (if is_val e then no_calls P h es else no_call P h e)"
by(simp_all add: no_call_def no_calls_def)

lemma no_calls_map_Val [simp]:
  "no_calls P h (map Val vs)"
by(induct vs) simp_all

definition \<tau>red0 :: "(external_thread_action \<Rightarrow> (addr,thread_id,'x,heap,addr,obs_event option) thread_action) \<Rightarrow>
  J_prog \<Rightarrow> heap \<Rightarrow> (expr \<times> locals) \<Rightarrow> (expr \<times> locals) \<Rightarrow> bool"
where "\<tau>red0 extTA P h exs e'xs' = (extTA,P \<turnstile> \<langle>fst exs, (h, snd exs)\<rangle> -\<epsilon>\<rightarrow> \<langle>fst e'xs', (h, snd e'xs')\<rangle> \<and> \<tau>move0 P h (fst exs) \<and> no_call P h (fst exs))"

definition \<tau>reds0 :: "(external_thread_action \<Rightarrow> (addr,thread_id,'x,heap,addr,obs_event option) thread_action) \<Rightarrow>
  J_prog \<Rightarrow> heap \<Rightarrow> (expr list \<times> locals) \<Rightarrow> (expr list \<times> locals) \<Rightarrow> bool"
where "\<tau>reds0 extTA P h esxs es'xs' = (extTA,P \<turnstile> \<langle>fst esxs, (h, snd esxs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>fst es'xs', (h, snd es'xs')\<rangle> \<and> \<tau>moves0 P h (fst esxs) \<and> no_calls P h (fst esxs))"

abbreviation \<tau>red0t :: "(external_thread_action \<Rightarrow> (addr,thread_id,'x,heap,addr,obs_event option) thread_action) \<Rightarrow> 
  J_prog \<Rightarrow> heap \<Rightarrow> (expr \<times> locals) \<Rightarrow> (expr \<times> locals) \<Rightarrow> bool"
where "\<tau>red0t extTA P h \<equiv> (\<tau>red0 extTA P h)^++"

abbreviation \<tau>reds0t :: "(external_thread_action \<Rightarrow> (addr,thread_id,'x,heap,addr,obs_event option) thread_action) \<Rightarrow>
  J_prog \<Rightarrow> heap \<Rightarrow> (expr list \<times> locals) \<Rightarrow> (expr list \<times> locals) \<Rightarrow> bool"
where "\<tau>reds0t extTA P h \<equiv> (\<tau>reds0 extTA P h)^++"

abbreviation \<tau>red0r :: "(external_thread_action \<Rightarrow> (addr,thread_id,'x,heap,addr,obs_event option) thread_action) \<Rightarrow> 
  J_prog \<Rightarrow> heap \<Rightarrow> (expr \<times> locals) \<Rightarrow> (expr \<times> locals) \<Rightarrow> bool"
where "\<tau>red0r extTA P h \<equiv> (\<tau>red0 extTA P h)^**"

abbreviation \<tau>reds0r :: "(external_thread_action \<Rightarrow> (addr,thread_id,'x,heap,addr,obs_event option) thread_action) \<Rightarrow>
  J_prog \<Rightarrow> heap \<Rightarrow> (expr list \<times> locals) \<Rightarrow> (expr list \<times> locals) \<Rightarrow> bool"
where "\<tau>reds0r extTA P h \<equiv> (\<tau>reds0 extTA P h)^**"

lemma \<tau>red0_iff [iff]:
  "\<tau>red0 extTA P h (e, xs) (e', xs') = (extTA,P \<turnstile> \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle> \<and> \<tau>move0 P h e \<and> no_call P h e)"
by(simp add: \<tau>red0_def)

lemma \<tau>reds0_iff [iff]:
  "\<tau>reds0 extTA P h (es, xs) (es', xs') = (extTA,P \<turnstile> \<langle>es, (h, xs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', (h, xs')\<rangle> \<and> \<tau>moves0 P h es \<and> no_calls P h es)"
by(simp add: \<tau>reds0_def)

lemma \<tau>red0t_1step:
  "\<lbrakk> extTA,P \<turnstile> \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>; \<tau>move0 P h e; no_call P h e \<rbrakk>
  \<Longrightarrow> \<tau>red0t extTA P h (e, xs) (e', xs')"
by(blast intro: tranclp.r_into_trancl)

lemma \<tau>red0t_2step:
  "\<lbrakk> extTA,P \<turnstile> \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>; \<tau>move0 P h e; no_call P h e;
     extTA,P \<turnstile> \<langle>e', (h, xs')\<rangle> -\<epsilon>\<rightarrow> \<langle>e'', (h, xs'')\<rangle>; \<tau>move0 P h e'; no_call P h e' \<rbrakk>
  \<Longrightarrow> \<tau>red0t extTA P h (e, xs) (e'', xs'')"
by(blast intro: tranclp.trancl_into_trancl[OF \<tau>red0t_1step])

lemma \<tau>red1t_3step:
  "\<lbrakk> extTA,P \<turnstile> \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>; \<tau>move0 P h e; no_call P h e; 
     extTA,P \<turnstile> \<langle>e', (h, xs')\<rangle> -\<epsilon>\<rightarrow> \<langle>e'', (h, xs'')\<rangle>; \<tau>move0 P h e'; no_call P h e';
     extTA,P \<turnstile> \<langle>e'', (h, xs'')\<rangle> -\<epsilon>\<rightarrow> \<langle>e''', (h, xs''')\<rangle>; \<tau>move0 P h e''; no_call P h e'' \<rbrakk>
  \<Longrightarrow> \<tau>red0t extTA P h (e, xs) (e''', xs''')"
by(blast intro: tranclp.trancl_into_trancl[OF \<tau>red0t_2step])

lemma \<tau>reds0t_1step:
  "\<lbrakk> extTA,P \<turnstile> \<langle>es, (h, xs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', (h, xs')\<rangle>; \<tau>moves0 P h es; no_calls P h es \<rbrakk>
  \<Longrightarrow> \<tau>reds0t extTA P h (es, xs) (es', xs')"
by(blast intro: tranclp.r_into_trancl)

lemma \<tau>reds0t_2step:
  "\<lbrakk> extTA,P \<turnstile> \<langle>es, (h, xs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', (h, xs')\<rangle>; \<tau>moves0 P h es; no_calls P h es; 
     extTA,P \<turnstile> \<langle>es', (h, xs')\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es'', (h, xs'')\<rangle>; \<tau>moves0 P h es'; no_calls P h es' \<rbrakk>
  \<Longrightarrow> \<tau>reds0t extTA P h (es, xs) (es'', xs'')"
by(blast intro: tranclp.trancl_into_trancl[OF \<tau>reds0t_1step])

lemma \<tau>reds0t_3step:
  "\<lbrakk> extTA,P \<turnstile> \<langle>es, (h, xs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', (h, xs')\<rangle>; \<tau>moves0 P h es; no_calls P h es; 
     extTA,P \<turnstile> \<langle>es', (h, xs')\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es'', (h, xs'')\<rangle>; \<tau>moves0 P h es'; no_calls P h es';
     extTA,P \<turnstile> \<langle>es'', (h, xs'')\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es''', (h, xs''')\<rangle>; \<tau>moves0 P h es''; no_calls P h es'' \<rbrakk>
  \<Longrightarrow> \<tau>reds0t extTA P h (es, xs) (es''', xs''')"
by(blast intro: tranclp.trancl_into_trancl[OF \<tau>reds0t_2step])

lemma \<tau>red0r_1step:
  "\<lbrakk> extTA,P \<turnstile> \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>; \<tau>move0 P h e; no_call P h e \<rbrakk>
  \<Longrightarrow> \<tau>red0r extTA P h (e, xs) (e', xs')"
by(blast intro: r_into_rtranclp)

lemma \<tau>red0r_2step:
  "\<lbrakk> extTA,P \<turnstile> \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>; \<tau>move0 P h e; no_call P h e;
     extTA,P \<turnstile> \<langle>e', (h, xs')\<rangle> -\<epsilon>\<rightarrow> \<langle>e'', (h, xs'')\<rangle>; \<tau>move0 P h e'; no_call P h e' \<rbrakk>
  \<Longrightarrow> \<tau>red0r extTA P h (e, xs) (e'', xs'')"
by(blast intro: rtranclp.rtrancl_into_rtrancl[OF \<tau>red0r_1step])

lemma \<tau>red0r_3step:
  "\<lbrakk> extTA,P \<turnstile> \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>; \<tau>move0 P h e; no_call P h e; 
     extTA,P \<turnstile> \<langle>e', (h, xs')\<rangle> -\<epsilon>\<rightarrow> \<langle>e'', (h, xs'')\<rangle>; \<tau>move0 P h e'; no_call P h e';
     extTA,P \<turnstile> \<langle>e'', (h, xs'')\<rangle> -\<epsilon>\<rightarrow> \<langle>e''', (h, xs''')\<rangle>; \<tau>move0 P h e''; no_call P h e'' \<rbrakk>
  \<Longrightarrow> \<tau>red0r extTA P h (e, xs) (e''', xs''')"
by(blast intro: rtranclp.rtrancl_into_rtrancl[OF \<tau>red0r_2step])

lemma \<tau>reds0r_1step:
  "\<lbrakk> extTA,P \<turnstile> \<langle>es, (h, xs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', (h, xs')\<rangle>; \<tau>moves0 P h es; no_calls P h es \<rbrakk>
  \<Longrightarrow> \<tau>reds0r extTA P h (es, xs) (es', xs')"
by(blast intro: r_into_rtranclp)

lemma \<tau>reds0r_2step:
  "\<lbrakk> extTA,P \<turnstile> \<langle>es, (h, xs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', (h, xs')\<rangle>; \<tau>moves0 P h es; no_calls P h es; 
     extTA,P \<turnstile> \<langle>es', (h, xs')\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es'', (h, xs'')\<rangle>; \<tau>moves0 P h es'; no_calls P h es' \<rbrakk>
  \<Longrightarrow> \<tau>reds0r extTA P h (es, xs) (es'', xs'')"
by(blast intro: rtranclp.rtrancl_into_rtrancl[OF \<tau>reds0r_1step])

lemma \<tau>reds0r_3step:
  "\<lbrakk> extTA,P \<turnstile> \<langle>es, (h, xs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', (h, xs')\<rangle>; \<tau>moves0 P h es; no_calls P h es; 
     extTA,P \<turnstile> \<langle>es', (h, xs')\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es'', (h, xs'')\<rangle>; \<tau>moves0 P h es'; no_calls P h es';
     extTA,P \<turnstile> \<langle>es'', (h, xs'')\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es''', (h, xs''')\<rangle>; \<tau>moves0 P h es''; no_calls P h es'' \<rbrakk>
  \<Longrightarrow> \<tau>reds0r extTA P h (es, xs) (es''', xs''')"
by(blast intro: rtranclp.rtrancl_into_rtrancl[OF \<tau>reds0r_2step])

lemma \<tau>red0t_inj_\<tau>reds0t: "\<tau>red0t extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>reds0t extTA P h (e # es, xs) (e' # es, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl ListRed1)

lemma \<tau>reds0t_cons_\<tau>reds0t: "\<tau>reds0t extTA P h (es, xs) (es', xs') \<Longrightarrow> \<tau>reds0t extTA P h (Val v # es, xs) (Val v # es', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl ListRed2)

lemma \<tau>red0r_inj_\<tau>reds0r: "\<tau>red0r extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>reds0r extTA P h (e # es, xs) (e' # es, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl ListRed1)

lemma \<tau>reds0r_cons_\<tau>reds0r: "\<tau>reds0r extTA P h (es, xs) (es', xs') \<Longrightarrow> \<tau>reds0r extTA P h (Val v # es, xs) (Val v # es', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl ListRed2)

lemma NewArray_\<tau>red0t_xt:
  "\<tau>red0t extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P h (newA T\<lfloor>e\<rceil>, xs) (newA T\<lfloor>e'\<rceil>, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl NewArrayRed)

lemma Cast_\<tau>red0t_xt:
  "\<tau>red0t extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P h (Cast T e, xs) (Cast T e', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl CastRed)

lemma BinOp_\<tau>red0t_xt1:
  "\<tau>red0t extTA P h (e1, xs) (e1', xs') \<Longrightarrow> \<tau>red0t extTA P h (e1 \<guillemotleft>bop\<guillemotright> e2, xs) (e1' \<guillemotleft>bop\<guillemotright> e2, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl BinOpRed1)

lemma BinOp_\<tau>red0t_xt2:
  "\<tau>red0t extTA P h (e2, xs) (e2', xs') \<Longrightarrow> \<tau>red0t extTA P h (Val v \<guillemotleft>bop\<guillemotright> e2, xs) (Val v \<guillemotleft>bop\<guillemotright> e2', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl BinOpRed2)

lemma LAss_\<tau>red0t:
  "\<tau>red0t extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P h (V := e, xs) (V := e', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl LAssRed)

lemma AAcc_\<tau>red0t_xt1:
  "\<tau>red0t extTA P h (a, xs) (a', xs') \<Longrightarrow> \<tau>red0t extTA P h (a\<lfloor>i\<rceil>, xs) (a'\<lfloor>i\<rceil>, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl AAccRed1)

lemma AAcc_\<tau>red0t_xt2:
  "\<tau>red0t extTA P h (i, xs) (i', xs') \<Longrightarrow> \<tau>red0t extTA P h (Val a\<lfloor>i\<rceil>, xs) (Val a\<lfloor>i'\<rceil>, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl AAccRed2)

lemma AAss_\<tau>red0t_xt1:
  "\<tau>red0t extTA P h (a, xs) (a', xs') \<Longrightarrow> \<tau>red0t extTA P h (a\<lfloor>i\<rceil> := e, xs) (a'\<lfloor>i\<rceil> := e, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl AAssRed1)

lemma AAss_\<tau>red0t_xt2:
  "\<tau>red0t extTA P h (i, xs) (i', xs') \<Longrightarrow> \<tau>red0t extTA P h (Val a\<lfloor>i\<rceil> := e, xs) (Val a\<lfloor>i'\<rceil> := e, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl AAssRed2)

lemma AAss_\<tau>red0t_xt3:
  "\<tau>red0t extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P h (Val a\<lfloor>Val i\<rceil> := e, xs) (Val a\<lfloor>Val i\<rceil> := e', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl AAssRed3)

lemma ALength_\<tau>red0t_xt:
  "\<tau>red0t extTA P h (a, xs) (a', xs') \<Longrightarrow> \<tau>red0t extTA P h (a\<bullet>length, xs) (a'\<bullet>length, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl ALengthRed)

lemma FAcc_\<tau>red0t_xt:
  "\<tau>red0t extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P h (e\<bullet>F{D}, xs) (e'\<bullet>F{D}, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl FAccRed)

lemma FAss_\<tau>red0t_xt1:
  "\<tau>red0t extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P h (e\<bullet>F{D} := e2, xs) (e'\<bullet>F{D} := e2, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl FAssRed1)

lemma FAss_\<tau>red0t_xt2:
  "\<tau>red0t extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P h (Val v\<bullet>F{D} := e, xs) (Val v\<bullet>F{D} := e', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl FAssRed2)

lemma Call_\<tau>red0t_obj:
  "\<tau>red0t extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P h (e\<bullet>M(ps), xs) (e'\<bullet>M(ps), xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl CallObj)

lemma Call_\<tau>red0t_param:
  "\<tau>reds0t extTA P h (es, xs) (es', xs') \<Longrightarrow> \<tau>red0t extTA P h (Val v\<bullet>M(es), xs) (Val v\<bullet>M(es'), xs')"
by(induct rule: tranclp_induct2)(fastsimp intro: tranclp.trancl_into_trancl CallParams)+

lemma Block_\<tau>red0t_xt:
  "\<tau>red0t extTA P h (e, xs(V := vo)) (e', xs') \<Longrightarrow> \<tau>red0t extTA P h ({V:T=vo; e}, xs) ({V:T=xs' V; e'}, xs'(V := xs V))"
proof(induct rule: tranclp_induct2)
  case base thus ?case by(auto intro: BlockRed simp del: fun_upd_apply)
next
  case (step e' xs' e'' xs'')
  from `\<tau>red0 extTA P h (e', xs') (e'', xs'')` 
  have "extTA,P \<turnstile> \<langle>e',(h, xs')\<rangle> -\<epsilon>\<rightarrow> \<langle>e'',(h, xs'')\<rangle>" "\<tau>move0 P h e'" "no_call P h e'" by auto
  hence "extTA,P \<turnstile> \<langle>e',(h, xs'(V := xs V, V := xs' V))\<rangle> -\<epsilon>\<rightarrow> \<langle>e'',(h, xs'')\<rangle>" by simp
  from BlockRed[OF this, of T] `\<tau>move0 P h e'` `no_call P h e'`
  have "\<tau>red0 extTA P h ({V:T=xs' V; e'}, xs'(V := xs V)) ({V:T=xs'' V; e''}, xs''(V := xs V))" by(auto)
  with `\<tau>red0t extTA P h ({V:T=vo; e}, xs) ({V:T=xs' V; e'}, xs'(V := xs V))` show ?case ..
qed

lemma Sync_\<tau>red0t_xt:
  "\<tau>red0t extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P h (sync\<^bsub>V\<^esub> (e) e2, xs) (sync\<^bsub>V\<^esub> (e') e2, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl SynchronizedRed1)

lemma InSync_\<tau>red0t_xt:
  "\<tau>red0t extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P h (insync\<^bsub>V\<^esub> (a) e, xs) (insync\<^bsub>V\<^esub> (a) e', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl SynchronizedRed2)

lemma Seq_\<tau>red0t_xt:
  "\<tau>red0t extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P h (e;;e2, xs) (e';;e2, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl SeqRed)

lemma Cond_\<tau>red0t_xt:
  "\<tau>red0t extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P h (if (e) e1 else e2, xs) (if (e') e1 else e2, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl CondRed)

lemma Throw_\<tau>red0t_xt:
  "\<tau>red0t extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P h (throw e, xs) (throw e', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl ThrowRed)

lemma Try_\<tau>red0t_xt:
  "\<tau>red0t extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P h (try e catch(C V) e2, xs) (try e' catch(C V) e2, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl TryRed)

lemma NewArray_\<tau>red0r_xt:
  "\<tau>red0r extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P h (newA T\<lfloor>e\<rceil>, xs) (newA T\<lfloor>e'\<rceil>, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl NewArrayRed)

lemma Cast_\<tau>red0r_xt:
  "\<tau>red0r extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P h (Cast T e, xs) (Cast T e', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl CastRed)

lemma BinOp_\<tau>red0r_xt1:
  "\<tau>red0r extTA P h (e1, xs) (e1', xs') \<Longrightarrow> \<tau>red0r extTA P h (e1 \<guillemotleft>bop\<guillemotright> e2, xs) (e1' \<guillemotleft>bop\<guillemotright> e2, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl BinOpRed1)

lemma BinOp_\<tau>red0r_xt2:
  "\<tau>red0r extTA P h (e2, xs) (e2', xs') \<Longrightarrow> \<tau>red0r extTA P h (Val v \<guillemotleft>bop\<guillemotright> e2, xs) (Val v \<guillemotleft>bop\<guillemotright> e2', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl BinOpRed2)

lemma LAss_\<tau>red0r:
  "\<tau>red0r extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P h (V := e, xs) (V := e', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl LAssRed)

lemma AAcc_\<tau>red0r_xt1:
  "\<tau>red0r extTA P h (a, xs) (a', xs') \<Longrightarrow> \<tau>red0r extTA P h (a\<lfloor>i\<rceil>, xs) (a'\<lfloor>i\<rceil>, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl AAccRed1)

lemma AAcc_\<tau>red0r_xt2:
  "\<tau>red0r extTA P h (i, xs) (i', xs') \<Longrightarrow> \<tau>red0r extTA P h (Val a\<lfloor>i\<rceil>, xs) (Val a\<lfloor>i'\<rceil>, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl AAccRed2)

lemma AAss_\<tau>red0r_xt1:
  "\<tau>red0r extTA P h (a, xs) (a', xs') \<Longrightarrow> \<tau>red0r extTA P h (a\<lfloor>i\<rceil> := e, xs) (a'\<lfloor>i\<rceil> := e, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl AAssRed1)

lemma AAss_\<tau>red0r_xt2:
  "\<tau>red0r extTA P h (i, xs) (i', xs') \<Longrightarrow> \<tau>red0r extTA P h (Val a\<lfloor>i\<rceil> := e, xs) (Val a\<lfloor>i'\<rceil> := e, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl AAssRed2)

lemma AAss_\<tau>red0r_xt3:
  "\<tau>red0r extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P h (Val a\<lfloor>Val i\<rceil> := e, xs) (Val a\<lfloor>Val i\<rceil> := e', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl AAssRed3)

lemma ALength_\<tau>red0r_xt:
  "\<tau>red0r extTA P h (a, xs) (a', xs') \<Longrightarrow> \<tau>red0r extTA P h (a\<bullet>length, xs) (a'\<bullet>length, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl ALengthRed)

lemma FAcc_\<tau>red0r_xt:
  "\<tau>red0r extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P h (e\<bullet>F{D}, xs) (e'\<bullet>F{D}, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl FAccRed)

lemma FAss_\<tau>red0r_xt1:
  "\<tau>red0r extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P h (e\<bullet>F{D} := e2, xs) (e'\<bullet>F{D} := e2, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl FAssRed1)

lemma FAss_\<tau>red0r_xt2:
  "\<tau>red0r extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P h (Val v\<bullet>F{D} := e, xs) (Val v\<bullet>F{D} := e', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl FAssRed2)

lemma Call_\<tau>red0r_obj:
  "\<tau>red0r extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P h (e\<bullet>M(ps), xs) (e'\<bullet>M(ps), xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl CallObj)

lemma Call_\<tau>red0r_param:
  "\<tau>reds0r extTA P h (es, xs) (es', xs') \<Longrightarrow> \<tau>red0r extTA P h (Val v\<bullet>M(es), xs) (Val v\<bullet>M(es'), xs')"
by(induct rule: rtranclp_induct2)(fastsimp intro: rtranclp.rtrancl_into_rtrancl CallParams)+

lemma Block_\<tau>red0r_xt:
  "\<tau>red0r extTA P h (e, xs(V := vo)) (e', xs') \<Longrightarrow> \<tau>red0r extTA P h ({V:T=vo; e}, xs) ({V:T=xs' V; e'}, xs'(V := xs V))"
proof(induct rule: rtranclp_induct2)
  case refl thus ?case by(simp del: fun_upd_apply)(auto simp add: fun_upd_apply)
next
  case (step e' xs' e'' xs'')
  from `\<tau>red0 extTA P h (e', xs') (e'', xs'')` 
  have "extTA,P \<turnstile> \<langle>e',(h, xs')\<rangle> -\<epsilon>\<rightarrow> \<langle>e'',(h, xs'')\<rangle>" "\<tau>move0 P h e'" "no_call P h e'" by auto
  hence "extTA,P \<turnstile> \<langle>e',(h, xs'(V := xs V, V := xs' V))\<rangle> -\<epsilon>\<rightarrow> \<langle>e'',(h, xs'')\<rangle>" by simp
  from BlockRed[OF this, of T] `\<tau>move0 P h e'` `no_call P h e'`
  have "\<tau>red0 extTA P h ({V:T=xs' V; e'}, xs'(V := xs V)) ({V:T=xs'' V; e''}, xs''(V := xs V))" by auto
  with `\<tau>red0r extTA P h ({V:T=vo; e}, xs) ({V:T=xs' V; e'}, xs'(V := xs V))` show ?case ..
qed

lemma Sync_\<tau>red0r_xt:
  "\<tau>red0r extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P h (sync\<^bsub>V\<^esub> (e) e2, xs) (sync\<^bsub>V\<^esub> (e') e2, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl SynchronizedRed1)

lemma InSync_\<tau>red0r_xt:
  "\<tau>red0r extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P h (insync\<^bsub>V\<^esub> (a) e, xs) (insync\<^bsub>V\<^esub> (a) e', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl SynchronizedRed2)

lemma Seq_\<tau>red0r_xt:
  "\<tau>red0r extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P h (e;;e2, xs) (e';;e2, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl SeqRed)

lemma Cond_\<tau>red0r_xt:
  "\<tau>red0r extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P h (if (e) e1 else e2, xs) (if (e') e1 else e2, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl CondRed)

lemma Throw_\<tau>red0r_xt:
  "\<tau>red0r extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P h (throw e, xs) (throw e', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl ThrowRed)

lemma Try_\<tau>red0r_xt:
  "\<tau>red0r extTA P h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P h (try e catch(C V) e2, xs) (try e' catch(C V) e2, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl TryRed)

definition \<tau>Red0 :: "J_prog \<Rightarrow> heap \<Rightarrow> (expr \<times> expr list) \<Rightarrow> (expr \<times> expr list) \<Rightarrow> bool"
where "\<tau>Red0 P h ees e'es' = (P \<turnstile>0 \<langle>fst ees/snd ees, h\<rangle> -\<epsilon>\<rightarrow> \<langle>fst e'es'/snd e'es', h\<rangle> \<and> \<tau>Move0 P h ees)"

lemma \<tau>Red0_conv [iff]:
  "\<tau>Red0 P h (e, es) (e', es') = (P \<turnstile>0 \<langle>e/es, h\<rangle> -\<epsilon>\<rightarrow> \<langle>e'/es', h\<rangle> \<and> \<tau>Move0 P h (e, es))"
by(simp add: \<tau>Red0_def)

lemma \<tau>red0r_lcl_incr:
  "\<tau>red0r extTA P h (e, xs) (e', xs') \<Longrightarrow> dom xs \<subseteq> dom xs'"
by(induct rule: rtranclp_induct2)(auto dest: red_lcl_incr del: subsetI)

lemma \<tau>red0t_lcl_incr:
  "\<tau>red0t extTA P h (e, xs) (e', xs') \<Longrightarrow> dom xs \<subseteq> dom xs'"
by(rule \<tau>red0r_lcl_incr)(rule tranclp_into_rtranclp)

lemma \<tau>red0r_dom_lcl:
  assumes wwf: "wwf_J_prog P"
  shows "\<tau>red0r extTA P h (e, xs) (e', xs') \<Longrightarrow> dom xs' \<subseteq> dom xs \<union> fv e"
apply(induct rule: converse_rtranclp_induct2)
 apply blast
apply(clarsimp del: subsetI)
apply(frule red_dom_lcl)
 apply(drule red_fv_subset[OF wwf])
apply auto
done

lemma \<tau>red0t_dom_lcl:
  assumes wwf: "wwf_J_prog P"
  shows "\<tau>red0t extTA P h (e, xs) (e', xs') \<Longrightarrow> dom xs' \<subseteq> dom xs \<union> fv e"
by(rule \<tau>red0r_dom_lcl[OF wwf])(rule tranclp_into_rtranclp)

lemma \<tau>red0r_fv_subset:
  assumes wwf: "wwf_J_prog P"
  shows "\<tau>red0r extTA P h (e, xs) (e', xs') \<Longrightarrow> fv e' \<subseteq> fv e"
by(induct rule: converse_rtranclp_induct2)(auto dest: red_fv_subset[OF wwf])

lemma \<tau>red0t_fv_subset:
  assumes wwf: "wwf_J_prog P"
  shows "\<tau>red0t extTA P h (e, xs) (e', xs') \<Longrightarrow> fv e' \<subseteq> fv e"
by(rule \<tau>red0r_fv_subset[OF wwf])(rule tranclp_into_rtranclp)

abbreviation \<tau>Red0r :: "J_prog \<Rightarrow> heap \<Rightarrow> (expr \<times> expr list) \<Rightarrow> (expr \<times> expr list) \<Rightarrow> bool"
where "\<tau>Red0r P h \<equiv> (\<tau>Red0 P h)^**"

abbreviation \<tau>Red0t :: "J_prog \<Rightarrow> heap \<Rightarrow> (expr \<times> expr list) \<Rightarrow> (expr \<times> expr list) \<Rightarrow> bool"
where "\<tau>Red0t P h \<equiv> (\<tau>Red0 P h)^++"

lemma fixes e :: "('a, 'b) exp" and es :: "('a, 'b) exp list"
  shows \<tau>move0_not_call: "\<lbrakk> \<tau>move0 P h e; call e = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> \<not> synthesized_call P h aMvs"
  and \<tau>moves0_not_calls: "\<lbrakk> \<tau>moves0 P h es; calls es = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> \<not> synthesized_call P h aMvs"
apply(induct e and es)
apply(auto simp add: is_vals_conv append_eq_map_conv map_eq_append_conv split: split_if_asm)
apply(auto simp add: synthesized_call_def)
done

lemma fixes e :: "('a, 'b) exp" and es :: "('a, 'b) exp list"
  shows \<tau>move0_callD: "call e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> \<tau>move0 P h e \<longleftrightarrow> \<not> synthesized_call P h aMvs"
  and \<tau>moves0_callsD: "calls es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> \<tau>moves0 P h es \<longleftrightarrow> \<not> synthesized_call P h aMvs"
apply(induct e and es)
apply(auto split: split_if_asm simp add: is_vals_conv)
apply(auto simp add: synthesized_call_def map_eq_append_conv)
done

lemma \<tau>red0_into_\<tau>Red0:
  assumes red: "\<tau>red0 (extTA2J0 P) P h (e, empty) (e', xs')"
  shows "\<tau>Red0 P h (e, es) (e', es)"
proof -
  from red have red: "extTA2J0 P,P \<turnstile> \<langle>e, (h, empty)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>" and "\<tau>move0 P h e" and "no_call P h e" by auto
  hence "P \<turnstile>0 \<langle>e/es,h\<rangle> -\<epsilon>\<rightarrow> \<langle>e'/es,h\<rangle>"
    by-(erule red0Red,auto simp add: no_call_def)
  thus ?thesis using `\<tau>move0 P h e` by(auto)
qed

lemma \<tau>red0r_into_\<tau>Red0r:
  assumes wwf: "wwf_J_prog P"
  shows
  "\<lbrakk> \<tau>red0r (extTA2J0 P) P h (e, empty) (e'', empty); fv e = {} \<rbrakk>
  \<Longrightarrow> \<tau>Red0r P h (e, es) (e'', es)"
proof(induct e xs\<equiv>"empty :: locals" rule: converse_rtranclp_induct2)
  case refl show ?case by blast
next
  case (step e xs e' xs')
  from `\<tau>red0 (extTA2J0 P) P h (e, xs) (e', xs')`
  have red: "extTA2J0 P,P \<turnstile> \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>" and "\<tau>move0 P h e"  and "no_call P h e" by auto
  from wwf red have "fv e' \<subseteq> fv e" by(rule red_fv_subset)
  with `fv e = {}` have "fv e' = {}" by blast
  moreover from red_dom_lcl[OF red] `fv e = {}` `xs = empty`
  have "dom xs' = {}" by(auto split:split_if_asm)
  hence "xs' = empty" by(auto)
  ultimately have "\<tau>Red0r P h (e', es) (e'', es)" by(rule step)
  moreover from red `\<tau>move0 P h e` `xs' = empty` `xs = empty` `no_call P h e`
  have "\<tau>Red0 P h (e, es) (e', es)" by(auto simp add: no_call_def intro!: red0Red)
  ultimately show ?case by(blast intro: converse_rtranclp_into_rtranclp)
qed


lemma \<tau>red0t_into_\<tau>Red0t:
  assumes wwf: "wwf_J_prog P"
  shows
  "\<lbrakk> \<tau>red0t (extTA2J0 P) P h (e, empty) (e'', empty); fv e = {} \<rbrakk>
  \<Longrightarrow> \<tau>Red0t P h (e, es) (e'', es)"
proof(induct e xs\<equiv>"empty :: locals" rule: converse_tranclp_induct2)
  case (base e xs)
  thus ?case by(blast intro!: tranclp.r_into_trancl \<tau>red0_into_\<tau>Red0)
next
  case (step e xs e' xs')
  from `\<tau>red0 (extTA2J0 P) P h (e, xs) (e', xs')` 
  have red: "extTA2J0 P,P \<turnstile> \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>" and "\<tau>move0 P h e" and "no_call P h e" by auto
  from wwf red have "fv e' \<subseteq> fv e" by(rule red_fv_subset)
  with `fv e = {}` have "fv e' = {}" by blast
  moreover from red_dom_lcl[OF red] `fv e = {}` `xs = empty`
  have "dom xs' = {}" by(auto split:split_if_asm)
  hence "xs' = empty" by auto
  ultimately have "\<tau>Red0t P h (e', es) (e'', es)" by(rule step)
  moreover from red `\<tau>move0 P h e` `xs' = empty` `xs = empty` `no_call P h e`
  have "\<tau>Red0 P h (e, es) (e', es)" by(auto simp add: no_call_def intro!: red0Red)
  ultimately show ?case by(blast intro: tranclp_into_tranclp2)
qed


abbreviation \<tau>MOVE :: "'m prog \<Rightarrow> ((expr \<times> locals) \<times> heap, J_thread_action) trsys"
where "\<tau>MOVE \<equiv> \<lambda>P ((e, x), h) ta s'. \<tau>move0 P h e \<and> ta = \<epsilon>"
  
abbreviation \<tau>MOVE0 :: "'m prog \<Rightarrow> ((expr \<times> expr list) \<times> heap, J0_thread_action) trsys"
where "\<tau>MOVE0 \<equiv> \<lambda>P (es, h) ta s. \<tau>Move0 P h es \<and> ta = \<epsilon>"

abbreviation final_expr0 :: "expr \<times> expr list \<Rightarrow> bool" where
  "final_expr0 \<equiv> \<lambda>(e, es). final e \<and> es = []"

lemma red0_mthr: "multithreaded (mred0 P)"
apply(unfold_locales)
apply(auto elim!: red0.cases)
by(auto dest: red_new_thread_heap)

interpretation red0_mthr: multithreaded final_expr0 "mred0 P" for P
by(rule red0_mthr)

interpretation red_\<tau>mthr: \<tau>multithreaded final_expr "mred P" "\<tau>MOVE P" for P
by(unfold_locales)

interpretation red0_\<tau>mthr: \<tau>multithreaded final_expr0 "mred0 P" "\<tau>MOVE0 P" for P
.

lemma red0_final_thread_wf: "final_thread_wf final_expr0 (mred0 P)"
by(unfold_locales)(auto elim!: red0.cases)

interpretation red0_mthr: final_thread_wf final_expr0 "mred0 P" for P
by(rule red0_final_thread_wf)

lemma red_\<tau>mthr_wf: "\<tau>multithreaded_wf final_expr (mred P) (\<tau>MOVE P) wfs"
proof
  fix x1 m1 ta1 x1' m1'
  assume "mred P (x1, m1) ta1 (x1', m1')" "\<tau>MOVE P (x1, m1) ta1 (x1', m1')"
  thus "m1 = m1'" by(auto dest: \<tau>move0_heap_unchanged simp add: split_def)
qed(simp add: split_beta)

interpretation red_\<tau>mthr_wf: \<tau>multithreaded_wf final_expr "mred P" "\<tau>MOVE P" wfs for P wfs
by(rule red_\<tau>mthr_wf)

lemma red0_\<tau>mthr_wf: "\<tau>multithreaded_wf final_expr0 (mred0 P) (\<tau>MOVE0 P) wfs"
proof
  fix x1 m1 ta1 x1' m1'
  assume "mred0 P (x1, m1) ta1 (x1', m1')" "\<tau>MOVE0 P (x1, m1) ta1 (x1', m1')"
  thus "m1 = m1'" by(cases x1)(fastsimp elim!: red0.cases dest: \<tau>move0_heap_unchanged)
qed(simp add: split_beta)

interpretation red0_\<tau>mthr_wf: \<tau>multithreaded_wf final_expr0 "mred0 P" "\<tau>MOVE0 P" wfs for P wfs
by(rule red0_\<tau>mthr_wf)

end
