(*  Title:      JinjaThreads/Compiler/J0.thy
    Author:     Andreas Lochbihler
*)

header {* \chapter{Compilation}\label{cha:comp}
          The Jinja source language and small step semantics with explicit call stacks *}
theory J0 imports "../J/SmallStep" "../J/WWellForm" "../J/WellType" begin

declare widen_refT [elim]

primrec noRetBlock :: "('a, 'b) exp \<Rightarrow> bool"
  and noRetBlocks :: "('a, 'b) exp list \<Rightarrow> bool"
where
  "noRetBlock (new C) = True"
| "noRetBlock (newA T\<lfloor>e\<rceil>) = noRetBlock e"
| "noRetBlock (Cast T e) = noRetBlock e"
| "noRetBlock (Val v) = True"
| "noRetBlock (e1 \<guillemotleft>bop\<guillemotright> e2) = (noRetBlock e1 \<and> noRetBlock e2)"
| "noRetBlock (Var V) = True"
| "noRetBlock (V:=e) = noRetBlock e"
| "noRetBlock (a\<lfloor>i\<rceil>) = (noRetBlock a \<and> noRetBlock i)"
| "noRetBlock (a\<lfloor>i\<rceil> := e) = (noRetBlock a \<and> noRetBlock i \<and> noRetBlock e)"
| "noRetBlock (a\<bullet>length) = noRetBlock a"
| "noRetBlock (e\<bullet>F{D}) = noRetBlock e"
| "noRetBlock (e\<bullet>F{D} := e2) = (noRetBlock e \<and> noRetBlock e2)"
| "noRetBlock (e\<bullet>M(es)) = (noRetBlock e \<and> noRetBlocks es)"
| "noRetBlock {V:T=vo;e}\<^bsub>cr\<^esub> = (\<not> cr \<and> noRetBlock e)"
| "noRetBlock (sync\<^bsub>V\<^esub> (e1) e2) = (noRetBlock e1 \<and> noRetBlock e2)"
| "noRetBlock (insync\<^bsub>V\<^esub> (a) e) = (noRetBlock e)"
| "noRetBlock (e1;;e2) = (noRetBlock e1 \<and> noRetBlock e2)"
| "noRetBlock (if (b) e1 else e2) = (noRetBlock b \<and> noRetBlock e1 \<and> noRetBlock e2)"
| "noRetBlock (while (b) c) = (noRetBlock b \<and> noRetBlock c)"
| "noRetBlock (throw e) = noRetBlock e"
| "noRetBlock (try e1 catch(C V) e2) = (noRetBlock e1 \<and> noRetBlock e2)"

| "noRetBlocks [] = True"
| "noRetBlocks (e#es) = (noRetBlock e \<and> noRetBlocks es)"

lemma noRetBlocks_append [simp]: "noRetBlocks (es @ es') \<longleftrightarrow> noRetBlocks es \<and> noRetBlocks es'"
by(induct es) auto

lemma WT_noRetBlock: "P,E \<turnstile> e :: T \<Longrightarrow> noRetBlock e"
  and WTs_noRetBlocks: "P,E \<turnstile> es [::] Ts \<Longrightarrow> noRetBlocks es"
by(induct rule: WT_WTs.inducts) auto

lemma noRetBlock_blocks:
  "\<lbrakk> length Ts = length Vs; length vs = length Vs \<rbrakk>
  \<Longrightarrow> noRetBlock (blocks (Vs,Ts,vs,e)) = noRetBlock e"
by(induct Vs Ts vs e rule: blocks.induct) auto

lemma noRetBlocks_map_Val [simp]: "noRetBlocks (map Val vs)"
by(induct vs) auto

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
  "call ({V:T=vo; e}\<^bsub>cr\<^esub>) = call e"
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
  "inline_call f ({V:T=vo; e}\<^bsub>cr\<^esub>) = {V:T=vo; inline_call f e}\<^bsub>cr\<^esub>"
  "inline_call f (sync\<^bsub>V\<^esub> (o') e) = sync\<^bsub>V\<^esub> (inline_call f o') e"
  "inline_call f (insync\<^bsub>V\<^esub> (a) e) = insync\<^bsub>V\<^esub> (a) (inline_call f e)"
  "inline_call f (e;;e') = inline_call f e;;e'"
  "inline_call f (if (b) e else e') = (if (inline_call f b) e else e')"
  "inline_call f (while (b) e) = while (b) e"
  "inline_call f (throw e) = throw (inline_call f e)"
  "inline_call f (try e1 catch(C V) e2) = try inline_call f e1 catch(C V) e2"

  "inline_calls f [] = []"
  "inline_calls f (e#es) = (if is_val e then e # inline_calls f es else inline_call f e # es)"

lemma inline_calls_map_Val [simp]:
  "inline_calls f (map Val vs @ es) = map Val vs @ inline_calls f es"
by(induct vs, auto)

lemma inline_call_eq_Val_aux:
  "inline_call e E = Val v \<Longrightarrow> call E = \<lfloor>aMvs\<rfloor> \<Longrightarrow> e = Val v"
by(induct E)(auto split: split_if_asm)

lemmas inline_call_eq_Val [dest] = inline_call_eq_Val_aux inline_call_eq_Val_aux[OF sym, THEN sym]

lemma inline_calls_eq_empty [simp]: "inline_calls e es = [] \<longleftrightarrow> es = []"
by(cases es, auto)

lemma 
  fixes E :: "('a,'b) exp"
  fixes Es :: "('a,'b) exp list"
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
  "call e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> call (inline_call {v:T=vo; e'}\<^bsub>cr\<^esub> e) = call e'"
  "calls es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> calls (inline_calls {v:T=vo;e'}\<^bsub>cr\<^esub> es) = call e'"
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
where "synthesized_call P h = (\<lambda>(a, M, vs). is_external_call P (the (typeof\<^bsub>h\<^esub> (Addr a))) M (length vs))"

lemma synthesized_call_conv:
  "synthesized_call P h (a, M, vs) = is_external_call P (the (typeof\<^bsub>h\<^esub> (Addr a))) M (length vs)"
by(simp add: synthesized_call_def)


types
  J0_thread_action = "(addr,thread_id,(expr \<times> locals) \<times> (expr \<times> locals) list,heap,addr) thread_action"


definition extNTA2J0 :: "J_prog \<Rightarrow> (cname \<times> mname \<times> addr) \<Rightarrow> ((expr \<times> locals) \<times> (expr \<times> locals) list)"
where "extNTA2J0 P = (\<lambda>(C, M, a). let (pns, body) = snd (snd (snd (method P C M))) in ((body, [this \<mapsto> Addr a]), [(addr a\<bullet>M([]), empty)]))"

lemma extNTA2J0_iff [simp]:
  "extNTA2J0 P (C, M, a) = ((snd (snd (snd (snd (method P C M)))), [this \<mapsto> Addr a]), [(addr a\<bullet>M([]), empty)])"
by(simp add: extNTA2J0_def split_def)

abbreviation extTA2J0 :: "J_prog \<Rightarrow> external_thread_action \<Rightarrow> J0_thread_action"
where "extTA2J0 P \<equiv> convert_extTA (extNTA2J0 P)"

inductive red0 :: "J_prog \<Rightarrow> (expr \<times> locals) \<Rightarrow> (expr \<times> locals) list \<Rightarrow> heap \<Rightarrow>
                           J0_thread_action \<Rightarrow> (expr \<times> locals) \<Rightarrow> (expr \<times> locals) list \<Rightarrow> heap \<Rightarrow> bool"
                ("_ \<turnstile>0 ((1\<langle>_'/_,/_\<rangle>) -_\<rightarrow>/ (1\<langle>_'/_,/_\<rangle>))" [51,0,0,0,0,0,0,0] 81)
for P ::J_prog
where

  red0Red:
  "\<lbrakk> extTA2J0 P,P \<turnstile> \<langle>e, (h, x)\<rangle> -ta\<rightarrow> \<langle>e', (h', x')\<rangle>; \<forall>aMvs. call e = \<lfloor>aMvs\<rfloor> \<longrightarrow> synthesized_call P h aMvs \<rbrakk>
  \<Longrightarrow> P \<turnstile>0 \<langle>(e, x)/exs, h\<rangle> -ta\<rightarrow> \<langle>(e', x')/exs, h'\<rangle>"

| red0Call:
  "\<lbrakk> call e = \<lfloor>(a, M, vs)\<rfloor>; h a = \<lfloor>Obj C fs\<rfloor>; P \<turnstile> C sees M:Ts\<rightarrow>T = (pns, body) in D; 
     size vs = size pns; size Ts = size pns \<rbrakk>
  \<Longrightarrow> P \<turnstile>0 \<langle>(e, x)/exs, h\<rangle> -\<epsilon>\<rightarrow> \<langle>(blocks(pns, Ts, vs, body), [this \<mapsto> Addr a])/(e, x)#exs, h\<rangle>"

| red0Return:
  "\<lbrakk> call e = \<lfloor>aMvs\<rfloor>; final e' \<rbrakk>
  \<Longrightarrow> P \<turnstile>0 \<langle>(e', x')/(e, x)#exs, h\<rangle> -\<epsilon>\<rightarrow> \<langle>(inline_call e' e, x)/exs, h\<rangle>"

lemma fv_extRet2J [simp]: "fv (extRet2J va) = {}"
by(cases va) simp_all

lemma assumes wf: "wwf_J_prog P"
  shows red_fv_subset: "extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> fv e' \<subseteq> fv e"
  and reds_fvs_subset: "extTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> fvs es' \<subseteq> fvs es"
(* apply(induct rule: red_reds.inducts)
apply(fastsimp)+
defer -- RedCall
apply(fastsimp)+
. *)
proof(induct rule: red_reds.inducts)
  case (RedCall s a C fs M vs Ts T pns body D)
  hence "fv body \<subseteq> {this} \<union> set pns"
    using wf by(fastsimp dest!:sees_wf_mdecl simp:wf_mdecl_def)
  with RedCall show ?case by fastsimp
qed(fastsimp)+

declare domIff[iff del]

lemma assumes wwf: "wwf_J_prog P"
  shows red_fv_ok: "\<lbrakk> extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; fv e \<subseteq> dom (lcl s) \<rbrakk> \<Longrightarrow> fv e' \<subseteq> dom (lcl s')"
  and reds_fvs_ok: "\<lbrakk> extTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; fvs es \<subseteq> dom (lcl s) \<rbrakk> \<Longrightarrow> fvs es' \<subseteq> dom (lcl s')"
proof(induct rule: red_reds.inducts)
  case (RedCall s a C fs M vs Ts T pns body D)
  from `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D` have "wwf_J_mdecl P D (M,Ts,t,pns,body)"
    by(auto dest!: sees_wf_mdecl[OF wwf] simp add: wf_mdecl_def)
  with RedCall show ?case by(auto)
next
  case (BlockRed e h x V vo ta e' h' x' T cr)
  note red = `extTA,P \<turnstile> \<langle>e,(h, x(V := vo))\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>`
  hence "fv e' \<subseteq> fv e" by(auto dest: red_fv_subset[OF wwf] del: subsetI)
  moreover from ` fv {V:T=vo; e}\<^bsub>cr\<^esub> \<subseteq> dom (lcl (h, x))`
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

end
