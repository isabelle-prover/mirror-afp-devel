(*  Title:      JinjaThreads/J/SmallStep.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

header {* \isaheader{Small Step Semantics} *}

theory SmallStep imports
  Expr
  State
  "../Common/ExternalCall"
begin

consts blocks :: "'a list * ty list * val list * ('a,'b) exp \<Rightarrow> ('a,'b) exp"
recdef blocks "measure(\<lambda>(Vs,Ts,vs,e). size Vs)"
 "blocks(V#Vs, T#Ts, v#vs, e) = {V:T=\<lfloor>v\<rfloor>; blocks(Vs,Ts,vs,e)}"
 "blocks([],[],[],e) = e"


lemma [simp]:
  "\<lbrakk> size vs = size Vs; size Ts = size Vs \<rbrakk> \<Longrightarrow> fv(blocks(Vs,Ts,vs,e)) = fv e - set Vs"
(*<*)
apply(induct rule:blocks.induct)
apply simp_all
apply blast
done
(*>*)

lemma expr_locks_blocks:
  "\<lbrakk> length vs = length pns; length Ts = length pns \<rbrakk>
  \<Longrightarrow> expr_locks (blocks (pns, Ts, vs, e)) = expr_locks e"
by(induct pns Ts vs e rule: blocks.induct)(auto)

types
  J_thread_action = "(addr,thread_id,expr \<times> locals,heap,addr,obs_event option) thread_action"

translations
  (type) "J_thread_action" <= (type) "(nat,nat,expr \<times> (String.literal \<rightharpoonup> val),heap,nat,obs_event option) thread_action"

definition extNTA2J :: "J_prog \<Rightarrow> (cname \<times> mname \<times> addr) \<Rightarrow> expr \<times> locals"
where "extNTA2J P = (\<lambda>(C, M, a). let (D,Ts,T,pns,body) = method P C M
                                 in ({this:Class D=\<lfloor>Addr a\<rfloor>; body}, empty))"

lemma extNTA2J_iff [simp]:
  "extNTA2J P (C, M, a) = ({this:Class (fst (method P C M))=\<lfloor>Addr a\<rfloor>; snd (snd (snd (snd (method P C M))))}, empty)"
by(simp add: extNTA2J_def split_beta)

abbreviation extTA2J :: "J_prog \<Rightarrow> external_thread_action \<Rightarrow> J_thread_action"
where "extTA2J P \<equiv> convert_extTA (extNTA2J P)"

primrec extRet2J :: "val + addr \<Rightarrow> ('a, 'b) exp"
where
  "extRet2J (Inl v) = Val v"
| "extRet2J (Inr a) = Throw a"

text{* Locking mechanism:
  The expression on which the thread is synchronized is evaluated first to a value.
  If this expression evaluates to null, a null pointer expression is thrown.
  If this expression evaluates to an address, a lock must be obtained on this address, the
  sync expression is rewritten to insync.
  For insync expressions, the body expression may be evaluated.
  If the body expression is only a value or a thrown exception, the lock is released and
  the synchronized expression reduces to the body's expression. This is the normal Java semantics,
  not the one as presented in LNCS 1523, Cenciarelli/Knapp/Reus/Wirsing. There
  the expression on which the thread synchronized is evaluated except for the last step.
  If the thread can obtain the lock on the object immediately after the last evaluation step, the evaluation is
  done and the lock acquired. If the lock cannot be obtained, the evaluation step is discarded. If another thread
  changes the evaluation result of this last step, the thread then will try to synchronize on the new object. *}

inductive red :: "(external_thread_action \<Rightarrow> (addr,thread_id,'x,heap,addr,obs_event option) thread_action) \<Rightarrow> J_prog \<Rightarrow> 
                 expr \<Rightarrow> (heap \<times> locals) \<Rightarrow> (addr,thread_id,'x,heap,addr,obs_event option) thread_action \<Rightarrow> expr \<Rightarrow> (heap \<times> locals) \<Rightarrow> bool"
                ("_,_ \<turnstile> ((1\<langle>_,/_\<rangle>) -_\<rightarrow>/ (1\<langle>_,/_\<rangle>))" [51,51,0,0,0,0,0] 81)
 and reds ::  "(external_thread_action \<Rightarrow> (addr,thread_id,'x,heap,addr,obs_event option) thread_action) \<Rightarrow> J_prog \<Rightarrow>
                 expr list \<Rightarrow> (heap \<times> locals) \<Rightarrow> (addr,thread_id,'x,heap,addr,obs_event option) thread_action \<Rightarrow> expr list \<Rightarrow> (heap \<times> locals) \<Rightarrow> bool"
               ("_,_ \<turnstile> ((1\<langle>_,/_\<rangle>) [-_\<rightarrow>]/ (1\<langle>_,/_\<rangle>))" [51,51,0,0,0,0,0] 81)
for extTA :: "external_thread_action \<Rightarrow> (addr,thread_id,'x,heap,addr,obs_event option) thread_action" and P :: J_prog
where
  RedNew:
  "\<lbrakk> new_Addr h = Some a; P \<turnstile> C has_fields FDTs; h' = h(a\<mapsto>(Obj C (init_fields FDTs))) \<rbrakk>
  \<Longrightarrow> extTA,P \<turnstile> \<langle>new C, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>addr a, (h', l)\<rangle>"

| RedNewFail:
  "new_Addr (hp s) = None \<Longrightarrow>
  extTA,P \<turnstile> \<langle>new C, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW OutOfMemory, s\<rangle>"

| NewArrayRed:
  "extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>newA T\<lfloor>e\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>newA T\<lfloor>e'\<rceil>, s'\<rangle>"

| RedNewArray:
  "\<lbrakk> new_Addr h = Some a; i \<ge> 0; h' = h(a \<mapsto> (Arr T (replicate (nat i) (default_val T)))) \<rbrakk>
  \<Longrightarrow> extTA,P \<turnstile> \<langle>newA T\<lfloor>Val (Intg i)\<rceil>, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>addr a, (h', l)\<rangle>"

| RedNewArrayNegative:
  "i < 0 \<Longrightarrow> extTA,P \<turnstile> \<langle>newA T\<lfloor>Val (Intg i)\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NegativeArraySize, s\<rangle>"

| RedNewArrayFail:
  "\<lbrakk> new_Addr h = None; i \<ge> 0 \<rbrakk>
  \<Longrightarrow> extTA,P \<turnstile> \<langle>newA T\<lfloor>Val (Intg i)\<rceil>, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW OutOfMemory, (h, l)\<rangle>"

| CastRed:
  "extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>Cast C e, s\<rangle> -ta\<rightarrow> \<langle>Cast C e', s'\<rangle>"

| RedCast:
 "\<lbrakk> typeof\<^bsub>hp s\<^esub> v = \<lfloor>U\<rfloor>; P \<turnstile> U \<le> T \<rbrakk>
  \<Longrightarrow> extTA,P \<turnstile> \<langle>Cast T (Val v), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| RedCastFail:
  "\<lbrakk> typeof\<^bsub>hp s\<^esub> v = \<lfloor>U\<rfloor>; \<not> P \<turnstile> U \<le> T \<rbrakk>
  \<Longrightarrow> extTA,P \<turnstile> \<langle>Cast T (Val v), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ClassCast, s\<rangle>"

| BinOpRed1:
  "extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>e \<guillemotleft>bop\<guillemotright> e2, s\<rangle> -ta\<rightarrow> \<langle>e' \<guillemotleft>bop\<guillemotright> e2, s'\<rangle>"

| BinOpRed2:
  "extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>(Val v) \<guillemotleft>bop\<guillemotright> e, s\<rangle> -ta\<rightarrow> \<langle>(Val v) \<guillemotleft>bop\<guillemotright> e', s'\<rangle>"

| RedBinOp:
  "binop bop v1 v2 = Some v \<Longrightarrow>
  extTA,P \<turnstile> \<langle>(Val v1) \<guillemotleft>bop\<guillemotright> (Val v2), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| RedVar:
  "lcl s V = Some v \<Longrightarrow>
  extTA,P \<turnstile> \<langle>Var V, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| LAssRed:
  "extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>V:=e, s\<rangle> -ta\<rightarrow> \<langle>V:=e', s'\<rangle>"

| RedLAss:
  "extTA,P \<turnstile> \<langle>V:=(Val v), (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>unit, (h, l(V \<mapsto> v))\<rangle>"

| AAccRed1:
  "extTA,P \<turnstile> \<langle>a, s\<rangle> -ta\<rightarrow> \<langle>a', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>a\<lfloor>i\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>a'\<lfloor>i\<rceil>, s'\<rangle>"

| AAccRed2:
  "extTA,P \<turnstile> \<langle>i, s\<rangle> -ta\<rightarrow> \<langle>i', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>(Val a)\<lfloor>i\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>(Val a)\<lfloor>i'\<rceil>, s'\<rangle>"

| RedAAccNull:
  "extTA,P \<turnstile> \<langle>null\<lfloor>Val i\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| RedAAccBounds:
  "\<lbrakk> hp s a = Some(Arr T el); i < 0 \<or> i \<ge> int (length el) \<rbrakk>
  \<Longrightarrow> extTA,P \<turnstile> \<langle>(addr a)\<lfloor>Val (Intg i)\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ArrayIndexOutOfBounds, s\<rangle>"

| RedAAcc:
  "\<lbrakk> hp s a = Some(Arr T el); i \<ge> 0; i < int (length el) \<rbrakk>
  \<Longrightarrow> extTA,P \<turnstile> \<langle>(addr a)\<lfloor>Val (Intg i)\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val (el ! nat i), s\<rangle>"

| AAssRed1:
  "extTA,P \<turnstile> \<langle>a, s\<rangle> -ta\<rightarrow> \<langle>a', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>a\<lfloor>i\<rceil> := e, s\<rangle> -ta\<rightarrow> \<langle>a'\<lfloor>i\<rceil> := e, s'\<rangle>"

| AAssRed2:
  "extTA,P \<turnstile> \<langle>i, s\<rangle> -ta\<rightarrow> \<langle>i', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>(Val a)\<lfloor>i\<rceil> := e, s\<rangle> -ta\<rightarrow> \<langle>(Val a)\<lfloor>i'\<rceil> := e, s'\<rangle>"

| AAssRed3:
  "extTA,P \<turnstile> \<langle>(e::expr), s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>(Val a)\<lfloor>Val i\<rceil> := e, s\<rangle> -ta\<rightarrow> \<langle>(Val a)\<lfloor>Val i\<rceil> := e', s'\<rangle>"

| RedAAssNull:
  "extTA,P \<turnstile> \<langle>null\<lfloor>Val i\<rceil> := (Val e::expr), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| RedAAssBounds:
  "\<lbrakk> hp s a = Some(Arr T el); i < 0 \<or> i \<ge> int (length el) \<rbrakk>
  \<Longrightarrow> extTA,P \<turnstile> \<langle>(addr a)\<lfloor>Val (Intg i)\<rceil> := (Val e::expr), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ArrayIndexOutOfBounds, s\<rangle>"

| RedAAssStore:
  "\<lbrakk> hp s a = Some(Arr T el); i \<ge> 0; i < int (length el); typeof\<^bsub>hp s\<^esub> w = \<lfloor>U\<rfloor>; \<not> (P \<turnstile> U \<le> T) \<rbrakk>
  \<Longrightarrow> extTA,P \<turnstile> \<langle>(addr a)\<lfloor>Val (Intg i)\<rceil> := (Val w::expr), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ArrayStore, s\<rangle>"

| RedAAss:
  "\<lbrakk> h a = Some(Arr T el); i \<ge> 0; i < int (length el); typeof\<^bsub>h\<^esub> w = Some U; P \<turnstile> U \<le> T;
    h' = h(a \<mapsto> (Arr T (el[nat i := w]))) \<rbrakk>
  \<Longrightarrow> extTA,P \<turnstile> \<langle>(addr a)\<lfloor>Val (Intg i)\<rceil> := Val w::expr, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>unit, (h', l)\<rangle>"

| ALengthRed:
  "extTA,P \<turnstile> \<langle>a, s\<rangle> -ta\<rightarrow> \<langle>a', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>a\<bullet>length, s\<rangle> -ta\<rightarrow> \<langle>a'\<bullet>length, s'\<rangle>"

| RedALength:
  "hp s a = \<lfloor>Arr T el\<rfloor> \<Longrightarrow> extTA,P \<turnstile> \<langle>addr a\<bullet>length, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val (Intg (int (length el))), s\<rangle>"

| RedALengthNull:
  "extTA,P \<turnstile> \<langle>null\<bullet>length, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| FAccRed:
  "extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>e\<bullet>F{D}, s\<rangle> -ta\<rightarrow> \<langle>e'\<bullet>F{D}, s'\<rangle>"

| RedFAcc:
  "\<lbrakk> hp s a = Some(Obj C fs); fs(F,D) = Some v \<rbrakk>
  \<Longrightarrow> extTA,P \<turnstile> \<langle>(addr a)\<bullet>F{D}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| RedFAccNull:
  "extTA,P \<turnstile> \<langle>null\<bullet>F{D}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| FAssRed1:
  "extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>e\<bullet>F{D}:=e2, s\<rangle> -ta\<rightarrow> \<langle>e'\<bullet>F{D}:=e2, s'\<rangle>"

| FAssRed2:
  "extTA,P \<turnstile> \<langle>(e::expr), s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>Val v\<bullet>F{D}:=e, s\<rangle> -ta\<rightarrow> \<langle>Val v\<bullet>F{D}:=e', s'\<rangle>"

| RedFAss:
  "h a = Some(Obj C fs) \<Longrightarrow>
  extTA,P \<turnstile> \<langle>(addr a)\<bullet>F{D}:=(Val v :: expr), (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>unit, (h(a \<mapsto> (Obj C (fs((F,D) \<mapsto> v)))), l)\<rangle>"

| RedFAssNull:
  "extTA,P \<turnstile> \<langle>null\<bullet>F{D}:=Val v::expr, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| CallObj:
  "extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>e\<bullet>M(es), s\<rangle> -ta\<rightarrow> \<langle>e'\<bullet>M(es), s'\<rangle>"

| CallParams:
  "extTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow>
  extTA,P \<turnstile> \<langle>(Val v)\<bullet>M(es),s\<rangle> -ta\<rightarrow> \<langle>(Val v)\<bullet>M(es'),s'\<rangle>"

| RedCall:
  "\<lbrakk> hp s a = \<lfloor>Obj C fs\<rfloor>; \<not> is_external_call P (Class C) M; P \<turnstile> C sees M:Ts\<rightarrow>T = (pns,body) in D; 
    size vs = size pns; size Ts = size pns \<rbrakk>
  \<Longrightarrow> extTA,P \<turnstile> \<langle>(addr a)\<bullet>M(map Val vs), s\<rangle> -\<epsilon>\<rightarrow> \<langle>blocks(this#pns, Class D#Ts, Addr a#vs, body), s\<rangle>"

| RedCallExternal:
  "\<lbrakk> typeof\<^bsub>hp s\<^esub> (Addr a) = \<lfloor>T\<rfloor>; is_external_call P T M; P \<turnstile> \<langle>a\<bullet>M(vs), hp s\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>;
     ta' = extTA ta; e' = extRet2J va; s' = (h', lcl s) \<rbrakk>
  \<Longrightarrow> extTA,P \<turnstile> \<langle>(addr a)\<bullet>M(map Val vs), s\<rangle> -ta'\<rightarrow> \<langle>e', s'\<rangle>"

| RedCallNull:
  "extTA,P \<turnstile> \<langle>null\<bullet>M(map Val vs), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| BlockRed:
  "extTA,P \<turnstile> \<langle>e, (h, l(V:=vo))\<rangle> -ta\<rightarrow> \<langle>e', (h', l')\<rangle>
  \<Longrightarrow> extTA,P \<turnstile> \<langle>{V:T=vo; e}, (h, l)\<rangle> -ta\<rightarrow> \<langle>{V:T=l' V; e'}, (h', l'(V := l V))\<rangle>"

| RedBlock:
  "extTA,P \<turnstile> \<langle>{V:T=vo; Val u}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val u, s\<rangle>"

| SynchronizedRed1:
  "extTA,P \<turnstile> \<langle>o', s\<rangle> -ta\<rightarrow> \<langle>o'', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>sync(o') e, s\<rangle> -ta\<rightarrow> \<langle>sync(o'') e, s'\<rangle>"

| SynchronizedNull:
  "extTA,P \<turnstile> \<langle>sync(null) e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| LockSynchronized:
  "hp s a = \<lfloor>arrobj\<rfloor> \<Longrightarrow> extTA,P \<turnstile> \<langle>sync(addr a) e, s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Lock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub>Synchronization a\<rbrace>\<rightarrow> \<langle>insync(a) e, s\<rangle>"

| SynchronizedRed2:
  "extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>insync(a) e, s\<rangle> -ta\<rightarrow> \<langle>insync(a) e', s'\<rangle>"

| UnlockSynchronized:
  "extTA,P \<turnstile> \<langle>insync(a) (Val v), s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub>Synchronization a\<rbrace>\<rightarrow> \<langle>Val v, s\<rangle>"

| SeqRed:
  "extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>e;;e2, s\<rangle> -ta\<rightarrow> \<langle>e';;e2, s'\<rangle>"

| RedSeq:
  "extTA,P \<turnstile> \<langle>(Val v);;e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>e, s\<rangle>"

| CondRed:
  "extTA,P \<turnstile> \<langle>b, s\<rangle> -ta\<rightarrow> \<langle>b', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>if (b) e1 else e2, s\<rangle> -ta\<rightarrow> \<langle>if (b') e1 else e2, s'\<rangle>"

| RedCondT:
  "extTA,P \<turnstile> \<langle>if (true) e1 else e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>e1, s\<rangle>"

| RedCondF:
  "extTA,P \<turnstile> \<langle>if (false) e1 else e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>e2, s\<rangle>"

| RedWhile:
  "extTA,P \<turnstile> \<langle>while(b) c, s\<rangle> -\<epsilon>\<rightarrow> \<langle>if (b) (c;;while(b) c) else unit, s\<rangle>"

| ThrowRed:
  "extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>throw e, s\<rangle> -ta\<rightarrow> \<langle>throw e', s'\<rangle>"

| RedThrowNull:
  "extTA,P \<turnstile> \<langle>throw null, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| TryRed:
  "extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>try e catch(C V) e2, s\<rangle> -ta\<rightarrow> \<langle>try e' catch(C V) e2, s'\<rangle>"

| RedTry:
  "extTA,P \<turnstile> \<langle>try (Val v) catch(C V) e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| RedTryCatch:
  "\<lbrakk> hp s a = Some(Obj D fs); P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> extTA,P \<turnstile> \<langle>try (Throw a) catch(C V) e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>{V:Class C=\<lfloor>Addr a\<rfloor>; e2}, s\<rangle>"

| RedTryFail:
  "\<lbrakk> hp s a = Some(Obj D fs); \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> extTA,P \<turnstile> \<langle>try (Throw a) catch(C V) e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"

| ListRed1:
  "extTA,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  extTA,P \<turnstile> \<langle>e#es,s\<rangle> [-ta\<rightarrow>] \<langle>e'#es,s'\<rangle>"

| ListRed2:
  "extTA,P \<turnstile> \<langle>es,s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow>
  extTA,P \<turnstile> \<langle>Val v # es,s\<rangle> [-ta\<rightarrow>] \<langle>Val v # es',s'\<rangle>"

-- "Exception propagation"

| NewArrayThrow: "extTA,P \<turnstile> \<langle>newA T\<lfloor>Throw a\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| CastThrow: "extTA,P \<turnstile> \<langle>Cast C (Throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| BinOpThrow1: "extTA,P \<turnstile> \<langle>(Throw a) \<guillemotleft>bop\<guillemotright> e\<^isub>2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| BinOpThrow2: "extTA,P \<turnstile> \<langle>(Val v\<^isub>1) \<guillemotleft>bop\<guillemotright> (Throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| LAssThrow: "extTA,P \<turnstile> \<langle>V:=(Throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| AAccThrow1: "extTA,P \<turnstile> \<langle>(Throw a)\<lfloor>i\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| AAccThrow2: "extTA,P \<turnstile> \<langle>(Val v)\<lfloor>Throw a\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| AAssThrow1: "extTA,P \<turnstile> \<langle>(Throw a)\<lfloor>i\<rceil> := e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| AAssThrow2: "extTA,P \<turnstile> \<langle>(Val v)\<lfloor>Throw a\<rceil> := e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| AAssThrow3: "extTA,P \<turnstile> \<langle>(Val v)\<lfloor>Val i\<rceil> := Throw a :: expr, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| ALengthThrow: "extTA,P \<turnstile> \<langle>(Throw a)\<bullet>length, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| FAccThrow: "extTA,P \<turnstile> \<langle>(Throw a)\<bullet>F{D}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| FAssThrow1: "extTA,P \<turnstile> \<langle>(Throw a)\<bullet>F{D}:=e\<^isub>2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| FAssThrow2: "extTA,P \<turnstile> \<langle>Val v\<bullet>F{D}:=(Throw a::expr), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| CallThrowObj: "extTA,P \<turnstile> \<langle>(Throw a)\<bullet>M(es), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| CallThrowParams: "\<lbrakk> es = map Val vs @ Throw a # es' \<rbrakk> \<Longrightarrow> extTA,P \<turnstile> \<langle>(Val v)\<bullet>M(es), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| BlockThrow: "extTA,P \<turnstile> \<langle>{V:T=vo; Throw a}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| SynchronizedThrow1: "extTA,P \<turnstile> \<langle>sync(Throw a) e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| SynchronizedThrow2: "extTA,P \<turnstile> \<langle>insync(a) Throw ad, s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub>Synchronization a\<rbrace>\<rightarrow> \<langle>Throw ad, s\<rangle>"
| SeqThrow: "extTA,P \<turnstile> \<langle>(Throw a);;e\<^isub>2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| CondThrow: "extTA,P \<turnstile> \<langle>if (Throw a) e\<^isub>1 else e\<^isub>2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| ThrowThrow: "extTA,P \<turnstile> \<langle>throw(Throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"

inductive_cases red_cases:
  "extTA,P \<turnstile> \<langle>new C, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P \<turnstile> \<langle>newA T\<lfloor>e\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P \<turnstile> \<langle>Cast T e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P \<turnstile> \<langle>e \<guillemotleft>bop\<guillemotright> e', s\<rangle> -ta\<rightarrow> \<langle>e'', s'\<rangle>"
  "extTA,P \<turnstile> \<langle>Var V, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P \<turnstile> \<langle>V:=e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P \<turnstile> \<langle>a\<lfloor>i\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P \<turnstile> \<langle>a\<lfloor>i\<rceil> := e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P \<turnstile> \<langle>a\<bullet>length, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P \<turnstile> \<langle>e\<bullet>F{D}, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P \<turnstile> \<langle>e\<bullet>F{D} := e', s\<rangle> -ta\<rightarrow> \<langle>e'', s'\<rangle>"
  "extTA,P \<turnstile> \<langle>e\<bullet>M(es), s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P \<turnstile> \<langle>{V:T=vo; e}, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P \<turnstile> \<langle>sync(o') e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P \<turnstile> \<langle>insync(a) e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P \<turnstile> \<langle>e;;e', s\<rangle> -ta\<rightarrow> \<langle>e'', s'\<rangle>"
  "extTA,P \<turnstile> \<langle>if (b) e1 else e2, s \<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P \<turnstile> \<langle>while (b) e, s \<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P \<turnstile> \<langle>throw e, s \<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P \<turnstile> \<langle>try e catch(C V) e', s\<rangle> -ta\<rightarrow> \<langle>e'', s'\<rangle>"

inductive_cases reds_cases:
  "extTA,P \<turnstile> \<langle>e # es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>"


abbreviation red' :: "J_prog \<Rightarrow> expr \<Rightarrow> (heap \<times> locals) \<Rightarrow> J_thread_action \<Rightarrow> expr \<Rightarrow> (heap \<times> locals) \<Rightarrow> bool"
                ("_ \<turnstile> ((1\<langle>_,/_\<rangle>) -_\<rightarrow>/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0,0] 81)
where "red' P \<equiv> red (extTA2J P) P"

abbreviation reds' :: "J_prog \<Rightarrow> expr list \<Rightarrow> (heap \<times> locals) \<Rightarrow> J_thread_action \<Rightarrow> expr list \<Rightarrow> (heap \<times> locals) \<Rightarrow> bool"
               ("_ \<turnstile> ((1\<langle>_,/_\<rangle>) [-_\<rightarrow>]/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0,0] 81)
where "reds' P \<equiv> reds (extTA2J P) P"

subsection{* The reflexive transitive closure *}

abbreviation
  Step :: "(external_thread_action \<Rightarrow> (addr,thread_id,'x,heap,addr,obs_event option) thread_action) \<Rightarrow> J_prog \<Rightarrow>
           expr \<Rightarrow> (heap \<times> locals) \<Rightarrow> ((addr,thread_id,'x,heap,addr,obs_event option) thread_action) list \<Rightarrow>
           expr \<Rightarrow> (heap \<times> locals) \<Rightarrow> bool"
          ("_,_ \<turnstile> ((1\<langle>_,/_\<rangle>) -_\<rightarrow>*/ (1\<langle>_,/_\<rangle>))" [51,51,0,0,0,0,0] 81)
where
  "extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow>* \<langle>e', s'\<rangle> == rtrancl3p (\<lambda>(e, s) ta (e', s'). extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>) (e,s) ta (e',s')"

lemmas Step_induct = rtrancl3p.induct[where r = "\<lambda>(e, s) ta (e', s'). extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>", split_format (complete), simplified, consumes 1, case_names refl step]

subsection{*Some easy lemmas*}

lemma [iff]:
  "\<not> extTA,P \<turnstile> \<langle>Val v, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
by(fastsimp elim:red.cases)

lemma red_no_val [dest]:
  "\<lbrakk> extTA,P \<turnstile> \<langle>e, s\<rangle> -tas\<rightarrow> \<langle>e', s'\<rangle>; is_val e \<rbrakk> \<Longrightarrow> False"
by(auto)


lemma [iff]: "\<not> extTA,P \<turnstile> \<langle>Throw a, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
by(fastsimp elim: red_cases)

lemma reds_preserves_len:
  "extTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> length es' = length es"
by(induct es arbitrary: es')(auto elim: reds.cases)

lemma red_hext_incr: "extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> hp s \<unlhd> hp s'"
  and reds_hext_incr: "extTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> hp s \<unlhd> hp s'"
proof(induct rule:red_reds.inducts)
  case (RedNew C FDTs a h h' l) thus ?case by(auto dest: new_Addr_SomeD intro: hext_new simp del: fun_upd_apply)
next
  case RedNewArray thus ?case by(auto dest: new_Addr_SomeD intro: hext_new simp del: fun_upd_apply)
next
  case RedAAss thus ?case by(fastsimp dest:new_Addr_SomeD simp:hext_def split:if_splits)
next
  case RedFAss thus ?case by(fastsimp simp add:hext_def split:if_splits)
next
  case RedCallExternal thus ?case by(auto intro: red_external_hext)
qed fastsimp+

lemma red_lcl_incr: "extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> dom (lcl s) \<subseteq> dom (lcl s')"
  and reds_lcl_incr: "extTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> dom (lcl s) \<subseteq> dom (lcl s')"
apply(induct rule:red_reds.inducts)
apply(auto simp del: fun_upd_apply split: split_if_asm)
done

lemma red_lcl_add_aux:
  "extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>e, (hp s, l0 ++ lcl s)\<rangle> -ta\<rightarrow> \<langle>e', (hp s', l0 ++ lcl s')\<rangle>"
  and reds_lcl_add_aux:
  "extTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>es, (hp s, l0 ++ lcl s)\<rangle> [-ta\<rightarrow>] \<langle>es', (hp s', l0 ++ lcl s')\<rangle>"
proof (induct arbitrary: l0 and l0 rule:red_reds.inducts)
  case (BlockRed e h x V vo ta e' h' x' T)
  note IH = `\<And>l0. extTA,P \<turnstile> \<langle>e,(hp (h, x(V := vo)), l0 ++ lcl (h, x(V := vo)))\<rangle> -ta\<rightarrow> \<langle>e',(hp (h', x'), l0 ++ lcl (h', x'))\<rangle>`[simplified]
  have lrew: "\<And>x x'. x(V := vo) ++ x'(V := vo) = (x ++ x')(V := vo)" 
    by(simp add:expand_fun_eq map_add_def)
  have lrew1: "\<And>X X' X'' vo. (X(V := vo) ++ X')(V := (X ++ X'') V) = X ++ X'(V := X'' V)"
    by(simp add: expand_fun_eq map_add_def)
  have lrew2: "\<And>X X'. (X(V := None) ++ X') V = X' V"
    by(simp add: map_add_def) 
  show ?case
  proof(cases vo)
    case None
    from IH[of "l0(V := vo)"]
    show ?thesis
      apply(simp del: fun_upd_apply add: lrew)
      apply(drule red_reds.BlockRed)
      by(simp only: lrew1 None lrew2)
  next
    case (Some v)
    with `extTA,P \<turnstile> \<langle>e,(h, x(V := vo))\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>`
    have "x' V \<noteq> None"
      by -(drule red_lcl_incr, auto split: split_if_asm)
    with IH[of "l0(V := vo)"]
    show ?thesis
      apply(clarsimp simp del: fun_upd_apply simp add: lrew)
      apply(drule red_reds.BlockRed)
      by(simp add: lrew1 Some del: fun_upd_apply)
  qed
next
  case (RedTryFail s a D fs C V e2 l0) thus ?case
    by(auto intro: red_reds.RedTryFail)
qed(fastsimp intro:red_reds.intros simp del: fun_upd_apply)+

lemma red_lcl_add: "extTA,P \<turnstile> \<langle>e, (h, l)\<rangle> -ta\<rightarrow> \<langle>e', (h', l')\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>e, (h, l0 ++ l)\<rangle> -ta\<rightarrow> \<langle>e', (h', l0 ++ l')\<rangle>"
  and reds_lcl_add: "extTA,P \<turnstile> \<langle>es, (h, l)\<rangle> [-ta\<rightarrow>] \<langle>es', (h', l')\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>es, (h, l0 ++ l)\<rangle> [-ta\<rightarrow>] \<langle>es', (h', l0 ++ l')\<rangle>"
by(auto dest:red_lcl_add_aux reds_lcl_add_aux)

lemma Step_lcl_add:
  "extTA,P \<turnstile> \<langle>e, (h, l)\<rangle> -ta\<rightarrow>* \<langle>e', (h', l')\<rangle> \<Longrightarrow> extTA,P \<turnstile> \<langle>e, (h, l0 ++ l)\<rangle> -ta\<rightarrow>* \<langle>e', (h', l0 ++ l')\<rangle>"
proof(induct rule: Step_induct)
  case refl thus ?case by(auto intro: rtrancl3p.intros)
next
  case (step e h l ta e' h' l' las tas cas was obs e'' h'' l'')
  have IH: "extTA,P \<turnstile> \<langle>e,(h, l0 ++ l)\<rangle> -ta\<rightarrow>* \<langle>e',(h', l0 ++ l')\<rangle>"
   and red: "extTA,P \<turnstile> \<langle>e',(h', l')\<rangle> -(las, tas, cas, was, obs)\<rightarrow> \<langle>e'',(h'', l'')\<rangle>" by fact+
  from red have "extTA,P \<turnstile> \<langle>e',(h', l0 ++ l')\<rangle> -(las, tas, cas, was, obs)\<rightarrow> \<langle>e'',(h'', l0 ++ l'')\<rangle>" by(rule red_lcl_add)
  with IH show ?case by(auto elim: rtrancl3p_step)
qed

lemma reds_no_val [dest]:
  "\<lbrakk> extTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; is_vals es \<rbrakk> \<Longrightarrow> False"
apply(induct es arbitrary: s ta es' s')
 apply(blast elim: reds.cases)
apply(erule reds.cases)
apply(auto, blast)
done

lemma red_no_Throw [dest!]:
  "extTA,P \<turnstile> \<langle>Throw a, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> False"
by(auto elim!: red_cases)

lemma red_lcl_sub:
  "\<lbrakk> extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; fv e \<subseteq> W \<rbrakk> \<Longrightarrow> extTA,P \<turnstile> \<langle>e, (hp s, (lcl s)|`W)\<rangle> -ta\<rightarrow> \<langle>e', (hp s', (lcl s')|`W)\<rangle>"

  and reds_lcl_sub:
  "\<lbrakk> extTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; fvs es \<subseteq> W \<rbrakk> \<Longrightarrow> extTA,P \<turnstile> \<langle>es, (hp s, (lcl s)|`W)\<rangle> [-ta\<rightarrow>] \<langle>es', (hp s', (lcl s')|`W)\<rangle>"
proof(induct arbitrary: W and W rule: red_reds.inducts)
  case (RedLAss V v h l W)
  have "extTA,P \<turnstile> \<langle>V:=Val v,(h, l |` W)\<rangle> -\<epsilon>\<rightarrow> \<langle>unit,(h, (l |`W)(V \<mapsto> v))\<rangle>"
    by(rule red_reds.RedLAss)
  with RedLAss show ?case by(simp del: fun_upd_apply)
next
  case (BlockRed e h x V vo ta e' h' x' T)
  have IH: "\<And>W. fv e \<subseteq> W \<Longrightarrow> extTA,P \<turnstile> \<langle>e,(hp (h, x(V := vo)), lcl (h, x(V := vo)) |` W)\<rangle> -ta\<rightarrow> \<langle>e',(hp (h', x'), lcl (h', x') |` W)\<rangle>" by fact
  from `fv {V:T=vo; e} \<subseteq> W` have fve: "fv e \<subseteq> insert V W" by auto
  show ?case
  proof(cases "V \<in> W")
    case True
    with fve have "fv e \<subseteq> W" by auto
    from True IH[OF this] have "extTA,P \<turnstile> \<langle>e,(h, (x |` W )(V := vo))\<rangle> -ta\<rightarrow> \<langle>e',(h', x' |` W)\<rangle>" by(simp)
    with True have "extTA,P \<turnstile> \<langle>{V:T=vo; e},(h, x |` W)\<rangle> -ta\<rightarrow> \<langle>{V:T=x' V; e'},(h', (x' |` W)(V := x V))\<rangle>"
      by -(drule red_reds.BlockRed[where T=T], simp)
    with True show ?thesis by(simp del: fun_upd_apply)
  next
    case False
    with IH[OF fve] have "extTA,P \<turnstile> \<langle>e,(h, (x |` W)(V := vo))\<rangle> -ta\<rightarrow> \<langle>e',(h', x' |` insert V W)\<rangle>" by(simp)
    with False have "extTA,P \<turnstile> \<langle>{V:T=vo; e},(h, x |` W)\<rangle> -ta\<rightarrow> \<langle>{V:T=x' V; e'},(h', (x' |` W))\<rangle>"
      by -(drule red_reds.BlockRed[where T=T],simp)
    with False show ?thesis by(simp del: fun_upd_apply)
  qed
next
  case RedTryFail thus ?case by(auto intro: red_reds.RedTryFail)
qed(fastsimp intro: red_reds.intros)+

lemma red_notfree_unchanged: "\<lbrakk> extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; V \<notin> fv e \<rbrakk> \<Longrightarrow> lcl s' V = lcl s V"
  and reds_notfree_unchanged: "\<lbrakk> extTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; V \<notin> fvs es \<rbrakk> \<Longrightarrow> lcl s' V = lcl s V"
apply(induct rule: red_reds.inducts)
apply(fastsimp)+
done

lemma red_dom_lcl: "extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> dom (lcl s') \<subseteq> dom (lcl s) \<union> fv e"
  and reds_dom_lcl: "extTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> dom (lcl s') \<subseteq> dom (lcl s) \<union> fvs es"
proof (induct rule:red_reds.inducts)
  case (BlockRed e h x V vo ta e' h' x' T)
  thus ?case by(clarsimp)(fastsimp split:split_if_asm)
qed auto

subsection {* Final expressions *}

inductive final :: "('a,'b) exp \<Rightarrow> bool" where
  "final (Val v)"
| "final (Throw a)"

declare final.cases [elim]
declare final.intros[simp]

lemmas finalE[consumes 1, case_names Val Throw] = final.cases

lemma final_iff: "final e \<longleftrightarrow> (\<exists>v. e = Val v) \<or> (\<exists>a. e = Throw a)"
by(auto)

lemma final_locks: "final e \<Longrightarrow> expr_locks e l = 0"
by(auto elim: finalE)

constdefs
  finals:: "('a,'b) exp list \<Rightarrow> bool"
  "finals es  \<equiv>  (\<exists>vs. es = map Val vs) \<or> (\<exists>vs a es'. es = map Val vs @ Throw a # es')"

lemma [iff]: "finals []"
by(simp add:finals_def)

lemma [iff]: "finals (Val v # es) = finals es"
apply(clarsimp simp add: finals_def)
apply(rule iffI)
 apply(erule disjE)
  apply fastsimp
 apply(rule disjI2)
 apply clarsimp
 apply(case_tac vs)
  apply simp
 apply fastsimp
apply(erule disjE)
 apply clarsimp
 apply(rule_tac x="v#vs" in exI)
 apply(simp)
apply(rule disjI2)
apply clarsimp
apply(rule_tac x = "v#vs" in exI)
apply simp
done

lemma finals_app_map[iff]: "finals (map Val vs @ es) = finals es"
(*<*)by(induct_tac vs, auto)(*>*)

lemma [iff]: "finals (map Val vs)"
(*<*)using finals_app_map[of vs "[]"]by(simp)(*>*)

lemma [iff]: "finals (throw e # es) = (\<exists>a. e = addr a)"
(*<*)
apply(simp add:finals_def)
apply(rule iffI)
 apply(erule disjE)
  apply(fastsimp)
 apply clarsimp
 apply(case_tac vs)
  apply simp
 apply fastsimp
apply clarsimp
apply(rule_tac x = "[]" in exI)
apply simp
apply(erule_tac x="[]" in allE)
apply(fastsimp)
done
(*>*)

lemma not_finals_ConsI: "\<not> final e \<Longrightarrow> \<not> finals(e#es)"
 (*<*)
apply(clarsimp simp add:finals_def final_iff)
apply(rule conjI)
 apply(fastsimp)
apply(clarsimp)
apply(case_tac vs)
apply auto
done
(*>*)


end