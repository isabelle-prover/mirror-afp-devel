(*  Title:      JinjaThreads/J/SmallStep.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

header {* \isaheader{Small Step Semantics} *}

theory SmallStep imports
  Expr
  State
  "../Common/StartConfig"
  JHeap
begin

types
  'heap J_thread_action = "(expr \<times> locals,'heap) Jinja_thread_action"
  'heap J_state = "(addr,thread_id,expr \<times> locals,'heap,addr) state"

translations
  (type) "'heap J_thread_action" <= (type) "(expr \<times> (String.literal \<rightharpoonup> val),'heap) Jinja_thread_action"
  (type) "'heap J_state" <= (type) "(nat,nat,expr \<times> locals,'heap,nat) state"

definition extNTA2J :: "J_prog \<Rightarrow> (cname \<times> mname \<times> addr) \<Rightarrow> expr \<times> locals"
where "extNTA2J P = (\<lambda>(C, M, a). let (D,Ts,T,pns,body) = method P C M
                                 in ({this:Class D=\<lfloor>Addr a\<rfloor>; body}, empty))"

abbreviation (in J_heap_base) J_start_state :: "J_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> val list \<Rightarrow> 'heap J_state"
where
  "J_start_state \<equiv> 
   start_state (\<lambda>C M Ts T (pns, body) vs. (blocks (this # pns) (Class C # Ts) (Null # vs) body, empty))"

lemma extNTA2J_iff [simp]:
  "extNTA2J P (C, M, a) = ({this:Class (fst (method P C M))=\<lfloor>Addr a\<rfloor>; snd (snd (snd (snd (method P C M))))}, empty)"
by(simp add: extNTA2J_def split_beta)

abbreviation extTA2J :: "J_prog \<Rightarrow> 'heap external_thread_action \<Rightarrow> 'heap J_thread_action"
where "extTA2J P \<equiv> convert_extTA (extNTA2J P)"

lemma extTA2J_\<epsilon>: "extTA2J P \<epsilon> = \<epsilon>"
by(simp)

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

context J_heap_base begin

inductive red :: "('heap external_thread_action \<Rightarrow> (addr,thread_id,'x,'heap,addr,obs_event list) thread_action) \<Rightarrow> J_prog \<Rightarrow> thread_id \<Rightarrow>
                 expr \<Rightarrow> 'heap Jstate \<Rightarrow> (addr,thread_id,'x,'heap,addr,obs_event list) thread_action \<Rightarrow> expr \<Rightarrow> 'heap Jstate \<Rightarrow> bool"
                ("_,_,_ \<turnstile> ((1\<langle>_,/_\<rangle>) -_\<rightarrow>/ (1\<langle>_,/_\<rangle>))" [51,51,0,0,0,0,0,0] 81)
 and reds ::  "('heap external_thread_action \<Rightarrow> (addr,thread_id,'x,'heap,addr,obs_event list) thread_action) \<Rightarrow> J_prog \<Rightarrow> thread_id \<Rightarrow>
                 expr list \<Rightarrow> 'heap Jstate \<Rightarrow> (addr,thread_id,'x,'heap,addr,obs_event list) thread_action \<Rightarrow> expr list \<Rightarrow> 'heap Jstate \<Rightarrow> bool"
               ("_,_,_ \<turnstile> ((1\<langle>_,/_\<rangle>) [-_\<rightarrow>]/ (1\<langle>_,/_\<rangle>))" [51,51,0,0,0,0,0,0] 81)
for extTA :: "'heap external_thread_action \<Rightarrow> (addr,thread_id,'x,'heap,addr,obs_event list) thread_action"
  and P :: J_prog and t :: thread_id
where
  RedNew:
  "new_obj h C = (h', \<lfloor>a\<rfloor>)
  \<Longrightarrow> extTA,P,t \<turnstile> \<langle>new C, (h, l)\<rangle> -\<epsilon>\<lbrace>\<^bsub>o\<^esub> NewObj a C \<rbrace>\<rightarrow> \<langle>addr a, (h', l)\<rangle>"

| RedNewFail:
  "new_obj h C = (h', None)
  \<Longrightarrow> extTA,P,t \<turnstile> \<langle>new C, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW OutOfMemory, (h', l)\<rangle>"

| NewArrayRed:
  "extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>newA T\<lfloor>e\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>newA T\<lfloor>e'\<rceil>, s'\<rangle>"

| RedNewArray:
  "\<lbrakk> 0 <=s i; new_arr h T (nat (sint i)) = (h', \<lfloor>a\<rfloor>) \<rbrakk>
  \<Longrightarrow> extTA,P,t \<turnstile> \<langle>newA T\<lfloor>Val (Intg i)\<rceil>, (h, l)\<rangle> -\<epsilon>\<lbrace>\<^bsub>o\<^esub> NewArr a T (nat (sint i))\<rbrace>\<rightarrow> \<langle>addr a, (h', l)\<rangle>"

| RedNewArrayNegative:
  "i <s 0 \<Longrightarrow> extTA,P,t \<turnstile> \<langle>newA T\<lfloor>Val (Intg i)\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NegativeArraySize, s\<rangle>"

| RedNewArrayFail:
  "\<lbrakk> 0 <=s i; new_arr h T (nat (sint i)) = (h', None) \<rbrakk>
  \<Longrightarrow> extTA,P,t \<turnstile> \<langle>newA T\<lfloor>Val (Intg i)\<rceil>, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW OutOfMemory, (h', l)\<rangle>"

| CastRed:
  "extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>Cast C e, s\<rangle> -ta\<rightarrow> \<langle>Cast C e', s'\<rangle>"

| RedCast:
 "\<lbrakk> typeof\<^bsub>hp s\<^esub> v = \<lfloor>U\<rfloor>; P \<turnstile> U \<le> T \<rbrakk>
  \<Longrightarrow> extTA,P,t \<turnstile> \<langle>Cast T (Val v), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| RedCastFail:
  "\<lbrakk> typeof\<^bsub>hp s\<^esub> v = \<lfloor>U\<rfloor>; \<not> P \<turnstile> U \<le> T \<rbrakk>
  \<Longrightarrow> extTA,P,t \<turnstile> \<langle>Cast T (Val v), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ClassCast, s\<rangle>"

| InstanceOfRed:
  "extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>e instanceof T, s\<rangle> -ta\<rightarrow> \<langle>e' instanceof T, s'\<rangle>"

| RedInstanceOf:
  "\<lbrakk> typeof\<^bsub>hp s\<^esub> v = \<lfloor>U\<rfloor>; b \<longleftrightarrow> v \<noteq> Null \<and> P \<turnstile> U \<le> T \<rbrakk>
   \<Longrightarrow> extTA,P,t \<turnstile> \<langle>(Val v) instanceof T, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val (Bool b), s\<rangle>"

| BinOpRed1:
  "extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>e \<guillemotleft>bop\<guillemotright> e2, s\<rangle> -ta\<rightarrow> \<langle>e' \<guillemotleft>bop\<guillemotright> e2, s'\<rangle>"

| BinOpRed2:
  "extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>(Val v) \<guillemotleft>bop\<guillemotright> e, s\<rangle> -ta\<rightarrow> \<langle>(Val v) \<guillemotleft>bop\<guillemotright> e', s'\<rangle>"

| RedBinOp:
  "binop bop v1 v2 = Some v \<Longrightarrow>
  extTA,P,t \<turnstile> \<langle>(Val v1) \<guillemotleft>bop\<guillemotright> (Val v2), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| RedVar:
  "lcl s V = Some v \<Longrightarrow>
  extTA,P,t \<turnstile> \<langle>Var V, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| LAssRed:
  "extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>V:=e, s\<rangle> -ta\<rightarrow> \<langle>V:=e', s'\<rangle>"

| RedLAss:
  "extTA,P,t \<turnstile> \<langle>V:=(Val v), (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>unit, (h, l(V \<mapsto> v))\<rangle>"

| AAccRed1:
  "extTA,P,t \<turnstile> \<langle>a, s\<rangle> -ta\<rightarrow> \<langle>a', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>a\<lfloor>i\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>a'\<lfloor>i\<rceil>, s'\<rangle>"

| AAccRed2:
  "extTA,P,t \<turnstile> \<langle>i, s\<rangle> -ta\<rightarrow> \<langle>i', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>(Val a)\<lfloor>i\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>(Val a)\<lfloor>i'\<rceil>, s'\<rangle>"

| RedAAccNull:
  "extTA,P,t \<turnstile> \<langle>null\<lfloor>Val i\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| RedAAccBounds:
  "\<lbrakk> typeof_addr (hp s) a = \<lfloor>Array T\<rfloor>; i <s 0 \<or> sint i \<ge> int (array_length (hp s) a) \<rbrakk>
  \<Longrightarrow> extTA,P,t \<turnstile> \<langle>(addr a)\<lfloor>Val (Intg i)\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ArrayIndexOutOfBounds, s\<rangle>"

| RedAAcc:
  "\<lbrakk> typeof_addr h a = \<lfloor>Array T\<rfloor>; 0 <=s i; sint i < int (array_length h a); 
     heap_read h a (ACell (nat (sint i))) v \<rbrakk>
  \<Longrightarrow> extTA,P,t \<turnstile> \<langle>(addr a)\<lfloor>Val (Intg i)\<rceil>, (h, l)\<rangle> -\<epsilon>\<lbrace>\<^bsub>o\<^esub> ReadMem a (ACell (nat (sint i))) v \<rbrace>\<rightarrow> \<langle>Val v, (h, l)\<rangle>"

| AAssRed1:
  "extTA,P,t \<turnstile> \<langle>a, s\<rangle> -ta\<rightarrow> \<langle>a', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>a\<lfloor>i\<rceil> := e, s\<rangle> -ta\<rightarrow> \<langle>a'\<lfloor>i\<rceil> := e, s'\<rangle>"

| AAssRed2:
  "extTA,P,t \<turnstile> \<langle>i, s\<rangle> -ta\<rightarrow> \<langle>i', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>(Val a)\<lfloor>i\<rceil> := e, s\<rangle> -ta\<rightarrow> \<langle>(Val a)\<lfloor>i'\<rceil> := e, s'\<rangle>"

| AAssRed3:
  "extTA,P,t \<turnstile> \<langle>(e::expr), s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>(Val a)\<lfloor>Val i\<rceil> := e, s\<rangle> -ta\<rightarrow> \<langle>(Val a)\<lfloor>Val i\<rceil> := e', s'\<rangle>"

| RedAAssNull:
  "extTA,P,t \<turnstile> \<langle>null\<lfloor>Val i\<rceil> := (Val e::expr), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| RedAAssBounds:
  "\<lbrakk> typeof_addr (hp s) a = \<lfloor>Array T\<rfloor>; i <s 0 \<or> sint i \<ge> int (array_length (hp s) a) \<rbrakk>
  \<Longrightarrow> extTA,P,t \<turnstile> \<langle>(addr a)\<lfloor>Val (Intg i)\<rceil> := (Val e::expr), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ArrayIndexOutOfBounds, s\<rangle>"

| RedAAssStore:
  "\<lbrakk> typeof_addr (hp s) a = \<lfloor>Array T\<rfloor>; 0 <=s i; sint i < int (array_length (hp s) a);
     typeof\<^bsub>hp s\<^esub> w = \<lfloor>U\<rfloor>; \<not> (P \<turnstile> U \<le> T) \<rbrakk>
  \<Longrightarrow> extTA,P,t \<turnstile> \<langle>(addr a)\<lfloor>Val (Intg i)\<rceil> := (Val w::expr), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ArrayStore, s\<rangle>"

| RedAAss:
  "\<lbrakk> typeof_addr h a = \<lfloor>Array T\<rfloor>; 0 <=s i; sint i < int (array_length h a); typeof\<^bsub>h\<^esub> w = Some U; P \<turnstile> U \<le> T;
     heap_write h a (ACell (nat (sint i))) w h' \<rbrakk>
  \<Longrightarrow> extTA,P,t \<turnstile> \<langle>(addr a)\<lfloor>Val (Intg i)\<rceil> := Val w::expr, (h, l)\<rangle> -\<epsilon>\<lbrace>\<^bsub>o\<^esub> WriteMem a (ACell (nat (sint i))) w \<rbrace>\<rightarrow> \<langle>unit, (h', l)\<rangle>"

| ALengthRed:
  "extTA,P,t \<turnstile> \<langle>a, s\<rangle> -ta\<rightarrow> \<langle>a', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>a\<bullet>length, s\<rangle> -ta\<rightarrow> \<langle>a'\<bullet>length, s'\<rangle>"

| RedALength:
  "typeof_addr h a = \<lfloor>Array T\<rfloor> 
  \<Longrightarrow> extTA,P,t \<turnstile> \<langle>addr a\<bullet>length, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>Val (Intg (word_of_int (int (array_length h a)))), (h, l)\<rangle>"

| RedALengthNull:
  "extTA,P,t \<turnstile> \<langle>null\<bullet>length, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| FAccRed:
  "extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>e\<bullet>F{D}, s\<rangle> -ta\<rightarrow> \<langle>e'\<bullet>F{D}, s'\<rangle>"

| RedFAcc:
  "heap_read h a (CField D F) v
  \<Longrightarrow> extTA,P,t \<turnstile> \<langle>(addr a)\<bullet>F{D}, (h, l)\<rangle> -\<epsilon>\<lbrace>\<^bsub>o\<^esub> ReadMem a (CField D F) v\<rbrace>\<rightarrow> \<langle>Val v, (h, l)\<rangle>"

| RedFAccNull:
  "extTA,P,t \<turnstile> \<langle>null\<bullet>F{D}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| FAssRed1:
  "extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>e\<bullet>F{D}:=e2, s\<rangle> -ta\<rightarrow> \<langle>e'\<bullet>F{D}:=e2, s'\<rangle>"

| FAssRed2:
  "extTA,P,t \<turnstile> \<langle>(e::expr), s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>Val v\<bullet>F{D}:=e, s\<rangle> -ta\<rightarrow> \<langle>Val v\<bullet>F{D}:=e', s'\<rangle>"

| RedFAss:
  "heap_write h a (CField D F) v h' \<Longrightarrow>
  extTA,P,t \<turnstile> \<langle>(addr a)\<bullet>F{D}:= Val v, (h, l)\<rangle> -\<epsilon>\<lbrace>\<^bsub>o\<^esub> WriteMem a (CField D F) v \<rbrace>\<rightarrow> \<langle>unit, (h', l)\<rangle>"

| RedFAssNull:
  "extTA,P,t \<turnstile> \<langle>null\<bullet>F{D}:=Val v::expr, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| CallObj:
  "extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>e\<bullet>M(es), s\<rangle> -ta\<rightarrow> \<langle>e'\<bullet>M(es), s'\<rangle>"

| CallParams:
  "extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow>
  extTA,P,t \<turnstile> \<langle>(Val v)\<bullet>M(es),s\<rangle> -ta\<rightarrow> \<langle>(Val v)\<bullet>M(es'),s'\<rangle>"

| RedCall:
  "\<lbrakk> typeof_addr (hp s) a = \<lfloor>Class C\<rfloor>; \<not> is_external_call P (Class C) M; P \<turnstile> C sees M:Ts\<rightarrow>T = (pns,body) in D; 
    size vs = size pns; size Ts = size pns \<rbrakk>
  \<Longrightarrow> extTA,P,t \<turnstile> \<langle>(addr a)\<bullet>M(map Val vs), s\<rangle> -\<epsilon>\<rightarrow> \<langle>blocks (this # pns) (Class D # Ts) (Addr a # vs) body, s\<rangle>"

| RedCallExternal:
  "\<lbrakk> typeof_addr (hp s) a = \<lfloor>T\<rfloor>; is_external_call P T M; P,t \<turnstile> \<langle>a\<bullet>M(vs), hp s\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>;
     ta' = extTA ta; e' = extRet2J ((addr a)\<bullet>M(map Val vs)) va; s' = (h', lcl s) \<rbrakk>
  \<Longrightarrow> extTA,P,t \<turnstile> \<langle>(addr a)\<bullet>M(map Val vs), s\<rangle> -ta'\<rightarrow> \<langle>e', s'\<rangle>"

| RedCallNull:
  "extTA,P,t \<turnstile> \<langle>null\<bullet>M(map Val vs), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| BlockRed:
  "extTA,P,t \<turnstile> \<langle>e, (h, l(V:=vo))\<rangle> -ta\<rightarrow> \<langle>e', (h', l')\<rangle>
  \<Longrightarrow> extTA,P,t \<turnstile> \<langle>{V:T=vo; e}, (h, l)\<rangle> -ta\<rightarrow> \<langle>{V:T=l' V; e'}, (h', l'(V := l V))\<rangle>"

| RedBlock:
  "extTA,P,t \<turnstile> \<langle>{V:T=vo; Val u}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val u, s\<rangle>"

| SynchronizedRed1:
  "extTA,P,t \<turnstile> \<langle>o', s\<rangle> -ta\<rightarrow> \<langle>o'', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>sync(o') e, s\<rangle> -ta\<rightarrow> \<langle>sync(o'') e, s'\<rangle>"

| SynchronizedNull:
  "extTA,P,t \<turnstile> \<langle>sync(null) e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| LockSynchronized:
  "extTA,P,t \<turnstile> \<langle>sync(addr a) e, s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Lock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub>SyncLock a\<rbrace>\<rightarrow> \<langle>insync(a) e, s\<rangle>"

| SynchronizedRed2:
  "extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>insync(a) e, s\<rangle> -ta\<rightarrow> \<langle>insync(a) e', s'\<rangle>"

| UnlockSynchronized:
  "extTA,P,t \<turnstile> \<langle>insync(a) (Val v), s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub>SyncUnlock a\<rbrace>\<rightarrow> \<langle>Val v, s\<rangle>"

| SeqRed:
  "extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>e;;e2, s\<rangle> -ta\<rightarrow> \<langle>e';;e2, s'\<rangle>"

| RedSeq:
  "extTA,P,t \<turnstile> \<langle>(Val v);;e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>e, s\<rangle>"

| CondRed:
  "extTA,P,t \<turnstile> \<langle>b, s\<rangle> -ta\<rightarrow> \<langle>b', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>if (b) e1 else e2, s\<rangle> -ta\<rightarrow> \<langle>if (b') e1 else e2, s'\<rangle>"

| RedCondT:
  "extTA,P,t \<turnstile> \<langle>if (true) e1 else e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>e1, s\<rangle>"

| RedCondF:
  "extTA,P,t \<turnstile> \<langle>if (false) e1 else e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>e2, s\<rangle>"

| RedWhile:
  "extTA,P,t \<turnstile> \<langle>while(b) c, s\<rangle> -\<epsilon>\<rightarrow> \<langle>if (b) (c;;while(b) c) else unit, s\<rangle>"

| ThrowRed:
  "extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>throw e, s\<rangle> -ta\<rightarrow> \<langle>throw e', s'\<rangle>"

| RedThrowNull:
  "extTA,P,t \<turnstile> \<langle>throw null, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| TryRed:
  "extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>try e catch(C V) e2, s\<rangle> -ta\<rightarrow> \<langle>try e' catch(C V) e2, s'\<rangle>"

| RedTry:
  "extTA,P,t \<turnstile> \<langle>try (Val v) catch(C V) e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| RedTryCatch:
  "\<lbrakk> typeof_addr (hp s) a = \<lfloor>Class D\<rfloor>; P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> extTA,P,t \<turnstile> \<langle>try (Throw a) catch(C V) e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>{V:Class C=\<lfloor>Addr a\<rfloor>; e2}, s\<rangle>"

| RedTryFail:
  "\<lbrakk> typeof_addr (hp s) a = \<lfloor>Class D\<rfloor>; \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> extTA,P,t \<turnstile> \<langle>try (Throw a) catch(C V) e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"

| ListRed1:
  "extTA,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  extTA,P,t \<turnstile> \<langle>e#es,s\<rangle> [-ta\<rightarrow>] \<langle>e'#es,s'\<rangle>"

| ListRed2:
  "extTA,P,t \<turnstile> \<langle>es,s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow>
  extTA,P,t \<turnstile> \<langle>Val v # es,s\<rangle> [-ta\<rightarrow>] \<langle>Val v # es',s'\<rangle>"

-- "Exception propagation"

| NewArrayThrow: "extTA,P,t \<turnstile> \<langle>newA T\<lfloor>Throw a\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| CastThrow: "extTA,P,t \<turnstile> \<langle>Cast C (Throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| InstanceOfThrow: "extTA,P,t \<turnstile> \<langle>(Throw a) instanceof T, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| BinOpThrow1: "extTA,P,t \<turnstile> \<langle>(Throw a) \<guillemotleft>bop\<guillemotright> e\<^isub>2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| BinOpThrow2: "extTA,P,t \<turnstile> \<langle>(Val v\<^isub>1) \<guillemotleft>bop\<guillemotright> (Throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| LAssThrow: "extTA,P,t \<turnstile> \<langle>V:=(Throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| AAccThrow1: "extTA,P,t \<turnstile> \<langle>(Throw a)\<lfloor>i\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| AAccThrow2: "extTA,P,t \<turnstile> \<langle>(Val v)\<lfloor>Throw a\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| AAssThrow1: "extTA,P,t \<turnstile> \<langle>(Throw a)\<lfloor>i\<rceil> := e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| AAssThrow2: "extTA,P,t \<turnstile> \<langle>(Val v)\<lfloor>Throw a\<rceil> := e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| AAssThrow3: "extTA,P,t \<turnstile> \<langle>(Val v)\<lfloor>Val i\<rceil> := Throw a :: expr, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| ALengthThrow: "extTA,P,t \<turnstile> \<langle>(Throw a)\<bullet>length, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| FAccThrow: "extTA,P,t \<turnstile> \<langle>(Throw a)\<bullet>F{D}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| FAssThrow1: "extTA,P,t \<turnstile> \<langle>(Throw a)\<bullet>F{D}:=e\<^isub>2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| FAssThrow2: "extTA,P,t \<turnstile> \<langle>Val v\<bullet>F{D}:=(Throw a::expr), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| CallThrowObj: "extTA,P,t \<turnstile> \<langle>(Throw a)\<bullet>M(es), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| CallThrowParams: "\<lbrakk> es = map Val vs @ Throw a # es' \<rbrakk> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>(Val v)\<bullet>M(es), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| BlockThrow: "extTA,P,t \<turnstile> \<langle>{V:T=vo; Throw a}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| SynchronizedThrow1: "extTA,P,t \<turnstile> \<langle>sync(Throw a) e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| SynchronizedThrow2: "extTA,P,t \<turnstile> \<langle>insync(a) Throw ad, s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub>SyncUnlock a\<rbrace>\<rightarrow> \<langle>Throw ad, s\<rangle>"
| SeqThrow: "extTA,P,t \<turnstile> \<langle>(Throw a);;e\<^isub>2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| CondThrow: "extTA,P,t \<turnstile> \<langle>if (Throw a) e\<^isub>1 else e\<^isub>2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| ThrowThrow: "extTA,P,t \<turnstile> \<langle>throw(Throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"

inductive_cases red_cases:
  "extTA,P,t \<turnstile> \<langle>new C, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P,t \<turnstile> \<langle>newA T\<lfloor>e\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P,t \<turnstile> \<langle>Cast T e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P,t \<turnstile> \<langle>e instanceof T, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P,t \<turnstile> \<langle>e \<guillemotleft>bop\<guillemotright> e', s\<rangle> -ta\<rightarrow> \<langle>e'', s'\<rangle>"
  "extTA,P,t \<turnstile> \<langle>Var V, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P,t \<turnstile> \<langle>V:=e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P,t \<turnstile> \<langle>a\<lfloor>i\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P,t \<turnstile> \<langle>a\<lfloor>i\<rceil> := e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P,t \<turnstile> \<langle>a\<bullet>length, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P,t \<turnstile> \<langle>e\<bullet>F{D}, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P,t \<turnstile> \<langle>e\<bullet>F{D} := e', s\<rangle> -ta\<rightarrow> \<langle>e'', s'\<rangle>"
  "extTA,P,t \<turnstile> \<langle>e\<bullet>M(es), s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P,t \<turnstile> \<langle>{V:T=vo; e}, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P,t \<turnstile> \<langle>sync(o') e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P,t \<turnstile> \<langle>insync(a) e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P,t \<turnstile> \<langle>e;;e', s\<rangle> -ta\<rightarrow> \<langle>e'', s'\<rangle>"
  "extTA,P,t \<turnstile> \<langle>if (b) e1 else e2, s \<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P,t \<turnstile> \<langle>while (b) e, s \<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P,t \<turnstile> \<langle>throw e, s \<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "extTA,P,t \<turnstile> \<langle>try e catch(C V) e', s\<rangle> -ta\<rightarrow> \<langle>e'', s'\<rangle>"

inductive_cases reds_cases:
  "extTA,P,t \<turnstile> \<langle>e # es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>"

abbreviation red' :: "J_prog \<Rightarrow> thread_id \<Rightarrow> expr \<Rightarrow> ('heap \<times> locals) \<Rightarrow> 'heap J_thread_action \<Rightarrow> expr \<Rightarrow> ('heap \<times> locals) \<Rightarrow> bool"
                ("_,_ \<turnstile> ((1\<langle>_,/_\<rangle>) -_\<rightarrow>/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0,0,0] 81)
where "red' P \<equiv> red (extTA2J P) P"

abbreviation reds' :: "J_prog \<Rightarrow> thread_id \<Rightarrow> expr list \<Rightarrow> ('heap \<times> locals) \<Rightarrow> 'heap J_thread_action \<Rightarrow> expr list \<Rightarrow> ('heap \<times> locals) \<Rightarrow> bool"
               ("_,_ \<turnstile> ((1\<langle>_,/_\<rangle>) [-_\<rightarrow>]/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0,0,0] 81)
where "reds' P \<equiv> reds (extTA2J P) P"

subsection{*Some easy lemmas*}

lemma [iff]:
  "\<not> extTA,P,t \<turnstile> \<langle>Val v, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
by(fastsimp elim:red.cases)

lemma red_no_val [dest]:
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>e, s\<rangle> -tas\<rightarrow> \<langle>e', s'\<rangle>; is_val e \<rbrakk> \<Longrightarrow> False"
by(auto)

lemma [iff]: "\<not> extTA,P,t \<turnstile> \<langle>Throw a, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
by(fastsimp elim: red_cases)

lemma reds_map_Val_Throw:
  "extTA,P,t \<turnstile> \<langle>map Val vs @ Throw a # es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<longleftrightarrow> False"
by(induct vs arbitrary: es')(auto elim!: reds_cases)

lemma reds_preserves_len:
  "extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> length es' = length es"
by(induct es arbitrary: es')(auto elim: reds.cases)

lemma red_lcl_incr: "extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> dom (lcl s) \<subseteq> dom (lcl s')"
  and reds_lcl_incr: "extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> dom (lcl s) \<subseteq> dom (lcl s')"
apply(induct rule:red_reds.inducts)
apply(auto simp del: fun_upd_apply split: split_if_asm)
done

lemma red_lcl_add_aux:
  "extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>e, (hp s, l0 ++ lcl s)\<rangle> -ta\<rightarrow> \<langle>e', (hp s', l0 ++ lcl s')\<rangle>"
  and reds_lcl_add_aux:
  "extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>es, (hp s, l0 ++ lcl s)\<rangle> [-ta\<rightarrow>] \<langle>es', (hp s', l0 ++ lcl s')\<rangle>"
proof (induct arbitrary: l0 and l0 rule:red_reds.inducts)
  case (BlockRed e h x V vo ta e' h' x' T)
  note IH = `\<And>l0. extTA,P,t \<turnstile> \<langle>e,(hp (h, x(V := vo)), l0 ++ lcl (h, x(V := vo)))\<rangle> -ta\<rightarrow> \<langle>e',(hp (h', x'), l0 ++ lcl (h', x'))\<rangle>`[simplified]
  have lrew: "\<And>x x'. x(V := vo) ++ x'(V := vo) = (x ++ x')(V := vo)" 
    by(simp add:fun_eq_iff map_add_def)
  have lrew1: "\<And>X X' X'' vo. (X(V := vo) ++ X')(V := (X ++ X'') V) = X ++ X'(V := X'' V)"
    by(simp add: fun_eq_iff map_add_def)
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
    with `extTA,P,t \<turnstile> \<langle>e,(h, x(V := vo))\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>`
    have "x' V \<noteq> None"
      by -(drule red_lcl_incr, auto split: split_if_asm)
    with IH[of "l0(V := vo)"]
    show ?thesis
      apply(clarsimp simp del: fun_upd_apply simp add: lrew)
      apply(drule red_reds.BlockRed)
      by(simp add: lrew1 Some del: fun_upd_apply)
  qed
next
  case RedTryFail thus ?case
    by(auto intro: red_reds.RedTryFail)
qed(fastsimp intro:red_reds.intros simp del: fun_upd_apply)+

lemma red_lcl_add: "extTA,P,t \<turnstile> \<langle>e, (h, l)\<rangle> -ta\<rightarrow> \<langle>e', (h', l')\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>e, (h, l0 ++ l)\<rangle> -ta\<rightarrow> \<langle>e', (h', l0 ++ l')\<rangle>"
  and reds_lcl_add: "extTA,P,t \<turnstile> \<langle>es, (h, l)\<rangle> [-ta\<rightarrow>] \<langle>es', (h', l')\<rangle> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>es, (h, l0 ++ l)\<rangle> [-ta\<rightarrow>] \<langle>es', (h', l0 ++ l')\<rangle>"
by(auto dest:red_lcl_add_aux reds_lcl_add_aux)

lemma reds_no_val [dest]:
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; is_vals es \<rbrakk> \<Longrightarrow> False"
apply(induct es arbitrary: s ta es' s')
 apply(blast elim: reds.cases)
apply(erule reds.cases)
apply(auto, blast)
done

lemma red_no_Throw [dest!]:
  "extTA,P,t \<turnstile> \<langle>Throw a, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> False"
by(auto elim!: red_cases)

lemma red_lcl_sub:
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; fv e \<subseteq> W \<rbrakk> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>e, (hp s, (lcl s)|`W)\<rangle> -ta\<rightarrow> \<langle>e', (hp s', (lcl s')|`W)\<rangle>"

  and reds_lcl_sub:
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; fvs es \<subseteq> W \<rbrakk> \<Longrightarrow> extTA,P,t \<turnstile> \<langle>es, (hp s, (lcl s)|`W)\<rangle> [-ta\<rightarrow>] \<langle>es', (hp s', (lcl s')|`W)\<rangle>"
proof(induct arbitrary: W and W rule: red_reds.inducts)
  case (RedLAss V v h l W)
  have "extTA,P,t \<turnstile> \<langle>V:=Val v,(h, l |` W)\<rangle> -\<epsilon>\<rightarrow> \<langle>unit,(h, (l |`W)(V \<mapsto> v))\<rangle>"
    by(rule red_reds.RedLAss)
  with RedLAss show ?case by(simp del: fun_upd_apply)
next
  case (BlockRed e h x V vo ta e' h' x' T)
  have IH: "\<And>W. fv e \<subseteq> W \<Longrightarrow> extTA,P,t \<turnstile> \<langle>e,(hp (h, x(V := vo)), lcl (h, x(V := vo)) |` W)\<rangle> -ta\<rightarrow> \<langle>e',(hp (h', x'), lcl (h', x') |` W)\<rangle>" by fact
  from `fv {V:T=vo; e} \<subseteq> W` have fve: "fv e \<subseteq> insert V W" by auto
  show ?case
  proof(cases "V \<in> W")
    case True
    with fve have "fv e \<subseteq> W" by auto
    from True IH[OF this] have "extTA,P,t \<turnstile> \<langle>e,(h, (x |` W )(V := vo))\<rangle> -ta\<rightarrow> \<langle>e',(h', x' |` W)\<rangle>" by(simp)
    with True have "extTA,P,t \<turnstile> \<langle>{V:T=vo; e},(h, x |` W)\<rangle> -ta\<rightarrow> \<langle>{V:T=x' V; e'},(h', (x' |` W)(V := x V))\<rangle>"
      by -(drule red_reds.BlockRed[where T=T], simp)
    with True show ?thesis by(simp del: fun_upd_apply)
  next
    case False
    with IH[OF fve] have "extTA,P,t \<turnstile> \<langle>e,(h, (x |` W)(V := vo))\<rangle> -ta\<rightarrow> \<langle>e',(h', x' |` insert V W)\<rangle>" by(simp)
    with False have "extTA,P,t \<turnstile> \<langle>{V:T=vo; e},(h, x |` W)\<rangle> -ta\<rightarrow> \<langle>{V:T=x' V; e'},(h', (x' |` W))\<rangle>"
      by -(drule red_reds.BlockRed[where T=T],simp)
    with False show ?thesis by(simp del: fun_upd_apply)
  qed
next
  case RedTryFail thus ?case by(auto intro: red_reds.RedTryFail)
qed(fastsimp intro: red_reds.intros)+

lemma red_notfree_unchanged: "\<lbrakk> extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; V \<notin> fv e \<rbrakk> \<Longrightarrow> lcl s' V = lcl s V"
  and reds_notfree_unchanged: "\<lbrakk> extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; V \<notin> fvs es \<rbrakk> \<Longrightarrow> lcl s' V = lcl s V"
apply(induct rule: red_reds.inducts)
apply(fastsimp)+
done

lemma red_dom_lcl: "extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> dom (lcl s') \<subseteq> dom (lcl s) \<union> fv e"
  and reds_dom_lcl: "extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> dom (lcl s') \<subseteq> dom (lcl s) \<union> fvs es"
proof (induct rule:red_reds.inducts)
  case (BlockRed e h x V vo ta e' h' x' T)
  thus ?case by(clarsimp)(fastsimp split:split_if_asm)
qed auto

lemma red_Suspend_is_call:
  "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>a vs T. call e' = \<lfloor>(a, wait, vs)\<rfloor> \<and> typeof_addr (hp s) a = \<lfloor>T\<rfloor> \<and> is_external_call P T wait"
  and reds_Suspend_is_calls:
  "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>a vs T. calls es' = \<lfloor>(a, wait, vs)\<rfloor> \<and> typeof_addr (hp s) a = \<lfloor>T\<rfloor> \<and> is_external_call P T wait"
proof(induct rule: red_reds.inducts)
  case RedCallExternal
  thus ?case
    apply clarsimp
    apply(frule red_external_Suspend_StaySame, simp)
    apply(drule red_external_Suspend_waitD, simp_all)
    done
qed auto

end

context J_heap begin

lemma red_hext_incr: "extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> hp s \<unlhd> hp s'"
  and reds_hext_incr: "extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> hp s \<unlhd> hp s'"
by(induct rule:red_reds.inducts)(auto intro: hext_heap_ops red_external_hext)

lemma red_preserves_tconf: "\<lbrakk> extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; P,hp s \<turnstile> t \<surd>t \<rbrakk> \<Longrightarrow> P,hp s' \<turnstile> t \<surd>t"
by(drule red_hext_incr)(rule tconf_hext_mono)

lemma reds_preserves_tconf: "\<lbrakk> extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; P,hp s \<turnstile> t \<surd>t \<rbrakk> \<Longrightarrow> P,hp s' \<turnstile> t \<surd>t"
by(drule reds_hext_incr)(rule tconf_hext_mono)

end

subsection {* Code generation *}

context J_heap_base begin

lemma RedCall_code:
  "\<lbrakk> is_vals es; typeof_addr (hp s) a = \<lfloor>Class C\<rfloor>; \<not> is_external_call P (Class C) M; P \<turnstile> C sees M:Ts\<rightarrow>T = (pns,body) in D; 
    size es = size pns; size Ts = size pns \<rbrakk>
  \<Longrightarrow> extTA,P,t \<turnstile> \<langle>(addr a)\<bullet>M(es), s\<rangle> -\<epsilon>\<rightarrow> \<langle>blocks (this # pns) (Class D # Ts) (Addr a # map the_Val es) body, s\<rangle>"

  and RedCallExternal_code:
  "\<lbrakk> is_vals es; typeof_addr (hp s) a = \<lfloor>T\<rfloor>; is_external_call P T M; P,t \<turnstile> \<langle>a\<bullet>M(map the_Val es), hp s\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle> \<rbrakk>
  \<Longrightarrow> extTA,P,t \<turnstile> \<langle>(addr a)\<bullet>M(es), s\<rangle> -extTA ta\<rightarrow> \<langle>extRet2J ((addr a)\<bullet>M(es)) va, (h', lcl s)\<rangle>"

  and RedCallNull_code:
  "is_vals es \<Longrightarrow> extTA,P,t \<turnstile> \<langle>null\<bullet>M(es), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"
  
  and CallThrowParams_code:
  "is_Throws es \<Longrightarrow> extTA,P,t \<turnstile> \<langle>(Val v)\<bullet>M(es), s\<rangle> -\<epsilon>\<rightarrow> \<langle>hd (dropWhile is_val es), s\<rangle>"

apply(auto simp add: is_vals_conv is_Throws_conv o_def intro: RedCall RedCallExternal RedCallNull simp del: blocks.simps)
apply(subst dropWhile_append2)
apply(auto intro: CallThrowParams)
done

end

lemmas [code_pred_intro] =
  J_heap_base.RedNew J_heap_base.RedNewFail J_heap_base.NewArrayRed J_heap_base.RedNewArray J_heap_base.RedNewArrayNegative
  J_heap_base.RedNewArrayFail J_heap_base.CastRed J_heap_base.RedCast J_heap_base.RedCastFail J_heap_base.InstanceOfRed
  J_heap_base.RedInstanceOf J_heap_base.BinOpRed1 J_heap_base.BinOpRed2 J_heap_base.RedBinOp J_heap_base.RedVar
  J_heap_base.LAssRed J_heap_base.RedLAss J_heap_base.AAccRed1 J_heap_base.AAccRed2 J_heap_base.RedAAccNull
  J_heap_base.RedAAccBounds J_heap_base.RedAAcc J_heap_base.AAssRed1 J_heap_base.AAssRed2 J_heap_base.AAssRed3
  J_heap_base.RedAAssNull J_heap_base.RedAAssBounds J_heap_base.RedAAssStore J_heap_base.RedAAss J_heap_base.ALengthRed
  J_heap_base.RedALength J_heap_base.RedALengthNull J_heap_base.FAccRed J_heap_base.RedFAcc J_heap_base.RedFAccNull
  J_heap_base.FAssRed1 J_heap_base.FAssRed2 J_heap_base.RedFAss J_heap_base.RedFAssNull J_heap_base.CallObj
  J_heap_base.CallParams

declare
  J_heap_base.RedCall_code[code_pred_intro RedCall_code]
  J_heap_base.RedCallExternal_code[code_pred_intro RedCallExternal_code]
  J_heap_base.RedCallNull_code[code_pred_intro RedCallNull_code]

lemmas [code_pred_intro] =
  J_heap_base.BlockRed J_heap_base.RedBlock J_heap_base.SynchronizedRed1 J_heap_base.SynchronizedNull
  J_heap_base.LockSynchronized J_heap_base.SynchronizedRed2 J_heap_base.UnlockSynchronized
  J_heap_base.SeqRed J_heap_base.RedSeq J_heap_base.CondRed J_heap_base.RedCondT J_heap_base.RedCondF J_heap_base.RedWhile
  J_heap_base.ThrowRed

declare
  J_heap_base.RedThrowNull[code_pred_intro RedThrowNull']

lemmas [code_pred_intro] =
  J_heap_base.TryRed J_heap_base.RedTry J_heap_base.RedTryCatch
  J_heap_base.RedTryFail J_heap_base.ListRed1 J_heap_base.ListRed2
  J_heap_base.NewArrayThrow J_heap_base.CastThrow J_heap_base.InstanceOfThrow J_heap_base.BinOpThrow1 J_heap_base.BinOpThrow2
  J_heap_base.LAssThrow J_heap_base.AAccThrow1 J_heap_base.AAccThrow2 J_heap_base.AAssThrow1 J_heap_base.AAssThrow2
  J_heap_base.AAssThrow3 J_heap_base.ALengthThrow J_heap_base.FAccThrow J_heap_base.FAssThrow1 J_heap_base.FAssThrow2
  J_heap_base.CallThrowObj 

declare
  J_heap_base.CallThrowParams_code[code_pred_intro CallThrowParams_code]

lemmas [code_pred_intro] =
  J_heap_base.BlockThrow J_heap_base.SynchronizedThrow1 J_heap_base.SynchronizedThrow2 J_heap_base.SeqThrow
  J_heap_base.CondThrow

declare
  J_heap_base.ThrowThrow[code_pred_intro ThrowThrow']

code_pred
  (modes:
    J_heap_base.red: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool 
   and
    J_heap_base.reds: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)
  [detect_switches, skip_proof] -- "proofs are possible, but take veeerry long"
  J_heap_base.red
proof -
  case red
  from red.prems show thesis
  proof(cases rule: J_heap_base.red.cases[consumes 1, case_names
    RedNew RedNewFail NewArrayRed RedNewArray RedNewArrayNegative RedNewArrayFail CastRed RedCast RedCastFail InstanceOfRed
    RedInstanceOf BinOpRed1 BinOpRed2 RedBinOp RedVar LAssRed RedLAss AAccRed1 AAccRed2 RedAAccNull RedAAccBounds RedAAcc
    AAssRed1 AAssRed2 AAssRed3 RedAAssNull RedAAssBounds RedAAssStore RedAAss ALengthRed RedALength RedALengthNull FAccRed
    RedFAcc RedFAccNull FAssRed1 FAssRed2 RedFAss RedFAssNull CallObj CallParams RedCall RedCallExternal RedCallNull
    BlockRed RedBlock SynchronizedRed1 SynchronizedNull LockSynchronized SynchronizedRed2 UnlockSynchronized SeqRed
    RedSeq CondRed RedCondT RedCondF RedWhile ThrowRed RedThrowNull TryRed RedTry RedTryCatch RedTryFail
    NewArrayThrow CastThrow InstanceOfThrow BinOpThrow1 BinOpThrow2 LAssThrow AAccThrow1 AAccThrow2 AAssThrow1 AAssThrow2
    AAssThrow3 ALengthThrow FAccThrow FAssThrow1 FAssThrow2 CallThrowObj CallThrowParams BlockThrow SynchronizedThrow1 
    SynchronizedThrow2 SeqThrow CondThrow ThrowThrow])

    case (RedCall s a C M Ts T pns body D vs)
    with RedCall_code[OF refl refl refl refl refl refl refl refl refl refl, of a M "map Val vs" s pns D Ts body C T]
    show ?thesis by(simp add: o_def)
  next
    case (RedCallExternal s a T M vs ta va h' ta' e' s')
    with RedCallExternal_code[OF refl refl refl refl refl refl refl refl refl refl, of a M "map Val vs" s ta va h' T]
    show ?thesis by(simp add: o_def)
  next
    case (RedCallNull M vs s)
    with RedCallNull_code[OF refl refl refl refl refl refl refl refl refl refl, of M "map Val vs" s]
    show ?thesis by(simp add: o_def)
  next
    case (CallThrowParams es vs a es' v M s)
    with CallThrowParams_code[OF refl refl refl refl refl refl refl refl refl refl, of v M "map Val vs @ Throw a # es'" s]
    show ?thesis 
      apply(auto simp add: is_Throws_conv)
      apply(erule meta_impE)
      apply(subst dropWhile_append2)
      apply auto
      done
  next
    case RedThrowNull thus ?thesis
      by-(erule (4) RedThrowNull'[OF refl refl refl refl refl refl refl refl refl refl])
  next
    case ThrowThrow thus ?thesis
      by-(erule (4) ThrowThrow'[OF refl refl refl refl refl refl refl refl refl refl])
  qed(assumption|erule (4) that[OF refl refl refl refl refl refl refl refl refl refl])+
next
  case reds
  from reds.prems show thesis
    by(rule J_heap_base.reds.cases)(assumption|erule (4) that[OF refl refl refl refl refl refl refl refl refl refl])+
qed

end