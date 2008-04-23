(*  Title:      Jinja/J/SmallStep.thy
    ID:         $Id: SmallStep.thy,v 1.3 2008-04-23 08:43:37 alochbihler Exp $
    Author:     Tobias Nipkow, Andreas Lochbihler
    Copyright   2003 Technische Universitaet Muenchen
*)

header {* \isaheader{Small Step Semantics} *}

theory SmallStep imports Expr State "../Framework/FWState" "../Common/Exceptions" begin

consts blocks :: "vname list * ty list * val list * expr \<Rightarrow> expr"
recdef blocks "measure(\<lambda>(Vs,Ts,vs,e). size Vs)"
 "blocks(V#Vs, T#Ts, v#vs, e) = {V:T := Val v; blocks(Vs,Ts,vs,e)}"
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
  "\<lbrakk> expr_locks e = (\<lambda>ad. 0); length vs = length pns; length Ts = length pns \<rbrakk>
  \<Longrightarrow> expr_locks (blocks (pns, Ts, vs, e)) = (\<lambda>ad. 0)"
by(induct pns Ts vs e rule: blocks.induct)(auto)


constdefs
  assigned :: "vname \<Rightarrow> expr \<Rightarrow> bool"
  "assigned V e  \<equiv>  \<exists>v e'. e = (V := Val v;; e')"

inductive red :: "J_prog \<Rightarrow> expr \<Rightarrow> (heap \<times> locals) \<Rightarrow> (addr,thread_id,expr \<times> locals,heap,addr) thread_action \<Rightarrow> expr \<Rightarrow> (heap \<times> locals) \<Rightarrow> bool"
          ("_ \<turnstile> ((1\<langle>_,/_\<rangle>) -_\<rightarrow>/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0,0] 81)
for P :: J_prog
where
  RedNew:
  "\<lbrakk> new_Addr h = Some a; P \<turnstile> C has_fields FDTs; h' = h(a\<mapsto>(Obj C (init_fields FDTs))) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>new C, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>addr a, (h', l)\<rangle>"

| RedNewFail:
  "new_Addr (hp s) = None \<Longrightarrow>
  P \<turnstile> \<langle>new C, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW OutOfMemory, s\<rangle>"

| NewArrayRed:
  "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>newA T\<lfloor>e\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>newA T\<lfloor>e'\<rceil>, s'\<rangle>"

| RedNewArray:
  "\<lbrakk> new_Addr h = Some a; i \<ge> 0; h' = h(a \<mapsto> (Arr T i (\<lambda>i. default_val T))) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>newA T\<lfloor>Val (Intg i)\<rceil>, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>addr a, (h', l)\<rangle>"

| RedNewArrayNegative:
  "i < 0 \<Longrightarrow> P \<turnstile> \<langle>newA T\<lfloor>Val (Intg i)\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NegativeArraySize, s\<rangle>"

| RedNewArrayFail:
  "\<lbrakk> new_Addr h = None; i \<ge> 0 \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>newA T\<lfloor>Val (Intg i)\<rceil>, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW OutOfMemory, (h, l)\<rangle>"

| CastRed:
  "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>Cast C e, s\<rangle> -ta\<rightarrow> \<langle>Cast C e', s'\<rangle>"

| RedCast:
 "\<lbrakk> typeof\<^bsub>hp s\<^esub> v = \<lfloor>U\<rfloor>; P \<turnstile> U \<le> T \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>Cast T (Val v), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| RedCastFail:
  "\<lbrakk> typeof\<^bsub>hp s\<^esub> v = \<lfloor>U\<rfloor>; \<not> P \<turnstile> U \<le> T \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>Cast T (Val v), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ClassCast, s\<rangle>"

| BinOpRed1:
  "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e \<guillemotleft>bop\<guillemotright> e2, s\<rangle> -ta\<rightarrow> \<langle>e' \<guillemotleft>bop\<guillemotright> e2, s'\<rangle>"

| BinOpRed2:
  "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>(Val v) \<guillemotleft>bop\<guillemotright> e, s\<rangle> -ta\<rightarrow> \<langle>(Val v) \<guillemotleft>bop\<guillemotright> e', s'\<rangle>"

| RedBinOp:
  "binop(bop, v1, v2) = Some v \<Longrightarrow>
  P \<turnstile> \<langle>(Val v1) \<guillemotleft>bop\<guillemotright> (Val v2), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| RedVar:
  "lcl s V = Some v \<Longrightarrow>
  P \<turnstile> \<langle>Var V, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| LAssRed:
  "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>V:=e, s\<rangle> -ta\<rightarrow> \<langle>V:=e', s'\<rangle>"

| RedLAss:
  "P \<turnstile> \<langle>V:=(Val v), (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>unit, (h, l(V \<mapsto> v))\<rangle>"

| AAccRed1:
  "P \<turnstile> \<langle>a, s\<rangle> -ta\<rightarrow> \<langle>a', s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>a\<lfloor>i\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>a'\<lfloor>i\<rceil>, s'\<rangle>"

| AAccRed2:
  "P \<turnstile> \<langle>i, s\<rangle> -ta\<rightarrow> \<langle>i', s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>(Val a)\<lfloor>i\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>(Val a)\<lfloor>i'\<rceil>, s'\<rangle>"

| RedAAccNull:
  "P \<turnstile> \<langle>null\<lfloor>Val i\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| RedAAccBounds:
  "\<lbrakk> hp s a = Some(Arr T si el); i < 0 \<or> i \<ge> si \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<lfloor>Val (Intg i)\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ArrayIndexOutOfBounds, s\<rangle>"

| RedAAcc:
  "\<lbrakk> hp s a = Some(Arr T si el); i \<ge> 0; i < si \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<lfloor>Val (Intg i)\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val (el i), s\<rangle>"

| AAssRed1:
  "P \<turnstile> \<langle>a, s\<rangle> -ta\<rightarrow> \<langle>a', s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>a\<lfloor>i\<rceil> := e, s\<rangle> -ta\<rightarrow> \<langle>a'\<lfloor>i\<rceil> := e, s'\<rangle>"

| AAssRed2:
  "P \<turnstile> \<langle>i, s\<rangle> -ta\<rightarrow> \<langle>i', s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>(Val a)\<lfloor>i\<rceil> := e, s\<rangle> -ta\<rightarrow> \<langle>(Val a)\<lfloor>i'\<rceil> := e, s'\<rangle>"

| AAssRed3:
  "P \<turnstile> \<langle>(e::expr), s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>(Val a)\<lfloor>Val i\<rceil> := e, s\<rangle> -ta\<rightarrow> \<langle>(Val a)\<lfloor>Val i\<rceil> := e', s'\<rangle>"

| RedAAssNull:
  "P \<turnstile> \<langle>null\<lfloor>Val i\<rceil> := (Val e::expr), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| RedAAssBounds:
  "\<lbrakk> hp s a = Some(Arr T si el); i < 0 \<or> i \<ge> si \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<lfloor>Val (Intg i)\<rceil> := (Val e::expr), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ArrayIndexOutOfBounds, s\<rangle>"

| RedAAssStore:
  "\<lbrakk> hp s a = Some(Arr T si el); i \<ge> 0; i < si; typeof\<^bsub>hp s\<^esub> w = \<lfloor>U\<rfloor>; \<not>(P \<turnstile> U \<le> T) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<lfloor>Val (Intg i)\<rceil> := (Val w::expr), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ArrayStore, s\<rangle>"

| RedAAss:
  "\<lbrakk> h a = Some(Arr T s el); i \<ge> 0; i < s; typeof\<^bsub>h\<^esub> w = Some U; P \<turnstile> U \<le> T;
    h' = h(a \<mapsto> (Arr T s (el(i := w)))) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<lfloor>Val (Intg i)\<rceil> := Val w::expr, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>unit, (h', l)\<rangle>"

| FAccRed:
  "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>F{D}, s\<rangle> -ta\<rightarrow> \<langle>e'\<bullet>F{D}, s'\<rangle>"

| RedFAcc:
  "\<lbrakk> hp s a = Some(Obj C fs); fs(F,D) = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<bullet>F{D}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| RedFAccNull:
  "P \<turnstile> \<langle>null\<bullet>F{D}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| FAssRed1:
  "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>F{D}:=e2, s\<rangle> -ta\<rightarrow> \<langle>e'\<bullet>F{D}:=e2, s'\<rangle>"

| FAssRed2:
  "P \<turnstile> \<langle>(e::expr), s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>Val v\<bullet>F{D}:=e, s\<rangle> -ta\<rightarrow> \<langle>Val v\<bullet>F{D}:=e', s'\<rangle>"

| RedFAss:
  "h a = Some(Obj C fs) \<Longrightarrow>
  P \<turnstile> \<langle>(addr a)\<bullet>F{D}:=(Val v :: expr), (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>unit, (h(a \<mapsto> (Obj C (fs((F,D) \<mapsto> v)))), l)\<rangle>"

| RedFAssNull:
  "P \<turnstile> \<langle>null\<bullet>F{D}:=Val v::expr, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| CallObj:
  "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(es), s\<rangle> -ta\<rightarrow> \<langle>e'\<bullet>M(es), s'\<rangle>"

| CallParams:
  "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>(Val v)\<bullet>M((map Val vs) @ e # es), s\<rangle> -ta\<rightarrow> \<langle>(Val v)\<bullet>M((map Val vs) @ e' # es), s'\<rangle>"

| RedCall:
  "\<lbrakk> hp s a = Some(Obj C fs); P \<turnstile> C sees M:Ts\<rightarrow>T = (pns,body) in D; size vs = size pns; size Ts = size pns (*; \<not> threadstart P C M*) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<bullet>M(map Val vs), s\<rangle> -\<epsilon>\<rightarrow> \<langle>blocks(this#pns, Class D#Ts, Addr a#vs, body), s\<rangle>"

| RedNewThread:
  "\<lbrakk> hp s a = Some(Obj C fs); P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<bullet>start([]), s\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub> NewThread a (((Var this)\<bullet>run([])), [this \<mapsto> Addr a]) (hp s)\<rbrace>\<rightarrow> \<langle>unit, s\<rangle>"

| RedNewThreadFail:
  "\<lbrakk> hp s a = Some(Obj C fs); P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>(addr a)\<bullet>start([]), s\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub> ThreadExists a \<rbrace>\<rightarrow> \<langle>THROW IllegalThreadState, s\<rangle>"

| RedWait:
  "\<lbrakk> hp s a = \<lfloor>arrobj\<rfloor> \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<bullet>wait([]), s\<rangle> -\<epsilon>\<lbrace>\<^bsub>w\<^esub> Suspend a \<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a \<rbrace>\<rightarrow> \<langle>unit, s\<rangle>"

| RedWaitFail:
  "\<lbrakk> hp s a = \<lfloor>arrobj\<rfloor> \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<bullet>wait([]), s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a \<rbrace>\<rightarrow> \<langle>THROW IllegalMonitorState, s\<rangle>"

| RedNotify:
  "\<lbrakk> hp s a = \<lfloor>arrobj\<rfloor> \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<bullet>notify([]), s\<rangle> -\<epsilon>\<lbrace>\<^bsub>w\<^esub> Notify a \<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a \<rbrace>\<rightarrow> \<langle>unit, s\<rangle>"

| RedNotifyFail:
  "\<lbrakk> hp s a = \<lfloor>arrobj\<rfloor> \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<bullet>notify([]), s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a \<rbrace>\<rightarrow> \<langle>THROW IllegalMonitorState, s\<rangle>"

| RedNotifyAll:
  "\<lbrakk> hp s a = \<lfloor>arrobj\<rfloor> \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<bullet>notifyAll([]), s\<rangle> -\<epsilon>\<lbrace>\<^bsub>w\<^esub> NotifyAll a \<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a \<rbrace>\<rightarrow> \<langle>unit, s\<rangle>"

| RedNotifyAllFail:
  "\<lbrakk> hp s a = \<lfloor>arrobj\<rfloor> \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<bullet>notifyAll([]), s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a \<rbrace>\<rightarrow> \<langle>THROW IllegalMonitorState, s\<rangle>"

| RedJoin:
  "\<lbrakk> hp s a = Some(Obj C fs); P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<bullet>join([]), s\<rangle> -\<epsilon>\<lbrace>\<^bsub>c\<^esub> Join a\<rbrace>\<rightarrow> \<langle>unit, s\<rangle>"

| RedCallNull:
  "P \<turnstile> \<langle>null\<bullet>M(map Val vs), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| BlockRedNone:
  "\<lbrakk> P \<turnstile> \<langle>e, (h, l(V:=None))\<rangle> -ta\<rightarrow> \<langle>e', (h', l')\<rangle>;
     l' V = None; \<not> assigned V e \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>{V:T; e}, (h, l)\<rangle> -ta\<rightarrow> \<langle>{V:T; e'}, (h', l'(V := l V))\<rangle>"

| BlockRedSome:
  "\<lbrakk> P \<turnstile> \<langle>e, (h, l(V:=None))\<rangle> -ta\<rightarrow> \<langle>e', (h', l')\<rangle>;
     l' V = Some v; \<not> assigned V e \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>{V:T; e}, (h, l)\<rangle> -ta\<rightarrow> \<langle>{V:T := Val v; e'}, (h', l'(V := l V))\<rangle>"

| InitBlockRed:
  "\<lbrakk> P \<turnstile> \<langle>e, (h, l(V \<mapsto> v))\<rangle> -ta\<rightarrow> \<langle>e', (h', l')\<rangle>; l' V = Some v' \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>{V:T := Val v; e}, (h, l)\<rangle> -ta\<rightarrow> \<langle>{V:T := Val v'; e'}, (h', l'(V := l V))\<rangle>"

| RedBlock:
  "P \<turnstile> \<langle>{V:T; Val u}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val u, s\<rangle>"

| RedInitBlock:
  "P \<turnstile> \<langle>{V:T := Val v; Val u}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val u, s\<rangle>"

(* Locking mechanism:
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
  changes the evaluation result of this last step, the thread then will try to synchronize on the new object. *)

| SynchronizedRed1:
  "P \<turnstile> \<langle>o', s\<rangle> -ta\<rightarrow> \<langle>o'', s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>sync(o') e, s\<rangle> -ta\<rightarrow> \<langle>sync(o'') e, s'\<rangle>"

| SynchronizedNull:
  "P \<turnstile> \<langle>sync(null) e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| LockSynchronized:
  "hp s a = \<lfloor>arrobj\<rfloor> \<Longrightarrow> P \<turnstile> \<langle>sync(addr a) e, s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Lock\<rightarrow>a \<rbrace>\<rightarrow> \<langle>insync(a) e, s\<rangle>"

| SynchronizedRed2:
  "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>insync(a) e, s\<rangle> -ta\<rightarrow> \<langle>insync(a) e', s'\<rangle>"

| UnlockSynchronized:
  "P \<turnstile> \<langle>insync(a) (Val v), s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a \<rbrace>\<rightarrow> \<langle>Val v, s\<rangle>"

| SeqRed:
  "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e;;e2, s\<rangle> -ta\<rightarrow> \<langle>e';;e2, s'\<rangle>"

| RedSeq:
  "P \<turnstile> \<langle>(Val v);;e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>e, s\<rangle>"

| CondRed:
  "P \<turnstile> \<langle>b, s\<rangle> -ta\<rightarrow> \<langle>b', s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>if (b) e1 else e2, s\<rangle> -ta\<rightarrow> \<langle>if (b') e1 else e2, s'\<rangle>"

| RedCondT:
  "P \<turnstile> \<langle>if (true) e1 else e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>e1, s\<rangle>"

| RedCondF:
  "P \<turnstile> \<langle>if (false) e1 else e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>e2, s\<rangle>"

| RedWhile:
  "P \<turnstile> \<langle>while(b) c, s\<rangle> -\<epsilon>\<rightarrow> \<langle>if (b) (c;;while(b) c) else unit, s\<rangle>"

| ThrowRed:
  "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>throw e, s\<rangle> -ta\<rightarrow> \<langle>throw e', s'\<rangle>"

| RedThrowNull:
  "P \<turnstile> \<langle>throw null, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| TryRed:
  "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>try e catch(C V) e2, s\<rangle> -ta\<rightarrow> \<langle>try e' catch(C V) e2, s'\<rangle>"

| RedTry:
  "P \<turnstile> \<langle>try (Val v) catch(C V) e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| RedTryCatch:
  "\<lbrakk> hp s a = Some(Obj D fs); P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>try (Throw a) catch(C V) e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>{V:Class C := addr a; e2}, s\<rangle>"

| RedTryFail:
  "\<lbrakk> hp s a = Some(Obj D fs); \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>try (Throw a) catch(C V) e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"

-- "Exception propagation"

| NewArrayThrow: "P \<turnstile> \<langle>newA T\<lfloor>throw a\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>throw a, s\<rangle>"
| CastThrow: "P \<turnstile> \<langle>Cast C (throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>throw a, s\<rangle>"
| BinOpThrow1: "P \<turnstile> \<langle>(throw a) \<guillemotleft>bop\<guillemotright> e\<^isub>2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>throw a, s\<rangle>"
| BinOpThrow2: "P \<turnstile> \<langle>(Val v\<^isub>1) \<guillemotleft>bop\<guillemotright> (throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>throw a, s\<rangle>"
| LAssThrow: "P \<turnstile> \<langle>V:=(throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>throw a, s\<rangle>"
| AAccThrow1: "P \<turnstile> \<langle>(throw a)\<lfloor>i\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>throw a, s\<rangle>"
| AAccThrow2: "P \<turnstile> \<langle>(Val v)\<lfloor>throw a\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>throw a, s\<rangle>"
| AAssThrow1: "P \<turnstile> \<langle>(throw a)\<lfloor>i\<rceil> := e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>throw a, s\<rangle>"
| AAssThrow2: "P \<turnstile> \<langle>(Val v)\<lfloor>throw a\<rceil> := e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>throw a, s\<rangle>"
| AAssThrow3: "P \<turnstile> \<langle>(Val v)\<lfloor>Val i\<rceil> := throw a :: expr, s\<rangle> -\<epsilon>\<rightarrow> \<langle>throw a, s\<rangle>"
| FAccThrow: "P \<turnstile> \<langle>(throw a)\<bullet>F{D}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>throw a, s\<rangle>"
| FAssThrow1: "P \<turnstile> \<langle>(throw a)\<bullet>F{D}:=e\<^isub>2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>throw a, s\<rangle>"
| FAssThrow2: "P \<turnstile> \<langle>Val v\<bullet>F{D}:=(throw a::expr), s\<rangle> -\<epsilon>\<rightarrow> \<langle>throw a, s\<rangle>"
| CallThrowObj: "P \<turnstile> \<langle>(throw a)\<bullet>M(es), s\<rangle> -\<epsilon>\<rightarrow> \<langle>throw a, s\<rangle>"
| CallThrowParams: "\<lbrakk> es = map Val vs @ throw a # es' \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>(Val v)\<bullet>M(es), s\<rangle> -\<epsilon>\<rightarrow> \<langle>throw a, s\<rangle>"
| BlockThrow: "P \<turnstile> \<langle>{V:T; Throw a}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| InitBlockThrow: "P \<turnstile> \<langle>{V:T := Val v; Throw a}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| SynchronizedThrow1: "P \<turnstile> \<langle>sync(throw a) e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>throw a, s\<rangle>"
| SynchronizedThrow2: "P \<turnstile> \<langle>insync(a) throw ad, s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a \<rbrace>\<rightarrow> \<langle>throw ad, s\<rangle>"
| SeqThrow: "P \<turnstile> \<langle>(throw a);;e\<^isub>2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>throw a, s\<rangle>"
| CondThrow: "P \<turnstile> \<langle>if (throw a) e\<^isub>1 else e\<^isub>2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>throw a, s\<rangle>"
| ThrowThrow: "P \<turnstile> \<langle>throw(throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>throw a, s\<rangle>"

inductive_cases red_cases:
  "P \<turnstile> \<langle>new C, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile> \<langle>newA T\<lfloor>e\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile> \<langle>Cast T e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile> \<langle>e \<guillemotleft>bop\<guillemotright> e', s\<rangle> -ta\<rightarrow> \<langle>e'', s'\<rangle>"
  "P \<turnstile> \<langle>Var V, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile> \<langle>V:=e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile> \<langle>a\<lfloor>i\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile> \<langle>a\<lfloor>i\<rceil> := e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile> \<langle>e\<bullet>F{D}, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile> \<langle>e\<bullet>F{D} := e', s\<rangle> -ta\<rightarrow> \<langle>e'', s'\<rangle>"
  "P \<turnstile> \<langle>e\<bullet>start([]), s\<rangle> -ta\<rightarrow> \<langle>e'', s'\<rangle>"
  "P \<turnstile> \<langle>e\<bullet>wait([]), s\<rangle> -ta\<rightarrow> \<langle>e'', s'\<rangle>"
  "P \<turnstile> \<langle>e\<bullet>notify([]), s\<rangle> -ta\<rightarrow> \<langle>e'', s'\<rangle>"
  "P \<turnstile> \<langle>e\<bullet>notifyAll([]), s\<rangle> -ta\<rightarrow> \<langle>e'', s'\<rangle>"
  "P \<turnstile> \<langle>e\<bullet>join([]), s\<rangle> -ta\<rightarrow> \<langle>e'', s'\<rangle>"
  "P \<turnstile> \<langle>e\<bullet>M(es), s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile> \<langle>{V:T; e}, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile> \<langle>sync(o') e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile> \<langle>insync(a) e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile> \<langle>e;;e', s\<rangle> -ta\<rightarrow> \<langle>e'', s'\<rangle>"
  "P \<turnstile> \<langle>if (b) e1 else e2, s \<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile> \<langle>while (b) e, s \<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile> \<langle>throw e, s \<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile> \<langle>try e catch(C V) e', s\<rangle> -ta\<rightarrow> \<langle>e'', s'\<rangle>"

subsection{* The reflexive transitive closure *}

abbreviation
  Step :: "J_prog \<Rightarrow> expr \<Rightarrow> (heap \<times> locals) \<Rightarrow> (addr,thread_id,expr \<times> locals,heap,addr) thread_action list \<Rightarrow> expr \<Rightarrow> (heap \<times> locals) \<Rightarrow> bool"
          ("_ \<turnstile> ((1\<langle>_,/_\<rangle>) -_\<rightarrow>*/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0,0] 81)
where
  "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow>* \<langle>e', s'\<rangle> == stepify_pred (\<lambda>(e, s) ta (e', s'). red P e s ta e' s') (e,s) ta (e',s')"

lemmas Step_induct = stepify_pred.induct[where r = "\<lambda>(e, s) ta (e', s'). red P e s ta e' s'", split_format (complete), simplified, consumes 1, case_names refl step]

subsection{*Some easy lemmas*}

lemma [iff]:
  "\<not> P \<turnstile> \<langle>Val v, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
by(fastsimp elim:red.cases)

lemma red_no_val [dest]:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -tas\<rightarrow> \<langle>e', s'\<rangle>; is_val e \<rbrakk> \<Longrightarrow> False"
by(auto)


lemma [iff]: "\<not> P \<turnstile> \<langle>Throw a, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
by(fastsimp elim: red.cases)

lemma red_hext_incr:
  "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> hp s \<unlhd> hp s'"
proof(induct rule:red.induct)
  case (RedNew C FDTs a h h' l) thus ?case by(auto dest: new_Addr_SomeD intro: hext_new simp del: fun_upd_apply)
next
  case RedNewArray thus ?case by(auto dest: new_Addr_SomeD intro: hext_new simp del: fun_upd_apply)
next
  case RedAAss thus ?case by(fastsimp dest:new_Addr_SomeD simp:hext_def split:if_splits)
next
  case RedFAss thus ?case by(fastsimp simp add:hext_def split:if_splits)
qed fastsimp+

lemma red_lcl_incr:
  "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> dom (lcl s) \<subseteq> dom (lcl s')"
apply(induct rule:red.induct)
by(auto simp del: fun_upd_apply)

lemma red_lcl_add_aux: 
  "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e, (hp s, l0 ++ lcl s)\<rangle> -ta\<rightarrow> \<langle>e', (hp s', l0 ++ lcl s')\<rangle>"
proof (induct arbitrary: l0 rule:red.induct) prefer 38
  case (RedNewThread s a C fs l0)
  hence "P \<turnstile> \<langle>addr a\<bullet>start([]),(hp s, l0 ++ lcl s)\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub> NewThread a ((Var this\<bullet>run([])), [this \<mapsto> Addr a]) (hp (hp s, l0 ++ lcl s))\<rbrace>\<rightarrow> \<langle>unit,(hp s, l0 ++ lcl s)\<rangle>"
    by(fastsimp intro: red.RedNewThread)
  thus ?case by(simp)
next prefer 46
  case (BlockRedNone E H L V TA E' H' L' T L0)
  have red: "P \<turnstile> \<langle>E, (H, L(V := None))\<rangle> -TA\<rightarrow> \<langle>E', (H', L')\<rangle>" .
  have IH: "\<And>l0. P \<turnstile> \<langle>E,(hp (H, L(V := None)), l0 ++ lcl (H, L(V := None)))\<rangle> -TA\<rightarrow> \<langle>E',(hp (H', L'), l0 ++ lcl (H', L'))\<rangle>" .
  have l'V: "L' V = None"
   and unass: "\<not> assigned V E" .
  have lrew: "\<And>l l'. l(V := None) ++ l'(V := None) = (l ++ l')(V := None)" 
    by(simp add:expand_fun_eq map_add_def)
  have lrew1: "(L0(V := None) ++ L')(V := (L0 ++ L) V) = L0 ++ L'(V := L V)"
    by(simp add:expand_fun_eq map_add_def)
  from IH[of "L0(V := None)"] have "P \<turnstile> \<langle>E,(H, (L0 ++ L)(V := None))\<rangle> -TA\<rightarrow> \<langle>E',(H', L0(V := None) ++ L')\<rangle>" by(simp add: lrew)
  with l'V red unass
  show ?case
    apply(clarsimp simp del:fun_upd_apply)
    apply(simp only: lrew1[THEN sym])
    apply(erule red.BlockRedNone)
    by(simp)+
next prefer 46
  case (BlockRedSome E H L V TA E' H' L' v T L0)
  have IH: "\<And>l0. P \<turnstile> \<langle>E,(hp (H, L(V := None)), l0 ++ lcl (H, L(V := None)))\<rangle> -TA\<rightarrow> \<langle>E',(hp (H', L'), l0 ++ lcl (H', L'))\<rangle>" .
  have l'V: "L' V = Some v"
   and unass: "\<not> assigned V E" .
  have red: "P \<turnstile> \<langle>E,(H, L(V := None))\<rangle> -TA\<rightarrow> \<langle>E',(H', L')\<rangle>" .
  have lrew: "\<And>l l'. l(V := None) ++ l'(V := None) = (l ++ l')(V := None)" 
    by(simp add:expand_fun_eq map_add_def)
  have lrew1: "(L0(V := None) ++ L')(V := (L0 ++ L) V) = L0 ++ L'(V := L V)"
    by(simp add:expand_fun_eq map_add_def)
  from IH[of "L0(V := None)"] 
  have "P \<turnstile> \<langle>E,(H, (L0 ++ L)(V := None))\<rangle> -TA\<rightarrow> \<langle>E',(H', L0(V := None) ++ L')\<rangle>" by (simp add: lrew)
  with l'V red unass
  show ?case
    apply(clarsimp simp del:fun_upd_apply)
    apply(simp only: lrew1[THEN sym])
    apply(erule red.BlockRedSome)
    by(simp)+
next prefer 46
  case (InitBlockRed E H L V v TA E' H' L' v' T L0)
  have red: "P \<turnstile> \<langle>E,(H, L(V \<mapsto> v))\<rangle> -TA\<rightarrow> \<langle>E',(H', L')\<rangle>" .
  have IH: "\<And>l0. P \<turnstile> \<langle>E,(hp (H, L(V \<mapsto> v)), l0 ++ lcl (H, L(V \<mapsto> v)))\<rangle> -TA\<rightarrow> \<langle>E',(hp (H', L'), l0 ++ lcl (H', L'))\<rangle>" .
  have l'V: "L' V = \<lfloor>v'\<rfloor>" .
  have lrew: "(L0 ++ L')(V := (L0 ++ L) V) = L0 ++ L'(V := L V)" by (rule ext)(simp add: map_add_def)
  from IH[of "L0"] l'V show ?case
    apply(clarsimp simp del:fun_upd_apply)
    apply(simp only: lrew[THEN sym])
    apply(rule red.InitBlockRed)
    by(simp_all)
next
  case (RedTryFail s a D fs C V e2 l0) thus ?case
    by(auto intro: red.RedTryFail)
qed (fastsimp intro:red.intros simp del: fun_upd_apply)+

lemma red_lcl_add:
  "P \<turnstile> \<langle>e, (h, l)\<rangle> -ta\<rightarrow> \<langle>e', (h', l')\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e, (h, l0 ++ l)\<rangle> -ta\<rightarrow> \<langle>e', (h', l0 ++ l')\<rangle>"
by(auto dest:red_lcl_add_aux
)
lemma Step_lcl_add:
  "P \<turnstile> \<langle>e, (h, l)\<rangle> -ta\<rightarrow>* \<langle>e', (h', l')\<rangle> \<Longrightarrow>  P \<turnstile> \<langle>e, (h, l0 ++ l)\<rangle> -ta\<rightarrow>* \<langle>e', (h', l0 ++ l')\<rangle>"
proof(induct rule: Step_induct)
  case refl thus ?case by(auto intro: stepify_pred.intros)
next
  case (step e h l ta e' h' l' las tas cas was e'' h'' l'')
  have IH: "P \<turnstile> \<langle>e,(h, l0 ++ l)\<rangle> -ta\<rightarrow>* \<langle>e',(h', l0 ++ l')\<rangle>"
   and red: "P \<turnstile> \<langle>e',(h', l')\<rangle> -(las, tas, cas, was)\<rightarrow> \<langle>e'',(h'', l'')\<rangle>" .
  from red have "P \<turnstile> \<langle>e',(h', l0 ++ l')\<rangle> -(las, tas, cas, was)\<rightarrow> \<langle>e'',(h'', l0 ++ l'')\<rangle>" by - (rule red_lcl_add)
  with IH show ?case
    by(auto elim: stepify_pred_step)
qed


inductive final :: "expr \<Rightarrow> bool" where
  "final (Val v)"
| "final (Throw a)"

declare final.cases [elim]
declare final.intros[simp]

lemmas finalE[consumes 1, case_names Val Throw] = final.cases

lemma final_iff: "final e \<longleftrightarrow> (\<exists>v. e = Val v) \<or> (\<exists>a. e = Throw a)"
by(auto)

lemma final_locks: "final e \<Longrightarrow> expr_locks e l = 0"
by(auto elim: finalE)

end