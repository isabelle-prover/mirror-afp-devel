(*  Title:      JinjaThreads/Compiler/J1.thy
    Author:     Andreas Lochbihler
*)

header {* An intermediate language *}

theory J1 imports "J0" begin

types
  expr1 = "(nat,nat) exp"
  J1_prog = "expr1 prog"

  locals1 = "val list"

types
  J1state = "(expr1 \<times> locals1) list"

types
  J1_thread_action = "(addr,thread_id,(expr1 \<times> locals1) \<times> (expr1 \<times> locals1) list,heap,addr) thread_action"


consts
  max_vars:: "('a,'b) exp \<Rightarrow> nat"
  max_varss:: "('a,'b) exp list \<Rightarrow> nat"
primrec
"max_vars (new C) = 0"
"max_vars (newA T\<lfloor>e\<rceil>) = max_vars e"
"max_vars (Cast C e) = max_vars e"
"max_vars (Val v) = 0"
"max_vars (e \<guillemotleft>bop\<guillemotright> e') = max (max_vars e) (max_vars e')"
"max_vars (Var V) = 0"
"max_vars (V:=e) = max_vars e"
"max_vars (a\<lfloor>i\<rceil>) = max (max_vars a) (max_vars i)"
"max_vars (AAss a i e) = max (max (max_vars a) (max_vars i)) (max_vars e)"
"max_vars (a\<bullet>length) = max_vars a"
"max_vars (e\<bullet>F{D}) = max_vars e"
"max_vars (FAss e\<^isub>1 F D e\<^isub>2) = max (max_vars e\<^isub>1) (max_vars e\<^isub>2)"
"max_vars (e\<bullet>M(es)) = max (max_vars e) (max_varss es)"
"max_vars ({V:T=vo; e}\<^bsub>cr\<^esub>) = max_vars e + 1"
(* sync and insync will need an extra local variable when compiling to bytecode to store the object that is being synchronized on until its release *)
"max_vars (sync\<^bsub>V\<^esub> (e') e) = max (max_vars e') (max_vars e + 1)"
"max_vars (insync\<^bsub>V\<^esub> (a) e) = max_vars e + 1"
"max_vars (e\<^isub>1;;e\<^isub>2) = max (max_vars e\<^isub>1) (max_vars e\<^isub>2)"
"max_vars (if (e) e\<^isub>1 else e\<^isub>2) =
   max (max_vars e) (max (max_vars e\<^isub>1) (max_vars e\<^isub>2))"
"max_vars (while (b) e) = max (max_vars b) (max_vars e)"
"max_vars (throw e) = max_vars e"
"max_vars (try e\<^isub>1 catch(C V) e\<^isub>2) = max (max_vars e\<^isub>1) (max_vars e\<^isub>2 + 1)"

"max_varss [] = 0"
"max_varss (e#es) = max (max_vars e) (max_varss es)"

lemma max_varss_append [simp]:
  "max_varss (es @ es') = max (max_varss es) (max_varss es')"
by(induct es, auto)

definition extNTA2J1 :: "J1_prog \<Rightarrow> (cname \<times> mname \<times> addr) \<Rightarrow> ((expr1 \<times> locals1) \<times> (expr1 \<times> locals1) list)"
where "extNTA2J1 P = (\<lambda>(C, M, a). let body = snd (snd (snd (method P C M))) in ((body, Addr a # replicate (max_vars body) arbitrary), [(addr a\<bullet>M([]), [])]))"

lemma extNTA2J1_iff [simp]:
  "extNTA2J1 P (C, M, a) = ((snd (snd (snd (method P C M))), Addr a # replicate (max_vars (snd (snd (snd (method P C M))))) arbitrary), [(addr a\<bullet>M([]), [])])"
by(simp add: extNTA2J1_def)

abbreviation extTA2J1 :: "J1_prog \<Rightarrow> external_thread_action \<Rightarrow> J1_thread_action"
where "extTA2J1 P \<equiv> convert_extTA (extNTA2J1 P)"

abbreviation (input) extRet2J1 :: "val + addr \<Rightarrow> expr1"
where "extRet2J1 \<equiv> extRet2J"


lemma max_vars_extRet2J1 [simp]: 
  "max_vars (extRet2J1 va) = 0"
by(cases va) simp_all

inductive red1 :: "J1_prog \<Rightarrow> expr1 \<Rightarrow> heap \<times> locals1 \<Rightarrow> J1_thread_action \<Rightarrow> expr1 \<Rightarrow> heap \<times> locals1 \<Rightarrow> bool"
                 ("_ \<turnstile>1 ((1\<langle>_,/_\<rangle>) -_\<rightarrow>/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0,0] 81)
  and reds1 :: "J1_prog \<Rightarrow> expr1 list \<Rightarrow> heap \<times> locals1 \<Rightarrow> J1_thread_action \<Rightarrow> expr1 list \<Rightarrow> heap \<times> locals1 \<Rightarrow> bool"
                 ("_ \<turnstile>1 ((1\<langle>_,/_\<rangle>) [-_\<rightarrow>]/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0,0] 81)
for P :: J1_prog
where
  Red1New:
  "\<lbrakk> new_Addr h = Some a; P \<turnstile> C has_fields FDTs; h' = h(a\<mapsto>(Obj C (init_fields FDTs))) \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>new C, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>addr a, (h', l)\<rangle>"

| Red1NewFail:
  "new_Addr (hp s) = None
  \<Longrightarrow> P \<turnstile>1 \<langle>new C, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW OutOfMemory, s\<rangle>"

| New1ArrayRed:
  "P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>
  \<Longrightarrow> P \<turnstile>1 \<langle>newA T\<lfloor>e\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>newA T\<lfloor>e'\<rceil>, s'\<rangle>"

| Red1NewArray:
  "\<lbrakk> new_Addr h = Some a; i \<ge> 0; h' = h(a \<mapsto> (Arr T (replicate (nat i) (default_val T)))) \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>newA T\<lfloor>Val (Intg i)\<rceil>, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>addr a, (h', l)\<rangle>"

| Red1NewArrayNegative:
  "i < 0 \<Longrightarrow> P \<turnstile>1 \<langle>newA T\<lfloor>Val (Intg i)\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NegativeArraySize, s\<rangle>"

| Red1NewArrayFail:
  "\<lbrakk> new_Addr h = None; i \<ge> 0 \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>newA T\<lfloor>Val (Intg i)\<rceil>, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW OutOfMemory, (h, l)\<rangle>"

| Cast1Red:
  "P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>
  \<Longrightarrow> P \<turnstile>1 \<langle>Cast C e, s\<rangle> -ta\<rightarrow> \<langle>Cast C e', s'\<rangle>"

| Red1Cast:
 "\<lbrakk> typeof\<^bsub>hp s\<^esub> v = \<lfloor>U\<rfloor>; P \<turnstile> U \<le> T \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>Cast T (Val v), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| Red1CastFail:
  "\<lbrakk> typeof\<^bsub>hp s\<^esub> v = \<lfloor>U\<rfloor>; \<not> P \<turnstile> U \<le> T \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>Cast T (Val v), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ClassCast, s\<rangle>"

| Bin1OpRed1:
  "P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile>1 \<langle>e \<guillemotleft>bop\<guillemotright> e2, s\<rangle> -ta\<rightarrow> \<langle>e' \<guillemotleft>bop\<guillemotright> e2, s'\<rangle>"

| Bin1OpRed2:
  "P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile>1 \<langle>(Val v) \<guillemotleft>bop\<guillemotright> e, s\<rangle> -ta\<rightarrow> \<langle>(Val v) \<guillemotleft>bop\<guillemotright> e', s'\<rangle>"

| Red1BinOp:
  "binop(bop, v1, v2) = Some v \<Longrightarrow>
  P \<turnstile>1 \<langle>(Val v1) \<guillemotleft>bop\<guillemotright> (Val v2), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| Red1Var:
  "\<lbrakk> (lcl s)!V = v; V < size (lcl s) \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>Var V, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| LAss1Red:
  "P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>
  \<Longrightarrow> P \<turnstile>1 \<langle>V:=e, s\<rangle> -ta\<rightarrow> \<langle>V:=e', s'\<rangle>"

| Red1LAss:
  "V < size l
  \<Longrightarrow> P \<turnstile>1 \<langle>V:=(Val v), (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>unit, (h, l[V := v])\<rangle>"

| AAcc1Red1:
  "P \<turnstile>1 \<langle>a, s\<rangle> -ta\<rightarrow> \<langle>a', s'\<rangle> \<Longrightarrow> P \<turnstile>1 \<langle>a\<lfloor>i\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>a'\<lfloor>i\<rceil>, s'\<rangle>"

| AAcc1Red2:
  "P \<turnstile>1 \<langle>i, s\<rangle> -ta\<rightarrow> \<langle>i', s'\<rangle> \<Longrightarrow> P \<turnstile>1 \<langle>(Val a)\<lfloor>i\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>(Val a)\<lfloor>i'\<rceil>, s'\<rangle>"

| Red1AAccNull:
  "P \<turnstile>1 \<langle>null\<lfloor>Val i\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| Red1AAccBounds:
  "\<lbrakk> hp s a = Some(Arr T el); i < 0 \<or> i \<ge> int (length el) \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>(addr a)\<lfloor>Val (Intg i)\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ArrayIndexOutOfBounds, s\<rangle>"

| Red1AAcc:
  "\<lbrakk> hp s a = Some(Arr T el); i \<ge> 0; i < int (length el) \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>(addr a)\<lfloor>Val (Intg i)\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val (el ! nat i), s\<rangle>"

| AAss1Red1:
  "P \<turnstile>1 \<langle>a, s\<rangle> -ta\<rightarrow> \<langle>a', s'\<rangle> \<Longrightarrow> P \<turnstile>1 \<langle>a\<lfloor>i\<rceil> := e, s\<rangle> -ta\<rightarrow> \<langle>a'\<lfloor>i\<rceil> := e, s'\<rangle>"

| AAss1Red2:
  "P \<turnstile>1 \<langle>i, s\<rangle> -ta\<rightarrow> \<langle>i', s'\<rangle> \<Longrightarrow> P \<turnstile>1 \<langle>(Val a)\<lfloor>i\<rceil> := e, s\<rangle> -ta\<rightarrow> \<langle>(Val a)\<lfloor>i'\<rceil> := e, s'\<rangle>"

| AAss1Red3:
  "P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile>1 \<langle>AAss (Val a) (Val i) e, s\<rangle> -ta\<rightarrow> \<langle>(Val a)\<lfloor>Val i\<rceil> := e', s'\<rangle>"

| Red1AAssNull:
  "P \<turnstile>1 \<langle>AAss null (Val i) (Val e), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| Red1AAssBounds:
  "\<lbrakk> hp s a = Some(Arr T el); i < 0 \<or> i \<ge> int (length el) \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>AAss (addr a) (Val (Intg i)) (Val e), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ArrayIndexOutOfBounds, s\<rangle>"

| Red1AAssStore:
  "\<lbrakk> hp s a = Some(Arr T el); i \<ge> 0; i < int (length el); typeof\<^bsub>hp s\<^esub> w = \<lfloor>U\<rfloor>; \<not> (P \<turnstile> U \<le> T) \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>AAss (addr a) (Val (Intg i)) (Val w), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ArrayStore, s\<rangle>"

| Red1AAss:
  "\<lbrakk> h a = Some(Arr T el); i \<ge> 0; i < int (length el); typeof\<^bsub>h\<^esub> w = Some U; P \<turnstile> U \<le> T;
    h' = h(a \<mapsto> (Arr T (el[nat i := w]))) \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>AAss (addr a) (Val (Intg i)) (Val w), (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>unit, (h', l)\<rangle>"

| ALength1Red:
  "P \<turnstile>1 \<langle>a, s\<rangle> -ta\<rightarrow> \<langle>a', s'\<rangle> \<Longrightarrow> P \<turnstile>1 \<langle>a\<bullet>length, s\<rangle> -ta\<rightarrow> \<langle>a'\<bullet>length, s'\<rangle>"

| Red1ALength:
  "hp s a = \<lfloor>Arr T elem\<rfloor> \<Longrightarrow> P \<turnstile>1 \<langle>addr a\<bullet>length, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val (Intg (int (length elem))), s\<rangle>"

| Red1ALengthNull:
  "P \<turnstile>1 \<langle>null\<bullet>length, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| FAcc1Red:
  "P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile>1 \<langle>e\<bullet>F{D}, s\<rangle> -ta\<rightarrow> \<langle>e'\<bullet>F{D}, s'\<rangle>"

| Red1FAcc:
  "\<lbrakk> hp s a = Some(Obj C fs); fs(F,D) = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>(addr a)\<bullet>F{D}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| Red1FAccNull:
  "P \<turnstile>1 \<langle>null\<bullet>F{D}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| FAss1Red1:
  "P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile>1 \<langle>e\<bullet>F{D}:=e2, s\<rangle> -ta\<rightarrow> \<langle>e'\<bullet>F{D}:=e2, s'\<rangle>"

| FAss1Red2:
  "P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile>1 \<langle>FAss (Val v) F D e, s\<rangle> -ta\<rightarrow> \<langle>Val v\<bullet>F{D}:=e', s'\<rangle>"

| Red1FAss:
  "h a = Some(Obj C fs) \<Longrightarrow>
  P \<turnstile>1 \<langle>FAss (addr a) F D (Val v), (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>unit, (h(a \<mapsto> (Obj C (fs((F,D) \<mapsto> v)))), l)\<rangle>"

| Red1FAssNull:
  "P \<turnstile>1 \<langle>FAss null F D (Val v), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| Call1Obj:
  "P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile>1 \<langle>e\<bullet>M(es), s\<rangle> -ta\<rightarrow> \<langle>e'\<bullet>M(es), s'\<rangle>"

| Call1Params:
  "P \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow>
  P \<turnstile>1 \<langle>(Val v)\<bullet>M(es),s\<rangle> -ta\<rightarrow> \<langle>(Val v)\<bullet>M(es'),s'\<rangle>"

| Red1CallExternal:
  "\<lbrakk> typeof\<^bsub>hp s\<^esub> (Addr a) = \<lfloor>T\<rfloor>; is_external_call P T M (length vs); P \<turnstile> \<langle>a\<bullet>M(vs), hp s\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>;
     ta' = extTA2J1 P ta; e' = extRet2J1 va; s' = (h', lcl s) \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>(addr a)\<bullet>M(map Val vs), s\<rangle> -ta'\<rightarrow> \<langle>e', s'\<rangle>"

| Red1CallNull:
  "P \<turnstile>1 \<langle>null\<bullet>M(map Val vs), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| Block1RedNone:
  "\<lbrakk> P \<turnstile>1 \<langle>e, (h, x)\<rangle> -ta\<rightarrow> \<langle>e', (h', x')\<rangle>; V < size x \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>{V:T=None; e}\<^bsub>cr\<^esub>, (h, x)\<rangle> -ta\<rightarrow> \<langle>{V:T=None; e'}\<^bsub>cr\<^esub>, (h', x')\<rangle>"

| Block1RedSome:
  "\<lbrakk> P \<turnstile>1 \<langle>e, (h, x[V := v])\<rangle> -ta\<rightarrow> \<langle>e', (h', x')\<rangle>; V < size x \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>{V:T=\<lfloor>v\<rfloor>; e}\<^bsub>cr\<^esub>, (h, x)\<rangle> -ta\<rightarrow> \<langle>{V:T=None; e'}\<^bsub>cr\<^esub>, (h', x')\<rangle>"

| Red1BlockNone:
  "V < size (lcl s) \<Longrightarrow> P \<turnstile>1 \<langle>{V:T=None; Val u}\<^bsub>cr\<^esub>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val u, s\<rangle>"

| Red1BlockSome:
  "V < size xs \<Longrightarrow> P \<turnstile>1 \<langle>{V:T=\<lfloor>v\<rfloor>; Val u}\<^bsub>cr\<^esub>, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>Val u, (h, xs[V:=v])\<rangle>"

| Synchronized1Red1:
  "P \<turnstile>1 \<langle>o', s\<rangle> -ta\<rightarrow> \<langle>o'', s'\<rangle> \<Longrightarrow> P \<turnstile>1 \<langle>sync\<^bsub>V\<^esub> (o') e, s\<rangle> -ta\<rightarrow> \<langle>sync\<^bsub>V\<^esub> (o'') e, s'\<rangle>"

| Synchronized1Null:
  "V < length xs \<Longrightarrow> P \<turnstile>1 \<langle>sync\<^bsub>V\<^esub> (null) e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, (h, xs[V := Null])\<rangle>"

| Lock1Synchronized:
  "\<lbrakk> h a = \<lfloor>arrobj\<rfloor>; V < length xs \<rbrakk> \<Longrightarrow> P \<turnstile>1 \<langle>sync\<^bsub>V\<^esub> (addr a) e, (h, xs)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Lock\<rightarrow>a \<rbrace>\<rightarrow> \<langle>insync\<^bsub>V\<^esub> (a) e, (h, xs[V := Addr a])\<rangle>"

| Synchronized1Red2:
  "P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) e, s\<rangle> -ta\<rightarrow> \<langle>insync\<^bsub>V\<^esub> (a) e', s'\<rangle>"

| Unlock1Synchronized:
  "\<lbrakk> xs ! V = Addr a'; V < length xs \<rbrakk> \<Longrightarrow> P \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) (Val v), (h, xs)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a' \<rbrace>\<rightarrow> \<langle>Val v, (h, xs)\<rangle>"

| Unlock1SynchronizedNull:
  "\<lbrakk> xs ! V = Null; V < length xs \<rbrakk> \<Longrightarrow> P \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) (Val v), (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, (h, xs)\<rangle>"

| Unlock1SynchronizedFail:
  "\<lbrakk> xs ! V = Addr a'; V < length xs \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) (Val v), (h, xs)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a' \<rbrace>\<rightarrow> \<langle>THROW IllegalMonitorState, (h, xs)\<rangle>"

| Seq1Red:
  "P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile>1 \<langle>e;;e2, s\<rangle> -ta\<rightarrow> \<langle>e';;e2, s'\<rangle>"

| Red1Seq:
  "P \<turnstile>1 \<langle>Seq (Val v) e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>e, s\<rangle>"

| Cond1Red:
  "P \<turnstile>1 \<langle>b, s\<rangle> -ta\<rightarrow> \<langle>b', s'\<rangle> \<Longrightarrow> P \<turnstile>1 \<langle>if (b) e1 else e2, s\<rangle> -ta\<rightarrow> \<langle>if (b') e1 else e2, s'\<rangle>"

| Red1CondT:
  "P \<turnstile>1 \<langle>if (true) e1 else e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>e1, s\<rangle>"

| Red1CondF:
  "P \<turnstile>1 \<langle>if (false) e1 else e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>e2, s\<rangle>"

| Red1While:
  "P \<turnstile>1 \<langle>while(b) c, s\<rangle> -\<epsilon>\<rightarrow> \<langle>if (b) (c;;while(b) c) else unit, s\<rangle>"

| Throw1Red:
  "P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile>1 \<langle>throw e, s\<rangle> -ta\<rightarrow> \<langle>throw e', s'\<rangle>"

| Red1ThrowNull:
  "P \<turnstile>1 \<langle>throw null, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| Try1Red:
  "P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> P \<turnstile>1 \<langle>try e catch(C V) e2, s\<rangle> -ta\<rightarrow> \<langle>try e' catch(C V) e2, s'\<rangle>"

| Red1Try:
  "P \<turnstile>1 \<langle>try (Val v) catch(C V) e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| Red1TryCatch:
  "\<lbrakk> h a = Some(Obj D fs); P \<turnstile> D \<preceq>\<^sup>* C; V < length x \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>try (Throw a) catch(C V) e2, (h, x)\<rangle> -\<epsilon>\<rightarrow> \<langle>{V:Class C=None; e2}\<^bsub>False\<^esub>, (h, x[V := Addr a])\<rangle>"

| Red1TryFail:
  "\<lbrakk> hp s a = \<lfloor>Obj D fs\<rfloor>; \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>try (Throw a) catch(C V) e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"

| List1Red1:
  "P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P \<turnstile>1 \<langle>e#es,s\<rangle> [-ta\<rightarrow>] \<langle>e'#es,s'\<rangle>"

| List1Red2:
  "P \<turnstile>1 \<langle>es,s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow>
  P \<turnstile>1 \<langle>Val v # es,s\<rangle> [-ta\<rightarrow>] \<langle>Val v # es',s'\<rangle>"

| New1ArrayThrow: "P \<turnstile>1 \<langle>newA T\<lfloor>Throw a\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| Cast1Throw: "P \<turnstile>1 \<langle>Cast C (Throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| Bin1OpThrow1: "P \<turnstile>1 \<langle>(Throw a) \<guillemotleft>bop\<guillemotright> e\<^isub>2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| Bin1OpThrow2: "P \<turnstile>1 \<langle>(Val v\<^isub>1) \<guillemotleft>bop\<guillemotright> (Throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| LAss1Throw: "P \<turnstile>1 \<langle>V:=(Throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| AAcc1Throw1: "P \<turnstile>1 \<langle>(Throw a)\<lfloor>i\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| AAcc1Throw2: "P \<turnstile>1 \<langle>(Val v)\<lfloor>Throw a\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| AAss1Throw1: "P \<turnstile>1 \<langle>(Throw a)\<lfloor>i\<rceil> := e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| AAss1Throw2: "P \<turnstile>1 \<langle>(Val v)\<lfloor>Throw a\<rceil> := e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| AAss1Throw3: "P \<turnstile>1 \<langle>AAss (Val v) (Val i) (Throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| ALength1Throw: "P \<turnstile>1 \<langle>(Throw a)\<bullet>length, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| FAcc1Throw: "P \<turnstile>1 \<langle>(Throw a)\<bullet>F{D}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| FAss1Throw1: "P \<turnstile>1 \<langle>(Throw a)\<bullet>F{D}:=e\<^isub>2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| FAss1Throw2: "P \<turnstile>1 \<langle>FAss (Val v) F D (Throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| Call1ThrowObj: "P \<turnstile>1 \<langle>(Throw a)\<bullet>M(es), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| Call1ThrowParams: "\<lbrakk> es = map Val vs @ Throw a # es' \<rbrakk> \<Longrightarrow> P \<turnstile>1 \<langle>(Val v)\<bullet>M(es), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| Block1ThrowNone: "V < length (lcl s) \<Longrightarrow> P \<turnstile>1 \<langle>{V:T=None; Throw a}\<^bsub>cr\<^esub>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| Block1ThrowSome: "V < length xs \<Longrightarrow> P \<turnstile>1 \<langle>{V:T=\<lfloor>v\<rfloor>; Throw a}\<^bsub>cr\<^esub>, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, (h, xs[V := v])\<rangle>"
| Synchronized1Throw1: "P \<turnstile>1 \<langle>sync\<^bsub>V\<^esub> (Throw a) e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| Synchronized1Throw2:
  "\<lbrakk> xs ! V = Addr a'; V < length xs \<rbrakk> \<Longrightarrow> P \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Throw ad, (h, xs)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a' \<rbrace>\<rightarrow> \<langle>Throw ad, (h, xs)\<rangle>"
| Synchronized1Throw2Fail:
  "\<lbrakk> xs ! V = Addr a'; V < length xs \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Throw ad, (h, xs)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a' \<rbrace>\<rightarrow> \<langle>THROW IllegalMonitorState, (h, xs)\<rangle>"
| Synchronized1Throw2Null:
  "\<lbrakk> xs ! V = Null; V < length xs \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Throw ad, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, (h, xs)\<rangle>"
| Seq1Throw: "P \<turnstile>1 \<langle>(Throw a);;e\<^isub>2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| Cond1Throw: "P \<turnstile>1 \<langle>if (Throw a) e\<^isub>1 else e\<^isub>2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| Throw1Throw: "P \<turnstile>1 \<langle>throw(Throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"

inductive_cases red1_cases:
  "P \<turnstile>1 \<langle>new C, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile>1 \<langle>new T\<lfloor>e\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile>1 \<langle>e \<guillemotleft>bop\<guillemotright> e', s\<rangle> -ta\<rightarrow> \<langle>e'', s'\<rangle>"
  "P \<turnstile>1 \<langle>Var V, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile>1 \<langle>V:=e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile>1 \<langle>a\<lfloor>i\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile>1 \<langle>a\<lfloor>i\<rceil> := e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile>1 \<langle>a\<bullet>length, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile>1 \<langle>e\<bullet>F{D}, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile>1 \<langle>e\<bullet>F{D} := e2, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile>1 \<langle>e\<bullet>M(es), s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile>1 \<langle>{V:T=vo; e}\<^bsub>cr\<^esub>, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile>1 \<langle>sync\<^bsub>V\<^esub> (o') e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile>1 \<langle>e;;e', s\<rangle> -ta\<rightarrow> \<langle>e'', s'\<rangle>"
  "P \<turnstile>1 \<langle>throw e, s \<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "P \<turnstile>1 \<langle>try e catch(C V) e'', s \<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"

lemma red1_preserves_len: "P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> length (lcl s') = length (lcl s)"
  and reds1_preserves_len: "P \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> length (lcl s') = length (lcl s)"
by(induct rule: red1_reds1.inducts)(auto)

lemma reds1_preserves_elen: "P \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> length es' = length es"
by(induct es arbitrary: es')(auto elim: reds1.cases)

lemma red1_no_val [dest]:
  "P \<turnstile>1 \<langle>Val v, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> False"
by(auto elim: red1.cases)

lemma reds1_no_val [dest]:
  "P \<turnstile>1 \<langle>map Val vs, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> False"
apply(induct vs arbitrary: es')
apply(erule reds1.cases, auto)+
done

lemma no_reds1_map_Val_Throw [dest]:
  "P \<turnstile>1 \<langle>map Val vs @ Throw a # es,s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> False"
by(induct vs arbitrary: es')(auto elim: reds1.cases elim!: red1_cases)

lemma red1_hext_incr: "P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> hext (hp s) (hp s')"
  and reds1_hext_incr: "P \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> hext (hp s) (hp s')"
apply(induct rule: red1_reds1.inducts)
apply(auto simp del: fun_upd_apply intro: hext_new hext_upd_arr hext_upd_obj dest: new_Addr_SomeD red_external_hext)
done

lemma red1_no_Throw [dest]:
  "P \<turnstile>1 \<langle>Throw a, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> False"
by(auto elim: red1.cases)

lemma red1_max_vars_decr: "P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> max_vars e' \<le> max_vars e" 
  and reds1_max_varss_decr: "P \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> max_varss es' \<le> max_varss es"
apply(induct rule: red1_reds1.inducts)
apply(auto)
done 


primrec clearInitBlock :: "expr1 \<Rightarrow> locals1 \<Rightarrow> expr1 \<times> locals1"
  and clearInitBlocks :: "expr1 list \<Rightarrow> locals1 \<Rightarrow> expr1 list \<times> locals1"
where
  "clearInitBlock (new C) xs = (new C, xs)"
| "clearInitBlock (newA T\<lfloor>e\<rceil>) xs = (let (e', xs') = clearInitBlock e xs in (newA T\<lfloor>e'\<rceil>, xs'))"
| "clearInitBlock (Cast C e) xs = (let (e', xs') = clearInitBlock e xs in (Cast C e', xs'))"
| "clearInitBlock (Val v) xs = (Val v, xs)"
| "clearInitBlock (Var V) xs = (Var V, xs)"
| "clearInitBlock (V := e) xs = (let (e', xs') = clearInitBlock e xs in (V := e', xs'))"
| "clearInitBlock (e1\<guillemotleft>bop\<guillemotright>e2) xs =
   (if is_val e1
    then let (e2', xs') = clearInitBlock e2 xs in (e1\<guillemotleft>bop\<guillemotright>e2', xs')
    else let (e1', xs') = clearInitBlock e1 xs in (e1'\<guillemotleft>bop\<guillemotright>e2, xs'))"
| "clearInitBlock (a\<lfloor>i\<rceil>) xs =
   (if is_val a
    then let (i', xs') = clearInitBlock i xs in (a\<lfloor>i'\<rceil>, xs')
    else let (a', xs') = clearInitBlock a xs in (a'\<lfloor>i\<rceil>, xs'))"
| "clearInitBlock (a\<lfloor>i\<rceil>:=e) xs =
   (if is_val a
    then if is_val i then let (e', xs') = clearInitBlock e xs in (a\<lfloor>i\<rceil> := e', xs')
                     else let (i', xs') = clearInitBlock i xs in (a\<lfloor>i'\<rceil> := e, xs')
    else let (a', xs') = clearInitBlock a xs in (a'\<lfloor>i\<rceil> := e, xs'))"
| "clearInitBlock (a\<bullet>length) xs = (let (a', xs') = clearInitBlock a xs in (a'\<bullet>length, xs'))"
| "clearInitBlock (e\<bullet>F{D}) xs = (let (e', xs') = clearInitBlock e xs in (e'\<bullet>F{D}, xs'))"
| "clearInitBlock (e1\<bullet>F{D} := e2) xs =
   (if is_val e1
    then let (e2', xs') = clearInitBlock e2 xs in (e1\<bullet>F{D} := e2', xs')
    else let (e1', xs') = clearInitBlock e1 xs in (e1'\<bullet>F{D} := e2, xs'))"
| "clearInitBlock (e\<bullet>M(es)) xs =
   (if is_val e
    then let (es', xs') = clearInitBlocks es xs in (e\<bullet>M(es'), xs')
    else let (e', xs') = clearInitBlock e xs in (e'\<bullet>M(es), xs'))"
| "clearInitBlock {V:T=vo; e}\<^bsub>cr\<^esub> xs = (let (e', xs'') = clearInitBlock e (case vo of None \<Rightarrow> xs | \<lfloor>v\<rfloor> \<Rightarrow> xs[V := v])
                                    in ({V:T=None; e'}\<^bsub>cr\<^esub>, xs''))"
| "clearInitBlock (sync\<^bsub>V\<^esub> (o') e) xs = (let (o'', xs') = clearInitBlock o' xs in (sync\<^bsub>V\<^esub> (o'') e, xs'))"
| "clearInitBlock (insync\<^bsub>V\<^esub> (a) e) xs = (let (e', xs') = clearInitBlock e xs in (insync\<^bsub>V\<^esub> (a) e', xs'))"
| "clearInitBlock (e1;;e2) xs = (let (e1', xs') = clearInitBlock e1 xs in (e1';;e2, xs'))"
| "clearInitBlock (if (b) e1 else e2) xs = (let (b', xs') = clearInitBlock b xs in (if (b') e1 else e2, xs'))"
| "clearInitBlock (while (b) c) xs = (while (b) c, xs)"
| "clearInitBlock (throw e) xs = (let (e', xs') = clearInitBlock e xs in (throw e', xs'))"
| "clearInitBlock (try e1 catch(C V) e2) xs = (let (e1', xs') = clearInitBlock e1 xs in (try e1' catch(C V) e2, xs'))"

| "clearInitBlocks [] xs = ([], xs)"
| "clearInitBlocks (e # es) xs = 
   (if is_val e
    then let (es', xs') = clearInitBlocks es xs in (e # es', xs')
    else let (e', xs') = clearInitBlock e xs in (e' # es, xs'))"

lemma is_val_clearInitBlockD [simp]: "fst (clearInitBlock e xs) = Val v \<longleftrightarrow> e = Val v"
  and is_vals_clearInitBlocksD [simp]: "fst (clearInitBlocks es xs) = map Val vs \<longleftrightarrow> es = map Val vs"
apply(induct e and es arbitrary: xs v and xs vs)
apply(auto simp add: split_beta split: split_if_asm)
done

lemma call_clearInitBlock [simp]: "call (fst (clearInitBlock e xs)) = call e"
  and calls_clearInitBlocks [simp]: "calls (fst (clearInitBlocks es xs)) = calls es"
by(induct e and es arbitrary: xs and xs)(auto simp add: split_beta is_vals_conv)

lemma clearInitBlock_extRet2J1 [simp]:
  "clearInitBlock (extRet2J1 va) xs = (extRet2J1 va, xs)"
by(cases va) simp_all

fun blocks1 :: "nat \<Rightarrow> ty list \<Rightarrow> (nat,'b) exp \<Rightarrow> (nat,'b) exp"
where 
  "blocks1 n [] e = e"
| "blocks1 n (T#Ts) e = {n:T=None; blocks1 (Suc n) Ts e}\<^bsub>False\<^esub>"

inductive Red1 :: "J1_prog \<Rightarrow> (expr1 \<times> locals1) \<Rightarrow> (expr1 \<times> locals1) list \<Rightarrow> heap \<Rightarrow> J1_thread_action \<Rightarrow>
                           (expr1 \<times> locals1) \<Rightarrow> (expr1 \<times> locals1) list \<Rightarrow> heap \<Rightarrow> bool"
                ("_ \<turnstile>1 ((1\<langle>_'/_,/_\<rangle>) -_\<rightarrow>/ (1\<langle>_'/_,/_\<rangle>))" [51,0,0,0,0,0,0,0] 81)
for P ::J1_prog
where

  red1Red:
  "P \<turnstile>1 \<langle>e, (h, x)\<rangle> -ta\<rightarrow> \<langle>e', (h', x')\<rangle>
  \<Longrightarrow> P \<turnstile>1 \<langle>(e, x)/exs, h\<rangle> -ta\<rightarrow> \<langle>(e', x')/exs, h'\<rangle>"

| red1Call:
  "\<lbrakk> call e = \<lfloor>(a, M, vs)\<rfloor>; h a = \<lfloor>Obj C fs\<rfloor>; \<not> is_external_call P (Class C) M (length vs); P \<turnstile> C sees M:Ts\<rightarrow>T = body in D; 
     size vs = size Ts \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>(e, x)/exs, h\<rangle> -\<epsilon>\<rightarrow> \<langle>(blocks1 (Suc 0) Ts body, Addr a # vs @ replicate (max_vars body) arbitrary)/clearInitBlock e x#exs, h\<rangle>"

| red1Return:
  "\<lbrakk> call e = \<lfloor>aMvs\<rfloor>; final e' \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>(e', x')/(e, x)#exs, h\<rangle> -\<epsilon>\<rightarrow> \<langle>(inline_call e' (fst (clearInitBlock e x)), snd (clearInitBlock e x))/exs, h\<rangle>"


end

