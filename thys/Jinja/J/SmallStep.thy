(*  Title:      Jinja/J/SmallStep.thy
    Author:     Tobias Nipkow
    Copyright   2003 Technische Universitaet Muenchen
*)

header {* \isaheader{Small Step Semantics} *}

theory SmallStep
imports Expr State
begin

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


definition assigned :: "vname \<Rightarrow> expr \<Rightarrow> bool"
where
  "assigned V e  \<equiv>  \<exists>v e'. e = (V := Val v;; e')"

inductive_set
  red  :: "J_prog \<Rightarrow> ((expr \<times> state) \<times> (expr \<times> state)) set"
  and reds  :: "J_prog \<Rightarrow> ((expr list \<times> state) \<times> (expr list \<times> state)) set"
  and red' :: "J_prog \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> bool"
          ("_ \<turnstile> ((1\<langle>_,/_\<rangle>) \<rightarrow>/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  and reds' :: "J_prog \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> bool"
          ("_ \<turnstile> ((1\<langle>_,/_\<rangle>) [\<rightarrow>]/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  for P :: J_prog
where

  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<equiv> ((e,s), e',s') \<in> red P"
| "P \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle> \<equiv> ((es,s), es',s') \<in> reds P"

| RedNew:
  "\<lbrakk> new_Addr h = Some a; P \<turnstile> C has_fields FDTs; h' = h(a\<mapsto>(C,init_fields FDTs)) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>new C, (h,l)\<rangle> \<rightarrow> \<langle>addr a, (h',l)\<rangle>"

| RedNewFail:
  "new_Addr h = None \<Longrightarrow>
  P \<turnstile> \<langle>new C, (h,l)\<rangle> \<rightarrow> \<langle>THROW OutOfMemory, (h,l)\<rangle>"

| CastRed:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>Cast C e, s\<rangle> \<rightarrow> \<langle>Cast C e', s'\<rangle>"

| RedCastNull:
  "P \<turnstile> \<langle>Cast C null, s\<rangle> \<rightarrow> \<langle>null,s\<rangle>"

| RedCast:
 "\<lbrakk> hp s a = Some(D,fs); P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>Cast C (addr a), s\<rangle> \<rightarrow> \<langle>addr a, s\<rangle>"

| RedCastFail:
  "\<lbrakk> hp s a = Some(D,fs); \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>Cast C (addr a), s\<rangle> \<rightarrow> \<langle>THROW ClassCast, s\<rangle>"

| BinOpRed1:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e \<guillemotleft>bop\<guillemotright> e\<^isub>2, s\<rangle> \<rightarrow> \<langle>e' \<guillemotleft>bop\<guillemotright> e\<^isub>2, s'\<rangle>"

| BinOpRed2:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>(Val v\<^isub>1) \<guillemotleft>bop\<guillemotright> e, s\<rangle> \<rightarrow> \<langle>(Val v\<^isub>1) \<guillemotleft>bop\<guillemotright> e', s'\<rangle>"

| RedBinOp:
  "binop(bop,v\<^isub>1,v\<^isub>2) = Some v \<Longrightarrow>
  P \<turnstile> \<langle>(Val v\<^isub>1) \<guillemotleft>bop\<guillemotright> (Val v\<^isub>2), s\<rangle> \<rightarrow> \<langle>Val v,s\<rangle>"

| RedVar:
  "lcl s V = Some v \<Longrightarrow>
  P \<turnstile> \<langle>Var V,s\<rangle> \<rightarrow> \<langle>Val v,s\<rangle>"

| LAssRed:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>V:=e,s\<rangle> \<rightarrow> \<langle>V:=e',s'\<rangle>"

| RedLAss:
  "P \<turnstile> \<langle>V:=(Val v), (h,l)\<rangle> \<rightarrow> \<langle>unit, (h,l(V\<mapsto>v))\<rangle>"

| FAccRed:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<bullet>F{D}, s\<rangle> \<rightarrow> \<langle>e'\<bullet>F{D}, s'\<rangle>"

| RedFAcc:
  "\<lbrakk> hp s a = Some(C,fs); fs(F,D) = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<bullet>F{D}, s\<rangle> \<rightarrow> \<langle>Val v,s\<rangle>"

| RedFAccNull:
  "P \<turnstile> \<langle>null\<bullet>F{D}, s\<rangle> \<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| FAssRed1:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<bullet>F{D}:=e\<^isub>2, s\<rangle> \<rightarrow> \<langle>e'\<bullet>F{D}:=e\<^isub>2, s'\<rangle>"

| FAssRed2:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>Val v\<bullet>F{D}:=e, s\<rangle> \<rightarrow> \<langle>Val v\<bullet>F{D}:=e', s'\<rangle>"

| RedFAss:
  "h a = Some(C,fs) \<Longrightarrow>
  P \<turnstile> \<langle>(addr a)\<bullet>F{D}:=(Val v), (h,l)\<rangle> \<rightarrow> \<langle>unit, (h(a \<mapsto> (C,fs((F,D) \<mapsto> v))),l)\<rangle>"

| RedFAssNull:
  "P \<turnstile> \<langle>null\<bullet>F{D}:=Val v, s\<rangle> \<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| CallObj:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<bullet>M(es),s\<rangle> \<rightarrow> \<langle>e'\<bullet>M(es),s'\<rangle>"

| CallParams:
  "P \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>(Val v)\<bullet>M(es),s\<rangle> \<rightarrow> \<langle>(Val v)\<bullet>M(es'),s'\<rangle>"

| RedCall:
  "\<lbrakk> hp s a = Some(C,fs); P \<turnstile> C sees M:Ts\<rightarrow>T = (pns,body) in D; size vs = size pns; size Ts = size pns \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<bullet>M(map Val vs), s\<rangle> \<rightarrow> \<langle>blocks(this#pns, Class D#Ts, Addr a#vs, body), s\<rangle>"

| RedCallNull:
  "P \<turnstile> \<langle>null\<bullet>M(map Val vs),s\<rangle> \<rightarrow> \<langle>THROW NullPointer,s\<rangle>"

| BlockRedNone:
  "\<lbrakk> P \<turnstile> \<langle>e, (h,l(V:=None))\<rangle> \<rightarrow> \<langle>e', (h',l')\<rangle>; l' V = None; \<not> assigned V e \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>{V:T; e}, (h,l)\<rangle> \<rightarrow> \<langle>{V:T; e'}, (h',l'(V := l V))\<rangle>"

| BlockRedSome:
  "\<lbrakk> P \<turnstile> \<langle>e, (h,l(V:=None))\<rangle> \<rightarrow> \<langle>e', (h',l')\<rangle>; l' V = Some v;\<not> assigned V e \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>{V:T; e}, (h,l)\<rangle> \<rightarrow> \<langle>{V:T := Val v; e'}, (h',l'(V := l V))\<rangle>"

| InitBlockRed:
  "\<lbrakk> P \<turnstile> \<langle>e, (h,l(V\<mapsto>v))\<rangle> \<rightarrow> \<langle>e', (h',l')\<rangle>; l' V = Some v' \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>{V:T := Val v; e}, (h,l)\<rangle> \<rightarrow> \<langle>{V:T := Val v'; e'}, (h',l'(V := l V))\<rangle>"

| RedBlock:
  "P \<turnstile> \<langle>{V:T; Val u}, s\<rangle> \<rightarrow> \<langle>Val u, s\<rangle>"

| RedInitBlock:
  "P \<turnstile> \<langle>{V:T := Val v; Val u}, s\<rangle> \<rightarrow> \<langle>Val u, s\<rangle>"

| SeqRed:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e;;e\<^isub>2, s\<rangle> \<rightarrow> \<langle>e';;e\<^isub>2, s'\<rangle>"

| RedSeq:
  "P \<turnstile> \<langle>(Val v);;e\<^isub>2, s\<rangle> \<rightarrow> \<langle>e\<^isub>2, s\<rangle>"

| CondRed:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>if (e) e\<^isub>1 else e\<^isub>2, s\<rangle> \<rightarrow> \<langle>if (e') e\<^isub>1 else e\<^isub>2, s'\<rangle>"

| RedCondT:
  "P \<turnstile> \<langle>if (true) e\<^isub>1 else e\<^isub>2, s\<rangle> \<rightarrow> \<langle>e\<^isub>1, s\<rangle>"

| RedCondF:
  "P \<turnstile> \<langle>if (false) e\<^isub>1 else e\<^isub>2, s\<rangle> \<rightarrow> \<langle>e\<^isub>2, s\<rangle>"

| RedWhile:
  "P \<turnstile> \<langle>while(b) c, s\<rangle> \<rightarrow> \<langle>if(b) (c;;while(b) c) else unit, s\<rangle>"

| ThrowRed:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>throw e, s\<rangle> \<rightarrow> \<langle>throw e', s'\<rangle>"

| RedThrowNull:
  "P \<turnstile> \<langle>throw null, s\<rangle> \<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| TryRed:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>try e catch(C V) e\<^isub>2, s\<rangle> \<rightarrow> \<langle>try e' catch(C V) e\<^isub>2, s'\<rangle>"

| RedTry:
  "P \<turnstile> \<langle>try (Val v) catch(C V) e\<^isub>2, s\<rangle> \<rightarrow> \<langle>Val v, s\<rangle>"

| RedTryCatch:
  "\<lbrakk> hp s a = Some(D,fs); P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>try (Throw a) catch(C V) e\<^isub>2, s\<rangle> \<rightarrow> \<langle>{V:Class C := addr a; e\<^isub>2}, s\<rangle>"

| RedTryFail:
  "\<lbrakk> hp s a = Some(D,fs); \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>try (Throw a) catch(C V) e\<^isub>2, s\<rangle> \<rightarrow> \<langle>Throw a, s\<rangle>"

| ListRed1:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e#es,s\<rangle> [\<rightarrow>] \<langle>e'#es,s'\<rangle>"

| ListRed2:
  "P \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>Val v # es,s\<rangle> [\<rightarrow>] \<langle>Val v # es',s'\<rangle>"

-- "Exception propagation"

| CastThrow: "P \<turnstile> \<langle>Cast C (throw e), s\<rangle> \<rightarrow> \<langle>throw e, s\<rangle>"
| BinOpThrow1: "P \<turnstile> \<langle>(throw e) \<guillemotleft>bop\<guillemotright> e\<^isub>2, s\<rangle> \<rightarrow> \<langle>throw e, s\<rangle>"
| BinOpThrow2: "P \<turnstile> \<langle>(Val v\<^isub>1) \<guillemotleft>bop\<guillemotright> (throw e), s\<rangle> \<rightarrow> \<langle>throw e, s\<rangle>"
| LAssThrow: "P \<turnstile> \<langle>V:=(throw e), s\<rangle> \<rightarrow> \<langle>throw e, s\<rangle>"
| FAccThrow: "P \<turnstile> \<langle>(throw e)\<bullet>F{D}, s\<rangle> \<rightarrow> \<langle>throw e, s\<rangle>"
| FAssThrow1: "P \<turnstile> \<langle>(throw e)\<bullet>F{D}:=e\<^isub>2, s\<rangle> \<rightarrow> \<langle>throw e,s\<rangle>"
| FAssThrow2: "P \<turnstile> \<langle>Val v\<bullet>F{D}:=(throw e), s\<rangle> \<rightarrow> \<langle>throw e, s\<rangle>"
| CallThrowObj: "P \<turnstile> \<langle>(throw e)\<bullet>M(es), s\<rangle> \<rightarrow> \<langle>throw e, s\<rangle>"
| CallThrowParams: "\<lbrakk> es = map Val vs @ throw e # es' \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>(Val v)\<bullet>M(es), s\<rangle> \<rightarrow> \<langle>throw e, s\<rangle>"
| BlockThrow: "P \<turnstile> \<langle>{V:T; Throw a}, s\<rangle> \<rightarrow> \<langle>Throw a, s\<rangle>"
| InitBlockThrow: "P \<turnstile> \<langle>{V:T := Val v; Throw a}, s\<rangle> \<rightarrow> \<langle>Throw a, s\<rangle>"
| SeqThrow: "P \<turnstile> \<langle>(throw e);;e\<^isub>2, s\<rangle> \<rightarrow> \<langle>throw e, s\<rangle>"
| CondThrow: "P \<turnstile> \<langle>if (throw e) e\<^isub>1 else e\<^isub>2, s\<rangle> \<rightarrow> \<langle>throw e, s\<rangle>"
| ThrowThrow: "P \<turnstile> \<langle>throw(throw e), s\<rangle> \<rightarrow> \<langle>throw e, s\<rangle>"
(*<*)
lemmas red_reds_induct = red_reds.induct [split_format (complete)]
  and red_reds_inducts = red_reds.inducts [split_format (complete)]

inductive_cases [elim!]:
 "P \<turnstile> \<langle>V:=e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>e1;;e2,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
(*>*)

subsection{* The reflexive transitive closure *}

abbreviation
  Step :: "J_prog \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> bool"
          ("_ \<turnstile> ((1\<langle>_,/_\<rangle>) \<rightarrow>*/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  where "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<equiv> ((e,s), e',s') \<in> (red P)\<^sup>*"

abbreviation
  Steps :: "J_prog \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> bool"
          ("_ \<turnstile> ((1\<langle>_,/_\<rangle>) [\<rightarrow>]*/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  where "P \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>]* \<langle>es',s'\<rangle> \<equiv> ((es,s), es',s') \<in> (reds P)\<^sup>*"

lemma converse_rtrancl_induct_red[consumes 1]:
assumes "P \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow>* \<langle>e',(h',l')\<rangle>"
and "\<And>e h l. R e h l e h l"
and "\<And>e\<^isub>0 h\<^isub>0 l\<^isub>0 e\<^isub>1 h\<^isub>1 l\<^isub>1 e' h' l'.
       \<lbrakk> P \<turnstile> \<langle>e\<^isub>0,(h\<^isub>0,l\<^isub>0)\<rangle> \<rightarrow> \<langle>e\<^isub>1,(h\<^isub>1,l\<^isub>1)\<rangle>; R e\<^isub>1 h\<^isub>1 l\<^isub>1 e' h' l' \<rbrakk> \<Longrightarrow> R e\<^isub>0 h\<^isub>0 l\<^isub>0 e' h' l'"
shows "R e h l e' h' l'"
(*<*)
proof -
  { fix s s'
    assume reds: "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
       and base: "\<And>e s. R e (hp s) (lcl s) e (hp s) (lcl s)"
       and red\<^isub>1: "\<And>e\<^isub>0 s\<^isub>0 e\<^isub>1 s\<^isub>1 e' s'.
           \<lbrakk> P \<turnstile> \<langle>e\<^isub>0,s\<^isub>0\<rangle> \<rightarrow> \<langle>e\<^isub>1,s\<^isub>1\<rangle>; R e\<^isub>1 (hp s\<^isub>1) (lcl s\<^isub>1) e' (hp s') (lcl s') \<rbrakk>
           \<Longrightarrow> R e\<^isub>0 (hp s\<^isub>0) (lcl s\<^isub>0) e' (hp s') (lcl s')"
    from reds have "R e (hp s) (lcl s) e' (hp s') (lcl s')"
    proof (induct rule:converse_rtrancl_induct2)
      case refl show ?case by(rule base)
    next
      case (step e\<^isub>0 s\<^isub>0 e s)
      thus ?case by(blast intro:red\<^isub>1)
    qed
    }
  with assms show ?thesis by fastsimp
qed
(*>*)


subsection{*Some easy lemmas*}

lemma [iff]: "\<not> P \<turnstile> \<langle>[],s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle>"
(*<*)by(blast elim: reds.cases)(*>*)

lemma [iff]: "\<not> P \<turnstile> \<langle>Val v,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
(*<*)by(fastsimp elim: red.cases)(*>*)

lemma [iff]: "\<not> P \<turnstile> \<langle>Throw a,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
(*<*)by(fastsimp elim: red.cases)(*>*)


lemma red_hext_incr: "P \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle>  \<Longrightarrow> h \<unlhd> h'"
  and reds_hext_incr: "P \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle>  \<Longrightarrow> h \<unlhd> h'"
(*<*)
proof(induct rule:red_reds_inducts)
  case RedNew thus ?case
    by(fastsimp dest:new_Addr_SomeD simp:hext_def split:if_splits)
next
  case RedFAss thus ?case by(simp add:hext_def split:if_splits)
qed simp_all
(*>*)


lemma red_lcl_incr: "P \<turnstile> \<langle>e,(h\<^isub>0,l\<^isub>0)\<rangle> \<rightarrow> \<langle>e',(h\<^isub>1,l\<^isub>1)\<rangle> \<Longrightarrow> dom l\<^isub>0 \<subseteq> dom l\<^isub>1"
and "P \<turnstile> \<langle>es,(h\<^isub>0,l\<^isub>0)\<rangle> [\<rightarrow>] \<langle>es',(h\<^isub>1,l\<^isub>1)\<rangle> \<Longrightarrow> dom l\<^isub>0 \<subseteq> dom l\<^isub>1"
(*<*)by(induct rule: red_reds_inducts)(auto simp del:fun_upd_apply)(*>*)


lemma red_lcl_add: "P \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> (\<And>l\<^isub>0. P \<turnstile> \<langle>e,(h,l\<^isub>0++l)\<rangle> \<rightarrow> \<langle>e',(h',l\<^isub>0++l')\<rangle>)"
and "P \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> (\<And>l\<^isub>0. P \<turnstile> \<langle>es,(h,l\<^isub>0++l)\<rangle> [\<rightarrow>] \<langle>es',(h',l\<^isub>0++l')\<rangle>)"
(*<*)
proof (induct rule:red_reds_inducts)
  case RedCast thus ?case by(fastsimp intro:red_reds.intros)
next
  case RedCastFail thus ?case by(force intro:red_reds.intros)
next
  case RedFAcc thus ?case by(fastsimp intro:red_reds.intros)
next
  case RedCall thus ?case by(fastsimp intro:red_reds.intros)
next
  case (InitBlockRed e h l V v e' h' l' v' T l\<^isub>0)
  have IH: "\<And>l\<^isub>0. P \<turnstile> \<langle>e,(h, l\<^isub>0 ++ l(V \<mapsto> v))\<rangle> \<rightarrow> \<langle>e',(h', l\<^isub>0 ++ l')\<rangle>"
    and l'V: "l' V = Some v'" by fact+
  from IH have IH': "P \<turnstile> \<langle>e,(h, (l\<^isub>0 ++ l)(V \<mapsto> v))\<rangle> \<rightarrow> \<langle>e',(h', l\<^isub>0 ++ l')\<rangle>"
    by simp
  have "(l\<^isub>0 ++ l')(V := (l\<^isub>0 ++ l) V) = l\<^isub>0 ++ l'(V := l V)"
    by(rule ext)(simp add:map_add_def)
  with red_reds.InitBlockRed[OF IH'] l'V show ?case by(simp del:fun_upd_apply)
next
  case (BlockRedNone e h l V e' h' l' T l\<^isub>0)
  have IH: "\<And>l\<^isub>0. P \<turnstile> \<langle>e,(h, l\<^isub>0 ++ l(V := None))\<rangle> \<rightarrow> \<langle>e',(h', l\<^isub>0 ++ l')\<rangle>"
    and l'V: "l' V = None" and unass: "\<not> assigned V e" by fact+
  have "l\<^isub>0(V := None) ++ l(V := None) = (l\<^isub>0 ++ l)(V := None)"
    by(simp add:fun_eq_iff map_add_def)
  hence IH': "P \<turnstile> \<langle>e,(h, (l\<^isub>0++l)(V := None))\<rangle> \<rightarrow> \<langle>e',(h', l\<^isub>0(V := None) ++ l')\<rangle>"
    using IH[of "l\<^isub>0(V := None)"] by simp
  have "(l\<^isub>0(V := None) ++ l')(V := (l\<^isub>0 ++ l) V) = l\<^isub>0 ++ l'(V := l V)"
    by(simp add:fun_eq_iff map_add_def)
  with red_reds.BlockRedNone[OF IH' _ unass] l'V show ?case
    by(simp add: map_add_def)
next
  case (BlockRedSome e h l V e' h' l' v T l\<^isub>0)
  have IH: "\<And>l\<^isub>0. P \<turnstile> \<langle>e,(h, l\<^isub>0 ++ l(V := None))\<rangle> \<rightarrow> \<langle>e',(h', l\<^isub>0 ++ l')\<rangle>"
    and l'V: "l' V = Some v" and unass: "\<not> assigned V e" by fact+
  have "l\<^isub>0(V := None) ++ l(V := None) = (l\<^isub>0 ++ l)(V := None)"
    by(simp add:fun_eq_iff map_add_def)
  hence IH': "P \<turnstile> \<langle>e,(h, (l\<^isub>0++l)(V := None))\<rangle> \<rightarrow> \<langle>e',(h', l\<^isub>0(V := None) ++ l')\<rangle>"
    using IH[of "l\<^isub>0(V := None)"] by simp
  have "(l\<^isub>0(V := None) ++ l')(V := (l\<^isub>0 ++ l) V) = l\<^isub>0 ++ l'(V := l V)"
    by(simp add:fun_eq_iff map_add_def)
  with red_reds.BlockRedSome[OF IH' _ unass] l'V show ?case
    by(simp add:map_add_def)
next
  case RedTryCatch thus ?case by(fastsimp intro:red_reds.intros)
next
  case RedTryFail thus ?case by(force intro!:red_reds.intros)
qed (simp_all add:red_reds.intros)
(*>*)


lemma Red_lcl_add:
assumes "P \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow>* \<langle>e',(h',l')\<rangle>" shows "P \<turnstile> \<langle>e,(h,l\<^isub>0++l)\<rangle> \<rightarrow>* \<langle>e',(h',l\<^isub>0++l')\<rangle>"
(*<*)
using assms
proof(induct rule:converse_rtrancl_induct_red)
  case 1 thus ?case by simp
next
  case 2 thus ?case
    by (blast dest: red_lcl_add intro: converse_rtrancl_into_rtrancl)
qed
(*>*)


end
