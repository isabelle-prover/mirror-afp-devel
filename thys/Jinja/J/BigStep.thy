(*  Title:      Jinja/J/BigStep.thy
    ID:         $Id: BigStep.thy,v 1.5 2006-05-27 15:32:27 makarius Exp $
    Author:     Tobias Nipkow
    Copyright   2003 Technische Universitaet Muenchen
*)

header {* \isaheader{Big Step Semantics} *}

theory BigStep imports Expr State begin

consts
  eval  :: "J_prog \<Rightarrow> ((expr \<times> state) \<times> (expr \<times> state)) set"
  evals  :: "J_prog \<Rightarrow> ((expr list \<times> state) \<times> (expr list \<times> state)) set"

(*<*)
syntax (xsymbols)
  eval :: "J_prog \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> bool"
          ("_ \<turnstile> ((1\<langle>_,/_\<rangle>) \<Rightarrow>/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  evals :: "J_prog \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> bool"
           ("_ \<turnstile> ((1\<langle>_,/_\<rangle>) [\<Rightarrow>]/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
(*>*)

translations
  "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"  ==  "((e,s), e',s') \<in> eval P"
  "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle>"  ==  "((es,s), es',s') \<in> evals P"
(*<*)
  "P \<turnstile> \<langle>e,(h,l)\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle>" <= "((e,h,l), e',h',l') \<in> eval P"
  "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle>" <= "((e,s), e',h',l') \<in> eval P"
  "P \<turnstile> \<langle>e,(h,l)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" <= "((e,h,l), e',s') \<in> eval P"
  "P \<turnstile> \<langle>e,(h,l)\<rangle> [\<Rightarrow>] \<langle>e',(h',l')\<rangle>" <= "((e,h,l), e',h',l') \<in> evals P"
  "P \<turnstile> \<langle>e,s\<rangle> [\<Rightarrow>] \<langle>e',(h',l')\<rangle>" <= "((e,s), e',h',l') \<in> evals P"
  "P \<turnstile> \<langle>e,(h,l)\<rangle> [\<Rightarrow>] \<langle>e',s'\<rangle>" <= "((e,h,l), e',s') \<in> evals P"
(*>*)


inductive "eval P" "evals P"
intros

New:
  "\<lbrakk> new_Addr h = Some a; P \<turnstile> C has_fields FDTs; h' = h(a\<mapsto>(C,init_fields FDTs)) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>new C,(h,l)\<rangle> \<Rightarrow> \<langle>addr a,(h',l)\<rangle>"

NewFail:
  "new_Addr h = None \<Longrightarrow>
  P \<turnstile> \<langle>new C, (h,l)\<rangle> \<Rightarrow> \<langle>THROW OutOfMemory,(h,l)\<rangle>"

Cast:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,l)\<rangle>; h a = Some(D,fs); P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,l)\<rangle>"

CastNull:
  "P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle>"

CastFail:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^isub>0\<rangle>\<Rightarrow> \<langle>addr a,(h,l)\<rangle>; h a = Some(D,fs); \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>THROW ClassCast,(h,l)\<rangle>"

CastThrow:
  "P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"

Val:
  "P \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>Val v,s\<rangle>"

BinOp:
  "\<lbrakk> P \<turnstile> \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v\<^isub>1,s\<^isub>1\<rangle>; P \<turnstile> \<langle>e\<^isub>2,s\<^isub>1\<rangle> \<Rightarrow> \<langle>Val v\<^isub>2,s\<^isub>2\<rangle>; binop(bop,v\<^isub>1,v\<^isub>2) = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2,s\<^isub>0\<rangle>\<Rightarrow>\<langle>Val v,s\<^isub>2\<rangle>"

BinOpThrow1:
  "P \<turnstile> \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2, s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^isub>1\<rangle>"

BinOpThrow2:
  "\<lbrakk> P \<turnstile> \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v\<^isub>1,s\<^isub>1\<rangle>; P \<turnstile> \<langle>e\<^isub>2,s\<^isub>1\<rangle> \<Rightarrow> \<langle>throw e,s\<^isub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^isub>2\<rangle>"

Var:
  "l V = Some v \<Longrightarrow>
  P \<turnstile> \<langle>Var V,(h,l)\<rangle> \<Rightarrow> \<langle>Val v,(h,l)\<rangle>"

LAss:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,(h,l)\<rangle>; l' = l(V\<mapsto>v) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>V:=e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>unit,(h,l')\<rangle>"

LAssThrow:
  "P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>V:=e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"

FAcc:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,l)\<rangle>; h a = Some(C,fs); fs(F,D) = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>F{D},s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,(h,l)\<rangle>"

FAccNull:
  "P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<bullet>F{D},s\<^isub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^isub>1\<rangle>"

FAccThrow:
  "P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<bullet>F{D},s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"

FAss:
  "\<lbrakk> P \<turnstile> \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^isub>1\<rangle>; P \<turnstile> \<langle>e\<^isub>2,s\<^isub>1\<rangle> \<Rightarrow> \<langle>Val v,(h\<^isub>2,l\<^isub>2)\<rangle>;
     h\<^isub>2 a = Some(C,fs); fs' = fs((F,D)\<mapsto>v); h\<^isub>2' = h\<^isub>2(a\<mapsto>(C,fs')) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^isub>1\<bullet>F{D}:=e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>unit,(h\<^isub>2',l\<^isub>2)\<rangle>"

FAssNull:
  "\<lbrakk> P \<turnstile> \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle>;  P \<turnstile> \<langle>e\<^isub>2,s\<^isub>1\<rangle> \<Rightarrow> \<langle>Val v,s\<^isub>2\<rangle> \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>e\<^isub>1\<bullet>F{D}:=e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^isub>2\<rangle>"

FAssThrow1:
  "P \<turnstile> \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<^isub>1\<bullet>F{D}:=e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"

FAssThrow2:
  "\<lbrakk> P \<turnstile> \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^isub>1\<rangle>; P \<turnstile> \<langle>e\<^isub>2,s\<^isub>1\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^isub>1\<bullet>F{D}:=e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>2\<rangle>"

CallObjThrow:
  "P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<bullet>M(ps),s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"

CallParamsThrow:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^isub>1\<rangle>; P \<turnstile> \<langle>es,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs @ throw ex # es',s\<^isub>2\<rangle> \<rbrakk>
   \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(es),s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^isub>2\<rangle>"

CallNull:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle>;  P \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,s\<^isub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(ps),s\<^isub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^isub>2\<rangle>"

Call:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^isub>1\<rangle>;  P \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^isub>2,l\<^isub>2)\<rangle>;
     h\<^isub>2 a = Some(C,fs);  P \<turnstile> C sees M:Ts\<rightarrow>T = (pns,body) in D;
     length vs = length pns;  l\<^isub>2' = [this\<mapsto>Addr a, pns[\<mapsto>]vs];
     P \<turnstile> \<langle>body,(h\<^isub>2,l\<^isub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(ps),s\<^isub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>2)\<rangle>"

Block:
  "P \<turnstile> \<langle>e\<^isub>0,(h\<^isub>0,l\<^isub>0(V:=None))\<rangle> \<Rightarrow> \<langle>e\<^isub>1,(h\<^isub>1,l\<^isub>1)\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>{V:T; e\<^isub>0},(h\<^isub>0,l\<^isub>0)\<rangle> \<Rightarrow> \<langle>e\<^isub>1,(h\<^isub>1,l\<^isub>1(V:=l\<^isub>0 V))\<rangle>"

Seq:
  "\<lbrakk> P \<turnstile> \<langle>e\<^isub>0,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^isub>1\<rangle>; P \<turnstile> \<langle>e\<^isub>1,s\<^isub>1\<rangle> \<Rightarrow> \<langle>e\<^isub>2,s\<^isub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^isub>0;;e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>e\<^isub>2,s\<^isub>2\<rangle>"

SeqThrow:
  "P \<turnstile> \<langle>e\<^isub>0,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<^isub>0;;e\<^isub>1,s\<^isub>0\<rangle>\<Rightarrow>\<langle>throw e,s\<^isub>1\<rangle>"

CondT:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>true,s\<^isub>1\<rangle>; P \<turnstile> \<langle>e\<^isub>1,s\<^isub>1\<rangle> \<Rightarrow> \<langle>e',s\<^isub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>if (e) e\<^isub>1 else e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>e',s\<^isub>2\<rangle>"

CondF:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>false,s\<^isub>1\<rangle>; P \<turnstile> \<langle>e\<^isub>2,s\<^isub>1\<rangle> \<Rightarrow> \<langle>e',s\<^isub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>if (e) e\<^isub>1 else e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>e',s\<^isub>2\<rangle>"

CondThrow:
  "P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>if (e) e\<^isub>1 else e\<^isub>2, s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"

WhileF:
  "P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>false,s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>while (e) c,s\<^isub>0\<rangle> \<Rightarrow> \<langle>unit,s\<^isub>1\<rangle>"

WhileT:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>true,s\<^isub>1\<rangle>; P \<turnstile> \<langle>c,s\<^isub>1\<rangle> \<Rightarrow> \<langle>Val v\<^isub>1,s\<^isub>2\<rangle>; P \<turnstile> \<langle>while (e) c,s\<^isub>2\<rangle> \<Rightarrow> \<langle>e\<^isub>3,s\<^isub>3\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>while (e) c,s\<^isub>0\<rangle> \<Rightarrow> \<langle>e\<^isub>3,s\<^isub>3\<rangle>"

WhileCondThrow:
  "P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle> throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>while (e) c,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"

WhileBodyThrow:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>true,s\<^isub>1\<rangle>; P \<turnstile> \<langle>c,s\<^isub>1\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>2\<rangle>\<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>while (e) c,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>2\<rangle>"

Throw:
  "P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>throw e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Throw a,s\<^isub>1\<rangle>"

ThrowNull:
  "P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>throw e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^isub>1\<rangle>"

ThrowThrow:
  "P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>throw e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"

Try:
  "P \<turnstile> \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v\<^isub>1,s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>try e\<^isub>1 catch(C V) e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v\<^isub>1,s\<^isub>1\<rangle>"

TryCatch:
  "\<lbrakk> P \<turnstile> \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Throw a,(h\<^isub>1,l\<^isub>1)\<rangle>;  h\<^isub>1 a = Some(D,fs);  P \<turnstile> D \<preceq>\<^sup>* C;
     P \<turnstile> \<langle>e\<^isub>2,(h\<^isub>1,l\<^isub>1(V\<mapsto>Addr a))\<rangle> \<Rightarrow> \<langle>e\<^isub>2',(h\<^isub>2,l\<^isub>2)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>try e\<^isub>1 catch(C V) e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>e\<^isub>2',(h\<^isub>2,l\<^isub>2(V:=l\<^isub>1 V))\<rangle>"

TryThrow:
  "\<lbrakk> P \<turnstile> \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Throw a,(h\<^isub>1,l\<^isub>1)\<rangle>;  h\<^isub>1 a = Some(D,fs);  \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>try e\<^isub>1 catch(C V) e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Throw a,(h\<^isub>1,l\<^isub>1)\<rangle>"

Nil:
  "P \<turnstile> \<langle>[],s\<rangle> [\<Rightarrow>] \<langle>[],s\<rangle>"

Cons:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^isub>1\<rangle>; P \<turnstile> \<langle>es,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>es',s\<^isub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e#es,s\<^isub>0\<rangle> [\<Rightarrow>] \<langle>Val v # es',s\<^isub>2\<rangle>"

ConsThrow:
  "P \<turnstile> \<langle>e, s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e', s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e#es, s\<^isub>0\<rangle> [\<Rightarrow>] \<langle>throw e' # es, s\<^isub>1\<rangle>"

(*<*)
lemmas eval_evals_induct = eval_evals.induct [split_format (complete)]
  and eval_evals_inducts = eval_evals.inducts [split_format (complete)]

inductive_cases eval_cases [cases set]:
 "P \<turnstile> \<langle>Cast C e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>V:=e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>e\<bullet>F{D},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>e\<^isub>1\<bullet>F{D}:=e\<^isub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>e\<bullet>M{D}(es),s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>{V:T;e\<^isub>1},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>e\<^isub>1;;e\<^isub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>if (e) e\<^isub>1 else e\<^isub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>while (b) c,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>throw e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>try e\<^isub>1 catch(C V) e\<^isub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 
inductive_cases evals_cases [cases set]:
 "P \<turnstile> \<langle>[],s\<rangle> [\<Rightarrow>] \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>e#es,s\<rangle> [\<Rightarrow>] \<langle>e',s'\<rangle>"
(*>*) 


subsection"Final expressions"

constdefs
  final :: "'a exp \<Rightarrow> bool"
  "final e  \<equiv>  (\<exists>v. e = Val v) \<or> (\<exists>a. e = Throw a)"
  finals:: "'a exp list \<Rightarrow> bool"
  "finals es  \<equiv>  (\<exists>vs. es = map Val vs) \<or> (\<exists>vs a es'. es = map Val vs @ Throw a # es')"

lemma [simp]: "final(Val v)"
(*<*)by(simp add:final_def)(*>*)

lemma [simp]: "final(throw e) = (\<exists>a. e = addr a)"
(*<*)by(simp add:final_def)(*>*)

lemma finalE: "\<lbrakk> final e;  \<And>v. e = Val v \<Longrightarrow> R;  \<And>a. e = Throw a \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
(*<*)by(auto simp:final_def)(*>*)

lemma [iff]: "finals []"
(*<*)by(simp add:finals_def)(*>*)

lemma [iff]: "finals (Val v # es) = finals es"
(*<*)
apply(clarsimp simp add: finals_def)
apply(rule iffI)
 apply(erule disjE)
  apply simp
 apply(rule disjI2)
 apply clarsimp
 apply(case_tac vs)
  apply simp
 apply fastsimp
apply(erule disjE)
 apply clarsimp
apply(rule disjI2)
apply clarsimp
apply(rule_tac x = "v#vs" in exI)
apply simp
done
(*>*)

lemma finals_app_map[iff]: "finals (map Val vs @ es) = finals es"
(*<*)by(induct_tac vs, auto)(*>*)

lemma [iff]: "finals (map Val vs)"
(*<*)using finals_app_map[of vs "[]"]by(simp)(*>*)

lemma [iff]: "finals (throw e # es) = (\<exists>a. e = addr a)"
(*<*)
apply(simp add:finals_def)
apply(rule iffI)
 apply clarsimp
 apply(case_tac vs)
  apply simp
 apply fastsimp
apply clarsimp
apply(rule_tac x = "[]" in exI)
apply simp
done
(*>*)

lemma not_finals_ConsI: "\<not> final e \<Longrightarrow> \<not> finals(e#es)"
 (*<*)
apply(clarsimp simp add:finals_def final_def)
apply(case_tac vs)
apply auto
done
(*>*)


lemma eval_final: "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> final e'"
 and evals_final: "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> finals es'"
(*<*)by(induct rule:eval_evals.inducts, simp_all)(*>*)


lemma eval_lcl_incr: "P \<turnstile> \<langle>e,(h\<^isub>0,l\<^isub>0)\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>1,l\<^isub>1)\<rangle> \<Longrightarrow> dom l\<^isub>0 \<subseteq> dom l\<^isub>1"
 and evals_lcl_incr: "P \<turnstile> \<langle>es,(h\<^isub>0,l\<^isub>0)\<rangle> [\<Rightarrow>] \<langle>es',(h\<^isub>1,l\<^isub>1)\<rangle> \<Longrightarrow> dom l\<^isub>0 \<subseteq> dom l\<^isub>1"
(*<*)
proof (induct rule: eval_evals_inducts)
  case BinOp show ?case by(rule subset_trans)
next
  case Call thus ?case
    by(simp del: fun_upd_apply) 
next
  case Seq show ?case by(rule subset_trans)
next
  case CondT show ?case by(rule subset_trans)
next
  case CondF show ?case by(rule subset_trans)
next
  case WhileT thus ?case by(blast)
next
  case TryCatch thus ?case by(clarsimp simp:dom_def split:split_if_asm) blast
next
  case Cons show ?case by(rule subset_trans)
next
  case Block thus ?case by(auto simp del:fun_upd_apply)
qed auto
(*>*)

text{* Only used later, in the small to big translation, but is already a
good sanity check: *}

lemma eval_finalId:  "final e \<Longrightarrow> P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e,s\<rangle>"
(*<*)by (erule finalE) (iprover intro: eval_evals.intros)+(*>*)


lemma eval_finalsId:
assumes finals: "finals es" shows "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es,s\<rangle>"
(*<*)
  using finals
proof (induct es type: list)
  case Nil show ?case by (rule eval_evals.intros)
next
  case (Cons e es)
  have hyp: "finals es \<Longrightarrow> P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es,s\<rangle>"
   and finals: "finals (e # es)".
  show "P \<turnstile> \<langle>e # es,s\<rangle> [\<Rightarrow>] \<langle>e # es,s\<rangle>"
  proof cases
    assume "final e"
    thus ?thesis
    proof (cases rule: finalE)
      fix v assume e: "e = Val v"
      have "P \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>Val v,s\<rangle>" by (simp add: eval_finalId)
      moreover from finals e have "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es,s\<rangle>" by(fast intro:hyp)
      ultimately have "P \<turnstile> \<langle>Val v#es,s\<rangle> [\<Rightarrow>] \<langle>Val v#es,s\<rangle>"
	by (rule eval_evals.intros)
      with e show ?thesis by simp
    next
      fix a assume e: "e = Throw a"
      have "P \<turnstile> \<langle>Throw a,s\<rangle> \<Rightarrow> \<langle>Throw a,s\<rangle>" by (simp add: eval_finalId)
      hence "P \<turnstile> \<langle>Throw a#es,s\<rangle> [\<Rightarrow>] \<langle>Throw a#es,s\<rangle>" by (rule eval_evals.intros)
      with e show ?thesis by simp
    qed
  next
    assume "\<not> final e"
    with not_finals_ConsI finals have False by blast
    thus ?thesis ..
  qed
qed
(*>*)


theorem eval_hext: "P \<turnstile> \<langle>e,(h,l)\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> h \<unlhd> h'"
and evals_hext:  "P \<turnstile> \<langle>es,(h,l)\<rangle> [\<Rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> h \<unlhd> h'"
(*<*)
proof (induct rule: eval_evals_inducts)
  case New thus ?case
    by(fastsimp intro!: hext_new intro:someI simp:new_Addr_def
                split:split_if_asm simp del:fun_upd_apply)
next
  case BinOp thus ?case by (fast elim!:hext_trans)
next
  case BinOpThrow2 thus ?case by(fast elim!: hext_trans)
next
  case FAss thus ?case
    by(auto simp:sym[THEN hext_upd_obj] simp del:fun_upd_apply
            elim!: hext_trans)
next
  case FAssNull thus ?case by (fast elim!:hext_trans)
next
  case FAssThrow2 thus ?case by (fast elim!:hext_trans)
next
  case CallParamsThrow thus ?case by(fast elim!: hext_trans)
next
  case CallNull thus ?case by(fast elim!: hext_trans)
next
  case Call thus ?case by(fast elim!: hext_trans)
next
  case Seq thus ?case by(fast elim!: hext_trans)
next
  case CondT thus ?case by(fast elim!: hext_trans)
next
  case CondF thus ?case by(fast elim!: hext_trans)
next
  case WhileT thus ?case by(fast elim!: hext_trans)
next
  case WhileBodyThrow thus ?case by (fast elim!: hext_trans)
next
  case TryCatch thus ?case  by(fast elim!: hext_trans)
next
  case Cons thus ?case by (fast intro: hext_trans)
qed auto
(*>*)


end
