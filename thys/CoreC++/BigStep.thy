(*  Title:       CoreC++
    ID:          $Id: BigStep.thy,v 1.12 2006-08-03 14:54:46 wasserra Exp $
    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

    Based on the Jinja theory J/BigStep.thy by Tobias Nipkow
*)


header {* Big Step Semantics *}

theory BigStep imports Syntax State begin

subsection {* The rules *}

consts
  eval  :: "prog \<Rightarrow> (env \<times> (expr \<times> state) \<times> (expr \<times> state)) set"
  evals  :: "prog \<Rightarrow> (env \<times> (expr list \<times> state) \<times> (expr list \<times> state)) set"


syntax (xsymbols)
  eval :: "prog \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> bool"
          ("_,_ \<turnstile> ((1\<langle>_,/_\<rangle>) \<Rightarrow>/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  evals :: "prog \<Rightarrow> env \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> bool"
           ("_,_ \<turnstile> ((1\<langle>_,/_\<rangle>) [\<Rightarrow>]/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)


translations
  "P,E \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"  ==  "(E,(e,s), e',s') \<in> eval P"
  "P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle>"  ==  "(E,(es,s), es',s') \<in> evals P"

  "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle>" <= "(E,(e,h,l), e',h',l') \<in> eval P"
  "P,E \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle>" <= "(E,(e,s), e',h',l') \<in> eval P"
  "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" <= "(E,(e,h,l), e',s') \<in> eval P"
  "P,E \<turnstile> \<langle>e,(h,l)\<rangle> [\<Rightarrow>] \<langle>e',(h',l')\<rangle>" <= "(E,(e,h,l), e',h',l') \<in> evals P"
  "P,E \<turnstile> \<langle>e,s\<rangle> [\<Rightarrow>] \<langle>e',(h',l')\<rangle>" <= "(E,(e,s), e',h',l') \<in> evals P"
  "P,E \<turnstile> \<langle>e,(h,l)\<rangle> [\<Rightarrow>] \<langle>e',s'\<rangle>" <= "(E,(e,h,l), e',s') \<in> evals P"



inductive "eval P" "evals P"
intros

New:
  "\<lbrakk> new_Addr h = Some a; h' = h(a\<mapsto>(C,init_obj P C)) \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>new C,(h,l)\<rangle> \<Rightarrow> \<langle>ref (a,[C]),(h',l)\<rangle>"

NewFail:
  "new_Addr h = None \<Longrightarrow>
  P,E \<turnstile> \<langle>new C, (h,l)\<rangle> \<Rightarrow> \<langle>THROW OutOfMemory,(h,l)\<rangle>"

StaticUpCast:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),s\<^isub>1\<rangle>; P \<turnstile> Path last Cs to C via Cs'; Ds = Cs@\<^sub>pCs' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Ds),s\<^isub>1\<rangle>"

StaticDownCast:
  "P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs@[C]@Cs'),s\<^isub>1\<rangle>
   \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs@[C]),s\<^isub>1\<rangle>"

StaticCastNull:
  "P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle>"

StaticCastFail:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),s\<^isub>1\<rangle>; \<not> P \<turnstile> (last Cs) \<preceq>\<^sup>* C; C \<notin> set Cs \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>THROW ClassCast,s\<^isub>1\<rangle>"

StaticCastThrow:
  "P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"

StaticUpDynCast:(* path uniqueness not necessary for type proof but for determinism *)
  "\<lbrakk>P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref(a,Cs),s\<^isub>1\<rangle>; P \<turnstile> Path last Cs to C unique;
    P \<turnstile> Path last Cs to C via Cs'; Ds = Cs@\<^sub>pCs' \<rbrakk>
\<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref(a,Ds),s\<^isub>1\<rangle>"

StaticDownDynCast:
  "P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs@[C]@Cs'),s\<^isub>1\<rangle>
   \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs@[C]),s\<^isub>1\<rangle>"

DynCast: (* path uniqueness not necessary for type proof but for determinism *)
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),(h,l)\<rangle>; h a = Some(D,S);
    P \<turnstile> Path D to C via Cs'; P \<turnstile> Path D to C unique \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs'),(h,l)\<rangle>"

DynCastNull:
  "P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle>"

DynCastFail: (* forth premise not necessary for type proof but for determinism *)
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle>\<Rightarrow> \<langle>ref (a,Cs),(h,l)\<rangle>; h a = Some(D,S); \<not> P \<turnstile> Path D to C unique;
    \<not> P \<turnstile> Path last Cs to C unique; C \<notin> set Cs \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,(h,l)\<rangle>"

DynCastThrow:
  "P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"

Val:
  "P,E \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>Val v,s\<rangle>"

BinOp:
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v\<^isub>1,s\<^isub>1\<rangle>; P,E \<turnstile> \<langle>e\<^isub>2,s\<^isub>1\<rangle> \<Rightarrow> \<langle>Val v\<^isub>2,s\<^isub>2\<rangle>; 
    binop(bop,v\<^isub>1,v\<^isub>2) = Some v \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2,s\<^isub>0\<rangle>\<Rightarrow>\<langle>Val v,s\<^isub>2\<rangle>"

BinOpThrow1:
  "P,E \<turnstile> \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^isub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2, s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^isub>1\<rangle>"

BinOpThrow2:
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v\<^isub>1,s\<^isub>1\<rangle>; P,E \<turnstile> \<langle>e\<^isub>2,s\<^isub>1\<rangle> \<Rightarrow> \<langle>throw e,s\<^isub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^isub>2\<rangle>"

Var:
  "l V = Some v \<Longrightarrow>
  P,E \<turnstile> \<langle>Var V,(h,l)\<rangle> \<Rightarrow> \<langle>Val v,(h,l)\<rangle>"

LAss:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,(h,l)\<rangle>; E V = Some T;
     P \<turnstile> T casts v to v'; l' = l(V\<mapsto>v') \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>V:=e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v',(h,l')\<rangle>"

LAssThrow:
  "P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>V:=e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"

FAcc:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs'),(h,l)\<rangle>; h a = Some(D,S);
     Ds = Cs'@\<^sub>pCs; (Ds,fs) \<in> S; fs F = Some v \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>F{Cs},s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,(h,l)\<rangle>"

FAccNull:
  "P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<bullet>F{Cs},s\<^isub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^isub>1\<rangle>" 

FAccThrow:
  "P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<bullet>F{Cs},s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"

FAss:
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs'),s\<^isub>1\<rangle>; P,E \<turnstile> \<langle>e\<^isub>2,s\<^isub>1\<rangle> \<Rightarrow> \<langle>Val v,(h\<^isub>2,l\<^isub>2)\<rangle>;
     h\<^isub>2 a = Some(D,S); P \<turnstile> (last Cs') has least F:T via Cs; P \<turnstile> T casts v to v';
     Ds = Cs'@\<^sub>pCs; (Ds,fs) \<in> S; fs' = fs(F\<mapsto>v'); 
     S' = S - {(Ds,fs)} \<union> {(Ds,fs')}; h\<^isub>2' = h\<^isub>2(a\<mapsto>(D,S'))\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<^isub>1\<bullet>F{Cs}:=e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v',(h\<^isub>2',l\<^isub>2)\<rangle>"

FAssNull:
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle>;  P,E \<turnstile> \<langle>e\<^isub>2,s\<^isub>1\<rangle> \<Rightarrow> \<langle>Val v,s\<^isub>2\<rangle> \<rbrakk> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<^isub>1\<bullet>F{Cs}:=e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^isub>2\<rangle>" 

FAssThrow1:
  "P,E \<turnstile> \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<^isub>1\<bullet>F{Cs}:=e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"

FAssThrow2:
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^isub>1\<rangle>; P,E \<turnstile> \<langle>e\<^isub>2,s\<^isub>1\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<^isub>1\<bullet>F{Cs}:=e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>2\<rangle>"

CallObjThrow:
  "P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<bullet>M(ps),s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"

CallParamsThrow:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^isub>1\<rangle>; P,E \<turnstile> \<langle>es,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs @ throw ex # es',s\<^isub>2\<rangle> \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>M(es),s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^isub>2\<rangle>"

Call:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),s\<^isub>1\<rangle>;  P,E \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^isub>2,l\<^isub>2)\<rangle>;
     h\<^isub>2 a = Some(C,S);  P \<turnstile> last Cs has least M = (Ts',T',pns',body') via Ds;
     P \<turnstile> (C,Cs@\<^sub>pDs) selects M = (Ts,T,pns,body) via Cs'; length vs = length pns; 
     P \<turnstile> Ts Casts vs to vs'; l\<^isub>2' = [this\<mapsto>Ref (a,Cs'), pns[\<mapsto>]vs'];
     new_body = (case T' of Class D \<Rightarrow> \<lparr>D\<rparr>body   | _  \<Rightarrow> body);  
     P,E(this\<mapsto>Class(last Cs'), pns[\<mapsto>]Ts) \<turnstile> \<langle>new_body,(h\<^isub>2,l\<^isub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>M(ps),s\<^isub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>2)\<rangle>"

CallNull:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle>;  P,E \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,s\<^isub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>M(ps),s\<^isub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^isub>2\<rangle>"

Block:
  "\<lbrakk>P,E(V \<mapsto> T) \<turnstile> \<langle>e\<^isub>0,(h\<^isub>0,l\<^isub>0(V:=None))\<rangle> \<Rightarrow> \<langle>e\<^isub>1,(h\<^isub>1,l\<^isub>1)\<rangle> \<rbrakk> \<Longrightarrow>
  P,E \<turnstile> \<langle>{V:T; e\<^isub>0},(h\<^isub>0,l\<^isub>0)\<rangle> \<Rightarrow> \<langle>e\<^isub>1,(h\<^isub>1,l\<^isub>1(V:=l\<^isub>0 V))\<rangle>"

Seq:
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^isub>0,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^isub>1\<rangle>; P,E \<turnstile> \<langle>e\<^isub>1,s\<^isub>1\<rangle> \<Rightarrow> \<langle>e\<^isub>2,s\<^isub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<^isub>0;;e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>e\<^isub>2,s\<^isub>2\<rangle>"

SeqThrow:
  "P,E \<turnstile> \<langle>e\<^isub>0,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^isub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<^isub>0;;e\<^isub>1,s\<^isub>0\<rangle>\<Rightarrow>\<langle>throw e,s\<^isub>1\<rangle>"

CondT:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>true,s\<^isub>1\<rangle>; P,E \<turnstile> \<langle>e\<^isub>1,s\<^isub>1\<rangle> \<Rightarrow> \<langle>e',s\<^isub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>if (e) e\<^isub>1 else e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>e',s\<^isub>2\<rangle>"

CondF:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>false,s\<^isub>1\<rangle>; P,E \<turnstile> \<langle>e\<^isub>2,s\<^isub>1\<rangle> \<Rightarrow> \<langle>e',s\<^isub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>if (e) e\<^isub>1 else e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>e',s\<^isub>2\<rangle>"

CondThrow:
  "P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>if (e) e\<^isub>1 else e\<^isub>2, s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"

WhileF:
  "P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>false,s\<^isub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>while (e) c,s\<^isub>0\<rangle> \<Rightarrow> \<langle>unit,s\<^isub>1\<rangle>"

WhileT:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>true,s\<^isub>1\<rangle>; P,E \<turnstile> \<langle>c,s\<^isub>1\<rangle> \<Rightarrow> \<langle>Val v\<^isub>1,s\<^isub>2\<rangle>; 
     P,E \<turnstile> \<langle>while (e) c,s\<^isub>2\<rangle> \<Rightarrow> \<langle>e\<^isub>3,s\<^isub>3\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>while (e) c,s\<^isub>0\<rangle> \<Rightarrow> \<langle>e\<^isub>3,s\<^isub>3\<rangle>"

WhileCondThrow:
  "P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle> throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>while (e) c,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"

WhileBodyThrow:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>true,s\<^isub>1\<rangle>; P,E \<turnstile> \<langle>c,s\<^isub>1\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>2\<rangle>\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>while (e) c,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>2\<rangle>"

Throw:
  "P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref r,s\<^isub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>throw e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Throw r,s\<^isub>1\<rangle>"

ThrowNull:
  "P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>throw e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^isub>1\<rangle>"

ThrowThrow:
  "P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>throw e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"

Nil:
  "P,E \<turnstile> \<langle>[],s\<rangle> [\<Rightarrow>] \<langle>[],s\<rangle>"

Cons:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^isub>1\<rangle>; P,E \<turnstile> \<langle>es,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>es',s\<^isub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e#es,s\<^isub>0\<rangle> [\<Rightarrow>] \<langle>Val v # es',s\<^isub>2\<rangle>"

ConsThrow:
  "P,E \<turnstile> \<langle>e, s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e', s\<^isub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e#es, s\<^isub>0\<rangle> [\<Rightarrow>] \<langle>throw e' # es, s\<^isub>1\<rangle>"

lemmas eval_evals_induct = eval_evals.induct [split_format (complete)]
  and eval_evals_inducts = eval_evals.inducts [split_format (complete)]

inductive_cases eval_cases [cases set]:
 "P,E \<turnstile> \<langle>new C,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>Cast C e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>Var V,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>V:=e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>e\<bullet>F{Cs},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>e\<^isub>1\<bullet>F{Cs}:=e\<^isub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>e\<bullet>M(es),s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>{V:T;e\<^isub>1},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>e\<^isub>1;;e\<^isub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>if (e) e\<^isub>1 else e\<^isub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>while (b) c,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>throw e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
  
inductive_cases evals_cases [cases set]:
 "P,E \<turnstile> \<langle>[],s\<rangle> [\<Rightarrow>] \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>e#es,s\<rangle> [\<Rightarrow>] \<langle>e',s'\<rangle>"



subsection"Final expressions"

constdefs
  final :: "expr \<Rightarrow> bool"
  "final e  \<equiv>  (\<exists>v. e = Val v) \<or> (\<exists>r. e = Throw r)"
  finals:: "expr list \<Rightarrow> bool"
  "finals es  \<equiv>  (\<exists>vs. es = map Val vs) \<or> (\<exists>vs r es'. es = map Val vs @ Throw r # es')"

lemma [simp]: "final(Val v)"
by(simp add:final_def)

lemma [simp]: "final(throw e) = (\<exists>r. e = ref r)"
by(simp add:final_def)

lemma finalE: "\<lbrakk> final e;  \<And>v. e = Val v \<Longrightarrow> Q;  \<And>r. e = Throw r \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by(auto simp:final_def)

lemma [iff]: "finals []"
by(simp add:finals_def)

lemma [iff]: "finals (Val v # es) = finals es"

apply(clarsimp simp add:finals_def)
apply(rule iffI)
 apply(erule disjE)
  apply simp
 apply(rule disjI2)
 apply clarsimp
 apply(case_tac vs)
  apply simp
 apply fastsimp
apply(erule disjE)
 apply (rule disjI1)
 apply clarsimp
apply(rule disjI2)
apply clarsimp
apply(rule_tac x = "v#vs" in exI)
apply simp
done


lemma finals_app_map[iff]: "finals (map Val vs @ es) = finals es"
by(induct_tac vs, auto)

lemma [iff]: "finals (map Val vs)"
using finals_app_map[of vs "[]"]by(simp)

lemma [iff]: "finals (throw e # es) = (\<exists>r. e = ref r)"

apply(simp add:finals_def)
apply(rule iffI)
 apply clarsimp
 apply(case_tac vs)
  apply simp
 apply fastsimp
apply fastsimp
done


lemma not_finals_ConsI: "\<not> final e \<Longrightarrow> \<not> finals(e#es)"
 
apply(auto simp add:finals_def final_def)
apply(case_tac vs)
apply auto
done


lemma eval_final: "P,E \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> final e'"
 and evals_final: "P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> finals es'"
by(induct rule:eval_evals.inducts, simp_all)


lemma eval_lcl_incr: "P,E \<turnstile> \<langle>e,(h\<^isub>0,l\<^isub>0)\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>1,l\<^isub>1)\<rangle> \<Longrightarrow> dom l\<^isub>0 \<subseteq> dom l\<^isub>1"
 and evals_lcl_incr: "P,E \<turnstile> \<langle>es,(h\<^isub>0,l\<^isub>0)\<rangle> [\<Rightarrow>] \<langle>es',(h\<^isub>1,l\<^isub>1)\<rangle> \<Longrightarrow> dom l\<^isub>0 \<subseteq> dom l\<^isub>1"
by (induct rule:eval_evals_inducts) (auto simp del:fun_upd_apply)


text{* Only used later, in the small to big translation, but is already a
good sanity check: *}

lemma eval_finalId:  "final e \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e,s\<rangle>"
by (erule finalE) (fastsimp intro: eval_evals.intros)+


lemma eval_finalsId:
assumes finals: "finals es" shows "P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es,s\<rangle>"

  using finals
proof (induct es type: list)
  case Nil show ?case by (rule eval_evals.intros)
next
  case (Cons e es)
  have hyp: "finals es \<Longrightarrow> P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es,s\<rangle>"
   and finals: "finals (e # es)".
  show "P,E \<turnstile> \<langle>e # es,s\<rangle> [\<Rightarrow>] \<langle>e # es,s\<rangle>"
  proof cases
    assume "final e"
    thus ?thesis
    proof (cases rule: finalE)
      fix v assume e: "e = Val v"
      have "P,E \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>Val v,s\<rangle>" by (simp add: eval_finalId)
      moreover from finals e have "P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es,s\<rangle>" by(fast intro:hyp)
      ultimately have "P,E \<turnstile> \<langle>Val v#es,s\<rangle> [\<Rightarrow>] \<langle>Val v#es,s\<rangle>"
	by (rule eval_evals.intros)
      with e show ?thesis by simp
    next
      fix a assume e: "e = Throw a"
      have "P,E \<turnstile> \<langle>Throw a,s\<rangle> \<Rightarrow> \<langle>Throw a,s\<rangle>" by (simp add: eval_finalId)
      hence "P,E \<turnstile> \<langle>Throw a#es,s\<rangle> [\<Rightarrow>] \<langle>Throw a#es,s\<rangle>" by (rule eval_evals.intros)
      with e show ?thesis by simp
    qed
  next
    assume "\<not> final e"
    with not_finals_ConsI finals have False by blast
    thus ?thesis ..
  qed
qed


lemma
eval_preserves_obj:"P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> (\<And>S. h a = Some(D,S) 
  \<Longrightarrow> \<exists>S'. h' a = Some(D,S'))"
and evals_preserves_obj:"P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<Rightarrow>] \<langle>es',(h',l')\<rangle> 
\<Longrightarrow> (\<And>S. h a = Some(D,S) \<Longrightarrow> \<exists>S'. h' a = Some(D,S'))"
by(induct rule:eval_evals_inducts)(fastsimp dest:new_Addr_SomeD)+

end
