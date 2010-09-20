(*  Title:      Jinja/Compiler/J1.thy
    Author:     Tobias Nipkow
    Copyright   2003 Technische Universitaet Muenchen
*)

header {* \chapter{Compilation}\label{cha:comp}
          \isaheader{An Intermediate Language} *}

theory J1 imports "../J/BigStep" begin

types
  expr\<^isub>1 = "nat exp"
  J\<^isub>1_prog = "expr\<^isub>1 prog"

  state\<^isub>1 = "heap \<times> (val list)"

primrec
  max_vars :: "'a exp \<Rightarrow> nat"
  and max_varss :: "'a exp list \<Rightarrow> nat"
where
  "max_vars(new C) = 0"
| "max_vars(Cast C e) = max_vars e"
| "max_vars(Val v) = 0"
| "max_vars(e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2) = max (max_vars e\<^isub>1) (max_vars e\<^isub>2)"
| "max_vars(Var V) = 0"
| "max_vars(V:=e) = max_vars e"
| "max_vars(e\<bullet>F{D}) = max_vars e"
| "max_vars(FAss e\<^isub>1 F D e\<^isub>2) = max (max_vars e\<^isub>1) (max_vars e\<^isub>2)"
| "max_vars(e\<bullet>M(es)) = max (max_vars e) (max_varss es)"
| "max_vars({V:T; e}) = max_vars e + 1"
| "max_vars(e\<^isub>1;;e\<^isub>2) = max (max_vars e\<^isub>1) (max_vars e\<^isub>2)"
| "max_vars(if (e) e\<^isub>1 else e\<^isub>2) =
   max (max_vars e) (max (max_vars e\<^isub>1) (max_vars e\<^isub>2))"
| "max_vars(while (b) e) = max (max_vars b) (max_vars e)"
| "max_vars(throw e) = max_vars e"
| "max_vars(try e\<^isub>1 catch(C V) e\<^isub>2) = max (max_vars e\<^isub>1) (max_vars e\<^isub>2 + 1)"

| "max_varss [] = 0"
| "max_varss (e#es) = max (max_vars e) (max_varss es)"

inductive
  eval\<^isub>1 :: "J\<^isub>1_prog \<Rightarrow> expr\<^isub>1 \<Rightarrow> state\<^isub>1 \<Rightarrow> expr\<^isub>1 \<Rightarrow> state\<^isub>1 \<Rightarrow> bool"
          ("_ \<turnstile>\<^sub>1 ((1\<langle>_,/_\<rangle>) \<Rightarrow>/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  and evals\<^isub>1 :: "J\<^isub>1_prog \<Rightarrow> expr\<^isub>1 list \<Rightarrow> state\<^isub>1 \<Rightarrow> expr\<^isub>1 list \<Rightarrow> state\<^isub>1 \<Rightarrow> bool"
           ("_ \<turnstile>\<^sub>1 ((1\<langle>_,/_\<rangle>) [\<Rightarrow>]/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  for P :: J\<^isub>1_prog
where

  New\<^isub>1:
  "\<lbrakk> new_Addr h = Some a; P \<turnstile> C has_fields FDTs; h' = h(a\<mapsto>(C,init_fields FDTs)) \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>new C,(h,l)\<rangle> \<Rightarrow> \<langle>addr a,(h',l)\<rangle>"
| NewFail\<^isub>1:
  "new_Addr h = None \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>new C, (h,l)\<rangle> \<Rightarrow> \<langle>THROW OutOfMemory,(h,l)\<rangle>"

| Cast\<^isub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,l)\<rangle>; h a = Some(D,fs); P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,l)\<rangle>"
| CastNull\<^isub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle>"
| CastFail\<^isub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,l)\<rangle>; h a = Some(D,fs); \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>THROW ClassCast,(h,l)\<rangle>"
| CastThrow\<^isub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"

| Val\<^isub>1:
  "P \<turnstile>\<^sub>1 \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>Val v,s\<rangle>"

| BinOp\<^isub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v\<^isub>1,s\<^isub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^isub>2,s\<^isub>1\<rangle> \<Rightarrow> \<langle>Val v\<^isub>2,s\<^isub>2\<rangle>; binop(bop,v\<^isub>1,v\<^isub>2) = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^isub>2\<rangle>"
| BinOpThrow\<^isub>1\<^isub>1:
  "P \<turnstile>\<^sub>1 \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2, s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^isub>1\<rangle>"
| BinOpThrow\<^isub>2\<^isub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v\<^isub>1,s\<^isub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^isub>2,s\<^isub>1\<rangle> \<Rightarrow> \<langle>throw e,s\<^isub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^isub>2\<rangle>"

| Var\<^isub>1:
  "\<lbrakk> ls!i = v; i < size ls \<rbrakk> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>Var i,(h,ls)\<rangle> \<Rightarrow> \<langle>Val v,(h,ls)\<rangle>"

| LAss\<^isub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,(h,ls)\<rangle>; i < size ls; ls' = ls[i := v] \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>i:= e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>unit,(h,ls')\<rangle>"
| LAssThrow\<^isub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>i:= e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"

| FAcc\<^isub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,ls)\<rangle>; h a = Some(C,fs); fs(F,D) = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<bullet>F{D},s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,(h,ls)\<rangle>"
| FAccNull\<^isub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>e\<bullet>F{D},s\<^isub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^isub>1\<rangle>"
| FAccThrow\<^isub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>e\<bullet>F{D},s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"

| FAss\<^isub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^isub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^isub>2,s\<^isub>1\<rangle> \<Rightarrow> \<langle>Val v,(h\<^isub>2,l\<^isub>2)\<rangle>;
    h\<^isub>2 a = Some(C,fs); fs' = fs((F,D)\<mapsto>v); h\<^isub>2' = h\<^isub>2(a\<mapsto>(C,fs')) \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<^isub>1\<bullet>F{D}:= e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>unit,(h\<^isub>2',l\<^isub>2)\<rangle>"
| FAssNull\<^isub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle>;  P \<turnstile>\<^sub>1 \<langle>e\<^isub>2,s\<^isub>1\<rangle> \<Rightarrow> \<langle>Val v,s\<^isub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<^isub>1\<bullet>F{D}:= e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^isub>2\<rangle>"
| FAssThrow\<^isub>1\<^isub>1:
  "P \<turnstile>\<^sub>1 \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>e\<^isub>1\<bullet>F{D}:= e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"
| FAssThrow\<^isub>2\<^isub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^isub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^isub>2,s\<^isub>1\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<^isub>1\<bullet>F{D}:= e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>2\<rangle>"

| CallObjThrow\<^isub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>e\<bullet>M(es),s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"
| CallNull\<^isub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>es,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,s\<^isub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<bullet>M(es),s\<^isub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^isub>2\<rangle>"
| Call\<^isub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^isub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>es,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^isub>2,ls\<^isub>2)\<rangle>;
    h\<^isub>2 a = Some(C,fs); P \<turnstile> C sees M:Ts\<rightarrow>T = body in D;
    size vs = size Ts; ls\<^isub>2' = (Addr a) # vs @ replicate (max_vars body) undefined;
    P \<turnstile>\<^sub>1 \<langle>body,(h\<^isub>2,ls\<^isub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,ls\<^isub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<bullet>M(es),s\<^isub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,ls\<^isub>2)\<rangle>"
| CallParamsThrow\<^isub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^isub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>es,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>es',s\<^isub>2\<rangle>;
     es' = map Val vs @ throw ex # es\<^isub>2 \<rbrakk>
   \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<bullet>M(es),s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^isub>2\<rangle>"

| Block\<^isub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>e',s\<^isub>1\<rangle> \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>Block i T e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>e',s\<^isub>1\<rangle>"

| Seq\<^isub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^isub>0,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^isub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^isub>1,s\<^isub>1\<rangle> \<Rightarrow> \<langle>e\<^isub>2,s\<^isub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<^isub>0;;e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>e\<^isub>2,s\<^isub>2\<rangle>"
| SeqThrow\<^isub>1:
  "P \<turnstile>\<^sub>1 \<langle>e\<^isub>0,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>e\<^isub>0;;e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^isub>1\<rangle>"

| CondT\<^isub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>true,s\<^isub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^isub>1,s\<^isub>1\<rangle> \<Rightarrow> \<langle>e',s\<^isub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>if (e) e\<^isub>1 else e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>e',s\<^isub>2\<rangle>"
| CondF\<^isub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>false,s\<^isub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^isub>2,s\<^isub>1\<rangle> \<Rightarrow> \<langle>e',s\<^isub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>if (e) e\<^isub>1 else e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>e',s\<^isub>2\<rangle>"
| CondThrow\<^isub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>if (e) e\<^isub>1 else e\<^isub>2, s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"

| WhileF\<^isub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>false,s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>while (e) c,s\<^isub>0\<rangle> \<Rightarrow> \<langle>unit,s\<^isub>1\<rangle>"
| WhileT\<^isub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>true,s\<^isub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>c,s\<^isub>1\<rangle> \<Rightarrow> \<langle>Val v\<^isub>1,s\<^isub>2\<rangle>;
    P \<turnstile>\<^sub>1 \<langle>while (e) c,s\<^isub>2\<rangle> \<Rightarrow> \<langle>e\<^isub>3,s\<^isub>3\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>while (e) c,s\<^isub>0\<rangle> \<Rightarrow> \<langle>e\<^isub>3,s\<^isub>3\<rangle>"
| WhileCondThrow\<^isub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>while (e) c,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"
| WhileBodyThrow\<^isub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>true,s\<^isub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>c,s\<^isub>1\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>2\<rangle>\<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>while (e) c,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>2\<rangle>"

| Throw\<^isub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>throw e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Throw a,s\<^isub>1\<rangle>"
| ThrowNull\<^isub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>throw e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^isub>1\<rangle>"
| ThrowThrow\<^isub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>throw e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle>"

| Try\<^isub>1:
  "P \<turnstile>\<^sub>1 \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v\<^isub>1,s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>try e\<^isub>1 catch(C i) e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v\<^isub>1,s\<^isub>1\<rangle>"
| TryCatch\<^isub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Throw a,(h\<^isub>1,ls\<^isub>1)\<rangle>;
    h\<^isub>1 a = Some(D,fs); P \<turnstile> D \<preceq>\<^sup>* C; i < length ls\<^isub>1;
    P \<turnstile>\<^sub>1 \<langle>e\<^isub>2,(h\<^isub>1,ls\<^isub>1[i:=Addr a])\<rangle> \<Rightarrow> \<langle>e\<^isub>2',(h\<^isub>2,ls\<^isub>2)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>try e\<^isub>1 catch(C i) e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>e\<^isub>2',(h\<^isub>2,ls\<^isub>2)\<rangle>"
| TryThrow\<^isub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Throw a,(h\<^isub>1,ls\<^isub>1)\<rangle>; h\<^isub>1 a = Some(D,fs); \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>try e\<^isub>1 catch(C i) e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Throw a,(h\<^isub>1,ls\<^isub>1)\<rangle>"

| Nil\<^isub>1:
  "P \<turnstile>\<^sub>1 \<langle>[],s\<rangle> [\<Rightarrow>] \<langle>[],s\<rangle>"

| Cons\<^isub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^isub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>es,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>es',s\<^isub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e#es,s\<^isub>0\<rangle> [\<Rightarrow>] \<langle>Val v # es',s\<^isub>2\<rangle>"
| ConsThrow\<^isub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^isub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>e#es,s\<^isub>0\<rangle> [\<Rightarrow>] \<langle>throw e' # es, s\<^isub>1\<rangle>"

(*<*)
lemmas eval\<^isub>1_evals\<^isub>1_induct = eval\<^isub>1_evals\<^isub>1.induct [split_format (complete)]
  and eval\<^isub>1_evals\<^isub>1_inducts = eval\<^isub>1_evals\<^isub>1.inducts [split_format (complete)]
(*>*)

lemma eval\<^isub>1_preserves_len:
  "P \<turnstile>\<^sub>1 \<langle>e\<^isub>0,(h\<^isub>0,ls\<^isub>0)\<rangle> \<Rightarrow> \<langle>e\<^isub>1,(h\<^isub>1,ls\<^isub>1)\<rangle> \<Longrightarrow> length ls\<^isub>0 = length ls\<^isub>1"
and evals\<^isub>1_preserves_len:
  "P \<turnstile>\<^sub>1 \<langle>es\<^isub>0,(h\<^isub>0,ls\<^isub>0)\<rangle> [\<Rightarrow>] \<langle>es\<^isub>1,(h\<^isub>1,ls\<^isub>1)\<rangle> \<Longrightarrow> length ls\<^isub>0 = length ls\<^isub>1"
(*<*)by (induct rule:eval\<^isub>1_evals\<^isub>1_inducts, simp_all)(*>*)


lemma evals\<^isub>1_preserves_elen:
  "\<And>es' s s'. P \<turnstile>\<^sub>1 \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> length es = length es'"
(*<*)
apply(induct es type:list)
apply (auto elim:evals\<^isub>1.cases)
done
(*>*)


lemma eval\<^isub>1_final: "P \<turnstile>\<^sub>1 \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> final e'"
 and evals\<^isub>1_final: "P \<turnstile>\<^sub>1 \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> finals es'"
(*<*)by(induct rule:eval\<^isub>1_evals\<^isub>1.inducts, simp_all)(*>*)


end
