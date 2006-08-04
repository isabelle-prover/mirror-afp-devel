(*  Title:       CoreC++
    ID:          $Id: Expr.thy,v 1.5 2006-08-04 10:56:49 wasserra Exp $
    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>
    Based on the Jinja theory J/Expr.thy by Tobias Nipkow 
*)


header {* \isaheader{Expressions} *}

theory Expr imports Value begin

section {* The expressions *}


datatype bop = Eq | Add     -- "names of binary operations"

datatype expr
  = new cname            -- "class instance creation"
  | Cast cname expr      -- "dynamic type cast"
  | StatCast cname expr  -- "static type cast"        
                                 ("\<lparr>_\<rparr>_" [80,81] 80)
  | Val val              -- "value"
  | BinOp expr bop expr          ("_ \<guillemotleft>_\<guillemotright> _" [80,0,81] 80)     
     -- "binary operation"
  | Var vname            -- "local variable"
  | LAss vname expr              ("_:=_" [70,70] 70)            
     -- "local assignment"
  | FAcc expr vname path         ("_\<bullet>_{_}" [10,90,99] 90)      
     -- "field access"
  | FAss expr vname path expr    ("_\<bullet>_{_} := _" [10,70,99,70] 70)      
     -- "field assignment"
  | Call expr mname "expr list"  ("_\<bullet>_'(_')" [90,99,0] 90)            
     -- "method call"
  | Block vname ty expr          ("'{_:_; _}")
  | Seq expr expr                ("_;;/ _" [61,60] 60)
  | Cond expr expr expr          ("if '(_') _/ else _" [80,79,79] 70)
  | While expr expr              ("while '(_') _" [80,79] 70)
  | throw expr


text{*The semantics of binary operators: *}

consts
  binop :: "bop \<times> val \<times> val \<Rightarrow> val option"

recdef binop "{}"
  "binop(Eq,v\<^isub>1,v\<^isub>2) = Some(Bool (v\<^isub>1 = v\<^isub>2))"
  "binop(Add,Intg i\<^isub>1,Intg i\<^isub>2) = Some(Intg(i\<^isub>1+i\<^isub>2))"
  "binop(bop,v\<^isub>1,v\<^isub>2) = None"

lemma [simp]:
  "(binop(Add,v\<^isub>1,v\<^isub>2) = Some v) = (\<exists>i\<^isub>1 i\<^isub>2. v\<^isub>1 = Intg i\<^isub>1 \<and> v\<^isub>2 = Intg i\<^isub>2 \<and> v = Intg(i\<^isub>1+i\<^isub>2))"

apply(cases v\<^isub>1)
apply auto
apply(cases v\<^isub>2)
apply auto
done


lemma binop_not_ref[simp]:
  "binop(bop,v\<^isub>1,v\<^isub>2) = Some (Ref r) \<Longrightarrow> False"
by(cases bop)auto


section{*Free Variables*} 

consts
  fv  :: "expr      \<Rightarrow> vname set"
  fvs :: "expr list \<Rightarrow> vname set"
primrec
  "fv(new C) = {}"
  "fv(Cast C e) = fv e"
  "fv(\<lparr>C\<rparr>e) = fv e"
  "fv(Val v) = {}"
  "fv(e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2) = fv e\<^isub>1 \<union> fv e\<^isub>2"
  "fv(Var V) = {V}"
  "fv(V := e) = {V} \<union> fv e"
  "fv(e\<bullet>F{Cs}) = fv e"
  "fv(e\<^isub>1\<bullet>F{Cs}:=e\<^isub>2) = fv e\<^isub>1 \<union> fv e\<^isub>2"
  "fv(e\<bullet>M(es)) = fv e \<union> fvs es"
  "fv({V:T; e}) = fv e - {V}"
  "fv(e\<^isub>1;;e\<^isub>2) = fv e\<^isub>1 \<union> fv e\<^isub>2"
  "fv(if (b) e\<^isub>1 else e\<^isub>2) = fv b \<union> fv e\<^isub>1 \<union> fv e\<^isub>2"
  "fv(while (b) e) = fv b \<union> fv e"
  "fv(throw e) = fv e"

  "fvs([]) = {}"
  "fvs(e#es) = fv e \<union> fvs es"

lemma [simp]: "fvs(es\<^isub>1 @ es\<^isub>2) = fvs es\<^isub>1 \<union> fvs es\<^isub>2"
by (induct es\<^isub>1 type:list) auto

lemma [simp]: "fvs(map Val vs) = {}"
by (induct vs) auto


end
