(*  Title:      Jinja/J/Example.thy
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* \isaheader{Example Jinja Program} *}

theory Example imports SystemClasses JWellForm begin

text {* 
The following example Jinja program includes:
 class declarations with inheritance, hiding of fields, and overriding of
  methods (with refined result type), 
 instance creation, local assignment, sequential composition,
 method call with dynamic binding, literal values,
 expression statement, local access, type cast, field assignment (in part), 
 skip.

\begin{verbatim}
class Base {
  boolean vee;
  Base foo(Base x) {return x;}
}

class Ext extends Base {
  int vee;
  Ext foo(Base x) {((Ext)x).vee=1; return null;}
}

class Example {
  public static void main (String args[]) {
    Base e=new Ext();
    e.foo(null);
  }
}
\end{verbatim}
*}

datatype cnam' = Base' | Ext'
datatype vnam' = vee' | x' | e'

consts
  cnam' :: "cnam' => cname"
  vnam' :: "vnam' => vnam"

-- "@{text cnam'} and @{text vnam'} are intended to be isomorphic 
    to @{text cnam} and @{text vnam}"
axioms 
  inj_cnam':  "(cnam' x = cnam' y) = (x = y)"
  inj_vnam':  "(vnam' x = vnam' y) = (x = y)"

  surj_cnam': "\<exists>m. n = cnam' m"
  surj_vnam': "\<exists>m. n = vnam' m"

declare inj_cnam' [simp] inj_vnam' [simp]

abbreviation "Base == cnam' Base'"
abbreviation "Ext == cnam' Ext'"
abbreviation "vee == VName (vnam' vee')"
abbreviation "x == VName (vnam' x')"
abbreviation "e == VName (vnam' e')"

axioms
  Base_not_Object: "Base \<noteq> Object"
  Ext_not_Object:  "Ext  \<noteq> Object"
  Base_not_Xcpt:   "Base \<noteq> Xcpt z"
  Ext_not_Xcpt:    "Ext  \<noteq> Xcpt z"
  e_not_This:      "e \<noteq> This"  

declare Base_not_Object [simp] Ext_not_Object [simp]
declare Base_not_Xcpt [simp] Ext_not_Xcpt [simp]
declare e_not_This [simp]
declare Base_not_Object [symmetric, simp]
declare Ext_not_Object  [symmetric, simp]
declare Base_not_Xcpt [symmetric, simp]
declare Ext_not_Xcpt  [symmetric, simp]

consts
  foo_Base::  J_mb
  foo_Ext ::  J_mb
  BaseC   :: "J_mb cdecl"
  ExtC    :: "J_mb cdecl"
  test    ::  stmt
  foo   ::  mname
  a   ::  loc
  b       ::  loc

defs
  foo_Base_def:"foo_Base == ([x],[],Expr(LAss Result (Var x)))"
  BaseC_def:"BaseC == (Base, (Object, 
           [(vee, PrimT Boolean)], 
           [(foo,[Class Base],Class Base,foo_Base)]))"
  foo_Ext_def:"foo_Ext == ([x],[],Expr( {Ext}Cast Ext
               (Var x)\<bullet>vee:=Lit (Intg Numeral1));;
               Expr(LAss Result (Lit Null)))"
  ExtC_def: "ExtC  == (Ext,  (Base  , 
           [(vee, PrimT Integer)], 
           [(foo,[Class Base],Class Ext,foo_Ext)]))"

  test_def:"test == Expr(e:=New Ext);; 
                    Expr(Var e\<bullet>foo([Lit Null]))"


abbreviation "NP == NullPointer"
abbreviation "tprg == [ObjectC, BaseC, ExtC, ClassCastC, NullPointerC, OutOfMemoryC]"

abbreviation (output)
  "obj1 == (Ext, empty((vee, Base)\<mapsto>Bool False)
         ((vee, Ext )\<mapsto>Intg 0))"

abbreviation "s0 == Norm    (empty, empty)"
abbreviation "s1 == Norm    (empty(a\<mapsto>obj1),empty(e\<mapsto>Addr a))"
abbreviation "s2 == Norm    (empty(a\<mapsto>obj1),empty(x\<mapsto>Null)(This\<mapsto>Addr a))"
abbreviation "s3 == (Some NP, empty(a\<mapsto>obj1),empty(e\<mapsto>Addr a))"


lemmas map_of_Cons = map_of.simps(2)
lemma map_of_Cons1 [simp]: "map_of ((aa,bb)#ps) aa = Some bb"
(*<*)
apply (simp (no_asm))
done
(*>*)
lemma map_of_Cons2 [simp]: "aa\<noteq>k ==> map_of ((k,bb)#ps) aa = map_of ps aa"
(*<*)
apply (simp (no_asm_simp))
done
(*>*)
declare map_of_Cons [simp del] -- "sic!"

lemma class_tprg_Object [simp]: "class tprg Object = Some (undefined, [], [])"
(*<*)
apply (unfold ObjectC_def class_def)
apply (simp (no_asm))
done
(*>*)

lemma class_tprg_NP [simp]: "class tprg (Xcpt NP) = Some (Object, [], [])"
(*<*)
apply (unfold ObjectC_def NullPointerC_def ClassCastC_def OutOfMemoryC_def BaseC_def ExtC_def class_def)
apply (simp (no_asm))
done
(*>*)

lemma class_tprg_OM [simp]: "class tprg (Xcpt OutOfMemory) = Some (Object, [], [])"
(*<*)
apply (unfold ObjectC_def NullPointerC_def ClassCastC_def OutOfMemoryC_def BaseC_def ExtC_def class_def)
apply (simp (no_asm))
done
(*>*)

lemma class_tprg_CC [simp]: "class tprg (Xcpt ClassCast) = Some (Object, [], [])"
(*<*)
apply (unfold ObjectC_def NullPointerC_def ClassCastC_def OutOfMemoryC_def BaseC_def ExtC_def class_def)
apply (simp (no_asm))
done
(*>*)

lemma class_tprg_Base [simp]: 
"class tprg Base = Some (Object,  
    [(vee, PrimT Boolean)],  
          [(foo, [Class Base], Class Base, foo_Base)])"
(*<*)
apply (unfold ObjectC_def NullPointerC_def ClassCastC_def OutOfMemoryC_def BaseC_def ExtC_def class_def)
apply (simp (no_asm))
done
(*>*)

lemma class_tprg_Ext [simp]: 
"class tprg Ext = Some (Base,  
    [(vee, PrimT Integer)],  
          [(foo, [Class Base], Class Ext, foo_Ext)])"
(*<*)
apply (unfold ObjectC_def BaseC_def ExtC_def class_def)
apply (simp (no_asm))
done
(*>*)

lemma not_Object_subcls [elim!]: "(Object,C) \<in> (subcls1 tprg)^+ ==> R"
(*<*)
apply (auto dest!: tranclD subcls1D)
done
(*>*)

lemma subcls_ObjectD [dest!]: "tprg\<turnstile>Object\<preceq>\<^sub>C C ==> C = Object"
(*<*)
apply (erule rtrancl_induct)
apply  auto
apply (drule subcls1D)
apply auto
done
(*>*)

lemma not_Base_subcls_Ext [elim!]: "(Base, Ext) \<in> (subcls1 tprg)^+ ==> R"
(*<*)
apply (auto dest!: tranclD subcls1D)
done
(*>*)

lemma class_tprgD: 
"class tprg C = Some z ==> C=Object \<or> C=Base \<or> C=Ext \<or> C=Xcpt NP \<or> C=Xcpt ClassCast \<or> C=Xcpt OutOfMemory"
(*<*)
apply (unfold ObjectC_def ClassCastC_def NullPointerC_def OutOfMemoryC_def BaseC_def ExtC_def class_def)
apply (auto split add: split_if_asm simp add: map_of_Cons)
done
(*>*)

lemma not_class_subcls_class [elim!]: "(C,C) \<in> (subcls1 tprg)^+ ==> R"
(*<*)
apply (auto dest!: tranclD subcls1D)
apply (frule class_tprgD)
apply (auto dest!:)
apply (drule rtranclD)
apply auto
done
(*>*)

lemma distinct_fst_classes: "distinct_fst tprg"
(*<*)
apply (simp (no_asm) add: ObjectC_def BaseC_def ExtC_def NullPointerC_def ClassCastC_def OutOfMemoryC_def)
done
(*>*)

lemmas subcls_direct = subcls1I [THEN r_into_rtrancl]

lemma Ext_subcls_Base [simp]: "tprg\<turnstile>Ext\<preceq>\<^sub>C Base"
(*<*)
apply (rule subcls_direct)
apply auto
done
(*>*)

lemma Ext_widen_Base [simp]: "tprg\<turnstile>Class Ext\<preceq> Class Base"
(*<*)
apply (rule widen.subcls)
apply (simp (no_asm))
done
(*>*)

declare ty_expr_ty_exprs_wt_stmt.intros [intro!]

lemma acyclic_subcls1': "acyclic (subcls1 tprg)"
(*<*)
apply (rule acyclicI)
apply safe
done
(*>*)

lemmas wf_subcls1' = acyclic_subcls1' [THEN finite_subcls1 [THEN finite_acyclic_wf_converse]]

lemmas fields_rec' = wf_subcls1' [THEN [2] fields_rec_lemma]

lemma fields_Object [simp]: "fields (tprg, Object) = []"
(*<*)
apply (subst fields_rec')
apply   auto
done
(*>*)

declare is_class_def [simp]

lemma fields_Base [simp]: "fields (tprg,Base) = [((vee, Base), PrimT Boolean)]"
(*<*)
apply (subst fields_rec')
apply   auto
done
(*>*)

lemma fields_Ext [simp]: 
  "fields (tprg, Ext)  = [((vee, Ext ), PrimT Integer)] @ fields (tprg, Base)"
(*<*)
apply (rule trans)
apply  (rule fields_rec')
apply   auto
done
(*>*)

lemmas method_rec' = wf_subcls1' [THEN [2] method_rec_lemma]

lemma method_Object [simp]: "method tprg Object = map_of []"
(*<*)
apply (subst method_rec')
apply  auto
done
(*>*)

lemma method_Base [simp]: "method tprg Base = map_of  
  [(foo, Base, [Class Base], (Class Base, foo_Base))]"
(*<*)
apply (rule trans)
apply  (rule method_rec')
apply  (auto simp: map_of.simps)
done
(*>*)

lemma method_Ext [simp]: "method tprg Ext = (method tprg Base ++ map_of  
  [(foo, Ext, [Class Base], Class Ext, foo_Ext)])"
(*<*)
apply (rule trans)
apply  (rule method_rec')
apply  (auto simp: map_of.simps)
done
(*>*)

lemma wf_foo_Base: 
"wf_mdecl wf_J_mdecl tprg Base (foo, [Class Base], Class Base, foo_Base)"
(*<*)
apply (unfold wf_mdecl_def wf_mhead_def wf_J_mdecl_def foo_Base_def)
apply auto
apply(rule exI)
apply(rule conjI)
apply(rule DIstmt.intros)
apply(rule DIexpr_DIexprs.intros)
apply(rule DIexpr_DIexprs.intros)
apply simp
apply simp
done
(*>*)

lemma wf_foo_Ext: 
"wf_mdecl wf_J_mdecl tprg Ext (foo, [Class Base], Class Ext, foo_Ext)"
(*<*)
apply (unfold wf_mdecl_def wf_mhead_def wf_J_mdecl_def foo_Ext_def)
apply auto
apply  (rule ty_expr_ty_exprs_wt_stmt.Cast)
prefer 2
apply   (simp)
apply   (rule_tac [2] cast.subcls)
apply   (unfold field_def)
apply   auto
apply(rule exI)
apply(rule conjI)
apply(rule DIexpr_DIexprs.intros DIstmt.intros)+
apply simp
apply(rule DIexpr_DIexprs.intros DIstmt.intros)+
apply simp
done
(*>*)

lemma wf_ObjectC: 
"wf_cdecl wf_J_mdecl tprg ObjectC"
(*<*)
apply (unfold wf_cdecl_def wf_fdecl_def ObjectC_def)
apply (simp (no_asm))
done
(*>*)

lemma wf_NP:
"wf_cdecl wf_J_mdecl tprg NullPointerC"
(*<*)
apply (unfold wf_cdecl_def wf_fdecl_def NullPointerC_def)
apply (simp add: class_def)
apply (fold NullPointerC_def class_def)
apply auto
done
(*>*)

lemma wf_OM:
"wf_cdecl wf_J_mdecl tprg OutOfMemoryC"
(*<*)
apply (unfold wf_cdecl_def wf_fdecl_def OutOfMemoryC_def)
apply (simp add: class_def)
apply (fold OutOfMemoryC_def class_def)
apply auto
done
(*>*)

lemma wf_CC:
"wf_cdecl wf_J_mdecl tprg ClassCastC"
(*<*)
apply (unfold wf_cdecl_def wf_fdecl_def ClassCastC_def)
apply (simp add: class_def)
apply (fold ClassCastC_def class_def)
apply auto
done
(*>*)

lemma wf_BaseC: 
"wf_cdecl wf_J_mdecl tprg BaseC"
(*<*)
apply (unfold wf_cdecl_def wf_fdecl_def BaseC_def)
apply (simp (no_asm))
apply (fold BaseC_def)
apply (rule wf_foo_Base [THEN conjI])
apply auto
done
(*>*)

lemma wf_ExtC: 
"wf_cdecl wf_J_mdecl tprg ExtC"
(*<*)
apply (unfold wf_cdecl_def wf_fdecl_def ExtC_def)
apply (simp (no_asm))
apply (fold ExtC_def)
apply (rule wf_foo_Ext [THEN conjI])
apply (auto simp add: fun_of_def)
apply (drule rtranclD)
apply auto 
done
(*>*)

lemma [simp]: "fst ObjectC = Object" by (simp add: ObjectC_def)

lemma wf_tprg: 
"wf_prog wf_J_mdecl tprg"
(*<*)
apply (unfold wf_prog_def Let_def)
apply (simp add: wf_ObjectC wf_BaseC wf_ExtC wf_NP wf_OM wf_CC distinct_fst_classes)
apply (rule wf_syscls)
apply (simp add: SystemClasses_def)
done
(*>*)

ML {* fun t thm = resolve_tac @{thms ty_expr_ty_exprs_wt_stmt.intros} 1 thm *}
lemma wt_test: "(tprg, empty(e\<mapsto>Class Base))\<turnstile>  
  Expr(e:=New Ext);; Expr(Var e\<bullet>foo([Lit Null]))\<surd>"
(*<*)
apply (tactic t) -- ";;"
apply  (tactic t) -- "Expr"
apply  (tactic t) -- "LAss"
apply    simp -- {* @{text "e \<noteq> This"} *}
apply    (tactic t) -- "Var"
apply     (simp (no_asm))
apply    (simp (no_asm))
apply   (tactic t) -- "New"
apply   (simp (no_asm))
apply  (simp (no_asm))
apply (tactic t) -- "Expr"
apply (tactic t) -- "Call"
apply   (tactic t) -- "Var"
apply     (simp (no_asm))
apply    (simp (no_asm))
apply   (fastsimp)
apply  (tactic t) -- "Cons"
apply   (tactic t) -- "Lit"
apply   (simp (no_asm))
apply  (tactic t) -- "Nil"
apply (simp add:null fun_of_def)
done
(*>*)

ML {* fun e t = resolve_tac @{thms eval_evals_exec.intros} 1 t *}

declare split_if [split del]
declare init_vars_def [simp] cast_ok_def [simp]
lemma exec_test: 
 "[|new_Addr (hp(snd s0)) = (a, None)|] ==>  tprg \<turnstile> s0 -test\<rightarrow> ?s"
(*<*)
apply (unfold test_def)
-- "?s = s3 "
apply (tactic e) -- ";;"
apply  (tactic e) -- "Expr"
apply  (tactic e) -- "LAss"
apply   (tactic e) -- "New"
apply    force
apply   force
apply  (simp (no_asm))
apply (erule thin_rl)
apply (tactic e) -- "Expr"
apply (tactic e) -- "Call"
apply       (tactic e) -- "Var"
apply      force
apply     (tactic e) -- "Cons"
apply      (tactic e) -- "Lit"
apply     (tactic e) -- "Nil"
apply    (simp (no_asm))
apply   (force simp add: foo_Ext_def)
apply  (simp (no_asm))
apply  (tactic e) -- ";;"
 apply  (tactic e) -- "Expr"
 apply  (tactic e) -- "FAss"
 apply       (tactic e) -- "Cast"
 apply        (tactic e) -- "Var"
 apply       (simp (no_asm))
 apply      (simp (no_asm))
 apply     (simp (no_asm))
 apply     (fast)
 apply    (simp (no_asm))
 apply   (rule surjective_pairing [THEN sym, THEN[2]trans], subst Pair_eq, force)
 apply  (simp (no_asm))
apply  (tactic e) -- "Expr"
done
(*>*)

end
