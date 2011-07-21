theory Code_Generation imports
  "J_Execute"
  "JVM_Execute" 
  "../Compiler/Preprocessor"
  "../BV/BCVExec"
  "../Compiler/Compiler"
  "ToString"
  "../../Coinductive/Lazy_TLList"
  "~~/src/HOL/Library/Code_Integer"
  "~~/src/HOL/Library/Code_Char"
  "~~/src/HOL/Library/Efficient_Nat"
begin

definition j_Program :: "addr J_mb cdecl list \<Rightarrow> addr J_prog"
where "j_Program = Program"

export_code wf_J_prog' j_Program in SML file "~/isabelle/JinjaThreads/JinjaThreads/Execute/JWellForm.ML" 

text {*
  Replace @{term undefined} values by constants.
  The JVM fills the array of local variables with @{term "undefined"}, which
  causes ML to raise an exception, although these values are never used.
*}

definition undefined_value :: "'addr val" where [code del]: "undefined_value = undefined"
lemmas [code_inline] = undefined_value_def[symmetric]
code_const undefined_value
  (SML "Value.Unit")
  (Haskell "Value.Unit")
  (OCaml "Value.Unit")


text {* equations on predicate operations for code inlining *}

lemma eq_i_o_conv_single: "eq_i_o = Predicate.single"
by(rule ext)(simp add: Predicate.single_bind eq.equation)

lemma eq_o_i_conv_single: "eq_o_i = Predicate.single"
by(rule ext)(simp add: Predicate.single_bind eq.equation)

lemma sup_exp_case_exp_case_same:
  "semilattice_sup_class.sup 
    (exp_case cNew cNewArray cCast cInstanceOf cVal cBinOp cVar cLAss cAAcc cAAss cALen cFAcc cFAss cCall cBlock cSync cInSync cSeq cCond cWhile cThrow cTry e)
    (exp_case cNew' cNewArray' cCast' cInstanceOf' cVal' cBinOp' cVar' cLAss' cAAcc' cAAss' cALen' cFAcc' cFAss' cCall' cBlock' cSync' cInSync' cSeq' cCond' cWhile' cThrow' cTry' e) =
  (case e of
    new C \<Rightarrow> semilattice_sup_class.sup (cNew C) (cNew' C)
  | newArray T e \<Rightarrow> semilattice_sup_class.sup (cNewArray T e) (cNewArray' T e)
  | Cast T e \<Rightarrow> semilattice_sup_class.sup (cCast T e) (cCast' T e)
  | InstanceOf e T \<Rightarrow> semilattice_sup_class.sup (cInstanceOf e T) (cInstanceOf' e T)
  | Val v \<Rightarrow> semilattice_sup_class.sup (cVal v) (cVal' v)
  | BinOp e bop e' \<Rightarrow> semilattice_sup_class.sup (cBinOp e bop e') (cBinOp' e bop e')
  | Var V \<Rightarrow> semilattice_sup_class.sup (cVar V) (cVar' V)
  | LAss V e \<Rightarrow> semilattice_sup_class.sup (cLAss V e) (cLAss' V e)
  | AAcc a e \<Rightarrow> semilattice_sup_class.sup (cAAcc a e) (cAAcc' a e)
  | AAss a i e \<Rightarrow> semilattice_sup_class.sup (cAAss a i e) (cAAss' a i e)
  | ALen a \<Rightarrow> semilattice_sup_class.sup (cALen a) (cALen' a)
  | FAcc e F D \<Rightarrow> semilattice_sup_class.sup (cFAcc e F D) (cFAcc' e F D)
  | FAss e F D e' \<Rightarrow> semilattice_sup_class.sup (cFAss e F D e') (cFAss' e F D e')
  | Call e M es \<Rightarrow> semilattice_sup_class.sup (cCall e M es) (cCall' e M es)
  | Block V T vo e \<Rightarrow> semilattice_sup_class.sup (cBlock V T vo e) (cBlock' V T vo e)
  | Synchronized v e e' \<Rightarrow> semilattice_sup_class.sup (cSync v e e') (cSync' v e e')
  | InSynchronized v a e \<Rightarrow> semilattice_sup_class.sup (cInSync v a e) (cInSync' v a e)
  | Seq e e' \<Rightarrow> semilattice_sup_class.sup (cSeq e e') (cSeq' e e')
  | Cond b e e' \<Rightarrow> semilattice_sup_class.sup (cCond b e e') (cCond' b e e')
  | While b e \<Rightarrow> semilattice_sup_class.sup (cWhile b e) (cWhile' b e)
  | throw e \<Rightarrow> semilattice_sup_class.sup (cThrow e) (cThrow' e)
  | TryCatch e C V e' \<Rightarrow> semilattice_sup_class.sup (cTry e C V e') (cTry' e C V e'))"
apply(cases e)
apply(simp_all)
done

lemma sup_exp_case_exp_case_other:
  "semilattice_sup_class.sup 
    (exp_case cNew cNewArray cCast cInstanceOf cVal cBinOp cVar cLAss cAAcc cAAss cALen cFAcc cFAss cCall cBlock cSync cInSync cSeq cCond cWhile cThrow cTry e)
    (semilattice_sup_class.sup (exp_case cNew' cNewArray' cCast' cInstanceOf' cVal' cBinOp' cVar' cLAss' cAAcc' cAAss' cALen' cFAcc' cFAss' cCall' cBlock' cSync' cInSync' cSeq' cCond' cWhile' cThrow' cTry' e) p) =
  semilattice_sup_class.sup (case e of
    new C \<Rightarrow> semilattice_sup_class.sup (cNew C) (cNew' C)
  | newArray T e \<Rightarrow> semilattice_sup_class.sup (cNewArray T e) (cNewArray' T e)
  | Cast T e \<Rightarrow> semilattice_sup_class.sup (cCast T e) (cCast' T e)
  | InstanceOf e T \<Rightarrow> semilattice_sup_class.sup (cInstanceOf e T) (cInstanceOf' e T)
  | Val v \<Rightarrow> semilattice_sup_class.sup (cVal v) (cVal' v)
  | BinOp e bop e' \<Rightarrow> semilattice_sup_class.sup (cBinOp e bop e') (cBinOp' e bop e')
  | Var V \<Rightarrow> semilattice_sup_class.sup (cVar V) (cVar' V)
  | LAss V e \<Rightarrow> semilattice_sup_class.sup (cLAss V e) (cLAss' V e)
  | AAcc a e \<Rightarrow> semilattice_sup_class.sup (cAAcc a e) (cAAcc' a e)
  | AAss a i e \<Rightarrow> semilattice_sup_class.sup (cAAss a i e) (cAAss' a i e)
  | ALen a \<Rightarrow> semilattice_sup_class.sup (cALen a) (cALen' a)
  | FAcc e F D \<Rightarrow> semilattice_sup_class.sup (cFAcc e F D) (cFAcc' e F D)
  | FAss e F D e' \<Rightarrow> semilattice_sup_class.sup (cFAss e F D e') (cFAss' e F D e')
  | Call e M es \<Rightarrow> semilattice_sup_class.sup (cCall e M es) (cCall' e M es)
  | Block V T vo e \<Rightarrow> semilattice_sup_class.sup (cBlock V T vo e) (cBlock' V T vo e)
  | Synchronized v e e' \<Rightarrow> semilattice_sup_class.sup (cSync v e e') (cSync' v e e')
  | InSynchronized v a e \<Rightarrow> semilattice_sup_class.sup (cInSync v a e) (cInSync' v a e)
  | Seq e e' \<Rightarrow> semilattice_sup_class.sup (cSeq e e') (cSeq' e e')
  | Cond b e e' \<Rightarrow> semilattice_sup_class.sup (cCond b e e') (cCond' b e e')
  | While b e \<Rightarrow> semilattice_sup_class.sup (cWhile b e) (cWhile' b e)
  | throw e \<Rightarrow> semilattice_sup_class.sup (cThrow e) (cThrow' e)
  | TryCatch e C V e' \<Rightarrow> semilattice_sup_class.sup (cTry e C V e') (cTry' e C V e')) p"
apply(cases e)
apply(simp_all add: inf_sup_aci sup.assoc)
done

lemma sup_bot1: "semilattice_sup_class.sup bot a = a"
by(rule sup_absorb2)auto

lemma sup_bot2: "semilattice_sup_class.sup a bot = a"
by(rule sup_absorb1) auto

lemma sup_val_case_val_case_same:
  "semilattice_sup_class.sup (val_case cUnit cNull cBool cIntg cAddr v) (val_case cUnit' cNull' cBool' cIntg' cAddr' v) =
   (case v of
     Unit \<Rightarrow> semilattice_sup_class.sup cUnit cUnit'
   | Null \<Rightarrow> semilattice_sup_class.sup cNull cNull'
   | Bool b \<Rightarrow> semilattice_sup_class.sup (cBool b) (cBool' b)
   | Intg i \<Rightarrow> semilattice_sup_class.sup (cIntg i) (cIntg' i)
   | Addr a \<Rightarrow> semilattice_sup_class.sup (cAddr a) (cAddr' a))"
apply(cases v)
apply simp_all
done

lemma sup_bool_case_bool_case_same:
  "semilattice_sup_class.sup (bool_case t f b) (bool_case t' f' b) =
  (if b then semilattice_sup_class.sup t t' else semilattice_sup_class.sup f f')"
by simp

lemmas predicate_code_inline =
  Predicate.single_bind Predicate.bind_single split
  eq_i_o_conv_single eq_o_i_conv_single
  sup_exp_case_exp_case_same sup_exp_case_exp_case_other unit.cases
  sup_bot1 sup_bot2 sup_val_case_val_case_same sup_bool_case_bool_case_same

declare predicate_code_inline [code_inline]

text {* Functions for extracting calls to the native print method *}

definition purge where
  "\<And>run.
  purge run = 
  lmap (\<lambda>obs. case obs of ExternalCall _ _ (Cons (Intg i) _) v \<Rightarrow> i)
  (lfilter
    (\<lambda>obs. case obs of ExternalCall _ M (Cons (Intg i) Nil) _ \<Rightarrow> M = print | _ \<Rightarrow> False) 
    (lconcat (lmap (llist_of \<circ> snd) (llist_of_tllist run))))"

text {* Various other functions *}

fun heapobj_toString :: "heapobj \<Rightarrow> String.literal"
where
  "heapobj_toString (Obj C fs) = Aux.concat [STR ''(Obj '', toString C, STR '', '', toString fs, STR '')'']"
| "heapobj_toString (Arr T si fs el) = 
   Aux.concat [STR ''(['', toString si, STR '']'', toString T, STR '', '', toString fs, STR '', '', toString (map snd (rm_to_list el)), STR '')'']"
instantiation heapobj :: toString begin
definition [code]: "toString = heapobj_toString"
instance proof qed
end

definition llist_case' where "llist_case' = llist_case"
definition tllist_case' where "tllist_case' = tllist_case"
definition terminal' where "terminal' = terminal"
definition llist_of_tllist' where "llist_of_tllist' = llist_of_tllist"
definition thr' where "thr' = thr"
definition shr' where "shr' = shr"

definition heap_toString :: "heap \<Rightarrow> String.literal"
where "heap_toString = toString"

definition thread_toString :: "(thread_id, (addr expr \<times> addr locals) \<times> (addr \<Rightarrow>\<^isub>f nat)) rbt \<Rightarrow> String.literal"
where "thread_toString = toString"

definition trace_toString :: "thread_id \<times> (addr, thread_id) obs_event list \<Rightarrow> String.literal"
where "trace_toString = toString"

export_code
  wf_J_prog' exec_J_rr exec_J_rnd 
  j_Program
  purge llist_case' tllist_case' terminal' llist_of_tllist'
  thr' shr' heap_toString thread_toString trace_toString
  in SML
  file "~/isabelle/JinjaThreads/JinjaThreads/Execute/J_Execute.ML"

definition j2jvm :: "addr J_prog \<Rightarrow> addr jvm_prog" where "j2jvm = J2JVM"

export_code
  wf_jvm_prog' exec_JVM_rr exec_JVM_rnd j2jvm
  j_Program
  purge llist_case' tllist_case' terminal' llist_of_tllist'
  thr' shr' heap_toString thread_toString trace_toString
  in SML
  file "~/isabelle/JinjaThreads/JinjaThreads/Execute/JVM_Execute.ML"

end