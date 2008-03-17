(*  Title:      HOL/MicroJava/JVM/JVMExec.thy
    ID:         $Id: JVMExec.thy,v 1.4 2008-03-17 22:01:38 makarius Exp $
    Author:     Cornelia Pusch, Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* \isaheader{Program Execution in the JVM} *}

theory JVMExec imports JVMExecInstr JVMExceptions begin

syntax instrs_of :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> instr list"
translations "instrs_of P C M" == "fst(snd(snd(snd(snd(snd(method P C M))))))"


-- "single step execution:"
consts
  exec :: "jvm_prog \<times> jvm_state => jvm_state option"
recdef exec "{}"
  "exec (P, xp, h, []) = None"

  "exec (P, None, h, (stk,loc,C,M,pc)#frs) =
  (let 
     i = instrs_of P C M ! pc;
     (xcpt', h', frs') = exec_instr i P h stk loc C M pc frs
   in Some(case xcpt' of
             None \<Rightarrow> (None,h',frs')
           | Some a \<Rightarrow> find_handler P a h ((stk,loc,C,M,pc)#frs)))"

  "exec (P, Some xa, h, frs) = None" 

(* Needed because recdef splits clauses further up *)
lemma [simp]: "exec (P, x, h, []) = None"
by(cases x) simp+

-- "relational view"
inductive_set
  exec_1 :: "jvm_prog \<Rightarrow> (jvm_state \<times> jvm_state) set"
  and exec_1' :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> jvm_state \<Rightarrow> bool" 
    ("_ \<turnstile>/ _ -jvm\<rightarrow>\<^isub>1/ _" [61,61,61] 60)
  for P :: jvm_prog
where
  "P \<turnstile> \<sigma> -jvm\<rightarrow>\<^isub>1 \<sigma>' \<equiv> (\<sigma>,\<sigma>') \<in> exec_1 P"
| exec_1I: "exec (P,\<sigma>) = Some \<sigma>' \<Longrightarrow> P \<turnstile> \<sigma> -jvm\<rightarrow>\<^isub>1 \<sigma>'"

-- "reflexive transitive closure:"
consts
  exec_all :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> jvm_state \<Rightarrow> bool"
              ("_ |-/ _ -jvm->/ _" [61,61,61]60)
(* FIXME exec_all \<rightarrow> exec_star, also in Def.JVM *)
syntax (xsymbols)
  exec_all :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> jvm_state \<Rightarrow> bool"
              ("(_ \<turnstile>/ _ -jvm\<rightarrow>/ _)" [61,61,61]60)
defs
  exec_all_def1: "P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>' \<equiv> (\<sigma>,\<sigma>') \<in> (exec_1 P)\<^sup>*"


lemma exec_1_eq:
  "exec_1 P = {(\<sigma>,\<sigma>'). exec (P,\<sigma>) = Some \<sigma>'}"
(*<*)by (auto intro: exec_1I elim: exec_1.cases)(*>*)

lemma exec_1_iff:
  "P \<turnstile> \<sigma> -jvm\<rightarrow>\<^isub>1 \<sigma>' = (exec (P,\<sigma>) = Some \<sigma>')"
(*<*)by (simp add: exec_1_eq)(*>*)

lemma exec_all_def:
  "P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>' = ((\<sigma>,\<sigma>') \<in> {(\<sigma>,\<sigma>'). exec (P,\<sigma>) = Some \<sigma>'}\<^sup>*)"
(*<*)by (simp add: exec_all_def1 exec_1_eq)(*>*)

lemma jvm_refl[iff]: "P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>"
(*<*)by(simp add: exec_all_def)(*>*)

lemma jvm_trans[trans]:
 "\<lbrakk> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'; P \<turnstile> \<sigma>' -jvm\<rightarrow> \<sigma>'' \<rbrakk> \<Longrightarrow> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>''"
(*<*)by(simp add: exec_all_def)(*>*)

lemma jvm_one_step1[trans]:
 "\<lbrakk> P \<turnstile> \<sigma> -jvm\<rightarrow>\<^isub>1 \<sigma>'; P \<turnstile> \<sigma>' -jvm\<rightarrow> \<sigma>'' \<rbrakk> \<Longrightarrow> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>''"
(*<*) by (simp add: exec_all_def1) (*>*)

lemma jvm_one_step2[trans]:
 "\<lbrakk> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'; P \<turnstile> \<sigma>' -jvm\<rightarrow>\<^isub>1 \<sigma>'' \<rbrakk> \<Longrightarrow> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>''"
(*<*) by (simp add: exec_all_def1) (*>*)

lemma exec_all_conf:
  "\<lbrakk> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'; P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'' \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<sigma>' -jvm\<rightarrow> \<sigma>'' \<or> P \<turnstile> \<sigma>'' -jvm\<rightarrow> \<sigma>'"
(*<*)by(simp add: exec_all_def single_valued_def single_valued_confluent)(*>*)


lemma exec_all_finalD: "P \<turnstile> (x, h, []) -jvm\<rightarrow> \<sigma> \<Longrightarrow> \<sigma> = (x, h, [])"
(*<*)
apply(simp only: exec_all_def)
apply(erule converse_rtranclE)
 apply simp
apply simp
done
(*>*)

lemma exec_all_deterministic:
  "\<lbrakk> P \<turnstile> \<sigma> -jvm\<rightarrow> (x,h,[]); P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>' \<rbrakk> \<Longrightarrow> P \<turnstile> \<sigma>' -jvm\<rightarrow> (x,h,[])"
(*<*)
apply(drule (1) exec_all_conf)
apply(blast dest!: exec_all_finalD)
done
(*>*)


text {*
  The start configuration of the JVM: in the start heap, we call a 
  method @{text m} of class @{text C} in program @{text P}. The 
  @{text this} pointer of the frame is set to @{text Null} to simulate
  a static method invokation.
*}
constdefs  
  start_state :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> jvm_state"
  "start_state P C M \<equiv>
  let (D,Ts,T,mxs,mxl\<^isub>0,b) = method P C M in
    (None, start_heap P, [([], Null # replicate mxl\<^isub>0 arbitrary, C, M, 0)])"

end
