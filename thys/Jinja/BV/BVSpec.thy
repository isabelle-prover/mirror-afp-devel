(*  Title:      HOL/MicroJava/BV/BVSpec.thy
    ID:         $Id: BVSpec.thy,v 1.2 2008-06-24 22:23:29 makarius Exp $
    Author:     Cornelia Pusch, Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen

*)

header {* \isaheader{The Bytecode Verifier}\label{sec:BVSpec} *}

theory BVSpec
imports Effect
begin

text {*
  This theory contains a specification of the BV. The specification
  describes correct typings of method bodies; it corresponds 
  to type \emph{checking}.
*}


constdefs
  -- "The method type only contains declared classes:"
  check_types :: "'m prog \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ty\<^isub>i' err list \<Rightarrow> bool"
  "check_types P mxs mxl \<tau>s \<equiv> set \<tau>s \<subseteq> states P mxs mxl"

  -- "An instruction is welltyped if it is applicable and its effect"
  -- "is compatible with the type at all successor instructions:"
  wt_instr :: "['m prog,ty,nat,pc,ex_table,instr,pc,ty\<^isub>m] \<Rightarrow> bool"
  ("_,_,_,_,_ \<turnstile> _,_ :: _" [60,0,0,0,0,0,0,61] 60)
  "P,T,mxs,mpc,xt \<turnstile> i,pc :: \<tau>s \<equiv>
  app i P mxs T pc mpc xt (\<tau>s!pc) \<and> 
  (\<forall>(pc',\<tau>') \<in> set (eff i P pc xt (\<tau>s!pc)). P \<turnstile> \<tau>' \<le>' \<tau>s!pc')"

  -- {* The type at @{text "pc=0"} conforms to the method calling convention: *}
  wt_start :: "['m prog,cname,ty list,nat,ty\<^isub>m] \<Rightarrow> bool"
  "wt_start P C Ts mxl\<^isub>0 \<tau>s \<equiv>
  P \<turnstile> Some ([],OK (Class C)#map OK Ts@replicate mxl\<^isub>0 Err) \<le>' \<tau>s!0"

  -- "A method is welltyped if the body is not empty,"
  -- "if the method type covers all instructions and mentions"
  -- "declared classes only, if the method calling convention is respected, and"
  -- "if all instructions are welltyped."
  wt_method :: "['m prog,cname,ty list,ty,nat,nat,instr list,
                 ex_table,ty\<^isub>m] \<Rightarrow> bool"
  "wt_method P C Ts T\<^isub>r mxs mxl\<^isub>0 is xt \<tau>s \<equiv>
  0 < size is \<and> size \<tau>s = size is \<and>
  check_types P mxs (1+size Ts+mxl\<^isub>0) (map OK \<tau>s) \<and>
  wt_start P C Ts mxl\<^isub>0 \<tau>s \<and>
  (\<forall>pc < size is. P,T\<^isub>r,mxs,size is,xt \<turnstile> is!pc,pc :: \<tau>s)"

  -- "A program is welltyped if it is wellformed and all methods are welltyped"
  wf_jvm_prog_phi :: "ty\<^isub>P \<Rightarrow> jvm_prog \<Rightarrow> bool" ("wf'_jvm'_prog\<^bsub>_\<^esub>")
  "wf_jvm_prog\<^bsub>\<Phi>\<^esub> \<equiv>
    wf_prog (\<lambda>P C (M,Ts,T\<^isub>r,(mxs,mxl\<^isub>0,is,xt)). 
      wt_method P C Ts T\<^isub>r mxs mxl\<^isub>0 is xt (\<Phi> C M))"

  wf_jvm_prog :: "jvm_prog \<Rightarrow> bool"
  "wf_jvm_prog P \<equiv> \<exists>\<Phi>. wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"

notation (input)
  wf_jvm_prog_phi  ("wf'_jvm'_prog\<^sub>_ _" [0,999] 1000)


lemma wt_jvm_progD:
  "wf_jvm_prog\<^sub>\<Phi> P \<Longrightarrow> \<exists>wt. wf_prog wt P"
(*<*) by (unfold wf_jvm_prog_phi_def, blast) (*>*)

lemma wt_jvm_prog_impl_wt_instr:
  "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; 
      P \<turnstile> C sees M:Ts \<rightarrow> T = (mxs,mxl\<^isub>0,ins,xt) in C; pc < size ins \<rbrakk> 
  \<Longrightarrow> P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
(*<*)
  apply (unfold wf_jvm_prog_phi_def)
  apply (drule (1) sees_wf_mdecl)
  apply (simp add: wf_mdecl_def wt_method_def)
  done
(*>*)

lemma wt_jvm_prog_impl_wt_start:
  "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; 
     P \<turnstile> C sees M:Ts \<rightarrow> T = (mxs,mxl\<^isub>0,ins,xt) in C \<rbrakk> \<Longrightarrow> 
  0 < size ins \<and> wt_start P C Ts mxl\<^isub>0 (\<Phi> C M)"
(*<*)
  apply (unfold wf_jvm_prog_phi_def)
  apply (drule (1) sees_wf_mdecl)
  apply (simp add: wf_mdecl_def wt_method_def)
  done
(*>*)

end
