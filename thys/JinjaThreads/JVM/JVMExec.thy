(*  Title:      JinjaThreads/JVM/JVMExec.thy
    Author:     Cornelia Pusch, Gerwin Klein, Andreas Lochbihler
*)

header {* \isaheader{Program Execution in the JVM} *}

theory JVMExec imports JVMExecInstr JVMExceptions begin

syntax instrs_of :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> instr list"
translations "instrs_of P C M" == "fst(snd(snd(snd(snd(snd(method P C M))))))"


-- "single step execution:"

fun exception_step :: "jvm_prog \<Rightarrow> jvm_ta_state \<Rightarrow> jvm_ta_state"
where
  "exception_step P (ta, \<lfloor>a\<rfloor>, h, (stk, loc, C, M, pc) # frs) = 
   (case match_ex_table P (cname_of h a) pc (ex_table_of P C M) of
          None \<Rightarrow> (ta, \<lfloor>a\<rfloor>, h, frs)
        | Some (pc', d) \<Rightarrow> (ta, None, h, (Addr a # drop (size stk - d) stk, loc, C, M, pc') # frs))"
| "exception_step P \<sigma> = \<sigma>"


lemma exception_step_def_raw:
  "exception_step = 
   (\<lambda>P (ta, xcp, h, frs).
    case frs of [] \<Rightarrow> (ta, xcp, h, [])
    | ((stk, loc, C, M, pc) # frs') \<Rightarrow> (case xcp of None \<Rightarrow> (ta, xcp, h, frs)
                                                   | \<lfloor>a\<rfloor> \<Rightarrow> (case match_ex_table P (cname_of h a) pc (ex_table_of P C M) of
                                                                 None \<Rightarrow> (ta, \<lfloor>a\<rfloor>, h, frs')
                                                      | Some (pc', d) \<Rightarrow> (ta, None, h, (Addr a # drop (size stk - d) stk, loc, C, M, pc') # frs'))))"
by(auto simp add: expand_fun_eq split: list.split)

fun exec :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> jvm_ta_state list" where
  "exec P (xcp, h, []) = []"
| "exec P (None, h, (stk, loc, C, M, pc) # frs) = exec_instr (instrs_of P C M ! pc) P h stk loc C M pc frs"
| "exec P (\<lfloor>a\<rfloor>, h, fr # frs) = [exception_step P (\<epsilon>, \<lfloor>a\<rfloor>, h, fr # frs)]"

lemma exec_not_empty:
  "exec P (xcp, h, f # frs) \<noteq> []"
by(cases f, cases xcp, auto intro: exec_instr_not_empty del: notI)



-- "relational view"
inductive
  exec_1 :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> jvm_thread_action \<Rightarrow> jvm_state \<Rightarrow> bool" ("_ \<turnstile>/ _ -_-jvm\<rightarrow>/ _" [61,61,0,61] 60)
  for P :: jvm_prog
where
  exec_1I:
  "(ta, \<sigma>') \<in> set (exec P \<sigma>) \<Longrightarrow> P \<turnstile> \<sigma> -ta-jvm\<rightarrow> \<sigma>'"

-- "reflexive transitive closure:"
definition
  exec_star :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) thread_action list \<Rightarrow> jvm_state \<Rightarrow> bool" ("_ \<turnstile>/ _ -_-jvm\<rightarrow>*/ _" [61,61,0,61] 60)
where
  "P \<turnstile> \<sigma> -tas-jvm\<rightarrow>* \<sigma>' \<equiv> rtrancl3p (exec_1 P) \<sigma> tas \<sigma>'"

lemma exec_1_iff:
  "P \<turnstile> \<sigma> -ta-jvm\<rightarrow> \<sigma>' \<longleftrightarrow> (ta, \<sigma>') \<in> set (exec P \<sigma>)"
by(auto intro: exec_1I elim: exec_1.cases)

lemma jvm_refl[iff]: "P \<turnstile> \<sigma> -[]-jvm\<rightarrow>* \<sigma>"
by(auto intro: rtrancl3p.intros simp add: exec_star_def)


lemma jvm_trans[trans]:
 "\<lbrakk> P \<turnstile> \<sigma> -tas-jvm\<rightarrow>* \<sigma>'; P \<turnstile> \<sigma>' -tas'-jvm\<rightarrow>* \<sigma>'' \<rbrakk> \<Longrightarrow> P \<turnstile> \<sigma> -tas@tas'-jvm\<rightarrow>* \<sigma>''"
  unfolding exec_star_def
  by(rule rtrancl3p_trans)

lemma jvm_one_step1[trans]:
 "\<lbrakk> P \<turnstile> \<sigma> -tas-jvm\<rightarrow> \<sigma>'; P \<turnstile> \<sigma>' -tas'-jvm\<rightarrow>* \<sigma>'' \<rbrakk> \<Longrightarrow> P \<turnstile> \<sigma> -tas#tas'-jvm\<rightarrow>* \<sigma>''"
  unfolding exec_star_def
  by(rule rtrancl3p_step_converse)

lemma jvm_one_step2[trans]:
 "\<lbrakk> P \<turnstile> \<sigma> -tas-jvm\<rightarrow>* \<sigma>'; P \<turnstile> \<sigma>' -tas'-jvm\<rightarrow> \<sigma>'' \<rbrakk> \<Longrightarrow> P \<turnstile> \<sigma> -tas@[tas']-jvm\<rightarrow>* \<sigma>''"
  unfolding exec_star_def
  by(rule rtrancl3p.rtrancl3p_step)

lemma exec_all_finalD: "P \<turnstile> (x, h, []) -tas-jvm\<rightarrow>* \<sigma> \<Longrightarrow> \<sigma> = (x, h, []) \<and> tas = []"
apply(simp only: exec_star_def)
apply(erule rtrancl3p_converseE)
apply(auto elim: exec_1.cases)
done


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
