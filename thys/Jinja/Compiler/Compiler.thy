(*  Title:      Jinja/Compiler/Compiler.thy
    ID:         $Id: Compiler.thy,v 1.2 2005-09-06 15:06:08 makarius Exp $
    Author:     Tobias Nipkow
    Copyright   TUM 2003
*)

header {* \isaheader{Combining Stages 1 and 2} *}

theory Compiler imports  Correctness1 Correctness2 begin

constdefs
  J2JVM :: "J_prog \<Rightarrow> jvm_prog"
  "J2JVM  \<equiv>  compP\<^isub>2 \<circ> compP\<^isub>1"

theorem comp_correct:
assumes wwf: "wwf_J_prog P"
and method: "P \<turnstile> C sees M:Ts\<rightarrow>T = (pns,body) in C"
and eval: "P \<turnstile> \<langle>body,(h,[this#pns [\<mapsto>] vs])\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle>"
and sizes: "size vs = size pns + 1"    "size rest = max_vars body"
shows "J2JVM P \<turnstile> (None,h,[([],vs@rest,C,M,0)]) -jvm\<rightarrow> (exception e',h',[])"
(*<*)
proof -
  let ?P\<^isub>1 = "compP\<^isub>1 P"
  have fv: "fv body \<subseteq> set (this#pns)"
    using wwf method by(auto dest!:sees_wf_mdecl simp:wf_mdecl_def)
  have init: "[this#pns [\<mapsto>] vs] \<subseteq>\<^sub>m [this#pns [\<mapsto>] vs@rest]"
    using sizes by simp
  have "?P\<^isub>1 \<turnstile> C sees M: Ts\<rightarrow>T = (compE\<^isub>1 (this#pns) body) in C"
    using sees_method_compP[OF method, of "\<lambda>(pns,e). compE\<^isub>1 (this#pns) e"]
    by(simp)
  moreover obtain ls' where
    "?P\<^isub>1 \<turnstile>\<^sub>1 \<langle>compE\<^isub>1 (this#pns) body, (h, vs@rest)\<rangle> \<Rightarrow> \<langle>fin\<^isub>1 e', (h',ls')\<rangle>"
    using eval\<^isub>1_eval[OF wwf eval fv init] sizes by auto
  ultimately show ?thesis using comp\<^isub>2_correct eval_final[OF eval]
    by(fastsimp simp add:J2JVM_def final_def)
qed
(*>*)


end
