(*  Title:      JinjaThreads/JVM/JVMExceptions.thy
    Author:     Gerwin Klein, Martin Strecker, Andreas Lochbihler
*)

header {* \isaheader{Exception handling in the JVM} *}

theory JVMExceptions imports JVMInstructions "../Common/Exceptions" begin

constdefs
  matches_ex_entry :: "'m prog \<Rightarrow> cname \<Rightarrow> pc \<Rightarrow> ex_entry \<Rightarrow> bool"
 "matches_ex_entry P C pc xcp \<equiv>
                 let (s, e, C', h, d) = xcp in
                 s \<le> pc \<and> pc < e \<and> P \<turnstile> C \<preceq>\<^sup>* C'"


consts
  match_ex_table :: "'m prog \<Rightarrow> cname \<Rightarrow> pc \<Rightarrow> ex_table \<Rightarrow> (pc \<times> nat) option"
primrec
  "match_ex_table P C pc []     = None"
  "match_ex_table P C pc (e#es) = (if matches_ex_entry P C pc e
                                   then Some (snd(snd(snd e)))
                                   else match_ex_table P C pc es)"

consts
  ex_table_of :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> ex_table"
translations
  "ex_table_of P C M" == "snd (snd (snd (snd (snd (snd(method P C M))))))"

end
