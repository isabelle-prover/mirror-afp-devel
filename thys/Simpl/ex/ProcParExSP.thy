(*  Title:      ProcParEx.thy
    Author:     Norbert Schirmer, TU Muenchen

Copyright (C) 2007-2008 Norbert Schirmer 
Some rights reserved, TU Muenchen

This library is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as
published by the Free Software Foundation; either version 2.1 of the
License, or (at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
USA
*)

header "Examples for Procedures as Parameters using Statespaces"
theory ProcParExSP imports "../Vcg" begin


lemma DynProcProcPar':
 assumes adapt: "P \<subseteq> {s. p s = q \<and>
         (\<exists>Z. init s \<in> P' Z \<and>
              (\<forall>t \<in> Q' Z. return s t \<in> R s t) \<and>
              (\<forall>t \<in> A' Z. return s t \<in> A))}"
 assumes result: "\<forall>s t. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>(R s t) result s t Q,A" 
 assumes q: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>(P' Z) Call q (Q' Z),(A' Z)"
 shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P dynCall init p return result Q,A"
apply (rule DynProcProcPar [OF _ result q])
apply (insert adapt)
apply fast
done




lemma conseq_exploit_pre':
             "\<lbrakk>\<forall>s \<in> S. \<Gamma>,\<Theta> \<turnstile> ({s} \<inter> P) c Q,A\<rbrakk>
              \<Longrightarrow>
              \<Gamma>,\<Theta>\<turnstile> (P \<inter> S)c Q,A"
  apply (rule Conseq)
  apply clarify
  apply (rule_tac x="{s} \<inter> P" in exI)  
  apply (rule_tac x="Q" in exI)  
  apply (rule_tac x="A" in exI)  
  by simp


lemma conseq_exploit_pre'':
             "\<lbrakk>\<forall>Z. \<forall>s \<in> S Z.  \<Gamma>,\<Theta> \<turnstile> ({s} \<inter> P Z) c (Q Z),(A Z)\<rbrakk>
              \<Longrightarrow>
              \<forall>Z. \<Gamma>,\<Theta>\<turnstile> (P Z \<inter> S Z)c (Q Z),(A Z)"
  apply (rule allI)
  apply (rule conseq_exploit_pre')
  apply blast
  done

lemma conseq_exploit_pre''':
             "\<lbrakk>\<forall>s \<in> S. \<forall>Z. \<Gamma>,\<Theta> \<turnstile> ({s} \<inter> P Z) c (Q Z),(A Z)\<rbrakk>
              \<Longrightarrow>
              \<forall>Z. \<Gamma>,\<Theta>\<turnstile> (P Z \<inter> S)c (Q Z),(A Z)"
  apply (rule allI)
  apply (rule conseq_exploit_pre')
  apply blast
  done


procedures compare(i::nat,j::nat|r::bool) "NoBody"
  

print_locale! compare_signature


context compare_impl
begin
ML "HoareSyntax.use_call_tr' := false"
term "\<acute>r :== CALL compare(\<acute>i,\<acute>j)"
ML "HoareSyntax.use_call_tr' := true"
end



procedures
  LEQ (i::nat,j::nat | r::bool) "\<acute>r :== \<acute>i \<le> \<acute>j"
  LEQ_spec: "\<forall>\<sigma>. \<Gamma>\<turnstile> {\<sigma>}  PROC LEQ(\<acute>i,\<acute>j,\<acute>r) \<lbrace>\<acute>r = (\<^bsup>\<sigma>\<^esup>i \<le> \<^bsup>\<sigma>\<^esup>j)\<rbrace>"
  LEQ_modifies: "\<forall>\<sigma>. \<Gamma>\<turnstile> {\<sigma>} PROC LEQ(\<acute>i,\<acute>j,\<acute>r) {t. t may_only_modify_globals \<sigma> in []}"



constdefs mx:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
"mx leq a b \<equiv> if leq a b then a else b"

ML "Toplevel.debug := false"
procedures (imports compare_signature)
  Max (compare::string, n::nat, m::nat | k::nat)  
  where b::bool
  in
  "\<acute>b :== DYNCALL \<acute>compare(\<acute>n,\<acute>m);;
   IF \<acute>b THEN \<acute>k :== \<acute>n ELSE \<acute>k :== \<acute>m FI"

  Max_spec: "\<And>leq. \<forall>\<sigma>. \<Gamma>\<turnstile> 
  ({\<sigma>} \<inter> {s. (\<forall>\<tau>. \<Gamma>\<turnstile> {\<tau>} \<acute>r :== PROC \<^bsup>s\<^esup>compare(\<acute>i,\<acute>j) \<lbrace>\<acute>r = (leq \<^bsup>\<tau>\<^esup>i \<^bsup>\<tau>\<^esup>j)\<rbrace>) \<and> 
              (\<forall>\<tau>. \<Gamma>\<turnstile> {\<tau>} \<acute>r :== PROC \<^bsup>s\<^esup>compare(\<acute>i,\<acute>j) {t. t may_only_modify_globals \<tau> in []})})
    PROC Max(\<acute>compare,\<acute>n,\<acute>m,\<acute>k)
  \<lbrace>\<acute>k = mx leq \<^bsup>\<sigma>\<^esup>n \<^bsup>\<sigma>\<^esup>m\<rbrace>"

context Max_spec
begin
thm Max_spec
end
context Max_impl
begin
term "\<acute>b :== DYNCALL \<acute>compare(\<acute>n,\<acute>m)"
ML "HoareSyntax.use_call_tr' := false"
term "\<acute>b :== DYNCALL \<acute>compare(\<acute>n,\<acute>m)"
ML "HoareSyntax.use_call_tr' := true"
end



lemma (in Max_impl ) Max_spec: 
shows
"\<forall>\<sigma> leq. \<Gamma>\<turnstile> 
  ({\<sigma>} \<inter> \<lbrace> (\<forall>\<tau>. \<Gamma>\<turnstile>{\<tau>} \<acute>r :== PROC \<acute>compare(\<acute>i,\<acute>j) \<lbrace>\<acute>r = (leq \<^bsup>\<tau>\<^esup>i \<^bsup>\<tau>\<^esup>j)\<rbrace>) \<and> 
      (\<forall>\<tau>. \<Gamma>\<turnstile> {\<tau>} \<acute>r :== PROC \<acute>compare(\<acute>i,\<acute>j) {t. t may_only_modify_globals \<tau> in []})\<rbrace>)
    \<acute>k :== PROC Max(\<acute>compare,\<acute>n,\<acute>m)
  \<lbrace>\<acute>k = mx leq \<^bsup>\<sigma>\<^esup>n \<^bsup>\<sigma>\<^esup>m\<rbrace>"
apply (hoare_rule ProcNoRec1)
apply (intro allI)
apply (rule conseq_exploit_pre')
apply (rule)
apply clarify
proof -
  fix \<sigma>:: "('a, 'b, 'c, 'd) stateSP_scheme" and s::"('a, 'b, 'c, 'd) stateSP_scheme" and leq
   assume compare_spec: 
       "\<forall>\<tau>. \<Gamma>\<turnstile>{\<tau>} \<acute>r :== PROC \<^bsup>s\<^esup>compare(\<acute>i,\<acute>j) \<lbrace>\<acute>r = leq \<^bsup>\<tau>\<^esup>i \<^bsup>\<tau>\<^esup>j\<rbrace>"
 
  assume compare_modifies:
        "\<forall>\<tau>. \<Gamma>\<turnstile>{\<tau>} \<acute>r :== PROC \<^bsup>s\<^esup>compare(\<acute>i,\<acute>j) 
                {t. t may_only_modify_globals \<tau> in []}"

   show "\<Gamma>\<turnstile>({s} \<inter> {\<sigma>})
            \<acute>b :== DYNCALL \<acute>compare (\<acute>n,\<acute>m);;
            IF \<acute>b THEN \<acute>k :== \<acute>n ELSE \<acute>k :== \<acute>m FI
            \<lbrace>\<acute>k = mx leq \<^bsup>\<sigma>\<^esup>n \<^bsup>\<sigma>\<^esup>m\<rbrace>"
     apply vcg     
     apply (clarsimp simp add: mx_def)
     done
 qed


lemma (in Max_impl) Max_spec: 
shows
"\<forall>\<sigma> leq. \<Gamma>\<turnstile> 
  ({\<sigma>} \<inter> \<lbrace>(\<forall>\<tau>. \<Gamma>\<turnstile> {\<tau>} \<acute>r :== PROC \<acute>compare(\<acute>i,\<acute>j) \<lbrace>\<acute>r = (leq \<^bsup>\<tau>\<^esup>i \<^bsup>\<tau>\<^esup>j)\<rbrace>) \<and> 
      (\<forall>\<tau>. \<Gamma>\<turnstile> {\<tau>} \<acute>r :== PROC \<acute>compare(\<acute>i,\<acute>j) {t. t may_only_modify_globals \<tau> in []})\<rbrace>)
    \<acute>k :== PROC Max(\<acute>compare,\<acute>n,\<acute>m)
  \<lbrace>\<acute>k = mx leq \<^bsup>\<sigma>\<^esup>n \<^bsup>\<sigma>\<^esup>m\<rbrace>"
apply (hoare_rule ProcNoRec1)
apply (intro allI)
apply (rule conseq_exploit_pre')
apply (rule)
apply clarify
apply vcg
apply (clarsimp simp add: mx_def)
done

lemma (in Max_impl) Max_spec: 
shows
"\<forall>n m leq. \<Gamma>\<turnstile> 
  (\<lbrace>\<acute>n=n \<and> \<acute>m=m\<rbrace>  \<inter> 
   \<lbrace>(\<forall>\<tau>. \<Gamma>\<turnstile> {\<tau>} \<acute>r :== PROC \<acute>compare(\<acute>i,\<acute>j) \<lbrace>\<acute>r = (leq \<^bsup>\<tau>\<^esup>i \<^bsup>\<tau>\<^esup>j)\<rbrace>) \<and> 
     (\<forall>\<tau>. \<Gamma>\<turnstile> {\<tau>} \<acute>r :== PROC \<acute>compare(\<acute>i,\<acute>j) {t. t may_only_modify_globals \<tau> in []})\<rbrace>)
    \<acute>k :== PROC Max(\<acute>compare,\<acute>n,\<acute>m)
  \<lbrace>\<acute>k = mx leq n m\<rbrace>"
apply (hoare_rule ProcNoRec1)
apply (intro allI)
apply (rule conseq_exploit_pre')
apply (rule)
apply clarify
apply vcg
apply (clarsimp simp add: mx_def)
done

lemma (in Max_impl) Max_spec: 
shows
"\<forall>n m leq. \<Gamma>\<turnstile> 
  (\<lbrace>\<acute>n=n \<and> \<acute>m=m\<rbrace> \<inter> \<lbrace>\<forall>\<tau>. \<Gamma>\<turnstile> {\<tau>} \<acute>r :== PROC \<acute>compare(\<acute>i,\<acute>j) \<lbrace>\<acute>r = (leq \<^bsup>\<tau>\<^esup>i \<^bsup>\<tau>\<^esup>j)\<rbrace>\<rbrace>)
    \<acute>k :== PROC Max(\<acute>compare,\<acute>n,\<acute>m)
  \<lbrace>\<acute>k = mx leq n m\<rbrace>"
apply (hoare_rule ProcNoRec1)
apply (intro allI)
apply (rule conseq_exploit_pre')
apply (rule)
apply clarify
apply vcg
apply (clarsimp simp add: mx_def)
done

print_locale Max_spec

(* We have to rename the parameters of the compare procedure to match the LEQ procedure *)
locale Max_test = Max_spec \<Gamma> compare_'Max_' n_'Max_' m_'Max_' k_'Max_' project_nat
        inject_nat project_List_char_List_list inject_List_char_List_list StateType
        Max_'proc i_'LEQ_' j_'LEQ_' r_'LEQ_' project_bool
        inject_bool compare_'proc
       + LEQ_spec + LEQ_modifies

lemma (in Max_test) 
  shows
  "\<Gamma>\<turnstile> {\<sigma>} \<acute>k :== CALL Max(LEQ_'proc,\<acute>n,\<acute>m) \<lbrace>\<acute>k = mx (op \<le>) \<^bsup>\<sigma>\<^esup>n \<^bsup>\<sigma>\<^esup>m\<rbrace>"
proof -
  thm Max_spec
  note Max_spec = Max_spec [where leq="(op \<le>)"]
  show ?thesis
    ML "Toplevel.debug := true"
    apply vcg
    apply (clarsimp)
    apply (rule conjI)
    apply (rule LEQ_spec)
    apply (rule LEQ_modifies)
    done
qed






lemma (in Max_impl) Max_spec:
shows
"\<forall>n m leq. \<Gamma>\<turnstile> 
  (\<lbrace>\<acute>n=n \<and> \<acute>m=m\<rbrace> \<inter> \<lbrace>\<forall>n' m'. \<Gamma>\<turnstile> \<lbrace>\<acute>i=n' \<and> \<acute>j=m'\<rbrace> \<acute>r :== PROC \<acute>compare(\<acute>i,\<acute>j) \<lbrace>\<acute>r = (leq n' m')\<rbrace>\<rbrace>)
    \<acute>k :== PROC Max(\<acute>compare,\<acute>n,\<acute>m)
  \<lbrace>\<acute>k = mx leq n m\<rbrace>"
term "\<lbrace>{s. \<^bsup>s\<^esup>n = n' \<and> \<^bsup>s\<^esup>m = m'} = X\<rbrace>"
apply (hoare_rule ProcNoRec1)
apply (intro allI)
apply (rule conseq_exploit_pre')
apply (rule)
apply clarify
apply vcg
apply clarsimp
apply (clarsimp simp add: mx_def)
done

lemma (in LEQ_impl)
 LEQ_spec: "\<forall>n m. \<Gamma>\<turnstile> \<lbrace>\<acute>i=n \<and> \<acute>j=m\<rbrace>  PROC LEQ(\<acute>i,\<acute>j,\<acute>r) \<lbrace>\<acute>r = (n \<le> m)\<rbrace>"
  apply vcg
  apply simp
  done


print_locale Max_impl
locale Max_test' = Max_impl \<Gamma> compare_'Max_' n_'Max_' m_'Max_' k_'Max_' b_'Max_' project_nat
        inject_nat project_bool inject_bool
        project_List_char_List_list inject_List_char_List_list StateType
        i_'LEQ_' j_'LEQ_' r_'LEQ_' compare_'proc Max_'proc + LEQ_impl
lemma (in Max_test') 
  shows
  "\<forall>n m. \<Gamma>\<turnstile> \<lbrace>\<acute>n=n \<and> \<acute>m=m\<rbrace> \<acute>k :== CALL Max(LEQ_'proc,\<acute>n,\<acute>m) \<lbrace>\<acute>k = mx (op \<le>) n m\<rbrace>"
apply vcg
apply (rule_tac x="op \<le>" in exI)
apply clarsimp
apply (rule LEQ_spec [rule_format])
done

end




