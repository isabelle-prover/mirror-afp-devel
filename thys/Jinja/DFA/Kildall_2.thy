(*  Title:      HOL/MicroJava/BV/Kildall.thy
    Author:     Tobias Nipkow, Gerwin Klein
    Copyright   2000 TUM

Kildall's algorithm.
*)

section \<open>Kildall's Algorithm \label{sec:Kildall}\<close>

theory Kildall_2
imports SemilatAlg Kildall_1
begin



primrec propa :: "'s binop \<Rightarrow> (nat \<times> 's) list \<Rightarrow> 's list \<Rightarrow> nat set \<Rightarrow> 's list * nat set"
where
  "propa f []      \<tau>s w = (\<tau>s,w)"
| "propa f (q'#qs) \<tau>s w = (let (q,\<tau>) = q';
                             u = \<tau> \<squnion>\<^bsub>f\<^esub> \<tau>s!q;
                             w' = (if u = \<tau>s!q then w else insert q w)
                         in propa f qs (\<tau>s[q := u]) w')"

definition iter :: "'s binop \<Rightarrow> 's step_type \<Rightarrow>
          's list \<Rightarrow> nat set \<Rightarrow> 's list \<times> nat set"
where
  "iter f step \<tau>s w =
   while (\<lambda>(\<tau>s,w). w \<noteq> {})
         (\<lambda>(\<tau>s,w). let p = some_elem w
                   in propa f (step p (\<tau>s!p)) \<tau>s (w-{p}))
         (\<tau>s,w)"

definition unstables :: "'s ord \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> nat set"
where
  "unstables r step \<tau>s = {p. p < size \<tau>s \<and> \<not>stable r step \<tau>s p}"

definition kildall :: "'s ord \<Rightarrow> 's binop \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> 's list"
where
  "kildall r f step \<tau>s = fst(iter f step \<tau>s (unstables r step \<tau>s))"


(** propa **)
lemma (in Semilat) merges_incr_lemma:
  "\<forall>xs. xs \<in> nlists n A \<longrightarrow> (\<forall>(p,x)\<in>set ps. p<size xs \<and> x \<in> A) \<longrightarrow> xs [\<sqsubseteq>\<^bsub>r\<^esub>] merges f ps xs"
  apply (induct ps)
  apply auto[1]
  apply simp
  apply clarify
  apply (rule order_trans [OF _ list_update_incr])
         apply force
        apply simp+     
  done       

(*>*)

lemma (in Semilat) merges_incr:
 "\<lbrakk> xs \<in> nlists n A; \<forall>(p,x)\<in>set ps. p<size xs \<and> x \<in> A \<rbrakk> 
  \<Longrightarrow> xs [\<sqsubseteq>\<^bsub>r\<^esub>] merges f ps xs"
  by (simp add: merges_incr_lemma)


lemma (in Semilat) merges_same_conv [rule_format]:
 "(\<forall>xs. xs \<in> nlists n A \<longrightarrow> (\<forall>(p,x)\<in>set ps. p<size xs \<and> x\<in>A) \<longrightarrow> 
     (merges f ps xs = xs) = (\<forall>(p,x)\<in>set ps. x \<sqsubseteq>\<^bsub>r\<^esub> xs!p))"
(*<*)
  apply (induct_tac ps)
   apply simp
  apply clarsimp
  apply (rename_tac p x ps xs)
  apply (rule iffI)
   apply (rule context_conjI)
    apply (subgoal_tac "xs[p := x \<squnion>\<^bsub>f\<^esub> xs!p] [\<sqsubseteq>\<^bsub>r\<^esub>] xs")
     apply (fastforce dest!: le_listD)  \<comment>\<open>apply (force dest!: le_listD simp add: nth_list_update) \<close>
    apply (smt (verit, ccfv_threshold) case_prodD case_prodI2 closed_f merges_incr
      nlistsE_length nlistsE_nth_in nlists_update_in_list)
   apply clarify
  using le_iff_plus_unchanged apply fastforce
  apply (simp add: le_iff_plus_unchanged [THEN iffD1] list_update_same_conv [THEN iffD2])
  done
    (*>*)

lemma decomp_propa:
  "\<And>ss w. (\<forall>(q,t)\<in>set qs. q < size ss) \<Longrightarrow> 
   propa f qs ss w = 
   (merges f qs ss, {q. \<exists>t.(q,t)\<in>set qs \<and> t \<squnion>\<^bsub>f\<^esub> ss!q \<noteq> ss!q} \<union> w)"
(*<*)
  by (induct qs; fastforce simp add: nth_list_update)
(*>*)

lemma (in Semilat) stable_pres_lemma:
shows "\<lbrakk>pres_type step n A; bounded step n; 
     ss \<in> nlists n A; p \<in> w; \<forall>q\<in>w. q < n; 
     \<forall>q. q < n \<longrightarrow> q \<notin> w \<longrightarrow> stable r step ss q; q < n; 
     \<forall>s'. (q,s') \<in> set (step p (ss!p)) \<longrightarrow> s' \<squnion>\<^bsub>f\<^esub> ss!q = ss!q; 
     q \<notin> w \<or> q = p \<rbrakk> 
  \<Longrightarrow> stable r step (merges f (step p (ss!p)) ss) q"
(*<*)
  apply (unfold stable_def)
  apply (subgoal_tac "\<forall>s'. (q,s') \<in> set (step p (ss!p)) \<longrightarrow> s' : A")
   prefer 2
   apply (meson nlistsE_nth_in pres_typeD)
  apply simp
  apply clarify
  apply (subst nth_merges)
     apply simp
     apply (blast dest: boundedD)
    apply assumption
   apply clarify
  apply (metis boundedD nlistsE_nth_in pres_typeD)
  apply simp
  apply(subgoal_tac "q < length ss")
   prefer 2 apply simp
  apply (frule nth_merges [of q _ _ "step p (ss!p)"]) (* fixme: why does method subst not work?? *)
    apply assumption
   apply clarify
   apply (metis boundedD nlistsE_nth_in pres_typeD)
  apply (drule_tac P = "\<lambda>x. (a, b) \<in> set (step q x)" in subst)
   apply assumption

  apply (simp add: plusplus_empty)
  apply (cases "q \<in> w")
   apply simp
   apply (smt (verit, ccfv_SIG) Semilat_axioms bounded_def nlistsE_length nlistsE_set
      nth_in old.prod.case pres_type_def ub1')

  apply simp
  apply (erule allE, erule impE, assumption, erule impE, assumption) 
  apply (rule order_trans)    
       apply fastforce
      defer     
      apply (rule pp_ub2)
       apply simp        
       apply clarify
       apply simp
       apply (rule pres_typeD)
          apply assumption
         prefer 3 
         apply assumption
        apply (blast intro: nlistsE_nth_in)
       apply (blast)
      apply (blast intro: nlistsE_nth_in dest: boundedD)
     prefer 4
     apply fastforce     
    apply (blast intro: nlistsE_nth_in dest: pres_typeD)
   apply (blast intro: nlistsE_nth_in dest: boundedD)
  apply(subgoal_tac "\<forall>(q,t) \<in> set (step p (ss!p)). q < n \<and> t \<in> A")

   apply (subgoal_tac "merges f (step p (ss!p)) ss \<in> nlists n A")
    apply (metis (lifting) boundedD nlistsE_length nlistsE_set nth_in
      nth_merges)
   apply (blast dest:merges_preserves_type)
  by (smt (verit, best) boundedD case_prodI2 nlistsE_nth_in pres_typeD)
    (*>*)


lemma (in Semilat) merges_bounded_lemma:
 "\<lbrakk> mono r step n A; bounded step n; pres_type step n A; 
    \<forall>(p',s') \<in> set (step p (ss!p)). s' \<in> A; ss \<in> nlists n A; ts \<in> nlists n A; p < n; 
    ss [\<sqsubseteq>\<^sub>r] ts; \<forall>p. p < n \<longrightarrow> stable r step ts p \<rbrakk> 
  \<Longrightarrow> merges f (step p (ss!p)) ss [\<sqsubseteq>\<^sub>r] ts" 
(*<*)
  apply (unfold stable_def)
  apply (rule merges_pres_le_ub)
     apply simp
    apply simp
   prefer 2 apply assumption

  apply clarsimp
  apply (drule boundedD, assumption+)
  apply (erule allE, erule impE, assumption)
  apply (drule bspec, assumption)
  apply simp

  apply (drule monoD [of _ _ _ _ p "ss!p"  "ts!p"])
     apply assumption
    apply simp
   apply (simp add: le_listD)
  
  apply (drule lesub_step_typeD, assumption) 
  apply clarify
  apply (drule bspec, assumption)
  apply simp
  by (meson nlistsE_nth_in pres_typeD trans_r)
(*>*)



(** iter **)
lemma termination_lemma: assumes "Semilat A r f"
shows "\<lbrakk> ss \<in> nlists n A; \<forall>(q,t)\<in>set qs. q<n \<and> t\<in>A; p\<in>w \<rbrakk> \<Longrightarrow> 
      ss [\<sqsubset>\<^sub>r] merges f qs ss \<or> 
  merges f qs ss = ss \<and> {q. \<exists>t. (q,t)\<in>set qs \<and> t \<squnion>\<^bsub>f\<^esub> ss!q \<noteq> ss!q} \<union> (w-{p}) \<subset> w"
(*<*) (is "PROP ?P")
proof -
  interpret Semilat A r f by fact
  show "PROP ?P"
  apply(insert semilat)
    apply (unfold lesssub_def)
    apply (simp (no_asm_simp) add: merges_incr)
    apply (rule impI)
    apply (rule merges_same_conv [THEN iffD1, elim_format]) 
    apply assumption+
    apply fastforce
     apply force
     apply (subgoal_tac "\<forall>q t. \<not>((q, t) \<in> set qs \<and> t \<squnion>\<^bsub>f\<^esub> ss ! q \<noteq> ss ! q)")
     apply (blast intro!: psubsetI elim: equalityE)
    by fastforce
qed
(*>*)

end
