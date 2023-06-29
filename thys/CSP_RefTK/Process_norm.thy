(*<*)
\<comment>\<open> ********************************************************************
 * Project         : CSP-RefTK - A Refinement Toolkit for HOL-CSP
 * Version         : 1.0
 *
 * Author          : Burkhart Wolff, Safouan Taha, Lina Ye.
 *
 * This file       : A Normalization Theory
 *
 * Copyright (c) 2020 Université Paris-Saclay, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************\<close>
(*>*)

chapter\<open> Normalisation of Deterministic CSP Processes \<close>

theory Process_norm

imports "Properties" "HOL-CSP.Induction_ext"

begin

section\<open>Deterministic normal-forms with explicit state\<close>

abbreviation "P_dnorm \<tau> \<upsilon> \<equiv> (\<mu> X. (\<lambda> s. \<box> e \<in> (\<tau> s) \<rightarrow> X (\<upsilon> s e)))"

notation      P_dnorm ("P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>_,_\<rbrakk>" 60)

lemma dnorm_cont[simp]:
  fixes \<tau>::"'\<sigma>::type \<Rightarrow> 'event::type set" and \<upsilon>::"'\<sigma> \<Rightarrow> 'event \<Rightarrow> '\<sigma>"
  shows "cont (\<lambda>X. (\<lambda>s. \<box> e \<in> (\<tau> s) \<rightarrow> X (\<upsilon> s e)))" (is "cont ?f")
proof -
  have  "cont (\<lambda>X. ?f X s)" for s by (simp add:cont_fun) 
  then show ?thesis by simp
qed

section\<open>Interleaving product lemma\<close>

lemma dnorm_inter:  
  fixes \<tau>\<^sub>1 ::"'\<sigma>\<^sub>1::type \<Rightarrow> 'event::type set" and \<tau>\<^sub>2::"'\<sigma>\<^sub>2::type \<Rightarrow> 'event set" 
    and \<upsilon>\<^sub>1 ::"'\<sigma>\<^sub>1 \<Rightarrow> 'event \<Rightarrow> '\<sigma>\<^sub>1"          and \<upsilon>\<^sub>2::"'\<sigma>\<^sub>2 \<Rightarrow> 'event \<Rightarrow> '\<sigma>\<^sub>2"
  defines P: "P \<equiv> P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>\<tau>\<^sub>1,\<upsilon>\<^sub>1\<rbrakk>" (is "P \<equiv> fix\<cdot>(\<Lambda> X. ?P X)")
  defines Q: "Q \<equiv> P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>\<tau>\<^sub>2,\<upsilon>\<^sub>2\<rbrakk>" (is "Q \<equiv> fix\<cdot>(\<Lambda> X. ?Q X)")

  assumes indep: \<open>\<forall>s\<^sub>1 s\<^sub>2. \<tau>\<^sub>1 s\<^sub>1 \<inter> \<tau>\<^sub>2 s\<^sub>2 = {}\<close>

  defines Tr: "\<tau> \<equiv> (\<lambda>(s\<^sub>1,s\<^sub>2). \<tau>\<^sub>1 s\<^sub>1 \<union> \<tau>\<^sub>2 s\<^sub>2)"
  defines Up: "\<upsilon> \<equiv> (\<lambda>(s\<^sub>1,s\<^sub>2) e. if e \<in> \<tau>\<^sub>1 s\<^sub>1 then (\<upsilon>\<^sub>1 s\<^sub>1 e,s\<^sub>2)
                                else if e \<in> \<tau>\<^sub>2 s\<^sub>2 then (s\<^sub>1, \<upsilon>\<^sub>2 s\<^sub>2 e) else (s\<^sub>1,s\<^sub>2))"  
  defines S: "S \<equiv> P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>\<tau>,\<upsilon>\<rbrakk>" (is "S \<equiv> fix\<cdot>(\<Lambda> X. ?S X)")
  
  shows "(P s\<^sub>1 ||| Q s\<^sub>2) = S (s\<^sub>1,s\<^sub>2)"

proof -
  have P_rec: "P = ?P P" using fix_eq[of "(\<Lambda> X. ?P X)"] P by simp 
  have Q_rec: "Q = ?Q Q" using fix_eq[of "(\<Lambda> X. ?Q X)"] Q by simp 
  have S_rec: "S = ?S S" using fix_eq[of "(\<Lambda> X. ?S X)"] S by simp
  have dir1: "\<forall> s\<^sub>1 s\<^sub>2. (P s\<^sub>1 ||| Q s\<^sub>2) \<sqsubseteq>\<^sub>F\<^sub>D S (s\<^sub>1, s\<^sub>2)"
  proof(subst P, subst Q, 
        induct rule:parallel_fix_ind_inc[of "\<lambda>x y. \<forall> s\<^sub>1 s\<^sub>2. (x s\<^sub>1 ||| y s\<^sub>2) \<sqsubseteq>\<^sub>F\<^sub>D S (s\<^sub>1,s\<^sub>2)"])
    case admissibility
    then show ?case
        by (intro adm_all le_FD_adm) (simp_all add: cont2cont_fun monofunI)
  next
    case (base_fst y)
    then show ?case by (metis app_strict BOT_leFD Sync_BOT Sync_commute)
  next
    case (base_snd x)
    then show ?case by (simp add: Sync_BOT)
  next
    case (step x)
    then show ?case (is "\<forall> s\<^sub>1 s\<^sub>2. ?C s\<^sub>1 s\<^sub>2")
      proof(intro allI)
        fix s\<^sub>1 s\<^sub>2
        show "?C s\<^sub>1 s\<^sub>2"
          apply simp
          apply (subst Mprefix_Sync_distr_indep[where S = "{}", simplified])
          apply (subst S_rec, simp add: Tr Up Mprefix_Un_distrib)
          apply (intro mono_Det_FD mono_Mprefix_FD)
          using step(3)[simplified] indep apply simp
          using step(2)[simplified] indep by fastforce
      qed
    qed         
  have dir2: "\<forall> s\<^sub>1 s\<^sub>2.  S (s\<^sub>1, s\<^sub>2) \<sqsubseteq>\<^sub>F\<^sub>D (P s\<^sub>1 ||| Q s\<^sub>2)"
    proof(subst S, induct rule:fix_ind_k[of "\<lambda>x. \<forall> s\<^sub>1 s\<^sub>2. x (s\<^sub>1,s\<^sub>2) \<sqsubseteq>\<^sub>F\<^sub>D (P s\<^sub>1 ||| Q s\<^sub>2)" 1])
      case admissibility
      show ?case  by (intro adm_all le_FD_adm) (simp_all add: cont_fun monofunI) 
    next
      case base_k_steps
      then show ?case by simp
    next
      case step
      then show ?case (is "\<forall> s\<^sub>1 s\<^sub>2. ?C s\<^sub>1 s\<^sub>2")
      proof(intro allI)
        fix s\<^sub>1 s\<^sub>2
        have P_rec_sym:"Mprefix (\<tau>\<^sub>1 s\<^sub>1) (\<lambda>e. P (\<upsilon>\<^sub>1 s\<^sub>1 e)) = P s\<^sub>1" using P_rec by metis
        have Q_rec_sym:"Mprefix (\<tau>\<^sub>2 s\<^sub>2) (\<lambda>e. Q (\<upsilon>\<^sub>2 s\<^sub>2 e)) = Q s\<^sub>2" using Q_rec by metis
        show "?C s\<^sub>1 s\<^sub>2"
          apply (simp add: Tr Up Mprefix_Un_distrib)
          apply (subst P_rec, subst Q_rec, subst Mprefix_Sync_distr_indep[where S="{}", simplified])
          apply (intro mono_Det_FD mono_Mprefix_FD)
          apply (subst Q_rec_sym, simp add:step[simplified])
          apply (subst P_rec_sym) using step[simplified] indep by fastforce
      qed
    qed
  from dir1 dir2 show ?thesis using FD_antisym by blast
qed

section \<open>Synchronous product lemma\<close>

lemma dnorm_par:  
  fixes \<tau>\<^sub>1 ::"'\<sigma>\<^sub>1::type \<Rightarrow> 'event::type set" and \<tau>\<^sub>2::"'\<sigma>\<^sub>2::type \<Rightarrow> 'event set" 
    and \<upsilon>\<^sub>1 ::"'\<sigma>\<^sub>1 \<Rightarrow> 'event \<Rightarrow> '\<sigma>\<^sub>1"          and \<upsilon>\<^sub>2::"'\<sigma>\<^sub>2 \<Rightarrow> 'event \<Rightarrow> '\<sigma>\<^sub>2"
  defines P: "P \<equiv> P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>\<tau>\<^sub>1,\<upsilon>\<^sub>1\<rbrakk>" (is "P \<equiv> fix\<cdot>(\<Lambda> X. ?P X)")
  defines Q: "Q \<equiv> P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>\<tau>\<^sub>2,\<upsilon>\<^sub>2\<rbrakk>" (is "Q \<equiv> fix\<cdot>(\<Lambda> X. ?Q X)")

  defines Tr: "\<tau> \<equiv> (\<lambda>(s\<^sub>1,s\<^sub>2).  \<tau>\<^sub>1 s\<^sub>1 \<inter> \<tau>\<^sub>2 s\<^sub>2)"
  defines Up: "\<upsilon> \<equiv> (\<lambda>(s\<^sub>1,s\<^sub>2) e. (\<upsilon>\<^sub>1 s\<^sub>1 e, \<upsilon>\<^sub>2 s\<^sub>2 e))"  
  defines S: "S \<equiv> P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>\<tau>,\<upsilon>\<rbrakk>" (is "S \<equiv> fix\<cdot>(\<Lambda> X. ?S X)")
  
  shows "(P s\<^sub>1 || Q s\<^sub>2) = S (s\<^sub>1,s\<^sub>2)"

proof -
  have P_rec: "P = ?P P" using fix_eq[of "(\<Lambda> X. ?P X)"] P by simp 
  have Q_rec: "Q = ?Q Q" using fix_eq[of "(\<Lambda> X. ?Q X)"] Q by simp 
  have S_rec: "S = ?S S" using fix_eq[of "(\<Lambda> X. ?S X)"] S by simp
  have dir1: "\<forall> s\<^sub>1 s\<^sub>2. (P s\<^sub>1 || Q s\<^sub>2) \<sqsubseteq>\<^sub>F\<^sub>D S (s\<^sub>1, s\<^sub>2)"
  proof(subst P, subst Q, 
        induct rule:parallel_fix_ind[of "\<lambda>x y. \<forall> s\<^sub>1 s\<^sub>2. (x s\<^sub>1 || y s\<^sub>2) \<sqsubseteq>\<^sub>F\<^sub>D S (s\<^sub>1,s\<^sub>2)"])
      case adm:1
      then show ?case
        by (intro adm_all le_FD_adm) (simp_all add: cont2cont_fun monofunI)
    next
      case base:2
      then show ?case by (simp add: Sync_BOT)
    next
      case step:(3 x y)
      then show ?case (is "\<forall> s\<^sub>1 s\<^sub>2. ?C s\<^sub>1 s\<^sub>2")
      proof(intro allI)
        fix s\<^sub>1 s\<^sub>2
        show "?C s\<^sub>1 s\<^sub>2"
          apply(simp)
          apply(subst Mprefix_Sync_distr_subset[where S="UNIV", simplified])
          apply(subst S_rec, simp add: Tr Up Mprefix_Un_distrib)
          by (simp add: step)
      qed
    qed     
  have dir2: "\<forall> s\<^sub>1 s\<^sub>2.  S (s\<^sub>1, s\<^sub>2) \<sqsubseteq>\<^sub>F\<^sub>D (P s\<^sub>1 || Q s\<^sub>2)"
    proof(subst S, induct rule:fix_ind_k[of "\<lambda>x. \<forall> s\<^sub>1 s\<^sub>2. x (s\<^sub>1,s\<^sub>2) \<sqsubseteq>\<^sub>F\<^sub>D (P s\<^sub>1 || Q s\<^sub>2)" 1])
      case admissibility
      show ?case  by (intro adm_all le_FD_adm) (simp_all add: cont_fun monofunI) 
    next
      case base_k_steps
      then show ?case by simp
    next
      case step
      then show ?case (is "\<forall> s\<^sub>1 s\<^sub>2. ?C s\<^sub>1 s\<^sub>2")
      proof(intro allI)
        fix s\<^sub>1 s\<^sub>2
        have P_rec_sym:"Mprefix (\<tau>\<^sub>1 s\<^sub>1) (\<lambda>e. P (\<upsilon>\<^sub>1 s\<^sub>1 e)) = P s\<^sub>1" using P_rec by metis
        have Q_rec_sym:"Mprefix (\<tau>\<^sub>2 s\<^sub>2) (\<lambda>e. Q (\<upsilon>\<^sub>2 s\<^sub>2 e)) = Q s\<^sub>2" using Q_rec by metis
        show "?C s\<^sub>1 s\<^sub>2"
          apply(simp add: Tr Up)
          apply(subst P_rec, subst Q_rec, subst Mprefix_Sync_distr_subset[where S="UNIV", simplified])
          apply(rule mono_Mprefix_FD) 
          using step by auto
      qed
    qed
  from dir1 dir2 show ?thesis using FD_antisym by blast
qed

section\<open>Consequences\<close>

\<comment>\<open>reachable states from one starting state\<close>

inductive_set \<RR> for     \<tau>  ::"'\<sigma>::type \<Rightarrow> 'event::type set"
                    and \<upsilon>  ::"'\<sigma> \<Rightarrow> 'event \<Rightarrow> '\<sigma>" 
                    and \<sigma>\<^sub>0 ::'\<sigma> 
  where rbase: "\<sigma>\<^sub>0 \<in> \<RR> \<tau> \<upsilon> \<sigma>\<^sub>0"
      | rstep: "s \<in> \<RR> \<tau> \<upsilon> \<sigma>\<^sub>0 \<Longrightarrow> e \<in> \<tau> s  \<Longrightarrow> \<upsilon> s e \<in> \<RR> \<tau> \<upsilon> \<sigma>\<^sub>0"



\<comment>\<open>Deadlock freeness\<close>
lemma deadlock_free_dnorm_ :
  fixes \<tau> ::"'\<sigma>::type \<Rightarrow> 'event::type set" 
    and \<upsilon> ::"'\<sigma> \<Rightarrow> 'event \<Rightarrow> '\<sigma>" 
    and \<sigma>\<^sub>0 ::'\<sigma> 
  assumes non_reachable_sink: "\<forall>s \<in> \<RR> \<tau> \<upsilon> \<sigma>\<^sub>0. \<tau> s \<noteq> {}"
  defines P: "P \<equiv> P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>\<tau>,\<upsilon>\<rbrakk>" (is "P \<equiv> fix\<cdot>(\<Lambda> X. ?P X)")
  shows  "s \<in> \<RR> \<tau> \<upsilon> \<sigma>\<^sub>0 \<Longrightarrow> deadlock_free_v2 (P s)"
proof(unfold deadlock_free_v2_FD DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def, induct arbitrary:s rule:fix_ind)
  show "adm (\<lambda>a. \<forall>x. x \<in> \<RR> \<tau> \<upsilon> \<sigma>\<^sub>0 \<longrightarrow> a \<sqsubseteq>\<^sub>F\<^sub>D P x)" by (simp add: monofun_def) 
next
  fix s :: "'\<sigma>" 
  show "s \<in> \<RR> \<tau> \<upsilon> \<sigma>\<^sub>0 \<Longrightarrow> \<bottom> \<sqsubseteq>\<^sub>F\<^sub>D P s" by simp
next
  fix s :: "'\<sigma>"  and x :: "'event process"
  have P_rec: "P = ?P P" using fix_eq[of "(\<Lambda> X. ?P X)"] P by simp 
  assume 1 : "\<And>s. s \<in> \<RR> \<tau> \<upsilon> \<sigma>\<^sub>0 \<Longrightarrow> x \<sqsubseteq>\<^sub>F\<^sub>D P s" 
   and   2 : "s \<in> \<RR> \<tau> \<upsilon> \<sigma>\<^sub>0 "
  from   1 2 show "(\<Lambda> x. (\<sqinter>xa\<in>UNIV \<rightarrow>  x) \<sqinter> SKIP)\<cdot>x \<sqsubseteq>\<^sub>F\<^sub>D P s"
    apply (subst P_rec, rule_tac trans_FD[rotated, OF Mprefix_refines_Mndetprefix_FD])
    apply simp
    apply (rule mono_Ndet_FD_left)
    apply (rule trans_FD[OF mono_Mndetprefix_FD_set[of \<open>\<tau> s\<close> \<open>UNIV\<close>]
                            mono_Mndetprefix_FD[rule_format, OF 1]])
    using non_reachable_sink[rule_format, OF 2] apply assumption
    by blast (meson \<RR>.rstep)
qed



lemmas deadlock_free_dnorm = deadlock_free_dnorm_[rotated, OF rbase, rule_format]

end

