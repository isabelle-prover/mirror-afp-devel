(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in  Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : Example of Copy Buffer
 *
 * Copyright (c) 2009 Université Paris-Sud, France
 * Copyright (c) 2025 Université Paris-Saclay, France
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

chapter\<open> Annex: Refinement Example with Buffer over infinite Alphabet\<close>

(*<*)
theory     CopyBuffer 
  imports   CSP
begin 
  (*>*)

section\<open> Defining the Copy-Buffer Example \<close>


datatype 'a channel = left 'a | right 'a | mid 'a | ack

definition SYN  :: "'a channel set"
  where     "SYN  \<equiv> range mid \<union> {ack}"

definition COPY :: "'a channel process"
  where     "COPY \<equiv> \<mu> COPY. left\<^bold>?x \<rightarrow> right\<^bold>!x \<rightarrow> COPY"

definition SEND :: "'a channel process"
  where     "SEND \<equiv> \<mu> SEND. left\<^bold>?x \<rightarrow> mid\<^bold>!x \<rightarrow> ack \<rightarrow> SEND"

definition REC  :: "'a channel process"
  where     "REC  \<equiv> \<mu> REC. mid\<^bold>?x \<rightarrow> right\<^bold>!x \<rightarrow> ack \<rightarrow> REC"


definition SYSTEM :: "'a channel process"
  where     \<open>SYSTEM \<equiv> SEND \<lbrakk> SYN \<rbrakk> REC \ SYN\<close>

thm SYSTEM_def

section\<open> The Standard Proof \<close>

subsection\<open> Channels and Synchronization Sets\<close>

text\<open> First part: abstract properties for these events to SYN.
       This kind of stuff could be automated easily by some
       extra-syntax for channels and SYN-sets. \<close>

lemma simplification_lemmas [simp] :
  \<open>range left \<inter> SYN = {}\<close>
  \<open>range right \<inter> SYN = {}\<close>
  \<open>ack \<in> SYN\<close>
  \<open>range mid \<subseteq> SYN\<close>
  \<open>mid x \<in> SYN\<close>
  \<open>right x \<notin> SYN\<close>
  \<open>left x \<notin> SYN\<close>
  \<open>inj mid\<close>
  by (auto simp: SYN_def inj_on_def)

lemma "finite (SYN:: 'a channel set) \<Longrightarrow> finite {(t::'a). True}"
  by (metis (no_types) SYN_def UNIV_def channel.inject(3) finite_Un finite_imageD inj_on_def)

subsection\<open> Definitions by Recursors \<close>

text\<open> Second part: Derive recursive process equations, which
       are easier to handle in proofs. This part IS actually
       automated if we could reuse the fixrec-syntax below. \<close>

lemma COPY_rec:
  "COPY = left\<^bold>?x \<rightarrow> right\<^bold>!x \<rightarrow> COPY"
  by(simp add: COPY_def,rule trans, rule fix_eq, simp)

lemma SEND_rec: 
  "SEND = left\<^bold>?x \<rightarrow> mid\<^bold>!x \<rightarrow> ack \<rightarrow> SEND"
  by(simp add: SEND_def,rule trans, rule fix_eq, simp)

lemma REC_rec:
  "REC = mid\<^bold>?x \<rightarrow> right\<^bold>!x \<rightarrow> ack \<rightarrow> REC"
  by(simp add: REC_def,rule trans, rule fix_eq, simp)


subsection\<open> Various Samples of Refinement Proofs \<close>


(* ************************************************************************* *)
(* 	                                                    								     *)
(* Setup for rewriting							                                         *)
(* 									                                                        *)
(* ************************************************************************* *)

lemmas Sync_rules = read_Sync_read_subset_forced_read_same_chan
  read_Sync_read_left read_Sync_read_right
  write_Sync_read_left write_Sync_read_right
  read_Sync_write_left read_Sync_write_right
  write_Sync_write_subset
  write_Sync_read_subset read_Sync_write_subset

write0_Sync_write_right write0_Sync_write0

lemmas Hiding_rules = Hiding_read_disjoint Hiding_write_subset Hiding_write_disjoint
  Hiding_write0_non_disjoint Hiding_write0_disjoint

lemmas mono_rules = mono_read_FD mono_write_FD mono_write0_FD



text\<open>An example for a very explicit structured proof. 
     Slow-motion for presentations. Note that the proof makes
     no assumption over the structure of the content of the channel;
     it is truly polymorphic wrt. the channel type \<^typ>\<open>'\<alpha>\<close>.\<close>

lemma impl_refines_spec' : "(COPY :: 'a channel process) \<sqsubseteq>\<^sub>F\<^sub>D SYSTEM"
  unfolding  SYSTEM_def COPY_def
proof (rule fix_ind)
  show "adm (\<lambda>a. a \<sqsubseteq>\<^sub>F\<^sub>D (SEND \<lbrakk>SYN\<rbrakk> REC \\ SYN))" 
    by (simp add: cont2mono)
next 
  show "\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D (SEND \<lbrakk>SYN\<rbrakk> REC \\ SYN)"
    by simp
next
  fix x :: "'a channel process"
  assume hyp : "x \<sqsubseteq>\<^sub>F\<^sub>D (SEND \<lbrakk>SYN\<rbrakk> REC \\ SYN)"
  show "(\<Lambda> x. left\<^bold>?xa \<rightarrow> right\<^bold>!xa \<rightarrow> x)\<cdot>x \<sqsubseteq>\<^sub>F\<^sub>D (SEND \<lbrakk>SYN\<rbrakk> REC \\ SYN)"
    apply (subst SEND_rec, subst REC_rec)
    apply (simp add: cont_fun)
  proof - 
    have      "   left\<^bold>?x \<rightarrow> mid\<^bold>!x \<rightarrow> ack \<rightarrow> SEND \<lbrakk>SYN\<rbrakk> mid\<^bold>?x \<rightarrow> right\<^bold>!x \<rightarrow> ack \<rightarrow> REC \\ SYN 
                   =  left\<^bold>?x \<rightarrow> (mid\<^bold>!x \<rightarrow> ack \<rightarrow> SEND \<lbrakk>SYN\<rbrakk> mid\<^bold>?x \<rightarrow> right\<^bold>!x \<rightarrow> ack \<rightarrow> REC \\ SYN) " 
      (is "?lhs = _")
      by (simp add: Sync_rules Hiding_rules)
    also have " ... =  left\<^bold>?x \<rightarrow> (mid\<^bold>!x \<rightarrow> (ack \<rightarrow> SEND \<lbrakk>SYN\<rbrakk> right\<^bold>!x \<rightarrow> ack \<rightarrow> REC) \\ SYN)"
      by (simp add: Sync_rules Hiding_rules)
    also have " ... = left\<^bold>?x \<rightarrow> (ack \<rightarrow> SEND \<lbrakk>SYN\<rbrakk> right\<^bold>!x \<rightarrow> ack \<rightarrow> REC) \\ SYN"
      by (simp add: Sync_rules Hiding_rules)
    also have " ... = left\<^bold>?x \<rightarrow> right\<^bold>!x \<rightarrow> (ack \<rightarrow> SEND \<lbrakk>SYN\<rbrakk>  ack \<rightarrow> REC) \\ SYN"
      by (simp add: Sync_rules Hiding_rules )
    also  have " ...  = left\<^bold>?x \<rightarrow> right\<^bold>!x \<rightarrow> (SEND \<lbrakk>SYN\<rbrakk> REC \\ SYN)"  (is "_ = ?rhs")
      by (simp add: Sync_rules Hiding_rules) 
    finally have * :  "?lhs = ?rhs" .
    show "    left\<^bold>?xa \<rightarrow> right\<^bold>!xa \<rightarrow> x  \<sqsubseteq>\<^sub>F\<^sub>D ?lhs"
      by (simp only : "*" mono_read_FD mono_write_FD hyp)
  qed
qed



text\<open>An example for a highly automated proof.\<close>
text\<open>Not too bad in automation considering what is inferred, but wouldn't scale for large examples. \<close>


lemma impl_refines_spec : "COPY \<sqsubseteq>\<^sub>F\<^sub>D SYSTEM"
  unfolding SYSTEM_def COPY_def
  apply(rule fix_ind, auto intro: le_FD_adm simp:  cont_fun monofunI)
  apply(subst SEND_rec, subst REC_rec)
  apply (simp add: Sync_rules Hiding_rules mono_read_FD mono_write_FD) (*  write0_Sync_write0 write_is_write0 *)
  oops


lemma spec_refines_impl : 
  assumes fin: "finite (SYN:: 'a channel set)"
  shows        "SYSTEM \<sqsubseteq>\<^sub>F\<^sub>D (COPY :: 'a channel process)"
  apply(simp add: SYSTEM_def SEND_def)
  apply(rule fix_ind, simp_all)
   apply (intro le_FD_adm)
    apply (simp add: fin)
   apply (simp add: cont2mono)
  apply (simp add: Sync_commute)
  apply (subst COPY_rec, subst REC_rec)
  apply (simp add: read_def write_def comp_def)
  apply (subst Mprefix_Sync_Mprefix_right) apply auto[2]
  apply (simp add: Sync_rules Hiding_rules comp_def)
  apply (subst Hiding_Mprefix_disjoint) apply auto[1]
  apply (intro mono_Mprefix_FD ballI)
  apply (subst Mprefix_Sync_Mprefix_subset) apply auto[2]
  apply (subst Hiding_Mprefix_non_disjoint) apply auto[1]
  apply simp
  apply (fold write0_def)
  by (simp add: Hiding_write0_disjoint Hiding_write0_non_disjoint Sync_commute mono_write0_FD write0_Sync_write0)



text\<open> Note that this was actually proven for the
       Process ordering, not the refinement ordering. 
       But the former implies the latter.
       And due to anti-symmetry, equality follows
       for the case of finite alphabets \ldots \<close>

lemma spec_equal_impl : 
  assumes fin:  "finite (SYN::('a channel)set)"
  shows         "SYSTEM = (COPY::'a channel process)"
  by (simp add: FD_antisym fin impl_refines_spec' spec_refines_impl)

subsection\<open>Deadlock Freeness Proof \<close>

text\<open>HOL-CSP can be used to prove deadlock-freeness of processes with infinite alphabet. In the
case of the @{term COPY} - process, this can be formulated as the following refinement problem:\<close>

lemma DF_COPY : "(DF (range left \<union> range right)) \<sqsubseteq>\<^sub>F\<^sub>D COPY"
  apply(simp add:DF_def,rule fix_ind2)
proof -
  show "adm (\<lambda>a. a \<sqsubseteq>\<^sub>F\<^sub>D COPY)"   by(rule le_FD_adm, simp_all add: monofunI)
next
  show "\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D COPY" by fastforce
next
  have 1: "(\<sqinter>xa\<in> (range left \<union> range right) \<rightarrow> \<bottom>) \<sqsubseteq>\<^sub>F\<^sub>D (\<sqinter>xa\<in> range left \<rightarrow>  \<bottom>)"
    by (simp add: Mndetprefix_FD_subset)
  have 2: "(\<sqinter>xa\<in> range left \<rightarrow>  \<bottom>)  \<sqsubseteq>\<^sub>F\<^sub>D (left\<^bold>?x \<rightarrow>  \<bottom>)" 
    unfolding read_def
    by (meson Mndetprefix_FD_Mprefix BOT_leFD mono_Mndetprefix_FD trans_FD)
  show "(\<Lambda> x. \<sqinter>xa\<in>(range left \<union> range right) \<rightarrow>  x)\<cdot>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D COPY" 
    by simp (metis (mono_tags, lifting) 1 2 COPY_rec mono_read_FD BOT_leFD trans_FD)
next
  fix P::"'a channel process"
  assume  *: "P \<sqsubseteq>\<^sub>F\<^sub>D COPY" and ** : "(\<Lambda> x. \<sqinter>xa\<in>(range left \<union> range right) \<rightarrow>  x)\<cdot>P \<sqsubseteq>\<^sub>F\<^sub>D COPY"
  have 1:"\<sqinter>xa\<in> (range left \<union> range right) \<rightarrow>  P \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>xa\<in> range right \<rightarrow>  P"
    by (simp add: Mndetprefix_FD_subset)
  have 2:"\<sqinter>xa\<in> range right \<rightarrow>  P \<sqsubseteq>\<^sub>F\<^sub>D right\<^bold>!x \<rightarrow>  P" for x
    apply (unfold write_def, rule trans_FD[OF Mndetprefix_FD_subset[of \<open>{right x}\<close> \<open>range right\<close>]])
    by (simp_all add: Mndetprefix_FD_Mprefix Mprefix_singl)
  from 1 2 have ab:"\<sqinter>xa\<in> (range left \<union> range right) \<rightarrow>  P \<sqsubseteq>\<^sub>F\<^sub>D right\<^bold>!x \<rightarrow>  P" for x
    using trans_FD by blast
  hence 3:"left\<^bold>?x \<rightarrow> \<sqinter>xa\<in> (range left \<union> range right) \<rightarrow>  P \<sqsubseteq>\<^sub>F\<^sub>D left\<^bold>?x \<rightarrow> right\<^bold>!x \<rightarrow>  P"
    by (simp add: mono_read_FD)
  have 4:"\<And>X. \<sqinter>xa\<in> (range left \<union> range right) \<rightarrow> X \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>xa\<in> range left \<rightarrow> X"
    by (rule Mndetprefix_FD_subset, simp, blast) 
  have 5:"\<And>X. \<sqinter>xa\<in> range left \<rightarrow> X \<sqsubseteq>\<^sub>F\<^sub>D left\<^bold>?x \<rightarrow> X"
    by (unfold read_def, subst K_record_comp, fact Mndetprefix_FD_Mprefix)
  from 3 4[of "\<sqinter>xa\<in> (range left \<union> range right) \<rightarrow>  P"] 
    5  [of "\<sqinter>xa\<in> (range left \<union> range right) \<rightarrow>  P"] 
  have 6:"\<sqinter>xa\<in> (range left \<union> range right) \<rightarrow> 
                  \<sqinter>xa\<in> (range left \<union> range right) \<rightarrow>  P \<sqsubseteq>\<^sub>F\<^sub>D left\<^bold>?x \<rightarrow> right\<^bold>!x \<rightarrow>  P"
    using trans_FD by blast
  from * ** have 7:"left\<^bold>?x \<rightarrow> right\<^bold>!x \<rightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D left\<^bold>?x \<rightarrow> right\<^bold>!x \<rightarrow> COPY"
    by (simp add: mono_read_FD mono_write_FD)

  show "(\<Lambda> x. \<sqinter>xa\<in>(range left \<union> range right) \<rightarrow>  x)\<cdot>
             ((\<Lambda> x. \<sqinter>xa\<in>(range left \<union> range right) \<rightarrow>  x)\<cdot>P) \<sqsubseteq>\<^sub>F\<^sub>D COPY"
    by simp (metis (mono_tags, lifting) "6" "7" COPY_rec trans_FD)
qed

section\<open> An Alternative Approach: Using the fixrec-Package \<close>

subsection\<open> Channels and Synchronisation Sets \<close>

text\<open> As before. \<close>

subsection\<open> Process Definitions via fixrec-Package  \<close>

fixrec
  COPY' :: "'a channel process"
  and
  SEND' :: "'a channel process"
  and
  REC' :: "'a channel process"
  where
    COPY'_rec[simp del]:  "COPY' = left\<^bold>?x \<rightarrow> right\<^bold>!x \<rightarrow> COPY'"
  |  SEND'_rec[simp del]:  "SEND' = left\<^bold>?x \<rightarrow> mid\<^bold>!x \<rightarrow> ack \<rightarrow> SEND'"
  |  REC'_rec[simp del] :  "REC'  = mid\<^bold>?x  \<rightarrow> right\<^bold>!x \<rightarrow> ack \<rightarrow> REC'"

thm COPY'_rec
definition SYSTEM' :: "'a channel process"
  where     \<open>SYSTEM' \<equiv> ((SEND' \<lbrakk> SYN \<rbrakk> REC') \ SYN)\<close>

subsection\<open> Another Refinement Proof on fixrec-infrastructure \<close>

text\<open> Third part: No comes the proof by fixpoint induction. 
       Not too bad in automation considering what is inferred,
       but wouldn't scale for large examples. \<close>
thm COPY'_SEND'_REC'.induct
lemma impl_refines_spec'' : "(COPY'::'a channel process) \<sqsubseteq>\<^sub>F\<^sub>D SYSTEM'"
  apply (unfold SYSTEM'_def)
  apply (rule_tac P=\<open>\<lambda> a b c. a \<sqsubseteq>\<^sub>F\<^sub>D ((SEND' \<lbrakk>SYN\<rbrakk> REC') \ SYN)\<close> in COPY'_SEND'_REC'.induct)
    apply (subst case_prod_beta')+
    apply (intro le_FD_adm, simp_all add: monofunI)
  apply (subst SEND'_rec, subst REC'_rec)
  by (simp add: Sync_rules Hiding_rules mono_read_FD mono_write_FD)

lemma spec_refines_impl' : 
  assumes fin:  "finite (SYN::'a channel set)"
  shows         "SYSTEM' \<sqsubseteq>\<^sub>F\<^sub>D (COPY'::'a channel process)"
proof(unfold SYSTEM'_def, rule_tac P=\<open>\<lambda> a b c. ((b \<lbrakk>SYN\<rbrakk> REC') \ SYN) \<sqsubseteq>\<^sub>F\<^sub>D COPY'\<close> 
    in  COPY'_SEND'_REC'.induct, goal_cases)
  case 1
  have aa:\<open>adm (\<lambda>(a::'a channel process). ((a \<lbrakk>SYN\<rbrakk> REC') \ SYN) \<sqsubseteq>\<^sub>F\<^sub>D COPY')\<close>
    apply (intro le_FD_adm)
    by (simp_all add: fin cont2mono)
  thus ?case using adm_subst[of "\<lambda>(a,b,c). b", simplified, OF aa] by (simp add: split_def)
next
  case 2
  then show ?case by (simp add: Sync_commute)
next
  case (3 a aa b)
  then show ?case 
    by (subst COPY'_rec, subst REC'_rec)
      (simp add: Sync_rules Hiding_rules mono_read_FD mono_write_FD)
qed

lemma spec_equal_impl' : 
  assumes fin:  "finite (SYN::('a channel)set)"
  shows         "SYSTEM' = (COPY'::'a channel process)"
  apply (rule FD_antisym)
   apply (rule spec_refines_impl'[OF fin])
  apply (rule impl_refines_spec'')
  done


(*<*)
end
  (*>*)
