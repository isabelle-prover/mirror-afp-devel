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

chapter\<open> Annex: A Note on a Classical Example: The ``Merge Anomaly''\<close>

theory MergeAnomaly
  imports "HOL-CSP"
begin

text\<open>Manfred Broy proposed in his 'Habilitationsschrift' (\<^footnote>\<open>Published in 
``A Theory for Nondeterminism, Parallelism, Communication, and Concurrency. TCS (1986)''\<close>) 
a stream processing language \<open>AMPL\<close>, which is in many respect similar to \<^theory>\<open>HOL-CSP\<close>. 
Unfortunately, the underlying Powerset-construction contained a error that made it possible 
that in an interleaving between a stream \<open>1\<^sup>\<infinity>\<close> and a stream \<open>1.0\<^sup>\<infinity>\<close> a \<open>0\<close> can get ahead of the
leading \<open>1\<close> which contradicts the intuition that interleaving should preserve causality in 
both inputs.

Since we believe in the importance of a \<^emph>\<open>formally verified\<close>  semantics of a language for 
concurrency, we take this anecdotical reference to the Merge-Anomaly as an example to 
study in the process algebra  \<^theory>\<open>HOL-CSP\<close>, so in a setting with trace, failure and 
failure/divergence semantics.

First, we define the three processes corresponding to the notation \<open>1\<^sup>\<infinity>\<close>, \<open>0\<^sup>\<infinity>\<close> and \<open>1.0\<^sup>\<infinity>\<close>:
\<close>

definition ones      :: "nat process" where \<open>ones =  (\<mu> X. 1 \<rightarrow> X)\<close>
definition zeros     :: "nat process" where \<open>zeros = (\<mu> X. 0 \<rightarrow> X)\<close>
definition oneszeros :: "nat process" where \<open>oneszeros = (\<mu> X. \<box>x\<in>{0,1} \<rightarrow> X)\<close>

text\<open>... and derive the more handy recursive stream-equations:\<close>

lemma ones_rec: "ones =  1 \<rightarrow> ones"  by (subst cont_process_rec[OF ones_def]) simp_all

lemma zeros_rec: "zeros =  0 \<rightarrow> zeros" by (subst cont_process_rec[OF zeros_def]) simp_all

lemma oneszeros_rec: "oneszeros = \<box>x\<in>{0,1} \<rightarrow> oneszeros" 
      by (subst cont_process_rec[OF oneszeros_def]) simp_all

text\<open>Now, we can establish that \<open>ones ||| zeros\<close> and \<open>oneszeros\<close> are indeed equal
in the failure/divergence semantics in  \<^theory>\<open>HOL-CSP\<close>. This is formally proven as follows: \<close>

lemma ones_Inter_zeros_eq_oneszeros : \<open>ones ||| zeros = oneszeros\<close>
proof (rule FD_antisym)
  show \<open>oneszeros \<sqsubseteq>\<^sub>F\<^sub>D ones ||| zeros\<close>
  proof (unfold oneszeros_def, induct rule: cont_fix_ind)
    fix X assume \<open>X \<sqsubseteq>\<^sub>F\<^sub>D ones ||| zeros\<close>
    have \<open>ones ||| zeros = (1 \<rightarrow> (ones ||| 0 \<rightarrow> zeros)) \<box> (0 \<rightarrow> (1 \<rightarrow> ones ||| zeros))\<close>
      by (subst ones_rec, subst zeros_rec) (simp add: write0_Inter_write0)
    also have \<open>\<dots> = (1 \<rightarrow> (ones ||| zeros)) \<box> (0 \<rightarrow> (ones ||| zeros))\<close>
      by (simp del: One_nat_def flip: ones_rec zeros_rec)
    also have \<open>\<dots> = \<box>a\<in>{0, 1} \<rightarrow> (ones ||| zeros)\<close>
      by (metis Mprefix_Un_distrib Mprefix_singl Un_insert_right sup_bot.right_neutral)
    also have \<open>\<box>a\<in>{0, 1} \<rightarrow> X \<sqsubseteq>\<^sub>F\<^sub>D \<dots>\<close>
      by (simp add: \<open>X \<sqsubseteq>\<^sub>F\<^sub>D ones ||| zeros\<close> mono_Mprefix_FD)
    finally show \<open>\<box>a\<in>{0, 1} \<rightarrow> X \<sqsubseteq>\<^sub>F\<^sub>D ones ||| zeros\<close> .
  qed simp_all
next
  show \<open>ones ||| zeros \<sqsubseteq>\<^sub>F\<^sub>D oneszeros\<close>
    \<comment> \<open>With stronger theoretical footprint, this could be skipped since \<^const>\<open>oneszeros\<close>
        is a deterministic process (therefore maximal for \<^term>\<open>(\<sqsubseteq>\<^sub>F\<^sub>D)\<close>).\<close>
  proof (unfold ones_def zeros_def, induct rule: parallel_fix_ind_inc)
    fix X Y
    assume hyps : \<open>(\<Lambda> X. 1 \<rightarrow> X)\<cdot>X ||| Y \<sqsubseteq>\<^sub>F\<^sub>D oneszeros\<close> 
                  \<open>X ||| (\<Lambda> Y. 0 \<rightarrow> Y)\<cdot>Y \<sqsubseteq>\<^sub>F\<^sub>D oneszeros\<close>
    have \<open>(\<Lambda> X. 1 \<rightarrow> X)\<cdot>X ||| (\<Lambda> Y. 0 \<rightarrow> Y)\<cdot>Y = (1 \<rightarrow> X) ||| (0 \<rightarrow> Y)\<close> by simp
    also have \<open>\<dots> = (1 \<rightarrow> (X ||| 0 \<rightarrow> Y)) \<box> (0 \<rightarrow> (1 \<rightarrow> X ||| Y))\<close>
      by (simp add: write0_Inter_write0)
    also have \<open>\<dots> = \<box>a \<in> {0, 1} \<rightarrow> (if a = 0 then 1 \<rightarrow> X ||| Y else X ||| 0 \<rightarrow> Y)\<close>
      by (auto simp add: write0_def Mprefix_Det_Mprefix intro: mono_Mprefix_eq)
    also have \<open>\<dots> \<sqsubseteq>\<^sub>F\<^sub>D oneszeros\<close>
      by (subst oneszeros_rec)
        (use hyps in \<open>auto intro: mono_Mprefix_FD\<close>)
    finally show \<open>(\<Lambda> X. 1 \<rightarrow> X)\<cdot>X ||| (\<Lambda> Y. 0 \<rightarrow> Y)\<cdot>Y \<sqsubseteq>\<^sub>F\<^sub>D oneszeros\<close> .
  qed simp_all
qed

text\<open>As a consequence, in the trace model, we can establish that there will be no ``Anomaly''
in \<^theory>\<open>HOL-CSP\<close>, so \<open>ones ||| (1 \<rightarrow> zeros)\<close> will be equal to \<open>1 \<rightarrow> oneszeros\<close> in the
originally intended trace-projection. The proof proceeds indirectly over induction over the traces; 
This is the recommended proof strategy if arguments over trace sets have to be established. In 
contrast, an argument over the \<^term>\<open>lfp\<close>-operator, which seems natural at first sight, is amazingly 
complicated. We have:\<close>

lemma \<open>\<T> (ones ||| (1 \<rightarrow> zeros)) = \<T> (1 \<rightarrow> oneszeros)\<close> (is \<open>?lhs = ?rhs\<close>)
proof (rule set_eqI)
  show \<open>t \<in> ?lhs \<longleftrightarrow> t \<in> ?rhs\<close> for t
  proof (induct t)
    case Nil show ?case by simp
  next
    case (Cons e t)
    show ?case
    proof (rule iffI)
      assume \<open>e # t \<in> \<T> (1 \<rightarrow> oneszeros)\<close>
      hence \<open>e = ev 1\<close> \<open>t \<in> \<T> oneszeros\<close>
        by (simp_all add: T_write0)
      thus \<open>e # t \<in> \<T> (ones ||| 1 \<rightarrow> zeros)\<close>
        apply (subst ones_rec)
        apply (simp del: One_nat_def add: write0_Inter_write0 T_Det T_write0)
        apply (fold ones_rec ones_Inter_zeros_eq_oneszeros)
        ..
    next
      show \<open>e # t \<in> \<T> (ones ||| 1 \<rightarrow> zeros) \<Longrightarrow> e # t \<in> \<T> (1 \<rightarrow> oneszeros)\<close>
        apply (subst (asm) ones_rec)
        apply (simp del: One_nat_def add: write0_Inter_write0 T_Det T_write0)
        apply (fold ones_rec)
        apply (unfold Cons.hyps)
        apply (unfold ones_Inter_zeros_eq_oneszeros)
        apply (subst (asm) (2) oneszeros_rec, subst oneszeros_rec)
        by (auto simp add: T_Mprefix T_write0)
    qed
  qed
qed


text\<open>However, \<open>ones ||| (1 \<rightarrow> zeros)\<close> will be \<^emph>\<open>not\<close> equal to \<open>1 \<rightarrow> oneszeros\<close> in the failure
model and therefore not in the failure/divergence model. The deeper reason is the interleave
operator \<^emph>\<open>can neither refuse\<close> \<open>0\<close> or \<open>1\<close>; it is designed to be sensitive to the process 
context and let pass any possible interleaving admitted by the context which is reflected 
in the rule @{thm Read_Write_CSP_Laws.write0_Inter_write0}.\<close>


lemma \<open>ones ||| (1 \<rightarrow> zeros) \<noteq> 1 \<rightarrow> oneszeros\<close> (is \<open>?P1 \<noteq> ?P2\<close>) 
proof -
  have \<open>([ev 1], {ev 0}) \<notin> \<F> ?P2\<close>
    by (subst oneszeros_rec)
      (simp add: Process_eq_spec F_write0 F_Mprefix)
  moreover have \<open>([ev 1], {ev 0}) \<in> \<F> ?P1\<close>
    by (subst ones_rec, subst ones_rec)
      (simp add: write0_Inter_write0 Process_eq_spec F_Det F_write0)
  ultimately show \<open>?P1 \<noteq> ?P2\<close> by metis
qed

text\<open>One might ask what happens if we would have defined the process \<^const>\<open>oneszeros\<close> via the
non-deterministic choice, so using the following definition:\<close>

definition oneszeros' :: "nat process" where \<open>oneszeros' = (\<mu> X. \<sqinter>x\<in>{0,1} \<rightarrow> X)\<close>

lemma oneszeros'_rec : \<open>oneszeros' = \<sqinter>x \<in> {0, 1} \<rightarrow> oneszeros'\<close>
  by (subst cont_process_rec[OF oneszeros'_def]) simp_all

text\<open>But this means that already the first step in the above argument breaks down:
Since interleaving \<^emph>\<open>can neither refuse\<close> \<open>0\<close> or \<open>1\<close>, while the deterministic choice of
\<^const>\<open>oneszeros'\<close> does, we can easily show:\<close>

lemma \<open>ones ||| zeros \<noteq> oneszeros'\<close>
proof (rule notI)
  assume \<open>ones ||| zeros = oneszeros'\<close>
  with ones_Inter_zeros_eq_oneszeros have \<open>oneszeros' = oneszeros\<close> by metis
  moreover have \<open>([], {ev 0}) \<in> \<F> oneszeros'\<close>
    by (subst oneszeros'_rec)
      (simp add: F_Mndetprefix')
  moreover have \<open>([], {ev 0}) \<notin> \<F> oneszeros\<close>
    by (subst oneszeros_rec) (simp add: F_Mprefix)
  ultimately show False by simp
qed



end
