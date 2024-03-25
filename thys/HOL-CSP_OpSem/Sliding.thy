(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_OpSem - Operational semantics for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff
 *
 * This file       : The Sliding operator
 *
 * Copyright (c) 2023 Université Paris-Saclay, France
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


chapter\<open> New Operators \<close>

text \<open>Three operators of CSP has not been defined yet in \<^session>\<open>HOL-CSP\<close> 
      (and not in \<^session>\<open>HOL-CSPM\<close> either): Sliding, Interrupt and Throw.
      Since they are mentioned by Roscoe \<^cite>\<open>"Roscoe2010UnderstandingCS"\<close> (and since 
      he provides operational laws for them too in \<^cite>\<open>"DBLP:journals/entcs/Roscoe15"\<close>), 
      it would  be a shame not to include them in our work.
      
      We will therefore define them now before moving on to the construction
      of our correspondence between semantics.\<close>


section\<open> The Sliding Operator (also called Timeout)\<close>

theory  Sliding
  imports "HOL-CSPM.CSPM"
begin


subsection \<open>Definition\<close>

definition Sliding :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> process \<Rightarrow> '\<alpha> process\<close> (infixl \<open>\<rhd>\<close> 78)
  where \<open>P \<rhd> Q \<equiv> (P \<box> Q) \<sqinter> Q\<close>

\<comment> \<open>See if we want to define a MultiSliding operator like MultiSeq.\<close>



subsection \<open>Projections\<close>

lemma F_Sliding:
  \<open>\<F> (P \<rhd> Q) = \<F> Q \<union> {(s, X). s \<noteq> [] \<and> (s, X) \<in> \<F> P \<or> 
                               s = [] \<and> (s \<in> \<D> P \<or> tick \<notin> X \<and> [tick] \<in> \<T> P)}\<close>
  by (auto simp add: Sliding_def F_Ndet F_Det NF_ND is_processT6_S2)

corollary \<open>\<F> (Mprefix A P \<rhd> Q) = \<F> Q \<union> {(s, X) \<in> \<F> (Mprefix A P). s \<noteq> []}\<close>
  by (auto simp add: F_Sliding)

lemma D_Sliding: \<open>\<D> (P \<rhd> Q) = \<D> P \<union> \<D> Q\<close>
  by (simp add: Sliding_def D_Ndet D_Det)

lemma T_Sliding: \<open>\<T> (P \<rhd> Q) = \<T> P \<union> \<T> Q\<close>
  by (simp add: Sliding_def T_Ndet T_Det)



subsection \<open>Monotony\<close>

lemma mono_right_Sliding_F: \<open>Q \<sqsubseteq>\<^sub>F Q' \<Longrightarrow> P \<rhd> Q \<sqsubseteq>\<^sub>F P \<rhd> Q'\<close>
  and mono_Sliding_D:  \<open>P \<sqsubseteq>\<^sub>D P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>D Q' \<Longrightarrow> P \<rhd> Q \<sqsubseteq>\<^sub>D P' \<rhd> Q'\<close>
  and mono_Sliding_T:  \<open>P \<sqsubseteq>\<^sub>T P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>T Q' \<Longrightarrow> P \<rhd> Q \<sqsubseteq>\<^sub>T P' \<rhd> Q'\<close>
  and mono_Sliding_FD: \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>F\<^sub>D Q' \<Longrightarrow> P \<rhd> Q \<sqsubseteq>\<^sub>F\<^sub>D P' \<rhd> Q'\<close>
  and mono_Sliding_DT: \<open>P \<sqsubseteq>\<^sub>D\<^sub>T P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>D\<^sub>T Q' \<Longrightarrow> P \<rhd> Q \<sqsubseteq>\<^sub>D\<^sub>T P' \<rhd> Q'\<close>
  by (simp add: failure_refine_def F_Sliding subset_iff)
     (simp_all add: Sliding_def)



subsection \<open>Properties\<close>

lemma Sliding_id: \<open>P \<rhd> P = P\<close>
  by (simp add: Det_id Ndet_id Sliding_def)

lemma STOP_Sliding: \<open>STOP \<rhd> P = P\<close>
  unfolding Sliding_def by (simp add: Det_commute Det_STOP Ndet_id)


text \<open>Of course, \<^term>\<open>P \<rhd> STOP \<noteq> STOP\<close> and \<^term>\<open>P \<rhd> STOP \<noteq> P\<close> in general.\<close>
lemma \<open>\<exists>P. P \<rhd> STOP \<noteq> STOP \<and> P \<rhd> STOP \<noteq> P\<close>
proof (intro exI)
  show \<open>SKIP \<rhd> STOP \<noteq> STOP \<and> SKIP \<rhd> STOP \<noteq> SKIP\<close>
    by (metis Det_STOP Ndet_commute SKIP_F_iff SKIP_Neq_STOP
            STOP_F_iff Sliding_def mono_Ndet_F_left)
qed
  

text \<open>But we still have this result.\<close>
lemma Sliding_is_STOP_iff: \<open>P \<rhd> Q = STOP \<longleftrightarrow> P = STOP \<and> Q = STOP\<close>
  by (auto simp add: STOP_iff_T T_Sliding intro: Nil_elem_T)


lemma Sliding_STOP_Det: \<open>(P \<rhd> STOP) \<box> Q = P \<rhd> Q\<close>
  by (simp add: Det_STOP Det_commute Det_distrib Sliding_def)


lemma BOT_Sliding: \<open>\<bottom> \<rhd> P = \<bottom>\<close>
  and Sliding_BOT: \<open>P \<rhd> \<bottom> = \<bottom>\<close>
  unfolding Sliding_def by (simp_all add: Det_commute Det_BOT Ndet_commute Ndet_BOT)

lemma Sliding_is_BOT_iff: \<open>P \<rhd> Q = \<bottom> \<longleftrightarrow> P = \<bottom> \<or> Q = \<bottom>\<close>
  by (simp add: Det_is_BOT_iff Ndet_is_BOT_iff Sliding_def)


lemma Sliding_assoc: \<open>P1 \<rhd> P2 \<rhd> P3 = P1 \<rhd> (P2 \<rhd> P3)\<close>
  by (metis Det_assoc Det_commute Det_distrib Ndet_assoc
            Ndet_commute Ndet_distrib Ndet_id Sliding_def)


lemma SKIP_Sliding: \<open>SKIP \<rhd> P = P \<sqinter> SKIP\<close>
  by (auto simp add: Sliding_def Process_eq_spec F_Ndet
                     F_Det T_SKIP D_Ndet D_Det F_SKIP D_SKIP NF_ND)

lemma Sliding_SKIP: \<open>P \<rhd> SKIP = P \<box> SKIP\<close> 
  by (auto simp add: Sliding_def Process_eq_spec F_Ndet
                     F_Det T_SKIP D_Ndet D_Det F_SKIP D_SKIP)


lemma Sliding_Det: \<open>(P \<rhd> P') \<box> Q = P \<rhd> P' \<box> Q\<close>
  by (metis Det_assoc Det_commute Det_distrib Sliding_def)


lemma Sliding_Ndet: \<open>(P \<sqinter> P') \<rhd> Q = (P \<rhd> Q) \<sqinter> (P' \<rhd> Q)\<close>
                    \<open>P \<rhd> (Q \<sqinter> Q') = (P \<rhd> Q) \<sqinter> (P \<rhd> Q')\<close>
  by (auto simp add: Process_eq_spec F_Ndet D_Ndet T_Ndet F_Sliding D_Sliding)
  

lemma Renaming_Sliding:
  \<open>Renaming (P \<rhd> Q) f = Renaming P f \<rhd> Renaming Q f\<close>
  by (simp add: Renaming_Det Renaming_Ndet Sliding_def)


lemma events_Sliding: \<open>events_of (P \<rhd> Q) = events_of P \<union> events_of Q\<close>
  unfolding Sliding_def by (simp add: events_of_def T_Det T_Ndet)



subsection \<open>Continuity\<close>

text \<open>From the definition, continuity is obvious.\<close>

lemma Sliding_cont[simp] : \<open>cont f \<Longrightarrow> cont g \<Longrightarrow> cont (\<lambda>x. f x \<rhd> g x)\<close>
  by (simp add: Sliding_def)


end