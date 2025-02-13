(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_OpSem - Operational semantics for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff
 *
 * This file       : Comparison with the work of He and Hoare:
 *                   From algebra to operational semantics
 *
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

chapter \<open> Comparison with He and Hoare \<close>

(*<*)
theory  Comparison_He_Hoare
  imports Operational_Semantics_Laws "HOL-Library.LaTeXsugar"
begin
  (*>*)


lemma (in After) initial_ev_imp_eq_prefix_After_Sliding :
  \<open>P = (e \<rightarrow> (P after e)) \<rhd> P\<close> if \<open>ev e \<in> P\<^sup>0\<close>
proof (subst Process_eq_spec, safe)
  show \<open>(s, X) \<in> \<F> P \<Longrightarrow> (s, X) \<in> \<F> ((e \<rightarrow> (P after e)) \<rhd> P)\<close> for s X
    by (simp add: F_Sliding)
next
  show \<open>(s, X) \<in> \<F> ((e \<rightarrow> (P after e)) \<rhd> P) \<Longrightarrow> (s, X) \<in> \<F> P\<close> for s X
    by (cases s) (auto simp add: F_Sliding write0_def F_Mprefix F_After \<open>ev e \<in> P\<^sup>0\<close>)
next
  show \<open>s \<in> \<D> P \<Longrightarrow> s \<in> \<D> ((e \<rightarrow> (P after e)) \<rhd> P)\<close> for s
    by (simp add: D_Sliding)
next
  show \<open>s \<in> \<D> ((e \<rightarrow> (P after e)) \<rhd> P) \<Longrightarrow> s \<in> \<D> P\<close> for s
    by (cases s) (auto simp add: D_Sliding write0_def D_Mprefix D_After \<open>ev e \<in> P\<^sup>0\<close>)
qed



context OpSemTransitions
begin

(* not really useful since we need an additional assumption
   to establish something like FD @{thm FD_iff_eq_Ndet} *)

(* lemma \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<longleftrightarrow> P = P \<sqinter> Q\<close> by (fact FD_iff_eq_Ndet) *)

abbreviation \<tau>_eq :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infix \<open>=\<^sub>\<tau>\<close> 50)
  where \<open>P =\<^sub>\<tau> Q \<equiv> P \<leadsto>\<^sub>\<tau> Q \<and> Q \<leadsto>\<^sub>\<tau> P\<close>

lemma \<tau>_eqI  : \<open>P \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> Q \<leadsto>\<^sub>\<tau> P \<Longrightarrow> P =\<^sub>\<tau> Q\<close>
  and \<tau>_eqD1 : \<open>P =\<^sub>\<tau>  Q \<Longrightarrow> P \<leadsto>\<^sub>\<tau> Q\<close>
  and \<tau>_eqD2 : \<open>P =\<^sub>\<tau>  Q \<Longrightarrow> Q \<leadsto>\<^sub>\<tau> P\<close>
  by simp_all

lemma \<tau>_trans_iff_\<tau>_eq_Ndet:
  \<open>\<forall>P Q P' Q'. P \<leadsto>\<^sub>\<tau> P' \<longrightarrow> Q \<leadsto>\<^sub>\<tau> Q' \<longrightarrow> P \<sqinter> Q \<leadsto>\<^sub>\<tau> P' \<sqinter> Q' \<Longrightarrow> P \<leadsto>\<^sub>\<tau> Q \<longleftrightarrow> P =\<^sub>\<tau> P \<sqinter> Q\<close>
  by (metis Ndet_id \<tau>_trans_NdetL \<tau>_trans_NdetR \<tau>_trans_transitivity)

lemma eq_imp_\<tau>_eq: \<open>P = Q \<Longrightarrow> P =\<^sub>\<tau> Q\<close> by (simp add: \<tau>_trans_eq)



definition ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> 'a \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close> (\<open>_ \<^bsub>HOARE\<^esub>\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
  where \<open>P \<^bsub>HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> Q \<equiv> P \<leadsto>\<^sub>\<tau> (e \<rightarrow> Q) \<box> P\<close>


lemma ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_imp_in_initials:
  \<open>P \<^bsub>HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> Q \<Longrightarrow> ev e \<in> P\<^sup>0\<close>
  using \<tau>_trans_ev_trans ev_trans_DetL ev_trans_prefix unfolding ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_def by blast


lemma ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_imp_ev_trans: \<open>P \<leadsto>\<^bsub>e\<^esub> Q\<close> if \<open>P \<^bsub>HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> Q\<close>
proof (rule conjI)
  from \<open>P \<^bsub>HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> Q\<close> show \<open>ev e \<in> P\<^sup>0\<close> by (fact ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_imp_in_initials)

  from \<open>P \<^bsub>HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> Q\<close>[unfolded ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_def]
  have \<open>P after\<^sub>\<checkmark> ev e \<leadsto>\<^sub>\<tau> ((e \<rightarrow> Q) \<box> P) after\<^sub>\<checkmark> ev e\<close>
    by (rule \<tau>_trans_mono_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k[rotated]) (simp add: initials_Det initials_write0)
  moreover have \<open>\<dots> = Q \<sqinter> (P after\<^sub>\<checkmark> ev e)\<close>
    by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Det \<open>ev e \<in> P\<^sup>0\<close> initials_write0 After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0)
  moreover have \<open>\<dots> \<leadsto>\<^sub>\<tau> Q\<close> by (fact \<tau>_trans_NdetL)
  ultimately show \<open>P after\<^sub>\<checkmark> ev e \<leadsto>\<^sub>\<tau> Q\<close>
    using \<open>ev e \<in> P\<^sup>0\<close> ev_trans_\<tau>_trans by presburger
qed



text \<open>Two assumptions on \<open>\<tau>\<close> transitions are necessary in the following proof, but are automatic
      when we instantiate \<^term>\<open>(\<leadsto>\<^sub>\<tau>)\<close> with \<^term>\<open>(\<sqsubseteq>\<^sub>F\<^sub>D)\<close>, \<^term>\<open>(\<sqsubseteq>\<^sub>D\<^sub>T)\<close>, \<^term>\<open>(\<sqsubseteq>\<^sub>F)\<close> or \<^term>\<open>(\<sqsubseteq>\<^sub>T)\<close>.\<close>

lemma hyps_on_\<tau>_trans_imp_ev_trans_imp_ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E: \<open>P \<^bsub>HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> Q\<close>
  if non_BOT_\<tau>_trans_DetL : \<open>\<forall>P P' Q. P = \<bottom> \<or> P' \<noteq> \<bottom> \<longrightarrow> P \<leadsto>\<^sub>\<tau> P' \<longrightarrow> P \<box> Q \<leadsto>\<^sub>\<tau> P' \<box> Q\<close>
    and \<tau>_trans_prefix      : \<open>\<forall>P P' e. P \<leadsto>\<^sub>\<tau> P' \<longrightarrow> (e \<rightarrow> P) \<leadsto>\<^sub>\<tau> (e \<rightarrow> P')\<close>
    and \<open>P \<leadsto>\<^bsub>e\<^esub> Q\<close>
proof (unfold ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_def)
  show \<open>P \<leadsto>\<^sub>\<tau> (e \<rightarrow> Q) \<box> P\<close>
  proof (rule \<tau>_trans_transitivity)
    have \<open>P = (e \<rightarrow> (P after e)) \<rhd> P\<close>
      by (simp add: initial_ev_imp_eq_prefix_After_Sliding \<open>P \<leadsto>\<^bsub>e\<^esub> Q\<close>)
    also have \<open>(e \<rightarrow> (P after e)) \<rhd> P \<leadsto>\<^sub>\<tau> (e \<rightarrow> (P after e)) \<box> P\<close>
      by (simp add: Sliding_def \<tau>_trans_NdetL)
    finally show \<open>P \<leadsto>\<^sub>\<tau> (e \<rightarrow> (P after e)) \<box> P\<close> .
  next
    show \<open>(e \<rightarrow> (P after e)) \<box> P \<leadsto>\<^sub>\<tau> (e \<rightarrow> Q) \<box> P\<close>
      by (rule non_BOT_\<tau>_trans_DetL[rule_format],
          solves \<open>simp add: write0_def\<close>)
        (rule \<tau>_trans_prefix[rule_format],
          fact \<open>P \<leadsto>\<^bsub>e\<^esub> Q\<close>[simplified ev_trans_is, THEN conjunct2])
  qed
qed


\<comment>\<open>Of course, we obtain an equivalence.\<close>
lemma hyps_on_\<tau>_trans_imp_ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_iff_ev_trans:
  \<open>\<forall>P P' Q. P = \<bottom> \<or> P' \<noteq> \<bottom> \<longrightarrow> P \<leadsto>\<^sub>\<tau> P' \<longrightarrow> P \<box> Q \<leadsto>\<^sub>\<tau> P' \<box> Q \<Longrightarrow>
   \<forall>P P' e. P \<leadsto>\<^sub>\<tau> P' \<longrightarrow> (e \<rightarrow> P) \<leadsto>\<^sub>\<tau> (e \<rightarrow> P') \<Longrightarrow> P \<^bsub>HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> Q \<longleftrightarrow> P \<leadsto>\<^bsub>e\<^esub> Q\<close>
  by (rule iffI[OF ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_imp_ev_trans hyps_on_\<tau>_trans_imp_ev_trans_imp_ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E])


\<comment>\<open>When \<^term>\<open>P = \<bottom>\<close>, we have the following result.\<close>
lemma BOT_ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_anything: \<open>\<bottom> \<^bsub>HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> P\<close>
proof -
  have \<open>\<bottom> = (e \<rightarrow> P) \<box> \<bottom>\<close> by simp
  thus \<open>\<bottom> \<^bsub>HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> P\<close> unfolding ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_def by (simp add: \<tau>_trans_eq)
qed


\<comment>\<open>Finally, again under two (automatic during instantiation) assumption on \<^term>\<open>(\<leadsto>\<^sub>\<tau>)\<close>,
   we have an equivalent definition with an \<open>\<tau>\<close> equality instead of a \<open>\<tau>\<close> transition.\<close>
lemma hyps_on_\<tau>_trans_imp_ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_def_bis: \<open>P \<^bsub>HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> Q \<longleftrightarrow> P =\<^sub>\<tau> (e \<rightarrow> Q) \<rhd> P\<close>
  if non_BOT_\<tau>_trans_SlidingL : \<open>\<forall>P P' Q. P = \<bottom> \<or> P' \<noteq> \<bottom> \<longrightarrow> P \<leadsto>\<^sub>\<tau> P' \<longrightarrow> P \<rhd> Q \<leadsto>\<^sub>\<tau> P' \<rhd> Q\<close>
    and \<tau>_trans_prefix           : \<open>\<forall>P P' e. P \<leadsto>\<^sub>\<tau> P' \<longrightarrow> (e \<rightarrow> P) \<leadsto>\<^sub>\<tau> (e \<rightarrow> P')\<close>
proof (rule iffI)
  show \<open>P =\<^sub>\<tau> (e \<rightarrow> Q) \<rhd> P \<Longrightarrow> P \<^bsub>HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> Q\<close>
    by (metis Sliding_def \<tau>_trans_NdetL \<tau>_trans_transitivity ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_def)
next
  show \<open>P =\<^sub>\<tau> (e \<rightarrow> Q) \<rhd> P\<close> if \<open>P \<^bsub>HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> Q\<close>
  proof (rule \<tau>_eqI)
    show \<open>(e \<rightarrow> Q) \<rhd> P \<leadsto>\<^sub>\<tau> P\<close> by (simp add: \<tau>_trans_SlidingR)
  next
    from \<open>P \<^bsub>HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> Q\<close> have \<open>P = (e \<rightarrow> (P after e)) \<rhd> P\<close>
      by (simp add: ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_imp_in_initials initial_ev_imp_eq_prefix_After_Sliding)
    also have \<open>\<dots> \<leadsto>\<^sub>\<tau> (e \<rightarrow> Q) \<rhd> P\<close>
      by (rule non_BOT_\<tau>_trans_SlidingL[rule_format],
          solves \<open>simp add: write0_def\<close>)
        (rule \<tau>_trans_prefix[rule_format],
          fact \<open>P \<^bsub>HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> Q\<close>[THEN ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_imp_ev_trans,
            unfolded ev_trans_is, THEN conjunct2])
    finally show \<open>P \<leadsto>\<^sub>\<tau> (e \<rightarrow> Q) \<rhd> P\<close> .
  qed
qed


end


context OpSemFD
begin

notation ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E (\<open>_ \<^bsub>FD-HOARE\<^esub>\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation \<tau>_eq (infix \<open>\<^sub>F\<^sub>D=\<^sub>\<tau>\<close> 50)

theorem ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_iff_ev_trans : \<open>P \<^bsub>FD-HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> Q \<longleftrightarrow> P \<^sub>F\<^sub>D\<leadsto>\<^bsub>e\<^esub> Q\<close>
  by (simp add: \<tau>_trans_DetL hyps_on_\<tau>_trans_imp_ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_iff_ev_trans mono_write0_FD)

theorem ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_def_bis: \<open>P \<^bsub>FD-HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> Q \<longleftrightarrow> P \<^sub>F\<^sub>D=\<^sub>\<tau> (e \<rightarrow> Q) \<rhd> P\<close>
  by (simp add: \<tau>_trans_SlidingL hyps_on_\<tau>_trans_imp_ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_def_bis mono_write0_FD)

end


context OpSemDT
begin

notation ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E (\<open>_ \<^bsub>DT-HOARE\<^esub>\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation \<tau>_eq (infix \<open>\<^sub>D\<^sub>T=\<^sub>\<tau>\<close> 50)

theorem ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_iff_ev_trans : \<open>P \<^bsub>DT-HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> Q \<longleftrightarrow> P \<^sub>D\<^sub>T\<leadsto>\<^bsub>e\<^esub> Q\<close>
  by (simp add: \<tau>_trans_DetL hyps_on_\<tau>_trans_imp_ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_iff_ev_trans mono_write0_DT)

theorem ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_def_bis: \<open>P \<^bsub>DT-HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> Q \<longleftrightarrow> P \<^sub>D\<^sub>T=\<^sub>\<tau> (e \<rightarrow> Q) \<rhd> P\<close>
  by (simp add: \<tau>_trans_SlidingL hyps_on_\<tau>_trans_imp_ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_def_bis mono_write0_DT)

end


context OpSemF
begin

notation ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E (\<open>_ \<^bsub>F-HOARE\<^esub>\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation \<tau>_eq (infix \<open>\<^sub>F=\<^sub>\<tau>\<close> 50)

theorem ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_iff_ev_trans : \<open>P \<^bsub>F-HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> Q \<longleftrightarrow> P \<^sub>F\<leadsto>\<^bsub>e\<^esub> Q\<close>
  by (simp add: hyps_on_\<tau>_trans_imp_ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_iff_ev_trans \<tau>_trans_DetL mono_write0_F)

theorem ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_def_bis: \<open>P \<^bsub>F-HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> Q \<longleftrightarrow> P \<^sub>F=\<^sub>\<tau> (e \<rightarrow> Q) \<rhd> P\<close>
  by (simp add: hyps_on_\<tau>_trans_imp_ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_def_bis \<tau>_trans_SlidingL mono_write0_F)


end


context OpSemT
begin

notation ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E (\<open>_ \<^bsub>T-HOARE\<^esub>\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation \<tau>_eq (infix \<open>\<^sub>T=\<^sub>\<tau>\<close> 50)

theorem ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_iff_ev_trans : \<open>P \<^bsub>T-HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> Q \<longleftrightarrow> P \<^sub>T\<leadsto>\<^bsub>e\<^esub> Q\<close>
  using \<tau>_trans_DetL ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_imp_ev_trans hyps_on_\<tau>_trans_imp_ev_trans_imp_ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E
    mono_write0_T by blast

theorem ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_def_bis: \<open>P \<^bsub>T-HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> Q \<longleftrightarrow> P \<^sub>T=\<^sub>\<tau> (e \<rightarrow> Q) \<rhd> P\<close>
  by (simp add: \<tau>_trans_SlidingL hyps_on_\<tau>_trans_imp_ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_def_bis mono_write0_T)

end

(*<*)
end
  (*>*)

