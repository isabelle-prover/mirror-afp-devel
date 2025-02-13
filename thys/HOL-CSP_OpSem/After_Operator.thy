(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_OpSem - Operational semantics for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff.
 *
 * This file       : The After operator with a locale
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

chapter \<open> Construction of the After Operator \<close>

(*<*)
theory  After_Operator
  imports Initials
begin
  (*>*)


text \<open>Now that we have defined \<^term>\<open>P\<^sup>0\<close>, we can talk about what
      happens to \<^term>\<open>P\<close> after an event belonging to this set.\<close>

section \<open>Definition\<close>

text \<open>We want to define a new operator on a process \<^term>\<open>P\<close> which would in
      some way be the reciprocal of the prefix operator \<^term>\<open>a \<rightarrow> P\<close>.\<close>

text \<open>The intuitive way of doing so is to only keep the tails of the traces
      beginning by \<^term>\<open>ev a\<close> (and similar for failures and divergences).
      However we have an issue if \<^term>\<open>ev a \<notin> P\<^sup>0\<close> i.e. if no trace of
      \<^term>\<open>P\<close> begins with \<^term>\<open>ev a\<close>: the result would no longer verify the 
      invariant \<^const>\<open>is_process\<close> because its trace set would be empty.
      We must therefore distinguish this case.\<close>

text \<open>In the previous version, we agreed to get \<^const>\<open>STOP\<close> after an event \<^term>\<open>ev a\<close> 
      that was not in the \<^const>\<open>initials\<close> of \<^term>\<open>P\<close>.
      But even if its repercussions were minimal, this choice seemed a little artificial
      and arbitrary.
      In this new version we use a placeholder instead: \<^term>\<open>\<Psi>\<close>.
      When \<^term>\<open>ev a \<in> P\<^sup>0\<close> we use our intuitive definition, and
      \<^term>\<open>ev a \<notin> P\<^sup>0\<close> we define \<^term>\<open>P\<close> after \<^term>\<open>a\<close> being equal to \<^term>\<open>\<Psi> P a\<close>.\<close>

text \<open>For the moment we have no additional assumption on \<^term>\<open>\<Psi>\<close>.\<close>

locale After = 
  fixes \<Psi> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
begin


lift_definition After :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (infixl \<open>after\<close> 86)
  is \<open>\<lambda>P a.   if ev a \<in> P\<^sup>0
            then ({(t, X). (ev a # t, X) \<in> \<F> P},
                  { t    .  ev a # t     \<in> \<D> P})
            else (\<F> (\<Psi> P a), \<D> (\<Psi> P a))\<close>
proof -
  show \<open>?thesis P a\<close> (is \<open>is_process (if _ then (?f, ?d) else _)\<close>) for P a
  proof (split if_split, intro conjI impI)
    show \<open>is_process (\<F> (\<Psi> P a), \<D> (\<Psi> P a))\<close>
      by (metis CollectD Divergences.rep_eq Failures.rep_eq process\<^sub>0_of_process process_surj_pair)
  next
    show \<open>is_process (?f, ?d)\<close> if \<open>ev a \<in> P\<^sup>0\<close>
      unfolding is_process_def FAILURES_def DIVERGENCES_def fst_conv snd_conv
    proof (intro conjI impI allI)
      from \<open>ev a \<in> P\<^sup>0\<close> show \<open>([], {}) \<in> ?f\<close> by (simp add: initials_memD T_F_spec)
    next
      show \<open>(t, X) \<in> ?f \<Longrightarrow> ftF t\<close> for t X
        by simp (metis front_tickFree_Cons_iff front_tickFree_Nil is_processT2)
    next
      show \<open>(t @ u, {}) \<in> ?f \<Longrightarrow> (t, {}) \<in> ?f\<close> for t u by (simp add: is_processT3)
    next
      from is_processT4 show \<open>(t, Y) \<in> ?f \<and> X \<subseteq> Y \<Longrightarrow> (t, X) \<in> ?f\<close> for t X Y by blast
    next
      from \<open>ev a \<in> P\<^sup>0\<close> show \<open>(t, X) \<in> ?f \<and> (\<forall>e. e \<in> Y \<longrightarrow> (t @ [e], {}) \<notin> ?f)
                             \<Longrightarrow> (t, X \<union> Y) \<in> ?f\<close> for t X Y
        by (simp add: initials_memD is_processT5)
    next
      show \<open>(t @ [\<checkmark>(r)], {}) \<in> ?f \<Longrightarrow> (t, X - {\<checkmark>(r)}) \<in> ?f\<close> for t r X
        by (simp add: is_processT6)
    next
      from is_processT7 show \<open>t \<in> ?d \<and> tF t \<and> ftF u \<Longrightarrow> t @ u \<in> ?d\<close> for t u by force
    next
      from D_F show \<open>t \<in> ?d \<Longrightarrow> (t, X) \<in> ?f\<close> for t X by blast
    next
      show \<open>t @ [\<checkmark>(r)] \<in> ?d \<Longrightarrow> t \<in> ?d\<close> for t r
        by simp (metis append_Cons process_charn)
    qed
  qed
qed



section \<open>Projections\<close>

lemma F_After :
  \<open>\<F> (P after a) = (if ev a \<in> P\<^sup>0 then {(t, X). (ev a # t, X) \<in> \<F> P} else \<F> (\<Psi> P a))\<close>
  by (simp add: Failures_def After.rep_eq FAILURES_def)

lemma D_After :
  \<open>\<D> (P after a) = (if ev a \<in> P\<^sup>0 then {s. ev a # s \<in> \<D> P} else \<D> (\<Psi> P a))\<close> 
  by (simp add: Divergences_def After.rep_eq DIVERGENCES_def)

lemma T_After :
  \<open>\<T> (P after a) = (if ev a \<in> P\<^sup>0 then {s. ev a # s \<in> \<T> P} else \<T> (\<Psi> P a))\<close>
  by (auto simp add: T_F_spec[symmetric] F_After)

lemmas After_projs = F_After D_After T_After


lemma not_initial_After : \<open>ev a \<notin> P\<^sup>0 \<Longrightarrow> P after a = \<Psi> P a\<close>
  by (simp add: After.abs_eq Process_spec)

lemma initials_After :
  \<open>(P after a)\<^sup>0 = (if ev a \<in> P\<^sup>0 then {e. ev a # [e] \<in> \<T> P} else (\<Psi> P a)\<^sup>0)\<close>
  by (simp add: T_After initials_def)



section \<open>Monotony\<close>

lemma mono_After : \<open>P after a \<sqsubseteq> Q after a\<close>
  if \<open>P \<sqsubseteq> Q\<close> and \<open>ev a \<notin> Q\<^sup>0 \<Longrightarrow> \<Psi> P a \<sqsubseteq> \<Psi> Q a\<close>
proof (subst le_approx_def, safe)
  from that(1)[THEN anti_mono_initials] that(1)[THEN le_approx2T] that[THEN le_approx1]
  show \<open>t \<in> \<D> (Q after a) \<Longrightarrow> t \<in> \<D> (P after a)\<close> for t
    by (simp add: D_After initials_def subset_iff split: if_split_asm)
      (metis D_imp_front_tickFree append_Cons append_Nil butlast.simps(2) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1)
        is_processT7 last.simps tickFree_Nil tickFree_butlast)
next
  from that(1)[THEN anti_mono_initials] that(2)[THEN le_approx2] that(1)[THEN proc_ord2a]
  show \<open>t \<notin> \<D> (P after a) \<Longrightarrow> X \<in> \<R>\<^sub>a (P after a) t \<Longrightarrow> X \<in> \<R>\<^sub>a (Q after a) t\<close> for t X
    by (simp add: Refusals_after_def After_projs initials_def subset_iff split: if_split_asm)
      (metis initials_memI F_T initials_def mem_Collect_eq, blast)
next
  from that(1)[THEN anti_mono_initials] that[THEN le_approx2] that(1)[THEN le_approx2T]
  show \<open>t \<notin> \<D> (P after a) \<Longrightarrow> X \<in> \<R>\<^sub>a (Q after a) t \<Longrightarrow> X \<in> \<R>\<^sub>a (P after a) t\<close> for t X
    by (simp add: Refusals_after_def After_projs initials_def subset_iff split: if_split_asm)
      (metis F_imp_front_tickFree append_Cons append_Nil butlast.simps(2)
        event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) is_processT7 last.simps tickFree_Nil tickFree_butlast)
next
  show \<open>t \<in> min_elems (\<D> (P after a)) \<Longrightarrow> t \<in> \<T> (Q after a)\<close> for t 
  proof (cases \<open>P = \<bottom>\<close>)
    assume \<open>t \<in> min_elems (\<D> (P after a))\<close> and \<open>P = \<bottom>\<close>
    hence \<open>t = []\<close>
      by (simp add: BOT_iff_Nil_D D_After D_BOT min_elems_def)
        (metis append_butlast_last_id front_tickFree_single nil_less2)
    thus \<open>t \<in> \<T> (Q after a)\<close> by simp
  next
    from that(1)[THEN anti_mono_initials] that(1)[THEN le_approx2T]
      that(2)[THEN le_approx3] min_elems6[OF _ _ that(1)]
    show \<open>t \<in> min_elems (\<D> (P after a)) \<Longrightarrow> P \<noteq> \<bottom> \<Longrightarrow> t \<in> \<T> (Q after a)\<close>
      apply (auto simp add: min_elems_def After_projs BOT_iff_Nil_D split: if_split_asm)
      by (metis T_F_spec append_butlast_last_id butlast.simps(2) less_self)
        (metis (mono_tags, lifting) T_F_spec append_Nil initials_def mem_Collect_eq)
  qed
qed


lemma mono_After_T  : \<open>P \<sqsubseteq>\<^sub>T Q  \<Longrightarrow> P after a \<sqsubseteq>\<^sub>T Q after a\<close>
  and mono_After_F  : \<open>P \<sqsubseteq>\<^sub>F Q  \<Longrightarrow> P after a \<sqsubseteq>\<^sub>F Q after a\<close>
  and mono_After_D  : \<open>P \<sqsubseteq>\<^sub>D Q  \<Longrightarrow> P after a \<sqsubseteq>\<^sub>D Q after a\<close>
  and mono_After_FD : \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> P after a \<sqsubseteq>\<^sub>F\<^sub>D Q after a\<close>
  and mono_After_DT : \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> P after a \<sqsubseteq>\<^sub>D\<^sub>T Q after a\<close>
  if \<open>ev a \<in> Q\<^sup>0\<close>
  using that F_subset_imp_T_subset[of Q P] D_T[of \<open>ev a # _\<close> P]
  unfolding failure_divergence_refine_def trace_divergence_refine_def
    failure_refine_def divergence_refine_def trace_refine_def
  by (auto simp add: After_projs initials_def)
    (metis initials_memI in_mono mem_Collect_eq initials_def)

lemmas monos_After = mono_After mono_After_FD mono_After_DT
  mono_After_F mono_After_D mono_After_T



section \<open>Behaviour of @{const [source] After} with \<^const>\<open>STOP\<close>, \<^const>\<open>SKIP\<close> and \<^term>\<open>\<bottom>\<close>\<close>

lemma After_STOP : \<open>STOP after a = \<Psi> STOP a\<close>
  by (simp add: Process_eq_spec After_projs)

lemma After_SKIP : \<open>SKIP r after a = \<Psi> (SKIP r) a\<close>
  by (simp add: Process_eq_spec After_projs)

lemma After_BOT : \<open>\<bottom> after a = \<bottom>\<close>
  by (force simp add: BOT_iff_Nil_D D_After D_BOT)

lemma After_is_BOT_iff :
  \<open>P after a = \<bottom> \<longleftrightarrow> (if ev a \<in> P\<^sup>0 then [ev a] \<in> \<D> P else \<Psi> P a = \<bottom>)\<close>
  using hd_Cons_tl by (force simp add: BOT_iff_Nil_D D_After initials_def D_T)



section \<open>Behaviour of @{const [source] After} with Operators of \<^session>\<open>HOL-CSP\<close>\<close>

text \<open>In future theories, we will need to know how @{const [source] After}
      behaves with other operators of CSP.
      More specifically, we want to know how @{const [source] After} can be "distributed"
      over a sequential composition, a synchronization, etc.\<close>

text \<open>In some way, we are looking for reversing the "step-laws"
      (laws of distributivity of \<^const>\<open>Mprefix\<close> over other operators).
      Given the difficulty in establishing these results in \<^session>\<open>HOL-CSP\<close>
      and \<^session>\<open>HOL-CSPM\<close>, one can easily imagine that proving
      @{const [source] After} versions will require a lot of work.\<close>



subsection \<open>Loss of Determinism\<close>

text \<open>A first interesting observation is that the @{const [source] After} 
      operator leads to the loss of determinism.\<close>

lemma After_Mprefix_is_After_Mndetprefix:
  \<open>a \<in> A \<Longrightarrow> (\<box>a \<in> A \<rightarrow> P a) after a = (\<sqinter>a \<in> A \<rightarrow> P a) after a\<close>
  by (auto simp add: Process_eq_spec initials_Mprefix initials_Mndetprefix
      After_projs Mprefix_projs Mndetprefix_projs)

lemma After_Det_is_After_Ndet :
  \<open>ev a \<in> P\<^sup>0 \<union> Q\<^sup>0 \<Longrightarrow> (P \<box> Q) after a = (P \<sqinter> Q) after a\<close>
  by (auto simp add: Process_eq_spec initials_Det initials_Ndet
      After_projs Det_projs Ndet_projs)

lemma After_Sliding_is_After_Ndet :
  \<open>ev a \<in> P\<^sup>0 \<union> Q\<^sup>0 \<Longrightarrow> (P \<rhd> Q) after a = (P \<sqinter> Q) after a\<close>
  by (auto simp add: Process_eq_spec initials_Sliding initials_Ndet
      After_projs Sliding_projs Ndet_projs)


lemma After_Ndet: 
  \<open>(P \<sqinter> Q) after a = 
   (  if ev a \<in> P\<^sup>0 \<inter> Q\<^sup>0 then P after a \<sqinter> Q after a
    else   if ev a \<in> P\<^sup>0 then P after a
         else   if ev a \<in> Q\<^sup>0 then Q after a
              else \<Psi> (P \<sqinter> Q) a)\<close> for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof -
  { fix P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    assume \<open>ev a \<in> P\<^sup>0\<close> \<open>ev a \<notin> Q\<^sup>0\<close>
    hence \<open>(P \<sqinter> Q) after a = P after a\<close>
      by (simp add: Process_eq_spec After_projs Ndet_projs initials_Ndet)
        (meson initials_memI D_T F_T)
  }
  moreover have \<open>ev a \<notin> P\<^sup>0 \<union> Q\<^sup>0 \<Longrightarrow> (P \<sqinter> Q) after a = \<Psi> (P \<sqinter> Q) a\<close>
    by (simp add: Process_eq_spec After_projs initials_Ndet)
  moreover have \<open>ev a \<in> P\<^sup>0 \<inter> Q\<^sup>0 \<Longrightarrow>  (P \<sqinter> Q) after a = P after a \<sqinter> Q after a\<close>
    by (auto simp add: Process_eq_spec After_projs Ndet_projs initials_Ndet)
  ultimately show ?thesis by (metis Int_iff Ndet_commute Un_iff)
qed

lemma After_Det: 
  \<open>(P \<box> Q) after a = 
   (  if ev a \<in> P\<^sup>0 \<inter> Q\<^sup>0 then P after a \<sqinter> Q after a
    else   if ev a \<in> P\<^sup>0 then P after a
         else   if ev a \<in> Q\<^sup>0 then Q after a
              else \<Psi> (P \<box> Q) a)\<close>
  by (simp add: After_Det_is_After_Ndet After_Ndet not_initial_After initials_Det)

lemma After_Sliding:
  \<open>(P \<rhd> Q) after a = 
   (  if ev a \<in> P\<^sup>0 \<inter> Q\<^sup>0 then P after a \<sqinter> Q after a
    else   if ev a \<in> P\<^sup>0 then P after a
         else   if ev a \<in> Q\<^sup>0 then Q after a
              else \<Psi> (P \<rhd> Q) a)\<close>
  by (simp add: After_Ndet After_Sliding_is_After_Ndet initials_Sliding not_initial_After)


lemma After_Mprefix:
  \<open>(\<box> a \<in> A \<rightarrow> P a) after a = (if a \<in> A then P a else \<Psi> (\<box> a \<in> A \<rightarrow> P a) a)\<close>
  by (simp add: Process_eq_spec After_projs initials_Mprefix
      Mprefix_projs image_iff)

lemma After_Mndetprefix:
  \<open>(\<sqinter> a \<in> A \<rightarrow> P a) after a = (if a \<in> A then P a else \<Psi> (\<sqinter> a \<in> A \<rightarrow> P a) a)\<close>
  by (metis (full_types) After_Mprefix After_Mprefix_is_After_Mndetprefix
      event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(1) imageE not_initial_After initials_Mndetprefix)

corollary After_write0 : \<open>(a \<rightarrow> P) after b = (if b = a then P else \<Psi> (a \<rightarrow> P) b)\<close>
  by (simp add: write0_def After_Mprefix)

lemma \<open>(a \<rightarrow> P) after a = P\<close> by (simp add: After_write0)

text \<open>This result justifies seeing \<^term>\<open>P after a\<close> as the reciprocal operator of the 
      prefix \<^term>\<open>a \<rightarrow> P\<close>.

      However, we lose information with @{const [source] After}: in general,
      \<^term>\<open>a \<rightarrow> P after a \<noteq> P\<close> (even when \<^term>\<open>ev a \<in> P\<^sup>0\<close> and \<^term>\<open>P \<noteq> \<bottom>\<close>).\<close>

lemma \<open>\<exists>P. a \<rightarrow> P after a \<noteq> P\<close>
proof (intro exI)
  show \<open>a \<rightarrow> SKIP undefined after a \<noteq> SKIP undefined\<close> by simp
qed

lemma \<open>\<exists>P. ev a \<in> P\<^sup>0 \<and> a \<rightarrow> P after a \<noteq> P\<close>
  by (metis UNIV_I initials_BOT write0_neq_BOT)

lemma \<open>\<exists>P. ev a \<in> P\<^sup>0 \<and> P \<noteq> \<bottom> \<and> a \<rightarrow> P after a \<noteq> P\<close>
proof (intro exI)
  define P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where P_def: \<open>P = (a \<rightarrow> STOP) \<box> SKIP undefined\<close>
  have * : \<open>ev a \<in> P\<^sup>0\<close> by (simp add: P_def initials_Det initials_write0)
  moreover have \<open>P \<noteq> \<bottom>\<close> by (simp add: Det_is_BOT_iff P_def)
  moreover have \<open>a \<rightarrow> P after a = a \<rightarrow> STOP\<close>
    by (rule arg_cong[where f = \<open>\<lambda>P. a \<rightarrow> P\<close>])
      (simp add: P_def After_Det initials_write0 After_write0)
  moreover have \<open>a \<rightarrow> STOP \<noteq> P\<close>
    by (rule contrapos_nn[of \<open>(a \<rightarrow> STOP)\<^sup>0 = P\<^sup>0\<close> \<open>a \<rightarrow> STOP = P\<close>])
      (auto simp add: P_def initials_Det initials_write0)
  ultimately show \<open>ev a \<in> P\<^sup>0 \<and> P \<noteq> \<bottom> \<and> a \<rightarrow> P after a \<noteq> P\<close> by presburger
qed


corollary After_write : \<open>(c\<^bold>!a \<rightarrow> P) after b = (if b = c a then P else \<Psi> (c\<^bold>!a \<rightarrow> P) b)\<close>
  by (simp add: write_def After_Mprefix)

corollary After_read :
  \<open>(c\<^bold>?a\<in>A \<rightarrow> P a) after b = (if b \<in> c ` A then P (inv_into A c b) else \<Psi> (c\<^bold>?a\<in>A \<rightarrow> P a) b)\<close>
  by (simp add: read_def After_Mprefix)

corollary After_ndet_write :
  \<open>(c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) after b = (if b \<in> c ` A then P (inv_into A c b) else \<Psi> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) b)\<close>
  by (simp add: ndet_write_def After_Mndetprefix)



subsection \<open>@{const [source] After} Sequential Composition\<close>

text \<open>The first goal is to obtain an equivalent of 
      @{thm Mprefix_Seq[of \<open>{a}\<close> \<open>\<lambda>a. P\<close> Q, folded write0_def]}.
      But in order to be exhaustive we also have to consider the possibility of \<^term>\<open>Q\<close> taking
      the lead when \<^term>\<open>\<checkmark>(r) \<in> P\<^sup>0\<close> in the sequential composition \<^term>\<open>P \<^bold>; Q\<close>.\<close>

lemma not_skippable_or_not_initialR_After_Seq:
  \<open>(P \<^bold>; Q) after a = (if ev a \<in> P\<^sup>0 then P after a \<^bold>; Q else \<Psi> (P \<^bold>; Q) a)\<close>
  if \<open>range tick \<inter> P\<^sup>0 = {} \<or> (\<forall>r. \<checkmark>(r) \<in> P\<^sup>0 \<longrightarrow> ev a \<notin> Q\<^sup>0)\<close>
proof (cases \<open>P = \<bottom>\<close>)
  show \<open>P = \<bottom> \<Longrightarrow>
        (P \<^bold>; Q) after a =
        (if ev a \<in> P\<^sup>0 then P after a \<^bold>; Q else \<Psi> (P \<^bold>; Q) a)\<close>
    by (simp add: After_BOT)
next
  assume non_BOT: \<open>P \<noteq> \<bottom>\<close>
  with that have $ : \<open>ev a \<in> (P \<^bold>; Q)\<^sup>0 \<longleftrightarrow> ev a \<in> P\<^sup>0\<close>
    by (auto simp add: initials_Seq)
  show \<open>(P \<^bold>; Q) after a =
        (if ev a \<in> P\<^sup>0 then P after a \<^bold>; Q else \<Psi> (P \<^bold>; Q) a)\<close>
  proof (split if_split, intro conjI impI)
    from "$" show \<open>ev a \<notin> P\<^sup>0 \<Longrightarrow> (P \<^bold>; Q) after a = \<Psi> (P \<^bold>; Q) a\<close>
      by (simp add: not_initial_After)
  next
    assume initial_P : \<open>ev a \<in> P\<^sup>0\<close>
    show \<open>(P \<^bold>; Q) after a = P after a \<^bold>; Q\<close>
    proof (subst Process_eq_spec_optimized, safe)
      fix s
      assume \<open>s \<in> \<D> ((P \<^bold>; Q) after a)\<close>
      hence * : \<open>ev a # s \<in> \<D> (P \<^bold>; Q)\<close>
        by (simp add: D_After "$" initial_P split: if_split_asm)
      then consider \<open>ev a # s \<in> \<D> P\<close> 
        | t1 t2 r where \<open>ev a # s = t1 @ t2\<close> \<open>t1 @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>t2 \<in> \<D> Q\<close>
        by (simp add: D_Seq) blast
      thus \<open>s \<in> \<D> (P after a \<^bold>; Q)\<close>
      proof cases
        show \<open>ev a # s \<in> \<D> P \<Longrightarrow> s \<in> \<D> (P after a \<^bold>; Q)\<close>
          by (simp add: D_Seq D_After initial_P)
      next
        fix t1 t2 r assume ** : \<open>ev a # s = t1 @ t2\<close> \<open>t1 @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>t2 \<in> \<D> Q\<close>
        have \<open>t1 \<noteq> []\<close> by (metis "**" initials_memI D_T
              append_self_conv2 disjoint_iff rangeI that)
        with "**"(1) obtain t1'
          where \<open>t1 = ev a # t1'\<close> \<open>s = t1' @ t2\<close> by (metis Cons_eq_append_conv)
        with "**"(2, 3) show \<open>s \<in> \<D> (P after a \<^bold>; Q)\<close>
          by (simp add: D_Seq T_After) (blast intro: initial_P)
      qed
    next
      fix s
      assume \<open>s \<in> \<D> (P after a\<^bold>; Q)\<close>
      hence \<open>ev a # s \<in> \<D> P \<or> (\<exists>t1 t2 r. s = t1 @ t2 \<and> ev a # t1 @ [\<checkmark>(r)] \<in> \<T> P \<and> t2 \<in> \<D> Q)\<close>
        by (simp add: D_Seq After_projs initial_P)
      hence \<open>ev a # s \<in> \<D> (P \<^bold>; Q)\<close>
        by (elim disjE; simp add: D_Seq) (metis append_Cons)
      thus \<open>s \<in> \<D> ((P \<^bold>; Q) after a)\<close>
        by (simp add: D_After "$" initial_P)
    next
      fix s X
      assume same_div : \<open>\<D> ((P \<^bold>; Q) after a) = \<D> (P after a \<^bold>; Q)\<close>
      assume \<open>(s, X) \<in> \<F> ((P \<^bold>; Q) after a)\<close>
      then consider \<open>ev a \<in> (P \<^bold>; Q)\<^sup>0\<close> \<open>(ev a # s, X) \<in> \<F> (P \<^bold>; Q)\<close>
        | \<open>ev a \<notin> (P \<^bold>; Q)\<^sup>0\<close> \<open>s = []\<close> by (simp add: F_After "$" initial_P)
      thus \<open>(s, X) \<in> \<F> (P after a \<^bold>; Q)\<close>
      proof cases
        assume assms : \<open>ev a \<in> (P \<^bold>; Q)\<^sup>0\<close> \<open>(ev a # s, X) \<in> \<F> (P \<^bold>; Q)\<close>
        from assms(2) consider \<open>ev a # s \<in> \<D> (P \<^bold>; Q)\<close>
          | \<open>(ev a # s, X \<union> range tick) \<in> \<F> P\<close> \<open>tF s\<close>
          | t1 t2 r where \<open>ev a # s = t1 @ t2\<close> \<open>t1 @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>(t2, X) \<in> \<F> Q\<close>
          by (simp add: F_Seq D_Seq) blast
        thus \<open>(s, X) \<in> \<F> (P after a \<^bold>; Q)\<close>
        proof cases
          assume \<open>ev a # s \<in> \<D> (P \<^bold>; Q)\<close>
          hence \<open>s \<in> \<D> ((P \<^bold>; Q) after a)\<close>
            by (simp add: D_After assms(1))
          with same_div D_F show \<open>(s, X) \<in> \<F> (P after a \<^bold>; Q)\<close> by blast
        next
          show \<open>(ev a # s, X \<union> range tick) \<in> \<F> P \<Longrightarrow> tF s \<Longrightarrow> (s, X) \<in> \<F> (P after a \<^bold>; Q)\<close>
            by (simp add: F_Seq F_After initial_P)
        next
          fix t1 t2 r assume * : \<open>ev a # s = t1 @ t2\<close> \<open>t1 @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>(t2, X) \<in> \<F> Q\<close>
          have \<open>t1 \<noteq> []\<close> by (metis "*" initials_memI F_T
                disjoint_iff rangeI self_append_conv2 that)
          with "*"(1) obtain t1'
            where \<open>t1 = ev a # t1'\<close> \<open>s = t1' @ t2\<close> by (metis Cons_eq_append_conv)
          with "*"(2, 3) show \<open>(s, X) \<in> \<F> (P after a \<^bold>; Q)\<close>
            by (simp add: F_Seq T_After) (blast intro: initial_P)
        qed
      next
        show \<open>ev a \<notin> (P \<^bold>; Q)\<^sup>0 \<Longrightarrow> s = [] \<Longrightarrow> (s, X) \<in> \<F> (P after a \<^bold>; Q)\<close>
          by (simp add: F_Seq F_After "$" initial_P)
      qed
    next
      fix s X
      assume same_div : \<open>\<D> ((P \<^bold>; Q) after a) = \<D> (P after a \<^bold>; Q)\<close>
      assume \<open>(s, X) \<in> \<F> (P after a \<^bold>; Q)\<close>
      then consider \<open>s \<in> \<D> (P after a \<^bold>; Q)\<close>
        | \<open>(s, X \<union> range tick) \<in> \<F> (P after a)\<close> \<open>tF s\<close>
        | t1 t2 r where \<open>s = t1 @ t2\<close> \<open>t1 @ [\<checkmark>(r)] \<in> \<T> (P after a)\<close> \<open>(t2, X) \<in> \<F> Q\<close>
        by (simp add: F_Seq D_Seq) blast
      thus \<open>(s, X) \<in> \<F> ((P \<^bold>; Q) after a)\<close>
      proof cases
        from same_div D_F show \<open>s \<in> \<D> (P after a \<^bold>; Q) \<Longrightarrow> (s, X) \<in> \<F> ((P \<^bold>; Q) after a)\<close> by blast
      next
        show \<open>(s, X \<union> range tick) \<in> \<F> (P after a) \<Longrightarrow> tF s \<Longrightarrow> (s, X) \<in> \<F> ((P \<^bold>; Q) after a)\<close>
          by (simp add: F_After "$" initial_P F_Seq)
      next
        fix t1 t2 r assume * : \<open>s = t1 @ t2\<close> \<open>t1 @ [\<checkmark>(r)] \<in> \<T> (P after a)\<close> \<open>(t2, X) \<in> \<F> Q\<close>
        from "*"(2) have \<open>ev a # t1 @ [\<checkmark>(r)] \<in> \<T> P\<close> by (simp add: T_After initial_P)
        with "*"(1, 3) show \<open>(s, X) \<in> \<F> ((P \<^bold>; Q) after a)\<close>
          by (simp add: F_After "$" initial_P F_Seq) (metis append_Cons)
      qed
    qed
  qed
qed


lemma skippable_not_initialL_After_Seq:
  \<open>(P \<^bold>; Q) after a = (  if (\<exists>r. \<checkmark>(r) \<in> P\<^sup>0) \<and> ev a \<in> Q\<^sup>0
                      then Q after a else \<Psi> (P \<^bold>; Q) a)\<close>
  (is \<open>(P \<^bold>; Q) after a = (if ?prem then ?rhs else _)\<close>) if \<open>ev a \<notin> P\<^sup>0\<close>
proof -
  from initials_BOT \<open>ev a \<notin> P\<^sup>0\<close> have non_BOT : \<open>P \<noteq> \<bottom>\<close> by blast
  with \<open>ev a \<notin> P\<^sup>0\<close> have $ : \<open>ev a \<in> (P \<^bold>; Q)\<^sup>0 \<longleftrightarrow> ?prem\<close>
    by (auto simp add: initials_Seq)
  show \<open>(P \<^bold>; Q) after a = (if ?prem then ?rhs else \<Psi> (P \<^bold>; Q) a)\<close>
  proof (split if_split, intro conjI impI)
    show \<open>\<not> ?prem \<Longrightarrow> (P \<^bold>; Q) after a = \<Psi> (P \<^bold>; Q) a\<close>
      by (rule not_initial_After, use "$" in blast)
  next
    show \<open>(P \<^bold>; Q) after a = ?rhs\<close> if ?prem
    proof (subst Process_eq_spec, safe)
      fix t
      assume \<open>t \<in> \<D> ((P \<^bold>; Q) after a)\<close>
      with \<open>?prem\<close> have \<open>ev a # t \<in> \<D> (P \<^bold>; Q)\<close> by (simp add: D_After "$")
      with \<open>ev a \<notin> P\<^sup>0\<close> obtain t1 t2 r where * : \<open>ev a # t = t1 @ t2\<close> \<open>t1 @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>t2 \<in> \<D> Q\<close>
        by (simp add: D_Seq) (meson initials_memI D_T)
      from "*"(1, 2) \<open>ev a \<notin> P\<^sup>0\<close> initials_memI have \<open>t1 = []\<close>
        by (cases t1; simp) blast
      with "*" show \<open>t \<in> \<D> ?rhs\<close>
        by (auto simp add: D_After intro: initials_memI D_T)
    next
      from \<open>?prem\<close> show \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ((P \<^bold>; Q) after a)\<close> for s
        by (simp add: D_After "$" D_Seq split: if_split_asm)
          (metis append_Nil initials_memD)
    next
      fix t X
      assume \<open>(t, X) \<in> \<F> ((P \<^bold>; Q) after a)\<close>
      hence \<open>ev a \<in> (P \<^bold>; Q)\<^sup>0\<close> \<open>(ev a # t, X) \<in> \<F> (P \<^bold>; Q)\<close>
        by (simp_all add: F_After "$" split: if_split_asm) (use \<open>?prem\<close> in blast)+
      thus \<open>(t, X) \<in> \<F> ?rhs\<close>
        by (simp add: F_After F_Seq "$")
          (metis (no_types, lifting) initials_memI D_T F_T Nil_is_append_conv
            append_self_conv2 hd_append2 list.exhaust_sel list.sel(1) \<open>ev a \<notin> P\<^sup>0\<close>)
    next
      show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ((P \<^bold>; Q) after a)\<close> for s X
        by (simp add: F_After "$" F_Seq split: if_split_asm)
          (metis append_Nil initials_memD \<open>?prem\<close>, use \<open>?prem\<close> in blast)
    qed
  qed
qed


lemma skippable_initialL_initialR_After_Seq:
  \<open>(P \<^bold>; Q) after a = (P after a \<^bold>; Q) \<sqinter> Q after a\<close>
  (is \<open>(P \<^bold>; Q) after a = (P after a \<^bold>; Q) \<sqinter> ?rhs\<close>)
  if assms : \<open>(\<exists>r. \<checkmark>(r) \<in> P\<^sup>0) \<and> ev a \<in> Q\<^sup>0\<close> \<open>ev a \<in> P\<^sup>0\<close>
proof (cases \<open>P = \<bottom>\<close>)
  show \<open>P = \<bottom> \<Longrightarrow> (P \<^bold>; Q) after a = (P after a \<^bold>; Q) \<sqinter> ?rhs\<close>
    by (simp add: After_BOT)
next
  show \<open>(P \<^bold>; Q) after a = (P after a \<^bold>; Q) \<sqinter> ?rhs\<close> if \<open>P \<noteq> \<bottom>\<close>
  proof (subst Process_eq_spec_optimized, safe)
    fix s
    assume \<open>s \<in> \<D> ((P \<^bold>; Q) after a)\<close>
    hence \<open>ev a # s \<in> \<D> (P \<^bold>; Q)\<close>
      by (simp add: D_After initials_Seq \<open>P \<noteq> \<bottom>\<close> \<open>ev a \<in> P\<^sup>0\<close> image_iff)
    then consider \<open>ev a # s \<in> \<D> P\<close>
      | t1 t2 r where \<open>ev a # s = t1 @ t2\<close> \<open>t1 @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>t2 \<in> \<D> Q\<close>
      by (simp add: D_Seq) blast
    thus \<open>s \<in> \<D> ((P after a \<^bold>; Q) \<sqinter> ?rhs)\<close>
    proof cases
      show \<open>ev a # s \<in> \<D> P \<Longrightarrow> s \<in> \<D> ((P after a \<^bold>; Q) \<sqinter> ?rhs)\<close>
        by (simp add: D_After D_Seq D_Ndet \<open>P \<noteq> \<bottom>\<close> assms(2))
    next
      fix t1 t2 r assume * : \<open>ev a # s = t1 @ t2\<close> \<open>t1 @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>t2 \<in> \<D> Q\<close>
      show \<open>s \<in> \<D> ((P after a \<^bold>; Q) \<sqinter> ?rhs)\<close>
      proof (cases \<open>t1 = []\<close>)
        from "*"(1, 3) assms(1) show \<open>t1 = [] \<Longrightarrow> s \<in> \<D> ((P after a \<^bold>; Q) \<sqinter> ?rhs)\<close>
          by (simp add: D_After D_Ndet)
      next
        assume \<open>t1 \<noteq> []\<close>
        with "*"(1, 3) obtain t1' where \<open>t1 = ev a # t1'\<close> by (cases t1; simp)
        with "*" show \<open>s \<in> \<D> ((P after a \<^bold>; Q) \<sqinter> ?rhs)\<close>
          by (simp add: T_After D_Seq D_Ndet assms(2)) blast
      qed
    qed
  next
    fix s
    assume \<open>s \<in> \<D> ((P after a \<^bold>; Q) \<sqinter> ?rhs)\<close>
    then consider \<open>s \<in> \<D> (P after a \<^bold>; Q)\<close> | \<open>s \<in> \<D> ?rhs\<close>
      by (simp add: D_Ndet) blast
    thus \<open>s \<in> \<D> ((P \<^bold>; Q) after a)\<close>
    proof cases
      show \<open>s \<in> \<D> (P after a \<^bold>; Q) \<Longrightarrow> s \<in> \<D> ((P \<^bold>; Q) after a)\<close>
        by (simp add: After_projs D_Seq initials_Seq \<open>P \<noteq> \<bottom>\<close> assms(2) image_iff)
          (metis append_Cons)
    next
      from assms show \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ((P \<^bold>; Q) after a)\<close>
        by (simp add: D_After D_Seq initials_Seq \<open>P \<noteq> \<bottom>\<close> split: if_split_asm)
          (metis append_Nil initials_def mem_Collect_eq)
    qed
  next
    fix s X
    assume same_div : \<open>\<D> ((P \<^bold>; Q) after a) = \<D> ((P after a \<^bold>; Q) \<sqinter> ?rhs)\<close>
    assume \<open>(s, X) \<in> \<F> ((P \<^bold>; Q) after a)\<close>
    hence \<open>(ev a # s, X) \<in> \<F> (P \<^bold>; Q)\<close>
      by (simp add: F_After initials_Seq \<open>P \<noteq> \<bottom>\<close> assms(2) image_iff)
    then consider \<open>ev a # s \<in> \<D> P\<close>
      | \<open>(ev a # s, X \<union> range tick) \<in> \<F> P\<close> \<open>tF s\<close>
      | t1 t2 r where \<open>ev a # s = t1 @ t2\<close> \<open>t1 @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>(t2, X) \<in> \<F> Q\<close>
      by (simp add: F_Seq D_Seq) blast
    thus \<open>(s, X) \<in> \<F> ((P after a \<^bold>; Q) \<sqinter> ?rhs)\<close>
    proof cases
      assume \<open>ev a # s \<in> \<D> P\<close>
      hence \<open>s \<in> \<D> (P after a \<^bold>; Q)\<close> 
        by (simp add: D_After D_Seq assms(2))
      with same_div D_Ndet D_F show \<open>(s, X) \<in> \<F> ((P after a \<^bold>; Q) \<sqinter> ?rhs)\<close> by blast
    next
      show \<open>(ev a # s, X \<union> range tick) \<in> \<F> P \<Longrightarrow> tF s \<Longrightarrow>
            (s, X) \<in> \<F> ((P after a \<^bold>; Q) \<sqinter> ?rhs)\<close>
        by (simp add: F_Ndet F_Seq F_After assms(2))
    next
      fix t1 t2 r assume * : \<open>ev a # s = t1 @ t2\<close> \<open>t1 @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>(t2, X) \<in> \<F> Q\<close>
      show \<open>(s, X) \<in> \<F> ((P after a \<^bold>; Q) \<sqinter> ?rhs)\<close>
      proof (cases \<open>t1 = []\<close>)
        from "*"(1, 3) assms show \<open>t1 = [] \<Longrightarrow> (s, X) \<in> \<F> ((P after a \<^bold>; Q) \<sqinter> ?rhs)\<close>
          by (simp add: F_Ndet F_Seq F_After assms(2))
      next
        assume \<open>t1 \<noteq> []\<close>
        with "*"(1, 3) obtain t1' where \<open>t1 = ev a # t1'\<close> by (cases t1; simp)
        with "*" show \<open>(s, X) \<in> \<F> ((P after a \<^bold>; Q) \<sqinter> ?rhs)\<close>
          by (simp add: F_Ndet F_Seq F_After T_After assms(2)) blast
      qed
    qed
  next
    fix s X
    assume same_div : \<open>\<D> ((P \<^bold>; Q) after a) = \<D> ((P after a \<^bold>; Q) \<sqinter> ?rhs)\<close>
    assume \<open>(s, X) \<in> \<F> ((P after a \<^bold>; Q) \<sqinter> ?rhs)\<close>
    then consider \<open>(s, X) \<in> \<F> (P after a \<^bold>; Q)\<close> | \<open>(s, X) \<in> \<F> ?rhs\<close>
      by (simp add: F_Ndet) blast
    thus \<open>(s, X) \<in> \<F> ((P \<^bold>; Q) after a)\<close>
    proof cases
      assume \<open>(s, X) \<in> \<F> (P after a \<^bold>; Q)\<close>
      then consider \<open>s \<in> \<D> (P after a \<^bold>; Q)\<close>
        | \<open>(s, X \<union> range tick) \<in> \<F> (P after a)\<close> \<open>tF s\<close>
        | t1 t2 r where \<open>s = t1 @ t2\<close> \<open>t1 @ [\<checkmark>(r)] \<in> \<T> (P after a)\<close> \<open>(t2, X) \<in> \<F> Q\<close>
        by (simp add: F_Seq D_Seq) blast
      thus \<open>(s, X) \<in> \<F> ((P \<^bold>; Q) after a)\<close>
      proof cases
        show \<open>s \<in> \<D> (P after a \<^bold>; Q) \<Longrightarrow> (s, X) \<in> \<F> ((P \<^bold>; Q) after a)\<close>
          using same_div D_Ndet D_F by blast
      next
        show \<open>(s, X \<union> range tick) \<in> \<F> (P after a) \<Longrightarrow> tF s \<Longrightarrow> (s, X) \<in> \<F> ((P \<^bold>; Q) after a)\<close>
          by (simp add: F_After F_Seq initials_Seq assms(2) image_iff)
      next
        show \<open>s = t1 @ t2 \<Longrightarrow> t1 @ [\<checkmark>(r)] \<in> \<T> (P after a) \<Longrightarrow> (t2, X) \<in> \<F> Q
              \<Longrightarrow> (s, X) \<in> \<F> ((P \<^bold>; Q) after a)\<close> for t1 t2 r
          by (simp add: F_After T_After F_Seq initials_Seq
              assms(2) image_iff \<open>P \<noteq> \<bottom>\<close>) (metis Cons_eq_appendI)
      qed
    next
      from assms(1) \<open>P \<noteq> \<bottom>\<close> show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ((P \<^bold>; Q) after a)\<close>
        by (simp add: F_GlobalNdet F_After F_Seq initials_Seq image_iff split: if_split_asm)
          (simp add: initials_def, metis append_Nil)
    qed
  qed
qed


lemma not_initialL_not_skippable_or_not_initialR_After_Seq:
  \<open>ev a \<notin> P\<^sup>0 \<Longrightarrow> range tick \<inter> P\<^sup>0 = {} \<or> (\<forall>r. tick r \<in> P\<^sup>0 \<longrightarrow> ev a \<notin> Q\<^sup>0) \<Longrightarrow> 
   (P \<^bold>; Q) after a = \<Psi> (P \<^bold>; Q) a\<close> 
  by (simp add: not_skippable_or_not_initialR_After_Seq not_initial_After)


lemma After_Seq:
  \<open>(P \<^bold>; Q) after a =
   (  if range tick \<inter> P\<^sup>0 = {} \<or> (\<forall>r. \<checkmark>(r) \<in> P\<^sup>0 \<longrightarrow> ev a \<notin> Q\<^sup>0)
    then   if ev a \<in> P\<^sup>0 then P after a \<^bold>; Q else \<Psi> (P \<^bold>; Q) a
    else   if ev a \<in> P\<^sup>0
         then (P after a \<^bold>; Q) \<sqinter> Q after a
         else Q after a)\<close>
  by (simp add: not_skippable_or_not_initialR_After_Seq
      skippable_initialL_initialR_After_Seq skippable_not_initialL_After_Seq)


subsection \<open>@{const [source] After} Synchronization\<close>

text \<open>Now let's focus on \<^const>\<open>Sync\<close>.
      We want to obtain an equivalent of

      @{thm Mprefix_Sync_Mprefix}

      We will also divide the task.\<close>

text \<open>@{const [source] After} version of

      @{thm Mprefix_Sync_Mprefix_left
      [of \<open>{a}\<close> _ _ \<open>\<lambda>a. P\<close>, folded write0_def, simplified]}.\<close>

lemma initialL_not_initialR_not_in_After_Sync:
  \<open>(P \<lbrakk>S\<rbrakk> Q) after a = P after a \<lbrakk>S\<rbrakk> Q\<close>
  if initial_hyps: \<open>ev a \<in> P\<^sup>0\<close> \<open>ev a \<notin> Q\<^sup>0\<close> and notin: \<open>a \<notin> S\<close>
proof (subst Process_eq_spec_optimized, safe)
  { fix s X
    assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>(ev a # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close>
      and same_div : \<open>\<D> ((P \<lbrakk>S\<rbrakk> Q) after a) = \<D> (P after a \<lbrakk>S\<rbrakk> Q)\<close>
    have \<open>(s, X) \<in> \<F> (P after a \<lbrakk>S\<rbrakk> Q)\<close>
    proof (cases \<open>ev a # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>)
      case True
      hence \<open>s \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) after a)\<close>
        by (force simp add: D_After initials_Sync initial_hyps(1) assms(1, 2) notin)
      with D_F same_div show \<open>(s, X) \<in> \<F> (P after a \<lbrakk>S\<rbrakk> Q)\<close> by blast
    next
      case False
      with assms(3) obtain s_P s_Q X_P X_Q 
        where * : \<open>(s_P, X_P) \<in> \<F> P\<close> \<open>(s_Q, X_Q) \<in> \<F> Q\<close> 
          \<open>(ev a # s) setinterleaves ((s_P, s_Q), range tick \<union> ev ` S)\<close>
          \<open>X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` S) \<union> X_P \<inter> X_Q\<close>
        by (simp add: F_Sync D_Sync) blast
      have ** : \<open>s_P \<noteq> [] \<and> hd s_P = ev a \<and> s setinterleaves ((tl s_P, s_Q), range tick \<union> ev ` S)\<close>
        using *(3) apply (cases s_P; cases s_Q; simp add: notin image_iff split: if_split_asm)
        using "*"(2) initials_memI F_T initial_hyps(2) by blast+
      hence \<open>(tl s_P, X_P) \<in> \<F> (P after a) \<and> (s_Q, X_Q) \<in> \<F> Q \<and>
             s setinterleaves ((tl s_P, s_Q), range tick \<union> ev ` S) \<and>
             X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` S) \<union> X_P \<inter> X_Q\<close>
        by (simp add: F_After "**" initial_hyps(1))
          (metis "*"(1) "*"(2) "*"(4) "**" list.exhaust_sel)
      thus \<open>(s, X) \<in> \<F> (P after a \<lbrakk>S\<rbrakk> Q)\<close>
        by (simp add: F_Sync) blast
    qed
  } note * = this

  show \<open>\<D> ((P \<lbrakk>S\<rbrakk> Q) after a) = \<D> (P after a \<lbrakk>S\<rbrakk> Q) \<Longrightarrow>
        (s, X) \<in> \<F> ((P \<lbrakk>S\<rbrakk> Q) after a) \<Longrightarrow> (s, X) \<in> \<F> (P after a \<lbrakk>S\<rbrakk> Q)\<close> for s X
    by (simp add: "*" F_After initials_Sync initial_hyps notin image_iff split: if_split_asm)
      (metis After_BOT BOT_Sync CollectI D_BOT F_imp_front_tickFree Sync_BOT
        front_tickFree_Cons_iff front_tickFree_Nil is_processT8)
next

  fix s X
  assume same_div : \<open>\<D> ((P \<lbrakk>S\<rbrakk> Q) after a) = \<D> (P after a \<lbrakk>S\<rbrakk> Q)\<close>
  { assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>(s, X) \<in> \<F> (P after a \<lbrakk>S\<rbrakk> Q)\<close>
    from assms(3) consider
      \<open>\<exists>s_P s_Q X_P X_Q. (s_P, X_P) \<in> \<F> (P after a) \<and> (s_Q, X_Q) \<in> \<F> Q \<and>
                          s setinterleaves ((s_P, s_Q), range tick \<union> ev ` S) \<and> 
                          X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` S) \<union> X_P \<inter> X_Q\<close> |
      \<open>s \<in> \<D> (P after a \<lbrakk>S\<rbrakk> Q)\<close>
      by (simp add: F_Sync D_Sync) blast
    hence \<open>(ev a # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close>
    proof cases
      case 1
      then obtain s_P s_Q X_P X_Q
        where * : \<open>(ev a # s_P, X_P) \<in> \<F> P\<close> \<open>(s_Q, X_Q) \<in> \<F> Q\<close> 
          \<open>s setinterleaves ((s_P, s_Q), range tick \<union> ev ` S)\<close>
          \<open>X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` S) \<union> X_P \<inter> X_Q\<close>
        by (simp add: F_After initial_hyps(1)) blast
      have \<open>(s_Q, X_Q) \<in> \<F> Q \<and> 
            (ev a # s) setinterleaves ((ev a # s_P, s_Q), range tick \<union> ev ` S) \<and>
             X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` S) \<union> X_P \<inter> X_Q\<close>
        apply (simp add: *(2, 4))
        using *(3) by (cases s_Q; simp add: notin image_iff)
      with "*"(1) show \<open>(ev a # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close>
        by (simp add: F_Sync) blast
    next
      case 2
      from "2"[simplified same_div[symmetric]]
      have \<open>ev a # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close> 
        by (simp add: D_After initial_hyps(1) initials_Sync assms(1, 2) image_iff notin)
      with D_F show \<open>(ev a # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close> by blast
    qed
  }
  thus \<open>(s, X) \<in> \<F> (P after a \<lbrakk>S\<rbrakk> Q) \<Longrightarrow> (s, X) \<in> \<F> ((P \<lbrakk>S\<rbrakk> Q) after a)\<close> 
    by (simp add: F_After initials_Sync initial_hyps After_BOT F_BOT image_iff
        notin F_imp_front_tickFree front_tickFree_Cons_iff)
next

  { fix s
    assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>ev a # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
    from assms(3) obtain t u r v
      where * : \<open>ftF v\<close> \<open>tF  r \<or> v = []\<close> \<open>ev a # s = r @ v\<close>
        \<open>r setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
        \<open>t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> P\<close> by (simp add: D_Sync) blast
    have ** : \<open>r \<noteq> [] \<and> hd r = ev a\<close>
      by (metis "*"(3, 4, 5) BOT_iff_Nil_D assms(1, 2) empty_setinterleaving hd_append list.sel(1))
    hence *** : \<open>(t \<in> \<D> P \<and> u \<in> \<T> Q \<longrightarrow> t \<noteq> [] \<and> hd t = ev a \<and> 
                              tl r setinterleaves ((tl t, u), range tick \<union> ev ` S)) \<and> 
                 (t \<in> \<D> Q \<and> u \<in> \<T> P \<longrightarrow> u \<noteq> [] \<and> hd u = ev a \<and> 
                              tl r setinterleaves ((t, tl u), range tick \<union> ev ` S))\<close>
      using *(4) assms(1, 2)[simplified BOT_iff_Nil_D] initial_hyps[simplified initials_def] notin
      by (cases t; cases u; simp split: if_split_asm)
        (metis [[metis_verbose = false]] initials_memI D_T 
          list.sel(1) list.sel(3) initial_hyps(2))+
    from *(5) have \<open>s \<in> \<D> (P after a \<lbrakk>S\<rbrakk> Q)\<close>
    proof (elim disjE)
      assume \<open>t \<in> \<D> P \<and> u \<in> \<T> Q\<close>
      hence \<open>ftF v \<and> (tF  (tl r) \<or> v = []) \<and> s = tl r @ v \<and>
             tl r setinterleaves ((tl t, u), range tick \<union> ev ` S) \<and>
             tl t \<in> \<D> (P after a) \<and> u \<in> \<T> Q\<close>
        by (simp add: D_After initial_hyps(1))
          (metis "*"(1, 2, 3) "**" "***" list.collapse list.sel(3) 
            tickFree_tl tl_append2)
      thus \<open>s \<in> \<D> (P after a \<lbrakk>S\<rbrakk> Q)\<close> by (simp add: D_Sync) blast
    next
      assume \<open>t \<in> \<D> Q \<and> u \<in> \<T> P\<close>
      hence \<open>ftF v \<and> (tF  (tl r) \<or> v = []) \<and> s = tl r @ v \<and>
             tl r setinterleaves ((t, tl u), range tick \<union> ev ` S) \<and>
             t \<in> \<D> Q \<and> tl u \<in> \<T> (P after a)\<close>
        by (simp add: T_After initial_hyps(1))
          (metis "*"(1, 2, 3) "**" "***" list.collapse
            list.sel(3) tickFree_tl tl_append2)
      thus \<open>s \<in> \<D> (P after a \<lbrakk>S\<rbrakk> Q)\<close>
        by (simp add: D_Sync) blast
    qed
  } note * = this

  show \<open>s \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) after a) \<Longrightarrow> s \<in> \<D> (P after a \<lbrakk>S\<rbrakk> Q)\<close> for s
    by (simp add: D_After initials_Sync initial_hyps notin image_iff "*"
        split: if_split_asm)
      (elim disjE;
        simp add: After_BOT D_BOT, metis front_tickFree_Cons_iff front_tickFree_Nil)
next 

  fix s
  { assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>s \<in> \<D> (P after a \<lbrakk>S\<rbrakk> Q)\<close>
    from assms(3) obtain t u r v
      where * : \<open>ftF v\<close> \<open>tF  r \<or> v = []\<close> \<open>s = r @ v\<close> 
        \<open>r setinterleaves ((t, u), range tick \<union> ev ` S)\<close> 
        \<open>t \<in> \<D> (P after a) \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> (P after a)\<close>
      by (simp add: D_Sync) blast
    from "*"(5) have \<open>ev a # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
    proof (elim disjE)
      assume \<open>t \<in> \<D> (P after a) \<and> u \<in> \<T> Q\<close>
      with "*"(1, 2, 3, 4) initial_hyps(1)
      have ** : \<open>ftF v \<and> (tF  (ev a # r) \<or> v = []) \<and> s = r @ v \<and>
                 (ev a # r) setinterleaves ((ev a # t, u), range tick \<union> ev ` S) \<and>
                 ev a # t \<in> \<D> P \<and> u \<in> \<T> Q\<close>
        by (cases u; simp add: D_After notin image_iff)
      show \<open>ev a # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
        by (simp add: D_Sync) (metis "**" Cons_eq_appendI)
    next
      assume \<open>t \<in> \<D> Q \<and> u \<in> \<T> (P after a)\<close>
      with "*"(1, 2, 3, 4) initial_hyps(1)
      have ** : \<open>ftF v \<and> (tF  (ev a # r) \<or> v = []) \<and> s = r @ v \<and>
                 (ev a # r) setinterleaves ((t, ev a # u), range tick \<union> ev ` S) \<and>
                 t \<in> \<D> Q \<and> ev a # u \<in> \<T> P\<close>
        by (cases t; simp add: T_After notin image_iff)
      show \<open>ev a # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
        by (simp add: D_Sync) (metis "**" Cons_eq_appendI)
    qed
  }
  thus \<open>s \<in> \<D> (P after a \<lbrakk>S\<rbrakk> Q) \<Longrightarrow> s \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) after a)\<close>
    by (simp add: D_After initials_Sync initial_hyps After_BOT D_BOT
        notin image_iff D_imp_front_tickFree front_tickFree_Cons_iff)
qed



lemma not_initialL_in_After_Sync:
  \<open>ev a \<notin> P\<^sup>0 \<Longrightarrow> a \<in> S \<Longrightarrow> 
   (P \<lbrakk>S\<rbrakk> Q) after a = (if Q = \<bottom> then \<bottom> else \<Psi> (P \<lbrakk>S\<rbrakk> Q) a)\<close>
  by (simp add: After_BOT, intro impI)
    (subst not_initial_After, auto simp add: After_BOT initials_Sync)



text \<open>@{const [source] After} version of @{thm Mprefix_Sync_Mprefix_subset
      [of \<open>{a}\<close> _ \<open>{a}\<close> \<open>\<lambda>a. P\<close> \<open>\<lambda>a. Q\<close>, simplified, folded write0_def]}.\<close>

lemma initialL_initialR_in_After_Sync:
  \<open>(P \<lbrakk>S\<rbrakk> Q) after a = P after a \<lbrakk>S\<rbrakk> Q after a\<close> 
  if initial_hyps: \<open>ev a \<in> P\<^sup>0\<close> \<open>ev a \<in> Q\<^sup>0\<close> and inside: \<open>a \<in> S\<close>
proof (subst Process_eq_spec_optimized, safe)

  { fix s X
    assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>(ev a # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close> 
      and same_div : \<open>\<D> ((P \<lbrakk>S\<rbrakk> Q) after a) = \<D> (P after a \<lbrakk>S\<rbrakk> Q after a)\<close>
    from assms(3) consider
      \<open>\<exists>s_P s_Q X_P X_Q. (s_P, X_P) \<in> \<F> P \<and> (s_Q, X_Q) \<in> \<F> Q \<and>
                         (ev a # s) setinterleaves ((s_P, s_Q), range tick \<union> ev ` S) \<and> 
                         X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` S) \<union> X_P \<inter> X_Q\<close> |
      \<open>ev a # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
      by (simp add: F_Sync D_Sync) blast
    hence \<open>(s, X) \<in> \<F> (P after a \<lbrakk>S\<rbrakk> Q after a)\<close>
    proof cases
      case 1
      then obtain s_P s_Q X_P X_Q
        where * : \<open>(s_P, X_P) \<in> \<F> P\<close> \<open>(s_Q, X_Q) \<in> \<F> Q\<close>
          \<open>(ev a # s) setinterleaves ((s_P, s_Q), range tick \<union> ev ` S)\<close>
          \<open>X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` S) \<union> X_P \<inter> X_Q\<close> by blast
      from *(3) have \<open>s_P \<noteq> [] \<and> hd s_P = ev a \<and> s_Q \<noteq> [] \<and> hd s_Q = ev a \<and>
                      s setinterleaves ((tl s_P, tl s_Q), range tick \<union> ev ` S)\<close>
        using inside by (cases s_P; cases s_Q, auto simp add: split: if_split_asm)
      hence \<open>(tl s_P, X_P) \<in> \<F> (P after a) \<and> (tl s_Q, X_Q) \<in> \<F> (Q after a) \<and>
            s setinterleaves ((tl s_P, tl s_Q), range tick \<union> ev ` S) \<and>
            X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` S) \<union> X_P \<inter> X_Q\<close>
        using "*"(1, 2, 4) initial_hyps by (simp add: F_After) (metis list.exhaust_sel)
      thus \<open>(s, X) \<in> \<F> (P after a \<lbrakk>S\<rbrakk> Q after a)\<close>
        by (simp add: F_Sync) blast
    next
      assume \<open>ev a # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
      hence \<open>s \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) after a)\<close> 
        by (force simp add: D_After initials_Sync initial_hyps assms(1, 2))
      from this[simplified same_div] D_F
      show \<open>(s, X) \<in> \<F> (P after a \<lbrakk>S\<rbrakk> Q after a)\<close> by blast
    qed
  } note * = this

  show \<open>\<D> ((P \<lbrakk>S\<rbrakk> Q) after a) = \<D> (P after a \<lbrakk>S\<rbrakk> Q after a) \<Longrightarrow>
        (s, X) \<in> \<F> ((P \<lbrakk>S\<rbrakk> Q) after a) \<Longrightarrow> (s, X) \<in> \<F> (P after a \<lbrakk>S\<rbrakk> Q after a)\<close> for s X
    by (simp add: "*" F_After initials_Sync initial_hyps image_iff split: if_split_asm)
      (metis After_BOT BOT_Sync BOT_iff_Nil_D CollectI D_BOT F_imp_front_tickFree
        Sync_BOT front_tickFree_Cons_iff is_processT8)
next

  fix s X
  assume same_div : \<open>\<D> ((P \<lbrakk>S\<rbrakk> Q) after a) = \<D> (P after a \<lbrakk>S\<rbrakk> Q after a)\<close>
  { assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>(s, X) \<in> \<F> (P after a \<lbrakk>S\<rbrakk> Q after a)\<close>
    from assms(3) consider 
      \<open>\<exists>s_P s_Q X_P X_Q. (ev a # s_P, X_P) \<in> \<F> P \<and> (ev a # s_Q, X_Q) \<in> \<F> Q \<and>
                         s setinterleaves ((s_P, s_Q), range tick \<union> ev ` S) \<and> 
                         X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` S) \<union> X_P \<inter> X_Q\<close> |
      \<open>s \<in> \<D> (P after a \<lbrakk>S\<rbrakk> Q after a)\<close>
      by (simp add: F_Sync D_Sync F_After initial_hyps) blast
    hence \<open>(ev a # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close>
    proof cases
      case 1
      then obtain s_P s_Q X_P X_Q 
        where * : \<open>(ev a # s_P, X_P) \<in> \<F> P\<close> \<open>(ev a # s_Q, X_Q) \<in> \<F> Q\<close> 
          \<open>s setinterleaves ((s_P, s_Q), range tick \<union> ev ` S)\<close>
          \<open>X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` S) \<union> X_P \<inter> X_Q\<close> by blast
      have ** : \<open>(ev a # s) setinterleaves ((ev a # s_P, ev a # s_Q), range tick \<union> ev ` S)\<close>
        by (simp add: inside "*"(3))
      show \<open>(ev a # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close>
        apply (simp add: F_Sync)
        using "*"(1, 2, 4) "**" by blast
    next
      assume \<open>s \<in> \<D> (P after a \<lbrakk>S\<rbrakk> Q after a)\<close>
      with same_div[symmetric] have \<open>ev a # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
        by (simp add: D_After initial_hyps initials_Sync assms(1, 2) image_iff)
      with D_F show \<open>(ev a # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close> by blast
    qed
  }
  thus \<open>(s, X) \<in> \<F> (P after a \<lbrakk>S\<rbrakk> Q after a) \<Longrightarrow> (s, X) \<in> \<F> ((P \<lbrakk>S\<rbrakk> Q) after a)\<close>
    by (simp add: F_After initials_Sync initial_hyps F_BOT image_iff
        F_imp_front_tickFree front_tickFree_Cons_iff)
next

  { fix s
    assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>ev a # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close> 
    from assms(3) obtain t u r v
      where * : \<open>ftF v\<close> \<open>tF  r \<or> v = []\<close> \<open>ev a # s = r @ v\<close>
        \<open>r setinterleaves ((t, u), range tick \<union> ev ` S)\<close> 
        \<open>t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> P\<close> by (simp add: D_Sync) blast
    have ** : \<open>r \<noteq> [] \<and> hd r = ev a \<and> t \<noteq> [] \<and> hd t = ev a \<and> u \<noteq> [] \<and> hd u = ev a \<and>
               tl r setinterleaves ((tl t, tl u), range tick \<union> ev ` S)\<close>
      using *(3, 4, 5) inside assms(1, 2)[simplified BOT_iff_Nil_D]
      by (cases t; cases u) (auto simp add: image_iff split: if_split_asm)
    have \<open>(tF  (tl r) \<or> v = []) \<and> s = tl r @ v \<and>
          (tl t \<in> \<D> (P after a) \<and> tl u \<in> \<T> (Q after a) \<or> 
           tl t \<in> \<D> (Q after a) \<and> tl u \<in> \<T> (P after a))\<close>
      using "*"(2, 3, 5) "**" apply (simp add: D_After initial_hyps T_After)
      by (metis list.collapse list.sel(3) tickFree_tl tl_append2)
    with "*"(1) "**" have \<open>s \<in> \<D> (P after a \<lbrakk>S\<rbrakk> Q after a)\<close> by (simp add: D_Sync) blast
  } note * = this

  show \<open>s \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) after a) \<Longrightarrow> s \<in> \<D> (P after a \<lbrakk>S\<rbrakk> Q after a)\<close> for s
    by (simp add: "*" D_After initials_Sync initial_hyps image_iff split: if_split_asm)
      (metis After_BOT BOT_Sync BOT_iff_Nil_D D_BOT Sync_BOT front_tickFree_Cons_iff mem_Collect_eq)
next

  fix s
  { assume \<open>s \<in> \<D> (P after a \<lbrakk>S\<rbrakk> Q after a)\<close>
    from this obtain t u r v
      where * : \<open>ftF v\<close> \<open>tF  r \<or> v = []\<close> \<open>s = r @ v\<close>
        \<open>r setinterleaves ((t, u), range tick \<union> ev ` S)\<close> 
        \<open>ev a # t \<in> \<D> P \<and> ev a # u \<in> \<T> Q \<or> ev a # t \<in> \<D> Q \<and> ev a # u \<in> \<T> P\<close> 
      by (simp add: D_Sync After_projs initial_hyps) blast
    have ** : \<open>(ev a # r) setinterleaves ((ev a # t, ev a # u), range tick \<union> ev ` S)\<close>
      by (simp add: inside "*"(4))
    have \<open>ev a # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
      by (simp add: D_Sync inside)
        (metis "*"(1, 2, 3, 5) "**" Cons_eq_appendI event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) tickFree_Cons_iff)
  }
  thus \<open>s \<in> \<D> (P after a \<lbrakk>S\<rbrakk> Q after a) \<Longrightarrow> s \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) after a)\<close>
    by (simp add: D_After initials_Sync initial_hyps After_BOT D_BOT inside)
qed



text \<open>@{const [source] After} version of
     
      @{thm Mprefix_Sync_Mprefix_indep
      [of \<open>{e}\<close> _ \<open>{e}\<close> \<open>\<lambda>a. P\<close> \<open>\<lambda>a. Q\<close>, simplified, folded write0_def]}.\<close>

lemma initialL_initialR_not_in_After_Sync: 
  \<open>(P \<lbrakk>S\<rbrakk> Q) after a = (P after a \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after a)\<close>
  if initial_hyps: \<open>ev a \<in> P\<^sup>0\<close> \<open>ev a \<in> Q\<^sup>0\<close> and notin: \<open>a \<notin> S\<close> for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (subst Process_eq_spec_optimized, safe)

  { fix P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and s X s_P s_Q X_P X_Q
    assume assms : \<open>(s_P, X_P) \<in> \<F> P\<close> \<open>(s_Q, X_Q) \<in> \<F> Q\<close> 
      \<open>X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` S) \<union> X_P \<inter> X_Q\<close>
      \<open>s_P \<noteq> []\<close> \<open>hd s_P = ev a\<close>
      \<open>s setinterleaves ((tl s_P, s_Q), range tick \<union> ev ` S)\<close>
      \<open>ev a \<in> P\<^sup>0\<close>
    from assms(1, 4, 5, 7) have \<open>(tl s_P, X_P) \<in> \<F> (P after a)\<close>
      by (simp add: F_After) (metis list.exhaust_sel)
    with assms(2, 3, 6) have \<open>(s, X) \<in> \<F> (P after a \<lbrakk>S\<rbrakk> Q)\<close>
      by (simp add: F_Sync) blast
  } note * = this

  { fix s X
    assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>(ev a # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close>
      and same_div : \<open>\<D> ((P \<lbrakk>S\<rbrakk> Q) after a) = \<D> ((P after a \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after a))\<close>
    from assms(3) consider
      \<open>\<exists>s_P s_Q X_P X_Q. (s_P, X_P) \<in> \<F> P \<and> (s_Q, X_Q) \<in> \<F> Q \<and>
                          (ev a # s) setinterleaves ((s_P, s_Q), range tick \<union> ev ` S) \<and> 
                          X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` S) \<union> X_P \<inter> X_Q\<close> |
      \<open>s \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) after a)\<close>
      by (simp add: F_Sync D_After D_Sync initials_Sync assms(1, 2) initial_hyps image_iff) blast
    hence \<open>(s, X) \<in> \<F> ((P after a \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after a))\<close>
    proof cases
      case 1
      then obtain s_P s_Q X_P X_Q
        where ** : \<open>(s_P, X_P) \<in> \<F> P\<close> \<open>(s_Q, X_Q) \<in> \<F> Q\<close> 
          \<open>(ev a # s) setinterleaves ((s_P, s_Q), range tick \<union> ev ` S)\<close>
          \<open>X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` S) \<union> X_P \<inter> X_Q\<close> by blast
      have \<open>s_P \<noteq> [] \<and> hd s_P = ev a \<and> s setinterleaves ((tl s_P, s_Q), range tick \<union> ev ` S) \<or>
            s_Q \<noteq> [] \<and> hd s_Q = ev a \<and> s setinterleaves ((s_P, tl s_Q), range tick \<union> ev ` S)\<close>
        using **(3) by (cases s_P; cases s_Q; simp add: notin image_iff split: if_split_asm) blast
      thus \<open>(s, X) \<in> \<F> ((P after a \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after a))\<close>
        apply (elim disjE; simp add: F_Ndet)
        using "*" "**"(1, 2, 4) initial_hyps(1) apply blast
        apply (rule disjI2, subst Sync_commute, rule *[OF **(2, 1)])
        by (simp_all add: "**"(4) Int_commute Un_commute Sync_commute
            setinterleaving_sym initial_hyps(2))
    next
      assume \<open>s \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) after a)\<close>
      from this[simplified same_div] D_F
      show \<open>(s, X) \<in> \<F> ((P after a \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after a))\<close> by blast
    qed
  } note ** = this

  show \<open>\<D> ((P \<lbrakk>S\<rbrakk> Q) after a) = \<D> ((P after a \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after a)) \<Longrightarrow>
        (s, X) \<in> \<F> ((P \<lbrakk>S\<rbrakk> Q) after a) \<Longrightarrow> (s, X) \<in> \<F> ((P after a \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after a))\<close> for s X
    by (simp add: "**" F_After initials_Sync initial_hyps image_iff split: if_split_asm)
      (metis After_BOT BOT_Sync BOT_iff_Nil_D D_BOT F_imp_front_tickFree Sync_commute
        front_tickFree_Cons_iff is_processT8 mem_Collect_eq)
next

  { fix s X P Q
    assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>(s, X) \<in> \<F> (P after a \<lbrakk>S\<rbrakk> Q)\<close> \<open>ev a \<in> P\<^sup>0\<close>
      and same_div : \<open>\<D> ((P \<lbrakk>S\<rbrakk> Q) after a) = \<D> ((P after a \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after a))\<close>
    from assms(3)[simplified F_Sync, simplified] consider
      s_P s_Q X_P X_Q where \<open>(ev a # s_P, X_P) \<in> \<F> P\<close> \<open>(s_Q, X_Q) \<in> \<F> Q\<close>
      \<open>s setinterleaves ((s_P, s_Q), range tick \<union> ev ` S)\<close>
      \<open>X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` S) \<union> X_P \<inter> X_Q\<close>
    | \<open>s \<in> \<D> (P after a \<lbrakk>S\<rbrakk> Q)\<close>
      by (simp add: F_Sync F_After assms(4) D_Sync) blast
    hence \<open>(ev a # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close>
    proof cases
      fix s_P s_Q X_P X_Q
      assume * : \<open>(ev a # s_P, X_P) \<in> \<F> P\<close> \<open>(s_Q, X_Q) \<in> \<F> Q\<close>
        \<open>s setinterleaves ((s_P, s_Q), range tick \<union> ev ` S)\<close>
        \<open>X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` S) \<union> X_P \<inter> X_Q\<close>
      have \<open>(ev a # s) setinterleaves ((ev a # s_P, s_Q), range tick \<union> ev ` S)\<close>
        using "*"(3) by (cases s_Q; simp add: notin image_iff)
      with "*"(1, 2, 4) show \<open>(ev a # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close>
        by (simp add: F_Sync) blast
    next
      assume \<open>s \<in> \<D> (P after a \<lbrakk>S\<rbrakk> Q)\<close>
      hence \<open>s \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) after a)\<close> using same_div[simplified D_Ndet] by fast
      hence \<open>(s, X) \<in> \<F> ((P \<lbrakk>S\<rbrakk> Q) after a)\<close> by (simp add: is_processT8)
      thus \<open>(ev a # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close> 
        by (simp add: F_After initials_Sync assms(1, 2, 4) notin image_iff)
    qed
  } note * = this

  show \<open>\<D> ((P \<lbrakk>S\<rbrakk> Q) after a) = \<D> ((P after a \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after a)) \<Longrightarrow>
        (s, X) \<in> \<F> ((P after a \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after a)) \<Longrightarrow> (s, X) \<in> \<F> ((P \<lbrakk>S\<rbrakk> Q) after a)\<close> for s X
    apply (simp add: F_After initials_Sync initial_hyps F_BOT image_iff
        F_imp_front_tickFree front_tickFree_Cons_iff)
    apply (rule impI, simp add: F_Ndet, elim disjE conjE)
    by (simp add: "*" initial_hyps(1))
      (metis "*" Ndet_commute Sync_commute initial_hyps(2))
next

  { fix s
    assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>ev a # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
    from assms(3) obtain t u r v
      where ** : \<open>ftF v\<close> \<open>tF  r \<or> v = []\<close> \<open>ev a # s = r @ v\<close>
        \<open>r setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
        \<open>t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> P\<close> by (simp add: D_Sync) blast
    have *** : \<open>r \<noteq> []\<close> using "**"(4, 5) BOT_iff_Nil_D assms(1, 2) empty_setinterleaving by blast
    have \<open>t \<noteq> [] \<and> hd t = ev a \<and> tl r setinterleaves ((tl t, u), range tick \<union> ev ` S) \<or>
          u \<noteq> [] \<and> hd u = ev a \<and> tl r setinterleaves ((t, tl u), range tick \<union> ev ` S)\<close>
      using **(3, 4) by (cases t; cases u, auto simp add: *** notin split: if_split_asm)
    with "**"(5) have \<open>s \<in> \<D> ((P after a \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after a))\<close>
    proof (elim disjE)
      assume * : \<open>t \<in> \<D> P \<and> u \<in> \<T> Q\<close>
        \<open>t \<noteq> [] \<and> hd t = ev a \<and> tl r setinterleaves ((tl t, u), range tick \<union> ev ` S)\<close>
      hence \<open>s = tl r @ v \<and> tl t \<in> \<D> (P after a) \<and> u \<in> \<T> Q\<close>
        using "**"(3) "***" initial_hyps(1) apply (simp add: D_After, intro conjI)
        by (metis list.sel(3) tl_append2) (metis list.collapse)
      thus \<open>s \<in> \<D> ((P after a \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after a))\<close>
        using "*"(2) "**"(1, 2) tickFree_tl by (simp add: D_Ndet D_Sync) blast
    next
      assume * : \<open>t \<in> \<D> P \<and> u \<in> \<T> Q\<close>
        \<open>u \<noteq> [] \<and> hd u = ev a \<and> tl r setinterleaves ((t, tl u), range tick \<union> ev ` S)\<close>
      hence \<open>s = tl r @ v \<and> t \<in> \<D> P \<and> tl u \<in> \<T> (Q after a)\<close>
        using "**"(3) initial_hyps(2) "***" apply (simp add: T_After, intro conjI)
        by (metis list.sel(3) tl_append2) (metis list.collapse)
      thus \<open>s \<in> \<D> ((P after a \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after a))\<close>
        using "*"(2) "**"(1, 2) tickFree_tl by (simp add: D_Ndet D_Sync) blast
    next
      assume * : \<open>t \<in> \<D> Q \<and> u \<in> \<T> P\<close>
        \<open>t \<noteq> [] \<and> hd t = ev a \<and> tl r setinterleaves ((tl t, u), range tick \<union> ev ` S)\<close>
      hence \<open>s = tl r @ v \<and> tl t \<in> \<D> (Q after a) \<and> u \<in> \<T> P\<close>
        using "**"(1, 2, 3) initial_hyps apply (simp add: D_After, intro conjI)
        by (metis "***" list.sel(3) tl_append2) (metis list.collapse)
      thus \<open>s \<in> \<D> ((P after a \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after a))\<close>
        using "*"(2) "**"(1, 2) tickFree_tl by (simp add: D_Ndet D_Sync) blast
    next
      assume * : \<open>t \<in> \<D> Q \<and> u \<in> \<T> P\<close>
        \<open>u \<noteq> [] \<and> hd u = ev a \<and> tl r setinterleaves ((t, tl u), range tick \<union> ev ` S)\<close>
      hence \<open>s = tl r @ v \<and> t \<in> \<D> Q \<and> tl u \<in> \<T> (P after a)\<close>
        using "**"(1, 2, 3) initial_hyps apply (simp add: T_After, intro conjI)
        by (metis "***" list.sel(3) tl_append2) (metis list.collapse)
      thus \<open>s \<in> \<D> ((P after a \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after a))\<close>
        using "*"(2) "**"(1, 2) tickFree_tl by (simp add: D_Ndet D_Sync) blast
    qed
  } note * = this

  show \<open>s \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) after a) \<Longrightarrow> s \<in> \<D> ((P after a \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after a))\<close> for s
    by (simp add: "*" D_After initials_Sync initial_hyps image_iff split: if_split_asm)
      (metis D_BOT Ndet_is_BOT_iff Sync_is_BOT_iff
        front_tickFree_Cons_iff front_tickFree_Nil mem_Collect_eq)
next

  { fix s P Q
    assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>s \<in> \<D> ((P after a \<lbrakk>S\<rbrakk> Q))\<close> \<open>ev a \<in> P\<^sup>0\<close>
    from assms(3)[simplified D_Sync, simplified] obtain t u r v
      where * : \<open>ftF v\<close> \<open>tF  r \<or> v = []\<close> \<open>s = r @ v\<close> 
        \<open>r setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
        \<open>ev a # t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> ev a # u \<in> \<T> P\<close>
      by (simp add: D_Sync After_projs assms(4)) blast
    from "*"(5) have \<open>ev a # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
    proof (elim disjE)
      assume ** : \<open>ev a # t \<in> \<D> P \<and> u \<in> \<T> Q\<close>
      have *** : \<open>(ev a # r) setinterleaves ((ev a # t, u), range tick \<union> ev ` S)\<close>
        using "*"(4) by (cases u; simp add: notin image_iff "*"(1, 2, 3))
      show \<open>ev a # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
        by (simp add: D_Sync)
          (metis "*"(1, 2, 3) "**" "***" append_Cons event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) tickFree_Cons_iff)
    next
      assume ** : \<open>t \<in> \<D> Q \<and> ev a # u \<in> \<T> P\<close>
      have *** : \<open>(ev a # r) setinterleaves ((t, ev a # u), range tick \<union> ev ` S)\<close>
        using "*"(4) by (cases t; simp add: notin image_iff "*"(1, 2, 3))
      show \<open>ev a # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
        by (simp add: D_Sync)
          (metis "*"(1, 2, 3) "**" "***" append_Cons event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) tickFree_Cons_iff)
    qed
  } note * = this 

  show \<open>s \<in> \<D> ((P after a \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after a)) \<Longrightarrow> s \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) after a)\<close> for s
    by (simp add: D_After initials_Sync D_BOT image_iff notin)
      (metis "*" D_Ndet D_imp_front_tickFree Sync_commute
        UnE event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) front_tickFree_Cons_iff initial_hyps)

qed


lemma not_initialL_not_initialR_After_Sync: \<open>(P \<lbrakk>S\<rbrakk> Q) after a = \<Psi> (P \<lbrakk>S\<rbrakk> Q) a\<close> 
  if initial_hyps: \<open>ev a \<notin> P\<^sup>0\<close> \<open>ev a \<notin> Q\<^sup>0\<close>
  apply (subst not_initial_After, simp add: initials_Sync)
  using initials_BOT initial_hyps by auto


text \<open>Finally, the monster theorem !\<close>

theorem After_Sync: 
  \<open>(P \<lbrakk>S\<rbrakk> Q) after a =
   (  if P = \<bottom> \<or> Q = \<bottom> then \<bottom>
    else   if ev a \<in> P\<^sup>0 \<inter> Q\<^sup>0
         then   if a \<in> S then P after a \<lbrakk>S\<rbrakk> Q after a
              else (P after a \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after a)
         else   if ev a \<in> P\<^sup>0 \<and> a \<notin> S then P after a \<lbrakk>S\<rbrakk> Q
              else   if ev a \<in> Q\<^sup>0 \<and> a \<notin> S then P \<lbrakk>S\<rbrakk> Q after a
                   else \<Psi> (P \<lbrakk>S\<rbrakk> Q) a)\<close>
  by (simp add: After_BOT initialL_initialR_in_After_Sync initialL_initialR_not_in_After_Sync)
    (metis initialL_not_initialR_not_in_After_Sync Sync_commute
      not_initialL_in_After_Sync not_initialL_not_initialR_After_Sync)



subsection \<open>@{const [source] After} Hiding Operator\<close>

text \<open>\<^term>\<open>P \ A\<close> is harder to deal with, we will only obtain refinements results.\<close>

lemma Hiding_FD_Hiding_After_if_initial_inside:
  \<open>a \<in> A \<Longrightarrow> P \ A \<sqsubseteq>\<^sub>F\<^sub>D P after a \ A\<close>
  and After_Hiding_FD_Hiding_After_if_initial_notin:
  \<open>a \<notin> A \<Longrightarrow> (P \ A) after a \<sqsubseteq>\<^sub>F\<^sub>D P after a \ A\<close>
  if initial: \<open>ev a \<in> P\<^sup>0\<close>
   supply initial' = initial_notin_imp_initial_Hiding[OF initial]
proof -
  { fix s
    assume \<open>s \<in> \<D> (P after a \ A)\<close>
    with D_Hiding obtain t u 
      where * : \<open>ftF u\<close> \<open>tF t\<close> \<open>s = trace_hide t (ev ` A) @ u\<close> 
        \<open>t \<in> \<D> (P after a) \<or> (\<exists> f. isInfHiddenRun f (P after a) A \<and> t \<in> range f)\<close> 
      by blast
    from "*"(4) have \<open>s \<in> (if a \<in> A then \<D> (P \ A) else \<D> ((P \ A) after a))\<close>
    proof (elim disjE)
      assume \<open>t \<in> \<D> (P after a)\<close>
      hence ** : \<open>ev a # t \<in> \<D> P\<close> by (simp add: D_After initial)
      show  \<open>s \<in> (if a \<in> A then \<D> (P \ A) else \<D> ((P \ A) after a))\<close>
      proof (split if_split, intro conjI impI)
        assume \<open>a \<in> A\<close>
        with "*"(3) have *** : \<open>s = trace_hide (ev a # t) (ev ` A) @ u\<close> by simp
        show \<open>s \<in> \<D> (P \ A)\<close>
          by (simp add: D_Hiding)
            (metis "*"(1, 2) "**" "***" event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) tickFree_Cons_iff)
      next
        assume \<open>a \<notin> A\<close>
        with "*"(3) have *** : \<open>ev a # s = trace_hide (ev a # t) (ev ` A) @ u\<close>
          by (simp add: image_iff)
        have \<open>ev a # s \<in> \<D> (P \ A)\<close>
          by (simp add: D_Hiding)
            (metis "*"(1, 2) "**" "***" event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) tickFree_Cons_iff)
        thus \<open>s \<in> \<D> ((P \ A) after a)\<close> by (simp add: D_After initial' \<open>a \<notin> A\<close>)
      qed
    next
      assume \<open>\<exists>f. isInfHiddenRun f (P after a) A \<and> t \<in> range f\<close>
      then obtain f where \<open>isInfHiddenRun f (P after a) A\<close> \<open>t \<in> range f\<close> by blast
      hence ** : \<open>isInfHiddenRun (\<lambda>i. ev a # f i) P A \<and>
                  ev a # t \<in> range (\<lambda>i. ev a # f i)\<close>
        by (simp add: monotone_on_def T_After initial) blast
      show \<open>s \<in> (if a \<in> A then \<D> (P \ A) else \<D> ((P \ A) after a))\<close>
      proof (split if_split, intro conjI impI)
        assume \<open>a \<in> A\<close>
        with "*"(3) have *** : \<open>s = trace_hide (ev a # t) (ev ` A) @ u\<close> by simp
        show \<open>s \<in> \<D> (P \ A)\<close>
          by (simp add: D_Hiding)
            (metis "*"(1, 2) "**" "***" event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) tickFree_Cons_iff)
      next
        assume \<open>a \<notin> A\<close>
        with "*"(3) have *** : \<open>ev a # s = trace_hide (ev a # t) (ev ` A) @ u\<close>
          by (simp add: image_iff)
        have \<open>ev a # s \<in> \<D> (P \ A)\<close>
          by (simp add: D_Hiding)
            (metis "*"(1, 2) "**" "***" event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) tickFree_Cons_iff)
        thus \<open>s \<in> \<D> ((P \ A) after a)\<close> by (simp add: D_After initial' \<open>a \<notin> A\<close>)
      qed
    qed
  } note div_ref = this

  { fix s X
    assume \<open>(s, X) \<in> \<F> (P after a \ A)\<close>
    with F_Hiding D_Hiding consider 
      \<open>\<exists>t. s = trace_hide t (ev ` A) \<and> (t, X \<union> ev ` A) \<in> \<F> (P after a)\<close> 
      | \<open>s \<in> \<D> (P after a \ A)\<close> by blast
    hence \<open>(s, X) \<in> (if a \<in> A then \<F> (P \ A) else \<F> ((P \ A) after a))\<close>
    proof cases
      assume \<open>\<exists>t. s = trace_hide t (ev ` A) \<and> (t, X \<union> ev ` A) \<in> \<F> (P after a)\<close>
      then obtain t where * : \<open>s = trace_hide t (ev ` A)\<close> \<open>(ev a # t, X \<union> ev ` A) \<in> \<F> P\<close>
        by (simp add: F_After initial) blast
      show \<open>(s, X) \<in> (if a \<in> A then \<F> (P \ A) else \<F> ((P \ A) after a))\<close>
      proof (split if_split, intro conjI impI)
        from "*" show \<open>a \<in> A \<Longrightarrow> (s, X) \<in> \<F> (P \ A)\<close>
          by (simp add: F_Hiding) (metis filter.simps(2) image_eqI)
      next
        assume \<open>a \<notin> A\<close>
        with "*"(1) have ** : \<open>ev a # s = trace_hide (ev a # t) (ev ` A)\<close>
          by (simp add: image_iff)
        show \<open>(s, X) \<in> \<F> ((P \ A) after a)\<close>
          by (simp add: F_After initial' \<open>a \<notin> A\<close> F_Hiding) (blast intro: "*"(2) "**")
      qed
    next
      show \<open>s \<in> \<D> (P after a \ A) \<Longrightarrow> (s, X) \<in> (if a \<in> A then \<F> (P \ A) else \<F> ((P \ A) after a))\<close>
        by (drule div_ref, simp split: if_split_asm; use D_F in blast)
    qed 
  } note fail_ref = this

  show \<open>a \<in> A \<Longrightarrow> P \ A \<sqsubseteq>\<^sub>F\<^sub>D P after a \ A\<close>
    and \<open>a \<notin> A \<Longrightarrow> (P \ A) after a \<sqsubseteq>\<^sub>F\<^sub>D P after a \ A\<close>
    unfolding failure_divergence_refine_def failure_refine_def divergence_refine_def
    using div_ref fail_ref by auto
qed


lemmas Hiding_F_Hiding_After_if_initial_inside = 
  Hiding_FD_Hiding_After_if_initial_inside[THEN leFD_imp_leF]
  and After_Hiding_F_Hiding_After_if_initial_notin = 
  After_Hiding_FD_Hiding_After_if_initial_notin[THEN leFD_imp_leF]
  and Hiding_D_Hiding_After_if_initial_inside = 
  Hiding_FD_Hiding_After_if_initial_inside[THEN leFD_imp_leD]
  and After_Hiding_D_Hiding_After_if_initial_notin = 
  After_Hiding_FD_Hiding_After_if_initial_notin[THEN leFD_imp_leD]
  and Hiding_T_Hiding_After_if_initial_inside = 
  Hiding_FD_Hiding_After_if_initial_inside[THEN leFD_imp_leF, THEN leF_imp_leT]   
  and After_Hiding_T_Hiding_After_if_initial_notin = 
  After_Hiding_FD_Hiding_After_if_initial_notin[THEN leFD_imp_leF, THEN leF_imp_leT]

corollary Hiding_DT_Hiding_After_if_initial_inside:
  \<open>ev a \<in> P\<^sup>0 \<Longrightarrow> a \<in> A \<Longrightarrow> P \ A \<sqsubseteq>\<^sub>D\<^sub>T P after a \ A\<close>
  and After_Hiding_DT_Hiding_After_if_initial_notin: 
  \<open>ev a \<in> P\<^sup>0 \<Longrightarrow> a \<notin> A \<Longrightarrow> (P \ A) after a \<sqsubseteq>\<^sub>D\<^sub>T P after a \ A\<close>
  by (simp add: Hiding_D_Hiding_After_if_initial_inside 
      Hiding_T_Hiding_After_if_initial_inside leD_leT_imp_leDT)
    (simp add: After_Hiding_D_Hiding_After_if_initial_notin 
      After_Hiding_T_Hiding_After_if_initial_notin leD_leT_imp_leDT)

end

(* text \<open>This is the best we can obtain: even by restricting ourselves to two events, 
      we can already construct a counterexample.\<close>

lemma defines P_def: \<open>P \<equiv> (Suc 0 \<rightarrow> (0 \<rightarrow> STOP)) \<sqinter> (0 \<rightarrow> SKIP)\<close> 
          and B_def: \<open>B \<equiv> {Suc 0}\<close> and e_def : \<open>e \<equiv> 0\<close> and f_def: \<open>f \<equiv> Suc 0\<close>
        shows \<open>ev e \<in> P\<^sup>0 \<and> f \<in> B \<and> P \ B \<noteq> P after f \ B\<close>
          and \<open>ev e \<in> P\<^sup>0 \<and> e \<notin> B \<and> (P \ B) after e \<noteq> P after e \ B\<close> 
  unfolding e_def f_def P_def B_def
  apply (simp_all add: initials_Ndet initials_write0)
  apply (simp_all add: After_Ndet initials_write0 After_write0 Hiding_set_SKIP)
  apply (simp_all add: Hiding_Ndet After_Ndet initials_write0 After_write0 Hiding_set_SKIP 
                       Hiding_set_STOP no_Hiding_write0 Hiding_write0)
  by (metis After_write0 Ndet_is_STOP_iff SKIP_Neq_STOP write0_Ndet)
     (metis mono_Ndet_FD_right Ndet_commute SKIP_FD_iff SKIP_Neq_STOP STOP_FD_iff) *)

subsection \<open>Renaming is tricky\<close>

text \<open>In all generality, \<^const>\<open>Renaming\<close> takes a process
      @{term [show_types, source] \<open>P :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>}, a function
      @{term [show_types, source ] \<open>f :: 'a \<Rightarrow> 'b\<close>}, a function
      @{term [show_types, source ] \<open>g :: 'r \<Rightarrow> 's\<close>}, and returns 
      @{term [show_types, source] \<open>Renaming P f g :: ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>}.
      But if we try to write and prove a lemma \<open>After_Renaming\<close> like we did for
      the other operators, the mechanism of the locale \<^locale>\<open>After\<close> would
      constrain @{term [show_types, source] \<open>f :: 'a \<Rightarrow> 'a\<close>} and
      @{term [show_types, source] \<open>g :: 'r \<Rightarrow> 'r\<close>}.\<close>

text \<open>We solve this issue with a trick: we duplicate the locale,
      instantiating each one with a different free type.\<close>

locale AfterDuplicated = After\<^sub>\<alpha> : After \<Psi>\<^sub>\<alpha> + After\<^sub>\<beta> : After \<Psi>\<^sub>\<beta>
  for \<Psi>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> 
    and \<Psi>\<^sub>\<beta> :: \<open>[('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'b] \<Rightarrow> ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
begin

notation After\<^sub>\<alpha>.After (infixl \<open>after\<^sub>\<alpha>\<close> 86)
notation After\<^sub>\<beta>.After (infixl \<open>after\<^sub>\<beta>\<close> 86)

lemma After_Renaming:
  \<open>Renaming P f g after\<^sub>\<beta> b =
  \<comment>\<open>We highlight the fact that @{term [show_types, source] \<open>f :: 'a \<Rightarrow> 'b\<close>}\<close>
   (  if P = \<bottom> then \<bottom>
    else   if \<exists>a. ev a \<in> P\<^sup>0 \<and> f a = b
         then \<sqinter> a\<in>{a. ev a \<in> P\<^sup>0 \<and> f a = b}. Renaming (P after\<^sub>\<alpha> a) f g
         else \<Psi>\<^sub>\<beta> (Renaming P f g) b)\<close>
  (is \<open>?lhs = (if P = \<bottom> then \<bottom>
                else if \<exists>a. ev a \<in> P\<^sup>0 \<and> f a = b then ?rhs else _)\<close>)

proof (split if_split, intro conjI impI)
  show \<open>P = \<bottom> \<Longrightarrow> ?lhs= \<bottom>\<close> by (simp add: After\<^sub>\<beta>.After_BOT)
next
  assume non_BOT: \<open>P \<noteq> \<bottom>\<close>
  show \<open>?lhs = (if \<exists>a. ev a \<in> P\<^sup>0 \<and> f a = b then ?rhs else \<Psi>\<^sub>\<beta> (Renaming P f g) b)\<close>
  proof (split if_split, intro conjI impI)
    show \<open>\<nexists>a. ev a \<in> P\<^sup>0 \<and> f a = b \<Longrightarrow> ?lhs = \<Psi>\<^sub>\<beta> (Renaming P f g) b\<close>
      by (subst After\<^sub>\<beta>.not_initial_After)
        (auto simp add: initials_Renaming non_BOT image_iff ev_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
  next
    assume assm : \<open>\<exists>a. ev a \<in> P\<^sup>0 \<and> f a = b\<close>
    hence initial: \<open>ev b \<in> (Renaming P f g)\<^sup>0\<close>
      by (auto simp add: initials_Renaming image_iff ev_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
    show \<open>?lhs = ?rhs\<close>
    proof (subst Process_eq_spec_optimized, safe)
      fix s
      assume \<open>s \<in> \<D> ?lhs\<close>
      hence * : \<open>ev b # s \<in> \<D> (Renaming P f g)\<close>
        by (auto simp add: initial After\<^sub>\<beta>.D_After split: if_split_asm)
      from "*" obtain t1 t2
        where ** : \<open>tF t1\<close> \<open>ftF t2\<close>
          \<open>ev b # s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1 @ t2\<close> \<open>t1 \<in> \<D> P\<close>
        by (simp add: D_Renaming) blast
      from "**"(1, 3, 4) non_BOT obtain a t1'
        where *** : \<open>t1 = ev a # t1'\<close> \<open>f a = b\<close>
        by (cases t1) (auto simp add: BOT_iff_Nil_D ev_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
      have \<open>ev a \<in> P\<^sup>0\<close>
        using "**"(4) "***"(1) initials_memI D_T by blast
      also have \<open>s \<in> \<D> (Renaming (P after\<^sub>\<alpha> a) f g)\<close>
        using "**" "***"(1) by (simp add: D_Renaming After\<^sub>\<alpha>.D_After calculation) blast
      ultimately show \<open>s \<in> \<D> ?rhs\<close>
        using "***"(2) by (simp add: D_GlobalNdet) blast
    next
      fix s
      assume \<open>s \<in> \<D> ?rhs\<close>
      then obtain a where * : \<open>ev a \<in> P\<^sup>0\<close> \<open>f a = b\<close>
        \<open>s \<in> \<D> (Renaming (P after\<^sub>\<alpha> a) f g)\<close>
        by (simp add: D_GlobalNdet split: if_split_asm) blast
      from "*"(3) obtain s1 s2 
        where ** : \<open>tF s1\<close> \<open>ftF s2\<close>
          \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2\<close> \<open>ev a # s1 \<in> \<D> P\<close>
        by (simp add: D_Renaming After\<^sub>\<alpha>.D_After "*"(1)) blast
      have *** : \<open>tF (ev a # s1) \<and> ev b # s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (ev a # s1) @ s2\<close>
        by (simp add: "**"(1, 3) "*"(2))
      from "**"(2, 4)  show \<open>s \<in> \<D> ?lhs\<close>
        by (simp add: After\<^sub>\<beta>.D_After initial D_Renaming) (use "***" in blast)
    next
      fix s X
      assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
      assume \<open>(s, X) \<in> \<F> ?lhs\<close>
      then consider \<open>ev b \<notin> (Renaming P f g)\<^sup>0\<close> \<open>s = []\<close>
        | \<open>ev b \<in> (Renaming P f g)\<^sup>0\<close> \<open>(ev b # s, X) \<in> \<F> (Renaming P f g)\<close>
        by (simp add: initial After\<^sub>\<beta>.F_After split: if_split_asm) 
      thus \<open>(s, X) \<in> \<F> ?rhs\<close>
      proof cases
        from initial show \<open>ev b \<notin> (Renaming P f g)\<^sup>0 \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by simp
      next
        assume assms : \<open>ev b \<in> (Renaming P f g)\<^sup>0\<close>
          \<open>(ev b # s, X) \<in> \<F> (Renaming P f g)\<close>
        from assms(2) consider \<open>ev b # s \<in> \<D> (Renaming P f g)\<close>
          | s1 where \<open>(s1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> P\<close> \<open>ev b # s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close>
          by (simp add: F_Renaming D_Renaming) meson
        thus \<open>(s, X) \<in> \<F> ?rhs\<close>
        proof cases
          assume \<open>ev b # s \<in> \<D> (Renaming P f g)\<close>
          hence \<open>s \<in> \<D> ?lhs\<close> by (force simp add: After\<^sub>\<beta>.D_After assms(1))
          with D_F same_div show \<open>(s, X) \<in> \<F> ?rhs\<close> by blast
        next
          fix s1 assume * : \<open>(s1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> P\<close>
            \<open>ev b # s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close>
          from "*"(2) obtain a s1'
            where ** : \<open>s1 = ev a # s1'\<close> \<open>f a = b\<close>
            by (cases s1; simp) (metis map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_ev_iff)
          have \<open>ev a \<in> P\<^sup>0\<close>
            using "*"(1) "**"(1) initials_memI F_T by blast
          also have \<open>(s, X) \<in> \<F> (Renaming (P after\<^sub>\<alpha> a) f g)\<close>
            using "*"(1, 2) "**"(1) by (simp add: F_Renaming After\<^sub>\<alpha>.F_After calculation) blast
          ultimately show \<open>(s, X) \<in> \<F> ?rhs\<close>
            using "**"(2) by (simp add: F_GlobalNdet) blast
        qed
      qed
    next
      fix s X
      assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
      assume \<open>(s, X) \<in> \<F> ?rhs\<close>
      then consider \<open>\<forall>a. ev a \<in> P\<^sup>0 \<longrightarrow> f a \<noteq> b\<close> \<open>s = []\<close>
        | a where \<open>f a = b\<close> \<open>ev a \<in> P\<^sup>0\<close> \<open>(s, X) \<in> \<F> (Renaming (P after\<^sub>\<alpha> a) f g)\<close>
        by (auto simp add: F_GlobalNdet split: if_split_asm)
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof cases
        from assm show \<open>\<forall>a. ev a \<in> P\<^sup>0 \<longrightarrow> f a \<noteq> b \<Longrightarrow> s = [] \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          by (auto simp add: After\<^sub>\<beta>.F_After F_Renaming initials_Renaming non_BOT)
      next
        fix a assume * : \<open>f a = b\<close> \<open>ev a \<in> P\<^sup>0\<close> \<open>(s, X) \<in> \<F> (Renaming (P after\<^sub>\<alpha> a) f g)\<close>
        from "*"(3) consider \<open>s \<in> \<D> (Renaming (P after\<^sub>\<alpha> a) f g)\<close>
          | s1 where \<open>(s1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P after\<^sub>\<alpha> a)\<close> \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close>
          by (simp add: F_Renaming D_Renaming) blast
        thus \<open>(s, X) \<in> \<F> ?lhs\<close>
        proof cases
          assume \<open>s \<in> \<D> (Renaming (P after\<^sub>\<alpha> a) f g)\<close>
          with "*"(1, 2) have \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_GlobalNdet) blast
          with D_F same_div show \<open>(s, X) \<in> \<F> ?lhs\<close> by blast
        next
          fix s1 assume ** : \<open>(s1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P after\<^sub>\<alpha> a)\<close>
            \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close>
          from initial "*"(1, 2) "**"
          have \<open>(ev a # s1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> P \<and> ev b # s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (ev a # s1)\<close>
            by (simp add: After\<^sub>\<alpha>.F_After "*"(2))
          hence \<open>(ev b # s, X) \<in> \<F> (Renaming P f g)\<close>
            by (auto simp add: F_Renaming)
          thus \<open>(s, X) \<in> \<F> ?lhs\<close>
            by (simp add: After\<^sub>\<beta>.F_After initial)
        qed
      qed
    qed
  qed
qed

no_notation After\<^sub>\<alpha>.After (infixl \<open>after\<^sub>\<alpha>\<close> 86)
no_notation After\<^sub>\<beta>.After (infixl \<open>after\<^sub>\<beta>\<close> 86)

end


text \<open>Now we can get back to \<^locale>\<open>After\<close>.\<close>

context After
begin

section \<open>Behaviour of @{const [source] After} with Operators of \<^session>\<open>HOL-CSPM\<close>\<close>

lemma After_GlobalDet_is_After_GlobalNdet: 
  \<open>ev a \<in> (\<Union>a \<in> A. (P a)\<^sup>0) \<Longrightarrow> (\<box> a \<in> A. P a) after a = (\<sqinter> a \<in> A. P a) after a\<close>
  by (simp add: Process_eq_spec After_projs initials_GlobalDet
      initials_GlobalNdet GlobalNdet_projs GlobalDet_projs)


lemma After_GlobalNdet:
  \<open>(\<sqinter> a \<in> A. P a) after a =  (  if ev a \<in> (\<Union>a \<in> A. (P a)\<^sup>0)
                              then \<sqinter> x \<in> {x \<in> A. ev a \<in> (P x)\<^sup>0}. P x after a
                              else \<Psi> (\<sqinter> a \<in> A. P a) a)\<close>
  (is \<open>?lhs = (if ?prem then ?rhs else _)\<close>)
proof (split if_split, intro conjI impI)
  show \<open>\<not> ?prem \<Longrightarrow> ?lhs = \<Psi> (\<sqinter> a \<in> A. P a) a\<close>
    by (simp add: not_initial_After initials_GlobalNdet)
next
  assume ?prem
  then obtain x where \<open>x \<in> A\<close> \<open>ev a \<in> (P x)\<^sup>0\<close> by blast
  show \<open>?lhs = ?rhs\<close>
  proof (subst Process_eq_spec, safe)
    from \<open>x \<in> A\<close> \<open>ev a \<in> (P x)\<^sup>0\<close> show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
      by (auto simp add: D_After initials_GlobalNdet D_GlobalNdet
          split: if_split_asm intro: D_T initials_memI)
  next
    show \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
      by (auto simp add: D_GlobalNdet D_After initials_GlobalNdet)
  next
    from \<open>x \<in> A\<close> \<open>ev a \<in> (P x)\<^sup>0\<close> show \<open>(t, X) \<in> \<F> ?lhs \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for t X
      by (auto simp add: F_After initials_GlobalNdet F_GlobalNdet
          split: if_split_asm intro: F_T initials_memI)
  next
    from \<open>x \<in> A\<close> \<open>ev a \<in> (P x)\<^sup>0\<close> show \<open>(t, X) \<in> \<F> ?rhs \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for t X
      by (auto simp add: F_GlobalNdet F_After initials_GlobalNdet split: if_split_asm)
  qed
qed


lemma After_GlobalDet:
  \<open>(\<box> a \<in> A. P a) after a =  (  if ev a \<in> (\<Union>a \<in> A. (P a)\<^sup>0)
                              then \<sqinter> x \<in> {x \<in> A. ev a \<in> (P x)\<^sup>0}. P x after a
                              else \<Psi> (\<box> a \<in> A. P a) a)\<close>
  by (simp add: After_GlobalDet_is_After_GlobalNdet After_GlobalNdet
      initials_GlobalDet not_initial_After)


(* TODO: formulate and prove for MultiSync and MultiSeq *)



subsection \<open>@{const [source] After} Throwing\<close>

lemma After_Throw: 
  \<open>(P \<Theta> a \<in> A. Q a) after a = 
   (  if P = \<bottom> then \<bottom>
    else   if ev a \<in> P\<^sup>0 then   if a \<in> A then Q a
                                 else P after a \<Theta> a \<in> A. Q a
         else \<Psi> (P \<Theta> a \<in> A. Q a) a)\<close>
  (is \<open>?lhs = ?rhs\<close>)
proof -
  have \<open>?lhs = Q a\<close> if \<open>P \<noteq> \<bottom>\<close> and \<open>ev a \<in> P\<^sup>0\<close> and \<open>a \<in> A\<close>
  proof (rule Process_eq_optimizedI)
    fix t
    assume \<open>t \<in> \<D> ?lhs\<close>
    with \<open>ev a \<in> P\<^sup>0\<close> have \<open>ev a # t \<in> \<D> (P \<Theta> a \<in> A. Q a)\<close>
      by (simp add: D_After initials_Throw)
    with \<open>P \<noteq> \<bottom>\<close> show \<open>t \<in> \<D> (Q a)\<close>
      apply (simp add: D_Throw disjoint_iff BOT_iff_Nil_D, elim disjE)
      by (metis hd_append2 hd_in_set image_eqI list.sel(1) \<open>a \<in> A\<close>)
        (metis append_self_conv2 event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(1) hd_append2
          hd_in_set image_eqI list.sel(1, 3) \<open>a \<in> A\<close>)
  next
    have \<open>[ev a] \<in> \<T> P \<and> a \<in> A\<close> using initials_def \<open>ev a \<in> P\<^sup>0\<close> \<open>a \<in> A\<close> by blast
    thus \<open>t \<in> \<D> (Q a) \<Longrightarrow> t \<in> \<D> ((P \<Theta> a \<in> A. Q a) after a)\<close> for t
      by (simp add: D_After initials_Throw \<open>ev a \<in> P\<^sup>0\<close> D_Throw)
        (metis append_Nil empty_set inf_bot_left)
  next
    fix t X
    assume \<open>(t, X) \<in> \<F> ?lhs\<close>
    with \<open>ev a \<in> P\<^sup>0\<close> have \<open>(ev a # t, X) \<in> \<F> (P \<Theta> a \<in> A. Q a)\<close>
      by (simp add: F_After initials_Throw)
    with \<open>P \<noteq> \<bottom>\<close> \<open>a \<in> A\<close> show \<open>(t, X) \<in> \<F> (Q a)\<close>
      apply (simp add: F_Throw image_iff BOT_iff_Nil_D, elim disjE)
      by (metis disjoint_iff hd_append2 hd_in_set image_eqI list.sel(1))
        (metis append_Nil event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(1) hd_append2 imageI insert_disjoint(2) 
          list.exhaust_sel list.sel(1, 3) list.simps(15))
  next
    have \<open>[ev a] \<in> \<T> P \<and> a \<in> A\<close> using initials_def \<open>ev a \<in> P\<^sup>0\<close> \<open>a \<in> A\<close> by blast
    thus \<open>(t, X) \<in> \<F> (Q a) \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for t X
      by (simp add: F_After initials_Throw \<open>ev a \<in> P\<^sup>0\<close> F_Throw)
        (metis append_Nil empty_set inf_bot_left)
  qed

  also have \<open>?lhs = (P after a) \<Theta> a \<in> A. Q a\<close>
    if \<open>P \<noteq> \<bottom>\<close> and \<open>ev a \<in> P\<^sup>0\<close> and \<open>a \<notin> A\<close>
  proof (rule Process_eq_optimizedI)
    fix t
    assume \<open>t \<in> \<D> ?lhs\<close>
    with \<open>ev a \<in> P\<^sup>0\<close> have \<open>ev a # t \<in> \<D> (P \<Theta> a \<in> A. Q a)\<close>
      by (simp add: D_After initials_Throw)
    then consider (divL) t1 t2 where \<open>ev a # t = t1 @ t2\<close> \<open>t1 \<in> \<D> P\<close> \<open>tF t1\<close>
      \<open>set t1 \<inter> ev ` A = {}\<close> \<open>ftF t2\<close>
    | (divR) t1 t2 a' where \<open>ev a # t = t1 @ ev a' # t2\<close> \<open>t1 @ [ev a'] \<in> \<T> P\<close>
      \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a' \<in> A\<close> \<open>t2 \<in> \<D> (Q a')\<close>
      by (simp add: D_Throw) blast
    thus \<open>t \<in> \<D> ((P after a) \<Theta> a \<in> A. Q a)\<close>
    proof cases
      case divL
      from \<open>P \<noteq> \<bottom>\<close> divL(1, 2) BOT_iff_Nil_D obtain t1'
        where \<open>t1 = ev a # t1'\<close> by (cases t1) auto
      with divL(1-4) have \<open>t = t1' @ t2 \<and> t1' \<in> \<D> (P after a) \<and>
                           tF t1' \<and> set t1' \<inter> ev ` A = {}\<close>
        by (simp add: D_After \<open>ev a \<in> P\<^sup>0\<close>)
      with divL(5) show \<open>t \<in> \<D> ((P after a) \<Theta> a \<in> A. Q a)\<close>
        by (auto simp add: D_Throw) 
    next
      case divR
      have \<open>a \<noteq> a'\<close> using divR(4) \<open>a \<notin> A\<close> by blast
      with divR(1) obtain t1' where ** : \<open>t1 = ev a # t1'\<close> by (cases t1) auto
      with divR(2) \<open>ev a \<in> P\<^sup>0\<close> have \<open>t1' @ [ev a'] \<in> \<T> (P after a)\<close>
        by (simp add: T_After)
      with divR(1, 3-5) "**" show \<open>t \<in> \<D> ((P after a) \<Theta> a \<in> A. Q a)\<close>
        by (simp add: D_Throw) blast
    qed
  next
    fix t
    assume \<open>t \<in> \<D> ((P after a) \<Theta> a \<in> A. Q a)\<close>
    then consider (divL) t1 t2 where \<open>t = t1 @ t2\<close> \<open>t1 \<in> \<D> (P after a)\<close>
      \<open>tF t1\<close> \<open>set t1 \<inter> ev ` A = {}\<close> \<open>ftF t2\<close>
    | (divR) t1 a' t2 where \<open>t = t1 @ ev a' # t2\<close> \<open>t1 @ [ev a'] \<in> \<T> (P after a)\<close>
      \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a' \<in> A\<close> \<open>t2 \<in> \<D> (Q a')\<close>
      unfolding D_Throw by blast
    thus \<open>t \<in> \<D> ?lhs\<close>
    proof cases
      case divL
      from divL(2) \<open>ev a \<in> P\<^sup>0\<close> have ** : \<open>ev a # t1 \<in> \<D> P\<close> by (simp add: D_After)
      have *** : \<open>tF (ev a # t1) \<and> set (ev a # t1) \<inter> ev ` A = {}\<close>
        by (simp add: image_iff divL(3, 4) \<open>a \<notin> A\<close>)
      show \<open>t \<in> \<D> ?lhs\<close>
        by (simp add: D_After D_Throw initials_Throw \<open>ev a \<in> P\<^sup>0\<close>)
          (metis divL(1, 5) "**" "***" Cons_eq_appendI)
    next
      case divR
      from divR(2) \<open>ev a \<in> P\<^sup>0\<close> have ** : \<open>ev a # t1 @ [ev a'] \<in> \<T> P\<close>
        by (simp add: T_After)
      have *** : \<open>set (ev a # t1) \<inter> ev ` A = {}\<close>
        by (simp add: image_iff divR(3) \<open>a \<notin> A\<close>)
      show \<open>t \<in> \<D> ?lhs\<close>
        by (simp add: D_After D_Throw initials_Throw \<open>ev a \<in> P\<^sup>0\<close>) 
          (metis divR(1, 4, 5) "**" "***" Cons_eq_appendI)
    qed
  next
    fix t X assume \<open>t \<notin> \<D> ?lhs\<close>
    assume \<open>(t, X) \<in> \<F> ?lhs\<close>
    with \<open>ev a \<in> P\<^sup>0\<close> have \<open>(ev a # t, X) \<in> \<F> (P \<Theta> a \<in> A. Q a)\<close>
      by (simp add: F_After initials_Throw)
    with \<open>t \<notin> \<D> ?lhs\<close> \<open>(t, X) \<in> \<F> ?lhs\<close> consider \<open>(ev a # t, X) \<in> \<F> P\<close> \<open>set t \<inter> ev ` A = {}\<close>
      | (failR) t1 a' t2 where \<open>ev a # t = t1 @ ev a' # t2\<close> \<open>t1 @ [ev a'] \<in> \<T> P\<close>
        \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a' \<in> A\<close> \<open>(t2, X) \<in> \<F> (Q a')\<close>
      by (auto simp add: D_After Throw_projs initials_Throw split: if_split_asm)
        (metis D_T initials_memI is_processT7)
    thus \<open>(t, X) \<in> \<F> (P after a \<Theta> a\<in>A. Q a)\<close>
    proof cases
      show \<open>(ev a # t, X) \<in> \<F> P \<Longrightarrow> set t \<inter> ev ` A = {} \<Longrightarrow>
            (t, X) \<in> \<F> (P after a \<Theta> a\<in>A. Q a)\<close>
        by (simp add: F_Throw F_After \<open>ev a \<in> P\<^sup>0\<close>)
    next
      case failR
      have \<open>a \<noteq> a'\<close> using failR(4) \<open>a \<notin> A\<close> by blast
      with failR(1) obtain t1' where \<open>t1 = ev a # t1'\<close> by (cases t1) auto
      also have \<open>t1' @ [ev a'] \<in> \<T> (P after a) \<and> set t1' \<inter> ev ` A = {}\<close>
        using failR(2, 3) by (simp add: image_iff T_After \<open>ev a \<in> P\<^sup>0\<close> calculation)
      ultimately show \<open>(t, X) \<in> \<F> (P after a \<Theta> a \<in> A. Q a)\<close>
        using failR(1, 4, 5) by (simp add: F_Throw) blast
    qed
  next
    fix t X
    assume \<open>t \<notin> \<D> (P after a \<Theta> a\<in>A. Q a)\<close> and \<open>(t, X) \<in> \<F> (P after a \<Theta> a\<in>A. Q a)\<close>
    then consider (failL) \<open>(t, X) \<in> \<F> (P after a)\<close> \<open>set t \<inter> ev ` A = {}\<close>
      | (failR) t1 a' t2 where \<open>t = t1 @ ev a' # t2\<close> \<open>t1 @ [ev a'] \<in> \<T> (P after a)\<close>
        \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a' \<in> A\<close> \<open>(t2, X) \<in> \<F> (Q a')\<close>
      by (auto simp add: Throw_projs D_After \<open>ev a \<in> P\<^sup>0\<close>) 
    thus \<open>(t, X) \<in> \<F> ?lhs\<close>
    proof cases
      case failL
      from failL(2) have * : \<open>set (ev a # t) \<inter> ev ` A = {}\<close>
        by (simp add: image_iff \<open>a \<notin> A\<close> failL(2))
      from failL(1) have \<open>(ev a # t, X) \<in> \<F> P\<close>
        by (simp add: F_After \<open>ev a \<in> P\<^sup>0\<close>)
      with "*" show  \<open>(t, X) \<in> \<F> ?lhs\<close>
        by (simp add: F_After F_Throw initials_Throw \<open>ev a \<in> P\<^sup>0\<close>)
    next
      case failR
      from failR(2) \<open>ev a \<in> P\<^sup>0\<close> have ** : \<open>ev a # t1 @ [ev a'] \<in> \<T> P\<close>
        by (simp add: T_After)
      have *** : \<open>set (ev a # t1) \<inter> ev ` A = {}\<close>
        by (simp add: image_iff failR(3) \<open>a \<notin> A\<close>)
      from failR(1, 4, 5) show \<open>(t, X) \<in> \<F> ?lhs\<close>
        by (simp add: F_After F_Throw initials_Throw \<open>ev a \<in> P\<^sup>0\<close>) 
          (metis  "**" "***" append_Cons)
    qed
  qed

  ultimately show \<open>?lhs = ?rhs\<close>
    by (simp add: After_BOT not_initial_After initials_Throw)
qed



subsection \<open>@{const [source] After} Interrupting\<close>

theorem After_Interrupt: 
  \<open>(P \<triangle> Q) after a =
   (   if ev a \<in> P\<^sup>0 \<inter> Q\<^sup>0 
     then Q after a \<sqinter> (P after a \<triangle> Q)
     else    if ev a \<in> P\<^sup>0 \<and> ev a \<notin> Q\<^sup>0
           then P after a \<triangle> Q 
           else   if ev a \<notin> P\<^sup>0 \<and> ev a \<in> Q\<^sup>0
                then Q after a
                else \<Psi> (P \<triangle> Q) a)\<close>
proof -
  have \<open>(P \<triangle> Q) after a \<sqsubseteq>\<^sub>F\<^sub>D Q after a\<close> if initial: \<open>ev a \<in> Q\<^sup>0\<close>
  proof (unfold failure_divergence_refine_def failure_refine_def divergence_refine_def, safe)
    fix t
    assume \<open>t \<in> \<D> (Q after a)\<close>
    hence \<open>ev a # t \<in> \<D> Q\<close>
      by (simp add: D_After initial)
    thus \<open>t \<in> \<D> ((P \<triangle> Q) after a)\<close>
      by (simp add: D_After initial initials_Interrupt D_Interrupt)
        (metis Nil_elem_T append_Nil tickFree_Nil)
  next
    show \<open>(t, X) \<in> \<F> (Q after a) \<Longrightarrow> (t, X) \<in> \<F> ((P \<triangle> Q) after a)\<close> for t X
      by (simp add: F_After initials_Interrupt F_Interrupt initial)
        (metis Nil_elem_T append_Nil list.distinct(1) tickFree_Nil)
  qed

  moreover have \<open>(P \<triangle> Q) after a \<sqsubseteq>\<^sub>F\<^sub>D P after a \<triangle> Q\<close> if initial: \<open>ev a \<in> P\<^sup>0\<close>
  proof (unfold failure_divergence_refine_def failure_refine_def divergence_refine_def, safe)
    show \<open>t \<in> \<D> (P after a \<triangle> Q) \<Longrightarrow> t \<in> \<D> ((P \<triangle> Q) after a)\<close> for t
      by (simp add: D_Interrupt D_After initial T_After initials_Interrupt)
        (metis append_Cons event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) tickFree_Cons_iff)
  next
    show \<open>(t, X) \<in> \<F> (P after a \<triangle> Q) \<Longrightarrow> (t, X) \<in> \<F> ((P \<triangle> Q) after a)\<close> for t X
      by (simp add: F_Interrupt F_After initial initials_Interrupt T_After D_After, elim disjE)
        (metis [[metis_verbose = false]] Cons_eq_appendI event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) tickFree_Cons_iff)+ 
  qed

  moreover have \<open>Q after a \<sqsubseteq>\<^sub>F\<^sub>D (P \<triangle> Q) after a\<close>
    if initial_hyps: \<open>ev a \<notin> P\<^sup>0\<close> \<open>ev a \<in> Q\<^sup>0\<close>
  proof (unfold failure_divergence_refine_def failure_refine_def divergence_refine_def, safe)
    show \<open>t \<in> \<D> ((P \<triangle> Q) after a) \<Longrightarrow> t \<in> \<D> (Q after a)\<close> for t
      by (simp add: D_After initials_Interrupt D_Interrupt initial_hyps)
        (metis initials_memI D_T append_Nil hd_append
          list.exhaust_sel list.sel(1) initial_hyps(1))
  next
    from initials_memI[of \<open>ev a\<close> _ P, simplified initial_hyps(1)]
    show \<open>(t, X) \<in> \<F> ((P \<triangle> Q) after a) \<Longrightarrow> (t, X) \<in> \<F> (Q after a)\<close> for t X
      by (auto simp add: F_After initials_Interrupt F_Interrupt initial_hyps intro: F_T D_T)
        (metis, metis append_eq_Cons_conv, metis append_eq_Cons_conv is_processT8)
  qed

  moreover have \<open>P after a \<triangle> Q \<sqsubseteq>\<^sub>F\<^sub>D (P \<triangle> Q) after a\<close>
    if initial_hyps: \<open>ev a \<in> P\<^sup>0\<close> \<open>ev a \<notin> Q\<^sup>0\<close>
  proof (unfold failure_divergence_refine_def failure_refine_def divergence_refine_def, safe)
    from initials_memI[of \<open>ev a\<close> _ Q, simplified initial_hyps(2)]
    show \<open>t \<in> \<D> ((P \<triangle> Q) after a) \<Longrightarrow> t \<in> \<D> (P after a \<triangle> Q)\<close> for t
      by (simp add: After_projs initials_Interrupt initial_hyps D_Interrupt)
        (metis append_Nil hd_append2 list.exhaust_sel D_T
          list.sel(1, 3) tickFree_Cons_iff tl_append2)
  next
    fix t X
    assume \<open>(t, X) \<in> \<F> ((P \<triangle> Q) after a)\<close>
    with initial_hyps(1) have \<open>(ev a # t, X) \<in> \<F> (P \<triangle> Q)\<close>
      by (simp add: F_After initials_Interrupt)
    with initials_memI[of \<open>ev a\<close> _ Q, simplified initial_hyps(2)]
    show \<open>(t, X) \<in> \<F> (P after a \<triangle> Q)\<close>
      by (simp add: F_Interrupt After_projs initial_hyps(1), elim disjE)
        (metis (no_types, opaque_lifting) [[metis_verbose = false]]
          append_self_conv2 event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(3) tl_append2 F_T list.exhaust_sel
          list.sel(1, 3) tickFree_Cons_iff D_T hd_append2)+
  qed

  moreover have \<open>(Q after a) \<sqinter> (P after a \<triangle> Q) \<sqsubseteq>\<^sub>F\<^sub>D (P \<triangle> Q) after a\<close>
    if both_initial: \<open>ev a \<in> P\<^sup>0\<close> \<open>ev a \<in> Q\<^sup>0\<close>
  proof (unfold failure_divergence_refine_def failure_refine_def divergence_refine_def, safe)
    fix t assume \<open>t \<in> \<D> ((P \<triangle> Q) after a)\<close>
    with both_initial(1) have \<open>ev a # t \<in> \<D> (P \<triangle> Q)\<close>
      by (simp add: D_After initials_Interrupt)
    thus \<open>t \<in> \<D> ((Q after a) \<sqinter> (P after a \<triangle> Q))\<close>
      by (simp add: D_Interrupt After_projs D_Ndet both_initial)
        (metis tickFree_tl append_Cons append_Nil list.exhaust_sel list.sel(1, 3))
  next
    fix t X assume \<open>(t, X) \<in> \<F> ((P \<triangle> Q) after a)\<close>
    with both_initial(1) have \<open>(ev a # t, X) \<in> \<F> (P \<triangle> Q)\<close>
      by (simp add: F_After initials_Interrupt)
    thus \<open>(t, X) \<in> \<F> ((Q after a) \<sqinter> (P after a \<triangle> Q))\<close>
      by (simp add: F_Interrupt F_Ndet After_projs both_initial, elim disjE)
        (metis (no_types, opaque_lifting) [[metis_verbose = false]] 
          event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct(1) list.sel(1, 3) append_Nil hd_append2
          list.exhaust_sel process_charn tickFree_Cons_iff tl_append2)+
  qed

  ultimately show ?thesis
    by (auto simp add: not_initial_After initials_Interrupt
        intro: FD_antisym)
      (metis mono_Ndet_FD FD_antisym Ndet_id)
qed



section \<open>Behaviour of @{const [source] After} with Reference Processes\<close>

lemma After_DF:
  \<open>DF A after a = (if a \<in> A then DF A else \<Psi> (DF A) a)\<close>
  by (simp add: not_initial_After initials_DF image_iff)
    (subst DF_unfold, simp add: After_Mndetprefix)

lemma After_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S:
  \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R after a = (if a \<in> A then DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R else \<Psi> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) a)\<close>
  by (simp add: not_initial_After initials_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S image_iff)
    (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold,
      simp add: After_Ndet After_Mndetprefix initials_Mndetprefix image_iff)

lemma After_RUN:
  \<open>RUN A after a = (if a \<in> A then RUN A else \<Psi> (RUN A) a)\<close>
  by (simp add: not_initial_After initials_RUN image_iff)
    (subst RUN_unfold, subst After_Mprefix, simp)

lemma After_CHAOS:
  \<open>CHAOS A after a = (if a \<in> A then CHAOS A else \<Psi> (CHAOS A) a)\<close>
  by (simp add: not_initial_After initials_CHAOS image_iff)
    (subst CHAOS_unfold,
      simp add: After_Ndet initials_Mprefix After_Mprefix)

lemma After_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S: 
  \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R after a = (if a \<in> A then CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R else \<Psi> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) a)\<close>
  by (simp add: not_initial_After initials_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S image_iff)
    (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold,
      simp add: initials_Ndet initials_Mprefix After_Ndet After_Mprefix image_iff)



lemma DF_FD_After: \<open>DF A \<sqsubseteq>\<^sub>F\<^sub>D P after a\<close> if \<open>ev a \<in> P\<^sup>0\<close> and \<open>DF A \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
proof -
  have \<open>DF A after a \<sqsubseteq>\<^sub>F\<^sub>D P after a\<close> by (rule mono_After_FD[OF that]) 
  also have \<open>a \<in> A\<close>
    using anti_mono_initials_FD[OF that(2), THEN set_mp, OF that(1)]
    by (simp add: initials_DF image_iff)
  ultimately show \<open>DF A \<sqsubseteq>\<^sub>F\<^sub>D P after a\<close> by (subst (asm) After_DF, simp split: if_split_asm)
qed


lemma DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_After: \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R \<sqsubseteq>\<^sub>F\<^sub>D P after a\<close> if \<open>ev a \<in> P\<^sup>0\<close> and \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
proof -
  have \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R after a \<sqsubseteq>\<^sub>F\<^sub>D P after a\<close> by (rule mono_After_FD[OF that]) 
  also have \<open>a \<in> A\<close>
    using anti_mono_initials_FD[OF that(2), THEN set_mp, OF that(1)]
    by (simp add: initials_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S image_iff)
  ultimately show \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R \<sqsubseteq>\<^sub>F\<^sub>D P after a\<close> by (subst (asm) After_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S, simp split: if_split_asm)
qed


text \<open>We have corollaries on \<^const>\<open>deadlock_free\<close> and \<^const>\<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<close>.\<close>

corollary deadlock_free_After:
  \<open>deadlock_free P \<Longrightarrow>
   deadlock_free (P after a) \<longleftrightarrow>
   (if ev a \<in> P\<^sup>0 then True else deadlock_free (\<Psi> P a))\<close>
  by (simp add: not_initial_After deadlock_free_def)
    (intro impI DF_FD_After)

corollary deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_After:
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<Longrightarrow> 
   deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P after a) \<longleftrightarrow>
   (if ev a \<in> P\<^sup>0 then True else deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (\<Psi> P a))\<close>
  by (simp add: not_initial_After deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD)
    (intro impI DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_After)



section \<open>Continuity\<close>

text \<open>This is a new result whose main consequence will be the admissibility of the event
      transition that is defined later (property that paves the way for point-fixed induction)\<open>\<dots>\<close>\<close>

text \<open>Of course this result will require an additional assumption of continuity
      on the placeholder \<^term>\<open>\<Psi>\<close>.\<close>

context begin

(* TODO: do we want this accessible outside ? *)
private lemma mono_\<Psi>_imp_chain_After:
  \<open>(\<And>P Q. P \<sqsubseteq> Q \<Longrightarrow> \<Psi> P a \<sqsubseteq> \<Psi> Q a) \<Longrightarrow> chain Y \<Longrightarrow> chain (\<lambda>i. Y i after a)\<close>
  by (simp add: mono_After chain_def)

private lemma cont_prem_After :
  \<open>(\<Squnion> i. Y i) after a = (\<Squnion> i. Y i after a)\<close> (is \<open>?lhs = ?rhs\<close>)
  if cont_\<Psi>: \<open>cont (\<lambda>P. \<Psi> P a)\<close> and chain_Y : \<open>chain Y\<close>
proof -
  from chain_Y cont2monofunE cont_\<Psi> mono_\<Psi>_imp_chain_After
  have chain_After : \<open>chain (\<lambda>i. Y i after a)\<close> by blast
  show \<open>?lhs = ?rhs\<close>
  proof (cases \<open>ev a \<in> (\<Squnion> i. Y i)\<^sup>0\<close>)
    assume initial : \<open>ev a \<in> (\<Squnion> i. Y i)\<^sup>0\<close>
    hence * : \<open>\<forall>i. ev a \<in> (Y i)\<^sup>0\<close> by (simp add: initials_LUB chain_Y)
    show \<open>?lhs = ?rhs\<close>
    proof (rule Process_eq_optimizedI)
      show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
        by (simp add: D_After initial)
          (simp add: D_After "*" limproc_is_thelub chain_After chain_Y D_LUB)
    next
      fix t
      define S
        where \<open>S i \<equiv> {u. t = u \<and> ev a # u \<in> \<D> (Y i)}\<close> for i
      assume \<open>t \<in> \<D> ?rhs\<close>
      hence \<open>t \<in> \<D> (Y i after a)\<close> for i
        by (simp add: limproc_is_thelub D_LUB chain_After)
      hence \<open>S i \<noteq> {}\<close> for i by (simp add: S_def D_After "*")
      moreover have \<open>finite (S 0)\<close> unfolding S_def by (prove_finite_subset_of_prefixes t)
      moreover have \<open>S (Suc i) \<subseteq> S i\<close> for i
        by (simp add: S_def subset_iff) (metis in_mono le_approx1 po_class.chainE chain_Y)
      ultimately have \<open>(\<Inter>i. S i) \<noteq> {}\<close> by (rule Inter_nonempty_finite_chained_sets)
      then obtain t1 where \<open>\<forall>i. t1 \<in> S i\<close>
        by (meson INT_iff ex_in_conv iso_tuple_UNIV_I)
      thus \<open>t \<in> \<D> ?lhs\<close> by (simp add: S_def D_After initial "*")
          (simp add: limproc_is_thelub chain_Y D_LUB)
    next
      show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
        by (simp add: F_After initial)
          (simp add: F_After "*" limproc_is_thelub chain_After chain_Y F_LUB)
    next
      fix t X assume \<open>t \<notin> \<D> ?rhs\<close> and \<open>(t, X) \<in> \<F> ?rhs\<close>
      from \<open>t \<notin> \<D> ?rhs\<close> obtain j where \<open>t \<notin> \<D> (Y j after a)\<close>
        by (auto simp add: limproc_is_thelub chain_After \<open>chain Y\<close> D_LUB)
      moreover from \<open>(t, X) \<in> \<F> ?rhs\<close> have \<open>(t, X) \<in> \<F> (Y j after a)\<close>
        by (simp add: limproc_is_thelub chain_After \<open>chain Y\<close> F_LUB)
      ultimately show \<open>(t, X) \<in> \<F> ?lhs\<close>
        using chain_Y initial is_ub_thelub mono_After proc_ord2a by blast
    qed
  next
    assume \<open>ev a \<notin> (\<Squnion>i. Y i)\<^sup>0\<close>
    then obtain k where * : \<open>ev a \<notin> (Y (i + k))\<^sup>0\<close> for i
      by (simp add: initials_LUB chain_Y)
        (metis add.commute anti_mono_initials chain_Y in_mono le_add1 po_class.chain_mono)
    hence ** : \<open>ev a \<notin> (\<Squnion>i. Y (i + k))\<^sup>0\<close> by (simp add: initials_LUB chain_Y chain_shift)
    have \<open>?lhs = (\<Squnion> i. Y (i + k)) after a\<close> by (simp add: chain_Y lub_range_shift)
    also have \<open>\<dots> = (\<Squnion> i. Y (i + k) after a)\<close>
      by (simp add: not_initial_After "*" "**")
        (fact cont2contlubE[OF cont_\<Psi> chain_shift[OF chain_Y]]) 
    also from chain_After lub_range_shift have \<open>\<dots> = ?rhs\<close> by blast
    finally show \<open>?lhs = ?rhs\<close> .
  qed
qed


lemma After_cont [simp] : 
  \<open>cont (\<lambda>x. f x after a)\<close> if cont_\<Psi> : \<open>cont (\<lambda>P. \<Psi> P a)\<close> and cont_f : \<open>cont f\<close>
proof (rule contI2)
  show \<open>monofun (\<lambda>x. f x after a)\<close>
    by (rule monofunI) (metis cont2monofunE cont_\<Psi> cont_f mono_After)
next
  show \<open>chain Y \<Longrightarrow> f (\<Squnion>i. Y i) after a \<sqsubseteq> (\<Squnion>i. f (Y i) after a)\<close> for Y
    by (simp add: ch2ch_cont cont2contlubE cont_\<Psi> cont_f cont_prem_After)
qed

end

end

(*<*)
end
  (*>*)