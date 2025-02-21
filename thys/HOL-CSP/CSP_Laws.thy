(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : Algebraic laws
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


section \<open> Powerful Laws of CSP \<close>

(*<*)
theory CSP_Laws                                               
  imports Basic_CSP_Laws Step_CSP_Laws_Extended
begin
  (*>*)

subsection\<open> Laws for Mndetprefix and Sync\<close>

lemma Mndetprefix_Sync_Det_distr_FD :
  \<open>(\<sqinter> a \<in> A \<rightarrow> (P a \<lbrakk> C \<rbrakk> (\<sqinter> b \<in> B \<rightarrow> Q b))) \<box>
   (\<sqinter> b \<in> B \<rightarrow> ((\<sqinter> a \<in> A \<rightarrow> P a) \<lbrakk> C \<rbrakk> Q b))
   \<sqsubseteq>\<^sub>F\<^sub>D (\<sqinter> a \<in> A \<rightarrow> P a) \<lbrakk> C \<rbrakk> (\<sqinter> b \<in> B \<rightarrow> Q b)\<close>
  (is \<open>?lhs1 \<box> ?lhs2 \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>)
  if \<open>A \<noteq> {}\<close> \<open>B \<noteq> {}\<close> \<open>A \<inter> C = {}\<close> \<open>B \<inter> C = {}\<close>
proof -
  have \<open>?lhs1 = \<sqinter> b\<in>B. \<sqinter> a\<in>A. (a \<rightarrow> (P a \<lbrakk>C\<rbrakk> (b \<rightarrow> Q b)))\<close> (is \<open>_ = ?lhs1'\<close>)
    by (simp add: \<open>A \<noteq> {}\<close> \<open>B \<noteq> {}\<close> Mndetprefix_GlobalNdet
        Sync_distrib_GlobalNdet_left Sync_distrib_GlobalNdet_right
        write0_def GlobalNdet_Mprefix_distr[OF \<open>B \<noteq> {}\<close>, symmetric])
      (subst GlobalNdet_sets_commute, simp)
  moreover have \<open>?lhs2 = \<sqinter> b\<in>B. \<sqinter> a\<in>A. (b \<rightarrow> (a \<rightarrow> P a \<lbrakk>C\<rbrakk> Q b))\<close> (is \<open>_ = ?lhs2'\<close>)
    by (simp add: \<open>A \<noteq> {}\<close> \<open>B \<noteq> {}\<close> Mndetprefix_GlobalNdet
        Sync_distrib_GlobalNdet_left Sync_distrib_GlobalNdet_right
        write0_def GlobalNdet_Mprefix_distr[OF \<open>A \<noteq> {}\<close>, symmetric])
  ultimately have \<open>?lhs1 \<box> ?lhs2 = ?lhs1' \<box> ?lhs2'\<close> by simp
  moreover have \<open>?lhs1' \<box> ?lhs2' \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter> b\<in>B. \<sqinter> a\<in>A.   (a \<rightarrow> (P a \<lbrakk>C\<rbrakk> (b \<rightarrow> Q b)))
                                                    \<box> (b \<rightarrow> ((a \<rightarrow> P a) \<lbrakk>C\<rbrakk> Q b))\<close>
    by (auto simp add: \<open>A \<noteq> {}\<close> \<open>B \<noteq> {}\<close> refine_defs GlobalNdet_projs Det_projs write0_def)
  moreover have \<open>\<dots> = \<sqinter> b\<in>B. \<sqinter> a\<in>A. ((a \<rightarrow> P a) \<lbrakk>C\<rbrakk> (b \<rightarrow> Q b))\<close>
    by (rule mono_GlobalNdet_eq, rule mono_GlobalNdet_eq,
        simp add: write0_def, subst Mprefix_Sync_Mprefix_indep)
      (use \<open>A \<inter> C = {}\<close> \<open>B \<inter> C = {}\<close> in auto)
  moreover have \<open>\<dots> = ?rhs\<close>
    by (simp add: \<open>A \<noteq> {}\<close> \<open>B \<noteq> {}\<close> Mndetprefix_GlobalNdet
        Sync_distrib_GlobalNdet_left Sync_distrib_GlobalNdet_right)
  ultimately show \<open>?lhs1 \<box> ?lhs2 \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close> by argo
qed


lemmas Mndetprefix_Sync_Det_distr_F = Mndetprefix_Sync_Det_distr_FD[THEN leFD_imp_leF]
  and Mndetprefix_Sync_Det_distr_D = Mndetprefix_Sync_Det_distr_FD[THEN leFD_imp_leD]

lemmas Mndetprefix_Sync_Det_distr_T = Mndetprefix_Sync_Det_distr_F[THEN leF_imp_leT]

lemma Mndetprefix_Sync_Det_distr_DT :
  \<open>\<lbrakk>A \<noteq> {}; B \<noteq> {}; A \<inter> C = {}; B \<inter> C = {}\<rbrakk> \<Longrightarrow>
   (\<sqinter> a \<in> A \<rightarrow> (P a \<lbrakk> C \<rbrakk> (\<sqinter> b \<in> B \<rightarrow> Q b))) \<box>
   (\<sqinter> b \<in> B \<rightarrow> ((\<sqinter> a \<in> A \<rightarrow> P a) \<lbrakk> C \<rbrakk> Q b))
   \<sqsubseteq>\<^sub>D\<^sub>T (\<sqinter> a \<in> A \<rightarrow> P a) \<lbrakk> C \<rbrakk> (\<sqinter> b \<in> B \<rightarrow> Q b)\<close>
  by (simp add: Mndetprefix_Sync_Det_distr_D Mndetprefix_Sync_Det_distr_T leD_leT_imp_leDT)


subsection \<open>Hiding Operator Laws\<close>

theorem Hiding_Hiding_less_eq_process_Hiding_Un : \<open>P \ A \ B \<sqsubseteq>\<^sub>F\<^sub>D P \ (A \<union> B)\<close>
proof (rule failure_divergence_refine_optimizedI)
  fix s assume \<open>s \<in> \<D> (P \ (A \<union> B))\<close>
  then obtain t u
    where * : \<open>ftF u\<close> \<open>tF t\<close> \<open>s = trace_hide t (ev ` (A \<union> B)) @ u\<close>
      \<open>t \<in> \<D> P \<or> (\<exists>f. isInfHiddenRun f P (A \<union> B) \<and> t \<in> range f)\<close>
    unfolding D_Hiding by blast
  have ** : \<open>trace_hide t (ev ` (A \<union> B)) = trace_hide (trace_hide t (ev ` A)) (ev ` B)\<close>
    using trace_hide_ev_union by blast
  from "*"(4) show \<open>s \<in> \<D> (P \ A \ B)\<close>
  proof (elim disjE exE)
    assume \<open>t \<in> \<D> P\<close>
    with mem_D_imp_mem_D_Hiding have \<open>trace_hide t (ev ` A) \<in> \<D> (P \ A)\<close> by blast
    thus \<open>s \<in> \<D> (P \ A \ B)\<close>
      by (subst D_Hiding) (use"*"(1, 2, 3) "**" Hiding_tickFree in blast)
  next
    fix f assume ** : \<open>isInfHiddenRun f P (A \<union> B) \<and> t \<in> range f\<close>
    hence \<open>strict_mono f\<close> by simp
    define ff where \<open>ff i \<equiv> take (i + length (f 0)) (f i)\<close> for i
    have *** : \<open>isInfHiddenRun ff P (A \<union> B) \<and> t \<in> range ff\<close>
    proof (intro conjI allI)
      show \<open>strict_mono ff\<close>
      proof (unfold strict_mono_Suc_iff, rule allI, unfold ff_def)
        fix i nat
        from length_strict_mono[of f \<open>Suc i\<close>, OF \<open>strict_mono f\<close>]
        have $ : \<open>take (i + length (f 0)) (f (Suc i)) < take ((Suc i) + length (f 0)) (f (Suc i))\<close>
          by (simp add: take_Suc_conv_app_nth)
        from \<open>strict_mono f\<close>[THEN strict_monoD, of i \<open>Suc i\<close>, simplified] 
        obtain t where \<open>f (Suc i) = f i @ t\<close> by (meson strict_prefixE')
        with length_strict_mono[of f i, OF \<open>strict_mono f\<close>]
        have \<open>take (i + length (f 0)) (f i) = take (i + length (f 0)) (f (Suc i))\<close> by simp
        with "$" show \<open>take (i + length (f 0)) (f i) < take (Suc i + length (f 0)) (f (Suc i))\<close> by simp
      qed
    next
      show \<open>ff i \<in> \<T> P\<close> for i
        by (unfold ff_def) (metis "**" prefixI append_take_drop_id is_processT3_TR)
    next
      show \<open>trace_hide (ff i) (ev ` (A \<union> B)) = trace_hide (ff 0) (ev ` (A \<union> B))\<close> for i
      proof (rule order_antisym)
        have \<open>f 0 \<le> f i\<close> by (simp add: "**" strict_mono_less_eq)
        hence \<open>f 0 \<le> take (i + length (f 0)) (f i)\<close>
          by (metis prefixE Prefix_Order.prefixI le_add2 take_all_iff take_append)
        from mono_trace_hide[OF this]
        show \<open>trace_hide (ff 0) (ev ` (A \<union> B)) \<le> trace_hide (ff i) (ev ` (A \<union> B))\<close>
          by (unfold ff_def) (metis le_add2 take_all_iff)
      next
        have \<open>take (i + length (f 0)) (f i) \<le> f i\<close>
          by (metis prefixI append_take_drop_id)
        from mono_trace_hide[OF this]
        show \<open>trace_hide (ff i) (ev ` (A \<union> B)) \<le> trace_hide (ff 0) (ev ` (A \<union> B))\<close>
          by (unfold ff_def) (metis "**" le_add2 take_all_iff)
      qed
    next
      from "**" obtain i where \<open>t = f i\<close> by blast
      moreover have \<open>f 0 \<le> f i\<close> by (simp add: "**" strict_mono_less_eq)
      ultimately have \<open>t = ff (max i (length t - length (f 0)))\<close>
        by (simp add: ff_def max_def le_length_mono)
          (metis "**" prefixE append_eq_conv_conj strict_mono_less_eq)
      thus \<open>t \<in> range ff\<close> by blast
    qed

    show \<open>s \<in> \<D> (P \ A \ B)\<close>
    proof (cases \<open>\<exists>m. \<forall>i>m. last (ff i) \<in> ev ` A\<close>)
      assume \<open>\<exists>m. \<forall>i>m. last (ff i) \<in> ev ` A\<close>
      then obtain m where $ : \<open>m < i \<Longrightarrow> last (ff i) \<in> ev ` A\<close> for i by blast
      hence \<open>tF (ff m)\<close>
        by (metis "***" strict_prefixE' append_T_imp_tickFree list.distinct(1) strict_mono_Suc_iff)
      have $$ : \<open>\<exists>t. ff (i + m) = ff m @ t \<and> set t \<subseteq> ev ` A\<close> for i
      proof (induct i)
        show \<open>\<exists>t. ff (0 + m) = ff m @ t \<and> set t \<subseteq> ev ` A\<close> by simp
      next
        fix i assume \<open>\<exists>t. ff (i + m) = ff m @ t \<and> set t \<subseteq> ev ` A\<close>
        then obtain t where \<open>ff (i + m) = ff m @ t\<close> \<open>set t \<subseteq> ev ` A\<close> by blast
        obtain r where \<open>ff (Suc i + m) = ff (i + m) @ r\<close>
          by (metis "***" strict_prefixE' add_Suc strict_mono_Suc_iff)
        moreover have \<open>length (ff (Suc i + m)) = Suc (length (ff (i + m)))\<close>
          by (simp add: ff_def) (metis "**" add_Suc length_strict_mono min_absorb2)
        ultimately have \<open>length r = 1\<close> by (metis Suc_eq_plus1 add_left_cancel length_append)
        with \<open>ff (Suc i + m) = ff (i + m) @ r\<close>
        have \<open>ff (Suc i + m) = ff (i + m) @ [last (ff (Suc i + m))]\<close> by (cases r) simp_all
        with \<open>ff (i + m) = ff m @ t\<close>
        have \<open>ff (Suc i + m) = ff m @ t @ [last (ff (Suc i + m))]\<close> by simp
        moreover have \<open>last (ff (Suc i + m)) \<in> ev ` A\<close> by (simp add: "$")
        ultimately show \<open>\<exists>t. ff (Suc i + m) = ff m @ t \<and> set t \<subseteq> ev ` A\<close>
          by (intro exI[of _ \<open>t @ [last (ff (Suc i + m))]\<close>]) (simp add: \<open>set t \<subseteq> ev ` A\<close>)
      qed
      then obtain fff where $$$$ : \<open>ff (i + m) = ff m @ fff i\<close> \<open>set (fff i) \<subseteq> ev ` A\<close> for i by metis
      show \<open>s \<in> \<D> (P \ A \ B)\<close>
        apply (simp add: D_Hiding)
        apply (rule exI[of _ \<open>trace_hide (ff m) (ev ` A)\<close>], rule exI[of _ u], intro conjI)
        subgoal by (fact \<open>ftF u\<close>)
        subgoal using Hiding_tickFree \<open>tF (ff m)\<close> by blast
        subgoal by (metis (no_types) "*"(3) "***" rangeE trace_hide_ev_union)
        apply (rule disjI1)
        apply (rule exI[of _ \<open>ff m\<close>], rule exI[of _ \<open>[]\<close>], simp add: \<open>tF (ff m)\<close>)
        apply (rule disjI2)
        apply (rule exI[of _ \<open>\<lambda>i. ff (i + m)\<close>], intro conjI)
        subgoal by (metis (mono_tags, lifting) "***" add_Suc strict_mono_Suc_iff)
        subgoal using "***" by blast
        subgoal using "$$$$" by (simp add: subset_iff)
        by (metis (mono_tags) add_0 rangeI)
    next
      assume \<open>\<nexists>m. \<forall>i>m. last (ff i) \<in> ev ` A\<close>
      { fix i :: nat assume \<open>0 < i\<close>
        from "***" obtain t where \<open>ff i = ff 0 @ t\<close> \<open>set t \<subseteq> ev ` (A \<union> B)\<close>
          unfolding isInfHiddenRun_1 by blast
        with \<open>0 < i\<close> have \<open>last (ff i) \<in> ev ` (A \<union> B)\<close>
          by (cases t) (auto simp add: "***" strict_mono_eq)
      }
      with \<open>\<nexists>m. \<forall>i>m. last (ff i) \<in> ev ` A\<close> have $ : \<open>\<forall>i. \<exists>j>i. last(ff j) \<in> ev ` B - ev ` A\<close>
        by (metis Un_Diff_cancel2 Un_iff gr0I image_Un not_less0)
      define fff where \<open>fff = rec_nat t (\<lambda>i t. ff (SOME j. t < ff j \<and> last (ff j) \<in> ev ` B - ev ` A))\<close>
      hence \<open>fff i \<in> range ff\<close> for i
        unfolding fff_def
        by (metis (mono_tags, lifting) "***" gr0_conv_Suc nat.rec(2)
            old.nat.simps(6) rangeI zero_less_iff_neq_zero)
      have $$$ : \<open>strict_mono (\<lambda>i. trace_hide (fff i) (ev ` A))\<close>
      proof (unfold strict_mono_Suc_iff, rule allI)
        fix i
        have "\<pounds>" : \<open>fff (Suc i) = ff (SOME j. fff i < ff j \<and> last (ff j) \<in> ev ` B - ev ` A)\<close>
          by (simp add: fff_def)
        from \<open>\<And>i. fff i \<in> range ff\<close> obtain j where \<open>fff i = ff j\<close> by blast
        hence \<open>\<exists>j. fff i < ff j \<and> last (ff j) \<in> ev ` B - ev ` A\<close> by (metis "$" "***" monotoneD)
        hence "\<pounds>\<pounds>" : \<open>fff i < fff (Suc i) \<and> last (fff (Suc i)) \<notin> ev ` A\<close>
          by (metis (no_types, lifting) Diff_iff "\<pounds>" someI_ex)
        then obtain r where \<open>fff (Suc i) = fff i @ r\<close> \<open>last r \<notin> ev ` A\<close>
          by (metis append_self_conv last_append less_eq_list_def prefix_def less_list_def)
        thus \<open>trace_hide (fff i) (ev ` A) < trace_hide (fff (Suc i)) (ev ` A)\<close>
          by (metis (mono_tags, lifting) prefixI "\<pounds>\<pounds>" empty_filter_conv
              filter_append last_in_set nless_le self_append_conv)
      qed
      show \<open>s \<in> \<D> (P \ A \ B)\<close>
        apply (simp add: D_Hiding)
        apply (rule exI[of _ \<open>trace_hide t (ev ` A)\<close>], rule exI[of _ u], intro conjI)
        subgoal by (fact \<open>ftF u\<close>)
        subgoal using Hiding_tickFree \<open>tF t\<close> by blast
        subgoal by (simp add: "*"(3))
        apply (rule disjI2)
        apply (rule exI[of _ \<open>\<lambda>i. trace_hide (fff i) (ev ` A)\<close>], intro conjI)
        subgoal by (fact "$$$")
        subgoal by (metis "***" \<open>\<And>i. fff i \<in> range ff\<close> mem_T_imp_mem_T_Hiding rangeE)
        subgoal by (metis (no_types) "***" \<open>\<And>i. fff i \<in> range ff\<close> rangeE trace_hide_ev_union)
        by (metis (mono_tags, lifting) fff_def old.nat.simps(6) rangeI)
    qed
  qed
next
  assume subset_div : \<open>\<D> (P \ (A \<union> B)) \<subseteq> \<D> (P \ A \ B)\<close>
  fix s X assume \<open>(s, X) \<in> \<F> (P \ (A \<union> B))\<close>
  then consider \<open>s \<in> \<D> (P \ (A \<union> B))\<close>
    | t where \<open>s = trace_hide t (ev ` (A \<union> B))\<close> \<open>(t, X \<union> ev ` (A \<union> B)) \<in> \<F> P\<close>
    unfolding F_Hiding D_Hiding by blast
  thus \<open>(s, X) \<in> \<F> (P \ A \ B)\<close>
  proof cases
    from subset_div D_F show \<open>s \<in> \<D> (P \ (A \<union> B)) \<Longrightarrow> (s, X) \<in> \<F> (P \ A \ B)\<close> by blast
  next
    fix t assume \<open>s = trace_hide t (ev ` (A \<union> B))\<close> \<open>(t, X \<union> ev ` (A \<union> B)) \<in> \<F> P\<close>
    hence * : \<open>s = trace_hide (trace_hide t (ev ` A)) (ev ` B)\<close>
      \<open>(t, X \<union> ev ` B \<union> ev ` A) \<in> \<F> P\<close>
      by (simp_all add: image_Un sup_commute sup_left_commute)
    show \<open>(s, X) \<in> \<F> (P \ A \ B)\<close>
      by (simp add: F_Hiding) (use "*" in blast)
  qed
qed


theorem Hiding_Un : \<open>P \ (A \<union> B) = P \ A \ B\<close>
  if \<open>finite A\<close> for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (rule order_antisym)
  show \<open>P \ (A \<union> B) \<le> P \ A \ B\<close>
  proof (rule failure_divergence_refine_optimizedI)
    fix s assume \<open>s \<in> \<D> (P \ A \ B)\<close>
    then obtain t u
      where * : \<open>ftF u\<close> \<open>tF t\<close> \<open>s = trace_hide t (ev ` B) @ u\<close>
        \<open>t \<in> \<D> (P \ A) \<or> (\<exists>x. isInfHidden_seqRun_strong x (P \ A) B t)\<close>
      by (elim D_Hiding_seqRunE)
    from "*"(4) show \<open>s \<in> \<D> (P \ (A \<union> B))\<close>
    proof (elim disjE exE)
      assume \<open>t \<in> \<D> (P \ A)\<close>
      then obtain t' u'
        where ** : \<open>ftF u'\<close> \<open>tF t'\<close> \<open>t = trace_hide t' (ev ` A) @ u'\<close>
          \<open>t' \<in> \<D> P \<or> (\<exists>x. isInfHidden_seqRun_strong x P A t')\<close>
        by (elim D_Hiding_seqRunE)
      from "*"(1, 2) "**"(3) have *** : \<open>ftF (trace_hide u' (ev ` B) @ u)\<close>
        using Hiding_tickFree front_tickFree_append tickFree_append_iff by blast
      show \<open>s \<in> \<D> (P \ (A \<union> B))\<close>
        apply (unfold D_Hiding_seqRun, clarify)
        apply (rule exI[of _ t'], rule exI[of _ \<open>trace_hide u' (ev ` B) @ u\<close>])
        apply (intro conjI)
        subgoal by (fact "***")
        subgoal by (fact "**"(2))
        subgoal by (simp add: "*"(3) "**"(3))
        by (metis "**"(4) Un_iff image_Un)
    next
      fix x assume ** : \<open>isInfHidden_seqRun_strong x (P \ A) B t\<close>
      have trH_x : \<open>trace_hide (seqRun t x i) (ev ` B) = trace_hide t (ev ` B)\<close> for i
        using "**" trace_hide_seqRun_eq_iff by blast
      from "**" have \<open>\<forall>i. seqRun t x i \<in> {trace_hide t (ev ` A) |t. (t, ev ` A) \<in> \<F> P}\<close>
        unfolding T_Hiding D_Hiding by blast
      with F_T have \<open>\<forall>i. \<exists>w. seqRun t x i = trace_hide w (ev ` A) \<and> w \<in> \<T> P\<close> by blast
      then obtain f where *** : \<open>seqRun t x i = trace_hide (f i) (ev ` A)\<close> \<open>f i \<in> \<T> P\<close> for i by metis
      have \<open>inj f\<close> by (rule injI) (metis "***"(1) seqRun_eq_iff)
      with finite_imageD have \<open>infinite (range f)\<close> by blast
      have $ : \<open>set (take i t') \<subseteq> set (seqRun t x i) \<union> ev ` A\<close> if \<open>t' \<in> range f\<close> for i t'
      proof -
        from \<open>t' \<in> range f\<close> obtain j where \<open>t' = f j\<close> ..
        hence "\<pounds>" : \<open>seqRun t x j = trace_hide t' (ev ` A)\<close> \<open>t' \<in> \<T> P\<close> by (simp_all add: "***")
        consider \<open>i \<le> j\<close> | \<open>j \<le> i\<close> by linarith
        thus \<open>set (take i t') \<subseteq> set (seqRun t x i) \<union> ev ` A\<close>
        proof cases
          assume \<open>j \<le> i\<close>
          hence \<open>seqRun t x j \<le> seqRun t x i\<close> by simp
          hence \<open>set (seqRun t x j) \<subseteq> set (seqRun t x i)\<close>
            by (metis prefixE Un_iff set_append subsetI)
          moreover have \<open>set (take i t') \<subseteq> set (seqRun t x j) \<union> ev ` A\<close>
            by (rule subsetI, drule in_set_takeD) (simp add: "\<pounds>"(1))
          ultimately show \<open>set (take i t') \<subseteq> set (seqRun t x i) \<union> ev ` A\<close> by blast
        next
          assume \<open>i \<le> j\<close>
          hence \<open>seqRun t x i \<le> seqRun t x j\<close> by simp
          hence \<open>take i (seqRun t x j) \<le> seqRun t x i\<close> by simp
          have \<open>seqRun t x j = trace_hide (take i t') (ev ` A) @ trace_hide (drop i t') (ev ` A)\<close>
            by (metis "\<pounds>"(1) append_take_drop_id filter_append)
          moreover have \<open>length (trace_hide (take i t') (ev ` A)) \<le> i\<close>
            by (metis length_filter_le length_take min.bounded_iff)
          ultimately have \<open>trace_hide (take i t') (ev ` A) \<le> take i (seqRun t x j)\<close> by simp
          with \<open>take i (seqRun t x j) \<le> seqRun t x i\<close> obtain t''
            where \<open>seqRun t x i = trace_hide (take i t') (ev ` A) @ t''\<close>
            by (meson prefixE dual_order.trans)
          thus \<open>set (take i t') \<subseteq> set (seqRun t x i) \<union> ev ` A\<close> by (simp add: subsetI)
        qed
      qed
      have \<open>finite {take i w |w. w \<in> range f}\<close> for i
      proof (induct i)
        show \<open>finite {take 0 w |w. w \<in> range f}\<close> by simp
      next
        fix i assume hyp : \<open>finite {take i w |w. w \<in> range f}\<close>
        show \<open>finite {take (Suc i) w |w. w \<in> range f}\<close>
        proof (rule finite_subset)
          show \<open>  {take (Suc i) w |w. w \<in> range f}
                \<subseteq>    {take i w |w. w \<in> range f}
                   \<union> (\<Union>e\<in>set (seqRun t x (Suc i)) \<union> ev ` A. {take i w @ [e] |w. w \<in> range f})\<close>
            (is \<open>?lhs \<subseteq> {take i w |w. w \<in> range f} \<union> (\<Union>e\<in>?S1. ?S2 e)\<close>)
          proof (intro subsetI)
            fix t' assume \<open>t' \<in> ?lhs\<close>
            then obtain w where "\<pounds>" : \<open>t' = take (Suc i) w\<close> \<open>w \<in> range f\<close> by blast
            show \<open>t' \<in> {take i w |w. w \<in> range f} \<union> (\<Union>e\<in>?S1. ?S2 e)\<close>
            proof (cases \<open>i < length t'\<close>)
              assume \<open>i < length t'\<close>
              with "\<pounds>"(1) take_Suc_conv_app_nth
              have \<open>take (Suc i) t' = take i w @ [t' ! i]\<close> by auto
              moreover from "\<pounds>" "$" \<open>i < length t'\<close> nth_mem have \<open>t' ! i \<in> ?S1\<close> by blast
              ultimately have \<open>t' \<in> (\<Union>e\<in>?S1. ?S2 e)\<close>
                by (intro UN_I[of \<open>t' ! i\<close>], simp_all)
                  (metis "\<pounds>" less_not_refl min.absorb2 not_le_imp_less take_take)
              thus \<open>t' \<in> {take i w |w. w \<in> range f} \<union> (\<Union>e\<in>?S1. ?S2 e)\<close> by simp
            next
              assume \<open>\<not> i < length t'\<close>
              hence \<open>take (Suc i) t' = take i t'\<close> by simp
              with "\<pounds>" show \<open>t' \<in> {take i w |w. w \<in> range f} \<union> (\<Union>e\<in>?S1. ?S2 e)\<close> by auto
            qed
          qed
        next
          show \<open>finite ({take i w |w. w \<in> range f} \<union>
                        (\<Union>e\<in>set (seqRun t x (Suc i)) \<union> ev ` A.
                             {take i w @ [e] |w. w \<in> range f}))\<close>
          proof (rule finite_UnI)
            show \<open>finite {take i w |w. w \<in> range f}\<close> by (fact hyp)
          next
            show \<open>finite (\<Union>e\<in>set (seqRun t x (Suc i)) \<union> ev ` A. {take i w @ [e] |w. w \<in> range f})\<close>
            proof (rule finite_UN_I)
              show \<open>finite (set (seqRun t x (Suc i)) \<union> ev ` A)\<close>
                by (simp add: \<open>finite A\<close>) \<comment>\<open>Here we use that \<^term>\<open>A\<close> is \<^const>\<open>finite\<close>.\<close>
            next
              fix e assume \<open>e \<in> set (seqRun t x (Suc i)) \<union> ev ` A\<close>
              have \<open>  {take i w @ [e] |w. w \<in> range f}
                   = (\<lambda>t'. t' @ [e]) ` {take i w |w. w \<in> range f}\<close> by auto
              also have \<open>finite \<dots>\<close> by (rule finite_imageI) (fact hyp)
              finally show \<open>finite {take i w @ [e] |w. w \<in> range f}\<close> .
            qed
          qed
        qed
      qed
      also have \<open>{take i w |w. w \<in> range f} = {w. \<exists>t'\<in>range f. w = take i t'}\<close> for i by auto
      finally have \<open>\<forall>i. finite {w. \<exists>t'\<in>range f. w = take i t'}\<close> ..
      from KoenigLemma[OF \<open>infinite (range f)\<close> this]
      obtain ff :: \<open>nat \<Rightarrow> ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
        where $$ : \<open>strict_mono ff\<close> \<open>range ff \<subseteq> {t. \<exists>t'\<in>range f. t \<le> t'}\<close> by blast
      from "$$"(2) have $$$ : \<open>\<exists>t'. ff (Suc j) \<le> t' \<and> t' \<in> range f\<close> for j by blast
      hence \<open>ftF (ff (Suc j))\<close> for j
        by (metis "***"(2) imageE is_processT2_TR is_processT3_TR)
      hence \<open>tF (ff j)\<close> for j
        using strict_monoD[OF "$$"(1), of j \<open>Suc j\<close>, simplified]
        by (metis strict_prefixE' front_tickFree_append_iff list.distinct(1))
      from "$$"(2) "***"(2) have \<open>ff (j + i) \<in> \<T> P\<close> for i j
        by (simp add: subset_iff) (meson is_processT3_TR rangeI)
      have $$$$ : \<open>\<exists>w. trace_hide (ff i) (ev ` A) \<le> t @ w\<close> for i
      proof -
        from "$$"(2) obtain j where \<open>ff i \<le> f j\<close> by auto
        moreover from "**" isInfHiddenRun_1 have \<open>\<exists>w. seqRun t x j = t @ w\<close>
          by (simp add: seqRun_def) 
        ultimately show \<open>\<exists>w. trace_hide (ff i) (ev ` A) \<le> t @ w\<close>
          by (metis "***"(1) mono_trace_hide)
      qed
      have \<open>\<exists>i. t \<le> trace_hide (ff i) (ev ` A)\<close>
      proof (rule ccontr)
        define fff where \<open>fff i \<equiv> trace_hide (ff i) (ev ` A)\<close> for i
        assume assm : \<open>\<nexists>i. t \<le> fff i\<close>
        moreover from "$$$$" have \<open>\<forall>i. \<exists>w. fff i \<le> t @ w\<close> unfolding fff_def ..
        ultimately have assm_bis : \<open>\<forall>i. fff i \<le> t\<close>
          by (metis prefixI le_same_imp_eq_or_less order.order_iff_strict)
        have \<open>mono fff\<close>
          by (rule monoI, simp add: fff_def)
            (metis "$$"(1) prefixE prefixI filter_append strict_mono_less_eq)
        from mono_constant[OF this assm_bis]
        obtain j where \<open>j \<le> i \<Longrightarrow> fff i = fff j\<close> for i by blast
        have \<open>fff j \<in> \<D> (P \ A)\<close>
          apply (unfold D_Hiding, clarify)
          apply (rule exI[of _ \<open>ff j\<close>], rule exI[of _ \<open>[]\<close>])
          apply (simp add: fff_def \<open>tF (ff j)\<close>)
          apply (rule disjI2)
          apply (rule exI[of _ \<open>\<lambda>i. ff (j + i)\<close>])
          apply (intro conjI)
          subgoal by (simp add: "$$"(1) strict_monoI strict_mono_less)
          subgoal by (simp add: \<open>\<And>i. ff (j + i) \<in> \<T> P\<close>)
          subgoal by (metis \<open>\<And>i. j \<le> i \<Longrightarrow> fff i = fff j\<close> fff_def le_add1)
          subgoal by (metis Nat.add_0_right rangeI) .
        thus False
          by (metis (no_types) "**" prefixE T_imp_front_tickFree append.right_neutral assm_bis
              front_tickFree_append_iff is_processT3_TR is_processT7 t_le_seqRun)
      qed
      then obtain j where \<open>t \<le> trace_hide (ff j) (ev ` A)\<close> ..
      have "\<pounds>" : \<open>s = trace_hide (ff j) (ev ` (A \<union> B)) @ u\<close>
      proof (unfold "*"(3), rule arg_cong[where f = \<open>\<lambda>x. x @ _\<close>])
        from "$$"(1) "$$$" obtain l where \<open>ff j \<le> f l\<close>
          by (metis dual_order.trans order_less_imp_le rangeE strict_mono_Suc_iff)
        from mono_trace_hide[OF this] have \<open>trace_hide (ff j) (ev ` A) \<le> seqRun t x l\<close>
          unfolding "***"(1) by presburger
        with mono_trace_hide[OF this] mono_trace_hide[OF \<open>t \<le> trace_hide (ff j) (ev ` A)\<close>]
        show \<open>trace_hide t (ev ` B) = trace_hide (ff j) (ev ` (A \<union> B))\<close>
          by (metis trH_x dual_order.eq_iff trace_hide_ev_union)
      qed
      have "\<pounds>\<pounds>" : \<open>trace_hide (ff (j + i)) (ev ` (A \<union> B)) = trace_hide (ff (j + 0)) (ev ` (A \<union> B))\<close> for i
      proof -
        from "$$"(1) "$$$" obtain l where \<open>ff (j + i) \<le> f l\<close>
          by (metis dual_order.trans order_less_imp_le rangeE strict_mono_Suc_iff)
        from mono_trace_hide[OF this] have \<open>trace_hide (ff (j + i)) (ev ` A) \<le> seqRun t x l\<close> 
          unfolding "***"(1) by presburger
        from mono_trace_hide[OF this, of B]
          mono_trace_hide[THEN mono_trace_hide, of _ _ B A,
            OF \<open>strict_mono ff\<close>[THEN strict_mono_mono, THEN monoD, of j \<open>j + i\<close>, simplified]]
          mono_trace_hide[OF \<open>t \<le> trace_hide (ff j) (ev ` A)\<close>, of B]
        show \<open>trace_hide (ff (j + i)) (ev ` (A \<union> B)) =
              trace_hide (ff (j + 0)) (ev ` (A \<union> B))\<close> by (simp add: trH_x)
      qed
      show \<open>s \<in> \<D> (P \ (A \<union> B))\<close>
        apply (unfold D_Hiding, clarify)
        apply (rule exI[of _ \<open>ff j\<close>], rule exI[of _ u])
        apply (intro conjI)
        subgoal by (fact \<open>ftF u\<close>)
        subgoal by (fact \<open>tF (ff j)\<close>)
        subgoal by (fact "\<pounds>")
        apply (rule disjI2)
        apply (rule exI[of _ \<open>\<lambda>i. ff (j + i)\<close>])
        apply (intro conjI)
        subgoal by (simp add: "$$"(1) strict_monoI strict_mono_less)
        subgoal by (simp add: \<open>\<And>i. ff (j + i) \<in> \<T> P\<close>)
        subgoal by (use "\<pounds>\<pounds>" in blast)
        by (metis Nat.add_0_right rangeI)
    qed
  next
    assume subset_div : \<open>\<D> (P \ A \ B) \<subseteq> \<D> (P \ (A \<union> B))\<close>
    fix s X assume \<open>(s, X) \<in> \<F> (P \ A \ B)\<close>
    from this[simplified F_Hiding[of \<open>P \ A\<close> B]] D_Hiding[of \<open>P \ A\<close> B]
    consider \<open>s \<in> \<D> (P \ A \ B)\<close>
      | t where \<open>s = trace_hide t (ev ` B)\<close> \<open>(t, X \<union> ev ` B) \<in> \<F> (P \ A)\<close> by blast
    thus \<open>(s, X) \<in> \<F> (P \ (A \<union> B))\<close>
    proof cases
      from subset_div D_F show \<open>s \<in> \<D> (P \ A \ B) \<Longrightarrow> (s, X) \<in> \<F> (P \ (A \<union> B))\<close> by blast
    next
      fix t assume * : \<open>s = trace_hide t (ev ` B)\<close> \<open>(t, X \<union> ev ` B) \<in> \<F> (P \ A)\<close>
      from "*"(2) consider \<open>t \<in> \<D> (P \ A)\<close>
        | u where \<open>t = trace_hide u (ev ` A)\<close> \<open>(u, X \<union> ev ` B \<union> ev ` A) \<in> \<F> P\<close>
        unfolding F_Hiding D_Hiding by blast
      thus \<open>(s, X) \<in> \<F> (P \ (A \<union> B))\<close>
      proof cases
        assume \<open>t \<in> \<D> (P \ A)\<close>
        with "*"(1) mem_D_imp_mem_D_Hiding have \<open>s \<in> \<D> (P \ A \ B)\<close> by fast
        with subset_div D_F show \<open>(s, X) \<in> \<F> (P \ (A \<union> B))\<close> by blast
      next
        fix u assume ** : \<open>t = trace_hide u (ev ` A)\<close> \<open>(u, X \<union> ev ` B \<union> ev ` A) \<in> \<F> P\<close>
        from "*"(1) "**"(1) have \<open>s = trace_hide u (ev ` (A \<union> B))\<close> by simp
        moreover from "**"(2) have \<open>(u, X \<union> ev ` (A \<union> B)) \<in> \<F> P\<close>
          by (simp add: image_Un sup_commute sup_left_commute)
        ultimately show \<open>(s, X) \<in> \<F> (P \ (A \<union> B))\<close> unfolding F_Hiding by blast
      qed
    qed
  qed
next
  show \<open>P \ A \ B \<le> P \ (A \<union> B)\<close> by (fact Hiding_Hiding_less_eq_process_Hiding_Un)
qed




subsection\<open> Sync Operator Laws \<close>  

subsubsection\<open> Preliminaries \<close>

lemma tickFree_isInfHiddenRun : \<open>tF s\<close>
  if \<open>isInfHiddenRun f P A\<close> and \<open>s \<in> range f\<close>
proof -
  from \<open>s \<in> range f\<close> obtain i where \<open>s = f i\<close> ..
  moreover have \<open>f i < f (Suc i)\<close> by (meson \<open>isInfHiddenRun f P A\<close> strict_mono_Suc_iff)
  ultimately obtain t where \<open>t \<noteq> []\<close> \<open>f (Suc i) = s @ t\<close> by (meson strict_prefixE' list.discI)
  moreover from \<open>isInfHiddenRun f P A\<close> is_processT2_TR
  have \<open>ftF (f (Suc i))\<close> by blast
  ultimately show \<open>tF s\<close> by (simp add: front_tickFree_append_iff)
qed

lemma Hiding_interleave: 
  \<open>r setinterleaves ((t, u), C) \<Longrightarrow>
   (trace_hide r A) setinterleaves ((trace_hide t A, trace_hide u A), C)\<close>
  (* The hypothesis \<open>A \<inter> C = {}\<close> was useless, see if we can obtain more powerful results *)
proof (induct \<open>(t, C, u)\<close> arbitrary: r t u rule: setinterleaving.induct)
  case 1 thus ?case by simp
next
  case (2 x t) thus ?case by auto
next
  case (3 y u) thus ?case by auto
next
  case (4 x t y u)
  thus ?case 
    by (simp split: if_splits)
      (safe, simp_all, (use SyncSingleHeadAdd setinterleaving_sym in blast)+)
qed

lemma non_Sync_interleaving: 
  \<open>(set t \<union> set u) \<inter> C = {} \<Longrightarrow> setinterleaving (t, C, u) \<noteq> {}\<close> (* FINALLY NON-USED*)
  by (induct \<open>(t, C, u)\<close> arbitrary: t u rule: setinterleaving.induct) simp_all


lemma interleave_Hiding: 
  \<open>s setinterleaves ((trace_hide t A, trace_hide u A), C) 
   \<Longrightarrow> \<exists>r. s = trace_hide r A \<and> r setinterleaves ((t, u), C)\<close> if \<open>A \<inter> C = {}\<close>
proof (induct \<open>(t, C, u)\<close> arbitrary: t u s rule: setinterleaving.induct)
  case 1
  thus ?case by simp
next
  case (2 y u)
  from "2.prems" \<open>A \<inter> C = {}\<close> show ?case
    by (simp add: disjoint_iff split: if_split_asm)
      (metis "2.hyps" "2.prems" emptyLeftProperty filter.simps(1))+
next
  case (3 x t)
  from "3.prems" \<open>A \<inter> C = {}\<close> show ?case
    by (simp add: disjoint_iff split: if_split_asm)
      (metis "3.hyps" "3.prems" emptyRightProperty filter.simps(1))+
next
  case (4 x t y u)
  from "4.prems" \<open>A \<inter> C = {}\<close> show ?case
    apply (cases \<open>x = y\<close>, simp_all add: disjoint_iff split: if_split_asm)
    subgoal using "4.hyps"(1) by force
    subgoal by (metis (no_types, lifting) "4.hyps"(3) "4.hyps"(4) filter.simps(2))
    subgoal by (metis (no_types, lifting) "4.hyps"(3) filter.simps(2))
    subgoal using "4.hyps"(2) by force
    subgoal by (metis (no_types, lifting) "4.hyps"(3) "4.hyps"(4) filter.simps(2)) 
    subgoal using "4.hyps"(5) by force 
    subgoal by (metis (no_types, lifting) "4.hyps"(2) "4.hyps"(4) filter.simps(2))
    subgoal by (metis (no_types, lifting) "4.hyps"(3) "4.hyps"(5) filter.simps(2))
    subgoal by (metis (no_types, lifting) "4.hyps"(4) filter.simps(2))
    done
qed


lemma le_trace_hide : \<open>u \<le> trace_hide t S \<Longrightarrow> \<exists>u'. u = trace_hide u' S \<and> u' \<le> t\<close>
proof (induct t arbitrary: u)
  show \<open>u \<le> trace_hide [] S \<Longrightarrow> \<exists>u'. u = trace_hide u' S \<and> u' \<le> []\<close> for u by simp
next
  fix a t u assume prem: \<open>u \<le> trace_hide (a # t) S\<close>
  assume hyp : \<open>u \<le> trace_hide t S \<Longrightarrow> \<exists>u'. u = trace_hide u' S \<and> u' \<le> t\<close> for u
  from prem consider \<open>u = []\<close> | \<open>a \<in> S\<close> \<open>u \<le> trace_hide t S\<close>
    | v where \<open>a \<notin> S\<close> \<open>u = a # v\<close> \<open>v \<le> trace_hide t S\<close>
    by (cases u) (simp_all split: if_split_asm)
  thus \<open>\<exists>u'. u = trace_hide u' S \<and> u' \<le> a # t\<close>
  proof cases
    show \<open>u = [] \<Longrightarrow> \<exists>u'. u = trace_hide u' S \<and> u' \<le> a # t\<close>
      by (metis filter.simps(1) nil_le)
  next
    assume \<open>a \<in> S\<close> \<open>u \<le> trace_hide t S\<close>
    from hyp[OF \<open>u \<le> trace_hide t S\<close>] obtain u' where \<open>u = trace_hide u' S \<and> u' \<le> t\<close> ..
    with \<open>a \<in> S\<close> have \<open>u = trace_hide (a # u') S \<and> a # u' \<le> a # t\<close> by simp
    thus \<open>\<exists>u'. u = trace_hide u' S \<and> u' \<le> a # t\<close> ..
  next
    fix v assume \<open>a \<notin> S\<close> \<open>u = a # v\<close> \<open>v \<le> trace_hide t S\<close>
    from hyp[OF \<open>v \<le> trace_hide t S\<close>] obtain v' where \<open>v = trace_hide v' S \<and> v' \<le> t\<close> ..
    with \<open>a \<notin> S\<close> \<open>u = a # v\<close> have \<open>u = trace_hide (a # v') S \<and> a # v' \<le> a # t\<close> by simp
    thus \<open>\<exists>u'. u = trace_hide u' S \<and> u' \<le> a # t\<close> ..
  qed
qed



lemma append_interleave :
  \<open>s1 setinterleaves ((t1, u1), S) \<Longrightarrow> s2 setinterleaves ((t2, u2), S) \<Longrightarrow>
   (s1 @ s2) setinterleaves ((t1 @ t2, u1 @ u2), S)\<close>
proof (induct \<open>(t1, S, u1)\<close> arbitrary: s1 t1 u1 rule: setinterleaving.induct)
  case 1 thus ?case by simp
next
  case (2 y u1)
  thus ?case by (auto split: if_split_asm)
      (use SyncSingleHeadAdd setinterleaving_sym in blast)
next
  case (3 x t1)
  thus ?case by (auto split: if_split_asm) (blast intro: SyncSingleHeadAdd)
next
  case (4 x t2 y u2)
  thus ?case by auto
qed


subsubsection \<open>The Theorem: Sync and Hiding\<close>

theorem Hiding_Sync : \<open>(P \<lbrakk>S\<rbrakk> Q) \ A = (P \ A) \<lbrakk>S\<rbrakk> (Q \ A)\<close>
  if \<open>finite A\<close> and \<open>A \<inter> S = {}\<close> for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    \<comment> \<open>Monster theorem!\<close>
proof (subst Process_eq_spec_optimized, safe)
  let ?trH_A = \<open>\<lambda>t. trace_hide t (ev ` A)\<close> and ?tick_S = \<open>range tick \<union> ev ` S\<close>
  fix s assume \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q \ A)\<close>
  then obtain t u
    where * : \<open>ftF u\<close> \<open>tF t\<close> \<open>s = ?trH_A t @ u\<close>
      \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk> Q) \<or> (\<exists>x. isInfHidden_seqRun_strong x (P \<lbrakk>S\<rbrakk> Q) A t)\<close>
    by (elim D_Hiding_seqRunE)
  from "*"(4) show \<open>s \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close>
  proof (elim disjE exE)
    assume \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
    then obtain t' u' r' v'
      where ** : \<open>ftF v'\<close> \<open>tF r' \<or> v' = []\<close>
        \<open>t = r' @ v'\<close> \<open>r' setinterleaves ((t', u'), ?tick_S)\<close>
        \<open>t' \<in> \<D> P \<and> u' \<in> \<T> Q \<or> t' \<in> \<D> Q \<and> u' \<in> \<T> P\<close>
      unfolding D_Sync by blast
    { fix t' u' and P Q
      assume *** : \<open>r' setinterleaves ((t', u'), ?tick_S)\<close>
        \<open>t' \<in> \<D> P\<close> \<open>u' \<in> \<T> Q\<close>
      have \<open>?trH_A r' setinterleaves ((?trH_A t', ?trH_A u'), ?tick_S)\<close>
        using "***"(1) Hiding_interleave by blast
      moreover from "***"(2) mem_D_imp_mem_D_Hiding have \<open>?trH_A t' \<in> \<D> (P \ A)\<close> by blast
      moreover from "***"(3) mem_T_imp_mem_T_Hiding have \<open>?trH_A u' \<in> \<T> (Q \ A)\<close> by blast
      ultimately have \<open>s \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close>
        apply (simp add: "*"(3) D_Sync)
        apply (rule exI[of _ \<open>?trH_A t'\<close>], rule exI[of _ \<open>?trH_A u'\<close>],
            rule exI[of _ \<open>?trH_A r'\<close>], rule exI[of _ \<open>?trH_A v' @ u\<close>])
        apply (simp add: "*"(3) "**"(3) Hiding_tickFree)
        using "*"(1, 2) "**"(3) Hiding_tickFree front_tickFree_append tickFree_append_iff by blast
    } note $ = this
    from "**"(5) show \<open>s \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close>
    proof (elim disjE conjE)
      show \<open>t' \<in> \<D> P \<Longrightarrow> u' \<in> \<T> Q \<Longrightarrow> s \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close>
        by (metis "$" "**"(4))
      show \<open>t' \<in> \<D> Q \<Longrightarrow> u' \<in> \<T> P \<Longrightarrow> s \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close>
        by (metis "$" "**"(4) Sync_commute)
    qed
  next
    fix x assume ** : \<open>isInfHidden_seqRun_strong x (P \<lbrakk>S\<rbrakk> Q) A t\<close>
    from "**" have *** : \<open>\<exists>t' u'. t' \<in> \<T> P \<and> u' \<in> \<T> Q \<and>
                                  seqRun t x i setinterleaves ((t', u'), ?tick_S)\<close> for i
      unfolding T_Sync D_Sync by blast
    define ftu where \<open>ftu i \<equiv> SOME (t', u'). t' \<in> \<T> P \<and> u' \<in> \<T> Q \<and>
                              seqRun t x i setinterleaves ((t', u'), ?tick_S)\<close> for i
    define ft fu where \<open>ft \<equiv> \<lambda>i. fst (ftu i)\<close> and \<open>fu \<equiv> \<lambda>i. snd (ftu i)\<close>
    have **** : \<open>ft i \<in> \<T> P\<close> \<open>fu i \<in> \<T> Q\<close>
      \<open>seqRun t x i setinterleaves ((ft i, fu i), ?tick_S)\<close> for i
      by (use "***"[of i] in \<open>simp add: ft_def fu_def,
                              cases \<open>ftu i\<close>, simp add: ftu_def,
                              metis (mono_tags, lifting) case_prod_conv someI_ex\<close>)+
    from "**" have \<open>set (seqRun t x i) \<subseteq> set t \<union> ev ` A\<close> for i
      by (auto simp add: seqRun_def)

    have \<open>set (ft i) \<union> set (fu i) \<subseteq> set t \<union> ev ` A\<close> for i
      by (rule subset_trans[OF interleave_set[OF "****"(3)]])
        (fact \<open>set (seqRun t x i) \<subseteq> set t \<union> ev ` A\<close>)
    have \<open>inj ftu\<close>
    proof (rule injI)
      fix i j assume \<open>ftu i = ftu j\<close>
      obtain t' u' where \<open>(t', u') = ftu i\<close> by (metis surj_pair)
      with \<open>ftu i = ftu j\<close> have \<open>seqRun t x i setinterleaves ((t', u'), ?tick_S)\<close>
        \<open>seqRun t x j setinterleaves ((t', u'), ?tick_S)\<close>
        by (metis "****"(3) fst_conv ft_def fu_def snd_conv)+
      from interleave_eq_size[OF this] have \<open>length (seqRun t x i) = length (seqRun t x j)\<close> .
      thus \<open>i = j\<close> by simp
    qed
    hence \<open>infinite (range ftu)\<close> using finite_imageD by blast
    moreover have \<open>range ftu \<subseteq> range ft \<times> range fu\<close>
      by (clarify, metis fst_conv ft_def fu_def rangeI snd_conv)
    ultimately have \<open>infinite (range ft) \<or> infinite (range fu)\<close> 
      by (meson finite_SigmaI infinite_super)

    { fix ft fu P Q
      assume assms : \<open>infinite (range ft)\<close>
        \<open>\<And>i. set (ft i) \<union> set (fu i) \<subseteq> set t \<union> ev ` A\<close>
        \<open>\<And>i. ft i \<in> \<T> P\<close> \<open>\<And>i. fu i \<in> \<T> Q\<close>
        \<open>\<And>i. seqRun t x i setinterleaves ((ft i, fu i), ?tick_S)\<close>

      have \<open>finite {t. \<exists>t'\<in>range ft. t = take i t'}\<close> for i
      proof (rule finite_subset)
        show \<open>  {w. \<exists>t'\<in>range ft. w = take i t'}
              \<subseteq> {w. set w \<subseteq> set t \<union> ev ` A \<and> length w \<le> i}\<close>
          by auto (meson Un_iff assms(2) in_set_takeD subsetD)
      next
        show \<open>finite {w. set w \<subseteq> set t \<union> ev ` A \<and> length w \<le> i}\<close>
          by (rule finite_lists_length_le) (simp add: \<open>finite A\<close>)
            \<comment> \<open>Here we use the assumption @{thm \<open>finite A\<close>}.\<close>
      qed
      with assms(1) obtain ft' :: \<open>nat \<Rightarrow> _\<close>
        where $ : \<open>strict_mono ft'\<close> \<open>range ft' \<subseteq> {w. \<exists>t'\<in>range ft. w \<le> t'}\<close>
        using KoenigLemma by blast
      from "$"(2) assms(3) is_processT3_TR have \<open>range ft' \<subseteq> \<T> P\<close> by blast
      define ft'' where \<open>ft'' i \<equiv> ft' (i + length t)\<close> for i
      find_theorems name: unifo
      from \<open>range ft' \<subseteq> \<T> P\<close> have \<open>range ft'' \<subseteq> \<T> P\<close> and \<open>strict_mono ft''\<close>
        by (auto simp add: ft''_def "$"(1) strict_monoD strict_monoI)
      have $$ : \<open>?trH_A (ft'' i) = ?trH_A (ft'' 0)\<close> for i
      proof -
        have \<open>length t \<le> length (ft'' 0)\<close>
          by (metis "$"(1) add_0 add_leD1 ft''_def length_strict_mono)
        obtain t' where \<open>ft'' i = ft'' 0 @ t'\<close>
          by (meson prefixE \<open>strict_mono ft''\<close> strict_mono_less_eq zero_order(1))
        moreover from "$"(2) obtain j where \<open>ft'' i \<le> ft j\<close> by (auto simp add: ft''_def)
        ultimately obtain t'' where \<open>ft j = ft'' 0 @ t' @ t''\<close> by (metis prefixE append.assoc)
        have \<open>set (t' @ t'') \<subseteq> set (drop (length t) (seqRun t x j))\<close>
        proof (rule subset_trans)
          show \<open>set (t' @ t'') \<subseteq> set (drop (length (ft'' 0)) (seqRun t x j))\<close>
            by (rule interleave_order, fold \<open>ft j = ft'' 0 @ t' @ t''\<close>, fact assms(5))
        next
          show \<open>set (drop (length (ft'' 0)) (seqRun t x j)) \<subseteq> set (drop (length t) (seqRun t x j))\<close>
            by (simp add: \<open>length t \<le> length (ft'' 0)\<close> set_drop_subset_set_drop)
        qed
        also from "**" have \<open>set (drop (length t) (seqRun t x j)) \<subseteq> ev ` A\<close>
          by (auto simp add: seqRun_def)
        finally show \<open>?trH_A (ft'' i) = ?trH_A (ft'' 0)\<close>
          by (simp add: \<open>ft'' i = ft'' 0 @ t'\<close> subset_iff)
      qed
      from "$"(2) obtain i where \<open>ft'' 0 \<le> ft i\<close> by (auto simp add: ft''_def)
      with prefixE obtain v where \<open>ft i = ft'' 0 @ v\<close> by blast

      have \<open>ftF u\<close> by (fact "*"(1))
      moreover have \<open>tF (?trH_A (seqRun t x i)) \<or> u = []\<close>
        by (metis "*"(2) "**" Hiding_tickFree trace_hide_seqRun_eq_iff)
      moreover have \<open>s = ?trH_A (seqRun t x i) @ u\<close>
        by (metis "*"(3) "**" trace_hide_seqRun_eq_iff)
      moreover have \<open>?trH_A (seqRun t x i) setinterleaves ((?trH_A (ft i), ?trH_A (fu i)), ?tick_S)\<close>
        using assms(5) Hiding_interleave by blast
      moreover have \<open>?trH_A (ft i) \<in> \<D> (P \ A)\<close>
        apply (unfold D_Hiding, clarify)
        apply (rule exI[of _ \<open>ft'' 0\<close>])
        apply (rule exI[of _ \<open>?trH_A v\<close>])
        apply (intro conjI)
        subgoal by (metis assms(3) Hiding_front_tickFree \<open>ft i = ft'' 0 @ v\<close>
              front_tickFree_Nil front_tickFree_nonempty_append_imp is_processT2_TR) 
        subgoal by (metis strict_prefixE' T_imp_front_tickFree \<open>range ft'' \<subseteq> \<T> P\<close> \<open>strict_mono ft''\<close>
              front_tickFree_append_iff list.distinct(1) range_subsetD strict_mono_Suc_iff)
        subgoal by (simp add: \<open>ft i = ft'' 0 @ v\<close>)
        subgoal using "$$" \<open>range ft'' \<subseteq> \<T> P\<close> \<open>strict_mono ft''\<close> by blast .
      moreover have \<open>?trH_A (fu i) \<in> \<T> (Q \ A)\<close>
      proof (cases \<open>\<exists>t'. ?trH_A t' = ?trH_A (fu i) \<and> (t', ev ` A) \<in> \<F> Q\<close>)
        assume \<open>\<exists>t'. ?trH_A t' = ?trH_A (fu i) \<and> (t', ev ` A) \<in> \<F> Q\<close>
        then obtain t' where \<open>?trH_A (fu i) = ?trH_A t'\<close> \<open>(t', ev ` A) \<in> \<F> Q\<close> by metis
        thus \<open>?trH_A (fu i) \<in> \<T> (Q \ A)\<close> unfolding T_Hiding by blast
      next
        assume \<open>\<nexists>t'. ?trH_A t' = ?trH_A (fu i) \<and> (t', ev ` A) \<in> \<F> Q\<close>
        with assms(4) inf_hidden obtain fu' j
          where $$$ : \<open>isInfHiddenRun fu' Q A\<close> \<open>fu i = fu' j\<close> by blast
        show \<open>?trH_A (fu i) \<in> \<T> (Q \ A)\<close>
          apply (unfold T_Hiding, simp)
          apply (rule disjI2)
          apply (rule exI[of _ \<open>fu' j\<close>], rule exI[of _ \<open>[]\<close>])
          apply (intro conjI)
          subgoal by simp
          subgoal by (metis "$$$"(1) strict_prefixE' T_imp_front_tickFree neq_Nil_conv
                front_tickFree_nonempty_append_imp strict_mono_Suc_iff)
          subgoal by (simp add: "$$$"(2))
          subgoal using "$$$"(1) by blast .
      qed
      ultimately have \<open>s \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close> unfolding D_Sync by blast
    } note $ = this

    from \<open>infinite (range ft) \<or> infinite (range fu)\<close>
    show \<open>s \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close>
    proof (elim disjE)
      from "$" "****" \<open>\<And>i. set (ft i) \<union> set (fu i) \<subseteq> set t \<union> ev ` A\<close>
      show \<open>infinite (range ft) \<Longrightarrow> s \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close> by blast
    next
      from "$" "****" \<open>\<And>i. set (ft i) \<union> set (fu i) \<subseteq> set t \<union> ev ` A\<close>
      show \<open>infinite (range fu) \<Longrightarrow> s \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close> 
        by (metis Sync_commute setinterleaving_sym sup_commute)
    qed
  qed
next
  let ?trH_A = \<open>\<lambda>t. trace_hide t (ev ` A)\<close> and ?tick_S = \<open>range tick \<union> ev ` S\<close>
  assume same_div : \<open>\<D> (P \<lbrakk>S\<rbrakk> Q \ A) = \<D> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close>
  fix s X assume \<open>(s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q \ A)\<close>
  then consider \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q \ A)\<close>
    | t where \<open>s = trace_hide t (ev ` A)\<close> \<open>(t, X \<union> ev ` A) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close>
    unfolding F_Hiding D_Hiding by blast
  thus \<open>(s, X) \<in> \<F> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close>
  proof cases
    from same_div D_F show \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q \ A) \<Longrightarrow> (s, X) \<in> \<F> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close> by blast
  next
    fix t assume * : \<open>s = ?trH_A t\<close> \<open>(t, X \<union> ev ` A) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close>
    then consider \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
      | (F) t_P X_P t_Q X_Q
      where \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
        \<open>t setinterleaves ((t_P, t_Q), ?tick_S)\<close>
        \<open>X \<union> ev ` A = (X_P \<union> X_Q) \<inter> ?tick_S \<union> X_P \<inter> X_Q\<close>
      by (auto simp add: F_Sync D_Sync) 
    thus \<open>(s, X) \<in> \<F> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close>
    proof cases
      assume \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
      with "*"(1) mem_D_imp_mem_D_Hiding have \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q \ A)\<close> by blast
      with same_div D_F show \<open>(s, X) \<in> \<F> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close> by blast
    next
      case F
      from inf_hidden[OF _ F(1)[THEN F_T], of A] inf_hidden[OF _ F(2)[THEN F_T], of A]
      consider (D_P) f_P where \<open>isInfHiddenRun f_P P A\<close> \<open>t_P \<in> range f_P\<close>
        | (D_Q) f_Q where \<open>isInfHiddenRun f_Q Q A\<close> \<open>t_Q \<in> range f_Q\<close>
        | (F_both) t_P' t_Q'
        where \<open>?trH_A t_P' = ?trH_A t_P\<close> \<open>(t_P', ev ` A) \<in> \<F> P\<close>
          \<open>?trH_A t_Q' = ?trH_A t_Q\<close> \<open>(t_Q', ev ` A) \<in> \<F> Q\<close>
        by blast
      thus \<open>(s, X) \<in> \<F> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close>
      proof cases
        case D_P
        have $ : \<open>?trH_A t_P \<in> \<D> (P \ A)\<close>
          apply (unfold D_Hiding, clarify)
          apply (rule exI[of _ \<open>t_P\<close>], rule exI[of _ \<open>[]\<close>])
          using tickFree_isInfHiddenRun D_P front_tickFree_Nil by blast
        from F(2) F_T mem_T_imp_mem_T_Hiding
        have $$ : \<open>?trH_A t_Q \<in> \<T> (Q \ A)\<close> by blast
        show \<open>(s, X) \<in> \<F> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close>
          apply (simp add: F_Sync)
          apply (rule disjI2)
          apply (rule exI[of _ \<open>?trH_A t_P\<close>])
          apply (rule exI[of _ \<open>?trH_A t_Q\<close>])
          apply (rule exI[of _ \<open>?trH_A t\<close>], rule exI[of _ \<open>[]\<close>])
          by (simp add: "*"(1) F(3) Hiding_interleave "$" "$$")
      next
        case D_Q
        from F(1) F_T mem_T_imp_mem_T_Hiding
        have $ : \<open>?trH_A t_P\<in> \<T> (P \ A)\<close> by blast
        have $$ : \<open>?trH_A t_Q \<in> \<D> (Q \ A)\<close>
          apply (unfold D_Hiding, clarify)
          apply (rule exI[of _ \<open>t_Q\<close>], rule exI[of _ \<open>[]\<close>])
          using tickFree_isInfHiddenRun D_Q front_tickFree_Nil by blast
        show \<open>(s, X) \<in> \<F> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close>
          apply (simp add: F_Sync)
          apply (rule disjI2)
          apply (rule exI[of _ \<open>?trH_A t_Q\<close>])
          apply (rule exI[of _ \<open>?trH_A t_P\<close>])
          apply (rule exI[of _ \<open>?trH_A t\<close>], rule exI[of _ \<open>[]\<close>])
          by (simp add: "*"(1) F(3) Hiding_interleave setinterleaving_sym "$" "$$")
      next
        case F_both
        from F(4) \<open>A \<inter> S = {}\<close> have \<open>ev ` A \<subseteq> X_P\<close> and \<open>ev ` A \<subseteq> X_Q\<close> by auto
        have \<open>(?trH_A t_P, X_P) \<in> \<F> (P \ A)\<close>
          by (simp add: F_Hiding) (metis F(1) F_both(1) \<open>ev ` A \<subseteq> X_P\<close> sup.orderE)
        moreover have \<open>(?trH_A t_Q, X_Q) \<in> \<F> (Q \ A)\<close>
          by (simp add: F_Hiding) (metis F(2) F_both(3) \<open>ev ` A \<subseteq> X_Q\<close> sup.orderE)
        moreover from F(3) Hiding_interleave
        have \<open>s setinterleaves ((?trH_A t_P, ?trH_A t_Q), ?tick_S)\<close>
          unfolding "*"(1) by blast
        ultimately have \<open>(s, (X_P \<union> X_Q) \<inter> ?tick_S \<union> X_P \<inter> X_Q) \<in> \<F> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close>
          unfolding F_Sync by blast
        moreover from F(4) have \<open>X \<subseteq> (X_P \<union> X_Q) \<inter> ?tick_S \<union> X_P \<inter> X_Q\<close> by blast
        ultimately show \<open>(s, X) \<in> \<F> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close> by (fact is_processT4)
      qed
    qed
  qed
next
  let ?trH_A = \<open>\<lambda>t. trace_hide t (ev ` A)\<close> and ?tick_S = \<open>range tick \<union> ev ` S\<close>
  fix s assume \<open>s \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close>
  then obtain t_P t_Q r v
    where * : \<open>ftF v\<close> \<open>tF r \<or> v = []\<close> \<open>s = r @ v\<close> \<open>r setinterleaves ((t_P, t_Q), ?tick_S)\<close>
      \<open>t_P \<in> \<D> (P \ A) \<and> t_Q \<in> \<T> (Q \ A) \<or> t_P \<in> \<D> (Q \ A) \<and> t_Q \<in> \<T> (P \ A)\<close>
    unfolding D_Sync by blast
  from \<open>s \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close> have \<open>ftF s\<close>
    by (simp add: D_imp_front_tickFree)
  { fix t_P t_Q and P Q
    assume ** : \<open>r setinterleaves ((t_P, t_Q), ?tick_S)\<close>
      \<open>t_P \<in> \<D> (P \ A)\<close> \<open>t_Q \<in> \<T> (Q \ A)\<close>
    from **(2) obtain t u
      where *** : \<open>ftF u\<close> \<open>tF t\<close> \<open>t_P = ?trH_A t @ u\<close>
        \<open>t \<in> \<D> P \<or> (\<exists>x. isInfHidden_seqRun_strong x P A t)\<close>
      by (elim D_Hiding_seqRunE)
    from interleave_append_left[OF "**"(1)[unfolded "***"(3)]]
    obtain t_Q1 t_Q2 r1 r2
      where **** : \<open>t_Q = t_Q1 @ t_Q2\<close> \<open>r = r1 @ r2\<close>
        \<open>r1 setinterleaves ((?trH_A t, t_Q1), ?tick_S)\<close>
        \<open>r2 setinterleaves ((u, t_Q2), ?tick_S)\<close> by blast
    from "**"(3) consider t_Q' where \<open>t_Q = ?trH_A t_Q'\<close> \<open>(t_Q', ev ` A) \<in> \<F> Q\<close>
      | (D_Q) t' u' where \<open>ftF u'\<close> \<open>tF t'\<close> \<open>t_Q = ?trH_A t' @ u'\<close>
        \<open>t' \<in> \<D> Q \<or> (\<exists>y. isInfHidden_seqRun_strong y Q A t')\<close>
      by (elim T_Hiding_seqRunE)
    hence \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q \ A)\<close>
    proof cases
      fix t_Q' assume \<open>t_Q = ?trH_A t_Q'\<close> \<open>(t_Q', ev ` A) \<in> \<F> Q\<close>
      from trace_hide_append[OF this(1)[unfolded "****"(1)]]
      obtain t_Q1' t_Q2' where $ : \<open>t_Q' = t_Q1' @ t_Q2'\<close> \<open>t_Q1 = ?trH_A t_Q1'\<close>
        \<open>t_Q2 = ?trH_A t_Q2'\<close> by blast
      from \<open>A \<inter> S = {}\<close> have \<open>ev ` A \<inter> ?tick_S = {}\<close> by blast
      from interleave_Hiding[OF this "****"(3)[unfolded "$"(2)]]
      obtain r1' where $$ : \<open>r1 = ?trH_A r1'\<close>
        \<open>r1' setinterleaves ((t, t_Q1'), ?tick_S)\<close> by blast

      show \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q \ A)\<close>
      proof (rule D_Hiding_seqRunI)
        show \<open>ftF (r2 @ v)\<close>
          by (metis "*"(1, 3) "****"(2) \<open>ftF s\<close>
              front_tickFree_append_iff tickFree_append_iff)
      next
        show \<open>tF r1'\<close>
          by (metis "$"(1) "$$"(2) "***"(2) F_imp_front_tickFree SyncWithTick_imp_NTF
              \<open>(t_Q', ev ` A) \<in> \<F> Q\<close> front_tickFree_dw_closed nonTickFree_n_frontTickFree
              non_tickFree_tick tickFree_append_iff ftf_Sync tickFree_imp_front_tickFree)
      next
        from "$$"(1) "*"(3) "****"(2) append.assoc
        show \<open>s = ?trH_A r1' @ r2 @ v\<close> by blast
      next
        from "***"(4) show \<open>r1' \<in> \<D> (P \<lbrakk>S\<rbrakk> Q) \<or>
                            (\<exists>x. \<forall>i. seqRun r1' x i \<in> \<T> (P \<lbrakk>S\<rbrakk> Q) \<and> x i \<in> ev ` A)\<close>
        proof (elim disjE exE)
          assume \<open>t \<in> \<D> P\<close>
          moreover have \<open>t_Q1' \<in> \<T> Q\<close>
            by (metis "$"(1) F_T prefixI \<open>(t_Q', ev ` A) \<in> \<F> Q\<close> is_processT3_TR)
          ultimately have \<open>r1' \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
            unfolding D_Sync using "$$"(2) front_tickFree_Nil by blast
          thus \<open>r1' \<in> \<D> (P \<lbrakk>S\<rbrakk> Q) \<or> (\<exists>x. isInfHidden_seqRun x (P \<lbrakk>S\<rbrakk> Q) A r1')\<close> ..
        next
          fix x assume "\<pounds>" : \<open>isInfHidden_seqRun_strong x P A t\<close>
          from "\<pounds>" \<open>A \<inter> S = {}\<close> have \<open>set (map x [0..<i]) \<inter> ?tick_S = {}\<close> for i
            by (simp add: disjoint_iff image_iff)
              (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(1))
          from "$$"(2)[THEN interleave_append_tail_left, OF this, folded seqRun_def]
          have "\<pounds>\<pounds>" : \<open>seqRun r1' x i setinterleaves ((seqRun t x i, t_Q1'), ?tick_S)\<close> for i .
          have \<open>isInfHidden_seqRun x (P \<lbrakk>S\<rbrakk> Q) A r1'\<close>
          proof (intro allI conjI)
            have \<open>t_Q1' \<in> \<T> Q\<close>
              by (metis "$"(1) F_T prefixI \<open>(t_Q', ev ` A) \<in> \<F> Q\<close> is_processT3_TR)
            with "\<pounds>" "\<pounds>\<pounds>" show \<open>seqRun r1' x i \<in> \<T> (P \<lbrakk>S\<rbrakk> Q)\<close> for i
              unfolding T_Sync by blast
          next
            show \<open>x i \<in> ev ` A\<close> for i by (simp add: "\<pounds>")
          qed
          thus \<open>r1' \<in> \<D> (P \<lbrakk>S\<rbrakk> Q) \<or> (\<exists>x. isInfHidden_seqRun x (P \<lbrakk>S\<rbrakk> Q) A r1')\<close> by blast
        qed
      qed
    next
      case D_Q
      have \<open>t \<in> \<T> P\<close> using "***"(4) D_T by (metis seqRun_0)
      consider \<open>?trH_A t' \<le> t_Q1\<close> | \<open>t_Q1 \<le> ?trH_A t'\<close>
        by (metis "****"(1) D_Q(3) prefixI dual_order.eq_iff le_same_imp_eq_or_less nless_le)
      thus \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q \ A)\<close>
      proof cases
        assume \<open>?trH_A t' \<le> t_Q1\<close>
        from interleave_le_right[OF "****"(3) this]
        obtain r1_bis t_hidden_bis
          where \<open>r1_bis \<le> r1\<close> \<open>t_hidden_bis \<le> ?trH_A t\<close>
            \<open>r1_bis setinterleaves ((t_hidden_bis, ?trH_A t'), ?tick_S)\<close> by blast
        moreover from le_trace_hide[OF \<open>t_hidden_bis \<le> ?trH_A t\<close>]
        obtain t_bis where \<open>t_hidden_bis = ?trH_A t_bis \<and> t_bis \<le> t\<close> ..
        ultimately have $ : \<open>r1_bis \<le> r1\<close> \<open>t_bis \<le> t\<close>
          \<open>r1_bis setinterleaves ((?trH_A t_bis, ?trH_A t'), ?tick_S)\<close> by blast+
        from interleave_Hiding[OF _ "$"(3)] \<open>A \<inter> S = {}\<close>
        obtain r1_bis_unhidden
          where $$ : \<open>r1_bis = ?trH_A r1_bis_unhidden\<close>
            \<open>r1_bis_unhidden setinterleaves ((t_bis, t'), ?tick_S)\<close> by blast
        from "$"(2) \<open>t \<in> \<T> P\<close> is_processT3_TR have \<open>t_bis \<in> \<T> P\<close> by blast
        from D_Q(4) have \<open>r1_bis \<in> \<D> (P \<lbrakk>S\<rbrakk> Q \ A)\<close>
        proof (elim disjE exE)
          assume \<open>t' \<in> \<D> Q\<close>
          with "$$"(2) \<open>t_bis \<in> \<T> P\<close> have \<open>r1_bis_unhidden \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
            by (simp add: D_Sync)
              (use front_tickFree_Nil setinterleaving_sym in blast)
          with "$$"(1) mem_D_imp_mem_D_Hiding show \<open>r1_bis \<in> \<D> (P \<lbrakk>S\<rbrakk> Q \ A)\<close> by blast
        next
          fix y assume \<pounds> : \<open>isInfHidden_seqRun_strong y Q A t'\<close>
            (*  with exists_suff obtain g_suff
          where g_suff_props : \<open>g i = g 0 @ g_suff i\<close> \<open>set (g_suff i) \<subseteq> ev ` A\<close>
                               \<open>set (g_suff i) \<inter> ?tick_S = {}\<close> \<open>strict_mono g_suff\<close> for i by metis *)
          from "\<pounds>" \<open>A \<inter> S = {}\<close> have \<open>set (map y [0..<i]) \<inter> ?tick_S = {}\<close> for i
            by (simp add: disjoint_iff image_iff)
              (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(1))
          from "$$"(2)[THEN interleave_append_tail_right, OF this, folded seqRun_def]
          have $$$ : \<open>seqRun r1_bis_unhidden y i setinterleaves ((t_bis, seqRun t' y i), ?tick_S)\<close> for i .
          have $$$$ : \<open>isInfHidden_seqRun y (P \<lbrakk>S\<rbrakk> Q) A r1_bis_unhidden\<close>
          proof (intro allI conjI)
            from "$$$" "\<pounds>" \<open>t_bis \<in> \<T> P\<close>
            show \<open>seqRun r1_bis_unhidden y i \<in> \<T> (P \<lbrakk>S\<rbrakk> Q)\<close> for i
              unfolding T_Sync by blast
          next
            show \<open>y i \<in> ev ` A\<close> for i by (simp add: "\<pounds>")
          qed
          show \<open>r1_bis \<in> \<D> (P \<lbrakk>S\<rbrakk> Q \ A)\<close>
          proof (rule D_Hiding_seqRunI)
            show \<open>ftF []\<close> by simp
          next
            show \<open>tF r1_bis_unhidden\<close>
              by (metis "$$"(2) D_Q(2) SyncWithTick_imp_NTF T_imp_front_tickFree \<open>t_bis \<in> \<T> P\<close>
                  ftf_Sync nonTickFree_n_frontTickFree non_tickFree_tick
                  tickFree_append_iff tickFree_imp_front_tickFree)
          next
            show \<open>r1_bis = ?trH_A r1_bis_unhidden @ []\<close> by (simp add: $$(1))
          next
            from "$$$$" show \<open>r1_bis_unhidden \<in> \<D> (P \<lbrakk>S\<rbrakk> Q) \<or>
                              (\<exists>x. isInfHidden_seqRun x (P \<lbrakk>S\<rbrakk> Q) A r1_bis_unhidden)\<close> by blast
          qed
        qed
        with "$"(1) show \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q \ A)\<close>
          unfolding less_eq_list_def prefix_def
          by (metis (no_types, opaque_lifting) "*"(3) "****"(2) \<open>ftF s\<close>
              append_Nil2 front_tickFree_append_iff front_tickFree_dw_closed is_processT7)
      next
        assume \<open>t_Q1 \<le> ?trH_A t'\<close>
        from le_trace_hide[OF this] obtain t_Q1_unhidden
          where $ : \<open>t_Q1 = ?trH_A t_Q1_unhidden\<close> \<open>t_Q1_unhidden \<le> t'\<close> by blast
        from \<open>A \<inter> S = {}\<close> have \<open>ev ` A \<inter> ?tick_S = {}\<close> by blast
        from "****"(3)[unfolded "$"(1)]
        have \<open>r1 setinterleaves ((?trH_A t, ?trH_A t_Q1_unhidden), ?tick_S)\<close> .
        from interleave_Hiding[OF \<open>ev ` A \<inter> ?tick_S = {}\<close> this]
        obtain r1_unhidden
          where $$ : \<open>r1 = ?trH_A r1_unhidden\<close>
            \<open>r1_unhidden setinterleaves ((t, t_Q1_unhidden), ?tick_S)\<close> by blast
        from \<open>t_Q1_unhidden \<le> t'\<close> have \<open>t_Q1_unhidden \<in> \<T> Q\<close>
          by (metis D_Q(4) D_T is_processT3_TR t_le_seqRun)

        from "***"(4) have \<open>r1 \<in> \<D> (P \<lbrakk>S\<rbrakk> Q \ A)\<close>
        proof (elim disjE exE)
          assume \<open>t \<in> \<D> P\<close>
          have \<open>r1_unhidden \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
          proof (unfold D_Sync, clarify, intro exI conjI)
            show \<open>ftF []\<close> \<open>tF r1_unhidden \<or> [] = []\<close>
              \<open>r1_unhidden = r1_unhidden @ []\<close> by simp_all
          next
            show \<open>r1_unhidden setinterleaves ((t, t_Q1_unhidden), ?tick_S)\<close> by (fact "$$"(2))
          next
            show \<open>t \<in> \<D> P \<and> t_Q1_unhidden \<in> \<T> Q \<or> t \<in> \<D> Q \<and> t_Q1_unhidden \<in> \<T> P\<close>
              by (simp add: \<open>t \<in> \<D> P\<close> \<open>t_Q1_unhidden \<in> \<T> Q\<close>)
          qed
          thus \<open>r1 \<in> \<D> (P \<lbrakk>S\<rbrakk> Q \ A)\<close> unfolding "$$"(1) by (fact mem_D_imp_mem_D_Hiding)
        next
          fix x assume \<pounds> : \<open>isInfHidden_seqRun_strong x P A t\<close>
          from "\<pounds>" \<open>A \<inter> S = {}\<close> have \<open>set (map x [0..<i]) \<inter> ?tick_S = {}\<close> for i
            by (simp add: disjoint_iff image_iff)
              (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(1))
          from "$$"(2)[THEN interleave_append_tail_left, OF this, folded seqRun_def]
          have "\<pounds>\<pounds>" : \<open>seqRun r1_unhidden x i setinterleaves ((seqRun t x i, t_Q1_unhidden), ?tick_S)\<close> for i .
          have "\<pounds>\<pounds>\<pounds>" : \<open>isInfHidden_seqRun x (P \<lbrakk>S\<rbrakk> Q) A r1_unhidden\<close>
          proof (intro allI conjI)
            from "\<pounds>" "\<pounds>\<pounds>" \<open>t_Q1_unhidden \<in> \<T> Q\<close>
            show \<open>seqRun r1_unhidden x i \<in> \<T> (P \<lbrakk>S\<rbrakk> Q)\<close> for i unfolding T_Sync by blast
          next
            from "\<pounds>" show \<open>x i \<in> ev ` A\<close> for i by blast
          qed
          show \<open>r1 \<in> \<D> (P \<lbrakk>S\<rbrakk> Q \ A)\<close>
          proof (unfold D_Hiding_seqRun, clarify, intro exI conjI)
            show \<open>ftF []\<close> by simp
          next
            from isInfHidden_seqRun_imp_tickFree[OF "\<pounds>\<pounds>\<pounds>"] show \<open>tF r1_unhidden\<close> .
          next
            show \<open>r1 = ?trH_A r1_unhidden @ []\<close> by (simp add: "$$"(1))
          next
            from "\<pounds>\<pounds>\<pounds>" show \<open>r1_unhidden \<in> \<D> (P \<lbrakk>S\<rbrakk> Q) \<or>
                             (\<exists>x. isInfHidden_seqRun x (P \<lbrakk>S\<rbrakk> Q) A r1_unhidden)\<close> by blast
          qed
        qed
        thus \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q \ A)\<close>
          by (metis "*"(3) "****"(2) \<open>ftF s\<close> append.right_neutral
              front_tickFree_append_iff front_tickFree_dw_closed is_processT7)
      qed
    qed
  } note $ = this
  from "*"(5) show \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q \ A)\<close>
    by (elim disjE conjE) (metis "$" "*"(4), metis "$" "*"(4) Sync_commute)
next
  let ?trH_A = \<open>\<lambda>t. trace_hide t (ev ` A)\<close> and ?tick_S = \<open>range tick \<union> ev ` S\<close>
  assume same_div : \<open>\<D> (P \<lbrakk>S\<rbrakk> Q \ A) = \<D> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close>
  fix s X assume \<open>(s, X) \<in> \<F> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close>
  then consider \<open>s \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close>
    | (F) s_P X_P s_Q X_Q
    where \<open>(s_P, X_P) \<in> \<F> (P \ A)\<close> \<open>(s_Q, X_Q) \<in> \<F> (Q \ A)\<close>
      \<open>s setinterleaves ((s_P, s_Q), ?tick_S)\<close>
      \<open>X = (X_P \<union> X_Q) \<inter> ?tick_S \<union> X_P \<inter> X_Q\<close>
    unfolding F_Sync D_Sync by blast
  thus \<open>(s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q \ A)\<close>
  proof cases
    from same_div D_F show \<open>s \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A)) \<Longrightarrow> (s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q \ A)\<close> by blast
  next
    case F
    from F(1, 2) consider \<open>s_P \<in> \<D> (P \ A)\<close> | \<open>s_Q \<in> \<D> (Q \ A)\<close>
      | (F_both) s_P' s_Q'
      where \<open>s_P = ?trH_A s_P'\<close> \<open>(s_P', X_P \<union> ev ` A) \<in> \<F> P\<close>
        \<open>s_Q = ?trH_A s_Q'\<close> \<open>(s_Q', X_Q \<union> ev ` A) \<in> \<F> Q\<close>
      unfolding F_Hiding D_Hiding by blast
    thus \<open>(s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q \ A)\<close>
    proof cases
      assume \<open>s_P \<in> \<D> (P \ A)\<close>
      moreover from F(2) F_T have \<open>s_Q \<in> \<T> (Q \ A)\<close> by blast
      ultimately have \<open>s \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close>
        using F(3) front_tickFree_Nil unfolding D_Sync by blast
      with same_div D_F show \<open>(s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q \ A)\<close> by blast
    next
      from F(1) F_T have \<open>s_P \<in> \<T> (P \ A)\<close> by blast
      moreover assume \<open>s_Q \<in> \<D> (Q \ A)\<close>
      moreover have \<open>s setinterleaves ((s_Q, s_P), range tick \<union> ev ` S)\<close>
        by (simp add: F(3) setinterleaving_sym)
      ultimately have \<open>s \<in> \<D> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close>
        using front_tickFree_Nil unfolding D_Sync by blast
      with same_div D_F show \<open>(s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q \ A)\<close> by blast
    next
      case F_both
      from \<open>A \<inter> S = {}\<close> have \<open>ev ` A \<inter> (range tick \<union> ev ` S) = {}\<close> by blast
      from interleave_Hiding[OF this F(3)[unfolded F_both(1, 3)]]
      obtain s' where * : \<open>s = ?trH_A s'\<close>
        \<open>s' setinterleaves ((s_P', s_Q'), range tick \<union> ev ` S)\<close> by blast
      have \<open>X \<union> ev ` A =   (X_P \<union> ev ` A \<union> (X_Q \<union> ev ` A)) \<inter> (range tick \<union> ev ` S)
                         \<union> (X_P \<union> ev ` A) \<inter> (X_Q \<union> ev ` A)\<close>
        by (simp add: F(4) Un_Int_distrib2 Un_assoc sup_left_commute)
      thus \<open>(s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q \ A)\<close>
        by (simp add: "*"(1) F_Hiding F_Sync) (use "*"(2) F_both(2, 4) in blast)
    qed
  qed
qed





(* TODO: do we need this ? *)
(* Trivial results have been removed *)
(* 
lemmas Par_SKIP_SKIP = SKIP_Sync_SKIP[where S = \<open>UNIV\<close>]
   and Par_SKIP_STOP = SKIP_Sync_STOP[where S = \<open>UNIV\<close>]
   and Par_commute = Sync_commute[where S = \<open>UNIV\<close>]
   and Par_assoc = Sync_assoc[where S = \<open>UNIV\<close>]
   and Mprefix_Par_SKIP = Mprefix_Sync_SKIP[where S = \<open>UNIV\<close>, simplified]
   and prefix_Par_SKIP = prefix_Sync_SKIP[where S = \<open>UNIV\<close>, simplified]
   and prefix_Par1 = prefix_Sync1[where S = \<open>UNIV\<close>, simplified]
   and prefix_Par2 = prefix_Sync2[where S = \<open>UNIV\<close>, simplified]
   and Mprefix_Par_distr = Mprefix_Sync_Mprefix_subset[where S = \<open>UNIV\<close>, simplified]

   and Inter_SKIP_SKIP = SKIP_Sync_SKIP[where S = \<open>{}\<close>]
   and Inter_SKIP_STOP = SKIP_Sync_STOP[where S = \<open>{}\<close>]
   and Inter_commute = Sync_commute[where S = \<open>{}\<close>]
   and Inter_assoc = Sync_assoc[where S = \<open>{}\<close>]
   and Mprefix_Inter_SKIP = Mprefix_Sync_SKIP[where S = \<open>{}\<close>, simplified]
   and prefix_Inter_SKIP = prefix_Sync_SKIP[where S = \<open>{}\<close>, simplified]
   (* and Hiding_Inter = Hiding_Sync[where S = \<open>{}\<close>, simplified] *)
   and Mprefix_Inter_distr = Mprefix_Sync_Mprefix_indep[where S = \<open>{}\<close>, simplified]
   and prefix_Inter = Mprefix_Sync_Mprefix_indep[of \<open>{a}\<close> \<open>{}\<close> \<open>{b}\<close> \<open>\<lambda>x. P\<close> \<open>\<lambda>x. Q\<close>,
                                               simplified, folded write0_def] for a P b Q
 *)




subsection \<open>Renaming Operator Laws\<close>

lemma Renaming_Ndet: \<open>Renaming (P \<sqinter> Q) f g = Renaming P f g \<sqinter> Renaming Q f g\<close>
  by (subst Process_eq_spec) (auto simp add: F_Renaming D_Renaming F_Ndet D_Ndet)


lemma Renaming_Det:  \<open>Renaming (P \<box> Q) f g = Renaming P f g \<box> Renaming Q f g\<close>
proof (subst Process_eq_spec, safe)
  show \<open>(s, X) \<in> \<F> (Renaming (P \<box> Q) f g) \<Longrightarrow>
        (s, X) \<in> \<F> (Renaming P f g \<box> Renaming Q f g)\<close> for s X
    by (cases s) (auto simp add: F_Renaming F_Det D_Renaming D_Det T_Renaming)+
next
  fix s X assume \<open>(s, X) \<in> \<F> (Renaming P f g \<box> Renaming Q f g)\<close>
  then consider \<open>s = []\<close> \<open>(s, X) \<in> \<F> (Renaming P f g)\<close> \<open>(s, X) \<in> \<F> (Renaming Q f g)\<close>
    | e s' where \<open>s = e # s'\<close> \<open>(s, X) \<in> \<F> (Renaming P f g) \<or> (s, X) \<in> \<F> (Renaming Q f g)\<close>
    | \<open>s = []\<close> \<open>s \<in> \<D> (Renaming P f g) \<or> s \<in> \<D> (Renaming Q f g)\<close>
    | r where \<open>s = []\<close> \<open>\<checkmark>(r) \<notin> X\<close> \<open>([\<checkmark>(r)] \<in> \<T> (Renaming P f g) \<or> [\<checkmark>(r)] \<in> \<T> (Renaming Q f g))\<close>
    by (cases s) (auto simp add: F_Det)
  thus \<open>(s, X) \<in> \<F> (Renaming (P \<box> Q) f g)\<close>
  proof cases
    show \<open>\<lbrakk>s = []; (s, X) \<in> \<F> (Renaming P f g); (s, X) \<in> \<F> (Renaming Q f g)\<rbrakk>
          \<Longrightarrow> (s, X) \<in> \<F> (Renaming (P \<box> Q) f g)\<close>
      by (auto simp add: F_Renaming F_Det)
  next
    show \<open>s = e # s' \<Longrightarrow> (s, X) \<in> \<F> (Renaming P f g) \<or> (s, X) \<in> \<F> (Renaming Q f g)
          \<Longrightarrow> (s, X) \<in> \<F> (Renaming (P \<box> Q) f g)\<close> for s' e
      by (simp add: F_Renaming F_Det D_Det, safe)
        (metis list.distinct(1) list.simps(9), presburger)+
  next
    show \<open>s = [] \<Longrightarrow> s \<in> \<D> (Renaming P f g) \<or> s \<in> \<D> (Renaming Q f g)
          \<Longrightarrow> (s, X) \<in> \<F> (Renaming (P \<box> Q) f g)\<close>
      by (simp add: D_Renaming F_Renaming D_Det)
  next
    show \<open>\<lbrakk>s = []; \<checkmark>(r) \<notin> X; [\<checkmark>(r)] \<in> \<T> (Renaming P f g) \<or> [\<checkmark>(r)] \<in> \<T> (Renaming Q f g)\<rbrakk>
          \<Longrightarrow> (s, X) \<in> \<F> (Renaming (P \<box> Q) f g)\<close> for r
      by (auto simp add: T_Renaming F_Renaming D_Det F_Det
          dest: map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_tick_iff[THEN iffD1, OF sym, of r])
        (metis append_eq_Cons_conv list.map_disc_iff map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree
          non_tickFree_tick tickFree_Nil tickFree_append_iff)+
  qed
next
  show \<open>s \<in> \<D> (Renaming (P \<box> Q) f g) \<Longrightarrow> s \<in> \<D> (Renaming P f g \<box> Renaming Q f g)\<close>
    and \<open>s \<in> \<D> (Renaming P f g \<box> Renaming Q f g) \<Longrightarrow> s \<in> \<D> (Renaming (P \<box> Q) f g)\<close> for s
    by (auto simp add: D_Renaming D_Det)
qed


lemma Sliding_STOP_Det [simp] : \<open>(P \<rhd> STOP) \<box> Q = P \<rhd> Q\<close>
  by (simp add: Det_commute Det_distrib_Ndet_left Sliding_def)

lemma Sliding_Det: \<open>(P \<rhd> P') \<box> Q = P \<rhd> P' \<box> Q\<close>
  by (metis Det_assoc Sliding_STOP_Det)  


lemma Renaming_Sliding:
  \<open>Renaming (P \<rhd> Q) f g = Renaming P f g \<rhd> Renaming Q f g\<close>
  by (simp add: Renaming_Det Renaming_Ndet Sliding_def)



(* TODO: do we need the following versions ? *)
lemma Renaming_Mprefix_image:
  \<open>Renaming (\<box> a \<in> A \<rightarrow> P (f a)) f g =
   \<box> b \<in> f ` A \<rightarrow> Renaming (P b) f g\<close> (is \<open>?lhs = ?rhs\<close>)
  by (subst Renaming_Mprefix, rule mono_Mprefix_eq)
    (simp add: Process_eq_spec F_GlobalNdet D_GlobalNdet F_Renaming D_Renaming, safe, auto)

lemma Renaming_Mprefix_image_inj_on:
  \<open>Renaming (Mprefix A P) f g = \<box> b \<in> f ` A \<rightarrow> Renaming (P (THE a. a \<in> A \<and> f a = b)) f g\<close> 
  if inj_on_f: \<open>inj_on f A\<close>
  apply (subst Renaming_Mprefix_image[symmetric])
  apply (intro arg_cong[where f = \<open>\<lambda>Q. Renaming Q f g\<close>] mono_Mprefix_eq)
  by (metis that the_inv_into_def the_inv_into_f_f)

corollary Renaming_Mprefix_image_inj:
  \<open>Renaming (Mprefix A P) f g = \<box> b \<in> f ` A \<rightarrow> Renaming (P (THE a. f a = b)) f g\<close> if inj_f: \<open>inj f\<close>
  apply (subst Renaming_Mprefix_image_inj_on, metis inj_eq inj_onI that)
  apply (rule mono_Mprefix_eq[rule_format])
  by (metis imageE inj_eq[OF inj_f])


lemma Renaming_Mndetprefix_image: \<open>Renaming (\<sqinter> a \<in> A \<rightarrow> P (f a)) f g = \<sqinter> b \<in> f ` A \<rightarrow> Renaming (P b) f g\<close>
  by (auto simp add: Mndetprefix_GlobalNdet Renaming_distrib_GlobalNdet write0_def Renaming_Mprefix
      intro!: mono_Mprefix_eq mono_GlobalNdet_eq2 intro: sym)

corollary Renaming_Mndetprefix_inj_on:
  \<open>Renaming (Mndetprefix A P) f g = \<sqinter> b \<in> f ` A \<rightarrow> Renaming (P (THE a. a \<in> A \<and> f a = b)) f g\<close> 
  if inj_on_f: \<open>inj_on f A\<close>
  apply (subst Renaming_Mndetprefix_image[symmetric])
  apply (intro arg_cong[where f = \<open>\<lambda>Q. Renaming Q f g\<close>] mono_Mndetprefix_eq)
  by (metis that the_inv_into_def the_inv_into_f_f)

corollary Renaming_Mndetprefix_inj:
  \<open>Renaming (Mndetprefix A P) f g = \<sqinter> b \<in> f ` A \<rightarrow>  Renaming (P (THE a. f a = b)) f g\<close> 
  if inj_f: \<open>inj f\<close>
  apply (subst Renaming_Mndetprefix_inj_on, metis inj_eq inj_onI that)
  apply (rule mono_Mndetprefix_eq[rule_format])
  by (metis imageE inj_eq[OF inj_f])



lemma Hiding_distrib_FD_GlobalNdet :
  \<open>(\<sqinter>a \<in> A. P a) \ S \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a \<in> A. (P a \ S)\<close> (is \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>)
proof (cases \<open>A = {}\<close>)
  show \<open>A = {} \<Longrightarrow> ?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close> by simp
next
  show \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close> if \<open>A \<noteq> {}\<close>
  proof (rule failure_divergence_refine_optimizedI)
    show \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
      by (simp add: GlobalNdet_projs D_Hiding_seqRun) blast
  next
    assume subset_div : \<open>\<D> ?rhs \<subseteq> \<D> ?lhs\<close>
    fix s X assume \<open>(s, X) \<in> \<F> ?rhs\<close>
    then obtain a where \<open>a \<in> A\<close> \<open>(s, X) \<in> \<F> (P a \ S)\<close>
      by (auto simp add: F_GlobalNdet \<open>A \<noteq> {}\<close>)
    from \<open>(s, X) \<in> \<F> (P a \ S)\<close> consider \<open>s \<in> \<D> (P a \ S)\<close>
      | t where \<open>s = trace_hide t (ev ` S)\<close> \<open>(t, X \<union> ev ` S) \<in> \<F> (P a)\<close>
      unfolding D_Hiding F_Hiding by blast
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      assume \<open>s \<in> \<D> (P a \ S)\<close>
      with \<open>a \<in> A\<close> have \<open>s \<in> \<D> ?rhs\<close> by (auto simp add: D_GlobalNdet)
      with subset_div D_F show \<open>(s, X) \<in> \<F> ?lhs\<close> by blast
    next
      from \<open>a \<in> A\<close> show \<open>s = trace_hide t (ev ` S) \<Longrightarrow> (t, X \<union> ev ` S) \<in> \<F> (P a)
                         \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for t
        by (simp add: F_Hiding_seqRun F_GlobalNdet) blast
    qed
  qed
qed



lemma Renaming_Seq :
  \<open>Renaming (P \<^bold>; Q) f g = Renaming P f g \<^bold>; Renaming Q f g\<close> (is \<open>?lhs = ?rhs\<close>)
proof (rule Process_eq_optimizedI)
  fix t assume \<open>t \<in> \<D> ?lhs\<close>
  then obtain u v where \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close> \<open>u \<in> \<D> (P \<^bold>; Q)\<close>
    unfolding D_Renaming by blast
  from \<open>u \<in> \<D> (P \<^bold>; Q)\<close> consider \<open>u \<in> \<D> P\<close>
    | u1 u2 r where \<open>u = u1 @ u2\<close> \<open>u1 @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>u2 \<in> \<D> Q\<close>
    unfolding D_Seq by blast
  thus \<open>t \<in> \<D> ?rhs\<close>
  proof cases
    from \<open>ftF v\<close> \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u @ v\<close> \<open>tF u\<close>
    show \<open>u \<in> \<D> P \<Longrightarrow> t \<in> \<D> ?rhs\<close> by (auto simp add: D_Seq D_Renaming)
  next
    fix u1 u2 r assume \<open>u = u1 @ u2\<close> \<open>u1 @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>u2 \<in> \<D> Q\<close>
    from \<open>u1 @ [\<checkmark>(r)] \<in> \<T> P\<close> have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ [\<checkmark>(g r)] \<in> \<T> (Renaming P f g)\<close>
      by (auto simp add: T_Renaming)
    moreover from \<open>u2 \<in> \<D> Q\<close> \<open>tF u\<close> \<open>u = u1 @ u2\<close>
    have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u2 \<in> \<D> (Renaming Q f g)\<close>
      by (simp add: D_Renaming) (use front_tickFree_Nil in blast)
    ultimately have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u \<in> \<D> ?rhs\<close> by (auto simp add: \<open>u = u1 @ u2\<close> D_Seq)
    thus \<open>t \<in> \<D> ?rhs\<close> by (simp add: \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u @ v\<close> \<open>ftF v\<close>
          \<open>tF u\<close> is_processT7 map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
  qed
next
  fix t assume \<open>t \<in> \<D> ?rhs\<close>
  thm this[simplified D_Seq, simplified]
  then consider \<open>t \<in> \<D> (Renaming P f g)\<close>
    | t1 t2 s where \<open>t = t1 @ t2\<close> \<open>t1 @ [\<checkmark>(s)] \<in> \<T> (Renaming P f g)\<close>
      \<open>t1 @ [\<checkmark>(s)] \<notin> \<D> (Renaming P f g)\<close> \<open>t2 \<in> \<D> (Renaming Q f g)\<close>
    by (simp add: D_Seq) (metis D_imp_front_tickFree append_T_imp_tickFree
        is_processT7 is_processT9 list.distinct(1))
  thus \<open>t \<in> \<D> ?lhs\<close>
  proof cases
    show \<open>t \<in> \<D> (Renaming P f g) \<Longrightarrow> t \<in> \<D> ?lhs\<close>
      by (auto simp add: D_Renaming D_Seq)
  next
    fix t1 t2 s assume \<open>t = t1 @ t2\<close> \<open>t1 @ [\<checkmark>(s)] \<in> \<T> (Renaming P f g)\<close>
      \<open>t1 @ [\<checkmark>(s)] \<notin> \<D> (Renaming P f g)\<close> \<open>t2 \<in> \<D> (Renaming Q f g)\<close>
    from this(2, 3) obtain u1' where \<open>t1 @ [\<checkmark>(s)] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1'\<close> \<open>u1' \<in> \<T> P\<close>
      by (auto simp add: Renaming_projs)
    then obtain u1 r where \<open>s = g r\<close> \<open>t1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1\<close> \<open>u1 @ [\<checkmark>(r)] \<in> \<T> P\<close>
      by (cases u1' rule: rev_cases) (auto simp add: tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
    from \<open>t2 \<in> \<D> (Renaming Q f g)\<close> obtain u2 u3
      where \<open>t2 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u2 @ u3\<close> \<open>tF u2\<close> \<open>ftF u3\<close> \<open>u2 \<in> \<D> Q\<close>
      unfolding D_Renaming by blast
    from \<open>u1 @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>u2 \<in> \<D> Q\<close> have \<open>u1 @ u2 \<in> \<D> (P \<^bold>; Q)\<close>
      by (auto simp add: D_Seq)
    with \<open>ftF u3\<close> \<open>tF u2\<close> \<open>u1 @ [\<checkmark>(r)] \<in> \<T> P\<close> show \<open>t \<in> \<D> ?lhs\<close>
      by (simp add: \<open>t = t1 @ t2\<close> \<open>t1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1\<close>
          \<open>t2 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u2 @ u3\<close> D_Renaming)
        (metis append_T_imp_tickFree append_eq_appendI map_append not_Cons_self tickFree_append_iff)
  qed
next
  fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
  from \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close> obtain u
    where \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close> \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P \<^bold>; Q)\<close>
    unfolding Renaming_projs by blast
  from \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P \<^bold>; Q)\<close> \<open>t \<notin> \<D> ?lhs\<close>
  consider \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> range tick) \<in> \<F> P\<close> \<open>tF u\<close>
    | u1 r u2 where \<open>u = u1 @ u2\<close> \<open>u1 @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>(u2, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> Q\<close>
    by (auto simp add: \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close> Seq_projs D_Renaming)
      (metis D_imp_front_tickFree butlast_snoc front_tickFree_iff_tickFree_butlast front_tickFree_single
        is_processT8 is_processT9 map_append map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_front_tickFree nonTickFree_n_frontTickFree)
  thus \<open>(t, X) \<in> \<F> ?rhs\<close>
  proof cases
    assume \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> range tick) \<in> \<F> P\<close> \<open>tF u\<close>
    have \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` range tick \<subseteq> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> range tick\<close>
      by (auto simp add: map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_tick_iff)
    with \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> range tick) \<in> \<F> P\<close>
    have \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` range tick) \<in> \<F> P\<close>
      by (meson is_processT4)
    with \<open>tF u\<close> show \<open>(t, X) \<in> \<F> ?rhs\<close>
      by (auto simp add: F_Seq \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close> F_Renaming map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
  next
    fix u1 u2 r assume \<open>u = u1 @ u2\<close> \<open>u1 @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>(u2, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> Q\<close>
    from \<open>u1 @ [\<checkmark>(r)] \<in> \<T> P\<close> have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ [\<checkmark>(g r)] \<in> \<T> (Renaming P f g)\<close>
      by (auto simp add: T_Renaming)
    moreover from \<open>(u2, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> Q\<close>
    have \<open>(map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u2, X) \<in> \<F> (Renaming Q f g)\<close> by (auto simp add: F_Renaming)
    ultimately show \<open>(t, X) \<in> \<F> ?rhs\<close>
      by (auto simp add: \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close> \<open>u = u1 @ u2\<close> F_Seq)
  qed
next
  fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
  then consider \<open>(t, X \<union> range tick) \<in> \<F> (Renaming P f g)\<close> \<open>tF t\<close>
    | t1 t2 s where \<open>t = t1 @ t2\<close> \<open>t1 @ [\<checkmark>(s)] \<in> \<T> (Renaming P f g)\<close> \<open>(t2, X) \<in> \<F> (Renaming Q f g)\<close>
    unfolding Seq_projs by blast
  thus \<open>(t, X) \<in> \<F> ?lhs\<close>
  proof cases
    assume \<open>(t, X \<union> range tick) \<in> \<F> (Renaming P f g)\<close> \<open>tF t\<close>
    with \<open>t \<notin> \<D> ?rhs\<close> obtain u
      where \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close>
        \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` range tick) \<in> \<F> P\<close>
      by (auto simp add: D_Seq Renaming_projs)
    from this(2) have \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> range tick) \<in> \<F> P\<close>
      by (rule is_processT4) auto
    with \<open>tF t\<close> show \<open>(t, X) \<in> \<F> ?lhs\<close>
      by (auto simp add: F_Renaming F_Seq \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
  next
    fix t1 t2 s assume \<open>t = t1 @ t2\<close> \<open>t1 @ [\<checkmark>(s)] \<in> \<T> (Renaming P f g)\<close> \<open>(t2, X) \<in> \<F> (Renaming Q f g)\<close>
    from \<open>t \<notin> \<D> ?rhs\<close> have \<open>t1 @ [\<checkmark>(s)] \<notin> \<D> (Renaming P f g)\<close>
      by (simp add: \<open>t = t1 @ t2\<close> D_Seq)
        (metis D_imp_front_tickFree F_imp_front_tickFree \<open>(t2, X) \<in> \<F> (Renaming Q f g)\<close>
          front_tickFree_append_iff is_processT7 is_processT9 not_Cons_self)
    with \<open>t1 @ [\<checkmark>(s)] \<in> \<T> (Renaming P f g)\<close> obtain u1'
      where \<open>t1 @ [\<checkmark>(s)] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1'\<close> \<open>u1' \<in> \<T> P\<close>
      unfolding Renaming_projs by blast
    then obtain u1 r where \<open>s = g r\<close> \<open>t1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1\<close> \<open>u1 @ [\<checkmark>(r)] \<in> \<T> P\<close>
      by (cases u1' rule: rev_cases) (auto simp add: tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
    from \<open>t \<notin> \<D> ?rhs\<close> \<open>t1 @ [\<checkmark>(s)] \<in> \<T> (Renaming P f g)\<close> have \<open>t2 \<notin> \<D> (Renaming Q f g)\<close>
      by (auto simp add: \<open>t = t1 @ t2\<close> D_Seq)
    with \<open>(t2, X) \<in> \<F> (Renaming Q f g)\<close> obtain u2
      where \<open>t2 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u2\<close> \<open>(u2, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> Q\<close>
      unfolding Renaming_projs by blast
    from \<open>(u2, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> Q\<close> \<open>u1 @ [\<checkmark>(r)] \<in> \<T> P\<close>
    have \<open>(u1 @ u2, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P \<^bold>; Q)\<close> by (auto simp add: F_Seq)
    thus \<open>(t, X) \<in> \<F> ?lhs\<close>
      by (auto simp add: \<open>t = t1 @ t2\<close> \<open>t1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1\<close>
          \<open>t2 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u2\<close> F_Renaming)
  qed
qed



lemma Renaming_fix :
  \<open>Renaming (\<mu> X. \<phi> X) f g = (\<mu> X. ((\<lambda>P. Renaming P f g) \<circ> \<phi> \<circ> (\<lambda>P. Renaming P (inv f) (inv g))) X)\<close>
  (is \<open>Renaming (\<mu> X. \<phi> X) f g = (\<mu> X. ?\<phi>' X)\<close>) if \<open>cont \<phi>\<close>
  and \<open>bij f\<close> and \<open>bij g\<close> for \<phi> :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof -
  \<comment> \<open>Some facts first.\<close>
  have * : \<open>\<phi> = (\<lambda>P. Renaming P (inv f) (inv g)) \<circ> ?\<phi>' \<circ> (\<lambda>P. Renaming P f g)\<close>
    by (rule ext) (simp add: Renaming_inv bij_is_inj \<open>bij f\<close> \<open>bij g\<close>)

  have mono_\<phi>  : \<open>P \<sqsubseteq> Q \<Longrightarrow> \<phi> P \<sqsubseteq> \<phi> Q\<close> for P Q
    by (simp add: cont2monofunE \<open>cont \<phi>\<close>)
  have mono_\<phi>' : \<open>P \<sqsubseteq> Q \<Longrightarrow> ?\<phi>' P \<sqsubseteq> ?\<phi>' Q\<close> for P Q
    by (simp add: mono_Renaming mono_\<phi>)

  have finitary_props : \<open>finitary f\<close> \<open>finitary g\<close> \<open>finitary (inv f)\<close> \<open>finitary (inv g)\<close>
    by (simp_all add: bij_is_inj bij_is_surj surj_imp_inj_inv \<open>bij f\<close> \<open>bij g\<close>)
  have \<open>cont (\<lambda>X. Renaming (\<phi> X) f g)\<close> by (simp add: finitary_props(1, 2) \<open>cont \<phi>\<close>)
  moreover have \<open>cont (\<lambda>X. Renaming X (inv f) (inv g))\<close> by (simp add: finitary_props(3, 4))
  ultimately have \<open>cont ?\<phi>'\<close> unfolding comp_def by (rule cont_compose)

  from \<open>cont \<phi>\<close> \<open>cont ?\<phi>'\<close> cont_process_rec 
  have ** : \<open>(\<mu> X. \<phi> X) = \<phi> (\<mu> X. \<phi> X)\<close> \<open>(\<mu> X. ?\<phi>' X) = ?\<phi>' (\<mu> X. ?\<phi>' X)\<close> by blast+

  show \<open>Renaming (\<mu> X. \<phi> X) f g = (\<mu> X. ?\<phi>' X)\<close>
  proof (rule below_antisym)
    show \<open>Renaming (\<mu> X. \<phi> X) f g \<sqsubseteq> (\<mu> X. ?\<phi>' X)\<close>
    proof (induct rule: fix_ind[where F = \<open>\<Lambda> X. \<phi> X\<close>])
      show \<open>adm (\<lambda>a. Renaming a f g \<sqsubseteq> (\<mu> X. ?\<phi>' X))\<close>
        by (simp add: \<open>finitary f\<close> \<open>finitary g\<close> monofunI)
    next
      show \<open>Renaming \<bottom> f g \<sqsubseteq> (\<mu> X. ?\<phi>' X)\<close> by simp
    next
      fix X assume \<open>Renaming X f g \<sqsubseteq> (\<mu> X. ?\<phi>' X)\<close>
      hence \<open>?\<phi>' (Renaming X f g) \<sqsubseteq> ?\<phi>' (\<mu> X. ?\<phi>' X)\<close> by (fact mono_\<phi>')
      hence \<open>Renaming (?\<phi>' (Renaming X f g)) (inv f) (inv g) \<sqsubseteq>
             Renaming (?\<phi>' (\<mu> X. ?\<phi>' X)) (inv f) (inv g)\<close> by (fact mono_Renaming)
      also from "*" have \<open>Renaming (?\<phi>' (Renaming X f g)) (inv f) (inv g) = \<phi> X\<close>
        unfolding comp_def by metis
      also from "**"(2) have \<open>?\<phi>' (\<mu> X. ?\<phi>' X) = (\<mu> X. ?\<phi>' X)\<close> by argo
      finally have \<open>Renaming (\<phi> X) f g \<sqsubseteq> Renaming (Renaming (\<mu> X. ?\<phi>' X) (inv f) (inv g)) f g\<close>
        by (fact mono_Renaming)
      also have \<open>\<dots> = (\<mu> X. ?\<phi>' X)\<close> by (simp add: inv_Renaming \<open>bij f\<close> \<open>bij g\<close>)
      finally show \<open>Renaming ((\<Lambda> X. \<phi> X)\<cdot>X) f g \<sqsubseteq> (\<mu> X. ?\<phi>' X)\<close>
        by (subst beta_cfun[OF \<open>cont \<phi>\<close>]) (simp add: comp_def)
    qed
  next
    show \<open>(\<mu> X. ?\<phi>' X) \<sqsubseteq> Renaming (\<mu> X. \<phi> X) f g\<close>
    proof (induct rule: fix_ind[where F = \<open>\<Lambda> X. ?\<phi>' X\<close>])
      show \<open>adm (\<lambda>a. a \<sqsubseteq> Renaming (\<mu> x. \<phi> x) f g)\<close> by (simp add: monofunI)
    next
      show \<open>\<bottom> \<sqsubseteq> Renaming (\<mu> x. \<phi> x) f g\<close> by simp
    next
      fix X assume hyp : \<open>X \<sqsubseteq> Renaming (\<mu> X. \<phi> X) f g\<close>
      hence \<open>Renaming X (inv f) (inv g) \<sqsubseteq> Renaming (Renaming (\<mu> X. \<phi> X) f g) (inv f) (inv g)\<close>
        by (fact mono_Renaming)
      also have \<open>\<dots> = (\<mu> X. \<phi> X)\<close> by (simp add: Renaming_inv bij_is_inj \<open>bij f\<close> \<open>bij g\<close>)
      finally have \<open>\<phi> (Renaming X (inv f) (inv g)) \<sqsubseteq> \<phi> (\<mu> X. \<phi> X)\<close> by (fact mono_\<phi>)
      hence \<open>Renaming (\<phi> (Renaming X (inv f) (inv g))) f g \<sqsubseteq>
             Renaming (\<phi> (\<mu> x. \<phi> x)) f g\<close> by (fact mono_Renaming)
      also from "**"(1) have \<open>\<phi> (\<mu> x. \<phi> x) = (\<mu> X. \<phi> X)\<close> by presburger
      finally show \<open>(\<Lambda> X. ?\<phi>' X)\<cdot>X \<sqsubseteq> Renaming (\<mu> X. \<phi> X) f g\<close>
        by (subst beta_cfun[OF \<open>cont ?\<phi>'\<close>]) (simp add: comp_def)
    qed
  qed
qed



(*<*)
end
  (*>*)

