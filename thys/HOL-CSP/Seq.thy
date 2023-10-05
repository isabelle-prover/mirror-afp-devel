(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP - A Shallow Embedding of CSP in  Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Burkhart Wolff, Safouan Taha.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : A Combined CSP Theory
 *
 * Copyright (c) 2009 Université Paris-Sud, France
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

section\<open>The Sequence Operator\<close>

theory  Seq
  imports Process 
begin 

subsection\<open>Definition\<close>
abbreviation "div_seq P Q   \<equiv> {t1 @ t2 |t1 t2. t1 \<in> \<D> P \<and> tickFree t1 \<and> front_tickFree t2}
                            \<union> {t1 @ t2 |t1 t2. t1 @ [tick] \<in> \<T> P \<and> t2 \<in> \<D> Q}"

lift_definition  Seq :: "['a process,'a process] \<Rightarrow> 'a process"  (infixl  "\<^bold>;" 74)  
is       "\<lambda>P Q. ({(t, X). (t, X \<union> {tick}) \<in> \<F> P \<and> tickFree t} \<union>
                 {(t, X). \<exists>t1 t2. t = t1 @ t2 \<and> t1 @ [tick] \<in> \<T> P \<and> (t2, X) \<in> \<F> Q} \<union>
                 {(t, X). t \<in> div_seq P Q},
                 div_seq P Q)"
proof -
  show "is_process ({(t, X). (t, X \<union> {tick}) \<in> \<F> (P :: 'a process) \<and> tickFree t} \<union>
                    {(t, X). \<exists>t1 t2. t = t1 @ t2 \<and> t1 @ [tick] \<in> \<T> P \<and> (t2, X) \<in> \<F> Q} \<union>
                    {(t, X). t \<in> div_seq P Q},
                    div_seq P Q)"
   (is "is_process(?f, ?d)") for P Q
    unfolding is_process_def FAILURES_def DIVERGENCES_def
  proof (simp only: fst_conv snd_conv, intro conjI)
    show "([], {}) \<in> ?f" 
      apply(cases "[tick] \<in> \<T> P", simp_all add: is_processT1)
      using F_T is_processT5_S6 by blast        
  next
    show " \<forall>s X. (s, X) \<in> ?f \<longrightarrow> front_tickFree s"
      by (auto simp:is_processT2 append_T_imp_tickFree front_tickFree_append D_imp_front_tickFree)   
  next
    show "\<forall>s t. (s @ t, {}) \<in> ?f \<longrightarrow> (s, {}) \<in> ?f"       
      apply auto
            apply (metis F_T append_Nil2 is_processT is_processT3_SR is_processT5_S3)
           apply(simp add:append_eq_append_conv2) 
           apply (metis T_F_spec append_Nil2 is_processT is_processT5_S4)
          apply (metis append_self_conv front_tickFree_append front_tickFree_mono is_processT2_TR 
                no_Trace_implies_no_Failure non_tickFree_implies_nonMt non_tickFree_tick)
         apply (metis (mono_tags, lifting) F_T append_Nil2 is_processT5_S3 process_charn)
        apply (metis front_tickFree_append front_tickFree_mono self_append_conv)
       apply(simp add:append_eq_append_conv2)
       apply (metis T_F_spec append_Nil2 is_processT is_processT5_S4)
      by (metis D_imp_front_tickFree append_T_imp_tickFree front_tickFree_append 
                 front_tickFree_mono not_Cons_self2 self_append_conv)
  next
    show "\<forall>s X Y. (s, Y) \<in> ?f \<and> X \<subseteq> Y \<longrightarrow> (s, X) \<in> ?f" 
      apply auto
         apply (metis insert_mono is_processT4_S1 prod.sel(1) prod.sel(2))
        apply (metis is_processT4)
       apply (simp add: append_T_imp_tickFree)
      by (metis process_charn)
  next
    { fix sa X Y
      have "(sa, X \<union> {tick}) \<in> \<F> P \<Longrightarrow>
              tickFree sa \<Longrightarrow>
              \<forall>c. c \<in> Y \<and> c \<noteq> tick \<longrightarrow> (sa @ [c], {}) \<notin> \<F> P \<Longrightarrow> 
              (sa, X \<union> Y \<union> {tick}) \<in> \<F> P \<and> tickFree sa"
      apply(rule_tac t="X \<union> Y \<union> {tick}" and s="X \<union> {tick} \<union> (Y-{tick})" in subst,auto)
      by   (metis DiffE Un_insert_left is_processT5 singletonI)
    } note is_processT5_SEQH3 = this
    have is_processT5_SEQH4 : 
         "\<And> sa X Y. (sa, X \<union> {tick}) \<in> \<F> P 
                     \<Longrightarrow> tickFree sa 
                     \<Longrightarrow> \<forall>c. c \<in> Y \<longrightarrow> (sa@[c],{tick}) \<notin> \<F> P \<or> \<not> tickFree(sa@[c]) 
                     \<Longrightarrow> \<forall>c. c \<in> Y \<longrightarrow> (\<forall>t1 t2. sa@[c]\<noteq>t1@t2 \<or> t1@[tick]\<notin>\<T> P \<or> (t2,{})\<notin>\<F> Q) 
                     \<Longrightarrow> (sa, X \<union> Y \<union> {tick}) \<in> \<F> P \<and> tickFree sa"
      by (metis append_Nil2 is_processT1 is_processT5_S3 is_processT5_SEQH3 
                           no_Trace_implies_no_Failure tickFree_Cons tickFree_append)
    let ?f1 = "{(t, X). (t, X \<union> {tick}) \<in> \<F> P \<and> tickFree t} \<union> 
               {(t, X). \<exists>t1 t2. t = t1 @ t2 \<and> t1 @ [tick] \<in> \<T> P \<and> (t2, X) \<in> \<F> Q}"
    have is_processT5_SEQ2: "\<And> sa X Y. (sa, X) \<in> ?f1 
                                        \<Longrightarrow> (\<forall>c. c \<in> Y \<longrightarrow> (sa@[c], {})\<notin>?f) 
                                        \<Longrightarrow> (sa, X\<union>Y) \<in> ?f1"
      apply (clarsimp,rule is_processT5_SEQH4[simplified])
      by (auto simp: is_processT5)
    show "\<forall>s X Y. (s, X) \<in> ?f \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> ?f) \<longrightarrow> (s, X \<union> Y) \<in> ?f"
      apply(intro allI impI, elim conjE UnE)
        apply(rule rev_subsetD)
         apply(rule is_processT5_SEQ2)
          apply auto
        using is_processT5_S1 apply force
       apply (simp add: append_T_imp_tickFree)
      using is_processT5[rule_format, OF conjI] by force
  next  
    show "\<forall>s X. (s @ [tick], {}) \<in> ?f \<longrightarrow> (s, X - {tick}) \<in> ?f" 
      apply auto
          apply (metis (no_types, lifting) append_T_imp_tickFree butlast_append 
                       butlast_snoc is_processT2 is_processT6 nonTickFree_n_frontTickFree 
                       non_tickFree_tick tickFree_append)
         apply (metis append_T_imp_tickFree front_tickFree_append front_tickFree_mono 
                      is_processT2 non_tickFree_implies_nonMt non_tickFree_tick)
        apply (metis process_charn)
       apply (metis front_tickFree_append front_tickFree_implies_tickFree)
      apply (metis D_T T_nonTickFree_imp_decomp append_T_imp_tickFree append_assoc 
                   append_same_eq non_tickFree_implies_nonMt non_tickFree_tick process_charn 
                   tickFree_append)
      by    (metis D_imp_front_tickFree append_T_imp_tickFree front_tickFree_append 
                      front_tickFree_mono non_tickFree_implies_nonMt non_tickFree_tick)
  next
    show "\<forall>s t. s \<in> ?d \<and> tickFree s \<and> front_tickFree t \<longrightarrow> s @ t \<in> ?d"
      apply auto 
       using front_tickFree_append apply blast     
      by (metis process_charn)
  next  
    show "\<forall>s X. s \<in> ?d \<longrightarrow>  (s, X) \<in> ?f"
      by blast
  next  
    show "\<forall>s. s @ [tick] \<in> ?d \<longrightarrow> s \<in> ?d"
      apply auto      
       apply (metis append_Nil2 front_tickFree_implies_tickFree process_charn)
      by (metis append1_eq_conv append_assoc front_tickFree_implies_tickFree is_processT2_TR 
                  nonTickFree_n_frontTickFree non_tickFree_tick process_charn tickFree_append)
  qed
qed


subsection\<open>The Projections\<close>

lemma F_Seq: \<open>\<F> (P \<^bold>; Q) = {(t, X). (t, X \<union> {tick}) \<in> \<F> P \<and> tickFree t} \<union> 
                          {(t1 @ t2, X) |t1 t2 X. t1 @ [tick] \<in> \<T> P \<and> (t2, X) \<in> \<F> Q} \<union>
                          {(t1, X) |t1 X. t1 \<in> \<D> P}\<close>
  apply (subst Failures.rep_eq, auto simp add: Seq.rep_eq FAILURES_def)
  using is_processT7 is_processT apply (blast+)[5]
  by (meson is_processT)
     (metis front_tickFree_implies_tickFree front_tickFree_single
            is_processT nonTickFree_n_frontTickFree)

 
lemma D_Seq: \<open>\<D> (P \<^bold>; Q) = \<D> P \<union> {t1 @ t2 |t1 t2. t1 @ [tick] \<in> \<T> P \<and> t2 \<in> \<D> Q}\<close>
  apply (subst Divergences.rep_eq, auto simp add: Seq.rep_eq DIVERGENCES_def)
  by (simp add: is_processT7_S)
     (metis elem_min_elems front_tickFree_mono is_processT min_elems_charn 
            nonTickFree_n_frontTickFree non_tickFree_tick tickFree_Nil tickFree_append)


lemma T_Seq: \<open>\<T> (P \<^bold>; Q) = {t. \<exists>X. (t, X \<union> {tick}) \<in> \<F> P \<and> tickFree t} \<union> 
                          {t1 @ t2 |t1 t2. t1 @ [tick] \<in> \<T> P \<and> t2 \<in> \<T> Q} \<union>
                          \<D> P\<close>
  by (auto simp add: Traces.rep_eq TRACES_def Failures.rep_eq[symmetric] F_Seq)
   

subsection\<open> Continuity Rule \<close>

lemma mono_Seq_D11:  
"P \<sqsubseteq> Q \<Longrightarrow> \<D> (Q \<^bold>; S) \<subseteq> \<D> (P \<^bold>; S)"
  apply(auto simp: D_Seq)
   using le_approx1 apply blast
  using le_approx_lemma_T by blast

lemma mono_Seq_D12: 
assumes ordered: "P \<sqsubseteq> Q"
shows   "(\<forall> s. s \<notin> \<D> (P \<^bold>; S) \<longrightarrow> Ra (P \<^bold>; S) s = Ra (Q \<^bold>; S) s)"
proof -
  have mono_SEQI2a:"P \<sqsubseteq> Q \<Longrightarrow> \<forall>s. s \<notin> \<D> (P \<^bold>; S) \<longrightarrow> Ra (Q \<^bold>; S) s \<subseteq> Ra (P \<^bold>; S) s"
    apply(simp add: Ra_def D_Seq F_Seq)
    apply(insert le_approx_lemma_F[of P Q] le_approx_lemma_T[of P Q], auto) 
    using le_approx1 by blast+
  have mono_SEQI2b:"P \<sqsubseteq> Q \<Longrightarrow> \<forall>s. s \<notin> \<D> (P \<^bold>; S) \<longrightarrow> Ra (P \<^bold>; S) s \<subseteq> Ra (Q \<^bold>; S) s"
    apply(simp add: Ra_def D_Seq F_Seq)
    apply(insert le_approx_lemma_F[of P Q] le_approx_lemma_T[of P Q] 
          le_approx1[of P Q] le_approx2T[of P Q], auto) 
      using le_approx2 apply fastforce
     apply (metis front_tickFree_implies_tickFree is_processT2_TR process_charn)
    apply (simp add: append_T_imp_tickFree) 
    by (metis front_tickFree_implies_tickFree is_processT2_TR process_charn)
  show ?thesis 
    using ordered mono_SEQI2a mono_SEQI2b by(blast)
qed

lemma minSeqInclu: 
  "min_elems(\<D> (P \<^bold>; S)) 
   \<subseteq> min_elems(\<D> P) \<union> {t1@t2|t1 t2. t1@[tick]\<in>\<T> P\<and>t1\<notin>\<D> P\<and>t2\<in>min_elems(\<D> S)}"
  apply(auto simp: D_Seq min_elems_def)
  by (metis append_single_T_imp_tickFree less_append process_charn)
    

lemma mono_Seq_D13 : 
assumes ordered: "P \<sqsubseteq> Q"
shows        "min_elems (\<D> (P \<^bold>; S)) \<subseteq> \<T> (Q \<^bold>; S)"
  apply (insert ordered, frule le_approx3, rule subset_trans [OF minSeqInclu])
  apply (auto simp: F_Seq T_Seq min_elems_def append_T_imp_tickFree)
     apply(rule_tac x="{}" in exI, rule is_processT5_S3)
      apply (metis (no_types, lifting) T_F elem_min_elems le_approx3 less_list_def min_elems5 subset_eq)
     using Nil_elem_T no_Trace_implies_no_Failure apply fastforce
       apply (metis (no_types, lifting) less_self nonTickFree_n_frontTickFree process_charn)  
     apply (metis (no_types, opaque_lifting) D_T le_approx2T process_charn)
  by (metis (no_types, lifting) less_self nonTickFree_n_frontTickFree process_charn)  

lemma mono_Seq[simp] : "P \<sqsubseteq> Q \<Longrightarrow> (P \<^bold>; S) \<sqsubseteq> (Q \<^bold>; S)"
by (auto simp: le_approx_def mono_Seq_D11 mono_Seq_D12 mono_Seq_D13)

lemma mono_Seq_D21:  
"P \<sqsubseteq> Q \<Longrightarrow> \<D> (S \<^bold>; Q) \<subseteq> \<D> (S \<^bold>; P)"
  apply(auto simp: D_Seq)
  using le_approx1 by blast

lemma mono_Seq_D22: 
assumes ordered: "P \<sqsubseteq> Q"
shows   "(\<forall> s. s \<notin> \<D> (S \<^bold>; P) \<longrightarrow> Ra (S \<^bold>; P) s = Ra (S \<^bold>; Q) s)"
proof -
  have mono_SEQI2a:"P \<sqsubseteq> Q \<Longrightarrow> \<forall>s. s \<notin> \<D> (S \<^bold>; P) \<longrightarrow> Ra (S \<^bold>; Q) s \<subseteq> Ra (S \<^bold>; P) s"
    apply(simp add: Ra_def D_Seq F_Seq)
    by(use le_approx_lemma_F[of P Q] le_approx_lemma_T[of P Q] in auto) 
  have mono_SEQI2b:"P \<sqsubseteq> Q \<Longrightarrow> \<forall>s. s \<notin> \<D> (S \<^bold>; P) \<longrightarrow> Ra (S \<^bold>; P) s \<subseteq> Ra (S \<^bold>; Q) s"
    apply(simp add: Ra_def D_Seq F_Seq)
    apply(insert le_approx_lemma_F[of P Q] le_approx_lemma_T[of P Q] 
            le_approx1[of P Q] le_approx2T[of P Q], auto) 
    using le_approx2 by fastforce+
  show ?thesis 
    using ordered mono_SEQI2a mono_SEQI2b by(blast)
qed

lemma mono_Seq_D23 : 
assumes ordered: "P \<sqsubseteq> Q"
shows       "min_elems (\<D> (S \<^bold>; P)) \<subseteq> \<T> (S \<^bold>; Q)"
  apply (insert ordered, frule le_approx3, auto simp: D_Seq T_Seq min_elems_def)
     apply (metis (no_types, lifting) D_imp_front_tickFree Nil_elem_T append.assoc below_refl 
            front_tickFree_charn less_self min_elems2 no_Trace_implies_no_Failure)
   apply (simp add: append_T_imp_tickFree)
  by (metis (no_types, lifting) append.assoc is_processT less_self nonTickFree_n_frontTickFree)

lemma mono_Seq_sym[simp] : "P \<sqsubseteq> Q \<Longrightarrow> (S \<^bold>; P) \<sqsubseteq> (S \<^bold>; Q)"
by (auto simp: le_approx_def mono_Seq_D21 mono_Seq_D22 mono_Seq_D23)

lemma chain_Seq1: "chain Y \<Longrightarrow> chain (\<lambda>i. Y i \<^bold>; S)"
  by(simp add: chain_def) 

lemma chain_Seq2: "chain Y \<Longrightarrow> chain (\<lambda>i. S \<^bold>; Y i)"
  by(simp add: chain_def)  

lemma limproc_Seq_D1: "chain Y \<Longrightarrow> \<D> (lim_proc (range Y) \<^bold>; S) = \<D> (lim_proc (range (\<lambda>i. Y i \<^bold>; S)))"
  apply(auto simp:Process_eq_spec D_Seq F_Seq F_LUB D_LUB T_LUB chain_Seq1)
  by (metis ND_F_dir2' append_single_T_imp_tickFree is_processT is_ub_thelub)
  

lemma limproc_Seq_F1: "chain Y \<Longrightarrow> \<F> (lim_proc (range Y) \<^bold>; S) = \<F> (lim_proc (range (\<lambda>i. Y i \<^bold>; S)))"
  apply(auto simp add:Process_eq_spec D_Seq F_Seq F_LUB D_LUB T_LUB chain_Seq1)
  proof (auto, goal_cases)
    case (1 a b x y)
    then show ?case
      apply (erule_tac x=x in allE, elim disjE exE, auto simp add: is_processT7 is_processT8_S) 
      apply (erule_tac x=t1 in allE, erule_tac x=t2 in allE) 
      by (metis ND_F_dir2' append_single_T_imp_tickFree is_processT is_ub_thelub)
  next
    case (2 a b x)
    assume A1:"a \<notin> \<D> (Y x)"
      and  A3:"\<forall>t1 t2. a = t1 @ t2 \<longrightarrow> (\<exists>x. t1 @ [tick] \<notin> \<T> (Y x)) \<or> (t2, b) \<notin> \<F> S"
      and  B: "\<forall>x. (a, insert tick b) \<in> \<F> (Y x) \<and> tickFree a \<or> 
                   (\<exists>t1 t2. a = t1 @ t2 \<and> t1 @ [tick] \<in> \<T> (Y x) \<and> (t2, b) \<in> \<F> S) \<or>
                   a \<in> \<D> (Y x)"
      and  C:"chain Y" 
    have E:"\<not> tickFree a \<Longrightarrow> False"
      proof -
        assume F:"\<not> tickFree a"
        from A obtain f 
          where D:"f = (\<lambda>t2. {n. \<exists>t1. a = t1 @ t2 \<and> t1 @ [tick] \<in> \<T> (Y n) \<and> (t2, b) \<in> \<F> S}
                           \<union> {n. \<exists>t1. a = t1 @ t2 \<and> t1 \<in> \<D> (Y n) \<and> tickFree t1 \<and> front_tickFree t2})"
          by simp
        with B F have "\<forall>n. n \<in> (\<Union>x\<in>{t. \<exists>t1. a = t1 @ t}. f x)"  
                      (is "\<forall>n. n \<in> ?S f") using NF_ND
          by (smt (verit, best) A1 A3 C ND_F_dir2' append_single_T_imp_tickFree is_processT is_ub_thelub) 
        hence "infinite (?S f)" by (simp add: Sup_set_def)
        then obtain t2 where E:"t2\<in>{t. \<exists>t1. a = t1 @ t} \<and> infinite (f t2)" using suffixes_fin by blast
        { assume E1:"infinite{n. \<exists>t1. a = t1 @ t2 \<and> t1 @ [tick] \<in> \<T> (Y n) \<and> (t2, b) \<in> \<F> S}" 
                     (is "infinite ?E1")
          with E obtain t1 where F:"a = t1 @ t2 \<and> (t2, b) \<in> \<F> S" using D not_finite_existsD by blast
          with A3 obtain m where G:"t1@ [tick] \<notin> \<T> (Y m)" by blast
          with E1 obtain n where "n \<ge> m \<and> n \<in> ?E1" by (meson finite_nat_set_iff_bounded_le nat_le_linear)
          with D have "n \<ge> m \<and> t1@ [tick] \<in> \<T> (Y n)" by (simp add: F)
          with G C have False using le_approx_lemma_T chain_mono by blast
        } note E1 = this
        { assume E2:"infinite{n. \<exists>t1. a = t1 @ t2 \<and> t1 \<in> \<D> (Y n) \<and> tickFree t1 \<and> front_tickFree t2}" 
                    (is "infinite ?E2")
          with E obtain t1 where F:"a = t1 @ t2 \<and> tickFree t1 \<and> front_tickFree t2" 
            using D not_finite_existsD by blast
          with A1 obtain m where G:"t1 \<notin> \<D> (Y m)" using is_processT7_S by blast
          with E2 obtain n where "n \<ge> m \<and> n \<in> ?E2" by (meson finite_nat_set_iff_bounded_le nat_le_linear)
          with D have "n \<ge> m \<and> t1 \<in> \<D> (Y n)" by (simp add: F)
          with G C have False using le_approx1 chain_mono by blast
        } note E2 = this      
        from D E E1 E2 show False by blast
      qed
    from E show "tickFree a" by blast
  qed

lemma cont_left_D_Seq : "chain Y \<Longrightarrow> ((\<Squnion> i. Y i) \<^bold>; S) = (\<Squnion> i. (Y i \<^bold>; S))"
  by (simp add: Process_eq_spec chain_Seq1 limproc_Seq_D1 limproc_Seq_F1 limproc_is_thelub)

lemma limproc_Seq_D2: "chain Y \<Longrightarrow> \<D> (S \<^bold>; lim_proc (range Y)) = \<D> (lim_proc (range (\<lambda>i. S \<^bold>; Y i )))"
  apply(auto simp add:Process_eq_spec D_Seq F_Seq F_LUB D_LUB T_LUB chain_Seq2)
proof -
  fix x
  assume B: "\<forall>n. \<exists>t1 t2. x = t1 @ t2 \<and> t1 @ [tick] \<in> \<T> S \<and> t2 \<in> \<D> (Y n)"
  and C: "chain Y"
  from A obtain f where D:"f = (\<lambda>t2. {n. \<exists>t1. x = t1 @ t2 \<and> t1 @ [tick] \<in> \<T> S \<and> t2 \<in> \<D> (Y n)})"
    by simp
  with B have "\<forall>n. n \<in> (\<Union>x\<in>{t. \<exists>t1. x = t1 @ t}. f x)" (is "\<forall>n. n \<in> ?S f") by fastforce
  hence "infinite (?S f)" by (simp add: Sup_set_def)
  then obtain t2 where E:"t2\<in>{t. \<exists>t1. x = t1 @ t} \<and> infinite (f t2)" using suffixes_fin by blast
  then obtain t1 where F:"x = t1 @ t2 \<and> t1 @ [tick] \<in> \<T> S" using D not_finite_existsD by blast
  thus "\<exists>t1 t2. x = t1 @ t2 \<and> t1 @ [tick] \<in> \<T> S \<and> (\<forall>x. t2 \<in> \<D> (Y x))" 
    apply (rule_tac x = t1 in exI, rule_tac x = t2 in exI)
  proof (rule ccontr, simp)
    assume \<open>\<exists>m. t2 \<notin> \<D> (Y m)\<close>
    then obtain m where G: \<open>t2 \<notin> \<D> (Y m)\<close> ..
    with E obtain n where "n \<ge> m \<and> n \<in> (f t2)" by (meson finite_nat_set_iff_bounded_le nat_le_linear)
    with D have "n \<ge> m \<and> t2 \<in> \<D> (Y n)" by blast 
    with G C show False using le_approx1 po_class.chain_mono by blast
  qed
qed

      

lemma limproc_Seq_F2: 
  "chain Y \<Longrightarrow> \<F> (S \<^bold>; lim_proc (range Y)) = \<F> (lim_proc (range (\<lambda>i. S \<^bold>; Y i )))"
  apply(auto simp:Process_eq_spec D_Seq F_Seq T_Seq F_LUB D_LUB D_LUB_2 T_LUB T_LUB_2 chain_Seq2 del:conjI)
     apply(auto)[3]
proof (goal_cases)
  fix s X
  assume A:"\<forall>t1. t1 @ [tick] \<in> \<T> S \<longrightarrow> (\<forall>t2. s = t1 @ t2 \<longrightarrow> (\<exists>m. (t2, X) \<notin> \<F> (Y m)))"
  and B: "\<forall>n. \<exists>t1 t2. s = t1 @ t2 \<and> t1 @ [tick] \<in> \<T> S \<and> (t2, X) \<in> \<F> (Y n)"
  and C: "chain Y"
  from B have D:"\<forall>n. (\<exists>t1 t2. s = t1 @ t2 \<and> t1 @ [tick] \<in> \<T> S \<and> (t2, X) \<in> \<F> (Y n))" by (meson NF_ND)
  from A obtain f where D:"f = (\<lambda>t2. {n. \<exists>t1. s = t1 @ t2 \<and> t1 @ [tick] \<in> \<T> S \<and> (t2, X) \<in> \<F> (Y n)})"
    by simp
  with D have "\<forall>n. n \<in> (\<Union>x\<in>{t. \<exists>t1. s = t1 @ t}. f x)" using B NF_ND by fastforce
  hence "infinite (\<Union>x\<in>{t. \<exists>t1. s = t1 @ t}. f x)" by (simp add: Sup_set_def)
  then obtain t2 where E:"t2\<in>{t. \<exists>t1. s = t1 @ t} \<and> infinite (f t2)" using suffixes_fin by blast
  then obtain t1 where F:"s = t1 @ t2 \<and> t1 @ [tick] \<in> \<T> S" using D not_finite_existsD by blast
  from A F obtain m where G:"(t2, X) \<notin> \<F> (Y m)" by blast
  with E obtain n where "n \<ge> m \<and> n \<in> (f t2)" by (meson finite_nat_set_iff_bounded_le nat_le_linear)
  with D have "n \<ge> m \<and> (t2, X) \<in> \<F> (Y n)" by blast
  with G C have False using is_processT8 po_class.chain_mono proc_ord2a by blast
  thus \<open>(s, insert tick X) \<in> \<F> S \<and> tickFree s\<close> by simp
qed

lemma cont_right_D_Seq : "chain Y \<Longrightarrow> (S \<^bold>; (\<Squnion> i. Y i)) = (\<Squnion> i. (S \<^bold>; Y i))"
  by (simp add: Process_eq_spec chain_Seq2 limproc_Seq_D2 limproc_Seq_F2 limproc_is_thelub)

lemma Seq_cont[simp]:
assumes f:"cont f"
and     g:"cont g"
shows     "cont (\<lambda>x. f x \<^bold>; g x)"
proof -
  have A : "\<And>x. cont g \<Longrightarrow> cont (\<lambda>y. y \<^bold>; g x)"
    apply (rule contI2, rule monofunI)
     apply (auto)
    by (simp add: cont_left_D_Seq)
  have B : "\<And>y. cont g \<Longrightarrow> cont (\<lambda>x. y \<^bold>; g x)"
    apply (rule_tac c="(\<lambda> x. y \<^bold>; x)" in cont_compose)
     apply (rule contI2,rule monofunI)
    by (auto simp add: chain_Seq2 cont_right_D_Seq)
  show ?thesis using f g 
    apply(rule_tac f="(\<lambda>x. (\<lambda> f. f \<^bold>; g x))" in cont_apply)
      by(auto intro:contI2 monofunI simp:A B)
qed

end

