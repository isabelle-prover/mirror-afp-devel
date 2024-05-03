(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ModifiesProofs
imports CLanguage
begin

(* Rules for breaking down modifies goals before feeding them to the VCG.
   Helps avoid some pathological performance issues. *)

definition
  modifies_inv_refl :: "('a \<Rightarrow> 'a set) \<Rightarrow> bool"
where
  "modifies_inv_refl P \<equiv> \<forall>x. x \<in> P x"

definition
  modifies_inv_incl :: "('a \<Rightarrow> 'a set) \<Rightarrow> bool"
where
  "modifies_inv_incl P \<equiv> \<forall>x y. y \<in> P x \<longrightarrow> P y \<subseteq> P x"

definition
  modifies_inv_prop :: "('a \<Rightarrow> 'a set) \<Rightarrow> bool"
where
  "modifies_inv_prop P \<equiv> modifies_inv_refl P \<and> modifies_inv_incl P"

lemma modifies_inv_prop:
  "modifies_inv_refl P \<Longrightarrow> modifies_inv_incl P \<Longrightarrow> modifies_inv_prop P"
  by (simp add: modifies_inv_prop_def)

named_theorems modifies_inv_intros

locale modifies_assertion =
  fixes P :: "'s \<Rightarrow> 's set"
  assumes p: "modifies_inv_prop P"
begin

lemmas modifies_inv_prop' =
  p[unfolded modifies_inv_prop_def modifies_inv_refl_def modifies_inv_incl_def]

lemma modifies_inv_prop_lift:
  assumes c: "\<And>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (P \<sigma>) c (P \<sigma>),(P \<sigma>)"
  using modifies_inv_prop' by (fastforce intro: c hoarep.Conseq)

lemma modifies_inv_prop_lower:
  assumes c: "\<And>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (P \<sigma>) c (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c (P \<sigma>),(P \<sigma>)"
  using modifies_inv_prop' by (fastforce intro: c hoarep.Conseq)

text \<open>Note that the C-Parser associates sequential composition to the right. So the first statement
is typically already an 'atomic' statement (or at least no further sequential composition) 
that can be solved. We place it as the second precondition because the modifies-tactic follows the 
canonical order of tactical reasoning and solves the subgoals from the back. 
So \<^term>\<open>c1\<close> is already solved before further decomposing \<^term>\<open>c2\<close>. This keeps
the number of subgoals (and thus the overall goal-state) small.
\<close>
lemma modifies_inv_Seq [modifies_inv_intros]:
  assumes c: "\<And>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c2 (P \<sigma>),(P \<sigma>)" "\<And>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c1 (P \<sigma>),(P \<sigma>)" 
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c1 ;; c2 (P \<sigma>),(P \<sigma>)"
  by (intro modifies_inv_prop_lower HoarePartial.SeqSwap[OF c[THEN modifies_inv_prop_lift]])

lemma modifies_inv_Cond [modifies_inv_intros]:
  assumes c: "\<And>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c1 (P \<sigma>),(P \<sigma>)" "\<And>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c2 (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} Cond b c1 c2 (P \<sigma>),(P \<sigma>)"
  by (auto intro: HoarePartial.Cond c)

lemma modifies_inv_Guard_strip [modifies_inv_intros]:
  assumes c: "\<And>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} c (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} Guard f b c (P \<sigma>),(P \<sigma>)"
  by (rule HoarePartial.GuardStrip[OF subset_refl c UNIV_I])

lemma modifies_inv_Skip [modifies_inv_intros]:
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} SKIP (P \<sigma>),(P \<sigma>)"
  using modifies_inv_prop' by (auto intro: modifies_inv_prop_lift HoarePartial.Skip)

lemma modifies_inv_Skip' [modifies_inv_intros]:
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} SKIP (P \<sigma>)"
  using modifies_inv_prop' by (auto intro: modifies_inv_prop_lift HoarePartial.Skip)

lemma modifies_inv_whileAnno [modifies_inv_intros]:
  assumes c: "\<And>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} whileAnno b I V c (P \<sigma>),(P \<sigma>)"
  apply (rule HoarePartial.reannotateWhileNoGuard[where I="P \<sigma>"])
  by (intro HoarePartial.While hoarep.Conseq;
      fastforce simp: modifies_inv_prop' intro: modifies_inv_prop_lift c)

lemma modifies_inv_While [modifies_inv_intros]:
  assumes c: "\<And>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} While b c (P \<sigma>),(P \<sigma>)"
  by (intro modifies_inv_whileAnno[unfolded whileAnno_def] c)

lemma modifies_inv_Throw [modifies_inv_intros]:
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} THROW (P \<sigma>),(P \<sigma>)"
  using modifies_inv_prop' by (auto intro: modifies_inv_prop_lift HoarePartial.Throw)

lemma modifies_inv_Catch [modifies_inv_intros]:
  assumes c: "\<And>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c1 (P \<sigma>),(P \<sigma>)"
             "\<And>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c2 (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} TRY c1 CATCH c2 END (P \<sigma>),(P \<sigma>)"
  by (intro modifies_inv_prop_lower HoarePartial.Catch[OF c[THEN modifies_inv_prop_lift]])

lemma modifies_inv_Catch_all [modifies_inv_intros]:
  assumes 1: "\<And>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c1 (P \<sigma>),(P \<sigma>)"
  assumes 2: "\<And>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c2 (P \<sigma>)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} TRY c1 CATCH c2 END (P \<sigma>)"
  apply (intro HoarePartial.Catch[OF 1] hoarep.Conseq, clarsimp)
  apply (metis modifies_inv_prop' 2 singletonI)
  done

lemma modifies_inv_switch_Nil [modifies_inv_intros]:
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} switch v [] (P \<sigma>),(P \<sigma>)"
  by (auto intro: modifies_inv_Skip)

lemma modifies_inv_switch_Cons [modifies_inv_intros]:
  assumes c: "\<And>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c (P \<sigma>),(P \<sigma>)"
             "\<And>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} switch p vcs (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} switch p ((v,c) # vcs) (P \<sigma>),(P \<sigma>)"
  by (auto intro: c modifies_inv_Cond)

end

locale modifies_state_assertion = modifies_assertion P for
  P :: "('g, 'l, 'e, 'x) state_scheme \<Rightarrow> ('g, 'l, 'e, 'x) state_scheme set" +
  assumes p: "modifies_inv_prop P"
begin

lemma modifies_inv_creturn [modifies_inv_intros]:
  assumes c: "\<And>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} Basic (\<lambda>s. xfu (\<lambda>_. v s) s) (P \<sigma>),(P \<sigma>)"
             "\<And>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} Basic (rtu (\<lambda>_. Return)) (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} creturn rtu xfu v (P \<sigma>),(P \<sigma>)"
  unfolding creturn_def by (intro p c modifies_inv_intros)

lemma modifies_inv_creturn_void [modifies_inv_intros]:
  assumes c: "\<And>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} Basic (rtu (\<lambda>_. Return)) (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} creturn_void rtu (P \<sigma>),(P \<sigma>)"
  unfolding creturn_void_def by (intro p c modifies_inv_intros)

lemma modifies_inv_cbreak [modifies_inv_intros]:
  assumes c: "\<And>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} Basic (rtu (\<lambda>_. Break)) (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} cbreak rtu (P \<sigma>),(P \<sigma>)"
  unfolding cbreak_def by (intro p c modifies_inv_intros)

lemma modifies_inv_ccatchbrk [modifies_inv_intros]:
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} ccatchbrk rt (P \<sigma>),(P \<sigma>)"
  unfolding ccatchbrk_def by (intro p modifies_inv_intros)

lemma modifies_inv_cgoto [modifies_inv_intros]:
  assumes c: "\<And>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} Basic (rtu (\<lambda>_. Goto l)) (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} cgoto l rtu (P \<sigma>),(P \<sigma>)"
  unfolding cgoto_def by (intro p c modifies_inv_intros)

lemma modifies_inv_ccatchgoto [modifies_inv_intros]:
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} ccatchgoto l rt (P \<sigma>),(P \<sigma>)"
  unfolding ccatchgoto_def by (intro p modifies_inv_intros)

lemma modifies_inv_ccatchreturn [modifies_inv_intros]:
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} ccatchreturn rt (P \<sigma>),(P \<sigma>)"
  unfolding ccatchreturn_def by (intro p modifies_inv_intros)

end

lemma On_Exit_wp:
  assumes cleanup: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> R cleanup Q, A"
  assumes cleanup_catch: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> B cleanup A, A"
  assumes c: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c R, B"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P On_Exit c cleanup Q, A"
  unfolding On_Exit_def
  apply (rule HoarePartial.SeqSwap [where R=R])
   apply (rule HoarePartial.conseq_no_aux)
    apply (rule cleanup)
  apply simp
  apply (rule HoarePartial.Catch)
   apply (rule c)
  apply (rule HoarePartial.SeqSwap )
   apply (rule HoarePartial.Throw)
   apply (rule subset_refl)
  apply (rule cleanup_catch)
  done


lemma DynCom_fix_pre: "\<forall>s \<in> P. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {s} (c s) Q,A
      \<Longrightarrow>
      \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (DynCom c) Q,A"
  by (smt (verit, best) HoarePartial.conseq_exploit_pre Int_insert_left_if1 hoarep.DynCom inf_bot_left singletonD)

lemma "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>{s. (\<forall>t. (s, t) \<in> r \<longrightarrow> t \<in> Q) \<and> (\<exists>t. (s, t) \<in> r)} Spec r Q,A"
  by (rule hoarep.Spec)

lemma hoarep_Spec_fixed: "(\<exists>t. (s, t) \<in> r) \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub>{s} Spec r {t. (s, t) \<in> r},A"
  by (simp add: HoarePartial.Spec)

context stack_heap_state
begin

lemma With_Fresh_Stack_Ptr_tight:
  assumes c: "\<And>s p d vs bs. s \<in> P \<Longrightarrow> vs \<in> init s \<Longrightarrow> length vs = n \<Longrightarrow> length bs = n * size_of TYPE('a) \<Longrightarrow> 
    (p, d) \<in> stack_allocs n \<S> TYPE('a::mem_type) (htd s) \<Longrightarrow>   
           \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub>{hmem_upd (fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (vs!i) (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs))) [0..<n]) (htd_upd (\<lambda>_. d) s)} 
             (c p) 
           {t.  \<forall>bs. length bs = n * size_of TYPE('a) \<longrightarrow> hmem_upd (heap_update_list (ptr_val p) bs) (htd_upd (stack_releases n p) t) \<in> Q}, 
           {t.  \<forall>bs. length bs = n * size_of TYPE('a) \<longrightarrow> hmem_upd (heap_update_list (ptr_val p) bs) (htd_upd (stack_releases n p) t) \<in> A}"
  assumes no_overflow: "StackOverflow \<in> F"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P With_Fresh_Stack_Ptr n init c Q, A"
  unfolding With_Fresh_Stack_Ptr_def
  apply (rule hoarep.Guarantee [OF no_overflow])
   apply (rule DynCom_fix_pre)
  apply (rule ballI)
  apply clarsimp
  apply (rule HoarePartial.Seq)
   apply (rule  hoarep_Spec_fixed)
   apply clarsimp
  subgoal using Ex_list_of_length 
    by (metis equals0I old.prod.exhaust)

  apply clarsimp
  apply (rule DynCom_fix_pre)
  apply (rule ballI)
  apply clarsimp
  apply (rule On_Exit_wp)



    apply (rule HoarePartial.Spec)
    apply (rule subset_refl)
   apply (rule HoarePartial.Spec)
   apply (rule subset_refl)
  subgoal premises prems for s vs p d' vsa bs
  proof -
    have eq1: "length vs = n" using prems by simp
    have eq2:"(allocated_ptrs n \<S> TYPE('a) (htd s) d') = p" using prems by (simp add: stack_allocs_allocated_ptrs)
    show ?thesis
      apply (simp add: eq1 eq2 Ex_list_of_length)
      apply (rule HoarePartialDef.conseqPost [OF c [where s1=s and vs1=vsa and d1=d' and p1=p]])
      using prems
         apply auto
      done
  qed
  done


lemma With_Fresh_Stack_Ptr_tight_wp:
  assumes conseq: "\<And>s p d vs bs. s \<in> P \<Longrightarrow> vs \<in> init s \<Longrightarrow> length vs = n \<Longrightarrow>  length bs = n * size_of TYPE('a) \<Longrightarrow>  
             (p, d) \<in> stack_allocs n \<S> TYPE('a::mem_type) (htd s) \<Longrightarrow> 
           (hmem_upd (fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (vs!i) (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs))) [0..<n]) (htd_upd (\<lambda>_. d) s)) \<in> R s p d vs"
  assumes c: "\<And>s p d vs bs. s \<in> P \<Longrightarrow> vs \<in> init s \<Longrightarrow> length vs = n \<Longrightarrow>  length bs = n * size_of TYPE('a) \<Longrightarrow> 
            (p, d) \<in> stack_allocs n \<S> TYPE('a::mem_type) (htd s) \<Longrightarrow> 
           (hmem_upd (fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (vs!i) (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs))) [0..<n]) (htd_upd (\<lambda>_. d) s)) \<in> R s p d vs \<Longrightarrow> 
           \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub>(R s p d vs) (c p) 
             {t. \<forall>bs. length bs = n * size_of TYPE('a) \<longrightarrow> hmem_upd (heap_update_list (ptr_val p) bs) (htd_upd (stack_releases n p) t) \<in> Q}, 
             {t. \<forall>bs. length bs = n * size_of TYPE('a) \<longrightarrow> hmem_upd (heap_update_list (ptr_val p) bs) (htd_upd (stack_releases n p) t) \<in> A}"
  assumes no_overflow: "StackOverflow \<in> F"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P With_Fresh_Stack_Ptr n init c Q, A"
  apply (rule With_Fresh_Stack_Ptr_tight [OF _ no_overflow])
  subgoal for s p d vs bs
    apply (rule HoarePartial.conseq)
     apply (rule allI)
     apply (rule c[where s1=s and vs1=vs and d1=d])
          apply assumption
         apply assumption
        apply assumption
       apply assumption
      apply assumption
     apply (rule conseq)
         apply assumption
        apply assumption
       apply assumption
      apply assumption
     apply clarsimp
    subgoal premises prems 
    proof -
      from prems have eq: "length vs = n" by simp
      show ?thesis
        apply (simp add: eq)
        apply (rule conseq)
        using prems by auto
    qed
    done
  done



text \<open>Caution: this WP-setup was developed to solve the modified clauses. It might not be the
 best fit for WP-style reasoning in general. Also note that it is currently not
 invoked by the automatic modifies-proofs triggerd by the C-parser as \<^const>\<open>With_Fresh_Stack_Ptr\<close> is
 first decomposed by the @{thm modifies_inv_intros} (see the rule below).\<close>
declaration \<open>fn phi =>
let
  val rule = Morphism.thm phi @{thm With_Fresh_Stack_Ptr_tight}
  fun tac cont_tac ctxt mode i = 
       resolve_tac ctxt [rule] i THEN 
       SOLVED_verbose "no_overflow" ctxt (simp_tac ctxt) (i + 1) THEN 
       cont_tac true i 
in 
    Hoare.add_hoare_tacs [("With_Fresh_Stack_Ptr_tac", tac)]
end
\<close>

end

locale modifies_assertion_stack_heap_state =
  modifies_assertion P + stack_heap_state htd htd_upd hmem hmem_upd \<S>
  for P::"'s \<Rightarrow> 's set" and
    htd:: "'s \<Rightarrow> heap_typ_desc" and
    htd_upd:: "(heap_typ_desc \<Rightarrow> heap_typ_desc) \<Rightarrow> 's \<Rightarrow> 's" and
    hmem:: "'s \<Rightarrow> heap_mem" and
    hmem_upd:: "(heap_mem \<Rightarrow> heap_mem) \<Rightarrow> 's \<Rightarrow> 's"   and  
    \<S>::"addr set" +
  assumes hmem_upd_inv: "\<And>\<sigma> m. hmem_upd m \<sigma> \<in> (P \<sigma>)"
  assumes htd_upd_inv: "\<And>\<sigma> d. htd_upd d \<sigma> \<in> (P \<sigma>)"
begin

lemma modifies_With_Fresh_Stack_Ptr [modifies_inv_intros]:
  assumes no_overflow: "StackOverflow \<in> F"
  assumes c: "\<And>\<sigma> p. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} (c (p::'a::mem_type ptr)) (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} With_Fresh_Stack_Ptr n init c (P \<sigma>), (P \<sigma>)"
  apply (rule With_Fresh_Stack_Ptr_tight_wp [where R = "\<lambda> s p d v. P s"])
  subgoal for s p d vs bs
  proof -
    have "(htd_upd (\<lambda>_. d) s) \<in> P s" by (rule htd_upd_inv)
    moreover have "hmem_upd (fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (vs!i) (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs))) [0..<n]) (htd_upd (\<lambda>_. d) s) \<in> P (htd_upd (\<lambda>_. d) s)"
      by (rule hmem_upd_inv)
    ultimately
    show "hmem_upd (fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (vs!i) (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs))) [0..<n]) (htd_upd (\<lambda>_. d) s) \<in> P s"
      using modifies_inv_prop' p by blast
  qed
  subgoal for s p d v
    apply (rule HoarePartial.conseq [where P'=P and Q'=P and A'=P])
   apply (rule allI)
    subgoal for Z
      apply (rule modifies_inv_prop_lift)
      apply (rule c)
      done
    using modifies_inv_prop' hmem_upd_inv htd_upd_inv 
    by (smt (verit, best) mem_Collect_eq singletonD subset_eq)
  apply (rule no_overflow)
  done

end



locale modifies_assertion_stack_heap_raw_state =
  modifies_assertion P + stack_heap_raw_state t_hrs t_hrs_update \<S>
  for P::"'s \<Rightarrow> 's set" and
    t_hrs:: "'s \<Rightarrow> heap_raw_state" and
    t_hrs_update:: "(heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> 's \<Rightarrow> 's" and
    \<S>::"addr set" +
  assumes hrs_upd_inv: "\<And>\<sigma> m. t_hrs_update m \<sigma> \<in> (P \<sigma>)"
begin

sublocale modifies_assertion_stack_heap_state 
  P
  "\<lambda>s. hrs_htd (t_hrs s)" "\<lambda>upd. t_hrs_update (hrs_htd_update upd)" 
  "\<lambda>s. hrs_mem (t_hrs s)" "\<lambda>upd. t_hrs_update (hrs_mem_update upd)" 
  "\<S>"
  using hrs_upd_inv by unfold_locales auto

end

end
