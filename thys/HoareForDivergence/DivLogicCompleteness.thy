section "Completeness of Hoare logic for diverging programs"

theory DivLogicCompleteness
  imports DivLogic StdLogicCompleteness StdLogicSoundness
begin

declare pohjola.intros[intro, simp]
declare pohjola.intros(7)[simp del]
declare pohjola.intros(7)[rule del]
declare pohjola.intros(6)[rule del]

theorem pohjola_strengthen:
  "\<lbrakk>pohjola P' p D;  \<forall>s. P s \<longrightarrow> P' s\<rbrakk> \<Longrightarrow> pohjola P p D"
  by blast

inductive div_at_iteration where
  "guard f s \<Longrightarrow> diverges s c l \<Longrightarrow> D l \<Longrightarrow> div_at_iteration 0 s f c D"
| "guard f s \<Longrightarrow> terminates s c t \<Longrightarrow> div_at_iteration n t f c D \<Longrightarrow>
     div_at_iteration (Suc n) s f c D"
print_theorems

inductive_cases
  div_at_0 [elim!]:   "div_at_iteration 0 s f c D" and
  div_at_S [elim!]: "div_at_iteration (Suc n) s f c D"
print_theorems

theorem div_at_iteration_11:
  "div_at_iteration i s f c D \<Longrightarrow>
    div_at_iteration j s f c D \<Longrightarrow> i = j"
  apply (induct arbitrary: j rule: div_at_iteration.induct)
   apply (erule div_at_iteration.cases; simp)
   apply (erule diverges.cases; clarsimp)
  apply (rotate_tac -1)
  apply (erule div_at_iteration.cases)
   apply (erule diverges.cases, blast)
  apply safe
  apply (drule (1) terminates_deterministic)
  apply clarsimp
  done

lemma star_n_While_flatten:
  "star_n (\<lambda>s t. star step (While x p, s) (While x p, t)
                         \<and> terminates s p t \<and> guard x s) i s t
       \<Longrightarrow> \<exists>n'. star_n step n' (While x p, s) (While x p, t) \<and> n' \<ge> i"
  apply (induct arbitrary: s t rule: nat_less_induct)
  apply (rename_tac n s t)
  apply (clarsimp simp: star_eq_star_n)
  apply (case_tac n; simp)
   apply clarsimp
   apply (erule star_n.cases; clarsimp)
   apply fastforce
  apply clarsimp
  apply (erule star_n.cases; clarsimp)
  apply (rename_tac ac bc n ad bd na)
  apply (drule_tac x=n in spec)
  apply clarsimp
  apply (drule_tac x=ac and y=bc in spec2)
  apply (drule_tac x=ad and y=bd in spec2)
  apply simp
  apply clarsimp
  apply (clarsimp simp: terminates star_eq_star_n)
  apply (rename_tac n' nb)
  apply (drule (1) While_body_add3step)
  apply (thin_tac "star_n _ na _ _")
  apply (frule (1) star_n_trans)
  apply (rule_tac x="nb + 3 + n'" in exI)
  apply fastforce
  done

lemma diverges_init_state:
  "\<lbrakk>terminates s c t; diverges t (While g c) l; guard g s\<rbrakk> \<Longrightarrow> diverges s (While g c) l"
  apply (simp (no_asm) add: diverges_While diverges_If)
  apply clarsimp
  apply (simp (no_asm) add: diverges_Seq)
  apply (rule disjI2)
  apply (rule_tac x="fst t" in exI, rule_tac x="snd t" in exI)
  by fastforce

lemma diverges_init_state_n:
  "\<lbrakk>star_n (\<lambda>s t. terminates s c t \<and> guard g s) n s t; diverges t (While g c) l; guard g t\<rbrakk>
    \<Longrightarrow> diverges s (While g c) l"
  apply (induct n arbitrary: s t)
   apply (erule star_n.cases, clarsimp)
   apply (clarsimp simp: terminates)
  apply (erule star_n.cases; clarsimp)
  apply (rename_tac a b a' b' n a'' b'')
  apply (drule_tac x=a' and y=b' in meta_spec2)
  apply (drule_tac x=a'' and y=b'' in meta_spec2)
  apply clarsimp
  apply (frule diverges_init_state; simp?)
  done

lemma div_at_i_unwind:
  "div_at_iteration i s g c D
    \<longleftrightarrow> (\<exists>t. star_n (\<lambda>s t. terminates s c t \<and> guard g s) i s t \<and> guard g t
                                                  \<and> (\<exists>l. diverges t c l \<and> D l))"
  apply (rule iffI)
   apply (induct i arbitrary: s)
    apply fastforce
   apply clarsimp
   apply (rename_tac a' b')
   apply (drule_tac x=a' and y=b' in meta_spec2)
   apply fastforce
  apply clarsimp
  apply (induct i arbitrary: s)
   apply (erule star_n.cases; simp)
   apply (rule div_at_iteration.intros(1); simp)
  apply (erule star_n.cases; simp)
  apply clarsimp
  apply (rename_tac l a b a' b' n a'' b'')
  apply (rule div_at_iteration.intros(2); simp?)
  apply (drule_tac x=a'' and y=b'' in meta_spec2)
  apply (drule_tac x=l in meta_spec)
  apply (drule_tac x=a' and y=b' in meta_spec2)
  apply clarsimp
  done

lemma diverging_body_diverges:
  "\<lbrakk>diverges s c l; guard g s\<rbrakk> \<Longrightarrow> diverges s (While g c) l"
  apply (simp add: diverges_While diverges_If)
  apply (simp add: diverges_Seq)
  done

lemma non_diverging_inf_loop:
  "\<lbrakk>\<forall>i. \<not> div_at_iteration i s g c D; diverges s (While g c) l; D l\<rbrakk>
    \<Longrightarrow> \<forall>i. \<exists>t. star_n (\<lambda>s t. (\<exists>k. star_n step k (While g c, s) (While g c, t))
                                                    \<and> terminates s c t \<and> guard g s) i s t"
  apply clarsimp
  apply (simp add: diverges_While diverges_If)
  apply (case_tac "guard g s"; simp)
  apply (simp add: diverges_Seq)
  apply (erule disjE)
   apply (fastforce intro!: div_at_iteration.intros)
  apply clarsimp
  apply (rule nat.induct)
   apply (cases s; blast)
  apply clarsimp
  apply (rename_tac a b n a' b')
  apply (subgoal_tac "guard g (a', b')")
   prefer 2
   apply (rule ccontr)
   apply (frule star_n_While_flatten[simplified star_eq_star_n])
   apply clarsimp
   apply (subgoal_tac "star_n step (Suc (Suc 0)) (While g c, a', b')
                 (if guard g (a', b') then Seq c (While g c) else Skip, a', b')")
    prefer 2
    apply fastforce
   apply (drule (1) star_n_trans)
   apply (drule (2) diverges_init_state)
   apply (clarsimp simp: diverges.simps terminates.simps star_eq_star_n)
  apply (insert terminates_or_diverges)
  apply (drule_tac x="(a', b')" and y=c in meta_spec2)
  apply (erule disjE)
   (* terminating case *)
   apply clarsimp
   apply (rename_tac aa ba)
   apply (rule_tac x=aa in exI)
   apply (rule_tac x=ba in exI)
   apply (rule step_n_rev, simp)
   apply clarsimp
   apply (clarsimp simp: terminates star_eq_star_n)
   apply (rename_tac nb)
   apply (drule_tac n=nb in While_body_add3step, simp, fastforce)
  (* diverging case *)
  apply clarsimp
  apply (frule (1) diverging_body_diverges)
  apply (frule star_n_conjunct2)
  apply (drule (2) diverges_init_state_n)
  apply (drule (2) diverges_init_state)
  apply (drule (1) diverges_deterministic, simp)
  apply (simp add: div_at_i_unwind)
  apply (drule star_n_conjunct2)
  by blast

lemma While_lemma:
  "\<lbrakk>\<forall>i. \<not> div_at_iteration i s g c D; diverges s (While g c) l; D l\<rbrakk>
   \<Longrightarrow> \<exists>ts. ts 0 = s \<and> (\<forall>i. guard g (ts i) \<and> terminates (ts i) c (ts (Suc i))
                            \<and> (\<exists>k. star_n step (i+k) (While g c, ts 0) (While g c, ts i)))"
  apply (rule_tac x="\<lambda>i. SOME t. star_n (\<lambda>s t. terminates s c t) i s t" in exI)
  apply (rule context_conjI)
   apply (rule some_equality; clarsimp?)
   apply (erule star_n.cases; simp)
  apply clarsimp
  apply (rename_tac i)
  apply (drule (2) non_diverging_inf_loop)
  apply (rule someI2_ex)
   apply (drule_tac x=i in spec, clarsimp)
   apply (drule star_n_conjunct2[THEN star_n_conjunct1])
   apply fastforce
  apply (frule_tac x=i in spec)
  apply (elim exE conjE)
  apply (frule star_n_conjunct2[THEN star_n_conjunct1])
  apply (rename_tac t)
  apply (drule NRC_terminates, drule_tac x=t in spec, simp)
  apply (drule_tac x="Suc i" in spec)
  apply (elim exE conjE)
  apply (rename_tac a b)
  apply (frule_tac t="(a, b)" in star_n_conjunct2[THEN star_n_conjunct1])
  apply (erule star_n_lastE, clarsimp)
  apply (rename_tac ad bd ae be k)
  apply (frule_tac t="(ad, bd)" in star_n_conjunct2[THEN star_n_conjunct1])
  apply (drule NRC_terminates, drule_tac x="(ad, bd)" in spec, clarsimp)
  apply (rename_tac b n a' b' a a'' b'' k)
  apply (rule conjI)
   apply (rule someI2_ex, fastforce)
   apply (fastforce simp: NRC_terminates)
  apply (simp add: star_eq_star_n[symmetric])
  apply (drule star_n_While_flatten, clarsimp)
  apply (rule_tac x="n' - n" in exI, clarsimp)
  done

(* output equality *)

lemma H_for_Nil_output:
  "H i (a, b) \<Longrightarrow> ignores_output H \<Longrightarrow> H i (a, [])"
  using ignores_output_def by blast

lemma output_of_simp[simp]:
  "output_of (a, b) = b" by (fastforce simp: output_of_def)

lemma star_n_step_output_extend:
  "star_n step n (c, s) (c', t) \<Longrightarrow>
         \<exists>new. snd t = snd s @ new \<and>
               (\<forall>xs.  star_n step n (c, fst s, xs)
                          (c', fst t, xs @ new)) "
  apply (induct n arbitrary: c s t c')
   apply (erule star_n.cases; fastforce)
  apply clarsimp
  apply (erule star_n.cases; simp)
  apply clarsimp
  apply (rename_tac c a b c' a' b' n c'' a'' b'')
  apply (drule_tac x=c' in meta_spec)
  apply (drule_tac x=a' and y=b' in meta_spec2)
  apply (drule_tac x=a'' and y=b'' in meta_spec2)
  apply (drule_tac x=c'' in meta_spec)
  apply clarsimp
  apply (drule step_output_extend)
  apply clarsimp
  apply (rotate_tac -1)
  apply (rename_tac newa xs)
  apply (drule_tac x=xs in spec)
  apply (drule_tac x="xs@newa" in spec)
  apply clarsimp
  done

lemma lappend_initial_output:
  "{llist_of out |out.
             \<exists>q t. star step (While x p, a, b) (q, t, out)}
   =  lappend (llist_of b) ` {llist_of out |out.
             \<exists>q t. star step (While x p, a, []) (q, t, out)}"
  apply (rule equalityI; clarsimp simp: star_eq_star_n)
   apply (drule star_n_step_output_extend)
   apply clarsimp
   apply (drule_tac x=Nil in spec)
   apply clarsimp
   apply (metis (mono_tags, lifting) lappend_llist_of_llist_of mem_Collect_eq rev_image_eqI)
  apply (drule star_n_step_output_extend)
  apply clarsimp
  apply (drule_tac x=b in spec)
  apply (rename_tac out q t n)
  apply (rule_tac x="b@out" in exI)
  using lappend_llist_of_llist_of by blast

(***)

lemma ts_accum:
  "\<forall>i. prefix (output_of (ts i)) (output_of (ts (Suc i))) \<Longrightarrow>
   concat (map (\<lambda>i. drop (length (output_of (ts i))) (output_of (ts (Suc i)))) [0..<i])
   = drop (length (output_of (ts 0))) (output_of (ts i))"
  apply (induct i)
   apply clarsimp
  apply clarsimp
  apply (rule injD[where f="\<lambda>x. output_of (ts 0) @ x"])
   apply (metis append_eq_append_conv injI)
  apply (frule min_prefix)
  apply (rotate_tac -1)
  apply (rename_tac i)
  apply (frule_tac x=i in spec)
  apply (drule prefix_drop_append)
  apply (drule_tac x="Suc i" in spec)
  apply (drule prefix_drop_append)
  apply (simp only: append_assoc[symmetric])
  apply (frule_tac x=i in spec)
  apply (drule prefix_drop_append)
  apply clarsimp
  done

theorem Pohjola_diverges:
  "pohjola (\<lambda>s. \<exists>l. diverges s c l \<and> D l) c D"
proof (induct c)
  case (Seq c1 c2)
  then show ?case
    apply (clarsimp simp: diverges_Seq)
    apply (rule_tac b="\<lambda>s. \<exists>l. diverges s c1 l \<and> D l" in p_case)
     apply (rule pohjola_strengthen[where P="\<lambda>s. P s \<and> Q s" and P'=Q for P Q]; clarsimp)
    apply (rule_tac P'="\<lambda>s. \<exists>l. (\<exists>t. terminates s c1 t \<and> diverges t c2 l) \<and> D l"
                    in pohjola_strengthen[rotated])
     apply fastforce
    apply (rule_tac M="\<lambda>s. \<exists>l. diverges s c2 l \<and> D l" in p_seq_h; clarsimp)
    by (rule_tac Q'="\<lambda>s. \<exists>l. diverges s c2 l \<and> D l" in h_weaken[OF _ Hoare_terminates]; fastforce)
next
  case (If x1 c1 c2)
  then show ?case
    apply (clarsimp simp: diverges_If)
    apply (rule p_if)
     apply (erule pohjola_strengthen, clarsimp)
    by (erule pohjola_strengthen, clarsimp)
next
  case (While x1 c)
  then show ?case
    apply (rule_tac b="\<lambda>s. \<exists>i. div_at_iteration i s x1 c D" in p_case)
     apply (rule_tac P'="\<lambda>s. \<exists>i. div_at_iteration i s x1 c D" in pohjola_strengthen[rotated])
      apply clarsimp
     apply (rule_tac R="wf_to_wfP (measure (\<lambda>s. SOME i. div_at_iteration i s x1 c D))"
                 and b="\<lambda>s.\<not> div_at_iteration 0 s x1 c D"
                  in p_while2)
        apply clarsimp
        apply (erule div_at_iteration.cases; clarsimp)
       apply (simp only: wf_to_wfP_def wfP_def)
       using wf_measure
       apply (metis (no_types, lifting) case_prodE mem_Collect_eq subsetI wf_subset)
      apply clarsimp
      apply (rule Hoare_completeness)
      apply (clarsimp simp: hoare_sem_def wf_to_wfP_def)
      apply (case_tac i; clarsimp)
      apply (rename_tac a b n a' b')
      apply (rule_tac x=a' in exI, rule_tac x=b' in exI, clarsimp)
      apply (frule (2) div_at_iteration.intros(2))
      apply (rule conjI, fastforce)
      apply (rule someI2_ex, fastforce)
      apply (drule (1) div_at_iteration_11)
      apply (rule someI2, simp)
      apply (drule (1) div_at_iteration_11, clarsimp)
     apply clarsimp
     apply (rule pohjola_strengthen, simp)
     apply fastforce
    apply (rule p_while1, clarsimp)
    apply (drule (2) While_lemma)
    apply clarsimp
    apply (rule context_conjI)
     apply (drule_tac x=0 in spec, clarsimp)
    apply (rename_tac ts)
    apply (rule_tac x="\<lambda>i s. fst s = fst (ts i)" in exI)
    apply clarsimp
    apply (rule context_conjI)
     apply (clarsimp simp: ignores_output_def)
    apply (rule_tac x="\<lambda>i. drop (length (output_of (ts i))) (output_of (ts (Suc i)))" in exI)
    apply (rule conjI; clarsimp?)
     defer
     apply (rule Hoare_completeness)
     apply (clarsimp simp: hoare_sem_def)
     apply (rename_tac i)
     apply (frule_tac x=i in spec)
     apply (drule_tac x="Suc i" in spec, clarsimp)
     apply (intro conjI; (clarsimp simp: output_of_def guard_def; fail)?)
     apply (drule terminates_history, clarsimp)
     apply (drule_tac x=Nil in spec)
     apply (clarsimp simp: split_def output_of_def)
    apply (thin_tac "pohjola _ _ _")
    apply (clarsimp simp: diverges.simps)
    apply (erule back_subst[of D])
    apply (simp only: lappend_initial_output[THEN arg_cong[where f=lSup]])
    apply (subst lSup_lappend)
      apply (rule chainI)
      apply clarsimp
      apply (meson lprefix_chain_NRC_step' lprefix_llist_of star_eq_star_n)
     apply blast
    apply (rename_tac a b ts)
    apply (rule_tac f="lappend (llist_of b)" in arg_cong)
    apply (subst lmap_inf_llist[symmetric])
    apply (simp only: flat_inf_llist_lSup)
    apply (subst ts_accum)
     apply clarsimp
     apply (rename_tac i)
     apply (drule_tac x=i in spec)
     apply safe
     apply (meson NRC_step_output_mono star_star_n terminates.cases)
    apply (rename_tac a b ts)
    apply (rule upper_subset_lSup_eq[OF lprefix_chain_RTC_step])
     apply clarsimp
     apply (rename_tac i)
     apply (drule_tac x=i in spec)
     apply clarsimp
     apply (drule_tac star_n_step_output_extend, clarsimp simp: star_eq_star_n)
     apply (drule_tac x=Nil in spec)
     apply clarsimp
     apply (metis (mono_tags, opaque_lifting) append_eq_conv_conj output_of_simp prod.exhaust_sel)
    apply (clarsimp simp: star_eq_star_n)
    apply (rename_tac n)
    apply (subgoal_tac "\<exists>i k. star_n step (i + k) (While x1 c, a, b) (While x1 c, ts i)
                              \<and> n < i + k")
     apply clarsimp
     apply (rename_tac i k)
     apply (drule_tac x=i in spec)
     apply clarsimp
     apply (drule_tac n="i + k" in star_n_step_output_extend)
     apply clarsimp
     apply (rename_tac new)
     apply (drule_tac x=Nil in spec, clarsimp)
     apply (rule_tac x="llist_of new" in exI)
     apply clarsimp
     apply (rule conjI)
      apply (metis append_eq_conv_conj output_of_def snd_def)
     apply (metis (no_types, lifting) NRC_step_output_mono output_of_simp star_n_step_decompose)
    by (meson not_less_less_Suc_eq trans_less_add1)
qed clarsimp+

theorem Pohjola_completeness:
  "pohjola_sem P c D \<Longrightarrow> pohjola P c D"
  apply (clarsimp simp: pohjola_sem_def)
  using pohjola_strengthen[OF Pohjola_diverges] by simp

end