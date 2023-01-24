section "Soundness of Hoare logic for diverging programs"

theory DivLogicSoundness imports StdLogicSoundness DivLogicCompleteness begin

lemma p_loop_deterministic:
  "star_n (\<lambda>s t. guard x s \<and> terminates s p t) n s t \<Longrightarrow>
     star_n (\<lambda>s t. guard x s \<and> terminates s p t) n s t' \<Longrightarrow> t = t'"
proof(induct rule: star_n.induct)
  case (refl_n x) thus ?case by cases simp
next
  case (step_n x y n z)
  show ?case using step_n.prems step_n.hyps
    by cases (force dest: terminates_deterministic)
qed

lemma loop_accum:
  " \<lbrakk>\<forall>i. hoare (\<lambda>s. H i s \<and> output_of s = []) p
             (\<lambda>s. H (Suc i) s \<and> output_of s = ev i \<and> guard x s);
     guard x (a, b); H 0 (a, b); ignores_output H\<rbrakk>
       \<Longrightarrow> \<forall>i. \<exists> s. star_n (\<lambda>s t. guard x s \<and> terminates s p t) i (a, b) s \<and>
                 guard x s \<and> H i s"
  apply (rule allI)
  apply (rule nat.induct)
   apply clarsimp
   apply (rule_tac x=a in exI)
   apply (rule_tac x=b in exI)
   apply clarsimp
  apply clarsimp
  apply (rename_tac n a' b')
  apply (drule_tac x=n in spec)
  apply (drule Hoare_soundness)
  apply (clarsimp simp: hoare_sem_def)
  apply (drule_tac x=a' in spec)
  apply (frule_tac i=n in H_for_Nil_output[rotated], simp)
  apply clarsimp
  apply (drule_tac s="(a', [])" in terminates_history)
  apply clarsimp
  apply (drule_tac x=b' in spec)
  apply (drule step_n_rev)
   apply fastforce
  apply (fastforce simp: guard_def ignores_output_def)
  done

lemma output_accum:
  " \<lbrakk>star_n (\<lambda>s t. guard x s \<and> terminates s p t) i (a, b) s;
     guard x (a, b); H 0 (a, b); ignores_output H;
     \<forall>i. hoare (\<lambda>s. H i s \<and> output_of s = []) p
             (\<lambda>s. H (Suc i) s \<and> output_of s = ev i \<and> guard x s)\<rbrakk>
       \<Longrightarrow> output_of s = b @ (concat (map ev [0..<i]))"
proof(induct i arbitrary: s)
  case 0 thus ?case by cases clarsimp
next
  case (Suc n) thus ?case
    apply clarsimp
    apply (erule star_n_lastE)
    apply clarsimp
    apply (rename_tac a' b' a'' b'')
    apply (frule (3) loop_accum)
    apply (rotate_tac -1)
    apply (drule_tac x=n in spec)
    apply clarsimp
    apply (drule (1) p_loop_deterministic, clarsimp)
    apply (rename_tac a')
    apply (drule_tac x=n in spec)
    apply (drule Hoare_soundness)
    apply (clarsimp simp: hoare_sem_def)
    apply (drule_tac x=a' in spec)
    apply (subgoal_tac "H n (a', [])")
     prefer 2
     apply (fastforce simp: ignores_output_def)
    apply clarsimp
    apply (drule_tac x=a' and y=b' in meta_spec2)
    apply clarsimp
    apply (drule_tac s="(a', [])" in terminates_history)
    apply clarsimp
    apply (drule_tac x="b @ concat (map ev [0..<n])" in spec)
    apply clarsimp
    apply (drule (1) terminates_deterministic, clarsimp)
    done
qed

lemma helper_lemma:
  " \<lbrakk>guard x (a, b); H 0 (a, b); ignores_output H;
        \<forall>i. hoare (\<lambda>s. H i s \<and> output_of s = []) p
             (\<lambda>s. H (Suc i) s \<and> output_of s = ev i \<and> guard x s)\<rbrakk>
       \<Longrightarrow> \<forall>i. \<exists> s. star_n (\<lambda>s t. guard x s \<and> terminates s p t) i (a, b) s \<and>
                 guard x s \<and> H i s \<and> output_of s = b @ (concat (map ev [0..< i]))"
  apply clarsimp
  apply (frule (3) loop_accum)
  apply (rotate_tac -1)
  apply (rename_tac i)
  apply (drule_tac x=i in spec)
  apply clarsimp
  apply (frule (4) output_accum)
  apply (rename_tac a' b')
  apply (rule_tac x=a' in exI)
  apply (clarsimp simp: output_of_def)
  done

lemma add_While_loops:
  " \<lbrakk>star_n (\<lambda>s t. guard x s \<and> terminates s p t) i (a, b) s\<rbrakk>
       \<Longrightarrow> star_n (\<lambda>s t. star step (While x p, s) (While x p, t) \<and> terminates s p t \<and> guard x s)
                   i (a, b) s"
proof(induct i arbitrary: a b s)
  case 0
  then show ?case by cases simp
next
  case (Suc n a b s)
  thus ?case
    by(force dest: While_body_add3real_step star_n_real_step_step
             simp: terminates star_eq_star_n
             elim: step_n_rev star_n_lastE)
qed

lemma loop_upper_bound:
  "\<lbrakk>\<forall>i. \<exists>s. star_n (\<lambda>s t. guard x s \<and> terminates s p t) i (a, b) s \<and> guard x s \<and> H i s;
    star_n step n (While x p, a, []) (q, t, out)\<rbrakk> \<Longrightarrow>
        \<exists>i t' n'. star_n (\<lambda>s t. star step (While x p, s) (While x p, t)
                                           \<and> terminates s p t \<and> guard x s) i (a, b) t' \<and>
                  star_n step n' (While x p, a, b) (While x p, t') \<and> n \<le> n'"
  apply (insert add_While_loops[of x p])
  apply (subgoal_tac "\<exists>i>n. \<exists>s. star_n
                 (\<lambda>s t. star step (While x p, s) (While x p, t) \<and>
                        terminates s p t \<and> guard x s)
                 i (a, b) s")
   prefer 2
   apply (meson lessI)
  apply safe
  apply (rename_tac i a' b')
  apply (rule_tac x=i in exI)
  apply (drule_tac x=i in spec)+
  apply (rule_tac x="(a', b')" in exI)
  apply clarsimp
  apply (drule star_n_While_flatten)
  apply fastforce
  done

theorem Pohjola_soundness:
  "pohjola P c Q \<Longrightarrow> pohjola_sem P c Q"
  unfolding pohjola_sem_def
proof (induct rule: pohjola.induct)
  case (p_seq_d P p D q)
  then show ?case
    using diverges_Seq by blast
next
  case (p_seq_h P p M q D)
  then show ?case
    apply clarsimp
    apply (frule Hoare_soundness)
    apply (clarsimp simp: hoare_sem_def)
    apply (rotate_tac -1)
    apply (rename_tac a b)
    apply (drule_tac x=a and y=b in spec2)
    by clarsimp (meson diverges_Seq)
next
  case (p_if P x p D q)
  then show ?case
    apply clarsimp
    apply (rename_tac a b)
    apply (drule_tac x=a and y=b in spec2)+
    using diverges_If by fastforce
next
  case (p_while1 P x D p)
  then show ?case
    apply clarsimp
    apply (rename_tac a b)
    apply (drule_tac x=a and y=b in meta_spec2)
    apply clarsimp
    apply (frule (3) loop_accum)
    apply (rename_tac ev)
    apply (rule_tac x="flat (LCons (output_of (a, b)) (inf_llist ev))" in exI)
    apply (simp (no_asm_simp) add: diverges.simps)
    apply (rule context_conjI)
     apply clarsimp
     apply (drule terminates_While_NRC, simp)
     apply clarsimp
     apply (rename_tac n)
     apply (drule_tac x=n in spec)+
     apply clarsimp
     apply (drule (1) p_loop_deterministic, clarsimp)
    apply (subst lappend_initial_output)
    apply (subst lSup_lappend)
      apply (rule chainI)
      apply clarsimp
      apply (meson lprefix_chain_NRC_step' lprefix_llist_of star_eq_star_n)
     apply blast
    apply (rule_tac f="lappend (llist_of b)" in arg_cong)
    apply (subst lmap_inf_llist[symmetric])
    apply (subst flat_inf_llist_lSup)
    apply (rule sym)
    apply (rule upper_subset_lSup_eq[OF lprefix_chain_RTC_step])
     apply safe
     apply (simp (no_asm_simp))
     apply (rotate_tac -2)
     apply (rename_tac i)
     apply (drule_tac x=i in spec)
     apply safe
     apply (frule (4) output_accum)
     apply clarsimp
     apply (drule add_While_loops[THEN star_n_While_flatten])
     apply clarsimp
     apply (drule star_n_step_output_extend, clarsimp)
     apply (drule_tac x=Nil in spec, clarsimp simp: star_eq_star_n)
     apply fastforce
    apply (simp only: star_eq_star_n, erule exE)
    apply (rename_tac n)
    apply (drule (1) loop_upper_bound, elim exE conjE)
    apply (frule star_n_conjunct2[THEN star_n_commute])
    apply (frule (4) output_accum)
    apply clarsimp
    apply (drule_tac n=n in star_n_step_output_extend)
    apply clarsimp
    apply (drule_tac x=b in spec)
    apply (simp add: le_eq_less_or_eq)
    apply (erule disjE)
     apply (drule (2) star_n_step_decompose)
    using NRC_step_output_mono apply fastforce
    apply simp
    apply (drule (1) NRC_step_deterministic, simp)
    apply fastforce
    done
next
  case (p_while2 P x R b p D)
  then show ?case
    apply -
    apply rotate_tac
    apply (intro allI)
    apply (erule wfP_induct)
    apply (intro impI allI)
    apply (rename_tac xa)
    apply (case_tac "b xa")
     apply (drule_tac x=xa in spec)
     apply (drule Hoare_soundness)+
     apply (clarsimp simp: hoare_sem_def)
     apply (rotate_tac -6)
     apply (rename_tac aa bb)
     apply (drule_tac x=aa and y=bb in spec2)
     apply simp
     apply (elim exE)
     apply (simp (no_asm) add: diverges_While diverges_If)
     apply (simp add: diverges_Seq)
     apply (rename_tac l)
     apply (rule_tac x=l in exI)
     apply (rule conjI; simp?)
     apply fastforce
    apply (simp (no_asm) add: diverges_While diverges_If)
    apply (simp add: diverges_Seq)
    by fastforce
qed fastforce+

end
