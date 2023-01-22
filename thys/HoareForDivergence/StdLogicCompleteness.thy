section "Completeness of the standard Hoare logic"

theory StdLogicCompleteness imports StdLogic WhileLangLemmas begin

lemma Hoare_strengthen:
  "(\<And>s. P s \<Longrightarrow> P' s) \<Longrightarrow> hoare P' p Q \<Longrightarrow> hoare P p Q" using h_weaken by blast

lemma Hoare_strengthen_post:
  "(\<And>s. Q' s \<Longrightarrow> Q s) \<Longrightarrow> hoare P p Q' \<Longrightarrow> hoare P p Q" using h_weaken by blast

theorem Hoare_While:
  assumes h1: "(\<And>s. P s \<Longrightarrow> R s)"
  assumes h2: "(\<And>s. R s \<and> \<not>guard x s \<Longrightarrow> Q s)"
  assumes h3:  "\<And>s0. hoare (\<lambda>s. R s \<and> guard x s \<and> s = s0) p (\<lambda>s. R s \<and> m s < ((m s0)::nat))"
  shows "hoare P (While x p) Q"
  apply (rule_tac P'=R and Q'="\<lambda>s. R s \<and> \<not>guard x s" in h_weaken; (simp add: h1 h2)?)
  apply (rule h_while[OF h3])
  apply (clarsimp simp: wfP_def)
  using wf_measure[where f=m, simplified measure_def inv_image_def]
  by auto

lemma NRC_lemma:
  "star_n (\<lambda>s t. guard f s \<and> terminates s c t) k0 m t0 \<Longrightarrow>
    star_n (\<lambda>s t. guard f s \<and> terminates s c t) k1 m t1 \<Longrightarrow>
    \<not>guard f t0 \<and> \<not>guard f t1 \<Longrightarrow>
    t0 = t1 \<and> k0 = k1"
  apply (induct k0 arbitrary: k1 m; clarsimp)
   apply (case_tac k1; clarsimp)
    apply (erule star_n.cases)+
      apply clarsimp+
   apply (erule star_n.cases)+
     apply clarsimp+
  apply (case_tac k1; clarsimp)
   apply (erule star_n.cases)+
     apply clarsimp+
   apply (erule star_n.cases)+
     apply clarsimp+
  apply (rename_tac k1)
  apply (drule_tac x=k1 in meta_spec)
  apply (erule star_n.cases)
   apply clarsimp+
  apply (erule star_n.cases)
   apply clarsimp+
  apply (drule (1) terminates_deterministic)
  apply clarsimp
  done

lemma Hoare_terminates:
  "hoare (\<lambda>s. \<exists>t. terminates s c t \<and> Q t) c Q"
proof (induct c arbitrary: Q)
  case (Seq c1 c2)
  then show ?case
    apply (clarsimp simp: terminates_Seq)
    apply (rule_tac M="\<lambda>s. \<exists>s'. terminates s c2 s' \<and> Q s'" in h_seq)
     apply (drule_tac x="\<lambda>s. \<exists>s'. terminates s c2 s' \<and> Q s'" in meta_spec)
     apply clarsimp
     apply (rule Hoare_strengthen[rotated], simp, fastforce)
    by fastforce
next
  case (If x1 c1 c2)
  then show ?case
    apply (clarsimp simp: terminates_If)
    apply (rule h_if)
    by (rule Hoare_strengthen[rotated], fastforce+)+
next
  case (While x1 c)
  then show ?case
    apply (rule_tac m="\<lambda>s. THE n. \<exists>t. (star_n (\<lambda>s t. guard x1 s \<and> terminates s c t) n s t)
                                       \<and> \<not>guard x1 t"
           in Hoare_While)
      apply assumption
     apply (clarsimp simp: terminates_While terminates_If terminates_Skip)
    apply (rename_tac s0)
    apply (rule_tac Q'="\<lambda>s. terminates s0 c s \<and> (\<exists>a b. terminates s (While x1 c) (a, b)
                                                        \<and> guard x1 s0 \<and> Q (a, b))"
           in Hoare_strengthen_post[rotated])
     apply (drule_tac x="\<lambda>s. terminates s0 c s \<and> (\<exists>a b. terminates s (While x1 c) (a, b)
                                                         \<and> guard x1 s0 \<and> Q (a, b))"
            in meta_spec)
     apply clarsimp
     apply (rule Hoare_strengthen[rotated])
      apply assumption
     apply clarsimp
     apply (subst (asm) (3) terminates_While)
     apply (clarsimp simp: terminates_If terminates_Seq)
     apply fastforce
    apply (rule conjI)
     apply fastforce
    apply clarsimp
    apply (drule_tac p="While x1 c" and f=x1 and c=c in terminates_While_NRC)
     apply clarsimp
    apply (erule exE)
    apply (subst the_equality)
      apply (rename_tac ab bb n)
      apply (rule_tac x=ab in exI, rule_tac x=bb in exI)
      apply (fastforce dest: NRC_lemma)+
    apply clarsimp
    apply (drule step_n[rotated], simp)
    apply (subst the_equality)
      apply (fastforce dest: NRC_lemma)+
    done
qed (clarsimp simp: terminates_Skip terminates_Assign terminates_Print)+

theorem Hoare_completeness:
  "hoare_sem P c Q \<Longrightarrow> hoare P c Q"
  apply (unfold hoare_sem_def)
  using h_weaken[OF _ Hoare_terminates] by blast

(* lemmas about properties of hoare *)

lemma hoare_pre_False:
  "hoare (\<lambda>_. False) prog Q"
  apply (rule Hoare_completeness)
  apply (simp add: hoare_sem_def)
  done

end