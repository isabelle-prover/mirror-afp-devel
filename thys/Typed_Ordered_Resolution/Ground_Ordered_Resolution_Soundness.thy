theory Ground_Ordered_Resolution_Soundness
  imports Ground_Ordered_Resolution
begin

lemma (in ground_ordered_resolution_calculus) soundness_ground_resolution:
  assumes
    step: "resolution D C R"
  shows "G_entails {D, C} {R}"
  using step
proof (cases D C R rule: resolution.cases)
  case (resolutionI L\<^sub>C C' L\<^sub>D D')

  show ?thesis
    unfolding G_entails_def true_clss_singleton
    unfolding true_clss_insert
  proof (intro allI impI, elim conjE)
    fix I :: "'t set"
    assume "I \<TTurnstile> C" and "I \<TTurnstile> D"

    then obtain K1 K2 :: "'t literal" where
      "K1 \<in># C" and "I \<TTurnstile>l K1" and "K2 \<in># D" and "I \<TTurnstile>l K2"
      by (auto simp: true_cls_def)

    show "I \<TTurnstile> R"
    proof (cases "K1 = L\<^sub>C")
      case K1_def: True

      hence "I \<TTurnstile>l L\<^sub>C"
        using \<open>I \<TTurnstile>l K1\<close> 
        by simp

      show ?thesis
      proof (cases "K2 = L\<^sub>D")
        case K2_def: True

        hence "I \<TTurnstile>l L\<^sub>D"
          using \<open>I \<TTurnstile>l K2\<close> 
          by simp

        hence False
          using \<open>I \<TTurnstile>l L\<^sub>C\<close> 
          by (simp add: local.resolutionI(3,4))

        thus ?thesis ..
      next
        case False

        hence "K2 \<in># D'"
          using \<open>K2 \<in># D\<close>
          unfolding resolutionI
          by simp

        hence "I \<TTurnstile> D'"
          using \<open>I \<TTurnstile>l K2\<close> 
          by blast

        thus ?thesis
          unfolding resolutionI 
          by simp
      qed
    next
      case False

      hence "K1 \<in># C'"
        using \<open>K1 \<in># C\<close>
        unfolding resolutionI 
        by simp

      hence "I \<TTurnstile> C'"
        using \<open>I \<TTurnstile>l K1\<close> 
        by blast

      thus ?thesis
        unfolding resolutionI 
        by simp
    qed
  qed
qed

lemma (in ground_ordered_resolution_calculus) soundness_ground_factoring:
  assumes step: "factoring C D"
  shows "G_entails {C} {D}"
  using step
proof (cases C D rule: factoring.cases)
  case (factoringI L\<^sub>1 C')

  show ?thesis
    unfolding G_entails_def true_clss_singleton
  proof (intro allI impI)
    fix I :: "'t set"
    assume "I \<TTurnstile> C"

    then obtain K :: "'t literal" where
      "K \<in># C" and "I \<TTurnstile>l K"
      by (auto simp: true_cls_def)

    show "I \<TTurnstile> D"
    proof (cases "K = L\<^sub>1")
      case True

      hence "I \<TTurnstile>l L\<^sub>1"
        using \<open>I \<TTurnstile>l K\<close> 
        by metis

      thus ?thesis
        unfolding factoringI
        by (metis true_cls_add_mset)
    next
      case False

      hence "K \<in># C'"
        using \<open>K \<in># C\<close>
        unfolding factoringI
        by auto

      hence "K \<in># D"
        unfolding factoringI
        by simp

      thus ?thesis
        using \<open>I \<TTurnstile>l K\<close> 
        by blast
    qed
  qed
qed

sublocale ground_ordered_resolution_calculus \<subseteq> sound_inference_system where
  Inf = G_Inf and
  Bot = G_Bot and
  entails = G_entails
proof unfold_locales
  fix \<iota>
  assume "\<iota> \<in> G_Inf"

  then show "G_entails (set (prems_of \<iota>)) {concl_of \<iota>}"
    unfolding G_Inf_def
    using soundness_ground_resolution soundness_ground_factoring
    by auto
qed

end
