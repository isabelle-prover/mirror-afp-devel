theory Ground_Ordered_Resolution_Soundness
  imports Ground_Ordered_Resolution
begin

context ground_ordered_resolution_calculus
begin

lemma soundness_ground_resolution:
  assumes
    step: "resolution D E C"
  shows "G_entails {D, E} {C}"
  using step
proof (cases D E C rule: resolution.cases)
  case (resolutionI l\<^sub>1 l\<^sub>2 E' D' t)

  show ?thesis
    unfolding G_entails_def true_clss_singleton
    unfolding true_clss_insert
  proof (intro allI impI, elim conjE)
    fix I :: "'t set"
    assume "I \<TTurnstile> E" and "I \<TTurnstile> D"

    then obtain k\<^sub>1 k\<^sub>2 :: "'t literal" where
      "k\<^sub>1 \<in># E" and "I \<TTurnstile>l k\<^sub>1" and "k\<^sub>2 \<in># D" and "I \<TTurnstile>l k\<^sub>2"
      by (auto simp: true_cls_def)

    show "I \<TTurnstile> C"
    proof (cases "k\<^sub>1 = l\<^sub>1")
      case K1_def: True

      hence "I \<TTurnstile>l l\<^sub>1"
        using \<open>I \<TTurnstile>l k\<^sub>1\<close> 
        by simp

      show ?thesis
      proof (cases "k\<^sub>2 = l\<^sub>2")
        case K2_def: True

        hence "I \<TTurnstile>l l\<^sub>2"
          using \<open>I \<TTurnstile>l k\<^sub>2\<close> 
          by simp

        hence False
          using \<open>I \<TTurnstile>l l\<^sub>1\<close> local.resolutionI(7,8) by auto

        thus ?thesis ..
      next
        case False

        hence "k\<^sub>2 \<in># D'"
          using \<open>k\<^sub>2 \<in># D\<close>
          unfolding resolutionI
          by simp

        hence "I \<TTurnstile> D'"
          using \<open>I \<TTurnstile>l k\<^sub>2\<close> 
          by blast

        thus ?thesis
          unfolding resolutionI 
          by simp
      qed
    next
      case False

      hence "k\<^sub>1 \<in># E'"
        using \<open>k\<^sub>1 \<in># E\<close>
        unfolding resolutionI 
        by simp

      hence "I \<TTurnstile> E'"
        using \<open>I \<TTurnstile>l k\<^sub>1\<close> 
        by blast

      thus ?thesis
        unfolding resolutionI 
        by simp
    qed
  qed
qed

lemma soundness_ground_factoring:
  assumes step: "factoring D C"
  shows "G_entails {D} {C}"
  using step
proof (cases D C rule: factoring.cases)
  case (factoringI l D' t)

  show ?thesis
    unfolding G_entails_def true_clss_singleton
  proof (intro allI impI)
    fix I :: "'t set"
    assume "I \<TTurnstile> D"

    then obtain k :: "'t literal" where
      "k \<in># D" and "I \<TTurnstile>l k"
      by (auto simp: true_cls_def)

    show "I \<TTurnstile> C"
    proof (cases "k = l")
      case True

      hence "I \<TTurnstile>l l"
        using \<open>I \<TTurnstile>l k\<close> 
        by metis

      thus ?thesis
        unfolding factoringI
        by (metis true_cls_add_mset)
    next
      case False

      hence "k \<in># D'"
        using \<open>k \<in># D\<close>
        unfolding factoringI
        by auto

      hence "k \<in># C"
        unfolding factoringI
        by simp

      thus ?thesis
        using \<open>I \<TTurnstile>l k\<close> 
        by blast
    qed
  qed
qed

sublocale sound_inference_system where
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

end
