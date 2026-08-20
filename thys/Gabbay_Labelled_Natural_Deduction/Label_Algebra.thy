(*  Title:      Label_Algebra.thy
    Author:     Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz, 2026
    Maintainer: Arthur Freitas Ramos

    Label-algebra locale packaging the two generic adequacy obligations
    (erasure-to-unit uniformity and lift coherence), and the
    framework-adequacy meta-theorem reducing labelled derivability up to a
    label to ordinary derivability after erasure.
*)

theory Label_Algebra
  imports Erasure
begin

text \<open>
The label-algebra layer packages the two generic adequacy requirements used by
the concrete interpretations.  Label erasure targets @{typ unit}, so every
erasure map is extensionally the unique one.  The lift operation may inspect
the labelled context, which is needed for calculi whose assumption labels carry
semantic data.
\<close>

lemma erase_ctx_mem_label:
  assumes "A \<in> set (erase_ctx \<Gamma>)"
  obtains l where "(l, A) \<in> set \<Gamma>"
proof -
  from assms obtain x where "x \<in> set \<Gamma>" and "snd x = A"
    unfolding erase_ctx_def by auto
  obtain l B where "x = (l, B)"
    by (cases x)
  with \<open>x \<in> set \<Gamma>\<close> \<open>snd x = A\<close> have "(l, A) \<in> set \<Gamma>"
    by simp
  then show thesis
    by (rule that)
qed

context label_structure
begin

lemma lifting_general_aux:
  assumes "\<Delta> \<turnstile> A" and "erase_ctx \<Gamma> = \<Delta>"
  shows "\<exists>l. \<Gamma> \<turnstile>L (l, A)"
  using assms
proof (induction arbitrary: \<Gamma> rule: derives.induct)
  case (Assm A \<Delta>)
  then have "A \<in> set (erase_ctx \<Gamma>)"
    by simp
  then obtain l where "(l, A) \<in> set \<Gamma>"
    by (rule erase_ctx_mem_label)
  then have "\<Gamma> \<turnstile>L (l, A)"
    by (rule LAssm)
  then show ?case
    by blast
next
  case (BotE \<Delta> A)
  then obtain l where "\<Gamma> \<turnstile>L (l, Bot)"
    by blast
  then have "\<Gamma> \<turnstile>L (abort l, A)"
    by (rule LBotE)
  then show ?case
    by blast
next
  case (ImpI A \<Delta> B)
  have "erase_ctx ((undefined, A) # \<Gamma>) = A # \<Delta>"
    using ImpI.prems by simp
  then obtain m where "(undefined, A) # \<Gamma> \<turnstile>L (m, B)"
    using ImpI.IH by blast
  then have "\<Gamma> \<turnstile>L (lam undefined m, Imp A B)"
    by (rule LImpI)
  then show ?case
    by blast
next
  case (ImpE \<Delta> A B)
  then obtain l where imp: "\<Gamma> \<turnstile>L (l, Imp A B)"
    by blast
  from ImpE obtain m where arg: "\<Gamma> \<turnstile>L (m, A)"
    by blast
  from imp arg have "\<Gamma> \<turnstile>L (app l m, B)"
    by (rule LImpE)
  then show ?case
    by blast
next
  case (ConI \<Delta> A B)
  then obtain l where left: "\<Gamma> \<turnstile>L (l, A)"
    by blast
  from ConI obtain m where right: "\<Gamma> \<turnstile>L (m, B)"
    by blast
  from left right have "\<Gamma> \<turnstile>L (pair l m, Con A B)"
    by (rule LConI)
  then show ?case
    by blast
next
  case (ConE1 \<Delta> A B)
  then obtain l where "\<Gamma> \<turnstile>L (l, Con A B)"
    by blast
  then have "\<Gamma> \<turnstile>L (fst_l l, A)"
    by (rule LConE1)
  then show ?case
    by blast
next
  case (ConE2 \<Delta> A B)
  then obtain l where "\<Gamma> \<turnstile>L (l, Con A B)"
    by blast
  then have "\<Gamma> \<turnstile>L (snd_l l, B)"
    by (rule LConE2)
  then show ?case
    by blast
next
  case (DisI1 \<Delta> A B)
  then obtain l where "\<Gamma> \<turnstile>L (l, A)"
    by blast
  then have "\<Gamma> \<turnstile>L (inl l, Dis A B)"
    by (rule LDisI1)
  then show ?case
    by blast
next
  case (DisI2 \<Delta> B A)
  then obtain l where "\<Gamma> \<turnstile>L (l, B)"
    by blast
  then have "\<Gamma> \<turnstile>L (inr l, Dis A B)"
    by (rule LDisI2)
  then show ?case
    by blast
next
  case (DisE \<Delta> A B C)
  then obtain l where disj: "\<Gamma> \<turnstile>L (l, Dis A B)"
    by blast
  have left_ctx: "erase_ctx ((undefined, A) # \<Gamma>) = A # \<Delta>"
    using DisE.prems by simp
  then obtain n where left: "(undefined, A) # \<Gamma> \<turnstile>L (n, C)"
    using DisE.IH(2) by blast
  have right_ctx: "erase_ctx ((undefined, B) # \<Gamma>) = B # \<Delta>"
    using DisE.prems by simp
  then obtain q where right: "(undefined, B) # \<Gamma> \<turnstile>L (q, C)"
    using DisE.IH(3) by blast
  from disj left right have "\<Gamma> \<turnstile>L (cases l undefined n undefined q, C)"
    by (rule LDisE)
  then show ?case
    by blast
qed

theorem lifting_general:
  assumes "erase_ctx \<Gamma> \<turnstile> A"
  shows "\<exists>l. \<Gamma> \<turnstile>L (l, A)"
  using lifting_general_aux[OF assms refl] .

end

locale label_algebra =
  fixes app :: "'l \<Rightarrow> 'l \<Rightarrow> 'l"
    and lam :: "'l \<Rightarrow> 'l \<Rightarrow> 'l"
    and pair :: "'l \<Rightarrow> 'l \<Rightarrow> 'l"
    and fst_l :: "'l \<Rightarrow> 'l"
    and snd_l :: "'l \<Rightarrow> 'l"
    and abort :: "'l \<Rightarrow> 'l"
    and inl :: "'l \<Rightarrow> 'l"
    and inr :: "'l \<Rightarrow> 'l"
    and cases :: "'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l"
    and lderives :: "('l, 'f) lfm list \<Rightarrow> ('l, 'f) lfm \<Rightarrow> bool"
      ("_ \<turnstile>L _" [50, 50] 50)
    and erase_label :: "'l \<Rightarrow> unit"
    and lift_label :: "('l, 'f) lfm list \<Rightarrow> 'f fm \<Rightarrow> 'l"
  assumes erase_label_unique [simp]: "erase_label l = ()"
    and erasure_sound_law:
      "\<Gamma> \<turnstile>L x \<Longrightarrow> erase_ctx \<Gamma> \<turnstile> erase_lfm x"
    and lift_coherence:
      "erase_ctx \<Gamma> \<turnstile> A \<Longrightarrow> \<Gamma> \<turnstile>L (lift_label \<Gamma> A, A)"
begin

definition erase_judgement ::
    "(('l, 'f) lfm list \<times> ('l, 'f) lfm) \<Rightarrow> ('f fm list \<times> 'f fm)"
  where "erase_judgement J = (erase_ctx (fst J), erase_lfm (snd J))"

lemma erase_judgement_simps [simp]:
  "erase_judgement (\<Gamma>, (l, A)) = (erase_ctx \<Gamma>, A)"
  by (simp add: erase_judgement_def)

lemma erasure_uniformity:
  "erase_label (app l m) = ()"
  "erase_label (lam l m) = ()"
  "erase_label (pair l m) = ()"
  "erase_label (fst_l l) = ()"
  "erase_label (snd_l l) = ()"
  "erase_label (abort l) = ()"
  "erase_label (inl l) = ()"
  "erase_label (inr l) = ()"
  "erase_label (cases l m n p q) = ()"
  by simp_all

lemma erasure_uniformity_judgement:
  "erase_judgement (\<Gamma>, (app l m, A)) = (erase_ctx \<Gamma>, A)"
  "erase_judgement (\<Gamma>, (lam l m, Imp A B)) = (erase_ctx \<Gamma>, Imp A B)"
  "erase_judgement (\<Gamma>, (pair l m, Con A B)) = (erase_ctx \<Gamma>, Con A B)"
  "erase_judgement (\<Gamma>, (fst_l l, A)) = (erase_ctx \<Gamma>, A)"
  "erase_judgement (\<Gamma>, (snd_l l, B)) = (erase_ctx \<Gamma>, B)"
  "erase_judgement (\<Gamma>, (abort l, A)) = (erase_ctx \<Gamma>, A)"
  "erase_judgement (\<Gamma>, (inl l, Dis A B)) = (erase_ctx \<Gamma>, Dis A B)"
  "erase_judgement (\<Gamma>, (inr l, Dis A B)) = (erase_ctx \<Gamma>, Dis A B)"
  "erase_judgement (\<Gamma>, (cases l m n p q, C)) = (erase_ctx \<Gamma>, C)"
  by simp_all

theorem framework_adequacy:
  fixes \<Gamma>L :: "('l, 'f) lfm list"
    and A :: "'f fm"
  shows "(\<exists>l. \<Gamma>L \<turnstile>L (l, A)) \<longleftrightarrow>
    (erase_ctx \<Gamma>L \<turnstile> A \<and> \<Gamma>L \<turnstile>L (lift_label \<Gamma>L A, A))"
proof
  assume "\<exists>l. \<Gamma>L \<turnstile>L (l, A)"
  then obtain l where deriv: "\<Gamma>L \<turnstile>L (l, A)"
    by blast
  have "erase_ctx \<Gamma>L \<turnstile> erase_lfm (l, A)"
    using deriv by (rule erasure_sound_law)
  then have ordinary: "erase_ctx \<Gamma>L \<turnstile> A"
    by simp
  moreover have "\<Gamma>L \<turnstile>L (lift_label \<Gamma>L A, A)"
    using ordinary by (rule lift_coherence)
  ultimately show "erase_ctx \<Gamma>L \<turnstile> A \<and> \<Gamma>L \<turnstile>L (lift_label \<Gamma>L A, A)"
    by blast
next
  assume "erase_ctx \<Gamma>L \<turnstile> A \<and> \<Gamma>L \<turnstile>L (lift_label \<Gamma>L A, A)"
  then show "\<exists>l. \<Gamma>L \<turnstile>L (l, A)"
    by blast
qed

corollary framework_adequacy_iff:
  fixes \<Gamma>L :: "('l, 'f) lfm list"
    and A :: "'f fm"
  shows "(\<exists>l. \<Gamma>L \<turnstile>L (l, A)) \<longleftrightarrow> erase_ctx \<Gamma>L \<turnstile> A"
proof
  assume "\<exists>l. \<Gamma>L \<turnstile>L (l, A)"
  then show "erase_ctx \<Gamma>L \<turnstile> A"
    using framework_adequacy by blast
next
  assume ordinary: "erase_ctx \<Gamma>L \<turnstile> A"
  then have "\<Gamma>L \<turnstile>L (lift_label \<Gamma>L A, A)"
    by (rule lift_coherence)
  with ordinary show "\<exists>l. \<Gamma>L \<turnstile>L (l, A)"
    using framework_adequacy by blast
qed

end

end
