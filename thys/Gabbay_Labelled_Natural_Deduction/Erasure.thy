(*  Title:      Erasure.thy
    Author:     Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz, 2026
    Maintainer: Arthur Freitas Ramos

    Erasure soundness: every labelled derivation erases to an ordinary
    natural-deduction derivation of the underlying formula from the
    erased context.
*)

theory Erasure
  imports Labelled_Natural_Deduction
begin

text \<open>
This theory proves that labels are conservative annotations for the parametric
kernel: every labelled derivation erases to an ordinary natural deduction
derivation of the underlying formula from the erased context.
\<close>

context label_structure
begin

theorem labelled_sound_under_erasure:
  assumes "\<Gamma> \<turnstile>L x"
  shows "erase_ctx \<Gamma> \<turnstile> erase_lfm x"
  using assms
proof (induction rule: lderives.induct)
  case (LAssm x \<Gamma>)
  have "erase_lfm x \<in> set (erase_ctx \<Gamma>)"
    using LAssm.hyps by (induction \<Gamma>) (auto simp: erase_ctx_def erase_lfm_def)
  then show ?case
    by (rule derives.Assm)
next
  case (LBotE \<Gamma> l A)
  then show ?case
    by (simp add: derives.BotE)
next
  case (LImpI l A \<Gamma> m B)
  then show ?case
    by (simp add: derives.ImpI)
next
  case (LImpE \<Gamma> l A B m)
  then show ?case
    by (simp add: derives.ImpE)
next
  case (LConI \<Gamma> l A m B)
  then show ?case
    by (simp add: derives.ConI)
next
  case (LConE1 \<Gamma> l A B)
  then show ?case
    by (simp add: derives.ConE1)
next
  case (LConE2 \<Gamma> l A B)
  then show ?case
    by (simp add: derives.ConE2)
next
  case (LDisI1 \<Gamma> l A B)
  then show ?case
    by (simp add: derives.DisI1)
next
  case (LDisI2 \<Gamma> l B A)
  then show ?case
    by (simp add: derives.DisI2)
next
  case (LDisE \<Gamma> l A B m n C p q)
  then show ?case
    by (simp add: derives.DisE)
qed

lemmas erasure_sound = labelled_sound_under_erasure

end

end
