(*  Title:      Labelled_Natural_Deduction.thy
    Author:     Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz, 2026
    Maintainer: Arthur Freitas Ramos

    Parametric labelled natural-deduction kernel: a locale fixing inert
    label constructors for the logical rules, with the labelled judgement
    and its structural metatheory.
*)

theory Labelled_Natural_Deduction
  imports Natural_Deduction
begin

text \<open>
This theory introduces the parametric labelled natural-deduction kernel.  A
locale fixes inert label constructors for the logical rules, but imposes no
equations on them; concrete label disciplines are supplied later by
interpretation.
\<close>

locale label_structure =
  fixes app :: "'l \<Rightarrow> 'l \<Rightarrow> 'l"
    and lam :: "'l \<Rightarrow> 'l \<Rightarrow> 'l"
    and pair :: "'l \<Rightarrow> 'l \<Rightarrow> 'l"
    and fst_l :: "'l \<Rightarrow> 'l"
    and snd_l :: "'l \<Rightarrow> 'l"
    and abort :: "'l \<Rightarrow> 'l"
    and inl :: "'l \<Rightarrow> 'l"
    and inr :: "'l \<Rightarrow> 'l"
    and cases :: "'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l"
begin

inductive lderives :: "('l, 'a) lfm list \<Rightarrow> ('l, 'a) lfm \<Rightarrow> bool"
    ("_ \<turnstile>L _" [50, 50] 50)
where
  LAssm: "x \<in> set \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>L x"
| LBotE: "\<Gamma> \<turnstile>L (l, Bot) \<Longrightarrow> \<Gamma> \<turnstile>L (abort l, A)"
| LImpI: "(l, A) # \<Gamma> \<turnstile>L (m, B) \<Longrightarrow> \<Gamma> \<turnstile>L (lam l m, Imp A B)"
| LImpE: "\<Gamma> \<turnstile>L (l, Imp A B) \<Longrightarrow> \<Gamma> \<turnstile>L (m, A) \<Longrightarrow> \<Gamma> \<turnstile>L (app l m, B)"
| LConI: "\<Gamma> \<turnstile>L (l, A) \<Longrightarrow> \<Gamma> \<turnstile>L (m, B) \<Longrightarrow> \<Gamma> \<turnstile>L (pair l m, Con A B)"
| LConE1: "\<Gamma> \<turnstile>L (l, Con A B) \<Longrightarrow> \<Gamma> \<turnstile>L (fst_l l, A)"
| LConE2: "\<Gamma> \<turnstile>L (l, Con A B) \<Longrightarrow> \<Gamma> \<turnstile>L (snd_l l, B)"
| LDisI1: "\<Gamma> \<turnstile>L (l, A) \<Longrightarrow> \<Gamma> \<turnstile>L (inl l, Dis A B)"
| LDisI2: "\<Gamma> \<turnstile>L (l, B) \<Longrightarrow> \<Gamma> \<turnstile>L (inr l, Dis A B)"
| LDisE:
    "\<Gamma> \<turnstile>L (l, Dis A B) \<Longrightarrow>
     (m, A) # \<Gamma> \<turnstile>L (n, C) \<Longrightarrow>
     (p, B) # \<Gamma> \<turnstile>L (q, C) \<Longrightarrow>
     \<Gamma> \<turnstile>L (cases l m n p q, C)"

lemma labelled_weakening:
  assumes "\<Gamma> \<turnstile>L x" and "set \<Gamma> \<subseteq> set \<Delta>"
  shows "\<Delta> \<turnstile>L x"
  using assms
proof (induction arbitrary: \<Delta> rule: lderives.induct)
  case (LAssm x \<Gamma>)
  then have "x \<in> set \<Delta>"
    by auto
  then show ?case
    by (rule lderives.intros(1))
next
  case (LBotE \<Gamma> l A)
  then show ?case
    by (meson lderives.intros)
next
  case (LImpI l A \<Gamma> m B)
  show ?case
  proof (rule lderives.intros(3))
    show "(l, A) # \<Delta> \<turnstile>L (m, B)"
      by (rule LImpI.IH) (use LImpI.prems in auto)
  qed
next
  case (LImpE \<Gamma> l A B m)
  then show ?case
    by (meson lderives.intros)
next
  case (LConI \<Gamma> l A m B)
  then show ?case
    by (meson lderives.intros)
next
  case (LConE1 \<Gamma> l A B)
  then show ?case
    by (meson lderives.intros)
next
  case (LConE2 \<Gamma> l A B)
  then show ?case
    by (meson lderives.intros)
next
  case (LDisI1 \<Gamma> l A B)
  then show ?case
    by (meson lderives.intros)
next
  case (LDisI2 \<Gamma> l B A)
  then show ?case
    by (meson lderives.intros)
next
  case (LDisE \<Gamma> l A B m n C p q)
  show ?case
  proof (rule lderives.intros(10))
    show "\<Delta> \<turnstile>L (l, Dis A B)"
      using LDisE.IH(1) LDisE.prems by blast
    show "(m, A) # \<Delta> \<turnstile>L (n, C)"
      by (rule LDisE.IH(2)) (use LDisE.prems in auto)
    show "(p, B) # \<Delta> \<turnstile>L (q, C)"
      by (rule LDisE.IH(3)) (use LDisE.prems in auto)
  qed
qed

lemma labelled_weakening_cons:
  assumes "\<Gamma> \<turnstile>L x"
  shows "y # \<Gamma> \<turnstile>L x"
  using assms by (rule labelled_weakening) auto

lemma labelled_exchange:
  assumes "x # y # \<Gamma> \<turnstile>L z"
  shows "y # x # \<Gamma> \<turnstile>L z"
  using assms by (rule labelled_weakening) auto

lemma labelled_cut_general:
  assumes "\<Gamma> \<turnstile>L x"
    and "\<Delta> \<turnstile>L y"
    and "set \<Delta> \<subseteq> insert x (set \<Sigma>)"
    and "set \<Gamma> \<subseteq> set \<Sigma>"
  shows "\<Sigma> \<turnstile>L y"
  using assms(2,3,1,4)
proof (induction arbitrary: \<Gamma> x \<Sigma> rule: lderives.induct)
  case (LAssm y \<Delta>)
  from LAssm.hyps LAssm.prems(1) have "y = x \<or> y \<in> set \<Sigma>"
    by auto
  then show ?case
  proof
    assume "y = x"
    then show ?thesis
      using LAssm.prems(2,3) labelled_weakening by blast
  next
    assume "y \<in> set \<Sigma>"
    then show ?thesis
      by (rule lderives.intros(1))
  qed
next
  case (LBotE \<Delta> l A)
  then show ?case
    by (meson lderives.intros)
next
  case (LImpI l A \<Delta> m B)
  show ?case
  proof (rule lderives.intros(3))
    have sub: "set ((l, A) # \<Delta>) \<subseteq> insert x (set ((l, A) # \<Sigma>))"
      using LImpI.prems(1) by auto
    have sub_context: "set \<Gamma> \<subseteq> set ((l, A) # \<Sigma>)"
      using LImpI.prems(3) by auto
    show "(l, A) # \<Sigma> \<turnstile>L (m, B)"
      by (rule LImpI.IH[OF sub LImpI.prems(2) sub_context])
  qed
next
  case (LImpE \<Delta> l A B m)
  then show ?case
    by (meson lderives.intros)
next
  case (LConI \<Delta> l A m B)
  then show ?case
    by (meson lderives.intros)
next
  case (LConE1 \<Delta> l A B)
  then show ?case
    by (meson lderives.intros)
next
  case (LConE2 \<Delta> l A B)
  then show ?case
    by (meson lderives.intros)
next
  case (LDisI1 \<Delta> l A B)
  then show ?case
    by (meson lderives.intros)
next
  case (LDisI2 \<Delta> l B A)
  then show ?case
    by (meson lderives.intros)
next
  case (LDisE \<Delta> l A B m n C p q)
  show ?case
  proof (rule lderives.intros(10))
    show "\<Sigma> \<turnstile>L (l, Dis A B)"
      using LDisE.IH(1) LDisE.prems by blast
    have sub_m: "set ((m, A) # \<Delta>) \<subseteq> insert x (set ((m, A) # \<Sigma>))"
      using LDisE.prems(1) by auto
    have sub_context_m: "set \<Gamma> \<subseteq> set ((m, A) # \<Sigma>)"
      using LDisE.prems(3) by auto
    show "(m, A) # \<Sigma> \<turnstile>L (n, C)"
      by (rule LDisE.IH(2)[OF sub_m LDisE.prems(2) sub_context_m])
    have sub_p: "set ((p, B) # \<Delta>) \<subseteq> insert x (set ((p, B) # \<Sigma>))"
      using LDisE.prems(1) by auto
    have sub_context_p: "set \<Gamma> \<subseteq> set ((p, B) # \<Sigma>)"
      using LDisE.prems(3) by auto
    show "(p, B) # \<Sigma> \<turnstile>L (q, C)"
      by (rule LDisE.IH(3)[OF sub_p LDisE.prems(2) sub_context_p])
  qed
qed

lemma labelled_cut:
  assumes "\<Gamma> \<turnstile>L x" and "x # \<Delta> \<turnstile>L y"
  shows "\<Gamma> @ \<Delta> \<turnstile>L y"
proof (rule labelled_cut_general)
  show "\<Gamma> \<turnstile>L x"
    by (rule assms(1))
  show "x # \<Delta> \<turnstile>L y"
    by (rule assms(2))
  show "set (x # \<Delta>) \<subseteq> insert x (set (\<Gamma> @ \<Delta>))"
    by auto
  show "set \<Gamma> \<subseteq> set (\<Gamma> @ \<Delta>)"
    by auto
qed

lemma assumption_substitution_lift:
  assumes "x \<in> set \<Gamma>"
  shows "(fst x, fm_subst \<sigma> (snd x)) \<in> set (map (map_prod id (fm_subst \<sigma>)) \<Gamma>)"
  using assms by (induction \<Gamma>) auto

lemma labelled_substitution_atom_aux:
  assumes "\<Gamma> \<turnstile>L x"
  shows "map (map_prod id (fm_subst \<sigma>)) \<Gamma> \<turnstile>L (fst x, fm_subst \<sigma> (snd x))"
  using assms
proof (induction rule: lderives.induct)
  case (LAssm x \<Gamma>)
  then have "(fst x, fm_subst \<sigma> (snd x)) \<in>
      set (map (map_prod id (fm_subst \<sigma>)) \<Gamma>)"
    by (rule assumption_substitution_lift)
  then show ?case
    by (rule lderives.LAssm)
next
  case (LBotE \<Gamma> l A)
  then show ?case
    by (auto intro: lderives.LBotE)
next
  case (LImpI l A \<Gamma> m B)
  then have "(l, fm_subst \<sigma> A) # map (map_prod id (fm_subst \<sigma>)) \<Gamma>
      \<turnstile>L (m, fm_subst \<sigma> B)"
    by (simp add: id_def)
  then have "map (map_prod id (fm_subst \<sigma>)) \<Gamma>
      \<turnstile>L (lam l m, Imp (fm_subst \<sigma> A) (fm_subst \<sigma> B))"
    by (rule lderives.LImpI)
  then show ?case
    by (simp add: id_def)
next
  case (LImpE \<Gamma> l A B m)
  then show ?case
    by (auto intro: lderives.LImpE)
next
  case (LConI \<Gamma> l A m B)
  then show ?case
    by (auto intro: lderives.LConI)
next
  case (LConE1 \<Gamma> l A B)
  then show ?case
    by (auto intro: lderives.LConE1)
next
  case (LConE2 \<Gamma> l A B)
  then show ?case
    by (auto intro: lderives.LConE2)
next
  case (LDisI1 \<Gamma> l A B)
  then show ?case
    by (auto intro: lderives.LDisI1)
next
  case (LDisI2 \<Gamma> l B A)
  then show ?case
    by (auto intro: lderives.LDisI2)
next
  case (LDisE \<Gamma> l A B m n C p q)
  then show ?case
    by (auto intro: lderives.LDisE)
qed

lemma labelled_substitution_atom:
  assumes "\<Gamma> \<turnstile>L (l, A)"
  shows "map (map_prod id (fm_subst \<sigma>)) \<Gamma> \<turnstile>L (l, fm_subst \<sigma> A)"
  using labelled_substitution_atom_aux[OF assms] by simp

end

end
