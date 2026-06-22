(*  Title:      Natural_Deduction.thy
    Author:     Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz, 2026
    Maintainer: Arthur Freitas Ramos

    Ordinary intuitionistic propositional natural deduction over list
    contexts, with weakening, exchange, substitution, and cut admissibility.
*)

theory Natural_Deduction
  imports Labelled_Formulas
begin

text \<open>
This theory defines ordinary intuitionistic propositional natural deduction
over list contexts.  The structural metatheory is stated in terms of the set of
assumptions represented by a list, which keeps exchange and weakening explicit
while avoiding dependence on a particular context order.
\<close>

primrec fm_subst :: "('a \<Rightarrow> 'b fm) \<Rightarrow> 'a fm \<Rightarrow> 'b fm" where
  "fm_subst \<sigma> (Atom p) = \<sigma> p"
| "fm_subst \<sigma> Bot = Bot"
| "fm_subst \<sigma> (Imp A B) = Imp (fm_subst \<sigma> A) (fm_subst \<sigma> B)"
| "fm_subst \<sigma> (Con A B) = Con (fm_subst \<sigma> A) (fm_subst \<sigma> B)"
| "fm_subst \<sigma> (Dis A B) = Dis (fm_subst \<sigma> A) (fm_subst \<sigma> B)"

inductive derives :: "'a fm list \<Rightarrow> 'a fm \<Rightarrow> bool"  ("_ \<turnstile> _" [50, 50] 50)
where
  Assm: "A \<in> set \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> A"
| BotE: "\<Gamma> \<turnstile> Bot \<Longrightarrow> \<Gamma> \<turnstile> A"
| ImpI: "A # \<Gamma> \<turnstile> B \<Longrightarrow> \<Gamma> \<turnstile> Imp A B"
| ImpE: "\<Gamma> \<turnstile> Imp A B \<Longrightarrow> \<Gamma> \<turnstile> A \<Longrightarrow> \<Gamma> \<turnstile> B"
| ConI: "\<Gamma> \<turnstile> A \<Longrightarrow> \<Gamma> \<turnstile> B \<Longrightarrow> \<Gamma> \<turnstile> Con A B"
| ConE1: "\<Gamma> \<turnstile> Con A B \<Longrightarrow> \<Gamma> \<turnstile> A"
| ConE2: "\<Gamma> \<turnstile> Con A B \<Longrightarrow> \<Gamma> \<turnstile> B"
| DisI1: "\<Gamma> \<turnstile> A \<Longrightarrow> \<Gamma> \<turnstile> Dis A B"
| DisI2: "\<Gamma> \<turnstile> B \<Longrightarrow> \<Gamma> \<turnstile> Dis A B"
| DisE: "\<Gamma> \<turnstile> Dis A B \<Longrightarrow> A # \<Gamma> \<turnstile> C \<Longrightarrow> B # \<Gamma> \<turnstile> C \<Longrightarrow> \<Gamma> \<turnstile> C"

lemma weakening:
  assumes "\<Gamma> \<turnstile> A" and "set \<Gamma> \<subseteq> set \<Delta>"
  shows "\<Delta> \<turnstile> A"
  using assms
proof (induction arbitrary: \<Delta> rule: derives.induct)
  case (Assm A \<Gamma>)
  then show ?case
    by (meson derives.Assm subsetD)
next
  case (BotE \<Gamma> A)
  then show ?case
    by (meson derives.BotE)
next
  case (ImpI A \<Gamma> B)
  show ?case
  proof (rule derives.ImpI)
    show "A # \<Delta> \<turnstile> B"
      by (rule ImpI.IH) (use ImpI.prems in auto)
  qed
next
  case (ImpE \<Gamma> A B)
  then show ?case
    by (meson derives.ImpE)
next
  case (ConI \<Gamma> A B)
  then show ?case
    by (meson derives.ConI)
next
  case (ConE1 \<Gamma> A B)
  then show ?case
    by (meson derives.ConE1)
next
  case (ConE2 \<Gamma> A B)
  then show ?case
    by (meson derives.ConE2)
next
  case (DisI1 \<Gamma> A B)
  then show ?case
    by (meson derives.DisI1)
next
  case (DisI2 \<Gamma> B A)
  then show ?case
    by (meson derives.DisI2)
next
  case (DisE \<Gamma> A B C)
  show ?case
  proof (rule derives.DisE)
    show "\<Delta> \<turnstile> Dis A B"
      using DisE.IH(1) DisE.prems by blast
    show "A # \<Delta> \<turnstile> C"
      by (rule DisE.IH(2)) (use DisE.prems in auto)
    show "B # \<Delta> \<turnstile> C"
      by (rule DisE.IH(3)) (use DisE.prems in auto)
  qed
qed

lemma weakening_cons:
  assumes "\<Gamma> \<turnstile> A"
  shows "B # \<Gamma> \<turnstile> A"
  using assms by (rule weakening) auto

lemma exchange:
  assumes "A # B # \<Gamma> \<turnstile> C"
  shows "B # A # \<Gamma> \<turnstile> C"
  using assms by (rule weakening) auto

lemma cut_general:
  assumes "\<Gamma> \<turnstile> A" and "\<Delta> \<turnstile> B" and "set \<Delta> \<subseteq> insert A (set \<Gamma>)"
  shows "\<Gamma> \<turnstile> B"
  using assms(2,3,1)
proof (induction arbitrary: \<Gamma> A rule: derives.induct)
  case (Assm B \<Delta>)
  from Assm.hyps Assm.prems(1) have "B = A \<or> B \<in> set \<Gamma>"
    by auto
  then show ?case
  proof
    assume "B = A"
    then show ?thesis
      using Assm.prems(2) by simp
  next
    assume "B \<in> set \<Gamma>"
    then show ?thesis
      by (rule derives.Assm)
  qed
next
  case (BotE \<Delta> B)
  then show ?case
    by (meson derives.BotE)
next
  case (ImpI C \<Delta> D)
  show ?case
  proof (rule derives.ImpI)
    have deriv: "C # \<Gamma> \<turnstile> A"
      using ImpI.prems(2) by (rule weakening_cons)
    have sub: "set (C # \<Delta>) \<subseteq> insert A (set (C # \<Gamma>))"
      using ImpI.prems(1) by auto
    show "C # \<Gamma> \<turnstile> D"
      by (rule ImpI.IH[OF sub deriv])
  qed
next
  case (ImpE \<Delta> C D)
  then show ?case
    by (meson derives.ImpE)
next
  case (ConI \<Delta> C D)
  then show ?case
    by (meson derives.ConI)
next
  case (ConE1 \<Delta> C D)
  then show ?case
    by (meson derives.ConE1)
next
  case (ConE2 \<Delta> C D)
  then show ?case
    by (meson derives.ConE2)
next
  case (DisI1 \<Delta> C D)
  then show ?case
    by (meson derives.DisI1)
next
  case (DisI2 \<Delta> D C)
  then show ?case
    by (meson derives.DisI2)
next
  case (DisE \<Delta> C D E)
  show ?case
  proof (rule derives.DisE)
    show "\<Gamma> \<turnstile> Dis C D"
      using DisE.IH(1) DisE.prems by blast
    have deriv_C: "C # \<Gamma> \<turnstile> A"
      using DisE.prems(2) by (rule weakening_cons)
    have sub_C: "set (C # \<Delta>) \<subseteq> insert A (set (C # \<Gamma>))"
      using DisE.prems(1) by auto
    show "C # \<Gamma> \<turnstile> E"
      by (rule DisE.IH(2)[OF sub_C deriv_C])
    have deriv_D: "D # \<Gamma> \<turnstile> A"
      using DisE.prems(2) by (rule weakening_cons)
    have sub_D: "set (D # \<Delta>) \<subseteq> insert A (set (D # \<Gamma>))"
      using DisE.prems(1) by auto
    show "D # \<Gamma> \<turnstile> E"
      by (rule DisE.IH(3)[OF sub_D deriv_D])
  qed
qed

lemma cut:
  assumes "\<Gamma> \<turnstile> A" and "A # \<Gamma> \<turnstile> B"
  shows "\<Gamma> \<turnstile> B"
  using assms by (rule cut_general) auto

theorem deduction_theorem:
  "A # \<Gamma> \<turnstile> B \<longleftrightarrow> \<Gamma> \<turnstile> Imp A B"
proof
  show "A # \<Gamma> \<turnstile> B \<Longrightarrow> \<Gamma> \<turnstile> Imp A B"
    by (rule derives.ImpI)
next
  assume "\<Gamma> \<turnstile> Imp A B"
  then have "A # \<Gamma> \<turnstile> Imp A B"
    by (rule weakening_cons)
  moreover have "A # \<Gamma> \<turnstile> A"
    by (rule derives.Assm) simp
  ultimately show "A # \<Gamma> \<turnstile> B"
    by (rule derives.ImpE)
qed

lemma substitution_atom:
  assumes "\<Gamma> \<turnstile> A"
  shows "map (fm_subst \<sigma>) \<Gamma> \<turnstile> fm_subst \<sigma> A"
  using assms
  by (induction rule: derives.induct) (auto intro: derives.intros)

end
