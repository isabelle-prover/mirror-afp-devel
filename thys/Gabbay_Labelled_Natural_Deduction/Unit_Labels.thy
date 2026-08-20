(*  Title:      Unit_Labels.thy
    Author:     Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz, 2026
    Maintainer: Arthur Freitas Ramos

    Singleton-label instance of the framework: labelled derivability
    coincides with ordinary natural deduction, witnessing conservativity.
*)

theory Unit_Labels
  imports Label_Algebra
begin

text \<open>
This theory instantiates the labelled kernel with a singleton label type.  Since
all label constructors return the unique label, labelled derivability over the
lifted context is equivalent to ordinary natural deduction.
\<close>

datatype unit_label = Star

interpretation unit_labels: label_structure
  where app = "\<lambda>_ _. Star"
    and lam = "\<lambda>_ _. Star"
    and pair = "\<lambda>_ _. Star"
    and fst_l = "\<lambda>_. Star"
    and snd_l = "\<lambda>_. Star"
    and abort = "\<lambda>_. Star"
    and inl = "\<lambda>_. Star"
    and inr = "\<lambda>_. Star"
    and cases = "\<lambda>_ _ _ _ _. Star"
  .

definition unit_erase_label :: "unit_label \<Rightarrow> unit" where
  "unit_erase_label l = ()"

definition unit_lift_label :: "(unit_label, 'a) lfm list \<Rightarrow> 'a fm \<Rightarrow> unit_label" where
  "unit_lift_label \<Gamma> A = Star"

interpretation unit_labels: label_algebra
  where app = "\<lambda>_ _. Star"
    and lam = "\<lambda>_ _. Star"
    and pair = "\<lambda>_ _. Star"
    and fst_l = "\<lambda>_. Star"
    and snd_l = "\<lambda>_. Star"
    and abort = "\<lambda>_. Star"
    and inl = "\<lambda>_. Star"
    and inr = "\<lambda>_. Star"
    and cases = "\<lambda>_ _ _ _ _. Star"
    and lderives = unit_labels.lderives
    and erase_label = unit_erase_label
    and lift_label = unit_lift_label
proof
  fix l
  show "unit_erase_label l = ()"
    by (simp add: unit_erase_label_def)
next
  fix \<Gamma> :: "(unit_label, 'a) lfm list" and x :: "(unit_label, 'a) lfm"
  assume "unit_labels.lderives \<Gamma> x"
  then show "erase_ctx \<Gamma> \<turnstile> erase_lfm x"
    by (rule unit_labels.erasure_sound)
next
  fix \<Gamma> :: "(unit_label, 'a) lfm list" and A :: "'a fm"
  assume ordinary: "erase_ctx \<Gamma> \<turnstile> A"
  then obtain l where deriv: "unit_labels.lderives \<Gamma> (l, A)"
    using unit_labels.lifting_general by blast
  then show "unit_labels.lderives \<Gamma> (unit_lift_label \<Gamma> A, A)"
    by (cases l) (simp add: unit_lift_label_def)
qed

definition unit_lift :: "'a fm list \<Rightarrow> (unit_label \<times> 'a fm) list" where
  "unit_lift \<Gamma> = map (\<lambda>A. (Star, A)) \<Gamma>"

lemma erase_ctx_unit_lift [simp]:
  "erase_ctx (unit_lift \<Gamma>) = \<Gamma>"
  by (simp add: unit_lift_def erase_ctx_def comp_def)

lemma unit_labels_from_ordinary:
  assumes "\<Gamma> \<turnstile> A"
  shows "unit_labels.lderives (unit_lift \<Gamma>) (Star, A)"
  using assms
proof (induction rule: derives.induct)
  case (Assm A \<Gamma>)
  then have "(Star, A) \<in> set (unit_lift \<Gamma>)"
    by (auto simp: unit_lift_def)
  then show ?case
    by (rule unit_labels.LAssm)
next
  case (BotE \<Gamma> A)
  have "unit_labels.lderives (unit_lift \<Gamma>) ((\<lambda>_. Star) Star, A)"
    using BotE.IH by (rule unit_labels.LBotE)
  then show ?case
    by simp
next
  case (ImpI A \<Gamma> B)
  have "unit_labels.lderives ((Star, A) # unit_lift \<Gamma>) (Star, B)"
    using ImpI.IH by (simp add: unit_lift_def)
  then show ?case
    by (rule unit_labels.LImpI)
next
  case (ImpE \<Gamma> A B)
  have "unit_labels.lderives (unit_lift \<Gamma>) ((\<lambda>_ _. Star) Star Star, B)"
    using ImpE.IH by (rule unit_labels.LImpE)
  then show ?case
    by simp
next
  case (ConI \<Gamma> A B)
  have "unit_labels.lderives (unit_lift \<Gamma>) ((\<lambda>_ _. Star) Star Star, Con A B)"
    using ConI.IH by (rule unit_labels.LConI)
  then show ?case
    by simp
next
  case (ConE1 \<Gamma> A B)
  have "unit_labels.lderives (unit_lift \<Gamma>) ((\<lambda>_. Star) Star, A)"
    using ConE1.IH by (rule unit_labels.LConE1)
  then show ?case
    by simp
next
  case (ConE2 \<Gamma> A B)
  have "unit_labels.lderives (unit_lift \<Gamma>) ((\<lambda>_. Star) Star, B)"
    using ConE2.IH by (rule unit_labels.LConE2)
  then show ?case
    by simp
next
  case (DisI1 \<Gamma> A B)
  have "unit_labels.lderives (unit_lift \<Gamma>) ((\<lambda>_. Star) Star, Dis A B)"
    using DisI1.IH by (rule unit_labels.LDisI1)
  then show ?case
    by simp
next
  case (DisI2 \<Gamma> B A)
  have "unit_labels.lderives (unit_lift \<Gamma>) ((\<lambda>_. Star) Star, Dis A B)"
    using DisI2.IH by (rule unit_labels.LDisI2)
  then show ?case
    by simp
next
  case (DisE \<Gamma> A B C)
  have disj: "unit_labels.lderives (unit_lift \<Gamma>) (Star, Dis A B)"
    by (rule DisE.IH(1))
  have left: "unit_labels.lderives ((Star, A) # unit_lift \<Gamma>) (Star, C)"
    using DisE.IH(2) by (simp add: unit_lift_def)
  have right: "unit_labels.lderives ((Star, B) # unit_lift \<Gamma>) (Star, C)"
    using DisE.IH(3) by (simp add: unit_lift_def)
  have "unit_labels.lderives (unit_lift \<Gamma>) ((\<lambda>_ _ _ _ _. Star) Star Star Star Star Star, C)"
    using disj left right by (rule unit_labels.LDisE)
  then show ?case
    by simp
qed

theorem unit_labels_conservative:
  "\<Gamma> \<turnstile> A \<longleftrightarrow> unit_labels.lderives (unit_lift \<Gamma>) (Star, A)"
proof
  assume ordinary: "\<Gamma> \<turnstile> A"
  then have ordinary_erased: "erase_ctx (unit_lift \<Gamma>) \<turnstile> A"
    by simp
  have "unit_labels.lderives
      (unit_lift \<Gamma>) (unit_lift_label (unit_lift \<Gamma>) A, A)"
    using ordinary_erased by (rule unit_labels.lift_coherence)
  with ordinary_erased have "\<exists>l. unit_labels.lderives (unit_lift \<Gamma>) (l, A)"
    using unit_labels.framework_adequacy by blast
  then obtain l where "unit_labels.lderives (unit_lift \<Gamma>) (l, A)"
    by blast
  then show "unit_labels.lderives (unit_lift \<Gamma>) (Star, A)"
    by (cases l) simp
next
  assume "unit_labels.lderives (unit_lift \<Gamma>) (Star, A)"
  then have "\<exists>l. unit_labels.lderives (unit_lift \<Gamma>) (l, A)"
    by blast
  then have "erase_ctx (unit_lift \<Gamma>) \<turnstile> A"
    using unit_labels.framework_adequacy by blast
  then show "\<Gamma> \<turnstile> A"
    by simp
qed

end
