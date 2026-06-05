(*  Title:      Lifting.thy
    Author:     Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz, 2026
    Maintainer: Arthur Freitas Ramos

    Concrete proof-label datatype and the locale interpretation supplying
    a canonical lift; ordinary derivations admit a labelling under this
    default discipline.
*)

theory Lifting
  imports Label_Algebra
begin

text \<open>
This theory supplies a concrete datatype of proof labels and interprets the
abstract label-structure locale with its constructors.  With these labels,
ordinary derivations can always be decorated to obtain a labelled derivation
over any labelled context whose erasure is the ordinary context.
\<close>

datatype label =
    Hyp nat
  | App label label
  | Lam label label
  | Pair label label
  | FstL label
  | SndL label
  | Inl label
  | Inr label
  | Cases label label label label label
  | Abort label

interpretation default_labels: label_structure
  where app = App
    and lam = Lam
    and pair = Pair
    and fst_l = FstL
    and snd_l = SndL
    and abort = Abort
    and inl = Inl
    and inr = Inr
    and cases = Cases
  .

definition default_erase_label :: "label \<Rightarrow> unit" where
  "default_erase_label l = ()"

definition default_lift_label :: "(label, 'a) lfm list \<Rightarrow> 'a fm \<Rightarrow> label" where
  "default_lift_label \<Gamma> A =
    (SOME l. default_labels.lderives \<Gamma> (l, A))"

interpretation default_labels: label_algebra
  where app = App
    and lam = Lam
    and pair = Pair
    and fst_l = FstL
    and snd_l = SndL
    and abort = Abort
    and inl = Inl
    and inr = Inr
    and cases = Cases
    and lderives = default_labels.lderives
    and erase_label = default_erase_label
    and lift_label = default_lift_label
proof
  fix l
  show "default_erase_label l = ()"
    by (simp add: default_erase_label_def)
next
  fix \<Gamma> :: "(label, 'a) lfm list" and x :: "(label, 'a) lfm"
  assume "default_labels.lderives \<Gamma> x"
  then show "erase_ctx \<Gamma> \<turnstile> erase_lfm x"
    by (rule default_labels.erasure_sound)
next
  fix \<Gamma> :: "(label, 'a) lfm list" and A :: "'a fm"
  assume ordinary: "erase_ctx \<Gamma> \<turnstile> A"
  have "\<exists>l. default_labels.lderives \<Gamma> (l, A)"
    by (rule default_labels.lifting_general[OF ordinary])
  then show "default_labels.lderives \<Gamma> (default_lift_label \<Gamma> A, A)"
    unfolding default_lift_label_def by (rule someI_ex)
qed

lemma erase_ctx_mem_ex:
  assumes "A \<in> set (erase_ctx \<Gamma>)"
  shows "\<exists>l. (l, A) \<in> set \<Gamma>"
  using assms
  by (induction \<Gamma>) (auto simp: erase_ctx_def)

lemma erase_ctx_mem_witness:
  assumes "A \<in> set (erase_ctx \<Gamma>)"
  obtains l where "(l, A) \<in> set \<Gamma>"
  using erase_ctx_mem_ex[OF assms] by blast

lemma ordinary_derivations_have_labelling_aux:
  assumes "\<Delta> \<turnstile> A" and "erase_ctx \<Gamma> = \<Delta>"
  shows "\<exists>l. default_labels.lderives \<Gamma> (l, A)"
  using assms
proof (induction arbitrary: \<Gamma> rule: derives.induct)
  case (Assm A \<Delta>)
  then have "A \<in> set (erase_ctx \<Gamma>)"
    by simp
  then obtain l where "(l, A) \<in> set \<Gamma>"
    by (rule erase_ctx_mem_witness)
  then have "default_labels.lderives \<Gamma> (l, A)"
    by (rule default_labels.LAssm)
  then show ?case
    by blast
next
  case (BotE \<Delta> A)
  then obtain l where "default_labels.lderives \<Gamma> (l, Bot)"
    by blast
  then have "default_labels.lderives \<Gamma> (Abort l, A)"
    by (rule default_labels.LBotE)
  then show ?case
    by blast
next
  case (ImpI A \<Delta> B)
  have "erase_ctx ((Hyp 0, A) # \<Gamma>) = A # \<Delta>"
    using ImpI.prems by simp
  then obtain m where "default_labels.lderives ((Hyp 0, A) # \<Gamma>) (m, B)"
    using ImpI.IH by blast
  then have "default_labels.lderives \<Gamma> (Lam (Hyp 0) m, Imp A B)"
    by (rule default_labels.LImpI)
  then show ?case
    by blast
next
  case (ImpE \<Delta> A B)
  then obtain l where imp: "default_labels.lderives \<Gamma> (l, Imp A B)"
    by blast
  from ImpE obtain m where arg: "default_labels.lderives \<Gamma> (m, A)"
    by blast
  from imp arg have "default_labels.lderives \<Gamma> (App l m, B)"
    by (rule default_labels.LImpE)
  then show ?case
    by blast
next
  case (ConI \<Delta> A B)
  then obtain l where left: "default_labels.lderives \<Gamma> (l, A)"
    by blast
  from ConI obtain m where right: "default_labels.lderives \<Gamma> (m, B)"
    by blast
  from left right have "default_labels.lderives \<Gamma> (Pair l m, Con A B)"
    by (rule default_labels.LConI)
  then show ?case
    by blast
next
  case (ConE1 \<Delta> A B)
  then obtain l where "default_labels.lderives \<Gamma> (l, Con A B)"
    by blast
  then have "default_labels.lderives \<Gamma> (FstL l, A)"
    by (rule default_labels.LConE1)
  then show ?case
    by blast
next
  case (ConE2 \<Delta> A B)
  then obtain l where "default_labels.lderives \<Gamma> (l, Con A B)"
    by blast
  then have "default_labels.lderives \<Gamma> (SndL l, B)"
    by (rule default_labels.LConE2)
  then show ?case
    by blast
next
  case (DisI1 \<Delta> A B)
  then obtain l where "default_labels.lderives \<Gamma> (l, A)"
    by blast
  then have "default_labels.lderives \<Gamma> (Inl l, Dis A B)"
    by (rule default_labels.LDisI1)
  then show ?case
    by blast
next
  case (DisI2 \<Delta> B A)
  then obtain l where "default_labels.lderives \<Gamma> (l, B)"
    by blast
  then have "default_labels.lderives \<Gamma> (Inr l, Dis A B)"
    by (rule default_labels.LDisI2)
  then show ?case
    by blast
next
  case (DisE \<Delta> A B C)
  then obtain l where disj: "default_labels.lderives \<Gamma> (l, Dis A B)"
    by blast
  have left_ctx: "erase_ctx ((Hyp 0, A) # \<Gamma>) = A # \<Delta>"
    using DisE.prems by simp
  then obtain n where left: "default_labels.lderives ((Hyp 0, A) # \<Gamma>) (n, C)"
    using DisE.IH(2) by blast
  have right_ctx: "erase_ctx ((Hyp 1, B) # \<Gamma>) = B # \<Delta>"
    using DisE.prems by simp
  then obtain q where right: "default_labels.lderives ((Hyp 1, B) # \<Gamma>) (q, C)"
    using DisE.IH(3) by blast
  from disj left right have "default_labels.lderives \<Gamma> (Cases l (Hyp 0) n (Hyp 1) q, C)"
    by (rule default_labels.LDisE)
  then show ?case
    by blast
qed

theorem ordinary_derivations_have_labelling:
  assumes "erase_ctx \<Gamma> \<turnstile> A"
  shows "\<exists>l. default_labels.lderives \<Gamma> (l, A)"
proof -
  have "default_labels.lderives \<Gamma> (default_lift_label \<Gamma> A, A)"
    using assms by (rule default_labels.lift_coherence)
  with assms show ?thesis
    using default_labels.framework_adequacy by blast
qed

theorem ordinary_derivations_admit_labelling:
  assumes "erase_ctx \<Gamma> \<turnstile> A"
  shows "\<exists>l. default_labels.lderives \<Gamma> (l, A)"
  using assms ordinary_derivations_have_labelling by blast

end
