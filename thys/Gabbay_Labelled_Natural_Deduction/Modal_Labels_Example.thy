(*  Title:      Modal_Labels_Example.thy
    Author:     Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz, 2026
    Maintainer: Arthur Freitas Ramos

    Possible-world modal instance: instantiates the framework locale as
    @{term modal_labels} and extends the propositional labelled calculus
    with modal BoxI and BoxE rules; carries the soundness link to Kripke
    validity.
*)

theory Modal_Labels_Example
  imports Label_Algebra
begin

text \<open>
This theory instantiates the framework locale as @{term modal_labels} and then
extends the resulting propositional labelled calculus with modal @{text BoxI}
and @{text BoxE} rules.  Modal labels carry possible-world annotations; the
propositional constructors preserve the current world, while box elimination
projects to an accessible world.
\<close>

datatype modal_label =
    MWorld nat
  | MApp modal_label modal_label
  | MLam modal_label modal_label
  | MPair modal_label modal_label
  | MFst modal_label
  | MSnd modal_label
  | MInl modal_label
  | MInr modal_label
  | MCases modal_label modal_label modal_label modal_label modal_label
  | MAbort modal_label
  | MBoxI modal_label
  | MBoxE modal_label

fun world_of :: "modal_label \<Rightarrow> nat" where
  "world_of (MWorld w) = w"
| "world_of (MApp l m) = world_of l"
| "world_of (MLam l m) = world_of m"
| "world_of (MPair l m) = world_of l"
| "world_of (MFst l) = world_of l"
| "world_of (MSnd l) = world_of l"
| "world_of (MInl l) = world_of l"
| "world_of (MInr l) = world_of l"
| "world_of (MCases l m n p q) = world_of l"
| "world_of (MAbort l) = world_of l"
| "world_of (MBoxI l) = world_of l"
| "world_of (MBoxE l) = world_of l"

interpretation modal_labels: label_structure
  where app = MApp
    and lam = MLam
    and pair = MPair
    and fst_l = MFst
    and snd_l = MSnd
    and abort = MAbort
    and inl = MInl
    and inr = MInr
    and cases = MCases
  .

definition modal_erase_label :: "modal_label \<Rightarrow> unit" where
  "modal_erase_label l = ()"

definition modal_lift_label :: "(modal_label, 'a) lfm list \<Rightarrow> 'a fm \<Rightarrow> modal_label" where
  "modal_lift_label \<Gamma> A =
    (SOME l. modal_labels.lderives \<Gamma> (l, A))"

interpretation modal_labels: label_algebra
  where app = MApp
    and lam = MLam
    and pair = MPair
    and fst_l = MFst
    and snd_l = MSnd
    and abort = MAbort
    and inl = MInl
    and inr = MInr
    and cases = MCases
    and lderives = modal_labels.lderives
    and erase_label = modal_erase_label
    and lift_label = modal_lift_label
proof
  fix l
  show "modal_erase_label l = ()"
    by (simp add: modal_erase_label_def)
next
  fix \<Gamma> :: "(modal_label, 'a) lfm list" and x :: "(modal_label, 'a) lfm"
  assume "modal_labels.lderives \<Gamma> x"
  then show "erase_ctx \<Gamma> \<turnstile> erase_lfm x"
    by (rule modal_labels.erasure_sound)
next
  fix \<Gamma> :: "(modal_label, 'a) lfm list" and A :: "'a fm"
  assume ordinary: "erase_ctx \<Gamma> \<turnstile> A"
  have "\<exists>l. modal_labels.lderives \<Gamma> (l, A)"
    by (rule modal_labels.lifting_general[OF ordinary])
  then show "modal_labels.lderives \<Gamma> (modal_lift_label \<Gamma> A, A)"
    unfolding modal_lift_label_def by (rule someI_ex)
qed

datatype 'a mfm =
    MAtom 'a
  | MBot
  | MImp "'a mfm" "'a mfm"
  | MCon "'a mfm" "'a mfm"
  | MDis "'a mfm" "'a mfm"
  | Box "'a mfm"

primrec modalise_fm :: "'a fm \<Rightarrow> 'a mfm" where
  "modalise_fm (Atom p) = MAtom p"
| "modalise_fm Bot = MBot"
| "modalise_fm (Imp A B) = MImp (modalise_fm A) (modalise_fm B)"
| "modalise_fm (Con A B) = MCon (modalise_fm A) (modalise_fm B)"
| "modalise_fm (Dis A B) = MDis (modalise_fm A) (modalise_fm B)"

definition modalise_lfm :: "nat \<Rightarrow> (modal_label, 'a) lfm \<Rightarrow> modal_label \<times> 'a mfm" where
  "modalise_lfm w x = (MWorld w, modalise_fm (snd x))"

primrec modal_kripke_sat ::
    "(nat \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a mfm \<Rightarrow> bool"
where
  "modal_kripke_sat V R w (MAtom p) = V w p"
| "modal_kripke_sat V R w MBot = False"
| "modal_kripke_sat V R w (MImp A B) =
    (modal_kripke_sat V R w A \<longrightarrow> modal_kripke_sat V R w B)"
| "modal_kripke_sat V R w (MCon A B) =
    (modal_kripke_sat V R w A \<and> modal_kripke_sat V R w B)"
| "modal_kripke_sat V R w (MDis A B) =
    (modal_kripke_sat V R w A \<or> modal_kripke_sat V R w B)"
| "modal_kripke_sat V R w (Box A) =
    (\<forall>v. R w v \<longrightarrow> modal_kripke_sat V R v A)"

inductive mlderives ::
    "(modal_label \<times> 'a mfm) list \<Rightarrow>
      (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> (modal_label \<times> 'a mfm) \<Rightarrow> bool"
where
  MAssm: "x \<in> set \<Gamma> \<Longrightarrow> mlderives \<Gamma> R x"
| MBotE: "mlderives \<Gamma> R (l, MBot) \<Longrightarrow> mlderives \<Gamma> R (MAbort l, A)"
| MImpI:
    "world_of l = world_of m \<Longrightarrow>
     mlderives ((l, A) # \<Gamma>) R (m, B) \<Longrightarrow>
     mlderives \<Gamma> R (MLam l m, MImp A B)"
| MImpE:
    "world_of l = world_of m \<Longrightarrow>
     mlderives \<Gamma> R (l, MImp A B) \<Longrightarrow>
     mlderives \<Gamma> R (m, A) \<Longrightarrow>
     mlderives \<Gamma> R (MApp l m, B)"
| MConI:
    "world_of l = world_of m \<Longrightarrow>
     mlderives \<Gamma> R (l, A) \<Longrightarrow>
     mlderives \<Gamma> R (m, B) \<Longrightarrow>
     mlderives \<Gamma> R (MPair l m, MCon A B)"
| MConE1: "mlderives \<Gamma> R (l, MCon A B) \<Longrightarrow> mlderives \<Gamma> R (MFst l, A)"
| MConE2: "mlderives \<Gamma> R (l, MCon A B) \<Longrightarrow> mlderives \<Gamma> R (MSnd l, B)"
| MDisI1: "mlderives \<Gamma> R (l, A) \<Longrightarrow> mlderives \<Gamma> R (MInl l, MDis A B)"
| MDisI2: "mlderives \<Gamma> R (l, B) \<Longrightarrow> mlderives \<Gamma> R (MInr l, MDis A B)"
| MDisE:
    "world_of l = world_of m \<Longrightarrow>
     world_of l = world_of n \<Longrightarrow>
     world_of l = world_of p \<Longrightarrow>
     world_of l = world_of q \<Longrightarrow>
     mlderives \<Gamma> R (l, MDis A B) \<Longrightarrow>
     mlderives ((m, A) # \<Gamma>) R (n, C) \<Longrightarrow>
     mlderives ((p, B) # \<Gamma>) R (q, C) \<Longrightarrow>
     mlderives \<Gamma> R (MCases l m n p q, C)"
| MBoxI:
    "(\<And>v. R (world_of l) v \<Longrightarrow>
      \<exists>m. world_of m = v \<and> mlderives \<Gamma> R (m, A)) \<Longrightarrow>
     mlderives \<Gamma> R (MBoxI l, Box A)"
| MBoxE:
    "mlderives \<Gamma> R (l, Box A) \<Longrightarrow>
     R (world_of l) v \<Longrightarrow>
     mlderives \<Gamma> R (MBoxE (MWorld v), A)"

theorem propositional_modal_sound:
  assumes "modal_labels.lderives \<Gamma> x"
  shows "\<exists>l. world_of l = w \<and>
    mlderives (map (modalise_lfm w) \<Gamma>) R (l, modalise_fm (snd x))"
  using assms
proof (induction arbitrary: w R rule: modal_labels.lderives.induct)
  case (LAssm x \<Gamma>)
  then show ?case
    by (intro exI[of _ "MWorld w"])
      (auto simp: modalise_lfm_def intro: mlderives.MAssm)
next
  case (LBotE \<Gamma> l A)
  then obtain k where k: "world_of k = w"
      "mlderives (map (modalise_lfm w) \<Gamma>) R (k, MBot)"
    by auto
  then show ?case
    by (intro exI[of _ "MAbort k"]) (auto intro: mlderives.MBotE)
next
  case (LImpI l A \<Gamma> m B)
  then obtain k where k: "world_of k = w"
      "mlderives (map (modalise_lfm w) ((l, A) # \<Gamma>)) R (k, modalise_fm B)"
    by auto
  then have body: "mlderives ((MWorld w, modalise_fm A) #
      map (modalise_lfm w) \<Gamma>) R (k, modalise_fm B)"
    by (simp add: modalise_lfm_def)
  then have "mlderives (map (modalise_lfm w) \<Gamma>) R
      (MLam (MWorld w) k, MImp (modalise_fm A) (modalise_fm B))"
    using k(1) by (auto intro: mlderives.MImpI)
  then show ?case
    by (intro exI[of _ "MLam (MWorld w) k"]) (simp add: k(1))
next
  case (LImpE \<Gamma> l A B m)
  from LImpE.IH(1)[of w R] obtain k where k: "world_of k = w"
      "mlderives (map (modalise_lfm w) \<Gamma>) R (k, MImp (modalise_fm A) (modalise_fm B))"
    by auto
  from LImpE.IH(2)[of w R] obtain h where h: "world_of h = w"
      "mlderives (map (modalise_lfm w) \<Gamma>) R (h, modalise_fm A)"
    by auto
  then have "mlderives (map (modalise_lfm w) \<Gamma>) R (MApp k h, modalise_fm B)"
    using k by (auto intro: mlderives.MImpE)
  then show ?case
    by (intro exI[of _ "MApp k h"]) (simp add: k h)
next
  case (LConI \<Gamma> l A m B)
  from LConI.IH(1)[of w R] obtain k where k: "world_of k = w"
      "mlderives (map (modalise_lfm w) \<Gamma>) R (k, modalise_fm A)"
    by auto
  from LConI.IH(2)[of w R] obtain h where h: "world_of h = w"
      "mlderives (map (modalise_lfm w) \<Gamma>) R (h, modalise_fm B)"
    by auto
  then have "mlderives (map (modalise_lfm w) \<Gamma>) R
      (MPair k h, MCon (modalise_fm A) (modalise_fm B))"
    using k by (auto intro: mlderives.MConI)
  then show ?case
    by (intro exI[of _ "MPair k h"]) (simp add: k h)
next
  case (LConE1 \<Gamma> l A B)
  then obtain k where k: "world_of k = w"
      "mlderives (map (modalise_lfm w) \<Gamma>) R (k, MCon (modalise_fm A) (modalise_fm B))"
    by auto
  then show ?case
    by (intro exI[of _ "MFst k"]) (auto intro: mlderives.MConE1)
next
  case (LConE2 \<Gamma> l A B)
  then obtain k where k: "world_of k = w"
      "mlderives (map (modalise_lfm w) \<Gamma>) R (k, MCon (modalise_fm A) (modalise_fm B))"
    by auto
  then show ?case
    by (intro exI[of _ "MSnd k"]) (auto intro: mlderives.MConE2)
next
  case (LDisI1 \<Gamma> l A B)
  then obtain k where k: "world_of k = w"
      "mlderives (map (modalise_lfm w) \<Gamma>) R (k, modalise_fm A)"
    by auto
  then show ?case
    by (intro exI[of _ "MInl k"]) (auto intro: mlderives.MDisI1)
next
  case (LDisI2 \<Gamma> l B A)
  then obtain k where k: "world_of k = w"
      "mlderives (map (modalise_lfm w) \<Gamma>) R (k, modalise_fm B)"
    by auto
  then show ?case
    by (intro exI[of _ "MInr k"]) (auto intro: mlderives.MDisI2)
next
  case (LDisE \<Gamma> l A B m n C p q)
  from LDisE.IH(1)[of w R] obtain d where d:
      "world_of d = w"
      "mlderives (map (modalise_lfm w) \<Gamma>) R (d, MDis (modalise_fm A) (modalise_fm B))"
    by auto
  from LDisE.IH(2)[of w R] obtain left where left:
      "world_of left = w"
      "mlderives (map (modalise_lfm w) ((m, A) # \<Gamma>)) R (left, modalise_fm C)"
    by auto
  from LDisE.IH(3)[of w R] obtain right where right:
      "world_of right = w"
      "mlderives (map (modalise_lfm w) ((p, B) # \<Gamma>)) R (right, modalise_fm C)"
    by auto
  from left have left_deriv: "mlderives ((MWorld w, modalise_fm A) #
      map (modalise_lfm w) \<Gamma>) R (left, modalise_fm C)"
    by (simp add: modalise_lfm_def)
  from right have right_deriv: "mlderives ((MWorld w, modalise_fm B) #
      map (modalise_lfm w) \<Gamma>) R (right, modalise_fm C)"
    by (simp add: modalise_lfm_def)
  have "mlderives (map (modalise_lfm w) \<Gamma>) R
      (MCases d (MWorld w) left (MWorld w) right, modalise_fm C)"
    using d left right left_deriv right_deriv by (auto intro: mlderives.MDisE)
  then show ?case
    by (intro exI[of _ "MCases d (MWorld w) left (MWorld w) right"])
      (simp add: d left right)
qed

theorem modal_labels_sound:
  assumes "mlderives \<Gamma> R x"
    and "\<forall>(l, A) \<in> set \<Gamma>. modal_kripke_sat V R (world_of l) A"
  shows "modal_kripke_sat V R (world_of (fst x)) (snd x)"
  using assms
proof (induction arbitrary: V rule: mlderives.induct)
  case (MAssm x \<Gamma> R)
  then show ?case
    by (cases x) auto
next
  case (MBotE \<Gamma> R l A)
  then show ?case
    by auto
next
  case (MImpI l m A \<Gamma> R B)
  then show ?case
    by auto
next
  case (MImpE l m \<Gamma> R A B)
  then show ?case
    by auto
next
  case (MConI l m \<Gamma> R A B)
  then show ?case
    by auto
next
  case (MConE1 \<Gamma> R l A B)
  then show ?case
    by auto
next
  case (MConE2 \<Gamma> R l A B)
  then show ?case
    by auto
next
  case (MDisI1 \<Gamma> R l A B)
  then show ?case
    by auto
next
  case (MDisI2 \<Gamma> R l B A)
  then show ?case
    by auto
next
  case (MDisE l m n p q \<Gamma> R A B C)
  then show ?case
    by auto
next
  case (MBoxI l R \<Gamma> A)
  then show ?case
    by auto
next
  case (MBoxE \<Gamma> R l A v)
  then show ?case
    by auto
qed

end
