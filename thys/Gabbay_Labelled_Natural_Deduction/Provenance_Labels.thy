(*  Title:      Provenance_Labels.thy
    Author:     Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz, 2026
    Maintainer: Arthur Freitas Ramos

    Provenance-label instance: labels are sets of natural-number
    assumption indices. Records a sound over-approximation of assumption
    dependencies and the headline provenance-completeness theorem
    equating ordinary derivability with the existence of a
    provenance-labelled derivation whose filtered sub-context still
    derives the conclusion.
*)

theory Provenance_Labels
  imports Label_Algebra
begin

text \<open>
This theory instantiates labels by sets of natural-number assumption indices.
Application and pairing combine provenance by union, implication introduction
removes the discharged assumption label, and disjunction elimination records
the analysed disjunction together with the branch dependencies that survive
discharge.
\<close>

type_synonym prov = "nat set"

interpretation provenance: label_structure
  where app = "\<lambda>(S::prov) T. S \<union> T"
    and lam = "\<lambda>(S::prov) T. T - S"
    and pair = "\<lambda>(S::prov) T. S \<union> T"
    and fst_l = "\<lambda>(S::prov). S"
    and snd_l = "\<lambda>(S::prov). S"
    and abort = "\<lambda>(S::prov). S"
    and inl = "\<lambda>(S::prov). S"
    and inr = "\<lambda>(S::prov). S"
    and cases = "\<lambda>(S::prov) (M::prov) (N::prov) (P::prov) (Q::prov).
      S \<union> (N - M) \<union> (Q - P)"
  .

definition provenance_erase_label :: "prov \<Rightarrow> unit" where
  "provenance_erase_label S = ()"

definition provenance_lift_label :: "(prov, 'a) lfm list \<Rightarrow> 'a fm \<Rightarrow> prov" where
  "provenance_lift_label \<Gamma> A =
    (SOME S. provenance.lderives \<Gamma> (S, A))"

interpretation provenance: label_algebra
  where app = "\<lambda>(S::prov) T. S \<union> T"
    and lam = "\<lambda>(S::prov) T. T - S"
    and pair = "\<lambda>(S::prov) T. S \<union> T"
    and fst_l = "\<lambda>(S::prov). S"
    and snd_l = "\<lambda>(S::prov). S"
    and abort = "\<lambda>(S::prov). S"
    and inl = "\<lambda>(S::prov). S"
    and inr = "\<lambda>(S::prov). S"
    and cases = "\<lambda>(S::prov) (M::prov) (N::prov) (P::prov) (Q::prov).
      S \<union> (N - M) \<union> (Q - P)"
    and lderives = provenance.lderives
    and erase_label = provenance_erase_label
    and lift_label = provenance_lift_label
proof
  fix S :: prov
  show "provenance_erase_label S = ()"
    by (simp add: provenance_erase_label_def)
next
  fix \<Gamma> :: "(prov, 'a) lfm list" and x :: "(prov, 'a) lfm"
  assume "provenance.lderives \<Gamma> x"
  then show "erase_ctx \<Gamma> \<turnstile> erase_lfm x"
    by (rule provenance.erasure_sound)
next
  fix \<Gamma> :: "(prov, 'a) lfm list" and A :: "'a fm"
  assume ordinary: "erase_ctx \<Gamma> \<turnstile> A"
  have "\<exists>S. provenance.lderives \<Gamma> (S, A)"
    by (rule provenance.lifting_general[OF ordinary])
  then show "provenance.lderives \<Gamma> (provenance_lift_label \<Gamma> A, A)"
    unfolding provenance_lift_label_def by (rule someI_ex)
qed

fun indexed :: "nat \<Rightarrow> 'a fm list \<Rightarrow> (prov \<times> 'a fm) list" where
  "indexed n [] = []"
| "indexed n (A # \<Gamma>) = ({n}, A) # indexed (Suc n) \<Gamma>"

definition ctx_prov :: "(prov, 'a) lfm list \<Rightarrow> prov" where
  "ctx_prov \<Gamma> = \<Union>(fst ` set \<Gamma>)"

lemma ctx_prov_Cons [simp]:
  "ctx_prov ((M, A) # \<Gamma>) = M \<union> ctx_prov \<Gamma>"
  unfolding ctx_prov_def
  by auto

lemma erase_ctx_indexed [simp]:
  "erase_ctx (indexed n \<Gamma>) = \<Gamma>"
  by (induction \<Gamma> arbitrary: n) auto

lemma finite_ctx_prov_indexed [simp]:
  "finite (ctx_prov (indexed n \<Gamma>))"
  by (induction \<Gamma> arbitrary: n) (auto simp: ctx_prov_def)

definition filter_indexed_by :: "nat set \<Rightarrow> 'a fm list \<Rightarrow> 'a fm list" where
  "filter_indexed_by S \<Gamma> =
     map snd (filter (\<lambda>(i, A). i \<in> S) (zip [0..<length \<Gamma>] \<Gamma>))"

lemma filter_indexed_by_mono:
  assumes "S \<subseteq> T"
  shows "set (filter_indexed_by S \<Gamma>) \<subseteq> set (filter_indexed_by T \<Gamma>)"
  using assms
  unfolding filter_indexed_by_def
  by auto

lemma filter_indexed_by_subset_ctx:
  shows "set (filter_indexed_by S \<Gamma>) \<subseteq> set \<Gamma>"
  unfolding filter_indexed_by_def
  by (auto simp: in_set_zip)

lemma filter_indexed_by_empty [simp]:
  "filter_indexed_by {} \<Gamma> = []"
  unfolding filter_indexed_by_def
  by auto

lemma filter_indexed_by_union:
  "set (filter_indexed_by (S \<union> T) \<Gamma>) =
    set (filter_indexed_by S \<Gamma>) \<union> set (filter_indexed_by T \<Gamma>)"
  unfolding filter_indexed_by_def
  by auto

definition filter_labeled_by :: "prov \<Rightarrow> (prov \<times> 'a fm) list \<Rightarrow> 'a fm list" where
  "filter_labeled_by S \<Gamma> =
     map snd (filter (\<lambda>(M, A). M \<inter> S \<noteq> {}) \<Gamma>)"

definition nonempty_prov_ctx :: "(prov \<times> 'a fm) list \<Rightarrow> bool" where
  "nonempty_prov_ctx \<Gamma> \<longleftrightarrow> (\<forall>x \<in> set \<Gamma>. fst x \<noteq> {})"

lemma nonempty_prov_ctx_Cons [simp]:
  "nonempty_prov_ctx ((S, A) # \<Gamma>) \<longleftrightarrow> S \<noteq> {} \<and> nonempty_prov_ctx \<Gamma>"
  unfolding nonempty_prov_ctx_def
  by auto

lemma nonempty_prov_ctx_indexed [simp]:
  "nonempty_prov_ctx (indexed n \<Gamma>)"
  by (induction \<Gamma> arbitrary: n) (auto simp: nonempty_prov_ctx_def)

lemma filter_labeled_by_mono:
  assumes "S \<subseteq> T"
  shows "set (filter_labeled_by S \<Gamma>) \<subseteq> set (filter_labeled_by T \<Gamma>)"
  using assms
  unfolding filter_labeled_by_def
  by auto

lemma filter_labeled_by_union_left:
  "set (filter_labeled_by S \<Gamma>) \<subseteq> set (filter_labeled_by (S \<union> T) \<Gamma>)"
  by (rule filter_labeled_by_mono) auto

lemma filter_labeled_by_union_right:
  "set (filter_labeled_by T \<Gamma>) \<subseteq> set (filter_labeled_by (S \<union> T) \<Gamma>)"
  by (rule filter_labeled_by_mono) auto

lemma ctx_prov_contains_label:
  assumes "(M, A) \<in> set \<Gamma>"
  shows "M \<subseteq> ctx_prov \<Gamma>"
  using assms
  unfolding ctx_prov_def
  by auto

lemma filter_labeled_by_minus_fresh:
  assumes "M \<inter> ctx_prov \<Gamma> = {}"
  shows "set (filter_labeled_by N \<Gamma>) \<subseteq> set (filter_labeled_by (N - M) \<Gamma>)"
proof
  fix A
  assume "A \<in> set (filter_labeled_by N \<Gamma>)"
  then obtain y where y_in: "y \<in> set \<Gamma>"
    and y_used: "(case y of (L, B) \<Rightarrow> L \<inter> N \<noteq> {})"
    and y_snd: "snd y = A"
    unfolding filter_labeled_by_def
    by auto
  obtain L B where y: "y = (L, B)"
    by (cases y)
  have in_ctx: "(L, A) \<in> set \<Gamma>"
    using y y_in y_snd by auto
  have used: "L \<inter> N \<noteq> {}"
    using y y_used by simp
  have "L \<inter> M = {}"
    using assms ctx_prov_contains_label[OF in_ctx] by auto
  with used have "L \<inter> (N - M) \<noteq> {}"
    by auto
  with in_ctx have "(L, A) \<in>
      set (filter (\<lambda>(K, B). K \<inter> (N - M) \<noteq> {}) \<Gamma>)"
    by auto
  then show "A \<in> set (filter_labeled_by (N - M) \<Gamma>)"
    unfolding filter_labeled_by_def by force
qed

lemma filter_labeled_by_cons_minus_subset:
  assumes "M \<inter> ctx_prov \<Gamma> = {}"
  shows "set (filter_labeled_by N ((M, A) # \<Gamma>)) \<subseteq>
    set (A # filter_labeled_by (N - M) \<Gamma>)"
proof -
  have "set (filter_labeled_by N ((M, A) # \<Gamma>)) \<subseteq>
      insert A (set (filter_labeled_by N \<Gamma>))"
    unfolding filter_labeled_by_def
    by auto
  also have "\<dots> \<subseteq> set (A # filter_labeled_by (N - M) \<Gamma>)"
    using filter_labeled_by_minus_fresh[OF assms] by auto
  finally show ?thesis .
qed

lemma filter_labeled_by_cons_minus_mono_subset:
  assumes "M \<inter> ctx_prov \<Gamma> = {}" and "N - M \<subseteq> U"
  shows "set (filter_labeled_by N ((M, A) # \<Gamma>)) \<subseteq>
    set (A # filter_labeled_by U \<Gamma>)"
proof -
  have "set (filter_labeled_by N ((M, A) # \<Gamma>)) \<subseteq>
      set (A # filter_labeled_by (N - M) \<Gamma>)"
    using assms(1) by (rule filter_labeled_by_cons_minus_subset)
  moreover have "set (filter_labeled_by (N - M) \<Gamma>) \<subseteq>
      set (filter_labeled_by U \<Gamma>)"
    using assms(2) by (rule filter_labeled_by_mono)
  ultimately show ?thesis
    by auto
qed

lemma filter_labeled_by_indexed_upt:
  "filter_labeled_by S (indexed n \<Gamma>) =
    map snd (filter (\<lambda>(i, A). i \<in> S) (zip [n..<n + length \<Gamma>] \<Gamma>))"
proof (induction \<Gamma> arbitrary: n)
  case Nil
  then show ?case
    by (simp add: filter_labeled_by_def)
next
  case (Cons A \<Gamma>)
  have upt: "[n..<n + length (A # \<Gamma>)] =
      n # [Suc n..<Suc n + length \<Gamma>]"
  proof -
    have "[n..<n + length (A # \<Gamma>)] = n # [Suc n..<n + length (A # \<Gamma>)]"
      by (rule upt_conv_Cons) simp
    also have "\<dots> = n # [Suc n..<Suc n + length \<Gamma>]"
      by simp
    finally show ?thesis .
  qed
  show ?case
    using Cons.IH[of "Suc n"] upt
    by (auto simp: filter_labeled_by_def)
qed

lemma filter_labeled_by_indexed_0:
  "filter_labeled_by S (indexed 0 \<Gamma>) = filter_indexed_by S \<Gamma>"
  by (simp add: filter_labeled_by_indexed_upt filter_indexed_by_def)

inductive prov_safe :: "(prov \<times> 'a fm) list \<Rightarrow> prov \<times> 'a fm \<Rightarrow> bool"
  ("_ \<turnstile>P _" [50, 50] 50)
where
  PAssm:
    "x \<in> set \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>P x"
| PBotE:
    "\<Gamma> \<turnstile>P (S, Bot) \<Longrightarrow> \<Gamma> \<turnstile>P (S, A)"
| PImpI:
    "(M, A) # \<Gamma> \<turnstile>P (N, B) \<Longrightarrow>
     M \<inter> ctx_prov \<Gamma> = {} \<Longrightarrow>
     M \<noteq> {} \<Longrightarrow>
     \<Gamma> \<turnstile>P (N - M, Imp A B)"
| PImpE:
    "\<Gamma> \<turnstile>P (S, Imp A B) \<Longrightarrow>
     \<Gamma> \<turnstile>P (T, A) \<Longrightarrow>
     \<Gamma> \<turnstile>P (S \<union> T, B)"
| PConI:
    "\<Gamma> \<turnstile>P (S, A) \<Longrightarrow>
     \<Gamma> \<turnstile>P (T, B) \<Longrightarrow>
     \<Gamma> \<turnstile>P (S \<union> T, Con A B)"
| PConE1:
    "\<Gamma> \<turnstile>P (S, Con A B) \<Longrightarrow> \<Gamma> \<turnstile>P (S, A)"
| PConE2:
    "\<Gamma> \<turnstile>P (S, Con A B) \<Longrightarrow> \<Gamma> \<turnstile>P (S, B)"
| PDisI1:
    "\<Gamma> \<turnstile>P (S, A) \<Longrightarrow> \<Gamma> \<turnstile>P (S, Dis A B)"
| PDisI2:
    "\<Gamma> \<turnstile>P (S, B) \<Longrightarrow> \<Gamma> \<turnstile>P (S, Dis A B)"
| PDisE:
    "\<Gamma> \<turnstile>P (S, Dis A B) \<Longrightarrow>
     (M, A) # \<Gamma> \<turnstile>P (N, C) \<Longrightarrow>
     (P, B) # \<Gamma> \<turnstile>P (Q, C) \<Longrightarrow>
     M \<inter> ctx_prov \<Gamma> = {} \<Longrightarrow> M \<noteq> {} \<Longrightarrow>
     P \<inter> ctx_prov \<Gamma> = {} \<Longrightarrow> P \<noteq> {} \<Longrightarrow>
     M \<inter> P = {} \<Longrightarrow>
     \<Gamma> \<turnstile>P (S \<union> (N - M) \<union> (Q - P), C)"

lemma provenance_labels_in_context:
  assumes "provenance.lderives \<Gamma> x"
  shows "fst x \<subseteq> ctx_prov \<Gamma>"
  using assms
  by (induction rule: provenance.lderives.induct) (auto simp: ctx_prov_def)

lemma ctx_prov_indexed_bound:
  assumes "i \<in> ctx_prov (indexed n \<Gamma>)"
  shows "i < n + length \<Gamma>"
  using assms
proof (induction \<Gamma> arbitrary: n i)
  case Nil
  then show ?case
    by (simp add: ctx_prov_def)
next
  case (Cons A \<Gamma>)
  then consider "i = n" | "i \<in> ctx_prov (indexed (Suc n) \<Gamma>)"
    by (auto simp: ctx_prov_def)
  then show ?case
  proof cases
    case 1
    then show ?thesis
      by simp
  next
    case 2
    then have "i < Suc n + length \<Gamma>"
      by (rule Cons.IH)
    then show ?thesis
      by simp
  qed
qed

theorem provenance_overapproximates_dependencies:
  assumes "provenance.lderives (indexed 0 \<Gamma>0) (S, A)"
  shows "\<forall>i. i \<in> S \<longrightarrow> i < length \<Gamma>0"
proof
  fix i
  show "i \<in> S \<longrightarrow> i < length \<Gamma>0"
  proof
    assume "i \<in> S"
    moreover have "S \<subseteq> ctx_prov (indexed 0 \<Gamma>0)"
      using provenance_labels_in_context[OF assms] by simp
    ultimately have "i \<in> ctx_prov (indexed 0 \<Gamma>0)"
      by auto
    then show "i < length \<Gamma>0"
      using ctx_prov_indexed_bound[of i 0 \<Gamma>0] by simp
  qed
qed

lemma prov_safe_implies_lderives:
  assumes "\<Gamma> \<turnstile>P x"
  shows "provenance.lderives \<Gamma> x"
  using assms
  by (induction rule: prov_safe.induct)
    (auto intro: provenance.LAssm provenance.LBotE provenance.LImpI
      provenance.LImpE provenance.LConI provenance.LConE1 provenance.LConE2
      provenance.LDisI1 provenance.LDisI2 provenance.LDisE)

lemma provenance_drop_unused_general:
  assumes "\<Gamma> \<turnstile>P x" and "nonempty_prov_ctx \<Gamma>"
  shows "filter_labeled_by (fst x) \<Gamma> \<turnstile> snd x"
  using assms
proof (induction rule: prov_safe.induct)
  case (PAssm x \<Gamma>)
  obtain M A where x: "x = (M, A)"
    by (cases x)
  then have in_ctx: "(M, A) \<in> set \<Gamma>"
    using PAssm by simp
  moreover have "M \<noteq> {}"
    using PAssm x
    unfolding nonempty_prov_ctx_def filter_labeled_by_def
    by auto
  then have "M \<inter> M \<noteq> {}"
    by auto
  ultimately have "(M, A) \<in>
      set (filter (\<lambda>(L, B). L \<inter> M \<noteq> {}) \<Gamma>)"
    by auto
  then have "A \<in> set (filter_labeled_by M \<Gamma>)"
    unfolding filter_labeled_by_def by force
  then show ?case
    using x by (auto intro: derives.Assm)
next
  case (PBotE \<Gamma> S A)
  then show ?case
    by (auto intro: derives.BotE)
next
  case (PImpI M A \<Gamma> N B)
  have ne: "nonempty_prov_ctx ((M, A) # \<Gamma>)"
    using PImpI by simp
  have body: "filter_labeled_by N ((M, A) # \<Gamma>) \<turnstile> B"
    using PImpI.IH[OF ne] by simp
  have sub: "set (filter_labeled_by N ((M, A) # \<Gamma>)) \<subseteq>
      set (A # filter_labeled_by (N - M) \<Gamma>)"
    using PImpI by (intro filter_labeled_by_cons_minus_subset) auto
  have "filter_labeled_by (N - M) \<Gamma> \<turnstile> Imp A B"
  proof (rule derives.ImpI)
    show "A # filter_labeled_by (N - M) \<Gamma> \<turnstile> B"
      by (rule weakening[OF body sub])
  qed
  then show ?case
    by simp
next
  case (PImpE \<Gamma> S A B T)
  have imp0: "filter_labeled_by S \<Gamma> \<turnstile> Imp A B"
    using PImpE.IH(1)[OF PImpE.prems] by simp
  have arg0: "filter_labeled_by T \<Gamma> \<turnstile> A"
    using PImpE.IH(2)[OF PImpE.prems] by simp
  have imp: "filter_labeled_by (S \<union> T) \<Gamma> \<turnstile> Imp A B"
    by (rule weakening[OF imp0 filter_labeled_by_union_left])
  have arg: "filter_labeled_by (S \<union> T) \<Gamma> \<turnstile> A"
    by (rule weakening[OF arg0 filter_labeled_by_union_right])
  have "filter_labeled_by (S \<union> T) \<Gamma> \<turnstile> B"
    by (rule derives.ImpE[OF imp arg])
  then show ?case
    by simp
next
  case (PConI \<Gamma> S A T B)
  have left0: "filter_labeled_by S \<Gamma> \<turnstile> A"
    using PConI.IH(1)[OF PConI.prems] by simp
  have right0: "filter_labeled_by T \<Gamma> \<turnstile> B"
    using PConI.IH(2)[OF PConI.prems] by simp
  have left: "filter_labeled_by (S \<union> T) \<Gamma> \<turnstile> A"
    by (rule weakening[OF left0 filter_labeled_by_union_left])
  have right: "filter_labeled_by (S \<union> T) \<Gamma> \<turnstile> B"
    by (rule weakening[OF right0 filter_labeled_by_union_right])
  have "filter_labeled_by (S \<union> T) \<Gamma> \<turnstile> Con A B"
    by (rule derives.ConI[OF left right])
  then show ?case
    by simp
next
  case (PConE1 \<Gamma> S A B)
  then show ?case
    by (auto intro: derives.ConE1)
next
  case (PConE2 \<Gamma> S A B)
  then show ?case
    by (auto intro: derives.ConE2)
next
  case (PDisI1 \<Gamma> S A B)
  then show ?case
    by (auto intro: derives.DisI1)
next
  case (PDisI2 \<Gamma> S B A)
  then show ?case
    by (auto intro: derives.DisI2)
next
  case (PDisE \<Gamma> S A B M N C P Q)
  let ?U = "S \<union> (N - M) \<union> (Q - P)"
  have ne_left: "nonempty_prov_ctx ((M, A) # \<Gamma>)"
    using PDisE by simp
  have ne_right: "nonempty_prov_ctx ((P, B) # \<Gamma>)"
    using PDisE by simp
  have disj0: "filter_labeled_by S \<Gamma> \<turnstile> Dis A B"
    using PDisE.IH(1)[OF PDisE.prems] by simp
  have left0: "filter_labeled_by N ((M, A) # \<Gamma>) \<turnstile> C"
    using PDisE.IH(2)[OF ne_left] by simp
  have right0: "filter_labeled_by Q ((P, B) # \<Gamma>) \<turnstile> C"
    using PDisE.IH(3)[OF ne_right] by simp
  have disj_sub: "set (filter_labeled_by S \<Gamma>) \<subseteq>
      set (filter_labeled_by ?U \<Gamma>)"
    by (rule filter_labeled_by_mono) auto
  have disj: "filter_labeled_by ?U \<Gamma> \<turnstile> Dis A B"
    by (rule weakening[OF disj0 disj_sub])
  have left_sub: "set (filter_labeled_by N ((M, A) # \<Gamma>)) \<subseteq>
      set (A # filter_labeled_by ?U \<Gamma>)"
    using PDisE
    by (intro filter_labeled_by_cons_minus_mono_subset) auto
  have left: "A # filter_labeled_by ?U \<Gamma> \<turnstile> C"
    by (rule weakening[OF left0 left_sub])
  have right_sub: "set (filter_labeled_by Q ((P, B) # \<Gamma>)) \<subseteq>
      set (B # filter_labeled_by ?U \<Gamma>)"
    using PDisE
    by (intro filter_labeled_by_cons_minus_mono_subset) auto
  have right: "B # filter_labeled_by ?U \<Gamma> \<turnstile> C"
    by (rule weakening[OF right0 right_sub])
  have "filter_labeled_by ?U \<Gamma> \<turnstile> C"
    by (rule derives.DisE[OF disj left right])
  then show ?case
    by simp
qed

theorem provenance_drop_unused:
  assumes "indexed 0 \<Gamma>0 \<turnstile>P (S, A)"
  shows "filter_indexed_by S \<Gamma>0 \<turnstile> A"
proof -
  have "filter_labeled_by S (indexed 0 \<Gamma>0) \<turnstile> A"
    using provenance_drop_unused_general[OF assms] by simp
  then show ?thesis
    by (simp add: filter_labeled_by_indexed_0)
qed

lemma fresh_nat:
  assumes "finite F"
  obtains i :: nat where "i \<notin> F"
proof -
  have "\<exists>i :: nat. i \<notin> F"
    using assms ex_new_if_finite[OF infinite_UNIV_nat] by blast
  then show ?thesis
    using that by blast
qed

lemma fresh_nat2:
  assumes "finite F"
  obtains i j :: nat where "i \<notin> F" and "j \<notin> F" and "i \<noteq> j"
proof -
  obtain i where i: "i \<notin> F"
    using assms by (rule fresh_nat)
  from assms have "finite (insert i F)"
    by simp
  then obtain j where j: "j \<notin> insert i F"
    by (rule fresh_nat)
  from j have "j \<notin> F" and "i \<noteq> j"
    by auto
  with i show ?thesis
    by (rule that)
qed

lemma ordinary_admits_safe_provenance_labeled:
  assumes "\<Delta> \<turnstile> A"
    and "erase_ctx \<Gamma> = \<Delta>"
    and "nonempty_prov_ctx \<Gamma>"
    and "finite (ctx_prov \<Gamma>)"
  shows "\<exists>S. \<Gamma> \<turnstile>P (S, A) \<and> S \<subseteq> ctx_prov \<Gamma>"
  using assms
proof (induction arbitrary: \<Gamma> rule: derives.induct)
  case (Assm A \<Delta>)
  then have "A \<in> set (erase_ctx \<Gamma>)"
    by simp
  then obtain S where in_ctx: "(S, A) \<in> set \<Gamma>"
    by (rule erase_ctx_mem_label)
  have "\<Gamma> \<turnstile>P (S, A)"
    using in_ctx by (rule prov_safe.PAssm)
  moreover have "S \<subseteq> ctx_prov \<Gamma>"
    using in_ctx by (rule ctx_prov_contains_label)
  ultimately show ?case
    by blast
next
  case (BotE \<Delta> A)
  then obtain S where deriv: "\<Gamma> \<turnstile>P (S, Bot)"
    and sub: "S \<subseteq> ctx_prov \<Gamma>"
    by blast
  have "\<Gamma> \<turnstile>P (S, A)"
    by (rule prov_safe.PBotE[OF deriv])
  with sub show ?case
    by blast
next
  case (ImpI A \<Delta> B)
  obtain i where fresh: "i \<notin> ctx_prov \<Gamma>"
    using ImpI.prems(3) by (rule fresh_nat)
  let ?M = "{i}"
  have erase: "erase_ctx ((?M, A) # \<Gamma>) = A # \<Delta>"
    using ImpI.prems(1) by simp
  have nonempty: "nonempty_prov_ctx ((?M, A) # \<Gamma>)"
    using ImpI.prems(2) by simp
  have finite: "finite (ctx_prov ((?M, A) # \<Gamma>))"
    using ImpI.prems(3) by simp
  obtain N where body: "(?M, A) # \<Gamma> \<turnstile>P (N, B)"
    and sub_body: "N \<subseteq> ctx_prov ((?M, A) # \<Gamma>)"
    using ImpI.IH[OF erase nonempty finite] by blast
  have deriv: "\<Gamma> \<turnstile>P (N - ?M, Imp A B)"
    by (rule prov_safe.PImpI[OF body]) (use fresh in auto)
  have "N - ?M \<subseteq> ctx_prov \<Gamma>"
    using sub_body fresh by auto
  with deriv show ?case
    by blast
next
  case (ImpE \<Delta> A B)
  obtain S where imp: "\<Gamma> \<turnstile>P (S, Imp A B)"
    and sub_imp: "S \<subseteq> ctx_prov \<Gamma>"
    using ImpE.IH(1)[OF ImpE.prems] by blast
  obtain T where arg: "\<Gamma> \<turnstile>P (T, A)"
    and sub_arg: "T \<subseteq> ctx_prov \<Gamma>"
    using ImpE.IH(2)[OF ImpE.prems] by blast
  have "\<Gamma> \<turnstile>P (S \<union> T, B)"
    by (rule prov_safe.PImpE[OF imp arg])
  moreover have "S \<union> T \<subseteq> ctx_prov \<Gamma>"
    using sub_imp sub_arg by auto
  ultimately show ?case
    by blast
next
  case (ConI \<Delta> A B)
  obtain S where left: "\<Gamma> \<turnstile>P (S, A)"
    and sub_left: "S \<subseteq> ctx_prov \<Gamma>"
    using ConI.IH(1)[OF ConI.prems] by blast
  obtain T where right: "\<Gamma> \<turnstile>P (T, B)"
    and sub_right: "T \<subseteq> ctx_prov \<Gamma>"
    using ConI.IH(2)[OF ConI.prems] by blast
  have "\<Gamma> \<turnstile>P (S \<union> T, Con A B)"
    by (rule prov_safe.PConI[OF left right])
  moreover have "S \<union> T \<subseteq> ctx_prov \<Gamma>"
    using sub_left sub_right by auto
  ultimately show ?case
    by blast
next
  case (ConE1 \<Delta> A B)
  then obtain S where deriv: "\<Gamma> \<turnstile>P (S, Con A B)"
    and sub: "S \<subseteq> ctx_prov \<Gamma>"
    by blast
  have "\<Gamma> \<turnstile>P (S, A)"
    by (rule prov_safe.PConE1[OF deriv])
  with sub show ?case
    by blast
next
  case (ConE2 \<Delta> A B)
  then obtain S where deriv: "\<Gamma> \<turnstile>P (S, Con A B)"
    and sub: "S \<subseteq> ctx_prov \<Gamma>"
    by blast
  have "\<Gamma> \<turnstile>P (S, B)"
    by (rule prov_safe.PConE2[OF deriv])
  with sub show ?case
    by blast
next
  case (DisI1 \<Delta> A B)
  then obtain S where deriv: "\<Gamma> \<turnstile>P (S, A)"
    and sub: "S \<subseteq> ctx_prov \<Gamma>"
    by blast
  have "\<Gamma> \<turnstile>P (S, Dis A B)"
    by (rule prov_safe.PDisI1[OF deriv])
  with sub show ?case
    by blast
next
  case (DisI2 \<Delta> B A)
  then obtain S where deriv: "\<Gamma> \<turnstile>P (S, B)"
    and sub: "S \<subseteq> ctx_prov \<Gamma>"
    by blast
  have "\<Gamma> \<turnstile>P (S, Dis A B)"
    by (rule prov_safe.PDisI2[OF deriv])
  with sub show ?case
    by blast
next
  case (DisE \<Delta> A B C)
  obtain i j where fresh_i: "i \<notin> ctx_prov \<Gamma>"
    and fresh_j: "j \<notin> ctx_prov \<Gamma>"
    and neq: "i \<noteq> j"
    using DisE.prems(3) by (rule fresh_nat2)
  let ?M = "{i}"
  let ?P = "{j}"
  obtain S where disj: "\<Gamma> \<turnstile>P (S, Dis A B)"
    and sub_disj: "S \<subseteq> ctx_prov \<Gamma>"
    using DisE.IH(1)[OF DisE.prems] by blast
  have erase_left: "erase_ctx ((?M, A) # \<Gamma>) = A # \<Delta>"
    using DisE.prems(1) by simp
  have nonempty_left: "nonempty_prov_ctx ((?M, A) # \<Gamma>)"
    using DisE.prems(2) by simp
  have finite_left: "finite (ctx_prov ((?M, A) # \<Gamma>))"
    using DisE.prems(3) by simp
  obtain N where left: "(?M, A) # \<Gamma> \<turnstile>P (N, C)"
    and sub_left: "N \<subseteq> ctx_prov ((?M, A) # \<Gamma>)"
    using DisE.IH(2)[OF erase_left nonempty_left finite_left] by blast
  have erase_right: "erase_ctx ((?P, B) # \<Gamma>) = B # \<Delta>"
    using DisE.prems(1) by simp
  have nonempty_right: "nonempty_prov_ctx ((?P, B) # \<Gamma>)"
    using DisE.prems(2) by simp
  have finite_right: "finite (ctx_prov ((?P, B) # \<Gamma>))"
    using DisE.prems(3) by simp
  obtain Q where right: "(?P, B) # \<Gamma> \<turnstile>P (Q, C)"
    and sub_right: "Q \<subseteq> ctx_prov ((?P, B) # \<Gamma>)"
    using DisE.IH(3)[OF erase_right nonempty_right finite_right] by blast
  have deriv: "\<Gamma> \<turnstile>P (S \<union> (N - ?M) \<union> (Q - ?P), C)"
    by (rule prov_safe.PDisE[OF disj left right]) (use fresh_i fresh_j neq in auto)
  have "S \<union> (N - ?M) \<union> (Q - ?P) \<subseteq> ctx_prov \<Gamma>"
    using sub_disj sub_left sub_right fresh_i fresh_j by auto
  with deriv show ?case
    by blast
qed

theorem ordinary_admits_safe_provenance:
  assumes "\<Gamma> \<turnstile> A"
  shows "\<exists>S. (indexed 0 \<Gamma> \<turnstile>P (S, A))
            \<and> S \<subseteq> {0..<length \<Gamma>}
            \<and> set (filter_indexed_by S \<Gamma>) \<subseteq> set \<Gamma>"
proof -
  obtain S where deriv: "indexed 0 \<Gamma> \<turnstile>P (S, A)"
    and sub_ctx: "S \<subseteq> ctx_prov (indexed 0 \<Gamma>)"
    using ordinary_admits_safe_provenance_labeled[OF assms, of "indexed 0 \<Gamma>"]
    by simp blast
  have sub_indices: "S \<subseteq> {0..<length \<Gamma>}"
  proof
    fix i
    assume "i \<in> S"
    then have "i \<in> ctx_prov (indexed 0 \<Gamma>)"
      using sub_ctx by auto
    then have "i < length \<Gamma>"
      using ctx_prov_indexed_bound[of i 0 \<Gamma>] by simp
    then show "i \<in> {0..<length \<Gamma>}"
      by simp
  qed
  have "set (filter_indexed_by S \<Gamma>) \<subseteq> set \<Gamma>"
    by (rule filter_indexed_by_subset_ctx)
  with deriv sub_indices show ?thesis
    by blast
qed

corollary ordinary_admits_tight_provenance:
  assumes "\<Gamma> \<turnstile> A"
  shows "\<exists>S. (indexed 0 \<Gamma> \<turnstile>P (S, A))
            \<and> S \<subseteq> {0..<length \<Gamma>}
            \<and> filter_indexed_by S \<Gamma> \<turnstile> A"
proof -
  obtain S where deriv: "indexed 0 \<Gamma> \<turnstile>P (S, A)"
    and sub: "S \<subseteq> {0..<length \<Gamma>}"
    using ordinary_admits_safe_provenance[OF assms] by blast
  have "filter_indexed_by S \<Gamma> \<turnstile> A"
    by (rule provenance_drop_unused[OF deriv])
  with deriv sub show ?thesis
    by blast
qed

theorem provenance_completeness:
  shows "(\<Gamma> \<turnstile> A) \<longleftrightarrow>
         (\<exists>S. (indexed 0 \<Gamma> \<turnstile>P (S, A)) \<and> filter_indexed_by S \<Gamma> \<turnstile> A)"
proof
  assume "\<Gamma> \<turnstile> A"
  then show "\<exists>S. (indexed 0 \<Gamma> \<turnstile>P (S, A)) \<and> filter_indexed_by S \<Gamma> \<turnstile> A"
    using ordinary_admits_tight_provenance by blast
next
  assume "\<exists>S. (indexed 0 \<Gamma> \<turnstile>P (S, A)) \<and> filter_indexed_by S \<Gamma> \<turnstile> A"
  then obtain S where deriv: "indexed 0 \<Gamma> \<turnstile>P (S, A)"
    by blast
  have "filter_indexed_by S \<Gamma> \<turnstile> A"
    by (rule provenance_drop_unused[OF deriv])
  moreover have "set (filter_indexed_by S \<Gamma>) \<subseteq> set \<Gamma>"
    by (rule filter_indexed_by_subset_ctx)
  ultimately show "\<Gamma> \<turnstile> A"
    by (rule weakening)
qed

end
