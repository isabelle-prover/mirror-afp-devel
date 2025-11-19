(* Authors: Fabian Lehr *)

section \<open>Parikh images\<close>

theory Parikh_Img
  imports 
    "Reg_Lang_Exp"
    "HOL-Library.Multiset"
begin


subsection \<open>Definition and basic lemmas\<close>

text \<open>The Parikh vector of a finite word describes how often each symbol of the alphabet occurs in the word.
We represent parikh vectors by multisets. The Parikh image of a language \<open>L\<close>, denoted by \<open>\<Psi> L\<close>,
is then the set of Parikh vectors of all words in the language.\<close>

definition parikh_img :: "'a lang \<Rightarrow> 'a multiset set" where
  "parikh_img L \<equiv> mset ` L"

notation parikh_img ("\<Psi>")

lemma parikh_img_Un [simp]: "\<Psi> (L1 \<union> L2) = \<Psi> L1 \<union> \<Psi> L2"
  by (auto simp add: parikh_img_def)

lemma parikh_img_UNION: "\<Psi> (\<Union>(L ` I)) = \<Union> ((\<lambda>i. \<Psi> (L i)) ` I)"
  by (auto simp add: parikh_img_def)

lemma parikh_img_conc: "\<Psi> (L1 @@ L2) = { m1 + m2 | m1 m2. m1 \<in> \<Psi> L1 \<and> m2 \<in> \<Psi> L2 }"
  unfolding parikh_img_def by force

lemma parikh_img_commut: "\<Psi> (L1 @@ L2) = \<Psi> (L2 @@ L1)"
proof -
  have "{ m1 + m2 | m1 m2. m1 \<in> \<Psi> L1 \<and> m2 \<in> \<Psi> L2 } = 
        { m2 + m1 | m1 m2. m1 \<in> \<Psi> L1 \<and> m2 \<in> \<Psi> L2 }"
    using add.commute by blast
  then show ?thesis
    using parikh_img_conc[of L1] parikh_img_conc[of L2] by auto
qed


subsection \<open>Monotonicity properties\<close>

lemma parikh_img_mono: "A \<subseteq> B \<Longrightarrow> \<Psi> A \<subseteq> \<Psi> B"
  unfolding parikh_img_def by fast

lemma parikh_conc_right_subset: "\<Psi> A \<subseteq> \<Psi> B \<Longrightarrow> \<Psi> (A @@ C) \<subseteq> \<Psi> (B @@ C)"
  by (auto simp add: parikh_img_conc)

lemma parikh_conc_left_subset: "\<Psi> A \<subseteq> \<Psi> B \<Longrightarrow> \<Psi> (C @@ A) \<subseteq> \<Psi> (C @@ B)"
  by (auto simp add: parikh_img_conc)

lemma parikh_conc_subset:
  assumes "\<Psi> A \<subseteq> \<Psi> C"
      and "\<Psi> B \<subseteq> \<Psi> D"
    shows "\<Psi> (A @@ B) \<subseteq> \<Psi> (C @@ D)"
  using assms parikh_conc_right_subset parikh_conc_left_subset by blast

lemma parikh_conc_right: "\<Psi> A = \<Psi> B \<Longrightarrow> \<Psi> (A @@ C) = \<Psi> (B @@ C)"
  by (auto simp add: parikh_img_conc)

lemma parikh_conc_left: "\<Psi> A = \<Psi> B \<Longrightarrow> \<Psi> (C @@ A) = \<Psi> (C @@ B)"
  by (auto simp add: parikh_img_conc)

lemma parikh_pow_mono: "\<Psi> A \<subseteq> \<Psi> B \<Longrightarrow> \<Psi> (A ^^ n) \<subseteq> \<Psi> (B ^^ n)"
  by (induction n) (auto simp add: parikh_img_conc)


lemma parikh_star_mono:
  assumes "\<Psi> A \<subseteq> \<Psi> B"
  shows "\<Psi> (star A) \<subseteq> \<Psi> (star B)"
proof
  fix v
  assume "v \<in> \<Psi> (star A)"
  then obtain w where w_intro: "mset w = v \<and> w \<in> star A" unfolding parikh_img_def by blast
  then obtain n where "w \<in> A ^^ n" unfolding star_def by blast
  then have "v \<in> \<Psi> (A ^^ n)" using w_intro unfolding parikh_img_def by blast
  with assms have "v \<in> \<Psi> (B ^^ n)" using parikh_pow_mono by blast
  then show "v \<in> \<Psi> (star B)" unfolding star_def using parikh_img_UNION by fastforce
qed

lemma parikh_star_mono_eq:
  assumes "\<Psi> A = \<Psi> B"
  shows "\<Psi> (star A) = \<Psi> (star B)"
  using parikh_star_mono by (metis Orderings.order_eq_iff assms)


lemma parikh_img_subst_mono:
  assumes "\<forall>i. \<Psi> (eval (A i) v) \<subseteq> \<Psi> (eval (B i) v)"
  shows "\<Psi> (eval (subst A f) v) \<subseteq> \<Psi> (eval (subst B f) v)"
proof (induction f)
  case (Concat f1 f2)
  then have "\<Psi> (eval (subst A f1) v @@ eval (subst A f2) v)
              \<subseteq> \<Psi> (eval (subst B f1) v @@ eval (subst B f2) v)"
    using parikh_conc_subset by blast
  then show ?case by simp
next
  case (Star f)
  then have "\<Psi> (star (eval (subst A f) v)) \<subseteq> \<Psi> (star (eval (subst B f) v))"
    using parikh_star_mono by blast
  then show ?case by simp
qed (use assms(1) in auto)

lemma parikh_img_subst_mono_upd:
  assumes "\<Psi> (eval A v) \<subseteq> \<Psi> (eval B v)"
  shows "\<Psi> (eval (subst (Var(x := A)) f) v) \<subseteq> \<Psi> (eval (subst (Var(x := B)) f) v)"
  using parikh_img_subst_mono[of "Var(x := A)" v "Var(x := B)"] assms by auto

lemma rlexp_mono_parikh:
  assumes "\<forall>i \<in> vars f. \<Psi> (v i) \<subseteq> \<Psi> (v' i)"
  shows "\<Psi> (eval f v) \<subseteq> \<Psi> (eval f v')"
using assms proof (induction f rule: rlexp.induct)
case (Concat f1 f2)
  then have "\<Psi> (eval f1 v @@ eval f2 v) \<subseteq> \<Psi> (eval f1 v' @@ eval f2 v')"
    using parikh_conc_subset by (metis UnCI vars.simps(4))
  then show ?case by simp
qed (auto simp add: SUP_mono' parikh_img_UNION parikh_star_mono)

lemma rlexp_mono_parikh_eq:
  assumes "\<forall>i \<in> vars f. \<Psi> (v i) = \<Psi> (v' i)"
  shows "\<Psi> (eval f v) = \<Psi> (eval f v')"
  using assms rlexp_mono_parikh by blast



subsection \<open>$\Psi \; (A \cup B)^* = \Psi \; A^* B^*$\<close>

text \<open>\label{sec:parikh_img_star}\<close>
text \<open>This property is claimed by Pilling in \<^cite>\<open>Pilling\<close> and will be needed later.\<close>

lemma parikh_img_union_pow_aux1:
  assumes "v \<in> \<Psi> ((A \<union> B) ^^ n)"
    shows "v \<in> \<Psi> (\<Union>i \<le> n. A ^^ i @@ B ^^ (n-i))"
using assms proof (induction n arbitrary: v)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain w where w_intro: "w \<in> (A \<union> B) ^^ (Suc n) \<and> mset w = v"
    unfolding parikh_img_def by auto
  then obtain w1 w2 where w1_w2_intro: "w = w1@w2 \<and> w1 \<in> A \<union> B \<and> w2 \<in> (A \<union> B) ^^ n" by fastforce
  let ?v1 = "mset w1" and ?v2 = "mset w2"
  from w1_w2_intro have "?v2 \<in> \<Psi> ((A \<union> B) ^^ n)" unfolding parikh_img_def by blast
  with Suc.IH have "?v2 \<in> \<Psi> (\<Union>i \<le> n. A ^^ i @@ B ^^ (n-i))" by auto
  then obtain w2' where w2'_intro: "mset w2' = mset w2 \<and>
      w2' \<in> (\<Union>i \<le> n. A ^^ i @@ B ^^ (n-i))" unfolding parikh_img_def by fastforce
  then obtain i where i_intro: "i \<le> n \<and> w2' \<in> A ^^ i @@ B ^^ (n-i)" by blast
  from w1_w2_intro w2'_intro have "mset w = mset (w1@w2')"
    by simp
  moreover have "mset (w1@w2') \<in> \<Psi> (\<Union>i \<le> Suc n. A ^^ i @@ B ^^ (Suc n-i))"
  proof (cases "w1 \<in> A")
    case True
    with i_intro have Suc_i_valid: "Suc i \<le> Suc n" and "w1@w2' \<in> A ^^ (Suc i) @@ B ^^ (Suc n - Suc i)"
      by (auto simp add: conc_assoc)
    then have "mset (w1@w2') \<in> \<Psi> (A ^^ (Suc i) @@ B ^^ (Suc n - Suc i))"
      unfolding parikh_img_def by blast
    with Suc_i_valid parikh_img_UNION show ?thesis by fast
  next
    case False
    with w1_w2_intro have "w1 \<in> B" by blast
    with i_intro have "mset (w1@w2') \<in> \<Psi> (B @@ A ^^ i @@ B ^^ (n-i))"
      unfolding parikh_img_def by blast
    then have "mset (w1@w2') \<in> \<Psi> (A ^^ i @@ B ^^ (Suc n-i))"
      using parikh_img_commut conc_assoc
      by (metis Suc_diff_le conc_pow_comm i_intro lang_pow.simps(2))
    with i_intro parikh_img_UNION show ?thesis by fastforce
  qed
  ultimately show ?case using w_intro by auto
qed

lemma parikh_img_star_aux1:
  assumes "v \<in> \<Psi> (star (A \<union> B))"
  shows "v \<in> \<Psi> (star A @@ star B)"
proof -
  from assms have "v \<in> (\<Union>n. \<Psi> ((A \<union> B) ^^ n))"
    unfolding star_def using parikh_img_UNION by metis
  then obtain n where "v \<in> \<Psi> ((A \<union> B) ^^ n)" by blast
  then have "v \<in> \<Psi> (\<Union>i \<le> n. A ^^ i @@ B ^^ (n-i))"
    using parikh_img_union_pow_aux1 by auto
  then have "v \<in> (\<Union>i\<le>n. \<Psi> (A ^^ i @@ B ^^ (n-i)))" using parikh_img_UNION by metis
  then obtain i where "i\<le>n \<and> v \<in> \<Psi> (A ^^ i @@ B ^^ (n-i))" by blast
  then obtain w where w_intro: "mset w = v \<and> w \<in> A ^^ i @@ B ^^ (n-i)"
    unfolding parikh_img_def by blast
  then obtain w1 w2 where w_decomp: "w=w1@w2 \<and> w1 \<in> A ^^ i \<and> w2 \<in> B ^^ (n-i)" by blast
  then have "w1 \<in> star A" and "w2 \<in> star B" by auto
  with w_decomp have "w \<in> star A @@ star B" by auto
  with w_intro show ?thesis unfolding parikh_img_def by blast
qed

lemma parikh_img_star_aux2:
  assumes "v \<in> \<Psi> (star A @@ star B)"
  shows "v \<in> \<Psi> (star (A \<union> B))"
proof -
  from assms obtain w where w_intro: "mset w = v \<and> w \<in> star A @@ star B"
    unfolding parikh_img_def by blast
  then obtain w1 w2 where w_decomp: "w=w1@w2 \<and> w1 \<in> star A \<and> w2 \<in> star B" by blast
  then obtain i j where "w1 \<in> A ^^ i" and w2_intro: "w2 \<in> B ^^ j" unfolding star_def by blast
  then have w1_in_union: "w1 \<in> (A \<union> B) ^^ i" using lang_pow_mono by blast
  from w2_intro have "w2 \<in> (A \<union> B) ^^ j" using lang_pow_mono by blast
  with w1_in_union w_decomp have "w \<in> (A \<union> B) ^^ (i+j)" using lang_pow_add by fast
  with w_intro show ?thesis unfolding parikh_img_def by auto
qed

lemma parikh_img_star: "\<Psi> (star (A \<union> B)) = \<Psi> (star A @@ star B)"
proof
  show "\<Psi> (star (A \<union> B)) \<subseteq> \<Psi> (star A @@ star B)" using parikh_img_star_aux1 by auto
  show "\<Psi> (star A @@ star B) \<subseteq> \<Psi> (star (A \<union> B))" using parikh_img_star_aux2 by auto
qed



subsection \<open>$\Psi \; (E^* F)^* = \Psi \; \left(\{\varepsilon\} \cup E^* F^* F\right)$\<close>

text \<open>\label{sec:parikh_img_star2}\<close>
text \<open>This property (where $\varepsilon$ denotes the empty word) is claimed by
Pilling as well \<^cite>\<open>Pilling\<close>; we will use it later.\<close>

(* It even holds = but \<subseteq> suffices for the proof *)
lemma parikh_img_conc_pow: "\<Psi> ((A @@ B) ^^ n) \<subseteq> \<Psi> (A ^^ n @@ B ^^ n)"
proof (induction n)
  case (Suc n)
  then have "\<Psi> ((A @@ B) ^^ n @@ A @@ B) \<subseteq> \<Psi> (A ^^ n @@ B ^^ n @@ A @@ B)"
    using parikh_conc_right_subset conc_assoc by metis
  also have "\<dots> = \<Psi> (A ^^ n @@ A @@ B ^^ n @@ B)"
    by (metis parikh_img_commut conc_assoc parikh_conc_left)
  finally show ?case by (simp add: conc_assoc conc_pow_comm)
qed simp

lemma parikh_img_conc_star: "\<Psi> (star (A @@ B)) \<subseteq> \<Psi> (star A @@ star B)"
proof
  fix v
  assume "v \<in> \<Psi> (star (A @@ B))"
  then have "\<exists>n. v \<in> \<Psi> ((A @@ B) ^^ n)" unfolding star_def by (simp add: parikh_img_UNION)
  then obtain n where "v \<in> \<Psi> ((A @@ B) ^^ n)" by blast
  with parikh_img_conc_pow have "v \<in> \<Psi> (A ^^ n @@ B ^^ n)" by fast
  then have "v \<in> \<Psi> (A ^^ n @@ star B)"
    unfolding star_def using parikh_conc_left_subset
    by (metis (no_types, lifting) Sup_upper parikh_img_mono rangeI subset_eq)
  then show "v \<in> \<Psi> (star A @@ star B)"
    unfolding star_def using parikh_conc_right_subset
    by (metis (no_types, lifting) Sup_upper parikh_img_mono rangeI subset_eq)
qed

lemma parikh_img_conc_pow2: "\<Psi> ((A @@ B) ^^ Suc n) \<subseteq> \<Psi> (star A @@ star B @@ B)"
proof
  fix v
  assume "v \<in> \<Psi> ((A @@ B) ^^ Suc n)"
  with parikh_img_conc_pow have "v \<in> \<Psi> (A ^^ Suc n @@ B ^^ n @@ B)"
    by (metis conc_pow_comm lang_pow.simps(2) subsetD)
  then have "v \<in> \<Psi> (star A @@ B ^^ n @@ B)"
    unfolding star_def using parikh_conc_right_subset
    by (metis (no_types, lifting) Sup_upper parikh_img_mono rangeI subset_eq)
  then show "v \<in> \<Psi> (star A @@ star B @@ B)"
    unfolding star_def using parikh_conc_right_subset parikh_conc_left_subset
    by (metis (no_types, lifting) Sup_upper parikh_img_mono rangeI subset_eq)
qed

lemma parikh_img_star2_aux1:
  "\<Psi> (star (star E @@ F)) \<subseteq> \<Psi> ({[]} \<union> star E @@ star F @@ F)"
proof
  fix v
  assume "v \<in> \<Psi> (star (star E @@ F))"
  then have "\<exists>n. v \<in> \<Psi> ((star E @@ F) ^^ n)"
    unfolding star_def by (simp add: parikh_img_UNION)
  then obtain n where v_in_pow_n: "v \<in> \<Psi> ((star E @@ F) ^^ n)" by blast
  show "v \<in> \<Psi> ({[]} \<union> star E @@ star F @@ F)"
  proof (cases n)
    case 0
    with v_in_pow_n have "v = mset []" unfolding parikh_img_def by simp
    then show ?thesis unfolding parikh_img_def by blast
  next
    case (Suc m)
    with parikh_img_conc_pow2 v_in_pow_n have "v \<in> \<Psi> (star (star E) @@ star F @@ F)" by blast
    then show ?thesis by (metis UnCI parikh_img_Un star_idemp)
  qed
qed

lemma parikh_img_star2_aux2: "\<Psi> (star E @@ star F @@ F) \<subseteq> \<Psi> (star (star E @@ F))"
proof -
  have "F \<subseteq> star E @@ F" unfolding star_def using Nil_in_star
    by (metis concI_if_Nil1 star_def subsetI)
  then have "\<Psi> (star E @@ F @@ star F) \<subseteq> \<Psi> (star E @@ F @@ star (star E @@ F))"
    using parikh_conc_left_subset parikh_img_mono parikh_star_mono by meson
  also have "\<dots> \<subseteq> \<Psi> (star (star E @@ F))"
    by (metis conc_assoc inf_sup_ord(3) parikh_img_mono star_unfold_left)
  finally show ?thesis using conc_star_comm by metis
qed

lemma parikh_img_star2: "\<Psi> (star (star E @@ F)) = \<Psi> ({[]} \<union> star E @@ star F @@ F)"
proof
  from parikh_img_star2_aux1
    show "\<Psi> (star (star E @@ F)) \<subseteq> \<Psi> ({[]} \<union> star E @@ star F @@ F)" .
  from parikh_img_star2_aux2
    show "\<Psi> ({[]} \<union> star E @@ star F @@ F) \<subseteq> \<Psi> (star (star E @@ F))"
    by (metis le_sup_iff parikh_img_Un star_unfold_left sup.cobounded2)
qed



subsection \<open>A homogeneous-like property for regular language expressions\<close>

text \<open>\label{sec:rlexp_homogeneous}\<close>

lemma rlexp_homogeneous_aux:
  assumes "v x = star Y @@ Z"
    shows "\<Psi> (eval f v) \<subseteq> \<Psi> (star Y @@ eval f (v(x := Z)))"
proof (induction f)
  case (Var y)
  show ?case
  proof (cases "x = y")
    case True
    with Var assms show ?thesis by simp
  next
    case False
    have "eval (Var y) v \<subseteq> star Y @@ eval (Var y) v" by (metis Nil_in_star concI_if_Nil1 subsetI)
    with False parikh_img_mono show ?thesis by auto
  qed
next
  case (Const l)
  have "eval (Const l) v \<subseteq> star Y @@ eval (Const l) v" using concI_if_Nil1 by blast
  then show ?case by (simp add: parikh_img_mono)
next
  case (Union f g)
  then have "\<Psi> (eval (Union f g) v) \<subseteq> \<Psi> (star Y @@ eval f (v(x := Z)) \<union>
                                                            star Y @@ eval g (v(x := Z)))"
    by (metis eval.simps(3) parikh_img_Un sup.mono)
  then show ?case by (metis conc_Un_distrib(1) eval.simps(3))
next
  case (Concat f g)
  then have "\<Psi> (eval (Concat f g) v) \<subseteq> \<Psi> ((star Y @@ eval f (v(x := Z)))
                                                          @@ star Y @@ eval g (v(x := Z)))"
    by (metis eval.simps(4) parikh_conc_subset)
  also have "\<dots> = \<Psi> (star Y @@ star Y @@ eval f (v(x := Z)) @@ eval g (v(x := Z)))"
    by (metis conc_assoc parikh_conc_right parikh_img_commut)
  also have "\<dots> = \<Psi> (star Y @@ eval f (v(x := Z)) @@ eval g (v(x := Z)))"
    by (metis conc_assoc conc_star_star)
  finally show ?case by (metis eval.simps(4))
next
  case (Star f)
  then have "\<Psi> (star (eval f v)) \<subseteq> \<Psi> (star (star Y @@ eval f (v(x := Z))))"
    using parikh_star_mono by metis
  also from parikh_img_conc_star have "\<dots> \<subseteq> \<Psi> (star Y @@ star (eval f (v(x := Z))))"
    by fastforce
  finally show ?case by (metis eval.simps(5))
qed

text \<open>Now we can prove the desired homogeneous-like property which will become useful later.
Notably this property slightly differs from the property claimed in \<^cite>\<open>Pilling\<close>. However, our
property is easier to prove formally and it suffices for the rest of the proof.\<close>
lemma rlexp_homogeneous:  "\<Psi> (eval (subst (Var(x := Concat (Star y) z)) f) v)
                          \<subseteq> \<Psi> (eval (Concat (Star y) (subst (Var(x := z)) f)) v)"
                          (is "\<Psi> ?L \<subseteq> \<Psi> ?R")
proof -
  let ?v' = "v(x := star (eval y v) @@ eval z v)"
  have "\<Psi> ?L = \<Psi> (eval f ?v')" using substitution_lemma_upd[where f=f] by simp
  also have "\<dots> \<subseteq> \<Psi> (star (eval y v) @@ eval f (?v'(x := eval z v)))"
    using rlexp_homogeneous_aux[of ?v'] unfolding fun_upd_def by auto
  also have "\<dots> = \<Psi> ?R" using substitution_lemma[of "v(x := eval z v)"] by simp
  finally show ?thesis .
qed


subsection \<open>Extension of Arden's lemma to Parikh images\<close>

text \<open>\label{sec:parikh_arden}\<close>

lemma parikh_img_arden_aux:
  assumes "\<Psi> (A @@ X \<union> B) \<subseteq> \<Psi> X"
  shows "\<Psi> (A ^^ n @@ B) \<subseteq> \<Psi> X"
proof (induction n)
  case 0
  with assms show ?case by auto
next
  case (Suc n)
  then have "\<Psi> (A ^^ (Suc n) @@ B) \<subseteq> \<Psi> (A @@ A ^^ n @@B)"
    by (simp add: conc_assoc)
  moreover from Suc parikh_conc_left have "\<dots> \<subseteq> \<Psi> (A @@ X)"
    by (metis conc_Un_distrib(1) parikh_img_Un sup.orderE sup.orderI)
  moreover from Suc.prems assms have "\<dots> \<subseteq> \<Psi> X" by auto
  ultimately show ?case by fast
qed

lemma parikh_img_arden:
  assumes "\<Psi> (A @@ X \<union> B) \<subseteq> \<Psi> X"
  shows "\<Psi> (star A @@ B) \<subseteq> \<Psi> X"
proof
  fix x
  assume "x \<in> \<Psi> (star A @@ B)"
  then have "\<exists>n. x \<in> \<Psi> (A ^^ n @@ B)"
    unfolding star_def by (simp add: conc_UNION_distrib(2) parikh_img_UNION)
  then obtain n where "x \<in> \<Psi> (A ^^ n @@ B)" by blast
  then show "x \<in> \<Psi> X" using parikh_img_arden_aux[OF assms] by fast
qed


subsection \<open>Equivalence class of languages with identical Parikh image\<close>

text \<open>\label{sec:parikh_eq_class}\<close>
text \<open>For a given language \<open>L\<close>, we define the equivalence class of all languages with identical Parikh
image:\<close>

definition parikh_img_eq_class :: "'a lang \<Rightarrow> 'a lang set" where
  "parikh_img_eq_class L \<equiv> {L'. \<Psi> L' = \<Psi> L}"

lemma parikh_img_Union_class: "\<Psi> A = \<Psi> (\<Union>(parikh_img_eq_class A))"
proof
  let ?A' = "\<Union>(parikh_img_eq_class A)"
  show "\<Psi> A \<subseteq> \<Psi> ?A'"
    unfolding parikh_img_eq_class_def by (simp add: Union_upper parikh_img_mono)
  show "\<Psi> ?A' \<subseteq> \<Psi> A"
  proof
    fix v
    assume "v \<in> \<Psi> ?A'"
    then obtain a where a_intro: "mset a = v \<and> a \<in> ?A'"
      unfolding parikh_img_def by blast
    then obtain L where L_intro: "a \<in> L \<and> L \<in> parikh_img_eq_class A"
      unfolding parikh_img_eq_class_def by blast
    then have "\<Psi> L = \<Psi> A" unfolding parikh_img_eq_class_def by fastforce
    with a_intro L_intro show "v \<in> \<Psi> A" unfolding parikh_img_def by blast
  qed
qed

lemma subseteq_comm_subseteq:
  assumes "\<Psi> A \<subseteq> \<Psi> B"
  shows "A \<subseteq> \<Union>(parikh_img_eq_class B)" (is "A \<subseteq> ?B'")
proof
  fix a
  assume a_in_A: "a \<in> A"
  from assms have "\<Psi> A \<subseteq> \<Psi> ?B'"
    using parikh_img_Union_class by blast
  with a_in_A have vec_a_in_B': "mset a \<in> \<Psi> ?B'" unfolding parikh_img_def by fast
  then have "\<exists>b. mset b = mset a \<and> b \<in> ?B'"
    unfolding parikh_img_def by fastforce
  then obtain b where b_intro: "mset b = mset a \<and> b \<in> ?B'" by blast
  with vec_a_in_B' have "\<Psi> (?B' \<union> {a}) = \<Psi> ?B'"unfolding parikh_img_def by blast
  with parikh_img_Union_class have "\<Psi> (?B' \<union> {a}) = \<Psi> B" by blast
  then show "a \<in> ?B'" unfolding parikh_img_eq_class_def by blast
qed

end
