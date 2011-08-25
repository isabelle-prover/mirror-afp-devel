header {*  Preliminaries  *}

theory Preliminaries
imports Main "~~/src/HOL/Library/Lattice_Syntax"
begin

subsection {*Simplification Lemmas*}

declare fun_upd_idem[simp]

lemma simp_eq_emptyset:
  "(X = {}) = (\<forall> x. x \<notin> X)"
  by blast

lemma mono_comp[simp]:
  "mono f \<Longrightarrow> mono g \<Longrightarrow> mono (f o g)" 
  apply (unfold mono_def)
  by auto

lemma neg_fun_pred: "(- A) x = - (A x)"
  by (simp add: fun_Compl_def)

lemma bot_fun_pred: "bot i = {}"
  by (simp add: bot_fun_def)

subsection {*  Finite sets and cardinal properties  *}

lemma marked_finite [simp]: "finite (-X) \<Longrightarrow> finite (-insert x X)"
  apply (case_tac "(-insert x X) \<subseteq> -X")
  by (rule finite_subset, auto)

lemma card_insert [simp]: "(-insert x X) = (-X) - {x}"
by auto

lemma card_remove [simp]: "finite X \<Longrightarrow> x \<in> X \<Longrightarrow> card (X - {x}) = card(X) - 1"
apply(rule_tac t = X in insert_Diff [THEN subst], assumption)
apply(simp del:insert_Diff_single)
done

lemma nonempty_card [simp]: "finite X \<Longrightarrow> x \<in> X \<Longrightarrow> card(X) \<noteq>  0"
apply auto
done

subsection {*Complete Lattice Results*}

abbreviation
  SUP1_syntax :: "('a \<Rightarrow> 'b::complete_lattice) \<Rightarrow> 'b"  ("(SUP _)" [1000] 1000)
  where "SUP P == SUPR UNIV P"

theorem SUP_upper:
  "P w \<le> SUP P"
  by (simp add: le_SUPI)


theorem SUP_least:
  "(!! w . P w \<le> Q) \<Longrightarrow> SUP P \<le> Q"
  by (simp add: SUP_leI)


lemma SUP_fun_eq:
  "SUP A i = SUP (\<lambda> w . A w i)"
  by (rule SUP_apply)

text {*Monotonic applications which map monotonic to monotonic have monotonic fixpoints*}

definition
  "mono_mono F = (mono F \<and> (\<forall> f . mono f \<longrightarrow> mono (F f)))"

theorem lfp_mono [simp]:
  "mono_mono F \<Longrightarrow> mono (lfp F)"
  apply (simp add: mono_mono_def)
  apply (rule_tac f="F" and P = "mono" in lfp_ordinal_induct)
  apply auto
  apply (simp add: mono_def)
  apply auto
  apply (simp_all add: Sup_fun_def)
  apply (fast intro: SUP_leI le_SUPI2)
  done

text {*Some lattice simplification rules*}

lemma inf_bot_bot[simp]:
  "x \<sqinter> \<bottom> = \<bottom>"
  apply (rule antisym)
  by auto

theorem Sup_bottom:
  "(Sup X = (bot::'a::complete_lattice)) = (\<forall> x \<in> X . x = bot)"
  by (fact Sup_bot_conv)

theorem Inf_top:
  "(Inf X = (\<top>::'a::complete_lattice)) = (\<forall> x \<in> X . x = \<top>)"
  by (fact Inf_top_conv)

end
