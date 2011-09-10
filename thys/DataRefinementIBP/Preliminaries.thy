header {*  Preliminaries  *}

theory Preliminaries
imports Main "~~/src/HOL/Library/Lattice_Syntax"
begin

subsection {*Simplification Lemmas*}

declare fun_upd_idem[simp]

lemma simp_eq_emptyset:
  "(X = {}) = (\<forall> x. x \<notin> X)"
  by blast

lemma mono_comp: "mono f \<Longrightarrow> mono g \<Longrightarrow> mono (f o g)" 
  by (unfold mono_def) auto


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

lemma inf_bot_bot: (* FIXME *)
  "(x::'a::{semilattice_inf,bot}) \<sqinter> \<bottom> = \<bottom>"
  apply (rule antisym)
  by auto

end
