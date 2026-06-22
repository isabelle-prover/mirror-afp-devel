(*  Title:      Labelled_Formulas.thy
    Author:     Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz, 2026
    Maintainer: Arthur Freitas Ramos

    Propositional formula language and elementary label-erasure operations.
*)

theory Labelled_Formulas
  imports Main
begin

text \<open>
This theory fixes the propositional formula language and the elementary
operations that erase labels from labelled formulae, databases, and list
contexts.  Labels are deliberately represented by a product component, so the
logical shape of a labelled formula is recovered by taking its second
projection.
\<close>

datatype 'a fm =
    Atom 'a
  | Bot
  | Imp "'a fm" "'a fm"
  | Con "'a fm" "'a fm"
  | Dis "'a fm" "'a fm"

type_synonym ('l, 'a) lfm = "'l \<times> 'a fm"

definition erase_lfm :: "('l, 'a) lfm \<Rightarrow> 'a fm" where
  "erase_lfm x = snd x"

definition erase_db :: "('l, 'a) lfm set \<Rightarrow> 'a fm set" where
  "erase_db \<Gamma> = snd ` \<Gamma>"

definition erase_ctx :: "('l, 'a) lfm list \<Rightarrow> 'a fm list" where
  "erase_ctx \<Gamma> = map snd \<Gamma>"

lemma erase_lfm_simps [simp]:
  "erase_lfm (l, A) = A"
  by (simp add: erase_lfm_def)

lemma erase_ctx_Nil [simp]:
  "erase_ctx [] = []"
  by (simp add: erase_ctx_def)

lemma erase_ctx_Cons [simp]:
  "erase_ctx (x # \<Gamma>) = erase_lfm x # erase_ctx \<Gamma>"
  by (cases x) (simp add: erase_ctx_def)

lemma erase_ctx_append [simp]:
  "erase_ctx (\<Gamma> @ \<Delta>) = erase_ctx \<Gamma> @ erase_ctx \<Delta>"
  by (simp add: erase_ctx_def)

lemma erase_db_insert [simp]:
  "erase_db (insert x \<Gamma>) = insert (erase_lfm x) (erase_db \<Gamma>)"
  by (cases x) (auto simp: erase_db_def erase_lfm_def)

lemma erase_db_Un [simp]:
  "erase_db (\<Gamma> \<union> \<Delta>) = erase_db \<Gamma> \<union> erase_db \<Delta>"
  by (auto simp: erase_db_def)

end
