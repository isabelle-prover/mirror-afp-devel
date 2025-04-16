theory Nonground_Clause
  imports 
    Nonground_Clause_Generic 
    Literal_Functor
begin

section \<open>Nonground Clauses\<close>

type_synonym 'f ground_atom = "'f gterm"
type_synonym ('f, 'v) atom = "('f, 'v) term"

locale nonground_clause = nonground_term_with_context
begin

subsection \<open>Nonground Literals\<close>

sublocale nonground_clause_generic where 
  atom_vars = term.vars and atom_subst = "(\<cdot>t)" and atom_to_ground = term.to_ground and
  atom_from_ground = term.from_ground
  by unfold_locales

lemma obtain_from_pos_literal_subst:
  assumes "l \<cdot>l \<sigma> = Pos t'"
  obtains t
  where "l = Pos t" "t' = t \<cdot>t \<sigma>"
  using assms subst_pos_stable
  by (metis is_pos_def literal.sel(1) subst_literal(3))

lemma obtain_from_neg_literal_subst:
  assumes "l \<cdot>l \<sigma> = Neg t'"
  obtains t
  where "l = Neg t" "t' = t \<cdot>t \<sigma>"
  using assms subst_neg_stable
  by (metis literal.collapse(2) literal.disc(2) literal.sel(2) subst_literal(3))

lemmas obtain_from_literal_subst = obtain_from_pos_literal_subst obtain_from_neg_literal_subst

subsection \<open>Nonground Clauses\<close>

lemmas clause_safe_unfolds =
  literal_to_ground_atom_to_ground
  literal_from_ground_atom_from_ground
  literal_from_ground_polarity_stable
  subst_literal
  vars_literal

end

end
