theory Nonground_Clause_With_Equality
  imports
    Nonground_Clause_Generic
    Uprod_Literal_Functor
begin

section \<open>Nonground Clauses with Equality\<close>

locale nonground_clause = "term": nonground_term
begin

subsection \<open>Nonground Atoms\<close>

sublocale atom: term_based_lifting where
  sub_subst = "(\<cdot>t)" and sub_vars = term.vars and map = map_uprod and to_set = set_uprod and
  sub_to_ground = term.to_ground and sub_from_ground = term.from_ground and
  to_ground_map = map_uprod and from_ground_map = map_uprod and ground_map = map_uprod and
  to_set_ground = set_uprod
  by unfold_locales

(* TODO: *)
notation atom.subst (infixl "\<cdot>a" 67)

lemma vars_atom [simp]: "atom.vars (Upair t\<^sub>1 t\<^sub>2) = term.vars t\<^sub>1 \<union> term.vars t\<^sub>2"
  by (simp_all add: atom.vars_def)

lemma subst_atom [simp]:
  "Upair t\<^sub>1 t\<^sub>2 \<cdot>a \<sigma> = Upair (t\<^sub>1 \<cdot>t \<sigma>) (t\<^sub>2 \<cdot>t \<sigma>)"
  unfolding atom.subst_def
  by simp_all

lemma atom_from_ground_term_from_ground [simp]:
  "atom.from_ground (Upair t\<^sub>G\<^sub>1 t\<^sub>G\<^sub>2) = Upair (term.from_ground t\<^sub>G\<^sub>1) (term.from_ground t\<^sub>G\<^sub>2)"
  by (simp add: atom.from_ground_def)

lemma atom_to_ground_term_to_ground [simp]:
  "atom.to_ground (Upair t\<^sub>1 t\<^sub>2) = Upair (term.to_ground t\<^sub>1) (term.to_ground t\<^sub>2)"
  by (simp add: atom.to_ground_def)

lemma atom_is_ground_term_is_ground [simp]:
  "atom.is_ground (Upair t\<^sub>1 t\<^sub>2) \<longleftrightarrow> term.is_ground t\<^sub>1 \<and> term.is_ground t\<^sub>2"
  by simp

lemma obtain_from_atom_subst:
  assumes "Upair t\<^sub>1' t\<^sub>2' = a \<cdot>a \<sigma>"
  obtains t\<^sub>1 t\<^sub>2
  where "a = Upair t\<^sub>1 t\<^sub>2" "t\<^sub>1' = t\<^sub>1 \<cdot>t \<sigma>" "t\<^sub>2' = t\<^sub>2 \<cdot>t \<sigma>"
  using assms
  unfolding atom.subst_def
  by(cases a) force

subsection \<open>Nonground Literals\<close>

sublocale nonground_clause_generic where 
  atom_vars = atom.vars and atom_subst = "(\<cdot>a)" and atom_to_ground = atom.to_ground and
  atom_from_ground = atom.from_ground
  by unfold_locales

lemma obtain_from_pos_literal_subst:
  assumes "l \<cdot>l \<sigma> = t\<^sub>1' \<approx> t\<^sub>2'"
  obtains t\<^sub>1 t\<^sub>2
  where "l = t\<^sub>1 \<approx> t\<^sub>2" "t\<^sub>1' = t\<^sub>1 \<cdot>t \<sigma>" "t\<^sub>2' = t\<^sub>2 \<cdot>t \<sigma>"
  using assms obtain_from_atom_subst subst_pos_stable
  by (metis is_pos_def literal.sel(1) subst_literal(3))

lemma obtain_from_neg_literal_subst:
  assumes "l \<cdot>l \<sigma> = t\<^sub>1' !\<approx> t\<^sub>2'"
  obtains t\<^sub>1 t\<^sub>2
  where "l = t\<^sub>1 !\<approx> t\<^sub>2" "t\<^sub>1 \<cdot>t \<sigma> = t\<^sub>1'" "t\<^sub>2 \<cdot>t \<sigma> = t\<^sub>2'"
  using assms obtain_from_atom_subst subst_neg_stable
  by (metis literal.collapse(2) literal.disc(2) literal.sel(2) subst_literal(3))

lemmas obtain_from_literal_subst = obtain_from_pos_literal_subst obtain_from_neg_literal_subst

subsection \<open>Nonground Literals - Alternative\<close>

lemma uprod_literal_subst_eq_literal_subst: "map_uprod_literal (\<lambda>t. t \<cdot>t \<sigma>) l = l \<cdot>l \<sigma>"
  unfolding atom.subst_def literal.subst_def
  by auto

lemma uprod_literal_vars_eq_literal_vars: "\<Union> (term.vars ` uprod_literal_to_set l) = literal.vars l"
  unfolding literal.vars_def atom.vars_def
  by(cases l) simp_all

lemma uprod_literal_from_ground_eq_literal_from_ground:
  "map_uprod_literal term.from_ground l\<^sub>G = literal.from_ground l\<^sub>G"
  unfolding literal.from_ground_def atom.from_ground_def ..

lemma uprod_literal_to_ground_eq_literal_to_ground:
  "map_uprod_literal term.to_ground l = literal.to_ground l"
  unfolding literal.to_ground_def atom.to_ground_def ..

sublocale uprod_literal: term_based_lifting where
  sub_subst = "(\<cdot>t)" and sub_vars = term.vars and map = map_uprod_literal and
  to_set = uprod_literal_to_set and sub_to_ground = term.to_ground and
  sub_from_ground = term.from_ground and to_ground_map = map_uprod_literal and
  from_ground_map = map_uprod_literal and ground_map = map_uprod_literal and
  to_set_ground = uprod_literal_to_set
rewrites
  uprod_literal_subst [simp]: "\<And>l \<sigma>. uprod_literal.subst l \<sigma> = literal.subst l \<sigma>" and
  uprod_literal_vars [simp]: "\<And>l. uprod_literal.vars l = literal.vars l" and
  uprod_literal_from_ground [simp]: "\<And>l\<^sub>G. uprod_literal.from_ground l\<^sub>G = literal.from_ground l\<^sub>G" and
  uprod_literal_to_ground [simp]:"\<And>l. uprod_literal.to_ground l = literal.to_ground l"
proof unfold_locales

  interpret term_based_lifting where
    sub_vars = term.vars and sub_subst = "(\<cdot>t)" and map = map_uprod_literal and
    to_set = uprod_literal_to_set and sub_to_ground = term.to_ground and
    sub_from_ground = term.from_ground and to_ground_map = map_uprod_literal and
    from_ground_map = map_uprod_literal and ground_map = map_uprod_literal and
    to_set_ground = uprod_literal_to_set
    by unfold_locales

  fix l and \<sigma>

  show "subst l \<sigma> = l \<cdot>l \<sigma>"
    unfolding subst_def literal.subst_def atom.subst_def
    by simp

  show "vars l = literal.vars l"
    unfolding atom.vars_def vars_def literal.vars_def
    by(cases l) simp_all

  fix l\<^sub>G 
  show "from_ground l\<^sub>G = literal.from_ground l\<^sub>G"
    unfolding from_ground_def literal.from_ground_def atom.from_ground_def..

  fix l
  show "to_ground l = literal.to_ground l"
    unfolding to_ground_def literal.to_ground_def atom.to_ground_def ..
qed

subsection \<open>Nonground Clauses\<close>

lemmas clause_safe_unfolds =
  atom_to_ground_term_to_ground
  literal_to_ground_atom_to_ground
  atom_from_ground_term_from_ground
  literal_from_ground_atom_from_ground
  literal_from_ground_polarity_stable
  subst_atom
  subst_literal
  vars_atom
  vars_literal

end

end
