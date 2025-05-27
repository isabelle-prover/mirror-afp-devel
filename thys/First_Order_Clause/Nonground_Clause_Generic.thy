theory Nonground_Clause_Generic
  imports
    Nonground_Term
    Multiset_Extra
    Multiset_Grounding_Lifting
    Saturation_Framework_Extensions.Clausal_Calculus
begin

section \<open>Nonground Clauses and Substitutions\<close>


subsection \<open>Setup for lifting from terms\<close>

locale term_based_multiset_lifting =
  term_based_lifting where
  map = image_mset and to_set = set_mset and to_ground_map = image_mset and
  from_ground_map = image_mset and ground_map = image_mset and to_set_ground = set_mset
begin

sublocale multiset_grounding_lifting where
  id_subst = Var and comp_subst = comp_subst
  by unfold_locales

end

locale nonground_clause_generic =
  literal: term_based_lifting where
  sub_vars = atom_vars and sub_subst = atom_subst and sub_to_ground = atom_to_ground and
  sub_from_ground = atom_from_ground and map = map_literal and to_set = set_literal and
  to_ground_map = map_literal and from_ground_map = map_literal and ground_map = map_literal and
  to_set_ground = set_literal
for
  atom_from_ground :: "'g \<Rightarrow> 'a" and
  atom_to_ground :: "'a \<Rightarrow> 'g" and
  atom_subst :: "'a \<Rightarrow> ('v \<Rightarrow> 't) \<Rightarrow> 'a" and
  atom_vars :: "'a \<Rightarrow> 'v set"
begin

subsection \<open>Nonground Literals\<close>

(* TODO? *)
notation atom_subst (infixl "\<cdot>a" 66)
notation literal.subst (infixl "\<cdot>l" 66)

lemma vars_literal [simp]:
  "literal.vars (Pos a) = atom_vars a"
  "literal.vars (Neg a) = atom_vars a"
  "literal.vars ((if b then Pos else Neg) a) = atom_vars a"
  by (simp_all add: literal.vars_def)

lemma subst_literal [simp]:
  "Pos a \<cdot>l \<sigma> = Pos (a \<cdot>a \<sigma>)"
  "Neg a \<cdot>l \<sigma> = Neg (a \<cdot>a \<sigma>)"
  "atm_of (l \<cdot>l \<sigma>) = atm_of l \<cdot>a \<sigma>"
  unfolding literal.subst_def
  using literal.map_sel
  by auto

lemma subst_literal_if [simp]:
  "(if b then Pos else Neg) a \<cdot>l \<rho> = (if b then Pos else Neg) (a \<cdot>a \<rho>)"
  by simp

lemma subst_polarity_stable:
  shows
    subst_neg_stable [simp]: "is_neg (l \<cdot>l \<sigma>) \<longleftrightarrow> is_neg l" and
    subst_pos_stable [simp]: "is_pos (l \<cdot>l \<sigma>) \<longleftrightarrow> is_pos l"
  by (simp_all add: literal.subst_def)

declare literal.discI [intro]

lemma literal_from_ground_atom_from_ground [simp]:
  "literal.from_ground (Neg a\<^sub>G) = Neg (atom_from_ground a\<^sub>G)"
  "literal.from_ground (Pos a\<^sub>G) = Pos (atom_from_ground a\<^sub>G)"
  by (simp_all add: literal.from_ground_def)

lemma literal_from_ground_polarity_stable [simp]:
  shows
    neg_literal_from_ground_stable: "is_neg (literal.from_ground l\<^sub>G) \<longleftrightarrow> is_neg l\<^sub>G" and
    pos_literal_from_ground_stable: "is_pos (literal.from_ground l\<^sub>G) \<longleftrightarrow> is_pos l\<^sub>G"
  by (simp_all add: literal.from_ground_def)

lemma literal_to_ground_atom_to_ground [simp]:
  "literal.to_ground (Pos a) = Pos (atom_to_ground a)"
  "literal.to_ground (Neg a) = Neg (atom_to_ground a)"
  by (simp_all add: literal.to_ground_def)

lemma literal_is_ground_atom_is_ground [intro]:
  "literal.is_ground l \<longleftrightarrow> literal.sub.is_ground (atm_of l)"
  by (simp add: literal.vars_def set_literal_atm_of)

subsection \<open>Nonground Clauses\<close>

sublocale clause: term_based_multiset_lifting where
  sub_subst = literal.subst and sub_vars = literal.vars and sub_to_ground = literal.to_ground and
  sub_from_ground = literal.from_ground
  by unfold_locales

notation clause.subst (infixl "\<cdot>" 67)

lemmas clause_submset_vars_clause_subset [intro] =
  clause.to_set_subset_vars_subset[OF set_mset_mono]

lemmas sub_ground_clause = clause.to_set_subset_is_ground[OF set_mset_mono]

lemma subst_clause_remove1_mset [simp]:
  assumes "l \<in># C"
  shows "remove1_mset l C \<cdot> \<sigma> = remove1_mset (l \<cdot>l \<sigma>) (C \<cdot> \<sigma>)"
  unfolding clause.subst_def image_mset_remove1_mset_if
  using assms
  by simp

lemma clause_from_ground_remove1_mset [simp]:
  "clause.from_ground (remove1_mset l\<^sub>G C\<^sub>G) =
    remove1_mset (literal.from_ground l\<^sub>G) (clause.from_ground C\<^sub>G)"
  unfolding clause.from_ground_def image_mset_remove1_mset[OF literal.inj_from_ground]..

end

locale groundable_nonground_clause = 
  nonground_clause_generic where atom_subst = atom_subst
for 
  atom_subst :: "'a \<Rightarrow> ('v \<Rightarrow> 't) \<Rightarrow> 'a"  and
  is_ground_instance :: "'env \<Rightarrow> 'a clause \<Rightarrow> ('v \<Rightarrow> 't) \<Rightarrow> bool" +
assumes is_ground_instance_is_ground:
  "\<And>\<Gamma> C \<gamma>. is_ground_instance \<Gamma> C \<gamma> \<Longrightarrow> clause.is_ground (C \<cdot> \<gamma>)"
begin

definition ground_instances where
  "ground_instances \<Gamma> C = { clause.to_ground (C \<cdot> \<gamma>) | \<gamma>. is_ground_instance \<Gamma> C \<gamma> }"

end

end
