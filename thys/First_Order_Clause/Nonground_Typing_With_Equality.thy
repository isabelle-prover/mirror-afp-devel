theory Nonground_Typing_With_Equality
  imports
    Nonground_Typing_Generic
    Clause_Typing_With_Equality
    Nonground_Clause_With_Equality
begin

type_synonym ('t, 'v, 'ty) typed_clause = "('v, 'ty) var_types \<times> 't clause"

locale nonground_typing =
  nonground_clause +
  term_typing_properties +
  atom: term_based_nonground_typing_lifting where 
  sub_welltyped = welltyped and sub_subst = "(\<cdot>t)" and sub_vars = term.vars and 
  to_set = set_uprod and map = map_uprod and sub_to_ground = term.to_ground and 
  sub_from_ground = term.from_ground and to_ground_map = map_uprod and 
  from_ground_map = map_uprod and ground_map = map_uprod and to_set_ground = set_uprod
begin

sublocale nonground_typing_generic where 
  atom_subst = "(\<cdot>a)" and atom_vars = atom.vars and atom_to_ground = atom.to_ground and
  atom_from_ground = atom.from_ground and atom_welltyped = atom.welltyped
  by unfold_locales

sublocale clause_typing "welltyped \<V>"
  by unfold_locales

definition type_preserving_atom where
  "type_preserving_atom \<V> a \<equiv>
    case rep_uprod a of (t, t') \<Rightarrow> \<forall>\<tau>. \<V> \<turnstile> t : \<tau> \<longleftrightarrow> \<V> \<turnstile> t' : \<tau>"

definition type_preserving_literal where
  "type_preserving_literal \<V> l \<equiv> type_preserving_atom \<V> (atm_of l)"

definition type_preserving_literals where
  "type_preserving_literals \<V> C \<equiv> \<forall>l\<in># C. type_preserving_literal \<V> l"

abbreviation is_ground_instance where 
  "is_ground_instance \<V> C \<gamma> \<equiv>
    clause.is_ground (C \<cdot> \<gamma>) \<and>
    type_preserving_on (clause.vars C) \<V> \<gamma> \<and>
    infinite_variables_per_type \<V> \<and>
    type_preserving_literals \<V> C"

sublocale groundable_nonground_clause where 
  atom_subst = "(\<cdot>a)" and atom_vars = atom.vars and atom_to_ground = atom.to_ground and
  atom_from_ground = atom.from_ground and is_ground_instance = is_ground_instance
  by unfold_locales simp

lemma rep_uprod_same_type [simp]: 
  "(case rep_uprod (Upair t t') of (t, t') \<Rightarrow> \<forall>\<tau>. \<V> \<turnstile> t : \<tau> \<longleftrightarrow> \<V> \<turnstile> t' : \<tau>) \<longleftrightarrow>
   (\<forall>\<tau>. \<V> \<turnstile> t : \<tau> \<longleftrightarrow> \<V> \<turnstile> t' : \<tau>)"
  by (rule rep_uprod_UpairI) auto

lemma type_preserving_atom_iff [simp]: 
  "type_preserving_atom \<V> (Upair t t') \<longleftrightarrow> (\<forall>\<tau>. \<V> \<turnstile> t : \<tau> \<longleftrightarrow> \<V> \<turnstile> t' : \<tau>)"
  unfolding type_preserving_atom_def
  by auto

lemma type_preserving_literal_iff [simp]:
  "type_preserving_literal \<V> (Pos a) \<longleftrightarrow> type_preserving_atom \<V> a"
  "type_preserving_literal \<V> (Neg a) \<longleftrightarrow> type_preserving_atom \<V> a"
  unfolding type_preserving_literal_def
  by auto

lemma type_preserving_literals_add_mset [simp]: 
  "type_preserving_literals \<V> (add_mset l C) \<longleftrightarrow> 
   type_preserving_literal \<V> l \<and>  type_preserving_literals \<V> C"
  unfolding type_preserving_literals_def
  by auto

lemma type_preserving_literals_plus [simp]: 
  "type_preserving_literals \<V> (C + C') \<longleftrightarrow> 
   type_preserving_literals \<V> C \<and> type_preserving_literals \<V> C'"
  unfolding type_preserving_literals_def
  by auto

lemma type_preserving_literals_empty [intro]: "type_preserving_literals \<V>' {#}"
  unfolding type_preserving_literals_def
  by simp

lemma \<P>_simps:
  assumes "\<P> \<in> {Pos, Neg}"
  shows 
    "\<And>a \<sigma>. \<P> a \<cdot>l \<sigma> = \<P> (a \<cdot>a \<sigma>)"
    "\<And>\<V> a. literal.is_welltyped \<V> (\<P> a) \<longleftrightarrow> atom.is_welltyped \<V> a"
    "\<And>a. literal.vars (\<P> a) = atom.vars a"
    "\<And>a. atm_of (\<P> a) = a"
    "\<And>\<V> a. type_preserving_literal \<V> (\<P> a) \<longleftrightarrow> type_preserving_atom \<V> a"
  using assms
  by (auto simp: literal_is_welltyped_iff_atm_of)

(* TODO: Lifting? *)
lemma type_preserving_atom_subst [simp]:
  assumes "type_preserving_on (atom.vars a) \<V> \<sigma>"
  shows "type_preserving_atom \<V> (a \<cdot>a \<sigma>) \<longleftrightarrow> type_preserving_atom \<V> a"
  using assms
proof (cases a)
  case (Upair t t')

  have type_preserving_\<sigma>: "type_preserving_on (term.vars t \<union> term.vars t') \<V> \<sigma>"
    using assms
    unfolding Upair
    by auto
    
  then show ?thesis
    unfolding Upair
    using term.welltyped_subst_stability
    by auto
qed

lemma type_preserving_literal_subst [simp]:
  assumes "type_preserving_on (literal.vars l) \<V> \<sigma>"
  shows "type_preserving_literal \<V> (l \<cdot>l \<sigma>) \<longleftrightarrow> type_preserving_literal \<V> l"
  using assms
  unfolding type_preserving_literal_def
  by (cases l) auto

lemma type_preserving_literals_subst [simp]:
  assumes "type_preserving_on (clause.vars C) \<V> \<sigma>"
  shows "type_preserving_literals \<V> (C \<cdot> \<sigma>) \<longleftrightarrow> type_preserving_literals \<V> C"
  using assms
  by (induction C) auto

lemma type_preserving_atom_renaming [simp]:
  assumes
    \<rho>: "term.is_renaming \<rho>" and
    \<V>_\<V>': "\<forall>x\<in>atom.vars a. \<V> x = \<V>' (term.rename \<rho> x)"
  shows "type_preserving_atom \<V>' (a \<cdot>a \<rho>) \<longleftrightarrow> type_preserving_atom \<V> a"
  using term.welltyped_renaming[OF \<rho>] \<V>_\<V>'
  unfolding type_preserving_atom_def
  by (cases a) (auto simp: Set.ball_Un)

lemma type_preserving_literal_renaming [simp]:
  assumes
    \<rho>: "term.is_renaming \<rho>" and
    \<V>_\<V>': "\<forall>x\<in>literal.vars l. \<V> x = \<V>' (term.rename \<rho> x)"
  shows "type_preserving_literal \<V>' (l \<cdot>l \<rho>) \<longleftrightarrow> type_preserving_literal \<V> l"
  using assms type_preserving_atom_renaming
  unfolding type_preserving_literal_def
  by (cases l) auto

lemma type_preserving_literals_renaming [simp]:
  assumes
    \<rho>: "term.is_renaming \<rho>" and
    \<V>_\<V>': "\<forall>x\<in>clause.vars C. \<V> x = \<V>' (term.rename \<rho> x)"
  shows "type_preserving_literals \<V>' (C \<cdot> \<rho>) \<longleftrightarrow> type_preserving_literals \<V> C"
  using assms 
  by (induction C) (auto simp: Set.ball_Un)

end

locale witnessed_nonground_typing =
  nonground_typing +
  atom: term_based_witnessed_nonground_typing_lifting where
  sub_welltyped = welltyped and sub_subst = "(\<cdot>t)" and sub_vars = term.vars and
  to_set = set_uprod and map = map_uprod and sub_to_ground = term.to_ground and
  sub_from_ground = term.from_ground and to_ground_map = map_uprod and
  from_ground_map = map_uprod and ground_map = map_uprod and to_set_ground = set_uprod
begin

sublocale witnessed_nonground_typing_generic where
  atom_welltyped = atom.welltyped and atom_subst = "(\<cdot>a)" and atom_vars = atom.vars and 
  atom_to_ground = atom.to_ground and atom_from_ground = atom.from_ground
  by unfold_locales

end

end
