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

definition weakly_welltyped_atom where
  "weakly_welltyped_atom \<V> a \<equiv>
    case rep_uprod a of (t, t') \<Rightarrow> \<forall>\<tau>. \<V> \<turnstile> t : \<tau> \<longleftrightarrow> \<V> \<turnstile> t' : \<tau>"

definition weakly_welltyped_literal where
  "weakly_welltyped_literal \<V> l \<equiv> weakly_welltyped_atom \<V> (atm_of l)"

lemma imgu_weakly_welltyped_atom [intro]:
  assumes "type_preserving_on (atom.vars a) \<V> \<mu>" "term.is_imgu \<mu> {set_uprod a}"
  shows "weakly_welltyped_atom \<V> a"
proof -

  obtain t t' where rep_uprod_a: "rep_uprod a = (t, t')" and a: "a = Upair t t'"
    by (cases a) (metis Quotient3_uprod surj_pair Quotient3_def Upair.abs_eq)

  have "type_preserving_on (term.vars t \<union> term.vars t') \<V> \<mu>" "term.is_imgu \<mu> {{t, t'}}"
    using assms
    unfolding a
    by simp_all

  then show ?thesis
    using term.imgu_same_type
    unfolding weakly_welltyped_atom_def rep_uprod_a
    by blast
qed  

lemma imgu_weakly_welltyped_literal [intro]:
  assumes "type_preserving_on (literal.vars l) \<V> \<mu>" "term.is_imgu \<mu> {uprod_literal_to_set l}"
  shows "weakly_welltyped_literal \<V> l"
  using imgu_weakly_welltyped_atom assms
  unfolding weakly_welltyped_literal_def
  by (cases l) simp_all

lemma [intro]:
  assumes "type_preserving_on (term.vars t \<union> term.vars t') \<V> \<mu>" "term.is_imgu \<mu> {{t, t'}}"
  shows 
    imgu_weakly_welltyped_literal_Pos: "weakly_welltyped_literal \<V> (t \<approx> t')" and 
    imgu_weakly_welltyped_literal_Neg: "weakly_welltyped_literal \<V> (t !\<approx> t')"
  using imgu_weakly_welltyped_atom assms
  unfolding weakly_welltyped_literal_def
  by simp_all

definition weakly_welltyped_clause where
  "weakly_welltyped_clause \<V> C \<equiv> \<forall>l\<in># C. weakly_welltyped_literal \<V> l"

abbreviation is_ground_instance where 
  "is_ground_instance \<V> C \<gamma> \<equiv>
    clause.is_ground (C \<cdot> \<gamma>) \<and>
    type_preserving_on (clause.vars C) \<V> \<gamma> \<and>
    infinite_variables_per_type \<V> \<and>
    weakly_welltyped_clause \<V> C"

sublocale groundable_nonground_clause where 
  atom_subst = "(\<cdot>a)" and atom_vars = atom.vars and atom_to_ground = atom.to_ground and
  atom_from_ground = atom.from_ground and is_ground_instance = is_ground_instance
  by unfold_locales simp

lemma rep_uprod_same_type [simp]: 
  "(case rep_uprod (Upair t t') of (t, t') \<Rightarrow> \<forall>\<tau>. \<V> \<turnstile> t : \<tau> \<longleftrightarrow> \<V> \<turnstile> t' : \<tau>) \<longleftrightarrow>
   (\<forall>\<tau>. \<V> \<turnstile> t : \<tau> \<longleftrightarrow> \<V> \<turnstile> t' : \<tau>)"
  by (rule rep_uprod_UpairI) auto

lemma weakly_welltyped_atom_iff [simp]: 
  "weakly_welltyped_atom \<V> (Upair t t') \<longleftrightarrow> (\<forall>\<tau>. \<V> \<turnstile> t : \<tau> \<longleftrightarrow> \<V> \<turnstile> t' : \<tau>)"
  unfolding weakly_welltyped_atom_def
  by auto

lemma weakly_welltyped_literal_iff [simp]:
  "weakly_welltyped_literal \<V> (Pos a) \<longleftrightarrow> weakly_welltyped_atom \<V> a"
  "weakly_welltyped_literal \<V> (Neg a) \<longleftrightarrow> weakly_welltyped_atom \<V> a"
  unfolding weakly_welltyped_literal_def
  by auto

lemma weakly_welltyped_clause_add_mset [simp]: 
  "weakly_welltyped_clause \<V> (add_mset l C) \<longleftrightarrow>
   weakly_welltyped_literal \<V> l \<and> weakly_welltyped_clause \<V> C"
  unfolding weakly_welltyped_clause_def
  by auto

lemma weakly_welltyped_clause_plus [simp]: 
  "weakly_welltyped_clause \<V> (C + C') \<longleftrightarrow> 
   weakly_welltyped_clause \<V> C \<and> weakly_welltyped_clause \<V> C'"
  unfolding weakly_welltyped_clause_def
  by auto

lemma weakly_welltyped_clause_empty [intro]: "weakly_welltyped_clause \<V>' {#}"
  unfolding weakly_welltyped_clause_def
  by simp

lemma \<P>_simps:
  assumes "\<P> \<in> {Pos, Neg}"
  shows 
    "\<And>a \<sigma>. \<P> a \<cdot>l \<sigma> = \<P> (a \<cdot>a \<sigma>)"
    "\<And>\<V> a. literal.is_welltyped \<V> (\<P> a) \<longleftrightarrow> atom.is_welltyped \<V> a"
    "\<And>a. literal.vars (\<P> a) = atom.vars a"
    "\<And>a. atm_of (\<P> a) = a"
    "\<And>\<V> a. weakly_welltyped_literal \<V> (\<P> a) \<longleftrightarrow> weakly_welltyped_atom \<V> a"
  using assms
  by (auto simp: literal_is_welltyped_iff_atm_of)

(* TODO: Lifting? *)
lemma weakly_welltyped_atom_subst [simp]:
  assumes "type_preserving_on (atom.vars a) \<V> \<sigma>"
  shows "weakly_welltyped_atom \<V> (a \<cdot>a \<sigma>) \<longleftrightarrow> weakly_welltyped_atom \<V> a"
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

lemma weakly_welltyped_literal_subst [simp]:
  assumes "type_preserving_on (literal.vars l) \<V> \<sigma>"
  shows "weakly_welltyped_literal \<V> (l \<cdot>l \<sigma>) \<longleftrightarrow> weakly_welltyped_literal \<V> l"
  using assms
  unfolding weakly_welltyped_literal_def
  by (cases l) auto

lemma weakly_welltyped_clause_subst [simp]:
  assumes "type_preserving_on (clause.vars C) \<V> \<sigma>"
  shows "weakly_welltyped_clause \<V> (C \<cdot> \<sigma>) \<longleftrightarrow> weakly_welltyped_clause \<V> C"
  using assms
  by (induction C) auto

lemma weakly_welltyped_atom_renaming [simp]:
  assumes
    \<rho>: "term.is_renaming \<rho>" and
    \<V>_\<V>': "\<forall>x\<in>atom.vars a. \<V> x = \<V>' (term.rename \<rho> x)"
  shows "weakly_welltyped_atom \<V>' (a \<cdot>a \<rho>) \<longleftrightarrow> weakly_welltyped_atom \<V> a"
  using term.welltyped_renaming[OF \<rho>] \<V>_\<V>'
  unfolding weakly_welltyped_atom_def
  by (cases a) (auto simp: Set.ball_Un)

lemma weakly_welltyped_literal_renaming [simp]:
  assumes
    \<rho>: "term.is_renaming \<rho>" and
    \<V>_\<V>': "\<forall>x\<in>literal.vars l. \<V> x = \<V>' (term.rename \<rho> x)"
  shows "weakly_welltyped_literal \<V>' (l \<cdot>l \<rho>) \<longleftrightarrow> weakly_welltyped_literal \<V> l"
  using assms weakly_welltyped_atom_renaming
  unfolding weakly_welltyped_literal_def
  by (cases l) auto

lemma weakly_welltyped_clause_renaming [simp]:
  assumes
    \<rho>: "term.is_renaming \<rho>" and
    \<V>_\<V>': "\<forall>x\<in>clause.vars C. \<V> x = \<V>' (term.rename \<rho> x)"
  shows "weakly_welltyped_clause \<V>' (C \<cdot> \<rho>) \<longleftrightarrow> weakly_welltyped_clause \<V> C"
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
