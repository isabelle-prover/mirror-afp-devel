theory Superposition
  imports
    First_Order_Clause.Nonground_Order_With_Equality
    First_Order_Clause.Nonground_Selection_Function
    First_Order_Clause.Nonground_Typing_With_Equality
    First_Order_Clause.Typed_Tiebreakers
    First_Order_Clause.Infinite_Variables
                          
    Ground_Superposition
begin

section \<open>Nonground Layer\<close>

locale type_system =
  context_compatible_term_typing_properties where
  welltyped = welltyped and from_ground_context_map = from_ground_context_map +
  witnessed_nonground_typing where welltyped = welltyped
for
  welltyped :: "('v, 'ty) var_types \<Rightarrow> 't \<Rightarrow> 'ty \<Rightarrow> bool" and
  from_ground_context_map :: "('t\<^sub>G \<Rightarrow> 't) \<Rightarrow> 'c\<^sub>G \<Rightarrow> 'c"

locale superposition_calculus =
  type_system where
  welltyped = welltyped and id_subst = "id_subst :: 'subst" and
  from_ground_context_map = "from_ground_context_map :: ('t\<^sub>G \<Rightarrow> 't) \<Rightarrow> 'c\<^sub>G \<Rightarrow> 'c" +

  context_compatible_nonground_order where less\<^sub>t = less\<^sub>t +

  nonground_selection_function where
  select = select and atom_subst = "(\<cdot>a)" and atom_vars = atom.vars and
  atom_to_ground = atom.to_ground and atom_from_ground = atom.from_ground and
  atom_is_ground = atom.is_ground +

  tiebreakers where tiebreakers = tiebreakers +

  ground_critical_pairs where
  compose_context = compose_ground_context and apply_context = apply_ground_context and
  hole = ground_hole +

  infinite_variables where
  exists_nonground = term.exists_nonground and variables = "UNIV :: 'v set"
  for
    select :: "'t atom select" and
    less\<^sub>t :: "'t \<Rightarrow> 't \<Rightarrow> bool" and
    tiebreakers :: "('t\<^sub>G atom, 't atom) tiebreakers" and
    welltyped :: "('v, 'ty) var_types \<Rightarrow> 't \<Rightarrow> 'ty \<Rightarrow> bool"
begin

interpretation term_order_notation .

(* TODO: side condition order *)
inductive eq_resolution :: "('t, 'v, 'ty) typed_clause \<Rightarrow> ('t, 'v, 'ty) typed_clause \<Rightarrow> bool" where
  eq_resolutionI:
  "D = add_mset l D' \<Longrightarrow>
   l = t !\<approx> t' \<Longrightarrow>
   C = D' \<cdot> \<mu> \<Longrightarrow>
   eq_resolution (\<V>, D) (\<V>, C)"
if
  "type_preserving_on (clause.vars D) \<V> \<mu>"
  "term.is_imgu \<mu> {{t, t'}}"
  "select D = {#} \<Longrightarrow> is_maximal (l \<cdot>l \<mu>) (D \<cdot> \<mu>)"
  "select D \<noteq> {#} \<Longrightarrow> is_maximal (l \<cdot>l \<mu>) (select D \<cdot> \<mu>)"

inductive eq_factoring :: "('t, 'v, 'ty) typed_clause \<Rightarrow> ('t, 'v, 'ty) typed_clause \<Rightarrow> bool" where
  eq_factoringI:
  "D = add_mset l\<^sub>1 (add_mset l\<^sub>2 D') \<Longrightarrow>
   l\<^sub>1 = t\<^sub>1 \<approx> t\<^sub>1' \<Longrightarrow>
   l\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2' \<Longrightarrow>
   C = add_mset (t\<^sub>1 \<approx> t\<^sub>2') (add_mset (t\<^sub>1' !\<approx> t\<^sub>2') D') \<cdot> \<mu> \<Longrightarrow>
   eq_factoring (\<V>, D) (\<V>, C)"
if
  "select D = {#}"
  "is_maximal (l\<^sub>1 \<cdot>l \<mu>) (D \<cdot> \<mu>)"
  "\<not> (t\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>1' \<cdot>t \<mu>)"
  "type_preserving_on (clause.vars D) \<V> \<mu>"
  "term.is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}}"

inductive superposition ::
  "('t, 'v, 'ty) typed_clause \<Rightarrow>
   ('t, 'v, 'ty) typed_clause \<Rightarrow>
   ('t, 'v, 'ty) typed_clause \<Rightarrow> bool" where
  superpositionI:
  "E = add_mset l\<^sub>1 E' \<Longrightarrow>
   D = add_mset l\<^sub>2 D' \<Longrightarrow>
   l\<^sub>1 = \<P> (Upair c\<^sub>1\<langle>t\<^sub>1\<rangle> t\<^sub>1') \<Longrightarrow>
   l\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2' \<Longrightarrow>
   C = add_mset (\<P> (Upair (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1))) (E' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
   superposition (\<V>\<^sub>2, D) (\<V>\<^sub>1, E) (\<V>\<^sub>3, C)"
if
  "\<P> \<in> {Pos, Neg}"
  "term.exists_nonground \<Longrightarrow> infinite_variables_per_type \<V>\<^sub>1"
  "term.exists_nonground \<Longrightarrow> infinite_variables_per_type \<V>\<^sub>2"
  "term.is_renaming \<rho>\<^sub>1"
  "term.is_renaming \<rho>\<^sub>2"
  "clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {}"
  "\<not> term.is_Var t\<^sub>1"
  "type_preserving_on (clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 \<mu>"
  "term.is_imgu \<mu> {{t\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}}"
  "\<not> (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>c D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>)"
  "\<not> (c\<^sub>1\<langle>t\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<mu>)"
  "\<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<odot> \<mu>)"
  "\<P> = Pos \<Longrightarrow> select E = {#}"
  "\<P> = Pos \<Longrightarrow> is_strictly_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
  "\<P> = Neg \<Longrightarrow> select E = {#} \<Longrightarrow> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
  "\<P> = Neg \<Longrightarrow> select E \<noteq> {#} \<Longrightarrow> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) ((select E) \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
  "select D = {#}"
  "is_strictly_maximal (l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<mu>) (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>)"
  "\<forall>x \<in> clause.vars E. \<V>\<^sub>1 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>1 x)"
  "\<forall>x \<in> clause.vars D. \<V>\<^sub>2 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>2 x)"
  "type_preserving_on (clause.vars E) \<V>\<^sub>1 \<rho>\<^sub>1"
  "type_preserving_on (clause.vars D) \<V>\<^sub>2 \<rho>\<^sub>2"
  "clause.weakly_welltyped \<V>\<^sub>3 C \<Longrightarrow> literal.weakly_welltyped \<V>\<^sub>2 l\<^sub>2"

abbreviation eq_factoring_inferences where
  "eq_factoring_inferences \<equiv> { Infer [D] C | D C. eq_factoring D C }"

abbreviation eq_resolution_inferences where
  "eq_resolution_inferences \<equiv> { Infer [D] C | D C. eq_resolution D C }"

abbreviation superposition_inferences where
  "superposition_inferences \<equiv> { Infer [D, E] C | D E C. superposition D E C }"

definition inferences :: "('t, 'v, 'ty) typed_clause inference set" where
  "inferences \<equiv> superposition_inferences \<union> eq_resolution_inferences \<union> eq_factoring_inferences"

abbreviation bottom\<^sub>F :: "('t, 'v, 'ty) typed_clause set" ("\<bottom>\<^sub>F") where
  "bottom\<^sub>F \<equiv> {(\<V>, {#}) | \<V>. term.exists_nonground \<longrightarrow> infinite_variables_per_type \<V> }"

end

end
