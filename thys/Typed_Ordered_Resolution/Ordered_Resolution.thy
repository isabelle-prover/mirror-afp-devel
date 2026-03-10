theory Ordered_Resolution
  imports
    First_Order_Clause.Nonground_Order
    First_Order_Clause.Nonground_Selection_Function
    First_Order_Clause.Nonground_Typing
    First_Order_Clause.Typed_Tiebreakers
    First_Order_Clause.Infinite_Variables
begin

locale ordered_resolution_calculus =
  witnessed_nonground_typing where
  welltyped = welltyped and term_to_ground = "term_to_ground :: 't \<Rightarrow> 't\<^sub>G" and
  id_subst = "id_subst :: 'subst" +

  nonground_order where less\<^sub>t = less\<^sub>t +

  nonground_selection_function where
  select = select and atom_subst = "(\<cdot>t)" and atom_vars = term.vars and
  atom_from_ground = term.from_ground and atom_to_ground = term.to_ground and
  atom_is_ground = term.is_ground +
  tiebreakers tiebreakers +
  infinite_variables where
  exists_nonground = term.exists_nonground and variables = "UNIV :: 'v set"
for
  select :: "'t select" and
  less\<^sub>t :: "'t \<Rightarrow> 't \<Rightarrow> bool" and
  tiebreakers :: "('t\<^sub>G, 't) tiebreakers" and
  welltyped :: "('v, 'ty) var_types \<Rightarrow> 't \<Rightarrow> 'ty \<Rightarrow> bool"
begin

inductive factoring :: "('t, 'v, 'ty) typed_clause \<Rightarrow> ('t, 'v, 'ty) typed_clause \<Rightarrow> bool" where
  factoringI: 
  "D = add_mset l\<^sub>1 (add_mset l\<^sub>2 D') \<Longrightarrow>
   l\<^sub>1 = Pos t\<^sub>1 \<Longrightarrow>
   l\<^sub>2 = Pos t\<^sub>2 \<Longrightarrow>
   C = (add_mset l\<^sub>1 D') \<cdot> \<mu> \<Longrightarrow>
   factoring (\<V>, D) (\<V>, C)"
if
  "select D = {#}"
  "is_maximal (l\<^sub>1 \<cdot>l \<mu>) (D \<cdot> \<mu>)"
  "type_preserving_on (clause.vars D) \<V> \<mu>" 
  "term.is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}}"

inductive resolution ::
  "('t, 'v, 'ty) typed_clause \<Rightarrow>
   ('t, 'v, 'ty) typed_clause \<Rightarrow>
   ('t, 'v, 'ty) typed_clause \<Rightarrow> bool" where
  resolutionI: 
  "E = add_mset l\<^sub>1 E' \<Longrightarrow>
   D = add_mset l\<^sub>2 D' \<Longrightarrow>
   l\<^sub>1 = Neg t\<^sub>1 \<Longrightarrow>
   l\<^sub>2 = Pos t\<^sub>2 \<Longrightarrow>
   C = (E' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
   resolution (\<V>\<^sub>2, D) (\<V>\<^sub>1, E) (\<V>\<^sub>3, C)"
if
  "term.exists_nonground \<Longrightarrow> infinite_variables_per_type \<V>\<^sub>1"
  "term.exists_nonground \<Longrightarrow> infinite_variables_per_type \<V>\<^sub>2"
  "term.is_renaming \<rho>\<^sub>1"
  "term.is_renaming \<rho>\<^sub>2"
  "clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {}"
  "type_preserving_on (clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 \<mu>" 
  "term.is_imgu \<mu> {{t\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}}"
  "\<not> (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>c D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>)"
  "select E = {#} \<Longrightarrow> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
  "select E \<noteq> {#} \<Longrightarrow> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) ((select E) \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
  "select D = {#}"
  "is_strictly_maximal (l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<mu>) (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>)"
  "\<forall>x \<in> clause.vars E. \<V>\<^sub>1 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>1 x)"
  "\<forall>x \<in> clause.vars D. \<V>\<^sub>2 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>2 x)"
  "type_preserving_on (clause.vars E) \<V>\<^sub>1 \<rho>\<^sub>1"
  "type_preserving_on (clause.vars D) \<V>\<^sub>2 \<rho>\<^sub>2"

abbreviation factoring_inferences where
 "factoring_inferences \<equiv> { Infer [D] C | D C. factoring D C }"

abbreviation resolution_inferences where
 "resolution_inferences \<equiv> { Infer [D, E] C | D E C. resolution D E C }"

definition inferences :: "('t, 'v, 'ty) typed_clause inference set" where
 "inferences \<equiv> resolution_inferences \<union> factoring_inferences"

abbreviation bottom\<^sub>F :: "('t, 'v, 'ty) typed_clause set" ("\<bottom>\<^sub>F") where
  "bottom\<^sub>F \<equiv> {(\<V>, {#}) | \<V>. term.exists_nonground \<longrightarrow> infinite_variables_per_type \<V> }"

end

end
