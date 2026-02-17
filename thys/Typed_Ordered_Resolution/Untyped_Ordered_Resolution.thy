theory Untyped_Ordered_Resolution
  imports
    First_Order_Clause.Nonground_Order
    First_Order_Clause.Nonground_Selection_Function
    First_Order_Clause.Tiebreakers
    First_Order_Clause.Infinite_Variables
begin

locale untyped_ordered_resolution_calculus =
  nonground_order where
  less\<^sub>t = less\<^sub>t and id_subst = id_subst and term_from_ground = "term_from_ground :: 't\<^sub>G \<Rightarrow> 't" and
  term_vars = term_vars +

  nonground_selection_function where
  select = select and atom_subst = "(\<cdot>t)" and atom_vars = term.vars and term_vars = term_vars and
  atom_from_ground = term.from_ground and atom_to_ground = term.to_ground and
  atom_is_ground = term.is_ground and id_subst = id_subst +

  tiebreakers tiebreakers +

  "term": exists_imgu where
  vars = term_vars and subst = "(\<cdot>t)" and id_subst = id_subst and is_ground = term_is_ground +

  infinite_variables where
  variables = "UNIV :: 'v set" and exists_nonground = term.exists_nonground +

  (* TODO: *)
  subst_eq where
  vars = term_vars and subst = "(\<cdot>t)" and is_ground = term_is_ground and id_subst = id_subst +
  vars_grounded_iff_is_grounding where 
  vars = term_vars and subst = "(\<cdot>t)" and is_ground = term_is_ground and id_subst = id_subst and
  base_vars = term_vars and base_subst = "(\<cdot>t)" and base_is_ground = term_is_ground +
  subst_updates_compat where
  vars = term_vars and subst = "(\<cdot>t)" and is_ground = term_is_ground and id_subst = id_subst
for
  select :: "'t select" and
  less\<^sub>t :: "'t \<Rightarrow> 't \<Rightarrow> bool" and
  tiebreakers :: "('t\<^sub>G, 't) tiebreakers" and
  id_subst :: 'subst and
  term_vars :: "'t \<Rightarrow> 'v set"
begin

inductive factoring :: "'t clause \<Rightarrow> 't clause \<Rightarrow> bool" where
  factoringI: 
  "D = add_mset l\<^sub>1 (add_mset l\<^sub>2 D') \<Longrightarrow>
   l\<^sub>1 = Pos t\<^sub>1 \<Longrightarrow>
   l\<^sub>2 = Pos t\<^sub>2 \<Longrightarrow>
   C = (add_mset l\<^sub>1 D') \<cdot> \<mu> \<Longrightarrow>
   factoring D C"
if
  "select D = {#}"
  "is_maximal (l\<^sub>1 \<cdot>l \<mu>) (D \<cdot> \<mu>)"
  "term.is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}}"

inductive resolution :: "'t clause \<Rightarrow> 't clause \<Rightarrow> 't clause \<Rightarrow> bool" where
  resolutionI: 
  "E = add_mset l\<^sub>1 E' \<Longrightarrow>
   D = add_mset l\<^sub>2 D' \<Longrightarrow>
   l\<^sub>1 = Neg t\<^sub>1 \<Longrightarrow>
   l\<^sub>2 = Pos t\<^sub>2 \<Longrightarrow>
   C = (E' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
   resolution D E C"
 if
  "term.is_renaming \<rho>\<^sub>1"
  "term.is_renaming \<rho>\<^sub>2"
  "clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {}"
  "term.is_imgu \<mu> {{t\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}}"
  "\<not> (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>c D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>)"
  "select E = {#} \<Longrightarrow> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
  "select E \<noteq> {#} \<Longrightarrow> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (select E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
  "select D = {#}"
  "is_strictly_maximal (l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<mu>) (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>)"

abbreviation factoring_inferences where
 "factoring_inferences \<equiv> { Infer [D] C | D C. factoring D C }"

abbreviation resolution_inferences where
 "resolution_inferences \<equiv> { Infer [D, E] C | D E C. resolution D E C }"

definition inferences :: "'t clause inference set" where
"inferences \<equiv> resolution_inferences \<union> factoring_inferences"

abbreviation bottom :: "'t clause set" where
  "bottom \<equiv> {{#}}"

end

end
