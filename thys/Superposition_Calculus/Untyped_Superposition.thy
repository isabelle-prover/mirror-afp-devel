theory Untyped_Superposition
  imports 
    First_Order_Clause.Nonground_Order_With_Equality
    First_Order_Clause.Nonground_Selection_Function
    First_Order_Clause.Tiebreakers
    First_Order_Clause.Infinite_Variables

    Ground_Term_Context
begin

locale untyped_superposition_calculus =
  nonground_term_with_context where
  term_vars = "term_vars :: 't \<Rightarrow> 'v set" and
  term_to_ground = "term_to_ground :: 't \<Rightarrow> 't\<^sub>G" +

  context_compatible_nonground_order where less\<^sub>t = less\<^sub>t +

  nonground_selection_function where
  select = select and atom_subst = "(\<cdot>a)" and atom_vars = atom.vars and
  atom_is_ground = atom.is_ground and atom_to_ground = atom.to_ground and
  atom_from_ground = atom.from_ground +

  "term": exists_imgu where vars = term_vars and subst = "(\<cdot>t)" and is_ground = term_is_ground +

  infinite_variables where
  variables = "UNIV :: 'v set" and exists_nonground = term.exists_nonground +

  ground_term_context' +

  tiebreakers tiebreakers +

  (* TODO: *)
  subst_eq where vars = term_vars and subst = "(\<cdot>t)" and is_ground = term_is_ground +
  vars_grounded_iff_is_grounding where 
  vars = term_vars and subst = "(\<cdot>t)" and is_ground = term_is_ground and base_vars = term_vars and 
  base_subst = "(\<cdot>t)" and base_is_ground = term_is_ground +
  subst_updates_compat where vars = term_vars and subst = "(\<cdot>t)" and is_ground = term_is_ground
  for
    select :: "'t atom select" and
    less\<^sub>t :: "'t \<Rightarrow> 't \<Rightarrow> bool" and
    tiebreakers :: "('t\<^sub>G atom, 't atom) tiebreakers" 
begin

interpretation term_order_notation .

inductive eq_resolution :: "'t clause \<Rightarrow> 't clause \<Rightarrow> bool" where
  eq_resolutionI:
  "D = add_mset l D' \<Longrightarrow>
   l = t !\<approx> t' \<Longrightarrow>
   C = D' \<cdot> \<mu> \<Longrightarrow>
   eq_resolution D C"
if 
  "term.is_imgu \<mu> {{t, t'}}"
  "select D = {#} \<Longrightarrow> is_maximal (l \<cdot>l \<mu>) (D \<cdot> \<mu>)"
  "select D \<noteq> {#} \<Longrightarrow> is_maximal (l \<cdot>l \<mu>) (select D \<cdot> \<mu>)"

inductive eq_factoring :: "'t clause \<Rightarrow> 't clause \<Rightarrow> bool" where
  eq_factoringI:
  "D = add_mset l\<^sub>1 (add_mset l\<^sub>2 D') \<Longrightarrow>
   l\<^sub>1 = t\<^sub>1 \<approx> t\<^sub>1' \<Longrightarrow>
   l\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2' \<Longrightarrow>
   C = add_mset (t\<^sub>1 \<approx> t\<^sub>2') (add_mset (t\<^sub>1' !\<approx> t\<^sub>2') D') \<cdot> \<mu> \<Longrightarrow>
   eq_factoring D C"
if
  "select D = {#}"
  "is_maximal (l\<^sub>1 \<cdot>l \<mu>) (D \<cdot> \<mu>)"
  "\<not> (t\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>1' \<cdot>t \<mu>)"
  "term.is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}}"

inductive superposition :: "'t clause \<Rightarrow> 't clause \<Rightarrow> 't clause \<Rightarrow> bool" where
  superpositionI:
  "E = add_mset l\<^sub>1 E' \<Longrightarrow>
   D = add_mset l\<^sub>2 D' \<Longrightarrow>
   l\<^sub>1 = \<P> (Upair c\<^sub>1\<langle>t\<^sub>1\<rangle> t\<^sub>1') \<Longrightarrow>
   l\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2' \<Longrightarrow>
   C = add_mset (\<P> (Upair (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1))) (E' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
   superposition D E C"
if
  "\<P> \<in> {Pos, Neg}"
  "term.is_renaming \<rho>\<^sub>1"
  "term.is_renaming \<rho>\<^sub>2"
  "clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {}"
  "\<not> term.is_Var t\<^sub>1"
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

abbreviation eq_factoring_inferences where
  "eq_factoring_inferences \<equiv> { Infer [D] C | D C. eq_factoring D C }"

abbreviation eq_resolution_inferences where
  "eq_resolution_inferences \<equiv> { Infer [D] C | D C. eq_resolution D C }"

abbreviation superposition_inferences where
  "superposition_inferences \<equiv> { Infer [D, E] C | D E C. superposition D E C }"

definition inferences :: "'t clause inference set" where
  "inferences \<equiv> superposition_inferences \<union> eq_resolution_inferences \<union> eq_factoring_inferences"

abbreviation bottom :: "'t clause set" where
  "bottom \<equiv> {{#}}"

end

end
