theory Untyped_Ordered_Resolution
   imports 
    First_Order_Clause.Nonground_Order
    First_Order_Clause.Nonground_Selection_Function
    First_Order_Clause.Tiebreakers

    Fresh_Identifiers.Fresh
begin

locale untyped_ordered_resolution_calculus =
  nonground_order where
  less\<^sub>t = less\<^sub>t and Var = Var and term_from_ground = "term_from_ground :: 't\<^sub>G \<Rightarrow> 't" +

  nonground_selection_function where
  select = select and atom_subst = "(\<cdot>t)" and atom_vars = term.vars and
  atom_from_ground = term.from_ground and atom_to_ground = term.to_ground and Var = Var +

  tiebreakers tiebreakers +
  (* TODO? *)
  "term": exists_imgu where vars = term_vars and subst = "(\<cdot>t)" and id_subst = Var
for
  select :: "'t select" and
  less\<^sub>t :: "'t \<Rightarrow> 't \<Rightarrow> bool" and
  tiebreakers :: "('t\<^sub>G, 't) tiebreakers" and
  Var :: "'v :: infinite \<Rightarrow> 't" 
begin

(* TODO: Names of Clauses *)
inductive factoring :: "'t clause \<Rightarrow> 't clause \<Rightarrow> bool"
where
  factoringI: 
  "C = add_mset L\<^sub>1 (add_mset L\<^sub>2 C') \<Longrightarrow>
  L\<^sub>1 = (Pos t\<^sub>1) \<Longrightarrow>
  L\<^sub>2 = (Pos t\<^sub>2) \<Longrightarrow>
  D = (add_mset L\<^sub>1 C') \<cdot> \<mu> \<Longrightarrow>
  factoring C D"
if
  "select C = {#}"
  "is_maximal (L\<^sub>1 \<cdot>l \<mu>) (C \<cdot> \<mu>)"
  "term.is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}}"

inductive resolution :: "'t clause \<Rightarrow> 't clause \<Rightarrow> 't clause \<Rightarrow> bool"
where
  resolutionI: 
   "C = add_mset L\<^sub>1 C' \<Longrightarrow>
    D = add_mset L\<^sub>2 D' \<Longrightarrow>
    L\<^sub>1 = (Neg t\<^sub>1) \<Longrightarrow>
    L\<^sub>2 = (Pos t\<^sub>2) \<Longrightarrow>
    R = (C' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    resolution D C R"
 if
  "term.is_renaming \<rho>\<^sub>1"
  "term.is_renaming \<rho>\<^sub>2"
  "clause.vars (C \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {}"
  "term.is_imgu \<mu> {{t\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}}"
  "\<not> (C \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>c D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>)"
  "select C = {#} \<Longrightarrow> is_maximal (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (C \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
  "select C \<noteq> {#} \<Longrightarrow> is_maximal (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) ((select C) \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
  "select D = {#}"
  "is_strictly_maximal (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<mu>) (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>)"

abbreviation factoring_inferences where
 "factoring_inferences \<equiv> { Infer [C] D | C D. factoring C D}"

abbreviation resolution_inferences where
 "resolution_inferences \<equiv> { Infer [D, C] R | D C R. resolution D C R}"

definition inferences :: "'t clause inference set" where
"inferences \<equiv> resolution_inferences \<union> factoring_inferences"

abbreviation bottom :: "'t clause set" where
  "bottom \<equiv> {{#}}"

end

end