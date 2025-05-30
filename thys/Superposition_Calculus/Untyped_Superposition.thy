theory Untyped_Superposition
  imports Superposition
begin

locale untyped_superposition_calculus =
  nonground_term_with_context where
  term_vars = "term_vars :: 't \<Rightarrow> 'v :: infinite set" and
  term_to_ground = "term_to_ground :: 't \<Rightarrow> 't\<^sub>G" +
  nonground_order where less\<^sub>t = less\<^sub>t +
  nonground_selection_function where
  select = select and atom_subst = "(\<cdot>a)" and atom_vars = atom.vars and
  atom_to_ground = atom.to_ground and atom_from_ground = atom.from_ground +
  (* TODO? *)
  "term": exists_imgu where vars = term_vars and subst = "(\<cdot>t)" and id_subst = Var +
  ground_critical_pairs where
  compose_context = compose_ground_context and apply_context = apply_ground_context and
  hole = ground_hole
  for
    select :: "'t atom select" and
    less\<^sub>t :: "'t \<Rightarrow> 't \<Rightarrow> bool" and
    tiebreakers :: "('t\<^sub>G ground_atom, 't atom) tiebreakers" +
  assumes
    wfp_tiebreakers[iff]: "\<And>C\<^sub>G. wfp (tiebreakers C\<^sub>G)" and
    transp_tiebreakers[iff]: "\<And>C\<^sub>G. transp (tiebreakers C\<^sub>G)"
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

end

end
