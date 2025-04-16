theory Untyped_Superposition
  imports Superposition
begin

locale untyped_superposition_calculus =
  nonground_order less\<^sub>t +
  nonground_selection_function where
  select = select and atom_subst = "(\<cdot>a)" and atom_vars = atom.vars and
  atom_to_ground = atom.to_ground and atom_from_ground = atom.from_ground +
  ground_critical_pair_theorem "TYPE('f)"
  for
    select :: "('f, 'v :: infinite) atom select" and
    less\<^sub>t :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" and
    tiebreakers :: "('f ground_atom, ('f, 'v) atom) tiebreakers" +
  assumes
    wfp_tiebreakers[iff]: "\<And>C\<^sub>G. wfp (tiebreakers C\<^sub>G)" and
    transp_tiebreakers[iff]: "\<And>C\<^sub>G. transp (tiebreakers C\<^sub>G)"
begin

interpretation term_order_notation.

inductive eq_resolution :: "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
  eq_resolutionI:
  "D = add_mset l D' \<Longrightarrow>
   l = t !\<approx> t' \<Longrightarrow>
   C = D' \<cdot> \<mu> \<Longrightarrow>
   eq_resolution D C"
if 
  "term_subst.is_imgu \<mu> {{t, t'}}"
  "select D = {#} \<Longrightarrow> is_maximal (l \<cdot>l \<mu>) (D \<cdot> \<mu>)"
  "select D \<noteq> {#} \<Longrightarrow> is_maximal (l \<cdot>l \<mu>) (select D \<cdot> \<mu>)"

inductive eq_factoring :: "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
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
  "term_subst.is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}}"

inductive superposition ::
  "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
  superpositionI:
  "E = add_mset l\<^sub>1 E' \<Longrightarrow>
   D = add_mset l\<^sub>2 D' \<Longrightarrow>
   l\<^sub>1 = \<P> (Upair c\<^sub>1\<langle>t\<^sub>1\<rangle> t\<^sub>1') \<Longrightarrow>
   l\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2' \<Longrightarrow>
   C = add_mset (\<P> (Upair (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1))) (E' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
   superposition D E C"
if
  "\<P> \<in> {Pos, Neg}"
  "term_subst.is_renaming \<rho>\<^sub>1"
  "term_subst.is_renaming \<rho>\<^sub>2"
  "clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {}"
  "\<not> is_Var t\<^sub>1"
  "term_subst.is_imgu \<mu> {{t\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}}"
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
