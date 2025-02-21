theory Superposition
  imports
    First_Order_Clause.Nonground_Order
    First_Order_Clause.Nonground_Selection_Function
    First_Order_Clause.Nonground_Typing
    First_Order_Clause.Typed_Tiebreakers
    First_Order_Clause.Welltyped_IMGU

    Ground_Superposition
begin


section \<open>Nonground Layer\<close>

locale superposition_calculus =
  nonground_inhabited_typing \<F> +
  nonground_equality_order less\<^sub>t +
  nonground_selection_function select +
  typed_tiebreakers tiebreakers +
  ground_critical_pair_theorem "TYPE('f)"
  for
    select :: "('f, 'v :: infinite) select" and
    less\<^sub>t :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" and
    \<F> :: "('f, 'ty) fun_types" and
    tiebreakers :: "('f, 'v) tiebreakers" +
  assumes
    types_ordLeq_variables: "|UNIV :: 'ty set| \<le>o |UNIV :: 'v set|"
begin

interpretation term_order_notation.

inductive eq_resolution :: "('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool" where
  eq_resolutionI:
   "D = add_mset l D' \<Longrightarrow>
    l = t !\<approx> t' \<Longrightarrow>
    welltyped_imgu_on (clause.vars D) \<V> t t' \<mu> \<Longrightarrow>
    select D = {#} \<and> is_maximal (l \<cdot>l \<mu>) (D \<cdot> \<mu>) \<or> is_maximal (l \<cdot>l \<mu>) (select D \<cdot> \<mu>) \<Longrightarrow>
    C = D' \<cdot> \<mu> \<Longrightarrow>
    eq_resolution (D, \<V>) (C, \<V>)"

inductive eq_factoring :: "('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool" where
  eq_factoringI:
   "D = add_mset l\<^sub>1 (add_mset l\<^sub>2 D') \<Longrightarrow>
    l\<^sub>1 = t\<^sub>1 \<approx> t\<^sub>1' \<Longrightarrow>
    l\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2' \<Longrightarrow>
    select D = {#} \<Longrightarrow>
    is_maximal (l\<^sub>1 \<cdot>l \<mu>) (D \<cdot> \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>1' \<cdot>t \<mu>) \<Longrightarrow>
    welltyped_imgu_on (clause.vars D) \<V> t\<^sub>1 t\<^sub>2 \<mu> \<Longrightarrow>
    C = add_mset (t\<^sub>1 \<approx> t\<^sub>2') (add_mset (t\<^sub>1' !\<approx> t\<^sub>2') D') \<cdot> \<mu> \<Longrightarrow>
    eq_factoring (D, \<V>) (C, \<V>)"

inductive superposition ::
  "('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool"
where
  superpositionI:
   "infinite_variables_per_type \<V>\<^sub>1 \<Longrightarrow>
    infinite_variables_per_type \<V>\<^sub>2 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    E = add_mset l\<^sub>1 E' \<Longrightarrow>
    D = add_mset l\<^sub>2 D' \<Longrightarrow>
    \<P> \<in> {Pos, Neg} \<Longrightarrow>
    l\<^sub>1 = \<P> (Upair c\<^sub>1\<langle>t\<^sub>1\<rangle> t\<^sub>1') \<Longrightarrow>
    l\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2' \<Longrightarrow>
    \<not> is_Var t\<^sub>1 \<Longrightarrow>
    welltyped_imgu_on (clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 (t\<^sub>1 \<cdot>t \<rho>\<^sub>1) (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu> \<Longrightarrow>
    \<forall>x \<in> clause.vars E. \<V>\<^sub>1 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>1 x) \<Longrightarrow>
    \<forall>x \<in> clause.vars D. \<V>\<^sub>2 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>2 x) \<Longrightarrow>
    term.subst.is_welltyped_on (clause.vars E) \<V>\<^sub>1 \<rho>\<^sub>1 \<Longrightarrow>
    term.subst.is_welltyped_on (clause.vars D) \<V>\<^sub>2 \<rho>\<^sub>2 \<Longrightarrow>
    (\<And>\<tau> \<tau>'. typed \<V>\<^sub>2 t\<^sub>2 \<tau> \<Longrightarrow> typed \<V>\<^sub>2 t\<^sub>2' \<tau>' \<Longrightarrow> \<tau> = \<tau>') \<Longrightarrow>
    \<not> (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>c D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    (\<P> = Pos \<Longrightarrow> select E = {#}) \<Longrightarrow>
    (\<P> = Pos \<Longrightarrow> is_strictly_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)) \<Longrightarrow>
    (\<P> = Neg \<Longrightarrow> select E = {#} \<Longrightarrow> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)) \<Longrightarrow>
    (\<P> = Neg \<Longrightarrow> select E \<noteq> {#} \<Longrightarrow> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) ((select E) \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)) \<Longrightarrow>
    select D = {#} \<Longrightarrow>
    is_strictly_maximal (l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<mu>) (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    \<not> (c\<^sub>1\<langle>t\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    C = add_mset (\<P> (Upair (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1))) (E' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    superposition (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C, \<V>\<^sub>3)"

abbreviation eq_factoring_inferences where
  "eq_factoring_inferences \<equiv> { Infer [D] C | D C. eq_factoring D C }"

abbreviation eq_resolution_inferences where
  "eq_resolution_inferences \<equiv> { Infer [D] C | D C. eq_resolution D C }"

abbreviation superposition_inferences where
  "superposition_inferences \<equiv> { Infer [D, E] C | D E C. superposition D E C}"

definition inferences :: "('f, 'v, 'ty) typed_clause inference set" where
  "inferences \<equiv> superposition_inferences \<union> eq_resolution_inferences \<union> eq_factoring_inferences"

abbreviation bottom\<^sub>F :: "('f, 'v, 'ty) typed_clause set" ("\<bottom>\<^sub>F") where
  "bottom\<^sub>F \<equiv> {({#}, \<V>) | \<V>. infinite_variables_per_type \<V> }"

subsubsection \<open>Alternative Specification of the Superposition Rule\<close>

inductive superposition' ::
  "('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool"
where
  superposition'I:
   "infinite_variables_per_type \<V>\<^sub>1 \<Longrightarrow>
    infinite_variables_per_type \<V>\<^sub>2 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    E = add_mset l\<^sub>1 E' \<Longrightarrow>
    D = add_mset l\<^sub>2 D' \<Longrightarrow>
    \<P> \<in> {Pos, Neg} \<Longrightarrow>
    l\<^sub>1 = \<P> (Upair c\<^sub>1\<langle>t\<^sub>1\<rangle> t\<^sub>1') \<Longrightarrow>
    l\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2' \<Longrightarrow>
    \<not> is_Var t\<^sub>1 \<Longrightarrow>
    welltyped_imgu_on (clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 (t\<^sub>1 \<cdot>t \<rho>\<^sub>1) (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu> \<Longrightarrow>
    \<forall>x \<in> clause.vars E. \<V>\<^sub>1 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>1 x) \<Longrightarrow>
    \<forall>x \<in> clause.vars D. \<V>\<^sub>2 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>2 x) \<Longrightarrow>
    term.subst.is_welltyped_on (clause.vars E) \<V>\<^sub>1 \<rho>\<^sub>1 \<Longrightarrow>
    term.subst.is_welltyped_on (clause.vars D) \<V>\<^sub>2 \<rho>\<^sub>2 \<Longrightarrow>
    (\<And>\<tau> \<tau>'. typed \<V>\<^sub>2 t\<^sub>2 \<tau> \<Longrightarrow> typed \<V>\<^sub>2 t\<^sub>2' \<tau>' \<Longrightarrow> \<tau> = \<tau>') \<Longrightarrow>
    \<not> (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>c D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    (\<P> = Pos \<and> select E = {#} \<and> is_strictly_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>) \<or>
     \<P> = Neg \<and> (select E = {#} \<and> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>) \<or>
                  is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) ((select E) \<cdot> \<rho>\<^sub>1 \<odot> \<mu>))) \<Longrightarrow>
    select D = {#} \<Longrightarrow>
    is_strictly_maximal (l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<mu>) (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    \<not> (c\<^sub>1\<langle>t\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    C = add_mset (\<P> (Upair (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1))) (E' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    superposition' (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C, \<V>\<^sub>3)"

lemma superposition_eq_superposition': "superposition = superposition'"
proof (intro ext iffI)
  fix D E C
  assume "superposition D E C"
  then show "superposition' D E C"

  proof (cases D E C rule: superposition.cases)
    case (superpositionI \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 E D l\<^sub>1 E' l\<^sub>2 D' \<P> c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<V>\<^sub>3 \<mu> C)

    show ?thesis
    proof (unfold superpositionI(1-3), rule superposition'I[of \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2]; (rule superpositionI)?)

      show "\<P> = Pos \<and> select E = {#} \<and> is_strictly_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>) \<or>
       \<P> = Neg \<and> (select E = {#} \<and> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>) \<or>
                   is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (select E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>))"
        using superpositionI(11,22-25)
        by fastforce
    qed
  qed
next
  fix D E C
  assume "superposition' D E C"
  then show "superposition D E C"
  proof (cases D E C rule: superposition'.cases)
    case (superposition'I \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 E D l\<^sub>1 E' l\<^sub>2 D' \<P> c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<V>\<^sub>3 \<mu> C)

    show ?thesis
    proof (unfold superposition'I(1-3), rule superpositionI[of \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2]; (rule superposition'I)?)

      show
        "\<P> = Pos \<Longrightarrow> select E = {#}"
        "\<P> = Pos \<Longrightarrow> is_strictly_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
        "\<P> = Neg \<Longrightarrow> select E = {#} \<Longrightarrow> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
        "\<P> = Neg \<Longrightarrow> select E \<noteq> {#} \<Longrightarrow> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (select E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
        using superposition'I(22) is_maximal_not_empty
        by auto
    qed
  qed
qed

inductive pos_superposition ::
  "('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool"
where
  pos_superpositionI:
   "infinite_variables_per_type \<V>\<^sub>1 \<Longrightarrow>
    infinite_variables_per_type \<V>\<^sub>2 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    E = add_mset l\<^sub>1 E' \<Longrightarrow>
    D = add_mset l\<^sub>2 D' \<Longrightarrow>
    l\<^sub>1 = c\<^sub>1\<langle>t\<^sub>1\<rangle> \<approx> t\<^sub>1' \<Longrightarrow>
    l\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2' \<Longrightarrow>
    \<not> is_Var t\<^sub>1 \<Longrightarrow>
    welltyped_imgu_on (clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 (t\<^sub>1 \<cdot>t \<rho>\<^sub>1) (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu> \<Longrightarrow>
    \<forall>x \<in> clause.vars E. \<V>\<^sub>1 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>1 x) \<Longrightarrow>
    \<forall>x \<in> clause.vars D. \<V>\<^sub>2 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>2 x) \<Longrightarrow>
    term.subst.is_welltyped_on (clause.vars E) \<V>\<^sub>1 \<rho>\<^sub>1 \<Longrightarrow>
    term.subst.is_welltyped_on (clause.vars D) \<V>\<^sub>2 \<rho>\<^sub>2 \<Longrightarrow>
    (\<And>\<tau> \<tau>'. typed \<V>\<^sub>2 t\<^sub>2 \<tau> \<Longrightarrow> typed \<V>\<^sub>2 t\<^sub>2' \<tau>' \<Longrightarrow> \<tau> = \<tau>') \<Longrightarrow>
    \<not> (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>c D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    select E = {#} \<Longrightarrow>
    is_strictly_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>) \<Longrightarrow>
    select D = {#} \<Longrightarrow>
    is_strictly_maximal (l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<mu>) (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    \<not> (c\<^sub>1\<langle>t\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    C = add_mset ((c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> \<approx> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1)) (E' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    pos_superposition (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C, \<V>\<^sub>3)"

lemma superposition_if_pos_superposition:
  assumes "pos_superposition D E C"
  shows "superposition D E C"
  using assms
proof (cases rule: pos_superposition.cases)
  case (pos_superpositionI \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 E D l\<^sub>1 E' l\<^sub>2 D' c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu> \<V>\<^sub>3  C)
  then show ?thesis
    using superpositionI[of \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 E D l\<^sub>1 E' l\<^sub>2 D' Pos c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu> \<V>\<^sub>3 C]
    by fast
qed

inductive neg_superposition ::
  "('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool"
where
  neg_superpositionI:
   "infinite_variables_per_type \<V>\<^sub>1 \<Longrightarrow>
    infinite_variables_per_type \<V>\<^sub>2 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    E = add_mset l\<^sub>1 E' \<Longrightarrow>
    D = add_mset l\<^sub>2 D' \<Longrightarrow>
    l\<^sub>1 = c\<^sub>1\<langle>t\<^sub>1\<rangle> !\<approx> t\<^sub>1' \<Longrightarrow>
    l\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2' \<Longrightarrow>
    \<not> is_Var t\<^sub>1 \<Longrightarrow>
    welltyped_imgu_on (clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 (t\<^sub>1 \<cdot>t \<rho>\<^sub>1) (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu> \<Longrightarrow>
    \<forall>x \<in> clause.vars E. \<V>\<^sub>1 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>1 x) \<Longrightarrow>
    \<forall>x \<in> clause.vars D. \<V>\<^sub>2 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>2 x) \<Longrightarrow>
    term.subst.is_welltyped_on (clause.vars E) \<V>\<^sub>1 \<rho>\<^sub>1 \<Longrightarrow>
    term.subst.is_welltyped_on (clause.vars D) \<V>\<^sub>2 \<rho>\<^sub>2 \<Longrightarrow>
    (\<And>\<tau> \<tau>'. typed \<V>\<^sub>2 t\<^sub>2 \<tau> \<Longrightarrow> typed \<V>\<^sub>2 t\<^sub>2' \<tau>' \<Longrightarrow> \<tau> = \<tau>') \<Longrightarrow>
    \<not> (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>c D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    (select E = {#} \<Longrightarrow> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)) \<Longrightarrow>
    (select E \<noteq> {#} \<Longrightarrow> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) ((select E) \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)) \<Longrightarrow>
    select D = {#} \<Longrightarrow>
    is_strictly_maximal (l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<mu>) (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    \<not> (c\<^sub>1\<langle>t\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    C = add_mset ((c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> !\<approx> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1)) (E' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    neg_superposition (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C, \<V>\<^sub>3)"

lemma superposition_if_neg_superposition:
  assumes "neg_superposition E D C"
  shows "superposition E D C"
  using assms
proof (cases E D C rule: neg_superposition.cases)
  case (neg_superpositionI \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 E D l\<^sub>1 E' l\<^sub>2 D' c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu> \<V>\<^sub>3 C)
  then show ?thesis
    using
      superpositionI[of \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 E D l\<^sub>1 E' l\<^sub>2 D' Neg c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu> \<V>\<^sub>3 C]
      literals_distinct(2)
    by blast
qed

lemma superposition_iff_pos_or_neg:
  "superposition D E C \<longleftrightarrow> pos_superposition D E C \<or> neg_superposition D E C"
proof (rule iffI)
  assume "superposition D E C"
  thus "pos_superposition D E C \<or> neg_superposition D E C"
  proof (cases D E C rule: superposition.cases)
    case (superpositionI \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 E D l\<^sub>1 E' l\<^sub>2 D' \<P> c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<V>\<^sub>3 \<mu> C)

    show ?thesis
    proof(cases "\<P> = Pos")
      case True
      then have "pos_superposition (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C, \<V>\<^sub>3)"
        using
          superpositionI
          pos_superpositionI[of \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 E D l\<^sub>1 E' l\<^sub>2 D' c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<V>\<^sub>3 \<mu> C]
        by argo

      then show ?thesis
        unfolding superpositionI(1-3)
        by simp

    next
      case False

      then have "\<P> = Neg"
        using superpositionI(11)
        by blast

      then have "neg_superposition (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C, \<V>\<^sub>3)"
        using
          superpositionI
          neg_superpositionI[of \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 E D l\<^sub>1 E' l\<^sub>2 D' c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<V>\<^sub>3 \<mu> C]
        by argo

      then show ?thesis
        unfolding superpositionI(1-3)
        by simp
    qed
  qed
next
  assume "pos_superposition D E C \<or> neg_superposition D E C"
  thus "superposition D E C"
    using superposition_if_neg_superposition superposition_if_pos_superposition
    by metis
qed

end

end
