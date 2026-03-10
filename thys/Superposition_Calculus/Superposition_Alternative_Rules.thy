theory Superposition_Alternative_Rules
  imports Superposition
begin

context superposition_calculus
begin

subsubsection \<open>Alternative Specification of the Superposition Rule\<close>

inductive superposition' ::
  "('t, 'v, 'ty) typed_clause \<Rightarrow> 
   ('t, 'v, 'ty) typed_clause \<Rightarrow> 
   ('t, 'v, 'ty) typed_clause \<Rightarrow> bool" where
  superposition'I:
   "(term.exists_nonground \<Longrightarrow> infinite_variables_per_type \<V>\<^sub>1) \<Longrightarrow>
    (term.exists_nonground \<Longrightarrow> infinite_variables_per_type \<V>\<^sub>2) \<Longrightarrow>
    term.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    E = add_mset l\<^sub>1 E' \<Longrightarrow>
    D = add_mset l\<^sub>2 D' \<Longrightarrow>
    \<P> \<in> {Pos, Neg} \<Longrightarrow>
    l\<^sub>1 = \<P> (Upair c\<^sub>1\<langle>t\<^sub>1\<rangle> t\<^sub>1') \<Longrightarrow>
    l\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2' \<Longrightarrow>
    \<not> term.is_Var t\<^sub>1 \<Longrightarrow>
    type_preserving_on (clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 \<mu> \<Longrightarrow>
    term.is_imgu \<mu> {{t\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}} \<Longrightarrow>
    \<forall>x \<in> clause.vars E. \<V>\<^sub>1 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>1 x) \<Longrightarrow>
    \<forall>x \<in> clause.vars D. \<V>\<^sub>2 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>2 x) \<Longrightarrow>
    type_preserving_on (clause.vars E) \<V>\<^sub>1 \<rho>\<^sub>1 \<Longrightarrow>
    type_preserving_on (clause.vars D) \<V>\<^sub>2 \<rho>\<^sub>2 \<Longrightarrow>
    (clause.weakly_welltyped \<V>\<^sub>3 C \<Longrightarrow> literal.weakly_welltyped \<V>\<^sub>2 l\<^sub>2) \<Longrightarrow>
    \<not> (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>c D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    (\<P> = Pos \<and> select E = {#} \<and> is_strictly_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>) \<or>
     \<P> = Neg \<and> (select E = {#} \<and> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>) \<or>
                  is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) ((select E) \<cdot> \<rho>\<^sub>1 \<odot> \<mu>))) \<Longrightarrow>
    select D = {#} \<Longrightarrow>
    is_strictly_maximal (l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<mu>) (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    \<not> (c\<^sub>1\<langle>t\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    C = add_mset (\<P> (Upair (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1))) (E' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    superposition' (\<V>\<^sub>2, D) (\<V>\<^sub>1, E) (\<V>\<^sub>3, C)"

lemma superposition_eq_superposition': "superposition = superposition'"
proof (intro ext iffI)
  fix D E C
  assume "superposition D E C"
  then show "superposition' D E C"

  proof (cases D E C rule: superposition.cases)
    case (superpositionI \<P> \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 E D t\<^sub>1 \<V>\<^sub>3 \<mu> t\<^sub>2 c\<^sub>1 t\<^sub>1' t\<^sub>2' l\<^sub>1 l\<^sub>2 C E' D')

    show ?thesis
    proof (unfold superpositionI(1-3), rule superposition'I; (rule superpositionI)?)

      show "\<P> = Pos \<and> select E = {#} \<and> is_strictly_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>) \<or>
       \<P> = Neg \<and> (select E = {#} \<and> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>) \<or>
                   is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (select E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>))"
        using superpositionI
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
    proof (unfold superposition'I(1-3), rule superpositionI; (rule superposition'I)?)

      show
        "\<P> = Pos \<Longrightarrow> select E = {#}"
        "\<P> = Pos \<Longrightarrow> is_strictly_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
        "\<P> = Neg \<Longrightarrow> select E = {#} \<Longrightarrow> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
        "\<P> = Neg \<Longrightarrow> select E \<noteq> {#} \<Longrightarrow> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (select E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
        using superposition'I(23) is_maximal_not_empty
        by auto
    qed
  qed
qed

inductive pos_superposition ::
  "('t, 'v, 'ty) typed_clause \<Rightarrow> ('t, 'v, 'ty) typed_clause \<Rightarrow> ('t, 'v, 'ty) typed_clause \<Rightarrow> bool"
where
  pos_superpositionI:
   "(term.exists_nonground \<Longrightarrow> infinite_variables_per_type \<V>\<^sub>1) \<Longrightarrow>
    (term.exists_nonground \<Longrightarrow> infinite_variables_per_type \<V>\<^sub>2) \<Longrightarrow>
    term.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    E = add_mset l\<^sub>1 E' \<Longrightarrow>
    D = add_mset l\<^sub>2 D' \<Longrightarrow>
    l\<^sub>1 = c\<^sub>1\<langle>t\<^sub>1\<rangle> \<approx> t\<^sub>1' \<Longrightarrow>
    l\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2' \<Longrightarrow>
    \<not> term.is_Var t\<^sub>1 \<Longrightarrow>
    type_preserving_on (clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 \<mu> \<Longrightarrow>
    term.is_imgu \<mu> {{t\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}} \<Longrightarrow>
    \<forall>x \<in> clause.vars E. \<V>\<^sub>1 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>1 x) \<Longrightarrow>
    \<forall>x \<in> clause.vars D. \<V>\<^sub>2 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>2 x) \<Longrightarrow>
    type_preserving_on (clause.vars E) \<V>\<^sub>1 \<rho>\<^sub>1 \<Longrightarrow>
    type_preserving_on (clause.vars D) \<V>\<^sub>2 \<rho>\<^sub>2 \<Longrightarrow>
    (clause.weakly_welltyped \<V>\<^sub>3 C \<Longrightarrow> literal.weakly_welltyped \<V>\<^sub>2 l\<^sub>2) \<Longrightarrow>
    \<not> (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>c D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    select E = {#} \<Longrightarrow>
    is_strictly_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>) \<Longrightarrow>
    select D = {#} \<Longrightarrow>
    is_strictly_maximal (l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<mu>) (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    \<not> (c\<^sub>1\<langle>t\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    C = add_mset ((c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> \<approx> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1)) (E' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    pos_superposition (\<V>\<^sub>2, D) (\<V>\<^sub>1, E) (\<V>\<^sub>3, C)"

lemma superposition_if_pos_superposition:
  assumes "pos_superposition D E C"
  shows "superposition D E C"
  using assms
proof (cases rule: pos_superposition.cases)
  case (pos_superpositionI \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 E D l\<^sub>1 E' l\<^sub>2 D' c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<V>\<^sub>3 \<mu> C)

  then show ?thesis
    using superpositionI[of Pos \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 E D t\<^sub>1 \<V>\<^sub>3 \<mu> t\<^sub>2 c\<^sub>1 t\<^sub>1' t\<^sub>2' l\<^sub>1 l\<^sub>2 C E' D']
    by blast
qed

inductive neg_superposition ::
  "('t, 'v, 'ty) typed_clause \<Rightarrow> ('t, 'v, 'ty) typed_clause \<Rightarrow> ('t, 'v, 'ty) typed_clause \<Rightarrow> bool"
where
  neg_superpositionI:
   "(term.exists_nonground \<Longrightarrow> infinite_variables_per_type \<V>\<^sub>1) \<Longrightarrow>
    (term.exists_nonground \<Longrightarrow> infinite_variables_per_type \<V>\<^sub>2) \<Longrightarrow>
    term.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    E = add_mset l\<^sub>1 E' \<Longrightarrow>
    D = add_mset l\<^sub>2 D' \<Longrightarrow>
    l\<^sub>1 = c\<^sub>1\<langle>t\<^sub>1\<rangle> !\<approx> t\<^sub>1' \<Longrightarrow>
    l\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2' \<Longrightarrow>
    \<not> term.is_Var t\<^sub>1 \<Longrightarrow>
    type_preserving_on (clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 \<mu> \<Longrightarrow>
    term.is_imgu \<mu> {{t\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}} \<Longrightarrow>
    \<forall>x \<in> clause.vars E. \<V>\<^sub>1 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>1 x) \<Longrightarrow>
    \<forall>x \<in> clause.vars D. \<V>\<^sub>2 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>2 x) \<Longrightarrow>
    type_preserving_on (clause.vars E) \<V>\<^sub>1 \<rho>\<^sub>1 \<Longrightarrow>
    type_preserving_on (clause.vars D) \<V>\<^sub>2 \<rho>\<^sub>2 \<Longrightarrow>
    (clause.weakly_welltyped \<V>\<^sub>3 C \<Longrightarrow> literal.weakly_welltyped \<V>\<^sub>2 l\<^sub>2) \<Longrightarrow>
    \<not> (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>c D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    (select E = {#} \<Longrightarrow> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)) \<Longrightarrow>
    (select E \<noteq> {#} \<Longrightarrow> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) ((select E) \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)) \<Longrightarrow>
    select D = {#} \<Longrightarrow>
    is_strictly_maximal (l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<mu>) (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    \<not> (c\<^sub>1\<langle>t\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    C = add_mset ((c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> !\<approx> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1)) (E' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    neg_superposition (\<V>\<^sub>2, D) (\<V>\<^sub>1, E) (\<V>\<^sub>3, C)"

lemma superposition_if_neg_superposition:
  assumes "neg_superposition E D C"
  shows "superposition E D C"
  using assms
proof (cases E D C rule: neg_superposition.cases)
  case (neg_superpositionI \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 E D l\<^sub>1 E' l\<^sub>2 D' c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<V>\<^sub>3 \<mu> C)
 
  then show ?thesis
    using
      superpositionI[of Neg \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 E D t\<^sub>1 \<V>\<^sub>3 \<mu> t\<^sub>2 c\<^sub>1 t\<^sub>1' t\<^sub>2' l\<^sub>1 l\<^sub>2 C E' D']
      literals_distinct(2)
    by blast
qed

lemma superposition_iff_pos_or_neg:
  "superposition D E C \<longleftrightarrow> pos_superposition D E C \<or> neg_superposition D E C"
proof (rule iffI)
  assume "superposition D E C"
  thus "pos_superposition D E C \<or> neg_superposition D E C"
  proof (cases D E C rule: superposition.cases)
    case (superpositionI \<P> \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 E D t\<^sub>1 \<V>\<^sub>3 \<mu> t\<^sub>2 c\<^sub>1 t\<^sub>1' t\<^sub>2' l\<^sub>1 l\<^sub>2 C E' D')

    show ?thesis
    proof(cases "\<P> = Pos")
      case True

      then show ?thesis
        using
          superpositionI
          pos_superpositionI[of \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 E D l\<^sub>1 E' l\<^sub>2 D' c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<V>\<^sub>3 \<mu> C]
        unfolding superpositionI(1-3)
        by argo
    next
      case False

      then show ?thesis
        using
          superpositionI
          neg_superpositionI[of \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 E D l\<^sub>1 E' l\<^sub>2 D' c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<V>\<^sub>3 \<mu> C]
        using superpositionI(4)
        unfolding superpositionI(1-3)
        by blast
    qed
  qed
next
  assume "pos_superposition D E C \<or> neg_superposition D E C"

  thus "superposition D E C"
    using superposition_if_neg_superposition superposition_if_pos_superposition
    by fast
qed

end

end
