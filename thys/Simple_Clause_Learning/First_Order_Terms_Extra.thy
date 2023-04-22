theory First_Order_Terms_Extra
  imports
    "First_Order_Terms.Term"
    "First_Order_Terms.Option_Monad"
    "First_Order_Terms.Unification"
begin

section \<open>Term\<close>

lemma inj_on_Var[simp]:
  "inj_on Var A"
  by (rule inj_onI) simp

lemma member_image_the_Var_image_subst:
  assumes is_var_\<sigma>: "\<forall>x. is_Var (\<sigma> x)"
  shows "x \<in> the_Var ` \<sigma> ` V \<longleftrightarrow> Var x \<in> \<sigma> ` V"
  using is_var_\<sigma> image_iff
  by (metis (no_types, opaque_lifting) term.collapse(1) term.sel(1))

lemma image_the_Var_image_subst_renaming_eq:
  assumes is_var_\<sigma>: "\<forall>x. is_Var (\<rho> x)"
  shows "the_Var ` \<rho> ` V = (\<Union>x \<in> V. vars_term (\<rho> x))"
proof (rule Set.equalityI; rule Set.subsetI)
  from is_var_\<sigma> show "\<And>x. x \<in> the_Var ` \<rho> ` V \<Longrightarrow> x \<in> (\<Union>x\<in>V. vars_term (\<rho> x))"
    using term.set_sel(3) by force
next
  from is_var_\<sigma> show "\<And>x. x \<in> (\<Union>x\<in>V. vars_term (\<rho> x)) \<Longrightarrow> x \<in> the_Var ` \<rho> ` V"
    by (smt (verit, best) Term.term.simps(17) UN_iff image_eqI singletonD term.collapse(1))
qed

lemma mem_range_varsI:
  assumes "\<sigma> x = Var y" and "x \<noteq> y"
  shows "y \<in> range_vars \<sigma>"
  unfolding range_vars_def UN_iff
proof (rule bexI[of _ "Var y"])
  show "y \<in> vars_term (Var y)"
    by simp
next
  from assms show "Var y \<in> subst_range \<sigma>"
    by (simp_all add: subst_domain_def)
qed
lemma subst_range_Var[simp]:
  "subst_range Var = {}"
  by simp

lemma range_vars_Var[simp]:
  "range_vars Var = {}"
  by (simp add: range_vars_def)

lemma subst_apply_term_ident:
  "vars_term t \<inter> subst_domain \<sigma> = {} \<Longrightarrow> t \<cdot> \<sigma> = t"
proof (induction t)
  case (Var x)
  thus ?case
    by (simp add: subst_domain_def)
next
  case (Fun f ts)
  thus ?case
    by (auto intro: list.map_ident_strong)
qed

lemma vars_term_subst_apply_term:
  "vars_term (t \<cdot> \<sigma>) = (\<Union>x \<in> vars_term t. vars_term (\<sigma> x))"
  by (induction t) (auto simp add: insert_Diff_if subst_domain_def)

corollary vars_term_subst_apply_term_subset:
  "vars_term (t \<cdot> \<sigma>) \<subseteq> vars_term t - subst_domain \<sigma> \<union> range_vars \<sigma>"
  unfolding vars_term_subst_apply_term
proof (induction t)
  case (Var x)
  show ?case
    by (cases "\<sigma> x = Var x") (auto simp add: range_vars_def subst_domain_def)
next
  case (Fun f xs)
  thus ?case by auto
qed

lemma inv_renaming_sound:
  assumes is_var_\<rho>: "\<forall>x. is_Var (\<rho> x)" and "inj \<rho>"
  shows "\<rho> \<circ>\<^sub>s (Var \<circ> (inv (the_Var \<circ> \<rho>))) = Var"
proof -
  define \<rho>' where "\<rho>' = the_Var \<circ> \<rho>"
  have \<rho>_def: "\<rho> = Var \<circ> \<rho>'"
    unfolding \<rho>'_def using is_var_\<rho> by auto

  from is_var_\<rho> \<open>inj \<rho>\<close> have "inj \<rho>'"
    unfolding inj_def \<rho>_def comp_def by fast
  hence "inv \<rho>' \<circ> \<rho>' = id"
    using inv_o_cancel[of \<rho>'] by simp
  hence "Var \<circ> (inv \<rho>' \<circ> \<rho>') = Var"
    by simp
  hence "\<forall>x. (Var \<circ> (inv \<rho>' \<circ> \<rho>')) x = Var x"
    by metis
  hence "\<forall>x. ((Var \<circ> \<rho>') \<circ>\<^sub>s (Var \<circ> (inv \<rho>'))) x = Var x"
    unfolding subst_compose_def by auto
  thus "\<rho> \<circ>\<^sub>s (Var \<circ> (inv \<rho>')) = Var"
    using \<rho>_def by auto
qed

lemma ex_inverse_of_renaming:
  assumes "\<forall>x. is_Var (\<rho> x)" and "inj \<rho>"
  shows "\<exists>\<tau>. \<rho> \<circ>\<^sub>s \<tau> = Var"
  using inv_renaming_sound[OF assms] by blast

lemma subst_compose_apply_eq_apply_lhs:
  assumes
    "range_vars \<sigma> \<inter> subst_domain \<delta> = {}"
    "x \<notin> subst_domain \<delta>"
  shows "(\<sigma> \<circ>\<^sub>s \<delta>) x = \<sigma> x"
proof (cases "\<sigma> x")
  case (Var y)
  show ?thesis
  proof (cases "x = y")
    case True
    with Var have \<open>\<sigma> x = Var x\<close>
      by simp
    moreover from \<open>x \<notin> subst_domain \<delta>\<close> have "\<delta> x = Var x"
      by (simp add: disjoint_iff subst_domain_def)
    ultimately show ?thesis
      by (simp add: subst_compose_def)
  next
    case False
    have "y \<in> range_vars \<sigma>"
      unfolding range_vars_def UN_iff
    proof (rule bexI)
      show "y \<in> vars_term (Var y)"
        by simp
    next
      from Var False show "Var y \<in> subst_range \<sigma>"
        by (simp_all add: subst_domain_def)
    qed
    hence "y \<notin> subst_domain \<delta>"
      using \<open>range_vars \<sigma> \<inter> subst_domain \<delta> = {}\<close>
      by (simp add: disjoint_iff)
    with Var show ?thesis
      unfolding subst_compose_def
      by (simp add: subst_domain_def)
  qed
next
  case (Fun f ys)
  hence "Fun f ys \<in> subst_range \<sigma> \<or> (\<forall>y\<in>set ys. y \<in> subst_range \<sigma>)"
    using subst_domain_def by fastforce
  hence "\<forall>x \<in> vars_term (Fun f ys). x \<in> range_vars \<sigma>"
    by (metis UN_I range_vars_def term.distinct(1) term.sel(4) term.set_cases(2))
  hence "Fun f ys \<cdot> \<delta> = Fun f ys \<cdot> Var"
    unfolding term_subst_eq_conv
    using \<open>range_vars \<sigma> \<inter> subst_domain \<delta> = {}\<close>
    by (simp add: disjoint_iff subst_domain_def)
  hence "Fun f ys \<cdot> \<delta> = Fun f ys"
    by simp
  with Fun show ?thesis
    by (simp add: subst_compose_def)
qed

lemma subst_apply_term_subst_apply_term_eq_subst_apply_term_lhs:
  assumes "range_vars \<sigma> \<inter> subst_domain \<delta> = {}" and "vars_term t \<inter> subst_domain \<delta> = {}"
  shows "t \<cdot> \<sigma> \<cdot> \<delta> = t \<cdot> \<sigma>"
proof -
  from assms have "\<And>x. x \<in> vars_term t \<Longrightarrow> (\<sigma> \<circ>\<^sub>s \<delta>) x = \<sigma> x"
    using subst_compose_apply_eq_apply_lhs by fastforce
  hence "t \<cdot> \<sigma> \<circ>\<^sub>s \<delta> = t \<cdot> \<sigma>"
    using term_subst_eq_conv[of t "\<sigma> \<circ>\<^sub>s \<delta>" \<sigma>] by metis
  thus ?thesis
    by simp
qed


subsection \<open>Restrict the Domain of a Substitution\<close>

definition restrict_subst_domain where
  "restrict_subst_domain V \<sigma> x \<equiv> (if x \<in> V then \<sigma> x else Var x)"

lemma restrict_subst_domain_empty[simp]:
  "restrict_subst_domain {} \<sigma> = Var"
  unfolding restrict_subst_domain_def by auto

lemma restrict_subst_domain_Var[simp]:
  "restrict_subst_domain V Var = Var"
  unfolding restrict_subst_domain_def by auto

lemma subst_domain_restrict_subst_domain[simp]:
  "subst_domain (restrict_subst_domain V \<sigma>) = V \<inter> subst_domain \<sigma>"
  unfolding restrict_subst_domain_def subst_domain_def by auto

lemma subst_apply_term_restrict_subst_domain:
  "vars_term t \<subseteq> V \<Longrightarrow> t \<cdot> restrict_subst_domain V \<sigma> = t \<cdot> \<sigma>"
  by (rule term_subst_eq) (simp add: restrict_subst_domain_def subsetD)


subsection \<open>Rename the Domain of a Substitution\<close>

definition rename_subst_domain where
  "rename_subst_domain \<rho> \<sigma> x =
    (if Var x \<in> \<rho> ` subst_domain \<sigma> then
      \<sigma> (the_inv \<rho> (Var x))
    else
      Var x)"

lemma rename_subst_domain_Var_lhs[simp]:
  "rename_subst_domain Var \<sigma> = \<sigma>"
  by (rule ext) (simp add: rename_subst_domain_def inj_image_mem_iff the_inv_f_f subst_domain_def)

lemma rename_subst_domain_Var_rhs[simp]:
  "rename_subst_domain \<rho> Var = Var"
  by (rule ext) (simp add: rename_subst_domain_def)

lemma subst_domain_rename_subst_domain_subset:
  assumes is_var_\<rho>: "\<forall>x. is_Var (\<rho> x)"
  shows "subst_domain (rename_subst_domain \<rho> \<sigma>) \<subseteq> the_Var ` \<rho> ` subst_domain \<sigma>"
  by (auto simp add: subst_domain_def rename_subst_domain_def
      member_image_the_Var_image_subst[OF is_var_\<rho>])

lemma subst_range_rename_subst_domain_subset:
  assumes "inj \<rho>"
  shows "subst_range (rename_subst_domain \<rho> \<sigma>) \<subseteq> subst_range \<sigma>"
proof (intro Set.equalityI Set.subsetI)
  fix t assume "t \<in> subst_range (rename_subst_domain \<rho> \<sigma>)"
  then obtain x where
    t_def: "t = rename_subst_domain \<rho> \<sigma> x" and
    "rename_subst_domain \<rho> \<sigma> x \<noteq> Var x"
    by (auto simp: image_iff subst_domain_def)

  show "t \<in> subst_range \<sigma>"
  proof (cases \<open>Var x \<in> \<rho> ` subst_domain \<sigma>\<close>)
    case True
    then obtain x' where "\<rho> x' = Var x" and "x' \<in> subst_domain \<sigma>"
      by auto
    then show ?thesis
      using the_inv_f_f[OF \<open>inj \<rho>\<close>, of x']
      by (simp add: t_def rename_subst_domain_def)
  next
    case False
    hence False
      using \<open>rename_subst_domain \<rho> \<sigma> x \<noteq> Var x\<close>
      by (simp add: t_def rename_subst_domain_def)
    thus ?thesis ..
  qed
qed

lemma range_vars_rename_subst_domain_subset:
  assumes "inj \<rho>"
  shows "range_vars (rename_subst_domain \<rho> \<sigma>) \<subseteq> range_vars \<sigma>"
  unfolding range_vars_def
  using subst_range_rename_subst_domain_subset[OF \<open>inj \<rho>\<close>]
  by (metis Union_mono image_mono)

lemma renaming_cancels_rename_subst_domain:
  assumes is_var_\<rho>: "\<forall>x. is_Var (\<rho> x)" and "inj \<rho>" and vars_t: "vars_term t \<subseteq> subst_domain \<sigma>"
  shows "t \<cdot> \<rho> \<cdot> rename_subst_domain \<rho> \<sigma> = t \<cdot> \<sigma>"
  unfolding subst_subst
proof (intro term_subst_eq ballI)
  fix x assume "x \<in> vars_term t"
  with vars_t have x_in: "x \<in> subst_domain \<sigma>"
    by blast

  obtain x' where \<rho>_x: "\<rho> x = Var x'"
    using is_var_\<rho> by (meson is_Var_def)
  with x_in have x'_in: "Var x' \<in> \<rho> ` subst_domain \<sigma>"
    by (metis image_eqI)

  have "(\<rho> \<circ>\<^sub>s rename_subst_domain \<rho> \<sigma>) x = \<rho> x \<cdot> rename_subst_domain \<rho> \<sigma>"
    by (simp add: subst_compose_def)
  also have "\<dots> = rename_subst_domain \<rho> \<sigma> x'"
    using \<rho>_x by simp
  also have "\<dots> = \<sigma> (the_inv \<rho> (Var x'))"
    by (simp add: rename_subst_domain_def if_P[OF x'_in])
  also have "\<dots> = \<sigma> (the_inv \<rho> (\<rho> x))"
    by (simp add: \<rho>_x)
  also have "\<dots> = \<sigma> x"
    using \<open>inj \<rho>\<close> by (simp add: the_inv_f_f)
  finally show "(\<rho> \<circ>\<^sub>s rename_subst_domain \<rho> \<sigma>) x = \<sigma> x"
    by simp
qed


subsection \<open>Rename the Domain and Range of a Substitution\<close>

definition rename_subst_domain_range where
  "rename_subst_domain_range \<rho> \<sigma> x =
    (if Var x \<in> \<rho> ` subst_domain \<sigma> then
      ((Var o the_inv \<rho>) \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<rho>) (Var x)
    else
      Var x)"

lemma rename_subst_domain_range_Var_lhs[simp]:
  "rename_subst_domain_range Var \<sigma> = \<sigma>"
  by (rule ext) (simp add: rename_subst_domain_range_def inj_image_mem_iff the_inv_f_f
      subst_domain_def subst_compose_def)

lemma rename_subst_domain_range_Var_rhs[simp]:
  "rename_subst_domain_range \<rho> Var = Var"
  by (rule ext) (simp add: rename_subst_domain_range_def)

lemma subst_compose_renaming_rename_subst_domain_range:
  fixes \<sigma> \<rho> :: "('f, 'v) subst"
  assumes is_var_\<rho>: "\<forall>x. is_Var (\<rho> x)" and "inj \<rho>"
  shows "\<rho> \<circ>\<^sub>s rename_subst_domain_range \<rho> \<sigma> = \<sigma> \<circ>\<^sub>s \<rho>"
proof (rule ext)
  fix x
  from is_var_\<rho> obtain x' where "\<rho> x = Var x'"
    by (meson is_Var_def is_renaming_def)
  with \<open>inj \<rho>\<close> have inv_\<rho>_x': "the_inv \<rho> (Var x') = x"
    by (metis the_inv_f_f)

  show "(\<rho> \<circ>\<^sub>s rename_subst_domain_range \<rho> \<sigma>) x = (\<sigma> \<circ>\<^sub>s \<rho>) x"
  proof (cases "x \<in> subst_domain \<sigma>")
    case True
    hence "Var x' \<in> \<rho> ` subst_domain \<sigma>"
      using \<open>\<rho> x = Var x'\<close> by (metis imageI)
    thus ?thesis
      by (simp add: \<open>\<rho> x = Var x'\<close> rename_subst_domain_range_def subst_compose_def inv_\<rho>_x')
  next
    case False
    hence "Var x' \<notin> \<rho> ` subst_domain \<sigma>"
    proof (rule contrapos_nn)
      assume "Var x' \<in> \<rho> ` subst_domain \<sigma>"
      hence "\<rho> x \<in> \<rho> ` subst_domain \<sigma>"
        unfolding \<open>\<rho> x = Var x'\<close> .
      thus "x \<in> subst_domain \<sigma>"
        unfolding inj_image_mem_iff[OF \<open>inj \<rho>\<close>] .
    qed
    with False \<open>\<rho> x = Var x'\<close> show ?thesis
      by (simp add: subst_compose_def subst_domain_def rename_subst_domain_range_def)
  qed
qed

corollary subst_apply_term_renaming_rename_subst_domain_range:
  \<comment> \<open>This might be easier to find with @{command find_theorems}.\<close>
  fixes t :: "('f, 'v) term" and \<sigma> \<rho> :: "('f, 'v) subst"
  assumes is_var_\<rho>: "\<forall>x. is_Var (\<rho> x)" and "inj \<rho>"
  shows "t \<cdot> \<rho> \<cdot> rename_subst_domain_range \<rho> \<sigma> = t \<cdot> \<sigma> \<cdot> \<rho>"
  unfolding subst_subst
  unfolding subst_compose_renaming_rename_subst_domain_range[OF assms]
  by (rule refl)


section \<open>Option Monad\<close>

lemma zip_option_same[simp]:
  "zip_option xs xs = Some (zip xs xs)"
  by (induction xs) (simp_all add: zip_option.simps)


section \<open>Unifiers\<close>

subsubsection \<open>Properties of \<^term>\<open>is_imgu\<close>\<close>

lemma rename_subst_domain_range_preserves_is_imgu:
  fixes E :: "('f, 'v) equations" and \<mu> \<rho> :: "('f, 'v) subst"
  assumes imgu_\<mu>: "is_imgu \<mu> E" and is_var_\<rho>: "\<forall>x. is_Var (\<rho> x)" and "inj \<rho>"
  shows "is_imgu (rename_subst_domain_range \<rho> \<mu>) (subst_set \<rho> E)"
proof (unfold is_imgu_def, intro conjI ballI)
  from imgu_\<mu> have unif_\<mu>: "\<mu> \<in> unifiers E"
    by (simp add: is_imgu_def)

  show "rename_subst_domain_range \<rho> \<mu> \<in> unifiers (subst_set \<rho> E)"
    unfolding unifiers_subst_set unifiers_def mem_Collect_eq
  proof (rule ballI)
    fix e\<^sub>\<rho> assume "e\<^sub>\<rho> \<in> subst_set \<rho> E"
    then obtain e where "e \<in> E" and "e\<^sub>\<rho> = (fst e \<cdot> \<rho>, snd e \<cdot> \<rho>)"
      by (auto simp: subst_set_def)
    then show "fst e\<^sub>\<rho> \<cdot> rename_subst_domain_range \<rho> \<mu> = snd e\<^sub>\<rho> \<cdot> rename_subst_domain_range \<rho> \<mu>"
      using unif_\<mu> subst_apply_term_renaming_rename_subst_domain_range[OF is_var_\<rho> \<open>inj \<rho>\<close>, of _ \<mu>]
      by (simp add: unifiers_def)
  qed
next
  fix \<upsilon> :: "('f, 'v) subst"
  assume "\<upsilon> \<in> unifiers (subst_set \<rho> E)"
  hence "(\<rho> \<circ>\<^sub>s \<upsilon>) \<in> unifiers E"
    by (simp add: subst_set_def unifiers_def)
  with imgu_\<mu> have \<mu>_\<rho>_\<upsilon>: "\<mu> \<circ>\<^sub>s \<rho> \<circ>\<^sub>s \<upsilon> = \<rho> \<circ>\<^sub>s \<upsilon>"
    by (simp add: is_imgu_def subst_compose_assoc)

  show "\<upsilon> = rename_subst_domain_range \<rho> \<mu> \<circ>\<^sub>s \<upsilon>"
  proof (rule ext)
    fix x
    show "\<upsilon> x = (rename_subst_domain_range \<rho> \<mu> \<circ>\<^sub>s \<upsilon>) x"
    proof (cases "Var x \<in> \<rho> ` subst_domain \<mu>")
      case True
      hence "(rename_subst_domain_range \<rho> \<mu> \<circ>\<^sub>s \<upsilon>) x = (\<mu> \<circ>\<^sub>s \<rho> \<circ>\<^sub>s \<upsilon>) (the_inv \<rho> (Var x))"
        by (simp add: rename_subst_domain_range_def subst_compose_def)
      also have "\<dots> = (\<rho> \<circ>\<^sub>s \<upsilon>) (the_inv \<rho> (Var x))"
        by (simp add: \<mu>_\<rho>_\<upsilon>)
      also have "\<dots> = (\<rho> (the_inv \<rho> (Var x))) \<cdot> \<upsilon>"
        by (simp add: subst_compose)
      also have "\<dots> = Var x \<cdot> \<upsilon>"
        using True f_the_inv_into_f[OF \<open>inj \<rho>\<close>, of "Var x"] by force
      finally show ?thesis
        by simp
    next
      case False
      thus ?thesis
        by (simp add: rename_subst_domain_range_def subst_compose)
    qed
  qed
qed

corollary rename_subst_domain_range_preserves_is_imgu_singleton:
  fixes t u :: "('f, 'v) term" and \<mu> \<rho> :: "('f, 'v) subst"
  assumes imgu_\<mu>: "is_imgu \<mu> {(t, u)}" and is_var_\<rho>: "\<forall>x. is_Var (\<rho> x)" and "inj \<rho>"
  shows "is_imgu (rename_subst_domain_range \<rho> \<mu>) {(t \<cdot> \<rho>, u \<cdot> \<rho>)}"
  by (rule rename_subst_domain_range_preserves_is_imgu[OF imgu_\<mu> is_var_\<rho> \<open>inj \<rho>\<close>,
        unfolded subst_set_def, simplified])


section \<open>Unification\<close>

lemma decompose_same_Fun[simp]:
  "decompose (Fun f ss) (Fun f ss) = Some (zip ss ss)"
  by (simp add: decompose_def)

lemma unify_append_prefix_same:
  "(\<forall>e \<in> set es1. fst e = snd e) \<Longrightarrow> unify (es1 @ es2) bs = unify es2 bs"
proof (induction "es1 @ es2" bs arbitrary: es1 es2 bs rule: unify.induct)
  case (1 bs)
  thus ?case by simp
next
  case (2 f ss g ts E bs)
  show ?case
  proof (cases es1)
    case Nil
    thus ?thesis by simp
  next
    case (Cons e es1')
    hence e_def: "e = (Fun f ss, Fun g ts)" and E_def: "E = es1' @ es2"
      using "2" by simp_all
    hence "f = g" and "ss = ts"
      using "2.prems" local.Cons by auto
    hence "unify (es1 @ es2) bs = unify ((zip ts ts @ es1') @ es2) bs"
      by (simp add: Cons e_def)
    also have "\<dots> = unify es2 bs"
    proof (rule "2.hyps"(1))
      show "decompose (Fun f ss) (Fun g ts) = Some (zip ts ts)"
        by (simp add: \<open>f = g\<close> \<open>ss = ts\<close>)
    next
      show "zip ts ts @ E = (zip ts ts @ es1') @ es2"
        by (simp add: E_def)
    next
      show "\<forall>e\<in>set (zip ts ts @ es1'). fst e = snd e"
        using "2.prems" by (auto simp: Cons zip_same)
    qed
    finally show ?thesis .
  qed
next
  case (3 x t E bs)
  show ?case
  proof (cases es1)
    case Nil
    thus ?thesis by simp
  next
    case (Cons e es1')
    hence e_def: "e = (Var x, t)" and E_def: "E = es1' @ es2"
      using 3 by simp_all
    show ?thesis
    proof (cases "t = Var x")
      case True
      show ?thesis
        using 3(1)[OF True E_def]
        using "3.hyps"(3) "3.prems" local.Cons by fastforce
    next
      case False
      thus ?thesis
        using "3.prems" e_def local.Cons by force
    qed
  qed
next
  case (4 v va x E bs)
  then show ?case
  proof (cases es1)
    case Nil
    thus ?thesis by simp
  next
    case (Cons e es1')
    hence e_def: "e = (Fun v va, Var x)" and E_def: "E = es1' @ es2"
      using 4 by simp_all
    thus ?thesis
      using "4.prems" local.Cons by fastforce
  qed
qed

corollary unify_Cons_same:
  "fst e = snd e \<Longrightarrow> unify (e # es) bs = unify es bs"
  by (rule unify_append_prefix_same[of "[_]", simplified])

corollary unify_same:
  "(\<forall>e \<in> set es. fst e = snd e) \<Longrightarrow> unify es bs = Some bs"
  by (rule unify_append_prefix_same[of _ "[]", simplified])

corollary ex_unify_if_unifiers_not_empty:
  "unifiers es \<noteq> {} \<Longrightarrow> set xs = es \<Longrightarrow> \<exists>ys. unify xs [] = Some ys"
  using unify_complete by auto

corollary ex_mgu_if_unifiers_not_empty:
  "unifiers {(t,u)} \<noteq> {} \<Longrightarrow> \<exists>\<mu>. mgu t u = Some \<mu>"
  using mgu_complete by auto

corollary ex_mgu_if_subst_apply_term_eq_subst_apply_term:
  fixes t u :: "('f, 'v) Term.term" and \<sigma> :: "('f, 'v) subst"
  assumes t_eq_u: "t \<cdot> \<sigma> = u \<cdot> \<sigma>"
  shows "\<exists>\<mu> :: ('f, 'v) subst. Unification.mgu t u = Some \<mu>"
proof -
  from t_eq_u have "unifiers {(t, u)} \<noteq> {}"
    unfolding unifiers_def by auto
  thus ?thesis
    by (rule ex_mgu_if_unifiers_not_empty)
qed

lemma unify_subst_domain:
  assumes unif: "unify E [] = Some xs"
  shows "subst_domain (subst_of xs) \<subseteq> (\<Union>e \<in> set E. vars_term (fst e) \<union> vars_term (snd e))"
proof -
  from unify_Some_UNIF[OF unif] obtain xs' where
    "subst_of xs = compose xs'" and "UNIF xs' (mset E) {#}"
    by auto
  thus ?thesis
    using UNIF_subst_domain_subset
    by (metis (mono_tags, lifting) multiset.set_map set_mset_mset vars_mset_def)
qed

lemma unify_range_vars:
  assumes unif: "unify E [] = Some xs"
  shows "range_vars (subst_of xs) \<subseteq> (\<Union>e \<in> set E. vars_term (fst e) \<union> vars_term (snd e))"
proof -
  from unify_Some_UNIF[OF unif] obtain xs' where
    "subst_of xs = compose xs'" and "UNIF xs' (mset E) {#}"
    by auto
  thus ?thesis
    using UNIF_range_vars_subset
    by (metis (mono_tags, lifting) multiset.set_map set_mset_mset vars_mset_def)
qed

lemma mgu_range_vars:
  assumes "mgu s t = Some \<mu>"
  shows "range_vars \<mu> \<subseteq> vars_term s \<union> vars_term t"
proof -
  obtain xs where "unify [(s, t)] [] = Some xs" and "\<mu> = subst_of xs"
    using assms by (simp split: option.splits)
  thus ?thesis
    using unify_range_vars by fastforce
qed

lemma unify_subst_domain_range_vars_disjoint:
  assumes unif: "unify E [] = Some xs"
  shows "subst_domain (subst_of xs) \<inter> range_vars (subst_of xs) = {}"
proof -
  from unify_Some_UNIF[OF unif] obtain xs' where
    "subst_of xs = compose xs'" and "UNIF xs' (mset E) {#}"
    by auto
  thus ?thesis
    using UNIF_subst_domain_range_vars_Int by metis
qed

lemma mgu_subst_domain_range_vars_disjoint:
  assumes "mgu s t = Some \<mu>"
  shows "subst_domain \<mu> \<inter> range_vars \<mu> = {}"
proof -
  obtain xs where "unify [(s, t)] [] = Some xs" and "\<mu> = subst_of xs"
    using assms by (simp split: option.splits)
  thus ?thesis
    using unify_subst_domain_range_vars_disjoint by metis
qed

corollary subst_apply_term_eq_subst_apply_term_if_mgu:
  assumes mgu_t_u: "mgu t u = Some \<mu>"
  shows "t \<cdot> \<mu> = u \<cdot> \<mu>"
  using mgu_sound[OF mgu_t_u]
  by (simp add: is_imgu_def unifiers_def)

lemma mgu_same: "mgu t t = Some Var"
  by (simp add: unify_same)

lemma mgu_is_Var_if_not_in_equations:
  fixes \<mu> :: "('f, 'v) subst" and E :: "('f, 'v) equations" and x :: 'v
  assumes
    mgu_\<mu>: "is_mgu \<mu> E" and
    x_not_in: "x \<notin> (\<Union>e\<in>E. vars_term (fst e) \<union> vars_term (snd e))"
  shows "is_Var (\<mu> x)"
proof -
  from mgu_\<mu> have unif_\<mu>: "\<mu> \<in> unifiers E" and minimal_\<mu>: "\<forall>\<tau> \<in> unifiers E. \<exists>\<gamma>. \<tau> = \<mu> \<circ>\<^sub>s \<gamma>"
    by (simp_all add: is_mgu_def)

  define \<tau> :: "('f, 'v) subst" where
    "\<tau> = (\<lambda>x. if x \<in> (\<Union>e \<in> E. vars_term (fst e) \<union> vars_term (snd e)) then \<mu> x else Var x)"

  have \<open>\<tau> \<in> unifiers E\<close>
    unfolding unifiers_def mem_Collect_eq
  proof (rule ballI)
    fix e assume "e \<in> E"
    with unif_\<mu> have "fst e \<cdot> \<mu> = snd e \<cdot> \<mu>"
      by blast
    moreover from \<open>e \<in> E\<close> have "fst e \<cdot> \<tau> = fst e \<cdot> \<mu>" and "snd e \<cdot> \<tau> = snd e \<cdot> \<mu>"
      unfolding term_subst_eq_conv
      by (auto simp: \<tau>_def)
    ultimately show "fst e \<cdot> \<tau> = snd e \<cdot> \<tau>"
      by simp
  qed
  with minimal_\<mu> obtain \<gamma> where "\<mu> \<circ>\<^sub>s \<gamma> = \<tau>"
    by auto
  with x_not_in have "(\<mu> \<circ>\<^sub>s \<gamma>) x = Var x"
    by (simp add: \<tau>_def)
  thus "is_Var (\<mu> x)"
    by (metis subst_apply_eq_Var subst_compose term.disc(1))
qed

corollary mgu_ball_is_Var:
  "is_mgu \<mu> E \<Longrightarrow> \<forall>x \<in> - (\<Union>e\<in>E. vars_term (fst e) \<union> vars_term (snd e)). is_Var (\<mu> x)"
  by (rule ballI) (rule mgu_is_Var_if_not_in_equations[folded Compl_iff])

lemma mgu_inj_on:
  fixes \<mu> :: "('f, 'v) subst" and E :: "('f, 'v) equations"
  assumes mgu_\<mu>: "is_mgu \<mu> E"
  shows "inj_on \<mu> (- (\<Union>e \<in> E. vars_term (fst e) \<union> vars_term (snd e)))"
proof (rule inj_onI)
  fix x y
  assume
    x_in: "x \<in> - (\<Union>e\<in>E. vars_term (fst e) \<union> vars_term (snd e))" and
    y_in: "y \<in> - (\<Union>e\<in>E. vars_term (fst e) \<union> vars_term (snd e))" and
    "\<mu> x = \<mu> y"

  from mgu_\<mu> have unif_\<mu>: "\<mu> \<in> unifiers E" and minimal_\<mu>: "\<forall>\<tau> \<in> unifiers E. \<exists>\<gamma>. \<tau> = \<mu> \<circ>\<^sub>s \<gamma>"
    by (simp_all add: is_mgu_def)

  define \<tau> :: "('f, 'v) subst" where
    "\<tau> = (\<lambda>x. if x \<in> (\<Union>e \<in> E. vars_term (fst e) \<union> vars_term (snd e)) then \<mu> x else Var x)"

  have \<open>\<tau> \<in> unifiers E\<close>
    unfolding unifiers_def mem_Collect_eq
  proof (rule ballI)
    fix e assume "e \<in> E"
    with unif_\<mu> have "fst e \<cdot> \<mu> = snd e \<cdot> \<mu>"
      by blast
    moreover from \<open>e \<in> E\<close> have "fst e \<cdot> \<tau> = fst e \<cdot> \<mu>" and "snd e \<cdot> \<tau> = snd e \<cdot> \<mu>"
      unfolding term_subst_eq_conv
      by (auto simp: \<tau>_def)
    ultimately show "fst e \<cdot> \<tau> = snd e \<cdot> \<tau>"
      by simp
  qed
  with minimal_\<mu> obtain \<gamma> where "\<mu> \<circ>\<^sub>s \<gamma> = \<tau>"
    by auto
  hence "(\<mu> \<circ>\<^sub>s \<gamma>) x = Var x" and "(\<mu> \<circ>\<^sub>s \<gamma>) y = Var y"
    using ComplD[OF x_in] ComplD[OF y_in]
    by (simp_all add: \<tau>_def)
  with \<open>\<mu> x = \<mu> y\<close> show "x = y"
    by (simp add: subst_compose_def)
qed

lemma imgu_subst_domain_subset:
  fixes \<mu> :: "('f, 'v) subst" and E :: "('f, 'v) equations" and Evars :: "'v set"
  assumes imgu_\<mu>: "is_imgu \<mu> E" and fin_E: "finite E"
  defines "Evars \<equiv> (\<Union>e \<in> E. vars_term (fst e) \<union> vars_term (snd e))"
  shows "subst_domain \<mu> \<subseteq> Evars"
proof (intro Set.subsetI)
  from imgu_\<mu> have unif_\<mu>: "\<mu> \<in> unifiers E" and minimal_\<mu>: "\<forall>\<tau> \<in> unifiers E. \<mu> \<circ>\<^sub>s \<tau> = \<tau>"
    by (simp_all add: is_imgu_def)

  from fin_E obtain es :: "('f, 'v) equation list" where
    "set es = E"
    using finite_list by auto
  then obtain xs :: "('v \<times> ('f, 'v) Term.term) list" where
    unify_es: "unify es [] = Some xs"
    using unif_\<mu> ex_unify_if_unifiers_not_empty by blast

  define \<tau> :: "('f, 'v) subst" where
    "\<tau> = subst_of xs"

  have dom_\<tau>: "subst_domain \<tau> \<subseteq> Evars"
    using unify_subst_domain[OF unify_es, unfolded \<open>set es = E\<close>, folded Evars_def \<tau>_def] .
  have range_vars_\<tau>: "range_vars \<tau> \<subseteq> Evars"
    using unify_range_vars[OF unify_es, unfolded \<open>set es = E\<close>, folded Evars_def \<tau>_def] .

  have "\<tau> \<in> unifiers E"
    using \<open>set es = E\<close> unify_es \<tau>_def is_imgu_def unify_sound by blast
  with minimal_\<mu> have \<mu>_comp_\<tau>: "\<And>x. (\<mu> \<circ>\<^sub>s \<tau>) x = \<tau> x"
    by auto

  fix x :: 'v assume "x \<in> subst_domain \<mu>"
  hence "\<mu> x \<noteq> Var x"
    by (simp add: subst_domain_def)

  show "x \<in> Evars"
  proof (cases "x \<in> subst_domain \<tau>")
    case True
    thus ?thesis
      using dom_\<tau> by auto
  next
    case False
    hence "\<tau> x = Var x"
      by (simp add: subst_domain_def)
    hence "\<mu> x \<cdot> \<tau> = Var x"
      using \<mu>_comp_\<tau>[of x] by (simp add: subst_compose)
    thus ?thesis
    proof (rule subst_apply_eq_Var[of "\<mu> x" \<tau> x])
      show "\<And>y. \<mu> x = Var y \<Longrightarrow> \<tau> y = Var x \<Longrightarrow> ?thesis"
        using \<open>\<mu> x \<noteq> Var x\<close> range_vars_\<tau> mem_range_varsI[of \<tau> _ x] by auto
    qed
  qed
qed

lemma imgu_range_vars_of_equations_vars_subset:
  fixes \<mu> :: "('f, 'v) subst" and E :: "('f, 'v) equations" and Evars :: "'v set"
  assumes imgu_\<mu>: "is_imgu \<mu> E" and fin_E: "finite E"
  defines "Evars \<equiv> (\<Union>e \<in> E. vars_term (fst e) \<union> vars_term (snd e))"
  shows "(\<Union>x \<in> Evars. vars_term (\<mu> x)) \<subseteq> Evars"
proof (rule Set.subsetI)
  from imgu_\<mu> have unif_\<mu>: "\<mu> \<in> unifiers E" and minimal_\<mu>: "\<forall>\<tau> \<in> unifiers E. \<mu> \<circ>\<^sub>s \<tau> = \<tau>"
    by (simp_all add: is_imgu_def)

  from fin_E obtain es :: "('f, 'v) equation list" where
    "set es = E"
    using finite_list by auto
  then obtain xs :: "('v \<times> ('f, 'v) Term.term) list" where
    unify_es: "unify es [] = Some xs"
    using unif_\<mu> ex_unify_if_unifiers_not_empty by blast

  define \<tau> :: "('f, 'v) subst" where
    "\<tau> = subst_of xs"

  have dom_\<tau>: "subst_domain \<tau> \<subseteq> Evars"
    using unify_subst_domain[OF unify_es, unfolded \<open>set es = E\<close>, folded Evars_def \<tau>_def] .
  have range_vars_\<tau>: "range_vars \<tau> \<subseteq> Evars"
    using unify_range_vars[OF unify_es, unfolded \<open>set es = E\<close>, folded Evars_def \<tau>_def] .
  hence ball_vars_apply_\<tau>_subset: "\<forall>x \<in> subst_domain \<tau>. vars_term (\<tau> x) \<subseteq> Evars"
    unfolding range_vars_def
    by (simp add: SUP_le_iff)

  have "\<tau> \<in> unifiers E"
    using \<open>set es = E\<close> unify_es \<tau>_def is_imgu_def unify_sound by blast
  with minimal_\<mu> have \<mu>_comp_\<tau>: "\<And>x. (\<mu> \<circ>\<^sub>s \<tau>) x = \<tau> x"
    by auto

  fix y :: 'v assume "y \<in> (\<Union>x \<in> Evars. vars_term (\<mu> x))"
  then obtain x :: 'v where
    x_in: "x \<in> Evars" and y_in: "y \<in> vars_term (\<mu> x)"
    by (auto simp: subst_domain_def)
  have vars_\<tau>_x: "vars_term (\<tau> x) \<subseteq> Evars"
    using ball_vars_apply_\<tau>_subset subst_domain_def x_in by fastforce

  show "y \<in> Evars"
  proof (rule ccontr)
    assume "y \<notin> Evars"
    hence "y \<notin> vars_term (\<tau> x)"
      using vars_\<tau>_x by blast
    moreover have "y \<in> vars_term ((\<mu> \<circ>\<^sub>s \<tau>) x)"
    proof -
      have "\<tau> y = Var y"
        using \<open>y \<notin> Evars\<close> dom_\<tau>
        by (auto simp add: subst_domain_def)
      thus ?thesis
        unfolding subst_compose_def vars_term_subst_apply_term UN_iff
        using y_in by force
    qed
    ultimately show False
      using \<mu>_comp_\<tau>[of x] by simp
  qed
qed

lemma imgu_range_vars_subset:
  fixes \<mu> :: "('f, 'v) subst" and E :: "('f, 'v) equations"
  assumes imgu_\<mu>: "is_imgu \<mu> E" and fin_E: "finite E"
  shows "range_vars \<mu> \<subseteq> (\<Union>e \<in> E. vars_term (fst e) \<union> vars_term (snd e))"
proof -
  have "range_vars \<mu> = (\<Union>x \<in> subst_domain \<mu>. vars_term (\<mu> x))"
    by (simp add: range_vars_def)
  also have "\<dots> \<subseteq> (\<Union>x \<in> (\<Union>e \<in> E. vars_term (fst e) \<union> vars_term (snd e)). vars_term (\<mu> x))"
    using imgu_subst_domain_subset[OF imgu_\<mu> fin_E] by fast
  also have "\<dots> \<subseteq> (\<Union>e \<in> E. vars_term (fst e) \<union> vars_term (snd e))"
    using imgu_range_vars_of_equations_vars_subset[OF imgu_\<mu> fin_E] by metis
  finally show ?thesis .
qed

end