theory Nonground_Term_Typing
  imports
    Term_Typing
    Typed_Functional_Substitution
    Nonground_Term
begin

(* TODO: Create base version to avoid parameters? *)
locale base_typed_properties =
  base_typed_renaming +
  base_typed_subst_stability +
  replaceable_\<V> where
    base_subst = subst and base_vars = vars and base_welltyped = welltyped +
  typed_grounding_functional_substitution where 
    base_subst = subst and base_vars = vars and base_welltyped = welltyped

locale base_typing_properties =
  welltyped: base_typed_properties where welltyped = welltyped
  for welltyped :: "('var, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" 

locale base_inhabited_typing_properties =
  base_typing_properties +
  welltyped: inhabited_typed_functional_substitution where 
    welltyped = welltyped and base_subst = subst and base_vars = vars and base_welltyped = welltyped

locale nonground_term_typing =
  "term": nonground_term +
  fixes \<F> :: "('f, 'ty) fun_types"
begin

inductive welltyped :: "('v, 'ty) var_types \<Rightarrow> ('f,'v) term \<Rightarrow> 'ty \<Rightarrow> bool"
  for \<V> where
    Var: "\<V> x = \<tau> \<Longrightarrow> welltyped \<V> (Var x) \<tau>"
  | Fun: "\<F> f (length ts) = (\<tau>s, \<tau>) \<Longrightarrow> list_all2 (welltyped \<V>) ts \<tau>s \<Longrightarrow> welltyped \<V> (Fun f ts) \<tau>"

sublocale "term": base_typing where
  welltyped = "welltyped \<V>" for \<V>
proof unfold_locales
  show "right_unique (welltyped \<V>)"
  proof (rule right_uniqueI)
    fix t \<tau>\<^sub>1 \<tau>\<^sub>2
    assume "welltyped \<V> t \<tau>\<^sub>1" and "welltyped \<V> t \<tau>\<^sub>2"
    thus "\<tau>\<^sub>1 = \<tau>\<^sub>2"
      by (auto elim!: welltyped.cases)
  qed
qed

sublocale "term": term_typing where
  welltyped = "welltyped \<V>" and Fun = Fun for \<V>
proof unfold_locales
  fix t t' c \<tau> \<tau>'

  assume
    t_type: "welltyped \<V> t \<tau>'" and
    t'_type: "welltyped \<V> t' \<tau>'" and
    c_type: "welltyped \<V> c\<langle>t\<rangle> \<tau>"

  from c_type show "welltyped \<V> c\<langle>t'\<rangle> \<tau>"
  proof (induction c arbitrary: \<tau>)
    case Hole
    then show ?case
      using t_type t'_type
      by auto
  next
    case (More f ss1 c ss2)

    have "welltyped \<V> (Fun f (ss1 @ c\<langle>t\<rangle> # ss2)) \<tau>"
      using More.prems
      by simp

    hence "welltyped \<V> (Fun f (ss1 @ c\<langle>t'\<rangle> # ss2)) \<tau>"
    proof (cases \<V> "Fun f (ss1 @ c\<langle>t\<rangle> # ss2)" \<tau> rule: welltyped.cases)
      case (Fun \<tau>s)

      show ?thesis
      proof (rule welltyped.Fun)
        show "\<F> f (length (ss1 @ c\<langle>t'\<rangle> # ss2)) = (\<tau>s, \<tau>)"
          using Fun 
          by simp
      next
        show "list_all2 (welltyped \<V>) (ss1 @ c\<langle>t'\<rangle> # ss2) \<tau>s"
          using \<open>list_all2 (welltyped \<V>) (ss1 @ c\<langle>t\<rangle> # ss2) \<tau>s\<close>
          using More.IH
          by (smt (verit, del_insts) list_all2_Cons1 list_all2_append1 list_all2_lengthD)
      qed
    qed

    thus ?case
      by simp
  qed
next
  fix f ts \<tau>
  assume "welltyped \<V> (Fun f ts) \<tau>"
  then show " \<forall>t\<in>set ts. \<exists>\<tau>'. welltyped \<V> t \<tau>'"
    by (cases rule: welltyped.cases) (metis in_set_conv_nth list_all2_conv_all_nth)
qed

sublocale "term": base_typing_properties where
  id_subst = "Var :: 'v \<Rightarrow> ('f, 'v) term" and comp_subst = "(\<odot>)" and subst = "(\<cdot>t)" and
  vars = term.vars and welltyped = welltyped and to_ground = term.to_ground and
  from_ground = term.from_ground
proof(unfold_locales; (intro welltyped.Var refl)?)
  fix \<tau> and \<V> and t :: "('f, 'v) term" and \<sigma>

  assume is_welltyped_on: "\<forall>x \<in> term.vars t. welltyped \<V> (\<sigma> x) (\<V> x)"

  show "welltyped \<V> (t \<cdot>t \<sigma>) \<tau> \<longleftrightarrow> welltyped \<V> t \<tau>"
  proof (rule iffI)

    assume "welltyped \<V> t \<tau>"

    then show "welltyped \<V> (t \<cdot>t \<sigma>) \<tau>"
      using is_welltyped_on
      by (induction rule: welltyped.induct)
         (auto simp: list.rel_mono_strong list_all2_map1 welltyped.simps)
  next

    assume "welltyped \<V> (t \<cdot>t \<sigma>) \<tau>"

    then show "welltyped \<V> t \<tau>"
      using is_welltyped_on
    proof (induction "t \<cdot>t \<sigma>" \<tau> arbitrary: t rule: welltyped.induct)
      case (Var x \<tau>)

      then obtain x' where t: "t = Var x'"
        by (metis subst_apply_eq_Var)

      have "welltyped \<V> t (\<V> x')"
        unfolding t
        by (simp add: welltyped.Var)

      moreover have "welltyped \<V> t (\<V> x)"
        using Var
        unfolding t
        by (simp add: welltyped.simps)

      ultimately have \<V>_x': "\<tau> = \<V> x'"
        using Var.hyps
        by blast

      show ?case
        unfolding t \<V>_x'
        by (simp add: welltyped.Var)
    next
      case (Fun f \<tau>s \<tau> ts)

      then show ?case
        by (cases t) (simp_all add: list.rel_mono_strong list_all2_map1 welltyped.simps)
    qed
  qed
next
  fix t :: "('f, 'v) term" and \<V> \<V>' \<tau>

  assume "welltyped \<V> t \<tau>" "\<forall>x\<in>term.vars t. \<V> x = \<V>' x"

  then show "welltyped \<V>' t \<tau>"
    by (induction rule: welltyped.induct) (simp_all add: welltyped.simps list.rel_mono_strong)
next
  fix \<V> \<V>' :: "('v, 'ty) var_types" and t :: "('f, 'v) term" and \<rho> :: "('f, 'v) subst" and \<tau>

  assume
    renaming: "term_subst.is_renaming \<rho>" and
    \<V>: "\<forall>x\<in>term.vars t. \<V> x = \<V>' (term.rename \<rho> x)"

  then show "welltyped \<V>' (t \<cdot>t \<rho>) \<tau> \<longleftrightarrow> welltyped \<V> t \<tau>"
  proof(intro iffI)

    assume "welltyped \<V>' (t \<cdot>t \<rho>) \<tau>"

    with \<V> show "welltyped \<V> t \<tau>"
    proof(induction t arbitrary: \<tau>)
      case (Var x)

      then have "\<V>' (term.rename \<rho> x) = \<tau>"
        using renaming term.id_subst_rename[OF renaming]
        by (metis eval_term.simps(1) nonground_term_typing.Var
            term.right_uniqueD)

      then have "\<V> x = \<tau>"
        by (simp add: Var.prems(1))

      then show ?case
        by(rule welltyped.Var)
    next
      case (Fun f ts)

      then have "welltyped \<V>' (Fun f (map (\<lambda>s. s \<cdot>t \<rho>) ts)) \<tau>"
        by auto

      then obtain \<tau>s where \<tau>s:
        "list_all2 (welltyped \<V>') (map (\<lambda>s. s \<cdot>t \<rho>) ts) \<tau>s" 
        "\<F> f (length (map (\<lambda>s. s \<cdot>t \<rho>) ts)) = (\<tau>s, \<tau>)"
        using welltyped.simps
        by blast

      then have \<F>: "\<F> f (length ts) = (\<tau>s, \<tau>)"
        by simp
       
      show ?case
      proof(rule welltyped.Fun[OF \<F>])

        show "list_all2 (welltyped \<V>) ts \<tau>s"
          using \<tau>s(1) Fun.IH
          by (smt (verit, ccfv_SIG) Fun.prems(1) eval_term.simps(2) in_set_conv_nth length_map
              list_all2_conv_all_nth nth_map term.set_intros(4))
      qed
    qed
  next
    assume "welltyped \<V> t \<tau>"
    then show "welltyped \<V>' (t \<cdot>t \<rho>) \<tau>"
      using \<V>
    proof(induction rule: welltyped.induct)
      case (Var x \<tau>)

      then have "\<V>' (term.rename \<rho> x) = \<tau>"
        by simp

      then show ?case
        using term.id_subst_rename[OF renaming]
        by (metis eval_term.simps(1) welltyped.Var)
    next
      case (Fun f ts \<tau>s \<tau>)

      have "list_all2 (welltyped \<V>') (map (\<lambda>s. s \<cdot>t \<rho>) ts) \<tau>s"
        using Fun
        by (auto simp: list.rel_mono_strong list_all2_map1)

      then show ?case
        by (simp add: Fun.hyps welltyped.simps)
    qed
  qed
qed

sublocale functional_substitution_typing where 
  id_subst = "Var :: 'v \<Rightarrow> ('f, 'v) term" and comp_subst = "(\<odot>)" and subst = "(\<cdot>t)" and
  vars = term.vars and welltyped = welltyped
  by unfold_locales

end

locale nonground_term_inhabited_typing =
  nonground_term_typing where \<F> = \<F> for \<F> :: "('f, 'ty) fun_types" +
  assumes types_inhabited: "\<And>\<tau>. \<exists>f. \<F> f 0 = ([], \<tau>)"
begin

sublocale base_inhabited_typing_properties where
  id_subst = "Var :: 'v \<Rightarrow> ('f, 'v) term" and comp_subst = "(\<odot>)" and subst = "(\<cdot>t)" and
  vars = term.vars and welltyped = welltyped and to_ground = term.to_ground and
  from_ground = term.from_ground
proof unfold_locales
  fix \<V> :: "('v, 'ty) var_types" and \<tau>

  obtain f where f: "\<F> f 0 = ([], \<tau>)"
    using types_inhabited
    by blast

  show "\<exists>t. term.is_ground t \<and> welltyped \<V> t \<tau>"
  proof(rule exI[of _ "Fun f []"], intro conjI welltyped.Fun)

    show "term.is_ground (Fun f [])"
      by simp
  next

    show "\<F> f (length []) = ([], \<tau>)"
      using f
      by simp
  next

    show "list_all2 (welltyped \<V>) [] []"
      by simp
  qed
qed

end

end
