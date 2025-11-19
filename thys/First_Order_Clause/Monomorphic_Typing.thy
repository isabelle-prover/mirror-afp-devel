theory Monomorphic_Typing
  imports
    Nonground_Term_Typing
    Ground_Term_Typing
    IsaFoR_Nonground_Term
    Typed_IMGU
begin

no_notation Ground_Term_Typing.welltyped (\<open>_ \<turnstile> _ : _\<close> [1000, 0, 50] 50)
notation Ground_Term_Typing.welltyped (\<open>_ \<turnstile> _ :\<^sub>G _\<close> [1000, 0, 50] 50)

locale monomorphic_term_typing =
  fixes \<F> :: "('f, 'ty) fun_types"
begin

inductive welltyped :: "('v, 'ty) var_types \<Rightarrow> ('f,'v) term \<Rightarrow> 'ty \<Rightarrow> bool" 
  for \<V> where
    Var: "welltyped \<V> (Var x) \<tau>" if 
    "\<V> x = \<tau>" 
  | Fun: "welltyped \<V> (Fun f ts) \<tau>" if 
    "\<F> f (length ts) = Some (\<tau>s, \<tau>)"
    "list_all2 (welltyped \<V>) ts \<tau>s"

(* TODO: Introduce notations also for lifting + substition *)
notation welltyped (\<open>_ \<turnstile> _ : _\<close> [1000, 0, 50] 50)


sublocale "term": base_typing where welltyped = "welltyped \<V>" for \<V>
proof unfold_locales
  show "right_unique (welltyped \<V>)"
  proof (rule right_uniqueI)
    fix t \<tau>\<^sub>1 \<tau>\<^sub>2
    assume "\<V> \<turnstile> t : \<tau>\<^sub>1" and "\<V> \<turnstile> t : \<tau>\<^sub>2"
    thus "\<tau>\<^sub>1 = \<tau>\<^sub>2"
      by (auto elim!: welltyped.cases)
  qed
qed

sublocale "term": term_typing where 
  welltyped = "welltyped \<V>" and apply_context = ctxt_apply_term for \<V>
proof unfold_locales
  fix t t' c \<tau> \<tau>'

  assume
    welltyped_t_t': "\<V> \<turnstile> t : \<tau>'" "\<V> \<turnstile> t' : \<tau>'" and
    welltyped_c_t: "\<V> \<turnstile> c\<langle>t\<rangle> : \<tau>"

  from welltyped_c_t show "\<V> \<turnstile> c\<langle>t'\<rangle> : \<tau>"
  proof (induction c arbitrary: \<tau>)
    case Hole
    then show ?case
      using welltyped_t_t'
      by auto
  next
    case (More f ss1 c ss2)

    have "\<V> \<turnstile> Fun f (ss1 @ c\<langle>t\<rangle> # ss2) : \<tau>"
      using More.prems
      by simp

    then have "\<V> \<turnstile> Fun f (ss1 @ c\<langle>t'\<rangle> # ss2) : \<tau>"
    proof (cases \<V> "Fun f (ss1 @ c\<langle>t\<rangle> # ss2)" \<tau> rule: welltyped.cases)
      case (Fun \<tau>s)

      show ?thesis
      proof (rule welltyped.Fun)
        show "\<F> f (length (ss1 @ c\<langle>t'\<rangle> # ss2)) = Some (\<tau>s, \<tau>)"
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
  fix c t \<tau>
  assume "\<V> \<turnstile> c\<langle>t\<rangle> : \<tau>" 
  then show "\<exists>\<tau>'. \<V> \<turnstile> t : \<tau>'"
    by
      (induction c arbitrary: \<tau>)
      (auto simp: welltyped.simps list_all2_Cons1 list_all2_append1)
qed

sublocale "term": base_typing_properties where
  id_subst = "Var :: 'v \<Rightarrow> ('f, 'v) term" and comp_subst = "(\<circ>\<^sub>s)" and subst = "(\<cdot>)" and
  vars = term.vars and welltyped = welltyped and to_ground = term.to_ground and
  from_ground = term.from_ground and
  subst_updates = subst_updates and apply_subst = apply_subst and subst_update = fun_upd
proof(unfold_locales; (intro welltyped.Var refl)?)
  fix t :: "('f, 'v) term" and \<V> \<sigma> \<tau>
  assume type_preserving_\<sigma>: " \<forall>x\<in>term.vars t. \<V> \<turnstile> Var x : \<V> x \<longrightarrow> \<V> \<turnstile> \<sigma> x : \<V> x"

  show "\<V> \<turnstile> t \<cdot> \<sigma> : \<tau> \<longleftrightarrow> \<V> \<turnstile> t : \<tau>"  
  proof (rule iffI)

    assume "\<V> \<turnstile> t : \<tau>"

    then show "\<V> \<turnstile> t \<cdot> \<sigma> : \<tau>"
      using type_preserving_\<sigma>
      by 
        (induction rule: welltyped.induct)
        (auto simp: list.rel_mono_strong list_all2_map1 welltyped.simps)
  next

    assume "\<V> \<turnstile> t \<cdot> \<sigma> : \<tau>"

    then show "\<V> \<turnstile> t : \<tau>"
      using type_preserving_\<sigma>
    proof (induction "t \<cdot> \<sigma>" \<tau> arbitrary: t rule: welltyped.induct)
      case (Var x \<tau>)

      then obtain x' where t: "t = Var x'"
        by (metis subst_apply_eq_Var)

      have "\<V> \<turnstile> t : \<V> x'"
        unfolding t
        by (simp add: welltyped.Var)

      moreover have "\<V> \<turnstile> t : \<V> x"
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

  assume "\<V> \<turnstile> t : \<tau>" "\<forall>x\<in>term.vars t. \<V> x = \<V>' x"

  then show "\<V>' \<turnstile> t : \<tau>"
    by (induction rule: welltyped.induct) (simp_all add: welltyped.simps list.rel_mono_strong)
next
  fix \<V> \<V>' :: "('v, 'ty) var_types" and t :: "('f, 'v) term" and \<rho> :: "('f, 'v) subst" and \<tau>

  assume
    renaming: "term.is_renaming \<rho>" and
    \<V>: "\<forall>x\<in>term.vars t. \<V> x = \<V>' (term.rename \<rho> x)"

  then show "\<V>' \<turnstile> t \<cdot> \<rho> : \<tau> \<longleftrightarrow> \<V> \<turnstile> t : \<tau>"
  proof(intro iffI)

    assume "\<V>' \<turnstile> t \<cdot> \<rho> : \<tau>"

    with \<V> show "\<V> \<turnstile> t : \<tau>"
    proof(induction t arbitrary: \<tau>)
      case (Var x)

      then have "\<V>' (term.rename \<rho> x) = \<tau>"
        using renaming Var term.id_subst_rename[OF renaming]
        by (metis eval_term.simps(1) term.right_uniqueD welltyped.Var)

      then have "\<V> x = \<tau>"
        by (simp add: Var.prems(1))

      then show ?case
        by(rule welltyped.Var)
    next
      case (Fun f ts)

      then have "\<V>' \<turnstile> Fun f (map (\<lambda>s. s \<cdot> \<rho>) ts) : \<tau>"
        by auto

      then obtain \<tau>s where \<tau>s:
        "list_all2 (welltyped \<V>') (map (\<lambda>s. s \<cdot> \<rho>) ts) \<tau>s" 
        "\<F> f (length (map (\<lambda>s. s \<cdot> \<rho>) ts)) = Some (\<tau>s, \<tau>)"
        using welltyped.simps
        by blast

      then have \<F>: "\<F> f (length ts) = Some (\<tau>s, \<tau>)"
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
    assume "\<V> \<turnstile> t : \<tau>"

    then show "\<V>' \<turnstile> t \<cdot> \<rho> : \<tau>"
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

      have "list_all2 (welltyped \<V>') (map (\<lambda>s. s \<cdot> \<rho>) ts) \<tau>s"
        using Fun
        by (auto simp: list.rel_mono_strong list_all2_map1)

      then show ?case
        by (simp add: Fun.hyps welltyped.simps)
    qed
  qed
next
  fix \<V> :: "('v, 'ty) var_types"  and x

  show "\<V> \<turnstile> Var x : \<V> x \<or> \<not> term.is_welltyped \<V> (Var x)"
    by (simp add: Var)
qed

sublocale "term": typed_term_imgu where 
  welltyped = "welltyped :: ('v \<Rightarrow> 'ty) \<Rightarrow> ('f, 'v) Term.term \<Rightarrow> 'ty \<Rightarrow> bool"
  by unfold_locales

lemma exists_witness_if_exists_const_for_all_types: 
  assumes "\<And>\<tau>. \<exists>f. \<F> f 0 = Some ([], \<tau>)"
  shows "\<exists>t. term.is_ground t \<and> welltyped \<V> t \<tau>"
proof -
  fix \<V> :: "('v, 'ty) var_types" and \<tau>

  obtain f where f: "\<F> f 0 = Some ([], \<tau>)"
    using assms
    by blast

  show "\<exists>t. term.is_ground t \<and> \<V> \<turnstile> t : \<tau>"
  proof(rule exI[of _ "Fun f []"], intro conjI welltyped.Fun)

    show "term.is_ground (Fun f [])"
      by simp
  next

    show "\<F> f (length []) = Some ([], \<tau>)"
      using f
      by simp
  next

    show "list_all2 (welltyped \<V>) [] []"
      by simp
  qed
qed

end

end
