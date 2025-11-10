theory Monomorphic_Typing
  imports
    Nonground_Term_Typing
    Ground_Term_Typing
    IsaFoR_Nonground_Term
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

    hence "\<V> \<turnstile> Fun f (ss1 @ c\<langle>t'\<rangle> # ss2) : \<tau>"
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
  id_subst = "Var :: 'v :: infinite \<Rightarrow> ('f, 'v) term" and comp_subst = "(\<circ>\<^sub>s)" and subst = "(\<cdot>)" and
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
        using renaming term.id_subst_rename[OF renaming]
        by (metis eval_term.simps(1) monomorphic_term_typing.Var term.right_uniqueD)

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

(* TODO: Try to put in other file *)
lemma unify_subterms:
  assumes "term.type_preserving_unifier \<V> \<upsilon> (Fun f ts) (Fun f ts')"
  shows "list_all2 (term.type_preserving_unifier \<V> \<upsilon>) ts ts'"
  using assms
  unfolding list_all2_iff
  by (auto elim: in_set_zipE intro: map_eq_imp_length_eq)

lemma type_preserving_subst:
  assumes "\<V> \<turnstile> Var x : \<tau>" "\<V> \<turnstile> t : \<tau>"
  shows "term.type_preserving \<V> (subst x t)"
  using assms
  unfolding subst_def
  by auto

lemma type_preserving_unifier_subst:
  assumes "\<forall>(s, s') \<in> set ((Var x, t) # es). term.type_preserving_unifier \<V> \<upsilon> s s'"
  shows "\<forall>(s, s') \<in> set es. term.type_preserving_unifier \<V> \<upsilon> (s \<cdot> subst x t) (s' \<cdot> subst x t)"
proof (intro ballI2)
  fix s s'
  assume s_s': "(s, s') \<in> set es"

  then have "term.type_preserving_on (term.vars (s \<cdot> subst x t) \<union> term.vars (s' \<cdot> subst x t)) \<V> \<upsilon>"
    using assms term.vars_id_subst_update
    unfolding subst_def
    by (smt (verit, del_insts) Un_iff case_prodD in_mono list.set_intros(1,2))

  then show "term.type_preserving_unifier \<V> \<upsilon> (s \<cdot> subst x t) (s' \<cdot> subst x t)"
    using assms s_s'
    by (metis (mono_tags, lifting) eval_term.simps(1) list.set_intros(1,2) prod.case 
        subst_apply_left_idemp)
qed

lemma type_preserving_unifier_subst_list:
  assumes "\<forall>(s, s') \<in> set ((Var x, t) # es). term.type_preserving_unifier \<V> \<upsilon> s s'"
  shows "\<forall>(s, s') \<in> set (subst_list (subst x t) es). term.type_preserving_unifier \<V> \<upsilon> s s'"
  using type_preserving_unifier_subst[OF assms]
  unfolding subst_list_def
  by (smt (verit, best) case_prod_conv image_iff list.set_map prod.collapse)

lemma unify_subterms_zip_option:
  assumes
    type_preserving_unifier: "term.type_preserving_unifier \<V> \<upsilon> (Fun f ts) (Fun f ts')" and
    zip_option: "zip_option ts ts' = Some es"
  shows
    "\<forall>(t, t') \<in> set es. term.type_preserving_unifier \<V> \<upsilon> t t'"
  using unify_subterms[OF type_preserving_unifier] zip_option
  unfolding zip_option_zip_conv list_all2_iff
  by argo

lemma type_preserving_unifier_decompose_Fun:
  assumes
    type_preserving_unifier: "term.type_preserving_unifier \<V> \<upsilon> (Fun f ts) (Fun g ss)" and
    decompose: "decompose (Fun f ts) (Fun g ss) = Some es"
  shows "\<forall>(t, t') \<in> set es. term.type_preserving_unifier \<V> \<upsilon> t t'"
  using type_preserving_unifier decompose_Some[OF decompose]
  by (metis (mono_tags, lifting) list_all2_iff unify_subterms)

lemma type_preserving_unifier_decompose:
  assumes
    type_preserving_unifier: "term.type_preserving_unifier \<V> \<upsilon> f g" and
    decompose: "decompose f g = Some es"
  shows "\<forall>(t, t') \<in> set es. term.type_preserving_unifier \<V> \<upsilon> t t'"
proof -

  obtain f' fs gs where Fun: "f = Fun f' fs" "g = Fun f' gs"
    using decompose
    unfolding decompose_def
    by (auto split: term.splits if_splits)

  show ?thesis
    using type_preserving_unifier_decompose_Fun[OF assms[unfolded Fun]] .
qed

lemma type_preserving_unify:
  assumes
    "unify es bs = Some unifier"
    "\<forall>(t, t') \<in> set es. term.type_preserving_unifier \<V> \<upsilon> t t'"
    "term.type_preserving \<V> (subst_of bs)"
  shows "term.type_preserving \<V> (subst_of unifier)"
  using assms
proof(induction es bs rule: unify.induct)
  case 1

  then show ?case
    by simp
next
  case (2 f ss g ts es bs)

  obtain es' where es': "decompose (Fun f ss) (Fun g ts) = Some es'"
    using 2(2)
    by (simp split: option.splits)

  show ?case
  proof (rule "2.IH"[OF es' _ _ "2.prems"(3)])

    show "unify (es' @ es) bs = Some unifier"
      using es' "2.prems"(1)
      by auto
  next

    have 
      "\<forall>(t, t')\<in>set es'. term.type_preserving_unifier \<V> \<upsilon> t t'" 
      "\<forall>(t, t')\<in>set es. term.type_preserving_unifier \<V> \<upsilon> t t'"
      using type_preserving_unifier_decompose[OF _ es'] "2.prems"(2) 
      by auto
    
    then show "\<forall>(t, t')\<in>set (es' @ es). term.type_preserving_unifier \<V> \<upsilon> t t'"
      by auto
  qed
next
  case (3 x t es bs)

  show ?case
  proof(cases "t = Var x")
    case True

    then show ?thesis
      using 3
      by simp
  next
    case False

    then show ?thesis
    proof (rule 3(2))

      show "x \<notin> term.vars t"
        using "3.prems"(1) False
        by auto
    next

      show "unify (subst_list (subst x t) es) ((x, t) # bs) = Some unifier"
        using False 3(3)
        by (auto split: if_splits)
    next

      show "\<forall>(s, s') \<in> set (subst_list (subst x t) es). term.type_preserving_unifier \<V> \<upsilon> s s'"
        using type_preserving_unifier_subst_list[OF 3(4)] .
    next

      have "term.type_preserving \<V> (subst x t)"
        using 3(4) type_preserving_subst term.type_preserving_unifier
        by (smt (verit, del_insts) fun_upd_other list.set_intros(1) prod.case subst_def)  

      then show "term.type_preserving \<V> (subst_of ((x, t) # bs))"
        using 3(5)
        by  (simp add: subst_compose_def)
    qed
  qed
next
  case (4 f ts x es bs)

  let ?t = "Fun f ts"

  show ?case
  proof (rule 4(1))

    show "x \<notin> term.vars ?t"
      using "4.prems"
      by fastforce
  next

    show "unify (subst_list (subst x ?t) es) ((x, ?t) # bs) = Some unifier"
      using "4.prems"(1)
      by (auto split: if_splits)
  next

    show "\<forall>(s, s') \<in> set (subst_list (subst x ?t) es). term.type_preserving_unifier \<V> \<upsilon> s s'"
    proof (rule type_preserving_unifier_subst_list)
      show "\<forall>(s, s')\<in>set ((Var x, ?t) # es). term.type_preserving_unifier \<V> \<upsilon> s s'"
        using "4.prems"(2)
        by auto
    qed
  next
    have "term.type_preserving \<V> (subst x ?t)"
      using 4(3) type_preserving_subst term.type_preserving_unifier
      by (smt (verit, del_insts) fun_upd_other list.set_intros(1) prod.case subst_def)  

    then show "term.type_preserving \<V> (subst_of ((x, ?t) # bs))"
      using 4(4)
      by (simp add: subst_compose_def)
  qed
qed

lemma type_preserving_unify_single:
  assumes
    unify: "unify [(t, t')] [] = Some unifier" and
    unifier: "term.type_preserving_unifier \<V> \<upsilon> t t'"
  shows "term.type_preserving \<V> (subst_of unifier)"
  using type_preserving_unify[OF unify] unifier
  by simp

lemma type_preserving_the_mgu:
  assumes
    the_mgu: "the_mgu t t' = \<mu>" and
    unifier: "term.type_preserving_unifier \<V> \<upsilon> t t'"
  shows "term.type_preserving \<V> \<mu>"
  using the_mgu type_preserving_unify_single[OF _ unifier]
  unfolding the_mgu_def mgu_def
  by (metis (mono_tags, lifting) option.exhaust option.simps(4,5))

sublocale type_preserving_imgu where 
  id_subst = "Var :: 'v :: infinite \<Rightarrow> ('f, 'v) term" and comp_subst = "(\<circ>\<^sub>s)" and subst = "(\<cdot>)" and
  vars = term.vars and welltyped = welltyped and subst_update = fun_upd and
  apply_subst = apply_subst
proof unfold_locales
  fix \<V> \<upsilon> and t t' :: "('f, 'v) term"
  assume unifier: "term.type_preserving_unifier \<V> \<upsilon> t t'"
  show "\<exists>\<mu>. term.type_preserving_on UNIV \<V> \<mu> \<and> term.is_imgu \<mu> {{t, t'}}"
  proof (rule exI)

    have "term.is_imgu (the_mgu t t') {{t, t'}}"
      using the_mgu_is_imgu unifier
      unfolding Unifiers_is_mgu_iff_is_imgu_image_set_prod
      by auto

    then show "term.type_preserving_on UNIV \<V> (the_mgu t t') \<and> term.is_imgu (the_mgu t t') {{t, t'}}"
      using type_preserving_the_mgu[OF refl unifier]
      by satx
  qed
qed

end

locale witnessed_monomorphic_term_typing =
  monomorphic_term_typing where \<F> = \<F> for \<F> :: "('f, 'ty) fun_types" +
assumes types_witnessed: "\<And>\<tau>. \<exists>f. \<F> f 0 = Some ([], \<tau>)"
begin

sublocale "term": base_witnessed_typing_properties where
  id_subst = "Var :: 'v :: infinite \<Rightarrow> ('f, 'v) term" and comp_subst = "(\<circ>\<^sub>s)" and subst = "(\<cdot>)" and
  vars = term.vars and welltyped = welltyped and to_ground = term.to_ground and
  from_ground = term.from_ground and subst_updates = subst_updates and
  apply_subst = apply_subst and subst_update = fun_upd
proof unfold_locales
  fix \<V> :: "('v, 'ty) var_types" and \<tau>

  obtain f where f: "\<F> f 0 = Some ([], \<tau>)"
    using types_witnessed
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
