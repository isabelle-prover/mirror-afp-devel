theory Typed_IMGU
  imports 
    Nonground_Term_Typing
    IsaFoR_Nonground_Term
begin

locale typed_term_imgu =
  nonground_term where
    term_vars = term.vars and id_subst = "Var :: 'v \<Rightarrow> ('f, 'v) term" and term_subst = "(\<cdot>)" and
    subst_updates = subst_updates and apply_subst = apply_subst and subst_update = fun_upd and
    term_to_ground = term.to_ground and term_from_ground = term.from_ground and
    comp_subst = "(\<circ>\<^sub>s)" +

  base_typed_substitution where
     subst = "(\<cdot>)" and vars = term.vars and id_subst = Var and apply_subst = apply_subst and
     subst_update = fun_upd and welltyped = welltyped and comp_subst = "(\<circ>\<^sub>s)" +

  base_typed_subst_stability where
     subst = "(\<cdot>)" and vars = term.vars and id_subst = Var and apply_subst = apply_subst and
     subst_update = fun_upd and welltyped = welltyped and comp_subst = "(\<circ>\<^sub>s)" 

for welltyped  :: "('v \<Rightarrow> 'ty) \<Rightarrow> ('f, 'v) Term.term \<Rightarrow> 'ty \<Rightarrow> bool"
begin

lemma unify_subterms:
  assumes "type_preserving_unifier \<V> \<upsilon> (Fun f ts) (Fun f ts')"
  shows "list_all2 (type_preserving_unifier \<V> \<upsilon>) ts ts'"
  using assms
  unfolding list_all2_iff
  by (auto elim: in_set_zipE intro: map_eq_imp_length_eq)

lemma type_preserving_subst:
  assumes "\<V> \<turnstile> Var x : \<tau>" "\<V> \<turnstile> t : \<tau>"
  shows "type_preserving \<V> (subst x t)"
  using assms
  unfolding subst_def
  by auto

lemma type_preserving_unifier_subst:
  assumes "\<forall>(s, s') \<in> set ((Var x, t) # es). type_preserving_unifier \<V> \<upsilon> s s'"
  shows "\<forall>(s, s') \<in> set es. type_preserving_unifier \<V> \<upsilon> (s \<cdot> subst x t) (s' \<cdot> subst x t)"
proof (intro ballI2)
  fix s s'
  assume s_s': "(s, s') \<in> set es"

  then have "type_preserving_on (vars (s \<cdot> subst x t) \<union> vars (s' \<cdot> subst x t)) \<V> \<upsilon>"
    using assms term.vars_id_subst_update
    unfolding subst_def
    by (smt (verit, del_insts) Un_iff case_prodD in_mono list.set_intros(1,2))

  then show "type_preserving_unifier \<V> \<upsilon> (s \<cdot> subst x t) (s' \<cdot> subst x t)"
    using assms s_s'
    by (metis (mono_tags, lifting) eval_term.simps(1) list.set_intros(1,2) prod.case 
        subst_apply_left_idemp)
qed

lemma type_preserving_unifier_subst_list:
  assumes "\<forall>(s, s') \<in> set ((Var x, t) # es). type_preserving_unifier \<V> \<upsilon> s s'"
  shows "\<forall>(s, s') \<in> set (Unification.subst_list (subst x t) es). type_preserving_unifier \<V> \<upsilon> s s'"
  using type_preserving_unifier_subst[OF assms]
  unfolding Unification.subst_list_def
  by (smt (verit, best) case_prod_conv image_iff list.set_map prod.collapse)

lemma unify_subterms_zip_option:
  assumes
    type_preserving_unifier: "type_preserving_unifier \<V> \<upsilon> (Fun f ts) (Fun f ts')" and
    zip_option: "zip_option ts ts' = Some es"
  shows
    "\<forall>(t, t') \<in> set es. type_preserving_unifier \<V> \<upsilon> t t'"
  using unify_subterms[OF type_preserving_unifier] zip_option
  unfolding zip_option_zip_conv list_all2_iff
  by argo

lemma type_preserving_unifier_decompose_Fun:
  assumes
    type_preserving_unifier: "type_preserving_unifier \<V> \<upsilon> (Fun f ts) (Fun g ss)" and
    decompose: "decompose (Fun f ts) (Fun g ss) = Some es"
  shows "\<forall>(t, t') \<in> set es. type_preserving_unifier \<V> \<upsilon> t t'"
  using type_preserving_unifier decompose_Some[OF decompose]
  by (metis (mono_tags, lifting) list_all2_iff unify_subterms)

lemma type_preserving_unifier_decompose:
  assumes
    type_preserving_unifier: "type_preserving_unifier \<V> \<upsilon> f g" and
    decompose: "decompose f g = Some es"
  shows "\<forall>(t, t') \<in> set es. type_preserving_unifier \<V> \<upsilon> t t'"
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
    "\<forall>(t, t') \<in> set es. type_preserving_unifier \<V> \<upsilon> t t'"
    "type_preserving \<V> (subst_of bs)"
  shows "type_preserving \<V> (subst_of unifier)"
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

    have "\<forall>(t, t')\<in>set es'. type_preserving_unifier \<V> \<upsilon> t t'" 
    proof(rule type_preserving_unifier_decompose[OF _ es'], intro conjI)

      show "type_preserving_on (vars (Fun f ss) \<union> vars (Fun g ts)) \<V> \<upsilon>"
        using "2.prems"(2)
        by (metis (mono_tags, lifting) case_prod_conv list.set_intros(1))

      show "Fun f ss \<cdot> \<upsilon> = Fun g ts \<cdot> \<upsilon>"
        using "2.prems"(2)
        by auto
    qed

    moreover have "\<forall>(t, t')\<in>set es. type_preserving_unifier \<V> \<upsilon> t t'"
      using "2.prems"(2) 
      by (meson list.set_intros(2))
    
    ultimately show "\<forall>(t, t')\<in>set (es' @ es). type_preserving_unifier \<V> \<upsilon> t t'"
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

      show "x \<notin> vars t"
        using "3.prems"(1) False
        by auto
    next

      show "unify (Unification.subst_list (subst x t) es) ((x, t) # bs) = Some unifier"
        using False 3(3)
        by (auto split: if_splits)
    next

      show 
        "\<forall>(s, s') \<in> set (Unification.subst_list (subst x t) es). type_preserving_unifier \<V> \<upsilon> s s'"
        using type_preserving_unifier_subst_list[OF 3(4)] .
    next

      have "type_preserving \<V> (subst x t)"
        using 3(4) type_preserving_subst type_preserving_unifier
        by (smt (verit, del_insts) fun_upd_other list.set_intros(1) prod.case subst_def)  

      then show "type_preserving \<V> (subst_of ((x, t) # bs))"
        using 3(5)
        by (smt (verit, best) prod.sel(1,2) subst_of_simps(3) type_preserving_subst_compose)
    qed
  qed
next
  case (4 f ts x es bs)

  let ?t = "Fun f ts"

  show ?case
  proof (rule 4(1))

    show "x \<notin> vars ?t"
      using "4.prems"
      by fastforce
  next

    show "unify (Unification.subst_list (subst x ?t) es) ((x, ?t) # bs) = Some unifier"
      using "4.prems"(1)
      by (auto split: if_splits)
  next

    show "\<forall>(s, s') \<in> set (Unification.subst_list (subst x ?t) es). type_preserving_unifier \<V> \<upsilon> s s'"
    proof (rule type_preserving_unifier_subst_list)
      show "\<forall>(s, s')\<in>set ((Var x, ?t) # es). type_preserving_unifier \<V> \<upsilon> s s'"
        using "4.prems"(2)
        by fastforce
    qed
  next
    have "type_preserving \<V> (subst x ?t)"
      using 4(3) type_preserving_subst type_preserving_unifier
      by (smt (verit, del_insts) fun_upd_other list.set_intros(1) prod.case subst_def)  

    then show "type_preserving \<V> (subst_of ((x, ?t) # bs))"
      using 4(4)
      by (smt (verit, best) prod.sel(1,2) subst_of_simps(3) type_preserving_subst_compose)
  qed
qed

lemma type_preserving_unify_single:
  assumes
    unify: "unify [(t, t')] [] = Some unifier" and
    unifier: "type_preserving_unifier \<V> \<upsilon> t t'"
  shows "type_preserving \<V> (subst_of unifier)"
  using type_preserving_unify[OF unify] unifier
  by simp

lemma type_preserving_the_mgu:
  assumes
    the_mgu: "the_mgu t t' = \<mu>" and
    unifier: "type_preserving_unifier \<V> \<upsilon> t t'"
  shows "type_preserving \<V> \<mu>"
  using the_mgu type_preserving_unify_single[OF _ unifier]
  unfolding the_mgu_def mgu_def
  by (metis (mono_tags, lifting) option.exhaust option.simps(4,5))

sublocale type_preserving_imgu where 
  id_subst = "Var :: 'v \<Rightarrow> ('f, 'v) term" and comp_subst = "(\<circ>\<^sub>s)" and subst = "(\<cdot>)" and
  vars = term.vars and welltyped = welltyped and subst_update = fun_upd and
  apply_subst = apply_subst
proof unfold_locales
  fix \<V> \<upsilon> and t t' :: "('f, 'v) term"
  assume unifier: "type_preserving_unifier \<V> \<upsilon> t t'"
  show "\<exists>\<mu>. type_preserving_on UNIV \<V> \<mu> \<and> term.is_imgu \<mu> {{t, t'}}"
  proof (rule exI)

    have "is_imgu (the_mgu t t') {{t, t'}}"
      using the_mgu_is_imgu unifier
      unfolding Unifiers_is_mgu_iff_is_imgu_image_set_prod
      by auto

    then show "type_preserving_on UNIV \<V> (the_mgu t t') \<and> is_imgu (the_mgu t t') {{t, t'}}"
      using type_preserving_the_mgu[OF refl unifier]
      by satx
  qed
qed

end

end
