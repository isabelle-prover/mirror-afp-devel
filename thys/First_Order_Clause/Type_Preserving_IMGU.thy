theory Type_Preserving_IMGU
  imports Nonground_Term_Typing
begin

context term_typing_properties
begin

abbreviation type_preserving_unifier where
  "type_preserving_unifier \<V> \<upsilon> t t' \<equiv>
    type_preserving_on (term.vars t \<union> term.vars t') \<V> \<upsilon> \<and> t \<cdot>t \<upsilon> = t' \<cdot>t \<upsilon>"

lemma type_preserving_unifier_set_comm:
  "(\<forall>(s, s') \<in> set ((t, t') # es). type_preserving_unifier \<V> \<upsilon> s s') \<longleftrightarrow>
   (\<forall>(s, s') \<in> set ((t', t) # es). type_preserving_unifier \<V> \<upsilon> s s')"
  by auto

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
  shows "\<forall>(s, s') \<in> set es. type_preserving_unifier \<V> \<upsilon> (s \<cdot>t subst x t) (s' \<cdot>t subst x t)"
proof (intro ballI2)
  fix s s'
  assume s_s': "(s, s') \<in> set es"

  then have "type_preserving_on (term.vars (s \<cdot>t subst x t) \<union> term.vars (s' \<cdot>t subst x t)) \<V> \<upsilon>"
    using assms term.vars_id_subst_update
    unfolding subst_def
    by (smt (verit, del_insts) UnCI UnE case_prodD list.set_intros(1,2) subset_iff)

  then show "type_preserving_unifier \<V> \<upsilon> (s \<cdot>t subst x t) (s' \<cdot>t subst x t)"
    using assms s_s'
    by auto
qed

lemma type_preserving_unifier_subst_list:
  assumes "\<forall>(s, s') \<in> set ((Var x, t) # es). type_preserving_unifier \<V> \<upsilon> s s'"
  shows "\<forall>(s, s') \<in> set (subst_list (subst x t) es). type_preserving_unifier \<V> \<upsilon> s s'"
  using type_preserving_unifier_subst[OF assms]
  unfolding subst_list_def
  by auto

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

    have 
      "\<forall>(t, t')\<in>set es'. type_preserving_unifier \<V> \<upsilon> t t'" 
      "\<forall>(t, t')\<in>set es. type_preserving_unifier \<V> \<upsilon> t t'"
      using type_preserving_unifier_decompose[OF _ es'] "2.prems"(2) 
      by auto
    
    then show "\<forall>(t, t')\<in>set (es' @ es). type_preserving_unifier \<V> \<upsilon> t t'"
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

      show "\<forall>(s, s') \<in> set (subst_list (subst x t) es). type_preserving_unifier \<V> \<upsilon> s s'"
        using type_preserving_unifier_subst_list[OF 3(4)] .
    next

      show "type_preserving \<V> (subst_of ((x, t) # bs))"
        using 3(4, 5) type_preserving_subst
        by (auto simp: subst_compose_def subst_def)
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

    show "\<forall>(s, s') \<in> set (subst_list (subst x ?t) es). type_preserving_unifier \<V> \<upsilon> s s'"
      using type_preserving_unifier_subst_list "4.prems"(2) type_preserving_unifier_set_comm
      by meson
  next

    have "type_preserving \<V> (subst x ?t)"
      using 4(3) type_preserving_subst term.type_preserving_unifier
      by (smt (verit, del_insts) fun_upd_other list.set_intros(1) prod.case subst_def)  

    then show "type_preserving \<V> (subst_of ((x, ?t) # bs))"
      using 4(4)
      by (simp add: subst_compose_def)
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

(* TODO: inline? + Name 
abbreviation welltyped_imgu_on where
  "welltyped_imgu_on X \<V> t t' \<mu> \<equiv> type_preserving_on X \<V> \<mu> \<and> term_subst.is_imgu \<mu> {{t, t'}}"

abbreviation welltyped_imgu where
  "welltyped_imgu \<equiv> welltyped_imgu_on UNIV"*)

lemma obtain_type_preserving_imgu:
  fixes \<upsilon> :: "('f, 'v) subst"
  assumes "type_preserving_unifier \<V> \<upsilon> t t'"
  obtains \<mu> :: "('f, 'v) subst"
  where "\<upsilon> = \<mu> \<odot> \<upsilon>" "type_preserving \<V> \<mu>" "term_subst.is_imgu \<mu> {{t, t'}}"
proof (rule that)

  show "\<upsilon> = (the_mgu t t') \<odot> \<upsilon>"
    using the_mgu assms
    by blast
next

  show "type_preserving \<V> (the_mgu t t')"
    using type_preserving_the_mgu assms
    by metis
next

  show "term_subst.is_imgu (the_mgu t t') {{t, t'}}"
    using assms the_mgu_term_subst_is_imgu
    by metis
qed

lemma obtain_type_preserving_on_imgu:
  fixes \<upsilon> :: "('f, 'v) subst"
  assumes "type_preserving_unifier \<V> \<upsilon> t t'"
  obtains \<mu> :: "('f, 'v) subst"
  where "\<upsilon> = \<mu> \<odot> \<upsilon>" "type_preserving_on X \<V> \<mu>" "term_subst.is_imgu \<mu> {{t, t'}}"
  using obtain_type_preserving_imgu[OF assms] UNIV_I
  by metis

end

end
