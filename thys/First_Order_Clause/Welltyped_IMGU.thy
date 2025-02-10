theory Welltyped_IMGU
  imports Nonground_Term_Typing
begin

context nonground_term_typing
begin

lemma is_welltyped_subst:
  assumes "welltyped \<V> (Var x) \<tau>" "welltyped \<V> t \<tau>"
  shows "term.subst.is_welltyped \<V> (subst x t)"
  using assms
  unfolding subst_def
  by (simp add: welltyped.simps)

lemma Fun_arg_types:
  assumes
    "welltyped \<V> (Fun f fs) \<tau>"
    "welltyped \<V> (Fun f gs) \<tau>"
  obtains \<tau>s where
    "\<F> f = (\<tau>s, \<tau>)"
    "list_all2 (welltyped \<V>) fs \<tau>s"
    "list_all2 (welltyped \<V>) gs \<tau>s"
  using assms
  by (metis Pair_inject term.distinct(1) term.inject(2) welltyped.simps)

lemma welltyped_zip_option:
  assumes
    "welltyped \<V> (Fun f ts) \<tau>"
    "welltyped \<V> (Fun f ss) \<tau>"
    "zip_option ts ss = Some es"
  shows
    "\<forall>(t, t') \<in> set es. \<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau>"
proof -

  obtain \<tau>s where
    "list_all2 (welltyped \<V>) ts \<tau>s"
    "list_all2 (welltyped \<V>) ss \<tau>s"
    using Fun_arg_types[OF assms(1, 2)].

  with assms(3) show ?thesis
  proof(induction ts ss arbitrary: \<tau>s es rule: zip_induct)
    case (Cons_Cons t ts s ss)
    then obtain \<tau>' \<tau>s' where \<tau>s: "\<tau>s = \<tau>' # \<tau>s'"
      by (meson list_all2_Cons1)

    from Cons_Cons(2)
    obtain e es' where es: "es = e # es'"
      by auto

    have "zip_option ts ss = Some es'"
      using Cons_Cons(2)
      unfolding es
      by fastforce

    moreover have "list_all2 (welltyped \<V>) ts \<tau>s'"
      using Cons_Cons.prems(2) \<tau>s
      by blast

    moreover have "list_all2 (welltyped \<V>) ss \<tau>s'"
      using Cons_Cons.prems(3) \<tau>s
      by blast

    ultimately have "\<forall>(t, s)\<in>set es'. \<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> s \<tau>"
      using Cons_Cons.IH
      by presburger

    moreover have "\<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> s \<tau>"
      using Cons_Cons.prems(2) Cons_Cons.prems(3) \<tau>s by blast

    ultimately show ?case
      using Cons_Cons.prems(1) es
      by fastforce
  qed auto
qed

lemma welltyped_decompose_Fun:
  assumes
    "welltyped \<V> (Fun f fs) \<tau>"
    "welltyped \<V> (Fun f gs) \<tau>"
    "decompose (Fun f fs) (Fun g gs) = Some es"
  shows "\<forall>(t, t') \<in> set es. \<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau>"
  using assms welltyped_zip_option[OF assms(1,2)]
  by (metis (lifting) decompose_Some not_Some_eq zip_option_simps(2,3))

lemma welltyped_decompose:
  assumes
    "welltyped \<V> f \<tau>"
    "welltyped \<V> g \<tau>" and
    decompose: "decompose f g = Some es"
  shows "\<forall>(t, t') \<in> set es. \<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau>"
proof-

  obtain f' fs gs where Fun: "f = Fun f' fs" "g = Fun f' gs"
    using decompose
    unfolding decompose_def
    by (auto split: term.splits if_splits)

  show ?thesis
    using welltyped_decompose_Fun[OF assms[unfolded Fun]] .
qed

lemma is_welltyped_unify:
  assumes
    "unify es bs = Some unifier"
    "\<forall>(t, t') \<in> set es. \<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau>"
    "term.subst.is_welltyped \<V> (subst_of bs)"
  shows "term.subst.is_welltyped \<V> (subst_of unifier)"
  using assms
proof(induction es bs rule: unify.induct)
  case (1 bs)

  then show ?case
    by simp
next
  case (2 f ss g ts es bs)

  obtain es' where es': "decompose (Fun f ss) (Fun g ts) = Some es'"
    using 2(2)
    by (simp split: option.splits)

  moreover then have "unify (es' @ es) bs = Some unifier"
    using "2.prems"
    by auto

  moreover have "\<forall>(t, t')\<in>set (es' @ es). \<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau>"
    using welltyped_decompose[OF _ _ es'] 2(3)
    by fastforce

  show ?case
  proof (rule "2.IH"[OF es' _ _ "2.prems"(3)])

    show "unify (es' @ es) bs = Some unifier"
      using es' "2.prems"
      by auto

    show "\<forall>(t, t')\<in>set (es' @ es). \<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau>"
      using welltyped_decompose[OF _ _ es'] 2(3)
      by fastforce
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

    show ?thesis
    proof (rule 3(2)[OF False])

      show "x \<notin> term.vars t"
        using "3.prems"(1) False
        by auto
    next

      show "unify (subst_list (subst x t) es) ((x, t) # bs) = Some unifier"
        using False 3(3)
        by (auto split: if_splits)
    next

      {
        fix s s'

        assume s_s': "(s, s') \<in> set es"

        have "term.subst.is_welltyped \<V> (Var(x := t))"
          using 3(4) term.welltyped.subst_update
          by auto

        then have "\<exists>\<tau>. welltyped \<V> (s \<cdot>t Var(x := t)) \<tau> \<and> welltyped \<V> (s' \<cdot>t Var(x := t)) \<tau>"
          using 3(4) s_s'
          by auto
      }

      then show "\<forall>(s, s') \<in> set (subst_list (subst x t) es). \<exists>\<tau>. welltyped \<V> s \<tau> \<and> welltyped \<V> s' \<tau>"
        unfolding subst_def subst_list_def
        by fastforce
    next

      have "term.subst.is_welltyped \<V> (subst x t)"
        using 3(4) is_welltyped_subst
        by fastforce

      then show "term.subst.is_welltyped \<V> (subst_of ((x, t) # bs))"
        using 3(5)
        by (simp add: subst_compose_def)
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
      by (metis option.discI unify.simps(4))
  next

    {
      fix s s'

      assume s_s': "(s, s') \<in> set es"

      obtain \<tau> where "welltyped \<V> (Var x) \<tau>" "welltyped \<V> ?t \<tau>"
        using 4(3)
        by auto

      then have "term.subst.is_welltyped \<V> (Var(x := ?t))"
        using term.welltyped.subst_update
        by auto

      then have "\<exists>\<tau>. welltyped \<V> (s \<cdot>t Var(x := ?t)) \<tau> \<and> welltyped \<V> (s' \<cdot>t Var(x := ?t)) \<tau>"
        using 4(3) s_s'
        by auto
    }

    then show "\<forall>(s, s') \<in> set (subst_list (subst x ?t) es). \<exists>\<tau>. welltyped \<V> s \<tau> \<and> welltyped \<V> s' \<tau>"
      unfolding subst_def subst_list_def
      by fastforce
  next

    have "term.subst.is_welltyped \<V> (subst x ?t)"
      using 4(3) is_welltyped_subst
      by fastforce

    then show "term.subst.is_welltyped \<V> (subst_of ((x, ?t) # bs))"
      using 4(4)
      by (simp add: subst_compose_def)
  qed
qed

lemma is_welltyped_unify_single:
  assumes
    unify: "unify [(t, t')] [] = Some unifier" and
    \<tau>: "\<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau>"
  shows "term.subst.is_welltyped \<V> (subst_of unifier)"
  using is_welltyped_unify[OF unify] \<tau>
  by auto

lemma welltyped_the_mgu:
  assumes
    the_mgu: "the_mgu t t' = \<mu>" and
    \<tau>: "\<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau>"
  shows "term.subst.is_welltyped \<V> \<mu>"
  using assms is_welltyped_unify_single[of t t' _ \<V>]
  unfolding the_mgu_def mgu_def
  by (auto simp: welltyped.Var split: option.splits)

abbreviation welltyped_imgu_on where
  "welltyped_imgu_on X \<V> t t' \<mu> \<equiv>
    (\<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau>) \<and>
    term.subst.is_welltyped_on X \<V> \<mu> \<and>
    term_subst.is_imgu \<mu> {{t, t'}}"

abbreviation welltyped_imgu where
  "welltyped_imgu \<equiv> welltyped_imgu_on UNIV"

lemma obtain_welltyped_imgu:
  fixes \<upsilon> :: "('f, 'v) subst"
  assumes unified: "t \<cdot>t \<upsilon> = t' \<cdot>t \<upsilon>" and welltyped: "welltyped \<V> t \<tau>" "welltyped \<V> t' \<tau>"
  obtains \<mu> :: "('f, 'v) subst"
  where "\<upsilon> = \<mu> \<odot> \<upsilon>" "welltyped_imgu \<V> t t' \<mu>"
proof (rule that)

  show "\<upsilon> = (the_mgu t t') \<odot> \<upsilon>"
    using the_mgu[OF unified]
    by blast

  show "welltyped_imgu \<V> t t' (the_mgu t t')"
    using welltyped welltyped_the_mgu the_mgu_term_subst_is_imgu[OF unified]
    by blast
qed

lemma obtain_welltyped_imgu_on:
  fixes \<upsilon> :: "('f, 'v) subst"
  assumes "t \<cdot>t \<upsilon> = t' \<cdot>t \<upsilon>" "welltyped \<V> t \<tau>" "welltyped \<V> t' \<tau>"
  obtains \<mu> :: "('f, 'v) subst"
  where "\<upsilon> = \<mu> \<odot> \<upsilon>" "welltyped_imgu_on X \<V> t t' \<mu>"
  using obtain_welltyped_imgu[OF assms] UNIV_I
  by metis

end

end
