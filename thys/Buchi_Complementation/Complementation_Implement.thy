section {* Complementation Implementation *}

theory Complementation_Implement
imports
  "HOL-Library.Lattice_Syntax"
  "Transition_Systems_and_Automata.BA_Implement"
  "Complementation"
begin

  (* TODO: split this into refine and implement parts? *)

  type_synonym item = "nat \<times> bool"
  (* TODO: inline? *)
  type_synonym 'state items = "'state \<rightharpoonup> item"

  abbreviation "item_rel \<equiv> nat_rel \<times>\<^sub>r bool_rel"
  abbreviation "state_rel \<equiv> \<langle>nat_rel, item_rel\<rangle> list_map_rel"

  subsection {* Phase 1 *}

  definition cs_lr :: "'state items \<Rightarrow> 'state lr" where
    "cs_lr f \<equiv> map_option fst \<circ> f"
  definition cs_st :: "'state items \<Rightarrow> 'state st" where
    "cs_st f \<equiv> f -` Some ` snd -` {True}"
  abbreviation cs_abs :: "'state items \<Rightarrow> 'state cs" where
    "cs_abs f \<equiv> (cs_lr f, cs_st f)"
  definition cs_rep :: "'state cs \<Rightarrow> 'state items" where
    "cs_rep \<equiv> \<lambda> (g, P) p. map_option (\<lambda> k. (k, p \<in> P)) (g p)"

  lemma cs_abs_rep[simp]: "cs_rep (cs_abs f) = f"
  proof
    show "cs_rep (cs_abs f) x = f x" for x
      unfolding cs_lr_def cs_st_def cs_rep_def by (cases "f x") (force+)
  qed
  lemma cs_rep_lr[simp]: "cs_lr (cs_rep (g, P)) = g"
  proof
    show "cs_lr (cs_rep (g, P)) x = g x" for x
      unfolding cs_rep_def cs_lr_def by (cases "g x") (auto)
  qed
  lemma cs_rep_st[simp]: "cs_st (cs_rep (g, P)) = P \<inter> dom g"
    unfolding cs_rep_def cs_st_def by force

  lemma cs_lr_dom[simp]: "dom (cs_lr f) = dom f" unfolding cs_lr_def by simp
  lemma cs_lr_apply[simp]:
    assumes "p \<in> dom f"
    shows "the (cs_lr f p) = fst (the (f p))"
    using assms unfolding cs_lr_def by auto

  lemma cs_rep_dom[simp]: "dom (cs_rep (g, P)) = dom g" unfolding cs_rep_def by auto
  lemma cs_rep_apply[simp]:
    assumes "p \<in> dom f"
    shows "fst (the (cs_rep (f, P) p)) = the (f p)"
    using assms unfolding cs_rep_def by auto

  abbreviation cs_rel :: "('state items \<times> 'state cs) set" where
    "cs_rel \<equiv> br cs_abs top"

  lemma cs_rel_inv_single_valued: "single_valued (cs_rel\<inverse>)"
    by (auto intro!: inj_onI) (metis cs_abs_rep)

  definition refresh_1 :: "'state items \<Rightarrow> 'state items" where
    "refresh_1 f \<equiv> if True \<in> snd ` ran f then f else map_option (apsnd top) \<circ> f"
  definition ranks_1 ::
    "('label, 'state) ba \<Rightarrow> 'label \<Rightarrow> 'state items \<Rightarrow> 'state items set" where
    "ranks_1 A a f \<equiv> {g.
      dom g = UNION (dom f) (succ A a) \<and>
      (\<forall> p \<in> dom f. \<forall> q \<in> succ A a p. fst (the (g q)) \<le> fst (the (f p))) \<and>
      (\<forall> q \<in> dom g. accepting A q \<longrightarrow> even (fst (the (g q)))) \<and>
      cs_st g = {q \<in> UNION (cs_st f) (succ A a). even (fst (the (g q)))}}"
  definition complement_succ_1 ::
    "('label, 'state) ba \<Rightarrow> 'label \<Rightarrow> 'state items \<Rightarrow> 'state items set" where
    "complement_succ_1 A a = ranks_1 A a \<circ> refresh_1"
  definition complement_1 :: "('label, 'state) ba \<Rightarrow> ('label, 'state items) ba" where
    "complement_1 A \<equiv>
    \<lparr>
      alphabet = alphabet A,
      initial = {const (Some (2 * card (nodes A), False)) |` initial A},
      succ = complement_succ_1 A,
      accepting = \<lambda> f. cs_st f = {}
    \<rparr>"

  lemma refresh_1_dom[simp]: "dom (refresh_1 f) = dom f" unfolding refresh_1_def by simp
  lemma refresh_1_apply[simp]: "fst (the (refresh_1 f p)) = fst (the (f p))"
    unfolding refresh_1_def by (cases "f p") (auto)
  lemma refresh_1_cs_st[simp]: "cs_st (refresh_1 f) = (if cs_st f = {} then dom f else cs_st f)"
    unfolding refresh_1_def cs_st_def ran_def image_def vimage_def by auto

  lemma complement_succ_1_abs:
    assumes "g \<in> complement_succ_1 A a f"
    shows "cs_abs g \<in> complement_succ A a (cs_abs f)"
  unfolding complement_succ_def
  proof (simp, rule)
    have 1:
      "dom g = UNION (dom f) (succ A a)"
      "\<forall> p \<in> dom f. \<forall> q \<in> succ A a p. fst (the (g q)) \<le> fst (the (f p))"
      "\<forall> p \<in> dom g. accepting A p \<longrightarrow> even (fst (the (g p)))"
      using assms unfolding complement_succ_1_def ranks_1_def by simp_all
    show "cs_lr g \<in> lr_succ A a (cs_lr f)"
    unfolding lr_succ_def
    proof (intro CollectI conjI ballI impI)
      show "dom (cs_lr g) = UNION (dom (cs_lr f)) (succ A a)" using 1 by simp
    next
      fix p q
      assume 2: "p \<in> dom (cs_lr f)" "q \<in> succ A a p"
      have 3: "q \<in> dom (cs_lr g)" using 1 2 by auto
      show "the (cs_lr g q) \<le> the (cs_lr f p)" using 1 2 3 by simp
    next
      fix p
      assume 2: "p \<in> dom (cs_lr g)" "accepting A p"
      show "even (the (cs_lr g p))" using 1 2 by auto
    qed
    have 2: "cs_st g = {q \<in> UNION (cs_st (refresh_1 f)) (succ A a). even (fst (the (g q)))}"
      using assms unfolding complement_succ_1_def ranks_1_def by simp
    show "cs_st g = st_succ A a (cs_lr g) (cs_st f)"
    proof (cases "cs_st f = {}")
      case True
      have 3: "the (cs_lr g q) = fst (the (g q))" if "q \<in> UNION (dom f) (succ A a)" for q
        using that 1(1) by simp
      show ?thesis using 2 3 unfolding st_succ_def refresh_1_cs_st True cs_lr_dom 1(1) by force
    next
      case False
      have 3: "the (cs_lr g q) = fst (the (g q))" if "q \<in> UNION (cs_st f) (succ A a)" for q
        using that 1(1) by 
          (auto intro!: cs_lr_apply)
          (metis IntE UN_iff cs_abs_rep cs_lr_dom cs_rep_st domD prod.collapse)
      have "cs_st g = {q \<in> UNION (cs_st (refresh_1 f)) (succ A a). even (fst (the (g q)))}"
        using 2 by this
      also have "cs_st (refresh_1 f) = cs_st f" using False by simp
      also have "{q \<in> UNION (cs_st f) (succ A a). even (fst (the (g q)))} =
        {q \<in> UNION (cs_st f) (succ A a). even (the (cs_lr g q))}" using 3 by metis
      also have "\<dots> = st_succ A a (cs_lr g) (cs_st f)" unfolding st_succ_def using False by simp
      finally show ?thesis by this
    qed
  qed
  lemma complement_succ_1_rep:
    assumes "P \<subseteq> dom f" "(g, Q) \<in> complement_succ A a (f, P)"
    shows "cs_rep (g, Q) \<in> complement_succ_1 A a (cs_rep (f, P))"
  unfolding complement_succ_1_def ranks_1_def comp_apply
  proof (intro CollectI conjI ballI impI)
    have 1:
      "dom g = UNION (dom f) (succ A a)"
      "\<forall> p \<in> dom f. \<forall> q \<in> succ A a p. the (g q) \<le> the (f p)"
      "\<forall> p \<in> dom g. accepting A p \<longrightarrow> even (the (g p))"
      using assms(2) unfolding complement_succ_def lr_succ_def by simp_all
    have 2: "Q = {q \<in> if P = {} then dom g else UNION P (succ A a). even (the (g q))}"
      using assms(2) unfolding complement_succ_def st_succ_def by simp
    have 3: "Q \<subseteq> dom g" unfolding 2 1(1) using assms(1) by auto
    show "dom (cs_rep (g, Q)) = UNION (dom (refresh_1 (cs_rep (f, P)))) (succ A a)" using 1 by simp
    show "\<And> p q. p \<in> dom (refresh_1 (cs_rep (f, P))) \<Longrightarrow> q \<in> succ A a p \<Longrightarrow>
      fst (the (cs_rep (g, Q) q)) \<le> fst (the (refresh_1 (cs_rep (f, P)) p))"
      using 1(1, 2) by (auto) (metis UN_I cs_rep_apply domI option.sel)
    show "\<And> p. p \<in> dom (cs_rep (g, Q)) \<Longrightarrow> accepting A p \<Longrightarrow> even (fst (the (cs_rep (g, Q) p)))"
      using 1(1, 3) by auto
    show "cs_st (cs_rep (g, Q)) = {q \<in> UNION (cs_st (refresh_1 (cs_rep (f, P)))) (succ A a).
      even (fst (the (cs_rep (g, Q) q)))}"
    proof (cases "P = {}")
      case True
      have "cs_st (cs_rep (g, Q)) = Q" using 3 by auto
      also have "\<dots> = {q \<in> dom g. even (the (g q))}" unfolding 2 using True by auto
      also have "\<dots> = {q \<in> dom g. even (fst (the (cs_rep (g, Q) q)))}" using cs_rep_apply by metis
      also have "dom g = UNION (dom f) (succ A a)" using 1(1) by this
      also have "dom f = cs_st (refresh_1 (cs_rep (f, P)))" using True by simp
      finally show ?thesis by this
    next
      case False
      have 4: "fst (the (cs_rep (g, Q) q)) = the (g q)" if "q \<in> UNION P (succ A a)" for q
        using 1(1) that assms(1) by (fast intro: cs_rep_apply)
      have "cs_st (cs_rep (g, Q)) = Q" using 3 by auto
      also have "\<dots> = {q \<in> UNION P (succ A a). even (the (g q))}" unfolding 2 using False by auto
      also have "\<dots> = {q \<in> UNION P (succ A a). even (fst (the (cs_rep (g, Q) q)))}" using 4 by force
      also have "P = (cs_st (refresh_1 (cs_rep (f, P))))" using assms(1) False by auto
      finally show ?thesis by simp
    qed
  qed

  lemma complement_succ_1_refine: "(complement_succ_1, complement_succ) \<in>
    Id \<rightarrow> Id \<rightarrow> cs_rel \<rightarrow> \<langle>cs_rel\<rangle> set_rel"
  proof (clarsimp simp: br_set_rel_alt in_br_conv)
    fix A :: "('a, 'b) ba"
    fix a f
    show "complement_succ A a (cs_abs f) = cs_abs ` complement_succ_1 A a f"
    proof safe
      fix g Q
      assume 1: "(g, Q) \<in> complement_succ A a (cs_abs f)"
      have 2: "Q \<subseteq> dom g"
        using 1 unfolding complement_succ_def lr_succ_def st_succ_def
        by (auto) (metis IntE cs_abs_rep cs_lr_dom cs_rep_st)
      have 3: "cs_st f \<subseteq> dom (cs_lr f)" unfolding cs_st_def by auto
      show "(g, Q) \<in> cs_abs ` complement_succ_1 A a f"
      proof
        show "(g, Q) = cs_abs (cs_rep (g, Q))" using 2 by auto
        have "cs_rep (g, Q) \<in> complement_succ_1 A a (cs_rep (cs_abs f))"
          using complement_succ_1_rep 3 1 by this
        also have "cs_rep (cs_abs f) = f" by simp
        finally show "cs_rep (g, Q) \<in> complement_succ_1 A a f" by this
      qed
    next
      fix g
      assume 1: "g \<in> complement_succ_1 A a f"
      show "cs_abs g \<in> complement_succ A a (cs_abs f)" using complement_succ_1_abs 1 by this
    qed
  qed
  lemma complement_1_refine: "(complement_1, complement) \<in> \<langle>Id, Id, Id\<rangle> ba_rel \<rightarrow> \<langle>Id, cs_rel, Id\<rangle> ba_rel"
  unfolding complement_1_def complement_def
  proof parametricity
    fix A B :: "('a, 'b) ba"
    assume 1: "(A, B) \<in> \<langle>Id, Id, Id\<rangle> ba_rel"
    have 2: "(const (Some (2 * card (nodes B), False)) |` initial B,
      const (Some (2 * card (nodes B))) |` initial B, {}) \<in> cs_rel"
      unfolding cs_lr_def cs_st_def in_br_conv by (force simp: restrict_map_def)
    show "(complement_succ_1 A, complement_succ B) \<in> Id \<rightarrow> cs_rel \<rightarrow> \<langle>cs_rel\<rangle> set_rel"
      using complement_succ_1_refine 1 by parametricity auto
    show "({const (Some (2 * card (nodes A), False)) |` initial A},
      {const (Some (2 * card (nodes B))) |` initial B} \<times> {{}}) \<in> \<langle>cs_rel\<rangle> set_rel"
      using 1 2 by simp parametricity
    show "(\<lambda> f. cs_st f = {}, \<lambda> (f, P). P = {}) \<in> cs_rel \<rightarrow> bool_rel" by (auto simp: in_br_conv)
  qed

  subsection {* Phase 2 *}

  definition ranks_2 :: "('label, 'state) ba \<Rightarrow> 'label \<Rightarrow> 'state items \<Rightarrow> 'state items set" where
    "ranks_2 A a f \<equiv> {g.
      dom g = UNION (dom f) (succ A a) \<and>
      (\<forall> q l d. g q = Some (l, d) \<longrightarrow>
        l \<le> \<Sqinter> (fst ` Some -` f ` pred A a q) \<and>
        (d \<longleftrightarrow> \<Squnion> (snd ` Some -` f ` pred A a q) \<and> even l) \<and>
        (accepting A q \<longrightarrow> even l))}"
  definition complement_succ_2 ::
    "('label, 'state) ba \<Rightarrow> 'label \<Rightarrow> 'state items \<Rightarrow> 'state items set" where
    "complement_succ_2 A a \<equiv> ranks_2 A a \<circ> refresh_1"
  definition complement_2 :: "('label, 'state) ba \<Rightarrow> ('label, 'state items) ba" where
    "complement_2 A \<equiv>
    \<lparr>
      alphabet = alphabet A,
      initial = {const (Some (2 * card (nodes A), False)) |` initial A},
      succ = complement_succ_2 A,
      accepting = \<lambda> f. True \<notin> snd ` ran f
    \<rparr>"

  lemma ranks_2_refine: "ranks_2 = ranks_1"
  proof (intro ext)
    fix A :: "('a, 'b) ba" and a f
    show "ranks_2 A a f = ranks_1 A a f"
    proof safe
      fix g
      assume 1: "g \<in> ranks_2 A a f"
      have 2: "dom g = UNION (dom f) (succ A a)" using 1 unfolding ranks_2_def by auto
      have 3: "g q = Some (l, d) \<Longrightarrow> l \<le> \<Sqinter> (fst ` Some -` f ` pred A a q)" for q l d
        using 1 unfolding ranks_2_def by auto
      have 4: "g q = Some (l, d) \<Longrightarrow> d \<longleftrightarrow> \<Squnion> (snd ` Some -` f ` pred A a q) \<and> even l" for q l d
        using 1 unfolding ranks_2_def by auto
      have 5: "g q = Some (l, d) \<Longrightarrow> accepting A q \<Longrightarrow> even l" for q l d
        using 1 unfolding ranks_2_def by auto
      show "g \<in> ranks_1 A a f"
      unfolding ranks_1_def
      proof (intro CollectI conjI ballI impI)
        show "dom g = UNION (dom f) (succ A a)" using 2 by this
      next
        fix p q
        assume 10: "p \<in> dom f" "q \<in> succ A a p"
        obtain k c where 11: "f p = Some (k, c)" using 10(1) by auto
        have 12: "q \<in> dom g" using 10 2 by auto
        obtain l d where 13: "g q = Some (l, d)" using 12 by auto
        have "fst (the (g q)) = l" unfolding 13 by simp
        also have "\<dots> \<le> \<Sqinter> (fst ` Some -` f ` pred A a q)" using 3 13 by this
        also have "\<dots> \<le> k"
        proof (rule cInf_lower)
          show "k \<in> fst ` Some -` f ` pred A a q" using 11 10(2) by force
          show "bdd_below (fst ` Some -` f ` pred A a q)" by simp
        qed
        also have "\<dots> = fst (the (f p))" unfolding 11 by simp
        finally show "fst (the (g q)) \<le> fst (the (f p))" by this
      next
        fix q
        assume 10: "q \<in> dom g" "accepting A q"
        show "even (fst (the (g q)))" using 10 5 by auto
      next
        show "cs_st g = {q \<in> UNION (cs_st f) (succ A a). even (fst (the (g q)))}"
        proof
          show "cs_st g \<subseteq> {q \<in> UNION (cs_st f) (succ A a). even (fst (the (g q)))}"
            using 4 unfolding cs_st_def image_def vimage_def by auto metis+
          show "{q \<in> UNION (cs_st f) (succ A a). even (fst (the (g q)))} \<subseteq> cs_st g"
          proof safe
            fix p q
            assume 10: "even (fst (the (g q)))" "p \<in> cs_st f" "q \<in> succ A a p"
            have 12: "q \<in> dom g" using 10 2 unfolding cs_st_def by auto
            show "q \<in> cs_st g" using 10 4 12 unfolding cs_st_def image_def by force
          qed
        qed
      qed
    next
      fix g
      assume 1: "g \<in> ranks_1 A a f"
      have 2: "dom g = UNION (dom f) (succ A a)" using 1 unfolding ranks_1_def by auto
      have 3: "\<And> p q. p \<in> dom f \<Longrightarrow> q \<in> succ A a p \<Longrightarrow> fst (the (g q)) \<le> fst (the (f p))"
        using 1 unfolding ranks_1_def by auto
      have 4: "\<And> q. q \<in> dom g \<Longrightarrow> accepting A q \<Longrightarrow> even (fst (the (g q)))"
        using 1 unfolding ranks_1_def by auto
      have 5: "cs_st g = {q \<in> UNION (cs_st f) (succ A a). even (fst (the (g q)))}"
        using 1 unfolding ranks_1_def by auto
      show "g \<in> ranks_2 A a f"
        unfolding ranks_2_def
      proof (intro CollectI conjI allI impI)
        show "dom g = UNION (dom f) (succ A a)" using 2 by this
      next
        fix q l d
        assume 10: "g q = Some (l, d)"
        have 11: "q \<in> dom g" using 10 by auto
        show "l \<le> \<Sqinter> (fst ` Some -` f ` pred A a q)"
        proof (rule cInf_greatest)
          show "fst ` Some -` f ` pred A a q \<noteq> {}" using 11 unfolding 2 image_def vimage_def by force
          show "\<And> x. x \<in> fst ` Some -` f ` pred A a q \<Longrightarrow> l \<le> x"
            using 3 10 by (auto) (metis domI fst_conv option.sel)
        qed
        have "d \<longleftrightarrow> q \<in> cs_st g" unfolding cs_st_def by (force simp: 10)
        also have "cs_st g = {q \<in> UNION (cs_st f) (succ A a). even (fst (the (g q)))}" using 5 by this
        also have "q \<in> \<dots> \<longleftrightarrow> (\<exists> x \<in> cs_st f. q \<in> succ A a x) \<and> even l"
          unfolding mem_Collect_eq 10 by simp
        also have "\<dots> \<longleftrightarrow> \<Squnion> (snd ` Some -` f ` pred A a q) \<and> even l"
          unfolding cs_st_def image_def vimage_def by auto metis+
        finally show "d \<longleftrightarrow> \<Squnion> (snd ` Some -` f ` pred A a q) \<and> even l" by this
        show "accepting A q \<Longrightarrow> even l" using 4 10 11 by force
      qed
    qed
  qed

  lemma complement_2_refine: "(complement_2, complement_1) \<in> \<langle>Id, Id, Id\<rangle> ba_rel \<rightarrow> \<langle>Id, Id, Id\<rangle> ba_rel"
    unfolding complement_2_def complement_1_def complement_succ_2_def complement_succ_1_def
    unfolding ranks_2_refine cs_st_def image_def vimage_def ran_def by auto

  subsection {* Phase 3 *}

  definition bounds_3 :: "('label, 'state) ba \<Rightarrow> 'label \<Rightarrow> 'state items \<Rightarrow> 'state items" where
    "bounds_3 A a f \<equiv> \<lambda> q. let S = Some -` f ` pred A a q in
      if S = {} then None else Some (INFIMUM S fst, SUPREMUM S snd)"
  definition items_3 :: "('label, 'state) ba \<Rightarrow> 'state \<Rightarrow> item \<Rightarrow> item set" where
    "items_3 A p \<equiv> \<lambda> (k, c). {(l, c \<and> even l) |l. l \<le> k \<and> (accepting A p \<longrightarrow> even l)}"
  definition get_3 :: "('label, 'state) ba \<Rightarrow> 'state items \<Rightarrow> ('state \<rightharpoonup> item set)" where
    "get_3 A f \<equiv> \<lambda> p. map_option (items_3 A p) (f p)"
  definition complement_succ_3 ::
    "('label, 'state) ba \<Rightarrow> 'label \<Rightarrow> 'state items \<Rightarrow> 'state items set" where
    "complement_succ_3 A a \<equiv> expand_map \<circ> get_3 A \<circ> bounds_3 A a \<circ> refresh_1"
  definition complement_3 :: "('label, 'state) ba \<Rightarrow> ('label, 'state items) ba" where
    "complement_3 A \<equiv>
    \<lparr>
      alphabet = alphabet A,
      initial = {(Some \<circ> (const (2 * card (nodes A), False))) |` initial A},
      succ = complement_succ_3 A,
      accepting = \<lambda> f. \<forall> (p, k, c) \<in> map_to_set f. \<not> c
    \<rparr>"

  lemma bounds_3_dom[simp]: "dom (bounds_3 A a f) = UNION (dom f) (succ A a)"
    unfolding bounds_3_def Let_def dom_def by (force split: if_splits)

  lemma items_3_nonempty[intro!, simp]: "items_3 A p s \<noteq> {}" unfolding items_3_def by auto
  lemma items_3_finite[intro!, simp]: "finite (items_3 A p s)"
    unfolding items_3_def by (auto split: prod.splits)

  lemma get_3_dom[simp]: "dom (get_3 A f) = dom f" unfolding get_3_def by (auto split: bind_splits)
  lemma get_3_finite[intro, simp]: "S \<in> ran (get_3 A f) \<Longrightarrow> finite S"
    unfolding get_3_def ran_def by auto
  lemma get_3_update[simp]: "get_3 A (f (p \<mapsto> s)) = (get_3 A f) (p \<mapsto> items_3 A p s)"
    unfolding get_3_def by auto

  lemma expand_map_get_bounds_3: "expand_map \<circ> get_3 A \<circ> bounds_3 A a = ranks_2 A a"
  proof (intro ext set_eqI, unfold comp_apply)
    fix f g
    have 1: "(\<forall> x S y. get_3 A (bounds_3 A a f) x = Some S \<longrightarrow> g x = Some y \<longrightarrow> y \<in> S) \<longleftrightarrow>
      (\<forall> q S l d. get_3 A (bounds_3 A a f) q = Some S \<longrightarrow> g q = Some (l, d) \<longrightarrow> (l, d) \<in> S)"
      by auto
    have 2: "(\<forall> S. get_3 A (bounds_3 A a f) q = Some S \<longrightarrow> g q = Some (l, d) \<longrightarrow> (l, d) \<in> S) \<longleftrightarrow>
      (g q = Some (l, d) \<longrightarrow> l \<le> INFIMUM (Some -` f ` pred A a q) fst \<and>
      (d \<longleftrightarrow> SUPREMUM (Some -` f ` pred A a q) snd \<and> even l) \<and> (accepting A q \<longrightarrow> even l))"
      if 3: "dom g = UNION (dom f) (succ A a)" for q l d
    proof -
      have 4: "q \<notin> dom g" if "Some -` f ` pred A a q = {}" unfolding 3 using that by force
      show ?thesis unfolding get_3_def items_3_def bounds_3_def Let_def using 4 by auto
    qed
    show "g \<in> expand_map (get_3 A (bounds_3 A a f)) \<longleftrightarrow> g \<in> ranks_2 A a f"
      unfolding expand_map_alt_def ranks_2_def mem_Collect_eq
      unfolding get_3_dom bounds_3_dom 1 using 2 by blast
  qed

  lemma complement_succ_3_refine: "complement_succ_3 = complement_succ_2"
    unfolding complement_succ_3_def complement_succ_2_def expand_map_get_bounds_3 by rule
  lemma complement_initial_3_refine: "{const (Some (2 * card (nodes A), False)) |` initial A} =
    {(Some \<circ> (const (2 * card (nodes A), False))) |` initial A}"
    unfolding comp_apply by rule
  lemma complement_accepting_3_refine: "True \<notin> snd ` ran f \<longleftrightarrow> (\<forall> (p, k, c) \<in> map_to_set f. \<not> c)"
    unfolding map_to_set_def ran_def by auto

  lemma complement_3_refine: "(complement_3, complement_2) \<in> \<langle>Id, Id, Id\<rangle> ba_rel \<rightarrow> \<langle>Id, Id, Id\<rangle> ba_rel"
    unfolding complement_3_def complement_2_def
    unfolding complement_succ_3_refine complement_initial_3_refine complement_accepting_3_refine
    by auto

  subsection {* Phase 4 *}

  (* TODO: find abstract representations for all of these, have them implemented by autoref,
    we don't want to deal with this intermediate representation by hand on the overall algorithm
    level, since it's all compositional and can be handled on an operations level,
    although some things can't be implemented on an operations level since we have to prove
    at some point that the nondeterminism actually doesn't matter, like with expand_map
    just keep the 3 step process (abstract, abstract algorithm, implementation) as short and
    isolated as possible in these cases, use resulting transitive rule as autoref rule, don't
    do the composition by hand *)
  (* TODO: this is just a map (or build_map?), can't autoref do this? *)
  (* TODO: it would be ideal if we could just give a deterministic abstract specification for
    the whole complement automaton from which autoref can generate the implementation automaton
    with the correct refinement statement *)
  definition refresh_4 :: "'state items \<Rightarrow> 'state items nres" where
    "refresh_4 f \<equiv> if \<exists> (p, k, c) \<in> map_to_set f. c
      then RETURN f
      else do
      {
        ASSUME (finite (dom f));
        FOREACH (map_to_set f) (\<lambda> (p, k, c) m. do
        {
          ASSERT (p \<notin> dom m);
          RETURN (m (p \<mapsto> (k, True)))
        }
        ) empty
      }"
  definition merge_4 :: "item \<Rightarrow> item option \<Rightarrow> item" where
    "merge_4 \<equiv> \<lambda> (k, c). \<lambda> None \<Rightarrow> (k, c) | Some (l, d) \<Rightarrow> (k \<sqinter> l, c \<squnion> d)"
  definition bounds_4 :: "('label, 'state) ba \<Rightarrow> 'label \<Rightarrow> 'state items \<Rightarrow> 'state items nres" where
    "bounds_4 A a f \<equiv> do
    {
      ASSUME (finite (dom f));
      ASSUME (\<forall> p. finite (succ A a p));
      FOREACH (map_to_set f) (\<lambda> (p, s) m.
        FOREACH (succ A a p) (\<lambda> q f.
          RETURN (f (q \<mapsto> merge_4 s (f q))))
        m)
      empty
    }"
  definition items_4 :: "('label, 'state) ba \<Rightarrow> 'state \<Rightarrow> item \<Rightarrow> item set" where
    "items_4 A p \<equiv> \<lambda> (k, c). do
    {
      let values = if accepting A p then Set.filter even {.. k} else {.. k};
      let item = \<lambda> l. (l, c \<and> even l);
      item ` values
    }"
  definition get_4 :: "('label, 'state) ba \<Rightarrow> 'state items \<Rightarrow> ('state \<rightharpoonup> item set)" where
    "get_4 A f \<equiv> \<lambda> p. map_option (items_4 A p) (f p)"
  definition expand_4 :: "('a \<rightharpoonup> 'b set) \<Rightarrow> ('a \<rightharpoonup> 'b) set nres" where
    "expand_4 f \<equiv> FOREACH (map_to_set f) (\<lambda> (x, S) X. do {
        ASSERT (\<forall> g \<in> X. x \<notin> dom g);
        ASSERT (\<forall> a \<in> S. \<forall> b \<in> S. a \<noteq> b \<longrightarrow> (\<lambda> y. (\<lambda> g. g (x \<mapsto> y)) ` X) a \<inter> (\<lambda> y. (\<lambda> g. g (x \<mapsto> y)) ` X) b = {});
        RETURN (\<Union> y \<in> S. (\<lambda> g. g (x \<mapsto> y)) ` X)
      }) {empty}"
  definition complement_succ_4 ::
    "('label, 'state) ba \<Rightarrow> 'label \<Rightarrow> 'state items \<Rightarrow> 'state items set nres" where
    "complement_succ_4 A a f \<equiv> do
    {
      f \<leftarrow> refresh_4 f;
      f \<leftarrow> bounds_4 A a f;
      ASSUME (finite (dom f));
      expand_4 (get_4 A f)
    }"

  lemma bounds_3_empty: "bounds_3 A a empty = empty"
    unfolding bounds_3_def Let_def by auto
  lemma bounds_3_update: "bounds_3 A a (f (p \<mapsto> s)) =
    override_on (bounds_3 A a f) (Some \<circ> merge_4 s \<circ> bounds_3 A a (f (p := None))) (succ A a p)"
  proof
    note fun_upd_image[simp]
    fix q
    show "bounds_3 A a (f (p \<mapsto> s)) q =
      override_on (bounds_3 A a f) (Some \<circ> merge_4 s \<circ> bounds_3 A a (f (p := None))) (succ A a p) q"
    proof (cases "q \<in> succ A a p")
      case True
      define S where "S \<equiv> Some -` f ` (pred A a q - {p})"
      have 1: "Some -` f (p := Some s) ` pred A a q = insert s S" using True unfolding S_def by auto
      have 2: "Some -` f (p := None) ` pred A a q = S" unfolding S_def by auto
      have "bounds_3 A a (f (p \<mapsto> s)) q = Some (INFIMUM (insert s S) fst, SUPREMUM (insert s S) snd)"
        unfolding bounds_3_def 1 by simp
      also have "\<dots> = Some (merge_4 s (bounds_3 A a (f (p := None)) q))"
        unfolding 2 bounds_3_def merge_4_def by (cases s) (auto simp: cINF_insert)
      also have "\<dots> = override_on (bounds_3 A a f) (Some \<circ> merge_4 s \<circ> bounds_3 A a (f (p := None)))
        (succ A a p) q" using True by simp
      finally show ?thesis by this
    next
      case False
      show ?thesis using False unfolding bounds_3_def by simp
    qed
  qed

  lemma refresh_4_refine: "(refresh_4, \<lambda> f. RETURN (refresh_1 f)) \<in> Id \<rightarrow> \<langle>Id\<rangle> nres_rel"
  proof safe
    fix f :: "'a \<Rightarrow> item option"
    have 1: "(\<exists> (p, k, c) \<in> map_to_set f. c) \<longleftrightarrow> True \<in> snd ` ran f"
      unfolding image_def map_to_set_def ran_def by force
    show "(refresh_4 f, RETURN (refresh_1 f)) \<in> \<langle>Id\<rangle> nres_rel"
      unfolding refresh_4_def refresh_1_def 1
      by (refine_vcg FOREACH_rule_map_eq[where X = "\<lambda> m. map_option (apsnd \<top>) \<circ> m"]) (auto)
  qed
  lemma bounds_4_refine: "(bounds_4 A a, \<lambda> f. RETURN (bounds_3 A a f)) \<in> Id \<rightarrow> \<langle>Id\<rangle> nres_rel"
    unfolding bounds_4_def by
      (refine_vcg FOREACH_rule_map_eq[where X = "bounds_3 A a"] FOREACH_rule_insert_eq)
      (auto simp: override_on_insert bounds_3_empty bounds_3_update)
  lemma items_4_refine: "items_4 = items_3"
    unfolding items_4_def items_3_def by (intro ext) (auto split: if_splits)
  lemma get_4_refine: "get_4 = get_3"
    unfolding get_4_def get_3_def items_4_refine by rule
  lemma expand_4_refine: "(expand_4 f, ASSERT (finite (dom f)) \<then> RETURN (expand_map f)) \<in> \<langle>Id\<rangle> nres_rel"
    unfolding expand_4_def
    by (refine_vcg FOREACH_rule_map_eq[where X = expand_map]) (auto dest!: expand_map_dom map_upd_eqD1)

  lemma complement_succ_4_refine: "(complement_succ_4, RETURN \<circ>\<circ>\<circ> complement_succ_3) \<in>
    Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle> nres_rel"
    unfolding complement_succ_4_def complement_succ_3_def get_4_refine comp_apply
    by (refine_vcg vcg1[OF refresh_4_refine] vcg1[OF bounds_4_refine] vcg0[OF expand_4_refine]) (auto)

  subsection {* Phase 5 *}

  definition expand_map_get_5 :: "('label, 'state) ba \<Rightarrow> 'state items \<Rightarrow> 'state items set nres" where
    "expand_map_get_5 A f \<equiv> FOREACH (map_to_set f) (\<lambda> (k, v) X. do {
      ASSERT (\<forall> g \<in> X. k \<notin> dom g);
      ASSERT (\<forall> a \<in> (items_4 A k v). \<forall> b \<in> (items_4 A k v). a \<noteq> b \<longrightarrow> (\<lambda> y. (\<lambda> g. g (k \<mapsto> y)) ` X) a \<inter> (\<lambda> y. (\<lambda> g. g (k \<mapsto> y)) ` X) b = {});
      RETURN (\<Union> y \<in> items_4 A k v. (\<lambda> g. g (k \<mapsto> y)) ` X)
      }) {empty}"

  lemma expand_map_get_5_refine: "(expand_map_get_5, expand_4 \<circ>\<circ> get_4) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle> nres_rel"
    unfolding expand_map_get_5_def expand_4_def get_4_def by (auto intro: FOREACH_rule_map_map[param_fo])

  definition complement_succ_5 ::
    "('label, 'state) ba \<Rightarrow> 'label \<Rightarrow> 'state items \<Rightarrow> 'state items set nres" where
    "complement_succ_5 A a f \<equiv> do
    {
      f \<leftarrow> refresh_4 f;
      f \<leftarrow> bounds_4 A a f;
      ASSUME (finite (dom f));
      expand_map_get_5 A f
    }"

  lemma complement_succ_5_refine:
    "(complement_succ_5, complement_succ_4) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle> nres_rel"
    unfolding complement_succ_5_def complement_succ_4_def
    by (refine_vcg vcg2[OF expand_map_get_5_refine]) (auto intro: refine_IdI)

  subsection {* Phase 6 *}

  interpretation autoref_syn by this

  context
    fixes fi f
    assumes fi[autoref_rules]: "(fi, f) \<in> \<langle>nat_rel, item_rel\<rangle> list_map_rel"
  begin

    private lemma [simp]: "finite (dom f)"
      using list_map_rel_finite fi unfolding finite_map_rel_def by force

    schematic_goal refresh_6: "(?f :: ?'a, refresh_4 f) \<in> ?R"
      unfolding refresh_4_def by (autoref_monadic (plain))

  end

  concrete_definition refresh_6 uses refresh_6

  lemma refresh_6_refine:
    "(\<lambda> f. RETURN (refresh_6 f), refresh_4) \<in>
    \<langle>nat_rel, item_rel\<rangle> list_map_rel \<rightarrow> \<langle>\<langle>nat_rel, item_rel\<rangle> list_map_rel\<rangle> nres_rel"
    using refresh_6.refine by fast

  context
    fixes A :: "('label, nat) ba"
    fixes succi a fi f
    assumes succi[autoref_rules]: "(succi, succ A a) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle> list_set_rel"
    assumes fi[autoref_rules]: "(fi, f) \<in> \<langle>nat_rel, item_rel\<rangle> list_map_rel"
  begin

    private lemma [simp]: "finite (succ A a p)"
      using list_set_rel_finite succi[param_fo] unfolding finite_set_rel_def by blast
    private lemma [simp]: "finite (dom f)"
      using list_map_rel_finite fi unfolding finite_map_rel_def by force

    private lemma [autoref_op_pat]: "succ A a \<equiv> OP (succ A a)" by simp

    private lemma [autoref_rules]: "(min, min) \<in> nat_rel \<rightarrow> nat_rel \<rightarrow> nat_rel" by simp

    schematic_goal bounds_6: "(?f :: ?'a, bounds_4 A a f) \<in> ?R"
      unfolding bounds_4_def merge_4_def sup_bool_def inf_nat_def by (autoref_monadic (plain))

  end

  concrete_definition bounds_6 uses bounds_6

  lemma bounds_6_refine: "(si, succ A a) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle> list_set_rel \<Longrightarrow>
    (\<lambda> p. RETURN (bounds_6 si p), bounds_4 A a) \<in>
    \<langle>nat_rel, item_rel\<rangle> list_map_rel \<rightarrow> \<langle>\<langle>nat_rel, item_rel\<rangle> dflt_ahm_rel\<rangle> nres_rel"
    using bounds_6.refine by auto

  context
    fixes A :: "('label, nat) ba"
    fixes acci
    assumes [autoref_rules]: "(acci, accepting A) \<in> nat_rel \<rightarrow> bool_rel"
  begin

    private lemma [autoref_op_pat]: "accepting A \<equiv> OP (accepting A)" by simp

    private lemma [autoref_rules]: "((dvd), (dvd)) \<in> nat_rel \<rightarrow> nat_rel \<rightarrow> bool_rel" by simp
    private lemma [autoref_rules]: "(\<lambda> k. upt 0 (Suc k), atMost) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle> list_set_rel"
      by (auto simp: list_set_rel_def in_br_conv)

    schematic_goal items_6: "(?f :: ?'a, items_4 A) \<in> ?R"
      unfolding items_4_def Let_def Set.filter_def by autoref

  end

  concrete_definition items_6 uses items_6

  (* TODO: use generic expand_map implementation *)
  context
    fixes A :: "('label, nat) ba"
    fixes ai
    fixes fi f
    assumes ai: "(ai, accepting A) \<in> nat_rel \<rightarrow> bool_rel"
    assumes fi[autoref_rules]: "(fi, f) \<in> \<langle>nat_rel, item_rel\<rangle> dflt_ahm_rel"
  begin

    private lemma [simp]: "finite (dom f)"
      using dflt_ahm_rel_finite_nat fi unfolding finite_map_rel_def by force
    private lemma [simp]:
      assumes "\<And> m. m \<in> S \<Longrightarrow> x \<notin> dom m"
      shows "inj_on (\<lambda> m. m (x \<mapsto> y)) S"
      using assms unfolding dom_def inj_on_def by (auto) (metis fun_upd_triv fun_upd_upd)
    private lemmas [simp] = op_map_update_def[abs_def]

    private lemma UNION_pat[autoref_op_pat]: "UNION S m \<equiv> OP UNION S m" by simp
    private lemma [autoref_op_pat]: "items_4 A \<equiv> OP (items_4 A)" by simp

    private lemmas [autoref_rules] = items_6.refine[OF ai]

    schematic_goal expand_map_get_6: "(?f, expand_map_get_5 A f) \<in>
      \<langle>\<langle>\<langle>nat_rel, item_rel\<rangle> list_map_rel\<rangle> list_set_rel\<rangle> nres_rel"
      unfolding expand_map_get_5_def by (autoref_monadic (plain))

    lemmas [autoref_op_pat del] = UNION_pat

  end

  concrete_definition expand_map_get_6 uses expand_map_get_6

  lemma expand_map_get_6_refine:
    assumes "(ai, accepting A) \<in> nat_rel \<rightarrow> bool_rel"
    shows "(\<lambda> fi. RETURN (expand_map_get_6 ai fi),
      \<lambda> f. ASSUME (finite (dom f)) \<then> expand_map_get_5 A f) \<in>
      \<langle>nat_rel, item_rel\<rangle> dflt_ahm_rel \<rightarrow> \<langle>\<langle>\<langle>nat_rel, item_rel\<rangle> list_map_rel\<rangle> list_set_rel\<rangle> nres_rel"
    using expand_map_get_6.refine[OF assms] by auto

  context
    fixes A :: "('label, nat) ba"
    fixes a :: "'label"
    fixes p :: "nat items"
    fixes Ai
    fixes ai
    fixes pi
    assumes Ai: "(Ai, A) \<in> \<langle>Id, Id, Id\<rangle> bai_ba_rel"
    assumes ai: "(ai, a) \<in> Id"
    assumes pi[autoref_rules]: "(pi, p) \<in> \<langle>nat_rel, item_rel\<rangle> list_map_rel"
  begin

    private lemmas succi = bai_ba_param(4)[THEN fun_relD, OF Ai, THEN fun_relD, OF ai]
    private lemmas acceptingi = bai_ba_param(5)[THEN fun_relD, OF Ai]

    private lemma [autoref_op_pat]: "(\<lambda> g. ASSUME (finite (dom g)) \<then> expand_map_get_5 A g) \<equiv>
      OP (\<lambda> g. ASSUME (finite (dom g)) \<then> expand_map_get_5 A g)" by simp
    private lemma [autoref_op_pat]: "bounds_4 A a \<equiv> OP (bounds_4 A a)" by simp

    private lemmas [autoref_rules] =
      refresh_6_refine
      bounds_6_refine[OF succi]
      expand_map_get_6_refine[OF acceptingi]

    schematic_goal complement_succ_6: "(?f :: ?'a, complement_succ_5 A a p) \<in> ?R"
      unfolding complement_succ_5_def by (autoref_monadic (plain))

  end

  concrete_definition complement_succ_6 uses complement_succ_6

  lemma complement_succ_6_refine:
    "(RETURN \<circ>\<circ>\<circ> complement_succ_6, complement_succ_5) \<in>
      \<langle>Id, Id, Id\<rangle> bai_ba_rel \<rightarrow> Id \<rightarrow> \<langle>nat_rel, item_rel\<rangle> list_map_rel \<rightarrow>
      \<langle>\<langle>\<langle>nat_rel, item_rel\<rangle> list_map_rel\<rangle> list_set_rel\<rangle> nres_rel"
    using complement_succ_6.refine unfolding comp_apply by parametricity

  context
    fixes A :: "('label, nat) ba"
    fixes Ai
    fixes n ni :: nat
    assumes Ai: "(Ai, A) \<in> \<langle>Id, Id, Id\<rangle> bai_ba_rel"
    assumes ni[autoref_rules]: "(ni, n) \<in> Id"
  begin

    private lemma [autoref_op_pat]: "initial A \<equiv> OP (initial A)" by simp

    private lemmas [autoref_rules] = bai_ba_param(3)[THEN fun_relD, OF Ai]

    schematic_goal complement_initial_6:
      "(?f :: ?'a, {(Some \<circ> (const (2 * n, False))) |` initial A}) \<in> ?R"
      by autoref

  end

  concrete_definition complement_initial_6 uses complement_initial_6

  schematic_goal complement_accepting_6: "(?f :: ?'a, \<lambda> f. \<forall> (p, k, c) \<in> map_to_set f. \<not> c) \<in> ?R"
    by autoref

  concrete_definition complement_accepting_6 uses complement_accepting_6

  definition complement_6 :: "('label, nat) bai \<Rightarrow> nat \<Rightarrow> ('label, (nat \<times> item) list) bai" where
    "complement_6 Ai ni \<equiv>
    \<lparr>
      alphabeti = alphabeti Ai,
      initiali = complement_initial_6 Ai ni,
      succi = complement_succ_6 Ai,
      acceptingi = complement_accepting_6
    \<rparr>"

  lemma complement_6_refine[autoref_rules]:
    assumes "(Ai, A) \<in> \<langle>Id, Id, Id\<rangle> bai_ba_rel"
    assumes "(ni,
      (OP card ::: \<langle>Id\<rangle> ahs_rel bhc \<rightarrow> nat_rel) $
      ((OP nodes ::: \<langle>Id, Id, Id\<rangle> bai_ba_rel \<rightarrow> \<langle>Id\<rangle> ahs_rel bhc) $ A)) \<in> nat_rel"
    shows "(complement_6 Ai ni, (OP complement_3 :::
      \<langle>Id, Id, Id\<rangle> bai_ba_rel \<rightarrow> \<langle>Id, state_rel, Id\<rangle> bai_ba_rel) $ A) \<in> \<langle>Id, state_rel, Id\<rangle> bai_ba_rel"
  proof -
    note complement_succ_6_refine
    also note complement_succ_5_refine
    also note complement_succ_4_refine
    finally have 1: "(complement_succ_6, complement_succ_3) \<in>
      \<langle>Id, Id, Id\<rangle> bai_ba_rel \<rightarrow> Id \<rightarrow> state_rel \<rightarrow> \<langle>state_rel\<rangle> list_set_rel"
      unfolding nres_rel_comp unfolding nres_rel_def unfolding fun_rel_def by auto
    show ?thesis
      unfolding complement_6_def complement_3_def
      using 1 complement_initial_6.refine complement_accepting_6.refine assms
      unfolding autoref_tag_defs
      by parametricity
  qed

  theorem complement_6_correct:
    assumes "bai A" "finite (nodes (ba A))"
    shows "language (ba (complement_6 A (card (nodes (ba A))))) =
      streams (alphabet (ba A)) - language (ba A)"
  proof -
    let ?I = "\<langle>\<langle>Id\<rangle> stream_rel\<rangle> set_rel"
    let ?n = "card (nodes (ba A))"
    have 1: "(A, ba A) \<in> \<langle>Id, Id, Id\<rangle> bai_ba_rel"
      unfolding bai_ba_br in_br_conv using assms(1) by auto
    have "(language (ba (complement_6 A ?n)), language (id (complement_3 (ba A)))) \<in> ?I"
      using complement_6_refine 1 by parametricity auto
    also have "language (id (complement_3 (ba A))) = language (complement_3 (ba A))" by simp
    also have "(language (complement_3 (ba A)), language (complement_2 (ba A))) \<in> ?I"
      using complement_3_refine by parametricity auto
    also have "(language (complement_2 (ba A)), language (complement_1 (ba A))) \<in> ?I"
      using complement_2_refine by parametricity auto
    also have "(language (complement_1 (ba A)), language (complement (ba A))) \<in> ?I"
      using complement_1_refine by parametricity auto
    also have "language (complement (ba A)) = streams (alphabet (ba A)) - language (ba A)"
      using complement_language assms(2) by this
    finally show ?thesis by simp
  qed

  (* TODO: possible optimizations:
    - introduce op_map_map operation for maps instead of manually iterating via FOREACH
    - consolidate various binds and maps in expand_map_get_6 *)

  export_code complement_6 in SML module_name Complementation

end
