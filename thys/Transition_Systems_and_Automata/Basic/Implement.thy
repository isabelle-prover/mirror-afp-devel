section {* Implementation *}

theory Implement
imports
  "HOL-Library.Monad_Syntax"
  "Collections.Refine_Dflt"
  "Refine"
begin

  subsection {* Syntax *}

  (* TODO: this syntax has unnecessarily high inner binding strength, requiring extra parentheses
    the regular let syntax correctly uses inner binding strength 0: ("(2_ =/ _)" 10) *)
  no_syntax "_do_let" :: "[pttrn, 'a] \<Rightarrow> do_bind" ("(2let _ =/ _)" [1000, 13] 13)
  syntax "_do_let" :: "[pttrn, 'a] \<Rightarrow> do_bind" ("(2let _ =/ _)" 13)

  subsection {* Monadic Refinement *}

  lemmas [refine] = plain_nres_relI

  lemma vcg0:
    assumes "(f, g) \<in> \<langle>Id\<rangle> nres_rel"
    shows "g \<le> h \<Longrightarrow> f \<le> h"
    using order_trans nres_relD[OF assms[param_fo, OF], THEN refine_IdD] by this
  lemma vcg1:
    assumes "(f, g) \<in> Id \<rightarrow> \<langle>Id\<rangle> nres_rel"
    shows "g x \<le> h x \<Longrightarrow> f x \<le> h x"
    using order_trans nres_relD[OF assms[param_fo, OF IdI], THEN refine_IdD] by this
  lemma vcg2:
    assumes "(f, g) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle> nres_rel"
    shows "g x y \<le> h x y \<Longrightarrow> f x y \<le> h x y"
    using order_trans nres_relD[OF assms[param_fo, OF IdI IdI], THEN refine_IdD] by this

  lemma FOREACH_rule_insert:
    assumes "finite S"
    assumes "I {} s"
    assumes "\<And> s. I S s \<Longrightarrow> P s"
    assumes "\<And> T x s. T \<subseteq> S \<Longrightarrow> I T s \<Longrightarrow> x \<in> S \<Longrightarrow> x \<notin> T \<Longrightarrow> f x s \<le> SPEC (I (insert x T))"
    shows "FOREACH S f s \<le> SPEC P"
  proof (rule FOREACH_rule[where I = "\<lambda> T s. I (S - T) s"])
    show "finite S" using assms(1) by this
    show "I (S - S) s" using assms(2) by simp
    show "P s" if "I (S - {}) s" for s using assms(3) that by simp
  next
    fix x T s
    assume 1: "x \<in> T" "T \<subseteq> S" "I (S - T) s"
    have "f x s \<le> SPEC (I (insert x (S - T)))" using assms(4) 1 by blast
    also have "insert x (S - T) = S - (T - {x})" using 1(1, 2) by (simp add: it_step_insert_iff)
    finally show "f x s \<le> SPEC (I (S - (T - {x})))" by this
  qed
  lemma FOREACH_rule_map:
    assumes "finite (dom g)"
    assumes "I empty s"
    assumes "\<And> s. I g s \<Longrightarrow> P s"
    assumes "\<And> h k v s. h \<subseteq>\<^sub>m g \<Longrightarrow> I h s \<Longrightarrow> g k = Some v \<Longrightarrow> k \<notin> dom h \<Longrightarrow>
      f (k, v) s \<le> SPEC (I (h (k \<mapsto> v)))"
    shows "FOREACH (map_to_set g) f s \<le> SPEC P"
  proof (rule FOREACH_rule_insert[where I = "\<lambda> H s. I (set_to_map H) s"])
    show "finite (map_to_set g)" unfolding finite_map_to_set using assms(1) by this
    show "I (set_to_map {}) s" using assms(2) by simp
    show "P s" if "I (set_to_map (map_to_set g)) s" for s
      using assms(3) that unfolding map_to_set_inverse by this
  next
    fix H x s
    assume 1: "H \<subseteq> map_to_set g" "I (set_to_map H) s" "x \<in> map_to_set g" "x \<notin> H"
    obtain k v where 2: "x = (k, v)" by force
    have 3: "inj_on fst H" using inj_on_fst_map_to_set inj_on_subset 1(1) by blast
    have "f x s = f (k, v) s" unfolding 2 by rule
    also have "\<dots> \<le> SPEC (I (set_to_map H (k \<mapsto> v)))"
    proof (rule assms(4))
      show "set_to_map H \<subseteq>\<^sub>m g"
        using 1(1) 3
        by (metis inj_on_fst_map_to_set map_leI map_to_set_inverse set_to_map_simp subset_eq)
      show "I (set_to_map H) s" using 1(2) by this
      show "g k = Some v" using 1(3) unfolding 2 map_to_set_def by simp
      show "k \<notin> dom (set_to_map H)"
        using 1(1, 3, 4) unfolding 2 set_to_map_dom
        by (metis fst_conv inj_on_fst_map_to_set inj_on_image_mem_iff)
    qed
    also have "set_to_map H (k \<mapsto> v) = set_to_map H (fst x \<mapsto> snd x)" unfolding 2 by simp
    also have "\<dots> = set_to_map (insert x H)"
      using 1(1, 3, 4) by (metis inj_on_fst_map_to_set inj_on_image_mem_iff set_to_map_insert)
    finally show "f x s \<le> SPEC (I (set_to_map (insert x H)))" by this
  qed
  lemma FOREACH_rule_insert_eq:
    assumes "finite S"
    assumes "X {} = s"
    assumes "X S = t"
    assumes "\<And> T x. T \<subseteq> S \<Longrightarrow> x \<in> S \<Longrightarrow> x \<notin> T \<Longrightarrow> f x (X T) \<le> SPEC (HOL.eq (X (insert x T)))"
    shows "FOREACH S f s \<le> SPEC (HOL.eq t)"
    by (rule FOREACH_rule_insert[where I = "HOL.eq \<circ> X"]) (use assms in auto)
  lemma FOREACH_rule_map_eq:
    assumes "finite (dom g)"
    assumes "X empty = s"
    assumes "X g = t"
    assumes "\<And> h k v. h \<subseteq>\<^sub>m g \<Longrightarrow> g k = Some v \<Longrightarrow> k \<notin> dom h \<Longrightarrow>
      f (k, v) (X h) \<le> SPEC (HOL.eq (X (h (k \<mapsto> v))))"
    shows "FOREACH (map_to_set g) f s \<le> SPEC (HOL.eq t)"
    by (rule FOREACH_rule_map[where I = "HOL.eq \<circ> X"]) (use assms in auto)

  lemma FOREACH_rule_map_map: "(FOREACH (map_to_set m) (\<lambda> (k, v). F k (f k v)),
    FOREACH (map_to_set (\<lambda> k. map_option (f k) (m k))) (\<lambda> (k, v). F k v)) \<in> Id \<rightarrow> \<langle>Id\<rangle> nres_rel"
  proof refine_vcg
    show "inj_on (\<lambda> (k, v). (k, f k v)) (map_to_set m)"
      unfolding map_to_set_def by rule auto
    show "map_to_set (\<lambda> k. map_option (f k) (m k)) = (\<lambda> (k, v). (k, f k v)) ` map_to_set m"
      unfolding map_to_set_def by auto
  qed auto

  subsection {* Implementations for Sets Represented by Lists *}

  lemma list_set_insert[param]:
    assumes "y \<notin> Y"
    assumes "(x, y) \<in> A" "(xs, Y) \<in> \<langle>A\<rangle> list_set_rel"
    shows "(x # xs, insert y Y) \<in> \<langle>A\<rangle> list_set_rel"
    using assms unfolding list_set_rel_def relcomp_unfold in_br_conv
    by (auto) (metis refine_list(2)[param_fo] distinct.simps(2) list.simps(15))
  lemma list_set_union[param]:
    assumes "X \<inter> Y = {}"
    assumes "(xs, X) \<in> \<langle>A\<rangle> list_set_rel" "(ys, Y) \<in> \<langle>A\<rangle> list_set_rel"
    shows "(xs @ ys, X \<union> Y) \<in> \<langle>A\<rangle> list_set_rel"
    using assms unfolding list_set_rel_def relcomp_unfold in_br_conv
    by (auto) (meson param_append[param_fo] distinct_append set_union_code)
  lemma list_set_Union[param]:
    assumes "\<And> X Y. X \<in> S \<Longrightarrow> Y \<in> S \<Longrightarrow> X \<noteq> Y \<Longrightarrow> X \<inter> Y = {}"
    assumes "(xs, S) \<in> \<langle>\<langle>A\<rangle> list_set_rel\<rangle> list_set_rel"
    shows "(concat xs, Union S) \<in> \<langle>A\<rangle> list_set_rel"
  proof -
    note distinct_map[iff]
    obtain zs where 1: "(xs, zs) \<in> \<langle>\<langle>A\<rangle> list_set_rel\<rangle> list_rel" "S = set zs" "distinct zs"
      using assms(2) unfolding list_set_rel_def relcomp_unfold in_br_conv by auto
    obtain ys where 2: "(xs, ys) \<in> \<langle>\<langle>A\<rangle> list_rel\<rangle> list_rel" "zs = map set ys" "list_all distinct ys"
      using 1(1)
      unfolding list_set_rel_def list_rel_compp
      unfolding relcomp_unfold mem_Collect_eq prod.case
      unfolding br_list_rel in_br_conv
      by auto
    have 20: "set a \<in> S" "set b \<in> S" "set a \<noteq> set b" if "a \<in> set ys" "b \<in> set ys" "a \<noteq> b" for a b
      using 1(3) that unfolding 1(2) 2(2) by (auto dest: inj_onD)
    have 3: "set a \<inter> set b = {}" if "a \<in> set ys" "b \<in> set ys" "a \<noteq> b" for a b
      using assms(1) 20 that by auto
    have 4: "Union S = set (concat ys)" unfolding 1(2) 2(2) by simp
    have 5: "distinct (concat ys)"
      using 1(3) 2(2, 3) 3 unfolding list.pred_set by (blast intro: distinct_concat)
    have 6: "(concat xs, concat ys) \<in> \<langle>A\<rangle> list_rel" using 2(1) by parametricity
    show ?thesis unfolding list_set_rel_def relcomp_unfold in_br_conv using 4 5 6 by blast
  qed
  lemma list_set_image[param]:
    assumes "inj_on g S"
    assumes "(f, g) \<in> A \<rightarrow> B" "(xs, S) \<in> \<langle>A\<rangle> list_set_rel"
    shows "(map f xs, g ` S) \<in> \<langle>B\<rangle> list_set_rel"
    using assms unfolding list_set_rel_def relcomp_unfold in_br_conv
    using param_map[param_fo] distinct_map by fastforce
  lemma list_set_bind[param]:
    assumes "\<And> x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x \<noteq> y \<Longrightarrow> g x \<inter> g y = {}"
    assumes "(xs, S) \<in> \<langle>A\<rangle> list_set_rel" "(f, g) \<in> A \<rightarrow> \<langle>B\<rangle> list_set_rel"
    shows "(xs \<bind> f, S \<bind> g) \<in> \<langle>B\<rangle> list_set_rel"
  proof -
    note [param] = list_set_autoref_filter list_set_autoref_isEmpty
    let ?xs = "filter (Not \<circ> is_Nil \<circ> f) xs"
    let ?S = "op_set_filter (Not \<circ> op_set_isEmpty \<circ> g) S"
    have 1: "inj_on g ?S" using assms(1) by (fastforce intro: inj_onI)
    have "xs \<bind> f = concat (map f ?xs)" by (induct xs) (auto split: list.split)
    also have "(\<dots>, UNION ?S g) \<in> \<langle>B\<rangle> list_set_rel" using assms 1 by parametricity auto
    also have "UNION ?S g = S \<bind> g" by auto auto
    finally show ?thesis by this
  qed

  subsection {* Implementations for Maps Represented by Lists *}

  lemma list_map_build:
    assumes "(g, f) \<in> K \<rightarrow> V"
    assumes "(xs, X) \<in> \<langle>K\<rangle> list_set_rel"
    shows "(zip xs (map g xs), (Some \<circ> f) |` X) \<in> \<langle>K, V\<rangle> list_map_rel"
  proof -
    obtain ys where 1: "(xs, ys) \<in> \<langle>K\<rangle> list_rel" "X = set ys" "distinct ys"
      using assms(2) unfolding list_set_rel_def relcomp_unfold in_br_conv by auto
    show ?thesis
    unfolding list_map_rel_def relcomp_unfold in_br_conv list_map_invar_def
    unfolding mem_Collect_eq prod.case
    proof (intro exI conjI ext)
      show "(zip xs (map g xs), zip ys (map f ys)) \<in> \<langle>K \<times>\<^sub>r V\<rangle> list_rel"
        using assms(1) 1(1) by parametricity
      show "((Some \<circ> f) |` X) k = map_of (zip ys (map f ys)) k" for k
        unfolding map_of_zip_map restrict_map_def 1(2) comp_apply by rule
      show "(distinct \<circ> map fst) (zip ys (map f ys))" using 1(3) by simp
    qed
  qed

  subsection {* Autoref Setup *}

  lemma dflt_ahm_rel_finite_nat: "finite_map_rel (\<langle>nat_rel, V\<rangle> dflt_ahm_rel)" by tagged_solver

  context
  begin

    interpretation autoref_syn by this

    lemma [autoref_op_pat]: "UNION S f \<equiv> OP UNION S f" by simp
    lemma [autoref_op_pat]: "(Some \<circ> f) |` X \<equiv> OP (\<lambda> f X. (Some \<circ> f) |` X) f X" by simp

    lemma list_set_union_autoref[autoref_rules]:
      assumes "PRIO_TAG_OPTIMIZATION"
      assumes "SIDE_PRECOND_OPT (a' \<inter> b' = {})"
      assumes "(a, a') \<in> \<langle>R\<rangle> list_set_rel"
      assumes "(b, b') \<in> \<langle>R\<rangle> list_set_rel"
      shows "(a @ b,
        (OP union ::: \<langle>R\<rangle> list_set_rel \<rightarrow> \<langle>R\<rangle> list_set_rel \<rightarrow> \<langle>R\<rangle> list_set_rel) $ a' $ b') \<in>
        \<langle>R\<rangle> list_set_rel"
      using assms list_set_union unfolding autoref_tag_defs by blast
    lemma list_set_image_autoref[autoref_rules]:
      assumes "PRIO_TAG_OPTIMIZATION"
      assumes INJ: "SIDE_PRECOND_OPT (inj_on f s)"
      assumes "\<And> xi x. (xi, x) \<in> Ra \<Longrightarrow> x \<in> s \<Longrightarrow> (fi xi, f $ x) \<in> Rb"
      assumes LP: "(l,s)\<in>\<langle>Ra\<rangle>list_set_rel"
      shows "(map fi l,
        (OP image ::: (Ra \<rightarrow> Rb) \<rightarrow> \<langle>Ra\<rangle> list_set_rel \<rightarrow> \<langle>Rb\<rangle> list_set_rel) $ f $ s) \<in>
        \<langle>Rb\<rangle> list_set_rel"
    proof -
      from LP obtain l' where 1: "(l,l')\<in>\<langle>Ra\<rangle>list_rel" and L'S: "(l',s)\<in>br set distinct"
        unfolding list_set_rel_def by auto
      have 2: "s = set l'" using L'S unfolding in_br_conv by auto
      have "(map fi l, map f l')\<in>\<langle>Rb\<rangle>list_rel"
        using 1 L'S assms(3) unfolding 2 in_br_conv by induct auto
      also from INJ L'S have "(map f l',f`s)\<in>br set distinct"
        by (induct l' arbitrary: s) (auto simp: br_def dest: injD)
      finally (relcompI) show ?thesis unfolding autoref_tag_defs list_set_rel_def by this
    qed
    lemma list_set_UNION_autoref[autoref_rules]:
      assumes "PRIO_TAG_OPTIMIZATION"
      assumes "SIDE_PRECOND_OPT (\<forall> x \<in> S. \<forall> y \<in> S. x \<noteq> y \<longrightarrow> g x \<inter> g y = {})"
      assumes "(xs, S) \<in> \<langle>A\<rangle> list_set_rel" "(f, g) \<in> A \<rightarrow> \<langle>B\<rangle> list_set_rel"
      shows "(xs \<bind> f,
        (OP UNION ::: \<langle>A\<rangle> list_set_rel \<rightarrow> (A \<rightarrow> \<langle>B\<rangle> list_set_rel) \<rightarrow> \<langle>B\<rangle> list_set_rel) $ S $ g) \<in>
        \<langle>B\<rangle> list_set_rel"
      using assms list_set_bind unfolding bind_UNION autoref_tag_defs by metis

    lemma list_map_build_autoref[autoref_rules]: "(\<lambda> g. map (\<lambda> x. (x, g x)), \<lambda> f X. (Some \<circ> f) |` X) \<in>
      (K \<rightarrow> V) \<rightarrow> \<langle>K\<rangle> list_set_rel \<rightarrow> \<langle>K, V\<rangle> list_map_rel"
      using list_map_build unfolding zip_map2 zip_same_conv_map map_map comp_apply prod.case by blast

  end

end
