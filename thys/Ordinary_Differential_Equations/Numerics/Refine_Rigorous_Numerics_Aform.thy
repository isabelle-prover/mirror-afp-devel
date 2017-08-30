theory Refine_Rigorous_Numerics_Aform
imports
  Refine_Rigorous_Numerics
  Refine_Reachability_Analysis (* TODO: remove this dependency (options) *)
  Collections.Locale_Code
begin

abbreviation "msum_aform' \<equiv> \<lambda>X. msum_aform (degree_aform X) X"

abbreviation "uncurry_options \<equiv> \<lambda>f x. f (precision x) (tolerance x)"

definition
  "split_aform_largest' optns = split_aform_largest (precision optns) (pre_split_summary_tolerance optns)"

text \<open>intersection with plane\<close>

definition inter_aform_plane
  where "inter_aform_plane optns Xs sctn =
    inter_aform_plane_ortho (precision optns) Xs (normal sctn) (pstn sctn)"

definition "reduce_aform optns X = apsnd (summarize_threshold (precision optns) (reduce_summary_tolerance optns) (degree_aform X)) X"

definition aform_inf_inner where "aform_inf_inner optns X n = Inf_aform' (precision optns) (inner_aform X n)"
definition aform_sup_inner where "aform_sup_inner optns X n = Sup_aform' (precision optns) (inner_aform X n)"

definition "support_aform optns b X = (let ia = inner_aform X b in fst X \<bullet> b + tdev' (precision optns) (snd ia))"

definition "width_aform optns X =
  (let t = tdev' (precision optns) (snd X) in sum_list' (precision optns) (map (\<lambda>i. t \<bullet> i) Basis_list))"

definition "inf_aforms optns xs = (Inf_aform' (precision optns) (xs))"
definition "sup_aforms optns xs = (Sup_aform' (precision optns) (xs))"

hide_const (open) floatarith.Max

definition "fresh_index_aforms xs = Max (insert 0 (degree_aform ` set xs))"

definition "independent_aforms x env = (msum_aform (fresh_index_aforms env) (0, zero_pdevs) x#env)"

definition "aform_euclarithform optns ea x = dRETURN (uncurry_options approx_euclarithform optns ea [x])"
definition "aform_slp optns ea xs = dRETURN (uncurry_options approx_slp optns ea xs)"

definition aform_rel_internal: "aform_rel R = br Affine top O \<langle>R\<rangle>set_rel"
lemma aform_rel_def: "\<langle>eucl_rel\<rangle>aform_rel = br Affine top"
  unfolding relAPP_def
  by (auto simp: aform_rel_internal)
definition "aforms_rel = br Joints top"

locale aform_approximate_sets =
  approximate_sets
    "aform_of_ivl::'a::executable_euclidean_space \<Rightarrow> _"
    msum_aform'
    Affine
    Joints
    inf_aforms
    sup_aforms
    split_aform_largest'
    aform_inf_inner
    aform_sup_inner
    "THE_DRES o3 inter_aform_plane"
    reduce_aform
    independent_aforms
    width_aform
    aform_slp
    aform_euclarithform
    aform_rel
    aforms_rel
    optns for optns::"('a::executable_euclidean_space, 'a aform) options"

lemma Affine_eq_permI:
  assumes "fst X = fst Y"
  assumes "map snd (list_of_pdevs (snd X)) <~~> map snd (list_of_pdevs (snd Y))" (is "?perm X Y")
  shows "Affine X = Affine Y"
proof -
  {
    fix X Y and e::"nat \<Rightarrow> real"
    assume perm: "?perm X Y" and e: "e \<in> funcset UNIV {- 1..1}"
    from pdevs_val_of_list_of_pdevs2[OF e, of "snd X"]
    obtain e' where e':
      "pdevs_val e (snd X) = pdevs_val e' (pdevs_of_list (map snd (list_of_pdevs (snd X))))"
      "e' \<in> funcset UNIV {- 1..1}"
      by auto
    note e'(1)
    also from pdevs_val_perm[OF perm e'(2)]
    obtain e'' where e'':
      "e'' \<in> funcset UNIV {- 1..1}"
      "pdevs_val e' (pdevs_of_list (map snd (list_of_pdevs (snd X)))) =
      pdevs_val e'' (pdevs_of_list (map snd (list_of_pdevs (snd Y))))"
      by auto
    note e''(2)
    also from pdevs_val_of_list_of_pdevs[OF e''(1), of "snd Y", simplified]
    obtain e''' where e''':
      "pdevs_val e'' (pdevs_of_list (map snd (list_of_pdevs (snd Y)))) = pdevs_val e''' (snd Y)"
      "e''' \<in> funcset UNIV {- 1..1}"
      by auto
    note e'''(1)
    finally have "\<exists>e' \<in> funcset UNIV {-1 .. 1}. pdevs_val e (snd X) = pdevs_val e' (snd Y)"
      using e'''(2) by auto
  } note E = this
  note e1 = E[OF assms(2)]
    and e2 = E[OF perm_sym[OF assms(2)]]
  show ?thesis
    by (auto simp: Affine_def valuate_def aform_val_def assms dest: e1 e2)
qed

context begin interpretation autoref_syn .

lemma aform_of_ivl_refine: "x \<le> y \<Longrightarrow> (aform_of_ivl x y, atLeastAtMost x y) \<in> \<langle>eucl_rel\<rangle>aform_rel"
  by (auto simp: aform_rel_def br_def Affine_aform_of_ivl)

lemma msum_aform'_refine: "(msum_aform', op +) \<in> \<langle>eucl_rel\<rangle>aform_rel \<rightarrow> \<langle>eucl_rel\<rangle>aform_rel \<rightarrow> \<langle>eucl_rel\<rangle>aform_rel"
  by (force simp: aform_rel_def br_def Affine_msum_aform set_plus_def)

lemma inf_aforms_refine:
  "(RETURN o inf_aforms optns, Inf_spec) \<in> \<langle>eucl_rel\<rangle>aform_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
  by (auto simp: Affine_def valuate_def aform_rel_def br_def inf_aforms_def comps nres_rel_def
      Inf_spec_def Inf_aform Inf_aform'[THEN order.trans])

lemma sup_aforms_refine:
  "(RETURN o sup_aforms optns, Sup_spec) \<in> \<langle>eucl_rel\<rangle>aform_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
  by (auto simp: Affine_def valuate_def aform_rel_def br_def sup_aforms_def comps nres_rel_def
      Sup_spec_def Sup_aform[THEN order.trans] Sup_aform')

lemma nres_of_THE_DRES_le:
  assumes "\<And>v. x = Some v \<Longrightarrow> RETURN v \<le> y"
  shows "nres_of (THE_DRES x) \<le> y"
  using assms by (auto simp: THE_DRES_def split: option.split)

lemma degree_le_fresh_index: "a \<in> set A \<Longrightarrow> degree_aform a \<le> fresh_index_aforms A"
  by (auto simp: fresh_index_aforms_def intro!: Max_ge)

lemma aform_val_zero_pdevs[simp]: "aform_val e (x, zero_pdevs) = x"
  by (auto simp: aform_val_def)

lemma zero_in_JointsI: "xs \<in> Joints XS \<Longrightarrow> z = (0, zero_pdevs) \<Longrightarrow> 0 # xs \<in> Joints (z # XS)"
  by (auto simp: Joints_def valuate_def)

lemma
  split_aform_largest'_refine:
  "((RETURN \<circ>\<circ> split_aform_largest') optns, split_spec) \<in> \<langle>eucl_rel\<rangle>aform_rel \<rightarrow> \<langle>\<langle>eucl_rel\<rangle>aform_rel \<times>\<^sub>r \<langle>eucl_rel\<rangle>aform_rel\<rangle>nres_rel"
proof -
  {
    fix x and X::"'a aform"
    assume "x \<in> Affine X"
    then obtain e where e: "e \<in> funcset UNIV {-1 .. 1}" "x = aform_val e X"
      by (auto simp: Affine_def valuate_def)
    let ?sum = "summarize_threshold (precision optns) (pre_split_summary_tolerance optns) (degree_aform X) (snd X)"
    obtain e' where e': "e' \<in> funcset UNIV {-1 .. 1}"
      "aform_val e' (fst X, ?sum) = aform_val e X"
      by (rule summarize_pdevsE[OF e(1) order_refl, of "snd X" "precision optns"
          "(\<lambda>i y. pre_split_summary_tolerance optns * infnorm (eucl_truncate_up (precision optns) (Radius' (precision optns) X)) \<le> infnorm y)"])
        (auto simp: summarize_threshold_def aform_val_def)
    from e e' have x: "x = aform_val e' (fst X, ?sum)"
      by simp
    have "x \<in> Affine (fst (split_aform_largest' optns X)) \<or>
          x \<in> Affine (snd (split_aform_largest' optns X))"
      apply (rule split_aformE[OF e'(1) x, where i="fst (max_pdev ?sum)"])
      using e'
      by (force simp: split_aform_def split_aform_largest'_def split_aform_largest_def split_aform_largest_uncond_def
        Let_def Affine_def valuate_def
        split: prod.split)+
  } note * = this
  have "\<exists>aa ba. (split_aform_largest' optns (a, b), aa, ba)
                   \<in> {(c, a). a = Affine c} \<times>\<^sub>r {(c, a). a = Affine c} \<and>
                   Affine (a, b) \<subseteq> aa \<union> ba" for a::'a and b
    apply (rule exI[where x = "Affine (fst (split_aform_largest' optns (a, b)))"])
    apply (rule exI[where x = "Affine (snd (split_aform_largest' optns (a, b)))"])
    apply (cases "split_aform_largest' optns (a, b)")
    by (auto dest: *)
  then show ?thesis
    by (auto simp: aform_rel_def br_def nres_rel_def
      split_spec_def
      split: prod.split
      intro!: RETURN_SPEC_refine)
qed

lemma aform_inf_inner_refine:
  "(RETURN o2 aform_inf_inner optns, Inf_inner) \<in> \<langle>eucl_rel\<rangle>aform_rel \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    apply (auto simp: aform_rel_def br_def nres_rel_def comps Affine_def valuate_def Pi_iff
      aform_val_def inner_aform_def algebra_simps
      Inf_inner_def aform_inf_inner_def
      split: prod.split
      intro!: RETURN_SPEC_refine order.trans[OF Inf_aform'_le])
    prefer 3 apply force+
    done

lemma aform_sup_inner_refine:
  "(RETURN o2 aform_sup_inner optns, Sup_inner) \<in> \<langle>eucl_rel\<rangle>aform_rel \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  by (auto simp: aform_rel_def br_def nres_rel_def comps Affine_def valuate_def Pi_iff
    aform_val_def inner_aform_def algebra_simps
    Sup_inner_def aform_sup_inner_def
    split: prod.split
    intro!: RETURN_SPEC_refine order.trans[OF _ Sup_aform'_le])

lemma inter_aform_plane_refine:
  "(nres_of o2 (THE_DRES o3 inter_aform_plane) optns, inter_sctn_spec) \<in> \<langle>eucl_rel\<rangle>aform_rel \<rightarrow> Id \<rightarrow> \<langle>\<langle>eucl_rel\<rangle>aform_rel\<rangle>nres_rel"
  by (auto simp: aform_rel_def br_def nres_rel_def comps
    inter_sctn_spec_def inter_aform_plane_def plane_of_def
    intro!: RETURN_SPEC_refine nres_of_THE_DRES_le
    dest!: inter_inter_aform_plane_ortho)

lemma Affine_reduce_aform: "x \<in> Affine X \<Longrightarrow> x \<in> Affine (reduce_aform optns X)"
proof (auto simp: reduce_aform_def summarize_threshold_def[abs_def] Affine_def valuate_def aform_val_def, goal_cases)
  case (1 e)
  from summarize_pdevsE[OF \<open>e \<in> _\<close> order_refl, of "snd X" "precision optns"
    "(\<lambda>(i::nat) y. reduce_summary_tolerance optns * infnorm (eucl_truncate_up (precision optns)
    (tdev' (precision optns) (snd X))) \<le> infnorm y)"]
  guess e' .
  thus ?case
    by (auto intro!: image_eqI[where x=e'])
qed

lemma reduce_aform_refine:
  "((RETURN \<circ>\<circ> reduce_aform) optns, reduce_spec) \<in> \<langle>eucl_rel\<rangle>aform_rel \<rightarrow> \<langle>\<langle>eucl_rel\<rangle>aform_rel\<rangle>nres_rel"
  by (auto simp: aform_rel_def br_def nres_rel_def
    reduce_spec_def Affine_reduce_aform
    intro!: RETURN_SPEC_refine)

lemma aform_euclarithform_refine:
  "(X, x) \<in> \<langle>eucl_rel\<rangle>aform_rel \<Longrightarrow> (nres_of (aform_euclarithform optns ef X), approx_euclarithform_spec ef x) \<in> \<langle>bool_rel\<rangle>nres_rel"
  by (auto simp: aform_rel_def nres_rel_def br_def comps env_len_def
    aform_euclarithform_def approx_euclarithform_spec_def Joints_imp_length_eq
    intro!: approx_euclarithform fresh_JointsI)

lemma approx_slp_refine_raw:
  shows "nres_of (aform_slp optns e X) \<le> SPEC (\<lambda>R. case R of Some R \<Rightarrow> \<forall>xs\<in>Joints X.
    let r = interpret_slp e xs in env_len (Joints R) (length r) \<and> r \<in> Joints R
    | None \<Rightarrow> True)"
  by (auto simp: Let_def aform_slp_def env_len_def approx_slp intro!: nres_of_THE_DRES_le split: option.split)
    (metis Joints_imp_length_eq approx_slp)

lemma approx_slp_refine:
  "(nres_of o2 aform_slp optns, approx_slp_spec) \<in> Id \<rightarrow> aforms_rel \<rightarrow> \<langle>\<langle>aforms_rel\<rangle>option_rel\<rangle>nres_rel"
  by (fastforce simp: aforms_rel_def nres_rel_def br_def approx_slp_spec_def comps
      intro!: SPEC_refine approx_slp_refine_raw[THEN order_trans]
      split: option.splits)

lemma fresh_index_aforms_Nil[simp]: "fresh_index_aforms [] = 0"
  by (auto simp: fresh_index_aforms_def)

lemma independent_aforms_Nil[simp]:
  "independent_aforms x [] = [x]"
  by (auto simp: independent_aforms_def)

lemma mem_Joints_zero_iff[simp]: "x # xs \<in> Joints ((0, zero_pdevs) # XS) \<longleftrightarrow> (x = 0 \<and> xs \<in> Joints XS)"
  by (auto simp: Joints_def valuate_def)

lemma Joints_independent_aforms_eq: "Joints (independent_aforms x xs) = set_Cons (Affine x) (Joints xs)"
  by (simp add: independent_aforms_def Joints_msum_aform degree_le_fresh_index set_Cons_def)

lemma independent_aforms_refine: "(independent_aforms, set_Cons) \<in> \<langle>eucl_rel\<rangle>aform_rel \<rightarrow> aforms_rel \<rightarrow> aforms_rel"
  by (auto simp: aforms_rel_def br_def aform_rel_def Joints_independent_aforms_eq)

end

definition "aform_of_list_aform x = (fst x, pdevs_of_list (snd x))"

setup Locale_Code.open_block
interpretation aform: aform_approximate_sets
  apply (unfold_locales)
  unfolding autoref_tag_defs
  subgoal unfolding relAPP_def aform_rel_internal[abs_def] .
  subgoal by (force simp: aforms_rel_def)
  subgoal by (force simp: aform_of_ivl_refine)
  subgoal by (rule independent_aforms_refine)
  subgoal by (rule msum_aform'_refine)
  subgoal by (rule inf_aforms_refine)
  subgoal by (rule sup_aforms_refine)
  subgoal by (rule split_aform_largest'_refine)
  subgoal by (rule aform_inf_inner_refine)
  subgoal by (rule aform_sup_inner_refine)
  subgoal by (rule inter_aform_plane_refine)
  subgoal by (rule reduce_aform_refine)
  subgoal by (force simp: width_spec_def nres_rel_def)
  subgoal by (rule approx_slp_refine)
  subgoal by (auto simp: comps intro!: aform_euclarithform_refine)
  subgoal by simp
  subgoal by (rule compact_Affine)
  subgoal by (rule convex_Affine)
  subgoal by (rule Joints_set_zip_subset; assumption)
  by (auto simp: Affine_def Joints_def valuate_def intro!: image_eqI)
setup Locale_Code.close_block

locale aform_approximate_ivp =
  approximate_ivp
    aform_of_ivl
    msum_aform'
    Affine
    Joints
    inf_aforms
    sup_aforms
    split_aform_largest'
    aform_inf_inner
    aform_sup_inner
    "THE_DRES o3 inter_aform_plane"
    reduce_aform
    independent_aforms
    width_aform
    aform_slp
    aform_euclarithform
    aform_rel
    aforms_rel
    optns
    ode
    safe
    ode_euclarith
    safe_euclarithform
    for ode safe ode_euclarith safe_euclarithform
    and optns
begin

definition "one_step_until_time_ivl_listres X0i hist ti =
  do {
    (X, h) \<leftarrow> one_step_until_time_ivl_impl X0i hist ti;
    dRETURN (X, map_option (\<lambda>xs. map (\<lambda>(c, ps). (c, map snd (list_of_pdevs ps))) xs) h)
  }"

lemma one_step_until_time_ivl_listres:
  assumes res: "one_step_until_time_ivl_listres X0i hist ti = dRETURN R"
  assumes "x0 \<in> Affine X0i"
  assumes "ti = t"
  assumes "{fst (fst R) .. snd (fst R)} \<subseteq> S"
  shows "t \<in> existence_ivl0 x0 \<and> flow0 x0 t \<in> S"
proof -
  from res obtain X h where
    1: "one_step_until_time_ivl_impl X0i hist ti = dRETURN (X, h)"
    and 2: "R = (X, map_option (\<lambda>xs. map (\<lambda>(c, ps). (c, map snd (list_of_pdevs ps))) xs) h)"
    by (auto simp: one_step_until_time_ivl_listres_def elim!: dbind.elims)
  show ?thesis
    apply (rule one_step_until_time_ivl_res[OF 1])
    using assms(2-)
    by (auto simp: 2)
qed

lemma one_step_until_time_ivl_listres_reachable:
  assumes res: "one_step_until_time_ivl_listres X0i hist ti = dRETURN R"
  assumes noNone: "snd R \<noteq> None"
  assumes "x0 \<in> Affine X0i"
  assumes "ti = t"
  assumes "{fst (fst R) .. snd (fst R)} \<subseteq> S"
  assumes REACH: "\<Union>(Affine ` set (map aform_of_list_aform (the (snd R)))) \<subseteq> REACH"
  shows "t \<in> existence_ivl0 x0 \<and> flow0 x0 t \<in> S \<and> (\<forall>s \<in> {0 .. t}. flow0 x0 s \<in> REACH)"
proof -
  from res noNone obtain X h where
    1: "one_step_until_time_ivl_impl X0i hist ti = dRETURN (X, Some h)"
    and 2: "R = (X, Some (map (\<lambda>(c, ps). (c, map snd (list_of_pdevs ps))) h))"
    by (auto simp: one_step_until_time_ivl_listres_def elim!: dbind.elims)
  have "t \<in> existence_ivl0 x0 \<and> flow0 x0 t \<in> S \<and> (\<forall>s\<in>{0..t}. flow0 x0 s \<in> UNION (set h) Affine)"
    apply (rule one_step_until_time_ivl_reachable_res[OF 1 assms(3-4), of S])
    using 2 assms
    by auto
  moreover have "UNION (set h) Affine \<subseteq> \<Union>(Affine ` set (map aform_of_list_aform (the (snd R))))"
    unfolding 2 snd_conv option.sel split_beta' set_map image_image
    by (rule UN_mono)
      (force simp: Affine_def valuate_def aform_val_def aform_of_list_aform_def
        split_beta'
        elim: pdevs_val_of_list_of_pdevs2
      intro!: UN_mono)+
  ultimately show ?thesis using assms by (force)
qed

definition "poincare_irects_listres X0i CX0i =
  do {
    (X, h) \<leftarrow> poincare_irects_impl X0i CX0i;
    dRETURN (X, map_option (\<lambda>xs. map (\<lambda>(c, ps). (c, map snd (list_of_pdevs ps))) xs) h)
  }"


lemma poincare_irects_listres:
  assumes "poincare_irects_listres ISi CXSi = dRETURN R"
  assumes "set_of_coll Affine ISi \<subseteq> Collect (le_halfspace (start_section optns))"
  assumes "set_of_coll Affine ISi \<subseteq> Collect safe"
  assumes safe: "set_of_coll Affine CXSi \<subseteq> Collect safe"
  shows "flowsto
    (set_of_coll Affine ISi)
    (set_of_coll (\<lambda>(x, xs). Affine (x, pdevs_of_list xs)) (snd R))
    (set_of_plane_coll (set_of_irect (irect_mod optns)) (fst R))"
proof -
  from assms obtain X h where
    "poincare_irects_impl ISi CXSi = dRETURN (X, h)"
    "R = (X, map_option (\<lambda>xs. map (\<lambda>(c, ps). (c, map snd (list_of_pdevs ps))) xs) h)"
    by (auto simp: poincare_irects_listres_def elim!: dbind.elims)
  from poincare_irects_impl_thm[OF this(1) assms(2,3,4)]
  have "flowsto (set_of_coll Affine ISi) (set_of_coll Affine h)
    (set_of_plane_coll (set_of_irect(irect_mod optns)) X)"
    by simp
  moreover have "(set_of_coll Affine h) \<subseteq>
    (set_of_coll (\<lambda>(x, xs). Affine (x, pdevs_of_list xs)) (snd R))"
    by (simp add: split_beta' set_of_coll_def \<open>R = _\<close> split: option.split)
      (force simp: Affine_def valuate_def aform_val_def aform_of_list_aform_def
        elim: pdevs_val_of_list_of_pdevs2
        intro!: UN_mono)+
  moreover
  {
    fix c X xs and e::"nat \<Rightarrow> real"
    assume cX: "(c, X) \<in> set xs"
      and e: "e \<in> funcset UNIV {- 1..1}"
      and safe: "(\<Union>x\<in>set xs. (\<lambda>e. fst x + pdevs_val e (snd x)) ` funcset UNIV {- 1..1}) \<subseteq> Collect safe"
    from pdevs_val_of_list_of_pdevs[OF \<open>e \<in> _\<close>, of X]
    obtain e' where "pdevs_val e (pdevs_of_list (map snd (list_of_pdevs X))) = pdevs_val e' X"
      "e' \<in> funcset UNIV {-1 .. 1}"
      by auto
    note this(1)
    also
    have "c + pdevs_val e' X \<in> (\<Union>x\<in>set xs. (\<lambda>e. fst x + pdevs_val e (snd x)) ` funcset UNIV {- 1..1})"
      using cX
      apply (rule UN_I)
      using _ \<open>e' \<in> _\<close>
      by (rule image_eqI) simp
    also note \<open>\<dots> \<subseteq> Collect safe\<close>
    finally have "safe (c + pdevs_val e (pdevs_of_list (map snd (list_of_pdevs X))))"
      by auto
  }
  ultimately show ?thesis
    apply -
    by (rule flowsto_subset, assumption)
      (auto simp: \<open>R = _\<close> dest!: flowsto_safeD
        simp: set_of_coll_def split_beta' Affine_def valuate_def aform_val_def
        split: option.splits
        elim: pdevs_val_of_list_of_pdevs2)
qed

end


definition "ivls_of_aforms p ress = map (\<lambda>(t0, CX, t1, X).
    (t0, eucl_truncate_down p (Inf_aform CX), eucl_truncate_up p (Sup_aform CX), t1,
      eucl_truncate_down p (Inf_aform X), eucl_truncate_up p (Sup_aform X))) ress"

primrec summarize_ivls where
  "summarize_ivls [] = None"
| "summarize_ivls (x#xs) = (case summarize_ivls xs of
      None \<Rightarrow> Some x
    | Some (t0', cl', cu', t1', xl', xu') \<Rightarrow>
      case x of (t0, cl, cu, t1, xl, xu) \<Rightarrow>
      if t0 = t1' then
        Some (min t0 t0', inf cl cl', sup cu cu', max t1 t1',
          if t1 \<le> t1' then xl' else xl, if t1 \<le> t1' then xu' else xu)
      else None)"

fun "set_res_of_ivl_res"
where "set_res_of_ivl_res (t0, CXl, CXu, t1 ,Xl, Xu) = (t0, {CXl .. CXu}, t1, {Xl .. Xu})"

fun parts::"nat\<Rightarrow>'a list\<Rightarrow>'a list list"
where
  "parts n [] = []"
| "parts 0 xs = [xs]"
| "parts n xs = take n xs # parts n (drop n xs)"

definition summarize_enclosure
where "summarize_enclosure p m xs =
  map the (filter (-Option.is_none) (map summarize_ivls (parts m (ivls_of_aforms p xs))))"

definition "ivls_result p m = (apsnd (summarize_enclosure p m o snd)) o snd"

definition "default_optns =
    \<lparr>
    precision = 53,
    tolerance = FloatR 1 (- 8),
    stepsize  = FloatR 1 (- 8),
    iterations = 40,
    halve_stepsizes = 10,
    widening_mod = 40,
    rk2_param = FloatR 1 0,
    max_tdev_thres = FloatR 1 100,
    pre_split_summary_tolerance = FloatR 1 0,
    reduce_summary_tolerance = FloatR 1 0,
    collect_granularity = FloatR 1 100,
    start_section = Sctn 0 0,
    checkpoint_sections = [Sctn 0 0],
    stop_sections = [Sctn 0 0],
    snap_sections = 1,
    min_section_distance = 1/2,
    next_section_distance_factor = 50,
    next_section_turn_distance_factor = 0,
    printing_fun = (\<lambda>_ _. ()),
    tracing_fun = (\<lambda>_ _. ()),
    irect_mod = 8,
    max_intersection_step = FloatR 1 (- 8),
    reduce_number_factor = 2,
    adaptive_atol = FloatR 1 (-12),
    adaptive_rtol = FloatR 1 (-12),
    adaptive_gtol = FloatR 1 (-12),
    method_id = 2
  \<rparr>"

end