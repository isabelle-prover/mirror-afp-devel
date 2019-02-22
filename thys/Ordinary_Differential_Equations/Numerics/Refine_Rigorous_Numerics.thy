theory Refine_Rigorous_Numerics
imports
  "HOL-Library.Parallel"
  Transfer_Euclidean_Space_Vector
  "../Refinement/Enclosure_Operations"
  "../Refinement/Refine_Vector_List"
  "../Refinement/Refine_Hyperplane"
  "../Refinement/Refine_Interval"
  "../Refinement/Refine_Invar"
  "../Refinement/Refine_Unions"
  "../Refinement/Refine_Info"
begin

section \<open>misc\<close>

lemma length_listset: "xi \<in> listset xs \<Longrightarrow> length xi = length xs"
  by (induction xs arbitrary: xi) (auto simp: set_Cons_def)

lemma Nil_mem_listset[simp]: "[] \<in> listset list \<longleftrightarrow> list = []"
  by (induction list) (auto simp: set_Cons_def)

lemma sing_mem_listset_iff[simp]: "[b] \<in> listset ys \<longleftrightarrow> (\<exists>z. ys = [z] \<and> b \<in> z)"
  \<comment> \<open>TODO: generalize to Cons?\<close>
  by (cases ys) (auto simp: set_Cons_def)


no_notation (in autoref_syn) funcset (infixr "\<rightarrow>" 60)

definition cfuncset where "cfuncset l u X = funcset {l .. u} X \<inter> Collect (continuous_on {l .. u})"
lemma cfuncset_iff: "f \<in> cfuncset l u X \<longleftrightarrow> (\<forall>i\<in>{l .. u}. f i \<in> X) \<and> continuous_on {l .. u} f"
  unfolding cfuncset_def by auto

lemma cfuncset_continuous_onD: "f \<in> cfuncset 0 h X \<Longrightarrow> continuous_on {0..h} f"
  by (simp add: cfuncset_iff)


section \<open>Implementations\<close>

subsection \<open>locale for sets\<close>

definition "product_listset xs ys = (\<lambda>(x, y). x @ y) ` ((xs::real list set) \<times> (ys::real list set))"

abbreviation "rl_rel \<equiv> \<langle>rnv_rel\<rangle>list_rel"

abbreviation "slp_rel \<equiv> \<langle>Id::floatarith rel\<rangle>list_rel"
abbreviation "fas_rel \<equiv> \<langle>Id::floatarith rel\<rangle>list_rel"

locale approximate_sets = autoref_syn +
  fixes appr_of_ivl::"real list \<Rightarrow> real list \<Rightarrow> 'b list"
  fixes product_appr::"'b list \<Rightarrow> 'b list \<Rightarrow> 'b list"
  fixes msum_appr::"'b list \<Rightarrow> 'b list \<Rightarrow> 'b list"
  fixes set_of_appr::"'b list \<Rightarrow> real list set"
  fixes inf_of_appr::"'options \<Rightarrow> 'b list \<Rightarrow> real list"
  fixes sup_of_appr::"'options \<Rightarrow> 'b list \<Rightarrow> real list"
  fixes split_appr::"'options \<Rightarrow> nat \<Rightarrow> 'b list \<Rightarrow> 'b list \<times> 'b list"
  fixes appr_inf_inner::"'options \<Rightarrow> 'b list \<Rightarrow> real list \<Rightarrow> real"
  fixes appr_sup_inner::"'options \<Rightarrow> 'b list \<Rightarrow> real list \<Rightarrow> real"
  fixes inter_appr_plane::"'options \<Rightarrow> 'b list \<Rightarrow> real list sctn \<Rightarrow> 'b list dres"
  fixes reduce_appr::"'options \<Rightarrow> ('b list \<Rightarrow> nat \<Rightarrow> real list \<Rightarrow> bool) \<Rightarrow> 'b list \<Rightarrow> 'b list"
  fixes width_appr::"'options \<Rightarrow> 'b list \<Rightarrow> real"
  fixes approx_slp::"'options \<Rightarrow> nat \<Rightarrow> slp \<Rightarrow> 'b list \<Rightarrow> 'b list option dres"
  fixes approx_euclarithform::"'options \<Rightarrow> form \<Rightarrow> 'b list \<Rightarrow> bool dres"
  fixes approx_isFDERIV::"'options \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> floatarith list \<Rightarrow> 'b list \<Rightarrow>
    bool dres"
  fixes appr_rell
  fixes optns::"'options"
  assumes appr_rell_internal: "appr_rell \<equiv> br set_of_appr top"
  assumes transfer_operations_rl:
    "SIDE_PRECOND (list_all2 (\<le>) xrs yrs) \<Longrightarrow>
      (xri, xrs) \<in> \<langle>rnv_rel\<rangle>list_rel \<Longrightarrow>
      (yri, yrs) \<in> \<langle>rnv_rel\<rangle>list_rel \<Longrightarrow>
      (appr_of_ivl xri yri, lv_ivl $ xrs $ yrs) \<in> appr_rell"
    "(product_appr, product_listset) \<in> appr_rell \<rightarrow> appr_rell \<rightarrow> appr_rell"
    "(msum_appr, (\<lambda>xs ys. {map2 (+) x y |x y. x \<in> xs \<and> y \<in> ys})) \<in> appr_rell \<rightarrow> appr_rell \<rightarrow> appr_rell"
    "(xi, x) \<in> appr_rell \<Longrightarrow> length xi = d \<Longrightarrow>
      (RETURN (inf_of_appr optns xi), Inf_specs d x) \<in> \<langle>rl_rel\<rangle>nres_rel"
    "(xi, x) \<in> appr_rell \<Longrightarrow> length xi = d \<Longrightarrow>
      (RETURN (sup_of_appr optns xi), Sup_specs d x) \<in> \<langle>rl_rel\<rangle>nres_rel"
    "(ni, n) \<in> nat_rel \<Longrightarrow> (xi, x) \<in> appr_rell \<Longrightarrow> length xi = d \<Longrightarrow>
      (RETURN (split_appr optns ni xi), split_spec_params d n x) \<in> \<langle>appr_rell \<times>\<^sub>r appr_rell\<rangle>nres_rel"
    "(RETURN o2 appr_inf_inner optns, Inf_inners) \<in> appr_rell \<rightarrow> rl_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
    "(RETURN o2 appr_sup_inner optns, Sup_inners) \<in> appr_rell \<rightarrow> rl_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
    "(xi, x) \<in> appr_rell \<Longrightarrow> length xi = d \<Longrightarrow> length (normal si) = d \<Longrightarrow> d > 0 \<Longrightarrow> (si, s) \<in> \<langle>rl_rel\<rangle>sctn_rel \<Longrightarrow>
      (nres_of (inter_appr_plane optns xi si), inter_sctn_specs d x s) \<in> \<langle>appr_rell\<rangle>nres_rel"
    "(Ci, C) \<in> \<langle>Id\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> rl_rel \<rightarrow> bool_rel \<Longrightarrow> (xi, x) \<in> appr_rell \<Longrightarrow> length xi = d \<Longrightarrow>
      (RETURN (reduce_appr optns Ci xi), reduce_specs d C x) \<in> \<langle>appr_rell\<rangle>nres_rel"
    "(RETURN o width_appr optns, width_spec) \<in> appr_rell \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
    "(nres_of o3 approx_slp optns, approx_slp_spec fas) \<in> nat_rel \<rightarrow> slp_rel \<rightarrow> appr_rell \<rightarrow> \<langle>\<langle>appr_rell\<rangle>option_rel\<rangle>nres_rel"
assumes approx_euclarithform[unfolded comps, autoref_rules]:
  "(nres_of o2 approx_euclarithform optns, approx_form_spec) \<in> Id \<rightarrow> appr_rell \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
assumes approx_isFDERIV[unfolded comps, autoref_rules]:
  "(\<lambda>N xs fas vs. nres_of (approx_isFDERIV optns N xs fas vs), isFDERIV_spec) \<in>
  nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow>  appr_rell \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
assumes set_of_appr_nonempty[simp]: "set_of_appr X \<noteq> {}"
assumes length_set_of_appr: "xrs \<in> set_of_appr xs \<Longrightarrow> length xrs = length xs"
assumes set_of_appr_project: "xrs \<in> set_of_appr xs \<Longrightarrow> (\<And>i. i \<in> set is \<Longrightarrow> i < length xs) \<Longrightarrow>
    map ((!) xrs) is \<in> set_of_appr (map ((!) xs) is)"
assumes set_of_apprs_ex_Cons: "xrs \<in> set_of_appr xs \<Longrightarrow> \<exists>r. r#xrs \<in> set_of_appr (b#xs)"
assumes set_of_apprs_Nil[simp]: "xrs \<in> set_of_appr [] \<longleftrightarrow> xrs = []"
begin

definition "appr_rel = appr_rell O \<langle>lv_rel\<rangle>set_rel"
lemmas [autoref_rel_intf] = REL_INTFI[of appr_rel i_appr]

lemma prod_rel_relcomp_distr: "(R \<times>\<^sub>r S) O (T \<times>\<^sub>r U) = (R O T) \<times>\<^sub>r (S O U)"
  by (auto simp: prod_rel_def)

lemma appr_relp_comp: "appr_rell O \<langle>lv_rel\<rangle>set_rel \<subseteq> appr_rel"
  "appr_rel \<subseteq> appr_rell O \<langle>lv_rel\<rangle>set_rel"
  by (auto simp: appr_rel_def)

lemma rnv_rel_comp2:
  "rnv_rel \<subseteq> rnv_rel O rnv_rel"
  "rnv_rel O rnv_rel \<subseteq> rnv_rel"
  by auto

lemma rl_comp_lv: "rl_rel O lv_rel \<subseteq> lv_rel"
  "lv_rel \<subseteq> rl_rel O lv_rel"
  by auto

lemmas rel_lemmas =
  fun_rel_comp_dist[THEN order_trans]
  fun_rel_mono nres_rel_comp[THEN eq_refl, THEN order_trans]
  nres_rel_mono prod_rel_mono prod_rel_relcomp_distr[THEN eq_refl, THEN order_trans]
  appr_relp_comp
  rnv_rel_comp2
  rl_comp_lv
  sctn_rel

lemma width_spec_width_spec: "(width_spec, width_spec) \<in> \<langle>lv_rel\<rangle>set_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  by (auto simp: width_spec_def nres_relI)

lemma [autoref_itype]:
  "width_spec ::\<^sub>i A \<rightarrow>\<^sub>i \<langle>i_rnv\<rangle>\<^sub>ii_nres"
  "Inf_spec ::\<^sub>i A \<rightarrow>\<^sub>i \<langle>B\<rangle>\<^sub>ii_nres"
  "Sup_spec ::\<^sub>i A \<rightarrow>\<^sub>i \<langle>B\<rangle>\<^sub>ii_nres"
  "inter_sctn_spec ::\<^sub>i A \<rightarrow>\<^sub>i \<langle>B\<rangle>\<^sub>ii_sctn \<rightarrow>\<^sub>i \<langle>C\<rangle>\<^sub>ii_nres"
  "split_spec ::\<^sub>i A \<rightarrow>\<^sub>i \<langle>\<langle>B, B\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_nres"
  "split_spec_param ::\<^sub>i i_nat \<rightarrow>\<^sub>i A \<rightarrow>\<^sub>i \<langle>\<langle>B, B\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_nres"
  "Inf_inner ::\<^sub>i A \<rightarrow>\<^sub>i B \<rightarrow>\<^sub>i \<langle>i_rnv\<rangle>\<^sub>ii_nres"
  "Sup_inner ::\<^sub>i A \<rightarrow>\<^sub>i B \<rightarrow>\<^sub>i \<langle>i_rnv\<rangle>\<^sub>ii_nres"
  by auto

lemma transfer_operations[unfolded comps, autoref_rules]:
  "SIDE_PRECOND (list_all2 (\<le>) xrs yrs) \<Longrightarrow>
    (xri, xrs) \<in> \<langle>rnv_rel\<rangle>list_rel \<Longrightarrow>
    (yri, yrs) \<in> \<langle>rnv_rel\<rangle>list_rel \<Longrightarrow>
    (appr_of_ivl xri yri, lv_ivl $ xrs $ yrs) \<in> appr_rell"
  "(product_appr, product_listset) \<in> appr_rell \<rightarrow> appr_rell \<rightarrow> appr_rell"
  "(msum_appr, (+)) \<in> appr_rel \<rightarrow> appr_rel \<rightarrow> appr_rel"
  "(RETURN o inf_of_appr optns, Inf_spec) \<in> appr_rel \<rightarrow> \<langle>lv_rel\<rangle>nres_rel"
  "(RETURN o sup_of_appr optns, Sup_spec) \<in> appr_rel \<rightarrow> \<langle>lv_rel\<rangle>nres_rel"
  "(RETURN o2 split_appr optns, split_spec_param) \<in> nat_rel \<rightarrow> appr_rel \<rightarrow> \<langle>appr_rel \<times>\<^sub>r appr_rel\<rangle>nres_rel"
  "(RETURN o2 appr_inf_inner optns, Inf_inner) \<in> appr_rel \<rightarrow> lv_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  "(RETURN o2 appr_sup_inner optns, Sup_inner) \<in> appr_rel \<rightarrow> lv_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  "(nres_of o2 inter_appr_plane optns, inter_sctn_spec) \<in> appr_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>appr_rel\<rangle>nres_rel"
  "(RETURN o2 reduce_appr optns, reduce_spec) \<in> (\<langle>Id\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> rl_rel \<rightarrow> bool_rel) \<rightarrow> appr_rel \<rightarrow> \<langle>appr_rel\<rangle>nres_rel"
  "(RETURN o width_appr optns, width_spec) \<in> appr_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  "(nres_of o3 approx_slp optns, approx_slp_spec fas) \<in> nat_rel \<rightarrow> slp_rel \<rightarrow> appr_rell \<rightarrow> \<langle>\<langle>appr_rell\<rangle>option_rel\<rangle>nres_rel"
  subgoal premises prems using transfer_operations_rl(1)[OF prems] by simp
  subgoal premises prems using transfer_operations_rl(2)[OF prems] by simp
  subgoal premises prems using transfer_operations_rl(3)[OF prems]
    unfolding appr_rel_def set_plus_def
    apply auto
    apply (drule fun_relD, assumption, drule fun_relD, assumption, rule relcompI, assumption)
    apply (auto simp: set_rel_sv[OF lv_rel_sv])
      apply (rule ImageI)
       apply (rule lv_rel_add[param_fo], assumption, assumption)
      apply force
    subgoal for a b c d e f g
      apply (rule bexI[where x="eucl_of_list f"])
       apply (rule bexI[where x="eucl_of_list g"])
      using lv_rel_add[param_fo, of f "eucl_of_list f", of g "eucl_of_list g::'a"]
      by (auto simp: lv_rel_def br_def subset_iff)
    subgoal
      by (auto simp: lv_rel_def br_def subset_iff)
    done
  subgoal apply (auto simp: appr_rel_def)
  proof goal_cases
    case (1 x y z)
    from transfer_operations_rl(4)[OF 1(1) refl]
    have Is: "(RETURN (inf_of_appr optns x), Inf_specs (length x) y) \<in> \<langle>rl_rel\<rangle>nres_rel"
      by auto
    from 1 have "length x = DIM('c)"
      unfolding set_rel_sv[OF lv_rel_sv]
      by (auto simp: lv_rel_def br_def appr_rell_internal length_set_of_appr subset_iff)
    from relcompI[OF _ Inf_specs_Inf_spec[param_fo], OF Is \<open>length x = _\<close> 1(2)]
    have "(RETURN (inf_of_appr optns x), Inf_spec z) \<in> \<langle>rl_rel\<rangle>nres_rel O \<langle>lv_rel\<rangle>nres_rel"
      by simp
    then show ?case
      by (simp add: nres_rel_comp)
  qed
  subgoal apply (auto simp: appr_rel_def)
  proof goal_cases
    case (1 x y z)
    from transfer_operations_rl(5)[OF 1(1) refl]
    have Is: "(RETURN (sup_of_appr optns x), Sup_specs (length x) y) \<in> \<langle>rl_rel\<rangle>nres_rel"
      by auto
    from 1 have "length x = DIM('d)"
      unfolding set_rel_sv[OF lv_rel_sv]
      by (auto simp: lv_rel_def br_def appr_rell_internal length_set_of_appr subset_iff)
    from relcompI[OF _ Sup_specs_Sup_spec[param_fo], OF Is \<open>length x = _\<close> 1(2)]
    have "(RETURN (sup_of_appr optns x), Sup_spec z) \<in> \<langle>rl_rel\<rangle>nres_rel O \<langle>lv_rel\<rangle>nres_rel"
      by simp
    then show ?case
      by (simp add: nres_rel_comp)
  qed
  subgoal apply (auto simp: appr_rel_def)
  proof goal_cases
    case (1 n x y z)
    from transfer_operations_rl(6)[OF _ 1(1) refl]
    have Is: "(RETURN (split_appr optns n x), split_spec_params (length x) n y) \<in> \<langle>appr_rell \<times>\<^sub>r appr_rell\<rangle>nres_rel"
      by auto
    from 1 have "length x = DIM('e)"
      unfolding set_rel_sv[OF lv_rel_sv]
      by (auto simp: lv_rel_def br_def appr_rell_internal length_set_of_appr subset_iff)
    from relcompI[OF _ split_spec_params_split_spec_param[param_fo], OF Is \<open>length x = _\<close> IdI 1(2)]
    have "(RETURN (split_appr optns n x), split_spec_param n z) \<in>
        \<langle>appr_rell \<times>\<^sub>r appr_rell\<rangle>nres_rel O \<langle>\<langle>lv_rel\<rangle>set_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>set_rel\<rangle>nres_rel"
      by simp
    then show ?case
      by (simp add: nres_rel_comp prod_rel_relcomp_distr comps)
  qed
  subgoal
    by (intro relcompI[OF transfer_operations_rl(7) Inf_inners_Inf_inner, THEN rev_subsetD] rel_lemmas)
  subgoal
    by (intro relcompI[OF transfer_operations_rl(8) Sup_inners_Sup_inner, THEN rev_subsetD] rel_lemmas)
  subgoal apply (auto simp: appr_rel_def)
  proof goal_cases
    case (1 r s x y z)
    from 1 have lens: "length (normal r) = length x"
      apply (cases r; cases s)
      apply (auto simp: sctn_rel_def)
      unfolding set_rel_sv[OF lv_rel_sv]
      by (auto simp: lv_rel_def br_def appr_rell_internal length_set_of_appr subset_iff)
    have poslen: "0 < length x"
      using 1
      apply (cases r; cases s)
      apply (auto simp: sctn_rel_def)
      by (auto simp: lv_rel_def set_rel_def br_def appr_rell_internal)
    have rr: "(r, r) \<in> \<langle>rl_rel\<rangle>sctn_rel"
      by (cases r) (auto simp: sctn_rel_def)
    from transfer_operations_rl(9)[OF 1(2) refl lens poslen rr]
    have Is: "(nres_of (inter_appr_plane optns x r), inter_sctn_specs (length x) y r) \<in> \<langle>appr_rell\<rangle>nres_rel"
      by (auto dest!: fun_relD)
    from 1 have "length x = DIM('h)"
      unfolding set_rel_sv[OF lv_rel_sv]
      by (auto simp: lv_rel_def br_def appr_rell_internal length_set_of_appr subset_iff)
    from relcompI[OF _ inter_sctn_specs_inter_sctn_spec[param_fo], OF Is, OF \<open>length x = _\<close> 1(3) 1(1)]
    have "(nres_of (inter_appr_plane optns x r), inter_sctn_spec z s) \<in> \<langle>appr_rell\<rangle>nres_rel O \<langle>\<langle>lv_rel\<rangle>set_rel\<rangle>nres_rel"
      by simp
    then show ?case
      by (simp add: nres_rel_comp prod_rel_relcomp_distr comps)
  qed
  subgoal apply (auto simp: appr_rel_def)
  proof goal_cases
    case (1 r x y z)
    from transfer_operations_rl(10)[OF _ 1(1) refl]
    have Is: "(RETURN (reduce_appr optns r x), reduce_specs (length x) r y) \<in> \<langle>appr_rell\<rangle>nres_rel"
      by auto
    from 1 have "length x = DIM('i)"
      unfolding set_rel_sv[OF lv_rel_sv]
      by (auto simp: lv_rel_def br_def appr_rell_internal length_set_of_appr subset_iff)
    from relcompI[OF _ reduce_specs_reduce_spec[param_fo], OF Is \<open>length x = _\<close> IdI 1(2)]
    have "(RETURN (reduce_appr optns r x), reduce_spec r z) \<in> \<langle>appr_rell\<rangle>nres_rel O \<langle>\<langle>lv_rel\<rangle>set_rel\<rangle>nres_rel"
      by simp
    then show ?case
      by (simp add: nres_rel_comp prod_rel_relcomp_distr comps)
  qed
  subgoal
    by (intro relcompI[OF transfer_operations_rl(11) width_spec_width_spec, THEN rev_subsetD] rel_lemmas)
  subgoal using transfer_operations_rl(12) by auto
  done

lemma approx_slp_spec[autoref_op_pat_def]: "approx_slp_spec fas \<equiv> OP (approx_slp_spec fas)"
  by auto

primrec concat_appr where
  "concat_appr [] = []"
| "concat_appr (x#xs) = product_appr x (concat_appr xs)"

definition [simp]: "op_concat_listset xs = concat ` listset xs"

lemma [autoref_op_pat_def]: "concat ` listset xs \<equiv> OP op_concat_listset $ xs"
  by simp

lemma
  concat_appr:
  assumes "(xsi, xs) \<in> \<langle>appr_rell\<rangle>list_rel"
  shows "(concat_appr xsi, concat ` listset xs) \<in> appr_rell"
  using assms
  apply (auto simp: appr_rell_internal br_def)
  subgoal premises prems for xi
  proof -
    have "length xi = length xs" "length xs = length xsi"
      using prems
       by (auto simp: list_rel_def list_all2_iff length_listset)
    then show ?thesis using prems
    proof (induction rule: list_induct3)
      case Nil
      then show ?case by simp
    next
      case (Cons x xs y ys z zs)
      have "(z, set_of_appr z) \<in> appr_rell"
        "(concat_appr zs, set_of_appr (concat_appr zs)) \<in> appr_rell"
        by (auto simp: appr_rell_internal br_def)
      from transfer_operations(2)[param_fo, OF this]
      have *: "set_of_appr (product_appr z (concat_appr zs)) =
        (\<lambda>(x, y). x @ y) ` (set_of_appr z \<times> set_of_appr (concat_appr zs))"
        by (simp add: appr_rell_internal br_def product_listset_def)
      show ?case
        using Cons
        apply (auto simp: appr_rell_internal *)
        apply (rule image_eqI[where x="(x, concat xs)"])
         by (auto simp: set_Cons_def)
     qed
   qed
   subgoal premises prems for z
   proof -
     have "length xsi = length xs"
       using prems
       by (auto simp: list_rel_def list_all2_iff)
     then show ?thesis
       using prems
     proof (induction arbitrary: z rule: list_induct2 )
       case Nil
       then show ?case by simp
     next
       case (Cons x xs y ys)
       have "(x, set_of_appr x) \<in> appr_rell" "(concat_appr xs, set_of_appr (concat_appr xs)) \<in> appr_rell"
         by (auto simp: appr_rell_internal br_def)
       from transfer_operations(2)[param_fo, OF this]
       have *: "set_of_appr (product_appr x (concat_appr xs)) =
          product_listset (set_of_appr x) (set_of_appr (concat_appr xs))"
         by (auto simp: appr_rell_internal br_def)
       show ?case using Cons
         apply (auto simp: * product_listset_def list_rel_def set_Cons_def)
         subgoal premises prems for a b
           using prems(2)[OF prems(7)] prems(6)
           apply (auto )
           subgoal for ya
           apply (rule image_eqI[where x="a#ya"])
             by (auto simp: set_Cons_def)
           done
         done
     qed
   qed
   done

lemma op_concat_listset_autoref[autoref_rules]:
  "(concat_appr, op_concat_listset) \<in> \<langle>appr_rell\<rangle>list_rel \<rightarrow> appr_rell"
  using concat_appr by force

lemma appr_rel_br: "appr_rel = br (\<lambda>xs. eucl_of_list ` (set_of_appr xs)::'a set) (\<lambda>xs. length xs = DIM('a::executable_euclidean_space))"
  unfolding appr_rel_def lv_rel_def set_rel_br
  unfolding appr_rell_internal br_chain o_def
  using length_set_of_appr
  by (auto dest!: brD intro: brI)

lemma list_all2_replicate [simp]: "list_all2 (\<le>) xs xs" for xs::"'a::order list"
  by (auto simp: list_all2_iff in_set_zip)

lemma lv_ivl_self[simp]: "lv_ivl xs xs = {xs}" for xs::"'a::order list"
  by (force simp: lv_ivl_def list_all2_conv_all_nth
      intro!: nth_equalityI)

lemma set_of_appr_of_ivl_point'[simp]:
  "set_of_appr (appr_of_ivl (replicate E 0) (replicate E 0)) = {replicate E (0::real)}"
  using transfer_operations(1)[of "(replicate E (0::real))" "(replicate E (0::real))" "(replicate E (0::real))" "(replicate E 0)"]
  by (auto simp: appr_rell_internal br_def)

lemma set_of_appr_of_ivl_point:
  "set_of_appr (appr_of_ivl xs xs) = {xs}"
  using transfer_operations(1)[of xs xs xs xs]
  by (auto simp: appr_rell_internal br_def)


lemma
  take_set_of_apprI:
  assumes "xs \<in> set_of_appr XS" "tXS = take d XS" "d < length xs"
  shows "take d xs \<in> set_of_appr tXS"
  using set_of_appr_project[OF assms(1), of "[0..<d]"]
  apply (auto simp: assms take_eq_map_nth length_set_of_appr)
  using assms(1) assms(3) length_set_of_appr take_eq_map_nth by fastforce

lemma length_appr_of_ivl[simp]:
  "length (appr_of_ivl xs ys) = length xs"
  if "list_all2 (\<le>) xs ys"
  using transfer_operations(1)[of xs ys xs ys] that
    apply (simp add: appr_rell_internal br_def lv_ivl_def)
  apply (auto simp: appr_rell_internal br_def list_all2_lengthD dest!: length_set_of_appr)
  using length_set_of_appr by fastforce

lemma length_appr_of_ivl_point[simp]:
  "length (appr_of_ivl xs xs) = length xs"
  by (simp add: list_all2_refl)

definition [simp]: "op_atLeastAtMost_appr = atLeastAtMost"
lemma [autoref_op_pat]: "atLeastAtMost \<equiv> OP op_atLeastAtMost_appr"
  by simp

lemma transfer_operations1[autoref_rules]:
  assumes "SIDE_PRECOND (x \<le> y)" "(xi, x) \<in> lv_rel" "(yi, y) \<in> lv_rel"
  shows "(appr_of_ivl xi yi, op_atLeastAtMost_appr $ x $ y) \<in> appr_rel"
proof -
  have "(appr_of_ivl xi yi, lv_ivl (list_of_eucl x) (list_of_eucl y)) \<in> appr_rell"
    apply (rule transfer_operations[unfolded autoref_tag_defs])
    using assms lv_rel_le[param_fo, of xi x yi y]
    by (auto simp: lv_rel_def br_def)
  then have "(appr_of_ivl xi yi, eucl_of_list ` lv_ivl (list_of_eucl x) (list_of_eucl y)::'a set) \<in> appr_rel"
    unfolding appr_rel_br
    using assms[unfolded lv_rel_def]
    using lv_rel_le[param_fo, of xi x yi y]
    by (auto simp: appr_rell_internal br_def appr_rel_br)
       (auto simp: lv_rel_def br_def)
  also have "eucl_of_list ` lv_ivl (list_of_eucl x) (list_of_eucl y) = {x .. y}"
    by (subst eucl_of_list_image_lv_ivl) auto
  finally show ?thesis by simp
qed

lemma appr_of_ivl_point_appr_rel:
  "(appr_of_ivl x x, {eucl_of_list x::'a::executable_euclidean_space}) \<in> appr_rel"
  if "length x = DIM('a)"
  using transfer_operations1[OF _ lv_relI lv_relI, OF _ that that]
  by auto

lemmas [autoref_post_simps] = concat.simps append_Nil2 append.simps

lemma is_empty_appr_rel[autoref_rules]:
  "(\<lambda>_. False, is_empty) \<in> appr_rel \<rightarrow> bool_rel"
  by (auto simp: appr_rel_br br_def)

definition card_info::"_ set \<Rightarrow> nat nres" where [refine_vcg_def]: "card_info x = SPEC top" \<comment> \<open>\<open>op_set_wcard\<close>\<close>
sublocale autoref_op_pat_def card_info .

lemma card_info[autoref_rules]:
  "((\<lambda>x. RETURN (length x)), card_info) \<in> clw_rel R \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"
  by (auto simp: card_info_def nres_rel_def)

lemma appr_rel_nonempty: "(x, X) \<in> appr_rel \<Longrightarrow> X \<noteq> {}"
  by (auto simp: appr_rel_br br_def)

lemma [autoref_rules]: "(optns, optns) \<in> Id"
  by simp

lemma single_valued_appr_rel[relator_props]:
  "single_valued (appr_rel)"
  by (auto simp: appr_rel_br)

lemma nth_append_cond:
  "i < length xs \<Longrightarrow> (xs @ ys) ! i = xs ! i"
  "i \<ge> length xs \<Longrightarrow> (xs @ ys) ! i = ys ! (i - length xs)"
  by (auto simp: nth_append)

lemma ivl_rep_of_set_nres:
  fixes X::"'a::executable_euclidean_space set"
  shows "do { let X = ((X ::: A):::appr_rel); i \<leftarrow> Inf_spec X; s \<leftarrow> Sup_spec X; RETURN (inf i s, s)} \<le> ivl_rep_of_set X"
  unfolding ivl_rep_of_set_def Inf_spec_def Sup_spec_def
  by (refine_vcg) (auto simp: inf.coboundedI1)

schematic_goal ivl_rep_of_set_impl:
  fixes X::"'a::executable_euclidean_space set"
  assumes [autoref_rules]: "(ai, X) \<in> appr_rel"
  shows "(RETURN (?f::?'r), ivl_rep_of_set X) \<in> ?R"
  by (rule ivl_rep_of_set_nres[THEN nres_rel_trans2]) (autoref_monadic (plain))
concrete_definition ivl_rep_of_set_impl for  ai uses ivl_rep_of_set_impl
lemma ivl_rep_of_set_autoref[autoref_rules]:
  shows "(\<lambda>x. RETURN (ivl_rep_of_set_impl x), ivl_rep_of_set) \<in> appr_rel \<rightarrow> \<langle>lv_rel \<times>\<^sub>r lv_rel\<rangle>nres_rel"
  using ivl_rep_of_set_impl.refine
  by auto

lemma ivl_rep_of_sets_nres:
  "FORWEAK XS (RETURN (0, 0)) ivl_rep_of_set (\<lambda>(i, s) (i', s'). RETURN (inf i i':::lv_rel, sup s s':::lv_rel)) \<le> ivl_rep_of_sets XS"
  apply (cases "XS = {}")
  subgoal by (simp add: ivl_rep_of_sets_def)
  subgoal premises ne
  proof -
    have "FORWEAK XS (RETURN (0, 0)) ivl_rep_of_set (\<lambda>(i, s) (i', s'). RETURN (inf i i', sup s s')) \<le> SPEC (\<lambda>(i, s). (\<forall>X\<in>XS. X \<subseteq> {i..s} \<and> i \<le> s))"
      by (auto simp: subset_iff le_infI1 le_infI2 le_supI1 le_supI2 ivl_rep_of_set_def split_beta' intro!: FORWEAK_elementwise_rule)
    also have "\<dots> \<le> ivl_rep_of_sets XS"
      using ne by (auto simp add: ivl_rep_of_sets_def)
    finally show ?thesis by (simp add: ne)
  qed
  done

schematic_goal ivl_rep_of_sets_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) n"
  assumes [autoref_rules]: "(ai, a) \<in> \<langle>appr_rel\<rangle>list_wset_rel"
  notes [refine_transfer] = FORWEAK_LIST_plain.refine
  shows "(RETURN (?f), ivl_rep_of_sets a::('a \<times> 'a)nres) \<in> \<langle>lv_rel \<times>\<^sub>r lv_rel\<rangle>nres_rel"
  by (rule nres_rel_trans2[OF ivl_rep_of_sets_nres]) (autoref_monadic(plain))
concrete_definition ivl_rep_of_sets_impl for n ai uses ivl_rep_of_sets_impl
lemma ivl_rep_of_sets_impl_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) n \<Longrightarrow>
  (\<lambda>ai. RETURN (ivl_rep_of_sets_impl n ai), ivl_rep_of_sets::_\<Rightarrow>('a \<times> 'a)nres) \<in> \<langle>appr_rel\<rangle>list_wset_rel \<rightarrow> \<langle>lv_rel \<times>\<^sub>r lv_rel\<rangle>nres_rel"
  using ivl_rep_of_sets_impl.refine by force

definition [simp]: "set_of_coll X = X"

definition [simp]: "ivl_rep_of_set_coll = ivl_rep_of_set"

lemma ivl_rep_of_set_coll:
  "do { Xs \<leftarrow> sets_of_coll (X:::clw_rel appr_rel); ivl_rep_of_sets Xs} \<le> ivl_rep_of_set_coll X"
  unfolding ivl_rep_of_set_def ivl_rep_of_set_coll_def
  by refine_vcg auto

schematic_goal ivl_rep_of_set_coll_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) n"
  assumes [autoref_rules]: "(ai, a) \<in> clw_rel appr_rel"
  shows "(RETURN (?f), ivl_rep_of_set_coll a::('a\<times>'a) nres) \<in> \<langle>lv_rel \<times>\<^sub>r lv_rel\<rangle>nres_rel"
  by (rule nres_rel_trans2[OF ivl_rep_of_set_coll]) (autoref_monadic (plain))
concrete_definition ivl_rep_of_set_coll_impl for n ai uses ivl_rep_of_set_coll_impl
lemma ivl_rep_of_set_coll_impl_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) n \<Longrightarrow>
  (\<lambda>ai. RETURN (ivl_rep_of_set_coll_impl n ai), ivl_rep_of_set_coll::_\<Rightarrow>('a\<times>'a) nres) \<in> clw_rel appr_rel \<rightarrow> \<langle>lv_rel \<times>\<^sub>r lv_rel\<rangle>nres_rel"
  using ivl_rep_of_set_coll_impl.refine by force

definition [refine_vcg_def]: "ivls_of_sets X = SPEC (\<lambda>R. X \<subseteq> R)"

lemma ivls_of_set_FORWEAK:
  "do {
    XS \<leftarrow> (sets_of_coll (X:::clw_rel appr_rel) ::: \<langle>\<langle>appr_rel\<rangle>list_wset_rel\<rangle>nres_rel);
    FORWEAK XS (RETURN (op_empty_coll:::clw_rel lvivl_rel))
      (\<lambda>X. do {
        (i, s) \<leftarrow> ivl_rep_of_set X;
        RETURN (mk_coll (op_atLeastAtMost_ivl i s:::\<langle>lv_rel\<rangle>ivl_rel))
      })
      (\<lambda>a b. RETURN (a \<union> b))
  } \<le> ivls_of_sets X"
  unfolding ivls_of_sets_def autoref_tag_defs
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>XS U. \<Union>XS \<subseteq> U"]) auto

schematic_goal ivls_of_sets_impl:
  assumes [autoref_rules]: "(xsi, xs) \<in> clw_rel appr_rel"
  shows "(nres_of (?f), ivls_of_sets $ xs) \<in> \<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  by (rule ivls_of_set_FORWEAK[THEN nres_rel_trans2]) autoref_monadic
concrete_definition ivls_of_sets_impl for xsi uses ivls_of_sets_impl
lemma ivls_of_set_impl_refine[autoref_rules]:
  "(\<lambda>ai. nres_of (ivls_of_sets_impl ai), ivls_of_sets) \<in> clw_rel appr_rel \<rightarrow> \<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  using ivls_of_sets_impl.refine by force

definition [simp]: "ivl_to_set X = X"

lemma ivl_to_set[autoref_rules]:
  assumes le[THEN GEN_OP_D, param_fo]: "GEN_OP le (\<le>) ((lv_rel::(_ \<times> 'a::executable_euclidean_space)set) \<rightarrow> lv_rel \<rightarrow> bool_rel)"
  shows "(\<lambda>(i, s). if le i s then [appr_of_ivl i s] else [], ivl_to_set::_\<Rightarrow>'a set) \<in> lvivl_rel \<rightarrow> clw_rel (appr_rel)"
  apply (clarsimp simp add: ivl_rel_def)
  subgoal premises prems for ls us l u X
    using le[OF \<open>(_, l) \<in> _\<close> \<open>(_, u) \<in> _\<close>] prems transfer_operations1[of l u ls us]
    apply (auto simp: Cons_mem_clw_rel_iff single_valued_appr_rel ivl_rel_def[symmetric] intro!: exI[where x=X])
    subgoal by (auto simp: set_of_ivl_def br_def)
    subgoal using Union_rel_empty by (auto simp: set_of_ivl_def br_def )
    done
  done

definition [simp]: "sets_of_ivls X = X"
lemma sets_of_ivls[autoref_rules]:
  assumes le[THEN GEN_OP_D, param_fo]: "GEN_OP le (\<le>) ((lv_rel::(_ \<times> 'a::executable_euclidean_space)set) \<rightarrow> lv_rel \<rightarrow> bool_rel)"
  shows "(\<lambda>xs. map (\<lambda>(i, s). appr_of_ivl i s) [(i,s) \<leftarrow> xs. le i s], sets_of_ivls::_\<Rightarrow>'a set) \<in> clw_rel lvivl_rel \<rightarrow> clw_rel (appr_rel)"
  apply (rule fun_relI)
  unfolding appr_rel_br ivl_rel_br clw_rel_br lvivl_rel_br
  apply (auto simp: br_def set_of_ivl_def)
  subgoal for a b c d
    apply (rule exI conjI le le[THEN IdD, THEN iffD2] lv_relI| assumption | force)+
    using transfer_operations1[where 'a='a, of "eucl_of_list c" "eucl_of_list d" c d]
    apply (auto simp: appr_rel_br br_def lvivl_rel_br set_of_ivl_def lv_rel_def)
    by (metis (mono_tags, lifting) atLeastAtMost_iff atLeastatMost_empty_iff case_prodD empty_iff)
  subgoal for a b c d
    using transfer_operations1[where 'a='a, of "eucl_of_list b" "eucl_of_list c" b c]
      le[of b _ c _, OF lv_relI lv_relI]
    by (auto simp: appr_rel_br br_def lvivl_rel_br set_of_ivl_def lv_rel_def intro!: bexI)
  subgoal for a b c
    using transfer_operations1[where 'a='a, of "eucl_of_list b" "eucl_of_list c" b c]
      le[of b _ c _, OF lv_relI lv_relI]
    by (auto simp: appr_rel_br br_def lvivl_rel_br set_of_ivl_def lv_rel_def intro!: bexI)
  done

schematic_goal above_sctn_impl:
  assumes [autoref_rules]: "(Xi, X) \<in> appr_rel" "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(?f::?'r, above_sctn $ X $ sctn) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule above_sctn_nres[THEN nres_rel_trans2]) autoref_monadic
concrete_definition above_sctn_impl for Xi sctni uses above_sctn_impl
lemma above_sctn_impl_refine[autoref_rules]:
  "(\<lambda>ai sctni. RETURN (above_sctn_impl ai sctni), above_sctn) \<in> appr_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using above_sctn_impl.refine by force

schematic_goal below_sctn_impl:
  assumes [autoref_rules]: "(ai, a) \<in> appr_rel"
  assumes [autoref_rules]: "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(?f::?'r, below_sctn $ a $ sctn) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule below_sctn_nres[THEN nres_rel_trans2]) (autoref_monadic (plain))
concrete_definition below_sctn_impl for ai sctni uses below_sctn_impl
lemma below_sctn_impl_refine[autoref_rules]:
  "(\<lambda>ai sctni. RETURN (below_sctn_impl ai sctni), below_sctn) \<in> appr_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using below_sctn_impl.refine by force

schematic_goal sbelow_sctn_impl:
  assumes [autoref_rules]: "(ai, a) \<in> appr_rel"
  assumes [autoref_rules]: "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(?f::?'r, sbelow_sctn $ a $ sctn) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule sbelow_sctn_nres[THEN nres_rel_trans2]) (autoref_monadic (plain))
concrete_definition sbelow_sctn_impl for ai sctni uses sbelow_sctn_impl
lemma sbelow_sctn_impl_refine[autoref_rules]:
  "(\<lambda>ai sctni. RETURN (sbelow_sctn_impl ai sctni), sbelow_sctn) \<in>
    appr_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using sbelow_sctn_impl.refine by force

schematic_goal sbelow_sctns_impl:
  assumes [autoref_rules]: "(ai, a) \<in> appr_rel"
  assumes [autoref_rules]: "(sctnsi, sctns) \<in> sctns_rel"
  shows "(?f::?'r, sbelow_sctns $ a $ sctns) \<in> ?R"
  unfolding autoref_tag_defs
  apply (rule sbelow_sctns_nres[THEN nres_rel_trans2])
  subgoal using list_set_rel_finiteD[of sctnsi sctns "\<langle>lv_rel\<rangle>sctn_rel"] \<open>(sctnsi, sctns) \<in> _\<close> by (simp add: relAPP_def)
  by (autoref_monadic (plain))
concrete_definition sbelow_sctns_impl for ai sctnsi uses sbelow_sctns_impl
lemma sbelow_sctns_impl_refine[autoref_rules]:
  "(\<lambda>ai sctni. RETURN (sbelow_sctns_impl ai sctni), sbelow_sctns) \<in>
    appr_rel \<rightarrow> sctns_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using sbelow_sctns_impl.refine by force

lemma intersects_nres:
  shows "(do {
    ii \<leftarrow> Inf_inner X (normal sctn);
    si \<leftarrow> Sup_inner X (normal sctn);
    RETURN (ii \<le> pstn sctn \<and> si \<ge> pstn sctn)
  }) \<le> intersects_spec X sctn"
  unfolding intersects_spec_def Inf_inner_def Sup_inner_def
  by refine_vcg (force simp: plane_of_def)

schematic_goal intersects_impl:
  assumes [autoref_rules]: "(ai, a) \<in> appr_rel"
  assumes [autoref_rules]: "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(?f::?'r, intersects_spec $ a $ sctn) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule intersects_nres[THEN nres_rel_trans2])
    (autoref_monadic (plain))
concrete_definition intersects_impl for ai sctni uses intersects_impl
lemma intersects_impl_refine[autoref_rules]:
  "(\<lambda>ai sctni. RETURN (intersects_impl ai sctni), intersects_spec) \<in> appr_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using intersects_impl.refine by force

definition [simp]: "sbelow_sctns_coll = sbelow_sctns"
lemma sbelow_sctns_coll_refine:
  "do {
    XS \<leftarrow> (sets_of_coll XS ::: \<langle>\<langle>appr_rel\<rangle>list_wset_rel\<rangle>nres_rel);
    FORWEAK XS (RETURN True) (\<lambda>X. sbelow_sctns X sctns) (\<lambda>a b. RETURN (a \<and> b))
  } \<le> sbelow_sctns_coll XS sctns"
  unfolding sbelow_sctns_def autoref_tag_defs sbelow_sctns_coll_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>X b. b \<longrightarrow> (\<Union>X \<subseteq> sbelow_halfspaces sctns)"]) auto
schematic_goal sbelow_sctns_coll_impl:
  assumes [autoref_rules]: "(ai, a) \<in> clw_rel appr_rel"
  assumes [autoref_rules]: "(sctnsi, sctns) \<in> sctns_rel"
  shows "(?f::?'r, sbelow_sctns_coll $ a $ sctns) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule sbelow_sctns_coll_refine[THEN nres_rel_trans2]) autoref
concrete_definition sbelow_sctns_coll_impl for ai sctnsi uses sbelow_sctns_coll_impl
lemma sbelow_sctns_coll_impl_refine[autoref_rules]:
  "(sbelow_sctns_coll_impl, sbelow_sctns_coll) \<in> clw_rel appr_rel \<rightarrow> sctns_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using sbelow_sctns_coll_impl.refine by force

schematic_goal sbelow_sctns_coll_dres:
  "nres_of ?r \<le> sbelow_sctns_coll_impl a sctns"
  unfolding sbelow_sctns_coll_impl_def
  by refine_transfer
concrete_definition sbelow_sctns_coll_dres for a sctns uses sbelow_sctns_coll_dres
lemmas [refine_transfer] = sbelow_sctns_coll_dres.refine

definition [simp]: "below_sctn_coll = below_sctn"
lemma below_sctn_coll_refine:
  "do {
    XS \<leftarrow> (sets_of_coll XS ::: \<langle>\<langle>appr_rel\<rangle>list_wset_rel\<rangle>nres_rel);
    FORWEAK XS (RETURN True) (\<lambda>X. below_sctn X sctn) (\<lambda>a b. RETURN (a \<and> b))
  } \<le> below_sctn_coll XS sctn"
  unfolding below_sctn_def autoref_tag_defs below_sctn_coll_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>X b. b \<longrightarrow> (\<Union>X \<subseteq> below_halfspace sctn)"]) auto
schematic_goal below_sctn_coll_impl:
  assumes [autoref_rules]: "(ai, a) \<in> clw_rel appr_rel"
  assumes [autoref_rules]: "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(?f::?'r, below_sctn_coll $ a $ sctn) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule below_sctn_coll_refine[THEN nres_rel_trans2]) autoref
concrete_definition below_sctn_coll_impl for ai sctni uses below_sctn_coll_impl
lemma below_sctn_coll_impl_refine[autoref_rules]:
  "(below_sctn_coll_impl, below_sctn_coll) \<in> clw_rel appr_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using below_sctn_coll_impl.refine by force
schematic_goal below_sctn_coll_dres:
  "nres_of ?r \<le> below_sctn_coll_impl a sctn"
  unfolding below_sctn_coll_impl_def
  by refine_transfer
concrete_definition below_sctn_coll_dres for a sctn uses below_sctn_coll_dres
lemmas [refine_transfer] = below_sctn_coll_dres.refine

definition [simp]: "intersects_clw = intersects_spec"

lemma intersects_clw:
  shows "(do {
    XS \<leftarrow> sets_of_coll (X:::clw_rel appr_rel);
    FORWEAK XS (RETURN False) (\<lambda>X. intersects_spec X sctn) (\<lambda>a b. RETURN (a \<or> b))
  }) \<le> intersects_clw X sctn"
  unfolding intersects_spec_def intersects_clw_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>XS b. b \<or> \<Union>XS \<inter> plane_of sctn = {}"]) auto

schematic_goal intersects_clw_impl:
  assumes [autoref_rules]: "(ai, a) \<in> clw_rel appr_rel"
  assumes [autoref_rules]: "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(?f::?'r, intersects_clw $ a $ sctn) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule intersects_clw[THEN nres_rel_trans2]) (autoref_monadic (plain))
concrete_definition intersects_clw_impl for ai sctni uses intersects_clw_impl
lemma intersects_clw_impl_refine[autoref_rules]:
  "(\<lambda>ai sctni. RETURN (intersects_clw_impl ai sctni), intersects_clw) \<in> clw_rel appr_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using intersects_clw_impl.refine by force

lemma subset_spec_ivl_impl:
  shows
  "do {
      (i', s') \<leftarrow> ((ivl_rep ((ivl))));
      (i, s) \<leftarrow> (ivl_rep_of_set ((X::'a::executable_euclidean_space set)));
      RETURN (((i' \<le> i):::bool_rel) \<and> ((s \<le> s'):::bool_rel))
    } \<le> subset_spec X ivl"
    unfolding subset_spec_def autoref_tag_defs
    by (refine_vcg) force
schematic_goal subset_spec_ivlc:
  assumes [autoref_rules]: "(Xi, X::'a::executable_euclidean_space set) \<in> appr_rel"
      "(ivli, ivl) \<in> \<langle>lv_rel\<rangle>ivl_rel"
  notes [autoref_post_simps] = Let_def
  shows "(RETURN (?f), subset_spec $ X $ ivl) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  by (rule subset_spec_ivl_impl[THEN nres_rel_trans2]) autoref_monadic
concrete_definition subset_spec_ivlc for Xi ivli uses subset_spec_ivlc

lemma subset_spec_ivl_refine[autoref_rules]:
  "(\<lambda>Xi Yi. RETURN (subset_spec_ivlc Xi Yi), subset_spec) \<in> appr_rel \<rightarrow> \<langle>lv_rel\<rangle>ivl_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  for A::"(_ \<times> 'a::executable_euclidean_space set) set"
  using subset_spec_ivlc.refine
  by auto

definition [simp]: "subset_spec_coll = subset_spec"

lemma subset_spec_ivl_coll_impl:
  "do {
    XS \<leftarrow> (sets_of_coll X:::\<langle>\<langle>appr_rel\<rangle>list_wset_rel\<rangle>nres_rel);
    FORWEAK XS (RETURN True)
      (\<lambda>X. subset_spec X ivl)
      (\<lambda>x y. RETURN (x \<and> y))
  } \<le> subset_spec_coll X ivl"
  unfolding autoref_tag_defs subset_spec_def subset_spec_coll_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>x b. b \<longrightarrow> \<Union>x \<subseteq> ivl"])
     (auto simp: subset_iff set_of_ivl_def)
schematic_goal subset_spec_ivl_collc:
  assumes [autoref_rules]: "(Xi, X::'a::executable_euclidean_space set) \<in> clw_rel appr_rel"
    "(ivli, ivl) \<in> \<langle>lv_rel\<rangle>ivl_rel"
  notes [autoref_post_simps] = Let_def
  shows "(RETURN (?f), subset_spec_coll $ X $ ivl) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  by (rule subset_spec_ivl_coll_impl[THEN nres_rel_trans2]) (autoref_monadic (plain))
concrete_definition subset_spec_ivl_collc for Xi ivli uses subset_spec_ivl_collc
lemma subset_spec_ivl_collc_refine[autoref_rules]:
  "(\<lambda>Xi Yi. RETURN (subset_spec_ivl_collc Xi Yi), subset_spec_coll) \<in> clw_rel appr_rel \<rightarrow> \<langle>lv_rel\<rangle>ivl_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using subset_spec_ivl_collc.refine by force

lemma project_set_appr_le:
  "inter_sctn_spec X (Sctn b y) \<le> project_set X b y"
  unfolding project_set_def
  by (refine_vcg) (force simp: plane_of_def)+

schematic_goal project_set_appr:
  fixes b::"'a::executable_euclidean_space" and y
  assumes [autoref_rules]: "(Xi, X) \<in> appr_rel"
  assumes [autoref_rules]: "(bi, b) \<in> lv_rel"
  assumes [autoref_rules]: "(yi, y) \<in> rnv_rel"
  shows "(nres_of (?f::?'r dres), project_set X b y) \<in> ?R"
  by (rule nres_rel_trans2[OF project_set_appr_le]) autoref_monadic
concrete_definition project_set_appr for Xi bi yi uses project_set_appr
lemma project_set_appr_refine[autoref_rules]:
  "(\<lambda>Xi bi yi. nres_of (project_set_appr Xi bi yi), project_set) \<in> appr_rel \<rightarrow> lv_rel \<rightarrow> rnv_rel \<rightarrow> \<langle>appr_rel\<rangle>nres_rel"
  using project_set_appr.refine by force

definition "subset_spec_ivls X Y = do {
    Ys \<leftarrow> sets_of_coll Y; FORWEAK Ys (RETURN False) (\<lambda>Y. subset_spec X Y) (\<lambda>a b. RETURN (a \<or> b))
  }"
sublocale autoref_op_pat_def subset_spec_ivls .

schematic_goal subset_spec_ivls_impl:
  assumes [autoref_rules]: "(Xi, X) \<in> appr_rel" "(Yi, Y) \<in> clw_rel lvivl_rel"
  shows "(RETURN ?f, subset_spec_ivls X Y) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding subset_spec_ivls_def
  by (autoref_monadic (plain))
concrete_definition subset_spec_ivls_impl for Xi Yi uses subset_spec_ivls_impl
lemmas [autoref_rules] = subset_spec_ivls_impl.refine[autoref_higher_order_rule]

lemma subset_spec_ivls[THEN order_trans, refine_vcg]:
  "subset_spec_ivls X Y \<le> subset_spec X Y"
  unfolding subset_spec_ivls_def subset_spec_def
  by (refine_vcg FORWEAK_mono_rule'[where I="\<lambda>Ys b. b \<longrightarrow> X - \<Union>Ys \<subseteq> Y"]) auto

definition "subset_spec_ivls_clw M X Y = do {
    X \<leftarrow> split_along_ivls M X Y;
    X \<leftarrow> sets_of_coll (sets_of_ivls X);
    FORWEAK X (RETURN True) (\<lambda>X. subset_spec_ivls X Y) (\<lambda>a b. RETURN (a \<and> b))
  }"
sublocale autoref_op_pat_def subset_spec_ivls_clw .

schematic_goal subset_spec_ivls_clw_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(Xi, X::'a set) \<in> clw_rel lvivl_rel" "(Yi, Y) \<in> clw_rel lvivl_rel"
    "(Mi, M) \<in> nat_rel"
  shows "(nres_of ?f, subset_spec_ivls_clw M X Y) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding subset_spec_ivls_clw_def
  including art
  by (autoref_monadic)
concrete_definition subset_spec_ivls_clw_impl for Mi Xi Yi uses subset_spec_ivls_clw_impl
lemma [autoref_rules]:
"DIM_precond TYPE('a::executable_euclidean_space) D \<Longrightarrow>
  (\<lambda>Mi Xi Yi. nres_of (subset_spec_ivls_clw_impl D Mi Xi Yi),
   subset_spec_ivls_clw::nat \<Rightarrow> 'a set \<Rightarrow> _)
  \<in> nat_rel \<rightarrow> clw_rel (\<langle>lv_rel\<rangle>ivl_rel) \<rightarrow> clw_rel (\<langle>lv_rel\<rangle>ivl_rel) \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using subset_spec_ivls_clw_impl.refine by force

definition [simp]: "REMDUPS x = x"
sublocale autoref_op_pat_def REMDUPS .
lemma REMDUPS_impl[autoref_rules]: "(remdups, REMDUPS) \<in> clw_rel A \<rightarrow> clw_rel A"
  if "PREFER single_valued A"
  using that
  by (force simp: clw_rel_br dest!: brD intro!: brI elim!: single_valued_as_brE)

definition "split_along_ivls2 M X Y = do {
    Xs \<leftarrow> sets_of_coll X;
    Rs \<leftarrow>FORWEAK Xs (RETURN op_empty_coll) (\<lambda>X. do {
      (I, N) \<leftarrow> split_intersecting Y (mk_coll X);
      split_along_ivls M (mk_coll X) I
    }) (\<lambda>x y. RETURN (y \<union> x));
    RETURN (REMDUPS Rs)
  }"
sublocale autoref_op_pat_def split_along_ivls2 .

lemma split_along_ivls2[THEN order_trans, refine_vcg]:"split_along_ivls2 M X IS \<le> SPEC (\<lambda>R. R = X)"
  unfolding split_along_ivls2_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>x xi. \<Union>x \<subseteq> xi \<and> xi \<subseteq> X"]) auto

schematic_goal split_along_ivls2_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(Xi, X::'a set) \<in> clw_rel lvivl_rel" "(ISi, IS) \<in> clw_rel lvivl_rel"
      "(Mi, M) \<in> nat_rel"
  shows "(nres_of ?f, split_along_ivls2 $ M $ X $ IS) \<in> \<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding split_along_ivls2_def
  by autoref_monadic
concrete_definition split_along_ivls2_impl uses split_along_ivls2_impl
lemmas [autoref_rules] = split_along_ivls2_impl.refine

definition [simp]: "op_list_of_eucl_image X = list_of_eucl ` X"
lemma [autoref_op_pat_def]: "list_of_eucl ` X \<equiv> OP op_list_of_eucl_image $ X" by simp

lemma op_list_of_eucl_image_autoref[autoref_rules]:
  shows "(\<lambda>xs. xs, op_list_of_eucl_image) \<in> appr_rel \<rightarrow> appr_rell"
  by (auto simp: length_set_of_appr appr_rel_def lv_rel_def image_image set_rel_br
      cong: image_cong
      dest!: brD)

definition [simp]: "op_eucl_of_list_image X = (eucl_of_list ` X::'a::executable_euclidean_space set)"
lemma [autoref_op_pat_def]: "eucl_of_list ` X \<equiv> OP op_eucl_of_list_image $ X" by simp

lemma op_eucl_of_list_image_autoref[autoref_rules]:
  assumes "(xsi, xs) \<in> appr_rell"
  assumes "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes "SIDE_PRECOND (env_len xs D)"
  shows "(xsi, op_eucl_of_list_image $ (xs)::'a set) \<in> appr_rel"
  using assms
  unfolding appr_rel_br
  by (auto simp: length_set_of_appr appr_rel_br br_def image_image env_len_def appr_rell_internal)

definition [simp]: "op_take_image n X = take n ` X"
lemma [autoref_op_pat_def]: "take n ` X \<equiv> OP op_take_image $ n $ X" by simp

lemma take_set_of_apprD: "xs \<in> set_of_appr XS \<Longrightarrow> take n xs \<in> set_of_appr (take n XS)"
  apply (cases "n < length xs")
   apply (subst take_eq_map_nth)
    apply simp
   apply (subst take_eq_map_nth)
    apply (simp add: length_set_of_appr)
   apply (rule set_of_appr_project)
  by (auto simp: length_set_of_appr)

lemma set_of_appr_ex_append1:
  "xrs \<in> set_of_appr xs \<Longrightarrow> \<exists>r. r @ xrs \<in> set_of_appr (b @ xs)"
proof (induction b)
  case Nil
  then show ?case by (auto intro!: exI[where x=Nil])
next
  case (Cons a b)
  then show ?case
    apply (auto)
    subgoal for r
      apply (drule set_of_apprs_ex_Cons[where b=a and xs="b@xs"])
      apply auto
      by (metis Cons_eq_appendI)
    done
qed

lemma set_of_appr_ex_append2:
  assumes "xrs \<in> set_of_appr xs" shows "\<exists>r. xrs @ r \<in> set_of_appr (xs @ b)"
proof -
  from set_of_appr_ex_append1[OF assms, of b]
  obtain r where r: "r @ xrs \<in> set_of_appr (b @ xs)" by auto
  have "map ((!) (r @ xrs)) ([length b..<length b + length xs] @ [0..<length b])
    \<in> set_of_appr (map ((!) (b @ xs)) ([length b..<length b + length xs] @ [0..<length b]))"
    by (rule set_of_appr_project[OF r, of "[length b..<length b + length xs] @ [0..<length b]"])
      auto
  also have "map ((!) (b @ xs)) ([length b..<length b + length xs] @ [0..<length b]) = xs @ b"
    by (auto intro!: nth_equalityI simp: nth_append)
  also have "map ((!) (r @ xrs)) ([length b..<length b + length xs] @ [0..<length b]) = xrs @ r"
    using length_set_of_appr[OF r] assms length_set_of_appr
    by (auto intro!: nth_equalityI simp: nth_append)
  finally show ?thesis by rule
qed

lemma drop_all_conc: "drop (length a) (a@b) = b"
  by (simp)

lemma set_of_appr_takeD: "xs \<in> set_of_appr (take n XS) \<Longrightarrow> xs \<in> take n ` set_of_appr XS"
  apply (frule set_of_appr_ex_append2[where b="map ((!) XS) [n..<length XS]"])
  apply (auto simp: take_append_take_minus_idem)
  apply (rule image_eqI)
   prefer 2 apply assumption
  by (metis append_eq_append_conv append_take_drop_id drop_all_conc length_drop length_set_of_appr)

lemma op_take_image_autoref[autoref_rules]:
  shows "(\<lambda>ni xs. take ni xs, op_take_image) \<in> nat_rel \<rightarrow> appr_rell \<rightarrow> appr_rell"
  apply (auto simp: appr_rell_internal br_def )
  subgoal by (rule take_set_of_apprD)
  subgoal by (rule set_of_appr_takeD)
  done

definition [simp]: "op_drop_image n X = drop n ` X"
lemma [autoref_op_pat_def]: "drop n ` X \<equiv> OP op_drop_image $ n $ X" by simp

lemma drop_eq_map_nth: "drop n xs = map ((!) xs) [n..<length xs]"
  by (auto intro!: nth_equalityI simp: nth_append)

lemma drop_set_of_apprD: "xs \<in> set_of_appr XS \<Longrightarrow> drop n xs \<in> set_of_appr (drop n XS)"
   apply (subst drop_eq_map_nth)
   apply (subst drop_eq_map_nth)
    apply (simp add: length_set_of_appr)
   apply (rule set_of_appr_project)
  by (auto simp: length_set_of_appr)

lemma drop_append_drop_minus_idem: "n < length XS \<Longrightarrow> map ((!) XS) [0..<n] @ drop n XS = XS"
  by (auto intro!: nth_equalityI simp: nth_append)

lemma set_of_appr_dropD: "xs \<in> set_of_appr (drop n XS) \<Longrightarrow> xs \<in> drop n ` set_of_appr XS"
  apply (cases "n < length XS")
  subgoal
    apply (frule set_of_appr_ex_append1[where b="map ((!) XS) [0..<n]"])
    apply (auto simp: drop_append_drop_minus_idem)
    apply (rule image_eqI)
    prefer 2 apply assumption
    by (metis (mono_tags, lifting) diff_add_inverse2 diff_diff_cancel drop_all_conc length_append
        length_drop length_set_of_appr less_imp_le)
  subgoal
    using set_of_appr_nonempty[of XS]
    by (auto simp: length_set_of_appr image_iff simp del: set_of_appr_nonempty)
  done

lemma op_drop_image_autoref[autoref_rules]:
  shows "(\<lambda>ni xs. drop ni xs, op_drop_image) \<in> nat_rel \<rightarrow> appr_rell \<rightarrow> appr_rell"
  apply (auto simp: appr_rell_internal br_def )
  subgoal by (rule drop_set_of_apprD)
  subgoal by (rule set_of_appr_dropD)
  done

lemma inj_on_nat_add_square: "inj_on (\<lambda>a::nat. a + a * a) S"
  by (rule strict_mono_imp_inj_on) (auto intro!: strict_monoI add_strict_mono mult_strict_mono)

lemma add_sq_eq[simp]: "a + a * a = b + b * b \<longleftrightarrow> a = b" for a b::nat
  using inj_on_nat_add_square[of UNIV, unfolded inj_on_def, rule_format, of a b]
  by auto

lemma mem_set_of_appr_appendE:
  assumes "zs \<in> set_of_appr (XS @ YS)"
  obtains xs ys where "zs = xs @ ys" "xs \<in> set_of_appr XS" "ys \<in> set_of_appr YS"
proof -
  have "zs = map ((!) zs) [0..<length XS] @ map ((!) zs) [length XS..<length XS + length YS]"
    using assms
    by (auto intro!: nth_equalityI simp: nth_append dest!: length_set_of_appr)
  moreover
  from
    set_of_appr_project[OF assms, of "[0..<length XS]"]
    set_of_appr_project[OF assms, of "[length XS..<length XS + length YS]"]
  have "map ((!) zs) [0..<length XS] \<in> set_of_appr XS"
    "map ((!) zs) [length XS..<length XS + length YS] \<in> set_of_appr YS"
    by (auto simp : map_nth_append2 map_nth_append1)
  ultimately show ?thesis ..
qed

lemma set_of_appr_of_ivl_append_point:
  "set_of_appr (xs @ appr_of_ivl p p) = (\<lambda>x. x @ p) ` set_of_appr xs"
  apply auto
   apply (frule length_set_of_appr)
  subgoal for x
    apply (rule image_eqI[where x="take (length xs) x"])
     apply (auto intro!: nth_equalityI simp: min_def)
     apply (simp add: nth_append)
    subgoal for i
      apply (frule set_of_appr_project[where ?is="[length xs..<length xs + length p]"])
       apply simp
      apply (auto simp: map_nth_append2 set_of_appr_of_ivl_point)
      subgoal premises prems
      proof -
        from prems
        have "map ((!) x) [length xs..<length xs + length p] ! (i - length xs) =
          p ! (i - length xs)"
          by simp
        also have "map ((!) x) [length xs..<length xs + length p] ! (i - length xs) = x ! i"
          using prems
          apply (auto simp: map_nth)
          by (metis add_diff_cancel_left' add_diff_inverse_nat add_less_cancel_left nth_map_upt)
        finally show ?thesis
          using prems by (simp add: min_def)
      qed
      done
    subgoal
      apply (frule set_of_appr_project[where ?is="[0..<length xs]"])
       apply (auto simp: map_nth_append1 take_eq_map_nth
          elim!: mem_set_of_appr_appendE
          dest: length_set_of_appr)
      done
    done
  subgoal premises prems for x
  proof -
    from set_of_appr_ex_append2[where b="appr_of_ivl p p", OF \<open>x \<in> set_of_appr xs\<close>]
    obtain r where r: "x @ r \<in> set_of_appr (xs @ appr_of_ivl p p)"
      by auto
    have "map ((!) (x @ r)) [length xs..<length xs + (length p)]
        \<in> set_of_appr
            (map ((!) (xs @ appr_of_ivl p p))
              [length xs..<length xs + (length p)])"
      by (rule set_of_appr_project[OF r, of "[length xs..<length xs+(length p)]"])
         auto
    also have "map ((!) (x @ r)) [length xs..<length xs + (length p)] = r"
      using length_set_of_appr prems r
      by (auto intro!: nth_equalityI simp: nth_append dest!: length_set_of_appr)
    also have "map ((!) (xs @ appr_of_ivl p p))
        [length xs..<length xs + (length p)] = appr_of_ivl p p"
      by (auto intro!: nth_equalityI)
    finally have "r = p"
      by (auto simp: set_of_appr_of_ivl_point)
    with r show ?thesis by simp
  qed
  done

lemma set_of_appr_of_ivl_point_append:
  "set_of_appr (appr_of_ivl p p @ xs) = (\<lambda>x. p @ x) ` set_of_appr xs"
  apply auto
   apply (frule length_set_of_appr)
  subgoal for x
    apply (rule image_eqI[where x="drop (length p) x"])
     apply (auto intro!: nth_equalityI simp: min_def)
     apply (simp add: nth_append)
    subgoal for i
      apply (frule set_of_appr_project[where ?is="[0..<(length p)]"])
       apply simp
      apply (auto simp: map_nth_append1 dest: length_set_of_appr)
      by (metis insertE mem_set_of_appr_appendE memb_imp_not_empty nth_append_cond(1) set_of_appr_of_ivl_point)
    by (metis add_right_imp_eq drop_all_conc drop_set_of_apprD length_append length_set_of_appr)
  subgoal premises prems for x
  proof -
    from set_of_appr_ex_append1[where b="appr_of_ivl p p",
        OF \<open>x \<in> set_of_appr xs\<close>]
    obtain r where r: "r @ x \<in> set_of_appr (appr_of_ivl p p @ xs)"
      by auto
    have "map ((!) (r @ x)) [0..<(length p)]
        \<in> set_of_appr
            (map ((!) (appr_of_ivl p p @ xs))
              [0..<(length p)])"
      by (rule set_of_appr_project[OF r, of "[0..<(length p)]"])
         (auto simp: )
    also have "map ((!) (r @ x)) [0..<(length p)] = r"
      using length_set_of_appr prems r
      by (auto intro!: nth_equalityI simp: nth_append dest!: length_set_of_appr)
    also have "map ((!) (appr_of_ivl p p @ xs))
        [0..<(length p)] = appr_of_ivl p p"
      by (auto intro!: nth_equalityI simp: nth_append)
    finally have "r = p"
      by (auto simp: set_of_appr_of_ivl_point)
    with r show ?thesis by simp
  qed
  done

lemma op_eucl_of_list_image_pad:
  assumes "(xsi, xs) \<in> appr_rell" "DIM_precond TYPE('a::executable_euclidean_space) E"
  shows "(take E xsi @ (let z = replicate (E - length xsi) 0 in appr_of_ivl z z),
    op_eucl_of_list_image $ xs::'a set) \<in> appr_rel"
  using assms
  unfolding appr_rel_br
  apply (auto simp: length_set_of_appr appr_rel_br br_def image_image env_len_def appr_rell_internal)
    apply (auto simp: Let_def set_of_appr_of_ivl_append_point length_set_of_appr)
   apply (rule image_eqI)
    prefer 2
    apply (rule image_eqI)
     apply (rule refl)
    apply (rule take_set_of_apprD)
    apply assumption
   apply auto
  apply (drule set_of_appr_takeD)
  apply auto
  done
concrete_definition op_eucl_of_list_image_pad for E xsi uses op_eucl_of_list_image_pad
lemma op_eucl_of_list_image_pad_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) E \<Longrightarrow>
  (op_eucl_of_list_image_pad E, op_eucl_of_list_image::_\<Rightarrow>'a set) \<in> appr_rell \<rightarrow> appr_rel"
  using op_eucl_of_list_image_pad.refine
  by force

definition "approx_slp_appr fas slp X = do {
    cfp \<leftarrow> approx_slp_spec fas DIM('a::executable_euclidean_space) slp X;
    (case cfp of
      Some cfp \<Rightarrow> do {
        RETURN ((eucl_of_list ` cfp::'a set):::appr_rel)
      }
      | None \<Rightarrow> do {
        SUCCEED
      }
    )
  }"
sublocale autoref_op_pat_def approx_slp_appr .
lemma [autoref_op_pat_def]: "approx_slp_appr fas \<equiv> OP (approx_slp_appr fas)"
  by auto
schematic_goal approx_slp_appr_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) E"
  assumes [autoref_rules]: "(slpi, slp) \<in> slp_rel" "(Xi, X) \<in> appr_rell"
    notes [autoref_rules] = IdI[of E]
  shows "(nres_of ?r, approx_slp_appr fas $ slp $ X::'a set nres) \<in> \<langle>appr_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding approx_slp_appr_def assms(1)[unfolded DIM_eq_def]
  including art
  by autoref_monadic

concrete_definition approx_slp_appr_impl for E slpi Xi uses approx_slp_appr_impl
lemma approx_slp_appr_impl_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) E \<Longrightarrow>
(\<lambda>slpi Xi. nres_of (approx_slp_appr_impl E slpi Xi), approx_slp_appr fas::_\<Rightarrow>_\<Rightarrow>'a set nres) \<in>
    slp_rel \<rightarrow> appr_rell \<rightarrow> \<langle>appr_rel\<rangle>nres_rel"
  using approx_slp_appr_impl.refine[where 'a='a, of E]
  by force

end

context begin interpretation autoref_syn .

lemma [autoref_rules]:
  "(slp_of_fas, slp_of_fas) \<in> fas_rel \<rightarrow> slp_rel"
  "(Norm, Norm) \<in> fas_rel \<rightarrow> Id"
  by auto

lemma length_slp_of_fas_le: "length fas \<le> length (slp_of_fas fas)"
  by (auto simp: slp_of_fas_def split: prod.splits)

lemma list_of_eucl_eqD: "list_of_eucl x = xs \<Longrightarrow> x = eucl_of_list xs"
  by auto

lemma slp_of_fasI:
  "d = (length fas) \<Longrightarrow>
    take d (interpret_slp (slp_of_fas fas) xs) =
    interpret_floatariths fas xs"
  using slp_of_fas by force

lemma [autoref_rules]: "(norm2_slp, norm2_slp) \<in> nat_rel \<rightarrow> Id"
  by auto

lemma [autoref_rules]:
  "(floatarith.Var, floatarith.Var) \<in> nat_rel \<rightarrow> Id"
  "(slp_of_fas, slp_of_fas) \<in> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel"
  "(fold_const_fa, fold_const_fa) \<in> Id \<rightarrow> Id"
  "(open_form, open_form) \<in> Id \<rightarrow> bool_rel"
  "(max_Var_floatariths, max_Var_floatariths) \<in> \<langle>Id\<rangle>list_rel \<rightarrow> nat_rel"
  "(max_Var_form, max_Var_form) \<in> Id \<rightarrow> nat_rel"
  "(length, length) \<in> \<langle>A\<rangle>list_rel \<rightarrow> nat_rel"
  by (auto simp: list_rel_imp_same_length)

end

context approximate_sets begin

lemma approx_fas[le, refine_vcg]:
  "approx_slp_appr fas slp X \<le> SPEC (\<lambda>R. \<forall>x \<in> X. einterpret fas x \<in> (R::'a set))"
  if "slp_of_fas fas = slp" "length fas = DIM('a::executable_euclidean_space)"
  unfolding approx_slp_appr_def
  by (refine_vcg that)

definition "mig_set D (X::'a::executable_euclidean_space set) = do {
    (i, s) \<leftarrow> ivl_rep_of_set (X:::appr_rel);
    let migc = mig_componentwise i s;
    ASSUME (D = DIM('a));
    let norm_fas = ([Norm (map Var [0..<D])]:::\<langle>Id\<rangle>list_rel);
    let env = (list_of_eucl ` ({migc .. migc}:::appr_rel):::appr_rell);
    (n::real set) \<leftarrow> approx_slp_appr  norm_fas (slp_of_fas norm_fas) env;
    (ni::real) \<leftarrow> Inf_spec (n:::appr_rel);
    RETURN (rnv_of_lv ni::real)
  }"

lemma DIM_precond_real[autoref_rules_raw]: "DIM_precond TYPE(real) 1" by simp

schematic_goal mig_set_impl: "(nres_of ?r, mig_set $ D $ X) \<in> \<langle>rnv_rel\<rangle>nres_rel"
  if [autoref_rules]: "(Xi, X::'a set) \<in> appr_rel"  "(Di, D) \<in> nat_rel"
  and [autoref_rules_raw, simplified, simp]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  unfolding autoref_tag_defs
  unfolding mig_set_def
  including art
  by autoref_monadic
concrete_definition mig_set_impl for Di Xi uses mig_set_impl
lemma mig_set_impl_refine[autoref_rules]:
  "(\<lambda>x. nres_of (mig_set_impl D x), mig_set $ D::'a set\<Rightarrow>_) \<in> appr_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  if "DIM_precond TYPE('a::executable_euclidean_space) D" "(Di, D) \<in> nat_rel"
  using mig_set_impl.refine that by force

lemma mig_set[le, refine_vcg]: "mig_set D X \<le> SPEC (\<lambda>m. \<forall>x \<in> X. m \<le> norm x)"
  unfolding mig_set_def
  apply refine_vcg
  apply (auto simp: dest!: bspec)
  apply (rule order_trans, assumption)
  apply (rule norm_mig_componentwise_le)
  by auto

end

consts i_alt::"interface \<Rightarrow> interface \<Rightarrow> interface"
context begin
interpretation autoref_syn .
definition alt_rel_internal: "alt_rel A B = {(x, y). case x of Inl x \<Rightarrow> (x, y) \<in> A | Inr x \<Rightarrow> (x, y) \<in> B}"

lemma alt_rel_def: "\<langle>A, B\<rangle>alt_rel = {(x, y). case x of Inl x \<Rightarrow> (x, y) \<in> A | Inr x \<Rightarrow> (x, y) \<in> B}"
  by (auto simp: relAPP_def alt_rel_internal)

primrec mk_alt::"'a + 'a \<Rightarrow> 'a" where
  "mk_alt (Inl X) = X"
| "mk_alt (Inr X) = X"

lemma alt_rel_const[autoref_rules]: "(\<lambda>x. x, mk_alt) \<in> \<langle>A, B\<rangle>sum_rel \<rightarrow> \<langle>A, B\<rangle>alt_rel"
  by (auto simp: mk_alt_def alt_rel_def split: sum.splits)

lemma unop_alt_rel:
  assumes "GEN_OP fa f (A \<rightarrow> C)"
  assumes "GEN_OP fb f (B \<rightarrow> D)"
  shows "(map_sum fa fb, f) \<in> \<langle>A, B\<rangle>alt_rel \<rightarrow> \<langle>C, D\<rangle>alt_rel"
  using assms
  by (auto simp: alt_rel_def map_sum_def split: sum.splits dest: fun_relD)

end

lemma prod_relI': "\<lbrakk>(a,fst ab')\<in>R1; (b,snd ab')\<in>R2\<rbrakk> \<Longrightarrow> ((a,b),ab')\<in>\<langle>R1,R2\<rangle>prod_rel"
  by  (auto simp: prod_rel_def)

lemma lv_relivl_relI:
  "((xs', ys'), {eucl_of_list xs..eucl_of_list ys::'a::executable_euclidean_space}) \<in> \<langle>lv_rel\<rangle>ivl_rel"
  if [simp]: "xs' = xs" "ys' = ys" "DIM('a) = length xs" "length ys = length xs"
  by (force simp: ivl_rel_def set_of_ivl_def
      intro!:  brI lv_relI prod_relI[of _ "eucl_of_list xs" _ _ "eucl_of_list ys"])

end