theory Concrete_Reachability_Analysis_C1
imports
  Abstract_Reachability_Analysis_C1
  Concrete_Reachability_Analysis
begin

lemma appr1e_rep_impl[autoref_rules]:
  "(\<lambda>x. RETURN x, scaleR2_rep) \<in> \<langle>A\<rangle>scaleR2_rel \<rightarrow> \<langle>(ereal_rel \<times>\<^sub>r ereal_rel) \<times>\<^sub>r A\<rangle>nres_rel"
  by (force simp: nres_rel_def scaleR2_rep_def scaleR2_rel_def image_image split_beta'
      dest!: brD intro!: RETURN_SPEC_refine)

lemma [autoref_op_pat]: "fst ` X \<equiv> Autoref_Tagging.APP (Autoref_Tagging.OP op_image_fst_colle) X"
  by auto

lemma [autoref_op_pat]: "fst ` X \<equiv> Autoref_Tagging.APP (Autoref_Tagging.OP op_image_fste) X"
  by simp

context approximate_sets_ode_slp'
begin

context includes autoref_syntax begin

lemma nonneg_reals_autoref[autoref_rules]: "(None, nonneg_reals) \<in> \<langle>Id\<rangle>phantom_rel"
  and pos_reals_autoref[autoref_rules]: "(None, pos_reals) \<in> \<langle>Id\<rangle>phantom_rel"
  by (auto simp: phantom_rel_def)

lemma appr1_relI:
  assumes "c1_info_invar DIM('n::executable_euclidean_space) X0i"
  shows "(X0i, (c1_info_of_appr X0i::'n c1_info set)) \<in> appr1_rel"
    using assms
  apply (cases "snd X0i")
  subgoal
    apply (simp add: c1_info_of_appr_def c1_info_invar_def)
    unfolding appr1_rel_internal
    apply (rule UnI1)
    apply auto
    apply (rule exI[where x="fst X0i"])
    apply safe
    subgoal by (auto simp: prod_eq_iff)
    subgoal
      apply (rule exI[where x="eucl_of_list ` set_of_appr (fst X0i)"])
      apply (auto simp: appr_rel_def)
      by (auto simp: appr_rell_internal lv_rel_def set_rel_br br_chain length_set_of_appr
          intro!: brI)
    done
  subgoal for D
    apply (simp add: c1_info_of_appr_def c1_info_invar_def)
    unfolding appr1_rel_internal
    apply (rule UnI2)
    apply (auto simp: set_rel_br)
    apply (rule exI[where x="fst X0i"])
    apply (rule exI[where x=D])
    apply safe
    subgoal by (auto simp: prod_eq_iff)
    subgoal
      by (auto simp: appr_rell_internal lv_rel_def set_rel_br br_chain length_set_of_appr
          intro!: brI) (auto simp:  power2_eq_square)
    done
  done

lemma appr1_rel_br: "appr1_rel = br (c1_info_of_appr::_\<Rightarrow>('n c1_info)set) (c1_info_invar DIM('n::executable_euclidean_space))"
  apply (auto simp: dest!: brD intro!: appr1_relI)
  apply (rule brI)
  subgoal by (auto simp: appr1_rel_internal c1_info_of_appr_def appr_rel_br set_rel_br dest!: brD)
  subgoal by (auto simp: c1_info_invar_def appr1_rel_internal appr_rel_br power2_eq_square dest!: brD)
  done

lemma appr1_rel_aux:
  "{((xs, Some ys), X) |xs ys X. (xs @ ys, X) \<in> appr_rel \<and> length ys = (length xs)\<^sup>2} O
    \<langle>br flow1_of_vec1 top\<rangle>set_rel =
  {((xs, Some ys), X::'n eucl1 set) |xs ys X.
     X = (\<lambda>xs. flow1_of_vec1 (eucl_of_list xs)) ` set_of_appr (xs @ ys) \<and>
     length xs = DIM((real, 'n::enum) vec) \<and> length ys = DIM((real, 'n) vec) * DIM((real, 'n) vec)}"
  apply (auto simp: set_rel_br appr_rel_br power2_eq_square dest!: brD)
  apply (rule relcompI)
   apply simp
   apply (rule brI) apply (rule refl) apply simp
  apply (rule brI) defer apply simp
  apply auto
  done

lemma flow1_of_list_def':
  shows "flow1_of_list xs = flow1_of_vec1 (eucl_of_list xs)"
  by (auto simp: flow1_of_list_def flow1_of_vec1_def eucl_of_list_prod
      blinfun_of_list_eq_blinfun_of_vmatrix)

lemma appr1_rel_def:
  "appr1_rel =
    {((xs, None   ), X \<times> UNIV)| xs X. (xs, X) \<in> appr_rel} \<union>
    {((xs, Some ys), X)| xs ys X. (xs @ ys, X) \<in> appr_rel \<and> length ys = (length xs)\<^sup>2} O \<langle>br flow1_of_vec1 top\<rangle>set_rel"
  unfolding appr1_rel_internal flow1_of_list_def'[abs_def] appr1_rel_aux ..

lemmas [autoref_rel_intf] = REL_INTFI[of appr1_rel i_appr1]
lemma [autoref_op_pat]: "(`) flow1_of_vec1 \<equiv> OP op_image_flow1_of_vec1"
  by auto

lemma op_image_flow1_of_vec1[autoref_rules]:
  assumes "DIM_precond TYPE('a rvec) D"
  shows "(\<lambda>xs. (take D xs, Some (drop D xs)),
    op_image_flow1_of_vec1::('a::enum) vec1 set\<Rightarrow>_) \<in> appr_rel \<rightarrow> appr1_rel"
  using assms
  apply (auto simp: appr1_rel_def set_rel_br flow1_of_vec1_def[abs_def] intro!: brI elim!: notE
      split: option.splits list.splits)
  apply (rule relcompI[OF _ brI[OF refl]])
   apply (auto simp: power2_eq_square min_def appr_rel_br br_def)
  done

lemma index_autoref[autoref_rules]:
  "(index, index) \<in> \<langle>lv_rel\<rangle>list_rel \<rightarrow> lv_rel \<rightarrow> nat_rel"
  unfolding index_def[abs_def] find_index_def
  apply parametricity
  apply (auto simp: lv_rel_def br_def list_rel_def)
  using list_of_eucl_eucl_of_list by force

lemma [autoref_op_pat]: "(`) fst \<equiv> OP op_image_fst"
  by auto

lemma op_image_fst_flow1[autoref_rules]:
  shows "(\<lambda>x. fst x, op_image_fst::_\<Rightarrow>'n::executable_euclidean_space set) \<in> appr1_rel \<rightarrow> appr_rel"
  apply (auto simp: appr1_rel_internal flow1_of_list_def set_rel_br image_image power2_eq_square dest!: brD)
  apply (auto simp: br_def appr_rel_br length_set_of_appr image_image eucl_of_list_prod
      dest!: set_of_appr_takeD)
  subgoal for xs ys a
    apply (rule image_eqI[where x="take DIM('n) a"])
    by (auto intro!: take_set_of_apprI dest: length_set_of_appr)
  subgoal for xs ys a
    apply (frule set_of_appr_ex_append2[where b=ys])
    apply auto
    subgoal for r
      apply (rule image_eqI[where x="a @ r"])
       apply (auto simp: length_set_of_appr )
      apply (rule eucl_of_list_eqI)
      by (auto dest!: length_set_of_appr)
    done
  done

lemma op_image_fste_impl[autoref_rules]:
  "((\<lambda>(_, x, _). x), op_image_fste) \<in> appr1e_rel \<rightarrow> appr_rel"
  by (auto simp: image_image split_beta' scaleR2_rel_def
      dest!: op_image_fst_flow1[param_fo] brD)

lemma DIM_precond_vec1I[autoref_rules_raw]:
  assumes "DIM_precond TYPE('n::enum rvec) D"
  shows "DIM_precond TYPE('n::enum vec1) (D + D*D)"
  using assms
  by (auto simp: )

lemma vec1rep_impl[autoref_rules]:
  "(\<lambda>(a, bs). RETURN (map_option ((@) a) bs), vec1rep) \<in> appr1_rel \<rightarrow> \<langle>\<langle>appr_rel\<rangle>option_rel\<rangle>nres_rel"
  apply (auto simp: vec1rep_def appr1_rel_def set_rel_br appr_rel_def power2_eq_square nres_rel_def
      dest!: brD
      intro!: RETURN_SPEC_refine)
  subgoal for xs ys a b
    apply (rule exI[where x="Some (eucl_of_list ` set_of_appr (xs @ ys))"])
    apply (auto simp: appr_rell_internal image_image lv_rel_def set_rel_br length_set_of_appr intro!: brI
        dest!: brD)
    done
  done

lemma [autoref_op_pat]: "X \<times> UNIV \<equiv> OP op_times_UNIV $ X" by simp

lemma op_times_UNIV_impl[autoref_rules]: "(\<lambda>x. (x, None), op_times_UNIV) \<in> appr_rel \<rightarrow> appr1_rel"
  by (auto simp: appr1_rel_internal)

lemma solve_poincare_slp_autoref: "(solve_poincare_slp, solve_poincare_slp) \<in> \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel"
  by auto

lemmas autoref_parameters2 = autoref_parameters solve_poincare_slp_autoref

schematic_goal solve_poincare_plane_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules]: "(ni, n) \<in> lv_rel" and CX[autoref_rules]: "(CXi, CX) \<in> appr1_rel"
  assumes ncc: "ncc_precond TYPE('n vec1)"
  notes [autoref_rules] = autoref_parameters2
  shows "(nres_of (?R), solve_poincare_plane $ n $ (CX::'n eucl1 set)) \<in> \<langle>appr1_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding solve_poincare_plane_def
  including art
  by autoref_monadic
concrete_definition solve_poincare_plane_impl for ni CXi uses solve_poincare_plane_impl
lemma solve_poincare_plane_impl_refine[autoref_rules]:
  "DIM_precond TYPE((real, 'n::enum) vec) D \<Longrightarrow> ncc_precond TYPE('n vec1) \<Longrightarrow>
  (\<lambda>ni CXi. nres_of (solve_poincare_plane_impl ni CXi), solve_poincare_plane::'n rvec \<Rightarrow> _)
  \<in> lv_rel \<rightarrow> appr1_rel \<rightarrow> \<langle>appr1_rel\<rangle>nres_rel"
  using solve_poincare_plane_impl.refine
  by force

lemma [autoref_rules_raw]:
  assumes "DIM_precond TYPE((real, 'n::enum) vec) K"
  shows "DIM_precond TYPE(((real, 'n) vec, 'n) vec) (K * K)"
  using assms by auto

lemma embed1_impl[autoref_rules]:
  assumes "DIM_precond TYPE((real, 'n::enum) vec) D"
  shows "((\<lambda>x. x @ replicate (D * D) 0), embed1::'n rvec\<Rightarrow>_) \<in> lv_rel \<rightarrow> lv_rel"
  using assms
  by (auto simp: lv_rel_def br_def eucl_of_list_prod)


lemma autoref_has_c1_slps[autoref_rules]: "(c1_slps \<noteq> None, has_c1_slps) \<in> bool_rel"
  by (auto simp: has_c1_slps_def)

lemma has_c1_slps_pat[autoref_op_pat_def]: "has_c1_slps \<equiv> OP has_c1_slps" by simp

schematic_goal choose_step1_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) D"
    "ncc_precond TYPE('n vec1)"
    "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules]: "(Xi, X::'n eucl1 set) \<in> appr1_rel" "(hi, h) \<in> rnv_rel"
  notes [autoref_post_simps] = fst_conv
  shows "(nres_of ?f, choose_step1 $ X $ h) \<in> \<langle>rnv_rel \<times>\<^sub>r appr1_rel \<times>\<^sub>r appr1_rel \<times>\<^sub>r appr1_rel\<rangle>nres_rel"
  unfolding choose_step1_def
  including art
  by autoref_monadic
concrete_definition choose_step1_impl for Xi hi uses choose_step1_impl
lemmas [autoref_rules] = choose_step1_impl.refine

lemma op_image_zerofst_impl[autoref_rules]:
  "(\<lambda>(_, x). (appr_of_ivl (replicate D 0) (replicate D 0), x), op_image_zerofst::'n c1_info set \<Rightarrow> _)
    \<in> appr1_rel \<rightarrow> appr1_rel"
  if "DIM_precond (TYPE('n::executable_euclidean_space)) D"
  using that
  apply (auto simp: appr1_rel_br dest!: brD intro!: brI)
  subgoal by (force simp: c1_info_of_appr_def image_image flow1_of_list_def
        set_of_appr_of_ivl_point_append eucl_of_list_prod c1_info_invar_def length_set_of_appr
        split: option.splits elim!: mem_set_of_appr_appendE cong del: image_cong_simp)
  subgoal for a b c d
    apply (auto simp: c1_info_of_appr_def
        split: option.splits)
    subgoal using set_of_appr_nonempty[of a]
      by (force  simp del: set_of_appr_nonempty)
    subgoal
      supply [simp del] = eucl_of_list_take_DIM
      apply (auto simp: image_image set_of_appr_of_ivl_point_append
          flow1_of_list_def)
      apply (frule set_of_appr_ex_append1[where b=a])
      apply auto
      apply (rule image_eqI) prefer 2 apply assumption
      by (auto simp: eucl_of_list_prod c1_info_invar_def
          dest!: length_set_of_appr)
    done
  subgoal
    by (auto simp: c1_info_of_appr_def flow1_of_vec1_def image_image
        set_of_appr_of_ivl_point_append eucl_of_list_prod c1_info_invar_def length_set_of_appr
        split: option.splits elim!: mem_set_of_appr_appendE)
  done

lemma op_image_zerofst_vec_impl[autoref_rules]:
  "(\<lambda>x. (appr_of_ivl (replicate D 0) (replicate D 0) @ drop D x), op_image_zerofst_vec::'n vec1 set \<Rightarrow> _)
    \<in> appr_rel \<rightarrow> appr_rel"
  if "DIM_precond (TYPE('n::enum rvec)) D"
  using that
  apply (auto simp: appr_rel_br set_of_appr_of_ivl_point_append image_image eucl_of_list_prod
      dest!: brD intro!: brI
      dest: drop_set_of_apprD[where n="CARD('n)"] cong del: image_cong_simp)
  subgoal for a b
    apply (drule set_of_appr_dropD)
    apply safe
    apply (rule image_eqI) defer apply assumption
    apply (auto simp: eucl_of_list_prod)
    apply (rule eucl_of_list_eq_takeI)
    apply simp
    done
  done

lemma [autoref_op_pat_def]: "embed1 ` X \<equiv> OP op_image_embed1 $ X"
  by auto

lemma op_image_embed1_impl[autoref_rules]:
  assumes "DIM_precond TYPE((real, 'n::enum) vec) D"
  shows "(\<lambda>x. x@appr_of_ivl (replicate (D*D) 0) (replicate (D*D) 0), op_image_embed1::'n rvec set \<Rightarrow> _)
    \<in> appr_rel \<rightarrow> appr_rel"
  using assms
  by (force simp: appr_rel_br br_def set_of_appr_of_ivl_point_append set_of_appr_of_ivl_append_point
      image_image eucl_of_list_prod length_set_of_appr)

lemma sv_appr1_rel[relator_props]: "single_valued appr1_rel"
  apply (auto simp:  appr1_rel_internal appr_rel_def intro!: relator_props single_valued_union)
   apply (auto simp: single_valued_def)
   apply (auto simp: lv_rel_def set_rel_br)
   apply (auto simp: br_def)
   apply (rule imageI)
  apply (metis single_valued_def sv_appr_rell)
  by (metis imageI single_valued_def sv_appr_rell)

schematic_goal inter_sctn1_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) D" "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(Xi, (X::'n eucl1 set)) \<in> appr1_rel" "(hi, h) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(nres_of ?f, inter_sctn1_spec $ X $ h) \<in> \<langle>appr1_rel \<times>\<^sub>r appr1_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding inter_sctn1_spec_def
  including art
  by autoref_monadic
concrete_definition inter_sctn1_impl for Xi hi uses inter_sctn1_impl
lemmas [autoref_rules] = inter_sctn1_impl.refine

schematic_goal op_image_fst_coll_nres_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::executable_euclidean_space) D"
  assumes [autoref_rules]: "(XSi, (XS::'n c1_info set)) \<in> clw_rel appr1_rel"
  shows "(RETURN ?r, op_image_fst_coll_nres $ XS) \<in> \<langle>clw_rel appr_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding op_image_fst_coll_nres_def
  including art
  by (autoref_monadic (plain))
concrete_definition op_image_fst_coll_nres_impl for XSi uses op_image_fst_coll_nres_impl
lemmas [autoref_rules] = op_image_fst_coll_nres_impl.refine

lemma [autoref_op_pat]: "(`) fst \<equiv> OP op_image_fst_coll"
  by auto
lemma op_image_fst_coll_impl[autoref_rules]:
  assumes "DIM_precond TYPE('n::executable_euclidean_space) D"
  shows "(op_image_fst_coll_nres_impl, op_image_fst_coll::_\<Rightarrow>'n set) \<in> clw_rel appr1_rel \<rightarrow> clw_rel appr_rel"
  apply rule
  subgoal premises prems for x
    using nres_rel_trans2[OF op_image_fst_coll_nres_spec[OF order_refl]
      op_image_fst_coll_nres_impl.refine[OF assms, simplified, OF prems]]
    by (auto simp: nres_rel_def RETURN_RES_refine_iff)
  done

schematic_goal fst_safe_coll_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::executable_euclidean_space) D"
  assumes [autoref_rules]: "(XSi, (XS::'n c1_info set)) \<in> clw_rel appr1_rel"
  shows "(nres_of ?r, fst_safe_coll $ XS) \<in> \<langle>clw_rel sappr_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding fst_safe_coll_def
  including art
  by autoref_monadic
concrete_definition fst_safe_coll_impl for XSi uses fst_safe_coll_impl
lemmas [autoref_rules] = fst_safe_coll_impl.refine

lemma [autoref_op_pat]: "(`) flow1_of_vec1 \<equiv> OP op_image_flow1_of_vec1_coll"
  by auto

lemma op_image_flow1_of_vec1_coll[autoref_rules]:
  "(map (\<lambda>x. (take D x, Some (drop D x))), op_image_flow1_of_vec1_coll::_\<Rightarrow>'n eucl1 set) \<in> clw_rel appr_rel \<rightarrow> clw_rel appr1_rel"
  if "DIM_precond TYPE('n::enum rvec) D"
  apply (rule lift_clw_rel_map)
     apply (rule relator_props)
  apply (rule relator_props)
  unfolding op_image_flow1_of_vec1_coll_def op_image_flow1_of_vec1_def[symmetric]
  apply (rule op_image_flow1_of_vec1)
  using that
  by auto

schematic_goal vec1reps_impl:
  assumes [autoref_rules]: "(Xi, X) \<in> clw_rel appr1_rel"
  shows "(RETURN ?r, vec1reps X) \<in> \<langle>\<langle>clw_rel appr_rel\<rangle>option_rel\<rangle>nres_rel"
  unfolding vec1reps_def
  including art
  by (autoref_monadic (plain))
concrete_definition vec1reps_impl for Xi uses vec1reps_impl
lemma vec1reps_impl_refine[autoref_rules]:
  "(\<lambda>x. RETURN (vec1reps_impl x), vec1reps) \<in> clw_rel appr1_rel \<rightarrow> \<langle>\<langle>clw_rel appr_rel\<rangle>option_rel\<rangle>nres_rel"
  using vec1reps_impl.refine by force

abbreviation "intersection_STATE_rel \<equiv>
  (appr1_rel \<times>\<^sub>r \<langle>Id\<rangle>phantom_rel \<times>\<^sub>r clw_rel appr1_rel \<times>\<^sub>r clw_rel appr1_rel \<times>\<^sub>r
    clw_rel (\<langle>sappr_rel, \<langle>lv_rel\<rangle>sbelows_rel\<rangle>inter_rel) \<times>\<^sub>r bool_rel \<times>\<^sub>r bool_rel)"

lemma print_set_impl1[autoref_rules]:
  shows "(\<lambda>a s. printing_fun optns a (list_of_appr1 s), print_set1) \<in> bool_rel \<rightarrow> A \<rightarrow> Id"
  by auto

lemma trace_set1_impl1[autoref_rules]:
  shows "(\<lambda>s a. tracing_fun optns s (map_option list_of_appr1 a), trace_set1) \<in> string_rel \<rightarrow> \<langle>A\<rangle>option_rel \<rightarrow> Id"
  by auto

lemma print_set_impl1e[autoref_rules]:
  shows "(\<lambda>a s. printing_fun optns a (list_of_appr1e s), print_set1e) \<in> bool_rel \<rightarrow> A \<rightarrow> Id"
  by auto
lemma trace_set1_impl1e[autoref_rules]:
  shows "(\<lambda>s a. tracing_fun optns s (map_option (list_of_appr1e) a), trace_set1e) \<in> string_rel \<rightarrow> \<langle>A\<rangle>option_rel \<rightarrow> Id"
  by auto


lemma under_pre_inter_granularity_spec_impl[autoref_rules]:
  "(\<lambda>ro x. RETURN (width_appr optns x \<le> pre_inter_granularity ro x), (under_pre_inter_granularity_spec)) \<in>
  reach_optns_rel \<rightarrow>
  appr_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  by (auto simp: nres_rel_def)

lemma under_post_inter_granularity_spec_impl[autoref_rules]:
  "(\<lambda>ro x. RETURN (width_appr optns x \<le> post_inter_granularity ro x), under_post_inter_granularity_spec) \<in>
  reach_optns_rel \<rightarrow>
  appr_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  by (auto simp: nres_rel_def)

lemma under_max_tdev_thres_spec_impl[autoref_rules]:
  "(\<lambda>ro x. RETURN (width_appr optns x \<le> max_tdev_thres ro x), under_max_tdev_thres_spec) \<in>
  reach_optns_rel \<rightarrow>
  appr_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  by (auto simp: nres_rel_def)

schematic_goal split_spec_param1_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::enum rvec) D"
  assumes [autoref_rules]: "(Xi, X) \<in> appr1_rel"
  notes [autoref_post_simps] = case_prod_eta
  notes [autoref_rules] = autoref_parameters2
  shows "(nres_of (?f), split_spec_param1 (X::'a eucl1 set)) \<in> \<langle>appr1_rel \<times>\<^sub>r appr1_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding split_spec_param1_def
  including art
  by autoref_monadic
concrete_definition split_spec_param1_impl for Xi uses split_spec_param1_impl
lemma split_spec_param1_refine[autoref_rules]:
  "DIM_precond TYPE('n::enum rvec) D \<Longrightarrow>
    (\<lambda>Xi. nres_of (split_spec_param1_impl Xi), split_spec_param1::_\<Rightarrow>(_\<times>'n eucl1 set)nres)
    \<in> appr1_rel \<rightarrow> \<langle>appr1_rel \<times>\<^sub>r appr1_rel\<rangle>nres_rel "
  using split_spec_param1_impl.refine by force

lemma [autoref_op_pat del]: "{} \<equiv> OP op_empty_default" "{} \<equiv> OP op_empty_coll"
  and [autoref_op_pat_def del]: "get_inter p \<equiv> OP (get_inter p)"
  by simp_all

lemma fst_image_c1_info_of_appr:
  "c1_info_invar (DIM('a)) X \<Longrightarrow>
    (fst ` c1_info_of_appr X::'a::executable_euclidean_space set) = eucl_of_list ` (set_of_appr (fst X))"
  apply (auto simp: c1_info_invar_def power2_eq_square image_image flow1_of_list_def
      c1_info_of_appr_def flow1_of_vec1_def eucl_of_list_prod split: option.splits)
  subgoal for a b
    by (rule image_eqI[where x="take DIM('a) b"]) (auto intro!: take_set_of_apprI simp: length_set_of_appr)
  subgoal for a b
    apply (frule set_of_appr_ex_append2[where b=a])
    apply auto
    subgoal for r
      by (rule image_eqI[where x="b@r"])
         (auto intro!: eucl_of_list_eqI dest!: length_set_of_appr)
    done
  done

lemma op_image_fst_colle_impl[autoref_rules]:
  "(map (\<lambda>(_, x, _). x), op_image_fst_colle) \<in> clw_rel appr1e_rel \<rightarrow> clw_rel appr_rel"
  apply (rule fun_relI)
  unfolding appr_rel_br
  apply (rule map_mem_clw_rel_br)
  unfolding appr1_rel_br
  unfolding scaleR2_rel_br
  unfolding clw_rel_br
   apply (auto dest!: brD simp: image_Union split_beta')
    apply (drule bspec, assumption)
    apply auto
    apply (drule bspec, assumption)
    apply (auto simp: fst_image_c1_info_of_appr)
   apply (rule bexI) prefer 2 apply assumption
   apply (auto simp: scaleR2_rel_br scaleR2_def image_def c1_info_of_appr_def
      split: option.splits)
  subgoal for a b c d e f g h i
    apply (rule bexI[where x="take DIM('a) i"])
    by (auto intro!: take_set_of_apprI simp: flow1_of_list_def eucl_of_list_prod c1_info_invar_def
        length_set_of_appr)
  subgoal
    by (auto intro!: take_set_of_apprI simp: flow1_of_vec1_def eucl_of_list_prod
        length_set_of_appr c1_info_invar_def)
  done


lemma scaleRe_ivl_impl[autoref_rules]:
  "(\<lambda>l u X. if l < u \<or> l > - \<infinity> \<and> l \<le> u \<and> u < \<infinity> then RETURN ((l, u), X) else SUCCEED,
    scaleRe_ivl_spec) \<in> ereal_rel \<rightarrow> ereal_rel \<rightarrow> A \<rightarrow> \<langle>\<langle>A\<rangle>scaleR2_rel\<rangle>nres_rel"
  apply (auto simp: scaleRe_ivl_spec_def scaleR2_rep_def scaleR2_rel_def nres_rel_def
        RETURN_RES_refine_iff
      intro!: RETURN_SPEC_refine )
  apply (rule relcompI)
   apply (rule prod_relI)
    apply (rule IdI)
    apply assumption defer
  apply (rule relcompI)
   apply (rule prod_relI)
    apply (rule IdI)
    apply assumption defer
   apply (auto intro!: brI)
  subgoal for a b c d
    apply (cases a; cases b)
    by (auto simp: vimage_def)
  subgoal for a b c d
    apply (cases a; cases b)
    by (auto simp: vimage_def)
  done

lemma
  is_empty_info_rel_autoref[autoref_rules]:
  "GEN_OP ie is_empty (A \<rightarrow> bool_rel) \<Longrightarrow> (\<lambda>x. ie(snd x), is_empty) \<in> \<langle>R, A\<rangle>info_rel \<rightarrow> bool_rel"
  by (force simp: info_rel_def br_def dest: fun_relD)

lemma is_empty_appr1_rel[autoref_rules]:
  "(\<lambda>_. False, is_empty) \<in> appr1_rel \<rightarrow> bool_rel"
  by (auto simp: appr1_rel_internal set_rel_br) (auto simp: appr_rel_br br_def)

lemma is_empty_scaleR2_rel[autoref_rules]:
  assumes "GEN_OP ie is_empty (A \<rightarrow> bool_rel)"
  shows "(\<lambda>(_, b). ie b, is_empty) \<in> (\<langle>A\<rangle>scaleR2_rel \<rightarrow> bool_rel)"
  using assms[THEN GEN_OP_D, param_fo]
  by (auto simp: scaleR2_rep_def scaleR2_rel_def  scaleR2_def vimage_def
      dest!: brD is_empty_appr1_rel[param_fo])

lemma sv_appr1e_rel[relator_props]: "single_valued A \<Longrightarrow> single_valued (\<langle>A\<rangle>scaleR2_rel)"
  by (auto simp: scaleR2_rep_def scaleR2_rel_def intro!: relator_props)


schematic_goal scaleR2_rep_coll_impl:
  assumes [relator_props]: "single_valued A"
  assumes [autoref_rules]: "(ai, a) \<in> clw_rel (\<langle>A\<rangle>scaleR2_rel)"
  shows "(nres_of ?r, scaleR2_rep_coll a) \<in> \<langle>(ereal_rel \<times>\<^sub>r ereal_rel) \<times>\<^sub>r clw_rel A\<rangle>nres_rel"
  unfolding scaleR2_rep_coll_def
  including art
  by autoref_monadic
concrete_definition scaleR2_rep_coll_impl for ai uses scaleR2_rep_coll_impl
lemma scaleR2_rep_coll_impl_refine[autoref_rules]:
  "PREFER single_valued A \<Longrightarrow> (\<lambda>x. nres_of (scaleR2_rep_coll_impl x), scaleR2_rep_coll) \<in>
    clw_rel (\<langle>A\<rangle>scaleR2_rel) \<rightarrow> \<langle>(ereal_rel \<times>\<^sub>r ereal_rel) \<times>\<^sub>r clw_rel A\<rangle>nres_rel"
  using scaleR2_rep_coll_impl.refine
  by force


schematic_goal split_spec_param1e_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::enum rvec) D"
  assumes [autoref_rules]: "(Xi, X) \<in> \<langle>appr1_rel\<rangle>scaleR2_rel"
  notes [autoref_post_simps] = case_prod_eta
  shows "(nres_of (?f), split_spec_param1e (X::'a eucl1 set)) \<in> \<langle>\<langle>appr1_rel\<rangle>scaleR2_rel \<times>\<^sub>r \<langle>appr1_rel\<rangle>scaleR2_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding split_spec_param1e_def
  including art
  by autoref_monadic
concrete_definition split_spec_param1e_impl for Xi uses split_spec_param1e_impl
lemma split_spec_param1e_refine[autoref_rules]:
  "DIM_precond TYPE('n::enum rvec) D \<Longrightarrow>
    (\<lambda>Xi. nres_of (split_spec_param1e_impl Xi), split_spec_param1e::_\<Rightarrow>(_\<times>'n eucl1 set)nres)
    \<in> \<langle>appr1_rel\<rangle>scaleR2_rel \<rightarrow> \<langle>\<langle>appr1_rel\<rangle>scaleR2_rel \<times>\<^sub>r \<langle>appr1_rel\<rangle>scaleR2_rel\<rangle>nres_rel"
  using split_spec_param1e_impl.refine by force

schematic_goal reduce_spec1_impl:
  "(nres_of ?r, reduce_spec1 C X) \<in> \<langle>appr1_rel\<rangle>nres_rel"
  if [autoref_rules]: "(Xi, X::'n eucl1 set) \<in> appr1_rel" "(Ci, C) \<in> reducer_rel"
    and [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) D"
  unfolding reduce_spec1_def
  by autoref_monadic
concrete_definition reduce_spec1_impl for Ci Xi uses reduce_spec1_impl

lemma reduce_spec1_impl_refine[autoref_rules]:
  "(\<lambda>C x. nres_of (reduce_spec1_impl C x), reduce_spec1::_\<Rightarrow>'n eucl1 set\<Rightarrow>_) \<in>
      reducer_rel \<rightarrow> appr1_rel \<rightarrow> \<langle>appr1_rel\<rangle>nres_rel"
  if "DIM_precond TYPE((real, 'n::enum) vec) D"
  using reduce_spec1_impl.refine that
  by force

schematic_goal reduce_spec1e_impl:
  "(nres_of ?r, reduce_spec1e C X) \<in> \<langle>\<langle>appr1_rel\<rangle>scaleR2_rel\<rangle>nres_rel"
  if [autoref_rules]: "(Xi, X::'n eucl1 set) \<in> \<langle>appr1_rel\<rangle>scaleR2_rel" "(Ci, C) \<in> reducer_rel"
  and [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) D"
  unfolding reduce_spec1e_def
  including art
  by autoref_monadic
concrete_definition reduce_spec1e_impl for Ci Xi uses reduce_spec1e_impl

lemma reduce_spec1e_impl_refine[autoref_rules]:
  "(\<lambda>C x. nres_of (reduce_spec1e_impl C x), reduce_spec1e::_\<Rightarrow>'n eucl1 set\<Rightarrow>_) \<in>
      reducer_rel \<rightarrow> \<langle>appr1_rel\<rangle>scaleR2_rel \<rightarrow> \<langle>\<langle>appr1_rel\<rangle>scaleR2_rel\<rangle>nres_rel"
  if "DIM_precond TYPE((real, 'n::enum) vec) D"
  using reduce_spec1e_impl.refine that
  by force

lemma eq_spec_impl[autoref_rules]:
  "(\<lambda>a b. RETURN (a = b), eq_spec) \<in> A \<rightarrow> A \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  if "PREFER single_valued A"
  using that by (auto simp: nres_rel_def single_valued_def)

schematic_goal select_with_inter_impl:
  assumes [relator_props]: "single_valued A" "single_valued P"
  assumes [autoref_rules]: "(ci, c) \<in> clw_rel (\<langle>A, P\<rangle>inter_rel)" "(ai, a) \<in> clw_rel A"
  shows "(RETURN ?r, select_with_inter $ c $ a) \<in> \<langle>clw_rel (\<langle>A, P\<rangle>inter_rel)\<rangle>nres_rel"
  unfolding select_with_inter_def
  including art
  by (autoref_monadic (plain))
concrete_definition select_with_inter_impl for ci ai uses select_with_inter_impl
lemmas [autoref_rules] = select_with_inter_impl.refine[OF PREFER_sv_D PREFER_sv_D]

schematic_goal choose_step1e_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) D"
    "ncc_precond TYPE('n vec1)"
    "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules]: "(Xi, X::'n eucl1 set) \<in> appr1e_rel" "(hi, h) \<in> rnv_rel"
  shows "(nres_of ?r, choose_step1e $ X $ h) \<in> \<langle>rnv_rel \<times>\<^sub>r appr1_rel \<times>\<^sub>r appr_rel \<times>\<^sub>r appr1e_rel\<rangle>nres_rel"
  unfolding choose_step1e_def
  including art
  by autoref_monadic
concrete_definition choose_step1e_impl for Xi hi uses choose_step1e_impl
lemmas [autoref_rules] = choose_step1e_impl.refine

schematic_goal step_split_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules]: "(Xi, X::'n eucl1 set) \<in> appr1e_rel"
    and [autoref_rules]: "(roptnsi, roptns) \<in> reach_optns_rel"
  shows "(nres_of (?f), step_split $ roptns $ X)\<in>\<langle>clw_rel appr1e_rel\<rangle>nres_rel"
  using assms
  unfolding step_split_def[abs_def]
  including art
  by autoref_monadic
concrete_definition step_split_impl for roptnsi Xi uses step_split_impl
lemmas [autoref_rules] = step_split_impl.refine

schematic_goal width_spec_appr1_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules]: "(Xi, X::'n eucl1 set) \<in> appr1_rel"
  shows "(?r, width_spec_appr1 X) \<in> \<langle>rnv_rel\<rangle>nres_rel"
  unfolding width_spec_appr1_def
  by autoref_monadic
concrete_definition width_spec_appr1_impl for Xi uses width_spec_appr1_impl
lemma width_spec_appr1_impl_refine[autoref_rules]:
  "DIM_precond TYPE((real, 'a::enum) vec) D \<Longrightarrow>
  (\<lambda>X. RETURN (width_spec_appr1_impl X), width_spec_appr1::'a eucl1 set \<Rightarrow> real nres) \<in> appr1_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  using width_spec_appr1_impl.refine by force

schematic_goal split_under_threshold_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) D"
  assumes [autoref_rules]: "(ti, t) \<in> reach_optns_rel" "(thi, th) \<in> rnv_rel" "(Xi, X) \<in> clw_rel (\<langle>appr1_rel\<rangle>scaleR2_rel)"
  shows "(nres_of (?x dres), split_under_threshold $ t $ th $ (X::'n eucl1 set)) \<in> \<langle>clw_rel (\<langle>appr1_rel\<rangle>scaleR2_rel)\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding split_under_threshold_def
  including art
  by autoref_monadic
concrete_definition split_under_threshold_impl for ti thi Xi uses split_under_threshold_impl
lemmas [autoref_rules] = split_under_threshold_impl.refine

schematic_goal pre_intersection_step_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]:
    "(Xi, X::'n eucl1 set) \<in> appr1e_rel"
    "(hi, (h::real)) \<in> rnv_rel"
    and [autoref_rules]: "(roptnsi, roptns::'b reach_options) \<in> reach_optns_rel"
  shows "(nres_of ?r, pre_intersection_step $ roptns $ X $ h) \<in>
    \<langle>clw_rel (iinfo_rel appr1e_rel) \<times>\<^sub>r clw_rel appr_rel \<times>\<^sub>r clw_rel (iinfo_rel appr1e_rel)\<rangle>nres_rel"
  unfolding pre_intersection_step_def
  including art
  by autoref_monadic
concrete_definition pre_intersection_step_impl for roptnsi Xi hi uses pre_intersection_step_impl
lemmas [autoref_rules] = pre_intersection_step_impl.refine

lemma with_infos_autoref[autoref_rules]:
  "((\<lambda>ri ai. nres_of (if ri = [] then dSUCCEED else dRETURN (List.product ri ai))), with_coll_infos) \<in>
    clw_rel R \<rightarrow> clw_rel A \<rightarrow> \<langle>clw_rel (\<langle>R, A\<rangle>info_rel)\<rangle>nres_rel"
  if "PREFER single_valued R" "PREFER single_valued A"
  using that
  by (force simp: relcomp_unfold nres_rel_def info_rel_br list_wset_rel_def Union_rel_br
      Id_arbitrary_interface_def RETURN_RES_refine_iff set_rel_br
      elim!: single_valued_as_brE
      intro!: brI dest!: brD
      split: if_splits)

schematic_goal subset_spec_plane_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a) D"
  assumes [autoref_rules]: "(Xi, X::'a::executable_euclidean_space set) \<in> lvivl_rel" "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(nres_of ?R, subset_spec_plane $ X $ sctn) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding subset_spec_plane_def
  by autoref_monadic
concrete_definition subset_spec_plane_impl for Xi sctni uses subset_spec_plane_impl
lemmas [autoref_rules] = subset_spec_plane_impl.refine

schematic_goal op_eventually_within_sctn_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(Xi, X::'a set) \<in> appr_rel" "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel" "(Si, S) \<in> lvivl_rel"
  shows "(nres_of ?R, op_eventually_within_sctn $ X $ sctn $ S) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding op_eventually_within_sctn_def
  including art
  by autoref_monadic

concrete_definition op_eventually_within_sctn_impl for Xi sctni Si uses op_eventually_within_sctn_impl
lemmas [autoref_rules] = op_eventually_within_sctn_impl.refine

schematic_goal nonzero_component_within_impl:
  "(nres_of ?r, nonzero_component_within $ ivl $ sctn $ (PDP::'n eucl1 set)) \<in> \<langle>bool_rel\<rangle>nres_rel"
  if [autoref_rules]:
    "(ivli, ivl) \<in> lvivl_rel"
    "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
    "(PDPi, PDP) \<in> appr1_rel"
    and [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) D"
  unfolding nonzero_component_within_def
  including art
  by autoref_monadic

concrete_definition nonzero_component_within_impl uses nonzero_component_within_impl
lemmas [autoref_rules] = nonzero_component_within_impl.refine

schematic_goal disjoints_spec_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules]: "(Xi, (X::'n::enum rvec set)) \<in> clw_rel appr_rel" "(Yi, (Y::'n rvec set)) \<in> clw_rel lvivl_rel"
  shows "(nres_of ?f, disjoints_spec $ X $ Y) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding disjoints_spec_def
  including art
  by autoref_monadic
concrete_definition disjoints_spec_impl for Xi Yi uses disjoints_spec_impl
lemmas [autoref_rules] = disjoints_spec_impl.refine

schematic_goal do_intersection_body_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(hi, h) \<in> rnv_rel"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> clw_rel lvivl_rel"
    and civl[autoref_rules]: "(ivli, ivl::'n rvec set) \<in> lvivl_rel"
    and csctns[autoref_rules]: "(sctni, sctn::'n rvec sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  and [autoref_rules]: "(STATEi, STATE) \<in> intersection_STATE_rel"
  notes [intro, simp] = list_set_rel_finiteD closed_ivl_rel[OF civl]
  shows "(nres_of ?f, do_intersection_body guards ivl sctn h STATE) \<in> \<langle>intersection_STATE_rel\<rangle>nres_rel"
  unfolding do_intersection_body_def
  by autoref_monadic

concrete_definition do_intersection_body_impl for guardsi ivli sctni hi STATEi uses do_intersection_body_impl
lemma do_intersection_body_impl_refine[autoref_rules]:
  "(\<lambda>guardsi ivli sctni hi STATEi. nres_of (do_intersection_body_impl guardsi ivli sctni hi STATEi),
  do_intersection_body::'a rvec set\<Rightarrow>_)
  \<in> clw_rel lvivl_rel \<rightarrow> \<langle>lv_rel\<rangle>ivl_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> rnv_rel \<rightarrow>
  intersection_STATE_rel \<rightarrow> \<langle>intersection_STATE_rel\<rangle>nres_rel"
  if "DIM_precond TYPE((real, 'a::enum) vec) D" "var.ncc_precond TYPE((real, 'a) vec)"
    "var.ncc_precond TYPE((real, 'a) vec \<times> ((real, 'a) vec, 'a) vec)"
  by (intro fun_relI do_intersection_body_impl.refine[OF that])

schematic_goal do_intersection_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(Xi, X) \<in> appr1_rel" "(hi, h) \<in> rnv_rel"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> clw_rel (\<langle>lvivl_rel, \<langle>lv_rel\<rangle>plane_rel\<rangle>inter_rel)"
    and civl[autoref_rules]: "(ivli, ivl::'n rvec set) \<in> lvivl_rel"
    and csctns[autoref_rules]: "(sctni, sctn::'n rvec sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  notes [intro, simp] = list_set_rel_finiteD closed_ivl_rel[OF civl]
  shows "(nres_of ?f, do_intersection guards ivl sctn (X::'n eucl1 set) h)\<in>
    \<langle>bool_rel \<times>\<^sub>r clw_rel appr1_rel \<times>\<^sub>r clw_rel appr1_rel \<times>\<^sub>r
      clw_rel (\<langle>sappr_rel, \<langle>lv_rel\<rangle>sbelows_rel\<rangle>inter_rel)\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding do_intersection_def
  including art
  by autoref_monadic
concrete_definition do_intersection_impl for guardsi ivli sctni Xi hi uses do_intersection_impl

lemma do_intersection_impl_refine[autoref_rules]:
  "(\<lambda>guardsi ivli  sctni Xi hi. nres_of (do_intersection_impl guardsi ivli sctni Xi hi),
 do_intersection::'a rvec set\<Rightarrow>_)
\<in> clw_rel
    (\<langle>lvivl_rel,
     \<langle>lv_rel\<rangle>plane_rel\<rangle>inter_rel) \<rightarrow>
  \<langle>lv_rel\<rangle>ivl_rel \<rightarrow>
  \<langle>lv_rel\<rangle>sctn_rel \<rightarrow>
  appr1_rel \<rightarrow> rnv_rel \<rightarrow>
  \<langle>bool_rel \<times>\<^sub>r clw_rel appr1_rel \<times>\<^sub>r clw_rel appr1_rel \<times>\<^sub>r
   clw_rel
    (\<langle>sappr_rel,
     \<langle>lv_rel\<rangle>sbelows_rel\<rangle>inter_rel)\<rangle>nres_rel"
  if "DIM_precond TYPE((real, 'a::enum) vec) D" "var.ncc_precond TYPE((real, 'a) vec)"
    "var.ncc_precond TYPE((real, 'a) vec \<times> ((real, 'a) vec, 'a) vec)"
  by (intro fun_relI do_intersection_impl.refine[OF that])

schematic_goal tolerate_error_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules]: "(Yi, Y::'n eucl1 set) \<in> appr1e_rel"
  assumes [autoref_rules]: "(Ei, E) \<in> appr1_rel"
  shows "(nres_of ?r, tolerate_error Y E) \<in> \<langle>bool_rel \<times>\<^sub>r rnv_rel\<rangle>nres_rel"
  unfolding tolerate_error_def
  including art
  by autoref_monadic

concrete_definition tolerate_error_impl for Yi Ei uses tolerate_error_impl
lemma tolerate_error_refine[autoref_rules]:
  "DIM_precond TYPE((real, 'n::enum) vec) D \<Longrightarrow>
    ((\<lambda>Yi Ei. nres_of (tolerate_error_impl Yi Ei)), tolerate_error::'n eucl1 set \<Rightarrow> _)
    \<in> appr1e_rel \<rightarrow> appr1_rel \<rightarrow> \<langle>bool_rel \<times>\<^sub>r rnv_rel\<rangle>nres_rel"
  using tolerate_error_impl.refine
  by force

lemma [autoref_rules]: "(adapt_stepsize_fa, adapt_stepsize_fa) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> Id"
  by auto

schematic_goal step_adapt_time_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]:
    "(hi, h) \<in> rnv_rel"
    "(Xi, X::'n eucl1 set) \<in> (appr1e_rel)"
  shows "(nres_of ?f, step_adapt_time $ X $ h)\<in>\<langle>rnv_rel \<times>\<^sub>r appr_rel \<times>\<^sub>r appr1e_rel \<times>\<^sub>r rnv_rel\<rangle>nres_rel"
  unfolding step_adapt_time_def[abs_def]
  including art
  by autoref_monadic
concrete_definition step_adapt_time_impl for Xi hi uses step_adapt_time_impl
lemmas [autoref_rules] = step_adapt_time_impl.refine


schematic_goal resolve_step_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]:
    "(hi, h) \<in> rnv_rel"
    "(Xi, X::'n eucl1 set) \<in> (appr1e_rel)"
    "(roptnsi, roptns::'b reach_options) \<in> reach_optns_rel"
  shows "(nres_of ?f, resolve_step $ roptns $ X $ h)\<in>\<langle>rnv_rel \<times>\<^sub>r clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r rnv_rel\<rangle>nres_rel"
  unfolding resolve_step_def[abs_def]
  including art
  by autoref_monadic
concrete_definition resolve_step_impl for roptnsi Xi hi uses resolve_step_impl
lemmas [autoref_rules] = resolve_step_impl.refine

schematic_goal reach_cont_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]:
    "(XSi, XS) \<in> clw_rel appr1e_rel"
    "(guardsi, guards::'n rvec set) \<in> clw_rel (iplane_rel lvivl_rel)"
    and [autoref_rules]: "(roptnsi, roptns::'b reach_options) \<in> reach_optns_rel"
  shows "(nres_of (?f::?'f dres), reach_cont $ roptns $ guards $ XS)\<in>?R"
  unfolding autoref_tag_defs
  unfolding reach_cont_def
  including art
  by autoref_monadic
concrete_definition reach_cont_impl for guardsi XSi uses reach_cont_impl
lemmas [autoref_rules] = reach_cont_impl.refine

lemma reach_cont_ho[autoref_rules]:
  "DIM_precond TYPE((real, 'a::enum) vec) D \<Longrightarrow>
  var.ncc_precond TYPE((real, 'a) vec) \<Longrightarrow>
  var.ncc_precond TYPE((real, 'a) vec \<times> ((real, 'a) vec, 'a) vec) \<Longrightarrow>
  (\<lambda>roptnsi guardsi XSi. nres_of (reach_cont_impl roptnsi guardsi XSi),
   reach_cont::_\<Rightarrow>'a rvec set \<Rightarrow> _)
  \<in> reach_optns_rel \<rightarrow> clw_rel
      (\<langle>\<langle>lv_rel\<rangle>ivl_rel,
       \<langle>lv_rel\<rangle>plane_rel\<rangle>inter_rel) \<rightarrow>
    clw_rel appr1e_rel \<rightarrow>
    \<langle>clw_rel sappr_rel \<times>\<^sub>r
     clw_rel
      (\<langle>\<langle>\<langle>lv_rel\<rangle>ivl_rel,
       \<langle>lv_rel:: (real list \<times> 'a rvec) set\<rangle>plane_rel\<rangle>inter_rel,
       \<langle>rnv_rel, appr1e_rel\<rangle>info_rel\<rangle>info_rel)\<rangle>nres_rel"
  using reach_cont_impl.refine by fastforce

schematic_goal reach_cont_par_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]:
    "(XSi, XS) \<in> clw_rel appr1e_rel"
    "(guardsi, guards::'n rvec set) \<in> clw_rel (iplane_rel lvivl_rel)"
    and [autoref_rules]: "(roptnsi, roptns::'b reach_options) \<in> reach_optns_rel"
  shows "(nres_of (?f::?'f dres), reach_cont_par $ roptns $ guards $ XS)\<in>?R"
  unfolding autoref_tag_defs
  unfolding reach_cont_par_def
  including art
  by autoref_monadic
concrete_definition reach_cont_par_impl for roptnsi guardsi XSi uses reach_cont_par_impl
lemmas [autoref_rules] = reach_cont_par_impl.refine

schematic_goal subset_iplane_coll_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(xi, x::'a set) \<in> iplane_rel lvivl_rel"
  assumes [autoref_rules]: "(icsi, ics) \<in> clw_rel (iplane_rel lvivl_rel)"
  shows "(nres_of ?r, subset_iplane_coll $ x $ ics) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding subset_iplane_coll_def
  including art
  by autoref_monadic
concrete_definition subset_iplane_coll_impl uses subset_iplane_coll_impl
lemmas [autoref_rules] = subset_iplane_coll_impl.refine


schematic_goal subsets_iplane_coll_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(xi, x::'a set set) \<in> \<langle>iplane_rel lvivl_rel\<rangle>list_wset_rel"
  assumes [autoref_rules]: "(icsi, ics) \<in> clw_rel (iplane_rel lvivl_rel)"
  shows "(nres_of ?r, subsets_iplane_coll $ x $ ics) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding subsets_iplane_coll_def
  including art
  by autoref_monadic
concrete_definition subsets_iplane_coll_impl uses subsets_iplane_coll_impl
lemmas [autoref_rules] = subsets_iplane_coll_impl.refine


schematic_goal symstart_coll_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(XSi, XS::'n eucl1 set) \<in> clw_rel appr1e_rel"
  assumes [autoref_rules]: "(symstarti, symstart::'n eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set)nres)
    \<in> appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  assumes [unfolded autoref_tag_defs, refine_transfer]: "\<And>X. TRANSFER (nres_of (symstartd X) \<le> symstarti X)"
  shows "(nres_of ?r, symstart_coll $ symstart $ XS) \<in> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  unfolding symstart_coll_def
  including art
  by autoref_monadic
concrete_definition symstart_coll_impl for symstartd XSi uses symstart_coll_impl
lemmas [autoref_rules] = symstart_coll_impl.refine

schematic_goal reach_cont_symstart_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]:
    "(XSi, XS::'n eucl1 set) \<in> clw_rel appr1e_rel"
    "(guardsi, guards::'n rvec set) \<in> clw_rel (iplane_rel lvivl_rel)"
    "(roptnsi, roptns) \<in> reach_optns_rel"
  assumes [autoref_rules]: "(symstarti, symstart::'n eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set)nres)
    \<in> appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  assumes [unfolded autoref_tag_defs, refine_transfer]: "\<And>X. TRANSFER (nres_of (symstartd X) \<le> symstarti X)"
  shows "(nres_of (?r), reach_cont_symstart $ roptns $ symstart $ guards $ XS) \<in>
  \<langle>clw_rel sappr_rel \<times>\<^sub>r
    clw_rel (\<langle>iplane_rel lvivl_rel::(_ \<times> 'n rvec set)set, iinfo_rel appr1e_rel\<rangle>info_rel)\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding reach_cont_symstart_def Let_def
  including art
  by autoref_monadic
concrete_definition reach_cont_symstart_impl for roptnsi symstartd XSi uses reach_cont_symstart_impl
lemmas [autoref_rules] = reach_cont_symstart_impl.refine

lemma sv_reach_conts_impl_aux:
  "single_valued (clw_rel (iinfo_rel appr1e_rel))" by (auto intro!: relator_props)

schematic_goal reach_conts_impl:
  assumes [autoref_rules]: "(symstarti, symstart::'n eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set)nres)
    \<in> appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]:
    "(XSi, XS) \<in> clw_rel appr1e_rel"
    "(guardsi, guards::'n rvec set) \<in> clw_rel (iplane_rel lvivl_rel)"
    and [autoref_rules]: "(roptnsi, roptns) \<in> reach_optns_rel"
  notes [simp] = list_wset_rel_finite[OF sv_reach_conts_impl_aux]
    assumes "(trapi, trap) \<in> ghost_rel"
  assumes [unfolded autoref_tag_defs, refine_transfer]: "\<And>X. TRANSFER (nres_of (symstartd X) \<le> symstarti X)"
  shows "(nres_of (?f::?'f dres), reach_conts $ roptns $ symstart $ trap $ guards $ XS)\<in>?R"
  unfolding autoref_tag_defs
  unfolding reach_conts_def
  including art
  by autoref_monadic
concrete_definition reach_conts_impl for guardsi XSi uses reach_conts_impl
lemmas [autoref_rules] = reach_conts_impl.refine

lemma get_sctns_autoref[autoref_rules]:
  "(\<lambda>x. RETURN x, get_sctns) \<in> \<langle>R\<rangle>halfspaces_rel \<rightarrow> \<langle>\<langle>\<langle>R\<rangle>sctn_rel\<rangle>list_set_rel\<rangle>nres_rel"
  by (auto simp: get_sctns_def nres_rel_def halfspaces_rel_def br_def intro!: RETURN_SPEC_refine)

schematic_goal leaves_halfspace_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes nccp[autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  notes [simp] = ncc_precondD[OF nccp]
  assumes [autoref_rules]: "(Si, S) \<in> \<langle>lv_rel\<rangle>halfspaces_rel"
  assumes [autoref_rules]: "(Xi, X::'n rvec set) \<in> clw_rel appr_rel"
  shows "(nres_of ?r, leaves_halfspace $ S $ X) \<in> \<langle>\<langle>\<langle>lv_rel\<rangle>sctn_rel\<rangle>option_rel\<rangle>nres_rel"
  unfolding leaves_halfspace_def
  including art
  by autoref_monadic
concrete_definition leaves_halfspace_impl for Si Xi uses leaves_halfspace_impl
lemmas [autoref_rules] = leaves_halfspace_impl.refine

schematic_goal poincare_start_on_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes ncc2[autoref_rules_raw]: "ncc_precond TYPE('n::enum rvec)"
  assumes ncc2[autoref_rules_raw]: "var.ncc_precond TYPE('n::enum vec1)"
  assumes [autoref_rules]:
    "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
    "(guardsi, guards) \<in> clw_rel lvivl_rel"
    "(X0i, X0::'n eucl1 set) \<in> clw_rel (appr1e_rel)"
  shows "(nres_of (?f), poincare_start_on $ guards $ sctn $ X0) \<in>
      \<langle>clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding poincare_start_on_def
  including art
  by autoref_monadic
concrete_definition poincare_start_on_impl for guardsi sctni X0i uses poincare_start_on_impl
lemmas [autoref_rules] = poincare_start_on_impl.refine


lemma isets_of_iivls[autoref_rules]:
  assumes "PREFER single_valued A"
  assumes le[THEN GEN_OP_D, param_fo]: "GEN_OP le (\<le>) ((lv_rel::(_ \<times> 'a::executable_euclidean_space)set) \<rightarrow> lv_rel \<rightarrow> bool_rel)"
  shows "(\<lambda>xs. map (\<lambda>((i, s), x). (appr_of_ivl i s, x)) [((i,s), x) \<leftarrow> xs. le i s], isets_of_iivls::_\<Rightarrow>'a set)
    \<in> clw_rel (\<langle>lvivl_rel, A\<rangle>inter_rel) \<rightarrow> clw_rel (\<langle>appr_rel, A\<rangle>inter_rel)"
  apply (rule fun_relI)
  using assms
  apply (auto elim!: single_valued_as_brE)
  unfolding appr_rel_br ivl_rel_br clw_rel_br lvivl_rel_br inter_rel_br
  apply (auto simp: br_def set_of_ivl_def)
  subgoal for a b c d e f g
    apply (rule exI[where x=e])
    apply (rule exI[where x=f])
    apply (rule exI[where x=g])
    apply (rule conjI)
    apply (assumption)
    apply (rule conjI)
    subgoal
      using transfer_operations1[where 'a='a, of "eucl_of_list e" "eucl_of_list f" e f]
        le[of e _ f _, OF lv_relI lv_relI]
      by (auto simp: appr_rel_br br_def lvivl_rel_br set_of_ivl_def lv_rel_def)
    subgoal
      apply (drule bspec, assumption)
      using transfer_operations1[where 'a='a, of "eucl_of_list e" "eucl_of_list f" e f]
        le[of e _ f _, OF lv_relI lv_relI]
      apply (auto simp: appr_rel_br br_def lvivl_rel_br set_of_ivl_def lv_rel_def)
      using atLeastAtMost_iff apply blast
      apply (drule order_trans)
       apply assumption apply simp
      done
    done
  subgoal for a b c d e f g
    apply (drule bspec, assumption)
    using transfer_operations1[where 'a='a, of "eucl_of_list d" "eucl_of_list e" d e]
      le[of d _ e _, OF lv_relI lv_relI]
    by (auto simp: appr_rel_br br_def lvivl_rel_br set_of_ivl_def lv_rel_def intro!: bexI)
  subgoal for a b c d e f
    apply (drule bspec, assumption)
    using transfer_operations1[where 'a='a, of "eucl_of_list d" "eucl_of_list e" d e]
      le[of d _ e _, OF lv_relI lv_relI]
    by (auto simp: appr_rel_br br_def lvivl_rel_br set_of_ivl_def lv_rel_def intro!: bexI)
  done

lemma [autoref_op_pat]: "X \<times> UNIV \<equiv> OP op_times_UNIV_coll $ X" by simp

lemma op_times_UNIV_coll_impl[autoref_rules]: "(map (\<lambda>x. (x, None)), op_times_UNIV_coll) \<in> clw_rel appr_rel \<rightarrow> clw_rel appr1_rel"
  apply (rule lift_clw_rel_map)
     apply (rule relator_props)
    apply (rule relator_props)
  unfolding op_times_UNIV_coll_def op_times_UNIV_def[symmetric]
   apply (rule op_times_UNIV_impl)
  by auto

lemma [autoref_op_pat]: "X \<inter> Y \<times> UNIV \<equiv> OP op_inter_fst $ X $ Y"
  by auto

lemma fst_imageIcc:
  "fst ` {a::'a::ordered_euclidean_space\<times>'c::ordered_euclidean_space .. b} =
  (if a \<le> b then {fst a .. fst b} else {})"
  by (auto intro!: simp: less_eq_prod_def)

lemma
  interval_inter_times_UNIVI:
  assumes "{fst a .. fst b} \<inter> {c .. d} = {fst e .. fst f}"
  assumes "{snd a .. snd b} = {snd e .. snd f}"
  shows "{a::('a::ordered_euclidean_space \<times> 'c::ordered_euclidean_space) .. b} \<inter>
      ({c .. d} \<times> UNIV) = {e .. f}"
  using assms
  by (cases a; cases b; cases e; cases f) (auto simp: subset_iff set_eq_iff)

lemma op_inter_fst_impl:
  assumes "DIM_precond TYPE('n::enum rvec) D"
  assumes "GEN_OP intr (op_inter_ivl::'n rvec set\<Rightarrow>_) (lvivl_rel \<rightarrow> lvivl_rel \<rightarrow> lvivl_rel)"
  assumes "GEN_OP le   ((\<le>) ::'n vec1 \<Rightarrow>_) (lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel)"
  shows "(\<lambda>x y.
    if le (fst x) (snd x) then
    case (intr (pairself (take D) x) y, pairself (drop D) x) of
      ((i, s), j, t) \<Rightarrow> (i @ j, s @ t)
    else x,
      op_inter_fst::('n vec1) set \<Rightarrow> 'n rvec set \<Rightarrow> ('n vec1) set) \<in> lvivl_rel \<rightarrow> lvivl_rel \<rightarrow> lvivl_rel"
proof (auto simp: split: prod.splits, goal_cases)
  case (1 a b c d e f g h)
  from 1 assms(1) assms(3)[THEN GEN_OP_D, param_fo, OF lv_relI lv_relI, of a b]
  have "((take D a, take D b), fst ` c) \<in> \<langle>lv_rel\<rangle>ivl_rel"
    apply (auto simp: lv_rel_def ivl_rel_def dest!: brD)
    apply (rule relcompI)
     apply (rule prod_relI)
      apply (rule brI)
       apply (rule refl)
      apply (simp;fail)
     apply (rule brI)
      apply (rule refl)
     apply (simp;fail)
    apply (rule brI)
     apply (simp add: set_of_ivl_def fst_imageIcc)
    by (auto simp: eucl_of_list_prod)
  from assms(2)[THEN GEN_OP_D, param_fo, OF this 1(2)] 1 assms(1)
  show ?case
    apply (auto simp: lv_rel_def ivl_rel_def dest!: brD)
    apply (rule relcompI)
     apply (rule prod_relI)
      apply (rule brI)
       apply (rule refl)
      apply (simp;fail)
     apply (rule brI)
      apply (rule refl)
     apply (simp;fail)
    apply (rule brI)
     apply (simp add: set_of_ivl_def fst_imageIcc)
     defer apply (simp; fail)
    apply (cases "(eucl_of_list (take CARD('n) a)::'n rvec) \<le> eucl_of_list (take CARD('n) b) \<and>
        (eucl_of_list (drop CARD('n) a)::((real, 'n) vec, 'n) vec) \<le> eucl_of_list (drop CARD('n) b)")
    subgoal apply simp
      apply (rule interval_inter_times_UNIVI)
      by (auto simp: eucl_of_list_prod)
    subgoal by (auto simp add: subset_iff eucl_of_list_prod)
    done
next
  case (2 a b c d e f g h)
  from assms(3)[THEN GEN_OP_D, param_fo, OF lv_relI lv_relI, of a b] assms(1) 2
  show ?case
    apply (auto simp: lv_rel_def ivl_rel_def dest!: brD)
    apply (rule relcompI)
     apply (rule prod_relI)
      apply (rule brI)
       apply (rule refl)
      apply (simp;fail)
     apply (rule brI)
      apply (rule refl)
     apply (simp;fail)
     apply (rule brI)
      apply (simp add: set_of_ivl_def fst_imageIcc)
    apply (simp; fail)
    done
qed

concrete_definition op_inter_fst_impl uses op_inter_fst_impl
lemmas [autoref_rules] = op_inter_fst_impl.refine

schematic_goal op_inter_fst_coll_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [THEN GEN_OP_D, autoref_rules]: "GEN_OP le ((\<le>) ::'n vec1 \<Rightarrow>_) (lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel)"
  assumes [autoref_rules]: "(XSi, XS::('n vec1) set) \<in> clw_rel lvivl_rel"
    "(Yi, Y::'n rvec set) \<in> lvivl_rel"
  shows "(nres_of ?r, op_inter_fst_coll XS Y) \<in> \<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding op_inter_fst_coll_def
  by autoref_monadic
concrete_definition op_inter_fst_coll_impl uses op_inter_fst_coll_impl
lemma op_inter_fst_coll_impl_refine[autoref_rules]:
  "DIM_precond TYPE((real, 'a::enum) vec) D \<Longrightarrow>
  GEN_OP le ((\<le>) ::'a vec1 \<Rightarrow> _) (lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel) \<Longrightarrow>
  (\<lambda>XSi Yi. nres_of (op_inter_fst_coll_impl le XSi Yi), op_inter_fst_coll::'a vec1 set\<Rightarrow> _)
  \<in> clw_rel (\<langle>lv_rel\<rangle>ivl_rel) \<rightarrow> \<langle>lv_rel\<rangle>ivl_rel \<rightarrow> \<langle>clw_rel (\<langle>lv_rel\<rangle>ivl_rel)\<rangle>nres_rel"
  using op_inter_fst_coll_impl.refine[where 'a='a, of le]
  by force

schematic_goal scaleRe_ivl_coll_impl:
  assumes [relator_props]: "single_valued A"
  assumes [autoref_rules]: "(li, l) \<in> ereal_rel" "(ui, u) \<in> ereal_rel" "(Xi, X) \<in> clw_rel A"
  shows "(nres_of ?r, scaleRe_ivl_coll_spec l u X) \<in> \<langle>clw_rel (\<langle>A\<rangle>scaleR2_rel)\<rangle>nres_rel"
  unfolding scaleRe_ivl_coll_spec_def
  including art
  by autoref_monadic
concrete_definition scaleRe_ivl_coll_impl uses scaleRe_ivl_coll_impl
lemma scaleRe_ivl_coll_impl_refine[autoref_rules]:
  "PREFER single_valued A \<Longrightarrow>
    (\<lambda>li ui Xi. nres_of (scaleRe_ivl_coll_impl li ui Xi), scaleRe_ivl_coll_spec)
    \<in> ereal_rel \<rightarrow> ereal_rel \<rightarrow> clw_rel A \<rightarrow> \<langle>clw_rel (\<langle>A\<rangle>scaleR2_rel)\<rangle>nres_rel"
  using scaleRe_ivl_coll_impl.refine by force

schematic_goal do_intersection_core_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) D"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(Xi, X::'n eucl1 set) \<in> iinfo_rel appr1e_rel"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> clw_rel (iplane_rel lvivl_rel)"
    and csctns[autoref_rules]: "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
    and csctns[autoref_rules]: "(ivli, ivl) \<in> lvivl_rel"
  notes [simp] = list_set_rel_finiteD
  shows "(nres_of ?f, do_intersection_core $ guards $ ivl $ sctn $ X) \<in>
      \<langle>clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel (isbelows_rel sappr_rel) \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  unfolding do_intersection_core_def[abs_def]
  including art
  by autoref_monadic
concrete_definition do_intersection_core_impl for guardsi ivli sctni Xi uses do_intersection_core_impl

lemma do_intersection_core_impl_refine[autoref_rules]:
  "DIM_precond TYPE((real, 'a::enum) vec) D \<Longrightarrow>
  var.ncc_precond TYPE((real, 'a) vec) \<Longrightarrow>
  var.ncc_precond TYPE((real, 'a) vec \<times> ((real, 'a) vec, 'a) vec) \<Longrightarrow>
  (\<lambda>guardsi ivli sctni Xi.
    nres_of (do_intersection_core_impl guardsi ivli sctni Xi), do_intersection_core::'a rvec set \<Rightarrow> _)
  \<in>  clw_rel (\<langle>\<langle>lv_rel\<rangle>ivl_rel, \<langle>lv_rel\<rangle>plane_rel\<rangle>inter_rel) \<rightarrow>
  \<langle>lv_rel\<rangle>ivl_rel \<rightarrow>
  \<langle>lv_rel\<rangle>sctn_rel \<rightarrow>
   \<langle>rnv_rel, appr1e_rel\<rangle>info_rel \<rightarrow>
  \<langle>clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel (\<langle>sappr_rel, \<langle>lv_rel\<rangle>sbelows_rel\<rangle>inter_rel) \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  using do_intersection_core_impl.refine[where 'a='a] by force

lemma finite_ra1eicacacslsbicae1lw: "(xc, x'c) \<in> \<langle>\<langle>rnv_rel, appr1e_rel\<rangle>info_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel
           (\<langle>sappr_rel,
            \<langle>lv_rel\<rangle>sbelows_rel\<rangle>inter_rel) \<times>\<^sub>r
          clw_rel appr1e_rel\<rangle>list_wset_rel \<Longrightarrow> finite x'c"
  for x'c::"('n::enum eucl1 set * 'n eucl1 set * 'n eucl1 set * 'n rvec set * 'n eucl1 set) set"
  apply (rule list_wset_rel_finite)
  by (auto intro!: relator_props)

schematic_goal do_intersection_coll_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) D"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(Xi, X::'n eucl1 set) \<in> clw_rel (iinfo_rel appr1e_rel)"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> clw_rel (iplane_rel lvivl_rel)"
    and csctns[autoref_rules]: "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
    and csctns[autoref_rules]: "(ivli, ivl) \<in> lvivl_rel"
  notes [simp] = finite_ra1eicacacslsbicae1lw[where 'n='n]
  shows "(nres_of ?f, do_intersection_coll $ guards $ ivl $ sctn $ X) \<in>
      \<langle>clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel (isbelows_rel sappr_rel) \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  unfolding do_intersection_coll_def[abs_def]
  including art
  by autoref_monadic
concrete_definition do_intersection_coll_impl for guardsi ivli sctni Xi uses do_intersection_coll_impl
lemmas [autoref_rules] = do_intersection_coll_impl.refine

schematic_goal op_enlarge_ivl_sctn_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(ivli, ivl::'a set) \<in> lvivl_rel" "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel" "(di, d) \<in> rnv_rel"
  shows "(nres_of ?R, op_enlarge_ivl_sctn $ ivl $ sctn $ d) \<in> \<langle>lvivl_rel\<rangle>nres_rel"
  unfolding op_enlarge_ivl_sctn_def
  including art
  by autoref_monadic
concrete_definition op_enlarge_ivl_sctn_impl for ivli sctni di uses op_enlarge_ivl_sctn_impl
lemmas [autoref_rules] = op_enlarge_ivl_sctn_impl.refine

lemma list_wset_autoref_delete[autoref_rules]:
  assumes "PREFER single_valued R"
  assumes "GEN_OP eq (=) (R \<rightarrow> R \<rightarrow> bool_rel)"
  shows "(\<lambda>y xs. [x\<leftarrow>xs. \<not>eq y x], op_set_delete) \<in> R \<rightarrow> \<langle>R\<rangle>list_wset_rel \<rightarrow> \<langle>R\<rangle>list_wset_rel"
  using assms
  apply (auto simp: list_wset_rel_def dest!: brD elim!: single_valued_as_brE)
  apply (rule relcompI)
   apply (rule brI)
    apply (rule refl)
   apply auto
  apply (auto simp: set_rel_br)
  apply (rule brI)
   apply (auto dest!: brD dest: fun_relD)
   apply (auto simp: image_iff dest: fun_relD intro: brI)
  subgoal for a b c d e
    apply (drule spec[where x=e])
    apply auto
    apply (drule fun_relD)
     apply (rule brI[where c="c"])
      apply (rule refl)
     apply assumption
    apply (drule bspec, assumption)
    apply (drule fun_relD)
     apply (rule brI[where c="e"])
      apply (rule refl)
     apply assumption
    apply auto
    done
  done


lemma lv_rel_le[autoref_rules]: "(list_all2 (\<lambda>x y. x < y), eucl_less) \<in> lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel"
  by (auto simp: lv_rel_def br_def eucl_less_def[where 'a='a] eucl_of_list_inner list_all2_conv_all_nth
      index_nth_id)
     (metis distinct_Basis_list index_nth_id length_Basis_list nth_Basis_list_in_Basis)

schematic_goal resolve_ivlplanes_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(XSi, XS::('n rvec set \<times> 'n eucl1 set) set) \<in> \<langle>iplane_rel lvivl_rel \<times>\<^sub>r clw_rel (iinfo_rel appr1e_rel)\<rangle>list_wset_rel"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> clw_rel (iplane_rel lvivl_rel)"
    and osctns[autoref_rules]: "(ivlplanesi, ivlplanes) \<in> clw_rel (iplane_rel lvivl_rel)"
  notes [intro, simp] = list_set_rel_finiteD
  shows "(nres_of ?r, resolve_ivlplanes $ guards $ ivlplanes $ XS) \<in>
    \<langle>\<langle>clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel \<times>\<^sub>r clw_rel (isbelows_rel sappr_rel)\<rangle>list_wset_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding resolve_ivlplanes_def
  including art
  by autoref_monadic
concrete_definition resolve_ivlplanes_impl for guardsi ivlplanesi XSi uses resolve_ivlplanes_impl
lemmas [autoref_rules] = resolve_ivlplanes_impl.refine

schematic_goal poincare_onto_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(XSi, XS::'n eucl1 set) \<in> clw_rel appr1e_rel"
  assumes [autoref_rules]: "(CXSi, CXS::'n rvec set) \<in> clw_rel sappr_rel"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> clw_rel (iplane_rel lvivl_rel)"
    and osctns[autoref_rules]: "(ivlplanesi, ivlplanes) \<in> clw_rel (iplane_rel lvivl_rel)"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel"
  assumes [autoref_rules]: "((), trap) \<in> ghost_rel"
  assumes [autoref_rules]: "(symstarti, symstart::'n eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set)nres)
    \<in> appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  assumes [unfolded autoref_tag_defs, refine_transfer]: "\<And>X. TRANSFER (nres_of (symstartd X) \<le> symstarti X)"
  notes [intro, simp] = list_set_rel_finiteD
  shows "(nres_of ?r, poincare_onto $ ro $ symstart $ trap $ guards $ ivlplanes $ XS $ CXS) \<in>
    \<langle>\<langle>clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel
      \<times>\<^sub>r clw_rel (isbelows_rel sappr_rel) \<times>\<^sub>r clw_rel sappr_rel\<rangle>list_wset_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding poincare_onto_def
  including art
  by autoref_monadic
concrete_definition poincare_onto_impl for roi symstarti guardsi ivlplanesi XSi uses poincare_onto_impl
lemmas [autoref_rules] = poincare_onto_impl.refine

schematic_goal empty_remainders_impl:
  assumes [autoref_rules]:
    "(PSi, PS) \<in> \<langle>clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel
            \<times>\<^sub>r clw_rel (isbelows_rel sappr_rel) \<times>\<^sub>r clw_rel sappr_rel\<rangle>list_wset_rel"
  shows "(nres_of ?r, empty_remainders PS) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding empty_remainders_def
  including art
  by autoref_monadic
concrete_definition empty_remainders_impl uses empty_remainders_impl

lemma [autoref_rules]:
  "(\<lambda>x. nres_of (empty_remainders_impl x), empty_remainders) \<in>
   \<langle>clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel
            \<times>\<^sub>r clw_rel (isbelows_rel sappr_rel) \<times>\<^sub>r clw_rel sappr_rel\<rangle>list_wset_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using empty_remainders_impl.refine
  by force

lemma empty_trap_impl[autoref_rules]: "((), empty_trap) \<in> ghost_rel"
  by (auto intro!: ghost_relI)
lemma empty_symstart_impl[autoref_rules]:
  "((\<lambda>x. nres_of (dRETURN ([], [x]))), empty_symstart) \<in>
    appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  unfolding empty_symstart_def
  using mk_coll[unfolded autoref_tag_defs, OF sv_appr1e_rel[OF sv_appr1_rel], param_fo]
  by (auto intro!: nres_relI simp:)

schematic_goal poincare_onto_empty_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(XSi, XS::'n eucl1 set) \<in> clw_rel appr1e_rel"
  assumes [autoref_rules]: "(CXSi, CXS::'n rvec set) \<in> clw_rel sappr_rel"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> clw_rel (iplane_rel lvivl_rel)"
    and osctns[autoref_rules]: "(ivlplanesi, ivlplanes) \<in> clw_rel (iplane_rel lvivl_rel)"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel"
  notes [intro, simp] = list_set_rel_finiteD
  shows "(nres_of (?r), poincare_onto_empty $ ro $ guards $ ivlplanes $ XS $ CXS) \<in>
    \<langle>\<langle>clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel
      \<times>\<^sub>r clw_rel (isbelows_rel sappr_rel) \<times>\<^sub>r clw_rel sappr_rel\<rangle>list_wset_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding poincare_onto_empty_def
  including art
  apply (rule autoref_monadicI)
   apply (autoref phases: id_op rel_inf fix_rel)
  apply (simp only: autoref_tag_defs)
   apply (rule poincare_onto_impl.refine[unfolded autoref_tag_defs])
            apply fact+
     apply (rule ghost_relI)
    apply (rule empty_symstart_impl)
   apply refine_transfer
  apply refine_transfer
  done

concrete_definition poincare_onto_empty_impl for guardsi XSi CXSi uses poincare_onto_empty_impl
lemmas [autoref_rules] = poincare_onto_empty_impl.refine

lemma sv_thingy: "single_valued (clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          \<langle>lv_rel\<rangle>ivl_rel \<times>\<^sub>r
          \<langle>lv_rel\<rangle>sctn_rel \<times>\<^sub>r
          clw_rel
           (\<langle>sappr_rel,
            \<langle>lv_rel\<rangle>sbelows_rel\<rangle>inter_rel) \<times>\<^sub>r
          clw_rel sappr_rel)"
  by (intro relator_props)

schematic_goal poincare_onto2_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(symstarti, symstart::'n eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set)nres)
    \<in> appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  assumes [unfolded autoref_tag_defs, refine_transfer]: "\<And>X. TRANSFER (nres_of (symstartd X) \<le> symstarti X)"
  assumes [autoref_rules]: "(XSi, XS::'n eucl1 set) \<in> clw_rel appr1e_rel"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> clw_rel (iplane_rel lvivl_rel)"
    and osctns[autoref_rules]: "(ivlplanesi, ivlplanes) \<in> clw_rel (iplane_rel lvivl_rel)"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel"
  assumes [autoref_rules]: "((), trap) \<in> ghost_rel"
  notes [intro, simp] = list_set_rel_finiteD list_wset_rel_finite[OF sv_thingy]
  shows "(nres_of (?r), poincare_onto2 $ ro $ symstart $ trap $ guards $ ivlplanes $ XS) \<in>
    \<langle>\<langle>bool_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel \<times>\<^sub>r
      clw_rel (isbelows_rel sappr_rel) \<times>\<^sub>r clw_rel sappr_rel\<rangle>list_wset_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding poincare_onto2_def
    including art
  by autoref_monadic
concrete_definition poincare_onto2_impl for guardsi XSi uses poincare_onto2_impl
lemmas [autoref_rules] = poincare_onto2_impl.refine

lemma is_empty_autoref[autoref_rules]:
  assumes "GEN_OP le (\<le>) (R \<rightarrow> R \<rightarrow> bool_rel)"
  shows "(\<lambda>(a, b). \<not> le a b, is_empty) \<in> \<langle>R\<rangle>ivl_rel \<rightarrow> bool_rel"
  using assms
  by (fastforce simp: ivl_rel_def br_def set_of_ivl_def dest: fun_relD)

lemma inter_ivl_clw[autoref_rules]:\<comment> \<open>TODO: fix @{thm inter_ivl_clw}\<close>
  assumes sv[THEN PREFER_sv_D]: "PREFER single_valued A"
  assumes intr[THEN GEN_OP_D]: "GEN_OP intr op_inter_ivl (\<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A\<rangle>ivl_rel)"
  assumes "GEN_OP le (\<le>) (A \<rightarrow> A \<rightarrow> bool_rel)"
  shows "(\<lambda>xs y. filter_empty_ivls_impl le (map (intr y) xs), op_inter_ivl_coll) \<in> clw_rel (\<langle>A\<rangle>ivl_rel) \<rightarrow> (\<langle>A\<rangle>ivl_rel) \<rightarrow> clw_rel (\<langle>A\<rangle>ivl_rel)"
  apply safe
  subgoal premises prems
    using filter_empty_ivls[OF assms(1,3), param_fo, OF inter_ivl_clw_aux[OF sv intr[unfolded op_inter_ivl_def], param_fo, OF prems]]
    by simp
  done

lemma list_of_eucl_autoref[autoref_rules]: "(\<lambda>x. x, list_of_eucl) \<in> lv_rel \<rightarrow> \<langle>rnv_rel\<rangle>list_rel"
  by (auto simp: lv_rel_def br_def)

schematic_goal width_spec_ivl_impl:
  assumes [autoref_rules]: "(Mi, M) \<in> nat_rel" "(xi, x) \<in> lvivl_rel"
  shows "(RETURN ?r, width_spec_ivl M x) \<in> \<langle>rnv_rel\<rangle>nres_rel"
  unfolding width_spec_ivl_def
  including art
  by (autoref_monadic (plain))
concrete_definition width_spec_ivl_impl for Mi xi uses width_spec_ivl_impl

lemma width_spec_ivl_impl_refine[autoref_rules]:
  "(\<lambda>Mi xi. RETURN (width_spec_ivl_impl Mi xi), width_spec_ivl) \<in> nat_rel \<rightarrow> lvivl_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  using width_spec_ivl_impl.refine by fastforce
schematic_goal partition_ivl_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) E"
  assumes [autoref_rules]: "(xsi, xs::'a set)\<in> clw_rel lvivl_rel" "(roi, ro) \<in> reach_optns_rel"
  notes [autoref_rules] = autoref_parameters2
  shows "(nres_of (?f), partition_ivl $ ro $ xs)\<in>\<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding partition_ivl_def[abs_def]
  including art
  by autoref_monadic
concrete_definition partition_ivl_impl for roi xsi uses partition_ivl_impl
lemmas [autoref_rules] = partition_ivl_impl.refine

schematic_goal op_inter_fst_ivl_scaleR2_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [THEN GEN_OP_D, autoref_rules]: "GEN_OP le ((\<le>) ::'n vec1 \<Rightarrow>_) (lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel)"
  assumes [autoref_rules]: "(XSi, XS::('n::enum vec1) set) \<in> elvivl_rel"
    "(Yi, Y::'n rvec set) \<in> lvivl_rel"
  shows "(nres_of ?r, op_inter_fst_ivl_scaleR2 XS Y) \<in> \<langle>clw_rel elvivl_rel\<rangle>nres_rel"
  unfolding op_inter_fst_ivl_scaleR2_def
  including art
  by autoref_monadic
concrete_definition op_inter_fst_ivl_scaleR2_impl uses op_inter_fst_ivl_scaleR2_impl
lemma op_inter_fst_ivl_scaleR2_impl_refine[autoref_rules]:
"DIM_precond TYPE((real, 'a::enum) vec) D \<Longrightarrow>
GEN_OP le ((\<le>) ::'a vec1 \<Rightarrow>_) (lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel) \<Longrightarrow>
(\<lambda>XSi Yi. nres_of (op_inter_fst_ivl_scaleR2_impl le XSi Yi),
 op_inter_fst_ivl_scaleR2::'a vec1 set \<Rightarrow> _)
\<in> elvivl_rel \<rightarrow> lvivl_rel \<rightarrow> \<langle>clw_rel elvivl_rel\<rangle>nres_rel"
  using op_inter_fst_ivl_scaleR2_impl.refine by force

schematic_goal op_inter_fst_ivl_coll_scaleR2_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [THEN GEN_OP_D, autoref_rules]: "GEN_OP le ((\<le>) ::'n vec1 \<Rightarrow>_) (lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel)"
  assumes [autoref_rules]: "(XSi, XS::('n::enum vec1) set) \<in> clw_rel elvivl_rel"
    "(Yi, Y::'n rvec set) \<in> lvivl_rel"
  shows "(nres_of ?r, op_inter_fst_ivl_coll_scaleR2 XS Y) \<in> \<langle>clw_rel elvivl_rel\<rangle>nres_rel"
  unfolding op_inter_fst_ivl_coll_scaleR2_def
  including art
  by autoref_monadic
concrete_definition op_inter_fst_ivl_coll_scaleR2_impl uses op_inter_fst_ivl_coll_scaleR2_impl
lemma op_inter_fst_ivl_coll_scaleR2_impl_refine[autoref_rules]:
"DIM_precond TYPE((real, 'a::enum) vec) D \<Longrightarrow>
GEN_OP le ((\<le>) ::'a vec1 \<Rightarrow>_) (lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel) \<Longrightarrow>
(\<lambda>XSi Yi. nres_of (op_inter_fst_ivl_coll_scaleR2_impl le XSi Yi),
 op_inter_fst_ivl_coll_scaleR2::'a vec1 set \<Rightarrow> _)
\<in> clw_rel elvivl_rel \<rightarrow> lvivl_rel \<rightarrow> \<langle>clw_rel elvivl_rel\<rangle>nres_rel"
  using op_inter_fst_ivl_coll_scaleR2_impl.refine by force

schematic_goal op_inter_ivl_coll_scaleR2_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [THEN GEN_OP_D, autoref_rules]: "GEN_OP le ((\<le>) ::'n vec1 \<Rightarrow>_) (lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel)"
  assumes [autoref_rules]: "(XSi, XS::('n::enum vec1) set) \<in> clw_rel elvivl_rel"
    "(Yi, Y::'n rvec set) \<in> lvivl_rel"
  shows "(nres_of ?r, op_inter_ivl_coll_scaleR2 XS Y) \<in> \<langle>clw_rel elvivl_rel\<rangle>nres_rel"
  unfolding op_inter_ivl_coll_scaleR2_def
  including art
  by autoref_monadic
concrete_definition op_inter_ivl_coll_scaleR2_impl uses op_inter_ivl_coll_scaleR2_impl
lemma op_inter_ivl_coll_scaleR2_impl_refine[autoref_rules]:
"DIM_precond TYPE((real, 'a::enum) vec) D \<Longrightarrow>
GEN_OP le ((\<le>) ::'a vec1 \<Rightarrow>_) (lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel) \<Longrightarrow>
(\<lambda>XSi Yi. nres_of (op_inter_ivl_coll_scaleR2_impl le XSi Yi),
 op_inter_ivl_coll_scaleR2::'a vec1 set \<Rightarrow> _)
\<in> clw_rel elvivl_rel \<rightarrow> lvivl_rel \<rightarrow> \<langle>clw_rel elvivl_rel\<rangle>nres_rel"
  using op_inter_ivl_coll_scaleR2_impl.refine by force

lemma op_image_fst_ivl[autoref_rules]:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes "GEN_OP le ((\<le>) ::'n vec1 \<Rightarrow>_) (lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel)"
  shows "(\<lambda>(l,u). nres_of (if le l u then dRETURN (pairself (take D) (l, u)) else dSUCCEED)
    , op_image_fst_ivl::('n vec1) set\<Rightarrow>_) \<in> lvivl_rel \<rightarrow> \<langle>lvivl_rel\<rangle>nres_rel"
  using assms
  apply (auto simp: ivl_rel_def nres_rel_def op_image_fst_ivl_def RETURN_RES_refine_iff
      dest!: brD intro!: )
  apply (rule relcompI)
   apply (rule prod_relI)
    apply (rule lv_relI)
    apply (simp add: lv_rel_def br_def)
    apply (rule lv_relI)
   apply (simp add: lv_rel_def br_def)
  apply (rule brI)
  subgoal for a b
    apply (drule fun_relD)
     apply (rule lv_relI[where x=a])
      apply (simp add: lv_rel_def br_def)
    apply (drule fun_relD)
     apply (rule lv_relI[where x=b])
      apply (simp add: lv_rel_def br_def)
    apply (auto simp: set_of_ivl_def lv_rel_def br_def fst_imageIcc eucl_of_list_prod)
    done
  subgoal by simp
  done

schematic_goal op_image_fst_ivl_coll_impl[autoref_rules]:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes "GEN_OP le ((\<le>) ::'n vec1 \<Rightarrow>_) (lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel)"
    assumes [autoref_rules]: "(Xi, X) \<in> clw_rel lvivl_rel"
    shows "(nres_of ?r, (op_image_fst_ivl_coll::('n vec1) set\<Rightarrow>_) X) \<in> \<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding op_image_fst_ivl_coll_def
  by autoref_monadic
concrete_definition op_image_fst_ivl_coll_impl uses op_image_fst_ivl_coll_impl
lemma op_image_fst_ivl_coll_impl_refine[autoref_rules]:
  "DIM_precond TYPE((real, 'n::enum) vec) D \<Longrightarrow>
  GEN_OP le ((\<le>) ::'n vec1 \<Rightarrow>_) (lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel) \<Longrightarrow>
  (\<lambda>Xi. nres_of (op_image_fst_ivl_coll_impl Xi), op_image_fst_ivl_coll::('n vec1) set\<Rightarrow>_) \<in>
  clw_rel (lvivl_rel) \<rightarrow> \<langle>clw_rel (\<langle>lv_rel\<rangle>ivl_rel)\<rangle>nres_rel"
  using op_image_fst_ivl_coll_impl.refine
  by force

schematic_goal op_single_inter_ivl_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) D"
  assumes [autoref_rules]: "(FXSi, FXS) \<in> clw_rel lvivl_rel" "(Ai, A::'n::enum rvec set) \<in> lvivl_rel"
  shows "(nres_of ?r, op_single_inter_ivl A FXS) \<in> \<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding op_single_inter_ivl_def
  by autoref_monadic
concrete_definition op_single_inter_ivl_impl for Ai FXSi uses op_single_inter_ivl_impl
lemma op_single_inter_ivl_impl_refine[autoref_rules]:
  "DIM_precond TYPE((real, 'a::enum) vec) D \<Longrightarrow>
  (\<lambda>Ai FXSi. nres_of (op_single_inter_ivl_impl Ai FXSi), op_single_inter_ivl::'a rvec set \<Rightarrow> _) \<in>
    lvivl_rel \<rightarrow> clw_rel (\<langle>lv_rel\<rangle>ivl_rel) \<rightarrow> \<langle>clw_rel (\<langle>lv_rel\<rangle>ivl_rel)\<rangle>nres_rel"
  using op_single_inter_ivl_impl.refine
  by force

schematic_goal partition_ivle_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules]: "(xsi, xs::'n vec1 set)\<in> clw_rel elvivl_rel" "(roi, ro) \<in> reach_optns_rel"
  notes [autoref_rules] = autoref_parameters2
  shows "(nres_of (?f), partition_ivle $ ro $ xs)\<in>\<langle>clw_rel elvivl_rel\<rangle>nres_rel"
  unfolding partition_ivle_def[abs_def]
  including art
  by autoref_monadic
concrete_definition partition_ivle_impl for roi xsi uses partition_ivle_impl
lemmas [autoref_rules] = partition_ivle_impl.refine

schematic_goal vec1repse_impl:
  assumes [autoref_rules]: "(Xi, X) \<in> clw_rel appr1e_rel"
  shows "(nres_of ?r, vec1repse X) \<in> \<langle>\<langle>clw_rel appre_rel\<rangle>option_rel\<rangle>nres_rel"
  unfolding vec1repse_def
  including art
  by autoref_monadic
concrete_definition vec1repse_impl for Xi uses vec1repse_impl
lemmas vec1repse_impl_refine[autoref_rules] = vec1repse_impl.refine[autoref_higher_order_rule]

schematic_goal scaleR2_rep1_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules]: "(Yi, Y::'n vec1 set) \<in> appre_rel"
  notes [autoref_rules] = autoref_parameters2
  shows "(nres_of ?r, scaleR2_rep1 $ Y) \<in> \<langle>elvivl_rel\<rangle>nres_rel"
  unfolding scaleR2_rep1_def
  including art
  by autoref_monadic
concrete_definition scaleR2_rep1_impl uses scaleR2_rep1_impl
lemmas [autoref_rules] = scaleR2_rep1_impl.refine

schematic_goal reduce_ivl_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE((real, 'n) vec) D"
  assumes [autoref_rules]:
    "(Yi, Y::'n::enum vec1 set) \<in> lvivl_rel"
    "(bi, b::((real, 'n) vec, 'n) vec) \<in> lv_rel"
  shows "(nres_of ?r, reduce_ivl $ Y $ b) \<in> \<langle>elvivl_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding reduce_ivl_def
  including art
  by autoref_monadic
concrete_definition reduce_ivl_impl for Yi bi uses reduce_ivl_impl
lemmas [autoref_rules] = reduce_ivl_impl.refine

schematic_goal reduce_ivle_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE((real, 'n) vec) D"
  assumes [autoref_rules]:
    "(Yi, Y::'n::enum vec1 set) \<in> elvivl_rel"
    "(bi, b::((real, 'n) vec, 'n) vec) \<in> lv_rel"
  notes [autoref_rules] = autoref_parameters2
  shows "(nres_of ?r, reduce_ivle $ Y $ b) \<in> \<langle>elvivl_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding reduce_ivle_def
  including art
  by autoref_monadic
concrete_definition reduce_ivle_impl for Yi bi uses reduce_ivle_impl
lemmas [autoref_rules] = reduce_ivle_impl.refine

schematic_goal reduces_ivle_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE((real, 'n) vec) D"
  assumes [autoref_rules]: "(Yi, Y::'n::enum vec1 set) \<in> elvivl_rel"
  notes [autoref_rules] = autoref_parameters2
  shows "(nres_of ?r, reduces_ivle $ Y) \<in> \<langle>elvivl_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding reduces_ivle_def
  including art
  by autoref_monadic
concrete_definition reduces_ivle_impl for Yi uses reduces_ivle_impl
lemmas [autoref_rules] = reduces_ivle_impl.refine


schematic_goal ivlse_of_setse_impl:
  "(nres_of ?r, ivlse_of_setse $ X) \<in> \<langle>clw_rel elvivl_rel\<rangle>nres_rel"
  if [autoref_rules]: "(Xi, X::'n vec1 set) \<in> clw_rel (appre_rel)"
  and  [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  unfolding ivlse_of_setse_def
  including art
  by autoref_monadic
concrete_definition ivlse_of_setse_impl uses ivlse_of_setse_impl
lemmas [autoref_rules] = ivlse_of_setse_impl.refine

schematic_goal setse_of_ivlse_impl:
  "(nres_of ?r, setse_of_ivlse X) \<in> \<langle>clw_rel (appre_rel)\<rangle>nres_rel"
  if [autoref_rules]: "(Xi, X) \<in> clw_rel elvivl_rel"
  unfolding setse_of_ivlse_def
  including art
  by autoref_monadic
concrete_definition setse_of_ivlse_impl uses setse_of_ivlse_impl
lemma setse_of_ivlse_impl_refine[autoref_rules]:
"(\<lambda>Xi. nres_of (setse_of_ivlse_impl Xi), setse_of_ivlse) \<in> clw_rel elvivl_rel \<rightarrow>
    \<langle>clw_rel appre_rel\<rangle>nres_rel"
  using setse_of_ivlse_impl.refine by force

lemma op_image_flow1_of_vec1_colle[autoref_rules]:
  "(map (\<lambda>(lu, x). (lu, (take D x, Some (drop D x)))), op_image_flow1_of_vec1_colle::_\<Rightarrow>'n eucl1 set) \<in> clw_rel appre_rel \<rightarrow> clw_rel appr1e_rel"
  if "DIM_precond TYPE('n::enum rvec) D"
  apply (rule lift_clw_rel_map)
     apply (rule relator_props)
     apply (rule relator_props)
    apply (rule relator_props)
    apply (rule relator_props)
    apply (rule lift_scaleR2)
  unfolding op_image_flow1_of_vec1_colle_def op_image_flow1_of_vec1_coll_def op_image_flow1_of_vec1_def[symmetric]
    apply (rule op_image_flow1_of_vec1)
  using that
  subgoal by force
  subgoal for l u x
    unfolding op_image_flow1_of_vec1_def flow1_of_vec1_def scaleR2_def
    apply (auto simp: image_def vimage_def)
    subgoal for a b c d e
      apply (rule exI[where x="c *\<^sub>R e"])
      apply (auto simp: blinfun_of_vmatrix_scaleR)
      apply (rule exI[where x="c"])
      apply auto
      apply (rule bexI) prefer 2 apply assumption
      apply auto
      done
    subgoal for a b c d e
      apply (rule exI[where x="c"])
      apply (auto simp: blinfun_of_vmatrix_scaleR)
      apply (rule exI[where x="blinfun_of_vmatrix e"])
      apply auto
      apply (rule bexI) prefer 2 apply assumption
      apply auto
      done
    done
  subgoal by auto
  done

schematic_goal partition_set_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules]: "(xsi,xs::'n eucl1 set)\<in> clw_rel appr1e_rel"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel"
  shows "(nres_of (?f), partition_set $ ro $ xs) \<in> \<langle>clw_rel appr1e_rel\<rangle>nres_rel"
  unfolding partition_set_def[abs_def]
  including art
  by autoref_monadic
concrete_definition partition_set_impl for roi xsi uses partition_set_impl
lemmas [autoref_rules] = partition_set_impl.refine

schematic_goal partition_sets_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules]: "(xsi,xs::(bool \<times> 'n eucl1 set \<times> _)set)\<in>
    \<langle>bool_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel
              \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel \<times>\<^sub>r
      clw_rel (isbelows_rel sappr_rel) \<times>\<^sub>r clw_rel sappr_rel\<rangle>list_wset_rel"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel"
  shows "(nres_of (?f), partition_sets $ ro $ xs)\<in>\<langle>clw_rel appr1e_rel\<rangle>nres_rel"
  unfolding partition_sets_def[abs_def]
  including art
  by autoref_monadic
concrete_definition partition_sets_impl for roi xsi uses partition_sets_impl
lemmas [autoref_rules] = partition_sets_impl.refine

lemma [autoref_rules]:
  assumes "PREFER single_valued A"
  shows "(\<lambda>xs. case xs of [x] \<Rightarrow> RETURN x | _ \<Rightarrow> SUCCEED, singleton_spec) \<in> \<langle>A\<rangle>list_wset_rel \<rightarrow> \<langle>A\<rangle>nres_rel"
  using assms
  by (auto simp: nres_rel_def singleton_spec_def list_wset_rel_def set_rel_br
      split: list.splits elim!: single_valued_as_brE dest!: brD
      intro!: RETURN_SPEC_refine brI)


lemma closed_ivl_prod8_list_rel:
  assumes "(xl, x'l)
       \<in> \<langle>bool_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          \<langle>lv_rel\<rangle>ivl_rel \<times>\<^sub>r
          \<langle>lv_rel\<rangle>sctn_rel \<times>\<^sub>r clw_rel (\<langle>sappr_rel, \<langle>lv_rel\<rangle>sbelows_rel\<rangle>inter_rel) \<times>\<^sub>r clw_rel sappr_rel\<rangle>list_wset_rel"
  shows "(\<forall>(b, X, PS1, PS2, R, ivl, sctn, CX, CXS)\<in>x'l. closed ivl)"
  using assms
  unfolding list_wset_rel_def set_rel_sv[OF single_valued_Id_arbitrary_interface]
  apply (subst (asm) set_rel_sv)
  subgoal
    by (auto simp: Id_arbitrary_interface_def intro!: relator_props intro: single_valuedI)
  by (auto simp: Id_arbitrary_interface_def)

lemma
  poincare_onto_series_rec_list_eq:\<comment> \<open>TODO: here is a problem if interrupt gets uncurried, too\<close>
  "poincare_onto_series interrupt trap guards XS ivl sctn ro = rec_list
      (\<lambda>(((((trap), XS0), ivl), sctn), ro).
          let guard0 = mk_coll (mk_inter ivl (plane_of sctn))
          in ASSUME (closed guard0) \<bind>
             (\<lambda>_. (poincare_onto2 (ro ::: reach_optns_rel) (interrupt:::appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel) trap
                    (op_empty_coll ::: clw_rel (\<langle>\<langle>lv_rel\<rangle>ivl_rel, \<langle>lv_rel\<rangle>plane_rel\<rangle>inter_rel)) guard0 XS0 :::
                   \<langle>\<langle>bool_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel \<times>\<^sub>r
      clw_rel (isbelows_rel sappr_rel) \<times>\<^sub>r clw_rel sappr_rel\<rangle>list_wset_rel\<rangle>nres_rel) \<bind>
                  (\<lambda>(XS1).
                      singleton_spec XS1 \<bind>
                      (\<lambda>(b, X, PS1, PS2, R, ivl', sctn', CX, CXS). var.CHECKs ''poincare_onto_series: last return!'' (ivl' = ivl \<and> sctn' = sctn) \<bind> (\<lambda>_. RETURN PS2)))))
      (\<lambda>x xs rr (((((trap), XS0), ivl), sctn), ro0).
          case x of
          (guard, ro) \<Rightarrow>
            ASSUME (closed ivl) \<bind> 
            (\<lambda>_. let guard0 = mk_coll (mk_inter ivl (plane_of sctn))
                 in ASSUME (closed guard0) \<bind>
                 (\<lambda>_. ASSUME (\<forall>(guard, ro)\<in>set (x # xs). closed guard) \<bind>
                      (\<lambda>_. let guardset = \<Union>(guard, ro)\<in>set ((guard0, ro0) # xs). guard
                           in (poincare_onto2 ro (interrupt:::appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel) trap (guardset ::: clw_rel (\<langle>\<langle>lv_rel\<rangle>ivl_rel, \<langle>lv_rel\<rangle>plane_rel\<rangle>inter_rel))
                                guard XS0 :::
                               \<langle>\<langle>bool_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel \<times>\<^sub>r
      clw_rel (isbelows_rel sappr_rel) \<times>\<^sub>r clw_rel sappr_rel\<rangle>list_wset_rel\<rangle>nres_rel) \<bind>
                              (\<lambda>(XS1).
                                  ASSUME (\<forall>(b, X, PS, PS2, R, ivl, sctn, CX, CXS)\<in>XS1. closed ivl) \<bind>
                                  (\<lambda>_.
                                    partition_sets ro XS1 \<bind>
                                    (\<lambda>XS2. fst_safe_colle XS2 \<bind> (\<lambda>_. rr (((((trap), XS2), ivl), sctn), ro0 ::: reach_optns_rel) \<bind> RETURN))))))))
      guards (((((trap), XS), ivl), sctn), ro)"
  by (induction guards arbitrary: XS ivl sctn ro) (auto simp: split_beta' split: prod.splits)

schematic_goal poincare_onto_series_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(XSi, XS::'n eucl1 set) \<in> clw_rel appr1e_rel"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> \<langle>clw_rel (iplane_rel lvivl_rel)\<times>\<^sub>rreach_optns_rel\<rangle>list_rel"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel" "(ivli, ivl) \<in> lvivl_rel" "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  assumes [autoref_rules]: "(symstarti, symstart::'n eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set)nres)
    \<in> appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  assumes [unfolded autoref_tag_defs, refine_transfer]: "\<And>X. TRANSFER (nres_of (symstartd X) \<le> symstarti X)"
    and [autoref_rules]: "((), trap) \<in> ghost_rel"
  notes [intro, simp] = list_set_rel_finiteD closed_ivl_prod3_list_rel closed_clw_rel_iplane_rel
    closed_ivl_prod8_list_rel
  notes [autoref_rules_raw] = ghost_relI[of x for x::"'n eucl1 set"]
  shows "(nres_of ?r, poincare_onto_series $ symstart $ trap $ guards $ XS $ ivl $ sctn $ ro) \<in> \<langle>clw_rel appr1e_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding poincare_onto_series_rec_list_eq
  including art
  apply autoref_monadic
  apply (rule ghost_relI)
  apply (autoref phases: trans)
  apply (autoref phases: trans)
  apply (rule ghost_relI)
  apply (autoref phases: trans)
  apply (autoref phases: trans)
  apply simp
  apply (autoref phases: trans)
    apply (autoref phases: trans)
   apply simp
  apply (refine_transfer)
  done

concrete_definition poincare_onto_series_impl for symstartd guardsi XSi ivli sctni roi uses poincare_onto_series_impl
lemmas [autoref_rules] = poincare_onto_series_impl.refine

schematic_goal poincare_onto_from_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(XSi, XS) \<in> clw_rel appr1e_rel"
    and [autoref_rules]: "(Si, S) \<in> \<langle>lv_rel\<rangle>halfspaces_rel"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> \<langle>clw_rel (iplane_rel lvivl_rel)\<times>\<^sub>rreach_optns_rel\<rangle>list_rel"
    and civl[autoref_rules]: "(ivli, ivl::'n rvec set) \<in> lvivl_rel"
    and csctns[autoref_rules]: "(sctni, sctn::'n rvec sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel"
  assumes [autoref_rules]: "(symstarti, symstart::'n eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set)nres)
    \<in> appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  assumes [unfolded autoref_tag_defs, refine_transfer]: "\<And>X. TRANSFER (nres_of (symstartd X) \<le> symstarti X)"
    and [autoref_rules]: "((), trap) \<in> ghost_rel"
  notes [intro, simp] = list_set_rel_finiteD closed_ivl_rel[OF civl] closed_ivl_prod3_list_rel
  shows "(nres_of ?r, poincare_onto_from $ symstart $ trap $ S $ guards $ ivl $ sctn $ ro $ XS) \<in>
    \<langle>clw_rel appr1e_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding poincare_onto_from_def
  including art
  by autoref_monadic

concrete_definition poincare_onto_from_impl for symstartd Si guardsi ivli sctni roi XSi uses poincare_onto_from_impl
lemmas [autoref_rules] = poincare_onto_from_impl.refine

lemma [autoref_op_pat]: "a \<times> b \<equiv> OP op_times_ivl $ a $ b"
  by (auto simp: )

lemma op_times_ivl[autoref_rules]:
  "(\<lambda>(l, u) (l', u'). (l @ l', u @ u'), op_times_ivl) \<in> lvivl_rel \<rightarrow> lvivl_rel \<rightarrow> lvivl_rel"
  apply (auto simp: ivl_rel_def br_def intro!: rel_funI)
  subgoal for a b c d e f g h
    apply (rule relcompI[where b="((c, g), (d, h))"])
    by (auto simp: lv_rel_def br_def set_of_ivl_def)
  done

lemma default_rep_op_pat[autoref_op_pat_def]: "default_rep d \<equiv> OP (default_rep d)"
  by (auto simp: )

lemma default_rep[autoref_rules]:
  "(\<lambda>x. RETURN x, default_rep d) \<in> (\<langle>R\<rangle>(default_rel d)) \<rightarrow> \<langle>\<langle>R\<rangle>option_rel\<rangle>nres_rel"
  by (force simp: default_rep_def nres_rel_def default_rel_def
      split: option.splits intro!: RETURN_SPEC_refine )

schematic_goal subset_spec1_impl:
  "(nres_of ?r, subset_spec1 R P dP) \<in> \<langle>bool_rel\<rangle>nres_rel"
  if [autoref_rules]:
    "(Ri, R) \<in> appr1_rel"
    "(Pimpl, P) \<in> lvivl_rel"
    "(dPi, dP) \<in> \<langle>lvivl_rel\<rangle>(default_rel UNIV)"
  unfolding subset_spec1_def
  including art
  by autoref_monadic
lemmas [autoref_rules] = subset_spec1_impl[autoref_higher_order_rule]

schematic_goal subset_spec1_collc:
  "(nres_of (?f), subset_spec1_coll R P dP) \<in> \<langle>bool_rel\<rangle>nres_rel"
  if [autoref_rules]:
    "(Ri, R) \<in> clw_rel appr1_rel"
    "(Pimpl, P) \<in> lvivl_rel"
    "(dPi, dP) \<in> \<langle>lvivl_rel\<rangle>(default_rel UNIV)"
  unfolding subset_spec1_coll_def
  including art
  by autoref_monadic
concrete_definition subset_spec1_collc for Ri Pimpl dPi uses subset_spec1_collc
lemmas subset_spec1_collc_refine[autoref_rules] = subset_spec1_collc.refine[autoref_higher_order_rule]

lemma phantom_rel_union_coll[autoref_rules]:\<comment> \<open>TODO: move!\<close>
  assumes [THEN GEN_OP_D, autoref_rules(overloaded)]: "GEN_OP un op_union_coll (clw_rel A \<rightarrow> clw_rel A \<rightarrow> clw_rel A)"
  shows "(\<lambda>a b. do {a \<leftarrow> a; b \<leftarrow> b; Some (un a b)}, op_union_phantom) \<in> \<langle>clw_rel A\<rangle>phantom_rel \<rightarrow> \<langle>clw_rel A\<rangle>phantom_rel \<rightarrow> \<langle>clw_rel A\<rangle>phantom_rel"
  using assms
  by (fastforce simp: phantom_rel_def dest: fun_relD)

schematic_goal one_step_until_time_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(X0i, X0::'n eucl1 set) \<in> appr1e_rel"
  assumes [autoref_rules]: "(phi, ph) \<in> bool_rel"
  assumes [autoref_rules]: "(t1i, t1) \<in> rnv_rel"
  notes [autoref_tyrel] = ty_REL[where 'a="real" and R="Id"]
  shows "(nres_of ?f, one_step_until_time $ X0 $ ph $ t1)\<in>\<langle>appr1e_rel \<times>\<^sub>r \<langle>clw_rel appr_rel\<rangle>phantom_rel\<rangle>nres_rel"
  unfolding one_step_until_time_def[abs_def]
  including art
  by autoref_monadic
concrete_definition one_step_until_time_impl for X0i phi t1i uses one_step_until_time_impl
lemmas one_step_until_time_impl_refine[autoref_rules] = one_step_until_time_impl.refine

lemma get_phantom_impl[autoref_rules]:
  "(\<lambda>x. nres_of (case x of None \<Rightarrow> dSUCCEED | Some y \<Rightarrow> dRETURN y), get_phantom) \<in> \<langle>A\<rangle>phantom_rel \<rightarrow> \<langle>A\<rangle>nres_rel"
  by (auto simp: get_phantom_def phantom_rel_def nres_rel_def RETURN_RES_refine_iff)

schematic_goal ivl_of_appr1_coll_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules]: "(Xi, X::'n::enum rvec set) \<in> clw_rel appr_rel"
  shows "(nres_of ?r, ivl_of_eucl_coll X) \<in> \<langle>appr1_rel\<rangle>nres_rel"
  unfolding ivl_of_eucl_coll_def
  by autoref_monadic
concrete_definition ivl_of_appr1_coll_impl uses ivl_of_appr1_coll_impl

lemma ivl_of_appr1_coll_impl_refine[autoref_rules]:
  "DIM_precond TYPE('n::enum rvec) D \<Longrightarrow>
    (\<lambda>Xi. nres_of (ivl_of_appr1_coll_impl Xi), ivl_of_eucl_coll::'n::enum rvec set\<Rightarrow>_) \<in>
  clw_rel appr_rel \<rightarrow> \<langle>appr1_rel\<rangle>nres_rel"
  using ivl_of_appr1_coll_impl.refine
  by force

schematic_goal one_step_until_time_ivl_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(X0i, X0::'n eucl1 set) \<in> appr1e_rel"
  assumes [autoref_rules]: "(phi, ph) \<in> bool_rel"
  assumes [autoref_rules]: "(t1i, t1) \<in> rnv_rel"
  assumes [autoref_rules]: "(t2i, t2) \<in> rnv_rel"
  shows "(nres_of ?r, one_step_until_time_ivl $ X0 $ ph $ t1 $ t2) \<in> \<langle>appr1e_rel \<times>\<^sub>r \<langle>clw_rel appr_rel\<rangle>phantom_rel\<rangle>nres_rel"
  unfolding one_step_until_time_ivl_def
  including art
  by autoref_monadic
concrete_definition one_step_until_time_ivl_impl for X0i phi t1i t2i uses one_step_until_time_ivl_impl
lemmas [autoref_rules] = one_step_until_time_ivl_impl.refine

end

end

context approximate_sets_options' begin

context includes autoref_syntax begin

lemma trace_str_impl[autoref_rules]:
  shows "(\<lambda>s. tracing_fun optns s None, trace_str) \<in> string_rel \<rightarrow> Id"
  by auto

lemma [autoref_rules]:
  "(approximate_sets_options.rk2_fas, approximate_sets_options.rk2_fas) \<in>
      \<langle>Id\<rangle>list_rel \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>list_rel\<rightarrow> Id\<rightarrow>  \<langle>Id\<rangle>list_rel"
  "(approximate_sets_options.euler_fas, approximate_sets_options.euler_fas) \<in>
      \<langle>Id\<rangle>list_rel \<rightarrow>  \<langle>Id\<rangle>list_rel \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>list_rel\<rightarrow> \<langle>Id\<rangle>list_rel"
  "(approximate_sets_options.euler_incr_fas, approximate_sets_options.euler_incr_fas) \<in>
      \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>list_rel\<rightarrow> \<langle>Id\<rangle>list_rel"
  "(approximate_sets_ode_slp.ode_e', approximate_sets_ode_slp.ode_e') \<in> \<langle>Id\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow>  \<langle>Id\<rangle>list_rel"
  "(approximate_sets_ode_slp'.solve_poincare_fas, approximate_sets_ode_slp'.solve_poincare_fas) \<in> nat_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> \<langle>Id\<rangle>list_rel"
  by (auto simp: list_rel_imp_same_length)

lemma ode_autoref:
  "(ode_e, ode_e) \<in> \<langle>Id\<rangle>list_rel"
  "(safe_form, safe_form) \<in> Id"
  by auto

schematic_goal init_ode_solver_autoref:
  assumes [autoref_rules]:
    "(ui, u) \<in> bool_rel"
  notes [autoref_rules] = ode_autoref
  shows "(nres_of (?f), init_ode_solver $ u) \<in>
    \<langle>nat_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r
    \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<times>\<^sub>r
                \<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel\<rangle>option_rel
     \<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding init_ode_solver_def
  including art
  by autoref_monadic
concrete_definition init_ode_solveri uses init_ode_solver_autoref
lemmas [autoref_rules] = init_ode_solveri.refine

lemma has_c1_info_pat[autoref_op_pat_def]: "has_c1_info \<equiv> OP has_c1_info" by simp

lemma has_c1_info_autoref[autoref_rules]:
  "(\<lambda>xs. if list_all (\<lambda>(_, _, c1). c1 \<noteq> None) xs then RETURN True else RETURN False, has_c1_info) \<in> clw_rel appr1e_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  by (auto simp: has_c1_info_def nres_rel_def)

lemma empty_symstart_dres_nres_rel:
  "((\<lambda>x. dRETURN ([], [x])), empty_symstart::'n::enum eucl1 set\<Rightarrow>_) \<in>
    (appr1e_rel) \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>dres_nres_rel"
  using mk_coll[OF PREFER_I[of single_valued, OF sv_appr1e_rel[OF sv_appr1_rel]], param_fo, of x y for x and y::"'n eucl1 set"]
  by (auto simp: mk_coll_def[abs_def] dres_nres_rel_def)

lemma empty_symstart_nres_rel[autoref_rules]:
  "((\<lambda>x. RETURN ([], [x])), empty_symstart::'n::enum eucl1 set\<Rightarrow>_) \<in>
    appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  using mk_coll[OF PREFER_I[of single_valued, OF sv_appr1e_rel[OF sv_appr1_rel]], param_fo, of x y for x and y::"'n eucl1 set"]
  by (auto simp: mk_coll_def[abs_def] nres_rel_def)

lemma TRANSFER_I: "x \<Longrightarrow> TRANSFER x"
  by simp

lemma dres_nres_rel_nres_relD: "(symstartd, symstart) \<in> A \<rightarrow> \<langle>B\<rangle>dres_nres_rel \<Longrightarrow> (\<lambda>x. nres_of (symstartd x), symstart) \<in> A \<rightarrow> \<langle>B\<rangle>nres_rel"
  by (auto simp: dres_nres_rel_def nres_rel_def dest!: fun_relD)

lemma poincare_onto_from_ivla_refinep[autoref_rules]:
  assumes "DIM_precond TYPE('n::enum rvec) D"
  assumes "var.ncc_precond TYPE('n rvec)"
  assumes "var.ncc_precond TYPE('n vec1)"
  assumes "(Di, D) \<in> nat_rel"
  shows "(\<lambda>ode_slp euler_incr_slp euler_slp rk2_slp c1_slps solve_poincare_slp symstartd trapi Si guardsi ivli sctni roi XSi.
    nres_of (poincare_onto_from_impl Di ode_slp euler_incr_slp euler_slp rk2_slp c1_slps solve_poincare_slp symstartd Si guardsi ivli sctni roi XSi),
          poincare_onto_from $ D)
         \<in> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel\<rangle>option_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<rightarrow>
           (appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>dres_nres_rel) \<rightarrow>
           ghost_rel \<rightarrow>
           \<langle>lv_rel\<rangle>halfspaces_rel \<rightarrow>
           \<langle>clw_rel (iplane_rel lvivl_rel) \<times>\<^sub>r reach_optns_rel\<rangle>list_rel \<rightarrow>
           \<langle>lv_rel\<rangle>ivl_rel \<rightarrow>
           \<langle>lv_rel\<rangle>sctn_rel \<rightarrow>
           reach_optns_rel \<rightarrow>
           clw_rel (appr1e_rel::(_\<times>('n rvec \<times> _) set)set) \<rightarrow>
            \<langle>clw_rel appr1e_rel\<rangle>nres_rel"
  using poincare_onto_from_impl.refine[OF assms(1,2,3) _ _ _ _ _ _ _ TRANSFER_I[OF order_refl]] assms(4)
  by (force dest!: dres_nres_rel_nres_relD)

lemma wd_step_DIM_precond: "vwd_step D a b c d e f TYPE('n::enum)\<Longrightarrow> DIM_precond TYPE('n rvec) D"
  by (auto simp: vwd_step_def wd_def)

lemma poincare_onto_froma_def':
  "poincare_onto_froma interrupt trap S guards ivl sctn ro (XS0::'n::enum eucl1 set) =
  do {
    has_c1 \<leftarrow> has_c1_info XS0;
    (D, ode_slp, euler_incr_slp, euler_slp, rk2_slp, solve_poincare_slp, c1_slps) \<leftarrow> init_ode_solver has_c1;
    ASSERT (vwd_step D ode_slp euler_incr_slp euler_slp rk2_slp c1_slps
      solve_poincare_slp TYPE('n));
    OP poincare_onto_from D ode_slp euler_incr_slp euler_slp rk2_slp c1_slps
       solve_poincare_slp interrupt trap S guards ivl sctn ro XS0
  }"
  by (auto simp: poincare_onto_froma_def)

schematic_goal solve_poincare_map:
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n::enum rvec)"
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n::enum vec1)"
  assumes [autoref_rules]: "(XSi, XS::'n eucl1 set) \<in> clw_rel appr1e_rel"
    "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel" "(ivli, ivl) \<in> lvivl_rel"
    "(Si, S) \<in> \<langle>lv_rel\<rangle>halfspaces_rel"
    "(guardsi, guards) \<in> \<langle>clw_rel (iplane_rel lvivl_rel) \<times>\<^sub>r reach_optns_rel\<rangle>list_rel"
    "(symstartd, symstart) \<in> (appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>dres_nres_rel)"
    "((), trap) \<in> ghost_rel"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel"
  notes [autoref_rules_raw] = wd_step_DIM_precond
  shows "(nres_of (?f), poincare_onto_froma $ symstart $ trap $ S $ guards $ ivl $ sctn $ ro $ (XS::'n::enum eucl1 set)) \<in>
    \<langle>clw_rel appr1e_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding poincare_onto_froma_def'
  including art
  by autoref_monadic
concrete_definition solve_poincare_map for symstartd Si guardsi ivli sctni roi XSi uses solve_poincare_map
lemmas [autoref_rules] = solve_poincare_map.refine

lemma poincare_onto_series_refinep[autoref_rules]:
  assumes "DIM_precond TYPE('n::enum rvec) D"
  assumes "var.ncc_precond TYPE('n rvec)"
  assumes "var.ncc_precond TYPE('n vec1)"
  assumes "(Di, D) \<in> nat_rel"
  shows "(\<lambda>ode_slp euler_incr_slp euler_slp rk2_slp c1_slps solve_poincare_slp symstart trap guards X0 ivl sctn ro.
    nres_of (poincare_onto_series_impl Di ode_slp euler_incr_slp euler_slp rk2_slp c1_slps solve_poincare_slp symstart guards X0 ivl sctn ro),
          poincare_onto_series $ D)
         \<in> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel\<rangle>option_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<rightarrow>
           (appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>dres_nres_rel) \<rightarrow>
            ghost_rel \<rightarrow>
           \<langle>clw_rel (iplane_rel lvivl_rel) \<times>\<^sub>r reach_optns_rel\<rangle>list_rel \<rightarrow>
           clw_rel (appr1e_rel::(_\<times>('n rvec \<times> _) set)set) \<rightarrow>
           \<langle>lv_rel\<rangle>ivl_rel \<rightarrow>
           \<langle>lv_rel\<rangle>sctn_rel \<rightarrow>
           reach_optns_rel \<rightarrow>
            \<langle>clw_rel appr1e_rel\<rangle>nres_rel"
  using poincare_onto_series_impl.refine[OF assms(1,2,3) _ _ _ _ _ _ TRANSFER_I[OF order_refl]] assms(4)
  by (auto dest!: dres_nres_rel_nres_relD)

lemma poincare_ontoa_def': "poincare_ontoa guards ivl sctn ro (XS0::'n::enum eucl1 set) =
  do {
    has_c1 \<leftarrow> has_c1_info XS0;
    (D, ode_slp, euler_incr_slp, euler_slp, rk2_slp, solve_poincare_slp, c1_slps) \<leftarrow> init_ode_solver has_c1;
    ASSERT (vwd_step D ode_slp euler_incr_slp euler_slp rk2_slp c1_slps
      solve_poincare_slp TYPE('n));
    OP poincare_onto_series D ode_slp euler_incr_slp euler_slp rk2_slp c1_slps
       solve_poincare_slp empty_symstart empty_trap guards XS0 ivl sctn ro
  }"
  by (simp add: poincare_ontoa_def)

schematic_goal solve_poincare_onto:
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n::enum rvec)"
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n::enum vec1)"
  assumes [autoref_rules]: "(XSi, XS::'n eucl1 set) \<in> clw_rel appr1e_rel"
    "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel" "(ivli, ivl) \<in> lvivl_rel"
    "(guardsi, guards) \<in> \<langle>clw_rel (iplane_rel lvivl_rel) \<times>\<^sub>r reach_optns_rel\<rangle>list_rel"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel"
  notes [autoref_rules_raw] = wd_step_DIM_precond
  notes [autoref_rules] = empty_symstart_dres_nres_rel
  shows "(nres_of (?f), poincare_ontoa $ guards $ ivl $ sctn $ ro $ (XS::'n::enum eucl1 set)) \<in>
    \<langle>clw_rel appr1e_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding poincare_ontoa_def'
  including art
  by autoref_monadic
concrete_definition solve_poincare_onto for guardsi ivli sctni roi XSi uses solve_poincare_onto
lemmas [autoref_rules] = solve_poincare_onto.refine

lemma one_step_until_time_ivl_impl_refinep[autoref_rules]:
  assumes "DIM_precond TYPE('n::enum rvec) D"
  assumes "var.ncc_precond TYPE('n rvec)"
  assumes "var.ncc_precond TYPE('n vec1)"
  assumes "(Di, D) \<in> nat_rel"
  shows "(\<lambda>euler_incr_slp euler_slp rk2_slp c1_slps X0i histi t1i t2i.
      nres_of (one_step_until_time_ivl_impl Di euler_incr_slp euler_slp rk2_slp c1_slps X0i histi t1i t2i),
   one_step_until_time_ivl $ D)
         \<in> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r\<langle>Id\<rangle>list_rel \<times>\<^sub>r\<langle>Id\<rangle>list_rel\<rangle>option_rel \<rightarrow>
        appr1e_rel \<rightarrow> bool_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel \<rightarrow>
  \<langle>appr1e_rel \<times>\<^sub>r \<langle>clw_rel (appr_rel::(_\<times>('n rvec) set)set)\<rangle>phantom_rel\<rangle>nres_rel"
  using one_step_until_time_ivl_impl.refine assms by force

lemma solve_one_step_until_timea_def':
"solve_one_step_until_timea (X0::'n::enum eucl1 set) CX t1 t2 =
  do {
    has_c1 \<leftarrow> has_c1_info (mk_coll X0);
    (D, ode_slp, euler_incr_slp, euler_slp, rk2_slp, solve_poincare_slp,
       c1_slps) \<leftarrow> init_ode_solver has_c1;
    ASSERT (vwd_step D ode_slp euler_incr_slp euler_slp rk2_slp c1_slps solve_poincare_slp TYPE('n));
    OP one_step_until_time_ivl D euler_incr_slp euler_slp rk2_slp c1_slps X0 CX t1 t2
  }"
  by (auto simp: solve_one_step_until_timea_def)

schematic_goal solve_one_step_until_time_autoref:
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n::enum rvec)"
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n::enum vec1)"
  assumes [autoref_rules]: "(X0i, X0) \<in> appr1e_rel" "(CXi, CX) \<in> bool_rel" "(t1i, t1) \<in> rnv_rel"
     "(t2i, t2) \<in> rnv_rel"
  notes [autoref_rules_raw] = wd_step_DIM_precond
  shows "(nres_of ?f, solve_one_step_until_timea $ (X0::'n eucl1 set) $ CX $ t1 $ t2) \<in>
    \<langle>appr1e_rel \<times>\<^sub>r \<langle>clw_rel appr_rel\<rangle>phantom_rel\<rangle>nres_rel"
  unfolding solve_one_step_until_timea_def'
  including art
  by autoref_monadic
concrete_definition solve_one_step_until_time for X0i CXi t1i t2i uses solve_one_step_until_time_autoref
lemmas solve_one_step_until_time_refine[autoref_rules] = solve_one_step_until_time.refine

lemma c1_info_of_apprsI:
  assumes "(b, a) \<in> clw_rel appr1_rel"
  assumes "x \<in> a"
  shows "x \<in> c1_info_of_apprs b"
  using assms
  by (auto simp: appr1_rel_br clw_rel_br c1_info_of_apprs_def dest!: brD)

lemma clw_rel_appr1_relI:
  assumes "\<And>X. X \<in> set XS \<Longrightarrow> c1_info_invar CARD('n::enum) X"
  shows "(XS, c1_info_of_apprs XS::('n rvec\<times>_)set) \<in> clw_rel appr1_rel"
  by (auto simp: appr1_rel_br clw_rel_br c1_info_of_apprs_def intro!: brI assms)

lemma c1_info_of_appr'I:
  assumes "(b, a) \<in> \<langle>clw_rel appr1_rel\<rangle>phantom_rel"
  assumes "x \<in> a"
  shows "x \<in> c1_info_of_appr' b"
  using assms
  by (auto simp add: c1_info_of_appr'_def intro!: c1_info_of_apprsI split: option.splits)

lemma appr1e_relI:
  assumes "c1_info_invare CARD('n::enum) X0i"
  shows "(X0i, c1_info_of_appre X0i::'n eucl1 set) \<in> appr1e_rel"
  using assms
  apply (cases X0i)
  apply (auto simp: scaleR2_rel_def c1_info_of_appre_def c1_info_invare_def)
  apply (rule relcompI)
   apply (rule prod_relI)
    apply (rule IdI)
   apply (rule appr1_relI)
    apply (auto simp: vimage_def intro!: brI)
   apply (metis ereal_dense2 less_imp_le)
    apply (rule relcompI)
   apply (rule prod_relI)
    apply (rule IdI)
   apply (rule appr1_relI)
   apply (auto simp: vimage_def intro!: brI)
  by (metis basic_trans_rules(23) ereal_cases ereal_less_eq(1) ereal_top order_eq_refl)

lemma c1_info_of_apprI:
  assumes "(b, a) \<in> appr1_rel"
  assumes "x \<in> a"
  shows "x \<in> c1_info_of_appr b"
  using assms
  apply (auto simp add: c1_info_of_appr_def c1_info_invar_def appr1_rel_internal appr_rel_def lv_rel_def
      set_rel_br
      dest!: brD
      split: option.splits)
   apply (auto simp add:  appr_rell_internal dest!: brD)
  done

lemma c1_info_of_appreI:
  assumes "(lub, a) \<in> appr1e_rel"
  assumes "x \<in> a"
  shows "x \<in> c1_info_of_appre lub"
  using assms
  apply (auto simp add: scaleR2_def c1_info_of_appre_def image_def vimage_def scaleR2_rel_def
      dest!: brD
      intro!: c1_info_of_apprsI split: option.splits)
  subgoal for a b c d e f g h i
    apply (rule exI[where x=g])
    apply (rule conjI, assumption)+
    apply (rule bexI)
     prefer 2
     apply (rule c1_info_of_apprI) apply assumption
     apply assumption apply simp
    done
  done

lemma c1_info_of_apprseI:
  assumes "(b, a) \<in> clw_rel appr1e_rel"
  assumes "x \<in> a"
  shows "x \<in> c1_info_of_apprse b"
  using assms
  by (force simp: appr1_rel_br scaleR2_rel_br clw_rel_br c1_info_of_appre_def c1_info_of_apprse_def
      dest!: brD)

lemma clw_rel_appr1e_relI:
  assumes "\<And>X. X \<in> set XS \<Longrightarrow> c1_info_invare CARD('n::enum) X"
  shows "(XS, c1_info_of_apprse XS::('n rvec\<times>_)set) \<in> clw_rel appr1e_rel"
  using assms
  apply (auto simp: c1_info_of_apprse_def c1_info_of_appre_def c1_info_invare_def)
  unfolding appr1_rel_br scaleR2_rel_br clw_rel_br
  apply (rule brI)
   apply (auto simp: c1_info_invar_def vimage_def)
  subgoal premises prems for a b c d
    using prems(1)[OF prems(2)]
    by (cases a; cases b) auto
  done

schematic_goal poincare_onto_from_in_ivl_impl:
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n::enum rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(XSi, XS) \<in> clw_rel appr1e_rel"
    and [autoref_rules]: "(Si, S) \<in> \<langle>lv_rel\<rangle>halfspaces_rel"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> \<langle>clw_rel (iplane_rel lvivl_rel)\<times>\<^sub>rreach_optns_rel\<rangle>list_rel"
    and civl[autoref_rules]: "(ivli, ivl::'n rvec set) \<in> lvivl_rel"
    and csctns[autoref_rules]: "(sctni, sctn::'n rvec sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel"
  assumes [autoref_rules]: "(symstarti, symstart::'n eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set)nres)
    \<in> (appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>dres_nres_rel)"
    and [autoref_rules]: "((), trap) \<in> ghost_rel"
      "(Pimpl, P::'n rvec set) \<in> lvivl_rel"
      "(dPi, dP:: ((real, 'n) vec, 'n) vec set) \<in> \<langle>lvivl_rel\<rangle>(default_rel UNIV)"
  notes [intro, simp] = list_set_rel_finiteD closed_ivl_rel[OF civl] closed_ivl_prod3_list_rel
  shows "(nres_of ?r,
    poincare_onto_from_in_ivl $ symstart $ trap $ S $ guards $ ivl $ sctn $ ro $ XS $ P $ dP) \<in>
    \<langle>bool_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding poincare_onto_from_in_ivl_def
  including art
  by autoref_monadic
concrete_definition poincare_onto_from_in_ivl_impl for symstarti Si guardsi ivli sctni roi XSi Pimpl dPi
  uses poincare_onto_from_in_ivl_impl
lemmas [autoref_rules] = poincare_onto_from_in_ivl_impl.refine

schematic_goal one_step_until_time_ivl_in_ivl_impl:
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n::enum rvec)"
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(X0i, X0::'n eucl1 set) \<in> appr1e_rel"
  assumes [autoref_rules]: "(t1i, t1) \<in> rnv_rel"
  assumes [autoref_rules]: "(t2i, t2) \<in> rnv_rel"
      "(Ri, R) \<in> lvivl_rel"
      "(dRi, dR) \<in> \<langle>lvivl_rel\<rangle>(default_rel UNIV)"
  shows "(nres_of ?r, one_step_until_time_ivl_in_ivl X0 t1 t2 R dR) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding one_step_until_time_ivl_in_ivl_def
  including art
  by autoref_monadic
concrete_definition one_step_until_time_ivl_in_ivl_impl for X0i t1i t2i Ri dRi uses one_step_until_time_ivl_in_ivl_impl
lemmas one_step_until_time_ivl_in_ivl_impl_refine[autoref_rules] = one_step_until_time_ivl_in_ivl_impl.refine

schematic_goal poincare_onto_in_ivl_impl:
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n::enum rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(XSi, XS) \<in> clw_rel appr1e_rel"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> \<langle>clw_rel (iplane_rel lvivl_rel)\<times>\<^sub>rreach_optns_rel\<rangle>list_rel"
    and civl[autoref_rules]: "(ivli, ivl::'n rvec set) \<in> lvivl_rel"
    and csctns[autoref_rules]: "(sctni, sctn::'n rvec sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel"
      "(Pimpl, P::'n rvec set) \<in> lvivl_rel"
      "(dPi, dP:: ((real, 'n) vec, 'n) vec set) \<in> \<langle>lvivl_rel\<rangle>(default_rel UNIV)"
  notes [intro, simp] = list_set_rel_finiteD closed_ivl_rel[OF civl] closed_ivl_prod3_list_rel
  shows "(nres_of ?r,
    poincare_onto_in_ivl $ guards $ ivl $ sctn $ ro $ XS $ P $ dP) \<in>
    \<langle>bool_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding poincare_onto_in_ivl_def
  including art
  by autoref_monadic

concrete_definition poincare_onto_in_ivl_impl for guardsi ivli sctni roi XSi Pimpl dPi
  uses poincare_onto_in_ivl_impl
lemmas [autoref_rules] = poincare_onto_in_ivl_impl.refine

definition "solves_poincare_map symstart S guards ivli sctni roi XS P dP \<longleftrightarrow>
  poincare_onto_from_in_ivl_impl symstart S guards ivli sctni roi XS P dP = dRETURN True"

definition "solves_poincare_map' S = solves_poincare_map (\<lambda>x. dRETURN ([], [x])) [S]"

definition "one_step_until_time_ivl_in_ivl_check X t0 t1 Ri dRi \<longleftrightarrow>
  one_step_until_time_ivl_in_ivl_impl X t0 t1 Ri dRi = dRETURN True"

definition "solves_poincare_map_onto guards ivli sctni roi XS P dP \<longleftrightarrow>
  poincare_onto_in_ivl_impl guards ivli sctni roi XS P dP = dRETURN True"

end

end

end