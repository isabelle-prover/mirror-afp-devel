theory Refine_Reachability_Analysis
imports
  Print
  "../Refinement/Weak_Set"
  "../Refinement/Refine_String"
  "../Refinement/Refine_Folds"
  "../IVP/Flow"
  Refine_Rigorous_Numerics
begin


record ('a, 'b) options =
  precision :: nat
  tolerance :: real
  stepsize :: real
  iterations :: nat
  halve_stepsizes :: nat
  widening_mod :: nat
  rk2_param :: real
  max_tdev_thres :: real
  pre_split_summary_tolerance :: real
  reduce_summary_tolerance :: real
  collect_granularity :: real
  start_section :: "'a sctn"
  checkpoint_sections :: "'a sctn list"
  stop_sections :: "'a sctn list"
  snap_sections :: "real"
  min_section_distance :: "real"
  next_section_distance_factor :: "real"
  next_section_turn_distance_factor :: "real"
  printing_fun :: "bool \<Rightarrow> 'b \<Rightarrow> unit"
  tracing_fun :: "string \<Rightarrow> 'b option \<Rightarrow> unit"
  irect_mod :: "nat"
  max_intersection_step :: real
  reduce_number_factor :: real
  adaptive_atol :: real
  adaptive_rtol :: real
  adaptive_gtol :: real
  method_id :: nat

abbreviation "optns_rel \<equiv> (Id::('a, 'b) options rel)"

context begin interpretation autoref_syn .
lemma [autoref_rules]:
"(precision, precision)\<in>optns_rel \<rightarrow> nat_rel"
"(tolerance, tolerance)\<in>optns_rel \<rightarrow> eucl_rel"
"(stepsize, stepsize)\<in>optns_rel \<rightarrow> eucl_rel"
"(iterations, iterations)\<in> optns_rel\<rightarrow> nat_rel"
"(halve_stepsizes, halve_stepsizes)\<in> (optns_rel) \<rightarrow> nat_rel"
"(widening_mod, widening_mod)\<in> (optns_rel) \<rightarrow>nat_rel"
"(rk2_param, rk2_param)\<in> (optns_rel) \<rightarrow> eucl_rel"
"(max_tdev_thres, max_tdev_thres)\<in> (optns_rel) \<rightarrow> eucl_rel"
"(pre_split_summary_tolerance, pre_split_summary_tolerance)\<in> (optns_rel) \<rightarrow> eucl_rel"
"(reduce_summary_tolerance, reduce_summary_tolerance)\<in> (optns_rel) \<rightarrow> eucl_rel"
"(collect_granularity, collect_granularity)\<in> (optns_rel) \<rightarrow> eucl_rel"
"(start_section, start_section)\<in> (optns_rel) \<rightarrow> Id"
"(checkpoint_sections, checkpoint_sections)\<in> (optns_rel) \<rightarrow> \<langle>Id\<rangle>list_rel"
"(stop_sections, stop_sections)\<in> (optns_rel) \<rightarrow> \<langle>Id\<rangle>list_rel"
"(snap_sections, snap_sections)\<in> (optns_rel) \<rightarrow> eucl_rel"
"(min_section_distance, min_section_distance)\<in> (optns_rel) \<rightarrow> eucl_rel"
"(next_section_distance_factor, next_section_distance_factor)\<in> (optns_rel) \<rightarrow> eucl_rel"
"(next_section_turn_distance_factor, next_section_turn_distance_factor)\<in> (optns_rel) \<rightarrow> eucl_rel"
"(printing_fun, printing_fun)\<in> (optns_rel) \<rightarrow> bool_rel \<rightarrow> I \<rightarrow> unit_rel"
"(tracing_fun, tracing_fun)\<in> (optns_rel) \<rightarrow> string_rel \<rightarrow> \<langle>I\<rangle>option_rel \<rightarrow> unit_rel"
"(irect_mod, irect_mod)\<in> (optns_rel) \<rightarrow> nat_rel"
"(max_intersection_step, max_intersection_step)\<in> (optns_rel) \<rightarrow> eucl_rel"
"(adaptive_atol, adaptive_atol)\<in> (optns_rel) \<rightarrow> eucl_rel"
"(adaptive_rtol, adaptive_rtol)\<in> (optns_rel) \<rightarrow> eucl_rel"
"(adaptive_gtol, adaptive_gtol)\<in> (optns_rel) \<rightarrow> eucl_rel"
"(method_id, method_id)\<in> (optns_rel) \<rightarrow> nat_rel"
"(reduce_number_factor, reduce_number_factor) \<in> optns_rel \<rightarrow> eucl_rel"
by auto
end

definition cfuncset where "cfuncset l u X = funcset {l .. u} X \<inter> Collect (continuous_on {l .. u})"
lemma cfuncset_iff: "f \<in> cfuncset l u X \<longleftrightarrow> (\<forall>i\<in>{l .. u}. f i \<in> X) \<and> continuous_on {l .. u} f"
  unfolding cfuncset_def by auto

lemma cfuncset_continuous_onD: "f \<in> cfuncset 0 h X \<Longrightarrow> continuous_on {0..h} f"
  by (simp add: cfuncset_iff)

locale approximate_ivp =
  approximate_sets where optns = optns and apprs_rel = apprs_rel
  for apprs_rel :: "('b list \<times> 'a::executable_euclidean_space list set) set"
  and optns::"('a, 'b) options" +
  fixes ode::"'a \<Rightarrow> 'a"
  fixes safe::"'a \<Rightarrow> bool"
  fixes ode_euclarith::"nat \<Rightarrow> ('a, 'a) euclarith" \<comment>\<open>TODO: sbp?\<close>
  fixes safe_euclarithform::"nat \<Rightarrow> ('a, 'a) euclarithform"
(* TODO: fixes domain_euclarithform::"('a, 'a) euclarithform" *)
  assumes ode_euclarith: "i < length xs \<Longrightarrow> ode \<equiv> \<lambda>x. interpret_euclarith (ode_euclarith i) (xs[i:=x])"
  assumes safe_euclarithform: "i < length xs \<Longrightarrow> safe \<equiv> \<lambda>x. interpret_euclarithform (safe_euclarithform i) (xs[i:=x])"
  assumes fresh_euclarith_ode_euclarith: "i \<noteq> j \<Longrightarrow> fresh_euclarith (ode_euclarith i) j"
  assumes euclarith_ndiff:
    "x < length xs \<Longrightarrow> d1 < length xs \<Longrightarrow> d2 < length xs \<Longrightarrow> d3 < length xs \<Longrightarrow>
    distinct [x, d1, d2, d3] \<Longrightarrow>
    safe (xs ! x) \<Longrightarrow>
    isndiff_euclarith 3 (ode_euclarith x) x [d1, d2, d3] xs"
  assumes open_safe: "open (Collect safe)"
  assumes safe_nonempty: "Collect safe \<noteq> {}"
begin

definition print_set::"bool \<Rightarrow> 'a set \<Rightarrow> unit" where "print_set _ _ = ()"
sublocale autoref_op_pat_def print_set .
lemma print_set_impl[autoref_rules]: "(printing_fun optns, print_set) \<in> bool_rel \<rightarrow> \<langle>eucl_rel\<rangle>appr_rel \<rightarrow> Id"
  by auto

definition trace_set::"string\<Rightarrow>'a set option\<Rightarrow>unit" where "trace_set _ _ = ()"
sublocale autoref_op_pat_def trace_set .

lemma trace_set_impl[autoref_rules]: "(tracing_fun optns, trace_set) \<in> string_rel \<rightarrow> \<langle>\<langle>eucl_rel\<rangle>appr_rel\<rangle>option_rel \<rightarrow> Id"
  by auto

definition "ode_slp = (ode_euclarith 0 ;slp ReturnSLP [1])"
sublocale autoref_op_pat_def ode_slp .

lemma [autoref_rules]:
  "(ode_euclarith, ode_euclarith) \<in> Id"
  "(safe_euclarithform, safe_euclarithform) \<in> Id"
  "(ode_slp, ode_slp) \<in> Id"
  by auto

definition "ode_set X =
  do {
    env \<leftarrow> sings_spec X;
    env \<leftarrow> approx_slp_spec ode_slp env;
    (case env of
      Some env \<Rightarrow>
        do {
          r \<leftarrow> nth_image env 0;
          RETURN r
        }
    | None \<Rightarrow> do {
        let _ = trace_set (''ode_set failed'') (Some X);
        SUCCEED
      })
  }"
sublocale autoref_op_pat_def ode_set .

schematic_goal ode_set_impl:
  assumes [autoref_rules]: "(Xi, X) \<in> \<langle>eucl_rel\<rangle>appr_rel"
  shows "(?f, ode_set $ X) \<in> \<langle>\<langle>eucl_rel\<rangle>appr_rel\<rangle>nres_rel"
  unfolding ode_set_def[abs_def]
  by autoref_monadic

concrete_definition ode_set_impl for Xi uses ode_set_impl
lemmas [autoref_rules] = ode_set_impl.refine

lemma interpret_ode_set_slp:
  "interpret_slp ode_slp [x] = [ode x]"
  using ode_euclarith[of 0 "[0]"]
  by (auto simp: ode_slp_def)

lemma ode_set_spec[THEN order.trans, refine_vcg]:
  shows "ode_set X \<le> SPEC (\<lambda>r. ode ` X \<subseteq> r)"
  unfolding ode_set_def
  using interpret_ode_set_slp
  by (refine_vcg) (force simp: nth_image_precond_def)


definition "safe_set X = approx_euclarithform_spec (safe_euclarithform 0) X"
sublocale autoref_op_pat_def safe_set .

definition "safe_set_appr X = approx_euclarithform optns (safe_euclarithform 0) X"
lemma safe_set_appr[unfolded comps, autoref_rules]:
  shows "(nres_of o safe_set_appr, safe_set) \<in> \<langle>eucl_rel\<rangle>appr_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  by (auto simp add: appr_rel_def br_def nres_rel_def safe_set_appr_def comps safe_set_def
    approx_euclarithform[THEN fun_relD, unfolded in_nres_rel_iff, simplified])

lemma interpret_safe_euclarithform: "interpret_euclarithform (safe_euclarithform 0) (x#xs) = safe x"
  using safe_euclarithform[of 0 "0#xs"]
  by (auto simp: )

lemma safe_set_spec[THEN order.trans, refine_vcg]:
  shows "safe_set X \<le> SPEC (\<lambda>r. r \<longrightarrow> (\<forall>e\<in>X. safe (e)))"
  by (auto simp: safe_set_def approx_euclarithform_spec_def interpret_safe_euclarithform)


subsubsection \<open>first derivative\<close>

definition "ode_d_euclarith i j = derive_euclarith (ode_euclarith i) i j"
sublocale autoref_op_pat_def ode_d_euclarith .

lemma [autoref_rules]: "(ode_d_euclarith, ode_d_euclarith) \<in> Id" by simp

definition ode_d::"'a \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'a" where
  "ode_d x = Blinfun (\<lambda>dx. interpret_euclarith (ode_d_euclarith 0 1) [x, dx])"

lemma fresh_euclarith_ode_d_euclarith:
  shows "i \<noteq> j \<Longrightarrow> j \<noteq> k \<Longrightarrow> i \<noteq> k \<Longrightarrow> fresh_euclarith (ode_d_euclarith i j) k"
  unfolding ode_d_euclarith_def
  apply (rule fresh_euclarith_derive_realarith)
  by (auto intro!: fresh_euclarith_ode_euclarith)

lemma euclarith_diff1: "i < length xs \<Longrightarrow> safe (xs ! i) \<Longrightarrow> isdiff_euclarith (ode_euclarith i) xs"
  using euclarith_ndiff[of i "xs@[0, 0, 0]" "Suc i" "i + 2" "i + 3", simplified eval_nat_numeral, simplified]
  apply auto
  apply (rule isdiff_euclarith_freshI[where zs = "xs@[0, 0, 0]"])
  subgoal for j apply (case_tac "j = i")
    subgoal by (simp add: nth_append)
    subgoal by (simp add: fresh_euclarith_ode_euclarith)
    done
  by (simp add: nth_append)

lemma ode_has_derivative_derive_euclarith:
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> i \<noteq> j \<Longrightarrow>
    safe (xs ! i) \<Longrightarrow>
    (ode has_derivative (\<lambda>dx. interpret_euclarith (derive_euclarith (ode_euclarith i) i j) (xs[j := dx]))) (at (xs ! i))"
  apply (subst ode_euclarith[of i xs], force)
  apply (rule derive_euclarith[of "ode_euclarith i" j i xs, simplified])
  using euclarith_diff1
  by (simp_all add: fresh_euclarith_ode_euclarith)

lemma fderiv[derivative_intros]:
  "safe x \<Longrightarrow> (ode has_derivative ode_d x) (at x)"
  unfolding ode_d_def
  by (rule has_derivative_Blinfun)
    (auto simp: ode_d_euclarith_def ode_has_derivative_derive_euclarith[of 0 "[x, 0]" 1, simplified])

lemma interpret_ode_d_euclarith:
  assumes len: "i < length xs" "j < length xs" and ne: "i \<noteq> j" and safe: "safe (xs ! i)"
  shows "interpret_euclarith (ode_d_euclarith i j) xs = ode_d (xs ! i) (xs ! j)"
proof -
  note deriv1 = ode_has_derivative_derive_euclarith[OF assms]
  note deriv2 = ode_has_derivative_derive_euclarith[of 0 "[xs ! i, 0]" 1, simplified, OF safe]
  show ?thesis
    unfolding ode_d_def ode_d_euclarith_def
    apply (subst bounded_linear_Blinfun_apply)
    subgoal using deriv2 safe by (intro has_derivative_bounded_linear) force
    subgoal
      using has_derivative_unique[OF deriv1 deriv2, THEN fun_cong[where x="xs ! j"]]
      by simp
    done
qed

lemma ode_d_interpret_euclarith:
  fixes x
  assumes len: "i < length xs" "j < length xs" and ne: "i \<noteq> j" and safe: "safe x"
  shows "ode_d x y = interpret_euclarith (ode_d_euclarith i j) (xs[i:=x, j:=y])"
  apply (subst interpret_ode_d_euclarith)
  using assms
  by auto


subsubsection \<open>second derivative\<close>

definition "ode_d2_euclarith i j k = derive_euclarith (ode_d_euclarith i j) i k"
sublocale autoref_op_pat_def ode_d2_euclarith .

lemma [autoref_rules]: "(ode_d2_euclarith, ode_d2_euclarith) \<in> Id" by simp

definition ode_d2::"'a \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'a \<Rightarrow>\<^sub>L 'a" where
  "ode_d2 x = Blinfun (\<lambda>xa. Blinfun (\<lambda>i. interpret_euclarith (ode_d2_euclarith 0 1 2) [x, i, xa]))"

lemma fresh_ode_d2: "distinct [i, j, k, l] \<Longrightarrow> fresh_euclarith (ode_d2_euclarith i j k) l"
  unfolding ode_d2_euclarith_def
  apply (rule fresh_euclarith_derive_realarith)
  by (auto intro!: fresh_euclarith_ode_euclarith fresh_euclarith_ode_d_euclarith)

lemma euclarith_diff2: "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> i \<noteq> j \<Longrightarrow> safe (xs ! i) \<Longrightarrow>
  isdiff_euclarith (ode_d_euclarith i j) xs"
  using euclarith_ndiff[of i "xs@[0, 0]" "j" "length xs" "Suc (length xs)", simplified eval_nat_numeral, simplified]
  apply auto
  apply (rule isdiff_euclarith_freshI[where zs = "xs@[0, 0]"])
  subgoal for k apply (cases "k = i"; cases "k = j")
    subgoal by simp
    subgoal by (simp add: nth_append)
    subgoal by (simp add: nth_append)
    subgoal by (simp add: fresh_euclarith_ode_d_euclarith)
    done
  by (simp add: ode_d_euclarith_def nth_append)

lemma ode_d_has_derivative_euclarith:
  assumes "i < length xs" "j < length xs" "k < length xs" "i \<noteq> j" "i \<noteq> k" "j \<noteq> k" "safe (xs ! i)"
  shows "(ode_d has_derivative
    (\<lambda>dx2. Blinfun (\<lambda>dx. interpret_euclarith (derive_euclarith (ode_d_euclarith i j) i k) (xs[j := dx, k := dx2]))))
    (at (xs ! i))"
  using assms
  apply -
  apply (rule has_derivative_BlinfunI)
  apply (subst at_within_open[symmetric, where S="Collect safe"])
  subgoal by force
  subgoal by (rule open_safe)
  subgoal for dx
    apply (rule has_derivative_transform[OF _ ode_d_interpret_euclarith[of i xs j]])
    subgoal by force
    subgoal by force
    subgoal by force
    subgoal by force
    subgoal by force
    subgoal
      unfolding list_update_swap[OF \<open>i \<noteq> j\<close>]
      apply (subst at_within_open[OF _ open_safe], force)
      apply (rule
          derive_euclarith[of "ode_d_euclarith i j" k i "xs[j:=dx]",
            simplified nth_list_update_neq[OF \<open>i \<noteq> j\<close>[symmetric]], simplified])
      by (auto intro!: euclarith_diff2 fresh_ode_d2 fresh_euclarith_ode_d_euclarith)
    done
  done

lemma fderiv2[derivative_intros]:
  "safe x \<Longrightarrow> (ode_d has_derivative ode_d2 x) (at x)"
  unfolding ode_d2_def
  apply (rule has_derivative_Blinfun)
  unfolding ode_d2_euclarith_def
  using ode_d_has_derivative_euclarith[of 0 "[x, 0, 0]" 1 2]
  apply simp
  done

lemma euclarith_cont2:
  assumes "i < length xs" "j < length xs" "k < length xs"
    and "i \<noteq> j" "i \<noteq> k" "j \<noteq> k" "safe (xs ! i)"
  shows "isdiff_euclarith (ode_d2_euclarith i j k) xs"
  using euclarith_ndiff[of i "xs@[0]" j k "length xs"] assms
  apply -
  apply (rule isdiff_euclarith_freshI[of _ _ "xs @ [0]"])
  subgoal for l
    by (cases "i = l"; cases "j = l"; cases "k = l") (auto simp: nth_append fresh_ode_d2)
  subgoal by (force simp: ode_d2_euclarith_def ode_d_euclarith_def nth_append eval_nat_numeral)
  done

lemma blinfun_cong: "f = g \<Longrightarrow> blinfun_apply f x = blinfun_apply g x"
  by (rule arg_cong)

lemma interpret_ode_d2_euclarith:
  assumes "i < length xs" "j < length xs" "k < length xs"
    and "i \<noteq> j" "i \<noteq> k" "j \<noteq> k" "safe (xs ! i)"
  shows "interpret_euclarith (ode_d2_euclarith i j k) xs = ode_d2 (xs ! i) (xs ! j) (xs ! k)"
proof -
  interpret second_derivative ode ode_d "ode_d2 (xs ! i)" "(xs ! i)" "Collect safe"
    by unfold_locales (auto intro!: derivative_eq_intros assms interiorI[OF open_safe])
  have safe: "xs ! i \<in> Collect safe" using assms by auto
  moreover have "blinfun_apply (ode_d x) (xs ! j) = interpret_euclarith (ode_d_euclarith i j) (xs[i:=x])"
    if "safe x" for x
    by (auto simp: interpret_ode_d_euclarith assms that)
  ultimately have "((\<lambda>x. blinfun_apply (ode_d x) (xs ! j)) has_derivative
     (\<lambda>dx. interpret_euclarith (ode_d2_euclarith i j k) (xs[k := dx])))
     (at (xs ! i))"
     unfolding at_within_open[OF safe open_safe, symmetric]
     apply (rule has_derivative_transform)
     subgoal by force
     subgoal
       unfolding ode_d2_euclarith_def at_within_open[OF safe open_safe]
       by (rule derive_euclarith[of "ode_d_euclarith i j" k i xs, simplified])
          (auto intro!: fresh_euclarith_ode_d_euclarith euclarith_diff2 assms)
     done
  moreover
  have interior: "xs ! i \<in> interior (Collect safe)"
    by (auto intro!: interiorI open_safe safe)
  have "((\<lambda>x. blinfun_apply (ode_d x) (xs ! j)) has_derivative ode_d2 (xs ! i) (xs ! j)) (at (xs ! i))"
    using blinfun.FDERIV[of _ _ "xs ! i" UNIV, OF fderiv2[OF \<open>safe _\<close>] has_derivative_const[of "xs ! j"], simplified blinfun.bilinear_simps, simplified
      , simplified symmetric_second_derivative[OF interior, of _ "xs ! j"]]
    .
  ultimately
  have "interpret_euclarith (ode_d2_euclarith i j k) (xs[k:=xs!k]) = ode_d2 (xs ! i) (xs ! j) (xs ! k)"
    by (rule has_derivative_unique[THEN fun_cong[where x="xs ! k"]])
  then show ?thesis by simp
qed

lemma ode_d2_interpret_euclarith:
  assumes "i < length xs" "j < length xs" "k < length xs"
    and "i \<noteq> j" "i \<noteq> k" "j \<noteq> k" "safe x"
  shows "ode_d2 x y z = interpret_euclarith (ode_d2_euclarith i j k) (xs[i:=x, j:=y, k:=z])"
  apply (subst interpret_ode_d2_euclarith)
  using assms
  by auto

lemma derivative_within_safe[derivative_intros]:
  "(g has_derivative h) (at x) \<Longrightarrow> (g has_derivative h) (at x within Collect safe)"
  by (rule has_derivative_at_within)

lemma cont_fderiv2: "continuous_on (Collect safe) ode_d2"
proof -
  have "isCont (\<lambda>x. blinfun_apply (blinfun_apply (ode_d2 x) i) j) x"
    if "i \<in> Basis" "j \<in> Basis" "safe x"
    for i j x
  proof -
    have D: "((\<lambda>x. interpret_euclarith (ode_d2_euclarith 0 (Suc 0) 2) [x, i, j, 0])
      has_derivative
      (\<lambda>dx. interpret_euclarith (derive_euclarith (ode_d2_euclarith 0 1 2) 0 3) [x, i, j, dx]))
      (at x)"
      (is "(?f has_derivative ?f') _")
      using that derive_euclarith[of "ode_d2_euclarith 0 1 2" 3 0 "[x, i, j, 0]"]
      by (auto simp: fresh_ode_d2 euclarith_cont2)
    show ?thesis
      using that
      apply (intro has_derivative_continuous[where f'="?f'"])
      subgoal
        apply (subst at_within_open[symmetric, OF _ open_safe], force)
        apply (rule has_derivative_transform[where f = "?f"])
        subgoal by force
        subgoal
          by (rule ode_d2_interpret_euclarith[of 0 "[x, i, j, 0]" 1 2 for x i j, simplified]) simp
        subgoal apply (rule derivative_within_safe)
          apply (rule D)
          done
        done
      done
  qed
  then show ?thesis
    by (auto intro!: continuous_at_imp_continuous_on continuous_blinfun_componentwiseI1)
qed

lemma cont_fderiv: "continuous_on (Collect safe) ode_d"
  by (rule has_derivative_continuous_on) (auto intro!: derivative_intros)

lemmas cont_fderiv'[continuous_intros] = continuous_on_compose2[OF cont_fderiv]
lemmas cont_fderiv2'[continuous_intros] = continuous_on_compose2[OF cont_fderiv2]

lemma continuous_on_ode1:
  "continuous_on (Collect safe) ode"
  using fderiv
  by (auto intro!: has_derivative_continuous_on derivative_intros)

lemma continuous_on_ode[continuous_intros]:
  "continuous_on s g \<Longrightarrow> (\<And>x. x \<in> s \<Longrightarrow> safe (g x)) \<Longrightarrow> continuous_on s (\<lambda>x. ode (g x))"
  using continuous_on_ode1
  by (rule continuous_on_subset_comp) auto

lemma fderiv'[derivative_intros]:
  assumes "(g has_derivative g' y) (at y within X)"
  assumes "safe (g y)"
  shows "((\<lambda>y. ode (g y)) has_derivative
    (blinfun_apply (ode_d (g y)) \<circ>\<circ> g') y) (at y within X)"
  using diff_chain_within[OF assms(1) has_derivative_within_subset[OF fderiv]] assms(2)
  by (simp add: o_def)

lemma fderiv2'[derivative_intros]:
  assumes "(g has_derivative g' y) (at y within X)"
  assumes "safe (g y)"
  shows "((\<lambda>y. ode_d (g y)) has_derivative
    (blinfun_apply (ode_d2 (g y)) \<circ>\<circ> g') y) (at y within X)"
  using diff_chain_within[OF assms(1) has_derivative_within_subset[OF fderiv2]] assms(2)
  by (simp add: o_def)

sublocale c1_on_open_euclidean ode ode_d "Collect safe"
  using cont_fderiv
  by unfold_locales
    (auto simp: continuous_on_eq_continuous_within at_within_open[symmetric]
      intro!: derivative_eq_intros cont_fderiv continuous_at_imp_continuous_on open_safe
      continuous_blinfun_componentwiseI)

sublocale auto_ll_on_open_euclidean ode "Collect safe" by unfold_locales


subsubsection \<open>implementation of function space\<close>

definition appr_cfuncset_rel :: "((real \<times> real \<times> 'a \<times> 'a) \<times> (real \<Rightarrow> 'a) set) set"
where "appr_cfuncset_rel = br (\<lambda>(l, u, a, b). cfuncset l u {a .. b}) top"

definition "const_fun_bound l u F = SPEC (\<lambda>X. compact X \<and> F \<subseteq> cfuncset l u X)"
lemmas [refine_vcg] = const_fun_bound_def[THEN eq_refl, THEN order_trans]

definition [symmetric, autoref_op_pat_def]: "icfuncset l u a b \<equiv> cfuncset l u {a .. b}"
sublocale autoref_op_pat_def icfuncset .
lemma cfuncset_impl[autoref_rules]:
  assumes "PREFER_id R"
  assumes "PREFER_id S"
  shows "((\<lambda>l u a b. (l, u, a, b)), icfuncset) \<in> R \<rightarrow> R \<rightarrow> S \<rightarrow> S \<rightarrow> appr_cfuncset_rel"
  using assms
  by (auto simp: appr_cfuncset_rel_def appr_rel_def br_def icfuncset_def)

lemma const_fun_bound_impl[autoref_rules]:
  assumes "PREFER_id R"
  shows "(\<lambda>l u (l', u', a, b). if l' \<le> l \<and> u \<le> u' then RETURN (appr_of_ivl a b) else SUCCEED, const_fun_bound)
    \<in> R \<rightarrow> R \<rightarrow> appr_cfuncset_rel \<rightarrow> \<langle>\<langle>eucl_rel\<rangle>appr_rel\<rangle> nres_rel"
  using assms transfer_operations(1)[]
  by (auto simp: cfuncset_iff const_fun_bound_def appr_cfuncset_rel_def br_def nres_rel_def
    appr_rel_def Pi_iff set_of_appr_compact continuous_on_subset
    intro!: RETURN_SPEC_refine intro: continuous_on_subset)
    (metis atLeastAtMost_iff order.trans)

lemmas [refine_vcg] = const_fun_bound_def[THEN eq_refl, THEN order_trans]

subsubsection \<open>step of Picard iteration\<close>

definition
  "Picard_step X0 t0 h X = SPEC (\<lambda>R.
    case R of
      Some R \<Rightarrow>
        compact R \<and> (\<forall>r \<in> R. safe r) \<and>
        (\<forall>x0 \<in> X0. \<forall>h'\<in>{t0 .. t0 + h}. \<forall>phi\<in>cfuncset t0 h' X.
          x0 + integral {t0 .. h'} (\<lambda>t. ode (phi t)) \<in> R)
      | None \<Rightarrow> True)"
sublocale autoref_op_pat_def Picard_step .

lemmas [refine_vcg] = Picard_step_def[THEN eq_refl, THEN order.trans]

text \<open>TODO: Euler/RK as approximation for Picard?!\<close>

lemma interpret_ode_euclarith: "i < length xs \<Longrightarrow> interpret_euclarith (ode_euclarith i) xs = ode (xs ! i)"
  using ode_euclarith[of i xs]
  by (auto simp: )

definition "Picard_step_slp =
  (
  ode_euclarith 2 ;slp
  scaleR_eas 1 3 ;slp
  add_ea 0 4 ;slp
  ReturnSLP [5])"
sublocale autoref_op_pat_def Picard_step_slp .

lemma interpret_Picard_step_slp:
  "interpret_slp Picard_step_slp [x0, h, x] = [x0 + (roe h) *\<^sub>R ode x]"
  by (simp add: interpret_ode_euclarith Picard_step_slp_def roe_def)

definition Picard_step_ivl :: "'a set \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a set \<Rightarrow> 'a set option nres" where
  "Picard_step_ivl X0 t0 h X = do {
    ASSERT (0 \<le> h);
    let H = {eor 0  .. eor h};
    let env = listset [X0, H, X];
    env \<leftarrow> approx_slp_spec Picard_step_slp env;
    (case env of
      Some env \<Rightarrow>
        do {
          E_set \<leftarrow> nth_image env 0;
          (l, u) \<leftarrow> ivl_of_set E_set;
          ASSERT (l \<le> u);
          r \<leftarrow> safe_set {l .. u};
          CHECK r;
          RETURN (Some {l .. u})
        }
    | None \<Rightarrow> RETURN None)
  }"

lemma Basis_list_zero_mem_Basis[simp]:
  "Basis_list ! 0 \<in> Basis"
  unfolding Basis_list[symmetric]
  apply (rule nth_mem)
  apply (rule length_Basis_list_pos)
  done

lemma cfuncset_empty_iff:
  fixes l u::"'d::ordered_euclidean_space"
  shows "l \<le> u \<Longrightarrow> cfuncset l u X = {} \<longleftrightarrow> X = {}"
  unfolding cfuncset_def Pi_def
proof (safe, goal_cases)
  case hyps: (1 x)
  from \<open>x \<in> X\<close>
  have "(\<lambda>_. x) \<in> {f. \<forall>x. x \<in> {l..u} \<longrightarrow> f x \<in> X} \<inter> Collect (continuous_on {l..u})"
    by (auto intro!: continuous_on_const)
  then show ?case using hyps by auto
qed auto

lemma Picard_step_ivl_refine:
  assumes "\<And>x. x \<in> X \<Longrightarrow> safe x"
  assumes "0 \<le> h"
  shows "Picard_step_ivl X0 t0 h X \<le> Picard_step X0 t0 h X"
proof -
  have *: "(t'' - t0) *\<^sub>R ode (phi t') \<in> {l - x0..u - x0}"
    if "\<forall>e\<in>X0. \<forall>b\<in>{0..h}. \<forall>ba\<in>X. [e + b *\<^sub>R ode ba] \<in> E"
    "h' \<in> {t0..t0 + h}"
    "phi \<in> funcset {t0..h'} X"
    "t'' \<in> {t0..h'}"
    "t' \<in> {t0..h'}"
    "x0 \<in> X0"
    "(\<lambda>x. x ! 0) ` E \<subseteq> {l .. u}"
    for phi x0 h' t'' t' E l u
  proof -
    from that have "x0 + (t'' - t0) *\<^sub>R ode (phi t') \<in> (\<lambda>x. x ! 0) ` E"
      by (auto simp: Pi_iff intro!: image_eqI[OF _ that(1)[rule_format, OF \<open>x0 \<in> X0\<close> _ , of "(t'' - t0)" "phi t'"]])
    also note \<open>\<dots> \<subseteq> {l .. u}\<close>
    finally show ?thesis by (auto simp: algebra_simps)
  qed
  have "h' \<in> {t0..t0 + h} \<Longrightarrow> t0 \<le> h'" for h' by simp
  then show ?thesis
    using cfuncset_empty_iff[of t0 "t0 + h", where 'c='a] \<open>0 \<le> h\<close>
    unfolding Picard_step_ivl_def Picard_step_def
    by (refine_vcg)
      (auto simp: interpret_Picard_step_slp cfuncset_def compact_interval
        simp del: atLeastAtMost_iff
        intro: continuous_on_subset assms *
        intro!: add_integral_ivl_bound
        integrable_continuous_real continuous_intros indefinite_integral_continuous)
qed

lemma
  independent_appr:
  shows "set_Cons (set_of_appr B) (set_of_apprs BS) = set_of_apprs (appr_Cons B BS)"
proof -
  have "(B, set_of_appr B) \<in> \<langle>eucl_rel\<rangle>appr_rel"
    "(BS, set_of_apprs BS) \<in> apprs_rel"
    by (auto simp: appr_rel_def apprs_rel_def br_def)
  note * = transfer_operations(2)[THEN fun_relD, THEN fun_relD, OF this]
  from this show ?thesis
    by (auto simp: apprs_rel_def br_def Id_def)
qed

primrec independent_apprs where
  "independent_apprs [] xs = xs"
| "independent_apprs (y#ys) xs = appr_Cons y (independent_apprs ys xs)"
sublocale autoref_op_pat_def independent_apprs .

lemma independent_apprs_listset_append:
  assumes "set_of_apprs ys = listset (map set_of_appr ys)"
  shows "set_of_apprs (independent_apprs xs ys) = listset (map set_of_appr (xs @ ys))"
  using assms
  by (induction xs arbitrary: ys) (auto simp: independent_appr[symmetric] set_Cons_def)

lemma independent_apprs_listset_append_Nil:
  shows "set_of_apprs (independent_apprs xs []) = listset (map set_of_appr xs)"
  by (induction xs) (auto simp: independent_appr[symmetric] set_Cons_def)

lemma list_all2_set_of_appr_listset1:
  assumes "list_all2 (\<lambda>x x'. x' = set_of_appr x) a a'" "x \<in> listset a'"
  shows "x \<in> listset (map set_of_appr a)"
proof - \<comment>\<open>thank you s/h\<close>
  have f3: "list_all2 (\<lambda>A Aa. Aa = A) (map set_of_appr a) a'"
    using assms(1) list.rel_map(1) by blast
  obtain AA :: "('a set \<Rightarrow> 'a set \<Rightarrow> bool) \<Rightarrow> ('a set \<Rightarrow> 'a set \<Rightarrow> bool) \<Rightarrow> 'a set"
    and AAa :: "('a set \<Rightarrow> 'a set \<Rightarrow> bool) \<Rightarrow> ('a set \<Rightarrow> 'a set \<Rightarrow> bool) \<Rightarrow> 'a set"
    where f4: "\<And>p As Asa pa Asb Asc.
      (\<not> list_all2 p As Asa \<or> p (AA p pa) (AAa p pa) \<or> list_all2 pa As Asa) \<and>
      (\<not> pa (AA p pa) (AAa p pa) \<or> \<not> list_all2 p Asb Asc \<or> list_all2 pa Asb Asc)"
    by (metis (no_types) list_all2_mono)
  then have "\<And>p. AAa (\<lambda>A Aa. Aa = A) p = AA (\<lambda>A Aa. Aa = A) p \<or> list_all2 p (map set_of_appr a) a'"
    using f3 by meson
  then show ?thesis
    using f4 f3 assms(2) by (metis (no_types) list_all2_eq)
qed

lemma list_all2_set_of_appr_listset2:
  assumes "list_all2 (\<lambda>x x'. x' = set_of_appr x) a a'" "x \<in> listset (map set_of_appr a)"
  shows "x \<in> listset a'"
proof - \<comment>\<open>thank you s/h\<close>
  have f3: "list_all2 (\<lambda>A Aa. Aa = A) (map set_of_appr a) a'"
    using assms(1) by (simp add: list.rel_map(1))
  obtain AA :: "('a set \<Rightarrow> 'a set \<Rightarrow> bool) \<Rightarrow> ('a set \<Rightarrow> 'a set \<Rightarrow> bool) \<Rightarrow> 'a set"
    and AAa :: "('a set \<Rightarrow> 'a set \<Rightarrow> bool) \<Rightarrow> ('a set \<Rightarrow> 'a set \<Rightarrow> bool) \<Rightarrow> 'a set"
    where f4: "\<And>p As Asa pa Asb Asc.
      (\<not> list_all2 p As Asa \<or> p (AA p pa) (AAa p pa) \<or> list_all2 pa As Asa) \<and>
      (\<not> pa (AA p pa) (AAa p pa) \<or> \<not> list_all2 p Asb Asc \<or> list_all2 pa Asb Asc)"
    by (metis (no_types) list_all2_mono)
  then have "AA (\<lambda>A Aa. Aa = A) op = = AAa (\<lambda>A Aa. Aa = A) op = \<or> map set_of_appr a = a'"
    using f3 list_all2_eq by blast
  then show ?thesis
    using f4 f3 assms(2) by (metis (no_types) list_all2_eq)
qed

lemma listset_implementation[autoref_rules]:
  "(\<lambda>x. independent_apprs x [], listset) \<in> \<langle>\<langle>eucl_rel\<rangle>appr_rel\<rangle>list_rel \<rightarrow> apprs_rel"
  by (auto simp: list_rel_def appr_rel_def apprs_rel_def br_def independent_apprs_listset_append_Nil
      list_all2_set_of_appr_listset1 list_all2_set_of_appr_listset2)

schematic_goal Picard_step_impl:
  fixes h::real
  assumes "SIDE_PRECOND (\<forall>phi \<in> PHI. safe phi)"
  assumes nonneg_step: "SIDE_PRECOND (0 \<le> h)"
  assumes [autoref_rules]: "(X0i,X0)\<in>\<langle>eucl_rel\<rangle>appr_rel" "(hi, h) \<in> Id" "(t0i, t0) \<in> Id" "(PHIi,PHI)\<in>\<langle>eucl_rel\<rangle>appr_rel"
  notes [autoref_rules] = IdI[of Picard_step_slp] roe_impl eor_impl
  shows "(?f::?'r, Picard_step $ X0 $ t0 $ h $ PHI) \<in> ?R"
  unfolding autoref_tag_defs
  apply (rule nres_rel_trans2)
   apply (rule Picard_step_ivl_refine)
  using assms apply force
  using assms apply force
  unfolding Picard_step_ivl_def
  by (autoref_monadic)

concrete_definition  Picard_step_impl for X0i t0i hi PHIi uses Picard_step_impl
lemmas [autoref_rules] = Picard_step_impl.refine


subsubsection \<open>Picard iteration\<close>

lemma subset_spec_cfuncset[unfolded split_beta', autoref_rules]:
  "((\<lambda>(l, u, a, b) (l', u', a', b'). nres_of (if l \<le> l' \<and> u' \<le> u then dRETURN (a' \<le> a \<and> b \<le> b') else dSUCCEED)),
    subset_spec) \<in>
  appr_cfuncset_rel \<rightarrow> appr_cfuncset_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  apply (auto simp: appr_cfuncset_rel_def br_def nres_rel_def subset_spec_def cfuncset_def Pi_iff
    continuous_on_subset)
  apply (metis atLeastAtMost_iff inf.coboundedI2 inf.orderE)
  apply (metis atLeastAtMost_iff inf.coboundedI2 inf.orderE)
  done

primrec P_iter::"'a set \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> ('a) set \<Rightarrow> ('a) set option nres" where
  "P_iter X0 h 0 X = do {
    let _ = trace_set (''P_iter failed (0)'') (Some X);
    RETURN None
  }"
| "P_iter X0 h (Suc i) X = do {
    ASSERT (0 \<le> h);
    (l, u) \<leftarrow> ivl_of_set X;
    ASSERT (l \<le> u);
    s \<leftarrow> safe_set {l .. u};
    CHECK s;
    ASSERT (\<forall>x \<in> {l .. u}. safe x);
    X' \<leftarrow> Picard_step X0 0 h {l .. u};
    (case X' of
      Some X' \<Rightarrow> do {
        (l', u') \<leftarrow> ivl_of_set X';
        let l' = inf l' l - (if i mod (widening_mod optns) = 0 then abs (l' - l) else 0);
        let u' = sup u' u + (if i mod widening_mod optns = 0 then abs (u' - u) else 0);
        ASSERT (l' \<le> u');
        s \<leftarrow> safe_set {l' .. u'};
        CHECK s;
        ASSERT (\<forall>x \<in> {l' .. u'}. safe x);
        ASSUME (ncc {l' .. u'});
        if (l \<le> l' \<and> u' \<le> u) then RETURN (Some {l .. u})
        else P_iter X0 h i {l' .. u'}
      }
    | None \<Rightarrow> do {
        let _ = trace_set (''P_iter failed (Picard_step)'') (Some X);
        RETURN None
      }
    )
  }"
sublocale autoref_op_pat_def P_iter .

lemma [autoref_rules]:
  "(abs, abs) \<in> eucl_rel \<rightarrow> eucl_rel"
  by simp_all

lemma inf_le_supI[simp]:
  fixes a b c d::"'d::ordered_euclidean_space"
  shows
    "a \<le> c \<Longrightarrow> inf a b \<le> sup c d"
    "a \<le> d \<Longrightarrow> inf a b \<le> sup c d"
    "b \<le> c \<Longrightarrow> inf a b \<le> sup c d"
    "b \<le> d \<Longrightarrow> inf a b \<le> sup c d"
  by (auto simp: eucl_le[where 'a='d] eucl_inf[where 'a='d] eucl_sup[where 'a='d] inf_real_def sup_real_def
    intro!: setsum_mono scaleR_right_mono)

schematic_goal P_iter_impl:
  fixes h::real and i::nat
  assumes [autoref_rules]: "(X0i,X0)\<in>\<langle>eucl_rel\<rangle>appr_rel" "(PHIi,PHI)\<in>\<langle>eucl_rel\<rangle>appr_rel" "(hi, h) \<in> Id" "(i_i, i) \<in> Id"
  shows "(nres_of (?f::?'r dres), P_iter $ X0 $ h $ i $ PHI) \<in> ?R"
  unfolding P_iter_def autoref_tag_defs uncurry_rec_nat
  by autoref_monadic

concrete_definition P_iter_impl for X0i hi i_i PHIi uses P_iter_impl
lemmas [autoref_rules] = P_iter_impl.refine

lemma ncc_interval: "ncc {a .. b::'a} \<longleftrightarrow> a \<le> b"
  by (auto simp: ncc_def compact_interval convex_closed_interval)

lemma P_iter_spec[THEN order_trans, refine_vcg]:
  assumes "DEFER (\<lambda>PHI. \<forall>phi \<in> PHI. safe phi) PHI"
  assumes "DEFER (\<lambda>h. 0 \<le> h) h"
  shows "P_iter X0 h i PHI \<le>
    SPEC (\<lambda>r. case r of
        None \<Rightarrow> True
      | Some PHI' \<Rightarrow> ncc PHI' \<and> (\<exists>PHI'' \<subseteq> PHI'. RETURN (Some PHI'') \<le> Picard_step X0 0 h PHI'))"
  using assms[unfolded autoref_tag_defs]
proof (induction i arbitrary: PHI)
  case 0 then show ?case
    unfolding P_iter.simps
    by refine_vcg
next
  case (Suc i)
  show ?case
    unfolding P_iter.simps
    apply (refine_vcg Suc)
    subgoal by (auto simp: cfuncset_iff Picard_step_def algebra_simps add_increasing2)
    subgoal for lu l u b CX CX' lu' l' u' b'
      apply (simp add: ncc_interval Picard_step_def)
      apply (safe intro!: exI[where x="{l .. u}"] compact_interval)
      apply (rule set_mp[of CX' "{l .. u}"])
      subgoal
        apply (rule order_trans, assumption)
        unfolding atLeastatMost_subset_iff
        apply (rule disjI2)
        apply (rule conjI)
        subgoal
          by (rule order_trans[where y="inf l' l - (if i mod widening_mod optns = 0 then \<bar>l' - l\<bar> else 0)"])
            (simp_all split: if_split_asm add: algebra_simps add_increasing2)
        subgoal
          apply (split if_split_asm)
          apply (rule order_trans[where y="sup u' u + \<bar>u' - u\<bar>"])
          by (auto split: if_split_asm simp add: algebra_simps add_increasing2)
        done
      subgoal by force
      done
    done
qed


subsubsection \<open>iterate step size\<close>

context fixes m::"('a set \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a set \<Rightarrow> ('a set \<times> 'c) option nres)"
begin

primrec cert_stepsize::
  "'a set \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (real \<times> 'a set \<times> 'a set \<times> 'c) nres"
where
  "cert_stepsize X0 h n 0 = do { let _ = trace_set (''cert_stepsize failed'') (Some X0); SUCCEED}"
| "cert_stepsize X0 h n (Suc i) = do {
    (l, u) \<leftarrow> ivl_of_set X0;
    ASSERT (0 \<le> h);
    ASSERT (l \<le> u);
    safe \<leftarrow> safe_set {l .. u};
    CHECK safe;
    X' \<leftarrow> P_iter X0 h n {l .. u};
    case X' of Some X' \<Rightarrow>
      do {
        safe \<leftarrow> safe_set X';
        ASSUME (ncc X');
        if safe
        then do {
          r1 \<leftarrow> m X0 h h X';
          r2 \<leftarrow> m X0 0 h X';
          (case (r1, r2) of
            (Some (res, err), Some (res_ivl, _)) \<Rightarrow> RETURN (h, res, res_ivl, err)
          | _ \<Rightarrow>
              do {
                let _ = trace_set (''cert_stepsize method failed'') (Some X');
                cert_stepsize X0 (h / 2) n i
              }
         )}
        else do {
          let _ = trace_set (''cert_stepsize not safe: '') (Some X');
          cert_stepsize X0 (h / 2) n i
        }
      }
    | None \<Rightarrow> cert_stepsize X0 (h / 2) n i
    }"
end
sublocale autoref_op_pat_def cert_stepsize .

schematic_goal cert_stepsize_impl_nres:
  fixes h::real and i n::nat
  assumes [autoref_rules]:
    "(mi, m)\<in>(\<langle>eucl_rel\<rangle>appr_rel \<rightarrow> eucl_rel \<rightarrow> eucl_rel \<rightarrow> \<langle>eucl_rel\<rangle>appr_rel \<rightarrow> \<langle>\<langle>\<langle>eucl_rel\<rangle>appr_rel \<times>\<^sub>r R\<rangle> option_rel\<rangle>nres_rel)"
    "(X0i,X0)\<in>\<langle>eucl_rel\<rangle>appr_rel" "(hi, h) \<in> eucl_rel" "(ni, n) \<in> nat_rel" "(i_i, i) \<in> nat_rel"
  shows "(?f::?'r nres, cert_stepsize $ m $ X0 $ h $ n $ i) \<in> ?R"
  unfolding cert_stepsize_def uncurry_rec_nat autoref_tag_defs
  by autoref
concrete_definition cert_stepsize_impl_nres for mi X0i hi ni i_i uses cert_stepsize_impl_nres
lemmas [autoref_rules] = cert_stepsize_impl_nres.refine

schematic_goal cert_stepsize_impl_dres[refine_transfer]:
  assumes [refine_transfer]: "\<And>a b c d. nres_of (m a b c d) \<le> m' a b c d"
  shows "nres_of ?f \<le> cert_stepsize_impl_nres m' x h n i"
  unfolding cert_stepsize_impl_nres_def
  by (refine_transfer)

concrete_definition cert_stepsize_impl_dres for m x h n i uses cert_stepsize_impl_dres
lemmas [refine_transfer] = cert_stepsize_impl_dres.refine

lemma Ball_cfuncset_continuous_on:
  "\<forall>f\<in>cfuncset a b X. continuous_on {a..b} f"
  by (simp add: cfuncset_iff)

definition "one_step_method m \<longleftrightarrow> (\<forall>X0 CX hl hu. ncc CX \<longrightarrow> CX \<subseteq> Collect safe \<longrightarrow> (m X0 hl hu CX \<le>
    SPEC (\<lambda>r. case r of None \<Rightarrow> True | Some (res, err) \<Rightarrow> ncc res \<and> res \<subseteq> Collect safe \<and>
      (\<forall>x0 \<in> X0. \<forall>h \<in> {hl .. hu}. safe x0 \<longrightarrow> h \<ge> 0 \<longrightarrow> h \<in> existence_ivl0 x0 \<longrightarrow>
      (\<forall>h' \<in> {0 .. h}. flow0 x0 h' \<in> CX) \<longrightarrow> x0 + h *\<^sub>R ode x0 \<in> CX \<longrightarrow> flow0 x0 h \<in> res))))"

lemmas one_step_methodD = one_step_method_def[THEN iffD1, rule_format, THEN order_trans]
lemmas one_step_methodI = one_step_method_def[THEN iffD2, rule_format]

lemma cert_stepsize_spec[THEN order_trans,refine_vcg]:
  assumes "DEFER_tag (h \<ge> 0)"
  assumes "one_step_method m"
  shows "cert_stepsize m X0 h i n \<le> SPEC (\<lambda>(h', RES, RES_ivl, _). h' \<le> h \<and> flowpipe X0 h' h' RES_ivl RES)"
  using assms(1)[unfolded autoref_tag_defs]
proof (induction n arbitrary: h)
  case 0 then show ?case by simp
next
  case (Suc n)
  note [refine_vcg] = Suc.IH[of "h/2", THEN order_trans]
  show ?case
    unfolding cert_stepsize.simps
    using Suc.prems
    apply (refine_vcg Ball_cfuncset_continuous_on one_step_methodD[OF assms(2)])
    apply (clarsimp)
    subgoal premises prems for l u b1 PHI' b2 RES RES_ivl PHI''
    proof -
      from prems
      have Ps: "RETURN (Some PHI'') \<le> Picard_step X0 0 h PHI'"
        by simp
      from Ps have PHI':
        "compact PHI''" "PHI'' \<subseteq> Collect safe"
        "\<forall>x\<in>PHI''. safe x"
        "\<And>x0 h'' phi. x0 \<in> X0 \<Longrightarrow> 0 \<le> h'' \<Longrightarrow> h'' \<le> h \<Longrightarrow> phi \<in> cfuncset 0 h'' PHI' \<Longrightarrow>
        x0 + integral {0..h''} (\<lambda>t. ode (phi t)) \<in> PHI''"
        by (auto simp: Picard_step_def)
      then obtain cx where cx: "(\<lambda>t::real. cx) \<in> cfuncset 0 0 PHI'"
        using \<open>PHI'' \<subseteq> PHI'\<close> \<open>ncc PHI'\<close> by (auto simp: cfuncset_def continuous_on_const ncc_def)
      show "flowpipe X0 h h RES_ivl RES"
        unfolding flowpipe_def atLeastAtMost_singleton
      proof safe
        show "0 \<le> h" by fact
        show safe_X0: "safe x" if "x \<in> X0" for x using that \<open>Ball {l..u} safe\<close> \<open>X0 \<subseteq> {l..u}\<close> by blast
        show "safe x" if "x \<in> RES_ivl" for x using prems that by auto
        show "safe x" if "x \<in> RES" for x using prems that by auto
        fix x0 assume "x0 \<in> X0"
        from PHI'(4)[OF \<open>x0 \<in> X0\<close> order_refl \<open>0 \<le> h\<close> cx]
        have "x0 \<in> PHI''" by simp
        have *: "h \<in> existence_ivl0 x0" "s \<in> {0 .. h} \<Longrightarrow> flow0 x0 s \<in> PHI''" for s
          using \<open>x0 \<in> X0\<close> \<open>PHI'' \<subseteq> PHI'\<close> \<open>0 \<le> h\<close> PHI'(3) \<open>x0 \<in> PHI''\<close>
          by (auto
              simp: cfuncset_def Pi_iff closed_segment_real ivl_integral_def
              intro!: Picard_iterate_mem_existence_ivlI[OF UNIV_I _ UNIV_I \<open>compact PHI''\<close>
                \<open>x0 \<in> PHI''\<close> \<open>PHI'' \<subseteq> Collect safe\<close>] PHI'(4)) force+
        show h_ex: "h \<in> existence_ivl0 x0" by fact
        have cf: "(\<lambda>t::real. x0) \<in> cfuncset 0 h PHI'" for h
          using \<open>x0 \<in> PHI''\<close> \<open>PHI'' \<subseteq> PHI'\<close>
          by (auto simp: cfuncset_def continuous_intros)
        have mem_PHI': "x0 + h' *\<^sub>R ode x0 \<in> PHI'" if "0 \<le> h'" "h' \<le> h" for h'
          using that \<open>PHI'' \<subseteq> PHI'\<close> PHI'(4)[OF \<open>x0 \<in> X0\<close> that cf]
          by auto
        from this prems \<open>Ball PHI' safe\<close>  safe_X0
        show "flow0 x0 h \<in> RES"
          using \<open>0 \<le> h\<close> h_ex * \<open>PHI'' \<subseteq> PHI'\<close> \<open>x0 \<in> X0\<close>
          by (auto simp: subset_iff dest!: bspec[where x=x0])
        fix h' assume h': "h' \<in> {0..h}"
        then have "h' \<in> existence_ivl0 x0"
          using Suc.prems h_ex local.in_existence_between_zeroI real_Icc_closed_segment by blast
        from h' this prems \<open>Ball PHI' safe\<close>  safe_X0
        show "flow0 x0 h' \<in> RES_ivl"
          using \<open>0 \<le> h\<close> h_ex * \<open>PHI'' \<subseteq> PHI'\<close> \<open>x0 \<in> X0\<close> mem_PHI' \<open>x0 \<in> PHI''\<close>
          by (auto simp: subset_iff dest!: bspec[where x=x0])
      qed
    qed
    done
qed


subsubsection \<open>Euler step\<close>

definition "euler_incr_slp =
                           (* 0 = X0                             *)
                           (* 1 = h                              *)
                           (* 2 = CX                             *)
  (
  ode_euclarith 0     ;slp (* 3 = ODE X0                         *)
  scaleR_eas 1 3      ;slp (* 4 = h * ODE X0                     *)
  add_ea 0 4          ;slp (* 5 = X0 + h * ODE X0                *)
  ode_euclarith 2     ;slp (* 6 = ODE CX                         *)
  ode_d_euclarith 2 6 ;slp (* 7 = ODE' CX (ODE CX)               *)
  hadamard_ea 1 1     ;slp (* 8 = h*h                            *)
  scaleQ_eas 8 2 7    ;slp (* 9 = (h*h / 2) * ODE' CX (ODE CX)   *)
  add_ea 5 9          ;slp (* 10 = 5 + 9                         *)
  ReturnSLP [10, 9]
  )"
sublocale autoref_op_pat_def euler_incr_slp .

lemma autoref_euler_incr_slp[autoref_rules]: "(euler_incr_slp, euler_incr_slp) \<in> Id"
  by (rule IdI)

lemma interpret_euler_incr_slp:
  assumes "safe CX"
  shows "interpret_slp (euler_incr_slp) [X0, h, CX] =
    (let h = roe h in
    [X0 + h *\<^sub>R ode X0 + (h^2 / 2) *\<^sub>R ode_d CX (ode CX), (h^2 / 2) *\<^sub>R ode_d CX (ode CX)])"
  by (auto simp: euler_incr_slp_def interpret_ode_euclarith interpret_ode_d_euclarith roe_def
    Let_def power2_eq_square algebra_simps assms hadamard_inner_Basis)

definition "one_step X0 h m = do {
  CHECK (0 \<le> h);
  (h, res, res_ivl, err) \<leftarrow> cert_stepsize m X0 h (iterations optns) (halve_stepsizes optns);
  ASSERT (0 \<le> h);
  width \<leftarrow> width_spec err;
  s1 \<leftarrow> safe_set res;
  s2 \<leftarrow> safe_set res_ivl;
  CHECK s1;
  CHECK s2;
  ASSUME (ncc res_ivl);
  ASSUME (ncc res);
  RETURN (h, width, res_ivl, res)
  }"
sublocale autoref_op_pat_def euler_step .

definition "euler_step X0 h = one_step X0 h (\<lambda>X0 hl hu CX.
   do {
    env \<leftarrow> approx_slp_spec euler_incr_slp (listset [X0, {eor (min hl hu) .. eor (max hl hu)}, CX]);
    case env of None \<Rightarrow> RETURN None
    | Some env \<Rightarrow> do {
      res \<leftarrow> nth_image env 0;
      err \<leftarrow> nth_image env 1;
      ASSUME (ncc res);
      s \<leftarrow> safe_set res;
      if s then RETURN (Some (res, err)) else RETURN None
    }
  })"
sublocale autoref_op_pat_def euler_step .

lemma simpi:
  assumes "X0 < length (xs)"
  shows "(let ys = xs @ [a] in ys @ [b [ys ! X0]]) = xs @ [a, b [xs ! X0]]"
  using assms
  by (auto simp: nth_append_cond)

lemma embed_real_ivl_iff[simp]:
   "(\<forall>x \<in> {0 .. h *\<^sub>R (One::'a)}. P (x \<bullet> hd Basis_list)) \<longleftrightarrow> (\<forall>x \<in> {0 .. h}. P x)"
proof (auto simp: eucl_le[where 'a='a], goal_cases)
  case hyps: (1 x)
  have "x = x *\<^sub>R (One::'a) \<bullet> hd Basis_list"
    by auto
  also have "P \<dots>"
    apply (rule hyps[rule_format])
    using hyps
    by (auto simp: eucl_le[where 'a='a])
  finally show ?case .
qed

lemma convex_on_segmentI:
  assumes mem_convex: "convex C" "a \<in> C" "a + j *\<^sub>R b \<in> C"
  assumes "0 \<le> i" "i \<le> j"
  shows "a + i *\<^sub>R b \<in> C"
proof -
  have "a + i *\<^sub>R b = (1 - i / j) *\<^sub>R a + (i / j) *\<^sub>R (a + j *\<^sub>R b)"
    using assms
    by (auto simp: algebra_simps diff_divide_distrib)
  also have "\<dots> \<in> C"
    using assms
    by (auto simp: divide_simps intro!: convexD[OF mem_convex])
  finally show ?thesis .
qed

lemma one_step_flowpipe:
  assumes "X0 \<subseteq> Collect safe"
  assumes [THEN one_step_methodD, refine_vcg]: "one_step_method m"
  shows "one_step X0 h m \<le> SPEC (\<lambda>(h', _, RES_ivl, RES). h' \<le> h \<and> flowpipe X0 h' h' RES_ivl RES)"
  using assms
  unfolding one_step_def
  by refine_vcg (auto simp: flowpipe_def)

lemma euler_step_flowpipe:
  assumes "X0 \<subseteq> Collect safe"
  shows "euler_step X0 h \<le> SPEC (\<lambda>(h', _, RES_ivl, RES). h' \<le> h \<and> flowpipe X0 h' h' RES_ivl RES)"
  unfolding euler_step_def THE_NRES_def
  apply (intro SPEC_rule_conjI one_step_flowpipe assms one_step_methodI)
  apply refine_vcg
  apply (split option.splits)
proof (safe, goal_cases)
  case hyps: (2 X0 CX hl hu env_option env _ _ _ _ _  x0 h)
  then interpret derivative_on_prod "{0 .. h}" CX "\<lambda>_. ode" "\<lambda>(t, x). ode_d x o\<^sub>L snd_blinfun"
    by unfold_locales
      (auto intro!: continuous_intros derivative_eq_intros simp: split_beta' subset_iff)
  from \<open>h \<in> existence_ivl0 x0\<close> have s_ex: "s \<in> existence_ivl0 x0" if "0 \<le> s" "s \<le> h" for s
    by (metis (no_types, lifting) atLeastAtMost_iff ivl_subset_existence_ivl subset_iff that)
  have "flow0 x0 (h) = flow0 x0 (0 + (h))" by simp
  also have "\<dots> \<in> (\<lambda>x. x ! 0) ` env"
    using hyps
    by (intro euler_consistent_traj_set[where x="flow0 x0" and u = "h"])
      (auto intro!: \<open>0 \<le> h\<close> flow_has_vector_derivative[THEN has_vector_derivative_at_within]
        image_eqI[where x="let err = ((h)\<^sup>2 / 2) *\<^sub>R blinfun_apply (ode_d (flow0 x0 s)) (ode (flow0 x0 s)) in [x0 + h *\<^sub>R ode x0 + err, err]" for s]
        simp: ncc_imageD discrete_evolution_def euler_increment interpret_euler_incr_slp subset_iff
        Let_def s_ex min_def max_def)
  finally show "flow0 x0 (h) \<in> (\<lambda>x. x ! 0) ` env" .
qed force

schematic_goal euler_step_impl:
  assumes [autoref_rules]: "(Xi, X) \<in> \<langle>eucl_rel\<rangle>appr_rel" "(hi, h) \<in> Id"
  shows "(nres_of (?f::?'r dres), euler_step $ X $ h) \<in> ?R"
  unfolding one_step_def euler_step_def autoref_tag_defs
  by (autoref_monadic)

concrete_definition euler_step_impl for Xi hi uses euler_step_impl
lemmas [autoref_rules] = euler_step_impl.refine

definition "rk2_incr_slp =
   (* 0 = X0                             *)
   (* 1 = h                              *)
   (* 2 = s1                             *)
   (* 3 = s2                             *)
   (* 4 = flow X0 (H * s1)               *)
  (
  let p = rk2_param optns;
      p2 = (Inverse (Num (2 * p)));
      p4 = (Mult (Num p) (Inverse (Num 4)));
      pd = Mult (Num (p * 2 - 1)) (Inverse (Num (p * 2)))
  in
   (* 5  = *) hadamard_ea 1 2                 ;slp
   (* 6  = *) ode_euclarith 0                 ;slp
   (* 7  = *) ode_euclarith 4                 ;slp
   (* 8  = *) scaleR_ea (Num p) 1             ;slp
   (* 9  = *) scaleR_eas 8 6                  ;slp
   (* 10 = *) hadamard_ea 3 1                 ;slp
   (* 11 = *) scaleR_ea (Num p) 10            ;slp
   (* 12 = *) scaleR_eas 11 6                 ;slp
   (* 13 = *) add_ea 0 12                     ;slp
   (* 14 = *) scaleR_ea (Num 1) 7             ;slp
   (* 15 = *) ode_d2_euclarith 4 7 14         ;slp
   (* 16 = *) ode_d_euclarith 4 7             ;slp
   (* 17 = *) ode_d_euclarith 4 16            ;slp
   (* 18 = *) add_ea 15 17                    ;slp
   (* 19 = *) scaleR_ea (Inverse (Num 6)) 18  ;slp
   (* 20 = *) scaleR_ea (Num 1) 6             ;slp
   (* 21 = *) ode_d2_euclarith 13 6 20        ;slp
   (* 22 = *) scaleR_ea p4 21                 ;slp
   (* 23 = *) scaleR_ea pd 6                  ;slp
   (* 24 = *) add_ea 0 9                      ;slp
   (* 25 = *) ode_euclarith 24                ;slp
   (* 26 = *) scaleR_ea p2 25                 ;slp
   (* 27 = *) add_ea 23 26                    ;slp
   (* 28 = *) scaleR_eas 1 27                 ;slp
   (* 29 = *) add_ea 0 28                     ;slp
   (* 30 = *) minus_ea 19 22                  ;slp
   (* 31 = *) hadamard_ea 1 1                 ;slp
   (* 32 = *) hadamard_ea 1 31                ;slp
   (* 33 = *) scaleR_eas 32 30                ;slp
   (* 34 = *) add_ea 29 33                    ;slp
  ReturnSLP [34, 33]
  )"
sublocale autoref_op_pat_def rk2_incr_slp .

lemma autoref_rk2_incr_slp[autoref_rules]: "(rk2_incr_slp, rk2_incr_slp) \<in> Id"
  by (rule IdI)


text \<open>``nonautonomous, uncurried'' definitions\<close>

definition ode_na::"real \<times> 'a \<Rightarrow> 'a" where "ode_na = (\<lambda>a. ode (snd a))"
definition ode_d_na::"real \<times> 'a \<Rightarrow> (real \<times> 'a) \<Rightarrow>\<^sub>L 'a" where "ode_d_na = (\<lambda>tx. ode_d (snd tx) o\<^sub>L snd_blinfun)"
definition ode_d2_na::"real \<times> 'a \<Rightarrow> (real \<times> 'a) \<Rightarrow>\<^sub>L (real \<times> 'a) \<Rightarrow>\<^sub>L 'a" where
  "ode_d2_na = (\<lambda>tx. flip_blinfun (flip_blinfun (ode_d2 (snd tx) o\<^sub>L snd_blinfun) o\<^sub>L snd_blinfun))"

lemma interpret_rk2_incr_slp_image:
  assumes "safe x0" "safe (flow0 x0 (h * s1))" "safe (x0 + (rk2_param optns * (s2 * h)) *\<^sub>R ode x0)"
    "rk2_param optns > 0"
  shows "discrete_evolution (rk2_increment (rk2_param optns) (\<lambda>_. ode)) h 0 x0 +
      heun_remainder1                   (flow0 x0) ode_na ode_d_na ode_d2_na 0 h s1-
      heun_remainder2 (rk2_param optns) (flow0 x0) ode_na ode_d_na ode_d2_na 0 h s2
    = interpret_slp (rk2_incr_slp) [x0, eor h, eor s1, eor s2, flow0 x0 (h * s1)] ! 0"
  unfolding Let_def rk2_incr_slp_def
  using assms
  by (subst interpret_slp.simps, simp del: interpret_slp.simps
      add: roe_def eor_def hadamard_inner_Basis interpret_ode_euclarith interpret_ode_d_euclarith interpret_ode_d2_euclarith
      ode_na_def ode_d_na_def ode_d2_na_def heun_remainder1_def heun_remainder2_def discrete_evolution_def rk2_increment
      algebra_simps power3_eq_cube divide_simps)+

definition "rk2_step X0 h = one_step X0 h (\<lambda>X0 hl hu CX.
  do {
    env \<leftarrow> approx_slp_spec rk2_incr_slp (listset [X0, {eor (min hl hu) .. eor (max hl hu)}, {eor 0 .. eor 1}, {eor 0 .. eor 1}, CX]);
    case env of None \<Rightarrow> RETURN None
    | Some env \<Rightarrow> do {
      res \<leftarrow> nth_image env 0;
      err \<leftarrow> nth_image env 1;
      ASSUME (ncc res);
      s \<leftarrow> safe_set res;
      if s then RETURN (Some (res, err)) else RETURN None
    }
  })"
sublocale autoref_op_pat_def rk2_step .

lemma rk2_step_flowpipe:
  assumes "X0 \<subseteq> Collect safe"
  assumes "0 < rk2_param optns"
  assumes "rk2_param optns \<le> 1"
  shows "rk2_step X0 h \<le> SPEC (\<lambda>(h', _, RES_ivl, RES). h' \<le> h \<and> flowpipe X0 h' h' RES_ivl RES)"
  unfolding rk2_step_def THE_NRES_def
  apply (intro one_step_flowpipe assms one_step_methodI)
  apply refine_vcg
  apply (split option.splits)
proof (safe, goal_cases)
  case hyps: (2 X0 CX hl hu env_option env _ _ _ _ _ x0 h)
  have aux: "ode (flow0 x0 s) = ode (snd (s, flow0 x0 s))" for s
    by simp
  from hyps interpret derivative_on_prod "{0 .. h}" CX "\<lambda>_ x. ode x" "\<lambda>(t, x). ode_d x o\<^sub>L snd_blinfun"
    by unfold_locales
      (auto intro!: continuous_intros derivative_eq_intros simp: split_beta' subset_iff)

  have aux2: "blinfun_apply (ode_d (snd tx)) \<circ> snd = blinfun_apply (ode_d (snd tx) o\<^sub>L snd_blinfun)"
    for tx::"real\<times>'a"
    by (auto intro!: blinfun_eqI)

  have aux3: "blinfun_apply (ode_d2 (snd tx)) (snd h) o\<^sub>L snd_blinfun =
    (flip_blinfun (flip_blinfun (ode_d2 (snd tx) o\<^sub>L snd_blinfun) o\<^sub>L snd_blinfun)) h"
    for tx h::"real\<times>'a"
    by (auto intro!: blinfun_eqI)


  have "flow0 x0 (h) = flow0 x0 (0 + (h))" by simp
  also have "\<dots> \<in> (\<lambda>x. x ! 0) ` env"
    using hyps assms
    apply (intro rk2_consistent_traj_set[where
      x="flow0 x0" and u = "h" and T="{0..h}" and X="CX" and p="rk2_param optns"
      and f = "ode_na" and f' = ode_d_na and g' = ode_d_na and f'' = ode_d2_na and g'' = ode_d2_na])
    unfolding ode_na_def[abs_def] ode_d_na_def[abs_def] ode_d2_na_def[abs_def]
    subgoal by (simp add: \<open>0 \<le> h\<close>)
    subgoal by simp
    subgoal by simp
    subgoal by (auto simp add: ncc_def)
    subgoal by (auto simp add: ncc_def)
    subgoal
      apply (rule flow_has_vector_derivative[THEN has_vector_derivative_at_within, THEN has_vector_derivative_eq_rhs])
      subgoal by (metis (no_types, lifting) atLeastAtMost_iff ivl_subset_existence_ivl mem_Collect_eq subset_iff)
      subgoal by force
      done
    subgoal
      apply (rule derivative_eq_intros)
        apply (rule derivative_intros)
        apply (rule derivative_intros)
      subgoal by force
      subgoal by force
      done
    subgoal
      apply (rule derivative_eq_intros)
        apply (rule derivative_intros)
         apply (rule derivative_intros)
         apply (rule derivative_intros)
      subgoal by force
       apply (rule derivative_intros)
      subgoal by (auto intro!: aux3)
      done
    subgoal by (rule refl)
    subgoal by (rule refl)
    subgoal
      apply (rule compact_imp_bounded)
      apply (rule compact_continuous_image)
      subgoal by (auto intro!: continuous_intros)
      subgoal by (auto simp: ncc_def intro!: compact_Times compact_Icc)
      done
    subgoal by auto
    subgoal by simp
    subgoal by simp
    subgoal
      apply (rule convex_on_segmentI[where j=h])
      using mult_left_le_one_le[of h "rk2_param optns"]
      by (auto simp: ncc_def mult_left_le_one_le mult_le_one ac_simps dest: bspec[where x=0])
    subgoal by (simp add: ncc_def)
    subgoal by (simp add: ncc_def compact_imp_closed)
    subgoal for s1 s2
      apply (rule image_eqI[where x="interpret_slp rk2_incr_slp [x0, eor h, eor s1, eor s2, flow0 x0 (h * s1)]"])
      apply (subst interpret_rk2_incr_slp_image[unfolded ode_na_def ode_d_na_def ode_d2_na_def, symmetric])
      subgoal by force
      subgoal using hyps by (auto simp: mult_left_le_one_le mult_right_le_one_le)
      subgoal premises prems
      proof -
        have "x0 + ((rk2_param optns * s2) * h) *\<^sub>R ode x0 \<in> CX"
          by (rule convex_on_segmentI[where j=h])
            (use prems in \<open>auto simp: ncc_def mult_left_le_one_le mult_le_one dest: bspec[where x=0]\<close>)
        also note \<open>\<dots> \<subseteq> Collect safe\<close>
        finally show ?thesis
          by (simp add: ac_simps)
      qed
      subgoal by auto
      subgoal by auto
      subgoal using hyps by (auto simp: mult_right_le_one_le min_def max_def)
      done
    done
  finally show "flow0 x0 h \<in> (\<lambda>x. x ! 0) ` env" .
qed force

schematic_goal rk2_step_impl:
  assumes [autoref_rules]: "(Xi, X) \<in> \<langle>eucl_rel\<rangle>appr_rel" "(hi, h) \<in> Id"
  shows "(nres_of (?f::?'r dres), rk2_step $ X $ h) \<in> ?R"
  unfolding one_step_def rk2_step_def autoref_tag_defs
  by (autoref_monadic)

concrete_definition rk2_step_impl for Xi hi uses rk2_step_impl
lemmas [autoref_rules] = rk2_step_impl.refine

definition "choose_step = (if method_id optns = 2 then rk2_step else euler_step)"
sublocale autoref_op_pat_def choose_step .

schematic_goal choose_step_impl:
  assumes [autoref_rules]: "(Xi, X) \<in> \<langle>eucl_rel\<rangle>appr_rel" "(hi, h) \<in> Id"
  shows "(nres_of (?f::?'r dres), choose_step $ X $ h) \<in> ?R"
  unfolding choose_step_def autoref_tag_defs cond_application_beta
  by (autoref_monadic)

concrete_definition choose_step_impl for Xi hi uses choose_step_impl
lemmas [autoref_rules] = choose_step_impl.refine

lemma choose_step_flowpipe[THEN order_trans, refine_vcg]:
  assumes "DEFER (\<lambda>X0. X0 \<subseteq> Collect safe) X0"
  assumes "DEFER_tag (0 < rk2_param optns)"
  assumes "DEFER_tag (rk2_param optns \<le> 1)"
  shows "choose_step X0 h \<le> SPEC (\<lambda>(h', _, RES_ivl, RES). h' \<le> h \<and> flowpipe X0 h' h' RES_ivl RES)"
  using assms
  unfolding choose_step_def autoref_tag_defs
  by (split if_split) (safe intro!: rk2_step_flowpipe euler_step_flowpipe)


definition "transversal_directions f =
  do {
    I \<leftarrow> Inf_spec f;
    S \<leftarrow> Sup_spec f;
    RETURN (listsum (map (\<lambda>b. (if I \<bullet> b \<le> 0 then if S \<bullet> b \<le> 0 then S \<bullet> b else 0 else if S \<bullet> b \<ge> 0 then I \<bullet> b else 0) *\<^sub>R b) (Basis_list::'a list)))
  }"
sublocale autoref_op_pat_def transversal_directions .

schematic_goal transversal_directions_impl:
  assumes [autoref_rules]: "(fi,f)\<in>\<langle>eucl_rel\<rangle>appr_rel"
  shows "(nres_of (?f::?'c dres), transversal_directions $ f)\<in>?R"
  unfolding transversal_directions_def[abs_def] autoref_tag_defs
  by (autoref_monadic (plain))
concrete_definition transversal_directions_impl for fi uses transversal_directions_impl
lemmas [autoref_rules] = transversal_directions_impl.refine

definition "strongest_transversal f =
  do { d \<leftarrow> transversal_directions f; RETURN (strongest_direction d)}"
sublocale autoref_op_pat_def strongest_transversal .
schematic_goal strongest_transversal_impl:
  assumes [autoref_rules]: "(fi, f) \<in> \<langle>eucl_rel\<rangle>appr_rel"
  shows "(nres_of (?f::?'c dres), strongest_transversal $ f) \<in> ?R"
  unfolding strongest_transversal_def[abs_def] autoref_tag_defs
  by (autoref_monadic (plain))
concrete_definition strongest_transversal_impl for fi uses strongest_transversal_impl
lemmas [autoref_rules] = strongest_transversal_impl.refine

lemma strongest_transversal_nonneg[THEN order_trans, refine_vcg]:
  "strongest_transversal f \<le> SPEC (\<lambda>(_, d). d \<ge> 0)"
  unfolding strongest_transversal_def transversal_directions_def
  by refine_vcg (auto simp: strongest_direction_def Let_def)


definition [refine_vcg_def]: "CHECK_ALLSAFE xs = SPEC (\<lambda>b::unit. \<forall>X \<in> xs. X \<subseteq> Collect safe)"
sublocale autoref_op_pat_def CHECK_ALLSAFE .

lemma CHECK_ALLSAFE_abs: "FORWEAK xs (RETURN ()) (\<lambda>x. do { s \<leftarrow> safe_set x; CHECK s}) (\<lambda>_ _. RETURN ()) \<le> CHECK_ALLSAFE xs"
  unfolding CHECK_ALLSAFE_def
  by (refine_vcg FORWEAK_elementwise_rule)

schematic_goal CHECK_ALLSAFE_impl:
  assumes [autoref_rules]: "(XSi, XS) \<in> \<langle>\<langle>eucl_rel\<rangle>appr_rel\<rangle>list_wset_rel"
  shows "(?r, CHECK_ALLSAFE $ XS) \<in> \<langle>unit_rel\<rangle>nres_rel"
  apply (rule nres_rel_trans2)
  unfolding autoref_tag_defs
  apply (rule CHECK_ALLSAFE_abs)
  apply autoref
  done
concrete_definition CHECK_ALLSAFE_impl uses CHECK_ALLSAFE_impl
lemmas [autoref_rules] = CHECK_ALLSAFE_impl
schematic_goal CHECK_ALLSAFE_refine[refine_transfer]:
  shows "nres_of ?r \<le> CHECK_ALLSAFE_impl X"
  unfolding CHECK_ALLSAFE_impl_def
  by refine_transfer


subsubsection \<open>Implementation of set as union of sets\<close>

definition "default_rel d R = {(x, y). case x of Some x' \<Rightarrow> (x', y) \<in> R | None \<Rightarrow> d = y}"
  \<comment>\<open> why not \<open>br (the_default d) top\<close>? There is no concrete Element to represent \<open>d\<close>! \<close>

definition coll_rel :: "('c \<times> 'e set) set \<Rightarrow> ('e \<times> 'a) set \<Rightarrow> ('c list option \<times> 'a set) set"
where coll_rel_internal: "coll_rel R S = default_rel (Collect safe) (\<langle>R\<rangle>list_wset_rel O {(x, y). \<Union>x = y} O \<langle>S\<rangle>set_rel O {(x, y). x = y \<and> x \<subseteq> Collect safe})"
lemma coll_rel_def[refine_rel_defs]: "\<langle>eucl_rel\<rangle>(coll_rel R) \<equiv> default_rel (Collect safe) (\<langle>R\<rangle>list_wset_rel O {(x, y). \<Union>x = y \<and> y \<subseteq> Collect safe})"
  unfolding relAPP_def
  apply (auto simp: coll_rel_internal relcomp_unfold intro!: eq_reflection)
  by (auto simp add: relAPP_def coll_rel_internal default_rel_def split: option.split)
lemmas [autoref_rel_intf] = REL_INTFI[of "coll_rel R" "i_set" for R]

lemma coll_union12[autoref_rules]:
  shows "(\<lambda>a b. do {a \<leftarrow> a; b \<leftarrow> b; Some (a @ b)}, op \<union>) \<in>
    \<langle>eucl_rel\<rangle>(coll_rel R) \<rightarrow> \<langle>eucl_rel\<rangle>(coll_rel R) \<rightarrow> \<langle>eucl_rel\<rangle>(coll_rel R)"
  by (fastforce simp: coll_rel_def default_rel_def bind_eq_Some_conv split: option.splits
      intro!: relcompI[OF union_wset_refine[THEN fun_relD, THEN fun_relD]]
              relcompI[OF union_wset_refine[THEN fun_relD, THEN fun_relD]])

lemma coll_split:
  assumes "PREFER single_valued R"
  shows "(\<lambda>xs.
      case xs of None \<Rightarrow> SUCCEED
      | Some [] \<Rightarrow> SUCCEED
      | Some (x # xs) \<Rightarrow> RETURN (x, Some xs),
    split_spec) \<in>
    \<langle>eucl_rel\<rangle>coll_rel R \<rightarrow> \<langle>R \<times>\<^sub>r \<langle>eucl_rel\<rangle>coll_rel R\<rangle>nres_rel"
  unfolding nres_rel_def split_spec_def coll_rel_def default_rel_def
  apply (clarsimp simp: nres_rel_def split_spec_def coll_rel_def default_rel_def
      intro!: RETURN_SPEC_refine split: list.splits option.splits)
proof goal_cases
  case hyps: (1 b c a)
  then obtain k where "(b, k) \<in> R" using hyps
    by (auto simp: list_wset_rel_def br_def set_rel_def)
  from hyps have "a = R `` insert b (set c)" by (auto simp: list_wset_rel_def br_def set_rel_def)
  also have "\<dots> = insert k (R `` (set c))" using assms
    by (simp add: Image_insert \<open>(b, k) \<in> R\<close>)
  finally show ?case
    apply (intro exI[where x="k"])
    apply (rule conjI)
    subgoal premises _ by fact
    subgoal premises prems
    proof -
      have *: "(c, \<Union>(R `` set c)) \<in> ({(c, a). a = set c} O \<langle>R\<rangle>set_rel) O {(x, y). \<Union>x = y \<and> y \<subseteq> Collect safe}"
        apply (rule relcompI[where b="R `` (set c)"])
        subgoal
          apply (rule relcompI[where b="set c"])
          subgoal by force
          subgoal using hyps by (force simp: set_rel_def list_wset_rel_def br_def)[]
          done
        subgoal using hyps prems by auto
        done
      show ?thesis
        apply (rule exI[where x="\<Union>(R `` (set c))"])
        using * prems
        by (auto simp: list_wset_rel_def br_def)
    qed
    done
qed

lemma list_rel_comp_coll_rel: "single_valued R \<Longrightarrow>  (\<langle>\<langle>R\<rangle>list_rel\<rangle>option_rel O \<langle>eucl_rel\<rangle>coll_rel S) = \<langle>eucl_rel\<rangle>coll_rel(R O S)"
  unfolding coll_rel_def default_rel_def
  apply (safe elim!: option_relE)
  subgoal by (auto)
  subgoal by (auto simp: list_rel_comp_list_wset_rel[symmetric])
  subgoal
    by (auto simp: list_rel_comp_list_wset_rel[symmetric] option_rel_def
        split: option.splits)
  done

lemma list_wset_relD:
  assumes "(a, b) \<in> \<langle>R\<rangle>list_wset_rel"
  shows "(set a, b) \<in> \<langle>R\<rangle>set_rel"
  using assms
  by (auto simp: list_wset_rel_def br_def)

lemma coll_Union[autoref_rules]:
  assumes "PREFER single_valued R"
  shows "(\<lambda>a. map_option concat (those a), Union) \<in>
    \<langle>\<langle>eucl_rel\<rangle>coll_rel R\<rangle>list_wset_rel \<rightarrow> \<langle>eucl_rel\<rangle>coll_rel R"
proof -
  have "((\<lambda>a. map_option concat (those a), (\<lambda>a. map_option concat (those a)))) \<in>
      \<langle>\<langle>\<langle>R\<rangle>list_rel\<rangle>option_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>R\<rangle>list_rel\<rangle>option_rel" (is "_ \<in> ?a")
    by parametricity
  moreover
  let ?coll_rel_unsafe = "\<langle>Id\<rangle>list_wset_rel O {(x, y). \<Union>x = y}"
  have 2: "(\<lambda>a. map_option concat (those a), Union) \<in> \<langle>\<langle>eucl_rel\<rangle>coll_rel Id\<rangle>list_wset_rel \<rightarrow> \<langle>eucl_rel\<rangle>coll_rel Id"
    (is "_ \<in> ?b")
  proof safe
    fix a a'
    assume a: "(a, a') \<in> \<langle>\<langle>eucl_rel\<rangle>coll_rel Id\<rangle>list_wset_rel"
    show "(map_option concat (those a), \<Union>a') \<in> \<langle>eucl_rel\<rangle>coll_rel Id"
    proof (cases "those a")
      case None then show ?thesis
        using a
        by (auto simp: list_wset_rel_def default_rel_def coll_rel_def br_def
            split: option.splits
            intro!: bexI[where x="Collect safe"];
            fastforce simp: those_eq_None_set_iff set_rel_def br_def)
    next
      case (Some xs)
      then have a_eq: "a = map Some xs"
        by (simp add: those_eq_Some_map_Some_iff)
      have "(Some (concat xs), \<Union>a') \<in> \<langle>eucl_rel\<rangle>coll_rel Id"
      proof -
        have "\<Union>UNION (set xs) set = \<Union>a'"
          using a unfolding a_eq
          apply (safe dest!: list_wset_relD)
          subgoal for a b c
            by (drule set_relD[where x="Some c"])
              (auto simp add: coll_rel_def default_rel_def list_wset_rel_def br_def dest!: list_wset_relD)
          subgoal for x y
            by (auto simp: list_wset_rel_def coll_rel_def set_rel_def default_rel_def br_def split: option.splits)
          done
        moreover have "\<Union>a' \<subseteq> Collect safe"
          using a unfolding a_eq
          by (force simp: list_wset_rel_def coll_rel_def set_rel_def default_rel_def split: option.splits)
        ultimately
        have "(concat xs, \<Union>a') \<in> \<langle>Id\<rangle>list_wset_rel O {(x, y). \<Union>x = y \<and> y \<subseteq> Collect safe}"
          by (intro relcompI[where b="\<Union>(set ` set xs)"]) (auto simp: list_wset_rel_def br_def)
        then show ?thesis
          by (simp add: coll_rel_def default_rel_def)
      qed
      then show ?thesis
        by (simp add: Some)
    qed
  qed
  ultimately have "(\<lambda>a. map_option concat (those a), Union) \<in> ?a O ?b"
    by blast
  also have "?a O ?b \<subseteq> \<langle>\<langle>\<langle>R\<rangle>list_rel\<rangle>option_rel\<rangle>list_rel O
    \<langle>\<langle>eucl_rel\<rangle>coll_rel Id\<rangle>list_wset_rel \<rightarrow> \<langle>\<langle>R\<rangle>list_rel\<rangle>option_rel O \<langle>eucl_rel\<rangle>coll_rel Id"
    (is "_ \<subseteq> ?i \<rightarrow> ?o")
    by (rule fun_rel_comp_dist)
  also have "?i = \<langle>\<langle>eucl_rel\<rangle>coll_rel R\<rangle>list_wset_rel"
    apply (subst list_rel_comp_list_wset_rel)
    subgoal by (rule relator_props assms[unfolded autoref_tag_defs])+
    apply (subst list_rel_comp_coll_rel)
    subgoal by (rule relator_props assms[unfolded autoref_tag_defs])+
    by simp
  also have "?o = \<langle>eucl_rel\<rangle>coll_rel R"
    by (auto simp: assms[unfolded autoref_tag_defs] list_rel_comp_coll_rel)
  finally show ?thesis .
qed

lemma [autoref_rules]:
  "(real_divl, real_divl) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> Id"
  "(truncate_down, truncate_down) \<in> Id \<rightarrow> Id \<rightarrow> Id"
  "(eucl_truncate_down, eucl_truncate_down) \<in> Id \<rightarrow> Id \<rightarrow> Id"
  "(truncate_up, truncate_up) \<in> Id \<rightarrow> Id \<rightarrow> Id"
  "(eucl_truncate_up, eucl_truncate_up) \<in> Id \<rightarrow> Id \<rightarrow> Id"
  "(max, max) \<in> Id \<rightarrow> Id \<rightarrow> Id"
  "(min, min) \<in> Id \<rightarrow> Id \<rightarrow> Id"
  "(op /, op /) \<in> Id \<rightarrow> Id \<rightarrow> Id"
  "(stepsize_update, stepsize_update) \<in> (Id \<rightarrow> Id) \<rightarrow> Id \<rightarrow> Id"
  "(lfloat10, lfloat10) \<in> Id \<rightarrow> Id"
  "(ufloat10, ufloat10) \<in> Id \<rightarrow> Id"
  "(shows_prec, shows_prec) \<in> Id \<rightarrow> nat_rel \<rightarrow> string_rel \<rightarrow> string_rel"
  "(shows_prec, shows_prec) \<in> Id \<rightarrow> int_rel \<rightarrow> string_rel \<rightarrow> string_rel"
  "(shows_prec, shows_prec) \<in> Id \<rightarrow> (Id::(_ \<times> float10) set) \<rightarrow> string_rel \<rightarrow> string_rel"
  "(int, int) \<in> Id \<rightarrow> Id"
  by (auto simp: string_rel_def)

definition Union_rel_internal: "Union_rel R = \<langle>R\<rangle>set_rel O {(x, y). \<Union>x = y}"
lemma Union_rel_def: "\<langle>R\<rangle>Union_rel = \<langle>R\<rangle>set_rel O {(x, y). \<Union>x = y}"
  by (auto simp add: Union_rel_internal br_def relAPP_def)

definition "snd_rel = br snd top"
definition with_stepsize_rel::"_ \<Rightarrow> ((real \<times> 'b) \<times> 'a set) set"
where with_stepsize_rel_internal: "with_stepsize_rel R = snd_rel O \<langle>R\<rangle>appr_rel"
lemma with_stepsize_rel_def: "\<langle>eucl_rel\<rangle>with_stepsize_rel = snd_rel O \<langle>eucl_rel\<rangle>appr_rel"
  by (simp add: relAPP_def with_stepsize_rel_internal)
lemmas [autoref_rel_intf] = REL_INTFI[of with_stepsize_rel i_set]

definition [refine_vcg_def]: "split_spec_with_stepsize x = SPEC (\<lambda>((h::real, a), b). x = a \<union> b)"
sublocale autoref_op_pat_def split_spec_with_stepsize .

lemma Some_mem_coll_rel_iff: "(Some x, y) \<in> \<langle>eucl_rel\<rangle>coll_rel S \<longleftrightarrow>
  (\<exists>ya. (x, ya) \<in> \<langle>S\<rangle>list_wset_rel \<and> \<Union>ya \<subseteq> Collect safe \<and> y = \<Union>ya)"
  by (auto simp: coll_rel_def default_rel_def)

lemma split_spec_with_stepsize_autoref[autoref_rules]:
  "((\<lambda>xs. case xs of None \<Rightarrow> SUCCEED | Some [] \<Rightarrow> SUCCEED | Some (x#xs) \<Rightarrow> RETURN (x, Some xs)), split_spec_with_stepsize) \<in>
    \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>with_stepsize_rel) \<rightarrow> \<langle>(eucl_rel \<times>\<^sub>r \<langle>eucl_rel\<rangle>appr_rel) \<times>\<^sub>r \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>with_stepsize_rel)\<rangle>nres_rel"
  unfolding split_spec_with_stepsize_def[abs_def]
  apply (safe intro!: nres_relI)
  subgoal premises a for a a'
    apply (cases a)
    subgoal by simp
    subgoal premises xs for xs
      apply (cases xs)
      subgoal by (simp add: xs)
      subgoal premises y for y ys
      proof -
        have a'_subset: "a' \<subseteq> (\<Union>(_, x) \<in> set(y#ys). set_of_appr x)"
          using a xs y
          by (auto simp: coll_rel_def default_rel_def with_stepsize_rel_def appr_rel_def
                list_wset_rel_def br_def snd_rel_def set_rel_def
              split: option.splits
              intro!: )
        have subset_a': "set_of_appr (snd z) \<subseteq> a'" if "z \<in> set (y#ys)" for z
          using a xs y that
          by (auto simp: coll_rel_def default_rel_def with_stepsize_rel_def appr_rel_def
                list_wset_rel_def br_def snd_rel_def
              split: option.splits
              intro!: bexI[where x="set_of_appr (snd z)"])
            (auto simp: set_rel_def)
        also from a have "a' \<subseteq> Collect safe"
          by (auto simp: coll_rel_def default_rel_def list_wset_rel_def split: option.splits)
        finally have safe: "set_of_appr (snd z) \<subseteq> Collect safe" if "z \<in> set (y#ys)" for z using that .
        have 1: "(y, fst y, set_of_appr (snd y)) \<in> eucl_rel \<times>\<^sub>r \<langle>eucl_rel\<rangle>appr_rel"
          by (auto simp: appr_rel_def br_def prod_rel_def)
        have 2: "(Some ys, \<Union>x\<in>set ys. set_of_appr (snd x)) \<in> \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>with_stepsize_rel)"
          using safe
          unfolding Some_mem_coll_rel_iff
          by (auto simp: list_wset_rel_def with_stepsize_rel_def set_rel_def snd_rel_def br_def appr_rel_def
              intro!: exI[where x="set_of_appr ` (snd ` (set ys))"])
        have 3: "x \<in> a' \<Longrightarrow> \<forall>xa\<in>set ys. x \<notin> set_of_appr (snd xa) \<Longrightarrow> x \<in> set_of_appr (snd y)" for x
          using a'_subset by force
        have 4: "x \<in> set_of_appr (snd y) \<Longrightarrow> x \<in> a'" for x
          by (meson contra_subsetD list.set_intros(1) subset_a')
        have 5: "(a, b) \<in> set ys \<Longrightarrow> x \<in> set_of_appr b \<Longrightarrow> x \<in> a'" for x a b
          using subset_a' by fastforce
        have "RETURN (y, Some ys) \<le> \<Down> ((eucl_rel \<times>\<^sub>r \<langle>eucl_rel\<rangle>appr_rel) \<times>\<^sub>r \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>with_stepsize_rel))
            (SPEC (\<lambda>((h, a), b). a' = a \<union> b))"
          apply (intro RETURN_SPEC_refine)
          apply (intro exI[where x="((fst y, set_of_appr (snd y)), \<Union>((set (map (set_of_appr o snd) ys))))"])
          by (auto intro: 4 5 intro!: 1 2 3 )
        then show ?thesis
          by (simp add: xs y)
      qed
      done
    done
  done

definition card_info::"_ set \<Rightarrow> nat nres" where [refine_vcg_def]: "card_info x = SPEC top" \<comment>\<open>op_set_wcard\<close>

sublocale autoref_op_pat_def card_info .

lemma card_info[autoref_rules]:
  "((\<lambda>x. RETURN (length (the_default [] x))), card_info) \<in> \<langle>eucl_rel\<rangle>coll_rel R \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"
  by (auto simp: card_info_def nres_rel_def)

definition with_stepsize::"real \<Rightarrow> 'a set \<Rightarrow> 'a set" where [simp]: "with_stepsize h x = x"
sublocale autoref_op_pat_def with_stepsize .

lemma with_stepsize_autoref[autoref_rules]:
  "((\<lambda>h x. (h, x)), with_stepsize) \<in> eucl_rel \<rightarrow> \<langle>eucl_rel\<rangle>appr_rel \<rightarrow> \<langle>eucl_rel\<rangle>with_stepsize_rel"
  by (auto simp: coll_rel_def with_stepsize_rel_def snd_rel_def br_def)

lemma None_mem_coll_rel[simp]: "(None, x) \<in> \<langle>eucl_rel\<rangle>coll_rel R \<longleftrightarrow> x = Collect safe"
  by (auto simp: coll_rel_def default_rel_def)

definition [simp]: "with_half_stepsizes x = x"
sublocale autoref_op_pat_def with_half_stepsize .

lemma with_half_stepsize_autoref[autoref_rules]:
  "(map_option (map (\<lambda>(h, x). (h/2, x))), with_half_stepsizes) \<in>
    \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>with_stepsize_rel) \<rightarrow> \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>with_stepsize_rel)"
  by (subst (2) coll_rel_def)
    (fastforce
      simp: with_stepsize_rel_def br_def default_rel_def Some_mem_coll_rel_iff set_rel_def
        snd_rel_def br_def relcomp_unfold appr_rel_def list_wset_rel_def
      split: option.splits)

lemma with_stepsize_coll_autoref[autoref_rules]:
  "(\<lambda>h. map_option (map (Pair h)), with_stepsize) \<in> eucl_rel \<rightarrow> \<langle>eucl_rel\<rangle>coll_rel(\<langle>eucl_rel\<rangle>appr_rel) \<rightarrow> \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>with_stepsize_rel)"
  apply (subst (2) coll_rel_def)
  apply (clarsimp simp add: default_rel_def with_stepsize_rel_def snd_rel_def br_def list_wset_rel_def)
proof goal_cases
  case hyps: (1 a' aa a'a)
  have "(set xa, za) \<in> \<langle>\<langle>eucl_rel\<rangle>appr_rel\<rangle>set_rel \<Longrightarrow>
       \<Union>za \<subseteq> Collect safe \<Longrightarrow>
       (map (Pair a') xa, \<Union>za) \<in>
        ({(c, a). a = set c} O \<langle>{(c, a). a = snd c} O \<langle>eucl_rel\<rangle>appr_rel\<rangle>set_rel) O
          {(x, y). \<Union>x = y \<and> y \<subseteq> Collect safe}"
          for xa za
    apply (rule relcompI[where b=za])
    subgoal
      apply (rule relcompI[where b="Pair a' ` set xa"])
      subgoal by force
      subgoal by (auto simp: appr_rel_def coll_rel_def with_stepsize_rel_def snd_rel_def br_def list_wset_rel_def set_rel_def
          relcomp_Image)
      done
    subgoal by force
    done
  then show ?case using hyps
    by (auto simp: default_rel_def with_stepsize_rel_def snd_rel_def br_def list_wset_rel_def
        coll_rel_def with_stepsize_rel_def snd_rel_def br_def list_wset_rel_def default_rel_def
        split: option.splits)
qed

lemma coll_rel_empty[autoref_rules]:
  shows "(Some [], {}) \<in> \<langle>eucl_rel\<rangle>coll_rel R"
  unfolding coll_rel_def default_rel_def
  by (auto intro!: relcompI[OF list_wset_autoref_empty])

definition mk_coll::"'a set \<Rightarrow> 'a set" where [simp]: "mk_coll x = x"

lemma mk_coll[autoref_rules]:
  "PREFER single_valued R \<Longrightarrow> (x, X) \<in> R \<Longrightarrow> SIDE_PRECOND (X \<subseteq> Collect safe) \<Longrightarrow> (Some [x], mk_coll $ X) \<in> \<langle>eucl_rel\<rangle>coll_rel R"
  by (auto simp: coll_rel_def list_wset_rel_def br_def default_rel_def set_rel_def single_valued_def
      intro!: relcompI[where b="{xa. (x, xa) \<in> R}"] relcompI[where b="{x}"])

definition "intersection_iteration sctn X h = do {
  ASSERT (X \<subseteq> Collect safe);
  F \<leftarrow> ode_set X;
  above \<leftarrow> above_sctn X sctn;
  strongest_trans \<leftarrow> strongest_transversal F;
  (X, F, PS, CXS, above, strongest_trans) \<leftarrow> WHILE (\<lambda>(X, F, PS, CXS, above, strongest_trans). \<not> above \<and> fst strongest_trans = normal sctn)
    (\<lambda>(X, F, PS::'a set, CXS, _, _).
      do {
        (_, _, CX', X') \<leftarrow> choose_step X h;
        let _ = trace_set (''interpolated step during intersection:'') (Some CX');
        let _ = print_set True CX';
        let _ = trace_set (''step during intersection:'') (Some X');
        let _ = print_set False X';
        R \<leftarrow> reduce_spec CX'; (* TODO: why reduce? Performance of inter_sctn? *)
        P \<leftarrow> inter_sctn_spec R sctn;
        let _ = trace_set (''intersection:'') (Some P);
        let _ = print_set False P;
        F' \<leftarrow> ode_set X';
        above \<leftarrow> above_sctn X' sctn;
        strongest_trans \<leftarrow> strongest_transversal F';
        s \<leftarrow> safe_set P;
        if s
        then do {
          ASSERT (P \<subseteq> Collect safe);
          ASSERT (CX' \<subseteq> Collect safe);
          RETURN (X', F', mk_coll P \<union> PS, mk_coll CX' \<union> CXS, above, strongest_trans)
        }
        else SUCCEED
      })
    (X, F, {}, mk_coll X, above, strongest_trans);
  RETURN (X, F, PS, CXS)
  }"
sublocale autoref_op_pat_def intersection_iteration .

schematic_goal intersection_iteration_impl:
  fixes sctn::"'a sctn"
  assumes [autoref_rules]: "(Xi, X) \<in> \<langle>eucl_rel\<rangle>appr_rel" "(sctni, sctn) \<in> Id" "(hi, h) \<in> Id"
  shows "(nres_of (?f::?'c dres), intersection_iteration $ sctn $ X $ h)\<in>?R"
  unfolding intersection_iteration_def[abs_def] autoref_tag_defs
  by (autoref_monadic)

concrete_definition intersection_iteration_impl for sctni Xi hi uses intersection_iteration_impl
lemmas [autoref_rules] = intersection_iteration_impl.refine

lemma
  intersection_iteration_spec[THEN order_trans, refine_vcg]:
  assumes "DEFER_tag (0 < stepsize optns)" "DEFER_tag (0 < rk2_param optns)" "DEFER_tag (rk2_param optns \<le> 1)" "DEFER (\<lambda>X. X \<subseteq> Collect safe) X"
  shows "intersection_iteration sctn X h \<le>
    SPEC (\<lambda>(X', F, PS, CXS).
      PS \<subseteq> Collect safe \<and> X' \<subseteq> Collect safe \<and>
      flowsto (X \<inter> below_halfspace sctn) (CXS) ((X' \<inter> below_halfspace sctn) \<union> (PS \<inter> plane_of sctn)))"
  using assms
  unfolding intersection_iteration_def
  apply (refine_vcg WHILE_rule[where I="\<lambda>(X', F, PS, CXS, above, _).
      PS \<subseteq> Collect safe \<and> X' \<subseteq> Collect safe \<and>
      flowsto (X \<inter> below_halfspace sctn) (CXS) (X' \<inter> below_halfspace sctn \<union> (PS) \<inter> plane_of sctn)"])
  apply clarsimp_all
  subgoal by (auto simp add: flowsto_self)
  subgoal by (force dest!: flowsto_safeD flowpipe_safeD)
  subgoal by (force dest!: flowpipe_safeD)
  subgoal by (force dest!: flowsto_safeD flowpipe_safeD)
  subgoal by (rule flowsto_intersection) (auto dest!: flowsto_safeD flowpipe_safeD)
  done

definition "do_intersection sctn X h =
  do {
    (Y, F, PS, CXS) \<leftarrow> intersection_iteration sctn X h;
    ASSERT (Y \<subseteq> Collect safe);
    a \<leftarrow> above_sctn Y sctn;
    RETURN (PS, CXS, if a then {} else mk_coll Y)}"
sublocale autoref_op_pat_def do_intersection .

schematic_goal do_intersection_impl:
  assumes [autoref_rules]: "(sctni, sctn) \<in> Id" "(Xi, X) \<in> \<langle>eucl_rel\<rangle>appr_rel" "(hi, h) \<in> Id"
  shows "(nres_of (?f::?'c dres), do_intersection $ sctn $ X $ h)\<in>?R"
  unfolding do_intersection_def autoref_tag_defs
  by autoref_monadic
concrete_definition do_intersection_impl for sctni Xi hi uses do_intersection_impl
lemmas [autoref_rules] = do_intersection_impl.refine

lemma
  do_intersection_flowsto_spec[THEN order_trans]:
  assumes "0 < stepsize optns" "0 < rk2_param optns" "rk2_param optns \<le> 1" "X \<subseteq> Collect safe"
  shows "do_intersection sctn X h \<le> SPEC (\<lambda>(PS, CXS, RS).
    CXS \<subseteq> Collect safe \<and> PS \<subseteq> Collect safe \<and> RS \<subseteq> Collect safe \<and>
    flowsto (X \<inter> below_halfspace sctn) (CXS) (PS \<inter> plane_of sctn \<union> (RS) \<inter> below_halfspace sctn))"
  using assms
  unfolding do_intersection_def
  by (refine_vcg) (force simp: ac_simps inter_Collect_eq_empty dest: flowsto_safeD split: if_splits)+

lemma
  do_intersection_spec[THEN order_trans, refine_vcg]:
  assumes "0 < stepsize optns" "0 < rk2_param optns" "rk2_param optns \<le> 1" "X \<subseteq> Collect safe"
  shows "do_intersection sctn X h \<le> SPEC (\<lambda>(PS, CXS, RS). flowsto_plane sctn X (CXS) (PS) (RS))"
  using \<open>X \<subseteq> Collect safe\<close>
  by (refine_vcg do_intersection_flowsto_spec[OF assms]) (auto intro!: flowsto_imp_flowsto_plane)

lemma inform_autoref[autoref_rules]: "(infnorm, infnorm) \<in> eucl_rel \<rightarrow> eucl_rel"
  by auto

definition "resolve_sctn sctn XS0 CXS0 =
  WHILE\<^bsup>(\<lambda>(XS, PS1, PS2, RS, CXS). flowsto_plane sctn XS0 CXS PS1 (XS \<union> RS) \<and> flowsto_plane sctn XS0 CXS {} (XS \<union> PS2 \<union> RS) \<and> CXS0 \<subseteq> CXS)\<^esup>
      (\<lambda>(XS, PS1, PS2, RS, CXS). XS \<noteq> {}) (\<lambda>(XS, PS1, PS2, RS, CXS).
  do {
    ASSERT (XS \<noteq> {});
    ((h, X), XS') \<leftarrow> split_spec_with_stepsize XS;
    let _ = trace_set (''next step in resolve_sctn using'') (Some X);
    ASSERT (X \<subseteq> Collect safe);
    ASSERT (XS' \<subseteq> Collect safe);
    ASSUME (ncc X);
    cXS::nat \<leftarrow> card_info XS;
    cPS1::nat \<leftarrow> card_info PS1;
    cPS2::nat \<leftarrow> card_info PS2;
    cRS::nat \<leftarrow> card_info RS;
    let _ = trace_set (''XS: '' @ show cXS) None;
    let _ = trace_set (''PS1: '' @ show cPS1) None;
    let _ = trace_set (''PS2: '' @ show cPS2) None;
    let _ = trace_set (''RS: '' @ show cRS) None;
    width_X \<leftarrow> width_spec X;
    if width_X > max_tdev_thres optns
    then do {
      (a, b) \<leftarrow> split_spec X;
      let splits = ({a, b}:::\<langle>\<langle>eucl_rel\<rangle>appr_rel\<rangle>list_wset_rel);
      CHECK_ALLSAFE splits;
      ASSERT (a \<subseteq> Collect safe);
      ASSERT (b \<subseteq> Collect safe);
      let a1 = (mk_coll a ::: \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel));
      let b1 = (mk_coll b ::: \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel));
      let a2 = (mk_coll (with_stepsize h a ::: \<langle>eucl_rel\<rangle>with_stepsize_rel) ::: \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>with_stepsize_rel));
      let b2 = (mk_coll (with_stepsize h b ::: \<langle>eucl_rel\<rangle>with_stepsize_rel) ::: \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>with_stepsize_rel));
      ASSUME (ncc a);
      ASSUME (ncc b);
      wa \<leftarrow> width_spec a;
      wb \<leftarrow> width_spec b;
      let _ = trace_set (''splitting: '' @ show (lfloat10 width_X) @ ''-->'' @ show (lfloat10 wa) @ '', ''  @ show (lfloat10 wb)) None;
      RETURN (XS' \<union> a2 \<union> b2 ::: \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>with_stepsize_rel),
        PS1, PS2, RS,
        (CXS \<union> a1 \<union> b1) ::: \<langle>eucl_rel\<rangle>coll_rel(\<langle>eucl_rel\<rangle>appr_rel))
    } else do {
      let _ = trace_set (''euler step: stepsize = '' @ show (lfloat10 h)) None;
      (h', error, CY, Y) \<leftarrow> choose_step X h;
      CHECK_ALLSAFE {Y, CY};
      ASSERT (Y \<subseteq> Collect safe);
      ASSERT (CY \<subseteq> Collect safe);
      ASSUME (ncc Y);
      ASSUME (ncc CY);
      let _ = trace_set (''error: '' @ show (lfloat10 error)) None;
      wX \<leftarrow> width_spec X;
      iX \<leftarrow> Inf_spec X;
      sX \<leftarrow> Sup_spec X;
      let aX = max (infnorm iX) (infnorm sX);
      if error > adaptive_atol optns      \<and> (* absolute error tolerance *)
        error > wX * adaptive_gtol optns \<and>  (* tolerance for growing of sets *)
        error > aX * adaptive_rtol optns     (* relative error tolerance *)
      then do {
        let _ = trace_set (''revoking step because of too large error'') None;
        RETURN (mk_coll (with_stepsize (h'/2) X) \<union> with_half_stepsizes XS', PS1, PS2, RS, CXS)
      } else do {
        i1 \<leftarrow> intersects_spec CY sctn;
        i2 \<leftarrow> intersects_spec Y sctn;
        if i1 \<or> i2 then (
          let _ = trace_set (''error OK, intersection '') None in
          if h' > max_intersection_step optns then do {
            let _ = trace_set (''revoke_intersection, can try with smaller steps'') None;
            RETURN (mk_coll (with_stepsize (h' / 2) X) \<union> XS', PS1, PS2, RS, CXS)
          } else do {
            let _ = trace_set (''do_intersection'') None;
            (PS', CXS', RS') \<leftarrow> do_intersection sctn X h';
            CHECK_ALLSAFE ({PS', CXS', RS'});
            let _ = trace_set (''done_intersection'') None;
            RETURN (XS', PS1 \<union> PS', mk_coll X \<union> PS2, RS \<union> RS', CXS \<union> CXS')
          }
        ) else do {
          let _ = trace_set (''error OK, resolve_sctn stepped '') None;
          let _ = trace_set (''interpolated step:'') (Some CY);
          let _ = print_set True CY;
          let _ = trace_set (''discrete step:'') (Some Y);
          let _ = print_set False Y;
          F \<leftarrow> ode_set Y;
          (n, _) \<leftarrow> strongest_transversal F;
          if n = normal sctn then
            RETURN (mk_coll (with_stepsize (min (3*h'/2) (max h' (truncate_down (precision optns) (h' * real_divl (precision optns) (adaptive_atol optns) (error))))) Y)
              \<union> XS', PS1, PS2, RS, CXS \<union> mk_coll CY)
          else
            RETURN (XS', PS1, PS2, mk_coll Y \<union> RS, CXS \<union> mk_coll CY)
        }
      }
    }
  })
  (with_stepsize (stepsize optns) XS0::: \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>with_stepsize_rel), {}, {}, {}, XS0 \<union> CXS0)"
sublocale autoref_op_pat_def resolve_sctn .

lemma op_set_isEmpty_coll_rel[autoref_rules]:
  shows
    "(\<lambda>xs. xs = Some [], op_set_isEmpty) \<in> \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel) \<rightarrow> bool_rel"
    "(\<lambda>xs. xs = Some [], op_set_isEmpty) \<in> \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>with_stepsize_rel) \<rightarrow> bool_rel"
  using safe_nonempty
  by (fastforce simp: default_rel_def relcomp_Image coll_rel_def list_wset_rel_def br_def set_rel_def appr_rel_def with_stepsize_rel_def snd_rel_def
    split: option.splits)+

lemma single_valued_snd_rel[relator_props]: "single_valued snd_rel"
  by (auto simp: snd_rel_def)

lemma single_valued_with_stepsize_rel[relator_props]:
  "single_valued (\<langle>eucl_rel\<rangle>with_stepsize_rel)"
  by (auto simp: with_stepsize_rel_def intro!: relator_props)

lemma Union_rel_eq: "{(x, y). \<Union>x = y} = br Union top"
  by (auto simp: br_def)

lemma single_valued_default_rel[relator_props]:
  "single_valued R \<Longrightarrow> single_valued (default_rel d R)"
  by (auto simp: default_rel_def single_valued_def split: option.splits)

lemma single_valued_coll_rel[relator_props]:
  "single_valued S \<Longrightarrow> single_valued R \<Longrightarrow> single_valued (\<langle>S\<rangle>coll_rel R)"
  unfolding relAPP_def
  by (auto simp: coll_rel_internal Union_rel_eq
    intro!: relator_props intro: single_valuedI
    split: option.splits)


definition uncoll::"'a set \<Rightarrow> 'a set" where "uncoll X = X"

lemma coll_rel_safe: "(xs, X) \<in> \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel) \<Longrightarrow> X \<subseteq> Collect safe"
  by (auto simp: coll_rel_def default_rel_def split: option.splits)

lemma CHECK_ALLSAFE_coll_autoref[autoref_rules]:
  "(\<lambda>x. RETURN (), CHECK_ALLSAFE) \<in> \<langle>\<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel)\<rangle>list_wset_rel \<rightarrow> \<langle>unit_rel\<rangle>nres_rel"
  by (auto simp: CHECK_ALLSAFE_def nres_rel_def list_wset_rel_def set_rel_def br_def
    dest!: coll_rel_safe)

schematic_goal resolve_sctn_impl:
  assumes prems: "DEFER_tag (0 < stepsize optns)" "DEFER_tag (0 < rk2_param optns)" "DEFER_tag (rk2_param optns \<le> 1)"
  assumes [autoref_rules]:
    "(XSi, XS) \<in> \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel)" "(CXSi, CXS) \<in> \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel)" "(sctni, sctn) \<in> Id"
  notes [autoref_tyrel]    = ty_REL[where 'a="'a set option" and R="\<langle>\<langle>eucl_rel\<rangle>appr_rel\<rangle>option_rel"]
  shows "(nres_of (?f::?'f dres), resolve_sctn $ sctn $ XS $ CXS)\<in>?R"
  using prems[unfolded autoref_tag_defs]
  unfolding resolve_sctn_def[abs_def]
  by (autoref_monadic)

concrete_definition resolve_sctn_impl for sctni XSi uses resolve_sctn_impl
lemmas [autoref_rules] = resolve_sctn_impl.refine

lemma Un_snd_sing_Pair_eq:
  "(e, f) \<in> a \<Longrightarrow> f \<union> (\<Union>x\<in>a - {(e, f)}. snd x) = (\<Union>x\<in>a. snd x)"
  by force

lemma let_unit: "Let X y = y ()" by simp

lemma
  resolve_sctn[THEN order_trans, refine_vcg]:
  assumes optns:
    "DEFER_tag (0 < stepsize optns)" "DEFER_tag (0 < rk2_param optns)" "DEFER_tag (rk2_param optns \<le> 1)"
    "DEFER_tag (X0S \<subseteq> Collect safe)" "DEFER_tag (CXS \<subseteq> Collect safe)"
  shows "resolve_sctn sctn X0S CXS \<le> SPEC (\<lambda>(XS, PS1, PS2, RS, CXS'). XS = {} \<and>
    flowsto_plane sctn (X0S) CXS' PS1 RS \<and>
    flowsto_plane sctn (X0S) CXS' {} (PS2 \<union> RS) \<and> CXS \<subseteq> CXS')"
  using assms[unfolded autoref_tag_defs]
  unfolding resolve_sctn_def
  apply (intro WHILEI_rule)
  subgoal by (auto intro!: flowsto_plane_self)
  defer
  subgoal by auto
  subgoal
    apply (refine_vcg refine_vcg)
    apply clarsimp_all
    subgoal by (auto dest!: flowsto_plane_safeD flowpipe_safeD)
    subgoal by (auto dest!: flowsto_plane_safeD flowpipe_safeD)
    subgoal premises prems for a b c d e f g
      using \<open>flowsto_plane sctn _ _ g _\<close>
      apply (rule flowsto_plane_subset)
      using prems by (auto dest!: flowsto_plane_safeD flowpipe_safeD)
    subgoal premises prems
      using \<open>flowsto_plane sctn _ _ {} _\<close>
      apply (rule flowsto_plane_subset)
      using prems by (auto dest!: flowsto_plane_safeD flowpipe_safeD)
    subgoal by auto
    subgoal premises prems for a b c d e f g h i j k l m n p q r s t u
      using flowsto_plane_trans[OF \<open>flowsto_plane sctn X0S d a (f \<union> u \<union> c)\<close> \<open>flowsto_plane sctn f s r t\<close>]
      apply (rule flowsto_plane_subset)
      using prems by (auto dest!: flowsto_plane_safeD flowpipe_safeD)
    subgoal premises prems
      using \<open>flowsto_plane sctn _ _ {} _\<close>
      apply (rule flowsto_plane_subset)
      using prems by (auto dest!: flowsto_plane_safeD flowpipe_safeD)
    subgoal by auto
    subgoal premises prems for a b c d e f g h i j k l m n p q s t u
    proof -
      from prems have h: "connected h" "h \<inter> plane_of sctn = {}"
        by (auto simp: ncc_def convex_connected)
      from flowsto_above_section[OF \<open>flowsto_plane sctn X0S a s (d \<union> b \<union> u)\<close>
        flowpipe_imp_flowsto[OF \<open>flowpipe _ _ _ _ _\<close>] h]
      have "flowsto_plane sctn X0S (a \<union> h) s (d \<union> b \<union> u - d \<union> i)" .
      then show ?thesis
        apply (rule flowsto_plane_subset)
        using prems
        by (auto dest!: flowsto_plane_safeD flowpipe_safeD intro: flowsto_plane_subset)
    qed
    subgoal premises prems for a b c d e f g h i j k l m n p q s t u
    proof -
      from prems have h: "connected h" "h \<inter> plane_of sctn = {}"
        by (auto simp: ncc_def convex_connected)
      from flowsto_above_section[OF \<open>flowsto_plane sctn X0S a {} (d \<union> b \<union> t \<union> u)\<close> flowpipe_imp_flowsto[OF \<open>flowpipe _ _ _ _ _\<close>] h]
      have "flowsto_plane sctn X0S (a \<union> h) {} (d \<union> b \<union> t \<union> u - d \<union> i)" .
      then show ?thesis
        apply (rule flowsto_plane_subset)
        using prems
        by (auto dest!: flowsto_plane_safeD flowpipe_safeD intro: flowsto_plane_subset)
    qed
    subgoal by auto
    subgoal premises prems for a b c d e f g h i j k l m n p q r s t u
    proof -
      from prems have h: "connected h" "h \<inter> plane_of sctn = {}"
        by (auto simp: ncc_def convex_connected)
      from flowsto_above_section[OF \<open>flowsto_plane sctn X0S b t (d \<union> s \<union> a)\<close> flowpipe_imp_flowsto[OF \<open>flowpipe d f f h i\<close>] h]
      have "flowsto_plane sctn X0S (b \<union> h) t (d \<union> s \<union> a - d \<union> i)" .
      then show ?thesis
        apply (rule flowsto_plane_subset)
        using prems
        by (auto dest!: flowsto_plane_safeD flowpipe_safeD intro: flowsto_plane_subset)
    qed
    subgoal premises prems for a b c d e f g h i j k l m n p q r s t u
    proof -
      from prems have h: "connected h" "h \<inter> plane_of sctn = {}"
        by (auto simp: ncc_def convex_connected)
      from flowsto_above_section[OF \<open>flowsto_plane sctn X0S b {} _\<close> flowpipe_imp_flowsto[OF \<open>flowpipe d f f h i\<close>] h]
      have "flowsto_plane sctn X0S (b \<union> h) {} (d \<union> s \<union> u \<union> a - d \<union> i)" .
      then show ?thesis
        apply (rule flowsto_plane_subset)
        using prems
        by (auto dest!: flowsto_plane_safeD flowpipe_safeD intro: flowsto_plane_subset)
    qed
    subgoal by auto
    done
  done


definition [refine_vcg_def]: "split_spec_exact x = SPEC (\<lambda>(a, b). x = a \<union> b)"
sublocale autoref_op_pat_def split_spec_with_stepsize .

lemma mem_appr_rel_list_wset_rel_iff:
  "(xs, X) \<in> \<langle>\<langle>eucl_rel\<rangle>appr_rel\<rangle>list_wset_rel \<longleftrightarrow> X = (set_of_appr ` set xs)"
  by (auto simp: list_wset_rel_def set_rel_def appr_rel_def br_def)

lemma mem_appr_rel_iff: "(x, y) \<in> \<langle>eucl_rel\<rangle>appr_rel \<longleftrightarrow> set_of_appr x = y"
  by (auto simp: appr_rel_def br_def)

lemma split_spec_exact_with_stepsize_autoref[autoref_rules]:
  "((\<lambda>xs. case xs of None \<Rightarrow> SUCCEED | Some [] \<Rightarrow> SUCCEED | Some (x#xs) \<Rightarrow> RETURN (x, Some xs)), split_spec_exact) \<in>
    \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel) \<rightarrow> \<langle>(\<langle>eucl_rel\<rangle>appr_rel) \<times>\<^sub>r \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel)\<rangle>nres_rel"
  by (subst (2) coll_rel_def)
    (fastforce simp: with_stepsize_rel_def nres_rel_def split_spec_exact_def default_rel_def
      simp: br_def mem_appr_rel_iff
      Some_mem_coll_rel_iff mem_appr_rel_list_wset_rel_iff
      split: list.splits option.splits
      intro!: RETURN_SPEC_refine exI[where x="set_of_appr x" for x] exI[where x="\<Union>(set_of_appr ` set (xs))" for xs] )

definition inter_overappr where [refine_vcg_def]: "inter_overappr X Y = SPEC (\<lambda>R. X \<inter> Y \<subseteq> R \<and> R \<subseteq> X)"

definition intersecting_sets where
  "intersecting_sets X Z = do {
    ASSERT (X \<subseteq> Collect safe);
    (_, R) \<leftarrow>
      WHILE (\<lambda>(X, _). X \<noteq> {}) (\<lambda>(X, R). do {
        (X, Y) \<leftarrow> split_spec_exact X;
        d \<leftarrow> disjoint_sets X Z;
        ASSERT (X \<subseteq> Collect safe);
        RETURN (Y, if d then R else (mk_coll X) \<union> R)
      }) (X, {});
    RETURN R
  }"
sublocale autoref_op_pat_def intersecting_sets .

lemma intersecting_sets_spec:
  assumes "X \<subseteq> Collect safe"
  shows "intersecting_sets X Y \<le> inter_overappr X Y"
  unfolding intersecting_sets_def inter_overappr_def
  using assms
  apply (refine_vcg)
  apply (rule WHILE_rule[where I="\<lambda>(Xs, R). (X - Xs) \<inter> Y \<subseteq> R \<and> R \<subseteq> X \<and> Xs \<subseteq> X"])
  subgoal by simp
  subgoal by (refine_vcg) (auto split: if_splits)
  subgoal by (refine_vcg)
  done

schematic_goal inter_overappr_impl:
  assumes [autoref_rules]: "(Xi,X)\<in>\<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel)"
  assumes [autoref_rules]: "(Zi,Z)\<in>\<langle>eucl_rel\<rangle>appr_rel"
  assumes safe: "DEFER_tag (X \<subseteq> Collect safe)"
  notes [autoref_rules(overloaded)] = coll_split
  shows "(?f, inter_overappr $ X $ Z)\<in>\<langle>\<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel)\<rangle>nres_rel"
  unfolding autoref_tag_defs
  using intersecting_sets_spec[OF safe[unfolded autoref_tag_defs]]
  apply (rule nres_rel_trans2)
  unfolding intersecting_sets_def[abs_def]
  by autoref_monadic

concrete_definition inter_overappr_impl for Xi Zi uses inter_overappr_impl
lemmas [autoref_rules] = inter_overappr_impl.refine

definition partition_set::"'a set \<Rightarrow> 'a set nres"
  where
 "partition_set xs = (if xs = {} then RETURN {} else do {
    ASSERT (xs \<noteq> {});
    ASSERT (xs \<subseteq> Collect safe);
    (i, s) \<leftarrow> ivl_of_set xs;
    ASSERT (i \<le> s);
    let r = {i .. s};
    CHECK_ALLSAFE {r};
    ASSERT (r \<subseteq> Collect safe);
    (rs, ps) \<leftarrow>
      WHILE\<^bsup>(\<lambda>(rs, ps). xs \<subseteq> rs \<union> ps \<and> rs \<union> ps \<subseteq> Collect safe)\<^esup> (\<lambda>(rs, ps). rs \<noteq> {})
      (\<lambda>(rs, ps).
      do {
        (r, rs') \<leftarrow> split_spec_exact rs;
        ASSERT (r \<subseteq> Collect safe);
        ASSERT (rs' \<subseteq> Collect safe);
        is \<leftarrow> inter_overappr xs (r);
        width \<leftarrow> width_spec r;
        let _ = trace_set (''partition loop'') None;
        if is = {} then RETURN (rs', ps)
        else do {
          ASSERT (is \<noteq> {});
          if width \<le> collect_granularity optns then
            RETURN (rs', mk_coll r \<union> ps)
          else do {
            (i', s') \<leftarrow> ivl_of_set is;
            (i, s) \<leftarrow> ivl_of_set r;
            let i'' = sup i i';
            let s'' = inf s s';
            CHECK (i'' \<le> s'');
            let r' = ({i'' .. s''} ::: \<langle>eucl_rel\<rangle>appr_rel);
            (a, b) \<leftarrow> split_spec r';
            (ia, sa) \<leftarrow> ivl_of_set a;
            (ib, sb) \<leftarrow> ivl_of_set b;
            let ia' = sup ia i'';
            let sa' = inf sa s'';
            let ib' = sup ib i'';
            let sb' = inf sb s'';
            CHECK (ia' \<le> sa');
            CHECK (ib' \<le> sb');
            let a' = ({ia' .. sa'} ::: \<langle>eucl_rel\<rangle>appr_rel);
            let b' = ({ib' .. sb'} ::: \<langle>eucl_rel\<rangle>appr_rel);
            CHECK_ALLSAFE {a', b'};
            ASSERT (a' \<subseteq> Collect safe);
            ASSERT (b' \<subseteq> Collect safe);
            RETURN (mk_coll a' \<union> mk_coll b' \<union> rs', ps)
          }
        }
      }) (mk_coll r, {});
    RETURN ps
  })"
sublocale autoref_op_pat_def partition_set .

lemma ivl_of_set_coll[autoref_rules]:
  assumes "PREFER_tag (X \<noteq> {})"
  assumes "(Xi, X) \<in> \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel)"
  shows "(nres_of (case Xi of None \<Rightarrow> dSUCCEED | Some Xi \<Rightarrow> ivl_of_sets_impl Xi), ivl_of_set $ X) \<in> \<langle>eucl_rel \<times>\<^sub>r eucl_rel\<rangle>nres_rel"
proof (cases Xi)
  fix Xi'
  assume s: "Xi = Some Xi'"
  from assms s have "ivl_of_sets $ set (map set_of_appr Xi') \<le> ivl_of_set $ X"
    unfolding autoref_tag_defs
    by refine_vcg (auto simp: ivl_of_set_def coll_rel_def list_wset_rel_def set_rel_def br_def appr_rel_def default_rel_def)
  moreover
  have rel: "(Xi', set (map set_of_appr Xi')) \<in> \<langle>\<langle>eucl_rel\<rangle>appr_rel\<rangle>list_wset_rel"
    by (auto simp: list_wset_rel_def coll_rel_def set_rel_def appr_rel_def br_def)
  ultimately
  have "(nres_of (ivl_of_sets_impl Xi'), ivl_of_set $ X) \<in> \<langle>eucl_rel \<times>\<^sub>r eucl_rel\<rangle>nres_rel"
    by (rule nres_rel_trans2[OF _ ivl_of_sets_impl.refine])
  then show ?thesis
    by (simp add: s)
next
  assume "Xi = None"
  then show ?thesis by (auto simp: ivl_of_set_def nres_rel_def)
qed

schematic_goal partition_set_impl:
  assumes [autoref_rules]: "(xsi,xs)\<in>\<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel)"
  notes [autoref_rules(overloaded)] = coll_split
  shows "((?f), partition_set $ xs)\<in>\<langle>\<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel)\<rangle>nres_rel"
  unfolding partition_set_def[abs_def]
  by (autoref_monadic)
concrete_definition partition_set_impl for xsi uses partition_set_impl
lemmas [autoref_rules] = partition_set_impl.refine

lemma partition_set_spec[THEN order_trans, refine_vcg]:
  assumes "XS \<subseteq> Collect safe"
  shows "partition_set XS \<le> SPEC (\<lambda>YS. XS \<subseteq> YS)"
  using assms
  unfolding partition_set_def
  apply (refine_vcg)
  subgoal by fastforce
  subgoal by fastforce
  subgoal by force
  subgoal
    apply clarsimp
    subgoal premises prems
      using prems(14,17,21,22,23,25,28,30,34,36,43,44)
      apply safe
      subgoal by fastforce
      subgoal by fastforce
      subgoal by fastforce
      subgoal by fastforce
      subgoal by fastforce
      subgoal by fastforce
      subgoal by (auto simp: subset_iff) blast
      subgoal by fastforce
      subgoal by fastforce
      subgoal by (auto simp: subset_iff) blast
      subgoal by fastforce
      subgoal by fastforce
      subgoal by fastforce
      subgoal by fastforce
      subgoal by fastforce
      subgoal by fastforce
      subgoal by fastforce
      subgoal by fastforce
      subgoal by fastforce
      subgoal by fastforce
      subgoal by fastforce
      subgoal by fastforce
      subgoal by fastforce
      subgoal by fastforce
      subgoal by (auto simp: subset_iff) blast
      subgoal by fastforce
      subgoal by fastforce
      subgoal by (auto simp: subset_iff) blast
      subgoal by fastforce
      subgoal by fastforce
      subgoal by fastforce
      subgoal by fastforce
      subgoal by fastforce
      subgoal by fastforce
      subgoal by fastforce
      subgoal by fastforce
      done
    done
  subgoal by simp blast
  done

definition "resolve_collect sctn X0s CX0s =
    do {
    (_, PS', PS0, RS, CXS) \<leftarrow> resolve_sctn sctn X0s CX0s;
    if (PS' = {}) then
      RETURN ({}, {}, RS, CXS)
    else do {
      ASSERT (PS' \<noteq> {});
      let _ = trace_set (''partitioning'') None;
      cPS \<leftarrow> partition_set PS';
      let _ = trace_set (''partitioned'') None;
      CHECK_ALLSAFE {cPS};
      card_cPS  \<leftarrow> card_info cPS;
      card_PS'  \<leftarrow> card_info PS';
      if reduce_number_factor optns * real card_cPS \<le> real card_PS'
      then RETURN (cPS, cPS, RS, CXS)
      else RETURN (PS0, cPS, RS, PS0 \<union> CXS)
    }
  }"
sublocale autoref_op_pat_def resolve_collect .

lemma real_autoref[autoref_rules]:
  "(real, real) \<in> nat_rel \<rightarrow> eucl_rel"
  by auto

schematic_goal resolve_collect_impl:
  assumes optns:
    "DEFER_tag (0 < stepsize optns)" "DEFER_tag (0 < rk2_param optns)" "DEFER_tag (rk2_param optns \<le> 1)"
  assumes [autoref_rules]: "(XSi, XS) \<in> \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel)" "(sctni, sctn) \<in> Id"
  assumes [autoref_rules]: "(CXSi, CXS) \<in> \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel)"
  shows "(nres_of (?f::?'c dres), resolve_collect $ sctn $ XS $ CXS)\<in>?R"
  using optns[unfolded autoref_tag_defs]
  unfolding resolve_collect_def[abs_def]
  by autoref_monadic

concrete_definition resolve_collect_impl for sctni XSi uses resolve_collect_impl
lemmas [autoref_rules] = resolve_collect_impl.refine

lemma CHECK_eq_ASSUME: "CHECK = ASSUME"
  by (auto simp: CHECK_def)

lemma resolve_collect_spec[THEN order_trans, refine_vcg]:
  assumes optns: "DEFER_tag (0 < stepsize optns)" "DEFER_tag (0 < rk2_param optns)" "DEFER_tag (rk2_param optns \<le> 1)"
  assumes init: "DEFER_tag (X0 \<subseteq> Collect safe)"
    and safe: "DEFER_tag (CX0S \<subseteq> Collect safe)"
  shows "resolve_collect sctn X0 CX0S \<le> (SPEC (\<lambda>(XS, XSg, RS, CXS). flowsto_plane sctn X0 CXS XSg RS \<and> flowsto_plane sctn X0 CXS {} (RS \<union> XS) \<and> CX0S \<subseteq> CXS))"
  unfolding resolve_collect_def conc_Id id_def
  apply (refine_vcg optns init safe)
  subgoal by (force dest!: flowsto_plane_safeD)
  subgoal by (auto) (meson Un_subset_iff flowsto_plane_safeD flowsto_plane_subset subset_refl)
  subgoal premises prems for x a b aa ba ab bb ac bc xa xb xc xd x1 x2 x1a x2a x1b x2b
  proof -
    {
      assume a1: "flowsto_plane sctn X0 x2b aa x1b"
      assume a2: "aa \<subseteq> x1a"
      assume a3: "x1a \<subseteq> Collect safe"
      have f5: "{} \<union> aa = aa"
        by simp
      have f6: "x1b \<union> x1a \<subseteq> Collect safe"
        using a3 a1 by (meson Un_subset_iff flowsto_plane_safeD)
      have f7: "\<And>A Aa. (A::'a set) \<subseteq> A \<union> Aa"
        by blast
      have "x1a \<union> aa = x1a"
        using a2 by (simp add: subset_antisym)
      then have "flowsto_plane sctn X0 x2b {} (x1b \<union> x1a)"
        using f7 f6 f5 a1 by (metis (no_types) flowsto_plane_subset3 flowsto_plane_weaken_intersection sup_assoc)
    } then show ?thesis using prems by auto
  qed
  subgoal by (auto) (meson Un_subset_iff flowsto_plane_safeD flowsto_plane_subset subset_refl)
  subgoal by (auto) (meson Un_subset_iff flowsto_plane_safeD flowsto_plane_subset subset_refl)
  subgoal by auto
  done

definition "max_height_sets b Xs = FORWEAK Xs (RETURN 0) (\<lambda>X. Sup_inner X b) (\<lambda>a b. RETURN (max a b))"
sublocale autoref_op_pat_def max_height_sets .

lemma Nil_list_wset_rel[simp]: "([], X) \<in> \<langle>A\<rangle>list_wset_rel \<longleftrightarrow> X = {}"
  by (auto simp: list_wset_rel_def br_def relcomp_unfold set_rel_def)

lemma empty_list_wset_rel[simp]: "(xs, {}) \<in> \<langle>A\<rangle>list_wset_rel \<longleftrightarrow> xs = []"
  by (force simp: list_wset_rel_def br_def relcomp_unfold set_rel_def)

lemma
  drop_if_refine:
  "a \<Longrightarrow> x \<le> (b::_ nres) \<Longrightarrow> x \<le> If a b c"
  "(\<not>a) \<Longrightarrow> x \<le> c \<Longrightarrow> x \<le> If a b c"
  by auto

lemma
  drop_if_if_refine:
  "x \<le> (If a b d::_ nres) \<Longrightarrow> x \<le> If a b (If a c d)"
  by auto

lemma list_wset_empty_iff: "(xs, X) \<in> \<langle>\<langle>eucl_rel\<rangle>appr_rel\<rangle>list_wset_rel \<Longrightarrow> X = {} \<longleftrightarrow> xs = []"
  by auto

lemma RETURN_op_refine: "RETURN x \<le> RETURN $ x"
  by (simp )

schematic_goal max_height_sets_impl:
  assumes ref[autoref_rules]: "(bi, b::'a) \<in> Id" "(XSi, XS) \<in> \<langle>\<langle>eucl_rel\<rangle>appr_rel\<rangle>list_wset_rel"
  notes [refine_transfer del] = FORWEAK_LIST_ne_plain.refine
  shows "(RETURN (?f::?'c), OP max_height_sets $ b $ XS)\<in>?R"
  unfolding max_height_sets_def autoref_tag_defs
  by (autoref_monadic (plain))
concrete_definition max_height_sets_impl for bi XSi uses max_height_sets_impl
lemma max_height_sets_impl_refine[autoref_rules]:
  "(\<lambda>bi XSi. RETURN (max_height_sets_impl bi XSi), max_height_sets) \<in> eucl_rel \<rightarrow> \<langle>\<langle>eucl_rel\<rangle>appr_rel\<rangle>list_wset_rel \<rightarrow> \<langle>eucl_rel\<rangle>nres_rel"
  using max_height_sets_impl.refine
  by auto

lemma max_height_spec[THEN order_trans, refine_vcg]:
  shows "max_height_sets b XS \<le> SPEC (\<lambda>r. \<forall>X \<in> XS. \<forall>x \<in> X. x \<bullet> b \<le> r)"
  unfolding max_height_sets_def[abs_def]
  by (auto intro!: refine_vcg FORWEAK_elementwise_rule)

definition [refine_vcg_def]: "max_height b X = SPEC (\<lambda>r. \<forall>x \<in> X. x \<bullet> b \<le> r)"
sublocale autoref_op_pat_def max_height .

definition [refine_vcg_def]: "sets_of_coll X = SPEC (\<lambda>XS. X = \<Union>XS)"
sublocale autoref_op_pat_def sets_of_coll .

lemma proj: \<comment>\<open>TODO: constant?\<close>
  shows "x \<in> Domain R \<Longrightarrow> (x, (SOME y. (x, y) \<in> R)) \<in> R"
  unfolding proj_def
  by (rule someI_ex) blast

lemma proj_image[simp]:
  assumes sv: "single_valued R" and dom: "S \<subseteq> Domain R"
  shows "(\<lambda>x. SOME y. (x, y) \<in> R) ` S = R `` S"
  using dom
  by (auto intro!: ImageI[OF proj] single_valuedD[OF sv _ proj])

lemma sets_of_coll_autoref[autoref_rules]:
  assumes [unfolded autoref_tag_defs, simp]: "PREFER single_valued R"
  shows "(\<lambda>x. case x of None \<Rightarrow> SUCCEED | Some x \<Rightarrow> RETURN x, sets_of_coll) \<in> \<langle>eucl_rel\<rangle> coll_rel R \<rightarrow> \<langle>\<langle>R\<rangle>list_wset_rel\<rangle>nres_rel"
proof -
  have "\<exists>x'. (y, x') \<in> {(c, a). a = set c} O {(S, S'). S' = R `` S \<and> S \<subseteq> Domain R} \<and> \<Union>(R `` set y) = \<Union>x'"
    "\<Union>(R `` set y) = Collect safe \<Longrightarrow>
      \<exists>x'. (y, x') \<in> {(c, a). a = set c} O {(S, S'). S' = R `` S \<and> S \<subseteq> Domain R} \<and> Collect safe = \<Union>x'"
    if "\<Union>(R `` set y) \<subseteq> Collect safe" "set y \<subseteq> Domain R"
    for y
    subgoal using that by (intro exI[where x="set (map ((\<lambda>x. SOME y. (x, y) \<in> R)) y)"]) auto
    subgoal using that by (intro exI[where x="set (map ((\<lambda>x. SOME y. (x, y) \<in> R)) y)"]) auto
    done
  then show ?thesis
    by (auto simp: sets_of_coll_def coll_rel_def list_wset_rel_def br_def set_rel_def default_rel_def
        nres_rel_def intro!: RETURN_SPEC_refine split: option.splits)
qed


lemma max_height_impl:
  fixes X::"'a set"
  shows "do { XS \<leftarrow> sets_of_coll X; max_height_sets b XS } \<le> (max_height b X)"
  unfolding max_height_def
  by refine_vcg

schematic_goal max_height_autoref[autoref_rules]:
  assumes ref[autoref_rules]: "(bi, b::'a) \<in> eucl_rel" "(XSi, XS) \<in> \<langle>eucl_rel\<rangle> coll_rel (\<langle>eucl_rel\<rangle>appr_rel)"
  shows "(nres_of (?f::?'c dres), max_height $ b $ XS)\<in>?R"
  unfolding max_height_sets_def autoref_tag_defs
  by (rule nres_rel_trans2[OF max_height_impl]) (autoref_monadic)

definition
  "defaultsec b si h' =
    (let h'' = h' + abs (min_section_distance optns) + abs si;
      sctn' =
          List.find
            (\<lambda>sctn. normal sctn = b \<and> h' \<le> pstn sctn \<and> (abs (h'' - pstn sctn) \<le> snap_sections optns
                  \<or> h'' \<ge> pstn sctn))
            (stop_sections optns@checkpoint_sections optns)
      in the_default (Sctn b h'') sctn')"
sublocale autoref_op_pat_def defaultsec .

lemma defaultsec_impl[autoref_rules]: "(defaultsec, defaultsec) \<in> eucl_rel \<rightarrow> eucl_rel \<rightarrow> eucl_rel \<rightarrow> Id"
  by auto

definition plane_rel_internal: "plane_rel soa R = br (\<lambda>(x, s). soa x \<inter> plane_of s) (\<lambda>(x, s). soa x \<subseteq> Collect safe) O \<langle>R\<rangle>set_rel"
lemma plane_rel_def: "\<langle>eucl_rel\<rangle>plane_rel soa = br (\<lambda>(x, s). soa x \<inter> plane_of s) (\<lambda>(x, s). soa x \<subseteq> Collect safe)"
  unfolding relAPP_def
  by (auto simp: plane_rel_internal)
lemmas [autoref_rel_intf] = REL_INTFI[of "plane_rel soa" "i_set" for soa]

definition appr_above_rel_internal: "appr_above_rel R = br (\<lambda>(x, s). set_of_appr x) (\<lambda>(x, s). set_of_appr x \<subseteq> below_halfspace s) O \<langle>R\<rangle>set_rel"
lemma appr_above_rel_def: "\<langle>eucl_rel\<rangle>appr_above_rel = br (\<lambda>(x, s). set_of_appr x) (\<lambda>(x, s). set_of_appr x \<subseteq> below_halfspace s)"
  unfolding relAPP_def
  by (auto simp: appr_above_rel_internal)
lemmas [autoref_rel_intf] = REL_INTFI[of "appr_above_rel" "i_set"]

lemma sv_appr_above_rel[relator_props]: "single_valued R \<Longrightarrow> single_valued (\<langle>R\<rangle>appr_above_rel)"
  and sv_plane_rel[relator_props]: "single_valued R \<Longrightarrow> single_valued (\<langle>R\<rangle>plane_rel soa)"
  unfolding relAPP_def
  by (auto simp: appr_above_rel_internal plane_rel_internal intro!: relator_props)


definition with_section::"'a sctn \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where [simp]: "with_section sctn X = X"

lemma mem_appr_above_rel_list_wset_rel_iff:
  "(xs, X) \<in> \<langle>\<langle>eucl_rel\<rangle>appr_above_rel\<rangle>list_wset_rel \<longleftrightarrow>
    (X = (\<lambda>(a, b). set_of_appr a) ` set xs \<and> (\<forall>(a, b) \<in> set xs. set_of_appr a \<subseteq> below_halfspace b))"
  by (fastforce simp: list_wset_rel_def set_rel_def appr_above_rel_def br_def)

lemma with_section_impl[autoref_rules]:
  assumes "(sctni, sctn) \<in> Id"
  assumes "(Xi, X) \<in> \<langle>eucl_rel\<rangle>coll_rel(\<langle>eucl_rel\<rangle>appr_rel)"
  assumes "SIDE_PRECOND (X \<subseteq> Collect (le_halfspace sctn))"
  shows "(map_option (map (\<lambda>x. (x, sctni))) Xi, with_section $ sctn $ X) \<in> \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_above_rel)"
  using assms
  by (cases Xi) (auto simp: Some_mem_coll_rel_iff mem_appr_rel_list_wset_rel_iff mem_appr_above_rel_list_wset_rel_iff)

definition Union_mk_coll_image::"'a set set \<Rightarrow> 'a set"
  where [simp]: "Union_mk_coll_image x = \<Union>(mk_coll ` x)"
sublocale autoref_op_pat_def Union_mk_coll_image .

lemma mk_coll_image_autoref[autoref_rules]:
  assumes "(xs, XX) \<in> \<langle>\<langle>eucl_rel\<rangle>appr_rel\<rangle>list_wset_rel"
  assumes "SIDE_PRECOND (\<Union>XX \<subseteq> Collect safe)"
  shows "(Some xs, Union_mk_coll_image $ XX) \<in> \<langle>eucl_rel\<rangle>coll_rel(\<langle>eucl_rel\<rangle>appr_rel)"
  using assms
  by (auto simp: coll_rel_def default_rel_def)

definition "next_sections d Xs =
  do {
    Xs \<leftarrow> sets_of_coll Xs ::: \<langle>\<langle>\<langle>eucl_rel\<rangle>appr_rel\<rangle>list_wset_rel\<rangle>nres_rel;
    M \<leftarrow> FORWEAK Xs (RETURN {}) (\<lambda>x. do {
        f \<leftarrow> ode_set x;
        (b, r) \<leftarrow> strongest_transversal f;
        RETURN {(b, r, x)}}) (\<lambda>a b. RETURN (a \<union> b));
    (_, R) \<leftarrow> WHILE (\<lambda>(m, _). m \<noteq> {}) (\<lambda>(m, m'). do {
        ASSERT (m \<noteq> {});
        (b, _, _)\<leftarrow>SPEC (\<lambda>x. x \<in> m);
        let xs = {x \<in> m. fst x = b};
        let m = {x \<in> m. fst x \<noteq> b};
        let XS = (snd ` snd ` xs ::: \<langle>\<langle>eucl_rel\<rangle>appr_rel\<rangle>list_wset_rel);
        ASSERT (XS \<noteq> {});
        h' \<leftarrow> max_height_sets b XS;
        ASSERT (xs \<noteq> {});
        f \<leftarrow> FORWEAK xs (RETURN 0) (\<lambda>a. RETURN (fst (snd a))) (\<lambda>x y. RETURN (max x y));
        si \<leftarrow> Sup_inner {(abs d * f)*\<^sub>Rb .. (abs d * f)*\<^sub>Rb} b; (* TODO: isnt that just abs d * f? *)
        let sctn = defaultsec b si h';
        ASSERT (\<Union>XS \<subseteq> Collect safe);
        let YS = Union_mk_coll_image XS;
        ASSERT (YS \<subseteq> Collect (le_halfspace sctn));
        RETURN (m, with_section sctn YS \<union> m')
      }) (M, {}:::\<langle>eucl_rel\<rangle>coll_rel(\<langle>eucl_rel\<rangle>appr_above_rel));
    RETURN R
  }"
sublocale autoref_op_pat_def next_sections .

lemma [autoref_rules]:
  "(abs, abs) \<in> Id \<rightarrow> Id"
  "(op @, op @) \<in> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel"
  "(op *\<^sub>R, op *\<^sub>R) \<in> Id \<rightarrow> Id \<rightarrow> Id"
  "(op +, op +) \<in> Id \<rightarrow> Id \<rightarrow> Id"
  "(List.find, List.find) \<in> (Id \<rightarrow> Id) \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>option_rel"
  "(Pair, Pair) \<in> (Id \<rightarrow> Id \<rightarrow> (Id \<times>\<^sub>r Id))"
  "(snd, snd) \<in> ((Id \<times>\<^sub>r Id) \<rightarrow> Id)"
  by auto

schematic_goal next_sections_abs_impl:
  assumes [autoref_rules]: "(XSi, XS) \<in> \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel)" "(di, d) \<in> Id"
  notes [autoref_tyrel] = ty_REL[where 'a="('a \<times> real \<times> 'a set) set" and R="\<langle>Id \<times>\<^sub>r Id \<times>\<^sub>r \<langle>eucl_rel\<rangle>appr_rel\<rangle>list_wset_rel"]
  shows "(nres_of ?f, next_sections $ d $ XS)\<in>\<langle>\<langle>eucl_rel\<rangle>coll_rel(\<langle>eucl_rel\<rangle>appr_above_rel)\<rangle>nres_rel"
  unfolding next_sections_def[abs_def]
  by autoref_monadic

concrete_definition next_sections_abs_impl for di XSi uses next_sections_abs_impl
lemmas [autoref_rules] = next_sections_abs_impl.refine

lemma snd_Pair_image: "snd ` (Pair x) ` X = X"
  by auto

lemma defaultsec_rule:
  assumes "l \<bullet> d \<le> g"
  shows "le_halfspace (defaultsec d i g) l"
proof -
  define h'' where "h'' \<equiv> g + \<bar>min_section_distance optns\<bar> + \<bar>i\<bar>"
  define sctn' where "sctn' \<equiv>
    List.find (\<lambda>sctn. normal sctn = d \<and> g \<le> pstn sctn \<and>
      (abs (h'' - pstn sctn) \<le> snap_sections optns \<or> h'' \<ge> pstn sctn))
      (stop_sections optns@checkpoint_sections optns)"
  from assms have "l \<bullet> d \<le> h''"
    by (auto simp: h''_def)
  show ?thesis
  proof (cases "sctn'")
    case None
    then show ?thesis
      by (auto simp: defaultsec_def Let_def le_halfspace_def
          sctn'_def[symmetric] h''_def[symmetric] \<open>l \<bullet> d \<le> h''\<close>)
  next
    case (Some sctn)
    from find_SomeD[OF this[unfolded sctn'_def]]
    have
      "normal sctn = d" "g \<le> pstn sctn"
      by auto
    then show ?thesis
      using \<open>l \<bullet> d \<le> g\<close>
      unfolding defaultsec_def Let_def h''_def[symmetric] sctn'_def[symmetric] Some the_default.simps
        le_halfspace_def
      by auto
  qed
qed

lemma next_sections_spec[THEN order_trans, refine_vcg]:
  assumes "X \<subseteq> Collect safe"
  notes Diff_Diff_Int[simp]
  shows "next_sections d X \<le> SPEC (\<lambda>R. X = R)"
  unfolding next_sections_def autoref_tag_defs
  apply (refine_vcg)
  subgoal for XS
    apply (rule FORWEAK_case_rule[where I="\<lambda>I R. XS - (I - snd ` snd ` R) = snd ` snd ` R"])
    subgoal by (refine_vcg WHILE_rule[where I="\<lambda>(old, new). old = {} \<and> new = {}"])
    subgoal by (refine_vcg)
    subgoal by (refine_vcg)
    subgoal by (refine_vcg) auto
    subgoal by refine_vcg auto
    subgoal
      apply (refine_vcg WHILE_rule[where I="\<lambda>(old, new). X = \<Union>(snd ` snd ` old) \<union> new"])
      subgoal by force
      subgoal
        apply (rule order_trans[OF FORWEAK_elementwise_rule[where Q="\<lambda>a b. fst (snd a) \<le> b"]])
        subgoal by force
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal
          using assms by (refine_vcg) (auto intro!: defaultsec_rule dest: make_neg_goal)
        done
      done
    done
  done

definition split_above_sctn::"'a set \<Rightarrow> (('a set \<times> 'a sctn) \<times> 'a set) nres"
  where [refine_vcg_def]: "split_above_sctn X = SPEC (\<lambda>((Y, sctn), YS). X = Y \<union> YS \<and> Y \<subseteq> Collect (le_halfspace sctn))"

abbreviation "splitbysndimpl xs \<equiv> do {
  let s = snd (hd xs);
  let (ys, zs) = List.partition (\<lambda>(_, sctn). sctn = s) xs;
  RETURN ((map fst ys, s), zs)
}"

lemma split_above_sctn_autoref[autoref_rules]:
  assumes "(xs, X) \<in> \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_above_rel)"
  shows
    "(case xs of None \<Rightarrow> SUCCEED | Some xs \<Rightarrow> do { ((xs, sctn), ys) \<leftarrow> splitbysndimpl xs; RETURN ((Some xs, sctn), Some ys)},
    split_above_sctn $ X) \<in>
    \<langle>(\<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel) \<times>\<^sub>r Id) \<times>\<^sub>r \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_above_rel)\<rangle>nres_rel"
  using assms
  apply (cases xs)
  subgoal by (auto simp: nres_rel_def)
  subgoal premises prems for ys
  proof -
    have "x \<in> set_of_appr a \<Longrightarrow> (a, snd (hd ys)) \<in> set ys \<Longrightarrow> \<exists>xa\<in>set ys. x \<in> set_of_appr (fst xa)"
      for x a
      by force
    moreover have "x \<in> set_of_appr a \<Longrightarrow> (a, b) \<in> set ys \<Longrightarrow> b \<noteq> snd (hd ys) \<Longrightarrow> \<exists>xa\<in>set ys. x \<in> set_of_appr (fst xa)"
      for x a b
      by (metis fst_conv)
    ultimately show ?thesis
      using prems
      by (fastforce simp: Some_mem_coll_rel_iff mem_appr_above_rel_list_wset_rel_iff
        mem_appr_rel_list_wset_rel_iff Let_def split_above_sctn_def split_beta'
        intro!: nres_relI RETURN_SPEC_refine)
  qed
  done

definition split_by_sctn::"'a set \<Rightarrow> ('a set \<times> 'a set) nres"
  where [refine_vcg_def]: "split_by_sctn X = SPEC (\<lambda>(Y, YS). X = Y \<union> YS)"

abbreviation "appr_plane_rel \<equiv> plane_rel set_of_appr"


lemma mem_plane_rel_list_wset_rel_iff:
  "(a, b) \<in> \<langle>\<langle>eucl_rel\<rangle>plane_rel s\<rangle>list_wset_rel \<longleftrightarrow>
  (b = (\<lambda>(i, sctn). s i \<inter> plane_of sctn) ` set a) \<and> (\<forall>(i, _) \<in> set a. s i \<subseteq> Collect safe)"
  by (fastforce simp: list_wset_rel_def set_rel_def plane_rel_def br_def)

lemma split_by_sctn_appr_plane_autoref[autoref_rules]:
  assumes "(xs, X) \<in> \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_plane_rel)"
  shows
    "(case xs of None \<Rightarrow> SUCCEED | Some xs \<Rightarrow> let (a, b) = List.partition (\<lambda>(_, sctn). sctn = snd (hd xs)) xs in RETURN (Some a, Some b),
    split_by_sctn $ X) \<in>
    \<langle>\<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_plane_rel) \<times>\<^sub>r \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_plane_rel)\<rangle>nres_rel"
  using assms
  apply (cases xs)
  subgoal by (auto simp: nres_rel_def)
  subgoal premises prems for ys
  proof -
    have "x \<in> plane_of (snd (hd ys)) \<Longrightarrow>
           x \<in> set_of_appr a \<Longrightarrow>
           (a, snd (hd ys)) \<in> set ys \<Longrightarrow> \<exists>xa\<in>set ys. x \<in> set_of_appr (fst xa) \<and> x \<in> plane_of (snd xa)"
      for x a
      by (metis snd_conv fst_conv)
    moreover
    have "x \<in> set_of_appr a \<Longrightarrow>
             x \<in> plane_of b \<Longrightarrow>
             (a, b) \<in> set ys \<Longrightarrow> b \<noteq> snd (hd ys) \<Longrightarrow> \<exists>xa\<in>set ys. x \<in> set_of_appr (fst xa) \<and> x \<in> plane_of (snd xa)"
      for x a b
      by (metis snd_conv fst_conv)
    ultimately show ?thesis
      using prems
      by (fastforce simp: Some_mem_coll_rel_iff mem_appr_above_rel_list_wset_rel_iff
          mem_plane_rel_list_wset_rel_iff
          mem_appr_rel_list_wset_rel_iff Let_def split_by_sctn_def split_beta'
          intro!: nres_relI RETURN_SPEC_refine)
  qed
  done

definition unplane::"'a set \<Rightarrow> 'a set nres"
  where [refine_vcg_def]: "unplane X = SPEC (\<lambda>R. X \<subseteq> R \<and> R \<subseteq> Collect safe)"
sublocale autoref_op_pat_def unplane .

lemma unplane_impl[autoref_rules]:
  "(\<lambda>xs. RETURN (map_option (map fst) xs), unplane) \<in> \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_plane_rel) \<rightarrow> \<langle>\<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel)\<rangle>nres_rel"
  apply (safe intro!: nres_relI )
  subgoal for xs X
    apply (cases xs)
    subgoal by (auto simp: unplane_def intro!: RETURN_SPEC_refine)
    subgoal premises prems for ys
    proof -
      have "(a, b) \<in> set ys \<Longrightarrow> x \<in> set_of_appr a \<Longrightarrow> \<exists>xa\<in>set ys. x \<in> set_of_appr (fst xa)"
        for a b x by (metis fst_conv)
      then show ?thesis
        using prems
        by (fastforce simp: Some_mem_coll_rel_iff mem_plane_rel_list_wset_rel_iff
            mem_appr_rel_list_wset_rel_iff unplane_def
            intro!: RETURN_SPEC_refine)
    qed
    done
  done

definition
  next_sections_collection::"'a set \<Rightarrow> 'a set nres"
where
  "next_sections_collection X =
    do {
      (_, R, _) \<leftarrow> WHILE (\<lambda>(X, R, ne). ne) (\<lambda>(X, R, _). do {
          (X, Y) \<leftarrow> split_by_sctn X;
          X' \<leftarrow> unplane X;
          Y' \<leftarrow> unplane Y;
          X' \<leftarrow> next_sections (next_section_distance_factor optns * stepsize optns) X';
          RETURN (Y, X' \<union> R, Y' \<noteq> {})
        }) (X, {}, True);
      RETURN R
    }"
sublocale autoref_op_pat_def next_sections_collection .

lemma op_set_isEmpty_appr_above_rel_coll_rel[autoref_rules]:
  "(\<lambda>xs. xs = Some [], op_set_isEmpty) \<in> \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_above_rel) \<rightarrow> bool_rel"
proof -
  have "x = []"
    if "safe k" "\<forall>x\<in>\<langle>eucl_rel\<rangle>appr_above_rel `` set x. x = {}" "set x \<subseteq> Domain (\<langle>eucl_rel\<rangle>appr_above_rel)"
    for k x
  proof (rule ccontr)
    assume "x \<noteq> []"
    then obtain y where "y \<in> set x" by blast
    then have "y \<in> Domain (\<langle>eucl_rel\<rangle>appr_above_rel)"
      using that by auto
    then have "set_of_appr (fst y) \<in> \<langle>eucl_rel\<rangle>appr_above_rel `` set x"
      using \<open>y \<in> set x\<close>
      by (auto simp: appr_above_rel_def br_def intro!: bexI[where x=y])
    from that(2)[rule_format, OF this]
    show False by simp
  qed
  then show ?thesis
    using safe_nonempty
    by (auto simp: relcomp_Image coll_rel_def list_wset_rel_def br_def set_rel_def
        with_stepsize_rel_def snd_rel_def Image_UN split_beta' default_rel_def split: option.splits)
qed

schematic_goal next_sections_collection_impl:
  assumes [autoref_rules]: "(cpsi, cps) \<in> \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_plane_rel)"
  notes [autoref_post_simps] = map_map o_def
  shows "(nres_of(?f::?'c dres), next_sections_collection $ cps)\<in>?R"
  unfolding next_sections_collection_def[abs_def]
  using [[autoref_trace, autoref_trace_failed_id]]
  by autoref_monadic
concrete_definition next_sections_collection_impl for cpsi uses next_sections_collection_impl
lemmas [autoref_rules] = next_sections_collection_impl.refine

lemma next_sections_collection_set[THEN order_trans, refine_vcg]: "next_sections_collection cps \<le> SPEC (\<lambda>R. cps \<subseteq> R \<and> R \<subseteq> Collect safe)"
  unfolding next_sections_collection_def
  by (refine_vcg WHILE_rule[where I="\<lambda>(X, R, b). cps \<subseteq> X \<union> R \<and> R \<subseteq> Collect safe \<and> (\<not> b \<longrightarrow> X = {})"]) auto

definition inter_plane::"'a set \<Rightarrow> 'a sctn \<Rightarrow> 'a set nres"
where [refine_vcg_def]: "inter_plane X sctn = SPEC (\<lambda>R. R = X \<inter> plane_of sctn)"
sublocale autoref_op_pat_def inter_plane .

lemma inter_plane_autoref[autoref_rules]:
  assumes "SIDE_PRECOND (XS \<subseteq> Collect safe)"
  assumes "(xs, XS) \<in>  \<langle>eucl_rel\<rangle>coll_rel(\<langle>eucl_rel\<rangle>appr_rel)"
  assumes "(sctni, sctn) \<in> Id"
  shows "(case xs of None \<Rightarrow> SUCCEED | Some xs \<Rightarrow> RETURN (Some ((map (\<lambda>x. (x, sctni))) xs)),
      inter_plane $ XS $ sctn) \<in>
    \<langle>\<langle>eucl_rel\<rangle>coll_rel(\<langle>eucl_rel\<rangle>appr_plane_rel)\<rangle>nres_rel"
  using assms
  apply (cases xs)
  subgoal by (auto simp: inter_plane_def nres_relI)
  subgoal for ys
    by (fastforce simp: Some_mem_coll_rel_iff mem_appr_rel_list_wset_rel_iff
      RETURN_RES_refine_iff inter_plane_def mem_plane_rel_list_wset_rel_iff
        intro!: nres_relI RETURN_SPEC_refine)
  done

definition "poincare_distance_d X0s CX0s =
  do {
    ASSERT (X0s \<subseteq> Collect (le_halfspace (start_section optns)));
    (_, _, stops, reachable, _) \<leftarrow>
      WHILE (\<lambda>(unres, cps, stops, reachable, checkpointed). \<not> checkpointed \<or> unres \<noteq> {})
          (\<lambda>(unres, cps, stops, reachable, checkpointed). do {
        if (unres \<noteq> {})
        then do {
          let _ = trace_set (''new round'') None;
          ((XS, sctn), unres) \<leftarrow> split_above_sctn unres;
          (XS, XSg, RS, CXS) \<leftarrow> resolve_collect sctn XS reachable;
          let _ = trace_set (''resolve_collected'') None;
          ASSERT (XSg \<subseteq> Collect safe);
          let _ = trace_set (''next sections'') None;
          RS' \<leftarrow> next_sections (next_section_turn_distance_factor optns * stepsize optns) RS;
          let _ = trace_set (''next sections ed'') None;
          if sctn \<in> set (stop_sections optns) then do {
            let _ = trace_set (''inter plane 1'') None;
            i \<leftarrow> inter_plane XSg sctn;
            let _ = trace_set (''inter planed 1'') None;
            RETURN (unres \<union> RS', cps, i \<union> stops, CXS, False)
          } else if sctn \<in> set (checkpoint_sections optns) then do {
            let _ = trace_set (''inter plane 2'') None;
            i \<leftarrow> inter_plane XSg sctn;
            let _ = trace_set (''inter planed 2'') None;
            RETURN (unres \<union> RS', i \<union> cps, stops, CXS, False)
          } else do {
            let _ = trace_set (''next sections 2'') None;
            XS' \<leftarrow> next_sections (next_section_distance_factor optns * stepsize optns) XS;
            let _ = trace_set (''next sections 2ed'') None;
            RETURN (unres \<union> XS' \<union> RS', cps, stops, CXS, False)
          }
        } else do {
          let _ = trace_set (''next sections_collection '') None;
          unres'' \<leftarrow> next_sections_collection cps;
          let _ = trace_set (''next sections_collectioned'') None;
          RETURN (unres'', {}, stops, reachable, True)
        }
      }) (with_section (start_section optns) X0s, {},
        {}, X0s \<union> CX0s, False);
    RETURN (stops, reachable)
  }"
sublocale autoref_op_pat_def poincare_distance_d .

schematic_goal poincare_distance_d_impl:
  assumes optns: "DEFER_tag (0 < stepsize optns)" "DEFER_tag (0 < rk2_param optns)" "DEFER_tag (rk2_param optns \<le> 1)"
  assumes [autoref_rules]: "(XSi, XS) \<in> \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel)" "(CXSi, CXS) \<in> \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel)"
  shows "( (?f::?'c nres), poincare_distance_d $ XS $ CXS)\<in>?R"
  unfolding poincare_distance_d_def[abs_def]
  using optns[unfolded autoref_tag_defs]
  by (autoref_monadic)

concrete_definition poincare_distance_d_impl for XSi CXSi uses poincare_distance_d_impl
lemmas [autoref_rules] = poincare_distance_d_impl.refine

lemma flowsto_step:
  assumes x: "flowsto X0 CX X1"
  assumes y: "flowsto Y0 CY Y1"
  shows "flowsto X0 (CX \<union> CY) (X1 - Y0 \<union> Y1)"
  apply (rule flowsto_subset[OF flowsto_trans_Un[of X0 CX Y0 "X1 - Y0" CY Y1, OF flowsto_subset[OF x] y]])
  using x y
  by (auto dest!: flowsto_safeD)

lemma plane_of_subset_halfspace: "plane_of sctn \<subseteq> Collect (le_halfspace sctn)"
  by (auto simp: plane_of_def le_halfspace_def)

lemma poincare_distance_d[THEN order_trans, refine_vcg]:
  assumes [refine_vcg]: "DEFER_tag (0 < stepsize optns)" "DEFER_tag (0 < rk2_param optns)" "DEFER_tag (rk2_param optns \<le> 1)"
  assumes start_below[refine_vcg]: "DEFER_tag (X0S \<subseteq> Collect (le_halfspace (start_section optns)))"
  assumes start_safe[refine_vcg]:  "DEFER_tag (X0S \<subseteq> Collect safe)"  "DEFER_tag (CX0S \<subseteq> Collect safe)"
  shows "poincare_distance_d X0S CX0S \<le>
    SPEC (\<lambda>(stops, CX). flowsto (X0S \<inter> below_halfspace (start_section optns)) CX stops)"
  using start_below start_safe
  unfolding poincare_distance_d_def autoref_tag_defs
  apply (refine_vcg WHILE_rule[where I="\<lambda>(unres, cps, stops, reachable, checkpointed).
        (checkpointed \<longrightarrow> cps = {}) \<and>
        (flowsto (X0S) reachable (unres \<union> cps \<union> stops)) \<and>
        CX0S \<subseteq> reachable"])
  apply clarsimp_all
  subgoal using start_below start_safe by (auto simp: Int_absorb2 subset_iff intro!: flowsto_self)
  subgoal by (auto dest!: flowsto_safeD)
  subgoal by (auto dest!: flowsto_safeD)
  subgoal by (auto dest!: flowsto_plane_safeD)
  subgoal by (auto dest!: flowsto_plane_safeD)
  subgoal premises prems for a b c d e f g h i j k l
  proof -
    from prems have "flowsto X0S b (e \<union> d \<union> j \<union> a)"
      "flowsto (e \<inter> Collect (le_halfspace f)) k (h \<inter> plane_of f \<union> i \<inter> Collect (le_halfspace f))"
      by (simp_all add: flowsto_plane_def)
    from flowsto_step[OF this]
    show "flowsto X0S k (d \<union> i \<union> j \<union> (h \<inter> plane_of f \<union> a))"
      apply (rule flowsto_subset)
      using prems
      by (auto simp: inter_plane_def dest!: flowsto_plane_safeD flowsto_safeD)
  qed
  subgoal by auto
  subgoal premises prems for a b c d e f g h i j k l
  proof -
    from prems have "flowsto X0S b (e \<union> d \<union> a \<union> j)"
      "flowsto (e \<inter> Collect (le_halfspace f)) k (h \<inter> plane_of f \<union> i \<inter> Collect (le_halfspace f))"
      by (simp_all add: flowsto_plane_def)
    from flowsto_step[OF this]
    show "flowsto X0S k (d \<union> i \<union> (h \<inter> plane_of f \<union> a) \<union> j)"
      apply (rule flowsto_subset)
      using prems
      by (auto simp: inter_plane_def dest!: flowsto_plane_safeD flowsto_safeD)
  qed
  subgoal by auto
  subgoal by (auto dest!: flowsto_plane_safeD)
  subgoal premises prems for a b c d e f g h i j k l
  proof -
    from prems have "flowsto X0S a (d \<union> c \<union> i \<union> j)"
      "flowsto (d \<inter> Collect (le_halfspace e)) k ((g \<union> h) \<inter> Collect (le_halfspace e))"
      by (simp_all add: flowsto_plane_def)
    from flowsto_step[OF this]
    show "flowsto X0S k (c \<union> h \<union> g \<union> i \<union> j)"
      apply (rule flowsto_subset)
      using prems
      by (auto simp: inter_plane_def dest!: flowsto_plane_safeD flowsto_safeD)
  qed
  subgoal by auto
  subgoal apply (rule flowsto_subset, assumption) by (auto dest!: flowsto_safeD)
  subgoal using start_below start_safe by (auto simp: flowsto_inter1)
  done

definition explicit_appr_plane :: "'a set \<Rightarrow> ('a set \<times> 'a sctn) set nres"
where "explicit_appr_plane X = SPEC (\<lambda>R. X = (\<Union>(X, sctn) \<in> R. X \<inter> plane_of sctn))"
sublocale autoref_op_pat_def explicit_appr_plane .

lemma mem_appr_rel_prod_rel_list_wset_rel_iff:
  "(xs, X) \<in> \<langle>\<langle>eucl_rel\<rangle>appr_rel \<times>\<^sub>r Id\<rangle>list_wset_rel \<longleftrightarrow> X = (\<lambda>(a, b). (set_of_appr a, b)) ` set xs"
  by (fastforce simp: list_wset_rel_def set_rel_def br_def appr_rel_def prod_rel_def)

lemma explicit_appr_plane_autoref[autoref_rules]:
  "(\<lambda>x. case x of None \<Rightarrow> SUCCEED | Some x \<Rightarrow> RETURN x, explicit_appr_plane) \<in>
    \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_plane_rel) \<rightarrow> \<langle>\<langle>\<langle>eucl_rel\<rangle>appr_rel \<times>\<^sub>r Id\<rangle>list_wset_rel\<rangle>nres_rel"
  apply (safe intro!: nres_relI)
  subgoal for xs X
    by (cases xs)
      (auto intro!: nres_relI simp: explicit_appr_plane_def Some_mem_coll_rel_iff
        mem_plane_rel_list_wset_rel_iff mem_appr_rel_prod_rel_list_wset_rel_iff
          intro!: RETURN_SPEC_refine)
  done

definition irects_of_set_encl::"'a set \<times> 'a sctn \<Rightarrow> ((int list \<times> 'a sctn) set) option nres"
  \<comment>\<open>TODO: improve by checking intersection, not just box enclosure\<close>
where "irects_of_set_encl Xsctn =
  do {
    CHECK (normal (snd Xsctn) \<in> set Basis_list \<or> - normal (snd Xsctn) \<in> set Basis_list);
    ASSUME (ncc (fst Xsctn));
    X \<leftarrow> project_set (fst Xsctn) (normal (snd Xsctn)) (pstn (snd Xsctn));
    let sctn = snd Xsctn;
    I \<leftarrow> Inf_spec X;
    S \<leftarrow> Sup_spec X;
    let i0s = [floor ((I\<bullet>b) * 2^(irect_mod optns)). b\<leftarrow>Basis_list];
    let s0s = [floor ((S\<bullet>b) * 2^(irect_mod optns)). b\<leftarrow>Basis_list];
    let res = set (map (\<lambda>x. (x, snd Xsctn)) (product_lists (map (\<lambda>(i, s). [i..s]) (zip i0s s0s))));
    CHECK_ALLSAFE (set_of_irect (irect_mod optns) ` fst ` res);
    RETURN (Some res)
  }"
sublocale autoref_op_pat_def irects_of_set_encl .

schematic_goal irects_of_set_encl_impl:
  fixes b y
  assumes [autoref_rules]: "(Xsctni, Xsctn) \<in> \<langle>eucl_rel\<rangle>appr_rel\<times>\<^sub>rId"
  shows "(?f::?'r, irects_of_set_encl Xsctn) \<in> ?R"
  unfolding irects_of_set_encl_def[abs_def] autoref_tag_defs
  by autoref_monadic
concrete_definition irects_of_set_encl_impl for Xsctni uses irects_of_set_encl_impl
lemma irects_of_set_encl_impl_refine[autoref_rules]:
  "((\<lambda>x. nres_of (irects_of_set_encl_impl x)),
    irects_of_set_encl) \<in>
    (\<langle>eucl_rel\<rangle>appr_rel\<times>\<^sub>rId) \<rightarrow> \<langle>\<langle>\<langle>\<langle>int_rel\<rangle>list_rel \<times>\<^sub>r Id\<rangle>list_wset_rel\<rangle>option_rel\<rangle>nres_rel"
  using irects_of_set_encl_impl.refine
  by auto

lemma project_set_inter_appr[THEN order_trans, refine_vcg]:
  fixes X::"'a set"
  notes project_set_def[refine_vcg_def]
  assumes X: "X \<noteq> {}"
  assumes n: "n \<in> Basis \<or> - n \<in> Basis"
  defines "n' \<equiv> - n"
  shows "project_set X n c \<le> SPEC (\<lambda>R. X \<inter> plane_of (Sctn n c) \<subseteq> R)"
  using n
  apply (rule disjE)
    subgoal
      using X n
      apply refine_vcg
      subgoal by (meson nonemptyE order.trans)
      subgoal
        by (auto simp: plane_of_def eucl_le[where 'a='a] inner_add_left inner_diff_left inner_Basis
            split: if_splits)
      done
    subgoal
    proof -
      have *: "n = -n'"
        by (simp add: n'_def)
      assume "- n \<in> Basis"
      then show ?thesis
        using X n
        unfolding *
        apply refine_vcg
        subgoal by (meson nonemptyE order.trans)
        subgoal by (auto simp: plane_of_def eucl_le[where 'a='a] inner_add_left inner_diff_left inner_Basis split: if_splits)
        done
    qed
  done

lemma irects_of_set_encl_spec[THEN order_trans, refine_vcg]:
  shows "irects_of_set_encl X \<le> SPEC (\<lambda>s. \<exists>R. s = Some R \<and>
    fst X \<inter> plane_of (snd X) \<subseteq> (\<Union>(r, sctn)\<in>R. set_of_irect (irect_mod optns) r \<inter> plane_of sctn) \<and>
    (\<Union>(r, sctn)\<in>R. set_of_irect (irect_mod optns) r) \<subseteq> Collect safe)"
  unfolding irects_of_set_encl_def
  apply (refine_vcg)
  subgoal by (auto simp: ncc_def)
  subgoal premises prems for a b c d
  proof -
    let ?P = "set (product_lists
      (map (\<lambda>(x, y). [x..y])
      (zip (map (\<lambda>ba. \<lfloor>b \<bullet> ba * 2 ^ irect_mod optns\<rfloor>) Basis_list)
      (map (\<lambda>b. \<lfloor>c \<bullet> b * 2 ^ irect_mod optns\<rfloor>) Basis_list))))"
    have "fst X \<inter> plane_of (snd X) \<subseteq> UNION ?P (set_of_irect (int (irect_mod optns)))"
      apply (auto simp: set_of_irect_def product_lists_set)
      subgoal premises prems' for f
      proof -
        have "b \<le> f" "f \<le> c"
          using prems prems'
          by auto
        moreover
        have x: "x * 2 ^ irect_mod optns * 2 powr - real (irect_mod optns) = x" for x
          by (auto simp: powr_realpow[symmetric] powr_add[symmetric] ac_simps)
        then have
          "(\<Sum>b\<in>Basis. (real_of_int \<lfloor>f \<bullet> b * 2 ^ irect_mod optns\<rfloor> * 2 powr - real (irect_mod optns)) *\<^sub>R b) \<le> f"
          "f \<le> (\<Sum>b\<in>Basis. ((real_of_int \<lfloor>f \<bullet> b * 2 ^ irect_mod optns\<rfloor> + 1) * 2 powr - real (irect_mod optns)) *\<^sub>R b)"
          using prems prems'
          by (auto simp: eucl_le[where 'a='a] x
              intro!: order_trans[OF mult_right_mono[OF of_int_floor_le]]
                order_trans[OF _ mult_right_mono[OF real_of_int_floor_add_one_ge]])
        ultimately show ?thesis
          using prems'
          by (auto
              simp: set_zip zip_map1 zip_same_conv_map
              intro!: exI[where x = "map (\<lambda>b. \<lfloor>f \<bullet> b * 2 ^ irect_mod optns\<rfloor>) Basis_list"] list_all2I
              floor_mono mult_right_mono inner_Basis_mono)
      qed
      done
    moreover
    have "(\<Union>x\<in>?P. set_of_irect (int (irect_mod optns)) x) \<subseteq> Collect safe"
      using prems(6)
      by auto
    ultimately show ?thesis by auto
  qed
  done

definition irects_of_appr_plane::"'a set \<Rightarrow> 'a set nres" where
  [refine_vcg_def]: "irects_of_appr_plane x = SPEC (\<lambda>r. x \<subseteq> r \<and> r \<subseteq> Collect safe)"
sublocale autoref_op_pat_def irects_of_appr_plane .

lemma Some_mem_default_rel: "(Some x, y) \<in> default_rel d R \<longleftrightarrow> (x, y) \<in> R"
  by (auto simp: default_rel_def)

lemma option_rel_inverse[simp]: "(\<langle>R\<rangle>option_rel)\<inverse> = \<langle>R\<inverse>\<rangle>option_rel"
  by (auto simp: option_rel_def)

lemma irects_of_appr_plane_ref[autoref_rules]:
  shows "(\<lambda>x. nres_of (irects_of_set_encl_impl x), irects_of_appr_plane) \<in>
    \<langle>eucl_rel\<rangle>appr_plane_rel \<rightarrow> \<langle>\<langle>eucl_rel\<rangle>coll_rel(\<langle>eucl_rel\<rangle>plane_rel (set_of_irect (irect_mod optns)))\<rangle>nres_rel"
proof (safe intro!: nres_relI)
  fix a sctn X
  assume aX: "((a, sctn), X) \<in> \<langle>eucl_rel\<rangle>appr_plane_rel"
  then have "((a, sctn), (set_of_appr a , sctn)) \<in> \<langle>eucl_rel\<rangle>appr_rel \<times>\<^sub>r Id"
    by (auto simp: plane_rel_def br_def appr_rel_def)
  from irects_of_set_encl_impl.refine[OF this]
  have "nres_of (irects_of_set_encl_impl (a, sctn)) \<le> \<Down> (\<langle>\<langle>\<langle>int_rel\<rangle>list_rel \<times>\<^sub>r Id\<rangle>list_wset_rel\<rangle>option_rel) (irects_of_set_encl (set_of_appr a, sctn))"
    by (auto dest!: nres_relD)
  also
  have "\<dots> \<le> \<Down> (\<langle>\<langle>\<langle>int_rel\<rangle>list_rel \<times>\<^sub>r Id\<rangle>list_wset_rel\<rangle>option_rel) (SPEC (\<lambda>s. \<exists>R. s = Some R \<and>
           set_of_appr a \<inter> plane_of sctn \<subseteq> (\<Union>(r, sctn)\<in>R. set_of_irect (irect_mod optns) r \<inter> plane_of sctn) \<and>
           (\<Union>(r, sctn)\<in>R. set_of_irect (irect_mod optns) r)
           \<subseteq> Collect safe))"
    using _ irects_of_set_encl_spec[of "(set_of_appr a, sctn)"]
    by (rule conc_trans_additional) auto
  also have "\<dots> \<le> \<Down> (\<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>plane_rel (set_of_irect (irect_mod optns)))) (irects_of_appr_plane X)"
  proof -
    have a: "X = set_of_appr a \<inter> plane_of sctn" "set_of_appr a \<subseteq> Collect safe"
      using aX
      by (auto simp: plane_rel_def br_def)
    let ?a = "\<lambda>aa. (\<Union>x\<in>set aa. case x of (r, sctn) \<Rightarrow> set_of_irect (int (irect_mod optns)) r \<inter> plane_of sctn)"
    have "Some aa \<in> (default_rel (Collect safe)
      (({(c, a). a = set c} O
      \<langle>{(c, a). a = (case c of (x, s) \<Rightarrow> set_of_irect (int (irect_mod optns)) x \<inter> plane_of s) \<and>
      (case c of (x, s) \<Rightarrow> set_of_irect (int (irect_mod optns)) x \<subseteq> Collect safe)}\<rangle>set_rel) O
      {(x, y). \<Union>x = y \<and> y \<subseteq> Collect safe}))\<inverse> ``
      {r. set_of_appr a \<inter> plane_of sctn \<subseteq> r \<and> r \<subseteq> Collect safe}"
      if subset: "set_of_appr a \<inter> plane_of sctn \<subseteq> (\<Union>x\<in>set aa. case x of (r, sctn) \<Rightarrow> set_of_irect (int (irect_mod optns)) r \<inter> plane_of sctn)"
        (is "_ \<subseteq> ?s1")
      and safe: "(\<Union>x\<in>set aa. case x of (r, sctn) \<Rightarrow> set_of_irect (int (irect_mod optns)) r) \<subseteq> Collect safe"
        (is "?s2 \<subseteq> _")
        for aa
      using that
      by (intro ImageI[where a="?s1"])
        (auto simp: set_rel_def Some_mem_default_rel
          intro!: relcompI[where b = "(\<lambda>(i, s). set_of_irect (irect_mod optns) i \<inter> plane_of s) ` set aa"]
          relcompI[where b="set aa"])
    then show ?thesis
      using aX
      by (auto simp: plane_rel_def br_def conc_fun_def irects_of_appr_plane_def option_rel_def
          list_wset_rel_def coll_rel_def )
  qed
  finally show "nres_of (irects_of_set_encl_impl (a, sctn)) \<le>
      \<Down> (\<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>plane_rel (set_of_irect (irect_mod optns)))) (irects_of_appr_plane X)"
    .
qed

lemma irects_of_appr_plane_FOREACH_refine:
  "do {
    Xs \<leftarrow> (sets_of_coll X ::: \<langle>\<langle>\<langle>eucl_rel\<rangle>appr_plane_rel\<rangle>list_wset_rel\<rangle>nres_rel);
    FORWEAK Xs (RETURN {}) irects_of_appr_plane (\<lambda>a b. RETURN (a \<union> b))
  } \<le> irects_of_appr_plane X"
  unfolding irects_of_appr_plane_def autoref_tag_defs
  by (refine_vcg FORWEAK_mono_rule'[where I="\<lambda>S s. \<Union>S \<subseteq> s \<and> s \<subseteq> Collect safe"]) auto

schematic_goal irects_of_appr_plane_coll_ref[autoref_rules]:
  assumes [autoref_rules]: "(xs, X) \<in> \<langle>eucl_rel\<rangle>coll_rel(\<langle>eucl_rel\<rangle>appr_plane_rel)"
  shows "(nres_of ?f, irects_of_appr_plane $ X) \<in> \<langle>\<langle>eucl_rel\<rangle>coll_rel(\<langle>eucl_rel\<rangle>plane_rel (set_of_irect (irect_mod optns)))\<rangle>nres_rel"
  unfolding autoref_tag_defs
  using irects_of_appr_plane_FOREACH_refine
  apply (rule nres_rel_trans2)
  by (autoref_monadic)

definition poincare_irects::"'a set \<Rightarrow> 'a set \<Rightarrow> ('a set \<times> 'a set) nres"
  where "poincare_irects si CXS = do {
      CHECK (0 < stepsize optns \<and> 0 < rk2_param optns \<and> rk2_param optns \<le> 1);
      CHECK_ALLSAFE {si};
      ASSERT (DEFER_tag (0 < rk2_param optns)); (* TODO: what about \<open>DEFER\<close>? *)
      ASSERT (DEFER_tag (0 < stepsize optns));
      ASSERT (DEFER_tag (rk2_param optns \<le> 1));
      ASSERT (si \<subseteq> Collect safe);
      (XS, CS) \<leftarrow> poincare_distance_d si CXS;
      let _ = trace_set (''next sections_collectioned'') None;
      IS \<leftarrow> irects_of_appr_plane XS;
      RETURN (IS, CS)
    }"
sublocale autoref_op_pat_def poincare_irects .

schematic_goal poincare_irects_impl:
  assumes [autoref_rules]: "(ISi, IS) \<in> \<langle>eucl_rel\<rangle> coll_rel (\<langle>eucl_rel\<rangle>appr_rel)"
  assumes [autoref_rules]: "(CXSi, CXS) \<in> \<langle>eucl_rel\<rangle> coll_rel (\<langle>eucl_rel\<rangle>appr_rel)"
  shows "(nres_of (?f::?'c dres), poincare_irects $ IS $ CXS)\<in>?R"
  unfolding poincare_irects_def autoref_tag_defs
  by (autoref_monadic)

concrete_definition poincare_irects_impl for ISi CXSi uses poincare_irects_impl
lemmas [autoref_rules] = poincare_irects_impl.refine

lemma poincare_irects_spec[THEN order_trans, refine_vcg]:
  assumes "IS \<subseteq> Collect (le_halfspace (start_section optns))" "CXS \<subseteq> Collect safe"
  shows "poincare_irects IS CXS \<le> SPEC (\<lambda>(stops, CX). flowsto (IS \<inter> below_halfspace (start_section optns)) CX stops)"
  using assms
  unfolding poincare_irects_def
  apply (refine_vcg)
  subgoal by (rule flowsto_subset) (auto dest: flowsto_safeD)
  done

definition "set_of_coll soi XSi = (case XSi of None \<Rightarrow> Collect safe | Some xs \<Rightarrow> \<Union>(soi ` set xs))"

lemma mem_coll_rel_iff: "((optn, y) \<in> \<langle>eucl_rel\<rangle>coll_rel S) =
  (case optn of
    None \<Rightarrow> y = Collect safe
  | Some x \<Rightarrow> (\<exists>ya. (x, ya) \<in> \<langle>S\<rangle>list_wset_rel \<and> \<Union>ya \<subseteq> Collect safe \<and> y = \<Union>ya))"
  by (auto simp: Some_mem_coll_rel_iff None_mem_coll_rel split: option.splits)

lemma coll_rel_appr_rel_br: "\<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel) =
  br (set_of_coll set_of_appr) (\<lambda>x. set_of_coll set_of_appr x \<subseteq> Collect safe)"
  by (auto simp: mem_coll_rel_iff set_of_coll_def default_rel_def list_wset_rel_def
    set_rel_def br_def appr_rel_def
    split: option.splits)+

definition "set_of_plane_coll soa XSi =
  (case XSi of None \<Rightarrow> Collect safe | Some xs \<Rightarrow> ((\<Union>(r, sctn)\<in>set xs. soa r \<inter> plane_of sctn)))"

lemma coll_rel_plane_rel_br:
  shows "\<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>plane_rel soa) =
    br (set_of_plane_coll soa) (\<lambda>x. case x of None \<Rightarrow> True | Some xs \<Rightarrow> \<Union>(soa ` fst ` (set xs)) \<subseteq> Collect safe)"
  by (fastforce simp: mem_coll_rel_iff  mem_plane_rel_list_wset_rel_iff
      set_of_plane_coll_def br_def
      split: option.splits)

lemma poincare_irects_impl_thm:
  assumes "poincare_irects_impl ISi CXSi = dRETURN R"
  assumes "set_of_coll set_of_appr ISi \<subseteq> Collect (le_halfspace (start_section optns))"
  assumes "set_of_coll set_of_appr ISi \<subseteq> Collect safe"
  assumes safe: "set_of_coll set_of_appr CXSi \<subseteq> Collect safe"
  shows "flowsto (set_of_coll set_of_appr ISi) (set_of_coll set_of_appr (snd R)) (set_of_plane_coll (set_of_irect (irect_mod optns)) (fst R))"
proof -
  have "(ISi, set_of_coll set_of_appr ISi) \<in>  \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel)"
    using assms
    by (auto simp: set_of_coll_def coll_rel_def default_rel_def list_wset_rel_def
      set_rel_def br_def appr_rel_def
      split: option.splits)
  moreover have "(CXSi, set_of_coll set_of_appr CXSi) \<in> \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel)"
    using safe
    by (auto simp: set_of_coll_def coll_rel_def default_rel_def list_wset_rel_def
      set_rel_def br_def appr_rel_def
      split: option.splits)
  ultimately have 1:
    "(nres_of (poincare_irects_impl ISi CXSi), poincare_irects $ set_of_coll set_of_appr ISi $ set_of_coll set_of_appr CXSi)
      \<in> \<langle>\<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>plane_rel (set_of_irect(irect_mod optns))) \<times>\<^sub>r \<langle>eucl_rel\<rangle>coll_rel (\<langle>eucl_rel\<rangle>appr_rel)\<rangle>nres_rel"
    by (rule poincare_irects_impl.refine)

  have 2: "poincare_irects $ set_of_coll set_of_appr ISi $ set_of_coll set_of_appr CXSi \<le>
    SPEC (\<lambda>(stops, CX). flowsto (set_of_coll set_of_appr ISi \<inter> below_halfspace (start_section optns)) CX stops)"
    using assms
    by (auto intro!: poincare_irects_spec)
  from nres_rel_trans2[OF 2 1] assms
  show ?thesis
    by (auto simp: coll_rel_plane_rel_br coll_rel_appr_rel_br nres_rel_def conc_fun_def
      br_def inf_absorb1
      elim!: prod_relE)
qed

definition "one_step_until_time X0 CX t1 =
  do {
    CHECK (0 \<le> t1 \<and> 0 < rk2_param optns \<and> rk2_param optns \<le> 1);
    CHECK_ALLSAFE {X0};
    CHECK_ALLSAFE {CX};
    ASSERT (X0 \<subseteq> Collect safe);
    ASSERT (CX \<subseteq> Collect safe);
    (t, _, X, CX) \<leftarrow> WHILE (\<lambda>(t, _, _, _). t < t1) (\<lambda>(t, _, X, CXs). do {
      (h, _, CX, X) \<leftarrow> choose_step X (min (stepsize optns) (t1 - t));
      let _ = trace_set (''interpolated step:'') (Some CX);
      let _ = print_set True CX;
      let _ = trace_set (''step:'') (Some X);
      let _ = print_set False X;
      ASSERT (CX \<subseteq> Collect safe);
      RETURN (t + h, h, X, mk_coll CX \<union> CXs)
    }) (0, 0, X0, mk_coll X0 \<union> CX);
    RETURN (X, CX)
  }"
sublocale autoref_op_pat_def one_step_until_time .

schematic_goal one_step_until_time_impl:
  assumes [autoref_rules]: "(X0i, X0) \<in> \<langle>eucl_rel\<rangle>appr_rel"
  assumes [autoref_rules]: "(CXi, CX) \<in> \<langle>eucl_rel\<rangle> coll_rel (\<langle>eucl_rel\<rangle>appr_rel)"
  assumes [autoref_rules]: "(t1i, t1) \<in> Id"
  notes [autoref_tyrel] = ty_REL[where 'a="real" and R="Id"]
  shows "(nres_of (?f::?'c dres), one_step_until_time $ X0 $ CX $ t1)\<in>?R"
  unfolding one_step_until_time_def[abs_def]
  by (autoref_monadic)
concrete_definition one_step_until_time_impl for X0i CXi t1i uses one_step_until_time_impl
lemmas [autoref_rules] = one_step_until_time_impl.refine

lemma one_step_until_time_spec[THEN order_trans, refine_vcg]:
  "one_step_until_time X0 CX t1 \<le> SPEC (\<lambda>(R, CX). \<forall>x0 \<in> X0. t1 \<in> existence_ivl0 x0 \<and>
    flow0 x0 t1 \<in> R \<and> R \<subseteq> Collect safe \<and>
    (\<forall>t \<in> {0 .. t1}. flow0 x0 t \<in> CX) \<and>
    CX \<subseteq> Collect safe)"
  unfolding one_step_until_time_def autoref_tag_defs
  apply (refine_vcg WHILE_rule[where I="\<lambda>(t, h, X, CX). X \<subseteq> Collect safe \<and> CX \<subseteq> Collect safe \<and> 0 \<le> h \<and> t \<le> t1 \<and>
        (\<forall>x0 \<in> X0. t - h \<in> existence_ivl0 x0 \<and> t \<in> existence_ivl0 x0 \<and> flow0 x0 t \<in> X \<and> (\<forall>t \<in> {0 .. t}. flow0 x0 t \<in> CX))"])
  subgoal by auto
  subgoal by (auto simp: flowpipe_def existence_ivl_trans flow_trans)
  subgoal by (auto simp: flowpipe_def existence_ivl_trans flow_trans)
  subgoal by (auto simp: flowpipe_def)
  subgoal by (auto simp: flowpipe_def)
  subgoal by (auto simp: flowpipe_def)
  apply clarsimp subgoal for a b c d e f g h
    apply (safe)
    subgoal by (auto simp: flowpipe_def existence_ivl_trans flow_trans)
    subgoal by (auto simp: flowpipe_def existence_ivl_trans flow_trans)
    subgoal premises prems for t
    proof -
      have mem_c: "flow0 h a \<in> c"
        by (simp add: prems)
      have "flow0 h t = flow0 (flow0 h a) (t - a)"
        apply (subst flow_trans[symmetric])
        subgoal using prems by auto
        subgoal
        proof -
          from prems
          have "f \<in> existence_ivl0 (flow0 h a)"
            by (auto simp: flowpipe_def)
          then show "t - a \<in> existence_ivl0 (flow0 h a)"
            apply (rule in_existence_between_zeroI)
            using prems
            by (force simp: closed_segment_real)
        qed
        subgoal using prems by auto
        done
      also
      have "\<dots> \<in> e"
        using mem_c \<open>flowpipe c f f e g\<close> prems
        by (fastforce simp: flowpipe_def)
      finally show ?thesis .
    qed
    done
  done

definition [simp]: "Collect_safe = Collect safe"
sublocale autoref_op_pat_def Collect_safe .
lemma [autoref_op_pat_def]: "Collect safe \<equiv> OP Collect_safe"
  by simp

definition "one_step_until_time_ivl X history t = do {
    (r, CX) \<leftarrow> one_step_until_time X (if history then {} else Collect_safe) t;
    (l, u) \<leftarrow> ivl_of_set r;
    ASSERT (l \<le> u);
    CHECK_ALLSAFE {{l .. u}};
    RETURN ((l, u), CX)
  }"
sublocale autoref_op_pat_def one_step_until_time_ivl .

lemma safe_set_autoref[autoref_rules]:
  "(None, Collect_safe) \<in> \<langle>eucl_rel\<rangle> coll_rel (\<langle>eucl_rel\<rangle> appr_rel)"
  by (auto simp: coll_rel_def default_rel_def)

schematic_goal one_step_until_time_ivl_impl:
  assumes [autoref_rules]: "(X0i, X0) \<in> \<langle>eucl_rel\<rangle>appr_rel"
  assumes [autoref_rules]: "(histi, hist) \<in> bool_rel"
  assumes [autoref_rules]: "(t1i, t1) \<in> Id"
  notes [autoref_tyrel] = ty_REL[where 'a="'a set" and R="\<langle>eucl_rel\<rangle>appr_rel"]
  notes [autoref_tyrel] = ty_REL[where 'a="real" and R="Id"]
  shows "(nres_of (?f::?'c dres), one_step_until_time_ivl $ X0 $ hist $ t1)\<in>?R"
  unfolding autoref_tag_defs
  unfolding one_step_until_time_ivl_def[abs_def]
  by (autoref_monadic)
concrete_definition one_step_until_time_ivl_impl for X0i histi t1i uses one_step_until_time_ivl_impl
lemmas [autoref_rules] = one_step_until_time_ivl_impl.refine

lemma one_step_until_time_ivl_spec:
  "one_step_until_time_ivl X0 CX t1 \<le> SPEC (\<lambda>((l, u), CX).
    \<forall>x0 \<in> X0. t1 \<in> existence_ivl0 x0 \<and> flow0 x0 t1 \<in> {l .. u} \<and> {l .. u} \<subseteq> Collect safe \<and> (\<forall>t \<in> {0 .. t1}. flow0 x0 t \<in> CX) \<and> CX \<subseteq> Collect safe)"
  unfolding one_step_until_time_ivl_def
  by refine_vcg auto

lemma coll_rel_br: "\<langle>eucl_rel\<rangle> coll_rel (\<langle>eucl_rel\<rangle>appr_rel) = br (\<lambda>x. case x of None \<Rightarrow> Collect safe | Some x \<Rightarrow> \<Union>(set_of_appr ` set x))
  (\<lambda>x. case x of None \<Rightarrow> True | Some x \<Rightarrow> \<Union>(set_of_appr ` set x) \<subseteq> Collect safe)"
  by (fastforce simp: coll_rel_def br_def default_rel_def list_wset_rel_def set_rel_def appr_rel_def
    relcomp_unfold
    split: option.splits)

lemma one_step_until_time_ivl_res:
  assumes "one_step_until_time_ivl_impl X0i hist ti = dRETURN R"
  assumes "x0 \<in> set_of_appr X0i"
  assumes "ti = t"
  assumes "{fst (fst R) .. snd (fst R)} \<subseteq> S"
  shows "t \<in> existence_ivl0 x0 \<and> flow0 x0 t \<in> S"
  using
    assms
    conc_trans[OF
      nres_relD[OF one_step_until_time_ivl_impl.refine[of X0i "set_of_appr X0i" hist hist t t, unfolded autoref_tag_defs]]
      Id_SPEC_refine[OF one_step_until_time_ivl_spec[of "set_of_appr X0i" _ t]]]
  by (cases R) (auto simp: appr_rel_def br_def RETURN_refine_iff elim!: RETURN_ref_SPECD)

lemma one_step_until_time_ivl_reachable_res:
  assumes "one_step_until_time_ivl_impl X0i hist ti = dRETURN (lu, Some reachable)"
  assumes "x0 \<in> set_of_appr X0i"
  assumes "ti = t"
  assumes "{fst lu .. snd lu} \<subseteq> S"
  shows "t \<in> existence_ivl0 x0 \<and> flow0 x0 t \<in> S \<and> (\<forall>s \<in> {0 .. t}. flow0 x0 s \<in> \<Union>(set_of_appr ` set reachable))"
  using
    assms
    conc_trans[OF
      nres_relD[OF one_step_until_time_ivl_impl.refine[of X0i "set_of_appr X0i" hist hist t t, unfolded autoref_tag_defs]]
      Id_SPEC_refine[OF one_step_until_time_ivl_spec[of "set_of_appr X0i" hist t]]]
  unfolding coll_rel_br
  by (auto simp: appr_rel_def br_def RETURN_refine_iff  elim!: RETURN_ref_SPECD)

end

end