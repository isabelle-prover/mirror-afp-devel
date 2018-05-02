theory Refine_Reachability_Analysis
imports
  Affine_Arithmetic.Print
  "HOL-ODE-Refinement.Weak_Set"
  "HOL-ODE-Refinement.Refine_String"
  "HOL-ODE-Refinement.Refine_Folds"
  Ordinary_Differential_Equations.Flow
  Refine_Rigorous_Numerics
  "HOL-Decision_Procs.Approximation"
begin

context auto_ll_on_open begin

lemma nonneg_interval_mem_existence_ivlI[intro]:\<comment> \<open>TODO: move!\<close>
  "0 \<le> t1 \<Longrightarrow> t1 \<le> t2 \<Longrightarrow> t2 \<in> existence_ivl0 x0 \<Longrightarrow> {t1..t2} \<subseteq> existence_ivl0 x0"
  "t1 \<le> t2 \<Longrightarrow> t2 \<le> 0 \<Longrightarrow> t1 \<in> existence_ivl0 x0 \<Longrightarrow> {t1..t2} \<subseteq> existence_ivl0 x0"
  "t1 \<le> 0 \<Longrightarrow> 0 \<le> t2 \<Longrightarrow> t1 \<in> existence_ivl0 x0 \<Longrightarrow> t2 \<in> existence_ivl0 x0 \<Longrightarrow> {t1..t2} \<subseteq> existence_ivl0 x0"
    apply auto
  apply (drule ivl_subset_existence_ivl) apply auto
  apply (drule ivl_subset_existence_ivl') apply auto
  apply (drule segment_subset_existence_ivl, assumption)
  apply (auto simp: closed_segment_eq_real_ivl)
  done

lemma interval_subset_existence_ivl:
  "t \<in> existence_ivl0 x0 \<Longrightarrow> s \<in> existence_ivl0 x0 \<Longrightarrow> t \<le> s \<Longrightarrow> {t .. s} \<subseteq> existence_ivl0 x0"
  using segment_subset_existence_ivl[of s x0 t]
  by (auto simp: closed_segment_eq_real_ivl)

end

lemma(in c1_on_open_euclidean) diff_existence_ivl_iff[simp]:\<comment> \<open>TODO: move!, also to @{term auto_ll_on_open}\<close>
  "t2 - t1 \<in> existence_ivl0 (flow0 x0 t1) \<longleftrightarrow> t2 \<in> existence_ivl0 x0"
  if "t1 \<le> t2" "t1 \<in> existence_ivl0 x0"
  apply auto
   apply (drule existence_ivl_trans[OF that(2)])
   apply (auto intro!: diff_existence_ivl_trans that)
  done

definition "scaleR2 l u X = (\<lambda>(r, (x, y)). (x, r *\<^sub>R y)) ` (ereal -` {l .. u} \<times> X)"

lemma scaleR2_1_1[simp]: "scaleR2 1 1 = (\<lambda>x::(_\<times>'x::real_vector)set. x)"
  by (force simp: scaleR2_def[abs_def] image_def vimage_def)

lemma (in auto_ll_on_open) flow_trans':
  "flow0 (flow0 x0 t1) t2 = flow0 x0 (t1 + t2)"
  if "t1 \<in> existence_ivl0 x0" "t1 + t2 \<in> existence_ivl0 x0"
  apply (subst flow_trans)
  using that
  by (auto intro!: existence_ivl_trans')

context begin interpretation autoref_syn .
definition [simp]: "ST (x::char list) = x"
lemma [autoref_op_pat_def]: "ST xs \<equiv> OP (ST xs)" by simp
lemma [autoref_rules]: "(x, ST x) \<in> string_rel"
  by (auto simp: string_rel_def)
end


context auto_ll_on_open begin

definition "flowpipe0 X0 hl hu CX X1 \<longleftrightarrow> 0 \<le> hl \<and> hl \<le> hu \<and> X0 \<subseteq> X \<and> CX \<subseteq> X \<and> X1 \<subseteq> X \<and>
  (\<forall>(x0) \<in> X0. \<forall>h \<in> {hl .. hu}. h \<in> existence_ivl0 x0 \<and> (flow0 x0 h) \<in> X1 \<and> (\<forall>h' \<in> {0 .. h}. (flow0 x0 h') \<in> CX))"

lemma flowpipe0D:
  assumes "flowpipe0 X0 hl hu CX X1"
  shows flowpipe0_safeD: "X0 \<union> CX \<union> X1 \<subseteq> X"
    and flowpipe0_nonneg: "0 \<le> hl" "hl \<le> hu"
    and flowpipe0_exivl: "hl \<le> h \<Longrightarrow> h \<le> hu \<Longrightarrow> (x0) \<in> X0 \<Longrightarrow> h \<in> existence_ivl0 x0"
    and flowpipe0_discrete: "hl \<le> h \<Longrightarrow> h \<le> hu \<Longrightarrow> (x0) \<in> X0 \<Longrightarrow> (flow0 x0 h) \<in> X1"
    and flowpipe0_cont: "hl \<le> h \<Longrightarrow> h \<le> hu \<Longrightarrow> (x0) \<in> X0 \<Longrightarrow> 0 \<le> h' \<Longrightarrow> h' \<le> h \<Longrightarrow> (flow0 x0 h') \<in> CX"
  using assms
  by (auto simp: flowpipe0_def)

lemma flowpipe0_source_subset: "flowpipe0 X0 hl hu CX X1 \<Longrightarrow> X0 \<subseteq> CX"
  apply (auto dest: bspec[where x=hl] bspec[where x=0] simp: flowpipe0_def)
  apply (drule bspec)
   apply (assumption)
  apply (drule bspec[where x=hl])
   apply auto
  apply (drule bspec[where x=0])
  by (auto simp: flow_initial_time_if)

end

text \<open>Approximation\<close>

record 'b numeric_options =
  precision :: nat
  reduce :: "'b list \<Rightarrow> nat \<Rightarrow> real list \<Rightarrow> bool" \<comment> \<open>is this too special?\<close>
  adaptive_atol :: real
  adaptive_rtol :: real
  method_id :: nat
  start_stepsize :: real
  iterations :: nat
  halve_stepsizes :: nat
  widening_mod :: nat
  rk2_param :: real
  printing_fun :: "bool \<Rightarrow> 'b list \<Rightarrow> unit"
  tracing_fun :: "string \<Rightarrow> 'b list option \<Rightarrow> unit"

record 'b reach_options =
  max_tdev_thres :: "'b list \<Rightarrow> real"
  pre_split_reduce :: "'b list \<Rightarrow> nat \<Rightarrow> real list \<Rightarrow> bool" \<comment> \<open>is this too special?\<close>

  pre_inter_granularity :: "'b list \<Rightarrow> real"
  post_inter_granularity :: "'b list \<Rightarrow> real"
  pre_collect_granularity :: real
  max_intersection_step :: real

abbreviation "num_optns_rel \<equiv> (Id::'b numeric_options rel)"
abbreviation "reach_optns_rel \<equiv> (Id::'b reach_options rel)"

context begin interpretation autoref_syn .
lemma [autoref_rules]:
  "(precision, precision)\<in>num_optns_rel \<rightarrow> nat_rel"
  "(reduce, reduce)\<in>num_optns_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> rl_rel \<rightarrow> bool_rel"
  "(start_stepsize, start_stepsize)\<in>num_optns_rel \<rightarrow> rnv_rel"
  "(iterations, iterations)\<in> num_optns_rel\<rightarrow> nat_rel"
  "(halve_stepsizes, halve_stepsizes)\<in> (num_optns_rel) \<rightarrow> nat_rel"
  "(widening_mod, widening_mod)\<in> (num_optns_rel) \<rightarrow>nat_rel"
  "(rk2_param, rk2_param)\<in> (num_optns_rel) \<rightarrow> rnv_rel"
  "(method_id, method_id)\<in> (num_optns_rel) \<rightarrow> nat_rel"
  "(adaptive_atol, adaptive_atol)\<in> (num_optns_rel) \<rightarrow> rnv_rel"
  "(adaptive_rtol, adaptive_rtol)\<in> (num_optns_rel) \<rightarrow> rnv_rel"
  "(printing_fun, printing_fun)\<in> (num_optns_rel) \<rightarrow> bool_rel \<rightarrow> I \<rightarrow> unit_rel"
  "(tracing_fun, tracing_fun)\<in> (num_optns_rel) \<rightarrow> string_rel \<rightarrow> \<langle>I\<rangle>option_rel \<rightarrow> unit_rel"
  by auto

lemma [autoref_rules]:
  "(pre_split_reduce, pre_split_reduce)\<in> (reach_optns_rel) \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> rl_rel \<rightarrow> bool_rel"
  "(max_intersection_step, max_intersection_step)\<in> (reach_optns_rel) \<rightarrow> rnv_rel"
  by auto

end


lemma list_of_eucl_of_env:
  assumes [simp]: "length xs = DIM('a)"
  shows "(list_of_eucl (eucl_of_env xs vs::'a)) = (map (\<lambda>i. vs ! (xs ! i)) [0..<DIM('a::executable_euclidean_space)])"
  by (auto intro!: nth_equalityI simp: eucl_of_env_def eucl_of_list_inner)

consts i_halfspace :: "interface \<Rightarrow> interface"
consts i_phantom :: "interface \<Rightarrow> interface"

context begin
interpretation autoref_syn .


definition halfspace_rel_internal: "halfspaces_rel R = \<langle>\<langle>R\<rangle>sctn_rel\<rangle>list_set_rel O br below_halfspaces top"
lemma halfspaces_rel_def: "\<langle>R\<rangle>halfspaces_rel = \<langle>\<langle>R\<rangle>sctn_rel\<rangle>list_set_rel O br below_halfspaces top"
  by (auto simp: relAPP_def halfspace_rel_internal)

lemmas [autoref_rel_intf] = REL_INTFI[of halfspaces_rel i_halfspace]

lemma below_halfspace_autoref[autoref_rules]:
  "(\<lambda>x. x, below_halfspaces) \<in> \<langle>\<langle>R\<rangle>sctn_rel\<rangle>list_set_rel \<rightarrow> \<langle>R\<rangle>halfspaces_rel"
  by (auto simp: halfspaces_rel_def br_def)

definition pphantom_rel_internal:
  "phantom_rel A = {(Some x, y)|x y. (x, y) \<in> A} \<union> {(None, y)|x y. (x, y) \<in> A}"
lemma phantom_rel_def: "\<langle>A\<rangle>phantom_rel = {(Some x, y)|x y. (x, y) \<in> A} \<union> {(None, y)|x y. (x, y) \<in> A}"
  by (auto simp: relAPP_def pphantom_rel_internal)
lemmas [autoref_rel_intf] = REL_INTFI[of phantom_rel i_phantom]

definition [simp]: "mk_phantom x = x"

lemma phantom_rel_const[autoref_rules(overloaded)]:
  shows "(Some, mk_phantom) \<in> A \<rightarrow> \<langle>A\<rangle>phantom_rel"
  by (auto simp: phantom_rel_def)

definition [simp]: "op_union_phantom = (\<union>)"
lemma [autoref_op_pat]: "(\<union>) \<equiv> OP op_union_phantom"
  by simp
lemma phantom_rel_union[autoref_rules]:
  assumes [THEN GEN_OP_D, autoref_rules(overloaded)]: "GEN_OP un (\<union>) (A \<rightarrow> A \<rightarrow> A)"
  shows "(\<lambda>a b. do {a \<leftarrow> a; b \<leftarrow> b; Some (un a b)}, op_union_phantom) \<in> \<langle>A\<rangle>phantom_rel \<rightarrow> \<langle>A\<rangle>phantom_rel \<rightarrow> \<langle>A\<rangle>phantom_rel"
  using assms
  by (fastforce simp: phantom_rel_def dest: fun_relD)

definition [simp]: "op_empty_phantom b = {}"

lemma phantom_rel_empty_coll[autoref_rules]:
  shows "(\<lambda>b. (if b then None else Some []), op_empty_phantom) \<in> bool_rel \<rightarrow> \<langle>clw_rel A\<rangle>phantom_rel"
  apply (auto simp: phantom_rel_def br_def lw_rel_def Union_rel_def)
    apply (rule relcompI)
     apply force
    apply (rule relcompI)
     defer
  by (force dest!: spec[where x="[]"])+


lemma mem_phantom_rel_Some[simp]:
  "(Some x, y) \<in> \<langle>A\<rangle>phantom_rel \<longleftrightarrow> (x, y) \<in> A"
  by (auto simp: phantom_rel_def)

lemma RETURN_None_ph_relI: "(RETURN y, x) \<in> \<langle>B\<rangle>nres_rel \<Longrightarrow> (RETURN None, x) \<in> \<langle>\<langle>B\<rangle>phantom_rel\<rangle>nres_rel"
  by (auto simp: phantom_rel_def nres_rel_def pw_le_iff refine_pw_simps)
lemma RETURN_Some_ph_relI: "(RETURN y, x) \<in> \<langle>B\<rangle>nres_rel \<Longrightarrow> (RETURN (Some y), x) \<in> \<langle>\<langle>B\<rangle>phantom_rel\<rangle>nres_rel"
  by (auto simp: phantom_rel_def nres_rel_def pw_le_iff refine_pw_simps)

lemma None_ph_relI: "(x, X) \<in> B \<Longrightarrow> (None, X) \<in> \<langle>B\<rangle>phantom_rel"
  by (auto simp: phantom_rel_def)

definition "phantom_rel_unop fid x = (case x of None \<Rightarrow> None | Some x \<Rightarrow> (Some (fid x)))"
lemma phantom_rel_unop:
  assumes f[THEN GEN_OP_D]: "GEN_OP fi f (A \<rightarrow> \<langle>B\<rangle>nres_rel)"
  assumes fi[unfolded autoref_tag_defs]: "\<And>x. TRANSFER (RETURN (fid x) \<le> fi x)"
  shows "(\<lambda>x. RETURN (phantom_rel_unop fid x), f) \<in> \<langle>A\<rangle>phantom_rel \<rightarrow> \<langle>\<langle>B\<rangle>phantom_rel\<rangle>nres_rel"
proof (rule fun_relI)
  fix x a assume x: "(x, a) \<in> \<langle>A\<rangle>phantom_rel"
  with assms obtain b where "(b, a) \<in> A" by (auto simp: phantom_rel_def)
  show "(RETURN (phantom_rel_unop fid x), f a) \<in> \<langle>\<langle>B\<rangle>phantom_rel\<rangle>nres_rel"
    using x
    by (auto split: option.splits intro!: x \<open>(b, a) \<in> A\<close> f[param_fo]
        RETURN_Some_ph_relI RETURN_None_ph_relI nres_rel_trans1[OF fi]
        simp: phantom_rel_unop_def)
qed

end

locale approximate_sets_options = approximate_sets
  where appr_rell = appr_rell
    and optns = optns
    for appr_rell :: "('b list \<times> real list set) set"
    and optns::"'b numeric_options"
    and ode_e::"floatarith list"
    and safe_form::"form"
begin

definition print_set::"bool \<Rightarrow> 'a set \<Rightarrow> unit" where "print_set _ _ = ()"
sublocale autoref_op_pat_def print_set .
lemma print_set_impl[autoref_rules]:
  shows "(printing_fun optns, print_set) \<in> bool_rel \<rightarrow> A \<rightarrow> Id"
  by auto

definition trace_set::"string\<Rightarrow>'a set option\<Rightarrow>unit" where "trace_set _ _ = ()"
sublocale autoref_op_pat_def trace_set .

lemma trace_set_impl[autoref_rules]:
  shows "(tracing_fun optns, trace_set) \<in> string_rel \<rightarrow> \<langle>A\<rangle>option_rel \<rightarrow> Id"
  by auto

abbreviation "CHECKs \<equiv> \<lambda>s. CHECK (\<lambda>_. tracing_fun optns s None)"

definition ode::"'a \<Rightarrow> 'a::executable_euclidean_space"
  where "ode x = eucl_of_list (interpret_floatariths ode_e (list_of_eucl x))"

definition "ode_d_expr_nth N n i =
    FDERIV_floatarith
     (FDERIV_n_floatarith (ode_e  ! i) [0..<N] (map floatarith.Var [N..<2 * N]) n) [0..<N]
         (map floatarith.Var [2 * N..<3 * N])"

definition "ode_d_expr N n =
    (FDERIV_floatariths
      (FDERIV_n_floatariths ode_e [0..<N] (map floatarith.Var [N..<2 * N]) n)
      [0..<N]
      (map floatarith.Var [2 * N..< 3 * N]))"

lemma ode_d_expr_nth: "i < length ode_e \<Longrightarrow> ode_d_expr_nth N n i = ode_d_expr N n ! i "
  by (auto simp: ode_d_expr_nth_def ode_d_expr_def
      FDERIV_n_floatariths_nth)

definition ode_d_raw::"nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a::executable_euclidean_space"
  where "ode_d_raw n x dn d =
    eucl_of_list (interpret_floatariths (ode_d_expr DIM('a) n) (list_of_eucl x @ list_of_eucl dn @ list_of_eucl d))"

definition "ode_fa_nth xs i = subst_floatarith (\<lambda>i. xs ! i) (ode_e ! i)"

definition "ode_fa xs = map (subst_floatarith (\<lambda>i. xs ! i)) ode_e"

lemma length_ode_d_expr[simp]: "length (ode_d_expr f n) = length ode_e"
  by (induction n) (auto simp: ode_d_expr_def FDERIV_n_floatariths_def)

lemma ode_fa_nth: "i < length ode_e \<Longrightarrow> ode_fa xs ! i = ode_fa_nth xs i"
  by (auto simp: ode_fa_nth_def ode_fa_def)

definition "ode_d_fa_nth n xs ds i = subst_floatarith (\<lambda>i. (xs@ds@ds) ! i) (ode_d_expr_nth (length xs) n i)"

definition "ode_d_fa n xs ds = map (subst_floatarith (\<lambda>i. (xs@ds@ds) ! i)) (ode_d_expr (length xs) n)"

lemma ode_d_fa_nth: "i < length ode_e \<Longrightarrow> ode_d_fa_nth n xs ds i = ode_d_fa n xs ds ! i"
  by (auto simp: ode_d_fa_def ode_d_fa_nth_def ode_d_expr_nth)

lemma length_ode_d_fa[simp]: "length (ode_d_fa n xs ds) = length ode_e"
  by (auto simp: ode_d_fa_def FDERIV_n_floatariths_def)

definition safe::"'a::executable_euclidean_space \<Rightarrow> bool"
  where "safe x \<longleftrightarrow>
    length ode_e = DIM('a) \<and>
    max_Var_floatariths ode_e \<le> DIM('a) \<and>
    open_form safe_form \<and>
    max_Var_form safe_form \<le> DIM('a) \<and>
    interpret_form safe_form (list_of_eucl x) \<and>
    isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl x)"

definition "Csafe = Collect safe"

definition "euler_incr_fas_nth X0 h CX i = X0 ! i + h * (ode_fa_nth CX i)"

definition "euler_incr_fas X0 h CX = map (euler_incr_fas_nth X0 h CX) [0..<length X0]"

definition "euler_err_fas_nth X0 h CX i = ((h ^\<^sub>e 2) / floatarith.Num 2) * ode_d_fa_nth 0 CX (ode_fa CX) i"

definition "euler_err_fas X0 h CX = map (euler_err_fas_nth X0 h CX) [0..<length X0]"

definition "euler_fas X0 h CX =
  map (\<lambda>i. (euler_incr_fas_nth X0 h X0 i + euler_err_fas_nth X0 h CX i)) [0..<length X0] @
  euler_err_fas X0 h CX"

definition "rk2_fas_err_nth rkp x0 h cx s2 i =
  ((((h ^\<^sub>e 3 / 6) *
        (ode_d_fa_nth 1 cx (ode_fa cx) i +
         ode_d_fa_nth 0 cx (ode_d_fa 0 cx (ode_fa cx)) i)))
      - ((h ^\<^sub>e 3 * rkp / 4) *
          ode_d_fa_nth 1 (euler_incr_fas x0 (s2 * h * rkp) x0) (ode_fa x0) i))"

definition "rk2_fas_err rkp x0 h cx s2 = map (rk2_fas_err_nth rkp x0 h cx s2) [0..<length x0]"

lemma length_rk2_fas_err[simp]: "length (rk2_fas_err rkp x0 h cx s2) = length x0"
  by (simp add: rk2_fas_err_def)

lemma length_euler_incr_fas[simp]: "length (euler_incr_fas X0 h CX) = length X0"
  by (auto simp: euler_incr_fas_def)

lemma length_euler_err_fas[simp]: "length (euler_err_fas X0 h CX) = length X0"
  by (auto simp: euler_err_fas_def)

lemma length_euler_floatarith[simp]: "length (euler_fas X0 h CX) = 2 * length X0"
  by (auto simp: euler_fas_def)

definition "rk2_fas rkp x0 h cx s2 =
  (map (\<lambda>i.
      ((x0 ! i +
        h * ((1 - (1 / (rkp * 2))) * ode_fa_nth x0 i +
          (1 / (rkp * 2)) * ode_fa_nth (euler_incr_fas x0 (h * rkp) x0) i))
      + rk2_fas_err_nth rkp x0 h cx s2 i)) [0..<length x0]) @ rk2_fas_err rkp x0 h cx s2"

lemma length_rk2_fas[simp]: "length (rk2_fas rkp x0 h cx s2) = 2 * length x0"
  by (simp add: rk2_fas_def)

lemma open_safe: "open Csafe"
proof -
  have leq: "list_updates [0..<DIM('a)] (list_of_eucl x) (replicate DIM('a) 0) = list_of_eucl x" for x::'a
    by (auto intro!: nth_equalityI simp: list_updates_nth)
  have "(Csafe::'a set) =
    (if length ode_e = DIM('a) \<and> max_Var_floatariths ode_e \<le> DIM('a) \<and> max_Var_form safe_form \<le> DIM('a) \<and> open_form safe_form then
      {x. interpret_form safe_form (list_of_eucl x)} \<inter>
      {x. isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl x)}
    else {})"
    by (auto simp: Csafe_def safe_def)
  also have "open \<dots>"
    apply (auto intro!: open_Int)
    subgoal premises prems using open_form[OF prems(4), where 'a='a, of "[0..<DIM('a)]" "replicate (DIM('a)) 0"]
      by (auto simp: leq)
    subgoal
      apply (rule isFDERIV_open)
      apply (rule order_trans)
      apply assumption
      apply arith
      done
    done
  finally show ?thesis .
qed

lemma safeD:
  fixes x::"'a::executable_euclidean_space"
  assumes "x \<in> Csafe"
  shows "interpret_form safe_form (list_of_eucl x)"
    and safe_isFDERIV: "isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl x)"
  using assms
  by (auto simp: Csafe_def safe_def)

lemma
  fixes x::"'a::executable_euclidean_space"
  shows safe_max_Var: "x \<in> Csafe \<Longrightarrow> max_Var_floatariths ode_e \<le> DIM('a)"
    and safe_length: "x \<in> Csafe \<Longrightarrow> length ode_e = DIM('a)"
    and safe_max_Var_form: "x \<in> Csafe \<Longrightarrow> max_Var_form safe_form \<le> DIM('a)"
  by (auto simp: safe_def Csafe_def)

lemma safe_isFDERIV_append:
  fixes x::"'a::executable_euclidean_space"
  shows "x \<in> Csafe \<Longrightarrow> isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl x @ xs)"
  apply (rule isFDERIV_max_Var_congI)
   apply (rule safe_isFDERIV)
   apply assumption
  using safe_max_Var[of x]
  by (auto simp: nth_append)

lemma ode_d_raw_0:
  assumes "x \<in> Csafe"
  shows "(ode has_derivative ode_d_raw 0 x d) (at x)"
  using assms safe_max_Var[OF assms] safe_length[OF assms]
  unfolding ode_def ode_d_raw_def ode_d_expr_def
  apply (intro interpret_floatarith_FDERIV_floatariths[THEN has_derivative_eq_rhs])
     apply (auto simp: isFDERIV_def FDERIV_n_floatariths_def safe_max_Var nth_append
      max_Var_floatariths_Max Csafe_def safe_def
      intro!: arg_cong[where f=eucl_of_list] ext interpret_floatariths_FDERIV_floatariths_cong
        freshs_floatariths_max_Var_floatarithsI 
        max_Var_floatarith_le_max_Var_floatariths[le])
  apply (rule interpret_floatariths_max_Var_cong)
  apply (auto simp: max_Var_floatariths_Max Max_gr_iff nth_append
      dest!: less_le_trans[OF _ max_Var_floatarith_DERIV_floatarith])
   apply (drule max_Var_floatariths_lessI) apply simp
  apply (auto dest!: less_le_trans[OF _ safe_max_Var[OF assms]])
   apply (drule max_Var_floatariths_lessI) apply simp
  apply (auto dest!: less_le_trans[OF _ safe_max_Var[OF assms]])
  done

lemma not_fresh_odeD: "x \<in> Csafe \<Longrightarrow> \<not>fresh_floatariths ode_e i \<Longrightarrow> i < DIM('a)" for x::"'a::executable_euclidean_space"
  using fresh_floatariths_max_Var[of ode_e i] safe_max_Var[of x] by arith

lemma safe_isnFDERIV:
  fixes x::"'a::executable_euclidean_space"
  assumes "x \<in> Csafe"
  shows "isnFDERIV DIM('a) ode_e [0..<DIM('a)] [DIM('a)..<2 * DIM('a)] (list_of_eucl x @ ys) n"
  apply (rule isFDERIV_imp_isnFDERIV)
     apply (rule isFDERIV_max_Var_congI)
      apply (rule safe_isFDERIV[OF assms])
  using safe_max_Var[OF assms] safe_length[OF assms]
  by (auto simp: nth_append)

lemma safe_isnFDERIVI:
  assumes "(eucl_of_list xs::'a::executable_euclidean_space) \<in> Csafe"
  assumes [simp]: "length xs = DIM('a)" "length ds = DIM('a)"
  shows "isnFDERIV DIM('a) ode_e [0..<DIM('a)] [DIM('a)..<2 * DIM('a)] (xs@ds) n"
proof -
  have "isnFDERIV DIM('a) ode_e [0..<DIM('a)] [DIM('a)..<2 * DIM('a)] (list_of_eucl (eucl_of_list xs::'a)@ds) n"
    by (rule safe_isnFDERIV; fact)
  also
  have "list_of_eucl (eucl_of_list xs::'a) = xs"
    by (auto intro!: nth_equalityI)
  finally show ?thesis .
qed

lemma dest_Num_eq_Some_iff[simp]: "dest_Num_fa fa = (Some x) \<longleftrightarrow> fa = floatarith.Num x"
  by (cases fa) auto

lemma ode_d_raw_Suc:
  assumes "x \<in> Csafe"
  shows "((\<lambda>x. ode_d_raw n x d d) has_derivative ode_d_raw (Suc n) x d) (at x)"
proof -
  let ?shift = "\<lambda>x. Var (if 2 * DIM('a) \<le> x \<and> x < 3 * DIM('a) then x - DIM('a) else x)"
  have subst_ode_e[simp]: "map (subst_floatarith ?shift) ode_e = ode_e"
    apply (auto intro!: nth_equalityI)
    apply (rule subst_floatarith_Var_max_Var_floatarith)
    by (auto dest!: max_Var_floatariths_lessI
        less_le_trans[OF _ safe_max_Var[OF assms]])
  have map_shift[simp]:
    "(map ?shift [DIM('a)..<2 * DIM('a)]) = (map floatarith.Var [DIM('a)..<2 * DIM('a)])"
    "(map ?shift [2 * DIM('a)..<3 * DIM('a)]) =
        (map floatarith.Var [DIM('a)..<2 * DIM('a)])"
    by (auto intro!: nth_equalityI)

  show ?thesis
    unfolding ode_def ode_d_raw_def ode_d_expr_def
    apply (rule interpret_floatarith_FDERIV_floatariths_append[THEN has_derivative_eq_rhs])
    subgoal
    proof -
      let ?shift = "\<lambda>x. if 2 * DIM('a) \<le> x \<and> x < 3 * DIM('a) then x - DIM('a) else x"
      have mv: "max_Var_floatariths
          (FDERIV_floatariths (FDERIV_n_floatariths ode_e [0..<DIM('a)] (map floatarith.Var [DIM('a)..<2 * DIM('a)]) n)
          [0..<DIM('a)] (map floatarith.Var [2 * DIM('a)..<3 * DIM('a)])) \<le> 3 * DIM('a)"
        and mv2: "max_Var_floatariths
              (FDERIV_floatariths (FDERIV_n_floatariths ode_e [0..<DIM('a)] (map floatarith.Var [DIM('a)..<2 * DIM('a)]) n)
                [0..<DIM('a)] (map floatarith.Var [DIM('a)..<2 * DIM('a)])) \<le> 2 * DIM('a)"
        by (auto intro!:
            max_Var_floatarith_FDERIV_floatariths[le]
            max_Var_floatarith_FDERIV_n_floatariths[le]
            safe_max_Var[OF assms, le])
      have eq: "(map (subst_floatarith (\<lambda>i. Var (if 2 * DIM('a) \<le> i \<and> i < 3 * DIM('a) then i - DIM('a) else i)))
       ((FDERIV_floatariths (FDERIV_n_floatariths ode_e [0..<DIM('a)] (map floatarith.Var [DIM('a)..<2 * DIM('a)]) n)
         [0..<DIM('a)] (map floatarith.Var [2 * DIM('a)..<3 * DIM('a)])))) =
      (FDERIV_floatariths (FDERIV_n_floatariths ode_e [0..<DIM('a)] (map floatarith.Var [DIM('a)..<2 * DIM('a)]) n)
          [0..<DIM('a)] (map floatarith.Var [DIM('a)..<2 * DIM('a)]))"
        apply (rule nth_equalityI)
         apply auto defer
        apply (subst subst_floatarith_Var_FDERIV_floatarith[where 'a='a], force, force, force)
        apply (subst subst_floatarith_Var_FDERIV_n_nth[where 'a='a], force, force, force, force)
        by (simp add: o_def)
      show ?thesis
        apply (subst isFDERIV_subst_Var_floatarith[symmetric, where s="?shift"])
        subgoal by (auto intro!: mv[le] max_Var_floatariths_fold_const_fa[le])
        subgoal by (auto simp: nth_append)
        subgoal by (auto intro!: mv[le])
        subgoal
        proof -
          have "isnFDERIV DIM('a) ode_e [0..<DIM('a)] [DIM('a)..<2*DIM('a)] (list_of_eucl x @ list_of_eucl d) (Suc (Suc n))"
            apply (rule safe_isnFDERIVI)
            using assms
            by auto
          from this[simplified, THEN conjunct1]
          show ?thesis
            unfolding eq isnFDERIV.simps
            apply (rule isFDERIV_max_Var_congI)
            apply (frule less_le_trans[OF _ mv2])
            apply (auto simp: nth_append)
            done
        qed
        done
    qed
    subgoal
      by (auto intro!: safe_max_Var[OF assms, le]
          max_Var_floatarith_FDERIV_floatariths[le]
          max_Var_floatarith_FDERIV_n_floatariths[le])
    subgoal using safe_length assms by simp
    subgoal
      apply (auto simp add: nth_append
          intro!: ext arg_cong[where f=eucl_of_list] interpret_floatariths_FDERIV_floatariths_cong
          freshs_floatariths_max_Var_floatarithsI
          safe_max_Var[OF assms, le]
          max_Var_floatarith_FDERIV_floatariths[le]
          max_Var_floatarith_FDERIV_n_floatariths[le])
      apply (rule nth_equalityI)
       apply auto
      subgoal premises prems for h i j
      proof -
        have *: "(list_of_eucl x @ list_of_eucl d @ list_of_eucl d @ list_of_eucl h) =
        (map (\<lambda>i. interpret_floatarith (?shift i)
             (list_of_eucl x @ list_of_eucl d @ list_of_eucl d @ list_of_eucl h)) [0..<4 * DIM('a)])"
          by (auto intro!: nth_equalityI simp: nth_append)
        have mv_le: "max_Var_floatarith
                (DERIV_floatarith j
                  (FDERIV_floatarith
                    (FDERIV_n_floatariths ode_e [0..<DIM('a)] (map floatarith.Var [DIM('a)..<2 * DIM('a)]) n ! i)
                    [0..<DIM('a)] (map floatarith.Var [DIM('a)..<2 * DIM('a)]))) \<le>
                2 * DIM('a)"
          "max_Var_floatarith
     (DERIV_floatarith j
       (FDERIV_floatarith (FDERIV_n_floatariths ode_e [0..<DIM('a)] (map floatarith.Var [DIM('a)..<2 * DIM('a)]) n ! i)
         [0..<DIM('a)] (map floatarith.Var [2 * DIM('a)..<3 * DIM('a)])))
      \<le> 3 * DIM('a)"
          by (auto intro!: prems
              safe_max_Var[OF assms, le]
              max_Var_floatarith_le_max_Var_floatariths_nth[le]
              max_Var_floatarith_DERIV_floatarith[le]
              max_Var_floatarith_FDERIV_floatarith[le]
              max_Var_floatarith_FDERIV_n_floatariths[le])
        show ?thesis
          apply (subst *)
          apply (subst interpret_floatarith_subst_floatarith[symmetric])
           apply (auto intro!: prems mv_le[le])
          apply (subst subst_floatarith_Var_DERIV_floatarith, use prems in force)
          apply (subst subst_floatarith_Var_FDERIV_floatarith[where 'a='a], force, force, force)
          apply (subst subst_floatarith_Var_FDERIV_n_nth[where 'a='a], force, force, force, use prems in force)
          apply (auto simp: o_def prems nth_append intro!: interpret_floatarith_max_Var_cong
              dest!: less_le_trans[OF _ mv_le(1)])
          done
      qed
      done
    done
qed

lift_definition ode_d::"nat \<Rightarrow> 'a::executable_euclidean_space \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'a" is
  "\<lambda>n x dn d. if x \<in> Csafe
    then ode_d_raw n x dn d
    else 0"
  subgoal for n x dn
    apply (cases n)
    subgoal
      by (cases "x \<in> Csafe")
       (auto intro: has_derivative_bounded_linear[OF ode_d_raw_0])
    subgoal for n'
      apply (cases "x \<in> Csafe")
      subgoal
        apply (simp del: isnFDERIV.simps)
        apply (rule has_derivative_bounded_linear)
        apply (rule ode_d_raw_Suc)
        apply assumption
        done
      subgoal by (simp del: isnFDERIV.simps)
      done
    done
  done

lemma eventually_Collect_open:
  assumes "P x" "open (Collect P)"
  shows "eventually P (at x)"
  using assms(1) assms(2) eventually_at_topological by blast

lemma ode_d_has_derivative:
  assumes "x \<in> Csafe"
  shows "((\<lambda>x. ode_d n x d d) has_derivative ode_d (Suc n) x d) (at x)"
  apply (transfer fixing: safe_form ode_e n d x)
  using assms
  apply (simp del: isnFDERIV.simps)
  apply (rule if_eventually_has_derivative)
  subgoal by (rule ode_d_raw_Suc)
  subgoal
    by (rule eventually_Collect_open)
      (auto simp: safe_max_Var[OF assms] open_safe intro!: safe_max_Var[OF assms, le])
  subgoal by (simp add: isnFDERIV.simps)
  subgoal by simp
  done

lemma interpret_ode_fa[simp]:
  assumes [simp]: "length xs = DIM('a::executable_euclidean_space)" "length vs \<ge> DIM('a)" "length ode_e = DIM('a)"
    and mV:  "max_Var_floatariths ode_e \<le> DIM('a)"
  shows "(eucl_of_list (interpret_floatariths (ode_fa xs) vs)::'a) = ode (eucl_of_list (interpret_floatariths xs vs))"
  unfolding ode_fa_def
  apply (auto intro!: euclidean_eqI[where 'a='a] simp: eucl_of_list_inner ode_def)
  apply (subst interpret_floatarith_subst_floatarith[where D="length vs"])
   apply (auto intro!: max_Var_floatarith_le_max_Var_floatariths_nth[le]
      mV[le])
  apply (rule interpret_floatarith_max_Var_cong)
  apply (drule max_Var_floatariths_lessI) apply simp
  apply (drule less_le_trans[OF _ mV])
  apply auto
  apply (subst nth_map)
   apply simp  using assms(2) order.strict_trans2 apply blast
  apply (subst nth_upt) apply simp
   apply (rule less_le_trans, assumption, simp)
  apply auto
  done

lemma length_ode_fa[simp]: "length (ode_fa xs) = length ode_e"
  by (auto simp: ode_fa_def)

lemma max_Var_ode_fa[le]:
  assumes "max_Var_floatariths ode_e \<le> length xs"
  shows "max_Var_floatariths (ode_fa xs) \<le> max_Var_floatariths xs"
  by (auto simp: ode_fa_def intro!: assms max_Var_floatariths_subst_floatarith_le)

lemma max_Var_floatariths_ode_d_expr[le]:
  "max_Var_floatariths ode_e \<le> d \<Longrightarrow> d > 0 \<Longrightarrow>
    max_Var_floatariths (ode_d_expr d m) \<le> 3 * d"
  by (auto simp: ode_d_expr_def
      intro!: max_Var_floatarith_FDERIV_n_floatariths[le]
        max_Var_floatarith_FDERIV_floatariths[le])

lemma interpret_ode_d_fa:
  assumes FDERIV: "(eucl_of_list (interpret_floatariths xs vs)::'a::executable_euclidean_space) \<in> Csafe"
  assumes [simp]: "length ds = DIM('a)" "length xs = DIM('a)"
  notes [simp] = safe_length[OF FDERIV]
  shows "(eucl_of_list (interpret_floatariths (ode_d_fa n xs ds) vs)::'a) =
      ode_d n (eucl_of_list (interpret_floatariths xs vs)) (eucl_of_list (interpret_floatariths ds vs))
        (eucl_of_list (interpret_floatariths ds vs))"
  apply (transfer fixing: safe_form ode_e xs ds vs n)
  using FDERIV apply (auto simp del: isnFDERIV.simps simp: interpret_floatariths_append)
  apply (auto simp add: list_of_eucl_of_env ode_def
      ode_d_raw_def eucl_of_list_inner
      intro!: euclidean_eqI[where 'a='a])
  apply (auto simp: ode_d_fa_def )
  apply (subst interpret_floatarith_subst_floatarith[OF max_Var_floatarith_le_max_Var_floatariths_nth], simp)
  apply (rule interpret_floatarith_max_Var_cong)
  subgoal premises prems for b i
  proof -
    from prems have i: "i < max_Var_floatariths (ode_d_expr DIM('a) n)"
      by (auto dest!: max_Var_floatariths_lessI)
    also have "\<dots> \<le> 3 * DIM('a)"
      by (auto intro!: max_Var_floatariths_ode_d_expr safe_max_Var[OF FDERIV])
    finally have "i < 3 * DIM('a)" .
    then show ?thesis
      using prems i
      by (auto simp: nth_append)
  qed
  done

definition "ode_d1 x = ode_d 0 x 0"

lemma ode_d1_eq: "ode_d1 x = ode_d 0 x j"
  unfolding ode_d1_def
proof (transfer fixing: x j, rule ext, cases "x \<in> Csafe", clarsimp_all, goal_cases)
  case (1 d)
  have "isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl x @ list_of_eucl (0::'a)) =
    isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl x @ list_of_eucl j)"
    by (rule isFDERIV_max_Var_cong)
       (auto dest!: less_le_trans[OF _ safe_max_Var[OF 1]] simp: nth_append)
  moreover
  have "interpret_floatariths (FDERIV_floatariths ode_e [0..<DIM('a)] (map floatarith.Var [2 * DIM('a)..<3 * DIM('a)]))
     (list_of_eucl x @ list_of_eucl (0::'a) @ list_of_eucl d) =
    interpret_floatariths (FDERIV_floatariths ode_e [0..<DIM('a)] (map floatarith.Var [2 * DIM('a)..<3 * DIM('a)]))
     (list_of_eucl x @ list_of_eucl j @ list_of_eucl d)"
    using 1
    by (intro interpret_floatariths_fresh_cong)
      (auto dest!: not_fresh_FDERIV_floatariths not_fresh_odeD
        simp: nth_append)
  ultimately show ?case
    by (auto simp: ode_d_raw_def ode_d_expr_def)
qed

lemma ode_has_derivative:
  assumes "isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl x)"
  assumes "(x::'a::executable_euclidean_space) \<in> Csafe"
  shows "(ode has_derivative ode_d1 x) (at x)"
proof -
  from assms(1) have *: "x \<in> Csafe \<Longrightarrow> isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl x @ list_of_eucl (0::'a))"
    apply (rule isFDERIV_max_Var_congI)
    using safe_max_Var[of x]
    by (auto simp: nth_append)
  show ?thesis
    unfolding ode_d1_def
    apply (transfer fixing: x)
    apply (rule ode_d_raw_0[THEN has_derivative_eq_rhs])
    by (auto intro!: * assms)
qed

lemma ode_has_derivative_safeI:
  assumes "x \<in> Csafe"
  shows "(ode has_derivative ode_d1 x) (at x)"
  using assms
  by (auto simp: safe_def Csafe_def intro!: ode_has_derivative)

lemma safe_at_within: "x \<in> Csafe \<Longrightarrow> at x = at x within Csafe"
  by (subst (2) at_within_open)  (auto simp: open_safe)

lemma ode_d1_has_derivative:
  assumes "x \<in> Csafe"
  shows "(ode_d1 has_derivative ode_d (Suc 0) x) (at x)"
proof (rule blinfun_has_derivative_componentwiseI[THEN has_derivative_eq_rhs])
  fix i::'a assume "i \<in> Basis"
  show "((\<lambda>x. blinfun_apply (ode_d1 x) i) has_derivative ode_d (Suc 0) x i) (at x)"
    unfolding ode_d1_eq[of _ i]
    apply (rule ode_d_has_derivative)
    apply fact
    done
next
  show "(\<lambda>xa. \<Sum>i\<in>Basis. blinfun_scaleR (blinfun_inner_left i) (blinfun_apply (ode_d (Suc 0) x i) xa)) = ode_d (Suc 0) x"
    apply (rule ext)
    apply (auto intro!: ext euclidean_eqI[where 'a='a] blinfun_euclidean_eqI
        simp: blinfun.bilinear_simps inner_sum_left inner_Basis if_distrib if_distribR
        sum.delta' cong: if_cong)
    apply (rule arg_cong[where f="\<lambda>x. x \<bullet> b" for b])
  proof goal_cases
    case (1 j i b)
    from eventually_isFDERIV[where params=Nil, simplified, OF safe_isFDERIV[OF assms] order_trans[OF safe_max_Var[of x]]]
    have "\<forall>\<^sub>F x in at x. isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl x)"
      by (auto simp: assms)
    then obtain S where S: "x \<in> S" "open S" "S \<subseteq> Csafe"
      and "\<And>xa. xa \<in> S \<Longrightarrow> xa \<noteq> x \<Longrightarrow> isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl xa)"
      using assms open_safe safe_isFDERIV by auto
    then have S_FDERIV: "\<And>s. s \<in> S \<Longrightarrow>
      isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl s)"
      using safe_isFDERIV[OF assms]
      by auto
    interpret second_derivative_on_open "ode" ode_d1 "ode_d (Suc 0) x" x S
    proof standard
      fix a assume "a \<in> S"
      with S have "a \<in> Csafe" by auto
      from S_FDERIV[OF \<open>a \<in> S\<close>]
      have "isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl a)" by simp
      then have "isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl a)"
        apply (rule isFDERIV_max_Var_congI)
        using safe_max_Var[of x]
        by (auto simp: nth_append)
      then show "(ode has_derivative blinfun_apply (ode_d1 a)) (at a)"
        using \<open>a \<in> Csafe\<close>
        by (rule ode_has_derivative)
    next
      fix i
      interpret linear "ode_d (Suc 0) x"
      proof
        fix y z
        have 1: "((\<lambda>x. ode_d 0 x (y + z) (y + z)) has_derivative ode_d (Suc 0) x (y + z)) (at x)"
          apply (rule ode_d_has_derivative)
          apply (rule assms)
          done
        have *: "ode_d 0 x (y + z) (y + z) = ode_d 0 x y y + ode_d 0 x z z" for x
          by (auto simp: blinfun.bilinear_simps ode_d1_eq[symmetric])
        have 2: "((\<lambda>x. ode_d 0 x (y + z) (y + z)) has_derivative
            ode_d (Suc 0) x y + ode_d (Suc 0) x z) (at x)"
          apply (subst *)
          apply (rule derivative_eq_intros)
            apply (rule ode_d_has_derivative)
            apply fact
           apply (rule ode_d_has_derivative)
           apply fact
          apply (auto simp: blinfun.bilinear_simps)
          done
        from has_derivative_unique[OF 1 2]
        show "ode_d (Suc 0) x (y + z) = ode_d (Suc 0) x y + ode_d (Suc 0) x z"
          by (auto intro!: blinfun_eqI)
      next
        fix r y
        have 1: "((\<lambda>x. ode_d 0 x (r *\<^sub>R y) (r *\<^sub>R y)) has_derivative ode_d (Suc 0) x (r *\<^sub>R y)) (at x)"
          by (rule ode_d_has_derivative; fact)
        have *: "ode_d 0 x (r *\<^sub>R y) (r *\<^sub>R y) = r *\<^sub>R ode_d 0 x y y" for x
          by (auto simp: blinfun.bilinear_simps ode_d1_eq[symmetric])
        have 2: "((\<lambda>x. ode_d 0 x (r *\<^sub>R y) (r *\<^sub>R y)) has_derivative
            r *\<^sub>R ode_d (Suc 0) x y) (at x)"
          apply (subst *)
          apply (rule derivative_eq_intros)
          apply (rule ode_d_has_derivative; fact)
          apply (auto simp: blinfun.bilinear_simps)
          done
        from has_derivative_unique[OF 1 2]
        show "(ode_d (Suc 0) x (r *\<^sub>R y)) = (r *\<^sub>R ode_d (Suc 0) x y)"
          by (auto intro!: blinfun_eqI)
      qed
      show "((\<lambda>x. blinfun_apply (ode_d1 x) i) has_derivative blinfun_apply (ode_d (Suc 0) x i))
          (at x)"
        apply (subst euclidean_representation[of i, symmetric])
        apply (subst (2) euclidean_representation[of i, symmetric])
        apply (auto simp: blinfun.bilinear_simps)
        apply (rule derivative_eq_intros)
         apply (rule derivative_eq_intros)
          apply (subst_tac j = i in ode_d1_eq)
          apply (rule ode_d_has_derivative)
          apply (rule assms)
        apply force
        apply (auto simp: blinfun.bilinear_simps[symmetric]
            intro!: ext euclidean_eqI[where 'a='a] blinfun_euclidean_eqI)
        apply (rule arg_cong[where f="\<lambda>x. x \<bullet> b" for b])
        by (auto simp: sum scaleR)
    next
      show "x \<in> S" "open S" by fact+
    qed
    show ?case
      by (rule symmetric_second_derivative) fact
  qed
qed

lemma ode_d1_has_derivative_safeI:
  assumes "x \<in> Csafe"
  shows "(ode_d1 has_derivative ode_d (Suc 0) x) (at x)"
  apply (rule ode_d1_has_derivative)
  using assms by (auto simp: safe_def)

sublocale c1_on_open_euclidean ode ode_d1 Csafe
  by unfold_locales
    (auto simp: continuous_on_eq_continuous_within at_within_open[OF _ open_safe]
      intro!: derivative_eq_intros  continuous_at_imp_continuous_on open_safe
        ode_has_derivative_safeI continuous_blinfun_componentwiseI
        has_derivative_continuous ode_d1_has_derivative_safeI)

definition ivlflows ::
    "'a::executable_euclidean_space sctn set
     \<Rightarrow> (('a \<times> 'a \<Rightarrow>\<^sub>L 'a) set
         \<Rightarrow> ('a \<times> 'a \<Rightarrow>\<^sub>L 'a) set \<times> ('a \<times> 'a \<Rightarrow>\<^sub>L 'a) set)
        \<Rightarrow> ('a \<times> 'a \<Rightarrow>\<^sub>L 'a) set \<Rightarrow> 'a sctn \<Rightarrow> bool"
where "ivlflows stops stopcont trap rsctn =
  (\<forall>ivl. ivl \<subseteq> UNION stops plane_of \<times> UNIV \<longrightarrow>
      ivl \<subseteq> (snd (stopcont ivl)) \<and>
      fst (stopcont ivl) \<subseteq> snd (stopcont ivl) \<and>
      (fst (stopcont ivl)) \<subseteq> sbelow_halfspace rsctn \<times> UNIV \<and>
      (snd (stopcont ivl)) \<subseteq> sbelow_halfspace rsctn \<times> UNIV \<and>
      flowsto (ivl) {0..} ((snd (stopcont ivl))) ((fst (stopcont ivl)) \<union> trap))"

lemma ivlflowsD:
  assumes "ivlflows stops stopcont trap rsctn" "ivl \<subseteq> UNION stops plane_of \<times> UNIV "
  shows "ivl \<subseteq> (snd (stopcont ivl))"
    "(fst (stopcont ivl)) \<subseteq> sbelow_halfspace rsctn \<times> UNIV"
    "fst (stopcont ivl) \<subseteq> snd (stopcont ivl)"
    "(snd (stopcont ivl)) \<subseteq> sbelow_halfspace rsctn \<times> UNIV"
    "flowsto (ivl) {0..} ((snd (stopcont ivl))) ((fst (stopcont ivl)) \<union> trap)"
  using assms(1)[unfolded ivlflows_def, rule_format, OF assms(2)]
  by auto

lemma ivlflows_flowsto:
  assumes "ivlflows stops stopcont trap rsctn" "ivl \<subseteq> UNION stops plane_of \<times> UNIV"
  assumes "stopcont ivl = (x, y)"
  shows "flowsto (ivl) {0..} y (x \<union> trap)"
  using ivlflowsD[OF assms(1,2)] assms(3)
  by auto

lemma ivlflows_emptyI: "ivlflows {} (\<lambda>x. (x, x)) J K"
  by (auto simp: ivlflows_def set_of_ivl_def)

lemma plane_of_neg[simp]: "plane_of (Sctn (- normal sctn) (- pstn sctn)) = plane_of sctn"
  by (auto simp: plane_of_def)

lemmas safe_max_Var_le[intro] = safe_max_Var[le]

lift_definition ode_d2::"'a::executable_euclidean_space \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'a \<Rightarrow>\<^sub>L 'a" is "\<lambda>x.
  if x \<in> Csafe then ode_d 1 x else (\<lambda>_. 0)"
  by (auto intro!: has_derivative_bounded_linear ode_d1_has_derivative)

lemmas [simp] = safe_length

lemma continuous_on_ode_d2: "continuous_on (Csafe) ode_d2"
proof -
  have isn: "isnFDERIV DIM('a) ode_e [0..<DIM('a)] [DIM('a)..<2 * DIM('a)] (list_of_eucl x @ list_of_eucl i)
                 (Suc (Suc 0))"
    if "x \<in> Csafe"
    for x i::'a
    by (rule safe_isnFDERIV) fact
  have "continuous_on (Csafe::'a set) (\<lambda>x. ode_d_raw (Suc 0) x i j)"
     if "i \<in> Basis" "j \<in> Basis" for i j
    apply (rule has_derivative_continuous_on)
    apply (auto simp: ode_d_raw_def at_within_open[OF _ open_safe])
     apply (rule interpret_floatarith_FDERIV_floatariths_append)
    apply (auto simp: ode_d_expr_def 
        intro!: isDERIV_FDERIV_floatariths safe_isFDERIV_append that isFDERIV_map_Var
        safe_max_Var_le
        max_Var_floatarith_FDERIV_floatariths[le])
     apply assumption
    apply arith
    done
  then show ?thesis
    apply (auto intro!: continuous_on_blinfun_componentwise)
    subgoal for i j
    apply (rule continuous_on_eq[where f="(\<lambda>x. ode_d_raw (Suc 0) x i j)"])
       apply force
      apply (subst ode_d2.rep_eq)
      apply simp
      apply (subst ode_d.rep_eq)
      apply (split if_splits)
      apply (rule conjI) apply simp
      using isn apply force
      done
    done
qed

lemmas continuous_on_ode_d2_comp[continuous_intros] = continuous_on_compose2[OF continuous_on_ode_d2]


definition ode_na::"real \<times> _ \<Rightarrow> _" where "ode_na = (\<lambda>a. ode (snd a))"

definition ode_d_na::"real \<times> _ \<Rightarrow> (real \<times> _) \<Rightarrow>\<^sub>L _" where "ode_d_na = (\<lambda>tx. ode_d1 (snd tx) o\<^sub>L snd_blinfun)"
definition ode_d2_na::"real \<times> _ \<Rightarrow> (real \<times> _) \<Rightarrow>\<^sub>L (real \<times> _) \<Rightarrow>\<^sub>L _" where
  "ode_d2_na = (\<lambda>tx. flip_blinfun (flip_blinfun (ode_d2 (snd tx) o\<^sub>L snd_blinfun) o\<^sub>L snd_blinfun))"

lemma map_ode_fa_nth[simp]:
  "d \<le> length ode_e \<Longrightarrow> map (ode_fa_nth CX) [0..<d] = map ((!) (ode_fa CX)) [0..<d]"
  by (auto simp: ode_fa_nth cong: map_cong)

lemma map_ode_d_fa_nth[simp]:
  "d \<le> length ode_e \<Longrightarrow> map (ode_d_fa_nth i CX X) [0..<d] = map ((!) (ode_d_fa i CX X)) [0..<d]"
  by (auto simp: ode_d_fa_nth cong: map_cong)

lemma einterpret_euler_incr_fas:
  assumes "length ode_e = DIM('a)" "length X0 = DIM('a)" "length CX = DIM('a)"
    "DIM('a) \<le> length vs" "max_Var_floatariths ode_e \<le> DIM('a)"
  shows "(einterpret (euler_incr_fas X0 h CX) vs::'a::executable_euclidean_space) =
    einterpret X0 vs + (interpret_floatarith h vs) *\<^sub>R ode (einterpret CX vs)"
  by (simp add: euler_incr_fas_def euler_incr_fas_nth_def assms ode_fa_nth cong: map_cong)

lemma einterpret_euler_err_fas:
  assumes safe: "(einterpret CX vs::'a) \<in> Csafe"
  assumes [simp]: "length X0 = DIM('a)" "length CX = DIM('a)" "DIM('a) \<le> length vs"
  shows "(einterpret (euler_err_fas X0 h CX) vs::'a::executable_euclidean_space) =
    (((interpret_floatarith h vs))\<^sup>2/2) *\<^sub>R ode_d 0 (einterpret CX vs) (ode (einterpret CX vs)) (ode (einterpret CX vs))"
  using safe_length[OF safe] safe_max_Var[OF safe]
  apply (simp add: euler_err_fas_def euler_err_fas_nth_def[abs_def] euler_incr_fas_def)
  apply (subst interpret_ode_d_fa)
  by (auto simp: safe)

lemma einterpret_euler_fas1:
  assumes safe[simp]: "(einterpret CX vs::'a) \<in> Csafe"
  assumes [simp]: "length X0 = DIM('a)" "length CX = DIM('a)" "DIM('a) \<le> length vs"
  shows "(einterpret (take DIM('a) (euler_fas X0 h CX)) vs::'a::executable_euclidean_space) =
    einterpret X0 vs + (interpret_floatarith h vs) *\<^sub>R ode (einterpret X0 vs) +
    (((interpret_floatarith h vs))\<^sup>2/2) *\<^sub>R ode_d 0 (einterpret CX vs) (ode (einterpret CX vs)) (ode (einterpret CX vs))"
  using safe_length[OF safe] safe_max_Var[OF safe]
  by (simp add: euler_fas_def euler_incr_fas_def euler_incr_fas_nth_def[abs_def]
      einterpret_euler_err_fas euler_err_fas_nth_def[abs_def] interpret_ode_d_fa)

lemma einterpret_euler_fas2:
  assumes [simp]: "(einterpret CX vs::'a) \<in> Csafe"
  assumes [simp]: "length X0 = DIM('a)" "length CX = DIM('a)" "DIM('a) \<le> length vs"
  shows "(einterpret (drop DIM('a) (euler_fas  X0 h CX)) vs::'a::executable_euclidean_space) =
    (((interpret_floatarith h vs))\<^sup>2/2) *\<^sub>R ode_d 0 (einterpret CX vs) (ode (einterpret CX vs)) (ode (einterpret CX vs))"
  by (simp add: euler_fas_def euler_incr_fas_def einterpret_euler_err_fas)

lemma ode_d_Suc_0_eq_ode_d2: "x \<in> Csafe \<Longrightarrow> ode_d (Suc 0) x = ode_d2 x"
  unfolding ode_d2.rep_eq by auto

lemma rk2_increment_rk2_fas_err:
  fixes h s1 s2 rkp x0 cx vs
  defines "h' \<equiv> interpret_floatarith h vs"
  defines "s2' \<equiv> interpret_floatarith s2 vs"
  defines "rkp' \<equiv> interpret_floatarith rkp vs"
  defines "x0' \<equiv> einterpret x0 vs"
  defines "cx' \<equiv> einterpret cx vs"
  assumes cx_flow: "cx' = flow0 x0' (h' * s1')"
  assumes [simp]: "length x0 = DIM('a)" "length cx = DIM('a)" "DIM('a) \<le> length vs"
  assumes safes: "x0' \<in> Csafe" "cx' \<in> Csafe" "(x0' + (s2' * h' * rkp') *\<^sub>R ode x0')\<in> Csafe"
  shows "(einterpret (rk2_fas_err rkp x0 h cx s2) vs::'a::executable_euclidean_space) =
    heun_remainder1 (flow0 x0') ode_na ode_d_na ode_d2_na 0 h' s1' -
    heun_remainder2 rkp' (flow0 x0') ode_na     ode_d2_na 0 h' s2'"
  using safes
  using safe_length[OF safes(1)] safe_max_Var[OF safes(1)]
  apply (auto simp: heun_remainder1_def heun_remainder2_def discrete_evolution_def
      ode_na_def ode_d_na_def ode_d2_na_def rk2_increment x0'_def rkp'_def h'_def s2'_def
      cx'_def euler_incr_fas_def rk2_fas_err_def rk2_fas_err_nth_def[abs_def]
        euler_incr_fas_nth_def[abs_def]
        interpret_ode_d_fa)
  apply (simp add: ode_d1_eq[symmetric] ode_d_Suc_0_eq_ode_d2 inverse_eq_divide)
  apply (simp add: algebra_simps field_simps divide_simps)
  unfolding cx'_def[symmetric] cx_flow x0'_def h'_def
  apply (simp add: algebra_simps)
  done

lemma map_rk2_fas_err_nth[simp]:
  "d = length ode_e \<Longrightarrow> length b = length ode_e \<Longrightarrow> map (rk2_fas_err_nth a b c e f) [0..<d] = map ((!) (rk2_fas_err a b c e f)) [0..<d]"
  unfolding rk2_fas_err_nth_def rk2_fas_err_def
  by (rule map_cong) auto

lemma rk2_increment_rk2_fas1:
  fixes h s1 s2 rkp x0 cx vs
  defines "h' \<equiv> interpret_floatarith h vs"
  defines "s2' \<equiv> interpret_floatarith s2 vs"
  defines "rkp' \<equiv> interpret_floatarith rkp vs"
  defines "x0' \<equiv> einterpret x0 vs"
  defines "cx' \<equiv> einterpret cx vs"
  assumes cx_flow: "cx' = flow0 x0' (h' * s1')"
  assumes [simp]: "length x0 = DIM('a)" "length cx = DIM('a)" "DIM('a) \<le> length vs"
  assumes safes: "(x0'::'a)\<in> Csafe" "(cx'::'a)\<in> Csafe" "(x0' + (s2' * h' * rkp') *\<^sub>R ode x0'::'a)\<in> Csafe"
  shows "(einterpret (take DIM('a) (rk2_fas rkp x0 h cx s2)) vs::'a::executable_euclidean_space) =
    discrete_evolution (rk2_increment rkp' (\<lambda>_. ode)) h' 0 x0' + (heun_remainder1 (flow0 x0') ode_na ode_d_na ode_d2_na 0 h' s1' -
    heun_remainder2 rkp' (flow0 x0') ode_na ode_d2_na 0 h' s2')"
  using safes  using safe_length[OF safes(1)] safe_max_Var[OF safes(1)]
  apply (auto simp: discrete_evolution_def rk2_fas_def)
  apply (subst rk2_increment_rk2_fas_err[OF cx_flow[unfolded cx'_def x0'_def h'_def]])
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by (simp add: x0'_def)
  subgoal by (simp add: cx'_def)
  subgoal by (simp add: x0'_def s2'_def h'_def rkp'_def)
  subgoal using [[show_consts, show_sorts, show_types]]
    by (auto simp: x0'_def s2'_def h'_def rkp'_def rk2_increment euler_incr_fas_def
        euler_incr_fas_nth_def[abs_def] inverse_eq_divide)
  done

lemma rk2_increment_rk2_fas2:
  fixes h s1 s2 rkp x0 cx vs
  defines "h' \<equiv> interpret_floatarith h vs"
  defines "s2' \<equiv> interpret_floatarith s2 vs"
  defines "rkp' \<equiv> interpret_floatarith rkp vs"
  defines "x0' \<equiv> einterpret x0 vs"
  defines "cx' \<equiv> einterpret cx vs"
  assumes cx_flow: "cx' = flow0 x0' (h' * s1')"
  assumes [simp]: "length x0 = DIM('a)" "length cx = DIM('a)" "DIM('a) \<le> length vs"
  assumes safes: "x0'\<in> Csafe" "cx'\<in> Csafe" "(x0' + (s2' * h' * rkp') *\<^sub>R ode x0')\<in> Csafe"
  shows "(einterpret (drop DIM('a) (rk2_fas rkp x0 h cx s2)) vs::'a::executable_euclidean_space) =
    (heun_remainder1 (flow0 x0') ode_na ode_d_na ode_d2_na 0 h' s1' -
    heun_remainder2 rkp' (flow0 x0') ode_na      ode_d2_na 0 h' s2')"
  using safes
  apply (auto simp: discrete_evolution_def rk2_fas_def)
  apply (subst rk2_increment_rk2_fas_err[OF cx_flow[unfolded cx'_def x0'_def h'_def]])
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by (simp add: x0'_def)
  subgoal by (simp add: cx'_def)
  subgoal by (simp add: x0'_def s2'_def h'_def rkp'_def)
  subgoal by (auto simp: x0'_def s2'_def h'_def rkp'_def rk2_increment euler_incr_fas_def inverse_eq_divide)
  done

subsubsection \<open>safe set relation\<close>

definition sappr_rel_internal_def: "sappr_rel = appr_rel O {(x,y). x = y \<and> x \<subseteq> Csafe}"
lemmas [autoref_rel_intf] = REL_INTFI[of sappr_rel i_appr]

lemmas sappr_rel_internal = sappr_rel_internal_def

lemma sappr_rel_br: "sappr_rel =
    br (\<lambda>xs. eucl_of_list ` set_of_appr xs::'a set)
     (\<lambda>xs. length xs = DIM('a::executable_euclidean_space) \<and> eucl_of_list ` set_of_appr xs \<subseteq> (Csafe::'a set))"
  by (auto simp: sappr_rel_internal_def appr_rel_br br_def)

lemma sv_sappr_rel[relator_props]: "single_valued sappr_rel"
  unfolding sappr_rel_br
  by (auto simp: single_valuedI relator_props)

definition "euler_incr_fas' D = (map fold_const_fa (euler_incr_fas (map floatarith.Var [0..<D]) (floatarith.Var (D))
      (map floatarith.Var [Suc D..<Suc (2*D)])))"
sublocale autoref_op_pat_def euler_incr_fas' .
definition "euler_fas' D = (map fold_const_fa (euler_fas  (map floatarith.Var [0..<D])
    (floatarith.Var (2*D)) (map floatarith.Var [D..<2*D])))"
sublocale autoref_op_pat_def euler_fas' .
definition "rk2_fas' D = (map fold_const_fa (rk2_fas
    (floatarith.Var (2*D))
    (map floatarith.Var [0..<D])
    (floatarith.Var (2*D+1))
    (map floatarith.Var [D..<2*D])
    (floatarith.Var (2*D+2))))"
sublocale autoref_op_pat_def rk2_fas' .
lemma [autoref_rules]: "(euler_incr_fas', euler_incr_fas') \<in> nat_rel \<rightarrow> fas_rel"
  "(euler_fas', euler_fas') \<in> nat_rel \<rightarrow> fas_rel"
  "(rk2_fas', rk2_fas') \<in> nat_rel \<rightarrow> fas_rel"
  by auto

definition "ode_slp_eq ode_slp \<longleftrightarrow> ode_slp = slp_of_fas ode_e"
lemmas ode_slp_eqD = ode_slp_eq_def[THEN iffD1]
definition "euler_incr_slp_eq euler_incr_slp D \<longleftrightarrow>
  euler_incr_slp = slp_of_fas (euler_incr_fas' D)"
lemmas euler_incr_slp_eqD = euler_incr_slp_eq_def[THEN iffD1]
definition "euler_slp_eq euler_slp D \<longleftrightarrow>
  euler_slp = slp_of_fas (euler_fas' D)"
lemmas euler_slp_eqD = euler_slp_eq_def[THEN iffD1]
definition "rk2_slp_eq rk2_slp D \<longleftrightarrow> rk2_slp = slp_of_fas (rk2_fas' D)"
lemmas rk2_slp_eqD = rk2_slp_eq_def[THEN iffD1]

end

locale approximate_sets_ode_slp = approximate_sets_options
  where appr_rell = appr_rell
    and ode_e = ode_e
    and safe_form = safe_form
    and optns = optns
    for appr_rell :: "('b list \<times> real list set) set" and safe_form ode_e optns and
      D::nat and ode_slp euler_incr_slp euler_slp rk2_slp::slp
begin

lemma autoref_parameters:
  "(D, D) \<in> nat_rel"
  "(ode_slp, ode_slp) \<in> \<langle>Id\<rangle>list_rel"
  "(ode_e, ode_e) \<in> \<langle>Id\<rangle>list_rel"
  "(euler_slp, euler_slp) \<in> slp_rel"
  "(euler_incr_slp, euler_incr_slp) \<in> slp_rel"
  "(rk2_slp, rk2_slp) \<in> slp_rel"
  "(safe_form, safe_form) \<in> Id"
  by auto

definition pad_zeroes :: "nat \<Rightarrow> real list set \<Rightarrow> real list set"
  where [simp]: "pad_zeroes n X = (\<lambda>xs. xs @ replicate n (0::real)) ` X"

lemma [autoref_op_pat_def]:
  "(\<lambda>xs. xs @ replicate D 0) ` X \<equiv> OP (pad_zeroes D) $ X"
  "pad_zeroes D X \<equiv> OP (pad_zeroes D) $ X" by simp_all

lemma op_append_image_autoref[autoref_rules]:
  assumes [simplified, symmetric, simp]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  shows "(\<lambda>xs. xs @ appr_of_ivl (replicate D 0) (replicate D 0), pad_zeroes D) \<in>
      appr_rell \<rightarrow> appr_rell"
  by (auto simp: appr_rell_internal br_def set_of_appr_of_ivl_append_point)

definition safe_set
  where "safe_set X = do {
    b1 \<leftarrow> approx_form_spec safe_form (list_of_eucl ` X);
    b2 \<leftarrow> isFDERIV_spec D [0..<D] ode_e (list_of_eucl ` X);
    RETURN (b1 \<and> b2)
  }"
sublocale autoref_op_pat_def safe_set .
schematic_goal safe_set_appr:
  assumes [autoref_rules]: "(Xi, X) \<in> appr_rel"
  notes [autoref_rules] = autoref_parameters
  shows "(nres_of ?f, safe_set $ X) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding safe_set_def
  by autoref_monadic
concrete_definition safe_set_appr for Xi uses safe_set_appr
lemma safe_set_appr_refine[autoref_rules]:
  "(\<lambda>Xi. nres_of (safe_set_appr Xi), safe_set) \<in> appr_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using safe_set_appr.refine by force

definition "wd (TYPE('a)) \<longleftrightarrow>
  (open_form safe_form \<and> length ode_e = DIM('a::executable_euclidean_space) \<and>
    max_Var_floatariths ode_e \<le> DIM('a) \<and> max_Var_form safe_form \<le> DIM('a) \<and> D = DIM('a))"

lemma wdD:
  assumes "wd TYPE('a::executable_euclidean_space)"
  shows "open_form safe_form" "length ode_e = DIM('a)" "max_Var_floatariths ode_e \<le> DIM('a)"
    "max_Var_form safe_form \<le> DIM('a)"
    "D = DIM('a)" "ode_e \<noteq> []"
  using assms
  by (auto simp: wd_def)

definition "mk_safe (X::'a::executable_euclidean_space set) = do {
    ASSERT (wd TYPE('a));
    s \<leftarrow> safe_set (X:::appr_rel::'a set);
    if s then RETURN (X:::appr_rel) else SUCCEED
  }"
sublocale autoref_op_pat_def mk_safe .

lemmas [refine_vcg_def] = approx_form_spec_def isFDERIV_spec_def

lemma safe_set_spec[THEN order.trans, refine_vcg]:
  assumes "wd TYPE('a::executable_euclidean_space)"
  shows "safe_set X \<le> SPEC (\<lambda>r. r \<longrightarrow> (X::'a set) \<subseteq> Csafe)"
  unfolding safe_set_def
  by (refine_vcg) (auto simp del: isnFDERIV.simps simp add: Csafe_def safe_def replicate_eq_list_of_eucl_zero wdD[OF \<open>wd _\<close>])

lemma mk_safe[le, refine_vcg]: "wd TYPE('a::executable_euclidean_space)\<Longrightarrow>
  mk_safe X \<le> SPEC (\<lambda>R::'a set. R = X \<and> X \<subseteq> Csafe)"
  unfolding mk_safe_def
  by refine_vcg

schematic_goal mk_safe_impl:
  assumes [autoref_rules]: "(Ri, R) \<in> appr_rel"
  shows "(nres_of ?f, mk_safe $ (R::'a::executable_euclidean_space set)) \<in> \<langle>appr_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding mk_safe_def
  by (autoref_monadic)
concrete_definition mk_safe_impl for Ri uses mk_safe_impl

lemma sappr_rel_nres_relI:
  assumes "(Xi, X) \<in> \<langle>appr_rel\<rangle>nres_rel"
  assumes "X \<le> SPEC (\<lambda>X. X \<subseteq> Csafe)"
  shows "(Xi, X) \<in> \<langle>sappr_rel\<rangle>nres_rel"
  using assms
  by (fastforce simp: sappr_rel_br br_def appr_rel_br nres_rel_def conc_fun_def split: nres.splits
      intro: order_trans)

lemma mk_safe_autoref[autoref_rules]:
  shows "(\<lambda>x. nres_of (mk_safe_impl x), mk_safe) \<in> appr_rel \<rightarrow> \<langle>sappr_rel\<rangle>nres_rel"
  apply (rule fun_relI)
  apply (auto simp: nres_rel_def mk_safe_def)
  apply refine_vcg
  apply (rule nres_relD)
  apply (rule sappr_rel_nres_relI)
  subgoal premises prems for a b
    using mk_safe_impl.refine[OF prems(1)] prems(2)
    by (auto simp: mk_safe_def)
  subgoal by (refine_vcg)
  done

definition
  "mk_safe_coll X = do {
      XS \<leftarrow> (sets_of_coll X);
      FORWEAK XS (RETURN op_empty_coll)
        (\<lambda>x. do {
          s \<leftarrow> mk_safe (x);
          RETURN (mk_coll s)
        })
        (\<lambda>b c. RETURN (b \<union> c))
    }"
sublocale autoref_op_pat_def mk_safe_coll .

lemma mk_safe_coll[le, refine_vcg]: "wd TYPE('a::executable_euclidean_space) \<Longrightarrow>
    mk_safe_coll X \<le> SPEC (\<lambda>R::'a set. R = X \<and> X \<subseteq> Csafe)"
  unfolding mk_safe_coll_def autoref_tag_defs
  by (refine_vcg FORWEAK_invarI[where I="\<lambda>a b. X = \<Union>b \<union> a \<and> a \<subseteq> Csafe"]) auto

schematic_goal mk_safe_coll_impl:
  assumes [autoref_rules]: "(ISi, IS) \<in> clw_rel appr_rel"
  shows "(nres_of (?f::?'c dres), mk_safe_coll IS)\<in>?R"
  unfolding mk_safe_coll_def
  by (subst rel_ANNOT_eq[of "sets_of_coll X" "\<langle>\<langle>appr_rel\<rangle>list_wset_rel\<rangle>nres_rel" for X])
    (autoref_monadic)

concrete_definition mk_safe_coll_impl for ISi uses mk_safe_coll_impl
lemma mk_safe_coll_impl_refine[autoref_rules]:
  "(\<lambda>ISi. nres_of (mk_safe_coll_impl ISi), mk_safe_coll) \<in> clw_rel appr_rel \<rightarrow> \<langle>clw_rel (sappr_rel)\<rangle>nres_rel"
  using mk_safe_coll_impl.refine
  by force

definition ode_set::"'a::executable_euclidean_space set \<Rightarrow> 'a set nres" where "ode_set X = do {
  _ \<leftarrow> mk_safe X;
  approx_slp_appr ode_e ode_slp (list_of_eucl ` (X))
  }"
sublocale autoref_op_pat_def ode_set .

definition [simp]: "op_DIM TYPE('a) = DIM('a::executable_euclidean_space)"
lemma [autoref_op_pat_def]: "DIM('a) \<equiv> OP (op_DIM TYPE('a::executable_euclidean_space))" by simp
lemma op_DIM[autoref_rules]:
  assumes [simplified, symmetric, simp]: "DIM_precond TYPE('a) D"
  shows "(D, (op_DIM TYPE('a::executable_euclidean_space))) \<in> nat_rel"
  using assms
  by auto

schematic_goal ode_set_impl:
  assumes [autoref_rules]: "(Xi, X) \<in> appr_rel"
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  notes [autoref_rules] = autoref_parameters
  shows "(nres_of ?f, ode_set $ X::'a set nres) \<in> \<langle>appr_rel\<rangle>nres_rel"
  unfolding ode_set_def[abs_def]
  including art
  by autoref_monadic
concrete_definition ode_set_impl for Xi uses ode_set_impl
lemmas [autoref_rules] = ode_set_impl.refine

lemma ode_set_spec[THEN order.trans, refine_vcg]:
  assumes [refine_vcg]: "wd TYPE('a::executable_euclidean_space)"
  assumes "ode_slp_eq ode_slp"
  shows "ode_set X \<le> SPEC (\<lambda>r. ode ` X \<subseteq> (r::'a set))"
  using assms wdD[OF assms(1)]
  unfolding ode_set_def
  apply (refine_vcg)
  subgoal by (auto simp: env_len_def ode_slp_eq_def)
  subgoal premises prems
    using prems(1,2,4-)
    by (auto simp: env_len_def eucl_of_list_prod ode_def)
  done

definition "ncc (X::'a::executable_euclidean_space set) \<longleftrightarrow> X \<noteq> {} \<and> compact X \<and> convex X"

definition "op_nres_ASSUME_bnd_safecoll x = op_nres_ASSUME_bnd (x \<subseteq> Csafe)"
sublocale autoref_op_pat_def op_nres_ASSUME_bnd_safecoll .

lemma ASSUME_safecoll[autoref_op_pat_def]: "do {ASSUME (x \<subseteq> Csafe); f} \<equiv> op_nres_ASSUME_bnd_safecoll x f"
  by (auto simp: op_nres_ASSUME_bnd_safecoll_def)

definition "saferel R \<longleftrightarrow> (\<forall>(c, A) \<in> R. A \<subseteq> Csafe)"

lemma saferel_trigger: "\<And>R. saferel R \<Longrightarrow> saferel R"
  by simp

declaration \<open>Tagged_Solver.add_triggers "Relators.relator_props_solver" @{thms saferel_trigger}\<close>

lemma saferel_coll[relator_props]:
  "saferel A \<Longrightarrow> saferel (\<langle>L, A\<rangle>Union_rel)"
  by (force simp: saferel_def Union_rel_def br_def set_rel_def)

lemma saferel_sappr[relator_props]:
  "saferel (sappr_rel)"
  by (auto simp: saferel_def sappr_rel_br br_def)

lemma saferel_info_rel[relator_props]:
  "saferel A \<Longrightarrow> saferel (\<langle>R, A\<rangle>info_rel)"
  by (force simp: saferel_def info_rel_def br_def)

lemma saferel_inter_rel[relator_props]:
  "saferel A \<Longrightarrow> saferel (\<langle>A, B\<rangle>inter_rel)"
  by (auto simp: inter_rel_def saferel_def set_rel_def)

lemma saferel_invar_rel[relator_props]:
  "saferel A \<Longrightarrow> saferel (\<langle>X, A\<rangle>invar_rel a)"
  by (auto simp: invar_rel_def saferel_def set_rel_def)

lemma autoref_ASSUME_bnd_safecoll[autoref_rules]:
  assumes "PREFER saferel A"
  assumes "X \<subseteq> Csafe \<Longrightarrow> (m',m) \<in> \<langle>R\<rangle>nres_rel"
  assumes "(Xi, X) \<in> A"
  shows "(m', (((OP op_nres_ASSUME_bnd_safecoll) ::: A \<rightarrow> \<langle>R\<rangle>nres_rel \<rightarrow> \<langle>R\<rangle>nres_rel)) $ X $ m)\<in>\<langle>R\<rangle>nres_rel"
  using assms
  by (auto simp: op_nres_ASSUME_bnd_safecoll_def saferel_def)

lemmas fderiv[derivative_intros] = ode_has_derivative_safeI

lemma fderiv2[derivative_intros]:
  "x \<in> Csafe \<Longrightarrow> (ode_d1 has_derivative ode_d2 x) (at x)"
  by (frule ode_d1_has_derivative_safeI)
    (simp add: ode_d_Suc_0_eq_ode_d2)

lemma derivative_within_safe[derivative_intros]:
  "(g has_derivative h) (at x) \<Longrightarrow> (g has_derivative h) (at x within Csafe)"
  by (rule has_derivative_at_withinI)

lemma cont_fderiv: "continuous_on (Csafe) ode_d1"
  by (rule has_derivative_continuous_on) (auto intro!: derivative_intros)

lemmas cont_fderiv'[continuous_intros] = continuous_on_compose2[OF cont_fderiv]

lemma continuous_on_ode1:
  "continuous_on (Csafe) (ode)"
  using fderiv
  by (auto intro!: has_derivative_continuous_on derivative_intros)

lemma continuous_on_ode[continuous_intros]:
  "continuous_on s g \<Longrightarrow> (\<And>x. x \<in> s \<Longrightarrow> (g x) \<in> Csafe) \<Longrightarrow> continuous_on s (\<lambda>x. ode (g x))"
  using continuous_on_ode1
  by (rule continuous_on_compose2) auto

lemma fderiv'[derivative_intros]:
  assumes "(g has_derivative g' y) (at y within X)"
  assumes "(g y) \<in> Csafe"
  shows "((\<lambda>y. ode (g y)) has_derivative
    (blinfun_apply (ode_d1 (g y)) \<circ>\<circ> g') y) (at y within X)"
  using diff_chain_within[OF assms(1) has_derivative_within_subset[OF fderiv]] assms(2)
  by (simp add: o_def)

lemma fderiv2'[derivative_intros]:
  assumes "(g has_derivative g' y) (at y within X)"
  assumes "(g y) \<in> Csafe"
  shows "((\<lambda>y. ode_d1 (g y)) has_derivative
    (blinfun_apply (ode_d2 (g y)) \<circ>\<circ> g') y) (at y within X)"
  using diff_chain_within[OF assms(1) has_derivative_within_subset[OF fderiv2]] assms(2)
  by (simp add: o_def)


subsubsection \<open>step of Picard iteration\<close>

definition "nonempty X \<longleftrightarrow> X \<noteq> {}"
lemma ncc_interval: "ncc {a .. b::'a::executable_euclidean_space} \<longleftrightarrow> a \<le> b"
  by (auto simp: ncc_def)
lemma nonempty_interval: "nonempty {a .. b::'a::executable_euclidean_space} \<longleftrightarrow> a \<le> b"
  by (auto simp: nonempty_def)

definition
  "Picard_step X0 t0 h X = SPEC (\<lambda>R.
    case R of
      Some R \<Rightarrow>
        nonempty R \<and> compact R \<and> (R \<subseteq> Csafe) \<and>
        (\<forall>x0 \<in> X0. \<forall>h'\<in>{t0 .. t0 + h}. \<forall>phi\<in>cfuncset t0 h' X.
          x0 + integral {t0 .. h'} (\<lambda>t. ode (phi t)) \<in> R)
      | None \<Rightarrow> True)"
sublocale autoref_op_pat_def Picard_step .

lemmas [refine_vcg] = Picard_step_def[THEN eq_refl, THEN order.trans]

definition [simp]: "set_of_sappr X \<equiv> X"
sublocale autoref_op_pat_def set_of_sappr .

lemmas sappr_rel_def = sappr_rel_internal_def

lemma set_of_sappr[autoref_rules]: "(\<lambda>x. x, set_of_sappr) \<in> sappr_rel \<rightarrow> appr_rel"
  by (auto simp: sappr_rel_def)

definition Picard_step_ivl :: "'a::executable_euclidean_space set \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a set \<Rightarrow> 'a set option nres" where
  "Picard_step_ivl X0 t0 h X = do {
    ASSERT (0 \<le> h);
    ASSERT (wd TYPE('a));
    let H = lv_ivl [0] [h];
    let env = concat ` listset [list_of_eucl ` set_of_sappr X0, H, list_of_eucl ` set_of_sappr X];
    env \<leftarrow> approx_slp_spec (euler_incr_fas' D) D euler_incr_slp env;
    (case env of
      Some env \<Rightarrow>
        do {
          (l, u) \<leftarrow> ivl_rep_of_set ((eucl_of_list ` env::'a set));
          ASSERT (l \<le> u);
          r \<leftarrow> mk_safe ({l .. u}:::appr_rel);
          RETURN (Some (r:::sappr_rel))
        }
    | None \<Rightarrow> RETURN None)
  }"
sublocale autoref_op_pat_def Picard_step_ivl .

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

lemma lv_ivl_sings: "lv_ivl [x] [y] = (\<lambda>x. [x]) ` {x .. y}"
  apply (auto simp: lv_ivl_def)
  subgoal for x by (cases x) auto
  done

lemma Picard_step_ivl_refine[le, refine_vcg]:
  assumes eis: "euler_incr_slp_eq euler_incr_slp D"
  assumes [refine_vcg]: "wd TYPE('a::executable_euclidean_space)"
  assumes "(X::'a set) \<subseteq> Csafe"
  assumes "0 \<le> h"
  shows "Picard_step_ivl X0 t0 h X \<le> Picard_step X0 t0 h X"
proof -
  have "h' \<in> {t0..t0 + h} \<Longrightarrow> t0 \<le> h'" for h' by simp
  then show ?thesis
    unfolding Picard_step_ivl_def Picard_step_def
    apply (refine_vcg, clarsimp_all simp del: atLeastAtMost_iff)
    subgoal using \<open>0 \<le> h\<close> by simp
    subgoal using eis by (auto simp: euler_incr_slp_eq_def)
    subgoal using eis by (auto simp: euler_incr_fas'_def)
    subgoal for XS l u
      apply (auto simp: lv_ivl_sings nonempty_interval
          simp del: atLeastAtMost_iff
          intro!: add_integral_ivl_bound)
      subgoal for x0 h' phi x h''
        apply (drule bspec, assumption)
        apply (drule bspec[where x="h'' - t0"], force)
      proof goal_cases
        case (1)
        have *: "map ((!) (list_of_eucl b)) [0..<DIM('a) - Suc 0] @ [b \<bullet> Basis_list ! (DIM('a) - Suc 0)]
          = list_of_eucl b" for b::'a
          apply (auto intro!: nth_equalityI simp: nth_append not_less)
          using Intersection.le_less_Suc_eq by blast
        have "phi x \<in> X" if "x \<in> {t0 .. h''}" for x
          using 1 that by (auto simp: cfuncset_iff)
        have "x0 + (h'' - t0) *\<^sub>R ode b \<in> {l .. u}" if "b \<in> X" for b
        proof -
          from 1(16)[rule_format, OF that]
          have "einterpret (euler_incr_fas' D) (list_of_eucl x0 @ (h'' - t0) # list_of_eucl b) \<in> eucl_of_list ` XS"
            by auto
          also have "eucl_of_list ` XS \<subseteq> {l .. u}" by fact
          finally show ?thesis
            by (simp add: euler_incr_fas'_def einterpret_euler_incr_fas map_nth_append1 nth_append wdD[OF \<open>wd _\<close>] *)
        qed
        then have *: "(h'' - t0) *\<^sub>R ode b \<in> {l - x0..u - x0}" if "b \<in> X" for b using that
          by (auto simp: algebra_simps)
        show ?case
          apply (rule *)
          using 1 by (auto simp: cfuncset_iff)
      qed
      subgoal
        using assms(3)
        by (auto intro!: integrable_continuous_real continuous_intros
            simp: cfuncset_iff)
      done
    done
qed

schematic_goal Picard_step_ivl_impl:
  fixes h::real
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(X0i,X0)\<in>sappr_rel" "(hi, h) \<in> rnv_rel" "(t0i, t0) \<in> rnv_rel" "(PHIi,PHI)\<in>sappr_rel"
  notes [autoref_rules] = autoref_parameters
  shows "(?f::?'r, Picard_step_ivl $ X0 $ t0 $ h $ PHI::'a set option nres) \<in> ?R"
  unfolding autoref_tag_defs
  unfolding Picard_step_ivl_def
  including art
  by (autoref_monadic)
concrete_definition Picard_step_ivl_impl for X0i t0i hi PHIi uses Picard_step_ivl_impl
lemmas [autoref_rules] = Picard_step_ivl_impl.refine


subsubsection \<open>Picard iteration\<close>

primrec P_iter::"'a::executable_euclidean_space set \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> ('a) set \<Rightarrow> ('a) set option nres" where
  "P_iter X0 h 0 X = do {
    let _ = trace_set (ST ''P_iter failed (0)'') (Some (set_of_sappr X));
    RETURN None
  }"
| "P_iter X0 h (Suc i) X = do {
    ASSERT (0 \<le> h);
    (l, u) \<leftarrow> ivl_rep_of_set (set_of_sappr X);
    ASSERT (l \<le> u);
    ivl \<leftarrow> mk_safe ({l .. u}:::appr_rel);
    X' \<leftarrow> Picard_step_ivl X0 0 h ivl;
    (case X' of
      Some X' \<Rightarrow> do {
        (l', u') \<leftarrow> ivl_rep_of_set (set_of_sappr X');
        let l' = inf l' l - (if i mod (widening_mod optns) = 0 then abs (l' - l) else 0);
        let u' = sup u' u + (if i mod widening_mod optns = 0 then abs (u' - u) else 0);
        ASSERT (l' \<le> u');
        ivl' \<leftarrow> mk_safe {l' .. u'};
        if (l \<le> l' \<and> u' \<le> u) then RETURN (Some ivl)
        else P_iter X0 h i ivl'
      }
    | None \<Rightarrow> do {
        let _ = trace_set (ST ''P_iter failed (Picard_step)'') (Some (set_of_sappr X));
        RETURN None
      }
    )
  }"
sublocale autoref_op_pat_def P_iter .

lemma [autoref_rules]:
  "(abs, abs:: 'a \<Rightarrow> 'a::executable_euclidean_space) \<in> rnv_rel \<rightarrow> rnv_rel"
  by simp_all

lemma inf_le_supI[simp]:
  fixes a b c d::"'d::ordered_euclidean_space"
  shows
    "a \<le> c \<Longrightarrow> inf a b \<le> sup c d"
    "a \<le> d \<Longrightarrow> inf a b \<le> sup c d"
    "b \<le> c \<Longrightarrow> inf a b \<le> sup c d"
    "b \<le> d \<Longrightarrow> inf a b \<le> sup c d"
  by (auto simp: eucl_le[where 'a='d] eucl_inf[where 'a='d] eucl_sup[where 'a='d] inf_real_def sup_real_def
    intro!: sum_mono scaleR_right_mono)

schematic_goal P_iter_impl:
  fixes h::real and i::nat
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(X0i,X0)\<in>sappr_rel" "(PHIi,PHI)\<in>sappr_rel"
    "(hi, h) \<in> Id" "(i_i, i) \<in> Id"
  notes [autoref_rules] = autoref_parameters
  shows "(nres_of (?f::?'r dres), P_iter $ X0 $ h $ i $ PHI::'a set option nres) \<in> ?R"
  unfolding P_iter_def uncurry_rec_nat APP_def
  including art
  by (autoref_monadic)

concrete_definition P_iter_impl for X0i hi i_i PHIi uses P_iter_impl
lemmas [autoref_rules] = P_iter_impl.refine

lemma P_iter_spec[le, refine_vcg]:
  assumes "PHI \<subseteq> Csafe"
  assumes "0 \<le> h"
  assumes [refine_vcg]: "euler_incr_slp_eq euler_incr_slp D" "wd TYPE('a::executable_euclidean_space)"
  shows "P_iter X0 h i PHI \<le>
    SPEC (\<lambda>r. case r of
        None \<Rightarrow> True
      | Some (PHI'::'a set) \<Rightarrow> nonempty PHI' \<and> compact PHI' \<and> (\<exists>PHI'' \<subseteq> PHI'. RETURN (Some PHI'') \<le> Picard_step X0 0 h PHI'))"
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
      apply (simp add: nonempty_interval Picard_step_def)
      apply (safe intro!: exI[where x="{l .. u}"] compact_interval)
      subgoal by (auto simp: nonempty_interval)
      apply (rule set_mp[of CX' "{l .. u}"])
      subgoal
        apply (rule order_trans, assumption)
        unfolding atLeastatMost_subset_iff
        apply (rule disjI2)
        apply (rule conjI)
        subgoal
          apply (rule order_trans[where y="inf l' l - (if i mod widening_mod optns = 0 then \<bar>l' - l\<bar> else 0)"])
          by (simp_all split: if_split_asm add: algebra_simps add_increasing2)
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

context fixes m::"('a::executable_euclidean_space set \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a set \<Rightarrow> ('a set \<times> 'c) option nres)"
begin

primrec cert_stepsize::
  "'a set \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (real \<times> 'a set \<times> 'a set \<times> 'c) nres"
where
  "cert_stepsize X0 h n 0 = do { let _ = trace_set (ST ''cert_stepsize failed'') (Some (X0)); SUCCEED}"
| "cert_stepsize X0 h n (Suc i) = do {
    (l, u) \<leftarrow> ivl_rep_of_set (set_of_sappr X0);
    ASSERT (0 \<le> h);
    ASSERT (l \<le> u);
    ivl \<leftarrow> mk_safe {l .. u};
    ASSERT (ivl \<noteq> {});
    X' \<leftarrow> P_iter X0 h n ivl;
    case X' of Some X' \<Rightarrow>
      do {
        r1 \<leftarrow> m X0 h h X';
        r2 \<leftarrow> m X0 0 h X';
        (case (r1, r2) of
          (Some (res, err), Some (res_ivl, _)) \<Rightarrow>
            do {
              ASSUME (res \<subseteq> Csafe);
              ASSUME (res_ivl \<subseteq> Csafe);
              RETURN (h, res, res_ivl, err)
            }
        | _ \<Rightarrow>
            do {
              let _ = trace_set (ST ''cert_stepsize method failed'') (Some (set_of_sappr X'));
              cert_stepsize X0 (h / 2) n i
            }
       )
      }
    | None \<Rightarrow> cert_stepsize X0 (h / 2) n i
    }"
end
sublocale autoref_op_pat_def cert_stepsize .

schematic_goal cert_stepsize_impl_nres:
  fixes h::real and i n::nat
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]:
    "(mi, m)\<in>(sappr_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel \<rightarrow> sappr_rel \<rightarrow> \<langle>\<langle>sappr_rel \<times>\<^sub>r R\<rangle> option_rel\<rangle>nres_rel)"
    "(X0i,X0)\<in>sappr_rel" "(hi, h) \<in> rnv_rel" "(ni, n) \<in> nat_rel" "(i_i, i) \<in> nat_rel"
  shows "(?f::?'r nres, cert_stepsize $ m $ (X0::'a set) $ h $ n $ i) \<in> ?R"
  unfolding cert_stepsize_def uncurry_rec_nat autoref_tag_defs
  including art
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

definition "one_step_method m \<longleftrightarrow> (\<forall>X0 CX hl hu. m X0 hl hu CX \<le>
    SPEC (\<lambda>r. case r of None \<Rightarrow> True | Some (res, err) \<Rightarrow> nonempty res \<and>
      (\<forall>x0 \<in> X0. \<forall>h \<in> {hl .. hu}. x0 \<in> Csafe \<longrightarrow> h \<ge> 0 \<longrightarrow> h \<in> existence_ivl0 x0 \<longrightarrow>
      (\<forall>h' \<in> {0 .. h}. flow0 x0 h' \<in> CX) \<longrightarrow> x0 + h *\<^sub>R ode x0 \<in> CX \<longrightarrow> flow0 x0 h \<in> res)))"

lemmas one_step_methodD = one_step_method_def[THEN iffD1, rule_format, le]
lemmas one_step_methodI = one_step_method_def[THEN iffD2, rule_format]

lemma cert_stepsize_spec[le,refine_vcg]:
  assumes "h > 0"
  assumes "one_step_method m"
  assumes [refine_vcg]: "euler_incr_slp_eq euler_incr_slp D" "wd TYPE('a::executable_euclidean_space)"
  shows "cert_stepsize m X0 h i n \<le> SPEC (\<lambda>(h', RES::'a set, RES_ivl, _). nonempty RES \<and> nonempty RES_ivl \<and> 0 < h' \<and> h' \<le> h \<and> flowpipe0 X0 h' h' RES_ivl RES)"
  using assms(1)[unfolded autoref_tag_defs]
proof (induction n arbitrary: h)
  case 0 then show ?case by simp
next
  case (Suc n)
  note [refine_vcg] = Suc.IH[of "h/2", le]
  show ?case
    unfolding cert_stepsize.simps
    using Suc.prems
    apply (refine_vcg Ball_cfuncset_continuous_on one_step_methodD[OF assms(2)])
     apply (clarsimp_all)
    subgoal premises prems for l u PHI' RES RES_ivl PHI''
    proof -
      from prems
      have Ps: "RETURN (Some PHI'') \<le> Picard_step X0 0 h PHI'"
        by simp
      from Ps have PHI':
        "compact PHI''" "PHI'' \<subseteq> Csafe"
        "\<forall>x\<in>PHI''. x \<in> Csafe"
        "\<And>x0 h'' phi. x0 \<in> X0 \<Longrightarrow> 0 \<le> h'' \<Longrightarrow> h'' \<le> h \<Longrightarrow> phi \<in> cfuncset 0 h'' PHI' \<Longrightarrow>
        x0 + integral {0..h''} (\<lambda>t. ode (phi t)) \<in> PHI''"
        by (auto simp: Picard_step_def)
      then obtain cx where cx: "(\<lambda>t::real. cx) \<in> cfuncset 0 0 PHI'"
        using \<open>PHI'' \<subseteq> PHI'\<close> \<open>nonempty PHI'\<close> by (auto simp: cfuncset_def continuous_on_const nonempty_def)
      show "flowpipe0 X0 h h RES_ivl RES"
        unfolding flowpipe0_def atLeastAtMost_singleton
      proof safe
        show "0 \<le> h" using \<open>0 < h\<close> by simp
        show safe_X0: "x \<in> Csafe" if "x \<in> X0" for x using that \<open>{l..u} \<subseteq> Csafe\<close> \<open>X0 \<subseteq> {l..u}\<close> by blast
        show "x \<in> Csafe" if "x \<in> RES_ivl" for x using prems that by (auto simp:)
        show "x \<in> Csafe" if "x \<in> RES" for x using prems that by (auto simp:)
        fix x0 assume "x0 \<in> X0"
        from PHI'(4)[OF \<open>x0 \<in> X0\<close> order_refl \<open>0 \<le> h\<close> cx]
        have "x0 \<in> PHI''" by simp
        have *: "h \<in> existence_ivl0 x0" "s \<in> {0 .. h} \<Longrightarrow> flow0 x0 s \<in> PHI''" for s
          using \<open>x0 \<in> X0\<close> \<open>PHI'' \<subseteq> PHI'\<close> \<open>0 \<le> h\<close> PHI'(3) \<open>x0 \<in> PHI''\<close>
          by (auto
              simp: cfuncset_def Pi_iff closed_segment_eq_real_ivl ivl_integral_def
              intro!: Picard_iterate_mem_existence_ivlI[OF UNIV_I _ UNIV_I \<open>compact PHI''\<close>
                \<open>x0 \<in> PHI''\<close> \<open>PHI'' \<subseteq> Csafe\<close>] PHI'(4)) force+
        show h_ex: "h \<in> existence_ivl0 x0" by fact
        have cf: "(\<lambda>t::real. x0) \<in> cfuncset 0 h PHI'" for h
          using \<open>x0 \<in> PHI''\<close> \<open>PHI'' \<subseteq> PHI'\<close>
          by (auto simp: cfuncset_def continuous_intros)
        have mem_PHI': "x0 + h' *\<^sub>R ode x0 \<in> PHI'" if "0 \<le> h'" "h' \<le> h" for h'
          using that \<open>PHI'' \<subseteq> PHI'\<close> PHI'(4)[OF \<open>x0 \<in> X0\<close> that cf]
          by auto
        from this prems safe_X0
        show "flow0 x0 h \<in> RES"
          using \<open>0 \<le> h\<close> h_ex * \<open>PHI'' \<subseteq> PHI'\<close> \<open>x0 \<in> X0\<close>
          by (auto simp: subset_iff dest!: bspec[where x=x0])
        fix h' assume h': "h' \<in> {0..h}"
        then have "h' \<in> existence_ivl0 x0"
          by (meson atLeastAtMost_iff existence_ivl_zero h_ex is_interval_1
              local.is_interval_existence_ivl local.mem_existence_ivl_iv_defined(2))
        from h' this prems safe_X0
        show "flow0 x0 h' \<in> RES_ivl"
          using \<open>0 < h\<close> h_ex * \<open>PHI'' \<subseteq> PHI'\<close> \<open>x0 \<in> X0\<close> mem_PHI' \<open>x0 \<in> PHI''\<close>
          by (auto simp: subset_iff dest!: bspec[where x=x0])
      qed
    qed
    done
qed


subsubsection \<open>Euler step\<close>

definition "one_step X0 h m = do {
  CHECKs ''one_step nonneg'' (0 < h);
  (h, res, res_ivl, err) \<leftarrow> cert_stepsize m X0 h (iterations optns) (halve_stepsizes optns);
  ASSERT (0 < h);
  RETURN (h, err, res_ivl, res)
  }"
sublocale autoref_op_pat_def one_step .

definition "euler_step X0 h = one_step X0 h (\<lambda>X0 hl hu CX.
   do {
    let H = lv_ivl [min hl hu] [max hl hu];
    ASSUME (CX \<subseteq> Csafe);
    let env = concat ` listset [list_of_eucl ` set_of_sappr X0, list_of_eucl ` set_of_sappr CX, H];
    env \<leftarrow> approx_slp_spec (euler_fas' D) (2 * D) euler_slp env;
    case env of None \<Rightarrow> RETURN None
    | Some env \<Rightarrow> do {
      let res' = take D ` env;
      ASSERT (env_len res' D);
      let res = (eucl_of_list ` res');
      ASSUME (ncc res);
      let err' = drop D ` take (D * 2) ` env;
      ASSERT (env_len err' D);
      let err = (eucl_of_list ` err'::'a::executable_euclidean_space set);
      res \<leftarrow> reduce_spec (reduce optns) res;
      ASSUME (ncc res);
      s \<leftarrow> safe_set res;
      if s then
      do {
        res \<leftarrow> mk_safe res;
        RETURN (Some (res::'a set, err))
      } else RETURN None
    }
  })"
sublocale autoref_op_pat_def euler_step .

lemma simpi:
  assumes "X0 < length (xs)"
  shows "(let ys = xs @ [a] in ys @ [b [ys ! X0]]) = xs @ [a, b [xs ! X0]]"
  using assms
  by (auto simp: nth_append_cond)

lemma embed_real_ivl_iff[simp]:
   "(\<forall>x \<in> {0 .. h *\<^sub>R (One::'a::executable_euclidean_space)}. P (x \<bullet> hd Basis_list)) \<longleftrightarrow> (\<forall>x \<in> {0 .. h}. P x)"
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
  assumes [THEN one_step_methodD, refine_vcg]: "one_step_method m"
  assumes [refine_vcg]: "euler_incr_slp_eq euler_incr_slp D" "wd TYPE('a::executable_euclidean_space)"
  shows "one_step X0 h m \<le> SPEC (\<lambda>(h', _, RES_ivl, RES::'a set). 0 < h' \<and> h' \<le> h \<and> flowpipe0 X0 h' h' RES_ivl RES)"
  using assms
  unfolding one_step_def
  by refine_vcg

lemma ncc_imageD:
  assumes "ncc ((\<lambda>x. x ! i) ` env)"
  assumes "nth_image_precond env i"
  shows "compact ((\<lambda>x. x ! i) ` env::real set)" "closed ((\<lambda>x. x ! i) ` env)" "bounded ((\<lambda>x. x ! i) ` env)"
    "((\<lambda>x. x ! i) ` env) \<noteq> {}" "convex ((\<lambda>x. x ! i) ` env)"
  using assms
  by (auto simp: ncc_def nth_image_precond_def compact_eq_bounded_closed)

lemma max_Var_floatariths_ode_d_fa[le]:
  assumes [simp]: "length ode_e > 0" "max_Var_floatariths ode_e \<le> length ode_e"
    "length cxs = length ode_e" "length ys = length ode_e"
  shows "max_Var_floatariths (ode_d_fa i cxs ys) \<le> max (max_Var_floatariths (cxs)) (max_Var_floatariths ys)"
  apply (auto simp: ode_d_fa_def max_Var_floatariths_Max )
  using assms apply auto[1]
  apply (auto intro!: max_Var_floatarith_subst_floatarith_le max_Var_floatariths_ode_d_expr
      max_Var_floatarith_le_max_Var_floatariths_nthI max_Var_ode_fa
      simp: in_set_conv_nth)
   apply (auto simp: max_Var_floatariths_Max in_set_conv_nth)
  done

lemma max_Var_floatariths_euler_err_fas[le]:
  assumes nz: "0 < length ode_e"
    and [simp]: "max_Var_floatariths ode_e \<le> length ode_e"
    "length xs = length ode_e"
    "length cxs = length ode_e"
  shows "max_Var_floatariths (euler_err_fas xs h cxs)
    \<le> max (max_Var_floatariths xs) (max (max_Var_floatarith h) (max_Var_floatariths cxs))"
  using nz
  by (auto simp: euler_err_fas_def[abs_def] euler_err_fas_nth_def[abs_def] map_nth_eq_self simp del: length_0_conv
      intro!: max_Var_floatariths_ode_d_fa max_Var_floatariths_map_times
        max_Var_floatariths_map_const max_Var_ode_fa; arith)

lemma max_Var_floatariths_euler_incr_fas[le]:
  assumes [simp]: "max_Var_floatariths ode_e \<le> length ode_e"
    "length xs = length ode_e"
    "length cxs = length ode_e"
  shows "max_Var_floatariths (euler_incr_fas xs h cxs)
    \<le> max (max_Var_floatariths xs) (max (max_Var_floatarith h) (max_Var_floatariths cxs))"
  using length_ode_fa
  by (auto simp: euler_incr_fas_def euler_incr_fas_nth_def[abs_def] simp del: length_ode_fa
      intro!: max_Var_floatariths_ode_d_fa max_Var_floatariths_map_plus max_Var_floatariths_map_times
      max_Var_floatariths_map_const max_Var_ode_fa)

lemma map_euler_incr_fas_nth: "length X0 = d \<Longrightarrow> map (euler_incr_fas_nth X0 h CX) [0..<d] = euler_incr_fas X0 h CX"
  by (auto simp: euler_incr_fas_def)

lemma map_euler_err_fas_nth: "length X0 = d \<Longrightarrow> map (euler_err_fas_nth X0 h CX) [0..<d] = euler_err_fas X0 h CX"
  by (auto simp: euler_err_fas_def)

lemma max_Var_floatariths_euler_fas[le]:
  assumes [simp]: "max_Var_floatariths ode_e \<le> length ode_e"
    "length xs = length ode_e"
    "length cxs = length ode_e"
  assumes nz: "0 < length ode_e"
  shows "max_Var_floatariths (euler_fas xs h cxs) \<le> Max {max_Var_floatariths xs, max_Var_floatarith h, max_Var_floatariths cxs}"
  using nz
  by (auto simp: euler_fas_def map_euler_incr_fas_nth map_euler_err_fas_nth
      intro!: max_Var_floatariths_map_plus max_Var_floatariths_euler_incr_fas
        max_Var_floatariths_euler_err_fas)

lemma take_interpret_floatariths:
  "d < length fas \<Longrightarrow> take d (interpret_floatariths fas vs) = interpret_floatariths (take d fas) vs"
  by (auto intro!: nth_equalityI)

lemma length_euler_slp_le: "euler_slp_eq euler_slp D \<Longrightarrow> 2 * D \<le> length euler_slp"
  by (auto simp: euler_slp_eq_def euler_fas'_def intro!: order_trans[OF _ length_slp_of_fas_le])

lemma ncc_nonempty[simp]: "ncc x \<Longrightarrow> nonempty x"
  by (simp add: ncc_def nonempty_def)

lemma nccD:
  assumes "ncc X"
  shows "compact X" "closed X" "bounded X" "X \<noteq> {}" "convex X"
  using assms
  by (auto simp: ncc_def nth_image_precond_def compact_eq_bounded_closed)

lemma euler_step_flowpipe:
  assumes [refine_vcg]: "euler_incr_slp_eq euler_incr_slp D" "euler_slp_eq euler_slp D"
      "wd TYPE('a::executable_euclidean_space)"
  shows "euler_step X0 h \<le> SPEC (\<lambda>(h', _, RES_ivl, RES::'a set). 0 < h' \<and> h' \<le> h \<and> flowpipe0 X0 h' h' RES_ivl RES)"
  unfolding euler_step_def THE_NRES_def
  apply (intro SPEC_rule_conjI one_step_flowpipe one_step_methodI)
    apply (refine_vcg, clarsimp_all)
  subgoal using assms(2) by (auto simp: euler_slp_eq_def euler_fas'_def)
  subgoal by (auto simp: euler_slp_eq_def euler_fas'_def)
  subgoal using length_euler_slp_le assms by (auto simp: env_len_def wdD[OF \<open>wd _\<close>])
  subgoal using length_euler_slp_le assms by (auto simp: env_len_def wdD[OF \<open>wd _\<close>])
proof (goal_cases)
  case hyps: (1 X0 CX hl hu env res b x0 enve h)
  then interpret derivative_on_prod "{0 .. h}" CX "\<lambda>_. ode" "\<lambda>(t, x). ode_d1 x o\<^sub>L snd_blinfun"
    by unfold_locales (auto intro!: continuous_intros derivative_eq_intros
        simp: split_beta' subset_iff  wdD[OF \<open>wd _\<close>])
  from \<open>h \<in> existence_ivl0 x0\<close> have s_ex: "s \<in> existence_ivl0 x0" if "0 \<le> s" "s \<le> h" for s
    by (metis (no_types, lifting) atLeastAtMost_iff ivl_subset_existence_ivl subset_iff that)
  have "flow0 x0 (h) = flow0 x0 (0 + (h))" by simp
  also have "\<dots> \<in> eucl_of_list ` take D ` env"
    using hyps
    apply (intro euler_consistent_traj_set[where x="flow0 x0" and u = "h"])
            apply (auto intro!: \<open>0 \<le> h\<close> flow_has_vector_derivative[THEN has_vector_derivative_at_within]
        simp: nccD discrete_evolution_def euler_increment subset_iff wdD[OF \<open>wd _\<close>]
          Let_def s_ex min_def max_def lv_ivl_sings)
    subgoal premises prems for s
    proof -
      have "interpret_floatariths (euler_fas' DIM('a)) (list_of_eucl x0 @ list_of_eucl (flow0 x0 s) @ [h]) \<in> env"
        using prems
        by (auto intro!: prems(1)[rule_format])
      then have "eucl_of_list (take D (interpret_floatariths (euler_fas' DIM('a)) (list_of_eucl x0 @ list_of_eucl (flow0 x0 s) @ [h])))
        \<in> eucl_of_list ` take D ` env"
        (is "eucl_of_list (take _ (interpret_floatariths  _ ?vs)) \<in> _")
        by auto
      also
      have "take (2 * D) (interpret_floatariths (euler_fas' DIM('a)) ?vs) =
        interpret_floatariths (map fold_const_fa (euler_fas (map floatarith.Var [0..<D]) (Var (2 * D)) (map floatarith.Var [D..<2 * D]))) ?vs"
        unfolding euler_slp_eqD[OF assms(2)] euler_fas'_def
        by (auto simp: euler_fas_def wdD[OF \<open>wd _\<close>] simp del: map_map
            intro!: max_Var_floatariths_map_plus max_Var_floatariths_euler_incr_fas
              max_Var_floatariths_euler_err_fas \<open>wd _\<close>
              max_Var_floatariths_fold_const_fa[le])
      then have "take D (take (2 * D) (interpret_floatariths (euler_fas' DIM('a)) ?vs)) =
        take D (interpret_floatariths (euler_fas  (map floatarith.Var [0..<D]) (Var(2 * D)) (map floatarith.Var [D..<2 * D])) ?vs)"
        by simp
      then have "take D (interpret_floatariths (euler_fas' DIM('a)) ?vs) =
        take DIM('a) (interpret_floatariths (euler_fas  (map floatarith.Var [0..<D]) (Var(2 * D)) (map floatarith.Var [D..<2 * D])) ?vs)"
        by (simp add: wdD[OF \<open>wd _\<close>])
      also have "eucl_of_list \<dots> =
          x0 + h *\<^sub>R ode x0 + (h\<^sup>2 / 2) *\<^sub>R (ode_d 0 (flow0 x0 s) (ode (flow0 x0 s))) (ode (flow0 x0 s))"
        by (auto simp: take_interpret_floatariths einterpret_euler_fas1 map_nth_append1 prems nth_append
            wdD[OF \<open>wd _\<close>])
      finally show ?thesis
        by (simp add: prems(10) prems(13) prems(14) prems(5) ode_d1_eq[symmetric] wdD[OF \<open>wd _\<close>])
    qed
    done
  also have "\<dots> \<subseteq> res" using hyps by auto
  finally show ?case by simp
qed (auto simp: assms)

definition "ncc_precond TYPE('a::executable_euclidean_space) \<longleftrightarrow> (\<forall>(Xi, X::'a set) \<in> appr_rel. ncc X)"

lemma ncc_precondD:
  assumes "ncc_precond TYPE('a::executable_euclidean_space)"
  shows "(Xi, X::'a set) \<in> sappr_rel \<Longrightarrow> ncc X" "(Xi, X::'a set) \<in> appr_rel \<Longrightarrow> ncc X"
  using assms
  by (auto simp: ncc_precond_def split_beta' sappr_rel_br br_def appr_rel_br
      dest!: bspec[where x="(Xi, X)"])

schematic_goal euler_step_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes ncc: "ncc_precond TYPE('a::executable_euclidean_space)"
  notes [simp] = ncc_precondD[OF ncc]
  assumes [autoref_rules]: "(Xi, X) \<in> sappr_rel" "(hi, h) \<in> Id"
  notes [autoref_rules] = autoref_parameters
  shows "(nres_of (?f::?'r dres), euler_step $ (X::'a set) $ h) \<in> ?R"
  unfolding one_step_def euler_step_def[abs_def]
  by autoref_monadic

concrete_definition euler_step_impl for Xi hi uses euler_step_impl
lemmas [autoref_rules] = euler_step_impl.refine

definition "rk2_step X0 h = one_step X0 h (\<lambda>X0 hl hu CX.
  do {
    let H = lv_ivl [min hl hu] [max hl hu];
    let rkp = lv_ivl [rk2_param optns] [rk2_param optns];
    let s2 = lv_ivl [0] [1];
    ASSUME (CX \<subseteq> Csafe);
    ASSUME (ncc CX);
    let env = concat ` listset [list_of_eucl ` set_of_sappr X0, list_of_eucl ` set_of_sappr CX, rkp, H, s2];
    env \<leftarrow> approx_slp_spec (rk2_fas' D) (2 * D) rk2_slp env;
    case env of None \<Rightarrow> RETURN None
    | Some env \<Rightarrow> do {
      let res' = take D ` env;
      ASSERT (env_len res' D);
      let res = (eucl_of_list ` res'::'a::executable_euclidean_space set);
      ASSUME (ncc res);
      let err' = drop D ` take (D * 2) ` env;
      ASSERT (env_len err' D);
      let err = (eucl_of_list ` err'::'a set);
      res \<leftarrow> reduce_spec (reduce optns) res;
      ASSUME (ncc res);
      s \<leftarrow> safe_set res;
      if s then
      do {
        res \<leftarrow> mk_safe res;
        RETURN (Some (res, err))
      } else RETURN None
    }
  })"
sublocale autoref_op_pat_def rk2_step .

lemma length_rk2_slp_le: "rk2_slp_eq rk2_slp D \<Longrightarrow> 2 * D \<le> length rk2_slp"
  by (auto simp: rk2_slp_eq_def rk2_fas'_def intro!: order_trans[OF _ length_slp_of_fas_le])

lemma max_Var_floatarith_R\<^sub>e[simp]: "max_Var_floatarith (R\<^sub>e x) = 0"
  by (auto simp: R\<^sub>e_def split: prod.splits)

lemma max_Var_floatariths_rk2_fas_err[le]:
  assumes nz: "0 < length ode_e"
    and [simp]: "max_Var_floatariths ode_e \<le> length ode_e" "length x0 = length ode_e" "length cx = length ode_e"
  shows "max_Var_floatariths (rk2_fas_err rkp x0 h cx s2) \<le>
    Max {max_Var_floatarith rkp, max_Var_floatariths x0, max_Var_floatarith h, max_Var_floatariths cx,
      max_Var_floatarith s2}"
  using nz
  unfolding rk2_fas_err_def rk2_fas_err_nth_def
  by (auto simp: rk2_fas_err_def
      intro!: max_Var_floatariths_append max_Var_floatariths_map_plus max_Var_floatariths_map_times
        max_Var_floatariths_map_const max_Var_ode_fa max_Var_floatariths_euler_incr_fas
        max_Var_floatariths_ode_d_fa; arith)

lemma max_Var_floatarith_one[simp]: "max_Var_floatarith 1 = 0"
  and max_Var_floatarith_zero[simp]: "max_Var_floatarith 0 = 0"
  by (auto simp: one_floatarith_def zero_floatarith_def)

lemma max_Var_floatariths_rk2_fas[le]:
  assumes nz: "0 < length ode_e"
    and [simp]: "max_Var_floatariths ode_e \<le> length ode_e" "length x0 = length ode_e" "length cx = length ode_e"
  shows "max_Var_floatariths (rk2_fas rkp x0 h cx s2) \<le>
    Max {max_Var_floatarith rkp, max_Var_floatariths x0, max_Var_floatarith h, max_Var_floatariths cx,
      max_Var_floatarith s2}"
  using nz
  by (auto simp: rk2_fas_def
      intro!: max_Var_floatariths_append max_Var_floatariths_map_plus max_Var_floatariths_map_times
        max_Var_floatariths_map_const max_Var_ode_fa max_Var_floatariths_euler_incr_fas
        max_Var_floatariths_rk2_fas_err)

lemma rk2_step_flowpipe:
  assumes "0 < rk2_param optns"
  assumes "rk2_param optns \<le> 1"
  assumes rs: "rk2_slp_eq rk2_slp D"
    and [refine_vcg]: "euler_incr_slp_eq euler_incr_slp D" "wd TYPE('a::executable_euclidean_space)"
  shows "rk2_step X0 h \<le> SPEC (\<lambda>(h', _, RES_ivl, RES::'a set). 0 < h' \<and> h' \<le> h \<and> flowpipe0 X0 h' h' RES_ivl RES)"
  unfolding rk2_step_def THE_NRES_def
  apply (intro one_step_flowpipe assms one_step_methodI)
  apply (refine_vcg, clarsimp_all)
  subgoal using rs by (auto simp: rk2_slp_eq_def rk2_fas'_def)
  subgoal by (auto simp: rk2_slp_eq_def rk2_fas'_def)
  subgoal using length_rk2_slp_le rs by (auto simp: env_len_def wdD[OF \<open>wd _\<close>])
  subgoal using length_rk2_slp_le rs by (auto simp: env_len_def wdD[OF \<open>wd _\<close>])
proof (goal_cases)
  case hyps: (1 X0 CX hl hu env res b x0 el h)
  have aux: "ode (flow0 x0 s) = ode (snd (s, flow0 x0 s))" for s
    by simp
  from hyps interpret derivative_on_prod "{0 .. h}" CX "\<lambda>_ x. ode x" "\<lambda>(t, x). ode_d1 x o\<^sub>L snd_blinfun"
    by unfold_locales
      (auto intro!: continuous_intros derivative_eq_intros simp: split_beta' subset_iff)

  have aux2: "blinfun_apply (ode_d1 (snd tx)) \<circ> snd = blinfun_apply (ode_d1 (snd tx) o\<^sub>L snd_blinfun)"
    for tx::"real\<times>'a"
    by (auto intro!: blinfun_eqI)

  have aux3: "blinfun_apply (ode_d2 (snd tx)) (snd h) o\<^sub>L snd_blinfun =
    (flip_blinfun (flip_blinfun (ode_d2 (snd tx) o\<^sub>L snd_blinfun) o\<^sub>L snd_blinfun)) h"
    for tx h::"real\<times>'a"
    by (auto intro!: blinfun_eqI)


  have "flow0 x0 (h) = flow0 x0 (0 + (h))" by simp
  also have "\<dots> \<in> eucl_of_list ` take D ` env"
    using hyps assms
    apply (intro rk2_consistent_traj_set[where
      x="flow0 x0" and u = "h" and T="{0..h}" and X="CX" and p="rk2_param optns"
      and f = "ode_na" and f' = ode_d_na and g' = ode_d_na and f'' = ode_d2_na and g'' = ode_d2_na])
    subgoal by (simp add: \<open>0 \<le> h\<close>)
    subgoal by simp
    subgoal by simp
    subgoal by auto
    subgoal by (auto simp add: ncc_def nonempty_def)
    subgoal
      apply (rule flow_has_vector_derivative[THEN has_vector_derivative_at_within, THEN has_vector_derivative_eq_rhs])
      subgoal by (metis (no_types, lifting) ivl_subset_existence_ivl subset_iff)
      subgoal by (force simp: ode_na_def[abs_def] ode_d_na_def[abs_def] ode_d2_na_def[abs_def])
      done
    subgoal
      unfolding ode_na_def ode_d_na_def ode_d2_na_def
      apply (rule derivative_eq_intros)
        apply (rule derivative_intros)
        apply (rule derivative_intros)
      subgoal by (force simp: ncc_def nonempty_def)\<comment> \<open>unnecessarily slow\<close>
      subgoal by force
      done
    subgoal
      unfolding ode_na_def ode_d_na_def ode_d2_na_def
      apply (rule derivative_eq_intros)
        apply (rule derivative_intros)
         apply (rule derivative_intros)
         apply (rule derivative_intros)
      subgoal by (force simp: nonempty_def)
       apply (rule derivative_intros)
      subgoal by (auto intro!: aux3)
      done
    subgoal by (rule refl)
    subgoal by (rule refl)
    subgoal
      apply (rule compact_imp_bounded)
      apply (rule compact_continuous_image)
      subgoal
        by (auto intro!: continuous_intros simp: ode_na_def ode_d_na_def ode_d2_na_def)
      subgoal by (auto simp: ncc_def intro!: compact_Times)
      done
    subgoal by auto
    subgoal by simp
    subgoal by simp
    subgoal
      apply (rule convex_on_segmentI[where j=h])
      using mult_left_le_one_le[of h "rk2_param optns"]
      by (auto simp: ncc_def mult_left_le_one_le mult_le_one ac_simps ode_na_def
          ode_d_na_def ode_d2_na_def dest: bspec[where x=0])
    subgoal by (simp add: ncc_def)
    subgoal by (simp add: ncc_def compact_imp_closed)
    subgoal for s1 s2
      apply (clarsimp simp add: lv_ivl_sings)
      subgoal premises prems
      proof -
        have "s2 * rk2_param optns * h \<le> h"
          apply (rule mult_left_le_one_le)
          using assms prems
          by (auto intro!: mult_le_one)
        then have s2: "(s2 * h * rk2_param optns) \<in> {0 .. h}"
          using prems assms by (auto simp: ac_simps)
        have s1: "h * s1 \<in> {0 .. h}" using prems
          by (auto intro!: mult_right_le_one_le)
        then have
          "interpret_floatariths (rk2_fas' D)
              (list_of_eucl x0 @ list_of_eucl (flow0 x0 (h * s1)) @ [rk2_param optns, h, s2]) \<in> env"
          apply (intro prems(15)[rule_format])
          using prems
          by auto
        then have "take (2 * D) (interpret_floatariths (rk2_fas' D)
              (list_of_eucl x0 @ list_of_eucl (flow0 x0 (h * s1)) @ [rk2_param optns, h, s2])) \<in> take (2 * D) ` env"
          (is "?l \<in> _")
          by auto
        also have "?l = interpret_floatariths
         (map fold_const_fa (rk2_fas (Var (2 * D)) (map floatarith.Var [0..<D]) (Var (2 * D + 1))
          (map floatarith.Var [D..<2 * D])
           (Var (2 * D + 2))))
         (list_of_eucl x0 @ list_of_eucl (flow0 x0 (h * s1)) @ [rk2_param optns, h, s2])"
          (is "_ = interpret_floatariths (map fold_const_fa ?fas) ?xs")
          unfolding rk2_slp_eqD[OF rs] rk2_fas'_def
          by (auto intro!: max_Var_floatariths_rk2_fas max_Var_floatariths_fold_const_fa[le] simp: wdD[OF \<open>wd _\<close>])
        finally have "take D (interpret_floatariths ?fas ?xs) \<in> take D ` take (2 * D) ` env"
          by auto
        also have "\<dots> = take D ` env" by (auto simp: image_image wdD[OF \<open>wd _\<close>])
        finally have "eucl_of_list (take D (interpret_floatariths ?fas ?xs)) \<in> eucl_of_list ` take D ` env"
          by simp
        then have "einterpret (take D ?fas) ?xs \<in> eucl_of_list ` take D ` env"
          by (simp add: take_interpret_floatariths wdD[OF \<open>wd _\<close>])
        also have "einterpret (take D ?fas) ?xs =
          discrete_evolution (rk2_increment (rk2_param optns) (\<lambda>t x. ode_na (t, x))) h 0 x0 +
          heun_remainder1 (flow0 x0) ode_na ode_d_na ode_d2_na 0 h s1 -
          heun_remainder2 (rk2_param optns) (flow0 x0) ode_na ode_d2_na 0 h s2"
          apply (simp add: wdD[OF \<open>wd _\<close>])
          apply (subst rk2_increment_rk2_fas1[where ?s1'.0 = s1])
          subgoal by (auto simp: nth_append map_nth_append1)
          subgoal by auto
          subgoal by auto
          subgoal by auto
          subgoal by (auto simp: nth_append map_nth_append1 \<open>x0 \<in> Csafe\<close>)
          subgoal
            apply (auto simp: nth_append map_nth_append1 \<open>x0 \<in> Csafe\<close>)
            by (meson connectedD_interval existence_ivl_zero flow0_defined hyps(16) hyps(17) hyps(18)
                mult_right_le_one_le mult_sign_intros(1) mvar.connected prems(28) prems(29))
          subgoal
          proof -
            have "x0 + ((rk2_param optns * s2) * h) *\<^sub>R ode x0 \<in> CX"
              by (rule convex_on_segmentI[where j=h])
                 (use prems in \<open>auto simp: ncc_def mult_left_le_one_le mult_le_one
                  dest: bspec[where x=0]\<close>)
            also note \<open>\<dots> \<subseteq> Csafe\<close>
            finally show ?thesis
              by (auto simp: nth_append map_nth_append1 \<open>x0 \<in> Csafe\<close> ac_simps)
          qed
          subgoal by (auto simp: nth_append map_nth_append1 ode_na_def)
          done
        finally show ?thesis by simp
      qed
      done
    done
  also have "\<dots> \<subseteq> res" using hyps(6) by auto
  finally show ?case by simp
qed

schematic_goal rk2_step_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(Xi, X) \<in> sappr_rel" "(hi, h) \<in> Id"
  assumes ncc: "ncc_precond TYPE('a::executable_euclidean_space)"
  notes [simp] = ncc_precondD[OF ncc]
  notes [autoref_rules] = autoref_parameters
  shows "(nres_of (?f::?'r dres), rk2_step $ (X::'a set) $ h) \<in> ?R"
  unfolding one_step_def rk2_step_def[abs_def]
  by (autoref_monadic)

concrete_definition rk2_step_impl for Xi hi uses rk2_step_impl
lemmas [autoref_rules] = rk2_step_impl.refine

definition "choose_step = (if method_id optns = 2 then rk2_step else euler_step)"
sublocale autoref_op_pat_def choose_step .

schematic_goal choose_step_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('a)"
  assumes [autoref_rules]: "(Xi, X) \<in> sappr_rel" "(hi, h) \<in> Id"
  shows "(nres_of (?f::?'r dres), choose_step $ (X::'a set) $ h) \<in> ?R"
  unfolding choose_step_def autoref_tag_defs if_distribR ncc_precond_def
  by (autoref_monadic)

concrete_definition choose_step_impl for Xi hi uses choose_step_impl
lemmas [autoref_rules] = choose_step_impl.refine

definition "wd_step TYPE('a::executable_euclidean_space) \<longleftrightarrow>
  0 < rk2_param optns \<and>
  rk2_param optns \<le> 1 \<and>
  ode_slp_eq ode_slp \<and>
  rk2_slp_eq rk2_slp D \<and>
  euler_slp_eq euler_slp D \<and>
  euler_incr_slp_eq euler_incr_slp D \<and>
  wd TYPE('a)"

lemmas wd_stepD = wd_step_def[THEN iffD1]

lemma choose_step_flowpipe[le, refine_vcg]:
  assumes "wd_step TYPE('a::executable_euclidean_space)"
  shows "choose_step X0 h \<le> SPEC (\<lambda>(h', _, RES_ivl, (RES::'a set)). 0 < h' \<and> h' \<le> h \<and> flowpipe0 X0 h' h' RES_ivl RES)"
  using wd_stepD[OF \<open>wd_step _\<close>]
  unfolding choose_step_def autoref_tag_defs
  by (split if_split) (safe intro!: rk2_step_flowpipe euler_step_flowpipe)

lemma wd_step_wdD:
  "wd_step TYPE('a::executable_euclidean_space) \<Longrightarrow> wd TYPE('a)"
  by (auto simp: wd_step_def)

definition "ode_e' = (ode_e @
  mmult_fa D D D (concat (map (\<lambda>j. map (\<lambda>i.
      (FDERIV_floatarith (ode_e ! j) [0..<D] (replicate D 0[i := 1]))) [0..<D]) [0..<D]))
    (map Var [D..<D + D*D]))"

end

definition blinfun_of_list :: "real list \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'a::executable_euclidean_space"
  where "blinfun_of_list xs = blinfun_of_matrix (\<lambda>i j. xs ! ((index Basis_list i) * DIM('a) + (index Basis_list j)))"

definition vec1_of_list :: "real list \<Rightarrow> 'n::{finite, one, plus} vec1"
  where "vec1_of_list xs =
    (vector (take CARD('n) xs), vector (map (\<lambda>i. vector (nths xs {CARD('n)*i..CARD('n)*Suc i})) [1..<Suc (CARD('n))]))"

definition flow1_of_vec1 :: "'n vec1 \<Rightarrow> ('n rvec * ('n rvec \<Rightarrow>\<^sub>L 'n::finite rvec))"
  where "flow1_of_vec1 xs = (fst xs, blinfun_of_vmatrix (snd xs))"

definition vec1_of_flow1 :: "('n::finite eucl1) \<Rightarrow> 'n vec1"
  where "vec1_of_flow1 xs = (fst xs, matrix (snd xs))"

lemma fst_flow1_of_vec1[simp]: "fst (flow1_of_vec1 x) = fst x"
  by (auto simp: flow1_of_vec1_def)

lemma fst_vec1_of_flow[simp]: "fst (vec1_of_flow1 x) = fst x"
  by (auto simp: vec1_of_flow1_def)

lemma isDERIV_simps[simp]:
  "isDERIV i 1 xs" "isDERIV i 0 xs"
  "isDERIV i (a + b) xs \<longleftrightarrow>  isDERIV i a xs \<and> isDERIV i b xs"
  "isDERIV i (a - b) xs \<longleftrightarrow> isDERIV i a xs \<and> isDERIV i b xs"
  "isDERIV i (a * b) xs \<longleftrightarrow> isDERIV i a xs \<and> isDERIV i b xs"
  "isDERIV i (a / b) xs \<longleftrightarrow> isDERIV i a xs \<and> isDERIV i b xs \<and> interpret_floatarith b xs \<noteq> 0"
  "isDERIV i (-a) xs = isDERIV i a xs"
  by (auto simp: one_floatarith_def zero_floatarith_def plus_floatarith_def minus_floatarith_def
      times_floatarith_def divide_floatarith_def uminus_floatarith_def)

abbreviation "float10_rel \<equiv> Id::(float10 \<times> float10) set"

locale approximate_sets_ode_slp' = approximate_sets_ode_slp\<comment> \<open>TODO: this prevents infinite chain of interpretations (?!)\<close>
  where ode_e = ode_e
    and safe_form = safe_form
    and optns = "optns::'b numeric_options"
    for ode_e safe_form optns
    +
  fixes ode_slp' euler_incr_slp' euler_slp' rk2_slp'::slp and
    solve_poincare_slp::"slp list"
begin

sublocale var: approximate_sets_ode_slp
  where ode_e = ode_e'
    and safe_form = safe_form
    and D = "D + D*D"
    and ode_slp = ode_slp'
    and euler_incr_slp = euler_incr_slp'
    and euler_slp = euler_slp'
    and rk2_slp = rk2_slp'
  by standard

lemma wd_imp_var_wd[refine_vcg, intro]: "wd (TYPE('n rvec)) \<Longrightarrow> var.wd (TYPE('n::enum vec1))"
  apply (auto simp: var.wd_def)
  unfolding ode_e'_def
  by (auto simp: wd_def length_concat o_def sum_list_distinct_conv_sum_set
      concat_map_map_index
      intro!: max_Var_floatariths_mmult_fa[le] max_Var_floatariths_mapI
      max_Var_floatarith_FDERIV_floatarith[le]
      max_Var_floatariths_fold_const_fa[le]
      max_Var_floatarith_le_max_Var_floatariths_nthI
      max_Var_floatariths_list_updateI max_Var_floatariths_replicateI)

lemma safe_eq:
  assumes "wd TYPE('n::enum rvec)"
  shows "var.Csafe = ((Csafe \<times> UNIV)::'n vec1 set)"
  using assms wd_imp_var_wd[OF assms]
  unfolding var.safe_def safe_def var.wd_def wd_def var.Csafe_def Csafe_def
  unfolding ode_e'_def
  apply (auto simp: )
  subgoal
    apply (subst interpret_form_max_Var_cong) prefer 2 apply assumption
    by (auto simp: nth_Basis_list_prod)
  subgoal for a b
    apply (drule isFDERIV_appendD1)
        apply simp apply simp apply (auto intro!: max_Var_floatariths_fold_const_fa[le])[]
    apply (rule isFDERIV_max_Var_congI, assumption)
    by (auto simp: nth_Basis_list_prod)
  subgoal
    apply (subst interpret_form_max_Var_cong) prefer 2 apply assumption
    by (auto simp: nth_Basis_list_prod)
  subgoal for a b
    apply (rule isFDERIV_appendI1)
    apply (rule isFDERIV_max_Var_congI, assumption)
        apply (auto simp: nth_Basis_list_prod)
     apply (auto simp: isFDERIV_def FDERIV_floatariths_def in_set_conv_nth isDERIV_inner_iff
      length_concat o_def sum_list_distinct_conv_sum_set concat_map_map_index
        intro!: isDERIV_FDERIV_floatarith isDERIV_mmult_fa_nth)
     apply (rule isDERIV_max_Var_floatarithI[where ys="list_of_eucl a"])
    subgoal for i j k
      apply (cases "i < CARD('n)")
      subgoal by auto
      subgoal apply (rule isDERIV_max_VarI)
         apply (rule max_Var_floatarith_le_max_Var_floatariths_nthI)
          apply force
         apply auto
        done
      done
    subgoal for i j k l by (auto dest!: max_Var_floatariths_lessI simp: nth_Basis_list_prod)
    subgoal by (auto simp: nth_list_update)
    done
  done

lemma CsafeI: "t \<in> existence_ivl0 x \<Longrightarrow> x \<in> Csafe"
  using local.mem_existence_ivl_iv_defined(2) by blast

lemma apply_vareq: "blinfun_apply (vareq x t) = ode_d1 (flow0 x t)"
  by (auto simp: vareq_def)

lemma Dflow_has_derivative:
  "t \<in> existence_ivl0 x \<Longrightarrow> (Dflow x has_derivative blinfun_scaleR_left (ode_d1 (flow0 x t) o\<^sub>L Dflow x t)) (at t)"
  by (auto simp: Dflow_def blinfun.bilinear_simps scaleR_blinfun_compose_left apply_vareq CsafeI
      intro!: derivative_eq_intros mvar.flow_has_derivative[THEN has_derivative_eq_rhs] ext
        blinfun_eqI)

lemma
  var_ode_eq:
  fixes x::"'n::enum vec1"
  assumes "wd TYPE('n rvec)" and [simp]: "(fst x) \<in> Csafe"
  shows "var.ode x = (ode (fst x), matrix (ode_d1 (fst x)) ** snd x)"
proof -
  have "interpret_floatariths ode_e (list_of_eucl x) =
    interpret_floatariths ode_e (list_of_eucl (fst x))"
    apply (rule interpret_floatariths_max_Var_cong)
    using wdD[OF \<open>wd _\<close>]
    by (auto simp: list_of_eucl_nth_if nth_Basis_list_prod inner_prod_def)
  moreover
  have "eucl_of_list
            (interpret_floatariths
              (mmult_fa D D D
       (concat (map (\<lambda>j. map (\<lambda>i. FDERIV_floatarith (ode_e ! j) [0..<D] (replicate D 0[i := 1])) [0..<D]) [0..<D]))
       (map floatarith.Var [D..<D + D * D])) (list_of_eucl x)) =
    matrix (blinfun_apply (ode_d 0 (fst x) 0)) ** snd x"
    unfolding matrix_eq
    apply auto
    apply (subst matrix_vector_mul_assoc[symmetric])
    apply (subst matrix_works)
    subgoal by (auto intro!: bounded_linear.linear blinfun.bounded_linear_right)
    apply (subst einterpret_mmult_fa[where 'n='n and 'm = 'n and 'l='n])
    subgoal by (simp add: wdD[OF \<open>wd _\<close>])
    subgoal by (simp add: length_concat o_def sum_list_distinct_conv_sum_set wdD[OF \<open>wd _\<close>])
    subgoal by (simp add: length_concat o_def sum_list_distinct_conv_sum_set wdD[OF \<open>wd _\<close>])
    subgoal for v
    proof -
      have v: "einterpret (map floatarith.Var [D..<D + D * D]) (list_of_eucl x) *v v = snd x *v v"
        apply (vector matrix_vector_mult_def)
        apply (simp add: vec_nth_eq_list_of_eucl2 wdD[OF \<open>wd _\<close>])
        apply (auto simp: vec_nth_eq_list_of_eucl1 sum_index_enum_eq)
        apply (subst sum_index_enum_eq)+
        apply (rule sum.cong)
        by (auto simp: nth_Basis_list_prod prod_eq_iff inner_prod_def)
      show ?thesis
        unfolding matrix_vector_mul_assoc[symmetric]
        apply (subst v)
        apply (auto simp: concat_map_map_index vec_nth_eq_list_of_eucl2)
        apply (subst  eucl_of_list_list_of_eucl[of "snd x *v v", symmetric])
        apply (subst (2) eucl_of_list_list_of_eucl[of "snd x *v v", symmetric])
        apply (subst eucl_of_list_matrix_vector_mult_eq_sum_nth_Basis_list)
        subgoal by (simp add: length_concat o_def sum_list_distinct_conv_sum_set wdD[OF \<open>wd _\<close>])
        subgoal by simp
        apply (subst blinfun_apply_eq_sum)
         apply (auto simp: vec_nth_eq_list_of_eucl1 sum_index_enum_eq)
        apply (auto simp: scaleR_sum_left ode_d.rep_eq intro!: sum.cong[OF refl])
        apply (auto simp: ode_d_raw_def wdD[OF \<open>wd _\<close>] eucl_of_list_inner )
        apply (auto simp: ode_d_expr_def FDERIV_floatariths_def wdD[OF \<open>wd _\<close>] )
        apply (rule interpret_floatarith_FDERIV_floatarith_cong)
        subgoal for x y i
          using wdD[OF \<open>wd _\<close>]
          by (auto simp add: nth_append inner_prod_def
              nth_Basis_list_prod dest!: max_Var_floatariths_lessI)
        subgoal by auto
        subgoal by auto
        subgoal
          apply (auto simp: wdD[OF \<open>wd _\<close>] nth_list_update inner_Basis intro!: nth_equalityI)
          by (metis \<open>length (list_of_eucl (snd x *v v)) = CARD('n)\<close> index_Basis_list_nth length_list_of_eucl)
        done
    qed
    done
  ultimately show ?thesis
    unfolding var.ode_def ode_def
    unfolding ode_e'_def
    by (auto simp: wdD[OF \<open>wd _\<close>] ode_d1_def intro!: euclidean_eqI[where 'a="'n vec1"])
qed

lemma var_existence_ivl_imp_existence_ivl:
  fixes x::"'n::enum vec1"
  assumes wd: "wd TYPE('n rvec)"
  assumes t: "t \<in> var.existence_ivl0 x"
  shows "t \<in> existence_ivl0 (fst x)"
proof (rule existence_ivl_maximal_segment)
  from var.flow_solves_ode[OF UNIV_I var.mem_existence_ivl_iv_defined(2), OF t]
  have D: "(var.flow0 x solves_ode (\<lambda>_. var.ode)) {0--t} (var.Csafe)"
    apply (rule solves_ode_on_subset)
     apply (rule var.closed_segment_subset_existence_ivl)
     apply (rule t)
    apply simp
    done
  show "((\<lambda>t. fst (var.flow0 x t)) solves_ode (\<lambda>_. ode)) {0--t} (Csafe)"
    using var.closed_segment_subset_existence_ivl[OF t]
    apply (auto simp: has_vderiv_on_def has_vector_derivative_def subset_iff
        intro!: solves_odeI derivative_eq_intros)
        apply (rule refl)
       apply (rule refl)
      apply (rule refl)
     apply (auto simp: var.flowderiv_def )
     apply (subst var_ode_eq[OF wd(1)])
      apply (auto simp: blinfun.bilinear_simps)
    subgoal for s
      using solves_odeD(2)[OF D, of s]
      by (subst(asm) (3) safe_eq[OF wd]) (auto )
    subgoal for s
      using solves_odeD(2)[OF D, of s]
      by (subst(asm) (3) safe_eq[OF wd]) (auto )
    done
next
  show "fst (var.flow0 x 0) = fst x"
    apply (subst var.flow_initial_time)
      apply simp
    apply (rule var.mem_existence_ivl_iv_defined[OF t])
    apply auto
    done
qed simp

lemma matrix_scaleR: "matrix (blinfun_apply (h *\<^sub>R X)) = h *\<^sub>R matrix X"
  by (vector matrix_def blinfun.bilinear_simps)

lemma existence_ivl_imp_var_existence_ivl:
  fixes x::"'n::enum rvec"
  assumes wd: "wd TYPE('n rvec)"
  assumes t: "t \<in> existence_ivl0 x"
  shows "t \<in> var.existence_ivl0 ((x, W)::'n vec1)"
proof (rule var.existence_ivl_maximal_segment)
  from flow_solves_ode[OF UNIV_I mem_existence_ivl_iv_defined(2), OF t]
  have D: "(flow0 x solves_ode (\<lambda>_. ode)) {0--t} (Csafe)"
    apply (rule solves_ode_on_subset)
     apply (rule closed_segment_subset_existence_ivl)
     apply (rule t)
    apply simp
    done
  show "((\<lambda>t. (flow0 x t, matrix (Dflow x t) ** W)) solves_ode (\<lambda>_. var.ode)) {0--t} (var.Csafe)"
    using closed_segment_subset_existence_ivl[OF t]
    apply (auto simp: has_vderiv_on_def has_vector_derivative_def subset_iff
        intro!: solves_odeI derivative_eq_intros)
        apply (rule refl)
        apply (rule refl)
        apply (rule refl)
       apply (rule has_derivative_at_withinI)
       apply (rule Dflow_has_derivative)
       apply force
      apply (rule refl)
     apply (auto simp: flowderiv_def )
     apply (subst var_ode_eq)
     apply (auto simp: blinfun.bilinear_simps matrix_blinfun_compose wd
        intro!: ext)
    subgoal for s h
      unfolding matrix_scaleR matrix_blinfun_compose matrix_mul_assoc matrix_scaleR_right ..
    subgoal for s
      using solves_odeD(2)[OF D, of s] safe_eq[OF wd]
      by auto
    done
next
  have "x \<in> Csafe" by rule fact
  then show "(flow0 x 0, matrix (blinfun_apply (Dflow x 0)) ** W) = (x, W)"
    apply (auto )
    apply (vector matrix_def matrix_matrix_mult_def axis_def)
    by (auto simp:  if_distrib if_distribR cong: if_cong)
qed auto

theorem var_existence_ivl0_eq_existence_ivl0:
  fixes x::"'n::enum vec1"
  assumes wd: "wd TYPE('n rvec)"
  shows "var.existence_ivl0 (x::'n vec1) = existence_ivl0 (fst x)"
  apply safe
  subgoal by (rule var_existence_ivl_imp_existence_ivl[OF wd, of _ "x", simplified], simp)
  subgoal
    by (rule existence_ivl_imp_var_existence_ivl[OF wd, of _ "fst x" "snd x", unfolded prod.collapse])
  done

theorem var_flow_eq_flow_Dflow:
  fixes x::"'n::enum vec1"
  assumes wd: "wd TYPE('n rvec)"
  assumes t: "t \<in> var.existence_ivl0 x"
  shows "var.flow0 x t = vec1_of_flow1 (flow0 (fst x) t, Dflow (fst x) t o\<^sub>L blinfun_of_vmatrix (snd x)) "
proof -
  have x: "x \<in> var.Csafe"
    by (rule var.mem_existence_ivl_iv_defined[OF t])
  then have "fst x \<in> Csafe"
    by (subst (asm) safe_eq[OF wd]) auto
  then have sx[simp]: "(fst x) \<in> Csafe" by simp
  show ?thesis
  proof (rule var.flow_unique_on[OF t])
    show "vec1_of_flow1 (flow0 (fst x) 0, Dflow (fst x) 0 o\<^sub>L blinfun_of_vmatrix (snd x)) = x"
      by (auto simp: vec1_of_flow1_def x)
    show "((\<lambda>a. vec1_of_flow1 (flow0 (fst x) a, Dflow (fst x) a o\<^sub>L blinfun_of_vmatrix (snd x))) has_vderiv_on
     (\<lambda>t. var.ode (vec1_of_flow1 (flow0 (fst x) t, Dflow (fst x) t o\<^sub>L blinfun_of_vmatrix (snd x)))))
     (var.existence_ivl0 x)"
      apply (auto simp: has_vderiv_on_def has_vector_derivative_def vec1_of_flow1_def
          at_within_open[OF _ var.open_existence_ivl] flowderiv_def
          intro!: derivative_eq_intros var_existence_ivl_imp_existence_ivl[OF wd]
          Dflow_has_derivative ext)
      apply (subst var_ode_eq[OF wd(1)])
       apply (auto simp: blinfun.bilinear_simps)
      subgoal for t
        using flow_in_domain[of t "fst x"]
        by (simp add: var_existence_ivl_imp_existence_ivl[OF wd])
      subgoal for t h
        by (simp add: matrix_blinfun_compose matrix_scaleR matrix_mul_assoc matrix_scaleR_right)
      done
    fix t
    assume "t \<in> var.existence_ivl0 x"
    then show "vec1_of_flow1 (flow0 (fst x) t, Dflow (fst x) t o\<^sub>L blinfun_of_vmatrix (snd x)) \<in> var.Csafe"
      by (subst safe_eq[OF wd])
        (auto simp: vec1_of_flow1_def dest!: var_existence_ivl_imp_existence_ivl[OF wd]
          flow_in_domain)
  qed
qed

lemma blinfun_of_vmatrix_matrix_matrix_mult[simp]:
  "blinfun_of_vmatrix (A ** B) = blinfun_of_vmatrix A o\<^sub>L blinfun_of_vmatrix B"
  including blinfun.lifting
  by transfer (auto simp: o_def matrix_vector_mul_assoc)

lemma blinfun_of_vmatrix_mat_1[simp]: "blinfun_of_vmatrix (mat 1) = 1\<^sub>L"
  including blinfun.lifting
  by transfer (auto simp: matrix_vector_mul_lid)

lemma blinfun_of_vmatrix_matrix[simp]:
  "blinfun_of_vmatrix (matrix (blinfun_apply A)) = A"
  including blinfun.lifting
  by transfer (auto simp: bounded_linear.linear matrix_works)

theorem flow_Dflow_eq_var_flow:
  fixes x::"'n::enum rvec"
  assumes wd: "wd TYPE('n rvec)"
  assumes t: "t \<in> existence_ivl0 x"
  shows "(flow0 x t, Dflow x t o\<^sub>L W) = flow1_of_vec1 (var.flow0 (x, matrix W) t::'n vec1)"
  using var_flow_eq_flow_Dflow[OF wd existence_ivl_imp_var_existence_ivl[OF wd t]]
  unfolding var_flow_eq_flow_Dflow[OF wd existence_ivl_imp_var_existence_ivl[OF wd t]]
  by (auto simp: flow1_of_vec1_def vec1_of_flow1_def)

lemma vec1_of_flow1_flow1_of_vec1[simp]:
  "vec1_of_flow1 (flow1_of_vec1 X) = X"
  unfolding vec1_of_flow1_def flow1_of_vec1_def
  by (transfer) (auto simp: matrix_of_matrix_vector_mul)

context includes blinfun.lifting begin
lemma flow1_of_vec1_vec1_of_flow1[simp]:
  "flow1_of_vec1 (vec1_of_flow1 X) = X"
  unfolding vec1_of_flow1_def flow1_of_vec1_def
  apply (transfer)
  apply (auto simp: matrix_of_matrix_vector_mul)
  using linear_conv_bounded_linear matrix_vector_mul by fastforce
end

lemma
  var_flowpipe0_flowpipe:
  assumes wd: "wd TYPE('n::enum rvec)"
  assumes "var.flowpipe0 X0 hl hu (CX) X1"
  assumes "fst ` X0 \<subseteq> Csafe"
  assumes "fst ` CX \<subseteq> Csafe"
  assumes "fst ` X1 \<subseteq> Csafe"
  shows "flowpipe (flow1_of_vec1 ` X0) hl hu (flow1_of_vec1 ` (CX::'n vec1 set)) (flow1_of_vec1 ` X1)"
  using assms
  unfolding flowpipe_def var.flowpipe0_def
  apply safe
  subgoal by (auto simp add: flow1_of_vec1_def vec1_of_flow1_def safe_eq[OF wd])
  subgoal by (auto simp add: flow1_of_vec1_def vec1_of_flow1_def safe_eq[OF wd])
  subgoal by (auto simp add: flow1_of_vec1_def vec1_of_flow1_def safe_eq[OF wd])
  subgoal for x W y V h
    apply (drule bspec[where x="(y, V)"], force)
    apply (drule bspec, assumption)
    by (simp add: var_existence_ivl0_eq_existence_ivl0[OF wd] flow1_of_vec1_def)
  subgoal for x W y V h
    apply (drule bspec[where x="(y, V)"], force)
    apply (drule bspec, assumption)
    apply (subst flow_Dflow_eq_var_flow[OF wd],
        force simp: var_existence_ivl0_eq_existence_ivl0[OF wd] flow1_of_vec1_def)
    apply (rule imageI)
    by (simp add: vec1_of_flow1_def flow1_of_vec1_def)
  subgoal for x W y V h h'
    apply (drule bspec[where x="vec1_of_flow1 (x, W)"], force)
    apply (drule bspec, assumption)
    apply (subst flow_Dflow_eq_var_flow[OF wd])
     apply (subst (asm) var_existence_ivl0_eq_existence_ivl0[OF wd])
     apply (simp add: flow1_of_vec1_def)
    subgoal
      by (meson local.existence_ivl_initial_time local.mem_existence_ivl_iv_defined(1)
          local.mem_existence_ivl_iv_defined(2) mem_is_interval_1_I mvar.interval)
    subgoal
      apply (rule imageI)
      by (simp add: vec1_of_flow1_def flow1_of_vec1_def)
    done
  done

definition "solve_poincare_fas n = map floatarith.Var [0..<D] @ concat (map (\<lambda>i \<comment> \<open>(row)\<close>. map (\<lambda>j \<comment> \<open>(column)\<close>.
    (if i \<noteq> n then Var (D + i * D + j) - (Var(D + n * D + j) * (ode_e ! i) / (ode_e ! n))
    else 0)
  ) [0..<D]) [0..<D])"

lemma inner_Basis_eq_vec_nth: "b \<in> Basis \<Longrightarrow> v \<bullet> b = vec_nth v (enum_class.enum ! index Basis_list b)"
  by (auto simp: inner_vec_def vec_nth_Basis if_distrib Basis_vec_def axis_eq_axis
        index_Basis_list_axis1
      cong: if_cong)

theorem einterpret_solve_poincare_fas:
  assumes wd: "wd TYPE('n rvec)"
  assumes "length CXs = D + D*D" "n < D"
  assumes nz: "ode (fst (eucl_of_list CXs::'n vec1)) \<bullet> Basis_list ! n \<noteq> 0"
  shows
  "flow1_of_vec1 (einterpret (solve_poincare_fas n) CXs::'n::enum vec1) =
  (let (x, d) = flow1_of_vec1 (eucl_of_list CXs::'n vec1) in (x,
     d - (blinfun_scaleR_left (ode (x)) o\<^sub>L
    (blinfun_scaleR_left (inverse (ode x \<bullet> Basis_list ! n)) o\<^sub>L (blinfun_inner_left (Basis_list ! n) o\<^sub>L d)))))"
  using assms
  apply (auto intro!: simp: flow1_of_vec1_def solve_poincare_fas_def)
  subgoal
    apply (auto intro!: euclidean_eqI[where 'a="'n rvec"])
    apply (subst eucl_of_list_prod)
    by (auto simp: eucl_of_list_prod length_concat o_def sum_list_distinct_conv_sum_set wdD[OF wd] take_eq_map_nth)
  subgoal premises prems
  proof -
    have ode_e_eq: "interpret_floatarith (ode_e ! i) (map ((!) CXs) [0..<CARD('n)]) = interpret_floatarith (ode_e ! i) CXs"
      if "i < D"
      for i
      apply (rule interpret_floatarith_max_Var_cong)
      apply (drule max_Var_floatariths_lessI)
      using that apply (simp add: wdD[OF wd])
      apply (subst nth_map)
       apply auto
      using wdD[OF wd]
      apply (simp add: )
      using wdD[OF wd]
      apply (simp add: )
      done
    define z where "z = (0::float)"
    show ?thesis
      supply [simp] = snd_eucl_of_list_prod fst_eucl_of_list_prod
      supply [simp del] = eucl_of_list_take_DIM
      using prems unfolding z_def[symmetric]
      including blinfun.lifting
      apply (transfer fixing: CXs D n z)
      unfolding z_def
      apply (auto simp: o_def ode_def intro!: ext)
      apply (vector matrix_vector_mult_def )
      apply (auto intro!: blinfun_euclidean_eqI simp: inner_Basis_eq_vec_nth wdD[OF wd])
      apply (auto simp: length_concat o_def sum_list_distinct_conv_sum_set wdD[OF wd] take_eq_map_nth)
      apply (auto simp: concat_map_map_index)
      apply (vector )
      apply (subst vec_nth_eq_list_of_eucl2 vec_nth_eq_list_of_eucl1)+
      apply (subst (asm) vec_nth_eq_list_of_eucl2 vec_nth_eq_list_of_eucl1)+
      apply (simp add: less_imp_le wdD[OF wd] index_nth_id )
      apply (auto simp: algebra_simps ode_e_eq wdD[OF wd] divide_simps)
      done
  qed
  done

definition "sps_eq \<longleftrightarrow> (length solve_poincare_slp = D \<and> (\<forall>i < D. solve_poincare_slp ! i = (slp_of_fas (map fold_const_fa (solve_poincare_fas i)))))"

lemma sps_eqD: "sps_eq \<Longrightarrow> i < D \<Longrightarrow> solve_poincare_slp ! i = slp_of_fas (map fold_const_fa (solve_poincare_fas i))"
  by (auto simp: sps_eq_def)

lemma sps_lengthD: "sps_eq \<Longrightarrow> length solve_poincare_slp = D"
  by (auto simp: sps_eq_def)

lemma sps_length_le:
  assumes sps_eq
  shows "i < D \<Longrightarrow> length (solve_poincare_slp ! i) \<ge> length (solve_poincare_fas i)"
  by (auto simp: sps_eqD[OF \<open>sps_eq\<close>] intro!: order_trans[OF _ length_slp_of_fas_le])

definition "vwd_step TYPE('n::enum) \<longleftrightarrow>
     wd TYPE('n rvec)
   \<and> 0 < rk2_param optns
   \<and> rk2_param optns \<le> 1
   \<and> ode_slp_eq ode_slp
   \<and> rk2_slp_eq rk2_slp D
   \<and> euler_slp_eq euler_slp D
   \<and> euler_incr_slp_eq euler_incr_slp D
   \<and> sps_eq
   \<and> var.ode_slp_eq ode_slp'
   \<and> var.rk2_slp_eq rk2_slp' (D + D * D)
   \<and> var.euler_slp_eq euler_slp' (D + D * D)
   \<and> var.euler_incr_slp_eq euler_incr_slp' (D + D * D)"

lemma
  vwd_stepD:
  assumes "vwd_step TYPE('n::enum)"
  shows "wd TYPE('n rvec)"
    "0 < rk2_param optns"
    "rk2_param optns \<le> 1"
    "sps_eq"
    "ode_slp_eq ode_slp"
    "rk2_slp_eq rk2_slp D"
    "euler_slp_eq euler_slp D"
    "euler_incr_slp_eq euler_incr_slp D"
    "var.ode_slp_eq ode_slp'"
    "var.rk2_slp_eq rk2_slp' (D + D * D)"
    "var.euler_slp_eq euler_slp' (D + D * D)"
    "var.euler_incr_slp_eq euler_incr_slp' (D + D * D)"
  using assms by (auto simp: vwd_step_def)

lemma vwd_step[refine_vcg, intro]:
  assumes "vwd_step TYPE('n::enum)"
  shows "var.wd_step TYPE('n::enum vec1)"
  using assms
  by (auto simp: var.wd_step_def vwd_step_def)

lemma choose_step'_flowpipe:
  assumes wd[refine_vcg]: "vwd_step TYPE('n::enum)"
  notes wd' = vwd_stepD[OF wd]
  assumes safe: "fst ` X0 \<subseteq> Csafe"
  shows "var.choose_step (X0::'n vec1 set) h \<le> SPEC (\<lambda>(h', _, RES_ivl, RES::'n vec1 set).
      0 < h' \<and> h' \<le> h \<and> flowpipe (flow1_of_vec1 ` X0) h' h' (flow1_of_vec1 ` RES_ivl) (flow1_of_vec1 ` RES))"
  apply refine_vcg
  apply (auto simp: )
  apply (frule var.flowpipe0_safeD)
  apply (drule var_flowpipe0_flowpipe[rotated])
  by (auto simp: safe_eq wd')

definition "transversal_directions f =
  do {
    (I, S) \<leftarrow> ivl_rep_of_set f;
    RETURN (sum_list (map (\<lambda>b. (if I \<bullet> b \<le> 0 then if S \<bullet> b \<le> 0 then S \<bullet> b else 0 else if S \<bullet> b \<ge> 0 then I \<bullet> b else 0) *\<^sub>R b)
      (Basis_list::'a::executable_euclidean_space list)))
  }"
sublocale autoref_op_pat_def transversal_directions .

lemma [autoref_rules]: "(sgn, sgn) \<in> rnv_rel \<rightarrow> rnv_rel"
  by auto

schematic_goal strongest_direction_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(xs, x) \<in> lv_rel"
  shows "(?f, strongest_direction $ (x::'a)) \<in> lv_rel \<times>\<^sub>r rnv_rel"
  unfolding strongest_direction_def
  including art
  by autoref
concrete_definition strongest_direction_impl for xs uses strongest_direction_impl
lemma strongest_direction_impl_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) D \<Longrightarrow> (strongest_direction_impl, (strongest_direction::'a\<Rightarrow>_)) \<in> lv_rel \<rightarrow> lv_rel \<times>\<^sub>r rnv_rel"
  using strongest_direction_impl.refine
  by force


lemma [autoref_rules]:
  "(real_divl, real_divl) \<in> nat_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "(truncate_down, truncate_down) \<in> nat_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "(eucl_truncate_down, eucl_truncate_down) \<in> nat_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "(truncate_up, truncate_up) \<in> nat_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "(eucl_truncate_up, eucl_truncate_up) \<in> nat_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "(max, max) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "(min, min) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "((/), (/)) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "(lfloat10, lfloat10) \<in> rnv_rel \<rightarrow> float10_rel"
  "(ufloat10, ufloat10) \<in> rnv_rel \<rightarrow> float10_rel"
  "(shows_prec, shows_prec) \<in> nat_rel \<rightarrow> nat_rel \<rightarrow> string_rel \<rightarrow> string_rel"
  "(shows_prec, shows_prec) \<in> nat_rel \<rightarrow> int_rel \<rightarrow> string_rel \<rightarrow> string_rel"
  "(shows_prec, shows_prec) \<in> nat_rel \<rightarrow> float10_rel \<rightarrow> string_rel \<rightarrow> string_rel"
  "(int, int) \<in> nat_rel \<rightarrow> int_rel"
  by (auto simp: string_rel_def)

lemma intersects_sctns_spec_nres:
  "do {
    ASSUME (finite sctns);
    FOREACH\<^bsup>\<lambda>sctns' b. \<not>b \<longrightarrow> X' \<inter> UNION (sctns - sctns') plane_of = {}\<^esup> sctns
          (\<lambda>sctn b. do {b' \<leftarrow> intersects_spec ( X') sctn; RETURN (b \<or> b')}) False
   } \<le> intersects_sctns_spec X' sctns"
  unfolding intersects_sctns_spec_def
  by refine_vcg auto

schematic_goal intersects_sctns_spec_impl:
  assumes [autoref_rules]: "(ai, a) \<in> appr_rel"
  assumes sctns[autoref_rules]: "(sctnsi, sctns) \<in> sctns_rel"
  notes [simp] = list_set_rel_finiteD[OF sctns]
  shows "(nres_of (?x::_ dres), intersects_sctns_spec $ (a::'a::executable_euclidean_space set) $ sctns) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  apply (rule nres_rel_trans2[OF intersects_sctns_spec_nres])
  including art
  by (autoref_monadic)

concrete_definition intersects_sctns_spec_impl for ai sctnsi uses intersects_sctns_spec_impl
lemma intersects_sctns_spec_impl_refine[autoref_rules]:
  "(\<lambda>ai sctni. nres_of (intersects_sctns_spec_impl ai sctni), intersects_sctns_spec) \<in>
    appr_rel \<rightarrow> sctns_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using intersects_sctns_spec_impl.refine by force

definition "trace_sets s X = do {
    XS \<leftarrow> sets_of_coll (X:::clw_rel (appr_rel)); FORWEAK XS (RETURN ()) (\<lambda>X. RETURN (trace_set s (Some X))) (\<lambda>_ _. RETURN ())
  }"
sublocale autoref_op_pat_def trace_sets .

schematic_goal trace_sets_impl:
  assumes [autoref_rules]: "(si, s) \<in> string_rel" "(Xi, X) \<in> clw_rel appr_rel"
  shows "(RETURN ?f, trace_sets $ s $ X) \<in> \<langle>unit_rel\<rangle>nres_rel"
  unfolding trace_sets_def
  by (subst rel_ANNOT_eq[of X "clw_rel appr_rel"]) (autoref_monadic (plain))
concrete_definition trace_sets_impl for si Xi uses trace_sets_impl
lemmas [autoref_rules] = trace_sets_impl.refine

definition "print_sets s X = do {
    XS \<leftarrow> sets_of_coll (X:::clw_rel (appr_rel)); FORWEAK XS (RETURN ()) (\<lambda>X. RETURN (print_set s (X))) (\<lambda>_ _. RETURN ())
  }"
sublocale autoref_op_pat_def print_sets .

schematic_goal print_sets_impl:
  assumes [autoref_rules]: "(si, s) \<in> bool_rel" "(Xi, X) \<in> clw_rel appr_rel"
  shows "(RETURN ?f, print_sets $ s $ X) \<in> \<langle>unit_rel\<rangle>nres_rel"
  unfolding print_sets_def
  by (subst rel_ANNOT_eq[of X "clw_rel appr_rel"]) (autoref_monadic (plain))
concrete_definition print_sets_impl for si Xi uses print_sets_impl
lemmas [autoref_rules] = print_sets_impl.refine

lemma
  assumes "GEN_OP ws width_spec (A \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel)"
  assumes "\<And>x. TRANSFER (RETURN (wsd x) \<le> ws x)"
  shows width_spec_invar_rel[autoref_rules]:
    "(\<lambda>(a, b). RETURN (wsd a), width_spec) \<in> \<langle>S, A\<rangle>invar_rel b \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
    and width_spec_inter_rel[autoref_rules]:
    "(\<lambda>(a, b). RETURN (wsd a), width_spec) \<in> \<langle>S, A\<rangle>inter_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  using assms
  by (auto simp: nres_rel_def width_spec_def invar_rel_def dest!: fun_relD)

lemma width_spec_coll[autoref_rules]:
  assumes "GEN_OP ws width_spec (A \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel)"
  assumes "\<And>x. TRANSFER (RETURN (wsd x) \<le> ws x)"
  shows "(\<lambda>xs. RETURN (sum_list (map wsd xs)), width_spec) \<in> clw_rel A \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  by (auto simp: nres_rel_def width_spec_def)

definition [simp]: "intersects_sctns_spec_clw = intersects_sctns_spec"

lemma intersects_sections_spec_clw_ref:
  "do {
    Rs \<leftarrow> sets_of_coll ((R:::clw_rel appr_rel):::clw_rel(appr_rel));
    FORWEAK Rs (RETURN False) (\<lambda>R. intersects_sctns_spec R sctns) (\<lambda>a b. RETURN (a \<or> b))
  } \<le> intersects_sctns_spec_clw R sctns"
  unfolding intersects_sctns_spec_def intersects_sctns_spec_clw_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>S b. \<not>b \<longrightarrow> \<Union>S \<inter> UNION sctns plane_of = {}"]) auto
schematic_goal intersects_sections_spec_clw[autoref_rules]:
  assumes [autoref_rules]: "(Ri, R) \<in> clw_rel appr_rel" "(sctnsi, sctns) \<in> sctns_rel"
  shows "(nres_of (?r::_ dres), intersects_sctns_spec_clw $ R $ sctns) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  by (rule nres_rel_trans2[OF intersects_sections_spec_clw_ref[]]) autoref_monadic

definition [simp]: "nonneg_reals = ({0..}::real set)"
sublocale autoref_op_pat_def nonneg_reals .
definition [simp]: "pos_reals = ({0<..}::real set)"
sublocale autoref_op_pat_def pos_reals .
lemma nonneg_reals_autoref[autoref_rules]: "(None, nonneg_reals) \<in> \<langle>Id\<rangle>phantom_rel"
  and pos_reals_autoref[autoref_rules]: "(None, pos_reals) \<in> \<langle>Id\<rangle>phantom_rel"
  by (auto simp: phantom_rel_def)

lemma eq_nth_iff_index:
  "distinct xs \<Longrightarrow> n < length xs \<Longrightarrow> i = xs ! n  \<longleftrightarrow> index xs i = n"
  using index_nth_id by fastforce

lemma
  max_Var_floatariths_ode_e_wd:
  assumes wd: "wd (TYPE('n::enum rvec))"
  assumes "CARD('n) \<le> K"
  shows "max_Var_floatariths ode_e \<le> K"
  using wdD[OF wd] assms by auto

lemma max_Var_floatariths_solve_poincare_fas[le]:
  assumes wd: "wd (TYPE('n::enum rvec))"
  shows "i < D \<Longrightarrow> max_Var_floatariths (solve_poincare_fas i) \<le> D + D * D"
  by (auto simp: solve_poincare_fas_def concat_map_map_index intro!: max_Var_floatariths_leI Suc_leI)
   (auto intro!: max_Var_floatarith_le_max_Var_floatariths_nthI max_Var_floatariths_ode_e_wd[OF wd]
      simp: wdD[OF wd])

definition "nonzero_component s X n = do {
    I \<leftarrow> Inf_inner X n;
    S \<leftarrow> Sup_inner X n;
    CHECKs s (I > 0 \<or> S < 0)
  }"
sublocale autoref_op_pat_def nonzero_component .
lemma nonzero_component[le, refine_vcg]: "nonzero_component s X n \<le> SPEC (\<lambda>_. \<forall>b\<in>X. b \<bullet> n \<noteq> 0)"
  unfolding nonzero_component_def
  by refine_vcg auto

schematic_goal nonzero_component_impl:
  assumes [autoref_rules]: "(Xi, X) \<in> appr_rel" "(ni, n) \<in> lv_rel" "(si, s) \<in> string_rel"
  shows "(nres_of ?f, nonzero_component $ s $ X $ n) \<in> \<langle>unit_rel\<rangle>nres_rel"
  unfolding nonzero_component_def autoref_tag_defs
  by autoref_monadic
concrete_definition nonzero_component_impl for si Xi ni uses nonzero_component_impl
lemma nonzero_component_impl_refine[autoref_rules]:
  "(\<lambda>si Xi ni. nres_of (nonzero_component_impl si Xi ni), nonzero_component) \<in> string_rel \<rightarrow> appr_rel \<rightarrow> lv_rel \<rightarrow> \<langle>unit_rel\<rangle>nres_rel"
  using nonzero_component_impl.refine by force

end

consts i_flow1::interface
consts i_appr1::interface
consts i_scaleR2::"interface\<Rightarrow>interface"

abbreviation "ereal_rel \<equiv> (Id::ereal rel)"

definition scaleR2_rel where scaleR2_rel_internal:
  "scaleR2_rel A = ((ereal_rel \<times>\<^sub>r ereal_rel) \<times>\<^sub>r A) O
    br (\<lambda>((l, u), X). scaleR2 l u X) (\<lambda>((l, u), _). ereal -` {l..u} \<noteq> {})"

lemma scaleR2_rel_def:
  "\<langle>A\<rangle>scaleR2_rel = ((ereal_rel \<times>\<^sub>r ereal_rel) \<times>\<^sub>r A) O
    br (\<lambda>((l, u), X). scaleR2 l u X) (\<lambda>((l, u), _). ereal -` {l..u} \<noteq> {})"
  by (auto simp: relAPP_def scaleR2_rel_internal)
lemmas [autoref_rel_intf] = REL_INTFI[of scaleR2_rel i_scaleR2]

definition [refine_vcg_def]: "scaleR2_rep X = SPEC (\<lambda>((l, u), Y). ereal -` {l..u} \<noteq> {} \<and> X = scaleR2 l u Y)"

context begin interpretation autoref_syn .

lemma appr1e_rep_impl[autoref_rules]:
  "(\<lambda>x. RETURN x, scaleR2_rep) \<in> \<langle>A\<rangle>scaleR2_rel \<rightarrow> \<langle>(ereal_rel \<times>\<^sub>r ereal_rel) \<times>\<^sub>r A\<rangle>nres_rel"
  by (force simp: nres_rel_def scaleR2_rep_def scaleR2_rel_def image_image split_beta'
      dest!: brD intro!: RETURN_SPEC_refine)

lemma fst_scaleR2_image[simp]: "ad \<le> ereal r \<Longrightarrow> ereal r \<le> bd \<Longrightarrow> fst ` scaleR2 ad bd be = fst ` be"
  by (cases ad; cases bd; force simp: scaleR2_def image_image split_beta' vimage_def)

definition [refine_vcg_def]: "scaleRe_ivl_spec l u X = SPEC (\<lambda>Y. Y = scaleR2 l u X)"

definition [simp]: "op_image_fst_colle = (`) fst"

lemma [autoref_op_pat]: "fst ` X \<equiv> OP op_image_fst_colle $ X"
  by auto
definition [simp]: "op_image_fste = (`) fst"
lemma [autoref_op_pat]: "fst ` X \<equiv> OP op_image_fste $ X"
  by simp

end

lemma scaleR2_rel_br: "\<langle>br a I\<rangle>scaleR2_rel =
  br (\<lambda>((x, xa), y). scaleR2 x xa (a y)) (\<lambda>((l, u), y). I y \<and> ereal -` {l..u} \<noteq> {})"
  unfolding scaleR2_rel_def
  unfolding Id_br br_rel_prod br_chain o_def
  by (auto simp: split_beta')

definition "flow1_of_list xs =
  (eucl_of_list (take DIM('a::executable_euclidean_space) xs)::'a,
    blinfun_of_list (take (DIM('a)*DIM('a)) (drop DIM('a) xs @
    replicate (DIM('a)*DIM('a) - (length xs - DIM('a))) 0))::'a\<Rightarrow>\<^sub>L'a)"

lemma blinfun_of_list_eq_blinfun_of_vmatrix:
  assumes "length xs = CARD('n)*CARD('n::enum)"
  shows "blinfun_of_list xs = blinfun_of_vmatrix (eucl_of_list xs::((real, 'n) vec, 'n) vec)"
  using assms
  apply (auto simp: blinfun_of_list_def)
  apply (auto intro!: simp: blinfun_ext blinfun_of_vmatrix.rep_eq blinfun_of_matrix.rep_eq)
  subgoal for i
    apply (subst (2) eucl_of_list_list_of_eucl[symmetric, of i])
    apply (subst eucl_of_list_matrix_vector_mult_eq_sum_nth_Basis_list)
    by (auto simp: sum_Basis_sum_nth_Basis_list scaleR_sum_left intro!: sum.cong)
  done

context approximate_sets_ode_slp' begin

definition "c1_info_of_appr XD =
  (case snd XD of None \<Rightarrow> eucl_of_list ` set_of_appr (fst XD) \<times> UNIV
   | Some D \<Rightarrow> flow1_of_list ` set_of_appr (fst XD @ D))"
definition "c1_info_of_apprs x = \<Union>set (map c1_info_of_appr x)"
definition "c1_info_of_appr' x = Affine_Code.the_default UNIV (map_option c1_info_of_apprs x)"
definition "c1_info_of_appre X = scaleR2 (fst (fst X)) (snd (fst X)) (c1_info_of_appr (snd X))"
definition "c1_info_of_apprse x = \<Union>set (map c1_info_of_appre x)"

definition appr1_rel::"(('b list \<times> 'b list option) \<times>
  ('a::executable_euclidean_space c1_info set)) set"
  where appr1_rel_internal: "appr1_rel = {((xs, None), X \<times> UNIV) |xs X. (xs, X) \<in> appr_rel} \<union>
{((xs, Some ys), X::('a c1_info) set) |xs ys X. X = flow1_of_list ` set_of_appr (xs @ ys) \<and>
  length xs = DIM('a::executable_euclidean_space) \<and>
  length ys = DIM('a) * DIM('a)}"

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

abbreviation "appr1e_rel \<equiv> \<langle>appr1_rel\<rangle>scaleR2_rel"

lemmas [autoref_rel_intf] = REL_INTFI[of appr1_rel i_appr1]

definition [simp]: "op_image_flow1_of_vec1 = (`) flow1_of_vec1"

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

definition [simp]: "op_image_flow1_of_vec1_coll = (`) flow1_of_vec1"

lemma index_autoref[autoref_rules]:
  "(index, index) \<in> \<langle>lv_rel\<rangle>list_rel \<rightarrow> lv_rel \<rightarrow> nat_rel"
  unfolding index_def[abs_def] find_index_def
  apply parametricity
  apply (auto simp: lv_rel_def br_def list_rel_def)
  using list_of_eucl_eucl_of_list by force

definition [simp]: "op_image_fst = (`) fst"
sublocale autoref_op_pat_def op_image_fst .
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

definition [refine_vcg_def]:
  "vec1rep CX = SPEC (\<lambda>R. case R of None \<Rightarrow> True | Some X \<Rightarrow> X = vec1_of_flow1 ` CX)"
sublocale autoref_op_pat_def vec1rep .

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

definition [simp]: "op_times_UNIV X = X \<times> UNIV"
sublocale autoref_op_pat_def op_times_UNIV .
lemma [autoref_op_pat]: "X \<times> UNIV \<equiv> OP op_times_UNIV $ X" by simp

lemma op_times_UNIV_impl[autoref_rules]: "(\<lambda>x. (x, None), op_times_UNIV) \<in> appr_rel \<rightarrow> appr1_rel"
  by (auto simp: appr1_rel_internal)

definition "solve_poincare_plane (n::'n::enum rvec) (CX::'n eucl1 set) = do {
    X \<leftarrow> mk_safe (((`) fst CX::'n rvec set));
    F \<leftarrow> ode_set (set_of_sappr X);
    nonzero_component (ST ''solve_poincare_map: not nonzero!'') F n;
    let i = index Basis_list n;
    ASSERT (i < length solve_poincare_slp);
    vCX \<leftarrow> vec1rep CX;
    case vCX of None \<Rightarrow>
      do {
        RETURN (op_times_UNIV (set_of_sappr X))
      }
    | Some vCX \<Rightarrow>
      do {
        (R::'n vec1 set) \<leftarrow> approx_slp_appr (map fold_const_fa (solve_poincare_fas i)) (solve_poincare_slp ! i) (list_of_eucl ` vCX);
        let R = (op_image_flow1_of_vec1 (R:::appr_rel):::appr1_rel);
        X \<leftarrow> mk_safe (op_image_fst R);
        F \<leftarrow> ode_set (set_of_sappr X);
        nonzero_component (ST ''solve_poincare_map: not nonzero!'') (F) n;
        RETURN (R::'n eucl1 set)
      }
  }"
sublocale autoref_op_pat_def solve_poincare_plane .

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

lemma
  interpret_slp_env_lenD:
  assumes "\<forall>cx\<in>CX. interpret_slp (slp_of_fas (fas)) (env cx) \<in> R"
  assumes "cx \<in> CX"
  shows "interpret_floatariths fas (env cx) \<in> take (length fas) ` R"
proof -
  from slp_of_fas
  have "take (length fas) (interpret_slp (slp_of_fas fas) (env cx)) = interpret_floatariths fas (env cx)"
    by auto
  moreover
  from assms(1)[rule_format, OF \<open>cx \<in> CX\<close>]
  have "interpret_slp (slp_of_fas fas) (env cx) \<in> R" by auto
  ultimately show ?thesis by force
qed

lemma length_solve_poincare_fas[simp]: "length (solve_poincare_fas n) = D + D * D"
  by (auto simp: solve_poincare_fas_def length_concat o_def sum_list_distinct_conv_sum_set)

theorem interpret_floatariths_solve_poincare_fas:
  assumes wd: "wd TYPE('n::enum rvec)"
  assumes "length CXs = D + D*D" "n < D"
  assumes nz: "ode (fst (eucl_of_list CXs::'n vec1)) \<bullet> Basis_list ! n \<noteq> 0"
  shows
  "interpret_floatariths (solve_poincare_fas n) CXs =
    list_of_eucl (vec1_of_flow1 (let (x, d) = flow1_of_vec1 (eucl_of_list CXs::'n vec1) in (x,
       d - (blinfun_scaleR_left (ode (x)) o\<^sub>L
      (blinfun_scaleR_left (inverse (ode x \<bullet> Basis_list ! n)) o\<^sub>L (blinfun_inner_left (Basis_list ! n) o\<^sub>L d))))))"
  using arg_cong[where f="list_of_eucl::'n vec1 \<Rightarrow> _", OF arg_cong[where f=vec1_of_flow1, OF einterpret_solve_poincare_fas[OF assms]]]
  apply (auto simp: )
  apply (subst (asm) list_of_eucl_eucl_of_list)
   apply (auto simp: )
  apply (auto simp: wdD[OF wd])
  done

lemma solve_poincare_plane[le, refine_vcg]:
  assumes vwd[refine_vcg]: "vwd_step (TYPE('n::enum))"
  notes wds[refine_vcg] = vwd_stepD[OF vwd]
  notes wd = wds(1)
  notes wd' = wdD[OF wd]
  assumes "n \<in> Basis"
  shows "solve_poincare_plane (n::'n::enum rvec) CX \<le> SPEC (\<lambda>PDP.
    fst ` PDP \<subseteq> Csafe \<and>
    (\<forall>(x, d) \<in> CX. (x, d - (blinfun_scaleR_left (ode x) o\<^sub>L
      (blinfun_scaleR_left (inverse (ode x \<bullet> n)) o\<^sub>L (blinfun_inner_left n o\<^sub>L d)))) \<in> PDP) \<and>
    (\<forall>(x, d) \<in> PDP. ode x \<bullet> n \<noteq> 0))"
  unfolding solve_poincare_plane_def
  apply (refine_vcg)
  subgoal using sps_eqD[OF \<open>sps_eq\<close>] sps_lengthD[OF \<open>sps_eq\<close>] \<open>n \<in> Basis\<close> wd' by auto
       apply (auto simp: assms sps_eqD[OF \<open>sps_eq\<close>] sps_lengthD[OF \<open>sps_eq\<close>])
  subgoal using sps_eqD[OF \<open>sps_eq\<close>] sps_lengthD[OF \<open>sps_eq\<close>] \<open>n \<in> Basis\<close> wd' by auto
  subgoal for F env F2 x d
    apply (drule bspec, assumption)
    apply (rule image_eqI)
     prefer 2 apply assumption
    apply (subst einterpret_solve_poincare_fas)
    subgoal using wd by auto
    subgoal using sps_eqD[OF \<open>sps_eq\<close>] sps_lengthD[OF \<open>sps_eq\<close>] \<open>n \<in> Basis\<close> wd' by auto
    subgoal by assumption
    subgoal using sps_eqD[OF \<open>sps_eq\<close>] sps_lengthD[OF \<open>sps_eq\<close>] \<open>n \<in> Basis\<close> wd' by auto
    subgoal using sps_eqD[OF \<open>sps_eq\<close>] sps_lengthD[OF \<open>sps_eq\<close>] \<open>n \<in> Basis\<close> wd' by auto
    done
  subgoal premises prems for F env F2 e x d l
  proof -
    note prems
    have "(d, l) \<in> flow1_of_vec1 ` env"
      apply (rule image_eqI)
      using prems by auto
    then have "ode (fst (d, l)) \<in> ode ` fst ` \<dots>" by blast
    also from prems have "\<dots> \<subseteq> F2" by simp
    finally have "ode d \<in> F2" by simp
    with prems have "ode d \<bullet> n \<noteq> 0" by auto
    then show ?thesis
      using prems
      by (simp add: in_Basis_index_Basis_list \<open>n \<in> Basis\<close>)
  qed
  done

definition embed1::"'n::enum rvec \<Rightarrow> ('n rvec * (real^'n::enum^'n::enum))" where [simp]: "embed1 x = (x, 0)"
sublocale autoref_op_pat_def embed1 .

lemma [autoref_rules_raw]:
  assumes "DIM_precond TYPE((real, 'n::enum) vec) K"
  shows "DIM_precond TYPE(((real, 'n) vec, 'n) vec) (K * K)"
  using assms by auto

lemma embed1_impl[autoref_rules]:
  assumes "DIM_precond TYPE((real, 'n::enum) vec) D"
  shows "((\<lambda>x. x @ replicate (D * D) 0), embed1::'n rvec\<Rightarrow>_) \<in> lv_rel \<rightarrow> lv_rel"
  using assms
  by (auto simp: lv_rel_def br_def eucl_of_list_prod)

definition "choose_step1 (X::'n::enum eucl1 set) h = do {
    lX \<leftarrow> vec1rep X;
    case lX of None \<Rightarrow>
      do {
        sX \<leftarrow> mk_safe (fst ` X);
        (h, err, CX', X') \<leftarrow> choose_step sX h;
        \<^cancel>\<open>err \<leftarrow> width_spec (err:::appr_rel);\<close>
        RETURN (h, err \<times> UNIV, (set_of_sappr CX') \<times> UNIV, (set_of_sappr X') \<times> UNIV)
      }
    | Some vX \<Rightarrow>
      do {
        sX \<leftarrow> var.mk_safe vX;
        (h, err, CX', X') \<leftarrow> var.choose_step sX h;
        let CX' = flow1_of_vec1 ` (set_of_sappr (CX':::var.sappr_rel):::appr_rel);
        let X' = flow1_of_vec1 ` (set_of_sappr (X':::var.sappr_rel):::appr_rel);
        let err' = flow1_of_vec1 ` (err:::appr_rel);
        \<^cancel>\<open>err \<leftarrow> width_spec (fst ` (flow1_of_vec1 ` (err:::appr_rel)):::appr_rel);\<close>
        RETURN (h, err', CX', X'::'n eucl1 set)
      }
  }"
sublocale autoref_op_pat_def choose_step1 .

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

lemma flowpipe0_imp_flowpipe:
  assumes "flowpipe0 (fst ` X0) x1 x1 aba bba"
  shows "flowpipe X0 x1 x1 (aba \<times> UNIV) (bba \<times> UNIV)"
  using assms
  by (auto simp: flowpipe0_def flowpipe_def)

lemma choose_step1_flowpipe[le, refine_vcg]:
  assumes vwd[refine_vcg]: "vwd_step TYPE('n::enum)"
  shows "choose_step1 (X0::'n eucl1 set) h \<le> SPEC (\<lambda>(h', _, RES_ivl, RES::'n eucl1 set).
      0 < h' \<and> h' \<le> h \<and> flowpipe X0 h' h' RES_ivl RES)"
  using assms
  unfolding choose_step1_def
  apply (refine_vcg choose_step'_flowpipe[le] vwd_stepD)
     apply (auto simp: image_image)
    apply (auto simp: wd_step_def vwd_stepD flowpipe0_imp_flowpipe env_len_def)
  by (auto simp: safe_eq vwd_step_def vec1_of_flow1_def)

definition "plane1_of x = plane_of x \<times> UNIV"
definition "below1_halfspaces x = below_halfspaces x \<times> UNIV"
definition "sbelow1_halfspaces x = sbelow_halfspaces x \<times> UNIV"
abbreviation "plane1_invar_rel \<equiv> \<lambda>A. \<langle>(\<langle>lv_rel\<rangle>sctn_rel), A\<rangle>invar_rel plane1_of "

definition "c1_info_invar N XD \<longleftrightarrow> length (fst XD) = N \<and> (case snd XD of Some D \<Rightarrow> length D = (length (fst XD))\<^sup>2 | None \<Rightarrow> True)"

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

definition op_image_zerofst :: "('a \<times> 'c) set \<Rightarrow> ('a::zero \<times> 'c) set"
  where [simp]: "op_image_zerofst \<equiv> \<lambda>X. (\<lambda>x. (0, snd x)) ` X"
sublocale autoref_op_pat_def op_image_zerofst .
lemma op_image_zerofst_impl[autoref_rules]:
  "(\<lambda>(_, x). (appr_of_ivl (replicate D 0) (replicate D 0), x), op_image_zerofst::'n c1_info set \<Rightarrow> _)
    \<in> appr1_rel \<rightarrow> appr1_rel"
  if "DIM_precond (TYPE('n::executable_euclidean_space)) D"
  using that
  apply (auto simp: appr1_rel_br dest!: brD intro!: brI)
  subgoal by (force simp: c1_info_of_appr_def image_image flow1_of_list_def
        set_of_appr_of_ivl_point_append eucl_of_list_prod c1_info_invar_def length_set_of_appr
        split: option.splits elim!: mem_set_of_appr_appendE)
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

definition op_image_zerofst_vec :: "('n::enum vec1) set \<Rightarrow> ('n::enum vec1) set"
  where [simp]: "op_image_zerofst_vec \<equiv> \<lambda>X. (\<lambda>x. (0, snd x)) ` X"
sublocale autoref_op_pat_def op_image_zerofst_vec .

lemma op_image_zerofst_vec_impl[autoref_rules]:
  "(\<lambda>x. (appr_of_ivl (replicate D 0) (replicate D 0) @ drop D x), op_image_zerofst_vec::'n vec1 set \<Rightarrow> _)
    \<in> appr_rel \<rightarrow> appr_rel"
  if "DIM_precond (TYPE('n::enum rvec)) D"
  using that
  apply (auto simp: appr_rel_br set_of_appr_of_ivl_point_append image_image eucl_of_list_prod
      dest!: brD intro!: brI
      dest: drop_set_of_apprD[where n="CARD('n)"] )
  subgoal for a b
    apply (drule set_of_appr_dropD)
    apply safe
    apply (rule image_eqI) defer apply assumption
    apply (auto simp: eucl_of_list_prod)
    apply (rule eucl_of_list_eq_takeI)
    apply simp
    done
  done

definition [simp]: "op_image_embed1 X = embed1 ` X"
lemma [autoref_op_pat_def]: "embed1 ` X \<equiv> OP op_image_embed1 $ X"
  by auto

lemma op_image_embed1_impl[autoref_rules]:
  assumes "DIM_precond TYPE((real, 'n::enum) vec) D"
  shows "(\<lambda>x. x@appr_of_ivl (replicate (D*D) 0) (replicate (D*D) 0), op_image_embed1::'n rvec set \<Rightarrow> _)
    \<in> appr_rel \<rightarrow> appr_rel"
  using assms
  by (force simp: appr_rel_br br_def set_of_appr_of_ivl_point_append set_of_appr_of_ivl_append_point
      image_image eucl_of_list_prod length_set_of_appr)

lemma sv_appr_rell[relator_props]: "single_valued appr_rell"
  by (auto simp: appr_rell_internal)

lemma single_valued_union:
  shows "single_valued X \<Longrightarrow> single_valued Y \<Longrightarrow> Domain X \<inter> Domain Y = {} \<Longrightarrow> single_valued (X \<union> Y)"
  by (auto simp: single_valued_def)

lemma sv_appr1_rel[relator_props]: "single_valued appr1_rel"
  apply (auto simp:  appr1_rel_internal appr_rel_def intro!: relator_props single_valued_union)
   apply (auto simp: single_valued_def)
   apply (auto simp: lv_rel_def set_rel_br)
   apply (auto simp: br_def)
   apply (rule imageI)
  apply (metis single_valued_def sv_appr_rell)
  by (metis imageI single_valued_def sv_appr_rell)

definition "inter_sctn1_spec (X::'n::enum eucl1 set) (sctn::'n rvec sctn) = do {
    R \<leftarrow> inter_sctn_spec (fst ` X) sctn;
    vX \<leftarrow> vec1rep X;
    case vX of None \<Rightarrow>
      do {
        let R1 = R \<times> UNIV;
        RETURN (R1, R1)
      }
    | Some X \<Rightarrow>
      do {
        let sctn = ((Sctn (embed1 (normal sctn)) (pstn sctn)::'n vec1 sctn));
        R1 \<leftarrow> inter_sctn_spec X sctn;
        let R2 = op_image_zerofst_vec X + op_image_embed1 R;
        RETURN ((flow1_of_vec1 ` R1), (flow1_of_vec1 ` R2))
      }
  }"
sublocale autoref_op_pat_def inter_sctn1_spec .

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

lemma image_flow1_of_vec1I:
  "vec1_of_flow1 x \<in> X \<Longrightarrow> x \<in> flow1_of_vec1 ` X"
  by (rule image_eqI) (rule flow1_of_vec1_vec1_of_flow1[symmetric])

lemma inter_sctn1_spec[le, refine_vcg]:
  "inter_sctn1_spec X sctn \<le> SPEC (\<lambda>(R, S). X \<inter> plane_of sctn \<times> UNIV \<subseteq> R \<and> fst ` R \<subseteq> plane_of sctn
  \<and> X \<inter> plane_of sctn \<times> UNIV \<subseteq> S \<and> fst ` S \<subseteq> plane_of sctn)"
  unfolding inter_sctn1_spec_def
  apply (refine_vcg, auto)
  subgoal by (rule image_flow1_of_vec1I) (auto simp: plane_of_def inner_prod_def)
  subgoal by (auto simp: plane_of_def inner_prod_def)
  subgoal by (rule image_flow1_of_vec1I)
         (force simp: set_plus_def plane_of_def inner_prod_def vec1_of_flow1_def)
  subgoal by (force simp: set_plus_def)
  done

lemma is_empty_ivl_rel[autoref_rules]:
  assumes le[THEN GEN_OP_D, param_fo]: "GEN_OP le (\<le>) (A \<rightarrow> A \<rightarrow> bool_rel)"
  shows "(\<lambda>(x, y). \<not> le x y, is_empty) \<in> \<langle>A\<rangle>ivl_rel \<rightarrow> bool_rel"
  apply (auto simp: ivl_rel_def br_def set_of_ivl_def)
  subgoal premises prems for a b c d
    using le[OF prems(2, 3)] prems(1,4-) order_trans
    by auto
  subgoal premises prems for a b c d
    using le[OF prems(3,4)] prems(1,2) order_trans
    by auto
  done

definition "disjoints_spec X Y = do {
    Xi \<leftarrow> ivls_of_sets X;
    IS \<leftarrow> inter_overappr (Xi:::clw_rel lvivl_rel) (Y:::clw_rel lvivl_rel);
    RETURN (is_empty IS)
  }"
sublocale autoref_op_pat_def disjoints_spec .
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

lemma disjoints_spec[le, refine_vcg]:
  "disjoints_spec X Y \<le> SPEC (\<lambda>b. b \<longrightarrow> (X \<inter> Y = {}))"
  unfolding disjoints_spec_def autoref_tag_defs
  by refine_vcg auto

definition "op_image_fst_coll_nres XS = do {
    XSs \<leftarrow> sets_of_coll XS;
    FORWEAK XSs (RETURN op_empty_coll) (\<lambda>X.
      RETURN (mk_coll (op_image_fst X:::appr_rel))) (\<lambda>A B. RETURN (B \<union> A))
  }"
sublocale autoref_op_pat_def op_image_fst_coll_nres .
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
lemma op_image_fst_coll_nres_spec[le, refine_vcg]: "op_image_fst_coll_nres X \<le> SPEC (\<lambda>R. R = fst ` X)"
  unfolding op_image_fst_coll_nres_def
  apply (refine_vcg FORWEAK_mono_rule[where I="\<lambda>it s. fst ` \<Union>it \<subseteq> s \<and> s \<subseteq> fst ` X"])
    apply auto
    apply force
  apply force
  done
definition [simp]: "op_image_fst_coll = (`) fst"
sublocale autoref_op_pat_def op_image_fst_coll_nres .
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

lemma real_autoref[autoref_rules]:
  "(real, real) \<in> nat_rel \<rightarrow> rnv_rel"
  by auto

definition "fst_safe_coll XS = do {
    C \<leftarrow> op_image_fst_coll_nres XS;
    mk_safe_coll (C:::clw_rel appr_rel)
  }"
sublocale autoref_op_pat_def fst_safe_coll .
schematic_goal fst_safe_coll_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::executable_euclidean_space) D"
  assumes [autoref_rules]: "(XSi, (XS::'n c1_info set)) \<in> clw_rel appr1_rel"
  shows "(nres_of ?r, fst_safe_coll $ XS) \<in> \<langle>clw_rel sappr_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding fst_safe_coll_def
  including art
  by (autoref_monadic)
concrete_definition fst_safe_coll_impl for XSi uses fst_safe_coll_impl
lemmas [autoref_rules] = fst_safe_coll_impl.refine
lemma fst_safe_coll[le, refine_vcg]:
  "wd TYPE('a) \<Longrightarrow>
      fst_safe_coll (X::('a::executable_euclidean_space*'c) set) \<le> SPEC (\<lambda>R. R = fst ` X \<and> fst ` X \<subseteq> Csafe)"
  unfolding fst_safe_coll_def
  by refine_vcg

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

lemma map_option_autoref[autoref_rules]: "(map_option, map_option) \<in> (A \<rightarrow> B) \<rightarrow> \<langle>A\<rangle>option_rel \<rightarrow> \<langle>B\<rangle>option_rel"
  by (rule map_option_param)

definition [refine_vcg_def]:
  "vec1reps X = do {
    XS \<leftarrow> sets_of_coll X;
    FORWEAK XS (RETURN (Some op_empty_coll))
      (\<lambda>x. do {
        x \<leftarrow> vec1rep x;
        RETURN (map_option mk_coll x:::\<langle>clw_rel appr_rel\<rangle>option_rel)
      })
      (\<lambda>a b.
        case (a, b) of (Some a, Some b) \<Rightarrow> RETURN (Some (b \<union> a))
        | _ \<Rightarrow> RETURN None)
  }"
sublocale autoref_op_pat_def vec1reps .

lemma vec1reps[THEN order_trans, refine_vcg]: "vec1reps CX \<le> SPEC (\<lambda>R. case R of None \<Rightarrow> True | Some X \<Rightarrow> X = vec1_of_flow1 ` CX)"
  unfolding vec1reps_def
  apply (refine_vcg FORWEAK_mono_rule[where
        I="\<lambda>XS R. case R of None \<Rightarrow> True | Some R \<Rightarrow> vec1_of_flow1 ` (\<Union>XS) \<subseteq> R \<and> R \<subseteq> vec1_of_flow1 ` CX"])
  by (auto simp:  split: option.splits) force+

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

lemma closed_ivl_rel[intro, simp]:  "(a, b) \<in> lvivl_rel \<Longrightarrow> closed b"
  by (auto simp: ivl_rel_def br_def set_of_ivl_def)

lemma inner_eq_zero_abs_BasisI:
  "\<bar>y\<bar> \<in> Basis \<Longrightarrow> b \<in> Basis \<Longrightarrow> \<bar>y\<bar> \<noteq> b \<Longrightarrow> y \<bullet> b = 0"
  for b y::"'a::executable_euclidean_space"
  by (metis abs_inner inner_Basis linorder_not_le order_refl zero_less_abs_iff)

lemma abs_in_Basis_absE:
  fixes x y::"'a::executable_euclidean_space"
  assumes "abs y \<in> Basis"
  obtains "abs y = y" | "abs y = -y"
proof -
  have "abs y = (\<Sum>i\<in>Basis. (abs (y \<bullet> i)) *\<^sub>R i)"
    by (simp add: euclidean_representation abs_inner[symmetric] assms)
  also have "Basis = insert (abs y) (Basis - {abs y})" using assms by auto
  also have "(\<Sum>i\<in>insert \<bar>y\<bar> (Basis - {\<bar>y\<bar>}). \<bar>y \<bullet> i\<bar> *\<^sub>R i) = \<bar>y \<bullet> \<bar>y\<bar>\<bar> *\<^sub>R \<bar>y\<bar>"
    apply (subst sum.insert)
    using assms
    by (auto simp: abs_inner[symmetric] inner_Basis if_distribR if_distrib
        cong: if_cong)
  finally have "\<bar>y\<bar> = \<bar>y \<bullet> \<bar>y\<bar>\<bar> *\<^sub>R \<bar>y\<bar>" by simp
  moreover have "\<dots> = y \<or> \<dots> = - y"
    using assms
    by (auto simp: abs_real_def algebra_simps  intro!: euclidean_eqI[where 'a='a]
        simp: inner_Basis inner_eq_zero_abs_BasisI split: if_splits)
  ultimately consider "\<bar>y\<bar> = y" | "\<bar>y\<bar> = - y" by auto
  then show ?thesis
    by (cases; rule that)
qed

lemma abs_in_BasisE:
  fixes x y::"'a::executable_euclidean_space"
  assumes "abs y \<in> Basis"
  obtains i where "i \<in> Basis" "y = i" | i where "i \<in> Basis" "y = -i"
proof -
  from abs_in_Basis_absE[OF assms]
  consider "\<bar>y\<bar> = y" | "\<bar>y\<bar> = - y"
    by auto
  then show ?thesis
  proof cases
    case 1 with assms have "abs y \<in> Basis" "y = abs y" by auto
    then show ?thesis ..
  next
    case 2
    with assms have "abs y \<in> Basis" "y = - abs y" by auto
    then show ?thesis ..
  qed
qed

definition subset_spec_plane :: "'a::executable_euclidean_space set \<Rightarrow> 'a sctn \<Rightarrow> bool nres" where
"subset_spec_plane X sctn = do {
    CHECKs ''subset_spec_plane: not in Basis'' (abs (normal sctn) \<in> set Basis_list);
    (i, s) \<leftarrow> ivl_rep X;
    RETURN (i \<bullet> normal sctn = pstn sctn \<and> s \<bullet> normal sctn = pstn sctn)
  }"
sublocale autoref_op_pat_def subset_spec_plane .
schematic_goal subset_spec_plane_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a) D"
  assumes [autoref_rules]: "(Xi, X::'a::executable_euclidean_space set) \<in> lvivl_rel" "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(nres_of ?R, subset_spec_plane $ X $ sctn) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding subset_spec_plane_def
  by (autoref_monadic)
concrete_definition subset_spec_plane_impl for Xi sctni uses subset_spec_plane_impl
lemmas [autoref_rules] = subset_spec_plane_impl.refine
lemma subset_spec_plane[le, refine_vcg]:
  "subset_spec_plane X sctn \<le> SPEC (\<lambda>b. b \<longrightarrow> X \<subseteq> plane_of sctn)"
  unfolding subset_spec_plane_def
  by (refine_vcg) (auto simp: plane_of_def eucl_le[where 'a='a] dest!: bspec elim!: abs_in_BasisE)

lemma subset_spec_coll_refine[le, refine_vcg]: "subset_spec_coll X Y \<le> subset_spec X Y"
  by (auto simp: subset_spec_def)

lemma ivl_rep_of_set_coll_refine[le, refine_vcg]: "ivl_rep_of_set_coll X \<le> ivl_rep_of_set X"
  by simp

lemma sbelow_sctns_coll_refine_lemma[le, refine_vcg]: "sbelow_sctns_coll a b \<le> sbelow_sctns a b"
  by simp

lemma
  eventually_in_planerectI:
  fixes n::"'a::executable_euclidean_space"
  assumes "abs n \<in> Basis"
  assumes "{l .. u} \<subseteq> plane n c" "l \<le> u"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> i \<noteq> abs n \<Longrightarrow> l \<bullet> i < x \<bullet> i"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> i \<noteq> abs n \<Longrightarrow> x \<bullet> i < u \<bullet> i"
  shows "\<forall>\<^sub>F x in at x within plane n c. x \<in> {l .. u}"
proof -
  have "\<forall>\<^sub>F x in at x within plane n c. x \<in> plane n c"
    unfolding eventually_at_filter
    by simp
  then have "\<forall>\<^sub>F x in at x within plane n c. l \<bullet> abs n \<le> x \<bullet> abs n \<and> x \<bullet> abs n \<le> u \<bullet> abs n"
    apply eventually_elim
    using assms(1,2,3)
    by (auto simp: elim!: abs_in_BasisE)
  moreover
  {
    fix i assume that: "i \<in> Basis" "i \<noteq> abs n"
    have "\<forall>\<^sub>F x in at x within plane n c. l \<bullet> i < x \<bullet> i" "\<forall>\<^sub>F x in at x within plane n c. x \<bullet> i < u \<bullet> i"
      by (auto intro!: order_tendstoD assms tendsto_eq_intros that)
    then have "\<forall>\<^sub>F x in at x within plane n c. l \<bullet> i < x \<bullet> i \<and> x \<bullet> i < u \<bullet> i"
      by eventually_elim auto
  } then have "\<forall>\<^sub>F x in at x within plane n c. \<forall>i \<in> Basis - {abs n}. l \<bullet> i < x \<bullet> i \<and> x \<bullet> i < u \<bullet> i"
    by (auto intro!: eventually_ball_finite)
  then have "\<forall>\<^sub>F x in at x within plane n c. \<forall>i \<in> Basis - {abs n}. l \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> u \<bullet> i"
    by eventually_elim (auto intro!: less_imp_le)
  ultimately
  have "\<forall>\<^sub>F x in at x within plane n c. \<forall>i\<in>Basis. l \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> u \<bullet> i"
    by eventually_elim auto
  then show ?thesis
    by eventually_elim (auto simp: eucl_le[where 'a='a])
qed

definition "op_eventually_within_sctn X sctn S = do {
    (l, u) \<leftarrow> ivl_rep S;
    (xl, xu) \<leftarrow> ivl_rep_of_set X;
    CHECKs ''op_eventually_within_sctn: empty ivl'' (l \<le> u);
    CHECKs ''op_eventually_within_sctn: not in Basis'' (abs (normal sctn) \<in> set Basis_list);
    b \<leftarrow> subset_spec_plane S sctn;
    CHECKs ''op_eventually_within_sctn: subset_spec_plane 1'' b;
    b \<leftarrow> subset_spec_plane ({xl .. xu}:::lvivl_rel) sctn;
    CHECKs ''op_eventually_within_sctn: subset_spec_plane 2'' b;
    RETURN (b \<and> (\<forall>i \<in> set Basis_list - {abs (normal sctn)}. l \<bullet> i < xl \<bullet> i \<and> xu \<bullet> i < u \<bullet> i))
  }"
sublocale autoref_op_pat_def op_eventually_within_sctn .

lemma mem_ivl_euclI: "k \<in> {c..d::'x::ordered_euclidean_space}" if "\<And>i. i \<in> Basis \<Longrightarrow> c \<bullet> i \<le> k \<bullet> i" "\<And>i. i \<in> Basis \<Longrightarrow> k \<bullet> i \<le> d \<bullet> i"
  using that
  by (auto simp: eucl_le[where 'a='x])

lemma op_eventually_within_sctn[le, refine_vcg]:
  "op_eventually_within_sctn X sctn S \<le>
    SPEC (\<lambda>b. b \<longrightarrow> (\<forall>x \<in> X. x \<in> S \<and> (\<forall>\<^sub>F x in at x within plane_of sctn. x \<in> S)))"
  unfolding op_eventually_within_sctn_def
  apply refine_vcg
  unfolding plane_of_def autoref_tag_defs
  apply (safe intro!: eventually_in_planerectI mem_ivl_euclI)
  subgoal premises prems for a b c d e f g h i j k B
  proof cases
    assume "B = \<bar>normal sctn\<bar>"
    moreover
    have "c \<in> plane (normal sctn) (pstn sctn)" "k \<in> plane (normal sctn) (pstn sctn)"
      using prems by auto
    ultimately show "c \<bullet> B \<le> k \<bullet> B" using \<open>\<bar>normal sctn\<bar> \<in> set Basis_list\<close>
      by (auto simp: elim!: abs_in_Basis_absE)
  next
    assume B: "B \<noteq> \<bar>normal sctn\<bar>"
    have "k \<bullet> B \<in> {g \<bullet> B .. h  \<bullet> B}"
      using \<open>k \<in> X\<close> \<open>X \<subseteq> {g..h}\<close> \<open>B \<in> Basis\<close> by (auto simp: eucl_le[where 'a='a])
    with B prems show ?thesis by (auto dest!: bspec elim!: abs_in_Basis_absE)
  qed
  subgoal premises prems for a b c d e f g h i j k B
  proof cases
    assume "B = \<bar>normal sctn\<bar>"
    moreover
    have "d \<in> plane (normal sctn) (pstn sctn)" "k \<in> plane (normal sctn) (pstn sctn)"
      using prems by auto
    ultimately show "d \<bullet> B \<ge> k \<bullet> B" using \<open>\<bar>normal sctn\<bar> \<in> set Basis_list\<close>
      by (auto simp: elim!: abs_in_Basis_absE)
  qed (use prems in \<open>auto elim!: abs_in_BasisE simp: eucl_le[where 'a='a] dest!: bspec set_mp\<close>)
  subgoal by simp
  subgoal by (auto elim!: abs_in_BasisE simp: eucl_le[where 'a='a] dest!: bspec set_mp)
  subgoal by (auto elim!: abs_in_BasisE simp: eucl_le[where 'a='a] dest!: bspec set_mp)
  done

schematic_goal op_eventually_within_sctn_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(Xi, X::'a set) \<in> appr_rel" "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel" "(Si, S) \<in> lvivl_rel"
  shows "(nres_of ?R, op_eventually_within_sctn $ X $ sctn $ S) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding op_eventually_within_sctn_def
  by (autoref_monadic)
concrete_definition op_eventually_within_sctn_impl for Xi sctni Si uses op_eventually_within_sctn_impl
lemmas [autoref_rules] = op_eventually_within_sctn_impl.refine

lemma Let_unit: "Let (x::unit) f = f ()"
  by auto
lemma CHECK_no_text: "CHECKs (x#ys) a = CHECKs [] a"
  by auto

lemma frontier_above_halfspace:
  "normal sctn \<noteq> 0 \<Longrightarrow> frontier (above_halfspace sctn) = plane_of sctn"
  using frontier_halfspace_ge[of "normal sctn" "pstn sctn"]
  by (auto simp: halfspace_simps plane_of_def inner_commute)

lemma
  flowpipe_subset:
  assumes "flowpipe X0 hl hu CX X1"
    and subs: "Y0 \<subseteq> X0" "hl \<le> il" "il \<le> iu" "iu \<le> hu" "CX \<subseteq> CY" "X1 \<subseteq> Y1"
    and safe: "fst ` CY \<union> fst ` Y1 \<subseteq> Csafe"
  shows "flowpipe Y0 il iu CY Y1"
proof -
  from assms(1) have fp: "0 \<le> hl" "hl \<le> hu" "fst ` X0 \<subseteq> Csafe" "fst ` CX \<subseteq> Csafe" "fst ` X1 \<subseteq> Csafe"
    "\<forall>(x0, d0)\<in>X0. \<forall>h\<in>{hl..hu}. h \<in> existence_ivl0 x0 \<and> (flow0 x0 h, Dflow x0 h o\<^sub>L d0) \<in> X1 \<and> (\<forall>h'\<in>{0..h}. (flow0 x0 h', Dflow x0 h' o\<^sub>L d0) \<in> CX)"
    by (auto simp: flowpipe_def)
  then show ?thesis
    unfolding flowpipe_def
    apply safe
    subgoal using subs by auto
    subgoal using subs by auto
    subgoal using subs by fastforce
    subgoal using safe by auto
    subgoal using safe by auto
    subgoal using subs by fastforce
    subgoal using subs fp by fastforce
    subgoal for x0 d0 h h'
      using subs fp
      apply -
      apply (rule set_mp, assumption)
      apply (drule bspec)
       apply (rule set_mp; assumption)
      apply safe
      apply (drule bspec[where x=h], force)
      apply auto
      done
    done
qed

lemma poincare_mapsto_unionI:
  assumes "poincare_mapsto P r U t d"
  assumes "poincare_mapsto P s U u e"
  shows "poincare_mapsto P (r \<union> s) U (t \<union> u) (d \<union> e)"
  using assms
  apply (auto simp: poincare_mapsto_def)
  subgoal
    apply (drule bspec, assumption)
    by auto
  subgoal by fastforce
  done

lemma sabove_not_le_halfspace:
  "x \<in> sabove_halfspace sctn \<longleftrightarrow> \<not> le_halfspace sctn x"
  by (auto simp: sabove_halfspace_def le_halfspace_def gt_halfspace_def)

lemma (in c1_on_open_euclidean) flowsto_self:\<comment> \<open>TODO: move!\<close>
  "0 \<in> T \<Longrightarrow> X0 \<subseteq> Z \<Longrightarrow> fst ` X0 \<subseteq> X \<Longrightarrow> flowsto X0 T Y Z"
  by (force simp: flowsto_def intro!: bexI[where x=0])

lemma (in c1_on_open_euclidean) flowpipe_imp_flowsto:\<comment> \<open>TODO: move!\<close>
  assumes "flowpipe X0 hl hu CX Y" "hl > 0"
  shows "flowsto X0 {0<..hl} CX Y"
  using assms
  by (fastforce simp: flowsto_def flowpipe_def open_segment_eq_real_ivl
      dest: bspec[where x=hl]
      intro!: bexI[where x=hl])

lemma flowsto_source_unionI:
  "flowsto X0 T A B \<Longrightarrow> flowsto Z T A B \<Longrightarrow> flowsto (X0 \<union> Z) T A B"
  by (fastforce simp: flowsto_def dest: bspec)

definition "do_intersection_spec S guards ivl sctn X0 = (\<lambda>(PS, CXS).
    poincare_mapsto {x \<in> ivl. x \<in> plane_of sctn} X0 S CXS PS \<and>
      CXS \<inter> guards = {} \<and>
      CXS \<inter> ivl \<inter> plane_of sctn = {} \<and>
      fst ` PS \<inter> guards = {} \<and>
      fst ` PS \<subseteq> {x \<in> ivl. x \<in> plane_of sctn} \<and>
      fst ` PS \<union> CXS \<subseteq> Csafe \<and>
      0 \<notin> (\<lambda>x. ode x \<bullet> normal sctn) ` fst ` PS \<and>
      (\<forall>x\<in>PS. (\<forall>\<^sub>F x in at (fst x) within plane_of sctn. x \<in> ivl)))"

lemma poincare_mapsto_subset:
  "poincare_mapsto P X0 U CX1 X1 \<Longrightarrow> X0' \<subseteq> X0 \<Longrightarrow> X1 \<subseteq> X2 \<Longrightarrow> CX1 \<subseteq> CX2 \<Longrightarrow> fst ` X2 \<subseteq> Csafe
  \<Longrightarrow> poincare_mapsto P X0' U CX2 X2"
  by (force simp: poincare_mapsto_def)

lemma PDP_abs_lemma:
  fixes n::"'a::executable_euclidean_space"
  assumes "abs n \<in> Basis"
  shows
    "(x, d - (blinfun_scaleR_left (f (x)) o\<^sub>L (blinfun_scaleR_left (inverse (f x \<bullet> n)) o\<^sub>L (blinfun_inner_left n o\<^sub>L d)))) =
     (x, d - (blinfun_scaleR_left (f (x)) o\<^sub>L (blinfun_scaleR_left (inverse (f x \<bullet> (abs n))) o\<^sub>L (blinfun_inner_left (abs n) o\<^sub>L d))))"
proof -
  consider "n \<in> Basis" | "- n \<in> Basis"
    using abs_in_Basis_absE[OF assms] assms by metis
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by simp
  next
    case 2
    define i where "i = -n"
    with 2 have "i \<in> Basis" "n = -i"
      by (auto simp: )
    then show ?thesis
      by (auto simp: inverse_eq_divide intro!: blinfun_eqI blinfun.bilinear_simps euclidean_eqI[where 'a='a])
  qed
qed

lemma abs_in_BasisI:
  "\<bar>n\<bar> \<in> Basis" if n: "n \<in> Basis \<or> - n \<in> Basis" for n::"'a::executable_euclidean_space"
proof -
  consider "n \<in> Basis" | "- n \<in> Basis"
    using n by auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by simp
  next
    case 2
    define i where "i = -n"
    with 2 have "i \<in> Basis" "n = -i"
      by (auto simp: )
    then show ?thesis
      by (auto simp: inverse_eq_divide intro!: blinfun_eqI blinfun.bilinear_simps euclidean_eqI[where 'a='a])
  qed
qed

abbreviation "inter_sbelows X sctns \<equiv> mk_inter X (sbelow_halfspaces sctns)"

definition "list_of_appr1 X = fst X @ the_default [] (snd X)"

definition print_set1::"bool \<Rightarrow> 'a set \<Rightarrow> unit" where "print_set1 _ _ = ()"
sublocale autoref_op_pat_def print_set1 .
lemma print_set_impl1[autoref_rules]:
  shows "(\<lambda>a s. printing_fun optns a (list_of_appr1 s), print_set1) \<in> bool_rel \<rightarrow> A \<rightarrow> Id"
  by auto
definition trace_set1::"string\<Rightarrow>'a set option\<Rightarrow>unit" where "trace_set1 _ _ = ()"
sublocale autoref_op_pat_def trace_set1 .
lemma trace_set1_impl1[autoref_rules]:
  shows "(\<lambda>s a. tracing_fun optns s (map_option list_of_appr1 a), trace_set1) \<in> string_rel \<rightarrow> \<langle>A\<rangle>option_rel \<rightarrow> Id"
  by auto

definition "nonzero_component_within ivl sctn PDP = do {
  fPDP \<leftarrow> mk_safe (fst ` PDP);
  F \<leftarrow> ode_set (set_of_sappr fPDP);
  nonzero_component ''solve_poincare_map: not nonzero!'' F (normal sctn);
  op_eventually_within_sctn (op_image_fst PDP) sctn ivl
}"
sublocale autoref_op_pat_def nonzero_component_within .
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
lemma nonzero_component_within[le, refine_vcg]:
  assumes wdp: "vwd_step (TYPE('n::enum))"
  notes [refine_vcg] = vwd_step vwd_stepD[OF wdp]
  shows "nonzero_component_within ivl sctn (PDP::'n eucl1 set) \<le> SPEC (\<lambda>b.
    (b \<longrightarrow> (\<forall>x\<in>PDP. fst x \<in> ivl \<and> (\<forall>\<^sub>F x in at (fst x) within plane_of sctn. x \<in> ivl))) \<and>
    fst ` PDP \<subseteq> Csafe \<and>
    (\<forall>x\<in>PDP. ode (fst x) \<bullet> normal sctn \<noteq> 0))"
  unfolding nonzero_component_within_def
  by refine_vcg auto

lemma sv_plane_rel[relator_props]: "single_valued A \<Longrightarrow> single_valued (\<langle>A\<rangle>plane_rel)"
  by (auto simp: plane_rel_def intro!: relator_props)
lemma sv_below_rel[relator_props]: "single_valued A \<Longrightarrow> single_valued (\<langle>A\<rangle>below_rel)"
  by (auto simp: below_rel_def intro!: relator_props)
lemma sv_sbelow_rel[relator_props]: "single_valued A \<Longrightarrow> single_valued (\<langle>A\<rangle>sbelow_rel)"
  by (auto simp: sbelow_rel_def intro!: relator_props)
lemma sv_sbelows_rel[relator_props]: "single_valued A \<Longrightarrow> single_valued (\<langle>A\<rangle>sbelows_rel)"
  by (auto simp: sbelows_rel_def intro!: relator_props)

definition "do_intersection_invar guards GUARDS ivl sctn X \<equiv> \<lambda>(X', T, PS, PS2, CXS, intersects, inside).
  (inside \<longrightarrow>
          (fst ` X \<inter> GUARDS = {} \<and>
          fst ` X \<subseteq> sbelow_halfspace sctn \<and>
          ivl \<subseteq> plane_of sctn \<and>
          fst ` X \<subseteq> CXS \<and>
          fst ` PS \<union> fst ` PS2 \<union> CXS \<union> fst ` X' \<subseteq> Csafe \<and>
          T \<subseteq> nonneg_reals \<and>
          (\<not>intersects \<longrightarrow> (fst ` X' \<inter> plane_of sctn = {} \<and> T = pos_reals)) \<and>
          CXS \<subseteq> (sbelow_halfspace sctn - guards) \<and>
          X' \<subseteq> (- guards) \<times> UNIV \<and>
          fst ` (PS \<union> PS2) \<inter> guards = {} \<and>
          (0 \<notin> (\<lambda>x. ode x \<bullet> normal sctn) ` fst ` (PS \<union> PS2)) \<and>
          ((\<forall>x\<in>PS \<union> PS2. (\<forall>\<^sub>F x in at (fst x) within plane_of sctn. x \<in> ivl))) \<and>
          (\<exists>A B. X = A \<union> B \<and>
            flowsto A T (CXS \<times> UNIV) (X' \<inter> (sbelow_halfspace sctn) \<times> UNIV) \<and>
            poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} B UNIV CXS PS \<and>
            poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} B UNIV CXS PS2)))"

definition "do_intersection_body GUARDS ivl sctn h \<equiv> \<lambda>(X, T, PDPS, PDPS2, CXS, _, _).
  do {
    (_, _, CX', X') \<leftarrow> choose_step1 (X:::appr1_rel) (h:::rnv_rel);
    let _ = trace_set1 (ST ''interpolated step during intersection:'') (Some (CX'));
    let _ = print_set1 True (CX');
    let _ = trace_set1 (ST ''step during intersection:'') (Some (X'));
    let _ = print_set1 False (X');
    CHECKs (ST ''unnormal intersection'') (abs (normal sctn) \<in> set Basis_list);
    CPDP \<leftarrow> solve_poincare_plane (abs (normal sctn)) CX';
    let _ = trace_set1 (ST ''CPDP: '') (Some CPDP);
    let _ = print_set1 False (CPDP);
    (PDP, PDP2) \<leftarrow> inter_sctn1_spec CPDP sctn;
    b1 \<leftarrow> disjoints_spec (mk_coll (op_image_fst X')) (GUARDS);
    b2 \<leftarrow> disjoints_spec (mk_coll (op_image_fst CX')) (GUARDS);
    b3 \<leftarrow> disjoints_spec (mk_coll (op_image_fst PDP)) (GUARDS);
    b4 \<leftarrow> disjoints_spec (mk_coll (op_image_fst PDP2)) (GUARDS);
    CHECKs (ST ''do_intersection: hitting several planes :('') (b1 \<and> b2 \<and> b3 \<and> b4);
    intersects \<leftarrow> intersects_spec (op_image_fst X') sctn;
    CX's \<leftarrow> mk_safe (op_image_fst CX');
    c1 \<leftarrow> nonzero_component_within ivl sctn PDP;
    c2 \<leftarrow> nonzero_component_within ivl sctn PDP2;
    RETURN (X', pos_reals:::\<langle>Id\<rangle>phantom_rel, mk_coll PDP \<union> PDPS,
      mk_coll PDP2 \<union> PDPS2,
      mk_coll (inter_sbelows (CX's:::sappr_rel) {sctn}) \<union> CXS, intersects, c1 \<and> c2)
  }"
sublocale autoref_op_pat_def do_intersection_body .

abbreviation "intersection_STATE_rel \<equiv>
  (appr1_rel \<times>\<^sub>r \<langle>Id\<rangle>phantom_rel \<times>\<^sub>r clw_rel appr1_rel \<times>\<^sub>r clw_rel appr1_rel \<times>\<^sub>r
    clw_rel (\<langle>sappr_rel, \<langle>lv_rel\<rangle>sbelows_rel\<rangle>inter_rel) \<times>\<^sub>r bool_rel \<times>\<^sub>r bool_rel)"
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
  including art
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

definition "do_intersection guards ivl sctn (X::'n::enum eucl1 set) (h::real) =
  do {
    ASSUME (closed ivl);
    sp \<leftarrow> subset_spec_plane ivl sctn;
    sX \<leftarrow> mk_safe (op_image_fst (X:::appr1_rel));
    GUARDS \<leftarrow> unintersect_coll guards;
    a \<leftarrow> sbelow_sctn (op_image_fst X) sctn;
    b \<leftarrow> disjoints_spec (mk_coll (op_image_fst X)) GUARDS;
    let inside = sp \<and> a \<and> b; \<comment> \<open>this is a bit of a hack: if the \<open>ivl\<close> is not subset of the plane,\<close>
      \<comment> \<open>then do not do intersections\<close>
    (X, T, PDPS, PDPS2, CXS, intersects, inside) \<leftarrow>
      WHILE\<^bsup>do_intersection_invar guards GUARDS ivl sctn X\<^esup>
      (\<lambda>(X, T, PDPS, PDPS2, CXS, intersects, inside). intersects \<and> inside)
      (do_intersection_body GUARDS ivl sctn h)
      (X, nonneg_reals:::\<langle>Id\<rangle>phantom_rel, op_empty_coll:::clw_rel appr1_rel::'n eucl1 set,
        op_empty_coll:::clw_rel appr1_rel::'n eucl1 set,
        mk_coll (inter_sbelows (sX:::sappr_rel) {sctn}), True, inside);
    a \<leftarrow> above_sctn (op_image_fst X) sctn;
    b \<leftarrow> subset_spec_coll (op_image_fst_coll PDPS) ivl;
    b2 \<leftarrow> subset_spec_coll (op_image_fst_coll PDPS2) ivl;
    RETURN (inside \<and> b \<and> b2 \<and> a, PDPS, PDPS2, CXS)
  }"
sublocale autoref_op_pat_def do_intersection .

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
     \<langle>lv_rel\<rangle>plane_rel\<rangle>Refine_Rigorous_Numerics.inter_rel) \<rightarrow>
  \<langle>lv_rel\<rangle>ivl_rel \<rightarrow>
  \<langle>lv_rel\<rangle>sctn_rel \<rightarrow>
  appr1_rel \<rightarrow> rnv_rel \<rightarrow>
  \<langle>bool_rel \<times>\<^sub>r clw_rel appr1_rel \<times>\<^sub>r clw_rel appr1_rel \<times>\<^sub>r
   clw_rel
    (\<langle>sappr_rel,
     \<langle>lv_rel\<rangle>sbelows_rel\<rangle>Refine_Rigorous_Numerics.inter_rel)\<rangle>nres_rel"
  if "DIM_precond TYPE((real, 'a::enum) vec) D" "var.ncc_precond TYPE((real, 'a) vec)"
    "var.ncc_precond TYPE((real, 'a) vec \<times> ((real, 'a) vec, 'a) vec)"
  by (intro fun_relI do_intersection_impl.refine[OF that])

lemma flowsto_poincareD:
  assumes f: "flowsto X0 T CX X1"
  assumes X1: "fst ` X1 \<subseteq> P"
  assumes P: "(P \<times> UNIV) \<inter> CX = {}" "closed P"
  assumes pos: "\<And>t. t \<in> T \<Longrightarrow> t > 0"
  assumes x0: "x0 \<in> fst ` X0"
  assumes "fst ` X1 \<subseteq> K"
  shows returns_to_flowstoI: "returns_to P x0"
    and poincare_map_mem_flowstoI: "poincare_map P x0 \<in> K"
proof -
  from x0 obtain d where x0d: "(x0, d) \<in> X0" by auto
  from flowstoE[OF f x0d] obtain h
    where h:
      "h \<in> T"
      "h \<in> existence_ivl0 x0"
      "(flow0 x0 h, Dflow x0 h o\<^sub>L d) \<in> X1"
      and CX: "\<And>h'. h' \<in> {0<--<h} \<Longrightarrow> (flow0 x0 h', Dflow x0 h' o\<^sub>L d) \<in> CX"
    by auto
  have "h > 0" by (auto intro!: pos h)
  have "flow0 x0 h \<in> P" using X1 h by auto
  have "\<forall>\<^sub>F t in at_right 0. t \<in> {0<..<h}"
    using order_tendstoD(2)[OF tendsto_ident_at \<open>0 < h\<close>, of "{0<..}"]
    by (auto simp: eventually_at_filter)
  then have "\<forall>\<^sub>F t in at_right 0. flow0 x0 t \<in> fst ` CX"
    by eventually_elim (use CX \<open>0 < h\<close> open_segment_eq_real_ivl in auto)
  then have evnP: "\<forall>\<^sub>F t in at_right 0. flow0 x0 t \<notin> P"
    by eventually_elim (use P in force)
  from \<open>h > 0\<close> h(2) \<open>flow0 x0 h \<in> P\<close> evnP P(2) show "returns_to P x0"
    by (rule returns_toI)
  have nin_P: "0 < s \<Longrightarrow> s < h \<Longrightarrow> flow0 x0 s \<notin> P" for s
    using CX[of s] P by (auto simp: open_segment_eq_real_ivl)
  have "return_time P x0 = h"
    using h X1
    by (auto intro!: return_time_eqI \<open>0 < h\<close> h assms simp: nin_P)
  then have "poincare_map P x0 = flow0 x0 h" by (auto simp: poincare_map_def)
  also have "\<dots> \<in> fst ` X1" using h by auto
  also note \<open>_ \<subseteq> K\<close>
  finally show "poincare_map P x0 \<in> K" .
qed

lemma
  inner_abs_Basis_eq_zero_iff:
  "abs n \<in> Basis \<Longrightarrow> x \<bullet> \<bar>n\<bar> = 0 \<longleftrightarrow> x \<bullet> n = 0" for n::"'a::executable_euclidean_space"
  by (auto simp: elim!: abs_in_BasisE)

lemmas [simp] = sbelow_halfspaces_insert

lemma Int_Un_eq_emptyI: "a \<inter> (b \<union> c) = {}" if "a \<inter> b = {}" "a \<inter> c = {}"
  using that by auto

lemma do_intersection_invar_inside:
  "do_intersection_invar guards b ivl sctn X (e, f, m, n, p, q, True) \<Longrightarrow>
  fst ` e \<subseteq> sabove_halfspace sctn \<Longrightarrow>
  fst ` mn \<subseteq> ivl \<Longrightarrow>
  mn = m \<or> mn = n \<Longrightarrow>
  do_intersection_spec UNIV guards ivl sctn X (mn, p)"
  subgoal premises prems
  proof -
    from prems have e: "e \<inter> sbelow_halfspace sctn \<times> UNIV = {}"
      by (auto simp: halfspace_simps plane_of_def)
    with prems(1) have
      "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} X UNIV p m"
      "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} X UNIV p n"
      "e \<inter> sbelow_halfspace sctn \<times> UNIV = {}"
      "fst ` X \<inter> b = {}"
      "fst ` X \<subseteq> sbelow_halfspace sctn"
      "ivl \<subseteq> plane (normal sctn) (pstn sctn)"
      "fst ` X \<subseteq> p"
      "fst ` m \<subseteq> Csafe"
      "fst ` n \<subseteq> Csafe"
      "p \<subseteq> Csafe"
      "fst ` e \<subseteq> Csafe"
      "f \<subseteq> {0..}"
      "p \<subseteq> sbelow_halfspace sctn - guards"
      "e \<subseteq> (- guards) \<times> UNIV"
      "fst ` (m \<union> n) \<inter> guards = {}"
      "0 \<notin> (\<lambda>x. ode x \<bullet> normal sctn) ` fst ` (m \<union> n)"
      "\<forall>x\<in>m \<union> n. \<forall>\<^sub>F x in at (fst x) within plane (normal sctn) (pstn sctn). x \<in> ivl"
      by (auto simp: do_intersection_invar_def do_intersection_spec_def plane_of_def)
    then show ?thesis
      using prems(2-)
      by (auto simp: do_intersection_spec_def plane_of_def halfspace_simps)
  qed
  done

lemma do_intersection_body_spec:
  fixes guards::"'n::enum rvec set"
  assumes invar: "do_intersection_invar guards GUARDS ivl sctn X (X', T, PS, PS2, i, True, True)"
    and wdp[refine_vcg]: "vwd_step TYPE('n)"
    and X: "fst ` X \<subseteq> Csafe"
    and ivl: "closed ivl" and GUARDS: "guards \<subseteq> GUARDS"
  notes [refine_vcg] = vwd_step vwd_stepD[OF wdp]
  shows "do_intersection_body GUARDS ivl sctn h (X', T, PS, PS2, i, True, True) \<le>
    SPEC (do_intersection_invar guards GUARDS ivl sctn X)"
proof -
  from invar
  obtain A B where AB: "fst ` (A \<union> B) \<inter> GUARDS = {} "
    "fst ` (A \<union> B) \<subseteq> sbelow_halfspace sctn "
    "ivl \<subseteq> plane_of sctn "
    "fst ` (A \<union> B) \<subseteq> i "
    "fst ` PS \<subseteq> Csafe "
    "fst ` PS2 \<subseteq> Csafe "
    "i \<subseteq> Csafe "
    "fst ` X' \<subseteq> Csafe "
    "T \<subseteq> {0..} "
    "i \<subseteq> sbelow_halfspace sctn - guards "
    "X' \<subseteq> (- guards) \<times> UNIV "
    "fst ` (PS \<union> PS2) \<inter> guards = {} "
    "0 \<notin> (\<lambda>x. ode x \<bullet> normal sctn) ` fst ` (PS \<union> PS2) "
    "\<forall>x\<in>PS \<union> PS2. \<forall>\<^sub>F x in at (fst x) within plane_of sctn. x \<in> ivl "
    "X = A \<union> B "
    "flowsto A T (i \<times> UNIV) (X' \<inter> sbelow_halfspace sctn \<times> UNIV) "
    "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} B UNIV i PS "
    "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} B UNIV i PS2"
    by (auto simp: do_intersection_invar_def)
  show ?thesis
    unfolding do_intersection_body_def do_intersection_invar_def
    apply simp
    apply (refine_vcg, clarsimp_all)
    subgoal using AB by (auto simp: )
    subgoal using AB by (auto simp: )
    subgoal using AB by (auto simp: )
    subgoal
      apply (rule conjI)
      subgoal using AB by auto\<comment> \<open>unnecessarily slow\<close>
      subgoal using AB by fastforce
      done
    subgoal using AB by (auto simp: )
    subgoal using AB by (auto simp: )
    subgoal using AB by (auto simp: )
    subgoal by (auto dest!: flowpipe_safeD)
    subgoal
      apply safe
      subgoal using AB GUARDS by auto
      subgoal using AB by auto
      subgoal using AB by auto
      subgoal using AB GUARDS by auto
      subgoal using AB by auto
      subgoal using AB by auto
      done
    subgoal using AB GUARDS by auto
    subgoal using AB GUARDS by auto\<comment> \<open>unnecessarily slow\<close>
    subgoal using AB GUARDS by auto
    subgoal premises prems for GUARDS b c d e f g h i j k l m n p q
      using \<open>\<forall>x\<in>PS \<union> PS2. \<forall>\<^sub>F x in at (fst x) within plane_of sctn. x \<in> ivl\<close>
      using \<open>\<forall>x\<in>d. fst x \<in> ivl \<and> (\<forall>\<^sub>F x in at (fst x) within plane_of sctn. x \<in> ivl)\<close>
      using \<open>\<forall>x\<in>e. fst x \<in> ivl \<and> (\<forall>\<^sub>F x in at (fst x) within plane_of sctn. x \<in> ivl)\<close>
        \<open>(p, q) \<in> d \<or> (p, q) \<in> PS \<or> (p, q) \<in> e \<or> (p, q) \<in> PS2\<close>
      by (auto dest!: bspec[where x="(p, q)"])
    subgoal for h' CX' PDP PDP' PDP'' b1 b2 b3 b4 b5 b6 Y b7 b8
    proof -
      assume normal_Basis: "\<bar>normal sctn\<bar> \<in> Basis"
        and inter_empties: "fst ` Y \<inter> GUARDS = {}" "fst ` CX' \<inter> GUARDS = {}"
        "fst ` PDP' \<inter> GUARDS = {}" "fst ` PDP'' \<inter> GUARDS = {}"
        and h': "0 < h'" "h' \<le> h"
        and safe: "fst ` PDP \<subseteq> Csafe" "fst ` CX' \<subseteq> Csafe"
        "fst ` PDP' \<subseteq> Csafe"
        "fst ` PDP'' \<subseteq> Csafe"
        and PDP:
        "\<forall>(x,d)\<in>CX'. (x,
            d - (blinfun_scaleR_left (ode x) o\<^sub>L
                  (blinfun_scaleR_left (inverse (ode x \<bullet> \<bar>normal sctn\<bar>)) o\<^sub>L
                  (blinfun_inner_left \<bar>normal sctn\<bar> o\<^sub>L d))))
               \<in> PDP"
        and PDP': "PDP \<inter> plane_of sctn \<times> UNIV \<subseteq> PDP'"
        and PDP'': "PDP \<inter> plane_of sctn \<times> UNIV \<subseteq> PDP''"
        and evin:
        "\<forall>x\<in>PDP'. fst x \<in> ivl \<and> (\<forall>\<^sub>F x in at (fst x) within plane_of sctn. x \<in> ivl)"
        "\<forall>x\<in>PDP''. fst x \<in> ivl \<and> (\<forall>\<^sub>F x in at (fst x) within plane_of sctn. x \<in> ivl)"
        and through: "\<forall>(x, d)\<in>PDP. ode x \<bullet> \<bar>normal sctn\<bar> \<noteq> 0"
        "\<forall>x\<in>PDP'. ode (fst x) \<bullet> normal sctn \<noteq> 0"
        "\<forall>x\<in>PDP''. ode (fst x) \<bullet> normal sctn \<noteq> 0"
        and plane:
        "fst ` PDP' \<subseteq> plane_of sctn"
        "fst ` PDP'' \<subseteq> plane_of sctn"
        and flowpipe: "flowpipe X' h' h' CX' Y"

      from flowpipe
      have 1: "flowpipe (X' \<inter> (sbelow_halfspace sctn) \<times> UNIV) h' h' CX' Y"
        by (rule flowpipe_subset) (use flowpipe in \<open>auto dest!: flowpipe_safeD\<close>)
      have 2: "fst ` (X' \<inter> (sbelow_halfspace sctn) \<times> UNIV) \<inter> {x. pstn sctn \<le> x \<bullet> normal sctn} = {}"
        by (auto simp: halfspace_simps plane_of_def)
      from normal_Basis have 3: "normal sctn \<noteq> 0"
        by (auto simp: )
      note 4 = \<open>closed ivl\<close>
      from \<open>ivl \<subseteq> plane_of sctn\<close> have 5: "ivl \<subseteq> plane (normal sctn) (pstn sctn)"
        by (auto simp: plane_of_def)
      have 6: "(x, d) \<in> CX' \<Longrightarrow> x \<in> plane (normal sctn) (pstn sctn) \<Longrightarrow>
          (x, d - (blinfun_scaleR_left (ode x) o\<^sub>L
                   (blinfun_scaleR_left (inverse (ode x \<bullet> normal sctn)) o\<^sub>L (blinfun_inner_left (normal sctn) o\<^sub>L d))))
          \<in> PDP' \<inter> PDP''" for x d
        unfolding PDP_abs_lemma[OF normal_Basis]
        apply (drule PDP[rule_format, of "(x, d)", unfolded split_beta' fst_conv snd_conv])
        using PDP' PDP''
        by (auto simp: plane_of_def)
      from normal_Basis through
      have 7: "(x, d) \<in> PDP' \<Longrightarrow> ode x \<bullet> normal sctn \<noteq> 0" for x d
        by (auto elim!: abs_in_BasisE)
      have 8: "(x, d) \<in> PDP' \<Longrightarrow> x \<in> ivl" for x d
        using evin by auto
      have 9: "(x, d) \<in> PDP' \<Longrightarrow> \<forall>\<^sub>F x in at x within plane (normal sctn) (pstn sctn). x \<in> ivl" for x d
        using evin by (auto simp add: plane_of_def)
      obtain X1 X2
        where X1X2: "X' \<inter> sbelow_halfspace sctn \<times> UNIV = X1 \<union> X2"
          and X1: "flowsto X1 {0<..h'} (CX' \<inter> {x. x \<bullet> normal sctn < pstn sctn} \<times> UNIV)
                      (CX' \<inter> {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} \<times> UNIV)"
          and X2: "flowsto X2 {h'..h'} (CX' \<inter> {x. x \<bullet> normal sctn < pstn sctn} \<times> UNIV)
                      (Y \<inter> {x. x \<bullet> normal sctn < pstn sctn} \<times> UNIV)"
          and P: "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} X1 UNIV
                      (fst ` CX' \<inter> {x. x \<bullet> normal sctn < pstn sctn}) (PDP' \<inter> PDP'')"
        by (rule flowpipe_split_at_above_halfspace[OF 1 2 3 4 5 6 7 8 9]) (auto simp: Ball_def)
    from \<open>flowsto A _ _ _\<close>[unfolded X1X2]
    obtain p1 p2 where p1p2: "A = p1 \<union> p2" and p1: "flowsto p1 T (i \<times> UNIV) X1" and p2: "flowsto p2 T (i \<times> UNIV) X2"
      by (rule flowsto_unionE)
    have "A \<union> B = p2 \<union> (p1 \<union> B)" using \<open>A = p1 \<union> p2\<close>
      by auto
    moreover
    from flowsto_trans[OF p2 X2]
    have "flowsto p2 {0<..} ((fst ` CX' \<inter> (sbelow_halfspace sctn) \<union> i) \<times> UNIV)
           (Y \<inter> (sbelow_halfspace sctn) \<times> UNIV)"
      apply (rule flowsto_subset)
      subgoal by (auto simp: halfspace_simps)
      subgoal using h' \<open>T \<subseteq> _\<close> by (auto simp: halfspace_simps intro!: add_nonneg_pos)
      subgoal
        using flowpipe_source_subset[OF 1, unfolded X1X2] X1X2
        apply auto
        by (auto simp: halfspace_simps)
      subgoal by (auto simp: halfspace_simps)
      done
    moreover
    have cls: "closed {x \<in> ivl. x \<bullet> normal sctn = pstn sctn}"
      by (rule closed_levelset_within continuous_intros \<open>closed ivl\<close>)+
    from flowsto_trans[OF p1 X1]
    have ftt: "flowsto p1 ({s + t |s t. s \<in> T \<and> t \<in> {0<..h'}})
       (i \<times> UNIV \<union> CX' \<inter> {x. x \<bullet> normal sctn < pstn sctn} \<times> UNIV \<union> X1 \<inter> X1)
       (X1 - X1 \<union> CX' \<inter> {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} \<times> UNIV)"
      by auto
    from X1X2 have X1_sb: "X1 \<subseteq> sbelow_halfspace sctn \<times> UNIV" by auto
    have "{x \<in> ivl. x \<bullet> normal sctn = pstn sctn} \<times> UNIV \<inter> (i \<times> UNIV \<union> CX' \<inter> {x. x \<bullet> normal sctn < pstn sctn} \<times> UNIV \<union> X1) = {}"
      apply (intro Int_Un_eq_emptyI)
      subgoal using \<open>i \<subseteq> sbelow_halfspace sctn - guards\<close> by (auto simp: halfspace_simps)
      subgoal by (auto simp: halfspace_simps)
      subgoal using X1_sb by (auto simp: halfspace_simps)
      done
    then have inter_empty:
      "{x \<in> ivl. x \<bullet> normal sctn = pstn sctn} \<times> UNIV \<inter> (i \<times> UNIV \<union> CX' \<inter> {x. x \<bullet> normal sctn < pstn sctn} \<times> UNIV \<union> X1 \<inter> X1) = {}"
      by auto
    have p1ret: "returns_to {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} x"
      and p1pm: "poincare_map {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} x \<in> fst ` (PDP' \<inter> PDP'')"
      if "(x, d) \<in> p1" for x d
       apply (rule flowsto_poincareD[OF ftt _ inter_empty _ _ _ order_refl])
      subgoal by auto
      subgoal by fact
      subgoal using \<open>T \<subseteq> _\<close> by auto
      subgoal using that by auto
      subgoal
        apply (rule flowsto_poincareD[OF ftt _ inter_empty])
        subgoal by auto
        subgoal by fact
        subgoal using \<open>T \<subseteq> _\<close> by auto
        subgoal using that by auto
        subgoal using 6 by force
        done
      done
    have crt: "isCont (return_time {x \<in> ivl. x \<bullet> normal sctn - pstn sctn = 0}) x" if "(x, d) \<in> p1" for x d
      apply (rule return_time_isCont_outside[where Ds="\<lambda>_. blinfun_inner_left (normal sctn)"])
      subgoal by (simp add: p1ret[OF that])
      subgoal by fact
      subgoal by (auto intro!: derivative_eq_intros)
      subgoal by simp
      subgoal apply simp
        using p1pm[OF that]
        by (auto dest!: 7)
      subgoal
        using p1pm[OF that]
        by (auto dest!: 9 simp: eventually_at_filter)
      subgoal
        using \<open>fst ` (A \<union> B) \<subseteq> sbelow_halfspace sctn\<close> that p1p2
        by (auto simp: halfspace_simps)
      done
    have pmij: "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} p1 UNIV
        (fst ` (i \<times> UNIV \<union> X1) \<union> fst ` CX' \<inter> {x. x \<bullet> normal sctn < pstn sctn}) (PDP' \<inter> PDP'')"
      apply (rule flowsto_poincare_trans[OF \<open>flowsto _ _ _ X1\<close> P])
      subgoal using \<open>T \<subseteq> {0..}\<close> by auto
      subgoal by auto
      subgoal
        using \<open>i \<subseteq> sbelow_halfspace sctn - guards\<close> X1X2
        by (force simp: halfspace_simps)
      subgoal by fact
      subgoal for x d using crt by simp
      subgoal by auto
      done
    from pmij have "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} p1 UNIV (fst ` (i \<times> UNIV \<union> X1) \<union> fst ` CX' \<inter> {x. x \<bullet> normal sctn < pstn sctn}) PDP'"
      apply (rule poincare_mapsto_subset)
      using \<open>fst ` PDP' \<subseteq> Csafe\<close>
      by auto
    from this \<open>poincare_mapsto _ _ _ i PS\<close>
    have "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} (p1 \<union> B) UNIV
      ((fst ` (i \<times> UNIV \<union> X1) \<union> fst ` CX' \<inter> {x. x \<bullet> normal sctn < pstn sctn}) \<union> i) (PDP' \<union> PS)"
      by (intro poincare_mapsto_unionI) (auto simp: plane_of_def)
    then have "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} (p1 \<union> B) UNIV (fst ` CX' \<inter> sbelow_halfspace sctn \<union> i) (PDP' \<union> PS)"
      apply (rule poincare_mapsto_subset)
      subgoal by auto
      subgoal by auto
      subgoal
        using flowpipe_source_subset[OF 1, unfolded X1X2] X1X2 
        apply (auto simp: halfspace_simps subset_iff)
        done
      subgoal using safe \<open>fst ` PS \<subseteq> Csafe\<close> by auto
      done
    moreover
    from pmij have "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} p1 UNIV (fst ` (i \<times> UNIV \<union> X1) \<union> fst ` CX' \<inter> {x. x \<bullet> normal sctn < pstn sctn}) PDP''"
      apply (rule poincare_mapsto_subset)
      using \<open>fst ` PDP'' \<subseteq> Csafe\<close>
      by auto
    from this \<open>poincare_mapsto _ _ _ i PS2\<close>
    have "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} (p1 \<union> B) UNIV
      ((fst ` (i \<times> UNIV \<union> X1) \<union> fst ` CX' \<inter> {x. x \<bullet> normal sctn < pstn sctn}) \<union> i) (PDP'' \<union> PS2)"
      by (intro poincare_mapsto_unionI) (auto simp: plane_of_def)
    then have "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} (p1 \<union> B) UNIV (fst ` CX' \<inter> sbelow_halfspace sctn \<union> i) (PDP'' \<union> PS2)"
      apply (rule poincare_mapsto_subset)
      subgoal by auto
      subgoal by auto
      subgoal
        using flowpipe_source_subset[OF 1, unfolded X1X2] X1X2
        apply (auto simp: halfspace_simps subset_iff)
        done
      subgoal using safe \<open>fst ` PS2 \<subseteq> Csafe\<close> by auto
      done
    ultimately
    show "\<exists>A B. X = A \<union> B \<and>
        flowsto A {0<..} ((fst ` CX' \<inter> sbelow_halfspace sctn \<union> i) \<times> UNIV) (Y \<inter> sbelow_halfspace sctn \<times> UNIV) \<and>
        poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} B UNIV (fst ` CX' \<inter> sbelow_halfspace sctn \<union> i) (PDP' \<union> PS) \<and>
        poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} B UNIV (fst ` CX' \<inter> sbelow_halfspace sctn \<union> i) (PDP'' \<union> PS2)"
      unfolding \<open>X = A \<union> B\<close> by blast
    qed
    done
qed

lemma
  do_intersection_spec[le, refine_vcg]:
  assumes wdp: "vwd_step (TYPE('n::enum))"
  notes [refine_vcg] = vwd_step vwd_stepD[OF wdp]
  shows "do_intersection guards ivl sctn (X::'n eucl1 set) h \<le>
    SPEC (\<lambda>(inside, P, P2, CX). (inside \<longrightarrow>
      (do_intersection_spec UNIV guards ivl sctn X (P, CX) \<and>
       do_intersection_spec UNIV guards ivl sctn X (P2, CX)) \<and> fst ` X \<subseteq> CX))"
  using assms
  unfolding do_intersection_def autoref_tag_defs
  apply (refine_vcg, clarsimp_all)
  subgoal
    unfolding do_intersection_invar_def
    apply clarsimp
    apply (intro conjI)
       apply force
      apply force
     apply force
    apply (rule exI[where x=X])
    apply (rule exI[where x="{}"])
    by (auto intro!: flowsto_self)
  subgoal by (rule do_intersection_body_spec)
  subgoal by (rule do_intersection_invar_inside, assumption) auto
  subgoal by (rule do_intersection_invar_inside, assumption) auto
  subgoal by (auto simp: plane_of_def halfspace_simps do_intersection_invar_def)
  done

lemma inform_autoref[autoref_rules]:
  "(\<lambda>x. Max (abs ` set x), (infnorm::'a::executable_euclidean_space\<Rightarrow>real)) \<in> lv_rel \<rightarrow> rnv_rel"
  apply (auto simp: lv_rel_def br_def infnorm_def eucl_of_list_inner
      intro!: Max_eqI le_cSup_finite)
  subgoal for a y
    apply (rule exI[where x="Basis_list ! index a y"])
    by (auto simp: eucl_of_list_inner)
  subgoal
    apply (rule set_rev_mp)
     apply (rule closed_contains_Sup)
       apply (auto intro!: finite_imp_closed)
    apply (rule imageI)
    apply (auto simp: eucl_of_list_inner)
    done
  done

definition "split_spec_param1 X = do {
    vX \<leftarrow> vec1rep X;
    case vX of None \<Rightarrow> do {
      (a, b) \<leftarrow> split_spec_param D (fst ` X);
      RETURN (a \<times> UNIV, b \<times> UNIV)
    }
    | Some X \<Rightarrow> do {
      (a, b) \<leftarrow> split_spec_param D X;
      RETURN (op_image_flow1_of_vec1 a, op_image_flow1_of_vec1 b)
    }
  }"
sublocale autoref_op_pat_def split_spec_param1 .

schematic_goal split_spec_param1_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::enum rvec) D"
  assumes [autoref_rules]: "(Xi, X) \<in> appr1_rel"
  notes [autoref_post_simps] = case_prod_eta
  notes [autoref_rules] = autoref_parameters2
  shows "(nres_of (?f), split_spec_param1 (X::'a eucl1 set)) \<in> \<langle>appr1_rel \<times>\<^sub>r appr1_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding split_spec_param1_def
  including art
  by (autoref_monadic)
concrete_definition split_spec_param1_impl for Xi uses split_spec_param1_impl
lemma split_spec_param1_refine[autoref_rules]:
  "DIM_precond TYPE('n::enum rvec) D \<Longrightarrow>
    (\<lambda>Xi. nres_of (split_spec_param1_impl Xi), split_spec_param1::_\<Rightarrow>(_\<times>'n eucl1 set)nres)
    \<in> appr1_rel \<rightarrow> \<langle>appr1_rel \<times>\<^sub>r appr1_rel\<rangle>nres_rel "
  using split_spec_param1_impl.refine by force

lemma mem_flow1_of_vec1_image_iff[simp]:
  "(c, d) \<in> flow1_of_vec1 ` a \<longleftrightarrow> vec1_of_flow1 (c, d) \<in> a"
  by force

lemma mem_vec1_of_flow1_image_iff[simp]:
  "(c, d) \<in> vec1_of_flow1 ` a \<longleftrightarrow> flow1_of_vec1 (c, d) \<in> a"
  by force

lemma split_spec_param1[le, refine_vcg]: "split_spec_param1 X \<le> SPEC (\<lambda>(A, B). X \<subseteq> A \<union> B)"
  unfolding split_spec_param1_def
  apply (refine_vcg)
  apply (auto simp add: subset_iff split: option.splits)
  by (metis flow1_of_vec1_vec1_of_flow1 surjective_pairing)

lemma [autoref_rules]:
  "(pre_collect_granularity, pre_collect_granularity) \<in> reach_optns_rel \<rightarrow> rnv_rel"
  by auto


abbreviation "iplane_rel \<equiv> \<lambda>A. \<langle>A, \<langle>lv_rel\<rangle>plane_rel\<rangle>inter_rel"
abbreviation "isbelow_rel \<equiv> \<lambda>A. \<langle>A, \<langle>lv_rel\<rangle>sbelow_rel\<rangle>inter_rel"
abbreviation "isbelows_rel \<equiv> \<lambda>A. \<langle>A, \<langle>lv_rel\<rangle>sbelows_rel\<rangle>inter_rel"

definition [refine_vcg_def]: "get_plane X = SPEC (\<lambda>sctn. X = plane_of sctn)"
sublocale autoref_op_pat_def get_plane .
lemma [autoref_rules]: "(RETURN, get_plane) \<in> \<langle>A\<rangle>plane_rel \<rightarrow> \<langle>\<langle>A\<rangle>sctn_rel\<rangle>nres_rel"
  by (auto simp: plane_rel_def get_plane_def nres_rel_def dest!: brD intro!: RETURN_SPEC_refine)

lemma [autoref_op_pat del]: "{} \<equiv> OP op_empty_default" "{} \<equiv> OP op_empty_coll"
  and [autoref_op_pat_def del]: "get_inter p \<equiv> OP (get_inter p)"
  by simp_all

lemma do_intersection_spec_empty:
  "X = {} \<Longrightarrow> Y = {} \<Longrightarrow> do_intersection_spec S sctns ivl sctn X ({}, Y)"
  by (auto simp: do_intersection_spec_def halfspaces_union)

lemma do_intersection_spec_subset:
  "do_intersection_spec S osctns ivl csctns Y (a, b) \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> do_intersection_spec S osctns ivl csctns X (a, b)"
  by (auto simp: do_intersection_spec_def halfspaces_union intro: flowsto_subset poincare_mapsto_subset)

lemma do_intersection_spec_union:
  "do_intersection_spec S osctns ivl csctns a (b, c) \<Longrightarrow>
   do_intersection_spec S osctns ivl csctns f (g, h) \<Longrightarrow>
   do_intersection_spec S osctns ivl csctns (a \<union> f) (b \<union> g, c \<union> h)"
  by (auto simp: do_intersection_spec_def intro!: poincare_mapsto_unionI)

abbreviation iinfo_rel :: "('c \<times> 'a set) set \<Rightarrow> ((real \<times> 'c) \<times> 'a::real_normed_vector set) set"
where "iinfo_rel \<equiv> \<lambda>s. \<langle>rnv_rel, s\<rangle>info_rel"

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

lemma cancel_times_UNIV_subset: "A \<times> UNIV \<subseteq> B \<times> UNIV \<longleftrightarrow> A \<subseteq> B"
  by auto

lemma
  is_empty_info_rel_autoref[autoref_rules]:
  "GEN_OP ie is_empty (A \<rightarrow> bool_rel) \<Longrightarrow> (\<lambda>x. ie(snd x), is_empty) \<in> \<langle>R, A\<rangle>info_rel \<rightarrow> bool_rel"
  by (force simp: info_rel_def br_def dest: fun_relD)

lemma is_empty_appr1_rel[autoref_rules]:
  "(\<lambda>_. False, is_empty) \<in> appr1_rel \<rightarrow> bool_rel"
  by (auto simp: appr1_rel_internal set_rel_br) (auto simp: appr_rel_br br_def)

definition "split_spec_param1e X = do {
    ((l, u), Y) \<leftarrow> scaleR2_rep X;
    (a, b) \<leftarrow> split_spec_param1 Y;
    a \<leftarrow> scaleRe_ivl_spec l u a;
    b \<leftarrow> scaleRe_ivl_spec l u b;
    RETURN (a, b)
  }"
sublocale autoref_op_pat_def split_spec_param1e .

definition "scaleR2_rep_coll X = do {
  XS \<leftarrow> sets_of_coll X;
  FORWEAK XS (RETURN ((0, 0), op_empty_coll)) (\<lambda>X. do {
    ((l, u), Y) \<leftarrow> scaleR2_rep X;
    RETURN ((l, u), mk_coll Y)
  }) (\<lambda>((l, u), Y) ((l', u'), Y'). RETURN ((inf l' l, sup u' u), Y' \<union> Y))
  }"
sublocale autoref_op_pat_def scaleR2_rep_coll .

lemma scaleR2_subset:
  assumes "x \<in> scaleR2 i' j' k'"
  assumes "i \<le> i'" "j' \<le> j" "k' \<subseteq> k"
  shows "x \<in> scaleR2 i j k"
  using assms
  by (force simp: scaleR2_def vimage_def image_def)

lemma scaleR2_rep_of_coll[le, refine_vcg]:
  "scaleR2_rep_coll X \<le> SPEC (\<lambda>((l, u), Y). X \<subseteq> scaleR2 l u Y)"
  unfolding scaleR2_rep_coll_def
  apply (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs ((l, u), Y). \<Union>Xs \<subseteq> scaleR2 l u Y"])
   apply (auto intro: scaleR2_subset)
  apply (rule scaleR2_subset)
     apply (rule set_mp)
      apply assumption
     apply auto
  done

lemma [autoref_rules]:
  "(sup, sup) \<in> ereal_rel \<rightarrow> ereal_rel \<rightarrow> ereal_rel"
  "(inf, inf) \<in> ereal_rel \<rightarrow> ereal_rel \<rightarrow> ereal_rel"
  by auto

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
  by (autoref_monadic)
concrete_definition split_spec_param1e_impl for Xi uses split_spec_param1e_impl
lemma split_spec_param1e_refine[autoref_rules]:
  "DIM_precond TYPE('n::enum rvec) D \<Longrightarrow>
    (\<lambda>Xi. nres_of (split_spec_param1e_impl Xi), split_spec_param1e::_\<Rightarrow>(_\<times>'n eucl1 set)nres)
    \<in> \<langle>appr1_rel\<rangle>scaleR2_rel \<rightarrow> \<langle>\<langle>appr1_rel\<rangle>scaleR2_rel \<times>\<^sub>r \<langle>appr1_rel\<rangle>scaleR2_rel\<rangle>nres_rel"
  using split_spec_param1e_impl.refine by force

lemma split_spec_param1e[le, refine_vcg]: "split_spec_param1e X \<le> SPEC (\<lambda>(A, B). X \<subseteq> A \<union> B)"
  unfolding split_spec_param1e_def
  apply (refine_vcg)
  apply clarsimp
    apply (thin_tac "_ \<noteq> {}")
  apply (auto simp: scaleR2_def vimage_def image_def)
  apply (rule exI, rule conjI, assumption, rule conjI, assumption)
  apply (auto simp: split_beta')
  apply (drule_tac x = x in spec)
  apply auto
  by (metis (no_types, lifting) UnE prod.sel(1) prod.sel(2) subset_eq)

abbreviation "reducer_rel \<equiv> \<langle>Id::'b rel\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> rl_rel \<rightarrow> bool_rel"

definition "reduce_spec1 C X = do {
  vX \<leftarrow> vec1rep X;
  case vX of None \<Rightarrow> do {
    X \<leftarrow> reduce_spec C (fst ` X);
    RETURN (X \<times> UNIV)
  }
  | Some vX \<Rightarrow> do {
    vX \<leftarrow> reduce_spec C vX;
    RETURN (flow1_of_vec1 ` vX)
  }
}"
sublocale autoref_op_pat_def reduce_spec1 .
schematic_goal reduce_spec1_impl:
  "(nres_of ?r, reduce_spec1 C X) \<in> \<langle>appr1_rel\<rangle>nres_rel"
  if [autoref_rules]: "(Xi, X::'n eucl1 set) \<in> appr1_rel" "(Ci, C) \<in> reducer_rel"
    and [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) D"
  unfolding reduce_spec1_def
  by (autoref_monadic)
concrete_definition reduce_spec1_impl for Ci Xi uses reduce_spec1_impl
lemma reduce_spec1_impl_refine[autoref_rules]:
  "(\<lambda>C x. nres_of (reduce_spec1_impl C x), reduce_spec1::_\<Rightarrow>'n eucl1 set\<Rightarrow>_) \<in>
      reducer_rel \<rightarrow> appr1_rel \<rightarrow> \<langle>appr1_rel\<rangle>nres_rel"
  if "DIM_precond TYPE((real, 'n::enum) vec) D"
  using reduce_spec1_impl.refine that
  by force
lemma reduce_spec1[le, refine_vcg]: "reduce_spec1 ro X \<le> SPEC (\<lambda>R. X \<subseteq> R)"
  unfolding reduce_spec1_def
  by refine_vcg auto
definition "reduce_spec1e C X = do {
  ((l, u), X) \<leftarrow> scaleR2_rep X;
  X \<leftarrow> reduce_spec1 C X;
  scaleRe_ivl_spec l u X
}"
sublocale autoref_op_pat_def reduce_spec1e .
schematic_goal reduce_spec1e_impl:
  "(nres_of ?r, reduce_spec1e C X) \<in> \<langle>\<langle>appr1_rel\<rangle>scaleR2_rel\<rangle>nres_rel"
  if [autoref_rules]: "(Xi, X::'n eucl1 set) \<in> \<langle>appr1_rel\<rangle>scaleR2_rel" "(Ci, C) \<in> reducer_rel"
  and [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) D"
  unfolding reduce_spec1e_def
  including art
  by (autoref_monadic)
concrete_definition reduce_spec1e_impl for Ci Xi uses reduce_spec1e_impl
lemma reduce_spec1e_impl_refine[autoref_rules]:
  "(\<lambda>C x. nres_of (reduce_spec1e_impl C x), reduce_spec1e::_\<Rightarrow>'n eucl1 set\<Rightarrow>_) \<in>
      reducer_rel \<rightarrow> \<langle>appr1_rel\<rangle>scaleR2_rel \<rightarrow> \<langle>\<langle>appr1_rel\<rangle>scaleR2_rel\<rangle>nres_rel"
  if "DIM_precond TYPE((real, 'n::enum) vec) D"
  using reduce_spec1e_impl.refine that
  by force
lemma reduce_spec1e[le, refine_vcg]: "reduce_spec1e ro X \<le> SPEC (\<lambda>R. X \<subseteq> R)"
  unfolding reduce_spec1e_def
  by refine_vcg (auto simp: scaleR2_def image_def vimage_def, force)

definition split_under_threshold::"'b reach_options \<Rightarrow> real \<Rightarrow> 'n::enum eucl1 set \<Rightarrow> 'n eucl1 set nres" where
  "split_under_threshold ro th X = do {
    (_, Ys) \<leftarrow> WHILE\<^bsup>\<lambda>(Xs, Ys). X \<subseteq> Xs \<union> Ys\<^esup> (\<lambda>(Xs, Ys). \<not> op_coll_is_empty Xs) (\<lambda>(Xs, Ys). do {
      (X, Xs') \<leftarrow> (split_spec_coll (Xs:::clw_rel (\<langle>appr1_rel\<rangle>scaleR2_rel)):::\<langle>\<langle>appr1_rel\<rangle>scaleR2_rel \<times>\<^sub>r clw_rel (\<langle>appr1_rel\<rangle>scaleR2_rel)\<rangle>nres_rel);
      w \<leftarrow> width_spec (op_image_fste X:::appr_rel);
      if w \<le> th then RETURN (Xs', mk_coll X \<union> Ys)
      else do {
        X \<leftarrow> reduce_spec1e (pre_split_reduce ro) X;
        (a, b) \<leftarrow> split_spec_param1e (X:::\<langle>appr1_rel\<rangle>scaleR2_rel);
        RETURN (mk_coll (a:::\<langle>appr1_rel\<rangle>scaleR2_rel) \<union> mk_coll (b:::\<langle>appr1_rel\<rangle>scaleR2_rel) \<union> Xs', Ys)
      }
    }) (X:::clw_rel (\<langle>appr1_rel\<rangle>scaleR2_rel), op_empty_coll:::clw_rel (\<langle>appr1_rel\<rangle>scaleR2_rel));
    RETURN Ys
  }"
sublocale autoref_op_pat_def split_under_threshold .

schematic_goal split_under_threshold_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) D"
  assumes [autoref_rules]: "(ti, t) \<in> reach_optns_rel" "(thi, th) \<in> rnv_rel" "(Xi, X) \<in> clw_rel (\<langle>appr1_rel\<rangle>scaleR2_rel)"
  shows "(nres_of (?x dres), split_under_threshold $ t $ th $ (X::'n eucl1 set)) \<in> \<langle>clw_rel (\<langle>appr1_rel\<rangle>scaleR2_rel)\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding split_under_threshold_def
  including art
  by (autoref_monadic)
concrete_definition split_under_threshold_impl for ti thi Xi uses split_under_threshold_impl
lemmas [autoref_rules] = split_under_threshold_impl.refine

lemma split_spec_coll_spec[le,refine_vcg]:
  "split_spec_coll X \<le> SPEC (\<lambda>(A, B). X \<subseteq> A \<union> B)"
  unfolding split_spec_coll_def
  by (refine_vcg)

lemma split_under_threshold[le, refine_vcg]:
  "split_under_threshold t th X \<le> SPEC (\<lambda>R. X \<subseteq> R)"
  unfolding split_under_threshold_def autoref_tag_defs
  by (refine_vcg) auto

definition "step_split (roptns::'b reach_options) (X::'n::enum eucl1 set) =
  do {
    X \<leftarrow> reduce_spec1e (pre_split_reduce roptns) X;
    (a, b) \<leftarrow> split_spec_param1e (X:::appr1e_rel);
    _ \<leftarrow> mk_safe (op_image_fste a);
    _ \<leftarrow> mk_safe (op_image_fste b);
    width_X \<leftarrow> width_spec (op_image_fste X:::appr_rel);
    wa \<leftarrow> width_spec (op_image_fste a:::appr_rel);
    wb \<leftarrow> width_spec (op_image_fste b:::appr_rel);
    let _ = trace_set (ST ''splitting: '' @ show (lfloat10 width_X) @ ST ''-->'' @ show (lfloat10 wa) @
      ST '', ''  @ show (lfloat10 wb)) (None::'n::enum eucl1 set option);
    RETURN (mk_coll a \<union> mk_coll b)
  }"
sublocale autoref_op_pat_def step_split .

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

lemma step_split[le, refine_vcg]:
  "wd TYPE((real, 'n::enum) vec) \<Longrightarrow> step_split roptns (X::'n eucl1 set) \<le> SPEC (\<lambda>Y. X \<subseteq> Y \<and> fst ` Y \<subseteq> Csafe)"
  unfolding step_split_def
  by (refine_vcg refine_vcg) auto

definition "width_spec_appr1 X = do {
    vX \<leftarrow> vec1rep X;
    case vX of None \<Rightarrow> width_spec (fst ` X:::appr_rel)
    | Some vX \<Rightarrow> width_spec (vX:::appr_rel)
  }"
sublocale autoref_op_pat_def width_spec_appr1 .
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

definition "tolerate_error Y E = \<^cancel>\<open>do {
    vY \<leftarrow> vec1rep Y;
    vE \<leftarrow> vec1rep E;
    case (vY, vE) of (None, None) \<Rightarrow>\<close>
      do {
        (ei, es) \<leftarrow> ivl_rep_of_set (fst ` E);
        (yi, ys) \<leftarrow> ivl_rep_of_set (fst ` Y);
        let ea = sup (abs ei) (abs es);
        let ya = sup (abs yi) (abs ys);

        let errtol = sup (adaptive_rtol optns *\<^sub>R ya) (adaptive_atol optns *\<^sub>R sum_list Basis_list);
        RETURN (ea \<le> errtol, infnorm ea)
      \<^cancel>\<open>}
    | (Some vY, Some vE) \<Rightarrow>
      do {
        (ei, es) \<leftarrow> ivl_rep_of_set (vE);
        (yi, ys) \<leftarrow> ivl_rep_of_set (vY);
        let ea = sup (abs ei) (abs es);
        let ya = sup (abs yi) (abs ys);
        let errtol = sup (adaptive_rtol optns *\<^sub>R ya) (adaptive_atol optns *\<^sub>R sum_list Basis_list);
        RETURN (ea \<le> errtol, infnorm ea)
      }
    | _ \<Rightarrow> do {CHECKs ''tolerate_error: different representations???'' False; SUCCEED}\<close>
  }"
sublocale autoref_op_pat_def tolerate_error .
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

lemma tolerate_error_SPEC[THEN order_trans, refine_vcg]:
  "tolerate_error Y E \<le> SPEC (\<lambda>b. True)"
  unfolding tolerate_error_def
  by refine_vcg


definition "adapt_stepsize_fa e h' =
  Num (float_of h') * floatarith.Powr (Num (float_of (adaptive_rtol optns)) / Num (float_of e))
                                (inverse (Num (float_of (method_id optns) + 1)))"
sublocale autoref_op_pat_def adapt_stepsize_fa .
lemma [autoref_rules]: "(adapt_stepsize_fa, adapt_stepsize_fa) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> Id"
  by auto
lemma interpret_adapt_stepsize_fa:
  "interpret_floatarith (adapt_stepsize_fa e h') []
    = float_of h' * (float_of(adaptive_rtol optns) / float_of e) powr (1 / (float_of (method_id optns) + 1))"
  by (auto simp: inverse_eq_divide adapt_stepsize_fa_def)

definition "choose_step1e X h = do {
    ((l, u), X) \<leftarrow> scaleR2_rep X;
    (h', error, CY, Y) \<leftarrow> choose_step1 X h;
    Y \<leftarrow> scaleRe_ivl_spec l u Y;
    RETURN (h', error, fst ` CY, Y)
  }"
sublocale autoref_op_pat_def choose_step1e .
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

lemma flowpipe_scaleR2I: "flowpipe (scaleR2 x1 x2 bc) x1a x1a (fst ` aca \<times> UNIV) (scaleR2 x1 x2 bca)"
  if "flowpipe (bc) x1a x1a (fst ` aca \<times> UNIV) (bca)"
  using that
  apply (auto simp: flowpipe_def scaleR2_def)
  apply (drule bspec, assumption)
  apply (auto simp: image_def vimage_def )
  apply (rule exI, rule conjI, assumption, rule conjI, assumption)
  apply (rule bexI) prefer 2 apply assumption
  by (auto simp: scaleR_blinfun_compose_right)

lemma choose_step1e_flowpipe[le, refine_vcg]:
  assumes vwd[refine_vcg]: "vwd_step TYPE('n::enum)"
  shows "choose_step1e (X0::'n eucl1 set) h \<le> SPEC (\<lambda>(h', _, RES_ivl, RES::'n eucl1 set).
      0 < h' \<and> h' \<le> h \<and> flowpipe X0 h' h' (RES_ivl \<times> UNIV) RES)"
  unfolding choose_step1e_def
  apply (refine_vcg)
    apply (auto intro: flowpipe_scaleR2I)
  apply (erule contrapos_np)
  apply (auto intro!: flowpipe_scaleR2I)
  apply (rule flowpipe_subset)
         apply assumption
        apply (auto dest!: flowpipe_safeD)
  done

definition "list_of_appr1e X = fst (snd X) @ the_default [] (snd (snd X)) @
  (let (l, u) = fst X;
    roer = (\<lambda>x. if x = - \<infinity> then FloatR 1 (-88) else if x = \<infinity> then FloatR 1 88 else real_of_ereal x)
  in
    appr_of_ivl [roer l] [roer u]
    )"

definition print_set1e::"bool \<Rightarrow> 'a set \<Rightarrow> unit" where "print_set1e _ _ = ()"
sublocale autoref_op_pat_def print_set1 .
lemma print_set_impl1e[autoref_rules]:
  shows "(\<lambda>a s. printing_fun optns a (list_of_appr1e s), print_set1e) \<in> bool_rel \<rightarrow> A \<rightarrow> Id"
  by auto
definition trace_set1e::"string\<Rightarrow>'a set option\<Rightarrow>unit" where "trace_set1e _ _ = ()"
sublocale autoref_op_pat_def trace_set1 .
lemma trace_set1_impl1e[autoref_rules]:
  shows "(\<lambda>s a. tracing_fun optns s (map_option (list_of_appr1e) a), trace_set1e) \<in> string_rel \<rightarrow> \<langle>A\<rangle>option_rel \<rightarrow> Id"
  by auto
definition "step_adapt_time (X::'n::enum eucl1 set) h =
  do {
    let X0 = fst ` X;
    _ \<leftarrow> mk_safe (X0:::appr_rel);
    (h', error, CY, Y) \<leftarrow> choose_step1e X h;
    (te, e) \<leftarrow> tolerate_error Y error;
    let _ = trace_set1 (ST ''discrete time step: stepsize = '' @ show (lfloat10 h)) (None::'n eucl1 set option);
    let _ = trace_set1 (ST ''discrete time step: stepsize' = '' @ show (lfloat10 h')) (None::'n eucl1 set option);
    let _ = trace_set1 (ST ''error estimation: '' @ show (lfloat10 e)) (None::'n eucl1 set option);
    if \<not> te
    then do {
      let _ = trace_set (ST ''revoking step'') (None::'n eucl1 set option);
      RETURN (0, fst ` X, X, 3 * h' / 2 / 2)
    } else do {
      let _ = trace_set1 (ST ''error OK, step_adapt_time stepped '') (None::'n eucl1 set option);
      let _ = trace_set (ST ''interpolated step:'') (Some (CY));
      let _ = print_set True CY;
      let _ = trace_set1e (ST ''discrete step:'') (Some (Y));
      let _ = print_set1e False Y;
      case approx (precision optns) (adapt_stepsize_fa e h') []
      of Some (h'', _) \<Rightarrow>
        let _ = trace_set1 (ST ''increase step: stepsize = '' @ show (lfloat10 h'')) (None::'n eucl1 set option)
        in RETURN (h', CY, Y, 15/2/2/2/2 * h'')
      | None \<Rightarrow>
        let _ = trace_set1 (ST ''increase time step (failure): stepsize = '' @ show (lfloat10 h')) (None::'n eucl1 set option)
        in RETURN (h', CY, Y, h' * 5 / 2 / 2)
    }
  }"
sublocale autoref_op_pat_def step_adapt_time .

lemma [autoref_rules]:
  "(float_of, float_of) \<in> rnv_rel \<rightarrow> Id"
  "(approx, approx) \<in> nat_rel \<rightarrow> Id \<rightarrow> \<langle>\<langle>Id \<times>\<^sub>r Id\<rangle>option_rel\<rangle>list_rel \<rightarrow> \<langle>Id \<times>\<^sub>r Id\<rangle>option_rel"
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

lemma convex_halfspace[simp]:\<comment> \<open>TODO: move\<close>
  "convex (below_halfspace sctn)"
  apply (auto simp: below_halfspace_def le_halfspace_def[abs_def])
  using convex_bound_le
  apply (auto intro!: convexI simp: algebra_simps)
  by blast

lemma width_spec_appr1[THEN order_trans, refine_vcg]: "width_spec_appr1 X \<le> SPEC (\<lambda>_. True)"
  unfolding width_spec_appr1_def
  by refine_vcg

lemma
  step_adapt_time[le, refine_vcg]:
  assumes wdp: "vwd_step (TYPE('n::enum))"
  notes [refine_vcg] = wdp vwd_step vwd_stepD[OF wdp]
  shows "step_adapt_time (X::'n eucl1 set) h \<le> SPEC (\<lambda>(t, CX, X1, h). flowpipe X t t (CX \<times> UNIV) X1)"
  unfolding step_adapt_time_def  autoref_tag_defs
  apply (refine_vcg refine_vcg, clarsimp)
  apply (auto simp: flowpipe_def)
  apply force
  done

lemma Un_snd_sing_Pair_eq:
  "(e, f) \<in> a \<Longrightarrow> f \<union> (\<Union>x\<in>a - {(e, f)}. snd x) = (\<Union>x\<in>a. snd x)"
  by force

lemma let_unit: "Let X y = y ()" by simp

lemma [autoref_rules]: "(max_intersection_step, max_intersection_step)\<in> (reach_optns_rel) \<rightarrow> rnv_rel"
  by auto

definition [refine_vcg_def, simp]: "under_pre_inter_granularity_spec ro X = SPEC (\<lambda>_::bool. True)"
sublocale autoref_op_pat_def under_pre_inter_granularity_spec .
lemma under_pre_inter_granularity_spec_impl[autoref_rules]:
  "(\<lambda>ro x. RETURN (width_appr optns x \<le> pre_inter_granularity ro x), (under_pre_inter_granularity_spec)) \<in>
  reach_optns_rel \<rightarrow>
  appr_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  by (auto simp: nres_rel_def)

definition [refine_vcg_def, simp]: "under_post_inter_granularity_spec ro X = SPEC (\<lambda>_::bool. True)"
sublocale autoref_op_pat_def under_post_inter_granularity_spec .
lemma under_post_inter_granularity_spec_impl[autoref_rules]:
  "(\<lambda>ro x. RETURN (width_appr optns x \<le> post_inter_granularity ro x), under_post_inter_granularity_spec) \<in>
  reach_optns_rel \<rightarrow>
  appr_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  by (auto simp: nres_rel_def)

definition [refine_vcg_def, simp]: "under_max_tdev_thres_spec ro X = SPEC (\<lambda>_::bool. True)"
sublocale autoref_op_pat_def under_max_tdev_thres_spec .
lemma under_max_tdev_thres_spec_impl[autoref_rules]:
  "(\<lambda>ro x. RETURN (width_appr optns x \<le> max_tdev_thres ro x), under_max_tdev_thres_spec) \<in>
  reach_optns_rel \<rightarrow>
  appr_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  by (auto simp: nres_rel_def)

definition "resolve_step roptns X h = do {
    width_X \<leftarrow> under_max_tdev_thres_spec roptns (op_image_fste X:::appr_rel);
    if \<not> width_X
    then do {
      Y \<leftarrow> step_split roptns X;
      RETURN (h, fst ` Y, Y, h)
    }
    else do {
      (h0, CY, Y, h') \<leftarrow> step_adapt_time (X::'n::enum eucl1 set) h;
      RETURN (h0, mk_coll (fst ` Y) \<union> mk_coll CY, mk_coll Y, h')
    }
  }"
sublocale autoref_op_pat_def resolve_step .

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

lemma (in c1_on_open_euclidean) flowpipe_imp_flowsto_nonneg:\<comment> \<open>TODO: move!\<close>
  assumes "flowpipe X0 hl hu CX Y"
  shows "flowsto X0 {0..} CX Y"
  using assms
  by (fastforce simp: flowsto_def flowpipe_def open_segment_eq_real_ivl
      dest: bspec[where x=hl]
      intro!: bexI[where x=hl])

lemma
  resolve_step[le, refine_vcg]:
  assumes wdp: "vwd_step (TYPE('n::enum))"
  notes [refine_vcg] = wdp vwd_step vwd_stepD[OF wdp]
  shows "resolve_step roptns (X::'n::enum eucl1 set) h \<le> SPEC (\<lambda>(_, CX, X1, _).
    flowsto X {0..} (CX \<times> UNIV) X1 \<and> X \<union> X1 \<subseteq> CX \<times> UNIV \<and> X1 \<union> CX \<times> UNIV \<subseteq> Csafe \<times> UNIV)"
  unfolding resolve_step_def  autoref_tag_defs
  apply (refine_vcg refine_vcg)
  subgoal by (rule flowsto_self) auto
  subgoal by auto
  subgoal by auto
  subgoal
    apply clarsimp
    apply (frule flowpipe_imp_flowsto_nonneg)
    apply (rule flowsto_subset, assumption)
    by auto
  subgoal
    by (auto dest: flowpipe_source_subset)
  subgoal
    by (auto dest!: flowpipe_safeD)
  done

definition "pre_intersection_step ro X h = do {
    if h > max_intersection_step ro
    then RETURN (with_infos (h/2) (mk_coll X), mk_coll (fst ` X), op_empty_coll:::clw_rel (iinfo_rel appr1e_rel))
    else do {
      upig \<leftarrow> under_pre_inter_granularity_spec ro (fst ` X:::appr_rel);
      if upig then
        RETURN (with_infos h (op_empty_coll:::clw_rel appr1e_rel), mk_coll (fst ` X),
                with_infos (5 * h / 2 / 2) (mk_coll X))
      else do {
        X' \<leftarrow> step_split ro X;
        RETURN (with_infos h X', fst ` X', op_empty_coll:::clw_rel (iinfo_rel appr1e_rel))
      }
    }
  }"
sublocale autoref_op_pat_def pre_intersection_step .
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
  by (autoref_monadic)
concrete_definition pre_intersection_step_impl for roptnsi Xi hi uses pre_intersection_step_impl
lemmas [autoref_rules] = pre_intersection_step_impl.refine

lemma pre_intersection_step[THEN order_trans, refine_vcg]:
  "pre_intersection_step ro (X::'n eucl1 set) h \<le> SPEC (\<lambda>(X', CX, G). X \<subseteq> X' \<union> G \<and> X \<union> X' \<union> G \<subseteq> CX \<times> UNIV)"
  if [refine_vcg]: "wd TYPE('n::enum rvec)"
  unfolding pre_intersection_step_def autoref_tag_defs
  by (refine_vcg) auto

definition [simp]: "uninfo X = X"
sublocale autoref_op_pat_def uninfo .
lemma uninfo_autoref[autoref_rules]:
  assumes "PREFER single_valued X"
  assumes "PREFER single_valued R"
  shows "(map snd, uninfo) \<in> clw_rel (\<langle>R, X\<rangle>info_rel) \<rightarrow> clw_rel X"
  using assms
  apply (auto simp: lw_rel_def Union_rel_br info_rel_def br_chain br_rel_prod elim!: single_valued_as_brE
      dest!: brD
      intro!: brI)
  apply force
  apply force
  apply force
  done

definition [simp]: "op_subset_ivl a b \<longleftrightarrow> a \<subseteq> b"
sublocale autoref_op_pat_def op_subset_ivl .
lemma [autoref_op_pat]: "(\<subseteq>) \<equiv> OP op_subset_ivl"
  by (force intro!: eq_reflection)

lemma op_subset_ivl:
  assumes le[THEN GEN_OP_D, autoref_rules, param_fo]: "GEN_OP le (\<le>) (A \<rightarrow> A \<rightarrow> bool_rel)"
  shows "(\<lambda>(a, b) (c, d). le a b \<longrightarrow> le c a \<and> le b d, op_subset_ivl) \<in> \<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A\<rangle>ivl_rel \<rightarrow> bool_rel"
  apply (clarsimp dest!: brD simp: ivl_rel_def)
  subgoal for a b c d e f g h
    using le[of a c b d]
    using le[of e g a c]
    using le[of b d f h]
    by (auto simp: set_of_ivl_def)
  done
concrete_definition op_subset_ivl_impl uses op_subset_ivl
lemmas [autoref_rules] = op_subset_ivl_impl.refine

definition [simp]: "op_eq_ivl a b \<longleftrightarrow> a = b"
sublocale autoref_op_pat_def op_eq_ivl .
lemma [autoref_op_pat]: "(=) \<equiv> OP op_eq_ivl"
  by (force intro!: eq_reflection)
lemma eq_ivl_impl:
  assumes le[THEN GEN_OP_D, autoref_rules, param_fo]: "GEN_OP le (\<le>) (A \<rightarrow> A \<rightarrow> bool_rel)"
  shows "(\<lambda>(a, b) (c, d). (le a b \<longrightarrow> le c a \<and> le b d) \<and> (le c d \<longrightarrow> le a c \<and> le d b), op_eq_ivl) \<in> \<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A\<rangle>ivl_rel \<rightarrow> bool_rel"
  apply (clarsimp dest!: brD simp: )
  subgoal premises prems for a b c d e f
    using op_subset_ivl[param_fo, OF assms prems(1,2)]
      op_subset_ivl[param_fo, OF assms prems(2,1)]
    by (auto simp: )
  done
concrete_definition eq_ivl_impl uses eq_ivl_impl
lemmas [autoref_rules] = eq_ivl_impl.refine

definition [simp]: "eq_spec x y = SPEC (\<lambda>r. r \<longrightarrow> x = y)"
sublocale autoref_op_pat_def eq_spec .
lemma [autoref_itype]: "eq_spec ::\<^sub>i A \<rightarrow>\<^sub>i A \<rightarrow>\<^sub>i \<langle>i_bool\<rangle>\<^sub>ii_nres" by simp
lemma eq_spec_impl[autoref_rules]:
  "(\<lambda>a b. RETURN (a = b), eq_spec) \<in> A \<rightarrow> A \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  if "PREFER single_valued A"
  using that by (auto simp: nres_rel_def single_valued_def)

definition "select_with_inter ci a = do {
    CIs \<leftarrow> (sets_of_coll ci);
    As \<leftarrow> sets_of_coll a;
    FORWEAK CIs (RETURN op_empty_coll)
      (\<lambda>ci. do {
        (c, I) \<leftarrow> (get_inter ci);
        FORWEAK As (RETURN op_empty_coll)
        (\<lambda>a. do {
          b \<leftarrow> eq_spec a c;
          if b then RETURN (mk_coll ci)
          else RETURN (op_empty_coll)
        })
        (\<lambda>CIS CIS'. RETURN (CIS' \<union> CIS))
      })
      (\<lambda>CIS CIS'. RETURN (CIS' \<union> CIS))
  }"
sublocale autoref_op_pat_def select_with_inter .

lemma [autoref_op_pat_def del]: "get_inter p \<equiv> OP (get_inter p)" by auto

schematic_goal select_with_inter_impl:
  assumes [relator_props]: "single_valued A" "single_valued P"
  assumes [autoref_rules]: "(ci, c) \<in> clw_rel (\<langle>A, P\<rangle>inter_rel)" "(ai, a) \<in> clw_rel A"
  shows "(RETURN ?r, select_with_inter $ c $ a) \<in> \<langle>clw_rel (\<langle>A, P\<rangle>inter_rel)\<rangle>nres_rel"
  unfolding select_with_inter_def
  including art
  by (autoref_monadic (plain))
concrete_definition select_with_inter_impl for ci ai uses select_with_inter_impl
lemmas [autoref_rules] = select_with_inter_impl.refine[OF PREFER_sv_D PREFER_sv_D]
lemma [THEN order_trans, refine_vcg]: "select_with_inter ci a \<le> SPEC (\<lambda>_. True)"
  unfolding select_with_inter_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>_ _. True"])

definition with_coll_infos::"'c set \<Rightarrow> 'a set \<Rightarrow> 'a set nres"
  where [simp, refine_vcg_def]: "with_coll_infos h x = SPEC (\<lambda>r. r = x)"
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

abbreviation "fst_safe_colle XS \<equiv> (mk_safe_coll (op_image_fst_colle XS:::clw_rel appr_rel):::\<langle>clw_rel sappr_rel\<rangle>nres_rel)"

definition "reach_cont ro (guardsi::'n::enum rvec set) XS0 =
  do {
    (_, XS0') \<leftarrow> scaleR2_rep_coll XS0;
    sXS0 \<leftarrow> fst_safe_coll XS0';
    let fX0 = op_image_fst_colle XS0;
    guards \<leftarrow> (unintersect_coll (guardsi:::clw_rel (iplane_rel lvivl_rel)):::\<langle>clw_rel lvivl_rel\<rangle>nres_rel);
    d \<leftarrow> disjoints_spec fX0 (guards);
    CHECKs (ST ''reach_cont: starting from guarded set'') d;
    (_, CXS, GS) \<leftarrow>
      WHILE\<^bsup>(\<lambda>(XS, CXS, GS).
        flowsto XS0 {0..} (CXS \<times> UNIV) (XS \<union> GS) \<and>
        (XS \<union> GS \<union> CXS \<times> UNIV) \<subseteq> (Csafe - guards) \<times> UNIV \<and>
        XS0 \<union> GS \<subseteq> CXS \<times> UNIV)\<^esup>
          (\<lambda>(XS, CXS, GS). \<not> op_coll_is_empty XS) (\<lambda>(XS, CXS, GS).
      do {
        (hX, XS') \<leftarrow> (split_spec_exact XS:::\<langle>iinfo_rel (appr1e_rel) \<times>\<^sub>r clw_rel (iinfo_rel (appr1e_rel))\<rangle>nres_rel);
        (h::real, X) \<leftarrow> get_info hX;
        let _ = trace_set1e (ST ''next step in resolve_sctns using'') (Some X);
        cXS::nat \<leftarrow> card_info XS;
        cGS::nat \<leftarrow> card_info GS;
        let _ = trace_set1 (ST ''XS: '' @ show cXS) (None::'n eucl1 set option);
        let _ = trace_set1 (ST ''GS: '' @ show cGS) (None::'n eucl1 set option);
        (h0, fCX', X', h') \<leftarrow> resolve_step ro X h;
        sfCX' \<leftarrow> (mk_safe_coll (fCX':::clw_rel appr_rel):::\<langle>clw_rel sappr_rel\<rangle>nres_rel);
        let fX' = (fst ` X');
        fXS \<leftarrow> ivls_of_sets (fCX' \<union> fX');
        IS \<leftarrow> inter_overappr guards fXS;
        let d = is_empty IS;
        if d then RETURN (with_infos h' X' \<union> XS':::clw_rel (iinfo_rel appr1e_rel), sfCX' \<union> CXS, GS)
        else do {
          (hX', fCX', hG') \<leftarrow> pre_intersection_step ro X h0;
          sfCX' \<leftarrow> (mk_safe_coll (fCX':::clw_rel appr_rel):::\<langle>clw_rel sappr_rel\<rangle>nres_rel);
          _ \<leftarrow> fst_safe_colle (uninfo hX');
          _ \<leftarrow> fst_safe_colle (uninfo hG');
          fGs \<leftarrow> ivls_of_sets (op_image_fst_colle (uninfo hG') \<union> fCX' \<union> op_image_fst_colle (uninfo hX'));
          d \<leftarrow> disjoints_spec (sets_of_ivls guards) fGs;
          CHECKs (ST ''reach_cont: pre_intersection_step should not change disjointness condition!'') d;
          iguards \<leftarrow> select_with_inter guardsi IS;
          iG' \<leftarrow> with_coll_infos iguards hG';
          RETURN (hX' \<union> XS', sfCX' \<union> CXS, iG' \<union> GS)
        }
      })
      (with_infos (start_stepsize optns) (XS0:::clw_rel appr1e_rel):::clw_rel (iinfo_rel appr1e_rel),
        sXS0:::clw_rel sappr_rel, op_empty_coll:::clw_rel (\<langle>iplane_rel (lvivl_rel::(_\<times>'n rvec set)set), iinfo_rel appr1e_rel\<rangle>info_rel));
    RETURN (CXS, GS)
  }"
sublocale autoref_op_pat_def reach_cont .
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

lemma subset_scaleR2_fstD: "X \<subseteq> scaleR2 l u Y \<Longrightarrow> fst ` X \<subseteq> fst ` Y"
  by (force simp: scaleR2_def subset_iff image_def vimage_def)

lemma subset_DiffI: "A \<subseteq> B \<Longrightarrow> A \<inter> C = {} \<Longrightarrow> A \<subseteq> B - C"
  by auto

lemmas [refine_vcg del] = scaleR2_rep_of_coll
lemma scaleR2_rep_of_coll2[le, refine_vcg]:
  "scaleR2_rep_coll X \<le> SPEC (\<lambda>((l, u), Y). X \<subseteq> scaleR2 l u Y \<and> fst ` X = fst ` Y)"
  unfolding scaleR2_rep_coll_def
  apply (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs ((l, u), Y).
      \<Union>Xs \<subseteq> scaleR2 l u Y \<and> fst ` \<Union>Xs \<subseteq> fst ` Y \<and> fst ` Y \<subseteq> fst ` X"])
        apply (auto intro: scaleR2_subset)
  subgoal by (auto simp: scaleR2_def)
  subgoal by (auto simp: scaleR2_def image_def vimage_def, fastforce)
  subgoal
    apply (rule scaleR2_subset)
       apply (rule set_mp)
        apply assumption
       apply auto
    done
  subgoal by force
  subgoal
    apply (rule scaleR2_subset)
       apply (rule set_mp)
        apply assumption
       apply auto
    done
  subgoal by (auto simp: scaleR2_def)
  subgoal by (auto simp: scaleR2_def)
  subgoal by (auto simp: scaleR2_def image_def vimage_def, fastforce)
  done

lemma reach_cont[le, refine_vcg]:
  assumes wdp: "vwd_step (TYPE('n::enum))"
  notes [refine_vcg] = wdp vwd_step vwd_stepD[OF wdp]
  shows "reach_cont roptns guards (X::'n eucl1 set) \<le> SPEC (\<lambda>(CX, G).
    G \<union> (CX \<times> UNIV) \<subseteq> (Csafe - guards) \<times> UNIV \<and>
    X \<union> G \<subseteq> CX \<times> UNIV \<and>
    flowsto X {0..} (CX \<times> UNIV) G)"
  unfolding reach_cont_def autoref_tag_defs
  apply (refine_vcg, clarsimp_all simp add: cancel_times_UNIV_subset)
  subgoal by (rule flowsto_self) (auto simp: )
  subgoal by (force simp: scaleR2_def)
  subgoal by (fastforce simp: scaleR2_def vimage_def image_def)
  subgoal premises prems for a b c d e f g h i j k l
    using \<open>flowsto X _ _ (g \<union> _ \<union> _)\<close>  \<open>flowsto g _ _ _\<close>
    apply (rule flowsto_stepI)
    using prems
    by auto
  subgoal
    apply safe
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
  subgoal by auto
  subgoal
    by (rule flowsto_subset, assumption) auto
  subgoal
    apply safe
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by fastforce
    subgoal by auto
    subgoal by auto
    subgoal
      by (metis (mono_tags, lifting) Diff_eq_empty_iff Diff_iff IntI)
    done
  subgoal
    apply safe
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
  subgoal by auto
  done


lemma reach_cont_ho[autoref_rules]:
  "DIM_precond TYPE((real, 'a::enum) vec) D \<Longrightarrow>
  var.ncc_precond TYPE((real, 'a) vec) \<Longrightarrow>
  var.ncc_precond TYPE((real, 'a) vec \<times> ((real, 'a) vec, 'a) vec) \<Longrightarrow>
  (\<lambda>roptnsi guardsi XSi. nres_of (reach_cont_impl roptnsi guardsi XSi),
   reach_cont::_\<Rightarrow>'a rvec set \<Rightarrow> _)
  \<in> reach_optns_rel \<rightarrow> clw_rel
      (\<langle>\<langle>lv_rel\<rangle>ivl_rel,
       \<langle>lv_rel\<rangle>plane_rel\<rangle>Refine_Rigorous_Numerics.inter_rel) \<rightarrow>
    clw_rel appr1e_rel \<rightarrow>
    \<langle>clw_rel sappr_rel \<times>\<^sub>r
     clw_rel
      (\<langle>\<langle>\<langle>lv_rel\<rangle>ivl_rel,
       \<langle>lv_rel:: (real list \<times> 'a rvec) set\<rangle>plane_rel\<rangle>Refine_Rigorous_Numerics.inter_rel,
       \<langle>rnv_rel, appr1e_rel\<rangle>info_rel\<rangle>info_rel)\<rangle>nres_rel"
  using reach_cont_impl.refine by fastforce

definition "reach_cont_par roptns guards XS = do {
  XS \<leftarrow> sets_of_coll XS;
  PARS \<leftarrow> PAR_IMAGE (\<lambda>X (CX, G).
      G \<union> (CX \<times> UNIV) \<subseteq> (Csafe - guards) \<times> UNIV \<and>
      X \<union> G \<subseteq> CX \<times> UNIV \<and> flowsto X {0..} (CX \<times> UNIV) G)
    (\<lambda>X. reach_cont roptns guards (mk_coll X)) XS;
  RETURN (\<Union>(fst ` snd ` PARS), \<Union>(snd ` snd ` PARS))
}"
sublocale autoref_op_pat_def reach_cont_par .

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

lemma flowsto_source_Union: "flowsto (\<Union>x\<in>R. X0 x) T CX X1"
  if "\<And>x. x \<in> R \<Longrightarrow> flowsto (X0 x) T CX X1"
  using that
  by (auto simp: flowsto_def)

lemma reach_cont_par[le, refine_vcg]:
  assumes wdp: "vwd_step (TYPE('n::enum))"
  notes [refine_vcg] = wdp vwd_step vwd_stepD[OF wdp]
  shows "reach_cont_par roptns guards (X::'n eucl1 set) \<le> SPEC (\<lambda>(CX, G).
    G \<union> (CX \<times> UNIV) \<subseteq> (Csafe - guards) \<times> UNIV \<and>
    X \<union> G \<subseteq> CX \<times> UNIV \<and>
    flowsto X {0..} (CX \<times> UNIV) G)"
  unfolding reach_cont_par_def
  apply refine_vcg
    apply auto
    apply force
    apply force
    apply force
     apply force
  subgoal
    apply (rule bexI)
     prefer 2 apply assumption
    by auto
  subgoal
    apply (rule bexI)
     prefer 2 apply assumption
    by auto
  subgoal for R
    apply (rule flowsto_source_Union)
    apply (drule bspec, assumption)
    apply auto
    apply (rule flowsto_subset, assumption)
       apply auto
    done
  done

end

definition "ghost_rel = Pair () ` UNIV"
consts i_ghost::interface
lemmas [autoref_rel_intf] = REL_INTFI[of ghost_rel i_ghost]

context begin
interpretation autoref_syn .

definition [refine_vcg_def]: "GSPEC x = SPEC x"
lemma [autoref_op_pat_def]: "GSPEC x \<equiv> OP (GSPEC x)" by auto

lemma GSPEC_impl[autoref_rules]:
  assumes "SIDE_PRECOND (Ex P)"
  shows "(RETURN (), GSPEC P) \<in> \<langle>ghost_rel\<rangle>nres_rel"
  using assms by (auto simp: nres_rel_def ghost_rel_def GSPEC_def intro!: RETURN_SPEC_refine)

end

lemmas [relator_props del] = sv_info_rel
lemma sv_info_rel'[relator_props]:
  "single_valued S \<Longrightarrow> single_valued (\<langle>I, S\<rangle>info_rel)"
  by (auto simp: info_rel_def single_valued_def br_def)

context approximate_sets_ode_slp' begin

definition "subset_iplane_coll x ics = do {
    X \<leftarrow> unintersect x;
    ics \<leftarrow> sets_of_coll ics;
    FORWEAK ics (RETURN False) (\<lambda>ic. do {
      (i, c) \<leftarrow> get_inter ic;
      sctn \<leftarrow> get_plane c;
      b1 \<leftarrow> subset_spec_plane X sctn;
      RETURN (b1 \<and> op_subset_ivl X i)
    }) (\<lambda>b c. RETURN (b \<or> c))
  }"
sublocale autoref_op_pat_def subset_iplane_coll .

schematic_goal subset_iplane_coll_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(xi, x::'a set) \<in> iplane_rel lvivl_rel"
  assumes [autoref_rules]: "(icsi, ics) \<in> clw_rel (iplane_rel lvivl_rel)"
  shows "(nres_of ?r, subset_iplane_coll $ x $ ics) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding subset_iplane_coll_def
  including art
  by (autoref_monadic)
concrete_definition subset_iplane_coll_impl uses subset_iplane_coll_impl
lemmas [autoref_rules] = subset_iplane_coll_impl.refine

lemma subset_iplane_coll[THEN order_trans, refine_vcg]:
  "subset_iplane_coll x ics \<le> SPEC (\<lambda>b. b \<longrightarrow> x \<subseteq> ics)"
  unfolding subset_iplane_coll_def
  apply refine_vcg
  subgoal for X icss
    by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>ic b. b \<longrightarrow> X \<subseteq> \<Union>(icss)"]) auto
  done

definition "subsets_iplane_coll xs ics = FORWEAK xs (RETURN True) (\<lambda>x. subset_iplane_coll x ics) (\<lambda>a b. RETURN (a \<and> b))"
sublocale autoref_op_pat_def subsets_iplane_coll .

schematic_goal subsets_iplane_coll_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(xi, x::'a set set) \<in> \<langle>iplane_rel lvivl_rel\<rangle>list_wset_rel"
  assumes [autoref_rules]: "(icsi, ics) \<in> clw_rel (iplane_rel lvivl_rel)"
  shows "(nres_of ?r, subsets_iplane_coll $ x $ ics) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding subsets_iplane_coll_def
  including art
  by (autoref_monadic)
concrete_definition subsets_iplane_coll_impl uses subsets_iplane_coll_impl
lemmas [autoref_rules] = subsets_iplane_coll_impl.refine

lemma subsets_iplane_coll[THEN order_trans, refine_vcg]:
  "subsets_iplane_coll x ics \<le> SPEC (\<lambda>b. b \<longrightarrow> \<Union>x \<subseteq> ics)"
  unfolding subsets_iplane_coll_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>x b. (b \<longrightarrow> \<Union>x \<subseteq> ics)"]) auto

definition "stable_set p = {x. {0..} \<subseteq> existence_ivl0 x \<and> (flow0 x \<longlongrightarrow> p) at_top}"

definition symstart_coll::"('n::enum eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set)nres) \<Rightarrow>
  'n eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set)nres"
  where
"symstart_coll symstart X0 = do {
    _ \<leftarrow> (fst_safe_colle (X0:::clw_rel appr1e_rel):::\<langle>clw_rel sappr_rel\<rangle>nres_rel);
    X0s \<leftarrow> sets_of_coll X0;
    (CX1, X1) \<leftarrow> FORWEAK X0s (RETURN (op_empty_coll, op_empty_coll)) (symstart)
      (\<lambda>(CX, X) (CX', X'). RETURN (CX' \<union> CX, X' \<union> X));
    RETURN (CX1, X1)
  }"
sublocale autoref_op_pat_def symstart_coll .

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

lemma symstart_coll[THEN order_trans, refine_vcg]:
  assumes [refine_vcg]: "wd (TYPE('n::enum rvec))"
  assumes [le, refine_vcg]:
    "\<And>X0. X0 \<subseteq> Csafe \<times> UNIV \<Longrightarrow> symstart X0 \<le> SPEC (\<lambda>(CX, X). flowsto (X0 - trap \<times> UNIV) {0..} (CX \<times> UNIV) (X))"
  shows "symstart_coll symstart X0 \<le> SPEC (\<lambda>(CX, X). flowsto ((X0::'n eucl1 set) - trap \<times> UNIV) {0..} (CX \<times> UNIV) X)"
  unfolding symstart_coll_def autoref_tag_defs
  apply (refine_vcg FORWEAK_mono_rule[where I="\<lambda>X (CY, Y). flowsto (\<Union>X - trap \<times> UNIV) {0..} (CY \<times> UNIV) Y"], clarsimp_all)
  subgoal by force
  subgoal for a b c d e by (rule flowsto_subset, assumption) auto
  subgoal by force
  subgoal for a b c d e f g
    unfolding Un_Diff
    apply (rule flowsto_source_unionI)
    subgoal by (rule flowsto_subset, assumption) auto
    subgoal by (rule flowsto_subset, assumption) auto
    done
  done

definition reach_cont_symstart ::
  "'b reach_options \<Rightarrow> _ \<Rightarrow> 'n::enum rvec set
      \<Rightarrow> 'n eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set) nres"
  where "reach_cont_symstart ro symstart (guards::'n rvec set) X0 = do {
    let fX0 = op_image_fst_colle X0;
    GUARDS \<leftarrow> unintersect_coll guards;
    d \<leftarrow> disjoints_spec fX0 GUARDS;
    CHECKs (ST ''reach_cont_symstart: starting from guarded set'') d;
    (CY, Y0) \<leftarrow> symstart_coll symstart X0;
    sCY \<leftarrow> (mk_safe_coll (op_image_fst_colle X0 \<union> CY:::clw_rel appr_rel):::\<langle>clw_rel sappr_rel\<rangle>nres_rel);
    b \<leftarrow> disjoints_spec (op_image_fst_colle Y0 \<union> CY) GUARDS;
    CHECKs ''reach_cont_symstart with a stupid guard'' b;
    (CX, GS) \<leftarrow> (reach_cont_par ro guards Y0:::\<langle>clw_rel sappr_rel \<times>\<^sub>r clw_rel (\<langle>iplane_rel lvivl_rel::(_ \<times> 'n rvec set) set, iinfo_rel appr1e_rel\<rangle>info_rel)\<rangle>nres_rel);
    let CZ = sCY \<union> CX;
    RETURN (CZ, GS)
  }"
sublocale autoref_op_pat_def reach_cont_symstart .

lemma ghost_relI: "((), x) \<in> ghost_rel" by (auto simp: ghost_rel_def)

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

lemma times_subset_iff: "A \<times> B \<subseteq> C \<times> E \<longleftrightarrow> A = {} \<or> B = {} \<or> A \<subseteq> C \<and> B \<subseteq> E"
  by auto

lemma reach_cont_symstart[le, refine_vcg]:
  assumes wdp: "vwd_step (TYPE('n::enum))"
  assumes [le, refine_vcg]: "\<And>X0. X0 \<subseteq> Csafe \<times> UNIV \<Longrightarrow> symstart X0 \<le> SPEC (\<lambda>(CX, X). flowsto (X0 - trap \<times> UNIV) {0..} (CX \<times> UNIV) (X))"
  notes [refine_vcg] = wdp vwd_step vwd_stepD[OF wdp]
  shows "reach_cont_symstart roptns symstart guards (X::'n eucl1 set) \<le> SPEC (\<lambda>(CX, G).
    G \<union> (CX \<times> UNIV) \<subseteq> (Csafe - guards) \<times> UNIV \<and>
    X \<subseteq> CX \<times> UNIV \<and>
    G \<subseteq> CX \<times> UNIV \<and>
    flowsto (X - trap \<times> UNIV) {0..} (CX \<times> UNIV) (G))"
  unfolding reach_cont_symstart_def autoref_tag_defs
  apply (refine_vcg, clarsimp_all)
  subgoal by (auto simp: times_subset_iff)
  subgoal by auto
  subgoal by auto
  subgoal for a b c d e f g
    apply (rule flowsto_stepI[OF _ _ order_refl])
         apply assumption
    by assumption auto
  done

definition reach_conts ::
  "'b reach_options \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> 'n::enum rvec set
      \<Rightarrow> 'n eucl1 set \<Rightarrow> ('n rvec set \<times> ('n rvec set \<times> 'n eucl1 set) set \<times> ('n eucl1 set \<Rightarrow> 'n eucl1 set)) nres"
  where "reach_conts ro symstart trap (guardsi::'n rvec set) X0 = do {
    (CX, GS) \<leftarrow> (reach_cont_symstart ro (symstart:::appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel) guardsi X0:::
      \<langle>clw_rel sappr_rel \<times>\<^sub>r
       clw_rel (\<langle>iplane_rel lvivl_rel::(_\<times>'n rvec set) set, iinfo_rel appr1e_rel\<rangle>info_rel)\<rangle>nres_rel);
    (IGSs:: ('n rvec set \<times> 'n eucl1 set) set) \<leftarrow> explicit_info_set GS;
    let GSs = snd ` IGSs;
    ASSUME (finite GSs);
    CHECKs '''' (GSs \<noteq> {});
    ASSERT       (\<exists>f. X0 = \<Union>(f ` GSs) \<and> (\<forall>G \<in> GSs. flowsto (f G - trap \<times> UNIV) {0..} (CX \<times> UNIV) (G)));
    X0f \<leftarrow> GSPEC (\<lambda>f. X0 = \<Union>(f ` GSs) \<and> (\<forall>G \<in> GSs. flowsto (f G - trap \<times> UNIV) {0..} (CX \<times> UNIV) (G)));
    let K = (fst ` IGSs);
    b \<leftarrow> subsets_iplane_coll K guardsi;
    CHECKs ''reach_conts: subsets_iplane_coll'' b;
    RETURN (CX, IGSs:::\<langle>iplane_rel lvivl_rel \<times>\<^sub>r clw_rel (iinfo_rel appr1e_rel)\<rangle>list_wset_rel, X0f)
  }"
sublocale autoref_op_pat_def reach_conts .

lemma
  list_wset_rel_finite:
  assumes "single_valued A"
  shows "(xs, X) \<in> \<langle>A\<rangle>list_wset_rel \<Longrightarrow> finite X"
  using assms
  by (auto simp: list_wset_rel_def set_rel_br dest!: brD elim!: single_valued_as_brE)

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

lemma
  flowsto_UnionE:
  assumes "finite Gs"
  assumes "flowsto X T CX (\<Union>Gs)"
  obtains XGs where "\<And>X G. (X, G) \<in> XGs \<Longrightarrow> flowsto X T CX G" "Gs = snd ` XGs" "X = \<Union>(fst ` XGs)"
  apply atomize_elim
  using assms
proof (induction arbitrary: X)
  case empty
  then show ?case by auto
next
  case (insert x F)
  from insert.prems obtain X1 X2 where X: "X = X1 \<union> X2" and X1: "flowsto X1 T CX x" and X2: "flowsto X2 T CX (\<Union>F)"
    by (auto elim!: flowsto_unionE)
  from insert.IH[OF X2] obtain XGs where XGs:
    "\<And>X G. (X, G) \<in> XGs \<Longrightarrow> flowsto X T CX G" "F = snd ` XGs" "X2 = (\<Union>a\<in>XGs. fst a)"
    by auto
  then show ?case
    using X X1 X2
    by (intro exI[where x="insert (X1, x) XGs"]) auto
qed

lemma flowsto_Union_funE:
  assumes "finite Gs"
  assumes "flowsto X T CX (\<Union>Gs)"
  obtains f where "\<And>G. G \<in> Gs \<Longrightarrow> flowsto (f G) T CX G" "X = \<Union>(f ` Gs)"
  apply atomize_elim
  using assms
proof (induction arbitrary: X)
  case empty
  then show ?case by auto
next
  case (insert x F)
  from insert.prems obtain X1 X2 where X: "X = X1 \<union> X2" and X1: "flowsto X1 T CX x" and X2: "flowsto X2 T CX (\<Union>F)"
    by (auto elim!: flowsto_unionE)
  from insert.IH[OF X2] obtain f where f:
    "\<And>G. G \<in> F \<Longrightarrow> flowsto (f G) T CX G" "X2 = (\<Union>a\<in>F. f a)"
    by auto
  then show ?case
    using X X1 X2 insert.hyps
    by (intro exI[where x="f (x:=X1)"]) (auto split: if_splits)
qed

lemma flowsto_Union_Un_funE:
  assumes "flowsto X T CX (\<Union>Gs \<union> trap)"
  assumes "finite Gs" "Gs \<noteq> {}"
  obtains f where "\<And>G. G \<in> Gs \<Longrightarrow> flowsto (f G) T CX (G \<union> trap)" "X = \<Union>(f ` Gs)"
proof -
  from assms have "flowsto X T CX (\<Union>g \<in> Gs. g \<union> trap)" by auto
  from flowsto_Union_funE[OF finite_imageI[OF \<open>finite Gs\<close>] this]
  obtain f where f: "\<And>G. G \<in> (\<lambda>g. g \<union> trap) ` Gs \<Longrightarrow> flowsto (f G) T CX G"
    "X = UNION ((\<lambda>g. g \<union> trap) ` Gs) f"
    by auto
  define f' where "f' g = f (g \<union> trap)" for g
  have "G \<in> Gs \<Longrightarrow> flowsto (f' G) T CX (G \<union> trap)" for G
    using f(1)[of "G \<union> trap"]
    by (auto simp: f'_def)
  moreover
  have "X = \<Union>(f' ` Gs)"
    using f by (auto simp: f'_def)
  ultimately show ?thesis ..
qed

lemma flowsto_Diff_to_Union_funE:
  assumes "flowsto (X - trap) T CX (\<Union>Gs)"
  assumes "finite Gs"
  obtains f where "\<And>G. G \<in> Gs \<Longrightarrow> flowsto (f G - trap) T CX G" "Gs \<noteq> {} \<Longrightarrow> X = \<Union>(f ` Gs)"
  apply atomize_elim
  using assms(2,1)
proof (induction arbitrary: X)
  case empty then show ?case by simp
next
  case (insert x F)
  from insert.prems obtain X1 X2 where X: "X - trap = X1 \<union> X2" and X1: "flowsto (X1) T CX x" and X2: "flowsto X2 T CX (\<Union>F)"
    by (auto elim!: flowsto_unionE)
  then have "X1 = X1 - trap" "X2 = X2 - trap" by auto
  then have X1': "flowsto (X1 - trap) T CX x" and X2': "flowsto (X2 - trap) T CX (\<Union>F)"
    using X1 X2 by auto
  from insert.IH[OF X2'] obtain f where f: "\<And>G. G \<in> F \<Longrightarrow> flowsto (f G - trap) T CX G" "F \<noteq> {} \<Longrightarrow> X2 = (\<Union>a\<in>F. f a)"
    by auto
  show ?case
    apply (cases "F = {}")
    subgoal using f X X1 X2 X1' X2' insert.hyps insert.prems by auto
    subgoal
      apply (rule exI[where x="f (x:=X1 \<union> (trap \<inter> X))"])
      apply auto
      subgoal
        using X1
        by (rule flowsto_subset) auto
      subgoal using X X1 X2 insert.hyps by auto
      subgoal using f X X1 X2 insert.hyps by auto
      subgoal using f X X1 X2 insert.hyps by auto
      subgoal using f X X1 X2 X1' X2' insert.hyps insert.prems by auto
      subgoal using f X X1 X2 X1' X2' insert.hyps insert.prems insert by auto
      subgoal using f X X1 X2 insert.hyps by (auto split: if_splits)
      done
    done
qed

lemma reach_conts[le, refine_vcg]:
  assumes wdp: "vwd_step (TYPE('n::enum))"
  assumes [refine_vcg]: "\<And>X0. X0 \<subseteq> Csafe \<times> UNIV \<Longrightarrow> symstart X0 \<le> SPEC (\<lambda>(CX, X). flowsto (X0 - trap \<times> UNIV) {0..} (CX \<times> UNIV) X)"
  notes [refine_vcg] = wdp vwd_step vwd_stepD[OF wdp]
  shows "reach_conts roptns symstart trap guards (X::'n eucl1 set) \<le> SPEC (\<lambda>(CX, IGs, X0).
    \<Union>(snd ` IGs) \<union> (CX \<times> UNIV) \<subseteq> (Csafe - guards) \<times> UNIV \<and>
    X \<subseteq> CX \<times> UNIV \<and>
    \<Union>(snd ` IGs) \<subseteq> CX \<times> UNIV \<and>
    \<Union>(fst ` IGs) \<subseteq> guards \<and>
    X = \<Union>(X0 ` (snd ` IGs)) \<and>
    (\<forall>(I, G) \<in> IGs. flowsto (X0 G - trap \<times> UNIV) {0..} (CX \<times> UNIV) G))"
  unfolding reach_conts_def autoref_tag_defs
  apply (refine_vcg, clarsimp_all)
  subgoal for a b
    apply (erule flowsto_Diff_to_Union_funE)
    apply (force simp: split_beta')
    subgoal for f
      apply (rule exI[where x=f])
      by (auto simp: split_beta')
    done
  subgoal by (auto)
  subgoal by (auto)
  subgoal by (auto)
  done

definition [refine_vcg_def]: "get_sctns X = SPEC (\<lambda>R. X = below_halfspaces R)"
sublocale autoref_op_pat_def get_sctns .

lemma get_sctns_autoref[autoref_rules]:
  "(\<lambda>x. RETURN x, get_sctns) \<in> \<langle>R\<rangle>halfspaces_rel \<rightarrow> \<langle>\<langle>\<langle>R\<rangle>sctn_rel\<rangle>list_set_rel\<rangle>nres_rel"
  by (auto simp: get_sctns_def nres_rel_def halfspaces_rel_def br_def intro!: RETURN_SPEC_refine)

definition "leaves_halfspace S X = do {
    sctns \<leftarrow> get_sctns S;
    sctnss \<leftarrow> op_set_to_list sctns;
    (case sctnss of
      [] \<Rightarrow> RETURN None
    | [sctn] \<Rightarrow>
      do {
        (Xi, Xs) \<leftarrow> ivl_rep_of_set_coll X;
        ASSERT (Xi \<le> Xs);
        b \<leftarrow> subset_spec_plane ({Xi .. Xs}:::lvivl_rel) sctn;
        CHECKs (ST ''leaves_halfspace: not subset of plane'') b;
        F \<leftarrow> ode_set ({Xi .. Xs}:::appr_rel);
        sF \<leftarrow> Sup_inner F (normal sctn);
        CHECKs (ST ''leaves_halfspace: not down from plane'') (sF < 0);
        RETURN (Some sctn)
      }
    | _ \<Rightarrow> do {CHECKs (ST ''leaves_halfspace: not a good halfspace'') False; SUCCEED})
  }"
sublocale autoref_op_pat_def leaves_halfspace .

schematic_goal leaves_halfspace_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  assumes nccp[autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  notes [simp] = ncc_precondD[OF nccp]
  assumes [autoref_rules]: "(Si, S) \<in> \<langle>lv_rel\<rangle>halfspaces_rel"
  assumes [autoref_rules]: "(Xi, X::'n rvec set) \<in> clw_rel appr_rel"
  shows "(nres_of ?r, leaves_halfspace $ S $ X) \<in> \<langle>\<langle>\<langle>lv_rel\<rangle>sctn_rel\<rangle>option_rel\<rangle>nres_rel"
  unfolding leaves_halfspace_def
  including art
  by (autoref_monadic)
concrete_definition leaves_halfspace_impl for Si Xi uses leaves_halfspace_impl
lemmas [autoref_rules] = leaves_halfspace_impl.refine

lemma refine_case_list[refine_vcg]:
  assumes "xs = [] \<Longrightarrow> f \<le> SPEC P"
  assumes "\<And>y ys. xs = y # ys \<Longrightarrow> g y ys \<le> SPEC P"
  shows "(case xs of [] \<Rightarrow> f | (x#xs) \<Rightarrow> g x xs) \<le> SPEC P"
  using assms
  by (auto split: list.splits)

lemma leaves_halfspace[le, refine_vcg]:
  assumes wdp: "vwd_step (TYPE('n::enum))"
  notes wds[refine_vcg] = wdp vwd_step vwd_stepD[OF wdp]
  shows "leaves_halfspace S (X::'n::enum rvec set) \<le>
    SPEC (\<lambda>b. case b of None \<Rightarrow> S = UNIV
      | Some sctn \<Rightarrow>
        (S = below_halfspace sctn \<and> X \<subseteq> plane_of sctn \<and> (\<forall>x \<in> X. ode x \<bullet> normal sctn < 0)))"
  unfolding leaves_halfspace_def autoref_tag_defs op_set_to_list_def
  apply (refine_vcg, clarsimp_all)
  subgoal by (force simp add: halfspace_simps plane_of_def)
  done

definition "poincare_start_on guards sctn X0S =
  do {
    X0SS \<leftarrow> sets_of_coll X0S;
    (FORWEAK X0SS (RETURN (op_empty_coll:::clw_rel appr1e_rel, op_empty_coll:::clw_rel appr_rel)) (\<lambda>X0. do {
      mk_safe (fst ` X0);
      (h, err, CX1, X1) \<leftarrow> choose_step1e X0 (start_stepsize optns);
      let _ = trace_set (ST ''interpolated start step:'') (Some CX1);
      let _ = print_set True CX1;
      let _ = trace_set1e (ST ''discrete start step:'') (Some X1);
      let _ = print_set1e False X1;
      let fX1 = op_image_fste X1;
      c0 \<leftarrow> below_sctn (op_image_fste X0) (sctn);
      c1 \<leftarrow> sbelow_sctn (fX1) (sctn);
      c2 \<leftarrow> disjoints_spec (mk_coll (fX1)) guards;
      c3 \<leftarrow> disjoints_spec (mk_coll (CX1)) guards;
      mk_safe (fX1);
      mk_safe (CX1);
      D \<leftarrow> (ode_set (CX1):::\<langle>appr_rel\<rangle>nres_rel);
      d \<leftarrow> Sup_inner D (normal sctn);
      let _ = trace_set (ST ''poincare_start_on: D '') (Some D);
      CHECKs (ST ''poincare_start_on: is away and really moves away'') (c0 \<and> c1 \<and> c2 \<and> c3 \<and> d < 0);
      RETURN (mk_coll X1:::clw_rel appr1e_rel, (mk_coll CX1):::clw_rel appr_rel)
    })
    (\<lambda>(X1, CX1) (X1S, CX1S). RETURN (op_union_coll X1 X1S:::clw_rel appr1e_rel, op_union_coll CX1 CX1S:::clw_rel appr_rel)))
  }"
sublocale autoref_op_pat_def poincare_start_on .
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

lemma flowsto_stays_sbelow:
  assumes "flowsto X0 {0<..} CXS X1"
  assumes "fst ` X0 \<subseteq> below_halfspace sctn"
  assumes "\<And>x d. (x, d) \<in> CXS \<Longrightarrow> ode x \<bullet> normal sctn < 0"
  shows "flowsto X0 {0<..} (CXS \<inter> sbelow_halfspace sctn \<times> UNIV) X1"
  unfolding flowsto_def
proof safe
  fix x d assume "(x, d) \<in> X0"
  with assms obtain t where
    "t>0" "t \<in> existence_ivl0 x" "(\<forall>s\<in>{0<..<t}. (flow0 x s, Dflow x s o\<^sub>L d) \<in> CXS)"
    "(flow0 x t, Dflow x t o\<^sub>L d) \<in> X1"
    by (auto simp: flowsto_def subset_iff open_segment_eq_real_ivl)
  moreover
  have "\<forall>s\<in>{0<..<t}. flow0 x s \<in> sbelow_halfspace sctn"
  proof (rule ccontr, clarsimp)
    fix s assume s: "flow0 x s \<notin> sbelow_halfspace sctn" "0 < s" "s < t"
    let ?f = "\<lambda>t. flow0 x t \<bullet> normal sctn - pstn sctn"
    let ?f' = "\<lambda>t dx. dx * (ode (flow0 x t) \<bullet> normal sctn)"
    have "\<exists>xa\<in>{0<..<s}. ?f s - ?f 0 = ?f' xa (s - 0)"
      by (rule mvt[OF \<open>0 < s\<close>, of ?f ?f'])
        (use ivl_subset_existence_ivl[OF \<open>t \<in> existence_ivl0 x\<close>] \<open>0 < s\<close> \<open>s < t\<close> in
          \<open>auto intro!: continuous_intros derivative_eq_intros flow_has_derivative
            simp: flowderiv_def blinfun.bilinear_simps\<close>)
    then obtain s' where "?f s - ?f 0 = ?f' s' (s - 0)" "0 < s'" "s' < s"
      by (auto simp: algebra_simps)
    note this(1)
    also
    have "(flow0 x s', Dflow x s' o\<^sub>L d )\<in> CXS"
      using \<open>0 < s'\<close> \<open>\<forall>s\<in>{0<..<t}. _ \<in> CXS\<close> \<open>s < t\<close> \<open>s' < s\<close> by auto
    then have "?f' s' (s - 0) < 0"
      using assms \<open>(x, d) \<in> X0\<close> \<open>0 < s\<close>
      by (auto simp: flowsto_def halfspace_simps algebra_simps subset_iff intro!: mult_pos_neg)
    finally have 1: "?f s < ?f 0"
      by simp
    also have "?f 0 \<le> 0"
      using \<open>(x, d) \<in> X0\<close> assms mem_existence_ivl_iv_defined[OF \<open>t \<in> existence_ivl0 _\<close>]
      by (auto simp: halfspace_simps subset_iff)
    finally have "?f s < 0" .
    moreover from s have "0 \<le> ?f s"
      by (auto simp: halfspace_simps not_less)
    ultimately show False by simp
  qed
  ultimately
  show "\<exists>t\<in>{0<..}. t \<in> existence_ivl0 x \<and> (flow0 x t, Dflow x t o\<^sub>L d) \<in> X1 \<and>
                (\<forall>s\<in>{0<--<t}. (flow0 x s, Dflow x s o\<^sub>L d) \<in> CXS \<inter> sbelow_halfspace sctn \<times> UNIV)"
    by (auto intro!: simp: open_segment_eq_real_ivl)
qed


lemma poincare_start_on[le, refine_vcg]:
  assumes wdp: "vwd_step (TYPE('n::enum))"
  notes wds[refine_vcg] = wdp vwd_step vwd_stepD[OF wdp]
  shows "poincare_start_on guards sctn (X0::'n eucl1 set) \<le> SPEC (\<lambda>(X1S, CX1S).
    fst ` (X1S \<union> (CX1S \<times> UNIV)) \<subseteq> Csafe \<and>
    fst ` X1S \<subseteq> sbelow_halfspace sctn \<and>
    fst ` (X1S \<union> (CX1S \<times> UNIV)) \<inter> guards = {} \<and>
    (X0 \<subseteq> (CX1S \<times> UNIV)) \<and>
    (\<forall>(x, d) \<in> CX1S \<times> UNIV. ode x \<bullet> normal sctn < 0) \<and>
    flowsto X0 pos_reals ((CX1S \<times> UNIV) \<inter> (sbelow_halfspace sctn \<times> UNIV)) X1S)"
  unfolding poincare_start_on_def autoref_tag_defs
  apply refine_vcg
  apply (rule FORWEAK_mono_rule[where I="\<lambda>X0S (X1S, CX1S).
      flowsto (\<Union>X0S) pos_reals ((CX1S \<times> UNIV) \<inter> sbelow_halfspace sctn \<times> UNIV) X1S \<and>
        fst ` (X1S \<union> (CX1S \<times> UNIV)) \<subseteq> Csafe \<and>
        (\<Union>X0S) \<subseteq> X0 \<and>
        (\<Union>X0S) \<subseteq> (CX1S \<times> UNIV) \<and>
        fst ` (X1S \<union> (CX1S \<times> UNIV)) \<inter> guards = {} \<and>
        (\<forall>(x, d) \<in> (CX1S \<times> UNIV). ode x \<bullet> normal sctn < 0) \<and>
        fst ` X1S  \<subseteq> sbelow_halfspace sctn"])
  subgoal by (refine_vcg)
  subgoal for A B
    apply (refine_vcg)
    subgoal
      apply (auto simp: dest!: flowpipe_imp_flowsto)
      apply (rule flowsto_subset)
          apply (rule flowsto_stays_sbelow[where sctn=sctn])
            apply (rule flowsto_subset) apply assumption
               apply (rule order_refl)
              apply force
             apply (rule order_refl)
            apply (rule order_refl)
           apply (auto simp: halfspace_simps)
      apply (rule le_less_trans)
       prefer 2 apply assumption
      apply (drule bspec)
       apply (rule set_mp, assumption)
       prefer 2 apply assumption
      apply auto
      done
    subgoal by auto
    subgoal by force
    subgoal by (auto simp: dest!: flowpipe_source_subset)
    subgoal by auto
    subgoal
      apply (auto simp: halfspace_simps subset_iff)
      apply (rule le_less_trans[rotated], assumption)
      by fastforce
    done
  subgoal by (auto intro: flowsto_subset) force
  subgoal for a b c d
    using assms
    apply (refine_vcg, clarsimp_all)
    subgoal for e f g h i j k l m n
      apply (rule flowsto_source_unionI)
      subgoal
        apply (drule flowpipe_imp_flowsto, assumption)
        apply (rule flowsto_subset[OF flowsto_stays_sbelow[where sctn=sctn] order_refl])
             apply (rule flowsto_subset[OF _ order_refl], assumption)
               apply force
              apply (rule order_refl)
             apply (rule order_refl)
            apply (auto simp: halfspace_simps)
        apply (rule le_less_trans)
         prefer 2 apply assumption
        apply (drule bspec)
         apply (rule set_mp, assumption)
         prefer 2 apply assumption
        apply auto
        done
      by (auto intro!: flowsto_source_unionI dest!: flowpipe_imp_flowsto intro: flowsto_subset[OF _ order_refl])
    subgoal
      apply (auto simp: subset_iff)
      apply (auto simp: image_Un)
      done
    subgoal by auto
    subgoal by (auto dest!: flowpipe_source_subset)
    subgoal by auto
    subgoal
      apply (auto simp: halfspace_simps subset_iff)
      apply (rule le_less_trans[rotated], assumption)
      by fastforce
    subgoal by auto
    done
  subgoal by auto
  done

abbreviation "inter_plane A B \<equiv> mk_inter A (plane_of B)"

definition [simp]: "isets_of_iivls x = x"

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

definition [simp]: "op_times_UNIV_coll X = X \<times> UNIV"
sublocale autoref_op_pat_def op_times_UNIV_coll .
lemma [autoref_op_pat]: "X \<times> UNIV \<equiv> OP op_times_UNIV_coll $ X" by simp

lemma op_times_UNIV_coll_impl[autoref_rules]: "(map (\<lambda>x. (x, None)), op_times_UNIV_coll) \<in> clw_rel appr_rel \<rightarrow> clw_rel appr1_rel"
  apply (rule lift_clw_rel_map)
     apply (rule relator_props)
    apply (rule relator_props)
  unfolding op_times_UNIV_coll_def op_times_UNIV_def[symmetric]
   apply (rule op_times_UNIV_impl)
  by auto

definition [simp]: "op_inter_fst X Y = X \<inter> Y \<times> UNIV"
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

definition "op_inter_fst_coll XS Y = do {
  XS \<leftarrow> sets_of_coll XS;
  FORWEAK XS (RETURN op_empty_coll) (\<lambda>X. RETURN (mk_coll (op_inter_fst X Y))) (\<lambda>X X'. RETURN (X' \<union> X))
  }"
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

lemma op_inter_fst_coll[le, refine_vcg]: "op_inter_fst_coll X Y \<le> SPEC (\<lambda>R. R = X \<inter> Y \<times> UNIV)"
  unfolding op_inter_fst_coll_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs R. \<Union>Xs \<inter> Y \<times> UNIV \<subseteq> R \<and> R \<subseteq> X \<inter> Y \<times> UNIV"])
    auto

definition "scaleRe_ivl_coll_spec l u X = do {
    XS \<leftarrow> sets_of_coll X;
    FORWEAK XS (RETURN op_empty_coll)
      (\<lambda>X. do {I \<leftarrow> scaleRe_ivl_spec l u X; RETURN (mk_coll I)})
      (\<lambda>X X'. RETURN (X' \<union> X))
  }"
sublocale autoref_op_pat_def scaleRe_ivl_coll_spec .

lemma mem_scaleR2_union[simp]: "x \<in> scaleR2 l u (A \<union> B) \<longleftrightarrow> x \<in> scaleR2 l u A \<or> x \<in> scaleR2 l u B"
  by (force simp: scaleR2_def vimage_def image_def)


lemma scaleR2_empty[simp]: "scaleR2 l u {} = {}"
  by (auto simp: scaleR2_def)

lemma scaleRe_ivl_coll_spec[le, refine_vcg]: "scaleRe_ivl_coll_spec l u X \<le> SPEC (\<lambda>Y. Y = scaleR2 l u X)"
  unfolding scaleRe_ivl_coll_spec_def
  apply (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs R. scaleR2 l u (\<Union>Xs) \<subseteq> R \<and> R \<subseteq> scaleR2 l u X"])
      apply (auto simp: intro: scaleR2_subset)
  subgoal
    by (force simp: intro: scaleR2_subset)
  done

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

definition "do_intersection_core guards ivl sctn hX =
  do {
    (h, eX) \<leftarrow> get_info hX;
    ((l, u), X) \<leftarrow> scaleR2_rep eX;
    (b, PS1, PS2, CXS) \<leftarrow> do_intersection (guards:::clw_rel (iplane_rel lvivl_rel)) ivl sctn X h;
    if b then do {
      PS1e \<leftarrow> scaleRe_ivl_coll_spec l u PS1;
      PS2e \<leftarrow> scaleRe_ivl_coll_spec l u PS2;
      RETURN (PS1e, PS2e, CXS, op_empty_coll)
    }
    else RETURN (op_empty_coll, op_empty_coll, op_empty_coll, mk_coll eX)
  }"
sublocale autoref_op_pat_def do_intersection_core .
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
  \<in>  clw_rel (\<langle>\<langle>lv_rel\<rangle>ivl_rel, \<langle>lv_rel\<rangle>plane_rel\<rangle>Refine_Rigorous_Numerics.inter_rel) \<rightarrow>
  \<langle>lv_rel\<rangle>ivl_rel \<rightarrow>
  \<langle>lv_rel\<rangle>sctn_rel \<rightarrow>
   \<langle>rnv_rel, appr1e_rel\<rangle>info_rel \<rightarrow>
  \<langle>clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel (\<langle>sappr_rel, \<langle>lv_rel\<rangle>sbelows_rel\<rangle>Refine_Rigorous_Numerics.inter_rel) \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  using do_intersection_core_impl.refine[where 'a='a] by force


lemma poincare_mapsto_scaleR2I:
  "poincare_mapsto P (scaleR2 x1 x2 baa) UNIV x1b (scaleR2 x1 x2 aca)"
  if "poincare_mapsto P (baa) UNIV x1b (aca)"
  using that
  apply (auto simp: poincare_mapsto_def scaleR2_def image_def vimage_def)
  apply (drule bspec, assumption)
  apply auto
  apply (rule exI, rule conjI, assumption)
  apply (rule exI, rule conjI, assumption, rule conjI, assumption)
  apply (rule bexI) prefer 2 apply assumption
  apply (auto simp: scaleR_blinfun_compose_right)
  done

lemma do_intersection_spec_scaleR2I:
  "do_intersection_spec UNIV sctns ivl sctn (scaleR2 x1 x2 baa) (scaleR2 x1 x2 aca, x1b)"
  if "do_intersection_spec UNIV sctns ivl sctn (baa) (aca, x1b)"
  using that
  by (auto simp: do_intersection_spec_def intro!: poincare_mapsto_scaleR2I)
     (auto simp: scaleR2_def image_def vimage_def)

lemma do_intersection_core[refine_vcg, le]:
  assumes wdp: "vwd_step (TYPE('n::enum))"
  notes [refine_vcg] = vwd_step vwd_stepD[OF wdp]
  shows "do_intersection_core sctns ivl sctn (X::'n eucl1 set) \<le>
    SPEC (\<lambda>(P1, P2, CX, X0s).
      do_intersection_spec UNIV sctns ivl sctn (X - X0s) (P1, CX) \<and>
      do_intersection_spec UNIV sctns ivl sctn (X - X0s) (P2, CX)
      \<and> fst ` (X - X0s) \<subseteq> CX
      \<and> X0s \<subseteq> X)"
  unfolding do_intersection_core_def autoref_tag_defs
  apply (refine_vcg assms, clarsimp_all)
  subgoal by (rule do_intersection_spec_scaleR2I) (auto simp: do_intersection_spec_def intro!: )
  subgoal by (rule do_intersection_spec_scaleR2I) (auto simp: do_intersection_spec_def intro!: )
  subgoal by (fastforce simp: scaleR2_def)
  subgoal by (auto simp: do_intersection_spec_def)
  subgoal by (auto simp: do_intersection_spec_def)
  done

definition "do_intersection_coll guards ivl sctn X =
  do {
    Xs \<leftarrow> sets_of_coll X;
    CHECKs ''nonempty inter nonfinite: '' (Xs \<noteq> {});
    RS \<leftarrow> PAR_IMAGE (\<lambda>X. \<lambda>(P1, P2, CX, X0s).
      do_intersection_spec UNIV guards ivl sctn (X - X0s) (P1, CX) \<and>
      do_intersection_spec UNIV guards ivl sctn (X - X0s) (P2, CX)
      \<and> fst ` (X - X0s) \<subseteq> CX
      \<and> X0s \<subseteq> X) (do_intersection_core guards ivl sctn) Xs;
    ASSUME (finite RS);
    RETURN ((\<Union>(X, (P1, P2, CX, X0s))\<in>RS. P1),
            (\<Union>(X, (P1, P2, CX, X0s))\<in>RS. P2),
            (\<Union>(X, (P1, P2, CX, X0s))\<in>RS. CX),
            (\<Union>(X, (P1, P2, CX, X0s))\<in>RS. X0s))
  }"
sublocale autoref_op_pat_def do_intersection_coll .

lemma finite_ra1eicacacslsbicae1lw: "(xc, x'c) \<in> \<langle>\<langle>rnv_rel, appr1e_rel\<rangle>info_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel
           (\<langle>sappr_rel,
            \<langle>lv_rel\<rangle>sbelows_rel\<rangle>Refine_Rigorous_Numerics.inter_rel) \<times>\<^sub>r
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

lemma poincare_mapsto_Union: "poincare_mapsto P (\<Union>xa) S CXS PS" 
  if "\<And>x. x \<in> xa \<Longrightarrow> poincare_mapsto P x S CXS PS"
  by (force simp: poincare_mapsto_def dest!: that)

lemma do_intersection_spec_Union:
  "do_intersection_spec S sctns ivl sctn (\<Union>X) A"
  if "\<And>x. x \<in> X \<Longrightarrow> do_intersection_spec S sctns ivl sctn x A"
    "X \<noteq> {}"
  using that(2)
  unfolding do_intersection_spec_def
  apply clarsimp
  apply safe
  subgoal by (rule poincare_mapsto_Union) (auto simp: do_intersection_spec_def dest!: that(1))
  subgoal by (auto simp: do_intersection_spec_def dest!: that(1))
  subgoal by (auto simp: do_intersection_spec_def dest!: that(1))
  subgoal by (fastforce simp: do_intersection_spec_def dest!: that(1))
  subgoal by (fastforce simp: do_intersection_spec_def dest!: that(1))
  subgoal by (fastforce simp: do_intersection_spec_def dest!: that(1))
  subgoal by (force simp: do_intersection_spec_def dest!: that(1))
  subgoal by (auto simp: do_intersection_spec_def dest!: that(1))
  subgoal by (fastforce simp: do_intersection_spec_def dest!: that(1))
  subgoal by (fastforce simp: do_intersection_spec_def dest!: that(1))
  done

lemma diff_subset: "(\<Union>x\<in>xa. f x) - (\<Union>x\<in>xa. g x) \<subseteq> (\<Union>x\<in>xa. f x - g x)"
  by auto

lemma do_intersection_spec_subset2:
  "do_intersection_spec S p ivl sctn X1 (ab, CY) \<Longrightarrow> CY \<subseteq> CX \<Longrightarrow> CX \<subseteq> Csafe \<Longrightarrow>
    CX \<inter> p = {} \<Longrightarrow> CX \<inter> ivl \<inter> plane_of sctn = {} \<Longrightarrow> X0 \<subseteq> X1 \<Longrightarrow>
  do_intersection_spec S p ivl sctn X0 (ab, CX)"
  by (auto simp: do_intersection_spec_def intro: poincare_mapsto_subset)

lemma do_intersection_spec_Union3:
  "do_intersection_spec S osctns ivl csctns (\<Union>x\<in>X. a x) ((\<Union>x\<in>X. b x), (\<Union>x\<in>X. c x))"
  if  "finite X" "X \<noteq> {}" "\<And>x. x \<in> X \<Longrightarrow> do_intersection_spec S osctns ivl csctns (a x) (b x, c x)"
  using that
proof induction
  case empty
  then show ?case by (auto simp: )
next
  case (insert x F)
  show ?case
    apply (cases "F = {}")
    subgoal using insert by simp
    subgoal 
      apply simp
      apply (rule do_intersection_spec_union)
       apply (rule insert.prems) apply simp
      apply (rule insert.IH)
       apply (assumption)
      apply (rule insert.prems) apply simp
      done
    done
qed

lemma do_intersection_coll[le]:
  assumes wdp: "vwd_step (TYPE('n::enum))"
  notes [refine_vcg] = vwd_step vwd_stepD[OF wdp]
  shows "do_intersection_coll sctns ivl sctn (X::'n eucl1 set) \<le>
    SPEC (\<lambda>(P1, P2, CX, X0s).
      do_intersection_spec UNIV sctns ivl sctn (X - X0s) (P1, CX) \<and>
      do_intersection_spec UNIV sctns ivl sctn (X - X0s) (P2, CX)
      \<and> fst ` (X - X0s) \<subseteq> CX
      \<and> X0s \<subseteq> X)"
  unfolding do_intersection_coll_def autoref_tag_defs
  apply (refine_vcg wdp, clarsimp_all)
  subgoal
    apply (rule do_intersection_spec_subset[OF _ diff_subset])
    apply (rule do_intersection_spec_Union3)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
  subgoal
    apply (rule do_intersection_spec_subset[OF _ diff_subset])
    apply (rule do_intersection_spec_Union3)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
  subgoal by fastforce
  subgoal by fastforce
  done

lemma poincare_mapsto_imp_flowsto:
  assumes "poincare_mapsto P X0 S CX X1"
  assumes "closed P"
  shows "flowsto X0 {0<..} (CX \<times> UNIV) (fst ` X1 \<times> UNIV)"
  unfolding flowsto_def
proof safe
  fix x0 d0 assume "(x0, d0) \<in> X0"
  with assms obtain D where D:
    "returns_to P x0"
    "fst ` X0 \<subseteq> S"
    "return_time P differentiable at x0 within S"
    "(poincare_map P has_derivative blinfun_apply D) (at x0 within S)"
    "(flow0 x0 (return_time P x0), D o\<^sub>L d0) \<in> X1"
    "\<And>t. 0 < t \<Longrightarrow> t < return_time P x0 \<Longrightarrow> flow0 x0 t \<in> CX"
    by (auto simp: poincare_mapsto_def poincare_map_def)
  show "\<exists>h\<in>{0<..}.
    h \<in> existence_ivl0 x0 \<and> (flow0 x0 h, Dflow x0 h o\<^sub>L d0) \<in> fst ` X1 \<times> UNIV \<and>
    (\<forall>h'\<in>{0<--<h}. (flow0 x0 h', Dflow x0 h' o\<^sub>L d0) \<in> CX \<times> UNIV)"
    by (auto intro!: bexI[where x="return_time P x0"] return_time_exivl D assms return_time_pos
        simp: open_segment_eq_real_ivl)
qed

lemma flowsto_poincare_mapsto_trans_flowsto:
  assumes "flowsto X0 T CX X1'"
  assumes "poincare_mapsto P X1 S CY X2"
  assumes "closed P"
  assumes "fst ` X1' \<subseteq> fst ` X1"
  assumes "X1' \<union> CX \<union> CY \<times> UNIV \<subseteq> CZ"
  assumes "\<And>t. t \<in> T \<Longrightarrow> t \<ge> 0"
  shows "flowsto X0 {0<..} CZ (fst ` X2 \<times> UNIV)"
proof -
  have X1D: "(a, b) \<in> X1' \<Longrightarrow> \<exists>c. (a, c) \<in> X1" for a b using assms(4) by force
  from poincare_mapsto_imp_flowsto[OF assms(2,3)]
  have "flowsto X1 {0<..} (CY \<times> UNIV) (fst ` X2 \<times> UNIV)" .
  then have "flowsto X1' {0<..} (CY \<times> UNIV) (fst ` X2 \<times> UNIV)"
    by (auto simp: flowsto_def dest!: X1D)
  from flowsto_trans[OF assms(1) this]
  show ?thesis
    apply (rule flowsto_subset)
    using assms
    by (auto intro!: add_nonneg_pos)
qed

lemma eq_blinfun_inner_left[intro]:
  "(\<lambda>x. x \<bullet> n) = blinfun_apply (blinfun_inner_left n)"
  by force

lemma
  do_intersection_flowsto_trans_outside:
  assumes "flowsto XS0 {0..} (CX \<times> UNIV) X1"
  assumes "do_intersection_spec UNIV guards ivl sctn X1 (P, CP)"
  assumes "fst ` X1 \<subseteq> CP"
  assumes "{x \<in> ivl. x \<in> plane_of sctn} \<inter> CX = {}"
  assumes "guards \<inter> (CX \<union> CP) = {}"
  assumes "XS0 \<subseteq> CX \<times> UNIV"
  assumes "closed ivl"
  assumes "CX \<subseteq> Csafe"
  shows "do_intersection_spec UNIV guards ivl sctn XS0 (P, CX \<union> CP)"
  using assms
  apply (auto simp: do_intersection_spec_def)
  subgoal
    apply (rule flowsto_poincare_trans, assumption, assumption)
    subgoal by simp
    subgoal by auto
    subgoal using assms(3) by auto
    subgoal by (auto intro!: closed_levelset_within continuous_intros simp: plane_of_def)
    subgoal premises prems for x d
    proof -
      have [intro, simp]: "closed {x \<in> ivl. x \<in> plane_of sctn} " "closed {x \<in> ivl. x \<bullet> normal sctn = pstn sctn}"
        by (auto intro!: closed_levelset_within continuous_intros simp: plane_of_def assms)
      from flowsto_poincare_mapsto_trans_flowsto[OF \<open>flowsto _ _ _ _\<close> \<open>poincare_mapsto _ _ _ _ _\<close> _ _ order_refl]
      have ft: "flowsto XS0 {0<..} (X1 \<union> CX \<times> UNIV \<union> CP \<times> UNIV) (fst ` P \<times> UNIV)"
        by (auto simp: )
      then have ret: "returns_to {x \<in> ivl. x \<bullet> normal sctn - pstn sctn = 0} x"
        apply (rule returns_to_flowstoI[OF _ _ _ _ _ _ order_refl])
        using prems by (auto simp: plane_of_def)
      have pm: "poincare_map {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} x \<in> fst ` P"
        apply (rule poincare_map_mem_flowstoI[OF ft])
        using prems by (auto simp: plane_of_def)
      from pm prems have "\<forall>\<^sub>F x in at (poincare_map {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} x) within
        plane_of sctn. x \<in> ivl"
        by auto
      from ret have "isCont (return_time {x \<in> ivl. x \<bullet> normal sctn - pstn sctn = 0}) x"
        apply (rule return_time_isCont_outside)
        using prems pm
        by (auto simp: eventually_at_filter plane_of_def intro!: assms derivative_eq_intros)
      then show "isCont (return_time {x \<in> ivl. x \<in> plane_of sctn}) x" by (simp add: plane_of_def)
    qed
    subgoal by simp
    done
  done

lemma flowsto_union_DiffE:
  assumes "flowsto X0 T CX (Y \<union> Z)"
  obtains X1 where "X1 \<subseteq> X0" "flowsto X1 T CX Y" "flowsto (X0 - X1) T CX Z"
proof -
  let ?X1 = "{x\<in>X0. flowsto {x} T CX Y}"
  from assms have "?X1 \<subseteq> X0" "flowsto ?X1 T CX Y" "flowsto (X0 - ?X1) T CX Z"
    by (auto simp: flowsto_def)
  thus ?thesis ..
qed

lemma do_intersection_coll_flowsto[le]:
  assumes wdp: "vwd_step (TYPE('n::enum))"
  assumes ft: "flowsto X0 {0..} (CX0 \<times> UNIV) X"
  assumes X_subset: "X \<subseteq> CX0 \<times> UNIV"
  assumes X0_subset: "X0 \<subseteq> CX0 \<times> UNIV" and CX0_safe: "CX0 \<subseteq> Csafe"
  assumes ci: "closed ivl"
  assumes disj: "ivl \<inter> plane_of sctn \<inter> CX0 = {}" "sctns \<inter> CX0 = {}"
  shows "do_intersection_coll sctns ivl sctn (X::'n eucl1 set) \<le>
    SPEC (\<lambda>(P1, P2, CX, X0s).
      \<exists>A.
        do_intersection_spec UNIV sctns ivl sctn A (P1, CX0 \<union> CX) \<and>
        do_intersection_spec UNIV sctns ivl sctn A (P2, CX0 \<union> CX) \<and>
        flowsto (X0 - A) {0..} (CX0 \<times> UNIV) X0s \<and>
        A \<subseteq> X0 \<and>
        P1 \<inter> X0s = {} \<and>
        P2 \<inter> X0s = {})"
  apply (rule do_intersection_coll)
   apply (rule wdp)
proof (clarsimp, goal_cases)
  case (1 P1 P2 CX R)
  from ft have "flowsto X0 {0..} (CX0 \<times> UNIV) (X - R \<union> R)"
    by (rule flowsto_subset) auto
  from flowsto_union_DiffE[OF this]
  obtain A where AB: "A \<subseteq> X0"
    and A: "flowsto A {0..} (CX0 \<times> UNIV) (X - R)"
    and B: "flowsto (X0 - A) {0..} (CX0 \<times> UNIV) (R)"
    by auto
  have di: "do_intersection_spec UNIV sctns ivl sctn A (P1, CX0 \<union> CX)"
    apply (rule do_intersection_flowsto_trans_outside[OF A 1(1)])
    subgoal using 1 by simp
    subgoal using disj by auto
    subgoal using 1 disj by (auto simp: do_intersection_spec_def)
    subgoal using X0_subset AB by (auto simp: do_intersection_spec_def)
    subgoal using ci by simp
    subgoal using CX0_safe .
    done
  then have "P1 \<subseteq> (ivl \<inter> plane_of sctn) \<times> UNIV"
    by (auto simp: do_intersection_spec_def)
  then have disjoint: "P1 \<inter> R = {}"
    using \<open>R \<subseteq> X\<close> disj X_subset
      apply (auto simp: subset_iff)
    by (metis (no_types, lifting) Int_iff disjoint_iff_not_equal)

  have di2: "do_intersection_spec UNIV sctns ivl sctn A (P2, CX0 \<union> CX)"
    apply (rule do_intersection_flowsto_trans_outside[OF A 1(2)])
    subgoal using 1 by simp
    subgoal using disj by auto
    subgoal using 1 disj by (auto simp: do_intersection_spec_def)
    subgoal using X0_subset AB by (auto simp: do_intersection_spec_def)
    subgoal using ci by simp
    subgoal using CX0_safe .
    done
  then have "P2 \<subseteq> (ivl \<inter> plane_of sctn) \<times> UNIV"
    by (auto simp: do_intersection_spec_def)
  then have "P2 \<inter> R = {}"
    using \<open>R \<subseteq> X\<close> disj X_subset
      apply (auto simp: subset_iff)
    by (metis (no_types, lifting) Int_iff disjoint_iff_not_equal)
  from AB this disjoint di di2 B show ?case
    by (auto simp:)
qed

definition "op_enlarge_ivl_sctn ivl sctn d = do {
    (l, u) \<leftarrow> ivl_rep ivl;
    CHECKs ''op_enlarge_ivl_sctn: trying to shrink'' (d \<ge> 0);
    CHECKs ''op_enlarge_ivl_sctn: empty ivl'' (l \<le> u);
    CHECKs ''op_enlarge_ivl_sctn: not in Basis'' (abs (normal sctn) \<in> set Basis_list);
    let dOne = sum_list (map (\<lambda>i. d *\<^sub>R i) Basis_list) - d *\<^sub>R abs (normal sctn);
    ASSERT (l - dOne \<le> u + dOne);
    RETURN (op_atLeastAtMost_ivl (l - dOne) (u + dOne))
  }"
sublocale autoref_op_pat_def op_enlarge_ivl_sctn .

schematic_goal op_enlarge_ivl_sctn_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(ivli, ivl::'a set) \<in> lvivl_rel" "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel" "(di, d) \<in> rnv_rel"
  shows "(nres_of ?R, op_enlarge_ivl_sctn $ ivl $ sctn $ d) \<in> \<langle>lvivl_rel\<rangle>nres_rel"
  unfolding op_enlarge_ivl_sctn_def
  including art
  by (autoref_monadic)
concrete_definition op_enlarge_ivl_sctn_impl for ivli sctni di uses op_enlarge_ivl_sctn_impl
lemmas [autoref_rules] = op_enlarge_ivl_sctn_impl.refine

lemma op_enlarge_ivl_sctn[le, refine_vcg]:
  "op_enlarge_ivl_sctn ivl sctn d \<le> SPEC (\<lambda>ivl'. ivl \<subseteq> ivl')"
  unfolding op_enlarge_ivl_sctn_def
  apply refine_vcg
  unfolding plane_of_def
  apply (safe intro!: eventually_in_planerectI)
  apply (auto  intro!: simp: eucl_le[where 'a='a] inner_sum_left inner_Basis if_distrib
     algebra_simps cong: if_cong)
  done

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

lemma eucl_less_le_trans:
  fixes a b::"'a::executable_euclidean_space"
  shows "eucl_less a b \<Longrightarrow> b \<le> c \<Longrightarrow> eucl_less a c"
  by (force simp: eucl_less_def[where 'a='a] eucl_le[where 'a='a])

lemma le_eucl_less_trans:
  fixes a b::"'a::executable_euclidean_space"
  shows "a \<le> b \<Longrightarrow> eucl_less b c \<Longrightarrow> eucl_less a c"
  by (force simp: eucl_less_def[where 'a='a] eucl_le[where 'a='a])

lemma wd_stepD':
  assumes "wd_step TYPE('a::executable_euclidean_space)"
  shows "0 < rk2_param optns"
    "rk2_param optns \<le> 1"
    "ode_slp_eq ode_slp"
    "rk2_slp_eq rk2_slp D"
    "euler_slp_eq euler_slp D"
    "euler_incr_slp_eq euler_incr_slp D"
    "wd TYPE('a)"
  using assms by (auto simp: wd_step_def)

definition "guardset guards = Union (case_prod (\<inter>) ` (\<lambda>(x, y). (x, plane_of y)) ` guards)"

definition "resolve_ivlplanes (guards::'n::enum rvec set)
                          (ivlplanes::'n::enum rvec set)
                          XS
                           =
  FORWEAK XS (RETURN ({}))
     (\<lambda>(ivlplane, X).
      do {
        (ivl, plane) \<leftarrow> (get_inter (ivlplane));
        ASSUME (closed ivl);
        sctn \<leftarrow> (get_plane plane);
        b \<leftarrow> subset_iplane_coll ivlplane ivlplanes;
        CHECKs ''reach_conts: subsets_iplane_coll'' b;
        (PS1, PS2, CXS, RS) \<leftarrow> (do_intersection_coll guards ivl sctn X);
        RETURN {(uninfo X, PS1, PS2, RS, ivl, sctn, CXS)}
      })
      (\<lambda>(PS) (PS'). RETURN (PS' \<union> PS))"
sublocale autoref_op_pat_def resolve_ivlplanes .

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
  by (autoref_monadic)
concrete_definition resolve_ivlplanes_impl for guardsi ivlplanesi XSi uses resolve_ivlplanes_impl
lemmas [autoref_rules] = resolve_ivlplanes_impl.refine

lemma resolve_ivlplanes[le]:
  assumes wdp: "vwd_step (TYPE('a::enum))"
  assumes
    "\<forall>x\<in>Xg. case x of (I, G) \<Rightarrow> flowsto (XSf G) {0..} (CXS \<times> UNIV) G"
    "(\<Union>x\<in>Xg. snd x) \<subseteq> (Csafe - (ivlplanes \<union> guards)) \<times> UNIV"
    "CXS \<times> UNIV \<subseteq> (Csafe - (ivlplanes \<union> guards)) \<times> UNIV"
    "(\<Union>a\<in>Xg. XSf (snd a)) \<subseteq> (CXS::'a rvec set) \<times> UNIV"
    "(\<Union>x\<in>Xg. snd x) \<subseteq> CXS \<times> UNIV"
    "(\<Union>x\<in>Xg. fst x) \<subseteq> ivlplanes \<union> guards"
  notes [refine_vcg] = wdp vwd_step vwd_stepD[OF wdp]
  shows "resolve_ivlplanes guards ivlplanes Xg \<le> SPEC (\<lambda>PS.
    CXS \<inter> (guards \<union> ivlplanes) = {} \<and>
    CXS \<subseteq> Csafe \<and>
    (\<exists>R0 P0. (\<Union>x\<in>PS. P0 x) \<union> (\<Union>x\<in>PS. R0 x) = (\<Union>a\<in>Xg. XSf (snd a))\<and>
       (\<forall>x\<in>PS. case x of (X, P1, P2, R, ivl, sctn, CX) \<Rightarrow>
          ivl \<inter> plane_of sctn \<subseteq> ivlplanes \<and> closed ivl \<and>
          P0 (X, P1, P2, R, ivl, sctn, CX) \<inter> R0 (X, P1, P2, R, ivl, sctn, CX) = {} \<and>
          R0 (X, P1, P2, R, ivl, sctn, CX) \<subseteq> (CXS \<times> UNIV) \<and>
          flowsto (R0 (X, P1, P2, R, ivl, sctn, CX)) {0..} (CXS \<times> UNIV) R \<and>
          do_intersection_spec UNIV guards ivl sctn (P0 (X, P1, P2, R, ivl, sctn, CX)) (P1, CXS \<union> CX) \<and>
          do_intersection_spec UNIV guards ivl sctn (P0 (X, P1, P2, R, ivl, sctn, CX)) (P2, CXS \<union> CX))))"
  using assms
  unfolding resolve_ivlplanes_def
  apply clarsimp_all
  apply (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xgs PS.
      (\<exists>R0 P0.
        snd ` Xgs \<subseteq> fst ` PS \<and> fst ` PS \<subseteq> snd ` Xg \<and>
        (\<forall>(X, P1, P2, R, ivl, sctn, CX) \<in> PS.
            P0 (X, P1, P2, R, ivl, sctn, CX) \<union> R0 (X, P1, P2, R, ivl, sctn, CX) = XSf X
          \<and> ivl \<inter> plane_of sctn \<subseteq> ivlplanes \<and> closed ivl
          \<and> P0 (X, P1, P2, R, ivl, sctn, CX) \<inter> R0 (X, P1, P2, R, ivl, sctn, CX) = {}
          \<and> R0 (X, P1, P2, R, ivl, sctn, CX) \<subseteq> (CXS \<times> UNIV)
          \<and> flowsto (R0 (X, P1, P2, R, ivl, sctn, CX)) {0..} (CXS \<times> UNIV) R
          \<and> do_intersection_spec UNIV guards ivl sctn (P0 (X, P1, P2, R, ivl, sctn, CX)) (P1, CXS \<union> CX)
          \<and> do_intersection_spec UNIV guards ivl sctn (P0 (X, P1, P2, R, ivl, sctn, CX)) (P2, CXS \<union> CX)))"],
        clarsimp_all)
    using [[goals_limit=1]]
    subgoal by auto
    subgoal by auto
    subgoal for a b c
      apply (frule bspec, assumption, clarsimp)
      apply (rule do_intersection_coll_flowsto)
              apply (rule wdp)
             apply assumption
            apply force
           apply force
          apply blast
         apply assumption
      subgoal premises prems
      proof -
        have "(b \<inter> plane_of c, a) \<in> Xg" using prems by simp
        with \<open>(\<Union>x\<in>Xg. fst x) \<subseteq> ivlplanes \<union> guards\<close>
        have "b \<inter> plane_of c \<subseteq> ivlplanes \<union> guards"
          by (force simp: subset_iff)
        then show ?thesis
          using \<open>CXS \<times> UNIV \<subseteq> (Csafe - (ivlplanes \<union> guards)) \<times> UNIV\<close>
          by auto
      qed
      subgoal by (auto simp: subset_iff)
      subgoal apply (refine_vcg, clarsimp_all) apply force
        apply (intro exI conjI)defer defer defer apply assumption+
         apply simp
         apply force
        apply force
        apply force
        done
      done
    subgoal by (auto simp: subset_iff) blast
    subgoal for a b c d e f R0 P0
      apply (frule bspec, assumption, clarsimp)
      apply (rule do_intersection_coll_flowsto)
              apply (rule wdp)
             apply assumption
      subgoal
        apply (rule order_trans[where y="(\<Union>x\<in>Xg. snd x)"]) 
        by auto
      subgoal
        apply (rule order_trans) defer apply assumption
        by auto
      subgoal by blast
      subgoal by simp
      subgoal premises prems
      proof -
        have "(d \<inter> plane_of e, c) \<in> Xg" using prems by simp
        with \<open>(\<Union>x\<in>Xg. fst x) \<subseteq> ivlplanes \<union> guards\<close>
        have "d \<inter> plane_of e \<subseteq> ivlplanes \<union> guards"
          by (force simp: subset_iff)
        then show ?thesis
          using \<open>CXS \<times> UNIV \<subseteq> (Csafe - (ivlplanes \<union> guards)) \<times> UNIV\<close>
          by auto
      qed
      subgoal by (auto simp: subset_iff)
      subgoal
        apply (refine_vcg, clarsimp_all)
        subgoal by (auto simp: subset_iff)
        subgoal by (auto simp: )
        subgoal for x1 x1' x2 x3 A
          apply (rule exI[where x="R0((c, x1, x1', x3, d, e, x2):=(XSf c - A))"])
          apply (rule exI[where x="P0((c, x1, x1', x3, d, e, x2):=A)"])
          apply clarsimp
          apply (rule conjI)
          subgoal by auto
          apply (rule conjI)
          subgoal premises prems
            using prems
            apply (auto simp: subset_iff)
            by fastforce
          apply clarsimp
          subgoal
            apply (drule bspec, assumption)
            apply (drule bspec, assumption)
            by force
          done
        done
      done
    subgoal by (auto simp: subset_iff)
    subgoal by (auto simp: subset_iff)
    subgoal for a R0 P0
      apply (rule exI[where x=R0])
      apply (rule exI[where x=P0])
      apply (rule conjI)
      subgoal premises prems
      proof -
        note prems
        show ?thesis
          using prems(9,8)
          by fastforce
      qed
      by auto
    done


definition "poincare_onto ro \<comment> \<open>options\<close>
                          symstart trap \<comment> \<open>symbolic start and trap\<close>
                          (guards::'n::enum rvec set) \<comment> \<open>avoiding guards\<close>
                          (ivlplanes::'n::enum rvec set) \<comment> \<open>target sections\<close>
                          (XS0::'n eucl1 set)
                          (CXS0::'n rvec set)
     =
  do {
    (CXS, XS, X0s) \<leftarrow> (reach_conts ro (symstart:::appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel) trap (ivlplanes \<union> guards) XS0:::
      \<langle>clw_rel sappr_rel \<times>\<^sub>r \<langle>iplane_rel lvivl_rel \<times>\<^sub>r clw_rel (iinfo_rel appr1e_rel)\<rangle>list_wset_rel \<times>\<^sub>r
     ghost_rel\<rangle>nres_rel);
    PS \<leftarrow> resolve_ivlplanes guards ivlplanes XS;
    ASSUME (CXS0 \<subseteq> Csafe);
    RETURN ((\<lambda>(X, P1, P2, R, ivl, sctn, CX). (X, P1, P2, R, ivl, sctn, CX, CXS \<union> CXS0)) ` PS)
  }"
sublocale autoref_op_pat_def poincare_onto .

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

lemma poincare_onto[le, refine_vcg]:
  assumes wdp: "vwd_step (TYPE('a::enum))"
  assumes [refine_vcg]: "\<And>X0. X0 \<subseteq> Csafe \<times> UNIV \<Longrightarrow> symstart X0 \<le>
    SPEC (\<lambda>(CX, X). flowsto (X0 - trap \<times> UNIV) {0..} (CX \<times> UNIV) X)"
  notes [refine_vcg] = wdp vwd_step vwd_stepD[OF wdp]
  assumes CXS0: "CXS0 \<inter> (guards \<union> ivlplanes) = {}"
  shows "poincare_onto ro symstart trap guards ivlplanes (XS0::'a eucl1 set) CXS0 \<le>
    SPEC (\<lambda>PS.
      (\<exists>R0 P0.
        \<Union>(P0 ` PS \<union> R0 ` PS) = XS0 - trap \<times> UNIV \<and>
        (\<forall>(X, P1, P2, R, ivl, sctn, CX, CXS) \<in> PS.
            ivl \<inter> plane_of sctn \<subseteq> ivlplanes \<and> closed ivl
          \<and> XS0 \<subseteq> CXS \<times> UNIV \<and> CXS0 \<subseteq> CXS \<and> CXS \<inter> (guards \<union> ivlplanes) = {}
          \<and> P0 (X, P1, P2, R, ivl, sctn, CX, CXS) \<inter> R0 (X, P1, P2, R, ivl, sctn, CX, CXS) = {}
          \<and> R0 (X, P1, P2, R, ivl, sctn, CX, CXS) \<subseteq> CXS \<times> UNIV
          \<and> flowsto (R0 (X, P1, P2, R, ivl, sctn, CX, CXS)) {0..} (CXS \<times> UNIV) R
          \<and> do_intersection_spec UNIV guards ivl sctn (P0 (X, P1, P2, R, ivl, sctn, CX, CXS)) (P1, CXS \<union> CX)
          \<and> do_intersection_spec UNIV guards ivl sctn (P0 (X, P1, P2, R, ivl, sctn, CX, CXS)) (P2, CXS \<union> CX))
        ))"
  unfolding poincare_onto_def autoref_tag_defs
  using [[goals_limit=1]]
  apply (refine_vcg, clarsimp_all)
  apply (refine_vcg resolve_ivlplanes[OF wdp])
  subgoal by force
  apply clarsimp
  subgoal for a b c d R0 P0
    apply (rule exI[where x="\<lambda>(X, P1, P2, R, ivl, sctn, CX, CXS). R0 (X, P1, P2, R, ivl, sctn, CX)"])
    apply (rule exI[where x="\<lambda>(X, P1, P2, R, ivl, sctn, CX, CXS). P0 (X, P1, P2, R, ivl, sctn, CX)"])
    apply (rule conjI)
    subgoal premises prems
      using \<open>(\<Union>x\<in>d. P0 x) \<union> (\<Union>x\<in>d. R0 x) = (\<Union>x\<in>b. c (snd x)) - trap \<times> UNIV\<close>
      by auto
    subgoal
      apply clarsimp
      apply (drule bspec, assumption)+
      apply (rule conjI, force)
      apply (rule conjI, force)
      apply (rule conjI, force)
      apply (rule conjI)
      subgoal using CXS0 by (auto simp: )
      apply (rule conjI, force)
      apply (rule conjI, force)
      apply (rule conjI)
      subgoal by (auto intro: flowsto_subset)
      subgoal
        apply clarsimp
        apply (rule conjI)
        subgoal
          apply (rule do_intersection_spec_subset2, assumption)
          subgoal by force
          subgoal by (force simp: do_intersection_spec_def)
          subgoal using CXS0 by (auto simp: do_intersection_spec_def)
          subgoal using CXS0 by (auto simp: do_intersection_spec_def)
          subgoal by auto
          done
        subgoal
          apply (rule do_intersection_spec_subset2, assumption)
          subgoal by force
          subgoal by (force simp: do_intersection_spec_def)
          subgoal using CXS0 by (auto simp: do_intersection_spec_def)
          subgoal using CXS0 by (auto simp: do_intersection_spec_def)
          subgoal by auto
          done
        done
      done
    done
  done

definition "empty_remainders PS =
  FORWEAK PS (RETURN True) (\<lambda>(X, P1, P2, R, ivl, sctn, CX, CXS). do { e \<leftarrow> isEmpty_spec R; RETURN e})
    (\<lambda>a b. RETURN (a \<and> b))"
sublocale autoref_op_pat_def empty_remainders .
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

lemma empty_remainders[le, refine_vcg]:
  "empty_remainders PS \<le> SPEC (\<lambda>b. b \<longrightarrow> (\<forall>(X, P1, P2, R, ivl, sctn, CX) \<in> PS. R = {}))"
  unfolding empty_remainders_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs b. b \<longrightarrow> (\<forall>(X, P1, P2, R, ivl, sctn, CX) \<in> Xs. R = {})"])
     auto

definition [simp]: "empty_trap = {}"
sublocale autoref_op_pat_def empty_trap .
lemma empty_trap_impl[autoref_rules]: "((), empty_trap) \<in> ghost_rel"
  by (auto intro!: ghost_relI)
definition empty_symstart::"((real, 'a) vec \<times> (real, 'a) vec \<Rightarrow>\<^sub>L (real, 'a) vec) set
   \<Rightarrow> ((real, 'a) vec set \<times> ((real, 'a) vec \<times> (real, 'a) vec \<Rightarrow>\<^sub>L (real, 'a) vec) set) nres"
  where [simp]: "empty_symstart \<equiv> \<lambda>X. RETURN (op_empty_coll, mk_coll X)"
sublocale autoref_op_pat_def empty_symstart .
lemma empty_symstart_impl[autoref_rules]:
  "((\<lambda>x. nres_of (dRETURN ([], [x]))), empty_symstart) \<in>
    appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  unfolding empty_symstart_def
  using mk_coll[unfolded autoref_tag_defs, OF sv_appr1e_rel[OF sv_appr1_rel], param_fo]
  by (auto intro!: nres_relI simp:)

definition "poincare_onto_empty ro \<comment> \<open>options\<close>
                          (guards::'n::enum rvec set) \<comment> \<open>avoiding guards\<close>
                          (ivlplanes::'n::enum rvec set) \<comment> \<open>target sections\<close>
                          (XS0::'n eucl1 set) =
  poincare_onto ro (OP empty_symstart:::appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel)
    empty_trap guards ivlplanes XS0"
sublocale autoref_op_pat_def poincare_onto_empty .

lemma poincare_onto_empty[le, refine_vcg]:
  assumes wdp: "vwd_step (TYPE('a::enum))"
  notes [refine_vcg] = wdp vwd_step vwd_stepD[OF wdp]
  assumes CXS0: "CXS0 \<inter> (guards \<union> ivlplanes) = {}"
  shows "poincare_onto_empty ro guards ivlplanes (XS0::'a eucl1 set) CXS0 \<le>
    SPEC (\<lambda>(PS).
      (\<exists>R0 P0.
        \<Union>(P0 ` PS \<union> R0 ` PS) = XS0 \<and>
        (\<forall>(X, P1, P2, R, ivl, sctn, CX, CXS) \<in> PS.
            ivl \<inter> plane_of sctn \<subseteq> ivlplanes \<and> closed ivl
          \<and> XS0 \<subseteq> CXS \<times> UNIV \<and> CXS0 \<subseteq> CXS \<and> CXS \<inter> (guards \<union> ivlplanes) = {}
          \<and> P0 (X, P1, P2, R, ivl, sctn, CX, CXS) \<inter> R0 (X, P1, P2, R, ivl, sctn, CX, CXS) = {}
          \<and> R0 (X, P1, P2, R, ivl, sctn, CX, CXS) \<subseteq> CXS \<times> UNIV
          \<and> flowsto (R0 (X, P1, P2, R, ivl, sctn, CX, CXS)) {0..} (CXS \<times> UNIV) R
          \<and> do_intersection_spec UNIV guards ivl sctn (P0 (X, P1, P2, R, ivl, sctn, CX, CXS)) (P1, CXS \<union> CX)
          \<and> do_intersection_spec UNIV guards ivl sctn (P0 (X, P1, P2, R, ivl, sctn, CX, CXS)) (P2, CXS \<union> CX))
        ))"
  using CXS0
  unfolding poincare_onto_empty_def autoref_tag_defs
  by (refine_vcg) (auto intro!: flowsto_self)

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


definition "poincare_onto2 ro \<comment> \<open>options\<close>
                          symstart trap \<comment> \<open>symbolic start and trap\<close>
                          (guards::'n::enum rvec set) \<comment> \<open>avoiding guards\<close>
                          (ivlplanes::'n::enum rvec set) \<comment> \<open>target sections\<close>
                          (XS0::'n eucl1 set) =
  do {
    (PS) \<leftarrow> (poincare_onto ro (symstart:::appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel)
      trap guards ivlplanes XS0 op_empty_coll:::
      \<langle>\<langle>clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel \<times>\<^sub>r
        clw_rel (isbelows_rel sappr_rel) \<times>\<^sub>r clw_rel sappr_rel\<rangle>list_wset_rel\<rangle>nres_rel);
    (PS2) \<leftarrow> FORWEAK PS (RETURN ({})) (\<lambda>(X, P1, P2, R, ivl, sctn, CX, CXS).
      if op_coll_is_empty R then RETURN ({})
      else do {
        ivlplaness \<leftarrow> (sets_of_coll ivlplanes:::\<langle>\<langle>iplane_rel lvivl_rel\<rangle>list_wset_rel\<rangle>nres_rel);
        ivlplaness' \<leftarrow> op_set_ndelete (mk_inter ivl (plane_of sctn)) ivlplaness;
        let ivlplanes' = (\<Union>(mk_coll ` ivlplaness':::\<langle>clw_rel (iplane_rel lvivl_rel)\<rangle>list_wset_rel));
        PS' \<leftarrow> (poincare_onto_empty ro (guards) ivlplanes' R CXS:::
            \<langle>\<langle>clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel
            \<times>\<^sub>r clw_rel (isbelows_rel sappr_rel) \<times>\<^sub>r clw_rel sappr_rel\<rangle>list_wset_rel\<rangle>nres_rel);
        b \<leftarrow> empty_remainders PS';
        CHECKs (ST ''poincare_onto2: empty remainders!'') b;
        ASSUME (finite PS');
        RETURN PS'
        }) (\<lambda>PS PS'. RETURN (PS' \<union> PS));
      RETURN (Pair True ` PS2 \<union> Pair False ` PS)
    }"
sublocale autoref_op_pat_def poincare_onto2 .

lemma sv_thingy: "single_valued (clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          \<langle>lv_rel\<rangle>ivl_rel \<times>\<^sub>r
          \<langle>lv_rel\<rangle>sctn_rel \<times>\<^sub>r
          clw_rel
           (\<langle>sappr_rel,
            \<langle>lv_rel\<rangle>sbelows_rel\<rangle>Refine_Rigorous_Numerics.inter_rel) \<times>\<^sub>r
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
  by (autoref_monadic)
concrete_definition poincare_onto2_impl for guardsi XSi uses poincare_onto2_impl
lemmas [autoref_rules] = poincare_onto2_impl.refine

lemma FORWEAK_mono_rule'':
  fixes f::"'d \<Rightarrow> 'e nres" and c::"'e \<Rightarrow> 'e \<Rightarrow> 'e nres" and I::"'d set \<Rightarrow> 'e \<Rightarrow> bool"
  assumes empty: "S = {} \<Longrightarrow> d \<le> SPEC P"
  assumes I0[THEN order_trans]: "\<And>s. s \<in> S \<Longrightarrow> f s \<le> SPEC (I {s})"
  assumes I_mono: "\<And>it it' \<sigma>. I it \<sigma> \<Longrightarrow> it' \<subseteq> it \<Longrightarrow> it \<subseteq> S \<Longrightarrow> I it' \<sigma>"
  assumes IP[THEN order_trans]:
    "\<And>x it \<sigma>. \<lbrakk> x\<in>S; x \<notin> it; it\<subseteq>S; I it \<sigma> \<rbrakk> \<Longrightarrow> f x \<le> SPEC (\<lambda>f'. c \<sigma> f' \<le> SPEC (I (insert x it)))"
  assumes II: "\<And>\<sigma>. I S \<sigma> \<Longrightarrow> P \<sigma>"
  shows "FORWEAK S d f c \<le> SPEC P"
  apply (rule FORWEAK_invarI[where I="\<lambda>b X. X \<subseteq> S \<and> I (S - X) b"])
  subgoal by (rule empty)
  subgoal by (auto simp: Diff_Diff_Int intro!: I0)
  subgoal
    by (metis (mono_tags, lifting) Diff_cancel I0 I_mono Refine_Basic.RES_sng_eq_RETURN iSPEC_rule
        less_eq_nres.simps(2) nres_order_simps(21) subset_insertI subset_refl)
  subgoal for a b it
    apply (rule IP[of _ "S - it" b])
    subgoal by force
    subgoal by force
    subgoal by force
    subgoal by force
    subgoal
      apply clarsimp
      apply (rule order_trans, assumption)
      by (auto simp: it_step_insert_iff intro: order_trans)
    done
  subgoal for a b it
    apply (rule IP[of _ "S - it" b])
    subgoal by force
    subgoal by force
    subgoal by force
    subgoal by force
    subgoal
      apply clarsimp
      apply (rule order_trans, assumption)
      by (auto simp: it_step_insert_iff intro: I_mono)
    done
  subgoal by (auto intro!: II)
  done

lemma FORWEAK_mono_rule_empty:
  fixes f::"'d \<Rightarrow> 'e nres" and c::"'e \<Rightarrow> 'e \<Rightarrow> 'e nres" and I::"'d set \<Rightarrow> 'e \<Rightarrow> bool"
  assumes empty: "S = {} \<Longrightarrow> RETURN d \<le> SPEC P"
  assumes I0: "I {} d"
  assumes I1: "\<And>s x. s \<in> S \<Longrightarrow> c d x \<le> SPEC (I {s}) \<Longrightarrow> I {s} x"
  assumes I_mono: "\<And>it it' \<sigma>. I it \<sigma> \<Longrightarrow> it' \<subseteq> it \<Longrightarrow> it \<subseteq> S \<Longrightarrow> I it' \<sigma>"
  assumes II: "\<And>\<sigma>. I S \<sigma> \<Longrightarrow> P \<sigma>"
  assumes IP: "\<And>x it \<sigma>. \<lbrakk> x\<in>S; x \<notin> it; it\<subseteq>S; I it \<sigma> \<rbrakk> \<Longrightarrow> f x \<le> SPEC (\<lambda>f'. c \<sigma> f' \<le> SPEC (I (insert x it)))"
  shows "FORWEAK S (RETURN d) f c \<le> SPEC P"
  apply (rule FORWEAK_mono_rule''[where S=S and I=I and P=P])
  subgoal by (rule empty)
  subgoal for s
    apply (rule IP[of _ "{}" d, le])
       apply assumption
       apply force
       apply force
     apply (rule I0)
    by (auto intro!: I1)
  subgoal by (rule I_mono)
  subgoal by (rule IP)
  subgoal by (rule II)
  done

lemma flowsto_source_UnionI:
  assumes "\<And>i. i \<in> I \<Longrightarrow> flowsto i T CXS (f i)"
  shows "flowsto (\<Union>I) T CXS (\<Union>(f ` I))"
  apply (auto simp: flowsto_def)
  subgoal premises prems for y a b
    using assms[unfolded flowsto_def, OF \<open>y \<in> I\<close>, rule_format, OF \<open>_ \<in> y\<close>] prems
    by auto
  done

lemma do_intersection_spec_union2:
  assumes "do_intersection_spec S osctns ivl csctns a (b, c)"
    "do_intersection_spec S osctns ivl csctns f (b, c)"
  shows "do_intersection_spec S osctns ivl csctns (a \<union> f) (b, c)"
  using do_intersection_spec_union[OF assms]
  by auto

lemma poincare_onto2[le, refine_vcg]:
  assumes wdp: "vwd_step (TYPE('a::enum))"
  assumes [refine_vcg]: "\<And>X0. X0 \<subseteq> Csafe \<times> UNIV \<Longrightarrow> symstart X0 \<le>
    SPEC (\<lambda>(CX, X). flowsto (X0 - trap \<times> UNIV) {0..} (CX \<times> UNIV) X)"
  notes [refine_vcg] = wdp vwd_step vwd_stepD[OF wdp]
  notes [refine_vcg_def] = op_set_ndelete_spec
  shows "poincare_onto2 ro symstart trap guards ivlplanes (XS0::'a eucl1 set) \<le>
    SPEC (\<lambda>(PS).
      (\<exists>P0. \<Union>(P0 ` PS) = XS0 - trap \<times> UNIV \<and>
        (\<forall>(s, X, P1, P2, R, ivl, sctn, CX, CXS) \<in> PS.
          XS0 \<subseteq> CXS \<times> UNIV \<and>
          do_intersection_spec UNIV guards ivl sctn (P0 (s, X, P1, P2, R, ivl, sctn, CX, CXS)) (P1, CXS \<union> CX) \<and>
          do_intersection_spec UNIV guards ivl sctn (P0 (s, X, P1, P2, R, ivl, sctn, CX, CXS)) (P2, CXS \<union> CX))))"
  unfolding poincare_onto2_def autoref_tag_defs
  apply (refine_vcg, clarsimp_all)
  subgoal for PS R0 P0
    apply (rule FORWEAK_mono_rule_empty[where I="\<lambda>PS1 PS2.
      (\<exists>X0.
        \<Union>(R0 ` PS1) \<subseteq> \<Union>(X0 ` PS2) \<and>
        (\<forall>(X, P1, P2, R, ivl, sctn, CX, CXS) \<in> PS2.
          XS0 \<subseteq> CXS \<times> UNIV \<and>
          do_intersection_spec UNIV guards ivl sctn (X0 (X, P1, P2, R, ivl, sctn, CX, CXS)) (P1, CXS \<union> CX) \<and>
          do_intersection_spec UNIV guards ivl sctn (X0 (X, P1, P2, R, ivl, sctn, CX, CXS)) (P2, CXS \<union> CX)))"])
    subgoal by refine_vcg
    subgoal by auto
    subgoal by auto
    subgoal
      apply clarsimp
      subgoal for c
        apply (rule exI[where x=c])
        apply (rule conjI)
         apply (rule order_trans) prefer 2 apply assumption
         apply (rule UN_mono) apply assumption apply (rule order_refl) apply assumption
        done
      done
    subgoal for \<sigma>
      apply (clarsimp)
      subgoal for X0
        apply (rule exI[where x="\<lambda>(b, x). (if b then X0 x else P0 x) \<inter> XS0 - trap \<times> UNIV "])
        apply (rule conjI)
        subgoal premises prems
          using \<open>(\<Union>x\<in>PS. P0 x) \<union> (\<Union>x\<in>PS. R0 x) = XS0 - trap \<times> UNIV\<close>
            \<open>(\<Union>x\<in>PS. R0 x) \<subseteq> (\<Union>x\<in>\<sigma>. X0 x)\<close>
          by auto
        subgoal by (auto intro: do_intersection_spec_subset)
        done
      done
    apply clarsimp
    subgoal for a b b' c d e f g h i j
      apply (cases "c = {}")
      subgoal by (auto intro!: exI[where x="j"])
      subgoal
        using [[goals_limit=1]]
        apply clarsimp
        apply refine_vcg
        subgoal premises prems for k l
        proof -
          note prems
          then show ?thesis
            apply -
            apply (drule bspec, assumption)+
            apply clarsimp
            subgoal premises prems
              using \<open>g \<inter> (guards \<union> \<Union>k) = {}\<close> \<open>l = k - {d \<inter> plane_of e} \<or> l = k\<close> \<open>d \<inter> plane_of e \<subseteq> \<Union>k\<close>
              by auto
            done
        qed
        apply simp
        apply (drule bspec, assumption)
        apply simp
        apply (erule exE conjE)+
        subgoal for k l m n p q
          apply (subgoal_tac "\<And>x. x \<in> m \<Longrightarrow> p x = {}")
           defer
          subgoal for x
          proof goal_cases
            case 1
            from 1(10,15,24)
            show ?case
              by (auto dest!: bspec[where x=x])
          qed
          apply simp
          subgoal premises prems
          proof -
            note prems
            from prems have "finite (q ` m)" "flowsto (R0 (a, b, b', c, d, e, f, g)) {0..} (g \<times> UNIV) (UNION m q)"
              by auto
            from flowsto_Union_funE[OF this]
            obtain XGs where
              XGs: "\<And>G. G \<in> q ` m \<Longrightarrow> flowsto (XGs G) {0..} (g \<times> UNIV) G"
              "R0 (a, b, b', c, d, e, f, g) = UNION (q ` m) XGs"
              by metis
            define q0 where "q0 = XGs o q"
            have "case x of (X, P1, P2, R, ivl, sctn, CX, CXS) \<Rightarrow>
                do_intersection_spec UNIV guards ivl sctn (q0 (X, P1, P2, R, ivl, sctn, CX, CXS)) (P1, CXS \<union> CX) \<and>
                do_intersection_spec UNIV guards ivl sctn (q0 (X, P1, P2, R, ivl, sctn, CX, CXS)) (P2, CXS \<union> CX)"
              if "x \<in> m"
              for x
            proof (clarsimp, goal_cases)
              case (1 X P1 P2 R ivl sctn CX CXS)
              with prems(10)[rule_format, OF \<open>x \<in> m\<close>] prems(15)[rule_format, OF \<open>x \<in> m\<close>] \<open>_ = c\<close>
              have *: "R = {}"
                "x = (X, P1, P2, {}, ivl, sctn, CX, CXS)"
                "ivl \<inter> plane_of sctn \<subseteq> \<Union>l"
                "closed ivl"
                "c \<subseteq> CXS \<times> UNIV"
                "g \<subseteq> CXS"
                "UNION m q \<subseteq> CXS \<times> UNIV"
                "CXS \<inter> (guards \<union> \<Union>l) = {}"
                "p (X, P1, P2, {}, ivl, sctn, CX, CXS) = {}"
                "p (X, P1, P2, R, ivl, sctn, CX, CXS) \<subseteq> CXS \<times> UNIV"
                "do_intersection_spec UNIV guards ivl sctn (q (X, P1, P2, {}, ivl, sctn, CX, CXS)) (P1, CXS \<union> CX)"
                "do_intersection_spec UNIV guards ivl sctn (q (X, P1, P2, {}, ivl, sctn, CX, CXS)) (P2, CXS \<union> CX)"
                by auto
              have "do_intersection_spec UNIV guards ivl sctn (q0 (X, P1, P2, R, ivl, sctn, CX, CXS)) (P1, (CXS \<union> CX) \<union> (CXS \<union> CX))"
                apply (rule do_intersection_flowsto_trans_outside)
                       apply (simp add: q0_def)
                       apply (rule flowsto_subset)
                           apply (rule XGs)
                using \<open>x \<in> m\<close> apply (rule imageI)
                using 1 apply force
                         apply force
                using * apply force
                       apply (rule order_refl)
                using * apply (auto intro!: *)[]
                subgoal
                  using * \<open>x \<in> m\<close>
                  by (auto simp add: )
                subgoal using * by (auto simp: do_intersection_spec_def)
                subgoal using * by (auto simp: do_intersection_spec_def)
                subgoal
                proof -
                  have "q0 (X, P1, P2, R, ivl, sctn, CX, CXS) \<subseteq> XGs (q x)"
                    by (auto simp: q0_def 1)
                  also have "\<dots> \<subseteq> R0 (a, b, b', c, d, e, f, g)" using \<open>x \<in>m\<close> XGs by auto
                  also have "\<dots> \<subseteq> (CXS \<union> CX) \<times> UNIV"
                    using prems(20) \<open>g \<subseteq> CXS\<close> by auto
                  finally show ?thesis by simp
                qed
                subgoal by fact
                subgoal using * by (auto simp: do_intersection_spec_def)
                done
              moreover have "do_intersection_spec UNIV guards ivl sctn (q0 (X, P1, P2, R, ivl, sctn, CX, CXS)) (P2, (CXS \<union> CX) \<union> (CXS \<union> CX))"
                apply (rule do_intersection_flowsto_trans_outside)
                       apply (simp add: q0_def)
                       apply (rule flowsto_subset)
                           apply (rule XGs)
                using \<open>x \<in> m\<close> apply (rule imageI)
                using 1 apply force
                         apply force
                using * apply force
                       apply (rule order_refl)
                using * apply (auto intro!: *)[]
                subgoal
                  using * \<open>x \<in> m\<close>
                  by (auto simp add: )
                subgoal using * by (auto simp: do_intersection_spec_def)
                subgoal using * by (auto simp: do_intersection_spec_def)
                subgoal
                proof -
                  have "q0 (X, P1, P2, R, ivl, sctn, CX, CXS) \<subseteq> XGs (q x)"
                    by (auto simp: q0_def 1)
                  also have "\<dots> \<subseteq> R0 (a, b, b', c, d, e, f, g)" using \<open>x \<in>m\<close> XGs by auto
                  also have "\<dots> \<subseteq> (CXS \<union> CX) \<times> UNIV"
                    using prems(20) \<open>g \<subseteq> CXS\<close> by auto
                  finally show ?thesis by simp
                qed
                subgoal by fact
                subgoal using * by (auto simp: do_intersection_spec_def)
                done
              ultimately show ?case
                by (simp add: )
            qed note q0 = this
            have q0': "(a, aa, aa', ab, ac, ad, ae, b) \<in> m \<Longrightarrow> XS0 \<subseteq> b \<times> UNIV" for a aa aa' ab ac ad ae b
              apply (drule prems(15)[rule_format])
              using \<open>XS0 \<subseteq> g \<times> UNIV\<close>
              by auto
            from prems
            show ?thesis
              apply (intro exI[where x="\<lambda>x. if x \<in> i \<inter> m then j x \<union> q0 x else if x \<in> i then j x else q0 x"] conjI)
              subgoal 1 premises prems
                unfolding XGs
                apply simp
                by (auto simp: q0_def)
              subgoal premises _
                by (rule order_trans[OF \<open>(\<Union>x\<in>h. R0 x) \<subseteq> (\<Union>x\<in>i. j x)\<close>]) auto
              subgoal premises _ using prems(6)[rule_format] q0
                apply auto
                subgoal by (auto dest!: prems(6)[rule_format] q0 intro!: do_intersection_spec_union2)
                subgoal by (auto dest!: prems(6)[rule_format] q0 intro!: do_intersection_spec_union2)
                subgoal by (auto intro!: do_intersection_spec_union2)
                subgoal by (auto dest!: prems(6)[rule_format] q0' intro!: do_intersection_spec_union2)
                subgoal by (auto dest!: prems(6)[rule_format] q0 intro!: do_intersection_spec_union2)
                subgoal by (auto dest!: prems(6)[rule_format] q0 intro!: do_intersection_spec_union2)
                subgoal by (auto dest!: prems(6)[rule_format] q0 intro!: do_intersection_spec_union2)
                subgoal by (auto dest!: prems(6)[rule_format] q0 intro!: do_intersection_spec_union2)
                done
              done
          qed
          done
        done
      done
    done
  done

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

definition "width_spec_ivl M x = do {
    (i, s) \<leftarrow> ivl_rep x;
    RETURN (\<Sum>(i, s)\<leftarrow>zip (take M (list_of_eucl i)) (take M (list_of_eucl s)). abs (s - i))
  }"
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
lemma width_spec_ivl[THEN order_trans, refine_vcg]: "width_spec_ivl M X \<le> SPEC (\<lambda>x. True)"
  unfolding width_spec_ivl_def
  by (refine_vcg)

definition partition_ivl::"'b reach_options \<Rightarrow> 'a::executable_euclidean_space set \<Rightarrow> 'a::executable_euclidean_space set nres"
  where
 "partition_ivl roptns xs = (if op_coll_is_empty xs then RETURN (op_empty_coll:::clw_rel lvivl_rel) else do {
    (i, s) \<leftarrow> ivl_rep_of_set_coll (sets_of_ivls (xs:::clw_rel lvivl_rel):::clw_rel appr_rel);
    ASSERT (i \<le> s);
    let r = (op_atLeastAtMost_ivl i s);
    (rs, ps) \<leftarrow>
      WHILE\<^bsup>(\<lambda>(rs, ps). (xs) \<subseteq> rs \<union> ps)\<^esup> (\<lambda>(rs, ps). \<not> op_coll_is_empty (rs:::clw_rel lvivl_rel))
      (\<lambda>(rs, ps).
      do {
        (r, rs') \<leftarrow> (split_spec_exact rs:::\<langle>lvivl_rel \<times>\<^sub>r clw_rel lvivl_rel\<rangle>nres_rel);
        (ri, rs) \<leftarrow> ivl_rep r;
        CHECKs (ST ''partition_ivl with strange ivl'') (ri \<le> rs);
        width \<leftarrow> under_post_inter_granularity_spec roptns ({ri .. rs}:::appr_rel);
        if width then
          RETURN (rs', mk_coll r \<union> ps)
        else do {
          (a, b) \<leftarrow> split_spec_ivl D r;
          let isa = (op_inter_ivl_coll (xs:::clw_rel lvivl_rel) (a:::lvivl_rel));
          let isb = (op_inter_ivl_coll(xs:::clw_rel lvivl_rel) (b:::lvivl_rel));
          ra' \<leftarrow> (if op_coll_is_empty isa then RETURN op_empty_coll else do {
            (i', s') \<leftarrow> ivl_rep_of_set_coll (sets_of_ivls isa);
            RETURN (mk_coll (({i' .. s'}:::lvivl_rel) \<inter> a))
          });
          rb' \<leftarrow> (if op_coll_is_empty isb then RETURN op_empty_coll else do {
            (i', s') \<leftarrow> ivl_rep_of_set_coll (sets_of_ivls isb);
            RETURN (mk_coll (({i' .. s'}:::lvivl_rel) \<inter> b))
          });
          RETURN (ra' \<union> rb' \<union> rs', ps)
        }
      }) (mk_coll r:::clw_rel lvivl_rel, op_empty_coll :::clw_rel lvivl_rel);
    RETURN ps
  })"
sublocale autoref_op_pat_def partition_ivl .

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

lemma partition_ivl_spec[le, refine_vcg]:
  shows "partition_ivl cg XS \<le> SPEC (\<lambda>YS. XS \<subseteq> YS)"
  unfolding partition_ivl_def autoref_tag_defs
  apply (refine_vcg, clarsimp_all)
  subgoal by fastforce
  subgoal by fastforce
  subgoal by fastforce
  subgoal by fastforce
  subgoal premises prems for a b c d e f g h i j k l m n 
  proof -
    have disj: "\<And>A Aa. n \<notin> A \<or> \<not> XS \<inter> A \<subseteq> Aa \<or> n \<in> Aa"
      using prems by blast
    then have "n \<in> g"
      using prems by (metis (no_types) Un_iff atLeastAtMost_iff subset_iff)
    then show ?thesis
      using disj prems by (meson atLeastAtMost_iff)
  qed
  done

abbreviation "elvivl_rel \<equiv> \<langle>lvivl_rel\<rangle>scaleR2_rel"

definition "op_inter_fst_ivl_scaleR2 X Y = do {
    ((l, u), X) \<leftarrow> scaleR2_rep X;
    (i, s) \<leftarrow> ivl_rep (op_inter_fst X Y);
    let R = op_inter_fst (op_atLeastAtMost_ivl i s) Y;
    scaleRe_ivl_coll_spec l u (filter_empty_ivls (mk_coll R))
  }"
sublocale autoref_op_pat_def op_inter_fst_ivl_scaleR2 .
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

lemma op_inter_fst_ivl_scaleR2[le,refine_vcg]:
  "op_inter_fst_ivl_scaleR2 X Y \<le> SPEC (\<lambda>R. X \<inter> (Y \<times> UNIV) = R)"
  unfolding op_inter_fst_ivl_scaleR2_def
  apply refine_vcg
  apply (auto simp: scaleR2_def)
  subgoal for a b c d e f g h i j k
    by (rule image_eqI[where x="(i, (j, k))"]; fastforce)
  subgoal for a b c d e f g h i j k
    by (rule image_eqI[where x="(i, (j, k))"]; fastforce)
  done


definition "op_inter_fst_ivl_coll_scaleR2 X Y = do {
    Xs \<leftarrow> sets_of_coll X;
    FORWEAK Xs (RETURN op_empty_coll) (\<lambda>X. op_inter_fst_ivl_scaleR2 X Y) (\<lambda>X X'. RETURN (X' \<union> X))
  }"
sublocale autoref_op_pat_def op_inter_fst_ivl_coll_scaleR2 .
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

lemma op_inter_fst_ivl_coll_scaleR2[le,refine_vcg]:
  "op_inter_fst_ivl_coll_scaleR2 X Y \<le> SPEC (\<lambda>R. X \<inter> (Y \<times> UNIV) = R)"
  unfolding op_inter_fst_ivl_coll_scaleR2_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs R. (\<Union>Xs) \<inter> (Y \<times> UNIV) \<subseteq> R \<and> R \<subseteq> X \<inter> (Y \<times> UNIV)"])
    auto

definition "op_inter_ivl_coll_scaleR2 X Y = do {
    eivls \<leftarrow> op_inter_fst_ivl_coll_scaleR2 X Y;
    ((l, u), ivls) \<leftarrow> scaleR2_rep_coll eivls;
    (i, s) \<leftarrow> ivl_rep_of_set_coll (sets_of_ivls ivls);
    let R = op_inter_fst (op_atLeastAtMost_ivl i s) Y;
    scaleRe_ivl_coll_spec l u (filter_empty_ivls (mk_coll R))
  }"
sublocale autoref_op_pat_def op_inter_ivl_coll_scaleR2 .
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

lemma op_inter_ivl_coll_scaleR2[le,refine_vcg]:
  "op_inter_ivl_coll_scaleR2 X Y \<le> SPEC (\<lambda>R. X \<inter> (Y \<times> UNIV) \<subseteq> R)"
  unfolding op_inter_ivl_coll_scaleR2_def
  apply refine_vcg
  apply (auto simp: scaleR2_def image_def vimage_def)
  apply (drule set_mp)
   apply (rule IntI, assumption, force)
  apply auto apply force
  done

definition [refine_vcg_def]: "op_image_fst_ivl X = SPEC (\<lambda>R. R = fst ` X)"
sublocale autoref_op_pat_def op_image_fst_ivl .

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
     apply (rule lv_relI[where c=a])
      apply (simp add: lv_rel_def br_def)
    apply (drule fun_relD)
     apply (rule lv_relI[where c=b])
      apply (simp add: lv_rel_def br_def)
    apply (auto simp: set_of_ivl_def lv_rel_def br_def fst_imageIcc eucl_of_list_prod)
    done
  subgoal by simp
  done

definition "op_image_fst_ivl_coll X = do {
  Xs \<leftarrow> sets_of_coll X;
  FORWEAK Xs (RETURN op_empty_coll) (\<lambda>X. do {i \<leftarrow> op_image_fst_ivl X; RETURN (mk_coll i)}) (\<lambda>X' X. RETURN (X' \<union> X))
  }"
sublocale autoref_op_pat_def op_image_fst_ivl_coll .

lemma [le, refine_vcg]: "op_image_fst_ivl_coll X \<le> SPEC (\<lambda>R. R = fst ` X)"
  unfolding op_image_fst_ivl_coll_def
  apply (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs R. fst ` (\<Union>Xs) \<subseteq> R \<and> R \<subseteq> fst ` X"])
     apply auto
  apply force+
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

definition "op_single_inter_ivl a fxs = do {
  let isa = (op_inter_ivl_coll (fxs:::clw_rel lvivl_rel) (a:::lvivl_rel));
  (if op_coll_is_empty isa then RETURN op_empty_coll else do {
    (i', s') \<leftarrow> ivl_rep_of_set_coll (sets_of_ivls isa);
    RETURN (mk_coll (({i' .. s'}:::lvivl_rel) \<inter> a))
  })
}"
sublocale autoref_op_pat_def op_single_inter_ivl .
lemma op_single_inter_ivl[le, refine_vcg]: "op_single_inter_ivl a fxs \<le> SPEC (\<lambda>R. a \<inter> fxs \<subseteq> R)"
  unfolding op_single_inter_ivl_def
  by refine_vcg auto
schematic_goal op_single_inter_ivl_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) D"
  assumes [autoref_rules]: "(FXSi, FXS) \<in> clw_rel lvivl_rel" "(Ai, A::'n::enum rvec set) \<in> lvivl_rel"
  shows "(nres_of ?r, op_single_inter_ivl A FXS) \<in> \<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding op_single_inter_ivl_def
  by (autoref_monadic)
concrete_definition op_single_inter_ivl_impl for Ai FXSi uses op_single_inter_ivl_impl
lemma op_single_inter_ivl_impl_refine[autoref_rules]:
  "DIM_precond TYPE((real, 'a::enum) vec) D \<Longrightarrow>
  (\<lambda>Ai FXSi. nres_of (op_single_inter_ivl_impl Ai FXSi), op_single_inter_ivl::'a rvec set \<Rightarrow> _) \<in>
    lvivl_rel \<rightarrow> clw_rel (\<langle>lv_rel\<rangle>ivl_rel) \<rightarrow> \<langle>clw_rel (\<langle>lv_rel\<rangle>ivl_rel)\<rangle>nres_rel"
  using op_single_inter_ivl_impl.refine
  by force

definition partition_ivle::
  "'b reach_options \<Rightarrow> ('n::enum vec1) set \<Rightarrow> _ set nres"
  where
 "partition_ivle roptns xse =
  (if op_coll_is_empty xse then RETURN (op_empty_coll:::clw_rel (elvivl_rel)) else do {
    (_, xs) \<leftarrow> scaleR2_rep_coll xse;
    xsf \<leftarrow> op_image_fst_ivl_coll xs;
    (i, s) \<leftarrow> ivl_rep_of_set_coll (sets_of_ivls (xsf:::clw_rel (lvivl_rel)):::clw_rel appr_rel);
    ASSERT (i \<le> s);
    let r = (op_atLeastAtMost_ivl i s);
    (rs, ps) \<leftarrow>
      WHILE\<^bsup>(\<lambda>(rs, ps). xse \<subseteq> (rs \<times> UNIV) \<union> ps)\<^esup> (\<lambda>(rs, ps). \<not> op_coll_is_empty (rs:::clw_rel lvivl_rel))
      (\<lambda>(rs, ps).
      do {
        (r, rs') \<leftarrow> (split_spec_exact rs:::\<langle>lvivl_rel \<times>\<^sub>r clw_rel lvivl_rel\<rangle>nres_rel);
        (ri, rs) \<leftarrow> ivl_rep r;
        CHECKs (ST ''partition_ivle with strange ivl'') (ri \<le> rs);
        width \<leftarrow> under_post_inter_granularity_spec roptns ({ri .. rs}:::appr_rel);
        if width then do {
          I \<leftarrow> op_inter_ivl_coll_scaleR2 (xse) (r);
          RETURN (rs', I \<union> ps)
        } else do {
          (a, b) \<leftarrow> split_spec_ivl D r;
          fxs \<leftarrow> op_image_fst_ivl_coll xs;
          ra' \<leftarrow> op_single_inter_ivl a fxs;
          rb' \<leftarrow> op_single_inter_ivl b fxs;
          RETURN (ra' \<union> rb' \<union> rs', ps)
        }
      }) (mk_coll r:::clw_rel lvivl_rel, op_empty_coll :::clw_rel elvivl_rel);
    RETURN ps
  })"
sublocale autoref_op_pat_def partition_ivle .

lemma partition_ivle_spec[le, refine_vcg]:
  shows "partition_ivle cg XS \<le> SPEC (\<lambda>YS. XS \<subseteq> YS)"
  unfolding partition_ivle_def autoref_tag_defs
  supply [refine_vcg del] = scaleR2_rep_of_coll2
    and [refine_vcg] = scaleR2_rep_of_coll
  apply (refine_vcg)
  subgoal by (fastforce simp: scaleR2_def)
  subgoal by auto
  apply clarsimp
  subgoal by (fastforce simp: scaleR2_def)
  done

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

definition
  "vec1repse X = do {
    XS \<leftarrow> sets_of_coll X;
    FORWEAK XS (RETURN (Some op_empty_coll))
      (\<lambda>x. do {
        ((l, u), x) \<leftarrow> scaleR2_rep x;
        xo \<leftarrow> vec1rep x;
        case xo of None \<Rightarrow> RETURN None
        | Some x \<Rightarrow> do {
            xe \<leftarrow> scaleRe_ivl_spec l u x;
            RETURN (Some (mk_coll xe))
          }
      })
      (\<lambda>a b.
        case (a, b) of (Some a, Some b) \<Rightarrow> RETURN (Some (b \<union> a))
        | _ \<Rightarrow> RETURN None)
  }"
sublocale autoref_op_pat_def vec1reps .

lemma vec1repse[THEN order_trans, refine_vcg]:
  "vec1repse CX \<le> SPEC (\<lambda>R. case R of None \<Rightarrow> True | Some X \<Rightarrow> X = vec1_of_flow1 ` CX)"
  unfolding vec1repse_def
  apply (refine_vcg FORWEAK_mono_rule[where
        I="\<lambda>XS R. case R of None \<Rightarrow> True | Some R \<Rightarrow> vec1_of_flow1 ` (\<Union>XS) \<subseteq> R \<and> R \<subseteq> vec1_of_flow1 ` CX"])
  apply (auto simp: scaleR2_def split: option.splits)
  subgoal for a b c d e f g h i j
    apply (auto simp: vimage_def image_def)
    apply (rule exI[where x="h"])
    apply auto
    apply (rule exI[where x=f])
    apply (rule exI[where x="matrix j"])
    apply auto
     apply (rule bexI)
    by (auto simp: vec1_of_flow1_def matrix_scaleR)
  subgoal for a b c d e f g h i j
    apply (rule bexI)
     defer apply assumption
    apply (rule image_eqI[where x="(f, g, j)"])
    by (auto simp: flow1_of_vec1_def vec1_of_flow1_def matrix_scaleR[symmetric])
  subgoal by fastforce
  subgoal for a b c d e f g h i j k l
    apply (auto simp: vimage_def image_def)
    apply (rule exI[where x="j"])
    apply auto
    apply (rule exI[where x=h])
    apply (rule exI[where x="matrix l"])
    apply auto
     apply (rule bexI)
    by (auto simp: vec1_of_flow1_def matrix_scaleR)
  subgoal by fastforce
  subgoal for a b c d e f g h i j k l
    apply (rule bexI)
     defer apply assumption
    apply (rule image_eqI[where x="(h, i, l)"])
    by (auto simp: flow1_of_vec1_def vec1_of_flow1_def matrix_scaleR[symmetric])
  done
abbreviation "appre_rel \<equiv> \<langle>appr_rel\<rangle>scaleR2_rel"
schematic_goal vec1repse_impl:
  assumes [autoref_rules]: "(Xi, X) \<in> clw_rel appr1e_rel"
  shows "(nres_of ?r, vec1repse X) \<in> \<langle>\<langle>clw_rel appre_rel\<rangle>option_rel\<rangle>nres_rel"
  unfolding vec1repse_def
  including art
  by (autoref_monadic)
concrete_definition vec1repse_impl for Xi uses vec1repse_impl
lemmas vec1repse_impl_refine[autoref_rules] = vec1repse_impl.refine[autoref_higher_order_rule]

end

sledgehammer_params [fact_filter=mepo]

context approximate_sets_ode_slp' begin

lemma [autoref_rules_raw del]: "(norm2_slp, norm2_slp) \<in> nat_rel \<rightarrow> Id"
  and [autoref_itype del]: "norm2_slp ::\<^sub>i i_nat \<rightarrow>\<^sub>i i_of_rel (Id::(floatarith list \<times> floatarith list) set)"
  by auto

lemma [autoref_rules]: "(norm2_slp, norm2_slp) \<in> nat_rel \<rightarrow> slp_rel"
  by auto

definition "scaleR2_rep1 Y = do {
    ((l, u), X) \<leftarrow> scaleR2_rep Y;
    (i, s) \<leftarrow> ivl_rep_of_set X;
    let mig = inf (abs i) (abs s);
    CHECKs (ST ''scaleR2_rep1: strange'') (i \<le> s);
    (N::real set) \<leftarrow> approx_slp_appr [floatarith.Inverse (norm2\<^sub>e D)] (norm2_slp D) (list_of_eucl ` ({mig .. mig}:::appr_rel));
    (sl, su) \<leftarrow> ivl_rep_of_set (N:::appr_rel);
    let scale = (rnv_of_lv sl + rnv_of_lv su)/2;
    CHECKs (ST ''scaleR2_rep1: scale 0'') (scale > 0);
    CHECKs (ST ''scaleR2_rep1: l 0'') (l > 0);
    CHECKs (ST ''scaleR2_rep1: u 0'') (u > 0);
    let scalel = real_divl (precision optns) 1 scale;
    let scaleu = real_divr (precision optns) 1 scale;
    CHECKs (ST ''scaleR2_rep1: scalel 0'') (scalel > 0);
    CHECKs (ST ''scaleR2_rep1: scaleu 0'') (scaleu > 0);
    (i, s) \<leftarrow> ivl_rep_of_set X;
    let (i0, i1) = split_lv_rel i;
    let (s0, s1) = split_lv_rel s;
    scaleRe_ivl_spec (scalel * l) (scaleu * u)
      (op_atLeastAtMost_ivl (Pair_lv_rel i0 (scale *\<^sub>R i1)) (Pair_lv_rel s0 (scale *\<^sub>R s1)))
  }"
sublocale autoref_op_pat_def scaleR2_rep1 .
lemma [autoref_rules_raw]: "DIM_precond TYPE(real) (Suc 0)"
  by auto
lemma [autoref_rules]: "(ereal, ereal) \<in> rnv_rel \<rightarrow> ereal_rel"
  "(real_divr, real_divr) \<in> nat_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "(( * ), ( * )) \<in> ereal_rel \<rightarrow> ereal_rel \<rightarrow> ereal_rel"
  by auto

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
lemma length_norm2_slp_ge: "length (norm2_slp D) \<ge> 1"
  unfolding norm2_slp_def
  by (auto simp: slp_of_fas_def split: prod.splits)

lemma scaleR2_rep1[le, refine_vcg]: "scaleR2_rep1 Y \<le> SPEC (\<lambda>R. Y \<subseteq> R)"
  unfolding scaleR2_rep1_def
  apply refine_vcg
  subgoal by (auto simp: norm2_slp_def)
  subgoal for a b c d e y z f g h i j k l m n p q r s
    apply (auto simp: scaleR2_def image_def vimage_def)
    subgoal premises prems for B C D E
    proof -
      define ij where "ij = (i + j) / 2"
      from prems
      have "ij > 0"
        by (auto simp: ij_def)
      show ?thesis
        unfolding ij_def[symmetric]
        apply (rule exI[where x="1 / ij * B"])
        apply (intro conjI) prefer 3
          apply (rule bexI[where x="(D, ij *\<^sub>R E)"])
        subgoal using \<open>ij > 0\<close> by auto
        subgoal using \<open>(D, E) \<in> c\<close> \<open>c \<subseteq> {(n, p)..(q, r)}\<close> \<open>ij > 0\<close>
          by (auto simp: ij_def[symmetric] intro!: scaleR_left_mono)
        subgoal
          using \<open>d \<le> ereal B\<close> \<open>0 < ij\<close> \<open>0 < d\<close>
          apply (cases d)
            apply (simp only: times_ereal.simps ereal_less_eq)
            apply (rule mult_mono)
               apply (rule real_divl)
          by auto
        subgoal
          using \<open>0 < d\<close> \<open>d \<le> ereal B\<close> \<open>ereal B \<le> e\<close> \<open>0 < ij\<close> \<open>0 < e\<close>
            \<open>0 < real_divr (precision optns) 1 ((i + j) / 2)\<close>
          unfolding ij_def[symmetric]
          apply (cases e; cases d)
                  apply (simp only: times_ereal.simps ereal_less_eq)
                  apply (rule mult_mono)
                     apply (rule real_divr)
          by auto
        done
    qed
    done
  done

definition "reduce_ivl (X::'n::enum vec1 set) b = do {
    (i, s) \<leftarrow> ivl_rep X;
    CHECKs (''reduce_ivl strange basis'') (b \<in> set Basis_list);
    CHECKs (''reduce_ivl strange ivl'') (i \<le> s);
    let (i0, i1) = split_lv_rel i;
    let (s0, s1) = split_lv_rel s;
    let ivl2 = op_atLeastAtMost_ivl i1 s1;
    P \<leftarrow> project_set_ivl ivl2 b 0;
    (iP, sP) \<leftarrow> ivl_rep P;
    if iP \<le> 0 \<and> 0 \<le> sP then
      if i1 \<bullet> b > 0 then do {
        let s = (i1 \<bullet> b) *\<^sub>R b;
        let P' = op_atLeastAtMost_ivl (Pair_lv_rel i0 (iP + s)) (Pair_lv_rel s0 (sP + s));
        scaleRe_ivl_spec 1 \<infinity> P'
      } else if s1 \<bullet> b < 0 then do {
        let s = (s1 \<bullet> b) *\<^sub>R b;
        let P' = op_atLeastAtMost_ivl (Pair_lv_rel i0 (iP + s)) (Pair_lv_rel s0 (sP + s));
        scaleRe_ivl_spec 1 \<infinity> P'
      } else scaleRe_ivl_spec 1 1 X
    else scaleRe_ivl_spec 1 1 X
  }"
sublocale autoref_op_pat_def reduce_ivl .
lemma [autoref_rules]: "(\<infinity>, \<infinity>) \<in> ereal_rel"
  by auto
schematic_goal reduce_ivl_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE((real, 'n) vec) D"
  assumes [autoref_rules]:
    "(Yi, Y::'n::enum vec1 set) \<in> lvivl_rel"
    "(bi, b::((real, 'n) vec, 'n) vec) \<in> lv_rel"
  shows "(nres_of ?r, reduce_ivl $ Y $ b) \<in> \<langle>elvivl_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding reduce_ivl_def
  including art
  by (autoref_monadic)
concrete_definition reduce_ivl_impl for Yi bi uses reduce_ivl_impl
lemmas [autoref_rules] = reduce_ivl_impl.refine

lemma reduce_ivl[le, refine_vcg]: "reduce_ivl Y b \<le> SPEC (\<lambda>R. Y \<subseteq> R)"
  unfolding reduce_ivl_def
  apply refine_vcg
     apply (auto simp add: scaleR2_def image_def vimage_def plane_of_def )
     prefer 2
  subgoal using basic_trans_rules(23) by blast
    prefer 3
  subgoal using basic_trans_rules(23) by blast
proof goal_cases
  case (1 i0 i1 s0 s1 y0 y1)
  from 1 have le: "1 \<le> (y1 \<bullet> b) / (i1 \<bullet> b)"
    by (auto simp: min_def dest!: inner_Basis_mono[OF _ \<open>b \<in> Basis\<close>])
  show ?case
    apply (rule exI[where x="(y1 \<bullet> b) / (i1 \<bullet> b)"])
    apply (rule conjI) apply fact
    apply (rule bexI[where x="(y0, ((i1 \<bullet> b) / (y1 \<bullet> b)) *\<^sub>R y1)"])
    subgoal using 1 le by simp
    subgoal using 1 le apply simp
      apply (rule conjI)
      subgoal
        apply (auto simp: eucl_le[where 'a="((real, 'a) vec, 'a) vec"])
        apply (auto simp: divide_simps)
        apply (subst mult.commute)
        subgoal for i
          apply (cases " y1 \<bullet> b \<le> i1 \<bullet> b")
           apply (rule order_trans)
            apply (rule mult_left_mono[where b="y1 \<bullet> i"])
             apply (auto simp: mult_le_cancel_right)
          apply (cases "i1 \<bullet> i \<le> 0")
           apply (rule order_trans)
            apply (rule mult_right_mono_neg[where b="i1 \<bullet> b"])
             apply auto
          by (auto simp: not_le inner_Basis split: if_splits dest!: bspec[where x=i])
        done
      subgoal
        apply (auto simp: eucl_le[where 'a="((real, 'a) vec, 'a) vec"])
        subgoal for i
          apply (cases "i = b")
           apply (auto simp: divide_simps)
          subgoal by (auto simp: divide_simps algebra_simps)
          subgoal apply (auto simp: divide_simps algebra_simps inner_Basis)
            apply (subst mult.commute)
            apply (rule order_trans)
             apply (rule mult_right_mono[where b="s1 \<bullet> i"]) apply simp
             apply simp
            apply (rule mult_left_mono)
            by auto
          done
        done
      done
    done
next
  case (2 i0 i1 s0 s1 y0 y1)
  from 2 have le: "1 \<le> (y1 \<bullet> b) / (s1 \<bullet> b)"
    by (auto simp: min_def abs_real_def divide_simps dest!: inner_Basis_mono[OF _ \<open>b \<in> Basis\<close>])
  show ?case
    apply (rule exI[where x="(y1 \<bullet> b) / (s1 \<bullet> b)"])
    apply (rule conjI) apply fact
    apply (rule bexI[where x="(y0, ((s1 \<bullet> b) / (y1 \<bullet> b)) *\<^sub>R y1)"])
    subgoal using 2 le by simp
    subgoal using 2 le apply simp
      apply (rule conjI)
      subgoal
        apply (auto simp: eucl_le[where 'a="((real, 'a) vec, 'a) vec"])
        subgoal for i
          apply (cases "i = b")
           apply (auto simp: divide_simps)
          subgoal by (auto simp: divide_simps algebra_simps)
          subgoal apply (auto simp: divide_simps algebra_simps inner_Basis)
            apply (subst mult.commute)
            apply (cases "y1 \<bullet> i \<le> 0")
             apply (rule order_trans)
              apply (rule mult_left_mono_neg[where b="y1 \<bullet> b"])
               apply (auto simp: mult_le_cancel_right not_le)
            apply (rule order_trans)
             apply (rule mult_right_mono_neg[where b="i1 \<bullet> i"])
              apply (auto intro!: mult_left_mono_neg)
            done
          done
        done
      subgoal
        apply (auto simp: eucl_le[where 'a="((real, 'a) vec, 'a) vec"])
        subgoal for i
          apply (cases "i = b")
          subgoal by (auto simp: divide_simps algebra_simps)
          subgoal apply (auto simp: divide_simps algebra_simps inner_Basis)
            apply (subst mult.commute)
            apply (cases "y1 \<bullet> i \<ge> 0")
             apply (rule order_trans)
              apply (rule mult_left_mono_neg[where b="y1 \<bullet> i"]) apply simp
              apply simp
             apply (rule mult_right_mono) apply force
             apply force
          proof -
            assume a1: "\<forall>i\<in>Basis. s1 \<bullet> b * (if b = i then 1 else 0) \<le> s1 \<bullet> i"
            assume a2: "i \<in> Basis"
            assume a3: "i \<noteq> b"
            assume a4: "y1 \<bullet> b < 0"
            assume a5: "s1 \<bullet> b < 0"
            assume a6: "\<not> 0 \<le> y1 \<bullet> i"
            have "s1 \<bullet> b * (if b = i then 1 else 0) \<le> s1 \<bullet> i"
              using a2 a1 by metis
            then have f7: "0 \<le> s1 \<bullet> i"
              using a3 by (metis (full_types) mult_zero_right)
            have f8: "y1 \<bullet> b \<le> 0"
              using a4 by (metis eucl_less_le_not_le)
            have "s1 \<bullet> b \<le> 0"
              using a5 by (metis eucl_less_le_not_le)
            then show "y1 \<bullet> b * (s1 \<bullet> i) \<le> s1 \<bullet> b * (y1 \<bullet> i)"
              using f8 f7 a6 by (metis mult_right_mono_le mult_zero_left zero_le_mult_iff zero_le_square)
          qed
          done
        done
      done
    done
qed

definition "reduce_ivle Y b = do {
    ((l, u), X) \<leftarrow> scaleR2_rep Y;
    R \<leftarrow> reduce_ivl X b;
    ((l', u'), R) \<leftarrow> scaleR2_rep R;
    CHECKs (''reduce_ivle: wtf?'') (0 < l' \<and> 0 < l \<and> 0 \<le> u \<and> l \<le> u \<and> l' \<le> u');
    scaleRe_ivl_spec (l'*l) (u' * u) R
  }"
sublocale autoref_op_pat_def reduce_ivle .

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
  by (autoref_monadic)
concrete_definition reduce_ivle_impl for Yi bi uses reduce_ivle_impl
lemmas [autoref_rules] = reduce_ivle_impl.refine

lemma reduce_ivle[le, refine_vcg]:
  "reduce_ivle Y b \<le> SPEC (\<lambda>R. Y \<subseteq> R)"
  unfolding reduce_ivle_def
  apply refine_vcg
  apply (auto simp: scaleR2_def image_def vimage_def)
  subgoal for a b c d e f g h i j k
    apply (drule set_mp, assumption)
    apply auto
    subgoal for l m
    apply (rule exI[where x="l * g"])
      apply (intro conjI)
    subgoal
      unfolding times_ereal.simps[symmetric]
      apply (rule ereal_mult_mono)
      subgoal by (cases e) auto
      subgoal by (cases b) auto
      subgoal by (cases b) auto
      subgoal by (cases e) auto
      done
    subgoal
      unfolding times_ereal.simps[symmetric]
      apply (rule ereal_mult_mono)
      subgoal by (cases b) auto
      subgoal by (cases b) auto
      subgoal by (cases b) auto
      subgoal by (cases e) auto
      done
    subgoal by force
    done
  done
  done

definition "reduces_ivle (X::'n::enum vec1 set) =
  FOREACH\<^bsup>\<lambda>B R. X \<subseteq> R\<^esup> (set Basis_list:::\<langle>lv_rel\<rangle>list_set_rel) (\<lambda>b X. reduce_ivle X b) X"
sublocale autoref_op_pat_def reduces_ivle .

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
lemma reduces_ivle[le, refine_vcg]:
  "reduces_ivle X \<le> SPEC (\<lambda>R. X \<subseteq> R)"
  unfolding reduces_ivle_def
  by refine_vcg auto

definition "ivlse_of_setse X = do {
  Xs \<leftarrow> sets_of_coll X;
  FORWEAK Xs (RETURN op_empty_coll) (\<lambda>X. do {
    I \<leftarrow> scaleR2_rep1 X;
    I \<leftarrow> reduces_ivle I;
    RETURN (mk_coll I)
  }) (\<lambda>X' X. RETURN (X' \<union> X))
  }"
sublocale autoref_op_pat_def ivlse_of_setse .
lemma ivlse_of_setse[le, refine_vcg]: "ivlse_of_setse X \<le> SPEC (\<lambda>R. X \<subseteq> R)"
  unfolding ivlse_of_setse_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs R. \<Union>Xs \<subseteq> R"])
    (auto simp: scaleR2_def image_def vimage_def)
schematic_goal ivlse_of_setse_impl:
  "(nres_of ?r, ivlse_of_setse $ X) \<in> \<langle>clw_rel elvivl_rel\<rangle>nres_rel"
  if [autoref_rules]: "(Xi, X::'n vec1 set) \<in> clw_rel (appre_rel)"
  and  [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) D"
  unfolding ivlse_of_setse_def
  including art
  by autoref_monadic
concrete_definition ivlse_of_setse_impl uses ivlse_of_setse_impl
lemmas [autoref_rules] = ivlse_of_setse_impl.refine

lemma lift_scaleR2:
  "(\<lambda>(lu, x). (lu, fi x), f) \<in> \<langle>A\<rangle>scaleR2_rel \<rightarrow> \<langle>B\<rangle>scaleR2_rel"
  if "(fi, f) \<in> A \<rightarrow> B"
  "\<And>l u x. x \<in> Range A \<Longrightarrow> ereal -` {l..u} \<noteq> {} \<Longrightarrow> scaleR2 l u (f x) = f (scaleR2 l u x)"
  using that
  apply (auto simp: scaleR2_rel_def )
  apply (rule relcompI)
   apply (rule prod_relI)
    apply (rule IdI)
   apply (drule fun_relD, assumption, assumption)
    apply (auto simp: br_def vimage_def)
  done

definition "setse_of_ivlse (X:: ('a::executable_euclidean_space \<times> 'c::executable_euclidean_space) set) = do {
  Xs \<leftarrow> sets_of_coll X;
  FORWEAK Xs (RETURN op_empty_coll) (\<lambda>X. do {
    ((l, u), x) \<leftarrow> scaleR2_rep X;
    (i, s) \<leftarrow> ivl_rep x;
    if i \<le> s then do {
      x \<leftarrow> scaleRe_ivl_spec l u {i .. s};
      RETURN (mk_coll x)
    } else RETURN op_empty_coll
  }) (\<lambda>X' X. RETURN (X' \<union> X))
}"
sublocale autoref_op_pat_def setse_of_ivlse .

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
lemma scaleR2_eq_empty_iff:
  "scaleR2 l u X = {} \<longleftrightarrow> X = {} \<or> ereal -` {l..u} = {}"
  by (auto simp: scaleR2_def)

lemma setse_of_ivlse[le, refine_vcg]:
  "setse_of_ivlse X \<le> SPEC (\<lambda>R. R = X)"
  unfolding setse_of_ivlse_def
  apply (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs R. \<Union>Xs \<subseteq> R \<and> R \<subseteq> X"])
       apply clarsimp_all
  subgoal by (rule bexI)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

definition [simp]: "op_image_flow1_of_vec1_colle \<equiv> op_image_flow1_of_vec1_coll"
sublocale autoref_op_pat_def op_image_flow1_of_vec1_colle .

lemma blinfun_of_vmatrix_scaleR: "blinfun_of_vmatrix (c *\<^sub>R e) = c *\<^sub>R blinfun_of_vmatrix e"
  including blinfun.lifting
  by transfer (vector sum_distrib_left algebra_simps matrix_vector_mult_def fun_eq_iff)

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

definition partition_set::"'b reach_options \<Rightarrow> 'n::enum eucl1 set \<Rightarrow> 'n eucl1 set nres"
  where
    "partition_set ro xs =
    (if op_coll_is_empty xs then RETURN (op_empty_coll:::clw_rel appr1e_rel) else do {
    ASSERT (xs \<noteq> {});
    xs \<leftarrow> split_under_threshold ro (pre_collect_granularity ro)
            (xs:::clw_rel appr1e_rel);
    vxs \<leftarrow> vec1repse xs;
    case vxs of None \<Rightarrow> do {
      xs \<leftarrow> ivls_of_sets (op_image_fst_colle xs);
      ps \<leftarrow> partition_ivl ro xs;
      scaleRe_ivl_coll_spec 1 1 (sets_of_ivls ps \<times> UNIV:::clw_rel appr1_rel)
    }
    | Some xs \<Rightarrow> do {
      xs \<leftarrow> ivlse_of_setse xs;
      ps \<leftarrow> partition_ivle ro xs;
      ps \<leftarrow> setse_of_ivlse ps;
      RETURN (op_image_flow1_of_vec1_colle ps)
    }
  })"
sublocale autoref_op_pat_def partition_set .

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

lemma partition_set_spec[le, refine_vcg]:
  shows "partition_set ro XS \<le> SPEC (\<lambda>YS. XS \<subseteq> YS)"
  unfolding partition_set_def autoref_tag_defs
  apply (refine_vcg)
  subgoal by (fastforce simp: scaleR2_def vimage_def image_def)
  subgoal by fastforce
  done

definition partition_sets::"'b reach_options \<Rightarrow>
  (bool \<times> 'a::enum eucl1 set \<times> 'a::enum eucl1 set \<times> 'a::enum eucl1 set \<times> 'a::enum eucl1 set \<times> 'a rvec set \<times> 'a rvec sctn \<times> 'a rvec set \<times> 'a rvec set) set \<Rightarrow>
  'a eucl1 set nres"
  where
 "partition_sets ro xs =
    FORWEAK xs (RETURN op_empty_coll) (\<lambda>(b, X, PS1, PS2, R, ivl', sctn', CX, CXS). do {
      PS \<leftarrow> partition_set ro PS1;
      RETURN PS
    })
    (\<lambda>a b. RETURN (b \<union> a))"
sublocale autoref_op_pat_def partition_sets .

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

lemma partition_sets_spec[le, refine_vcg]:
  shows "partition_sets ro XS \<le> SPEC (\<lambda>YS. (\<Union>(_, _, PS, _, _, _, _, _) \<in> XS. PS) \<subseteq> YS)"
  unfolding partition_sets_def autoref_tag_defs
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>X Y. (\<Union>(_, _, PS, _, _, _, _, _) \<in> X. PS) \<subseteq> Y"]) auto

definition "ivlsctn_to_set xs = (\<Union>(ivl, sctn)\<in>set xs. ivl \<inter> plane_of sctn)"

definition [refine_vcg_def]: "singleton_spec X = SPEC (\<lambda>x. X = {x})"
sublocale autoref_op_pat_def singleton_spec .
lemma [autoref_rules]:
  assumes "PREFER single_valued A"
  shows "(\<lambda>xs. case xs of [x] \<Rightarrow> RETURN x | _ \<Rightarrow> SUCCEED, singleton_spec) \<in> \<langle>A\<rangle>list_wset_rel \<rightarrow> \<langle>A\<rangle>nres_rel"
  using assms
  by (auto simp: nres_rel_def singleton_spec_def list_wset_rel_def set_rel_br
      split: list.splits elim!: single_valued_as_brE dest!: brD
      intro!: RETURN_SPEC_refine brI)

primrec poincare_onto_series where
  "poincare_onto_series interrupt trap [] XS0 ivl sctn ro = do {
    let guard0 = mk_coll (mk_inter ivl (plane_of sctn));
    ASSUME (closed guard0);
    XS1 \<leftarrow> (poincare_onto2 (ro:::reach_optns_rel)
       (interrupt:::appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel) trap
        (op_empty_coll:::clw_rel (iplane_rel lvivl_rel)) guard0 XS0:::
      \<langle>\<langle>bool_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel \<times>\<^sub>r
      clw_rel (isbelows_rel sappr_rel) \<times>\<^sub>r clw_rel sappr_rel\<rangle>list_wset_rel\<rangle>nres_rel);
    (b, X, PS1, PS2, R, ivl', sctn', CX, CXS) \<leftarrow> singleton_spec XS1;
    CHECKs ''poincare_onto_series: last return!'' (ivl' = ivl \<and> sctn' = sctn);
    RETURN PS2
  }"
| "poincare_onto_series interrupt trap ((guardro)#guards) XS0 ivl sctn ro0 = (case guardro of (guard, ro) \<Rightarrow>
    do {
      ASSUME (closed ivl);
      let guard0 = mk_coll (mk_inter ivl (plane_of sctn));
      ASSUME (closed guard0);
      ASSUME (\<forall>(guard, ro) \<in> set (guardro#guards). closed guard);
      let guardset = (\<Union>(guard, ro)\<in>set ((guard0, ro0)#guards). guard);
      XS1 \<leftarrow> (poincare_onto2 ro (interrupt:::appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel) trap (guardset:::clw_rel (iplane_rel lvivl_rel)) guard XS0 :::
        \<langle>\<langle>bool_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel \<times>\<^sub>r
      clw_rel (isbelows_rel sappr_rel) \<times>\<^sub>r clw_rel sappr_rel\<rangle>list_wset_rel\<rangle>nres_rel);
      ASSUME (\<forall>(b, X, PS1, PS1, R, ivl, sctn, CX, CXS) \<in> XS1. closed ivl);
      XS2 \<leftarrow> partition_sets ro XS1;
      _ \<leftarrow> fst_safe_colle XS2;
      XS3 \<leftarrow> poincare_onto_series interrupt trap guards XS2 ivl sctn (ro0:::reach_optns_rel);
      RETURN XS3
    })"
sublocale autoref_op_pat_def poincare_onto_series .

lemma plane_rel_br: "\<langle>br a I\<rangle>plane_rel = br (plane_of o map_sctn a) (\<lambda>x. I (normal x))"
  apply (auto simp: plane_rel_def sctn_rel_def br_def)
  subgoal for x y z by (cases x; cases y) auto
  subgoal for x y z by (cases x; cases y) auto
  subgoal for x y by (cases x; cases y) auto
  subgoal for a by (cases a; force)
  done

lemma closed_clw_rel_iplane_rel:
  "(xi, x) \<in> clw_rel (iplane_rel lvivl_rel) \<Longrightarrow> closed x"
  unfolding lvivl_rel_br
  by (force simp: lv_rel_def plane_rel_br inter_rel_br clw_rel_br set_of_ivl_def
      dest!: brD)

lemma closed_ivl_prod3_list_rel:
  assumes "(y, x') \<in> clw_rel (iplane_rel lvivl_rel) \<times>\<^sub>r A"
  assumes "(xa, x'a) \<in> \<langle>clw_rel (iplane_rel lvivl_rel) \<times>\<^sub>r B\<rangle>list_rel"
  shows "\<forall>(guard, ro)\<in>set (x' # x'a). closed guard"
  using assms closed_clw_rel_iplane_rel
  apply (auto simp: list_rel_def prod_rel_def in_set_conv_nth list_all2_conv_all_nth)
  apply (drule spec)
  by auto

lemma closed_ivl_prod8_list_rel:
  assumes "(xl, x'l)
       \<in> \<langle>bool_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          \<langle>lv_rel\<rangle>ivl_rel \<times>\<^sub>r
          \<langle>lv_rel\<rangle>sctn_rel \<times>\<^sub>r clw_rel (\<langle>sappr_rel, \<langle>lv_rel\<rangle>sbelows_rel\<rangle>Refine_Rigorous_Numerics.inter_rel) \<times>\<^sub>r clw_rel sappr_rel\<rangle>list_wset_rel"
  shows "(\<forall>(b, X, PS1, PS2, R, ivl, sctn, CX, CXS)\<in>x'l. closed ivl)"
  using assms
  unfolding list_wset_rel_def set_rel_sv[OF single_valued_Id_arbitrary_interface]
  apply (subst (asm) set_rel_sv)
  subgoal
    by (auto simp: Id_arbitrary_interface_def intro!: relator_props intro: single_valuedI)
  by (auto simp: Id_arbitrary_interface_def)

lemma
  rec_list_fun_eq1:
  assumes "\<And>x xs a. snd (h x xs a) = snd a"
  shows "rec_list z (\<lambda>x xs r xa. f x xs xa (r (h x xs xa))) xs ab =
    rec_list (\<lambda>a. z (a, snd ab)) (\<lambda>x xs r a. f x xs (a, snd ab) (r (fst (h x xs (a, snd ab))))) xs (fst ab)"
  using assms
  unfolding split_beta'
  by (induction xs arbitrary: ab) (auto simp: split_beta')

lemma
  rec_list_fun_eq2:
  assumes "\<And>x xs a. fst (h x xs a) = fst a"
  shows "rec_list z (\<lambda>x xs r xa. f x xs xa (r (h x xs xa))) xs ab =
    rec_list (\<lambda>b. z (fst ab, b)) (\<lambda>x xs r b. f x xs (fst ab, b) (r (snd (h x xs (fst ab, b))))) xs (snd ab)"
  using assms
  unfolding split_beta'
  by (induction xs arbitrary: ab) (auto simp: split_beta')

lemma
  poincare_onto_series_rec_list_eq:\<comment> \<open>TODO: here is a problem if interrupt gets uncurried, too\<close>
  "poincare_onto_series interrupt trap guards XS ivl sctn ro = rec_list
      (\<lambda>(((((trap), XS0), ivl), sctn), ro).
          let guard0 = mk_coll (mk_inter ivl (plane_of sctn))
          in ASSUME (closed guard0) \<bind>
             (\<lambda>_. (poincare_onto2 (ro ::: reach_optns_rel) (interrupt:::appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel) trap
                    (op_empty_coll ::: clw_rel (\<langle>\<langle>lv_rel\<rangle>ivl_rel, \<langle>lv_rel\<rangle>plane_rel\<rangle>Refine_Rigorous_Numerics.inter_rel)) guard0 XS0 :::
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
                           in (poincare_onto2 ro (interrupt:::appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel) trap (guardset ::: clw_rel (\<langle>\<langle>lv_rel\<rangle>ivl_rel, \<langle>lv_rel\<rangle>plane_rel\<rangle>Refine_Rigorous_Numerics.inter_rel))
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

lemma closed_subset_plane[intro]:
  "closed b \<Longrightarrow> closed {x \<in> b. x \<in> plane_of c}"
  "closed b \<Longrightarrow> closed {x \<in> b. x \<bullet> n = d}"
  by (auto simp: plane_of_def intro!: closed_levelset_within continuous_intros)

lemma poincare_mapsto_UnionI:
  assumes pm[unfolded poincare_mapsto_def, rule_format]: "\<And>i. i \<in> I \<Longrightarrow> poincare_mapsto p (X0 i) S (CX i) (X1 i)"
  assumes R: "\<And>i x. i \<in> I \<Longrightarrow> x \<in> X1 i \<Longrightarrow> x \<in> R"
  shows "poincare_mapsto p (\<Union>x\<in>I. X0 x) S ((\<Union>x\<in>I. CX x)) R"
  unfolding poincare_mapsto_def
proof (safe del: conjI, goal_cases)
  case (1 x0 d0 i)
  moreover
  have "fst ` UNION I X0 \<subseteq> S"
    proof (safe, goal_cases)
      case (1 _ x0 d0 i)
      from this pm[OF 1]
      show ?case by auto
    qed
  ultimately show ?case using pm[OF 1]
    by (auto intro!: R)
qed

lemma
  do_intersection_poincare_mapstos_trans:
  assumes pm: "\<And>i. i \<in> I \<Longrightarrow> poincare_mapsto (p i) (X0 i) UNIV (CX i) (X1 i)"
  assumes di: "do_intersection_spec UNIV guards ivl sctn (\<Union>i\<in>I. X1 i) (P, CP)"
  assumes "\<And>i. i \<in> I \<Longrightarrow> fst ` (X1 i) \<subseteq> CP"
  assumes "\<And>i. i \<in> I \<Longrightarrow> {x \<in> ivl. x \<in> plane_of sctn} \<inter> CX i = {}"
  assumes "\<And>i. i \<in> I \<Longrightarrow> guards \<inter> (CX i \<union> CP) = {}"
  assumes "\<And>i. i \<in> I \<Longrightarrow> X0 i \<subseteq> CX i \<times> UNIV"
  assumes "\<And>i. i \<in> I \<Longrightarrow> closed (p i)"
  assumes "closed ivl"
  assumes "\<And>i. i \<in> I \<Longrightarrow> CX i \<subseteq> Csafe"
  shows "do_intersection_spec UNIV guards ivl sctn (\<Union>i\<in>I. X0 i) (P, (\<Union>i\<in>I. CX i) \<union> CP)"
  apply (auto simp: do_intersection_spec_def)
  subgoal
    apply (simp del: UN_simps add: UN_extend_simps)
    apply (rule impI)
    apply (thin_tac "I \<noteq> {}")
    subgoal
    proof -
      from di have pmi: "poincare_mapsto {x \<in> ivl. x \<in> plane_of sctn} (X1 i) UNIV CP P" if "i \<in> I" for i
        by (auto simp: do_intersection_spec_def intro: poincare_mapsto_subset that)
      show ?thesis
        apply (rule poincare_mapsto_UnionI)
         apply (rule poincare_mapsto_trans[OF pm pmi])
               apply clarsimp_all
        subgoal s1 using assms by (auto simp: do_intersection_spec_def)
        subgoal using assms apply (auto simp: do_intersection_spec_def)
           apply blast
          by (metis (mono_tags, lifting) s1 mem_Collect_eq mem_simps(2) mem_simps(4))
        subgoal using assms by auto
        subgoal using assms by auto
        subgoal premises prems for i x d
        proof -
          note prems
          have [intro, simp]: "closed {x \<in> ivl. x \<in> plane_of sctn} " "closed {x \<in> ivl. x \<bullet> normal sctn = pstn sctn}"
            by (auto intro!: closed_levelset_within continuous_intros simp: plane_of_def assms)
          have set_eq: "(CX i \<union> CP) \<times> UNIV = (fst ` X1 i \<times> UNIV \<union> CX i \<times> UNIV \<union> CP \<times> UNIV)"
            using assms prems
            by auto
          have empty_inter: "{x \<in> ivl. x \<bullet> normal sctn - pstn sctn = 0} \<times> UNIV \<inter> (CX i \<union> CP) \<times> UNIV = {}"
            apply safe
            subgoal
              using assms(4)[of i] \<open>i \<in> I\<close>
              by (auto simp: plane_of_def )
            subgoal
              using assms(4)[of i]
              using prems assms by (auto simp: plane_of_def do_intersection_spec_def)
            done
          have ft: "flowsto (X0 i) {0<..} ((CX i \<union> CP) \<times> UNIV) (fst ` P \<times> UNIV)"
            unfolding set_eq
            apply (rule flowsto_poincare_mapsto_trans_flowsto[OF poincare_mapsto_imp_flowsto[OF pm[OF \<open>i \<in> I\<close>]]
                  pmi[OF \<open>i \<in> I\<close>] _ _ order_refl])
            using assms prems by (auto)
          then have ret: "returns_to {x \<in> ivl. x \<bullet> normal sctn - pstn sctn = 0} x"
            apply (rule returns_to_flowstoI[OF _ _ _ _ _ _ order_refl])
            subgoal using prems assms by (auto simp: plane_of_def do_intersection_spec_def)
            subgoal by (rule empty_inter)
            subgoal using prems assms by (auto simp: plane_of_def do_intersection_spec_def)
            subgoal using prems assms by (auto simp: plane_of_def do_intersection_spec_def)
            subgoal using prems assms by (auto simp: plane_of_def do_intersection_spec_def)
            done
          have pm: "poincare_map {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} x \<in> fst ` P"
            apply (rule poincare_map_mem_flowstoI[OF ft])
            subgoal using prems assms by (auto simp: plane_of_def do_intersection_spec_def)
            subgoal using empty_inter by simp
            subgoal by auto
            subgoal by auto
            subgoal using prems assms by (auto simp: plane_of_def do_intersection_spec_def)
            subgoal by auto
            done
          from ret have "isCont (return_time {x \<in> ivl. x \<bullet> normal sctn - pstn sctn = 0}) x"
            apply (rule return_time_isCont_outside)
            subgoal by fact
                apply (force intro!: derivative_eq_intros)
            subgoal by (auto intro!: continuous_intros)
            subgoal using prems pm assms by (auto simp: do_intersection_spec_def)
            subgoal using prems pm assms
              by (auto simp: eventually_at_filter plane_of_def do_intersection_spec_def)
            subgoal
            proof -
              have "x \<in> CX i" using \<open>_ \<in> I \<Longrightarrow> X0 _ \<subseteq> CX _ \<times> UNIV\<close>[OF \<open>i \<in> I\<close>] \<open>(x, _) \<in> _\<close>
                by auto
              with assms(4)[OF \<open>i \<in> I\<close>] show ?thesis
                by (auto simp: plane_of_def)
            qed
            done
          then show "isCont (return_time {x \<in> ivl. x \<in> plane_of sctn}) x" by (simp add: plane_of_def)
        qed
        done
    qed
    done
  subgoal using assms by (fastforce simp: plane_of_def do_intersection_spec_def)
  subgoal using assms by (auto simp: plane_of_def do_intersection_spec_def)
  subgoal using assms by (fastforce simp: plane_of_def do_intersection_spec_def)
  subgoal using assms by (auto simp: plane_of_def do_intersection_spec_def)
  subgoal using assms by (auto simp: plane_of_def do_intersection_spec_def)
  subgoal using assms by (auto simp: plane_of_def do_intersection_spec_def)
  subgoal using assms by (auto simp: plane_of_def do_intersection_spec_def)
  subgoal using assms by (auto simp: plane_of_def do_intersection_spec_def)
  subgoal using assms(9) by (fastforce simp: plane_of_def do_intersection_spec_def)
  subgoal using assms by (auto simp: plane_of_def do_intersection_spec_def)
  subgoal using assms by (auto simp: plane_of_def do_intersection_spec_def)
  subgoal using assms by (auto simp: plane_of_def do_intersection_spec_def)
  done

lemma tendsto_at_top_translateI:
  assumes "(f \<longlongrightarrow> l) (at_top::real filter)"
  shows "((\<lambda>x. f (x + t)::'a::topological_space) \<longlongrightarrow> l) at_top"
proof (rule topological_tendstoI)
  fix S::"'a set" assume "open S" "l \<in> S"
  from topological_tendstoD[OF assms this]
  obtain N where "\<And>n. n \<ge> N \<Longrightarrow> f n \<in> S" by (auto simp: eventually_at_top_linorder)
  then have "\<And>n. n \<ge> N - t \<Longrightarrow> f (n + t) \<in> S" by auto
  then show "\<forall>\<^sub>F x in at_top. f (x + t) \<in> S"
    unfolding eventually_at_top_linorder
    by blast
qed

lemma tendsto_at_top_translate_iff:
  "((\<lambda>x. f (x + t)::'a::topological_space) \<longlongrightarrow> l) at_top \<longleftrightarrow> (f \<longlongrightarrow> l) (at_top::real filter)"
  using tendsto_at_top_translateI[of f l t]
    tendsto_at_top_translateI[of "\<lambda>x. f (x + t)" l "- t"]
  by auto

lemma flow_in_stable_setD:
  "flow0 x0 t \<in> stable_set trap \<Longrightarrow> t \<in> existence_ivl0 x0 \<Longrightarrow> x0 \<in> stable_set trap"
  apply (auto simp: stable_set_def)
proof goal_cases
  case (1 s)
  then show ?case
    apply (cases "s \<le> t")
    apply (meson atLeastAtMost_iff contra_subsetD local.ivl_subset_existence_ivl)
    using contra_subsetD local.existence_ivl_reverse local.existence_ivl_trans' local.flows_reverse by fastforce
next
  case (2)
  have "\<forall>\<^sub>F x in at_top. x > max t 0"
    by (simp add: max_def)
  then have "\<forall>\<^sub>F x in at_top. flow0 (flow0 x0 t) x = flow0 x0 (t + x)"
    apply eventually_elim
    apply (subst flow_trans)
    using 2
    by auto
  from this 2(3) have "((\<lambda>s. flow0 x0 (t + s)) \<longlongrightarrow> trap) (at_top)"
    by (rule Lim_transform_eventually)
  then show ?case by (simp add: tendsto_at_top_translate_iff ac_simps)
qed

definition (in auto_ll_on_open) "stable_on CX trap \<longleftrightarrow>
  (\<forall>t x0. flow0 x0 t \<in> trap \<longrightarrow> t \<in> existence_ivl0 x0 \<longrightarrow> t > 0 \<longrightarrow>
    (\<forall>s\<in>{0<..t}. flow0 x0 s \<in> CX) \<longrightarrow> x0 \<in> trap)"

lemma  (in auto_ll_on_open) stable_onD:
  "\<And>t x0. flow0 x0 t \<in> trap \<Longrightarrow> t \<in> existence_ivl0 x0 \<Longrightarrow> t > 0 \<Longrightarrow>
      (\<And>s. 0 < s \<Longrightarrow> s \<le> t \<Longrightarrow> flow0 x0 s \<in> CX) \<Longrightarrow>
      x0 \<in> trap"
  if "stable_on CX trap"
  using that by (auto simp: stable_on_def)

lemma
  poincare_mapsto_avoid_trap:
  assumes "poincare_mapsto p (X0 - trap \<times> UNIV) S CX P"
  assumes "closed p"
  assumes trapprop[THEN stable_onD]: "stable_on (CX \<union> fst ` P) trap"
  shows "poincare_mapsto p (X0 - trap \<times> UNIV) S CX (P - trap \<times> UNIV)"
  using assms(1,2)
  apply (auto simp: poincare_mapsto_def)
  apply (drule bspec, force)
  apply auto
  subgoal for x0 d0 D
    apply (rule exI[where x=D])
    apply (auto dest!: trapprop simp: poincare_map_def intro!: return_time_exivl assms(1,2) return_time_pos)
    subgoal for s
      by (cases "s = return_time p x0") (auto simp: )
    done
  done

lemma stable_on_mono:
  "stable_on A B" if "stable_on C B" "A \<subseteq> C"
  using that
  unfolding stable_on_def
  by fastforce

lemma poincare_onto_series[le, refine_vcg]:
  assumes wdp: "vwd_step (TYPE('a::enum))"
  notes [refine_vcg] = wdp vwd_step vwd_stepD[OF wdp]
  assumes [refine_vcg]: "\<And>X0. X0 \<subseteq> Csafe \<times> UNIV \<Longrightarrow> symstart X0 \<le> SPEC (\<lambda>(CX, X). flowsto (X0 - trap \<times> UNIV) {0..} (CX \<times> UNIV) (X))"
  assumes trapprop: "stable_on (Csafe - (ivl \<inter> plane_of sctn)) trap"
  shows "poincare_onto_series symstart trap guards (X0::'a eucl1 set) ivl sctn ro \<le>
       SPEC (\<lambda>XS. do_intersection_spec UNIV {} ivl sctn (X0 - trap \<times> UNIV)
          (XS, Csafe - (ivl \<inter> plane_of sctn)) \<and>
          fst ` X0 - trap \<subseteq> Csafe - (ivl \<inter> plane_of sctn))"
proof (induction guards arbitrary: X0)
  case Nil
  then show ?case
    apply (simp add:)
    apply refine_vcg
    apply (clarsimp simp add: ivlsctn_to_set_def)
     apply (rule do_intersection_spec_subset2, assumption)
    subgoal by (auto simp: do_intersection_spec_def)
    subgoal by (auto simp: do_intersection_spec_def)
    subgoal by (auto simp: do_intersection_spec_def)
    subgoal by (auto simp: do_intersection_spec_def)
    subgoal by (auto simp: do_intersection_spec_def)
    subgoal by (auto simp: do_intersection_spec_def)
    done
next
  case (Cons a guards)
  note Cons.IH[le, refine_vcg]
  show ?case
    apply auto
    apply refine_vcg
     apply clarsimp_all
     defer
    subgoal premises prems for a b c d e f g h
    proof -
      from prems have "(f, g) \<in> (\<Union>x\<in>c. h x)"
        by auto
      then obtain x where "x \<in> c" "(f, g) \<in> (h x)"
        by auto
      then show ?thesis
        using prems(14)[rule_format, OF \<open>x \<in> c\<close>] prems(5-7)
        by (cases x) (auto simp: do_intersection_spec_def)
    qed
    subgoal premises prems for b c ro d e f
    proof -
      let ?s = "trap \<times> UNIV"
      note prems
      from \<open>do_intersection_spec _ _ _ _ _ _ \<close>
      have disro: "do_intersection_spec UNIV {} ivl sctn ((\<Union>i\<in>ro. case i of (_, _, PS, _, _, _, _, _, _) \<Rightarrow> PS - ?s))
          (e, Csafe - ivl \<inter> plane_of sctn)"
        apply (rule do_intersection_spec_subset)
        using prems by auto
      have subset: "(Csafe - ivl \<inter> plane (normal sctn) (pstn sctn)) \<supseteq>
        (snd (snd (snd (snd (snd (snd (snd (snd i))))))) \<union>
        fst (snd (snd (snd (snd (snd (snd (snd i))))))) \<union> fst ` fst (snd (snd i)))" if "i \<in> ro" for i
        using prems(12)[rule_format, unfolded do_intersection_spec_def, OF that]
        apply (clarsimp )
        subgoal for s X P1 P2 R ivla sctna CX CXS
          apply (rule conjI)
          subgoal by (auto simp: plane_of_def)
          subgoal by (auto simp: plane_of_def)
          done
        done
      have pmro: "poincare_mapsto
            (case i of (s, X, P1, P2, R, ivla, sctna, CX, CXS) \<Rightarrow> {x \<in> ivla. x \<in> plane_of sctna})
            (f i - ?s) UNIV
            (case i of (s, X, P1, P2, R, ivla, sctna, CX, CXS) \<Rightarrow> CXS \<union> CX)
            (case i of (s, X, P1, P2, R, ivla, sctna, CX, CXS) \<Rightarrow> P1)"
        if "i \<in> ro"
        for i
        using prems(12)[rule_format, unfolded do_intersection_spec_def, OF that]
        by (auto intro: poincare_mapsto_subset)
      then have pmro: "poincare_mapsto
            (case i of (s, X, P1, P2, R, ivla, sctna, CX, CXS) \<Rightarrow> {x \<in> ivla. x \<in> plane_of sctna})
            (f i - ?s) UNIV
            (case i of (s, X, P1, P2, R, ivla, sctna, CX, CXS) \<Rightarrow> CXS \<union> CX)
            (case i of (s, X, P1, P2, R, ivla, sctna, CX, CXS) \<Rightarrow> P1 - ?s)"
        if "i \<in> ro"
        for i
        unfolding split_beta'
        apply (rule poincare_mapsto_avoid_trap)
        using that prems assms
        by (auto intro!: closed_levelset_within continuous_intros
            stable_on_mono[OF _ subset]
            simp: plane_of_def)
      have "do_intersection_spec UNIV {} ivl sctn (\<Union>i\<in>ro. f i - ?s)
        (e, (\<Union>i\<in>ro. case i of (s, X, P1, P2, R, ivla, sctna, CX, CXS) \<Rightarrow> CXS \<union> CX) \<union>
        (Csafe - ivl \<inter> plane_of sctn))"
        apply (rule do_intersection_poincare_mapstos_trans[OF pmro disro])
        subgoal by auto
        subgoal premises that for i
          using prems(12)[rule_format, unfolded do_intersection_spec_def, OF that]
          by (auto simp: do_intersection_spec_def)
        subgoal using assms(1,2) prems by (auto simp: do_intersection_spec_def)
        subgoal by auto
        subgoal premises that for i
          using prems(12)[rule_format, unfolded do_intersection_spec_def, OF that]
            prems(11) that
          by (auto simp: do_intersection_spec_def)
        subgoal using assms(1,2) prems by (auto simp: do_intersection_spec_def)
        subgoal using assms(1,2) prems by (auto simp: do_intersection_spec_def)
        subgoal using assms(1,2) prems by (auto simp: do_intersection_spec_def)
        done
      then show ?thesis
        unfolding \<open>(\<Union>x\<in>ro. f x) = X0 - trap \<times> UNIV\<close>
        apply (rule do_intersection_spec_subset2)
        subgoal using assms(1,2) prems by (auto simp: do_intersection_spec_def)
        using prems
        by (auto simp: do_intersection_spec_def intro: poincare_mapsto_subset)
    qed
    done
qed

lemma
  do_intersection_flowsto_trans_return:
  assumes "flowsto XS0 {0<..} (CX \<times> UNIV) X1"
  assumes "do_intersection_spec UNIV guards ivl sctn X1 (P, CP)"
  assumes "fst ` X1 \<subseteq> CP"
  assumes "{x \<in> ivl. x \<in> plane_of sctn} \<inter> CX = {}"
  assumes "guards \<inter> (CX \<union> CP) = {}"
  assumes "closed ivl"
  assumes "CX \<subseteq> sbelow_halfspace sctn \<inter> Csafe"
  assumes subset_plane: "fst ` XS0 \<subseteq> plane_of sctn \<inter> ivl"
  assumes down: "\<And>x d. (x, d) \<in> XS0 \<Longrightarrow> ode x \<bullet> normal sctn < 0" "\<And>x. x \<in> CX \<Longrightarrow> ode x \<bullet> normal sctn < 0"
  shows "do_intersection_spec (below_halfspace sctn) guards ivl sctn XS0 (P, CX \<union> CP)"
  using assms
  apply (auto simp: do_intersection_spec_def)
  subgoal
    apply (rule flowsto_poincare_trans, assumption, assumption)
    subgoal by simp
    subgoal by auto
    subgoal using assms(3) by auto
    subgoal by (auto intro!: closed_levelset_within continuous_intros simp: plane_of_def)
     prefer 2
    subgoal by (auto simp add: plane_of_def halfspace_simps)
    subgoal premises prems for x d
    proof -
      have [intro, simp]: "closed {x \<in> ivl. x \<in> plane_of sctn} " "closed {x \<in> ivl. x \<bullet> normal sctn = pstn sctn}"
        by (auto intro!: closed_levelset_within continuous_intros simp: plane_of_def assms)
      from subset_plane have "fst ` XS0 \<subseteq> below_halfspace sctn" by (auto simp: )
      from flowsto_stays_sbelow[OF \<open>flowsto _ _ _ _\<close> this down(2)]
      have ft_below: "flowsto XS0 pos_reals (CX \<times> UNIV \<inter> sbelow_halfspace sctn \<times> UNIV) X1"
        by auto
      from flowsto_poincare_mapsto_trans_flowsto[OF ft_below \<open>poincare_mapsto _ _ _ _ _\<close> _ _ order_refl]
      have ft: "flowsto XS0 {0<..} (X1 \<union> CX \<times> UNIV \<inter> sbelow_halfspace sctn \<times> UNIV \<union> CP \<times> UNIV) (fst ` P \<times> UNIV)"
        by (auto simp: )
      have ret: "returns_to {x \<in> ivl. x \<bullet> normal sctn - pstn sctn = 0} x"
        apply (rule returns_to_flowstoI[OF ft])
        using prems by (auto simp: plane_of_def halfspace_simps)
      have pm: "poincare_map {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} x \<in> fst ` P"
        apply (rule poincare_map_mem_flowstoI[OF ft])
        using prems by (auto simp: plane_of_def halfspace_simps)
      from pm prems have evmem: "\<forall>\<^sub>F x in at (poincare_map {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} x) within
        plane_of sctn. x \<in> ivl"
        by auto
      from ret have "continuous (at x within {x. x \<bullet> normal sctn - pstn sctn \<le> 0})
        (return_time {x \<in> ivl. x \<bullet> normal sctn - pstn sctn = 0})"
        apply (rule return_time_continuous_below)
               apply (rule derivative_eq_intros refl)+
               apply force
        subgoal using \<open>closed ivl\<close> by auto
        subgoal using prems pm by (auto simp: plane_of_def eventually_at_filter)
        subgoal by (auto intro!: )
        subgoal using prems pm by auto
        subgoal using prems by auto
        subgoal using prems pm by (auto intro!: assms simp: plane_of_def)
        subgoal using prems pm by auto
        done
      then show "continuous (at x within below_halfspace sctn) (return_time {x \<in> ivl. x \<in> plane_of sctn})"
        by (simp add: plane_of_def halfspace_simps)
    qed
    done
  done

definition "poincare_onto_from interrupt trap
                               S                      \<comment> \<open>leaving this (half)space in the beginning\<close>
                          (guards)                    \<comment> \<open>avoiding guards\<close>
                          (ivl::'n rvec set)          \<comment> \<open>onto \<open>ivl\<close>\<close>
                          sctn                        \<comment> \<open>which is part of \<open>sctn\<close>\<close>
                          ro
                          (XS0::'n::enum eucl1 set) =
  do {
    ASSUME (closed ivl);
    let guardset = (\<Union>(ivlsctn, ro)\<in>set (guards). ivlsctn:::clw_rel (iplane_rel lvivl_rel));
    lsctn \<leftarrow> leaves_halfspace S (op_image_fst_colle XS0);
    XS0 \<leftarrow> (case lsctn of
        None \<Rightarrow> RETURN XS0
      | Some lsctn =>
        do {
            CHECKs ''poincare_onto_from: section only makes sense if start section = end section''
              (lsctn = sctn \<or> normal lsctn = - normal sctn \<and> pstn lsctn = - pstn sctn);
            guards \<leftarrow> unintersect_coll guardset;
            b \<leftarrow> subset_spec_coll (op_image_fst_colle XS0) ivl;
            CHECKs ''poincare_onto_from: section only makes sense if we start from there'' b;
            (XS0, _) \<leftarrow> poincare_start_on guards lsctn (XS0);
            RETURN XS0
        }
      );
    PS \<leftarrow> poincare_onto_series interrupt trap guards XS0 ivl sctn ro;
    RETURN PS
  }"
sublocale autoref_op_pat_def poincare_onto_from .

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
  by (autoref_monadic)

concrete_definition poincare_onto_from_impl for symstartd Si guardsi ivli sctni roi XSi uses poincare_onto_from_impl
lemmas [autoref_rules] = poincare_onto_from_impl.refine

lemma do_intersection_spec_sctn_cong:
  assumes "sctn = sctn' \<or> (normal sctn = - normal sctn' \<and> pstn sctn = - pstn sctn')"
  shows "do_intersection_spec a b c sctn d e = do_intersection_spec a b c sctn' d e"
  using assms
  by (auto simp: do_intersection_spec_def plane_of_def set_eq_iff intro!: )

lemma
  flowsto_mapsto_avoid_trap:
  assumes "flowsto (X0 - trap \<times> UNIV) {0<..} CX P"
  assumes trapprop: "stable_on (fst ` (CX \<union> P)) trap"
  shows "flowsto (X0 - trap \<times> UNIV) {0<..} CX (P - trap \<times> UNIV)"
  unfolding flowsto_def
proof (rule, goal_cases)
  case (1 xd)
  from assms(1)[unfolded flowsto_def, rule_format, OF this] obtain h x0 d0 where
    "xd = (x0, d0)" "0 < h"
    "h \<in> existence_ivl0 (x0)"
    "(flow0 x0 h, Dflow x0 h o\<^sub>L d0) \<in> P"
    "(\<forall>h'\<in>{0<--<h}. (flow0 x0 h', Dflow x0 h' o\<^sub>L d0) \<in> CX)"
    by auto
  then show ?case
    using 1 trapprop
    apply (auto intro!: bexI[where x=h] dest!: stable_onD simp: open_segment_eq_real_ivl image_Un)
    subgoal for s by (cases "s = h") auto
    done
qed

lemma poincare_onto_from[le, refine_vcg]:
  assumes wdp: "vwd_step (TYPE('a::enum))"
  notes [refine_vcg] = wdp vwd_step vwd_stepD[OF wdp]
  assumes [refine_vcg]: "\<And>X0. X0 \<subseteq> Csafe \<times> UNIV \<Longrightarrow> symstart X0 \<le> SPEC (\<lambda>(CX, X). flowsto (X0 - trap \<times> UNIV) {0..} (CX \<times> UNIV) (X))"
  assumes trapprop: "stable_on (Csafe - (ivl \<inter> plane_of sctn)) trap"
  shows "poincare_onto_from symstart trap S guards ivl sctn ro (XS0::'a eucl1 set) \<le>
    SPEC (poincare_mapsto (ivl \<inter> plane_of sctn) (XS0 - trap \<times> UNIV) S (Csafe - ivl \<inter> plane_of sctn))"
  unfolding poincare_onto_from_def autoref_tag_defs
  apply (refine_vcg, clarsimp_all simp: trapprop)
  subgoal by (auto simp: do_intersection_spec_def Int_def intro: poincare_mapsto_subset)
  subgoal premises prems for a b c d e f
  proof -
    note prems
    from trapprop
    have stable: "stable_on (fst ` (e \<times> UNIV \<inter> sbelow_halfspace a \<times> UNIV \<union> d)) trap"
      apply (rule stable_on_mono)
      using \<open>fst ` (d \<union> e \<times> UNIV) \<subseteq> Csafe\<close> \<open>a = sctn \<or> normal a = - normal sctn \<and> pstn a = - pstn sctn\<close>
        \<open>fst ` d \<subseteq> sbelow_halfspace a\<close>
      by (auto simp: halfspace_simps plane_of_def image_Un)
    from prems(16) have "flowsto (XS0 - trap \<times> UNIV) {0<..} (e \<times> UNIV \<inter> sbelow_halfspace a \<times> UNIV) d"
      by (rule flowsto_subset) auto
    then have ft: "flowsto (XS0 - trap \<times> UNIV) {0<..} ((e \<inter> sbelow_halfspace a) \<times> UNIV) (d - trap \<times> UNIV)"
      by (auto intro!: flowsto_mapsto_avoid_trap stable simp: Times_Int_distrib1)
    from prems(8) have di: "do_intersection_spec UNIV {} ivl a (d - trap \<times> UNIV) (f, Csafe - ivl \<inter> plane_of sctn)"
      apply (subst do_intersection_spec_sctn_cong)
       defer apply assumption
      using prems(2)
      by auto
    have "do_intersection_spec (below_halfspace a) {} ivl a (XS0 - trap \<times> UNIV)
         (f, e \<inter> sbelow_halfspace a \<union> (Csafe - ivl \<inter> plane_of sctn))"
      apply (rule do_intersection_flowsto_trans_return[OF ft di])
      subgoal using prems by (auto simp: do_intersection_spec_def halfspace_simps plane_of_def)
      subgoal by (auto simp: halfspace_simps plane_of_def)
      subgoal using prems by (auto simp: halfspace_simps plane_of_def)
      subgoal using prems by (auto simp: do_intersection_spec_def halfspace_simps plane_of_def)
      subgoal using prems by (auto simp: image_Un)
      subgoal using prems by (auto simp: do_intersection_spec_def halfspace_simps plane_of_def)
      subgoal using prems by (auto simp: do_intersection_spec_def halfspace_simps plane_of_def)
      subgoal using prems by (auto simp: do_intersection_spec_def halfspace_simps plane_of_def)
      done
    moreover have "plane_of a = plane_of sctn"
      using prems(2) by (auto simp: plane_of_def)
    ultimately show ?thesis
      apply (auto simp add: do_intersection_spec_def Int_def)
      apply (rule poincare_mapsto_subset, assumption)
      by auto
  qed
  done

definition [simp]: "op_times_ivl a b = a \<times> b"
lemma [autoref_op_pat]: "a \<times> b \<equiv> OP op_times_ivl $ a $ b"
  by (auto simp: )

lemma op_times_ivl[autoref_rules]:
  "(\<lambda>(l, u) (l', u'). (l @ l', u @ u'), op_times_ivl) \<in> lvivl_rel \<rightarrow> lvivl_rel \<rightarrow> lvivl_rel"
  apply (auto simp: ivl_rel_def br_def intro!: rel_funI)
  subgoal for a b c d e f g h
    apply (rule relcompI[where b="((c, g), (d, h))"])
    by (auto simp: lv_rel_def br_def set_of_ivl_def)
  done

definition [refine_vcg_def]: "default_rep d X = SPEC (\<lambda>x. case x of None \<Rightarrow> X = d | Some r \<Rightarrow> X = r)"
lemma [autoref_op_pat_def]: "default_rep d \<equiv> OP (default_rep d)"
  by (auto simp: )

lemma default_rep[autoref_rules]:
  "(\<lambda>x. RETURN x, default_rep d) \<in> (\<langle>R\<rangle>(default_rel d)) \<rightarrow> \<langle>\<langle>R\<rangle>option_rel\<rangle>nres_rel"
  by (force simp: default_rep_def nres_rel_def default_rel_def
      split: option.splits intro!: RETURN_SPEC_refine )

definition "subset_spec1 R P dP = do {
    R1 \<leftarrow> vec1rep R;
    dP \<leftarrow> default_rep UNIV dP;
    case (R1, dP) of (_, None) \<Rightarrow>
      subset_spec (fst ` R) P
    | (Some RdR, Some dP) \<Rightarrow>
      subset_spec RdR (P \<times> dP)
    | (None, Some _) \<Rightarrow> RETURN False
  }"
sublocale autoref_op_pat_def subset_spec1 .

schematic_goal subset_spec1_impl:
  "(nres_of ?r, subset_spec1 R P dP) \<in> \<langle>bool_rel\<rangle>nres_rel"
  if [autoref_rules]:
    "(Ri, R) \<in> appr1_rel"
    "(Pimpl, P) \<in> lvivl_rel"
    "(dPi, dP) \<in> \<langle>lvivl_rel\<rangle>(default_rel UNIV)"
  unfolding subset_spec1_def
  including art
  by (autoref_monadic)
lemmas [autoref_rules] = subset_spec1_impl[autoref_higher_order_rule]

lemma subset_spec1[refine_vcg]: "subset_spec1 R P dP \<le> SPEC (\<lambda>b. b \<longrightarrow> R \<subseteq> flow1_of_vec1 ` (P \<times> dP))"
  unfolding subset_spec1_def
  by refine_vcg (auto simp: vec1_of_flow1_def)

definition "subset_spec1_coll R P dP = do {
    XS \<leftarrow> sets_of_coll R;
    WEAK_ALL (\<lambda>x. x \<subseteq> flow1_of_vec1 ` (P \<times> dP)) XS (\<lambda>X. subset_spec1 X P dP)
  }"

lemma subset_spec1_coll[le, refine_vcg]:
  "subset_spec1_coll R P dP \<le> subset_spec R (flow1_of_vec1 ` (P \<times> dP))"
  unfolding autoref_tag_defs subset_spec_def subset_spec1_coll_def
  by (refine_vcg) (auto simp: subset_iff set_of_ivl_def)
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

lemma list_set_rel_br: "\<langle>Id\<rangle>list_set_rel = br set distinct"
  by (auto simp: list_set_rel_def)

lemma
  br_list_relD:
  shows "(x, y) \<in> \<langle>br a i\<rangle>list_set_rel \<Longrightarrow> y = a ` set x \<and> list_all i x"
  apply (auto simp: list_set_rel_def br_def list_rel_def)
  subgoal premises prems for s t
    using prems
    by (induction arbitrary: y rule: list.rel_induct) auto
  subgoal premises prems for s t
    using prems
    by (induction arbitrary: y rule: list.rel_induct) auto
  subgoal premises prems for s
    using prems
    by (induction arbitrary: y rule: list.rel_induct) auto
  done

lemma [autoref_itype]: "compact ::\<^sub>i A \<rightarrow>\<^sub>i i_bool"
  by auto

lemma lvivl_rel_compact[autoref_rules]:
  "(\<lambda>_::_\<times>_. True, compact) \<in> lvivl_rel \<rightarrow> bool_rel"
  "(\<lambda>_::(_\<times>_)list. True, compact) \<in> clw_rel lvivl_rel \<rightarrow> bool_rel"
  by (auto simp: lvivl_rel_br set_of_ivl_def lw_rel_def Union_rel_br dest!: brD)

lemma [autoref_itype del]: "ivl_rep_of_set ::\<^sub>i i_appr \<rightarrow>\<^sub>i \<langle>\<langle>i_rnv, i_rnv\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_nres"
  and [autoref_itype]: "ivl_rep_of_set ::\<^sub>i A \<rightarrow>\<^sub>i \<langle>\<langle>i_rnv, i_rnv\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_nres"
  by auto

lemma ivl_rep_of_set_lvivl_rel[autoref_rules]:
  "(\<lambda>(x, y). RETURN (map2 min x y, y), ivl_rep_of_set) \<in> lvivl_rel \<rightarrow> \<langle>lv_rel \<times>\<^sub>r lv_rel\<rangle>nres_rel"
  apply (auto simp: nres_rel_def ivl_rep_of_set_def lvivl_rel_br  br_def set_of_ivl_def min_def
      intro!: RETURN_SPEC_refine)
  subgoal for xs ys
    apply (rule exI[])
    apply (rule conjI)
     apply (rule lv_rel_inf[param_fo])
    by (auto simp: lv_rel_def intro!: brI lv_rel_inf[param_fo])
  done

lemma phantom_rel_union_coll[autoref_rules]:\<comment> \<open>TODO: move!\<close>
  assumes [THEN GEN_OP_D, autoref_rules(overloaded)]: "GEN_OP un op_union_coll (clw_rel A \<rightarrow> clw_rel A \<rightarrow> clw_rel A)"
  shows "(\<lambda>a b. do {a \<leftarrow> a; b \<leftarrow> b; Some (un a b)}, op_union_phantom) \<in> \<langle>clw_rel A\<rangle>phantom_rel \<rightarrow> \<langle>clw_rel A\<rangle>phantom_rel \<rightarrow> \<langle>clw_rel A\<rangle>phantom_rel"
  using assms
  by (fastforce simp: phantom_rel_def dest: fun_relD)

definition "one_step_until_time X0 (ph::bool) (t1::real) =
  do {
    CHECKs ''one_step_until_time optns'' (0 \<le> t1 \<and> 0 < start_stepsize optns \<and>
      0 < rk2_param optns \<and> rk2_param optns \<le> 1);
    let fX0 = fst ` X0;
    mk_safe (fX0);
    (t, _, X, CX) \<leftarrow> WHILE (\<lambda>(t, _, _, _). t < t1) (\<lambda>(t, h, X, CXs). do {
        let _ = trace_set1e (''choose step from:'') (Some X);
        (h0, CX, X, h') \<leftarrow> step_adapt_time X (min h (t1 - t));
        CHECKs ''one_step negative step'' (h0 \<ge> 0 \<and> h' > 0 \<and> h0 \<le> min h (t1 - t));
        let _ = trace_set (''interpolated step:'') (Some CX);
        let _ = print_set True CX;
        let _ = trace_set1e (''step:'') (Some X);
        let _ = print_set1e False X;
        let fCX = CX;
        mk_safe fCX;
        let fX = fst ` X;
        mk_safe fX;
        RETURN (t + h0, h', X, mk_phantom (mk_coll CX) \<union> CXs)
    }) (0::real, start_stepsize optns::real, X0, op_union_phantom (mk_phantom (mk_coll fX0)) (op_empty_phantom ph));
    RETURN (X, CX)
  }"
sublocale autoref_op_pat_def one_step_until_time .

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

lemma one_step_until_time_spec[le, refine_vcg]:
  assumes wdp: "vwd_step (TYPE('n::enum))"
  notes [refine_vcg] = wdp vwd_step vwd_stepD[OF wdp]
  shows "one_step_until_time (X0::'n eucl1 set) CX t1 \<le> SPEC (\<lambda>(R, CX).
    (\<forall>(x0, d0) \<in> X0. t1 \<in> existence_ivl0 x0 \<and>
      (flow0 x0 t1, Dflow x0 t1 o\<^sub>L d0) \<in> R \<and>
      (\<forall>t \<in> {0 .. t1}. flow0 x0 t \<in> CX)) \<and>
      fst ` R \<union> CX \<subseteq> Csafe)"
  unfolding one_step_until_time_def autoref_tag_defs
  apply (refine_vcg WHILE_rule[where I="\<lambda>(t, h, X, CX). fst ` X \<subseteq> Csafe \<and> CX \<subseteq> Csafe \<and> 0 \<le> h \<and> 0 \<le> t \<and> t \<le> t1 \<and>
        (\<forall>(x0, d0) \<in> X0. t \<in> existence_ivl0 x0 \<and>
          (flow0 x0 t, Dflow x0 t o\<^sub>L d0) \<in> X \<and>
          (\<forall>s \<in> {0 .. t}. flow0 x0 s \<in> CX))"])
  subgoal by auto
  subgoal by (force simp: flowpipe_def existence_ivl_trans flow_trans)
  subgoal by (auto simp: flowpipe_def existence_ivl_trans flow_trans)
  apply clarsimp subgoal for a b c d e f g h i j
    apply (safe)
    subgoal by (auto simp: flowpipe_def intro!: existence_ivl_trans flow_trans)
    subgoal
      apply (subst flow_trans, force)
      subgoal by (auto simp: flowpipe_def intro!: existence_ivl_trans flow_trans)
      apply (subst Dflow_trans, force)
      subgoal by (auto simp: flowpipe_def intro!: existence_ivl_trans flow_trans)
      by (auto simp: blinfun_compose_assoc flowpipe_def)
    subgoal for s
      apply (drule bspec[where x="(i, j)"], assumption)
      apply auto
      apply (cases "s \<le> a")
      subgoal by auto
      subgoal
        apply (auto simp: blinfun_compose_assoc flowpipe_def)
        apply (drule bspec, assumption)
        apply auto
      proof goal_cases
        case 1
        have a: "a \<in> existence_ivl0 i" using 1 by auto
        have sa: "s - a \<in> existence_ivl0 (flow0 i a)"
          using "1"(15) "1"(19) "1"(20) local.ivl_subset_existence_ivl by fastforce
        have "flow0 i s = flow0 (flow0 i a) (s - a)"
          by (auto simp: a sa flow_trans[symmetric])
        also have "\<dots> \<in> f"
          using 1 by auto
        finally show ?case
          using 1 by simp
      qed
      done
    done
  subgoal by auto
  done

text \<open>solve ODE until the time interval \<open>{t1 .. t2}\<close>\<close>

definition [refine_vcg_def]: "get_phantom X = SPEC (\<lambda>R. R = X)"
sublocale autoref_op_pat_def get_phantom .

lemma get_phantom_impl[autoref_rules]:
  "(\<lambda>x. nres_of (case x of None \<Rightarrow> dSUCCEED | Some y \<Rightarrow> dRETURN y), get_phantom) \<in> \<langle>A\<rangle>phantom_rel \<rightarrow> \<langle>A\<rangle>nres_rel"
  by (auto simp: get_phantom_def phantom_rel_def nres_rel_def RETURN_RES_refine_iff)

definition "ivl_of_eucl_coll CY =
  do {
    (i, s) \<leftarrow> ivl_rep_of_set_coll CY;
    ASSERT (i \<le> s);
    RETURN (({i .. s}\<times>UNIV):::appr1_rel)
  }"
sublocale autoref_op_pat_def ivl_of_eucl_coll .

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

lemma ivl_of_eucl1_coll[THEN order_trans, refine_vcg]: "ivl_of_eucl_coll X \<le> SPEC (\<lambda>R. X \<times> UNIV \<subseteq> R)"
  unfolding ivl_of_eucl_coll_def
  by refine_vcg auto

definition "one_step_until_time_ivl X0 (ph::bool) (t1::real) (t2::real) =
  do {
    (X, CX) \<leftarrow>  one_step_until_time X0 ph t1;
    CHECKs ''one_step_until_time_ivl empty time interval'' (0 \<le> t1 \<and> t1 \<le> t2);
    (if t2 = t1 then RETURN (X, CX)
    else do {
      (Y, CYp) \<leftarrow> one_step_until_time X False (t2 - t1);
      CY \<leftarrow> get_phantom CYp;
      R \<leftarrow> ivl_of_eucl_coll CY;
      mk_safe (fst ` R);
      R \<leftarrow> scaleRe_ivl_spec 1 1 R;
      RETURN (R, CYp \<union> CX)
    })
  }"
sublocale autoref_op_pat_def one_step_until_time_ivl .

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
  by (autoref_monadic)
concrete_definition one_step_until_time_ivl_impl for X0i phi t1i t2i uses one_step_until_time_ivl_impl
lemmas [autoref_rules] = one_step_until_time_ivl_impl.refine

lemma one_step_until_time_ivl_spec[le, refine_vcg]:
  assumes wdp: "vwd_step (TYPE('n::enum))"
  notes [refine_vcg] = wdp vwd_step vwd_stepD[OF wdp]
  shows "one_step_until_time_ivl (X0::'n eucl1 set) CX t1 t2 \<le> SPEC (\<lambda>(R, CX).
    (\<forall>(x0, d0) \<in> X0. {t1 .. t2} \<subseteq> existence_ivl0 x0 \<and>
      (\<forall>t \<in> {t1 .. t2}. (flow0 x0 t, Dflow x0 t o\<^sub>L d0) \<in> R) \<and>
      (\<forall>t \<in> {0 .. t1}. (flow0 x0 t) \<in> CX)) \<and>
      fst ` R \<union> CX \<subseteq> Csafe)"
  unfolding one_step_until_time_ivl_def
  apply (refine_vcg, clarsimp_all)
  subgoal for X CX Y CY CY' x0 d0
    apply (drule bspec, assumption, clarsimp)
    apply (drule bspec, assumption, clarsimp simp add: nonneg_interval_mem_existence_ivlI)
    apply (rule set_mp, assumption)
    subgoal for t
      apply (drule bspec[where x=0], force)
      apply (drule bspec[where x="t - t1"], force)
      using interval_subset_existence_ivl[of t1 x0 t2]
      by (auto simp: flow_trans')
    done
  subgoal
    by (auto simp: scaleR2_def image_def vimage_def)
  done

end

locale approximate_sets_options' = approximate_sets_options\<comment> \<open>TODO: really?!\<close>

context approximate_sets_options' begin

sublocale approximate_sets_ode_slp'
  where D = D
    and ode_slp = ode_slp
    and euler_incr_slp = euler_incr_slp
    and euler_slp = euler_slp
    and rk2_slp = rk2_slp

    and ode_slp' = ode_slp'
    and euler_incr_slp' = euler_incr_slp'
    and euler_slp' = euler_slp'
    and rk2_slp' = rk2_slp'
    and solve_poincare_slp = solve_poincare_slp

    for D::nat
    and ode_slp::slp
    and euler_incr_slp::slp
    and euler_slp::slp
    and rk2_slp::slp

    and ode_slp'
    and euler_incr_slp'
    and euler_slp'
    and rk2_slp'
    and solve_poincare_slp
  by standard

definition trace_str::"string\<Rightarrow>unit" where "trace_str _ = ()"
sublocale autoref_op_pat_def trace_str .

lemma trace_str_impl[autoref_rules]:
  shows "(\<lambda>s. tracing_fun optns s None, trace_str) \<in> string_rel \<rightarrow> Id"
  by auto

definition "init_ode_solver (x::unit) = do {
  let D = length (ode_e);
  CHECK (\<lambda>_. trace_str ''init_ode_solver failed: rk2_param'')
    (0 < rk2_param optns \<and> rk2_param optns \<le> 1);
  CHECK (\<lambda>_. trace_str ''init_ode_solver failed: max_Var_floatariths'') (max_Var_floatariths ode_e \<le> D);
  CHECK (\<lambda>_. trace_str ''init_ode_solver failed: max_Var_form'') (max_Var_form safe_form \<le> D);
  CHECK (\<lambda>_. trace_str ''init_ode_solver failed: open_form safe_form'') (open_form safe_form);
  let ode_slp = slp_of_fas ode_e;
  let solve_poincare_slp = map (\<lambda>i. slp_of_fas (map fold_const_fa (solve_poincare_fas D i))) [0..<D];

  let euler_incr_slp = slp_of_fas (map fold_const_fa (euler_incr_fas (map floatarith.Var [0..<D]) (floatarith.Var (D))
      (map floatarith.Var [Suc D..<Suc (2*D)])));
  let euler_slp = slp_of_fas (map fold_const_fa (euler_fas (map floatarith.Var [0..<D])
    (floatarith.Var (2*D)) (map floatarith.Var [D..<2*D])));
  let rk2_slp = slp_of_fas (map fold_const_fa (rk2_fas
    (floatarith.Var (2*D))
    (map floatarith.Var [0..<D])
    (floatarith.Var (2*D+1))
    (map floatarith.Var [D..<2*D])
    (floatarith.Var (2*D+2))));

  let ode_slp' = slp_of_fas (ode_e' D);
  let D2 = D + D * D;
  let rk2_slp' = slp_of_fas
    (map fold_const_fa (var.rk2_fas D (Var (2 * D2)) (map Var [0..<D2]) (Var (2 * D2 + 1))
      (map Var [D2..<2 * D2]) (Var(2 * D2 + 2))));
  let euler_slp' = slp_of_fas
      (map fold_const_fa (var.euler_fas D (map floatarith.Var [0..<D2]) (Var (2 * D2))
        (map Var [D2..<2 * D2])));
  let euler_incr_slp' =
   slp_of_fas
    (map fold_const_fa (var.euler_incr_fas D (map floatarith.Var [0..<D2]) (Var (D2))
      (map Var [Suc D2..<Suc (2 * D2)])));
  RETURN (D, ode_slp,  euler_incr_slp,  euler_slp,  rk2_slp,
             ode_slp', euler_incr_slp', euler_slp', rk2_slp',
          solve_poincare_slp)
}"\<comment> \<open>TODO: use definitions for slps\<close>
sublocale autoref_op_pat_def init_ode_solver .

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

sublocale autoref_op_pat_def slp_of_fas .

lemma ode_autoref:
  "(ode_e, ode_e) \<in> \<langle>Id\<rangle>list_rel"
  "(safe_form, safe_form) \<in> Id"
  by auto

schematic_goal init_ode_solver_autoref:
  assumes [autoref_rules]:
    "(ui, u) \<in> unit_rel"
  notes [autoref_rules] = ode_autoref
  shows "(nres_of (?f), init_ode_solver $ u) \<in>
    \<langle>nat_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r
                \<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r
     \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding init_ode_solver_def
  including art
  by (autoref_monadic)
concrete_definition init_ode_solveri uses init_ode_solver_autoref
lemmas [autoref_rules] = init_ode_solveri.refine

lemma init_ode_solver[le, refine_vcg]:
  assumes [simp]: "length ode_e = CARD('n::enum)"
  shows "init_ode_solver u \<le> SPEC (\<lambda>(D, ode_slp, euler_incr_slp, euler_slp, rk2_slp,
    ode_slp', euler_incr_slp', euler_slp', rk2_slp', solve_poincare_slp).
      CARD('n) = D \<and>
      vwd_step D ode_slp euler_incr_slp euler_slp rk2_slp ode_slp' euler_incr_slp' euler_slp'
        rk2_slp' solve_poincare_slp TYPE('n))"
  unfolding init_ode_solver_def wd_step_def vwd_step_def
  apply (refine_vcg)
        apply (auto simp: var.rk2_slp_eq_def var.euler_slp_eq_def wd_def
      ode_slp_eq_def var.ode_slp_eq_def rk2_slp_eq_def euler_slp_eq_def euler_incr_slp_eq_def
      sps_eq_def)
  by (auto simp: var.euler_incr_slp_eq_def rk2_fas'_def euler_fas'_def euler_incr_fas'_def
      var.rk2_fas'_def var.euler_fas'_def var.euler_incr_fas'_def)


definition "poincare_onto_froma interrupt trap S guards ivl sctn ro (XS0::'n::enum eucl1 set) =
  do {
    (D, ode_slp, euler_incr_slp, euler_slp, rk2_slp,
       ode_slp', euler_incr_slp', euler_slp', rk2_slp', solve_poincare_slp) \<leftarrow> init_ode_solver ();
    ASSERT (vwd_step D ode_slp euler_incr_slp euler_slp rk2_slp ode_slp' euler_incr_slp' euler_slp'
      rk2_slp' solve_poincare_slp TYPE('n));
    OP poincare_onto_from $ D $ ode_slp $ euler_incr_slp $ euler_slp $ rk2_slp $ euler_incr_slp' $ euler_slp' $ rk2_slp' $
       solve_poincare_slp $ interrupt $ trap $ S $ guards $ ivl $ sctn $ ro $ XS0
  }"
sublocale autoref_op_pat_def poincare_onto_froma .

lemma poincare_onto_from_ivla[le, refine_vcg]:
  assumes [simp]: "length ode_e = CARD('n::enum)"
  assumes [refine_vcg]: "\<And>X0. X0 \<subseteq> Csafe \<times> UNIV \<Longrightarrow> symstart X0 \<le> SPEC (\<lambda>(CX, X). flowsto (X0 - trap \<times> UNIV) {0..} (CX \<times> UNIV) (X))"
  assumes trapprop[refine_vcg]: "stable_on (Csafe - (ivl \<inter> plane_of sctn)) trap"
  shows "poincare_onto_froma symstart trap S guards ivl sctn ro (XS0::'n eucl1 set) \<le> SPEC
     (\<lambda>P.
        wd (length ode_e) TYPE((real, 'n) vec) \<and>
        poincare_mapsto (ivl \<inter> plane_of sctn) (XS0 - trap \<times> UNIV) S (Csafe - ivl \<inter> plane_of sctn) P)"
  unfolding poincare_onto_froma_def autoref_tag_defs
  by (refine_vcg) (auto dest!: vwd_stepD(1))

lemma dres_nres_rel_nres_relD: "(symstartd, symstart) \<in> A \<rightarrow> \<langle>B\<rangle>dres_nres_rel \<Longrightarrow> (\<lambda>x. nres_of (symstartd x), symstart) \<in> A \<rightarrow> \<langle>B\<rangle>nres_rel"
  by (auto simp: dres_nres_rel_def nres_rel_def dest!: fun_relD)

lemma TRANSFER_I: "x \<Longrightarrow> TRANSFER x"
  by simp

lemma poincare_onto_from_ivla_refinep[autoref_rules]:
  assumes "DIM_precond TYPE('n::enum rvec) D"
  assumes "var.ncc_precond TYPE('n rvec)"
  assumes "var.ncc_precond TYPE('n vec1)"
  assumes "(Di, D) \<in> nat_rel"
  shows "(\<lambda>ode_slp euler_incr_slp euler_slp rk2_slp euler_incr_slp' euler_slp'
    rk2_slp' solve_poincare_slp symstartd trapi Si guardsi ivli sctni roi XSi.
    nres_of (poincare_onto_from_impl Di ode_slp euler_incr_slp euler_slp rk2_slp euler_incr_slp'
     euler_slp' rk2_slp' solve_poincare_slp symstartd Si guardsi ivli sctni roi XSi),
          poincare_onto_from $ D)
         \<in> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<rightarrow>
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
sublocale autoref_op_pat_def poincare_onto_from .

lemma wd_step_DIM_precond: "vwd_step D a b c d e f g h i TYPE('n::enum)\<Longrightarrow> DIM_precond TYPE('n rvec) D"
  by (auto simp: vwd_step_def wd_def)

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
  unfolding poincare_onto_froma_def
  including art
  by autoref_monadic
concrete_definition solve_poincare_map for symstartd Si guardsi ivli sctni roi XSi uses solve_poincare_map
lemmas [autoref_rules] = solve_poincare_map.refine
sublocale autoref_op_pat_def poincare_onto_froma .

definition "solve_one_step_until_timea (X0::'n::enum eucl1 set) CX t1 t2 =
  do {
    (D, ode_slp, euler_incr_slp, euler_slp, rk2_slp,
       ode_slp', euler_incr_slp', euler_slp', rk2_slp', solve_poincare_slp) \<leftarrow> init_ode_solver ();
    ASSERT (vwd_step D ode_slp euler_incr_slp euler_slp rk2_slp ode_slp' euler_incr_slp' euler_slp' rk2_slp' solve_poincare_slp TYPE('n));
    OP one_step_until_time_ivl $ D $ euler_incr_slp $ euler_slp $ rk2_slp $ euler_incr_slp' $ euler_slp' $ rk2_slp' $ X0 $ CX $ t1 $ t2
  }"
sublocale autoref_op_pat_def solve_one_step_until_timea .

lemma one_step_until_time_ivl_impl_refinep[autoref_rules]:
  assumes "DIM_precond TYPE('n::enum rvec) D"
  assumes "var.ncc_precond TYPE('n rvec)"
  assumes "var.ncc_precond TYPE('n vec1)"
  assumes "(Di, D) \<in> nat_rel"
  shows "(\<lambda>euler_incr_slp euler_slp rk2_slp euler_incr_slp' euler_slp' rk2_slp' X0i histi t1i t2i.
      nres_of (one_step_until_time_ivl_impl Di euler_incr_slp euler_slp rk2_slp euler_incr_slp' euler_slp' rk2_slp' X0i histi t1i t2i),
   one_step_until_time_ivl $ D)
         \<in> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow>
        appr1e_rel \<rightarrow> bool_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel \<rightarrow>
  \<langle>appr1e_rel \<times>\<^sub>r \<langle>clw_rel (appr_rel::(_\<times>('n rvec) set)set)\<rangle>phantom_rel\<rangle>nres_rel"
  using one_step_until_time_ivl_impl.refine assms by force
sublocale autoref_op_pat_def one_step_until_time .

schematic_goal solve_one_step_until_time_autoref:
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n::enum rvec)"
  assumes [autoref_rules_raw]: "var.ncc_precond TYPE('n::enum vec1)"
  assumes [autoref_rules]: "(X0i, X0) \<in> appr1e_rel" "(CXi, CX) \<in> bool_rel" "(t1i, t1) \<in> rnv_rel"
     "(t2i, t2) \<in> rnv_rel"
  notes [autoref_rules_raw] = wd_step_DIM_precond
  shows "(nres_of ?f, solve_one_step_until_timea $ (X0::'n eucl1 set) $ CX $ t1 $ t2) \<in>
    \<langle>appr1e_rel \<times>\<^sub>r \<langle>clw_rel appr_rel\<rangle>phantom_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding solve_one_step_until_timea_def
  including art
  by (autoref_monadic)
concrete_definition solve_one_step_until_time for X0i CXi t1i t2i uses solve_one_step_until_time_autoref
lemmas solve_one_step_until_time_refine[autoref_rules] = solve_one_step_until_time.refine

lemma one_step_until_timea[le, refine_vcg]:
  assumes [simp]: "length ode_e = CARD('n::enum)"
  shows "solve_one_step_until_timea (X0::'n eucl1 set) CX t1 t2 \<le> SPEC (\<lambda>(X, CX).
     wd CARD('n) TYPE((real, 'n) vec) \<and>
     (\<forall>(x0, d0)\<in>X0.
         {t1 .. t2} \<subseteq> existence_ivl0 x0 \<and>
         (\<forall>t\<in>{t1 .. t2}. (flow0 x0 t, Dflow x0 t o\<^sub>L d0) \<in> X) \<and>
         (\<forall>t\<in>{0..t1}. (flow0 x0 t) \<in> CX)) \<and>
     CX \<subseteq> Csafe)"
  unfolding solve_one_step_until_timea_def autoref_tag_defs
  by (refine_vcg) (auto simp: vwd_stepD)

lemma map_prod_def': "map_prod f g x = (f (fst x), g (snd x))"
  by (cases x) auto

lemma sctn_rel_br: "\<langle>br a I\<rangle>sctn_rel = br (\<lambda>x. case x of Sctn n p \<Rightarrow> Sctn (a n) p) (\<lambda>x. I (normal x))"
  apply (auto simp: sctn_rel_def br_def in_rel_def[abs_def] split: sctn.splits)
  subgoal for b x1 x2 by (cases b) auto
  subgoal for a b by (cases a; cases b) auto
  done

lemma br_list_rel: "\<langle>br a I\<rangle>list_rel = br (map a) (list_all I)"
  by (fastforce simp: list_rel_def br_def list_all2_iff Ball_def in_set_zip list_all_length
      intro!: nth_equalityI)

lemma list_set_rel_brp: "\<langle>br a I\<rangle>list_set_rel = br (\<lambda>xs. a ` set xs) (\<lambda>xs. list_all I xs \<and> distinct (map a xs))"
  unfolding list_set_rel_def br_list_rel br_chain o_def o_def
  by (auto)

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

definition "c1_info_invare n X = (let l = (fst (fst X)); u = (snd (fst X))
  in (c1_info_invar n (snd X)) \<and> (l < u \<or> -\<infinity> < l \<and> l \<le> u \<and> u < \<infinity>))"

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

definition "c0_info_of_appr X = eucl_of_list ` set_of_appr X"
definition "c0_info_of_apprs X = (\<Union>x\<in>set X. c0_info_of_appr x)"
definition "c0_info_of_appr' X = the_default UNIV (map_option c0_info_of_apprs X)"

lemma c0_info_of_apprsI:
  assumes "(b, a) \<in> clw_rel appr_rel"
  assumes "x \<in> a"
  shows "x \<in> c0_info_of_apprs b"
  using assms
  by (auto simp: appr_rel_br clw_rel_br c0_info_of_apprs_def c0_info_of_appr_def dest!: brD)

lemma c0_info_of_appr'I:
  assumes "(b, a) \<in> \<langle>clw_rel appr_rel\<rangle>phantom_rel"
  assumes "x \<in> a"
  shows "x \<in> c0_info_of_appr' b"
  using assms
  by (auto simp add: c0_info_of_appr'_def intro!: c0_info_of_apprsI split: option.splits)

lemmas rel_prod_br = br_rel_prod

definition "poincare_onto_from_in_ivl interrupt trap
                               S                      \<comment> \<open>leaving this (half)space in the beginning\<close>
                          (guards)                    \<comment> \<open>avoiding guards\<close>
                          (ivl::'n rvec set)          \<comment> \<open>onto \<open>ivl\<close>\<close>
                          sctn                        \<comment> \<open>which is part of \<open>sctn\<close>\<close>
                          ro
                          (XS0::'n::enum eucl1 set)
                          P dP =
  do {
    RS \<leftarrow> poincare_onto_froma interrupt trap S guards ivl sctn ro XS0;
    ((l, u), R) \<leftarrow> scaleR2_rep_coll RS;
    CHECKs ''poincare_onto_from_in: there should not be scaleR2'' (l = 1 \<and> u = 1);
    (l, u) \<leftarrow> ivl_rep P;
    CHECKs ''poincare_onto_from_in: strange interval'' (l \<le> u);
    _ \<leftarrow> mk_safe (length ode_e) {l .. u};
    subset_spec1_coll R P dP
  }"
sublocale autoref_op_pat_def poincare_onto_from_in_ivl .

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
  by (autoref_monadic)
concrete_definition poincare_onto_from_in_ivl_impl for symstarti Si guardsi ivli sctni roi XSi Pimpl dPi
  uses poincare_onto_from_in_ivl_impl
lemmas [autoref_rules] = poincare_onto_from_in_ivl_impl.refine

lemma scaleR2_id[simp]: "scaleR2 (1::ereal) 1 = (\<lambda>(x::('d \<times> 'c::real_vector) set). x)"
  by (rule scaleR2_1_1)

lemma poincare_onto_from_in_ivl[le, refine_vcg]:
  assumes [simp]: "length ode_e = CARD('n::enum)"
  assumes [refine_vcg]: "\<And>X0. X0 \<subseteq> Csafe \<times> UNIV \<Longrightarrow> symstart X0 \<le> SPEC (\<lambda>(CX, X). flowsto (X0 - trap \<times> UNIV) {0..} (CX \<times> UNIV) (X))"
  assumes trapprop: "stable_on (Csafe - (ivl \<inter> plane_of sctn)) trap"
  shows "poincare_onto_from_in_ivl symstart trap S guards ivl sctn ro (XS0::'n::enum eucl1 set) P dP \<le>
    SPEC (\<lambda>b. b \<longrightarrow> poincare_mapsto (ivl \<inter> plane_of sctn) (XS0 - trap \<times> UNIV) S (Csafe - ivl \<inter> plane_of sctn) (flow1_of_vec1 ` (P \<times> dP)))"
  unfolding poincare_onto_from_in_ivl_def
  apply (refine_vcg, clarsimp_all)
   apply (rule trapprop)
  apply (rule poincare_mapsto_subset)
      apply assumption
  by (auto simp: )

definition "solves_poincare_map symstart S guards ivli sctni roi XS P dP \<longleftrightarrow>
  poincare_onto_from_in_ivl_impl symstart S guards ivli sctni roi XS P dP = dRETURN True"

lemmas lvivl_relI = lv_relivl_relI

definition "set_of_lvivl' x = (case x of None \<Rightarrow> UNIV | Some x \<Rightarrow> set_of_lvivl x)"

definition "lvivl'_invar n x =
  (case x of None \<Rightarrow> True | Some (l, u) \<Rightarrow> length l = length u \<and> length u = n)"

lemma lvivl_default_relI:
  "(dRi, set_of_lvivl' dRi::'e::executable_euclidean_space set) \<in> \<langle>lvivl_rel\<rangle>default_rel UNIV"
  if "lvivl'_invar DIM('e) dRi"
  using that
  by (auto simp: set_of_lvivl'_def set_of_lvivl_def set_of_ivl_def lvivl'_invar_def
      intro!: mem_default_relI lvivl_relI)

theorem solves_poincare_map_ncc:
  fixes sctni pos ivli ssc XS ph rl ru dRi CXS X0 S trap
  defines "P \<equiv> set_of_lvivl ivli \<inter> plane_of (map_sctn eucl_of_list sctni)"
  defines "Sa \<equiv> below_halfspace (map_sctn eucl_of_list S)::'n::enum rvec set"
  defines "X0 \<equiv> c1_info_of_apprse XS"
  defines "X1 \<equiv> flow1_of_vec1 ` ({eucl_of_list rl .. eucl_of_list ru} \<times> set_of_lvivl' dRi)"
  assumes ncc: "var.ncc_precond TYPE('n rvec)" "var.ncc_precond TYPE('n vec1)"
  assumes ret: "solves_poincare_map symstart [S] guards ivli sctni roi XS (rl, ru) dRi"
  assumes symstart: "(symstart, symstarta::'n eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set)nres) \<in> appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>dres_nres_rel"
  assumes symstart_spec: "\<And>X0. X0 \<subseteq> Csafe \<times> UNIV \<Longrightarrow> symstarta X0 \<le> SPEC (\<lambda>(CX, X). flowsto (X0 - trap \<times> UNIV) {0..} (CX \<times> UNIV) (X))"
  assumes trapprop: "stable_on (Csafe - P) trap"
  assumes invar: "\<And>X. X \<in> set XS \<Longrightarrow> c1_info_invare CARD('n) X"
  assumes lens: "length ode_e = CARD('n)" "length (normal sctni) = CARD('n)" "length (fst ivli) = CARD('n)" "length (snd ivli) = CARD('n)"
    "length (normal S) = CARD('n)" "length rl = CARD('n)" "length ru = CARD('n)"
     "lvivl'_invar (CARD('n)*CARD('n)) dRi"
    "\<And>a xs b ba ro. (xs, ro) \<in> set guards \<Longrightarrow> ((a, b), ba) \<in> set xs \<Longrightarrow> length a = CARD('n) \<and> length b = CARD('n) \<and> length (normal ba) = CARD('n)"
  shows "poincare_mapsto P (X0 - trap \<times> UNIV) Sa (Csafe - P) X1"
proof -
  define guardsa::"('n rvec set \<times> 'a reach_options) list"  where "guardsa \<equiv> map (\<lambda>(x, y). (\<Union>x\<in>set x. case x of (x, y) \<Rightarrow> (case x of (x, y) \<Rightarrow> set_of_ivl (eucl_of_list x, eucl_of_list y)) \<inter> plane_of (map_sctn eucl_of_list y), y)) guards"
  have spm:
    "(XS, X0) \<in> clw_rel (appr1e_rel)"
    "([S], Sa) \<in> \<langle>lv_rel\<rangle>halfspaces_rel"
    "(guards, guardsa) \<in> \<langle>clw_rel (iplane_rel lvivl_rel) \<times>\<^sub>r reach_optns_rel\<rangle>list_rel"
    "(ivli, set_of_lvivl ivli::'n rvec set) \<in> lvivl_rel"
    "(sctni, map_sctn eucl_of_list sctni::'n rvec sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
    "(roi, roi) \<in> reach_optns_rel"
    "(symstart, symstarta) \<in> appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>dres_nres_rel"
    "((), trap) \<in> ghost_rel"
    using lens symstart
    by (auto simp: X0_def X1_def Sa_def P_def appr_rel_br set_rel_br
        br_chain o_def clw_rel_br  lv_rel_def sctn_rel_br ivl_rel_br set_of_lvivl_def
        halfspaces_rel_def list_set_rel_brp below_halfspaces_def ghost_relI
        br_rel_prod br_list_rel guardsa_def Id_br inter_rel_br plane_rel_br
        split: sctn.splits
        intro!: brI list_allI clw_rel_appr1e_relI assms)

  have ivls: "((rl, ru), {eucl_of_list rl .. eucl_of_list ru::'n rvec}) \<in> lvivl_rel"
    "(dRi, set_of_lvivl' dRi::(('n rvec), 'n) vec set) \<in> \<langle>lvivl_rel\<rangle>default_rel UNIV"
    by (auto intro!: lvivl_relI lvivl_default_relI lens simp: lens set_of_lvivl_def set_of_ivl_def
        split: option.splits)

  have pmspec: "poincare_onto_from_in_ivl $ symstarta $ trap $ S $ guards $ ivl $ sctn $ ro $ XS0 $ IVL $ dIVL
  \<le> SPEC (\<lambda>b. b \<longrightarrow> poincare_mapsto (ivl \<inter> plane_of sctn) (XS0 - trap \<times> UNIV) S (Csafe - ivl \<inter> plane_of sctn)
                      (flow1_of_vec1 ` (IVL \<times> dIVL)))"
    if trapprop: "stable_on (Csafe - ivl \<inter> plane_of sctn) trap"
    for ivl sctn XS0 S guards ro IVL dIVL
    using poincare_onto_from_in_ivl[OF lens(1) symstart_spec trapprop order_refl,
        of S guards ro XS0 IVL dIVL]
    by auto
  from nres_rel_trans2[OF
      pmspec
      poincare_onto_from_in_ivl_impl.refine[OF ncc spm(1-8) ivls]
      ] ret trapprop
  show ?thesis
    by (auto simp: solves_poincare_map_def nres_rel_def P_def X1_def)
qed

lemma empty_symstart_dres_nres_rel:
  "((\<lambda>x. dRETURN ([], [x])), empty_symstart::'n::enum eucl1 set\<Rightarrow>_) \<in>
    (appr1e_rel) \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>dres_nres_rel"
  using mk_coll[OF PREFER_I[of single_valued, OF sv_appr1e_rel[OF sv_appr1_rel]], param_fo, of x y for x and y::"'n eucl1 set"]
  by (auto simp: mk_coll_def[abs_def] dres_nres_rel_def)

lemma empty_symstart_flowsto:
  "X0 \<subseteq> Csafe \<times> UNIV \<Longrightarrow>
    RETURN ({}, X0) \<le> SPEC (\<lambda>(CX, X). flowsto (X0 - {} \<times> UNIV) {0..} (CX \<times> UNIV) X)"
  by (auto intro!: flowsto_self)

definition "solves_poincare_map' S = solves_poincare_map (\<lambda>x. dRETURN ([], [x])) [S]"

lemma stable_on_empty[simp]: "stable_on A {}"
  by (auto simp: stable_on_def)

lemma solves_poincare_map'_ncc:
  "var.ncc_precond TYPE('n::enum rvec) \<Longrightarrow>
  var.ncc_precond TYPE('n vec1) \<Longrightarrow>
  solves_poincare_map' S guards ivli sctni roi XS (rl, ru) dRi \<Longrightarrow>
  (\<And>X. X \<in> set XS \<Longrightarrow> c1_info_invare CARD('n) X) \<Longrightarrow>
  length ode_e = CARD('n) \<Longrightarrow>
  length (normal sctni) = CARD('n) \<Longrightarrow>
  length (fst ivli) = CARD('n) \<Longrightarrow>
  length (snd ivli) = CARD('n) \<Longrightarrow>
  length (normal S) = CARD('n) \<Longrightarrow>
  length (rl) = CARD('n) \<Longrightarrow>
  length (ru) = CARD('n) \<Longrightarrow>
  lvivl'_invar (CARD('n)*CARD('n)) dRi \<Longrightarrow>
  (\<And>a xs b ba ro.
      (xs, ro) \<in> set guards \<Longrightarrow>
      ((a, b), ba) \<in> set xs \<Longrightarrow>
      length a = CARD('n) \<and>
      length b = CARD('n) \<and> length (normal ba) = CARD('n)) \<Longrightarrow>
  poincare_mapsto
   (set_of_lvivl ivli \<inter> plane_of (map_sctn eucl_of_list sctni)::'n rvec set)
   (c1_info_of_apprse XS) (below_halfspace (map_sctn eucl_of_list S))
   (Csafe - set_of_lvivl ivli \<inter> plane_of (map_sctn eucl_of_list sctni))
   (flow1_of_vec1 ` ({eucl_of_list rl .. eucl_of_list ru} \<times> set_of_lvivl' dRi))"
  by (rule solves_poincare_map_ncc[OF _ _ _
        empty_symstart_dres_nres_rel[unfolded empty_symstart_def op_empty_coll_def mk_coll_def]
         empty_symstart_flowsto,
    folded solves_poincare_map'_def, simplified])
    auto


definition "one_step_until_time_ivl_in_ivl X0 (t1::real) (t2::real) R dR =
  do {
    (X, CX) \<leftarrow> solve_one_step_until_timea X0 True t1 t2;
    ((l, u), X) \<leftarrow> scaleR2_rep X;
    CHECKs ''one_step_until_time_ivl_in_ivl: there should not be scaleR2'' (l = 1 \<and> u = 1);
    (l, u) \<leftarrow> ivl_rep R;
    CHECKs ''one_step_until_time_ivl_in_ivl: strange interval'' (l \<le> u);
    _ \<leftarrow> mk_safe (length ode_e) {l .. u};
    let _ = trace_set1 (ST ''final step to:'') (Some X);
    let _ = print_set1 False X;
    subset_spec1 X R dR
}"
sublocale autoref_op_pat_def one_step_until_time_ivl .

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
  by (autoref_monadic)
concrete_definition one_step_until_time_ivl_in_ivl_impl for X0i t1i t2i Ri dRi uses one_step_until_time_ivl_in_ivl_impl
lemmas one_step_until_time_ivl_in_ivl_impl_refine[autoref_rules] = one_step_until_time_ivl_in_ivl_impl.refine

lemma one_step_until_time_ivl_in_ivl_spec[le, refine_vcg]:
  "one_step_until_time_ivl_in_ivl (X0::'n::enum eucl1 set) t1 t2 R dR \<le> SPEC (\<lambda>b. b \<longrightarrow>
    (\<forall>(x0, d0) \<in> X0. {t1 .. t2} \<subseteq> existence_ivl0 x0 \<and>
      (\<forall>t \<in> {t1 .. t2}. (flow0 x0 t, Dflow x0 t o\<^sub>L d0) \<in> flow1_of_vec1 ` (R \<times> dR))))"
  if [simp]: "length ode_e = CARD('n::enum)"
  unfolding one_step_until_time_ivl_in_ivl_def
  apply (refine_vcg, clarsimp_all)
  subgoal for X CX Y CY CY' x0 d0
    apply (drule bspec, assumption, clarsimp)
    subgoal for t
      apply (drule bspec[where x=t], force)
      by (simp add: subset_iff )
    done
  done

definition "one_step_until_time_ivl_in_ivl_check X t0 t1 Ri dRi \<longleftrightarrow>
  one_step_until_time_ivl_in_ivl_impl X t0 t1 Ri dRi = dRETURN True"

theorem one_step_in_ivl_ncc:
  "t \<in> existence_ivl0 x0 \<and> (flow0 x0 t::'n rvec) \<in> R \<and> Dflow x0 t o\<^sub>L d0 \<in> dR"
  if ncc: "var.ncc_precond TYPE('n::enum rvec)" "var.ncc_precond TYPE('n vec1)"
   and t: "t \<in> {t0 .. t1}"
   and x0: "(x0, d0) \<in> c1_info_of_appre X"
   and invar: "c1_info_invare CARD('n) X"
   and R: "{eucl_of_list rl .. eucl_of_list ru} \<subseteq> R"
   and lens: "length rl = CARD('n)" "length ru = CARD('n)"
   and dRinvar: "lvivl'_invar (CARD('n)*CARD('n)) dRi"
   and dR: "blinfun_of_vmatrix ` set_of_lvivl' dRi \<subseteq> dR"
   and len_ode: "length ode_e = CARD('n)"
   and chk: "one_step_until_time_ivl_in_ivl_check X t0 t1 (rl, ru) dRi"
proof -
  have ivl: "((rl, ru), {eucl_of_list rl .. eucl_of_list ru::'n rvec}) \<in> \<langle>lv_rel\<rangle>ivl_rel"
    apply (rule lv_relivl_relI)
    using lens
    by auto
  from dRinvar have "lvivl'_invar DIM(((real, 'n) vec, 'n) vec) dRi" by simp
  note dRi = lvivl_default_relI[OF this]
  from one_step_until_time_ivl_in_ivl_impl_refine[OF ncc appr1e_relI[OF invar] IdI IdI ivl dRi, of t0 t1]
  have "nres_of (one_step_until_time_ivl_in_ivl_impl X t0 t1 (rl, ru) dRi)
    \<le> one_step_until_time_ivl_in_ivl (c1_info_of_appre X) t0 t1 {eucl_of_list rl::'n rvec..eucl_of_list ru} (set_of_lvivl' dRi)"
    by (auto simp: nres_rel_def)
  also note one_step_until_time_ivl_in_ivl_spec[OF len_ode order_refl]
  also have "one_step_until_time_ivl_in_ivl_impl X t0 t1 (rl, ru) dRi = dRETURN True"
    using chk
    by (auto simp: one_step_until_time_ivl_in_ivl_check_def split: dres.splits)
  finally show ?thesis
    using t R dR
    by (auto dest!: bspec[OF _ x0] bspec[where x=t] simp: vec1_of_flow1_def)
qed

end

end
