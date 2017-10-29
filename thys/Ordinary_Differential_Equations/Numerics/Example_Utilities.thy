theory Example_Utilities
imports
  Ordinary_Differential_Equations.ODE_Analysis
  Affine_Arithmetic.Print
  Refine_Rigorous_Numerics_Aform
  Transfer_Euclidean_Space_Vector
  Affine_Arithmetic.Float_Real
begin

declare [[ cd_patterns "_ = interpret_floatariths ?fas _" "_ = interpret_floatarith ?fa _"]]

concrete_definition reify_example for i j k uses reify_example


hide_const (open) Print.file_output
definition "file_output s f =
  (if s = String.implode ''''      then f (\<lambda>_. ())
  else if s = String.implode ''-'' then f print
  else                                  Print.file_output s f)"

definition "aforms_of_point xs = aforms_of_ivls xs xs"

definition "unit_matrix_list D = concat (map (\<lambda>i. map (\<lambda>j. if i = j then 1 else 0::real) [0..<D]) [0..<D])"

definition "with_unit_matrix D X = (fst X @ unit_matrix_list D, snd X @ unit_matrix_list D)"

definition "list_interval l u = {x. list_all2 op \<le> l x \<and> list_all2 op \<le> x u}"

context includes lifting_syntax begin
lemma list_interval_transfer[transfer_rule]:
  "((list_all2 A) ===> (list_all2 A) ===> rel_set (list_all2 A))
    list_interval list_interval"
  if [transfer_rule]: "(A ===> A ===> op =) op \<le> op \<le>" "bi_total A"
  unfolding list_interval_def
  by transfer_prover
end

lemma in_list_interval_lengthD: "x \<in> list_interval a b \<Longrightarrow> length x = length a"
  by (auto simp: list_interval_def list_all2_lengthD)


definition "varvec_fas' D C = ((map Var [0..<D]) @
      concat (map (\<lambda>b.
        (map (\<lambda>i. (Num (C i)) +
          Var (D + D * D) * (mvmult_fa D D (map Var [D..<D + D * D]) (map Num (replicate D 0[i:=1])) ! b)) [0..<D])) [0..<D]))"

definition "varvec_fas D C = ((map Var [0..<D]) @
      concat (map (\<lambda>i. (map (\<lambda>j. (Num (C i)) + Var (D + D * D) * Var (D + D * i + j)) [0..<D])) [0..<D]))"

lemma \<comment>\<open>for illustration\<close>
  assumes[simp]: "D=3" "rf = real_of_float"
  shows "interpret_floatariths (varvec_fas D (\<lambda>i. [a, b, c] ! i))
  [a, b, c, d11, d12, d13,
            d21, d22, d23,
            d31, d32, d33, 2] =
  [rf a, rf b, rf c,
  rf a + 2 * rf d11, rf a + 2 * rf d12, rf a + 2 * rf d13,
  rf b + 2 * rf d21, rf b + 2 * rf d22, rf b + 2 * rf d23,
  rf c + 2 * rf d31, rf c + 2 * rf d32, rf c + 2 * rf d33]"
  by (simp add: varvec_fas_def mvmult_fa_def eval_nat_numeral)

definition "vareq_projections
    n  (* dimension *)
    ps (* pairs of coordinates to project onto *)
    ds (* partial derivatives w.r.t. which variables *)
    cs (* (color) coding for partial derivatives *)
  =
  [(i + n * (x + 1)::nat, i + n * (y + 1), c). (i, c) \<leftarrow> zip ds cs, (x, y) \<leftarrow> ps]"

definition "varvec_aforms_line D X line =
  approx_floatariths
    30
    (varvec_fas D (\<lambda>i. float_of (fst (X ! i))))
    (take (D + D*D) X @ line)"

definition "varvec_aforms_head D X s = varvec_aforms_line D X (aforms_of_point [s])"
definition "varvec_aforms_vec D X s = varvec_aforms_line D (map (\<lambda>x. (fst x, zero_pdevs)) X) [aform_of_ivl 0 s]"

definition
  "shows_aforms_vareq
      n                (* dimension *)
      ps               (* pairs of coordinates to project onto *)
      ds               (* partial derivatives w.r.t. which variables *)
      csl              (* color coding for partial derivatives ('arrow' heads) *)
      csh              (* color coding for partial derivatives (lines) *)
      s                (* scale vectors for partial derivatives *)
      (no_str::string) (* default string if no C1 info is present *)
      X                (* affine form with C1 info *)
   =
    (case (varvec_aforms_head n X s, varvec_aforms_vec n X s) of (Some X, Some Y) \<Rightarrow>
        shows_sep (\<lambda>(x, y, c). shows_segments_of_aform x y X c) shows_nl (vareq_projections n ps ds csl) o shows_nl
      o shows_sep (\<lambda>(x, y, c). shows_segments_of_aform x y Y c) shows_nl (vareq_projections n ps ds csh) o shows_nl
    | _ \<Rightarrow> shows_string no_str o shows_nl)"

abbreviation "print_string s \<equiv> print (String.implode s)"
abbreviation "print_show s \<equiv> print_string (s '''')"

value [code] "print_show (shows_aforms_vareq 3 [(x, y). x \<leftarrow> [0..<3], y \<leftarrow> [0..<3], x < y]
  [0..<3] [''0x0000ff'', ''0x00ff00'', ''0xff0000''] [''0x0000ff'', ''0x00ff00'', ''0xff0000'']
  (FloatR 1 (-1)) ''# no C1 info''
    ((((\<lambda>(a, b). aforms_of_ivls a b) (with_unit_matrix 3 ([10, 20, 30], [12, 22, 32]))))))"

method_setup guess_rhs = \<open>
let
  fun compute ctxt var lhs =
    let
      val lhs' = Code_Evaluation.dynamic_value_strict ctxt lhs;
      val clhs' = Thm.cterm_of ctxt lhs';
      val inst = Thm.instantiate ([], [(var, clhs')]);
    in PRIMITIVE inst end;
  fun eval_schematic_rhs ctxt t = (case try (HOLogic.dest_eq o HOLogic.dest_Trueprop) t of
      SOME (lhs, Var var) => compute ctxt var lhs
    | _ => no_tac);
in
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD (HEADGOAL (SUBGOAL (fn (t, _) => eval_schematic_rhs ctxt t))))
end
\<close>

definition "true_form = Less (Num 0) (Num 1)"

lemma length_aforms_of_point[simp]: "length (aforms_of_point xs) = length xs"
  by (auto simp: aforms_of_point_def)

definition "aform2d_plot_segments x y a = shows_segments_of_aform x y a ''0x000000''"

lemma list_of_eucl_prod[simp]: "list_of_eucl (x, y) = list_of_eucl x @ list_of_eucl y"
  by (auto simp: list_of_eucl_def Basis_list_prod_def intro!: nth_equalityI)

lemma list_of_eucl_real[simp]: "list_of_eucl (x::real) = [x]"
  by (auto simp: list_of_eucl_def Basis_list_real_def)

lemma Joints_aforms_of_ivls_self[simp]: "xs \<in> Joints (aforms_of_ivls xs xs)"
  by (auto intro!: aforms_of_ivls)

lemma Joints_aforms_of_ivls_self_eq[simp]: "Joints (aforms_of_ivls xs xs) = {xs}"
  apply (auto )
  by (auto simp: aforms_of_ivls_def Joints_def valuate_def aform_val_def
      intro!: nth_equalityI)

lemma local_lipschitz_c1_euclideanI:
  fixes T::"real set" and X::"'a::euclidean_space set"
    and f::"real \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes f': "\<And>t x. t \<in> T \<Longrightarrow> x \<in> X \<Longrightarrow> (f t has_derivative f' t x) (at x)"
  assumes cont_f': "\<And>i. i \<in> Basis \<Longrightarrow> continuous_on (T \<times> X) (\<lambda>(t, x). f' t x i)"
  assumes "open T"
  assumes "open X"
  shows "local_lipschitz T X f"
  using assms
  apply (intro c1_implies_local_lipschitz[where f'="\<lambda>(t, x). Blinfun (f' t x)"])
     apply (auto simp: bounded_linear_Blinfun_apply has_derivative_bounded_linear split_beta'
      intro!: has_derivative_Blinfun continuous_on_blinfun_componentwise)
  apply (subst continuous_on_cong[OF refl]) defer apply assumption
  apply auto
  apply (subst bounded_linear_Blinfun_apply)
   apply (rule has_derivative_bounded_linear)
  by auto

lemma lipschitz_congI:
  assumes "lipschitz s' g' L'"
  assumes "s' = s"
  assumes "L' \<le> L"
  assumes "\<And>x y. x \<in> s \<Longrightarrow> g' x = g x"
  shows "lipschitz s g L"
  using assms
  by (auto simp: lipschitz_def intro!: order_trans[OF _ mult_right_mono[OF \<open>L' \<le> L\<close>]])

lemma local_lipschitz_congI:
  assumes "local_lipschitz s' t' g'"
  assumes "s' = s"
  assumes "t' = t"
  assumes "\<And>x y. x \<in> s \<Longrightarrow> y \<in> t \<Longrightarrow> g' x y = g x y"
  shows "local_lipschitz s t g"
proof -
  from assms have "local_lipschitz s t g'"
    by (auto simp: local_lipschitz_def)
  then show ?thesis
    apply (auto simp: local_lipschitz_def)
    apply (drule_tac bspec, assumption)
    apply (drule_tac bspec, assumption)
    apply auto
    subgoal for x y u L
    apply (rule exI[where x=u])
      apply (auto intro!: exI[where x=L])
      apply (drule bspec)
      apply simp
      apply (rule lipschitz_congI, assumption, rule refl, rule order_refl)
      using assms
      apply (auto)
      done
    done
qed

context ll_on_open_it\<comment>\<open>TODO: do this more generically for @{const ll_on_open_it}\<close>
begin

context fixes S Y g assumes cong: "X = Y" "T = S" "\<And>x t. x \<in> Y \<Longrightarrow> t \<in> S \<Longrightarrow> f t x = g t x"
begin

lemma ll_on_open_congI: "ll_on_open S g Y"
proof -
  interpret Y: ll_on_open_it S f Y t0
    apply (subst cong(1)[symmetric])
    apply (subst cong(2)[symmetric])
    by unfold_locales
  show ?thesis
    apply standard
    subgoal
      using local_lipschitz
      apply (rule local_lipschitz_congI)
      using cong by simp_all
    subgoal apply (subst continuous_on_cong) prefer 3 apply (rule cont)
      using cong by (auto)
    subgoal using open_domain by (auto simp: cong)
    subgoal using open_domain by (auto simp: cong)
    done
qed

lemma existence_ivl_subsetI:
  assumes t: "t \<in> existence_ivl t0 x0"
  shows "t \<in> ll_on_open.existence_ivl S g Y t0 x0"
proof -
  from assms have \<open>t0 \<in> T\<close> "x0 \<in> X"
    by (rule mem_existence_ivl_iv_defined)+
  interpret Y: ll_on_open S g Y by (rule ll_on_open_congI)
  have "(flow t0 x0 solves_ode f) (existence_ivl t0 x0) X"
    by (rule flow_solves_ode) (auto simp: \<open>x0 \<in> X\<close> \<open>t0 \<in> T\<close>)
  then have "(flow t0 x0 solves_ode f) {t0--t} X"
    by (rule solves_ode_on_subset)
     (auto simp add: t local.closed_segment_subset_existence_ivl)
  then have "(flow t0 x0 solves_ode g) {t0--t} Y"
    apply (rule solves_ode_congI)
       apply (auto intro!: assms cong)
    using \<open>(flow t0 x0 solves_ode f) {t0--t} X\<close> local.cong(1) solves_ode_domainD apply blast
    using \<open>t0 \<in> T\<close> assms closed_segment_subset_domainI general.mem_existence_ivl_subset local.cong(2)
    by blast
  then show ?thesis
    apply (rule Y.existence_ivl_maximal_segment)
    subgoal by (simp add: \<open>t0 \<in> T\<close> \<open>x0 \<in> X\<close>)
    apply (subst cong[symmetric])
    using \<open>t0 \<in> T\<close> assms closed_segment_subset_domainI general.mem_existence_ivl_subset local.cong(2)
    by blast
qed

lemma existence_ivl_cong:
  shows "existence_ivl t0 x0 = ll_on_open.existence_ivl S g Y t0 x0"
proof -
  interpret Y: ll_on_open S g Y by (rule ll_on_open_congI)
  show ?thesis
    apply (auto )
    subgoal by (rule existence_ivl_subsetI)
    subgoal
      apply (rule Y.existence_ivl_subsetI)
      using cong
      by auto
    done
qed

lemma flow_cong:
  assumes "t \<in> existence_ivl t0 x0"
  shows "flow t0 x0 t = ll_on_open.flow S g Y t0 x0 t"
proof -
  interpret Y: ll_on_open S g Y by (rule ll_on_open_congI)
  from assms have "t0 \<in> T" "x0 \<in> X"
    by (rule mem_existence_ivl_iv_defined)+
  from cong \<open>x0 \<in> X\<close> have "x0 \<in> Y" by auto
  from cong \<open>t0 \<in> T\<close> have "t0 \<in> S" by auto
  show ?thesis
    apply (rule Y.equals_flowI[where T'="existence_ivl t0 x0"])
    subgoal using \<open>t0 \<in> T\<close> \<open>x0 \<in> X\<close>  by auto
    subgoal using \<open>x0 \<in> X\<close> by auto
    subgoal by (auto simp: existence_ivl_cong \<open>x0 \<in> X\<close>)
    subgoal
      apply (rule solves_ode_congI)
          apply (rule flow_solves_ode[OF \<open>t0 \<in> T\<close> \<open>x0 \<in> X\<close>])
      using existence_ivl_subset[of x0]
      by (auto simp: cong(2)[symmetric] cong(1)[symmetric] assms flow_in_domain intro!: cong)
    subgoal using \<open>t0 \<in> S\<close> \<open>t0 \<in> T\<close> \<open>x0 \<in> X\<close> \<open>x0 \<in> Y\<close>
      by (auto simp:)
    subgoal by fact
    done
qed

end

end

context auto_ll_on_open begin

context fixes Y g assumes cong: "X = Y" "\<And>x t. x \<in> Y \<Longrightarrow> f x = g x"
begin

lemma auto_ll_on_open_congI: "auto_ll_on_open g Y"
  apply unfold_locales
  subgoal
    using local_lipschitz
    apply (rule local_lipschitz_congI)
    using cong by auto
  subgoal
    using open_domain
    using cong by auto
  done

lemma existence_ivl0_cong:
  shows "existence_ivl0 x0 = auto_ll_on_open.existence_ivl0 g Y x0"
proof -
  interpret Y: auto_ll_on_open g Y by (rule auto_ll_on_open_congI)
  show ?thesis
    unfolding Y.existence_ivl0_def
    apply (rule existence_ivl_cong)
    using cong by auto
qed

lemma flow0_cong:
  assumes "t \<in> existence_ivl0 x0"
  shows "flow0 x0 t = auto_ll_on_open.flow0 g Y x0 t"
proof -
  interpret Y: auto_ll_on_open g Y by (rule auto_ll_on_open_congI)
  show ?thesis
    unfolding Y.flow0_def
    apply (rule flow_cong)
    using cong assms by auto
qed

end

end


context c1_on_open_euclidean begin

context fixes Y g assumes cong: "X = Y" "\<And>x t. x \<in> Y \<Longrightarrow> f x = g x"
begin

lemma f'_cong: "(g has_derivative blinfun_apply (f' x)) (at x)" if "x \<in> Y"
proof -
  from derivative_rhs[of x] that cong
  have "(f has_derivative blinfun_apply (f' x)) (at x within Y)"
    by (auto intro!: has_derivative_at_within)
  then have "(g has_derivative blinfun_apply (f' x)) (at x within Y)"
    by (rule has_derivative_transform_within[OF _ zero_less_one that])
       (auto simp: cong)
  then show ?thesis
    using at_within_open[OF that] cong open_dom
    by (auto simp: )
qed

lemma c1_on_open_euclidean_congI: "c1_on_open_euclidean g f' Y"
proof -
  interpret Y: c1_on_open_euclidean f f' Y unfolding cong[symmetric] by unfold_locales
  show ?thesis
    apply standard
    subgoal using cong by simp
    subgoal by (rule f'_cong)
    subgoal by (simp add: cong[symmetric] continuous_derivative)
    done
qed

lemma vareq_cong: "vareq x0 t = c1_on_open_euclidean.vareq g f' Y x0 t"
  if "t \<in> existence_ivl0 x0"
proof -
  interpret Y: c1_on_open_euclidean g f' Y by (rule c1_on_open_euclidean_congI)
  show ?thesis
    unfolding vareq_def Y.vareq_def
    apply (rule arg_cong[where f=f'])
    apply (rule flow0_cong)
    using cong that by auto
qed

lemma Dflow_cong:
  assumes "t \<in> existence_ivl0 x0"
  shows "Dflow x0 t = c1_on_open_euclidean.Dflow g f' Y x0 t"
proof -
  interpret Y: c1_on_open_euclidean g f' Y by (rule c1_on_open_euclidean_congI)
  from assms have "x0 \<in> X"
    by (rule mem_existence_ivl_iv_defined)
  from cong \<open>x0 \<in> X\<close> have "x0 \<in> Y" by auto
  show ?thesis
    unfolding Dflow_def Y.Dflow_def
    apply (rule mvar.equals_flowI[symmetric, OF _ _ order_refl])
    subgoal using \<open>x0 \<in> X\<close> by auto
    subgoal using \<open>x0 \<in> X\<close> by auto
    subgoal
      apply (rule solves_ode_congI)
          apply (rule Y.mvar.flow_solves_ode)
           prefer 3 apply (rule refl)
      subgoal using \<open>x0 \<in> X\<close> \<open>x0 \<in> Y\<close> by auto
      subgoal using \<open>x0 \<in> X\<close> \<open>x0 \<in> Y\<close> by auto
      subgoal for t
        apply (subst vareq_cong)
         apply (subst (asm) Y.mvar_existence_ivl_eq_existence_ivl)
        subgoal using \<open>x0 \<in> Y\<close> by simp
        subgoal
          using cong
          by (subst (asm) existence_ivl0_cong[symmetric]) auto
        subgoal using \<open>x0 \<in> Y\<close> by simp
        done
      subgoal using \<open>x0 \<in> X\<close> \<open>x0 \<in> Y\<close>
        apply (subst mvar_existence_ivl_eq_existence_ivl)
        subgoal by simp
        apply (subst Y.mvar_existence_ivl_eq_existence_ivl)
        subgoal by simp
        using cong
        by (subst existence_ivl0_cong[symmetric]) auto
      subgoal by simp
      done
    subgoal using \<open>x0 \<in> X\<close> \<open>x0 \<in> Y\<close> by auto
    subgoal
      apply (subst mvar_existence_ivl_eq_existence_ivl)
       apply auto
       apply fact+
      done
    done
qed

lemma flowsto_congI1:
  assumes "flowsto A B C D"
  shows "c1_on_open_euclidean.flowsto g f' Y A B C D"
proof -
  interpret Y: c1_on_open_euclidean g f' Y by (rule c1_on_open_euclidean_congI)
  show ?thesis
    using assms
    unfolding flowsto_def Y.flowsto_def
    apply (auto simp: existence_ivl0_cong[OF cong]  flow0_cong[OF cong])
       apply (drule bspec, assumption)
    apply clarsimp
    apply (rule bexI)
    apply (rule conjI)
       apply assumption
    apply (subst flow0_cong[symmetric, OF cong])
     apply auto
      apply (subst existence_ivl0_cong[OF cong])
    apply auto
    apply (subst Dflow_cong[symmetric])
     apply auto
      apply (subst existence_ivl0_cong[OF cong])
    apply auto
    apply (drule bspec, assumption)
    apply (subst flow0_cong[symmetric, OF cong])
     apply auto
      apply (subst existence_ivl0_cong[OF cong])
    apply auto defer
    apply (subst Dflow_cong[symmetric])
     apply auto
      apply (subst existence_ivl0_cong[OF cong])
    apply auto
    apply (drule Y.closed_segment_subset_existence_ivl)
    by (auto simp: open_segment_real closed_segment_real split: if_splits)
qed

lemma flowsto_congI2:
  assumes "c1_on_open_euclidean.flowsto g f' Y A B C D"
  shows "flowsto A B C D"
proof -
  interpret Y: c1_on_open_euclidean g f' Y by (rule c1_on_open_euclidean_congI)
  show ?thesis
    apply (rule Y.flowsto_congI1)
    using assms
    by (auto simp: cong)
qed

lemma flowsto_congI: "flowsto A B C D = c1_on_open_euclidean.flowsto g f' Y A B C D"
  using flowsto_congI1[of A B C D] flowsto_congI2[of A B C D] by auto

lemma
  returns_to_congI1:
  assumes "returns_to A x"
  shows "auto_ll_on_open.returns_to g Y A x"
proof -
  interpret Y: c1_on_open_euclidean g f' Y by (rule c1_on_open_euclidean_congI)
  from assms obtain t where t:
    "\<forall>\<^sub>F t in at_right 0. flow0 x t \<notin> A"
    "0 < t" "t \<in> existence_ivl0 x" "flow0 x t \<in> A"
    by (auto simp: returns_to_def)

  note t(1)
  moreover
  have "\<forall>\<^sub>F s in at_right 0. s < t"
    using tendsto_ident_at \<open>0 < t\<close>
    by (rule order_tendstoD)
  moreover have "\<forall>\<^sub>F s in at_right 0. 0 < s"
    by (auto simp: eventually_at_topological)
  ultimately have "\<forall>\<^sub>F t in at_right 0. Y.flow0 x t \<notin> A"
    apply eventually_elim
    using ivl_subset_existence_ivl[OF \<open>t \<in> _\<close>]
    apply (subst (asm) flow0_cong[OF cong])
    by (auto simp: )

  moreover have "\<exists>t>0. t \<in> Y.existence_ivl0 x \<and> Y.flow0 x t \<in> A"
    using t
    by (auto intro!: exI[where x=t] simp: flow0_cong[OF cong] existence_ivl0_cong[OF cong])
  ultimately show ?thesis
    by (auto simp: Y.returns_to_def)
qed

lemma
  returns_to_congI2:
  assumes "auto_ll_on_open.returns_to g Y x A"
  shows "returns_to x A"
proof -
  interpret Y: c1_on_open_euclidean g f' Y by (rule c1_on_open_euclidean_congI)
  show ?thesis
    by (rule Y.returns_to_congI1) (auto simp: assms cong)
qed

lemma returns_to_cong: "auto_ll_on_open.returns_to g Y A x = returns_to A x"
  using returns_to_congI1 returns_to_congI2 by blast

lemma
  return_time_cong:
  shows "return_time A x = auto_ll_on_open.return_time g Y A x"
proof -
  interpret Y: c1_on_open_euclidean g f' Y by (rule c1_on_open_euclidean_congI)
  have P_eq: "0 < t \<and> t \<in> existence_ivl0 x \<and> flow0 x t \<in> A \<and> (\<forall>s\<in>{0<..<t}. flow0 x s \<notin> A) \<longleftrightarrow>
    0 < t \<and> t \<in> Y.existence_ivl0 x \<and> Y.flow0 x t \<in> A \<and> (\<forall>s\<in>{0<..<t}. Y.flow0 x s \<notin> A)"
    for t
    using ivl_subset_existence_ivl[of t x]
    apply (auto simp: existence_ivl0_cong[OF cong] flow0_cong[OF cong])
     apply (drule bspec)
      apply force
     apply (subst (asm) flow0_cong[OF cong])
    apply auto
    apply (auto simp: existence_ivl0_cong[OF cong, symmetric] flow0_cong[OF cong])
     apply (subst (asm) flow0_cong[OF cong])
    apply auto
    done
  show ?thesis
    unfolding return_time_def Y.return_time_def
    by (auto simp: returns_to_cong P_eq)
qed

lemma poincare_mapsto_congI1:
  assumes "poincare_mapsto A B C D E" "closed A"
  shows "c1_on_open_euclidean.poincare_mapsto g Y A B C D E"
proof -
  interpret Y: c1_on_open_euclidean g f' Y by (rule c1_on_open_euclidean_congI)
  show ?thesis
    using assms
    unfolding poincare_mapsto_def Y.poincare_mapsto_def
    apply auto
    subgoal for a b
      by (rule returns_to_congI1) auto
    subgoal for a b
      by (subst return_time_cong[abs_def, symmetric]) auto
    subgoal for a b
      unfolding poincare_map_def Y.poincare_map_def
      apply (drule bspec, assumption)
      apply safe
      subgoal for D
        apply (auto intro!: exI[where x=D])
        subgoal premises prems
        proof -
          have "\<forall>\<^sub>F y in at a within C. returns_to A y"
            apply (rule eventually_returns_to_continuousI)
              apply fact apply fact
            apply (rule differentiable_imp_continuous_within)
            apply fact
            done
          moreover have "\<forall>\<^sub>F y in at a within C. y \<in> C"
            by (auto simp: eventually_at_filter)
          ultimately have "\<forall>\<^sub>F x' in at a within C. flow0 x' (return_time A x') = Y.flow0 x' (Y.return_time A x')"
          proof eventually_elim
            case (elim x')
            then show ?case
              apply (subst flow0_cong[OF cong, symmetric], force)
               apply (subst return_time_cong[symmetric])
              using prems
               apply (auto intro!: return_time_exivl)
              apply (subst return_time_cong[symmetric])
              apply auto
              done
          qed
          with prems(7)
          show ?thesis
            apply (rule has_derivative_transform_eventually)
            using prems
             apply (subst flow0_cong[OF cong, symmetric], force)
              apply (subst return_time_cong[symmetric])
            using prems
              apply (auto intro!: return_time_exivl)
            apply (subst return_time_cong[symmetric])
            apply auto
            done
        qed
        subgoal
          apply (subst flow0_cong[OF cong, symmetric], force)
           apply (subst return_time_cong[symmetric])
           apply (auto intro!: return_time_exivl)
          apply (subst return_time_cong[symmetric])
          apply auto
          done
        done
      done
    subgoal for a b t
      apply (drule bspec, assumption)
      apply (subst flow0_cong[OF cong, symmetric])
        apply auto
       apply (subst (asm) return_time_cong[symmetric])
       apply (rule less_return_time_imp_exivl)
          apply (rule less_imp_le, assumption)
         apply (auto simp: return_time_cong)
      done
    done
qed

lemma poincare_mapsto_congI2:
  assumes "c1_on_open_euclidean.poincare_mapsto g Y A B C D E" "closed A"
  shows "poincare_mapsto A B C D E"
proof -
  interpret Y: c1_on_open_euclidean g f' Y by (rule c1_on_open_euclidean_congI)
  show ?thesis
    apply (rule Y.poincare_mapsto_congI1)
    using assms
    by (auto simp: cong)
qed

lemma poincare_mapsto_cong: "closed A \<Longrightarrow>
    poincare_mapsto A B C D E = c1_on_open_euclidean.poincare_mapsto g Y A B C D E"
  using poincare_mapsto_congI1[of A B C] poincare_mapsto_congI2[of A B C] by auto

end

end

definition "list_aform_of_aform (x::real aform) = (fst x, list_of_pdevs (snd x))"
primrec split_aforms_list:: "(real aform) list list
   \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (real aform) list list" where
  "split_aforms_list Xs i 0 = Xs"
| "split_aforms_list Xs i (Suc n) = split_aforms_list (concat (map (\<lambda>x. (let (a, b) = split_aforms x i in [a, b])) Xs)) i n"

definition "shows_aforms x y c X = shows_lines (map (\<lambda>b. (shows_segments_of_aform x y b c ''\<newline>'')) X)"

locale ode_interpretation =
  fixes safe_form and safe_set::"'a::executable_euclidean_space set" and ode_fas and ode::"'a \<Rightarrow> 'a"
    and finite::"'n::enum"
  assumes dims: "DIM('a) = CARD('n)"
  assumes safe_set: "safe_set = aform.Csafe ode_fas safe_form"
  assumes ode: "\<And>x. x \<in> safe_set \<Longrightarrow> ode x = aform.ode ode_fas x"
begin

sublocale auto_ll_on_open ode safe_set
  by (rule aform.auto_ll_on_open_congI[OF safe_set[symmetric] ode[symmetric]]) simp

lemma ode_has_derivative_ode_d1: "(ode has_derivative blinfun_apply (aform.ode_d1 ode_fas safe_form x)) (at x)"
  if "x \<in> safe_set" for x
proof -
  from aform.fderiv[OF that[unfolded safe_set]]
  have "(aform.ode ode_fas has_derivative blinfun_apply (aform.ode_d1 ode_fas safe_form x)) (at x)"
    by simp
  moreover
  from topological_tendstoD[OF tendsto_ident_at open_domain(2) that] 
  have "\<forall>\<^sub>F x' in at x. x' \<in> safe_set" .
  then have "\<forall>\<^sub>F x' in at x. aform.ode ode_fas x' = ode x'"
    by eventually_elim (auto simp: ode)
  ultimately show ?thesis
    by (rule has_derivative_transform_eventually) (auto simp: ode that)
qed

sublocale c1_on_open_euclidean ode "aform.ode_d1 ode_fas safe_form" safe_set
  apply unfold_locales
  subgoal by simp
  subgoal by (simp add: ode_has_derivative_ode_d1)
  subgoal by (rule aform.cont_fderiv') (auto intro!: continuous_intros simp: safe_set)
  done

sublocale transfer_eucl_vec for a::'a and n::'n
  by unfold_locales (simp add: dims)

lemma flow_eq: "t \<in> existence_ivl0 x \<Longrightarrow> aform.flow0 ode_fas safe_form x t = flow0 x t"
  and Dflow_eq: "t \<in> existence_ivl0 x \<Longrightarrow> aform.Dflow ode_fas safe_form x t = Dflow x t"
  and ex_ivl_eq: "t \<in> aform.existence_ivl0 ode_fas safe_form x \<Longrightarrow> aform.existence_ivl0 ode_fas safe_form x = existence_ivl0 x"
  and poincare_mapsto_eq: "closed a \<Longrightarrow> aform.poincare_mapsto ode_fas safe_form a b c d e = poincare_mapsto a b c d e"
  and flowsto_eq: "aform.flowsto ode_fas safe_form = flowsto"
      apply -
  subgoal by (rule flow0_cong[symmetric]) (auto simp: safe_set ode)
  subgoal by (rule Dflow_cong[symmetric]) (auto simp: safe_set ode)
  subgoal by (rule existence_ivl0_cong[symmetric]) (auto simp: safe_set ode)
  subgoal
    apply (subst aform.poincare_mapsto_cong[OF safe_set[symmetric]])
    by (auto simp: ode)
  subgoal
    apply (intro ext)
    apply (subst flowsto_congI[OF safe_set ode])
    by (auto simp: safe_set)
  done

definition "avf \<equiv> \<lambda>x::'n rvec. cast (aform.ode ode_fas (cast x)::'a)::'n rvec"

context includes lifting_syntax begin
lemma aform_ode_transfer[transfer_rule]: "(list_all2 op = ===> rel_ve ===> rel_ve) aform.ode aform.ode"
  unfolding aform.ode_def
  by transfer_prover
lemma cast_aform_ode: "cast (aform.ode ode_fas (cast (x::'n rvec))::'a) = aform.ode ode_fas x"
  by transfer simp

lemma aform_safe_transfer[transfer_rule]: "(list_all2 op = ===> op = ===> rel_ve ===> op =) aform.safe aform.safe"
  unfolding aform.safe_def
  by transfer_prover

lemma aform_Csafe_transfer[transfer_rule]: "(list_all2 op = ===> op = ===> rel_set rel_ve) aform.Csafe aform.Csafe"
  unfolding aform.Csafe_def
  by transfer_prover

lemma cast_safe_set: "(cast ` safe_set::'n rvec set) = aform.Csafe ode_fas safe_form"
  unfolding safe_set
  by transfer simp

lemma aform_ode_d_raw_transfer[transfer_rule]:
  "(list_all2 op = ===> op = ===> rel_ve ===> rel_ve ===> rel_ve ===> rel_ve) aform.ode_d_raw aform.ode_d_raw"
  unfolding aform.ode_d_raw_def
  by transfer_prover

lemma
  aform_ode_d_raw_aux_transfer:
  "(list_all2 op = ===> op = ===> rel_ve ===> rel_ve ===> rel_ve)
    (\<lambda>x ya xb xa. if xb \<in> aform.Csafe x ya then aform.ode_d_raw x 0 xb 0 xa else 0)
    (\<lambda>x ya xb xa. if xb \<in> aform.Csafe x ya then aform.ode_d_raw x 0 xb 0 xa else 0)"
  by transfer_prover

lemma aform_ode_d1_transfer[transfer_rule]:
  "(list_all2 op = ===> op = ===> rel_ve ===> rel_blinfun rel_ve rel_ve) aform.ode_d1 aform.ode_d1"
  apply (auto simp: rel_blinfun_def aform.ode_d1_def intro!: rel_funI)
  unfolding aform.ode_d.rep_eq
  using aform_ode_d_raw_aux_transfer
  apply (drule rel_funD)
  apply (drule rel_funD, rule refl)
  apply (drule rel_funD, assumption)
  apply (drule rel_funD; assumption)
  done

lemma cast_bl_transfer[transfer_rule]:
  "(rel_blinfun op = op = ===> rel_blinfun rel_ve rel_ve) id_blinfun cast_bl"
  by (auto simp: rel_ve_cast rel_blinfun_def intro!: rel_funI dest!: rel_funD)
lemma cast_bl_transfer'[transfer_rule]:
  "(rel_blinfun rel_ve rel_ve ===> rel_blinfun op = op =) id_blinfun cast_bl"
  apply (auto simp: rel_ve_cast rel_blinfun_def cast_cast intro!: rel_funI dest!: rel_funD)
  by (subst cast_cast) auto

lemma rel_blinfun_eq[relator_eq]: "rel_blinfun op = op = = op ="
  by (auto simp: Rel_def rel_blinfun_def blinfun_ext rel_fun_eq intro!: rel_funI ext)

lemma cast_aform_ode_D1:
  "cast_bl (aform.ode_d1 ode_fas safe_form (cast (x::'n rvec))::'a\<Rightarrow>\<^sub>L'a) =
    (aform.ode_d1 ode_fas safe_form x::'n rvec \<Rightarrow>\<^sub>L 'n rvec)"
  by transfer simp

end

definition "vf \<equiv> \<lambda>x. cast (ode (cast x))"
definition "vf' \<equiv> \<lambda>x::'n rvec. cast_bl (aform.ode_d1 ode_fas safe_form (cast x::'a))
  ::'n rvec \<Rightarrow>\<^sub>L 'n rvec"
definition "vX \<equiv> cast ` safe_set"
sublocale a?: transfer_c1_on_open_euclidean a n ode "aform.ode_d1 ode_fas safe_form" safe_set vf vf' vX
  for a::'a and n::'n
  by unfold_locales
    (simp_all add: dims vf_def vf'_def vX_def)

sublocale av: transfer_c1_on_open_euclidean a n "aform.ode ode_fas" "aform.ode_d1 ode_fas safe_form"
  "(aform.Csafe ode_fas safe_form)" avf vf' vX
  for a::'a and n::'n
     apply unfold_locales
  unfolding vX_def
  by (simp_all add: dims avf_def  safe_set)

lemma vflow_eq: "t \<in> v.existence_ivl0 x \<Longrightarrow> aform.flow0 ode_fas safe_form x t = v.flow0 x t"
  thm flow_eq[of t "cast x"] flow_eq[of t "cast x", untransferred]
  apply (subst flow_eq[of t "cast x", untransferred, symmetric])
   apply simp
  unfolding avf_def vX_def cast_aform_ode cast_safe_set
  ..

lemma vf'_eq: "vf' = aform.ode_d1 ode_fas safe_form"
  unfolding vf'_def cast_aform_ode_D1 ..

lemma vDflow_eq: "t \<in> v.existence_ivl0 x \<Longrightarrow> aform.Dflow ode_fas safe_form x t = v.Dflow x t"
  apply (subst Dflow_eq[of t "cast x", untransferred, symmetric])
   apply simp
  unfolding avf_def vX_def cast_aform_ode cast_safe_set vf'_eq
  ..

lemma vex_ivl_eq: "t \<in> aform.existence_ivl0 ode_fas safe_form x \<Longrightarrow> aform.existence_ivl0 ode_fas safe_form x = v.existence_ivl0 x"
  apply (subst ex_ivl_eq[of t "cast x", untransferred, symmetric])
  unfolding avf_def vX_def cast_aform_ode cast_safe_set vf'_eq
  by auto

context includes lifting_syntax begin
lemma id_cast_eucl1_transfer_eq: "(\<lambda>x. x) = (\<lambda>x. (fst x, 1\<^sub>L o\<^sub>L snd x o\<^sub>L 1\<^sub>L))"
  by auto
lemma cast_eucl1_transfer[transfer_rule]:
  "(rel_prod op = (rel_blinfun op = op =) ===> rel_prod rel_ve (rel_blinfun rel_ve rel_ve)) (\<lambda>x. x) cast_eucl1"
  unfolding cast_eucl1_def id_cast_eucl1_transfer_eq
  apply transfer_prover_start
       apply (transfer_step)
      apply (transfer_step)
     apply (transfer_step)
    apply (transfer_step)
   apply (transfer_step)
  apply simp
  done

end

lemma avpoincare_mapsto_eq:
  "aform.poincare_mapsto ode_fas safe_form a (b::'n eucl1 set) c d e = av.v.poincare_mapsto a b c d e"
  if "closed a"
  unfolding avf_def vX_def cast_aform_ode cast_safe_set vf'_eq
  by auto

lemma vpoincare_mapsto_eq:
  "aform.poincare_mapsto ode_fas safe_form a (b::'n eucl1 set) c d e = v.poincare_mapsto a b c d e"
  if "closed a"
proof -
  have "closed (cast ` a::'a set)" using that
    by transfer auto
  from poincare_mapsto_eq[of "cast ` a::'a set"
      "cast_eucl1 ` b::('a \<times> 'a \<Rightarrow>\<^sub>L 'a) set"
      "cast ` c::'a set" "cast ` d::'a set" "cast_eucl1 ` e::('a \<times> 'a \<Rightarrow>\<^sub>L 'a) set", OF this, untransferred]
  have "v.poincare_mapsto a b c d e = av.v.poincare_mapsto a b c d e"
    by auto
  also have "\<dots> = aform.poincare_mapsto ode_fas safe_form a (b::'n eucl1 set) c d e"
    unfolding avf_def vX_def cast_aform_ode cast_safe_set vf'_eq
    by auto
  finally show ?thesis by simp
qed

lemma avflowsto_eq: "aform.flowsto ode_fas safe_form = (av.v.flowsto::'n eucl1 set \<Rightarrow> _)"
proof (intro ext, goal_cases)
  case (1 a b c d)
  have "av.v.flowsto a b c d = aform.flowsto ode_fas safe_form a b c d"
    unfolding avf_def vX_def cast_aform_ode cast_safe_set vf'_eq
    by auto
  then show ?case by simp
qed

lemma vflowsto_eq: "aform.flowsto ode_fas safe_form = (v.flowsto::'n eucl1 set \<Rightarrow> _)"
proof (intro ext, goal_cases)
  case (1 a b c d)
  have "aform.flowsto ode_fas safe_form (cast_eucl1 ` a::'a c1_info set) b
    (cast_eucl1 ` c)  (cast_eucl1 ` d) =
    flowsto (cast_eucl1 ` a::'a c1_info set) b (cast_eucl1 ` c)  (cast_eucl1 ` d)"
    by (subst flowsto_eq) auto
  from this[untransferred] have "v.flowsto a b c d = av.v.flowsto a b c d" by auto
  also have "\<dots> = aform.flowsto ode_fas safe_form a b c d"
    unfolding avf_def vX_def cast_aform_ode cast_safe_set vf'_eq
    by auto
  finally show ?case by simp
qed

context includes lifting_syntax begin
lemma flow1_of_list_transfer[transfer_rule]:
  "(list_all2 op = ===> rel_prod rel_ve (rel_blinfun rel_ve rel_ve))
   flow1_of_list flow1_of_list"
  unfolding flow1_of_list_def blinfun_of_list_def o_def flow1_of_vec1_def
  by transfer_prover

lemma c1_info_of_appr_transfer[transfer_rule]:
  "(rel_prod (list_all2 op =) (rel_option (list_all2 op =)) ===> rel_set (rel_prod rel_ve (rel_blinfun rel_ve rel_ve)))
    aform.c1_info_of_appr
    aform.c1_info_of_appr"
  unfolding aform.c1_info_of_appr_def
  by transfer_prover

lemma c0_info_of_appr_transfer[transfer_rule]:
  "((list_all2 op =) ===> rel_set rel_ve) aform.c0_info_of_appr aform.c0_info_of_appr"
  unfolding aform.c0_info_of_appr_def
  by transfer_prover

lemma aform_scaleR2_transfer[transfer_rule]:
  "(op = ===> op = ===> rel_set (rel_prod A B) ===> rel_set (rel_prod A B))
    scaleR2 scaleR2"
  if [unfolded Rel_def, transfer_rule]: "(op = ===> B ===> B) op *\<^sub>R op *\<^sub>R"
  unfolding scaleR2_def
  by transfer_prover
lemma scaleR_rel_blinfun_transfer[transfer_rule]: "(op = ===> rel_blinfun rel_ve rel_ve ===> rel_blinfun rel_ve rel_ve) op *\<^sub>R op *\<^sub>R"
  apply (auto intro!: rel_funI simp: rel_blinfun_def blinfun.bilinear_simps)
  apply (drule rel_funD)
   apply assumption
  apply (rule scaleR_transfer[THEN rel_funD, THEN rel_funD])
   apply auto
  done
lemma c1_info_of_appre_transfer[transfer_rule]:
  "(rel_prod (rel_prod op = op =) (rel_prod (list_all2 op =) (rel_option (list_all2 op =))) ===>
      rel_set (rel_prod rel_ve (rel_blinfun rel_ve rel_ve)))
    aform.c1_info_of_appre
    aform.c1_info_of_appre"
  unfolding aform.c1_info_of_appre_def
  by transfer_prover

lemma c1_info_of_apprs_transfer[transfer_rule]:
  "(op = ===> rel_set (rel_prod rel_ve (rel_blinfun rel_ve rel_ve)))
    aform.c1_info_of_apprs
    aform.c1_info_of_apprs"
  unfolding aform.c1_info_of_apprs_def
  by transfer_prover
lemma c1_info_of_appr'_transfer[transfer_rule]:
  "(rel_option (list_all2 op =) ===> rel_set (rel_prod rel_ve (rel_blinfun rel_ve rel_ve)))
    aform.c1_info_of_appr' aform.c1_info_of_appr'"
  unfolding aform.c1_info_of_appr'_def
  by transfer_prover

lemma c0_info_of_apprs_transfer[transfer_rule]:
  "(op = ===> rel_set rel_ve)
    aform.c0_info_of_apprs
    aform.c0_info_of_apprs"
  unfolding aform.c0_info_of_apprs_def
  by transfer_prover
lemma c0_info_of_appr'_transfer[transfer_rule]:
  "(rel_option (list_all2 op =) ===> rel_set rel_ve)
    aform.c0_info_of_appr' aform.c0_info_of_appr'"
  unfolding aform.c0_info_of_appr'_def
  by transfer_prover

lemma aform_Csafe_vX[simp]: "aform.Csafe ode_fas safe_form = (vX::'n rvec set)"
  by (simp add: vX_def cast_safe_set)

definition blinfuns_of_lvivl::"real list \<times> real list \<Rightarrow> ('b \<Rightarrow>\<^sub>L 'b::executable_euclidean_space) set"
  where "blinfuns_of_lvivl x = blinfun_of_list ` list_interval (fst x) (snd x)"

lemma blinfun_of_list_transfer[transfer_rule]:
  "(list_all2 op = ===> rel_blinfun rel_ve rel_ve) blinfun_of_list blinfun_of_list"
  unfolding blinfun_of_list_def
  by transfer_prover

lemma blinfuns_of_lvivl_transfer[transfer_rule]:
  "(rel_prod (list_all2 op =) (list_all2 op =) ===> rel_set (rel_blinfun rel_ve rel_ve))
    blinfuns_of_lvivl
    blinfuns_of_lvivl"
  unfolding blinfuns_of_lvivl_def
  by transfer_prover

definition "blinfuns_of_lvivl' x = (case x of None \<Rightarrow> UNIV | Some x \<Rightarrow> blinfuns_of_lvivl x)"

lemma blinfuns_of_lvivl'_transfer[transfer_rule]:
  "(rel_option (rel_prod (list_all2 op =) (list_all2 op =)) ===> rel_set (rel_blinfun rel_ve rel_ve))
    blinfuns_of_lvivl'
    blinfuns_of_lvivl'"
  unfolding blinfuns_of_lvivl'_def
  by transfer_prover


lemma atLeastAtMost_transfer[transfer_rule]:
  "(A ===> A ===> rel_set A) atLeastAtMost atLeastAtMost"
  if [transfer_rule]: "(A ===> A ===> op =) op \<le> op \<le>" "bi_total A" "bi_unique A"
  unfolding atLeastAtMost_def atLeast_def atMost_def
  by transfer_prover

lemma set_of_ivl_transfer[transfer_rule]:
  "(rel_prod A A ===> rel_set A) set_of_ivl set_of_ivl"
  if [transfer_rule]: "(A ===> A ===> op =) op \<le> op \<le>" "bi_total A" "bi_unique A"
  unfolding set_of_ivl_def
  by transfer_prover

lemma set_of_lvivl_transfer[transfer_rule]:
  "(rel_prod (list_all2 op =) (list_all2 op =) ===> rel_set rel_ve) set_of_lvivl set_of_lvivl"
  unfolding set_of_lvivl_def
  by transfer_prover

lemma set_of_lvivl_eq: "set_of_lvivl I =
    (eucl_of_list ` list_interval (fst I) (snd I)::'b::executable_euclidean_space set)"
  if [simp]: "length (fst I) = DIM('b)" "length (snd I) = DIM('b)"
proof (auto simp: set_of_lvivl_def list_interval_def set_of_ivl_def, goal_cases)
  case (1 x)
  with lv_rel_le[where 'a='b, param_fo, OF lv_relI lv_relI, of  "fst I" "list_of_eucl x"]
    lv_rel_le[where 'a='b, param_fo, OF lv_relI lv_relI, of "list_of_eucl x" "snd I"]
  show ?case by force
next
  case (2 x)
  with lv_rel_le[where 'a='b, param_fo, OF lv_relI lv_relI, of  "fst I" "x"]
  show ?case by (auto simp: list_all2_lengthD)
next
  case (3 x)
  with lv_rel_le[where 'a='b, param_fo, OF lv_relI lv_relI, of "x" "snd I"]
  show ?case by (auto simp: list_all2_lengthD)
qed

lemma bounded_linear_matrix_vector_mul[THEN bounded_linear_compose, bounded_linear_intros]:
  "bounded_linear (op *v x)" for x::"real^'x^'y"
  unfolding linear_linear
  by (rule matrix_vector_mul_linear)

lemma blinfun_of_list_eq: "blinfun_of_list x = blinfun_of_vmatrix (eucl_of_list x::((real, 'b) vec, 'b) vec)"
  if "length x = CARD('b::enum)*CARD('b)"
  unfolding blinfun_of_list_def
  apply (transfer fixing: x)
  apply (rule linear_eq_stdbasis)
  unfolding linear_conv_bounded_linear
    apply (auto intro!: bounded_linear_intros)
proof goal_cases
  case (1 b)
  have "(eucl_of_list x::((real, 'b) vec, 'b) vec) *v b = (eucl_of_list x::((real, 'b) vec, 'b) vec) *v eucl_of_list (list_of_eucl b)"
    by simp
  also have "\<dots> = (\<Sum>i<CARD('b).
        (\<Sum>j<CARD('b). x ! (i * CARD('b) + j) * (b \<bullet> Basis_list ! j)) *\<^sub>R Basis_list ! i)"
    by (subst eucl_of_list_matrix_vector_mult_eq_sum_nth_Basis_list)
      (auto simp: that)
  also have "\<dots> = (\<Sum>i\<in>Basis.
       \<Sum>j\<in>Basis. (b \<bullet> j * x ! (index Basis_list i * CARD('b) + index Basis_list j)) *\<^sub>R i)"
    apply (subst sum_list_Basis_list[symmetric])+
    apply (subst sum_list_sum_nth)+
    by (auto simp add: atLeast0LessThan scaleR_sum_left intro!: sum.cong)
  finally show ?case by simp
qed

lemma blinfuns_of_lvivl_eq: "blinfuns_of_lvivl x =
    (blinfun_of_vmatrix ` set_of_lvivl x::((real, 'b) vec \<Rightarrow>\<^sub>L (real, 'b) vec) set)"
  if "length (fst x) = CARD('b::enum)*CARD('b)" "length (snd x) = CARD('b)*CARD('b)"
  apply (subst set_of_lvivl_eq)
  subgoal by (simp add: that)
  subgoal by (simp add: that)
  unfolding blinfuns_of_lvivl_def image_image
  by (auto simp: that blinfun_of_list_eq[symmetric] in_list_interval_lengthD cong: image_cong)

lemma range_blinfun_of_vmatrix[simp]: "range blinfun_of_vmatrix = UNIV"
  apply auto
  apply transfer
  subgoal for x
    unfolding linear_linear
    by (auto intro!: matrix_works[symmetric])
  done

lemma blinfun_of_vmatrix_image:
  "blinfun_of_vmatrix ` aform.set_of_lvivl' x =
    (blinfuns_of_lvivl' x::((real, 'b) vec \<Rightarrow>\<^sub>L (real, 'b) vec) set)"
  if "aform.lvivl'_invar (CARD('b)*CARD('b::enum)) x"
  using that
  by (auto simp: aform.set_of_lvivl'_def blinfuns_of_lvivl'_def blinfuns_of_lvivl_eq 
    aform.lvivl'_invar_def
      split: option.splits)

lemma one_step_result123:
  "solves_one_step_until_time_aform optns ode_fas safe_form X0i t1 t2 E dE \<Longrightarrow>
    (x0, d0) \<in> aform.c1_info_of_appre X0i \<Longrightarrow>
    t \<in> {t1 .. t2} \<Longrightarrow>
    set_of_lvivl E \<subseteq> S \<Longrightarrow>
    blinfuns_of_lvivl' dE \<subseteq> dS \<Longrightarrow>
    length (fst E) = CARD('n) \<Longrightarrow> length (snd E) = CARD('n) \<Longrightarrow>
    aform.lvivl'_invar (CARD('n) * CARD('n)) dE \<Longrightarrow>
    aform.c1_info_invare DIM('a) X0i \<Longrightarrow>
    length ode_fas = DIM('a) \<Longrightarrow>
      (t \<in> existence_ivl0 (x0::'a) \<and> flow0 x0 t \<in> S) \<and> Dflow x0 t o\<^sub>L d0 \<in> dS"
  apply (transfer fixing: optns ode_fas safe_form X0i t1 t2 t E dE)
  subgoal premises prems for x0 d0 S dS
  proof -
    have "t \<in> aform.existence_ivl0 ode_fas safe_form x0 \<and> aform.flow0 ode_fas safe_form x0 t \<in> S \<and> aform.Dflow ode_fas safe_form x0 t o\<^sub>L d0 \<in> dS"
      apply (rule aform.one_step_in_ivl[of t t1 t2 x0 d0 X0i "fst E" "snd E" S dE dS ode_fas optns safe_form])
      using prems
      by (auto simp: eucl_of_list_prod set_of_lvivl_def set_of_ivl_def blinfun_of_vmatrix_image)
    with vflow_eq[of t x0] vDflow_eq[of t x0] vex_ivl_eq[symmetric, of t x0] 
    show ?thesis
      by simp
  qed
  done

lemmas one_step_result12 = one_step_result123[THEN conjunct1]
  and one_step_result3 = one_step_result123[THEN conjunct2]
lemmas one_step_result1 = one_step_result12[THEN conjunct1]
  and one_step_result2 = one_step_result12[THEN conjunct2]

lemma plane_of_transfer[transfer_rule]: "(rel_sctn A ===> rel_set A) plane_of plane_of"
  if [transfer_rule]: "(A ===> A ===> op =) op \<bullet> op \<bullet>" "bi_total A"
  unfolding plane_of_def
  by transfer_prover

lemma below_halfspace_transfer[transfer_rule]: "(rel_sctn A ===> rel_set A) below_halfspace below_halfspace"
  if [transfer_rule]: "(A ===> A ===> op =) op \<bullet> op \<bullet>" "bi_total A"
  unfolding below_halfspace_def le_halfspace_def
  by transfer_prover

definition "rel_nres A a b \<longleftrightarrow> (a, b) \<in> \<langle>{(a, b). A a b}\<rangle>nres_rel"

lemma FAILi_transfer[transfer_rule]: "(rel_nres B) FAILi FAILi"
  by (auto simp: rel_nres_def nres_rel_def)

lemma RES_transfer[transfer_rule]: "(rel_set B ===> rel_nres B) RES RES"
  by (auto simp: rel_nres_def nres_rel_def rel_set_def intro!: rel_funI RES_refine)

context begin interpretation autoref_syn .
lemma RETURN_dres_nres_relI:
  "(fi, f) \<in> A \<rightarrow> B \<Longrightarrow> (\<lambda>x. dRETURN (fi x), (\<lambda>x. RETURN (f x))) \<in> A \<rightarrow> \<langle>B\<rangle>dres_nres_rel"
  by (auto simp: dres_nres_rel_def dest: fun_relD)
end

lemma br_transfer[transfer_rule]:
  "((B ===> C) ===> (B ===> op =) ===> rel_set (rel_prod B C)) br br"
  if [transfer_rule]: "bi_total B"  "bi_unique C" "bi_total C"
  unfolding br_def
  by transfer_prover

lemma aform_appr_rel_transfer[transfer_rule]:
  "(rel_set (rel_prod (list_all2 op =) (rel_set rel_ve))) aform.appr_rel aform.appr_rel"
  unfolding aform.appr_rel_br
  by (transfer_prover)

lemma appr1_rel_transfer[transfer_rule]: "(rel_set (rel_prod
  (rel_prod (list_all2 op =) (rel_option (list_all2 op =)))
  (rel_set (rel_prod rel_ve (rel_blinfun rel_ve rel_ve))))) aform.appr1_rel aform.appr1_rel"
  unfolding aform.appr1_rel_internal
  by transfer_prover

lemma relAPP_transfer[transfer_rule]:
  "((rel_set (rel_prod B C) ===> D) ===> rel_set (rel_prod B C) ===> D) Relators.relAPP Relators.relAPP"
  unfolding relAPP_def
  by transfer_prover

lemma prod_rel_transfer[transfer_rule]:
  "(rel_set (rel_prod B C) ===> rel_set (rel_prod D E) ===> rel_set (rel_prod (rel_prod B D) (rel_prod C E)))
    prod_rel prod_rel"
  if [transfer_rule]:
  "bi_total B" "bi_unique B"
  "bi_unique C" "bi_total C"
  "bi_unique D" "bi_total D"
  "bi_unique E" "bi_total E"
  unfolding prod_rel_def_internal
  by transfer_prover

lemma Domain_transfer[transfer_rule]:
  "(rel_set (rel_prod A B) ===> rel_set A) Domain Domain"
  if [transfer_rule]:
  "bi_total A" "bi_unique A"
  "bi_total B" "bi_unique B"
  unfolding Domain_unfold
  by transfer_prover

lemma set_rel_transfer[transfer_rule]:
  "(rel_set (rel_prod B C) ===> rel_set (rel_prod (rel_set B) (rel_set C))) set_rel set_rel"
  if [transfer_rule]:
  "bi_total B" "bi_unique B"
  "bi_unique C" "bi_total C"
  unfolding set_rel_def_internal
  by transfer_prover

lemma relcomp_transfer[transfer_rule]:
  "(rel_set (rel_prod B C) ===> rel_set (rel_prod C D) ===> rel_set (rel_prod B D)) relcomp relcomp"
  if [transfer_rule]:
  "bi_total B" "bi_unique B"
  "bi_unique C" "bi_total C"
  "bi_unique D" "bi_total D"
  unfolding relcomp_unfold
  by transfer_prover

lemma Union_rel_transfer[transfer_rule]:
  "(rel_set (rel_prod B (rel_set C)) ===> rel_set (rel_prod C (rel_set D)) ===> rel_set (rel_prod B (rel_set D)))
    Union_rel Union_rel"
  if [transfer_rule]:
  "bi_total B" "bi_unique B"
  "bi_unique C" "bi_total C"
  "bi_unique D" "bi_total D"
  unfolding Union_rel_internal top_fun_def top_bool_def
  by transfer_prover

lemma fun_rel_transfer[transfer_rule]:
  "(rel_set (rel_prod B C) ===> rel_set (rel_prod D E) ===> rel_set (rel_prod (B ===> D) (C ===> E))) Relators.fun_rel Relators.fun_rel"
  if [transfer_rule]:
  "bi_unique B"
  "bi_unique C"
  "bi_unique D" "bi_total D"
  "bi_unique E" "bi_total E"
  unfolding fun_rel_def_internal
  by transfer_prover

lemma c1_info_of_apprse_transfer[transfer_rule]:
  "(list_all2 (rel_prod (rel_prod op = op =) (rel_prod (list_all2 op =) (rel_option (list_all2 op =))))
    ===> rel_set (rel_prod rel_ve (rel_blinfun rel_ve rel_ve)))
    aform.c1_info_of_apprse
    aform.c1_info_of_apprse"
  unfolding aform.c1_info_of_apprse_def
  by transfer_prover

term scaleR2_rel
(*
"scaleR2_rel"
  ::
  "('b \<times> ('c \<times> 'd) set) set
   \<Rightarrow> (((ereal \<times> ereal) \<times> 'b) \<times> ('c \<times> 'd) set) set"
*)
lemma scaleR2_rel_transfer[transfer_rule]:
  "(rel_set (rel_prod op = (rel_set (rel_prod op = op =))) ===>
    rel_set (rel_prod (rel_prod (rel_prod op = op =) op =) (rel_set (rel_prod op = op =)))) scaleR2_rel scaleR2_rel"
  unfolding scaleR2_rel_internal
  by transfer_prover

lemma appr1_rele_transfer[transfer_rule]:
  "(rel_set (rel_prod
    (rel_prod (rel_prod op = op =) (rel_prod (list_all2 op =) (rel_option (list_all2 op =))))
    (rel_set (rel_prod rel_ve (rel_blinfun rel_ve rel_ve))))) aform.appr1e_rel aform.appr1e_rel"
  unfolding scaleR2_rel_internal
  by transfer_prover

lemma flow1_of_vec1_times: "flow1_of_vec1 ` (A \<times> B) = A \<times> blinfun_of_vmatrix ` B"
  by (auto simp: flow1_of_vec1_def vec1_of_flow1_def)

lemma stable_on_transfer[transfer_rule]:
  "(rel_set rel_ve ===> rel_set rel_ve ===> op =) v.stable_on stable_on"
  unfolding stable_on_def v.stable_on_def
  by transfer_prover

theorem solves_poincare_map_aform:
  "solves_poincare_map_aform optns ode_fas safe_form (\<lambda>x. dRETURN (symstart x)) [S] guards ivl sctn roi XS RET dRET \<Longrightarrow>
    (symstart, symstarta) \<in> fun_rel (aform.appr1e_rel) (clw_rel aform.appr_rel \<times>\<^sub>r clw_rel aform.appr1e_rel) \<Longrightarrow>
    (\<And>X0. (\<lambda>(CX, X). flowsto (X0 - trap \<times> UNIV) {0..} (CX \<times> UNIV) X) (symstarta X0)) \<Longrightarrow>
    stable_on (aform.Csafe ode_fas safe_form - set_of_lvivl ivl \<inter> plane_of (map_sctn eucl_of_list sctn)) trap \<Longrightarrow>
    (\<And>X. X \<in> set XS \<Longrightarrow> aform.c1_info_invare DIM('a) X) \<Longrightarrow>
    length ode_fas = DIM('a) \<Longrightarrow>
    length (normal sctn) = DIM('a) \<Longrightarrow>
    length (fst ivl) = DIM('a) \<Longrightarrow>
    length (snd ivl) = DIM('a) \<Longrightarrow>
    length (normal S) = DIM('a) \<Longrightarrow>
    (\<And>a xs b ba ro.
        (xs, ro) \<in> set guards \<Longrightarrow>
        ((a, b), ba) \<in> set xs \<Longrightarrow>
        length a = DIM('a) \<and>
        length b = DIM('a) \<and> length (normal ba) = DIM('a)) \<Longrightarrow>
    length (fst RET) = CARD('n) \<Longrightarrow> length (snd RET) = CARD('n) \<Longrightarrow>
    aform.lvivl'_invar (CARD('n) * CARD('n)) dRET \<Longrightarrow>
    poincare_mapsto
     ((set_of_lvivl ivl::('a set)) \<inter> plane_of (map_sctn eucl_of_list sctn))
     (aform.c1_info_of_apprse XS - trap \<times> UNIV)
     (below_halfspace (map_sctn eucl_of_list S))
     (aform.Csafe ode_fas safe_form -
      set_of_lvivl ivl \<inter> plane_of (map_sctn eucl_of_list sctn))
     (set_of_lvivl RET \<times> blinfuns_of_lvivl' dRET)"
  apply (transfer fixing: optns ode_fas safe_form symstart S guards ivl sctn roi XS RET dRET)
  subgoal premises prems for symstarta trap
  proof -
    have "aform.poincare_mapsto ode_fas safe_form (set_of_lvivl ivl \<inter> plane_of (map_sctn eucl_of_list sctn))
     (aform.c1_info_of_apprse XS - trap \<times> UNIV) (below_halfspace (map_sctn eucl_of_list S))
     (aform.Csafe ode_fas safe_form - set_of_lvivl ivl \<inter> plane_of (map_sctn eucl_of_list sctn))
     (flow1_of_vec1 ` ({eucl_of_list (fst RET)..eucl_of_list (snd RET)} \<times> aform.set_of_lvivl' dRET))"
      apply (rule aform.solves_poincare_map[OF _ RETURN_dres_nres_relI RETURN_rule,
        of optns ode_fas safe_form symstart S guards ivl sctn roi XS "fst RET" "snd RET" dRET symstarta trap])
      subgoal using prems(1) by simp
      subgoal using prems(2) by (auto simp: fun_rel_def_internal)
      subgoal for X0
        using prems(3)[of X0] vflowsto_eq
        by auto
      subgoal
        unfolding aform.stable_on_def
      proof (safe, goal_cases)
        case (1 t x0)
        from 1 have a: "t \<in> v.existence_ivl0 x0" using vex_ivl_eq by blast
        with 1 have b: "v.flow0 x0 t \<in> trap" using vflow_eq by simp
        have c: "v.flow0 x0 s \<in> vX - set_of_lvivl ivl \<inter> plane_of (map_sctn eucl_of_list sctn)"
          if s: "s \<in> {0<..t}"
          for s
          using 1(4)[rule_format, OF s]
          apply (subst (asm) vflow_eq)
          unfolding aform_Csafe_vX[symmetric]
          using s a
          by (auto dest!: a.v.ivl_subset_existence_ivl)
        from a b c show ?case 
          using prems(4)[unfolded v.stable_on_def, rule_format, OF b a 1(3) c]
          by simp
      qed
      subgoal using prems by auto
      subgoal using prems by auto
      subgoal using prems by auto
      subgoal using prems by auto
      subgoal using prems by auto
      subgoal using prems by auto
      subgoal using prems by auto
      subgoal using prems by auto
      subgoal using prems by auto
      subgoal using prems by auto
      done
    then show ?thesis
      using vflow_eq vex_ivl_eq vflowsto_eq prems
      apply (subst vpoincare_mapsto_eq[symmetric])
      by (auto simp: set_of_lvivl_def set_of_ivl_def blinfun_of_vmatrix_image flow1_of_vec1_times)
  qed
  done

theorem solves_poincare_map_aform':
  "solves_poincare_map_aform' optns ode_fas safe_form S guards ivl sctn roi XS RET dRET\<Longrightarrow>
    (\<And>X. X \<in> set XS \<Longrightarrow> aform.c1_info_invare DIM('a) X) \<Longrightarrow>
    length ode_fas = DIM('a) \<Longrightarrow>
    length (normal sctn) = DIM('a) \<Longrightarrow>
    length (fst ivl) = DIM('a) \<Longrightarrow>
    length (snd ivl) = DIM('a) \<Longrightarrow>
    length (normal S) = DIM('a) \<Longrightarrow>
    (\<And>a xs b ba ro.
        (xs, ro) \<in> set guards \<Longrightarrow>
        ((a, b), ba) \<in> set xs \<Longrightarrow>
        length a = DIM('a) \<and>
        length b = DIM('a) \<and> length (normal ba) = DIM('a)) \<Longrightarrow>
    length (fst RET) = CARD('n) \<Longrightarrow> length (snd RET) = CARD('n) \<Longrightarrow>
    aform.lvivl'_invar (CARD('n) * CARD('n)) dRET \<Longrightarrow>
    poincare_mapsto
     ((set_of_lvivl ivl::('a set)) \<inter> plane_of (map_sctn eucl_of_list sctn))
     (aform.c1_info_of_apprse XS)
     (below_halfspace (map_sctn eucl_of_list S))
     (aform.Csafe ode_fas safe_form -
      set_of_lvivl ivl \<inter> plane_of (map_sctn eucl_of_list sctn))
     (set_of_lvivl RET \<times> blinfuns_of_lvivl' dRET)"
  apply (transfer fixing: optns ode_fas safe_form S guards ivl sctn roi XS RET dRET)
  subgoal
    using aform.solves_poincare_map'[of optns ode_fas safe_form S guards ivl sctn roi XS "fst RET" "snd RET" dRET]
    using vflow_eq vex_ivl_eq vflowsto_eq
    apply (subst vpoincare_mapsto_eq[symmetric])
    by (auto intro!: closed_Int simp: set_of_lvivl_def set_of_ivl_def blinfun_of_vmatrix_image
        flow1_of_vec1_times)
  done

end

end

subsection \<open>Example Utilities!\<close>

hide_const floatarith.Max floatarith.Min

lemma degree_sum_pdevs_scaleR_Basis:
  "degree (sum_pdevs (\<lambda>i. pdevs_scaleR (a i) i) (Basis::'b::euclidean_space set)) = Max ((\<lambda>i. degree (a i)) ` Basis)"
  apply (rule antisym)
  subgoal apply (rule degree_le)
    by (auto )
  subgoal
    apply (rule Max.boundedI)
      apply simp
     apply simp
    apply (auto simp: intro!: degree_leI)
    by (auto simp: euclidean_eq_iff[where 'a='b])
  done

lemma Inf_aform_eucl_of_list_aform:
  assumes "length a = DIM('b::executable_euclidean_space)"
  shows "Inf_aform (eucl_of_list_aform a::'b aform) = eucl_of_list (map Inf_aform a)"
  using assms
  apply (auto simp: eucl_of_list_aform_def Inf_aform_def[abs_def] algebra_simps
      eucl_of_list_inner inner_sum_left
      intro!: euclidean_eqI[where 'a='b])
  apply (auto simp: tdev_def inner_sum_left abs_inner inner_Basis if_distrib cong: if_cong)
  apply (rule sum.mono_neutral_cong_left)
     apply simp
  by (auto simp: degree_sum_pdevs_scaleR_Basis)

lemma Sup_aform_eucl_of_list_aform:
  assumes "length a = DIM('b::executable_euclidean_space)"
  shows "Sup_aform (eucl_of_list_aform a::'b aform) = eucl_of_list (map Sup_aform a)"
  using assms
  apply (auto simp: eucl_of_list_aform_def Sup_aform_def[abs_def] algebra_simps
      eucl_of_list_inner inner_sum_left
      intro!: euclidean_eqI[where 'a='b])
  apply (auto simp: tdev_def inner_sum_left abs_inner inner_Basis if_distrib cong: if_cong)
  apply (rule sum.mono_neutral_cong_right)
     apply simp
  by (auto simp: degree_sum_pdevs_scaleR_Basis)

lemma
  eucl_of_list_map_Inf_aform_leI:
  assumes "x \<in> Affine (eucl_of_list_aform a::'b::executable_euclidean_space aform)"
  assumes "length a = DIM('b)"
  shows "eucl_of_list (map Inf_aform a) \<le> x"
  using Inf_aform_le_Affine[OF assms(1)] assms(2)
  by (auto simp: Inf_aform_eucl_of_list_aform)

lemma
  eucl_of_list_map_Sup_aform_geI:
  assumes "x \<in> Affine (eucl_of_list_aform a::'b::executable_euclidean_space aform)"
  assumes "length a = DIM('b)"
  shows "x \<le> eucl_of_list (map Sup_aform a)"
  using Sup_aform_ge_Affine[OF assms(1)] assms(2)
  by (auto simp: Sup_aform_eucl_of_list_aform)

lemma
  mem_Joints_appendE:
  assumes "x \<in> Joints (xs @ ys)"
  obtains x1 x2 where "x = x1 @ x2" "x1 \<in> Joints xs" "x2 \<in> Joints ys"
  using assms
  by (auto simp: Joints_def valuate_def)

lemma c1_info_of_appr_subsetI1:
  fixes X1::"'b::executable_euclidean_space set"
  assumes subset: "{eucl_of_list (map Inf_aform (fst R)) .. eucl_of_list (map Sup_aform (fst R))} \<subseteq> X1"
  assumes len: "length (fst R) = DIM('b)"
  shows "aform.c1_info_of_appr R \<subseteq> X1 \<times> UNIV"
  using len
  apply (auto simp: aform.c1_info_of_appr_def flow1_of_list_def
      split: option.splits
      intro!: set_mp[OF subset] elim!: mem_Joints_appendE)
  subgoal
    by (auto intro!: eucl_of_list_mem_eucl_of_list_aform eucl_of_list_map_Inf_aform_leI eucl_of_list_map_Sup_aform_geI)
  subgoal
    by (auto intro!: eucl_of_list_mem_eucl_of_list_aform eucl_of_list_map_Inf_aform_leI eucl_of_list_map_Sup_aform_geI)
  subgoal
    apply (subst (2) eucl_of_list_take_DIM[symmetric, OF refl])
      apply (auto simp: min_def)
    apply (simp add: Joints_imp_length_eq eucl_of_list_map_Inf_aform_leI eucl_of_list_mem_eucl_of_list_aform)
    apply (simp add: Joints_imp_length_eq eucl_of_list_map_Inf_aform_leI eucl_of_list_mem_eucl_of_list_aform)
      done
  subgoal
    apply (subst (2) eucl_of_list_take_DIM[symmetric, OF refl])
      apply (auto simp: min_def)
    by (simp add: Joints_imp_length_eq eucl_of_list_map_Sup_aform_geI eucl_of_list_mem_eucl_of_list_aform)
  done

lemmas [simp] = compute_tdev

syntax product_aforms::"(real aform) list \<Rightarrow> (real aform) list \<Rightarrow> (real aform) list"
  (infixr "\<times>\<^sub>a" 70)


lemma matrix_inner_Basis_list:
  assumes "k < CARD('n) * CARD('m)"
  shows "(f::(('n::enum rvec, 'm::enum) vec)) \<bullet> Basis_list ! k =
    vec_nth (vec_nth f (enum_class.enum ! (k div CARD('n)))) (enum_class.enum ! (k mod CARD('n)))"
proof -
  have "f \<bullet> Basis_list ! k =
    (\<Sum>x\<in>UNIV.
       \<Sum>xa\<in>UNIV.
         if enum_class.enum ! (k mod CARD('n)) = xa \<and> enum_class.enum ! (k div CARD('n)) = x then f $ x $ xa else 0)"
    using assms
    unfolding inner_vec_def
    apply (auto simp: Basis_list_vec_def concat_map_map_index)
    apply (subst (2) sum.cong[OF refl])
     apply (subst sum.cong[OF refl])
      apply (subst (2) vec_nth_Basis2)
       apply (force simp add: Basis_vec_def Basis_list_real_def)
      apply (rule refl)
     apply (rule refl)
    apply (auto simp: cond_application_beta if_distrib axis_eq_axis Basis_list_real_def cong: if_cong)
    done
  also have "\<dots> = f $ enum_class.enum ! (k div CARD('n)) $ enum_class.enum ! (k mod CARD('n))"
    apply (subst if_conn)
    apply (subst sum.delta')
     apply simp
    by (simp add: sum.delta')
  finally show ?thesis by simp
qed

lemma list_of_eucl_matrix:
  "(list_of_eucl (M::(('n::enum rvec, 'm::enum) vec))) =
    concat (map (\<lambda>i. map (\<lambda>j. M $ (enum_class.enum ! i)$ (enum_class.enum ! j) )
      [0..<CARD('n)]) [0..<CARD('m)])"
  by (auto intro!: nth_equalityI simp: length_concat o_def sum_list_distinct_conv_sum_set ac_simps
      concat_map_map_index matrix_inner_Basis_list)

lemma axis_eq_eucl_of_list:
  "(axis i 1::'n::enum rvec) = eucl_of_list (replicate CARD('n) 0[index enum_class.enum i := 1])"
  apply (auto intro!: euclidean_eqI[where 'a="'n rvec"]
      simp: eucl_of_list_inner nth_list_update )
   apply (auto simp: index_Basis_list_axis1[symmetric])
  by (simp add: inner_axis inner_commute vec_nth_Basis)

lemma eucl_of_list_012: "eucl_of_list [vec_nth A 0, vec_nth A 1, vec_nth A 2] = A" for A::"3 rvec"
  apply vector
  apply (auto simp: vec_nth_eucl_of_list_eq index_Basis_list_axis1)
  using exhaust_3 three_eq_zero by blast


definition "ldec x = (case quotient_of x of (i, j) \<Rightarrow> real_of_float (lapprox_rat 20 i j))"
definition "udec x = (case quotient_of x of (i, j) \<Rightarrow> real_of_float (rapprox_rat 20 i j))"

lemma ldec: "ldec x \<le> real_of_rat x"
  and udec: "real_of_rat x \<le> udec x"
   apply (auto simp: ldec_def udec_def split: prod.splits
      intro!: lapprox_rat[le] rapprox_rat[ge])
   apply (metis Fract_of_int_quotient less_eq_real_def less_int_code(1) of_rat_rat
      quotient_of_denom_pos quotient_of_div)
  apply (metis Fract_of_int_quotient less_eq_real_def less_int_code(1) of_rat_rat
      quotient_of_denom_pos quotient_of_div)
  done

definition "matrix_of_degrees\<^sub>e =
  (let
    ur = Rad_of (Var 0);
    vr = Rad_of (Var 1)
   in
    [Cos ur, Cos vr, 0,
     Sin ur, Sin vr, 0,
     0, 0, 0])"

definition "matrix_of_degrees u v =
  approx_floatariths 30 matrix_of_degrees\<^sub>e (aforms_of_point ([u, v, 0]))"

lemma interpret_floatariths_matrix_of_degrees:
  "interpret_floatariths matrix_of_degrees\<^sub>e
    (([u::real, v::real, 0]))
   =
  [cos (rad_of u), cos (rad_of v), 0,
   sin (rad_of u), sin (rad_of v), 0,
   0, 0, 0]"
  by (auto simp: matrix_of_degrees\<^sub>e_def Let_def inverse_eq_divide)

definition "num_options p m N a projs print_fun =
  \<lparr>
    precision = p,
    reduce = correct_girard (p) (m) (N),
    adaptive_atol = FloatR 1 (- a),
    adaptive_rtol = FloatR 1 (- a),
    method_id = 2,
    start_stepsize  = FloatR 1 (- 5),
    iterations = 40,
    halve_stepsizes = 40,
    widening_mod = 10,
    rk2_param = FloatR 1 0,
    printing_fun = (\<lambda>a b.
        let
           _ = fold (\<lambda>(x, y, c) _.
               print_fun (String.implode (shows_segments_of_aform (x) (y) b c ''\<newline>''))) projs ();
           _ = print_fun (String.implode (''# '' @ shows_box_of_aforms_hr (b) '''' @ ''\<newline>''))
        in
         ()
    ),
    tracing_fun = (\<lambda>a b.
      let
        _ = print_fun (String.implode (''# '' @ a @ ''\<newline>''))
      in case b of Some b \<Rightarrow>
        (let
          _ = ()
        in print_fun (String.implode (''# '' @ shows_box_of_aforms_hr (b) '''' @ ''\<newline>'')))
        | None \<Rightarrow> ())
  \<rparr>"

definition "num_options_c1 p m N a projs dcolors print_fun =
  (let
    no = num_options p m N a (map (\<lambda>(x, y, c, ds). (x, y, c)) projs) print_fun;
    D = length dcolors
  in no
    \<lparr>printing_fun:=
      (\<lambda>a b. let _ = printing_fun no a b
          in if a then ()
          else fold (\<lambda>(x, y, c, ds) _. print_fun
              (String.implode (shows_aforms_vareq D [(x, y)] ds
                dcolors
                dcolors
            (FloatR 1 (-1)) ''# no C1 info'' b ''''))) projs ()
      )
    \<rparr>)"

definition "num_options_code p m N a projs print_fun =
  num_options (nat_of_integer p) (nat_of_integer m) (nat_of_integer N)
    (int_of_integer a) (map (\<lambda>(i, j, k). (nat_of_integer i, nat_of_integer j, k)) projs) print_fun"

definition "ro s n M g0 g1 inter_step =
  \<lparr>max_tdev_thres = (\<lambda>_. FloatR 1 s),
      pre_split_reduce = correct_girard 30 n M,
      pre_inter_granularity = (\<lambda>_::real aform list. FloatR 1 g0),
      post_inter_granularity = (\<lambda>_.  FloatR 1 g1),
      pre_collect_granularity = FloatR 1 g0,
      max_intersection_step = FloatR 1 inter_step\<rparr>"

definition "code_ro s n m g0 g1 inter_step =
  ro (int_of_integer s) (nat_of_integer n) (nat_of_integer m) (int_of_integer g0) (int_of_integer g1) (int_of_integer inter_step)"

fun xsec:: "real \<Rightarrow> real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> (real list \<times> real list) \<times> real list sctn"
  where "xsec x (y0, y1) (z0, z1) = (([x, y0, z0], [x, y1, z1]), Sctn [1,0,0] x)"
fun xsec':: "real \<Rightarrow> real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> (real list \<times> real list) \<times> real list sctn"
  where "xsec' x (y0, y1) (z0, z1) = (([x, y0, z0], [x, y1, z1]), Sctn [-1,0,0] (-x))"

fun ysec:: "real \<times> real \<Rightarrow> real \<Rightarrow> real \<times> real \<Rightarrow> (real list \<times> real list) \<times> real list sctn"
  where "ysec (x0, x1) y (z0, z1) = (([x0, y, z0], [x1, y, z1]), Sctn [0, 1,0] y)"
fun ysec':: "real \<times> real \<Rightarrow> real \<Rightarrow> real \<times> real \<Rightarrow> (real list \<times> real list) \<times> real list sctn"
  where "ysec' (x0, x1) y (z0, z1) = (([x0, y, z0], [x1, y, z1]), Sctn [0, -1,0] (-y))"

fun zsec:: "real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> real \<Rightarrow> (real list \<times> real list) \<times> real list sctn"
  where "zsec (x0, x1) (y0, y1) z = (([x0, y0, z], [x1, y1, z]), Sctn [0, 0, 1] z)"
fun zsec':: "real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> real \<Rightarrow> (real list \<times> real list) \<times> real list sctn"
  where "zsec' (x0, x1) (y0, y1) z = (([x0, y0, z], [x1, y1, z]), Sctn [0, 0, -1] (-z))"


fun xsec2:: "real \<Rightarrow> real \<times> real \<Rightarrow> (real list \<times> real list) \<times> real list sctn"
  where "xsec2 x (y0, y1) = (([x, y0], [x, y1]), Sctn [1,0] x)"
fun xsec2':: "real \<Rightarrow> real \<times> real \<Rightarrow>(real list \<times> real list) \<times> real list sctn"
  where "xsec2' x (y0, y1) = (([x, y0], [x, y1]), Sctn [-1,0] (-x))"

fun ysec2:: "real \<times> real \<Rightarrow> real \<Rightarrow> (real list \<times> real list) \<times> real list sctn"
  where "ysec2 (x0, x1) y = (([x0, y], [x1, y]), Sctn [0, 1] y)"
fun ysec2':: "real \<times> real \<Rightarrow> real \<Rightarrow> (real list \<times> real list) \<times> real list sctn"
  where "ysec2' (x0, x1) y = (([x0, y], [x1, y]), Sctn [0, -1] (-y))"

definition "code_sctn N n c = Sctn (replicate (nat_of_integer N) (0::real)[nat_of_integer n := 1]) c"
definition "code_sctn' N n c = Sctn (replicate (nat_of_integer N) (0::real)[nat_of_integer n := -1]) (-c)"

definition "lrat i j = real_of_float (lapprox_rat 30 (int_of_integer i) (int_of_integer j))"
definition "urat i j = real_of_float (lapprox_rat 30 (int_of_integer i) (int_of_integer j))"

definition [simp]: "TAG_optns (optns::string \<times> ((String.literal \<Rightarrow> unit) \<Rightarrow> (real aform) numeric_options)) = True"
lemma TAG_optns: "P \<Longrightarrow> (TAG_optns optns \<Longrightarrow> P)"
  by (auto simp: )

definition [simp]: "TAG_reach_optns (roi::real aform reach_options) = True"
lemma TAG_reach_optns: "P \<Longrightarrow> (TAG_reach_optns optns \<Longrightarrow> P)"
  by (auto simp: )

definition [simp]: "TAG_sctn (b::bool) = True"
lemma TAG_sctn: "P \<Longrightarrow> (TAG_sctn optns \<Longrightarrow> P)"
  by (auto simp: )

subsection \<open>Integrals and Computation\<close>

lemma has_vderiv_on_PairD:
  assumes "((\<lambda>t. (f t, g t)) has_vderiv_on fg') T"
  shows "(f has_vderiv_on (\<lambda>t. fst (fg' t))) T" "(g has_vderiv_on (\<lambda>t. snd (fg' t))) T"
proof -
  from assms have "((\<lambda>x. (f x, g x)) has_derivative (\<lambda>xa. xa *\<^sub>R fg' t)) (at t within T)"
     if "t \<in> T" for t
    by (auto simp: has_vderiv_on_def has_vector_derivative_def that
        intro!: derivative_eq_intros)
  from diff_chain_within[OF this has_derivative_fst[OF has_derivative_ident]]
    diff_chain_within[OF this has_derivative_snd[OF has_derivative_ident]]
  show "(f has_vderiv_on (\<lambda>t. fst (fg' t))) T" "(g has_vderiv_on (\<lambda>t. snd (fg' t))) T"
    by (auto simp: has_vderiv_on_def has_vector_derivative_def o_def)
qed

lemma solves_autonomous_odeI:
  assumes "((\<lambda>t. (t, phi t)) solves_ode (\<lambda>t x. (1, f (fst x) (snd x)))) S (T \<times> X)"
  shows "(phi solves_ode f) S X"
proof (rule solves_odeI)
  from solves_odeD[OF assms]
  have
    "((\<lambda>t. (t, phi t)) has_vderiv_on (\<lambda>t. (1, f (fst (t, phi t)) (snd (t, phi t))))) S"
    "\<And>t. t \<in> S \<Longrightarrow> (phi t) \<in> X"
    by (auto simp: )
  from has_vderiv_on_PairD(2)[OF this(1)] this(2)
  show "(phi has_vderiv_on (\<lambda>t. f t (phi t))) S" "\<And>t. t \<in> S \<Longrightarrow> phi t \<in> X"
    by auto
qed

lemma integral_solves_autonomous_odeI:
  fixes f::"real \<Rightarrow> 'a::executable_euclidean_space"
  assumes "(phi solves_ode (\<lambda>t _. f t)) {a .. b} X" "phi a = 0"
  assumes "a \<le> b"
  shows "(f has_integral phi b) {a .. b}"
proof -
  have "(f has_integral phi b - phi a) {a..b}"
    apply (rule fundamental_theorem_of_calculus[of a b phi f])
    unfolding has_vderiv_on_def[symmetric]
     apply fact
    using solves_odeD[OF assms(1)]
    by (simp add: has_vderiv_on_def)
  then show ?thesis by (simp add: assms)
qed

lemma zero_eq_eucl_of_list_rep_DIM: "(0::'a::executable_euclidean_space) = eucl_of_list (replicate (DIM('a)) 0)"
  by (auto intro!: euclidean_eqI[where 'a='a] simp: eucl_of_list_inner)

lemma zero_eq_eucl_of_list_rep: "(0::'a::executable_euclidean_space) = eucl_of_list (replicate D 0)"
  if "D \<ge> DIM('a)"
proof -
  from that have "replicate D (0::real) = replicate (DIM('a)) 0 @ replicate (D - DIM('a)) 0"
    by (auto simp: replicate_add[symmetric])
  also have "eucl_of_list \<dots> = (eucl_of_list (replicate DIM('a) 0)::'a)"
    by (rule eucl_of_list_append_zeroes)
  also have "\<dots> = 0"
    by (rule zero_eq_eucl_of_list_rep_DIM[symmetric])
  finally show ?thesis by simp
qed

lemma one_has_ivl_integral: "((\<lambda>x. 1::real) has_ivl_integral b - a) a b"
  using has_integral_const_real[of "1::real" a b] has_integral_const_real[of "1::real" b a]
  by (auto simp: has_ivl_integral_def split: if_splits)

lemma Joints_aforms_of_point_self[simp]: "xs \<in> Joints (aforms_of_point xs)"
  by (simp add: aforms_of_point_def)

lemma bind_eq_dRETURN_conv:
  "(f \<bind> g = dRETURN S) \<longleftrightarrow> (\<exists>R. f = dRETURN R \<and> g R = dRETURN S)"
  by (cases f) auto

context approximate_sets_options' begin

lemma c1_info_of_appre_c0_I:
  "(x, d) \<in> c1_info_of_appre ((1, 1), X0, None)"
  if "list_of_eucl x \<in> set_of_appr X0"
  using that
  by (force simp: c1_info_of_appre_def c1_info_of_appr_def)

lemma lvivl'_invar_None[simp]: "lvivl'_invar n None"
  by (auto simp: lvivl'_invar_def)

lemma c1_info_invar_None: "c1_info_invar n (u, None) \<longleftrightarrow> length u = n"
  by (auto simp: c1_info_invar_def)

lemma c1_info_invare_None: "c1_info_invare n ((l, u), x, None) \<longleftrightarrow>((l < u \<or> -\<infinity> < l \<and> l \<le> u \<and> u < \<infinity>) \<and> length x = n)"
  by (auto simp: c1_info_invare_def Let_def c1_info_invar_None)

end

lemma list_of_eucl_memI: "list_of_eucl (x::'x::executable_euclidean_space) \<in> S"
  if "x \<in> eucl_of_list ` S" "\<And>x. x \<in> S \<Longrightarrow> length x = DIM('x)"
  using that
  by auto

context ode_interpretation begin

theorem solves_one_step_ivl:
  assumes T: "T \<subseteq> {t1 .. t2}"
  assumes X: "X \<subseteq> {eucl_of_list lx .. eucl_of_list ux}" "length lx = DIM('a)" "length ux = DIM('a)"
  assumes S: "{eucl_of_list ls::'a .. eucl_of_list us} \<subseteq> S"
  assumes lens: "length ls = DIM('a)" "length us = DIM('a)" \<comment>\<open>TODO: this could be verified\<close>
  assumes [simp]: "length ode_fas = DIM('a)"
  assumes r: "solves_one_step_until_time_aform optns ode_fas safe_form ((1,1), aforms_of_ivls lx ux, None) t1 t2 (ls, us) None"
  shows "t \<in> T \<longrightarrow> x0 \<in> X \<longrightarrow> t \<in> existence_ivl0 x0 \<and> flow0 x0 t \<in> S"
proof (intro impI)
  assume t: "t \<in> T" and x0: "x0 \<in> X"
  from S have S: "set_of_lvivl (ls, us) \<subseteq> S"
    by (auto simp: set_of_lvivl_def set_of_ivl_def)
  have lens: "length (fst (ls, us)) = CARD('n)" "length (snd (ls, us)) = CARD('n)"
    by (auto simp: lens)
  have x0: "list_of_eucl x0 \<in> Joints (aforms_of_ivls lx ux)"
    apply (rule aforms_of_ivls)
    subgoal by (simp add: X)
    subgoal by (simp add: X)
    using set_mp[OF X(1) x0]
    apply (auto simp: eucl_le[where 'a='a] X)
    apply (metis assms(3) dim length_Basis_list list_of_eucl_eucl_of_list list_of_eucl_nth nth_Basis_list_in_Basis)
    apply (metis assms(4) dim length_Basis_list list_of_eucl_eucl_of_list list_of_eucl_nth nth_Basis_list_in_Basis)
    done
  from t T have t: "t \<in> {t1 .. t2}" by auto
  show "t \<in> existence_ivl0 x0 \<and> flow0 x0 t \<in> S"
    by (rule one_step_result12[OF r aform.c1_info_of_appre_c0_I[OF x0] t S subset_UNIV lens])
      (auto simp: aform.c1_info_invare_None lens X)
qed

theorem solves_one_step_ivl':
  assumes T: "T \<subseteq> {t1 .. t2}"
  assumes X: "X \<subseteq> {eucl_of_list lx .. eucl_of_list ux}"
    "length lx = DIM('a)" "length ux = DIM('a)"
  assumes DS: "list_interval lds uds \<subseteq> list_interval ld ud"
    and lends: "length lds = DIM('a)*DIM('a)" "length uds = DIM('a)*DIM('a)"
  assumes S: "{eucl_of_list ls::'a .. eucl_of_list us} \<subseteq> S"
  assumes lens0: "length ls = DIM('a)" "length us = DIM('a)" \<comment>\<open>TODO: this could be verified\<close>
    "length dx0s = DIM('a)*DIM('a)"
  assumes [simp]: "length ode_fas = DIM('a)"
  assumes r: "solves_one_step_until_time_aform optns ode_fas safe_form
    ((1,1), aforms_of_ivls lx ux, Some (aforms_of_point dx0s)) t1 t2 (ls, us) (Some (lds, uds))"
  shows "t \<in> T \<longrightarrow> x0 \<in> X \<longrightarrow> t \<in> existence_ivl0 x0 \<and> flow0 x0 t \<in> S \<and>
    Dflow x0 t o\<^sub>L blinfun_of_list dx0s \<in> blinfuns_of_lvivl (ld, ud)"
proof (intro impI)
  assume t: "t \<in> T" and x0: "x0 \<in> X"
  from S have S: "set_of_lvivl (ls, us) \<subseteq> S"
    by (auto simp: set_of_lvivl_def set_of_ivl_def)
  have lens: "length (fst (ls, us)) = CARD('n)" "length (snd (ls, us)) = CARD('n)"
    by (auto simp: lens0)
  have x0: "list_of_eucl x0 \<in> Joints (aforms_of_ivls lx ux)"
    apply (rule aforms_of_ivls)
    subgoal by (simp add: X)
    subgoal by (simp add: X)
    using set_mp[OF X(1) x0]
    apply (auto simp: eucl_le[where 'a='a] X)
    apply (metis assms(3) dim length_Basis_list list_of_eucl_eucl_of_list list_of_eucl_nth nth_Basis_list_in_Basis)
    apply (metis assms(4) dim length_Basis_list list_of_eucl_eucl_of_list list_of_eucl_nth nth_Basis_list_in_Basis)
    done
  have x0dx0: "(x0, blinfun_of_list dx0s) \<in>
      aform.c1_info_of_appre ((1, 1), aforms_of_ivls lx ux, Some (aforms_of_point dx0s))"
    apply (auto simp: aform.c1_info_of_appre_def aform.c1_info_of_appr_def)
    apply (rule image_eqI[where x="list_of_eucl x0@dx0s"])
    using lens0
     apply (auto simp: flow1_of_list_def aforms_of_point_def aform.set_of_appr_of_ivl_append_point)
    apply (rule imageI)
    apply (rule x0)
    done
  from t T have t: "t \<in> {t1 .. t2}" by auto
  have DS: "blinfuns_of_lvivl' (Some (lds, uds)) \<subseteq> blinfun_of_list ` list_interval ld ud"
    using DS
    by (auto simp: blinfuns_of_lvivl'_def blinfuns_of_lvivl_def)
  have inv: "aform.lvivl'_invar (CARD('n) * CARD('n)) (Some (lds, uds))"
    "aform.c1_info_invare DIM('a) ((1::ereal, 1), aforms_of_ivls lx ux, Some (aforms_of_point dx0s))"
    by (auto simp: aform.lvivl'_invar_def lends aform.c1_info_invare_def X lens0 power2_eq_square
        aform.c1_info_invar_def)
  from one_step_result123[OF r x0dx0 t S DS lens inv \<open>length ode_fas = _\<close>]
  show "t \<in> existence_ivl0 x0 \<and> flow0 x0 t \<in> S \<and> Dflow x0 t o\<^sub>L blinfun_of_list dx0s \<in> blinfuns_of_lvivl (ld, ud)"
    by (auto simp: blinfuns_of_lvivl_def)
qed

end

definition "zero_aforms D = map (\<lambda>_. (0, zero_pdevs)) [0..<D]"

definition "solves_one_step_until_time_aform_fo soptns a b c d e f g =
  file_output (String.implode (fst soptns)) (\<lambda>pf. solves_one_step_until_time_aform (snd soptns pf) a b c d e f g)"

definition "solves_poincare_map_aform'_fo soptns a b c d e f g h i j =
  file_output (String.implode (fst soptns)) (\<lambda>pf. solves_poincare_map_aform' (snd soptns pf) a b c d e f g h i j)"

lemma solves_one_step_until_time_aform_foI:
  "solves_one_step_until_time_aform (snd optns (\<lambda>_. ())) a b c d e f g"
  if "solves_one_step_until_time_aform_fo optns a b c d e f g"
  using that
  by (auto simp: solves_one_step_until_time_aform_fo_def file_output_def Print.file_output_def
      print_def[abs_def]
      split: if_splits)

lemma solves_poincare_map_aform'_foI:
  "solves_poincare_map_aform' (snd optns (\<lambda>_. ())) a b c d e f g h i j"
  if "solves_poincare_map_aform'_fo optns a b c d e f g h i j"
  using that
  by (auto simp: solves_poincare_map_aform'_fo_def file_output_def Print.file_output_def
      print_def[abs_def]
      split: if_splits)

theorem solve_one_step_until_time_aform_integral_bounds:
  fixes f::"real \<Rightarrow> 'a::executable_euclidean_space"
  assumes "a \<le> b"
  assumes ba: "b - a \<in> {t1 .. t2}"
  assumes a: "a \<in> {a1 .. a2}"
  assumes ls_us_subset: "{eucl_of_list ls .. eucl_of_list us} \<subseteq> {l .. u}"
  assumes fas: "\<And>xs::real list. length xs > 0 \<Longrightarrow> (1::real, f (xs ! 0)) = einterpret fas xs"
  assumes D: "D = DIM('a) + 1" "D = CARD('i::enum)"
  assumes lenlu: "length ls + 1 = D" "length us + 1 = D"
  assumes lfas: "length fas = D"
  assumes sos[THEN solves_one_step_until_time_aform_foI]: "solves_one_step_until_time_aform_fo optns fas true_form
    ((1,1), (aforms_of_ivls (a1#replicate (D - 1) 0) (a2#replicate (D - 1) 0)), None) t1 t2 (0#ls, t2#us) None"
  shows "integral {a .. b} f \<in> {l .. u}"
proof -
  have lens0: "length ((x::real) # replicate (D - 1) 0) = DIM(real \<times> 'a)" for x
    using assms
    by auto
  have a0: "(a, 0) \<in> {eucl_of_list (a1 # replicate (D - 1) 0)..eucl_of_list (a2 # replicate (D - 1) 0)}"
    using assms
    by (auto simp: eucl_of_list_prod)
  let ?U = "aform.Csafe fas true_form"
  interpret ode_interpretation true_form ?U fas "\<lambda>x. (1::real, f (fst x))" "undefined::'i"
    apply unfold_locales
    subgoal using assms by simp
    subgoal by simp
    subgoal for x
      apply (cases x)
      unfolding aform.ode_def
      apply (rule HOL.trans[OF _ fas])
      by (auto simp: )
    done
  have lens: "length (0 # ls) = DIM(real \<times> 'a)" "length (t2 # us) = DIM(real \<times> 'a)" "length fas = DIM(real \<times> 'a)"
    using lenlu
    by (simp_all add: lfas D)
  from solves_one_step_ivl[rule_format, OF order_refl order_refl lens0 lens0  order_refl lens sos ba a0]
  have lsus: "flow0 (a, 0) (b - a) \<in> {eucl_of_list (0#ls)..eucl_of_list (t2#us)}"
    and exivl: "b - a \<in> existence_ivl0 (a, 0)"
    by auto
  have flow: "flow0 (a, 0) (b - a) \<in> UNIV \<times> {l..u}"
    using lsus
    apply (rule set_rev_mp)
    using ls_us_subset
    by (auto simp: eucl_of_list_prod)
  from ivl_subset_existence_ivl[OF exivl] \<open>a \<le> b\<close> exivl
  have "0 \<in> existence_ivl0 (a, 0)"
    by auto
  from mem_existence_ivl_iv_defined(2)[OF this]
  have safe: "(a, 0::'a) \<in> ?U" by simp
  from flow_solves_ode[OF UNIV_I this]
  have fs: "((\<lambda>t. (fst (flow0 (a, 0) t), snd (flow0 (a, 0) t))) solves_ode (\<lambda>_ x. (1, f (fst x)))) (existence_ivl0 (a, 0)) ?U"
    by simp
  with solves_odeD[OF fs]
  have vdp: "((\<lambda>t. (fst (flow0 (a, 0) t), snd (flow0 (a, 0) t))) has_vderiv_on (\<lambda>t. (1, f (fst (flow0 (a, 0) t))))) (existence_ivl0 (a, 0))"
    by simp
  have "fst (flow0 (a, 0) t) = a + t" if "t \<in> existence_ivl0 (a, 0)" for t
  proof -
    have "fst (flow0 (a, 0) 0) = a" using safe
      by (auto simp: )
    have "((\<lambda>t. fst (flow0 (a, 0) t)) has_vderiv_on (\<lambda>x. 1)) (existence_ivl0 (a, 0))"
      using has_vderiv_on_PairD[OF vdp] by auto
    then have "((\<lambda>t. fst (flow0 (a, 0) t)) has_vderiv_on (\<lambda>x. 1)) {0--t}"
      apply (rule has_vderiv_on_subset)
      using closed_segment_subset_existence_ivl[OF that]
      by auto
    from fundamental_theorem_of_calculus_ivl_integral[OF this, THEN ivl_integral_unique]
      one_has_ivl_integral[of t 0, THEN ivl_integral_unique] safe
    show ?thesis
      by auto
  qed
  with vdp have "((\<lambda>t. (t, snd (flow0 (a, 0) t))) solves_ode (\<lambda>t x. (1, f (a + fst x))))
    (existence_ivl0 (a, 0)) ((existence_ivl0 (a, 0)) \<times> UNIV)"
    apply (intro solves_odeI)
     apply auto
    apply (auto simp: has_vderiv_on_def has_vector_derivative_def)
  proof goal_cases
    case (1 x)
    have r: "((\<lambda>(x, y). (x - a, y::'a)) has_derivative (\<lambda>x. x)) (at x within t)" for x t
      by (auto intro!: derivative_eq_intros)
    from 1 have "((\<lambda>x. (a + x, snd (flow0 (a, 0) x))) has_derivative (\<lambda>xa. (xa, xa *\<^sub>R f (a + x))))
        (at x within existence_ivl0 (a, 0))"
      by auto
    from has_derivative_in_compose2[OF r subset_UNIV _ this, simplified] 1
    have "((\<lambda>x. (x, snd (flow0 (a, 0) x))) has_derivative (\<lambda>y. (y, y *\<^sub>R f (a + x)))) (at x within existence_ivl0 (a, 0))"
      by auto
    then show ?case
      by simp
  qed
  from solves_autonomous_odeI[OF this]
  have "((\<lambda>t. snd (flow0 (a, 0) t)) solves_ode (\<lambda>b c. f (a + b))) (existence_ivl0 (a, 0)) UNIV"
    by simp \<comment>\<open>TODO: do non-autonomous -- autonomous conversion automatically!\<close>
  then have "((\<lambda>t. snd (flow0 (a, 0) t)) solves_ode (\<lambda>b c. f (a + b))) {0 .. b - a} UNIV"
    apply (rule solves_ode_on_subset)
    using exivl
     apply auto
    using existence_ivl_zero mem_is_interval_1_I by blast
  from integral_solves_autonomous_odeI[OF this]
  have "((\<lambda>b. f (a + b)) has_integral snd (flow0 (a, 0) (b - a))) (cbox 0 (b - a))"
    using \<open>a \<le> b\<close> safe
    by auto
  from has_integral_affinity[OF this, where m=1 and c="-a"]
  have "(f has_integral snd (flow0 (a, 0) (b - a))) {a..b}"
    by auto
  then have "integral {a..b} f = snd (flow0 (a, 0) (b - a))" by blast
  also have "\<dots> \<in> {l .. u}"
    using flow
    by auto
  finally show ?thesis by simp
qed

lemma [code_computation_unfold]:
  "numeral x = real_of_int (Code_Target_Int.positive x)"
  by simp
lemma [code_computation_unfold]: "numeral x \<equiv> Float (Code_Target_Int.positive x) 0"
  by (simp add: Float_def)

definition no_print::"String.literal \<Rightarrow> unit" where "no_print x = ()"

lemmas [approximation_preproc] = list_of_eucl_real list_of_eucl_prod append.simps

named_theorems DIM_simps
lemmas [DIM_simps] =
  DIM_real DIM_prod length_nth_simps
  add_numeral_special
  add_numeral_special card_sum card_prod card_bit0 card_bit1 card_num0 card_num1
  numeral_times_numeral numeral_mult mult_1_right mult_1

lemma numeral_refl: "numeral x = numeral x" by simp

lemma plain_floatarith_approx_eq_SomeD:
  "approx prec fa [] = Some (fst (the (approx prec fa [])), snd (the (approx prec fa [])))"
  if "plain_floatarith 0 fa"
  using that
  by (auto dest!: plain_floatarith_approx_not_None[where p=prec and XS=Nil])

definition [simp]: "approx1 p f xs = real_of_float (fst (the (approx p f xs)))"
definition [simp]: "approx2 p f xs = real_of_float (snd (the (approx p f xs)))"
definition [simp]: "approx_defined p f xs \<longleftrightarrow> approx p f xs \<noteq> None"

definition "approxs p fs xs = those (map (\<lambda>f. approx p f xs) fs)"
definition [simp]: "approxs1 p f xs =
  (case approxs p f xs of Some y \<Rightarrow> (map (real_of_float o fst) y) | None \<Rightarrow> replicate (length f) 0)"
definition [simp]: "approxs2 p f xs =
  (case approxs p f xs of Some y \<Rightarrow> (map (real_of_float o snd) y) | None \<Rightarrow> replicate (length f) 0)"
definition "approxs_defined p fs xs \<longleftrightarrow> (those (map (\<lambda>f. approx p f xs) fs) \<noteq> None)"

lemma length_approxs:
  "length (approxs1 p f xs) = length f"
  "length (approxs2 p f xs) = length f"
  by (auto simp: approxs_def dest!: those_eq_SomeD split: option.splits)

lemma real_in_approxI:
  "x \<in> {(approx1 prec fa []) .. (approx2 prec fa [])}"
  if "x = interpret_floatarith fa []"
    "approx_defined prec fa []"
  using that
  by (auto dest: approx_emptyD)


lemma real_subset_approxI:
  "{a .. b} \<subseteq> {(approx1 prec fa []) .. (approx2 prec fb [])}"
  if "a = interpret_floatarith fa []"
    "b = interpret_floatarith fb []"
    "approx_defined prec fa []"
    "approx_defined prec fb []"
  using that
  by (auto dest: approx_emptyD)


lemma approxs_eq_Some_lengthD: "length ys = length fas" if "approxs prec fas XS = Some ys"
  using that
  by (auto simp: approxs_def dest!: those_eq_SomeD)

lemma approxs_pointwise:
  "interpret_floatarith (fas ! ia) xs \<in> {real_of_float (fst (ys ! ia)) .. (snd (ys ! ia))}"
  if "approxs prec fas XS = Some ys" "bounded_by xs XS" "ia < length fas"
proof -
  from those_eq_SomeD[OF that(1)[unfolded approxs_def]]
  have ys: "ys = map (the \<circ> (\<lambda>f. approx prec f XS)) fas"
    and ex: "\<exists>y. i < length fas \<longrightarrow> approx prec (fas ! i) XS = Some y" for i
    by auto
  from ex[of ia] that obtain l u where lu: "Some (l, u) = approx prec (fas ! ia) XS" by auto
  from approx[OF that(2) this]
  have "real_of_float l \<le> interpret_floatarith (fas ! ia) xs \<and> interpret_floatarith (fas ! ia) xs \<le> real_of_float u"
    by auto
  moreover
  have "ys ! ia = (l, u)"
    unfolding ys
    apply (auto simp: o_def)
    apply (subst nth_map)
     apply (simp add: that)
    using lu[symmetric] by simp
  ultimately show ?thesis
    using that
    by (auto simp: approxs_eq_Some_lengthD split: prod.splits)
qed

lemmas approxs_pointwise_le = approxs_pointwise[simplified, THEN conjunct1]
  and approxs_pointwise_ge = approxs_pointwise[simplified, THEN conjunct2]

lemma approxs_eucl:
  "eucl_of_list (interpret_floatariths fas xs) \<in>
    {eucl_of_list (map fst ys) .. eucl_of_list (map snd ys)::'a::executable_euclidean_space}"
  if "approxs prec fas XS = Some ys"
    "length fas = DIM('a)"
    "bounded_by xs XS"
  using that
  by (auto simp: eucl_le[where 'a='a] eucl_of_list_inner o_def approxs_eq_Some_lengthD
      intro!: approxs_pointwise_le approxs_pointwise_ge)

lemma plain_floatariths_approx_eq_SomeD:
  "approxs prec fas [] = Some (the (approxs prec fas []))"
  if "list_all (plain_floatarith 0) fas"
  using that
  apply (induction fas)
   apply (auto simp: approxs_def split: option.splits dest!: plain_floatarith_approx_eq_SomeD)
  subgoal for a fas aa b
    apply (cases "those (map (\<lambda>f. approx prec f []) fas)")
    by auto
  done

lemma approxs_definedD:
  "approxs prec fas xs = Some (the (approxs prec fas xs))"
  if "approxs_defined prec fas xs"
  using that
  by (auto simp: approxs_defined_def approxs_def)

lemma approxs_defined_ne_None[simp]:
  "approxs prec fas xs \<noteq> None"
  if "approxs_defined prec fas xs"
  using that
  by (auto simp: approxs_defined_def approxs_def)

lemma approx_subset_euclI:
  "{eucl_of_list (approxs2 prec fals [])::'a .. eucl_of_list (approxs1 prec faus [])} \<subseteq> {l .. u}"
  if "list_of_eucl l = interpret_floatariths fals []"
    and "list_of_eucl u = interpret_floatariths faus []"
    and "length fals = DIM('a::executable_euclidean_space)"
    and "length faus = DIM('a::executable_euclidean_space)"
    and "approxs_defined prec fals []"
    and "approxs_defined prec faus []"
  using that
  by (auto intro!: bounded_by_Nil
      dest!: approxs_eucl[where 'a='a] list_of_eucl_eqD plain_floatariths_approx_eq_SomeD[where prec=prec]
        split: option.splits)

lemma eucl_subset_approxI:
  "{l .. u} \<subseteq> {eucl_of_list (approxs1 prec fals [])::'a .. eucl_of_list (approxs2 prec faus [])}"
  if "list_of_eucl l = interpret_floatariths fals []"
    and "list_of_eucl u = interpret_floatariths faus []"
    and "length fals = DIM('a::executable_euclidean_space)"
    and "length faus = DIM('a::executable_euclidean_space)"
    and "approxs_defined prec fals []"
    and "approxs_defined prec faus []"
  using that
  by (auto intro!: bounded_by_Nil
      dest!: approxs_eucl[where 'a='a] list_of_eucl_eqD plain_floatariths_approx_eq_SomeD[where prec=prec]
        split: option.splits)

lemma approx_subset_listI:
  "list_interval (approxs2 prec fals []) (approxs1 prec faus []) \<subseteq> list_interval l u"
  if "l = interpret_floatariths fals []"
    and "u = interpret_floatariths faus []"
    and "length fals = length l"
    and "length faus = length u"
    and "approxs_defined prec fals []"
    and "approxs_defined prec faus []"
  using that
  apply (auto
      simp: list_interval_def list_all2_conv_all_nth
      dest: approxs_eq_Some_lengthD
      intro!: bounded_by_Nil
      dest!: plain_floatariths_approx_eq_SomeD[where prec=prec]
      split: option.splits)
   apply (rule order_trans)
    apply (rule approxs_pointwise_ge)
      apply assumption
     apply (rule bounded_by_Nil)
    apply (auto dest: approxs_eq_Some_lengthD)
  apply (subst interpret_floatariths_nth)
   apply (auto dest: approxs_eq_Some_lengthD)
    apply (rule approxs_pointwise_le[ge])
      apply assumption
     apply (rule bounded_by_Nil)
  apply (auto dest: approxs_eq_Some_lengthD)
  done


definition "unit_list D n = replicate D 0[n:=1]"

definition "mirror_sctn (sctn::real list sctn) = Sctn (map uminus (normal sctn)) (- pstn sctn)"
definition "mirrored_sctn b (sctn::real list sctn) = (if b then mirror_sctn sctn else sctn)"

lemma mirror_sctn_simps[simp]: "pstn (mirror_sctn sctn) = - pstn sctn"
  "normal (mirror_sctn sctn) = map uminus (normal sctn)"
  by (cases sctn) (auto simp: mirror_sctn_def)

lemma length_unit_list[simp]: "length (unit_list D n) = D"
  by (auto simp: unit_list_def)

lemma eucl_of_list_unit_list[simp]:
  "(eucl_of_list (unit_list D n)::'a::executable_euclidean_space) = Basis_list ! n"
  if "D = DIM('a)" "n < D"
  using that
  by (auto simp: unit_list_def eucl_of_list_inner inner_Basis nth_list_update'
      intro!: euclidean_eqI[where 'a='a])

lemma le_eucl_of_list_iff: "(t::'a::executable_euclidean_space) \<le> eucl_of_list uX0 \<longleftrightarrow>
  (\<forall>i. i < DIM('a) \<longrightarrow> t \<bullet> Basis_list ! i \<le> uX0 ! i)"
  if "length uX0 = DIM('a)"
  using that
  apply (auto simp: eucl_le[where 'a='a] eucl_of_list_inner)
  using nth_Basis_list_in_Basis apply force
  by (metis Basis_list in_Basis_index_Basis_list index_less_size_conv length_Basis_list)

lemma eucl_of_list_le_iff: "eucl_of_list uX0 \<le> (t::'a::executable_euclidean_space) \<longleftrightarrow>
  (\<forall>i. i < DIM('a) \<longrightarrow> uX0 ! i \<le> t \<bullet> Basis_list ! i)"
  if "length uX0 = DIM('a)"
  using that
  apply (auto simp: eucl_le[where 'a='a] eucl_of_list_inner)
  using nth_Basis_list_in_Basis apply force
  by (metis Basis_list in_Basis_index_Basis_list index_less_size_conv length_Basis_list)

lemma Joints_aforms_of_ivls: "Joints (aforms_of_ivls lX0 uX0) = list_interval lX0 uX0"
  if "list_all2 op \<le> lX0 uX0"
  using that
  apply (auto simp: list_interval_def dest: Joints_aforms_of_ivlsD1[OF _ that]
      Joints_aforms_of_ivlsD2[OF _ that] list_all2_lengthD
      intro!: aforms_of_ivls)
  by (auto simp: list_all2_conv_all_nth)

lemma list_of_eucl_in_list_interval_iff:
  "list_of_eucl x0 \<in> list_interval lX0 uX0 \<longleftrightarrow> x0 \<in> {eucl_of_list lX0 .. eucl_of_list uX0::'a}"
  if "length lX0 = DIM('a::executable_euclidean_space)"
     "length uX0 = DIM('a::executable_euclidean_space)"
  using that
  by (auto simp: list_interval_def eucl_of_list_le_iff le_eucl_of_list_iff list_all2_conv_all_nth)


text \<open>TODO: make a tactic out of this?!\<close>

lemma file_output_iff: "file_output s f = f (\<lambda>_. ())"
  by (auto simp: file_output_def print_def[abs_def] Print.file_output_def)

context ode_interpretation begin

lemma poincare_mapsto_subset:
     "poincare_mapsto P  X0 SS CX R"
  if "poincare_mapsto P' Y0 RR CZ S" "X0 \<subseteq> Y0" "CZ \<subseteq> CX" "S \<subseteq> R" "RR = SS" "P = P'"
  using that
  by (force simp: poincare_mapsto_def)

theorem solves_poincare_map_aform'_derivI:
  assumes solves:
    "solves_poincare_map_aform'_fo optns ode_fas safe_form
      (Sctn (unit_list D n) (lP ! n))
      guards
      (lP, uP)
      (Sctn (unit_list D n) (lP ! n))
      roi
      [((1,1), aforms_of_ivls lX0 uX0, Some (aforms_of_point DX0))]
      (lR, uR)
      (Some (lDR, uDR))"
    and D: "D = DIM('a)"
  assumes DS: "list_interval lDR uDR \<subseteq> list_interval lDS uDS"
  and ode_fas: "length ode_fas = DIM('a)"
  and lens:
    "length (lP) = DIM('a)" "length (uP) = DIM('a)"
    "length (lX0) = DIM('a)" "length (uX0) = DIM('a)"
    "length (lR) = DIM('a)" "length (uR) = DIM('a)"
    "length DX0 = DIM('a)*DIM('a)"
    "length lDR = CARD('n) * CARD('n)"
    "length uDR = CARD('n) * CARD('n)"
    and guards:
    "(\<And>a xs b ba ro.
        (xs, ro) \<in> set guards \<Longrightarrow>
      ((a, b), ba) \<in> set xs \<Longrightarrow>
          length a = DIM('a) \<and> length b = DIM('a) \<and> length (normal ba) = DIM('a))"
  and P: "P = {eucl_of_list lP .. eucl_of_list uP}"
  and plane: "uP ! n = lP ! n"
  and X0: "X0 \<subseteq> {eucl_of_list lX0 .. eucl_of_list uX0}"
  and nD: "n < DIM('a)"
  and SS: "SS = {x::'a. x \<bullet> Basis_list ! n \<le> lP ! n}"
  and R: "{eucl_of_list lR .. eucl_of_list uR} \<subseteq> R"
  shows "\<forall>x\<in>X0. returns_to P x \<and>
    return_time P differentiable at x within SS \<and>
    (\<exists>D. (poincare_map P has_derivative blinfun_apply D) (at x within SS) \<and>
         poincare_map P x \<in> R \<and> D o\<^sub>L blinfun_of_list DX0 \<in> blinfuns_of_lvivl (lDS, uDS))"
proof (rule ballI)
  fix x assume "x \<in> X0"
  then have la2: "list_all2 op \<le> lX0 uX0"
    using X0
    by (force simp: subset_iff eucl_of_list_le_iff le_eucl_of_list_iff lens list_all2_conv_all_nth)
  have 1: "\<And>X. X \<in> set [((1::ereal, 1::ereal), aforms_of_ivls lX0 uX0, Some (aforms_of_point DX0))] \<Longrightarrow>
      aform.c1_info_invare DIM('a) X"
    for X
    by (auto simp: aform.c1_info_invare_def aform.c1_info_invar_def lens power2_eq_square)
  have 2: "length (normal (Sctn (unit_list D n) (lP ! n))) = DIM('a)"
    by (auto simp: D)
  have 3: "length (fst (lP, uP)) = DIM('a)" "length (snd (lP, uP)) = DIM('a)"
    by (auto simp: lens)
  have 4: "length (normal (Sctn (unit_list D n) (lP ! n))) = DIM('a)"
    by (auto simp: D)
  have 5: "length (fst (lR, uR)) = CARD('n)" "length (snd (lR, uR)) = CARD('n)"
    "aform.lvivl'_invar (CARD('n) * CARD('n)) (Some (lDR, uDR))"
    by (auto simp: lens aform.lvivl'_invar_def)
  note solves = solves[unfolded solves_poincare_map_aform'_fo_def file_output_iff]
  have "poincare_mapsto
     (set_of_lvivl (lP, uP) \<inter>
      plane_of (map_sctn eucl_of_list (Sctn (unit_list D n) (lP ! n))))
     (aform.c1_info_of_apprse [((1, 1), aforms_of_ivls lX0 uX0, Some (aforms_of_point DX0))])
     (below_halfspace
       (map_sctn eucl_of_list (Sctn (unit_list D n) (lP ! n))))
     (aform.Csafe ode_fas safe_form -
      set_of_lvivl (lP, uP) \<inter>
      plane_of (map_sctn eucl_of_list (Sctn (unit_list D n) (lP ! n))))
     (set_of_lvivl (lR, uR) \<times> blinfuns_of_lvivl' (Some (lDR, uDR)))"
    by (rule solves_poincare_map_aform'[OF solves, OF 1 ode_fas 2 3 4 guards 5])
      auto
  then have "poincare_mapsto P (X0 \<times> {blinfun_of_list DX0}::('a \<times> ('a \<Rightarrow>\<^sub>L 'a)) set) SS UNIV
    (R \<times> blinfuns_of_lvivl (lDS, uDS))"
    apply (rule poincare_mapsto_subset)
    subgoal using X0
      apply (auto simp: aform.c1_info_of_appre_def aform.c1_info_of_appr_def
          aform.c1_info_of_apprse_def)
      subgoal for x0
        apply (rule image_eqI[where x="list_of_eucl x0@DX0"])
        using lens
         apply (auto simp: flow1_of_list_def aforms_of_point_def aform.set_of_appr_of_ivl_append_point)
        apply (rule imageI)
        using X0
        by (auto simp: Joints_aforms_of_ivls la2 list_of_eucl_in_list_interval_iff)
      done
    subgoal by simp
    subgoal using R DS
      by (auto simp: set_of_lvivl_def set_of_ivl_def blinfuns_of_lvivl'_def blinfuns_of_lvivl_def
          lens)
    subgoal
      using assms
      by (simp add: below_halfspace_def le_halfspace_def[abs_def])
    subgoal
      using assms
      by (fastforce simp add: P set_of_lvivl_def set_of_ivl_def plane_of_def
          le_eucl_of_list_iff eucl_of_list_le_iff)
    done
  then show "returns_to P x \<and>
    return_time P differentiable at x within SS \<and>
    (\<exists>D. (poincare_map P has_derivative blinfun_apply D) (at x within SS) \<and>
         poincare_map P x \<in> R \<and> D o\<^sub>L blinfun_of_list DX0 \<in> blinfuns_of_lvivl (lDS, uDS))"
    using \<open>x \<in> X0\<close>
    by (auto simp: poincare_mapsto_def)
qed

definition guards_invar::"nat \<Rightarrow> (((real list \<times> real list) \<times> real list sctn) list \<times>
    (real \<times> real pdevs) reach_options) list \<Rightarrow> bool"
  where "guards_invar D guards = (\<forall>(xs, ro) \<in> set guards.
    \<forall>((a, b), ba) \<in> set xs. length a = D \<and> length b = D \<and> length (normal ba) = D)"

theorem solves_poincare_map_aform'I:
  assumes "TAG_optns optns"
  assumes "TAG_reach_optns roi"
  assumes "TAG_sctn mirrored"
  assumes D: "D = DIM('a)"
  assumes guards: "guards_invar DIM('a) guards"
  and P: "P = {eucl_of_list lP .. eucl_of_list uP}"
  and plane: "uP ! n = lP ! n"
  and ode_fas: "length ode_fas = DIM('a)"
  and X0: "X0 \<subseteq> {eucl_of_list lX0 .. eucl_of_list uX0}"
  and nD: "n < DIM('a)"
  and R: "{eucl_of_list lR .. eucl_of_list uR} \<subseteq> R"
  and lens:
    "length (lP) = DIM('a)" "length (uP) = DIM('a)"
    "length (lX0) = DIM('a)" "length (uX0) = DIM('a)"
    "length (lR) = DIM('a)" "length (uR) = DIM('a)"
  and solves:
    "solves_poincare_map_aform'_fo optns ode_fas safe_form
      (Sctn (unit_list D n) (lP ! n))
      guards
      (lP, uP)
      (mirrored_sctn mirrored (Sctn (unit_list D n) (lP ! n)))
      roi
      [((1,1), aforms_of_ivls lX0 uX0, None)]
      (lR, uR)
      None"
shows "\<forall>x\<in>X0. returns_to P x \<and> poincare_map P x \<in> R"
proof -
  note solves = solves[unfolded solves_poincare_map_aform'_fo_def file_output_iff]
  have 1: "\<And>X. X \<in> set [((1::ereal, 1::ereal), aforms_of_ivls lX0 uX0, None)] \<Longrightarrow>
      aform.c1_info_invare DIM('a) X"
    for X
    by (auto simp: aform.c1_info_invare_def aform.c1_info_invar_def lens)
  have 2: "length (normal ((mirrored_sctn mirrored (Sctn (unit_list D n) (lP ! n))))) = DIM('a)"
    by (auto simp: D mirrored_sctn_def)
  have 3: "length (fst (lP, uP)) = DIM('a)" "length (snd (lP, uP)) = DIM('a)"
    by (auto simp: lens)
  have 4: "length (normal (((Sctn (unit_list D n) (lP ! n))))) = DIM('a)"
    by (auto simp: D mirrored_sctn_def)
  from guards have guards: "(xs, ro) \<in> set guards \<Longrightarrow>
       ((a, b), ba) \<in> set xs \<Longrightarrow>
       length a = DIM('a) \<and>
       length b = DIM('a) \<and> length (normal ba) = DIM('a)" for xs ro a b ba
    by (auto simp: guards_invar_def)
  have 5: "length (fst (lR, uR)) = CARD('n)" "length (snd (lR, uR)) = CARD('n)"
    "aform.lvivl'_invar (CARD('n) * CARD('n)) None"
    by (auto simp: lens)
  have "poincare_mapsto
    (set_of_lvivl (lP, uP) \<inter>
      plane_of (map_sctn eucl_of_list (mirrored_sctn mirrored (Sctn (unit_list D n) (lP ! n)))))
    (aform.c1_info_of_apprse [((1, 1), aforms_of_ivls lX0 uX0, None)])
    (below_halfspace (map_sctn eucl_of_list (Sctn (unit_list D n) (lP ! n))))
    (aform.Csafe ode_fas safe_form -
      set_of_lvivl (lP, uP) \<inter>
      plane_of (map_sctn eucl_of_list (mirrored_sctn mirrored (Sctn (unit_list D n) (lP ! n)))))
     (set_of_lvivl (lR, uR) \<times> blinfuns_of_lvivl' None)"
    by (rule solves_poincare_map_aform'[OF solves, OF 1 ode_fas 2 3 4 guards 5])
  then have "poincare_mapsto P (X0 \<times> UNIV::('a \<times> ('a \<Rightarrow>\<^sub>L 'a)) set)
      (below_halfspace (map_sctn eucl_of_list (((Sctn (unit_list D n) (lP ! n)))))) UNIV (R \<times> UNIV)"
    apply (rule poincare_mapsto_subset)
    subgoal using X0
      apply (auto simp: aform.c1_info_of_apprse_def aform.c1_info_of_appre_def
          aform.c1_info_of_appr_def)
      apply (rule image_eqI) apply (rule eucl_of_list_list_of_eucl[symmetric])
      apply (rule aforms_of_ivls)
      by (auto simp add: lens subset_iff le_eucl_of_list_iff eucl_of_list_le_iff)
    subgoal by simp
    subgoal using R by (auto simp: set_of_lvivl_def set_of_ivl_def)
    subgoal
      using assms
      by (simp add: below_halfspace_def le_halfspace_def[abs_def])
    subgoal
      using assms
      by (fastforce simp add: P set_of_lvivl_def set_of_ivl_def plane_of_def
          le_eucl_of_list_iff eucl_of_list_le_iff mirrored_sctn_def mirror_sctn_def)  
    done
  then show "\<forall>x\<in>X0. returns_to P x \<and> poincare_map P x \<in> R"
    by (auto simp: poincare_mapsto_def)
qed

end

lemmas [simp] = length_approxs

ML \<open>val ode_numerics_conv = @{computation_check
  terms:
    Trueprop

    Not

    solves_one_step_until_time_aform_fo
    solves_poincare_map_aform'_fo

    num_options
    num_options_c1
    ro

    (* nat *)
    Suc "0::nat" "1::nat" "op +::nat \<Rightarrow> nat \<Rightarrow> nat" "op - ::nat \<Rightarrow> nat \<Rightarrow> nat" "op =::nat\<Rightarrow>nat\<Rightarrow>bool"
    "op ^::nat\<Rightarrow>nat\<Rightarrow>nat"

    (* int / integer*)
    "op =::int\<Rightarrow>int\<Rightarrow>bool"
    "op +::int\<Rightarrow>int\<Rightarrow>int"
    "uminus::_\<Rightarrow>int"
    "uminus::_\<Rightarrow>integer"
    int_of_integer integer_of_int
    "0::int"
    "1::int"
    "op ^::int\<Rightarrow>nat\<Rightarrow>int"

    (* real *)
    "op =::real\<Rightarrow>real\<Rightarrow>bool"
    "real_of_float"
    "op /::real\<Rightarrow>real\<Rightarrow>real"
    "op ^::real\<Rightarrow>nat\<Rightarrow>real"
    "uminus::real\<Rightarrow>_"
    "op +::real\<Rightarrow>real\<Rightarrow>real" "op -::real\<Rightarrow>real\<Rightarrow>real"  "op *::real\<Rightarrow>real\<Rightarrow>real"
    real_divl real_divr
    real_of_int
    "0::real"
    "1::real"

    (* rat *)
    Fract
    "0::rat"
    "1::rat"
    "op +::rat\<Rightarrow>rat\<Rightarrow>rat"
    "op -::rat\<Rightarrow>rat\<Rightarrow>rat"
    "op *::rat\<Rightarrow>rat\<Rightarrow>rat"
    "uminus::rat\<Rightarrow>_"
    "op /::rat\<Rightarrow>rat\<Rightarrow>rat"
    "op ^::rat\<Rightarrow>nat\<Rightarrow>rat"

    (* ereal *)
    "1::ereal"

    (* lists: *)
    "replicate::_\<Rightarrow>real\<Rightarrow>_"
    "unit_list::_\<Rightarrow>_\<Rightarrow>real list"
    "Nil::(nat \<times> nat \<times> string) list"
    "Cons::_\<Rightarrow>_\<Rightarrow>(nat \<times> nat \<times> string) list"
    "Nil::(nat \<times> nat \<times> string \<times> nat list) list"
    "Cons::_\<Rightarrow>_\<Rightarrow>(nat \<times> nat \<times> string \<times> nat list) list"
    "Nil::real list"
    "Cons::_\<Rightarrow>_\<Rightarrow>real list"
    "Nil::nat list"
    "Cons::_\<Rightarrow>_\<Rightarrow>nat list"
    "Nil::string list"
    "Cons::_\<Rightarrow>_\<Rightarrow>string list"
    "Nil::real aform list"
    "Cons::_\<Rightarrow>_\<Rightarrow>real aform list"
    "Nil::(float \<times> float) option list"
    "Cons::_\<Rightarrow>_\<Rightarrow>(float \<times> float) option list"

    "nth::_\<Rightarrow>_\<Rightarrow>real"
    "upt"

    (* products: *)
    "Pair::_\<Rightarrow>_\<Rightarrow>(nat \<times> string)"
    "Pair::_\<Rightarrow>_\<Rightarrow>(nat \<times> nat \<times> string)"

    "Pair::_\<Rightarrow>_\<Rightarrow>char list \<times> nat list"
    "Pair::_\<Rightarrow>_\<Rightarrow>nat \<times> char list \<times> nat list"
    "Pair::_\<Rightarrow>_\<Rightarrow>nat \<times> nat \<times> char list \<times> nat list"

    "Pair::_\<Rightarrow>_\<Rightarrow>char list \<times> ((String.literal \<Rightarrow> unit) \<Rightarrow> (real \<times> real pdevs) numeric_options)"
    "Pair::_\<Rightarrow>_\<Rightarrow>ereal\<times>ereal"
    "Pair::_\<Rightarrow>_\<Rightarrow>real aform list \<times> real aform list option"
    "Pair::_\<Rightarrow>_\<Rightarrow>(ereal \<times> ereal) \<times> real aform list \<times> real aform list option"

    "Pair::_\<Rightarrow>_\<Rightarrow>real aform"
    "Pair::_\<Rightarrow>_\<Rightarrow>real list \<times> real list"

    "Nil::(((real list \<times> real list) \<times> real list sctn) list \<times> (real aform) reach_options) list"
    "Cons::_\<Rightarrow>_\<Rightarrow>(((real list \<times> real list) \<times> real list sctn) list \<times> (real aform) reach_options) list"
    "Nil::((real list \<times> real list) \<times> real list sctn) list"
    "Cons::_\<Rightarrow>_\<Rightarrow>((real list \<times> real list) \<times> real list sctn) list"

    "Pair::_\<Rightarrow>_\<Rightarrow>((real list \<times> real list) \<times> real list sctn) list \<times> real aform reach_options"

    "Nil::((ereal \<times> ereal) \<times> (real aform) list \<times> (real aform) list option) list"
    "Cons::_\<Rightarrow>_\<Rightarrow>((ereal \<times> ereal) \<times> (real aform) list \<times> (real aform) list option) list"

    (* option *)
    "None::(real aform) list option"
    "Some::_\<Rightarrow>(real aform) list option"
    "None::(real list \<times> real list) option"
    "Some::_\<Rightarrow>(real list \<times> real list) option"

    (* aforms *)
    "aform_of_ivl::_\<Rightarrow>_\<Rightarrow>real aform"
    aforms_of_ivls
    aforms_of_point

    (* pdevs*)
    "zero_pdevs::real pdevs"
    "zero_aforms::_ \<Rightarrow> real aform list"

    (* Characters/Strings *)
    String.Char
    String.implode
    "Nil::string"
    "Cons::_\<Rightarrow>_\<Rightarrow>string"

    (* float *)
    "op =::float\<Rightarrow>float\<Rightarrow>bool" "op +::float\<Rightarrow>float\<Rightarrow>float" "uminus::_\<Rightarrow>float" "op -::_\<Rightarrow>_\<Rightarrow>float"
    Float float_of_int float_of_nat

    (* approximation... *)
    approx
    approx1
    approx2
    approxs1
    approxs2
    approx_defined
    approxs_defined

    (* floatarith *)
    "0::floatarith"
    "1::floatarith"
    "op +::_\<Rightarrow>_\<Rightarrow>floatarith"
    "op -::_\<Rightarrow>_\<Rightarrow>floatarith"
    "op *::_\<Rightarrow>_\<Rightarrow>floatarith"
    "op /::_\<Rightarrow>_\<Rightarrow>floatarith"
    "inverse::_\<Rightarrow>floatarith"
    "uminus::_\<Rightarrow>floatarith"
    "Sum\<^sub>e::_\<Rightarrow>nat list\<Rightarrow>floatarith"
    Sin Half Tan
    R\<^sub>e Norm

    (* form *)
    true_form
    Half

    (* Printing *)
    print
    no_print

    (* sections *)
    xsec xsec' ysec ysec' zsec zsec'
    xsec2 xsec2' ysec2 ysec2'
    mirrored_sctn

    Code_Target_Nat.natural
    Code_Target_Int.positive
    Code_Target_Int.negative
    Code_Numeral.positive
    Code_Numeral.negative

  datatypes:
    bool
    num
    floatarith
    "floatarith list"
    form
    "real list sctn"
    "real \<times> real"
}
\<close>
ML \<open>fun ode_numerics_tac ctxt =
  CONVERSION (ode_numerics_conv ctxt) THEN' (resolve_tac ctxt [TrueI])\<close>

lemma eq_einterpretI:
  assumes "list_of_eucl (VS::'a::executable_euclidean_space) = interpret_floatariths fas xs"
  assumes "length fas = DIM('a)"
  shows "VS = eucl_of_list (interpret_floatariths fas xs)"
  using assms
  apply (subst (asm) list_of_eucl_eucl_of_list[symmetric])
  apply (auto intro!: )
  by (metis eucl_of_list_list_of_eucl)

lemma one_add_square_ne_zero[simp]: "1 + t * t \<noteq> 0" for t::real
  by (metis semiring_normalization_rules(12) sum_squares_eq_zero_iff zero_neq_one)

lemma abs_rat_bound:
  "abs (x - y) \<le> e / f" if "y \<in> {yl .. yu}" "x \<in> {yu - real_divl p e f.. yl + real_divl p e f}" for x y e::real
proof -
  note \<open>x \<in> _\<close>
  also have "{yu - real_divl p e f.. yl + real_divl p e f} \<subseteq> {yu - e / f .. yl + e / f}"
    by (auto intro!: diff_mono real_divl)
  finally show ?thesis
    using that
    unfolding abs_diff_le_iff
    by auto
qed

lemma in_ivl_selfI: "a \<in> {a .. a}" for a::real by auto

lemma pi4_bnds: "pi / 4 \<in> {real_divl 80 (lb_pi 80) 4 .. real_divr 80 (ub_pi 80) 4}"
  using pi_boundaries[of 80]
  unfolding atLeastAtMost_iff
  by (intro conjI real_divl[le] real_divr[ge] divide_right_mono) auto

ML \<open>
fun mk_nat n = HOLogic.mk_number @{typ nat} n
fun mk_int n = HOLogic.mk_number @{typ int} n
fun mk_integer n = @{term integer_of_int} $ (HOLogic.mk_number @{typ int} n)
fun mk_bool b = if b then @{term True} else @{term False}

fun mk_numeralT n =
  let
    fun mk_bit 0 ty = Type (@{type_name bit0}, [ty])
      | mk_bit 1 ty = Type (@{type_name bit1}, [ty]);
    fun bin_of n =
      if n = 1 then @{typ num1}
      else if n = 0 then @{typ num0}
      else if n = ~1 then raise TERM ("negative type numeral", [])
      else
        let val (q, r) = Integer.div_mod n 2;
        in mk_bit r (bin_of q) end;
  in bin_of n end;
\<close>

ML \<open>
fun print_tac' ctxt s = K (print_tac ctxt s)

val using_master_directory =
  File.full_path o Resources.master_directory o Proof_Context.theory_of;

fun using_master_directory_term ctxt s =
  (if s = "-" orelse s = ""
  then s
  else
    Path.explode s
    |> using_master_directory ctxt
    |> Path.implode)
  |> HOLogic.mk_string

fun real_in_approx_tac ctxt p =
  let
    val inst_approx =
       ([], [((("prec", 0), @{typ nat}), mk_nat p |> Thm.cterm_of ctxt)])
    val approx_thm = Thm.instantiate inst_approx @{thm real_in_approxI}
  in
    resolve_tac ctxt [approx_thm]
      THEN' SOLVED' (reify_floatariths_tac ctxt)
      THEN' ode_numerics_tac ctxt
  end

fun real_subset_approx_tac ctxt p =
  let
    val inst_approx =
       ([], [((("prec", 0), @{typ nat}), mk_nat p |> Thm.cterm_of ctxt)])
    val approx_thm = Thm.instantiate inst_approx @{thm real_subset_approxI}
  in
    resolve_tac ctxt [approx_thm]
      THEN' SOLVED' (reify_floatariths_tac ctxt)
      THEN' SOLVED' (reify_floatariths_tac ctxt)
      THEN' ode_numerics_tac ctxt
      THEN' ode_numerics_tac ctxt
  end

fun basic_nt_ss ctxt nt =
  put_simpset HOL_basic_ss ctxt addsimps Named_Theorems.get ctxt nt

fun DIM_tac ctxt = (Simplifier.simp_tac (basic_nt_ss ctxt @{named_theorems DIM_simps}))

fun subset_approx_preconds_tac ctxt p thm =
  let
    val inst_approx = ([], [((("prec", 0), @{typ nat}), mk_nat p |> Thm.cterm_of ctxt)])
  in
            resolve_tac ctxt [Thm.instantiate inst_approx thm]
      THEN' SOLVED' (reify_floatariths_tac ctxt)
      THEN' SOLVED' (reify_floatariths_tac ctxt)
      THEN' SOLVED' (DIM_tac ctxt)
      THEN' SOLVED' (DIM_tac ctxt)
      THEN' SOLVED' (ode_numerics_tac ctxt)
      THEN' SOLVED' (ode_numerics_tac ctxt)
  end

fun eucl_subset_approx_tac ctxt p = subset_approx_preconds_tac ctxt p @{thm eucl_subset_approxI}
fun approx_subset_eucl_tac ctxt p = subset_approx_preconds_tac ctxt p @{thm approx_subset_euclI}
fun approx_subset_list_tac ctxt p = subset_approx_preconds_tac ctxt p @{thm approx_subset_listI}

fun integral_bnds_tac d p m N atol filename ctxt i =
  let
    val insts =
       ([((("'i", 0), @{sort "{enum}"}), mk_numeralT (d + 1) |> Thm.ctyp_of ctxt)],
        [((("optns", 0), @{typ "string \<times> ((String.literal \<Rightarrow> unit) \<Rightarrow>(real aform) numeric_options)"}),
           HOLogic.mk_prod
             (using_master_directory_term ctxt filename,
              (@{term num_options} $ mk_nat p $ mk_nat m $ mk_nat N $ mk_int atol $
              @{term "[(0::nat, 1::nat, ''0x000000'')]"}))
          |> Thm.cterm_of ctxt)])
  in
          resolve_tac ctxt [Thm.instantiate insts @{thm solve_one_step_until_time_aform_integral_bounds}] i
    THEN (Lin_Arith.tac ctxt i ORELSE Simplifier.simp_tac ctxt i)
    THEN real_in_approx_tac ctxt p i
    THEN real_in_approx_tac ctxt p i
    THEN approx_subset_eucl_tac ctxt p i
    THEN resolve_tac ctxt @{thms eq_einterpretI} i
    THEN reify_floatariths_tac ctxt i
    THEN DIM_tac ctxt i
    THEN DIM_tac ctxt i
    THEN DIM_tac ctxt i
    THEN DIM_tac ctxt i
    THEN DIM_tac ctxt i
    THEN DIM_tac ctxt i
    THEN print_tac ctxt ""
    THEN ode_numerics_tac ctxt i
  end
\<close>

lemma abs_minus_leI: "\<bar>x - x'\<bar> \<le> e" if "x \<in> {x' - e .. x' + e}" for x e::real
  using that
  by (auto simp: )

lemmas [DIM_simps] = Suc_numeral One_nat_def[symmetric] TrueI Suc_1 length_approxs arith_simps

named_theorems solves_one_step_ivl_thms

context ode_interpretation begin

lemmas [solves_one_step_ivl_thms] =
  TAG_optns[OF solves_one_step_ivl[OF _ _ _ _ _ _ _ _ solves_one_step_until_time_aform_foI], rotated -1,
  of optns _ _ _ _ _ _ _ _ _ optns for optns]

lemmas [solves_one_step_ivl_thms] =
  TAG_optns[OF solves_one_step_ivl'[OF _ _ _ _ _ _ _ _ _ _ _ _ solves_one_step_until_time_aform_foI], rotated -1,
    of optns _ _ _ _ _ _ _ _ _ _ _ _ _ _ optns for optns]

lemmas [solves_one_step_ivl_thms] = solves_poincare_map_aform'I

end

named_theorems nth_list_eq_theorems

lemma [nth_list_eq_theorems]:
  "[a] ! 0 = [a] ! 0"
  "[a, b] ! 0 = [a, c] ! 0"
  "[a, b] ! 1 = [c, b] ! 1"
  "[a, b, d] ! 0 = [a, c, e] ! 0"
  "[a, b, d] ! 1 = [c, b, e] ! 1"
  "[a, b, d] ! 2 = [c, e, d] ! 2"
  by auto

lemma TAG_optnsI: "TAG_optns optns" by simp

named_theorems poincare_tac_theorems

lemmas [DIM_simps] = one_less_numeral_iff rel_simps

ML \<open>
fun mk_proj (m, n, s) = HOLogic.mk_tuple [mk_nat m, mk_nat n, HOLogic.mk_string s]
fun mk_projs projs = HOLogic.mk_list @{typ "nat \<times> nat \<times> string"} (map mk_proj projs)

fun mk_string_list ds = HOLogic.mk_list @{typ "string"} (map HOLogic.mk_string ds)
fun mk_nat_list ds = HOLogic.mk_list @{typ "nat"} (map mk_nat ds)
fun mk_proj_c1 (m, n, s, ds) = HOLogic.mk_tuple [mk_nat m, mk_nat n, HOLogic.mk_string s, mk_nat_list ds]
fun mk_projs_c1 projs = HOLogic.mk_list @{typ "nat \<times> nat \<times> string \<times> nat list"} (map mk_proj_c1 projs)

fun TAG_optns_thm p m N atol projs filename ctxt =
  Thm.instantiate ([],
          [((("optns", 0), @{typ "string \<times> ((String.literal \<Rightarrow> unit) \<Rightarrow>(real aform) numeric_options)"}),
           HOLogic.mk_prod
             (using_master_directory_term ctxt filename,
             @{term num_options} $ mk_nat p $ mk_nat m $ mk_nat N $ mk_int atol $ mk_projs projs)
          |> Thm.cterm_of ctxt)]) @{thm TAG_optnsI}

fun TAG_optns_c1_thm p m N atol projs ds filename ctxt =
  Thm.instantiate ([],
          [((("optns", 0), @{typ "string \<times> ((String.literal \<Rightarrow> unit) \<Rightarrow>(real aform) numeric_options)"}),
           HOLogic.mk_prod
             (using_master_directory_term ctxt filename,
             @{term num_options_c1} $ mk_nat p $ mk_nat m $ mk_nat N $ mk_int atol $ mk_projs_c1 projs $
              mk_string_list ds)
          |> Thm.cterm_of ctxt)]) @{thm TAG_optnsI}

fun ode_bnds_tac ode_def p m N atol projs filename ctxt =
  let
    val ctxt = Context.proof_map (Named_Theorems.add_thm @{named_theorems DIM_simps} ode_def) ctxt
  in
         resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems solves_one_step_ivl_thms})
    THEN' resolve_tac ctxt [TAG_optns_thm p m N atol projs filename ctxt]
    THEN' SOLVED' (real_subset_approx_tac ctxt p)
    THEN' SOLVED' (eucl_subset_approx_tac ctxt p)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (approx_subset_eucl_tac ctxt p)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' CONVERSION (Simplifier.rewrite (empty_simpset ctxt addsimps [ode_def]))
    THEN' ode_numerics_tac ctxt
  end

fun ode'_bnds_tac ode_def p m N atol projs ds filename ctxt =
  let
    val ctxt = Context.proof_map (Named_Theorems.add_thm @{named_theorems DIM_simps} ode_def) ctxt
  in
         resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems solves_one_step_ivl_thms})
    THEN' resolve_tac ctxt [TAG_optns_c1_thm p m N atol projs ds filename ctxt]
    THEN' SOLVED' (real_subset_approx_tac ctxt p)
    THEN' SOLVED' (eucl_subset_approx_tac ctxt p)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (approx_subset_list_tac ctxt p)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (approx_subset_eucl_tac ctxt p)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' CONVERSION (Simplifier.rewrite (empty_simpset ctxt addsimps [ode_def]))
    THEN' ode_numerics_tac ctxt
  end

fun poincare_bnds_tac ode_def p m N atol projs filename ctxt =
  let
    val ctxt = Context.proof_map (Named_Theorems.add_thm @{named_theorems DIM_simps} ode_def) ctxt
  in
         resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems solves_one_step_ivl_thms})
    THEN' resolve_tac ctxt [TAG_optns_thm p m N atol projs filename ctxt]
    THEN' resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems poincare_tac_theorems})
    THEN' resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems poincare_tac_theorems})
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems poincare_tac_theorems})
    THEN' resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems poincare_tac_theorems})
    THEN' resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems nth_list_eq_theorems})
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (eucl_subset_approx_tac ctxt p)
    THEN' (DIM_tac ctxt)
    THEN' SOLVED' (approx_subset_eucl_tac ctxt p)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' CONVERSION (Simplifier.rewrite (empty_simpset ctxt addsimps [ode_def]))
    THEN' ode_numerics_tac ctxt
  end

\<close>

abbreviation "point_ivl a \<equiv> {a .. a}"

lemma isFDERIV_compute: "isFDERIV D vs fas xs \<longleftrightarrow>
   (list_all (\<lambda>i. list_all (\<lambda>j. isDERIV (vs ! i) (fas ! j) xs) [0..<D]) [0..<D]) \<and> length fas = D \<and> length vs = D"
  unfolding isFDERIV_def
  by (auto simp: list.pred_set)


theorem (in ode_interpretation) solves_poincare_map_aform'_derivI'[solves_one_step_ivl_thms]:
\<comment>\<open>TODO: replace @{thm solves_poincare_map_aform'_derivI}\<close>
  assumes "TAG_optns optns"
  assumes "TAG_reach_optns roi"
  assumes "TAG_sctn mirrored"
    and D: "D = DIM('a)"
  assumes DS: "list_interval lDR uDR \<subseteq> list_interval lDS uDS"
    and ode_fas: "length ode_fas = DIM('a)"
    and guards: "guards_invar DIM('a) guards"
    and P: "P = {eucl_of_list lP .. eucl_of_list uP}"
    and plane: "uP ! n = lP ! n"
    and X0: "X0 \<subseteq> {eucl_of_list lX0 .. eucl_of_list uX0}"
    and nD: "n < DIM('a)"
    and R: "{eucl_of_list lR .. eucl_of_list uR} \<subseteq> R"
    and lens:
    "length (lP) = DIM('a)" "length (uP) = DIM('a)"
    "length (lX0) = DIM('a)" "length (uX0) = DIM('a)"
    "length (lR) = DIM('a)" "length (uR) = DIM('a)"
    "length DX0 = DIM('a)*DIM('a)"
    "length lDR = CARD('n) * CARD('n)"
    "length uDR = CARD('n) * CARD('n)"
    and SS: "SS = {x::'a. if mirrored then x \<bullet> Basis_list ! n \<le> lP ! n
        else x \<bullet> Basis_list ! n \<ge> lP ! n}"
  assumes solves:
    "solves_poincare_map_aform'_fo optns ode_fas safe_form
      (mirrored_sctn (\<not>mirrored) (Sctn (unit_list D n) (lP ! n)))
      guards
      (lP, uP)
      (mirrored_sctn mirrored (Sctn (unit_list D n) (lP ! n)))
      roi
      [((1,1), aforms_of_ivls lX0 uX0, Some (aforms_of_point DX0))]
      (lR, uR)
      (Some (lDR, uDR))"
  shows "\<forall>x\<in>X0. returns_to P x \<and>
    return_time P differentiable at x within SS \<and>
    (\<exists>D. (poincare_map P has_derivative blinfun_apply D) (at x within SS) \<and>
         poincare_map P x \<in> R \<and> D o\<^sub>L blinfun_of_list DX0 \<in> blinfuns_of_lvivl (lDS, uDS))"
proof (rule ballI)
  fix x assume "x \<in> X0"
  then have la2: "list_all2 op \<le> lX0 uX0"
    using X0
    by (force simp: subset_iff eucl_of_list_le_iff le_eucl_of_list_iff lens list_all2_conv_all_nth)
  have 1: "\<And>X. X \<in> set [((1::ereal, 1::ereal), aforms_of_ivls lX0 uX0, Some (aforms_of_point DX0))] \<Longrightarrow>
      aform.c1_info_invare DIM('a) X"
    for X
    by (auto simp: aform.c1_info_invare_def aform.c1_info_invar_def lens power2_eq_square)
  have 2: "length (normal (mirrored_sctn (\<not>mirrored) (Sctn (unit_list D n) (lP ! n)))) = DIM('a)"
    by (auto simp: D mirrored_sctn_def)
  have 3: "length (fst (lP, uP)) = DIM('a)" "length (snd (lP, uP)) = DIM('a)"
    by (auto simp: lens)
  have 4: "length (normal (mirrored_sctn mirrored (Sctn (unit_list D n) (lP ! n)))) = DIM('a)"
    by (auto simp: D mirrored_sctn_def)
  have 5: "length (fst (lR, uR)) = CARD('n)" "length (snd (lR, uR)) = CARD('n)"
    "aform.lvivl'_invar (CARD('n) * CARD('n)) (Some (lDR, uDR))"
    by (auto simp: lens aform.lvivl'_invar_def)
  note solves = solves[unfolded solves_poincare_map_aform'_fo_def file_output_iff]
  have "poincare_mapsto
     (set_of_lvivl (lP, uP) \<inter>
      plane_of (map_sctn eucl_of_list (mirrored_sctn mirrored (Sctn (unit_list D n) (lP ! n)))))
     (aform.c1_info_of_apprse [((1, 1), aforms_of_ivls lX0 uX0, Some (aforms_of_point DX0))])
     (below_halfspace (map_sctn eucl_of_list (mirrored_sctn (\<not>mirrored) (Sctn (unit_list D n) (lP ! n)))))
     (aform.Csafe ode_fas safe_form -
      set_of_lvivl (lP, uP) \<inter>
      plane_of (map_sctn eucl_of_list (mirrored_sctn mirrored (Sctn (unit_list D n) (lP ! n)))))
     (set_of_lvivl (lR, uR) \<times> blinfuns_of_lvivl' (Some (lDR, uDR)))"
    by (rule solves_poincare_map_aform'[OF solves, OF 1 ode_fas 4 3 2 _ 5])
      (use guards in \<open>auto simp: guards_invar_def\<close>)
  then have "poincare_mapsto P (X0 \<times> {blinfun_of_list DX0}::('a \<times> ('a \<Rightarrow>\<^sub>L 'a)) set) SS UNIV
    (R \<times> blinfuns_of_lvivl (lDS, uDS))"
    apply (rule poincare_mapsto_subset)
    subgoal using X0
      apply (auto simp: aform.c1_info_of_appre_def aform.c1_info_of_appr_def
          aform.c1_info_of_apprse_def)
      subgoal for x0
        apply (rule image_eqI[where x="list_of_eucl x0@DX0"])
        using lens
         apply (auto simp: flow1_of_list_def aforms_of_point_def aform.set_of_appr_of_ivl_append_point)
        apply (rule imageI)
        using X0
        by (auto simp: Joints_aforms_of_ivls la2 list_of_eucl_in_list_interval_iff)
      done
    subgoal by simp
    subgoal using R DS
      by (auto simp: set_of_lvivl_def set_of_ivl_def blinfuns_of_lvivl'_def blinfuns_of_lvivl_def
          lens)
    subgoal
      using assms
      by (auto simp:
          below_halfspace_def le_halfspace_def[abs_def] mirrored_sctn_def mirror_sctn_def)
    subgoal
      using assms
      by (fastforce simp add: P set_of_lvivl_def set_of_ivl_def plane_of_def
          le_eucl_of_list_iff eucl_of_list_le_iff mirrored_sctn_def mirror_sctn_def)
    done
  then show "returns_to P x \<and>
    return_time P differentiable at x within SS \<and>
    (\<exists>D. (poincare_map P has_derivative blinfun_apply D) (at x within SS) \<and>
         poincare_map P x \<in> R \<and> D o\<^sub>L blinfun_of_list DX0 \<in> blinfuns_of_lvivl (lDS, uDS))"
    using \<open>x \<in> X0\<close>
    by (auto simp: poincare_mapsto_def)
qed

ML \<open>
fun poincare'_bnds_tac ode_def p m N atol projs filename ctxt =
  let
    val ctxt = Context.proof_map (Named_Theorems.add_thm @{named_theorems DIM_simps} ode_def) ctxt
  in
         resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems solves_one_step_ivl_thms})
    THEN' resolve_tac ctxt [TAG_optns_thm p m N atol projs filename ctxt]
    THEN' resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems poincare_tac_theorems})
    THEN' resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems poincare_tac_theorems})
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' approx_subset_list_tac ctxt p
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems poincare_tac_theorems})
    THEN' resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems poincare_tac_theorems})
    THEN' resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems nth_list_eq_theorems})
    THEN' SOLVED' (eucl_subset_approx_tac ctxt p)
    THEN' (DIM_tac ctxt)
    THEN' SOLVED' (approx_subset_eucl_tac ctxt p)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' SOLVED' (DIM_tac ctxt)
    THEN' resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems poincare_tac_theorems})
    THEN' CONVERSION (Simplifier.rewrite
      (empty_simpset ctxt addsimps [ode_def]))
    THEN' ode_numerics_tac ctxt
  end
\<close>

lemma (in auto_ll_on_open) Poincare_Banach_fixed_pointI:
  assumes "convex S" and c: "complete S" "S \<noteq> {}" and "S \<subseteq> T"
  assumes derivative_bounded: "\<forall>x\<in>S.
    poincare_map \<Sigma> x \<in> S \<and> (\<exists>D. (poincare_map \<Sigma> has_derivative D) (at x within T) \<and> onorm D \<le> B)"
  assumes B: "B < 1"
  shows "\<exists>!x. x \<in> S \<and> poincare_map \<Sigma> x = x"
  using c _ B
proof (rule banach_fix)
  from derivative_bounded c show "0 \<le> B"
    by (auto dest!: has_derivative_bounded_linear onorm_pos_le)
  from derivative_bounded show "poincare_map \<Sigma> ` S \<subseteq> S" by auto
  obtain D where D:
    "\<forall>x \<in> S. (poincare_map \<Sigma> has_derivative D x) (at x within T) \<and>
      onorm (D x) \<le> B"
    apply atomize_elim
    apply (rule bchoice)
    using derivative_bounded
    by auto
  with \<open>S \<subseteq> T\<close> have "(\<And>x. x \<in> S \<Longrightarrow> (poincare_map \<Sigma> has_derivative D x) (at x within S))"
    by (auto intro: has_derivative_within_subset)
  from bounded_derivative_imp_lipschitz[of S "poincare_map \<Sigma>" D B, OF this] \<open>convex S\<close> D c
    \<open>0 \<le> B\<close>
  have "lipschitz S (poincare_map \<Sigma>) B" by auto
  then show "\<forall>x\<in>S. \<forall>y\<in>S. dist (poincare_map \<Sigma> x) (poincare_map \<Sigma> y) \<le> B * dist x y"
    by (auto simp: lipschitz_def)
qed

end