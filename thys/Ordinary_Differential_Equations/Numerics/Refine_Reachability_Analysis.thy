theory Refine_Reachability_Analysis
imports
  Abstract_Reachability_Analysis
begin

lemma list_of_eucl_of_env:
  assumes [simp]: "length xs = DIM('a)"
  shows "(list_of_eucl (eucl_of_env xs vs::'a)) = (map (\<lambda>i. vs ! (xs ! i)) [0..<DIM('a::executable_euclidean_space)])"
  by (auto intro!: nth_equalityI simp: eucl_of_env_def eucl_of_list_inner)

context approximate_sets_options
begin

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

lemma safe_at_within: "x \<in> Csafe \<Longrightarrow> at x = at x within Csafe"
  by (subst (2) at_within_open)  (auto simp: open_safe)

lemma ivlflowsD:
  assumes "ivlflows stops stopcont trap rsctn" "ivl \<subseteq> \<Union>(plane_of ` stops) \<times> UNIV "
  shows "ivl \<subseteq> (snd (stopcont ivl))"
    "(fst (stopcont ivl)) \<subseteq> sbelow_halfspace rsctn \<times> UNIV"
    "fst (stopcont ivl) \<subseteq> snd (stopcont ivl)"
    "(snd (stopcont ivl)) \<subseteq> sbelow_halfspace rsctn \<times> UNIV"
    "flowsto (ivl) {0..} ((snd (stopcont ivl))) ((fst (stopcont ivl)) \<union> trap)"
  using assms(1)[unfolded ivlflows_def, rule_format, OF assms(2)]
  by auto

lemma ivlflows_flowsto:
  assumes "ivlflows stops stopcont trap rsctn" "ivl \<subseteq> \<Union>(plane_of ` stops) \<times> UNIV"
  assumes "stopcont ivl = (x, y)"
  shows "flowsto (ivl) {0..} y (x \<union> trap)"
  using ivlflowsD[OF assms(1,2)] assms(3)
  by auto

lemma ivlflows_emptyI: "ivlflows {} (\<lambda>x. (x, x)) J K"
  by (auto simp: ivlflows_def set_of_ivl_def)

lemma plane_of_neg[simp]: "plane_of (Sctn (- normal sctn) (- pstn sctn)) = plane_of sctn"
  by (auto simp: plane_of_def)

lemmas safe_max_Var_le[intro] = safe_max_Var[le]

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

end

context approximate_sets_ode_slp
begin

lemma mk_safe[le, refine_vcg]: "wd TYPE('a::executable_euclidean_space)\<Longrightarrow>
  mk_safe X \<le> SPEC (\<lambda>R::'a set. R = X \<and> X \<subseteq> Csafe)"
  unfolding mk_safe_def
  by refine_vcg

lemma mk_safe_coll[le, refine_vcg]: "wd TYPE('a::executable_euclidean_space) \<Longrightarrow>
    mk_safe_coll X \<le> SPEC (\<lambda>R::'a set. R = X \<and> X \<subseteq> Csafe)"
  unfolding mk_safe_coll_def autoref_tag_defs
  by (refine_vcg FORWEAK_invarI[where I="\<lambda>a b. X = \<Union>b \<union> a \<and> a \<subseteq> Csafe"]) auto


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

lemma ncc_interval: "ncc {a .. b::'a::executable_euclidean_space} \<longleftrightarrow> a \<le> b"
  by (auto simp: ncc_def)
lemma nonempty_interval: "nonempty {a .. b::'a::executable_euclidean_space} \<longleftrightarrow> a \<le> b"
  by (auto simp: nonempty_def)

lemmas [refine_vcg] = Picard_step_def[THEN eq_refl, THEN order.trans]

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

subsubsection \<open>Picard iteration\<close>

lemma inf_le_supI[simp]:
  fixes a b c d::"'d::ordered_euclidean_space"
  shows
    "a \<le> c \<Longrightarrow> inf a b \<le> sup c d"
    "a \<le> d \<Longrightarrow> inf a b \<le> sup c d"
    "b \<le> c \<Longrightarrow> inf a b \<le> sup c d"
    "b \<le> d \<Longrightarrow> inf a b \<le> sup c d"
  by (auto simp: eucl_le[where 'a='d] eucl_inf[where 'a='d] eucl_sup[where 'a='d] inf_real_def sup_real_def
    intro!: sum_mono scaleR_right_mono)

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
      apply (rule subsetD[of CX' "{l .. u}"])
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
lemma Ball_cfuncset_continuous_on:
  "\<forall>f\<in>cfuncset a b X. continuous_on {a..b} f"
  by (simp add: cfuncset_iff)

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

lemma choose_step_flowpipe[le, refine_vcg]:
  assumes "wd_step TYPE('a::executable_euclidean_space)"
  shows "choose_step X0 h \<le> SPEC (\<lambda>(h', _, RES_ivl, (RES::'a set)). 0 < h' \<and> h' \<le> h \<and> flowpipe0 X0 h' h' RES_ivl RES)"
  using wd_stepD[OF \<open>wd_step _\<close>]
  unfolding choose_step_def autoref_tag_defs
  by (split if_split) (safe intro!: rk2_step_flowpipe euler_step_flowpipe)

lemma wd_step_wdD:
  "wd_step TYPE('a::executable_euclidean_space) \<Longrightarrow> wd TYPE('a)"
  by (auto simp: wd_step_def)

end

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

context approximate_sets_ode_slp'
begin

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
       (concat (map (\<lambda>j. map (\<lambda>i. FDERIV_floatarith (ode_e ! j) [0..<D] ((replicate D 0)[i := 1])) [0..<D]) [0..<D]))
       (map floatarith.Var [D..<D + D * D])) (list_of_eucl x)) =
    matrix (blinfun_apply (ode_d 0 (fst x) 0)) ** snd x"
    unfolding matrix_eq
    apply auto
    apply (subst matrix_vector_mul_assoc[symmetric])
    apply (subst matrix_works)
    subgoal by (auto simp: linear_matrix_vector_mul_eq
          intro!: bounded_linear.linear blinfun.bounded_linear_right)
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

context includes blinfun.lifting begin
lemma flow1_of_vec1_vec1_of_flow1[simp]:
  "flow1_of_vec1 (vec1_of_flow1 X) = X"
  unfolding vec1_of_flow1_def flow1_of_vec1_def
  by (transfer) auto
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

lemma sps_eqD: "sps_eq \<Longrightarrow> i < D \<Longrightarrow> solve_poincare_slp ! i = slp_of_fas (map fold_const_fa (solve_poincare_fas i))"
  by (auto simp: sps_eq_def)

lemma sps_lengthD: "sps_eq \<Longrightarrow> length solve_poincare_slp = D"
  by (auto simp: sps_eq_def)

lemma sps_length_le:
  assumes sps_eq
  shows "i < D \<Longrightarrow> length (solve_poincare_slp ! i) \<ge> length (solve_poincare_fas i)"
  by (auto simp: sps_eqD[OF \<open>sps_eq\<close>] intro!: order_trans[OF _ length_slp_of_fas_le])


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
  using assms by (auto simp: vwd_step_def)

lemma vwd_stepD2:
  assumes "vwd_step TYPE('n::enum)" "has_c1_slps"
  shows "var.ode_slp_eq ode_slp'"
    "var.rk2_slp_eq rk2_slp' (D + D * D)"
    "var.euler_slp_eq euler_slp' (D + D * D)"
    "var.euler_incr_slp_eq euler_incr_slp' (D + D * D)"
  using assms by (auto simp: vwd_step_def ode_slp'_def rk2_slp'_def euler_slp'_def
      euler_incr_slp'_def has_c1_slps_def split: option.splits)

lemma vwd_step[refine_vcg, intro]:
  assumes "vwd_step TYPE('n::enum)" has_c1_slps
  shows "var.wd_step TYPE('n::enum vec1)"
  using assms
  unfolding var.wd_step_def 
  by (auto simp: vwd_step_def ode_slp'_def has_c1_slps_def rk2_slp'_def euler_slp'_def euler_incr_slp'_def split: option.splits)

lemma choose_step'_flowpipe:
  assumes wd[refine_vcg]: "vwd_step TYPE('n::enum)" and nn[refine_vcg]: "has_c1_slps"
  notes wd' = vwd_stepD[OF wd] vwd_stepD2[OF wd nn]
  assumes safe: "fst ` X0 \<subseteq> Csafe"
  shows "var.choose_step (X0::'n vec1 set) h \<le> SPEC (\<lambda>(h', _, RES_ivl, RES::'n vec1 set).
      0 < h' \<and> h' \<le> h \<and> flowpipe (flow1_of_vec1 ` X0) h' h' (flow1_of_vec1 ` RES_ivl) (flow1_of_vec1 ` RES))"
  apply refine_vcg
  apply (auto simp: )
  apply (frule var.flowpipe0_safeD)
  apply (drule var_flowpipe0_flowpipe[rotated])
  by (auto simp: safe_eq wd')

lemma intersects_sctns_spec_nres[le, refine_vcg]:
  "intersects_sctns X' sctns \<le> intersects_sctns_spec X' sctns"
  unfolding intersects_sctns_spec_def intersects_sctns_def
  by refine_vcg auto

lemma intersects_sections_spec_clw_ref[le, refine_vcg]:
  "intersects_sctns_spec_clw R sctns \<le> intersects_sctns_spec R sctns"
  unfolding intersects_sctns_spec_def intersects_sctns_spec_clw_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>S b. \<not>b \<longrightarrow> \<Union>S \<inter> \<Union>(plane_of ` sctns) = {}"]) auto

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

lemma nonzero_component[le, refine_vcg]: "nonzero_component s X n \<le> SPEC (\<lambda>_. \<forall>b\<in>X. b \<bullet> n \<noteq> 0)"
  unfolding nonzero_component_def
  by refine_vcg auto

end

context approximate_sets_ode_slp' begin

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
  apply (refine_vcg choose_step'_flowpipe[le] vwd_stepD[OF vwd] vwd_stepD2[OF vwd])
     apply (auto simp: image_image)
    apply (auto simp: wd_step_def vwd_stepD flowpipe0_imp_flowpipe env_len_def)
  by (auto simp: safe_eq vwd_step_def vec1_of_flow1_def)

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

lemma disjoints_spec[le, refine_vcg]:
  "disjoints_spec X Y \<le> SPEC (\<lambda>b. b \<longrightarrow> (X \<inter> Y = {}))"
  unfolding disjoints_spec_def autoref_tag_defs
  by refine_vcg auto

lemma fst_safe_coll[le, refine_vcg]:
  "wd TYPE('a) \<Longrightarrow>
      fst_safe_coll (X::('a::executable_euclidean_space*'c) set) \<le> SPEC (\<lambda>R. R = fst ` X \<and> fst ` X \<subseteq> Csafe)"
  unfolding fst_safe_coll_def
  by refine_vcg

lemma vec1reps[THEN order_trans, refine_vcg]: "vec1reps CX \<le> SPEC (\<lambda>R. case R of None \<Rightarrow> True | Some X \<Rightarrow> X = vec1_of_flow1 ` CX)"
  unfolding vec1reps_def
  apply (refine_vcg FORWEAK_mono_rule[where
        I="\<lambda>XS R. case R of None \<Rightarrow> True | Some R \<Rightarrow> vec1_of_flow1 ` (\<Union>XS) \<subseteq> R \<and> R \<subseteq> vec1_of_flow1 ` CX"])
  by (auto simp:  split: option.splits) force+

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
  qed (use prems in \<open>auto elim!: abs_in_BasisE simp: eucl_le[where 'a='a] dest!: bspec subsetD\<close>)
  subgoal by simp
  subgoal by (auto elim!: abs_in_BasisE simp: eucl_le[where 'a='a] dest!: bspec subsetD cong del: image_cong_simp)
  subgoal by (auto elim!: abs_in_BasisE simp: eucl_le[where 'a='a] dest!: bspec subsetD cong del: image_cong_simp)
  done

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
      apply (rule subsetD, assumption)
      apply (drule bspec)
       apply (rule subsetD; assumption)
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

lemma nonzero_component_within[le, refine_vcg]:
  assumes wdp: "vwd_step (TYPE('n::enum))"
  notes [refine_vcg] = vwd_step vwd_stepD[OF wdp]
  shows "nonzero_component_within ivl sctn (PDP::'n eucl1 set) \<le> SPEC (\<lambda>b.
    (b \<longrightarrow> (\<forall>x\<in>PDP. fst x \<in> ivl \<and> (\<forall>\<^sub>F x in at (fst x) within plane_of sctn. x \<in> ivl))) \<and>
    fst ` PDP \<subseteq> Csafe \<and>
    (\<forall>x\<in>PDP. ode (fst x) \<bullet> normal sctn \<noteq> 0))"
  unfolding nonzero_component_within_def
  by refine_vcg auto

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

lemma cancel_times_UNIV_subset: "A \<times> UNIV \<subseteq> B \<times> UNIV \<longleftrightarrow> A \<subseteq> B"
  by auto

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
     apply (rule subsetD)
      apply assumption
     apply auto
  done

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

lemma reduce_spec1[le, refine_vcg]: "reduce_spec1 ro X \<le> SPEC (\<lambda>R. X \<subseteq> R)"
  unfolding reduce_spec1_def
  by refine_vcg auto

lemma reduce_spec1e[le, refine_vcg]: "reduce_spec1e ro X \<le> SPEC (\<lambda>R. X \<subseteq> R)"
  unfolding reduce_spec1e_def
  by refine_vcg (auto simp: scaleR2_def image_def vimage_def, force)

lemma split_spec_coll_spec[le,refine_vcg]:
  "split_spec_coll X \<le> SPEC (\<lambda>(A, B). X \<subseteq> A \<union> B)"
  unfolding split_spec_coll_def
  by (refine_vcg)

lemma split_under_threshold[le, refine_vcg]:
  "split_under_threshold t th X \<le> SPEC (\<lambda>R. X \<subseteq> R)"
  unfolding split_under_threshold_def autoref_tag_defs
  by (refine_vcg) auto

lemma step_split[le, refine_vcg]:
  "wd TYPE((real, 'n::enum) vec) \<Longrightarrow> step_split roptns (X::'n eucl1 set) \<le> SPEC (\<lambda>Y. X \<subseteq> Y \<and> fst ` Y \<subseteq> Csafe)"
  unfolding step_split_def
  by (refine_vcg refine_vcg) auto

lemma tolerate_error_SPEC[THEN order_trans, refine_vcg]:
  "tolerate_error Y E \<le> SPEC (\<lambda>b. True)"
  unfolding tolerate_error_def
  by refine_vcg


lemma interpret_adapt_stepsize_fa:
  "interpret_floatarith (adapt_stepsize_fa e h') []
    = float_of h' * (float_of(adaptive_rtol optns) / float_of e) powr (1 / (float_of (method_id optns) + 1))"
  by (auto simp: inverse_eq_divide adapt_stepsize_fa_def)

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

lemma pre_intersection_step[THEN order_trans, refine_vcg]:
  "pre_intersection_step ro (X::'n eucl1 set) h \<le> SPEC (\<lambda>(X', CX, G). X \<subseteq> X' \<union> G \<and> X \<union> X' \<union> G \<subseteq> CX \<times> UNIV)"
  if [refine_vcg]: "wd TYPE('n::enum rvec)"
  unfolding pre_intersection_step_def autoref_tag_defs
  by (refine_vcg) auto

lemma [THEN order_trans, refine_vcg]: "select_with_inter ci a \<le> SPEC (\<lambda>_. True)"
  unfolding select_with_inter_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>_ _. True"])

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
       apply (rule subsetD)
        apply assumption
       apply auto
    done
  subgoal by force
  subgoal
    apply (rule scaleR2_subset)
       apply (rule subsetD)
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

context approximate_sets_ode_slp' begin

lemma subset_iplane_coll[THEN order_trans, refine_vcg]:
  "subset_iplane_coll x ics \<le> SPEC (\<lambda>b. b \<longrightarrow> x \<subseteq> ics)"
  unfolding subset_iplane_coll_def
  apply refine_vcg
  subgoal for X icss
    by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>ic b. b \<longrightarrow> X \<subseteq> \<Union>(icss)"]) auto
  done

lemma subsets_iplane_coll[THEN order_trans, refine_vcg]:
  "subsets_iplane_coll x ics \<le> SPEC (\<lambda>b. b \<longrightarrow> \<Union>x \<subseteq> ics)"
  unfolding subsets_iplane_coll_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>x b. (b \<longrightarrow> \<Union>x \<subseteq> ics)"]) auto

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
    "X = \<Union> (f ` ((\<lambda>g. g \<union> trap) ` Gs))"
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
       apply (rule subsetD, assumption)
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
         apply (rule subsetD, assumption)
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

lemma op_inter_fst_coll[le, refine_vcg]: "op_inter_fst_coll X Y \<le> SPEC (\<lambda>R. R = X \<inter> Y \<times> UNIV)"
  unfolding op_inter_fst_coll_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs R. \<Union>Xs \<inter> Y \<times> UNIV \<subseteq> R \<and> R \<subseteq> X \<inter> Y \<times> UNIV"])
    auto

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

lemma op_enlarge_ivl_sctn[le, refine_vcg]:
  "op_enlarge_ivl_sctn ivl sctn d \<le> SPEC (\<lambda>ivl'. ivl \<subseteq> ivl')"
  unfolding op_enlarge_ivl_sctn_def
  apply refine_vcg
  unfolding plane_of_def
  apply (safe intro!: eventually_in_planerectI)
  apply (auto  intro!: simp: eucl_le[where 'a='a] inner_sum_left inner_Basis if_distrib
     algebra_simps cong: if_cong)
  done

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

lemma empty_remainders[le, refine_vcg]:
  "empty_remainders PS \<le> SPEC (\<lambda>b. b \<longrightarrow> (\<forall>(X, P1, P2, R, ivl, sctn, CX) \<in> PS. R = {}))"
  unfolding empty_remainders_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs b. b \<longrightarrow> (\<forall>(X, P1, P2, R, ivl, sctn, CX) \<in> Xs. R = {})"])
     auto

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
            from prems have "finite (q ` m)" "flowsto (R0 (a, b, b', c, d, e, f, g)) {0..} (g \<times> UNIV) (\<Union>(q ` m))"
              by auto
            from flowsto_Union_funE[OF this]
            obtain XGs where
              XGs: "\<And>G. G \<in> q ` m \<Longrightarrow> flowsto (XGs G) {0..} (g \<times> UNIV) G"
              "R0 (a, b, b', c, d, e, f, g) = \<Union>(XGs ` (q ` m))"
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
                "\<Union>(q ` m) \<subseteq> CXS \<times> UNIV"
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

lemma width_spec_ivl[THEN order_trans, refine_vcg]: "width_spec_ivl M X \<le> SPEC (\<lambda>x. True)"
  unfolding width_spec_ivl_def
  by (refine_vcg)

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

lemma op_inter_fst_ivl_coll_scaleR2[le,refine_vcg]:
  "op_inter_fst_ivl_coll_scaleR2 X Y \<le> SPEC (\<lambda>R. X \<inter> (Y \<times> UNIV) = R)"
  unfolding op_inter_fst_ivl_coll_scaleR2_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs R. (\<Union>Xs) \<inter> (Y \<times> UNIV) \<subseteq> R \<and> R \<subseteq> X \<inter> (Y \<times> UNIV)"])
    auto

lemma op_inter_ivl_coll_scaleR2[le,refine_vcg]:
  "op_inter_ivl_coll_scaleR2 X Y \<le> SPEC (\<lambda>R. X \<inter> (Y \<times> UNIV) \<subseteq> R)"
  unfolding op_inter_ivl_coll_scaleR2_def
  apply refine_vcg
  apply (auto simp: scaleR2_def image_def vimage_def)
  apply (drule subsetD)
   apply (rule IntI, assumption, force)
  apply auto apply force
  done

lemma [le, refine_vcg]: "op_image_fst_ivl_coll X \<le> SPEC (\<lambda>R. R = fst ` X)"
  unfolding op_image_fst_ivl_coll_def
  apply (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs R. fst ` (\<Union>Xs) \<subseteq> R \<and> R \<subseteq> fst ` X"])
     apply auto
  apply force+
  done

lemma op_single_inter_ivl[le, refine_vcg]: "op_single_inter_ivl a fxs \<le> SPEC (\<lambda>R. a \<inter> fxs \<subseteq> R)"
  unfolding op_single_inter_ivl_def
  by refine_vcg auto

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

end

context approximate_sets_ode_slp' begin

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

lemma reduce_ivle[le, refine_vcg]:
  "reduce_ivle Y b \<le> SPEC (\<lambda>R. Y \<subseteq> R)"
  unfolding reduce_ivle_def
  apply refine_vcg
  apply (auto simp: scaleR2_def image_def vimage_def)
  subgoal for a b c d e f g h i j k
    apply (drule subsetD, assumption)
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


lemma reduces_ivle[le, refine_vcg]:
  "reduces_ivle X \<le> SPEC (\<lambda>R. X \<subseteq> R)"
  unfolding reduces_ivle_def
  by refine_vcg auto

lemma ivlse_of_setse[le, refine_vcg]: "ivlse_of_setse X \<le> SPEC (\<lambda>R. X \<subseteq> R)"
  unfolding ivlse_of_setse_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs R. \<Union>Xs \<subseteq> R"])
    (auto simp: scaleR2_def image_def vimage_def)

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



lemma partition_set_spec[le, refine_vcg]:
  shows "partition_set ro XS \<le> SPEC (\<lambda>YS. XS \<subseteq> YS)"
  unfolding partition_set_def autoref_tag_defs
  apply (refine_vcg)
  subgoal by (fastforce simp: scaleR2_def vimage_def image_def)
  subgoal by fastforce
  done

lemma partition_sets_spec[le, refine_vcg]:
  shows "partition_sets ro XS \<le> SPEC (\<lambda>YS. (\<Union>(_, _, PS, _, _, _, _, _) \<in> XS. PS) \<subseteq> YS)"
  unfolding partition_sets_def autoref_tag_defs
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>X Y. (\<Union>(_, _, PS, _, _, _, _, _) \<in> X. PS) \<subseteq> Y"]) auto

lemma poincare_mapsto_UnionI:
  assumes pm[unfolded poincare_mapsto_def, rule_format]: "\<And>i. i \<in> I \<Longrightarrow> poincare_mapsto p (X0 i) S (CX i) (X1 i)"
  assumes R: "\<And>i x. i \<in> I \<Longrightarrow> x \<in> X1 i \<Longrightarrow> x \<in> R"
  shows "poincare_mapsto p (\<Union>x\<in>I. X0 x) S ((\<Union>x\<in>I. CX x)) R"
  unfolding poincare_mapsto_def
proof (safe del: conjI, goal_cases)
  case (1 x0 d0 i)
  moreover
  have "fst ` \<Union>(X0 ` I) \<subseteq> S"
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

lemma subset_spec1[refine_vcg]: "subset_spec1 R P dP \<le> SPEC (\<lambda>b. b \<longrightarrow> R \<subseteq> flow1_of_vec1 ` (P \<times> dP))"
  unfolding subset_spec1_def
  by refine_vcg (auto simp: vec1_of_flow1_def)


lemma subset_spec1_coll[le, refine_vcg]:
  "subset_spec1_coll R P dP \<le> subset_spec R (flow1_of_vec1 ` (P \<times> dP))"
  unfolding autoref_tag_defs subset_spec_def subset_spec1_coll_def
  by (refine_vcg) (auto simp: subset_iff set_of_ivl_def)

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

lemma ivl_of_eucl1_coll[THEN order_trans, refine_vcg]: "ivl_of_eucl_coll X \<le> SPEC (\<lambda>R. X \<times> UNIV \<subseteq> R)"
  unfolding ivl_of_eucl_coll_def
  by refine_vcg auto

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
    apply (rule subsetD, assumption)
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

context approximate_sets_options' begin

lemma init_ode_solver[le, refine_vcg]:
  assumes [simp]: "length ode_e = CARD('n::enum)"
  shows "init_ode_solver u \<le> SPEC (\<lambda>(D, ode_slp, euler_incr_slp, euler_slp, rk2_slp, solve_poincare_slp,
    c1_slps).
      CARD('n) = D \<and>
      vwd_step D ode_slp euler_incr_slp euler_slp rk2_slp c1_slps solve_poincare_slp TYPE('n))"
  unfolding init_ode_solver_def wd_step_def vwd_step_def
  apply (refine_vcg)
        apply (auto simp: var.rk2_slp_eq_def var.euler_slp_eq_def wd_def
      ode_slp_eq_def var.ode_slp_eq_def rk2_slp_eq_def euler_slp_eq_def euler_incr_slp_eq_def
      sps_eq_def)
  by (auto simp: var.euler_incr_slp_eq_def rk2_fas'_def euler_fas'_def euler_incr_fas'_def
      var.rk2_fas'_def var.euler_fas'_def var.euler_incr_fas'_def)

lemma empty_symstart_flowsto:
  "X0 \<subseteq> Csafe \<times> UNIV \<Longrightarrow>
    RETURN ({}, X0) \<le> SPEC (\<lambda>(CX, X). flowsto (X0 - {} \<times> UNIV) {0..} (CX \<times> UNIV) X)"
  by (auto intro!: flowsto_self)

subsection \<open>Poincare map returning to\<close>

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


subsection \<open>Poincare map onto (from outside of target)\<close>


lemma poincare_ontoa[le, refine_vcg]:
  assumes [simp]: "length ode_e = CARD('n::enum)"
  shows "poincare_ontoa guards ivl sctn ro (XS0::'n eucl1 set) \<le> SPEC
     (\<lambda>P.
        wd (length ode_e) TYPE((real, 'n) vec) \<and>
        poincare_mapsto (ivl \<inter> plane_of sctn) XS0 UNIV (Csafe - ivl \<inter> plane_of sctn) P)"
  unfolding poincare_ontoa_def autoref_tag_defs
  by (refine_vcg) (auto dest!: vwd_stepD(1) simp: do_intersection_spec_def Int_def stable_on_def intro!: flowsto_self)



subsection \<open>One step method (reachability in time)\<close>


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
  by (auto simp add: c0_info_of_appr'_def the_default_eq intro!: c0_info_of_apprsI split: option.splits)

lemmas rel_prod_br = br_rel_prod

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

lemmas lvivl_relI = lv_relivl_relI

lemma lvivl_default_relI:
  "(dRi, set_of_lvivl' dRi::'e::executable_euclidean_space set) \<in> \<langle>lvivl_rel\<rangle>default_rel UNIV"
  if "lvivl'_invar DIM('e) dRi"
  using that
  by (auto simp: set_of_lvivl'_def set_of_lvivl_def set_of_ivl_def lvivl'_invar_def
      intro!: mem_default_relI lvivl_relI)

end

end
