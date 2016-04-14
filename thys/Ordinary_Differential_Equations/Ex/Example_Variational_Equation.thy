theory Example_Variational_Equation
imports
  "../Library/Linear_ODE"
  "Example_van_der_Pol"
begin

subsection \<open>Variational equation for the van der Pol system\<close>

lift_definition blinfun_of_matrix22::"real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real \<times> real) \<Rightarrow>\<^sub>L (real \<times> real)"
  is of_matrix22
  by (auto intro!: bounded_linearI' simp: algebra_simps)

definition "vanderpol_d_blinfun \<equiv> \<lambda>(x, y). blinfun_of_matrix22 0 1 (- (1 + 2 * x * y)) (- x * x + 1)"

interpretation vanderpol: c1_on_open_euclidean vanderpol_real vanderpol_d_blinfun UNIV
  apply unfold_locales
  apply (force intro!: derivative_eq_intros continuous_on_blinfun_componentwise
    intro: continuous_intros
    simp: vanderpol_d_blinfun_def blinfun_of_matrix22.rep_eq algebra_simps split_beta')+
  done

abbreviation vareq_real::"real * real * real * real * real * real \<Rightarrow> real * real * real * real * real * real"
  where "vareq_real \<equiv> \<lambda>(x, y, a, b, c, d).
  (y, y * (1 + - x*x) + - x,
  c, d,
  - (a * (1 + 2 * x * y)) + c * (- x * x + 1),
  - (b * (1 + 2 * x * y)) + d * (- x * x + 1))"

approximate_affine vareq vareq_real

abbreviation vareq_d_real::"real * real * real * real * real * real \<Rightarrow>
    real * real * real * real * real * real \<Rightarrow> real * real * real * real * real * real"
  where "vareq_d_real \<equiv> \<lambda>(x, y, a, b, c, d). \<lambda>(d1, d2, d3, d4, d5, d6).
    (d2, d2 * (1 +- x * x) +- y * (2 * (d1 * x))+- d1, d5, d6,
        d5 * (1 +- x * x) +- c * (2 * (d1 * x)) +- (a * (2 * x * d2 + 2 * d1 * y) + d3 * (1 + 2 * x * y)),
        d6 * (1 +- x * x) +- d * (2 * (d1 * x)) +- (b * (2 * x * d2 + 2 * d1 * y) + d4 * (1 + 2 * x * y)))"

approximate_affine vareq_d vareq_d_real

lift_definition vareq_d_blinfun::
  "(real \<times> real \<times> real \<times> real \<times> real \<times> real) \<Rightarrow>
   (real \<times> real \<times> real \<times> real \<times> real \<times> real) \<Rightarrow>\<^sub>L (real \<times> real \<times> real \<times> real \<times> real \<times> real)" is
  vareq_d_real
  by (auto intro!: bounded_linearI' simp: algebra_simps)

lemma vareq_fderiv:
  "(vareq_real has_derivative vareq_d_real x) (at x within X)"
  by (auto intro!: derivative_eq_intros ext simp: split_beta')

interpretation vareq: c1_on_open_euclidean vareq_real vareq_d_blinfun UNIV
  by unfold_locales
    (force intro!: derivative_eq_intros continuous_on_blinfun_componentwise
      intro: continuous_intros
      simp: vareq_d_blinfun.rep_eq algebra_simps split_beta')+

abbreviation "vareq_ivp \<equiv> \<lambda>optns args. uncurry_options vareq optns (hd args) (tl args)"
abbreviation "vareq_d_ivp \<equiv> \<lambda>optns args. uncurry_options vareq_d optns (hd args) (hd (tl args)) (tl (tl args))"

interpretation vareq: aform_approximate_ivp
  vareq_ivp vareq_d_ivp
  vareq_real
  vareq_d_real
  apply unfold_locales
  unfolding list.sel
  apply (rule Joints2_JointsI)
  apply (rule vareq, assumption, assumption)
  apply (drule length_set_of_apprs, simp)\<comment>"TODO: prove in affine-approximation"
  apply (rule vareq_fderiv)
  apply (rule vareq_d[THEN Joints2_JointsI]) apply assumption apply assumption
  apply (drule length_set_of_apprs, simp)\<comment>"TODO: prove in affine-approximation"
  apply (auto intro!: continuous_intros simp: split_beta)
  apply intro_locales
  done

definition "vareqtest =
  (euler_series_result vareq_ivp vareq_d_ivp
    \<lparr>
    precision = 30,
    tolerance = FloatR 1 (- 5),
    stepsize  = FloatR 1 (- 4),
    min_stepsize = FloatR 1 (- 8),
    iterations = 40,
    halve_stepsizes = 10,
    widening_mod = 40,
    max_tdev_thres = FloatR 1 (- 8),
    presplit_summary_tolerance = FloatR 1 (- 1),
    collect_mod = 30,
    collect_granularity = FloatR 1 (- 1),
    override_section = (\<lambda>b y i s. ((0, 1, 0, 0, 0, 0), FloatR 4 (-1))),
    global_section = (\<lambda>X. Some (((0, 1, 0, 0, 0, 0), FloatR 4 (-1)))),
    stop_iteration = (\<lambda>X. True),
    printing_fun = (\<lambda>i t. print_rectangle i i t),
    result_fun = ivls_result 20 40
  \<rparr> 0)"

value[code] "vareqtest (aform_of_point (FloatR 5 (- 2), FloatR 146 (- 6), 1, 0, 0, 1)) 10"

lemma blinfun_apply_vanderpol_d_blinfun: "blinfun_apply (vanderpol_d_blinfun x) y =
  (snd y, (- 1 - 2 * fst x * snd x) * fst y + (1 - fst x * fst x) * snd y)"
  by (auto simp: vanderpol_d_blinfun_def blinfun_of_matrix22.rep_eq split_beta')

text \<open>TODO: generalize?\<close>
lemma vareq_encoding:
  notes [simp del] = add_uminus_conv_diff
  assumes "t \<in> vanderpol.existence_ivl (x0, y0)"
  shows
  "vareq.flow(x0, y0, 1, 0, 0, 1) t =
    (let
      xy = vanderpol.flow (x0, y0) t;
      M = vanderpol.W (x0, y0) t;
      ac = M (1, 0);
      bd = M (0, 1)
    in (fst xy, snd xy, fst ac, fst bd, snd ac, snd bd))"
  (is "?l = ?r")
proof -
  from vanderpol.total_derivative_ll_on_open[of "(x0, y0)"]
  interpret mvar: ll_on_open "(\<lambda>t. op o\<^sub>L (vanderpol.A (x0, y0) t))" "(vanderpol.existence_ivl (x0, y0))" "UNIV::((real \<times> real) \<Rightarrow>\<^sub>L (real \<times> real)) set"
    by auto
  have W_eq: "vanderpol.W (x0, y0) = mvar.flow 0 id_blinfun"
    by (subst vanderpol.W_def) auto
  have mvar_existence_ivlI: "t \<in> vanderpol.existence_ivl (x0, y0) \<Longrightarrow> t \<in> mvar.existence_ivl 0 id_blinfun" for t
    using vanderpol.existence_ivl_zero
    by (subst vanderpol.wholevar_existence_ivl_eq_existence_ivl)
      (auto )
  have "?l = vareq.na.flow 0 (x0, y0, 1, 0, 0, 1) t"
    unfolding vareq.flow_def ..
  also have "\<dots> = ?r"
    apply (rule vareq.na.maximal_existence_flowI[where K="vanderpol.existence_ivl (x0, y0)"])
    unfolding vareq.flow_def[symmetric] W_eq
    subgoal by simp
    subgoal by simp
    subgoal for t
      unfolding Let_def
    proof goal_cases
      case hyps: 1
      have eq: "vanderpol.A (x0, y0) t = vanderpol_d_blinfun (vanderpol.flow (x0, y0) t)"
        unfolding vanderpol.A_def vanderpol.XX_def
        by auto
      show ?case
        unfolding at_within_open[OF hyps vanderpol.open_existence_ivl] has_vector_derivative_def
        apply (rule derivative_eq_intros vanderpol.flow_has_derivative UNIV_I hyps refl
          mvar.flow_has_derivative vanderpol.existence_ivl_zero mvar_existence_ivlI)+
        unfolding blinfun.bilinear_simps eq blinfun_apply_vanderpol_d_blinfun
          blinfun_apply_blinfun_compose
        by (auto simp: algebra_simps prod_eq_iff
          intro!: ext simp: blinfun.bilinear_simps split: prod.split)
    qed
    subgoal by simp
    subgoal by (simp only: vanderpol.existence_ivl_zero mvar.flow_initial_time UNIV_I
        vanderpol.flow_zero blinfun_apply_id_blinfun fst_conv snd_conv Let_def)
    subgoal by (rule vanderpol.is_interval_existence_ivl)
    subgoal by (rule vanderpol.existence_ivl_zero) simp
    subgoal by simp
    subgoal by (rule assms)
    done
  finally show ?thesis .
qed

lemma blinfun_of_matrix22_works:
  fixes W::"(real \<times> real) \<Rightarrow>\<^sub>L (real \<times> real)"
  shows "blinfun_of_matrix22
     (fst (W (1, 0)))
     (fst (W (0, 1)))
     (snd (W (1, 0)))
     (snd (W (0, 1))) = W"
   apply (auto intro!: blinfun_eqI)
   apply (auto simp: blinfun_of_matrix22.rep_eq blinfun.bilinear_simps[symmetric])
proof goal_cases
  case (1 a b)
  have "(fst (W (1, 0)) * a + fst (W (0, 1)) * b, snd (W (1, 0)) * a + snd (W (0, 1)) * b) =
    (fst (a *\<^sub>R W (1, 0)) + fst (b *\<^sub>R W (0, 1)), snd (a *\<^sub>R W (1, 0)) + snd (b *\<^sub>R W (0, 1)))"
    by simp
  also have "\<dots> = (fst (W (a *\<^sub>R (1, 0))) + fst (W (b *\<^sub>R (0, 1))),
    snd (W (a *\<^sub>R (1, 0))) + snd (W (b *\<^sub>R (0, 1))))"
    unfolding blinfun.scaleR_right scaleR_blinfun.rep_eq[symmetric] ..
  also have "\<dots> = (fst (W ((a, 0))) + fst (W ((0, b))), snd (W ((a, 0))) + snd (W ((0, b))))"
    by auto
  also have "\<dots> = (fst (W ((a, 0)) + W ((0, b))), snd (W ((a, 0)) + W ((0, b))))"
    by auto
  also have "\<dots> = (fst (W (a, b)), snd (W (a, b)))"
    unfolding blinfun.add_right[symmetric]
    by auto
  finally show ?case by simp
qed

lemma compute_vareq:
  assumes "t \<in> vanderpol.existence_ivl (x0, y0)"
  shows
  "(vanderpol.flow (x0, y0) t, vanderpol.W (x0, y0) t) =
    (let
      (x, y, a, b, c, d) = vareq.flow (x0, y0, 1, 0, 0, 1) t
    in ((x, y), blinfun_of_matrix22 a b c d))"
  using vareq_encoding[OF assms]
  by (auto simp: Let_def blinfun_of_matrix22.rep_eq blinfun.bilinear_simps
    blinfun_of_matrix22_works
    intro!: blinfun_eqI)

end
