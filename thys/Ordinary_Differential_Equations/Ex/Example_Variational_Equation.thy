theory Example_Variational_Equation
imports
  "../Library/Linear_ODE"
(*   "Example_van_der_Pol"
 *)
  "Example_Utilities"
begin

subsection \<open>Variational equation for the van der Pol system\<close>

abbreviation "vdp_real \<equiv> \<lambda>(x::real, y::real). (y, y * (1 + - x*x) + - x)"

abbreviation "of_matrix22 a b c d \<equiv> (\<lambda>(x, y). (a * x + b * y, c * x + d * y))"

lift_definition blinfun_of_matrix22::"real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real \<times> real) \<Rightarrow>\<^sub>L (real \<times> real)"
  is of_matrix22
  by (auto intro!: bounded_linearI' simp: algebra_simps)

definition "vdp_d_blinfun \<equiv> \<lambda>(x, y). blinfun_of_matrix22 0 1 (- (1 + 2 * x * y)) (- x * x + 1)"

interpretation vdp: c1_on_open_euclidean vdp_real vdp_d_blinfun UNIV
  apply unfold_locales
  apply (force intro!: derivative_eq_intros continuous_on_blinfun_componentwise
    intro: continuous_intros
    simp: vdp_d_blinfun_def blinfun_of_matrix22.rep_eq algebra_simps split_beta')+
  done

abbreviation vareq_real::"real * real * real * real * real * real \<Rightarrow> real * real * real * real * real * real"
  where "vareq_real \<equiv> \<lambda>(x, y, a, b, c, d).
  (y, y * (1 + - x*x) + - x,
  c, d,
  - (a * (1 + 2 * x * y)) + c * (- x * x + 1),
  - (b * (1 + 2 * x * y)) + d * (- x * x + 1))"
approximate_affine vareq vareq_real
print_theorems
definition "vareq_euclarith \<equiv> \<lambda>n.
(AddE (ScaleR (realarith.Add
              (realarith.Minus
                (realarith.Mult (realarith.Var n (real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 1, real_of_float 0, real_of_float 0))
                  (realarith.Add (realarith.Num (real_of_float 1))
                    (realarith.Mult
                      (realarith.Mult (realarith.Num (real_of_float 2)) (realarith.Var n (real_of_float 1, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0)))
                      (realarith.Var n (real_of_float 0, real_of_float 1, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0))))))
              (realarith.Mult (realarith.Var n (real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 1))
                (realarith.Add
                  (realarith.Mult (realarith.Minus (realarith.Var n (real_of_float 1, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0)))
                    (realarith.Var n (real_of_float 1, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0)))
                  (realarith.Num (real_of_float 1)))))
      (real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 1))
(AddE (ScaleR (realarith.Add
                (realarith.Minus
                  (realarith.Mult (realarith.Var n (real_of_float 0, real_of_float 0, real_of_float 1, real_of_float 0, real_of_float 0, real_of_float 0))
                    (realarith.Add (realarith.Num (real_of_float 1))
                      (realarith.Mult
                        (realarith.Mult (realarith.Num (real_of_float 2)) (realarith.Var n (real_of_float 1, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0)))
                        (realarith.Var n (real_of_float 0, real_of_float 1, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0))))))
                (realarith.Mult (realarith.Var n (real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 1, real_of_float 0))
                  (realarith.Add
                    (realarith.Mult (realarith.Minus (realarith.Var n (real_of_float 1, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0)))
                      (realarith.Var n (real_of_float 1, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0)))
                    (realarith.Num (real_of_float 1)))))
        (real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 1, real_of_float 0))
  (AddE (ScaleR (realarith.Var n (real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 1))
          (real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 1, real_of_float 0, real_of_float 0))
    (AddE (ScaleR (realarith.Var n (real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 1, real_of_float 0))
            (real_of_float 0, real_of_float 0, real_of_float 1, real_of_float 0, real_of_float 0, real_of_float 0))
      (AddE (ScaleR (realarith.Add
                      (realarith.Mult (realarith.Var n (real_of_float 0, real_of_float 1, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0))
                        (realarith.Add (realarith.Num (real_of_float 1))
                          (realarith.Mult (realarith.Minus (realarith.Var n (real_of_float 1, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0)))
                            (realarith.Var n (real_of_float 1, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0)))))
                      (realarith.Minus (realarith.Var n (real_of_float 1, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0))))
              (real_of_float 0, real_of_float 1, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0))
        (ScaleR (realarith.Var n (real_of_float 0, real_of_float 1, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0))
          (real_of_float 1, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0, real_of_float 0)))))))"

abbreviation vareq_d_real::"real * real * real * real * real * real \<Rightarrow>
    real * real * real * real * real * real \<Rightarrow> real * real * real * real * real * real"
  where "vareq_d_real \<equiv> \<lambda>(x, y, a, b, c, d). \<lambda>(d1, d2, d3, d4, d5, d6).
    (d2, d2 * (1 +- x * x) +- y * (2 * (d1 * x))+- d1, d5, d6,
        d5 * (1 +- x * x) +- c * (2 * (d1 * x)) +- (a * (2 * x * d2 + 2 * d1 * y) + d3 * (1 + 2 * x * y)),
        d6 * (1 +- x * x) +- d * (2 * (d1 * x)) +- (b * (2 * x * d2 + 2 * d1 * y) + d4 * (1 + 2 * x * y)))"

lift_definition vareq_d_blinfun::
  "(real \<times> real \<times> real \<times> real \<times> real \<times> real) \<Rightarrow>
   (real \<times> real \<times> real \<times> real \<times> real \<times> real) \<Rightarrow>\<^sub>L (real \<times> real \<times> real \<times> real \<times> real \<times> real)" is
  vareq_d_real
  by (auto intro!: bounded_linearI' simp: algebra_simps)

lemma vareq_fderiv:
  "(vareq_real has_derivative vareq_d_real x) (at x within X)"
  by (auto intro!: derivative_eq_intros ext simp: split_beta')

setup Locale_Code.open_block
interpretation vareq: aform_approximate_ivp vareq_real "\<lambda>_. True" vareq_euclarith true_euclarithform
  by unfold_locales
    (auto simp add: vareq_euclarith_def plusE_def numeral_eq_Suc
      intro!: ext eq_reflection)
setup Locale_Code.close_block

definition "vareqtest =
  (vareq.one_step_until_time_ivl_listres
    \<lparr>
    precision = 30,
    tolerance = FloatR 1 (- 5),
    stepsize  = FloatR 1 (- 4),
    iterations = 40,
    halve_stepsizes = 10,
    widening_mod = 40,
    rk2_param = 1,
    max_tdev_thres = FloatR 1 (- 8),
    pre_split_summary_tolerance = FloatR 1 (- 1),
    reduce_summary_tolerance = FloatR 1 (- 1),
    collect_granularity = FloatR 1 (- 1),
    start_section = Sctn 0 0,
    checkpoint_sections = [],
    stop_sections = [],
    snap_sections = 0,
    min_section_distance = 0,
    next_section_distance_factor = 0,
    next_section_turn_distance_factor = 0,
    printing_fun = (\<lambda>_ b. print (String.implode ((shows_segments_of_aform (1,0) (0,1,0) b o shows_segments_of_aform (1,0) (0,0,1,0) b) ''''))),
    tracing_fun = (\<lambda>_ _. ()),
    irect_mod = 0,
    max_intersection_step = 0,
    reduce_number_factor = 2,
    adaptive_atol = 0,
    adaptive_rtol = 0,
    adaptive_gtol = 0,
    method_id = 2
  \<rparr>)"

lemma blinfun_apply_vdp_d_blinfun: "blinfun_apply (vdp_d_blinfun x) y =
  (snd y, (- 1 - 2 * fst x * snd x) * fst y + (1 - fst x * fst x) * snd y)"
  by (auto simp: vdp_d_blinfun_def blinfun_of_matrix22.rep_eq split_beta')

text \<open>TODO: generalize?\<close>
lemma vareq_encoding:
  notes [simp del] = add_uminus_conv_diff
  assumes "t \<in> vdp.existence_ivl0 (x0, y0)"
  shows
  "vareq.flow0 (x0, y0, 1, 0, 0, 1) t =
    (let
      xy = vdp.flow0 (x0, y0) t;
      M = vdp.W (x0, y0) t;
      ac = M (1, 0);
      bd = M (0, 1)
    in (fst xy, snd xy, fst ac, fst bd, snd ac, snd bd))"
  (is "?l = ?r")
proof -
  from vdp.total_derivative_ll_on_open[of "(x0, y0)"]
  interpret mvar: ll_on_open "(vdp.existence_ivl0 (x0, y0))" "(\<lambda>t. op o\<^sub>L (vdp.A (x0, y0) t))" "UNIV::((real \<times> real) \<Rightarrow>\<^sub>L (real \<times> real)) set"
    by auto
  have W_eq: "vdp.W (x0, y0) = mvar.flow 0 id_blinfun"
    by (subst vdp.W_def) auto
  have mvar_existence_ivlI: "t \<in> vdp.existence_ivl0 (x0, y0) \<Longrightarrow> t \<in> mvar.existence_ivl 0 id_blinfun" for t
    using vdp.existence_ivl_zero
    by (subst vdp.wholevar_existence_ivl_eq_existence_ivl)
      (auto )
  have "?l = vareq.flow 0 (x0, y0, 1, 0, 0, 1) t"
    by simp
  also have "\<dots> = ?r"
    unfolding diff_0_right
    apply (rule vareq.maximal_existence_flow[where K="vdp.existence_ivl0 (x0, y0)"])
    subgoal
      apply (rule solves_odeI)
      subgoal
        unfolding Let_def
      proof goal_cases
        case hyps: 1
        have eq: "vdp.A (x0, y0) t = vdp_d_blinfun (vdp.flow0 (x0, y0) t)" for t
          unfolding vdp.A_def vdp.XX_def
          by auto
        show ?case
          unfolding at_within_open[OF _ vdp.open_existence_ivl] has_vector_derivative_def
            has_vderiv_on_def W_eq
          apply (rule vdp.flow_has_derivative[THEN has_derivative_at_within], assumption; fail
                | rule mvar.flow_has_derivative[THEN has_derivative_at_within], rule mvar_existence_ivlI, assumption; fail
                | rule derivative_eq_intros ballI refl)+
          unfolding blinfun.bilinear_simps blinfun_apply_vdp_d_blinfun
            blinfun_apply_blinfun_compose eq
          by (auto simp: algebra_simps prod_eq_iff
              intro!: ext simp: blinfun.bilinear_simps split: prod.split)
      qed
      subgoal
        using vdp.existence_ivl_zero
        unfolding Let_def vdp.flow_initial_time_if W_eq mvar.flow_initial_time_if
        by (auto simp:)
      done
    subgoal
      using vdp.existence_ivl_zero
      unfolding Let_def vdp.flow_initial_time_if W_eq mvar.flow_initial_time_if
      by (auto simp:)
    subgoal by (rule mvar.interval)
    subgoal by (intro vdp.existence_ivl_zero UNIV_I)
    subgoal by (rule subset_UNIV)
    subgoal using assms by simp
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
proof -
  have "(fst (blinfun_apply W (1, 0)) * a + fst (blinfun_apply W (0, 1)) * b,
     snd (blinfun_apply W (1, 0)) * a + snd (blinfun_apply W (0, 1)) * b) =
    blinfun_apply W (a, b)" for a b
  proof -
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
    finally show ?thesis by simp
  qed
  then show ?thesis
    by (auto intro!: blinfun_eqI
        simp: blinfun_of_matrix22.rep_eq blinfun.bilinear_simps[symmetric])
qed

lemma compute_vareq:
  assumes "t \<in> vdp.existence_ivl0 (x0, y0)"
  shows
  "(vdp.flow0 (x0, y0) t, vdp.W (x0, y0) t) =
    (let
      (x, y, a, b, c, d) = vareq.flow0 (x0, y0, 1, 0, 0, 1) t
    in ((x, y), blinfun_of_matrix22 a b c d))"
  using vareq_encoding[OF assms]
  by (auto simp: Let_def blinfun_of_matrix22.rep_eq blinfun.bilinear_simps
    blinfun_of_matrix22_works
    intro!: blinfun_eqI)

schematic_goal solve_vareqtest:
  "vareqtest (aform_of_point (FloatR 5 (- 2), FloatR 146 (- 6), 1, 0, 0, 1)) False 2 = ?X"
  by guess_rhs eval

concrete_definition vareq_result uses solve_vareqtest is "_ = dRETURN ?X"

lemma vareq_enclosure: "2 \<in> vareq.existence_ivl0 (FloatR 5 (- 2), FloatR 146 (- 6), 1, 0, 0, 1) \<and>
  vareq.flow0 (FloatR 5 (- 2), FloatR 146 (- 6), 1, 0, 0, 1) 2 \<in> {1.13 .. 1.17} \<times> {-1.05 .. -1.01} \<times>
    {(-0.03, 0.39,
      -0.09, 0.25) ..
      (0.07, 0.45,
      0.01, 0.32)}"
  apply (rule vareq.one_step_until_time_ivl_listres[OF vareq_result.refine[unfolded vareqtest_def] mem_Affine_aform_of_point refl])
  apply (auto simp: vareq_result_def)
  done

end
