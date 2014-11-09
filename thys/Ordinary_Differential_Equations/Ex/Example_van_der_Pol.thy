theory Example_van_der_Pol
imports
  "../Numerics/Euler_Affine"
  "../Numerics/Optimize_Float"
begin

subsection {* Van der Pol oscillator *}
text {*\label{sec:vanderpol}*}
approximate_affine vanderpol "\<lambda>(x::real, y::real). (y, y * (1 + - x*x) + - x)"

lemma vanderpol_fderiv:
  "((\<lambda>(x::real, y::real). (y, y * (1 + - x*x) + - x))
    has_derivative
   (case x of (x, y) \<Rightarrow> \<lambda>(dx, dy). (dy, - (y * (2 * (dx * x))) + dy * (1 + - (x * x)) + - dx)))
   (at x within X)"
  by (auto intro!: derivative_eq_intros simp:  split_beta inverse_eq_divide)

approximate_affine vanderpol_d "\<lambda>(x::real, y) (dx, dy). (dy,
        - (y * (2 * (dx * x))) +
        dy * (1 + - (x * x)) +
        - dx)"

interpretation vanderpol!: aform_approximate_ivp
  "uncurry_options vanderpol"
  "uncurry_options vanderpol_d"
  "\<lambda>(x::real, y::real). (y, y * (1 + - x*x) + - x)"
  "\<lambda>(x::real, y) (dx, dy).
    (dy,
        - (y * (2 * (dx * x))) +
        dy * (1 + - (x * x)) +
        - dx)"
  apply unfold_locales
  apply (rule vanderpol[THEN Joints2_JointsI]) apply assumption apply assumption
  apply (rule vanderpol_fderiv)
  apply (rule vanderpol_d[THEN Joints2_JointsI]) apply assumption apply assumption
  apply (auto intro!: continuous_intros simp: split_beta)
  apply intro_locales
  done

definition "vanderpoltest =
  (poincare_distance_d (uncurry_options vanderpol) (uncurry_options vanderpol_d)
    \<lparr>
    precision = 30,
    tolerance = FloatR 1 (- 5),
    stepsize  = FloatR 1 (- 6),
    min_stepsize = FloatR 1 (- 7),
    iterations = 40,
    halve_stepsizes = 10,
    widening_mod = 40,
    max_tdev_thres = FloatR 1 (- 3),
    presplit_summary_tolerance = FloatR 1 (- 1),
    collect_mod = 30,
    collect_granularity = FloatR 1 (- 4),
    override_section = (\<lambda>b y i s. if snd i > FloatR 149 (- 6) then ((0, 1), FloatR 149 (- 6)) else
      if snd i = FloatR 149 (- 6) \<and> snd s = FloatR 149 (- 6) then (0, 0) else (b, y)),
    global_section = (\<lambda>X. None),
    stop_iteration = (\<lambda>X. False),
    printing_fun = (\<lambda>_ _. print_aform),
    result_fun = ivls_result 20 40
  \<rparr>)"

text {* @{term "vanderpoltest [aform_of_ivl (FloatR 5 (- 2), FloatR 146 (- 6)) (FloatR 49 (- 5), FloatR 149 (- 6))]"}
  proves a stable limit-cycle. *}
value "vanderpoltest [aform_of_ivl (FloatR 5 (- 2), FloatR 146 (- 6)) (FloatR 49 (- 5), FloatR 149 (- 6))]"

end
