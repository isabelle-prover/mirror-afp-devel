theory Example_Lorenz_Classic
imports
Example_Utilities
begin


abbreviation "lorenz_real \<equiv> \<lambda>(x::real, y::real, z::real). (10 * (y + - z), x * (28 + - z) + - y, x*y + - 8 * z * inverse 3)"
approximate_affine lorenz lorenz_real
print_theorems
definition "lorenz_euclarith \<equiv> \<lambda>n.
  (AddE (ScaleR (realarith.Add
                        (realarith.Mult (realarith.Var n (real_of_float 1, real_of_float 0, real_of_float 0))
                          (realarith.Var n (real_of_float 0, real_of_float 1, real_of_float 0)))
                        (realarith.Mult
                          (realarith.Mult (realarith.Minus (realarith.Num (real_of_float 8)))
                            (realarith.Var n (real_of_float 0, real_of_float 0, real_of_float 1)))
                          (realarith.Inverse (realarith.Num (real_of_float 3)))))
                (real_of_float 0, real_of_float 0, real_of_float 1))
          (AddE (ScaleR (realarith.Add
                          (realarith.Mult (realarith.Var n (real_of_float 1, real_of_float 0, real_of_float 0))
                            (realarith.Add (realarith.Num (real_of_float 28))
                              (realarith.Minus (realarith.Var n (real_of_float 0, real_of_float 0, real_of_float 1)))))
                          (realarith.Minus (realarith.Var n (real_of_float 0, real_of_float 1, real_of_float 0))))
                  (real_of_float 0, real_of_float 1, real_of_float 0))
            (ScaleR (realarith.Mult (realarith.Num (real_of_float 10))
                      (realarith.Add (realarith.Var n (real_of_float 0, real_of_float 1, real_of_float 0))
                        (realarith.Minus (realarith.Var n (real_of_float 0, real_of_float 0, real_of_float 1)))))
              (real_of_float 1, real_of_float 0, real_of_float 0))))"

setup Locale_Code.open_block
interpretation lorenz_ivp: aform_approximate_ivp lorenz_real "\<lambda>_. True" lorenz_euclarith true_euclarithform
  by unfold_locales
    (auto simp add: lorenz_euclarith_def plusE_def numeral_eq_Suc
      intro!: ext eq_reflection)
setup Locale_Code.close_block

definition "lorenz_optns =
    \<lparr>
    precision = 53,
    tolerance = FloatR 1 (- 4),
    stepsize  = FloatR 1 (- 8),
    iterations = 40,
    halve_stepsizes = 10,
    widening_mod = 40,
    rk2_param = FloatR 1 (- 1),
    max_tdev_thres = FloatR 1 (- 3),
    pre_split_summary_tolerance = FloatR 1 (- 2),
    reduce_summary_tolerance = FloatR 1 (- 2),
    collect_granularity = FloatR 1 (- 3),
    start_section = Sctn (0, 0, -1) (- (215/2/2/2)),
    checkpoint_sections = [Sctn (0, 0, 1) 36],
    stop_sections = [Sctn (0, 0, -1) (- 36)],
    snap_sections = 1,
    min_section_distance = 1/2/2/2,
    next_section_distance_factor = 25,
    next_section_turn_distance_factor = 0,
    printing_fun = (\<lambda>a b. print (String.implode (show_box_of_aform_hr b))),
    tracing_fun = (\<lambda>a b. ()),
    irect_mod = 5,
    max_intersection_step = FloatR 1 (- 10),
    reduce_number_factor = 2,
    adaptive_atol = FloatR 1 (-30),
    adaptive_rtol = FloatR 1 (-30),
    adaptive_gtol = FloatR 1 (-30),
    method_id = 2
  \<rparr>"

(* width(splitting) Euler, atol, reduction *)
definition lorenz_optns'::"int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "lorenz_optns' w m a r = lorenz_optns \<lparr>
      collect_granularity := FloatR 1 w,
      max_tdev_thres := FloatR 1 w,
      adaptive_atol := FloatR 1 a,
      start_section := if r\<noteq>0 then Sctn (0, -1) (- FloatR 100 (- 6)) else
        Sctn (0, -1) (- FloatR 1 100),
      next_section_distance_factor := if r ~= 0 then 100 else FloatR 1 100,
      next_section_turn_distance_factor := if r ~= 0 then 0 else FloatR 1 100,
      max_intersection_step := FloatR 1 (- 2),
      method_id := nat m\<rparr>"

definition "aform2d_plot_segments x y a = shows_segments_of_aform (Basis_list ! x) (Basis_list ! y) a"

definition lorenzc_optns::"int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "lorenzc_optns w m a r = lorenz_optns \<lparr>
      collect_granularity := FloatR 1 w,
      max_tdev_thres := FloatR 1 w,
      adaptive_atol := FloatR 1 a,
      start_section := if r\<noteq>0 then Sctn (0, 0, -1) (- 24) else
        Sctn (0, -1) (- FloatR 1 100),
      next_section_distance_factor := if r ~= 0 then 100 else FloatR 1 100,
      next_section_turn_distance_factor := if r ~= 0 then 0 else FloatR 1 100,
      max_intersection_step := FloatR 1 (- 2),
      method_id := nat m,
      printing_fun := (\<lambda>a b. ()),
      tracing_fun := (\<lambda>a b. ())
      \<rparr>"

definition "decimal x ex = (if ex \<ge> 0 then x * 10 ^ nat ex else real_divl 53 x (10^nat (-ex)))"

(* uses approximate inital sets, but this is irrelevant for the timings *)
definition lorenzc::"[int, int, int, int,int, int, int, int,int, int] \<Rightarrow> _" where
  "lorenzc w m a r x ex y ey u eu =
  lorenz_ivp.poincare_irects_listres
  (lorenzc_optns w m a r)
  (Some [msum_aform 53 (aform_of_point (decimal x ex, decimal y ey, 36)) (aform_of_ivl 0 (decimal u eu, decimal u eu, 0))])
  (Some [])"

schematic_goal solve_lorenzc:
  "lorenzc
    (1)      (* maxwidth *)
    2         (* method = rk2*)
    (-10)      (* absolute tolerance *)
    1         (* reduce *)
    (-61) (0)   (* x = 15 *)
    17 (0)  (* y = 22 *)
    0 0       (* uncertainty = 0*)
  =
  ?X"
  by guess_rhs eval
concrete_definition lorenzc_result uses solve_lorenzc is "_ = dRETURN ?X"
definition "lorenzc_reach = map aform_of_list_aform (the (snd (lorenzc_result)))"

value [code] "
  let
    _ = print (String.implode (gnuplot_aform2d (lorenzc_reach) 0 2));
    _ = print (String.implode (gnuplot_aform2d (lorenzc_reach) 1 2));
    _ = print (String.implode (gnuplot_aform2d (lorenzc_reach) 0 1))
  in ()"

end
