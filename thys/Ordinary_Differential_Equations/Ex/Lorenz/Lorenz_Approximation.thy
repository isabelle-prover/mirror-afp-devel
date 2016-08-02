section"Example: Lorenz attractor"
theory Lorenz_Approximation
imports
  Initials
  "~~/src/HOL/Library/Parallel"
  "../Example_Utilities"
begin
text \<open>\label{sec:lorenz}\<close>

abbreviation "lu == FloatR 6658416365912628 (- 49)"
abbreviation "lss == FloatR (- 6425432926773530) (- 48)"
abbreviation "ls == FloatR (- 6004799503160661) (- 51)"
abbreviation "k1 == FloatR 5198143472295670 (- 54)"
abbreviation "k2 == FloatR 4915166360050299 (- 51)"
abbreviation "k3 == FloatR (- 5777093055467152) (- 52)"

subsection \<open>Lorenz equations in Affine arithmetic\<close>

text \<open>TODO: lorenz -> lorenz-affine, lorenz-real -> lorenz\<close>
abbreviation "lorenz_real \<equiv> \<lambda>(x::real, y::real, z::real).
  (lu*x + -k1*(x + y)*z, lss*y + k1*(x + y)*z, ls*z + (x + y)*(k2*x + k3*y))"
approximate_affine lorenz lorenz_real
print_theorems
definition "lorenz_euclarith \<equiv> \<lambda>n.
  (AddE (ScaleR
          (realarith.Add
            (realarith.Mult (realarith.Num ls)
              (realarith.Var n (real_of_float 0, real_of_float 0, real_of_float 1)))
            (realarith.Mult
              (realarith.Add (realarith.Var n (real_of_float 1, real_of_float 0, real_of_float 0))
                (realarith.Var n (real_of_float 0, real_of_float 1, real_of_float 0)))
              (realarith.Add
                (realarith.Mult (realarith.Num k2)
                  (realarith.Var n (real_of_float 1, real_of_float 0, real_of_float 0)))
                (realarith.Mult (realarith.Num k3)
                  (realarith.Var n (real_of_float 0, real_of_float 1, real_of_float 0))))))
          (real_of_float 0, real_of_float 0, real_of_float 1))
    (AddE (ScaleR
            (realarith.Add
              (realarith.Mult (realarith.Num lss)
                (realarith.Var n (real_of_float 0, real_of_float 1, real_of_float 0)))
              (realarith.Mult
                (realarith.Mult (realarith.Num k1)
                  (realarith.Add (realarith.Var n (real_of_float 1, real_of_float 0, real_of_float 0))
                    (realarith.Var n (real_of_float 0, real_of_float 1, real_of_float 0))))
                (realarith.Var n (real_of_float 0, real_of_float 0, real_of_float 1))))
            (real_of_float 0, real_of_float 1, real_of_float 0))
      (ScaleR
        (realarith.Add
          (realarith.Mult (realarith.Num lu)
            (realarith.Var n (real_of_float 1, real_of_float 0, real_of_float 0)))
          (realarith.Mult
            (realarith.Mult (realarith.Minus (realarith.Num k1))
              (realarith.Add (realarith.Var n (real_of_float 1, real_of_float 0, real_of_float 0))
                (realarith.Var n (real_of_float 0, real_of_float 1, real_of_float 0))))
            (realarith.Var n (real_of_float 0, real_of_float 0, real_of_float 1))))
        (real_of_float 1, real_of_float 0, real_of_float 0))))"

setup Locale_Code.open_block
interpretation lorenz: aform_approximate_ivp lorenz_real "\<lambda>_. True" lorenz_euclarith true_euclarithform
  by unfold_locales
    (auto simp add: lorenz_euclarith_def plusE_def numeral_eq_Suc
      intro!: ext eq_reflection)
setup Locale_Code.close_block

definition shows_segments_of_aform_colored
where "shows_segments_of_aform_colored a b c x =
  shows_list_gen id '''' '''' (''\<newline>'') ''\<newline>'' (map (\<lambda>((x0, y0), (x1, y1)). shows_words (map lfloat10 [x0, y0, x1 - x0, y1 - y0]) o shows_space o shows c)
    (segments_of_aform (inner2_aform x a b)))"

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
    reduce_summary_tolerance = FloatR 0 0,
    collect_granularity = FloatR 1 (- 3),
    start_section = Sctn (0, 0, -1) (- (215/2/2/2)),
    checkpoint_sections = [Sctn (0, 0, 1) 27],
    stop_sections = [Sctn (0, 0, -1) (- 27), Sctn (0, 0, -1) (FloatR (- 25) (- 8))],
    snap_sections = 1/2/2/2/2,
    min_section_distance = 0,
    next_section_distance_factor = 25,
    next_section_turn_distance_factor = 0,
    printing_fun = (\<lambda>a b.
      let
        _ = print (String.implode (shows_segments_of_aform_colored (1, 0, 0) (0, 1, 0) ''0x7f0000'' b ''''));
        _ = print (String.implode (shows_segments_of_aform_colored (1, 0, 0) (0, 0, 1) ''0x007f00'' b ''''));
        _ = print (String.implode (shows_segments_of_aform_colored (0, 1, 0) (0, 0, 1) ''0x00007f'' b ''''))
      in ()
    ),
    tracing_fun = (\<lambda>a b.
      print (String.implode (''# '' @ a @ ''\<newline>''))
    ),
    irect_mod = 8,
    max_intersection_step = FloatR 1 (- 10),
    reduce_number_factor = 2,
    adaptive_atol = FloatR 1 (-30),
    adaptive_rtol = FloatR 1 (-30),
    adaptive_gtol = FloatR 1 (-30),
    method_id = 2
  \<rparr>"

definition lorenz_optns'::"nat \<Rightarrow> nat \<Rightarrow> _"
  where "lorenz_optns' p w = lorenz_optns \<lparr>
      irect_mod := p,
      collect_granularity := FloatR 2 (- int w),
      max_tdev_thres := FloatR 2 (- int w),
      adaptive_atol := FloatR 1 (- int (2 * (w + 1))),
      adaptive_rtol := FloatR 1 (- int (2 * (w + 1))),
      adaptive_gtol := FloatR 1 (- int (2 * (w + 1)))\<rparr>"

definition mirror_irects
  where "mirror_irects =
    map (\<lambda>irect. case irect of [i, j, k] \<Rightarrow> [if j < 0 then - i else i , abs j, k] | irect \<Rightarrow> irect)"

definition "print_irects irects =
  (let _ = map (\<lambda>is.
    let _ = map (\<lambda>j.
      let _ = print (String.implode (show j)) in print (STR '' '')) is in print (STR ''\<newline>'')) irects
  in ())"

definition "lorenz_irects p w i j =
  do {
    let optns = lorenz_optns' p w;
    (stops, _) \<leftarrow> lorenz.poincare_irects_impl optns (Some [aform.set_of_irect_impl p [i, j, 27 * 2 ^ p]]) None;
    let (returns, aborted) = List.partition (\<lambda>x. snd x = Sctn (0, 0, -1) (- 27)) (the stops);
    let irects = mirror_irects (map fst returns);
    let _ = (if length aborted > 0 then
      (let
        _ = print (STR ''= Aborted close to the origin:\<newline>'');
        _ = print_irects (map fst aborted)
      in ())
      else ());
    let _ = print (STR ''= Initial Rectangles of Return:\<newline>'');
    let _ = print_irects irects;
    dRETURN irects
  }"

(*
value [code] "lorenz_irects 8 8 910 21" \<comment>\<open>easy\<close>
value [code] "lorenz_irects 8 8 373 588" \<comment>\<open>harder\<close>
value [code] "lorenz_irects 8 8 198 541" \<comment>\<open>crazy\<close>
*)

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
      method_id := nat m\<rparr>"

definition "decimal x ex = (if ex \<ge> 0 then x * 10 ^ nat ex else real_divl 53 x (10^nat (-ex)))"

definition lorenzc::"[int, int, int, int,int, int, int, int,int, int] \<Rightarrow> _" where
  "lorenzc w m a r x ex y ey u eu =
  lorenz.poincare_irects_impl
  (lorenzc_optns w m a r)
  (Some [msum_aform 53 (aform_of_point (decimal x ex, decimal y ey, 27)) (aform_of_ivl 0 (decimal u eu, decimal u eu, 0))]) None"

end
