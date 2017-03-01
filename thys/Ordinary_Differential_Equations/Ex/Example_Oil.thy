theory Example_Oil
imports
Example_Utilities
begin

subsection \<open> Oil reservoir in Affine arithmetic \<close>
text \<open>\label{sec:exampleoil}\<close>
abbreviation "oil_real \<equiv> \<lambda>(y::real, z::real). (z, z*z + -3 * inverse (inverse 1000 + y*y))"
approximate_affine oil oil_real
print_theorems
definition "oil_euclarith \<equiv> \<lambda>n.
        (AddE (ScaleR
                (realarith.Add
                  (realarith.Mult (realarith.Var n (real_of_float 0, real_of_float 1))
                    (realarith.Var n (real_of_float 0, real_of_float 1)))
                  (realarith.Mult (realarith.Minus (realarith.Num (real_of_float 3)))
                    (realarith.Inverse
                      (realarith.Add (realarith.Inverse (realarith.Num (real_of_float 1000)))
                        (realarith.Mult (realarith.Var n (real_of_float 1, real_of_float 0))
                          (realarith.Var n (real_of_float 1, real_of_float 0)))))))
                (real_of_float 0, real_of_float 1))
          (ScaleR (realarith.Var n (real_of_float 0, real_of_float 1))
            (real_of_float 1, real_of_float 0)))"

lemma oil_deriv_ok: fixes y::real
shows "1 / 1000 + y*y = 0 \<longleftrightarrow> False"
proof -
  have "1 / 1000 + y*y > 0"
    by (auto intro!: add_pos_nonneg)
  thus ?thesis by auto
qed

setup Locale_Code.open_block
interpretation oil: aform_approximate_ivp oil_real "\<lambda>_. True" oil_euclarith true_euclarithform
  by unfold_locales
    (auto simp add: oil_euclarith_def plusE_def numeral_eq_Suc oil_deriv_ok
      intro!: ext eq_reflection)
setup Locale_Code.close_block

definition "oil_optns =
  \<lparr>
    precision = 50,
    tolerance = FloatR 1 (- 4),
    stepsize  = FloatR 1 (- 8),
    iterations = 40,
    halve_stepsizes = 40,
    widening_mod = 40,
    rk2_param = FloatR 1 0,
    max_tdev_thres = FloatR 1 (- 3),
    pre_split_summary_tolerance = FloatR 0 1,
    reduce_summary_tolerance = FloatR 0 1,
    collect_granularity = FloatR 1 (- 3),
    start_section = Sctn (-1, 0) 10,
    checkpoint_sections = [](*[ Sctn (0, -1) 5, Sctn (0, -1) 13, Sctn (0, -1) 20]*),
    stop_sections = [Sctn (-1, 0) 10],
    snap_sections = 1,
    min_section_distance = 1/2/2/2,
    next_section_distance_factor = FloatR 1 1, (* intersections *)
    next_section_turn_distance_factor = FloatR 1 1,  (* intersections *)
    printing_fun = (\<lambda>a b.
      ()
      (* print (String.implode (show_segments_of_aform (1, 0) (0, 1) b)) *)
      (* print (String.implode ((lshows_eucl (fst b) o shows_nl) [])) *)
    ),
    tracing_fun = (\<lambda>a b.
      ()
      (* print (String.implode (''# '' @ a @ ''\<newline>'')) *)
      (* print (String.implode (''%'' @ a @ '':\<newline>'' @ (case b of Some b \<Rightarrow> show_box_of_aform_hr b @ show_aform_hr b | None \<Rightarrow> '''') @''\<newline>'')) *)
    ),
    irect_mod = 11,
    max_intersection_step = FloatR 1 (100), (* use regular steps *)
    reduce_number_factor = 0,
    adaptive_atol = FloatR 1 (-30),
    adaptive_rtol = FloatR 1 (-30),
    adaptive_gtol = FloatR 1 (-30),
    method_id = 2
  \<rparr>"

definition oil_optns'::"int \<Rightarrow> _"
  where "oil_optns' w = oil_optns \<lparr>
      collect_granularity := FloatR 1 100, (* no splitting*)
      max_tdev_thres := FloatR 1 100, (* no splitting*)
      adaptive_atol := FloatR 1 w,
      adaptive_rtol := FloatR 1 w,
      adaptive_gtol := FloatR 1 w,
      method_id := 1\<rparr>"

definition "solve_oil w x0 = oil.poincare_irects_listres (oil_optns' w) (Some [x0]) None"

schematic_goal solve_ivl_oil:
  "solve_oil (-13) (aform_of_point (10, 0)) = ?X"
  by guess_rhs eval

concrete_definition oil_result uses solve_ivl_oil is "_ = dRETURN ?X"

lemma oil_final_enclosure: "oil.flowsto {(10, 0)} UNIV ({-10} \<times> {-0.1841 .. -0.1826})"
proof -
  have "oil.set_of_coll Affine (Some [aform_of_point (10, 0)]) \<subseteq> Collect (le_halfspace (start_section (oil_optns' (- 13))))"
    by (auto simp: oil.set_of_coll_def le_halfspace_def oil_optns'_def oil_optns_def)
  from oil.poincare_irects_listres[OF oil_result.refine[unfolded solve_oil_def] this]
  have "oil.flowsto (oil.set_of_coll Affine (Some [aform_of_point (10, 0)]))
   (oil.set_of_coll (\<lambda>(x, xs). Affine (x, pdevs_of_list xs)) (snd oil_result))
   (oil.set_of_plane_coll (aform.set_of_irect 11) (fst oil_result))"
    (is "oil.flowsto ?X ?CX ?Y")
    by (simp add: oil_optns'_def oil_optns_def)
  also have "?X = {(10, 0)}"
    by (auto simp: oil.set_of_coll_def)
  also have "?CX = UNIV"
    by (auto simp: oil_result_def oil.set_of_coll_def)
  also have "?Y = {(-10, - 377 / 2048) .. (-10, - 187 / 1024)}"
    by (auto simp: oil_result_def oil.set_of_plane_coll_def oil_optns'_def oil_optns_def
        aform.set_of_irect_def Basis_list_prod_def Basis_list_real_def plane_of_def
        divide_simps)
  finally show ?thesis
    by (rule oil.flowsto_subset) auto
qed

end
