theory Example_van_der_Pol
imports
Example_Utilities
begin

subsection \<open>TODO: move to Print\<close>

subsection \<open>Write to Output buffer\<close>

text \<open>Just for debugging purposes\<close>

definition writeln::"String.literal \<Rightarrow> unit" where "writeln x = ()"

code_printing constant writeln \<rightharpoonup> (SML) "writeln"


subsection \<open>Van der Pol oscillator\<close>
text \<open>\label{sec:vdp}\<close>

abbreviation "vdp_real \<equiv> \<lambda>(x::real, y::real). (y, y * (1 + - x*x) + - x)"
approximate_affine vdp vdp_real
print_theorems
definition "vdp_euclarith \<equiv> \<lambda>n.
        (AddE (ScaleR
                (realarith.Add
                  (realarith.Mult (realarith.Var n (real_of_float 0, real_of_float 1))
                    (realarith.Add (realarith.Num (real_of_float 1))
                      (realarith.Mult
                        (realarith.Minus
                          (realarith.Var n (real_of_float 1, real_of_float 0)))
                        (realarith.Var n (real_of_float 1, real_of_float 0)))))
                  (realarith.Minus (realarith.Var n (real_of_float 1, real_of_float 0))))
                (real_of_float 0, real_of_float 1))
          (ScaleR (realarith.Var n (real_of_float 0, real_of_float 1))
            (real_of_float 1, real_of_float 0)))"

setup Locale_Code.open_block
interpretation vdp: aform_approximate_ivp vdp_real "\<lambda>_. True" vdp_euclarith true_euclarithform
  by unfold_locales
    (auto simp add: vdp_euclarith_def plusE_def numeral_eq_Suc
      intro!: ext eq_reflection)
setup Locale_Code.close_block

definition "vdp_optns =
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
    reduce_summary_tolerance = FloatR 0 100,
    collect_granularity = FloatR 1 (- 3),
    start_section = Sctn (0, -1) (- FloatR 100 6),
    checkpoint_sections = [],
    stop_sections = [Sctn (0, -1) (- real_divl 53 225 100)],
    snap_sections = 1,
    min_section_distance = 1/2/2/2,
    next_section_distance_factor = 2,
    next_section_turn_distance_factor = 0,
    printing_fun = (\<lambda>a b.
      print (String.implode (show_segments_of_aform (1, 0) (0, 1) b))
      (* () *)
    ),
    tracing_fun = (\<lambda>a b. ()),
    irect_mod = 6,
    max_intersection_step = FloatR 1 (- 10),
    reduce_number_factor = 2,
    adaptive_atol = FloatR 1 (-30),
    adaptive_rtol = FloatR 1 (-30),
    adaptive_gtol = FloatR 1 (-30),
    method_id = 2
  \<rparr>"

(* width(splitting) Euler, atol, reduction *)
definition vdp_optns'::"int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> (real \<times> real, (real \<times> real) aform) options"
  where "vdp_optns' w m a r = vdp_optns \<lparr>
      collect_granularity := FloatR 1 w,
      max_tdev_thres := FloatR 1 w, (* splitting *)
      adaptive_atol := FloatR 1 a,
      adaptive_rtol := FloatR 1 a,
      adaptive_gtol := FloatR 1 a,
      start_section := if r\<noteq>0 then Sctn (0, -1) (- FloatR 100 (- 6)) else
        Sctn (0, -1) (- FloatR 1 100),
      next_section_distance_factor := if r ~= 0 then 100 else FloatR 1 100,
      next_section_turn_distance_factor := if r ~= 0 then 0 else FloatR 1 100,
      max_intersection_step := FloatR 1 100,
      method_id := nat m\<rparr>"

definition ldecimal::"int \<Rightarrow> int \<Rightarrow> real"
  where "ldecimal m e = (if e \<ge> 0 then real_of_int m * 10 ^ (nat e) else real_divl 53 m (10^(nat (-e))))"
definition udecimal::"int \<Rightarrow> int \<Rightarrow> real"
  where "udecimal m e = (if e \<ge> 0 then real_of_int m * 10 ^ (nat e) else real_divr 53 m (10^(nat (-e))))"

definition
  vdp_limit::"[int, int, int, int, int] \<Rightarrow>_" where
  "vdp_limit w e a r err = vdp.poincare_irects_listres
  (vdp_optns' w e a r)
  (Some [msum_aform' (aform_of_point (ldecimal 130 (-2), udecimal 225 (-2))) (aform_of_ivl 0 (udecimal err (-2), 0))])
  (Some [])"

schematic_goal solve_vdp_limit:
  "vdp_limit (-2) 2 (-9) 1 21 = ?X"
  using [[code_timing]]
  by guess_rhs eval

concrete_definition vdp_result uses solve_vdp_limit is "_ = dRETURN ?X"
definition "vdp_reachi = map_option (map aform_of_list_aform) ((snd (vdp_result)))"
definition "vdp_reach = vdp.set_of_coll Affine vdp_reachi"

definition "vdp_returni = fst (vdp_result)"
definition "vdp_return = vdp.set_of_plane_coll (aform.set_of_irect 6) vdp_returni"

lemma subset_Affine_msum_aform'_point_ivl:
  assumes "l \<le> u"
  assumes "X \<subseteq> {p + l .. p + u}"
  shows "X \<subseteq> Affine (msum_aform' (aform_of_point p) (aform_of_ivl l u))"
  apply (rule subsetI)
  subgoal for x
    using assms
    by (auto simp: aform_of_point_def Affine_aform_of_ivl zero_prod_def Affine_msum_aform
        Affine_aform_of_ivl subset_iff eucl_le[where 'a='a] algebra_simps
        intro!: exI[where x="x - p"] )
  done

lemma
  vdp_invar:
  shows "vdp.flowsto {(1.3, 2.25) .. (1.5, 2.25)} vdp_reach vdp_return"
    "vdp_return \<subseteq> {(1.3, 2.25) .. (1.5, 2.25)}"
proof -
  have decs:
    "udecimal 21 (- 2) = FloatR 15132094747964867 (- 56)"
    "ldecimal 130 (- 2) = FloatR 11709359031163289 (- 53)"
    "udecimal 225 (- 2) = FloatR 9 (- 2)"
    by eval+
  have dec_rat:
    "udecimal 21 (- 2) = 15132094747964867 / 72057594037927936"
    "ldecimal 130 (- 2) = 11709359031163289 / 9007199254740992"
    "udecimal 225 (- 2) = 2.25"
    by (auto simp: powr_minus powr_numeral decs)

  have *: "aform.set_of_irect
     (int (irect_mod (vdp_optns' (- 2) 2 (- 9) 1))) = aform.set_of_irect 6"
    by (auto simp add: vdp_optns'_def vdp_optns_def aform.set_of_irect_def)

  let ?I = "Affine (msum_aform' (aform_of_point (ldecimal 130 (- 2), udecimal 225 (- 2))) (aform_of_ivl 0 (udecimal 21 (- 2), 0)))"

  have subset1: "?I \<subseteq> UNIV \<times> {2.25 .. 2.25}"
    by (auto simp: aform_of_point_def Affine_aform_of_ivl zero_prod_def Affine_msum_aform
      powr_minus powr_numeral dec_rat)

  have subset2: "{(1.3, 2.25) .. (1.5, 2.25)} \<subseteq> ?I"
    by (rule subset_Affine_msum_aform'_point_ivl)
      (auto simp: aform_of_point_def Affine_aform_of_ivl zero_prod_def Affine_msum_aform
        powr_minus powr_numeral dec_rat)
  have "vdp.flowsto
    (vdp.set_of_coll Affine
     (Some [msum_aform' (aform_of_point (ldecimal 130 (- 2), udecimal 225 (- 2)))
     (aform_of_ivl 0 (udecimal 21 (- 2), 0))]))
   (vdp.set_of_coll (\<lambda>(x, xs). Affine (x, pdevs_of_list xs)) (snd vdp_result))
   (vdp.set_of_plane_coll (aform.set_of_irect 6) (fst vdp_result))"
    apply (rule vdp.poincare_irects_listres[OF vdp_result.refine[unfolded vdp_limit_def], unfolded *])
    using subset1
    by (auto simp: vdp.set_of_coll_def vdp_optns'_def le_halfspace_def)
  from this show "vdp.flowsto {(1.3, 2.25) .. (1.5, 2.25)} vdp_reach vdp_return"
    apply (rule vdp.flowsto_subset)
    using subset2
    by (auto simp: vdp.set_of_coll_def vdp_reach_def vdp_return_def vdp_reachi_def vdp_returni_def
        vdp.set_of_plane_coll_def aform_of_list_aform_def
        split: option.split)
  have vdp_result1: "fst vdp_result =
    Some [([86, 144], Sctn (FloatR 0 0, FloatR (- 1) 0) (FloatR (- 9) (- 2))),
            ([87, 144], Sctn (FloatR 0 0, FloatR (- 1) 0) (FloatR (- 9) (- 2))),
            ([88, 144], Sctn (FloatR 0 0, FloatR (- 1) 0) (FloatR (- 9) (- 2))),
            ([89, 144], Sctn (FloatR 0 0, FloatR (- 1) 0) (FloatR (- 9) (- 2))),
            ([90, 144], Sctn (FloatR 0 0, FloatR (- 1) 0) (FloatR (- 9) (- 2))),
            ([91, 144], Sctn (FloatR 0 0, FloatR (- 1) 0) (FloatR (- 9) (- 2))),
            ([92, 144], Sctn (FloatR 0 0, FloatR (- 1) 0) (FloatR (- 9) (- 2))),
            ([93, 144], Sctn (FloatR 0 0, FloatR (- 1) 0) (FloatR (- 9) (- 2))),
            ([94, 144], Sctn (FloatR 0 0, FloatR (- 1) 0) (FloatR (- 9) (- 2)))]"
    unfolding vdp_result_def fst_conv
    by simp
  show "vdp_return \<subseteq> {(1.3, 2.25)..(1.5, 2.25)}"
    by (auto simp: vdp_result1 vdp_return_def vdp.set_of_plane_coll_def vdp_returni_def
      aform.set_of_irect_def vdp_optns_def plane_of_def Basis_list_prod_def Basis_list_real_def
      split: option.split)
qed

text \<open>gnuplot output\<close>
value [code] "writeln (String.implode (gnuplot_aform2d (the vdp_reachi) 0 1))"

end
