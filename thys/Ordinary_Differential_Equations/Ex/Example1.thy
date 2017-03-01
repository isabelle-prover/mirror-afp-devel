section \<open>Examples\<close>
theory Example1
imports
Example_Utilities
begin

subsection \<open>Example 1\<close>
text \<open>\label{sec:example1}\<close>

abbreviation "e1_real \<equiv> \<lambda>(t::real, y::real). (1::real, y*y + - t)"
(* approximate_affine e1 e1_real *)

definition "e1_expr i =
  (AddE
    (ScaleR (Add (Mult (Var i (0, 1)) (Var i (0, 1))) (Minus (Var i (1, 0)))) (0, 1))
    (ScaleR (Num (real_of_float 1)) (1, 0)))"

setup Locale_Code.open_block
interpretation e1: aform_approximate_ivp e1_real "\<lambda>_. True" e1_expr true_euclarithform
  by unfold_locales
    (auto simp add: e1_expr_def plusE_def numeral_eq_Suc
      intro!: ext eq_reflection)
setup Locale_Code.close_block

definition "e1_optns = default_optns
    \<lparr> precision := 30,
      tolerance := FloatR 1 (- 4),
      stepsize  := FloatR 1 (- 3),
      printing_fun := (\<lambda>a b. ()),
      tracing_fun := (\<lambda>_ _. ())\<rparr>"

definition "solve_e1 = e1.one_step_until_time_ivl_listres (e1_optns)"
schematic_goal solve_ivl_e1:
  "solve_e1 (aform_of_point (real_of_float 0, FloatR 23 (- 5))) True 4 = ?X"
  by guess_rhs eval
concrete_definition e1_result uses solve_ivl_e1 is "_ = dRETURN ?X"
definition "e1_reach = map aform_of_list_aform (the (snd (e1_result)))"

lemma e1_enclosures:
   "4 \<in> e1.existence_ivl0 (0, 0.71875) \<and> e1.flow0 (0, 0.71875) 4 \<in> {4} \<times> {- 1.94 .. - 1.90} \<and>
    (\<forall>s \<in> {0 .. 4}. e1.flow0 (0, 0.71875) s \<in> \<Union>(Affine ` set e1_reach))"
  by (rule e1.one_step_until_time_ivl_listres_reachable[OF e1_result.refine[unfolded solve_e1_def]])
    (auto simp: powr_neg_numeral e1_reach_def, auto simp: e1_result_def)

value [code] "
  let
    _ = print (String.implode (gnuplot_box (e1_reach) (Lower 1) [Lower 2, Upper 2]));
    _ = print (String.implode (gnuplot_aform2d (e1_reach) 0 1))
  in ()"

end