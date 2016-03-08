section {* Examples *}
theory Example1
imports
  "../Numerics/Euler_Affine"
  "../Numerics/Optimize_Float"
begin

subsection {* Example 1 *}
text {* \label{sec:example1} *}
approximate_affine e1 "\<lambda>(t::real, y::real). (1::real, y*y + - t)"

lemma e1_fderiv: "((\<lambda>(t::real, y::real). (1::real, y * y + - t)) has_derivative (\<lambda>(a, b) (c, d). (0, 2 * (b * d) + - c)) x) (at x within X)"
  by (auto intro!: derivative_eq_intros simp: split_beta)

approximate_affine e1_d "\<lambda>(a::real, b::real) (c::real, d::real). (0::real, 2 * (b * d) + - c)"

abbreviation "e1_ivp \<equiv> \<lambda>optns args. uncurry_options e1 optns (hd args) (tl args)"
abbreviation "e1_d_ivp \<equiv> \<lambda>optns args. uncurry_options e1_d optns (hd args) (hd (tl args)) (tl (tl args))"

interpretation e1: aform_approximate_ivp
  e1_ivp e1_d_ivp
  "\<lambda>(t::real, y::real). (1::real, y*y + - t)"
  "\<lambda>(a::real, b::real) (c::real, d::real). (0::real, 2 * (b * d) + - c)"
  apply unfold_locales
  apply (rule e1[THEN Joints2_JointsI])
  unfolding list.sel apply assumption apply assumption
  apply (drule length_set_of_apprs, simp)--"TODO: prove in affine-approximation"
  apply (rule e1_fderiv)
  apply (rule e1_d[THEN Joints2_JointsI]) apply assumption apply assumption
  apply (drule length_set_of_apprs, simp)--"TODO: prove in affine-approximation"
  apply (auto intro!: continuous_intros simp: split_beta')
  done

definition "e1_optns = default_optns
    \<lparr> precision := 30,
      tolerance := FloatR 1 (- 4),
      stepsize  := FloatR 1 (- 5),
      result_fun := ivls_result 23 4,
      printing_fun := (\<lambda>_ _ _. ())\<rparr>"

definition "e1test = (\<lambda>_::unit. euler_series_result e1_ivp e1_d_ivp e1_optns 0 (aform_of_point (real_of_float 0, FloatR 23 (- 5))) (2 ^ 7))"

lemma e1test_result: "e1test () =
  Some (FloatR 128 (- 5),
       [(FloatR 124 (- 5), (FloatR 248 (- 6), FloatR (- 16128666) (- 23)), (FloatR 256 (- 6), FloatR (- 15740142) (- 23)),
         FloatR 128 (- 5), (FloatR 128 (- 5), FloatR (- 16125211) (- 23)), FloatR 128 (- 5), FloatR (- 16091195) (- 23)),
        (FloatR 120 (- 5), (FloatR 240 (- 6), FloatR (- 15790851) (- 23)), (FloatR 248 (- 6), FloatR (- 15351306) (- 23)),
         FloatR 124 (- 5), (FloatR 124 (- 5), FloatR (- 15785979) (- 23)), FloatR 124 (- 5), FloatR (- 15744397) (- 23)),
        (FloatR 116 (- 5), (FloatR 232 (- 6), FloatR (- 15418032) (- 23)), (FloatR 240 (- 6), FloatR (- 14902020) (- 23)),
         FloatR 120 (- 5), (FloatR 120 (- 5), FloatR (- 15410566) (- 23)), FloatR 120 (- 5), FloatR (- 15356755) (- 23)),
        (FloatR 112 (- 5), (FloatR 224 (- 6), FloatR (- 14993301) (- 23)), (FloatR 232 (- 6), FloatR (- 14368805) (- 23)),
         FloatR 116 (- 5), (FloatR 116 (- 5), FloatR (- 14983525) (- 23)), FloatR 116 (- 5), FloatR (- 14909318) (- 23)),
        (FloatR 108 (- 5), (FloatR 216 (- 6), FloatR (- 14493268) (- 23)), (FloatR 224 (- 6), FloatR (- 13713394) (- 23)),
         FloatR 112 (- 5), (FloatR 112 (- 5), FloatR (- 14479328) (- 23)), FloatR 112 (- 5), FloatR (- 14378493) (- 23)),
        (FloatR 104 (- 5), (FloatR 208 (- 6), FloatR (- 13887534) (- 23)), (FloatR 216 (- 6), FloatR (- 12895863) (- 23)),
         FloatR 108 (- 5), (FloatR 108 (- 5), FloatR (- 13868008) (- 23)), FloatR 108 (- 5), FloatR (- 13726401) (- 23)),
        (FloatR 100 (- 5), (FloatR 200 (- 6), FloatR (- 13122628) (- 23)), (FloatR 208 (- 6), FloatR (- 11861626) (- 23)),
         FloatR 104 (- 5), (FloatR 104 (- 5), FloatR (- 13100837) (- 23)), FloatR 104 (- 5), FloatR (- 12912482) (- 23)),
        (FloatR 96 (- 5), (FloatR 192 (- 6), FloatR (- 12153253) (- 23)), (FloatR 200 (- 6), FloatR (- 10545074) (- 23)),
         FloatR 100 (- 5), (FloatR 100 (- 5), FloatR (- 12123546) (- 23)), FloatR 100 (- 5), FloatR (- 11881819) (- 23)),
        (FloatR 92 (- 5), (FloatR 184 (- 6), FloatR (- 10917605) (- 23)), (FloatR 192 (- 6), FloatR (- 8897159) (- 23)),
         FloatR 96 (- 5), (FloatR 96 (- 5), FloatR (- 10883344) (- 23)), FloatR 96 (- 5), FloatR (- 10568667) (- 23)),
        (FloatR 88 (- 5), (FloatR 176 (- 6), FloatR (- 9366037) (- 23)), (FloatR 184 (- 6), FloatR (- 13810922) (- 24)),
         FloatR 92 (- 5), (FloatR 92 (- 5), FloatR (- 9327991) (- 23)), FloatR 92 (- 5), FloatR (- 8922623) (- 23)),
        (FloatR 84 (- 5), (FloatR 168 (- 6), FloatR (- 14921322) (- 24)), (FloatR 176 (- 6), FloatR (- 9216939) (- 24)),
         FloatR 88 (- 5), (FloatR 88 (- 5), FloatR (- 14853547) (- 24)), FloatR 88 (- 5), FloatR (- 13859369) (- 24)),
        (FloatR 80 (- 5), (FloatR 160 (- 6), FloatR (- 10454837) (- 24)), (FloatR 168 (- 6), FloatR (- 8491289) (- 25)),
         FloatR 84 (- 5), (FloatR 84 (- 5), FloatR (- 10409521) (- 24)), FloatR 84 (- 5), FloatR (- 9255556) (- 24)),
        (FloatR 76 (- 5), (FloatR 152 (- 6), FloatR (- 11027878) (- 25)), (FloatR 160 (- 6), FloatR 12605199 (- 28)),
         FloatR 80 (- 5), (FloatR 80 (- 5), FloatR (- 10996003) (- 25)), FloatR 80 (- 5), FloatR (- 8530561) (- 25)),
        (FloatR 72 (- 5), (FloatR 144 (- 6), FloatR (- 14225580) (- 29)), (FloatR 152 (- 6), FloatR 11079600 (- 25)),
         FloatR 76 (- 5), (FloatR 76 (- 5), FloatR (- 14225580) (- 29)), FloatR 76 (- 5), FloatR 12587625 (- 28)),
        (FloatR 68 (- 5), (FloatR 136 (- 6), FloatR 8760369 (- 25)), (FloatR 144 (- 6), FloatR 9674778 (- 24)),
         FloatR 72 (- 5), (FloatR 72 (- 5), FloatR 8760369 (- 25)), FloatR 72 (- 5), FloatR 11057176 (- 25)),
        (FloatR 64 (- 5), (FloatR 128 (- 6), FloatR 8648812 (- 24)), (FloatR 136 (- 6), FloatR 13022332 (- 24)),
         FloatR 68 (- 5), (FloatR 68 (- 5), FloatR 8648812 (- 24)), FloatR 68 (- 5), FloatR 9657115 (- 24)),
        (FloatR 60 (- 5), (FloatR 120 (- 6), FloatR 12157652 (- 24)), (FloatR 128 (- 6), FloatR 15549315 (- 24)),
         FloatR 64 (- 5), (FloatR 64 (- 5), FloatR 12157652 (- 24)), FloatR 64 (- 5), FloatR 13002210 (- 24)),
        (FloatR 56 (- 5), (FloatR 112 (- 6), FloatR 14848386 (- 24)), (FloatR 120 (- 6), FloatR 8661118 (- 23)),
         FloatR 60 (- 5), (FloatR 60 (- 5), FloatR 14848386 (- 24)), FloatR 60 (- 5), FloatR 15529820 (- 24)),
        (FloatR 52 (- 5), (FloatR 104 (- 6), FloatR 16774461 (- 24)), (FloatR 112 (- 6), FloatR 9231099 (- 23)),
         FloatR 56 (- 5), (FloatR 56 (- 5), FloatR 16774461 (- 24)), FloatR 56 (- 5), FloatR 8652629 (- 23)),
        (FloatR 48 (- 5), (FloatR 96 (- 6), FloatR 9022516 (- 23)), (FloatR 104 (- 6), FloatR 9549818 (- 23)),
         FloatR 52 (- 5), (FloatR 52 (- 5), FloatR 9022516 (- 23)), FloatR 52 (- 5), FloatR 9224207 (- 23)),
        (FloatR 44 (- 5), (FloatR 88 (- 6), FloatR 9393521 (- 23)), (FloatR 96 (- 6), FloatR 9675737 (- 23)),
         FloatR 48 (- 5), (FloatR 48 (- 5), FloatR 9393521 (- 23)), FloatR 48 (- 5), FloatR 9544472 (- 23)),
        (FloatR 40 (- 5), (FloatR 80 (- 6), FloatR 9559617 (- 23)), (FloatR 88 (- 6), FloatR 9683077 (- 23)),
         FloatR 44 (- 5), (FloatR 44 (- 5), FloatR 9559617 (- 23)), FloatR 44 (- 5), FloatR 9671710 (- 23)),
        (FloatR 36 (- 5), (FloatR 72 (- 6), FloatR 9459075 (- 23)), (FloatR 80 (- 6), FloatR 9656348 (- 23)),
         FloatR 40 (- 5), (FloatR 40 (- 5), FloatR 9570310 (- 23)), FloatR 40 (- 5), FloatR 9653261 (- 23)),
        (FloatR 32 (- 5), (FloatR 64 (- 6), FloatR 9266075 (- 23)), (FloatR 72 (- 6), FloatR 9527557 (- 23)),
         FloatR 36 (- 5), (FloatR 36 (- 5), FloatR 9464260 (- 23)), FloatR 36 (- 5), FloatR 9525296 (- 23)),
        (FloatR 28 (- 5), (FloatR 56 (- 6), FloatR 9004983 (- 23)), (FloatR 64 (- 6), FloatR 9316288 (- 23)),
         FloatR 32 (- 5), (FloatR 32 (- 5), FloatR 9270001 (- 23)), FloatR 32 (- 5), FloatR 9314613 (- 23)),
        (FloatR 24 (- 5), (FloatR 48 (- 6), FloatR 8690219 (- 23)), (FloatR 56 (- 6), FloatR 9041602 (- 23)),
         FloatR 28 (- 5), (FloatR 28 (- 5), FloatR 9007999 (- 23)), FloatR 28 (- 5), FloatR 9040328 (- 23)),
        (FloatR 20 (- 5), (FloatR 40 (- 6), FloatR 16663210 (- 24)), (FloatR 48 (- 6), FloatR 8716734 (- 23)),
         FloatR 24 (- 5), (FloatR 24 (- 5), FloatR 8692586 (- 23)), FloatR 24 (- 5), FloatR 8715727 (- 23)),
        (FloatR 16 (- 5), (FloatR 32 (- 6), FloatR 15871119 (- 24)), (FloatR 40 (- 6), FloatR 16701213 (- 24)),
         FloatR 20 (- 5), (FloatR 20 (- 5), FloatR 16667039 (- 24)), FloatR 20 (- 5), FloatR 16699530 (- 24)),
        (FloatR 12 (- 5), (FloatR 24 (- 6), FloatR 15011935 (- 24)), (FloatR 32 (- 6), FloatR 15897932 (- 24)),
         FloatR 16 (- 5), (FloatR 16 (- 5), FloatR 15874331 (- 24)), FloatR 16 (- 5), FloatR 15896432 (- 24)),
        (FloatR 8 (- 5), (FloatR 16 (- 6), FloatR 14089570 (- 24)), (FloatR 24 (- 6), FloatR 15030402 (- 24)),
         FloatR 12 (- 5), (FloatR 12 (- 5), FloatR 15014747 (- 24)), FloatR 12 (- 5), FloatR 15028973 (- 24)),
        (FloatR 4 (- 5), (FloatR 8 (- 6), FloatR 13104879 (- 24)), (FloatR 16 (- 6), FloatR 14101814 (- 24)),
         FloatR 8 (- 5), (FloatR 8 (- 5), FloatR 14092148 (- 24)), FloatR 8 (- 5), FloatR 14100364 (- 24)),
        (FloatR 0 0, (FloatR 0 (- 6), FloatR 12056138 (- 24)), (FloatR 8 (- 6), FloatR 13112497 (- 24)), FloatR 4 (- 5),
         (FloatR 4 (- 5), FloatR 13107355 (- 24)), FloatR 4 (- 5), FloatR 13110949 (- 24))])"
  by eval

end
