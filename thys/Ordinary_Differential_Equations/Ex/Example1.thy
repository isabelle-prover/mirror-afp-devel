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
       [(FloatR 124 (- 5), (FloatR 248 (- 6), FloatR (- 8064333) (- 22)), (FloatR 256 (- 6), FloatR (- 7870071) (- 22)),
         FloatR 128 (- 5), (FloatR 128 (- 5), FloatR (- 8062606) (- 22)), FloatR 128 (- 5), FloatR (- 8045597) (- 22)),
        (FloatR 120 (- 5), (FloatR 240 (- 6), FloatR (- 7895426) (- 22)), (FloatR 248 (- 6), FloatR (- 7675653) (- 22)),
         FloatR 124 (- 5), (FloatR 124 (- 5), FloatR (- 7892990) (- 22)), FloatR 124 (- 5), FloatR (- 7872198) (- 22)),
        (FloatR 116 (- 5), (FloatR 232 (- 6), FloatR (- 7709016) (- 22)), (FloatR 240 (- 6), FloatR (- 7451009) (- 22)),
         FloatR 120 (- 5), (FloatR 120 (- 5), FloatR (- 7705284) (- 22)), FloatR 120 (- 5), FloatR (- 7678377) (- 22)),
        (FloatR 112 (- 5), (FloatR 224 (- 6), FloatR (- 7496651) (- 22)), (FloatR 232 (- 6), FloatR (- 7184402) (- 22)),
         FloatR 116 (- 5), (FloatR 116 (- 5), FloatR (- 7491763) (- 22)), FloatR 116 (- 5), FloatR (- 7454659) (- 22)),
        (FloatR 108 (- 5), (FloatR 216 (- 6), FloatR (- 7246635) (- 22)), (FloatR 224 (- 6), FloatR (- 6856697) (- 22)),
         FloatR 112 (- 5), (FloatR 112 (- 5), FloatR (- 7239665) (- 22)), FloatR 112 (- 5), FloatR (- 7189246) (- 22)),
        (FloatR 104 (- 5), (FloatR 208 (- 6), FloatR (- 6943768) (- 22)), (FloatR 216 (- 6), FloatR (- 6447931) (- 22)),
         FloatR 108 (- 5), (FloatR 108 (- 5), FloatR (- 6934005) (- 22)), FloatR 108 (- 5), FloatR (- 6863200) (- 22)),
        (FloatR 100 (- 5), (FloatR 200 (- 6), FloatR (- 6561315) (- 22)), (FloatR 208 (- 6), FloatR (- 5930812) (- 22)),
         FloatR 104 (- 5), (FloatR 104 (- 5), FloatR (- 6550420) (- 22)), FloatR 104 (- 5), FloatR (- 6456240) (- 22)),
        (FloatR 96 (- 5), (FloatR 192 (- 6), FloatR (- 6076628) (- 22)), (FloatR 200 (- 6), FloatR (- 5272536) (- 22)),
         FloatR 100 (- 5), (FloatR 100 (- 5), FloatR (- 6061774) (- 22)), FloatR 100 (- 5), FloatR (- 5940909) (- 22)),
        (FloatR 92 (- 5), (FloatR 184 (- 6), FloatR (- 5458805) (- 22)), (FloatR 192 (- 6), FloatR (- 4448579) (- 22)),
         FloatR 96 (- 5), (FloatR 96 (- 5), FloatR (- 5441674) (- 22)), FloatR 96 (- 5), FloatR (- 5284333) (- 22)),
        (FloatR 88 (- 5), (FloatR 176 (- 6), FloatR (- 4683021) (- 22)), (FloatR 184 (- 6), FloatR (- 6905460) (- 23)),
         FloatR 92 (- 5), (FloatR 92 (- 5), FloatR (- 4663998) (- 22)), FloatR 92 (- 5), FloatR (- 4461311) (- 22)),
        (FloatR 84 (- 5), (FloatR 168 (- 6), FloatR (- 7460667) (- 23)), (FloatR 176 (- 6), FloatR (- 4608469) (- 23)),
         FloatR 88 (- 5), (FloatR 88 (- 5), FloatR (- 7426779) (- 23)), FloatR 88 (- 5), FloatR (- 6929684) (- 23)),
        (FloatR 80 (- 5), (FloatR 160 (- 6), FloatR (- 5227426) (- 23)), (FloatR 168 (- 6), FloatR (- 4245644) (- 24)),
         FloatR 84 (- 5), (FloatR 84 (- 5), FloatR (- 5204767) (- 23)), FloatR 84 (- 5), FloatR (- 4627778) (- 23)),
        (FloatR 76 (- 5), (FloatR 152 (- 6), FloatR (- 5513954) (- 24)), (FloatR 160 (- 6), FloatR 6302602 (- 27)),
         FloatR 80 (- 5), (FloatR 80 (- 5), FloatR (- 5498016) (- 24)), FloatR 80 (- 5), FloatR (- 4265280) (- 24)),
        (FloatR 72 (- 5), (FloatR 144 (- 6), FloatR (- 7113030) (- 28)), (FloatR 152 (- 6), FloatR 5539800 (- 24)),
         FloatR 76 (- 5), (FloatR 76 (- 5), FloatR (- 7113030) (- 28)), FloatR 76 (- 5), FloatR 6293815 (- 27)),
        (FloatR 68 (- 5), (FloatR 136 (- 6), FloatR 4380170 (- 24)), (FloatR 144 (- 6), FloatR 4837389 (- 23)),
         FloatR 72 (- 5), (FloatR 72 (- 5), FloatR 4380170 (- 24)), FloatR 72 (- 5), FloatR 5528588 (- 24)),
        (FloatR 64 (- 5), (FloatR 128 (- 6), FloatR 4324399 (- 23)), (FloatR 136 (- 6), FloatR 6511166 (- 23)),
         FloatR 68 (- 5), (FloatR 68 (- 5), FloatR 4324399 (- 23)), FloatR 68 (- 5), FloatR 4828558 (- 23)),
        (FloatR 60 (- 5), (FloatR 120 (- 6), FloatR 6078820 (- 23)), (FloatR 128 (- 6), FloatR 7774658 (- 23)),
         FloatR 64 (- 5), (FloatR 64 (- 5), FloatR 6078820 (- 23)), FloatR 64 (- 5), FloatR 6501105 (- 23)),
        (FloatR 56 (- 5), (FloatR 112 (- 6), FloatR 7424189 (- 23)), (FloatR 120 (- 6), FloatR 4330559 (- 22)),
         FloatR 60 (- 5), (FloatR 60 (- 5), FloatR 7424189 (- 23)), FloatR 60 (- 5), FloatR 7764910 (- 23)),
        (FloatR 52 (- 5), (FloatR 104 (- 6), FloatR 8387227 (- 23)), (FloatR 112 (- 6), FloatR 4615550 (- 22)),
         FloatR 56 (- 5), (FloatR 56 (- 5), FloatR 8387227 (- 23)), FloatR 56 (- 5), FloatR 4326315 (- 22)),
        (FloatR 48 (- 5), (FloatR 96 (- 6), FloatR 4511257 (- 22)), (FloatR 104 (- 6), FloatR 4774909 (- 22)),
         FloatR 52 (- 5), (FloatR 52 (- 5), FloatR 4511257 (- 22)), FloatR 52 (- 5), FloatR 4612104 (- 22)),
        (FloatR 44 (- 5), (FloatR 88 (- 6), FloatR 4696759 (- 22)), (FloatR 96 (- 6), FloatR 4837869 (- 22)),
         FloatR 48 (- 5), (FloatR 48 (- 5), FloatR 4696759 (- 22)), FloatR 48 (- 5), FloatR 4772236 (- 22)),
        (FloatR 40 (- 5), (FloatR 80 (- 6), FloatR 4779807 (- 22)), (FloatR 176 (- 7), FloatR 4841539 (- 22)),
         FloatR 44 (- 5), (FloatR 44 (- 5), FloatR 4779807 (- 22)), FloatR 44 (- 5), FloatR 4835855 (- 22)),
        (FloatR 36 (- 5), (FloatR 72 (- 6), FloatR 4729537 (- 22)), (FloatR 80 (- 6), FloatR 4828174 (- 22)),
         FloatR 40 (- 5), (FloatR 40 (- 5), FloatR 4785154 (- 22)), FloatR 40 (- 5), FloatR 4826631 (- 22)),
        (FloatR 32 (- 5), (FloatR 64 (- 6), FloatR 4633037 (- 22)), (FloatR 72 (- 6), FloatR 4763779 (- 22)),
         FloatR 36 (- 5), (FloatR 36 (- 5), FloatR 4732129 (- 22)), FloatR 36 (- 5), FloatR 4762648 (- 22)),
        (FloatR 28 (- 5), (FloatR 56 (- 6), FloatR 4502491 (- 22)), (FloatR 64 (- 6), FloatR 4658144 (- 22)),
         FloatR 32 (- 5), (FloatR 32 (- 5), FloatR 4635000 (- 22)), FloatR 32 (- 5), FloatR 4657307 (- 22)),
        (FloatR 24 (- 5), (FloatR 48 (- 6), FloatR 4345109 (- 22)), (FloatR 56 (- 6), FloatR 4520801 (- 22)),
         FloatR 28 (- 5), (FloatR 28 (- 5), FloatR 4503999 (- 22)), FloatR 28 (- 5), FloatR 4520164 (- 22)),
        (FloatR 20 (- 5), (FloatR 40 (- 6), FloatR 8331605 (- 23)), (FloatR 48 (- 6), FloatR 4358367 (- 22)),
         FloatR 24 (- 5), (FloatR 24 (- 5), FloatR 4346293 (- 22)), FloatR 24 (- 5), FloatR 4357864 (- 22)),
        (FloatR 16 (- 5), (FloatR 32 (- 6), FloatR 7935559 (- 23)), (FloatR 40 (- 6), FloatR 8350607 (- 23)),
         FloatR 20 (- 5), (FloatR 20 (- 5), FloatR 8333519 (- 23)), FloatR 20 (- 5), FloatR 8349765 (- 23)),
        (FloatR 12 (- 5), (FloatR 24 (- 6), FloatR 7505967 (- 23)), (FloatR 32 (- 6), FloatR 7948966 (- 23)),
         FloatR 16 (- 5), (FloatR 16 (- 5), FloatR 7937165 (- 23)), FloatR 16 (- 5), FloatR 7948216 (- 23)),
        (FloatR 8 (- 5), (FloatR 16 (- 6), FloatR 7044785 (- 23)), (FloatR 24 (- 6), FloatR 7515201 (- 23)),
         FloatR 12 (- 5), (FloatR 12 (- 5), FloatR 7507373 (- 23)), FloatR 12 (- 5), FloatR 7514487 (- 23)),
        (FloatR 4 (- 5), (FloatR 8 (- 6), FloatR 6552439 (- 23)), (FloatR 16 (- 6), FloatR 7050907 (- 23)),
         FloatR 8 (- 5), (FloatR 8 (- 5), FloatR 7046074 (- 23)), FloatR 8 (- 5), FloatR 7050182 (- 23)),
        (FloatR 0 0, (FloatR 0 (- 6), FloatR 6028069 (- 23)), (FloatR 8 (- 6), FloatR 6556249 (- 23)), FloatR 4 (- 5),
         (FloatR 4 (- 5), FloatR 6553677 (- 23)), FloatR 4 (- 5), FloatR 6555475 (- 23))])"
  by eval

end
