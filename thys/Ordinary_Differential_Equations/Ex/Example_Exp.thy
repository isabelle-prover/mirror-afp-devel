theory Example_Exp
imports
  "../Numerics/Euler_Affine"
  "../Numerics/Optimize_Float"
begin

subsection {* Example Exponential *}

text {* TODO: why not exp-ivp "lambda x::real. x"? *}

approximate_affine exp_affine "\<lambda>(x::real, y::real). (x, y)"

lemma exp_ivp_fderiv: "((\<lambda>(x::real, y::real). (x, y)) has_derivative (\<lambda>(a, b) (h\<^sub>1, h\<^sub>2). (h\<^sub>1, h\<^sub>2 + 0 *a*b)) x) (at x within X)"
  by (auto intro!: derivative_eq_intros simp: split_beta id_def)

approximate_affine exp_d "(\<lambda>(a::real, b::real) (h\<^sub>1::real, h\<^sub>2::real). (h\<^sub>1, h\<^sub>2 + 0 *a*b))"

abbreviation "exp_ivp \<equiv> \<lambda>optns args. uncurry_options exp_affine optns (hd args) (tl args)"
abbreviation "exp_d_ivp \<equiv> \<lambda>optns args. uncurry_options exp_d optns (hd args) (hd (tl args)) (tl (tl args))"

interpretation exp_ivp: aform_approximate_ivp
  exp_ivp
  exp_d_ivp
  "\<lambda>(y\<^sub>1, y\<^sub>2). (y\<^sub>1, y\<^sub>2)"
  "\<lambda>(a, b) (h\<^sub>1, h\<^sub>2). (h\<^sub>1, h\<^sub>2 + 0 *a*b)"
  apply standard
  apply (rule exp_affine[THEN Joints2_JointsI])
  unfolding list.sel
  apply assumption apply assumption
  apply (drule length_set_of_apprs, simp)--"TODO: prove in affine-approximation"
  apply (rule exp_ivp_fderiv)
  apply (rule exp_d[THEN Joints2_JointsI]) apply assumption apply assumption
  apply (drule length_set_of_apprs, simp)--"TODO: prove in affine-approximation"
  apply (auto intro!: continuous_intros simp: split_beta)
  done

definition "exp_optns = default_optns
    \<lparr> precision := 40,
      tolerance := FloatR 1 (- 9),
      stepsize  := FloatR 1 (- 6),
      result_fun := ivls_result 23 1,
      iterations := 40,
      widening_mod := 10,
      printing_fun := (\<lambda>_ _ _. ())\<rparr>"

definition "exptest = (\<lambda>_::unit. euler_series_result exp_ivp exp_d_ivp exp_optns 0
  (aform_of_point (1, 1)) (2 ^ 6))"

lemma "exptest () = Some (FloatR 64 (- 6),
       [(FloatR 63 (- 6), (FloatR 11224084 (- 22), FloatR 11224084 (- 22)), (FloatR 11402234 (- 22), FloatR 11402234 (- 22)),
         FloatR 64 (- 6), (FloatR 11400841 (- 22), FloatR 11400841 (- 22)), FloatR 11402234 (- 22), FloatR 11402234 (- 22)),
        (FloatR 62 (- 6), (FloatR 11050078 (- 22), FloatR 11050078 (- 22)), (FloatR 11225445 (- 22), FloatR 11225445 (- 22)),
         FloatR 63 (- 6), (FloatR 11224095 (- 22), FloatR 11224095 (- 22)), FloatR 11225445 (- 22), FloatR 11225445 (- 22)),
        (FloatR 61 (- 6), (FloatR 10878769 (- 22), FloatR 10878769 (- 22)), (FloatR 11051396 (- 22), FloatR 11051396 (- 22)),
         FloatR 62 (- 6), (FloatR 11050088 (- 22), FloatR 11050088 (- 22)), FloatR 11051396 (- 22), FloatR 11051396 (- 22)),
        (FloatR 60 (- 6), (FloatR 10710117 (- 22), FloatR 10710117 (- 22)), (FloatR 10880046 (- 22), FloatR 10880046 (- 22)),
         FloatR 61 (- 6), (FloatR 10878779 (- 22), FloatR 10878779 (- 22)), FloatR 10880046 (- 22), FloatR 10880046 (- 22)),
        (FloatR 59 (- 6), (FloatR 10544078 (- 22), FloatR 10544078 (- 22)), (FloatR 10711353 (- 22), FloatR 10711353 (- 22)),
         FloatR 60 (- 6), (FloatR 10710126 (- 22), FloatR 10710126 (- 22)), FloatR 10711353 (- 22), FloatR 10711353 (- 22)),
        (FloatR 58 (- 6), (FloatR 10380614 (- 22), FloatR 10380614 (- 22)), (FloatR 10545275 (- 22), FloatR 10545275 (- 22)),
         FloatR 59 (- 6), (FloatR 10544088 (- 22), FloatR 10544088 (- 22)), FloatR 10545275 (- 22), FloatR 10545275 (- 22)),
        (FloatR 57 (- 6), (FloatR 10219684 (- 22), FloatR 10219684 (- 22)), (FloatR 10381773 (- 22), FloatR 10381773 (- 22)),
         FloatR 58 (- 6), (FloatR 10380623 (- 22), FloatR 10380623 (- 22)), FloatR 10381773 (- 22), FloatR 10381773 (- 22)),
        (FloatR 56 (- 6), (FloatR 10061249 (- 22), FloatR 10061249 (- 22)), (FloatR 10220805 (- 22), FloatR 10220805 (- 22)),
         FloatR 57 (- 6), (FloatR 10219693 (- 22), FloatR 10219693 (- 22)), FloatR 10220805 (- 22), FloatR 10220805 (- 22)),
        (FloatR 55 (- 6), (FloatR 9905270 (- 22), FloatR 9905270 (- 22)), (FloatR 10062334 (- 22), FloatR 10062334 (- 22)),
         FloatR 56 (- 6), (FloatR 10061258 (- 22), FloatR 10061258 (- 22)), FloatR 10062334 (- 22), FloatR 10062334 (- 22)),
        (FloatR 54 (- 6), (FloatR 9751710 (- 22), FloatR 9751710 (- 22)), (FloatR 9906319 (- 22), FloatR 9906319 (- 22)),
         FloatR 55 (- 6), (FloatR 9905279 (- 22), FloatR 9905279 (- 22)), FloatR 9906319 (- 22), FloatR 9906319 (- 22)),
        (FloatR 53 (- 6), (FloatR 9600530 (- 22), FloatR 9600530 (- 22)), (FloatR 9752723 (- 22), FloatR 9752723 (- 22)),
         FloatR 54 (- 6), (FloatR 9751718 (- 22), FloatR 9751718 (- 22)), FloatR 9752723 (- 22), FloatR 9752723 (- 22)),
        (FloatR 52 (- 6), (FloatR 9451693 (- 22), FloatR 9451693 (- 22)), (FloatR 9601509 (- 22), FloatR 9601509 (- 22)),
         FloatR 53 (- 6), (FloatR 9600537 (- 22), FloatR 9600537 (- 22)), FloatR 9601509 (- 22), FloatR 9601509 (- 22)),
        (FloatR 51 (- 6), (FloatR 9305164 (- 22), FloatR 9305164 (- 22)), (FloatR 9452639 (- 22), FloatR 9452639 (- 22)),
         FloatR 52 (- 6), (FloatR 9451701 (- 22), FloatR 9451701 (- 22)), FloatR 9452639 (- 22), FloatR 9452639 (- 22)),
        (FloatR 50 (- 6), (FloatR 9160907 (- 22), FloatR 9160907 (- 22)), (FloatR 9306078 (- 22), FloatR 9306078 (- 22)),
         FloatR 51 (- 6), (FloatR 9305171 (- 22), FloatR 9305171 (- 22)), FloatR 9306078 (- 22), FloatR 9306078 (- 22)),
        (FloatR 49 (- 6), (FloatR 9018886 (- 22), FloatR 9018886 (- 22)), (FloatR 9161789 (- 22), FloatR 9161789 (- 22)),
         FloatR 50 (- 6), (FloatR 9160914 (- 22), FloatR 9160914 (- 22)), FloatR 9161789 (- 22), FloatR 9161789 (- 22)),
        (FloatR 48 (- 6), (FloatR 8879067 (- 22), FloatR 8879067 (- 22)), (FloatR 9019737 (- 22), FloatR 9019737 (- 22)),
         FloatR 49 (- 6), (FloatR 9018893 (- 22), FloatR 9018893 (- 22)), FloatR 9019737 (- 22), FloatR 9019737 (- 22)),
        (FloatR 47 (- 6), (FloatR 8741415 (- 22), FloatR 8741415 (- 22)), (FloatR 8879887 (- 22), FloatR 8879887 (- 22)),
         FloatR 48 (- 6), (FloatR 8879073 (- 22), FloatR 8879073 (- 22)), FloatR 8879887 (- 22), FloatR 8879887 (- 22)),
        (FloatR 46 (- 6), (FloatR 8605898 (- 22), FloatR 8605898 (- 22)), (FloatR 8742206 (- 22), FloatR 8742206 (- 22)),
         FloatR 47 (- 6), (FloatR 8741422 (- 22), FloatR 8741422 (- 22)), FloatR 8742206 (- 22), FloatR 8742206 (- 22)),
        (FloatR 45 (- 6), (FloatR 8472481 (- 22), FloatR 8472481 (- 22)), (FloatR 8606660 (- 22), FloatR 8606660 (- 22)),
         FloatR 46 (- 6), (FloatR 8605904 (- 22), FloatR 8605904 (- 22)), FloatR 8606660 (- 22), FloatR 8606660 (- 22)),
        (FloatR 44 (- 6), (FloatR 16682266 (- 23), FloatR 16682266 (- 23)), (FloatR 8473215 (- 22), FloatR 8473215 (- 22)),
         FloatR 45 (- 6), (FloatR 8472487 (- 22), FloatR 8472487 (- 22)), FloatR 8473215 (- 22), FloatR 8473215 (- 22)),
        (FloatR 43 (- 6), (FloatR 16423642 (- 23), FloatR 16423642 (- 23)), (FloatR 16683679 (- 23), FloatR 16683679 (- 23)),
         FloatR 44 (- 6), (FloatR 16682277 (- 23), FloatR 16682277 (- 23)), FloatR 16683679 (- 23), FloatR 16683679 (- 23)),
        (FloatR 42 (- 6), (FloatR 16169028 (- 23), FloatR 16169028 (- 23)), (FloatR 16425001 (- 23), FloatR 16425001 (- 23)),
         FloatR 43 (- 6), (FloatR 16423653 (- 23), FloatR 16423653 (- 23)), FloatR 16425001 (- 23), FloatR 16425001 (- 23)),
        (FloatR 41 (- 6), (FloatR 15918360 (- 23), FloatR 15918360 (- 23)), (FloatR 16170334 (- 23), FloatR 16170334 (- 23)),
         FloatR 42 (- 6), (FloatR 16169038 (- 23), FloatR 16169038 (- 23)), FloatR 16170334 (- 23), FloatR 16170334 (- 23)),
        (FloatR 40 (- 6), (FloatR 15671579 (- 23), FloatR 15671579 (- 23)), (FloatR 15919616 (- 23), FloatR 15919616 (- 23)),
         FloatR 41 (- 6), (FloatR 15918370 (- 23), FloatR 15918370 (- 23)), FloatR 15919616 (- 23), FloatR 15919616 (- 23)),
        (FloatR 39 (- 6), (FloatR 15428624 (- 23), FloatR 15428624 (- 23)), (FloatR 15672785 (- 23), FloatR 15672785 (- 23)),
         FloatR 40 (- 6), (FloatR 15671589 (- 23), FloatR 15671589 (- 23)), FloatR 15672785 (- 23), FloatR 15672785 (- 23)),
        (FloatR 38 (- 6), (FloatR 15189435 (- 23), FloatR 15189435 (- 23)), (FloatR 15429782 (- 23), FloatR 15429782 (- 23)),
         FloatR 39 (- 6), (FloatR 15428633 (- 23), FloatR 15428633 (- 23)), FloatR 15429782 (- 23), FloatR 15429782 (- 23)),
        (FloatR 37 (- 6), (FloatR 14953954 (- 23), FloatR 14953954 (- 23)), (FloatR 15190546 (- 23), FloatR 15190546 (- 23)),
         FloatR 38 (- 6), (FloatR 15189444 (- 23), FloatR 15189444 (- 23)), FloatR 15190546 (- 23), FloatR 15190546 (- 23)),
        (FloatR 36 (- 6), (FloatR 14722124 (- 23), FloatR 14722124 (- 23)), (FloatR 14955019 (- 23), FloatR 14955019 (- 23)),
         FloatR 37 (- 6), (FloatR 14953962 (- 23), FloatR 14953962 (- 23)), FloatR 14955019 (- 23), FloatR 14955019 (- 23)),
        (FloatR 35 (- 6), (FloatR 14493888 (- 23), FloatR 14493888 (- 23)), (FloatR 14723144 (- 23), FloatR 14723144 (- 23)),
         FloatR 36 (- 6), (FloatR 14722132 (- 23), FloatR 14722132 (- 23)), FloatR 14723144 (- 23), FloatR 14723144 (- 23)),
        (FloatR 34 (- 6), (FloatR 14269190 (- 23), FloatR 14269190 (- 23)), (FloatR 14494864 (- 23), FloatR 14494864 (- 23)),
         FloatR 35 (- 6), (FloatR 14493896 (- 23), FloatR 14493896 (- 23)), FloatR 14494864 (- 23), FloatR 14494864 (- 23)),
        (FloatR 33 (- 6), (FloatR 14047976 (- 23), FloatR 14047976 (- 23)), (FloatR 14270124 (- 23), FloatR 14270124 (- 23)),
         FloatR 34 (- 6), (FloatR 14269198 (- 23), FloatR 14269198 (- 23)), FloatR 14270124 (- 23), FloatR 14270124 (- 23)),
        (FloatR 32 (- 6), (FloatR 13830191 (- 23), FloatR 13830191 (- 23)), (FloatR 14048868 (- 23), FloatR 14048868 (- 23)),
         FloatR 33 (- 6), (FloatR 14047983 (- 23), FloatR 14047983 (- 23)), FloatR 14048868 (- 23), FloatR 14048868 (- 23)),
        (FloatR 31 (- 6), (FloatR 13615783 (- 23), FloatR 13615783 (- 23)), (FloatR 13831043 (- 23), FloatR 13831043 (- 23)),
         FloatR 32 (- 6), (FloatR 13830198 (- 23), FloatR 13830198 (- 23)), FloatR 13831043 (- 23), FloatR 13831043 (- 23)),
        (FloatR 30 (- 6), (FloatR 13404698 (- 23), FloatR 13404698 (- 23)), (FloatR 13616595 (- 23), FloatR 13616595 (- 23)),
         FloatR 31 (- 6), (FloatR 13615789 (- 23), FloatR 13615789 (- 23)), FloatR 13616595 (- 23), FloatR 13616595 (- 23)),
        (FloatR 29 (- 6), (FloatR 13196886 (- 23), FloatR 13196886 (- 23)), (FloatR 13405472 (- 23), FloatR 13405472 (- 23)),
         FloatR 30 (- 6), (FloatR 13404704 (- 23), FloatR 13404704 (- 23)), FloatR 13405472 (- 23), FloatR 13405472 (- 23)),
        (FloatR 28 (- 6), (FloatR 12992296 (- 23), FloatR 12992296 (- 23)), (FloatR 13197623 (- 23), FloatR 13197623 (- 23)),
         FloatR 29 (- 6), (FloatR 13196892 (- 23), FloatR 13196892 (- 23)), FloatR 13197623 (- 23), FloatR 13197623 (- 23)),
        (FloatR 27 (- 6), (FloatR 12790877 (- 23), FloatR 12790877 (- 23)), (FloatR 12992996 (- 23), FloatR 12992996 (- 23)),
         FloatR 28 (- 6), (FloatR 12992301 (- 23), FloatR 12992301 (- 23)), FloatR 12992996 (- 23), FloatR 12992996 (- 23)),
        (FloatR 26 (- 6), (FloatR 12592581 (- 23), FloatR 12592581 (- 23)), (FloatR 12791542 (- 23), FloatR 12791542 (- 23)),
         FloatR 27 (- 6), (FloatR 12790882 (- 23), FloatR 12790882 (- 23)), FloatR 12791542 (- 23), FloatR 12791542 (- 23)),
        (FloatR 25 (- 6), (FloatR 12397359 (- 23), FloatR 12397359 (- 23)), (FloatR 12593211 (- 23), FloatR 12593211 (- 23)),
         FloatR 26 (- 6), (FloatR 12592586 (- 23), FloatR 12592586 (- 23)), FloatR 12593211 (- 23), FloatR 12593211 (- 23)),
        (FloatR 24 (- 6), (FloatR 12205164 (- 23), FloatR 12205164 (- 23)), (FloatR 12397956 (- 23), FloatR 12397956 (- 23)),
         FloatR 25 (- 6), (FloatR 12397364 (- 23), FloatR 12397364 (- 23)), FloatR 12397956 (- 23), FloatR 12397956 (- 23)),
        (FloatR 23 (- 6), (FloatR 12015948 (- 23), FloatR 12015948 (- 23)), (FloatR 12205728 (- 23), FloatR 12205728 (- 23)),
         FloatR 24 (- 6), (FloatR 12205168 (- 23), FloatR 12205168 (- 23)), FloatR 12205728 (- 23), FloatR 12205728 (- 23)),
        (FloatR 22 (- 6), (FloatR 11829665 (- 23), FloatR 11829665 (- 23)), (FloatR 12016480 (- 23), FloatR 12016480 (- 23)),
         FloatR 23 (- 6), (FloatR 12015952 (- 23), FloatR 12015952 (- 23)), FloatR 12016480 (- 23), FloatR 12016480 (- 23)),
        (FloatR 21 (- 6), (FloatR 11646271 (- 23), FloatR 11646271 (- 23)), (FloatR 11830167 (- 23), FloatR 11830167 (- 23)),
         FloatR 22 (- 6), (FloatR 11829669 (- 23), FloatR 11829669 (- 23)), FloatR 11830167 (- 23), FloatR 11830167 (- 23)),
        (FloatR 20 (- 6), (FloatR 11465720 (- 23), FloatR 11465720 (- 23)), (FloatR 11646742 (- 23), FloatR 11646742 (- 23)),
         FloatR 21 (- 6), (FloatR 11646275 (- 23), FloatR 11646275 (- 23)), FloatR 11646742 (- 23), FloatR 11646742 (- 23)),
        (FloatR 19 (- 6), (FloatR 11287967 (- 23), FloatR 11287967 (- 23)), (FloatR 11466162 (- 23), FloatR 11466162 (- 23)),
         FloatR 20 (- 6), (FloatR 11465723 (- 23), FloatR 11465723 (- 23)), FloatR 11466162 (- 23), FloatR 11466162 (- 23)),
        (FloatR 18 (- 6), (FloatR 11112971 (- 23), FloatR 11112971 (- 23)), (FloatR 11288381 (- 23), FloatR 11288381 (- 23)),
         FloatR 19 (- 6), (FloatR 11287971 (- 23), FloatR 11287971 (- 23)), FloatR 11288381 (- 23), FloatR 11288381 (- 23)),
        (FloatR 17 (- 6), (FloatR 10940687 (- 23), FloatR 10940687 (- 23)), (FloatR 11113356 (- 23), FloatR 11113356 (- 23)),
         FloatR 18 (- 6), (FloatR 11112974 (- 23), FloatR 11112974 (- 23)), FloatR 11113356 (- 23), FloatR 11113356 (- 23)),
        (FloatR 16 (- 6), (FloatR 10771075 (- 23), FloatR 10771075 (- 23)), (FloatR 10941046 (- 23), FloatR 10941046 (- 23)),
         FloatR 17 (- 6), (FloatR 10940690 (- 23), FloatR 10940690 (- 23)), FloatR 10941046 (- 23), FloatR 10941046 (- 23)),
        (FloatR 15 (- 6), (FloatR 10604091 (- 23), FloatR 10604091 (- 23)), (FloatR 10771407 (- 23), FloatR 10771407 (- 23)),
         FloatR 16 (- 6), (FloatR 10771077 (- 23), FloatR 10771077 (- 23)), FloatR 10771407 (- 23), FloatR 10771407 (- 23)),
        (FloatR 14 (- 6), (FloatR 10439697 (- 23), FloatR 10439697 (- 23)), (FloatR 10604398 (- 23), FloatR 10604398 (- 23)),
         FloatR 15 (- 6), (FloatR 10604094 (- 23), FloatR 10604094 (- 23)), FloatR 10604398 (- 23), FloatR 10604398 (- 23)),
        (FloatR 13 (- 6), (FloatR 10277851 (- 23), FloatR 10277851 (- 23)), (FloatR 10439979 (- 23), FloatR 10439979 (- 23)),
         FloatR 14 (- 6), (FloatR 10439699 (- 23), FloatR 10439699 (- 23)), FloatR 10439979 (- 23), FloatR 10439979 (- 23)),
        (FloatR 12 (- 6), (FloatR 10118514 (- 23), FloatR 10118514 (- 23)), (FloatR 10278109 (- 23), FloatR 10278109 (- 23)),
         FloatR 13 (- 6), (FloatR 10277853 (- 23), FloatR 10277853 (- 23)), FloatR 10278109 (- 23), FloatR 10278109 (- 23)),
        (FloatR 11 (- 6), (FloatR 9961647 (- 23), FloatR 9961647 (- 23)), (FloatR 10118749 (- 23), FloatR 10118749 (- 23)),
         FloatR 12 (- 6), (FloatR 10118516 (- 23), FloatR 10118516 (- 23)), FloatR 10118749 (- 23), FloatR 10118749 (- 23)),
        (FloatR 10 (- 6), (FloatR 9807213 (- 23), FloatR 9807213 (- 23)), (FloatR 9961859 (- 23), FloatR 9961859 (- 23)),
         FloatR 11 (- 6), (FloatR 9961649 (- 23), FloatR 9961649 (- 23)), FloatR 9961859 (- 23), FloatR 9961859 (- 23)),
        (FloatR 9 (- 6), (FloatR 9655172 (- 23), FloatR 9655172 (- 23)), (FloatR 9807402 (- 23), FloatR 9807402 (- 23)),
         FloatR 10 (- 6), (FloatR 9807214 (- 23), FloatR 9807214 (- 23)), FloatR 9807402 (- 23), FloatR 9807402 (- 23)),
        (FloatR 8 (- 6), (FloatR 9505489 (- 23), FloatR 9505489 (- 23)), (FloatR 9655340 (- 23), FloatR 9655340 (- 23)),
         FloatR 9 (- 6), (FloatR 9655174 (- 23), FloatR 9655174 (- 23)), FloatR 9655340 (- 23), FloatR 9655340 (- 23)),
        (FloatR 7 (- 6), (FloatR 9358126 (- 23), FloatR 9358126 (- 23)), (FloatR 9505636 (- 23), FloatR 9505636 (- 23)),
         FloatR 8 (- 6), (FloatR 9505490 (- 23), FloatR 9505490 (- 23)), FloatR 9505636 (- 23), FloatR 9505636 (- 23)),
        (FloatR 6 (- 6), (FloatR 9213047 (- 23), FloatR 9213047 (- 23)), (FloatR 9358253 (- 23), FloatR 9358253 (- 23)),
         FloatR 7 (- 6), (FloatR 9358127 (- 23), FloatR 9358127 (- 23)), FloatR 9358253 (- 23), FloatR 9358253 (- 23)),
        (FloatR 5 (- 6), (FloatR 9070218 (- 23), FloatR 9070218 (- 23)), (FloatR 9213155 (- 23), FloatR 9213155 (- 23)),
         FloatR 6 (- 6), (FloatR 9213048 (- 23), FloatR 9213048 (- 23)), FloatR 9213155 (- 23), FloatR 9213155 (- 23)),
        (FloatR 4 (- 6), (FloatR 8929603 (- 23), FloatR 8929603 (- 23)), (FloatR 9070306 (- 23), FloatR 9070306 (- 23)),
         FloatR 5 (- 6), (FloatR 9070219 (- 23), FloatR 9070219 (- 23)), FloatR 9070306 (- 23), FloatR 9070306 (- 23)),
        (FloatR 3 (- 6), (FloatR 8791168 (- 23), FloatR 8791168 (- 23)), (FloatR 8929673 (- 23), FloatR 8929673 (- 23)),
         FloatR 4 (- 6), (FloatR 8929604 (- 23), FloatR 8929604 (- 23)), FloatR 8929673 (- 23), FloatR 8929673 (- 23)),
        (FloatR 2 (- 6), (FloatR 8654879 (- 23), FloatR 8654879 (- 23)), (FloatR 8791220 (- 23), FloatR 8791220 (- 23)),
         FloatR 3 (- 6), (FloatR 8791169 (- 23), FloatR 8791169 (- 23)), FloatR 8791220 (- 23), FloatR 8791220 (- 23)),
        (FloatR 1 (- 6), (FloatR 8520703 (- 23), FloatR 8520703 (- 23)), (FloatR 8654914 (- 23), FloatR 8654914 (- 23)),
         FloatR 2 (- 6), (FloatR 8654880 (- 23), FloatR 8654880 (- 23)), FloatR 8654914 (- 23), FloatR 8654914 (- 23)),
        (FloatR 0 0, (FloatR 8388608 (- 23), FloatR 8388608 (- 23)), (FloatR 8520721 (- 23), FloatR 8520721 (- 23)), FloatR 1 (- 6),
         (FloatR 8520703 (- 23), FloatR 8520703 (- 23)), FloatR 8520721 (- 23), FloatR 8520721 (- 23))])"
  by eval

end
