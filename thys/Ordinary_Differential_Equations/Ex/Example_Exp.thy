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
       [(FloatR 63 (- 6), (FloatR 5612042 (- 21), FloatR 5612042 (- 21)), (FloatR 5701117 (- 21), FloatR 5701117 (- 21)),
         FloatR 64 (- 6), (FloatR 5700420 (- 21), FloatR 5700420 (- 21)), FloatR 5701117 (- 21), FloatR 5701117 (- 21)),
        (FloatR 62 (- 6), (FloatR 5525039 (- 21), FloatR 5525039 (- 21)), (FloatR 5612723 (- 21), FloatR 5612723 (- 21)),
         FloatR 63 (- 6), (FloatR 5612047 (- 21), FloatR 5612047 (- 21)), FloatR 5612723 (- 21), FloatR 5612723 (- 21)),
        (FloatR 61 (- 6), (FloatR 5439384 (- 21), FloatR 5439384 (- 21)), (FloatR 5525698 (- 21), FloatR 5525698 (- 21)),
         FloatR 62 (- 6), (FloatR 5525044 (- 21), FloatR 5525044 (- 21)), FloatR 5525698 (- 21), FloatR 5525698 (- 21)),
        (FloatR 60 (- 6), (FloatR 5355058 (- 21), FloatR 5355058 (- 21)), (FloatR 5440023 (- 21), FloatR 5440023 (- 21)),
         FloatR 61 (- 6), (FloatR 5439389 (- 21), FloatR 5439389 (- 21)), FloatR 5440023 (- 21), FloatR 5440023 (- 21)),
        (FloatR 59 (- 6), (FloatR 5272039 (- 21), FloatR 5272039 (- 21)), (FloatR 5355677 (- 21), FloatR 5355677 (- 21)),
         FloatR 60 (- 6), (FloatR 5355063 (- 21), FloatR 5355063 (- 21)), FloatR 5355677 (- 21), FloatR 5355677 (- 21)),
        (FloatR 58 (- 6), (FloatR 5190307 (- 21), FloatR 5190307 (- 21)), (FloatR 5272638 (- 21), FloatR 5272638 (- 21)),
         FloatR 59 (- 6), (FloatR 5272044 (- 21), FloatR 5272044 (- 21)), FloatR 5272638 (- 21), FloatR 5272638 (- 21)),
        (FloatR 57 (- 6), (FloatR 5109842 (- 21), FloatR 5109842 (- 21)), (FloatR 5190887 (- 21), FloatR 5190887 (- 21)),
         FloatR 58 (- 6), (FloatR 5190311 (- 21), FloatR 5190311 (- 21)), FloatR 5190887 (- 21), FloatR 5190887 (- 21)),
        (FloatR 56 (- 6), (FloatR 5030624 (- 21), FloatR 5030624 (- 21)), (FloatR 5110403 (- 21), FloatR 5110403 (- 21)),
         FloatR 57 (- 6), (FloatR 5109846 (- 21), FloatR 5109846 (- 21)), FloatR 5110403 (- 21), FloatR 5110403 (- 21)),
        (FloatR 55 (- 6), (FloatR 4952635 (- 21), FloatR 4952635 (- 21)), (FloatR 5031167 (- 21), FloatR 5031167 (- 21)),
         FloatR 56 (- 6), (FloatR 5030629 (- 21), FloatR 5030629 (- 21)), FloatR 5031167 (- 21), FloatR 5031167 (- 21)),
        (FloatR 54 (- 6), (FloatR 4875855 (- 21), FloatR 4875855 (- 21)), (FloatR 4953160 (- 21), FloatR 4953160 (- 21)),
         FloatR 55 (- 6), (FloatR 4952639 (- 21), FloatR 4952639 (- 21)), FloatR 4953160 (- 21), FloatR 4953160 (- 21)),
        (FloatR 53 (- 6), (FloatR 4800265 (- 21), FloatR 4800265 (- 21)), (FloatR 4876362 (- 21), FloatR 4876362 (- 21)),
         FloatR 54 (- 6), (FloatR 4875859 (- 21), FloatR 4875859 (- 21)), FloatR 4876362 (- 21), FloatR 4876362 (- 21)),
        (FloatR 52 (- 6), (FloatR 4725846 (- 21), FloatR 4725846 (- 21)), (FloatR 4800755 (- 21), FloatR 4800755 (- 21)),
         FloatR 53 (- 6), (FloatR 4800268 (- 21), FloatR 4800268 (- 21)), FloatR 4800755 (- 21), FloatR 4800755 (- 21)),
        (FloatR 51 (- 6), (FloatR 4652582 (- 21), FloatR 4652582 (- 21)), (FloatR 4726320 (- 21), FloatR 4726320 (- 21)),
         FloatR 52 (- 6), (FloatR 4725850 (- 21), FloatR 4725850 (- 21)), FloatR 4726320 (- 21), FloatR 4726320 (- 21)),
        (FloatR 50 (- 6), (FloatR 4580453 (- 21), FloatR 4580453 (- 21)), (FloatR 4653039 (- 21), FloatR 4653039 (- 21)),
         FloatR 51 (- 6), (FloatR 4652585 (- 21), FloatR 4652585 (- 21)), FloatR 4653039 (- 21), FloatR 4653039 (- 21)),
        (FloatR 49 (- 6), (FloatR 4509443 (- 21), FloatR 4509443 (- 21)), (FloatR 4580895 (- 21), FloatR 4580895 (- 21)),
         FloatR 50 (- 6), (FloatR 4580457 (- 21), FloatR 4580457 (- 21)), FloatR 4580895 (- 21), FloatR 4580895 (- 21)),
        (FloatR 48 (- 6), (FloatR 4439533 (- 21), FloatR 4439533 (- 21)), (FloatR 4509869 (- 21), FloatR 4509869 (- 21)),
         FloatR 49 (- 6), (FloatR 4509446 (- 21), FloatR 4509446 (- 21)), FloatR 4509869 (- 21), FloatR 4509869 (- 21)),
        (FloatR 47 (- 6), (FloatR 4370707 (- 21), FloatR 4370707 (- 21)), (FloatR 4439944 (- 21), FloatR 4439944 (- 21)),
         FloatR 48 (- 6), (FloatR 4439536 (- 21), FloatR 4439536 (- 21)), FloatR 4439944 (- 21), FloatR 4439944 (- 21)),
        (FloatR 46 (- 6), (FloatR 4302949 (- 21), FloatR 4302949 (- 21)), (FloatR 4371103 (- 21), FloatR 4371103 (- 21)),
         FloatR 47 (- 6), (FloatR 4370711 (- 21), FloatR 4370711 (- 21)), FloatR 4371103 (- 21), FloatR 4371103 (- 21)),
        (FloatR 45 (- 6), (FloatR 4236240 (- 21), FloatR 4236240 (- 21)), (FloatR 4303330 (- 21), FloatR 4303330 (- 21)),
         FloatR 46 (- 6), (FloatR 4302952 (- 21), FloatR 4302952 (- 21)), FloatR 4303330 (- 21), FloatR 4303330 (- 21)),
        (FloatR 44 (- 6), (FloatR 8341133 (- 22), FloatR 8341133 (- 22)), (FloatR 4236608 (- 21), FloatR 4236608 (- 21)),
         FloatR 45 (- 6), (FloatR 4236243 (- 21), FloatR 4236243 (- 21)), FloatR 4236608 (- 21), FloatR 4236608 (- 21)),
        (FloatR 43 (- 6), (FloatR 8211821 (- 22), FloatR 8211821 (- 22)), (FloatR 8341840 (- 22), FloatR 8341840 (- 22)),
         FloatR 44 (- 6), (FloatR 8341138 (- 22), FloatR 8341138 (- 22)), FloatR 8341840 (- 22), FloatR 8341840 (- 22)),
        (FloatR 42 (- 6), (FloatR 8084514 (- 22), FloatR 8084514 (- 22)), (FloatR 8212501 (- 22), FloatR 8212501 (- 22)),
         FloatR 43 (- 6), (FloatR 8211826 (- 22), FloatR 8211826 (- 22)), FloatR 8212501 (- 22), FloatR 8212501 (- 22)),
        (FloatR 41 (- 6), (FloatR 7959180 (- 22), FloatR 7959180 (- 22)), (FloatR 8085167 (- 22), FloatR 8085167 (- 22)),
         FloatR 42 (- 6), (FloatR 8084519 (- 22), FloatR 8084519 (- 22)), FloatR 8085167 (- 22), FloatR 8085167 (- 22)),
        (FloatR 40 (- 6), (FloatR 7835789 (- 22), FloatR 7835789 (- 22)), (FloatR 7959808 (- 22), FloatR 7959808 (- 22)),
         FloatR 41 (- 6), (FloatR 7959185 (- 22), FloatR 7959185 (- 22)), FloatR 7959808 (- 22), FloatR 7959808 (- 22)),
        (FloatR 39 (- 6), (FloatR 7714312 (- 22), FloatR 7714312 (- 22)), (FloatR 7836393 (- 22), FloatR 7836393 (- 22)),
         FloatR 40 (- 6), (FloatR 7835794 (- 22), FloatR 7835794 (- 22)), FloatR 7836393 (- 22), FloatR 7836393 (- 22)),
        (FloatR 38 (- 6), (FloatR 7594717 (- 22), FloatR 7594717 (- 22)), (FloatR 7714891 (- 22), FloatR 7714891 (- 22)),
         FloatR 39 (- 6), (FloatR 7714316 (- 22), FloatR 7714316 (- 22)), FloatR 7714891 (- 22), FloatR 7714891 (- 22)),
        (FloatR 37 (- 6), (FloatR 7476977 (- 22), FloatR 7476977 (- 22)), (FloatR 7595273 (- 22), FloatR 7595273 (- 22)),
         FloatR 38 (- 6), (FloatR 7594722 (- 22), FloatR 7594722 (- 22)), FloatR 7595273 (- 22), FloatR 7595273 (- 22)),
        (FloatR 36 (- 6), (FloatR 7361062 (- 22), FloatR 7361062 (- 22)), (FloatR 7477510 (- 22), FloatR 7477510 (- 22)),
         FloatR 37 (- 6), (FloatR 7476981 (- 22), FloatR 7476981 (- 22)), FloatR 7477510 (- 22), FloatR 7477510 (- 22)),
        (FloatR 35 (- 6), (FloatR 7246944 (- 22), FloatR 7246944 (- 22)), (FloatR 7361572 (- 22), FloatR 7361572 (- 22)),
         FloatR 36 (- 6), (FloatR 7361066 (- 22), FloatR 7361066 (- 22)), FloatR 7361572 (- 22), FloatR 7361572 (- 22)),
        (FloatR 34 (- 6), (FloatR 7134595 (- 22), FloatR 7134595 (- 22)), (FloatR 7247432 (- 22), FloatR 7247432 (- 22)),
         FloatR 35 (- 6), (FloatR 7246948 (- 22), FloatR 7246948 (- 22)), FloatR 7247432 (- 22), FloatR 7247432 (- 22)),
        (FloatR 33 (- 6), (FloatR 7023988 (- 22), FloatR 7023988 (- 22)), (FloatR 7135062 (- 22), FloatR 7135062 (- 22)),
         FloatR 34 (- 6), (FloatR 7134599 (- 22), FloatR 7134599 (- 22)), FloatR 7135062 (- 22), FloatR 7135062 (- 22)),
        (FloatR 32 (- 6), (FloatR 6915095 (- 22), FloatR 6915095 (- 22)), (FloatR 7024434 (- 22), FloatR 7024434 (- 22)),
         FloatR 33 (- 6), (FloatR 7023991 (- 22), FloatR 7023991 (- 22)), FloatR 7024434 (- 22), FloatR 7024434 (- 22)),
        (FloatR 31 (- 6), (FloatR 6807891 (- 22), FloatR 6807891 (- 22)), (FloatR 6915522 (- 22), FloatR 6915522 (- 22)),
         FloatR 32 (- 6), (FloatR 6915099 (- 22), FloatR 6915099 (- 22)), FloatR 6915522 (- 22), FloatR 6915522 (- 22)),
        (FloatR 30 (- 6), (FloatR 6702349 (- 22), FloatR 6702349 (- 22)), (FloatR 6808298 (- 22), FloatR 6808298 (- 22)),
         FloatR 31 (- 6), (FloatR 6807894 (- 22), FloatR 6807894 (- 22)), FloatR 6808298 (- 22), FloatR 6808298 (- 22)),
        (FloatR 29 (- 6), (FloatR 6598443 (- 22), FloatR 6598443 (- 22)), (FloatR 6702736 (- 22), FloatR 6702736 (- 22)),
         FloatR 30 (- 6), (FloatR 6702352 (- 22), FloatR 6702352 (- 22)), FloatR 6702736 (- 22), FloatR 6702736 (- 22)),
        (FloatR 28 (- 6), (FloatR 6496148 (- 22), FloatR 6496148 (- 22)), (FloatR 6598812 (- 22), FloatR 6598812 (- 22)),
         FloatR 29 (- 6), (FloatR 6598446 (- 22), FloatR 6598446 (- 22)), FloatR 6598812 (- 22), FloatR 6598812 (- 22)),
        (FloatR 27 (- 6), (FloatR 6395438 (- 22), FloatR 6395438 (- 22)), (FloatR 6496498 (- 22), FloatR 6496498 (- 22)),
         FloatR 28 (- 6), (FloatR 6496150 (- 22), FloatR 6496150 (- 22)), FloatR 6496498 (- 22), FloatR 6496498 (- 22)),
        (FloatR 26 (- 6), (FloatR 6296290 (- 22), FloatR 6296290 (- 22)), (FloatR 6395771 (- 22), FloatR 6395771 (- 22)),
         FloatR 27 (- 6), (FloatR 6395441 (- 22), FloatR 6395441 (- 22)), FloatR 6395771 (- 22), FloatR 6395771 (- 22)),
        (FloatR 25 (- 6), (FloatR 6198679 (- 22), FloatR 6198679 (- 22)), (FloatR 6296606 (- 22), FloatR 6296606 (- 22)),
         FloatR 26 (- 6), (FloatR 6296293 (- 22), FloatR 6296293 (- 22)), FloatR 6296606 (- 22), FloatR 6296606 (- 22)),
        (FloatR 24 (- 6), (FloatR 6102582 (- 22), FloatR 6102582 (- 22)), (FloatR 6198978 (- 22), FloatR 6198978 (- 22)),
         FloatR 25 (- 6), (FloatR 6198682 (- 22), FloatR 6198682 (- 22)), FloatR 6198978 (- 22), FloatR 6198978 (- 22)),
        (FloatR 23 (- 6), (FloatR 6007974 (- 22), FloatR 6007974 (- 22)), (FloatR 6102864 (- 22), FloatR 6102864 (- 22)),
         FloatR 24 (- 6), (FloatR 6102584 (- 22), FloatR 6102584 (- 22)), FloatR 6102864 (- 22), FloatR 6102864 (- 22)),
        (FloatR 22 (- 6), (FloatR 5914832 (- 22), FloatR 5914832 (- 22)), (FloatR 6008240 (- 22), FloatR 6008240 (- 22)),
         FloatR 23 (- 6), (FloatR 6007976 (- 22), FloatR 6007976 (- 22)), FloatR 6008240 (- 22), FloatR 6008240 (- 22)),
        (FloatR 21 (- 6), (FloatR 5823135 (- 22), FloatR 5823135 (- 22)), (FloatR 5915084 (- 22), FloatR 5915084 (- 22)),
         FloatR 22 (- 6), (FloatR 5914834 (- 22), FloatR 5914834 (- 22)), FloatR 5915084 (- 22), FloatR 5915084 (- 22)),
        (FloatR 20 (- 6), (FloatR 5732860 (- 22), FloatR 5732860 (- 22)), (FloatR 5823371 (- 22), FloatR 5823371 (- 22)),
         FloatR 21 (- 6), (FloatR 5823137 (- 22), FloatR 5823137 (- 22)), FloatR 5823371 (- 22), FloatR 5823371 (- 22)),
        (FloatR 19 (- 6), (FloatR 5643983 (- 22), FloatR 5643983 (- 22)), (FloatR 5733081 (- 22), FloatR 5733081 (- 22)),
         FloatR 20 (- 6), (FloatR 5732861 (- 22), FloatR 5732861 (- 22)), FloatR 5733081 (- 22), FloatR 5733081 (- 22)),
        (FloatR 18 (- 6), (FloatR 5556485 (- 22), FloatR 5556485 (- 22)), (FloatR 5644191 (- 22), FloatR 5644191 (- 22)),
         FloatR 19 (- 6), (FloatR 5643985 (- 22), FloatR 5643985 (- 22)), FloatR 5644191 (- 22), FloatR 5644191 (- 22)),
        (FloatR 17 (- 6), (FloatR 5470343 (- 22), FloatR 5470343 (- 22)), (FloatR 5556678 (- 22), FloatR 5556678 (- 22)),
         FloatR 18 (- 6), (FloatR 5556487 (- 22), FloatR 5556487 (- 22)), FloatR 5556678 (- 22), FloatR 5556678 (- 22)),
        (FloatR 16 (- 6), (FloatR 5385537 (- 22), FloatR 5385537 (- 22)), (FloatR 5470523 (- 22), FloatR 5470523 (- 22)),
         FloatR 17 (- 6), (FloatR 5470345 (- 22), FloatR 5470345 (- 22)), FloatR 5470523 (- 22), FloatR 5470523 (- 22)),
        (FloatR 15 (- 6), (FloatR 5302045 (- 22), FloatR 5302045 (- 22)), (FloatR 5385704 (- 22), FloatR 5385704 (- 22)),
         FloatR 16 (- 6), (FloatR 5385538 (- 22), FloatR 5385538 (- 22)), FloatR 5385704 (- 22), FloatR 5385704 (- 22)),
        (FloatR 14 (- 6), (FloatR 5219848 (- 22), FloatR 5219848 (- 22)), (FloatR 5302199 (- 22), FloatR 5302199 (- 22)),
         FloatR 15 (- 6), (FloatR 5302047 (- 22), FloatR 5302047 (- 22)), FloatR 5302199 (- 22), FloatR 5302199 (- 22)),
        (FloatR 13 (- 6), (FloatR 5138925 (- 22), FloatR 5138925 (- 22)), (FloatR 5219990 (- 22), FloatR 5219990 (- 22)),
         FloatR 14 (- 6), (FloatR 5219849 (- 22), FloatR 5219849 (- 22)), FloatR 5219990 (- 22), FloatR 5219990 (- 22)),
        (FloatR 12 (- 6), (FloatR 5059257 (- 22), FloatR 5059257 (- 22)), (FloatR 5139055 (- 22), FloatR 5139055 (- 22)),
         FloatR 13 (- 6), (FloatR 5138926 (- 22), FloatR 5138926 (- 22)), FloatR 5139055 (- 22), FloatR 5139055 (- 22)),
        (FloatR 11 (- 6), (FloatR 4980823 (- 22), FloatR 4980823 (- 22)), (FloatR 5059375 (- 22), FloatR 5059375 (- 22)),
         FloatR 12 (- 6), (FloatR 5059258 (- 22), FloatR 5059258 (- 22)), FloatR 5059375 (- 22), FloatR 5059375 (- 22)),
        (FloatR 10 (- 6), (FloatR 4903606 (- 22), FloatR 4903606 (- 22)), (FloatR 4980930 (- 22), FloatR 4980930 (- 22)),
         FloatR 11 (- 6), (FloatR 4980824 (- 22), FloatR 4980824 (- 22)), FloatR 4980930 (- 22), FloatR 4980930 (- 22)),
        (FloatR 9 (- 6), (FloatR 4827586 (- 22), FloatR 4827586 (- 22)), (FloatR 4903701 (- 22), FloatR 4903701 (- 22)),
         FloatR 10 (- 6), (FloatR 4903607 (- 22), FloatR 4903607 (- 22)), FloatR 4903701 (- 22), FloatR 4903701 (- 22)),
        (FloatR 8 (- 6), (FloatR 4752744 (- 22), FloatR 4752744 (- 22)), (FloatR 4827670 (- 22), FloatR 4827670 (- 22)),
         FloatR 9 (- 6), (FloatR 4827587 (- 22), FloatR 4827587 (- 22)), FloatR 4827670 (- 22), FloatR 4827670 (- 22)),
        (FloatR 7 (- 6), (FloatR 4679063 (- 22), FloatR 4679063 (- 22)), (FloatR 4752818 (- 22), FloatR 4752818 (- 22)),
         FloatR 8 (- 6), (FloatR 4752745 (- 22), FloatR 4752745 (- 22)), FloatR 4752818 (- 22), FloatR 4752818 (- 22)),
        (FloatR 6 (- 6), (FloatR 4606523 (- 22), FloatR 4606523 (- 22)), (FloatR 4679127 (- 22), FloatR 4679127 (- 22)),
         FloatR 7 (- 6), (FloatR 4679063 (- 22), FloatR 4679063 (- 22)), FloatR 4679127 (- 22), FloatR 4679127 (- 22)),
        (FloatR 5 (- 6), (FloatR 4535109 (- 22), FloatR 4535109 (- 22)), (FloatR 4606578 (- 22), FloatR 4606578 (- 22)),
         FloatR 6 (- 6), (FloatR 4606524 (- 22), FloatR 4606524 (- 22)), FloatR 4606578 (- 22), FloatR 4606578 (- 22)),
        (FloatR 4 (- 6), (FloatR 4464801 (- 22), FloatR 4464801 (- 22)), (FloatR 4535153 (- 22), FloatR 4535153 (- 22)),
         FloatR 5 (- 6), (FloatR 4535109 (- 22), FloatR 4535109 (- 22)), FloatR 4535153 (- 22), FloatR 4535153 (- 22)),
        (FloatR 3 (- 6), (FloatR 4395584 (- 22), FloatR 4395584 (- 22)), (FloatR 4464837 (- 22), FloatR 4464837 (- 22)),
         FloatR 4 (- 6), (FloatR 4464802 (- 22), FloatR 4464802 (- 22)), FloatR 4464837 (- 22), FloatR 4464837 (- 22)),
        (FloatR 2 (- 6), (FloatR 4327439 (- 22), FloatR 4327439 (- 22)), (FloatR 4395610 (- 22), FloatR 4395610 (- 22)),
         FloatR 3 (- 6), (FloatR 4395584 (- 22), FloatR 4395584 (- 22)), FloatR 4395610 (- 22), FloatR 4395610 (- 22)),
        (FloatR 1 (- 6), (FloatR 4260351 (- 22), FloatR 4260351 (- 22)), (FloatR 4327457 (- 22), FloatR 4327457 (- 22)),
         FloatR 2 (- 6), (FloatR 4327440 (- 22), FloatR 4327440 (- 22)), FloatR 4327457 (- 22), FloatR 4327457 (- 22)),
        (FloatR 0 0, (FloatR 4194304 (- 22), FloatR 4194304 (- 22)), (FloatR 4260361 (- 22), FloatR 4260361 (- 22)),
         FloatR 1 (- 6), (FloatR 4260351 (- 22), FloatR 4260351 (- 22)), FloatR 4260361 (- 22), FloatR 4260361 (- 22))])"
  by eval

end
