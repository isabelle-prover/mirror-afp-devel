theory Example_Bessel
imports
  Example_Utilities
begin

subsection \<open>Bessel Function inspired example\<close>
text \<open>\label{sec:bessel}\<close>

abbreviation (input) "mu \<equiv> (0::real)" \<comment>\<open>why 0?\<close>

abbreviation "bessel_real \<equiv> \<lambda>(s::real, x::real, x'::real).
  (-1::real,
  -x',
  (((s * s + - mu*mu) * x + s * x') * inverse (s * s)))"
approximate_affine bessel bessel_real

definition "bessel_euclarith \<equiv> \<lambda>n.
          (AddE (ScaleR
                (Mult (Add (Mult (Mult (Var n (real_of_float 1, real_of_float 0, real_of_float 0))
                                   (Var n (real_of_float 1, real_of_float 0, real_of_float 0)))
                             (Var n (real_of_float 0, real_of_float 1, real_of_float 0)))
                        (Mult (Var n (real_of_float 1, real_of_float 0, real_of_float 0))
                          (Var n (real_of_float 0, real_of_float 0, real_of_float 1))))
                  (Inverse
                    (Mult (Var n (real_of_float 1, real_of_float 0, real_of_float 0))
                      (Var n (real_of_float 1, real_of_float 0, real_of_float 0)))))
                (real_of_float 0, real_of_float 0, real_of_float 1))
          (AddE (ScaleR (Minus (Var n (real_of_float 0, real_of_float 0, real_of_float 1)))
                  (real_of_float 0, real_of_float 1, real_of_float 0))
            (ScaleR (Minus (Num (real_of_float 1))) (real_of_float 1, real_of_float 0, real_of_float 0))))"

definition "bessel_safe \<equiv> (\<lambda>n.
  Pos (
    AddE
      (ScaleR (Minus (Var n (real_of_float 1, real_of_float 0, real_of_float 0))) (real_of_float 1, real_of_float 0, real_of_float 0))
    (AddE
      (ScaleR (Num 1) (real_of_float 0, real_of_float 1, real_of_float 0))
      (ScaleR (Num 1) (real_of_float 0, real_of_float 0, real_of_float 1)))))"

setup Locale_Code.open_block
interpretation bessel: aform_approximate_ivp bessel_real "\<lambda>(s, _, _). s < 0" bessel_euclarith bessel_safe
  apply unfold_locales
  apply (auto simp add: bessel_euclarith_def bessel_safe_def plusE_def numeral_eq_Suc split_beta'
      eucl_less_def Basis_prod_def
      intro!: ext eq_reflection)
  proof -
    fix x :: nat and xs :: "(real \<times> real \<times> real) list" and d1 :: nat and d2 :: nat and d3 :: nat
    assume a1: "0 > fst (xs ! x)"
    assume "xs ! x \<bullet> (1, 0, 0) = 0"
    then have "fst (xs ! x) = 0"
      by (metis inner_Pair_0(2) real_inner_1_right zero_prod_def)
    then show False
      using a1 by force
  next
    have "{x::real*real*real. 0 > fst x} = {..<0} \<times> UNIV"
      by auto
    also have "open \<dots>" by (auto intro!: open_Times)
    finally show "open {x::real*real*real. 0 > fst x}" .
  qed (force intro!: exI[where x="-One"])
setup Locale_Code.close_block

definition "bessel_optns =
  default_optns
    \<lparr> precision := 30,
      tolerance := FloatR 1 (- 4),
      stepsize  := FloatR 1 (- 4),
      printing_fun := (\<lambda>a b. ())\<rparr>"

definition "J0l = real_divl 50 (765197686557966551449717526103) 1000000000000000000000000000000"
definition "J0u = real_divr 50  (765197686557966551449717526103) 1000000000000000000000000000000"
definition "J0l' = real_divl 50 (440050585744933515959682203719) 1000000000000000000000000000000"
definition "J0u' = real_divr 50 (440050585744933515959682203719) 1000000000000000000000000000000"

definition "solve_bessel = bessel.one_step_until_time_ivl_listres (bessel_optns)"
definition "solve_bessel_ex (_::unit) = solve_bessel (aform_of_ivl (-1,J0l,J0l') (-1,J0u,J0u')) True 2"
schematic_goal solve_ivl_bessel:
  "solve_bessel_ex () = ?X"
  by (eval_lhs)
concrete_definition bessel_result uses solve_ivl_bessel is "_ = dRETURN ?X"
definition "bessel_reach = map aform_of_list_aform (the (snd (bessel_result)))"

lemma bessel_result:
  "2 \<in> bessel.existence_ivl0 (-1, 0.765197686557966551449717526103, 0.440050585744933515959682203719) \<and>
                bessel.flow0 (-1, 0.765197686557966551449717526103, 0.440050585744933515959682203719) 2 \<in>
  {-3} \<times> {-0.261 .. -0.259} \<times> {0.338 .. 0.340} \<and>
  (\<forall>s \<in> {0 .. 2}. bessel.flow0 (-1, 0.765197686557966551449717526103, 0.440050585744933515959682203719) s \<in> \<Union>(Affine ` set bessel_reach))"
  apply (rule bessel.one_step_until_time_ivl_listres_reachable[OF bessel_result.refine[unfolded solve_bessel_ex_def solve_bessel_def]])
  subgoal by (force simp: bessel_result_def)
  subgoal
    apply (auto simp: powr_neg_numeral bessel_reach_def)
    apply (subst Affine_aform_of_ivl)
    apply (auto simp: powr_neg_numeral J0l_def J0u_def J0l'_def J0u'_def bessel_result_def
      simp del: le_divide_eq_numeral1 divide_le_eq_numeral1
      intro!: order_trans[OF real_divl] order_trans[OF _ real_divr])
    done
  subgoal by auto
  subgoal by (auto simp: bessel_result_def)
  subgoal by (auto simp: powr_neg_numeral bessel_reach_def)
  done

end
