theory Example_Exp
imports
  Example_Utilities
begin

subsection \<open>Example Exponential\<close>

text \<open>TODO: why not exp-ivp "lambda x::real. x"?\<close>

abbreviation "exp_real \<equiv> \<lambda>(t::real, x::real). (1::real, x)"
approximate_affine exp_affine exp_real
print_theorems
definition "exp_euclarith \<equiv> \<lambda>n. (AddE
          (ScaleR (realarith.Var n (real_of_float 0, real_of_float 1))
            (real_of_float 0, real_of_float 1))
          (ScaleR (realarith.Num (real_of_float 1))
            (real_of_float 1, real_of_float 0)))"

setup Locale_Code.open_block
interpretation exp_ivp: aform_approximate_ivp exp_real "\<lambda>_. True" exp_euclarith true_euclarithform
  by unfold_locales
    (auto simp add: exp_euclarith_def plusE_def numeral_eq_Suc
      intro!: ext eq_reflection)
setup Locale_Code.close_block

definition "exp_optns = default_optns
    \<lparr> precision := 40,
      tolerance := FloatR 1 (- 2),
      stepsize  := FloatR 1 (- 6),
      iterations := 40,
      printing_fun := (\<lambda>a b. ()),
      widening_mod := 10\<rparr>"

definition "exp_ode x = exp_ivp.one_step_until_time_ivl_listres exp_optns (aform_of_point (0, 1)) False x"


subsection \<open>connection to exponential function\<close>

lemma exp_ivp_existence_ivl0:
  "exp_ivp.existence_ivl0 p = UNIV"
  by (rule exp_ivp.existence_ivl_eq_domain)
     (auto intro!: exI[where x=1] order_trans[OF norm_Pair_le] order_trans[OF _ norm_snd_le])

lemma exp_eq_exp_ivp_aux:
  "exp_ivp.flow0 (0, 1) x = (x, exp x)"
  apply (rule exp_ivp.flow_unique[where phi="\<lambda>x. (x, exp x)"])
  unfolding exp_ivp_existence_ivl0
  by (auto simp: has_vector_derivative_def intro!: derivative_eq_intros)

lemma ex_eq_exp_ivp: "exp x = snd (exp_ivp.flow0 (0, 1) x)"
  unfolding exp_eq_exp_ivp_aux by simp

lemma exp_ode_exp_mem:
  assumes "exp_ode x = dRETURN ((l, u), None)"
  shows "exp x \<in> {snd l .. snd u}"
  using exp_ivp.one_step_until_time_ivl_listres[OF assms[unfolded exp_ode_def], of "(0, 1)", OF _ refl order_refl]
  unfolding exp_ivp_existence_ivl0
  by (subst ex_eq_exp_ivp) (auto simp: less_eq_prod_def)

subsection \<open>concrete example\<close>

schematic_goal exp_ode: "exp_ode 1 = ?X"
  by guess_rhs eval
concrete_definition exp_result uses exp_ode is "_ = dRETURN ?X"
definition "e3_reach = map aform_of_list_aform (the (snd (exp_result)))"

lemma exp_ode_result: "1 \<in> exp_ivp.existence_ivl0 (0, 1) \<and>
  exp_ivp.flow0 (0, 1) 1 \<in> {1} \<times> {2.718281 .. 2.718284}"
  by (rule exp_ivp.one_step_until_time_ivl_listres[OF exp_ode[unfolded exp_ode_def]])
    (auto simp: powr_neg_numeral)

lemma exp1: "exp 1 \<in> {2.718281 .. 2.718284::real}"
  using exp_ode_exp_mem[OF exp_ode]
  by simp

end
