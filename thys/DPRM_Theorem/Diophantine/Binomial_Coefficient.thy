subsection \<open>Binomial Coefficient is Diophantine\<close>

theory Binomial_Coefficient
  imports Digit_Function
begin

lemma bin_coeff_diophantine:
  shows "c = a choose b \<longleftrightarrow> (\<exists>u.(u = 2^(Suc a) \<and> c = nth_digit ((u+1)^a) b u))"
proof-
  have "(u + 1)^a = (\<Sum>k\<le>a. (a choose k) * u ^ k)" for u
    using binomial[of u 1 a] by auto
  moreover have "a choose k < 2 ^ Suc a" for k
    using binomial_le_pow2[of a k] by (simp add: le_less_trans)
  ultimately have "nth_digit (((2 ^ Suc a) + 1)^a) b (2 ^ Suc a) = a choose b" 
    using nth_digit_gen_power_series[of "\<lambda>k.(a choose k)" a a b] by (simp add: atLeast0AtMost)
  then show ?thesis by auto
qed

definition binomial_coefficient ("[_ = _ choose _]" 1000)
  where "[A = B choose C] \<equiv> (TERNARY (\<lambda>a b c. a = b choose c) A B C)"

lemma binomial_coefficient_dioph[dioph]:
  fixes A B C :: polynomial
  defines "DR \<equiv> [C = A choose B]"
  shows "is_dioph_rel DR"
proof -
  define A' B' C' where pushed_def:
    "A' \<equiv> (push_param A 2)" "B' \<equiv> (push_param B 2)" "C' \<equiv> (push_param C 2)"

  (* Param 0 = u = 2^(a + 1), Param 1 = (u+1)^a *)
  define DS where "DS \<equiv> [\<exists>2] [Param 0 = Const 2 ^ (A' [+] \<^bold>1)]
                              [\<and>] [Param 1 = (Param 0 [+] \<^bold>1) ^ A']
                              [\<and>] [C' = Digit (Param 1) B' (Param 0)]"

  have "eval DS a = eval DR a" for a
  proof -
    have "eval DS a = (peval C a = nth_digit ((2 ^ Suc (peval A a) + 1)^ peval A a)
                                                      (peval B a) (2 ^ Suc (peval A a)))"
      unfolding DS_def defs pushed_def apply (auto simp add: push_push)
      apply (rule exI[of _ "[2 * 2 ^ peval A a, Suc (2 * 2 ^ peval A a) ^ peval A a]"])
      apply (auto simp add: push_push push_list_eval)
      by (metis (mono_tags, lifting) Suc_lessI mult_pos_pos n_not_Suc_n
                numeral_2_eq_2 one_eq_mult_iff pos2 zero_less_power)

    then show ?thesis
      unfolding DR_def binomial_coefficient_def defs by (simp add: bin_coeff_diophantine)
  qed

  moreover have "is_dioph_rel DS"
    unfolding DS_def by (auto simp: dioph)

  ultimately show ?thesis
    by (auto simp: is_dioph_rel_def)
qed

declare binomial_coefficient_def[defs]


text \<open>odd function is diophantine\<close>

lemma odd_dioph_repr:
  fixes a :: nat
  shows "odd a \<longleftrightarrow> (\<exists>x::nat. a = 2*x + 1)"
  by (meson dvd_triv_left even_plus_one_iff oddE)

definition odd_lift ("ODD _" [999] 1000)
  where "ODD A \<equiv> (UNARY (odd) A)"

lemma odd_dioph[dioph]:
  fixes A
  defines "DR \<equiv> (ODD A)"
  shows "is_dioph_rel DR"
proof -
  define DS where "DS \<equiv> [\<exists>] (push_param A 1) [=] Const 2 [*] Param 0 [+] Const 1"

  have "eval DS a = eval DR a" for a
    unfolding DS_def DR_def odd_lift_def defs using push_push1 by (simp add: odd_dioph_repr push0)

  moreover have "is_dioph_rel DS"
    unfolding DS_def by (auto simp: dioph)

  ultimately show ?thesis
    by (auto simp: is_dioph_rel_def)
qed

declare odd_lift_def[defs]

end