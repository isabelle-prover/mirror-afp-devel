subsection \<open>Exponentiation is a Diophantine Relation\<close>

theory Exponential_Relation
  imports Alpha_Sequence "Exponentiation"
begin


(* Exponentiation is diophantine *)
definition exp_equations :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "exp_equations p q r b m = (b = Exp_Matrices.\<alpha> (q + 4) (r + 1) + q * q + 2 \<and> 
                              m + q^2 + 1 = b * q \<and> 
                              p < m \<and> 
                              (p + b * Exp_Matrices.\<alpha> b r) mod m = (q * Exp_Matrices.\<alpha> b r + 
                                                                   Exp_Matrices.\<alpha> b (r + 1)) mod m)"

lemma exp_repr:
  fixes p q r :: nat
  shows "p = q^r \<longleftrightarrow> ((q = 0 \<and> r = 0 \<and> p = 1) \<or> 
                          (q = 0 \<and> 0 < r \<and> p = 0) \<or> 
                          (q > 0 \<and> (\<exists>b m :: nat. exp_equations p q r b m)))"  (is "?P \<longleftrightarrow> ?Q")
proof 
  assume P: ?P
    (* 3 disjunction elims applied to assumption; makes cases 1 and 2 trivial *)
    consider (c1)"q = 0 \<and> r = 0 \<and> p = 1" | (c2) "q = 0 \<and> 0 < r \<and> p = 0" | (c3) "q > 0 \<and> 
          (\<exists>b m. b = Exp_Matrices.\<alpha> (q + 4) (r + 1) + q * q + 2 \<and> m = b * q - q * q - 1 \<and>
          p < m \<and> p mod m = (q * Exp_Matrices.\<alpha> b r - (b * Exp_Matrices.\<alpha> b r -
            Exp_Matrices.\<alpha> b (r + 1))) mod m)" using exp_alpha[of p q r] P by auto
    then show ?Q using P
    proof cases
      case c1
      then show ?thesis by auto
    next
      case c2
      then show ?thesis by auto
    next
      case c3
      obtain b m where
        b_def: "b = Exp_Matrices.\<alpha> (q + 4) (r + 1) + q * q + 2" and
        "m = b * q - q * q - 1" and  
        "p < m" and
        "int (p mod m) = (int q * Exp_Matrices.\<alpha> b r - (int b * Exp_Matrices.\<alpha> b r -
        Exp_Matrices.\<alpha> b (r + 1))) mod int m" 
        using exp_alpha[of p q r] c3 by blast          
      then have "exp_equations p q r b m" unfolding exp_equations_def
        apply(intro conjI, auto simp add: power2_eq_square) using mod_add_right_eq by smt
      then show ?thesis using c3 by blast
    qed
next
  assume ?Q
  then show ?P
  proof (elim disjE)
    (* eliminate disjs, first two trivial cases by auto *)
    show "q = 0 \<and> r = 0 \<and> p = 1 \<Longrightarrow> p = q ^ r" by auto
    show "q = 0 \<and> 0 < r \<and> p = 0 \<Longrightarrow> p = q ^ r" by auto
    (* third, non-trivial case *)
    assume prems: "0 < q \<and> (\<exists>b m. exp_equations p q r b m)"
    obtain b m where cond: "exp_equations p q r b m" using prems by auto
    (* show that the four relevant conditions in exp_alpha hold; first three are easy *)
    hence "int b = Exp_Matrices.\<alpha> (q + 4) (r + 1) + int (q * q) + 2 \<and> 
                                        m = b * q - q * q - 1 \<and> p < m" 
      unfolding exp_equations_def power2_eq_square by auto
    (* the last one requires some extra care; but it's mainly mod_diff_cong *)
    moreover have "int (p mod m) = (int q * Exp_Matrices.\<alpha> b r - 
                               (int b * Exp_Matrices.\<alpha> b r - Exp_Matrices.\<alpha> b (r + 1))) mod int m"
      using cond unfolding exp_equations_def
      using mod_diff_cong[of "(p + b * Exp_Matrices.\<alpha> b r)" m "(q * Exp_Matrices.\<alpha> b r +
        Exp_Matrices.\<alpha> b (r + 1))" "b * Exp_Matrices.\<alpha> b r" "b * Exp_Matrices.\<alpha> b r"]
      unfolding diff_diff_eq2 by auto
    ultimately show "p = q ^ r" using prems exp_alpha by auto
  qed
qed

definition exp ("[_ = _ ^ _]" 1000)
  where "[Q = R ^ S] \<equiv> (TERNARY (\<lambda>a b c. a = b ^ c) Q R S)"

lemma exp_dioph[dioph]:
  fixes P Q R :: polynomial
  defines "D \<equiv> [P = Q ^ R]"
  shows "is_dioph_rel D"
proof -
  define P' Q' R' where pushed_def:
    "P' \<equiv> (push_param P 5)" "Q' \<equiv> (push_param Q 5)" "R' \<equiv> (push_param R 5)"
  define b m a0 a1 a2 where params_def: "b = Param 0" "m = Param 1" "a0 = Param 2"
    "a1 = Param 3" "a2 = Param 4"

  define S1 where "S1 \<equiv> [0=] Q [\<and>] [0=] R [\<and>] P [=] \<^bold>1 [\<or>]
                         [0=] Q [\<and>] (Const 0) [<] R [\<and>] [0=] P"
  define S2 where "S2 \<equiv> [a0 = \<alpha> (Q' [+] (Const 4)) (R' [+] \<^bold>1)]
                         [\<and>] b [=] (a0 [+] Q'[^2] [+] Const 2)"
  define S3 where "S3 \<equiv> (m [+] Q'[^2] [+] Const 1) [=] b [*] Q'
                         [\<and>] P' [<] m"
  define S4 where "S4 \<equiv> [a1 = \<alpha> b R']
                         [\<and>] [a2 = \<alpha> b (R' [+] \<^bold>1)]
                         [\<and>] MOD (P' [+] b [*] a1) m (Q' [*] a1 [+] a2)"

  note S_defs = S1_def S2_def S3_def S4_def

  define S where "S \<equiv> S1 [\<or>] (Q [>] Const 0) [\<and>] ([\<exists>5] S2 [\<and>] S3 [\<and>] S4)"

  have "is_dioph_rel S"
    unfolding S_def S_defs by (auto simp: dioph)

  moreover have "eval S a = eval D a" for a
  proof - 
    define p q r where evaled_defs: "p = peval P a" "q = peval Q a" "r = peval R a"

    show ?thesis
    proof (rule)
      assume "eval S a"
      then show "eval D a"
        unfolding S_def S_defs defs apply (simp add: sq_p_eval)
        unfolding D_def exp_def defs apply simp_all
        unfolding pushed_def params_def apply (auto simp add: push_push[where ?n = 5] push_list_eval)
        unfolding exp_repr exp_equations_def apply simp
        subgoal for ks
          apply (rule exI[of _ "ks!0"], auto) 
          subgoal by (simp add: power2_eq_square)
          subgoal apply (rule exI[of _ "ks!1"], auto)
            by (smt int_ops(7) mult_Suc of_nat_Suc of_nat_add power2_eq_square zmod_int) 
          done
        done
    next
      assume "eval D a"
      then obtain b_val m_val where cond: "(q = 0 \<and> r = 0 \<and> p = 1) \<or> 
                                           (q = 0 \<and> 0 < r \<and> p = 0) \<or> 
                                           (q > 0 \<and> exp_equations p q r b_val m_val)"
        unfolding D_def exp_def exp_repr evaled_defs ternary_eval by auto

      moreover define a0_val a1_val a2_val where
        "a0_val \<equiv> nat (Exp_Matrices.\<alpha> (q + 4) (r + 1))"
        "a1_val \<equiv> nat (Exp_Matrices.\<alpha> b_val r)"
        "a2_val \<equiv> nat (Exp_Matrices.\<alpha> b_val (r + 1))"
      ultimately show "eval S a"
        unfolding S_def S_defs defs evaled_defs apply (simp add: sq_p_eval)
        apply (elim disjE)
        subgoal unfolding defs by simp
        subgoal unfolding defs by simp
        subgoal apply(elim conjE) apply(intro disjI2, intro conjI)
          subgoal by simp
          subgoal premises prems
          proof-
            have bg3: "3 < b_val"
            proof-
              have "b_val = Exp_Matrices.\<alpha> (q + 4) (r + 1) + int q * int q + 2" 
                using cond prems(4) evaled_defs(2) unfolding exp_equations_def by linarith
              moreover have "int q * int q > 0" using evaled_defs(2) prems by simp
              moreover have "Exp_Matrices.\<alpha> (q + 4) (r + 1) > 0" 
                using Exp_Matrices.alpha_superlinear[of "q+4" "r+1"] by linarith
              ultimately show ?thesis by linarith
            qed
            show ?thesis apply (rule exI[of _ "[b_val, m_val, a0_val, a1_val, a2_val]"], intro conjI)
              using prems
              unfolding exp_equations_def pushed_def params_def 
              using push_list_def push_push bg3 Exp_Matrices.alpha_nonnegative apply simp_all
              subgoal using push_list_def by (smt Exp_Matrices.alpha_strictly_increasing int_nat_eq 
                    nat_int numeral_Bit0 numeral_One of_nat_1 of_nat_add of_nat_power plus_1_eq_Suc 
                     power2_eq_square)
              subgoal using push_list_def apply auto by (smt One_nat_def Suc_1 Suc_less_eq 
                      int_nat_eq less_Suc_eq nat_int numeral_3_eq_3 of_nat_add of_nat_mult zmod_int)
            done
          qed
        done
      done
    qed
  qed

  ultimately show ?thesis
    by (auto simp: is_dioph_rel_def)
qed

declare exp_def[defs]

end