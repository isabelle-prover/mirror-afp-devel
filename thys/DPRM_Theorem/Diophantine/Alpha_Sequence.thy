subsection \<open>Diophantine description of alpha function\<close>

theory Alpha_Sequence
  imports Modulo_Divisibility "Exponentiation"
begin

text \<open>The alpha function is diophantine\<close>
definition alpha ("[_ = \<alpha> _ _]" 1000)
  where "[X = \<alpha> B N] \<equiv> (TERNARY (\<lambda>b n x. b > 3 \<and> x = Exp_Matrices.\<alpha> b n) B N X)"

lemma alpha_dioph[dioph]:
  fixes B N X
  defines "D \<equiv> [X = \<alpha> B N]"
  shows "is_dioph_rel D"
proof -
  define r s t u v w x y where param_defs:
    "r == (Param 0)" "s == (Param 1)" "t == (Param 2)" "u == (Param 3)"  "v == (Param 4)"
    "w == (Param 5)" "x == (Param 6)" "y == (Param 7)"
  define B' X' N' where pushed_defs: "B' ==  (push_param B 8)" "X' ==  (push_param X 8)"
                                      "N' ==  (push_param N 8)"

  (* eqns. (3.41) -- (3.55) from YuMat lecture notes (p. 36) where "a" = X and "c" = N here *)
  (* don't confuse capital X with x == (param 6) here, this is unhappy notation *)
  define DR1 where "DR1 \<equiv> B' [>] (Const 3) [\<and>] (Const 1 [+] B' [*] u [*] t [=] u[^2] [+] t[^2])"
  define DR2 where "DR2 \<equiv> (Const 1 [+] B' [*] s [*] r [=] s[^2] [+] r[^2]) [\<and>] r [<] s" 
  define DR3 where "DR3 \<equiv> (DVD (u[^2]) s) [\<and>] (v [+] (Const 2) [*] r [=] B' [*] s)"
  define DR4 where "DR4 \<equiv> (MOD B' v w) [\<and>] (MOD (Const 2) u w) [\<and>] (Const 2) [<] w"
  define DR5 where "DR5 \<equiv> (Const 1 [+] w [*] x [*] y [=] x[^2] [+] y[^2])"
  define DR6 where "DR6 \<equiv> (Const 2) [*] X' [<] u [\<and>] (Const 2) [*] X' [<] v
                           [\<and>] (MOD x v X') [\<and>] (Const 2) [*] N' [<] u [\<and>] MOD x u N'"

  define DR where "DR \<equiv> [\<exists>8] DR1 [\<and>] DR2 [\<and>] DR3 [\<and>] DR4 [\<and>] DR5 [\<and>] DR6"
  (* definition would otherwise be too long to handle for Isabelle *)

  note DR_defs = DR1_def DR2_def DR3_def DR4_def DR5_def DR6_def

  have "is_dioph_rel DR"
    unfolding DR_def DR_defs
    by (auto simp: dioph)

  moreover have "eval D a = eval DR a" for a
  proof -
    define x_ev b n where evaled_defs: "x_ev \<equiv> peval X a" "b \<equiv> peval B a" "n \<equiv> peval N a"
    have h: "eval D a = (\<exists>r s t u v w x y::nat. Exp_Matrices.alpha_equations x_ev b n r s t u v w x y)"
      unfolding D_def alpha_def evaled_defs defs using alpha_equivalence by simp

    show ?thesis
    proof (rule)
      assume "eval D a"
      then obtain r s t u v w x y :: nat where "Exp_Matrices.alpha_equations x_ev b n r s t u v w x y"
        using h by auto
      then show "eval DR a"
        unfolding evaled_defs Exp_Matrices.alpha_equations_def
        unfolding DR_def DR_defs defs param_defs apply (auto simp: sq_p_eval)
        apply (rule exI[of _ "[r, s, t, u, v, w, x, y]"])
        unfolding pushed_defs by (auto simp add: push_push[where ?n = 8] push_list_eval) 
    next
      assume "eval DR a"
      then show "eval D a"
        (* simplify "eval DR a" and undo all the pushes *)
        unfolding DR_def DR_defs defs param_defs apply (auto simp: sq_p_eval)
        unfolding pushed_defs apply (auto simp add: push_push[where ?n = 8] push_list_eval)
        (* simplify "eval D a" using the above fact h *)
        unfolding h Exp_Matrices.alpha_equations_def evaled_defs
        subgoal for ks
          apply (rule exI[of _ "ks!0"]) apply (rule exI[of _ "ks!1"]) apply (rule exI[of _ "ks!2"])
          apply (rule exI[of _ "ks!3"]) apply (rule exI[of _ "ks!4"]) apply (rule exI[of _ "ks!5"])
          apply (rule exI[of _ "ks!6"]) apply (rule exI[of _ "ks!7"])
          by simp_all
        done
    qed
  qed

  ultimately show ?thesis
    by (auto simp: is_dioph_rel_def)
qed

declare alpha_def[defs]

end