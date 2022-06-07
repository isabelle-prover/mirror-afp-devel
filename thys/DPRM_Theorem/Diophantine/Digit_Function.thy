subsection \<open>Digit function is Diophantine\<close>

theory Digit_Function
  imports Exponential_Relation "Digit_Expansions.Bits_Digits"
begin

definition digit ("[ _ = Digit _ _ _]" [999] 1000)
  where "[D = Digit AA K BASE] \<equiv> (QUATERNARY (\<lambda>d a k b. b > 1
                                    \<and> d = nth_digit a k b) D AA K BASE)"
lemma mod_dioph2[dioph]:
  fixes A B C
  defines "D \<equiv> (MOD A B C)"
  shows "is_dioph_rel D"
proof -
  define A' B' C' where pushed_defs: "A' \<equiv> push_param A 2" "B' \<equiv> push_param B 2" "C' \<equiv> push_param C 2"
  define DS where "DS \<equiv> [\<exists>2] (Param 0 [*] B' [+] C' [=] Param 1 [*] B' [+] A')"

  have "eval DS a = eval D a" for a
  proof 
    show "eval DS a \<Longrightarrow> eval D a"
      unfolding DS_def defs D_def mod_def
      by auto (metis add.commute mod_mult_self1 push_push_simp pushed_defs(1)
                      pushed_defs(2) pushed_defs(3))
    show "eval D a \<Longrightarrow> eval DS a"
      unfolding DS_def defs D_def mod_def
      apply (auto simp: mod_repr)
      subgoal for x y
        apply (rule exI[of _ "[x, y]"])
        unfolding pushed_defs by (simp add: push_push[where ?n = 2] push_list_eval)
      done
  qed

  moreover have "is_dioph_rel DS"
    unfolding DS_def by (simp add: dioph)

  ultimately show ?thesis
    by (auto simp: is_dioph_rel_def)
qed

lemma digit_dioph[dioph]:
  fixes D A B K :: polynomial
  defines "DR \<equiv> [D = Digit A K B]"
  shows "is_dioph_rel DR"
proof -
  define D' A' B' K' where pushed_defs:
    "D' == (push_param D 4)" "A' == (push_param A 4)" "B' == (push_param B 4)" "K' == (push_param K 4)"
  (* Param 2 = b^(k+1), Param 3 = b^k *)
  define x y where param_defs:
    "x == (Param 0)" "y == (Param 1)"

  define DS where "DS \<equiv> [\<exists>4] ( B' [>] Const 1  [\<and>]
                               [(Param 2) = B' ^ (K' [+] Const 1)] [\<and>]
                               [(Param 3) = B' ^ K'] [\<and>] 
                               A' [=] x [*] (Param 2) [+] D' [*] (Param 3) [+] y [\<and>] 
                               D' [<] B' [\<and>] 
                               y [<] (Param 3)) "
  have "eval DS a = eval DR a" for a
  proof
    show "eval DS a \<Longrightarrow> eval DR a"
      unfolding DS_def defs DR_def digit_def apply auto
      unfolding pushed_defs push_push using pushed_defs push_push digit_gen_equiv by auto

    assume asm: "eval DR a"
    then obtain x_val y_val where cond: "(peval A a) = x_val *  (peval B a)^( (peval K a)+1) 
                                        + (peval D a) *  (peval B a)^ (peval K a) + y_val
                                      \<and> (peval D a) < (peval B a) 
                                      \<and> y_val <  (peval B a)^ (peval K a)"
      unfolding DS_def defs DR_def digit_def using digit_gen_equiv by auto metis
    show "eval DS a"
      using asm unfolding DS_def defs DR_def digit_def apply auto
      apply (rule exI[of _ "[x_val, y_val, (peval B a) ^ ((peval K a) + 1),
                                                        (peval B a) ^ (peval K a)]"])
      unfolding pushed_defs using param_defs push_push push_list_def cond by auto+
  qed

  moreover have "is_dioph_rel DS"
    unfolding DS_def by (simp add: dioph)

  ultimately show ?thesis 
    by (auto simp: is_dioph_rel_def) 
qed

declare digit_def[defs]


end