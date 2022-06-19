subsubsection \<open>Equations for arithmetization constants\<close>

theory Constants_Equations imports Equation_Setup "../Register_Machine/MachineMasking"
                                   "../Diophantine/Binary_And"

begin

context rm_eq_fixes
begin                     

  text \<open>Equation 4.14\<close>
  definition constant_b :: "bool" where
    "constant_b \<equiv> b = B c"
  
  text \<open>Equation 4.16\<close>
  definition constant_d :: "bool" where
    "constant_d \<equiv> d = D q c b"
  
  text \<open>Equation 4.18\<close>
  definition constant_e :: "bool" where
    "constant_e \<equiv> e = E q b"
  
  text \<open>Equation 4.21\<close>
  definition constant_f :: "bool" where
    "constant_f \<equiv> f = F q c b"
  
  text \<open>Equation not in the book\<close>
  definition c_gt_0 :: "bool" where
    "c_gt_0 \<equiv> c > 0"
  
  text \<open>Equation 4.26\<close>
  definition a_bound :: "bool" where
    "a_bound \<equiv> a < 2 ^ c"
  
  text \<open>Equation not in the book\<close>
  definition q_gt_0 :: "bool" where
    "q_gt_0 \<equiv> q > 0"


  definition constants_equations :: "bool" where
    "constants_equations \<equiv> constant_b \<and> constant_d \<and> constant_e \<and> constant_f"

  definition miscellaneous_equations :: "bool" where
    "miscellaneous_equations \<equiv> c_gt_0 \<and> a_bound \<and> q_gt_0 "

end

context register_machine
begin

definition rm_constant_equations :: 
  "polynomial \<Rightarrow> polynomial \<Rightarrow> polynomial \<Rightarrow> polynomial \<Rightarrow> polynomial \<Rightarrow> polynomial \<Rightarrow> relation" 
  ("[CONST] _ _ _ _ _ _") where
  "[CONST] b c d e f q \<equiv> NARY (\<lambda>l. rm_eq_fixes.constants_equations 
                                   (l!0) (l!1) (l!2) (l!3) (l!4) (l!5)) [b, c, d, e, f, q]"

definition rm_miscellaneous_equations :: 
  "polynomial \<Rightarrow> polynomial \<Rightarrow> polynomial \<Rightarrow> relation" 
  ("[MISC] _ _ _") where
  "[MISC] c a q \<equiv> NARY (\<lambda>l. rm_eq_fixes.miscellaneous_equations 
                                   (l!0) (l!1) (l!2)) [c, a, q]"

lemma rm_constant_equations_dioph:
  fixes b c d e f q
  defines "DR \<equiv> [CONST] b c d e f q"
  shows "is_dioph_rel DR"
proof-
  have fx: "rm_eq_fixes p n"
    using rm_eq_fixes_def local.register_machine_axioms by auto

  define b' c' d' e' f' q'  where pushed_defs:
    "b' = (push_param b 2)" "c' = (push_param c 2)" "d' = (push_param d 2)"
    "e' = (push_param e 2)" "f' = (push_param f 2)" "q' = (push_param q 2)"

  define s t where params_def: "s = Param 0" "t = Param 1"

  (* using equations (4.31) - (4.33) *)
  define DS1 where "DS1 \<equiv> [b' = Const 2 ^ (c' [+] \<^bold>1)] [\<and>] 
                        [s =  Const 2 ^ c'] [\<and>] [t = b' ^ (q' [+] \<^bold>1)] [\<and>]
                        (b' [-] \<^bold>1) [*] d' [=] (s [-] \<^bold>1) [*] (t [-] \<^bold>1)"

  define DS2 where "DS2 \<equiv> (b' [-] \<^bold>1) [*] e' [=] t [-] \<^bold>1  [\<and>]
                          (b' [-] \<^bold>1) [*] f' [=] s [*] (t [-] \<^bold>1)"

  define DS where "DS \<equiv> [\<exists>2] DS1 [\<and>] DS2"

  have "eval DS a = eval DR a" for a 
    unfolding DR_def DS_def DS1_def DS2_def rm_constant_equations_def defs
    apply (auto simp add: fx rm_eq_fixes.constants_equations_def[of p n])
    unfolding pushed_defs params_def push_push apply (auto simp add: push_list_eval)
    apply (auto simp add: fx rm_eq_fixes.constant_b_def[of p n] B_def 
      rm_eq_fixes.constant_d_def[of p n] rm_eq_fixes.constant_e_def[of p n] 
      rm_eq_fixes.constant_f_def[of p n])
    using d_geom_series[of "2 * 2 ^ peval c a" "peval c a" "(peval q a)" " peval d a"]
    using e_geom_series[of "(2 * 2 ^ peval c a)" "peval q a" "peval e a"]
    using f_geom_series[of  "2 * 2 ^ peval c a"  "peval c a" "(peval q a)" " peval f a"] 
    apply (auto) 
    apply (rule exI[of _ "[2 ^ peval c a, peval b a * peval b a ^ peval q a]"]) 
    using  push_list_def push_push by auto

    
  moreover have "is_dioph_rel DS" unfolding DS_def DS1_def DS2_def by (simp add: dioph)

  ultimately show ?thesis
    by (simp add: is_dioph_rel_def)
qed

lemma rm_miscellaneous_equations_dioph:
  fixes c a q
  defines "DR \<equiv> [MISC] a c q"
  shows "is_dioph_rel DR"
proof-
  define c' a' q' where pushed_defs:
      "c' == (push_param c 1)" "a' == (push_param a 1)" "q' = (push_param q 1)"

  define DS where "DS \<equiv>  [\<exists>] c' [>] \<^bold>0 
                  [\<and>]  [(Param 0) = (Const 2) ^ c'] [\<and>] a'[<] Param 0 
                  [\<and>] q' [>] \<^bold>0"

  have "eval DS a = eval DR a" for a unfolding DS_def defs DR_def 
    using rm_miscellaneous_equations_def 
    rm_eq_fixes.miscellaneous_equations_def rm_eq_fixes.c_gt_0_def rm_eq_fixes.a_bound_def 
    rm_eq_fixes.q_gt_0_def rm_eq_fixes_def local.register_machine_axioms apply auto 
    unfolding pushed_defs push_push1 
    apply (auto, rule exI[of _ "2 ^ peval c a"]) unfolding push0 by auto
     

  moreover have "is_dioph_rel DS" unfolding DS_def by (simp add: dioph)

  ultimately show ?thesis
    by (simp add: is_dioph_rel_def)
qed


end

end