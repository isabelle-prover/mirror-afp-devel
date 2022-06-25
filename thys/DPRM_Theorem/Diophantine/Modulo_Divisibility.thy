subsection \<open>Mod is Diophantine\<close>

theory Modulo_Divisibility
  imports Existential_Quantifier
begin

text \<open> Divisibility is diophantine \<close>
definition dvd ("DVD _ _" 1000) where "DVD Q R \<equiv> (BINARY (dvd) Q R)"

lemma dvd_repr:
  fixes a b :: nat
  shows "a dvd b \<longleftrightarrow> (\<exists>x. x * a = b)"
  using dvd_class.dvd_def by auto

lemma dvd_dioph[dioph]: "is_dioph_rel (DVD Q R)"
proof -
  define Q' R' where pushed_defs: "Q' \<equiv> push_param Q 1" "R' \<equiv> push_param R 1"
  define D where "D \<equiv> [\<exists>] (Param 0 [*] Q' [=] R')"

  have "eval (DVD Q R) a = eval D a" for a
    unfolding D_def pushed_defs defs using push_push1 apply (auto simp: push0)
    unfolding dvd_def by (auto simp: dvd_repr binary_eval)

  moreover have "is_dioph_rel D"
    unfolding D_def by (auto simp: dioph)

  ultimately show ?thesis
    by (auto simp: is_dioph_rel_def)
qed

declare dvd_def[defs]

(* Congruence is diophantine *)
definition mod ("MOD _ _ _" 1000)
  where "MOD A B C \<equiv> (TERNARY (\<lambda>a b c. a mod b = c mod b) A B C)"
declare mod_def[defs]

lemma mod_repr: 
  fixes a b c :: nat
  shows "a mod b = c mod b \<longleftrightarrow> (\<exists>x y. c + x*b = a + y*b)"
  by (metis mult.commute nat_mod_eq_iff)

lemma mod_dioph[dioph]:
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
      by auto (metis mod_mult_self3 push_push_simp pushed_defs(1) pushed_defs(2) pushed_defs(3))
    show "eval D a \<Longrightarrow> eval DS a"
      unfolding DS_def defs D_def mod_def
      apply (auto simp add: mod_repr)
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

declare mod_def[defs]

end