theory Splay_Tree_Analysis_Base
imports Complex_Main "~~/src/HOL/Library/Tree"
begin

section "Splay Tree Analysis Basics"

(* FIXME mv *)

text{* Function @{text size1} counts the number of Leaves. *}

definition "size1(t::'a tree) = size t + 1"
declare size1_def[simp]

lemma size1_simps[simp]:
  "size1 Leaf = 1"
  "size1(Node l x r) = size1 l + size1 r"
by simp_all


abbreviation "\<phi> t == log 2 (size1 t)"

fun \<Phi> :: "'a tree \<Rightarrow> real" where
"\<Phi> Leaf = 0" |
"\<Phi> (Node l a r) = \<Phi> l + \<Phi> r + \<phi> (Node l a r)"

lemma add_log_log1:
  assumes "x > 0" "y > 0" shows "1 + log 2 x + log 2 y < 2 * log 2 (x+y)"
proof -
  have 1: "2*x*y < (x+y)^2" using assms
    by(simp add: numeral_eq_Suc algebra_simps add_pos_pos)
  show ?thesis
    apply(rule powr_less_cancel_iff[of 2, THEN iffD1])
     apply simp
    using assms 1 by(simp add: powr_add log_powr[symmetric] powr_numeral)
qed

end
