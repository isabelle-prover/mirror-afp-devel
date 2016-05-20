theory Inits
imports Main "~~/src/HOL/Library/Sublist"
begin

fun inits where
  "inits [] = [[]]"
| "inits (i#is) = [] # map (op # i) (inits is)"

lemma inits_Snoc[simp]:
  "inits (is@[i]) = inits is @ [is@[i]]"
by (induction "is") auto

lemma inits_eq_Snoc:
  "inits is = xs @ [x] \<longleftrightarrow> (is = [] \<and> xs = [] \<or> (\<exists> i is'. is = is'@[i] \<and> xs = inits is')) \<and> x = is"
by (cases "is" rule: rev_cases) auto

lemma in_set_inits[simp]: "is' \<in> set (inits is) \<longleftrightarrow> prefixeq is' is"
  by (induction "is'" arbitrary: "is"; rename_tac "is", case_tac "is"; auto)

lemma prefixeq_snocD: "prefixeq (xs@[x]) ys \<Longrightarrow> prefix xs ys"
  by (simp add: prefixI' prefix_order.dual_order.strict_trans1)

lemma prefixeq_butlast: "prefixeq (butlast xs) xs"
  by (metis append_butlast_last_id butlast.simps(1) prefixI' prefix_order.eq_iff prefix_order.less_imp_le)

lemma prefixeq_app_Cons_elim:
  assumes "prefixeq (xs@[y]) (z#zs)"
  obtains "xs = []" and "y = z"
   | xs' where "xs = z#xs'" and "prefixeq (xs'@[y]) zs"
using assms by (cases xs) auto

lemma prefixeq_app_Cons_simp:
  "prefixeq (xs@[y]) (z#zs) \<longleftrightarrow> xs = [] \<and> y = z \<or> xs = z#tl xs \<and> prefixeq (tl xs@[y]) zs"
 by (cases xs) auto

end