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

lemma in_set_inits[simp]: "is' \<in> set (inits is) \<longleftrightarrow> prefix is' is"
  by (induction "is'" arbitrary: "is"; rename_tac "is", case_tac "is"; auto)

lemma prefix_snocD: "prefix (xs@[x]) ys \<Longrightarrow> strict_prefix xs ys"
  by (simp add: strict_prefixI' prefix_order.dual_order.strict_trans1)

lemma prefixeq_butlast: "prefix (butlast xs) xs"
  by (metis append_butlast_last_id butlast.simps(1) strict_prefixI' prefix_order.eq_iff prefix_order.less_imp_le)

lemma prefix_app_Cons_elim:
  assumes "prefix (xs@[y]) (z#zs)"
  obtains "xs = []" and "y = z"
   | xs' where "xs = z#xs'" and "prefix (xs'@[y]) zs"
using assms by (cases xs) auto

lemma prefix_app_Cons_simp:
  "prefix (xs@[y]) (z#zs) \<longleftrightarrow> xs = [] \<and> y = z \<or> xs = z#tl xs \<and> prefix (tl xs@[y]) zs"
 by (cases xs) auto

end