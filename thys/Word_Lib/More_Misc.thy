
section \<open>Miscellaneous lemmas\<close>

theory More_Misc
imports Main
begin

lemma power_numeral: "a ^ numeral k = a * a ^ (pred_numeral k)"
  by (simp add: numeral_eq_Suc)

lemma funpow_numeral [simp]: "f ^^ numeral k = f \<circ> f ^^ (pred_numeral k)"
  by (simp add: numeral_eq_Suc)

lemma funpow_minus_simp: "0 < n \<Longrightarrow> f ^^ n = f \<circ> f ^^ (n - 1)"
  by (auto dest: gr0_implies_Suc)

lemma rco_alt: "(f \<circ> g) ^^ n \<circ> f = f \<circ> (g \<circ> f) ^^ n"
  apply (rule ext)
  apply (induct n)
   apply (simp_all add: o_def)
  done

lemma union_sub:
  "\<lbrakk>B \<subseteq> A; C \<subseteq> B\<rbrakk> \<Longrightarrow> (A - B) \<union> (B - C) = (A - C)"
  by fastforce

lemma insert_sub:
  "x \<in> xs \<Longrightarrow> (insert x (xs - ys)) = (xs - (ys - {x}))"
  by blast

lemma ran_upd:
  "\<lbrakk> inj_on f (dom f); f y = Some z \<rbrakk> \<Longrightarrow> ran (\<lambda>x. if x = y then None else f x) = ran f - {z}"
  unfolding ran_def
  apply (rule set_eqI)
  apply simp
  by (metis domI inj_on_eq_iff option.sel)

lemma if_apply_def2:
  "(if P then F else G) = (\<lambda>x. (P \<longrightarrow> F x) \<and> (\<not> P \<longrightarrow> G x))"
  by simp

lemma case_bool_If:
  "case_bool P Q b = (if b then P else Q)"
  by simp

lemma if_f:
  "(if a then f b else f c) = f (if a then b else c)"
  by simp

lemmas ls_splits = prod.split prod.split_asm if_split_asm

lemma size_if: "size (if p then xs else ys) = (if p then size xs else size ys)"
  by (fact if_distrib)

lemma if_Not_x: "(if p then \<not> x else x) = (p = (\<not> x))"
  by auto

lemma if_x_Not: "(if p then x else \<not> x) = (p = x)"
  by auto

lemma if_same_and: "(If p x y \<and> If p u v) = (if p then x \<and> u else y \<and> v)"
  by auto

lemma if_same_eq: "(If p x y  = (If p u v)) = (if p then x = u else y = v)"
  by auto

lemma if_same_eq_not: "(If p x y = (\<not> If p u v)) = (if p then x = (\<not> u) else y = (\<not> v))"
  by auto

lemma the_elemI: "y = {x} \<Longrightarrow> the_elem y = x"
  by simp

lemma nonemptyE: "S \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> R) \<Longrightarrow> R"
  by auto

lemmas xtr1 = xtrans(1)
lemmas xtr2 = xtrans(2)
lemmas xtr3 = xtrans(3)
lemmas xtr4 = xtrans(4)
lemmas xtr5 = xtrans(5)
lemmas xtr6 = xtrans(6)
lemmas xtr7 = xtrans(7)
lemmas xtr8 = xtrans(8)

lemmas if_fun_split = if_apply_def2

end
