
theory Extra
imports Main Equiv_Relations "~~/src/HOL/Library/Option_ord"
begin

(* Extra lemmas that are not noteworthy. *)

lemma relation_mono:
  "\<lbrakk> A \<subseteq> C; B \<subseteq> D \<rbrakk> \<Longrightarrow> A \<times> B \<subseteq> C \<times> D"
  by bestsimp

lemma quotientI2:
  "\<lbrakk> x \<in> A; X = r `` {x} \<rbrakk> \<Longrightarrow> X \<in> A // r"
  by (simp add: quotientI)

instantiation prod :: (linorder, linorder) linorder
begin

definition less_eq_prod
  where "x \<le> y \<equiv> fst x < fst y \<or> (fst x = fst y \<and> snd x \<le> snd y)"

definition less_prod
  where "(x::'a \<times> 'b) < y \<equiv> fst x < fst y \<or> (fst x = fst y \<and> snd x < snd y)"

instance by intro_classes (unfold less_eq_prod_def less_prod_def, auto)

end

instantiation unit :: linorder
begin

definition less_eq_unit_def: "(x :: unit) \<le> y \<equiv> True"
definition less_unit_def: "(x :: unit) < y \<equiv> False"

instance
  apply intro_classes
  apply (unfold less_eq_unit_def less_unit_def)
  apply auto
  done

end

lemma map_prod_eq:
  assumes f: "map fst xs = map fst ys"
      and s: "map snd xs = map snd ys"
  shows "xs = ys"
  using assms by (induct rule: list_induct2[OF map_eq_imp_length_eq[OF f]]) (simp_all add: prod_eqI)

end

