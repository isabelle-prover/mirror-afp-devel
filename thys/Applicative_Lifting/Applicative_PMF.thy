(* Author: Andreas Lochbihler, ETH Zurich *)

subsection \<open>Probability mass functions\<close>

theory Applicative_PMF imports
  Applicative
  "~~/src/Tools/Adhoc_Overloading"
  "~~/src/HOL/Probability/Probability"
begin

lemma pair_return_pmf1: "pair_pmf (return_pmf x) y = map_pmf (Pair x) y"
by(simp add: pair_pmf_def bind_return_pmf map_pmf_def)

lemma pair_return_pmf2: "pair_pmf x (return_pmf y) = map_pmf (\<lambda>x. (x, y)) x"
by(simp add: pair_pmf_def bind_return_pmf map_pmf_def)

lemma pair_pair_pmf: "pair_pmf (pair_pmf u v) w = map_pmf (\<lambda>(x, (y, z)). ((x, y), z)) (pair_pmf u (pair_pmf v w))"
by(simp add: pair_pmf_def bind_return_pmf map_pmf_def bind_assoc_pmf)

lemma pair_commute_pmf: "pair_pmf x y = map_pmf (\<lambda>(x, y). (y, x)) (pair_pmf y x)"
unfolding pair_pmf_def by(subst bind_commute_pmf)(simp add: map_pmf_def bind_assoc_pmf bind_return_pmf)


abbreviation (input) pure_pmf :: "'a \<Rightarrow> 'a pmf"
where "pure_pmf \<equiv> return_pmf"

definition ap_pmf :: "('a \<Rightarrow> 'b) pmf \<Rightarrow> 'a pmf \<Rightarrow> 'b pmf"
where "ap_pmf f x = map_pmf (\<lambda>(f, x). f x) (pair_pmf f x)"

adhoc_overloading Applicative.ap ap_pmf

context begin interpretation applicative_syntax .

lemma ap_pmf_id: "pure_pmf (\<lambda>x. x) \<diamondop> x = x"
by(simp add: ap_pmf_def pair_return_pmf1 pmf.map_comp o_def)

lemma ap_pmf_comp: "pure_pmf op \<circ> \<diamondop> u \<diamondop> v \<diamondop> w = u \<diamondop> (v \<diamondop> w)"
by(simp add: ap_pmf_def pair_return_pmf1 pair_map_pmf1 pair_map_pmf2 pmf.map_comp o_def split_def pair_pair_pmf)

lemma ap_pmf_homo: "pure_pmf f \<diamondop> pure_pmf x = pure_pmf (f x)"
by(simp add: ap_pmf_def pair_return_pmf1)

lemma ap_pmf_interchange: "u \<diamondop> pure_pmf x = pure_pmf (\<lambda>f. f x) \<diamondop> u"
by(simp add: ap_pmf_def pair_return_pmf1 pair_return_pmf2 pmf.map_comp o_def)

lemma ap_pmf_K: "return_pmf (\<lambda>x _. x) \<diamondop> x \<diamondop> y = x"
by(simp add: ap_pmf_def pair_map_pmf1 pmf.map_comp pair_return_pmf1 o_def split_def map_fst_pair_pmf)

lemma ap_pmf_C: "return_pmf (\<lambda>f x y. f y x) \<diamondop> f \<diamondop> x \<diamondop> y = f \<diamondop> y \<diamondop> x"
apply(simp add: ap_pmf_def pair_map_pmf1 pmf.map_comp pair_return_pmf1 pair_pair_pmf o_def split_def)
apply(subst (2) pair_commute_pmf)
apply(simp add: pair_map_pmf2 pmf.map_comp o_def split_def)
done

applicative pmf (C, K)
for
  pure: pure_pmf
  ap: ap_pmf
by(rule ap_pmf_id ap_pmf_comp[unfolded o_def[abs_def]] ap_pmf_homo ap_pmf_interchange ap_pmf_C ap_pmf_K)+

end

end