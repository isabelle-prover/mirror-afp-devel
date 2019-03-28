(* Author: René Thiemann *)

text \<open>Generalizing Cramer's Lemma for fields to integral domains via fraction fields\<close>

theory Cramer_Lemma_Idom
  imports "HOL-Analysis.Determinants"
  "HOL-Computational_Algebra.Fraction_Field" 
begin

abbreviation "to_fract \<equiv> \<lambda> x. Fract x 1" 

named_theorems Fract_simps

lemma Fract_plus[Fract_simps]: "to_fract (x + y) = to_fract x + to_fract y" by simp
lemma Fract_times[Fract_simps]: "to_fract (x * y) = to_fract x * to_fract y" by simp
lemma Fract_diff[Fract_simps]: "to_fract (x - y) = to_fract x - to_fract y" by simp
lemma Fract_minus[Fract_simps]: "to_fract (- x) = - to_fract x" by simp
lemma Fract_zero[Fract_simps]: "to_fract 0 = 0" by (rule fract_collapse)
lemma Fract_one[Fract_simps]: "to_fract 1 = 1" by (rule fract_collapse)
lemma Fract_of_nat[Fract_simps]: "to_fract (of_nat x) = of_nat x" 
  by (rule Fract_of_nat_eq)

lemma Fract_of_int[Fract_simps]: "to_fract (of_int x) = of_int x" (is "to_fract (?oi1 x) = ?oi2 x")
proof (cases "x \<ge> 0")
  case True
  hence id: "?oi1 x = of_nat (nat x)" "?oi2 x = of_nat (nat x)" by auto
  show ?thesis unfolding id Fract_simps by simp
next
  case False
  hence id: "?oi1 x = - of_nat (nat (-x))" "?oi2 x = - of_nat (nat (-x))" by auto
  show ?thesis unfolding id Fract_simps by simp
qed

lemma Fract_sum[Fract_simps]: "to_fract (sum x A) = sum (to_fract o x) A" 
  by (induct A rule: infinite_finite_induct, auto simp: Fract_simps)

lemma Fract_prod[Fract_simps]: "to_fract (prod x A) = prod (to_fract o x) A" 
  by (induct A rule: infinite_finite_induct, auto simp: Fract_simps)

lemma Fract_det[Fract_simps]: fixes A :: "'a::idom^'n^'n"
  shows "to_fract (det A) = det ( \<chi> i j. to_fract (A $ i $ j))" 
  unfolding det_def Fract_simps o_def 
  by (intro sum.cong refl arg_cong2[of _ _ _ _ "(*)"] prod.cong, auto)

proposition  cramer_lemma_idom:
  fixes A :: "'a::idom^'n^'n"
  shows "det((\<chi> i j. if j = k then (A *v x)$i else A$i$j) :: 'a^'n^'n) = x$k * det A"
proof -
  let ?f = "to_fract :: 'a \<Rightarrow> _" 
  let ?x = "\<chi> i. ?f (x $ i)" 
  let ?A = "\<chi> i j. ?f (A $ i $ j)" 
  have "det((\<chi> i j. if j = k then (?A *v ?x)$i else ?A$i$j)) = ?x$k * det ?A" 
    by (rule cramer_lemma)
  also have "det ?A = ?f (det A)" unfolding Fract_simps .. 
  also have "?x$k * \<dots> = ?f (x$k * det A)" unfolding Fract_simps by simp
  also have "det((\<chi> i j. if j = k then (?A *v ?x)$i else ?A$i$j))
    = ?f (det((\<chi> i j. if j = k then (A *v x)$i else A$i$j)))" 
    unfolding Fract_simps
    by (rule arg_cong[of _ _ det], auto intro!: ext simp: matrix_vector_mult_def Fract_sum)
  finally show ?thesis by (simp add: eq_fract)
qed

end