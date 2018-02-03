(*
    Authors:    Jose Divasón
                Sebastiaan Joosten
                René Thiemann
                Akihisa Yamada
    License:    BSD
*)

section \<open>Lattice\<close>

text \<open>This theory implements the mathematical definition of lattice by means of locales
  and shows it forms a (HOL-Algebra) module.
\<close> 

theory Vector_Lattice_Locale
  imports
  "HOL-Library.Multiset"
  Norms
  Missing_Lemmas
begin

locale vlattice = abelian_group G for G (structure)
begin

fun nat_mult where "nat_mult 0 v = \<zero>" | "nat_mult (Suc n) v = v \<oplus> nat_mult n v"

lemma nat_mult_closed [simp]: "v \<in> carrier G \<Longrightarrow> nat_mult n v \<in> carrier G"
  by (induct n, auto)

lemma nat_mult_add_distrib1 [simp]:
  assumes v: "v \<in> carrier G" shows "nat_mult (x+y) v = nat_mult x v \<oplus> nat_mult y v"
  by (induct x, insert v, auto intro!: a_assoc[symmetric])

lemma nat_mult_add_distrib2 [simp]:
  assumes "v \<in> carrier G" and "w \<in> carrier G"
  shows "nat_mult x (v \<oplus> w) = nat_mult x v \<oplus> nat_mult x w"
proof(induct x)
  case (Suc x)
  have "nat_mult (Suc x) (v \<oplus> w) = v \<oplus> w \<oplus> nat_mult x (v \<oplus> w)" by simp
  also have "\<dots> = v \<oplus> (w \<oplus> nat_mult x v) \<oplus> nat_mult x w"
    using assms a_assoc by (auto simp: Suc)
  also have "w \<oplus> nat_mult x v = nat_mult x v \<oplus> w" using assms a_comm by auto
  finally show ?case using a_assoc assms by auto
qed simp

definition int_mult (infixl "\<cdot>" 70)
where "x \<cdot> v \<equiv> if x \<ge> 0 then nat_mult (Int.nat x) v else \<ominus> nat_mult (Int.nat (-x)) v"

lemma int_mult_closed [simp]: "v \<in> carrier G \<Longrightarrow> x \<cdot> v \<in> carrier G"
  by (unfold int_mult_def, auto)

lemma [simp]: assumes "v \<in> carrier G"
  shows zero_int_mult: "0 \<cdot> v = \<zero>" and one_int_mult: "1 \<cdot> v = v" and uminus_int_mult: "-x \<cdot> v = \<ominus> (x \<cdot> v)"
  using assms by (simp_all add: int_mult_def)

lemma int_mult_add_1:
  assumes v: "v \<in> carrier G"
  shows "(x + 1) \<cdot> v = v \<oplus> x \<cdot> v" (is "?l = ?r")
proof (cases x "-1::int" rule:linorder_cases)
  case greater
  then have "x \<ge> 0" by auto
  then obtain n where x: "x = int n" using zero_le_imp_eq_int by auto
  have "?l = int_mult (x + int 1) v" by simp
  also have "... = ?r" using v by (unfold x int_mult_def nat_int_add, auto)
  finally show ?thesis.
next
  case equal
  with v show ?thesis by (auto simp: a_inv_def)
next
  case less
  then have "- x - 2 \<ge> 0" by auto
  from zero_le_imp_eq_int[OF this] obtain n where "- x - 2 = int n" by auto
  then have x: "x = - (int n + int 2)" by auto
  have "?r = \<ominus> v \<ominus> int n \<cdot> v"
    using v 
    by (unfold x int_mult_def add.inverse_inverse nat_int_add, 
        simp add: a_assoc[symmetric] minus_add r_neg minus_eq)
  also have "... = (- (int 1 + int n)) \<cdot> v"
    using v 
    by (unfold int_mult_def add.inverse_inverse nat_int_add,
        simp add:add.inv_mult_group a_comm minus_eq)
  also have "... = ?l" by (auto simp: x)
  finally show ?thesis by simp
qed

lemmas int_mult_1_add = int_mult_add_1[folded add.commute[of 1]]

lemma int_mult_minus_1:
  assumes v: "v \<in> carrier G"
  shows "(x - 1) \<cdot> v = \<ominus> v \<oplus> x \<cdot> v" (is "?l = ?r")
proof (cases x "1::int" rule:linorder_cases)
  case less
  then have "-x \<ge> 0" by auto
  from zero_le_imp_eq_int[OF this] obtain n where x: "-x = int n"  by auto
  have "?l = (-(int n + int 1)) \<cdot> v" by (simp add: x[symmetric])
  also have "... = \<ominus> v \<oplus> - int n \<cdot> v"
    using v by (unfold int_mult_def add.inverse_inverse nat_int_add, simp add: minus_add)
  also have "... = ?r" by (fold x, auto)
  finally show ?thesis.
next
  case equal
  with v show ?thesis by (auto simp: l_neg)
next
  case greater
  then have "x - 2 \<ge> 0" by auto
  from zero_le_imp_eq_int[OF this] obtain n where "x - 2 = int n" by auto
  then have x: "x = int n + int 2" by auto
  have "?r = \<ominus> v \<oplus> (v \<oplus> (v \<oplus> nat_mult n v))"
     by (unfold x int_mult_def add.inverse_inverse nat_int_add, simp)
  also have "\<dots> = v \<oplus> int n \<cdot> v" using v by (simp add: a_assoc[symmetric] l_neg int_mult_def)
  also have "... = (int 1 + int n) \<cdot> v" by (unfold int_mult_def minus_minus nat_int_add, simp)
  also have "... = ?l" by (auto simp: x)
  finally show ?thesis by simp
qed

lemma int_mult_add_distrib1:
  assumes v [simp]: "v \<in> carrier G"
  shows "(x+y) \<cdot> v = x \<cdot> v \<oplus> y \<cdot> v"
proof (induct x)
  case (nonneg n)
  then show ?case using v
    by (induct n, auto simp: ac_simps a_assoc[symmetric] int_mult_1_add)
next
  case (neg n)
  show ?case
  proof(induct n)
    case 0 show ?case using v by (auto simp add: int_mult_minus_1 minus_eq)
    case IH: (Suc n)
    have "(- int (Suc (Suc n)) + y) = (- int (Suc n) + y - 1)" by simp
    also have "\<dots> \<cdot> v = \<ominus> v \<oplus> (- int (Suc n) + y) \<cdot> v" unfolding int_mult_minus_1[OF v] by simp
    also have "\<dots> = \<ominus> v \<oplus> (- int (Suc n) \<cdot> v \<oplus> y \<cdot> v)" by (unfold IH, simp)
    also have "\<dots> = (\<ominus> v \<oplus> (- int (Suc n) \<cdot> v)) \<oplus> y \<cdot> v" by (auto simp: a_assoc)
    also have "\<dots> = (- int (Suc (Suc n)) \<cdot> v) \<oplus> y \<cdot> v" by (subst int_mult_minus_1[symmetric], auto)
    finally show ?case.
  qed
qed

lemma int_mult_minus_distrib1:
  assumes "v \<in> carrier G"
  shows "(x - y) \<cdot> v = x \<cdot> v \<ominus> y \<cdot> v"
  using assms by (unfold diff_conv_add_uminus int_mult_add_distrib1, simp add: minus_eq)

lemma int_mult_mult:
  assumes v [simp]: "v \<in> carrier G"
  shows "x \<cdot> (y \<cdot> v) = x * y \<cdot> v"
proof (cases x)
  case x: (nonneg n)
  show ?thesis by (unfold x, induct n, auto simp: field_simps int_mult_add_distrib1)
next
  case x: (neg n)
  show ?thesis
  proof (unfold x, induct n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    have "- int (Suc (Suc n)) \<cdot> (y \<cdot> v) = (- int (Suc n) - 1) \<cdot> (y \<cdot> v)" by simp
    also have "\<dots> = \<ominus> (y \<cdot> v) \<oplus> - int (Suc n) \<cdot> (y \<cdot> v)" by (rule int_mult_minus_1, simp)
    also have "\<dots> = (- y \<cdot> v) \<oplus> - int (Suc n) * y \<cdot> v" unfolding Suc by simp
    also have "\<dots> = - int (Suc (Suc n)) * y \<cdot> v"
      by (subst int_mult_add_distrib1[symmetric], auto simp: left_diff_distrib)
    finally show ?case by (simp add: field_simps)
  qed
qed

lemma int_mult_add_distrib2[simp]:
  assumes "v \<in> carrier G" and "w \<in> carrier G"
  shows "x \<cdot> (v \<oplus> w) = x \<cdot> v \<oplus> x \<cdot> w" using assms by (auto simp: int_mult_def minus_add)

abbreviation int_ring
  where "int_ring \<equiv> \<lparr> carrier = UNIV::int set, monoid.mult = op *, one = 1, zero = 0, add = op + \<rparr>"

abbreviation lattice_module
  where "lattice_module \<equiv>
   \<lparr> carrier = carrier G, monoid.mult = op \<otimes>, one = \<one>, zero = \<zero>, add = op \<oplus>, module.smult = int_mult \<rparr>"

sublocale module: module "int_ring" lattice_module
  rewrites "carrier int_ring = UNIV"
    and "monoid.mult int_ring = op *"
    and "one int_ring = 1"
    and "zero int_ring = 0"
    and "add int_ring = op +"
    and "carrier lattice_module = carrier G"
    and "monoid.mult lattice_module = op \<otimes>"
    and "one lattice_module = \<one>"
    and "zero lattice_module = \<zero>"
    and "add lattice_module = op \<oplus>"
    and "module.smult lattice_module = int_mult"
  by (unfold_locales,
      auto simp: field_simps Units_def int_mult_mult l_neg r_neg int_mult_add_distrib1
      intro!: a_assoc a_comm exI[of _ "\<ominus> _"] bexI[of _ "\<ominus> _"])

end

(*
definition reduced where
  "reduced n vs \<equiv>
   let ws = gram_schmidt n vs in \<forall>i < length ws - 1. \<parallel>ws!i\<parallel>\<^sup>2 \<le> 2 * \<parallel>ws!Suc i\<parallel>\<^sup>2"*)

end