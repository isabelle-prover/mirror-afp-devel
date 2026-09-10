theory Jacobian_Counterexample
  imports
    Complex_Main
    "HOL-Analysis.Derivative"
    "HOL-Analysis.Determinants"
    "HOL-Decision_Procs.Commutative_Ring"
    "HOL-Library.Cardinality"
begin

section \<open>Formal multivariate polynomials\<close>

text \<open>
  We use a small expression datatype for multivariate polynomials.  This makes
  polynomiality syntactic and gives a direct definition of formal partial
  differentiation, independent of analytic differentiability.
\<close>

datatype ('v, 'a) poly_expr =
    PConst 'a
  | PVar 'v
  | PAdd "('v, 'a) poly_expr" "('v, 'a) poly_expr"
  | PMul "('v, 'a) poly_expr" "('v, 'a) poly_expr"
  | PPow "('v, 'a) poly_expr" nat

instantiation poly_expr :: (type, zero) zero
begin

definition "0 = PConst 0"

instance ..

end

fun eval_poly_expr ::
    "('v \<Rightarrow> 'a::semiring_1) \<Rightarrow> ('v, 'a) poly_expr \<Rightarrow> 'a" where
  "eval_poly_expr \<alpha> (PConst c) = c"
| "eval_poly_expr \<alpha> (PVar v) = \<alpha> v"
| "eval_poly_expr \<alpha> (PAdd p q) =
     eval_poly_expr \<alpha> p + eval_poly_expr \<alpha> q"
| "eval_poly_expr \<alpha> (PMul p q) =
     eval_poly_expr \<alpha> p * eval_poly_expr \<alpha> q"
| "eval_poly_expr \<alpha> (PPow p n) = eval_poly_expr \<alpha> p ^ n"

fun partial_poly_expr ::
    "'v \<Rightarrow> ('v, 'a::semiring_1) poly_expr \<Rightarrow> ('v, 'a) poly_expr" where
  "partial_poly_expr v (PConst c) = PConst 0"
| "partial_poly_expr v (PVar w) = PConst (if v = w then 1 else 0)"
| "partial_poly_expr v (PAdd p q) =
     PAdd (partial_poly_expr v p) (partial_poly_expr v q)"
| "partial_poly_expr v (PMul p q) =
     PAdd (PMul (partial_poly_expr v p) q)
       (PMul p (partial_poly_expr v q))"
| "partial_poly_expr v (PPow p n) =
     PMul (PMul (PConst (of_nat n)) (PPow p (n - 1)))
       (partial_poly_expr v p)"

lemma eval_partial_poly_expr_has_field_derivative:
  fixes \<alpha> :: "'v \<Rightarrow> complex"
  shows "((\<lambda>u. eval_poly_expr (\<alpha>(v := u)) p) has_field_derivative
    eval_poly_expr (\<alpha>(v := u)) (partial_poly_expr v p)) (at u)"
proof (induction p)
  case (PConst c)
  then show ?case
    by (auto intro!: derivative_eq_intros)
next
  case (PVar w)
  then show ?case
    by (cases "v = w") (auto intro!: derivative_eq_intros)
next
  case (PAdd p q)
  then show ?case
    by (auto intro!: derivative_eq_intros)
next
  case (PMul p q)
  then show ?case
    by (auto intro!: derivative_eq_intros)
next
  case (PPow p n)
  then show ?case
    by (auto intro!: derivative_eq_intros)
qed

definition eval_poly_map ::
    "(('n, 'a::semiring_1) poly_expr)^'n \<Rightarrow> 'a^'n \<Rightarrow> 'a^'n" where
  "eval_poly_map P x = (\<chi> i. eval_poly_expr (\<lambda>j. x $ j) (P $ i))"

definition jacobian_matrix ::
    "(('n, 'a::comm_ring_1) poly_expr)^'n \<Rightarrow> 'a^'n \<Rightarrow> 'a^'n^'n" where
  "jacobian_matrix P x =
     (\<chi> i j. eval_poly_expr (\<lambda>k. x $ k) (partial_poly_expr j (P $ i)))"

lemma jacobian_matrix_entry_has_field_derivative:
  fixes P :: "(('n, complex) poly_expr)^'n"
  shows "((\<lambda>u. eval_poly_expr ((\<lambda>k. x $ k)(j := u)) (P $ i))
    has_field_derivative jacobian_matrix P x $ i $ j) (at (x $ j))"
  unfolding jacobian_matrix_def
  using eval_partial_poly_expr_has_field_derivative[
    where \<alpha> = "\<lambda>k. x $ k" and v = j and p = "P $ i" and u = "x $ j"]
  by simp

definition polynomially_invertible ::
    "(('n, 'a::semiring_1) poly_expr)^'n \<Rightarrow> bool" where
  "polynomially_invertible P \<longleftrightarrow>
     (\<exists>Q.
       (\<forall>x. eval_poly_map Q (eval_poly_map P x) = x) \<and>
       (\<forall>x. eval_poly_map P (eval_poly_map Q x) = x))"

lemma polynomially_invertible_imp_inj:
  assumes "polynomially_invertible P"
  shows "inj (eval_poly_map P)"
proof (rule injI)
  fix x y
  assume same: "eval_poly_map P x = eval_poly_map P y"
  from assms obtain Q where left:
      "\<And>z. eval_poly_map Q (eval_poly_map P z) = z"
    unfolding polynomially_invertible_def by blast
  have "x = eval_poly_map Q (eval_poly_map P x)"
    by (simp add: left)
  also have "\<dots> = eval_poly_map Q (eval_poly_map P y)"
    by (simp add: same)
  also have "\<dots> = y"
    by (rule left)
  finally show "x = y" .
qed

definition keller_map ::
    "(('n, 'a::comm_ring_1) poly_expr)^'n \<Rightarrow> bool" where
  "keller_map P \<longleftrightarrow>
     (\<exists>d. d \<noteq> 0 \<and> (\<forall>x. det (jacobian_matrix P x) = d))"

definition normalized_keller_map ::
    "(('n, 'a::comm_ring_1) poly_expr)^'n \<Rightarrow> bool" where
  "normalized_keller_map P \<longleftrightarrow>
     (\<forall>x. det (jacobian_matrix P x) = 1)"

definition strong_keller_counterexample ::
    "(('n, 'a::comm_ring_1) poly_expr)^'n \<Rightarrow> bool" where
  "strong_keller_counterexample P \<longleftrightarrow>
     keller_map P \<and> \<not> inj (eval_poly_map P)"

definition keller_counterexample ::
    "(('n, 'a::comm_ring_1) poly_expr)^'n \<Rightarrow> bool" where
  "keller_counterexample P \<longleftrightarrow>
     keller_map P \<and> \<not> polynomially_invertible P"

definition strong_normalized_keller_counterexample ::
    "(('n, 'a::comm_ring_1) poly_expr)^'n \<Rightarrow> bool" where
  "strong_normalized_keller_counterexample P \<longleftrightarrow>
     normalized_keller_map P \<and> \<not> inj (eval_poly_map P)"

definition normalized_keller_counterexample ::
    "(('n, 'a::comm_ring_1) poly_expr)^'n \<Rightarrow> bool" where
  "normalized_keller_counterexample P \<longleftrightarrow>
     normalized_keller_map P \<and> \<not> polynomially_invertible P"

lemma strong_keller_counterexample_imp_keller_counterexample:
  "strong_keller_counterexample P \<Longrightarrow> keller_counterexample P"
  unfolding strong_keller_counterexample_def keller_counterexample_def
  using polynomially_invertible_imp_inj by blast

lemma strong_normalized_keller_counterexample_imp_counterexample:
  "strong_normalized_keller_counterexample P \<Longrightarrow>
    normalized_keller_counterexample P"
  unfolding strong_normalized_keller_counterexample_def
    normalized_keller_counterexample_def
  using polynomially_invertible_imp_inj by blast

section \<open>The announced polynomial map\<close>

text \<open>
  Alpöge announced the following three-coordinate polynomial map on July 20,
  2026 \<^cite>\<open>Alpoge2026\<close>.  The announcement credits Akhil Mathew with
  prompting the question and the AI system Claude Fable with work leading to
  the example; stable independent verification repositories appeared the same
  day \<^cite>\<open>Cureton2026 and Harrison2026\<close>.  The definitions below encode the
  map syntactically, so the subsequent Jacobian calculation is a theorem about
  formal polynomial differentiation rather than an imported computer-algebra
  result.
\<close>

definition x_poly :: "(3, 'a::comm_ring_1) poly_expr" where
  "x_poly = PVar 1"

definition y_poly :: "(3, 'a::comm_ring_1) poly_expr" where
  "y_poly = PVar 2"

definition z_poly :: "(3, 'a::comm_ring_1) poly_expr" where
  "z_poly = PVar 3"

definition one_plus_xy_poly :: "(3, 'a::comm_ring_1) poly_expr" where
  "one_plus_xy_poly = PAdd (PConst 1) (PMul x_poly y_poly)"

definition four_plus_three_xy_poly :: "(3, 'a::comm_ring_1) poly_expr" where
  "four_plus_three_xy_poly =
     PAdd (PConst 4) (PMul (PConst 3) (PMul x_poly y_poly))"

definition component_a_poly :: "(3, 'a::comm_ring_1) poly_expr" where
  "component_a_poly =
     PAdd (PMul (PPow one_plus_xy_poly 3) z_poly)
       (PMul (PMul (PPow y_poly 2) one_plus_xy_poly)
         four_plus_three_xy_poly)"

definition component_b_poly :: "(3, 'a::comm_ring_1) poly_expr" where
  "component_b_poly =
     PAdd y_poly
       (PAdd (PMul (PMul (PConst 3) x_poly)
          (PMul (PPow one_plus_xy_poly 2) z_poly))
        (PMul (PMul (PMul (PConst 3) x_poly) (PPow y_poly 2))
          four_plus_three_xy_poly))"

definition component_c_poly :: "(3, 'a::comm_ring_1) poly_expr" where
  "component_c_poly =
     PAdd (PMul (PConst 2) x_poly)
       (PAdd (PMul (PConst (-3)) (PMul (PPow x_poly 2) y_poly))
         (PMul (PConst (-1)) (PMul (PPow x_poly 3) z_poly)))"

definition alpoge_map :: "((3, 'a::comm_ring_1) poly_expr)^3" where
  "alpoge_map =
     vector [component_a_poly, component_b_poly, component_c_poly]"

lemma eval_alpoge_map:
  "eval_poly_map alpoge_map (vector [x, y, z]) =
   vector [
     (1 + x * y)^3 * z + y^2 * (1 + x * y) * (4 + 3 * x * y),
     y + 3 * x * (1 + x * y)^2 * z + 3 * x * y^2 * (4 + 3 * x * y),
     2 * x - 3 * x^2 * y - x^3 * z]"
  unfolding eval_poly_map_def alpoge_map_def component_a_poly_def
    component_b_poly_def component_c_poly_def one_plus_xy_poly_def
    four_plus_three_xy_poly_def x_poly_def y_poly_def z_poly_def
  by (simp add: vec_eq_iff vector_def forall_3 algebra_simps)

corollary alpoge_jacobian_entry_has_field_derivative:
  fixes x :: "complex^3"
  shows "((\<lambda>u.
      eval_poly_map (alpoge_map :: ((3, complex) poly_expr)^3)
        (\<chi> k. if k = j then u else x $ k) $ i)
    has_field_derivative
      jacobian_matrix (alpoge_map :: ((3, complex) poly_expr)^3) x $ i $ j)
    (at (x $ j))"
  using jacobian_matrix_entry_has_field_derivative[
    where P = "alpoge_map :: ((3, complex) poly_expr)^3"
      and x = x and i = i and j = j]
  by (simp add: eval_poly_map_def fun_upd_def)

lemma jacobian_alpoge_map:
  "jacobian_matrix alpoge_map (vector [x, y, z]) =
   vector [
     vector [
       3 * y * (1 + x * y)^2 * z +
         y^3 * (4 + 3 * x * y) + 3 * y^3 * (1 + x * y),
       3 * x * (1 + x * y)^2 * z +
         2 * y * (1 + x * y) * (4 + 3 * x * y) +
         x * y^2 * (4 + 3 * x * y) + 3 * x * y^2 * (1 + x * y),
       (1 + x * y)^3],
     vector [
       3 * (1 + x * y)^2 * z + 6 * x * y * (1 + x * y) * z +
         3 * y^2 * (4 + 3 * x * y) + 9 * x * y^3,
       1 + 6 * x^2 * (1 + x * y) * z +
         6 * x * y * (4 + 3 * x * y) + 9 * x^2 * y^2,
       3 * x * (1 + x * y)^2],
     vector [
       2 - 6 * x * y - 3 * x^2 * z,
       -3 * x^2,
       -(x^3)]]"
  unfolding jacobian_matrix_def alpoge_map_def component_a_poly_def
    component_b_poly_def component_c_poly_def one_plus_xy_poly_def
    four_plus_three_xy_poly_def x_poly_def y_poly_def z_poly_def
  apply (simp add: vec_eq_iff vector_def forall_3 algebra_simps)
  apply (intro conjI)
  apply ring+
  done

lemma alpoge_jacobian_det_coordinates:
  "det (jacobian_matrix alpoge_map (vector [x, y, z])) = -2"
  apply (subst jacobian_alpoge_map)
  apply (simp add: det_3 vector_def)
  apply ring
  done

theorem alpoge_jacobian_det:
  "det (jacobian_matrix alpoge_map p) = -2"
proof -
  have p: "p = vector [p $ 1, p $ 2, p $ 3]"
    by (simp add: vec_eq_iff vector_def forall_3)
  show ?thesis
    apply (subst p)
    apply (rule alpoge_jacobian_det_coordinates)
    done
qed

section \<open>An explicit three-point fibre\<close>

definition collision_point_0 :: "'a::field_char_0^3" where
  "collision_point_0 = vector [0, 0, -1 / 4]"

definition collision_point_pos :: "'a::field_char_0^3" where
  "collision_point_pos = vector [1, -3 / 2, 13 / 2]"

definition collision_point_neg :: "'a::field_char_0^3" where
  "collision_point_neg = vector [-1, 3 / 2, 13 / 2]"

definition collision_value :: "'a::field_char_0^3" where
  "collision_value = vector [-1 / 4, 0, 0]"

lemma collision_points_distinct:
  "distinct [collision_point_0, collision_point_pos, collision_point_neg]"
  unfolding collision_point_0_def collision_point_pos_def collision_point_neg_def
  by (simp add: vec_eq_iff vector_def forall_3)

lemma alpoge_collision:
  "eval_poly_map alpoge_map collision_point_0 = collision_value"
  "eval_poly_map alpoge_map collision_point_pos = collision_value"
  "eval_poly_map alpoge_map collision_point_neg = collision_value"
  unfolding collision_point_0_def collision_point_pos_def collision_point_neg_def
    collision_value_def eval_alpoge_map
  by (simp_all add: vec_eq_iff vector_def forall_3 field_simps algebra_simps)

lemma alpoge_map_not_injective:
  "\<not> inj
    (eval_poly_map (alpoge_map :: ((3, 'a::field_char_0) poly_expr)^3))"
proof
  assume inj: "inj
    (eval_poly_map (alpoge_map :: ((3, 'a) poly_expr)^3))"
  have same:
    "eval_poly_map (alpoge_map :: ((3, 'a) poly_expr)^3)
       (collision_point_0 :: 'a^3) =
     eval_poly_map alpoge_map (collision_point_pos :: 'a^3)"
    by (simp only: alpoge_collision)
  have "(collision_point_0 :: 'a^3) = collision_point_pos"
    using inj same by (rule injD)
  moreover have "(collision_point_0 :: 'a^3) \<noteq> collision_point_pos"
    unfolding collision_point_0_def collision_point_pos_def
    by (simp add: vec_eq_iff vector_def forall_3)
  ultimately show False
    by contradiction
qed

theorem alpoge_map_is_strong_keller_counterexample:
  "strong_keller_counterexample
    (alpoge_map :: ((3, 'a::field_char_0) poly_expr)^3)"
  unfolding strong_keller_counterexample_def keller_map_def
  using alpoge_jacobian_det alpoge_map_not_injective
  by (intro conjI exI[of _ "-2"]) auto

corollary alpoge_map_is_keller_counterexample:
  "keller_counterexample
    (alpoge_map :: ((3, 'a::field_char_0) poly_expr)^3)"
  using alpoge_map_is_strong_keller_counterexample
  by (rule strong_keller_counterexample_imp_keller_counterexample)

corollary alpoge_map_not_polynomially_invertible:
  "\<not> polynomially_invertible
    (alpoge_map :: ((3, 'a::field_char_0) poly_expr)^3)"
  using alpoge_map_is_keller_counterexample
  unfolding keller_counterexample_def by blast

section \<open>A determinant-one normalization\<close>

definition normalized_alpoge_map ::
    "((3, 'a::field_char_0) poly_expr)^3" where
  "normalized_alpoge_map =
     vector [
       PMul (PConst (-1 / 2)) component_a_poly,
       component_b_poly,
       component_c_poly]"

lemma eval_normalized_alpoge_map:
  "eval_poly_map normalized_alpoge_map (vector [x, y, z]) =
   vector [
     (-1 / 2) *
       ((1 + x * y)^3 * z + y^2 * (1 + x * y) * (4 + 3 * x * y)),
     y + 3 * x * (1 + x * y)^2 * z + 3 * x * y^2 * (4 + 3 * x * y),
     2 * x - 3 * x^2 * y - x^3 * z]"
  unfolding normalized_alpoge_map_def eval_poly_map_def component_a_poly_def
    component_b_poly_def component_c_poly_def one_plus_xy_poly_def
    four_plus_three_xy_poly_def x_poly_def y_poly_def z_poly_def
  by (simp add: vec_eq_iff vector_def forall_3 algebra_simps)

lemma jacobian_normalized_alpoge_map:
  "jacobian_matrix normalized_alpoge_map p =
   (\<chi> i j.
      if i = 1 then
        (-1 / 2) * (jacobian_matrix alpoge_map p $ i $ j)
      else jacobian_matrix alpoge_map p $ i $ j)"
  unfolding normalized_alpoge_map_def alpoge_map_def jacobian_matrix_def
  by (simp add: vec_eq_iff vector_def forall_3)

theorem normalized_alpoge_jacobian_det:
  "det (jacobian_matrix normalized_alpoge_map p) = 1"
proof -
  let ?J = "jacobian_matrix alpoge_map p"
  have scaled:
    "jacobian_matrix normalized_alpoge_map p =
     (\<chi> i. if i = 1 then (-1 / 2) *s row i ?J else row i ?J)"
    unfolding jacobian_normalized_alpoge_map row_def
    by (simp add: vec_eq_iff)
  have det_scaled:
    "det (\<chi> i. if i = 1 then (-1 / 2) *s row i ?J else row i ?J) =
     (-1 / 2) * det (\<chi> i. if i = 1 then row i ?J else row i ?J)"
    by (rule det_row_mul)
  have rows: "(\<chi> i. row i ?J) = ?J"
    unfolding row_def
    by (simp add: vec_eq_iff)
  show ?thesis
    apply (subst scaled)
    apply (subst det_scaled)
    using alpoge_jacobian_det[of p]
    apply (simp add: rows field_simps)
    done
qed

lemma normalized_alpoge_collision:
  "eval_poly_map normalized_alpoge_map collision_point_0 =
     vector [1 / 8, 0, 0]"
  "eval_poly_map normalized_alpoge_map collision_point_pos =
     vector [1 / 8, 0, 0]"
  "eval_poly_map normalized_alpoge_map collision_point_neg =
     vector [1 / 8, 0, 0]"
  unfolding collision_point_0_def collision_point_pos_def collision_point_neg_def
    eval_normalized_alpoge_map
  by (simp_all add: vec_eq_iff vector_def forall_3 field_simps algebra_simps)

lemma normalized_alpoge_map_not_injective:
  "\<not> inj
    (eval_poly_map
      (normalized_alpoge_map :: ((3, 'a::field_char_0) poly_expr)^3))"
proof
  assume inj: "inj
    (eval_poly_map (normalized_alpoge_map :: ((3, 'a) poly_expr)^3))"
  have same:
    "eval_poly_map (normalized_alpoge_map :: ((3, 'a) poly_expr)^3)
       (collision_point_0 :: 'a^3) =
     eval_poly_map normalized_alpoge_map (collision_point_pos :: 'a^3)"
    by (simp only: normalized_alpoge_collision)
  have "(collision_point_0 :: 'a^3) = collision_point_pos"
    using inj same by (rule injD)
  moreover have "(collision_point_0 :: 'a^3) \<noteq> collision_point_pos"
    unfolding collision_point_0_def collision_point_pos_def
    by (simp add: vec_eq_iff vector_def forall_3)
  ultimately show False
    by contradiction
qed

theorem normalized_alpoge_map_is_strong_counterexample:
  "strong_normalized_keller_counterexample
    (normalized_alpoge_map :: ((3, 'a::field_char_0) poly_expr)^3)"
  unfolding strong_normalized_keller_counterexample_def normalized_keller_map_def
  using normalized_alpoge_jacobian_det normalized_alpoge_map_not_injective
  by blast

theorem normalized_alpoge_map_is_counterexample:
  "normalized_keller_counterexample
    (normalized_alpoge_map :: ((3, 'a::field_char_0) poly_expr)^3)"
  using normalized_alpoge_map_is_strong_counterexample
  by (rule strong_normalized_keller_counterexample_imp_counterexample)

corollary normalized_alpoge_map_not_polynomially_invertible:
  "\<not> polynomially_invertible
    (normalized_alpoge_map :: ((3, 'a::field_char_0) poly_expr)^3)"
  using normalized_alpoge_map_is_counterexample
  unfolding normalized_keller_counterexample_def by blast

text \<open>
  This is the determinant-one form of the counterexample.  Since every
  coordinate is represented by a polynomial expression, the theorem directly
  refutes the normalized dimension-three Jacobian conjecture over any field of
  characteristic zero.
\<close>

corollary complex_jacobian_conjecture_counterexample:
  "normalized_keller_counterexample
    (normalized_alpoge_map :: ((3, complex) poly_expr)^3)"
  by (rule normalized_alpoge_map_is_counterexample)

section \<open>Identity padding in higher dimensions\<close>

lemma prod_UNIV_sum:
  fixes f :: "('n::finite + 'm::finite) \<Rightarrow> 'a::comm_monoid_mult"
  shows "(\<Prod>x\<in>UNIV. f x) =
    (\<Prod>i\<in>UNIV. f (Inl i)) * (\<Prod>j\<in>UNIV. f (Inr j))"
proof -
  have disj: "range (Inl :: 'n \<Rightarrow> 'n + 'm) \<inter> range Inr = {}"
    by auto
  have split:
    "prod f (range (Inl :: 'n \<Rightarrow> 'n + 'm) \<union> range Inr) =
     prod f (range Inl) * prod f (range Inr)"
    using disj by (simp add: prod.union_disjoint)
  have left:
    "prod f (range (Inl :: 'n \<Rightarrow> 'n + 'm)) =
     (\<Prod>i\<in>UNIV. f (Inl i))"
    by (simp add: prod.reindex)
  have right:
    "prod f (range (Inr :: 'm \<Rightarrow> 'n + 'm)) =
     (\<Prod>j\<in>UNIV. f (Inr j))"
    by (simp add: prod.reindex)
  show ?thesis
    using split left right by (simp add: UNIV_sum)
qed

definition block_identity_matrix ::
    "'a::semiring_1^'n^'n \<Rightarrow> 'a^('n + 'm::finite)^('n + 'm)" where
  "block_identity_matrix A =
    (\<chi> i j.
      case i of
        Inl r \<Rightarrow> (case j of Inl c \<Rightarrow> A $ r $ c | Inr _ \<Rightarrow> 0)
      | Inr r \<Rightarrow> (case j of Inl _ \<Rightarrow> 0 | Inr c \<Rightarrow> if r = c then 1 else 0))"

lemma det_block_identity_matrix:
  fixes A :: "'a::comm_ring_1^'n::finite^'n"
  shows "det (block_identity_matrix A :: 'a^('n + 'm::finite)^('n + 'm)) = det A"
proof -
  let ?U = "UNIV :: 'n set"
  let ?B = "range (Inl :: 'n \<Rightarrow> 'n + 'm)"
  let ?PU = "{p. p permutes ?U}"
  let ?PB = "{p. p permutes ?B}"
  let ?PAll = "{p. p permutes (UNIV :: ('n + 'm) set)}"
  let ?lift = "\<lambda>p x.
    if x \<in> ?B then Inl (p (inv_into ?U Inl x)) else x"
  let ?term = "\<lambda>p. of_int (sign p) *
    (\<Prod>i\<in>UNIV. block_identity_matrix A $ i $ p i)"
  have finite_all: "finite (UNIV :: ('n + 'm) set)"
    by simp
  have PB_sub: "?PB \<subseteq> ?PAll"
    by (auto intro: permutes_subset)
  have zero_out: "\<forall>p\<in>?PAll - ?PB. ?term p = 0"
  proof (intro ballI)
    fix p
    assume p: "p \<in> ?PAll - ?PB"
    have moves_right: "\<exists>j. p (Inr j) \<noteq> Inr j"
    proof (rule ccontr)
      assume "\<nexists>j. p (Inr j) \<noteq> Inr j"
      then have fixed_outside: "\<And>x. x \<notin> ?B \<Longrightarrow> p x = x"
        by (metis range_eqI sum.exhaust_sel)
      from p have bij: "\<And>y. \<exists>!x. p x = y"
        by (auto simp: permutes_def)
      have "p permutes ?B"
        unfolding permutes_def using fixed_outside bij by blast
      with p show False
        by blast
    qed
    then obtain j where moved: "p (Inr j) \<noteq> Inr j"
      by blast
    have entry_zero:
      "block_identity_matrix A $ Inr j $ p (Inr j) = 0"
      using moved by (cases "p (Inr j)") (auto simp: block_identity_matrix_def)
    have product_zero:
      "(\<Prod>i\<in>UNIV. block_identity_matrix A $ i $ p i) = 0"
      by (rule prod_zero) (use entry_zero in auto)
    show "?term p = 0"
      by (simp add: product_zero)
  qed
  have sum_restrict: "sum ?term ?PB = sum ?term ?PAll"
    by (rule sum.mono_neutral_cong_left[
      OF finite_permutations[OF finite_all] PB_sub zero_out]) auto
  have det_restrict:
    "det (block_identity_matrix A :: 'a^('n + 'm)^('n + 'm)) = sum ?term ?PB"
    unfolding det_def using sum_restrict by (rule sym)
  have bij_inl: "bij_betw (Inl :: 'n \<Rightarrow> 'n + 'm) ?U ?B"
    by (rule bij_betw_imageI) auto
  have bij_lift: "bij_betw ?lift ?PU ?PB"
    by (rule bij_betw_permutations[OF bij_inl])
  have lift_eq_map:
    "?lift p = map_permutation ?U (Inl :: 'n \<Rightarrow> 'n + 'm) p" for p
    unfolding map_permutation_def
    by (auto simp: fun_eq_iff restrict_id_def o_def)
  have sign_lift: "sign (?lift p) = sign p" if "p \<in> ?PU" for p
    using sign_map_permutation[of "Inl :: 'n \<Rightarrow> 'n + 'm" ?U p]
      that by (simp add: lift_eq_map)
  have product_lift:
    "(\<Prod>i\<in>UNIV. block_identity_matrix A $ i $ ?lift p i) =
     (\<Prod>i\<in>UNIV. A $ i $ p i)"
    if "p \<in> ?PU" for p
  proof -
    note split = prod_UNIV_sum[
      of "\<lambda>i. block_identity_matrix A $ i $ ?lift p i"]
    have in_left: "Inl i \<in> ?B" for i
      by auto
    have not_left: "Inr j \<notin> ?B" for j
      by auto
    have inv_left: "inv_into ?U Inl (Inl i) = i" for i
      by (rule inv_into_f_f) auto
    show ?thesis
      using split that
      by (simp add: block_identity_matrix_def in_left not_left inv_left)
  qed
  have term_lift:
    "?term (?lift p) =
     of_int (sign p) * (\<Prod>i\<in>UNIV. A $ i $ p i)"
    if "p \<in> ?PU" for p
    using sign_lift[OF that] product_lift[OF that] by simp
  have reindex:
    "sum (\<lambda>p. ?term (?lift p)) ?PU = sum ?term ?PB"
    by (rule sum.reindex_bij_betw[OF bij_lift])
  have "sum ?term ?PB = sum (\<lambda>p. ?term (?lift p)) ?PU"
    using reindex by (rule sym)
  also have "\<dots> =
      sum (\<lambda>p. of_int (sign p) * (\<Prod>i\<in>UNIV. A $ i $ p i)) ?PU"
    by (rule sum.cong) (auto intro: term_lift)
  also have "\<dots> = det A"
    by (simp only: det_def)
  finally show ?thesis
    using det_restrict by simp
qed

fun rename_poly_expr ::
    "('v \<Rightarrow> 'w) \<Rightarrow> ('v, 'a) poly_expr \<Rightarrow> ('w, 'a) poly_expr" where
  "rename_poly_expr f (PConst c) = PConst c"
| "rename_poly_expr f (PVar v) = PVar (f v)"
| "rename_poly_expr f (PAdd p q) =
     PAdd (rename_poly_expr f p) (rename_poly_expr f q)"
| "rename_poly_expr f (PMul p q) =
     PMul (rename_poly_expr f p) (rename_poly_expr f q)"
| "rename_poly_expr f (PPow p n) = PPow (rename_poly_expr f p) n"

lemma eval_rename_poly_expr:
  "eval_poly_expr \<alpha> (rename_poly_expr f p) =
   eval_poly_expr (\<alpha> \<circ> f) p"
  by (induction p) simp_all

lemma partial_rename_poly_expr_Inl:
  "partial_poly_expr (Inl v) (rename_poly_expr Inl p) =
   rename_poly_expr Inl (partial_poly_expr v p)"
  by (induction p) simp_all

lemma eval_partial_rename_poly_expr_Inr:
  "eval_poly_expr \<alpha>
    (partial_poly_expr (Inr w) (rename_poly_expr Inl p)) = 0"
  by (induction p) simp_all

definition join_vector ::
    "'a^'n \<Rightarrow> 'a^'m \<Rightarrow> 'a^('n + 'm)" where
  "join_vector x y =
    (\<chi> i. case i of Inl j \<Rightarrow> x $ j | Inr j \<Rightarrow> y $ j)"

lemma join_vector_Inl [simp]: "join_vector x y $ Inl i = x $ i"
  by (simp add: join_vector_def)

lemma join_vector_Inr [simp]: "join_vector x y $ Inr j = y $ j"
  by (simp add: join_vector_def)

lemma join_vector_comp_Inl [simp]:
  "($) (join_vector x y) \<circ> Inl = ($) x"
  by (rule ext) simp

lemma join_vector_comp_Inr [simp]:
  "($) (join_vector x y) \<circ> Inr = ($) y"
  by (rule ext) simp

lemma join_vector_eq_iff [simp]:
  "join_vector x y = join_vector x' y' \<longleftrightarrow> x = x' \<and> y = y'"
  by (simp add: join_vector_def vec_eq_iff split_sum_all)

definition pad_poly_map ::
    "(('n, 'a::semiring_1) poly_expr)^'n \<Rightarrow>
     (('n + 'm::finite, 'a) poly_expr)^('n + 'm)" where
  "pad_poly_map P =
    (\<chi> i.
      case i of
        Inl j \<Rightarrow> rename_poly_expr Inl (P $ j)
      | Inr j \<Rightarrow> PVar (Inr j))"

lemma eval_pad_poly_map:
  "eval_poly_map (pad_poly_map P) (join_vector x y) =
   join_vector (eval_poly_map P x) y"
  unfolding eval_poly_map_def pad_poly_map_def
  by (simp add: vec_eq_iff split_sum_all eval_rename_poly_expr)

lemma jacobian_pad_poly_map:
  "jacobian_matrix (pad_poly_map P) (join_vector x y) =
   block_identity_matrix (jacobian_matrix P x)"
  unfolding jacobian_matrix_def pad_poly_map_def
    block_identity_matrix_def
  by (simp add: vec_eq_iff split_sum_all eval_rename_poly_expr
      partial_rename_poly_expr_Inl eval_partial_rename_poly_expr_Inr)

corollary jacobian_det_pad_poly_map:
  "det (jacobian_matrix (pad_poly_map P) (join_vector x y)) =
   det (jacobian_matrix P x)"
  by (simp add: jacobian_pad_poly_map det_block_identity_matrix)

definition left_subvector :: "'a^('n::finite + 'm::finite) \<Rightarrow> 'a^'n" where
  "left_subvector z = (\<chi> i. z $ Inl i)"

definition right_subvector :: "'a^('n::finite + 'm::finite) \<Rightarrow> 'a^'m" where
  "right_subvector z = (\<chi> j. z $ Inr j)"

lemma join_vector_subvectors [simp]:
  "join_vector (left_subvector z) (right_subvector z) = z"
  by (simp add: join_vector_def left_subvector_def right_subvector_def
      vec_eq_iff split_sum_all)

lemma pad_poly_map_not_injective:
  fixes P :: "(('n, 'a::semiring_1) poly_expr)^'n"
  assumes "\<not> inj (eval_poly_map P)"
  shows "\<not> inj
    (eval_poly_map
      (pad_poly_map P ::
        (('n + 'm::finite, 'a) poly_expr)^('n + 'm)))"
proof -
  from assms obtain x x' where
      same: "eval_poly_map P x = eval_poly_map P x'" and neq: "x \<noteq> x'"
    by (auto simp: inj_def)
  let ?z = "0 :: 'a^'m"
  have same_pad:
    "eval_poly_map (pad_poly_map P) (join_vector x ?z) =
     eval_poly_map (pad_poly_map P) (join_vector x' ?z)"
    by (simp add: eval_pad_poly_map same)
  show ?thesis
  proof
    assume pad_inj: "inj
      (eval_poly_map
        (pad_poly_map P ::
          (('n + 'm, 'a) poly_expr)^('n + 'm)))"
    have "join_vector x ?z = join_vector x' ?z"
      using pad_inj same_pad by (rule injD)
    then have "x = x'"
      by simp
    with neq show False
      by contradiction
  qed
qed

lemma strong_normalized_keller_counterexample_pad_poly_map:
  fixes P :: "(('n, 'a::comm_ring_1) poly_expr)^'n"
  assumes "strong_normalized_keller_counterexample P"
  shows "strong_normalized_keller_counterexample
    (pad_poly_map P ::
      (('n + 'm::finite, 'a) poly_expr)^('n + 'm))"
proof -
  from assms have base_det:
      "\<And>x. det (jacobian_matrix P x) = 1"
    unfolding strong_normalized_keller_counterexample_def
      normalized_keller_map_def by blast
  have padded_det:
      "\<And>z. det (jacobian_matrix
        (pad_poly_map P ::
          (('n + 'm, 'a) poly_expr)^('n + 'm)) z) = 1"
  proof -
    fix z :: "'a^('n + 'm)"
    have "det (jacobian_matrix (pad_poly_map P) z) =
        det (jacobian_matrix P (left_subvector z))"
      using jacobian_det_pad_poly_map[
        of P "left_subvector z" "right_subvector z"]
      by simp
    also have "\<dots> = 1"
      by (rule base_det)
    finally show "det (jacobian_matrix
      (pad_poly_map P ::
        (('n + 'm, 'a) poly_expr)^('n + 'm)) z) = 1" .
  qed
  have padded_not_inj:
    "\<not> inj (eval_poly_map
      (pad_poly_map P ::
        (('n + 'm, 'a) poly_expr)^('n + 'm)))"
    using assms
    unfolding strong_normalized_keller_counterexample_def
    by (intro pad_poly_map_not_injective) blast
  show ?thesis
    unfolding strong_normalized_keller_counterexample_def
      normalized_keller_map_def
    using padded_det padded_not_inj by blast
qed

theorem normalized_alpoge_padding_is_strong_counterexample:
  "strong_normalized_keller_counterexample
    (pad_poly_map
      (normalized_alpoge_map :: ((3, 'a::field_char_0) poly_expr)^3) ::
      ((3 + 'm::finite, 'a) poly_expr)^(3 + 'm))"
  using normalized_alpoge_map_is_strong_counterexample
  by (rule strong_normalized_keller_counterexample_pad_poly_map)

theorem normalized_alpoge_padding_is_counterexample:
  "normalized_keller_counterexample
    (pad_poly_map
      (normalized_alpoge_map :: ((3, 'a::field_char_0) poly_expr)^3) ::
      ((3 + 'm::finite, 'a) poly_expr)^(3 + 'm))"
  using normalized_alpoge_padding_is_strong_counterexample
  by (rule strong_normalized_keller_counterexample_imp_counterexample)

corollary complex_jacobian_conjecture_counterexample_in_higher_dimension:
  "normalized_keller_counterexample
    (pad_poly_map
      (normalized_alpoge_map :: ((3, complex) poly_expr)^3) ::
      ((3 + 'm::finite, complex) poly_expr)^(3 + 'm))"
  by (rule normalized_alpoge_padding_is_counterexample)

lemma padded_dimension_card:
  "CARD(3 + 'm::finite) = 3 + CARD('m)"
  by (simp add: card_UNIV_sum)

lemma padded_dimension_greater_than_three:
  "3 < CARD(3 + 'm::finite)"
  using zero_less_card_finite[where 'a = 'm]
  by (simp add: padded_dimension_card)

text \<open>
  The extra finite type \<open>'m\<close> is nonempty, so the padded coordinate type has
  dimension strictly greater than three.  Conversely, every concrete finite
  dimension above three can be represented by choosing an extra finite type of
  the required cardinality.  Thus the dimension-three counterexample yields
  counterexamples in all dimensions \<open>n > 3\<close>.  Together with the original
  theorem this covers every \<open>n \<ge> 3\<close>.  Nothing in this development addresses
  the two-dimensional conjecture.
\<close>

end
