(*  Title:       Computational p-Adics: Prime-Indexed Equivalence and Depth of Formal Laurent Series
    Author:      Jeremy Sylvestre <jeremy.sylvestre at ualberta.ca>, 2025
    Maintainer:  Jeremy Sylvestre <jeremy.sylvestre at ualberta.ca>
*)

theory FLS_Prime_Equiv_Depth

imports
  Parametric_Equiv_Depth
  "HOL.Equiv_Relations"
  "HOL-Computational_Algebra.Formal_Laurent_Series"

begin

unbundle fps_syntax

section \<open>
  Equivalence of sequences of formal Laurent series relative to divisibility of partial sums by a
  fixed prime
\<close>

subsection \<open>Preliminaries\<close>

subsubsection \<open>Lift/transfer of equivalence relations.\<close>

lemma relfp_transfer:
  "reflp r \<Longrightarrow> reflp (\<lambda>x y. r (f x) (f y))"
  unfolding reflp_def by fast

lemma symp_transfer:
  "symp r \<Longrightarrow> symp (\<lambda>x y. r (f x) (f y))"
  unfolding symp_def by fast

lemma transp_transfer:
  "transp r \<Longrightarrow> transp (\<lambda>x y. r (f x) (f y))"
  unfolding transp_def by fast

lemma equivp_transfer:
  "equivp r \<Longrightarrow> equivp (\<lambda>x y. r (f x) (f y))"
  using relfp_transfer symp_transfer transp_transfer
        equivp_reflp_symp_transp[of r] equivp_reflp_symp_transp[of "\<lambda>x y. r (f x) (f y)"]
  by    fast

subsubsection \<open>An additional fact about products/sums\<close>

lemma (in comm_monoid_set) atLeastAtMost_int_shift_bounds:
  "F g {m..n} = F (g \<circ> plus m \<circ> int) {..nat (n - m)}"
  if  "m \<le> n"
  for m n :: int
proof (rule reindex_bij_witness)
  define i :: "nat \<Rightarrow> int" and j :: "int \<Rightarrow> nat"
    where "i \<equiv> plus m \<circ> int"
    and   "j \<equiv> (\<lambda>x. nat (x - m))"
  fix a b from i_def j_def that
    show  "a \<in> {m..n} \<Longrightarrow> i (j a) = a"
    and   "a \<in> {m..n} \<Longrightarrow> j a \<in> {..nat (n - m)}"
    and   "b \<in> {..nat (n - m)} \<Longrightarrow> j (i b) = b"
    and   "b \<in> {..nat (n - m)} \<Longrightarrow> i b \<in> {m..n}"
    and   "a \<in> {m..n} \<Longrightarrow> (g \<circ> (+) m \<circ> int) (j a) = g a"
    by auto
qed

subsubsection \<open>An additional fact about algebraic powers of functions\<close>

lemma pow_fun_apply: "(f ^ n) x = (f x) ^ n"
  by (induct n, simp_all)

subsubsection \<open>Some additional facts about formal power and Laurent series\<close>

lemma fps_shift_fps_mult_by_fps_const:
  fixes c :: "'a::{comm_monoid_add,mult_zero}"
  shows "fps_shift n (fps_const c * f) = fps_const c * fps_shift n f"
  and   "fps_shift n (f * fps_const c) = fps_shift n f * fps_const c"
  by    (auto intro: fps_ext)

lemma fps_shift_mult_Suc:
  fixes f g :: "'a::{comm_monoid_add,mult_zero} fps"
  shows "fps_shift (Suc n) (f*g)
          = fps_const (f$0) * fps_shift (Suc n) g + fps_shift n (fps_shift 1 f * g)"
  and   "fps_shift (Suc n) (f*g)
          = fps_shift n (f * fps_shift 1 g) + fps_shift (Suc n) f * fps_const (g$0)"
proof-
  show "fps_shift (Suc n) (f*g)
          = fps_const (f$0) * fps_shift (Suc n) g + fps_shift n (fps_shift 1 f * g)"
  proof (intro fps_ext)
    fix k
    have "{0<..Suc (k + n)} = {Suc 0..Suc (k + n)}" by auto
    thus
      "fps_shift (Suc n) (f*g) $ k
        = (fps_const (f$0) * fps_shift (Suc n) g + fps_shift n (fps_shift 1 f * g)) $ k"
      using fps_mult_nth[of _ g]
            sum.head[of 0 "k + Suc n" "\<lambda>i. f$i * g$(k + Suc n - i)"]
            sum.atLeast_Suc_atMost_Suc_shift[of "\<lambda>i. f$i * g$(k + Suc n - i)" 0 "k+n"]
      by    simp
  qed
  show "fps_shift (Suc n) (f*g)
          = fps_shift n (f * fps_shift 1 g) + fps_shift (Suc n) f * fps_const (g$0)"
  proof (intro fps_ext)
    fix k
    have "\<forall>i\<in>{0..k + n}. Suc (k + n) - i = Suc (k + n -i)" by auto
    thus "fps_shift (Suc n) (f*g) $ k
          = (fps_shift n (f * fps_shift 1 g) + fps_shift (Suc n) f * fps_const (g$0)) $ k"
      using fps_mult_nth[of f] by simp
  qed
qed

lemma fls_subdegree_minus':
  "fls_subdegree (f - g) = fls_subdegree f"
  if "f \<noteq> 0" and "fls_subdegree g > fls_subdegree f"
  using that by (auto intro: fls_subdegree_eqI)

lemma fls_regpart_times_fps_X:
  fixes   f :: "'a::{comm_monoid_add,mult_zero,monoid_mult} fls"
  assumes "fls_subdegree f \<ge> 0"
  shows   "fls_regpart f * fps_X = fls_regpart (fls_shift (-1) f)"
  and     "fps_X * fls_regpart f = fls_regpart (fls_shift (-1) f)"
proof-
  show "fls_regpart f * fps_X  = fls_regpart (fls_shift (-1) f)"
  proof (intro fps_ext)
    fix n show "(fls_regpart f * fps_X) $ n = fls_regpart (fls_shift (-1) f) $ n"
      using assms by (cases n) auto
  qed
  thus "fps_X * fls_regpart f = fls_regpart (fls_shift (-1) f)"
    by (simp add: fps_mult_fps_X_commute)
qed

lemma fls_regpart_times_fps_X_power:
  fixes   f :: "'a::semiring_1 fls"
  assumes "fls_subdegree f \<ge> 0"
  shows   "fls_regpart f * fps_X ^ n = fls_regpart (fls_shift (-n) f)"
  and     "fps_X ^ n * fls_regpart f = fls_regpart (fls_shift (-n) f)"
proof-
  show "fps_X ^ n * fls_regpart f = fls_regpart (fls_shift (-n) f)"
  proof (induct n)
    case (Suc n)
    from assms Suc
      have  A: "fps_X ^ Suc n * fls_regpart f = fls_regpart (fls_shift (-(int n + 1)) f)"
      using fls_shift_nonneg_subdegree[of "-int n" f]
      by    (simp add: mult.assoc fls_regpart_times_fps_X(2))
    have B: "- (int n + 1) = - int (Suc n)" by simp
    have "fls_regpart (fls_shift (-(int n + 1)) f) = fls_regpart (fls_shift (- int (Suc n)) f)"
      using arg_cong[OF B] by simp
    with A show ?case by simp
  qed simp
  thus "fls_regpart f * fps_X ^ n = fls_regpart (fls_shift (-n) f)"
    by (simp flip: fps_mult_fps_X_power_commute)
qed

lemma fls_base_factor_uminus: "fls_base_factor (-f) = - fls_base_factor f"
  unfolding fls_base_factor_def by simp


subsection \<open>Partial evaluation of formal power series\<close>

text \<open>Make a degree-n polynomial out of a formal power series.\<close>
definition poly_of_fps
  where "poly_of_fps f n = Abs_poly (\<lambda>i. if i \<le> n then f$i else 0)"

lemma if_then_MOST_zero:
  "\<forall>\<^sub>\<infinity>x. (if P x then f x else 0) = 0"
  if "\<forall>\<^sub>\<infinity>x. \<not> P x"
proof (rule iffD2, rule MOST_iff_cofinite)
  have "{x. (if P x then f x else 0) \<noteq> 0} \<subseteq> {x. \<not> \<not> P x}" by auto
  with that show "finite {x. (if P x then f x else 0) \<noteq> 0}"
    using iffD1[OF MOST_iff_cofinite] finite_subset by blast
qed

lemma truncated_fps_eventually_zero:
  "(\<lambda>i. if i \<le> n then f$i else 0) \<in> {g. \<forall>\<^sub>\<infinity>n. g n = 0}"
  by (auto intro: if_then_MOST_zero iffD2[OF eventually_cofinite])

lemma coeff_poly_of_fps[simp]:
  "coeff (poly_of_fps f n) i = (if i \<le> n then f$i else 0)"
  unfolding poly_of_fps_def
  using     truncated_fps_eventually_zero[of n f]
            Abs_poly_inverse[of "\<lambda>i. if i \<le> n then f$i else 0"]
  by        simp

lemma poly_of_fps_0[simp]: "poly_of_fps 0 n = 0"
  by (auto intro: poly_eqI)

lemma poly_of_fps_0th_conv_pCons[simp]: "poly_of_fps f 0 = [:f$0:]"
proof (intro poly_eqI)
  fix i
  show "coeff (poly_of_fps f 0) i = coeff [:f$0:] i"
    by (cases i) auto
qed

lemma poly_of_fps_degree: "degree (poly_of_fps f n) \<le> n"
  by (auto intro: degree_le)

lemma poly_of_fps_Suc:
  "poly_of_fps f (Suc n) = poly_of_fps f n + monom (f $ Suc n) (Suc n)"
proof (intro poly_eqI)
  fix m
  show
    "coeff (poly_of_fps f (Suc n)) m =
      coeff (poly_of_fps f n + monom (f $ Suc n) (Suc n)) m"
    by (cases "m \<le> Suc n") auto
qed

lemma poly_of_fps_Suc_nth_eq0:
  "poly_of_fps f (Suc n) = poly_of_fps f n" if "f $ Suc n = 0"
proof (intro poly_eqI)
  fix i from that show "coeff (poly_of_fps f (Suc n)) i = coeff (poly_of_fps f n) i"
    by (cases i "Suc n" rule: linorder_cases) auto
qed

lemma poly_of_fps_Suc_conv_pCons_shift:
  "poly_of_fps f (Suc n) = pCons (f$0) (poly_of_fps (fps_shift 1 f) n)"
proof (intro poly_eqI)
  fix i
  show "coeff (poly_of_fps f (Suc n)) i
          = coeff (pCons (f$0) (poly_of_fps (fps_shift 1 f) n)) i"
    by (cases i) auto
qed

abbreviation "fps_parteval f x n \<equiv> poly (poly_of_fps f n) x"
abbreviation "fls_base_parteval f \<equiv> fps_parteval (fls_base_factor_to_fps f)"

lemma fps_parteval_0[simp]: "fps_parteval 0 x n = 0"
  by (induct n) auto

lemma fps_parteval_0th[simp]: "fps_parteval f x 0 = f $ 0"
  by simp

lemma fps_parteval_Suc:
  "fps_parteval f x (Suc n) = fps_parteval f x n + (f $ Suc n) * x ^ Suc n"
  for f :: "'a::comm_semiring_1 fps"
  by  (simp add: poly_of_fps_Suc poly_monom)

lemma fps_parteval_Suc_cons:
  "fps_parteval f x (Suc n) = f$0 + x * fps_parteval (fps_shift 1 f) x n"
  by (simp add: poly_of_fps_Suc_conv_pCons_shift)

lemma fps_parteval_at_0[simp]: "fps_parteval f 0 n = f $ 0"
  by (cases n) (auto simp add: fps_parteval_Suc_cons)

lemma fps_parteval_conv_sum:
  "fps_parteval f x n = (\<Sum>k\<le>n. f$k * x^k)" for x :: "'a::comm_semiring_1"
  by (induct n) (auto simp add: fps_parteval_Suc)

lemma fls_base_parteval_conv_sum:
  "fls_base_parteval f x n = (\<Sum>k\<le>n. f$$(fls_subdegree f + int k) * x^k)"
  for f :: "'a::comm_semiring_1 fls" and x :: 'a and n :: nat
  using fps_parteval_conv_sum[of "fls_base_factor_to_fps f"] fls_base_factor_to_fps_nth[of f]
  by    presburger

lemma fps_parteval_fps_const[simp]:
  "fps_parteval (fps_const c) x n = c"
  by (induct n) (auto simp add: fps_parteval_Suc_cons fps_shift_fps_const)

lemma fps_parteval_1[simp]: "fps_parteval 1 x n = 1"
  using fps_parteval_fps_const[of 1] by simp

lemma fps_parteval_mult_by_fps_const:
  "fps_parteval (fps_const c * f) x n = c * fps_parteval f x n"
  using mult.commute[of c x] mult.assoc[of x c] mult.assoc[of c x]
  by    (induct n arbitrary: f)
        (auto simp add: fps_parteval_Suc_cons fps_shift_fps_mult_by_fps_const(1) distrib_left)

lemma fps_parteval_plus[simp]:
  "fps_parteval (f + g) x n = fps_parteval f x n + fps_parteval g x n"
  by  (induct n arbitrary: f g)
      (auto simp add: fps_parteval_Suc_cons fps_shift_add algebra_simps)

lemma fps_parteval_uminus[simp]:
  "fps_parteval (-f) x n = - fps_parteval f x n" for f :: "'a::comm_ring fps"
  by  (induct n arbitrary: f) (auto simp add: fps_parteval_Suc_cons fps_shift_uminus)

lemma fps_parteval_minus[simp]:
  "fps_parteval (f - g) x n = fps_parteval f x n - fps_parteval g x n"
  for f :: "'a::comm_ring fps"
  using fps_parteval_plus[of f "-g"] by simp

lemma fps_parteval_mult_fps_X:
  fixes f :: "'a::comm_semiring_1 fps"
  shows "fps_parteval (f * fps_X) x (Suc n) = x * fps_parteval f x n"
  and   "fps_parteval (fps_X * f) x (Suc n) = x * fps_parteval f x n"
  using fps_shift_times_fps_X'[of f]
  by    (auto simp add: fps_parteval_Suc_cons simp flip: fps_mult_fps_X_commute)

lemma fps_parteval_mult_fps_X_power:
  fixes f :: "'a::comm_semiring_1 fps"
  assumes "n \<ge> m"
  shows   "fps_parteval (f * fps_X ^ m) x n = x^m * fps_parteval f x (n - m)"
  and     "fps_parteval (fps_X ^ m * f) x n = x^m * fps_parteval f x (n - m)"
proof-
  have
    "n \<ge> m \<Longrightarrow> fps_parteval (f * fps_X ^ m) x n = x^m * fps_parteval f x (n - m)"
  proof (induct m arbitrary: n)
    case (Suc m) thus ?case
      using fps_shift_times_fps_X'[of "f * fps_X^m"]
      by    (cases n)
            (auto simp add: fps_parteval_Suc_cons mult.assoc simp flip: power_Suc2)
  qed simp
  with assms show "fps_parteval (f * fps_X ^ m) x n = x^m * fps_parteval f x (n - m)"
    by fast
  thus "fps_parteval (fps_X ^ m * f) x n = x^m * fps_parteval f x (n - m)"
    by (simp add: fps_mult_fps_X_power_commute)
qed

lemma fps_parteval_mult_right:
  "fps_parteval (f * g) x n =
    fps_parteval (Abs_fps (\<lambda>i. f$i * fps_parteval g x (n - i))) x n"
proof (induct n arbitrary: f)
  case (Suc n)
  have 1:
    "poly_of_fps (Abs_fps (\<lambda>i. f $ Suc i * fps_parteval g x (n - i))) n
      = poly_of_fps (Abs_fps (\<lambda>i. f $ Suc i * fps_parteval g x (Suc n - Suc i))) n"
    by (intro poly_eqI) auto
  from Suc have
    "fps_parteval (fps_shift 1 f * g) x n
      = fps_parteval (Abs_fps (\<lambda>i. f $ Suc i * fps_parteval g x (n - i))) x n"
    by simp
  with 1 have
    "fps_parteval (f * g) x (Suc n)
      = f$0 * fps_parteval g x (Suc n)
      + x * fps_parteval (Abs_fps (\<lambda>i. f $ Suc i * fps_parteval g x (n - i))) x n
    "
    using fps_shift_mult_Suc(1)[of 0 f g]
    by (simp add: fps_parteval_Suc_cons fps_parteval_mult_by_fps_const algebra_simps)
  thus ?case by (simp add: fps_parteval_Suc_cons fps_shift_def)
qed simp

lemma fps_parteval_mult_left:
  "fps_parteval (f * g) x n =
    fps_parteval (Abs_fps (\<lambda>i. fps_parteval f x (n - i) * g$i)) x n"
  using fps_parteval_mult_right[of g f]
  by    (simp add: mult.commute)

lemma fps_parteval_mult_conv_sum:
  fixes f g :: "'a::comm_semiring_1 fps"
  shows "fps_parteval (f * g) x n = (\<Sum>k\<le>n. f$k * fps_parteval g x (n - k) * x^k)"
  and   "fps_parteval (f * g) x n = (\<Sum>k\<le>n. fps_parteval f x (n - k) * g$k * x^k)"
  using fps_parteval_mult_right[of f g n x]
        fps_parteval_conv_sum[of "Abs_fps (\<lambda>i. f$i * fps_parteval g x (n - i))"]
        fps_parteval_mult_left[of f g n x]
        fps_parteval_conv_sum[of "Abs_fps (\<lambda>i. fps_parteval f x (n - i) * g$i)"]
  by    auto

lemma fps_parteval_fls_base_factor_to_fps_diff:
  "fls_base_parteval (f - g) x n = fls_base_parteval f x n"
  if "f \<noteq> 0" and "fls_subdegree g > fls_subdegree f + (int n)"
  for f g :: "'a::comm_ring_1 fls"
  using that
  by    (induct n) (auto simp add: fps_parteval_Suc fls_subdegree_minus')


subsection \<open>
  Vanishing of formal power series relative to divisibility of all partial sums
\<close>

definition fps_pvanishes :: "'a::comm_semiring_1 \<Rightarrow> 'a fps \<Rightarrow> bool"
  where "fps_pvanishes p f \<equiv> (\<forall>n::nat. p ^ Suc n dvd (fps_parteval f p n))"

lemma fps_pvanishesD: "fps_pvanishes p f \<Longrightarrow> p ^ Suc n dvd (fps_parteval f p n)"
  unfolding fps_pvanishes_def by simp

lemma fps_pvanishesI:
  "fps_pvanishes p f" if "\<And>n::nat. p ^ Suc n dvd (fps_parteval f p n)"
  using that unfolding fps_pvanishes_def by simp

lemma fps_pvanishes_0[simp]: "fps_pvanishes p 0"
  by (auto intro: fps_pvanishesI)

lemma fps_pvanishes_at_0[simp]: "fps_pvanishes 0 f = (f$0 = 0)"
  unfolding fps_pvanishes_def by auto

lemma fps_pvanishes_at_unit: "fps_pvanishes p f" if "is_unit p"
  by (metis that is_unit_power_iff unit_imp_dvd fps_pvanishesI)

lemma fps_pvanishes_one_iff:
  "fps_pvanishes p 1 = is_unit p"
  using fps_pvanishes_def is_unit_power_iff[of p "Suc _"] by auto

lemma fps_pvanishes_uminus[simp]:
  "fps_pvanishes p (-f)" if "fps_pvanishes p f" for f :: "'a::comm_ring_1 fps"
  using fps_pvanishesD[OF that] iffD2[OF dvd_minus_iff] by (fastforce intro: fps_pvanishesI)

lemma fps_pvanishes_add[simp]:
  "fps_pvanishes p (f + g)" if "fps_pvanishes p f" and "fps_pvanishes p g"
  for f :: "'a::comm_semiring_1 fps"
proof (intro fps_pvanishesI)
  fix n from that show "p ^ Suc n dvd fps_parteval (f+g) p n"
    using fps_pvanishesD[of p _ n]
          dvd_add[of "p^Suc n" "fps_parteval f p n" "fps_parteval g p n"]
    by    auto
qed

lemma fps_pvanishes_minus[simp]:
  "fps_pvanishes p (f - g)" if "fps_pvanishes p f" and "fps_pvanishes p g"
  for f :: "'a::comm_ring_1 fps"
  using that fps_pvanishes_uminus[of p g] fps_pvanishes_add[of p f "-g"] by simp

lemma fps_pvanishes_mult: "fps_pvanishes p (f * g)" if "fps_pvanishes p g"
proof (intro fps_pvanishesI)
  fix n
  have "p ^ Suc n dvd (\<Sum>i\<le>n. f$i * fps_parteval g p (n - i) * p^i)"
  proof (intro dvd_sum)
    fix k assume "k \<in> {..n}"
    with that show "p ^ Suc n dvd f $ k * fps_parteval g p (n - k) * p ^ k"
      using fps_pvanishesD[of p g] power_add[of p "Suc (n - k)" k] by (simp add: mult_dvd_mono)
  qed
  thus "p ^ Suc n dvd fps_parteval (f * g) p n" by (simp add: fps_parteval_mult_conv_sum(1))
qed

lemma fps_pvanishes_mult_fps_X_iff:
  assumes "(p::'a::idom) \<noteq> 0"
  shows "fps_pvanishes p f \<longleftrightarrow> fps_pvanishes p (f * fps_X)"
  and   "fps_pvanishes p f \<longleftrightarrow> fps_pvanishes p (fps_X * f)"
proof-
  show "fps_pvanishes p f \<longleftrightarrow> fps_pvanishes p (f * fps_X)"
  proof
    assume b: "fps_pvanishes p (f * fps_X)"
    show "fps_pvanishes p f"
    proof (intro fps_pvanishesI)
      fix n from b assms show "p ^ Suc n dvd fps_parteval f p n"
        using fps_pvanishesD[of p "f * fps_X" "Suc n"] fps_parteval_mult_fps_X(1)[of f n p]
        by    simp
    qed
  qed (auto intro: fps_pvanishes_mult simp add: mult.commute)
  thus "fps_pvanishes p f \<longleftrightarrow> fps_pvanishes p (fps_X * f)"
    by (simp add: fps_mult_fps_X_commute)
qed

lemma fps_pvanishes_mult_fps_X_power_iff:
  assumes "(p::'a::idom) \<noteq> 0"
  shows   "fps_pvanishes p f \<longleftrightarrow> fps_pvanishes p (f * fps_X ^ n)"
  and     "fps_pvanishes p f \<longleftrightarrow> fps_pvanishes p (fps_X ^ n * f)"
proof-
  show "fps_pvanishes p f \<longleftrightarrow> fps_pvanishes p (fps_X ^ n * f)"
  proof (induct n)
    case (Suc n) with assms show ?case
      using fps_pvanishes_mult_fps_X_iff(2)[of p "fps_X ^ n * f"]
      by    (simp add: mult.assoc)
  qed simp
  thus "fps_pvanishes p f \<longleftrightarrow> fps_pvanishes p (f * fps_X ^ n)"
    by (simp flip: fps_mult_fps_X_power_commute)
qed


subsection \<open>Equivalence and depth of formal Laurent series relative to a prime\<close>

subsubsection \<open>Definition of equivalence and basic facts\<close>

abbreviation "fps_primevanishes p \<equiv> fps_pvanishes (Rep_prime p)"

overloading
  p_equal_fls \<equiv>
    "p_equal :: 'a::nontrivial_factorial_comm_ring prime \<Rightarrow>
      'a fls \<Rightarrow> 'a fls \<Rightarrow> bool"
begin

definition p_equal_fls ::
  "'a::nontrivial_factorial_comm_ring prime \<Rightarrow>
    'a fls \<Rightarrow> 'a fls \<Rightarrow> bool"
  where
    "p_equal_fls p f g \<equiv> fps_primevanishes p (fls_base_factor_to_fps (f - g))"

end  (* overloading *)

context
  fixes p :: "'a :: nontrivial_factorial_comm_ring prime"
begin

lemma p_equal_flsD:
  "f \<simeq>\<^sub>p g \<Longrightarrow> fps_primevanishes p (fls_base_factor_to_fps (f - g))"
  for f g :: "'a fls"
  unfolding p_equal_fls_def by simp

lemma p_equal_fls_imp_p_dvd: "p pdvd ((f - g) $$ (fls_subdegree (f - g)))"
  if "f \<simeq>\<^sub>p g"
  for f g :: "'a fls"
proof-
  have "int (0::nat) = 0" by simp
  thus ?thesis
    by (metis
          that p_equal_flsD fps_pvanishesD power_Suc0_right fps_parteval_0th
          fls_base_factor_to_fps_nth add_0_right
    )
qed

lemma p_equal_flsI:
  "fps_primevanishes p (fls_base_factor_to_fps (f - g)) \<Longrightarrow> f \<simeq>\<^sub>p g"
  for f g :: "'a fls"
  unfolding p_equal_fls_def by simp

lemma p_equal_fls_conv_p_equal_0:
  "f \<simeq>\<^sub>p g \<longleftrightarrow> (f - g) \<simeq>\<^sub>p 0"
  for f g :: "'a fls"
  unfolding p_equal_fls_def by auto

lemma p_equal_fls_refl: "f \<simeq>\<^sub>p f" for f:: "'a fls"
  by (auto intro: p_equal_flsI)

lemma p_equal_fls_sym:
  "f \<simeq>\<^sub>p g \<Longrightarrow> g \<simeq>\<^sub>p f" for f g :: "'a fls"
  using     p_equal_flsD fps_pvanishes_uminus fls_uminus_subdegree[of "f-g"]
  unfolding p_equal_fls_def
  by        fastforce

lemma p_equal_fls_shift_iff:
  "f \<simeq>\<^sub>p g \<longleftrightarrow> (fls_shift n f) \<simeq>\<^sub>p (fls_shift n g)"
  for f g :: "'a fls"
  using fls_base_factor_shift[of n "f - g"] unfolding p_equal_fls_def by auto

lemma p_equal_fls_extended_sum_iff:
  "f \<simeq>\<^sub>p g \<longleftrightarrow>
    (\<forall>n. (Rep_prime p) ^ Suc n dvd
      (\<Sum>k\<le>n. (f - g)$$(N + int k) * (Rep_prime p)^k))"
  if "N \<le> min (fls_subdegree f) (fls_subdegree g)"
proof-
  define pp where "pp \<equiv> Rep_prime p"
  define dfg where "dfg \<equiv> fls_subdegree (f - g)"
  define D where "D \<equiv> nat (dfg - N - 1)"
  from that dfg_def D_def
    have  D: "f \<noteq> g \<Longrightarrow> N \<noteq> dfg \<Longrightarrow> dfg - N - 1 \<ge> 0"
    using fls_subdegree_minus
    by    force
  have
    "(f \<simeq>\<^sub>p g) =
      (\<forall>n. pp ^ Suc n dvd (\<Sum>k\<le>n. (f - g) $$ (N + int k) * pp ^ k))"
  proof (standard, standard)
    fix n :: nat
    assume fg: "f \<simeq>\<^sub>p g"
    consider
               "f = g"                    |
               "N = dfg"                  |
      (n_le_D) "f \<noteq> g" "N \<noteq> dfg" "n \<le> D" |
      (n_gt_D) "f \<noteq> g" "N \<noteq> dfg" "n > D"
      by fastforce
    thus "pp ^ Suc n dvd (\<Sum>k\<le>n. (f - g) $$ (N + int k) * pp ^ k)"
    proof cases
      case n_le_D
      with D_def have "\<forall>k\<le>n. N + int k < dfg" using D by linarith
      with dfg_def show ?thesis using fls_eq0_below_subdegree[of _ "f - g"] by simp
    next
      case n_gt_D
      with D_def that
        have  N_k  : "\<forall>k\<le>D. N + int k < dfg"
        and   N_D_k: "\<forall>k. N + int (Suc D + k) = dfg + int k"
        using D
        by    (force, linarith)
      from dfg_def have "\<forall>k\<le>D. (f - g)$$(N + int k) = 0"
        using N_k fls_eq0_below_subdegree[of _ "f - g"] by blast
      hence partsum: "(\<Sum>k\<le>D. (f - g)$$(N + int k) * pp^k) = 0" by force
      from pp_def \<open>f \<simeq>\<^sub>p g\<close> obtain k
        where k: "fls_base_parteval (f - g) pp (n - Suc D) = pp ^ Suc (n - Suc D) * k"
        using p_equal_flsD fps_pvanishesD by blast
      from \<open>n > D\<close> have exp: "Suc D + Suc (n - Suc D) = Suc n" by auto
      from \<open>n > D\<close> have
        "(\<Sum>k\<le>n. (f - g)$$(N + int k) * pp^k) =
          (\<Sum>k\<le>D. (f - g)$$(N + int k) * pp^k) +
          (\<Sum>k=Suc D..n. (f - g)$$(N + int k) * pp^k)"
        using sum_up_index_split[of _ D "n - D"] by auto
      also from \<open>n > D\<close> have
        "\<dots> = (\<Sum>k\<le>n - Suc D.
          (f - g) $$ (N + int (Suc D + k)) * pp ^ (Suc D + k))"
        using partsum atLeast0AtMost[of "n - Suc D"]
              sum.atLeastAtMost_shift_bounds[
                of "\<lambda>k. (f-g)$$(N + int k) * pp^k" 0 "Suc D" "n - Suc D"
              ]
        by    auto
      also from D_def have
        "\<dots> = (\<Sum>k\<le>n - Suc D. (f - g) $$ (dfg + int k) * (pp ^ Suc D * pp ^ k))"
        using N_D_k power_add[of pp "Suc D"] by force
      also have
        "\<dots> = pp ^ Suc D * (\<Sum>k\<le>n - Suc D. (f - g) $$ (dfg + int k) * pp ^ k)"
        by (simp add: algebra_simps sum_distrib_left)
      also have "\<dots> = pp ^ Suc D * (pp ^ Suc (n - Suc D) * k)"
        using k dfg_def fls_base_parteval_conv_sum[of "f - g" "n - Suc D" pp] by presburger
      also have "\<dots> = pp ^ (Suc D + Suc (n - Suc D)) * k"
        by (simp add: algebra_simps power_add)
      finally have "(\<Sum>k\<le>n. (f - g)$$(N + int k) * pp^k) = pp ^ Suc n * k"
        using \<open>n > D\<close> by auto
      thus ?thesis by auto
    qed (simp, metis fg dfg_def pp_def fls_base_parteval_conv_sum p_equal_flsD fps_pvanishesD)
  next
    assume *: "\<forall>n. pp ^ Suc n dvd (\<Sum>k\<le>n. (f - g)$$(N + int k) * pp^k)"
    consider "f = g" | "N = dfg" |  "f \<noteq> g" "N \<noteq> dfg" by blast
    thus "f \<simeq>\<^sub>p g"
    proof cases
      case 1 thus ?thesis by (simp add: p_equal_fls_refl)
    next
      case 2 with pp_def dfg_def * show ?thesis
        using p_equal_flsI fps_pvanishesI fls_base_parteval_conv_sum by metis
    next
      case 3 show ?thesis
      proof (intro p_equal_flsI fps_pvanishesI)
        fix n
        from 3 dfg_def D_def
          have  ND     : "\<forall>k. N + int (Suc D + k) = dfg + int k"
          and   dfg_N_n: "nat (dfg - N) + n = Suc D + n"
          and   sum_0  : "(\<Sum>k\<le>D. (f - g) $$ (N + int k) * pp ^ k) = 0"
          using D fls_eq0_below_subdegree[of _ "f - g"]
          by    (fastforce, simp, simp)
        have
          "(\<Sum>k\<le>nat (dfg - N) + n. (f - g)$$(N + int k) * pp^k) =
            (\<Sum>k = Suc D..Suc D + n. (f - g) $$ (N + int k) * pp ^ k)"
          using dfg_N_n sum_0
                sum_up_index_split[of "\<lambda>k. (f - g)$$(N + int k) * pp^k" D "Suc n"]
          by    auto
        also have
          "\<dots> = sum ((\<lambda>k. (f - g) $$ (N + int k) * pp ^ k) \<circ> (+) (Suc D))
            {0..n}"
          using add.commute[of "Suc D" n] add_0_left[of "Suc D"]
                sum.atLeastAtMost_shift_bounds[
                  of "\<lambda>k. (f-g)$$(N + int k) * pp^k" 0 "Suc D" n
                ]
          by    argo
        also have "\<dots> = pp ^ Suc D * (\<Sum>k\<le>n. (f - g) $$ (dfg + int k) * pp ^ k)"
          using ND by (force simp add: algebra_simps atLeast0AtMost power_add sum_distrib_left)
        finally have
          "(\<Sum>k\<le>nat (dfg - N) + n. (f - g)$$(N + int k) * pp^k) =
            pp ^ Suc D * fls_base_parteval (f - g) pp n"
          using dfg_def fls_base_parteval_conv_sum[of "f - g" n pp] by force
        moreover have "Suc (nat (dfg - N) + n) = Suc D + Suc n" using dfg_N_n by presburger
        moreover from pp_def have "pp ^ Suc D \<noteq> 0" using Rep_prime_n0 by auto
        ultimately have "pp ^ Suc n dvd fls_base_parteval (f - g) pp n"
          using * power_add dvd_times_left_cancel_iff by metis
        with pp_def show "Rep_prime p ^ Suc n dvd fls_base_parteval (f - g) (Rep_prime p) n"
          by blast
      qed
    qed
  qed
  with pp_def show ?thesis by fast
qed

lemma p_equal_fls_extended_intsum_iff:
  "f \<simeq>\<^sub>p g \<longleftrightarrow>
    (\<forall>n\<ge>N. (Rep_prime p) ^ Suc (nat (n - N)) dvd
      (\<Sum>k=N..n. (f - g)$$k * (Rep_prime p) ^ nat (k - N)))"
  if "N \<le> min (fls_subdegree f) (fls_subdegree g)"
proof (standard, clarify)
  assume fg: "f \<simeq>\<^sub>p g"
  fix n::int assume n: "n \<ge> N"
  define m where "m \<equiv> nat (n - N)"
  from that fg have
    "(Rep_prime p) ^ Suc m dvd (\<Sum>k\<le>m. (f - g)$$(N + int k) * (Rep_prime p)^k)"
    using p_equal_fls_extended_sum_iff by blast
  moreover from n m_def have
    "(\<Sum>k=N..n. (f - g)$$k * (Rep_prime p) ^ nat( k - N)) =
      (\<Sum>k\<le>m. (f - g)$$(N + int k) * (Rep_prime p)^k)"
    by (simp add: sum.atLeastAtMost_int_shift_bounds algebra_simps)
  ultimately show
    "(Rep_prime p) ^ Suc (nat (n - N)) dvd
      (\<Sum>k=N..n. (f - g)$$k * (Rep_prime p) ^ nat (k - N))"
    using m_def by argo
next
  assume dvd_sum:
    "\<forall>n\<ge>N. (Rep_prime p) ^ Suc (nat (n - N)) dvd
      (\<Sum>k=N..n. (f - g)$$k * (Rep_prime p) ^ nat (k - N))"
  show "f \<simeq>\<^sub>p g"
  proof (rule iffD2, rule p_equal_fls_extended_sum_iff, rule that, safe)
    fix n::nat
    have N_n: "N + int n \<ge> N" by fastforce
    moreover have "nat (N + int n - N) = n" by simp
    ultimately have
      "(Rep_prime p) ^ Suc n dvd
        (\<Sum>k=N..N + int n. (f - g)$$k * (Rep_prime p) ^ nat (k - N))"
      using dvd_sum by fastforce
    moreover from N_n have
      "(\<Sum>k\<le>n. (f - g) $$ (N + int k) * Rep_prime p ^ k) =
        (\<Sum>k=N..N + int n. (f - g)$$k * (Rep_prime p) ^ nat (k - N))"
      by (simp add: sum.atLeastAtMost_int_shift_bounds)
    ultimately show
      "Rep_prime p ^ Suc n dvd (\<Sum>k\<le>n. (f - g) $$ (N + int k) * Rep_prime p ^ k)"
      by presburger
  qed
qed

lemma fls_p_equal0_extended_sum_iff:
  "f \<simeq>\<^sub>p 0 \<longleftrightarrow>
    (\<forall>n. (Rep_prime p) ^ Suc n dvd
      (\<Sum>k\<le>n. f$$(N + int k) * (Rep_prime p)^k))"
  if "N \<le> fls_subdegree f"
proof-
  define pp where "pp \<equiv> Rep_prime p"
  have d0_case:
    "\<And>f N. fls_subdegree f = 0 \<Longrightarrow> N \<le> 0 \<Longrightarrow>
      f \<simeq>\<^sub>p 0 \<longleftrightarrow>
        (\<forall>n. pp ^ Suc n dvd (\<Sum>k\<le>n. f$$(N + int k) * pp^k))"
  proof-
    fix f N from pp_def
      show  "fls_subdegree f = 0 \<Longrightarrow> N \<le> 0 \<Longrightarrow> ?thesis f N"
      using p_equal_fls_extended_sum_iff[of N f 0]
      by    simp
  qed
  have "f \<simeq>\<^sub>p 0 \<longleftrightarrow> (fls_base_factor f) \<simeq>\<^sub>p 0"
    using p_equal_fls_shift_iff[of f 0] fls_base_factor_def by auto
  also from that pp_def have
    "\<dots> = (\<forall>n. pp ^ Suc n dvd (\<Sum>k\<le>n. f $$ ((N + int k)) * pp^k))"
    using fls_base_factor_subdegree[of f] d0_case[of "fls_base_factor f" "N - fls_subdegree f"]
    by    auto
  finally show ?thesis using pp_def by blast
qed

lemma fls_p_equal0_extended_intsum_iff:
  "f \<simeq>\<^sub>p 0 \<longleftrightarrow>
    (\<forall>n\<ge>N. (Rep_prime p) ^ Suc (nat (n - N)) dvd
      (\<Sum>k=N..n. f$$k * (Rep_prime p) ^ nat (k - N)))"
  if "N \<le> fls_subdegree f"
proof (standard, clarify)
  assume f: "f \<simeq>\<^sub>p 0"
  fix n::int assume n: "n \<ge> N"
  define m where "m \<equiv> nat (n - N)"
  from that f have
    "(Rep_prime p) ^ Suc m dvd (\<Sum>k\<le>m. f$$(N + int k) * (Rep_prime p)^k)"
    using fls_p_equal0_extended_sum_iff by blast
  moreover from n m_def have
    "(\<Sum>k=N..n. f$$k * (Rep_prime p) ^ nat (k - N)) =
      (\<Sum>k\<le>m. f$$(N + int k) * (Rep_prime p)^k)"
    by (simp add: sum.atLeastAtMost_int_shift_bounds algebra_simps)
  ultimately show
    "(Rep_prime p) ^ Suc (nat (n - N)) dvd
      (\<Sum>k=N..n. f$$k * (Rep_prime p) ^ nat (k - N))"
    using m_def by argo
next
  assume dvd_sum:
    "\<forall>n\<ge>N. (Rep_prime p) ^ Suc (nat (n - N)) dvd
      (\<Sum>k=N..n. f$$k * (Rep_prime p) ^ nat (k - N))"
  show "f \<simeq>\<^sub>p 0"
  proof (rule iffD2, rule fls_p_equal0_extended_sum_iff, rule that, safe)
    fix n::nat
    have N_n: "N + int n \<ge> N" by fastforce
    moreover have "nat (N + int n - N) = n" by simp
    ultimately have
      "(Rep_prime p) ^ Suc n dvd
        (\<Sum>k=N..N + int n. f$$k * (Rep_prime p) ^ nat (k - N))"
      using dvd_sum by fastforce
    moreover from N_n have
      "(\<Sum>k\<le>n. f $$ (N + int k) * Rep_prime p ^ k) =
        (\<Sum>k=N..N + int n. f$$k * (Rep_prime p) ^ nat (k - N))"
      by (simp add: sum.atLeastAtMost_int_shift_bounds)
    ultimately show
      "Rep_prime p ^ Suc n dvd (\<Sum>k\<le>n. f $$ (N + int k) * Rep_prime p ^ k)"
      by presburger
  qed
qed

end (* context nontrivial_factorial_comm_ring *)

context
  fixes p :: "'a :: nontrivial_factorial_idom prime"
begin

lemma fls_1_not_p_equal_0: "(1::'a fls) \<not>\<simeq>\<^sub>p 0"
  using fps_pvanishes_one_iff not_prime_unit Rep_prime[of p] unfolding p_equal_fls_def by auto

lemma p_equal_fls0_nonneg_subdegree:
  "f \<simeq>\<^sub>p 0 \<longleftrightarrow> fps_primevanishes p (fls_regpart f)"
  if "fls_subdegree f \<ge> 0"
proof-
  define n where "n \<equiv> nat (fls_subdegree f)"
  moreover have
    "f \<simeq>\<^sub>p 0 \<longleftrightarrow>
      fps_primevanishes p (fls_base_factor_to_fps f * fps_X ^ n)"
    unfolding p_equal_fls_def
    using     Rep_prime[of p] fps_pvanishes_mult_fps_X_power_iff(1)[of "Rep_prime p"]
    by        simp
  ultimately show ?thesis
    using fls_base_factor_subdegree[of f] fls_regpart_times_fps_X_power(1)[of "fls_base_factor f" n]
    by    (auto simp add: that)
qed

lemma p_equal_fls_nonneg_subdegree:
  "f \<simeq>\<^sub>p g \<longleftrightarrow> fps_primevanishes p (fls_regpart (f - g))"
  if "fls_subdegree f \<ge> 0" and "fls_subdegree g \<ge> 0"
proof-
  from that have "fls_subdegree (f - g) \<ge> 0"
    using fls_subdegree_minus[of f g] by (cases "f = g") auto
  thus ?thesis using p_equal_fls_conv_p_equal_0[of p f g] p_equal_fls0_nonneg_subdegree by blast
qed

lemma p_equal_fls_trans_to_0:
  "f \<simeq>\<^sub>p g" if "f \<simeq>\<^sub>p 0" and "g \<simeq>\<^sub>p 0" for f g :: "'a fls"
proof (rule iffD2, rule p_equal_fls_shift_iff, rule iffD2, rule p_equal_fls_nonneg_subdegree)
  define n where "n \<equiv> min (fls_subdegree f) (fls_subdegree g)"
  from n_def show "fls_subdegree (fls_shift n f) \<ge> 0" "fls_subdegree (fls_shift n g) \<ge> 0"
    using fls_shift_nonneg_subdegree[of n f] fls_shift_nonneg_subdegree[of n g] by auto
  with that show "fps_primevanishes p (fls_regpart (fls_shift n f - fls_shift n g))"
    using p_equal_fls0_nonneg_subdegree[of "fls_shift n f"] p_equal_fls_shift_iff[of p f 0]
          p_equal_fls0_nonneg_subdegree[of "fls_shift n g"] p_equal_fls_shift_iff[of p g 0]
    by (auto intro: fps_pvanishes_minus)
qed

lemma p_equal_fls_trans:
  "f \<simeq>\<^sub>p g \<Longrightarrow> g \<simeq>\<^sub>p h \<Longrightarrow>
    f \<simeq>\<^sub>p h"
  for f g h :: "'a fls"
  using p_equal_fls_conv_p_equal_0[of p f g] p_equal_fls_conv_p_equal_0[of p h g]
        p_equal_fls_sym[of p g h] p_equal_fls_trans_to_0[of "f-g" "h-g"]
        p_equal_fls_conv_p_equal_0[of p "f-g" "h-g"] p_equal_fls_conv_p_equal_0[of p f h]
  by    auto

end (* context nontrivial_factorial_idom *)

global_interpretation p_equality_fls:
  p_equality_1
    "p_equal :: 'a::nontrivial_factorial_idom prime \<Rightarrow>
      'a fls \<Rightarrow> 'a fls \<Rightarrow> bool"
proof (unfold_locales, intro equivpI)
  fix p :: "'a prime"
  define E :: "'a fls \<Rightarrow> 'a fls \<Rightarrow> bool" where "E \<equiv> p_equal p"
  show "reflp E"
    by (auto intro: reflpI simp add: E_def p_equal_fls_refl)
  show "symp E" using p_equal_fls_sym by (auto intro: sympI simp add: E_def)
  show "transp E"
   using E_def p_equal_fls_trans[of p] by (fastforce intro: transpI)

  fix x y :: "'a fls"
  show "y \<simeq>\<^sub>p 0 \<Longrightarrow> x * y \<simeq>\<^sub>p 0"
    using     p_equal_flsD fps_pvanishes_mult fls_base_factor_to_fps_mult[of x y]
    unfolding p_equal_fls_def
    by        fastforce

qed (rule p_equal_fls_conv_p_equal_0)

overloading
  globally_p_equal_fls \<equiv>
    "globally_p_equal ::
      'a::nontrivial_factorial_idom fls \<Rightarrow> 'a fls \<Rightarrow> bool"
begin

definition globally_p_equal_fls ::
  "'a::nontrivial_factorial_idom fls \<Rightarrow> 'a fls \<Rightarrow> bool"
  where globally_p_equal_fls[simp]:
    "globally_p_equal_fls = p_equality_fls.globally_p_equal"

end  (* overloading *)

context
  fixes p :: "'a :: nontrivial_factorial_idom prime"
begin

lemma p_equal_fls_const_iff:
  "(fls_const c) \<simeq>\<^sub>p (fls_const d) \<longleftrightarrow> c = d" for c d :: 'a
proof
  define pp where "pp \<equiv> Rep_prime p"
  assume "(fls_const c) \<simeq>\<^sub>p (fls_const d)"
  with pp_def have 1: "\<forall>n::nat. pp ^ Suc n dvd (c - d)"
    using p_equal_flsD unfolding fps_pvanishes_def by (fastforce simp add: fls_minus_const)
  have "infinite {n. pp ^ n dvd (c - d)}"
  proof
    assume "finite {n. pp ^ n dvd (c - d)}"
    moreover have "Suc (Max {n. pp ^ n dvd (c - d)}) \<in> {n. pp ^ n dvd (c - d)}" using 1 by simp
    ultimately have "Suc (Max {n. pp ^ n dvd (c - d)}) \<le> Max {n. pp ^ n dvd (c - d)}" by simp
    thus False by simp
  qed
  with pp_def show "c = d" using Rep_prime_not_unit finite_divisor_powers[of "c - d"] by fastforce
qed simp

lemma p_equal_fls_const_0_iff:
  "(fls_const c) \<simeq>\<^sub>p 0 \<longleftrightarrow> c = 0" for c :: 'a
  using p_equal_fls_const_iff[of c 0] by simp

lemma p_equal_fls_X_intpow_iff:
  "((fls_X_intpow m :: 'a fls) \<simeq>\<^sub>p (fls_X_intpow n)) = (m = n)"
proof (induction m n rule: linorder_less_wlog, standard)
  define pp and X :: "int \<Rightarrow> 'a fls"
    where "pp \<equiv> Rep_prime p" and "X \<equiv> fls_X_intpow"
  fix m n :: int assume eq: "(X m) \<simeq>\<^sub>p (X n)" and mn: "m < n"
  with pp_def X_def have
    "pp ^ Suc (nat (n - m)) dvd (\<Sum>k=m..n. (X m - X n)$$k * pp ^ nat (k - m))"
    using p_equal_fls_extended_intsum_iff[of m "X m" "X n" p]
    by    auto
  moreover have
    "(\<Sum>k=m..n. (X m - X n)$$k * pp ^ nat (k - m)) =
      (\<Sum>k\<in>{m,n}. (X m - X n)$$k * pp ^ nat (k - m))"
  proof (rule sum.mono_neutral_right, safe)
    from mn show "m \<in> {m..n}" and "n \<in> {m..n}" by auto
    fix i
    assume  i : "i \<in> {m..n}" "i \<noteq> m"
      and   Xi: "(X m - X n) $$ i * pp ^ nat (i - m) \<noteq> 0"
    with X_def have "X m $$ i = 0" by simp
    moreover from X_def have "i < n \<Longrightarrow> X n $$ i = 0" by force
    ultimately show "i = n" using i(1) Xi by fastforce
  qed
  ultimately have "pp ^ Suc (nat (n - m)) dvd 1 - (pp ^ nat (n - m))"
    using mn X_def by auto
  from this obtain k where "1 - (pp ^ nat (n - m)) = pp ^ Suc (nat (n - m)) * k" by fast
  hence "1 = pp ^ nat (n - m) * (1 + pp * k)" by (simp add: algebra_simps)
  with pp_def mn show "m = n"
    using dvdI[of 1] Rep_prime_not_unit is_unit_power_iff[of pp] by fastforce
qed (auto simp add: p_equal_fls_sym)

lemma fls_X_intpow_nequiv0: "(fls_X_intpow m :: 'a fls) \<not>\<simeq>\<^sub>p 0"
  using p_equal_fls_shift_iff fls_1_not_p_equal_0 by fastforce

end

subsubsection \<open>Depth as maximum subdegree of equivalent series\<close>

text \<open>Each nonzero equivalence class will have a maximum subdegree.\<close>

lemma no_greatest_p_equal_subdegree:
  "f \<simeq>\<^sub>p 0"
  if "\<forall>n :: int. (\<exists>g. fls_subdegree g > n \<and> f \<simeq>\<^sub>p g)"
  for p :: "'a::nontrivial_factorial_comm_ring prime" and f :: "'a fls"
proof (cases "f = 0")
  case False show ?thesis
  proof (intro p_equal_flsI fps_pvanishesI)
    fix n :: nat
    define pp where "pp \<equiv> Rep_prime p"
    from that obtain g where g: "fls_subdegree g > fls_subdegree f + int n" "f \<simeq>\<^sub>p g"
      by blast
    with False pp_def have "fls_base_parteval (f - g) pp n = fls_base_parteval (f - 0) pp n"
      using fps_parteval_fls_base_factor_to_fps_diff by auto
    with False pp_def g(2) show "pp ^ Suc n dvd fls_base_parteval (f - 0) pp n"
      using p_equal_flsD fps_pvanishesD by metis
  qed
qed (simp add: p_equal_fls_refl)

abbreviation
  "p_equal_fls_simplified_set p f \<equiv>
    {g. f \<simeq>\<^sub>p g \<and> fls_subdegree g \<ge> fls_subdegree f}"
\<comment>\<open>
We restrict to those equivalent series that represent a simplification of the given series so that
the image of the collection under taking subdegrees is finite.
\<close>

context
  fixes p :: "'a::nontrivial_factorial_comm_ring prime"
  and   f :: "'a fls"
begin

lemma p_equal_fls_simplifed_nempty:
  "fls_subdegree ` (p_equal_fls_simplified_set p f) \<noteq> {}"
  using p_equal_fls_refl[of p f] by fast

lemma p_equal_fls_simplifed_finite:
  "finite (fls_subdegree ` (p_equal_fls_simplified_set p f))" if "f \<not>\<simeq>\<^sub>p 0"
proof-
  from that obtain n::int
    where "\<forall>g. f \<simeq>\<^sub>p g \<longrightarrow> \<not> fls_subdegree g > n"
    using no_greatest_p_equal_subdegree[of p f]
    by    auto
  hence n: "\<forall>g. f \<simeq>\<^sub>p g \<longrightarrow> fls_subdegree g \<le> n" by auto
  define deg_diff where "deg_diff \<equiv> (\<lambda>n. n - fls_subdegree f)"
  define D where "D \<equiv> fls_subdegree ` (p_equal_fls_simplified_set p f)"
  show "finite D"
  proof (rule finite_imageD)
    show "finite (deg_diff ` D)"
    proof (rule finite_imageD)
      have "nat ` deg_diff ` D \<subseteq> {m::nat. m \<le> nat (deg_diff n)}"
        using n D_def deg_diff_def by auto
      thus "finite (nat ` deg_diff ` D)" using finite_subset by blast
      from D_def deg_diff_def show "inj_on nat (deg_diff ` D)"
        by (auto intro: inj_onI)
    qed
    from deg_diff_def show "inj_on deg_diff D" by (auto intro: inj_onI)
  qed
qed

end  (* context nontrivial_factorial_comm_ring fls *)

overloading
  p_depth_fls \<equiv>
    "p_depth :: 'a::nontrivial_factorial_comm_ring prime \<Rightarrow> 'a fls \<Rightarrow> int"
  p_depth_const \<equiv>
    "p_depth :: 'a::nontrivial_factorial_comm_ring prime \<Rightarrow> 'a \<Rightarrow> int"
begin

definition
  p_depth_fls :: "'a::nontrivial_factorial_comm_ring prime \<Rightarrow> 'a fls \<Rightarrow> int"
  where
  "p_depth_fls p f \<equiv>
    (if f \<simeq>\<^sub>p 0 then 0 else Max (fls_subdegree ` (p_equal_fls_simplified_set p f)))"

definition
  p_depth_const :: "'a::nontrivial_factorial_comm_ring prime \<Rightarrow> 'a \<Rightarrow> int"
  where
  "p_depth_const p c \<equiv> p_depth p (fls_const c)"

end  (* overloading *)

context
  fixes p :: "'a::nontrivial_factorial_comm_ring prime"
begin

lemma p_depth_fls_eqI:
  "f\<degree>\<^sup>p = fls_subdegree g"
  if  "f \<not>\<simeq>\<^sub>p 0" and "f \<simeq>\<^sub>p g"
  and "\<And>h. f \<simeq>\<^sub>p h \<Longrightarrow> fls_subdegree h \<le> fls_subdegree g"
  for f g :: "'a fls"
proof-
  define M where "M \<equiv> Max (fls_subdegree ` (p_equal_fls_simplified_set p f))"
  with that have "M = fls_subdegree g"
    using p_equal_fls_simplifed_finite
    by    (force intro: Max_eqI simp add: p_equal_fls_refl)
  with that(1) M_def show ?thesis by (auto simp add: p_depth_fls_def)
qed

lemma p_depth_fls_p_equal0[simp]:
  "(f\<degree>\<^sup>p) = 0" if "f \<simeq>\<^sub>p 0" for f :: "'a fls"
  using that by (simp add: p_depth_fls_def)

lemma p_depth_fls0[simp]: "(0::'a fls)\<degree>\<^sup>p = 0"
  by (simp add: p_depth_fls_def p_equal_fls_refl)

lemma p_depth_fls_n0D:
  "f\<degree>\<^sup>p = Max (fls_subdegree ` (p_equal_fls_simplified_set p f))"
  if  "f \<not>\<simeq>\<^sub>p 0"
  for f :: "'a fls"
  using that by (simp add: p_depth_fls_def)

lemma p_depth_flsE:
  fixes   f :: "'a fls"
  assumes "f \<not>\<simeq>\<^sub>p 0"
  obtains g where "f \<simeq>\<^sub>p g" and "fls_subdegree g = (f\<degree>\<^sup>p)"
  and "\<forall>h. f \<simeq>\<^sub>p h \<longrightarrow> fls_subdegree h \<le> fls_subdegree g"
proof-
  define M where "M \<equiv> Max (fls_subdegree ` (p_equal_fls_simplified_set p f))"
  with assms have "M \<in> fls_subdegree ` (p_equal_fls_simplified_set p f)"
    using p_equal_fls_simplifed_finite[of p f] p_equal_fls_simplifed_nempty[of p f] by simp
  from this obtain g where g: "g \<in> p_equal_fls_simplified_set p f" "M = fls_subdegree g" by fast
  from g(1) have "f \<simeq>\<^sub>p g" by blast
  moreover from g(2) M_def assms have 2: "fls_subdegree g = (f\<degree>\<^sup>p)"
    by (fastforce simp add: p_depth_fls_def)
  moreover have
    "\<forall>h. f \<simeq>\<^sub>p h \<longrightarrow> fls_subdegree h \<le> fls_subdegree g"
  proof clarify
    fix h assume "f \<simeq>\<^sub>p h" show "fls_subdegree h \<le> fls_subdegree g"
    proof (cases "fls_subdegree h \<ge> fls_subdegree f")
      case True with assms \<open>f \<simeq>\<^sub>p h\<close> M_def g show ?thesis
        using p_equal_fls_simplifed_finite by force
    next
      case False
      moreover from assms M_def g have "fls_subdegree f \<le> fls_subdegree g"
        using p_equal_fls_simplifed_finite by blast
      ultimately show ?thesis by simp
    qed
  qed
  ultimately show thesis using that by simp
qed

lemma p_depth_fls_ge_p_equal_subdegree:
  "(f\<degree>\<^sup>p) \<ge> fls_subdegree g"
  if  "f \<not>\<simeq>\<^sub>p 0" and "f \<simeq>\<^sub>p g"
  for f g :: "'a fls"
proof (cases "fls_subdegree g \<ge> fls_subdegree f")
  case True with that show ?thesis
    using p_equal_fls_simplifed_finite by (fastforce simp add: p_depth_fls_def)
next
  case False
  moreover from that(1) have "fls_subdegree f \<le> (f\<degree>\<^sup>p)"
    using p_equal_fls_simplifed_finite by (fastforce simp add: p_equal_fls_refl p_depth_fls_def)
  ultimately show ?thesis by simp
qed

lemma p_depth_fls_ge_p_equal_subdegree':
  "(f\<degree>\<^sup>p) \<ge> fls_subdegree f" if  "f \<not>\<simeq>\<^sub>p 0" for f g :: "'a fls"
  using that p_depth_fls_ge_p_equal_subdegree p_equal_fls_refl by blast

lemma p_equal_fls_simplified_set_shift:
  "p_equal_fls_simplified_set p (fls_shift n f) = fls_shift n ` p_equal_fls_simplified_set p f"
  if  "f \<not>\<simeq>\<^sub>p 0"
  for f :: "'a fls"
proof-
  have *:
    "\<And>f n. (f::'a fls) \<not>\<simeq>\<^sub>p 0 \<Longrightarrow>
      fls_shift n ` p_equal_fls_simplified_set p f \<subseteq>
        p_equal_fls_simplified_set p (fls_shift n f)"
  proof (intro subsetI, clarify)
    fix n ::int
    and f g :: "'a fls"
    assume f_neq_0: "f \<not>\<simeq>\<^sub>p 0"
      and  eq     : "f \<simeq>\<^sub>p g"
      and  deg    : "fls_subdegree f \<le> fls_subdegree g"
    from f_neq_0 eq have "f \<noteq> 0" "g \<noteq> 0" using p_equal_fls_refl by auto
    with deg have  "fls_subdegree (fls_shift n f) \<le> fls_subdegree (fls_shift n g)" by simp
    moreover from eq have "(fls_shift n f) \<simeq>\<^sub>p (fls_shift n g)"
      using p_equal_fls_shift_iff by fast
    ultimately show
      "(fls_shift n f) \<simeq>\<^sub>p (fls_shift n g) \<and>
        fls_subdegree (fls_shift n f) \<le> fls_subdegree (fls_shift n g)"
      by fast
  qed
  have "f \<simeq>\<^sub>p 0 \<longleftrightarrow> (fls_shift n f) \<simeq>\<^sub>p 0"
    using p_equal_fls_shift_iff[of p f 0] by simp
  with that have
    "p_equal_fls_simplified_set p (fls_shift n f) \<subseteq>
        fls_shift n ` p_equal_fls_simplified_set p f"
    using *[of "fls_shift n f" "-n"] by force
  with that show
    "p_equal_fls_simplified_set p (fls_shift n f) = fls_shift n ` p_equal_fls_simplified_set p f"
    using *[of f n] by fast
qed

lemma p_equal_fls_simplified_set_shift_subdegrees:
  "fls_subdegree ` p_equal_fls_simplified_set p (fls_shift n f) =
    (\<lambda>x. x - n) ` fls_subdegree ` p_equal_fls_simplified_set p f"
  if  "f \<not>\<simeq>\<^sub>p 0"
  for f :: "'a fls"
proof-
  from that have
    "fls_subdegree ` p_equal_fls_simplified_set p (fls_shift n f) =
      fls_subdegree ` fls_shift n ` p_equal_fls_simplified_set p f"
    using p_equal_fls_simplified_set_shift by fast
  moreover from that have "\<forall>g\<in>p_equal_fls_simplified_set p f. g \<noteq> 0" by auto
  ultimately show ?thesis by force
qed

lemma p_depth_fls_shift:
  "(fls_shift n f)\<degree>\<^sup>p = (f\<degree>\<^sup>p) - n" if "f \<not>\<simeq>\<^sub>p 0"
  for f :: "'a fls"
proof-
  from that have sf_nequiv_0: "(fls_shift n f) \<not>\<simeq>\<^sub>p 0"
    using p_equal_fls_shift_iff by fastforce
  with that have
    "(fls_shift n f)\<degree>\<^sup>p =
      Max ((\<lambda>x. x - n) ` fls_subdegree ` p_equal_fls_simplified_set p f)"
    using p_depth_fls_n0D p_equal_fls_simplified_set_shift_subdegrees
    by    fastforce
  thus ?thesis
    using p_equal_fls_simplifed_finite[OF that] p_equal_fls_simplifed_nempty
          p_depth_fls_n0D[OF that]
          Max_add_commute[of
            "fls_subdegree ` p_equal_fls_simplified_set p f"
            "\<lambda>x. x"
            "-n"
          ]
    by    auto
qed

end (* context factorial_comm_ring_1 *)

context
  fixes p :: "'a::nontrivial_factorial_idom prime"
  and   f g :: "'a fls"
begin

lemma p_depth_fls_p_equal: "(f\<degree>\<^sup>p) = (g\<degree>\<^sup>p)" if "f \<simeq>\<^sub>p g"
proof (cases "f \<simeq>\<^sub>p 0")
  case True with that show ?thesis using p_equality_fls.trans0_iff by fastforce
next
  case False
  with that have g: "g \<not>\<simeq>\<^sub>p 0" using p_equality_fls.trans0_iff by blast
  from this obtain h where h:
    "g \<simeq>\<^sub>p h" "fls_subdegree h = (g\<degree>\<^sup>p)"
    by (elim p_depth_flsE)
  from that h(1) have "f \<simeq>\<^sub>p h" using p_equality_fls.trans by fast
  moreover from that g h(2) have
    "\<And>h'. f \<simeq>\<^sub>p h' \<Longrightarrow> fls_subdegree h' \<le> fls_subdegree h"
    using p_equality_fls.trans_right p_depth_fls_ge_p_equal_subdegree by metis
  ultimately show ?thesis
    using False h(2) p_depth_fls_eqI by metis
qed

lemma p_depth_fls_can_simplify_iff:
  "p pdvd g $$ (fls_subdegree g) = (fls_subdegree g < (f\<degree>\<^sup>p))"
  if  f_nequiv0: "f \<not>\<simeq>\<^sub>p 0"
  and fg_equiv : "f \<simeq>\<^sub>p g"
proof
  define gdeg where "gdeg \<equiv> fls_subdegree g"
  define gth where "gth \<equiv> g $$ gdeg"
  define pp where "pp \<equiv> Rep_prime p"
  assume p_dvd: "p pdvd gth"
  from this obtain k where k: "gth = pp * k" unfolding pp_def gth_def gdeg_def by (elim dvdE)
  define h where
    "h \<equiv> g - fls_shift (-gdeg) (fls_const gth) + fls_shift (-(gdeg + 1)) (fls_const k)"
  from f_nequiv0 fg_equiv have "g \<noteq> 0" by blast
  with gth_def gdeg_def have
    "fls_subdegree (fls_shift (-gdeg) (fls_const gth) - fls_shift (-(gdeg + 1)) (fls_const k)) =
      gdeg"
    by (auto intro: fls_subdegree_eqI)
  with h_def have g_h: "fls_base_factor_to_fps (g - h) = fps_const gth - fps_const k * fps_X"
    by (auto intro: fps_ext)
  have p_g_h: "\<And>n. pp ^ Suc n dvd fls_base_parteval (g - h) pp n"
  proof-
    fix n
    from k p_dvd show "pp ^ Suc n dvd fls_base_parteval (g - h) pp n"
      using g_h by (cases n) (auto simp add: fps_parteval_mult_fps_X(1))
  qed
  with pp_def have "g \<simeq>\<^sub>p h" by (fastforce intro: p_equal_flsI fps_pvanishesI)
  moreover have "gdeg < fls_subdegree h"
  proof (intro fls_subdegree_greaterI)
    show "h \<noteq> 0"
    proof
      assume"h = 0"
      with pp_def have "g \<simeq>\<^sub>p 0"
        using p_g_h by (fastforce intro: p_equal_flsI fps_pvanishesI)
      with f_nequiv0 fg_equiv show False using p_equality_fls.trans0_iff by blast
    qed
  qed (simp add: h_def gdeg_def gth_def)
  ultimately show "gdeg < (f\<degree>\<^sup>p)"
    using gdeg_def that p_depth_fls_ge_p_equal_subdegree[of p f h]
          p_equal_fls_trans[of p f g h]
    by    force
next
  define pp where "pp \<equiv> Rep_prime p"
  assume g: "fls_subdegree g < (f\<degree>\<^sup>p)"
  with that obtain h where h: "f \<simeq>\<^sub>p h" "fls_subdegree h = (f\<degree>\<^sup>p)"
    by (elim p_depth_flsE)
  from f_nequiv0 fg_equiv have g_n0: "g \<noteq> 0" by blast
  with g h(2) have "fls_subdegree (g - h) = fls_subdegree g" by (auto intro: fls_subdegree_eqI)
  moreover from fg_equiv h(1) pp_def
    have  "pp ^ Suc 0 dvd (fps_parteval (fls_regpart (fls_base_factor (g - h))) pp 0)"
    using p_equality_fls.trans_right p_equal_flsD fps_pvanishesD
    by    blast
  ultimately show "p pdvd g $$ (fls_subdegree g)" by (simp add: pp_def g h(2))
qed

lemma p_depth_fls_rep_iff:
  "(f\<degree>\<^sup>p) = fls_subdegree g \<longleftrightarrow>
    \<not> p pdvd g $$ (fls_subdegree g)"
  if "f \<not>\<simeq>\<^sub>p 0" and "f \<simeq>\<^sub>p g"
  using that p_depth_fls_can_simplify_iff p_depth_fls_ge_p_equal_subdegree by fastforce

end (* context nontrivial_factorial_idom *)

global_interpretation p_depth_fls:
  p_equality_depth_no_zero_divisors_1
    "p_equal :: 'a::nontrivial_factorial_idom prime \<Rightarrow>
      'a fls \<Rightarrow> 'a fls \<Rightarrow> bool"
    "p_depth :: 'a prime \<Rightarrow> 'a fls \<Rightarrow> int"
proof (unfold_locales, intro notI)
  fix p :: "'a prime" and f g :: "'a fls"
  define pp where "pp \<equiv> Rep_prime p"
  assume  f_nequiv0: "f \<not>\<simeq>\<^sub>p 0"
    and   g_nequiv0: "g \<not>\<simeq>\<^sub>p 0"
    and   fg_equiv0: "(f * g) \<simeq>\<^sub>p 0"
  from f_nequiv0 obtain s_f
    where s_f: "f \<simeq>\<^sub>p s_f" "fls_subdegree s_f = (f\<degree>\<^sup>p)"
    using p_depth_flsE
    by    blast
  from g_nequiv0 obtain s_g
    where s_g: "g \<simeq>\<^sub>p s_g" "fls_subdegree s_g = (g\<degree>\<^sup>p)"
    using p_depth_flsE
    by    blast
  from s_f(1) s_g(1) fg_equiv0 have "(s_f * s_g) \<simeq>\<^sub>p 0"
    using p_equality_fls.mult p_equality_fls.trans0_iff by blast
  hence "fps_primevanishes p (fls_base_factor_to_fps (s_f * s_g))" using p_equal_flsD by fastforce
  with pp_def have "pp ^ Suc 0 dvd fls_base_parteval (s_f * s_g) pp 0"
    using fps_pvanishesD by fast
  with pp_def have "p pdvd s_f $$ (fls_subdegree s_f) * s_g $$ (fls_subdegree s_g)"
    using fls_base_factor_to_fps_mult[of s_f s_g] by fastforce
  hence
    "p pdvd s_f $$ (fls_subdegree s_f) \<or> p pdvd s_g $$ (fls_subdegree s_g)"
    using Rep_prime prime_dvd_multD by auto
  with pp_def f_nequiv0 s_f g_nequiv0 s_g show False by (metis p_depth_fls_rep_iff)
next
  fix p :: "'a prime"
  show "\<exists>x::'a fls. x \<not>\<simeq>\<^sub>p 0" using fls_1_not_p_equal_0 by auto
next
  fix p :: "'a :: nontrivial_factorial_idom prime" and f g :: "'a fls"
  assume fg_nequiv0: "(f * g) \<not>\<simeq>\<^sub>p 0"
  from fg_nequiv0
    have  f_nequiv0: "f \<not>\<simeq>\<^sub>p 0"
    and   g_nequiv0: "g \<not>\<simeq>\<^sub>p 0"
    by    (auto simp add: p_equality_fls.mult_0_left p_equality_fls.mult_0_right)
  from f_nequiv0 obtain s_f
    where s_f: "f \<simeq>\<^sub>p s_f" "fls_subdegree s_f = (f\<degree>\<^sup>p)"
    using p_depth_flsE
    by    blast
  from g_nequiv0 obtain s_g
    where s_g: "g \<simeq>\<^sub>p s_g" "fls_subdegree s_g = (g\<degree>\<^sup>p)"
    using p_depth_flsE
    by    blast
  from s_f(1) s_g(1) have equiv: "(f * g) \<simeq>\<^sub>p (s_f * s_g)"
    using p_equality_fls.mult by fast
  with fg_nequiv0 have "s_f \<noteq> 0" "s_g \<noteq> 0" by auto
  hence deg: "fls_subdegree (s_f * s_g) = fls_subdegree s_f + fls_subdegree s_g" by simp
  moreover have "(s_f * s_g)\<degree>\<^sup>p = fls_subdegree (s_f * s_g)"
  proof (rule iffD2, rule p_depth_fls_rep_iff)
    from fg_nequiv0 show "(s_f * s_g) \<not>\<simeq>\<^sub>p 0"
      using equiv p_equality_fls.trans0_iff by fast
    from s_f f_nequiv0 have "\<not> p pdvd s_f $$ (fls_subdegree s_f)"
      by (metis p_depth_fls_rep_iff)
    moreover from s_g g_nequiv0 have "\<not> p pdvd s_g $$ (fls_subdegree s_g)"
      by (metis p_depth_fls_rep_iff)
    moreover have
      "(s_f * s_g) $$ (fls_subdegree (s_f * s_g)) =
        s_f $$ (fls_subdegree s_f) *
        s_g $$ (fls_subdegree s_g)"
      using deg by simp
    ultimately show "\<not> p pdvd (s_f * s_g) $$ (fls_subdegree (s_f * s_g))"
      using Rep_prime prime_dvd_multD by auto
  qed simp
  ultimately show "(f * g)\<degree>\<^sup>p = (f\<degree>\<^sup>p) + (g\<degree>\<^sup>p)"
    using s_f(2) s_g(2) equiv p_depth_fls_p_equal by metis
next
  fix p :: "'a prime" and f :: "'a fls"
  show "(-f\<degree>\<^sup>p) = (f\<degree>\<^sup>p)"
  proof (cases "f \<simeq>\<^sub>p 0")
    case True thus ?thesis using p_equality_fls.uminus[of p f 0] by simp
  next
    case False
    moreover from this obtain h
      where "f \<simeq>\<^sub>p h"
      and   "fls_subdegree h = (f\<degree>\<^sup>p)"
      by    (elim p_depth_flsE)
    ultimately show "(- f)\<degree>\<^sup>p = (f\<degree>\<^sup>p)"
      using p_depth_fls_rep_iff p_equality_fls.uminus[of p f h] p_equality_fls.uminus[of p "-f" 0]
            p_depth_fls_rep_iff
      by    fastforce
  qed
next
  fix p :: "'a prime" and f g :: "'a fls"
  assume f: "f \<not>\<simeq>\<^sub>p 0" and d_f_g: "(f\<degree>\<^sup>p) < (g\<degree>\<^sup>p)"
  show  "((f + g)\<degree>\<^sup>p) = (f\<degree>\<^sup>p)"
  proof (cases "g \<simeq>\<^sub>p 0")
    case True thus ?thesis using p_equality_fls.add_0_right[of p g f] p_depth_fls_p_equal by auto
  next
    case False
    from f obtain s_f
      where s_f: "f \<simeq>\<^sub>p s_f" "fls_subdegree s_f = (f\<degree>\<^sup>p)"
      using p_depth_flsE
      by    blast
    from False obtain s_g
      where s_g: "g \<simeq>\<^sub>p s_g" "fls_subdegree s_g = (g\<degree>\<^sup>p)"
      using p_depth_flsE
      by    blast
    from f d_f_g s_f s_g(2) have deg: "fls_subdegree (s_f + s_g) = fls_subdegree s_f"
      using nth_fls_subdegree_zero_iff[of s_f] by (auto intro: fls_subdegree_eqI)
    from s_f s_g have "(f + g) \<simeq>\<^sub>p (s_f + s_g)"
      using p_equality_fls.add by blast
    moreover from s_f s_g(2) f d_f_g
      have  *: "\<not> p pdvd (s_f + s_g) $$ (fls_subdegree (s_f + s_g))"
      using deg p_depth_fls_rep_iff
      by    fastforce
    moreover have "(f + g) \<not>\<simeq>\<^sub>p 0"
    proof
      define pp where "pp \<equiv> Rep_prime p"
      assume "(f + g) \<simeq>\<^sub>p 0"
      with s_f(1) s_g(1) have f_g: "(s_f + s_g) \<simeq>\<^sub>p 0"
        by (meson p_equality_fls.add p_equality_fls.trans_right)
      with pp_def have "pp ^ Suc 0 dvd fls_base_parteval (s_f + s_g) pp 0"
        using p_equal_flsD[of p _ 0] fps_pvanishesD[of pp _ 0] by fastforce
      with pp_def show False using * by simp
    qed
    ultimately have "(f + g)\<degree>\<^sup>p = fls_subdegree (s_f + s_g)"
      using p_depth_fls_rep_iff by blast
    with s_f(2) show ?thesis using deg by auto
  qed
next
  fix p :: "'a prime" and f g :: "'a fls"
  assume  f    : "f \<not>\<simeq>\<^sub>p 0"
    and   fg   : "f + g \<not>\<simeq>\<^sub>p 0"
    and   d_f_g: "(f\<degree>\<^sup>p) = (g\<degree>\<^sup>p)"
  show "(f\<degree>\<^sup>p) \<le> ((f + g)\<degree>\<^sup>p)"
  proof (cases "g \<simeq>\<^sub>p 0")
    case True thus ?thesis
      using p_equality_fls.add_0_right[of p g f] p_depth_fls_p_equal[of p] by presburger
  next
    case False
    from f obtain s_f
      where s_f: "f \<simeq>\<^sub>p s_f" "fls_subdegree s_f = (f\<degree>\<^sup>p)"
      using p_depth_flsE
      by    blast
    from False obtain s_g
      where s_g: "g \<simeq>\<^sub>p s_g" "fls_subdegree s_g = (g\<degree>\<^sup>p)"
      using p_depth_flsE
      by    blast
    from s_f s_g have "(f + g) \<simeq>\<^sub>p (s_f + s_g)"
      using p_equality_fls.add by fast
    moreover from this fg d_f_g s_f(2) s_g(2)
      have  "fls_subdegree (s_f + s_g) \<ge> fls_subdegree s_f"
      by    (force intro: fls_subdegree_geI)
    ultimately show ?thesis
      using fg s_f(2) p_depth_fls_ge_p_equal_subdegree by fastforce
  qed
qed (simp, rule p_depth_fls_p_equal)

context
  fixes p :: "'a::nontrivial_factorial_idom prime"
begin

lemma p_depth_fls1[simp]: "(1::'a fls)\<degree>\<^sup>p = 0"
  by (rule FLS_Prime_Equiv_Depth.p_depth_fls.depth_of_1)

lemma p_depth_fls_X: "(fls_X::'a fls)\<degree>\<^sup>p = 1"
  using fls_1_not_p_equal_0 p_equal_fls_shift_iff[of p "fls_X::'a fls" 0 1]
        p_depth_fls_shift[of p _ 1]
  by    fastforce

lemma p_depth_fls_X_inv: "(fls_X_inv::'a fls)\<degree>\<^sup>p = -1"
  by (metis fls_1_not_p_equal_0 fls_X_inv_conv_shift_1 p_depth_fls_shift p_depth_fls1 diff_0)

lemma p_depth_fls_X_intpow: "((fls_X_intpow n)::'a fls)\<degree>\<^sup>p = n"
    using p_depth_fls_shift[of p] fls_1_not_p_equal_0 by fastforce

lemma p_depth_const:
  "c\<degree>\<^sup>p = pmultiplicity p c" for c :: 'a
proof (cases "c = 0")
  define pp where "pp \<equiv> Rep_prime p"
  case False
  moreover from pp_def have "\<not>is_unit pp" using Rep_prime_not_unit by simp
  ultimately obtain k where k: "c = pp ^ pmultiplicity p c * k" "\<not> p pdvd k"
    unfolding pp_def by (elim multiplicity_decompose')
  from k(2) have k_n0: "fls_const k \<noteq> 0" using fls_const_nonzero[of k] by blast
  define g and S
    where "g \<equiv> fls_shift (- pmultiplicity p c) (fls_const k)"
    and   "S \<equiv> fls_base_parteval (fls_const c - g) pp"
  have "\<And>n. pp ^ Suc n dvd S n"
  proof-
    fix n show "pp ^ Suc n dvd S n"
    proof (cases "n < pmultiplicity p c")
      case True
      with False pp_def S_def g_def k show ?thesis
        using k_n0 fps_parteval_fls_base_factor_to_fps_diff[of "fls_const c" n g pp]
              fls_const_nonzero[of c] dvd_power_le[of pp pp "Suc n" "multiplicity pp c"]
        by    force
    next
      case False
      from k(1) g_def have "fls_subdegree (fls_const c - g) = 0"
        by (cases "pmultiplicity p c = 0") (auto intro: fls_subdegree_eqI)
      with g_def False S_def k(1) show ?thesis
        using fls_times_conv_regpart[of "fls_X ^ (pmultiplicity p c)" "fls_const k"]
              fps_parteval_mult_fps_X_power(2)[of "pmultiplicity p c" n "fps_const k"]
        by    (simp add: fls_X_power_times_conv_shift(1) fls_X_pow_conv_fps_X_pow)
    qed
  qed
  with S_def have "fls_const c \<simeq>\<^sub>p g" using pp_def p_equal_flsI fps_pvanishesI by blast
  moreover from g_def pp_def k(2) have "\<not> p pdvd g $$ (fls_subdegree g)" using k_n0 by simp
  moreover from False have "fls_const c \<not>\<simeq>\<^sub>p 0"
    using p_equal_fls_const_0_iff by meson
  ultimately have "c\<degree>\<^sup>p = fls_subdegree g"
    by (metis p_depth_const_def  p_depth_fls_rep_iff)
  with g_def pp_def show ?thesis using k_n0 by simp
qed (simp add: p_depth_const_def)

lemma p_depth_prime_const: "(Rep_prime p)\<degree>\<^sup>p = 1"
  using Rep_prime[of p] p_depth_const by simp

end (* context factorial_idom *)


subsection \<open>Reduction relative to a prime\<close>

subsubsection \<open>Of scalars\<close>

class nontrivial_euclidean_ring_cancel = nontrivial_factorial_comm_ring + euclidean_semiring_cancel
begin
subclass nontrivial_factorial_idom ..
subclass euclidean_ring_cancel ..
end

instance int :: nontrivial_euclidean_ring_cancel ..

abbreviation pdiv ::
  "'a \<Rightarrow> 'a::nontrivial_euclidean_ring_cancel prime \<Rightarrow> 'a" (infix "pdiv" 70)
  where "a pdiv p \<equiv> a div (Rep_prime p)"

consts p_modulo :: "'a \<Rightarrow> 'b prime \<Rightarrow> 'a" (infixl "pmod" 70)

overloading p_modulo_scalar \<equiv> "p_modulo :: 'a \<Rightarrow> 'a prime \<Rightarrow> 'a"
begin
definition p_modulo_scalar ::
  "'a::nontrivial_euclidean_ring_cancel \<Rightarrow> 'a prime \<Rightarrow> 'a"
  where p_modulo_scalar_def[simp]: "p_modulo_scalar a p \<equiv> a mod (Rep_prime p)"
end

class nontrivial_unique_euclidean_ring = nontrivial_factorial_comm_ring + unique_euclidean_semiring
  + assumes division_segment_prime: "prime p \<Longrightarrow> division_segment p = 1"
begin
subclass nontrivial_euclidean_ring_cancel ..
end

instance int :: nontrivial_unique_euclidean_ring
proof
  fix p::int assume p: "prime p"
  hence "\<not> p < 0" using normalize_prime[of p] by force
  thus "division_segment p = 1" using division_segment_int_def by fastforce
qed

lemma division_segment_1: "division_segment (1::'a::unique_euclidean_semiring) = 1"
proof-
  have "is_unit (division_segment (1::'a))" by force
  from this obtain k where "1 = division_segment (1::'a) * k" by blast
  moreover have "division_segment (1::'a) = division_segment 1 * division_segment 1"
    using division_segment_mult[of 1 1] by force
  ultimately show "division_segment (1::'a) = 1"
    using mult.assoc mult_1_right by metis
qed

lemma one_pdiv: "(1::'a) pdiv p = 0"
  and one_pmod: "(1::'a) pmod p = 1"
  for p :: "'a::nontrivial_unique_euclidean_ring prime"
proof-
  define pp where "pp \<equiv> Rep_prime p"
  have "((1::'a) pdiv p, 1 pmod p) = (0, (1::'a))"
    unfolding p_modulo_scalar_def
  proof (intro euclidean_relationI)
    show "is_unit (Rep_prime p) \<Longrightarrow> 1 = 0 \<and> 1 = 0 * Rep_prime p"
      using Rep_prime[of p] by auto
    from pp_def have "division_segment (1::'a) = division_segment pp"
      using Rep_prime division_segment_1 division_segment_prime[of pp] by force
    moreover from pp_def have "euclidean_size (1::'a) < euclidean_size (pp * (1::'a))"
      using Rep_prime_n0 Rep_prime_not_unit euclidean_size_times_nonunit[of pp "1::'a"] by auto
    ultimately show
      "division_segment (1::'a) = division_segment (Rep_prime p) \<and>
        euclidean_size (1::'a) < euclidean_size (Rep_prime p) \<and>
        1 = 0 * Rep_prime p + 1"
      using pp_def by auto
  qed (simp_all add: Rep_prime_n0)
  thus "(1::'a) pdiv p = 0" and "(1::'a) pmod p = 1" by auto
qed

subsubsection \<open>Inductive partial reduction of formal Laurent series\<close>

text \<open>
  This inductive function reduces one term at a time.
  The @{type nat} argument specifies how far beyond the subdegree to reduce,
  so that all terms to @{emph \<open>one less\<close>} than the @{type nat} argument
  beyond the subdegree are reduced,
  and the term at the @{type nat} argument beyond the subdegree is updated
  to include the carry.
\<close>
primrec fls_partially_p_modulo_rep ::
  "'a::nontrivial_euclidean_ring_cancel fls \<Rightarrow>
    nat \<Rightarrow> 'a prime \<Rightarrow> (int \<Rightarrow> 'a)"
  where "fls_partially_p_modulo_rep f 0 p = ($$) f" |
  "fls_partially_p_modulo_rep f (Suc N) p =
    (fls_partially_p_modulo_rep f N p)(
      fls_subdegree f + int N :=
        (fls_partially_p_modulo_rep f N p (fls_subdegree f + int N)) pmod p,
      fls_subdegree f + int N + 1 :=
        f $$ (fls_subdegree f + int N + 1) +
        (fls_partially_p_modulo_rep f N p (fls_subdegree f + int N)) pdiv p
    )"

lemma fls_partially_p_modulo_rep_zero[simp]:
  "fls_partially_p_modulo_rep 0 N p n = 0"
proof-
  have "\<forall>n. fls_partially_p_modulo_rep 0 N p n = 0" by (induct N) auto
  thus ?thesis by blast
qed

lemma fls_partially_p_modulo_rep_zeros_below:
  "fls_partially_p_modulo_rep f N p n = 0" if "n < fls_subdegree f"
  using that by (induct N) simp_all

lemma fls_partially_p_modulo_rep_func_lower_bound:
  "\<forall>n<fls_subdegree f. fls_partially_p_modulo_rep f (nat (n + 1 - fls_subdegree f)) p n = 0"
  by simp

lemma fls_partially_p_modulo_rep_agrees:
  "fls_partially_p_modulo_rep f N p n = fls_partially_p_modulo_rep f M p n"
  if "n \<le> fls_subdegree f + int N - 1" and "M \<ge> N"
proof-
  have *:
    "\<And>K. fls_partially_p_modulo_rep f N p n = fls_partially_p_modulo_rep f (N + K) p n"
  proof-
    fix K from that(1) show
      "fls_partially_p_modulo_rep f N p n = fls_partially_p_modulo_rep f (N + K) p n"
      by (induct K) auto
  qed
  from that(2) show ?thesis using *[of "M - N"] by simp
qed

lemma fls_partially_p_modulo_rep_func_partially:
  "n > fls_subdegree f + int N \<Longrightarrow> fls_partially_p_modulo_rep f N p n = f $$ n"
  by (induct N, simp_all)

lemma fls_partially_p_modulo_rep_cong:
  "fls_partially_p_modulo_rep f N p n = fls_partially_p_modulo_rep g N p n"
  if "fls_subdegree f = fls_subdegree g" and "\<forall>k\<le>n. f $$ k = g $$ k"
proof-
  have
    "\<forall>k\<le>n. fls_partially_p_modulo_rep f N p k = fls_partially_p_modulo_rep g N p k"
  proof (induct N, safe)
    case (Suc N)
    fix k assume "k \<le> n"
    moreover consider
      "k = fls_subdegree f + int N" | "k = fls_subdegree f + int N + 1" |
      "k < fls_subdegree f + int N" | "k > fls_subdegree f + int N + 1"
      by fastforce
    ultimately
      show  "fls_partially_p_modulo_rep f (Suc N) p k = fls_partially_p_modulo_rep g (Suc N) p k"
      by    cases (auto simp add: that Suc)
  qed (simp add: that(2))
  thus ?thesis by auto
qed

lemma fls_partially_reduced_nth_vs_rep:
  "N \<le> n + 1 - fls_subdegree f \<Longrightarrow> fls_partially_p_modulo_rep f N p = ($$) f"
  if "\<forall>k\<le>n. (f $$ k) pdiv p = 0"
proof (induct N)
  case (Suc N) thus "fls_partially_p_modulo_rep f (Suc N) p = ($$) f"
    using that Suc div_mult_mod_eq[of "f $$ (fls_subdegree f + int N)" "Rep_prime p"] by simp
qed simp

lemma fls_partially_p_modulo_rep_carry:
  "(\<Sum>k=fls_subdegree f..N.
    (f$$k - fls_partially_p_modulo_rep f (nat (N - fls_subdegree f)) p k) *
      (Rep_prime p) ^ nat (k - fls_subdegree f)) = 0"
proof (cases "N \<ge> fls_subdegree f", induct N rule: int_ge_induct)
  case (step N)
  define pp and d :: "'a fls \<Rightarrow> int" and fpmod_rep
    where "pp \<equiv> Rep_prime p" and "d \<equiv> fls_subdegree"
    and   "fpmod_rep \<equiv> (\<lambda>n. fls_partially_p_modulo_rep f n p)"
  define S where
    "S \<equiv>
      (\<Sum>k=d(f)..N+1. (f$$k - fpmod_rep (nat (N + 1 - d(f))) k) * pp ^ nat (k - d(f)))"
  from d_def step(1) have natN: "nat (N + 1 - d(f)) = Suc (nat (N - d(f)))"
    by (simp add: Suc_nat_eq_nat_zadd1)
  from d_def step(1) have "{d(f)..N + 1} = insert (N+1) (insert N {d(f)..N-1})" by auto
  moreover from d_def fpmod_rep_def step(1) have
    "\<forall>k\<le>N-1. fpmod_rep (nat (N + 1 - d(f))) k = fpmod_rep (nat (N - d(f))) k"
    using fls_partially_p_modulo_rep_agrees[of _ f "nat (N - d(f))" "nat (N + 1 - d(f))"]
    by    simp
  ultimately have
    "S =
      (f$$N - ((fpmod_rep (nat (N - d(f))) N pdiv p) * pp + (fpmod_rep (nat (N - d(f))) N) pmod p))
      * pp ^ nat (N - d(f)) +
      (\<Sum>k\<in>{d(f)..N-1}. (f$$k - fpmod_rep (nat (N - d(f))) k) * pp ^ nat (k - d(f)))"
    using d_def fpmod_rep_def S_def step(1) natN
    by    (simp add: algebra_simps)
  moreover from d_def step(1) have df_to_N: "{d(f)..N} = insert N {d(f)..N-1}" by fastforce
  ultimately have
    "S = (\<Sum>k\<in>{d(f)..N}. (f$$k - fpmod_rep (nat (N - d(f))) k) * pp ^ nat (k - d(f)))"
    using pp_def S_def by (simp add: algebra_simps)
  with pp_def d_def fpmod_rep_def S_def show ?case using step(2) by presburger
qed simp_all

subsubsection \<open>Full reduction of formal Laurent series\<close>

text \<open>Now we collect the reduced terms into a formal Laurent series.\<close>

overloading p_modulo_fls \<equiv> "p_modulo :: 'a fls \<Rightarrow> 'a prime \<Rightarrow> 'a fls"
begin
definition p_modulo_fls ::
  "'a::nontrivial_euclidean_ring_cancel fls \<Rightarrow> 'a prime \<Rightarrow> 'a fls"
  where
    "p_modulo_fls f p \<equiv>
      Abs_fls (\<lambda>n. fls_partially_p_modulo_rep f (nat (n + 1 - fls_subdegree f)) p n)"
end

lemma p_modulo_fls_nth:
  "(f pmod p) $$ n = fls_partially_p_modulo_rep f (nat (n + 1 - fls_subdegree f)) p n"
  using     nth_Abs_fls_lower_bound fls_partially_p_modulo_rep_func_lower_bound
  unfolding p_modulo_fls_def
  by        meson

lemma p_modulo_fls_nth':
  "int N \<ge> n + 1 - fls_subdegree f \<Longrightarrow>
    (f pmod p) $$ n = fls_partially_p_modulo_rep f N p n"
proof (induct N)
  case (Suc N) thus ?case
    by (cases "int (Suc N) = n + 1 - fls_subdegree f", metis p_modulo_fls_nth nat_int, force)
qed (simp add: p_modulo_fls_nth)

context
  fixes p :: "'a::nontrivial_euclidean_ring_cancel prime"
begin

lemma fls_pmod_reduced[simp]: "((f pmod p) $$ n) pdiv p = 0"
  using fls_partially_p_modulo_rep.simps(2)[of f "nat (n - fls_subdegree f)" p]
  by (
    cases n "fls_subdegree f - 1" rule: linorder_cases,
    simp_all add: p_modulo_fls_nth Suc_nat_eq_nat_zadd1 algebra_simps
  )

lemma fls_pmod_pmod_nth[simp]: "((f pmod p) $$ n) pmod p = (f pmod p) $$ n" for f :: "'a fls"
  using div_mult_mod_eq[of "(f pmod p) $$ n" "Rep_prime p"] by auto

lemma fls_pmod_carry:
  "(\<Sum>k=fls_subdegree f..N. (f - (f pmod p)) $$ k * (Rep_prime p) ^ nat (k - fls_subdegree f)) =
    (fls_partially_p_modulo_rep f (nat (N + 1 - fls_subdegree f)) p (N + 1) - f $$ (N + 1)) *
    (Rep_prime p) ^ nat (N + 1 - fls_subdegree f)"
proof (cases "N \<ge> fls_subdegree f - 1")
  case True
  define d :: "'a fls \<Rightarrow> int" and fpmod_rep
    where "d \<equiv> fls_subdegree"
    and   "fpmod_rep \<equiv> (\<lambda>n. fls_partially_p_modulo_rep f n p)"
  from d_def True have "{d(f)..N + 1} = insert (N+1) {d(f)..N}" by auto
  moreover from d_def fpmod_rep_def True
    have  "\<forall>k\<le>N. fpmod_rep (nat (N + 1 - d(f))) k = (f pmod p) $$ k"
    using p_modulo_fls_nth'[of _ f "nat (N + 1 - d(f))"]
    by    force
  ultimately show ?thesis
    using d_def fpmod_rep_def fls_partially_p_modulo_rep_carry[of f "N + 1" p]
    by    (simp add: algebra_simps)
qed simp

lemma fls_pmod_carry':
  "(\<Sum>k=fls_subdegree f..N. (f - (f pmod p)) $$ k * (Rep_prime p) ^ nat (k - fls_subdegree f)) =
    (fls_partially_p_modulo_rep f (nat (N - fls_subdegree f)) p N pdiv p) *
      (Rep_prime p) ^ Suc (nat (N - fls_subdegree f))"
  if "N \<ge> fls_subdegree f"
  using that fls_pmod_carry[of f N]
        fls_partially_p_modulo_rep.simps(2)[of f "nat (N - fls_subdegree f)" p]
  by    (simp add: algebra_simps Suc_nat_eq_nat_zadd1)

lemma fls_p_reduced_is_zero_iff:
  "f = 0 \<longleftrightarrow> f \<simeq>\<^sub>p 0 \<and> (\<forall>n. f$$n pdiv p = 0)"
  for f :: "'a fls"
proof (standard, safe)
  assume f_0: "f \<simeq>\<^sub>p 0" and f_reduced: "\<forall>n. f$$n pdiv p = 0"
  define pp and d :: "'a fls \<Rightarrow> int"
    where "pp \<equiv> Rep_prime p" and "d \<equiv> fls_subdegree"
  show "f = 0"
  proof (intro fls_eqI)
    fix n have "\<forall>k\<le>n. f$$k = 0"
    proof (cases "n \<ge> d(f) - 1", induct n rule: int_ge_induct, safe)
      case (step n)
      fix k assume k: "k \<le> n + 1"
      define S where "S \<equiv> (\<Sum>k=d(f)..n + 1. f $$ k * pp ^ nat (k - d(f)))"
      with f_0 d_def pp_def step(1) have "pp ^ Suc (nat (n + 1 - d f)) dvd S"
        using fls_p_equal0_extended_intsum_iff[of _ f] by fastforce
      from this obtain T where T: "S = pp ^ Suc (nat (n + 1 - d f)) * T" by (elim dvdE)
      from step(1) have "{d(f)..n + 1} = insert (n + 1) {d(f)..n}" by fastforce
      with S_def pp_def step(2)
        have "S = ((f$$(n+1) pdiv p) * pp + f$$(n+1) pmod p) * pp ^ nat (n + 1 - d(f))"
        by   force
      moreover from f_reduced have "f$$(n+1) pdiv p = 0" by blast
      ultimately have "f$$(n + 1) = 0"
        using pp_def T Rep_prime_n0[of p] dvd_imp_mod_0[of pp] mod_mod_trivial[of "f$$(n + 1)" pp]
        by    force
      with k step(2) show "f $$ k = 0" by (cases "k = n + 1") auto
    qed (simp_all add: d_def)
    thus "f $$ n = 0 $$ n" by auto
  qed
qed simp_all

lemma p_modulo_fls_eq0[simp]:
  "f pmod p = 0" if "f \<simeq>\<^sub>p 0" for f :: "'a fls"
proof-
  define d :: "'a fls \<Rightarrow> int" and fpmod_rep
    where "d \<equiv> fls_subdegree"
    and   "fpmod_rep \<equiv> (\<lambda>n. fls_partially_p_modulo_rep f n p)"
  have "\<forall>n. \<forall>k\<le>n. (f pmod p) $$ k = 0"
  proof
    fix n show "\<forall>k\<le>n. (f pmod p) $$ k = 0"
    proof (cases "n \<ge> d(f)", induct n rule: int_ge_induct, safe)
      case base fix k assume k: "k \<le> d(f)"
      show "(f pmod p) $$ k = 0"
      proof (cases "k = d(f)")
        case True
        with that d_def show ?thesis
          using fls_p_equal0_extended_intsum_iff[of _ f] p_modulo_fls_nth[of f] by fastforce
      next
        case False with k d_def show ?thesis by (simp add: p_modulo_fls_nth)
      qed
    next
      case (step n)
      fix k assume k: "k \<le> n + 1"
      define pp where "pp \<equiv> Rep_prime p"
      define S where "S \<equiv> (\<Sum>k=d(f)..n + 1. f $$ k * pp ^ nat (k - d(f)))"
      with that d_def pp_def step(1) have "pp ^ Suc (nat (n + 1 - d f)) dvd S"
        using fls_p_equal0_extended_intsum_iff[of _ f] by fastforce
      from this obtain T where T: "S = pp ^ Suc (nat (n + 1 - d f)) * T" by (elim dvdE)
      moreover from step(1) have "{d(f)..n + 1} = insert (n + 1) {d(f)..n}" by fastforce
      ultimately have
        "(f pmod p) $$ (n+1) * pp ^ nat (n + 1 - d(f)) =
          (T - fpmod_rep (nat (n + 1 - d(f))) (n + 1) pdiv p) * pp * pp ^ nat (n + 1 - d(f))"
        using d_def fpmod_rep_def pp_def S_def step fls_pmod_carry'[of f "n + 1"]
        by (simp add: algebra_simps)
      with pp_def have "(f pmod p) $$ (n+1) = 0"
        using Rep_prime_n0[of p] dvd_mult_cancel_right fls_pmod_reduced[of f "n + 1"] by simp
      with k step(2) show "(f pmod p) $$ k = 0" by (cases "k = n + 1") auto
    qed (simp add: d_def p_modulo_fls_nth)
  qed
  thus "f pmod p = 0" using fls_eqI[of "f pmod p" 0] by auto
qed

lemma fls_pmod_eq0_iff:
  "f pmod p = 0 \<longleftrightarrow> f \<simeq>\<^sub>p 0" for f :: "'a fls"
proof (standard, rule iffD2, rule fls_p_equal0_extended_intsum_iff, safe)
  define pp and d :: "'a fls \<Rightarrow> int"
    where "pp \<equiv> Rep_prime p" and "d \<equiv> fls_subdegree"
  show "d(f) \<le> d(f)" by blast
  fix n assume "f pmod p = 0" and "n \<ge> d(f)"
  with pp_def d_def
    show  "pp ^ Suc (nat (n - d(f))) dvd (\<Sum>k=d(f)..n. f $$ k * pp ^ nat (k - d(f)))"
    using fls_pmod_carry'
    by    force
qed simp

lemma fls_pmod_equiv: "f \<simeq>\<^sub>p f pmod p" for f :: "'a fls"
proof (cases "f pmod p = 0")
  case True thus ?thesis using fls_pmod_eq0_iff by simp
next
  case False show ?thesis
  proof (rule iffD2, rule p_equal_fls_extended_intsum_iff, safe)
    define pp and d :: "'a fls \<Rightarrow> int"
      where "pp \<equiv> Rep_prime p" and "d \<equiv> fls_subdegree"
    from False d_def have "d(f) \<le> d(f pmod p)"
      by (auto intro: fls_subdegree_geI simp add: p_modulo_fls_nth)
    thus "d(f) \<le> min (d(f)) (d(f pmod p))" by fastforce
    fix n assume "n \<ge> d(f)"
    with d_def pp_def show
      "pp ^ Suc (nat (n - d(f))) dvd (\<Sum>k=d(f)..n. (f - f pmod p) $$ k * pp ^ nat (k - d(f)))"
      using fls_pmod_carry'[of f] by auto
  qed
qed

lemma fls_p_reduced_subdegree_unique:
  "fls_subdegree g = (f\<degree>\<^sup>p)"
  if  "f \<simeq>\<^sub>p g" and "\<forall>n. (g $$ n) pdiv p = 0"
  for f g :: "'a fls"
proof (cases "f \<simeq>\<^sub>p 0")
  case True
  with that have "g = 0" using fls_p_reduced_is_zero_iff p_equality_fls.trans_right by blast
  with True show ?thesis by (simp add: p_depth_fls_def)
next
  case False show ?thesis
  proof (intro p_depth_fls_eqI[symmetric], rule False, rule that(1))
    fix h assume h: "f \<simeq>\<^sub>p h"
    from that(1) h
      have  "fls_subdegree h > fls_subdegree g \<Longrightarrow> p pdvd g $$ (fls_subdegree g)"
      using fls_pmod_equiv p_equality_fls.trans_right[of p f]
            p_equal_fls_extended_intsum_iff[of "fls_subdegree g" g h]
      by    fastforce
    moreover from that(2) have "(g $$ (fls_subdegree g)) pdiv p = 0" by blast
    ultimately show "fls_subdegree h \<le> fls_subdegree g"
      using False that(1) nth_fls_subdegree_nonzero[of g] by fastforce
  qed
qed

lemma fls_pmod_subdegree:
  "fls_subdegree (f pmod p) = (f\<degree>\<^sup>p)" for f :: "'a fls"
  using fls_p_reduced_subdegree_unique fls_pmod_reduced fls_pmod_equiv by blast

lemma fls_pmod_depth:
  "(f pmod p)\<degree>\<^sup>p = (f\<degree>\<^sup>p)" for f :: "'a fls"
  by (metis p_depth_fls.depth_equiv fls_pmod_equiv)

lemma fls_pmod_subdegree_ge:
  "fls_subdegree (f pmod p) \<ge> fls_subdegree f" if "f \<not>\<simeq>\<^sub>p 0"
  for f :: "'a fls"
  using that fls_pmod_subdegree p_depth_fls_ge_p_equal_subdegree' by auto

lemma fls_pmod_nth_below_subdegree:
  "(f pmod p) $$ n = 0" if "n < fls_subdegree f" for f :: "'a fls"
  using that fls_pmod_subdegree_ge[of f] by fastforce

lemma fls_pmod_nth_cong:
  "(f pmod p) $$ n = (g pmod p) $$ n" if "\<forall>k\<le>n. f $$ k = g $$ k" for f g :: "'a fls"
proof-
  consider
    "f = 0" "g = 0" | (f_n0) "f \<noteq> 0" "g = 0" | (g_n0) "f = 0" "g \<noteq> 0" |
    (f_n0_upper) "f \<noteq> 0" "n \<ge> fls_subdegree f" |
    (g_n0_lower) "g \<noteq> 0" "n < fls_subdegree f"
    by linarith
  thus ?thesis
  proof cases
    case f_n0 with that show ?thesis
      using fls_subdegree_geI[of f "n + 1"] by (simp add: fls_pmod_nth_below_subdegree)
  next
    case g_n0 with that show ?thesis
      using fls_subdegree_geI[of g "n + 1"] by (simp add: fls_pmod_nth_below_subdegree)
  next
    case g_n0_lower with that show ?thesis
      using fls_subdegree_geI[of g "n + 1"] by (simp add: fls_pmod_nth_below_subdegree)
  next
    case f_n0_upper
    from f_n0_upper(2) have "\<And>k. k < fls_subdegree f \<Longrightarrow> k \<le> n" by simp
    with that have "\<And>k. k < fls_subdegree f \<Longrightarrow> g $$ k = 0" by fastforce
    with that f_n0_upper show ?thesis
      using nth_fls_subdegree_nonzero fls_subdegree_eqI p_modulo_fls_nth
            fls_partially_p_modulo_rep_cong
      by    metis
  qed simp
qed

lemma fls_partially_reduced_nth_vs_pmod:
  "(f pmod p) $$ n = f $$ n" if "\<forall>k\<le>n. (f $$ k) pdiv p = 0"
proof (cases "n \<ge> fls_subdegree f")
  case True with that show ?thesis
    by (simp add: p_modulo_fls_nth fls_partially_reduced_nth_vs_rep)
qed (force simp add: fls_pmod_nth_below_subdegree)

lemma fls_pmod_eqI:
  "f pmod p = g" if "f \<simeq>\<^sub>p g" and "\<forall>n. (g $$ n) pdiv p = 0"
proof (intro fls_eq_above_subdegreeI, safe)
  define d :: "'a fls \<Rightarrow> int" where "d \<equiv> fls_subdegree"
  with that have *: "d(f pmod p) \<ge> (f\<degree>\<^sup>p)" "d(g) \<ge> (f\<degree>\<^sup>p)"
    using fls_pmod_subdegree fls_p_reduced_subdegree_unique by (simp, presburger)
  thus "d(f pmod p) \<ge> (f\<degree>\<^sup>p) - 1" "d(g) \<ge> (f\<degree>\<^sup>p) - 1" by auto
  fix n assume n: "n \<ge> (f\<degree>\<^sup>p) - 1"
  hence "\<forall>k\<le>n. (f pmod p) $$ k = g $$ k"
  proof (induct n rule: int_ge_induct)
    case base from that show ?case using fls_pmod_subdegree fls_p_reduced_subdegree_unique by simp
  next
    case (step n) show ?case
    proof clarify
      define pp where "pp \<equiv> Rep_prime p"
      fix k assume k: "k \<le> n + 1"
      define S where
        "S \<equiv> (\<Sum>k=(f\<degree>\<^sup>p)..n + 1.
          (f pmod p - g) $$ k * pp ^ nat (k - (f\<degree>\<^sup>p)))"
      define A
        where "A \<equiv> (if n + 1 = (f\<degree>\<^sup>p) then {} else {(f\<degree>\<^sup>p)..n})"
      with step(1) have "{(f\<degree>\<^sup>p)..n + 1} = insert (n + 1) A" by force
      moreover from A_def step(2) have "\<forall>k\<in>A. (f pmod p - g) $$ k = 0" by simp
      ultimately have
        "S = (f pmod p - g) $$ (n + 1) * pp ^ nat (n + 1 - (f\<degree>\<^sup>p))"
        using S_def A_def by force
      moreover from step(1) that(1) d_def pp_def S_def
        have  "pp ^ Suc (nat (n + 1 - (f\<degree>\<^sup>p))) dvd S"
        using * p_equality_fls.trans_right fls_pmod_equiv
              p_equal_fls_extended_intsum_iff[of "(f\<degree>\<^sup>p)" "f pmod p" g]
        by    force
      ultimately have "p pdvd ((f pmod p) - g) $$ (n + 1)" using pp_def Rep_prime_n0 by auto
      with pp_def that(2)
        have  "(f pmod p) $$ (n + 1) = ((g$$(n+1)) pdiv p) * pp + (g$$(n+1)) pmod p"
        using mod_eq_dvd_iff fls_pmod_reduced div_mult_mod_eq[of "(f pmod p) $$ (n + 1)" pp]
        by    force
       with pp_def k show "(f pmod p) $$ k = g $$ k"
        using step(2) by (cases "k = n + 1") (auto simp add: div_mult_mod_eq)
    qed
  qed
  thus "(f pmod p) $$ n = g $$ n" by fast
qed

lemma fls_pmod_eq_pmod_iff:
  "f pmod p = g pmod p \<longleftrightarrow> f \<simeq>\<^sub>p g" for f g :: "'a fls"
proof
  show "f pmod p = g pmod p \<Longrightarrow> f \<simeq>\<^sub>p g"
    by (metis fls_pmod_equiv p_equality_fls.refl p_equality_fls.cong)
  show "f \<simeq>\<^sub>p g \<Longrightarrow> f pmod p = g pmod p"
    using fls_pmod_equiv p_equality_fls.trans fls_pmod_reduced fls_pmod_eqI by meson
qed

lemma fls_pmod_equiv_pmod_iff:
  "(f pmod p) \<simeq>\<^sub>p (g pmod p) \<longleftrightarrow> f \<simeq>\<^sub>p g"
  for f g :: "'a fls"
  using fls_pmod_equiv p_equality_fls.cong p_equality_fls.sym by meson

lemma fls_p_modulo_iff:
  "f pmod p = g \<longleftrightarrow> f \<simeq>\<^sub>p g \<and> (\<forall>n. (g $$ n) pdiv p = 0)"
  using fls_pmod_equiv fls_pmod_reduced fls_pmod_eqI by blast

lemma fls_pmod_pmod[simp]: "(f pmod p) pmod p = f pmod p" for f :: "'a fls"
  by (metis fls_pmod_equiv p_equal_fls_trans fls_pmod_reduced fls_pmod_eqI)

lemma fls_pmod_cong:
  "f pmod p = g pmod p" if "f \<simeq>\<^sub>p g" for f g :: "'a fls"
  using that fls_pmod_equiv p_equal_fls_trans fls_pmod_reduced fls_pmod_eqI by meson

end (* context nontrivial_euclidean_ring_cancel *)

subsubsection \<open>Algebraic properties of reduction\<close>

lemma fls_pmod_1[simp]:
  "(1::'a fls) pmod p = 1" for p :: "'a::nontrivial_unique_euclidean_ring prime"
  by (intro fls_pmod_eqI, simp_all add: one_pdiv)

context
  fixes p :: "'a::nontrivial_euclidean_ring_cancel prime"
begin

lemma fls_pmod_0: "(0::'a fls) pmod p = 0"
  by simp

lemma fls_pmod_uminus_equiv: "(-f) pmod p \<simeq>\<^sub>p -(f pmod p)" for f :: "'a fls"
  using fls_pmod_equiv p_equality_fls.uminus p_equality_fls.trans_right by blast

lemma fls_pmod_equiv_add:
  "(f + g) pmod p = (f' + g') pmod p" if "f \<simeq>\<^sub>p f'" and "g \<simeq>\<^sub>p g'"
  for f f' g g' :: "'a fls"
  using that p_equality_fls.add fls_pmod_equiv p_equal_fls_trans fls_pmod_reduced fls_pmod_eqI
  by    meson

lemma fls_pmod_const_add:
  "(fls_const c + f) pmod p = fls_const c + f pmod p" if "fls_subdegree f > 0" and "c pdiv p = 0"
  for c :: 'a and f :: "'a fls"
proof (intro fls_pmod_eqI, safe)
  fix n from that show "(fls_const c + f pmod p) $$ n pdiv p = 0"
    by (cases n "0::int" rule: linorder_cases, simp_all add: fls_pmod_nth_below_subdegree)
qed (simp add: fls_pmod_equiv p_equality_fls.add)

lemma fls_pmod_add_equiv:
  "(f + g) pmod p \<simeq>\<^sub>p (f pmod p) + (g pmod p)" for f g :: "'a fls"
  by (metis fls_pmod_equiv fls_pmod_equiv_add p_equality_fls.trans_left)

lemma fls_pmod_mismatched_add_nth:
  "n < fls_subdegree g \<Longrightarrow> ((f + g) pmod p) $$ n = (f pmod p) $$ n"
  "((f + g) pmod p) $$ (fls_subdegree g) =
    ((f pmod p) $$ (fls_subdegree g) + g $$ (fls_subdegree g)) pmod p"
  if "fls_subdegree g > fls_subdegree f"
  for f :: "'a fls"
proof-
  assume n: "n < fls_subdegree g"
  show "((f + g) pmod p) $$ n = (f pmod p) $$ n"
  proof (cases "f = 0")
    case True with n show ?thesis using fls_pmod_nth_below_subdegree by auto
  next
    case False
    with that have "fls_subdegree (f + g) = fls_subdegree f" by (simp add: fls_subdegree_eqI)
    with n show ?thesis
      using fls_partially_p_modulo_rep_cong[of "f + g"] by (simp add: p_modulo_fls_nth)
  qed
next
  define pp and d :: "'a fls \<Rightarrow> int" and pmod_rep
    where "pp \<equiv> Rep_prime p" and "d \<equiv> fls_subdegree"
    and   "pmod_rep \<equiv> (\<lambda>f N. fls_partially_p_modulo_rep f N p)"
  show
    "((f + g) pmod p) $$ (fls_subdegree g) =
      ((f pmod p) $$ (fls_subdegree g) + g $$ (fls_subdegree g)) pmod p"
  proof (cases "f = 0")
    case False
    with that d_def have dfg: "d(f + g) = d(f)" by (simp add: fls_subdegree_eqI)
    with that d_def pmod_rep_def pp_def show ?thesis
      using fls_partially_p_modulo_rep.simps(2)[of "f + g" "nat (d(g) - d(f))"]
            fls_partially_p_modulo_rep.simps(2)[of "f + g" "nat (d(g) - d(f) - 1)"]
            fls_partially_p_modulo_rep.simps(2)[of f "nat (d(g) - d(f) - 1)"]
            fls_partially_p_modulo_rep_cong[of "f + g" f "d(g) - 1" "nat (d(g) - d(f) - 1)"]
            fls_partially_p_modulo_rep.simps(2)[of f "nat (d(g) - d(f))"]
      by    (simp add: p_modulo_fls_nth Suc_nat_eq_nat_zadd1 algebra_simps mod_simps)
  qed (simp add: d_def pmod_rep_def p_modulo_fls_nth)
qed

lemma fls_pmod_equiv_minus:
  "(f - g) pmod p = (f' - g') pmod p" if "f \<simeq>\<^sub>p f'" and "g \<simeq>\<^sub>p g'"
  for f f' g g' :: "'a fls"
  using that p_equality_fls.minus fls_pmod_equiv p_equal_fls_trans fls_pmod_reduced fls_pmod_eqI
  by    meson

lemma fls_pmod_minus_equiv:
  "(f - g) pmod p \<simeq>\<^sub>p ((f pmod p) - (g pmod p))" for f g :: "'a fls"
  by (metis fls_pmod_equiv fls_pmod_equiv_minus p_equality_fls.trans_left)

lemma fls_pmod_equiv_times:
  "(f * g) pmod p = (f' * g') pmod p" if "f \<simeq>\<^sub>p f'" and "g \<simeq>\<^sub>p g'"
  for f f' g g' :: "'a fls"
  using that p_equality_fls.mult fls_pmod_equiv p_equal_fls_trans fls_pmod_reduced fls_pmod_eqI
  by    meson

lemma fls_pmod_times_equiv:
  "(f * g) pmod p \<simeq>\<^sub>p (f pmod p) * (g pmod p)" for f g :: "'a fls"
  by (metis fls_pmod_equiv fls_pmod_equiv_times p_equality_fls.trans_left)

lemma fls_pmod_diff_cancel:
  "(f pmod p) $$ n = (g pmod p) $$ n" if "n < ((f - g)\<degree>\<^sup>p)"
  for f g :: "'a fls"
proof-
  consider
    "f \<simeq>\<^sub>p 0" | "g \<simeq>\<^sub>p 0" |
    (nonzero) "f \<not>\<simeq>\<^sub>p 0" "g \<not>\<simeq>\<^sub>p 0"
    by fast
  thus ?thesis
    using that
  proof cases
    case nonzero
    hence "n < ((f - g)\<degree>\<^sup>p) \<Longrightarrow> (f pmod p) $$ n = (g pmod p) $$ n"
    proof (induct f g rule: linorder_wlog'[of "\<lambda>f. f\<degree>\<^sup>p"])
      case (le f g)
      have *:
        "\<And>n. n < ((f - g)\<degree>\<^sup>p) \<Longrightarrow>
          ((f pmod p - g pmod p) pmod p) $$ n = 0"
        using p_depth_fls.depth_diff_equiv fls_pmod_equiv fls_pmod_subdegree fls_eq0_below_subdegree
        by    metis
      from le(2) consider
        (diff_le)   "((f - g)\<degree>\<^sup>p) \<le> (f\<degree>\<^sup>p)" |
        (diff_gt)   "((f - g)\<degree>\<^sup>p) > (g\<degree>\<^sup>p)" |
        (diff_betw)
          "(f\<degree>\<^sup>p) < ((f - g)\<degree>\<^sup>p)"
          "((f - g)\<degree>\<^sup>p) \<le> (g\<degree>\<^sup>p)"
        by linarith
      thus "(f pmod p) $$ n = (g pmod p) $$ n"
      proof cases
        case diff_le with le(1,2) show ?thesis by (simp add: fls_pmod_subdegree)
      next
        case diff_betw
        from le(2) diff_betw(2) have "\<forall>k\<le>n. ((f pmod p - g pmod p) $$ k) pdiv p = 0"
          by (auto simp add: fls_pmod_subdegree)
        with le(2) have "(f pmod p - g pmod p) $$ n = 0"
          using * fls_partially_reduced_nth_vs_pmod by metis
        thus ?thesis by auto
      next
        case diff_gt
        have "\<not> (f\<degree>\<^sup>p) < (g\<degree>\<^sup>p)"
        proof
          assume lt: "(f\<degree>\<^sup>p) < (g\<degree>\<^sup>p)"
          moreover from this
            have  "\<forall>k\<le>(f\<degree>\<^sup>p). ((f pmod p - g pmod p) $$ k) pdiv p = 0"
            by    (auto simp add: fls_pmod_subdegree)
          ultimately have "(f pmod p - g pmod p) $$ (f\<degree>\<^sup>p) = 0"
            using diff_gt * fls_partially_reduced_nth_vs_pmod[of _ "f pmod p - g pmod p"]
            by    fastforce
          with le(3) lt show False
            using fls_pmod_subdegree[of _ p] fls_pmod_eq0_iff nth_fls_subdegree_nonzero by force
        qed
        with le(1) have df_dg: "(f\<degree>\<^sup>p) = (g\<degree>\<^sup>p)" by linarith
        define pp where "pp \<equiv> Rep_prime p"
        have
          "n < ((f - g)\<degree>\<^sup>p) \<Longrightarrow>
            \<forall>k\<le>n. (f pmod p) $$ k = (g pmod p) $$ k"
        proof (cases "n \<ge> (f\<degree>\<^sup>p)")
          case True
          have strong:
            "\<And>N. N < ((f - g)\<degree>\<^sup>p) \<Longrightarrow>
              \<forall>k<N. (f pmod p) $$ k = (g pmod p) $$ k \<Longrightarrow>
              \<not> (f pmod p) $$ N \<noteq> (g pmod p) $$ N"
          proof
            fix N
            assume  N  :  "N < ((f - g)\<degree>\<^sup>p)"
                          "\<forall>k<N. (f pmod p) $$ k = (g pmod p) $$ k"
              and   neq:  "(f pmod p) $$ N \<noteq> (g pmod p) $$ N"
            hence "(f pmod p - g pmod p) $$ N \<noteq> 0" by simp
            with N(2) have "fls_subdegree (f pmod p - g pmod p) = N"
              using fls_subdegree_eqI[of "f pmod p - g pmod p" N] by auto
            hence "((f pmod p - g pmod p) pmod p) $$ N = ((f pmod p - g pmod p) $$ N) pmod p"
              by (simp add: p_modulo_fls_nth)
            with N(1) have "((f pmod p - g pmod p) $$ N) pmod p = 0"
              using * by metis
            hence "((f pmod p) $$ N) pmod p = ((g pmod p) $$ N) pmod p"
              using mod_eq_dvd_iff by auto
            with neq show False using fls_pmod_pmod_nth[of f] fls_pmod_pmod_nth[of g] by metis
          qed
          from True show
            "n < ((f - g)\<degree>\<^sup>p) \<Longrightarrow>
              \<forall>k\<le>n. (f pmod p) $$ k = (g pmod p) $$ k"
          proof (induct n rule: int_ge_induct, safe)
            case base
            fix k
            from diff_gt have "(f\<degree>\<^sup>p) < (f - g\<degree>\<^sup>p)" using df_dg by auto
            moreover have k_lt: "\<forall>k<f\<degree>\<^sup>p. (f pmod p) $$ k = (g pmod p) $$ k"
              using df_dg by (auto simp add: fls_pmod_subdegree)
            ultimately have
              "\<not> (f pmod p) $$ (f\<degree>\<^sup>p) \<noteq>
                (g pmod p) $$ (f\<degree>\<^sup>p)"
              "k < (f\<degree>\<^sup>p) \<Longrightarrow> (f pmod p) $$ k = (g pmod p) $$ k"
              using strong by (presburger, blast)
            moreover assume "k \<le> (f\<degree>\<^sup>p)"
            ultimately show "(f pmod p) $$ k = (g pmod p) $$ k" by fastforce
          next
            case (step n)
            fix k
            from step(2,3) have "\<not> (f pmod p) $$ (n + 1) \<noteq> (g pmod p) $$ (n + 1)"
              using strong by auto
            hence "k = n + 1 \<Longrightarrow> (f pmod p) $$ k = (g pmod p) $$ k" by fastforce
            moreover from step(2,3)
              have  "k \<le> n \<Longrightarrow> (f pmod p) $$ k = (g pmod p) $$ k"
              by    auto
            moreover assume "k \<le> n + 1"
            ultimately show "(f pmod p) $$ k = (g pmod p) $$ k" by fastforce
          qed
        next
          case False thus "\<forall>k\<le>n. (f pmod p) $$ k = (g pmod p) $$ k"
            using df_dg by (auto simp add: fls_pmod_subdegree)
        qed
        with le(2) show ?thesis by fast
      qed
    qed (simp add: p_depth_fls.depth_diff)
    with that show ?thesis by blast
  qed (
    fastforce simp add: p_depth_fls.depth_diff_equiv0_left fls_pmod_eq0_iff fls_pmod_subdegree,
    fastforce simp add: p_depth_fls.depth_diff_equiv0_right fls_pmod_eq0_iff fls_pmod_subdegree
  )
qed

lemma fls_pmod_diff_cancel_iff:
  "((f - g)\<degree>\<^sup>p) > n \<longleftrightarrow>
    (\<forall>k\<le>n. (f pmod p) $$ k = (g pmod p) $$ k)"
  if "f \<not>\<simeq>\<^sub>p g"
  for f g :: "'a fls"
proof
  assume "\<forall>k\<le>n. (f pmod p) $$ k = (g pmod p) $$ k"
  moreover from that have "f pmod p \<noteq> g pmod p" using fls_pmod_eq_pmod_iff by auto
  ultimately have "fls_subdegree (f pmod p - g pmod p) > n"
    using fls_subdegree_greaterI[of "f pmod p - g pmod p"] by auto
  with that have "fls_subdegree ((f pmod p - g pmod p) pmod p) > n"
    using fls_pmod_subdegree_ge[of p "f pmod p - g pmod p"] fls_pmod_equiv_pmod_iff
          p_equality_fls.conv_0
    by    fastforce
  thus "((f - g)\<degree>\<^sup>p) > n"
    using fls_pmod_subdegree fls_pmod_equiv p_depth_fls.depth_diff_equiv by metis
qed (simp add: fls_pmod_diff_cancel)

end (* context nontrivial_euclidean_ring_cancel *)


subsection \<open>Inversion relative to a prime\<close>

subsubsection \<open>Of scalars\<close>

class bezout_semiring = semiring_gcd +
  assumes bezout: "\<exists>u v. u * x + v * y = gcd x y"

class bezout_ring = ring_gcd +
  assumes bezout: "\<exists>u v. u * x + v * y = gcd x y"
begin
subclass bezout_semiring using bezout by unfold_locales
subclass idom ..
end

instance int :: bezout_ring by (standard, rule bezout_int)

class nontrivial_factorial_euclidean_bezout = nontrivial_euclidean_ring_cancel + bezout_semiring
begin
subclass bezout_ring by (standard, rule bezout)
end

class nontrivial_factorial_unique_euclidean_bezout =
  nontrivial_unique_euclidean_ring + bezout_semiring
begin
subclass nontrivial_factorial_euclidean_bezout ..
end

instance int :: nontrivial_factorial_unique_euclidean_bezout ..

lemma prime_residue_inverse_ex1:
  "\<exists>!x. x pdiv p = 0 \<and> (x * a) pmod p = 1" if "\<not> p pdvd a"
  for a :: "'a::nontrivial_factorial_unique_euclidean_bezout" and p :: "'a prime"
proof (intro ex_ex1I, safe)
  define pp where "pp \<equiv> Rep_prime p"
  with that obtain u v where uv: "u * pp + v * a = 1"
    using Rep_prime[of p] prime_imp_coprime bezout[of pp a] coprime_iff_gcd_eq_1[of pp a]
    by    auto
  define y where "y \<equiv> v pmod p"
  with pp_def have "(y * a) pmod p = 1"
    by (metis
      uv p_modulo_scalar_def mod_add_left_eq mod_mult_self2_is_0 add_0_left mod_mult_left_eq
      one_pmod
    )
  moreover from y_def have "y pdiv p = 0" by auto
  ultimately show "\<exists>x. x pdiv p = 0 \<and> (x * a) pmod p = 1" by fast

  fix x x'
  assume  x : "x  pdiv p = 0" "x  * a pmod p = 1"
    and   x': "x' pdiv p = 0" "x' * a pmod p = 1"
  from pp_def x(1) have "x pmod p = x" using div_mult_mod_eq[of x pp] by auto
  with x'(2) have "x = ((x pmod p) * ((x' * a) pmod p)) pmod p" by auto
  also from pp_def x(2) have "\<dots> = (x' * 1) pmod p"
    by (metis p_modulo_scalar_def mult.assoc mult.commute mod_mult_right_eq)
  finally show "x = x'" using pp_def x'(1) div_mult_mod_eq[of x' pp] by simp
qed

consts pinverse :: "'a \<Rightarrow> 'b prime \<Rightarrow> 'a"
  ("(_\<inverse>\<^sup>_)" [51, 51] 50)

overloading pinverse_scalar \<equiv> "pinverse :: 'a \<Rightarrow> 'a prime \<Rightarrow> 'a"
begin
definition pinverse_scalar ::
  "'a::nontrivial_factorial_unique_euclidean_bezout \<Rightarrow> 'a prime \<Rightarrow> 'a"
  where
    "pinverse_scalar a p \<equiv>
      (if p pdvd a then 0 else
        (THE x. x pdiv p = 0 \<and> (x * a) pmod p = 1))"
end

context
  fixes p :: "'a::nontrivial_factorial_unique_euclidean_bezout prime"
begin

lemma pinverse_scalar: "((a\<inverse>\<^sup>p) * a) pmod p = 1" if "\<not> p pdvd a" for a :: 'a
  using that theI'[OF prime_residue_inverse_ex1] unfolding pinverse_scalar_def by auto

lemma pinverse_scalar_reduced: "(a\<inverse>\<^sup>p) pdiv p = 0" for a :: 'a
  using theI'[OF prime_residue_inverse_ex1] unfolding pinverse_scalar_def by auto

lemma pinverse_scalar_nzero: "(a\<inverse>\<^sup>p) \<noteq> 0" if "\<not> p pdvd a" for a :: 'a
  using that pinverse_scalar by fastforce

lemma pinverse_scalar_zero[simp]: "((0::'a)\<inverse>\<^sup>p) = 0"
  unfolding pinverse_scalar_def by force

lemma pinverse_scalar_one[simp]: "((1::'a)\<inverse>\<^sup>p) = 1"
  using     Rep_prime_not_unit the1_equality[OF prime_residue_inverse_ex1, of p 1] one_pdiv one_pmod
  unfolding pinverse_scalar_def
  by        auto

end (* context *)

subsubsection \<open>Inductive partial inversion of formal Laurent series\<close>

text \<open>
  Inductively define a depth-zero partial inverse representative function.
  It is effectively a polynomial of degree equal to the @{type nat} argument.
\<close>
primrec fls_partially_pinverse_rep ::
  "'a::nontrivial_factorial_unique_euclidean_bezout fls \<Rightarrow> nat \<Rightarrow>
    'a prime \<Rightarrow> (int \<Rightarrow> 'a)"
  where
    "fls_partially_pinverse_rep f 0 p n =
      (if n = 0
        then ((f pmod p) $$ (f\<degree>\<^sup>p))\<inverse>\<^sup>p
        else 0)"
  | "fls_partially_pinverse_rep f (Suc N) p =
      (fls_partially_pinverse_rep f N p)(
        int (Suc N) := -(
          (
            (
              fls_shift (f\<degree>\<^sup>p) (Abs_fls (fls_partially_pinverse_rep f N p)) *
              (f pmod p)
            ) pmod p
          ) $$ (int (Suc N)) * (((f pmod p) $$ (f\<degree>\<^sup>p))\<inverse>\<^sup>p)
        ) pmod p
      )"

lemma fls_partially_pinverse_rep_func_lower_bound:
  "\<forall>n<0. fls_partially_pinverse_rep f (nat n) p n = 0"
  by fastforce

lemma fls_partially_pinverse_rep_at_0:
  "fls_partially_pinverse_rep f N p 0 = (((f pmod p) $$ (f\<degree>\<^sup>p))\<inverse>\<^sup>p)"
  by (induct N) simp_all

lemma fls_partially_pinverse_rep_func_lower_bound':
  "\<forall>n<0. fls_partially_pinverse_rep f N p n = 0"
  by (induct N) simp_all

lemmas Abs_fls_partially_pinverse_rep_nth =
  nth_Abs_fls_lower_bound[OF fls_partially_pinverse_rep_func_lower_bound']

lemma fls_partially_pinverse_rep_func_truncates:
  "n > int N \<Longrightarrow> fls_partially_pinverse_rep f N p n = 0"
  by (induct N, simp_all)

context
  fixes p :: "'a::nontrivial_factorial_unique_euclidean_bezout prime"
begin

lemma pinverse_scalar_fls_pmod_base:
  "(
    (((f pmod p) $$ (f\<degree>\<^sup>p))\<inverse>\<^sup>p) * (f pmod p) $$ (f\<degree>\<^sup>p)
  ) pmod p = 1"
  if  "f \<not>\<simeq>\<^sub>p 0"
  for f :: "'a fls"
  using that fls_pmod_eq0_iff fls_pmod_subdegree[of f]
        nth_fls_subdegree_nonzero[of "f pmod p"]
        pinverse_scalar[of p "(f pmod p) $$ (f\<degree>\<^sup>p)"]
        fls_pmod_reduced[of f p "(f\<degree>\<^sup>p)"]
  by    fastforce

lemma fls_partially_pinverse_rep_eq_zero:
  "fls_partially_pinverse_rep f N p = 0" if "f \<simeq>\<^sub>p 0"
  for f :: "'a fls"
proof (induct N)
  case 0 from that show ?case by auto
next
  case (Suc N) show ?case
  proof
    fix n show "fls_partially_pinverse_rep f (Suc N) p n = 0 n"
    proof (cases "n = int (Suc N)")
      case True
      from Suc have
        "fls_shift (f\<degree>\<^sup>p) (Abs_fls (fls_partially_pinverse_rep f N p)) = 0"
        using fls_shift_zero unfolding zero_fls_def zero_fun_def by fastforce
      with True show ?thesis using fls_pmod_0 by auto
    qed (simp add: Suc)
  qed
qed

lemma fls_partially_pinverse_rep_nzero_at_0:
  "fls_partially_pinverse_rep f N p 0 \<noteq> 0" if "f \<not>\<simeq>\<^sub>p 0"  for f :: "'a fls"
  using that fls_partially_pinverse_rep_at_0[of f] pinverse_scalar_fls_pmod_base by fastforce

lemma fls_partially_pinverse_rep_eq_zero_iff:
  "fls_partially_pinverse_rep f N p = 0 \<longleftrightarrow> f \<simeq>\<^sub>p 0"
  for f :: "'a fls"
  using fls_partially_pinverse_rep_eq_zero[of f N] fls_partially_pinverse_rep_nzero_at_0[of f N]
  by    fastforce

lemma Abs_fls_partially_pinverse_rep_nzero:
  "Abs_fls (fls_partially_pinverse_rep f N p) \<noteq> 0" if "f \<not>\<simeq>\<^sub>p 0"
  for f :: "'a fls"
  using that fls_partially_pinverse_rep_nzero_at_0 Abs_fls_partially_pinverse_rep_nth[of f N p]
  by    fastforce

lemma Abs_fls_partially_pinverse_rep_eq_zero_iff:
  "Abs_fls (fls_partially_pinverse_rep f N p) = 0 \<longleftrightarrow> f \<simeq>\<^sub>p 0"
  for f :: "'a fls"
  using fls_eq_iff Abs_fls_partially_pinverse_rep_nth[of f]
        fls_partially_pinverse_rep_eq_zero_iff[of f N]
  by    fastforce

lemma Abs_fls_partially_pinverse_rep_subdegree:
  "fls_subdegree (Abs_fls (fls_partially_pinverse_rep f N p)) = 0" if "f \<not>\<simeq>\<^sub>p 0"
  for f :: "'a fls"
  using that fls_partially_pinverse_rep_nzero_at_0 fls_partially_pinverse_rep_func_lower_bound'
        Abs_fls_partially_pinverse_rep_nth fls_subdegree_eqI
  by    metis

lemma fls_shift_pinv_rep_subdegree:
  "fls_subdegree (fls_shift m (Abs_fls (fls_partially_pinverse_rep f N p))) = -m"
  if  "f \<not>\<simeq>\<^sub>p 0"
  for f :: "'a fls"
  using that Abs_fls_partially_pinverse_rep_nzero Abs_fls_partially_pinverse_rep_subdegree
  by    fastforce

lemma fls_partially_pinverse_rep_cong:
  "fls_partially_pinverse_rep f N p (n - K) = fls_partially_pinverse_rep g N p (n - K)"
  if "f\<degree>\<^sup>p = K" and "g\<degree>\<^sup>p = K" and "\<forall>k\<le>n. f $$ k = g $$ k"
  for f g :: "'a fls"
proof-
  have equiv0_case:
    "\<And>f g :: 'a fls.
      f \<simeq>\<^sub>p 0 \<Longrightarrow> g\<degree>\<^sup>p = 0 \<Longrightarrow>
        \<forall>k\<le>n. f $$ k = g $$ k \<Longrightarrow>
        fls_partially_pinverse_rep f N p n = fls_partially_pinverse_rep g N p n"
  proof-
    fix f g :: "'a fls"
    assume  f: "f \<simeq>\<^sub>p 0" and g: "g\<degree>\<^sup>p = 0"
      and   fg: "\<forall>k\<le>n. f $$ k = g $$ k"
    show "fls_partially_pinverse_rep f N p n = fls_partially_pinverse_rep g N p n"
    proof (cases "g \<simeq>\<^sub>p 0", metis f fls_partially_pinverse_rep_eq_zero)
      case False
      have "\<forall>k\<le>n. fls_partially_pinverse_rep g N p k = 0"
      proof (induct N)
        case 0 with f g fg show ?case using fls_pmod_nth_cong[of 0 g f] by auto
      next
        case (Suc N) show ?case
        proof clarify
          fix k assume k: "k \<le> n" show "fls_partially_pinverse_rep g (Suc N) p k = 0"
          proof (cases "k = int (Suc N)")
            case False with k Suc show ?thesis by force
          next
            case True
            moreover define G where "G \<equiv> Abs_fls (fls_partially_pinverse_rep g N p)"
            moreover have "((G * (g pmod p)) pmod p) $$ int (Suc N) = (0 pmod p) $$ int (Suc N)"
            proof (rule fls_pmod_nth_cong, clarify)
              fix j assume "j \<le> int (Suc N)"
              with f g fg G_def True False k show "(G * (g pmod p)) $$ j = 0 $$ j"
                using fls_times_nth(1)[of G] fls_pmod_subdegree[of g p]
                      Abs_fls_partially_pinverse_rep_subdegree[of g] fls_pmod_nth_cong[of _ g f]
                      p_modulo_fls_eq0[of p f]
                by    auto
            qed
            ultimately show "fls_partially_pinverse_rep g (Suc N) p k = 0" using g by simp
          qed
        qed
      qed
      with f show ?thesis using fls_partially_pinverse_rep_eq_zero by fastforce
    qed
  qed
  consider
    "f \<simeq>\<^sub>p 0" |
    "g \<simeq>\<^sub>p 0" |
    (nonzero) "f \<not>\<simeq>\<^sub>p 0" "g \<not>\<simeq>\<^sub>p 0"
    by blast
  thus ?thesis
    using that equiv0_case
  proof cases
    case nonzero
    from that have base:
      "n \<ge> K \<Longrightarrow>
        (((f pmod p) $$ K)\<inverse>\<^sup>p) = (((g pmod p) $$ K)\<inverse>\<^sup>p)"
      using fls_pmod_nth_cong[of K f g] by simp
    have
      "\<forall>k\<le>n.
        fls_partially_pinverse_rep f N p (k - K) = fls_partially_pinverse_rep g N p (k - K)"
    proof (induct N, simp add: that(1,2), safe, rule base, simp)
      case (Suc N)
      fix k assume k: "k \<le> n"
      show
        "fls_partially_pinverse_rep f (Suc N) p (k - K) =
          fls_partially_pinverse_rep g (Suc N) p (k - K)"
      proof (cases "k = int (Suc N) + K")
        case False with Suc k show ?thesis by fastforce (* simp works *)
      next
        case True
        with k have K: "n \<ge> K" by linarith
        define A :: "'a fls \<Rightarrow> 'a fls"
          where "A \<equiv> (\<lambda>f. Abs_fls (fls_partially_pinverse_rep f N p))"
        have
          "((fls_shift K (A f) * (f pmod p)) pmod p) $$ (int (Suc N)) =
            ((fls_shift K (A g) * (g pmod p)) pmod p) $$ (int (Suc N))"
        proof (rule fls_pmod_nth_cong, clarify)
          fix j assume j: "j \<le> int (Suc N)"
          with k True have "\<forall>i\<in>{0..j}. i + K \<le> n" by simp
          with Suc A_def have "\<forall>i\<in>{0..j}. A f $$ i = A g $$ i"
            using Abs_fls_partially_pinverse_rep_nth[of _ N p] by fastforce
          moreover from that(3) True j k have
            "\<forall>i\<in>{0..j}. (f pmod p) $$ (K + j - i) = (g pmod p) $$ (K + j - i)"
            using fls_pmod_nth_cong[of "K + j - _" f g p] by simp
          ultimately show
            "(fls_shift K (A f) * (f pmod p)) $$ j = (fls_shift K (A g) * (g pmod p)) $$ j"
            using that(1,2) nonzero A_def fls_shift_pinv_rep_subdegree fls_pmod_subdegree[of _ p]
                  fls_times_nth(1)[of "fls_shift K (A _)"]
            by    auto
        qed
        with that(1,2) True A_def show
          "fls_partially_pinverse_rep f (Suc N) p (k - K) =
            fls_partially_pinverse_rep g (Suc N) p (k - K)"
          using base K by simp
      qed
    qed
    thus ?thesis by auto
  qed (simp_all add: p_depth_fls.depth_equiv_0)
qed

lemma fls_pinv_rep_times_f_subdegree:
  "fls_subdegree (
    fls_shift (f\<degree>\<^sup>p) (Abs_fls (fls_partially_pinverse_rep f N p)) *
    (f pmod p)
  ) = 0"
  if  "f \<not>\<simeq>\<^sub>p 0"
  for f :: "'a fls"
proof-
  from that
    have  "f pmod p \<noteq> 0" and "Abs_fls (fls_partially_pinverse_rep f N p) \<noteq> 0"
    using fls_pmod_eq0_iff Abs_fls_partially_pinverse_rep_nzero by (blast, blast)
  with that show ?thesis
    using fls_shift_pinv_rep_subdegree fls_pmod_subdegree
          fls_shift_eq0_iff[of "(f\<degree>\<^sup>p)"]
    by    fastforce
qed

lemma Abs_fls_pinv_rep_Suc:
  fixes f :: "'a fls" and N :: nat
  defines
    "c \<equiv>
      -(
          (
            (
              fls_shift (f\<degree>\<^sup>p) (Abs_fls (fls_partially_pinverse_rep f N p)) *
              (f pmod p)
            ) pmod p
          ) $$ (int (Suc N)) * (((f pmod p) $$ (f\<degree>\<^sup>p))\<inverse>\<^sup>p)
      ) pmod p"
  assumes f: "f \<not>\<simeq>\<^sub>p 0"
  shows
    "Abs_fls (fls_partially_pinverse_rep f (Suc N) p) =
      Abs_fls (fls_partially_pinverse_rep f N p) + fls_shift (- int (Suc N)) (fls_const c)"
proof (intro fls_eqI)
  define Abs_inv_rep and s
    where "Abs_inv_rep \<equiv> (\<lambda>N. Abs_fls (fls_partially_pinverse_rep f N p))"
    and   "s \<equiv> fls_shift (- int (Suc N)) (fls_const c)"
  fix n show "Abs_inv_rep (Suc N) $$ n = (Abs_inv_rep N + s) $$ n"
  proof-
    consider (zero) "n = 0" | (SucN) "n = Suc N" | (neither) "n \<noteq> 0" "n \<noteq> Suc N"
      by blast
    thus ?thesis
    proof cases
      case zero
      moreover from this Abs_inv_rep_def have
        "Abs_inv_rep (Suc N) $$ n = (((f pmod p) $$ (f\<degree>\<^sup>p))\<inverse>\<^sup>p)"
        by (metis Abs_fls_partially_pinverse_rep_nth fls_partially_pinverse_rep_at_0)
      ultimately show ?thesis
        using Abs_inv_rep_def s_def Abs_fls_partially_pinverse_rep_nth[of f N]
              fls_partially_pinverse_rep_at_0[of f N]
        by    force
    next
      case SucN with Abs_inv_rep_def s_def c_def show ?thesis
        using Abs_fls_partially_pinverse_rep_nth[of f N]
              Abs_fls_partially_pinverse_rep_nth[of f "Suc N"]
              fls_partially_pinverse_rep_func_truncates[of N n]
        by    fastforce
    next
      case neither with Abs_inv_rep_def s_def show ?thesis
        using Abs_fls_partially_pinverse_rep_nth[of f N]
              Abs_fls_partially_pinverse_rep_nth[of f "Suc N"]
        by    fastforce
    qed
  qed
qed

lemma fls_pinv_rep_times_f_nth:
  "((
    fls_shift (f\<degree>\<^sup>p) (Abs_fls (fls_partially_pinverse_rep f N p)) *
    (f pmod p)
  ) pmod p) $$ n = 0"
  if  f: "f \<not>\<simeq>\<^sub>p 0" and n: "n \<ge> 1" "n \<le> int N"
  for f :: "'a fls" and n :: int
proof-
  define pp where "pp \<equiv> Rep_prime p"
  define Abs_inv_rep
    where "Abs_inv_rep \<equiv> (\<lambda>N. Abs_fls (fls_partially_pinverse_rep f N p))"
  define g where
    "g \<equiv> (\<lambda>N. fls_shift (f\<degree>\<^sup>p) (Abs_inv_rep N) * (f pmod p))"
  from f g_def Abs_inv_rep_def have dg: "\<forall>N. fls_subdegree (g N) = 0"
    using fls_pinv_rep_times_f_subdegree by presburger
  have "\<forall>k\<in>{1..int N}. (g N pmod p) $$ k = 0"
  proof (induct N)
    case (Suc N)
    define c where
      "c \<equiv> -(
        ((g N) pmod p) $$ (int (Suc N)) * (((f pmod p) $$ (f\<degree>\<^sup>p))\<inverse>\<^sup>p)
      ) pmod p"
    define s where "s \<equiv> fls_shift ((f\<degree>\<^sup>p) - int (Suc N)) (fls_const c)"
    from that s_def c_def g_def Abs_inv_rep_def
      have  g_SucN_decomp: "g (Suc N) = g N + s * (f pmod p)"
      using Abs_fls_pinv_rep_Suc[of f N]
      by    (simp add: algebra_simps)
    from pp_def have fpmod_base:
      "(f pmod p) $$ (f\<degree>\<^sup>p) pmod p = (f pmod p) $$ (f\<degree>\<^sup>p)"
      using fls_pmod_reduced[of f p "f\<degree>\<^sup>p"]
            div_mult_mod_eq[of "(f pmod p) $$ (f\<degree>\<^sup>p)" pp]
      by    simp
    show ?case
    proof (cases "c = 0", safe)
      case True fix k assume k: "k \<in> {1..int (Suc N)}"
      from f pp_def True c_def have
        "(((g N) pmod p) $$ (int (Suc N))) pmod p = 0"
        using fpmod_base pinverse_scalar_fls_pmod_base[of f]
              mod_mult_right_eq[of
                "-((g N) pmod p) $$ (int (Suc N))"
                "((((f pmod p) $$ (f\<degree>\<^sup>p))\<inverse>\<^sup>p) *
                  (f pmod p) $$ (f\<degree>\<^sup>p))"
                pp
              ]
        by    (auto simp add: algebra_simps)
      with pp_def have "((g N) pmod p) $$ (int (Suc N)) = 0"
        using fls_pmod_reduced div_mult_mod_eq[of "((g N) pmod p) $$ (int (Suc N))" pp] by simp
      moreover have "{1..int (Suc N)} = insert (int (Suc N)) {1..int N}" by force
      ultimately show "(g (Suc N) pmod p) $$ k = 0" using k Suc s_def True g_SucN_decomp by auto
    next
      case False fix k assume k: "k \<in> {1..int (Suc N)}"
      from False s_def have s_n0: "s \<noteq> 0" using fls_shift_eq0_iff[of _ "fls_const c"] by auto
      moreover from False s_def
        have  ds: "fls_subdegree s = - ((f\<degree>\<^sup>p) - int (Suc N))"
        by    simp
      ultimately have d_s_fpmod: "fls_subdegree (s * (f pmod p)) = int (Suc N)"
        using f fls_pmod_eq0_iff[of f p] fls_pmod_subdegree[of f p]
              fls_subdegree_mult[of s "f pmod p"]
        by    auto
      show "(g (Suc N) pmod p) $$ k = 0"
      proof (cases "k = int (Suc N)")
        case True
        with pp_def s_def c_def have
          "(g (Suc N) pmod p) $$ k =
            (
              (g N pmod p) $$ (int (Suc N)) +
              (
                -(
                  ((g N) pmod p) $$ (int (Suc N)) *
                  (((f pmod p) $$ (f\<degree>\<^sup>p))\<inverse>\<^sup>p)
                ) pmod p
                * ((f pmod p) $$ (f\<degree>\<^sup>p) pmod p)
              ) pmod p
            ) pmod p"
          using g_SucN_decomp dg ds d_s_fpmod fpmod_base
                fls_pmod_mismatched_add_nth(2)[of "g N" "s * (f pmod p)"]
                fls_times_base[of s "f pmod p"]
                fls_pmod_subdegree[of f p]
                mod_add_right_eq[of "(g N pmod p) $$ (int (Suc N))" _ pp]
          by    simp
        with f pp_def show ?thesis
          using pinverse_scalar_fls_pmod_base[of f]
                mod_mult_right_eq[of
                  "- ((g N) pmod p) $$ (int (Suc N))"
                  "(((f pmod p) $$ (f\<degree>\<^sup>p))\<inverse>\<^sup>p) *
                    ((f pmod p) $$ (f\<degree>\<^sup>p))"
                  pp
                ]
                mod_add_right_eq[of
                  "(g N pmod p) $$ (int (Suc N))" "- ((g N) pmod p) $$ (int (Suc N))" pp
                ]
          by    (simp add: mod_mult_eq algebra_simps)
      next
        case False
        with Suc k show ?thesis
          using g_SucN_decomp dg d_s_fpmod by (simp add: fls_pmod_mismatched_add_nth(1))
      qed
    qed
  qed simp
  with n g_def Abs_inv_rep_def show ?thesis by presburger
qed

end (* context *)

subsubsection \<open>Full inversion of formal Laurent series\<close>

text \<open>
  Now we collect the terms of the infinite sequence of partial inversion polynomials
  into a formal Laurent series,
  shifted to the opposite depth as the original.
\<close>

overloading pinverse_fls \<equiv> "pinverse :: 'a fls \<Rightarrow> 'a prime \<Rightarrow> 'a fls"
begin
definition pinverse_fls ::
  "'a::nontrivial_factorial_unique_euclidean_bezout fls \<Rightarrow> 'a prime \<Rightarrow> 'a fls"
  where
    "pinverse_fls f p \<equiv>
      (if f \<simeq>\<^sub>p 0 then 0 else
        fls_shift (f\<degree>\<^sup>p)
          (Abs_fls (\<lambda>n. fls_partially_pinverse_rep f (nat n) p n)))"
end

context
  fixes p :: "'a::nontrivial_factorial_unique_euclidean_bezout prime"
begin

lemma pinverse_fls_nth:
  "(f\<inverse>\<^sup>p) $$ n =
    fls_partially_pinverse_rep f (nat (n + (f\<degree>\<^sup>p))) p (n + (f\<degree>\<^sup>p))"
  if "f \<not>\<simeq>\<^sub>p 0"
  using     that nth_Abs_fls_lower_bound[OF fls_partially_pinverse_rep_func_lower_bound]
  unfolding pinverse_fls_def
  by        auto

lemma pinverse_fls_nth':
  "int N \<ge> n + (f\<degree>\<^sup>p) \<Longrightarrow>
    (f\<inverse>\<^sup>p) $$ n = fls_partially_pinverse_rep f N p (n + (f\<degree>\<^sup>p))"
  if "f \<not>\<simeq>\<^sub>p 0"
proof (induct N)
  case 0 with that show ?case by (simp add: pinverse_fls_nth)
next
  case (Suc N) with that show ?case using nat_int[of "Suc N"]
    by (cases "n + (f\<degree>\<^sup>p) = int (Suc N)") (auto simp add: pinverse_fls_nth)
qed

lemma pinverse_fls_eq0[simp]:
  "(f\<inverse>\<^sup>p) = 0" if "f \<simeq>\<^sub>p 0" for f :: "'a fls"
  using that unfolding pinverse_fls_def by auto

lemma fls_pinv_eq0_iff:
  "(f\<inverse>\<^sup>p) = 0 \<longleftrightarrow> f \<simeq>\<^sub>p 0" for f :: "'a fls"
  using pinverse_scalar_fls_pmod_base pinverse_fls_nth[of f "-(f\<degree>\<^sup>p)"] by fastforce

lemma fls_pinv_subdegree:
  "fls_subdegree (f\<inverse>\<^sup>p) = -(f\<degree>\<^sup>p)" for f :: "'a fls"
  using fls_partially_pinverse_rep_nzero_at_0[of p f 0] fls_partially_pinverse_rep_func_lower_bound
  by    (cases "f \<simeq>\<^sub>p 0")
        (simp, fastforce intro: fls_subdegree_eqI simp add: pinverse_fls_nth)

lemma fls_pinv_reduced[simp]: "((f\<inverse>\<^sup>p) $$ n) pdiv p = 0"
proof (cases "f \<simeq>\<^sub>p 0")
  case False show ?thesis
  proof (cases n "fls_subdegree (f\<inverse>\<^sup>p)" rule: linorder_cases)
    case greater
    hence "n + (f\<degree>\<^sup>p) - 1 \<ge> 0" using fls_pinv_subdegree[of f] by force
    hence "nat (n + (f\<degree>\<^sup>p)) = Suc (nat (n + (f\<degree>\<^sup>p) - 1))" by linarith
    with False show ?thesis by (fastforce simp add: pinverse_fls_nth)
  qed (simp, fastforce simp add: False pinverse_fls_nth fls_pinv_subdegree pinverse_scalar_reduced)
qed simp

lemma pinverse_times_p_modulo_fls:
  "( (f\<inverse>\<^sup>p) * (f pmod p) ) pmod p = 1" if "f \<not>\<simeq>\<^sub>p 0"
  for f :: "'a fls"
proof (intro fls_eq_above_subdegreeI, safe)
  define f_0 where "f_0 \<equiv> (f pmod p) $$ (f\<degree>\<^sup>p)"
  from that have d_prod: "fls_subdegree ((f\<inverse>\<^sup>p) * (f pmod p)) = 0"
    using fls_pmod_eq0_iff[of f] fls_pinv_eq0_iff[of f]
    by    (auto simp add: fls_pmod_subdegree fls_pinv_subdegree)
  with that have base: "((f\<inverse>\<^sup>p) * (f pmod p) pmod p) $$ 0 = 1"
    using pinverse_scalar_fls_pmod_base fls_times_base[of "f\<inverse>\<^sup>p" "f pmod p"]
    by    (auto simp add: p_modulo_fls_nth pinverse_fls_nth fls_pmod_subdegree fls_pinv_subdegree)
  hence "((f\<inverse>\<^sup>p) * (f pmod p)) \<not>\<simeq>\<^sub>p 0" by fastforce
  thus "0 \<le> fls_subdegree ((f\<inverse>\<^sup>p) * (f pmod p) pmod p)"
    using d_prod fls_pmod_subdegree_ge by metis
  fix k::int assume k: "k \<ge> 0"
  show "((f\<inverse>\<^sup>p) * (f pmod p) pmod p) $$ k = 1 $$ k"
  proof (cases "k = 0")
    case False
    define s where
      "s \<equiv>
        fls_shift (f\<degree>\<^sup>p) (Abs_fls (fls_partially_pinverse_rep f (nat k) p))"
    from that s_def have "fls_subdegree s = -(f\<degree>\<^sup>p)"
      using Abs_fls_partially_pinverse_rep_nzero Abs_fls_partially_pinverse_rep_subdegree
      by    fastforce
    with that s_def
      have  "((f\<inverse>\<^sup>p) * (f pmod p) pmod p) $$ k = (s * (f pmod p) pmod p) $$ k"
      using fls_times_nth(1)[of "f\<inverse>\<^sup>p"] fls_times_nth(1)[of s]
            pinverse_fls_nth'[of f _ "nat k"] Abs_fls_partially_pinverse_rep_nth[of f]
      by    (auto intro: fls_pmod_nth_cong simp add: fls_pmod_subdegree fls_pinv_subdegree)
    with that k False s_def show ?thesis using fls_pinv_rep_times_f_nth by fastforce
  qed (simp add: base)
qed simp

lemma pinverse_fls:
  "((f\<inverse>\<^sup>p) * f) pmod p = 1" if "f \<not>\<simeq>\<^sub>p 0" for f :: "'a fls"
  using that pinverse_times_p_modulo_fls fls_pmod_equiv[of p f]
        fls_pmod_equiv_times[of p "f\<inverse>\<^sup>p" "f\<inverse>\<^sup>p"]
  by    fastforce

lemma pinverse_fls_mult_equiv1:
  "((f\<inverse>\<^sup>p) * f) \<simeq>\<^sub>p 1" if "f \<not>\<simeq>\<^sub>p 0" for f :: "'a fls"
  by (metis that pinverse_fls fls_pmod_equiv)

lemma pinverse_fls_mult_equiv1':
  "(f * (f\<inverse>\<^sup>p)) \<simeq>\<^sub>p 1" if "f \<not>\<simeq>\<^sub>p 0" for f :: "'a fls"
  by (metis that pinverse_fls_mult_equiv1 mult.commute)

lemma p_modulo_pinverse_fls[simp]:
  "(f\<inverse>\<^sup>p) pmod p = (f\<inverse>\<^sup>p)" for f :: "'a fls"
  using fls_pmod_reduced fls_pmod_eqI by force

lemma fls_pinv_equiv0_iff:
  "(f\<inverse>\<^sup>p) \<simeq>\<^sub>p 0 \<longleftrightarrow> f \<simeq>\<^sub>p 0"
  for f :: "'a fls"
proof
  assume "((f\<inverse>\<^sup>p) \<simeq>\<^sub>p 0)"
  hence "(f\<inverse>\<^sup>p) pmod p = 0" by (simp del: p_modulo_pinverse_fls)
  thus "(f \<simeq>\<^sub>p 0)" using fls_pinv_eq0_iff by auto
qed simp

lemma fls_pinv_depth:
  "(f\<inverse>\<^sup>p)\<degree>\<^sup>p = -(f\<degree>\<^sup>p)" for f :: "'a fls"
proof (cases "f \<simeq>\<^sub>p 0")
  case False
  hence "(f\<inverse>\<^sup>p)\<degree>\<^sup>p = fls_subdegree (f\<inverse>\<^sup>p)"
    using fls_pinv_equiv0_iff[of f] fls_pinv_reduced[of f "fls_subdegree (f\<inverse>\<^sup>p)"]
          fls_pinv_eq0_iff[of f] nth_fls_subdegree_nonzero[of "f\<inverse>\<^sup>p"]
          p_depth_fls_rep_iff[of p _ "f\<inverse>\<^sup>p"]
    by    fastforce
  thus ?thesis using fls_pinv_subdegree by presburger
qed simp

lemma fls_pinv_eqI:
  "(f\<inverse>\<^sup>p) = g" if "g * f \<simeq>\<^sub>p 1" and "\<forall>n. (g $$ n) pdiv p = 0"
  for f g :: "'a fls"
proof-
  from that(1) have "f \<not>\<simeq>\<^sub>p 0"
    using p_equality_fls.mult_0_right fls_1_not_p_equal_0 p_equality_fls.trans_right by blast
  moreover from that(1)
    have  "g * ((f\<inverse>\<^sup>p) * f) \<simeq>\<^sub>p (f\<inverse>\<^sup>p)"
    using p_equality_fls.mult_one_left[of p "g * f" "f\<inverse>\<^sup>p"]
    by    (simp add: ac_simps)
  ultimately show ?thesis
    using that(2) fls_pmod_eqI[of p _ g] p_equality_fls.mult_left pinverse_fls_mult_equiv1
          p_equality_fls.trans_right[of p _ _ g]
    by    fastforce
qed

lemma fls_pinv_cong:
  "(f\<inverse>\<^sup>p) = (g\<inverse>\<^sup>p)" if "f \<simeq>\<^sub>p g" for f :: "'a fls"
proof (cases "g \<simeq>\<^sub>p 0")
  case True with that show ?thesis using p_equal_fls_trans by fastforce
next
  case False
  moreover from that have "(g\<inverse>\<^sup>p) * f \<simeq>\<^sub>p (g\<inverse>\<^sup>p) * g"
    using p_equality_fls.mult_left by fast
  ultimately show ?thesis
    using pinverse_fls_mult_equiv1 p_equal_fls_trans fls_pinv_eqI fls_pinv_reduced by blast
qed

lemma pinverse_p_modulo_fls:
  "(f pmod p)\<inverse>\<^sup>p = (f\<inverse>\<^sup>p)" for f :: "'a fls"
  using fls_pinv_cong p_equal_fls_sym fls_pmod_equiv by blast

lemma fls_pinv_X_intpow: "(fls_X_intpow n :: 'a fls)\<inverse>\<^sup>p = fls_X_intpow (-n)"
  by (intro fls_pinv_eqI, simp add: fls_times_both_shifted_simp, auto simp add: one_pdiv)

lemma fls_pinv_uminus: "(-f)\<inverse>\<^sup>p = (- (f\<inverse>\<^sup>p)) pmod p" for f :: "'a fls"
proof (cases "f \<simeq>\<^sub>p 0")
  case True thus ?thesis using p_equality_fls.uminus by fastforce
next
  case False
  hence "( (- (f\<inverse>\<^sup>p)) pmod p * - f) \<simeq>\<^sub>p 1"
    using fls_pmod_equiv[of p "(- (f\<inverse>\<^sup>p)) pmod p * - f"]
          fls_pmod_equiv[of p "(- (f\<inverse>\<^sup>p))"] p_equal_fls_refl[of p "-f"]
          p_equal_fls_sym[of p "(- (f\<inverse>\<^sup>p))" "(- (f\<inverse>\<^sup>p)) pmod p"]
          fls_pmod_equiv_times[of p _ "(- (f\<inverse>\<^sup>p))"] pinverse_fls
    by    fastforce
  thus ?thesis using fls_pinv_eqI fls_pmod_reduced by blast
qed

end (* context nontrivial_factorial_unique_euclidean_bezout *)

subsubsection \<open>Algebraic properties of inversion\<close>

context
  fixes p :: "'a::nontrivial_factorial_unique_euclidean_bezout prime"
begin

lemma fls_pinv0: "(0 :: 'a fls)\<inverse>\<^sup>p = 0"
  by simp

lemma fls_pinv1[simp]: "(1 :: 'a fls)\<inverse>\<^sup>p = 1"
  by (intro fls_pinv_eqI, simp_all, rule one_pdiv)

lemma fls_pinv_pinv:
  "((f\<inverse>\<^sup>p)\<inverse>\<^sup>p) = f pmod p" for f :: "'a fls"
proof (cases "f \<simeq>\<^sub>p 0")
  case False thus ?thesis
    using pinverse_times_p_modulo_fls fls_pmod_equiv mult.commute fls_pmod_reduced fls_pinv_eqI
    by    metis
qed simp

lemma fls_pinv_pinv_equiv:
  "((f\<inverse>\<^sup>p)\<inverse>\<^sup>p) \<simeq>\<^sub>p f" for f :: "'a fls"
  using fls_pinv_pinv[of f] fls_pmod_equiv p_equal_fls_sym by fastforce

lemma fls_pinv_mult:
  "(f * g)\<inverse>\<^sup>p = ((f\<inverse>\<^sup>p) * (g\<inverse>\<^sup>p)) pmod p"
  for f g :: "'a fls"
proof-
  have case0:
    "\<And>f g :: 'a fls.
      f \<simeq>\<^sub>p 0 \<Longrightarrow>
        (f * g)\<inverse>\<^sup>p = ((f\<inverse>\<^sup>p) * (g\<inverse>\<^sup>p)) pmod p"
  proof-
    fix f g :: "'a fls" assume "f \<simeq>\<^sub>p 0"
    thus "(f * g)\<inverse>\<^sup>p = ((f\<inverse>\<^sup>p) * (g\<inverse>\<^sup>p)) pmod p"
      using p_equality_fls.mult_0_left by fastforce
  qed
  consider
    "f \<simeq>\<^sub>p 0" | "g \<simeq>\<^sub>p 0" |
    (neither) "f \<not>\<simeq>\<^sub>p 0" "g \<not>\<simeq>\<^sub>p 0"
    by blast
  thus ?thesis
  proof (cases, metis case0, metis case0 mult.commute, intro fls_pinv_eqI)
    case neither
    hence "((f\<inverse>\<^sup>p) * f * ((g\<inverse>\<^sup>p) * g)) \<simeq>\<^sub>p 1"
      using p_equality_fls.mult pinverse_fls_mult_equiv1
      by    fastforce
    moreover have
      "(((f\<inverse>\<^sup>p) * (g\<inverse>\<^sup>p)) pmod p * (f * g)) \<simeq>\<^sub>p
        ((f\<inverse>\<^sup>p) * f * ((g\<inverse>\<^sup>p) * g))"
      using fls_pmod_equiv p_equal_fls_sym p_equality_fls.mult_right[of p _ _ "f * g"]
      by    (fastforce simp add: algebra_simps)
    ultimately
      show "((f\<inverse>\<^sup>p) * (g\<inverse>\<^sup>p) pmod p * (f * g)) \<simeq>\<^sub>p 1"
      using p_equal_fls_trans
      by    blast
    show "\<forall>n. ((f\<inverse>\<^sup>p) * (g\<inverse>\<^sup>p) pmod p) $$ n pdiv p = 0"
      using fls_pmod_reduced by fast
  qed
qed

lemma fls_pinv_mult_equiv:
  "((f * g)\<inverse>\<^sup>p) \<simeq>\<^sub>p (f\<inverse>\<^sup>p) * (g\<inverse>\<^sup>p)"
  for f g :: "'a fls"
  by (metis fls_pinv_mult fls_pmod_equiv p_equal_fls_sym)

lemma fls_pinv_pow:
  "(f ^ n)\<inverse>\<^sup>p = ((f\<inverse>\<^sup>p) ^ n) pmod p"
  for f g :: "'a fls"
proof (induct n)
  case (Suc n) thus ?case
    using fls_pinv_mult fls_pmod_equiv[of p "(f\<inverse>\<^sup>p) ^ n"]
          fls_pmod_equiv_times[of p "f\<inverse>\<^sup>p" "f\<inverse>\<^sup>p"]
    by    simp
qed simp

lemma fls_pinv_pow_equiv:
  "((f ^ n)\<inverse>\<^sup>p) \<simeq>\<^sub>p (f\<inverse>\<^sup>p) ^ n" for f :: "'a fls"
  by (metis fls_pinv_pow fls_pmod_equiv p_equal_fls_sym)

lemma fls_pinv_diff_cancel_lead_coeff:
  "(((f\<inverse>\<^sup>p) - (g\<inverse>\<^sup>p))\<degree>\<^sup>p) > -n"
  if  f : "f \<not>\<simeq>\<^sub>p 0" "f\<degree>\<^sup>p = n"
  and g : "g \<not>\<simeq>\<^sub>p 0" "g\<degree>\<^sup>p = n"
  and fg: "f \<not>\<simeq>\<^sub>p g" "((f - g)\<degree>\<^sup>p) > n"
  for f g :: "'a fls"
proof-
  from fg(1)
    have  inv_diff_n0: "((f\<inverse>\<^sup>p) - (g\<inverse>\<^sup>p)) \<not>\<simeq>\<^sub>p 0"
    by    (metis p_equality_fls.conv_0 fls_pinv_cong fls_pinv_pinv fls_pmod_eq_pmod_iff)
  moreover have "fls_subdegree ((f\<inverse>\<^sup>p) - (g\<inverse>\<^sup>p)) > -n"
  proof (rule fls_subdegree_greaterI)
    show "(f\<inverse>\<^sup>p) - (g\<inverse>\<^sup>p) \<noteq> 0" using inv_diff_n0 by fastforce
    fix k :: int
    from fg(2) have fg': "((f pmod p - g pmod p)\<degree>\<^sup>p) > n"
      using fls_pmod_depth fls_pmod_equiv fls_pmod_equiv_minus[of p f "f pmod p" g "g pmod p"]
      by    metis
    hence "fls_subdegree ((f pmod p - g pmod p) pmod p) > n" by (metis fls_pmod_subdegree)
    hence "((f pmod p - g pmod p) pmod p) $$ n = 0" by simp
    moreover have
      "((f pmod p - g pmod p) pmod p) $$ n =
        fls_partially_p_modulo_rep
          (f pmod p - g pmod p) (nat (n + 1 - fls_subdegree (f pmod p - g pmod p))) p n"
      using p_modulo_fls_nth[of "f pmod p - g pmod p" p n] by fastforce
    moreover from f(2) g(2) fg' have "fls_subdegree (f pmod p - g pmod p) \<ge> n"
      using fls_subdegree_minus[of "f pmod p" "g pmod p"]
            fls_pmod_subdegree[of f p] fls_pmod_subdegree[of g p]
      by    force
    ultimately have "((f pmod p) $$ n) pmod p = ((g pmod p) $$ n) pmod p"
      using mod_eq_dvd_iff by (cases "fls_subdegree (f pmod p - g pmod p) = n", force, simp)
    hence "(f pmod p) $$ n = (g pmod p) $$ n" using fls_pmod_pmod_nth by metis
    moreover from f(2) g(2)
      have  "k < -n \<Longrightarrow> ((f\<inverse>\<^sup>p) - (g\<inverse>\<^sup>p)) $$ k = 0"
      by    (simp add: fls_pinv_subdegree)
    ultimately
      show  "k \<le> -n \<Longrightarrow> ((f\<inverse>\<^sup>p) - (g\<inverse>\<^sup>p)) $$ k = 0"
      using f g
      by    (cases "k = -n", simp add: pinverse_fls_nth, simp)
  qed
  ultimately show ?thesis using p_depth_fls_ge_p_equal_subdegree' by fastforce
qed

end (* context *)


subsection \<open>Topology by place relative to indexed depth for formal Laurent series\<close>

subsubsection \<open>General pattern for constructing sequence limits\<close>

definition fls_condition_lim ::
  "'a::nontrivial_euclidean_ring_cancel prime \<Rightarrow> (nat \<Rightarrow> 'a fls) \<Rightarrow>
    (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> 'a fls"
  where
    "fls_condition_lim p F P =
      Abs_fls (\<lambda>n. (F (LEAST K. P (nat n) K) pmod p) $$ n)"

lemma fls_condition_lim_fun_ex_lower_bound:
  fixes p :: "'a::nontrivial_euclidean_ring_cancel prime"
    and F :: "nat \<Rightarrow> 'a fls"
    and P :: "int \<Rightarrow> nat \<Rightarrow> bool"
  defines
    "f \<equiv> (\<lambda>n. (F (LEAST K. P (nat n) K) pmod p) $$ n)"
  and
    "N \<equiv> min 0 (fls_subdegree ((F (LEAST K. P 0 K)) pmod p))"
  shows "\<forall>n<N. f n = 0"
  using assms by simp

lemma fls_condition_lim_nth:
  "fls_condition_lim p F P $$ n = ((F (LEAST K. P (nat n) K)) pmod p) $$ n"
  using nth_Abs_fls_lower_bound[OF fls_condition_lim_fun_ex_lower_bound, of F]
        fls_condition_lim_def[of p F]
  by    auto

lemma fls_pmod_condition_lim: "(fls_condition_lim p F P) pmod p = fls_condition_lim p F P"
  by (intro fls_pmod_eqI, simp_all add: fls_condition_lim_nth)


subsubsection \<open>Completeness\<close>

abbreviation "fls_p_limseq_condition      \<equiv> p_depth_fls.p_limseq_condition"
abbreviation "fls_p_limseq                \<equiv> p_depth_fls.p_limseq"
abbreviation "fls_p_cauchy_condition      \<equiv> p_depth_fls.p_cauchy_condition"
abbreviation "fls_p_cauchy                \<equiv> p_depth_fls.p_cauchy"

lemma fls_p_cauchy_condition_pmod_uniformity:
  "((F k) pmod p) $$ m = ((F k') pmod p) $$ m"
  if "fls_p_cauchy_condition p F n K" and "k \<ge> K" and "k' \<ge> K" and "m \<le> n"
  for p :: "'a::nontrivial_euclidean_ring_cancel prime" and F :: "nat \<Rightarrow> 'a fls"
  using that fls_pmod_cong[of p] fls_pmod_diff_cancel[of m p "F k" "F k'"]
        p_depth_fls.p_cauchy_conditionD
  by    fastforce

abbreviation
  "fls_p_cauchy_lim p X \<equiv>
    fls_condition_lim p X (\<lambda>n. fls_p_cauchy_condition p X (int n))"

lemma fls_p_cauchy_limseq: "fls_p_limseq p F (fls_p_cauchy_lim p F)" if "fls_p_cauchy p F"
proof
  fix n
  define K where "K \<equiv> (\<lambda>n. LEAST K. fls_p_cauchy_condition p F (int (nat n)) K)"
  have "fls_p_limseq_condition p F (fls_p_cauchy_lim p F) n (K n)"
  proof
    fix k assume k: "k \<ge> K n" "F k \<not>\<simeq>\<^sub>p (fls_p_cauchy_lim p F)"
    have "fls_subdegree ((F k pmod p) - fls_p_cauchy_lim p F) > n"
    proof (intro fls_subdegree_greaterI)
      from k(2) show "(F k) pmod p - (fls_p_cauchy_lim p F) \<noteq> 0"
        using fls_p_modulo_iff by auto
      fix j assume j: "j \<le> n"
      have "((F (K j)) pmod p) $$ j = ((F k) pmod p) $$ j"
      proof (intro fls_p_cauchy_condition_pmod_uniformity)
        from that K_def show "fls_p_cauchy_condition p F (int (nat j)) (K j)"
          using p_depth_fls.p_cauchy_condition_LEAST[of p F] by blast
        from j consider "j < 0" "n < 0" | "j < 0" "n \<ge> 0" | "j \<ge> 0" "n \<ge> 0"
          by linarith
        thus "k \<ge> K j"
          using that K_def k(1) j p_depth_fls.p_cauchy_condition_LEAST_mono
          by    cases (auto, fastforce, fastforce)
      qed simp_all
      with K_def have "(F k pmod p) $$ j = fls_p_cauchy_lim p F $$ j"
        by (metis fls_condition_lim_nth)
      thus "(F k pmod p - fls_p_cauchy_lim p F) $$ j = 0" by simp
    qed
    moreover from k(2) have
      "((F k - fls_p_cauchy_lim p F)\<degree>\<^sup>p) \<ge>
        fls_subdegree ((F k pmod p) - fls_p_cauchy_lim p F)"
      using p_equality_fls.conv_0[of p] p_equality_fls.minus[of p] fls_pmod_equiv[of p]
      by    (auto intro: p_depth_fls_ge_p_equal_subdegree)
    ultimately show "((F k - fls_p_cauchy_lim p F)\<degree>\<^sup>p) > n" by force
  qed
  thus "\<exists>K. fls_p_limseq_condition p F (fls_p_cauchy_lim p F) n K" by blast
qed

lemma fls_p_cauchy_lim_unique:
  "fls_p_cauchy_lim p F = fls_p_cauchy_lim p G"
  if "fls_p_cauchy p G" and "\<forall>n\<ge>N. (F n) \<simeq>\<^sub>p (G n)"
proof-
  have "fls_p_cauchy p F"
  proof
    fix n
    from that(1) obtain M where M: "fls_p_cauchy_condition p G n M" by force
    define K where "K \<equiv> max M N"
    have "fls_p_cauchy_condition p F n K"
    proof (intro p_depth_fls.p_cauchy_conditionI)
      fix k k' assume kk': "k \<ge> K" "k' \<ge> K" "(F k) \<not>\<simeq>\<^sub>p (F k')"
      moreover from that(2) K_def kk'(1,2)
        have  F_kk': "(F k) \<simeq>\<^sub>p (G k)" "(F k') \<simeq>\<^sub>p (G k')"
        by    auto
      ultimately have "k \<ge> M" and "k' \<ge> M" and "(G k) \<not>\<simeq>\<^sub>p (G k')"
        using K_def p_equality_fls.sym p_equality_fls.cong by (fastforce, fastforce, metis)
      with M show "((F k - F k')\<degree>\<^sup>p) > n"
        using F_kk' p_depth_fls.p_cauchy_conditionD[of p G n M k k'] p_depth_fls.depth_diff_equiv
        by    metis
    qed
    thus "\<exists>K. fls_p_cauchy_condition p F n K" by blast
  qed
  moreover from that have "fls_p_limseq p F (fls_p_cauchy_lim p G)"
    using fls_p_cauchy_limseq[of p G]
          p_depth_fls.p_limseq_p_cong[of N p F G "fls_p_cauchy_lim p G" "fls_p_cauchy_lim p G"]
    by    auto
  ultimately show ?thesis
    by (metis fls_p_cauchy_limseq p_depth_fls.p_limseq_unique fls_pmod_cong fls_pmod_condition_lim)
qed


subsection \<open>Transfer to prime-indexed sequences of formal Laurent series\<close>

subsubsection \<open>Equivalence and depth\<close>

text \<open>
The equivalence is by divisibility of the difference of each pair of corresponding
terms by the index for those terms.
\<close>

type_synonym 'a fls_pseq = "'a prime \<Rightarrow> 'a fls"

overloading
  p_equal_fls_pseq \<equiv>
    "p_equal :: 'a::nontrivial_factorial_semiring prime \<Rightarrow>
      'a fls_pseq \<Rightarrow> 'a fls_pseq \<Rightarrow> bool"
  p_restrict_fls_pseq \<equiv>
    "p_restrict ::
      'a fls_pseq \<Rightarrow> ('a prime \<Rightarrow> bool) \<Rightarrow> 'a fls_pseq"
  p_depth_fls_pseq \<equiv>
    "p_depth :: 'a prime \<Rightarrow> 'a fls_pseq \<Rightarrow> int"
  global_unfrmzr_pows_fls_pseq \<equiv>
    "global_unfrmzr_pows :: ('a prime \<Rightarrow> int) \<Rightarrow> 'a fls_pseq"
begin

definition p_equal_fls_pseq ::
  "'a::nontrivial_factorial_semiring prime \<Rightarrow>
    'a fls_pseq \<Rightarrow> 'a fls_pseq \<Rightarrow> bool"
  where p_equal_fls_pseq_def[simp]: "p_equal_fls_pseq p X Y \<equiv> (X p) \<simeq>\<^sub>p (Y p)"

definition p_restrict_fls_pseq ::
  "'a::nontrivial_factorial_semiring fls_pseq \<Rightarrow>
    ('a prime \<Rightarrow> bool) \<Rightarrow> 'a fls_pseq"
  where
    "p_restrict_fls_pseq X P \<equiv> (\<lambda>p::'a prime. if P p then X p else 0)"

definition p_depth_fls_pseq ::
  "'a::nontrivial_factorial_semiring prime \<Rightarrow> 'a fls_pseq \<Rightarrow> int"
  where p_depth_fls_pseq_def[simp]: "p_depth_fls_pseq p X \<equiv> (X p)\<degree>\<^sup>p"

definition global_unfrmzr_pows_fls_pseq ::
  "('a::nontrivial_factorial_semiring prime \<Rightarrow> int) \<Rightarrow> 'a fls_pseq"
  where "global_unfrmzr_pows_fls_pseq f \<equiv> (\<lambda>p::'a prime. fls_X_intpow (f p))"

end  (* overloading *)

global_interpretation p_equality_depth_fls_pseq:
  global_p_equality_depth_no_zero_divisors_1
    "p_equal :: 'a::nontrivial_factorial_idom prime \<Rightarrow>
      'a fls_pseq \<Rightarrow> 'a fls_pseq \<Rightarrow> bool"
    "p_restrict ::
      'a fls_pseq \<Rightarrow> ('a prime \<Rightarrow> bool) \<Rightarrow> 'a fls_pseq"
    "p_depth :: 'a prime \<Rightarrow> 'a fls_pseq \<Rightarrow> int"
proof
(* 
 (
  unfold_locales,
  simp_all add:
    p_equality_fls.mult_0_right p_depth_fls.no_zero_divisors p_restrict_fls_pseq_def
    p_depth_fls.depth_equiv p_depth_fls.depth_uminus p_depth_fls.depth_pre_nonarch(1)
    p_depth_fls.depth_mult_additive zero_fun_def
)
 *)
  fix p :: "'a prime"
  define
    E :: "'a fls_pseq \<Rightarrow> 'a fls_pseq \<Rightarrow> bool"
    where "E \<equiv> p_equal p"
  thus "equivp E"
    using     equivp_transfer p_equality_fls.equivp
    unfolding p_equal_fls_pseq_def
    by        fast

  fix X Y :: "'a fls_pseq"
  show "(X \<simeq>\<^sub>p Y) = ((X - Y) \<simeq>\<^sub>p 0)" using p_equality_fls.conv_0 by auto
  have "(\<lambda>q::'a prime. (1::'a fls)) \<not>\<simeq>\<^sub>p 0"
    by (auto simp add: fls_1_not_p_equal_0)
  thus "\<exists>X::'a fls_pseq. X \<not>\<simeq>\<^sub>p 0" by auto

  show
    "\<lbrakk>
        X \<not>\<simeq>\<^sub>p 0; X + Y \<not>\<simeq>\<^sub>p 0;
        (X\<degree>\<^sup>p) = (Y\<degree>\<^sup>p)
    \<rbrakk> \<Longrightarrow> (X\<degree>\<^sup>p) \<le> ((X + Y)\<degree>\<^sup>p)"
    using p_depth_fls.depth_pre_nonarch(2) by fastforce

qed (
  simp_all add:
    p_equality_fls.mult_0_right p_depth_fls.no_zero_divisors p_restrict_fls_pseq_def
    p_depth_fls.depth_equiv p_depth_fls.depth_uminus p_depth_fls.depth_pre_nonarch(1)
    p_depth_fls.depth_mult_additive
)

overloading
  globally_p_equal_fls_pseq \<equiv>
    "globally_p_equal :: 'a::nontrivial_factorial_idom fls_pseq \<Rightarrow>
      'a fls_pseq \<Rightarrow> bool"
  p_depth_set_fls_pseq \<equiv>
    "p_depth_set ::
      'a::nontrivial_factorial_idom prime \<Rightarrow> int \<Rightarrow> 'a fls_pseq set"
  global_depth_set_fls_pseq \<equiv>
    "global_depth_set :: int \<Rightarrow> 'a fls_pseq set"
begin

definition globally_p_equal_fls_pseq ::
  "'a::nontrivial_factorial_idom fls_pseq \<Rightarrow> 'a fls_pseq \<Rightarrow> bool"
  where globally_p_equal_fls_pseq_def[simp]:
    "globally_p_equal_fls_pseq = p_equality_depth_fls_pseq.globally_p_equal"

definition p_depth_set_fls_pseq ::
  "'a::nontrivial_factorial_idom prime \<Rightarrow> int \<Rightarrow> 'a fls_pseq set"
  where p_depth_set_fls_pseq_def[simp]:
    "p_depth_set_fls_pseq = p_equality_depth_fls_pseq.p_depth_set"

definition global_depth_set_fls_pseq ::
  "int \<Rightarrow> 'a::nontrivial_factorial_idom fls_pseq set"
  where global_depth_set_fls_pseq_def[simp]:
    "global_depth_set_fls_pseq = p_equality_depth_fls_pseq.global_depth_set"

end

lemma fls_pseq_globally_reduced:
  "X \<simeq>\<^sub>\<forall>\<^sub>p (\<lambda>p. (X p) pmod p)"
  for X :: "'a::nontrivial_euclidean_ring_cancel fls_pseq"
  unfolding p_equal_fls_pseq_def using fls_pmod_equiv by fastforce

lemma global_unfrmzr_pows0_fls_pseq:
  "(\<pp> (0 :: 'a::nontrivial_factorial_idom prime \<Rightarrow> int) :: 'a fls_pseq) = 1"
  unfolding global_unfrmzr_pows_fls_pseq_def by auto

context
  fixes p :: "'a::nontrivial_factorial_idom prime"
begin

lemma global_unfrmzr_pows_fls_pseq_nequiv0:
  "(\<pp> f :: 'a fls_pseq) \<not>\<simeq>\<^sub>p 0" for f :: "'a prime \<Rightarrow> int"
  by (simp add: global_unfrmzr_pows_fls_pseq_def fls_X_intpow_nequiv0)

lemma global_unfrmzr_pows_fls_pseq:
  "(\<pp> f :: 'a fls_pseq)\<degree>\<^sup>p = f p" for f :: "'a prime \<Rightarrow> int"
  by (simp add: global_unfrmzr_pows_fls_pseq_def p_depth_fls_X_intpow)

lemma global_unfrmzr_pows_fls_pseq_pequiv_iff:
  "(\<pp> f:: 'a fls_pseq) \<simeq>\<^sub>p (\<pp> g) \<longleftrightarrow> f p = g p"
  for f g :: "'a prime \<Rightarrow> int"
  using p_equal_fls_X_intpow_iff unfolding global_unfrmzr_pows_fls_pseq_def by auto

end (* context nontrivial_factorial_idom *)

lemma global_unfrmzr_pows_prod_fls_pseq:
  "(\<pp> f :: 'a fls_pseq) * (\<pp> g) = \<pp> (f + g)"
  for f g :: "'a::nontrivial_factorial_idom prime \<Rightarrow> int"
proof (standard)
  fix p :: "'a prime"
  define \<pp>f \<pp>g :: "'a fls_pseq"
    where "\<pp>f \<equiv> \<pp> f" and "\<pp>g \<equiv> \<pp> g"
  hence "\<pp>f p * \<pp>g p = fls_shift (- f p + - g p) (1 * 1)"
    using fls_times_both_shifted_simp unfolding global_unfrmzr_pows_fls_pseq_def by metis
  thus "(\<pp>f * \<pp>g) p = \<pp> (f + g) p" unfolding global_unfrmzr_pows_fls_pseq_def by simp
qed

context
  fixes p :: "'a::nontrivial_factorial_idom prime"
begin

lemma global_unfrmzr_pows_fls_pseq_nzero:
  "(\<pp> f :: 'a fls_pseq) \<not>\<simeq>\<^sub>p 0" for f :: "'a prime \<Rightarrow> int"
proof-
  define P :: "('a prime \<Rightarrow> int) \<Rightarrow> 'a fls_pseq" where "P \<equiv> \<pp>"
  hence *: "\<And>f. P f \<simeq>\<^sub>p 0 \<Longrightarrow> f p = 0"
    using global_unfrmzr_pows_fls_pseq p_equality_depth_fls_pseq.depth_equiv_0 by metis
  from P_def have "\<not> P f \<simeq>\<^sub>p 0"
    using *[of f] *[of "f + (\<lambda>p. 1)"] global_unfrmzr_pows_prod_fls_pseq[of f]
          p_equality_depth_fls_pseq.mult_0_left[of p _ "P (\<lambda>p. 1)"]
    by    fastforce
  with P_def show ?thesis by blast
qed

lemma prod_w_global_unfrmzr_pows_fls_pseq:
  "(X * \<pp> f)\<degree>\<^sup>p = (X\<degree>\<^sup>p) + f p" if "X \<not>\<simeq>\<^sub>p 0"
  for X :: "'a fls_pseq" and f :: "'a prime \<Rightarrow> int"
  using that global_unfrmzr_pows_fls_pseq_nzero p_equality_depth_fls_pseq.no_zero_divisors
        global_unfrmzr_pows_fls_pseq p_equality_depth_fls_pseq.depth_mult_additive
  by    metis

lemma normalize_depth_fls_pseq:
  "(X * \<pp> (\<lambda>p::'a prime. -(X\<degree>\<^sup>p)))\<degree>\<^sup>p = 0"
  for X :: "'a fls_pseq"
  using prod_w_global_unfrmzr_pows_fls_pseq p_equality_depth_fls_pseq.depth_equiv_0
        p_equality_depth_fls_pseq.mult_0_left[of p X]
  by    fastforce

end (* context nontrivial_factorial_idom *)

lemma normalized_depth_fls_pseq_product_additive:
  "(X * \<pp> (\<lambda>p::'a prime. -(X\<degree>\<^sup>p))) *
    (Y * \<pp> (\<lambda>p::'a prime. -(Y\<degree>\<^sup>p))) =
      ((X * Y) * \<pp> (\<lambda>p::'a prime. -((X\<degree>\<^sup>p) + (Y\<degree>\<^sup>p))))"
  for X Y :: "'a::nontrivial_factorial_idom fls_pseq"
  by (simp add: algebra_simps global_unfrmzr_pows_prod_fls_pseq plus_fun_def)

context
  fixes p :: "'a::nontrivial_factorial_idom prime"
begin

lemma normalized_depth_fls_pseq_product_equiv:
  "(X * \<pp> (\<lambda>p::'a prime. -(X\<degree>\<^sup>p))) *
    (Y * \<pp> (\<lambda>p::'a prime. -(Y\<degree>\<^sup>p))) \<simeq>\<^sub>p
      ((X * Y) * \<pp> (\<lambda>p::'a prime. -((X * Y)\<degree>\<^sup>p)))"
  for X Y :: "'a fls_pseq"
proof (cases "X * Y \<simeq>\<^sub>p 0")
  case True thus ?thesis
    using normalized_depth_fls_pseq_product_additive[of X Y]
          p_equality_depth_fls_pseq.trans_left[of p _ 0]
          p_equality_depth_fls_pseq.mult_0_left[of p]
    by    presburger
next
  case False thus ?thesis
    using global_unfrmzr_pows_fls_pseq_pequiv_iff[of p]
          p_equality_depth_fls_pseq.depth_mult_additive[of p X Y]
          normalized_depth_fls_pseq_product_additive[of X Y]
          p_equality_depth_fls_pseq.mult_left[of p _ _ "X * Y"]
    by    simp
qed

lemma trivial_global_unfrmzr_pows_fls_pseq:
  "(\<pp> f :: 'a fls_pseq) \<simeq>\<^sub>p 1" if "f p = 0" for f :: "'a prime \<Rightarrow> int"
  using that unfolding global_unfrmzr_pows_fls_pseq_def by auto

lemma prod_w_trivial_global_unfrmzr_pows_fls_pseq:
  "X * \<pp> f \<simeq>\<^sub>p X" if "f p = 0"
  for f :: "'a prime \<Rightarrow> int" and X :: "'a fls_pseq"
  using that trivial_global_unfrmzr_pows_fls_pseq p_equality_depth_fls_pseq.mult_left by fastforce

end (* context nontrivial_factorial_idom *)

lemma pow_global_unfrmzr_pows_fls_pseq:
  "(\<pp> f :: 'a fls_pseq) ^ n = (\<pp> (\<lambda>p::'a prime. int n * f p))"
  for f :: "'a::nontrivial_factorial_idom prime \<Rightarrow> int"
  by (
    induct n, simp flip: zero_fun_def one_fun_def, rule global_unfrmzr_pows0_fls_pseq,
    simp add: global_unfrmzr_pows_prod_fls_pseq plus_fun_def algebra_simps
  )

lemma global_unfrmzr_pows_fls_pseq_inv:
  "(\<pp> (-f) :: 'a fls_pseq) * (\<pp> f) = 1"
  for f :: "'a::nontrivial_factorial_idom prime \<Rightarrow> int"
  using global_unfrmzr_pows_prod_fls_pseq[of "-f" f] global_unfrmzr_pows0_fls_pseq by fastforce

lemma global_unfrmzr_pows_fls_pseq_decomp:
  "X = (
    (X * \<pp> (\<lambda>p::'a prime. -(X\<degree>\<^sup>p))) *
    \<pp> (\<lambda>p::'a prime. X\<degree>\<^sup>p)
  )"
  for X :: "'a::nontrivial_factorial_idom fls_pseq"
proof-
  have
    "- (\<lambda>p::'a prime. X\<degree>\<^sup>p) = (\<lambda>p::'a prime. -(X\<degree>\<^sup>p))"
    by force
  thus ?thesis
    using global_unfrmzr_pows_fls_pseq_inv[of "\<lambda>p::'a prime. (X\<degree>\<^sup>p)"]
    by    (simp add: algebra_simps)
qed

context
  fixes p :: "'a::nontrivial_factorial_idom prime"
begin

lemma global_unfrmzr_pth_fls_pseq:
  "(\<pp> (1 :: ('a prime \<Rightarrow> int)) p :: 'a fls) \<simeq>\<^sub>p
    (fls_const (Rep_prime p))"
proof (rule iffD2, rule p_equal_fls_extended_intsum_iff, safe)
  define pp where "pp \<equiv> Rep_prime p"
  define \<pp>1p :: "'a fls" where "\<pp>1p \<equiv> \<pp> (1 :: 'a prime \<Rightarrow> int) p"
  from pp_def \<pp>1p_def
    show      "0 \<le> min (fls_subdegree \<pp>1p) (fls_subdegree (fls_const pp))"
    unfolding global_unfrmzr_pows_fls_pseq_def
    by        simp
  fix n::int assume "n \<ge> 0"
  moreover have
    "n \<ge> 1 \<Longrightarrow>
      (\<Sum>k=0..n. (\<pp>1p - fls_const pp) $$ k * pp ^ nat (k - 0)) = 0"
  proof (induct n rule: int_ge_induct)
    case base
    have "{0..1::int} = {0,1}" by fastforce
    thus ?case unfolding \<pp>1p_def  global_unfrmzr_pows_fls_pseq_def by fastforce
  next
    case (step n)
    moreover from step(1) have "{0..n + 1} = insert (n + 1) {0..n}" by fastforce
    ultimately show ?case unfolding \<pp>1p_def global_unfrmzr_pows_fls_pseq_def by fastforce
  qed
  ultimately show
    "pp ^ Suc (nat (n - 0)) dvd (\<Sum>k=0..n. (\<pp>1p - fls_const pp) $$ k * pp ^ nat (k - 0))"
    by (
      cases "n = 0" "n = 1" rule: case_split[case_product case_split],
      simp_all add: \<pp>1p_def global_unfrmzr_pows_fls_pseq_def
    )
qed

lemma global_unfrmzr_fls_pseq:
  "(\<pp> (1 :: ('a prime \<Rightarrow> int)) :: 'a fls_pseq) \<simeq>\<^sub>p
    (\<lambda>p::'a prime. fls_const (Rep_prime p))"
  using p_equal_fls_pseq_def global_unfrmzr_pth_fls_pseq by fast

end (* context nontrivial_factorial_idom *)

lemma normalize_depth_fls_pseqE:
  fixes   X :: "'a::nontrivial_factorial_idom fls_pseq"
  obtains X_0
  where   "\<forall>p::'a prime. X_0\<degree>\<^sup>p = 0"
  and     "X = X_0 * \<pp> (\<lambda>p::'a prime. X\<degree>\<^sup>p)"
  using   normalize_depth_fls_pseq global_unfrmzr_pows_fls_pseq_decomp
  by      blast


subsubsection \<open>Inversion\<close>

abbreviation global_pinverse_fls_pseq ::
  "'a::nontrivial_factorial_comm_ring fls_pseq \<Rightarrow> 'a fls_pseq"
  ("(_\<inverse>\<^sup>\<forall>\<^sup>p)" [51] 50)
  where "global_pinverse_fls_pseq X \<equiv> (\<lambda>p. (X p)\<inverse>\<^sup>p)"

context
  fixes X :: "'a::nontrivial_factorial_unique_euclidean_bezout fls_pseq"
begin

lemma global_pinverse_fls_pseq_eq0[simp]:
  "(X\<inverse>\<^sup>\<forall>\<^sup>p) = 0" if "X \<simeq>\<^sub>\<forall>\<^sub>p 0"
  using that p_equality_depth_fls_pseq.globally_p_equalD by fastforce

lemma global_pinverse_fls_pseq_eq0_iff:
  "(X\<inverse>\<^sup>\<forall>\<^sup>p) = 0 \<longleftrightarrow>
    X \<simeq>\<^sub>\<forall>\<^sub>p 0"
proof
  assume X: "(X\<inverse>\<^sup>\<forall>\<^sup>p) = 0"
  have "\<forall>p. X p \<simeq>\<^sub>p 0"
  proof
    fix p :: "'a prime"
    have "\<not> (X \<not>\<simeq>\<^sub>p 0)"
    proof
      assume "X \<not>\<simeq>\<^sub>p 0"
      hence "(X\<inverse>\<^sup>\<forall>\<^sup>p) p \<noteq> 0" using fls_pinv_eq0_iff by auto
      with X show False using zero_fun_def by metis
    qed
    thus "X p \<simeq>\<^sub>p 0" by fastforce
  qed
  thus "X \<simeq>\<^sub>\<forall>\<^sub>p 0" by simp
qed (rule global_pinverse_fls_pseq_eq0)

lemma global_pinverse_fls_pseq_equiv0_iff:
  "(X\<inverse>\<^sup>\<forall>\<^sup>p) \<simeq>\<^sub>\<forall>\<^sub>p 0 \<longleftrightarrow>
    X \<simeq>\<^sub>\<forall>\<^sub>p 0"
  using     fls_pinv_equiv0_iff
  unfolding globally_p_equal_fls_pseq_def p_equality_depth_fls_pseq.globally_p_equal_def
  by        fastforce

lemma global_left_pinverse_fls_pseq:
  "(X\<inverse>\<^sup>\<forall>\<^sup>p) * X  \<simeq>\<^sub>\<forall>\<^sub>p
    (\<lambda>p. of_bool (X \<not>\<simeq>\<^sub>p 0))"
  using pinverse_fls_mult_equiv1 by fastforce

lemma global_right_pinverse_fls_pseq:
  "X * (X\<inverse>\<^sup>\<forall>\<^sup>p) \<simeq>\<^sub>\<forall>\<^sub>p
    (\<lambda>p. of_bool (X \<not>\<simeq>\<^sub>p 0))"
  using global_left_pinverse_fls_pseq mult.commute[of X] by presburger

lemma global_left_pinverse_fls_pseq':
  "(X\<inverse>\<^sup>\<forall>\<^sup>p) * X \<simeq>\<^sub>p 1" if "X \<not>\<simeq>\<^sub>p 0"
  for p :: "'a prime"
  using that global_left_pinverse_fls_pseq p_equality_depth_fls_pseq.globally_p_equalD[of _ _ p]
  by    fastforce

lemma global_right_pinverse_fls_pseq':
  "X * (X\<inverse>\<^sup>\<forall>\<^sup>p) \<simeq>\<^sub>p 1" if "X \<not>\<simeq>\<^sub>p 0"
  for p :: "'a prime"
  using that global_left_pinverse_fls_pseq' by (simp add: mult.commute)

lemma global_pinverse_pinverse_fls_pseq:
  "((X\<inverse>\<^sup>\<forall>\<^sup>p)\<inverse>\<^sup>\<forall>\<^sup>p)
    \<simeq>\<^sub>\<forall>\<^sub>p X"
  using fls_pinv_pinv_equiv by fastforce

lemma global_pinverse_mult_fls_pseq:
  "((X * Y)\<inverse>\<^sup>\<forall>\<^sup>p) \<simeq>\<^sub>\<forall>\<^sub>p
    (X\<inverse>\<^sup>\<forall>\<^sup>p) * (Y\<inverse>\<^sup>\<forall>\<^sup>p)"
  using fls_pinv_mult_equiv by fastforce

lemma global_pinverse_pow_fls_pseq:
  "((X ^ n)\<inverse>\<^sup>\<forall>\<^sup>p) \<simeq>\<^sub>\<forall>\<^sub>p
    (X\<inverse>\<^sup>\<forall>\<^sup>p) ^ n"
  by (simp, standard, metis pow_fun_apply fls_pinv_pow_equiv)

lemma global_pinverse_uminus_fls_pseq:
  "((-X)\<inverse>\<^sup>\<forall>\<^sup>p) \<simeq>\<^sub>\<forall>\<^sub>p
    - (X\<inverse>\<^sup>\<forall>\<^sup>p)"
  by (simp, standard, metis fls_pinv_uminus fls_pmod_equiv p_equal_fls_sym)

end (* context *)

lemma globally_pinverse_pcong:
  "(X\<inverse>\<^sup>\<forall>\<^sup>p) \<simeq>\<^sub>p (Y\<inverse>\<^sup>\<forall>\<^sup>p)"
  if    "X \<simeq>\<^sub>p Y"
  for p :: "'a::nontrivial_factorial_unique_euclidean_bezout prime" and X Y :: "'a fls_pseq"
  using that fls_pinv_cong
  by    fastforce

lemma globally_pinverse_cong:
  "(X\<inverse>\<^sup>\<forall>\<^sup>p) \<simeq>\<^sub>\<forall>\<^sub>p
    (Y\<inverse>\<^sup>\<forall>\<^sup>p)"
  if  "X \<simeq>\<^sub>\<forall>\<^sub>p Y"
  for X Y :: "'a::nontrivial_factorial_unique_euclidean_bezout fls_pseq"
  using that p_equality_depth_fls_pseq.globally_p_equalD globally_pinverse_pcong by fastforce

lemma globally_pinverse_global_unfrmzr_pows:
  "(\<pp> f :: 'a fls_pseq)\<inverse>\<^sup>\<forall>\<^sup>p = \<pp> (- f)"
  for f :: "'a::nontrivial_factorial_unique_euclidean_bezout prime \<Rightarrow> int"
  using fls_pinv_X_intpow unfolding global_unfrmzr_pows_fls_pseq_def by auto

lemma global_pinverse_fls_pseq0:
  "(
    (0::'a::nontrivial_factorial_unique_euclidean_bezout fls_pseq)\<inverse>\<^sup>\<forall>\<^sup>p
  ) = 0"
  by fastforce

lemma global_pinverse_fls_pseq1:
  "(
    (1::'a::nontrivial_factorial_unique_euclidean_bezout fls_pseq)\<inverse>\<^sup>\<forall>\<^sup>p
  ) = 1"
  by auto

lemma global_pinverse_diff_cancel_lead_coeff:
  "((
    (X\<inverse>\<^sup>\<forall>\<^sup>p) -
    (Y\<inverse>\<^sup>\<forall>\<^sup>p)
  )\<degree>\<^sup>p) > -n"
  if  "X \<not>\<simeq>\<^sub>p 0" and "X\<degree>\<^sup>p = n"
  and "Y \<not>\<simeq>\<^sub>p 0" and "Y\<degree>\<^sup>p = n"
  and "X \<not>\<simeq>\<^sub>p Y" and "((X - Y)\<degree>\<^sup>p) > n"
  for p   :: "'a::nontrivial_factorial_unique_euclidean_bezout prime"
  and X Y :: "'a fls_pseq"
  using that fls_pinv_diff_cancel_lead_coeff by auto

subsubsection \<open>Topology via global bounded depth\<close>

abbreviation "fls_pseq_bdd_global_depth \<equiv> p_equality_depth_fls_pseq.bdd_global_depth"
abbreviation "fls_pseq_bdd_global_dist  \<equiv> p_equality_depth_fls_pseq.bdd_global_dist"
abbreviation "fls_pseq_globally_cauchy  \<equiv> p_equality_depth_fls_pseq.globally_cauchy"
abbreviation
  "fls_pseq_global_cauchy_condition  \<equiv> p_equality_depth_fls_pseq.global_cauchy_condition"

lemma fls_pseq_global_cauchy_condition_pmod_uniformity:
  "((X k p) pmod p) $$ m = ((X k' p) pmod p) $$ m"
  if "fls_pseq_global_cauchy_condition X n K" and "k \<ge> K" and "k' \<ge> K" and "m \<le> int n"
  for p :: "'a::nontrivial_euclidean_ring_cancel prime" and X :: "nat \<Rightarrow> 'a fls_pseq"
  using that fls_pmod_cong[of p] fls_pmod_diff_cancel[of m p "X k p" "X k' p"]
        p_equality_depth_fls_pseq.global_cauchy_conditionD
  by    fastforce

abbreviation
  "fls_pseq_cauchy_lim X \<equiv>
    \<lambda>p. fls_condition_lim p (\<lambda>n. X n p) (fls_pseq_global_cauchy_condition X)"

lemma fls_pseq_cauchy_condition_lim:
  "\<forall>\<^sub>F k in sequentially. fls_pseq_bdd_global_dist (X k) (fls_pseq_cauchy_lim X) < e"
  if  pos: "e > 0" and cauchy: "fls_pseq_globally_cauchy X"
proof-
  define limval where
    "limval \<equiv>
      \<lambda>p. fls_condition_lim p (\<lambda>n. (X n) p) (fls_pseq_global_cauchy_condition X)"
  show "\<forall>\<^sub>F k in sequentially. fls_pseq_bdd_global_dist (X k) limval < e"
  proof (cases "e > 1")
    case True
    hence "\<And>n. fls_pseq_bdd_global_dist (X n) limval < e"
      using p_equality_depth_fls_pseq.bdd_global_dist_bdd order_le_less_subst1[of _ id 1 e]
      by    fastforce
    thus ?thesis by simp
  next
    case False show ?thesis
    proof (standard, intro p_equality_depth_fls_pseq.bdd_global_dist_lessI pos)
      fix n :: nat and p :: "'a prime"
      define d where "d \<equiv> \<lfloor>log 2 (inverse e)\<rfloor>"
      define K :: "int \<Rightarrow> nat"
        where "K \<equiv> \<lambda>n. (LEAST K. fls_pseq_global_cauchy_condition X (nat n) K)"
      assume n: "n \<ge> K d" "X n \<not>\<simeq>\<^sub>p limval"
      have "fls_subdegree (((X n p) pmod p) - limval p) \<ge> d"
      proof (intro fls_subdegree_geI)
        from n(2) show "(X n p) pmod p - limval p \<noteq> 0" using fls_p_modulo_iff by auto
        fix j assume j: "j < d"
        have "((X (K j) p) pmod p) $$ j = ((X n p) pmod p) $$ j"
        proof (intro fls_pseq_global_cauchy_condition_pmod_uniformity)
          from cauchy K_def show "fls_pseq_global_cauchy_condition X (nat j) (K j)"
            using p_equality_depth_fls_pseq.global_cauchy_condition_LEAST[of X "nat j"]
            by    fastforce
          from cauchy n j K_def show "K j \<le> n"
            using p_equality_depth_fls_pseq.global_cauchy_condition_LEAST_mono[of X "nat j" "nat d"]
            by    fastforce
        qed simp_all
        with K_def limval_def have "(X n p pmod p) $$ j = limval p $$ j"
          by (metis fls_condition_lim_nth)
        thus "(X n p pmod p - limval p) $$ j = 0" by auto
      qed
      moreover from n(2) have
        "((X n - limval)\<degree>\<^sup>p) \<ge>
          fls_subdegree ((X n p pmod p) - limval p)"
        using p_equality_fls.conv_0[of p] p_equality_fls.minus[of p] fls_pmod_equiv[of p]
        by    (auto intro: p_depth_fls_ge_p_equal_subdegree)
      ultimately show "((X n - limval)\<degree>\<^sup>p) \<ge> d" by simp
    qed
  qed
qed

end  (* theory *)
