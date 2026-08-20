theory Combinatorial_Nullstellensatz
  imports "HOL-Computational_Algebra.Polynomial"
begin

section \<open>Alon's Combinatorial Nullstellensatz\<close>

text \<open>
  Alon's Combinatorial Nullstellensatz \<^cite>\<open>Alon1999\<close> is a
  polynomial method theorem: if the coefficient of a distinguished monomial
  of total degree \<open>d\<^sub>1 + \<dots> + d\<^sub>n\<close> is nonzero, then the polynomial cannot
  vanish on every point of any grid whose \<open>i\<close>-th side has more than
  \<open>d\<^sub>i\<close> elements.

  The development below proves this statement for sparse multivariate
  polynomials over arbitrary fields.  A polynomial is represented by a
  finite-support coefficient function from exponent lists to coefficients.
  This keeps the formalization independent of a particular multivariate
  polynomial library while still matching the usual mathematical statement.
\<close>

subsection \<open>Univariate interpolation\<close>

text \<open>
  The proof starts with a small amount of univariate interpolation.  For a
  finite set \<open>S\<close> and a point \<open>x \<in> S\<close>, the following denominator and basis
  polynomial are the standard Lagrange factors.
\<close>

definition lagrange_denom :: "'a::field set \<Rightarrow> 'a \<Rightarrow> 'a" where
  "lagrange_denom S x = (\<Prod>y\<in>S - {x}. x - y)"

definition lagrange_basis :: "'a::field set \<Rightarrow> 'a \<Rightarrow> 'a poly" where
  "lagrange_basis S x =
     smult (inverse (lagrange_denom S x))
       (\<Prod>y\<in>S - {x}. [:- y, 1:])"

lemma lagrange_denom_nonzero:
  assumes "finite S" "x \<in> S"
  shows "lagrange_denom S x \<noteq> 0"
  using assms by (auto simp: lagrange_denom_def)

lemma poly_lagrange_basis:
  assumes "finite S" "x \<in> S" "z \<in> S"
  shows "poly (lagrange_basis S x) z = (if z = x then 1 else 0)"
proof (cases "z = x")
  case True
  have "poly (\<Prod>y\<in>S - {x}. [:- y, 1:]) x = lagrange_denom S x"
    by (simp add: lagrange_denom_def poly_prod)
  with assms True lagrange_denom_nonzero[of S x] show ?thesis
    by (simp add: lagrange_basis_def)
next
  case False
  with assms have "z \<in> S - {x}"
    by simp
  then have "poly (\<Prod>y\<in>S - {x}. [:- y, 1:]) z = 0"
    using assms by (simp add: poly_prod)
  with False show ?thesis
    by (simp add: lagrange_basis_def)
qed

lemma degree_lagrange_basis_le:
  assumes "finite S" "x \<in> S"
  shows "degree (lagrange_basis S x) \<le> card S - 1"
proof -
  have "degree (\<Prod>y\<in>S - {x}. [:- y, 1:] :: 'a poly)
      = (\<Sum>y\<in>S - {x}. degree ([:- y, 1:] :: 'a::field poly))"
    using assms by (intro degree_prod_sum_eq) auto
  also have "\<dots> \<le> card S - 1"
    using assms by auto
  finally show ?thesis
    by (simp add: lagrange_basis_def degree_smult_le dual_order.trans)
qed

lemma lagrange_interpolation:
  fixes P :: "'a::{field,ring_no_zero_divisors} poly"
  assumes fin: "finite S" and deg: "degree P < card S"
  shows "P = (\<Sum>x\<in>S. smult (poly P x) (lagrange_basis S x))"
proof (rule poly_eqI_degree[where A = S])
  fix z
  assume z: "z \<in> S"
  have "poly (\<Sum>x\<in>S. smult (poly P x) (lagrange_basis S x)) z =
      (\<Sum>x\<in>S. poly P x * poly (lagrange_basis S x) z)"
    by (simp add: poly_sum)
  also have "\<dots> = poly P z"
    using fin z
    by (subst sum.remove[of S z]) (auto simp: poly_lagrange_basis eq_commute)
  finally show "poly P z = poly (\<Sum>x\<in>S. smult (poly P x) (lagrange_basis S x)) z"
    by simp
next
  show "card S > degree P"
    using deg by simp
next
  have "degree (\<Sum>x\<in>S. smult (poly P x) (lagrange_basis S x)) \<le> card S - 1"
  proof (intro degree_sum_le fin)
    fix x
    assume "x \<in> S"
    then show "degree (smult (poly P x) (lagrange_basis S x)) \<le> card S - 1"
      by (meson degree_lagrange_basis_le degree_smult_le fin order_trans)
  qed
  moreover from deg have "card S > 0"
    by simp
  ultimately show "card S > degree (\<Sum>x\<in>S. smult (poly P x) (lagrange_basis S x))"
    by linarith
qed

lemma coeff_lagrange_basis_top:
  assumes fin: "finite S" and x: "x \<in> S"
  shows "poly.coeff (lagrange_basis S x) (card S - 1) =
    inverse (lagrange_denom S x)"
proof -
  have deg_prod: "degree (\<Prod>y\<in>S - {x}. [:- y, 1:] :: 'a::field poly) = card S - 1"
  proof -
    have "degree (\<Prod>y\<in>S - {x}. [:- y, 1:] :: 'a poly) = (\<Sum>y\<in>S - {x}. degree ([:- y, 1:] :: 'a poly))"
      using fin by (intro degree_prod_sum_eq) auto
    also have "\<dots> = card S - 1"
      using fin x by simp
    finally show ?thesis .
  qed
  have "poly.coeff (lagrange_basis S x) (card S - 1) =
      inverse (lagrange_denom S x) *
        poly.coeff (\<Prod>y\<in>S - {x}. [:- y, 1:] :: 'a poly) (card S - 1)"
    by (simp add: lagrange_basis_def)
  also have "\<dots> = inverse (lagrange_denom S x) *
      lead_coeff (\<Prod>y\<in>S - {x}. [:- y, 1:] :: 'a poly)"
    by (simp add: deg_prod)
  also have "\<dots> = inverse (lagrange_denom S x)"
    using fin by (simp add: lead_coeff_prod)
  finally show ?thesis .
qed

lemma lagrange_power_sum:
  fixes S :: "'a::field set"
  assumes fin: "finite S" and card: "card S = Suc d"
  assumes k: "k \<le> d"
  shows "(\<Sum>x\<in>S. x ^ k / lagrange_denom S x) = (if k = d then 1 else 0)"
proof -
  let ?X = "monom (1::'a) k"
  have interp: "?X = (\<Sum>x\<in>S. smult (poly ?X x) (lagrange_basis S x))"
    using card k by (intro lagrange_interpolation[OF fin]) (simp add: degree_monom_eq)
  have coeff_basis:
    "poly.coeff (lagrange_basis S x) d = inverse (lagrange_denom S x)" if "x \<in> S" for x
    using coeff_lagrange_basis_top[OF fin that] card by simp
  have "poly.coeff ?X d =
      poly.coeff (\<Sum>x\<in>S. smult (poly ?X x) (lagrange_basis S x)) d"
    using interp by simp
  also have "\<dots> = (\<Sum>x\<in>S. x ^ k / lagrange_denom S x)"
    using fin by (simp add: coeff_sum poly_monom coeff_basis divide_inverse)
  finally show ?thesis
    using k by simp
qed

lemma lagrange_power_sum_list:
  fixes xs :: "'a::field list"
  assumes dist: "distinct xs" and len: "length xs = Suc d" and k: "k \<le> d"
  shows "sum_list (map (\<lambda>x. x ^ k / lagrange_denom (set xs) x) xs) =  (if k = d then 1 else 0)"
proof -
  have "sum_list (map (\<lambda>x. x ^ k / lagrange_denom (set xs) x) xs) =
      (\<Sum>x\<in>set xs. x ^ k / lagrange_denom (set xs) x)"
    using dist by (rule sum_list_distinct_conv_sum_set)
  also have "\<dots> = (if k = d then 1 else 0)"
    using dist len k by (intro lagrange_power_sum) (auto simp: distinct_card)
  finally show ?thesis .
qed

subsection \<open>Sparse multivariate polynomials\<close>

text \<open>
  Monomials are indexed by exponent lists.  The value of \<open>[e\<^sub>1, \<dots>, e\<^sub>n]\<close>
  at \<open>[x\<^sub>1, \<dots>, x\<^sub>n]\<close> is \<open>x\<^sub>1 ^ e\<^sub>1 * \<dots> * x\<^sub>n ^ e\<^sub>n\<close>; mismatched
  lengths evaluate to zero.  The predicate \<open>sparse_poly\<close> records
  finite support and a fixed arity.
\<close>

fun monomial_value :: "nat list \<Rightarrow> 'a::comm_semiring_1 list \<Rightarrow> 'a" where
  "monomial_value [] [] = 1"
| "monomial_value (e # es) (x # xs) = x ^ e * monomial_value es xs"
| "monomial_value _ _ = 0"

fun grid_weight :: "'a::field list list \<Rightarrow> 'a list \<Rightarrow> 'a" where
  "grid_weight [] [] = 1"
| "grid_weight (S # Ss) (x # xs) = lagrange_denom (set S) x * grid_weight Ss xs"
| "grid_weight _ _ = 1"

definition support :: "(nat list \<Rightarrow> 'a::zero) \<Rightarrow> nat list set" where
  "support p = {m. p m \<noteq> 0}"

definition sparse_poly :: "nat \<Rightarrow> (nat list \<Rightarrow> 'a::zero) \<Rightarrow> bool" where
  "sparse_poly n p \<longleftrightarrow> finite (support p) \<and> (\<forall>m\<in>support p. length m = n)"

definition total_degree_le :: "(nat list \<Rightarrow> 'a::zero) \<Rightarrow> nat \<Rightarrow> bool" where
  "total_degree_le p d \<longleftrightarrow> (\<forall>m\<in>support p. sum_list m \<le> d)"

definition eval_sparse_poly :: "(nat list \<Rightarrow> 'a::comm_semiring_1) \<Rightarrow> 'a list \<Rightarrow> 'a" where
  "eval_sparse_poly p xs = (\<Sum>m\<in>support p. p m * monomial_value m xs)"

lemma product_lists_set_Cons:
  "set (product_lists (xs # xss)) = (\<lambda>(x, ys). x # ys) ` (set xs \<times> set (product_lists xss))"
  by auto

lemma sum_list_concat:
  "sum_list (concat xss) = sum_list (map sum_list xss)"
  by (induction xss) simp_all

lemma sum_list_map_zero:
  fixes f :: "'a \<Rightarrow> 'b::monoid_add"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> f x = 0"
  shows "sum_list (map f xs) = 0"
  using assms by (induction xs) auto

lemma sum_list_product_lists_Cons:
  "sum_list (map f (product_lists (xs # xss))) =
    sum_list (map (\<lambda>x. sum_list (map (\<lambda>ys. f (x # ys)) (product_lists xss))) xs)"
  by (simp add: sum_list_concat map_concat comp_def)

lemma grid_weight_Cons:
  "grid_weight (S # Ss) (x # xs) = lagrange_denom (set S) x * grid_weight Ss xs"
  by simp

lemma monomial_value_Cons:
  "monomial_value (e # es) (x # xs) = x ^ e * monomial_value es xs"
  by simp

definition grid_monom_sum :: "'a::field list list \<Rightarrow> nat list \<Rightarrow> 'a" where
  "grid_monom_sum Xss es =
    sum_list (map (\<lambda>xs. monomial_value es xs / grid_weight Xss xs) (product_lists Xss))"

lemma grid_monom_sum_Cons:
  assumes dist: "distinct Xs"
  shows "grid_monom_sum (Xs # Xss) (e # es) =
    sum_list (map (\<lambda>x. x ^ e / lagrange_denom (set Xs) x) Xs) *
      grid_monom_sum Xss es"
proof -
  have denom_nz: "lagrange_denom (set Xs) x \<noteq> 0" if "x \<in> set Xs" for x
    using that by (intro lagrange_denom_nonzero) auto
  have inner:
    "sum_list (map (\<lambda>xs. monomial_value (e # es) (x # xs) /
        grid_weight (Xs # Xss) (x # xs)) (product_lists Xss)) =
      (x ^ e / lagrange_denom (set Xs) x) *
        sum_list (map (\<lambda>xs. monomial_value es xs / grid_weight Xss xs)
          (product_lists Xss))"
    if "x \<in> set Xs" for x
  proof -
    have term_eq:
      "\<And>xs. monomial_value (e # es) (x # xs) / grid_weight (Xs # Xss) (x # xs) =
        (x ^ e / lagrange_denom (set Xs) x) *
          (monomial_value es xs / grid_weight Xss xs)"
      using denom_nz[OF that]
      by (simp add: divide_inverse ac_simps)
    have "sum_list (map (\<lambda>xs. monomial_value (e # es) (x # xs) /
        grid_weight (Xs # Xss) (x # xs)) (product_lists Xss)) =
      sum_list (map (\<lambda>xs. (x ^ e / lagrange_denom (set Xs) x) *
        (monomial_value es xs / grid_weight Xss xs)) (product_lists Xss))"
      by (simp add: term_eq)
    also have "\<dots> =
      (x ^ e / lagrange_denom (set Xs) x) *
        sum_list (map (\<lambda>xs. monomial_value es xs / grid_weight Xss xs) (product_lists Xss))"
      by (rule sum_list_const_mult)
    finally show ?thesis .
  qed
  have mapped:
    "map (\<lambda>x. sum_list (map (\<lambda>xs. monomial_value (e # es) (x # xs) /
        grid_weight (Xs # Xss) (x # xs)) (product_lists Xss))) Xs =
     map (\<lambda>x. (x ^ e / lagrange_denom (set Xs) x) *
        sum_list (map (\<lambda>xs. monomial_value es xs / grid_weight Xss xs)
          (product_lists Xss))) Xs"
    using inner by auto
  have "grid_monom_sum (Xs # Xss) (e # es) =
      sum_list (map (\<lambda>x. sum_list (map (\<lambda>xs. monomial_value (e # es) (x # xs) /
        grid_weight (Xs # Xss) (x # xs)) (product_lists Xss))) Xs)"
    unfolding grid_monom_sum_def by (rule sum_list_product_lists_Cons)
  also have "\<dots> =
      sum_list (map (\<lambda>x. x ^ e / lagrange_denom (set Xs) x) Xs) *
        grid_monom_sum Xss es"
    using grid_monom_sum_def[of Xss es] mapped 
          sum_list_mult_const[of _ "grid_monom_sum Xss es" Xs]
    by presburger
  finally show ?thesis .
qed

lemma grid_monom_sum_Nil [simp]:
  "grid_monom_sum [] [] = 1"
  by (simp add: grid_monom_sum_def)

lemma monomial_value_wrong_length:
  "length es \<noteq> length xs \<Longrightarrow> monomial_value es xs = 0"
proof (induction es arbitrary: xs)
  case Nil
  then show ?case
    by (cases xs) simp_all
next
  case (Cons e es xs)
  then show ?case
    by (cases xs) auto
qed

lemma grid_monom_sum_wrong_length:
  assumes "length es \<noteq> length Xss"
    shows "grid_monom_sum Xss es = 0"
proof -
  have zero: "monomial_value es xs = 0" if "xs \<in> set (product_lists Xss)" for xs
    by (metis in_set_product_lists_length assms monomial_value_wrong_length that)
  show ?thesis
    unfolding grid_monom_sum_def
    by (rule sum_list_map_zero) (metis divide_eq_0_iff zero)
qed

lemma grid_monom_sum_delta:
  fixes Xss :: "'a::field list list"
  assumes grids: "list_all2 (\<lambda>Xs d. distinct Xs \<and> length Xs = Suc d) Xss ds"
  assumes len: "length es = length ds"
  assumes deg: "sum_list es \<le> sum_list ds"
  shows "grid_monom_sum Xss es = (if es = ds then 1 else 0)"
  using grids len deg
proof (induction Xss arbitrary: ds es)
  case Nil
  then show ?case
    by (cases ds; cases es) simp_all
next
  case (Cons X Xss ds es)
  then obtain d ds' where ds: "ds = d # ds'"
    by (cases ds) auto
  then obtain e es' where es: "es = e # es'"
    using Cons.prems by (cases es) auto
  from Cons.prems ds es have X: "distinct X" "length X = Suc d"
    by auto
  from Cons.prems ds es have grids_tail:
    "list_all2 (\<lambda>Xs d. distinct Xs \<and> length Xs = Suc d) Xss ds'"
    and len_tail: "length es' = length ds'"
    and deg_all: "e + sum_list es' \<le> d + sum_list ds'"
    by auto
  show ?case
  proof (cases e d rule: linorder_cases)
    case less
    have head_delta: "sum_list (map (\<lambda>x. x ^ e / lagrange_denom (set X) x) X) =
        (if e = d then 1 else 0)"
      using X less by (intro lagrange_power_sum_list) auto
    then have head: "sum_list (map (\<lambda>x. x ^ e / lagrange_denom (set X) x) X) = 0"
      using less by simp
    show ?thesis
      using ds es less head X by (simp add: grid_monom_sum_Cons)
  next
    case equal
    have head_delta: "sum_list (map (\<lambda>x. x ^ e / lagrange_denom (set X) x) X) =
        (if e = d then 1 else 0)"
      using X equal by (intro lagrange_power_sum_list) auto
    then have head: "sum_list (map (\<lambda>x. x ^ e / lagrange_denom (set X) x) X) = 1"
      using equal by simp
    have tail_deg: "sum_list es' \<le> sum_list ds'"
      using deg_all equal by simp
    have tail: "grid_monom_sum Xss es' = (if es' = ds' then 1 else 0)"
      by (rule Cons.IH) (use grids_tail len_tail tail_deg in auto)
    show ?thesis
      using ds es equal head tail X by (simp add: grid_monom_sum_Cons)
  next
    case greater
    have tail_deg: "sum_list es' \<le> sum_list ds'"
      using deg_all greater by simp
    have tail_ne: "es' \<noteq> ds'"
    proof
      assume "es' = ds'"
      with deg_all greater show False
        by simp
    qed
    have tail: "grid_monom_sum Xss es' = 0"
      using Cons.IH[OF grids_tail len_tail tail_deg] tail_ne by auto
    show ?thesis
      using ds es greater tail X by (simp add: grid_monom_sum_Cons)
  qed
qed

text \<open>
  The next lemma is the coefficient formula specialized to the sparse
  representation: the weighted sum of all grid evaluations extracts exactly
  the coefficient of the target exponent list.
\<close>

lemma sum_list_sum:
  fixes f :: "'b \<Rightarrow> 'c \<Rightarrow> 'a::comm_monoid_add"
  assumes "finite A"
  shows "sum_list (map (\<lambda>x. \<Sum>a\<in>A. f x a) xs) =
    (\<Sum>a\<in>A. sum_list (map (\<lambda>x. f x a) xs))"
  using assms by (induction xs) (simp_all add: sum.distrib)

lemma eval_sparse_poly_grid_sum:
  fixes p :: "nat list \<Rightarrow> 'a::field"
  assumes sp: "sparse_poly (length ds) p"
  assumes grids: "list_all2 (\<lambda>Xs d. distinct Xs \<and> length Xs = Suc d) Xss ds"
  assumes deg: "total_degree_le p (sum_list ds)"
  shows "sum_list (map (\<lambda>xs. eval_sparse_poly p xs / grid_weight Xss xs) (product_lists Xss)) =
    p ds"
proof -
  have fin: "finite (support p)"
    using sp by (simp add: sparse_poly_def)
  have len_Xss: "length Xss = length ds"
    using grids by (simp add: list_all2_lengthD)
  have "sum_list (map (\<lambda>xs. eval_sparse_poly p xs / grid_weight Xss xs) (product_lists Xss)) =
      sum_list (map (\<lambda>xs. \<Sum>m\<in>support p.
        p m * (monomial_value m xs / grid_weight Xss xs)) (product_lists Xss))"
    by (simp add: eval_sparse_poly_def sum_divide_distrib sum_distrib_left mult.assoc)
  also have "\<dots> =
      (\<Sum>m\<in>support p.
        sum_list (map (\<lambda>xs. p m * (monomial_value m xs / grid_weight Xss xs))
          (product_lists Xss)))"
    using fin by (simp add: sum_list_sum)
  also have "\<dots> = (\<Sum>m\<in>support p. p m * grid_monom_sum Xss m)"
    by (intro sum.cong refl)
      (simp add: grid_monom_sum_def sum_list_const_mult divide_inverse ac_simps)
  also have "\<dots> = p ds"
  proof -
    have delta: "grid_monom_sum Xss m = (if m = ds then 1 else 0)" if "m \<in> support p" for m
    proof -
      have "length m = length ds"
        using sp that by (simp add: sparse_poly_def)
      moreover have "sum_list m \<le> sum_list ds"
        using deg that by (simp add: total_degree_le_def)
      ultimately show ?thesis
        by (rule grid_monom_sum_delta[OF grids])
    qed
    show ?thesis
    proof (cases "ds \<in> support p")
      case True
      have "(\<Sum>m\<in>support p. p m * grid_monom_sum Xss m) =
          p ds * grid_monom_sum Xss ds"
        using fin True delta by (subst sum.remove[of "support p" ds]) auto
      also have "\<dots> = p ds"
        using delta True by simp
      finally show ?thesis .
    next
      case False
      then have p0: "p ds = 0"
        by (simp add: support_def)
      have "(\<Sum>m\<in>support p. p m * grid_monom_sum Xss m) = 0"
        using fin False delta by (intro sum.neutral) auto
      with p0 show ?thesis
        by simp
    qed
  qed
  finally show ?thesis .
qed

theorem combinatorial_nullstellensatz_exact_lists:
  fixes p :: "nat list \<Rightarrow> 'a::field"
  assumes sp: "sparse_poly (length ds) p"
  assumes deg: "total_degree_le p (sum_list ds)"
  assumes coeff: "p ds \<noteq> 0"
  assumes grids: "list_all2 (\<lambda>Xs d. distinct Xs \<and> length Xs = Suc d) Xss ds"
  shows "\<exists>xs\<in>set (product_lists Xss). eval_sparse_poly p xs \<noteq> 0"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have zero: "\<And>xs. xs \<in> set (product_lists Xss) \<Longrightarrow> eval_sparse_poly p xs = 0"
    by auto
  have "sum_list (map (\<lambda>xs. eval_sparse_poly p xs / grid_weight Xss xs) (product_lists Xss)) = 0"
    by (rule sum_list_map_zero) (metis divide_eq_0_iff zero)
  moreover have "sum_list (map (\<lambda>xs. eval_sparse_poly p xs / grid_weight Xss xs) (product_lists Xss)) =
      p ds"
    by (rule eval_sparse_poly_grid_sum[OF sp grids deg])
  ultimately show False
    using coeff by simp
qed

text \<open>
  Finally, the standard ``more than \<open>d\<^sub>i\<close> points'' formulation follows by
  selecting \<open>d\<^sub>i + 1\<close> points from each side of the grid.
\<close>

definition exact_grid_sublists :: "'a list list \<Rightarrow> nat list \<Rightarrow> 'a list list" where
  "exact_grid_sublists Xss ds = map (\<lambda>(Xs, d). take (Suc d) Xs) (zip Xss ds)"

lemma exact_grid_sublists_all2:
  assumes "list_all2 (\<lambda>Xs d. distinct Xs \<and> length Xs > d) Xss ds"
  shows "list_all2 (\<lambda>Xs d. distinct Xs \<and> length Xs = Suc d)
    (exact_grid_sublists Xss ds) ds"
  using assms
proof (induction Xss arbitrary: ds)
  case Nil
  then show ?case
    by (cases ds) (simp_all add: exact_grid_sublists_def)
next
  case (Cons X Xss ds)
  then obtain d ds' where ds: "ds = d # ds'"
    by (cases ds) auto
  with Cons.prems have "distinct (take (Suc d) X)" "length (take (Suc d) X) = Suc d"
    by auto
  moreover have "list_all2 (\<lambda>Xs d. distinct Xs \<and> length Xs = Suc d)
      (exact_grid_sublists Xss ds') ds'"
    using Cons.IH Cons.prems ds by auto
  ultimately show ?case
    by (simp add: exact_grid_sublists_def ds)
qed

lemma exact_grid_sublists_subset:
  assumes "list_all2 (\<lambda>Xs d. length Xs > d) Xss ds"
  shows "set (product_lists (exact_grid_sublists Xss ds)) \<subseteq> set (product_lists Xss)"
  using assms
proof (induction Xss arbitrary: ds)
  case Nil
  then show ?case
    by (cases ds) (simp_all add: exact_grid_sublists_def)
next
  case (Cons X Xss ds)
  then obtain d ds' where ds: "ds = d # ds'"
    by (cases ds) auto
  have tail: "set (product_lists (exact_grid_sublists Xss ds')) \<subseteq> set (product_lists Xss)"
    using Cons.IH Cons.prems ds by auto
  show ?case
  proof
    fix xs
    assume "xs \<in> set (product_lists (exact_grid_sublists (X # Xss) ds))"
    then obtain x ys where xs: "xs = x # ys"
      and x: "x \<in> set (take (Suc d) X)"
      and ys: "ys \<in> set (product_lists (exact_grid_sublists Xss ds'))"
      by (auto simp: exact_grid_sublists_def ds)
    from x have "x \<in> set X"
      by (rule in_set_takeD)
    moreover from tail ys have "ys \<in> set (product_lists Xss)"
      by auto
    ultimately show "xs \<in> set (product_lists (X # Xss))"
      using xs by auto
  qed
qed

theorem combinatorial_nullstellensatz_lists:
  fixes p :: "nat list \<Rightarrow> 'a::field"
  assumes sp: "sparse_poly (length ds) p"
  assumes deg: "total_degree_le p (sum_list ds)"
  assumes coeff: "p ds \<noteq> 0"
  assumes grids: "list_all2 (\<lambda>Xs d. distinct Xs \<and> length Xs > d) Xss ds"
  shows "\<exists>xs\<in>set (product_lists Xss). eval_sparse_poly p xs \<noteq> 0"
proof -
  have exact: "list_all2 (\<lambda>Xs d. distinct Xs \<and> length Xs = Suc d)
      (exact_grid_sublists Xss ds) ds"
    by (rule exact_grid_sublists_all2[OF grids])
  obtain xs where xs: "xs \<in> set (product_lists (exact_grid_sublists Xss ds))"
    and nz: "eval_sparse_poly p xs \<noteq> 0"
    using combinatorial_nullstellensatz_exact_lists[OF sp deg coeff exact] by blast
  have lengths: "list_all2 (\<lambda>Xs d. length Xs > d) Xss ds"
    by (rule list_all2_mono[OF grids]) auto
  have "xs \<in> set (product_lists Xss)"
    using exact_grid_sublists_subset[OF lengths] xs by auto
  with nz show ?thesis
    by blast
qed

end

