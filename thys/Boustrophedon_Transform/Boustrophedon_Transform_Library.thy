section \<open>Preliminary material\<close>
theory Boustrophedon_Transform_Library
imports
  "HOL-Computational_Algebra.Computational_Algebra"
  "Polynomial_Interpolation.Ring_Hom_Poly"
  "HOL-Library.FuncSet"
  "HOL-Library.Groups_Big_Fun"
begin

(* TODO: Most of this should be moved to the library *)

subsection \<open>Miscellaneous\<close>

(* HOL-Library.Groups_Big_Fun *)
context comm_monoid_fun
begin           

interpretation F: comm_monoid_set f "\<^bold>1"
  ..

lemma expand_superset_cong:
  assumes "finite A" and "\<And>a. a \<notin> A \<Longrightarrow> g a = \<^bold>1" and "\<And>a. a \<in> A \<Longrightarrow> g a = h a"
  shows "G g = F.F h A"
proof -
  have "G g = F.F g A"
    by (rule expand_superset) (use assms(1,2) in auto)
  also have "\<dots> = F.F h A"
    by (rule F.cong) (use assms(3) in auto)
  finally show ?thesis .
qed

lemma reindex_bij_witness:
  assumes "\<And>x. h1 (h2 x) = x" "\<And>x. h2 (h1 x) = x"
  assumes "\<And>x. g1 (h1 x) = g2 x"
  shows   "G g1 = G g2"
proof -
  have "bij h1"
    using assms(1,2) by (metis bij_betw_def inj_def surj_def)
  have "G g1 = G (g1 \<circ> h1)"
    by (rule reindex_cong[of h1]) (use \<open>bij h1\<close> in auto)
  also have "g1 \<circ> h1 = g2"
    using assms(3) by auto
  finally show ?thesis .
qed

lemma distrib':
  assumes "\<And>x. x \<notin> A \<Longrightarrow> g1 x = \<^bold>1"
  assumes "\<And>x. x \<notin> A \<Longrightarrow> g2 x = \<^bold>1"
  assumes "finite A"
  shows "G (\<lambda>x. f (g1 x) (g2 x)) = f (G g1) (G g2)"
proof (rule distrib)
  show "finite {x. g1 x \<noteq> \<^bold>1}"
    by (rule finite_subset[OF _ assms(3)]) (use assms(1) in auto)
  show "finite {x. g2 x \<noteq> \<^bold>1}"
    by (rule finite_subset[OF _ assms(3)]) (use assms(2) in auto)
qed

end

lemma of_rat_fact [simp]: "of_rat (fact n) = fact n"
  by (induction n) (auto simp: of_rat_mult of_rat_add)

lemma Pow_conv_subsets_of_size:
  assumes "finite A"
  shows   "Pow A = (\<Union>k\<le>card A. {X. X \<subseteq> A \<and> card X = k})"
  using assms by (auto intro: card_mono)


subsection \<open>Linear orders\<close>

(* HOL.Order_Relation *)

lemma (in linorder) linorder_linear_order [intro]: "linear_order {(x,y). x \<le> y}"
  unfolding linear_order_on_def partial_order_on_def preorder_on_def antisym_def 
            trans_def refl_on_def total_on_def by auto

lemma (in linorder) less_strict_linear_order_on [intro]: "strict_linear_order_on A {(x,y). x < y}"
  unfolding strict_linear_order_on_def trans_def irrefl_def total_on_def by auto

lemma (in linorder) greater_strict_linear_order_on [intro]: "strict_linear_order_on A {(x,y). x > y}"
  unfolding strict_linear_order_on_def trans_def irrefl_def total_on_def by auto

lemma strict_linear_order_on_asym_on:
  assumes "strict_linear_order_on A R"
  shows   "asym_on A R"
  using assms unfolding strict_linear_order_on_def
  by (meson asym_on_iff_irrefl_on_if_trans_on asym_on_subset top_greatest)

lemma strict_linear_order_on_antisym_on:
  assumes "strict_linear_order_on A R"
  shows   "antisym_on A R"
  using assms unfolding strict_linear_order_on_def
  by (meson antisym_on_def irreflD transD)

lemma monotone_on_imp_inj_on:
  assumes "monotone_on A R R' f" "strict_linear_order_on A {(x,y). R x y}"
           "strict_linear_order_on (f ` A) {(x,y). R' x y}"
  shows   "inj_on f A"
proof
  fix x y assume xy: "x \<in> A" "y \<in> A" "f x = f y"
  show "x = y"
  proof (rule ccontr)
    assume "x \<noteq> y"
    hence "R x y \<or> R y x"
      using assms(2) xy unfolding strict_linear_order_on_def total_on_def by auto
    hence "R' (f x) (f y) \<or> R' (f y) (f x)"
      using assms(1) xy(1,2) by (auto simp: monotone_on_def)
    thus False
      using xy(3) assms(3) unfolding strict_linear_order_on_def irrefl_def
      by auto
  qed
qed  

lemma monotone_on_inv_into:
  assumes "monotone_on A R R' f" "strict_linear_order_on A {(x,y). R x y}"
          "strict_linear_order_on (f ` A) {(x,y). R' x y}"
  shows   "monotone_on (f ` A) R' R (inv_into A f)"
  unfolding monotone_on_def
proof safe
  fix x y assume xy: "x \<in> A" "y \<in> A" "R' (f x) (f y)"
  have "inj_on f A"
    using assms(1,2,3) by (rule monotone_on_imp_inj_on)
  have "f x \<noteq> f y"
    using xy assms(3) by (auto simp: strict_linear_order_on_def irrefl_def)
  have "\<not>R y x"
  proof
    assume "R y x"
    hence "R' (f y) (f x)"
      using assms(1) xy by (auto simp: monotone_on_def)
    thus False
      using xy strict_linear_order_on_antisym_on[OF assms(3)] \<open>f x \<noteq> f y\<close>
      by (auto simp: antisym_on_def)
  qed
  hence "R x y"
    using assms(2) xy \<open>f x \<noteq> f y\<close> by (auto simp: strict_linear_order_on_def total_on_def)
  thus "R (inv_into A f (f x)) (inv_into A f (f y))"
    by (subst (1 2) inv_into_f_f) (use xy \<open>inj_on f A\<close> in auto)
qed

lemma sorted_wrt_imp_distinct:
  assumes "sorted_wrt R xs" "\<And>x. x \<in> set xs \<Longrightarrow> \<not>R x x"
  shows   "distinct xs"
  using assms by (induction R xs rule: sorted_wrt.induct) auto

lemma strict_linear_order_on_finite_has_least:
  assumes "strict_linear_order_on A R" "finite A" "A \<noteq> {}"
  shows   "\<exists>x\<in>A. \<forall>y\<in>A-{x}. (x,y) \<in> R"
  using assms(2,1,3)
proof (induction A rule: finite_psubset_induct)
  case (psubset A)
  from \<open>A \<noteq> {}\<close> obtain x where x: "x \<in> A"
    by blast
  show ?case
  proof (cases "A - {x} = {}")
    case True
    thus ?thesis
      by (intro bexI[of _ x]) (use x in auto)
  next
    case False
    have trans: "(x,z) \<in> R" if "(x,y) \<in> R" "(y,z) \<in> R" for x y z
      using psubset.prems that unfolding strict_linear_order_on_def trans_def by blast
    have *: "strict_linear_order_on (A - {x}) R"
      using psubset.prems(1) by (auto simp: strict_linear_order_on_def total_on_def)
    have "\<exists>z\<in>A-{x}. \<forall>y\<in>A-{x}-{z}. (z,y) \<in> R"
      by (rule psubset.IH) (use x False * in auto)
    then obtain z where z: "z \<in> A - {x}" "\<And>y. y \<in> A - {x, z} \<Longrightarrow> (z,y) \<in> R"
      by blast
    have "(x, z) \<in> R \<or> (z, x) \<in> R"
      using psubset.prems x z unfolding strict_linear_order_on_def total_on_def
      by auto
    thus ?thesis
    proof
      assume "(x, z) \<in> R"
      thus ?thesis
        using x z by (auto intro!: bexI[of _ x] intro: trans)
    next
      assume "(z, x) \<in> R"
      thus ?thesis
        using x z by (auto intro!: bexI[of _ z] intro: trans)
    qed
  qed
qed

lemma strict_linear_orderE_sorted_list:
  assumes "strict_linear_order_on A R" "finite A"
  obtains xs where "sorted_wrt (\<lambda>x y. (x,y) \<in> R) xs" "set xs = A" "distinct xs"
proof -
  have "\<exists>xs. sorted_wrt (\<lambda>x y. (x,y) \<in> R) xs \<and> set xs = A"
    using assms(2,1)
  proof (induction A rule: finite_psubset_induct)
    case (psubset A)
    show ?case
    proof (cases "A = {}")
      case False
      then obtain x where x: "x \<in> A" "\<And>y. y \<in> A - {x} \<Longrightarrow> (x,y) \<in> R"
        using strict_linear_order_on_finite_has_least[OF psubset.prems psubset.hyps(1)] by blast
      have *: "strict_linear_order_on (A - {x}) R"
        using psubset.prems by (auto simp: strict_linear_order_on_def total_on_def)
      have "\<exists>xs. sorted_wrt (\<lambda>x y. (x,y) \<in> R) xs \<and> set xs = A - {x}"
        by (rule psubset.IH) (use x * in auto)
      then obtain xs where xs: "sorted_wrt (\<lambda>x y. (x,y) \<in> R) xs" "set xs = A - {x}"
        by blast
      have "sorted_wrt (\<lambda>x y. (x,y) \<in> R) (x # xs)" "set (x # xs) = A"
        using x xs by auto
      thus ?thesis
        by blast
    qed auto
  qed
  then obtain xs where xs: "sorted_wrt (\<lambda>x y. (x,y) \<in> R) xs" "set xs = A"
    by blast
  from xs(1) have "distinct xs"
    by (rule sorted_wrt_imp_distinct) (use assms in \<open>auto simp: strict_linear_order_on_def irrefl_def\<close>)
  with xs show ?thesis
    using that by blast
qed

lemma sorted_wrt_strict_linear_order_unique:
  assumes R: "strict_linear_order_on A R"
  assumes "sorted_wrt (\<lambda>x y. (x,y) \<in> R) xs" "sorted_wrt (\<lambda>x y. (x,y) \<in> R) ys"
  assumes "set xs \<subseteq> A" "set xs = set ys"
  shows   "xs = ys"
  using assms(2-)
proof (induction xs arbitrary: ys)
  case (Cons x xs ys')
  from Cons.prems obtain y ys where [simp]: "ys' = y # ys"
    by (cases ys') auto
  have "set ys' \<subseteq> A"
    unfolding \<open>set (x#xs) = set ys'\<close>[symmetric] by fact
  have [simp]: "(z, z) \<notin> R" for z
    using R by (auto simp: strict_linear_order_on_def irrefl_def)
  have "distinct (x # xs)"
    by (rule sorted_wrt_imp_distinct[OF \<open>sorted_wrt _ (x#xs)\<close>]) auto
  hence "x \<notin> set xs"
    by auto
  have "distinct ys'"
    by (rule sorted_wrt_imp_distinct[OF \<open>sorted_wrt _ ys'\<close>]) auto
  hence "y \<notin> set ys"
    by auto

  have *: "(x,y) \<in> R \<or> x = y \<or> (y,x) \<in> R"
    using R Cons.prems unfolding total_on_def by auto
  have "x = y"
    by (rule ccontr)
       (use Cons.prems strict_linear_order_on_asym_on[OF R] * 
            \<open>set ys' \<subseteq> A\<close> \<open>x \<notin> set xs\<close> \<open>y \<notin> set ys\<close>
        in \<open>auto simp: insert_eq_iff asym_on_def\<close>)
  moreover have "xs = ys"
    by (rule Cons.IH)
       (use Cons.prems \<open>x = y\<close> \<open>x \<notin> set xs\<close> \<open>y \<notin> set ys\<close> in \<open>simp_all add: insert_eq_iff\<close>)
  ultimately show ?case
    by simp
qed auto

definition sorted_list_of_set_wrt :: "('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> 'a list" where
  "sorted_list_of_set_wrt R A =
     (THE xs. sorted_wrt (\<lambda>x y. (x,y) \<in> R) xs \<and> distinct xs \<and> set xs = A)"

lemma sorted_list_of_set_wrt:
  assumes "strict_linear_order_on A R" "finite A"
  shows   "sorted_wrt (\<lambda>x y. (x,y) \<in> R) (sorted_list_of_set_wrt R A)"
          "distinct (sorted_list_of_set_wrt R A)"
          "set (sorted_list_of_set_wrt R A) = A"
proof -
  define P where "P = (\<lambda>xs. sorted_wrt (\<lambda>x y. (x,y) \<in> R) xs \<and> distinct xs \<and> set xs = A)"
  have "\<exists>xs. P xs"
    using strict_linear_orderE_sorted_list[OF assms] unfolding P_def by blast
  moreover have "xs = ys" if "P xs" "P ys" for xs ys
    using sorted_wrt_strict_linear_order_unique[OF assms(1)] that
    unfolding P_def by blast
  ultimately have *: "\<exists>!xs. P xs"
    by blast
  show "sorted_wrt (\<lambda>x y. (x,y) \<in> R) (sorted_list_of_set_wrt R A)"
       "distinct (sorted_list_of_set_wrt R A)"
       "set (sorted_list_of_set_wrt R A) = A"
    using theI'[OF *] unfolding P_def sorted_list_of_set_wrt_def by blast+
qed

lemma sorted_list_of_set_wrt_eqI:
  assumes "strict_linear_order_on A R" "sorted_wrt (\<lambda>x y. (x,y) \<in> R) xs" "set xs = A"
  shows   "sorted_list_of_set_wrt R A = xs"
proof (rule sym, rule sorted_wrt_strict_linear_order_unique[OF assms(1,2)])
  have *: "finite A"
    unfolding assms(3) [symmetric] by simp
  show "sorted_wrt (\<lambda>x y. (x, y) \<in> R) (sorted_list_of_set_wrt R A)"
       "set xs = set (sorted_list_of_set_wrt R A)"
    using assms(3) sorted_list_of_set_wrt[OF assms(1) *] by simp_all
qed (use assms in auto)
  
lemma strict_linear_orderE_bij_betw:
  assumes "strict_linear_order_on A R" "finite A"
  obtains f where
    "bij_betw f {0..<card A} A" "monotone_on {0..<card A} (<) (\<lambda>x y. (x,y) \<in> R) f"
proof -
  obtain xs where xs: "sorted_wrt (\<lambda>x y. (x,y) \<in> R) xs" "set xs = A" "distinct xs"
    using strict_linear_orderE_sorted_list[OF assms] by blast
  have length_xs: "length xs = card A"
    using distinct_card[of xs] xs by simp
  define f where "f = (\<lambda>i. xs ! i)"

  have "A = set xs"
    using xs by simp
  also have "\<dots> = {f i |i. i < card A}"
    by (simp add: set_conv_nth length_xs f_def)
  also have "\<dots> = f ` {0..<card A}"
    by auto
  finally have range: "f ` {0..<card A} = A"
    by blast

  show ?thesis
  proof (rule that[of f])
    show "monotone_on {0..<card A} (<) (\<lambda>x y. (x, y) \<in> R) f"
      using xs length_xs by (auto simp: monotone_on_def f_def sorted_wrt_iff_nth_less)
    hence "inj_on f {0..<card A}"
      by (rule monotone_on_imp_inj_on) (use assms range in auto)
    with range show "bij_betw f {0..<card A} A"
      by (simp add: bij_betw_def)
  qed
qed

lemma strict_linear_orderE_bij_betw':
  assumes "strict_linear_order_on A R" "finite A"
  obtains f where "bij_betw f {1..card A} A" "monotone_on {1..card A} (<) (\<lambda>x y. (x,y) \<in> R) f"
proof -
  obtain f where f: "bij_betw f {0..<card A} A" "monotone_on {0..<card A} (<) (\<lambda>x y. (x,y) \<in> R) f"
    using strict_linear_orderE_bij_betw[OF assms] .
  have *: "bij_betw (\<lambda>n. n - 1) {1..card A} {0..<card A}"
    by (rule bij_betwI[of _ _ _ "\<lambda>n. n + 1"]) auto
  have "bij_betw (f \<circ> (\<lambda>n. n - 1)) {1..card A} A"
    by (rule bij_betw_trans[OF * f(1)])
  moreover have "monotone_on {1..card A} (<) (\<lambda>x y. (x, y) \<in> R) (f \<circ> (\<lambda>n. n - 1))"
    using f(2) by (rule monotone_on_o) (auto simp: strict_mono_on_def)
  ultimately show ?thesis
    using that by blast
qed

lemma monotone_on_strict_linear_orderD:
  assumes "monotone_on A R R' f"
  assumes "strict_linear_order_on A {(x,y). R x y}" "strict_linear_order_on (f ` A) {(x,y). R' x y}"
  assumes "x \<in> A" "y \<in> A"
  shows   "R' (f x) (f y) \<longleftrightarrow> R x y"
proof
  assume "R x y"
  thus "R' (f x) (f y)"
    using assms by (auto simp: monotone_on_def)
next
  assume *: "R' (f x) (f y)"
  have "\<not>R y x"
  proof
    assume "R y x"
    hence "R' (f y) (f x)"
      using assms by (auto simp: monotone_on_def)
    with * show False
      using assms strict_linear_order_on_asym_on[OF assms(3)]
      by (auto simp: asym_on_def)
  qed
  moreover have "x \<noteq> y"
    using assms * by (auto simp: strict_linear_order_on_def irrefl_def)
  ultimately show "R x y"
    using assms by (auto simp: strict_linear_order_on_def total_on_def)
qed


subsection \<open>Polynomials, formal power series and Laurent series\<close>

(* HOL-Computational_Algebra.Polynomial *)

lemma lead_coeff_pderiv: "lead_coeff (pderiv p) = of_nat (degree p) * lead_coeff p"
  for p :: "'a::{comm_semiring_1,semiring_no_zero_divisors,semiring_char_0} poly"
proof (cases "pderiv p = 0")
  case False
  hence "degree p > 0"
    by (simp add: pderiv_eq_0_iff)
  thus ?thesis
    by (subst coeff_pderiv) (auto simp: degree_pderiv)
next
  case True
  thus ?thesis
    by (simp add: pderiv_eq_0_iff)
qed

lemma of_nat_poly_pderiv:
  "map_poly (of_nat :: nat \<Rightarrow> 'a :: {semidom, semiring_char_0}) (pderiv p) =
     pderiv (map_poly of_nat p)"
proof (induct p rule: pderiv.induct)
  case (1 a p)
  interpret of_nat_poly_hom: map_poly_comm_semiring_hom of_nat
    by standard auto
  show ?case using 1 unfolding pderiv.simps
    by (cases "p = 0") (auto simp: hom_distribs pderiv_pCons)
qed



(* HOL-Computational_Algebra.Formal_Power_Series *)

lemma fps_mult_left_numeral_nth [simp]:
  "((numeral c :: 'a ::{comm_monoid_add, semiring_1} fps) * f) $ n = numeral c * f $ n"
  by (simp add: numeral_fps_const)

lemma fps_mult_right_numeral_nth [simp]:
  "(f * (numeral c :: 'a ::{comm_monoid_add, semiring_1} fps)) $ n = f $ n * numeral c"
  by (simp add: numeral_fps_const)

lemma fps_shift_Suc_times_fps_X [simp]:
  fixes f :: "'a::{comm_monoid_add,mult_zero,monoid_mult} fps"
  shows "fps_shift (Suc n) (f * fps_X) = fps_shift n f"
  by (intro fps_ext) (simp add: nth_less_subdegree_zero)

lemma fps_shift_Suc_times_fps_X' [simp]:
  fixes f :: "'a::{comm_monoid_add,mult_zero,monoid_mult} fps"
  shows "fps_shift (Suc n) (fps_X * f) = fps_shift n f"
  by (intro fps_ext) (simp add: nth_less_subdegree_zero)

lemma fps_nth_inverse:
  fixes f :: "'a :: division_ring fps"
  assumes "fps_nth f 0 \<noteq> 0" "n > 0"
  shows   "fps_nth (inverse f) n = -(\<Sum>i=0..<n. inverse f $ i * f $ (n - i)) / f $ 0"
proof -
  have "inverse f * f = 1"
    using assms by (simp add: inverse_mult_eq_1)
  also have "fps_nth \<dots> n = 0"
    using \<open>n > 0\<close> by simp
  also have "fps_nth (inverse f * f) n = (\<Sum>i=0..n. inverse f $ i * f $ (n - i))"
    by (simp add: fps_mult_nth)
  also have "{0..n} = insert n {0..<n}"
    by auto
  also have "(\<Sum>i\<in>\<dots>. inverse f $ i * f $ (n - i)) = 
             inverse f $ n * f $ 0 + (\<Sum>i=0..<n. inverse f $ i * f $ (n - i))"
    by (subst sum.insert) auto
  finally show "inverse f $ n = -(\<Sum>i=0..<n. inverse f $ i * f $ (n - i)) / f $ 0"
    using assms by (simp add: field_simps add_eq_0_iff)
qed

lemma fps_compose_of_poly:
  fixes p :: "'a :: idom poly"
  assumes [simp]: "fps_nth f 0 = 0"
  shows "fps_compose (fps_of_poly p) f = poly (map_poly fps_const p) f"
  by (induction p)
     (simp_all add: fps_of_poly_pCons fps_compose_mult_distrib fps_compose_add_distrib
                    algebra_simps)

lemma fps_nth_compose_linear:
  fixes f :: "'a :: comm_ring_1 fps"
  shows "fps_nth (fps_compose f (fps_const c * fps_X)) n = c ^ n * fps_nth f n"
  by (subst fps_compose_linear) auto

lemma fps_nth_compose_uminus:
  fixes f :: "'a :: comm_ring_1 fps"
  shows "fps_nth (fps_compose f (-fps_X)) n = (-1) ^ n * fps_nth f n"
  using fps_nth_compose_linear[of f "-1" n] by (simp flip: fps_const_neg)

lemma fps_shift_compose_linear:
  fixes f :: "'a :: comm_ring_1 fps"
  shows "fps_shift n (fps_compose f (fps_const c * fps_X)) = fps_const (c ^ n) * fps_compose (fps_shift n f) (fps_const c * fps_X)"
  by (auto simp: fps_eq_iff fps_nth_compose_linear power_add)

lemma fps_compose_shift_linear:
  fixes f :: "'a :: field fps"
  assumes "c \<noteq> 0"
  shows "fps_compose (fps_shift n f) (fps_const c * fps_X) =
           fps_const (1 / c ^ n) * fps_shift n (fps_compose f (fps_const c * fps_X))"
  using assms by (auto simp: fps_eq_iff fps_nth_compose_linear power_add)



(* HOL-Computational_Algebra.Formal_Laurent_Series *)

lemma fls_compose_fps_sum [simp]: 
  assumes [simp]: "H \<noteq> 0" "fps_nth H 0 = 0"
  shows   "fls_compose_fps (\<Sum>x\<in>A. F x) H = (\<Sum>x\<in>A. fls_compose_fps (F x) H)"
  by (induction A rule: infinite_finite_induct) (auto simp: fls_compose_fps_add)

lemma divide_fps_eqI:
  assumes "F * G = (H :: 'a :: field fps)" "H \<noteq> 0 \<or> G \<noteq> 0 \<or> F = 0"
  shows   "H / G = F"
proof (cases "G = 0")
  case True
  with assms show ?thesis
    by auto
next
  case False
  have "(F * G) / G = F"
    by (rule fps_divide_times_eq) (use False in auto)
  thus ?thesis
    using assms by simp
qed
                    
lemma fps_to_fls_sum [simp]: "fps_to_fls (\<Sum>x\<in>A. f x) = (\<Sum>x\<in>A. fps_to_fls (f x))"
  by (induction A rule: infinite_finite_induct) auto

lemma fps_to_fls_sum_list [simp]: "fps_to_fls (sum_list fs) = (\<Sum>f\<leftarrow>fs. fps_to_fls f)"
  by (induction fs) auto

lemma fps_to_fls_sum_mset [simp]: "fps_to_fls (sum_mset F) = (\<Sum>f\<in>#F. fps_to_fls f)"
  by (induction F) auto

lemma fps_to_fls_prod [simp]: "fps_to_fls (\<Prod>x\<in>A. f x) = (\<Prod>x\<in>A. fps_to_fls (f x))"
  by (induction A rule: infinite_finite_induct) (auto simp: fls_times_fps_to_fls)

lemma fps_to_fls_prod_list [simp]: "fps_to_fls (prod_list fs) = (\<Prod>f\<leftarrow>fs. fps_to_fls f)"
  by (induction fs) (auto simp: fls_times_fps_to_fls)

lemma fps_to_fls_prod_mset [simp]: "fps_to_fls (prod_mset F) = (\<Prod>f\<in>#F. fps_to_fls f)"
  by (induction F) (auto simp: fls_times_fps_to_fls)




subsection \<open>Power series of trigonometric functions\<close>

(* HOL-Computational_Algebra.Formal_Power_Series *)

definition fps_sec :: "'a :: field_char_0 \<Rightarrow> 'a fps" 
  where "fps_sec c = inverse (fps_cos c)"

lemma fps_sec_deriv: "fps_deriv (fps_sec c) = fps_const c * fps_sec c * fps_tan c"
  by (simp add: fps_sec_def fps_tan_def fps_inverse_deriv fps_cos_deriv fps_divide_unit
                power2_eq_square flip: fps_const_neg)

lemma fps_sec_nth_0 [simp]: "fps_nth (fps_sec c) 0 = 1"
  by (simp add: fps_sec_def)

lemma fps_sec_square_conv_fps_tan_square:
  "fps_sec c ^ 2 = (1 + fps_tan c ^ 2 :: 'a :: field_char_0 fps)"
proof -
  have "fps_nth (fps_cos c) 0 \<noteq> fps_nth 0 0"
    by auto
  hence [simp]: "fps_cos c \<noteq> 0"
    by metis
  have "fps_to_fls (1 + fps_tan c ^ 2) =
          fps_to_fls 1 + fps_to_fls (fps_sin c) ^ 2 / fps_to_fls (fps_cos c) ^ 2"
    by (simp add: fps_tan_def field_simps fps_to_fls_power flip: fls_divide_fps_to_fls)
  also have "\<dots> = (fps_to_fls (fps_cos c ^ 2 + fps_sin c ^ 2)) / fps_to_fls (fps_cos c) ^ 2"
    by (simp add: field_simps fps_to_fls_power)
  also have "fps_cos c ^ 2 + fps_sin c ^ 2 = 1"
    by (rule fps_sin_cos_sum_of_squares)
  also have "fps_to_fls 1 / fps_to_fls (fps_cos c) ^ 2 = fps_to_fls (fps_sec c ^ 2)"
    by (simp add: fps_sec_def fps_to_fls_power field_simps flip: fls_inverse_fps_to_fls)
  finally show ?thesis
    by (simp only: fps_to_fls_eq_iff)
qed


definition fps_cosh :: "'a :: field_char_0 \<Rightarrow> 'a fps"
  where "fps_cosh c = fps_const (1/2) * (fps_exp c + fps_exp (-c))"

lemma fps_nth_cosh_0 [simp]: "fps_nth (fps_cosh c) 0 = 1"
  by (simp_all add: fps_cosh_def)

lemma fps_cos_conv_cosh: "fps_cos c = fps_cosh (\<i> * c)"
  by (simp add: fps_cosh_def fps_cos_fps_exp_ii)

lemma fps_cosh_conv_cos: "fps_cosh c = fps_cos (\<i> * c)"
  by (simp add: fps_cosh_def fps_cos_fps_exp_ii)

lemma fps_cosh_compose_linear [simp]: 
  "fps_cosh (d::'a::field_char_0) oo (fps_const c * fps_X) = fps_cosh (c * d)"
  by (simp add: fps_cosh_def fps_compose_add_distrib fps_compose_mult_distrib)
  
lemma fps_fps_cosh_compose_minus [simp]: 
  "fps_compose (fps_cosh c) (-fps_X) = fps_cosh (-c :: 'a :: field_char_0)"
  by (simp add: fps_cosh_def fps_compose_add_distrib fps_compose_mult_distrib)

lemma fps_nth_cosh: "fps_nth (fps_cosh c) n = (if even n then c ^ n / fact n else 0)"
proof -
  have "fps_nth (fps_cosh c) n = (c ^ n + (-c) ^ n) / (2 * fact n)"
    by (simp add: fps_cosh_def fps_exp_def fps_mult_left_const_nth add_divide_distrib mult_ac)
  also have "c ^ n + (-c) ^ n = (if even n then 2 * c ^ n else 0)"
    by (auto simp: uminus_power_if)
  also have "\<dots> / (2 * fact n) = (if even n then c ^ n / fact n else 0)"
    by auto
  finally show ?thesis .
qed


definition fps_sech :: "'a :: field_char_0 \<Rightarrow> 'a fps"
  where "fps_sech c = inverse (fps_cosh c)"

lemma fps_nth_sech_0 [simp]: "fps_nth (fps_sech c) 0 = 1"
  by (simp_all add: fps_sech_def)

lemma fps_sec_conv_sech: "fps_sec c = fps_sech (\<i> * c)"
  by (simp add: fps_sech_def fps_sec_def fps_cos_conv_cosh)

lemma fps_sech_conv_sec: "fps_sech c = fps_sec (\<i> * c)"
  by (simp add: fps_sech_def fps_sec_def fps_cosh_conv_cos)

lemma fps_sech_compose_linear [simp]: 
  "fps_sech (d::'a::field_char_0) oo (fps_const c * fps_X) = fps_sech (c * d)"
  by (simp add: fps_sech_def fps_inverse_compose)
  
lemma fps_fps_sech_compose_minus [simp]: 
  "fps_compose (fps_sech c) (-fps_X) = fps_sech (-c :: 'a :: field_char_0)"
  by (simp add: fps_sech_def fps_inverse_compose)


lemma fps_tan_deriv': "fps_deriv (fps_tan 1 :: 'a :: field_char_0 fps) = 1 + fps_tan 1 ^ 2"
proof -
  have "fps_nth (fps_cos (1::'a)) 0 \<noteq> fps_nth 0 0"
    by auto
  hence [simp]: "fps_cos (1::'a) \<noteq> 0"
    by metis
  have "fps_to_fls (fps_deriv (fps_tan (1 :: 'a :: field_char_0))) = 
          fps_to_fls 1 / fps_to_fls (fps_cos 1 ^ 2)"
    by (simp add: fls_deriv_fps_to_fls fps_tan_deriv flip: fls_divide_fps_to_fls)
  also have "1 = fps_cos 1 ^ 2 + fps_sin (1::'a) ^ 2"
    using fps_sin_cos_sum_of_squares[of "1::'a"] by simp
  also have "fps_to_fls \<dots> / fps_to_fls (fps_cos 1 ^ 2) = fps_to_fls (1 + fps_tan 1 ^ 2)"
    by (simp add: field_simps fps_tan_def power2_eq_square fls_times_fps_to_fls
             flip: fls_divide_fps_to_fls)
  finally show ?thesis
    by (simp only: fps_to_fls_eq_iff)
qed

lemma fps_tan_nth_0 [simp]: "fps_nth (fps_tan c) 0 = 0"
  by (simp add: fps_tan_def)


lemma fps_nth_sin_even:
  assumes "even n"
  shows   "fps_nth (fps_sin c) n = 0"
  using assms by (auto simp: fps_sin_def)

lemma fps_nth_cos_odd:
  assumes "odd n"
  shows   "fps_nth (fps_cos c) n = 0"
  using assms by (auto simp: fps_cos_def)

lemma fps_tan_odd: "fps_tan (-c) = -fps_tan c"
  by (simp add: fps_tan_def fps_sin_even fps_cos_odd fps_divide_uminus)

lemma fps_sec_even: "fps_sec (-c) = fps_sec c"
  by (simp add: fps_sec_def fps_cos_odd fps_divide_uminus)

lemma fps_sin_compose_linear [simp]: "fps_sin c oo (fps_const c' * fps_X) = fps_sin (c * c')"
  by (rule fps_ext) (simp_all add: fps_sin_def fps_compose_linear power_mult_distrib)

lemma fps_sin_compose_uminus [simp]: "fps_sin c oo (-fps_X) = fps_sin (-c)"
  using fps_sin_compose_linear[of c "-1"] by (simp flip: fps_const_neg del: fps_sin_compose_linear)

lemma fps_cos_compose_linear [simp]: "fps_cos c oo (fps_const c' * fps_X) = fps_cos (c * c')"
  by (rule fps_ext) (simp_all add: fps_cos_def fps_compose_linear power_mult_distrib)

lemma fps_cos_compose_uminus [simp]: "fps_cos c oo (-fps_X) = fps_cos (-c)"
  using fps_cos_compose_linear[of c "-1"] by (simp flip: fps_const_neg del: fps_cos_compose_linear)

lemma fps_tan_compose_linear [simp]: "fps_tan c oo (fps_const c' * fps_X) = fps_tan (c * c')"
  by (simp add: fps_tan_def fps_divide_compose)

lemma fps_tan_compose_uminus [simp]: "fps_tan c oo (-fps_X) = fps_tan (-c)"
  by (simp add: fps_tan_def fps_divide_compose)

lemma fps_sec_compose_linear [simp]: "fps_sec c oo (fps_const c' * fps_X) = fps_sec (c * c')"
  by (simp add: fps_sec_def fps_inverse_compose)

lemma fps_sec_compose_uminus [simp]: "fps_sec c oo (-fps_X) = fps_sec (-c)"
  by (simp add: fps_sec_def fps_inverse_compose)

lemma fps_nth_tan_even:
  assumes "even n"
  shows   "fps_nth (fps_tan c) n = 0"
proof -
  have "fps_tan c oo -fps_X = -fps_tan c"
    by (simp add: fps_tan_odd)
  hence "(fps_tan c oo -fps_X) $ n = (-fps_tan c) $ n"
    by (rule arg_cong)
  thus ?thesis using assms
    unfolding fps_eq_iff fps_nth_compose_uminus
    by (auto simp: minus_one_power_iff)
qed

lemma fps_nth_sec_odd:
  assumes "odd n"
  shows   "fps_nth (fps_sec c) n = 0"
proof -
  have "fps_sec c oo -fps_X = fps_sec c"
    by (simp add: fps_sec_even)
  hence "(fps_sec c oo -fps_X) $ n = (fps_sec c) $ n"
    by (rule arg_cong)
  thus ?thesis using assms
    unfolding fps_eq_iff fps_nth_compose_uminus
    by (auto simp: minus_one_power_iff)
qed

end