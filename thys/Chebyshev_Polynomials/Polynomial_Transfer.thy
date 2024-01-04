(*
  File:     Chebyshev_Polynomials/Polynomial_Transfer.thy
  Author:   Manuel Eberl (University of Innsbruck)

  Transfer rules for polynomials
*)
section \<open>Parametricity of polynomial operations\<close>
theory Polynomial_Transfer
  imports "HOL-Computational_Algebra.Polynomial"
begin

(* TODO: Move to distribution *)

definition rel_poly :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a :: zero poly \<Rightarrow> 'b :: zero poly \<Rightarrow> bool" where
  "rel_poly R p q \<longleftrightarrow> rel_fun (=) R (coeff p) (coeff q)"

lemma left_unique_rel_poly [transfer_rule]: "left_unique R \<Longrightarrow> left_unique (rel_poly R)"
  unfolding left_unique_def rel_poly_def poly_eq_iff rel_fun_def by meson

lemma right_unique_rel_poly [transfer_rule]: "right_unique R \<Longrightarrow> right_unique (rel_poly R)"
  unfolding right_unique_def rel_poly_def poly_eq_iff rel_fun_def by meson

lemma bi_unique_rel_poly [transfer_rule]: "bi_unique R \<Longrightarrow> bi_unique (rel_poly R)"
  unfolding bi_unique_def rel_poly_def poly_eq_iff rel_fun_def by meson

lemma rel_poly_swap: "rel_poly R x y \<longleftrightarrow> rel_poly (\<lambda>y x. R x y) y x"
  by (auto simp: rel_poly_def rel_fun_def)

lemma coeff_transfer [transfer_rule]:
  "rel_fun (rel_poly R) (rel_fun (=) R) coeff coeff"
  by (auto simp: rel_fun_def rel_poly_def)

lemma map_poly_transfer:
  assumes "rel_fun R S f g" "f 0 = 0" "g 0 = 0"
  shows   "rel_fun (rel_poly R) (rel_poly S) (map_poly f) (map_poly g)"
  using assms by (auto simp: rel_fun_def rel_poly_def coeff_map_poly)

lemma map_poly_transfer':
  assumes "rel_fun R S f g" "rel_poly R p q" "f 0 = 0" "g 0 = 0"
  shows   "rel_poly S (map_poly f p) (map_poly g q)"
  using assms by (auto simp: rel_fun_def rel_poly_def coeff_map_poly)

lemma rel_poly_id: "p = q \<Longrightarrow> rel_poly (=) p q"
  by (auto simp: rel_poly_def)

lemma left_total_rel_poly [transfer_rule]:
  assumes "left_total R" "right_unique R" "R 0 0"
  shows   "left_total (rel_poly R)"
  unfolding left_total_def
proof
  fix p :: "'a poly"
  from assms have "\<forall>x. \<exists>y. R x y"
    unfolding left_total_def by blast
  then obtain f where f: "R x (f x)" for x
    by metis
  have [simp]: "f 0 = 0"
    using assms f[of 0] by (auto dest: right_uniqueD)
  have "rel_poly R (map_poly (\<lambda>x. x) p) (map_poly f p)"
    by (rule map_poly_transfer'[of "(=)"] rel_funI)+ (auto intro: rel_poly_id f)
  thus "\<exists>q. rel_poly R p q"
    by force
qed

lemma right_total_rel_poly [transfer_rule]:
  assumes "right_total R" "left_unique R" "R 0 0"
  shows   "right_total (rel_poly R)"
  using left_total_rel_poly[of "\<lambda>x y. R y x"] assms
  by (metis left_totalE left_totalI left_unique_iff rel_poly_swap right_total_def right_unique_iff)

lemma bi_total_rel_poly [transfer_rule]:
  assumes "bi_total R" "bi_unique R" "R 0 0"
  shows   "bi_total (rel_poly R)"
  using left_total_rel_poly[of R] right_total_rel_poly[of R] assms
  by (simp add: bi_total_alt_def bi_unique_alt_def)

lemma zero_poly_transfer [transfer_rule]: "R 0 0 \<Longrightarrow> rel_poly R 0 0"
  by (auto simp: rel_fun_def rel_poly_def)

lemma one_poly_transfer [transfer_rule]: "R 0 0 \<Longrightarrow> R 1 1 \<Longrightarrow> rel_poly R 1 1"
  by (auto simp: rel_fun_def rel_poly_def)

lemma pCons_transfer [transfer_rule]:
  "rel_fun R (rel_fun (rel_poly R) (rel_poly R)) pCons pCons"
  by (auto simp: rel_fun_def rel_poly_def coeff_pCons split: nat.splits)

lemma plus_poly_transfer [transfer_rule]:
  "rel_fun R (rel_fun R R) (+) (+) \<Longrightarrow> 
   rel_fun (rel_poly R) (rel_fun (rel_poly R) (rel_poly R)) (+) (+)"
  by (auto simp: rel_fun_def rel_poly_def)

lemma minus_poly_transfer [transfer_rule]:
  "rel_fun R (rel_fun R R) (-) (-) \<Longrightarrow> 
   rel_fun (rel_poly R) (rel_fun (rel_poly R) (rel_poly R)) (-) (-)"
  by (auto simp: rel_fun_def rel_poly_def)

lemma uminus_poly_transfer [transfer_rule]:
  "rel_fun R R uminus uminus \<Longrightarrow> rel_fun (rel_poly R) (rel_poly R) uminus uminus"
  by (auto simp: rel_fun_def rel_poly_def)

lemma smult_transfer [transfer_rule]:
  "rel_fun R (rel_fun R R) (*) (*) \<Longrightarrow>
   rel_fun R (rel_fun (rel_poly R) (rel_poly R)) smult smult"
  by (auto simp: rel_fun_def rel_poly_def)

lemma monom_transfer [transfer_rule]:
  "R 0 0 \<Longrightarrow> rel_fun R (rel_fun (=) (rel_poly R)) monom monom"
  by (auto simp: rel_fun_def rel_poly_def)

lemma pderiv_transfer [transfer_rule]:
  assumes "R 0 0" "rel_fun R (rel_fun R R) (+) (+)"
  shows "rel_fun (rel_poly R) (rel_poly R) pderiv pderiv"
proof (rule rel_funI, goal_cases)
  case (1 p q)
  define f :: "nat \<Rightarrow> 'a \<Rightarrow> 'a" where
    "f = (\<lambda>n p. of_nat n * p)"
  define g :: "nat \<Rightarrow> 'b \<Rightarrow> 'b" where
    "g = (\<lambda>n p. of_nat n * p)"
  have plus: "R (x + y) (x' + y')" if "R x x'" "R y y'" for x x' y y'
    using assms(2) that by (auto simp: rel_fun_def)
  have fg: "R (f m x) (g n y)" if "m = n" "R x y" for x y m n
    unfolding that(1)
    by (induction n) (auto simp: f_def g_def ring_distribs intro!: assms(1) plus that)
  have "rel_fun (=) R (\<lambda>n. f (Suc n) (coeff p (Suc n))) (\<lambda>n. g (Suc n) (coeff q (Suc n)))"
    using 1 by (intro rel_funI fg) (auto simp: rel_poly_def rel_fun_def)
  thus ?case
    by (auto simp: rel_poly_def coeff_pderiv [abs_def] f_def g_def) 
qed

lemma If_transfer':
  assumes "P = P'" "P \<Longrightarrow> R x x'" "\<not>P \<Longrightarrow> R y y'"
  shows   "R (if P then x else y) (if P' then x' else y')"
  using assms by auto

lemma nth_transfer:
  assumes "list_all2 R xs ys" "i = j" "i < length xs"
  shows   "R (xs ! i) (ys ! j)"
  using assms by (simp add: list_all2_nthD)

lemma Poly_transfer [transfer_rule]:
  assumes [transfer_rule]: "R 0 0" "bi_unique R"
  shows   "rel_fun (list_all2 R) (rel_poly R) Poly Poly"
  unfolding rel_poly_def
proof (intro rel_funI, goal_cases)
  case [transfer_rule]: (1 p q i j)
  show "R (coeff (Poly p) i) (coeff (Poly q) j)"
    unfolding coeff_Poly_eq nth_default_def
  proof (rule If_transfer')
    show "(i < length p) = (j < length q)"
      by transfer_prover
    show "R (p ! i) (q ! j)" if "i < length p"
      by (rule nth_transfer) (use 1 that in auto)
  qed (use assms in auto)
qed

lemma poly_of_list_transfer [transfer_rule]:
  assumes [transfer_rule]: "R 0 0" "bi_unique R"
  shows   "rel_fun (list_all2 R) (rel_poly R) poly_of_list poly_of_list"
  unfolding poly_of_list_def by transfer_prover

lemma degree_transfer [transfer_rule]:
  assumes [transfer_rule]: "R 0 0" "bi_unique R"
  shows   "rel_fun (rel_poly R) (=) degree degree"
proof
  fix p q
  assume *: "rel_poly R p q"
  with assms have "coeff p i = 0 \<longleftrightarrow> coeff q i = 0" for i
    unfolding rel_poly_def rel_fun_def bi_unique_def by metis
  thus "degree p = degree q"
    using antisym degree_le coeff_eq_0 by metis
qed

lemma coeffs_transfer [transfer_rule]:
  assumes [transfer_rule]: "R 0 0" "bi_unique R"
  shows "rel_fun (rel_poly R) (list_all2 R) coeffs coeffs"
proof
  fix p q
  assume [transfer_rule]: "rel_poly R p q"
  have "degree p = degree q"
    by transfer_prover
  show "list_all2 R (coeffs p) (coeffs q)"
    unfolding coeffs_def by transfer_prover
qed

lemma times_poly_transfer [transfer_rule]:
  assumes [transfer_rule]: "rel_fun R (rel_fun R R) (+) (+)"
                           "rel_fun R (rel_fun R R) (*) (*)" "R 0 0" "bi_unique R"
  shows "rel_fun (rel_poly R) (rel_fun (rel_poly R) (rel_poly R)) (*) (*)"
  unfolding times_poly_def fold_coeffs_def by transfer_prover

(* TODO: bi_total not needed; it is enough if (div) is parametric on the coefficients *)
lemma dvd_poly_transfer [transfer_rule]:
  assumes [transfer_rule]: "rel_fun R (rel_fun R R) (+) (+)"
                           "rel_fun R (rel_fun R R) (*) (*)" "R 0 0" "bi_unique R" "bi_total R"
  shows "rel_fun (rel_poly R) (rel_fun (rel_poly R) (=)) (dvd) (dvd)"
  unfolding dvd_def by transfer_prover

lemma poly_transfer [transfer_rule]:
  assumes [transfer_rule]: "rel_fun R (rel_fun R R) (+) (+)"
                           "rel_fun R (rel_fun R R) (*) (*)" "R 0 0" "bi_unique R"
  shows "rel_fun (rel_poly R) (rel_fun R R) poly poly"
  unfolding poly_def horner_sum_foldr by transfer_prover

lemma pcompose_transfer [transfer_rule]:
  assumes [transfer_rule]: "rel_fun R (rel_fun R R) (+) (+)"
                           "rel_fun R (rel_fun R R) (*) (*)" "R 0 0" "bi_unique R"
  shows "rel_fun (rel_poly R) (rel_fun (rel_poly R) (rel_poly R)) pcompose pcompose"
  unfolding pcompose_def fold_coeffs_def by transfer_prover

lemma order_0_right: "order x 0 = Least (\<lambda>_. False)"
  unfolding order_def by simp

(* TODO: bi_total not needed; it is enough if (div) is parametric on the coefficients *)
lemma order_poly_transfer [transfer_rule]:
  assumes [transfer_rule]:
    "rel_fun R (rel_fun R R) (+) (+)" "rel_fun R (rel_fun R R) (*) (*)"
    "rel_fun R R uminus uminus"
    "R 0 0" "R 1 1" "bi_unique R" "bi_total R" "R x y" "rel_poly R p q"
  shows "order x p = order y q"
  unfolding order_def by transfer_prover

end