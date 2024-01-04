(*
  File:     Chebyshev_Polynomials/Chebyshev_Polynomials_Library.thy
  Author:   Manuel Eberl (University of Innsbruck)

  Various library to be moved to the distribution
*)
section \<open>Missing Library Material\<close>
theory Chebyshev_Polynomials_Library
  imports "HOL-Computational_Algebra.Polynomial" "HOL-Library.FuncSet"
begin

subsection \<open>Miscellaneous\<close>

(* TODO: Move to \<^theory>\<open>HOL.Fun\<close> *)
lemma bij_betw_Collect:
  assumes "bij_betw f A B" "\<And>x. x \<in> A \<Longrightarrow> Q (f x) \<longleftrightarrow> P x"
  shows   "bij_betw f {x\<in>A. P x} {y\<in>B. Q y}"
  using assms by (auto simp add: bij_betw_def inj_on_def)

(* TODO: Move somewhere, perhaps? Maybe \<^theory>\<open>HOL.Nat\<close>?*)
lemma induct_nat_012[case_names 0 1 ge2]:
  "P 0 \<Longrightarrow> P (Suc 0) \<Longrightarrow> (\<And>n. P n \<Longrightarrow> P (Suc n) \<Longrightarrow> P (Suc (Suc n))) \<Longrightarrow> P n"
proof (induction_schema, pat_completeness)
  show "wf (Wellfounded.measure id)"
    by simp
qed auto


subsection \<open>Lists\<close>

(* TODO: Move to \<^theory>\<open>HOL.List\<close> *)

lemma distinct_adj_conv_length_remdups_adj:
  "distinct_adj xs \<longleftrightarrow> length (remdups_adj xs) = length xs"
proof (induction xs rule: remdups_adj.induct)
  case (3 x y xs)
  thus ?case
    using remdups_adj_length[of "y # xs"] by auto
qed auto

lemma successively_conv_nth:
  "successively P xs \<longleftrightarrow> (\<forall>i. Suc i < length xs \<longrightarrow> P (xs ! i) (xs ! Suc i))"
  by (induction P xs rule: successively.induct)
     (force simp: nth_Cons split: nat.splits)+

lemma successively_nth: "successively P xs \<Longrightarrow> Suc i < length xs \<Longrightarrow> P (xs ! i) (xs ! Suc i)"
  unfolding successively_conv_nth by blast

lemma distinct_adj_conv_nth:
  "distinct_adj xs \<longleftrightarrow> (\<forall>i. Suc i < length xs \<longrightarrow> xs ! i \<noteq> xs ! Suc i)"
  by (simp add: distinct_adj_def successively_conv_nth)

lemma distinct_adj_nth: "distinct_adj xs \<Longrightarrow> Suc i < length xs \<Longrightarrow> xs ! i \<noteq> xs ! Suc i"
  unfolding distinct_adj_conv_nth by blast

text \<open>
  The following two lemmas give a full characterisation of the \<^const>\<open>filter\<close> function:
  The list \<^term>\<open>filter P xs\<close> is the only list \<open>ys\<close> for which there exists a strictly increasing
  function $f : \{0,\ldots,|\text{ys}|-1\} \to \{0,\ldots,|\text{xs}|-1\}$ such that:

    \<^item> $\text{ys}_i = \text{xs}_{f(i)}$

    \<^item> $P(\text{xs}_i) \longleftrightarrow \exists j{<}n.\ f(j) = i$, i.e.\ the range of $f$
      are precisely the indices of the elements of \<open>xs\<close> that satisfy \<open>P\<close>.

\<close>
lemma filterE:
  fixes P :: "'a \<Rightarrow> bool" and xs :: "'a list"
  assumes "length (filter P xs) = n"
  obtains f :: "nat \<Rightarrow> nat" where
    "strict_mono_on {..<n} f"
    "\<And>i. i < n \<Longrightarrow> f i < length xs"
    "\<And>i. i < n \<Longrightarrow> filter P xs ! i = xs ! f i"
    "\<And>i. i < length xs \<Longrightarrow> P (xs ! i) \<longleftrightarrow> (\<exists>j. j < n \<and> f j = i)"
  using assms(1)
proof (induction xs arbitrary: n thesis)
  case Nil
  thus ?case
    using that[of "\<lambda>_. 0"] by auto
next
  case (Cons x xs)
  define n' where "n' = (if P x then n - 1 else n)"
  obtain f :: "nat \<Rightarrow> nat" where f:
    "strict_mono_on {..<n'} f"
    "\<And>i. i < n'\<Longrightarrow> f i < length xs"
    "\<And>i. i < n' \<Longrightarrow> filter P xs ! i = xs ! f i"
    "\<And>i. i < length xs \<Longrightarrow> P (xs ! i) \<longleftrightarrow> (\<exists>j. j < n' \<and> f j = i)"
  proof (rule Cons.IH[where n = n'])
    show "length (filter P xs) = n'"
      using Cons.prems(2) by (auto simp: n'_def)
  qed auto
  define f' where "f' = (\<lambda>i. if P x then case i of 0 \<Rightarrow> 0 | Suc j \<Rightarrow> Suc (f j) else Suc (f i))"

  show ?case
  proof (rule Cons.prems(1))
    show "strict_mono_on {..<n} f'"
      by (auto simp: f'_def strict_mono_on_def n'_def strict_mono_onD[OF f(1)] split: nat.splits)
    show "f' i < length (x # xs)" if "i < n" for i
      using that f(2) by (auto simp: f'_def n'_def split: nat.splits)
    show "filter P (x # xs) ! i = (x # xs) ! f' i" if "i < n" for i
      using that f(3) by (auto simp: f'_def n'_def split: nat.splits)
    show "P ((x # xs) ! i) \<longleftrightarrow> (\<exists>j<n. f' j = i)" if "i < length (x # xs)" for i
    proof (cases i)
      case [simp]: 0
      show ?thesis using that Cons.prems(2)
        by (auto simp: f'_def intro!: exI[of _ 0])
    next
      case [simp]: (Suc i')
      have "P ((x # xs) ! i) \<longleftrightarrow> P (xs ! i')"
        by simp
      also have "\<dots> \<longleftrightarrow> (\<exists>j<n'. f j = i')"
        using that by (subst f(4)) simp_all
      also have "\<dots> \<longleftrightarrow> {j\<in>{..<n'}. f j = i'} \<noteq> {}"
        by blast
      also have "bij_betw (\<lambda>j. if P x then j+1 else j) {j\<in>{..<n'}. f j = i'} {j\<in>{..<n}. f' j = i}"
      proof (intro bij_betwI[of _ _ _ "\<lambda>j. if P x then j-1 else j"], goal_cases)
        case 2
        have "(if P x then j - 1 else j) < n'"
          if "j < n" "f' j = i" for j 
          using that by (auto simp: n'_def f'_def split: nat.splits)
        moreover have "f (if P x then j - 1 else j) = i'" if "j < n" "f' j = i" for j
          using that by (auto simp: n'_def f'_def split: nat.splits if_splits)
        ultimately show ?case by auto
      qed (auto simp: n'_def f'_def split: nat.splits)
      hence "{j\<in>{..<n'}. f j = i'} \<noteq> {} \<longleftrightarrow> {j\<in>{..<n}. f' j = i} \<noteq> {}"
        unfolding bij_betw_def by blast
      also have "\<dots> \<longleftrightarrow> (\<exists>j<n. f' j = i)"
        by auto
      finally show ?thesis .
    qed
  qed
qed

text \<open>
  The following lemma shows the uniqueness of the above property.
  It is very useful for finding a ``closed form'' for \<^term>\<open>filter P xs\<close> in some concrete
  situation. 
  
  For example, if we know that exactly every other element of \<open>xs\<close> satisfies \<open>P\<close>, 
  we can use it to prove that
  \<^prop>\<open>filter P xs = map (\<lambda>i. 2 * i) [0..<length xs div 2]\<close>
\<close>
lemma filter_eqI:
  fixes f :: "nat \<Rightarrow> nat" and xs ys :: "'a list"
  defines "n \<equiv> length ys"
  assumes "strict_mono_on {..<n} f"
  assumes "\<And>i. i < n \<Longrightarrow> f i < length xs"
  assumes "\<And>i. i < n \<Longrightarrow> ys ! i = xs ! f i"
  assumes "\<And>i. i < length xs \<Longrightarrow> P (xs ! i) \<longleftrightarrow> (\<exists>j. j < n \<and> f j = i)"
  shows   "filter P xs = ys"
  using assms(2-) unfolding n_def
proof (induction xs arbitrary: ys f)
  case Nil
  thus ?case by auto
next
  case (Cons x xs ys f)
  show ?case
  proof (cases "P x")
    case False
    have "filter P xs = ys"
    proof (rule Cons.IH)
      have pos: "f i > 0" if "i < length ys" for i
        using Cons.prems(4)[of "f i"] Cons.prems(2,3)[of i] that False
        by (auto intro!: Nat.gr0I)
      show "strict_mono_on {..<length ys} ((\<lambda>x. x - 1) \<circ> f)"
      proof (intro strict_mono_onI)
        fix i j assume ij: "i \<in> {..<length ys}" "j \<in> {..<length ys}" "i < j"
        thus "((\<lambda>x. x - 1) \<circ> f) i < ((\<lambda>x. x - 1) \<circ> f) j"
          using Cons.prems(1) pos[of i] pos[of j] 
          by (auto simp: strict_mono_on_def diff_less_mono)
      qed
      show "((\<lambda>x. x - 1) \<circ> f) i < length xs" if "i < length ys" for i
        using Cons.prems(2)[of i] pos[of i] that by auto
      show "ys ! i = xs ! ((\<lambda>x. x - 1) \<circ> f) i" if "i < length ys" for i
        using Cons.prems(3)[of i] pos[of i] that by auto
      show "P (xs ! i) \<longleftrightarrow> (\<exists>j<length ys. ((\<lambda>x. x - 1) \<circ> f) j = i)" if "i < length xs" for i
        using Cons.prems(4)[of "Suc i"] that pos by (auto split: if_splits)
    qed
    thus ?thesis
      using False by simp
  next
    case True
    have "ys \<noteq> []"
      using Cons.prems(4)[of 0] True by auto
    have [simp]: "f 0 = 0"
    proof -
      obtain j where "j < length ys" "f j = 0"
        using Cons.prems(4)[of 0] True by auto
      with strict_mono_onD[OF Cons.prems(1)] have "j = 0"
        by (metis gr_implies_not_zero lessThan_iff less_antisym zero_less_Suc)
      with \<open>f j = 0\<close> show ?thesis
        by simp
    qed
    have pos: "f j > 0" if "j > 0" "j < length ys" for j
      using strict_mono_onD[OF Cons.prems(1), of 0 j] that \<open>ys \<noteq> []\<close> by auto
    have f_eq_Suc_imp_pos: "j > 0" if "f j = Suc k" for j k
      by (rule Nat.gr0I) (use that in auto)

    define f' where "f' = (\<lambda>n. f (Suc n) - 1)"
    have "filter P xs = tl ys"
    proof (rule Cons.IH)
      show "strict_mono_on {..<length (tl ys)} f'"
      proof (intro strict_mono_onI)
        fix i j assume ij: "i \<in> {..<length (tl ys)}" "j \<in> {..<length (tl ys)}" "i < j"
        from ij have "Suc i < length ys" "Suc j < length ys"
          by auto
        thus "f' i < f' j"
          using strict_mono_onD[OF Cons.prems(1), of "Suc i" "Suc j"]
                pos[of "Suc i"] pos[of "Suc j"] \<open>ys \<noteq> []\<close> \<open>i < j\<close>
          by (auto simp: strict_mono_on_def diff_less_mono f'_def)
      qed
      show "f' i < length xs" and "tl ys ! i = xs ! f' i" if "i < length (tl ys)" for i
      proof -
        have "Suc i < length ys"
          using that by auto
        thus "f' i < length xs"
          using Cons.prems(2)[of "Suc i"] pos[of "Suc i"] that by (auto simp: f'_def)
        show "tl ys ! i = xs ! f' i"
          using \<open>Suc i < length ys\<close> that Cons.prems(3)[of "Suc i"] pos[of "Suc i"]
          by (auto simp: nth_tl nth_Cons f'_def split: nat.splits)
      qed
      show "P (xs ! i) \<longleftrightarrow> (\<exists>j<length (tl ys). f' j = i)" if "i < length xs" for i
      proof -
        have "P (xs ! i) \<longleftrightarrow> P ((x # xs) ! Suc i)"
          by simp
        also have "\<dots> \<longleftrightarrow> {j \<in> {..<length ys}. f j = Suc i} \<noteq> {}"
          using that by (subst Cons.prems(4)) auto
        also have "bij_betw (\<lambda>x. x - 1) {j \<in> {..<length ys}. f j = Suc i}
                     {j \<in> {..<length (tl ys)}. f' j = i}"
          by (rule bij_betwI[of _ _ _ Suc])
             (auto simp: f'_def Suc_diff_Suc f_eq_Suc_imp_pos diff_less_mono Suc_leI pos)
        hence "{j \<in> {..<length ys}. f j = Suc i} \<noteq> {} \<longleftrightarrow> {j \<in> {..<length (tl ys)}. f' j = i} \<noteq> {}"
          unfolding bij_betw_def by blast
        also have "\<dots> \<longleftrightarrow> (\<exists>j<length (tl ys). f' j = i)"
          by blast
        finally show ?thesis .
      qed
    qed
    moreover have "hd ys = x"
      using True \<open>f 0 = 0\<close> \<open>ys \<noteq> []\<close> Cons.prems(3)[of 0] by (auto simp: hd_conv_nth)
    ultimately show ?thesis
      using \<open>ys \<noteq> []\<close> True by force
  qed
qed

lemma filter_eq_iff:
  "filter P xs = ys \<longleftrightarrow>
     (\<exists>f. strict_mono_on {..<length ys} f \<and> 
          (\<forall>i<length ys. f i < length xs \<and> ys ! i = xs ! f i) \<and> 
          (\<forall>i<length xs. P (xs ! i) \<longleftrightarrow> (\<exists>j. j < length ys \<and> f j = i)))"
  (is "?lhs = ?rhs")
proof
  show ?rhs if ?lhs
    unfolding that [symmetric] by (rule filterE[OF refl, of P xs]) blast
  show ?lhs if ?rhs
    using that filter_eqI[of ys _ xs P] by blast
qed
(* END TODO *)

subsection \<open>Polynomials\<close>

(* TODO: Move to \<^theory>\<open>HOL-Computational_Algebra.Polynomial\<close> *)

lemma poly_of_nat [simp]: "poly (of_nat n) x = of_nat n"
  by (simp add: of_nat_poly)

lemma poly_of_int [simp]: "poly (of_int n) x = of_int n"
  by (simp add: of_int_poly) 

lemma poly_numeral [simp]: "poly (numeral n) x = numeral n"
  by (metis of_nat_numeral poly_of_nat)

lemma order_gt_0_iff: "p \<noteq> 0 \<Longrightarrow> order x p > 0 \<longleftrightarrow> poly p x = 0"
  by (subst order_root) auto

lemma order_eq_0_iff: "p \<noteq> 0 \<Longrightarrow> order x p = 0 \<longleftrightarrow> poly p x \<noteq> 0"
  by (subst order_root) auto

lemma coeff_pcompose_monom_linear [simp]:
  fixes p :: "'a :: comm_ring_1 poly"
  shows "coeff (pcompose p (monom c (Suc 0))) k = c ^ k * coeff p k"
  by (induction p arbitrary: k)
     (auto simp: coeff_pCons coeff_monom_mult pcompose_pCons split: nat.splits)

lemma of_nat_mult_conv_smult: "of_nat n * P = smult (of_nat n) P"
  by (simp add: monom_0 of_nat_monom)

lemma numeral_mult_conv_smult: "numeral n * P = smult (numeral n) P"
  by (metis of_nat_mult_conv_smult of_nat_numeral)

lemma has_field_derivative_poly [derivative_intros]:
  assumes "(f has_field_derivative f') (at x within A)"
  shows   "((\<lambda>x. poly p (f x)) has_field_derivative
             (f' * poly (pderiv p) (f x))) (at x within A)"
  using DERIV_chain[OF poly_DERIV assms, of p] by (simp add: o_def mult_ac)

lemma sum_order_le_degree:
  assumes "p \<noteq> 0"
  shows   "(\<Sum>x | poly p x = 0. order x p) \<le> degree p"
  using assms
proof (induction "degree p" arbitrary: p rule: less_induct)
  case (less p)
  show ?case
  proof (cases "\<exists>x. poly p x = 0")
    case False
    thus ?thesis
      by auto
  next
    case True
    then obtain x where x: "poly p x = 0"
      by auto
    have "[:-x, 1:] ^ order x p dvd p"
      by (simp add: order_1)
    then obtain q where q: "p = [:-x, 1:] ^ order x p * q"
      by (elim dvdE)
    have [simp]: "q \<noteq> 0"
      using q less.prems by auto
    have "order x p = order x p + order x q"
      by (subst q, subst order_mult) (auto simp: order_power_n_n)
    hence "order x q = 0"
      by auto
    hence [simp]: "poly q x \<noteq> 0"
      by (simp add: order_root)
    have deg_p: "degree p = degree q + order x p"
      by (subst q, subst degree_mult_eq) (auto simp: degree_power_eq)
    moreover have "order x p > 0"
      using x less.prems by (simp add: order_root)
    ultimately have "degree q < degree p"
      by linarith
    hence "(\<Sum>x | poly q x = 0. order x q) \<le> degree q"
      by (intro less.hyps) auto
    hence "order x p + (\<Sum>x | poly q x = 0. order x q) \<le> degree p"
      by (simp add: deg_p)
    also have "{y. poly q y = 0} = {y. poly p y = 0} - {x}"
      by (subst q) auto
    also have "(\<Sum>y \<in> {y. poly p y = 0} - {x}. order y q) =
               (\<Sum>y \<in> {y. poly p y = 0} - {x}. order y p)"
      by (intro sum.cong refl, subst q)
         (auto simp: order_mult order_power_n_n intro!: order_0I)
    also have "order x p + \<dots> = (\<Sum>y \<in> insert x ({y. poly p y = 0} - {x}). order y p)"
      using \<open>p \<noteq> 0\<close> by (subst sum.insert) (auto simp: poly_roots_finite)
    also have "insert x ({y. poly p y = 0} - {x}) = {y. poly p y = 0}"
      using \<open>poly p x = 0\<close> by auto
    finally show ?thesis .
  qed
qed
(* END TODO *)

subsection \<open>Trigonometric functions\<close>

(* TODO: Move to \<^theory>\<open>HOL.Transcendental\<close> *)
lemma sin_multiple_reduce:
  "sin (x * numeral n :: 'a :: {real_normed_field, banach}) = 
     sin x * cos (x * of_nat (pred_numeral n)) + cos x * sin (x * of_nat (pred_numeral n))"
proof -
  have "numeral n = of_nat (pred_numeral n) + (1 :: 'a)"
    by (metis add.commute numeral_eq_Suc of_nat_Suc of_nat_numeral)
  also have "sin (x * \<dots>) = sin (x * of_nat (pred_numeral n) + x)"
    unfolding of_nat_Suc by (simp add: ring_distribs)
  finally show ?thesis
    by (simp add: sin_add)
qed

lemma cos_multiple_reduce:
  "cos (x * numeral n :: 'a :: {real_normed_field, banach}) =
     cos (x * of_nat (pred_numeral n)) * cos x - sin (x * of_nat (pred_numeral n)) * sin x"
proof -
  have "numeral n = of_nat (pred_numeral n) + (1 :: 'a)"
    by (metis add.commute numeral_eq_Suc of_nat_Suc of_nat_numeral)
  also have "cos (x * \<dots>) = cos (x * of_nat (pred_numeral n) + x)"
    unfolding of_nat_Suc by (simp add: ring_distribs)
  finally show ?thesis
    by (simp add: cos_add)
qed

lemma arccos_eq_pi_iff: "x \<in> {-1..1} \<Longrightarrow> arccos x = pi \<longleftrightarrow> x = -1"
  by (metis arccos arccos_minus_1 atLeastAtMost_iff cos_pi)

lemma arccos_eq_0_iff: "x \<in> {-1..1} \<Longrightarrow> arccos x = 0 \<longleftrightarrow> x = 1"
  by (metis arccos arccos_1 atLeastAtMost_iff cos_zero)
(* END TODO *)


subsection \<open>Hyperbolic functions\<close>

(* TODO: Move to \<^theory>\<open>HOL.Transcendental\<close> *)
lemma cosh_double_cosh: "cosh (2 * x :: 'a :: {banach, real_normed_field}) = 2 * (cosh x)\<^sup>2 - 1"
  using cosh_double[of x] by (simp add: sinh_square_eq)

lemma sinh_multiple_reduce:
  "sinh (x * numeral n :: 'a :: {real_normed_field, banach}) = 
     sinh x * cosh (x * of_nat (pred_numeral n)) + cosh x * sinh (x * of_nat (pred_numeral n))"
proof -
  have "numeral n = of_nat (pred_numeral n) + (1 :: 'a)"
    by (metis add.commute numeral_eq_Suc of_nat_Suc of_nat_numeral)
  also have "sinh (x * \<dots>) = sinh (x * of_nat (pred_numeral n) + x)"
    unfolding of_nat_Suc by (simp add: ring_distribs)
  finally show ?thesis
    by (simp add: sinh_add)
qed

lemma cosh_multiple_reduce:
  "cosh (x * numeral n :: 'a :: {real_normed_field, banach}) =
     cosh (x * of_nat (pred_numeral n)) * cosh x + sinh (x * of_nat (pred_numeral n)) * sinh x"
proof -
  have "numeral n = of_nat (pred_numeral n) + (1 :: 'a)"
    by (metis add.commute numeral_eq_Suc of_nat_Suc of_nat_numeral)
  also have "cosh (x * \<dots>) = cosh (x * of_nat (pred_numeral n) + x)"
    unfolding of_nat_Suc by (simp add: ring_distribs)
  finally show ?thesis
    by (simp add: cosh_add)
qed

lemma cosh_arcosh_real [simp]:
  assumes "x \<ge> (1 :: real)"
  shows   "cosh (arcosh x) = x"
proof -
  have "eventually (\<lambda>t::real. cosh t \<ge> x) at_top"
    using cosh_real_at_top by (simp add: filterlim_at_top)
  then obtain t where "t \<ge> 1" "cosh t \<ge> x"
    by (metis eventually_at_top_linorder linorder_not_le order_le_less)
  moreover have "isCont cosh (y :: real)" for y
    by (intro continuous_intros)
  ultimately obtain y where "y \<ge> 0" "x = cosh y"
    using IVT[of cosh 0 x t] assms by auto
  thus ?thesis
    by (simp add: arcosh_cosh_real)
qed

lemma arcosh_eq_0_iff_real [simp]: "x \<ge> 1 \<Longrightarrow> arcosh x = 0 \<longleftrightarrow> x = (1 :: real)"
  using cosh_arcosh_real by fastforce

lemma arcosh_nonneg_real [simp]:
  assumes "x \<ge> 1"
  shows   "arcosh (x :: real) \<ge> 0"
proof -
  have "1 + 0 \<le> x + (x\<^sup>2 - 1) powr (1 / 2)"
    using assms by (intro add_mono) auto
  thus ?thesis unfolding arcosh_def by simp
qed

lemma arcosh_real_strict_mono:
  fixes x y :: real
  assumes "1 \<le> x" "x < y"
  shows   "arcosh x < arcosh y"
proof -
  have "cosh (arcosh x) < cosh (arcosh y)"
    by (subst (1 2) cosh_arcosh_real) (use assms in auto)
  thus ?thesis
    using assms by (subst (asm) cosh_real_nonneg_less_iff) auto
qed

lemma arcosh_less_iff_real [simp]:
  fixes x y :: real
  assumes "1 \<le> x" "1 \<le> y"
  shows   "arcosh x < arcosh y \<longleftrightarrow> x < y"
  using arcosh_real_strict_mono[of x y] arcosh_real_strict_mono[of y x] assms
  by (cases x y rule: linorder_cases) auto

lemma arcosh_real_gt_1_iff [simp]: "x \<ge> 1 \<Longrightarrow> arcosh x > 0 \<longleftrightarrow> x \<noteq> (1 :: real)"
  using arcosh_less_iff_real[of 1 x] by (auto simp del: arcosh_less_iff_real)

lemma sinh_arcosh_real: "x \<ge> 1 \<Longrightarrow> sinh (arcosh x) = sqrt (x\<^sup>2 - 1)"
  by (rule sym, rule real_sqrt_unique) (auto simp: sinh_square_eq)


lemma sinh_arsinh_real [simp]: "sinh (arsinh x :: real) = x"
proof -
  have "eventually (\<lambda>t::real. sinh t \<ge> x) at_top"
    using sinh_real_at_top by (simp add: filterlim_at_top)
  then obtain t where "sinh t \<ge> x"
    by (metis eventually_at_top_linorder linorder_not_le order_le_less)
  moreover have "eventually (\<lambda>t::real. sinh t \<le> x) at_bot"
    using sinh_real_at_bot by (simp add: filterlim_at_bot)
  then obtain t' where "t' \<le> t" "sinh t' \<le> x"
    by (metis eventually_at_bot_linorder nle_le)
  moreover have "isCont sinh (y :: real)" for y
    by (intro continuous_intros)
  ultimately obtain y where "x = sinh y"
    using IVT[of sinh t' x t] by auto
  thus ?thesis
    by (simp add: arsinh_sinh_real)
qed

lemma arsinh_real_strict_mono:
  fixes x y :: real
  assumes "x < y"
  shows   "arsinh x < arsinh y"
proof -
  have "sinh (arsinh x) < sinh (arsinh y)"
    by (subst (1 2) sinh_arsinh_real) (use assms in auto)
  thus ?thesis
    using assms by (subst (asm) sinh_real_less_iff) auto
qed

lemma arsinh_less_iff_real [simp]:
  fixes x y :: real
  shows "arsinh x < arsinh y \<longleftrightarrow> x < y"
  using arsinh_real_strict_mono[of x y] arsinh_real_strict_mono[of y x]
  by (cases x y rule: linorder_cases) auto

lemma arsinh_real_eq_0_iff [simp]: "arsinh x = 0 \<longleftrightarrow> x = (0 :: real)"
  by (metis arsinh_0 sinh_arsinh_real)

lemma arsinh_real_pos_iff [simp]: "arsinh x > 0 \<longleftrightarrow> x > (0 :: real)"
  using arsinh_less_iff_real[of 0 x] by (simp del: arsinh_less_iff_real)

lemma arsinh_real_neg_iff [simp]: "arsinh x < 0 \<longleftrightarrow> x < (0 :: real)"
  using arsinh_less_iff_real[of x 0] by (simp del: arsinh_less_iff_real)

lemma cosh_arsinh_real: "cosh (arsinh x) = sqrt (x\<^sup>2 + 1)"
  by (rule sym, rule real_sqrt_unique) (auto simp: cosh_square_eq)
(* END TODO *)

end