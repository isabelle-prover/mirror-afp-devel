section \<open>Tangent numbers\<close>
theory Tangent_Numbers
imports
  "HOL-Computational_Algebra.Computational_Algebra"
  "Bernoulli.Bernoulli_FPS" 
  "Polynomial_Interpolation.Ring_Hom_Poly"
  Boustrophedon_Transform_Library
  Alternating_Permutations
begin

subsection \<open>The higher derivatives of $\tan x$\<close>

text \<open>
  The $n$-th derivatives of $\tan x$ are:

    \<^item> $\tan x ^ 2 + 1$

    \<^item> $\tan x ^ 3 + \tan x$

    \<^item> $6 \tan x ^ 4 + 8 \tan x ^ 2 + 2$

    \<^item> $24 \tan x ^ 5 + 40 \tan x ^ 3 + 16 \tan x$

    \<^item> \dots

  No pattern is readily apparent, but it is obvious that for any $n$, the $n$-th derivative of 
  $\tan x$ can be expressed as a polynomial of degree $n+1$ in $\tan x$, i.e.\ it is of the form
  $P_n(\tan x)$ for some family of polynomials $P_n$.

  Using the fact that $\tan' x = \tan x ^ 2 + 1$ and the chain rule, one can deduce that
  $P_{n+1}(X) = (X^2 + 1)P_n'(X)$, and of course $P_0(X) = X$, which gives us a recursive 
  characterisation of $P_n$.
\<close>
primrec tangent_poly :: "nat \<Rightarrow> nat poly" where
  "tangent_poly 0 = [:0, 1:]"
| "tangent_poly (Suc n) = pderiv (tangent_poly n) * [:1,0,1:]"

lemma degree_tangent_poly [simp]: "degree (tangent_poly n) = n + 1"
  by (induction n)
     (auto simp: degree_mult_eq pderiv_eq_0_iff degree_pderiv simp del: mult_pCons_right)

lemma tangent_poly_altdef [code]:
  "tangent_poly n = ((\<lambda>p. pderiv p * [:1,0,1:]) ^^ n) [:0, 1:]"
  by (induction n) simp_all

lemma fps_tan_higher_deriv':
  "(fps_deriv ^^ n) (fps_tan (1::'a::field_char_0)) = 
     fps_compose (fps_of_poly (map_poly of_nat (tangent_poly n))) (fps_tan 1)"
proof -
  interpret of_nat_poly_hom: map_poly_comm_semiring_hom of_nat
    by standard auto
  show ?thesis
    by (induction n)
       (simp_all add: hom_distribs fps_of_poly_pderiv fps_of_poly_add
                      fps_of_poly_pCons fps_compose_add_distrib fps_compose_mult_distrib
                      fps_compose_deriv fps_tan_deriv' power2_eq_square of_nat_poly_pderiv)
qed

theorem fps_tan_higher_deriv:
  "(fps_deriv ^^ n) (fps_tan 1) = 
     poly (map_poly of_int (tangent_poly n)) (fps_tan (1::'a::field_char_0))"
  using fps_tan_higher_deriv'[of n]
  by (subst (asm) fps_compose_of_poly)
     (simp_all add: map_poly_map_poly o_def fps_of_nat)

text \<open>
  For easier notation, we give the name ``auxiliary tangent numbers'' to the coefficients of
  these polynomials and treat them as a number triangle $T_{n,j}$. These will aid us in
  the computation of the actual tangent numbers later.
\<close>
definition tangent_number_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "tangent_number_aux n j = poly.coeff (tangent_poly n) j"

text \<open>
  The coefficients satisfy the following recurrence and boundary conditions:

    \<^item> $T_{0, 1} = 1$

    \<^item> $T_{0, j} = 0$ if $j\neq 1$

    \<^item> $T_{n, j} = 0$ if $j > n+1$ or $n+j$ even

    \<^item> $T_{n, n+1} = n!$

    \<^item> $T_{n+1, j+1} = j T_{n,j} + (j+2) T_{n, j+2}$
\<close>
lemma tangent_number_aux_0_left:
  "tangent_number_aux 0 j = (if j = 1 then 1 else 0)"
  unfolding tangent_number_aux_def by (auto simp: coeff_pCons split: nat.splits)

lemma tangent_number_aux_0_left' [simp]:
  "j \<noteq> 1 \<Longrightarrow> tangent_number_aux 0 j = 0"
  "tangent_number_aux 0 (Suc 0) = 1"
  by (simp_all add: tangent_number_aux_0_left)

lemma tangent_number_aux_0_right:
  "tangent_number_aux (Suc n) 0 = poly.coeff (tangent_poly n) 1"
  unfolding tangent_number_aux_def tangent_poly.simps by (auto simp: coeff_pderiv)

lemma tangent_number_aux_rec:
  "tangent_number_aux (Suc n) (Suc j) = j * tangent_number_aux n j + (j + 2) * tangent_number_aux n (j + 2)"
  unfolding tangent_number_aux_def tangent_poly.simps
  by (simp_all add: coeff_pderiv coeff_pCons split: nat.splits)

lemma tangent_number_aux_rec':
  "n > 0 \<Longrightarrow> j > 0 \<Longrightarrow> tangent_number_aux n j = (j-1) * tangent_number_aux (n-1) (j-1) + (j+1) * tangent_number_aux (n-1) (j+1)"
  using tangent_number_aux_rec[of "n-1" "j-1"] by simp

lemma tangent_number_aux_odd_eq_0: "even (n + j) \<Longrightarrow> tangent_number_aux n j = 0"
  unfolding tangent_number_aux_def
  by (induction n arbitrary: j)
     (auto simp: coeff_pCons coeff_pderiv split: nat.splits)

lemma tangent_number_aux_eq_0 [simp]: "j > n + 1 \<Longrightarrow> tangent_number_aux n j = 0"
  unfolding tangent_number_aux_def by (simp add: coeff_eq_0)

lemma tangent_number_aux_last [simp]: "tangent_number_aux n (Suc n) = fact n"
  by (induction n) (auto simp: tangent_number_aux_rec)

lemma tangent_number_aux_last': "Suc m = n \<Longrightarrow> tangent_number_aux m n = fact m"
  by (cases n) auto

lemma tangent_number_aux_1_right [simp]:
  "tangent_number_aux i (Suc 0) = tangent_number_aux (i + 1) 0"
  by (simp add: tangent_number_aux_def coeff_pderiv)


subsection \<open>The tangent numbers\<close>

text \<open>
  The actual secant numbers $T_n$ are now defined to be the even-index coefficients of the
  power series expansion of $\tan x$ (the even-index ones are all $0$).~\oeiscite{A000182}

  This also turns out to be exactly the same as $T_{n, 0}$.
\<close>
definition tangent_number :: "nat \<Rightarrow> nat" where
  "tangent_number n = nat (floor (fps_nth (fps_tan 1) (2*n-1) * fact (2*n-1) :: real))"

lemma tangent_number_conv_zigzag_number:
  "n > 0 \<Longrightarrow> tangent_number n = zigzag_number (2 * n - 1)"
  unfolding tangent_number_def
  by (subst zigzag_number_conv_fps_tan [symmetric]) auto

lemma tangent_number_0 [simp]: "tangent_number 0 = 0"
  by (simp add: tangent_number_def fps_tan_def)

lemma fps_nth_tan_aux:
  "fps_tan (1::'a::field_char_0) $ (2*n-1) = 
     of_nat (tangent_number_aux (2*n-1) 0) / fact (2*n-1)"
proof (cases "n = 0")
  case False
  interpret of_nat_poly_hom: map_poly_comm_semiring_hom of_nat
    by standard auto
  from False have n: "n > 0"
    by simp
  have "fps_nth ((fps_deriv ^^ (2 * n - 1)) (fps_tan (1::'a))) 0 = 
          fact (2*n-1) * fps_nth (fps_tan 1) (2*n-1)"
    by (simp add: fps_0th_higher_deriv)
  also have "(fps_deriv ^^ (2*n-1)) (fps_tan (1::'a)) =
               fps_of_poly (map_poly of_nat (tangent_poly (2*n-1))) oo fps_tan 1"
    by (subst fps_tan_higher_deriv') auto
  also have "fps_nth \<dots> 0 = of_nat (tangent_number_aux (2*n-1) 0)"
    by (simp add: tangent_number_aux_def)
  finally show ?thesis
    by simp
qed auto

lemma fps_nth_tan:
  "fps_nth (fps_tan (1::'a :: field_char_0)) (2*n - Suc 0) = of_int (tangent_number n) / fact (2*n-1)"
  using fps_nth_tan_aux[of n, where ?'a = real] fps_nth_tan_aux[of n, where ?'a = 'a]
  by (simp add: tangent_number_def)

lemma tangent_number_conv_aux [code]:
  "tangent_number n = tangent_number_aux (2*n - Suc 0) 0"
  using fps_nth_tan[of n, where ?'a = real] fps_nth_tan_aux[of n, where ?'a = real] by simp

lemma tangent_number_1 [simp]: "tangent_number (Suc 0) = 1"
  by (simp add: tangent_number_conv_aux tangent_number_aux_0_right)


text \<open>
  The tangent number $T_n$ can be expressed in terms of the Bernoulli number $\mathcal{B}_n$:
\<close>
theorem tangent_number_conv_bernoulli:
   "2 * real n * of_int (tangent_number n) =
      (-1)^(n+1) * (2^(2*n) * (2^(2*n) - 1)) * bernoulli (2*n)"
proof -
  define F where "F = (\<lambda>c::complex. fps_compose bernoulli_fps (fps_const c * fps_X))"
  define E where "E = (\<lambda>c::complex. fps_to_fls (fps_exp c))"
  have neqI1: "f \<noteq> g" if "fls_nth f 0 \<noteq> fls_nth g 0" for f g :: "complex fls"
    using that by metis
  have [simp]: "fls_nth (E c) n = c ^ nat n / (fact (nat n))" if "n \<ge> 0" for n c
    using that by (auto simp: E_def)

  have [simp]: "subdegree (1 - fps_exp 1 :: complex fps) = 1"
    by (rule subdegreeI) auto
  have "fps_to_fls (F (2*\<i>) - F (4*\<i>) - fps_const \<i> * fps_X) = 
          2 * fls_const \<i> * fls_X / (E (2*\<i>) - 1) -
          4 * fls_const \<i> * fls_X / (E (4*\<i>) - 1) -
          fls_const \<i> * fls_X"
    unfolding F_def bernoulli_fps_def E_def
    apply (simp flip: fls_compose_fps_to_fls)
    apply (simp add: fls_compose_fps_divide fls_times_fps_to_fls fls_compose_fps_diff
                flip: fls_const_mult_const fls_divide_fps_to_fls)
    done
  also have "E (4 * \<i>) = E (2 * \<i>) ^ 2"
    by (simp add: fps_exp_power_mult E_def flip: fps_to_fls_power)
  also have "E (2 * \<i>) ^ 2 - 1 = (E (2 * \<i>) - 1) * (E (2 * \<i>) + 1)"
    by (simp add: algebra_simps power2_eq_square)
  also have "2 * fls_const \<i> * fls_X / (E (2 * \<i>) - 1) -
             4 * fls_const \<i> * fls_X / ((E (2 * \<i>) - 1) * (E (2 * \<i>) + 1)) =
             2 * fls_const \<i> * fls_X * (1 / (E (2 * \<i>) + 1))"
    unfolding E_def
    apply (simp add: divide_simps)
    apply (auto simp: algebra_simps add_eq_0_iff fls_times_fps_to_fls neqI1)
    done
  also have "1 / (E (2 * \<i>) + 1) = E (-\<i>) / (E (-\<i>) * (E (2 * \<i>) + 1))"
    by (simp add: divide_simps add_eq_0_iff2 neqI1)
  also have "E (-\<i>) * (E (2 * \<i>) + 1) = E \<i> + E (-\<i>)"
    by (simp add: E_def algebra_simps flip: fls_times_fps_to_fls fps_exp_add_mult)
  also have "2 * fls_const \<i> * fls_X * (E (-\<i>) / (E \<i> + E (-\<i>))) - fls_const \<i> * fls_X =
             fls_X * (fls_const (-\<i>) * (1 - 2 * E (-\<i>) / (E \<i> + E (-\<i>))))"
    by (simp add: algebra_simps)
  also have "1 - 2 * E (-\<i>) / (E \<i> + E (-\<i>)) = (E \<i> - E (-\<i>)) / (E \<i> + E (-\<i>))"
    by (simp add: divide_simps neqI1)
  also have "fls_const (-\<i>) * \<dots> = (-fls_const \<i>/2 * (E \<i> - E (-\<i>))) / ((E \<i> + E (-\<i>)) / 2)"
    by (simp add: divide_simps neqI1)
  also have "-fls_const \<i> / 2 * (E \<i> - E (-\<i>)) = fps_to_fls (fps_sin 1)"
    by (simp add: fps_sin_fps_exp_ii E_def fls_times_fps_to_fls flip: fls_const_divide_const)
  also have "(E \<i> + E (-\<i>)) / 2 = fps_to_fls (fps_cos 1)"
    by (simp add: fps_cos_fps_exp_ii E_def fls_times_fps_to_fls flip: fls_const_divide_const)
  also have "fls_X * (fps_to_fls (fps_sin 1) / fps_to_fls (fps_cos 1)) = 
               fps_to_fls (fps_X * fps_tan (1::complex))"
    by (simp add: fps_tan_def fls_times_fps_to_fls flip: fls_divide_fps_to_fls)
  finally have eq: "F (2 * \<i>) - F (4 * \<i>) - fps_const \<i> * fps_X =
                    fps_X * fps_tan 1" (is "?lhs = ?rhs") 
    by (simp only: fps_to_fls_eq_iff)

  show "2 * real n * of_int (tangent_number n) =
          (-1)^(n+1) * (2^(2*n) * (2^(2*n) - 1)) * bernoulli (2*n)"
  proof (cases "n = 0")
    case False
    hence n: "n > 0"
      by simp
    have "fps_nth ?lhs (2*n) = (-1)^n * (2^(2*n) - 4^(2*n)) * of_real (bernoulli (2 * n)) / fact (2*n)"
      using n unfolding F_def fps_nth_compose_linear fps_sub_nth
      by (simp add: algebra_simps diff_divide_distrib)
    also note \<open>?lhs = ?rhs\<close>
    also have "fps_nth ?rhs (2*n) = complex_of_int (tangent_number n) / fact (2 * n - 1)"
      using n by (simp add: fps_nth_tan)
    finally have "complex_of_int (tangent_number n) * (fact (2*n) / fact (2 * n - 1)) =
                  (- 1) ^ n * (2 ^ (2 * n) - 4 ^ (2 * n)) * complex_of_real (bernoulli (2 * n))"
      by (simp add: divide_simps)
    also have "complex_of_int (tangent_number n) * (fact (2*n) / fact (2 * n - 1)) =
               of_real (fact (2*n) / fact (2 * n - 1) * of_int (tangent_number n))"
      by (simp add: field_simps)
    also have "fact (2*n) / fact (2 * n - 1) = (2 * of_nat n :: real)"
      using fact_binomial[of 1 "2 * n", where ?'a = real] n by simp
    also have "2 ^ (2 * n) - 4 ^ (2 * n) = -(2 ^ (2 * n) * (2 ^ (2 * n) - 1 :: complex))"
      by (simp add: algebra_simps flip: power_mult_distrib)
    also have "(- 1) ^ n * - (2 ^ (2 * n) * (2 ^ (2 * n) - 1)) * complex_of_real (bernoulli (2 * n)) =
               of_real ((-1)^(n+1) * (2^(2*n) * (2^(2*n) - 1)) * bernoulli (2*n))"
      by simp
    finally show ?thesis
      by (simp only: of_real_eq_iff)
  qed auto
qed


subsection \<open>Efficient functional computation\<close>

text \<open>
  We will now formalise and verify an algorithm to compute the first $n$ tangent numbers 
  relatively efficiently via the auxiliary tangent numbers. The algorithm is a functional 
  variant of the imperative in-place algorithm given by Brent et al.~\<^cite>\<open>brent\<close>. The 
  functional algorithm could easily be adapted to one that returns a stream of all tangent numbers
  instead of a list of the first $n$ of them.

  The algorithm uses $O(n^2)$ additions and multiplications on integers, but since the numbers
  grow up to $\Theta(n \log n)$ bits, this translates to $O(n^3 \log{1+\varepsilon} n)$
  bit operations.

  Note that Brent et al.\ only define the tangent numbers $T_n$ starting with $n = 1$, whereas
  we also defined $T_0 = 0$. The algorithm only computes $T_1, \ldots, T_n$.
\<close>

function pochhammer_row_impl :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "pochhammer_row_impl k n x = (if k \<ge> n then [] else x # pochhammer_row_impl (Suc k) n (x * k))"
  by auto
termination by (relation "measure (\<lambda>(k,n,_) \<Rightarrow> n - k)") auto

lemmas [simp del] = pochhammer_row_impl.simps

lemma pochhammer_rec'': "k > 0 \<Longrightarrow> pochhammer n k = n * pochhammer (n+1) (k-1)"
  by (cases k) (auto simp: pochhammer_rec)

lemma pochhammer_row_impl_correct:
  "pochhammer_row_impl k n x = map (\<lambda>i. x * pochhammer k i) [0..<n-k]"
proof (induction k n x rule: pochhammer_row_impl.induct)
  case (1 k n x)
  show ?case
  proof (cases "k < n")
    case True
    have "pochhammer_row_impl k n x = x # map (\<lambda>i. x * k * pochhammer (Suc k) i) [0..<n - (k + 1)]"
      using True by (subst pochhammer_row_impl.simps) (simp_all add: "1.IH")
    also have "map (\<lambda>i. x * k * pochhammer (Suc k) i) [0..<n - (k + 1)] =
               map (\<lambda>i. x * pochhammer k i) (map Suc [0..<n - (k + 1)])"
      by (simp add: pochhammer_rec)
    also have "map Suc [0..<n - (k + 1)] = [Suc 0..<n-k]"
      using True by (simp add: map_Suc_upt Suc_diff_Suc del: upt_Suc)
    also have "x # map (\<lambda>i. x * pochhammer k i) [Suc 0..<n-k] =
               map (\<lambda>i. x * pochhammer k i) (0 # [Suc 0..<n-k])"
      by simp
    also have "0 # [Suc 0..<n-k] = [0..<n-k]"
      using True by (subst upt_conv_Cons) auto
    finally show ?thesis .
  qed (subst pochhammer_row_impl.simps; auto)
qed


context
  fixes T :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  defines "T \<equiv> tangent_number_aux"
begin

primrec tangent_number_impl_aux1 :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "tangent_number_impl_aux1 j y [] = []"
| "tangent_number_impl_aux1 j y (x # xs) =
     (let x' = j * y + (j+2) * x in x' # tangent_number_impl_aux1 (j+1) x' xs)"

lemma length_tangent_number_impl_aux1 [simp]: "length (tangent_number_impl_aux1 j y xs) = length xs"
  by (induction xs arbitrary: j y) (simp_all add: Let_def)

fun tangent_number_impl_aux2 :: "nat list \<Rightarrow> nat list" where
  "tangent_number_impl_aux2 [] = []"
| "tangent_number_impl_aux2 (x # xs) = x # tangent_number_impl_aux2 (tangent_number_impl_aux1 0 x xs)"

lemma tangent_number_impl_aux1_nth_eq:
  assumes "i < length xs"
  shows   "tangent_number_impl_aux1 j y xs ! i =
             (j+i) * (if i = 0 then y else tangent_number_impl_aux1 j y xs ! (i-1)) + (j+i+2) * xs ! i"
  using assms
proof (induction xs arbitrary: i j y)
  case (Cons x xs)
  show ?case
  proof (cases i)
    case 0
    thus ?thesis
      by (simp add: Let_def)
  next
    case (Suc i')
    define x' where "x' = j * y + (x + (x + j * x))"
    have "tangent_number_impl_aux1 j y (x # xs) ! i = tangent_number_impl_aux1 (Suc j) x' xs ! i'"
      by (simp add: x'_def Let_def Suc)
    also have "\<dots> = (Suc j + i') * (if i' = 0 then x' else tangent_number_impl_aux1 (Suc j) x' xs ! (i'-1)) + 
                    (Suc j + i' + 2) * xs ! i'"
      using Cons.prems by (subst Cons.IH) (auto simp: Suc)
    also have "Suc j + i' = j + i"
      by (simp add: Suc)
    also have "xs ! i' = (x # xs) ! i"
      by (auto simp: Suc)
    also have "(if i' = 0 then x' else tangent_number_impl_aux1 (Suc j) x' xs ! (i'-1)) =
               (x' # tangent_number_impl_aux1 j y (x # xs)) ! i"
      by (auto simp: Suc x'_def Let_def)
    finally show ?thesis
      by (simp add: Suc)
  qed
qed auto

lemma tangent_number_impl_aux2_correct:
  assumes "k \<le> n"
  shows  "tangent_number_impl_aux2 (map (\<lambda>i. T (2 * k + i) (i + 1)) [0..<n-k]) =
             map tangent_number [Suc k..<Suc n]"
  using assms
proof (induction k rule: inc_induct)
  case (step k)
  have *: "[0..<n-k] = 0 # map Suc [0..<n-Suc k]"
    by (subst upt_conv_Cons)
       (use step.hyps in \<open>auto simp: map_Suc_upt Suc_diff_Suc simp del: upt_Suc\<close>)
  define ts where 
    "ts = tangent_number_impl_aux1 0 (T (2*k) 1) (map (\<lambda>i. T (2*k+i+1) (i+2)) [0..<n-Suc k])"
  have T_rec: "T (Suc a) (Suc b) = b * T a b + (b + 2) * T a (b + 2)" for a b
    unfolding T_def tangent_number_aux_rec ..

  have "tangent_number_impl_aux2 (map (\<lambda>i. T (2 * k + i) (i + 1)) [0..<n-k]) =
          T (2 * k) 1 # tangent_number_impl_aux2 ts"
    unfolding * list.map tangent_number_impl_aux2.simps
    by (simp add: o_def ts_def algebra_simps numeral_3_eq_3)
  also have "ts = map (\<lambda>i. T (2 * Suc k + i) (i + 1)) [0..<n - Suc k]"
  proof (rule nth_equalityI)
    fix i assume "i < length ts"
    hence i: "i < n - Suc k"
      by (simp add: ts_def)
    hence "ts ! i = T (2 * Suc k + i) (i + 1)"
    proof (induction i)
      case 0
      thus ?case unfolding ts_def
        by (subst tangent_number_impl_aux1_nth_eq)
           (use T_rec[of "2*k+1" 0] in \<open>auto simp: eval_nat_numeral\<close>)
    next
      case (Suc i)
      have "ts ! Suc i = Suc i * T (Suc (Suc (2 * k + i))) (Suc i) +
                (Suc i + 2) * T (Suc (Suc (2 * k + i))) (Suc i + 2)"
        using Suc unfolding ts_def
        by (subst tangent_number_impl_aux1_nth_eq) (auto simp: eval_nat_numeral)
      also have "\<dots> = T (2 * Suc k + Suc i) (Suc i + 1)"
        using T_rec[of "2 * Suc k + i" "Suc i"] by simp
      finally show ?case .
    qed
    thus "ts ! i = map (\<lambda>i. T (2 * Suc k + i) (i + 1)) [0..<n - Suc k] ! i"
      using i by simp
  qed (simp_all add: ts_def)
  also have "tangent_number_impl_aux2 \<dots> = map tangent_number [Suc (Suc k)..<Suc n]"
    by (rule step.IH)
  also have "T (2 * k) 1 = tangent_number (Suc k)"
    by (simp add: tangent_number_conv_aux T_def)
  also have "tangent_number (Suc k) # map tangent_number [Suc (Suc k)..<Suc n] =
             map tangent_number [Suc k..<Suc n]"
    using step.hyps by (subst upt_conv_Cons) (auto simp del: upt_Suc)
  finally show ?case .
qed auto

definition tangent_numbers :: "nat \<Rightarrow> nat list" where
  "tangent_numbers n = map tangent_number [1..<Suc n]"

lemma tangent_numbers_code [code]:
  "tangent_numbers n = tangent_number_impl_aux2 (pochhammer_row_impl 1 (Suc n) 1)"
proof -
  have "pochhammer_row_impl 1 (Suc n) 1 = map (\<lambda>i. T i (i + 1)) [0..<n]"
    by (simp add: pochhammer_row_impl_correct pochhammer_fact T_def)
  also have "tangent_number_impl_aux2 \<dots> = map tangent_number [Suc 0..<Suc n]"
    using tangent_number_impl_aux2_correct[of 0 n] by (simp del: upt_Suc)
  finally show ?thesis
    by (simp only: tangent_numbers_def One_nat_def)
qed

lemma tangent_number_code [code]:
  "tangent_number n = (if n = 0 then 0 else last (tangent_numbers n))"
  by (simp add: tangent_numbers_def)

end

end