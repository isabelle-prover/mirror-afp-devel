section \<open>Secant numbers\<close>
theory Secant_Numbers
  imports
  "HOL-Computational_Algebra.Computational_Algebra"
  "Polynomial_Interpolation.Ring_Hom_Poly"
  Boustrophedon_Transform_Library
  Alternating_Permutations
  Tangent_Numbers
begin

subsection \<open>The higher derivatives of $\sec x$\<close>

text \<open>
  Similarly to what we saw with tangent numbers, the $n$-th derivatives of $\sec x$ do not
  follow an easily discernible pattern, but they can all be expressed in the form
  $\sec x P_n(\tan x)$, where $P_n$ is a polynomial of degree $n$.

  Using the facts that $\sec' x = \sec x \tan x$ and $\tan' x = 1 + \tan^2 x$ and the chain rule, 
  one can see that $P_n$ must satisfy the recurrence $P_{n+1}(X) = X P(X) + (1 + X^2) P'(X)$.
\<close>
primrec secant_poly :: "nat \<Rightarrow> nat poly" where
  "secant_poly 0 = 1"
| "secant_poly (Suc n) = (let p = secant_poly n in p * [:0, 1:] + pderiv p * [:1, 0, 1:])"

lemmas [simp del] = secant_poly.simps(2)

lemma degree_secant_poly [simp]: "degree (secant_poly n) = n"
proof (induction n)
  case (Suc n)
  define p where "p = secant_poly n"
  define q where "q = p * [:0, 1:]"
  define r where "r = pderiv p * [:1, 0, 1:]"
  have p: "degree p = n"
    using Suc.IH by (simp add: p_def)
  show ?case
  proof (cases "n = 0")
    case [simp]: True
    show ?thesis
      by (auto simp: secant_poly.simps(2))
  next
    case n: False
    have [simp]: "p \<noteq> 0" "pderiv p \<noteq> 0"
      using p n by (auto simp: pderiv_eq_0_iff)
    have q: "degree q = Suc n"
      unfolding q_def by (subst degree_mult_eq) (use p in auto)
    have r: "degree r = Suc n"
      unfolding r_def by (subst degree_mult_eq) (use p n in \<open>auto simp: degree_pderiv\<close>)

    have "secant_poly (Suc n) = q + r"
      by (simp add: Let_def secant_poly.simps(2) p_def q_def r_def)
    also have "degree \<dots> = Suc n"
    proof (rule antisym)
      show "degree (q + r) \<le> Suc n"
        using n by (intro degree_add_le) (auto simp: q r)
      show "degree (q + r) \<ge> Suc n"
      proof (rule le_degree)
        have "poly.coeff (q + r) (Suc n) = lead_coeff q + lead_coeff r"
          by (simp add: q r)
        also have "\<dots> = Suc (degree p) * lead_coeff p"
          by (simp add: q_def r_def lead_coeff_mult lead_coeff_pderiv del: mult_pCons_right)
        also have "\<dots> \<noteq> 0"
          by (subst mult_eq_0_iff) auto
        finally show "poly.coeff (q + r) (Suc n) \<noteq> 0" .
      qed
    qed
    finally show ?thesis .
  qed
qed auto

lemma secant_poly_altdef [code]:
  "secant_poly n = ((\<lambda>p. p * [:0,1:] + pderiv p * [:1, 0, 1:]) ^^ n) 1"
  by (induction n) (simp_all add: secant_poly.simps(2) Let_def)

lemma fps_sec_higher_deriv':
  "(fps_deriv ^^ n) (fps_sec (1::'a::field_char_0)) = 
     fps_sec 1 * fps_compose (fps_of_poly (map_poly of_nat (secant_poly n))) (fps_tan 1)"
proof -
  interpret of_nat_poly_hom: map_poly_comm_semiring_hom of_nat
    by standard auto
  show ?thesis
    by (induction n)
       (simp_all add: hom_distribs fps_of_poly_pderiv fps_of_poly_add fps_sec_deriv
                      fps_of_poly_pCons fps_compose_add_distrib fps_compose_mult_distrib
                      fps_compose_deriv fps_tan_deriv' power2_eq_square of_nat_poly_pderiv
                      secant_poly.simps(2) Let_def)
qed

theorem fps_sec_higher_deriv:
  "(fps_deriv ^^ n) (fps_sec 1) = 
     fps_sec 1 * poly (map_poly of_int (secant_poly n)) (fps_tan (1::'a::field_char_0))"
  using fps_sec_higher_deriv'[of n]
  by (subst (asm) fps_compose_of_poly)
     (simp_all add: map_poly_map_poly o_def fps_of_nat)


text \<open>
  For easier notation, we give the name ``auxiliary secant numbers'' to the coefficients of
  these polynomials and treat them as a number triangle $S_{n,j}$. These will aid us in
  the computation of the actual secant numbers later.
\<close>
definition secant_number_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "secant_number_aux n j = poly.coeff (secant_poly n) j"

text \<open>
  The coefficients satisfy the following recurrence and boundary conditions:

    \<^item> $S_{0, 0} = 1$

    \<^item> $S_{n, j} = 0$ if $j > n$ or $n+j$ odd

    \<^item> $S_{n,n} = n!$

    \<^item> $S_{n,j} = (j+1) S_{n,j} + (j+2) S_{n,j+2}$
\<close>
lemma secant_number_aux_0_left:
  "secant_number_aux 0 j = (if j = 0 then 1 else 0)"
  unfolding secant_number_aux_def by (auto simp: coeff_pCons split: nat.splits)

lemma secant_number_aux_0_left' [simp]:
  "j \<noteq> 0 \<Longrightarrow> secant_number_aux 0 j = 0"
  "secant_number_aux 0 0 = 1"
  by (simp_all add: secant_number_aux_0_left)

lemma secant_number_aux_0_right:
  "secant_number_aux (Suc n) 0 = secant_number_aux n 1"
  unfolding secant_number_aux_def secant_poly.simps by (auto simp: coeff_pderiv Let_def)

lemma secant_number_aux_rec:
  "secant_number_aux (Suc n) (Suc j) =
     (j+1) * secant_number_aux n j + (j + 2) * secant_number_aux n (j + 2)"
  unfolding secant_number_aux_def secant_poly.simps
  by (simp_all add: coeff_pderiv coeff_pCons Let_def split: nat.splits)

lemma secant_number_aux_rec':
  "n > 0 \<Longrightarrow> j > 0 \<Longrightarrow> secant_number_aux n j = j * secant_number_aux (n-1) (j-1) + (j+1) * secant_number_aux (n-1) (j+1)"
  using secant_number_aux_rec[of "n-1" "j-1"] by simp

lemma secant_number_aux_odd_eq_0: "odd (n + j) \<Longrightarrow> secant_number_aux n j = 0"
  unfolding secant_number_aux_def
  by (induction n arbitrary: j)
     (auto simp: coeff_pCons coeff_pderiv secant_poly.simps(2) Let_def elim: oddE split: nat.splits)

lemma secant_number_aux_eq_0 [simp]: "j > n \<Longrightarrow> secant_number_aux n j = 0"
  unfolding secant_number_aux_def by (simp add: coeff_eq_0)

lemma secant_number_aux_last [simp]: "secant_number_aux n n = fact n"
  by (induction n) (auto simp: secant_number_aux_rec)

lemma secant_number_aux_last': "m = n \<Longrightarrow> secant_number_aux m n = fact m"
  by (cases n) auto

lemma secant_number_aux_1_right [simp]:
  "secant_number_aux i (Suc 0) = secant_number_aux (i + 1) 0"
  by (simp add: secant_number_aux_def coeff_pderiv secant_poly.simps(2) Let_def)



subsection \<open>The secant numbers\<close>

text \<open>
  The actual secant numbers $S_n$ are now defined to be the even-index coefficients of the
  power series expansion of $\sec x$ (the odd-index ones are all $0$).\oeiscite{A000364}

  This also turns out to be exactly the same as $S_{n, 0}$.
\<close>
definition secant_number :: "nat \<Rightarrow> nat" where
  "secant_number n = nat (floor (fps_nth (fps_sec 1) (2*n) * fact (2*n) :: real))"

lemma secant_number_conv_zigzag_number:
  "secant_number n = zigzag_number (2 * n)"
  unfolding secant_number_def
  by (subst zigzag_number_conv_fps_sec [symmetric]) auto

lemma zigzag_number_conv_sectan [code]:
  "zigzag_number n = (if even n then secant_number (n div 2) else tangent_number ((n+1) div 2))"
  by (auto elim!: evenE simp: secant_number_conv_zigzag_number tangent_number_conv_zigzag_number)

lemma secant_number_0 [simp]: "secant_number 0 = 1"
  by (simp add: secant_number_def fps_sec_def)

lemma fps_nth_sec_aux:
  "fps_sec (1::'a::field_char_0) $ (2*n) = 
     of_nat (secant_number_aux (2*n) 0) / fact (2*n)"
proof (cases "n = 0")
  case False
  interpret of_nat_poly_hom: map_poly_comm_semiring_hom of_nat
    by standard auto
  from False have n: "n > 0"
    by simp
  have "fps_nth ((fps_deriv ^^ (2 * n)) (fps_sec (1::'a))) 0 = 
          fact (2*n) * fps_nth (fps_sec 1) (2*n)"
    by (simp add: fps_0th_higher_deriv)
  also have "(fps_deriv ^^ (2*n)) (fps_sec (1::'a)) =
               fps_sec 1 * (fps_of_poly (map_poly of_nat (secant_poly (2*n))) oo fps_tan 1)"
    by (subst fps_sec_higher_deriv') auto
  also have "fps_nth \<dots> 0 = of_nat (secant_number_aux (2*n) 0)"
    by (simp add: secant_number_aux_def)
  finally show ?thesis
    by simp
qed auto

lemma fps_nth_sec:
  "fps_nth (fps_sec (1::'a :: field_char_0)) (2*n) = of_int (secant_number n) / fact (2*n)"
  using fps_nth_sec_aux[of n, where ?'a = real] fps_nth_sec_aux[of n, where ?'a = 'a]
  by (simp add: secant_number_def)

lemma secant_number_conv_aux [code]:
  "secant_number n = secant_number_aux (2*n) 0"
  using fps_nth_sec[of n, where ?'a = real] fps_nth_sec_aux[of n, where ?'a = real] by simp

lemma secant_number_1 [simp]: "secant_number 1 = 1"
  by (simp add: secant_number_conv_aux secant_number_aux_def numeral_2_eq_2 
                secant_poly.simps(2) Let_def pderiv_pCons)


text \<open>
  By noting that $\tan'(x) = \sec(x)^2$ and comparing coefficients, one obtains the
  following identity that expresses the tangent numbers as a sum of secant numbers:
\<close>
theorem tangent_number_conv_secant_number:
  assumes n: "n > 0"
  shows   "tangent_number n = 
             (\<Sum>k<n. ((2*n-2) choose (2*k)) * secant_number k * secant_number (n - k - 1))"
proof -
  have [simp]: "Suc (2 * n - 2) = 2 * n - 1"
    using n by linarith
  define m where "m = 2 * n - 2"
  have "even m"
    using n by (auto simp: m_def)

  have "fps_deriv (fps_tan (1::real)) = fps_sec 1 ^ 2"
    by (simp add: fps_tan_deriv fps_sec_def fps_inverse_power fps_divide_unit)
  hence "fps_nth (fps_deriv (fps_tan (1::real))) (2*n-2) = fps_nth (fps_sec 1 ^ 2) m"
    unfolding fps_eq_iff m_def by blast
  hence "fact m * fps_nth (fps_deriv (fps_tan (1::real))) (2*n-2) = 
           fact m * fps_nth (fps_sec 1 ^ 2) m"
    by (rule arg_cong)
  also have "fps_nth (fps_deriv (fps_tan (1::real))) (2*n-2) =
               real (tangent_number n) * ((2 * real n - 1) / fact (2 * n - 1))"
    using n by (auto simp: fps_nth_tan of_nat_diff Suc_diff_Suc)
  also have "(2 * real n - 1) / fact (2 * n - 1) = 1 / fact m"
    using n by (cases n) (simp_all add: m_def)
  also have "fps_nth (fps_sec 1 ^ 2) m = (\<Sum>k\<le>m. fps_sec 1 $ k * fps_sec 1 $ (m - k))"
    by (simp add: fps_square_nth)
  also have "\<dots> = (\<Sum>k | k \<le> m \<and> even k. fps_sec 1 $ k * fps_sec 1 $ (m - k))"
    by (rule sum.mono_neutral_right) (use \<open>even m\<close> in \<open>auto simp: fps_nth_sec_odd\<close>)
  also have "\<dots> = (\<Sum>k<n. fps_sec 1 $ (2*k) * fps_sec 1 $ (m - 2 * k))"
    by (rule sum.reindex_bij_witness[of _ "\<lambda>k. 2 * k" "\<lambda>k. k div 2"]) 
       (use n in \<open>auto simp: m_def elim!: evenE\<close>)
  also have "fact m * \<dots> = 
               (\<Sum>k<n. real (((2 * n - 2) choose (2 * k)) * secant_number k * secant_number (n - k - 1)))"
    unfolding sum_distrib_left
  proof (intro sum.cong, goal_cases)
    case (2 k)
    have "fps_nth (fps_sec 1) (2 * (n - Suc k)) = secant_number (n - Suc k) / fact (2 * (n - Suc k))"
      by (subst fps_nth_sec) auto
    moreover have "2 * (n - Suc k) = m - 2 * k"
      using \<open>n > 0\<close> by (auto simp: m_def)
    ultimately have "fps_nth (fps_sec 1) (m - 2 * k) = secant_number (n - Suc k) / fact (2 * (n - Suc k))"
      by simp
    moreover have "fps_nth (fps_sec 1) (2 * k) = secant_number k / fact (2 * k)"
      by (subst fps_nth_sec) auto
    ultimately show ?case
      using 2 by (simp add: m_def diff_mult_distrib2 binomial_fact field_simps)
  qed auto
  also have "fact m * (real (tangent_number n) * (1 / fact m)) = real (tangent_number n)"
    by simp
  finally show ?thesis
    unfolding of_nat_sum [symmetric] by linarith
qed


subsection \<open>Efficient functional computation\<close>

text \<open>
  We again formalise a functional algorithm similar to what we have done for tangent numbers.
  This algorithm is again based on the one given by Brent et al.~\<^cite>\<open>brent\<close> and is completely
  analogous to the one for tangent numbers.
\<close>

context
  fixes S :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  defines "S \<equiv> secant_number_aux"
begin

primrec secant_number_impl_aux1 :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "secant_number_impl_aux1 j y [] = []"
| "secant_number_impl_aux1 j y (x # xs) =
     (let x' = j * y + (j+1) * x in x' # secant_number_impl_aux1 (j+1) x' xs)"

lemma length_secant_number_impl_aux1 [simp]: "length (secant_number_impl_aux1 j y xs) = length xs"
  by (induction xs arbitrary: j y) (simp_all add: Let_def)

fun secant_number_impl_aux2 :: "nat list \<Rightarrow> nat list" where
  "secant_number_impl_aux2 [] = []"
| "secant_number_impl_aux2 (x # xs) = x # secant_number_impl_aux2 (secant_number_impl_aux1 0 x xs)"

lemma secant_number_impl_aux1_nth_eq:
  assumes "i < length xs"
  shows   "secant_number_impl_aux1 j y xs ! i =
             (j+i) * (if i = 0 then y else secant_number_impl_aux1 j y xs ! (i-1)) + (j+i+1) * xs ! i"
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
    define x' where "x' = (j) * y + (j+1) * x"
    have "secant_number_impl_aux1 j y (x # xs) ! i = secant_number_impl_aux1 (Suc j) x' xs ! i'"
      by (simp add: x'_def Let_def Suc)
    also have "\<dots> = (Suc j + i') * (if i' = 0 then x' else secant_number_impl_aux1 (Suc j) x' xs ! (i'-1)) + 
                    (Suc j + i' + 1) * xs ! i'"
      using Cons.prems by (subst Cons.IH) (auto simp: Suc)
    also have "Suc j + i' = j + i"
      by (simp add: Suc)
    also have "xs ! i' = (x # xs) ! i"
      by (auto simp: Suc)
    also have "(if i' = 0 then x' else secant_number_impl_aux1 (Suc j) x' xs ! (i'-1)) =
               (x' # secant_number_impl_aux1 j y (x # xs)) ! i"
      by (auto simp: Suc x'_def Let_def)
    finally show ?thesis
      by (simp add: Suc)
  qed
qed auto

lemma secant_number_impl_aux2_correct:
  assumes "k \<le> n"
  shows  "secant_number_impl_aux2 (map (\<lambda>i. S (2 * k + i) i) [0..<n-k]) =
             map secant_number [k..<n]"
  using assms
proof (induction k rule: inc_induct)
  case (step k)
  have *: "[0..<n-k] = 0 # map Suc [0..<n-Suc k]"
    by (subst upt_conv_Cons)
       (use step.hyps in \<open>auto simp: map_Suc_upt Suc_diff_Suc simp del: upt_Suc\<close>)
  define ts where 
    "ts = secant_number_impl_aux1 0 (S (2*k) 0) (map (\<lambda>i. S (2*k+i+1) (i+1)) [0..<n-Suc k])"
  have S_rec: "S (Suc a) (Suc b) = (b + 1) * S a b + (b + 2) * S a (b + 2)" for a b
    unfolding S_def secant_number_aux_rec ..

  have "secant_number_impl_aux2 (map (\<lambda>i. S (2 * k + i) i) [0..<n-k]) =
          S (2 * k) 0 # secant_number_impl_aux2 ts"
    unfolding * list.map secant_number_impl_aux2.simps
    by (simp add: o_def ts_def algebra_simps numeral_3_eq_3)
  also have "ts = map (\<lambda>i. S (2 * Suc k + i) i) [0..<n - Suc k]"
  proof (rule nth_equalityI)
    fix i assume "i < length ts"
    hence i: "i < n - Suc k"
      by (simp add: ts_def)
    hence "ts ! i = S (2 * Suc k + i) i"
    proof (induction i)
      case 0
      thus ?case unfolding ts_def
        by (subst secant_number_impl_aux1_nth_eq) (simp_all add: S_def)
    next
      case (Suc i)
      have "ts ! Suc i = (i + 1) * S (2 * Suc k + i) i +
                (i + 2) * S (2 * Suc k + i) (Suc i + 1)"
        using Suc unfolding ts_def
        by (subst secant_number_impl_aux1_nth_eq) (simp_all add: eval_nat_numeral algebra_simps)
      also have "\<dots> = S (Suc (2 * Suc k + i)) (Suc i)"
        by (subst S_rec) simp_all
      finally show ?case by simp
    qed
    thus "ts ! i = map (\<lambda>i. S (2 * Suc k + i) i) [0..<n - Suc k] ! i"
      using i by simp
  qed (simp_all add: ts_def)
  also have "secant_number_impl_aux2 \<dots> = map secant_number [Suc k..<n]"
    by (rule step.IH)
  also have "S (2 * k) 0 = secant_number k"
    by (simp add: secant_number_conv_aux S_def)
  also have "secant_number k # map secant_number [Suc k..<n] =
             map secant_number [k..<n]"
    using step.hyps by (subst upt_conv_Cons) (auto simp del: upt_Suc)
  finally show ?case .
qed auto

definition secant_numbers :: "nat \<Rightarrow> nat list" where
  "secant_numbers n = map secant_number [0..<Suc n]"

lemma secant_numbers_code [code]:
  "secant_numbers n = secant_number_impl_aux2 (pochhammer_row_impl 1 (n+2) 1)"
proof -
  have "pochhammer_row_impl 1 (n+2) 1 = map (\<lambda>i. S i i) [0..<Suc n]"
    by (simp add: pochhammer_row_impl_correct pochhammer_fact S_def del: upt_Suc)
  also have "secant_number_impl_aux2 \<dots> = map secant_number [0..<Suc n]"
    using secant_number_impl_aux2_correct[of 0 "Suc n"] by (simp del: upt_Suc)
  finally show ?thesis
    by (simp only: secant_numbers_def One_nat_def)
qed

lemma secant_number_code [code]: "secant_number n = last (secant_numbers n)"
  by (simp add: secant_numbers_def)

end


definition zigzag_numbers :: "nat \<Rightarrow> nat list" where
  "zigzag_numbers n = map zigzag_number [0..<Suc n]"

lemma nth_splice:
  "i < length xs + length ys \<Longrightarrow>
     splice xs ys ! i =
       (if length xs \<le> length ys then
          if i < 2 * length xs then if even i then xs ! (i div 2) else ys ! (i div 2) else ys ! (i - length xs)
        else if i < 2 * length ys then if even i then xs ! (i div 2) else ys ! (i div 2) else xs ! (i - length ys))"
proof (induction xs ys arbitrary: i rule: splice.induct)
  case (2 x xs ys)
  show ?case
  proof (cases i)
    case i: (Suc i')
    have "splice (x # xs) ys ! i = splice ys xs ! i'"
      by (simp add: i)
    also have "\<dots> = (if length ys \<le> length xs
                     then if i' < 2 * length ys
                     then if even i' then ys ! (i' div 2) else xs ! (i' div 2) else xs ! (i' - length ys)
                     else if i' < 2 * length xs 
                     then if even i' then ys ! (i' div 2) else xs ! (i' div 2) else ys ! (i' - length xs))"
      by (rule "2.IH") (use "2.prems" i in auto)
    also have "\<dots> = (if length (x # xs) \<le> length ys then if i < 2 * length (x # xs)
                     then if even i then (x # xs) ! (i div 2) else ys ! (i div 2)
                     else ys ! (i - length (x # xs)) else if i < 2 * length ys
                     then if even i then (x # xs) ! (i div 2) else ys ! (i div 2)
                     else (x # xs) ! (i - length ys))"
      using "2.prems" by (force simp: i not_less intro!: arg_cong2[of _ _ _ _ nth] elim!: oddE evenE)
    finally show ?thesis .
  qed auto
qed auto

lemma zigzag_numbers_code [code]:
  "zigzag_numbers n = splice (secant_numbers (n div 2)) (tangent_numbers ((n+1) div 2))"
proof (rule nth_equalityI)
  fix i assume "i < length (zigzag_numbers n)"
  hence i: "i \<le> n"
    by (simp add: zigzag_numbers_def)
  define xs where "xs = secant_numbers (n div 2)"
  define ys where "ys = tangent_numbers ((n+1) div 2)"
  have [simp]: "length xs = n div 2 + 1" "length ys = (n+1) div 2"
    by (simp_all add: xs_def ys_def secant_numbers_def tangent_numbers_def)
  have "splice xs ys ! i = (if even i then xs ! (i div 2) else ys ! (i div 2))"
  proof (subst nth_splice, goal_cases)
    case 2
    show ?case
      by (cases "even n")
         (use i in \<open>auto elim!: evenE oddE simp: not_less double_not_eq_Suc_double 
                         intro!: arg_cong2[of _ _ _ _ nth]\<close>)
  qed (use i in auto)
  also have "\<dots> = zigzag_numbers n ! i"
    using i by (auto simp: zigzag_numbers_def secant_numbers_def tangent_numbers_def
                           zigzag_number_conv_sectan xs_def ys_def
                     elim!: evenE oddE simp del: upt_Suc)
  finally show "zigzag_numbers n ! i = splice xs ys ! i" ..
qed (auto simp: secant_numbers_def tangent_numbers_def zigzag_numbers_def)

end