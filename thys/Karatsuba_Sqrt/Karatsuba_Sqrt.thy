theory Karatsuba_Sqrt                                   
imports
  Complex_Main
  Karatsuba_Sqrt_Library
begin

subsection \<open>Definition of an integer square root with remainder\<close>

definition sqrt_rem :: "nat \<Rightarrow> nat" where
  "sqrt_rem n = n - floor_sqrt n ^ 2"

lemma sqrt_rem_upper_bound: "sqrt_rem n \<le> 2 * floor_sqrt n"
proof -
  define s where "s = floor_sqrt n"
  have "n < (s + 1) ^ 2"
    unfolding s_def using Suc_floor_sqrt_power2_gt[of n] by auto
  hence "n + 1 \<le> (s + 1) ^ 2"
    by linarith
  hence "n \<le> s ^ 2 + 2 * s"
    by (simp add: algebra_simps power2_eq_square)
  thus ?thesis
    unfolding s_def sqrt_rem_def by linarith
qed

lemma of_nat_sqrt_rem:
  "(of_nat (sqrt_rem n) :: 'a :: ring_1) = of_nat n - of_nat (floor_sqrt n) ^ 2"
  by (simp add: sqrt_rem_def)

definition sqrt_rem' where "sqrt_rem' n = (floor_sqrt n, sqrt_rem n)"

lemma Discrete_sqrt_code [code]: "floor_sqrt n = fst (sqrt_rem' n)"
  by (simp add: sqrt_rem'_def)

lemma sqrt_rem_code [code]: "sqrt_rem n = snd (sqrt_rem' n)"
  by (simp add: sqrt_rem'_def)



subsection \<open>Heron's method\<close>

text \<open>
  The method used here is a variant of Heron's method, which is itself essentially Newton's method 
  specialised to square roots. This is already in the AFP under the name ``Babylonian method''.
  However, that entry derives a more general version for \<open>n\<close>-th roots and lacks some flexibility
  that is useful for us here, so we instead derive a simple version for the square root
  directly. We will use this version in the base case of the algorithm.

  The starting value must be bigger than $\lfloor \sqrt{n}\rfloor$. We simply use
  $2^{\lceil \frac{1}{2}\log_2 n \rceil}$, which is easy to compute and fairly close to
  $\sqrt{n}$ already so that the Newton iterations converge very quickly.
\<close>

context
  fixes n :: nat
begin

function sqrt_rem_aux :: "nat \<Rightarrow> nat \<times> nat" where
  "sqrt_rem_aux x =
     (if x\<^sup>2 \<le> n then (x, n - x\<^sup>2) else sqrt_rem_aux ((n div x + x) div 2))"
  by auto
termination proof (relation "Wellfounded.measure id")
  fix x assume x: "\<not>(x\<^sup>2 \<le> n)"
  have "n div x * x \<le> n"
    by simp
  also from x have "n < x * x"
    by (simp add: power2_eq_square)
  finally have "n div x < x"
    using x by simp
  hence "(n div x + x) div 2 < x"
    by (subst div_less_iff_less_mult) auto
  thus "((n div x + x) div 2, x) \<in> measure id"
    by simp
qed auto

lemmas [simp del] = sqrt_rem_aux.simps

lemma sqrt_rem_aux_code [code]:
  "sqrt_rem_aux x = (
    let x2 = x*x; r = int n - int x2
    in if r \<ge> 0 then (x, nat r) else sqrt_rem_aux (drop_bit 1 (n div x + x)))"
  by (subst sqrt_rem_aux.simps)
     (auto simp: Let_def case_prod_unfold power2_eq_square nat_diff_distrib drop_bit_eq_div
           simp flip: of_nat_mult)

lemma sqrt_rem_aux_decompose: "fst (sqrt_rem_aux x) ^ 2 + snd (sqrt_rem_aux x) = n"
  by (induction x rule: sqrt_rem_aux.induct; subst (1 2) sqrt_rem_aux.simps) auto

lemma sqrt_rem_aux_correct:
  assumes "x \<ge> floor_sqrt n"
  shows   "fst (sqrt_rem_aux x) = floor_sqrt n"
  using assms
proof (induction x rule: sqrt_rem_aux.induct)
  case (1 x)
  show ?case
  proof (cases "x ^ 2 \<le> n")
    case True
    from True have "floor_sqrt n \<ge> x"
      by (simp add: le_floor_sqrtI)
    with "1.prems" show ?thesis using True
      by (subst sqrt_rem_aux.simps) auto
  next
    case False
    hence "x > 0"
      by (auto intro!: Nat.gr0I)
    have "0 < (x ^ 2 - n) ^ 2 / (4 * x ^ 2)"
      using \<open>x > 0\<close> False by (intro divide_pos_pos) auto
    also have "(x ^ 2 - n) ^ 2 / (4 * x ^ 2) = ((n / x + x) / 2) ^ 2 - n"
      using \<open>x > 0\<close> False by (simp add: field_simps power2_eq_square)
    finally have "n < ((n / x + x) / 2) ^ 2"
      by simp
    hence "sqrt n ^ 2 < ((n / x + x) / 2) ^ 2"
      by simp
    hence "sqrt n < (n / x + x) / 2"
      by (rule power_less_imp_less_base) auto
    hence "nat (floor (sqrt n)) \<le> nat (floor ((n / x + x) / 2))"
      by linarith
    also have "nat (floor (sqrt n)) = floor_sqrt n"
      by (simp add: floor_sqrt_conv_floor_of_sqrt)
    also have "floor ((n / x + x) / 2) = (n div x + x) div 2"
      using floor_divide_real_eq_div[of 2 "n / x + x"] by (simp add: floor_divide_of_nat_eq)
    finally have "floor_sqrt n \<le> (n div x + x) div 2"
      by simp
    from "1.IH"[OF False this] show ?thesis
      by (subst sqrt_rem_aux.simps) (use False in auto)
  qed
qed

lemma sqrt_rem_aux_correct':
  assumes "x \<ge> floor_sqrt n"
  shows   "sqrt_rem_aux x = sqrt_rem' n"
  using sqrt_rem_aux_correct[OF assms] sqrt_rem_aux_decompose[of x]
  by (simp add: sqrt_rem'_def prod_eq_iff sqrt_rem_def)

definition sqrt_rem'_heron :: "nat \<times> nat" where
  "sqrt_rem'_heron = sqrt_rem_aux (push_bit ((ceillog2 n + 1) div 2) 1)"

lemma sqrt_rem'_heron_correct:
  "sqrt_rem'_heron = sqrt_rem' n"
proof (cases "n = 0")
  case True
  show ?thesis unfolding sqrt_rem'_heron_def
    by (rule sqrt_rem_aux_correct') (auto simp: True)
next
  case False
  hence n: "n > 0"
    by auto
  show ?thesis unfolding sqrt_rem'_heron_def
  proof (rule sqrt_rem_aux_correct')
    have "real (floor_sqrt n) \<le> sqrt n"
      by (simp add: floor_sqrt_conv_floor_of_sqrt)
    also have "\<dots> = 2 powr log 2 (sqrt n)"
      using n by simp
    also have "log 2 (sqrt n) = log 2 n / 2"
      using n by (simp add: log_def ln_sqrt)
    also have "(2::real) powr \<dots> \<le> 2 powr ((ceillog2 n + 1) div 2)"
    proof (intro powr_mono)
      have "log 2 (real n) \<le> real (ceillog2 n)"
        by (simp add: ceillog2_ge_log n)
      also have "\<dots> / 2 \<le> (ceillog2 n + 1) div 2"
        by linarith
      finally show "log 2 n / 2 \<le> (ceillog2 n + 1) div 2"
        by - simp_all
    qed auto
    also have "\<dots> = real (2 ^ ((ceillog2 n + 1) div 2))"
      by (subst powr_realpow) auto
    also have "2 ^ ((ceillog2 n + 1) div 2) = push_bit ((ceillog2 n + 1) div 2) 1"
      by (simp add: push_bit_eq_mult)
    finally show "floor_sqrt n \<le> push_bit ((ceillog2 n + 1) div 2) 1"
      by linarith
  qed
qed

end

lemmas [code] = sqrt_rem'_heron_correct [symmetric]


subsection \<open>Main algorithm\<close>

subsubsection \<open>Single step\<close>

definition splice_bit where
  "splice_bit i n x = take_bit n (drop_bit i x)"

lemma of_nat_splice_bit:
  "of_nat (splice_bit i n x) =
     splice_bit i n (of_nat x :: 'a :: linordered_euclidean_semiring_bit_operations)"
  by (simp add: splice_bit_def of_nat_take_bit of_nat_drop_bit)

definition karatsuba_sqrt_step where
  "karatsuba_sqrt_step a32 a1 a0 b =
     (let (s, r) = sqrt_rem' a32;
          (q, u) = ((r * b + a1) div (2 * s), (r * b + a1) mod (2 * s));
          s' = int (s * b + q);
          r' = int (u * b + a0) - int (q ^ 2)
      in  if r' \<ge> 0 then (s', r') else (s' - 1, r' + 2 * s' - 1))"

definition karatsuba_sqrt_step' :: "nat \<Rightarrow> nat \<Rightarrow> int \<times> int" where
  "karatsuba_sqrt_step' n k =
     (let (s, r) = map_prod int int (sqrt_rem' (drop_bit (2*k) n));
          (q, u) = divmod_int (push_bit k r + splice_bit k k n) (push_bit 1 s);
          s' = push_bit k s + q;
          r' = push_bit k u + take_bit k n - q ^ 2
      in  if r' \<ge> 0 then (s', r') else (s' - 1, r' + push_bit 1 s' - 1))"

text \<open>
  Note that unlike Zimmerman, we do not have any upper bound on $a_{3}$ since this bound
  turned out to be unnecessary for the correctness of the algorithm. As long as $b^4$ is not much
  smaller than $n$, there is no efficiency problem either, since the step will still strip away
  about half of the bits of $n$.

  The advantage of this is that we do not have to do the ``normalisation'' done by Zimmerman to
  ensure that at least one of the two most significant bits of $a_3$ be set.
\<close>
lemma karatsuba_sqrt_step_correct:
  fixes a32 a1 a0 :: nat
  assumes "a1 < b" "a0 < b" "4 * a32 \<ge> b ^ 2" "even b"
  defines "n \<equiv> a32 * b ^ 2 + a1 * b + a0"
  shows   "karatsuba_sqrt_step a32 a1 a0 b =
             map_prod of_nat of_nat (sqrt_rem' n)"
proof -
  define s where "s = floor_sqrt a32"
  define r where "r = sqrt_rem a32"
  define q where "q = (r * b + a1) div (2 * s)"
  define u where "u = (r * b + a1) mod (2 * s)"
  define s' where "s' = int (s * b + q)"
  define r' where "r' = int (u * b + a0) - int (q ^ 2)"
  define s'' where "s'' = (if r' \<ge> 0 then s' else s' - 1)"
  define r'' where "r'' = (if r' \<ge> 0 then r' else r'  + 2 * s' - 1)"

  from assms have "b > 0"
    by auto
  have "s > 0"
    using assms by (auto simp: s_def intro!: Nat.gr0I)

  have "b \<le> 2 * s"
  proof -
    have "4 * (b div 2) ^ 2 = b ^ 2"
      using \<open>even b\<close> by (auto elim!: evenE simp: power2_eq_square)
    also have "\<dots> \<le> 4 * a32"
      by fact
    finally have "b div 2 \<le> s"
      unfolding s_def by (subst le_floor_sqrt_iff) auto
    thus "b \<le> 2 * s"
      using \<open>even b\<close> by (elim evenE) auto
  qed

  have s'_r': "int n = s' ^ 2 + r'"
  proof -
    have *: "int a1 = int q * (2 * int s) + int u - int r * int b"
      using arg_cong[OF div_mod_decomp[of "r * b + a1" "2 * s"], of int, folded q_def u_def]
      unfolding of_nat_add of_nat_mult by linarith
    have "int n = (int s ^ 2 + int r) * int b ^ 2 + int a1 * int b + int a0"
      by (simp add: n_def s_def r_def of_nat_sqrt_rem algebra_simps power_numeral_reduce)
    also have "\<dots> = s' ^ 2 + r'"
      by (simp add: power2_eq_square algebra_simps * r'_def s'_def)
    finally show "int n = s' ^ 2 + r'" .
  qed
  hence s''_r'': "int n = s'' ^ 2 + r''"
    by (simp add: s''_def r''_def power2_eq_square algebra_simps)

  have "int n < (s' + 1) ^ 2"
  proof -
    define t where "t = floor_sqrt n - s * b"
    have "s ^ 2 * b ^ 2 \<le> a32 * b ^ 2"
      unfolding s_def by (intro mult_right_mono floor_sqrt_power2_le) auto
    also have "\<dots> \<le> n"
      by (simp add: n_def)
    finally have "(s * b) ^ 2 \<le> n"
      by (simp add: power_mult_distrib)
    hence "floor_sqrt n \<ge> s * b"
      by (simp add: le_floor_sqrt_iff)
    hence sqrt_n_eq: "floor_sqrt n = s * b + t"
      unfolding t_def by simp

    have "int (2 * s * t * b) = 2 * int s * int b * int t"
      by simp
    also have "2 * int s * int b * int t \<le> 2 * int s * int b * int t + int t ^ 2"
      by simp
    also have "\<dots> = int ((s * b + t) ^ 2) - (int s * int b) ^ 2"
      unfolding of_nat_power of_nat_mult of_nat_add by algebra
    also have "s * b + t = floor_sqrt n"
      by (simp add: sqrt_n_eq)
    also have "floor_sqrt n ^ 2 \<le> n"
      by simp
    also have "n - (int s * int b) ^ 2 = int (a1 * b + a0) + (int a32 - int s ^ 2) * int b ^ 2"
      unfolding n_def of_nat_add of_nat_mult of_nat_power by algebra
    also have "int a32 - int s ^ 2 = int r"
      unfolding r_def by (simp add: of_nat_sqrt_rem s_def)
    also have "a0 < b"
      by fact
    also have "int (a1 * b + b) + int r * (int b)\<^sup>2 = int ((a1 + 1 + r * b) * b)"
      by (simp add: algebra_simps power2_eq_square)
    finally have "2 * s * t * b < (a1 + 1 + r * b) * b"
      unfolding of_nat_less_iff by - simp_all
    hence "2 * s * t < a1 + 1 + r * b"
      using \<open>b > 0\<close> mult_less_cancel2 by blast
    hence "2 * s * t \<le> r * b + a1"
      by linarith
    hence "t \<le> q"
      unfolding q_def using \<open>s > 0\<close>
      by (subst less_eq_div_iff_mult_less_eq) (auto simp: algebra_simps)
    with sqrt_n_eq have *: "floor_sqrt n \<le> s * b + q"
      by simp

    have "n < (floor_sqrt n + 1) ^ 2"
        using Suc_floor_sqrt_power2_gt[of n] by simp
    also have "\<dots> \<le> (s * b + q + 1) ^ 2"
      by (intro power_mono add_mono *) auto
    finally have "int n < int ((s * b + q + 1) ^ 2)"
      by linarith
    thus "int n < (s' + 1) ^ 2"
      by (simp add: algebra_simps s'_def)
  qed

  have "q \<le> r"
  proof -
    have "q \<le> (r * b + a1) div b"
      unfolding q_def using \<open>b \<le> 2 * s\<close> \<open>b > 0\<close> by (intro div_le_mono2)
    also have "\<dots> = r"
      using \<open>b > 0\<close> assms by simp
    finally show "q \<le> r" .
  qed

  have "int (q ^ 2) < 2 * s'"
  proof (cases "q = 0")
    case False
    have "q ^ 2 \<le> 2 * s * b"
      unfolding power2_eq_square
    proof (intro mult_mono)
      show "q \<le> 2 * s"
        using \<open>q \<le> r\<close> sqrt_rem_upper_bound[of a32] unfolding r_def s_def by linarith
    next
      show "q \<le> b"
      proof -
        have "r \<le> 2 * s"
          using \<open>q \<le> r\<close> unfolding r_def s_def using sqrt_rem_upper_bound[of a32] by linarith
        hence "q \<le> (2 * s * b + a1) div (2 * s)"
          unfolding q_def by (intro div_le_mono add_mono mult_right_mono) auto
        also have "\<dots> = b + a1 div (2 * s)"
          using assms \<open>s > 0\<close> by simp
        also have "a1 div (2 * s) = 0"
          using \<open>b \<le> 2 * s\<close> \<open>a1 < b\<close> by auto
        finally show "q \<le> b" by simp
      qed
    qed auto
    also have "2 * s * b < 2 * (s * b + q)"
      using \<open>q \<noteq> 0\<close> by (simp add: algebra_simps)
    also have "int \<dots> = 2 * s'"
      by (simp add: s'_def)
    finally show ?thesis by - simp_all
  qed (use \<open>s > 0\<close> \<open>b > 0\<close> in \<open>auto simp: s'_def\<close>)

  have "r'' \<ge> 0"
  proof (cases "r' \<ge> 0")
    case False
    have "r' + 2 * s' > 0"
      unfolding r'_def using \<open>int (q ^ 2) < 2 * s'\<close> by linarith
    thus ?thesis
      unfolding r''_def by auto
  qed (auto simp: r''_def)

  have "s'' \<ge> 0"
    using \<open>0 \<le> r''\<close> unfolding r''_def s''_def s'_def by auto

  have "s'' ^ 2 \<le> int n"
  proof -
    have "s'' ^ 2 = int n - r''"
      using s''_r'' by simp
    also have "\<dots> \<le> int n"
      using \<open>r'' \<ge> 0\<close> by simp
    finally show "s'' ^ 2 \<le> n" .
  qed

  have "floor_sqrt n = nat s''"
  proof (rule floor_sqrt_unique)
    show "nat s'' ^ 2 \<le> n"
      using \<open>s'' ^ 2 \<le> int n\<close>
      by (metis nat_eq_iff2 of_nat_le_of_nat_power_cancel_iff zero_eq_power2 zero_le)
  next
    have "int n < (s'' + 1) ^ 2"
    proof (cases "r' \<ge> 0")
      case True
      show ?thesis
        using True \<open>int n < (s' + 1) ^ 2\<close> by (simp add: s''_def)
    next
      case False
      have "int n < s' ^ 2"
        using False s'_r' by auto
      thus ?thesis using False by (simp add: s''_def)
    qed
    also have "(s'' + 1) ^ 2 = int (Suc (nat s'') ^ 2)"
      using \<open>s'' \<ge> 0\<close> by simp
    finally show "n < Suc (nat s'') ^ 2"
      by linarith
  qed
  moreover from this have "int (sqrt_rem n) = r''"
    using s''_r'' \<open>s'' \<ge> 0\<close> unfolding of_nat_sqrt_rem by auto
  hence "sqrt_rem n = nat r''"
    by linarith
  moreover have "karatsuba_sqrt_step a32 a1 a0 b = (s'', r'')"
    unfolding karatsuba_sqrt_step_def sqrt_rem'_def n_def s''_def r''_def r'_def s'_def
              r_def s_def u_def q_def Let_def case_prod_unfold 
    by (simp add: divmod_def)
  ultimately show ?thesis using \<open>r'' \<ge> 0\<close> \<open>s'' \<ge> 0\<close>
    by (simp add: n_def sqrt_rem'_def)
qed

lemma karatsuba_sqrt_step'_correct:
  fixes k n :: nat
  assumes k: "k > 0" and bitlen: "int k \<le> (bitlen n + 1) div 4"
  defines "a32 \<equiv> drop_bit (2*k) n"
  defines "a1 \<equiv> splice_bit k k n"
  defines "a0 \<equiv> take_bit k n"
  shows   "karatsuba_sqrt_step' n k = map_prod int int (sqrt_rem' n)"
proof -
  define n' where "n' = drop_bit (2*k) n"
  have less: "a0 < 2 ^ k" "a1 < 2 ^ k"
    by (auto simp: a0_def a1_def splice_bit_def)
  have mod_less: "x mod y < 2 ^ k" if "y \<le> 2 ^ k" "y > 0" for x y :: int
  proof -
    have "x mod y < y"
      using that by (intro pos_mod_bound) auto
    also have "\<dots> \<le> 2 ^ k"
      using that by simp
    finally show ?thesis .
  qed

  have n_eq: "n = a32 * 2 ^ (2 * k) + a1 * 2 ^ k + a0"
  proof -
    have "n = push_bit (2*k) (drop_bit (2*k) n) + take_bit (2*k) n"
      by (simp add: bits_ident)
    also have "take_bit (2*k) n = take_bit (2*k) (push_bit k (drop_bit k n) + take_bit k n)"
      by (simp add: bits_ident)
    also have "\<dots> = push_bit k (splice_bit k k n) + take_bit k n"
      by (subst bit_eq_iff)
         (auto simp: bit_take_bit_iff bit_push_bit_iff bit_disjunctive_add_iff splice_bit_def)
    also have "push_bit (2 * k) (drop_bit (2 * k) n) + (push_bit k (splice_bit k k n) + take_bit k n) = 
                 drop_bit (2 * k) n * 2 ^ (2 * k) + splice_bit k k n * 2 ^ k + take_bit k n"
      by (simp add: push_bit_eq_mult)
    finally show ?thesis by (simp add: a32_def a1_def a0_def)
  qed

  have "a32 > 0"
  proof (rule Nat.gr0I)
    assume "a32 = 0"
    hence "bitlen (int n) \<le> 2 * int k"
      by (simp add: a32_def drop_bit_eq_0_iff_nat)
    with bitlen and \<open>k > 0\<close> show False
      by linarith
  qed

  have *: "(2 ^ k) ^ 2 \<le> 4 * a32"
  proof -
    have "int ((2 ^ k) ^ 2) = (2 ^ (2 * k) :: int)"
      by (simp add: power_mult add: mult_ac)
    also have "\<dots> \<le> int (4 * a32) \<longleftrightarrow> bitlen (int a32 * 2 ^ 2) \<ge> 2 * k + 1"
      by (subst bitlen_ge_iff_power) (auto simp: nat_add_distrib nat_mult_distrib)
    also have "bitlen (int a32 * 2 ^ 2) = bitlen a32 + 2"
      using \<open>a32 > 0\<close> by (subst bitlen_pow2) auto
    also have "bitlen (int n) \<ge> 2 * int k"
      using assms(1,2) by linarith
    hence "bitlen (int a32) = bitlen (int n) - 2 * int k"
      by (simp add: a32_def of_nat_drop_bit bitlen_drop_bit)
    also have "(int (2 * k + 1) \<le> bitlen (int n) - 2 * int k + 2) \<longleftrightarrow> True"
      using assms(2) by simp
    finally show ?thesis
      unfolding of_nat_le_iff by simp
  qed

  have "n = a32 * 2 ^ (2 * k) + a1 * 2 ^ k + a0"
    by (simp add: n_eq)
  also have "map_prod int int (sqrt_rem' \<dots>) = karatsuba_sqrt_step a32 a1 a0 (2^k)"
    by (subst karatsuba_sqrt_step_correct)
       (use * less \<open>k > 0\<close> in \<open>auto simp: mult_ac simp flip: power_mult\<close>)
  also have "karatsuba_sqrt_step a32 a1 a0 (2^k) = 
           (let (s, r) = map_prod int int (sqrt_rem' a32);
                (q, u) = ((r * 2^k + a1) div (2 * s), (r * 2^k + a1) mod (2 * s));
                s' = s * 2^k + q;
                r' = u * 2^k + a0 - q ^ 2
            in  if r' \<ge> 0 then (s', r') else (s' - 1, r' + 2 * s' - 1))"
    unfolding karatsuba_sqrt_step_def
    by (simp add: case_prod_unfold Let_def divmod_def zdiv_int zmod_int)
  also have "\<dots> = karatsuba_sqrt_step' n k"
    unfolding karatsuba_sqrt_step'_def karatsuba_sqrt_step_def
    by (intro Let_cong case_prod_cong arg_cong2[of _ _ _ _ "divmod"]
              arg_cong[of _ _ "map_prod int int"]
              arg_cong[of _ _ sqrt_rem'] arg_cong[of _ _ int]
              arg_cong2[of _ _ _ _ "(-) :: int \<Rightarrow> _"] refl if_cong
              arg_cong2[of _ _ _ _ Pair] arg_cong2[of _ _ _ _ "(+)"])
        (auto simp: map_prod_def sqrt_rem'_def divmod_def a32_def a1_def a0_def of_nat_splice_bit
                    of_nat_drop_bit of_nat_take_bit divmod_int_def mult_ac push_bit_eq_mult)
  finally show ?thesis ..
qed


subsubsection \<open>Full algorithm\<close>

text \<open>
  Our algorithm is parameterised with a ``limb size'' and a cutoff.
  The cutoff value describes the threshold for the base case, i.e.\ the size of inputs (in bits)
  for which we fall back to Heron's method.

  The algorithm splits the input number into four parts in such a way that the bit size of the lower
  three parts is a multiple of $2^l$ (where $l$ is the limb size). This may be useful to avoid 
  unnecessary bit shifting, since one one always splits the input number exactly at limb
  boundaries. However, whether this actually helps depends on how bit shifting of
  arbitrary-precision integers is actually implemented in the runtime.

  There is only one rather weak condition on the limb size and cutoff. Which values work best
  must be determined experimentally.
\<close>

locale karatsuba_sqrt =
  fixes cutoff limb_size :: nat
  assumes cutoff: "2 ^ (2 + limb_size) \<le> cutoff + 2"
begin

function karatsuba_sqrt_aux :: "nat \<Rightarrow> int \<times> int" where
  "karatsuba_sqrt_aux n = (
    let sz = bitlen n
    in  if sz \<le> int cutoff then
          case sqrt_rem'_heron n of (s, r) \<Rightarrow> (int s, int r)
        else let 
          k = push_bit limb_size (drop_bit (2 + limb_size) (nat (bitlen n + 1)));
          (s, r) = karatsuba_sqrt_aux (drop_bit (2*k) n);
          (q, u) = divmod_int (push_bit k r + splice_bit k k n) (push_bit 1 s);
          s' = push_bit k s + q;
          r' = push_bit k u + take_bit k n - q ^ 2
      in  if r' \<ge> 0 then (s', r') else (s' - 1, r' + push_bit 1 s' - 1))"          
  by auto
termination proof (relation "measure id", goal_cases)
  case (2 n x k)
  have "2 ^ (2 + limb_size) \<le> cutoff + 2"
    using cutoff by simp
  also have "cutoff + 2 < nat (bitlen (int n) + 2)"
    using 2 by simp
  finally have "2 ^ (2 + limb_size) \<le> nat (bitlen (int n) + 1)"
    by linarith
  hence "k > 0"
    by (auto simp: push_bit_eq_mult drop_bit_eq_div 2(3) nat_add_distrib div_greater_zero_iff)
  hence "2 ^ 0 < (2 ^ (2 * k) :: nat)"
    using 2 by (intro power_strict_increasing Nat.gr0I)
               (auto simp: div_eq_0_iff nat_add_distrib not_le)
  moreover have "n > 0"
    using 2 by (auto intro!: Nat.gr0I)
  ultimately have "drop_bit (2 * k) n < n"
    by (auto simp: drop_bit_eq_div intro!: div_less_dividend)
  thus ?case
    by simp
qed auto

lemmas [simp del] = karatsuba_sqrt_aux.simps

lemma karatsuba_sqrt_aux_correct: "karatsuba_sqrt_aux n = map_prod int int (sqrt_rem' n)"
proof (induction n rule: karatsuba_sqrt_aux.induct)
  case (1 n)
  define sz where "sz = bitlen n"
  show ?case
  proof (cases "sz \<le> cutoff")
    case True
    thus ?thesis
       by (subst karatsuba_sqrt_aux.simps)
          (auto simp: sqrt_rem'_heron_correct sqrt_rem'_def sz_def)
  next
    case False
    define k where "k = push_bit limb_size (drop_bit (2 + limb_size) (nat (bitlen n + 1)))"
    have n_eq: "n = drop_bit (2 * k) n * (2 ^ k)\<^sup>2 + splice_bit k k n * 2 ^ k + take_bit k n"
    proof -
      have "n = push_bit (2*k) (drop_bit (2*k) n) + take_bit (2*k) n"
        by (simp add: bits_ident)
      also have "take_bit (2*k) n = take_bit (2*k) (push_bit k (drop_bit k n) + take_bit k n)"
        by (simp add: bits_ident)
      also have "\<dots> = push_bit k (splice_bit k k n) + take_bit k n"
        by (subst bit_eq_iff)
           (auto simp: bit_take_bit_iff bit_push_bit_iff bit_disjunctive_add_iff splice_bit_def)
      also have "push_bit (2 * k) (drop_bit (2 * k) n) + (push_bit k (splice_bit k k n) + take_bit k n) = 
                   drop_bit (2 * k) n * (2 ^ k)\<^sup>2 + splice_bit k k n * 2 ^ k + take_bit k n"
        by (simp add: push_bit_eq_mult flip: power_mult)
      finally show ?thesis .
    qed
      
    have "karatsuba_sqrt_aux n = karatsuba_sqrt_step' n k"
      using False "1.IH"[of sz k]
      by (subst karatsuba_sqrt_aux.simps)
         (simp_all add: karatsuba_sqrt_step'_def of_nat_splice_bit
                        of_nat_take_bit of_nat_drop_bit sz_def k_def Let_def)
    also have "\<dots> = map_prod int int (sqrt_rem' n)"
    proof (subst karatsuba_sqrt_step'_correct)
      have "k \<le> nat (bitlen (int n) + 1) div 4"
        by (simp add: k_def nat_add_distrib div_mult2_eq push_bit_eq_mult drop_bit_eq_div)
      moreover have "bitlen (int n) + 1 \<ge> 0"
        by (auto simp: bitlen_def)
      ultimately show "int k \<le> (bitlen (int n) + 1) div 4"
        by linarith
    next
      show "k > 0"
      proof (rule Nat.gr0I)
        assume "k = 0"
        hence "nat sz + 1 < 2 ^ nat (int limb_size + 2)"
          by (auto simp: k_def div_eq_0_iff sz_def drop_bit_eq_div nat_add_distrib bitlen_def)
        hence "sz + 1 < int (2 ^ nat (int limb_size + 2))"
          by linarith          
        also have "\<dots> = int (2 ^ (2 + limb_size))"
          by (simp add: nat_add_distrib)
        also have "\<dots> \<le> int (cutoff + 2)"
          using cutoff by linarith
        finally show False
          using False by simp
      qed
    qed (use n_eq in auto)
    finally show ?thesis .
  qed
qed

definition karatsuba_sqrt where
  "karatsuba_sqrt n = (case karatsuba_sqrt_aux n of (s, r) \<Rightarrow> (nat s, nat r))"

theorem karatsuba_sqrt_correct: "karatsuba_sqrt n = sqrt_rem' n"
  by (simp add: karatsuba_sqrt_def karatsuba_sqrt_aux_correct case_prod_unfold)

end



subsubsection \<open>Concrete instantiation\<close>

text \<open>
  We pick a cutoff of 1024 and a limb size of 64 as reasonable default values.
\<close>

definition karatsuba_sqrt_default where
  "karatsuba_sqrt_default = karatsuba_sqrt.karatsuba_sqrt 1024 6"

definition karatsuba_sqrt_default_aux where
  "karatsuba_sqrt_default_aux = karatsuba_sqrt.karatsuba_sqrt_aux 1024 6"

interpretation karatsuba_sqrt_default:
  karatsuba_sqrt 1024 6
  rewrites "karatsuba_sqrt.karatsuba_sqrt 1024 6 \<equiv> karatsuba_sqrt_default"
       and "karatsuba_sqrt.karatsuba_sqrt_aux 1024 6 \<equiv> karatsuba_sqrt_default_aux"
  by unfold_locales (auto simp: nat_add_distrib karatsuba_sqrt_default_aux_def karatsuba_sqrt_default_def)

lemmas [code] = 
  karatsuba_sqrt_default.karatsuba_sqrt_aux.simps[unfolded power2_eq_square]
  karatsuba_sqrt_default.karatsuba_sqrt_def
  karatsuba_sqrt_default.karatsuba_sqrt_correct [symmetric]




subsection \<open>Using \<^const>\<open>sqrt_rem\<close> to compute floors and ceilings of \<^const>\<open>sqrt\<close>\<close>

definition sqrt_nat_ceiling :: "nat \<Rightarrow> nat" where
  "sqrt_nat_ceiling n = nat (ceiling (sqrt (real n)))"

definition sqrt_int_floor :: "int \<Rightarrow> int" where
  "sqrt_int_floor n = floor (sqrt (real_of_int n))"

definition sqrt_int_ceiling :: "int \<Rightarrow> int" where
  "sqrt_int_ceiling n = ceiling (sqrt (real_of_int n))"

lemma sqrt_nat_ceiling_code [code]:
  "sqrt_nat_ceiling n = (case sqrt_rem' n of (s, r) \<Rightarrow> if r = 0 then s else s + 1)"
proof -
  have n: "(floor_sqrt n)\<^sup>2 + sqrt_rem n = n"
    by (auto simp: sqrt_rem_def)
  have "sqrt n = sqrt (floor_sqrt n ^ 2 + sqrt_rem n)"
    by (simp add: sqrt_rem_def)
  also have "ceiling \<dots> = floor_sqrt n + (if sqrt_rem n = 0 then 0 else 1)"
  proof (cases "sqrt_rem n = 0")
    case False
    have "n < (floor_sqrt n + 1)\<^sup>2"
      using Suc_floor_sqrt_power2_gt le_eq_less_or_eq by auto
    hence "real n < real ((floor_sqrt n + 1)\<^sup>2)"
      by linarith
    hence "sqrt (floor_sqrt n ^ 2 + sqrt_rem n) \<le> floor_sqrt n + 1"
      by (subst n) (auto intro!: real_le_lsqrt simp flip: of_nat_add)
    moreover have "floor_sqrt n < sqrt (floor_sqrt n ^ 2 + sqrt_rem n)"
      by (rule real_less_rsqrt) (use False in auto)
    ultimately have "ceiling (sqrt (floor_sqrt n ^ 2 + sqrt_rem n)) = floor_sqrt n + 1"
      by linarith
    thus ?thesis
      using False by simp
  qed auto
  finally show ?thesis
    by (simp add: sqrt_nat_ceiling_def sqrt_rem'_def nat_add_distrib)
qed  

lemma sqrt_int_floor_code [code]:
  "sqrt_int_floor n =
     (if n \<ge> 0 then int (floor_sqrt (nat n)) else -int (sqrt_nat_ceiling (nat (-n))))"
  by (auto simp: sqrt_int_floor_def sqrt_nat_ceiling_def floor_sqrt_conv_floor_of_sqrt
                 real_sqrt_minus ceiling_minus)

lemma sqrt_int_ceiling_code [code]:
  "sqrt_int_ceiling n =
     (if n \<ge> 0 then int (sqrt_nat_ceiling (nat n)) else -int (floor_sqrt (nat (-n))))"
  using sqrt_int_floor_code[of "-n"]
  by (cases n "0 :: int" rule: linorder_cases)
     (auto simp: sqrt_int_ceiling_def sqrt_int_floor_def sqrt_nat_ceiling_def[of 0]
                 real_sqrt_minus floor_minus)

end
