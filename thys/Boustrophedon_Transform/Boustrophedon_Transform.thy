section \<open>The Boustrophedon transform\<close>
theory Boustrophedon_Transform
  imports "HOL-Computational_Algebra.Computational_Algebra" Alternating_Permutations
begin

text \<open>
  The Boustrophedon transform maps one sequence of numbers to another sequence of numbers --
  or, equivalently, one exponential generating function to another exponential generating function.
  It was first described in its full generality by Millar et al.~\<^cite>\<open>millar\<close>.

  Its name derives from the Ancient Greek \greekbous\ (``ox''), \greekstrofe\ (``turn''), and
  \greekdon\ (``in the manner of'') because the number triangle from which it is obtained can
  be visualised as being traversed left-to-right, then right-to-left, etc.\ the same way an ox
  plows a field.
\<close>


subsection \<open>The Seidel triangle\<close>

(* TODO: this should probably be done in HOL-Library as well because the current
   syntax for "Sum_any" clashes with "suminf" and the type system cannot
   disambiguate it. *)
(*<*)
no_syntax
  "_Sum_any" :: "pttrn \<Rightarrow> 'a \<Rightarrow> 'a::comm_monoid_add"    ("(3\<Sum>_. _)" [0, 10] 10)
syntax
  "_Sum_any" :: "pttrn \<Rightarrow> 'a \<Rightarrow> 'a::comm_monoid_add"    ("(3\<Sum>\<^sub>?_. _)" [0, 10] 10)
(*>*)


text \<open>
  We define the triangle via its simplest recurrence. Let $T_{n,k}$ denote the $k$-th entry
  of the $n$-th row. The first entry of the $n$-th row is always $a(n)$, where $a$ is the input
  sequence. The $k+1$-th entry of a row is the sum of the previous entry in the same row and
  the $k$-th last entry of the previous row.

  That is: $T_{n, 0} = a(n)$ and $T_{n+1,k+1} = T_{n+1,k} + T_{n, n-k}$.

  In other words: one produces a new row of the triangle by starting with $a(n)$ and then
  adding the entries of the previous row, in right-to-left order, adding each intermediate
  sum to the new row.
\<close>
fun seidel_triangle :: "(nat \<Rightarrow> 'a :: monoid_add) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  "seidel_triangle a n 0 = a n"
| "seidel_triangle a 0 (Suc k) = 0"
| "seidel_triangle a (Suc n) (Suc k) =
     (if k > n then 0 else seidel_triangle a (Suc n) k + seidel_triangle a n (n - k))"

lemmas seidel_triangle_rec [simp del] = seidel_triangle.simps(3)

lemma seidel_triangle_greater_eq_0 [simp]: "k > n \<Longrightarrow> seidel_triangle a n k = 0"
  by (cases n; cases k) (auto simp: seidel_triangle_rec)

text \<open>
  There is also the following recurrence where the right-hand side contains only the entries
  of the previous row. Namely: The entry $T_{n,k}$ is equal to the sum of $a_n$ and the last 
  $k$ entries of the previous row.
\<close>
lemma seidel_triangle_conv_rowsum: 
  assumes "k \<le> n"
  shows   "seidel_triangle a n k = a n + (\<Sum>j<k. seidel_triangle a (n - 1) (n - Suc j))"
  using assms
proof (induction k)
  case (Suc k)
  then obtain n' where [simp]: "n = Suc n'"
    by (cases n) auto
  show ?case
    using Suc.IH Suc.prems by (simp add: seidel_triangle_rec add_ac)
qed auto


text \<open>
  The following function is the function $\pi(n,k,i)$ from the paper by Millar et al.
  They define it via the number of paths from one node to another node in a triangular directed
  graph.

  However, they also give a closed-form expression for $\pi(n,k,i)$ as a sum of binomial 
  coefficients and Entringer numbers, and we directly use this since it seemed easier to formalise.
\<close>
definition seidel_triangle_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "seidel_triangle_aux n k i =
     (\<Sum>s\<le>min k (n-i). (k choose s) * ((n-k) choose (n-i-s)) * entringer_number (n-i) s)"

lemma seidel_triangle_aux_same:
  assumes i: "i \<le> n"
  shows   "seidel_triangle_aux n n i = (n choose i) * zigzag_number (n - i)"
proof -
  have "seidel_triangle_aux n n i =
          (\<Sum>s\<le>n - i. (n choose s) * (0 choose (n - (i + s))) * entringer_number (n - i) s)"
    by (simp add: seidel_triangle_aux_def)
  also have "\<dots> = (\<Sum>s\<in>{n-i}. (n choose s) * (0 choose (n - (i + s))) * entringer_number (n - i) s)"
    by (rule sum.mono_neutral_right) auto
  also have "\<dots> = (n choose i) * zigzag_number (n - i)"
    using i by (simp flip: binomial_symmetric)
  finally show ?thesis .
qed

lemma seidel_triangle_aux_same2 [simp]: "seidel_triangle_aux n k n = 1"
  by (simp add: seidel_triangle_aux_def)

lemma seidel_triangle_aux_0_middle [simp]:
  "i < n \<Longrightarrow> seidel_triangle_aux n 0 i = 0"
  by (simp add: seidel_triangle_aux_def flip: binomial_symmetric)

lemma seidel_triangle_aux_0_right [simp]:
  assumes "k \<le> n"
  shows   "seidel_triangle_aux n k 0 = entringer_number n k"
proof -
  have "seidel_triangle_aux n k 0 = (\<Sum>s\<le>k. (k choose s) * (n - k choose (n - s)) * entringer_number n s)"
    using assms by (simp add: seidel_triangle_aux_def)
  also have "\<dots> = (\<Sum>s\<in>{k}. (k choose s) * (n - k choose (n - s)) * entringer_number n s)"
    by (rule sum.mono_neutral_right) (use assms in auto)
  finally show ?thesis
    by simp
qed

text \<open>
  The following lemma is where most of the proof work is done. Millar et al.\ do not mention it
  expicitly, but $\pi$ satistifies the recurrence
  $\pi(n+1, k+1, i) = \pi(n+1, k, i) + \pi(n, n-k, i)$.

  Note that this is the same type of recurrence that we have in the Seidel triangle and 
  the Entringer numbers.
\<close>
lemma seidel_triangle_aux_rec:
  defines "S \<equiv> seidel_triangle_aux"
  assumes k: "k \<le> n" and i: "i \<le> n"
  shows   "S (Suc n) (Suc k) i = S (Suc n) k i + S n (n - k) i"
proof -
  define N where "N = int n"
  define K where "K = int k"
  define I where "I = int i"

  define B where "B = (\<lambda>n k. if n < 0 \<or> k < 0 then 0 else ((nat n) choose (nat k)))"
  have [simp]: "B n k = 0" if "k < 0 \<or> k > n \<or> n < 0" for n k
    using that by (auto simp: B_def)
  have B_rec: "B (N+1) (K+1) = B N (K+1) + B N K" if "N \<ge> 0" for N K
    using that by (auto simp: B_def nat_add_distrib not_less)
  have B_eq: "B n' k' = (n choose k)" if "int n = n'" "int k = k'" for n n' k k'
    unfolding B_def using that by auto
  have B_mult_cong: "B x y * z = B x y * z'" if "x \<ge> 0 \<and> y \<ge> 0 \<and> y \<le> x \<longrightarrow> z = z'" for x y z z'
    using that by (auto simp: B_def)

  define E where "E = (\<lambda>n k. if n < 0 \<or> k < 0 then 0 else entringer_number (nat n) (nat k))"
  have [simp]: "E n k = 0" if "k < 0 \<or> k > n \<or> n < 0" for n k
    using that by (auto simp: E_def)
  have E_rec: "E (n+1) (k+1) = E (n+1) k + E n (n-k)" if "n \<ge> 0" "k \<le> n" for n k
    using that by (auto simp: E_def nat_add_distrib entringer_number_rec nat_diff_distrib)
  have E_eq: "E n' k' = entringer_number n k" if "int n = n'" "int k = k'" for n n' k k'
    unfolding E_def using that by auto

  have S_eq: "S n k i = (\<Sum>\<^sub>?s. B k' s * B (n'-k') (n'-i'-s) * E (n'-i') s)"
    if "k \<le> n" "i \<le> n" "k' = int k" "n' = int n" "i' = int i" for k n i :: nat and k' n' i' :: int
  proof -
    have "S n k i = (\<Sum>s\<le>min k (n - i). B k' s * B (n'-k') (n'-i'-s) * E (n'-i') s)"
      unfolding S_def seidel_triangle_aux_def using that
      by (intro sum.cong arg_cong2[of _ _ _ _ "(*)"] B_eq[symmetric] E_eq[symmetric]) auto
    also have "\<dots> = (\<Sum>s\<in>{0..min k' (n' - i')}. B k' s * B (n'-k') (n'-i'-s) * E (n'-i') s)"
      by (rule sum.reindex_bij_witness[of _ nat int]) (use that in auto)
    also have "\<dots> = (\<Sum>\<^sub>?s. B k' s * B (n'-k') (n'-i'-s) * E (n'-i') s)"
      by (rule Sum_any.expand_superset_cong [symmetric]) auto
    finally show ?thesis .
  qed

  have "S (Suc n) (Suc k) i = 
          (\<Sum>\<^sub>?s. B (K+1) s * B ((N+1)-(K+1)) (N+1-I-s) * E (N+1-I) s)"
    by (rule S_eq) (use assms in \<open>auto simp: N_def K_def I_def\<close>)
  also have "\<dots> = (\<Sum>\<^sub>?s. B (K+1) (s+1) * (B (N-K) (N-I-s) * E (N-I+1) (s+1)))"
    by (rule Sum_any.reindex_bij_witness[of "\<lambda>s. s+1" "\<lambda>s. s-1"]) (auto simp: algebra_simps)
  also have "\<dots> = (\<Sum>\<^sub>?s. B (K+1) (s+1) * (B (N-K) (N-I-s) * (E (N-I+1) s + E (N-I) (N-I-s))))"
    by (intro Sum_any.cong B_mult_cong impI, subst E_rec)
       (use assms in \<open>auto simp: N_def I_def\<close>)
  also have "\<dots> = (\<Sum>\<^sub>?s. B (K+1) (s+1) * B (N-K) (N-I-s) * E (N-I+1) s) +
                  (\<Sum>\<^sub>?s. B (K+1) (s+1) * B (N-K) (N-I-s) * E (N-I) (N-I-s))"
    unfolding ring_distribs mult.assoc [symmetric]
    by (rule Sum_any.distrib'[where A = "{0..N-I}"]) auto
  also have "(\<Sum>\<^sub>?s. B (K+1) (s+1) * B (N-K) (N-I-s) * E (N-I) (N-I-s)) =
             (\<Sum>\<^sub>?s. B (K+1) (N-I-s+1) * B (N-K) s * E (N-I) s)"
    by (rule Sum_any.reindex_bij_witness[of "\<lambda>s. N-I-s" "\<lambda>s. N-I-s"]) auto

  also have "K \<ge> 0"
    by (simp add: K_def)
  have "(\<Sum>\<^sub>?s. B (K+1) (s+1) * B (N-K) (N-I-s) * E (N-I+1) s) = 
           (\<Sum>\<^sub>?s. B K (s+1) * B (N-K) (N-I-s) * E (N-I+1) s) +
           (\<Sum>\<^sub>?s. B K s * B (N-K) (N-I-s) * E (N-I+1) s)"
    unfolding B_rec[OF \<open>K \<ge> 0\<close>] ring_distribs
    by (rule Sum_any.distrib'[where A = "{0..K}"]) auto

  also have "(\<Sum>\<^sub>?s. B (K+1) (N-I-s+1) * B (N-K) s * E (N-I) s) = 
               (\<Sum>\<^sub>?s. B K (N-I-s+1) * B (N-K) s * E (N-I) s) +
               (\<Sum>\<^sub>?s. B K (N-I-s) * B (N-K) s * E (N-I) s)"
    unfolding B_rec[OF \<open>K \<ge> 0\<close>] ring_distribs
    by (rule Sum_any.distrib'[where A = "{0..N-I+1}"]) auto
  finally have eq: "S (Suc n) (Suc k) i = 
                  (\<Sum>\<^sub>?s. B K (s+1) * B (N-K) (N-I-s) * E (N-I+1) s) +
                  (\<Sum>\<^sub>?s. B K s * B (N-K) (N-I-s) * E (N-I+1) s) +
                  (\<Sum>\<^sub>?s. B K (N-I-s+1) * B (N-K) s * E (N-I) s) +
                  (\<Sum>\<^sub>?s. B (N-K) s * B K (N-I-s) * E (N-I) s)"
    (is "_ = ?S1 + ?S2 + ?S3 + ?S4")
    by (simp only: add_ac mult.commute)

  have "S (Suc n) k i + S n (n - k) i =
          (\<Sum>\<^sub>?s. B K s * B (N+1-K) (N+1-I-s) * E (N+1-I) s) +
          (\<Sum>\<^sub>?s. B (N - K) s * B (N-(N - K)) (N-I-s) * E (N-I) s)"
    using assms by (intro arg_cong2[of _ _ _ _ "(+)"] S_eq) (auto simp: N_def K_def I_def)
  also have "\<dots> = (\<Sum>\<^sub>?s. B K s * B (N-K+1) (N-I-s+1) * E (N-I+1) s) +
                  (\<Sum>\<^sub>?s. B (N - K) s * B K (N-I-s) * E (N-I) s)"
    by (simp add: algebra_simps)
  also have "N - K \<ge> 0"
    using assms by (simp add: N_def K_def)
  have "(\<Sum>\<^sub>?s. B K s * B (N-K+1) (N-I-s+1) * E (N-I+1) s) =
               (\<Sum>\<^sub>?s. B K s * B (N-K) (N-I-s+1) * E (N-I+1) s) + ?S2"
    unfolding B_rec[OF \<open>N - K \<ge> 0\<close>] ring_distribs
    by (rule Sum_any.distrib'[where A = "{0..K}"]) auto

  also have "(\<Sum>\<^sub>?s. B K s * B (N-K) (N-I-s+1) * E (N-I+1) s) = ?S1 + ?S3"
  proof -
    have "N - I \<ge> 0"
      using assms by (auto simp: N_def I_def)
    have "(\<Sum>\<^sub>?s. B K s * B (N-K) (N-I-s+1) * E (N-I+1) s) =
          (\<Sum>\<^sub>?s. B K (s+1) * (B (N-K) (N-I-s) * E (N-I+1) (s+1)))"
      by (rule Sum_any.reindex_bij_witness[of "\<lambda>s. s+1" "\<lambda>s. s-1"]) (auto simp: algebra_simps)
    also have "\<dots> = (\<Sum>\<^sub>?s. B K (s+1) * (B (N-K) (N-I-s) * (E (N-I+1) s + E (N-I) (N-I-s))))"
      by (intro Sum_any.cong B_mult_cong impI, subst E_rec) (use \<open>N - I \<ge> 0\<close> in auto)
    also have "\<dots> = ?S1 + (\<Sum>\<^sub>?s. B K (s+1) * B (N-K) (N-I-s) * E (N-I) (N-I-s))"
      unfolding ring_distribs mult.assoc [symmetric]
      by (rule Sum_any.distrib'[where A = "{0..K}"]) auto
    also have "(\<Sum>\<^sub>?s. B K (s+1) * B (N-K) (N-I-s) * E (N-I) (N-I-s)) =
               (\<Sum>\<^sub>?s. B K (N-I-s+1) * B (N-K) s * E (N-I) s)"
      by (rule Sum_any.reindex_bij_witness[of "\<lambda>s. N-I-s" "\<lambda>s. N-I-s"]) (auto simp: algebra_simps)
    finally show ?thesis .
  qed

  finally show ?thesis
    using eq by algebra
qed

text \<open>
  With this, we can prove the following closed form for the entry $T_{n,k}$ in the
  Seidel triangle.
\<close>
theorem seidel_triangle_eq:
  assumes "k \<le> n"
  shows   "seidel_triangle a n k = (\<Sum>i\<le>n. of_nat (seidel_triangle_aux n k i) * a i)"
  using assms
proof (induction a n k rule: seidel_triangle.induct)
  case (1 a n)
  have "(\<Sum>i\<le>n. of_nat (seidel_triangle_aux n 0 i) * a i) =
        (\<Sum>i\<in>{n}. of_nat (seidel_triangle_aux n 0 i) * a i)"
    by (rule sum.mono_neutral_right) (auto simp: seidel_triangle_aux_def)
  thus ?case
    by (simp add: seidel_triangle_aux_def)
next
  case (3 a n k)
  define S where "S = (\<lambda>n k i. of_nat (seidel_triangle_aux n k i) :: 'a)"
  from "3.prems" have "k \<le> n"
    by simp
  have "seidel_triangle a (Suc n) (Suc k) =
          seidel_triangle a (Suc n) k + seidel_triangle a n (n - k)"
    using \<open>k \<le> n\<close> by (simp add: seidel_triangle_rec)
  also have "seidel_triangle a (Suc n) k = (\<Sum>i\<le>n. S (Suc n) k i * a i) + a (Suc n)"
    unfolding S_def by (subst "3.IH") (use \<open>k \<le> n\<close> in auto)
  also have "seidel_triangle a n (n - k) = (\<Sum>i\<le>n. S n (n - k) i * a i)"
    unfolding S_def by (subst "3.IH") (use \<open>k \<le> n\<close> in auto)
  also have "(\<Sum>i\<le>n. S (Suc n) k i * a i) + a (Suc n) + (\<Sum>i\<le>n. S n (n - k) i * a i) =
             (\<Sum>i\<le>n. (S (Suc n) k i + S n (n - k) i) * a i) + a (Suc n)"
    by (simp add: sum.distrib add_ac ring_distribs)
  also have "(\<Sum>i\<le>n. (S (Suc n) k i + S n (n - k) i) * a i) = (\<Sum>i\<le>n. S (Suc n) (Suc k) i * a i)"
    by (rule sum.cong) (use \<open>k \<le> n\<close> in \<open>simp_all add: S_def seidel_triangle_aux_rec\<close>)
  also have "\<dots> + a (Suc n) = (\<Sum>i\<le>Suc n. S (Suc n) (Suc k) i * a i)"
    by (simp add: S_def)
  finally show ?case 
    by (simp add: S_def)
qed auto



subsection \<open>The Boustrophedon transform of a sequence\<close>

text \<open>
  The Boustrophedon transform of a sequence $a_n$ is defined by taking the last entry
  of each row of the Seidel triangle of $a_n$.
\<close>

definition boustrophedon :: "(nat \<Rightarrow> 'a :: monoid_add) \<Rightarrow> nat \<Rightarrow> 'a" where
  "boustrophedon a n = seidel_triangle a n n"

definition inv_boustrophedon :: "(nat \<Rightarrow> 'a :: comm_ring_1) \<Rightarrow> nat \<Rightarrow> 'a" where
  "inv_boustrophedon a n = (-1)^n * boustrophedon (\<lambda>k. (-1)^k * a k) n"

text \<open>
  The Boustrophedon transform has the following nice closed form, which of course follows
  directly from our above closed form for the Seidel triangle:
\<close>
theorem boustrophedon_eq:
  fixes a :: "nat \<Rightarrow> 'a :: comm_semiring_1"
  shows "boustrophedon a n = (\<Sum>k\<le>n. of_nat (n choose k) * a k * of_nat (zigzag_number (n - k)))"
  by (simp add: boustrophedon_def seidel_triangle_eq seidel_triangle_aux_same mult_ac)

text \<open>
  The inverse Boustrophedon transform is the same as the normal Boustrophedon transform except
  that we must negate every other number in the input and output sequences.
\<close>
theorem inv_boustrophedon_eq:
  fixes a :: "nat \<Rightarrow> 'a :: comm_ring_1"
  shows "inv_boustrophedon a n = (\<Sum>k\<le>n. (-1) ^ (n - k) * of_nat (n choose k) * a k * of_nat (zigzag_number (n - k)))"
  unfolding inv_boustrophedon_def boustrophedon_eq sum_distrib_left
  by (intro sum.cong) (auto simp: uminus_power_if)

text \<open>
  In particular, the Entringer numbers are the Seidel triangle of the sequence
  $1, 0, 0, 0, \ldots$.
\<close>
corollary entringer_number_conv_seidel_triangle:
  "seidel_triangle (\<lambda>n. if n = 0 then 1 else 0 :: 'a :: comm_semiring_1) n k =
     of_nat (entringer_number n k)"
proof (cases "k \<le> n")
  case True
  have "k \<le> n"
    using True by auto
  have "seidel_triangle (\<lambda>n. if n = 0 then 1 else 0 :: 'a) n k =
          of_nat (\<Sum>i\<le>n. seidel_triangle_aux n k i * (if i = 0 then 1 else 0))"
    unfolding seidel_triangle_eq[OF \<open>k \<le> n\<close>] of_nat_sum
    by (rule sum.cong) (use True in auto)
  also have "(\<Sum>i\<le>n. seidel_triangle_aux n k i * (if i = 0 then 1 else 0)) =
             (\<Sum>i\<in>{0}. seidel_triangle_aux n k i * (if i = 0 then 1 else 0))"
    by (rule sum.mono_neutral_right) auto
  also have "\<dots> = entringer_number n k"
    using True by simp
  finally show ?thesis .
qed auto

text \<open>
  And consequently, the zigzag numbers are the Boustrophedon transform of the sequence
  $1, 0, 0, 0, \ldots$.
\<close>
corollary zigzag_number_conv_boustrophedon:
  "boustrophedon (\<lambda>n. if n = 0 then 1 else 0 :: 'a :: comm_semiring_1) n =
     of_nat (zigzag_number n)"
  unfolding boustrophedon_def
  by (subst entringer_number_conv_seidel_triangle) auto



subsection \<open>The Boustrophedon transform of a function\<close>

text \<open>
  Analogously, one can define the Boustrophedon transform $\mathcal B(f)(x)$ of an exponential 
  generating function $f(x) = \sum_{n\geq 0} f(n)/n! x^n$ and its inverse $\mathcal B^{-1}(f)(x)$:
\<close>
definition Boustrophedon :: "'a :: field_char_0 fps \<Rightarrow> 'a fps" where
  "Boustrophedon A = Abs_fps (\<lambda>n. boustrophedon (\<lambda>n. fps_nth A n * fact n) n / fact n)"

definition inv_Boustrophedon :: "'a :: field_char_0 fps \<Rightarrow> 'a fps" where
  "inv_Boustrophedon A = Abs_fps (\<lambda>n. inv_boustrophedon (\<lambda>n. fps_nth A n * fact n) n / fact n)"

lemma fps_nth_Boustrophedon:
  fixes A :: "'a :: field_char_0 fps"
  shows "fps_nth (Boustrophedon A) n =
           (\<Sum>k\<le>n. fps_nth A k * of_nat (zigzag_number (n - k)) / fact (n - k))"
  by (simp add: Boustrophedon_def boustrophedon_eq field_simps sum_distrib_left sum_distrib_right
                binomial_fact)

lemma fps_nth_inv_Boustrophedon:
  fixes A :: "'a :: field_char_0 fps"
  shows "fps_nth (inv_Boustrophedon A) n =
           (\<Sum>k\<le>n. (-1)^(n-k) * fps_nth A k * of_nat (zigzag_number (n - k)) / fact (n - k))"
  by (simp add: inv_Boustrophedon_def inv_boustrophedon_eq field_simps 
                sum_distrib_left sum_distrib_right binomial_fact)

text \<open>
  We have the closed form $\mathcal B(f) = (\sec + \tan)f$:
\<close>
theorem Boustrophedon_altdef:
  fixes A :: "'a :: field_char_0 fps"
  shows "Boustrophedon A = (fps_sec 1 + fps_tan 1) * A"
  by (subst mult.commute, rule fps_ext, 
      subst exponential_generating_function_zigzag_number [symmetric])
     (simp add: fps_nth_Boustrophedon fps_mult_nth atLeast0AtMost)

text \<open>
  It is also easy to see from the definition of $\mathcal B^{-1}$ that we have
  $\mathcal B^{-1}(f)(x) = \mathcal B(g)(-x)$, where $g(x) = f(-x)$.
\<close>
theorem inv_Boustrophedon_altdef1:
  fixes A :: "'a :: field_char_0 fps"
  shows "inv_Boustrophedon A = fps_compose (Boustrophedon (fps_compose A (-fps_X))) (-fps_X)"
  by (rule fps_ext)
     (simp_all add: inv_Boustrophedon_def Boustrophedon_def fps_nth_compose_uminus
                    inv_boustrophedon_def mult.assoc)

text \<open>
  Or, yet another view on $\mathcal B^{-1}$:
  $\mathcal B^{-1}(f)(x) = (\sec (-x) + \tan (-x)) f(x)$.
\<close>
lemma inv_Boustrophedon_altdef2:
  fixes A :: "'a :: field_char_0 fps"
  shows "inv_Boustrophedon A = (fps_sec 1 - fps_tan 1) * A"
proof -
  have "inv_Boustrophedon A =
          (A * fps_compose (Abs_fps (\<lambda>k. of_nat (zigzag_number k) / fact k)) (-fps_X))"
    unfolding fps_eq_iff fps_nth_inv_Boustrophedon fps_mult_nth
    by (simp add: fps_nth_compose_uminus mult_ac atLeast0AtMost)
  also have "Abs_fps (\<lambda>k. of_nat (zigzag_number k) / fact k) = fps_sec (1::'a) + fps_tan 1"
    by (simp add: exponential_generating_function_zigzag_number)
  also have "fps_compose \<dots> (-fps_X) = fps_sec 1 - fps_tan 1"
    by (simp add: fps_compose_add_distrib fps_sec_even fps_tan_odd)
  finally show ?thesis by (simp add: mult.commute)
qed

lemma fps_sec_plus_tan_times_sec_minus_tan:
  "(fps_sec (c ::'a :: field_char_0) + fps_tan c) * (fps_sec c - fps_tan c) = 1"
proof -
  define S where "S = fps_to_fls (fps_sin c)"
  define C where "C = fps_to_fls (fps_cos c)"
  have "fls_nth C 0 = 1"
    by (simp add: C_def)
  hence [simp]: "C \<noteq> 0"
    by auto

  have "fps_to_fls ((fps_sec c + fps_tan c) * (fps_sec c - fps_tan c)) =
          (inverse C + S / C) * (inverse C - S / C)"
    by (simp add: fps_sec_def fps_tan_def fls_times_fps_to_fls S_def C_def
             flip: fls_inverse_fps_to_fls fls_divide_fps_to_fls)
  also have "(inverse C - S / C) = (1 - S) / C"
    by (simp add: divide_simps)
  also have "(inverse C + S / C) = (1 + S) / C"
    by (simp add: divide_simps)
  also have "(1 + S) / C * ((1 - S) / C) = (1 - S ^ 2) / C ^ 2"
    by (simp add: algebra_simps power2_eq_square)
  also have "1 - S ^ 2 = C ^ 2"
  proof -
    have "1 - S ^ 2 = fps_to_fls (1 - fps_sin c ^ 2)"
      by (simp add: S_def fps_to_fls_power)
    also have "1 - fps_sin c ^ 2 = fps_cos c ^ 2"
      using fps_sin_cos_sum_of_squares[of c]  by algebra
    also have "fps_to_fls \<dots> = C ^ 2"
      by (simp add: C_def fps_to_fls_power)
    finally show ?thesis .
  qed
  also have "C ^ 2 / C ^ 2 = fps_to_fls 1"
    by simp
  finally show ?thesis
    by (simp only: fps_to_fls_eq_iff)
qed

text \<open>
  Or, equivalently: $\mathcal B^{-1}(f) = f / (\sec + \tan)$.
\<close>
theorem inv_Boustrophedon_altdef3:
  fixes A :: "'a :: field_char_0 fps"
  shows "inv_Boustrophedon A = A / (fps_sec 1 + fps_tan 1)"
proof (rule sym, rule divide_fps_eqI)
  have "inv_Boustrophedon A * (fps_sec 1 + fps_tan 1) =
          ((fps_sec 1 + fps_tan 1) * (fps_sec 1 - fps_tan 1)) * A"
    unfolding inv_Boustrophedon_altdef2 by (simp only: mult_ac)
  thus "inv_Boustrophedon A * (fps_sec 1 + fps_tan 1) = A"
    by (simp only: fps_sec_plus_tan_times_sec_minus_tan mult_1_left)
next
  have "fps_nth (fps_sec 1 + fps_tan (1::'a)) 0 = 1"
    by auto
  hence "fps_sec 1 + fps_tan (1::'a) \<noteq> 0"
    by (intro notI) simp_all
  thus "A \<noteq> 0 \<or> fps_sec 1 + fps_tan (1::'a) \<noteq> 0 \<or> inv_Boustrophedon A = 0"
    by blast
qed

text \<open>
  It is now obvious that $\mathcal B$ and $\mathcal B^{-1}$ really are inverse to one another.
\<close>
lemma Boustrophedon_inv_Boustrophedon [simp]:
  fixes A :: "'a :: field_char_0 fps"
  shows "Boustrophedon (inv_Boustrophedon A) = A"
proof -
  have "Boustrophedon (inv_Boustrophedon A) =
           A * ((fps_sec (1::'a) + fps_tan 1) * (fps_sec 1 - fps_tan 1))"
    by (simp add: Boustrophedon_altdef inv_Boustrophedon_altdef2)
  also have "(fps_sec (1::'a) + fps_tan 1) * (fps_sec 1 - fps_tan 1) = 1"
    by (rule fps_sec_plus_tan_times_sec_minus_tan)
  finally show ?thesis
    by simp
qed

lemma inv_Boustrophedon_Boustrophedon [simp]:
  fixes A :: "'a :: field_char_0 fps"
  shows "inv_Boustrophedon (Boustrophedon A) = A"
proof -
  have "inv_Boustrophedon (Boustrophedon A) =
           A * ((fps_sec (1::'a) + fps_tan 1) * (fps_sec 1 - fps_tan 1))"
    by (simp add: Boustrophedon_altdef inv_Boustrophedon_altdef2)
  also have "(fps_sec (1::'a) + fps_tan 1) * (fps_sec 1 - fps_tan 1) = 1"
    by (rule fps_sec_plus_tan_times_sec_minus_tan)
  finally show ?thesis
    by simp
qed


(*<*)
syntax
  "_Sum_any" :: "pttrn \<Rightarrow> 'a \<Rightarrow> 'a::comm_monoid_add"    ("(3\<Sum>_. _)" [0, 10] 10)
no_syntax
  "_Sum_any" :: "pttrn \<Rightarrow> 'a \<Rightarrow> 'a::comm_monoid_add"    ("(3\<Sum>\<^sub>?_. _)" [0, 10] 10)
(*>*)

end