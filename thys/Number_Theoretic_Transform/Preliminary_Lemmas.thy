(*
Title: Preliminary Lemmas for Number Theoretic Transform
Author: Thomas Ammer
*)

theory Preliminary_Lemmas
 imports Berlekamp_Zassenhaus.Finite_Field 
         "HOL-Number_Theory.Number_Theory"
begin

section \<open>Preliminary Lemmas\<close>

subsection \<open>A little bit of Modular Arithmetic\<close>

text \<open>An obvious lemma. Just for simplification.\<close>

lemma two_powrs_div:
  assumes "j < (i::nat) "
  shows "((2^i) div ((2::nat)^(Suc j)))*2 =  ((2^i) div (2^j))"
proof-
  have "((2::nat)^i) div (2^(Suc j)) = 2^(i -1) div(2^ j)" using assms 
    by (smt (z3) One_nat_def add_le_cancel_left diff_Suc_Suc div_by_Suc_0 div_if less_nat_zero_code plus_1_eq_Suc power_diff_power_eq zero_neq_numeral)
  thus ?thesis 
    by (metis Suc_diff_Suc Suc_leI assms less_imp_le_nat mult.commute power_Suc power_diff_power_eq zero_neq_numeral)
qed

lemma two_powr_div:
  assumes "j < (i::nat) "
  shows "((2^i) div ((2::nat)^j)) =  2^(i-j)" 
  by (simp add: assms less_or_eq_imp_le power_diff)


text \<open>
  The order of an element is the same whether we consider it as an integer or as a natural number.
\<close>
(* TODO: Move *)
lemma ord_int: "ord (int p) (int x) = ord p x"
proof (cases "coprime p x")
  case False
  thus ?thesis
    by (auto simp: ord_def)
next
  case True
  have "(LEAST d. 0 < d \<and> [int x ^ d = 1] (mod int p)) = ord p x"
  proof (intro Least_equality conjI)
    show "[int x ^ ord p x = 1] (mod int p)"
      using True by (metis cong_int_iff of_nat_1 of_nat_power ord_works)
    show "ord p x \<le> y" if "0 < y \<and> [int x ^ y = 1] (mod int p)" for y
      using that by (metis cong_int_iff int_ops(2) linorder_not_less of_nat_power ord_minimal)
  qed (use True in auto)
  thus ?thesis
    by (auto simp: ord_def)
qed

lemma not_residue_primroot_1:
  assumes "n > 2"
  shows   "\<not>residue_primroot n 1"
  using assms totient_gt_1[of n] by (auto simp: residue_primroot_def)

lemma residue_primroot_not_cong_1:
  assumes "residue_primroot n g" "n > 2"
  shows   "[g \<noteq> 1] (mod n)"
  using residue_primroot_cong not_residue_primroot_1 assms by metis  


text \<open>
We want to show the existence of a generating element of $\mathbb{Z}_p$ where $p$ is prime.
\label{primroot1} \<close>

text \<open>Non-trivial order of an element $g$ modulo $p$ in a ring  implies $g\neq1$.
Although this lemma applies to all rings, it's only intended to be used in connection with $nat$s or $int$s
\<close>

lemma prime_not_2_order_not_1:
  assumes "prime p"
          "p > 2 "
          "ord p g > 2"
  shows   "g \<noteq> 1"
proof
  assume "g = 1"
  hence "ord p g = 1" unfolding ord_def
    by (simp add: Least_equality)
  then show False using assms by auto
qed

text \<open>The same for modular arithmetic.\<close>

lemma prime_not_2_order_not_1_mod:
 assumes "prime p "
         "p > 2 "
         "ord p g > 2"
 shows   "[g \<noteq> 1] (mod p)"
proof
  assume "[g = 1] (mod p)"
  hence "ord p g = 1" unfolding ord_def
    by(split if_split, metis assms(1) assms(2) assms(3) ord_cong prime_not_2_order_not_1)
  then show False using assms by auto
qed

text \<open>
Now we formulate our lemma about generating elements in residue classes:
There is an element $g \in \mathbb{Z}_p$ such that for any $x \in \mathbb{Z}_p$ 
there is a natural $i$ such that $g^i \equiv x \; (\mod p)$.\<close>

lemma generator_exists:
  assumes "prime (p::nat)" "p > 2"
  shows "\<exists> g. [g \<noteq> 1] (mod p) \<and> (\<forall> x. (0<x \<and> x < p )\<longrightarrow> (\<exists> i. [g^i = x] (mod p)))"
proof-
  obtain g where g_prim_root:"residue_primroot p g" 
    using assms prime_gt_1_nat prime_primitive_root_exists
    by (metis One_nat_def)
  have g_not_1: "[g \<noteq> 1] (mod p)"
    using residue_primroot_not_cong_1 assms g_prim_root by blast

  have "\<exists>i. [g ^ i = x] (mod p)" if x_bounds: "x > 0" "x < p" for x
  proof -
    have 1:"coprime p x" 
      using assms prime_nat_iff'' x_bounds by blast
    have 2:"ord p g = p-1"
      by (metis assms(1) g_prim_root residue_primroot_def totient_prime)
    hence bij: "bij_betw (\<lambda>i. g ^ i mod p) {..<totient p} (totatives p)"
      using residue_primroot_is_generator[of p g] totatives_def[of p] 
          1 totient_def[of p] assms g_prim_root prime_gt_1_nat by blast
    have 3:"x mod p \<in> totatives p" 
      by (simp add: "1" coprime_commute in_totatives_iff order_le_less x_bounds)
    have " {..<totient p} \<noteq> {}" 
      by (metis assms(1) lessThan_empty_iff prime_nat_iff'' totient_0_iff)
   then obtain i where "g^i mod p = x mod p" 
      using bij_betw_inv[of "(\<lambda>i. g ^ i mod p)" "{..<totient p}" "(totatives p)"] 
      3 bij 
      by (metis (no_types, lifting) bij_betw_iff_bijections)
   then show ?thesis
     using cong_def by blast
  qed
  thus ?thesis
    using g_prim_root g_not_1 by auto
qed

subsection \<open>General Lemmas in a Finite Field\<close>

text \<open>
\label{primroot2}
We make certain assumptions:
From now on, we will calculate in a finite field which is the ring of integers modulo a prime $p$.
Let $n$ be the length of vectors to be transformed. 
By Dirichlet's theorem on arithmetic progressions we can
 assume that there is a natural number $k$ and a prime $p$ with $p = k\cdot n + 1$.
In order to avoid some special cases and even contradictions, 
we additionally assume that $p \geq 3$ and $n \geq 2$. 
\<close>

text \<open>\label{prelim}\<close>
locale preliminary = 
  fixes
       a_type::"('a::prime_card) itself" 
   and p::nat
   and n::nat 
   and k::nat
 assumes
       p_def: "p= CARD('a)" and p_lst3: "p > 2"  and p_fact: "p = k*n +1"
   and n_lst2: "n \<ge> 2" 
begin

lemma exp_rule: "((c::('a) mod_ring) * d )^e= (c^e) * (d^e)" 
  by (simp add: power_mult_distrib)

lemma "\<exists> y. x \<noteq> 0 \<longrightarrow> (x::(('a) mod_ring)) *  y = 1" 
  by (metis dvd_field_iff unit_dvdE)

lemma test: "prime p" 
  by (simp add: p_def prime_card)

lemma k_bound: "k > 0" 
  using p_fact prime_nat_iff'' test by force

text \<open>We show some homomorphisms.\<close>

lemma homomorphism_add: "(of_int_mod_ring x)+(of_int_mod_ring y) = 
              ((of_int_mod_ring  (x+y)) ::(('a::prime_card) mod_ring))"
  by (metis of_int_hom.hom_add of_int_of_int_mod_ring)

lemma homomorphism_mul_on_ring: "(of_int_mod_ring x)*(of_int_mod_ring y) =  
              ((of_int_mod_ring  (x*y)) ::(('a::prime_card) mod_ring))"
  by (metis of_int_mult of_int_of_int_mod_ring)

lemma exp_homo:"(of_int_mod_ring (x^i)) = ((of_int_mod_ring x)^i ::(('a::prime_card) mod_ring))"
  by (induction i) (metis of_int_of_int_mod_ring of_int_power)+

lemma mod_homo: "((of_int_mod_ring x)::(('a::prime_card) mod_ring)) = of_int_mod_ring (x mod p)"
  using p_def unfolding of_int_mod_ring_def by simp

lemma int_exp_hom: "int x ^i = int (x^i)" 
  by simp

lemma coprime_nat_int: "coprime (int p) (to_int_mod_ring pr) \<longleftrightarrow> coprime p (nat(to_int_mod_ring pr))"
  unfolding coprime_def to_int_mod_ring_def 
  by (smt (z3) Rep_mod_ring atLeastLessThan_iff dvd_trans int_dvd_int_iff int_nat_eq int_ops(2) prime_divisor_exists prime_nat_int_transfer primes_dvd_imp_eq test to_int_mod_ring.rep_eq to_int_mod_ring_def)

lemma nat_int_mod:"[nat (to_int_mod_ring pr) ^ d = 1] (mod p) = 
                           [ (to_int_mod_ring pr) ^ d = 1] (mod (int p)) "
  unfolding to_int_mod_ring_def 
  by (metis Rep_mod_ring atLeastLessThan_iff cong_int_iff int_exp_hom int_nat_eq int_ops(2) to_int_mod_ring.rep_eq to_int_mod_ring_def)

text \<open>Order of $p$ doesn't change when interpreting it as an integer.\<close>

lemma ord_lift: "ord (int p) (to_int_mod_ring pr) = ord p (nat (to_int_mod_ring pr))"
proof -
  have "to_int_mod_ring pr = int (nat (to_int_mod_ring pr))"
    by (metis Rep_mod_ring atLeastLessThan_iff int_nat_eq to_int_mod_ring.rep_eq)
  thus ?thesis
    using ord_int by metis
qed

text \<open>A primitive root has order $p-1$.\<close>

lemma primroot_ord: "residue_primroot p g \<Longrightarrow> ord p g = p -1" 
  by (simp add: residue_primroot_def test totient_prime)

text \<open>If $x^l = 1$ in $\mathbb{Z}_p$, then $l$ is an upper bound for the order of $x$ in $\mathbb{Z}_ p$.\<close>

lemma ord_max:
  assumes "l \<noteq> 0" "(x :: (('a::prime_card) mod_ring))^l = 1"
  shows " ord p (to_int_mod_ring x) \<le> l"
proof-
  have "[(to_int_mod_ring x)^l = 1] (mod p)" 
    by (metis assms(2) cong_def exp_homo of_int_mod_ring.rep_eq of_int_mod_ring_to_int_mod_ring one_mod_card_int one_mod_ring.rep_eq p_def)
  thus ?thesis unfolding ord_def using assms 
    by (smt (z3) Least_le less_imp_le_nat not_gr0)
qed

subsection \<open>Existence of $n$-th Roots of Unity in the Finite Field\<close>

text \<open>
\label{primroot3}
We obtain an element in the finite field such that
its reinterpretation as a $nat$ will be a primitive root in the residue class modulo $p$.
The difference between residue classes, their representatives in the Integers and elements 
of the finite field is notable. When conducting informal proofs, this distinction
 is usually blurred, but Isabelle enforces the explicit conversion between those structures.
\<close>

lemma primroot_ex:
  obtains primroot::"('a::prime_card) mod_ring" where 
    "primroot^(p-1) = 1"
    "primroot \<noteq> 1"
    "residue_primroot p (nat (to_int_mod_ring primroot))"
proof-
  obtain g where g_Def: "residue_primroot p g \<and> g \<noteq> 1" 
    using prime_nat_iff' prime_primitive_root_exists test 
    by (metis bigger_prime euler_theorem ord_1_right power_one_right prime_nat_iff'' residue_primroot.cases residue_primroot_cong)
  hence "[g \<noteq> 1] (mod p)" using prime_not_2_order_not_1_mod[of p g]
    by (metis One_nat_def p_lst3 less_numeral_extra(4) ord_eq_Suc_0_iff residue_primroot.cases totient_gt_1)
  hence "[g^(p-1) = 1] (mod p)" using g_Def
    by (metis coprime_commute euler_theorem residue_primroot_def test totient_prime)
  moreover hence "int (g ^ (p - 1)) mod int p = (1::int)" 
    by (metis cong_def int_ops(2) mod_less of_nat_mod prime_gt_1_nat test)
  moreover hence "of_int_mod_ring (int (g ^ (p - 1)) mod int p) = 
                      ((of_int_mod_ring 1) ::(('a::prime_card) mod_ring))" by simp
  ultimately have "(of_int_mod_ring (g^(p-1))) = (1 ::(('a::prime_card) mod_ring))" 
    using mod_homo[of "g^(p-1)"]  by (metis exp_homo power_0)
  hence "((of_int_mod_ring g)^(p-1) ::(('a::prime_card) mod_ring)) = 1" 
    using exp_homo[of "int g" "p-1"] by simp
  moreover 
  have "((of_int_mod_ring g) ::(('a::prime_card) mod_ring)) \<noteq> 1" 
  proof
    assume "((of_int_mod_ring g) ::(('a::prime_card) mod_ring)) = 1"
    hence "[int g = 1] (mod p)" using p_def unfolding of_int_mod_ring_def 
      by (metis \<open>of_int_mod_ring (int g) = 1\<close> cong_def of_int_mod_ring.rep_eq one_mod_card_int one_mod_ring.rep_eq)
    hence "[g=1] (mod p)"
      by (metis cong_int_iff int_ops(2))
    thus False 
      using \<open>[g \<noteq> 1] (mod p)\<close> by auto
  qed
  moreover have \<open>residue_primroot p (g mod p)\<close>
    using g_Def by simp
  then have \<open>residue_primroot p (nat (to_int_mod_ring (of_int_mod_ring (int g) :: 'a mod_ring)))\<close>
    by (transfer fixing: p) (simp add: p_def nat_mod_distrib)
  ultimately show thesis ..
qed

text \<open>From this, we obtain an $n$-th root of unity $\omega$ in the finite 
field of characteristic $p$.
 Note that in this step we will use the assumption $p = k \cdot n +1$ 
from locale $preliminary$: The $k$-th power of a primitive 
root $pr$ modulo $p$ will have the property $(pr^k)^n \equiv 1 \mod p$.
\<close>

lemma omega_properties_ex: 
  obtains \<omega> ::"(('a::prime_card) mod_ring)" 
  where  "\<omega>^n = 1" 
         "\<omega> \<noteq> 1"  
         "\<forall> m. \<omega>^m = 1 \<and> m\<noteq>0 \<longrightarrow> m \<ge> n"
proof-
  obtain pr::"(('a::prime_card) mod_ring)" where a: "pr^(p-1) = 1 " and b: "pr \<noteq> 1"
              and c: "residue_primroot p (nat( to_int_mod_ring pr))"
    using primroot_ex by blast
  moreover hence "(pr^k)^n =1" 
    by (simp add: p_fact power_mult)
  moreover have "pr^k \<noteq> 1"
  proof
    assume " pr ^ k = 1"
    hence "(to_int_mod_ring pr)^k mod p = 1"
      by (metis exp_homo of_int_mod_ring.rep_eq of_int_mod_ring_to_int_mod_ring one_mod_ring.rep_eq p_def)
    hence "ord p (to_int_mod_ring pr) \<le> k"
      by (simp add: \<open>pr ^ k = 1\<close> k_bound ord_max)
    hence "ord p (nat (to_int_mod_ring pr)) \<le> k" 
      by (metis ord_lift)
    also have "ord p (nat (to_int_mod_ring pr)) = p - 1"
      using c primroot_ord[of "(nat (to_int_mod_ring pr))"] by blast
    also have "\<dots> = k * n"
      using p_fact by simp
    finally have "n \<le> 1"
      using k_bound by simp
    thus False
      using n_lst2 by linarith
  qed
  moreover have "\<forall> m. (pr^k)^m = 1 \<and> m\<noteq>0 \<longrightarrow> m \<ge> n"
  proof(rule ccontr)
    assume  "\<not> (\<forall>m. (pr ^ k) ^ m = 1 \<and> m\<noteq>0 \<longrightarrow> n \<le> m) "
    then obtain m where "(pr^k)^m = 1  \<and> m\<noteq>0 \<and> m < n" by force
    hence "ord p (to_int_mod_ring pr) \<le> k * m" using ord_max[of "k*m" pr]
      by (metis calculation(5) mult_is_0 power_mult) 
    moreover have "ord p (nat (to_int_mod_ring pr)) = p-1" using c primroot_ord ord_lift by simp
    ultimately show False 
      by (metis \<open>(pr ^ k) ^ m = 1 \<and> m \<noteq> 0 \<and> m < n\<close> add_diff_cancel_right' nat_0_less_mult_iff nat_mult_le_cancel_disj not_less ord_lift p_def p_fact prime_card prime_gt_1_nat zero_less_diff)
  qed
    ultimately show ?thesis
    using that by simp
qed

text \<open>We define an $n$-th root of unity $\omega$ for $NTT$.\<close>
theorem omega_exists: "\<exists> \<omega> ::(('a::prime_card) mod_ring) .
                              \<omega>^n = 1 \<and> \<omega> \<noteq> 1 \<and> (\<forall> m. \<omega>^m = 1 \<and> m\<noteq>0 \<longrightarrow> m \<ge> n)"
  using omega_properties_ex by metis

definition "(omega::(('a::prime_card) mod_ring)) = 
       (SOME \<omega> . (\<omega>^n = 1 \<and> \<omega> \<noteq> 1\<and> (\<forall> m. \<omega>^m = 1 \<and> m\<noteq>0 \<longrightarrow> m \<ge> n)))"

lemma omega_properties: "omega^n = 1" "omega \<noteq> 1" 
  "(\<forall> m. omega^m = 1 \<and> m\<noteq>0 \<longrightarrow> m \<ge> n)"
  unfolding omega_def using omega_exists 
  by (smt (verit, best) verit_sko_ex')+

text \<open>We define the multiplicative inverse $\mu$ of $\omega$.\<close>

definition "mu = omega ^ (n - 1)"

lemma mu_properties: "mu * omega = 1" "mu \<noteq> 1" 
proof -
  have "omega ^ (n - 1) * omega = omega ^ Suc (n - 1)"
    by simp
  also have "Suc (n - 1) = n"
    using n_lst2 by simp
  also have "omega ^ n = 1"
    using omega_properties(1) by auto
  finally show "mu * omega = 1"
    by (simp add: mu_def)
next
  show "mu \<noteq> 1"
    using omega_properties n_lst2 by (auto simp: mu_def)
qed

subsection \<open>Some Lemmas on Sums\<close>
text \<open>\label{sums}\<close>

text \<open>The following lemmas concern sums over a finite field. 
 Most of the propositions are intuitive.\<close>

lemma sum_in: "(\<Sum>i=0..<(x::nat). f i * (y ::('a mod_ring))) = (\<Sum>i=0..<x. f i )* (y) "
  by(induction x) (auto simp add: algebra_simps)

lemma sum_eq: "(\<And> i. i < x \<Longrightarrow> f i = g i)
                    \<Longrightarrow> (\<Sum>i=0..<(x::nat). f i) = (\<Sum>i=0..<x. g i) " 
  by(induction x) (auto simp add: algebra_simps)

lemma sum_diff_in: "(\<Sum>i=0..<(x::nat). (f i)::('a mod_ring)) - (\<Sum>i=0..<x. g i) = 
                    (\<Sum>i=0..<x. f i - g i)"
 by(induction x) (auto simp add: algebra_simps)

lemma sum_swap: "(\<Sum>i=0..<(x::nat). \<Sum>j=0..<(y::nat). f i j) = 
                 (\<Sum>j=0..<(y::nat). \<Sum>i=0..<(x::nat). f i j ) "
  using Groups_Big.comm_monoid_add_class.sum.swap by fast

lemma sum_const: "(\<Sum>i=0..<(x::nat). (c::('a::prime_card) mod_ring)) = (of_int_mod_ring x) * c" 
  by(induction x, simp add: algebra_simps,  simp add: algebra_simps)
    (metis distrib_left mult.right_neutral of_int_of_int_mod_ring of_int_of_nat_eq of_nat_Suc)

lemma sum_split: "(r1::nat) < r2 \<Longrightarrow> (\<Sum>l = 0..<r1. ((f l)::(('a::prime_card) mod_ring))) 
                                         +(\<Sum>l = r1..<r2. f l) = (\<Sum>l = 0..<r2. f l)" 
  by (meson less_or_eq_imp_le sum.atLeastLessThan_concat zero_le)

lemma sum_index_shift: "(\<Sum>l = (a::nat)..< b. f(l+c)) = (\<Sum>l = (a+c)..< (b+c). f l )"
  by(induction a arbitrary: b c) (metis sum.shift_bounds_nat_ivl)+

text \<open>One may sum over even and odd indices independently.
The lemma statement was taken from a formalization of FFT~\parencite{FFT-AFP}. 
We give an alternative proof adapted to the finite field $\mathbb{Z}_p$. 
\<close>

lemma sum_splice:
  "(\<Sum>i::nat = 0..<2*nn. f i) = (\<Sum>i = 0..<nn. f (2*i)) + (\<Sum>i = 0..<nn. f (2*i+1))"
proof(induction nn)
  case (Suc n)
  have "(\<Sum>i::nat = 0..<2*(n+1). f i)  = (\<Sum>i::nat = 0..<(2*n). f i) + f(2*n+1) + f (2*n)" 
    by( simp add: algebra_simps)
  also have "\<dots> = (\<Sum>i::nat = 0..<n. f (2*i)) + (\<Sum>i::nat = 0..<n. f (2*i+1)) + f(2*n+1) + f (2*n)"
    using Suc by simp
  also have "\<dots> = (\<Sum>i::nat = 0..<(Suc n). f (2*i)) + (\<Sum>i::nat = 0..<(Suc n). f (2*i+1))"
   by( simp add: algebra_simps)
  finally show ?case by simp
qed simp

lemma sum_even_odd_split: "even (a::nat) \<Longrightarrow> (\<Sum>j=0..<(a div 2). f (2*j))+ (\<Sum>j=0..<(a div 2). f (2*j+1)) =  (\<Sum>j=0..<a. f j)"
  by (induction a, simp)(metis even_two_times_div_two sum_splice)

lemma sum_splice_other_way_round: " (\<Sum>j=(0::nat)..<i. f (2*j)) + (\<Sum>j=0..<i. f (2*j+1)) = 
        (\<Sum>j=(0::nat)..<2*i. f j )"
by (metis sum_splice)

lemma sum_neg_in: "- (\<Sum>j = 0..<l. (f j)::('a mod_ring)) =  (\<Sum>j = 0..<l. - f j) " 
  by (simp add: sum_negf)

subsection \<open>Geometric Sums\<close>

text \<open>\label{geosum}\<close>

text \<open>This lemma will be important for proving properties on $\mathsf{NTT}$. At first, an informal proof sketch:
\begin{align*}
(1-x) \cdot \sum \limits _{l = 0} ^ {r-1} x^l 
&= \sum \limits _{l = 0} ^ {r-1} x^l  - x \cdot \sum \limits _{l = 0} ^{r-1} x^l \\ 
&= \sum \limits _{l = 0} ^ {r-1} x^l  - \sum \limits _{l = 1} ^{r} x^l \\ 
& = 1 - x^r
\end{align*}

The same lemma for integers can be found in~\parencite{Dirichlet_Series-AFP}.
 Our version is adapted to finite fields.
\<close>

lemma geo_sum: 
  assumes "x \<noteq> 1"
  shows "(1-x)*(\<Sum>l = 0..<r. (x::('a mod_ring))^l) = (1-x^r)"
proof-
  have 0:"x * (\<Sum>l = 0..<r. x^l) = (\<Sum>l = 0..<r. x^(Suc l))" using sum_in[of "\<lambda> l. x^l" x r] 
    by(simp add: algebra_simps)
  have 1:"(\<Sum>l = 0..<r. x^l) - (\<Sum>l = 0..<r. x^(Suc l)) = (\<Sum>l = 0..<r. x^l - x^(Suc l))" 
    by(rule sum_diff_in)
  have 2: "(\<Sum>l = 0..<r. x^l - x^(Suc l)) = 1 - x^r"
    by(induction r) simp+
  thus ?thesis
    by (simp add: lessThan_atLeast0 one_diff_power_eq)
qed 

lemmas sum_rules = sum_in sum_eq sum_diff_in sum_swap sum_const sum_split sum_index_shift

end
end
