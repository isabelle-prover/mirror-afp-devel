(*
    File:      Arithmetic_Summatory.thy
    Author:    Manuel Eberl, TU München
*)
section \<open>Summatory arithmetic functions\<close>
theory Arithmetic_Summatory
  imports 
    More_Totient
    Moebius_Mu
    Liouville_Lambda
    Divisor_Count 
    Dirichlet_Series
begin

subsection \<open>Definition\<close>

definition sum_upto :: "(nat \<Rightarrow> 'a :: comm_monoid_add) \<Rightarrow> real \<Rightarrow> 'a" where
  "sum_upto f x = (\<Sum>i | 0 < i \<and> real i \<le> x. f i)"

lemma sum_upto_altdef: "sum_upto f x = (\<Sum>i\<in>{0<..nat \<lfloor>x\<rfloor>}. f i)"
  unfolding sum_upto_def
  by (cases "x \<ge> 0"; intro sum.cong refl) (auto simp: le_nat_iff le_floor_iff)

lemma sum_upto_1 [simp]: "sum_upto f 1 = f 1"
proof -
  have "{0<..Suc 0} = {1}" by auto
  thus ?thesis by (simp add: sum_upto_altdef)
qed

lemma sum_upto_cong [cong]:
  "(\<And>n. n > 0 \<Longrightarrow> real n \<le> x \<Longrightarrow> f n = f' n) \<Longrightarrow> x = x' \<Longrightarrow> sum_upto f x = sum_upto f' x'"
  unfolding sum_upto_def by (intro sum.cong) auto
    
lemma sum_upto_0 [simp]: "sum_upto f 0 = 0"
  by (simp add: sum_upto_altdef)

lemma finite_Nats_le_real [simp,intro]: "finite {n. 0 < n \<and> real n \<le> x}"
proof (rule finite_subset)
  show "finite {n. n \<le> nat \<lfloor>x\<rfloor>}" by auto
  show "{n. 0 < n \<and> real n \<le> x} \<subseteq> {n. n \<le> nat \<lfloor>x\<rfloor>}" by safe linarith
qed

lemma sum_upto_ind: "sum_upto (ind P) x = of_nat (card {n. n > 0 \<and> real n \<le> x \<and> P n})"
proof -
  have "sum_upto (ind P :: nat \<Rightarrow> 'a) x = (\<Sum>n | 0 < n \<and> real n \<le> x \<and> P n. 1)"
    unfolding sum_upto_def by (intro sum.mono_neutral_cong_right) (auto simp: ind_def)
  also have "\<dots> = of_nat (card {n. n > 0 \<and> real n \<le> x \<and> P n})" by simp
  finally show ?thesis .
qed

lemma sum_upto_sum_divisors:
  "sum_upto (\<lambda>n. \<Sum>d | d dvd n. f n d) x = sum_upto (\<lambda>k. sum_upto (\<lambda>d. f (d * k) k) (x / k)) x"
proof -
  let ?B = "(SIGMA k:{k. 0 < k \<and> real k \<le> x}. {d. 0 < d \<and> real d \<le> x / real k})"
  let ?A = "(SIGMA k:{k. 0 < k \<and> real k \<le> x}. {d. d dvd k})"
  have *: "real a \<le> x" if "real (a * b) \<le> x" "b > 0" for a b
  proof -
    have "real a * 1 \<le> real (a * b)" unfolding of_nat_mult using that
      by (intro mult_left_mono) auto
    also have "\<dots> \<le> x" by fact
    finally show ?thesis by simp
  qed
  have bij: "bij_betw (\<lambda>(k,d). (d * k, k)) ?B ?A"
    by (rule bij_betwI[where g = "\<lambda>(k,d). (d, k div d)"])
       (auto simp: * divide_simps mult.commute elim!: dvdE)

  have "sum_upto (\<lambda>n. \<Sum>d | d dvd n. f n d) x = (\<Sum>(k,d)\<in>?A. f k d)"
    unfolding sum_upto_def by (rule sum.Sigma) auto
  also have "\<dots> = (\<Sum>(k,d)\<in>?B. f (d * k) k)"
    by (subst sum.reindex_bij_betw[OF bij, symmetric]) (auto simp: case_prod_unfold)
  also have "\<dots> = sum_upto (\<lambda>k. sum_upto (\<lambda>d. f (d * k) k) (x / k)) x"
    unfolding sum_upto_def by (rule sum.Sigma [symmetric]) auto
  finally show ?thesis .
qed

lemma sum_upto_dirichlet_prod:
  "sum_upto (dirichlet_prod f g) x = sum_upto (\<lambda>d. f d * sum_upto g (x / real d)) x"
  unfolding dirichlet_prod_def
  by (subst sum_upto_sum_divisors) (simp add: sum_upto_def sum_distrib_left)

lemma sum_upto_real: 
  assumes "x \<ge> 0"
  shows   "sum_upto real x = of_int (floor x) * (of_int (floor x) + 1) / 2"
proof -
  have A: "2 * \<Sum>{1..n} = n * Suc n" for n by (induction n) simp_all
  have "2 * sum_upto real x = real (2 * \<Sum>{0<..nat \<lfloor>x\<rfloor>})" by (simp add: sum_upto_altdef)
  also have "{0<..nat \<lfloor>x\<rfloor>} = {1..nat \<lfloor>x\<rfloor>}" by auto
  also note A
  also have "real (nat \<lfloor>x\<rfloor> * Suc (nat \<lfloor>x\<rfloor>)) = of_int (floor x) * (of_int (floor x) + 1)" using assms
    by (simp add: algebra_simps)
  finally show ?thesis by simp
qed

lemma summable_imp_convergent_sum_upto:
  assumes "summable (f :: nat \<Rightarrow> 'a :: real_normed_vector)"
  obtains c where "(sum_upto f \<longlongrightarrow> c) at_top"
proof -
  from assms have "summable (\<lambda>n. f (Suc n))"
    by (subst summable_Suc_iff)
  then obtain c where "(\<lambda>n. f (Suc n)) sums c" by (auto simp: summable_def)
  hence "(\<lambda>n. \<Sum>k<n. f (Suc k)) \<longlonglongrightarrow> c" by (auto simp: sums_def)
  also have "(\<lambda>n. \<Sum>k<n. f (Suc k)) = (\<lambda>n. \<Sum>k\<in>{0<..n}. f k)"
    by (subst sum.atLeast1_atMost_eq [symmetric]) (auto simp: atLeastSucAtMost_greaterThanAtMost)
  finally have "((\<lambda>x. sum f {0<..nat \<lfloor>x\<rfloor>}) \<longlongrightarrow> c) at_top"
    by (rule filterlim_compose)
       (auto intro!: filterlim_compose[OF filterlim_nat_sequentially] filterlim_floor_sequentially)
  also have "(\<lambda>x. sum f {0<..nat \<lfloor>x\<rfloor>}) = sum_upto f"
    by (intro ext) (simp_all add: sum_upto_altdef)
  finally show ?thesis using that[of c] by blast
qed

lemma sum_upto_divisor_sum1:
  "sum_upto (\<lambda>n. \<Sum>d | d dvd n. f d :: real) x = sum_upto (\<lambda>n. f n * floor (x / n)) x"
proof -
  have "sum_upto (\<lambda>n. \<Sum>d | d dvd n. f d :: real) x =
          sum_upto (\<lambda>n. f n * real (nat (floor (x / n)))) x"
    using sum_upto_dirichlet_prod[of f "\<lambda>_. 1" x]
    by (simp add: dirichlet_prod_def sum_upto_altdef)
  also have "\<dots> = sum_upto (\<lambda>n. f n * floor (x / n)) x"
    unfolding sum_upto_def by (intro sum.cong) auto
  finally show ?thesis .
qed

lemma sum_upto_divisor_sum2:
  "sum_upto (\<lambda>n. \<Sum>d | d dvd n. f d :: real) x = sum_upto (\<lambda>n. sum_upto f (x / n)) x"
  using sum_upto_dirichlet_prod[of "\<lambda>_. 1" f x] by (simp add: dirichlet_prod_altdef1)

lemma ln_fact_conv_sum_mangoldt:
  "sum_upto (\<lambda>n. mangoldt n * \<lfloor>x / real n\<rfloor>) x = ln (fact (nat \<lfloor>x\<rfloor>))"
proof -
  have "sum_upto (\<lambda>n. mangoldt n * of_int \<lfloor>x / real n\<rfloor>) x =
          sum_upto (\<lambda>n. \<Sum>d | d dvd n. mangoldt d :: real) x"
    using sum_upto_divisor_sum1[of mangoldt x] by auto
  also have "\<dots> = sum_upto (\<lambda>n. of_real (ln (real n))) x"
    by (intro sum_upto_cong mangoldt_sum refl) auto
  also have "\<dots> = (\<Sum>n\<in>{0<..nat \<lfloor>x\<rfloor>}. ln n)"
    by (simp add: sum_upto_altdef)
  also have "\<dots> = ln (\<Prod>{0<..nat \<lfloor>x\<rfloor>})"
    unfolding of_nat_prod by (subst ln_prod) auto
  also have "{0<..nat \<lfloor>x\<rfloor>} = {1..nat \<lfloor>x\<rfloor>}" by auto
  also have "\<Prod>\<dots> = fact (nat \<lfloor>x\<rfloor>)"
    by (simp add: fact_prod)
  finally show ?thesis by simp
qed


subsection \<open>Generalised Dirichlet products\<close>

(* TODO: Move to Dirichlet_Series *)

definition dirichlet_prod' :: "(nat \<Rightarrow> 'a :: comm_semiring_1) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> 'a" where
  "dirichlet_prod' f g x = sum_upto (\<lambda>m. f m * g (x / real m)) x"

lemma dirichlet_prod'_one_left:
  "dirichlet_prod' (\<lambda>n. if n = 1 then 1 else 0) f x = (if x \<ge> 1 then f x else 0)"
proof -
  have  "dirichlet_prod' (\<lambda>n. if n = 1 then 1 else 0) f x =
           (\<Sum>i | 0 < i \<and> real i \<le> x. (if i = Suc 0 then 1 else 0) * f (x / real i))"
    by (simp add: dirichlet_prod'_def sum_upto_def)
  also have "\<dots> = (\<Sum>i\<in>(if x \<ge> 1 then {1::nat} else {}). f x)"
    by (intro sum.mono_neutral_cong_right) (auto split: if_splits)
  also have "\<dots> = (if x \<ge> 1 then f x else 0)"
    by simp
  finally show ?thesis .
qed

lemma dirichlet_prod'_cong:
  assumes "\<And>n. n > 0 \<Longrightarrow> real n \<le> x \<Longrightarrow> f n = f' n"
  assumes "\<And>y. y \<ge> 1 \<Longrightarrow> y \<le> x \<Longrightarrow> g y = g' y"
  assumes "x = x'"
  shows   "dirichlet_prod' f g x = dirichlet_prod' f' g' x'"
  unfolding dirichlet_prod'_def 
  by (intro sum_upto_cong assms, (subst assms | simp add: assms field_simps)+)

(* 2.21 *)
lemma dirichlet_prod'_assoc:
  "dirichlet_prod' f (\<lambda>y. dirichlet_prod' g h y) x = dirichlet_prod' (dirichlet_prod f g) h x"
proof -
  have "dirichlet_prod' f (\<lambda>y. dirichlet_prod' g h y) x =
          (\<Sum>m | m > 0 \<and> real m \<le> x. \<Sum>n | n > 0 \<and> real n \<le> x / m. f m * g n * h (x / (m * n)))"
    by (simp add: algebra_simps dirichlet_prod'_def dirichlet_prod_def
                  sum_upto_def sum_distrib_left sum_distrib_right)
  also have "\<dots> = (\<Sum>(m,n)\<in>(SIGMA m:{m. m > 0 \<and> real m \<le> x}. {n. n > 0 \<and> real n \<le> x / m}).
                     f m * g n * h (x / (m * n)))"
    by (subst sum.Sigma) auto
  also have "\<dots> = (\<Sum>(mn, m)\<in>(SIGMA mn:{mn. mn > 0 \<and> real mn \<le> x}. {m. m dvd mn}).
                    f m * g (mn div m) * h (x / mn))"
    by (rule sum.reindex_bij_witness[of _ "\<lambda>(mn, m). (m, mn div m)" "\<lambda>(m, n). (m * n, m)"])
       (auto simp: case_prod_unfold field_simps dest: dvd_imp_le)
  also have "\<dots> = dirichlet_prod' (dirichlet_prod f g) h x"
    by (subst sum.Sigma [symmetric])
       (simp_all add: dirichlet_prod'_def dirichlet_prod_def sum_upto_def
                      algebra_simps sum_distrib_left sum_distrib_right)
  finally show ?thesis .
qed

(* 2.22 *)
lemma dirichlet_prod'_inversion1:
  assumes "\<forall>x\<ge>1. g x = dirichlet_prod' a f x" "x \<ge> 1"
          "dirichlet_prod a ainv = (\<lambda>n. if n = 1 then 1 else 0)"
  shows   "f x = dirichlet_prod' ainv g x"
proof -
  have "dirichlet_prod' ainv g x = dirichlet_prod' ainv (dirichlet_prod' a f) x"
    using assms by (intro dirichlet_prod'_cong) auto
  also have "\<dots> = dirichlet_prod' (\<lambda>n. if n = 1 then 1 else 0) f x"
    using assms by (simp add: dirichlet_prod'_assoc dirichlet_prod_commutes)
  also have "\<dots> = f x"
    using assms by (subst dirichlet_prod'_one_left) auto
  finally show ?thesis ..
qed

lemma dirichlet_prod'_inversion2:
  assumes "\<forall>x\<ge>1. f x = dirichlet_prod' ainv g x" "x \<ge> 1"
          "dirichlet_prod a ainv = (\<lambda>n. if n = 1 then 1 else 0)"
  shows   "g x = dirichlet_prod' a f x"
proof -
  have "dirichlet_prod' a f x = dirichlet_prod' a (dirichlet_prod' ainv g) x"
    using assms by (intro dirichlet_prod'_cong) auto
  also have "\<dots> = dirichlet_prod' (\<lambda>n. if n = 1 then 1 else 0) g x"
    using assms by (simp add: dirichlet_prod'_assoc dirichlet_prod_commutes)
  also have "\<dots> = g x"
    using assms by (subst dirichlet_prod'_one_left) auto
  finally show ?thesis ..
qed

lemma dirichlet_prod'_inversion:
  assumes "dirichlet_prod a ainv = (\<lambda>n. if n = 1 then 1 else 0)"
  shows   "(\<forall>x\<ge>1. g x = dirichlet_prod' a f x) \<longleftrightarrow> (\<forall>x\<ge>1. f x = dirichlet_prod' ainv g x)"
  using dirichlet_prod'_inversion1[of g a f _ ainv] dirichlet_prod'_inversion2[of f ainv g _ a]
        assms by blast

lemma dirichlet_prod'_inversion':
  assumes "a 1 * y = 1"
  defines "ainv \<equiv> dirichlet_inverse a y"
  shows   "(\<forall>x\<ge>1. g x = dirichlet_prod' a f x) \<longleftrightarrow> (\<forall>x\<ge>1. f x = dirichlet_prod' ainv g x)"
  unfolding ainv_def
  by (intro dirichlet_prod'_inversion dirichlet_prod_inverse assms)

(* 3.11 *)
lemma dirichlet_prod'_floor_conv_sum_upto:
  "dirichlet_prod' f (\<lambda>x. real_of_int (floor x)) x = sum_upto (\<lambda>n. sum_upto f (x / n)) x"
proof -
  have [simp]: "sum_upto (\<lambda>_. 1 :: real) x = real (nat \<lfloor>x\<rfloor>)" for x
    by (simp add: sum_upto_altdef)
  show ?thesis
    using sum_upto_dirichlet_prod[of "\<lambda>n. 1::real" f] sum_upto_dirichlet_prod[of f "\<lambda>n. 1::real"]
    by (simp add: dirichlet_prod'_def dirichlet_prod_commutes)
qed

(* 2.23 *)
lemma dirichlet_prod_inversion_completely_multiplicative:
  fixes a :: "nat \<Rightarrow> 'a :: comm_ring_1"
  assumes "completely_multiplicative_function a"
  shows   "(\<forall>x\<ge>1. g x = dirichlet_prod' a f x) \<longleftrightarrow>
             (\<forall>x\<ge>1. f x = dirichlet_prod' (\<lambda>n. moebius_mu n * a n) g x)"
  by (intro dirichlet_prod'_inversion ext completely_multiplicative_imp_moebius_mu_inverse assms)



subsection \<open>The Hyperbola method\<close>

lemma hyperbola_method_semiring:
  fixes f g :: "nat \<Rightarrow> 'a :: comm_semiring_0"
  assumes "A \<ge> 0" and "B \<ge> 0" and "A * B = x"
  shows   "sum_upto (dirichlet_prod f g) x + sum_upto f A * sum_upto g B = 
             sum_upto (\<lambda>n. f n * sum_upto g (x / real n)) A +
             sum_upto (\<lambda>n. sum_upto f (x / real n) * g n) B"
proof -
  from assms have [simp]: "x \<ge> 0" by auto
  {
    fix a b :: real assume ab: "a > 0" "b > 0" "x \<ge> 0" "a * b \<le> x" "a > A" "b > B"
    hence "a * b > A * B" using assms by (intro mult_strict_mono) auto
    also from assms have "A * B = x" by simp
    finally have False using \<open>a * b \<le> x\<close> by simp
  } note * = this
  have *: "a \<le> A \<or> b \<le> B" if "a * b \<le> x" "a > 0" "b > 0" "x \<ge> 0" for a b
    by (rule ccontr) (insert *[of a b] that, auto)
  
  have nat_mult_leD1: "real a \<le> x" if "real a * real b \<le> x" "b > 0" for a b
  proof -
    from that have "real a * 1 \<le> real a * real b" by (intro mult_left_mono) simp_all
    also have "\<dots> \<le> x" by fact
    finally show ?thesis by simp
  qed
  have nat_mult_leD2: "real b \<le> x" if "real a * real b \<le> x" "a > 0" for a b
    using nat_mult_leD1[of b a] that by (simp add: mult_ac)
  
  have le_sqrt_mult_imp_le: "a * b \<le> x" 
    if "a \<ge> 0" "b \<ge> 0" "a \<le> A" "b \<le> B" for a b :: real
  proof -
    from that and assms have "a * b \<le> A * B" by (intro mult_mono) auto
    with assms show "a * b \<le> x" by simp
  qed
  
  define F G where "F = sum_upto f" and "G = sum_upto g"  
  let ?Bound = "{0<..nat \<lfloor>x\<rfloor>} \<times> {0<..nat \<lfloor>x\<rfloor>}"
  let ?B = "{(r,d). 0 < r \<and> real r \<le> A \<and> 0 < d \<and> real d \<le> x / real r}"
  let ?C = "{(r,d). 0 < d \<and> real d \<le> B \<and> 0 < r \<and> real r \<le> x / real d}"
  let ?B' = "SIGMA r:{r. 0 < r \<and> real r \<le> A}. {d. 0 < d \<and> real d \<le> x / real r}"
  let ?C' = "SIGMA d:{d. 0 < d \<and> real d \<le> B}. {r. 0 < r \<and> real r \<le> x / real d}"
  have "sum_upto (dirichlet_prod f g) x + F A * G B = 
          (\<Sum>(i,(r,d)) \<in> (SIGMA i:{i. 0 < i \<and> real i \<le> x}. {(r,d). r * d = i}). f r * g d) + 
          sum_upto f A * sum_upto g B" (is "_ = ?S + _")
    unfolding sum_upto_def dirichlet_prod_altdef2 F_def G_def
    by (subst sum.Sigma) (auto intro: finite_divisors_nat')
  also have "?S = (\<Sum>(r,d) | 0 < r \<and> 0 < d \<and> real (r * d) \<le> x. f r * g d)"
    (is "_ = sum _ ?A") by (intro sum.reindex_bij_witness[of _ "\<lambda>(r,d). (r*d,(r,d))" snd]) auto
  also have "?A = ?B \<union> ?C"  by (auto simp: field_simps dest: *)
  also have "sum_upto f A * sum_upto g B = 
               (\<Sum>r | 0 < r \<and> real r \<le> A. \<Sum>d | 0 < d \<and> real d \<le> B. f r * g d)"
    by (simp add: sum_upto_def sum_product)
  also have "\<dots> = (\<Sum>(r,d)\<in>{r. 0 < r \<and> real r \<le> A} \<times> {d. 0 < d \<and> real d \<le> B}. f r * g d)"
    (is "_ = sum _ ?X") by (rule sum.cartesian_product)
  also have "?X = ?B \<inter> ?C" by (auto simp: field_simps le_sqrt_mult_imp_le)
  also have "(\<Sum>(r,d)\<in>?B \<union> ?C. f r * g d) + (\<Sum>(r,d)\<in>?B \<inter> ?C. f r * g d) = 
               (\<Sum>(r,d)\<in>?B. f r * g d) + (\<Sum>(r,d)\<in>?C. f r * g d)"
    by (intro sum.union_inter finite_subset[of ?B ?Bound] finite_subset[of ?C ?Bound])
       (auto simp: field_simps le_nat_iff le_floor_iff dest: nat_mult_leD1 nat_mult_leD2)
  also have "?B = ?B'" by auto
  hence "(\<lambda>f. sum f ?B) = (\<lambda>f. sum f ?B')" by simp
  also have "(\<Sum>(r,d)\<in>?B'. f r * g d) = sum_upto (\<lambda>n. f n * G (x / real n)) A"
    by (subst sum.Sigma [symmetric]) (simp_all add: sum_upto_def sum_distrib_left G_def)
  also have "(\<Sum>(r,d)\<in>?C. f r * g d) = (\<Sum>(d,r)\<in>?C'. f r * g d)"
    by (intro sum.reindex_bij_witness[of _ "\<lambda>(x,y). (y,x)" "\<lambda>(x,y). (y,x)"]) auto
  also have "\<dots> = sum_upto (\<lambda>n. F (x / real n) * g n) B"
    by (subst sum.Sigma [symmetric]) (simp_all add: sum_upto_def sum_distrib_right F_def)
  finally show ?thesis by (simp only: F_def G_def)
qed

lemma hyperbola_method_semiring_sqrt:
  fixes f g :: "nat \<Rightarrow> 'a :: comm_semiring_0"
  assumes "x \<ge> 0"
  shows   "sum_upto (dirichlet_prod f g) x + sum_upto f (sqrt x) * sum_upto g (sqrt x) = 
             sum_upto (\<lambda>n. f n * sum_upto g (x / real n)) (sqrt x) +
             sum_upto (\<lambda>n. sum_upto f (x / real n) * g n) (sqrt x)"
  using assms hyperbola_method_semiring[of "sqrt x" "sqrt x" x] by simp

lemma hyperbola_method:
  fixes f g :: "nat \<Rightarrow> 'a :: comm_ring"
  assumes "A \<ge> 0" "B \<ge> 0" "A * B = x"
  shows   "sum_upto (dirichlet_prod f g) x = 
             sum_upto (\<lambda>n. f n * sum_upto g (x / real n)) A +
             sum_upto (\<lambda>n. sum_upto f (x / real n) * g n) B -
             sum_upto f A * sum_upto g B"
  using hyperbola_method_semiring[OF assms, of f g] by (simp add: algebra_simps)

lemma hyperbola_method_sqrt:
  fixes f g :: "nat \<Rightarrow> 'a :: comm_ring"
  assumes "x \<ge> 0"
  shows   "sum_upto (dirichlet_prod f g) x = 
             sum_upto (\<lambda>n. f n * sum_upto g (x / real n)) (sqrt x) +
             sum_upto (\<lambda>n. sum_upto f (x / real n) * g n) (sqrt x) -
             sum_upto f (sqrt x) * sum_upto g (sqrt x)"
  using assms hyperbola_method[of "sqrt x" "sqrt x" x] by simp


subsection \<open>A weighted sum of the Möbius \<open>\<mu>\<close> function\<close>

(* TODO: Move to Dirichlet_Series? *)

lemma sum_upto_moebius_times_floor_linear:
  "sum_upto (\<lambda>n. moebius_mu n * \<lfloor>x / real n\<rfloor>) x = (if x \<ge> 1 then 1 else 0)"
proof -
  have "real_of_int (sum_upto (\<lambda>n. moebius_mu n * \<lfloor>x / real n\<rfloor>) x) =
          sum_upto (\<lambda>n. moebius_mu n * of_int \<lfloor>x / real n\<rfloor>) x"
    by (simp add: sum_upto_def)
  also have "\<dots> = sum_upto (\<lambda>n. \<Sum>d | d dvd n. moebius_mu d :: real) x"
    using sum_upto_divisor_sum1[of moebius_mu x] by auto
  also have "\<dots> = sum_upto (\<lambda>n. if n = 1 then 1 else 0) x"
    by (intro sum_upto_cong sum_moebius_mu_divisors' refl)
  also have "\<dots> = real_of_int (if x \<ge> 1 then 1 else 0)"
    by (auto simp: sum_upto_def)
  finally show ?thesis unfolding of_int_eq_iff .
qed

(* 3.13 *)
context
  fixes M :: "real \<Rightarrow> real"
  defines "M \<equiv> (\<lambda>x. sum_upto (\<lambda>n. moebius_mu n / n) x)"
begin

lemma abs_sum_upto_moebius_mu_over_n_less:
  assumes x: "x \<ge> 2"
  shows   "\<bar>M x\<bar> < 1"
proof -
  have "x * sum_upto (\<lambda>n. moebius_mu n / n) x - sum_upto (\<lambda>n. moebius_mu n * frac (x / n)) x =
          sum_upto (\<lambda>n. moebius_mu n * (x / n - frac (x / n))) x"
    by (subst mult.commute[of x])
       (simp add: sum_upto_def sum_distrib_right sum_subtractf ring_distribs)
  also have "(\<lambda>n. x / real n - frac (x / real n)) = (\<lambda>n. of_int (floor (x / real n)))"
    by (simp add: frac_def)
  also have "sum_upto (\<lambda>n. moebius_mu n * real_of_int \<lfloor>x / real n\<rfloor>) x =
               real_of_int (sum_upto (\<lambda>n. moebius_mu n * \<lfloor>x / real n\<rfloor>) x)"
    by (simp add: sum_upto_def)
  also have "\<dots> = 1"
    using x by (subst sum_upto_moebius_times_floor_linear) auto
  finally have eq: "x * M x = 1 + sum_upto (\<lambda>n. moebius_mu n * frac (x / n)) x"
    by (simp add: M_def)

  have "x * \<bar>M x\<bar> = \<bar>x * M x\<bar>"
    using x by (simp add: abs_mult)
  also note eq
  also have "\<bar>1 + sum_upto (\<lambda>n. moebius_mu n * frac (x / n)) x\<bar> \<le>
               1 + \<bar>sum_upto (\<lambda>n. moebius_mu n * frac (x / n)) x\<bar>"
    by linarith
  also have "\<bar>sum_upto (\<lambda>n. moebius_mu n * frac (x / n)) x\<bar> \<le>
               sum_upto (\<lambda>n. \<bar>moebius_mu n * frac (x / n)\<bar>) x"
    unfolding sum_upto_def by (rule sum_abs)
  also have "\<dots> \<le> sum_upto (\<lambda>n. frac (x / n)) x"
    unfolding sum_upto_def by (intro sum_mono) (auto simp: moebius_mu_def abs_mult)
  also have "\<dots> = (\<Sum>n\<in>{0<..nat \<lfloor>x\<rfloor>}. frac (x / n))"
    by (simp add: sum_upto_altdef)
  also have "{0<..nat \<lfloor>x\<rfloor>} = insert 1 {1<..nat \<lfloor>x\<rfloor>}"
    using x by (auto simp: le_nat_iff le_floor_iff)
  also have "(\<Sum>n\<in>\<dots>. frac (x / n)) = frac x + (\<Sum>n\<in>{1<..nat \<lfloor>x\<rfloor>}. frac (x / n))"
    by (subst sum.insert) auto
  also have "(\<Sum>n\<in>{1<..nat \<lfloor>x\<rfloor>}. frac (x / n)) < (\<Sum>n\<in>{1<..nat \<lfloor>x\<rfloor>}. 1)"
    using x by (intro sum_strict_mono frac_lt_1) auto
  also have "\<dots> = nat \<lfloor>x\<rfloor> - 1" by simp
  also have "1 + (frac x + real (nat \<lfloor>x\<rfloor> - 1)) = x"
    using x by (subst of_nat_diff) (auto simp: le_nat_iff le_floor_iff frac_def)
  finally have "x * \<bar>M x\<bar> < x * 1" by simp
  with x show "\<bar>M x\<bar> < 1"
    by (subst (asm) mult_less_cancel_left_pos) auto
qed 

lemma sum_upto_moebius_mu_over_n_eq:
  assumes "x < 2"
  shows   "M x = (if x \<ge> 1 then 1 else 0)"
proof (cases "x \<ge> 1")
  case True
  have "M x = (\<Sum>n\<in>{n. n > 0 \<and> real n \<le> x}. moebius_mu n / n)"
    by (simp add: M_def sum_upto_def)
  also from assms True have "{n. n > 0 \<and> real n \<le> x} = {1}"
    by auto
  thus ?thesis using True by (simp add: M_def sum_upto_def)
next
  case False
  have "M x = (\<Sum>n\<in>{n. n > 0 \<and> real n \<le> x}. moebius_mu n / n)"
    by (simp add: M_def sum_upto_def)
  also from False have "{n. n > 0 \<and> real n \<le> x} = {}"
    by auto
  finally show ?thesis using False by (simp add: M_def)
qed

lemma abs_sum_upto_moebius_mu_over_n_le: "\<bar>M x\<bar> \<le> 1"
  using sum_upto_moebius_mu_over_n_eq[of x] abs_sum_upto_moebius_mu_over_n_less[of x]
  by (cases "x < 2") auto

end

end
