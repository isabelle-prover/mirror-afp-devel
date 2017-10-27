(*
    File:      Dirichlet_Series.thy
    Author:    Manuel Eberl, TU München
*)
section \<open>Formal Dirichlet series\<close>
theory Dirichlet_Series
imports 
  Complex_Main
  Dirichlet_Product
  Multiplicative_Function
  "HOL-Computational_Algebra.Computational_Algebra"
  "HOL-Number_Theory.Number_Theory"
  "HOL-Library.FuncSet"
begin

text \<open>
  A formal Dirichlet series
    \[A(s) = \sum_{n=1}^\infty \frac{a_n}{n^s}\]
  is represented its coefficient sequence starting from 1. For simplicity, we represent this
  in Isabelle with a function of type @{typ "nat \<Rightarrow> 'a"} whose value for $n$ is the $n+1$-th 
  coefficient.
\<close>  
typedef 'a fds = "UNIV :: (nat \<Rightarrow> 'a) set"
  by simp

setup_lifting type_definition_fds

lift_definition fds_nth :: "'a fds \<Rightarrow> nat \<Rightarrow> 'a :: zero" is
  "\<lambda>f::nat \<Rightarrow> 'a. case_nat 0 f" .
    
lift_definition fds :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a fds" is
  "\<lambda>f. f \<circ> Suc" .
    
lemma fds_nth_fds: "fds_nth (fds f) n = (if n = 0 then 0 else f n)"
  by transfer (simp split: nat.splits)
    
lemma fds_nth_fds': "f 0 = 0 \<Longrightarrow> fds_nth (fds f) = f"
  by (simp add: fun_eq_iff fds_nth_fds)
    
lemma fds_nth_0 [simp]: "fds_nth f 0 = 0"
  by transfer simp
    
lemma fds_nth_fds_pos [simp]: "n > 0 \<Longrightarrow> fds_nth (fds f) n = f n"
  by transfer (simp split: nat.splits)
    
lemma fds_fds_nth [simp]: "fds (fds_nth f) = f"
  by transfer (simp add: fun_eq_iff split: nat.splits)
    
lemma fds_eq_fds_iff:
  "fds f = fds g \<longleftrightarrow> (\<forall>n>0. f n = g n)"
proof transfer
  fix f g :: "nat \<Rightarrow> 'a"
  have "(f \<circ> Suc = g \<circ> Suc) \<longleftrightarrow> (\<forall>n. f (Suc n) = g (Suc n))" by (auto simp: fun_eq_iff)
  also have "\<dots> \<longleftrightarrow> (\<forall>n>0. f n = g n)"
  proof safe
    fix n :: nat assume "\<forall>n. f (Suc n) = g (Suc n)" "n > 0"
    thus "f n = g n" by (cases n) auto
  qed auto
  finally show "(f \<circ> Suc = g \<circ> Suc) = (\<forall>n>0. f n = g n)" .
qed

lemma fds_eq_fds_iff': "f 0 = g 0 \<Longrightarrow> fds f = fds g \<longleftrightarrow> f = g"
proof safe
  assume "f 0 = g 0" "fds f = fds g"
  hence "f n = g n" for n by (cases n) (auto simp: fds_eq_fds_iff)
  thus "f = g" by (simp add: fun_eq_iff)
qed

lemma fds_eqI [intro?]:
  assumes "(\<And>n. n > 0 \<Longrightarrow> fds_nth f n = fds_nth g n)"
  shows   "f = g"
proof -
  from assms have "fds_nth f n = fds_nth g n" if "n > 0" for n 
    by (cases n) (simp_all add: fun_eq_iff)
  hence "fds (fds_nth f) = fds (fds_nth g)" by (subst fds_eq_fds_iff) auto
  thus ?thesis by simp
qed
  
lemma fds_cong [cong]: "(\<And>n. n > 0 \<Longrightarrow> f n = (g n :: 'a :: zero)) \<Longrightarrow> fds f = fds g"
  by (rule fds_eqI) simp

lemma fds_eq_iff: "f = g \<longleftrightarrow> (\<forall>n>0. fds_nth f n = fds_nth g n)"
  by (auto intro: fds_eqI)

lemma dirichlet_prod_fds_nth_fds_left [simp]:
  "dirichlet_prod (fds_nth (fds f)) g = dirichlet_prod f g"
  by (simp add: fds_nth_fds)
  
lemma dirichlet_prod_fds_nth_fds_right [simp]:
  "dirichlet_prod f (fds_nth (fds g)) = dirichlet_prod f g"
  by (simp add: fds_nth_fds)


definition fds_const :: "'a :: zero \<Rightarrow> 'a fds" where
  "fds_const c = fds (\<lambda>n. if n = 1 then c else 0)"
  
abbreviation fds_ind where "fds_ind P \<equiv> fds (ind P)"


bundle fds_syntax
begin
  
notation fds_nth (infixl "$" 75)
notation fds (binder "\<chi>" 10)
notation dirichlet_prod (infixl "\<star>" 70)
 
end

instantiation fds :: (zero) zero
begin
definition zero_fds :: "'a fds" where "zero_fds = fds (\<lambda>_. 0)"
instance ..
end

instantiation fds :: ("{zero,one}") one
begin
definition one_fds :: "'a fds" where "one_fds = fds (\<lambda>n. if n = 1 then 1 else 0)"
instance ..
end

instantiation fds :: ("{plus,zero}") plus
begin
definition plus_fds :: "'a fds \<Rightarrow> 'a fds \<Rightarrow> 'a fds" 
  where "plus_fds f g = fds (\<lambda>n. fds_nth f n + fds_nth g n)"
instance ..
end

instantiation fds :: (semiring_0) times
begin
definition times_fds :: "'a fds \<Rightarrow> 'a fds \<Rightarrow> 'a fds" 
  where "times_fds f g = fds (dirichlet_prod (fds_nth f) (fds_nth g))"
instance ..
end
  
instantiation fds :: ("{uminus,zero}") uminus
begin
definition uminus_fds :: "'a fds \<Rightarrow> 'a fds"
  where "uminus_fds f = fds (\<lambda>n. -fds_nth f n)"
instance ..
end
  
instantiation fds :: ("{minus,zero}") minus
begin
definition minus_fds :: "'a fds \<Rightarrow> 'a fds \<Rightarrow> 'a fds"
  where "minus_fds f g = fds (\<lambda>n. fds_nth f n - fds_nth g n)"
instance ..
end


subsection \<open>General properties\<close>
  
lemma fds_nth_zero [simp]: "fds_nth 0 = (\<lambda>_. 0)"
  by (simp add: zero_fds_def fds_nth_fds fun_eq_iff)  

lemma fds_nth_one: "fds_nth 1 = (\<lambda>n. if n = 1 then 1 else 0)"
  by (simp add: one_fds_def fds_nth_fds fun_eq_iff)

lemma fds_nth_one_Suc_0 [simp]: "fds_nth 1 (Suc 0) = 1"
  by (simp add: fds_nth_one)
    
lemma fds_nth_one_not_Suc_0 [simp]: "n \<noteq> Suc 0 \<Longrightarrow> fds_nth 1 n = 0"
  by (simp add: fds_nth_one)
    
lemma fds_nth_plus [simp]: 
  "fds_nth (f + g) = (\<lambda>n. fds_nth f n + fds_nth g n :: 'a :: monoid_add)"
  by (simp add: plus_fds_def fds_nth_fds fun_eq_iff)

lemma fds_nth_minus [simp]: 
  "fds_nth (f - g) = (\<lambda>n. fds_nth f n - fds_nth g n :: 'a :: {cancel_comm_monoid_add})"
  by (simp add: minus_fds_def fds_nth_fds fun_eq_iff)

lemma fds_nth_uminus [simp]: "fds_nth (-g) = (\<lambda>n. - fds_nth g n :: 'a :: group_add)"
  by (simp add: uminus_fds_def fds_nth_fds fun_eq_iff)

lemma fds_nth_times: "fds_nth (f * g) = dirichlet_prod (fds_nth f) (fds_nth g)"
  by (simp add: times_fds_def fds_nth_fds dirichlet_prod_def fun_eq_iff)

lemma fds_nth_times_const_left [simp]: "fds_nth (fds_const c * f) n = c * fds_nth f n"
  by (cases "n = 0") (simp_all add: fds_nth_times fds_const_def)

lemma fds_nth_times_const_right [simp]: "fds_nth (f * fds_const c) n = fds_nth f n * c"
  by (cases "n = 0") (simp_all add: fds_nth_times fds_const_def)


instance fds :: ("{semigroup_add, zero}") semigroup_add
  by standard (simp_all add: fds_eq_iff algebra_simps plus_fds_def)

instance fds :: ("{ab_semigroup_add, zero}") ab_semigroup_add
  by standard (simp_all add: fds_eq_iff algebra_simps plus_fds_def)

instance fds :: ("{cancel_semigroup_add, zero}") cancel_semigroup_add
  by standard (simp_all add: fds_eq_iff algebra_simps plus_fds_def)
    
instance fds :: ("{cancel_ab_semigroup_add, zero}") cancel_ab_semigroup_add
  by standard (simp_all add: fds_eq_iff algebra_simps plus_fds_def minus_fds_def)
  
instance fds :: (monoid_add) monoid_add
  by standard (simp_all add: fds_eq_iff algebra_simps)

instance fds :: (comm_monoid_add) comm_monoid_add
  by standard (simp_all add: fds_eq_iff algebra_simps)

instance fds :: (cancel_comm_monoid_add) cancel_comm_monoid_add
  by standard (simp_all add: fds_eq_iff algebra_simps)

instance fds :: (group_add) group_add
  by standard (simp_all add: fds_eq_iff algebra_simps minus_fds_def)

instance fds :: (ab_group_add) ab_group_add
  by standard (simp_all add: fds_eq_iff algebra_simps)

instance fds :: (semiring_0) semiring_0
proof
  fix f g h :: "'a fds"
  show "(f + g) * h = f * h + g * h"
    by (simp add: fds_eq_iff fds_nth_times dirichlet_prod_def algebra_simps sum.distrib)
next
  fix f g h :: "'a fds"
  show "f * g * h = f * (g * h)" 
    by (intro fds_eqI) (simp add: fds_nth_times dirichlet_prod_assoc)
qed (simp_all add: fds_eq_iff fds_nth_times dirichlet_prod_def algebra_simps sum.distrib)
  
instance fds :: (comm_semiring_0) comm_semiring_0
proof
  fix f g :: "'a fds"
  show "f * g = g * f"
    by (simp add: fds_eq_iff fds_nth_times dirichlet_prod_commutes)
qed (simp_all add: fds_eq_iff fds_nth_times dirichlet_prod_def algebra_simps sum.distrib)

instance fds :: (semiring_0_cancel) semiring_0_cancel
  by standard (simp_all add: fds_eq_iff fds_nth_one fds_nth_times)

instance fds :: (comm_semiring_0_cancel) comm_semiring_0_cancel ..

instance fds :: (semiring_1) semiring_1
  by standard (simp_all add: fds_eq_iff fds_nth_one fds_nth_times)
    
instance fds :: (comm_semiring_1) comm_semiring_1
  by standard (simp_all add: fds_eq_iff fds_nth_one fds_nth_times)

instance fds :: (semiring_1_cancel) semiring_1_cancel .. 
instance fds :: (ring) ring ..
instance fds :: (ring_1) ring_1 ..
instance fds :: (comm_ring) comm_ring ..

instance fds :: (semiring_no_zero_divisors) semiring_no_zero_divisors
proof
  fix f g :: "'a fds"
  assume "f \<noteq> 0" "g \<noteq> 0"
  hence ex: "\<exists>m>0. fds_nth f m \<noteq> 0" "\<exists>n>0. fds_nth g n \<noteq> 0"
    by (auto simp: fds_eq_iff)
  define m where "m = (LEAST m. m > 0 \<and> fds_nth f m \<noteq> 0)"
  define n where "n = (LEAST n. n > 0 \<and> fds_nth g n \<noteq> 0)"
  from ex[THEN LeastI_ex, folded m_def n_def]
    have mn: "m > 0" "fds_nth f m \<noteq> 0" "n > 0" "fds_nth g n \<noteq> 0" by auto

  have *: "m \<le> m'" if "m' > 0" "fds_nth f m' \<noteq> 0" for m' 
    using conjI[OF that] unfolding m_def by (rule Least_le)
  have m': "fds_nth f m' = 0" if "m' \<in> {0<..<m}"  for m' using that *[of m'] by auto
      
  have *: "n \<le> n'" if "n' > 0" "fds_nth g n' \<noteq> 0" for n' 
    using conjI[OF that] unfolding n_def by (rule Least_le)
  have n': "fds_nth g n' = 0" if "n' \<in> {0<..<n}"  for n' using that *[of n'] by auto
    
  have "fds_nth (f * g) (m * n) = 
          (\<Sum>d | d dvd m * n. fds_nth f d * fds_nth g (m * n div d))"
    by (simp add: fds_nth_times dirichlet_prod_def)
  also have "\<dots> = (\<Sum>d | d dvd m * n. if d = m then fds_nth f m * fds_nth g n else 0)"
  proof (intro sum.cong refl, goal_cases)
    case (1 d)
    thus ?case
    proof (cases "d \<le> m")
      case True
      with mn(1,3) 1 show ?thesis by (auto elim!: dvdE simp: m' n' split: if_splits)
    next
      case False
      from 1 obtain k where k: "m * n = d * k" by (auto elim!: dvdE)
      with mn(1,3) have [simp]: "k > 0" by (auto intro!: Nat.gr0I)
      from False mn(3) have "m * n < d * n" by (intro mult_strict_right_mono) auto
      also note k
      finally have "k < n" by (subst (asm) mult_less_cancel1) auto
      with mn(1,3) and 1 and False show ?thesis
        by (auto simp: k m' n' split: if_splits)
    qed
  qed
  also have "\<dots> = fds_nth f m * fds_nth g n" using mn(1,3) by (subst sum.delta) auto
  also have "\<dots> \<noteq> 0" using mn by auto
  finally show "f * g \<noteq> 0" by auto
qed
  
instance fds :: (ring_no_zero_divisors) ring_no_zero_divisors ..
instance fds :: (idom) idom ..

instantiation fds :: (real_vector) real_vector
begin

definition scaleR_fds :: "real \<Rightarrow> 'a fds \<Rightarrow> 'a fds" where
  "scaleR_fds c f = fds (\<lambda>n. c *\<^sub>R fds_nth f n)"
  
lemma fds_nth_scaleR [simp]: "fds_nth (c *\<^sub>R f) = (\<lambda>n. c *\<^sub>R fds_nth f n)"
  by (simp add: scaleR_fds_def fun_eq_iff fds_nth_fds)

instance by standard (simp_all add: fds_eq_iff algebra_simps)

end
  
instance fds :: (real_algebra) real_algebra
  by standard (simp_all add: fds_eq_iff algebra_simps fds_nth_times
                             dirichlet_prod_def scaleR_sum_right)

instance fds :: (real_algebra_1) real_algebra_1 ..

lemma fds_nth_const: "fds_nth (fds_const c) = (\<lambda>n. if n = 1 then c else 0)"
  by (simp add: fds_const_def fds_nth_fds fun_eq_iff)
    
lemma fds_nth_const_Suc_0 [simp]: "fds_nth (fds_const c) (Suc 0) = c"
  by (simp add: fds_nth_const)
    
lemma fds_nth_const_not_Suc_0 [simp]: "n \<noteq> 1 \<Longrightarrow> fds_nth (fds_const c) n = 0"
  by (simp add: fds_nth_const)

lemma fds_const_zero [simp]: "fds_const 0 = 0"
  by (simp add: fds_eq_iff fds_nth_const)

lemma fds_const_one [simp]: "fds_const 1 = 1"
  by (simp add: fds_eq_iff fds_nth_const fds_nth_one)

lemma fds_const_add [simp]: "fds_const (a + b :: 'a :: monoid_add) = fds_const a + fds_const b"
  by (simp add: fds_eq_iff fds_nth_const)
    
lemma fds_const_minus [simp]: 
  "fds_const (a - b :: 'a :: cancel_comm_monoid_add) = fds_const a - fds_const b"
  by (simp add: fds_eq_iff fds_nth_const)
    
lemma fds_const_uminus [simp]: 
  "fds_const (- b :: 'a :: ab_group_add) = - fds_const b"
  by (simp add: fds_eq_iff fds_nth_const)
    
lemma fds_const_mult [simp]: 
  "fds_const (a * b :: 'a :: semiring_0) = fds_const a * fds_const b"
  by (simp add: fds_eq_iff fds_nth_const fds_nth_times)
    
lemma fds_const_of_nat [simp]: "fds_const (of_nat c) = of_nat c"
  by (induction c) (simp_all)

lemma fds_const_of_int [simp]: "fds_const (of_int c) = of_int c"
  by (cases c) simp_all

lemma fds_const_of_real [simp]: "fds_const (of_real c) = of_real c"
  by (simp add: of_real_def fds_eq_iff fds_const_def fds_nth_one)


instantiation fds :: ("{inverse, comm_ring_1}") inverse
begin

definition inverse_fds :: "'a fds \<Rightarrow> 'a fds" where
  "inverse_fds f = fds (\<lambda>n. dirichlet_inverse (fds_nth f) (inverse (fds_nth f 1)) n)"

definition divide_fds :: "'a fds \<Rightarrow> 'a fds \<Rightarrow> 'a fds" where
  "divide_fds f g = f * inverse g"

instance ..

end

lemma fds_ind_False [simp]: "fds_ind (\<lambda>_. False) = 0"
  by (rule fds_eqI) simp

lemma fds_commutes: 
  assumes "\<And>m n. m > 0 \<Longrightarrow> n > 0 \<Longrightarrow> fds_nth f m * fds_nth g n = fds_nth g n * fds_nth f m"
  shows   "f * g = g * f"
  by (intro fds_eqI, unfold fds_nth_times, subst dirichlet_prod_def, 
      subst dirichlet_prod_altdef1, intro sum.cong refl assms) (auto elim: dvdE)

lemma fds_nth_times_Suc_0 [simp]: 
  "fds_nth (f * g) (Suc 0) = fds_nth f (Suc 0) * fds_nth g (Suc 0)"
  by (simp add: fds_nth_times)
  
lemma fds_nth_inverse: 
  "fds_nth (inverse f) = dirichlet_inverse (fds_nth f) (inverse (fds_nth f 1))"
  by (simp add: inverse_fds_def fds_nth_fds fun_eq_iff)

lemma inverse_fds_nonunit:
  "fds_nth f 1 = (0 :: 'a :: field) \<Longrightarrow> inverse f = 0"
  by (auto simp: fds_eq_iff fds_nth_inverse dirichlet_inverse_noninvertible)

lemma inverse_0_fds [simp]: "inverse (0 :: 'a :: field fds) = 0"
  by (simp add: inverse_fds_def fds_eq_iff dirichlet_inverse.simps)

lemma fds_left_inverse: 
  "fds_nth f 1 \<noteq> (0 :: 'a :: field) \<Longrightarrow> inverse f * f = 1"
  by (auto simp: fds_eq_iff fds_nth_times fds_nth_inverse dirichlet_prod_inverse' fds_nth_one)

lemma fds_right_inverse: 
  "fds_nth f 1 \<noteq> (0 :: 'a :: field) \<Longrightarrow> f * inverse f = 1"
  by (auto simp: fds_eq_iff fds_nth_times fds_nth_inverse dirichlet_prod_inverse fds_nth_one)
    
lemma fds_left_inverse_unique:
  assumes "f * g = (1 :: 'a :: field fds)"
  shows   "f = inverse g"
proof -
  have "fds_nth (f * g) 1 = 1" by (subst assms) simp
  hence "fds_nth g 1 \<noteq> 0" by auto
  hence "(f - inverse g) * g = 0" 
    unfolding ring_distribs by (subst fds_left_inverse) (simp_all add: assms)
  moreover from assms have "g \<noteq> 0" by auto
  ultimately show "f = inverse g" by simp
qed
  
lemma fds_right_inverse_unique:
  assumes "f * g = (1 :: 'a :: field fds)"
  shows   "g = inverse f"
  using fds_left_inverse_unique[of g f] assms by (simp add: mult.commute)

lemma inverse_1_fds [simp]: "inverse (1 :: 'a :: field fds) = 1"
  by (rule fds_left_inverse_unique [symmetric]) simp

lemma inverse_const_fds [simp]: 
  "inverse (fds_const c :: 'a :: field fds) = fds_const (inverse c)"
proof (cases "c = 0")
  case False
  thus ?thesis 
    by (intro fds_right_inverse_unique[symmetric])
       (auto simp del: fds_const_mult simp: fds_const_mult [symmetric])
qed auto

lemma inverse_mult_fds: "inverse (f * g :: 'a :: field fds) = inverse f * inverse g"
proof (cases "fds_nth (f * g) (Suc 0) = 0")
  case False
  hence "(f * inverse f) * (g * inverse g) = 1" by (subst (1 2) fds_right_inverse) auto
  thus ?thesis by (intro fds_right_inverse_unique [symmetric]) (simp_all add: mult_ac)
qed (auto simp: inverse_fds_nonunit)


definition fds_zeta :: "'a :: one fds" 
  where "fds_zeta = fds (\<lambda>_. 1)"
    
lemma fds_zeta_altdef: "fds_zeta = fds (\<lambda>n. if n = 0 then 0 else 1)"
  by (rule fds_eqI) (simp add: fds_zeta_def)
    
lemma fds_nth_zeta: "fds_nth fds_zeta = (\<lambda>n. if n = 0 then 0 else 1)"
  by (simp add: fds_zeta_def fun_eq_iff)

lemma fds_nth_zeta_pos [simp]: "n > 0 \<Longrightarrow> fds_nth fds_zeta n = 1"
  by (simp add: fds_nth_zeta) 

lemma fds_zeta_commutes: "fds_zeta * (f :: 'a :: semiring_1 fds) = f * fds_zeta"
  by (intro fds_commutes) simp_all

lemma fds_ind_True [simp]: "fds_ind (\<lambda>_. True) = fds_zeta"
  by (rule fds_eqI) simp

lemma finite_extensional_prod_nat: 
  assumes "finite A" "b > 0"
  shows   "finite {d \<in> extensional A. prod d A = (b :: nat)}"
proof (rule finite_subset)
  from assms(1) show "finite (PiE A (\<lambda>_. {..b}))" by (rule finite_PiE) auto
  {
    fix d :: "'a \<Rightarrow> nat" and x :: 'a assume *: "x \<in> A" "prod d A = b"
    with prod_dvd_prod_subset[of A "{x}" d] assms have "d x dvd b" by auto
    with assms have "d x \<le> b" by (auto dest: dvd_imp_le)
  }
  thus "{d \<in> extensional A. prod d A = (b :: nat)} \<subseteq> \<dots>"
    by (auto simp: extensional_def)
qed

text \<open>
  The $n$-th coefficient of a product of Dirichlet series can be determined by 
  summing over all products of $k_i$-th coefficients of the series such that the 
  product of the $k_i$ is $n$.
\<close>
lemma fds_nth_prod:
  assumes "finite A" "A \<noteq> {}" "n > 0"
  shows   "fds_nth (\<Prod>x\<in>A. f x) n = 
             (\<Sum>d | d \<in> extensional A \<and> prod d A = n. \<Prod>x\<in>A. fds_nth (f x) (d x))"
using assms
proof (induction arbitrary: n rule: finite_ne_induct)
  case (singleton x n)
  have "{d \<in> extensional {x}. d x = n} = {\<lambda>y. if y = x then n else undefined}"
    by (auto simp: extensional_def)
  thus ?case by simp
next
  case (insert x A n)
  let ?f = "\<lambda>d. ((d x, n div d x), d(x := undefined))"
  let ?g = "\<lambda>(z,d). d(x := fst z)"
  from insert have "fds_nth (\<Prod>x\<in>insert x A. f x) n = 
           (\<Sum>z | fst z * snd z = n. \<Sum>d | d \<in> extensional A \<and> prod d A = snd z. 
              fds_nth (f x) (fst z) * (\<Prod>x\<in>A. fds_nth (f x) (d x)))"
    by (simp add: fds_nth_times dirichlet_prod_altdef2 sum_distrib_left case_prod_unfold)
  also have "\<dots> = (\<Sum>(z,d)\<in>(SIGMA x:{z. fst z * snd z = n}. {d \<in> extensional A. prod d A = snd x}).
                      fds_nth (f x) (fst z) * (\<Prod>x\<in>A. fds_nth (f x) (d x)))"
    using finite_divisors_nat'[of n] and insert.hyps and \<open>n > 0\<close>
    by (intro sum.Sigma finite_extensional_prod_nat ballI)  (auto simp: case_prod_unfold)
  also have "\<dots> = (\<Sum>d | d \<in> extensional (insert x A) \<and> prod d (insert x A) = n.
                      (\<Prod>x\<in>insert x A. fds_nth (f x) (d x)))"
  proof (rule sum.reindex_bij_witness [of _ ?f ?g], goal_cases)
    case (1 z)
    thus ?case using insert.hyps insert.prems by (auto simp: extensional_def)
  next
    case (2 z)
    thus ?case using insert.hyps insert.prems 
      by (auto simp: extensional_def sum.delta intro!: prod.cong)
  next
    case (4 z)
    thus ?case using insert.hyps insert.prems by (auto  intro!: prod.cong)
  next
    case (5 z)
    with insert.hyps insert.prems 
      have "(\<Prod>xa\<in>A. fds_nth (f xa) (if xa = x then fst (fst z) else snd z xa)) =
              (\<Prod>x\<in>A. fds_nth (f x) (snd z x))" by (intro prod.cong) auto
    with 5 insert.hyps insert.prems show ?case by (simp add: case_prod_unfold)
  qed auto
  finally show ?case .
qed


subsection \<open>Shifting the argument\<close>

class nat_power = semiring_1 +
  fixes nat_power :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes nat_power_0_left [simp]:  "x \<noteq> 0 \<Longrightarrow> nat_power 0 x = 0"
  assumes nat_power_0_right [simp]: "n > 0 \<Longrightarrow> nat_power n 0 = 1"
  assumes nat_power_1_left [simp]:  "nat_power (Suc 0) x = 1"
  assumes nat_power_1_right [simp]: "nat_power n 1 = of_nat n"
  assumes nat_power_add:            "n > 0 \<Longrightarrow> nat_power n (a + b) = nat_power n a * nat_power n b"
  assumes nat_power_mult_distrib:   
    "m > 0 \<Longrightarrow> n > 0 \<Longrightarrow> nat_power (m * n) a = nat_power m a * nat_power n a"
  assumes nat_power_power:
    "n > 0 \<Longrightarrow> nat_power n (a * of_nat m) = nat_power n a ^ m"
begin

lemma nat_power_of_nat [simp]: "m > 0 \<Longrightarrow> nat_power m (of_nat n) = of_nat (m ^ n)"
  by (induction n) (simp_all add: nat_power_add)

lemma nat_power_power_left: "m > 0 \<Longrightarrow> nat_power (m ^ k) n = nat_power m n ^ k"
  by (induction k) (simp_all add: nat_power_mult_distrib)

end

class nat_power_field = nat_power + field +
  assumes nat_power_nonzero [simp]: "n > 0 \<Longrightarrow> nat_power n z \<noteq> 0"
begin

lemma nat_power_diff: "n > 0 \<Longrightarrow> nat_power n (a - b) = nat_power n a / nat_power n b"  
  using nat_power_add[of n "a - b" b] by (simp add: divide_simps)

end

instantiation nat :: nat_power
begin
definition [simp]: "nat_power_nat a b = (a ^ b :: nat)"
instance by standard (simp_all add: power_add power_mult_distrib power_mult)
end

instantiation real :: nat_power_field
begin
definition [simp]: "nat_power_real a b = (real a powr b)"
instance proof
  fix n m :: nat and a :: real assume "n > 0"
  thus "nat_power n (a * real m) = nat_power n a ^ m"
    by (simp add: powr_def exp_of_nat_mult [symmetric])
qed (simp_all add: powr_add powr_mult)
end

text \<open>
  The following operation corresponds to shifting the argument of a Dirichlet series, i.\,e.\ 
  subtracting a constant from it. In effect, this turns the series
    \[A(s) = \sum_{n=1}^\infty \frac{a_n}{n^s}\]
  into the series
    \[A(s - c) = \sum_{n=1}^\infty \frac{n^c \cdot a_n}{n^s}\ .\]
\<close>
definition fds_shift :: "'a :: nat_power \<Rightarrow> 'a fds \<Rightarrow> 'a fds" where
  "fds_shift c f = fds (\<lambda>n. fds_nth f n * nat_power n c)"

lemma fds_nth_shift [simp]: "fds_nth (fds_shift c f) n = fds_nth f n * nat_power n c"
  by (simp add: fds_shift_def fds_nth_fds)

lemma fds_shift_shift [simp]: "fds_shift c (fds_shift c' f) = fds_shift (c' + c) f"
  by (rule fds_eqI) (simp add: nat_power_add mult_ac)

lemma fds_shift_zero [simp]: "fds_shift c 0 = 0"
  by (rule fds_eqI) simp

lemma fds_shift_add [simp]: 
  fixes f g :: "'a :: {monoid_add, nat_power} fds"
  shows "fds_shift c (f + g) = fds_shift c f + fds_shift c g"
  by (rule fds_eqI) (simp add: algebra_simps)

lemma fds_shift_minus [simp]: 
  fixes f g :: "'a :: {comm_semiring_1_cancel, nat_power} fds"
  shows "fds_shift c (f - g) = fds_shift c f - fds_shift c g"
  by (rule fds_eqI) (simp add: algebra_simps)    

lemma fds_shift_uminus [simp]: 
  fixes f :: "'a :: {ring, nat_power} fds"
  shows "fds_shift c (-f) = -fds_shift c f"
  by (rule fds_eqI) (simp add: algebra_simps)

lemma fds_shift_mult [simp]:
  fixes f g :: "'a :: {comm_semiring, nat_power} fds"
  shows "fds_shift c (f * g) = fds_shift c f * fds_shift c g"
  by (rule fds_eqI) 
     (auto simp: algebra_simps fds_nth_times dirichlet_prod_altdef2 
        sum_distrib_left sum_distrib_right nat_power_mult_distrib intro!: sum.cong)


subsection \<open>Scaling the argument\<close>

text \<open>
  The following operation corresponds to scaling the argument of a Dirichlet series with 
  a natural number, i.\,e.\ turning the series
    \[A(s) = \sum_{n=1}^\infty \frac{a_n}{n^s}\]
  into the series
    \[A(ks) = \sum_{n=1}^\infty \frac{a_n}{\left(n^k\right)^2}\ .\]
\<close>
definition fds_scale :: "nat \<Rightarrow> ('a :: zero) fds \<Rightarrow> 'a fds" where
  "fds_scale c f =
     fds (\<lambda>n. if n > 0 \<and> is_nth_power c n then fds_nth f (nth_root_nat c n) else 0)"

lemma fds_scale_0 [simp]: "fds_scale 0 f = 0"
  by (auto simp: fds_scale_def fds_eq_iff)  

lemma fds_scale_1 [simp]: "fds_scale 1 f = f"
  by (auto simp: fds_scale_def fds_eq_iff)
    
lemma fds_nth_scale_power [simp]:
  "c > 0 \<Longrightarrow> fds_nth (fds_scale c f) (n ^ c) = fds_nth f n"
  by (simp add: fds_scale_def fds_nth_fds)
    
lemma fds_nth_scale_nonpower [simp]:
  "\<not>is_nth_power c n \<Longrightarrow>  fds_nth (fds_scale c f) n = 0"
  by (simp add: fds_scale_def fds_nth_fds)

lemma fds_nth_scale:
  "fds_nth (fds_scale c f) n = 
     (if n > 0 \<and> is_nth_power c n then fds_nth f (nth_root_nat c n) else 0)"
  by (cases "c = 0") (auto simp: is_nth_power_def)

lemma fds_scale_const [simp]: "c > 0 \<Longrightarrow> fds_scale c (fds_const c') = fds_const c'"
  by (rule fds_eqI) (auto simp: fds_nth_scale fds_nth_const elim!: is_nth_powerE)

lemma fds_scale_zero [simp]: "fds_scale c 0 = 0"
  by (rule fds_eqI) (simp add: fds_nth_scale)

lemma fds_scale_one [simp]: "c > 0 \<Longrightarrow> fds_scale c 1 = 1"
  by (simp only: fds_const_one [symmetric] fds_scale_const)

lemma fds_scale_of_nat [simp]: "c > 0 \<Longrightarrow> fds_scale c (of_nat n) = of_nat n"
  by (simp only: fds_const_of_nat [symmetric] fds_scale_const)

lemma fds_scale_of_int [simp]: "c > 0 \<Longrightarrow> fds_scale c (of_int n) = of_int n"
  by (simp only: fds_const_of_int [symmetric] fds_scale_const)

lemma fds_scale_numeral [simp]: "c > 0 \<Longrightarrow> fds_scale c (numeral n) = numeral n"
  using fds_scale_of_nat[of c "numeral n"] by (simp del: fds_scale_of_nat)

lemma fds_scale_scale: "fds_scale c (fds_scale c' f) = fds_scale (c * c') f"
proof (cases "c = 0 \<or> c' = 0")
  case False
  hence cc': "c > 0" "c' > 0" by auto
  show ?thesis
  proof (rule fds_eqI, goal_cases)
    case (1 n)
    show ?case
    proof (cases "is_nth_power (c * c') n")
      case False
      with cc' 1 have "fds_nth (fds_scale c (fds_scale c' f)) n = 0"
        by (auto simp: fds_nth_scale is_nth_power_def power_mult [symmetric] mult.commute)
      with False cc' show ?thesis by simp
    next
      case True
      from True obtain n' where [simp]: "n = n' ^ (c' * c)" 
        by (auto elim: is_nth_powerE simp: mult.commute)
      with cc' have "fds_nth (fds_scale (c * c') f) n = fds_nth f n'"
        by (simp add: mult.commute)
      also have "\<dots> = fds_nth (fds_scale c (fds_scale c' f)) n"
        using cc' by (simp add: power_mult)
      finally show ?thesis ..
    qed
  qed
qed auto
          
lemma fds_scale_add [simp]: 
  fixes f g :: "'a :: monoid_add fds"
  shows "fds_scale c (f + g) = fds_scale c f + fds_scale c g"
  by (rule fds_eqI) (auto simp: fds_nth_scale)

lemma fds_scale_minus [simp]: 
  fixes f g :: "'a :: {cancel_comm_monoid_add} fds"
  shows "fds_scale c (f - g) = fds_scale c f - fds_scale c g"
  by (rule fds_eqI) (auto simp: fds_nth_scale)

lemma fds_scale_uminus [simp]: 
  fixes f :: "'a :: group_add fds"
  shows "fds_scale c (-f) = -fds_scale c f"
  by (rule fds_eqI) (auto simp: fds_nth_scale)

lemma fds_scale_mult [simp]: 
  fixes f g :: "'a :: semiring_0 fds"
  shows "fds_scale c (f * g) = fds_scale c f * fds_scale c g"
proof (cases "c > 0")
  case True
  show ?thesis
  proof (rule fds_eqI, goal_cases)
    case (1 n)
    show ?case
    proof (cases "is_nth_power c n")
      case False
      have "fds_nth (fds_scale c f * fds_scale c g) n = 
              (\<Sum>(r, d) | r * d = n. fds_nth (fds_scale c f) r * fds_nth (fds_scale c g) d)"
        by (simp add: fds_nth_times dirichlet_prod_altdef2)
      also from False have "\<dots> = (\<Sum>(r, d) | r * d = n. 0)"
        by (intro sum.cong refl) (auto simp: fds_nth_scale dest: is_nth_power_mult)
      also from False have "\<dots> = fds_nth (fds_scale c (f * g)) n" by simp
      finally show ?thesis ..
    next
      case True
      then obtain n' where [simp]: "n = n' ^ c" by (elim is_nth_powerE)
      define h where "h = map_prod (nth_root_nat c) (nth_root_nat c)"
      define i where "i = map_prod (\<lambda>n::nat. n ^ c) (\<lambda>n::nat. n ^ c)"
      define A where "A = {(r, d). r * d = n}"
      define S where "S = {rs\<in>A. \<not>is_nth_power c (fst rs) \<or> \<not>is_nth_power c (snd rs)}"

      have "fds_nth (fds_scale c f * fds_scale c g) n = 
              (\<Sum>(r, d) | r * d = n. fds_nth (fds_scale c f) r * fds_nth (fds_scale c g) d)"
        by (simp add: fds_nth_times dirichlet_prod_altdef2)
      also have "\<dots> = (\<Sum>(r, d) | r * d = n'. fds_nth f r * fds_nth g d)"
      proof (rule sym, intro sum.reindex_bij_witness_not_neutral[of "{}" S _ h i])
        show "finite S" unfolding S_def A_def
          by (rule finite_subset[OF _ finite_divisors_nat'[of n]]) (insert \<open>n > 0\<close>, auto)
        show "i (h rd) = rd" if "rd \<in> {(r, d). r * d = n} - S" for rd
          using \<open>c > 0\<close> that by (auto elim!: is_nth_powerE simp: S_def i_def h_def A_def)
        show "h rd \<in> {(r,d). r * d = n'} - {}" if "rd \<in> {(r, d). r * d = n} - S" for rd
          using \<open>c > 0\<close> that  by (auto elim!: is_nth_powerE 
            simp: S_def i_def h_def A_def power_mult_distrib [symmetric] power_eq_iff_eq_base)
        show "h (i rd) = rd" if "rd \<in> {(r, d). r * d = n'} - {}" for rd
          using that \<open>c > 0\<close> by (auto simp: h_def i_def)
        show "i rd \<in> {(r, d). r * d = n} - S" if "rd \<in> {(r,d). r * d = n'} - {}" for rd
          using that \<open>c > 0\<close> by (auto simp: i_def S_def power_mult_distrib [symmetric])
        show "(case rd of (r, d) \<Rightarrow> fds_nth (fds_scale c f) r * fds_nth (fds_scale c g) d) = 0"
          if "rd \<in> S" for rd using that by (auto simp: S_def case_prod_unfold)
      qed (insert \<open>c > 0\<close>, auto simp: case_prod_unfold i_def)
      also have "\<dots> = fds_nth (f * g) n'" by (simp add: fds_nth_times dirichlet_prod_altdef2)
      also from \<open>c > 0\<close> have "\<dots> = fds_nth (fds_scale c (f * g)) n" by simp
      finally show ?thesis ..
    qed
  qed
qed auto

lemma fds_scale_shift: 
  "fds_shift d (fds_scale c f) = fds_scale c (fds_shift (c * d) f)"
proof (cases "c > 0")
  case True
  thus ?thesis
  by (intro fds_eqI) (auto simp: fds_nth_scale power_mult elim!: is_nth_powerE)
qed auto

lemma fds_ind_nth_power: "k > 0 \<Longrightarrow> fds_ind (is_nth_power k) = fds_scale k fds_zeta"
  by (rule fds_eqI) (auto simp: ind_def fds_nth_scale elim!: is_nth_powerE)


subsection \<open>Formal derivative\<close>

text \<open>
  The formal derivative of a series
    \[A(s) = \sum_{n=1}^\infty \frac{a_n}{n^s}\]
  can easily be seen to be
    \[A'(s) = -\sum_{n=1}^\infty \frac{\ln n\cdot a_n}{n^s}\ .\]
\<close>
definition fds_deriv :: "'a :: real_algebra fds \<Rightarrow> 'a fds" where
  "fds_deriv f = fds (\<lambda>n. - ln (real n) *\<^sub>R fds_nth f n)"

lemma fds_nth_deriv: "fds_nth (fds_deriv f) n = -ln (real n) *\<^sub>R fds_nth f n"
  by (cases "n = 0") (simp_all add: fds_deriv_def)

lemma fds_deriv_const [simp]: "fds_deriv (fds_const c) = 0"
  by (rule fds_eqI) (simp add: fds_nth_deriv fds_nth_const)

lemma fds_deriv_0 [simp]: "fds_deriv 0 = 0"
  by (rule fds_eqI) (simp add: fds_nth_deriv)
    
lemma fds_deriv_1 [simp]: "fds_deriv 1 = 0"
  by (rule fds_eqI) (simp add: fds_nth_deriv fds_nth_one)

lemma fds_deriv_of_nat [simp]: "fds_deriv (of_nat n) = 0"
  by (simp only: fds_const_of_nat [symmetric] fds_deriv_const)
    
lemma fds_deriv_of_int [simp]: "fds_deriv (of_int n) = 0"
  by (simp only: fds_const_of_int [symmetric] fds_deriv_const)
    
lemma fds_deriv_of_real [simp]: "fds_deriv (of_real n) = 0"
  by (simp only: fds_const_of_real [symmetric] fds_deriv_const)

lemma fds_deriv_uminus [simp]: "fds_deriv (-f) = -fds_deriv f"
  by (rule fds_eqI) (simp add: fds_nth_deriv)

lemma fds_deriv_add [simp]: "fds_deriv (f + g) = fds_deriv f + fds_deriv g"
  by (rule fds_eqI) (simp add: fds_nth_deriv algebra_simps)

lemma fds_deriv_minus [simp]: "fds_deriv (f - g) = fds_deriv f - fds_deriv g"
  by (rule fds_eqI) (simp add: fds_nth_deriv algebra_simps)

lemma fds_deriv_times [simp]: 
  "fds_deriv (f * g) = fds_deriv f * g + f * fds_deriv g"
  by (rule fds_eqI) 
     (auto simp add: fds_nth_deriv fds_nth_times dirichlet_prod_altdef2 scaleR_right.sum 
        algebra_simps sum.distrib [symmetric] ln_mult intro!: sum.cong)

lemma fds_deriv_inverse [simp]:
  fixes f :: "'a :: {real_algebra, field} fds"
  assumes "fds_nth f (Suc 0) \<noteq> 0"
  shows   "fds_deriv (inverse f) = -fds_deriv f / f ^ 2"
proof -
  have "(0 :: 'a fds) = fds_deriv 1" by simp
  also from assms have "(1 :: 'a fds) = inverse f * f" by (simp add: fds_left_inverse)
  also have "fds_deriv \<dots> = fds_deriv (inverse f) * f + inverse f * fds_deriv f" by simp
  also have "\<dots> * inverse f = fds_deriv (inverse f) * (f * inverse f) + 
                                inverse f ^ 2 * fds_deriv f" 
    by (simp add: algebra_simps power2_eq_square)
  also from assms have "f * inverse f = 1" by (simp add: fds_right_inverse)
  finally show ?thesis
    by (simp add: algebra_simps power2_eq_square divide_fds_def inverse_mult_fds add_eq_0_iff)
qed

lemma fds_deriv_shift [simp]: "fds_deriv (fds_shift c f) = fds_shift c (fds_deriv f)"
  by (rule fds_eqI) (simp add: fds_nth_deriv algebra_simps)

lemma fds_deriv_scale: "fds_deriv (fds_scale c f) = of_nat c * fds_scale c (fds_deriv f)"
proof (cases "c > 0")
  case True
  have *: "of_nat a * (b :: 'a) = real a *\<^sub>R b" for a b
    by (induction a) (simp_all add: algebra_simps)
  from True show ?thesis
    by (intro fds_eqI)
       (auto simp: fds_nth_deriv fds_nth_scale is_nth_powerE fds_const_of_nat [symmetric]
                ln_realpow * simp del: fds_const_of_nat elim!: is_nth_powerE)
qed auto


lemma completely_multiplicative_fds_deriv:
  assumes "completely_multiplicative_function f"
  shows   "fds_deriv (fds f) = -fds (\<lambda>n. f n * mangoldt n) * fds f"
proof (rule fds_eqI, goal_cases)
  case (1 n)
  interpret completely_multiplicative_function f by fact
  have "fds_nth (-fds (\<lambda>n. f n * mangoldt n) * fds f) n = 
          -(\<Sum>(r, d) | r * d = n. f r * mangoldt r * f d)"
    by (simp add: fds_nth_times fds_nth_deriv dirichlet_prod_altdef2)
  also have "(\<Sum>(r, d) | r * d = n. f r * mangoldt r * f d) =
               (\<Sum>(r, d) | r * d = n. mangoldt r * f n)"
    using 1 by (intro sum.mono_neutral_cong_right refl) 
               (auto simp: mangoldt_def mult mult_ac intro!: finite_divisors_nat' split: if_splits)
  also have "\<dots> = (\<Sum>r | r dvd n. mangoldt r * f n)" using 1
    by (intro sum.reindex_bij_witness[of _ "\<lambda>r. (r, n div r)" fst]) auto
  also have "\<dots> = (\<Sum>r | r dvd n. mangoldt r) * f n" (is "_ = ?S * _")
    by (subst sum_distrib_right [symmetric]) simp
  also have "(\<Sum>r | r dvd n. mangoldt r) = of_real (ln (real n))"
    using 1 by (intro mangoldt_sum) simp
  also have "- (of_real (ln (real n)) * f n) = fds_nth (fds_deriv (fds f)) n"
    using 1 by (simp add: fds_nth_deriv scaleR_conv_of_real)
  finally show ?case ..
qed
  
lemma fds_deriv_zeta: 
  "fds_deriv fds_zeta = 
     -fds mangoldt * (fds_zeta :: 'a :: {comm_semiring_1,real_algebra_1} fds)"
proof -
  have "completely_multiplicative_function (\<lambda>n. if n = 0 then 0 else 1)"
    by standard simp_all
  from completely_multiplicative_fds_deriv [OF this, folded fds_zeta_altdef]
    show ?thesis by simp
qed

lemma fds_mangoldt_times_zeta: "fds mangoldt * fds_zeta = fds (\<lambda>x. of_real (ln (real x)))"
  by (rule fds_eqI) (simp add: fds_nth_times dirichlet_prod_def mangoldt_sum)
    
lemma fds_deriv_zeta': "fds_deriv fds_zeta = 
    -fds (\<lambda>x. of_real (ln (real x)):: 'a :: {comm_semiring_1,real_algebra_1})"
  by (simp add: fds_deriv_zeta fds_mangoldt_times_zeta)


subsection \<open>Convergence and connection to concrete functions\<close>

text \<open>
  The following definitions establish a connection of a formal Dirichlet series to 
  the concrete analytic function that it corresponds to. This correspondence is usually 
  partial in the sense that a series may not converge everywhere.
\<close>
definition eval_fds :: "('a :: {nat_power, real_normed_field, banach}) fds \<Rightarrow> 'a \<Rightarrow> 'a" where
  "eval_fds f s = (\<Sum>n. fds_nth f n / nat_power n s)"

lemma eval_fds_eqI:
  assumes "(\<lambda>n. fds_nth f (Suc n) / nat_power (Suc n) s) sums L"
  shows   "eval_fds f s = L"
proof -
  from assms have "(\<lambda>n. fds_nth f n / nat_power n s) sums L"
    by (subst (asm) sums_Suc_iff) auto
  thus ?thesis by (simp add: eval_fds_def sums_iff)
qed

definition fds_converges :: 
    "('a :: {nat_power, real_normed_field, banach}) fds \<Rightarrow> 'a \<Rightarrow> bool" where
  "fds_converges f s \<longleftrightarrow> summable (\<lambda>n. fds_nth f n / nat_power n s)"

lemma fds_converges_iff: 
  "fds_converges f s \<longleftrightarrow> (\<lambda>n. fds_nth f n / nat_power n s) sums eval_fds f s"
  by (simp add: fds_converges_def sums_iff eval_fds_def)

definition fds_abs_converges :: 
    "('a :: {nat_power, real_normed_field, banach}) fds \<Rightarrow> 'a \<Rightarrow> bool" where
  "fds_abs_converges f s \<longleftrightarrow> summable (\<lambda>n. norm (fds_nth f n / nat_power n s))"
  
lemma fds_abs_converges_imp_converges [dest, intro]: 
  "fds_abs_converges f s \<Longrightarrow> fds_converges f s"
  unfolding fds_abs_converges_def fds_converges_def by (rule summable_norm_cancel)

lemma fds_converges_altdef: 
  "fds_converges f s \<longleftrightarrow> (\<lambda>n. fds_nth f (Suc n) / nat_power (Suc n) s) sums eval_fds f s"
  unfolding fds_converges_def summable_sums_iff
  by (subst sums_Suc_iff) (simp_all add: eval_fds_def)

lemma fds_const_abs_converges [simp]: "fds_abs_converges (fds_const c) s"
proof -
  have "summable (\<lambda>n. norm (fds_nth (fds_const c) n / nat_power n s)) \<longleftrightarrow> 
          summable (\<lambda>n. if n = 1 then norm c else (0 :: real))"
    by (intro summable_cong) simp
  also have \<dots> by simp
  finally show ?thesis by (simp add: fds_abs_converges_def)
qed

lemma fds_const_converges [simp]: "fds_converges (fds_const c) s"
  by (rule fds_abs_converges_imp_converges) simp

lemma eval_fds_const [simp]: "eval_fds (fds_const c) = (\<lambda>_. c)"
proof
  fix s
  have "eval_fds (fds_const c) s = (\<Sum>n. if n = 1 then c else 0)" unfolding eval_fds_def
    by (intro suminf_cong) simp
  also have "\<dots> = c" using sums_single[of 1 "\<lambda>_. c"] by (simp add: sums_iff)
  finally show "eval_fds (fds_const c) s = c" .
qed
          
lemma fds_zero_abs_converges [simp]: "fds_abs_converges 0 s"
  by (simp add: fds_abs_converges_def)

lemma fds_zero_converges [simp]: "fds_converges 0 s"
  by (simp add: fds_converges_def)

lemma eval_fds_zero [simp]: "eval_fds 0 = (\<lambda>_. 0)"
  by (simp only: fds_const_zero [symmetric] eval_fds_const)

lemma fds_one_abs_converges [simp]: "fds_abs_converges 1 s"
  by (simp only: fds_const_one [symmetric] fds_const_abs_converges)

lemma fds_one_converges [simp]: "fds_converges 1 s"
  by (simp only: fds_const_one [symmetric] fds_const_converges)

lemma eval_fds_one [simp]: "eval_fds 1 = (\<lambda>_. 1)"
  by (simp only: fds_const_one [symmetric] eval_fds_const)


lemma fds_converges_add: 
  assumes "fds_converges f s" "fds_converges g s"
  shows   "fds_converges (f + g) s"
  using summable_add[OF assms[unfolded fds_converges_def]] 
  by (simp add: fds_converges_def add_divide_distrib)

lemma fds_abs_converges_add: 
  assumes "fds_abs_converges f s" "fds_abs_converges g s"
  shows   "fds_abs_converges (f + g) s"
  unfolding fds_abs_converges_def
proof (rule summable_comparison_test, intro exI allI impI)
  let ?A = "(\<lambda>n. norm (fds_nth f n / nat_power n s) + norm (fds_nth g n / nat_power n s))"
  from summable_add[OF assms[unfolded fds_abs_converges_def]] show "summable ?A" .
  fix n :: nat
  show "norm (norm (fds_nth (f + g) n / nat_power n s)) \<le> ?A n"
    by (simp add: norm_triangle_ineq add_divide_distrib)
qed

lemma eval_fds_add: 
  assumes "fds_converges f s" "fds_converges g s"
  shows   "eval_fds (f + g) s = eval_fds f s + eval_fds g s"
proof -
  from assms have "(\<lambda>n. fds_nth f n / nat_power n s) sums eval_fds f s"
                  "(\<lambda>n. fds_nth g n / nat_power n s) sums eval_fds g s"
    by (simp_all add: fds_converges_def sums_iff eval_fds_def)
  from sums_add[OF this] show ?thesis by (simp add: eval_fds_def sums_iff add_divide_distrib)
qed


lemma fds_converges_uminus: 
  assumes "fds_converges f s"
  shows   "fds_converges (-f) s"
  using summable_minus[OF assms[unfolded fds_converges_def]] 
  by (simp add: fds_converges_def add_divide_distrib)

lemma The_cong: "The P = The Q" if "\<And>x. P x \<longleftrightarrow> Q x"
proof -
  from that have "P = Q" by auto
  thus ?thesis by simp
qed

lemma fds_abs_converges_uminus: 
  assumes "fds_abs_converges f s"
  shows   "fds_abs_converges (-f) s"
  using assms by (simp add: fds_abs_converges_def)

lemma eval_fds_uminus: "fds_converges f s \<Longrightarrow> eval_fds (-f) s = -eval_fds f s"
  by (simp add: fds_converges_def eval_fds_def suminf_minus)


lemma fds_converges_diff: 
  assumes "fds_converges f s" "fds_converges g s"
  shows   "fds_converges (f - g) s"
  using summable_diff[OF assms[unfolded fds_converges_def]] 
  by (simp add: fds_converges_def diff_divide_distrib)

lemma fds_abs_converges_diff: 
  assumes "fds_abs_converges f s" "fds_abs_converges g s"
  shows   "fds_abs_converges (f - g) s"
  unfolding fds_abs_converges_def
proof (rule summable_comparison_test, intro exI allI impI)
  let ?A = "(\<lambda>n. norm (fds_nth f n / nat_power n s) + norm (fds_nth g n / nat_power n s))"
  from summable_add[OF assms[unfolded fds_abs_converges_def]] show "summable ?A" .
  fix n :: nat
  show "norm (norm (fds_nth (f - g) n / nat_power n s)) \<le> ?A n"
    by (simp add: norm_triangle_ineq4 diff_divide_distrib) 
qed

lemma eval_fds_diff: 
  assumes "fds_converges f s" "fds_converges g s"
  shows   "eval_fds (f - g) s = eval_fds f s - eval_fds g s"
proof -
  from assms have "(\<lambda>n. fds_nth f n / nat_power n s) sums eval_fds f s"
                  "(\<lambda>n. fds_nth g n / nat_power n s) sums eval_fds g s"
    by (simp_all add: fds_converges_def sums_iff eval_fds_def)
  from sums_diff[OF this] show ?thesis by (simp add: eval_fds_def sums_iff diff_divide_distrib)
qed


lemma eval_fds_at_nat: "eval_fds f (of_nat k) = (\<Sum>n. fds_nth f n / of_nat n ^ k)"
  unfolding eval_fds_def
proof (intro suminf_cong, goal_cases)
  case (1 n)
  thus ?case by (cases "n = 0") simp_all
qed

lemma eval_fds_at_numeral: "eval_fds f (numeral k) = (\<Sum>n. fds_nth f n / of_nat n ^ numeral k)"
  using eval_fds_at_nat[of f "numeral k"] by simp

lemma eval_fds_at_1: "eval_fds f 1 = (\<Sum>n. fds_nth f n / of_nat n)"
  using eval_fds_at_nat[of f 1] by simp
    
lemma eval_fds_at_0: "eval_fds f 0 = (\<Sum>n. fds_nth f n)"
  using eval_fds_at_nat[of f 0] by simp

lemma suminf_fds_zeta_aux: 
  "f 0 = 0 \<Longrightarrow> (\<Sum>n. fds_nth fds_zeta n / f n) = (\<Sum>n. 1 / f n :: 'a :: real_normed_field)"
  by (intro suminf_cong) (auto simp: fds_nth_zeta)


lemma fds_converges_shift [simp]:
  fixes z :: "'a :: {banach, nat_power_field, real_normed_field}"
  shows "fds_converges (fds_shift c f) z \<longleftrightarrow> fds_converges f (z - c)"
  unfolding fds_converges_def
  by (intro summable_cong) 
     (auto intro: eventually_mono [OF eventually_gt_at_top[of "0::nat"]] simp: nat_power_diff)

lemma fds_abs_converges_shift [simp]:
  fixes z :: "'a :: {banach, nat_power_field, real_normed_field}"
  shows "fds_abs_converges (fds_shift c f) z \<longleftrightarrow> fds_abs_converges f (z - c)"
  unfolding fds_abs_converges_def
  by (intro summable_cong) 
     (auto intro: eventually_mono [OF eventually_gt_at_top[of "0::nat"]] simp: nat_power_diff)

lemma fds_eval_shift [simp]:
  fixes z :: "'a :: {banach, nat_power_field, real_normed_field}"
  shows "eval_fds (fds_shift c f) z = eval_fds f (z - c)"
  unfolding eval_fds_def
proof (rule suminf_cong, goal_cases)
  case (1 n)
  show ?case by (cases "n = 0") (simp_all add: nat_power_diff)
qed


lemma fds_converges_scale [simp]:
  fixes z :: "'a :: {banach, nat_power_field, real_normed_field}"
  assumes c: "c > 0"
  shows   "fds_converges (fds_scale c f) z \<longleftrightarrow> fds_converges f (of_nat c * z)"
proof -
  have "fds_converges (fds_scale c f) z \<longleftrightarrow> 
          summable (\<lambda>n. fds_nth (fds_scale c f) (n ^ c) / nat_power (n ^ c) z)" 
    (is "_ = summable ?g") unfolding fds_converges_def
    by (rule summable_mono_reindex [symmetric])
       (insert c, auto simp: fds_nth_scale is_nth_power_def strict_mono_def power_strict_mono)
  also have "?g = (\<lambda>n. fds_nth f n / nat_power n (of_nat c * z))"
  proof (intro ext, goal_cases)
    case (1 n)
    thus ?case using c
      by (cases "n = 0") (simp_all add: nat_power_power_left nat_power_power [symmetric] mult_ac)
  qed
  finally show ?thesis by (simp add: fds_converges_def)
qed

lemma fds_abs_converges_scale [simp]:
  fixes z :: "'a :: {banach, nat_power_field, real_normed_field}"
  assumes c: "c > 0"
  shows   "fds_abs_converges (fds_scale c f) z \<longleftrightarrow> fds_abs_converges f (of_nat c * z)"
proof -
  have "fds_abs_converges (fds_scale c f) z \<longleftrightarrow> 
          summable (\<lambda>n. norm (fds_nth (fds_scale c f) (n ^ c) / nat_power (n ^ c) z))" 
    (is "_ = summable ?g") unfolding fds_abs_converges_def
    by (rule summable_mono_reindex [symmetric])
       (insert c, auto simp: fds_nth_scale is_nth_power_def strict_mono_def power_strict_mono)
  also have "?g = (\<lambda>n. norm (fds_nth f n / nat_power n (of_nat c * z)))"
  proof (intro ext, goal_cases)
    case (1 n)
    thus ?case using c
      by (cases "n = 0") (simp_all add: nat_power_power_left nat_power_power [symmetric] mult_ac)
  qed
  finally show ?thesis by (simp add: fds_abs_converges_def)
qed

lemma eval_fds_scale [simp]:
  fixes z :: "'a :: {banach, nat_power_field, real_normed_field}"
  assumes c: "c > 0"
  shows   "eval_fds (fds_scale c f) z = eval_fds f (of_nat c * z)"
proof -
  have "eval_fds (fds_scale c f) z = 
          (\<Sum>n. fds_nth (fds_scale c f) (n ^ c) / nat_power (n ^ c) z)"
    unfolding eval_fds_def
    by (rule suminf_mono_reindex [symmetric])
       (insert c, auto simp: fds_nth_scale is_nth_power_def strict_mono_def power_strict_mono)
  also have "\<dots> = (\<Sum>n. fds_nth f n / nat_power n (of_nat c * z))"
  proof (intro suminf_cong, goal_cases)
    case (1 n)
    thus ?case using c
      by (cases "n = 0") (simp_all add: nat_power_power_left nat_power_power [symmetric] mult_ac)
  qed
  finally show ?thesis by (simp add: eval_fds_def)
qed


(* TODO: evaluating deriv, etc. *)

end
