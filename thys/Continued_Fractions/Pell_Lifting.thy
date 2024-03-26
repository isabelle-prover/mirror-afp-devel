(*
  File:     Continued_Fractions/Pell_Lifting.thy
  Author:   Manuel Eberl, University of Innsbruck
*)
section \<open>Lifting solutions of Pell's Equation\<close>
theory Pell_Lifting
  imports Pell.Pell Pell.Pell_Algorithm
begin

subsection \<open>Auxiliary material\<close>

(* TODO Move *)
lemma (in pell) snth_pell_solutions: "snth (pell_solutions D) n = nth_solution n"
  by (simp add: pell_solutions_def Let_def find_fund_sol_correct nonsquare_D nth_solution_def
                pell_power_def pell_mul_commutes[of _ fund_sol])

definition square_squarefree_part_nat :: "nat \<Rightarrow> nat \<times> nat" where
  "square_squarefree_part_nat n = (square_part n, squarefree_part n)"

lemma prime_factorization_squarefree_part:
  assumes "x \<noteq> 0"
  shows   "prime_factorization (squarefree_part x) =
             mset_set {p \<in> prime_factors x. odd (multiplicity p x)}" (is "?lhs = ?rhs")
proof (rule multiset_eqI)
  fix p show "count ?lhs p = count ?rhs p"
  proof (cases "prime p")
    case False
    thus ?thesis by (auto simp: count_prime_factorization)
  next
    case True
    have "finite (prime_factors x)" by simp
    hence "finite {p. p dvd x \<and> prime p}" using assms 
      by (subst (asm) prime_factors_dvd) (auto simp: conj_commute)
    hence "finite {p. p dvd x \<and> prime p \<and> odd (multiplicity p x)}"
      by (rule finite_subset [rotated]) auto
    moreover have "odd (n :: nat) \<longleftrightarrow> n mod 2 = Suc 0" for n by presburger
    ultimately show ?thesis using assms
      by (cases "p dvd x"; cases "even (multiplicity p x)")
         (auto simp: count_prime_factorization prime_multiplicity_squarefree_part
                     in_prime_factors_iff not_dvd_imp_multiplicity_0)
  qed
qed

lemma squarefree_part_nat:
  "squarefree_part (n :: nat) = (\<Prod>{p \<in> prime_factors n. odd (multiplicity p n)})"
proof (cases "n = 0")
  case False
  hence "(\<Prod>{p \<in> prime_factors n. odd (multiplicity p n)}) = 
          prod_mset (prime_factorization (squarefree_part n))"
    by (subst prime_factorization_squarefree_part) (auto simp: prod_unfold_prod_mset)
  also have "\<dots> = squarefree_part n"
    by (intro prod_mset_prime_factorization_nat Nat.gr0I) auto
  finally show ?thesis ..
qed auto

lemma prime_factorization_square_part:
  assumes "x \<noteq> 0"
  shows   "prime_factorization (square_part x) =
             (\<Sum>p \<in> prime_factors x. replicate_mset (multiplicity p x div 2) p)" (is "?lhs = ?rhs")
proof (rule multiset_eqI)
  fix p show "count ?lhs p = count ?rhs p"
  proof (cases "prime p \<and> p dvd x")
    case False
    thus ?thesis by (auto simp: count_prime_factorization count_sum
                                prime_multiplicity_square_part not_dvd_imp_multiplicity_0)
  next
    case True
    thus ?thesis using assms
      by (cases "p dvd x")
         (auto simp: count_prime_factorization prime_multiplicity_squarefree_part
                     in_prime_factors_iff count_sum prime_multiplicity_square_part)
  qed
qed

lemma prod_mset_sum: "prod_mset (sum f A) = (\<Prod>x\<in>A. prod_mset (f x))"
  by (induction A rule: infinite_finite_induct) auto

lemma square_part_nat:
  assumes "n > 0"
  shows   "square_part (n :: nat) = (\<Prod>p \<in> prime_factors n. p ^ (multiplicity p n div 2))"
proof -
  have "(\<Prod>p \<in> prime_factors n. p ^ (multiplicity p n div 2)) = 
          prod_mset (prime_factorization (square_part n))" using assms
    by (subst prime_factorization_square_part) (auto simp: prod_unfold_prod_mset prod_mset_sum)
  also have "\<dots> = square_part n" using assms
    by (intro prod_mset_prime_factorization_nat Nat.gr0I) auto
  finally show ?thesis ..
qed

lemma square_squarefree_part_nat_code [code]:
  "square_squarefree_part_nat n = (if n = 0 then (0, 1)
     else let ps = prime_factorization n
          in  ((\<Prod>p\<in>set_mset ps. p ^ (count ps p div 2)),
                \<Prod>(Set.filter (\<lambda>p. odd (count ps p)) (set_mset ps))))"
  by (cases "n = 0")
     (auto simp: Let_def square_squarefree_part_nat_def squarefree_part_nat Set.filter_def 
                 count_prime_factorization square_part_nat intro!: prod.cong)

lemma square_part_nat_code [code_unfold]:
  "square_part (n :: nat) = (if n = 0 then 0
     else let ps = prime_factorization n in  (\<Prod>p\<in>set_mset ps. p ^ (count ps p div 2)))"
  using square_squarefree_part_nat_code[of n]
  by (simp add: square_squarefree_part_nat_def Let_def split: if_splits)

lemma squarefree_part_nat_code [code_unfold]:
  "squarefree_part (n :: nat) = (if n = 0 then 1
     else let ps = prime_factorization n in (\<Prod>(Set.filter (\<lambda>p. odd (count ps p)) (set_mset ps))))"
  using square_squarefree_part_nat_code[of n]
  by (simp add: square_squarefree_part_nat_def Let_def split: if_splits)

lemma is_nth_power_mult_nth_powerD:
  assumes "is_nth_power n (a * b ^ n)" "b > 0" "n > 0"
  shows   "is_nth_power n (a::nat)"
proof -
  from assms obtain k where k: "k ^ n = a * b ^ n"
    by (auto elim: is_nth_powerE)
  with assms(2,3) have "b dvd k"
    by (metis dvd_triv_right pow_divides_pow_iff)
  then obtain l where "k = b * l"
    by auto
  with k have "a = l ^ n" using assms(2)
    by (simp add: power_mult_distrib)
  thus ?thesis by auto
qed

lemma (in pell) fund_sol_eq_fstI:
  assumes "nontriv_solution (x, y)"
  assumes "\<And>x' y'. nontriv_solution (x', y') \<Longrightarrow> x \<le> x'"
  shows   "fund_sol = (x, y)"
proof -
  have "x = fst fund_sol"
    using fund_sol_is_nontriv_solution assms(1) fund_sol_minimal''[of "(x, y)"]
    by (auto intro!: antisym assms(2)[of "fst fund_sol" "snd fund_sol"])
  moreover from this have "y = snd fund_sol"
    using assms(1) solutions_linorder_strict[of x y "fst fund_sol" "snd fund_sol"]
          fund_sol_is_nontriv_solution
    by (auto simp: nontriv_solution_imp_solution prod_eq_iff)
  ultimately show ?thesis by simp
qed

lemma (in pell) fund_sol_eqI_fst':
  assumes "nontriv_solution xy"
  assumes "\<And>x' y'. nontriv_solution (x', y') \<Longrightarrow> fst xy \<le> x'"
  shows   "fund_sol = xy"
  using fund_sol_eq_fstI[of "fst xy" "snd xy"] assms by simp

lemma (in pell) fund_sol_eq_sndI:
  assumes "nontriv_solution (x, y)"
  assumes "\<And>x' y'. nontriv_solution (x', y') \<Longrightarrow> y \<le> y'"
  shows   "fund_sol = (x, y)"
proof -
  have "y = snd fund_sol"
    using fund_sol_is_nontriv_solution assms(1) fund_sol_minimal''[of "(x, y)"]
    by (auto intro!: antisym assms(2)[of "fst fund_sol" "snd fund_sol"])
  moreover from this have "x = fst fund_sol"
    using assms(1) solutions_linorder_strict[of x y "fst fund_sol" "snd fund_sol"]
          fund_sol_is_nontriv_solution
    by (auto simp: nontriv_solution_imp_solution prod_eq_iff)
  ultimately show ?thesis by simp
qed

lemma (in pell) fund_sol_eqI_snd':
  assumes "nontriv_solution xy"
  assumes "\<And>x' y'. nontriv_solution (x', y') \<Longrightarrow> snd xy \<le> y'"
  shows   "fund_sol = xy"
  using fund_sol_eq_sndI[of "fst xy" "snd xy"] assms by simp


subsection \<open>The lifting mechanism\<close>

text \<open>
  The solutions of Pell's equations for parameters \<open>D\<close> and \<open>a\<^sup>2 D\<close> stand in correspondence to
  one another: every solution \<open>(x, y)\<close> for parameter \<open>D\<close> can be lowered to a solution \<open>(x, ay)\<close>
  for \<open>a\<^sup>2 D\<close>, and every solution of the form \<open>(x, ay)\<close> for parameter \<open>a\<^sup>2 D\<close> can be lifted to a
  solution \<open>(x, y)\<close> for parameter \<open>D\<close>.
\<close>

locale pell_lift = pell +
  fixes a D' :: nat
  assumes nz: "a > 0"
  defines "D' \<equiv> D * a\<^sup>2"
begin

lemma nonsquare_D': "\<not>is_square D'"
  using nonsquare_D is_nth_power_mult_nth_powerD[of 2 D a] nz by (auto simp: D'_def)

definition lift_solution :: "nat \<times> nat \<Rightarrow> nat \<times> nat" where
  "lift_solution = (\<lambda>(x, y). (x, y div a))"

definition lower_solution :: "nat \<times> nat \<Rightarrow> nat \<times> nat" where
  "lower_solution = (\<lambda>(x, y). (x, y * a))"

definition liftable_solution :: "nat \<times> nat \<Rightarrow> bool" where
  "liftable_solution = (\<lambda>(x, y). a dvd y)"

sublocale lift: pell D'
  by unfold_locales (fact nonsquare_D')

lemma lift_solution_iff: "lift.solution xy \<longleftrightarrow> solution (lower_solution xy)"
  unfolding solution_def lift.solution_def
  by (auto simp: lower_solution_def D'_def case_prod_unfold power_mult_distrib)

lemma lift_solution:
  assumes "solution xy" "liftable_solution xy"
  shows   "lift.solution (lift_solution xy)"
  using assms unfolding solution_def lift.solution_def
  by (auto simp: liftable_solution_def lift_solution_def D'_def case_prod_unfold power_mult_distrib
           elim!: dvdE)

text \<open>
  In particular, the fundamental solution for \<open>a\<^sup>2 D\<close> is the smallest liftable solution for \<open>D\<close>:
\<close>
lemma lift_fund_sol:
  assumes "\<And>n. 0 < n \<Longrightarrow> n < m \<Longrightarrow> \<not>liftable_solution (nth_solution n)"
  assumes "liftable_solution (nth_solution m)" "m > 0"
  shows   "lift.fund_sol = lift_solution (nth_solution m)"
proof (rule lift.fund_sol_eqI_fst')
  from assms have "nontriv_solution (nth_solution m)"
    by (intro nth_solution_sound')
  hence "lift_solution (nth_solution m) \<noteq> (1, 0)" using nz assms(2)
    by (auto simp: lift_solution_def case_prod_unfold nontriv_solution_def liftable_solution_def)
  with assms show "lift.nontriv_solution (lift_solution (nth_solution m))"
    by (auto simp: lift.nontriv_solution_altdef intro: lift_solution)
next
  fix x' y' :: nat
  assume *: "lift.nontriv_solution (x', y')"
  hence nz': "x' \<noteq> 1" using nonsquare_D'
    by (auto simp: lift.nontriv_solution_altdef lift.solution_def)
  from * have "solution (lower_solution (x', y'))"
    by (simp add: lift_solution_iff lift.nontriv_solution_altdef)
  hence "lower_solution (x', y') \<in> range nth_solution" by (rule nth_solution_complete)
  then obtain n where n: "nth_solution n = lower_solution (x', y')" by auto
  with nz' have "n > 0" by (auto intro!: Nat.gr0I simp: nth_solution_def lower_solution_def)
  with n have "liftable_solution (nth_solution n)"
    by (auto simp: liftable_solution_def lower_solution_def)
  with \<open>n > 0\<close> and assms(1)[of n] have "n \<ge> m" by (cases "n \<ge> m") auto
  hence "fst (nth_solution m) \<le> fst (nth_solution n)"
    using strict_mono_less_eq[OF strict_mono_nth_solution(1)] by simp
  thus "fst (lift_solution (nth_solution m)) \<le> x'"
    by (simp add: lift_solution_def lower_solution_def n case_prod_unfold)
qed

end


subsection \<open>Accelerated computation of the fundamental solution for non-squarefree inputs\<close>

text \<open>
  Solving Pell's equation for some \<open>D\<close> of the form \<open>a\<^sup>2 D'\<close> can be done by solving
  it for \<open>D'\<close> and then lifting the solution. Thus, if \<open>D\<close> is not squarefree, we can compute
  its squarefree decomposition \<open>a\<^sup>2 D'\<close> with \<open>D'\<close> squarefree and thus speed up the computation
  (since \<open>D'\<close> is smaller than \<open>D\<close>).

  The squarefree decomposition can only be computed (according to current knowledge in mathematics)
  through the prime decomposition. However, given how big the solutions are for even
  moderate values of \<open>D\<close>, it is usually worth doing it if \<open>D\<close> is not squarefree.
\<close>

lemma squarefree_part_of_square [simp]:
  assumes "is_square (x :: 'a :: {factorial_semiring, normalization_semidom_multiplicative})"
  assumes "x \<noteq> 0"
  shows   "squarefree_part x = unit_factor x"
proof -
  from assms obtain y where [simp]: "x = y ^ 2"
    by (auto simp: is_nth_power_def)
  have "unit_factor x * normalize x = squarefree_part x * square_part x ^ 2"
    by (subst squarefree_decompose [symmetric]) auto
  also have "\<dots> = squarefree_part x * normalize x"
    by (simp add: square_part_even_power normalize_power)
  finally show ?thesis using assms
    by (subst (asm) mult_cancel_right) auto
qed

lemma squarefree_part_1_imp_square:
  assumes "squarefree_part x = 1"
  shows   "is_square x"
proof -
  have "is_square (square_part x ^ 2)"
    by auto
  also have "square_part x ^ 2 = squarefree_part x * square_part x ^ 2"
    using assms by simp
  also have "\<dots> = x"
    by (rule squarefree_decompose [symmetric])
  finally show ?thesis .
qed  


definition find_fund_sol_fast where
  "find_fund_sol_fast D =
     (let (a, D') = square_squarefree_part_nat D
      in
        if D' = 0 \<or> D' = 1 then (0, 0)
        else if a = 1 then pell.fund_sol D
        else map_prod id (\<lambda>y. y div a)
               (shd (sdrop_while (\<lambda>(_, y). y = 0 \<or> \<not>a dvd y) (pell_solutions D'))))"

lemma find_fund_sol_fast: "find_fund_sol D = find_fund_sol_fast D"
proof (cases "is_square D \<or> square_part D = 1")
  case True
  thus ?thesis
    using squarefree_part_1_imp_square[of D]
    by (cases "D = 0")
       (auto simp: find_fund_sol_correct find_fund_sol_fast_def
                    square_squarefree_part_nat_def square_test_correct unit_factor_nat_def)
next
  case False
  define D' a where "D' = squarefree_part D" and "a = square_part D"
  have "D > 0"
    using False by (intro Nat.gr0I) auto
  have "a > 0"
    using \<open>D > 0\<close> by (intro Nat.gr0I) (auto simp: a_def)
  moreover have "\<not>is_square D'"
    unfolding D'_def
    by (metis False is_nth_power_mult is_nth_power_nth_power squarefree_decompose)
  ultimately interpret lift: pell_lift D' a D
    using False \<open>D > 0\<close>           
    by unfold_locales (auto simp: D'_def a_def squarefree_decompose [symmetric])

  define i where "i = (LEAST i. case lift.nth_solution i of (_, y) \<Rightarrow> y > 0 \<and> a dvd y)"
  have ex: "\<exists>i. case lift.nth_solution i of (_, y) \<Rightarrow> y > 0 \<and> a dvd y"
  proof -
    define sol where "sol = lift.lift.fund_sol"
    have is_sol: "lift.solution (lift.lower_solution sol)"
      unfolding sol_def using lift.lift.fund_sol_is_nontriv_solution lift.lift_solution_iff by blast
    then obtain j where j: "lift.lower_solution sol = lift.nth_solution j"
      using lift.solution_iff_nth_solution by blast
    have "snd (lift.lower_solution sol) > 0"
    proof (rule Nat.gr0I)
      assume *: "snd (lift.lower_solution sol) = 0"
      have "lift.solution (fst (lift.lower_solution sol), snd (lift.lower_solution sol))"
        using is_sol by simp
      hence "fst (lift.lower_solution sol) = 1"
        by (subst (asm) *) simp
      with * have "lift.lower_solution sol = (1, 0)"
        by (cases "lift.lower_solution sol") auto
      hence "fst sol = 1"
        unfolding lift.lower_solution_def by (auto simp: lift.lower_solution_def case_prod_unfold)
      thus False
        unfolding sol_def
        using lift.lift.fund_sol_is_nontriv_solution \<open>D > 0\<close>
        by (auto simp: lift.lift.nontriv_solution_def)
    qed
    moreover have "a dvd snd (lift.lower_solution sol)"
      by (auto simp: lift.lower_solution_def case_prod_unfold)
    ultimately show ?thesis
      using j by (auto simp: case_prod_unfold)
  qed

  define sol where "sol = lift.nth_solution i"
  have sol: "snd sol > 0" "a dvd snd sol"
    using LeastI_ex[OF ex] by (simp_all add: sol_def i_def case_prod_unfold)
  have "i > 0"
    using sol by (intro Nat.gr0I) (auto simp: sol_def lift.nth_solution_def)

  have "find_fund_sol_fast D = map_prod id (\<lambda>y. y div a)
          (shd (sdrop_while (\<lambda>(_, y). y = 0 \<or> \<not>a dvd y) (pell_solutions D')))"
    unfolding D'_def a_def find_fund_sol_fast_def using False squarefree_part_1_imp_square[of D]
    by (auto simp: square_squarefree_part_nat_def)
  also have "sdrop_while (\<lambda>(_, y). y = 0 \<or> \<not>a dvd y) (pell_solutions D') =
             sdrop_while (Not \<circ> (\<lambda>(_, y). y > 0 \<and> a dvd y)) (pell_solutions D')"
    by (simp add: o_def case_prod_unfold)
  also have "\<dots> = sdrop i (pell_solutions D')"
    using ex by (subst sdrop_while_sdrop_LEAST) (simp_all add: lift.snth_pell_solutions i_def)
  also have "shd \<dots> = sol"
    by (simp add: lift.snth_pell_solutions sol_def)
  finally have eq: "find_fund_sol_fast D = map_prod id (\<lambda>y. y div a) sol" .

  have "lift.lift.fund_sol = lift.lift_solution sol"
    unfolding sol_def
  proof (rule lift.lift_fund_sol)
    show "i > 0" by fact
    show "lift.liftable_solution (lift.nth_solution i)"
      using sol by (simp add: sol_def lift.liftable_solution_def case_prod_unfold)
  next
    fix j :: nat assume j: "j > 0" "j < i"
    show "\<not>lift.liftable_solution (lift.nth_solution j)"
    proof
      assume liftable: "lift.liftable_solution (lift.nth_solution j)"
      have "snd (lift.nth_solution j) > 0"
        using \<open>j > 0\<close> by (metis gr0I lift.nontriv_solution_altdef lift.nth_solution_sound' 
                                lift.solution_0_snd_nat_iff prod.collapse)
      hence "case lift.nth_solution j of (_, y) \<Rightarrow> y > 0 \<and> a dvd y"
        using \<open>j > 0\<close> liftable by (auto simp: lift.liftable_solution_def)
      hence "i \<le> j"
        unfolding i_def by (rule Least_le)
      thus False using \<open>j < i\<close> by simp
    qed
  qed
  also have "\<dots> = find_fund_sol_fast D"
    by (simp add: eq lift.lift_solution_def case_prod_unfold map_prod_def)
  finally show ?thesis
    using \<open>D > 0\<close> False by (simp add: find_fund_sol_correct)
qed

end