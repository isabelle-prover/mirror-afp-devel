(*
  File:     Bertrand.thy
  Authors:  Julian Biendarra, Manuel Eberl <eberlm@in.tum.de>

  A proof of Bertrand's postulate (based on John Harrison's HOL Light proof).
  Uses reflection and the approximation tactic.
*)
theory Bertrand
  imports 
    Complex_Main
    "~~/src/HOL/Number_Theory/Number_Theory"
    "~~/src/HOL/Library/Discrete"
    "~~/src/HOL/Decision_Procs/Approximation"
begin

subsection \<open>Auxiliary facts\<close>

lemma of_nat_ge_1_iff: "(of_nat x :: 'a :: linordered_semidom) \<ge> 1 \<longleftrightarrow> x \<ge> 1"
  using of_nat_le_iff[of 1 x] by (subst (asm) of_nat_1)
  
lemma floor_conv_div_nat:
  "of_int (floor (real m / real n)) = real (m div n)"
  by (subst floor_divide_of_nat_eq) simp

lemma frac_conv_mod_nat:
  "frac (real m / real n) = real (m mod n) / real n"
  by (cases "n = 0")
     (simp_all add: frac_def floor_conv_div_nat field_simps of_nat_mult 
        [symmetric] of_nat_add [symmetric] del: of_nat_mult of_nat_add)

lemma of_nat_prod_mset: "prod_mset (image_mset of_nat A) = of_nat (prod_mset A)"
  by (induction A) simp_all

lemma prod_mset_pos: "(\<And>x :: 'a :: linordered_semidom. x \<in># A \<Longrightarrow> x > 0) \<Longrightarrow> prod_mset A > 0"
  by (induction A) simp_all

lemma ln_msetprod:
  assumes "\<And>x. x \<in>#I \<Longrightarrow> x > 0"
  shows "(\<Sum>p::nat\<in>#I. ln p) = ln (\<Prod>p\<in>#I. p)"
  using assms by (induction I) (simp_all add: of_nat_prod_mset ln_mult prod_mset_pos)

lemma ln_fact: "ln (fact n) = (\<Sum>d=1..n. ln d)"
  by (induction n) (simp_all add: ln_mult)

lemma overpower_lemma:
  fixes f g :: "real \<Rightarrow> real"
  assumes "f a \<le> g a"
  assumes "\<And>x. a \<le> x \<Longrightarrow> ((\<lambda>x. g x - f x) has_real_derivative (d x)) (at x)"
  assumes "\<And>x. a \<le> x \<Longrightarrow> d x \<ge> 0"
  assumes "a \<le> x"
  shows   "f x \<le> g x"
proof (cases "a < x")
  case True
  with assms have "\<exists>z. z > a \<and> z < x \<and> g x - f x - (g a - f a) = (x - a) * d z"
    by (intro MVT2) auto
  then obtain z where z: "z > a" "z < x" "g x - f x - (g a - f a) = (x - a) * d z" by blast
  hence "f x = g x + (f a - g a) + (a - x) * d z" by (simp add: algebra_simps)
  also from assms have "f a - g a \<le> 0" by (simp add: algebra_simps)
  also from assms z have "(a - x) * d z \<le> 0 * d z"
    by (intro mult_right_mono) simp_all
  finally show ?thesis by simp
qed (insert assms, auto)


subsection \<open>Preliminary definitions\<close>
  
definition primepow :: "nat \<Rightarrow> bool" where
  "primepow q \<longleftrightarrow> (\<exists> p k. 1 \<le> k \<and> prime p \<and> q = p^k)"

definition primepows :: "nat \<Rightarrow> nat set" where
  "primepows n = {x::nat. primepow x \<and> x dvd n}"

definition primepow_even :: "nat \<Rightarrow> bool" where
  "primepow_even q \<longleftrightarrow> (\<exists> p k. 1 \<le> k \<and> prime p \<and> q = p^(2*k))"

definition primepow_odd :: "nat \<Rightarrow> bool" where
  "primepow_odd q \<longleftrightarrow> (\<exists> p k. 1 \<le> k \<and> prime p \<and> q = p^(2*k+1))"

abbreviation isprimedivisor :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "isprimedivisor q p \<equiv> prime p \<and> p dvd q"

definition aprimedivisor :: "nat \<Rightarrow> nat" where
  "aprimedivisor q = (LEAST p. isprimedivisor q p)"

definition pre_mangoldt :: "nat \<Rightarrow> nat" where
  "pre_mangoldt d = (if primepow d then aprimedivisor d else 1)"
  
definition mangoldt :: "nat \<Rightarrow> real" where
  "mangoldt d = (if primepow d then ln (aprimedivisor d) else 0)"

definition mangoldt_even :: "nat \<Rightarrow> real" where
  "mangoldt_even d = (if primepow_even d then ln (aprimedivisor d) else 0)"

definition mangoldt_odd :: "nat \<Rightarrow> real" where
  "mangoldt_odd d = (if primepow_odd d then ln (aprimedivisor d) else 0)"

definition mangoldt_1 :: "nat \<Rightarrow> real" where
  "mangoldt_1 d = (if prime d then ln d else 0)"

definition psi :: "nat \<Rightarrow> real" where
  "psi n = (\<Sum>d=1..n. mangoldt d)"

definition psi_even :: "nat \<Rightarrow> real" where
  "psi_even n = (\<Sum>d=1..n. mangoldt_even d)"

definition psi_odd :: "nat \<Rightarrow> real" where
  "psi_odd n = (\<Sum>d=1..n. mangoldt_odd d)"

abbreviation (input) psi_even_2 :: "nat \<Rightarrow> real" where
  "psi_even_2 n \<equiv> (\<Sum>d=2..n. mangoldt_even d)"

abbreviation (input) psi_odd_2 :: "nat \<Rightarrow> real" where
  "psi_odd_2 n \<equiv> (\<Sum>d=2..n. mangoldt_odd d)"

definition theta :: "nat \<Rightarrow> real" where
  "theta n = (\<Sum>p=1..n. if prime p then ln (real p) else 0)"

subsection \<open>Properties of prime powers\<close>  

lemma
  assumes "n \<noteq> 0" "n \<noteq> 1"
  shows prime_aprimedivisor: "prime (aprimedivisor n)" 
    and aprimedivisor_dvd:   "aprimedivisor n dvd n"
proof -
  from assms(2) have A: "\<not>is_unit n" by auto
  from LeastI_ex[OF prime_divisor_exists[OF assms(1) A]] 
    show "prime (aprimedivisor n)" "aprimedivisor n dvd n"
      unfolding aprimedivisor_def by (simp_all add: conj_commute)
qed

lemma finite_primepows [simp]: "n \<noteq> 0 \<Longrightarrow> finite (primepows n)"
  by (rule finite_subset [OF _ finite_divisors_nat[of n]]) (auto simp: primepows_def)

lemma primepow_gt_Suc_0: "primepow n \<Longrightarrow> n > Suc 0"
  using one_less_power[of "p::nat" for p] by (auto simp: primepow_def prime_nat_iff)

lemma aprimedivisor_of_prime [simp]: "prime p \<Longrightarrow> aprimedivisor p = p"
  by (rule primes_dvd_imp_eq) (auto intro!: prime_aprimedivisor aprimedivisor_dvd prime_gt_0_nat)

lemma aprimedivisor_primepow_power:
  assumes "primepow n" "k > 0"
  shows   "aprimedivisor (n ^ k) = aprimedivisor n"
proof -
  from assms obtain p l where l: "prime p" "l \<ge> 1" "n = p ^ l"
    by (auto simp: primepow_def)
  from assms primepow_gt_Suc_0[of n] 
    have *: "prime (aprimedivisor (n ^ k))" "aprimedivisor (n ^ k) dvd n ^ k"
      by (intro prime_aprimedivisor aprimedivisor_dvd; simp)+
  from * l have "aprimedivisor (n ^ k) dvd p ^ (l * k)" by (simp add: power_mult)
  with assms * l have "aprimedivisor (n ^ k) dvd p" 
    by (subst (asm) prime_dvd_power_iff) simp_all
  with l assms have "aprimedivisor (n ^ k) = p"
    by (intro primes_dvd_imp_eq prime_aprimedivisor l) auto
  moreover from l have "aprimedivisor n dvd p ^ l" 
    by (auto intro: aprimedivisor_dvd simp: prime_gt_0_nat)
  with assms l have "aprimedivisor n dvd p"
    by (subst (asm) prime_dvd_power_iff) (auto intro!: prime_aprimedivisor simp: prime_gt_0_nat)
  with l assms have "aprimedivisor n = p"
    by (intro primes_dvd_imp_eq prime_aprimedivisor l) auto
  ultimately show ?thesis by simp
qed

lemma aprimedivisor_prime_power:
  assumes "prime p" "k > 0"
  shows   "aprimedivisor (p ^ k) = p"
proof -
  from assms have *: "prime (aprimedivisor (p ^ k))" "aprimedivisor (p ^ k) dvd p ^ k"
    by (intro prime_aprimedivisor aprimedivisor_dvd; simp add: prime_nat_iff)+
  from assms * have "aprimedivisor (p ^ k) dvd p" 
    by (subst (asm) prime_dvd_power_iff) simp_all
  with assms * show "aprimedivisor (p ^ k) = p" by (intro primes_dvd_imp_eq)
qed

lemma prime_factorization_primepow:
  assumes "primepow n"
  shows   "prime_factorization n = 
             replicate_mset (multiplicity (aprimedivisor n) n) (aprimedivisor n)"
  using assms
  by (auto simp: primepow_def aprimedivisor_prime_power prime_factorization_prime_power)

lemma primepow_decompose:
  assumes "primepow n"
  shows   "aprimedivisor n ^ multiplicity (aprimedivisor n) n = n"
proof -
  from assms have "n \<noteq> 0" by (intro notI) (auto simp: primepow_def)
  hence "n = prod_mset (prime_factorization n)"
    by (subst prod_mset_prime_factorization_nat) simp_all
  also have "prime_factorization n = 
               replicate_mset (multiplicity (aprimedivisor n) n) (aprimedivisor n)"
    by (intro prime_factorization_primepow assms)
  also have "prod_mset \<dots> = aprimedivisor n ^ multiplicity (aprimedivisor n) n" by simp
  finally show ?thesis ..
qed

lemma aprimedivisor_vimage:
  assumes "prime p"
  shows   "aprimedivisor -` {p} \<inter> primepows n = {p ^ k |k. k > 0 \<and> p ^ k dvd n}"
proof safe
  fix q assume q: "q \<in> primepows n"
  hence q': "q \<noteq> 0" "q \<noteq> 1" by (auto simp: primepow_def primepows_def prime_nat_iff)
  let ?n = "multiplicity (aprimedivisor q) q"
  from q q' have "q = aprimedivisor q ^ ?n \<and> ?n > 0 \<and> aprimedivisor q ^ ?n dvd n"
    by (auto simp: primepow_decompose primepows_def prime_multiplicity_gt_zero_iff
          prime_aprimedivisor prime_imp_prime_elem aprimedivisor_dvd)
  thus "\<exists>k. q = aprimedivisor q ^ k \<and> k > 0 \<and> aprimedivisor q ^ k dvd n" ..
next
  fix k :: nat assume k: "p ^ k dvd n" "k > 0"
  with assms show "p ^ k \<in> aprimedivisor -` {p}"
    by (auto simp: aprimedivisor_prime_power)
  with assms k show "p ^ k \<in> primepows n"
    by (auto simp: primepows_def primepow_def aprimedivisor_prime_power intro: Suc_leI)
qed

lemma aprimedivisor_primepows_conv_prime_factorization:
  assumes [simp]: "n \<noteq> 0"
  shows   "image_mset aprimedivisor (mset_set (primepows n)) = prime_factorization n" 
          (is "?lhs = ?rhs")
proof (intro multiset_eqI)
  fix p :: nat
  show "count ?lhs p = count ?rhs p"
  proof (cases "prime p")
    case False
    have "p \<notin># image_mset aprimedivisor (mset_set (primepows n))"
    proof
      assume "p \<in># image_mset aprimedivisor (mset_set (primepows n))"
      then obtain q where "p = aprimedivisor q" "q \<in> primepows n" by auto
      with False prime_aprimedivisor[of q] have "q = 0 \<or> q = 1" by blast
      with \<open>q \<in> primepows n\<close> show False by (auto simp: primepows_def primepow_def)
    qed
    hence "count ?lhs p = 0" by (simp only: Multiset.not_in_iff)
    with False show ?thesis by (simp add: count_prime_factorization)
  next
    case True
    hence "p > 1" by (auto simp: prime_nat_iff)
    have "count ?lhs p = card (aprimedivisor -` {p} \<inter> primepows n)" by (simp add: count_image_mset)
    also have "aprimedivisor -` {p} \<inter> primepows n = {p^k |k. k > 0 \<and> p ^ k dvd n}"
      using True by (rule aprimedivisor_vimage)
    also from True have "\<dots> = (\<lambda>k. p ^ k) ` {0<..multiplicity p n}"
      by (subst power_dvd_iff_le_multiplicity) auto
    also from \<open>p > 1\<close> have "card \<dots> = multiplicity p n"
      by (subst card_image) (auto intro!: inj_onI simp: )
    also from True have "\<dots> = count (prime_factorization n) p" 
      by (simp add: count_prime_factorization)
    finally show ?thesis .
  qed
qed

lemma aprimedivisor:
  assumes "n \<noteq> 1"
  shows   "prime (aprimedivisor n)" "aprimedivisor n dvd n"
proof -
  from assms have "\<exists>p. prime p \<and> p dvd n" by (rule prime_factor_nat)
  from LeastI_ex[OF this, folded aprimedivisor_def] 
    show "prime (aprimedivisor n)" "aprimedivisor n dvd n" by blast+
qed
  
lemma aprimedivisor_gt_1: 
  assumes "n \<noteq> 1"
  shows   "aprimedivisor n > 1"
proof -
  from assms have "prime (aprimedivisor n)" by (rule aprimedivisor)
  thus "aprimedivisor n > 1" by (simp add: prime_nat_iff)
qed

lemma aprimedivisor_le:
  assumes "n > 1"
  shows   "aprimedivisor n \<le> n"
proof -
  from assms have "aprimedivisor n dvd n" by (intro aprimedivisor) simp_all
  with assms show "aprimedivisor n \<le> n"
    by (intro dvd_imp_le) simp_all
qed

lemma primepow_even_imp_primepow:
  assumes "primepow_even n"
  shows   "primepow n"
proof -
  from assms guess p k unfolding primepow_even_def
    by (elim exE conjE)
  thus ?thesis unfolding primepow_def
    by (force simp: primepow_def intro: exI[of _ p, OF exI[of _ "2*k"]])
qed

lemma primepow_odd_imp_primepow:
  assumes "primepow_odd n"
  shows   "primepow n"
proof -
  from assms guess p k unfolding primepow_odd_def
    by (elim exE conjE)
  thus ?thesis unfolding primepow_def
    by (force simp: primepow_def intro: exI[of _ p, OF exI[of _ "2*k"]])
qed

lemma not_primepow_0 [simp]: "\<not>primepow 0"
  by (simp add: primepow_def)

lemma not_primepow_Suc_0 [simp]: "\<not>primepow (Suc 0)"
  using primepow_gt_Suc_0[of "Suc 0"] by auto

lemma aprimedivisor_primepow:
  assumes "prime p" "p dvd n" "primepow n"
  shows   "aprimedivisor (p * n) = p" "aprimedivisor n = p"
proof -
  define q where "q = aprimedivisor n"
  from assms(3) have n_gt_1: "n > Suc 0" by (rule primepow_gt_Suc_0)
  with assms have q: "prime q" by (auto simp: q_def intro!: prime_aprimedivisor)
  from \<open>primepow n\<close> have n: "n = q ^ multiplicity q n" by (simp add: primepow_decompose q_def)
  with assms have "multiplicity q n \<noteq> 0" by (intro notI) simp
  with \<open>prime p\<close> \<open>p dvd n\<close> have "p dvd q"
    by (subst (asm) n) (auto intro: prime_dvd_power_nat)
  with \<open>prime p\<close> q have "p = q" by (intro primes_dvd_imp_eq)
  thus "aprimedivisor n = p" by (simp add: q_def)

  define r where "r = aprimedivisor (p * n)"
  with n_gt_1 assms have r: "r dvd (p * n)" "prime r" unfolding r_def
    by (intro aprimedivisor_dvd prime_aprimedivisor; simp)+
  hence "r dvd q ^ Suc (multiplicity q n)"
    by (subst (asm) n) (simp_all add: \<open>p = q\<close>)
  with r have "r dvd q" 
    by (auto intro: prime_dvd_power_nat simp: prime_dvd_mult_iff dest: prime_dvd_power)
  with r q have "r = q" by (intro primes_dvd_imp_eq)
  thus "aprimedivisor (p * n) = p" by (simp add: r_def \<open>p = q\<close>)
qed

lemma primepow_power_iff:
  "primepow (p ^ n) \<longleftrightarrow> primepow p \<and> n > 0"
proof safe
  assume "primepow (p ^ n)"
  from primepow_gt_Suc_0[OF this] have n: "n \<noteq> 0" by (intro notI) simp
  thus "n > 0" by simp
  from \<open>primepow (p ^ n)\<close> obtain q k where *: "k \<ge> 1" "prime q" "p ^ n = q ^ k"
    by (auto simp: primepow_def)
  with prime_power_exp_nat[of q n p k] n obtain i where "p = q ^ i" by auto
  with \<open>primepow (p ^ n)\<close> have "i \<noteq> 0" by (intro notI) simp
  with \<open>p = q ^ i\<close> \<open>prime q\<close> show "primepow p"
    by (auto simp: primepow_def intro!: exI[of _ q, OF exI[of _ i]])
next
  assume "primepow p" "n > 0"
  then obtain q k where *: "k \<ge> 1" "prime q" "p = q ^ k" by (auto simp: primepow_def)
  with \<open>n > 0\<close> show "primepow (p ^ n)"
    by (auto simp: primepow_def power_mult intro!: exI[of _ q, OF exI[of _ "k * n"]])
qed

lemma primepow_prime [simp]: "prime n \<Longrightarrow> primepow n"
  by (auto simp: primepow_def intro!: exI[of _ n, OF exI[of _ 1]])

lemma primepow_prime_power [simp]: "prime p \<Longrightarrow> primepow (p ^ n) \<longleftrightarrow> n > 0"
  by (simp add: primepow_power_iff)

lemma primepow_multD:
  assumes "primepow (a * b)"
  shows   "a = 1 \<or> primepow a" "b = 1 \<or> primepow b"
proof -
  from assms obtain p k where k: "k \<ge> 1" "a * b = p ^ k" "prime p"
    unfolding primepow_def by auto
  then obtain i j where "a = p ^ i" "b = p ^ j"
    using prime_power_mult_nat[of p a b] by blast
  with \<open>prime p\<close> show "a = 1 \<or> primepow a" "b = 1 \<or> primepow b" by auto
qed

lemma primepow_mult_aprimedivisorI:
  assumes "primepow n"
  shows   "primepow (aprimedivisor n * n)"
  by (subst (2) primepow_decompose[OF assms, symmetric], subst power_Suc [symmetric],
      subst primepow_prime_power) 
     (insert assms, auto intro!: prime_aprimedivisor dest: primepow_gt_Suc_0)

lemma primepow_odd_altdef:
  "primepow_odd n \<longleftrightarrow>
     primepow n \<and> odd (multiplicity (aprimedivisor n) n) \<and> multiplicity (aprimedivisor n) n > 1"
proof (intro iffI conjI; (elim conjE)?)
  assume "primepow_odd n"
  then obtain p k where n: "k \<ge> 1" "prime p" "n = p ^ (2 * k + 1)"
    by (auto simp: primepow_odd_def)
  thus "odd (multiplicity (aprimedivisor n) n)" "multiplicity (aprimedivisor n) n > 1"
    by (simp_all add: aprimedivisor_primepow prime_elem_multiplicity_mult_distrib)
next
  assume A: "primepow n" and B: "odd (multiplicity (aprimedivisor n) n)"
     and C: "multiplicity (aprimedivisor n) n > 1"
  from A obtain p k where n: "k \<ge> 1" "prime p" "n = p ^ k"
    by (auto simp: primepow_def)
  with B C have "odd k" "k > 1"
    by (simp_all add: aprimedivisor_primepow prime_elem_multiplicity_mult_distrib)
  then obtain j where j: "k = 2 * j + 1" "j > 0" by (auto elim!: oddE)
  with n show "primepow_odd n" by (auto simp: primepow_odd_def intro!: exI[of _ p, OF exI[of _ j]])
qed (auto dest: primepow_odd_imp_primepow)

lemma primepow_even_altdef:
  "primepow_even n \<longleftrightarrow> primepow n \<and> even (multiplicity (aprimedivisor n) n)"
proof (intro iffI conjI; (elim conjE)?)
  assume "primepow_even n"
  then obtain p k where n: "k \<ge> 1" "prime p" "n = p ^ (2 * k)"
    by (auto simp: primepow_even_def)
  thus "even (multiplicity (aprimedivisor n) n)"
    by (simp_all add: aprimedivisor_primepow prime_elem_multiplicity_mult_distrib)
next
  assume A: "primepow n" and B: "even (multiplicity (aprimedivisor n) n)"
  from A obtain p k where n: "k \<ge> 1" "prime p" "n = p ^ k"
    by (auto simp: primepow_def)
  with B have "even k"
    by (simp_all add: aprimedivisor_primepow prime_elem_multiplicity_mult_distrib)
  then obtain j where j: "k = 2 * j" by (auto elim!: evenE)
  from j n have "j \<noteq> 0" by (intro notI) simp_all
  with j n show "primepow_even n"
    by (auto simp: primepow_even_def intro!: exI[of _ p, OF exI[of _ j]])
qed (auto dest: primepow_even_imp_primepow)

lemma prime_elem_aprimedivisor: "d > 1 \<Longrightarrow> prime_elem (aprimedivisor d)"
  using prime_aprimedivisor[of d] by simp

lemma aprimedivisor_gt_0 [simp]: "d > 1 \<Longrightarrow> aprimedivisor d > 0"
  using prime_aprimedivisor[of d] by (simp add: prime_gt_0_nat)

lemma aprimedivisor_not_zero [simp]: "d > 1 \<Longrightarrow> aprimedivisor d \<noteq> 0"
  using prime_aprimedivisor[of d] by (simp add: prime_gt_0_nat)

lemma aprimedivisor_gt_Suc_0 [simp]: "d > 1 \<Longrightarrow> aprimedivisor d > Suc 0"
  using prime_aprimedivisor[of d] by (simp add: prime_gt_Suc_0_nat)

lemma aprimedivisor_not_Suc_0 [simp]: "d > 1 \<Longrightarrow> aprimedivisor d \<noteq> Suc 0"
  using aprimedivisor_gt_Suc_0[of d] by (intro notI) (simp del:
aprimedivisor_gt_Suc_0)

lemma multiplicity_aprimedivisor_gt_0 [simp]:
  "d > 1 \<Longrightarrow> multiplicity (aprimedivisor d) d > 0"
  by (subst multiplicity_gt_zero_iff) (auto intro: aprimedivisor_dvd)

lemma primepow_odd_mult:
  assumes "d > 1"
  shows   "primepow_odd (aprimedivisor d * d) \<longleftrightarrow> primepow_even d"
    using assms
    by (auto simp: primepow_odd_altdef primepow_even_altdef primepow_mult_aprimedivisorI
                   aprimedivisor_primepow prime_aprimedivisor aprimedivisor_dvd
                   prime_elem_multiplicity_mult_distrib prime_elem_aprimedivisor
             dest!: primepow_multD)

lemma primepowI:
  "prime p \<Longrightarrow> k \<ge> 1 \<Longrightarrow> p ^ k = n \<Longrightarrow> primepow n \<and> aprimedivisor n = p"
  unfolding primepow_def by (auto simp: aprimedivisor_prime_power)

lemma not_primepowI:
  assumes "prime p" "prime q" "p \<noteq> q" "p dvd n" "q dvd n"
  shows   "\<not>primepow n"
  using assms by (auto dest: aprimedivisor_primepow(2))

lemma pre_mangoldt_primepow:
  assumes "primepow n" "aprimedivisor n = p"
  shows   "pre_mangoldt n = p"
  using assms by (simp add: pre_mangoldt_def)

lemma pre_mangoldt_notprimepow:
  assumes "\<not>primepow n"
  shows   "pre_mangoldt n = 1"
  using assms by (simp add: pre_mangoldt_def)

lemma not_primepow_1: "\<not>primepow 1" by simp

lemma sum_prime_factorization_conv_sum_primepows:
  assumes "n \<noteq> 0"
  shows "(\<Sum>q\<in>primepows n. f (aprimedivisor q)) = (\<Sum>p\<in>#prime_factorization n. f p)"
proof -
  from assms have "prime_factorization n = image_mset aprimedivisor (mset_set (primepows n))"
    by (rule aprimedivisor_primepows_conv_prime_factorization [symmetric])
  also have "(\<Sum>p\<in>#\<dots>. f p) = (\<Sum>q\<in>primepows n. f (aprimedivisor q))"
    by (simp add: image_mset.compositionality sum_unfold_sum_mset o_def)
  finally show ?thesis ..
qed    

lemma primepow_gt_0: "primepow n \<Longrightarrow> n > 0"
  using primepow_gt_Suc_0[of n] by simp

lemma multiplicity_aprimedivisor_Suc_0_iff:
  assumes "primepow n"
  shows   "multiplicity (aprimedivisor n) n = Suc 0 \<longleftrightarrow> prime n"
  by (subst (3) primepow_decompose [OF assms, symmetric])
     (insert assms primepow_gt_Suc_0[OF assms],
      auto simp add: prime_power_iff intro!: prime_aprimedivisor)

lemma primepow_cases:
  "primepow d \<longleftrightarrow>
     (  primepow_even d \<and> \<not> primepow_odd d \<and> \<not> prime d) \<or>
     (\<not> primepow_even d \<and>   primepow_odd d \<and> \<not> prime d) \<or>
     (\<not> primepow_even d \<and> \<not> primepow_odd d \<and>   prime d)"
  by (auto simp: primepow_even_altdef primepow_odd_altdef multiplicity_aprimedivisor_Suc_0_iff
           elim!: oddE intro!: Nat.gr0I)  

  
subsection \<open>Deriving a recurrence for the psi function\<close>
  
lemma ln_fact_bounds:
  assumes "n > 0"
  shows "abs(ln (fact n) - n * ln n + n) \<le> 1 + ln n"
proof -
  have "\<forall>n\<in>{0<..}. \<exists>z>real n. z < real (n + 1) \<and> real (n + 1) * ln (real (n + 1)) - 
          real n * ln (real n) = (real (n + 1) - real n) * (ln z + 1)"
    by (intro ballI MVT2) (auto intro!: derivative_eq_intros)
  hence "\<forall>n\<in>{0<..}. \<exists>z>real n. z < real (n + 1) \<and> real (n + 1) * ln (real (n + 1)) - 
          real n * ln (real n) = (ln z + 1)" by (simp add: algebra_simps)
  from bchoice[OF this] obtain k :: "nat \<Rightarrow> real"
    where lb: "real n < k n" and ub: "k n < real (n + 1)" and 
          mvt: "real (n+1) * ln (real (n+1)) - real n * ln (real n) = ln (k n) + 1" 
          if "n > 0" for n::nat by blast
  have *: "(n + 1) * ln (n + 1) = (\<Sum>i=1..n. ln(k i) + 1)" for n::nat
  proof (induction n)
    case (Suc n)
    have "(\<Sum>i = 1..n+1. ln (k i) + 1) = (\<Sum>i = 1..n. ln (k i) + 1) + ln (k (n+1)) + 1"
      by simp
    also from Suc.IH have "(\<Sum>i = 1..n. ln (k i) + 1) = real (n+1) * ln (real (n+1))" ..
    also from mvt[of "n+1"] have "\<dots> = real (n+2) * ln (real (n+2)) - ln (k (n+1)) - 1"
      by simp
    finally show ?case
      by simp
  qed simp
  have **: "abs((\<Sum>i=1..n+1. ln i) - ((n+1) * ln (n+1) - (n+1))) \<le> 1 + ln(n+1)" for n::nat
  proof -
    have "(\<Sum>i=1..n+1. ln i) \<le> (\<Sum>i=1..n. ln i) + ln (n+1)"
      by simp
    also have "(\<Sum>i=1..n. ln i) \<le> (\<Sum>i=1..n. ln (k i))"
      by (intro sum_mono, subst ln_le_cancel_iff) (auto simp: Suc_le_eq dest: lb ub)
    also have "\<dots> = (\<Sum>i=1..n. ln (k i) + 1) - n"
      by (simp add: sum.distrib)
    also from * have "\<dots> = (n+1) * ln (n+1) - n"
      by simp
    finally have a_minus_b: "(\<Sum>i=1..n+1. ln i) - ((n+1) * ln (n+1) - (n+1)) \<le> 1 + ln (n+1)"
      by simp

    from * have "(n+1) * ln (n+1) - n = (\<Sum>i=1..n. ln (k i) + 1) - n"
      by simp
    also have "\<dots> = (\<Sum>i=1..n. ln (k i))"
      by (simp add: sum.distrib)
    also have "\<dots> \<le> (\<Sum>i=1..n. ln (i+1))"
      by (intro sum_mono, subst ln_le_cancel_iff) (auto simp: Suc_le_eq dest: lb ub)
    also from sum_shift_bounds_cl_nat_ivl[of "ln" 1 1 n] have "\<dots> = (\<Sum>i=1+1..n+1. ln i)" ..
    also have "\<dots> = (\<Sum>i=1..n+1. ln i)"
      by (rule sum.mono_neutral_left) auto
    finally have b_minus_a: "((n+1) * ln (n+1) - (n+1)) - (\<Sum>i=1..n+1. ln i) \<le> 1"
      by simp
    have "0 \<le> ln (n+1)"
      by simp
    with b_minus_a have "((n+1) * ln (n+1) - (n+1)) - (\<Sum>i=1..n+1. ln i) \<le> 1 + ln (n+1)"
      by linarith
    with a_minus_b show ?thesis
      by linarith
  qed
  from \<open>n > 0\<close> have "n \<ge> 1" by simp
  thus ?thesis
  proof (induction n rule: dec_induct)
    case base
    then show ?case by simp
  next
    case (step n)
    from ln_fact[of "n+1"] **[of n] show ?case by simp
  qed
qed

lemma ln_fact_diff_bounds:
  "abs(ln (fact n) - 2 * ln (fact (n div 2)) - n * ln 2) \<le> 4 * ln (if n = 0 then 1 else n) + 3"
proof (cases "n div 2 = 0")
  case True
  hence "n \<le> 1" by simp
  with ln_le_minus_one[of "2::real"] show ?thesis by (cases n) simp_all
next
  case False
  then have "n > 1" by simp
  let ?a = "real n * ln 2"
  let ?b = "4 * ln (real n) + 3"
  let ?l1 = "ln (fact (n div 2))"
  let ?a1 = "real (n div 2) * ln (real (n div 2)) - real (n div 2)"
  let ?b1 = "1 + ln (real (n div 2))"
  let ?l2 = "ln (fact n)"
  let ?a2 = "real n * ln (real n) - real n"
  let ?b2 = "1 + ln (real n)"
  have abs_a: "abs(?a - (?a2 - 2 * ?a1)) \<le> ?b - 2 * ?b1 - ?b2"
  proof (cases "even n")
    case True
    then have "real (2 * (n div 2)) = real n"
      by simp
    then have n_div_2: "real (n div 2) = real n / 2"
      by simp
    from \<open>n > 1\<close> have *: "abs(?a - (?a2 - 2 * ?a1)) = 0"
      by (simp add: n_div_2 ln_div algebra_simps)
    from \<open>even n\<close> and \<open>n > 1\<close> have "0 \<le> ln (real n) - ln (real (n div 2))"
      by (auto elim: evenE)
    also have "2 * \<dots> \<le> 3 * ln (real n) - 2 * ln (real (n div 2))"
      using \<open>n > 1\<close> by (auto intro!: ln_ge_zero)
    also have "\<dots> = ?b - 2 * ?b1 - ?b2" by simp
    finally show ?thesis using * by simp
  next
    case False
    then have "real (2 * (n div 2)) = real (n - 1)"
      by simp
    with \<open>n > 1\<close> have n_div_2: "real (n div 2) = (real n - 1) / 2"
      by simp
    from \<open>odd n\<close> \<open>n div 2 \<noteq> 0\<close> have "n \<ge> 3"
      by presburger

    have "?a - (?a2 - 2 * ?a1) = real n * ln 2 - real n * ln (real n) + real n + 
             2 * real (n div 2) * ln (real (n div 2)) - 2* real (n div 2)"
      by (simp add: algebra_simps)
    also from n_div_2 have "2 * real (n div 2) = real n - 1"
      by simp
    also have "real n * ln 2 - real n * ln (real n) + real n + 
                   (real n - 1) * ln (real (n div 2)) - (real n - 1)
                 = real n * (ln (real n - 1) - ln (real n)) - ln (real (n div 2)) + 1"
      using \<open>n > 1\<close> by (simp add: algebra_simps n_div_2 ln_div)
    finally have lhs: "abs(?a - (?a2 - 2 * ?a1)) = 
        abs(real n * (ln (real n - 1) - ln (real n)) - ln (real (n div 2)) + 1)"
      by simp

    from \<open>n > 1\<close> have "real n * (ln (real n - 1) - ln (real n)) \<le> 0"
      by (simp add: algebra_simps mult_left_mono pos_prod_le)
    moreover from \<open>n > 1\<close> have "ln (real (n div 2)) \<le> ln (real n)" by simp
    moreover {
      have "exp 1 \<le> (3::real)" by (rule exp_le)
      also from \<open>n \<ge> 3\<close> have "\<dots> \<le> exp (ln (real n))" by simp
      finally have "ln (real n) \<ge> 1" by simp
    }
    ultimately have ub: "real n * (ln (real n - 1) - ln (real n)) - ln(real (n div 2)) + 1 \<le> 
                           3 * ln (real n) - 2 * ln(real (n div 2))" by simp
 
    have mon: "real n' * (ln (real n') - ln (real n' - 1)) \<le> 
                 real n * (ln (real n) - ln (real n - 1))" 
      if "n \<ge> 3" "n' \<ge> n" for n n'::nat
    proof (rule DERIV_nonpos_imp_nonincreasing[where f = "\<lambda>x. x * (ln x - ln (x - 1))"], goal_cases)
      case 2
      show ?case
      proof clarify
        fix t assume t: "real n \<le> t" "t \<le> real n'"
        with that have "1 / (t - 1) \<ge> ln (1 + 1/(t - 1))"
          by (intro ln_add_one_self_le_self) simp_all
        also from t that have "ln (1 + 1/(t - 1)) = ln t- ln (t - 1)"
          by (simp add: ln_div [symmetric] field_simps)
        finally have "ln t - ln (t - 1) \<le> 1 / (t - 1)" .
        with that t
          show "\<exists>y. ((\<lambda>x. x * (ln x - ln (x - 1))) has_field_derivative y) (at t) \<and> y \<le> 0"
          by (intro exI[of _ "1 / (1 - t) + ln t - ln (t - 1)"])
             (force intro!: derivative_eq_intros simp: field_simps)+
      qed
    qed (insert that, simp_all)
    
    from \<open>n > 1\<close> have "ln 2 = ln (real n) - ln (real n / 2)"
      by (simp add: ln_div)
    also from \<open>n > 1\<close> have "\<dots> \<le> ln (real n) - ln (real (n div 2))" 
      by simp
    finally have *: "3*ln 2 + ln(real (n div 2)) \<le> 3* ln(real n) - 2* ln(real (n div 2))"
      by simp
    
    have "- real n * (ln (real n - 1) - ln (real n)) + ln(real (n div 2)) - 1 = 
            real n * (ln (real n) - ln (real n - 1)) - 1 + ln(real (n div 2))"
      by (simp add: algebra_simps)
    also have "real n * (ln (real n) - ln (real n - 1)) \<le> 3 * (ln 3 - ln (3 - 1))"
      using mon[OF _ \<open>n \<ge> 3\<close>] by simp
    also have "3 * (ln 3 - ln (3 - 1)) - 1 \<le> 3 * ln (2 :: real)"
      by (approximation 3)
    also note *
    finally have "- real n * (ln (real n - 1) - ln (real n)) + ln(real (n div 2)) - 1 \<le> 
                    3 * ln (real n) - 2 * ln (real (n div 2))" by simp
    hence lhs': "abs(real n * (ln (real n - 1) - ln (real n)) - ln(real (n div 2)) + 1) \<le> 
                   3 * ln (real n) - 2 * ln (real (n div 2))"
      using ub by simp
    have rhs: "?b - 2 * ?b1 - ?b2 = 3* ln (real n) - 2 * ln (real (n div 2))"
      by simp
    from \<open>n > 1\<close> have "ln (real (n div 2)) \<le> 3* ln (real n) - 2* ln (real (n div 2))"
      by simp
    with rhs lhs lhs' show ?thesis
      by simp
  qed
  then have minus_a: "-?a \<le> ?b - 2 * ?b1 - ?b2 - (?a2 - 2 * ?a1)"
    by simp
  from abs_a have a: "?a \<le> ?b - 2 * ?b1 - ?b2 + ?a2 - 2 * ?a1"
    by simp
  from ln_fact_bounds[of "n div 2"] False have abs_l1: "abs(?l1 - ?a1) \<le> ?b1"
    by (simp add: algebra_simps)
  then have minus_l1: "?a1 - ?l1 \<le> ?b1"
    by linarith
  from abs_l1 have l1: "?l1 - ?a1 \<le> ?b1"
    by linarith
  from ln_fact_bounds[of n] False have abs_l2: "abs(?l2 - ?a2) \<le> ?b2"
    by (simp add: algebra_simps)
  then have l2: "?l2 - ?a2 \<le> ?b2"
    by simp
  from abs_l2 have minus_l2: "?a2 - ?l2 \<le> ?b2"
    by simp
  from minus_a minus_l1 l2 have "?l2 - 2 * ?l1 - ?a \<le> ?b"
    by simp
  moreover from a l1 minus_l2 have "- ?l2 + 2 * ?l1 + ?a \<le> ?b"
    by simp
  ultimately have "abs((?l2 - 2*?l1) - ?a) \<le> ?b"
    by simp
  then show ?thesis 
    by simp
qed  
  
lemma ln_primefact:
  assumes "n \<noteq> 0"
  shows   "ln n = (\<Sum>d=1..n. if primepow d \<and> d dvd n then ln (aprimedivisor d) else 0)" 
          (is "?lhs = ?rhs")
proof -
  have "?rhs = (\<Sum>d\<in>{x \<in> {1..n}. primepow x \<and> x dvd n}. ln (real (aprimedivisor d)))" 
    unfolding primepows_def by (subst sum.inter_filter [symmetric]) simp_all
  also have "{x \<in> {1..n}. primepow x \<and> x dvd n} = primepows n"
    using assms by (auto simp: primepows_def dest: dvd_imp_le primepow_gt_Suc_0)
  finally have *: "(\<Sum>d\<in>primepows n. ln (real (aprimedivisor d))) = ?rhs" ..
  from in_prime_factors_imp_prime prime_gt_0_nat 
    have pf_pos: "\<And>p. p\<in>#prime_factorization n \<Longrightarrow> p > 0"
    by blast
  from ln_msetprod[of "prime_factorization n", OF pf_pos] assms
    have "ln n = (\<Sum>p\<in>#prime_factorization n. ln p)"
      by (simp add: of_nat_prod_mset)
  also from * sum_prime_factorization_conv_sum_primepows[of n ln, OF assms(1)]
    have "\<dots> = ?rhs" by simp
  finally show ?thesis .
qed

context
begin

private lemma divisors:
  fixes x d::nat
  assumes "x \<in> {1..n}"
  assumes "d dvd x"
  shows "\<exists>k\<in>{1..n div d}. x = d * k"
proof -
  from assms have "x \<le> n"
    by simp
  then have ub: "x div d \<le> n div d"
    by (simp add: div_le_mono \<open>x \<le> n\<close>)
  from assms have "1 \<le> x div d" by (auto elim!: dvdE)
  with ub have "x div d \<in> {1..n div d}"
    by simp
  with \<open>d dvd x\<close> show ?thesis by (auto intro!: bexI[of _ "x div d"])
qed

lemma ln_fact_conv_mangoldt:
  shows "ln (fact n) = (\<Sum>d=1..n. mangoldt d * floor (n / d))"
proof -
  have *: "(\<Sum>da=1..n. if primepow da \<and>
        da dvd d then ln (aprimedivisor da) else 0) = 
        (\<Sum>da=1..d. if primepow da \<and>
        da dvd d then ln (aprimedivisor da) else 0)" if d: "d \<in> {1..n}" for d
    by (rule sum.mono_neutral_right, insert d) (auto dest: dvd_imp_le)
  have "(\<Sum>d=1..n. \<Sum>da=1..d. if primepow da \<and>
      da dvd d then ln (aprimedivisor da) else 0) = 
      (\<Sum>d=1..n. \<Sum>da=1..n. if primepow da \<and>
      da dvd d then ln (aprimedivisor da) else 0)"
    by (rule sum.cong) (insert *, simp_all)
  also have "\<dots> = (\<Sum>da=1..n. \<Sum>d=1..n. if primepow da \<and>
                     da dvd d then ln (aprimedivisor da) else 0)"
    by (rule sum.commute)
  also have "\<dots> = sum (\<lambda>d. mangoldt d * floor (n/d)) {1..n}"
  proof (rule sum.cong)
    fix d assume d: "d \<in> {1..n}"
    have "(\<Sum>da = 1..n. if primepow d \<and> d dvd da then ln (real (aprimedivisor d)) else 0) =
            (\<Sum>da = 1..n. if d dvd da then mangoldt d else 0)"
      by (intro sum.cong) (simp_all add: mangoldt_def)
    also have "\<dots> = mangoldt d * real (card {x. x \<in> {1..n} \<and> d dvd x})"
      by (subst sum.inter_filter [symmetric]) (simp_all add: algebra_simps)
    also {
      have "{x. x \<in> {1..n} \<and> d dvd x} = {x. \<exists>k \<in>{1..n div d}. x=k*d}"
      proof safe
        fix x assume "x \<in> {1..n}" "d dvd x"
        thus "\<exists>k\<in>{1..n div d}. x = k * d" using divisors[of x n d] by auto
      next
        fix x k assume k: "k \<in> {1..n div d}"
        from k have "k * d \<le> n div d * d" by (intro mult_right_mono) simp_all
        also have "n div d * d \<le> n div d * d + n mod d" by (rule le_add1)
        also have "\<dots> = n" by simp
        finally have "k * d \<le> n" .
        thus "k * d \<in> {1..n}" using d k by auto
      qed auto
      also have "\<dots> = (\<lambda>k. k*d) ` {1..n div d}"
        by fast
      also have "card \<dots> = card {1..n div d}"
        by (rule card_image) (simp add: inj_on_def)
      also have "\<dots> = n div d"
        by simp
      also have "... = \<lfloor>n / d\<rfloor>"
        by (simp add: floor_divide_of_nat_eq)
      finally have "real (card {x. x \<in> {1..n} \<and> d dvd x}) = real_of_int \<lfloor>n / d\<rfloor>"
        by force
    }
    finally show "(\<Sum>da = 1..n. if primepow d \<and> d dvd da then ln (real (aprimedivisor d)) else 0) =
            mangoldt d * real_of_int \<lfloor>real n / real d\<rfloor>" .
  qed simp_all
  finally have "(\<Sum>d=1..n. \<Sum>da=1..d. if primepow da \<and>
      da dvd d then ln (aprimedivisor da) else 0) = 
    sum (\<lambda>d. mangoldt d * floor (n/d)) {1..n}" .
  with ln_primefact have "(\<Sum>d=1..n. ln d) =
    (\<Sum>d=1..n. mangoldt d * floor (n/d))"
    by simp
  with ln_fact show ?thesis
    by simp
qed

end

lemma mangoldt_pos: "0 \<le> mangoldt d"
  using aprimedivisor_gt_1[of d]
  by (auto simp: mangoldt_def of_nat_le_iff[of 1 x for x, unfolded of_nat_1] Suc_le_eq
           intro!: ln_ge_zero dest: primepow_gt_Suc_0)
  
context
begin

private lemma div_2_mult_2_bds:
  fixes n d :: nat
  assumes "d > 0"
  shows "0 \<le> \<lfloor>n / d\<rfloor> - 2 * \<lfloor>(n div 2) / d\<rfloor>" "\<lfloor>n / d\<rfloor> - 2 * \<lfloor>(n div 2) / d\<rfloor> \<le> 1"
proof -
  have "\<lfloor>2::real\<rfloor> * \<lfloor>(n div 2) / d\<rfloor> \<le> \<lfloor>2 * ((n div 2) / d)\<rfloor>" 
    by (rule le_mult_floor) simp_all
  also from assms have "\<dots> \<le> \<lfloor>n / d\<rfloor>" by (intro floor_mono) (simp_all add: field_simps)
  finally show "0 \<le> \<lfloor>n / d\<rfloor> - 2 * \<lfloor>(n div 2) / d\<rfloor>" by (simp add: algebra_simps)
next  
  have "real (n div d) \<le> real (2 * ((n div 2) div d) + 1)"
    by (subst div_mult2_eq [symmetric], simp only: mult.commute, subst div_mult2_eq) simp
  thus "\<lfloor>n / d\<rfloor> - 2 * \<lfloor>(n div 2) / d\<rfloor> \<le> 1"
    unfolding of_nat_add of_nat_mult floor_conv_div_nat [symmetric] by simp_all
qed

private lemma n_div_d_eq_1: "d \<in> {n div 2 + 1..n} \<Longrightarrow> \<lfloor>real n / real d\<rfloor> = 1"
  by (cases "n = d") (auto simp: field_simps intro: floor_eq)
    
lemma psi_bounds_ln_fact:
  shows "ln (fact n) - 2 * ln (fact (n div 2)) \<le> psi n"
        "psi n - psi (n div 2) \<le> ln (fact n) - 2 * ln (fact (n div 2))"
proof -
  fix n::nat
  let ?k = "n div 2" and ?d = "n mod 2"
  have *: "\<lfloor>?k / d\<rfloor> = 0" if "d > ?k" for d
  proof -
    from that div_less have "0 = ?k div d" by simp
    also have "\<dots> = \<lfloor>?k / d\<rfloor>" by (rule floor_divide_of_nat_eq [symmetric])
    finally show "\<lfloor>?k / d\<rfloor> = 0" by simp
  qed
  have sum_eq: "(\<Sum>d=1..2*?k+?d. mangoldt d * \<lfloor>?k / d\<rfloor>) = (\<Sum>d=1..?k. mangoldt d * \<lfloor>?k / d\<rfloor>)"
    by (intro sum.mono_neutral_right) (auto simp: *)
  from ln_fact_conv_mangoldt have "ln (fact n) = (\<Sum>d=1..n. mangoldt d * \<lfloor>n / d\<rfloor>)" .
  also have "\<dots> = (\<Sum>d=1..n. mangoldt d * \<lfloor>(2 * (n div 2) + n mod 2) / d\<rfloor>)"
    by simp
  also have "\<dots> \<le> (\<Sum>d=1..n. mangoldt d * (2 * \<lfloor>?k / d\<rfloor> + 1))"
    using div_2_mult_2_bds(2)[of _ n]
    by (intro sum_mono mult_left_mono, subst of_int_le_iff)
       (auto simp: algebra_simps mangoldt_pos)
  also have "\<dots> = 2 * (\<Sum>d=1..n. mangoldt d * \<lfloor>(n div 2) / d\<rfloor>) + (\<Sum>d=1..n. mangoldt d)"
    by (simp add: algebra_simps sum.distrib sum_distrib_left)
  also have "\<dots> = 2 * (\<Sum>d=1..2*?k+?d. mangoldt d * \<lfloor>(n div 2) / d\<rfloor>) + (\<Sum>d=1..n. mangoldt d)"
    by presburger
  also from sum_eq have "\<dots> = 2 * (\<Sum>d=1..?k. mangoldt d * \<lfloor>(n div 2) / d\<rfloor>) + (\<Sum>d=1..n. mangoldt d)"
    by presburger
  also from ln_fact_conv_mangoldt psi_def have "\<dots> = 2 * ln (fact ?k) + psi n"
    by presburger
  finally show "ln (fact n) - 2 * ln (fact (n div 2)) \<le> psi n"
    by simp
next
  fix n::nat
  let ?k = "n div 2" and  ?d = "n mod 2"
  from psi_def have "psi n - psi ?k = (\<Sum>d=1..2*?k+?d. mangoldt d) - (\<Sum>d=1..?k. mangoldt d)"
    by presburger
  also have "\<dots> = sum mangoldt ({1..2 * (n div 2) + n mod 2} - {1..n div 2})"
    by (subst sum_diff) simp_all
  also have "\<dots> = (\<Sum>d\<in>({1..2 * (n div 2) + n mod 2} - {1..n div 2}). 
                    (if d \<le> ?k then 0 else mangoldt d))"
    by (intro sum.cong) simp_all
  also have "\<dots> = (\<Sum>d=1..2*?k+?d. (if d \<le> ?k then 0 else mangoldt d))"
    by (intro sum.mono_neutral_left) auto
  also have "\<dots> = (\<Sum>d=1..n. (if d \<le> ?k then 0 else mangoldt d))"
    by presburger
  also have "\<dots> = (\<Sum>d=1..n. (if d \<le> ?k then mangoldt d * 0 else mangoldt d))"
    by (intro sum.cong) simp_all
  also from div_2_mult_2_bds(1) have "\<dots> \<le> (\<Sum>d=1..n. (if d \<le> ?k then mangoldt d * (\<lfloor>n/d\<rfloor> - 2 * \<lfloor>?k/d\<rfloor>) else mangoldt d))"
    by (intro sum_mono) 
       (auto simp: algebra_simps mangoldt_pos intro!: mult_left_mono simp del: of_int_mult)
  also from n_div_d_eq_1 have "\<dots> = (\<Sum>d=1..n. (if d \<le> ?k then mangoldt d * (\<lfloor>n/d\<rfloor> - 2 * \<lfloor>?k/d\<rfloor>) else mangoldt d * \<lfloor>n/d\<rfloor>))"
    by (intro sum.cong refl) auto
  also have "\<dots> = (\<Sum>d=1..n. mangoldt d * real_of_int (\<lfloor>real n / real d\<rfloor>) -
                     (if d \<le> ?k then 2 * mangoldt d * real_of_int \<lfloor>real ?k / real d\<rfloor> else 0))"
    by (intro sum.cong refl) (auto simp: algebra_simps)
  also have "\<dots> = (\<Sum>d=1..n. mangoldt d * real_of_int (\<lfloor>real n / real d\<rfloor>)) - 
                  (\<Sum>d=1..n. (if d \<le> ?k then 2 * mangoldt d * real_of_int \<lfloor>real ?k / real d\<rfloor> else 0))"
    by (rule sum_subtractf)    
  also have "(\<Sum>d=1..n. (if d \<le> ?k then 2 * mangoldt d * real_of_int \<lfloor>real ?k / real d\<rfloor> else 0)) =
               (\<Sum>d=1..?k. (if d \<le> ?k then 2 * mangoldt d * real_of_int \<lfloor>real ?k / real d\<rfloor> else 0))"
    by (intro sum.mono_neutral_right) auto
  also have "\<dots> = (\<Sum>d=1..?k. 2 * mangoldt d * real_of_int \<lfloor>real ?k / real d\<rfloor>)"
    by (intro sum.cong) simp_all
  also have "\<dots> = 2 * (\<Sum>d=1..?k. mangoldt d * real_of_int \<lfloor>real ?k / real d\<rfloor>)"
    by (simp add: sum_distrib_left mult_ac)
  also have "(\<Sum>d = 1..n. mangoldt d * real_of_int \<lfloor>real n / real d\<rfloor>) - \<dots> = 
               ln (fact n) - 2 * ln (fact (n div 2))"
    by (simp add: ln_fact_conv_mangoldt)
  finally show "psi n - psi (n div 2) \<le> ln (fact n) - 2 * ln (fact (n div 2))" .
qed

end

lemma psi_bounds_induct:
  "real n * ln 2 - (4 * ln (real (if n = 0 then 1 else n)) + 3) \<le> psi n"
  "psi n - psi (n div 2) \<le> real n * ln 2 + (4 * ln (real (if n = 0 then 1 else n)) + 3)"
proof -
  from le_imp_neg_le[OF ln_fact_diff_bounds]
    have "n * ln 2 - (4 * ln (if n = 0 then 1 else n) + 3)
         \<le> n * ln 2 - abs(ln (fact n) - 2 * ln (fact (n div 2)) - n * ln 2)"
    by simp
  also have "\<dots> \<le> ln (fact n) - 2 * ln (fact (n div 2))"
    by simp
  also from psi_bounds_ln_fact (1) have "\<dots> \<le> psi n"
    by simp
  finally show "real n * ln 2 - (4 * ln (real (if n = 0 then 1 else n)) + 3) \<le> psi n" .
next
  from psi_bounds_ln_fact (2) have "psi n - psi (n div 2) \<le> ln (fact n) - 2 * ln (fact (n div 2))" .
  also have "\<dots> \<le> n * ln 2 + abs(ln (fact n) - 2 * ln (fact (n div 2)) - n * ln 2)"
    by simp
  also from ln_fact_diff_bounds [of n] 
    have "abs(ln (fact n) - 2 * ln (fact (n div 2)) - n * ln 2)
            \<le> (4 * ln (real (if n = 0 then 1 else n)) + 3)" by simp
  finally show "psi n - psi (n div 2) \<le> real n * ln 2 + (4 * ln (real (if n = 0 then 1 else n)) + 3)"
    by simp
qed
  

subsection \<open>Bounding the psi function\<close>

text \<open>
  In this section, we will first prove the relatively tight estimate
  @{prop "psi n \<le> 3 / 2 + ln 2 * n"} for @{term "n \<le> 128"} and then use the 
  recurrence we have just derived to extend it to @{prop "psi n \<le> 551 / 256"} for 
  @{term "n \<le> 1024"}, at which point applying the recurrence can be used to prove 
  the same bound for arbitrarily big numbers.

  First of all, we will prove the bound for @{term "n <= 128"} using reflection and
  approximation.
\<close>  

ML \<open>
structure Bertrand = 
struct

local

fun prime (ct, b) = Thm.mk_binop @{cterm "Pure.eq :: bool \<Rightarrow> bool \<Rightarrow> prop"}
  ct (if b then @{cterm True} else @{cterm False});

val (_, prime_oracle) = Context.>>> (Context.map_theory_result
  (Thm.add_oracle (@{binding prime}, prime)));

in

val raw_prime_computation_conv =
  @{computation_conv bool terms: "prime :: nat \<Rightarrow> bool"
     "Ball :: nat set \<Rightarrow> _" "{0, 1, 2, 3} :: nat set"}
  (fn _ => fn b => fn ct => prime_oracle (ct, b));

fun prime_computation_conv ctxt =
  HOLogic.Trueprop_conv (raw_prime_computation_conv ctxt);

end

end;
\<close>
  
context
begin

private lemma Ball_insertD:
  assumes "\<forall>x\<in>insert y A. P x"
  shows   "P y" "\<forall>x\<in>A. P x"
  using assms by auto

private lemma meta_eq_TrueE: "PROP A \<equiv> Trueprop True \<Longrightarrow> PROP A"
  by simp

private lemma pre_mangoldt_pos: "pre_mangoldt n > 0"
  unfolding pre_mangoldt_def by (auto simp: primepow_gt_Suc_0)

private lemma psi_conv_pre_mangoldt: "psi n = ln (real (prod pre_mangoldt {1..n}))"
  by (auto simp: psi_def mangoldt_def pre_mangoldt_def ln_prod primepow_gt_Suc_0 intro!: sum.cong)

private lemma eval_psi_aux1: "psi 0 = ln (real (numeral Num.One))"
  by (simp add: psi_def)

private lemma eval_psi_aux2:
  assumes "psi m = ln (real (numeral x))" "pre_mangoldt n = y" "m + 1 = n" "numeral x * y = z"
  shows   "psi n = ln (real z)"
proof -
  from assms(2) [symmetric] have [simp]: "y > 0" by (simp add: pre_mangoldt_pos)
  have "psi n = psi (Suc m)" by (simp add: assms(3) [symmetric])
  also have "\<dots> = ln (real y * (\<Prod>x = Suc 0..m. real (pre_mangoldt x)))"
    using assms(2,3) [symmetric] by (simp add: psi_conv_pre_mangoldt prod_nat_ivl_Suc' mult_ac)
  also have "\<dots> = ln (real y) + psi m"
    by (subst ln_mult) (simp_all add: pre_mangoldt_pos prod_pos psi_conv_pre_mangoldt)
  also have "psi m = ln (real (numeral x))" by fact
  also have "ln (real y) + \<dots> = ln (real (numeral x * y))" by (simp add: ln_mult)
  finally show ?thesis by (simp add: assms(4) [symmetric])
qed

private lemma Ball_atLeast0AtMost_doubleton:
  assumes "psi 0 \<le> 3 / 2 * ln 2 * real 0"
  assumes "psi 1 \<le> 3 / 2 * ln 2 * real 1"
  shows   "(\<forall>x\<in>{0..1}. psi x \<le> 3 / 2 * ln 2 * real x)"
  using assms unfolding One_nat_def atLeast0_atMost_Suc ball_simps by auto

private lemma Ball_atLeast0AtMost_insert:
  assumes "(\<forall>x\<in>{0..m}. psi x \<le> 3 / 2 * ln 2 * real x)"
  assumes "psi (numeral n) \<le> 3 / 2 * ln 2 * real (numeral n)" "m = pred_numeral n"
  shows   "(\<forall>x\<in>{0..numeral n}. psi x \<le> 3 / 2 * ln 2 * real x)"
  using assms
  by (subst numeral_eq_Suc[of n], subst atLeast0_atMost_Suc,
      subst ball_simps, simp only: numeral_eq_Suc [symmetric])

private lemma eval_psi_ineq_aux:
  assumes "psi n = x" "x \<le> 3 / 2 * ln 2 * n"
  shows   "psi n \<le> 3 / 2 * ln 2 * n"
  using assms by simp_all

ML_file \<open>bertrand.ML\<close>

(* This should not take more than a few seconds *)
local_setup \<open> fn ctxt =>
let
  fun tac {context = ctxt, ...} =
    let
      val psi_cache = Bertrand.prove_psi ctxt 129
      fun prove_psi_ineqs ctxt cache =
        let
          fun tac {context = ctxt, ...} = 
            HEADGOAL (Approximation.approximation_tac 12 [] NONE ctxt)
          fun prove (_, _, thm) =
            let
              val thm = thm RS @{thm eval_psi_ineq_aux}
              val [prem] = Thm.prems_of thm
              val prem = Goal.prove ctxt [] [] prem tac
            in
              prem RS thm
            end
        in
          cache |> map prove
        end
      val psi_ineqs = prove_psi_ineqs ctxt psi_cache
      fun prove_ball ctxt (thm1 :: thm2 :: thms) =
            let
              val thm = @{thm Ball_atLeast0AtMost_doubleton} OF [thm1, thm2]
              fun solve_prem thm =
                let
                  fun tac {context = ctxt, ...} = HEADGOAL (Simplifier.simp_tac ctxt)
                  val thm' = Goal.prove ctxt [] [] (Thm.cprem_of thm 1 |> Thm.term_of) tac
                in
                  thm' RS thm
                end
              fun go thm thm' = (@{thm Ball_atLeast0AtMost_insert} OF [thm', thm]) |> solve_prem
            in
              fold go thms thm
            end
        | prove_ball _ _ = raise Match
    in
      HEADGOAL (resolve_tac ctxt [prove_ball ctxt psi_ineqs])
    end
  val thm = Goal.prove @{context} [] [] @{prop "\<forall>n\<in>{0..128}. psi n \<le> 3 / 2 * ln 2 * n"} tac
in
  Local_Theory.note ((@{binding psi_ubound_log_128}, []), [thm]) ctxt |> snd
end
\<close>

end


context
begin
  
private lemma psi_ubound_aux:
  defines "f \<equiv> \<lambda>x::real. (4 * ln x + 3) / (ln 2 * x)"
  assumes "x \<ge> 2" "x \<le> y"
  shows   "f x \<ge> f y"
using assms(3)
proof (rule DERIV_nonpos_imp_nonincreasing, clarify, goal_cases)
  case (1 t)
  define f' where "f' = (\<lambda>x. (1 - 4 * ln x) / x^2 / ln 2 :: real)"
  from 1 assms(2) have "(f has_real_derivative f' t) (at t)" unfolding f_def f'_def
    by (auto intro!: derivative_eq_intros simp: field_simps power2_eq_square)
  moreover {
    have "1/4 \<le> ln (2::real)" by (approximation 5)
    also from assms(2) 1 have "\<dots> \<le> ln t" by simp
    finally have "ln t \<ge> 1/4" .
  }
  with 1 assms(2) have "f' t \<le> 0" by (simp add: f'_def field_simps)
  ultimately show ?case by (intro exI[of _ "f' t"]) simp_all
qed  

text \<open>
  These next rules are used in combination with @{thm psi_bounds_induct} and 
  @{thm psi_ubound_log_128} to extend the upper bound for @{term "psi"} from values no greater 
  than 128 to values no greater than 1024. The constant factor of the upper bound changes every 
  time, but once we have reached 1024, the recurrence is self-sustaining in the sense that we do 
  not have to adjust the constant factor anymore in order to double the range.
\<close>
lemma psi_ubound_log_double_cases':
  assumes "\<And>n. n \<le> m \<Longrightarrow> psi n \<le> c * ln 2 * real n" "n \<le> m'" "m' = 2*m"
          "c \<le> c'" "c \<ge> 0" "m \<ge> 1" "c' \<ge> 1 + c/2 + (4 * ln (m+1) + 3) / (ln 2 * (m+1))"
  shows   "psi n \<le> c' * ln 2 * real n"
proof (cases "n > m")
  case False
  hence "psi n \<le> c * ln 2 * real n" by (intro assms) simp_all
  also have "c \<le> c'" by fact
  finally show ?thesis by - (simp_all add: mult_right_mono)
next
  case True
  hence n: "n \<ge> m+1" by simp
  from psi_bounds_induct(2)[of n] True
    have "psi n \<le> real n * ln 2 + 4 * ln (real n) + 3 + psi (n div 2)" by simp
  also from assms have "psi (n div 2) \<le> c * ln 2 * real (n div 2)" 
    by (intro assms) simp_all
  also have "real (n div 2) \<le> real n / 2" by simp
  also have "c * ln 2 * \<dots> = c / 2 * ln 2 * real n" by simp
  also have "real n * ln 2 + 4 * ln (real n) + 3 + \<dots> = 
               (1 + c/2) * ln 2 * real n + (4 * ln (real n) + 3)" by (simp add: field_simps)
  also {
    have "(4 * ln (real n) + 3) / (ln 2 * (real n)) \<le> (4 * ln (m+1) + 3) / (ln 2 * (m+1))"
      using n assms by (intro psi_ubound_aux) simp_all
    also from assms have "(4 * ln (m+1) + 3) / (ln 2 * (m+1)) \<le> c' - 1 - c/2" 
      by (simp add: algebra_simps)
    finally have "4 * ln (real n) + 3 \<le> (c' - 1 - c/2) * ln 2 * real n" 
      using n by (simp add: field_simps)
  }
  also have "(1 + c / 2) * ln 2 * real n + (c' - 1 - c / 2) * ln 2 * real n = c' * ln 2 * real n"
    by (simp add: field_simps)
  finally show ?thesis using \<open>c \<ge> 0\<close> by (simp_all add: mult_left_mono)
qed

end  

lemma psi_ubound_log_double_cases:
  assumes "\<forall>n\<le>m. psi n \<le> c * ln 2 * real n"
          "c' \<ge> 1 + c/2 + (4 * ln (m+1) + 3) / (ln 2 * (m+1))"
          "m' = 2*m" "c \<le> c'" "c \<ge> 0" "m \<ge> 1" 
  shows   "\<forall>n\<le>m'. psi n \<le> c' * ln 2 * real n"
  using assms(1) by (intro allI impI assms psi_ubound_log_double_cases'[of m c _ m' c']) auto

lemma psi_ubound_log_1024:
  "\<forall>n\<le>1024. psi n \<le> 551 / 256 * ln 2 * real n"
proof -
  from psi_ubound_log_128 have "\<forall>n\<le>128. psi n \<le> 3 / 2 * ln 2 * real n" by simp
  hence "\<forall>n\<le>256. psi n \<le> 1025 / 512 * ln 2 * real n"
    by (rule psi_ubound_log_double_cases) (approximation 10, simp_all)
  hence "\<forall>n\<le>512. psi n \<le> 549 / 256 * ln 2 * real n"
    by (rule psi_ubound_log_double_cases) (approximation 10, simp_all)
  thus "\<forall>n\<le>1024. psi n \<le> 551 / 256 * ln 2 * real n"
    by (rule psi_ubound_log_double_cases) (approximation 10, simp_all)
qed  
  
lemma psi_bounds_sustained_induct:
  assumes "4 * ln (1 + 2 ^ j) + 3 \<le> d * ln 2 * (1 + 2^j)"
  assumes "4 / (1 + 2^j) \<le> d * ln 2"
  assumes "0 \<le> c"
  assumes "c / 2 + d + 1 \<le> c"
  assumes "j \<le> k"
  assumes "\<And>n. n \<le> 2^k \<Longrightarrow> psi n \<le> c * ln 2 * n"
  assumes "n \<le> 2^(Suc k)"
  shows "psi n \<le> c * ln 2 * n"
proof (cases "n \<le> 2^k")
  case True
  with assms(6) show ?thesis .
next
  case False
  from psi_bounds_induct(2) 
    have "psi n - psi (n div 2) \<le> real n * ln 2 + (4 * ln (real (if n = 0 then 1 else n)) + 3)" .
  also from False have "(if n = 0 then 1 else n) = n"
    by simp
  finally have "psi n \<le> real n * ln 2 + (4 * ln (real n) + 3) + psi (n div 2)"
    by simp
  also from assms(6,7) have "psi (n div 2) \<le> c * ln 2 * (n div 2)"
    by simp
  also have "real (n div 2) \<le> real n / 2"
    by simp
  also have "real n * ln 2 + (4 * ln (real n) + 3) + c * ln 2 * (n / 2) \<le> c * ln 2 * real n"
    proof (rule overpower_lemma[of
            "\<lambda>x. x * ln 2 + (4 * ln x + 3) + c * ln 2 * (x / 2)" "1+2^j"
            "\<lambda>x. c * ln 2 * x" "\<lambda>x. c * ln 2 - ln 2 - 4 / x - c / 2 * ln 2"
            "real n"])
      from assms(1) have "4 * ln (1 + 2^j) + 3 \<le> d * ln 2 * (1 + 2^j)" .
      also from assms(4) have "d \<le> c - c/2 - 1"
        by simp
      also have "(\<dots>) * ln 2 * (1 + 2 ^ j) = c * ln 2 * (1 + 2 ^ j) - c / 2 * ln 2 * (1 + 2 ^ j)
          - (1 + 2 ^ j) * ln 2"
        by (simp add: left_diff_distrib)
      finally have "4 * ln (1 + 2^j) + 3 \<le> c * ln 2 * (1 + 2 ^ j) - c / 2 * ln 2 * (1 + 2 ^ j)
          - (1 + 2 ^ j) * ln 2"
        by (simp add: add_pos_pos)
      then show "(1 + 2 ^ j) * ln 2 + (4 * ln (1 + 2 ^ j) + 3)
                    + c * ln 2 * ((1 + 2 ^ j) / 2) \<le> c * ln 2 * (1 + 2 ^ j)"
        by simp
    next
      fix x::real
      assume x: "1 + 2^j \<le> x"
      moreover have "1 + 2 ^ j > (0::real)" by (simp add: add_pos_pos)
      ultimately have x_pos: "x > 0" by linarith
      show "((\<lambda>x. c * ln 2 * x - (x * ln 2 + (4 * ln x + 3) + c * ln 2 * (x / 2)))
              has_real_derivative c * ln 2 - ln 2 - 4 / x - c / 2 * ln 2) (at x)"
        by (rule derivative_eq_intros refl | simp add: \<open>0 < x\<close>)+
      from \<open>0 < x\<close> \<open>0 < 1 + 2^j\<close> have "0 < x * (1 + 2^j)"
        by (rule mult_pos_pos)
      have "4 / x \<le> 4 / (1 + 2^j)"
        by (intro divide_left_mono mult_pos_pos add_pos_pos x x_pos) simp_all
      also from assms(2) have "4 / (1 + 2^j) \<le> d * ln 2" .
      also from assms(4) have "d \<le> c - c/2 - 1" by simp
      also have "\<dots> * ln 2 = c * ln 2 - c/2 * ln 2 - ln 2" by (simp add: algebra_simps)
      finally show "0 \<le> c * ln 2 - ln 2 - 4 / x - c / 2 * ln 2" by simp
    next
      have "1 + 2^j = real (1 + 2^j)" by simp
      also from assms(5) have "\<dots> \<le> real (1 + 2^k)" by simp
      also from False have "2^k \<le> n - 1" by simp
      finally show "1 + 2^j \<le> real n" using False by simp 
    qed
    finally show ?thesis using assms by - (simp_all add: mult_left_mono)
qed

lemma psi_bounds_sustained:
  assumes "\<And>n. n \<le> 2^k \<Longrightarrow> psi n \<le> c * ln 2 * n"
  assumes "4 * ln (1 + 2^k) + 3 \<le> (c/2 - 1) * ln 2 * (1 + 2^k)"
  assumes "4 / (1 + 2^k) \<le> (c/2 - 1) * ln 2"
  assumes "c \<ge> 0"
  shows "psi n \<le> c * ln 2 * n"
proof -
  have *: "psi n \<le> c * ln 2 * n" if "n \<le> 2^j" for j n
  using that
  proof (induction j arbitrary: n)
    case 0
    with assms(4) 0 show ?case unfolding psi_def mangoldt_def by (cases n) auto
  next
    case (Suc j)
    show ?case
      proof (cases "k \<le> j")
        case True
        from assms(4) have c_div_2: "c/2 + (c/2 - 1) + 1 \<le> c"
          by simp
        from psi_bounds_sustained_induct[of k "c/2 -1" c j,
             OF assms(2) assms(3) assms(4) c_div_2 True Suc.IH Suc.prems]
          show ?thesis by simp
      next
        case False
        then have j_lt_k: "Suc j \<le> k" by simp
        from Suc.prems have "n \<le> 2 ^ Suc j" .
        also have "(2::nat) ^ Suc j \<le> 2 ^ k"
          using power_increasing[of "Suc j" k "2::nat", OF j_lt_k]
          by simp
        finally show ?thesis using assms(1) by simp
      qed
    qed
    have "n < 2 ^ n" by (induction n) simp_all
    with *[of n n] show ?thesis by simp
qed

lemma psi_ubound_log: "psi n \<le> 551 / 256 * ln 2 * n"
proof (rule psi_bounds_sustained)
  show "0 \<le> 551 / (256 :: real)" by simp
next
  fix n :: nat assume "n \<le> 2 ^ 10"
  with psi_ubound_log_1024 show "psi n \<le> 551 / 256 * ln 2 * real n" by auto
qed (approximation 5)+

lemma psi_ubound_3_2: "psi n \<le> 3/2 * n"
proof -
  have "551 / 256 * ln 2 \<le> 3/(2::real)" by (approximation 10)
  with of_nat_0_le_iff mult_right_mono have "551 / 256 * ln 2 * n \<le> 3/2 * n"
    by blast
  with psi_ubound_log[of "n"] show ?thesis
    by linarith
qed


subsection \<open>Doubling psi and theta\<close>  

lemma psi_residues_compare_2:
  "psi_odd_2 n \<le> psi_even_2 n"
proof -
  have "psi_odd_2 n = (\<Sum>d\<in>{d. d \<in> {2..n} \<and> primepow_odd d}. mangoldt_odd d)"
    unfolding mangoldt_odd_def by (rule sum.mono_neutral_right) auto
  also have "\<dots> = (\<Sum>d\<in>{d. d \<in> {2..n} \<and> primepow_odd d}. ln (real (aprimedivisor d)))"
    by (intro sum.cong refl) (simp add: mangoldt_odd_def)
  also have "\<dots> \<le> (\<Sum>d\<in>{d. d \<in> {2..n} \<and> primepow_even d}. ln (real (aprimedivisor d)))"
  proof (rule sum_le_included [where i = "\<lambda>y. y * aprimedivisor y"]; clarify?)
    fix d :: nat assume "d \<in> {2..n}" "primepow_odd d"
    note d = this
    then obtain p k where d': "k \<ge> 1" "prime p" "d = p ^ (2*k+1)" 
      by (auto simp: primepow_odd_def)
    from d' have "p ^ (2 * k) \<le> p ^ (2 * k + 1)" 
      by (subst power_increasing_iff) (auto simp: prime_gt_Suc_0_nat)
    also from d d' have "\<dots> \<le> n" by simp
    finally have "p ^ (2 * k) \<le> n" .
    moreover from d' have "p ^ (2 * k) > 1" 
      by (intro one_less_power) (simp_all add: prime_gt_Suc_0_nat)
    ultimately have "p ^ (2 * k) \<in> {2..n}" by simp
    moreover from d' have "primepow_even (p ^ (2 * k))"
      by (auto simp: primepow_even_def)
    ultimately show "\<exists>y\<in>{d \<in> {2..n}. primepow_even d}. y * aprimedivisor y = d \<and>
                       ln (real (aprimedivisor d)) \<le> ln (real (aprimedivisor y))" using d'
      by (intro bexI[of _ "p ^ (2 * k)"])
         (auto simp: aprimedivisor_prime_power aprimedivisor_primepow)
  qed (simp_all add: of_nat_ge_1_iff Suc_le_eq)
  also have "\<dots> = (\<Sum>d\<in>{d. d \<in> {2..n} \<and> primepow_even d}. mangoldt_even d)"
    by (intro sum.cong refl) (simp add: mangoldt_even_def)
  also have "\<dots> = psi_even_2 n"
    unfolding mangoldt_even_def by (rule sum.mono_neutral_left) auto
  finally show ?thesis .
qed

lemma psi_residues_compare:
  "psi_odd n \<le> psi_even n"
proof -
  have "\<not> primepow_odd 1" by (simp add: primepow_odd_def)
  hence *: "mangoldt_odd 1 = 0" by (simp add: mangoldt_odd_def)
  have "\<not> primepow_even 1"
    using primepow_gt_Suc_0[OF primepow_even_imp_primepow, of 1] by auto
  with mangoldt_even_def have **: "mangoldt_even 1 = 0"
    by simp
  from psi_odd_def have "psi_odd n = (\<Sum>d=1..n. mangoldt_odd d)"
    by simp
  also from * have "\<dots> = psi_odd_2 n"
    by (cases "n \<ge> 1") (simp_all add: eval_nat_numeral sum_head_Suc)
  also from psi_residues_compare_2 have "\<dots> \<le> psi_even_2 n" .
  also from ** have "\<dots> = psi_even n"
    by (cases "n \<ge> 1") (simp_all add: eval_nat_numeral sum_head_Suc psi_even_def)
  finally show ?thesis .
qed

lemma primepow_iff_even_sqr:
  "primepow n \<longleftrightarrow> primepow_even (n^2)"
  by (auto simp: primepow_even_altdef aprimedivisor_primepow_power primepow_power_iff
                 prime_elem_multiplicity_power_distrib prime_aprimedivisor prime_imp_prime_elem
           dest: primepow_gt_Suc_0)

lemma psi_sqrt: "psi (Discrete.sqrt n) = psi_even n"
proof (induction n)
  case 0
  with psi_def psi_even_def show ?case by simp
next
  case (Suc n)
  then show ?case
    proof cases
      assume asm: "\<exists> m. Suc n = m^2"
      with sqrt_Suc have sqrt_seq: "Discrete.sqrt(Suc n) = Suc(Discrete.sqrt n)"
        by simp
      from asm obtain "m" where "   Suc n = m^2"
        by blast
      with sqrt_seq have "Suc(Discrete.sqrt n) = m"
        by simp
      with \<open>Suc n = m^2\<close> have suc_sqrt_n_sqrt: "(Suc(Discrete.sqrt n))^2 = Suc n"
        by simp
      from sqrt_seq have "psi (Discrete.sqrt (Suc n)) = psi (Suc (Discrete.sqrt n))"
        by simp
      also from psi_def have "\<dots> = psi (Discrete.sqrt n) + mangoldt (Suc (Discrete.sqrt n))"
        by simp
      also from Suc.IH have "psi (Discrete.sqrt n) = psi_even n" .
      also have "mangoldt (Suc (Discrete.sqrt n)) = mangoldt_even (Suc n)"
      proof (cases "primepow (Suc(Discrete.sqrt n))")
        case True
        with primepow_iff_even_sqr have True2: "primepow_even ((Suc(Discrete.sqrt n))^2)"
          by simp
        from suc_sqrt_n_sqrt have "mangoldt_even (Suc n) = mangoldt_even ((Suc(Discrete.sqrt n))^2)"
          by simp
        also from mangoldt_even_def True2
          have "\<dots> = ln (aprimedivisor ((Suc (Discrete.sqrt n))^2))"
          by simp
        also from True have "aprimedivisor ((Suc (Discrete.sqrt n))^2) = aprimedivisor (Suc (Discrete.sqrt n))"
          by (simp add: aprimedivisor_primepow_power)
        also from True mangoldt_def
          have "ln (\<dots>) = mangoldt (Suc (Discrete.sqrt n))"
          by simp
        finally show ?thesis ..
      next
        case False
        with primepow_iff_even_sqr
          have False2: "\<not> primepow_even ((Suc(Discrete.sqrt n))^2)"
          by simp
        from suc_sqrt_n_sqrt have "mangoldt_even (Suc n) = mangoldt_even ((Suc(Discrete.sqrt n))^2)"
          by simp
        also from mangoldt_even_def False2
          have "\<dots> = 0"
          by simp
        also from False mangoldt_def
          have "\<dots> = mangoldt (Suc (Discrete.sqrt n))"
          by simp
        finally show ?thesis ..
      qed  
      also from psi_even_def have "psi_even n + mangoldt_even (Suc n) = psi_even (Suc n)"
        by simp
      finally show ?case .
    next
      assume asm: "\<not>(\<exists>m. Suc n = m^2)"
      with sqrt_Suc have sqrt_eq: "Discrete.sqrt (Suc n) = Discrete.sqrt n"
        by simp
      then have lhs: "psi (Discrete.sqrt (Suc n)) = psi (Discrete.sqrt n)"
        by simp
      have "\<not> primepow_even (Suc n)"
        proof
          assume "primepow_even (Suc n)"
          with primepow_even_def obtain "p" "k"
            where "1 \<le> k \<and> prime p \<and> Suc n = p ^ (2 * k)" 
            by blast
          with power_even_eq have "Suc n = (p ^ k)^2"
            by simp
          with asm show False by blast
        qed
      with psi_even_def mangoldt_even_def
        have rhs: "psi_even (Suc n) = psi_even n"
        by simp
      from Suc.IH lhs rhs show ?case
        by simp
    qed
qed

lemma mangoldt_split:
  "mangoldt d = mangoldt_1 d + mangoldt_even d + mangoldt_odd d"
proof (cases "primepow d")
  case False
  thus ?thesis
    by (auto simp: mangoldt_def mangoldt_1_def mangoldt_even_def mangoldt_odd_def
             dest: primepow_even_imp_primepow primepow_odd_imp_primepow)
next
  case True
  thus ?thesis
    by (auto simp: mangoldt_def mangoldt_1_def mangoldt_even_def mangoldt_odd_def primepow_cases)
qed

lemma psi_split: "psi n = theta n + psi_even n + psi_odd n"
  by (induction n) 
     (simp_all add: psi_def theta_def psi_even_def psi_odd_def mangoldt_1_def mangoldt_split)

lemma psi_mono: "m \<le> n \<Longrightarrow> psi m \<le> psi n"
  using mangoldt_pos sum_mono2[of "{1..n}" "{1..m}" "mangoldt"] by (simp add: psi_def)

lemma psi_pos: "0 \<le> psi n"
  by (auto simp: psi_def intro!: sum_nonneg mangoldt_pos)

lemma mangoldt_odd_pos: "0 \<le> mangoldt_odd d"
  using aprimedivisor_gt_Suc_0[of d]
  by (auto simp: mangoldt_odd_def of_nat_le_iff[of 1, unfolded of_nat_1]
           simp del: aprimedivisor_gt_Suc_0 intro!: ln_ge_zero 
           dest!: primepow_odd_imp_primepow primepow_gt_Suc_0)

lemma psi_odd_mono: "m \<le> n \<Longrightarrow> psi_odd m \<le> psi_odd n"
  using mangoldt_odd_pos sum_mono2[of "{1..n}" "{1..m}" "mangoldt_odd"] 
  by (simp add: psi_odd_def)

lemma psi_odd_pos: "0 \<le> psi_odd n"
  by (auto simp: psi_odd_def intro!: sum_nonneg mangoldt_odd_pos)

lemma psi_theta:
  "theta n + psi (Discrete.sqrt n) \<le> psi n" "psi n \<le> theta n + 2 * psi (Discrete.sqrt n)"
  using psi_odd_pos[of n] psi_residues_compare[of n] psi_sqrt[of n] psi_split[of n]
  by simp_all

context
begin

private lemma sum_minus_one: 
  "(\<Sum>x \<in> {1..y}. (- 1 :: real) ^ (x + 1)) = (if odd y then 1 else 0)"
  by (induction y) simp_all
  
private lemma div_invert:
  fixes x y n :: nat
  assumes "x > 0" "y > 0" "y \<le> n div x"
  shows "x \<le> n div y"
proof -
  from assms(1,3) have "y * x \<le> (n div x) * x"
    by simp
  also have "\<dots> \<le> n"
    by (simp add: minus_mod_eq_div_mult[symmetric])
  finally have "y * x \<le> n" .
  with assms(2) show ?thesis
    using div_le_mono[of "y*x" n y] by simp
qed

lemma sum_expand_lemma:
  "(\<Sum>d=1..n. (-1) ^ (d + 1) * psi (n div d)) = 
     (\<Sum>d = 1..n. (if odd (n div d) then 1 else 0) * mangoldt d)"
proof -
  have **: "x \<le> n" if "x \<le> n div y" for x y
    using div_le_dividend order_trans that by blast
  have "(\<Sum>d=1..n. (-1)^(d+1) * psi (n div d)) = 
          (\<Sum>d=1..n. (-1)^(d+1) * (\<Sum>e=1..n div d. mangoldt e))"
    by (simp add: psi_def)
  also have "\<dots> = (\<Sum>d = 1..n. \<Sum>e = 1..n div d. (-1)^(d+1) * mangoldt e)"
    by (simp add: sum_distrib_left)
  also from ** have "\<dots> = (\<Sum>d = 1..n. \<Sum>e\<in>{y\<in>{1..n}. y \<le> n div d}. (-1)^(d+1) * mangoldt e)"
    by (intro sum.cong) auto
  also have "\<dots> = (\<Sum>y = 1..n. \<Sum>x | x \<in> {1..n} \<and> y \<le> n div x. (- 1) ^ (x + 1) * mangoldt y)"
    by (rule sum.commute_restrict) simp_all
  also have "\<dots> = (\<Sum>y = 1..n. \<Sum>x | x \<in> {1..n} \<and> x \<le> n div y. (- 1) ^ (x + 1) * mangoldt y)"
    by (intro sum.cong) (auto intro: div_invert)
  also from ** have "\<dots> = (\<Sum>y = 1..n. \<Sum>x \<in> {1..n div y}. (- 1) ^ (x + 1) * mangoldt y)"
    by (intro sum.cong) auto
  also have "\<dots> = (\<Sum>y = 1..n. (\<Sum>x \<in> {1..n div y}. (- 1) ^ (x + 1)) * mangoldt y)"
    by (intro sum.cong) (simp_all add: sum_distrib_right)
  also have "\<dots> = (\<Sum>y = 1..n. (if odd (n div y) then 1 else 0) * mangoldt y)"
    by (intro sum.cong refl) (simp_all only: sum_minus_one)
  finally show ?thesis .
qed

private lemma floor_half_interval:
  fixes n d :: nat
  assumes "d \<noteq> 0"
  shows "real (n div d) - real (2 * ((n div 2) div d)) = (if odd (n div d) then 1 else 0)"
proof -
  have "((n div 2) div d) = (n div (2 * d))"
    by (rule div_mult2_eq[symmetric])
  also have "\<dots> = ((n div d) div 2)"
    by (simp add: mult_ac div_mult2_eq)
  also have "real (n div d) - real (2 * \<dots>) = (if odd (n div d) then 1 else 0)"
    by (cases "odd (n div d)", cases "n div d = 0 ", simp_all)
  finally show ?thesis by simp
qed

lemma fact_expand_psi:
  "ln (fact n) - 2 * ln (fact (n div 2)) = (\<Sum>d=1..n. (-1)^(d+1) * psi (n div d))"
proof -
  have "ln (fact n) - 2 * ln (fact (n div 2)) =
    (\<Sum>d=1..n. mangoldt d * \<lfloor>n / d\<rfloor>) - 2 * (\<Sum>d=1..n div 2. mangoldt d * \<lfloor>(n div 2) / d\<rfloor>)"
    by (simp add:  ln_fact_conv_mangoldt)
  also have "(\<Sum>d=1..n div 2. mangoldt d * \<lfloor>real (n div 2) / d\<rfloor>) =
               (\<Sum>d=1..n. mangoldt d * \<lfloor>real (n div 2) / d\<rfloor>)"
    by (rule sum.mono_neutral_left) (auto simp: floor_unique[of 0])
  also have "2 * \<dots> = (\<Sum>d=1..n. mangoldt d * 2 * \<lfloor>real (n div 2) / d\<rfloor>)"
    by (simp add: sum_distrib_left mult_ac)
  also have "(\<Sum>d=1..n. mangoldt d * \<lfloor>n / d\<rfloor>) - \<dots> = 
               (\<Sum>d=1..n. (mangoldt d * \<lfloor>n / d\<rfloor> - mangoldt d * 2 * \<lfloor>real (n div 2) / d\<rfloor>))"
    by (simp add: sum_subtractf)
  also have "\<dots> = (\<Sum>d=1..n. mangoldt d * (\<lfloor>n / d\<rfloor> - 2 * \<lfloor>real (n div 2) / d\<rfloor>))"
    by (simp add: algebra_simps)
  also have "\<dots> = (\<Sum>d=1..n. mangoldt d * (if odd(n div d) then 1 else 0))"
    by (intro sum.cong refl)
       (simp_all add: floor_conv_div_nat [symmetric] floor_half_interval [symmetric])
  also have "\<dots> = (\<Sum>d=1..n. (if odd(n div d) then 1 else 0) * mangoldt d)"
    by (simp add: mult_ac)
  also from sum_expand_lemma[symmetric] have "\<dots> = (\<Sum>d=1..n. (-1)^(d+1) * psi (n div d))" .  
  finally show ?thesis .
qed
  
end

lemma psi_expansion_cutoff:
  assumes "m \<le> p"
  shows   "(\<Sum>d=1..2*m. (-1)^(d+1) * psi (n div d)) \<le> (\<Sum>d=1..2*p. (-1)^(d+1) * psi (n div d))"
          "(\<Sum>d=1..2*p+1. (-1)^(d+1) * psi (n div d)) \<le> (\<Sum>d=1..2*m+1. (-1)^(d+1) * psi (n div d))"
using assms
proof (induction m rule: inc_induct)
  case (step k)
  have "(\<Sum>d = 1..2 * k. (-1)^(d + 1) * psi (n div d)) \<le> 
          (\<Sum>d = 1..2 * Suc k. (-1)^(d + 1) * psi (n div d))"
    by (simp add: psi_mono div_le_mono2)
  with step.IH(1)
    show "(\<Sum>d = 1..2 * k. (-1)^(d + 1) * psi (n div d))
      \<le> (\<Sum>d = 1..2 * p. (-1)^(d + 1) * psi (n div d))"
      by simp
  from step.IH(2)
    have "(\<Sum>d = 1..2 * p + 1. (-1)^(d + 1) * psi (n div d))
      \<le> (\<Sum>d = 1..2 * Suc k + 1. (-1)^(d + 1) * psi (n div d))" .
  also have "\<dots> \<le> (\<Sum>d = 1..2 * k + 1. (-1)^(d + 1) * psi (n div d))"
    by (simp add: psi_mono div_le_mono2)
  finally show "(\<Sum>d = 1..2 * p + 1. (-1)^(d + 1) * psi (n div d))
       \<le> (\<Sum>d = 1..2 * k + 1. (-1)^(d + 1) * psi (n div d))" .
qed simp_all

lemma fact_psi_bound_even:
  assumes "even k"
  shows   "(\<Sum>d=1..k. (-1)^(d+1) * psi (n div d)) \<le> ln (fact n) - 2 * ln (fact (n div 2))"
proof -
  have "(\<Sum>d=1..k. (-1)^(d+1) * psi (n div d)) \<le> (\<Sum>d = 1..n. (- 1) ^ (d + 1) * psi (n div d))"
  proof (cases "k \<le> n")
    case True
    with psi_expansion_cutoff(1)[of "k div 2" "n div 2" n]
      have "(\<Sum>d=1..2*(k div 2). (-1)^(d+1) * psi (n div d))
        \<le> (\<Sum>d = 1..2*(n div 2). (- 1) ^ (d + 1) * psi (n div d))"
      by simp
    also from assms have "2*(k div 2) = k"
      by simp
    also have "(\<Sum>d = 1..2*(n div 2). (- 1) ^ (d + 1) * psi (n div d))
      \<le> (\<Sum>d = 1..n. (- 1) ^ (d + 1) * psi (n div d))"
    proof (cases "even n")
      case True
      then show ?thesis
        by simp
    next
      case False
      from psi_pos have "(\<Sum>d = 1..2*(n div 2). (- 1) ^ (d + 1) * psi (n div d))
          \<le> (\<Sum>d = 1..2*(n div 2) + 1. (- 1) ^ (d + 1) * psi (n div d))"
        by simp
      with False show ?thesis
        by simp
    qed
    finally show ?thesis .
  next
    case False
    hence *: "n div 2 \<le> (k-1) div 2"
      by simp
    have "(\<Sum>d=1..k. (-1)^(d+1) * psi (n div d)) \<le>
            (\<Sum>d=1..2*((k-1) div 2) + 1. (-1)^(d+1) * psi (n div d))"
    proof (cases "k = 0")
      case True
      with psi_pos show ?thesis by simp
    next
      case False
      with sum_cl_ivl_Suc[of "\<lambda>d. (-1)^(d+1) * psi (n div d)" 1 "k-1"]
      have "(\<Sum>d=1..k. (-1)^(d+1) * psi (n div d)) = (\<Sum>d=1..k-1. (-1)^(d+1) * psi (n div d))
          + (-1)^(k+1) * psi (n div k)"
        by simp
      also from assms psi_pos have "(-1)^(k+1) * psi (n div k) \<le> 0"
        by simp
      also from assms False have "k-1 = 2*((k-1) div 2) + 1"
        by presburger
      finally show ?thesis by simp
    qed
    also from * psi_expansion_cutoff(2)[of "n div 2" "(k-1) div 2" n]
      have "\<dots> \<le> (\<Sum>d=1..2*(n div 2) + 1. (-1)^(d+1) * psi (n div d))" by blast
    also have "\<dots> \<le> (\<Sum>d = 1..n. (- 1) ^ (d + 1) * psi (n div d))"
      by (cases "even n") (simp_all add: psi_def)
    finally show ?thesis .
  qed
  also from fact_expand_psi have "\<dots> = ln (fact n) - 2 * ln (fact (n div 2))" ..
  finally show ?thesis .
qed

lemma fact_psi_bound_odd:
  assumes "odd k"
  shows "ln (fact n) - 2 * ln (fact (n div 2)) \<le> (\<Sum>d=1..k. (-1)^(d+1) * psi (n div d))"
proof -
  from fact_expand_psi 
    have "ln (fact n) - 2 * ln (fact (n div 2)) = (\<Sum>d = 1..n. (- 1) ^ (d + 1) * psi (n div d))" .
  also have "\<dots> \<le> (\<Sum>d=1..k. (-1)^(d+1) * psi (n div d))"
  proof (cases "k \<le> n")
    case True
    have "(\<Sum>d=1..n. (-1)^(d+1) * psi (n div d)) \<le> (
             \<Sum>d=1..2*(n div 2)+1. (-1)^(d+1) * psi (n div d))"
      by (cases "even n") (simp_all add: psi_pos)
    also from True assms psi_expansion_cutoff(2)[of "k div 2" "n div 2" n]
      have "\<dots> \<le> (\<Sum>d=1..k. (-1)^(d+1) * psi (n div d))"
        by simp
    finally show ?thesis .
  next
    case False
    have "(\<Sum>d=1..n. (-1)^(d+1) * psi (n div d)) \<le> (\<Sum>d=1..2*((n+1) div 2). (-1)^(d+1) * psi (n div d))"
      by (cases "even n") (simp_all add: psi_def)
    also from False assms psi_expansion_cutoff(1)[of "(n+1) div 2" "k div 2" n]
      have "(\<Sum>d=1..2*((n+1) div 2). (-1)^(d+1) * psi (n div d)) \<le> (\<Sum>d=1..2*(k div 2). (-1)^(d+1) * psi (n div d))"
        by simp
    also from assms have "\<dots> \<le> (\<Sum>d=1..k. (-1)^(d+1) * psi (n div d))"
      by (auto elim: oddE simp: psi_pos)
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

lemma fact_psi_bound_2_3:
  "psi n - psi (n div 2) \<le> ln (fact n) - 2 * ln (fact (n div 2))"
  "ln (fact n) - 2 * ln (fact (n div 2)) \<le> psi n - psi (n div 2) + psi (n div 3)"
proof -
  show "psi n - psi (n div 2) \<le> ln (fact n) - 2 * ln (fact (n div 2))" 
    by (rule psi_bounds_ln_fact (2))
next
  from fact_psi_bound_odd[of 3 n] have "ln (fact n) - 2 * ln (fact (n div 2))
  \<le> (\<Sum>d = 1..3. (- 1) ^ (d + 1) * psi (n div d))"
    by simp
  also have "\<dots> = psi n - psi (n div 2) + psi (n div 3)"
    by (simp add: sum_head_Suc numeral_2_eq_2)
  finally show "ln (fact n) - 2 * ln (fact (n div 2)) \<le> psi n - psi (n div 2) + psi (n div 3)" .
qed

lemma psi_double_lemma:
  assumes "n \<ge> 1200"
  shows "real n / 6 \<le> psi n - psi (n div 2)"
proof -
  from ln_fact_diff_bounds
    have "\<bar>ln (fact n) - 2 * ln (fact (n div 2)) - real n * ln 2\<bar>
        \<le> 4 * ln (real (if n = 0 then 1 else n)) + 3" .
  with assms have "ln (fact n) - 2 * ln (fact (n div 2))
        \<ge> real n * ln 2 - 4 * ln (real n) - 3"
    by simp
  moreover have "real n * ln 2 - 4 * ln (real n) - 3 \<ge> 2 / 3 * n"
  proof (rule overpower_lemma[of "\<lambda>n. 2/3 * n" 1200])
    show "2 / 3 * 1200 \<le> 1200 * ln 2 - 4 * ln 1200 - (3::real)"
      by (approximation 12)
  next
    fix x::real
    assume "1200 \<le> x"
    then have "0 < x"
      by simp
    show "((\<lambda>x. x * ln 2 - 4 * ln x - 3 - 2 / 3 * x)
        has_real_derivative ln 2 - 4 / x - 2 / 3) (at x)"
      by (rule derivative_eq_intros refl | simp add: \<open>0 < x\<close>)+
  next
    fix x::real
    assume "1200 \<le> x"
    then have "12 / x \<le> 12 / 1200"
      by simp
    then have "0 \<le> 0.67 - 4 / x - 2 / 3"
      by simp
    also have "0.67 \<le> ln (2::real)"
      by (approximation 6)
    finally show "0 \<le> ln 2 - 4 / x - 2 / 3"
      by simp
  next
    from assms show "1200 \<le> real n"
      by simp
  qed
  ultimately have "2 / 3 * real n \<le> ln (fact n) - 2 * ln (fact (n div 2))"
    by simp
  with psi_ubound_3_2[of "n div 3"]
    have "n/6 + psi (n div 3) \<le> ln (fact n) - 2 * ln (fact (n div 2))"
    by simp
  with fact_psi_bound_2_3[of "n"] show ?thesis
    by simp
qed

lemma theta_double_lemma:
  assumes "n \<ge> 1200"
  shows "theta (n div 2) < theta n"
proof -
  from psi_theta[of "n div 2"] psi_pos[of "Discrete.sqrt (n div 2)"]
    have theta_le_psi_n_2: "theta (n div 2) \<le> psi (n div 2)"
    by simp
  have "(Discrete.sqrt n * 18)^2 \<le> 324 * n"
    by simp
  from mult_less_cancel2[of "324" "n" "n"] assms have "324 * n < n^2"
    by (simp add: power2_eq_square)
  with \<open>(Discrete.sqrt n * 18)^2 \<le> 324 * n\<close> have "(Discrete.sqrt n*18)^2 < n^2"
    by presburger
  with power2_less_imp_less assms have "Discrete.sqrt n * 18 < n"
    by blast
  with psi_ubound_3_2[of "Discrete.sqrt n"] have "2 * psi (Discrete.sqrt n) < n / 6"
    by simp
  with psi_theta[of "n"] have psi_lt_theta_n: "psi n - n / 6 < theta n"
    by simp
  from psi_double_lemma[OF assms(1)] have "psi (n div 2) \<le> psi n - n / 6"
    by simp
  with theta_le_psi_n_2 psi_lt_theta_n show ?thesis
    by simp
qed
  

subsection \<open>Proof of the main result\<close>

lemma theta_mono: "mono theta"
  by (auto simp: theta_def [abs_def] intro!: monoI sum_mono3)
  
lemma theta_lessE:
  assumes "theta m < theta n" "m \<ge> 1"
  obtains p where "p \<in> {m<..n}" "prime p"
proof -
  from mono_invE[OF theta_mono assms(1)] have "m \<le> n" by blast
  hence "theta n = theta m + (\<Sum>p\<in>{m<..n}. if prime p then ln (real p) else 0)"
    unfolding theta_def using assms(2)
    by (subst sum.union_disjoint [symmetric]) (auto simp: ivl_disj_un)
  also note assms(1)
  finally have "(\<Sum>p\<in>{m<..n}. if prime p then ln (real p) else 0) \<noteq> 0" by simp
  from sum.not_neutral_contains_not_neutral [OF this] guess p .
  thus ?thesis using that[of p] by (auto intro!: exI[of _ p] split: if_splits)
qed

theorem bertrand:
  fixes   n :: nat
  assumes "n > 1"
  shows   "\<exists>p\<in>{n<..<2*n}. prime p"
proof cases
  assume n_less: "n < 600"
  define prime_constants
    where "prime_constants = {2, 3, 5, 7, 13, 23, 43, 83, 163, 317, 631::nat}"
  from \<open>n > 1\<close> n_less have "\<exists>p \<in> prime_constants. n < p \<and> p < 2 * n"
    unfolding bex_simps greaterThanLessThan_iff prime_constants_def by presburger
  moreover have "\<forall>p\<in>prime_constants. prime p" unfolding prime_constants_def by eval
  ultimately show ?thesis
    unfolding greaterThanLessThan_def greaterThan_def lessThan_def by blast
next
  assume n: "\<not>(n < 600)"
  from n have "theta n < theta (2 * n)" using theta_double_lemma[of "2 * n"] by simp
  with assms obtain p where "p \<in> {n<..2*n}" "prime p" by (auto elim!: theta_lessE)
  moreover from assms have "\<not>prime (2*n)" by (auto dest!: prime_product)
  with \<open>prime p\<close> have "p \<noteq> 2 * n" by auto
  ultimately show ?thesis by force
qed

end
