(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Missing Unsorted\<close>

text \<open>This theory contains several lemmas which might be of interest to the Isabelle distribution.
  For instance, we prove that $b^n \cdot n^k$ is bounded by a constant whenever $0 < b < 1$.\<close>

theory Missing_Unsorted
imports
  Complex
begin

lemma bernoulli_inequality: assumes x: "-1 \<le> (x :: 'a :: linordered_field)"
  shows "1 + of_nat n * x \<le> (1 + x) ^ n"
proof (induct n)
  case (Suc n)
  have "1 + of_nat (Suc n) * x = 1 + x + of_nat n * x" by (simp add: field_simps)
  also have "\<dots> \<le> \<dots> + of_nat n * x ^ 2" by simp
  also have "\<dots> = (1 + of_nat n * x) * (1 + x)" by (simp add: field_simps power2_eq_square)
  also have "\<dots> \<le> (1 + x) ^ n * (1 + x)"
    by (rule mult_right_mono[OF Suc], insert x, auto)
  also have "\<dots> = (1 + x) ^ (Suc n)" by simp
  finally show ?case .
qed simp

context
  fixes b :: "'a :: archimedean_field"
  assumes b: "0 < b" "b < 1"
begin
private lemma pow_one: "b ^ x \<le> 1" using power_Suc_less_one[OF b, of "x - 1"] by (cases x, auto)

private lemma pow_zero: "0 < b ^ x" using b(1) by simp

lemma exp_tends_to_zero: assumes c: "c > 0"
  shows "\<exists> x. b ^ x \<le> c" 
proof (rule ccontr)
  assume not: "\<not> ?thesis"
  def bb \<equiv> "inverse b"
  def cc \<equiv> "inverse c"
  from b have bb: "bb > 1" unfolding bb_def by (rule one_less_inverse)  
  from c have cc: "cc > 0" unfolding cc_def by simp
  def bbb \<equiv> "bb - 1"
  have id: "bb = 1 + bbb" and bbb: "bbb > 0" and bm1: "bbb \<ge> -1" unfolding bbb_def using bb by auto
  have "\<exists> n. cc / bbb < of_nat n" by (rule ex_less_of_nat)
  then obtain n where lt: "cc / bbb < of_nat n" by auto
  from not have "\<not> b ^ n \<le> c" by auto
  hence bnc: "b ^ n > c" by simp
  have "bb ^ n = inverse (b ^ n)" unfolding bb_def by (rule power_inverse)
  also have "\<dots> < cc" unfolding cc_def
    by (rule less_imp_inverse_less[OF bnc c])
  also have "\<dots> < bbb * of_nat n" using lt bbb by (metis mult.commute pos_divide_less_eq)
  also have "\<dots> \<le> bb ^ n"
    using bernoulli_inequality[OF bm1, folded id, of n] by (simp add: ac_simps)
  finally show False by simp
qed

lemma linear_exp_bound: "\<exists> p. \<forall> x. b ^ x * of_nat x \<le> p"
proof -
  from b have "1 - b > 0" by simp
  from exp_tends_to_zero[OF this]
  obtain x0 where x0: "b ^ x0 \<le> 1 - b" ..
  {
    fix x
    assume "x \<ge> x0"
    hence "\<exists> y. x = x0 + y" by arith
    then obtain y where x: "x = x0 + y" by auto
    have "b ^ x = b ^ x0 * b ^ y" unfolding x by (simp add: power_add)
    also have "\<dots> \<le> b ^ x0" using pow_one[of y] pow_zero[of x0] by auto
    also have "\<dots> \<le> 1 - b" by (rule x0)
    finally have "b ^ x \<le> 1 - b" .
  } note x0 = this
  def bs \<equiv> "insert 1 { b ^ Suc x * of_nat (Suc x) | x . x \<le> x0}"
  have bs: "finite bs" unfolding bs_def by auto
  def p \<equiv> "Max bs"
  have bs: "\<And> b. b \<in> bs \<Longrightarrow> b \<le> p" unfolding p_def using bs by simp
  hence p1: "p \<ge> 1" unfolding bs_def by auto
  show ?thesis
  proof (rule exI[of _ p], intro allI)
    fix x
    show "b ^ x * of_nat x \<le> p"
    proof (induct x)
      case (Suc x)
      show ?case
      proof (cases "x \<le> x0")
        case True
        show ?thesis 
          by (rule bs, unfold bs_def, insert True, auto)
      next
        case False
        let ?x = "of_nat x :: 'a"
        have "b ^ (Suc x) * of_nat (Suc x) = b * (b ^ x * ?x) + b ^ Suc x" by (simp add: field_simps)
        also have "\<dots> \<le> b * p + b ^ Suc x"
          by (rule add_right_mono[OF mult_left_mono[OF Suc]], insert b, auto)
        also have "\<dots> = p - ((1 - b) * p - b ^ (Suc x))" by (simp add: field_simps)
        also have "\<dots> \<le> p - 0"
        proof -
          have "b ^ Suc x \<le> 1 - b" using x0[of "Suc x"] False by auto
          also have "\<dots> \<le> (1 - b) * p" using b p1 by auto
          finally show ?thesis
            by (intro diff_left_mono, simp)
        qed
        finally show ?thesis by simp
      qed
    qed (insert p1, auto)
  qed
qed

lemma poly_exp_bound: "\<exists> p. \<forall> x. b ^ x * of_nat x ^ deg \<le> p" 
proof -
  show ?thesis
  proof (induct deg)
    case 0
    show ?case
      by (rule exI[of _ 1], intro allI, insert pow_one, auto)
  next
    case (Suc deg)
    then obtain q where IH: "\<And> x. b ^ x * (of_nat x) ^ deg \<le> q" by auto
    def p \<equiv> "max 0 q"
    from IH have IH: "\<And> x. b ^ x * (of_nat x) ^ deg \<le> p" unfolding p_def using le_max_iff_disj by blast
    have p: "p \<ge> 0" unfolding p_def by simp
    show ?case
    proof (cases "deg = 0")
      case True
      thus ?thesis using linear_exp_bound by simp
    next
      case False note deg = this
      def p' \<equiv> "p*p * 2 ^ Suc deg * inverse b"
      let ?f = "\<lambda> x. b ^ x * (of_nat x) ^ Suc deg"
      def f \<equiv> ?f
      {
        fix x
        let ?x = "of_nat x :: 'a"
        have "f (2 * x) \<le> (2 ^ Suc deg) * (p * p)"
        proof (cases "x = 0")
          case False
          hence x1: "?x \<ge> 1" by (cases x, auto)
          from x1 have x: "?x ^ (deg - 1) \<ge> 1" by simp
          from x1 have xx: "?x ^ Suc deg \<ge> 1" by (rule one_le_power)
          def c \<equiv> "b ^ x * b ^ x * (2 ^ Suc deg)"
          have c: "c > 0" unfolding c_def using b by auto
          have "f (2 * x) = ?f (2 * x)" unfolding f_def by simp
          also have "b ^ (2 * x) = (b ^ x) * (b ^ x)" by (simp add: power2_eq_square power_even_eq)
          also have "of_nat (2 * x) = 2 * ?x" by (simp add: of_nat_mult)
          also have "(2 * ?x) ^ Suc deg = 2 ^ Suc deg * ?x ^ Suc deg" by simp
          finally have "f (2 * x) = c * ?x ^ Suc deg" unfolding c_def by (simp add: ac_simps)
          also have "\<dots> \<le> c * ?x ^ Suc deg * ?x ^ (deg - 1)"
          proof -
            have "c * ?x ^ Suc deg > 0" using c xx by simp
            thus ?thesis unfolding mult_le_cancel_left1 using x by simp
          qed
          also have "\<dots> = c * ?x ^ (Suc deg + (deg - 1))" by (simp add: power_add)
          also have "Suc deg + (deg - 1) = deg + deg" using deg by simp
          also have "?x ^ (deg + deg) = (?x ^ deg) * (?x ^ deg)" by (simp add: power_add)
          also have "c * \<dots> = (2 ^ Suc deg) * ((b ^ x * ?x ^ deg) * (b ^ x * ?x ^ deg))" 
            unfolding c_def by (simp add: ac_simps)  
          also have "\<dots> \<le> (2 ^ Suc deg) * (p * p)"
            by (rule mult_left_mono[OF mult_mono[OF IH IH p]], insert pow_zero[of x], auto)
          finally show "f (2 * x) \<le> (2 ^ Suc deg) * (p * p)" .
        qed (auto simp: f_def)
        hence "?f (2 * x) \<le> (2 ^ Suc deg) * (p * p)" unfolding f_def .
      } note even = this
      show ?thesis
      proof (rule exI[of _ p'], intro allI)
        fix y
        show "?f y \<le> p'"
        proof (cases "even y")
          case True
          def x \<equiv> "y div 2"
          have "y = 2 * x" unfolding x_def using True by simp
          from even[of x, folded this] have "?f y \<le> 2 ^ Suc deg * (p * p)" .
          also have "\<dots> \<le> \<dots> * inverse b"
            unfolding mult_le_cancel_left1 using b p by (simp add:sign_simps one_le_inverse)
          also have "\<dots> = p'" unfolding p'_def by (simp add: ac_simps)
          finally show "?f y \<le> p'" .
        next
          case False
          def x \<equiv> "y div 2"
          have "y = 2 * x + 1" unfolding x_def using False by simp
          hence "?f y = ?f (2 * x + 1)" by simp
          also have "\<dots> \<le> b ^ (2 * x + 1) * of_nat (2 * x + 2) ^ Suc deg"
            by (rule mult_left_mono[OF power_mono], insert b, auto) 
          also have "b ^ (2 * x + 1) = b ^ (2 * x + 2) * inverse b" using b by auto
          also have "b ^ (2 * x + 2) * inverse b * of_nat (2 * x + 2) ^ Suc deg = 
            inverse b * ?f (2 * (x + 1))" by (simp add: ac_simps)
          also have "\<dots> \<le> inverse b * ((2 ^ Suc deg) * (p * p))"
            by (rule mult_left_mono[OF even], insert b, auto)
          also have "\<dots> = p'" unfolding p'_def by (simp add: ac_simps)
          finally show "?f y \<le> p'" .
        qed
      qed
    qed
  qed
qed
end

lemma listprod_replicate[simp]: "listprod (replicate n a) = a ^ n"
  by (induct n, auto)

lemma listprod_power: fixes xs :: "'a :: comm_monoid_mult list"
  shows "listprod xs ^ n = (\<Prod>x\<leftarrow>xs. x ^ n)"
  by (induct xs, auto simp: power_mult_distrib)

lemma set_upt_Suc: "{0 ..< Suc i} = insert i {0 ..< i}" by auto

lemma setprod_pow[simp]: "(\<Prod>i = 0..<n. p) = (p :: 'a :: comm_monoid_mult) ^ n"
  by (induct n, auto simp: set_upt_Suc)


text \<open>For determinant computation, we require the @{class ring_div}-class.
In order to also support rational and real numbers, we therefore provide the
following class which defines @{const mod} for fields and will be a subclass
of @{class ring_div}.\<close>

class ring_div_field = field + div +
  assumes mod: "(x :: 'a) mod y = (if y = 0 then x else 0)"
begin

subclass ring_div
  by (unfold_locales, auto simp: mod field_simps)

end

instantiation rat :: ring_div_field
begin
definition "mod_rat (x :: rat) (y :: rat) = (if y = 0 then x else 0)"
instance
  by (intro_classes, auto simp: mod_rat_def)
end

instantiation real :: ring_div_field
begin
definition "mod_real (x :: real) (y :: real) = (if y = 0 then x else 0)"
instance
  by (intro_classes, auto simp: mod_real_def)
end

instantiation complex :: ring_div_field
begin
definition "mod_complex (x :: complex) (y :: complex) = (if y = 0 then x else 0)"
instance
  by (intro_classes, auto simp: mod_complex_def)
end


(* GCD and LCM part *)

lemma dvd_abs_mult_left_int[simp]: "(abs (a :: int) * y dvd x) = (a * y dvd x)"
  by (simp add: GCD.dvd_int_iff nat_abs_mult_distrib)

lemma gcd_abs_mult_right_int[simp]: "gcd x (\<bar>a\<bar> * (y :: int)) = gcd x (a * y)" 
  by (simp add: gcd_int_def nat_abs_mult_distrib)

lemma lcm_abs_mult_right_int[simp]: "lcm x (\<bar>a\<bar> * (y :: int)) = lcm x (a * y)" 
  by (simp add: lcm_int_def nat_abs_mult_distrib)

lemma gcd_abs_mult_left_int[simp]: "gcd x (a * (abs y :: int)) = gcd x (a * y)" 
  by (simp add: gcd_int_def nat_abs_mult_distrib)

lemma lcm_abs_mult_left_int[simp]: "lcm x (a * (abs y :: int)) = lcm x (a * y)" 
  by (simp add: lcm_int_def nat_abs_mult_distrib)


definition list_gcd :: "'a :: semiring_gcd list \<Rightarrow> 'a" where
  "list_gcd xs \<equiv> foldr gcd xs 0"

definition list_lcm :: "'a :: semiring_gcd list \<Rightarrow> 'a" where
  "list_lcm xs \<equiv> foldr lcm xs 1"


lemma list_gcd_simps: "list_gcd [] = 0" "list_gcd (x # xs) = gcd x (list_gcd xs)"
  by (auto simp: list_gcd_def)

lemma list_gcd: "x \<in> set xs \<Longrightarrow> list_gcd xs dvd x" 
proof (induct xs)
  case (Cons y ys)
  show ?case
  proof (cases "x = y")
    case False
    with Cons have "list_gcd ys dvd x" by auto
    thus ?thesis unfolding list_gcd_simps using dvd_trans by blast
  next
    case True
    thus ?thesis unfolding list_gcd_simps using dvd_trans by blast
  qed
qed simp

lemma list_gcd_greatest: "(\<And> x. x \<in> set xs \<Longrightarrow> y dvd x) \<Longrightarrow> y dvd (list_gcd xs)"
proof (induct xs)
  case (Cons x xs)
  from Cons have "y dvd x" "y dvd (list_gcd xs)" by auto
  thus ?case unfolding list_gcd_simps by (rule gcd_greatest)
qed (simp add: list_gcd_simps)

lemma list_gcd_mult_int[simp]: fixes xs :: "int list"
  shows "list_gcd (map (op * a) xs) = \<bar>a\<bar> * list_gcd xs"
  by (induct xs, auto simp: list_gcd_simps gcd_mult_distrib_int)

lemma list_lcm_simps: "list_lcm [] = 1" "list_lcm (x # xs) = lcm x (list_lcm xs)"
  by (auto simp: list_lcm_def)

lemma list_lcm: "x \<in> set xs \<Longrightarrow> x dvd list_lcm xs" 
proof (induct xs)
  case (Cons y ys)
  have res: "list_lcm (y # ys) = lcm y (list_lcm ys)" unfolding list_lcm_def by simp
  show ?case
  proof (cases "x = y")
    case False
    with Cons have "x dvd list_lcm ys" by auto
    thus ?thesis unfolding list_lcm_simps by (rule dvd_lcmI2)
  qed (simp add: list_lcm_simps)
qed simp

lemma list_lcm_least: "(\<And> x. x \<in> set xs \<Longrightarrow> x dvd y) \<Longrightarrow> list_lcm xs dvd y"
proof (induct xs)
  case (Cons x xs)
  from Cons have "x dvd y" "list_lcm xs dvd y" by auto
  thus ?case unfolding list_lcm_simps by (rule lcm_least)
qed (simp add: list_lcm_simps)

lemma lcm_mult_distrib_nat: "(k :: nat) * lcm m n = lcm (k * m) (k * n)"
  unfolding lcm_nat_def gcd_mult_distrib_nat[symmetric]
  by (simp add: Divides.div_mult2_eq div_mult_swap mult.left_commute)

lemma lcm_mult_distrib_int: "abs (k::int) * lcm m n = lcm (k * m) (k * n)"
  unfolding lcm_int_def nat_mult_distrib[OF abs_ge_zero] abs_mult
  unfolding lcm_mult_distrib_nat[symmetric] by simp

lemma list_lcm_mult_int[simp]:
  "list_lcm (map (op * (a :: int)) xs) = (if xs = [] then 1 else \<bar>a\<bar> * list_lcm xs)"
  by (induct xs, auto simp: list_lcm_simps lcm_mult_distrib_int abs_mult)

lemma list_lcm_pos: "list_lcm xs \<ge> (0 :: int)" "0 \<notin> set xs \<Longrightarrow> list_lcm xs \<noteq> 0"
  "0 \<notin> set xs \<Longrightarrow> list_lcm xs > 0" 
proof -
  show ge: "list_lcm xs \<ge> 0"
    by (induct xs, auto simp: list_lcm_simps)
  assume "0 \<notin> set xs"
  thus neq: "list_lcm xs \<noteq> 0"
    by (induct xs, auto simp: list_lcm_simps)
  from ge neq show "list_lcm xs > 0" by auto
qed


lemma quotient_of_nonzero: "snd (quotient_of r) > 0" "snd (quotient_of r) \<noteq> 0"
  using quotient_of_denom_pos[of r] by (cases "quotient_of r", auto)+

lemma quotient_of_int_div: assumes q: "quotient_of (of_int x / of_int y) = (a, b)"
  and y: "y \<noteq> 0" 
  shows "\<exists> z. z \<noteq> 0 \<and> x = a * z \<and> y = b * z"
proof -
  let ?r = "rat_of_int"
  def z \<equiv> "gcd x y"
  def x' \<equiv> "x div z"
  def y' \<equiv> "y div z"
  have id: "x = z * x'" "y = z * y'" unfolding x'_def y'_def z_def by auto
  from y have y': "y' \<noteq> 0" unfolding id by auto
  have z: "z \<noteq> 0" unfolding z_def using y by auto
  have cop: "coprime x' y'" unfolding x'_def y'_def z_def 
    using div_gcd_coprime_int y by blast
  have "?r x / ?r y = ?r x' / ?r y'" unfolding id using z y y' by (auto simp: field_simps) 
  from assms[unfolded this] have quot: "quotient_of (?r x' / ?r y') = (a, b)" by auto
  from quotient_of_coprime[OF quot] have cop': "coprime a b" .
  hence cop: "coprime b a" by (simp add: gcd.commute)
  from quotient_of_denom_pos[OF quot] have b: "b > 0" "b \<noteq> 0" by auto
  from quotient_of_div[OF quot] quotient_of_denom_pos[OF quot] y'
  have "?r x' * ?r b = ?r a * ?r y'" by (auto simp: field_simps)
  hence id': "x' * b = a * y'" unfolding of_int_mult[symmetric] by linarith
  from id'[symmetric] have "b dvd y' * a" unfolding mult.commute[of y'] by auto
  with cop y' have "b dvd y'" by (metis coprime_dvd_mult_int)
  then obtain z' where ybz: "y' = b * z'" unfolding dvd_def by auto
  from id[unfolded y' this] have y: "y = b * (z * z')" by auto
  with `y \<noteq> 0` have zz: "z * z' \<noteq> 0" by auto
  from quotient_of_div[OF q] `y \<noteq> 0` `b \<noteq> 0` 
  have "?r x * ?r b = ?r y * ?r a" by (auto simp: field_simps)
  hence id': "x * b = y * a" unfolding of_int_mult[symmetric] by linarith
  from this[unfolded y] b have x: "x = a * (z * z')" by auto
  show ?thesis unfolding x y using zz by blast
qed

lemma listprod_zero_iff: "(listprod (xs :: 'a :: idom list) = 0) = (0 \<in> set xs)"
  by (induct xs, auto)

fun max_list_non_empty :: "('a :: linorder) list \<Rightarrow> 'a" where
  "max_list_non_empty [x] = x"
| "max_list_non_empty (x # xs) = max x (max_list_non_empty xs)"

lemma max_list_non_empty: "x \<in> set xs \<Longrightarrow> x \<le> max_list_non_empty xs"
proof (induct xs)
  case (Cons y ys) note oCons = this
  show ?case 
  proof (cases ys)
    case (Cons z zs)
    hence id: "max_list_non_empty (y # ys) = max y (max_list_non_empty ys)" by simp
    from oCons show ?thesis unfolding id by (auto simp: max.coboundedI2)
  qed (insert oCons, auto)
qed simp

lemma cnj_reals[simp]: "(cnj c \<in> \<real>) = (c \<in> \<real>)"
  using Reals_cnj_iff by fastforce

lemma sgn_real_mono: "x \<le> y \<Longrightarrow> sgn x \<le> sgn (y :: real)"
  unfolding sgn_real_def
  by (auto split: if_splits)

lemma sgn_minus_rat: "sgn (- (x :: rat)) = - sgn x"
  by (simp add: sgn_rat_def)

lemma real_of_rat_sgn: "sgn (of_rat x) = real_of_rat (sgn x)"
  unfolding sgn_real_def sgn_rat_def by auto

lemma inverse_sgn[simp]: "sgn (inverse a) = (sgn a :: real)"
  by (simp add: sgn_real_def)

lemma inverse_sgn_rat[simp]: "sgn (inverse a) = (sgn a :: rat)"
  by (simp add: sgn_rat_def)

lemma inverse_le_iff_sgn: assumes sgn: "sgn x = sgn y"
  shows "(inverse (x :: real) \<le> inverse y) = (y \<le> x)"
proof (cases "x = 0")
  case True
  with sgn have "sgn y = 0" by simp
  hence "y = 0" unfolding sgn_real_def by (cases "y = 0"; cases "y < 0"; auto)
  thus ?thesis using True by simp
next
  case False note x = this
  show ?thesis
  proof (cases "x < 0")
    case True
    with x sgn have "sgn y = -1" by simp
    hence "y < 0" unfolding sgn_real_def by (cases "y = 0"; cases "y < 0", auto)
    show ?thesis
      by (rule inverse_le_iff_le_neg[OF True `y < 0`])
  next
    case False
    with x have x: "x > 0" by auto
    with sgn have "sgn y = 1" by auto
    hence "y > 0" unfolding sgn_real_def by (cases "y = 0"; cases "y < 0", auto)
    show ?thesis
      by (rule inverse_le_iff_le[OF x `y > 0`])
  qed
qed

lemma inverse_le_sgn: assumes sgn: "sgn x = sgn y" and xy: "x \<le> (y :: real)"
  shows "inverse y \<le> inverse x"
  using xy inverse_le_iff_sgn[OF sgn] by auto

lemma set_list_update: "set (xs [i := k]) = 
  (if i < length xs then insert k (set (take i xs) \<union> set (drop (Suc i) xs)) else set xs)"
proof (induct xs arbitrary: i)
  case (Cons x xs i) 
  thus ?case
    by (cases i, auto)
qed simp

end