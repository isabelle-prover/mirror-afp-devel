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
  Archimedean_Field
  Real 
  Rat
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
  have "bb ^ n = inverse (b ^ n)" unfolding bb_def by (rule sym, rule power_inverse)
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

lemma set_upt_Suc: "{0 ..< Suc i} = insert i {0 ..< i}" by auto

lemma setprod_pow[simp]: "(\<Prod>i = 0..<n. p) = (p :: 'a :: comm_monoid_mult) ^ n"
  by (induct n, auto simp: set_upt_Suc)


text \<open>For determinant computation, we require the @{const div}-operation.
In order to also support rational and real numbers, we therefore provide the
following class which has both @{const div} and @{const divide}.\<close>

class ring_div_field = field + div +
  assumes div: "(op div :: 'a \<Rightarrow> 'a \<Rightarrow> 'a) = op /"
  and mod: "(x :: 'a) mod y = (if y = 0 then x else 0)"
begin

subclass ring_div
  by (unfold_locales, auto simp: div mod field_simps)

end

instantiation rat :: ring_div_field
begin
definition "div_rat = (op / :: rat \<Rightarrow> rat \<Rightarrow> rat)"
definition "mod_rat (x :: rat) (y :: rat) = (if y = 0 then x else 0)"
instance
  by (intro_classes, auto simp: div_rat_def mod_rat_def)
end

instantiation real :: ring_div_field
begin
definition "div_real = (op / :: real \<Rightarrow> real \<Rightarrow> real)"
definition "mod_real (x :: real) (y :: real) = (if y = 0 then x else 0)"
instance
  by (intro_classes, auto simp: div_real_def mod_real_def)
end

end