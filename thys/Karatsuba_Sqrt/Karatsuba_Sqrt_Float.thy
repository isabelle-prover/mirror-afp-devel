theory Karatsuba_Sqrt_Float
imports
  Karatsuba_Sqrt
  "HOL-Library.Interval_Float"
begin

subsection \<open>Floating-point approximation of \<^const>\<open>sqrt\<close>\<close>

definition shift_int :: "int \<Rightarrow> int \<Rightarrow> int"
  where "shift_int k n = (if k \<ge> 0 then n * 2 ^ nat k else n div 2 ^ (nat (-k)))"

lemma shift_int_code [code]:
  "shift_int k n = (if k \<ge> 0 then push_bit (nat k) n else drop_bit (nat (-k)) n)"
  by (simp add: shift_int_def push_bit_eq_mult drop_bit_eq_div)

definition lb_sqrt :: "nat \<Rightarrow> float \<Rightarrow> float" where
  "lb_sqrt prec x = (let n = mantissa x; e = exponent x; k = nat (2 * int prec - bitlen n);
                       k' = (if even k = even e then k else k + 1) in
     normfloat (Float (sqrt_int_floor (shift_int k' n)) (shift_int (-1) (e - k'))))"

definition ub_sqrt :: "nat \<Rightarrow> float \<Rightarrow> float" where
  "ub_sqrt prec x = (let n = mantissa x; e = exponent x; k = nat (2 * prec - bitlen n);
                       k' = (if even k = even e then k else k + 1) in
     normfloat (Float (sqrt_int_ceiling (shift_int k' n)) (shift_int (-1) (e - k'))))"

lemma lb_sqrt: "lb_sqrt prec x \<le> sqrt x"
proof -
  define n where "n = mantissa x"
  define e where "e = exponent x"
  define k where "k = nat (2 * int  prec - bitlen n)"
  define k' where "k' = (if even k = even e then k else k + 1)"
  have "even (e - k')"
    by (auto simp: k'_def)
  define e'' where "e'' = (e - k') div 2"
  have e'': "k' = e - 2 * e''"
    using \<open>even (e - k')\<close> by (auto simp: e''_def)
  have "real_of_float (lb_sqrt prec x) = of_int \<lfloor>sqrt (n * 2 powi int k')\<rfloor> * 2 powi ((e - k') div 2)"
    by (simp add: lb_sqrt_def n_def e_def k_def k'_def
                  Let_def powr_real_of_int' shift_int_def add_ac nat_add_distrib
                  sqrt_int_floor_def sqrt_int_ceiling_def)
  also have "\<dots> \<le> sqrt (n * 2 powi int k') * 2 powi ((e - k') div 2)"
    by (intro mult_right_mono) auto
  also have "\<dots> = sqrt (of_int n * 2 powi e) * (2 powi e'' / sqrt (2 powi (2 * e'')))"
    unfolding e'' by (simp add: power_int_diff real_sqrt_divide)
  also have "2 powi (2 * e'') = (2 powi e'' :: real) ^ 2"
    by (simp add: mult.commute power_int_mult)
  also have "sqrt \<dots> = 2 powi e''"
    by simp
  also have "real_of_int n * 2 powi e = real_of_float (Float n e)"
    by (simp add: powr_real_of_int')
  also have "Float n e = x"
    by (simp add: n_def e_def Float_mantissa_exponent)
  finally show ?thesis
    by simp
qed

lemma ub_sqrt: "ub_sqrt prec x \<ge> sqrt x"
proof -
  define n where "n = mantissa x"
  define e where "e = exponent x"
  define k where "k = nat (2 * int  prec - bitlen n)"
  define k' where "k' = (if even k = even e then k else k + 1)"
  have "even (e - k')"
    by (auto simp: k'_def)
  define e'' where "e'' = (e - k') div 2"
  have e'': "k' = e - 2 * e''"
    using \<open>even (e - k')\<close> by (auto simp: e''_def)
  have "sqrt x = sqrt (Float n e)"
    by (simp add: n_def e_def Float_mantissa_exponent)
  also have "\<dots> = sqrt (of_int n * 2 powi e) * (2 powi e'' / sqrt (2 powi (2 * e'')))"
    by (simp add: mult.commute power_int_mult powr_real_of_int')
  also have "\<dots> = sqrt (of_int n * 2 powi (e - 2 * e'')) * 2 powi e''"
    by (simp add: real_sqrt_divide power_int_diff)
  also have "\<dots> = sqrt (of_int n * 2 powi int k') * 2 powi ((e - k') div 2)"
    unfolding e'' by simp
  also have "\<dots> \<le> \<lceil>sqrt (of_int n * 2 powi int k')\<rceil> * 2 powi ((e - k') div 2)"
    by (intro mult_right_mono) auto
  also have "\<dots> = real_of_float (ub_sqrt prec x)"
    by (simp add: ub_sqrt_def n_def e_def k_def k'_def
                  Let_def powr_real_of_int' shift_int_def add_ac nat_add_distrib
                  sqrt_int_floor_def sqrt_int_ceiling_def)
  finally show ?thesis .
qed

context
  includes interval.lifting
begin

lift_definition sqrt_float_interval :: "nat \<Rightarrow> float interval \<Rightarrow> float interval" is
  "\<lambda>prec (l, u). (lb_sqrt prec l, ub_sqrt prec u)"
proof goal_cases
  case (1 prec lu)
  obtain l u where [simp]: "lu = (l, u)"
    by (cases lu)
  have "real_of_float (lb_sqrt prec l) \<le> sqrt l"
    by (rule lb_sqrt)
  also have "\<dots> \<le> sqrt u"
    using 1 by auto
  also have "\<dots> \<le> real_of_float (ub_sqrt prec u)"
    by (rule ub_sqrt)
  finally show ?case
    by simp
qed

lemma sqrt_float_intervalI:
  fixes x :: real and X :: "float interval"
  assumes "x \<in> set_of (real_interval X)"
  shows   "sqrt x \<in> set_of (real_interval (sqrt_float_interval prec X))"
  using assms
proof (transfer, goal_cases)
  case (1 x lu prec)
  obtain l u where [simp]: "lu = (l, u)"
    by (cases lu)
  from 1 have x: "real_of_float l \<le> x" "x \<le> real_of_float u"
    by simp_all
  have "real_of_float (lb_sqrt prec l) \<le> sqrt x" 
    using lb_sqrt[of prec l] x(1) by (meson dual_order.trans real_sqrt_le_iff)
  moreover have "real_of_float (ub_sqrt prec u) \<ge> sqrt x" 
    using ub_sqrt[of u prec] x(2) by (meson dual_order.trans real_sqrt_le_iff)
  ultimately show ?case
    by simp
qed

lemma sqrt_float_interval:
  "sqrt ` set_of (real_interval X) \<subseteq> set_of (real_interval (sqrt_float_interval prec X))"
  using sqrt_float_intervalI[of _ X] by blast

end

end