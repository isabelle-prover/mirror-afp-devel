theory Wrap_Speedup_Arithmetic
  imports Wrap_Speedup
begin

section \<open>Absorbing the linear speedup's constants\<close>

text \<open>Form 1 of the linear speedup theorem, run on the raw input
  (@{thm [source] linear_speedup_form_1_raw_nae}), costs
  \<open>n + 3\<lceil>n/m\<rceil> + 8\<lceil>T(n)/m\<rceil> + 9\<close> steps at compression alphabet size \<open>m\<close>.
  Against a bound with \<open>t(n) \<ge> n + n/q\<close>, write \<open>t(n) = n + s\<close>: then
  \<open>8 c s / m\<close>, \<open>20\<close>, \<open>(3 + 8c) n / m\<close> and \<open>8 e / m\<close> each take a fixed
  fraction of \<open>s\<close> once \<open>m\<close> is large relative to \<open>c\<close> and \<open>q\<close> and \<open>n\<close> is
  large relative to \<open>q\<close> and \<open>e\<close>.  The lemma below multiplies through by
  \<open>16 m\<close> so that the argument stays in \<^typ>\<open>nat\<close>.

  Each ceiling is bounded by the floor plus one: the upper half of
  @{thm [source] nat_ceil_div_eq}, the entry's ceiling-division identity.\<close>

lemma speedup_round_up_le:
  fixes x m :: nat
  assumes m: "0 < m"
  shows "(x + m - 1) div m \<le> x div m + 1"
  using nat_ceil_div_eq [OF m, of x, symmetric] by simp

lemma speedup_band_arith:
  fixes c e q m n tn :: nat
  assumes q: "0 < q"
      and m: "16 * (3 + 8 * c) * (q + 1) + 16 * c + 1 \<le> m"
      and n: "q * (81 + 128 * e) \<le> n"
      and tn: "n + n div q \<le> tn"
  shows "n + (n + m - 1) div m + 5 + 2 * ((n + m - 1) div m)
           + 8 * ((c * tn + e + m - 1) div m) + 4 \<le> tn"
proof -
  have m0: "0 < m" using m by simp
  define a where "a = n div m"
  define b where "b = (c * tn + e) div m"
  have ca: "(n + m - 1) div m \<le> a + 1" unfolding a_def by (rule speedup_round_up_le [OF m0])
  have cb: "(c * tn + e + m - 1) div m \<le> b + 1" unfolding b_def by (rule speedup_round_up_le [OF m0])
  have ma: "m * a \<le> n" unfolding a_def by (rule times_div_less_eq_dividend)
  have mb: "m * b \<le> c * tn + e" unfolding b_def by (rule times_div_less_eq_dividend)
  define s where "s = tn - n"
  have t_eq: "tn = n + s" using tn unfolding s_def by simp
  define d where "d = n div q"
  have ds: "d \<le> s" using tn unfolding s_def d_def by simp
  have dbig: "81 + 128 * e \<le> d"
  proof -
    have "(q * (81 + 128 * e)) div q \<le> n div q" by (rule div_le_mono [OF n])
    then show ?thesis unfolding d_def using q by simp
  qed
  have nd: "n \<le> q * (s + 1)"
  proof -
    have "n = q * d + n mod q" unfolding d_def by (rule mult_div_mod_eq [symmetric])
    moreover have "n mod q < q" using q by simp
    moreover have "q * d \<le> q * s" using ds by (rule mult_le_mono2)
    ultimately have "n \<le> q * s + q" by linarith
    then show ?thesis by (simp add: algebra_simps)
  qed
  have s1: "81 + 128 * e \<le> s" using dbig ds by simp
  have h1: "128 * (c * s) \<le> 8 * (m * s)"
  proof -
    have "16 * c \<le> m" using m by simp
    then have "16 * c * s \<le> m * s" by (rule mult_le_mono1)
    then show ?thesis by simp
  qed
  have h2: "320 * m \<le> 4 * (m * s)"
  proof -
    have "m * 80 \<le> m * s" using s1 by simp
    then show ?thesis by simp
  qed
  have h3: "16 * ((3 + 8 * c) * n) \<le> 2 * (m * s)"
  proof -
    have K: "16 * (3 + 8 * c) * q \<le> m"
    proof -
      have "16 * (3 + 8 * c) * q \<le> 16 * (3 + 8 * c) * (q + 1)" by simp
      then show ?thesis using m by linarith
    qed
    have "16 * ((3 + 8 * c) * n) \<le> 16 * ((3 + 8 * c) * (q * (s + 1)))"
      using nd by simp
    also have "\<dots> = 16 * (3 + 8 * c) * q * (s + 1)" by (simp only: mult.assoc)
    also have "\<dots> \<le> m * (s + 1)" using K by (rule mult_le_mono1)
    also have "\<dots> \<le> 2 * (m * s)"
    proof -
      have "m \<le> m * s" using s1 by simp
      then show ?thesis by (simp add: algebra_simps)
    qed
    finally show ?thesis .
  qed
  have h4: "128 * e \<le> m * s"
  proof -
    have "s \<le> m * s" using m0 by simp
    then show ?thesis using s1 by linarith
  qed
  define P where "P = m * n"
  define A where "A = m * a"
  define B where "B = m * b"
  define C where "C = c * tn"
  define W where "W = c * n"
  define X where "X = (3 + 8 * c) * n"
  define Y where "Y = c * s"
  define Z where "Z = m * s"
  have ma': "A \<le> n" using ma unfolding A_def .
  have mb': "B \<le> C + e" using mb unfolding B_def C_def .
  have e2: "C = W + Y" unfolding C_def W_def Y_def t_eq by (simp add: algebra_simps)
  have e3: "X = 3 * n + 8 * W" unfolding X_def W_def by (simp add: algebra_simps)
  have h1': "128 * Y \<le> 8 * Z" using h1 unfolding Y_def Z_def .
  have h2': "320 * m \<le> 4 * Z" using h2 unfolding Z_def .
  have h3': "16 * X \<le> 2 * Z" using h3 unfolding X_def Z_def .
  have h4': "128 * e \<le> Z" using h4 unfolding Z_def .
  have core: "P + 3 * A + 8 * B + 20 * m \<le> P + Z"
    using ma' mb' e2 e3 h1' h2' h3' h4' by linarith
  have e1: "m * (n + 3 * a + 8 * b + 20) = P + 3 * A + 8 * B + 20 * m"
    unfolding P_def A_def B_def by (simp add: algebra_simps)
  have e4: "m * tn = P + Z" unfolding P_def Z_def t_eq by (simp add: algebra_simps)
  have main: "m * (n + 3 * a + 8 * b + 20) \<le> m * tn"
    unfolding e1 e4 by (rule core)
  then have R: "n + 3 * a + 8 * b + 20 \<le> tn" using m0 by simp
  show ?thesis using ca cb R by linarith
qed

end
