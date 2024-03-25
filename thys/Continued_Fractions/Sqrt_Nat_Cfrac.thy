(*
  File:     Continued_Fractions/Sqrt_Nat_Cfrac.thy
  Author:   Manuel Eberl, University of Innsbruck
*)
section \<open>Continued fraction expansions for square roots of naturals\<close>
theory Sqrt_Nat_Cfrac
imports
  Quadratic_Irrationals
  "HOL-Library.While_Combinator"
  "HOL-Library.IArray"
begin

text \<open>
  In this section, we shall explore the continued fraction expansion of $\sqrt{D}$, where $D$
  is a natural number.
\<close>

lemma butlast_nth [simp]: "n < length xs - 1 \<Longrightarrow> butlast xs ! n = xs ! n"
  by (induction xs arbitrary: n) (auto simp: nth_Cons split: nat.splits)

text \<open>
  The following is the length of the period in the continued fraction expansion of
  $\sqrt{D}$ for a natural number $D$.
\<close>
definition sqrt_nat_period_length :: "nat \<Rightarrow> nat" where
  "sqrt_nat_period_length D =
     (if is_square D then 0
      else (LEAST l. l > 0 \<and> (\<forall>n. cfrac_nth (cfrac_of_real (sqrt D)) (Suc n + l) =
                                  cfrac_nth (cfrac_of_real (sqrt D)) (Suc n))))"

text \<open>  
  Next, we define a more workable representation for the continued fraction expansion of
  $\sqrt{D}$ consisting of the period length, the natural number $\lfloor\sqrt{D}\rfloor$, and
  the content of the period.
\<close>
definition sqrt_cfrac_info :: "nat \<Rightarrow> nat \<times> nat \<times> nat list" where
  "sqrt_cfrac_info D =
     (sqrt_nat_period_length D, Discrete.sqrt D, 
      map (\<lambda>n. nat (cfrac_nth (cfrac_of_real (sqrt D)) (Suc n))) [0..<sqrt_nat_period_length D])"

lemma sqrt_nat_period_length_square [simp]: "is_square D \<Longrightarrow> sqrt_nat_period_length D = 0"
  by (auto simp: sqrt_nat_period_length_def)

definition sqrt_cfrac :: "nat \<Rightarrow> cfrac"
  where "sqrt_cfrac D = cfrac_of_real (sqrt (real D))"

context
  fixes D D' :: nat
  defines "D' \<equiv> nat \<lfloor>sqrt D\<rfloor>"
begin

text \<open>
  A number $\alpha = \frac{\sqrt D + p}{q}$ for \<open>p, q \<in> \<nat>\<close> is called a \<^emph>\<open>reduced quadratic surd\<close>
  if $\alpha > 1$ and $bar\alpha \in (-1;0)$, where $\bar\alpha$ denotes the conjugate
  $\frac{-\sqrt D + p}{q}$.

  It is furthermore called \<^emph>\<open>associated\<close> to $D$ if \<open>q\<close> divides \<open>D - p\<^sup>2\<close>.
\<close>
definition red_assoc :: "nat \<times> nat \<Rightarrow> bool" where
  "red_assoc = (\<lambda>(p, q).
     q > 0 \<and> q dvd (D - p\<^sup>2) \<and> (sqrt D + p) / q > 1 \<and> (-sqrt D + p) / q \<in> {-1<..<0})"

text \<open>
  The following two functions convert between a surd represented as a pair of natural numbers
  and the actual real number and its conjugate:
\<close>
definition surd_to_real :: "nat \<times> nat \<Rightarrow> real"
  where "surd_to_real = (\<lambda>(p, q). (sqrt D + p) / q)"

definition surd_to_real_cnj :: "nat \<times> nat \<Rightarrow> real"
  where "surd_to_real_cnj = (\<lambda>(p, q). (-sqrt D + p) / q)"

text \<open>
  The next function performs a single step in the continued fraction expansion of $\sqrt{D}$.
\<close>
definition sqrt_remainder_step :: "nat \<times> nat \<Rightarrow> nat \<times> nat" where
  "sqrt_remainder_step = (\<lambda>(p, q). let X = (p + D') div q; p' = X * q - p in (p', (D - p'\<^sup>2) div q))"

text \<open>
  If we iterate this step function starting from the surd
   $\frac{1}{\sqrt{D} - \lfloor\sqrt{D}\rfloor}$, we get the entire expansion.
\<close>
definition sqrt_remainder_surd :: "nat \<Rightarrow> nat \<times> nat"
  where "sqrt_remainder_surd = (\<lambda>n. (sqrt_remainder_step ^^ n) (D', D - D'\<^sup>2))"

context
  fixes sqrt_cfrac_nth :: "nat \<Rightarrow> nat" and l
  assumes nonsquare: "\<not>is_square D"
  defines "sqrt_cfrac_nth \<equiv> (\<lambda>n. case sqrt_remainder_surd n of (p, q) \<Rightarrow> (D' + p) div q)"
  defines "l \<equiv> sqrt_nat_period_length D"
begin

lemma D'_pos: "D' > 0"
  using nonsquare by (auto simp: D'_def of_nat_ge_1_iff intro: Nat.gr0I)

lemma D'_sqr_less_D: "D'\<^sup>2 < D"
proof -
  have "D' \<le> sqrt D" by (auto simp: D'_def)
  hence "real D' ^ 2 \<le> sqrt D ^ 2" by (intro power_mono) auto
  also have "\<dots> = D" by simp
  finally have "D'\<^sup>2 \<le> D" by simp
  moreover from nonsquare have "D \<noteq> D'\<^sup>2" by auto
  ultimately show ?thesis by simp
qed

lemma red_assoc_imp_irrat:
  assumes "red_assoc pq"
  shows   "surd_to_real pq \<notin> \<rat>"
proof 
  assume rat: "surd_to_real pq \<in> \<rat>"
  with assms rat show False using irrat_sqrt_nonsquare[OF nonsquare]
    by (auto simp: field_simps red_assoc_def surd_to_real_def divide_in_Rats_iff2 add_in_Rats_iff1)
qed

lemma surd_to_real_cnj_irrat:
  assumes "red_assoc pq"
  shows   "surd_to_real_cnj pq \<notin> \<rat>"
proof 
  assume rat: "surd_to_real_cnj pq \<in> \<rat>"
  with assms rat show False using irrat_sqrt_nonsquare[OF nonsquare]
    by (auto simp: field_simps red_assoc_def surd_to_real_cnj_def divide_in_Rats_iff2 diff_in_Rats_iff1)
qed

lemma surd_to_real_nonneg [intro]: "surd_to_real pq \<ge> 0"
  by (auto simp: surd_to_real_def case_prod_unfold divide_simps intro!: divide_nonneg_nonneg)

lemma surd_to_real_pos [intro]: "red_assoc pq \<Longrightarrow> surd_to_real pq > 0"
  by (auto simp: surd_to_real_def case_prod_unfold divide_simps red_assoc_def
           intro!: divide_nonneg_nonneg)

lemma surd_to_real_nz [simp]: "red_assoc pq \<Longrightarrow> surd_to_real pq \<noteq> 0"
  by (auto simp: surd_to_real_def case_prod_unfold divide_simps red_assoc_def
           intro!: divide_nonneg_nonneg)

lemma surd_to_real_cnj_nz [simp]: "red_assoc pq \<Longrightarrow> surd_to_real_cnj pq \<noteq> 0"
  using surd_to_real_cnj_irrat[of pq] by auto

lemma red_assoc_step:
  assumes "red_assoc pq"
  defines "X \<equiv> (D' + fst pq) div snd pq"
  defines "pq' \<equiv> sqrt_remainder_step pq"
  shows   "red_assoc pq'"
          "surd_to_real pq' = 1 / frac (surd_to_real pq)"
          "surd_to_real_cnj pq' = 1 / (surd_to_real_cnj pq - X)"
          "X > 0" "X * snd pq \<le> 2 * D'" "X = nat \<lfloor>surd_to_real pq\<rfloor>"
          "X = nat \<lfloor>-1 / surd_to_real_cnj pq'\<rfloor>"
proof -
  obtain p q where [simp]: "pq = (p, q)" by (cases pq)
  obtain p' q' where [simp]: "pq' = (p', q')" by (cases pq')
  define \<alpha> where "\<alpha> = (sqrt D + p) / q"
  define \<alpha>' where "\<alpha>' = 1 / frac \<alpha>"
  define cnj_\<alpha>' where "cnj_\<alpha>' = (-sqrt D + (X * q - int p)) / ((D - (X * q - int p)\<^sup>2) div q)"
  from assms(1) have "\<alpha> > 0" "q > 0"
    by (auto simp: \<alpha>_def red_assoc_def)
  from assms(1) nonsquare have "\<alpha> \<notin> \<rat>"
    by (auto simp: \<alpha>_def red_assoc_def divide_in_Rats_iff2 add_in_Rats_iff2 irrat_sqrt_nonsquare)
  hence \<alpha>'_pos: "frac \<alpha> > 0" using Ints_subset_Rats by auto
  from \<open>pq' = (p', q')\<close> have p'_def: "p' = X * q - p" and q'_def: "q' = (D - p'\<^sup>2) div q"
    unfolding pq'_def sqrt_remainder_step_def X_def by (auto simp: Let_def add_ac)

  have "D' + p = \<lfloor>sqrt D + p\<rfloor>"
    by (auto simp: D'_def)
  also have "\<dots> div int q = \<lfloor>(sqrt D + p) / q\<rfloor>"
    by (subst floor_divide_real_eq_div [symmetric]) auto
  finally have X_altdef: "X = nat \<lfloor>(sqrt D + p) / q\<rfloor>"
    unfolding X_def zdiv_int [symmetric] by auto

  have nz: "sqrt (real D) + (X * q - real p) \<noteq> 0"
  proof
    assume "sqrt (real D) + (X * q - real p) = 0"
    hence "sqrt (real D) = real p - X * q" by (simp add: algebra_simps)
    also have "\<dots> \<in> \<rat>" by auto
    finally show False using irrat_sqrt_nonsquare nonsquare by blast
  qed

  from assms(1) have "real (p ^ 2) \<le> sqrt D ^ 2"
    unfolding of_nat_power by (intro power_mono) (auto simp: red_assoc_def field_simps)
  also have "sqrt D ^ 2 = D" by simp
  finally have "p\<^sup>2 \<le> D" by (subst (asm) of_nat_le_iff)

  have "frac \<alpha> = \<alpha> - X"
    by (simp add: X_altdef frac_def \<alpha>_def)
  also have "\<dots> = (sqrt D - (X * q - int p)) / q"
    using \<open>q > 0\<close> by (simp add: field_simps \<alpha>_def)
  finally have "1 / frac \<alpha> = q / (sqrt D - (X * q - int p))"
    by simp
  also have "\<dots> = q * (sqrt D + (X * q - int p)) /
                    ((sqrt D - (X * q - int p)) * (sqrt D + (X * q - int p)))" (is "_ = ?A / ?B")
    using nz by (subst mult_divide_mult_cancel_right) auto
  also have "?B = real_of_int (D - int p ^ 2 + 2 * X * p * q - int X ^ 2 * q ^ 2)"
    by (auto simp: algebra_simps power2_eq_square)
  also have "q dvd (D - p ^ 2)" using assms(1) by (auto simp: red_assoc_def)
  with \<open>p\<^sup>2 \<le> D\<close> have "int q dvd (int D - int p ^ 2)" 
    unfolding of_nat_power [symmetric] by (subst of_nat_diff [symmetric]) auto
  hence "D - int p ^ 2 + 2 * X * p * q - int X ^ 2 * q ^ 2 = q * ((D - (X * q - int p)\<^sup>2) div q)"
    by (auto simp: power2_eq_square algebra_simps)
  also have "?A / \<dots> = (sqrt D + (X * q - int p)) / ((D - (X * q - int p)\<^sup>2) div q)"
    unfolding of_int_mult of_int_of_nat_eq
    by (rule mult_divide_mult_cancel_left) (insert \<open>q > 0\<close>, auto)
  finally have \<alpha>': "\<alpha>' = \<dots>" by (simp add: \<alpha>'_def)

  have dvd: "q dvd (D - (X * q - int p)\<^sup>2)"
    using assms(1) \<open>int q dvd (int D - int p ^ 2)\<close>
    by (auto simp: power2_eq_square algebra_simps)

  have "X \<le> (sqrt D + p) / q" unfolding X_altdef by simp
  moreover have "X \<noteq> (sqrt D + p) / q"
  proof
    assume "X = (sqrt D + p) / q"
    hence "sqrt D = q * X - real p" using \<open>q > 0\<close> by (auto simp: field_simps)
    also have "\<dots> \<in> \<rat>" by auto
    finally show False using irrat_sqrt_nonsquare[OF nonsquare] by simp
  qed
  ultimately have "X < (sqrt D + p) / q" by simp
  hence *: "(X * q - int p) < sqrt D"
    using \<open>q > 0\<close> by (simp add: field_simps)
  moreover
  have pos: "real_of_int (int D - (int X * int q - int p)\<^sup>2) > 0"
  proof (cases "X * q \<ge> p")
    case True
    hence "real p \<le> real X * real q" unfolding of_nat_mult [symmetric] of_nat_le_iff .
    hence "real_of_int ((X * q - int p) ^ 2) < sqrt D ^ 2" using *
      unfolding of_int_power by (intro power_strict_mono) auto
    also have "\<dots> = D" by simp
    finally show ?thesis by simp
  next
    case False
    hence less: "real X * real q < real p"
      unfolding of_nat_mult [symmetric] of_nat_less_iff by auto
    have "(real X * real q - real p)\<^sup>2 = (real p - real X * real q)\<^sup>2"
      by (simp add: power2_eq_square algebra_simps)
    also have "\<dots> \<le> real p ^ 2" using less by (intro power_mono) auto
    also have "\<dots> < sqrt D ^ 2" 
      using \<open>q > 0\<close> assms(1) unfolding of_int_power
      by (intro power_strict_mono) (auto simp: red_assoc_def field_simps)
    also have "\<dots> = D" by simp
    finally show ?thesis by simp
  qed
  hence pos': "int D - (int X * int q - int p)\<^sup>2 > 0"
    by (subst (asm) of_int_0_less_iff)
  from pos have "real_of_int ((int D - (int X * int q - int p)\<^sup>2) div q) > 0"
    using \<open>q > 0\<close> dvd by (subst real_of_int_div) (auto intro!: divide_pos_pos)
  ultimately have cnj_neg: "cnj_\<alpha>' < 0" unfolding cnj_\<alpha>'_def using dvd
    unfolding of_int_0_less_iff by (intro divide_neg_pos) auto

  have "(p - sqrt D) / q < 0"
    using assms(1) by (auto simp: red_assoc_def X_altdef le_nat_iff)
  also have "X \<ge> 1"
    using assms(1) by (auto simp: red_assoc_def X_altdef le_nat_iff)
  hence "0 \<le> real X - 1" by simp
  finally have "q < sqrt D + int q * X - p"
    using \<open>q > 0\<close> by (simp add: field_simps)
  hence "q * (sqrt D - (int q * X - p)) < (sqrt D + (int q * X - p)) * (sqrt D - (int q * X - p))"
    using * by (intro mult_strict_right_mono) (auto simp: red_assoc_def X_altdef field_simps)
  also have "\<dots> = D - (int q * X - p) ^ 2"
    by (simp add: power2_eq_square algebra_simps)
  finally have "cnj_\<alpha>' > -1"
    using dvd pos \<open>q > 0\<close> by (simp add: real_of_int_div field_simps cnj_\<alpha>'_def)

  from cnj_neg and this have "cnj_\<alpha>' \<in> {-1<..<0}" by auto
  have "\<alpha>' > 1" using \<open>frac \<alpha> > 0\<close>
    by (auto simp: \<alpha>'_def field_simps frac_lt_1)

  have "0 = 1 + (-1 :: real)"
    by simp
  also have "1 + -1 < \<alpha>' + cnj_\<alpha>'"
    using \<open>cnj_\<alpha>' > -1\<close> and \<open>\<alpha>' > 1\<close> by (intro add_strict_mono)
  also have "\<alpha>' + cnj_\<alpha>' = 2 * (real X * q - real p) / ((int D - (int X * q - int p)\<^sup>2) div int q)"
    by (simp add: \<alpha>' cnj_\<alpha>'_def add_divide_distrib [symmetric])
  finally have "real X * q - real p > 0" using pos dvd \<open>q > 0\<close>
    by (subst (asm) zero_less_divide_iff, subst (asm) (1 2 3) real_of_int_div)
       (auto simp: field_simps)
  hence "real (X * q) > real p" unfolding of_nat_mult by simp
  hence p_less_Xq: "p < X * q" by (simp only: of_nat_less_iff)

  from pos' and p_less_Xq have "int D > int ((X * q - p)\<^sup>2)"
    by (subst of_nat_power) (auto simp: of_nat_diff)
  hence pos'': "D > (X * q - p)\<^sup>2" unfolding of_nat_less_iff .

  from dvd have "int q dvd int (D - (X * q - p)\<^sup>2)"
    using p_less_Xq pos'' by (subst of_nat_diff) (auto simp: of_nat_diff)
  with dvd have dvd': "q dvd (D - (X * q - p)\<^sup>2)"
    by simp

  have \<alpha>'_altdef: "\<alpha>' = (sqrt D + p') / q'"
    using dvd dvd' pos'' p_less_Xq \<alpha>'
    by (simp add: real_of_int_div p'_def q'_def real_of_nat_div mult_ac of_nat_diff)
  have cnj_\<alpha>'_altdef: "cnj_\<alpha>' = (-sqrt D + p') / q'"
    using dvd dvd' pos'' p_less_Xq unfolding cnj_\<alpha>'_def
    by (simp add: real_of_int_div p'_def q'_def real_of_nat_div mult_ac of_nat_diff)
  from dvd' have dvd'': "q' dvd (D - p'\<^sup>2)"
    by (auto simp: mult_ac p'_def q'_def)
  have "real ((D - p'\<^sup>2) div q) > 0" unfolding p'_def
    by (subst real_of_nat_div[OF dvd'], rule divide_pos_pos) (insert \<open>q > 0\<close> pos'', auto)
  hence "q' > 0" unfolding q'_def of_nat_0_less_iff .

  show "red_assoc pq'" using \<open>\<alpha>' > 1\<close> and \<open>cnj_\<alpha>' \<in> _\<close> and dvd'' and \<open>q' > 0\<close>
    by (auto simp: red_assoc_def \<alpha>'_altdef cnj_\<alpha>'_altdef)

  from assms(1) have "real p < sqrt D"
    by (auto simp add: field_simps red_assoc_def)
  hence "p \<le> D'" unfolding D'_def by linarith
  with * have "real (X * q) < sqrt (real D) + D'"
    by simp
  thus "X * snd pq \<le> 2 * D'" unfolding D'_def \<open>pq = (p, q)\<close> snd_conv by linarith

  have "(sqrt D + p') / q' = \<alpha>'"
    by (rule \<alpha>'_altdef [symmetric])
  also have "\<alpha>' = 1 / frac ((sqrt D + p) / q)"
    by (simp add: \<alpha>'_def \<alpha>_def)
  finally show "surd_to_real pq' = 1 / frac (surd_to_real pq)" by (simp add: surd_to_real_def)
  from \<open>X \<ge> 1\<close> show "X > 0" by simp
  from X_altdef show "X = nat \<lfloor>surd_to_real pq\<rfloor>" by (simp add: surd_to_real_def)

  have "sqrt (real D) < real p + 1 * real q"
    using assms(1) by (auto simp: red_assoc_def field_simps)
  also have "\<dots> \<le> real p + real X * real q"
    using \<open>X > 0\<close> by (intro add_left_mono mult_right_mono) (auto simp: of_nat_ge_1_iff)
  finally have "sqrt (real D) < \<dots>" .

  have "real p < sqrt D"
    using assms(1) by (auto simp add: field_simps red_assoc_def)
  also have "\<dots> \<le> sqrt D + q * X"
    by linarith
  finally have less: "real p < sqrt D + X * q" by (simp add: algebra_simps)
  moreover have "D + p * p' + X * q * sqrt D = q * q' + p * sqrt D + p' * sqrt D + X * p' * q"
    using dvd' pos'' p_less_Xq \<open>q > 0\<close> unfolding p'_def q'_def of_nat_mult of_nat_add
    by (simp add:  power2_eq_square field_simps of_nat_diff real_of_nat_div)
  ultimately show *: "surd_to_real_cnj pq' = 1 / (surd_to_real_cnj pq - X)"
    using \<open>q > 0\<close> \<open>q' > 0\<close> by (auto simp: surd_to_real_cnj_def field_simps)

  have **: "a = nat \<lfloor>y\<rfloor>" if "x \<ge> 0" "x < 1" "real a + x = y" for a :: nat and x y :: real
    using that by linarith
  from assms(1) have surd_to_real_cnj: "surd_to_real_cnj (p, q) \<in> {-1<..<0}"
    by (auto simp: surd_to_real_cnj_def red_assoc_def)
  have "surd_to_real_cnj (p, q) < X"
    using assms(1) less by (auto simp: surd_to_real_cnj_def field_simps red_assoc_def)
  hence "real X = surd_to_real_cnj (p, q) - 1 / surd_to_real_cnj (p', q')" using *
    using surd_to_real_cnj_irrat assms(1) \<open>red_assoc pq'\<close> by (auto simp: field_simps)
  thus "X = nat \<lfloor>-1 / surd_to_real_cnj pq'\<rfloor>" using surd_to_real_cnj
    by (intro **[of "-surd_to_real_cnj (p, q)"]) auto
qed

lemma red_assoc_denom_2D:
  assumes "red_assoc (p, q)"
  defines "X \<equiv> (D' + p) div q"
  assumes "X > D'"
  shows  "q = 1"
proof -
  have "X * q \<le> 2 * D'" "X > 0"
    using red_assoc_step(4,5)[OF assms(1)] by (simp_all add: X_def)
  note this(1)
  also have "2 * D' < 2 * X"
    by (intro mult_strict_left_mono assms) auto
  finally have "q < 2" using \<open>X > 0\<close> by simp
  moreover from assms(1) have "q > 0" by (auto simp: red_assoc_def)
  ultimately show ?thesis by simp
qed

lemma red_assoc_denom_1:
  assumes "red_assoc (p, 1)"
  shows   "p = D'" 
proof -
  from assms have "sqrt D > p" "sqrt D < real p + 1"
    by (auto simp: red_assoc_def)
  thus "p = D'" unfolding D'_def
    by linarith
qed

lemma red_assoc_begin:
  "red_assoc (D', D - D'\<^sup>2)"
  "surd_to_real (D', D - D'\<^sup>2) = 1 / frac (sqrt D)"
  "surd_to_real_cnj (D', D - D'\<^sup>2) = -1 / (sqrt D + D')"
proof -
  have pos: "D > 0" "D' > 0"
    using nonsquare by (auto simp: D'_def of_nat_ge_1_iff intro!: Nat.gr0I)

  have "sqrt D \<noteq> D'"
    using irrat_sqrt_nonsquare[OF nonsquare] by auto
  moreover have "sqrt D \<ge> 0" by simp
  hence "D' \<le> sqrt D" unfolding D'_def by linarith
  ultimately have less: "D' < sqrt D" by simp

  have "sqrt D \<noteq> D' + 1"
    using irrat_sqrt_nonsquare[OF nonsquare] by auto
  moreover have "sqrt D \<ge> 0" by simp
  hence "D' \<ge> sqrt D - 1" unfolding D'_def by linarith
  ultimately have gt: "D' > sqrt D - 1" by simp

  from less have "real D' ^ 2 < sqrt D ^ 2" by (intro power_strict_mono) auto
  also have "\<dots> = D" by simp
  finally have less': "D'\<^sup>2 < D" unfolding of_nat_power [symmetric] of_nat_less_iff .

  moreover have "real D' * (real D' - 1) < sqrt D * (sqrt D - 1)"
    using less pos
    by (intro mult_strict_mono diff_strict_right_mono) (auto simp: of_nat_ge_1_iff)
  hence "D'\<^sup>2 + sqrt D < D' + D"
    by (simp add: field_simps power2_eq_square)
  moreover have "(sqrt D - 1) * sqrt D < real D' * (real D' + 1)"
    using pos gt by (intro mult_strict_mono) auto
  hence "D < sqrt D + D'\<^sup>2 + D'" by (simp add: power2_eq_square field_simps)
  ultimately show "red_assoc (D', D - D'\<^sup>2)"
    by (auto simp: red_assoc_def field_simps of_nat_diff less)

  have frac: "frac (sqrt D) = sqrt D - D'" unfolding frac_def D'_def
    by auto
  show "surd_to_real (D', D - D'\<^sup>2) = 1 / frac (sqrt D)" unfolding surd_to_real_def
    using less less' pos by (subst frac) (auto simp: of_nat_diff power2_eq_square field_simps)

  have "surd_to_real_cnj (D', D - D'\<^sup>2) = -((sqrt D - D') / (D - D'\<^sup>2))"
    using less less' pos by (auto simp: surd_to_real_cnj_def field_simps)
  also have "real (D - D'\<^sup>2) = (sqrt D - D') * (sqrt D + D')"
    using less' by (simp add: power2_eq_square algebra_simps of_nat_diff)
  also have "(sqrt D - D') / \<dots> = 1 / (sqrt D + D')"
    using less by (subst nonzero_divide_mult_cancel_left) auto
  finally show "surd_to_real_cnj (D', D - D'\<^sup>2) = -1 / (sqrt D + D')" by simp
qed

lemma cfrac_remainder_surd_to_real:
  assumes "red_assoc pq"
  shows   "cfrac_remainder (cfrac_of_real (surd_to_real pq)) n =
             surd_to_real ((sqrt_remainder_step ^^ n) pq)"
  using assms(1)
proof (induction n arbitrary: pq)
  case 0
  hence "cfrac_lim (cfrac_of_real (surd_to_real pq)) = surd_to_real pq"
    by (intro cfrac_lim_of_real red_assoc_imp_irrat 0)
  thus ?case using 0
    by auto
next
  case (Suc n)
  obtain p q where [simp]: "pq = (p, q)" by (cases pq)
  have "surd_to_real ((sqrt_remainder_step ^^ Suc n) pq) = 
          surd_to_real ((sqrt_remainder_step ^^ n) (sqrt_remainder_step (p, q)))"
    by (subst funpow_Suc_right) auto
  also have "\<dots> = cfrac_remainder (cfrac_of_real (surd_to_real (sqrt_remainder_step (p, q)))) n"
    using red_assoc_step(1)[of "(p, q)"] Suc.prems
    by (intro Suc.IH [symmetric]) (auto simp: sqrt_remainder_step_def Let_def add_ac)
  also have "surd_to_real (sqrt_remainder_step (p, q)) = 1 / frac (surd_to_real (p, q))"
    using red_assoc_step(2)[of "(p, q)"] Suc.prems
    by (auto simp: sqrt_remainder_step_def Let_def add_ac surd_to_real_def)
  also have "cfrac_of_real \<dots> = cfrac_tl (cfrac_of_real (surd_to_real (p, q)))"
    using Suc.prems Ints_subset_Rats red_assoc_imp_irrat by (subst cfrac_tl_of_real) auto
  also have "cfrac_remainder \<dots> n = cfrac_remainder (cfrac_of_real (surd_to_real (p, q))) (Suc n)"
    by (simp add: cfrac_drop_Suc_right cfrac_remainder_def)
  finally show ?case by simp
qed

lemma red_assoc_step' [intro]: "red_assoc pq \<Longrightarrow> red_assoc (sqrt_remainder_step pq)"
  using red_assoc_step(1)[of pq]
  by (simp add: sqrt_remainder_step_def case_prod_unfold add_ac Let_def)

lemma red_assoc_steps [intro]: "red_assoc pq \<Longrightarrow> red_assoc ((sqrt_remainder_step ^^ n) pq)"
  by (induction n) auto

lemma floor_sqrt_less_sqrt: "D' < sqrt D"
proof -
  have "D' \<le> sqrt D" unfolding D'_def by auto
  moreover have "sqrt D \<noteq> D'"
    using irrat_sqrt_nonsquare[OF nonsquare] by auto
  ultimately show ?thesis by auto
qed

lemma red_assoc_bounds: 
  assumes "red_assoc pq"
  shows   "pq \<in> (SIGMA p:{0<..D'}. {Suc D' - p..D' + p})"
proof -
  obtain p q where [simp]: "pq = (p, q)" by (cases pq)
  from assms have *: "p < sqrt D"
    by (auto simp: red_assoc_def field_simps)
  hence p: "p \<le> D'" unfolding D'_def by linarith
  from assms have "p > 0" by (auto intro!: Nat.gr0I simp: red_assoc_def)

  have "q > sqrt D - p" "q < sqrt D + p" 
    using assms by (auto simp: red_assoc_def field_simps)
  hence "q \<ge> D' + 1 - p" "q \<le> D' + p"
    unfolding D'_def by linarith+
  with p \<open>p > 0\<close> show ?thesis by simp
qed

lemma surd_to_real_cnj_eq_iff: 
  assumes "red_assoc pq" "red_assoc pq'"
  shows   "surd_to_real_cnj pq = surd_to_real_cnj pq' \<longleftrightarrow> pq = pq'"
proof
  assume eq: "surd_to_real_cnj pq = surd_to_real_cnj pq'"
  from assms have pos: "snd pq > 0" "snd pq' > 0" by (auto simp: red_assoc_def)
  have "snd pq = snd pq'"
  proof (rule ccontr)
    assume "snd pq \<noteq> snd pq'"
    with eq have "sqrt D = (real (fst pq' * snd pq) - fst pq * snd pq') / (real (snd pq) - snd pq')"
      using pos by (auto simp: field_simps surd_to_real_cnj_def case_prod_unfold)
    also have "\<dots> \<in> \<rat>" by auto
    finally show False using irrat_sqrt_nonsquare[OF nonsquare] by auto
  qed
  moreover from this eq pos have "fst pq = fst pq'"
    by (auto simp: surd_to_real_cnj_def case_prod_unfold)
  ultimately show "pq = pq'" by (simp add: prod_eq_iff)
qed auto

lemma red_assoc_sqrt_remainder_surd [intro]: "red_assoc (sqrt_remainder_surd n)"
  by (auto simp: sqrt_remainder_surd_def intro!: red_assoc_begin)

lemma surd_to_real_sqrt_remainder_surd:
  "surd_to_real (sqrt_remainder_surd n) = cfrac_remainder (cfrac_of_real (sqrt D)) (Suc n)"
proof (induction n)
  case 0
  from nonsquare have "D > 0" by (auto intro!: Nat.gr0I)
  with red_assoc_begin show ?case using nonsquare irrat_sqrt_nonsquare[OF nonsquare]
    using Ints_subset_Rats cfrac_drop_Suc_right cfrac_remainder_def cfrac_tl_of_real
          sqrt_remainder_surd_def by fastforce
next
  case (Suc n)
  have "surd_to_real (sqrt_remainder_surd (Suc n)) =
          surd_to_real (sqrt_remainder_step (sqrt_remainder_surd n))"
    by (simp add: sqrt_remainder_surd_def)
  also have "\<dots> = 1 / frac (surd_to_real (sqrt_remainder_surd n))"
    using red_assoc_step[OF red_assoc_sqrt_remainder_surd[of n]] by simp
  also have "surd_to_real (sqrt_remainder_surd n) =
               cfrac_remainder (cfrac_of_real (sqrt D)) (Suc n)" (is "_ = ?X")
    by (rule Suc.IH)
  also have "\<lfloor>cfrac_remainder (cfrac_of_real (sqrt (real D))) (Suc n)\<rfloor> =
               cfrac_nth (cfrac_of_real (sqrt (real D))) (Suc n)"
    using irrat_sqrt_nonsquare[OF nonsquare] by (intro floor_cfrac_remainder) auto
  hence "1 / frac ?X = cfrac_remainder (cfrac_of_real (sqrt D)) (Suc (Suc n))"
    using irrat_sqrt_nonsquare[OF nonsquare]
    by (subst cfrac_remainder_Suc[of "Suc n"])
       (simp_all add: frac_def cfrac_length_of_real_irrational)
  finally show ?case .
qed

lemma sqrt_cfrac: "sqrt_cfrac_nth n = cfrac_nth (cfrac_of_real (sqrt D)) (Suc n)"
proof -
  have "cfrac_nth (cfrac_of_real (sqrt D)) (Suc n) =
          \<lfloor>cfrac_remainder (cfrac_of_real (sqrt D)) (Suc n)\<rfloor>"
    using irrat_sqrt_nonsquare[OF nonsquare] by (subst floor_cfrac_remainder) auto
  also have "cfrac_remainder (cfrac_of_real (sqrt D)) (Suc n) = surd_to_real (sqrt_remainder_surd n)"
    by (rule surd_to_real_sqrt_remainder_surd [symmetric])
  also have "nat \<lfloor>surd_to_real (sqrt_remainder_surd n)\<rfloor> = sqrt_cfrac_nth n"
    unfolding sqrt_cfrac_nth_def using red_assoc_step(6)[OF red_assoc_sqrt_remainder_surd[of n]]
    by (simp add: case_prod_unfold)
  finally show ?thesis
    by (simp add: nat_eq_iff)
qed

lemma sqrt_cfrac_pos: "sqrt_cfrac_nth k > 0"
  using red_assoc_step(4)[OF red_assoc_sqrt_remainder_surd[of k]]
  by (simp add: sqrt_cfrac_nth_def case_prod_unfold)

lemma snd_sqrt_remainder_surd_pos: "snd (sqrt_remainder_surd n) > 0"
  using red_assoc_sqrt_remainder_surd[of n] by (auto simp: red_assoc_def)


lemma
  shows period_nonempty:      "l > 0"
    and period_length_le_aux: "l \<le> D' * (D' + 1)"
    and sqrt_remainder_surd_periodic:   "\<And>n. sqrt_remainder_surd n = sqrt_remainder_surd (n mod l)"
    and sqrt_cfrac_periodic: "\<And>n. sqrt_cfrac_nth n = sqrt_cfrac_nth (n mod l)"
    and sqrt_remainder_surd_smallest_period:
          "\<And>n. n \<in> {0<..<l} \<Longrightarrow> sqrt_remainder_surd n \<noteq> sqrt_remainder_surd 0"
    and snd_sqrt_remainder_surd_gt_1:   "\<And>n. n < l - 1 \<Longrightarrow> snd (sqrt_remainder_surd n) > 1"
    and sqrt_cfrac_le:       "\<And>n. n < l - 1 \<Longrightarrow> sqrt_cfrac_nth n \<le> D'"
    and sqrt_remainder_surd_last:       "sqrt_remainder_surd (l - 1) = (D', 1)"
    and sqrt_cfrac_last:     "sqrt_cfrac_nth (l - 1) = 2 * D'"
    and sqrt_cfrac_palindrome: "\<And>n. n < l - 1 \<Longrightarrow> sqrt_cfrac_nth (l - n - 2) = sqrt_cfrac_nth n"
    and sqrt_cfrac_smallest_period:
          "\<And>l'. l' > 0 \<Longrightarrow> (\<And>k. sqrt_cfrac_nth (k + l') = sqrt_cfrac_nth k) \<Longrightarrow> l' \<ge> l"
proof -
  note [simp] = sqrt_remainder_surd_def
  define f where "f = sqrt_remainder_surd"
  have *[intro]: "red_assoc (f n)" for n
    unfolding f_def by (rule red_assoc_sqrt_remainder_surd)

  define S where "S = (SIGMA p:{0<..D'}. {Suc D' - p..D' + p})"
  have [intro]: "finite S" by (simp add: S_def)
  have "card S = (\<Sum>p=1..D'. 2 * p)" unfolding S_def
    by (subst card_SigmaI) (auto intro!: sum.cong)
  also have "\<dots> = D' * (D' + 1)"
    by (induction D') (auto simp: power2_eq_square)
  finally have [simp]: "card S = D' * (D' + 1)" .
  
  have "D' * (D' + 1) + 1 = card {..D' * (D' + 1)}" by simp
  define k1 where
    "k1 = (LEAST k1. k1 \<le> D' * (D' + 1) \<and> (\<exists>k2. k2 \<le> D' * (D' + 1) \<and> k1 \<noteq> k2 \<and> f k1 = f k2))"
  define k2 where
    "k2 = (LEAST k2. k2 \<le> D' * (D' + 1) \<and> k1 \<noteq> k2 \<and> f k1 = f k2)"
  
  have "f ` {..D' * (D' + 1)} \<subseteq> S" unfolding S_def
    using red_assoc_bounds[OF *] by blast
  hence "card (f ` {..D' * (D' + 1)}) \<le> card S"
    by (intro card_mono) auto
  also have "card S = D' * (D' + 1)" by simp
  also have "\<dots> < card {..D' * (D' + 1)}" by simp
  finally have "\<not>inj_on f {..D' * (D' + 1)}"
    by (rule pigeonhole)
  hence "\<exists>k1. k1 \<le> D' * (D' + 1) \<and> (\<exists>k2. k2 \<le> D' * (D' + 1) \<and> k1 \<noteq> k2 \<and> f k1 = f k2)"
    by (auto simp: inj_on_def)
  from LeastI_ex[OF this, folded k1_def]
    have "k1 \<le> D' * (D' + 1)" "\<exists>k2\<le>D' * (D' + 1). k1 \<noteq> k2 \<and> f k1 = f k2" by auto
  moreover from LeastI_ex[OF this(2), folded k2_def]
    have "k2 \<le> D' * (D' + 1)" "k1 \<noteq> k2" "f k1 = f k2" by auto
  moreover have "k1 \<le> k2"
  proof (rule ccontr)
    assume "\<not>(k1 \<le> k2)"
    hence "k2 \<le> D' * (D' + 1) \<and> (\<exists>k2'. k2' \<le> D' * (D' + 1) \<and> k2 \<noteq> k2' \<and> f k2 = f k2')"
      using \<open>k1 \<le> D' * (D' + 1)\<close> and \<open>k1 \<noteq> k2\<close> and \<open>f k1 = f k2\<close> by auto
    hence "k1 \<le> k2" unfolding k1_def by (rule Least_le)
    with \<open>\<not>(k1 \<le> k2)\<close> show False by simp
  qed
  ultimately have k12: "k1 < k2" "k2 \<le> D' * (D' + 1)" "f k1 = f k2" by auto

  have [simp]: "k1 = 0"
  proof (cases k1)
    case (Suc k1')
    define k2' where "k2' = k2 - 1"
    have Suc': "k2 = Suc k2'" using k12 by (simp add: k2'_def)
    have nz: "surd_to_real_cnj (sqrt_remainder_step (f k1')) \<noteq> 0"
             "surd_to_real_cnj (sqrt_remainder_step (f k2')) \<noteq> 0"
      using surd_to_real_cnj_nz[OF *[of k2]] surd_to_real_cnj_nz[OF *[of k1]] 
      by (simp_all add: f_def Suc Suc')

    define a where "a = (D' + fst (f k1)) div snd (f k1)"
    define a' where "a' = (D' + fst (f k1')) div snd (f k1')"
    define a'' where "a'' = (D' + fst (f k2')) div snd (f k2')"
    have "a' = nat \<lfloor>- 1 / surd_to_real_cnj (sqrt_remainder_step (f k1'))\<rfloor>"
      using red_assoc_step[OF *[of k1']] by (simp add: a'_def)
    also have "sqrt_remainder_step (f k1') = f k1"
      by (simp add: Suc f_def)
    also have "f k1 = f k2" by fact
    also have "f k2 = sqrt_remainder_step (f k2')" by (simp add: Suc' f_def)
    also have "nat \<lfloor>- 1 / surd_to_real_cnj (sqrt_remainder_step (f k2'))\<rfloor> = a''"
      using red_assoc_step[OF *[of k2']] by (simp add: a''_def)
    finally have a'_a'': "a' = a''" .

    have "surd_to_real_cnj (f k2') \<noteq> a''"
      using surd_to_real_cnj_irrat[OF *[of k2']] by auto
    hence "surd_to_real_cnj (f k2') = 1 / surd_to_real_cnj (sqrt_remainder_step (f k2')) + a''"
      using red_assoc_step(3)[OF *[of k2'], folded a''_def] nz
      by (simp add: field_simps)
    also have "\<dots> = 1 / surd_to_real_cnj (sqrt_remainder_step (f k1')) + a'"
      using k12 by (simp add: a'_a'' k12 Suc Suc' f_def)
    also have nz': "surd_to_real_cnj (f k1') \<noteq> a'"
      using surd_to_real_cnj_irrat[OF *[of k1']] by auto
    hence "1 / surd_to_real_cnj (sqrt_remainder_step (f k1')) + a' = surd_to_real_cnj (f k1')"
      using red_assoc_step(3)[OF *[of k1'], folded a'_def] nz nz'
      by (simp add: field_simps)
    finally have "f k1' = f k2'"
      by (subst (asm) surd_to_real_cnj_eq_iff) auto
    with k12 have "k1' \<le> D' * (D' + 1) \<and> (\<exists>k2\<le>D' * (D' + 1). k1' \<noteq> k2 \<and> f k1' = f k2)"
      by (auto simp: Suc Suc' intro!: exI[of _ k2'])
    hence "k1 \<le> k1'" unfolding k1_def by (rule Least_le)
    thus "k1 = 0" by (simp add: Suc)
  qed auto

  have smallest_period: "f k \<noteq> f 0" if "k \<in> {0<..<k2}" for k
  proof
    assume "f k = f 0"
    hence "k \<le> D' * (D' + 1) \<and> k1 \<noteq> k \<and> f k1 = f k"
      using k12 that by auto
    hence "k2 \<le> k" unfolding k2_def by (rule Least_le)
    with that show False by auto
  qed

  have snd_f_gt_1: "snd (f k) > 1" if "k < k2 - 1" for k
  proof -
    have "snd (f k) \<noteq> 1"
    proof
      assume "snd (f k) = 1"
      hence "f k = (D', 1)" using red_assoc_denom_1[of "fst (f k)"] *[of k]
        by (cases "f k") auto
      hence "sqrt_remainder_step (f k) = (D', D - D'\<^sup>2)" by (auto simp: sqrt_remainder_step_def)
      hence "f (Suc k) = f 0" by (simp add: f_def)
      moreover have "f (Suc k) \<noteq> f 0"
        using that by (intro smallest_period) auto
      ultimately show False by contradiction
    qed
    moreover have "snd (f k) > 0" using *[of k] by (auto simp: red_assoc_def)
    ultimately show ?thesis by simp
  qed

  have sqrt_cfrac_le: "sqrt_cfrac_nth k \<le> D'" if "k < k2 - 1" for k
  proof -
    define p and q where "p = fst (f k)" and "q = snd (f k)"
    have "q \<ge> 2" using snd_f_gt_1[of k] that by (auto simp: q_def)
    also have "sqrt_cfrac_nth k * q \<le> D' * 2"
      using red_assoc_step(5)[OF *[of k]]
      by (simp add: sqrt_cfrac_nth_def p_def q_def case_prod_unfold f_def)
    finally show ?thesis by simp
  qed 

  have last: "f (k2 - 1) = (D', 1)"
  proof -
    define p and q where "p = fst (f (k2 - 1))" and "q = snd (f (k2 - 1))"
    have pq: "f (k2 - 1) = (p, q)" by (simp add: p_def q_def)
    have "sqrt_remainder_step (f (k2 - 1)) = f (Suc (k2 - 1))"
      by (simp add: f_def)
    also from k12 have "Suc (k2 - 1) = k2" by simp
    also have "f k2 = f 0"
      using k12 by simp
    also have "f 0 = (D', D - D'\<^sup>2)" by (simp add: f_def)
    finally have eq: "sqrt_remainder_step (f (k2 - 1)) = (D', D - D'\<^sup>2)" .

    hence "(D - D'\<^sup>2) div q = D - D'\<^sup>2" unfolding sqrt_remainder_step_def Let_def pq
      by auto
    moreover have "q > 0" using *[of "k2 - 1"]
      by (auto simp: red_assoc_def q_def)
    ultimately have "q = 1" using D'_sqr_less_D
      by (subst (asm) div_eq_dividend_iff) auto
    hence "p = D'"
      using red_assoc_denom_1[of p] *[of "k2 - 1"] unfolding pq by auto
    with \<open>q = 1\<close> show "f (k2 - 1) = (D', 1)" unfolding pq by simp
  qed

  have period: "sqrt_remainder_surd n = sqrt_remainder_surd (n mod k2)" for n
    unfolding sqrt_remainder_surd_def using k12 by (intro funpow_cycle) (auto simp: f_def)
  have period': "sqrt_cfrac_nth k = sqrt_cfrac_nth (k mod k2)" for k
    using period[of k] by (simp add: sqrt_cfrac_nth_def)

  have k2_le: "l \<ge> k2" if "l > 0" "\<And>k. sqrt_cfrac_nth (k + l) = sqrt_cfrac_nth k" for l
  proof (rule ccontr)
    assume *: "\<not>(l \<ge> k2)"
    hence "sqrt_cfrac_nth (k2 - Suc l) = sqrt_cfrac_nth (k2 - 1)"
      using that(2)[of "k2 - Suc l"] by simp
    also have "\<dots> = 2 * D'"
      using last by (simp add: sqrt_cfrac_nth_def f_def)
    finally have "2 * D' = sqrt_cfrac_nth (k2 - Suc l)" ..
    also have "\<dots> \<le> D'" using k12 that *
      by (intro sqrt_cfrac_le diff_less_mono2) auto
    finally show False using D'_pos by simp
  qed

  have "l = (LEAST l. 0 < l \<and> (\<forall>n. int (sqrt_cfrac_nth (n + l)) = int (sqrt_cfrac_nth n)))"
    using nonsquare unfolding sqrt_cfrac_def
    by (simp add: l_def sqrt_nat_period_length_def sqrt_cfrac)
  hence l_altdef: "l = (LEAST l. 0 < l \<and> (\<forall>n. sqrt_cfrac_nth (n + l) = sqrt_cfrac_nth n))"
    by simp

  have [simp]: "D \<noteq> 0" using nonsquare by (auto intro!: Nat.gr0I)
  have "\<exists>l. l > 0 \<and> (\<forall>k. sqrt_cfrac_nth (k + l) = sqrt_cfrac_nth k)"
  proof (rule exI, safe)
    fix k show "sqrt_cfrac_nth (k + k2) = sqrt_cfrac_nth k"
      using period'[of k] period'[of "k + k2"] k12 by simp
  qed (insert k12, auto)
  from LeastI_ex[OF this, folded l_altdef]
  have l: "l > 0" "\<And>k. sqrt_cfrac_nth (k + l) = sqrt_cfrac_nth k"
    by (simp_all add: sqrt_cfrac)

  have "l \<le> k2" unfolding l_altdef
    by (rule Least_le) (subst (1 2) period', insert k12, auto)
  moreover have "k2 \<le> l" using k2_le l by blast
  ultimately have [simp]: "l = k2" by auto

  define x' where "x' = (\<lambda>k. -1 / surd_to_real_cnj (f k))"
  {
    fix k :: nat
    have nz: "surd_to_real_cnj (f k) \<noteq> 0" "surd_to_real_cnj (f (Suc k)) \<noteq> 0"
      using surd_to_real_cnj_nz[OF *, of k] surd_to_real_cnj_nz[OF *, of "Suc k"]
      by (simp_all add: f_def)

    have "surd_to_real_cnj (f k) \<noteq> sqrt_cfrac_nth k"
      using surd_to_real_cnj_irrat[OF *[of k]] by auto
    hence "x' (Suc k) = sqrt_cfrac_nth k + 1 / x' k"
      using red_assoc_step(3)[OF *[of k]] nz
      by (simp add: field_simps sqrt_cfrac_nth_def case_prod_unfold f_def x'_def)
  } note x'_Suc = this

  have x'_nz: "x' k \<noteq> 0" for k
    using surd_to_real_cnj_nz[OF *[of k]] by (auto simp: x'_def)
  have x'_0: "x' 0 = real D' + sqrt D"
    using red_assoc_begin by (simp add: x'_def f_def)

  define c' where "c' = cfrac (\<lambda>n. sqrt_cfrac_nth (l - Suc n))"
  define c'' where "c'' = cfrac (\<lambda>n. if n = 0 then 2 * D' else sqrt_cfrac_nth (n - 1))"
  have nth_c' [simp]: "cfrac_nth c' n = sqrt_cfrac_nth (l - Suc n)" for n
    unfolding c'_def by (subst cfrac_nth_cfrac) (auto simp: is_cfrac_def intro!: sqrt_cfrac_pos)
  have nth_c'' [simp]: "cfrac_nth c'' n = (if n = 0 then 2 * D' else sqrt_cfrac_nth (n - 1))" for n
    unfolding c''_def by (subst cfrac_nth_cfrac) (auto simp: is_cfrac_def intro!: sqrt_cfrac_pos)

  have "conv' c' n (x' (l - n)) = x' l" if "n \<le> l" for n
    using that
  proof (induction n)
    case (Suc n)
    have "x' l = conv' c' n (x' (l - n))"
      using Suc.prems by (intro Suc.IH [symmetric]) auto
    also have "l - n = Suc (l - Suc n)"
      using Suc.prems by simp
    also have "x' \<dots> = cfrac_nth c' n + 1 / x' (l - Suc n)"
      by (subst x'_Suc) simp
    also have "conv' c' n \<dots> = conv' c' (Suc n) (x' (l - Suc n))"
      by (simp add: conv'_Suc_right)
    finally show ?case ..
  qed simp_all
  from this[of l] have conv'_x'_0: "conv' c' l (x' 0) = x' 0"
    using k12 by (simp add: x'_def)

  have "cfrac_nth (cfrac_of_real (x' 0)) n = cfrac_nth c'' n" for n
  proof (cases n)
    case 0
    thus ?thesis by (simp add: x'_0 D'_def)
  next
    case (Suc n')
    have "sqrt D \<notin> \<int>"
      using red_assoc_begin(1) red_assoc_begin(2) by auto
    hence "cfrac_nth (cfrac_of_real (real D' + sqrt (real D))) (Suc n') =
          cfrac_nth (cfrac_of_real (sqrt (real D))) (Suc n')"
      by (simp add: cfrac_tl_of_real frac_add_of_nat Ints_add_left_cancel flip: cfrac_nth_tl)
    thus ?thesis using x'_nz[of 0]
      by (simp add: x'_0 sqrt_cfrac Suc)
  qed

  show "sqrt_cfrac_nth (l - n - 2) = sqrt_cfrac_nth n" if "n < l - 1" for n
  proof -
    have "D > 1" using nonsquare by (cases D) (auto intro!: Nat.gr0I)
    hence "D' + sqrt D > 0 + 1" using D'_pos by (intro add_strict_mono) auto
    hence "x' 0 > 1" by (auto simp: x'_0)
    hence "cfrac_nth c' (Suc n) = cfrac_nth (cfrac_of_real (conv' c' l (x' 0))) (Suc n)"
      using \<open>n < l - 1\<close> using cfrac_of_real_conv' by auto
    also have "\<dots> = cfrac_nth (cfrac_of_real (x' 0)) (Suc n)"
      by (subst conv'_x'_0) auto
    also have "\<dots> = cfrac_nth c'' (Suc n)" by fact
    finally show "sqrt_cfrac_nth (l - n - 2) = sqrt_cfrac_nth n"
      by simp
  qed

  show "l > 0" "l \<le> D' * (D' + 1)" using k12 by simp_all
  show "sqrt_remainder_surd n = sqrt_remainder_surd (n mod l)"
       "sqrt_cfrac_nth n = sqrt_cfrac_nth (n mod l)" for n
    using period[of n] period'[of n] by simp_all
  show "sqrt_remainder_surd n \<noteq> sqrt_remainder_surd 0" if "n \<in> {0<..<l}" for n
    using smallest_period[of n] that by (auto simp: f_def)
  show "snd (sqrt_remainder_surd n) > 1" if "n < l - 1" for n
    using that snd_f_gt_1[of n] by (simp add: f_def)
  show "f (l - 1) = (D', 1)" and "sqrt_cfrac_nth (l - 1) = 2 * D'"
    using last by (simp_all add: sqrt_cfrac_nth_def f_def)
  show "sqrt_cfrac_nth k \<le> D'" if "k < l - 1" for k
    using sqrt_cfrac_le[of k] that by simp
  show "l' \<ge> l" if "l' > 0" "\<And>k. sqrt_cfrac_nth (k + l') = sqrt_cfrac_nth k" for l'
    using k2_le[of l'] that by auto
qed

theorem cfrac_sqrt_periodic:
  "cfrac_nth (cfrac_of_real (sqrt D)) (Suc n) =
   cfrac_nth (cfrac_of_real (sqrt D)) (Suc (n mod l))"
  using sqrt_cfrac_periodic[of n] by (metis sqrt_cfrac)

theorem cfrac_sqrt_le: "n \<in> {0<..<l} \<Longrightarrow> cfrac_nth (cfrac_of_real (sqrt D)) n \<le> D'"
  using sqrt_cfrac_le[of "n - 1"]
  by (metis Suc_less_eq Suc_pred add.right_neutral greaterThanLessThan_iff of_nat_mono
            period_nonempty plus_1_eq_Suc sqrt_cfrac)

theorem cfrac_sqrt_last: "cfrac_nth (cfrac_of_real (sqrt D)) l = 2 * D'"
  using sqrt_cfrac_last by (metis One_nat_def Suc_pred period_nonempty sqrt_cfrac)

theorem cfrac_sqrt_palindrome:
  assumes "n \<in> {0<..<l}"
  shows   "cfrac_nth (cfrac_of_real (sqrt D)) (l - n) = cfrac_nth (cfrac_of_real (sqrt D)) n"
proof -
  have "cfrac_nth (cfrac_of_real (sqrt D)) (l - n) = sqrt_cfrac_nth (l - n - 1)"
    using assms by (subst sqrt_cfrac) (auto simp: Suc_diff_Suc)
  also have "\<dots> = sqrt_cfrac_nth (n - 1)"
    using assms by (subst sqrt_cfrac_palindrome [symmetric]) auto
  also have "\<dots> = cfrac_nth (cfrac_of_real (sqrt D)) n"
    using assms by (subst sqrt_cfrac) auto
  finally show ?thesis .
qed

lemma sqrt_cfrac_info_palindrome:
  assumes "sqrt_cfrac_info D = (a, b, cs)"
  shows   "rev (butlast cs) = butlast cs"
proof (rule List.nth_equalityI; safe?)
  fix i assume "i < length (rev (butlast cs))"
  with period_nonempty have "Suc i < length cs" by simp
  thus "rev (butlast cs) ! i = butlast cs ! i"
    using assms cfrac_sqrt_palindrome[of "Suc i"] period_nonempty unfolding l_def
    by (auto simp: sqrt_cfrac_info_def rev_nth algebra_simps Suc_diff_Suc simp del: cfrac.simps)
qed simp_all

lemma sqrt_cfrac_info_last:
  assumes "sqrt_cfrac_info D = (a, b, cs)"
  shows   "last cs = 2 * Discrete.sqrt D"
proof -
  from assms show ?thesis using period_nonempty cfrac_sqrt_last
    by (auto simp: sqrt_cfrac_info_def last_map l_def D'_def Discrete_sqrt_altdef)
qed

text \<open>
  The following lemmas allow us to compute the period of the expansion of the square root:
\<close>
lemma while_option_sqrt_cfrac:
  defines "step' \<equiv> (\<lambda>(as, pq). ((D' + fst pq) div snd pq # as, sqrt_remainder_step pq))"
  defines "b \<equiv> (\<lambda>(_, pq). snd pq \<noteq> 1)"
  defines "initial \<equiv> ([] :: nat list, (D', D - D'\<^sup>2))"
  shows "while_option b step' initial =
           Some (rev (map sqrt_cfrac_nth [0..<l -1]), (D', 1))"
proof -
  define P where 
    "P = (\<lambda>(as, pq). let n = length as
                     in  n < l \<and> pq = sqrt_remainder_surd n \<and> as = rev (map sqrt_cfrac_nth [0..<n]))"
  define \<mu> :: "nat list \<times> (nat \<times> nat) \<Rightarrow> nat" where "\<mu> = (\<lambda>(as, _). l - length as)"
  have [simp]: "P initial" using period_nonempty
    by (auto simp: initial_def P_def sqrt_remainder_surd_def)
  have step': "P (step' s) \<and> Suc (length (fst s)) < l" if "P s" "b s" for s
  proof (cases s)
    case (fields as p q)
    define n where "n = length as"
    from that fields sqrt_remainder_surd_last have "Suc n \<le> l"
      by (auto simp: b_def P_def Let_def n_def [symmetric])
    moreover from that fields sqrt_remainder_surd_last have "Suc n \<noteq> l"
      by (auto simp: b_def P_def Let_def n_def [symmetric])
    ultimately have "Suc n < l" by auto
    with that fields sqrt_remainder_surd_last show "P (step' s) \<and> Suc (length (fst s)) < l"
      by (simp add: b_def P_def Let_def n_def step'_def sqrt_cfrac_nth_def 
                    sqrt_remainder_surd_def case_prod_unfold)
  qed
  have [simp]: "length (fst (step' s)) = Suc (length (fst s))" for s
    by (simp add: step'_def case_prod_unfold)

  have "\<exists>x. while_option b step' initial = Some x"
  proof (rule measure_while_option_Some)
    fix s assume *: "P s" "b s"
    from step'[OF *] show "P (step' s) \<and> \<mu> (step' s) < \<mu> s"
      by (auto simp: b_def \<mu>_def case_prod_unfold intro!: diff_less_mono2)
  qed auto
  then obtain x where x: "while_option b step' initial = Some x" ..
  have "P x" by (rule while_option_rule[OF _ x]) (insert step', auto)
  have "\<not>b x" using while_option_stop[OF x] by auto

  obtain as p q where [simp]: "x = (as, (p, q))" by (cases x)
  define n where "n = length as"
  have [simp]: "q = 1" using \<open>\<not>b x\<close> by (auto simp: b_def)
  have [simp]: "p = D'" using \<open>P x\<close>
    using red_assoc_denom_1[of p] by (auto simp: P_def Let_def)
  have "n < l" "sqrt_remainder_surd (length as) = (D', Suc 0)"
       and as: "as = rev (map sqrt_cfrac_nth [0..<n])" using \<open>P x\<close>
    by (auto simp: P_def Let_def n_def)
  hence "\<not>(n < l - 1)"
    using snd_sqrt_remainder_surd_gt_1[of n] by (intro notI) auto
  with \<open>n < l\<close> have [simp]: "n = l - 1"  by auto
  show ?thesis by (simp add: as x)
qed

lemma while_option_sqrt_cfrac_info:
  defines "step' \<equiv> (\<lambda>(as, pq). ((D' + fst pq) div snd pq # as, sqrt_remainder_step pq))"
  defines "b \<equiv> (\<lambda>(_, pq). snd pq \<noteq> 1)"
  defines "initial \<equiv> ([], (D', D - D'\<^sup>2))"
  shows "sqrt_cfrac_info D =
           (case while_option b step' initial of
             Some (as, _) \<Rightarrow> (Suc (length as), D', rev ((2 * D') # as)))"
proof -
  have "nat (cfrac_nth (cfrac_of_real (sqrt (real D))) (Suc k)) = sqrt_cfrac_nth k" for k
    by (metis nat_int sqrt_cfrac)
  thus ?thesis unfolding assms while_option_sqrt_cfrac
    using period_nonempty sqrt_cfrac_last
    by (cases l) (auto simp: sqrt_cfrac_info_def D'_def l_def Discrete_sqrt_altdef)
qed

end
end

lemma sqrt_nat_period_length_le: "sqrt_nat_period_length D \<le> nat \<lfloor>sqrt D\<rfloor> * (nat \<lfloor>sqrt D\<rfloor> + 1)"
  by (cases "is_square D") (use period_length_le_aux[of D] in auto)

lemma sqrt_nat_period_length_0_iff [simp]:
  "sqrt_nat_period_length D = 0 \<longleftrightarrow> is_square D"
  using period_nonempty[of D] by (cases "is_square D") auto

lemma sqrt_nat_period_length_pos_iff [simp]:
  "sqrt_nat_period_length D > 0 \<longleftrightarrow> \<not>is_square D"
  using period_nonempty[of D] by (cases "is_square D") auto

lemma sqrt_cfrac_info_code [code]:
  "sqrt_cfrac_info D =
     (let D' = Discrete.sqrt D
      in  if D'\<^sup>2 = D then (0, D', [])
          else
            case while_option
                   (\<lambda>(_, pq). snd pq \<noteq> 1)
                   (\<lambda>(as, (p, q)). let X = (p + D') div q; p' = X * q - p
                                   in  (X # as, p', (D - p'\<^sup>2) div q))
                   ([], D', D - D'\<^sup>2)
            of Some (as, _) \<Rightarrow> (Suc (length as), D', rev ((2 * D') # as)))"
proof -
  define D' where "D' = Discrete.sqrt D"
  show ?thesis
  proof (cases "is_square D")
    case True
    hence "D' ^ 2 = D" by (auto simp: D'_def elim!: is_nth_powerE)
    thus ?thesis using True
      by (simp add: D'_def Let_def sqrt_cfrac_info_def sqrt_nat_period_length_def)
  next
    case False
    hence "D' ^ 2 \<noteq> D" by (subst eq_commute) auto
    thus ?thesis using while_option_sqrt_cfrac_info[OF False]
      by (simp add: sqrt_cfrac_info_def D'_def Let_def
                    case_prod_unfold Discrete_sqrt_altdef add_ac sqrt_remainder_step_def)
  qed
qed

lemma sqrt_nat_period_length_code [code]:
  "sqrt_nat_period_length D = fst (sqrt_cfrac_info D)"
  by (simp add: sqrt_cfrac_info_def)

text \<open>
  For efficiency reasons, it is often better to use an array instead of a list:
\<close>
definition sqrt_cfrac_info_array where
  "sqrt_cfrac_info_array D = (case sqrt_cfrac_info D of (a, b, c) \<Rightarrow> (a, b, IArray c))"

lemma fst_sqrt_cfrac_info_array [simp]: "fst (sqrt_cfrac_info_array D) = sqrt_nat_period_length D"
  by (simp add: sqrt_cfrac_info_array_def sqrt_cfrac_info_def)

lemma snd_sqrt_cfrac_info_array [simp]: "fst (snd (sqrt_cfrac_info_array D)) = Discrete.sqrt D"
  by (simp add: sqrt_cfrac_info_array_def sqrt_cfrac_info_def)


definition cfrac_sqrt_nth :: "nat \<times> nat \<times> nat iarray \<Rightarrow> nat \<Rightarrow> nat" where
  "cfrac_sqrt_nth info n =
     (case info of (l, a0, as) \<Rightarrow> if n = 0 then a0 else as !! ((n - 1) mod l))"

lemma cfrac_sqrt_nth:
  assumes "\<not>is_square D"
  shows   "cfrac_nth (cfrac_of_real (sqrt D)) n =
             int (cfrac_sqrt_nth (sqrt_cfrac_info_array D) n)" (is "?lhs = ?rhs")
proof (cases n)
  case (Suc n')
  define l where "l = sqrt_nat_period_length D"
  from period_nonempty[OF assms] have "l > 0" by (simp add: l_def)
  have "cfrac_nth (cfrac_of_real (sqrt D)) (Suc n') =
        cfrac_nth (cfrac_of_real (sqrt D)) (Suc (n' mod l))" unfolding l_def
    using cfrac_sqrt_periodic[OF assms, of n'] by simp
  also have "\<dots> = map (\<lambda>n. nat (cfrac_nth (cfrac_of_real (sqrt D)) (Suc n))) [0..<l] ! (n' mod l)"
    using \<open>l > 0\<close> by (subst nth_map) auto
  finally show ?thesis using Suc
    by (simp add: sqrt_cfrac_info_array_def sqrt_cfrac_info_def l_def cfrac_sqrt_nth_def)
qed (simp_all add: sqrt_cfrac_info_def sqrt_cfrac_info_array_def
                   Discrete_sqrt_altdef cfrac_sqrt_nth_def)

lemma sqrt_cfrac_code [code]:
  "sqrt_cfrac D =
     (let info = sqrt_cfrac_info_array D;
          (l, a0, _) = info
      in  if l = 0 then cfrac_of_int (int a0) else cfrac (cfrac_sqrt_nth info))"
proof (cases "is_square D")
  case True
  hence "sqrt (real D) = of_int (Discrete.sqrt D)"
    by (auto elim!: is_nth_powerE)
  thus ?thesis using True
    by (auto simp: Let_def sqrt_cfrac_info_array_def sqrt_cfrac_info_def sqrt_cfrac_def)
next
  case False
  have "cfrac_sqrt_nth (sqrt_cfrac_info_array D) n > 0" if "n > 0" for n
  proof -
    have "int (cfrac_sqrt_nth (sqrt_cfrac_info_array D) n) > 0"
      using False that by (subst cfrac_sqrt_nth [symmetric]) auto
    thus ?thesis by simp
  qed
  moreover have "sqrt D \<notin> \<rat>"
    using False irrat_sqrt_nonsquare by blast
  ultimately have "sqrt_cfrac D = cfrac (cfrac_sqrt_nth (sqrt_cfrac_info_array D))"
    using cfrac_sqrt_nth[OF False]
    by (intro cfrac_eqI) (auto simp: sqrt_cfrac_def is_cfrac_def)
  thus ?thesis
    using False by (simp add: Let_def sqrt_cfrac_info_array_def sqrt_cfrac_info_def)
qed

text \<open>
  As a test, we determine the continued fraction expansion of $\sqrt{129}$, which is
  $[11; \overline{2, 1, 3, 1, 6, 1, 3, 1, 2, 22}]$ (a period length of 10):
\<close>
value "let info = sqrt_cfrac_info_array 129 in info"
value "sqrt_nat_period_length 129"

text \<open>
  We can also compute convergents of $\sqrt{129}$ and observe that the difference between
  the square of the convergents and 129 vanishes quickly::
\<close>
value "map (conv (sqrt_cfrac 129)) [0..<10]"
value "map (\<lambda>n. \<bar>conv (sqrt_cfrac 129) n ^ 2 - 129\<bar>) [0..<20]"

end