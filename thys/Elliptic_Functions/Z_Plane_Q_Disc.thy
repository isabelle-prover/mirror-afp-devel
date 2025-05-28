subsection \<open>The $z$-plane vs the $q$-disc\<close>
theory Z_Plane_Q_Disc
  imports "HOL-Complex_Analysis.Complex_Analysis" "Theta_Functions.Nome"
begin

text \<open>
  In the study of modular forms and related subjects, we often need convert between the upper
  half of the complex plane (typically with a parameter written as $z$ or $\tau$) and the unit
  disc (with a parameter written as $q$).

  This is particularly interesting for 1-periodic functions $f(z)$
  (or more generally $n$-periodic functions where $n > 0$ is an integer) since such functions
  have a Fourier expansion in terms of $q$, i.e.\ we can view them both as functions $f(z)$ for
  $\text{Im}(z) > 0$ or $f(q)$ for $|q| < 1$, where the latter is only well-defined due to the
  periodicity.
\<close>

subsubsection \<open>The neighbourhood of $i\infty$\<close>

text \<open>
  The following filter describes the neighbourhood of $i\infty$, i.e.\ the neighbourhood of all
  points with sufficiently big imaginary value. In terms of $q$, this corresponds to the point
  $q = 0$.
\<close>
definition at_ii_inf :: "complex filter" ("at'_\<i>\<infinity>") where
  "at_ii_inf = filtercomap Im at_top"

lemma eventually_at_ii_inf:
  "eventually (\<lambda>z. Im z > c) at_ii_inf"
  unfolding at_ii_inf_def using filterlim_at_top_dense by blast

lemma eventually_at_ii_inf_iff:
  "(\<forall>\<^sub>F z in at_ii_inf. P z) \<longleftrightarrow> (\<exists>c. \<forall>z. Im z > c \<longrightarrow> P z)"
  by (simp add: at_ii_inf_def eventually_filtercomap_at_top_dense)

lemma eventually_at_ii_inf_iff':
  "(\<forall>\<^sub>F z in at_ii_inf. P z) \<longleftrightarrow> (\<exists>c. \<forall>z. Im z \<ge> c \<longrightarrow> P z)"
  by (simp add: at_ii_inf_def eventually_filtercomap_at_top_linorder)

lemma filterlim_Im_at_ii_inf: "filterlim Im at_top at_\<i>\<infinity>"
  unfolding at_ii_inf_def by (rule filterlim_filtercomap)

lemma filterlim_at_ii_infI:
  assumes "filterlim f F at_top"
  shows   "filterlim (\<lambda>x. f (Im x)) F at_\<i>\<infinity>"
  using filterlim_filtercomapI[of f F at_top Im] assms by (simp add: at_ii_inf_def)

lemma filtermap_scaleR_at_ii_inf:
  assumes "c > 0"
  shows   "filtermap (\<lambda>z. c *\<^sub>R z) at_ii_inf = at_ii_inf"
proof (rule antisym)
  show "filtermap (\<lambda>z. c *\<^sub>R z) at_ii_inf \<le> at_ii_inf"
  proof (rule filter_leI)
    fix P
    assume "eventually P at_ii_inf"
    then obtain b where b: "\<And>z. Im z > b \<Longrightarrow> P z"
      by (auto simp: eventually_at_ii_inf_iff)
    have "eventually (\<lambda>z. Im z > b / c) at_ii_inf"
      by (intro eventually_at_ii_inf)
    thus "eventually P (filtermap (\<lambda>z. c *\<^sub>R z) at_ii_inf)"
      unfolding eventually_filtermap
      by eventually_elim (use assms in \<open>auto intro!: b simp: field_simps\<close>)
  qed
next
  show "filtermap (\<lambda>z. c *\<^sub>R z) at_ii_inf \<ge> at_ii_inf"
  proof (rule filter_leI)
    fix P
    assume "eventually P (filtermap (\<lambda>z. c *\<^sub>R z) at_ii_inf)"
    then obtain b where b: "\<And>z. Im z > b \<Longrightarrow> P (c *\<^sub>R z)"
      by (auto simp: eventually_at_ii_inf_iff eventually_filtermap)
    have b': "P z" if "Im z > b * c" for z
      using b[of "z /\<^sub>R c"] that assms by (auto simp: field_simps)
    have "eventually (\<lambda>z. Im z > b * c) at_ii_inf"
      by (intro eventually_at_ii_inf)
    thus "eventually P at_ii_inf"
      unfolding eventually_filtermap
      by eventually_elim (use assms in \<open>auto intro!: b' simp: field_simps\<close>)
  qed
qed

lemma at_ii_inf_neq_bot [simp]: "at_ii_inf \<noteq> bot"
  unfolding at_ii_inf_def by (intro filtercomap_neq_bot_surj surj_Im) auto


subsubsection \<open>The parameter $q$\<close>

text \<open>
  The standard mapping from $z$ to $q$ is $z \mapsto \exp(2 i \pi z)$, which is also sometimes
  referred to as the square of the \<^emph>\<open>nome\<close>. However, if the period of the function is $n > 01$, 
  we have to opt for $z \mapsto \exp(2 i \pi z/n)$ instead, so we allow this additional flexibility
  here.

  Note that the inverse mapping from $q$ to $z$ is multivalued. We arbitrarily choose the strip
  with $\text{Re}(z) \in (-\frac{1}{2}, \frac{1}{2}]$ as the codomain of the inverse mapping.
\<close>
definition to_q :: "nat \<Rightarrow> complex \<Rightarrow> complex" where
  "to_q n \<tau> = exp (2 * pi * \<i> * \<tau> / n)"

lemma to_nome_conv_to_q: "to_nome = to_q 2"
  by (auto simp: fun_eq_iff to_q_def to_nome_def mult_ac)

lemma to_q_conv_to_nome: "to_q n z = to_nome (2 * z / of_nat n)"
  by (simp add: to_q_def to_nome_def field_simps)

lemma to_q_add: "to_q n (w + z) = to_q n w * to_q n z"
  and to_q_diff: "to_q n (w - z) = to_q n w / to_q n z"
  and to_q_minus: "to_q n (-w) = inverse (to_q n w)"
  and to_q_power: "to_q n w ^ k = to_q n (of_nat k * w)"
  and to_q_power_int: "to_q n w powi m = to_q n (of_int m * w)"
  by (simp_all add: to_q_def add_divide_distrib diff_divide_distrib 
                    exp_add exp_diff exp_minus ring_distribs mult_ac exp_power_int
               flip: exp_of_nat_mult)

interpretation to_q: periodic_fun_simple "to_q n" "of_nat n"
proof
  show "to_q n (z + of_nat n) = to_q n z" for z
    by (cases "n = 0") (simp_all add: to_q_def ring_distribs exp_add add_divide_distrib)
qed

lemma to_q_of_nat_period [simp]: "to_q n (of_nat n) = 1"
  by (simp add: to_q_def exp_eq_polar)

lemma to_q_of_int [simp]: 
  assumes "int n dvd m"
  shows   "to_q n (of_int m) = 1"
proof -
  obtain k where m_eq: "m = int n * k"
    using assms by (elim dvdE)
  have "to_q n (of_int m) = to_q n (of_nat n * of_int k)"
    by (simp add: m_eq)
  also have "\<dots> = to_q n (of_nat n) powi k"
    by (simp only: to_q_power_int mult_ac)
  also have "\<dots> = 1"
    by simp
  finally show ?thesis .
qed

lemma to_q_of_nat [simp]: 
  assumes "n dvd m"
  shows   "to_q n (of_nat m) = 1"
  using to_q_of_int[of n "int m"] assms by (simp del: to_q_of_int)

lemma to_q_numeral [simp]: 
  assumes "n dvd numeral m"
  shows   "to_q n (numeral m) = 1"
  using to_q_of_nat[of n "numeral m"] assms by (simp del: to_q_of_nat)

lemma to_q_of_nat_period_1 [simp]: "w \<in> \<int> \<Longrightarrow> to_q (Suc 0) w = 1"
  by (auto elim!: Ints_cases)

lemma Ln_to_q:
  assumes "x \<in> Re -` {n/2<..n/2}" "n > 0"
  shows "Ln (to_q n x) = 2 * pi * \<i> * x / n"
unfolding to_q_def 
proof (rule Ln_exp)
  have "-1/2 * pi < Re x / n * pi" "Re x / n * pi \<le> 1/2 * pi"
    using assms by (auto simp: field_simps)
  thus "-pi < Im (complex_of_real (2 * pi) * \<i> * x / n)" 
    using assms(2) by (auto simp: field_simps)
  show "Im (complex_of_real (2 * pi) * \<i> * x / n) \<le> pi"
    using \<open>Re x / n * pi \<le> 1/2 * pi\<close> using assms(2) by (auto simp: field_simps)
qed

lemma to_q_nonzero [simp]: "to_q n \<tau> \<noteq> 0"
  by (auto simp: to_q_def)

lemma norm_to_q [simp]: "norm (to_q n z) = exp (-2 * pi * Im z / n)"
  by (simp add: to_q_def)

lemma to_q_has_field_derivative [derivative_intros]:
  assumes [derivative_intros]: "(f has_field_derivative f') (at z)" and n: "n > 0"
  shows   "((\<lambda>z. to_q n (f z)) has_field_derivative (2 * pi * \<i> * f' / n * to_q n (f z))) (at z)"
  unfolding to_q_def by (rule derivative_eq_intros refl | (use n in simp; fail))+  

lemma deriv_to_q [simp]: "n > 0 \<Longrightarrow> deriv (to_q n) z = 2 * pi * \<i> / n * to_q n z"
  by (auto intro!: DERIV_imp_deriv derivative_eq_intros)

lemma to_q_holomorphic_on [holomorphic_intros]:
  "f holomorphic_on A \<Longrightarrow> n > 0 \<Longrightarrow> (\<lambda>z. to_q n (f z)) holomorphic_on A"
  unfolding to_q_def by (intro holomorphic_intros) auto

lemma to_q_analytic_on [analytic_intros]:
  "f analytic_on A \<Longrightarrow> n > 0 \<Longrightarrow> (\<lambda>z. to_q n (f z)) analytic_on A"
  unfolding to_q_def by (intro analytic_intros) auto

lemma to_q_continuous_on [continuous_intros]:
  "continuous_on A f \<Longrightarrow> n > 0 \<Longrightarrow> continuous_on A (\<lambda>z. to_q n (f z))"
  unfolding to_q_def by (intro continuous_intros) auto

lemma to_q_continuous [continuous_intros]:
  "continuous F f \<Longrightarrow> n > 0 \<Longrightarrow> continuous F (\<lambda>z. to_q n (f z))"
  unfolding to_q_def by (auto intro!: continuous_intros simp: divide_inverse)

lemma to_q_tendsto [tendsto_intros]:
  "(f \<longlongrightarrow> x) F \<Longrightarrow> n > 0 \<Longrightarrow> ((\<lambda>z. to_q n (f z)) \<longlongrightarrow> to_q n x) F"
  unfolding to_q_def by (intro tendsto_intros) auto

lemma to_q_eq_to_qE:
  assumes "to_q m \<tau> = to_q m \<tau>'" "m > 0"
  obtains n where "\<tau>' = \<tau> + of_int n * of_nat m"
proof -
  from assms obtain n where "2 * pi * \<i> * \<tau> / m = 2 * pi * \<i> * \<tau>' / m + real_of_int (2 * n) * pi * \<i>"
    using assms unfolding to_q_def exp_eq by blast
  also have "\<dots> = 2 * pi * \<i> * (\<tau>' / m + of_int n)"
    by (simp add: algebra_simps)
  also have "2 * pi * \<i> * \<tau> / m = 2 * pi * \<i> * (\<tau> / m)"
    by simp
  finally have "\<tau> / m = \<tau>' / m + of_int n"
    by (subst (asm) mult_cancel_left) auto
  hence "\<tau> = \<tau>' + of_int n * of_nat m"
    using \<open>m > 0\<close> by (metis divide_add_eq_iff divide_cancel_right of_nat_eq_0_iff rel_simps(70))
  thus ?thesis
    by (intro that[of "-n"]) auto
qed

lemma to_q_inj_on_standard:
  assumes n: "n > 0"
  shows "inj_on (to_q n) (Re -` {-n/2..<n/2})"
  unfolding inj_on_def
proof safe+
  fix x y::complex
  assume eq: "to_q n x = to_q n y" 
      and xRe: "Re x \<in> {- real n/2..<real n/2}" and yRe:"Re y \<in> {- real n/2..<real n/2}"
  obtain rx ix where x:"x=Complex rx ix" by (meson complex.exhaust_sel)
  obtain ry iy where y:"y=Complex ry iy" by (meson complex.exhaust_sel)
  define pp where "pp= 2*pi"
  have rxry:"rx/n\<in>{-1/2..<1/2}" "ry/n\<in>{-1/2..<1/2}" 
    using xRe yRe x y n by (auto simp: field_simps)

  define prx where "prx = pp*rx / n"
  define pry where "pry = pp*ry / n"

  have coseq:"exp (- (pp * ix / n)) * cos prx 
        = exp (- (pp * iy / n)) * cos pry"
  proof -
    have "Re (to_q n x) = Re (to_q n y)"
      using eq by simp
    then show ?thesis
      unfolding x y to_q_def Re_exp Im_exp pp_def prx_def pry_def using assms
      by simp 
  qed
  moreover have sineq:"exp (- (pp * ix / n)) * sin prx 
        = exp (- (pp * iy / n)) * sin pry"
  proof -
    have "Im (to_q n x) = Im (to_q n y)"
      using eq by simp
    then show ?thesis
      unfolding x y to_q_def Re_exp Im_exp pp_def prx_def pry_def
      by simp
  qed
  ultimately have "(exp (- (pp * ix / n)) * sin (prx))
    / (exp (- (pp * ix / n)) * cos (prx))
    = (exp (- (pp * iy / n)) * sin (pry))
    / (exp (- (pp * iy / n)) * cos (pry))"
    by auto
  then have teq:"tan prx  = tan pry"
    by (subst (asm) (1 2) mult_divide_mult_cancel_left) (auto simp: tan_def)

  have sgn_eq_cos:"sgn (cos (prx)) = sgn (cos (pry))" 
  proof -
    have "sgn (exp (- (pp * ix / n)) * cos prx) 
        = sgn (exp (- (pp * iy / n)) * cos pry)"
      using coseq by simp
    then show ?thesis by (simp add:sgn_mult)
  qed
  have sgn_eq_sin:"sgn (sin (prx)) = sgn (sin (pry))" 
  proof -
    have "sgn (exp (- (pp * ix / n)) * sin prx) 
        = sgn (exp (- (pp * iy / n)) * sin pry)"
      using sineq by simp
    then show ?thesis by (simp add:sgn_mult)
  qed
  
  have "prx=pry" if "tan prx = 0"
  proof -
    define pi2 where "pi2 = pi /2"
    have [simp]: "cos pi2 = 0" "cos (-pi2) = 0"
      "sin pi2 = 1" "sin (-pi2) = -1"
      unfolding pi2_def by auto
    have "prx\<in>{-pi,-pi2,0,pi2}"
    proof -
      from tan_eq_0_Ex[OF that]
      obtain k0 where k0:"prx = real_of_int k0 / 2 * pi"
        by auto
      then have "rx / n = real_of_int k0 / 4" 
        unfolding pp_def prx_def using n by (auto simp: field_simps)
      with rxry have "k0\<in>{-2,-1,0,1}"
        by auto
      then show ?thesis using k0 pi2_def by auto
    qed
    moreover have "pry\<in>{-pi,-pi2,0,pi2}" 
    proof -
      from tan_eq_0_Ex that teq
      obtain k0 where k0:"pry = real_of_int k0 / 2 * pi"
        by auto
      then have "ry / n = real_of_int k0/4" 
        unfolding pp_def pry_def using n by (auto simp: field_simps)
      with rxry have "k0\<in>{-2,-1,0,1}"
        by auto
      then show ?thesis using k0 pi2_def by auto
    qed
    moreover note sgn_eq_cos sgn_eq_sin
    ultimately show "prx=pry" by auto
  qed
  moreover have "prx=pry" if "tan prx \<noteq> 0"
  proof -
    from tan_eq[OF teq that]
    obtain k0 where k0:"prx = pry + real_of_int k0 * pi"
      by auto
    then have "pi * (2 * rx / n) = pi* (2 * ry / n + real_of_int k0)"
      unfolding pp_def prx_def pry_def by (auto simp: algebra_simps)
    then have "real_of_int k0 = 2 * ((rx - ry) / n)" 
      by (subst diff_divide_distrib, subst (asm) mult_left_cancel) (use n in auto)
    also have "... \<in> {-2<..<2}"
      using rxry using n by (auto simp: field_simps)
    finally have "real_of_int k0 \<in> {- 2<..<2}" by simp
    then have "k0 \<in> {-1,0,1}" by auto
    then have "prx=pry-pi \<or> prx = pry \<or> prx = pry+pi"
      using k0 by auto
    moreover have False if "prx=pry-pi \<or> prx = pry+pi"
    proof -
      have "cos prx = - cos pry"
        using that by auto
      moreover note sgn_eq_cos
      ultimately have "cos prx = 0" 
        by (simp add: sgn_zero_iff)
      then have "tan prx = 0" unfolding tan_def by auto
      then show False 
        using \<open>tan prx \<noteq> 0\<close> unfolding prx_def by auto
    qed
    ultimately show "prx = pry" by auto
  qed
  ultimately have "prx=pry" by auto
  then have "rx = ry" unfolding prx_def pry_def pp_def using n by auto
  moreover have "ix = iy"
  proof - 
    have "cos prx \<noteq>0 \<or>  sin prx\<noteq>0"
      using sin_zero_norm_cos_one by force 
    then have "exp (- (pp * ix))  = exp (- (pp * iy))"
      using coseq sineq \<open>prx = pry\<close> n by auto
    then show "ix= iy" unfolding pp_def by auto
  qed
  ultimately show "x=y" unfolding x y by auto
qed

lemma filterlim_to_q_at_ii_inf' [tendsto_intros]:
  assumes n: "n > 0"
  shows   "filterlim (to_q n) (nhds 0) at_ii_inf"
proof -
  have "((\<lambda>z. exp (- (2 * pi * Im z) / n)) \<longlongrightarrow> 0) at_ii_inf"
    unfolding at_ii_inf_def 
    by (rule filterlim_compose[OF _ filterlim_filtercomap]) (use n in real_asymp)
  hence "filterlim (\<lambda>z. norm (to_q n z)) (nhds 0) at_ii_inf"
    by (simp add: to_q_def)
  thus ?thesis
    using tendsto_norm_zero_iff by blast
qed

lemma filterlim_to_q_at_ii_inf [tendsto_intros]: "n > 0 \<Longrightarrow> filterlim (to_q n) (at 0) at_ii_inf"
  using filterlim_to_q_at_ii_inf' by (auto simp: filterlim_at)  

lemma eventually_to_q_neq:
  assumes n: "n > 0"
  shows "eventually (\<lambda>w. to_q n w \<noteq> to_q n z) (at z)"
proof -
  have "eventually (\<lambda>w. w \<in> ball z 1 - {z}) (at z)"
    by (intro eventually_at_in_open) auto
  thus ?thesis
  proof eventually_elim
    case (elim w)
    show ?case
    proof
      assume "to_q n w = to_q n z"
      then obtain m where eq: "z = w + of_int m * of_nat n"
        using n by (elim to_q_eq_to_qE)
      with elim have "real_of_int (\<bar>m\<bar> * int n) < 1"
        by (simp add: dist_norm norm_mult)
      hence "\<bar>m\<bar> * int n < 1"
        by linarith
      with n have "m = 0"
        by (metis add_0 mult_pos_pos not_less of_nat_0_less_iff zero_less_abs_iff zless_imp_add1_zle)
      thus False
        using elim eq by simp
    qed
  qed
qed


lemma inj_on_to_q:
  assumes n: "n > 0"
  shows "inj_on (to_q n) (ball z (1/2))"
proof
  fix x y assume xy: "x \<in> ball z (1/2)" "y \<in> ball z (1/2)" "to_q n x = to_q n y"
  from xy have "dist x z < 1 / 2" "dist y z < 1 / 2"
    by (auto simp: dist_commute)
  hence "dist x y < 1 / 2 + 1 / 2"
    using dist_triangle_less_add by blast
  moreover obtain m where m: "y = x + of_int m * of_nat n"
    by (rule to_q_eq_to_qE[OF xy(3) n]) auto
  ultimately have "real_of_int (\<bar>m\<bar> * int n) < 1"
    by (auto simp: dist_norm norm_mult)
  hence "\<bar>m\<bar> * int n < 1"
    by linarith
  with n have "m = 0"
    by (metis add_0 mult_pos_pos not_less of_nat_0_less_iff zero_less_abs_iff zless_imp_add1_zle)
  thus "x = y"
    using m by simp
qed

lemma filtermap_to_q_nhds:
  assumes n: "n > 0"
  shows "filtermap (to_q n) (nhds z) = nhds (to_q n z)"
proof (rule filtermap_nhds_open_map')
  show "open (ball z (1 / 2))" "z \<in> ball z (1 / 2)" "isCont (to_q n) z"
    using n by (auto intro!: continuous_intros)
  show "open (to_q n ` S)" if "open S" "S \<subseteq> ball z (1 / 2)" for S
  proof (rule open_mapping_thm3)
    show "inj_on (to_q n) S"
      using that by (intro inj_on_subset[OF inj_on_to_q] n)
  qed (use that n in \<open>auto intro!: holomorphic_intros\<close>)
qed

lemma filtermap_to_q_at:
  assumes n: "n > 0"
  shows "filtermap (to_q n) (at z) = at (to_q n z)"
  using filtermap_to_q_nhds
proof (rule filtermap_nhds_eq_imp_filtermap_at_eq)
  show "eventually (\<lambda>x. to_q n x = to_q n z \<longrightarrow> x = z) (at z)"
    using eventually_to_q_neq[OF n, of z] by eventually_elim (use n in auto)
qed fact+

lemma is_pole_to_q_iff:
  assumes n: "n > 0"
  shows "is_pole f (to_q n x) \<longleftrightarrow> is_pole (f o to_q n) x"
proof -
  have "filtermap f (at (to_q n x)) 
          = filtermap f (filtermap (to_q n) (at x)) "
    unfolding filtermap_to_q_at[OF n] by simp
  also have "... = filtermap (f \<circ> to_q n) (at x)"
    unfolding filtermap_filtermap unfolding comp_def by simp
  finally show ?thesis unfolding is_pole_def filterlim_def by simp
qed

definition of_q :: "nat \<Rightarrow> complex \<Rightarrow> complex" where
  "of_q n q = ln q / (2 * pi * \<i> / n)"

lemma Im_of_q: "q \<noteq> 0 \<Longrightarrow> n > 0 \<Longrightarrow> Im (of_q n q) = -n * ln (norm q) / (2 * pi)"
  by (simp add: of_q_def Im_divide power2_eq_square)

lemma Im_of_q_gt:
  assumes "norm q < exp (-2 * pi * c / n)" "q \<noteq> 0" "n > 0"
  shows   "Im (of_q n q) > c"
proof -
  have "-Im (of_q n q) = n * ln (norm q) / (2 * pi)"
    using assms by (subst Im_of_q) auto
  also have "ln (norm q) < ln (exp (-2 * pi * c / n))"
    by (subst ln_less_cancel_iff) (use assms in auto)
  hence "n * ln (norm q) / (2 * pi) < n * ln (exp (-2 * pi * c / n)) / (2 * pi)"
    using \<open>n > 0\<close> by (intro mult_strict_left_mono divide_strict_right_mono) auto
  also have "\<dots> = -c"
    using \<open>n > 0\<close> by simp
  finally show ?thesis
    by simp
qed

lemma to_q_of_q [simp]: "q \<noteq> 0 \<Longrightarrow> n > 0 \<Longrightarrow> to_q n (of_q n q) = q"
  by (simp add: to_q_def of_q_def)

lemma of_q_to_q:
  assumes "m > 0"
  shows "\<exists>n. of_q m (to_q m \<tau>) = \<tau> + of_int n * of_nat m"
proof
  show "of_q m (to_q m \<tau>) =
          \<tau> + of_int (-unwinding (complex_of_real (2 * pi) * \<i> * \<tau> / m)) * of_nat m"
    using unwinding[of "2 * pi * \<i> * \<tau> / m"] assms
    by (simp add: of_q_def to_q_def field_simps)
qed

lemma filterlim_norm_at_0: "filterlim norm (at_right 0) (at 0)"
  unfolding filterlim_at
  by (auto simp: eventually_at tendsto_norm_zero_iff intro: exI[of _ 1])

lemma filterlim_of_q_at_0:
  assumes n: "n > 0"
  shows "filterlim (of_q n) at_ii_inf (at 0)"
proof -
  have "filterlim (\<lambda>q. -n * ln (norm q) / (2 * pi)) at_top (at 0)"
    by (rule filterlim_compose[OF _ filterlim_norm_at_0]) (use n in real_asymp)
  also have "eventually (\<lambda>q::complex. q \<noteq> 0) (at 0)"
    by (auto simp: eventually_at intro: exI[of _ 1])
  hence "eventually (\<lambda>q. -n * ln (norm q) / (2 * pi) = Im (of_q n q)) (at 0)"
    by eventually_elim (use n in \<open>simp add: Im_of_q\<close>)
  hence "filterlim (\<lambda>q::complex. -n * ln (norm q) / (2 * pi)) at_top (at 0) \<longleftrightarrow>
         filterlim (\<lambda>q. Im (of_q n q)) at_top (at 0)"
    by (intro filterlim_cong) auto
  finally show ?thesis
    by (simp add: at_ii_inf_def filterlim_filtercomap_iff o_def)
qed

lemma at_ii_inf_filtermap:
  assumes "n > 0"
  shows   "filtermap (to_q n) at_ii_inf = at 0"
proof (rule filtermap_fun_inverse[OF  filterlim_of_q_at_0 filterlim_to_q_at_ii_inf])
  have "eventually (\<lambda>x. x \<noteq> 0) (at (0 :: complex))"
    by (rule eventually_neq_at_within)
  thus "\<forall>\<^sub>F x in at 0. to_q n (of_q n x) = x"
    by eventually_elim (use assms in auto)
qed fact+

lemma eventually_at_ii_inf_to_q:
  assumes n: "n > 0"
  shows "eventually P (at 0) = (\<forall>\<^sub>F x in at_ii_inf. P (to_q n x))"
proof -
  have "(\<forall>\<^sub>F x in at_ii_inf. P (to_q n x)) \<longleftrightarrow> (\<forall>\<^sub>F x in filtermap (to_q n) at_ii_inf. P x)"
    by (simp add: eventually_filtermap)
  also have "\<dots> \<longleftrightarrow> eventually P (at 0)"
    by (simp add: at_ii_inf_filtermap n)
  finally show ?thesis ..
qed

lemma of_q_tendsto:
  assumes "x \<in> Re -` {real n / 2<..real n / 2}" "n > 0"
  shows "of_q n \<midarrow>to_q n x\<rightarrow> x"
proof -
  obtain rx ix where x:"x = Complex rx ix" 
    using complex.exhaust_sel by blast
  have "Re (to_q n x) > 0" if "Im (to_q n x) = 0" 
  proof -
    have "sin (2 * pi * rx / n) = 0" 
      using that unfolding to_q_def x Im_exp Re_exp by simp
    then obtain k where "pi * (2 * rx / n) = pi * real_of_int k"
      unfolding sin_zero_iff_int2 by (auto simp: algebra_simps)
    hence k: "2 * rx / n = real_of_int k"
      using mult_cancel_left pi_neq_zero by blast
    moreover have "2*rx/n \<in> {-1<..<1}"
      using assms unfolding x by simp
    ultimately have "k=0" by auto
    then have "rx=0" using k \<open>n > 0\<close> by auto
    then show ?thesis unfolding to_q_def x
      using Re_exp by simp
  qed
  then have "to_q n x \<notin> \<real>\<^sub>\<le>\<^sub>0" 
    unfolding complex_nonpos_Reals_iff
    unfolding Im_exp Re_exp to_q_def
    by (auto simp add: complex_nonpos_Reals_iff)
  moreover have "Ln (to_q n x) / (2 * complex_of_real pi * \<i> / n) = x" 
    by (subst Ln_to_q) (use assms in \<open>auto simp: field_simps\<close>)
  ultimately show "of_q n \<midarrow>to_q n x\<rightarrow> x"
    unfolding of_q_def by (auto intro!: tendsto_eq_intros)
qed

lemma of_q_to_q_Re:
  assumes "x \<in> Re -` {real n / 2<..real n / 2}" "n > 0"
  shows "of_q n (to_q n x) = x"
proof -
  have "- pi < Im (complex_of_real (2 * pi) * \<i> * x / n)"
  proof -
    have "pi* (-1/2) < pi * (Re x / n)" 
      by (rule mult_strict_left_mono) (use assms in auto)
    then show ?thesis by auto
  qed
  moreover have "Im (complex_of_real (2 * pi) * \<i> * x / n) \<le> pi"
    using assms by auto
  ultimately show ?thesis using assms(2)
    unfolding to_q_def of_q_def
    by (subst Ln_exp) auto
qed

end