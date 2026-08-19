section \<open>A ``safe'' power operator for real and complex numbers\<close>
theory Safe_Power
  imports "HOL-Complex_Analysis.Complex_Analysis"
begin

text \<open>
  Isabelle/HOL currently has three different power operators:

    \<^item> \<^const>\<open>power\<close>, denoted \<^term>\<open>x ^ n\<close>, where \<open>n\<close> is a natural number and \<open>x\<close> is an element of a
      multiplicatively written monoid (\<^class>\<open>monoid_mult\<close>).

    \<^item> \<^const>\<open>power_int\<close>, denoted \<^term>\<open>x powi n\<close>, where \<open>n\<close> is an integer and \<open>x\<close> is an element of
      a multiplicatively written monoid with some kind of inverse operation (typically a 
      \<^class>\<open>division_ring\<close>).

    \<^item> \<^const>\<open>powr\<close>, denoted \<^term>\<open>x powr y\<close>, where \<open>x\<close> and \<open>y\<close> are complete normed real algebra
      with a 1 and some kind of natural logarithm. In practice, the only reasonable examples of
      such a structure are probably \<^typ>\<open>real\<close> and \<^typ>\<open>complex\<close>. It is defined as 
      \<^prop>\<open>x powr y = exp (ln x * y)\<close>, except when \<open>x = 0\<close>, in which case it returns \<open>0\<close> by
      convention.

   All three of these operators are required, since none of them is a generalisation of another.
   For example, the \<^const>\<open>power\<close> operator is the most restrictive in what the right argument can
   be, but it is the most general in terms of what the left argument can be.

   For the most part, the three operators agree in all the cases where they are simultaneously
   defined, but there are some caveats.

   First of all, note that different conventions apply for $0^0$: We have \<^prop>\<open>x ^ n = 1\<close> and
   \<^prop>\<open>x powr n = 1\<close> for any \<open>x\<close>, including for \<open>x = 0\<close>, whereas \<^prop>\<open>0 powr y = 0\<close> for any \<open>y\<close>, 
   including \<open>y = 0\<close>.

   Second, for negative real \<open>x\<close>, the \<^const>\<open>powr\<close> operator inherits somewhat strange behaviour from
   the real-valued \<^const>\<open>ln\<close> operator, which in Isabelle/HOL is defined symmetrically,
   i.e.\ \<^prop>\<open>ln (-x) = ln x\<close>, so we also have \<^prop>\<open>(-x) powr y = x powr y\<close> for real \<open>x\<close> and \<open>y\<close>. 
   This means that while \<^prop>\<open>(-1::real) ^ 3 = -1\<close> as expected, we have 
   \<^prop>\<open>(-1::real) powr 3 = 1\<close>. It is therefore better to consider \<^term>\<open>x powr y\<close> to be undefined
   for negative real \<open>x\<close>.

   In the following, we will define a ``safe'' version of the \<^const>\<open>powr\<close> operator that coincides
   with \<^const>\<open>power\<close> and \<^const>\<open>power_int\<close> whenever applicable.
\<close>


text \<open>
  First, we define the inverse of the canonical ring homomorphism $\mathbb{Z}\to R$ using
  the choice operator, i.e.\ for any $x\in\mathbb{Z}$, the operator \<open>the_int\<close> gives us an
  integer $n$ such that $x = n = \underbrace{1 + \ldots + 1}_{n\ \text{times}}$. 
  For $x\notin\mathbb{Z}$, the operator's behaviour is unspecified.
\<close>
definition the_int :: "'a :: ring_char_0 \<Rightarrow> int" where
  "the_int x = (THE n. x = of_int n)"

lemma the_int_of_int [simp]: "the_int (of_int n :: 'a :: ring_char_0) = n"
  unfolding the_int_def using theI'[of "\<lambda>m. of_int n = (of_int m :: 'a)"] by simp

lemma the_int_eqI: "of_int n = x \<Longrightarrow> the_int x = n"
  by (metis the_int_of_int)

lemma the_int_0 [simp]: "the_int 0 = 0"
  using the_int_of_int[of 0] by (simp del: the_int_of_int)

lemma the_int_1 [simp]: "the_int 1 = 1"
  using the_int_of_int[of 1] by (simp del: the_int_of_int)

lemma the_int_of_nat [simp]: "the_int (of_nat n) = int n"
  using the_int_of_int[of "int n"] by (simp del: the_int_of_int)

lemma the_int_numeral [simp]: "the_int (numeral n) = numeral n"
  using the_int_of_int[of "numeral n"] by (simp del: the_int_of_int)

lemma the_int_uminus [simp]: "x \<in> \<int> \<Longrightarrow> the_int (-x) = -the_int x"
  by (metis Ints_cases of_int_minus the_int_of_int)

lemma of_int_the_int: "x \<in> \<int> \<Longrightarrow> of_int (the_int x) = x"
  by (elim Ints_cases) auto

lemma the_int_add: "x \<in> \<int> \<Longrightarrow> y \<in> \<int> \<Longrightarrow> the_int (x + y) = the_int x + the_int y"
  by (rule the_int_eqI) (auto simp: of_int_the_int)

lemma the_int_diff: "x \<in> \<int> \<Longrightarrow> y \<in> \<int> \<Longrightarrow> the_int (x - y) = the_int x - the_int y"
  by (rule the_int_eqI) (auto simp: of_int_the_int)

lemma the_int_mult: "x \<in> \<int> \<Longrightarrow> y \<in> \<int> \<Longrightarrow> the_int (x * y) = the_int x * the_int y"
  by (rule the_int_eqI) (auto simp: of_int_the_int)

lemma the_int_power: "x \<in> \<int> \<Longrightarrow> the_int (x ^ n) = the_int x ^ n"
  by (rule the_int_eqI) (auto simp: of_int_the_int)


text \<open>
  Now we simply define the \<open>powr'\<close> operator as a version of the \<^const>\<open>powr\<close> operator that
  falls back to the \<^const>\<open>power_int\<close> operator whenever possible.
\<close>
definition powr' :: "'a :: {division_ring, ln} \<Rightarrow> 'a \<Rightarrow> 'a" (infixr \<open>powr''\<close> 80) where
  "x powr' y = (if y \<in> \<int> then x powi (the_int y) else x powr y)"

lemma powr'_powr: "y \<notin> \<int> \<Longrightarrow> x powr' y = x powr y"
  by (simp add: powr'_def)

lemma powr'_0_left [simp]: "y \<noteq> 0 \<Longrightarrow> 0 powr' y = 0"
  by (auto simp: powr'_def elim!: Ints_cases)

lemma powr'_0_left_if: "0 powr' y = (if y = 0 then 1 else 0)"
  by (auto simp: powr'_def elim!: Ints_cases)

lemma powr'_of_int [simp]: "x powr' of_int n = x powi n"
  by (simp add: powr'_def)

lemma powr'_of_nat [simp]: "x powr' of_nat n = x ^ n"
  by (simp add: powr'_def)

lemma powr'_0 [simp]: "x powr' 0 = 1"
  by (simp add: powr'_def)

lemma powr'_1 [simp]: "x powr' 1 = x"
  by (simp add: powr'_def)

lemma powr'_numeral [simp]: "x powr' numeral n = x ^ numeral n"
  by (simp add: powr'_def)

text \<open>
  If $x$ is positive or if $x$ is non-negative and $y$ is positive, the safe power operator
  and the normal power operator agree..
\<close>
lemma powr'_real: "x \<ge> 0 \<Longrightarrow> x \<noteq> 0 \<or> y > 0 \<Longrightarrow> x powr' y = x powr (y :: real)"
  by (auto simp: powr'_def powr_real_of_int' elim!: Ints_cases)

lemma powr'_real_pos: "x > 0 \<Longrightarrow> x powr' y = x powr (y :: real)"
  by (auto simp: powr'_def powr_real_of_int' elim!: Ints_cases)

text \<open>
  For complex inputs, the two operators always agree except in the case of $0^0$.
\<close>
lemma powr'_complex: "x \<noteq> 0 \<or> y \<noteq> 0 \<Longrightarrow> x powr' y = x powr (y :: complex)"
  by (auto simp: powr'_def complex_powr_of_int elim!: Ints_cases)

lemma powr'_complex_of_real:
  "x \<ge> 0 \<or> y \<in> \<int> \<Longrightarrow> complex_of_real x powr' of_real y = (of_real (x powr' y))"
  by (auto simp: powr'_def powr_Reals_eq elim!: Ints_cases)

lemma powr'_Reals_eq: "\<lbrakk>x \<in> \<real>; y \<in> \<real>; Re x \<ge> 0\<rbrakk> \<Longrightarrow> x powr' y = of_real (Re x powr' Re y)"
  by (cases "x = 0"; cases "y = 0")
     (auto elim!: Reals_cases simp: powr'_complex powr'_real powr_Reals_eq)

text \<open>
  For this reason, the \<^const>\<open>powr'\<close> operator is holomorphic in both inputs except for a branch
  cut along the non-positive reals.
\<close>
lemma holomorphic_on_powr' [holomorphic_intros]:
  assumes "f holomorphic_on A" "g holomorphic_on A" "\<And>x. x \<in> A \<Longrightarrow> f x \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "(\<lambda>x. f x powr' g x) holomorphic_on A"
proof -
  have "(\<lambda>x. f x powr g x) holomorphic_on A"
    by (intro holomorphic_intros assms)
  also have "(\<lambda>x. f x powr g x) holomorphic_on A \<longleftrightarrow> (\<lambda>x. f x powr' g x) holomorphic_on A"
    by (intro holomorphic_cong refl) (subst powr'_complex, auto dest: assms(3))
  finally show ?thesis .
qed

lemma analytic_on_powr' [analytic_intros]:
  assumes "f analytic_on A" "g analytic_on A" "\<And>x. x \<in> A \<Longrightarrow> f x \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "(\<lambda>x. f x powr' g x) analytic_on A"
proof -
  from assms(1) obtain B where B: "open B" "A \<subseteq> B" "f holomorphic_on B"
    using analytic_on_holomorphic by blast
  from assms(2) obtain C where C: "open C" "A \<subseteq> C" "g holomorphic_on C"
    using analytic_on_holomorphic by blast
  note [holomorphic_intros] = holomorphic_on_subset[OF B(3)] holomorphic_on_subset[OF C(3)]
  have "(\<lambda>x. f x powr' g x) holomorphic_on ((B \<inter> C) \<inter> f -` (-\<real>\<^sub>\<le>\<^sub>0))"
    by (intro holomorphic_intros) auto
  moreover have "open ((B \<inter> C) \<inter> f -` (-\<real>\<^sub>\<le>\<^sub>0))" using B(1) C(1)
    by (intro continuous_open_preimage holomorphic_on_imp_continuous_on holomorphic_intros) auto
  moreover have "A \<subseteq> (B \<inter> C) \<inter> f -` (-\<real>\<^sub>\<le>\<^sub>0)"
    using assms(3) B C by auto
  ultimately show ?thesis
    using analytic_on_holomorphic by blast
qed

(* TODO: sort out version in library *)
lemma has_field_derivative_powr_complex [derivative_intros]:
  assumes "(f has_field_derivative f') (at x within A)"
  assumes "(g has_field_derivative g') (at x within A)"
  assumes "f x \<notin> (\<real>\<^sub>\<le>\<^sub>0 :: complex set)"
  shows   "((\<lambda>x. f x powr g x) has_field_derivative 
             (f x powr g x * (f' / f x * g x + g' * ln (f x)))) (at x within A)"
proof -
  have "((\<lambda>x. exp (ln (f x) * g x)) has_field_derivative 
          (exp (ln (f x) * g x) * (f' / f x * g x + g' * ln (f x)))) (at x within A)"
    by (auto intro!: derivative_eq_intros assms simp: field_simps)
  also have "(exp (ln (f x) * g x) * (f' / f x * g x + g' * ln (f x))) = 
             (f x powr g x * (f' / f x * g x + g' * ln (f x)))"
    by (use assms(3) in \<open>auto simp: powr_def mult_ac\<close>)
  also have "((\<lambda>x. exp (ln (f x) * g x)) has_field_derivative \<dots>) (at x within A) \<longleftrightarrow> ?thesis"
  proof (intro has_field_derivative_cong_eventually)
    have "eventually (\<lambda>z. z \<in> -{0}) (nhds (f x))"
      by (intro eventually_nhds_in_open) (use assms(3) in auto)
    moreover have "continuous (at x within A) f"
      using assms(1) DERIV_continuous by blast
    hence "filterlim f (nhds (f x)) (at x within A)"
      by (simp add: continuous_within)
    ultimately have "eventually (\<lambda>x. f x \<in> -{0}) (at x within A)"
      by (rule eventually_compose_filterlim)
    thus "\<forall>\<^sub>F x in at x within A. exp (ln (f x) * g x) = f x powr g x"
      by eventually_elim (auto simp: powr_def mult_ac)
  next
    show "exp (Ln (f x) * g x) = f x powr g x"
      by (use assms(3) in \<open>auto simp: powr_def mult_ac\<close>)
  qed
  finally show ?thesis .
qed

(* TODO: real *)
lemma has_field_derivative_powr'_complex [derivative_intros]:
  assumes "(f has_field_derivative f') (at x within A)"
  assumes "(g has_field_derivative g') (at x within A)"
  assumes "f x \<notin> (\<real>\<^sub>\<le>\<^sub>0 :: complex set)"
  shows   "((\<lambda>x. f x powr' g x) has_field_derivative 
             (f x powr' g x * (f' / f x * g x + g' * ln (f x)))) (at x within A)"
proof -
  have "((\<lambda>x. exp (ln (f x) * g x)) has_field_derivative 
          (exp (ln (f x) * g x) * (f' / f x * g x + g' * ln (f x)))) (at x within A)"
    by (auto intro!: derivative_eq_intros assms simp: field_simps)
  also have "(exp (ln (f x) * g x) * (f' / f x * g x + g' * ln (f x))) = 
             (f x powr' g x * (f' / f x * g x + g' * ln (f x)))"
    by (subst powr'_complex) (use assms(3) in \<open>auto simp: powr_def mult_ac\<close>)
  also have "((\<lambda>x. exp (ln (f x) * g x)) has_field_derivative \<dots>) (at x within A) \<longleftrightarrow> ?thesis"
  proof (intro has_field_derivative_cong_eventually)
    have "eventually (\<lambda>z. z \<in> -{0}) (nhds (f x))"
      by (intro eventually_nhds_in_open) (use assms(3) in auto)
    moreover have "continuous (at x within A) f"
      using assms(1) DERIV_continuous by blast
    hence "filterlim f (nhds (f x)) (at x within A)"
      by (simp add: continuous_within)
    ultimately have "eventually (\<lambda>x. f x \<in> -{0}) (at x within A)"
      by (rule eventually_compose_filterlim)
    thus "\<forall>\<^sub>F x in at x within A. exp (ln (f x) * g x) = f x powr' g x"
      by eventually_elim (auto simp: powr'_complex powr_def mult_ac)
  next
    show "exp (Ln (f x) * g x) = f x powr' g x"
      by (subst powr'_complex) (use assms(3) in \<open>auto simp: powr_def mult_ac\<close>)
  qed
  finally show ?thesis .
qed

lemma has_field_derivative_powr'_Ints:
  assumes "(f has_field_derivative f') (at x within A)"
  assumes "c \<in> (\<int> :: 'a :: {real_normed_field, ln} set)" "c \<in> \<nat> \<or> f x \<noteq> 0"
  shows   "((\<lambda>x. f x powr' c) has_field_derivative (c * f x powr' (c-1) * f')) (at x within A)"
proof -
  from assms(2) obtain n where c: "c = of_int n"
    by (elim Ints_cases)
  have "n \<ge> 0 \<or> f x \<noteq> 0"
    using assms(3) c
    by (metis Nats_cases dual_order.refl int_nat_eq nat_int of_int_eq_iff of_int_of_nat_eq)
  hence "((\<lambda>x. f x powi n) has_field_derivative (of_int n * f x powi (n - 1) * f')) (at x within A)"
    by (auto intro!: derivative_eq_intros assms(1))
  also have "of_int n * f x powi (n - 1) * f' = c * f x powr' (of_int (n - 1)) * f'"
    by (subst powr'_of_int) (use c in auto)
  also have "of_int (n - 1) = c - 1"
    using c by simp
  finally show ?thesis
    unfolding c by (subst powr'_of_int) auto
qed

lemma continuous_on_powr'_complex [continuous_intros]:
  assumes "A \<subseteq> {z. Re (f z) \<ge> 0 \<or> Im (f z) \<noteq> 0}"
  assumes "\<And>z. z \<in> A \<Longrightarrow> f z = 0 \<Longrightarrow> Re (g z) > 0"
  assumes "continuous_on A f" "continuous_on A g"
  shows   "continuous_on A (\<lambda>z. f z powr' g z)"
proof -
  have "continuous_on A (\<lambda>z. f z powr g z)"
    by (intro continuous_intros assms)
  also have "?this \<longleftrightarrow> ?thesis"
  proof (rule continuous_on_cong)
    fix x assume "x \<in> A"
    hence "f x \<noteq> 0 \<or> g x \<noteq> 0"
      using assms(2)[of x] assms(1) by (auto simp: complex_eq_iff)
    thus "f x powr g x = f x powr' g x"
      by (simp add: powr'_complex)
  qed auto
  finally show ?thesis .
qed

lemma tendsto_powr'_complex [tendsto_intros]:
  fixes f g :: "_ \<Rightarrow> complex"
  assumes "a \<notin> \<real>\<^sub>\<le>\<^sub>0 \<or> (a = 0 \<and> Re b > 0)" and "(f \<longlongrightarrow> a) F" "(g \<longlongrightarrow> b) F"
  shows   "((\<lambda>z. f z powr' g z) \<longlongrightarrow> a powr' b) F"
proof -
  have "((\<lambda>z. f z powr g z) \<longlongrightarrow> a powr b) F"
    by (rule tendsto_intros) (use assms in auto)
  also have "a \<noteq> 0 \<or> b \<noteq> 0"
    using assms(1) by auto
  hence "a powr b = a powr' b"
    by (simp add: powr'_complex)
  also have "eventually (\<lambda>z. f z \<noteq> 0 \<or> g z \<noteq> 0) F"
  proof (cases "a = 0")
    case True
    have "eventually (\<lambda>z. g z \<in> -{0}) F"
      by (rule eventually_compose_filterlim[OF eventually_nhds_in_open assms(3)])
         (use True assms(1) in auto)
    thus ?thesis
      by eventually_elim auto
  next
    case False
    have "eventually (\<lambda>z. f z \<in> -{0}) F"
      by (rule eventually_compose_filterlim[OF eventually_nhds_in_open assms(2)]) (use False in auto)
    thus ?thesis
      by eventually_elim auto
  qed
  hence "eventually (\<lambda>z. f z powr g z = f z powr' g z) F"
    by eventually_elim (auto simp: powr'_complex)
  hence "((\<lambda>z. f z powr g z) \<longlongrightarrow> a powr' b) F \<longleftrightarrow> ?thesis"
    by (intro filterlim_cong) auto
  finally show ?thesis .
qed

(* TODO: replace version in library? *)
lemma ln_at_0': "filterlim (ln :: real \<Rightarrow> real) at_bot (at 0)"
proof -
  have "filterlim abs (at_right 0) (at (0::real))"
  proof (rule tendsto_imp_filterlim_at_right)
    show "abs \<midarrow>0\<rightarrow> (0::real)"
      by (rule tendsto_rabs_zero) auto
  next
    show "eventually (\<lambda>x. \<bar>x\<bar> > (0::real)) (at 0)"
      using eventually_neq_at_within by eventually_elim auto
  qed
  hence "filterlim (\<lambda>x. ln \<bar>x\<bar> :: real) at_bot (at 0)"
    by (rule filterlim_compose[OF ln_at_0])
  also have "?this \<longleftrightarrow> filterlim (\<lambda>x. ln x :: real) at_bot (at 0)"
    by (simp add: ln_real_def cong: if_cong)
  finally show ?thesis .
qed

(* TODO: replace version in library *)
lemma tendsto_powr_real [tendsto_intros]:
  fixes f g :: "_ \<Rightarrow> real"
  assumes "(f \<longlongrightarrow> a) F" "(g \<longlongrightarrow> b) F"
  assumes "a = 0 \<longrightarrow> b > 0" 
  shows   "((\<lambda>z. f z powr g z) \<longlongrightarrow> a powr b) F"
proof (cases "a = 0")
  case False
  thus ?thesis
    using assms by (auto intro!: tendsto_intros)
next
  case [simp]: True
  have "((\<lambda>z. if f z = 0 then 0 else exp (g z * ln (f z))) \<longlongrightarrow> 0) F"
  proof (rule filterlim_If)
    show "((\<lambda>z. exp (g z * ln (f z))) \<longlongrightarrow> 0) (inf F (principal {z. f z \<noteq> 0}))"
    proof (rule filterlim_compose[OF exp_at_bot])
      show "filterlim (\<lambda>z. g z * ln (f z)) at_bot (inf F (principal {z. f z \<noteq> 0}))"
      proof (rule filterlim_tendsto_pos_mult_at_bot)
        show "(g \<longlongrightarrow> b) (inf F (principal {z. f z \<noteq> 0}))"
          using assms(2) by (rule filterlim_mono) auto
      next
        show "filterlim (\<lambda>x. ln (f x)) at_bot (inf F (principal {z. f z \<noteq> 0}))"
        proof (rule filterlim_compose[OF ln_at_0'])
          show "filterlim f (at 0) (inf F (principal {z. f z \<noteq> 0}))"
          proof (rule filterlim_atI)
            have "\<forall>\<^sub>F x in principal {z. f z \<noteq> 0}. f x \<noteq> 0"
              by (auto simp: eventually_principal)
            thus "\<forall>\<^sub>F x in inf F (principal {z. f z \<noteq> 0}). f x \<noteq> 0"
              by (rule filter_leD[rotated]) auto
          next
            show "(f \<longlongrightarrow> 0) (inf F (principal {z. f z \<noteq> 0}))"
              using assms(1) by (rule filterlim_mono) auto
          qed
        qed
      qed (use assms(3) in auto)
    qed
  qed auto
  thus ?thesis
    by (simp add: powr_def)
qed

lemmas [tendsto_intros del] = tendsto_powr tendsto_powr'

lemma tendsto_powr'_real [tendsto_intros]:
  fixes f g :: "_ \<Rightarrow> real"
  assumes "(f \<longlongrightarrow> a) F" "(g \<longlongrightarrow> b) F"
  assumes "a > 0 \<or> (a = 0 \<and> b > 0)" 
  shows   "((\<lambda>z. f z powr' g z) \<longlongrightarrow> a powr' b) F"
proof (cases "a = 0")
  case False
  with assms have "a > 0"
    by auto
  have ev: "eventually (\<lambda>x. f x \<in> {0<..}) F"
    by (rule eventually_compose_filterlim[OF eventually_nhds_in_open assms(1)]) 
       (use \<open>a > 0\<close> in auto)
  have "((\<lambda>z. f z powr g z) \<longlongrightarrow> a powr b) F"
    by (rule tendsto_powr_real) (use assms in auto)
  also have "?this \<longleftrightarrow> ((\<lambda>z. f z powr' g z) \<longlongrightarrow> a powr' b) F"
    using \<open>a > 0\<close> by (intro filterlim_cong) (auto simp: powr'_real intro!: eventually_mono[OF ev])
  finally show ?thesis .
next
  case [simp]: True
  with assms have "b > 0"
    by auto
  have "((\<lambda>z. f z powr' g z) \<longlongrightarrow> 0) F"
    unfolding powr'_def
  proof (rule filterlim_If)
    have "((\<lambda>z. f z powr g z) \<longlongrightarrow> 0) F"
      by (rule tendsto_eq_intros assms(1,2))+ (use \<open>b > 0\<close> in auto)
    thus "((\<lambda>z. f z powr g z) \<longlongrightarrow> 0) (inf F (principal {z. g z \<notin> \<int>}))"
      by (rule filterlim_mono) auto
  next
    show "((\<lambda>z. f z powi the_int (g z)) \<longlongrightarrow> 0) (inf F (principal {z. g z \<in> \<int>}))"
    proof (cases "inf F (principal {z. g z \<in> \<int>}) = bot")
      case False
      define n' where "n' = round b"
      define n where "n = nat n'"
      have "b = n'"
      proof -
        from False have "\<exists>\<^sub>F x in F. g x \<in> \<int>"
          by (auto simp: trivial_limit_def eventually_inf_principal frequently_def)
        moreover have "eventually (\<lambda>x. g x \<in> ball b (1/2)) F"
          by (rule eventually_compose_filterlim[OF eventually_nhds_in_open assms(2)]) auto
        hence "eventually (\<lambda>x. dist (g x) n' < 1) F"
        proof eventually_elim
          case (elim x)
          have "dist (g x) n' \<le> dist (g x) b + dist b n'"
            by (rule dist_triangle)
          also have "dist (g x) b < 1/2"
            using elim by (simp add: dist_commute)
          also have "dist b n' \<le> 1 / 2"
            using of_int_round_abs_le[of b] by (auto simp: n'_def dist_norm abs_minus_commute)
          finally show ?case
            by simp
        qed
        hence "eventually (\<lambda>x. g x \<in> \<int> \<longrightarrow> g x = n') F"
          by eventually_elim (auto elim!: Ints_cases simp: dist_of_int)
        ultimately have "\<exists>\<^sub>F x in F. g x = n'"
          by (rule frequently_rev_mp)
        moreover have "F \<noteq> bot"
          using \<open>_ \<noteq> bot\<close> by auto
        ultimately show "b = n'"
          using assms(2) limit_frequently_eq \<open>F \<noteq> bot\<close> by blast
      qed

      have "b = n" "n > 0"
        using \<open>b = n'\<close> assms by (auto simp: n_def)

      have ev: "eventually (\<lambda>x. g x = n) (inf F (principal {z. g z \<in> \<int>}))"
      proof -
        have "eventually (\<lambda>x. g x \<in> ball b 1) F"
          by (rule eventually_compose_filterlim[OF eventually_nhds_in_open assms(2)]) auto
        hence "eventually (\<lambda>x. g x \<in> \<int> \<longrightarrow> g x = n') F"
          by eventually_elim (auto simp: \<open>b = n'\<close> dist_of_int elim!: Ints_cases)
        thus ?thesis
          by (simp add: eventually_inf_principal \<open>b = n'\<close> flip: \<open>b = n\<close>)
      qed

      have "((\<lambda>z. f z ^ n) \<longlongrightarrow> 0) F"
        using assms(1) by (rule tendsto_eq_intros) (use \<open>n > 0\<close> in auto)
      hence "((\<lambda>z. f z ^ n) \<longlongrightarrow> 0) (inf F (principal {z. g z \<in> \<int>}))"
        by (rule filterlim_mono) auto
      also have "?this \<longleftrightarrow> ((\<lambda>z. f z powi the_int (g z)) \<longlongrightarrow> 0) (inf F (principal {z. g z \<in> \<int>}))"
      proof (rule filterlim_cong)
        show "\<forall>\<^sub>F x in inf F (principal {z. g z \<in> \<int>}). f x ^ n = f x powi the_int (g x)"
          using ev by eventually_elim auto
      qed auto
      finally show ?thesis .
    qed auto
  qed
  thus ?thesis
    using \<open>b > 0\<close> by simp
qed

lemma continuous_powr'_complex [continuous_intros]: 
  assumes "continuous F f" "continuous F g"
  assumes "Re (f (netlimit F)) \<ge> 0 \<or> Im (f (netlimit F)) \<noteq> 0"
  assumes "f (netlimit F) = 0 \<longrightarrow> Re (g (netlimit F)) > 0"
  shows   "continuous F (\<lambda>z. f z powr' g z :: complex)"
  using assms unfolding continuous_def
  by (intro tendsto_intros) (auto simp: complex_nonpos_Reals_iff complex_eq_iff)

end