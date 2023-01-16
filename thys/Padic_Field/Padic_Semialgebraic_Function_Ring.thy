theory Padic_Semialgebraic_Function_Ring
  imports Padic_Field_Powers
begin

section\<open>Rings of Semialgebraic Functions\<close>

text\<open>
  In order to efficiently formalize Denef's proof of Macintyre's theorem, it is necessary to be
  able to reason about semialgebraic functions algebraically. For example, we need to consider
  polynomials in one variable whose coefficients are semialgebraic functions, and take their
  Taylor expansions centered at a semialgebraic function. To facilitate this kind of reasoning, it
  is necessary to construct, for each arity $m$, a ring \texttt{SA(m)} of semialgebraic functions in
  $m$ variables. These functions must be extensional functions which are undefined outside of the
  carrier set of $\mathbb{Q}_p^m$.

  The developments in this theory are mainly lemmas and defintitions which build the necessary
  theory to prove the cell decomposition theorems of \<^cite>\<open>"denef1986"\<close>, and finally Macintyre's
  Theorem, which says that semi-algebraic sets are closed under projections.
\<close>
(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Some eint Arithmetic\<close>
(**************************************************************************************************)
(**************************************************************************************************)

context padic_fields
begin

lemma eint_minus_ineq':
  assumes "a \<le> eint N"
  assumes "b - a \<le> c"
  shows "b - eint N \<le> c"
  using assms by(induction c, induction b, induction a, auto )

lemma eint_minus_plus:
"a - (eint b + eint c) = a - eint b - eint c"
  apply(induction a)
  apply (metis diff_add_eq_diff_diff_swap idiff_eint_eint plus_eint_simps(1) semiring_normalization_rules(24))
  using idiff_infinity by presburger

lemma eint_minus_plus':
"a - (eint b + eint c) = a - eint c - eint b"
  by (metis add.commute eint_minus_plus)

lemma eint_minus_plus'':
  assumes "a - eint c - eint b = eint f"
  shows "a - eint c - eint f =  eint b"
  using assms  apply(induction a )
  apply (metis add.commute add_diff_cancel_eint eint.distinct(2) eint_add_cancel_fact)
  by simp

lemma uminus_involutive[simp]:
"-(-x::eint) = x"
  apply(induction x)
  unfolding uminus_eint_def by auto

lemma eint_minus:
"(a::eint) - (b::eint) = a + (-b)"
  apply(induction a)
   apply(induction b)
proof -
  fix int :: int and inta :: int
  have "\<forall>e ea. (ea::eint) + (e + - ea) = ea - ea + e"
    by (simp add: eint_uminus_eq)
  then have "\<forall>i ia. eint (ia + i) + - eint ia = eint i"
    by (metis ab_group_add_class.ab_diff_conv_add_uminus add.assoc add_minus_cancel idiff_eint_eint plus_eint_simps(1))
  then show "eint inta - eint int = eint inta + - eint int"
    by (metis ab_group_add_class.ab_diff_conv_add_uminus add.commute add_minus_cancel idiff_eint_eint)
next
  show "\<And>int. eint int - \<infinity> = eint int + - \<infinity>"
  by (metis eint_uminus_eq i0_ne_infinity idiff_infinity_right idiff_self plus_eq_infty_iff_eint uminus_involutive)
  show " \<infinity> - b = \<infinity> + - b"
    apply(induction b)
  apply simp
    by auto
qed

lemma eint_mult_Suc:
   "eint (Suc k) * a = eint k * a + a"
  apply(induction a)
  apply (metis add.commute eSuc_eint mult_eSuc' of_nat_Suc)
  using plus_eint_simps(3) times_eint_simps(4)
  by presburger

lemma eint_mult_Suc_mono:
assumes "a \<le> eint b \<longrightarrow> eint (int k) * a \<le> eint (int k) * eint b"
shows "a \<le> eint b \<longrightarrow> eint (int (Suc k)) * a \<le> eint (int (Suc k)) * eint b"
  using assms eint_mult_Suc
  by (metis add_mono_thms_linordered_semiring(1))

lemma eint_nat_mult_mono:
  assumes "(a::eint) \<le> b"
  shows "eint (k::nat)*a \<le> eint k*b"
proof-
  have "(a::eint) \<le> b \<longrightarrow> eint (k::nat)*a \<le> eint k*b"
    apply(induction k) apply(induction b)
  apply (metis eint_ile eq_iff mult_not_zero of_nat_0 times_eint_simps(1))
  apply simp
 apply(induction b)
    using eint_mult_Suc_mono apply blast
  using eint_ord_simps(3) times_eint_simps(4) by presburger
  thus ?thesis using assms by blast
qed

lemma eint_Suc_zero:
"eint (int (Suc 0)) * a = a"
  apply(induction a)
  apply simp
  by simp

lemma eint_add_mono:
  assumes "(a::eint) \<le> b"
  assumes "(c::eint) \<le> d"
  shows "a + c \<le> b + d"
  using assms
  by (simp add: add_mono)

lemma eint_nat_mult_mono_rev:
  assumes "k > 0"
  assumes "eint (k::nat)*a \<le> eint k*b"
  shows "(a::eint) \<le> b"
proof(rule ccontr)
  assume "\<not> a \<le> b"
  then have A: "b < a"
    using leI by blast
  have "b < a \<longrightarrow> eint (k::nat)*b < eint k*a"
    apply(induction b) apply(induction a)
      using A assms eint_ord_simps(2) times_eint_simps(1) zmult_zless_mono2_lemma apply presburger
    using eint_ord_simps(4) nat_mult_not_infty times_eint_simps(4) apply presburger
    using eint_ord_simps(6) by blast
  then have "eint (k::nat)*b < eint k*a"
    using A by blast
  hence "\<not> eint (k::nat)*a \<le> eint k*b"
    by (metis \<open>\<not> a \<le> b\<close> antisym eint_nat_mult_mono linear neq_iff)
  then show False using assms by blast
qed


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Lemmas on Function Ring Operations\<close>
(**************************************************************************************************)
(**************************************************************************************************)

lemma Qp_funs_is_cring:
"cring (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
  using F.M_cring by blast

lemma Qp_funs_is_monoid:
"monoid (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
  using F.is_monoid by blast

lemma Qp_funs_car_memE:
  assumes "f \<in> carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
  shows "f \<in> (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) \<rightarrow> (carrier Q\<^sub>p)"
  by (simp add: assms ring_pow_function_ring_car_memE(2))

lemma Qp_funs_car_memI:
  assumes "g \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  assumes "\<And>x. x \<notin> (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) \<Longrightarrow> g x = undefined"
  shows "g \<in> carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
apply(rule Qp.function_ring_car_memI)
  using assms  apply blast
  using assms by blast

lemma Qp_funs_car_memI':
  assumes "g \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  assumes "restrict g (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) = g"
  shows "g \<in> carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
  apply(intro Qp_funs_car_memI assms)
  using assms  unfolding restrict_def
  by (metis (mono_tags, lifting))

lemma Qp_funs_car_memI'':
  assumes "f \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  assumes "g = (\<lambda> x \<in> (carrier (Q\<^sub>p\<^bsup>n\<^esup>)). f x)"
  shows "g \<in> carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
  apply(rule Qp_funs_car_memI)
  using assms
  apply (meson restrict_Pi_cancel)
  by (metis assms(2) restrict_def)

lemma Qp_funs_one:
"\<one>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> = (\<lambda> x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). \<one>)"
  unfolding function_ring_def function_one_def
  by (meson monoid.select_convs(2))

lemma Qp_funs_zero:
"\<zero>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> = (\<lambda> x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). \<zero>\<^bsub>Q\<^sub>p\<^esub>)"
  unfolding function_ring_def function_zero_def
  by (meson ring_record_simps(11))

lemma Qp_funs_add:
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f \<in> (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) \<rightarrow> carrier Q\<^sub>p"
  assumes "g \<in> (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) \<rightarrow> carrier Q\<^sub>p"
  shows "(f \<oplus>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> g) x = f x \<oplus>\<^bsub>Q\<^sub>p\<^esub> g x"
  using assms function_ring_def[of "carrier (Q\<^sub>p\<^bsup>n\<^esup>)" "Q\<^sub>p"]
  unfolding function_add_def
  by (metis (mono_tags, lifting) restrict_apply' ring_record_simps(12))

lemma Qp_funs_add':
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f \<in> (carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
  assumes "g \<in> (carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
  shows "(f \<oplus>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> g) x = f x \<oplus>\<^bsub>Q\<^sub>p\<^esub> g x"
  using assms Qp_funs_add Qp_funs_car_memE
  by blast

lemma Qp_funs_add'':
  assumes "f \<in> (carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
  assumes "g \<in> (carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
  shows "(f \<oplus>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> g) = (\<lambda> x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). f x \<oplus>\<^bsub>Q\<^sub>p\<^esub> g x)"
  unfolding function_ring_def function_add_def using ring_record_simps(12)
  by metis

lemma Qp_funs_add''':
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "(f \<oplus>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> g) x = f x \<oplus>\<^bsub>Q\<^sub>p\<^esub> g x"
  using assms function_ring_def[of "carrier (Q\<^sub>p\<^bsup>n\<^esup>)" "Q\<^sub>p"]
  unfolding function_add_def
  by (metis (mono_tags, lifting) restrict_apply' ring_record_simps(12))

lemma Qp_funs_mult:
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f \<in> (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) \<rightarrow> carrier Q\<^sub>p"
  assumes "g \<in> (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) \<rightarrow> carrier Q\<^sub>p"
  shows "(f \<otimes>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> g) x = f x \<otimes> g x"
  using assms function_ring_def[of "carrier (Q\<^sub>p\<^bsup>n\<^esup>)" "Q\<^sub>p"]
  unfolding function_mult_def
  by (metis (no_types, lifting) monoid.select_convs(1) restrict_apply')

lemma Qp_funs_mult':
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f \<in> (carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
  assumes "g \<in> (carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
  shows "(f \<otimes>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> g) x = f x \<otimes> g x"
  using assms Qp_funs_mult Qp_funs_car_memE
  by blast

lemma Qp_funs_mult'':
  assumes "f \<in> (carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
  assumes "g \<in> (carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
  shows "(f \<otimes>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> g) = (\<lambda> x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). f x \<otimes> g x)"
  unfolding function_ring_def function_mult_def using ring_record_simps(5)
  by metis

lemma Qp_funs_mult''':
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "(f \<otimes>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> g) x = f x \<otimes> g x"
  using assms function_ring_def[of "carrier (Q\<^sub>p\<^bsup>n\<^esup>)" "Q\<^sub>p"]
  unfolding function_mult_def
  by (metis (mono_tags, lifting) monoid.select_convs(1) restrict_apply')

lemma Qp_funs_a_inv:
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f \<in> (carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
  shows "(\<ominus>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f) x = \<ominus> (f x)"
  using assms local.function_uminus_eval
  by (simp add: local.function_uminus_eval'')

lemma Qp_funs_a_inv':
  assumes "f \<in> (carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
  shows "(\<ominus>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f) = (\<lambda> x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). \<ominus> (f x))"
proof fix x
  show "(\<ominus>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f) x = (\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>n\<^esup>). \<ominus> f x) x"
    apply(cases "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)")
     apply (metis (no_types, lifting) Qp_funs_a_inv assms restrict_apply')
  by (simp add: assms local.function_ring_not_car)
qed

abbreviation(input) Qp_const ("\<cc>\<^bsub>_\<^esub>_") where
"Qp_const n c \<equiv> constant_function (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) c"

lemma Qp_constE:
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "Qp_const n c x = c"
  using assms unfolding constant_function_def
  by (meson restrict_apply')

lemma Qp_funs_Units_memI:
  assumes "f \<in> (carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
  assumes "\<And> x. x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<Longrightarrow>  f x \<noteq> \<zero>\<^bsub>Q\<^sub>p\<^esub>"
  shows "f \<in> (Units (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
        "inv\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f = (\<lambda> x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). inv\<^bsub>Q\<^sub>p\<^esub> (f x))"
proof-
  obtain g where g_def: "g = (\<lambda> x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). inv\<^bsub>Q\<^sub>p\<^esub> (f x))"
    by blast
  have g_closed: "g \<in> (carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
    by(rule Qp_funs_car_memI, unfold  g_def, auto,
            intro field_inv(3) assms Qp.function_ring_car_memE[of _ n], auto )
  have "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<Longrightarrow> f x \<otimes> g x = \<one>"
    using assms g_def
    by (metis (no_types, lifting) Qp.function_ring_car_memE field_inv(2) restrict_apply)
  then have 0: "f \<otimes>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> g = \<one>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub>"
    using assms g_def Qp_funs_mult''[of f n g] Qp_funs_one[of n] g_closed
    by (metis (no_types, lifting) restrict_ext)
  then show "f \<in> (Units (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
    using comm_monoid.UnitsI[of "Fun\<^bsub>n\<^esub> Q\<^sub>p"] assms(1) g_closed local.F.comm_monoid_axioms by presburger
  have "inv\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f = g"
    using g_def g_closed 0 cring.invI[of "Fun\<^bsub>n\<^esub> Q\<^sub>p"] Qp_funs_is_cring assms(1)
    by presburger
  show "inv\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f = (\<lambda> x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). inv\<^bsub>Q\<^sub>p\<^esub> (f x))"
    using assms g_def 0  \<open>inv\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f = g\<close>
    by blast
qed

lemma Qp_funs_Units_memE:
  assumes "f \<in> (Units (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
  shows "f \<otimes>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> inv\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f = \<one>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub>"
        "inv\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f \<otimes>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f = \<one>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub>"
        "\<And> x. x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<Longrightarrow>  f x \<noteq> \<zero>\<^bsub>Q\<^sub>p\<^esub>"
  using monoid.Units_r_inv[of "Fun\<^bsub>n\<^esub> Q\<^sub>p" f ] assms  Qp_funs_is_monoid
    apply blast
  using monoid.Units_l_inv[of "Fun\<^bsub>n\<^esub> Q\<^sub>p" f ] assms  Qp_funs_is_monoid
    apply blast
proof-
  obtain g where g_def: "g = inv\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f"
    by blast
  show "\<And> x. x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<Longrightarrow>  f x \<noteq> \<zero>\<^bsub>Q\<^sub>p\<^esub>"
  proof- fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
    have "f \<otimes>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> g = \<one>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub>"
      using assms g_def Qp_funs_is_monoid
        \<open>\<lbrakk>Group.monoid (Fun\<^bsub>n\<^esub> Q\<^sub>p); f \<in> Units (Fun\<^bsub>n\<^esub> Q\<^sub>p)\<rbrakk> \<Longrightarrow> f \<otimes>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> inv\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f = \<one>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub>\<close>
      by blast
    then have 0: "f x \<otimes> g x = \<one>"
      using A assms g_def Qp_funs_mult'[of x n f g] Qp_funs_one[of n]
      by (metis Qp_funs_is_monoid monoid.Units_closed monoid.Units_inv_closed restrict_apply)
    have 1: "g x \<in> carrier Q\<^sub>p"
      using g_def A assms local.function_ring_car_closed by auto
    then show "f x \<noteq> \<zero>\<^bsub>Q\<^sub>p\<^esub>"
      using 0
      by (metis Qp.l_null local.one_neq_zero)
  qed
qed

lemma Qp_funs_m_inv:
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f \<in> (Units (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
  shows "(inv\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f) x = inv\<^bsub>Q\<^sub>p\<^esub> (f x)"
  using Qp_funs_Units_memI(2)  Qp_funs_Units_memE(3) assms
  by (metis (no_types, lifting) Qp_funs_is_monoid monoid.Units_closed restrict_apply)


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Defining the Rings of Semialgebraic Functions\<close>
(**************************************************************************************************)
(**************************************************************************************************)


definition semialg_functions  where
"semialg_functions n  = {f \<in> (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) \<rightarrow> carrier Q\<^sub>p. is_semialg_function n f \<and> f = restrict f (carrier (Q\<^sub>p\<^bsup>n\<^esup>))}"

lemma semialg_functions_memE:
  assumes "f \<in> semialg_functions n"
  shows "is_semialg_function n f"
        "f \<in> carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
        "f \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  using semialg_functions_def assms apply blast
  apply(rule Qp_funs_car_memI')
  using assms
  apply (metis (no_types, lifting) mem_Collect_eq semialg_functions_def)
  using assms unfolding semialg_functions_def
   apply (metis (mono_tags, lifting) mem_Collect_eq)
  by (metis (no_types, lifting) assms mem_Collect_eq semialg_functions_def)

lemma semialg_functions_in_Qp_funs:
"semialg_functions n \<subseteq> carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
  using semialg_functions_memE
  by blast

lemma semialg_functions_memI:
  assumes "f \<in> carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
  assumes "is_semialg_function n f"
  shows "f \<in> semialg_functions n"
  using assms unfolding semialg_functions_def
  by (metis (mono_tags, lifting) Qp_funs_car_memI function_ring_car_eqI
      is_semialg_function_closed mem_Collect_eq restrict_Pi_cancel restrict_apply)

lemma restrict_is_semialg:
  assumes "is_semialg_function n f"
  shows "is_semialg_function n (restrict f (carrier (Q\<^sub>p\<^bsup>n\<^esup>)))"
proof(rule is_semialg_functionI)
  show 0: "restrict f (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
    using assms is_semialg_function_closed by blast
  show "\<And>k S. S \<in> semialg_sets (1 + k) \<Longrightarrow> is_semialgebraic (n + k) (partial_pullback n (restrict f (carrier (Q\<^sub>p\<^bsup>n\<^esup>))) k S)"
  proof- fix k S assume A: "S \<in> semialg_sets (1 + k)"
    have "(partial_pullback n (restrict f (carrier (Q\<^sub>p\<^bsup>n\<^esup>))) k S) = partial_pullback n f k S"
      apply(intro equalityI'  partial_pullback_memI, meson partial_pullback_memE)
      unfolding partial_pullback_def partial_image_def evimage_eq restrict_def
        apply (metis (mono_tags, lifting) le_add1 local.take_closed)
       apply blast
      by (metis (mono_tags, lifting) le_add1 local.take_closed)
    then show " is_semialgebraic (n + k) (partial_pullback n (restrict f (carrier (Q\<^sub>p\<^bsup>n\<^esup>))) k S)"
      using assms A is_semialg_functionE is_semialgebraicI
      by presburger
  qed
qed

lemma restrict_in_semialg_functions:
  assumes "is_semialg_function n f"
  shows "(restrict f (carrier (Q\<^sub>p\<^bsup>n\<^esup>))) \<in> semialg_functions n"
  using assms restrict_is_semialg
  unfolding semialg_functions_def
  by (metis (mono_tags, lifting) is_semialg_function_closed mem_Collect_eq restrict_apply' restrict_ext)

lemma constant_function_is_semialg:
  assumes "a \<in> carrier Q\<^sub>p"
  shows "is_semialg_function n (constant_function (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) a)"
proof-
  have "(constant_function (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) a) = restrict (Qp_ev (Qp.indexed_const a)) (carrier (Q\<^sub>p\<^bsup>n\<^esup>))"
    apply(rule ext)
    unfolding constant_function_def
    using eval_at_point_const assms by simp
  then show ?thesis using restrict_in_semialg_functions poly_is_semialg[of  "Qp.indexed_const a"]
    using assms(1)  Qp_to_IP_car restrict_is_semialg by presburger
qed

lemma constant_function_in_semialg_functions:
  assumes "a \<in> carrier Q\<^sub>p"
  shows "Qp_const n a \<in> semialg_functions n"
  apply(unfold semialg_functions_def constant_function_def mem_Collect_eq, intro conjI, auto simp: assms)
  using assms constant_function_is_semialg[of a n] unfolding constant_function_def by auto

lemma function_one_as_constant:
"\<one>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> = Qp_const n \<one>"
  unfolding constant_function_def  function_ring_def[of "carrier (Q\<^sub>p\<^bsup>n\<^esup>)" Q\<^sub>p] function_one_def
  by simp

lemma function_zero_as_constant:
"\<zero>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> = Qp_const n \<zero>\<^bsub>Q\<^sub>p\<^esub>"
  unfolding constant_function_def function_ring_def[of "carrier (Q\<^sub>p\<^bsup>n\<^esup>)" Q\<^sub>p] function_zero_def
  by simp

lemma sum_in_semialg_functions:
  assumes "f \<in> semialg_functions n"
  assumes "g \<in> semialg_functions n"
  shows "f \<oplus>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> g \<in> semialg_functions n"
proof-
  have 0:"f \<oplus>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> g = restrict (function_tuple_comp Q\<^sub>p [f,g] Qp_add_fun) (carrier (Q\<^sub>p\<^bsup>n\<^esup>))"
  proof fix x
    show "(f \<oplus>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> g) x = restrict (function_tuple_comp Q\<^sub>p [f, g] Qp_add_fun) (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) x"
    proof(cases "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)")
      case True
      have " restrict (function_tuple_comp Q\<^sub>p [f, g] Qp_add_fun) (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) x = Qp_add_fun [f x, g x]"
        unfolding function_tuple_comp_def function_tuple_eval_def restrict_def
        using comp_apply[of "Qp_add_fun" "(\<lambda>x. map (\<lambda>f. f x) [f, g])" x]
        by (metis (no_types, lifting) True list.simps(8) list.simps(9))
      then have "restrict (function_tuple_comp Q\<^sub>p [f, g] Qp_add_fun) (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) x = f x \<oplus>\<^bsub>Q\<^sub>p\<^esub> g x"
        unfolding Qp_add_fun_def
        by (metis One_nat_def nth_Cons_0 nth_Cons_Suc)
      then show ?thesis  using True function_ring_def[of "carrier (Q\<^sub>p\<^bsup>n\<^esup>)" Q\<^sub>p]
        unfolding function_add_def
        by (metis (no_types, lifting) Qp_funs_add assms(1) assms(2) mem_Collect_eq semialg_functions_def)
    next
      case False
      have "(f \<oplus>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> g) x = undefined"
        using function_ring_def[of "carrier (Q\<^sub>p\<^bsup>n\<^esup>)" Q\<^sub>p] unfolding function_add_def
        by (metis (mono_tags, lifting) False restrict_apply ring_record_simps(12))
      then show ?thesis
        by (metis False restrict_def)
    qed
  qed
  have 1: "is_semialg_function_tuple n [f, g]"
    using assms is_semialg_function_tupleI[of "[f, g]" n] semialg_functions_memE
    by (metis list.distinct(1) list.set_cases set_ConsD)
  have 2: "is_semialg_function n (function_tuple_comp Q\<^sub>p [f,g] Qp_add_fun)"
    apply(rule semialg_function_tuple_comp[of _ _  2])
        apply (simp add: "1")
       apply simp
    by (simp add: addition_is_semialg)
  show ?thesis
    apply(rule semialg_functions_memI)
  apply (meson Qp_funs_is_cring assms(1) assms(2) cring.cring_simprules(1) semialg_functions_memE(2))
    using 0 2 restrict_is_semialg by presburger
qed

lemma prod_in_semialg_functions:
  assumes "f \<in> semialg_functions n"
  assumes "g \<in> semialg_functions n"
  shows "f \<otimes>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> g \<in> semialg_functions n"
proof-
  have 0:"f \<otimes>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> g = restrict (function_tuple_comp Q\<^sub>p [f,g] Qp_mult_fun) (carrier (Q\<^sub>p\<^bsup>n\<^esup>))"
  proof fix x
    show "(f \<otimes>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> g) x = restrict (function_tuple_comp Q\<^sub>p [f, g] Qp_mult_fun) (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) x"
    proof(cases "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)")
      case True
      have " restrict (function_tuple_comp Q\<^sub>p [f, g] Qp_mult_fun) (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) x = Qp_mult_fun [f x, g x]"
        unfolding function_tuple_comp_def function_tuple_eval_def restrict_def
        using comp_apply[of "Qp_mult_fun" "(\<lambda>x. map (\<lambda>f. f x) [f, g])" x]
        by (metis (no_types, lifting) True list.simps(8) list.simps(9))
      then have "restrict (function_tuple_comp Q\<^sub>p [f, g] Qp_mult_fun) (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) x = f x \<otimes> g x"
        unfolding Qp_mult_fun_def
        by (metis One_nat_def nth_Cons_0 nth_Cons_Suc)
      then show ?thesis  using True function_ring_def[of "carrier (Q\<^sub>p\<^bsup>n\<^esup>)" Q\<^sub>p]
        unfolding function_mult_def
        by (metis (no_types, lifting) Qp_funs_mult  assms(1) assms(2) mem_Collect_eq semialg_functions_def)
    next
      case False
      have "(f \<otimes>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> g) x = undefined"
        using function_ring_def[of "carrier (Q\<^sub>p\<^bsup>n\<^esup>)" Q\<^sub>p] unfolding function_mult_def
        by (metis (mono_tags, lifting) False restrict_apply ring_record_simps(5))
      then show ?thesis
        by (metis False restrict_def)
    qed
  qed
  have 1: "is_semialg_function_tuple n [f, g]"
    using assms is_semialg_function_tupleI[of "[f, g]" n] semialg_functions_memE
    by (metis list.distinct(1) list.set_cases set_ConsD)
  have 2: "is_semialg_function n (function_tuple_comp Q\<^sub>p [f,g] Qp_mult_fun)"
    apply(rule semialg_function_tuple_comp[of _ _  2])
        apply (simp add: "1")
       apply simp
    by (simp add: multiplication_is_semialg)
  show ?thesis
    apply(rule semialg_functions_memI)
    apply (meson Qp_funs_is_cring assms(1) assms(2) cring.cring_simprules(5) semialg_functions_memE(2))
    using 0 2 restrict_is_semialg by presburger
qed

lemma inv_in_semialg_functions:
  assumes "f \<in> semialg_functions n"
  assumes "\<And> x. x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<Longrightarrow> f x \<noteq> \<zero>\<^bsub>Q\<^sub>p\<^esub>"
  shows "inv\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f \<in> semialg_functions n "
proof-
  have 0: "inv\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f = restrict (function_tuple_comp Q\<^sub>p [f] Qp_invert) (carrier (Q\<^sub>p\<^bsup>n\<^esup>))"
  proof fix x
    show "(inv\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f) x = restrict (function_tuple_comp Q\<^sub>p [f] Qp_invert) (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) x"
    proof(cases "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)")
      case True
      have "(function_tuple_comp Q\<^sub>p [f] Qp_invert) x = Qp_invert [f x]"
        unfolding function_tuple_comp_def function_tuple_eval_def
        using comp_apply  by (metis (no_types, lifting) list.simps(8) list.simps(9))
      then have "(function_tuple_comp Q\<^sub>p [f] Qp_invert) x = inv\<^bsub>Q\<^sub>p\<^esub> (f x)"
        unfolding Qp_invert_def
        using True assms(2) Qp.to_R_to_R1 by presburger
      then show ?thesis
        using True restrict_apply
        by (metis (mono_tags, opaque_lifting) Qp_funs_Units_memI(1)
            Qp_funs_m_inv assms(1) assms(2) semialg_functions_memE(2))
    next
      case False
      have "inv\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f \<in> carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
        using assms
        by (meson Qp_funs_Units_memI(1) Qp_funs_is_monoid monoid.Units_inv_closed semialg_functions_memE(2))
      then show ?thesis using False restrict_apply function_ring_not_car
        by auto
    qed
  qed
  have "is_semialg_function n (function_tuple_comp Q\<^sub>p [f] Qp_invert)"
    apply(rule semialg_function_tuple_comp[of _ _  1])
        apply (simp add: assms(1) is_semialg_function_tuple_def semialg_functions_memE(1))
        apply simp
        using Qp_invert_is_semialg by blast
  then show ?thesis
    using "0" restrict_in_semialg_functions
    by presburger
qed

lemma a_inv_in_semialg_functions:
  assumes "f \<in> semialg_functions n"
  shows "\<ominus>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f \<in> semialg_functions n"
proof-
  have "\<ominus>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f = (Qp_const n (\<ominus> \<one>)) \<otimes>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f"
  proof fix x
    show "(\<ominus>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f) x = (Qp_const n (\<ominus> \<one>) \<otimes>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f) x"
    proof(cases "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)")
      case True
      have 0: "(\<ominus>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f) x = \<ominus> (f x)"
        using Qp_funs_a_inv semialg_functions_memE True assms(1) by blast
      have 1: "(Qp_const n (\<ominus> \<one>) \<otimes>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f) x = (\<ominus> \<one>)\<otimes>(f x)"
        using Qp_funs_mult[of x n "Qp_const n (\<ominus> \<one>)" f] assms Qp_constE[of "\<ominus> \<one>" x n]
          Qp_funs_mult'  Qp.add.inv_closed Qp.one_closed Qp_funs_mult''' True by presburger
      have 2: "f x \<in> carrier Q\<^sub>p"
        using True semialg_functions_memE[of f n]  assms by blast
      show ?thesis
        using True assms 0 1 2 Qp.l_minus Qp.l_one Qp.one_closed by presburger
    next
      case False
      have "(\<ominus>\<^bsub>function_ring (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) Q\<^sub>p\<^esub> f) x = undefined"
        using  Qp_funs_a_inv'[of f n] False assms semialg_functions_memE
        by (metis (no_types, lifting) restrict_apply)
      then show ?thesis
        using False function_ring_defs(2)[of n] Qp_funs_a_inv'[of f n]
        unfolding function_mult_def restrict_def
        by presburger
    qed
  qed
  then show ?thesis
    using prod_in_semialg_functions[of "Qp_const n (\<ominus> \<one>)" n f] assms
      constant_function_in_semialg_functions[of "\<ominus> \<one>" n]  Qp.add.inv_closed Qp.one_closed
    by presburger
qed

lemma semialg_functions_subring:
  shows "subring (semialg_functions n) (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
  apply(rule ring.subringI)
  using Qp_funs_is_cring cring.axioms(1) apply blast
  apply (simp add: semialg_functions_in_Qp_funs)
  using Qp.one_closed  constant_function_in_semialg_functions function_one_as_constant apply presburger
  using a_inv_in_semialg_functions  apply blast
  using  prod_in_semialg_functions apply blast
  using  sum_in_semialg_functions by blast

lemma semialg_functions_subcring:
  shows "subcring (semialg_functions n) (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
  using semialg_functions_subring cring.subcringI'
  using Qp_funs_is_cring by blast

definition SA where
"SA n = (Fun\<^bsub>n\<^esub> Q\<^sub>p)\<lparr> carrier := semialg_functions n\<rparr>"

lemma SA_is_ring:
  shows "ring (SA n)"
proof-
  have "ring (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
    by (simp add: Qp_funs_is_cring cring.axioms(1))
  then show ?thesis
    unfolding SA_def
  using  ring.subring_is_ring[of "Fun\<^bsub>n\<^esub> Q\<^sub>p" "semialg_functions n"] semialg_functions_subring[of n]
  by blast
qed

lemma SA_is_cring:
  shows "cring (SA n)"
  using ring.subcring_iff[of "Fun\<^bsub>n\<^esub> Q\<^sub>p" "semialg_functions n"] semialg_functions_subcring[of n]
         Qp_funs_is_cring cring.axioms(1) semialg_functions_in_Qp_funs
    unfolding SA_def
  by blast

lemma SA_is_monoid:
  shows "monoid (SA n)"
  using SA_is_ring[of n]  unfolding ring_def
  by linarith

lemma SA_is_abelian_monoid:
  shows "abelian_monoid (SA n)"
  using SA_is_ring[of n]  unfolding ring_def abelian_group_def by blast

lemma SA_car:
"carrier (SA n) = semialg_functions n"
    unfolding SA_def
  by simp

lemma SA_car_in_Qp_funs_car:
"carrier (SA n) \<subseteq> carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
  by (simp add: SA_car semialg_functions_in_Qp_funs)

lemma SA_car_memI:
  assumes "f \<in> carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
  assumes "is_semialg_function n f"
  shows "f \<in> carrier (SA n)"
  using assms semialg_functions_memI[of f n] SA_car
  by blast

lemma SA_car_memE:
  assumes "f \<in> carrier (SA n)"
  shows "is_semialg_function n f"
        "f \<in> carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
        "f \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  using SA_car assms semialg_functions_memE(1) apply blast
  using SA_car assms semialg_functions_memE(2) apply blast
  using SA_car assms semialg_functions_memE(3) by blast

lemma SA_plus:
"(\<oplus>\<^bsub>SA n\<^esub>) = (\<oplus>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub>)"
  unfolding SA_def
  by simp

lemma SA_times:
"(\<otimes>\<^bsub>SA n\<^esub>) = (\<otimes>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub>)"
  unfolding SA_def
  by simp

lemma SA_one:
"(\<one>\<^bsub>SA n\<^esub>) = (\<one>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub>)"
  unfolding SA_def
  by simp

lemma SA_zero:
"(\<zero>\<^bsub>SA n\<^esub>) = (\<zero>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub>)"
  unfolding SA_def
  by simp

lemma SA_zero_is_function_ring:
"(Fun\<^bsub>0\<^esub> Q\<^sub>p) = SA 0"
proof-
  have 0: "carrier (Fun\<^bsub>0\<^esub> Q\<^sub>p) = carrier (SA 0)"
  proof
    show "carrier (function_ring (carrier (Q\<^sub>p\<^bsup>0\<^esup>)) Q\<^sub>p) \<subseteq> carrier (SA 0)"
    proof fix f assume A0: "f \<in> carrier (function_ring (carrier (Q\<^sub>p\<^bsup>0\<^esup>)) Q\<^sub>p)"
      show "f \<in> carrier (SA 0)"
      proof(rule SA_car_memI)
        show "f \<in> carrier (function_ring (carrier (Q\<^sub>p\<^bsup>0\<^esup>)) Q\<^sub>p)"
          using A0 by blast
        show "is_semialg_function 0 f"
        proof(rule is_semialg_functionI)
          show "f \<in> carrier (Q\<^sub>p\<^bsup>0\<^esup>) \<rightarrow> carrier Q\<^sub>p"
            using A0 Qp.function_ring_car_memE by blast
          show "\<And>k S. S \<in> semialg_sets (1 + k) \<Longrightarrow> is_semialgebraic (0 + k) (partial_pullback 0 f k S)"
          proof- fix k S assume A: "S \<in> semialg_sets (1+k)"
            obtain a where a_def: "a = f []"
              by blast
            have 0: "carrier (Q\<^sub>p\<^bsup>0\<^esup>) = {[]}"
              using Qp_zero_carrier by blast
            have 1: "(partial_pullback 0 f k S) = {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). a#x \<in> S}"
            proof
              show "partial_pullback 0 f k S \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). a # x \<in> S}"
                apply(rule subsetI)
              unfolding partial_pullback_def partial_image_def using a_def
              by (metis (no_types, lifting) add.left_neutral drop0 evimage_eq mem_Collect_eq take_eq_Nil)
              show "{x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). a # x \<in> S} \<subseteq> partial_pullback 0 f k S"
                apply(rule subsetI)
                unfolding partial_pullback_def partial_image_def  a_def
                by (metis (no_types, lifting) add.left_neutral drop0 evimageI2 mem_Collect_eq take0)
            qed
            have 2: "cartesian_product {[a]} (partial_pullback 0 f k S) = (cartesian_product {[a]} (carrier (Q\<^sub>p\<^bsup>k\<^esup>))) \<inter> S"
            proof
              show "cartesian_product {[a]} (partial_pullback 0 f k S) \<subseteq> cartesian_product {[a]} (carrier (Q\<^sub>p\<^bsup>k\<^esup>)) \<inter> S"
              proof(rule subsetI) fix x assume A: "x \<in> cartesian_product {[a]} (partial_pullback 0 f k S)"
                then obtain y where y_def: "y \<in> (partial_pullback 0 f k S) \<and>x = a#y"
                  using cartesian_product_memE'
                  by (metis (no_types, lifting) Cons_eq_appendI self_append_conv2 singletonD)
                hence 20: "x \<in> S"
                  unfolding 1 by blast
                have 21: "x = [a]@y"
                  using y_def by (simp add: y_def)
                have "x \<in> cartesian_product {[a]} (carrier (Q\<^sub>p\<^bsup>k\<^esup>))"
                  unfolding 21 apply(rule cartesian_product_memI'[of _ Q\<^sub>p 1 _ k])
                  using a_def  apply (metis function_ring_car_closed Qp_zero_carrier \<open>f \<in> carrier (function_ring (carrier (Q\<^sub>p\<^bsup>0\<^esup>)) Q\<^sub>p)\<close> empty_subsetI insert_subset singletonI Qp.to_R1_closed)
                    apply blast
                   apply blast
                  using y_def unfolding partial_pullback_def  evimage_def
                  by (metis IntD2 add_cancel_right_left)
                thus "x \<in> cartesian_product {[a]} (carrier (Q\<^sub>p\<^bsup>k\<^esup>)) \<inter> S"
                  using 20 by blast
              qed
              show " cartesian_product {[a]} (carrier (Q\<^sub>p\<^bsup>k\<^esup>)) \<inter> S \<subseteq> cartesian_product {[a]} (partial_pullback 0 f k S)"
              proof fix x assume A: "x \<in> cartesian_product {[a]} (carrier (Q\<^sub>p\<^bsup>k\<^esup>)) \<inter> S"
                then obtain y where y_def: "x = a#y \<and> y \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
                  using cartesian_product_memE'
                  by (metis (no_types, lifting) Cons_eq_appendI IntD1 append_Nil singletonD)
                have 00: "y \<in> partial_pullback 0 f k S"
                  using y_def unfolding 1  using A by blast
                have 01: "x = [a]@y"
                  using y_def by (simp add: y_def)
                have 02: "partial_pullback 0 f k S \<subseteq> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
                  unfolding partial_pullback_def
                  by (simp add: extensional_vimage_closed)
                show "x \<in> cartesian_product {[a]} (partial_pullback 0 f k S)"
                  unfolding 01 apply(rule cartesian_product_memI'[of "{[a]}" Q\<^sub>p 1 "partial_pullback 0 f k S" k "[a]" y ])
                  apply (metis function_ring_car_closed Qp_zero_carrier \<open>f \<in> carrier (function_ring (carrier (Q\<^sub>p\<^bsup>0\<^esup>)) Q\<^sub>p)\<close> a_def empty_subsetI insert_subset singletonI Qp.to_R1_closed)
                  using "02" apply blast
                   apply blast
                  using 00 by blast
              qed
            qed
            have 3:"is_semialgebraic 1 {[a]}"
            proof-
              have "a \<in> carrier Q\<^sub>p"
                using a_def Qp.function_ring_car_memE 0  \<open>f \<in> carrier (function_ring (carrier (Q\<^sub>p\<^bsup>0\<^esup>)) Q\<^sub>p)\<close> by blast
              hence "[a] \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
                using Qp.to_R1_closed by blast
              thus ?thesis
                using is_algebraic_imp_is_semialg singleton_is_algebraic by blast
            qed
            have  4: "is_semialgebraic (1+k)  (cartesian_product {[a]} (carrier (Q\<^sub>p\<^bsup>k\<^esup>)))"
              using 3 carrier_is_semialgebraic cartesian_product_is_semialgebraic less_one by blast
            have  5: "is_semialgebraic (1+k) (cartesian_product {[a]} (partial_pullback 0 f k S))"
              unfolding 2 using 3 4 A intersection_is_semialg padic_fields.is_semialgebraicI padic_fields_axioms by blast
            have 6: "{[a]} \<subseteq> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
              using a_def A0 0 by (metis Qp.function_ring_car_memE empty_subsetI insert_subset singletonI Qp.to_R1_closed)
            have  7: "is_semialgebraic (k+1) (cartesian_product (partial_pullback 0 f k S) {[a]})"
              apply(rule cartesian_product_swap)
                using "6" apply blast
               apply (metis add_cancel_right_left partial_pullback_closed)
              using "5" by auto
            have 8: "is_semialgebraic k (partial_pullback 0 f k S)"
              apply(rule cartesian_product_singleton_factor_projection_is_semialg'[of _ _ "[a]" 1])
                  apply (metis add_cancel_right_left partial_pullback_closed)
                 apply (metis A0 Qp.function_ring_car_memE Qp_zero_carrier a_def singletonI Qp.to_R1_closed)
                using "7" by blast
            thus "is_semialgebraic (0 + k) (partial_pullback 0 f k S)"
                by simp
          qed
        qed
      qed
    qed
    show "carrier (SA 0) \<subseteq> carrier (function_ring (carrier (Q\<^sub>p\<^bsup>0\<^esup>)) Q\<^sub>p)"
      using SA_car_in_Qp_funs_car by blast
  qed
  then have 1: "semialg_functions 0 = carrier (Fun\<^bsub>0\<^esub> Q\<^sub>p)"
    unfolding 0 SA_def by auto
  show ?thesis unfolding SA_def 1 by auto
qed

lemma constant_fun_closed:
  assumes "c \<in> carrier Q\<^sub>p"
  shows "constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) c \<in> carrier (SA m)"
  using constant_function_in_semialg_functions SA_car assms by blast

lemma SA_0_car_memI:
  assumes "\<xi> \<in> carrier (Q\<^sub>p\<^bsup>0\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  assumes "\<And>x. x \<notin> carrier (Q\<^sub>p\<^bsup>0\<^esup>) \<Longrightarrow> \<xi> x = undefined"
  shows "\<xi> \<in> carrier (SA 0)"
proof-
  have 0: "carrier (Q\<^sub>p\<^bsup>0\<^esup>) = {[]}"
    by (simp add: Qp_zero_carrier)
  obtain c where c_def: "\<xi> [] = c"
    by blast
  have 1: "\<xi> = constant_function (carrier (Q\<^sub>p\<^bsup>0\<^esup>)) c"
    unfolding constant_function_def restrict_def
    using assms c_def  unfolding 0
    by (metis empty_iff insert_iff)
  have 2: "c \<in> carrier Q\<^sub>p"
    using assms(1) c_def unfolding 0 by blast
  show ?thesis unfolding 1
    using 2 constant_fun_closed by blast
qed

lemma car_SA_0_mem_imp_const:
  assumes "a \<in> carrier (SA 0)"
  shows "\<exists> c \<in> carrier Q\<^sub>p. a = Qp_const 0 c"
proof-
  obtain c where c_def: "c =  a []"
    by blast
  have car_zero: "carrier (Q\<^sub>p\<^bsup>0\<^esup>) = {[]}"
    using Qp_zero_carrier by blast
  have 0: "a = constant_function (carrier (Q\<^sub>p\<^bsup>0\<^esup>)) c"
  proof fix x
    show " a x = constant_function (carrier (Q\<^sub>p\<^bsup>0\<^esup>)) c x"
      apply(cases "x \<in> carrier (Q\<^sub>p\<^bsup>0\<^esup>)")
      using assms SA_car_memE[of a 0] c_def
      unfolding constant_function_def restrict_def  car_zero
       apply (metis empty_iff insert_iff)
      using assms SA_car_memE(2)[of a 0] c_def
      unfolding constant_function_def restrict_def car_zero
      by (metis car_zero function_ring_not_car)
  qed
  have c_closed: "c \<in> carrier Q\<^sub>p"
    using assms  SA_car_memE(3)[of  a 0] unfolding c_def car_zero
    by blast
  thus ?thesis using 0 by blast
qed

lemma SA_zeroE:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "\<zero> \<^bsub>SA n\<^esub> a = \<zero>"
  using function_zero_eval SA_zero assms by presburger

lemma SA_oneE:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "\<one> \<^bsub>SA n\<^esub> a = \<one>"
  using function_one_eval  SA_one assms by presburger
end

sublocale padic_fields < UPSA?: UP_cring "SA m" "UP (SA m)"
  unfolding UP_cring_def using SA_is_cring[of m] by auto

context padic_fields
begin

lemma SA_add:
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "(f \<oplus>\<^bsub>SA n\<^esub> g) x = f x \<oplus>\<^bsub>Q\<^sub>p\<^esub> g x"
  using Qp_funs_add''' SA_plus assms by presburger

lemma SA_add':
  assumes "x \<notin> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "(f \<oplus>\<^bsub>SA n\<^esub> g) x = undefined"
proof-
  have "(f \<oplus>\<^bsub>SA n\<^esub> g) x = function_add (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) Q\<^sub>p f g x"
    using SA_plus[of n] unfolding function_ring_def
    by (metis ring_record_simps(12))
  then show ?thesis
    unfolding function_add_def using restrict_apply assms
    by (metis (no_types, lifting))
qed

lemma SA_mult:
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "(f \<otimes>\<^bsub>SA n\<^esub> g) x = f x \<otimes> g x"
  using Qp_funs_mult''' SA_times assms by presburger

lemma SA_mult':
  assumes "x \<notin> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "(f \<otimes>\<^bsub>SA n\<^esub> g) x = undefined"
proof-
  have "(f \<otimes>\<^bsub>SA n\<^esub> g) x = function_mult (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) Q\<^sub>p f g x"
    using SA_times[of n] unfolding function_ring_def
    by (metis ring_record_simps(5))
  then show ?thesis
    unfolding function_mult_def using restrict_apply assms
    by (metis (no_types, lifting))
qed

lemma SA_u_minus_eval:
  assumes "f \<in> carrier (SA n)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "(\<ominus>\<^bsub>SA n\<^esub> f) x = \<ominus> (f x)"
proof-
  have  "f \<oplus>\<^bsub>SA n\<^esub> (\<ominus>\<^bsub>SA n\<^esub> f) = \<zero> \<^bsub>SA n\<^esub>"
    using assms SA_is_cring cring.cring_simprules(17) by metis
  have  "(f \<oplus>\<^bsub>SA n\<^esub> (\<ominus>\<^bsub>SA n\<^esub> f)) x = \<zero> \<^bsub>SA n\<^esub> x"
    using assms \<open>f \<oplus>\<^bsub>SA n\<^esub> \<ominus>\<^bsub>SA n\<^esub> f = \<zero>\<^bsub>SA n\<^esub>\<close> by presburger
  then have "(f x) \<oplus> (\<ominus>\<^bsub>SA n\<^esub> f) x = \<zero>"
    using assms function_zero_eval SA_add unfolding   SA_zero by blast
  then show ?thesis
    using assms SA_is_ring
    by (meson Qp.add.inv_closed Qp.add.inv_comm Qp.function_ring_car_memE Qp.minus_unique Qp.r_neg SA_car_memE(2) ring.ring_simprules(3))
qed

lemma SA_a_inv_eval:
  assumes "f \<in> carrier (SA n)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "(\<ominus>\<^bsub>SA n\<^esub> f) x = \<ominus> (f x)"
proof-
  have  "f \<oplus>\<^bsub>SA n\<^esub> (\<ominus>\<^bsub>SA n\<^esub> f) = \<zero> \<^bsub>SA n\<^esub>"
    using assms SA_is_cring cring.cring_simprules(17) by metis
  have  "(f \<oplus>\<^bsub>SA n\<^esub> (\<ominus>\<^bsub>SA n\<^esub> f)) x = \<zero> \<^bsub>SA n\<^esub> x"
    using assms \<open>f \<oplus>\<^bsub>SA n\<^esub> \<ominus>\<^bsub>SA n\<^esub> f = \<zero>\<^bsub>SA n\<^esub>\<close> by presburger
  then have "(f x) \<oplus> (\<ominus>\<^bsub>SA n\<^esub> f) x = \<zero>"
    by (metis function_zero_eval SA_add SA_zero assms)
  then show ?thesis
    by (metis (no_types, lifting) PiE Q\<^sub>p_def Qp.add.m_comm Qp.minus_equality SA_is_cring Zp_def assms(1) assms(2) cring.cring_simprules(3) padic_fields.SA_car_memE(3) padic_fields_axioms)
qed

lemma SA_nat_pow:
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "(f [^]\<^bsub>SA n\<^esub> (k::nat)) x = (f x) [^]\<^bsub>Q\<^sub>p\<^esub> k"
  apply(induction k)
  using assms  nat_pow_def
  apply (metis function_one_eval SA_one old.nat.simps(6))
  using assms SA_mult
  by (metis Group.nat_pow_Suc)

lemma SA_nat_pow':
  assumes "x \<notin> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "(f [^]\<^bsub>SA n\<^esub> (k::nat)) x = undefined"
  apply(induction k)
  using assms nat_pow_def[of "SA n" f]
  apply (metis (no_types, lifting) Group.nat_pow_0 Qp_funs_one SA_one restrict_apply)
  by (metis Group.nat_pow_Suc SA_mult' assms)

lemma SA_add_closed_id:
  assumes "is_semialg_function n f"
  assumes "is_semialg_function n g"
  shows "restrict f (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) \<oplus>\<^bsub>SA n\<^esub> restrict g (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) = f \<oplus>\<^bsub>SA n\<^esub> g "
proof fix x
  show "(restrict f (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) \<oplus>\<^bsub>SA n\<^esub> restrict g (carrier (Q\<^sub>p\<^bsup>n\<^esup>))) x = (f \<oplus>\<^bsub>SA n\<^esub> g) x"
    apply(cases "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)")
    using assms restrict_apply
    apply (metis SA_add)
    using assms
    by (metis SA_add')
qed

lemma SA_mult_closed_id:
  assumes "is_semialg_function n f"
  assumes "is_semialg_function n g"
  shows "restrict f (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) \<otimes>\<^bsub>SA n\<^esub> restrict g (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) = f \<otimes>\<^bsub>SA n\<^esub> g "
proof fix x
  show "(restrict f (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) \<otimes>\<^bsub>SA n\<^esub> restrict g (carrier (Q\<^sub>p\<^bsup>n\<^esup>))) x = (f \<otimes>\<^bsub>SA n\<^esub> g) x"
    apply(cases "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)")
    using assms restrict_apply
    apply (metis SA_mult)
    using assms
    by (metis SA_mult')
qed

lemma SA_add_closed:
  assumes "is_semialg_function n f"
  assumes "is_semialg_function n g"
  shows "f \<oplus>\<^bsub>SA n\<^esub> g \<in> carrier (SA n)"
    using assms SA_add_closed_id
    by (metis SA_car SA_plus restrict_in_semialg_functions sum_in_semialg_functions)

lemma SA_mult_closed:
  assumes "is_semialg_function n f"
  assumes "is_semialg_function n g"
  shows "f \<otimes>\<^bsub>SA n\<^esub> g \<in> carrier (SA n)"
    using assms SA_mult_closed_id
  by (metis SA_car SA_is_cring cring.cring_simprules(5) restrict_in_semialg_functions)

lemma SA_add_closed_right:
  assumes "is_semialg_function n f"
  assumes "g \<in> carrier (SA n)"
  shows "f \<oplus>\<^bsub>SA n\<^esub> g \<in> carrier (SA n)"
  using SA_add_closed SA_car_memE(1) assms(1) assms(2)   by blast

lemma SA_mult_closed_right:
  assumes "is_semialg_function n f"
  assumes "g \<in> carrier (SA n)"
  shows "f \<otimes>\<^bsub>SA n\<^esub> g \<in> carrier (SA n)"
  using SA_car_memE(1) SA_mult_closed assms(1) assms(2)   by blast

lemma SA_add_closed_left:
  assumes "f \<in> carrier (SA n)"
  assumes "is_semialg_function n g"
  shows "f \<oplus>\<^bsub>SA n\<^esub> g \<in> carrier (SA n)"
  using SA_add_closed SA_car_memE(1) assms(1) assms(2)   by blast

lemma SA_mult_closed_left:
  assumes "f \<in> carrier (SA n)"
  assumes "is_semialg_function n g"
  shows "f \<otimes>\<^bsub>SA n\<^esub> g \<in> carrier (SA n)"
  using SA_car_memE(1) SA_mult_closed assms(1) assms(2)  by blast

lemma SA_nat_pow_closed:
  assumes "is_semialg_function n f"
  shows "f [^]\<^bsub>SA n\<^esub> (k::nat) \<in> carrier (SA n)"
  apply(induction k)
  using nat_pow_def[of "SA n" f ]
  apply (metis Group.nat_pow_0  monoid.one_closed SA_is_monoid)
  by (metis Group.nat_pow_Suc SA_car assms(1) assms SA_mult_closed semialg_functions_memE(1))

lemma SA_imp_semialg:
  assumes "f \<in> carrier (SA n)"
  shows "is_semialg_function n f"
  using SA_car assms semialg_functions_memE(1) by blast

lemma SA_minus_closed:
  assumes "f \<in> carrier (SA n)"
  assumes "g \<in> carrier (SA n)"
  shows "(f  \<ominus>\<^bsub>SA n\<^esub> g) \<in> carrier (SA n)"
  using assms unfolding a_minus_def
  by (meson SA_add_closed_left SA_imp_semialg SA_is_ring ring.ring_simprules(3))

lemma(in ring) add_pow_closed :
  assumes "b \<in> carrier R"
  shows "([(m::nat)]\<cdot>\<^bsub>R\<^esub>b) \<in> carrier R"
  by(rule add.nat_pow_closed, rule assms)

lemma(in ring) add_pow_Suc:
  assumes "b \<in> carrier R"
  shows "[(Suc m)]\<cdot>b = [m]\<cdot>b \<oplus> b"
  using assms add.nat_pow_Suc by blast

lemma(in ring) add_pow_zero:
  assumes "b \<in> carrier R"
  shows "[(0::nat)]\<cdot>b = \<zero>"
  using assms nat_mult_zero
  by blast

lemma Fun_add_pow_apply:
  assumes "b \<in> carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "([(m::nat)]\<cdot>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> b) a = [m]\<cdot>( b a)"
proof-
  have 0: "b a \<in> carrier Q\<^sub>p"
    using Qp.function_ring_car_mem_closed assms by fastforce
  have 1: "ring (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
    using function_ring_is_ring by blast
  show ?thesis
  proof(induction m)
    case 0
    have "([(0::nat)] \<cdot>\<^bsub>function_ring (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) Q\<^sub>p\<^esub> b) = \<zero>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub>"
      using 1 ring.add_pow_zero[of "Fun\<^bsub>n\<^esub> Q\<^sub>p" b ] assms  by blast
    then show ?case
      using  function_zero_eval Qp.nat_mult_zero assms  by presburger
  next
    case (Suc m)
    then show ?case using Suc ring.add_pow_Suc[of "SA n" b m] assms
      by (metis (no_types, lifting) "0" "1" Qp.ring_axioms SA_add SA_plus ring.add_pow_Suc)
  qed
qed

lemma SA_add_pow_apply:
  assumes "b \<in> carrier (SA n)"
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "([(m::nat)]\<cdot>\<^bsub>SA n\<^esub> b) a = [m]\<cdot>( b a)"
  apply(induction m)
  using assms SA_is_ring[of n] Fun_add_pow_apply
  apply (metis function_zero_eval Qp.nat_mult_zero SA_zero ring.add_pow_zero)
  using assms SA_is_ring[of n] ring.add_pow_Suc[of "Fun\<^bsub>n\<^esub> Q\<^sub>p" b]  ring.add_pow_Suc[of "SA n" b] SA_plus[of n]
  using Fun_add_pow_apply
  by (metis Qp.add.nat_pow_Suc SA_add)

lemma Qp_funs_Units_SA_Units:
  assumes "f \<in> Units (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
  assumes "is_semialg_function n f"
  shows "f \<in> Units (SA n)"
proof-
  have 0: "f \<in> carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
    by (meson Qp_funs_is_monoid assms(1) monoid.Units_closed)
  have 1: "inv\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f \<in> semialg_functions n"
    using monoid.Units_closed[of "Fun\<^bsub>n\<^esub> Q\<^sub>p" f]
      assms inv_in_semialg_functions[of f n] Qp_funs_Units_memE(3)[of f n]
      semialg_functions_memI[of f n] Qp_funs_is_monoid by blast
  then have 2: "f \<otimes>\<^bsub>SA n\<^esub> (inv\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f ) = \<one>\<^bsub>SA n\<^esub>"
    using Qp_funs_Units_memE(1)[of f n] SA_one SA_times assms(1)
    by presburger
  then have 3: "(inv\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f ) \<otimes>\<^bsub>SA n\<^esub> f  = \<one>\<^bsub>SA n\<^esub>"
    using Qp_funs_Units_memE(2)[of f n] SA_one SA_times assms(1)
    by presburger
  have 4: "f \<in> carrier (SA n)"
    using "0" SA_car assms(2) semialg_functions_memI by blast
  have 5: "inv\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f \<in> carrier (SA n)"
    using SA_car_memI "1" SA_car by blast
  show ?thesis
    using 5 4 3 2 unfolding Units_def
    by blast
qed

lemma SA_Units_memE:
  assumes "f \<in> (Units (SA n))"
  shows "f \<otimes>\<^bsub>SA n\<^esub> inv\<^bsub>SA n\<^esub> f = \<one>\<^bsub>SA n\<^esub>"
        "inv\<^bsub>SA n\<^esub> f \<otimes>\<^bsub>SA n\<^esub> f = \<one>\<^bsub>SA n\<^esub>"
  using assms SA_is_monoid[of n] monoid.Units_r_inv[of "SA n" f]
  apply blast
  using assms SA_is_monoid[of n] monoid.Units_l_inv[of "SA n" f]
  by blast

lemma SA_Units_closed:
  assumes "f \<in> (Units (SA n))"
  shows "f \<in> carrier (SA n)"
  using assms unfolding Units_def by blast

lemma SA_Units_inv_closed:
  assumes "f \<in> (Units (SA n))"
  shows "inv\<^bsub>SA n\<^esub> f \<in> carrier (SA n)"
  using assms SA_is_monoid[of n] monoid.Units_inv_closed[of "SA n" f]
  by blast

lemma SA_Units_Qp_funs_Units:
  assumes "f \<in> (Units (SA n))"
  shows "f \<in> (Units (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
proof-
  have 0:  "f \<otimes>\<^bsub>SA n\<^esub> inv\<^bsub>SA n\<^esub> f = \<one>\<^bsub>SA n\<^esub>"
        "inv\<^bsub>SA n\<^esub> f \<otimes>\<^bsub>SA n\<^esub> f = \<one>\<^bsub>SA n\<^esub>"
     using R.Units_r_inv assms apply blast
     using R.Units_l_inv assms by blast
  have 1: "f \<in> carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
    using assms
    by (metis SA_car SA_is_monoid monoid.Units_closed semialg_functions_memE(2))
  have 2: "inv\<^bsub>SA n\<^esub> f \<in> carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
    using SA_Units_inv_closed SA_car assms semialg_functions_memE(2) by blast
  then show ?thesis
   using 0 1 2  SA_one SA_times local.F.UnitsI(1) by auto
qed

lemma SA_Units_Qp_funs_inv:
  assumes "f \<in> (Units (SA n))"
  shows "inv\<^bsub>SA n\<^esub> f = inv\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub> f"
  using assms SA_Units_Qp_funs_Units
  by (metis (no_types, opaque_lifting) Qp_funs_is_cring Qp_funs_is_monoid SA_Units_memE(1)
      SA_is_monoid SA_one SA_times cring.invI(1) monoid.Units_closed monoid.Units_inv_Units)

lemma SA_Units_memI:
  assumes "f \<in> (carrier (SA n))"
  assumes "\<And> x. x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<Longrightarrow>  f x \<noteq> \<zero>\<^bsub>Q\<^sub>p\<^esub>"
  shows "f \<in> (Units (SA n))"
  using assms Qp_funs_Units_memI[of f n] Qp_funs_Units_SA_Units SA_car SA_imp_semialg
      semialg_functions_memE(2) by blast

lemma SA_Units_memE':
  assumes "f \<in> (Units (SA n))"
  shows  "\<And> x. x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<Longrightarrow>  f x \<noteq> \<zero>\<^bsub>Q\<^sub>p\<^esub>"
  using assms Qp_funs_Units_memE[of f n] SA_Units_Qp_funs_Units
  by blast

lemma Qp_n_nonempty:
  shows "carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<noteq> {}"
  apply(induction n)
  apply (simp add: Qp_zero_carrier)
  using cartesian_power_cons[of _ Q\<^sub>p _ \<one>] Qp.one_closed
  by (metis Suc_eq_plus1 all_not_in_conv cartesian_power_cons empty_iff)

lemma SA_one_not_zero:
  shows "\<one>\<^bsub>SA n\<^esub> \<noteq> \<zero>\<^bsub> SA n\<^esub>"
proof-
  obtain a where a_def: "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
    using Qp_n_nonempty by blast
  have "\<one>\<^bsub>SA n\<^esub> a  \<noteq> \<zero>\<^bsub> SA n\<^esub> a"
    using function_one_eval function_zero_eval SA_one SA_zero a_def local.one_neq_zero by presburger
  then show ?thesis
    by metis
qed

lemma SA_units_not_zero:
  assumes "f \<in> Units (SA n)"
  shows "f \<noteq> \<zero>\<^bsub> SA n\<^esub>"
  using SA_one_not_zero
  by (metis assms padic_fields.SA_is_ring padic_fields_axioms ring.ring_in_Units_imp_not_zero)

lemma SA_Units_nonzero:
  assumes "f \<in> Units (SA m)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "f x \<in> nonzero Q\<^sub>p"
  unfolding nonzero_def  mem_Collect_eq
  apply(rule conjI)
  using assms  SA_Units_closed SA_car_memE(3)[of f m]  apply blast
  using assms SA_Units_memE' by blast

lemma SA_car_closed:
  assumes "f \<in> carrier (SA m)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "f x \<in> carrier Q\<^sub>p"
  using assms SA_car_memE(3) by blast

lemma SA_Units_closed_fun:
  assumes "f \<in> Units (SA m)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "f x \<in> carrier Q\<^sub>p"
  using SA_Units_closed SA_car_closed assms by blast

lemma SA_inv_eval:
  assumes "f \<in> Units (SA n)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "(inv\<^bsub>SA n\<^esub> f) x = inv (f x)"
proof-
  have  "f \<otimes>\<^bsub>SA n\<^esub> (inv\<^bsub>SA n\<^esub> f) = \<one> \<^bsub>SA n\<^esub>"
    using assms SA_is_cring  SA_Units_memE(1) by blast
  hence  "(f \<otimes>\<^bsub>SA n\<^esub> (inv\<^bsub>SA n\<^esub> f)) x = \<one>  \<^bsub>SA n\<^esub> x"
    using assms by presburger
  then have "(f x) \<otimes> (inv\<^bsub>SA n\<^esub> f) x = \<one>"
    by (metis function_one_eval SA_mult SA_one assms)
  then show ?thesis
    by (metis Q\<^sub>p_def Qp_funs_m_inv Zp_def assms(1) assms(2) padic_fields.SA_Units_Qp_funs_Units padic_fields.SA_Units_Qp_funs_inv padic_fields_axioms)
qed

lemma SA_div_eval:
  assumes "f \<in> Units (SA n)"
  assumes "h \<in> carrier (SA n)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "(h \<otimes>\<^bsub>SA n\<^esub> (inv\<^bsub>SA n\<^esub> f)) x = h x \<otimes> inv (f x)"
  using assms SA_inv_eval  SA_mult by presburger

lemma SA_unit_int_pow:
  assumes "f \<in> Units (SA m)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "(f[^]\<^bsub>SA m\<^esub>(i::int)) x = (f x)[^]i"
proof(induction i)
  case (nonneg n)
  have  0: "(f [^]\<^bsub>SA m\<^esub> int n) = (f [^]\<^bsub>SA m\<^esub> n)"
    using assms by (meson int_pow_int)
  then show ?case using SA_Units_closed[of f m] assms
    by (metis SA_nat_pow int_pow_int)
next
  case (neg n)
  have 0: "(f [^]\<^bsub>SA m\<^esub> - int (Suc n)) = inv \<^bsub>SA m\<^esub>(f [^]\<^bsub>SA m\<^esub> (Suc n))"
    using assms by (metis R.int_pow_inv' int_pow_int)
  then show ?case unfolding 0 using assms
    by (metis Qp.int_pow_inv' R.Units_pow_closed SA_Units_nonzero SA_inv_eval SA_nat_pow Units_eq_nonzero int_pow_int)
qed

lemma restrict_in_SA_car:
  assumes "is_semialg_function n f"
  shows "restrict f (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) \<in> carrier (SA n)"
  using assms  SA_car restrict_in_semialg_functions
  by blast

lemma SA_smult:
"(\<odot>\<^bsub>SA n\<^esub>) = (\<odot>\<^bsub>Fun\<^bsub>n\<^esub> Q\<^sub>p\<^esub>)"
  unfolding SA_def by auto

lemma SA_smult_formula:
  assumes "h \<in> carrier (SA n)"
  assumes "q \<in> carrier Q\<^sub>p"
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "(q \<odot>\<^bsub>SA n\<^esub> h) a = q \<otimes>(h a)"
  using SA_smult assms function_smult_eval SA_car_memE(2) by presburger

lemma SA_smult_closed:
  assumes "h \<in> carrier (SA n)"
  assumes "q \<in> carrier Q\<^sub>p"
  shows "q \<odot>\<^bsub>SA n\<^esub> h \<in> carrier (SA n)"
proof-
  obtain g where g_def: "g = \<cc>\<^bsub>n\<^esub> q"
    by blast
  have g_closed: "g \<in> carrier (SA n)"
    using g_def assms constant_function_is_semialg[of q n] constant_function_closed SA_car_memI
    by blast
  have "q \<odot>\<^bsub>SA n\<^esub> h = g \<otimes>\<^bsub>SA n\<^esub> h"
    apply(rule function_ring_car_eqI[of _ n])
    using function_smult_closed SA_car_memE(2) SA_smult assms apply presburger
    using SA_car_memE(2) assms(1) assms(2) g_closed padic_fields.SA_imp_semialg padic_fields.SA_mult_closed_right padic_fields_axioms apply blast
    using Qp_constE SA_mult SA_smult_formula assms   g_def by presburger
  thus ?thesis
    using SA_imp_semialg SA_mult_closed_right assms(1) assms(2) g_closed by presburger
qed

lemma p_mult_function_val:
  assumes "f \<in> carrier (SA m)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "val ((\<pp> \<odot>\<^bsub>SA m\<^esub>f) x) = val (f x) + 1"
proof-
  have 0: "(\<pp>\<odot>\<^bsub>SA m\<^esub>f) x = \<pp>\<otimes>(f x)"
    using Qp.int_inc_closed SA_smult_formula assms(1) assms(2) by blast
  show ?thesis  unfolding 0 using assms
    by (metis Qp.function_ring_car_memE Qp.int_inc_closed Qp.m_comm SA_car semialg_functions_memE(2) val_mult val_p)
qed

lemma Qp_char_0'':
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "a \<noteq> \<zero>"
  assumes "(k::nat) > 0"
  shows "[k]\<cdot>a \<noteq> \<zero>"
proof-
  have 0: "[k]\<cdot>\<one> \<noteq>\<zero>"
    using Qp_char_0 assms(3) by blast
  have "[k]\<cdot>a = [k]\<cdot>\<one> \<otimes> a"
    using Qp.add_pow_ldistr Qp.l_one Qp.one_closed assms(1) by presburger
  thus ?thesis using 0 assms
    using Qp.integral by blast
qed

lemma SA_char_zero:
  assumes "f \<in> carrier (SA m)"
  assumes "f \<noteq> \<zero>\<^bsub>SA m\<^esub>"
  assumes "n > 0"
  shows "[(n::nat)]\<cdot>\<^bsub>SA m\<^esub>f \<noteq> \<zero>\<^bsub>SA m\<^esub>"
proof assume A: "[n] \<cdot>\<^bsub>SA m\<^esub> f = \<zero>\<^bsub>SA m\<^esub>"
  obtain x where x_def: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<and> f x \<noteq> \<zero>"
    using assms
    by (metis function_ring_car_eqI R.cring_simprules(2) SA_car_memE(2) SA_zeroE)
  have 0: "([(n::nat)]\<cdot>\<^bsub>SA m\<^esub>f) x = [n]\<cdot>(f x)"
    using SA_add_pow_apply assms(1) x_def by blast
  have 1: "[n]\<cdot>(f x) = \<zero>"
    using 0 unfolding A  using SA_zeroE x_def by blast
  have 2: "f x \<in> nonzero Q\<^sub>p"
    using x_def assms
    by (metis Qp.function_ring_car_memE SA_car not_nonzero_Qp semialg_functions_memE(2))
  then show False using x_def
    using "1" Qp.nonzero_memE(1) Qp_char_0'' assms(3) by blast
qed



(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Defining Semialgebraic Maps\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>
  We can define a semialgebraic map in essentially the same way that Denef defines
  semialgebraic functions. As for functions, we can define the partial pullback of a set
  $S \subseteq \mathbb{Q}_p^{n+l}$ by a map $g: \mathbb{Q}_p^m \to \mathbb{Q}_p^n$ to be the set
  \[
  \{(x,y) \in \mathbb{Q}_p^m \times \mathbb{Q}_p^l \mid (f(x), y) \in S \}
  \]
  and say that $g$ is a semialgebraic map if for every $l$, and every semialgebraic
  $S \subseteq \mathbb{Q}_p^{n+l}$, the partial pullback of $S$ by $g$ is also semialgebraic.
  On this definition, it is immediate that the composition $f \circ g$ of a semialgebraic
  function $f: \mathbb{Q}_p^n \to \mathbb{Q}$ and a semialgebraic map
  $g: \mathbb{Q}_p^m \to \mathbb{Q}_p^n$ is semialgebraic. It is also not hard to show that a map
  is semialgebraic if and only if all of its coordinate functions are semialgebraic functions.
  This allows us to build new semialgebraic functions out of old ones via composition.
\<close>


text\<open>Generalizing the notion of partial image partial pullbacks from functions to maps:\<close>

definition map_partial_image where
"map_partial_image m f xs = (f (take m xs))@(drop m xs)"

definition map_partial_pullback where
"map_partial_pullback m f l S = (map_partial_image m f)  \<inverse>\<^bsub>m+l\<^esub> S"

lemma map_partial_pullback_memE:
  assumes "as \<in> map_partial_pullback m f l S"
  shows "as \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)" "map_partial_image m f as \<in> S"
  using assms unfolding map_partial_pullback_def  evimage_def
  apply (metis (no_types, opaque_lifting) Int_iff add.commute)
  using assms unfolding map_partial_pullback_def
  by blast

lemma map_partial_pullback_closed:
"map_partial_pullback m f l S \<subseteq> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
  using map_partial_pullback_memE(1) by blast

lemma map_partial_pullback_memI:
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
  assumes "(f (take m as))@(drop m as) \<in> S"
  shows "as \<in> map_partial_pullback m f k S"
  using assms unfolding map_partial_pullback_def map_partial_image_def
  by blast

lemma map_partial_image_eq:
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "bs \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
  assumes "x = as @ bs"
  shows "map_partial_image n f x = (f as)@bs"
proof-
  have 0: "(take n x) = as"
    by (metis append_eq_conv_conj assms(1) assms(3) cartesian_power_car_memE)
  have 1: "drop n x = bs"
    by (metis "0" append_take_drop_id assms(3) same_append_eq)
  show ?thesis using 0 1 unfolding map_partial_image_def
    by blast
qed

lemma map_partial_pullback_memE':
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "bs \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
  assumes "x = as @ bs"
  assumes "x \<in> map_partial_pullback n f k S"
  shows "(f as)@bs \<in> S"
  using map_partial_pullback_memE[of x n f k S] map_partial_image_def[of n f x]
  by (metis assms(1) assms(2) assms(3) assms(4) map_partial_image_eq)

text\<open>Partial pullbacks have the same algebraic properties as pullbacks.\<close>

lemma map_partial_pullback_intersect:
"map_partial_pullback m f l (S1 \<inter> S2) = (map_partial_pullback m f l S1) \<inter> (map_partial_pullback m f l S2)"
  unfolding map_partial_pullback_def
  by simp

lemma map_partial_pullback_union:
"map_partial_pullback m f l (S1 \<union> S2) = (map_partial_pullback m f l S1) \<union> (map_partial_pullback m f l S2)"
  unfolding map_partial_pullback_def
  by simp

lemma map_partial_pullback_complement:
  assumes "f \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "map_partial_pullback m f l (carrier (Q\<^sub>p\<^bsup>n+l\<^esup>) - S) = carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) - (map_partial_pullback m f l S) "
  apply(rule equalityI)
  using map_partial_pullback_def[of m f l "(carrier (Q\<^sub>p\<^bsup>n+l\<^esup>) - S)"]
        map_partial_pullback_def[of m f l S]
   apply (metis (no_types, lifting) DiffD2 DiffI evimage_Diff map_partial_pullback_memE(1) subsetI)
proof fix x assume A: " x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) - map_partial_pullback m f l S"
  show " x \<in> map_partial_pullback m f l (carrier (Q\<^sub>p\<^bsup>n+l\<^esup>) - S) "
    apply(rule map_partial_pullback_memI)
    using A
     apply blast
  proof
    have 0: "drop m x \<in> carrier (Q\<^sub>p\<^bsup>l\<^esup>)"
      by (meson A DiffD1 cartesian_power_drop)
    have 1: "take m x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using A
      by (meson DiffD1 take_closed le_add1)
    show "f (take m x) @ drop m x \<in> carrier (Q\<^sub>p\<^bsup>n+l\<^esup>) "
      using 0 1 assms
      by (meson Pi_iff cartesian_power_concat(1))
    show "f (take m x) @ drop m x \<notin> S"
      using A unfolding map_partial_pullback_def map_partial_image_def
      by blast
  qed
qed

lemma map_partial_pullback_carrier:
  assumes "f \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "map_partial_pullback m f l (carrier (Q\<^sub>p\<^bsup>n+l\<^esup>)) = carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
  apply(rule equalityI)
  using map_partial_pullback_memE(1) apply blast
proof fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
  show "x \<in> map_partial_pullback m f l (carrier (Q\<^sub>p\<^bsup>n+l\<^esup>))"
    apply(rule map_partial_pullback_memI)
  using A cartesian_power_drop[of x m l] take_closed assms
   apply blast
proof-
  have "f (take m x) \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
    using A take_closed assms
    by (meson Pi_mem le_add1)
  then show "f (take m x) @ drop m x \<in> carrier (Q\<^sub>p\<^bsup>n+l\<^esup>)"
    using cartesian_power_drop[of x m l] A cartesian_power_concat(1)[of _ Q\<^sub>p n _ l]
    by blast
qed
qed

definition is_semialg_map where
"is_semialg_map m n f = (f \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier (Q\<^sub>p\<^bsup>n\<^esup>)  \<and>
                          (\<forall>l \<ge> 0. \<forall>S \<in> semialg_sets (n + l). is_semialgebraic (m + l) (map_partial_pullback m f l S)))"

lemma is_semialg_map_closed:
  assumes "is_semialg_map m n f"
  shows "f \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  using is_semialg_map_def assms by blast

lemma is_semialg_map_closed':
  assumes "is_semialg_map m n f" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "f x \<in>  carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  using is_semialg_map_def assms by blast

lemma is_semialg_mapE:
  assumes "is_semialg_map m n f"
  assumes "is_semialgebraic (n + k) S"
  shows " is_semialgebraic (m + k) (map_partial_pullback m f k S)"
  using is_semialg_map_def assms
  by (meson is_semialgebraicE le0)

lemma is_semialg_mapE':
  assumes "is_semialg_map m n f"
  assumes "is_semialgebraic (n + k) S"
  shows " is_semialgebraic (m + k) (map_partial_image m f \<inverse>\<^bsub>m+k\<^esub> S)"
  using assms is_semialg_mapE unfolding map_partial_pullback_def
  by blast

lemma is_semialg_mapI:
  assumes "f \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "\<And>k  S. S \<in> semialg_sets (n + k) \<Longrightarrow> is_semialgebraic (m + k) (map_partial_pullback m f k S)"
  shows "is_semialg_map m n f"
  using assms unfolding is_semialg_map_def
  by blast

lemma is_semialg_mapI':
  assumes "f \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "\<And>k  S. S \<in> semialg_sets (n + k) \<Longrightarrow> is_semialgebraic (m + k) (map_partial_image m f \<inverse>\<^bsub>m+k\<^esub> S)"
  shows "is_semialg_map m n f"
  using assms is_semialg_mapI unfolding map_partial_pullback_def
  by blast

text\<open>Semialgebraicity for functions can be verified on basic semialgebraic sets.\<close>

lemma is_semialg_mapI'':
  assumes "f \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "\<And>k  S. S \<in> basic_semialgs (n + k) \<Longrightarrow> is_semialgebraic (m + k) (map_partial_pullback m f k S)"
  shows "is_semialg_map m n f"
  apply(rule is_semialg_mapI)
  using assms(1) apply blast
proof-
  show "\<And>k S. S \<in> semialg_sets (n + k) \<Longrightarrow> is_semialgebraic (m + k) (map_partial_pullback m f k S)"
  proof- fix k S assume A: "S \<in> semialg_sets (n + k)"
    show "is_semialgebraic (m + k) (map_partial_pullback m f k S)"
      apply(rule gen_boolean_algebra.induct[of S "carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)" "basic_semialgs (n + k)"])
        using A unfolding semialg_sets_def
            apply blast
        using map_partial_pullback_carrier assms carrier_is_semialgebraic plus_1_eq_Suc apply presburger
        apply (simp add: assms(1) assms(2) carrier_is_semialgebraic intersection_is_semialg map_partial_pullback_carrier map_partial_pullback_intersect)
        using map_partial_pullback_union union_is_semialgebraic apply presburger
        using assms(1) complement_is_semialg map_partial_pullback_complement plus_1_eq_Suc by presburger
  qed
qed

lemma is_semialg_mapI''':
  assumes "f \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "\<And>k  S. S \<in> basic_semialgs (n + k) \<Longrightarrow> is_semialgebraic (m + k) (map_partial_image m f \<inverse>\<^bsub>m+k\<^esub> S)"
  shows "is_semialg_map m n f"
  using is_semialg_mapI'' assms unfolding map_partial_pullback_def
  by blast

lemma id_is_semialg_map:
"is_semialg_map n n (\<lambda> x. x)"
proof-
  have 0: "\<And>k S. S \<in> semialg_sets (n + k) \<Longrightarrow> (\<lambda>xs. take n xs @ drop n xs) -` S \<inter> carrier (Q\<^sub>p\<^bsup>n + k\<^esup>) =
            S"
    apply(rule equalityI')
     apply (metis (no_types, lifting) Int_iff append_take_drop_id vimage_eq)
    by (metis (no_types, lifting) IntI append_take_drop_id in_mono is_semialgebraicI is_semialgebraic_closed vimageI)
  show ?thesis
    by(intro is_semialg_mapI,
          unfold  map_partial_pullback_def map_partial_image_def evimage_def is_semialgebraic_def  0,
          auto)
qed

lemma map_partial_pullback_comp:
  assumes "is_semialg_map m n f"
  assumes "is_semialg_map k m g"
  shows  "(map_partial_pullback k (f \<circ> g) l S) = (map_partial_pullback k g l (map_partial_pullback m f l S))"
proof
  show "map_partial_pullback k (f \<circ> g) l S \<subseteq> map_partial_pullback k g l (map_partial_pullback m f l S)"
  proof fix x assume A: " x \<in> map_partial_pullback k (f \<circ> g) l S"
    show " x \<in> map_partial_pullback k g l (map_partial_pullback m f l S)"
    proof(rule map_partial_pullback_memI)
      show 0: "x \<in> carrier (Q\<^sub>p\<^bsup>k+l\<^esup>)"
        using A map_partial_pullback_memE(1) by blast
      show "g (take k x) @ drop k x \<in> map_partial_pullback m f l S"
      proof(rule map_partial_pullback_memI)
        show "g (take k x) @ drop k x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
        proof-
          have 1: "g (take k x) \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
            using 0 assms(2) is_semialg_map_closed[of k m g]
            by (meson Pi_iff le_add1 take_closed)
          then show ?thesis
            by (metis "0" add.commute cartesian_power_concat(2) cartesian_power_drop)
        qed
        show "f (take m (g (take k x) @ drop k x)) @ drop m (g (take k x) @ drop k x) \<in> S"
        using map_partial_pullback_memE[of x k "f \<circ> g" l S]
          comp_apply[of f g] map_partial_image_eq[of "take k x" k "drop k x" l x "f \<circ> g"]
        by (metis (no_types, lifting) A \<open>g (take k x) @ drop k x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)\<close>
            append_eq_append_conv append_take_drop_id cartesian_power_car_memE
            cartesian_power_drop map_partial_image_def)
      qed
    qed
  qed
  show "map_partial_pullback k g l (map_partial_pullback m f l S) \<subseteq> map_partial_pullback k (f \<circ> g) l S"
  proof fix x assume A: "x \<in> map_partial_pullback k g l (map_partial_pullback m f l S)"
    have 0: "(take m (map_partial_image k g x)) = g (take k x)"
    proof-
      have "take k x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
        using map_partial_pullback_memE[of x k g l] A le_add1 take_closed
        by blast
      then have "length (g (take k x)) = m"
        using assms is_semialg_map_closed[of k m g] cartesian_power_car_memE
        by blast
      then show ?thesis
        using assms unfolding map_partial_image_def
        by (metis append_eq_conv_conj)
    qed
    show " x \<in> map_partial_pullback k (f \<circ> g) l S"
      apply(rule map_partial_pullback_memI)
      using A map_partial_pullback_memE
       apply blast
      using 0 assms A comp_apply map_partial_pullback_memE[of x k g l "map_partial_pullback m f l S"]
            map_partial_pullback_memE[of "map_partial_image k g x" m f l S]
  map_partial_image_eq[of "take k x" k "drop k x" l x g]
   map_partial_image_eq[of "take m (map_partial_image k g x)" m "drop m (map_partial_image k g x)" l "(map_partial_image k g x)" f ]
  by (metis (no_types, lifting) cartesian_power_drop le_add1 map_partial_image_def map_partial_pullback_memE' take_closed)
qed
qed

lemma semialg_map_comp_closed:
  assumes "is_semialg_map m n f"
  assumes "is_semialg_map k m g"
  shows "is_semialg_map k n (f \<circ> g)"
  apply(intro is_semialg_mapI , unfold Pi_iff comp_def, intro ballI,
        intro is_semialg_map_closed'[of m n f] is_semialg_map_closed'[of k m g]  assms, blast)
proof- fix l S assume A: "S \<in> semialg_sets (n + l)"
  have " is_semialgebraic (k + l) (map_partial_pullback k (f \<circ> g) l S)"
    using map_partial_pullback_comp is_semialg_mapE A assms(1) assms(2) is_semialgebraicI
    by presburger
  thus "is_semialgebraic (k + l) (map_partial_pullback k (\<lambda>x. f (g x)) l S)"
    unfolding comp_def by auto
qed

lemma partial_pullback_comp:
  assumes "is_semialg_function m f"
  assumes "is_semialg_map k m g"
  shows  "(partial_pullback k (f \<circ> g) l S) = (map_partial_pullback k g l (partial_pullback m f l S))"
proof
  show "partial_pullback k (f \<circ> g) l S \<subseteq> map_partial_pullback k g l (partial_pullback m f l S)"
  proof fix x assume A: "x \<in> partial_pullback k (f \<circ> g) l S"
    show "x \<in> map_partial_pullback k g l (partial_pullback m f l S)"
    proof(rule map_partial_pullback_memI)
      show 0: "x \<in> carrier (Q\<^sub>p\<^bsup>k+l\<^esup>)"
        using A partial_pullback_memE(1) by blast
      show "g (take k x) @ drop k x \<in> partial_pullback m f l S"
      proof(rule partial_pullback_memI)
        show "g (take k x) @ drop k x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
        proof-
          have 1: "g (take k x) \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
            using 0 assms(2) is_semialg_map_closed[of k m g]
            by (meson Pi_iff le_add1 take_closed)
          then show ?thesis
            by (metis "0" add.commute cartesian_power_concat(2) cartesian_power_drop)
        qed
        show "f (take m (g (take k x) @ drop k x)) # drop m (g (take k x) @ drop k x) \<in> S"
        using partial_pullback_memE[of x k "f \<circ> g" l S]
          comp_apply[of f g] partial_image_eq[of "take k x" k "drop k x" l x "f \<circ> g"]
        by (metis (no_types, lifting) A \<open>g (take k x) @ drop k x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)\<close>
            add_diff_cancel_left' append_eq_append_conv append_take_drop_id
            cartesian_power_car_memE length_drop local.partial_image_def)
      qed
    qed
  qed
  show "map_partial_pullback k g l (partial_pullback m f l S) \<subseteq> partial_pullback k (f \<circ> g) l S"
  proof fix x assume A: "x \<in> map_partial_pullback k g l (partial_pullback m f l S)"
    have 0: "(take m (map_partial_image k g x)) = g (take k x)"
    proof-
      have "take k x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
        using map_partial_pullback_memE[of x k g l] A le_add1 take_closed
        by blast
      then have "length (g (take k x)) = m"
        using assms is_semialg_map_closed[of k m g] cartesian_power_car_memE
        by blast
      then show ?thesis
        using assms unfolding map_partial_image_def
        by (metis append_eq_conv_conj)
    qed
    show "x \<in> partial_pullback k (f \<circ> g) l S"
      apply(rule partial_pullback_memI)
      using A map_partial_pullback_memE
       apply blast
      using 0 assms A comp_apply map_partial_pullback_memE[of x k g l "partial_pullback m f l S"]
            partial_pullback_memE[of "map_partial_image k g x" m f l S]
            map_partial_image_eq[of "take k x" k "drop k x" l x g]
   partial_image_eq[of "take m (map_partial_image k g x)" m "drop m (map_partial_image k g x)" l "(map_partial_image k g x)" f ]
  by (metis (no_types, lifting) cartesian_power_drop le_add1 map_partial_image_def partial_pullback_memE' take_closed)

qed
qed

lemma semialg_function_comp_closed:
  assumes "is_semialg_function m f"
  assumes "is_semialg_map k m g"
  shows "is_semialg_function k (f \<circ> g)"
proof(rule is_semialg_functionI)
  show "f \<circ> g \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  proof fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
    show " (f \<circ> g) x \<in> carrier Q\<^sub>p"
      using A assms is_semialg_map_closed[of k m g ] is_semialg_function_closed[of m f] comp_apply[of f g x]
      by (metis (no_types, lifting) Pi_mem)
  qed
  show " \<And>ka S. S \<in> semialg_sets (1 + ka) \<Longrightarrow> is_semialgebraic (k + ka) (partial_pullback k (f \<circ> g) ka S)"
  proof- fix n S assume A: "S \<in> semialg_sets (1 + n)"
    show "is_semialgebraic (k + n) (partial_pullback k (f \<circ> g) n S)"
      using A assms partial_pullback_comp is_semialg_functionE is_semialg_mapE
        is_semialgebraicI  by presburger
  qed
qed

lemma semialg_map_evimage_is_semialg:
  assumes "is_semialg_map k m g"
  assumes "is_semialgebraic m S"
  shows "is_semialgebraic k (g  \<inverse>\<^bsub>k\<^esub> S)"
proof-
  have "g  \<inverse>\<^bsub>k\<^esub> S = map_partial_pullback k g 0 S"
  proof
    show "g \<inverse>\<^bsub>k\<^esub> S \<subseteq> map_partial_pullback k g 0 S"
    proof fix x assume A: "x \<in> g  \<inverse>\<^bsub>k\<^esub> S"
      then have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<and> g x \<in> S"
        by (meson evimage_eq)
      have "x = take k x @ drop k x"
        using 0  by (simp add: "0")
      then show "x \<in> map_partial_pullback k g 0 S"
        unfolding map_partial_pullback_def map_partial_image_def
        by (metis (no_types, lifting) "0" Nat.add_0_right add.commute append_Nil2 append_same_eq
        append_take_drop_id evimageI2 map_partial_image_def map_partial_image_eq take0 take_drop)
    qed
    show "map_partial_pullback k g 0 S \<subseteq> g \<inverse>\<^bsub>k\<^esub> S"
    proof fix x assume A: "x \<in> map_partial_pullback k g 0 S "
      then have 0: " g (take k x) @ (drop k x) \<in> S"
        unfolding map_partial_pullback_def map_partial_image_def
        by blast
      have 1: "x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
        using A unfolding map_partial_pullback_def map_partial_image_def
        by (metis (no_types, lifting) Nat.add_0_right evimage_eq)
      hence "take k x = x"
        by (metis cartesian_power_car_memE le_eq_less_or_eq take_all)
      then show " x \<in> g \<inverse>\<^bsub>k\<^esub> S"
        using 0 1 unfolding evimage_def
        by (metis (no_types, lifting) IntI append.assoc append_same_eq append_take_drop_id same_append_eq vimageI)
    qed
  qed
  then show ?thesis using assms
    by (metis add.right_neutral is_semialg_mapE' map_partial_pullback_def)
qed


(**************************************************************************************************)
(**************************************************************************************************)
subsection \<open>Examples of Semialgebraic Maps\<close>
(**************************************************************************************************)
(**************************************************************************************************)


lemma semialg_map_on_carrier:
  assumes "is_semialg_map n m f"
  assumes "restrict f (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) = restrict g (carrier (Q\<^sub>p\<^bsup>n\<^esup>))"
  shows "is_semialg_map n m g"
proof(rule is_semialg_mapI)
  have 0: "f \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms(1) is_semialg_map_closed
    by blast
  show "g \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  proof fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)" then show " g x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using assms(2) 0
      by (metis (no_types, lifting) PiE restrict_Pi_cancel)
  qed
  show "\<And>k S. S \<in> semialg_sets (m + k) \<Longrightarrow> is_semialgebraic (n + k) (map_partial_pullback n g k S)"
  proof- fix k S
    assume A: "S \<in> semialg_sets (m + k)"
    have 1: "is_semialgebraic (n + k) (map_partial_pullback n f k S)"
      using A assms(1) is_semialg_mapE is_semialgebraicI
      by blast
    have 2: "(map_partial_pullback n f k S) = (map_partial_pullback n g k S)"
      unfolding map_partial_pullback_def map_partial_image_def evimage_def
    proof
      show "(\<lambda>xs. f (take n xs) @ drop n xs) -` S \<inter> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>) \<subseteq> (\<lambda>xs. g (take n xs) @ drop n xs) -` S \<inter> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
      proof fix x assume A: "x \<in> (\<lambda>xs. f (take n xs) @ drop n xs) -` S \<inter> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
        have "(take n x) \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
          using assms A
          by (meson Int_iff le_add1 take_closed)
        then have "f (take n x) = g (take n x)"
          using assms unfolding  restrict_def
          by meson
        then show "x \<in> (\<lambda>xs. g (take n xs) @ drop n xs) -` S \<inter> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
          using assms
          by (metis (no_types, lifting) A Int_iff vimageE vimageI)
      qed
      show " (\<lambda>xs. g (take n xs) @ drop n xs) -` S \<inter> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>) \<subseteq> (\<lambda>xs. f (take n xs) @ drop n xs) -` S \<inter> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
      proof fix x assume A: "x \<in> (\<lambda>xs. g (take n xs) @ drop n xs) -` S \<inter> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
        have "(take n x) \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
          using assms
          by (meson A  inf_le2 le_add1 subset_iff take_closed)
        then have "f (take n x) = g (take n x)"
          using assms unfolding  restrict_def
          by meson
        then show " x \<in> (\<lambda>xs. f (take n xs) @ drop n xs) -` S \<inter> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
          using A by blast
      qed
    qed
    then show "is_semialgebraic (n + k) (map_partial_pullback n g k S)"
      using 1 by auto
  qed
qed

lemma semialg_function_tuple_is_semialg_map:
  assumes "is_semialg_function_tuple m fs"
  assumes "length fs = n"
  shows "is_semialg_map m n (function_tuple_eval Q\<^sub>p m fs)"
  apply(rule is_semialg_mapI)
  using function_tuple_eval_closed[of m fs]
  apply (metis Pi_I assms(1) assms(2) semialg_function_tuple_is_function_tuple)
proof- fix k S assume A: "S \<in> semialg_sets (n + k)"
  show "is_semialgebraic (m + k) (map_partial_pullback m (function_tuple_eval Q\<^sub>p m fs) k S)"
  using is_semialg_map_tupleE[of m fs k S] assms A tuple_partial_pullback_is_semialg_map_tuple[of m fs]
  unfolding tuple_partial_pullback_def map_partial_pullback_def
        map_partial_image_def tuple_partial_image_def is_semialgebraic_def
  by (metis evimage_def)
qed

lemma index_is_semialg_function:
  assumes "n > k"
  shows "is_semialg_function n (\<lambda>as. as!k)"
proof-
  have 0: "restrict (\<lambda>as. as!k) (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) = restrict (Qp_ev (pvar Q\<^sub>p k)) (carrier (Q\<^sub>p\<^bsup>n\<^esup>))"
    using assms by (metis (no_types, lifting) eval_pvar restrict_ext)
  have 1: "is_semialg_function n (Qp_ev (pvar Q\<^sub>p k))"
    using pvar_closed   assms poly_is_semialg[of  "pvar Q\<^sub>p k"] by blast
  show ?thesis
    using 0 1 semialg_function_on_carrier[of n "Qp_ev (pvar Q\<^sub>p k)" "(\<lambda>as. as!k)"]
    by presburger
qed

definition Qp_ith where
"Qp_ith m i = (\<lambda> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). x!i)"

lemma Qp_ith_closed:
  assumes "i < m"
  shows "Qp_ith m i \<in> carrier (SA m)"
proof(rule SA_car_memI)
  show "Qp_ith m i \<in> carrier (function_ring (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) Q\<^sub>p)"
    apply(rule Qp.function_ring_car_memI[of "carrier(Q\<^sub>p\<^bsup>m\<^esup>)"])
    using assms cartesian_power_car_memE'[of _ Q\<^sub>p m i] unfolding Qp_ith_def
    apply (metis restrict_apply)
    unfolding restrict_def by meson
  have 0: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> Qp_ith m i x = eval_at_point Q\<^sub>p  x (pvar Q\<^sub>p i)"
    using assms eval_pvar[of i m] unfolding Qp_ith_def restrict_def by presburger
  have 1: "is_semialg_function m (eval_at_poly Q\<^sub>p  (pvar Q\<^sub>p i))"
    using assms pvar_closed[of i m] poly_is_semialg by blast
  show "is_semialg_function m (local.Qp_ith m i)"
    apply(rule semialg_function_on_carrier'[of m "eval_at_poly Q\<^sub>p  (pvar Q\<^sub>p i)"])
    using 1 apply blast
    using 0 by blast
qed

lemma take_is_semialg_map:
  assumes "n \<ge> k"
  shows "is_semialg_map n k (take k)"
proof-
  obtain fs where fs_def: "fs = map (\<lambda>i::nat. (\<lambda>as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). as!i)) [0::nat..< k]"
    by blast
  have 0: "is_semialg_function_tuple n fs"
  proof(rule is_semialg_function_tupleI)
    fix f assume A: "f \<in> set fs"
    then obtain i where i_def: "i \<in> set [0::nat..< k] \<and> f = (\<lambda>as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). as!i)"
      using A fs_def
      by (metis (no_types, lifting) in_set_conv_nth length_map nth_map)
    have i_less: "i < k"
    proof-
      have "set [0::nat..< k] = {0..<k}"
        using atLeastLessThan_upt by blast
      then show ?thesis using i_def
        using atLeastLessThan_iff by blast
    qed
    show "is_semialg_function n f"
      apply(rule semialg_function_on_carrier[of n "(\<lambda>as. as ! i)"],
            rule index_is_semialg_function[of i n ]  )
      using A i_def assms by auto
  qed
  have 1: "restrict (function_tuple_eval Q\<^sub>p n fs) (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) = restrict (take k) (carrier (Q\<^sub>p\<^bsup>n\<^esup>))"
  unfolding function_tuple_eval_def
  proof fix x
    show " (\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>n\<^esup>). map (\<lambda>f. f x) fs) x = restrict (take k) (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) x"
  proof(cases "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)")
    case True
    have "(map (\<lambda>f. f x) fs) = take k x"
    proof-
      have "\<And>i. i < k \<Longrightarrow> (map (\<lambda>f. f x) fs) ! i = x ! i"
      proof- fix i assume A: "i < k"
        have "length [0::nat..< k] = k"
          using assms by simp
        then have "length fs = k"
          using fs_def
          by (metis length_map)
        then have 0: "(map (\<lambda>f. f x) fs) ! i = (fs!i) x"
          using A by (meson nth_map)
        have 1: "(fs!i) x = x!i"
          using A nth_map[of i "[0..<k]" "(\<lambda>i. \<lambda>as\<in>carrier (Q\<^sub>p\<^bsup>n\<^esup>). as ! i)"] True
          unfolding fs_def  restrict_def  by auto
        then show "map (\<lambda>f. f x) fs ! i = x ! i"
          using 0 assms A True fs_def nth_map[of i fs] cartesian_power_car_memE[of x Q\<^sub>p n]
          by blast
      qed
      then have 0: "\<And>i. i < k \<Longrightarrow> (map (\<lambda>f. f x) fs) ! i = (take k x) ! i"
        using assms True  nth_take by blast
      have 1: "length (map (\<lambda>f. f x) fs) = length (take k x)"
        using fs_def True assms
        by (metis cartesian_power_car_memE length_map map_nth take_closed)
      have 2: "length (take k x) = k"
        using assms True cartesian_power_car_memE take_closed
        by blast
      show ?thesis using 0 1 2
        by (metis nth_equalityI)
    qed
    then show ?thesis using True unfolding restrict_def
      by presburger
  next
    case False
    then show ?thesis unfolding restrict_def
      by (simp add: False)
  qed
  qed
  have 2: " is_semialg_map n k (function_tuple_eval Q\<^sub>p n fs)"
    using 0 semialg_function_tuple_is_semialg_map[of n fs k] assms fs_def  length_map
    by (metis (no_types, lifting) diff_zero length_upt)
  show ?thesis using 1 2
    using semialg_map_on_carrier by blast
qed

lemma drop_is_semialg_map:
  shows "is_semialg_map (k + n) n (drop k)"
proof-
  obtain fs where fs_def: "fs = map (\<lambda>i::nat. (\<lambda>as \<in> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>). as!i)) [k..<n+k]"
    by blast
  have 0: "is_semialg_function_tuple (k+n) fs"
  proof(rule is_semialg_function_tupleI)
    fix f assume A: "f \<in> set fs"
    then obtain i where i_def: "i \<in> set [k..<n+k] \<and> f = (\<lambda>as \<in> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>). as!i)"
      using A fs_def
      by (metis (no_types, lifting) in_set_conv_nth length_map nth_map)
    have i_less: "i \<ge> k \<and> i < n + k"
    proof-
      have "set [k..<n+k] = {k..<n+k}"
        using atLeastLessThan_upt by blast
      then show ?thesis using i_def
        using atLeastLessThan_iff by blast
    qed
    have "is_semialg_function (n + k) f"
      using A index_is_semialg_function[of i "n+k" ]
            i_less semialg_function_on_carrier[of "n+k" "(\<lambda>as. as ! i)" f] i_def
            restrict_is_semialg
      by blast
    then show "is_semialg_function (k + n) f"
      by (simp add: add.commute)
  qed
  have 1: "restrict (function_tuple_eval Q\<^sub>p (n+k) fs) (carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)) = restrict (drop k) (carrier (Q\<^sub>p\<^bsup>n+k\<^esup>))"
  unfolding function_tuple_eval_def
  proof fix x
    show " (\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>n+k\<^esup>). map (\<lambda>f. f x) fs) x = restrict (drop k) (carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)) x"
  proof(cases "x\<in>carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)")
    case True
    have "(map (\<lambda>f. f x) fs) = drop k x"
    proof-
      have "\<And>i. i < n \<Longrightarrow> (map (\<lambda>f. f x) fs) ! i = x ! (i+k)"
      proof- fix i assume A: "i < n"
        have 00: "length [k..<n+k] = n"
           by simp
        then have "length fs = n"
          using fs_def
          by (metis length_map)
        then have 0:"(map (\<lambda>f. f x) fs) ! i = (fs!i) x"
          using A  by (meson nth_map)
        have "[k..<n+k]!i = i + k"
          by (simp add: A)
        have "( map (\<lambda>i. \<lambda>as\<in>carrier (Q\<^sub>p\<^bsup>n+k\<^esup>). as ! i) [k..<n + k]) ! i = ((\<lambda>i. \<lambda>as\<in>carrier (Q\<^sub>p\<^bsup>n+k\<^esup>). as ! i) ([k..<n + k] ! i))"
          using A 00 nth_map[of i "[k..< n + k]" "(\<lambda>i. \<lambda>as\<in>carrier (Q\<^sub>p\<^bsup>n+k\<^esup>). as ! i)"]
          by linarith
        then have 1: "fs!i =  (\<lambda>as \<in> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>). as!(i+k))"
          using fs_def A  \<open>[k..<n + k] ! i = i + k\<close> by presburger
        then show "map (\<lambda>f. f x) fs ! i = x ! (i + k)"
          using True 0
          by (metis (no_types, lifting) restrict_apply)
      qed
      then have 0: "\<And>i. i < n \<Longrightarrow> (map (\<lambda>f. f x) fs) ! i = (drop k x) ! i"
        using True  nth_drop
        by (metis add.commute cartesian_power_car_memE le_add2)
      have 1: "length (map (\<lambda>f. f x) fs) = length (drop k x)"
        using fs_def True length_drop[of k x]
        by (metis cartesian_power_car_memE length_map length_upt)
      have 2: "length (drop k x) = n"
        using True cartesian_power_car_memE
        by (metis add_diff_cancel_right' length_drop)
      show ?thesis using 0 1 2
        by (metis nth_equalityI)
    qed
    then show ?thesis using True unfolding restrict_def
      by presburger
  next
    case False
    then show ?thesis unfolding restrict_def
      by (simp add: False)
  qed
  qed
  have 00: "length [k..<n+k] = n"
    by simp
  then have "length fs = n"
    using fs_def
    by (metis length_map)
  then have 2: " is_semialg_map (k + n) n (function_tuple_eval Q\<^sub>p (k + n) fs)"
    using 0 semialg_function_tuple_is_semialg_map[of "k + n" fs n]
    by blast
  show ?thesis using 1 2
    using semialg_map_on_carrier[of "k + n" n "function_tuple_eval Q\<^sub>p (k + n) fs" "drop k"]
    by (metis add.commute)
qed

lemma project_at_indices_is_semialg_map:
  assumes "S \<subseteq> {..<n}"
  shows "is_semialg_map n (card S) \<pi>\<^bsub>S\<^esub>"
proof-
  obtain k where k_def: "k = card S"
    by blast
  have 0: "card {..<n} = n"
    by simp
  have 1: "finite S"
    using assms finite_subset
    by blast
  have 2: "card S \<le> n"
    using assms 0 1
    by (metis card_mono finite_lessThan)
  then have k_size: " k \<le> n"
    using k_def assms 0 1 2
    by blast
  obtain fs where fs_def: "fs = map (\<lambda>i::nat. (\<lambda>as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). as!(nth_elem S i))) [0..<k]"
    by blast
  have 4: "length fs = k"
    using fs_def assms "1" k_def
    by (metis Ex_list_of_length length_map map_nth)
  have 5: "is_semialg_function_tuple n fs"
  proof(rule is_semialg_function_tupleI)
    fix f assume A: "f \<in> set fs"
    then obtain i where i_def: "i \<in> set [0..<k] \<and> f = (\<lambda>as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). as!(nth_elem S i))"
      using A fs_def atLeast_upt "4"  in_set_conv_nth  map_eq_conv map_nth
      by auto
    have i_le_k:"i < k"
    proof-
      have "set [0..<k] = {..<k}"
        using atLeast_upt by blast
      then show ?thesis
        using i_def
        by blast
    qed
    then have i_in_S: "nth_elem S i \<in> S"
      using "1" k_def nth_elem_closed by blast
    then have "nth_elem S i < n"
      using assms
      by blast
    show "is_semialg_function n f"
      using A index_is_semialg_function[of "nth_elem S i" n]
            semialg_function_on_carrier[of n "(\<lambda>as. as ! nth_elem S i)"] i_def restrict_is_semialg
            \<open>nth_elem S i < n\<close> by blast
  qed
  have 6: "restrict (function_tuple_eval Q\<^sub>p n fs) (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) = restrict (\<pi>\<^bsub>S\<^esub>) (carrier (Q\<^sub>p\<^bsup>n\<^esup>))"
  unfolding function_tuple_eval_def
  proof fix x
    show " (\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>n\<^esup>). map (\<lambda>f. f x) fs) x = restrict (\<pi>\<^bsub>S\<^esub>) (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) x"
    proof(cases "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)")
    case True
    have "(map (\<lambda>f. f x) fs) = \<pi>\<^bsub>S\<^esub> x"
    proof-
      have "\<And>i. i < k \<Longrightarrow> (map (\<lambda>f. f x) fs) ! i = (\<pi>\<^bsub>S\<^esub> x) ! i"
      proof- fix i assume A: "i < k"
        have T0:"(map (\<lambda>f. f x) fs) ! i = (fs!i) x"
          using A nth_map by (metis "4")
        have T1: "indices_of x = {..< n}"
          using True cartesian_power_car_memE indices_of_def
          by blast
        have T2: "set (set_to_list S) \<subseteq> indices_of x"
          using assms True  by (simp add: True "1" T1)
        have T3: "length x = n"
          using True cartesian_power_car_memE by blast
        have T4: "([0..<k] ! i) =   i"
          using A by simp
        have T5: "nth_elem S i < n"
          using assms 0 1 2 A k_def
          by (meson lessThan_iff nth_elem_closed subsetD)
        have T6: "nth_elem S ([0..<k] ! i) = nth_elem S i"
          by (simp add: T4)
        have T6: "(\<lambda>as\<in>carrier (Q\<^sub>p\<^bsup>n\<^esup>). as ! nth_elem S ([0..<k] ! i)) x = x! (nth_elem S i)"
        proof-
          have "(\<lambda>as\<in>carrier (Q\<^sub>p\<^bsup>n\<^esup>). as ! nth_elem S ([0..<k] ! i)) x = x! nth_elem S ([0..<k] ! i)"
            using True restrict_def by metis
          then show ?thesis
            using A T3 T4 0 1 2 T5 T6  True
            by metis
        qed
        have T7: " map (\<lambda>f. f x) fs ! i = x! (nth_elem S i)"
          using fs_def T0 A nth_map[of i "[0..<k]" "(\<lambda>i. \<lambda>as\<in>carrier (Q\<^sub>p\<^bsup>n\<^esup>). as ! nth_elem S i)"]
          by (metis "4" T6 length_map)
        show "map (\<lambda>f. f x) fs ! i = \<pi>\<^bsub>S\<^esub> x ! i"
          using True T0 T1 T2 fs_def 5 unfolding T7
          by (metis A assms(1) k_def project_at_indices_nth)
      qed
      have 1: "length (map (\<lambda>f. f x) fs) = length (\<pi>\<^bsub>S\<^esub> x)"
        using fs_def True assms proj_at_index_list_length[of S x] k_def
        by (metis "4" cartesian_power_car_memE indices_of_def length_map)
      have 2: "length (\<pi>\<^bsub>S\<^esub> x) = k"
        using assms True 0 1 2
        by (metis "4" length_map)
      show ?thesis using  1 2
        by (metis \<open>\<And>i. i < k \<Longrightarrow> map (\<lambda>f. f x) fs ! i = \<pi>\<^bsub>S\<^esub> x ! i\<close> nth_equalityI)
    qed
    then show ?thesis using True unfolding restrict_def
      by presburger
    next
    case False
    then show ?thesis unfolding restrict_def
      by (simp add: False)
    qed
  qed
  have 7: " is_semialg_map n k (function_tuple_eval Q\<^sub>p n fs)"
    using 0 semialg_function_tuple_is_semialg_map[of n fs k] assms fs_def  length_map "4" "5" k_size
    by blast
  show ?thesis using 6 7
    using semialg_map_on_carrier k_def
    by blast
qed

lemma tl_is_semialg_map:
  shows "is_semialg_map (Suc n) n tl"
proof-
  have 0: "(card {1..<Suc n}) = n"
  proof-
    have "Suc n - 1 = n"
      using diff_Suc_1 by blast
    then show ?thesis
      by simp
  qed
  have 3: "{1..<Suc n} \<subseteq> {..<Suc n}"
    using atLeastLessThan_iff by blast
  have 4: " is_semialg_map (Suc n) n (project_at_indices {1..<Suc n})"
    using 0 project_at_indices_is_semialg_map
    by (metis "3")
  show ?thesis
    using 0 3 4
        semialg_map_on_carrier[of "Suc n" n "(project_at_indices {1..<Suc n})" tl]
    unfolding restrict_def
    by (metis (no_types, lifting) tl_as_projection)
qed

text\<open>Coordinate functions are semialgebraic maps.\<close>

lemma coord_fun_is_SA:
  assumes "is_semialg_map n m g"
  assumes "i < m"
  shows "coord_fun Q\<^sub>p n g i \<in> carrier (SA n)"
proof(rule SA_car_memI)
  show "coord_fun Q\<^sub>p n g i \<in> carrier (function_ring (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) Q\<^sub>p)"
    apply(rule Qp.function_ring_car_memI)
    unfolding coord_fun_def using assms
     apply (metis (no_types, lifting) Pi_iff cartesian_power_car_memE' is_semialg_map_closed restrict_apply')
      by (meson restrict_apply)
  show "is_semialg_function n (coord_fun Q\<^sub>p n g i)"
  proof-
    have 0: "is_semialg_function m (\<lambda> x. x ! i)"
      using assms gr_implies_not0 index_is_semialg_function by blast
    have 1: "(coord_fun Q\<^sub>p n g i) = restrict ((\<lambda>x.  x ! i) \<circ> g) (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) "
      unfolding coord_fun_def using comp_apply
      by metis
    show ?thesis
      using semialg_function_on_carrier[of n "((\<lambda>x. x ! i) \<circ> g)" "coord_fun Q\<^sub>p n g i"]
             assms semialg_function_comp_closed[of m "\<lambda>x. x ! i" n g] assms 0 1
      unfolding coord_fun_def
      using restrict_is_semialg by presburger
  qed
qed

lemma coord_fun_map_is_semialg_tuple:
  assumes "is_semialg_map n m g"
  shows "is_semialg_function_tuple n (map (coord_fun Q\<^sub>p n g) [0..<m])"
proof(rule is_semialg_function_tupleI)
  have 0: "set [0..<m] = {..<m}"
    using atLeast_upt by blast
  fix f assume A: "f \<in> set (map (coord_fun Q\<^sub>p n g) [0..<m])"
  then obtain i where i_def: "i < m \<and> f = coord_fun Q\<^sub>p n g i"
    using set_map[of "coord_fun Q\<^sub>p n g" "[0..<m]"] 0
    by (metis image_iff lessThan_iff)
  show " is_semialg_function n f"
  using i_def A assms coord_fun_is_SA[of n m g i] SA_imp_semialg by blast
qed

lemma semialg_map_cons:
  assumes "is_semialg_map n m g"
  assumes "f \<in> carrier (SA n)"
  shows "is_semialg_map n (Suc m) (\<lambda> x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). f x # g x)"
proof-
  obtain Fs where Fs_def: "Fs = f # (map (coord_fun Q\<^sub>p n g) [0..<m])"
    by blast
  have 0: "is_semialg_function_tuple n Fs"
    apply(rule  is_semialg_function_tupleI)
    using is_semialg_function_tupleE'[of n "map (coord_fun Q\<^sub>p n g) [0..<m]"]
          coord_fun_map_is_semialg_tuple[of n m g] assms SA_car_memE(1)[of f n]
          set_ConsD[of _ f "map (coord_fun Q\<^sub>p n g) [0..<m]"] assms
    unfolding Fs_def by blast
  have 1: "(\<lambda> x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). f x # g x) = (\<lambda> x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). function_tuple_eval Q\<^sub>p n Fs x)"
  proof(rule ext) fix x show "(\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>n\<^esup>). f x # g x) x = restrict (function_tuple_eval Q\<^sub>p n Fs) (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) x"
    proof(cases "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)")
      case True then have T0: "(\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>n\<^esup>). f x # g x) x = f x # g x"
        by (meson restrict_apply')
      have T1: "restrict (function_tuple_eval Q\<^sub>p n Fs) (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) x = function_tuple_eval Q\<^sub>p n Fs x"
        using True by (meson restrict_apply')
      hence T2: "restrict (function_tuple_eval Q\<^sub>p n Fs) (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) x = f x # (function_tuple_eval Q\<^sub>p n (map (coord_fun Q\<^sub>p n g) [0..<m]) x)"
        unfolding function_tuple_eval_def Fs_def by (metis (no_types, lifting) list.simps(9))
      have T3: "g x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using assms True is_semialg_map_closed by blast
      have "length [0..<m] = m"
        by auto
      hence T4: "length (map (coord_fun Q\<^sub>p n g) [0..<m]) = m"
        using length_map[of "(coord_fun Q\<^sub>p n g)" "[0..<m]"] by metis
      hence T5: "length (function_tuple_eval Q\<^sub>p n (map (coord_fun Q\<^sub>p n g) [0..<m]) x) = m"
        unfolding function_tuple_eval_def using length_map by metis
      have T6: "(function_tuple_eval Q\<^sub>p n (map (coord_fun Q\<^sub>p n g) [0..<m]) x) = g x"
        apply(rule nth_equalityI) using T3 T5
          using cartesian_power_car_memE apply blast
          using cartesian_power_car_memE[of "g x" Q\<^sub>p m]  T5 T4  T3 True
                nth_map[of _ "(map (\<lambda>i. \<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>n\<^esup>). g x ! i) [0..<m])" "(\<lambda>f. f x)"]
                nth_map[of _ "[0..<m]" "(\<lambda>i. \<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>n\<^esup>). g x ! i)"]
          unfolding function_tuple_eval_def  coord_fun_def restrict_def
          by (metis (no_types, lifting) \<open>length [0..<m] = m\<close> map_nth nth_map)
      hence T7: "restrict (function_tuple_eval Q\<^sub>p n Fs) (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) x = f x # g x"
        using T4 T2 by presburger
      thus ?thesis using T0
        by presburger
    next
      case False
      then show ?thesis unfolding restrict_def
        by metis
    qed
  qed
  have 2: "length Fs = Suc m"
    unfolding Fs_def using length_map[of "(coord_fun Q\<^sub>p n g)" "[0..<m]"] length_Cons[of f "map (coord_fun Q\<^sub>p n g) [0..<m]"]
    using length_upt by presburger
  have 3: "is_semialg_map n (Suc m) (\<lambda> x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). function_tuple_eval Q\<^sub>p n Fs x)"
    apply(rule semialg_map_on_carrier[of _ _  "function_tuple_eval Q\<^sub>p n Fs"],
          intro semialg_function_tuple_is_semialg_map[of n Fs "Suc m"] 0 2)
    by auto
  show ?thesis using 1 3
    by presburger
qed

text\<open>Extensional Semialgebraic Maps:\<close>

definition semialg_maps where
"semialg_maps n m \<equiv> {f. is_semialg_map n m f \<and> f \<in> struct_maps (Q\<^sub>p\<^bsup>n\<^esup>) (Q\<^sub>p\<^bsup>m\<^esup>)}"

lemma semialg_mapsE:
  assumes "f \<in> (semialg_maps n m)"
  shows "is_semialg_map n m f"
        "f \<in> struct_maps (Q\<^sub>p\<^bsup>n\<^esup>) (Q\<^sub>p\<^bsup>m\<^esup>)"
        "f \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  using assms unfolding semialg_maps_def apply blast
  using assms unfolding semialg_maps_def apply blast
  apply(rule is_semialg_map_closed)
  using assms unfolding semialg_maps_def by blast

definition to_semialg_map where
"to_semialg_map n m f = restrict f (carrier (Q\<^sub>p\<^bsup>n\<^esup>))"

lemma to_semialg_map_is_semialg_map:
  assumes "is_semialg_map n m f"
  shows "to_semialg_map n m f \<in> semialg_maps n m"
  using assms unfolding to_semialg_map_def semialg_maps_def struct_maps_def mem_Collect_eq
  using is_semialg_map_closed' semialg_map_on_carrier by force

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Application of Functions to Segments of Tuples\<close>
(**************************************************************************************************)
(**************************************************************************************************)


definition take_apply where
"take_apply m n f = restrict (f \<circ> take n) (carrier (Q\<^sub>p\<^bsup>m\<^esup>))"

definition drop_apply where
"drop_apply m n f = restrict (f \<circ> drop n) (carrier (Q\<^sub>p\<^bsup>m\<^esup>))"

lemma take_apply_closed:
  assumes "f \<in> carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
  assumes "k \<ge> n"
  shows "take_apply k n f \<in> carrier (Fun\<^bsub>k\<^esub> Q\<^sub>p)"
proof(rule Qp.function_ring_car_memI)
  show  "\<And>a. a \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<Longrightarrow> take_apply k n f a \<in> carrier Q\<^sub>p"
  proof-  fix a assume A: "a \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)" show "take_apply k n f a \<in> carrier Q\<^sub>p"
      using A assms comp_apply[of f "take n" a] Qp.function_ring_car_memE[of f n] take_closed[of n k a]
      unfolding take_apply_def restrict_def
      by metis
  qed
  show " \<And>a. a \<notin> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<Longrightarrow> take_apply k n f a = undefined"
    unfolding take_apply_def restrict_def
    by meson
qed

lemma take_apply_SA_closed:
  assumes "f \<in> carrier (SA n)"
  assumes "k \<ge> n"
  shows "take_apply k n f \<in> carrier (SA k)"
  apply(rule SA_car_memI)
  using SA_car_memE(2) assms(1) assms(2) take_apply_closed apply blast
  using assms take_is_semialg_map[of n k] unfolding take_apply_def
  by (metis padic_fields.SA_imp_semialg
      padic_fields_axioms restrict_is_semialg semialg_function_comp_closed)

lemma drop_apply_closed:
  assumes "f \<in> carrier (Fun\<^bsub>k - n\<^esub> Q\<^sub>p)"
  assumes "k \<ge> n"
  shows "drop_apply k n f \<in> carrier (Fun\<^bsub>k\<^esub> Q\<^sub>p)"
proof(rule Qp.function_ring_car_memI)
  show  " \<And>a. a \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<Longrightarrow> drop_apply k n f a \<in> carrier Q\<^sub>p"
  proof-  fix a assume A: "a \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)" show "drop_apply k n f a \<in> carrier Q\<^sub>p"
      using A assms comp_apply[of f "drop n" a] Qp.function_ring_car_memE[of f ] drop_closed[of n k a Q\<^sub>p]
      unfolding drop_apply_def restrict_def
      by (metis (no_types, opaque_lifting) Qp.function_ring_car_memE add_diff_cancel_right'
          cartesian_power_drop dec_induct diff_diff_cancel diff_less_Suc diff_less_mono2
          infinite_descent le_neq_implies_less less_antisym linorder_neqE_nat not_less0 not_less_eq_eq)
  qed
  show " \<And>a. a \<notin> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<Longrightarrow> drop_apply k n f a = undefined"
    unfolding drop_apply_def restrict_def
    by meson
qed

lemma drop_apply_SA_closed:
  assumes "f \<in> carrier (SA (k-n))"
  assumes "k \<ge> n"
  shows "drop_apply k n f \<in> carrier (SA k)"
  apply(rule SA_car_memI)
  using SA_car_memE(2) assms(1) assms(2) drop_apply_closed less_imp_le_nat apply blast
  using assms drop_is_semialg_map[of n "k - n" ] semialg_function_comp_closed[of "k - n" f k "drop n"] unfolding drop_apply_def
  by (metis (no_types, lifting) SA_imp_semialg le_add_diff_inverse  restrict_is_semialg)

lemma take_apply_apply:
  assumes "f \<in> carrier (SA n)"
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "b \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
  shows "take_apply (n+k) n f (a@b) = f a"
proof-
  have "a@b \<in> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
    using assms cartesian_power_concat(1) by blast
  thus ?thesis
    unfolding take_apply_def restrict_def
    using assms cartesian_power_car_memE comp_apply[of f "take n"]
    by (metis append_eq_conv_conj)
qed

lemma drop_apply_apply:
  assumes "f \<in> carrier (SA k)"
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "b \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
  shows "drop_apply (n+k) n f (a@b) = f b"
proof-
  have "a@b \<in> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
    using assms cartesian_power_concat(1) by blast
  thus ?thesis
    unfolding drop_apply_def  restrict_def
    using assms cartesian_power_car_memE comp_apply[of f "drop n"]
    by (metis append_eq_conv_conj)
qed

lemma drop_apply_add:
  assumes "f \<in> carrier (SA n)"
  assumes "g \<in> carrier (SA n)"
  shows "drop_apply (n+k) k (f \<oplus>\<^bsub>SA n\<^esub> g) = drop_apply (n+k) k f \<oplus>\<^bsub>SA (n + k)\<^esub> drop_apply (n+k) k g"
  apply(rule function_ring_car_eqI[of _ "n + k"])
  using drop_apply_SA_closed  assms fun_add_closed SA_car_memE(2) SA_plus diff_add_inverse2 drop_apply_closed le_add2 apply presburger
  using drop_apply_SA_closed assms fun_add_closed SA_car_memE(2) SA_plus diff_add_inverse2 drop_apply_closed le_add2 apply presburger
proof-
  fix a  assume A: "a \<in> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
  then obtain  b c where bc_def: "b \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<and> c \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<and> a  =  b@c"
    by (metis (no_types, lifting) add.commute cartesian_power_decomp)
  have 0: "drop_apply (n + k) k (f \<oplus>\<^bsub>SA n\<^esub> g) a = f c \<oplus> g c"
    using assms  bc_def drop_apply_apply[of "f \<oplus>\<^bsub>SA n\<^esub> g" n b k c ]
    by (metis SA_add SA_imp_semialg add.commute padic_fields.SA_add_closed_left padic_fields_axioms)
  then show " drop_apply (n + k) k (f \<oplus>\<^bsub>SA n\<^esub> g) a = (drop_apply (n + k) k f \<oplus>\<^bsub>SA (n + k)\<^esub> drop_apply (n + k) k g) a"
    using bc_def drop_apply_apply assms
    by (metis A SA_add add.commute)
qed

lemma drop_apply_mult:
  assumes "f \<in> carrier (SA n)"
  assumes "g \<in> carrier (SA n)"
  shows "drop_apply (n+k) k (f \<otimes> \<^bsub>SA n\<^esub> g) = drop_apply (n+k) k f \<otimes>\<^bsub>SA (n + k)\<^esub> drop_apply (n+k) k g"
  apply(rule function_ring_car_eqI[of _ "n + k"])
  using drop_apply_SA_closed  assms fun_mult_closed SA_car_memE(2) SA_times diff_add_inverse2 drop_apply_closed le_add2 apply presburger
  using drop_apply_SA_closed assms fun_mult_closed SA_car_memE(2)  SA_times diff_add_inverse2 drop_apply_closed le_add2 apply presburger
proof-
  fix a  assume A: "a \<in> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
  then obtain  b c where bc_def: "b \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<and> c \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<and> a  =  b@c"
    by (metis (no_types, lifting) add.commute cartesian_power_decomp)
  have 0: "drop_apply (n + k) k (f \<otimes>\<^bsub>SA n\<^esub> g) a = f c \<otimes> g c"
    using assms  bc_def drop_apply_apply[of "f \<otimes>\<^bsub>SA n\<^esub> g" n b k c ]
    by (metis SA_imp_semialg SA_mult SA_mult_closed_right add.commute)
  then show " drop_apply (n + k) k (f \<otimes>\<^bsub>SA n\<^esub> g) a = (drop_apply (n + k) k f \<otimes>\<^bsub>SA (n + k)\<^esub> drop_apply (n + k) k g) a"
    using bc_def drop_apply_apply assms by (metis A SA_mult add.commute)
qed

lemma drop_apply_one:
  shows "drop_apply (n+k) k \<one>\<^bsub>SA n\<^esub> = \<one>\<^bsub>SA (n+k)\<^esub>"
  apply(rule function_ring_car_eqI[of _  "n + k"])
  apply (metis function_one_closed SA_one add_diff_cancel_right' drop_apply_closed le_add2)
  using function_one_closed SA_one apply presburger
proof-
  fix a assume A: "a \<in> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
  show "drop_apply (n + k) k \<one>\<^bsub>SA n\<^esub> a = \<one>\<^bsub>SA (n + k)\<^esub> a"
  unfolding drop_apply_def restrict_def
  using  SA_one[of "n+k"] SA_one[of n] comp_apply[of "\<one>\<^bsub>SA n\<^esub>" "drop k" a] drop_closed[of k "n+k" a Q\<^sub>p]
        function_ring_defs(4)
  unfolding function_one_def
  by (metis A function_one_eval add.commute cartesian_power_drop)
qed

lemma drop_apply_is_hom:
  shows "drop_apply (n + k) k \<in> ring_hom (SA n) (SA (n + k))"
  apply(rule ring_hom_memI)
  using drop_apply_SA_closed[of _ "k+n" k]
  apply (metis add.commute add_diff_cancel_left' le_add1)
  using drop_apply_mult apply blast
   using drop_apply_add apply blast
     using drop_apply_one by blast

lemma take_apply_add:
  assumes "f \<in> carrier (SA k)"
  assumes "g \<in> carrier (SA k)"
  shows "take_apply (n+k) k (f \<oplus>\<^bsub>SA k\<^esub> g) = take_apply (n+k) k f \<oplus>\<^bsub>SA (n + k)\<^esub> take_apply (n+k) k g"
  apply(rule function_ring_car_eqI[of _ "n + k"])
  using take_apply_SA_closed  assms fun_add_closed SA_car_memE(2) SA_plus diff_add_inverse2 take_apply_closed le_add2 apply presburger
  using take_apply_SA_closed assms fun_add_closed SA_car_memE(2) SA_plus diff_add_inverse2 take_apply_closed le_add2 apply presburger
proof-
  fix a  assume A: "a \<in> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
  then obtain  b c where bc_def: "b \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<and> c \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<and> a  =  b@c"
    by (metis (no_types, lifting) add.commute cartesian_power_decomp)
  hence 0: "take_apply (n + k) k (f \<oplus>\<^bsub>SA k\<^esub> g) a =  f b \<oplus> g b"
    using assms bc_def take_apply_apply[of "f \<oplus>\<^bsub>SA k\<^esub> g" k b c ]
    by (metis SA_add SA_imp_semialg add.commute padic_fields.SA_add_closed_left padic_fields_axioms)
  then show "take_apply (n + k) k (f \<oplus>\<^bsub>SA k\<^esub> g) a = (take_apply (n + k) k f \<oplus>\<^bsub>SA (n + k)\<^esub> take_apply (n + k) k g) a"
    using bc_def take_apply_apply assms
    by (metis A SA_add add.commute)
qed

lemma take_apply_mult:
  assumes "f \<in> carrier (SA k)"
  assumes "g \<in> carrier (SA k)"
  shows "take_apply (n+k) k (f \<otimes>\<^bsub>SA k\<^esub> g) = take_apply (n+k) k f \<otimes>\<^bsub>SA (n + k)\<^esub> take_apply (n+k) k g"
  apply(rule function_ring_car_eqI[of _ "n + k"])
  using take_apply_SA_closed  assms fun_mult_closed SA_car_memE(2) SA_times diff_add_inverse2 take_apply_closed le_add2 apply presburger
  using take_apply_SA_closed assms fun_mult_closed SA_car_memE(2) SA_times diff_add_inverse2 take_apply_closed le_add2 apply presburger
proof-
  fix a  assume A: "a \<in> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
  then obtain  b c where bc_def: "b \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<and> c \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<and> a  =  b@c"
    by (metis (no_types, lifting) add.commute cartesian_power_decomp)
  hence 0: "take_apply (n + k) k (f \<otimes>\<^bsub>SA k\<^esub> g) a =  f b \<otimes> g b"
    using assms bc_def take_apply_apply[of "f \<otimes>\<^bsub>SA k\<^esub> g" k b c ]
    by (metis SA_mult SA_imp_semialg add.commute padic_fields.SA_mult_closed_left padic_fields_axioms)
  then show "take_apply (n + k) k (f \<otimes>\<^bsub>SA k\<^esub> g) a = (take_apply (n + k) k f \<otimes>\<^bsub>SA (n + k)\<^esub> take_apply (n + k) k g) a"
    using bc_def take_apply_apply assms
    by (metis A SA_mult add.commute)
qed

lemma take_apply_one:
  shows "take_apply (n+k) k \<one>\<^bsub>SA k\<^esub> = \<one>\<^bsub>SA (n+k)\<^esub>"
  apply(rule function_ring_car_eqI[of _  "n + k"])
  using function_one_closed SA_one le_add2 take_apply_closed apply presburger
  using function_one_closed SA_one apply presburger
proof-
  fix a assume A: "a \<in> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
  show "take_apply (n + k) k \<one>\<^bsub>SA k\<^esub> a = \<one>\<^bsub>SA (n + k)\<^esub> a"
  unfolding take_apply_def restrict_def
  using  SA_one[of "n+k"] SA_one[of k] comp_apply[of "\<one>\<^bsub>SA k\<^esub>" "take k" a] take_closed[of k "n + k" a]
        function_ring_defs(4)
  unfolding function_one_def
  using A function_one_eval le_add2 by metis
qed

lemma take_apply_is_hom:
  shows "take_apply (n + k) k \<in> ring_hom (SA k) (SA (n + k))"
  apply(rule ring_hom_memI)
  using take_apply_SA_closed[of _ k "n+k"]  le_add2 apply blast
  using   take_apply_mult apply blast
   using   take_apply_add apply blast
     using   take_apply_one by blast

lemma drop_apply_units:
  assumes "f \<in> Units (SA n)"
  shows "drop_apply (n+k) k f \<in> Units (SA (n+k))"
  apply(rule SA_Units_memI)
  using drop_apply_SA_closed[of f "n+k" k ] assms SA_Units_closed
  apply (metis add_diff_cancel_right' le_add2)
proof-
  show "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>n + k\<^esup>) \<Longrightarrow> drop_apply (n + k) k f x \<noteq> \<zero>"
  proof- fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
    then have "drop_apply (n + k) k f x = f (drop k x)"
      unfolding drop_apply_def restrict_def by (meson comp_def)
    then show "drop_apply (n + k) k f x \<noteq> \<zero>"
      using SA_Units_memE'[of f n "drop k x"]
      by (metis A add.commute assms  cartesian_power_drop)
  qed
qed

lemma take_apply_units:
  assumes "f \<in> Units (SA k)"
  shows "take_apply (n+k) k f \<in> Units (SA (n+k))"
  apply(rule SA_Units_memI)
  using take_apply_SA_closed[of f k "n+k" ] assms SA_Units_closed le_add2 apply blast
proof-
  show "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>n + k\<^esup>) \<Longrightarrow> take_apply (n + k) k f x \<noteq> \<zero>"
  proof- fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
    then have "take_apply (n + k) k f x = f (take k x)"
      unfolding take_apply_def restrict_def by (meson comp_def)
    then show "take_apply (n + k) k f x \<noteq> \<zero>"
      using SA_Units_memE'[of f k "take k x"]  A assms le_add2 local.take_closed by blast
  qed
qed


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Level Sets of Semialgebraic Functions\<close>
(**************************************************************************************************)
(**************************************************************************************************)


lemma evimage_is_semialg:
  assumes "h \<in> carrier (SA n)"
  assumes "is_univ_semialgebraic S"
  shows "is_semialgebraic n (h  \<inverse>\<^bsub>n\<^esub> S)"
proof-
  have 0: "is_semialgebraic 1 (to_R1 ` S)"
    using assms is_univ_semialgebraicE by blast
  have 1: "h  \<inverse>\<^bsub>n\<^esub> S = partial_pullback n h (0::nat) (to_R1 ` S)"
  proof show "h \<inverse>\<^bsub>n\<^esub> S \<subseteq> partial_pullback n h 0 ((\<lambda>a. [a]) ` S)"
    proof fix x assume A: "x \<in> h \<inverse>\<^bsub>n\<^esub> S"
      then have 0: "h x \<in> S" by blast
      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
        by (meson A evimage_eq)
      have 1: "drop n x = []"
        using cartesian_power_car_memE[of x Q\<^sub>p n] drop_all x_closed
        by blast
      have 2: "take n x = x"
        using cartesian_power_car_memE[of x Q\<^sub>p n] x_closed take_all
        by blast
      then show "x \<in> partial_pullback n h 0 ((\<lambda>a. [a]) ` S)"
        unfolding partial_pullback_def partial_image_def evimage_def
        using 0 1 2 x_closed
        by (metis (no_types, lifting) IntI Nat.add_0_right image_iff vimageI)
    qed
    show "partial_pullback n h 0 ((\<lambda>a. [a]) ` S) \<subseteq> h \<inverse>\<^bsub>n\<^esub> S"
    proof fix x assume A: "x \<in> partial_pullback n h 0 ((\<lambda>a. [a]) ` S)"
      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
        using A unfolding partial_pullback_def evimage_def
        by (metis A Nat.add_0_right partial_pullback_memE(1))
      then have "(partial_image n h) x = [h x]"
        unfolding partial_image_def
        by (metis (no_types, opaque_lifting) One_nat_def Qp.zero_closed append.right_neutral append_Nil
            local.partial_image_def partial_image_eq segment_in_car' Qp.to_R1_closed)
      then have "h x \<in> S"
        using A unfolding partial_pullback_def
        by (metis (no_types, lifting) A image_iff partial_pullback_memE(2) Qp.to_R_to_R1)
      thus "x \<in> h \<inverse>\<^bsub>n\<^esub> S"
        using x_closed by blast
    qed
  qed
  then show ?thesis
    using 0 is_semialg_functionE[of n h 0 "((\<lambda>a. [a]) ` S)"] assms SA_car_memE(1)[of h n]
    by (metis Nat.add_0_right SA_car)
qed

lemma semialg_val_ineq_set_is_semialg:
  assumes "g \<in> carrier (SA k)"
  assumes "f \<in> carrier (SA k)"
  shows "is_semialgebraic k {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (g x) \<le> val (f x)}"
proof-
  obtain F where F_def: "F = function_tuple_eval Q\<^sub>p  k [f, g]"
    by blast
  have P0: "is_semialg_function_tuple k [f, g] "
    using is_semialg_function_tupleI[of "[f, g]" k]
    by (metis assms  list.distinct(1) list.set_cases padic_fields.SA_imp_semialg padic_fields_axioms set_ConsD)
  hence P1: "is_semialg_map k 2 F"
    using  assms semialg_function_tuple_is_semialg_map[of k "[f, g]" 2]
    unfolding F_def by (simp add: \<open>f \<in> carrier (SA k)\<close> \<open>g \<in> carrier (SA k)\<close>)
  have "{x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (g x) \<le> val (f x)} = F  \<inverse>\<^bsub>k\<^esub> val_relation_set"
  proof
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (g x) \<le> val (f x)} \<subseteq> F \<inverse>\<^bsub>k\<^esub> val_relation_set"
    proof fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (g x) \<le> val (f x)}"
      then have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<and> val (g x) \<le> val (f x)" by blast
      have 1: "F x = [f x, g x]"
        unfolding F_def using A unfolding function_tuple_eval_def
        by (metis (no_types, lifting) list.simps(8) map_eq_Cons_conv)
      have 2: "val (g x) \<le> val (f x)"
        using A
        by blast
      have 3: "F x \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>)"
        using assms A 1
        by (metis (no_types, lifting) "0" Qp.function_ring_car_mem_closed Qp_2I SA_car_memE(2))
      then have 4: "x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<and> F x \<in> val_relation_set"
        unfolding val_relation_set_def F_def using 0 1 2 3
        by (metis (no_types, lifting) cartesian_power_car_memE cartesian_power_car_memE'
            list.inject local.F_def one_less_numeral_iff pair_id semiring_norm(76) val_relation_setI
            val_relation_set_def zero_less_numeral)
      then show "x \<in> F \<inverse>\<^bsub>k\<^esub> val_relation_set"
        by blast
    qed
    show "F \<inverse>\<^bsub>k\<^esub> val_relation_set \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (g x) \<le> val (f x)}"
    proof fix x assume A: "x \<in> F \<inverse>\<^bsub>k\<^esub> val_relation_set"
      then have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<and> F x \<in> val_relation_set"
        by (meson evimage_eq)
      then have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<and> [f x, g x] \<in> val_relation_set"
        unfolding F_def function_tuple_eval_def
        by (metis (no_types, lifting) list.simps(8) list.simps(9))
      then have "x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<and> val (g x) \<le> val (f x)"
        unfolding F_def val_relation_set_def
        by (metis (no_types, lifting) "0" list.inject val_relation_setE)
      then show "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (g x) \<le> val (f x)}"
        by blast
    qed
  qed
  then show ?thesis
    using assms P0 P1 val_relation_is_semialgebraic semialg_map_evimage_is_semialg[of k 2 F val_relation_set] pos2
    by presburger
qed

lemma semialg_val_ineq_set_is_semialg':
  assumes "f \<in> carrier (SA k)"
  shows "is_semialgebraic k {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) \<le> C}"
proof-
  obtain a where a_def: "a \<in> carrier Q\<^sub>p \<and> val a = C"
    by (meson Qp.carrier_not_empty Qp.minus_closed dist_nonempty' equals0I)
  then obtain g where g_def: "g = constant_function (carrier (Q\<^sub>p\<^bsup>k\<^esup>)) a"
    by blast
  have 0: "g \<in> carrier (SA k)"
    using g_def a_def SA_car assms(1) constant_function_in_semialg_functions by blast
  have 1: "{x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) \<le> C} = {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) \<le> val (g x)}"
    using g_def by (metis (no_types, lifting) Qp_constE a_def)
  then show ?thesis using assms 0 semialg_val_ineq_set_is_semialg[of f k g]
    by presburger
qed

lemma semialg_val_ineq_set_is_semialg'':
  assumes "f \<in> carrier (SA k)"
  shows "is_semialgebraic k {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) \<ge> C}"
proof-
  obtain a where a_def: "a \<in> carrier Q\<^sub>p \<and> val a = C"
    by (meson Qp.carrier_not_empty Qp.minus_closed dist_nonempty' equals0I)
  then obtain g where g_def: "g = constant_function (carrier (Q\<^sub>p\<^bsup>k\<^esup>)) a"
    by blast
  have 0: "g \<in> carrier (SA k)"
    using g_def a_def SA_car assms(1) constant_function_in_semialg_functions by blast
  have 1: "{x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) \<ge> C} = {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) \<ge> val (g x)}"
    using g_def by (metis (no_types, lifting) Qp_constE a_def)
  then show ?thesis using assms 0 semialg_val_ineq_set_is_semialg[of g k f]
    by presburger
qed

lemma semialg_level_set_is_semialg:
  assumes "f \<in> carrier (SA k)"
  assumes "c \<in> carrier Q\<^sub>p"
  shows "is_semialgebraic k {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). f x = c}"
proof-
  have 0: "is_univ_semialgebraic {c}"
    apply(rule finite_is_univ_semialgebraic) using assms apply blast by auto
  have 1: "{x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). f x = c} = f  \<inverse>\<^bsub>k\<^esub> {c}"
    unfolding evimage_def by auto
  then show ?thesis using 0 assms evimage_is_semialg by presburger
qed

lemma semialg_val_eq_set_is_semialg':
  assumes "f \<in> carrier (SA k)"
  shows "is_semialgebraic k {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) = C}"
proof(cases "C = \<infinity>")
  case True
  then have "{x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) = C} = {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). f x = \<zero>}"
    using assms unfolding val_def by (meson eint.distinct(1))
  then have "{x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) = C} = f  \<inverse>\<^bsub>k\<^esub> {\<zero>}"
    unfolding evimage_def by blast
  then show ?thesis
    using assms semialg_level_set_is_semialg[of f k \<zero>]  Qp.zero_closed \<open>{x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) = C} = {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). f x = \<zero>}\<close> by presburger
next
  case False
  then obtain N::int where N_def: "C = eint N"
    by blast
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) = C} = {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) \<le> N} - {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) \<le> (eint (N-1))}"
  proof
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) = C} \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) \<le> N} - {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) \<le> (eint (N-1))}"
    proof
      fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) = C}"
      then have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<and> val (f x) = C"
        by blast
      have 1: "\<not> val (f x) \<le> (eint (N-1))"
        using A N_def assms 0 eint_ord_simps(1) by presburger
      have 2: "val (f x) \<le> (eint N)"
        using 0 N_def eint_ord_simps(1) by presburger
      show "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) \<le> N} - {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) \<le> (eint (N-1))}"
        using 0 1 2
        by blast
    qed
    show  "{x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) \<le> N} - {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) \<le> (eint (N-1))} \<subseteq>  {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) = C}"
    proof fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) \<le> N} - {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) \<le> (eint (N-1))}"
      have 0:  "x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<and> val (f x) \<le> C"
        using A N_def by blast
      have 1: "\<not> val (f x) \<le> (eint (N-1))"
        using A 0  by blast
      have 2: "val (f x) = C"
      proof(rule ccontr)
        assume "val (f x) \<noteq> C"
        then have "val (f x) < C"
          using 0 by auto
        then obtain M where M_def: "val (f x) = eint M"
          using N_def eint_iless by blast
        then have "M < N"
          by (metis N_def \<open>val (f x) < C\<close> eint_ord_simps(2))
        then have "val (f x) \<le> eint (N - 1)"
          using M_def eint_ord_simps(1) by presburger
        then show False using 1 by blast
      qed
      show "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) = C} "
        using 0 2  by blast
    qed
  qed
  have 1: "is_semialgebraic k {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) \<le> N}"
    using assms semialg_val_ineq_set_is_semialg'[of f k N] by blast
  have 2: "is_semialgebraic k {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) \<le> (eint (N-1))}"
    using assms semialg_val_ineq_set_is_semialg' by blast
  show ?thesis using 0 1 2
    using diff_is_semialgebraic by presburger
qed

lemma semialg_val_eq_set_is_semialg:
  assumes "g \<in> carrier (SA k)"
  assumes "f \<in> carrier (SA k)"
  shows "is_semialgebraic k {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (g x) = val (f x)}"
proof-
  have 0: "is_semialgebraic k {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (g x) \<le> val (f x)}"
    using assms semialg_val_ineq_set_is_semialg[of g k f] by blast
  have 1: "is_semialgebraic k {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (g x) \<ge> val (f x)}"
    using assms semialg_val_ineq_set_is_semialg[of f k g] by blast
  have 2: " {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (g x) = val (f x)} =  {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (g x) \<le> val (f x)} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (g x) \<ge> val (f x)}"
    using eq_iff by blast
  show ?thesis using 0 1 2 intersection_is_semialg by presburger
qed

lemma semialg_val_strict_ineq_set_formula:
"{x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (g x) < val (f x)} = {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (g x) \<le> val (f x)} - {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (g x) = val (f x)}"
  using neq_iff le_less by blast

lemma semialg_val_ineq_set_complement:
"carrier (Q\<^sub>p\<^bsup>k\<^esup>) - {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (g x) \<le> val (f x)} = {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) < val (g x)}"
  using not_le by blast

lemma semialg_val_strict_ineq_set_complement:
"carrier (Q\<^sub>p\<^bsup>k\<^esup>) - {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (g x) < val (f x)} = {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) \<le> val (g x)}"
  using not_le by blast

lemma semialg_val_strict_ineq_set_is_semialg:
  assumes "g \<in> carrier (SA k)"
  assumes "f \<in> carrier (SA k)"
  shows "is_semialgebraic k {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (g x) < val (f x)}"
  using semialg_val_ineq_set_complement[of k f g] assms diff_is_semialgebraic
        semialg_val_ineq_set_is_semialg[of f ]
  by (metis (no_types, lifting) complement_is_semialg)

lemma semialg_val_strict_ineq_set_is_semialg':
  assumes "f \<in> carrier (SA k)"
  shows "is_semialgebraic k {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) < C}"
proof-
  obtain a where a_def: "a \<in> carrier Q\<^sub>p \<and> val a = C"
    by (meson Qp.carrier_not_empty Qp.minus_closed dist_nonempty' equals0I)
  then obtain g where g_def: "g = constant_function (carrier (Q\<^sub>p\<^bsup>k\<^esup>)) a"
    by blast
  have 0: "g \<in> carrier (SA k)"
    using g_def a_def SA_car assms(1) constant_function_in_semialg_functions by blast
  have 1: "{x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) < C} = {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) < val (g x)}"
    using g_def by (metis (no_types, lifting) Qp_constE a_def)
  then show ?thesis using assms 0 semialg_val_strict_ineq_set_is_semialg[of f k g]
    by presburger
qed

lemma semialg_val_strict_ineq_set_is_semialg'':
  assumes "f \<in> carrier (SA k)"
  shows "is_semialgebraic k {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) > C}"
proof-
  obtain a where a_def: "a \<in> carrier Q\<^sub>p \<and> val a = C"
    by (meson Qp.carrier_not_empty Qp.minus_closed dist_nonempty' equals0I)
  then obtain g where g_def: "g = constant_function (carrier (Q\<^sub>p\<^bsup>k\<^esup>)) a"
    by blast
  have 0: "g \<in> carrier (SA k)"
    using g_def a_def SA_car assms(1) constant_function_in_semialg_functions by blast
  have 1: "{x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) > C} = {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). val (f x) > val (g x)}"
    using g_def by (metis (no_types, lifting) Qp_constE a_def)
  then show ?thesis using assms 0 semialg_val_strict_ineq_set_is_semialg[of g k f]
    by presburger
qed

lemma semialg_val_ineq_set_plus:
  assumes "N > 0"
  assumes "c \<in> carrier (SA N)"
  assumes "a \<in> carrier (SA N)"
  shows "is_semialgebraic N  {x \<in> carrier (Q\<^sub>p\<^bsup>N\<^esup>). val (c x) \<le> val (a x) + eint n}"
proof-
  obtain b where b_def: "b = \<pp>[^]n \<odot>\<^bsub>SA N\<^esub> a"
    by blast
  have b_closed: "b \<in> carrier (SA N)"
    unfolding b_def using assms SA_smult_closed p_intpow_closed(1) by blast
  have "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>N\<^esup>) \<Longrightarrow> val (b x) = val (a x) + eint n"
    unfolding b_def by (metis Qp.function_ring_car_memE SA_car_memE(2) SA_smult_formula assms(3) p_intpow_closed(1) times_p_pow_val)
  hence 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>N\<^esup>). val (c x) \<le> val (a x) + eint n} = {x \<in> carrier (Q\<^sub>p\<^bsup>N\<^esup>). val (c x) \<le> val (b x)}"
    by (metis (no_types, opaque_lifting) add.commute)
  show ?thesis unfolding 0 using assms b_def b_closed semialg_val_ineq_set_is_semialg[of c N b]  by blast
qed

lemma semialg_val_eq_set_plus:
  assumes "N > 0"
  assumes "c \<in> carrier (SA N)"
  assumes "a \<in> carrier (SA N)"
  shows "is_semialgebraic N  {x \<in> carrier (Q\<^sub>p\<^bsup>N\<^esup>). val (c x) = val (a x) + eint n}"
proof-
  obtain b where b_def: "b = \<pp>[^]n \<odot>\<^bsub>SA N\<^esub> a"
    by blast
  have b_closed: "b \<in> carrier (SA N)"
    unfolding b_def using assms SA_smult_closed p_intpow_closed(1) by blast
  have "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>N\<^esup>) \<Longrightarrow> val (b x) = val (a x) + eint n"
    unfolding b_def by (metis Qp.function_ring_car_memE SA_car_memE(2) SA_smult_formula assms(3) p_intpow_closed(1) times_p_pow_val)
  hence 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>N\<^esup>). val (c x) = val (a x) + eint n} = {x \<in> carrier (Q\<^sub>p\<^bsup>N\<^esup>). val (c x) = val (b x)}"
    by (metis (no_types, opaque_lifting) add.commute)
  show ?thesis unfolding 0 using assms b_def b_closed semialg_val_eq_set_is_semialg[of c N b]  by blast
qed

definition SA_zero_set where
"SA_zero_set n f = {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). f x = \<zero>}"

lemma SA_zero_set_is_semialgebraic:
  assumes "f \<in> carrier (SA n)"
  shows "is_semialgebraic n (SA_zero_set n f)"
  using assms semialg_level_set_is_semialg[of f n \<zero>] unfolding SA_zero_set_def
  by blast

lemma SA_zero_set_memE:
  assumes "f \<in> carrier (SA n)"
  assumes "x \<in> SA_zero_set n f"
  shows "f x = \<zero>"
  using assms unfolding SA_zero_set_def by blast

lemma SA_zero_set_memI:
  assumes "f \<in> carrier (SA n)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f x = \<zero>"
  shows  "x \<in> SA_zero_set n f"
  using assms unfolding SA_zero_set_def by blast

lemma SA_zero_set_of_zero:
"SA_zero_set m (\<zero>\<^bsub>SA m\<^esub>) = carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  apply(rule equalityI')
  unfolding SA_zero_set_def mem_Collect_eq
  apply blast
  using SA_zeroE by blast

definition SA_nonzero_set where
"SA_nonzero_set n f = {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). f x \<noteq> \<zero>}"

lemma nonzero_evimage_closed:
  assumes "f \<in> carrier (SA n)"
  shows "is_semialgebraic n {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). f x \<noteq> \<zero>}"
proof-
  have "{x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). f x \<noteq> \<zero>} = f  \<inverse>\<^bsub>n\<^esub> nonzero Q\<^sub>p"
    unfolding nonzero_def evimage_def using SA_car_memE[of f n] assms by blast
  thus ?thesis   using assms evimage_is_semialg[of f n "nonzero Q\<^sub>p"] nonzero_is_univ_semialgebraic
    by presburger
qed

lemma SA_nonzero_set_is_semialgebraic:
  assumes "f \<in> carrier (SA n)"
  shows "is_semialgebraic n (SA_nonzero_set n f)"
  using assms semialg_level_set_is_semialg[of f n \<zero>] unfolding SA_nonzero_set_def
  using nonzero_evimage_closed by blast

lemma SA_nonzero_set_memE:
  assumes "f \<in> carrier (SA n)"
  assumes "x \<in> SA_nonzero_set n f"
  shows "f x \<noteq> \<zero>"
  using assms unfolding SA_nonzero_set_def by blast

lemma SA_nonzero_set_memI:
  assumes "f \<in> carrier (SA n)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f x \<noteq>  \<zero>"
  shows  "x \<in> SA_nonzero_set n f"
  using assms unfolding SA_nonzero_set_def
  by blast

lemma SA_nonzero_set_of_zero:
"SA_nonzero_set m (\<zero>\<^bsub>SA m\<^esub>) = {}"
  apply(rule equalityI')
  unfolding SA_nonzero_set_def mem_Collect_eq
  using SA_zeroE apply blast
  by blast

lemma SA_car_memI':
  assumes "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> f x \<in> carrier Q\<^sub>p"
  assumes "\<And>x. x \<notin> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> f x = undefined"
  assumes "\<And>k n P. n > 0 \<Longrightarrow> P \<in> carrier (Q\<^sub>p [\<X>\<^bsub>1 + k\<^esub>]) \<Longrightarrow> is_semialgebraic (m + k) (partial_pullback m f k (basic_semialg_set (1 + k) n P))"
  shows "f \<in> carrier (SA m)"
  apply(rule SA_car_memI)
   apply(rule Qp.function_ring_car_memI)
  using assms(1) apply blast using assms(2) apply blast
  apply(rule is_semialg_functionI')
  using assms(1) apply blast
  using assms(3) unfolding is_basic_semialg_def
  by blast

lemma(in padic_fields) SA_zero_set_is_semialg:
  assumes "a \<in> carrier (SA m)"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). a x = \<zero>}"
  using assms semialg_level_set_is_semialg[of a m \<zero>] Qp.zero_closed by blast

lemma(in padic_fields) SA_nonzero_set_is_semialg:
  assumes "a \<in> carrier (SA m)"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). a x \<noteq> \<zero>}"
proof-
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). a x \<noteq> \<zero>} = carrier (Q\<^sub>p\<^bsup>m\<^esup>) - {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). a x = \<zero>}"
    by blast
  show ?thesis using assms  SA_zero_set_is_semialg[of a m] complement_is_semialg[of m "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). a x = \<zero>}"]
    unfolding 0  by blast
qed

lemma zero_set_nonzero_set_covers:
"carrier (Q\<^sub>p\<^bsup>n\<^esup>) = SA_zero_set n f \<union> SA_nonzero_set n f"
  unfolding SA_zero_set_def SA_nonzero_set_def
  apply(rule equalityI')
  unfolding mem_Collect_eq
  apply blast
  by blast

lemma zero_set_nonzero_set_covers':
  assumes "S \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "S = (S \<inter> SA_zero_set n f) \<union> (S \<inter> SA_nonzero_set n f)"
  using assms zero_set_nonzero_set_covers by blast

lemma zero_set_nonzero_set_covers_semialg_set:
  assumes "is_semialgebraic n S"
  shows "S = (S \<inter> SA_zero_set n f) \<union> (S \<inter> SA_nonzero_set n f)"
  using assms is_semialgebraic_closed zero_set_nonzero_set_covers' by blast


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Partitioning Semialgebraic Sets According to Valuations of Functions\<close>
(**************************************************************************************************)
(**************************************************************************************************)


text\<open>
  Given a semialgebraic set $A$ and a finite set of semialgebraic functions $Fs$, a common
  construction is to simplify one's understanding of the behaviour of the functions $\mathit{Fs}$ on
  $A$ by finitely paritioning $A$ into subsets where the element $f \in F$ for which $val (f x)$ is
  minimal is constant as $x$ ranges over each piece of the parititon. The function
  \texttt{Min\_set} helps construct this by picking out the subset of a set $A$ where the valuation
  of a particular element of $\mathit{Fs}$ is minimal. Such a set will always be semialgebraic.
\<close>

lemma disjointify_semialg:
  assumes "finite As"
  assumes "As \<subseteq> semialg_sets n"
  shows "disjointify As \<subseteq> semialg_sets n"
  using assms unfolding semialg_sets_def
  by (simp add: disjointify_gen_boolean_algebra)

lemma semialgebraic_subalgebra:
  assumes "finite Xs"
  assumes "Xs \<subseteq> semialg_sets n"
  shows "atoms_of Xs \<subseteq> semialg_sets n"
  using assms unfolding semialg_sets_def
  by (simp add: atoms_of_gen_boolean_algebra)

lemma(in padic_fields) finite_intersection_is_semialg:
  assumes "finite  Xs"
  assumes "Xs \<noteq> {}"
  assumes "F ` Xs \<subseteq> semialg_sets m"
  shows "is_semialgebraic m (\<Inter> i \<in> Xs. F i)"
proof-
  have 0: "F ` Xs \<subseteq> semialg_sets m \<and> F ` Xs \<noteq> {} "
    using assms by blast
  thus ?thesis
    using assms finite_intersection_is_semialgebraic[of "F ` Xs" m]
    by blast
qed


definition Min_set where
"Min_set m As a = carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<inter> (\<Inter> f \<in> As. {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (a x) \<le> val (f x) })"

lemma Min_set_memE:
  assumes "x \<in> Min_set m As a"
  assumes "f \<in> As"
  shows "val (a x) \<le> val (f x)"
  using assms unfolding Min_set_def by blast

lemma Min_set_closed:
"Min_set m As a \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  unfolding Min_set_def by blast

lemma Min_set_semialg0:
  assumes "As \<subseteq> carrier (SA m)"
  assumes "finite As"
  assumes "a \<in> As"
  assumes "As \<noteq> {}"
  shows "is_semialgebraic m (Min_set m As a)"
  unfolding Min_set_def apply(rule intersection_is_semialg)
  using carrier_is_semialgebraic apply blast
  apply(rule finite_intersection_is_semialg)
  using assms apply blast
  using assms apply blast
proof(rule subsetI) fix x assume A: " x \<in> (\<lambda>i. {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (a x) \<le> val (i x)}) ` As"
  then obtain f where f_def: "f \<in> As \<and> x = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (a x) \<le> val (f x)}"
    by blast
  have f_closed: "f \<in> carrier (SA m)"
    using f_def assms by blast
  have a_closed: "a \<in> carrier (SA m)"
    using assms by blast
  have "is_semialgebraic m  {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (a x) \<le> val (f x)}"
    using a_closed f_closed semialg_val_ineq_set_is_semialg by blast
  thus " x \<in> semialg_sets m"
    using f_def unfolding is_semialgebraic_def by blast
qed

lemma Min_set_semialg:
  assumes "As \<subseteq> carrier (SA m)"
  assumes "finite As"
  assumes "a \<in> As"
  shows "is_semialgebraic m (Min_set m As a)"
  apply(cases "As = {}")
  using Min_set_def  assms(3) apply blast
  using assms Min_set_semialg0 by blast

lemma Min_sets_cover:
  assumes "As \<noteq> {}"
  assumes "finite As"
  shows "carrier (Q\<^sub>p\<^bsup>m\<^esup>) = (\<Union> a \<in> As. Min_set m As a)"
proof
  show "carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<subseteq> \<Union> (Min_set m As ` As)"
  proof fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) "
    obtain v where v_def: "v = Min ((\<lambda>f. val (f x)) ` As)"
      by blast
    obtain f where f_def: "f \<in> As \<and> v = val (f x)"
      unfolding v_def using assms Min_in[of "((\<lambda>f. val (f x)) ` As)"]
      by blast
    have v_def': "v = val (f x)"
      using f_def by blast
    have 0: "x \<in> Min_set m As f"
      unfolding Min_set_def
      apply(rule IntI)
      using A apply blast
    proof(rule InterI) fix s assume s: "s \<in> (\<lambda>fa. {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (f x) \<le> val (fa x)}) ` As"
      then obtain g where g_def: "g \<in> As \<and> s=  {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (f x) \<le> val (g x)}"
        by blast
      have s_def: "s=  {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (f x) \<le> val (g x)}"
        using g_def by blast
      have 00: " val (g x) \<in> ((\<lambda>f. val (f x)) ` As)"
        using g_def by blast
      show "x \<in> s"
        unfolding s_def mem_Collect_eq using 00 A assms  MinE[of "((\<lambda>f. val (f x)) ` As)" v "val (g x)"]
        unfolding v_def  by (metis f_def finite_imageI v_def)
    qed
    thus "x \<in> \<Union> (Min_set m As ` As)"
      using f_def by blast
  qed
  show "\<Union> (Min_set m As ` As) \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    unfolding Min_set_def by blast
qed

text\<open>
  The sets defined by the function \texttt{Min\_set} for a fixed set of functions may not all be
   disjoint, but we can easily refine then to obtain a finite partition via the function
  "disjointify".
\<close>

definition Min_set_partition where
"Min_set_partition m As B = disjointify ((\<inter>)B  ` (Min_set m As ` As))"

lemma Min_set_partition_finite:
  assumes "finite As"
  shows "finite (Min_set_partition m As B)"
  unfolding Min_set_partition_def
  by (meson assms disjointify_finite finite_imageI)

lemma Min_set_partition_semialg0:
  assumes "finite As"
  assumes "As \<subseteq> carrier (SA m)"
  assumes "is_semialgebraic m B"
  assumes "S \<in> ((\<inter>)B  ` (Min_set m As ` As))"
  shows "is_semialgebraic m S"
  using Min_set_semialg[of As m] assms intersection_is_semialg[of m B]
  by blast

lemma Min_set_partition_semialg:
  assumes "finite As"
  assumes "As \<subseteq> carrier (SA m)"
  assumes "is_semialgebraic m B"
  assumes "S \<in> (Min_set_partition m As B)"
  shows "is_semialgebraic m S"
proof-
  have 0: "(\<inter>) B ` Min_set m As ` As \<subseteq> semialg_sets m "
    apply(rule subsetI)
    using Min_set_partition_semialg0[of As m B ] assms unfolding is_semialgebraic_def
    by blast
  thus ?thesis
  unfolding is_semialgebraic_def
  using assms  Min_set_partition_semialg0[of As m B] disjointify_semialg[of "((\<inter>) B ` Min_set m As ` As)" m]
  unfolding Min_set_partition_def  is_semialgebraic_def by blast
qed

lemma Min_set_partition_covers0:
  assumes "finite As"
  assumes "As \<noteq> {}"
  assumes "As \<subseteq> carrier (SA m)"
  assumes "is_semialgebraic m B"
  shows "\<Union> ((\<inter>)B  ` (Min_set m As ` As)) = B"
proof-
  have 0: "\<Union> ((\<inter>)B  ` (Min_set m As ` As)) = B \<inter> \<Union> (Min_set m As ` As)"
    by blast
  have 1: "B \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms is_semialgebraic_closed by blast
  show ?thesis unfolding 0 using 1 assms Min_sets_cover[of As m]  by blast
qed

lemma Min_set_partition_covers:
  assumes "finite As"
  assumes "As \<subseteq> carrier (SA m)"
  assumes "As \<noteq> {}"
  assumes "is_semialgebraic m B"
  shows "\<Union> (Min_set_partition m As B)  = B"
  unfolding Min_set_partition_def
  using Min_set_partition_covers0[of As m B] assms disjointify_union[of "((\<inter>) B ` Min_set m As ` As)"]
  by (metis finite_imageI)

lemma Min_set_partition_disjoint:
  assumes "finite As"
  assumes "As \<subseteq> carrier (SA m)"
  assumes "As \<noteq> {}"
  assumes "is_semialgebraic m B"
  assumes "s \<in> Min_set_partition m As B"
  assumes "s' \<in> Min_set_partition m As B"
  assumes "s \<noteq>  s'"
  shows  "s \<inter> s' = {}"
  apply(rule  disjointify_is_disjoint[of "((\<inter>) B ` Min_set m As ` As)" s s'])
  using assms finite_imageI apply blast
  using assms unfolding Min_set_partition_def apply blast
  using assms unfolding Min_set_partition_def apply blast
  using assms by blast

lemma Min_set_partition_memE:
  assumes "finite As"
  assumes "As \<subseteq> carrier (SA m)"
  assumes "As \<noteq> {}"
  assumes "is_semialgebraic m B"
  assumes "s \<in> Min_set_partition m As B"
  shows "\<exists>f \<in> As. (\<forall>x \<in> s. (\<forall>g \<in> As. val (f x) \<le> val (g x)))"
proof-
  obtain s' where s'_def: "s' \<in> ((\<inter>) B ` Min_set m As ` As) \<and> s \<subseteq>  s'"
    using finite_imageI assms disjointify_subset[of "((\<inter>) B ` Min_set m As ` As)" s] unfolding Min_set_partition_def  by blast
  obtain f where f_def: "f \<in> As \<and> s' = B \<inter> Min_set m As f"
    using s'_def by blast
  have 0: "(\<forall>x \<in> s'. (\<forall>g \<in> As. val (f x) \<le> val (g x)))"
    using f_def Min_set_memE[of _ m As f] by blast
  thus ?thesis
    using s'_def  by (meson f_def subset_iff)
qed


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Valuative Congruence Sets for Semialgebraic Functions\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>
  The set of points $x$ where the values $\mathit{ord}\ f(x)$ satisfy a congruence are important
  basic examples of semialgebraic sets, and will be vital in the proof of Macintyre's Theorem. The
  lemma below is essentially the content of Denef's Lemma 2.1.3 from his cell decomposition paper.
\<close>

lemma pre_SA_unit_cong_set_is_semialg:
  assumes "k \<ge> 0"
  assumes "f \<in> Units (SA n)"
  shows "is_semialgebraic n {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). ord (f x) mod k  = a }"
proof-
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). ord (f x) mod k  = a } = f  \<inverse>\<^bsub>n\<^esub> ord_congruence_set k a"
    unfolding ord_congruence_set_def
    apply(rule equalityI')
    using assms unfolding evimage_def vimage_def mem_Collect_eq
    apply (metis (mono_tags, lifting) IntI Qp.function_ring_car_memE SA_Units_closed SA_Units_memE' SA_car_memE(2) mem_Collect_eq not_nonzero_Qp)
    using assms by blast
  show ?thesis unfolding 0
    apply(rule evimage_is_semialg)
    using assms  apply blast
    using  assms ord_congruence_set_univ_semialg[of k a]
    by blast
qed

lemma SA_unit_cong_set_is_semialg:
  assumes "f \<in> Units (SA n)"
  shows "is_semialgebraic n {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). ord (f x) mod k = a}"
proof(cases "k \<ge> 0")
  case True
  then show ?thesis
    using assms pre_SA_unit_cong_set_is_semialg by presburger
next
  case False
  show ?thesis
  proof(cases "a = 0")
    case True
    have T0: "{x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). ord (f x) mod k  = a } = {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). ord (f x) mod (-k)  = a }"
      apply(rule equalityI')
      unfolding mem_Collect_eq using True zmod_zminus2_not_zero  apply meson
      using True zmod_zminus2_not_zero
      by (metis equation_minus_iff)
    show ?thesis unfolding T0 apply(rule pre_SA_unit_cong_set_is_semialg[of "-k" f n a])
      using False apply presburger using assms by blast
  next
    case F: False
    show ?thesis
    proof(cases "a = k")
      case True
      have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). ord (f x) mod k = a} = {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). ord (f x) mod k = k}"
        using True by blast
      have 1: "{x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). ord (f x) mod k = a} = {} \<or> k = 0"
      proof(cases "{x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). ord (f x) mod k = a} \<noteq> {}")
        case T: True
        then obtain x where "ord (f x) mod k = k"
          unfolding True by blast
        then have "k = 0"
          by (metis mod_mod_trivial mod_self)
        thus ?thesis by blast
      next
        case False
        then show ?thesis by blast
      qed
      show ?thesis apply(cases "{x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). ord (f x) mod k = a} = {}")
        using empty_is_semialgebraic apply presburger
        using 1 pre_SA_unit_cong_set_is_semialg assms by blast
    next
      case F': False
      have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). ord (f x) mod k = a} = {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). ord (f x) mod (-k) = a - k}"
        apply(rule equalityI')
        unfolding mem_Collect_eq using zmod_zminus2_eq_if assms apply (metis F)
        unfolding mem_Collect_eq zmod_zminus2_eq_if using False F F' assms
        by (metis (no_types, opaque_lifting) cancel_ab_semigroup_add_class.diff_right_commute group_add_class.right_minus_eq)
      show ?thesis unfolding 0 apply(rule pre_SA_unit_cong_set_is_semialg)
        using False apply presburger using assms by blast
    qed
  qed
qed

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Gluing Functions Along Semialgebraic Sets\<close>
(**************************************************************************************************)
(**************************************************************************************************)
text\<open>
  Semialgebraic functions have the useful property that they are closed under piecewise definitions.
  That is, if $f, g$ are semialgebraic and $C \subseteq \mathbb{Q}_p^m$ is a semialgebraic set,
  then the function:
  \[
   h(x) =
    \begin{cases}
                                     f(x) & \text{if $x \in C$} \\
                                     g(x) & \text{if $x \in \mathbb{Q}_p^m - C$} \\
    undefined & \text{otherwise}
    \end{cases}
  \]
  is again semialgebraic. The function $h$ can be obtained by the definition
  \[\texttt{h = fun\_glue m C f g}\] which is defined below. This closure property means that we
  can avoid having to define partial semialgebraic functions which are undefined outside of some
  proper subset of $\mathbb{Q}_p^m$, since it usually suffices to just define the function as some
  arbitrary constant outside of the desired domain. This is useful for defining partial
  multiplicative inverses of arbitrary functions. If $f$ is semialgebraic, then its nonzero set
  $\{x \in \mathbb{Q}_p^m \mid f x \neq 0\}$ is semialgebraic. By gluing $f$ to the constant
  function $1$ outside of its nonzero set, we obtain an invertible element in the ring
  \texttt{SA(m)} which evaluates to a multiplicative inverse of $f(x)$ on the largest domain
  possible.
\<close>
(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Defining Piecewise Semialgebraic Functions\<close>
(**************************************************************************************************)
(**************************************************************************************************)


text\<open>
  An important property that will be repeatedly used is that we can define piecewise semialgebraic
  functions, which will themselves be semialgebraic as long as the pieces are semialgebraic sets.
  An important application of this principle will be that a function $f$ which is always nonzero
  on some semialgebraic set $A$ can be replaced with a global unit in the ring of semialgebraic
  functions. This global unit admits a global multiplicative inverse that inverts $f$ pointwise on
  $A$, and allows us to avoid having to consider localizations of function rings to locally invert
  such functions.
\<close>

definition fun_glue where
"fun_glue n S f g = (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). if x \<in> S then f x else g x)"

lemma fun_glueE:
  assumes "f \<in> carrier (SA n)"
  assumes "g \<in> carrier (SA n)"
  assumes "S \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "x \<in> S"
  shows "fun_glue n S f g x = f x"
proof-
  have "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
    using assms by blast
  thus ?thesis
    unfolding fun_glue_def using assms
    by (metis (mono_tags, lifting) restrict_apply')
qed

lemma fun_glueE':
  assumes "f \<in> carrier (SA n)"
  assumes "g \<in> carrier (SA n)"
  assumes "S \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) - S"
  shows "fun_glue n S f g x = g x"
proof-
  have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
    using assms by blast
  have 1: "x \<notin> S"
    using assms by blast
  show ?thesis
    unfolding fun_glue_def using assms 0 1
    by (metis (mono_tags, lifting) restrict_apply')
qed

lemma fun_glue_evimage:
  assumes "f \<in> carrier (SA n)"
  assumes "g \<in> carrier (SA n)"
  assumes "S \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "fun_glue n S f g \<inverse>\<^bsub>n\<^esub> T = ((f  \<inverse>\<^bsub>n\<^esub> T) \<inter> S) \<union> ((g  \<inverse>\<^bsub>n\<^esub> T) - S)"
proof
  show "fun_glue n S f g \<inverse>\<^bsub>n\<^esub> T \<subseteq> ((f  \<inverse>\<^bsub>n\<^esub> T) \<inter> S) \<union> ((g  \<inverse>\<^bsub>n\<^esub> T) - S)"
  proof fix x assume A: "x \<in> fun_glue n S f g \<inverse>\<^bsub>n\<^esub> T "
    then have 0: "fun_glue n S f g x \<in> T"
      by blast
    have 1: "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
      using A  by (meson evimage_eq)
    show "x \<in> ((f  \<inverse>\<^bsub>n\<^esub> T) \<inter> S) \<union> ((g  \<inverse>\<^bsub>n\<^esub> T) - S)"
      apply(cases "x \<in> S")
      apply auto[1]
      using "1" apply force
      using "0" assms(1) assms(2) assms(3) fun_glueE apply force
      apply auto[1] using 1 apply blast
      using A 1  unfolding fun_glue_def evimage_def Int_iff  by auto
  qed
  show " f \<inverse>\<^bsub>n\<^esub> T \<inter> S \<union> (g \<inverse>\<^bsub>n\<^esub> T - S) \<subseteq> fun_glue n S f g \<inverse>\<^bsub>n\<^esub> T"
  proof fix x assume A: "x \<in> f \<inverse>\<^bsub>n\<^esub> T \<inter> S \<union> (g \<inverse>\<^bsub>n\<^esub> T - S)"
    then have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
      by (metis (no_types, opaque_lifting) Diff_iff Int_iff UnE extensional_vimage_closed subsetD)
    show "x \<in> fun_glue n S f g \<inverse>\<^bsub>n\<^esub> T"
      apply(cases "x \<in> S")
      using x_closed fun_glueE assms
       apply (metis A DiffD2 IntD1 UnE evimage_eq)
      using x_closed fun_glueE' assms
      by (metis A Diff_iff Int_iff Un_iff evimageD evimageI2)
  qed
qed

lemma fun_glue_partial_pullback:
  assumes "f \<in> carrier (SA k)"
  assumes "g \<in> carrier (SA k)"
  assumes "S \<subseteq> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
  shows "partial_pullback k (fun_glue k S f g) n T =
          ((cartesian_product S (carrier (Q\<^sub>p\<^bsup>n\<^esup>))) \<inter> partial_pullback k f n T) \<union> ((partial_pullback k g n T)- (cartesian_product S (carrier (Q\<^sub>p\<^bsup>n\<^esup>))))"
proof
  show "partial_pullback k (fun_glue k S f g) n T \<subseteq> (cartesian_product S (carrier (Q\<^sub>p\<^bsup>n\<^esup>))) \<inter> partial_pullback k f n T \<union> (partial_pullback k g n T - (cartesian_product S (carrier (Q\<^sub>p\<^bsup>n\<^esup>))))"
  proof fix x assume A: "x \<in> partial_pullback k (fun_glue k S f g) n T "
    then have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>k+n\<^esup>)" unfolding partial_pullback_def partial_image_def
      by (meson evimage_eq)
    show " x \<in> cartesian_product S (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) \<inter> partial_pullback k f n T \<union> (partial_pullback k g n T - (cartesian_product S (carrier (Q\<^sub>p\<^bsup>n\<^esup>))))"
    proof(cases "x \<in> cartesian_product S (carrier (Q\<^sub>p\<^bsup>n\<^esup>))")
      case True
      then have T0: "take k x \<in> S"
        using assms cartesian_product_memE(1) by blast
      then have "(fun_glue k S f g) (take k x) = f (take k x)"
        using assms fun_glueE[of f k g S "take k x"]
        by blast
      then have "partial_image k (fun_glue k S f g) x = partial_image k f x"
        using A x_closed unfolding partial_pullback_def partial_image_def
        by blast
      then show ?thesis using T0 A unfolding partial_pullback_def evimage_def
        by (metis IntI Int_iff True Un_iff vimageI vimage_eq x_closed)
    next
      case False
      then have F0: "take k x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>) - S"
        using A x_closed assms cartesian_product_memI
        by (metis (no_types, lifting) DiffI carrier_is_semialgebraic cartesian_power_drop is_semialgebraic_closed le_add1 local.take_closed)
      then have "(fun_glue k S f g) (take k x) = g (take k x)"
        using assms fun_glueE'[of f k g S "take k x"]
        by blast
      then have "partial_image k (fun_glue k S f g) x = partial_image k g x"
        using A x_closed unfolding partial_pullback_def partial_image_def
        by blast
      then have "x \<in> partial_pullback k g n T "
        using F0 x_closed A unfolding partial_pullback_def partial_image_def evimage_def
        by (metis (no_types, lifting) A IntI local.partial_image_def partial_pullback_memE(2) vimageI)
      then have "x \<in> (partial_pullback k g n T - cartesian_product S (carrier (Q\<^sub>p\<^bsup>n\<^esup>)))"
        using False by blast
      then show ?thesis by blast
    qed
  qed
  show "cartesian_product S (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) \<inter> partial_pullback k f n T \<union> (partial_pullback k g n T - cartesian_product S (carrier (Q\<^sub>p\<^bsup>n\<^esup>)))
    \<subseteq> partial_pullback k (fun_glue k S f g) n T"
  proof fix x assume A: "x \<in> cartesian_product S (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) \<inter> partial_pullback k f n T \<union> (partial_pullback k g n T - cartesian_product S (carrier (Q\<^sub>p\<^bsup>n\<^esup>)))"
    then have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
      by (metis DiffD1 Int_iff Un_iff add.commute partial_pullback_memE(1))
    show "x \<in> partial_pullback k (fun_glue k S f g) n T"
    proof(cases "x \<in> cartesian_product S (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) \<inter> partial_pullback k f n T")
      case True
      show ?thesis apply(rule partial_pullback_memI)
        using x_closed apply (metis add.commute)
        using x_closed True assms fun_glueE[of f k g S "take k x"] partial_pullback_memE[of x k f n T]
        unfolding partial_image_def by (metis Int_iff cartesian_product_memE(1))
    next
      case False
      show ?thesis apply(rule partial_pullback_memI)
        using x_closed apply (metis add.commute)
        using A x_closed False assms fun_glueE'[of f k g S "take k x"] partial_pullback_memE[of x k g n T]
        unfolding partial_image_def
        by (metis (no_types, lifting) Diff_iff Un_iff carrier_is_semialgebraic cartesian_power_drop cartesian_product_memI is_semialgebraic_closed le_add2 local.take_closed)
    qed
  qed
qed

lemma fun_glue_eval_closed:
  assumes "f \<in> carrier (SA n)"
  assumes "g \<in> carrier (SA n)"
  assumes "is_semialgebraic n S"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "fun_glue n S f g x \<in> carrier Q\<^sub>p"
  apply(cases "x \<in> S")
  using assms fun_glueE SA_car_memE
   apply (metis Qp.function_ring_car_mem_closed is_semialgebraic_closed)
proof- assume A: "x \<notin> S"
  then have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) - S"
    using assms by auto
  hence 1: "fun_glue n S f g x = g x"
    using assms fun_glueE' is_semialgebraic_closed by auto
  show "fun_glue n S f g x \<in> carrier Q\<^sub>p"
    unfolding 1 using assms SA_car_memE by blast
qed

lemma fun_glue_closed:
  assumes "f \<in> carrier (SA n)"
  assumes "g \<in> carrier (SA n)"
  assumes "is_semialgebraic n S"
  shows "fun_glue n S f g \<in> carrier (SA n)"
  apply(rule SA_car_memI)
   apply(rule Qp.function_ring_car_memI)
  using fun_glue_eval_closed assms apply blast
  using fun_glue_def unfolding restrict_apply apply metis
  apply(rule is_semialg_functionI, intro Pi_I fun_glue_eval_closed assms, blast)
proof-
  fix k T assume A: "T \<in> semialg_sets (1 + k)"
  have 0: "is_semialgebraic (n+k) (partial_pullback n f k T)"
    using assms A SA_car_memE[of f n]  is_semialg_functionE[of n f k T]  padic_fields.is_semialgebraicI padic_fields_axioms by blast
  have 1: "is_semialgebraic (n+k) (partial_pullback n g k T)"
    using assms A SA_car_memE[of g n]  is_semialg_functionE[of n g k T] padic_fields.is_semialgebraicI padic_fields_axioms by blast
  have 2: "partial_pullback n (fun_glue n S f g) k T =
    cartesian_product S (carrier (Q\<^sub>p\<^bsup>k\<^esup>)) \<inter> partial_pullback n f k T \<union> (partial_pullback n g k T - cartesian_product S (carrier (Q\<^sub>p\<^bsup>k\<^esup>)))"
    using assms fun_glue_partial_pullback[of f n g S k T] \<open>f \<in> carrier (SA n)\<close> \<open>g \<in> carrier (SA n)\<close> is_semialgebraic_closed
    by blast
  show "is_semialgebraic (n + k) (partial_pullback n (fun_glue n S f g) k T)"
    using assms 0 1 2 cartesian_product_is_semialgebraic carrier_is_semialgebraic
      diff_is_semialgebraic intersection_is_semialg union_is_semialgebraic by presburger
qed

lemma fun_glue_unit:
  assumes "f \<in> carrier (SA n)"
  assumes "is_semialgebraic n S"
  assumes "\<And>x. x \<in> S \<Longrightarrow> f x \<noteq> \<zero>"
  shows "fun_glue n S f \<one>\<^bsub>SA n\<^esub> \<in> Units (SA n)"
proof(rule SA_Units_memI)
  show "fun_glue n S f \<one>\<^bsub>SA n\<^esub> \<in> carrier (SA n)"
    using fun_glue_closed assms SA_is_cring cring.cring_simprules(6) by blast
  show "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<Longrightarrow> fun_glue n S f \<one>\<^bsub>SA n\<^esub> x \<noteq> \<zero>"
  proof- fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
    show "fun_glue n S f \<one>\<^bsub>SA n\<^esub> x \<noteq> \<zero>"
      apply(cases "x \<in> S")
      using assms SA_is_cring cring.cring_simprules(6) assms(3)[of x] fun_glueE[of f n "\<one>\<^bsub>SA n\<^esub>" S x]
      apply (metis is_semialgebraic_closed)
      using assms SA_is_cring[of n] cring.cring_simprules(6)[of "SA n"]
            A  fun_glueE'[of f n "\<one>\<^bsub>SA n\<^esub>" S x] is_semialgebraic_closed[of n S]
      unfolding SA_one[of n] function_ring_defs(4)[of n] function_one_def
      by (metis Diff_iff function_one_eval Qp_funs_one local.one_neq_zero)
  qed
qed

definition parametric_fun_glue where
"parametric_fun_glue n Xs fs = (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). let S = (THE S. S \<in> Xs \<and> x \<in> S) in (fs S x))"

lemma parametric_fun_glue_formula:
  assumes "Xs partitions (carrier (Q\<^sub>p\<^bsup>n\<^esup>))"
  assumes "x \<in> S"
  assumes "S \<in> Xs"
  shows "parametric_fun_glue n Xs fs x = fs S x"
proof-
  have 0: "(THE S. S \<in> Xs \<and> x \<in> S) = S"
    apply(rule the_equality)
    using assms apply blast
    using assms unfolding is_partition_def by (metis Int_iff empty_iff disjointE)
  have 1: "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
    using assms unfolding is_partition_def by blast
  then show ?thesis using 0 unfolding parametric_fun_glue_def  restrict_def by metis
qed

definition char_fun where
"char_fun n S = (\<lambda> x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). if x \<in> S then \<one> else \<zero>)"

lemma char_fun_is_semialg:
  assumes "is_semialgebraic n S"
  shows "char_fun n S \<in> carrier (SA n)"
proof-
  have "char_fun n S = fun_glue n S \<one>\<^bsub>SA n\<^esub> \<zero>\<^bsub>SA n\<^esub>"
    unfolding char_fun_def fun_glue_def
    by (metis (no_types, lifting) function_one_eval function_zero_eval SA_one SA_zero restrict_ext)
  then show ?thesis
    using assms fun_glue_closed
    by (metis SA_is_cring cring.cring_simprules(2) cring.cring_simprules(6))
qed

lemma SA_finsum_apply:
  assumes "finite S"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "F \<in> S \<rightarrow> carrier (SA n) \<longrightarrow> finsum (SA n) F S x = (\<Oplus>s\<in>S. F s x)"
proof(rule finite.induct[of S])
  show "finite S"
    using assms by blast
  show " F \<in> {} \<rightarrow> carrier (SA n) \<longrightarrow> finsum (SA n) F {} x = (\<Oplus>s\<in>{}. F s x)"
    using assms abelian_monoid.finsum_empty[of "SA n"]   Qp.abelian_monoid_axioms SA_is_abelian_monoid
    by (simp add: SA_zeroE)
  show "\<And>A a. finite A \<Longrightarrow>
           F \<in> A \<rightarrow> carrier (SA n) \<longrightarrow> finsum (SA n) F A x = (\<Oplus>s\<in>A. F s x) \<Longrightarrow>
           F \<in> insert a A \<rightarrow> carrier (SA n) \<longrightarrow> finsum (SA n) F (insert a A) x = (\<Oplus>s\<in>insert a A. F s x)"
  proof- fix A a assume A: "finite A" "F \<in> A \<rightarrow> carrier (SA n) \<longrightarrow> finsum (SA n) F A x = (\<Oplus>s\<in>A. F s x)"
    show " F \<in> insert a A \<rightarrow> carrier (SA n) \<longrightarrow> finsum (SA n) F (insert a A) x = (\<Oplus>s\<in>insert a A. F s x)"
    proof assume A': "F \<in> insert a A \<rightarrow> carrier (SA n)"
      then have 0: "F \<in> A \<rightarrow> carrier (SA n)"
        by blast
      hence 1: "finsum (SA n) F A x = (\<Oplus>s\<in>A. F s x)"
        using A by blast
      show "finsum (SA n) F (insert a A) x = (\<Oplus>s\<in>insert a A. F s x)"
      proof(cases "a \<in> A")
        case True
        then show ?thesis
          using 1 by (metis insert_absorb)
      next
        case False
        have F00: "(\<lambda>s. F s x) \<in> A \<rightarrow> carrier Q\<^sub>p"
          apply(rule Pi_I, rule SA_car_closed[of _ n] )
          using "0" assms by auto
        have F01: "F a x \<in> carrier Q\<^sub>p"
          using A' assms
          by (metis (no_types, lifting) Qp.function_ring_car_mem_closed Pi_split_insert_domain SA_car_in_Qp_funs_car subsetD)
        have F0: "(\<Oplus>s\<in>insert a A. F s x) = F a x \<oplus> (\<Oplus>s\<in>A. F s x)"
          using F00 F01  A' False A(1) Qp.finsum_insert[of A a "\<lambda>s. F s x"] by blast
        have F1: "finsum (SA n) F (insert a A) = F a \<oplus>\<^bsub>SA n\<^esub> finsum (SA n) F A"
          using abelian_monoid.finsum_insert[of "SA n" A a F]
          by (metis (no_types, lifting) A' A(1) False Pi_split_insert_domain SA_is_abelian_monoid assms(1))
        show ?thesis
          using Qp.finsum_closed[of "\<lambda>s. F s x" A] abelian_monoid.finsum_closed[of "SA n" F A]
                SA_is_abelian_monoid[of n] assms F0 F1 "0" A(2) SA_add by presburger
      qed
    qed
  qed
qed

lemma SA_finsum_apply_zero:
  assumes "finite S"
  assumes "F \<in> S \<rightarrow> carrier (SA n)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "\<And>s. s \<in> S \<Longrightarrow> F s x = \<zero>"
  shows "finsum (SA n) F S x = \<zero>"
proof-
  have "finsum (SA n) F S x = (\<Oplus>s\<in>S. F s x)"
    using SA_finsum_apply assms by blast
  then show ?thesis using assms
    by (metis Qp.add.finprod_one_eqI)
qed

lemma parametric_fun_glue_is_SA:
  assumes "finite Xs"
  assumes "Xs partitions (carrier (Q\<^sub>p\<^bsup>n\<^esup>))"
  assumes "fs \<in> Xs \<rightarrow> carrier (SA n)"
  assumes "\<forall> S \<in> Xs. is_semialgebraic n S"
  shows "parametric_fun_glue n Xs fs \<in> carrier (SA n)"
proof-
  obtain F where F_def: "F = (\<lambda>S. fs S \<otimes>\<^bsub>SA n\<^esub> char_fun n S)"
    by blast
  have 0: "F \<in> Xs \<rightarrow> carrier (SA n)" proof fix S assume "S \<in> Xs" then show "F S \<in> carrier (SA n)"
      using  SA_mult_closed[of n "fs S" "char_fun n S"] char_fun_is_semialg[of n S] assms SA_car_memE
      unfolding F_def by blast qed
  have 1: "\<And>S x. S \<in> Xs \<Longrightarrow> x \<in> S \<Longrightarrow> F S x = fs S x"
  proof- fix S x assume A: "S \<in> Xs" "x \<in> S"
    then have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
      using assms unfolding is_partition_def by blast
    then have 0: "F S x = fs S x \<otimes> char_fun n S x"
      unfolding F_def using SA_mult by blast
    have 1: "char_fun n S x = \<one>"
      using char_fun_def A x_closed by auto
    have 2: "fs S x \<in> carrier Q\<^sub>p"
      apply(intro SA_car_closed[of _ n] x_closed )
      using assms A by auto
    show "F S x = fs S x"
      unfolding 0  1 using 2 Qp.cring_simprules(12) by auto
  qed
  have 2: "\<And>S x. S \<in> Xs \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<Longrightarrow> x \<notin> S \<Longrightarrow> F S x = \<zero>"
  proof- fix S x assume A: "S \<in> Xs" "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)" "x \<notin> S"
    then have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
      using assms unfolding is_partition_def by blast
    hence 20: "F S x = fs S x \<otimes> char_fun n S x"
      unfolding F_def using SA_mult by blast
    have 21: "char_fun n S x = \<zero>"
      unfolding char_fun_def using A x_closed by auto
    have 22: "fs S x \<in> carrier Q\<^sub>p"
      apply(intro SA_car_closed[of _ n] x_closed )
      using assms A by auto
    show "F S x = \<zero>"
      using 22 unfolding 20 21 by auto
  qed
  obtain g where g_def: "g = finsum (SA n) F Xs"
    by blast
  have g_closed: "g \<in> carrier (SA n)"
    using abelian_monoid.finsum_closed[of "SA n" F Xs] assms SA_is_ring 0
    unfolding g_def ring_def abelian_group_def by blast
  have "g = parametric_fun_glue n Xs fs"
  proof fix x show "g x = parametric_fun_glue n Xs fs x"
    proof(cases "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)")
      case True
      then obtain S where S_def: "S \<in> Xs \<and> x \<in> S"
        using assms is_partitionE by blast
      then have T0: "parametric_fun_glue n Xs fs x = F S x"
        using 1 assms parametric_fun_glue_formula by blast
      have T1: "g x = F S x"
      proof-
        have 00: " F S \<oplus>\<^bsub>SA n\<^esub> finsum (SA n) F (Xs - {S}) =  finsum (SA n) F (insert S (Xs - {S}))"
          using abelian_monoid.finsum_insert[of "SA n" "Xs - {S}" S F ]
          by (metis (no_types, lifting) "0" Diff_iff Pi_anti_mono Pi_split_insert_domain SA_is_abelian_monoid S_def Set.basic_monos(7) assms(1) finite_Diff insert_iff subsetI)
        have T10: "g  = F S \<oplus>\<^bsub>SA n\<^esub> finsum (SA n) F (Xs - {S})"
          using S_def unfolding 00 g_def
          by (simp add: insert_absorb)
        have T11: "finsum (SA n) F (Xs - {S}) \<in> carrier (SA n)"
          using abelian_monoid.finsum_closed[of "SA n" F "Xs - {S}"] assms SA_is_ring 0
          unfolding g_def ring_def abelian_group_def by blast
        hence T12: "g x = F S x \<oplus> finsum (SA n) F (Xs - {S}) x"
          using SA_add S_def T10 assms is_semialgebraic_closed by blast
        have T13: "finsum (SA n) F (Xs - {S}) x = \<zero>"
          apply(rule SA_finsum_apply_zero[of "Xs - {S}" F n x])
              using assms apply blast
                using "0" apply blast
                using True apply blast
        proof-
           fix s assume AA: "s \<in> Xs - {S}"
           then have "x \<notin> s"
             using True assms S_def is_partitionE[of Xs "carrier (Q\<^sub>p\<^bsup>n\<^esup>)"]  disjointE[of Xs S s]
             by blast
           then show "F s x = \<zero>"
             using AA 2[of s x] True by blast
        qed
        have T14: "F S x \<in> carrier Q\<^sub>p"
          using assms True S_def  by (metis (no_types, lifting) "0" Qp.function_ring_car_mem_closed PiE SA_car_memE(2))
        then show ?thesis using T12 T13 assms True Qp.add.l_cancel_one Qp.zero_closed by presburger
      qed
      show ?thesis using T0 T1 by blast
    next
      case False
      then show ?thesis
        using g_closed unfolding parametric_fun_glue_def
        by (metis (mono_tags, lifting) function_ring_not_car SA_car_memE(2) restrict_def)
    qed
  qed
  then show ?thesis using g_closed by blast
qed

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Turning Functions into Units Via Gluing\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>
  By gluing a function to the multiplicative unit on its zero set, we can get a canonical choice of
  local multiplicative inverse of a function $f$. Denef's proof frequently reasons about functions
  of the form $\frac{f(x)}{g(x)}$ with the tacit understanding that they are meant to be defined
  on the largest domain of definition possible. This technical tool allows us to replicate this
  kind of reasoning in our formal proofs.
\<close>

definition to_fun_unit where
"to_fun_unit n f = fun_glue n {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). f x \<noteq> \<zero>} f \<one>\<^bsub>SA n\<^esub>"

lemma to_fun_unit_is_unit:
  assumes "f \<in> carrier (SA n)"
  shows "to_fun_unit n f \<in> Units (SA n)"
  unfolding to_fun_unit_def
  apply(rule fun_glue_unit)
  apply (simp add: assms)
  using assms nonzero_evimage_closed[of f] apply blast
  by blast

lemma to_fun_unit_closed:
  assumes "f \<in> carrier (SA n)"
  shows "to_fun_unit n f \<in> carrier (SA n)"
  using assms to_fun_unit_is_unit SA_is_ring SA_Units_closed by blast

lemma to_fun_unit_eq:
  assumes "f \<in> carrier (SA n)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f x \<noteq> \<zero>"
  shows "to_fun_unit n f x = f x"
  unfolding to_fun_unit_def fun_glue_def using assms
  by simp

lemma to_fun_unit_eq':
  assumes "f \<in> carrier (SA n)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f x = \<zero>"
  shows "to_fun_unit n f x = \<one>"
  unfolding to_fun_unit_def fun_glue_def using assms
  by (simp add: SA_oneE)

definition one_over_fun where
"one_over_fun n f = inv\<^bsub>SA n\<^esub> (to_fun_unit n f)"

lemma one_over_fun_closed:
  assumes "f \<in> carrier (SA n)"
  shows "one_over_fun n f \<in> carrier (SA n)"
  using assms SA_is_ring[of n] to_fun_unit_is_unit[of f n]
  by (metis SA_Units_closed one_over_fun_def ring.Units_inverse)

lemma one_over_fun_eq:
  assumes "f \<in> carrier (SA n)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f x \<noteq> \<zero>"
  shows "one_over_fun n f x = inv (f x)"
  using assms to_fun_unit_eq unfolding one_over_fun_def
  using Qp_funs_m_inv SA_Units_Qp_funs_Units SA_Units_Qp_funs_inv to_fun_unit_is_unit by presburger

lemma one_over_fun_smult_eval:
  assumes "f \<in> carrier (SA n)"
  assumes "a \<noteq> \<zero>"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f x \<noteq> \<zero>"
  shows "one_over_fun n (a \<odot>\<^bsub>SA n\<^esub>f) x = inv (a \<otimes> (f x))"
  using one_over_fun_eq[of "a \<odot>\<^bsub>SA n\<^esub> f" n x] assms
  by (metis Qp.function_ring_car_memE Qp.integral SA_car_memE(2) SA_smult_closed SA_smult_formula)

lemma one_over_fun_smult_eval':
  assumes "f \<in> carrier (SA n)"
  assumes "a \<noteq> \<zero>"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f x \<noteq> \<zero>"
  shows "one_over_fun n (a \<odot>\<^bsub>SA n\<^esub>f) x = inv a \<otimes> inv (f x)"
proof-
  have 0: "one_over_fun n (a \<odot>\<^bsub>SA n\<^esub> f) x = inv (a \<otimes> f x)"
    using assms one_over_fun_smult_eval[of f n a x]
    by fastforce
  have 1: "f x \<in> nonzero Q\<^sub>p"
    by(intro nonzero_memI SA_car_closed[ of _ n] assms)
  show ?thesis
    unfolding 0 using 1 assms
    using Qp.comm_inv_char Qp.cring_simprules(11) Qp.cring_simprules(5) SA_car_closed field_inv(2) field_inv(3) local.fract_cancel_right by presburger
qed



lemma SA_add_pow_closed:
  assumes "f \<in> carrier (SA n)"
  shows "([(k::nat)]\<cdot>\<^bsub>SA n\<^esub>f) \<in> carrier (SA n)"
  using assms SA_is_ring[of n]
  by (meson ring.nat_mult_closed)

lemma one_over_fun_add_pow_eval:
  assumes "f \<in> carrier (SA n)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f x \<noteq> \<zero>"
  assumes "(k::nat) > 0"
  shows "one_over_fun n ([k]\<cdot>\<^bsub>SA n\<^esub>f) x = inv ([k] \<cdot>f x)"
proof-
  have 0: "([k] \<cdot>\<^bsub>SA n\<^esub> f) x = [k] \<cdot> f x"
    using assms SA_add_pow_apply[of f n x k] by linarith
  hence 1: "([k] \<cdot>\<^bsub>SA n\<^esub> f) x \<noteq> \<zero>"
    using assms Qp_char_0'' Qp.function_ring_car_mem_closed SA_car_memE(2)
    by metis
  have 2: "one_over_fun n ([k] \<cdot>\<^bsub>SA n\<^esub> f) x = inv ([k] \<cdot>\<^bsub>SA n\<^esub> f) x"
    using assms one_over_fun_eq[of "[k]\<cdot>\<^bsub>SA n\<^esub>f" n x] 1 SA_add_pow_closed by blast
  thus ?thesis using 1 0 by presburger
qed

lemma one_over_fun_pow_closed:
  assumes "f \<in> carrier (SA n)"
  shows "one_over_fun n (f[^]\<^bsub>SA n\<^esub>(k::nat)) \<in> carrier (SA n)"
  using assms
  by (meson SA_nat_pow_closed one_over_fun_closed padic_fields.SA_imp_semialg padic_fields_axioms)

lemma one_over_fun_pow_eval:
  assumes "f \<in> carrier (SA n)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f x \<noteq> \<zero>"
  shows "one_over_fun n (f[^]\<^bsub>SA n\<^esub>(k::nat)) x = inv ((f x) [^] k)"
  using one_over_fun_eq[of  "f[^]\<^bsub>SA n\<^esub>k" n x] assms
  by (metis Qp.function_ring_car_memE Qp.nonzero_pow_nonzero SA_car_memE(2) SA_nat_pow SA_nat_pow_closed padic_fields.SA_car_memE(1) padic_fields_axioms)


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Inclusions of Lower Dimensional Function Rings\<close>
(**************************************************************************************************)
(**************************************************************************************************)


definition fun_inc where
"fun_inc m n f = (\<lambda> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). f (take n x))"

lemma fun_inc_closed:
  assumes "f \<in> carrier (SA n)"
  assumes "m \<ge> n"
  shows  "fun_inc m n f \<in> carrier (SA m)"
proof-
  have 0: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> fun_inc m n f x = (f \<circ> take n) x"
    unfolding fun_inc_def by (metis comp_apply restrict_apply')
  have 1: "is_semialg_function m (f \<circ> take n)"
    using assms comp_take_is_semialg
    by (metis SA_imp_semialg le_neq_implies_less padic_fields.semialg_function_comp_closed padic_fields_axioms take_is_semialg_map)
  have 2: "is_semialg_function m (fun_inc m n f)"
    using 0 1 semialg_function_on_carrier' by blast
  show ?thesis apply(rule SA_car_memI) apply(rule  Qp.function_ring_car_memI)
    using "2" is_semialg_function_closed apply blast
    using fun_inc_def[of m n f] unfolding restrict_def apply presburger
    using 2 by blast
qed

lemma fun_inc_eval:
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "fun_inc m n f x = f (take n x)"
  unfolding fun_inc_def using assms
  by (meson restrict_apply')

lemma ord_congruence_set_univ_semialg_fixed:
  assumes "n \<ge> 0"
  shows "is_univ_semialgebraic (ord_congruence_set n a)"
  using ord_congruence_set_univ_semialg assms
  by auto

lemma ord_congruence_set_SA_function:
  assumes "n \<ge> 0"
  assumes "c \<in> carrier (SA (m+l))"
  shows "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). c x \<in> nonzero Q\<^sub>p \<and> ord (c x) mod n = a}"
proof-
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). c x \<in> nonzero Q\<^sub>p \<and> ord (c x) mod n = a} = c  \<inverse>\<^bsub>m+l\<^esub> (ord_congruence_set n a)"
    unfolding ord_congruence_set_def evimage_def using assms by blast
  show ?thesis unfolding 0 apply(rule evimage_is_semialg)
    using assms apply blast using assms  ord_congruence_set_univ_semialg_fixed[of n a]
    by blast
qed

lemma ac_cong_set_SA:
  assumes "n > 0"
  assumes "k \<in> Units (Zp_res_ring n)"
  assumes "c \<in> carrier (SA (m+l))"
  shows "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). c x \<in> nonzero Q\<^sub>p \<and> ac n (c x) = k}"
proof-
  have  "{x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). c x \<in> nonzero Q\<^sub>p \<and> ac n (c x) = k}= (c \<inverse>\<^bsub>m + l\<^esub> ac_cong_set n k)"
    unfolding ac_cong_set_def evimage_def nonzero_def mem_Collect_eq using assms by blast
  thus ?thesis
    using assms ac_cong_set_is_univ_semialg[of n k] evimage_is_semialg[of c "m+l" "ac_cong_set n k"]
    by presburger
qed

lemma ac_cong_set_SA':
  assumes "n >0 "
  assumes "k \<in> Units (Zp_res_ring n)"
  assumes "c \<in> carrier (SA m)"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). c x \<in> nonzero Q\<^sub>p \<and> ac n (c x) = k}"
  using assms ac_cong_set_SA[of n k c m 0] unfolding Nat.add_0_right by blast

lemma ac_cong_set_SA'':
  assumes "n >0 "
  assumes "m > 0"
  assumes "k \<in> Units (Zp_res_ring n)"
  assumes "c \<in> carrier (SA m)"
  assumes "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> c x \<noteq> \<zero>"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ac n (c x) = k}"
proof-
  have "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). c x \<in> nonzero Q\<^sub>p \<and> ac n (c x) = k} = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ac n (c x) = k}"
    apply(rule subset_antisym) apply blast
    apply(rule subsetI) using assms unfolding nonzero_def mem_Collect_eq
    using Qp.function_ring_car_memE SA_car_memE(2) by blast
  thus ?thesis using assms ac_cong_set_SA'[of n k c m] by metis
qed


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Miscellaneous\<close>
(**************************************************************************************************)
(**************************************************************************************************)


lemma nth_pow_wits_SA_fun_prep:
  assumes "n > 0"
  assumes "h \<in> carrier (SA m)"
  assumes "\<rho> \<in> nth_pow_wits n"
  shows "is_semialgebraic m (h \<inverse>\<^bsub>m\<^esub>pow_res n \<rho>)"
  by(intro evimage_is_semialg assms  pow_res_is_univ_semialgebraic nth_pow_wits_closed(1)[of n])

definition kth_rt where
"kth_rt m (k::nat) f x = (if x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) then (THE b. b \<in> carrier Q\<^sub>p \<and> b[^]k = (f x) \<and> ac (nat (ord ([k]\<cdot>\<one>)) + 1) b = 1)
                                                           else undefined )"

text\<open>Normalizing a semialgebraic function to have a constant angular component\<close>

lemma ac_res_Unit_inc:
  assumes "n > 0"
  assumes "t \<in> Units (Zp_res_ring n)"
  shows "ac n ([t]\<cdot>\<one>) = t"
proof-
  have 0: "[t]\<cdot>\<one> \<noteq>\<zero>"
    using assms by (metis Qp_char_0_int less_one less_or_eq_imp_le nat_neq_iff zero_not_in_residue_units)
  have 1: "[t]\<cdot>\<one> \<in> \<O>\<^sub>p"
    by (metis Zp.one_closed Zp_int_mult_closed image_eqI inc_of_int)
  hence 2: "angular_component ([t]\<cdot>\<one>) = ac_Zp ([t]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>)"
    using angular_component_of_inclusion[of "[t]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>"]
    by (metis "0" Qp.int_inc_zero Zp.int_inc_zero Zp_int_inc_closed inc_of_int not_nonzero_Qp)
  hence 3: "ac n ([t]\<cdot>\<one>) = ac_Zp ([t]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) n"
    unfolding ac_def using 0 by presburger
  hence "val_Zp ([t]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) = 0"
  proof-
    have "coprime p t"
      using assms
      by (metis coprime_commute less_one less_or_eq_imp_le nat_neq_iff padic_integers.residue_UnitsE padic_integers_axioms)
    then show ?thesis
      by (metis Zp_int_inc_closed Zp_int_inc_res coprime_mod_right_iff coprime_power_right_iff mod_by_0 order_refl p_residues residues.m_gt_one residues.mod_in_res_units val_Zp_0_criterion val_Zp_p val_Zp_p_int_unit zero_less_one zero_neq_one_class.one_neq_zero zero_not_in_residue_units)
  qed
  hence 4: "[t]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub> \<in> Units Z\<^sub>p"
    using val_Zp_0_imp_unit by blast
  hence 5: "ac_Zp ([t]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>)  = [t]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>"  using
      ac_Zp_of_Unit  \<open>val_Zp ([t] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>) = 0\<close> by blast
  have 6: "ac_Zp ([t]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) n  = t"
  proof-
    have "t \<in> carrier (Zp_res_ring n)"
      using assms monoid.Units_closed[of "Zp_res_ring n" t] cring_def padic_integers.R_cring padic_integers_axioms ring_def by blast
    hence "t < p^n \<and> t \<ge> 0 "
      using p_residue_ring_car_memE by auto
    thus ?thesis
      unfolding 5 unfolding Zp_int_inc_rep p_residue_def residue_def by auto
  qed
  show ?thesis
    unfolding 3 using 6 by blast
qed

lemma val_of_res_Unit:
  assumes "n > 0"
  assumes "t \<in> Units (Zp_res_ring n)"
  shows "val ([t]\<cdot>\<one>) = 0"
proof-
  have 0: "[t]\<cdot>\<one> \<noteq>\<zero>"
    using assms by (metis Qp_char_0_int less_one less_or_eq_imp_le nat_neq_iff zero_not_in_residue_units)
  have 1: "[t]\<cdot>\<one> \<in> \<O>\<^sub>p"
    by (metis Zp.one_closed Zp_int_mult_closed image_eqI inc_of_int)
  hence 2: "angular_component ([t]\<cdot>\<one>) = ac_Zp ([t]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>)"
    using angular_component_of_inclusion[of "[t]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>"]
    by (metis "0" Qp.int_inc_zero Zp.int_inc_zero Zp_int_inc_closed inc_of_int not_nonzero_Qp)
  hence 3: "ac n ([t]\<cdot>\<one>) = ac_Zp ([t]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) n"
    unfolding ac_def using 0 by presburger
  hence "val_Zp ([t]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) = 0"
  proof-
    have "coprime p t"
      using assms
      by (metis coprime_commute less_one less_or_eq_imp_le nat_neq_iff padic_integers.residue_UnitsE padic_integers_axioms)
    then show ?thesis
      by (metis Zp_int_inc_closed Zp_int_inc_res coprime_mod_right_iff coprime_power_right_iff mod_by_0 order_refl p_residues residues.m_gt_one residues.mod_in_res_units val_Zp_0_criterion val_Zp_p val_Zp_p_int_unit zero_less_one zero_neq_one_class.one_neq_zero zero_not_in_residue_units)
  qed
  then show ?thesis using assms
    by (metis Zp_int_inc_closed inc_of_int val_of_inc)
qed


lemma(in padic_integers) res_map_is_hom:
  assumes "N > 0"
  shows "ring_hom_ring Zp (Zp_res_ring N) (\<lambda> x. x N)"
  apply(rule ring_hom_ringI)
  apply (simp add: R.ring_axioms)
  using assms cring.axioms(1) local.R_cring apply blast
  using residue_closed apply blast
  using residue_of_prod apply blast
  using residue_of_sum apply blast
  using assms residue_of_one(1) by blast

lemma ac_of_fraction:
  assumes "N > 0"
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "b \<in> nonzero Q\<^sub>p"
  shows "ac N (a \<div> b) = ac N a \<otimes>\<^bsub>Zp_res_ring N\<^esub> inv \<^bsub>Zp_res_ring N\<^esub> ac N b"
  using ac_mult[of a "inv b" N] ac_inv assms Qp.nonzero_closed nonzero_inverse_Qp by presburger

lemma pow_res_eq_rel:
  assumes "n > 0"
  assumes "b \<in> carrier Q\<^sub>p"
  shows "{x \<in> carrier Q\<^sub>p. pow_res n x = pow_res n b} = pow_res n b"
  apply(rule equalityI',  unfold mem_Collect_eq, metis pow_res_refl,
        intro conjI)
    using pow_res_def apply auto[1]
    apply(rule equal_pow_resI)
    using pow_res_def apply auto[1]
    using  pow_res_refl assms  by (metis equal_pow_resI)

lemma pow_res_is_univ_semialgebraic':
  assumes "n > 0"
  assumes "b \<in> carrier Q\<^sub>p"
  shows "is_univ_semialgebraic {x \<in> carrier Q\<^sub>p. pow_res n x = pow_res n b}"
  using assms pow_res_eq_rel pow_res_is_univ_semialgebraic by presburger

lemma evimage_eqI:
  assumes "c \<in> carrier (SA n)"
  shows "c  \<inverse>\<^bsub>n\<^esub> {x \<in> carrier Q\<^sub>p. P x} = {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). P (c x)}"
  by(rule equalityI', unfold evimage_def mem_Collect_eq Int_iff,  intro conjI, auto
        , rule SA_car_closed[of _ n], auto simp: assms)

lemma SA_pow_res_is_semialgebraic:
  assumes "n > 0"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "c \<in> carrier (SA N)"
  shows "is_semialgebraic N  {x \<in> carrier (Q\<^sub>p\<^bsup>N\<^esup>). pow_res n (c x) = pow_res n b}"
proof-
  have " c  \<inverse>\<^bsub>N\<^esub> {x \<in> carrier Q\<^sub>p. pow_res n x = pow_res n b} = {x \<in> carrier (Q\<^sub>p\<^bsup>N\<^esup>). pow_res n (c x) = pow_res n b}"
    apply(rule evimage_eqI) using assms by blast
  thus ?thesis
    using pow_res_is_univ_semialgebraic' evimage_is_semialg assms
    by (metis (no_types, lifting))
qed

lemma eint_diff_imp_eint:
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "val a = val b + eint i"
  shows "b \<in> nonzero Q\<^sub>p"
  using assms val_zero
  by (metis Qp.nonzero_closed Qp.not_nonzero_memE not_eint_eq plus_eint_simps(2) val_ord')

lemma SA_minus_eval:
  assumes "f \<in> carrier (SA n)"
  assumes "g \<in> carrier (SA n)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "(f  \<ominus>\<^bsub>SA n\<^esub> g) x = f x \<ominus> g x"
  using assms unfolding a_minus_def
  using SA_a_inv_eval SA_add  by metis

lemma Qp_cong_set_evimage:
  assumes "f \<in> carrier (SA n)"
  assumes "a \<in> carrier Z\<^sub>p"
  shows  "is_semialgebraic n (f \<inverse>\<^bsub>n\<^esub> (Qp_cong_set \<alpha> a))"
  using assms Qp_cong_set_is_univ_semialgebraic evimage_is_semialg by blast

lemma SA_constant_res_set_semialg:
  assumes "l \<in> carrier (Zp_res_ring n)"
  assumes "f \<in> carrier (SA m)"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). f x \<in> \<O>\<^sub>p \<and> Qp_res (f x) n = l}"
proof-
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). f x \<in> \<O>\<^sub>p \<and> Qp_res (f x) n = l} = f  \<inverse>\<^bsub>m\<^esub> {x \<in> \<O>\<^sub>p. Qp_res x n = l}"
    unfolding evimage_def  by blast
  show ?thesis unfolding 0
    by(rule evimage_is_semialg, rule assms, rule constant_res_set_semialg, rule assms)
qed

lemma val_ring_cong_set:
  assumes "f \<in> carrier (SA k)"
  assumes "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<Longrightarrow> f x \<in> \<O>\<^sub>p"
  assumes "t \<in> carrier (Zp_res_ring n)"
  shows "is_semialgebraic k {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). to_Zp (f x) n = t}"
proof-
  have 0: "[t] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> \<in> carrier Z\<^sub>p "
    by blast
  have 1: "([t] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>) n = t"
    using assms
    unfolding Zp_int_inc_rep p_residue_def residue_def residue_ring_def by simp
  have "{x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). to_Zp (f x) n = t} = f  \<inverse>\<^bsub>k\<^esub> {x \<in> \<O>\<^sub>p. (to_Zp x) n = t}"
    unfolding evimage_def using assms by auto
  then show ?thesis using 0 1 assms  Qp_cong_set_evimage[of f k "[t]\<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>" n] unfolding Qp_cong_set_def
    by presburger
qed

lemma val_ring_pullback_SA:
  assumes "N > 0"
  assumes "c \<in> carrier (SA N)"
  shows "is_semialgebraic N {x \<in> carrier (Q\<^sub>p\<^bsup>N\<^esup>). c x \<in> \<O>\<^sub>p}"
proof-
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>N\<^esup>). c x \<in> \<O>\<^sub>p} = c  \<inverse>\<^bsub>N\<^esub> \<O>\<^sub>p"
    unfolding evimage_def by blast
  have 1: "is_univ_semialgebraic \<O>\<^sub>p"
    using Qp_val_ring_is_univ_semialgebraic by blast
  show ?thesis using assms 0 1 evimage_is_semialg by presburger
qed

lemma(in padic_fields) res_eq_set_is_semialg:
  assumes "k > 0"
  assumes "c \<in> carrier (SA k)"
  assumes "s \<in> carrier (Zp_res_ring n)"
  shows "is_semialgebraic k {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). c x \<in> \<O>\<^sub>p \<and> to_Zp (c x) n = s}"
proof-
  obtain a where a_def: "a = [s]\<cdot>\<one>"
    by blast
  have 0: "a \<in> \<O>\<^sub>p"
    using a_def
    by (metis Zp.one_closed Zp_int_mult_closed image_iff inc_of_int)
  have 1: "to_Zp a = [s]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>"
    using 0 unfolding a_def
    by (metis Q\<^sub>p_def Zp_def Zp_int_inc_closed \<iota>_def inc_to_Zp padic_fields.inc_of_int padic_fields_axioms)
  have 2: "([s]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) n = s"
    using assms
    by (metis Zp_int_inc_res mod_pos_pos_trivial p_residue_ring_car_memE(1) p_residue_ring_car_memE(2))
  have 3: "{x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). c x \<in> \<O>\<^sub>p \<and> to_Zp (c x) n = s} = c  \<inverse>\<^bsub>k\<^esub> B\<^bsub>n\<^esub>[a]"
  proof
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). c x \<in> \<O>\<^sub>p \<and> to_Zp (c x) n = s} \<subseteq> c \<inverse>\<^bsub>k\<^esub> B\<^bsub>int n\<^esub>[a]"
    proof fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). c x \<in> \<O>\<^sub>p \<and> to_Zp (c x) n = s}"
      then have  30: "x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)" by blast
      have 31: "c x \<in> \<O>\<^sub>p" using A by blast
      have 32: "to_Zp (c x) n = s" using A by blast
      have 33: "to_Zp (c x) \<in> carrier Z\<^sub>p"
        using 31 val_ring_memE to_Zp_closed by blast
      have 34: "to_Zp (c x) n = (to_Zp a) n"
        using "1" "2" "32" by presburger
      hence "((to_Zp (c x)) \<ominus>\<^bsub>Z\<^sub>p\<^esub> (to_Zp a)) n = 0"
        using "1" "33" Zp_int_inc_closed res_diff_zero_fact'' by presburger
      hence 35: "val_Zp ((to_Zp (c x)) \<ominus>\<^bsub>Z\<^sub>p\<^esub> (to_Zp a)) \<ge> n"
        using "1" "33" "34" Zp.one_closed Zp_int_mult_closed val_Zp_dist_def val_Zp_dist_res_eq2 by presburger
      have 36: "val (c x \<ominus> a) = val_Zp ((to_Zp (c x)) \<ominus>\<^bsub>Z\<^sub>p\<^esub> (to_Zp a))"
        using 31 0
        by (metis to_Zp_minus to_Zp_val val_ring_minus_closed)
      hence "val (c x \<ominus> a) \<ge> n"
        using 35 by presburger
      hence "c x \<in>  B\<^bsub>int n\<^esub>[a]"
        using 31 c_ballI  val_ring_memE by blast
      thus "x \<in> c \<inverse>\<^bsub>k\<^esub> B\<^bsub>int n\<^esub>[a]"
        using 30  by blast
    qed
    show "c \<inverse>\<^bsub>k\<^esub> B\<^bsub>int n\<^esub>[a] \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). c x \<in> \<O>\<^sub>p \<and> to_Zp (c x) n = s}"
    proof fix x assume A: "x \<in> c \<inverse>\<^bsub>k\<^esub> B\<^bsub>int n\<^esub>[a]"
      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
        using A  by (meson evimage_eq)
      have 00: "val (c x \<ominus> a) \<ge> n"
        using A c_ballE(2) by blast
      have cx_closed: "c x \<in> carrier Q\<^sub>p"
        using x_closed assms function_ring_car_closed SA_car_memE(2) by blast
      hence 11: "c x \<ominus> a \<in> \<O>\<^sub>p"
      proof-
        have "(0::eint) \<le> n"
          by (metis eint_ord_simps(1) of_nat_0_le_iff zero_eint_def)
        thus ?thesis using 00 order_trans[of "0::eint" n] Qp_val_ringI
          by (meson "0" Qp.minus_closed val_ring_memE cx_closed)
      qed
      hence 22: "c x \<in> \<O>\<^sub>p"
      proof-
        have 00: "c x = (c x \<ominus> a) \<oplus> a"
          using cx_closed 0
          by (metis "11" Qp.add.inv_solve_right' Qp.minus_eq val_ring_memE(2))
        have 01: "(c x \<ominus> a) \<oplus> a \<in> \<O>\<^sub>p"
          by(intro val_ring_add_closed 0 11)
        then show ?thesis
          using 0 11 image_iff  "00" by auto
      qed
      have 33: "val (c x \<ominus> a) = val_Zp (to_Zp (c x) \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp a)"
        using 11 22 0
        by (metis to_Zp_minus to_Zp_val)
      have 44: "val_Zp (to_Zp (c x) \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp a) \<ge> n"
        using 33 00 by presburger
      have tzpcx: "to_Zp (c x) \<in> carrier Z\<^sub>p"
        using 22 by (metis image_iff inc_to_Zp)
      have tzpa: "to_Zp a \<in> carrier Z\<^sub>p"
        using 0 val_ring_memE to_Zp_closed by blast
      have 55: "(to_Zp (c x) \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp a) n = 0"
        using 44 tzpcx tzpa Zp.minus_closed zero_below_val_Zp by blast
      hence 66: "to_Zp (c x) n = s"
        using 0 1 2 tzpa tzpcx
        by (metis res_diff_zero_fact(1))
      then show "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). c x \<in> \<O>\<^sub>p \<and> to_Zp (c x) n = s}"
        using "22" x_closed by blast
    qed
  qed
  thus ?thesis
    using evimage_is_semialg[of c k] 0  val_ring_memE assms(2) ball_is_univ_semialgebraic by presburger
qed

lemma SA_constant_res_set_semialg':
  assumes "f \<in> carrier (SA m)"
  assumes "C \<in> Qp_res_classes n"
  shows "is_semialgebraic m (f  \<inverse>\<^bsub>m\<^esub> C)"
proof-
  obtain l where l_def: "l \<in> carrier (Zp_res_ring n) \<and> C = Qp_res_class n ([l]\<cdot>\<one>)"
    using Qp_res_classes_wits assms by blast
  have C_eq: "C = Qp_res_class n ([l]\<cdot>\<one>)"
    using l_def by blast
  have 0: "Qp_res ([l] \<cdot> \<one>) n = l"
    using l_def
    by (metis Qp_res_int_inc mod_pos_pos_trivial p_residue_ring_car_memE(1) p_residue_ring_car_memE(2))
  have 1: "f  \<inverse>\<^bsub>m\<^esub> C = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). f x \<in> \<O>\<^sub>p \<and> Qp_res (f x) n = l}"
    apply(rule equalityI')
    unfolding evimage_def C_eq Qp_res_class_def mem_Collect_eq unfolding 0 apply blast
    by blast
  show ?thesis
    unfolding 1 apply(rule SA_constant_res_set_semialg )
    using  l_def apply blast by(rule assms)
qed


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Semialgebraic Polynomials\<close>
(**************************************************************************************************)
(**************************************************************************************************)


lemma UP_SA_n_is_ring:
  shows "ring (UP (SA n))"
  using SA_is_ring
  by (simp add: UP_ring.UP_ring UP_ring.intro)

lemma UP_SA_n_is_cring:
  shows "cring (UP (SA n))"
  using SA_is_cring
  by (simp add: UP_cring.UP_cring UP_cring.intro)

text\<open>The evaluation homomorphism from \texttt{Qp\_funs} to \texttt{Qp}\<close>

definition eval_hom where
"eval_hom a = (\<lambda>f. f a)"

lemma eval_hom_is_hom:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "ring_hom_ring (Fun\<^bsub>n\<^esub> Q\<^sub>p) Q\<^sub>p (eval_hom a)"
  apply(rule ring_hom_ringI)
  using Qp_funs_is_cring cring.axioms(1) apply blast
  apply (simp add: Qp.ring_axioms)
  apply (simp add: Qp.function_ring_car_mem_closed assms eval_hom_def)
  apply (metis Qp_funs_mult' assms eval_hom_def)
  apply (metis Qp_funs_add' assms eval_hom_def)
  by (metis function_one_eval assms eval_hom_def)

text\<open>the homomorphism from \texttt{Fun n Qp [x]} to \texttt{Qp [x]} induced by evaluation of coefficients\<close>

definition Qp_fpoly_to_Qp_poly where
"Qp_fpoly_to_Qp_poly n a = poly_lift_hom (Fun\<^bsub>n\<^esub> Q\<^sub>p) Q\<^sub>p (eval_hom a)"

lemma Qp_fpoly_to_Qp_poly_is_hom:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "(Qp_fpoly_to_Qp_poly n a) \<in> ring_hom (UP (Fun\<^bsub>n\<^esub> Q\<^sub>p)) (Q\<^sub>p_x) "
  unfolding Qp_fpoly_to_Qp_poly_def
  apply(rule UP_cring.poly_lift_hom_is_hom)
  unfolding UP_cring_def
  apply (simp add: Qp_funs_is_cring)
  apply (simp add: UPQ.R_cring)
  using assms eval_hom_is_hom[of a] ring_hom_ring.homh by blast

lemma Qp_fpoly_to_Qp_poly_extends_apply:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f \<in> carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
  shows "Qp_fpoly_to_Qp_poly n a (to_polynomial (Fun\<^bsub>n\<^esub> Q\<^sub>p) f) = to_polynomial Q\<^sub>p (f a)"
  unfolding Qp_fpoly_to_Qp_poly_def
  using assms eval_hom_is_hom[of a] UP_cring.poly_lift_hom_extends_hom[of "Fun\<^bsub>n\<^esub> Q\<^sub>p" Q\<^sub>p "eval_hom a" ]
        Qp.function_ring_car_memE[of f n] ring_hom_ring.homh
  unfolding eval_hom_def UP_cring_def
  using Qp_funs_is_cring UPQ.R_cring by blast

lemma Qp_fpoly_to_Qp_poly_X_var:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "Qp_fpoly_to_Qp_poly n a (X_poly (Fun\<^bsub>n\<^esub> Q\<^sub>p)) = X_poly Q\<^sub>p"
  unfolding X_poly_def Qp_fpoly_to_Qp_poly_def
  apply(rule UP_cring.poly_lift_hom_X_var) unfolding UP_cring_def
    apply (simp add: Qp_funs_is_cring)
      apply (simp add: UPQ.R_cring)
        using assms(1) eval_hom_is_hom ring_hom_ring.homh
  by blast

lemma Qp_fpoly_to_Qp_poly_monom:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f \<in> carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
  shows "Qp_fpoly_to_Qp_poly n a (up_ring.monom (UP (Fun\<^bsub>n\<^esub> Q\<^sub>p)) f m) = up_ring.monom Q\<^sub>p_x (f a) m"
  unfolding Qp_fpoly_to_Qp_poly_def
  using UP_cring.poly_lift_hom_monom[of "Fun\<^bsub>n\<^esub> Q\<^sub>p" Q\<^sub>p "eval_hom a" f m] assms ring_hom_ring.homh
        eval_hom_is_hom[of a] unfolding eval_hom_def UP_cring_def
  using Qp_funs_is_cring UPQ.R_cring by blast

lemma Qp_fpoly_to_Qp_poly_coeff:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f \<in> carrier (UP (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
  shows "Qp_fpoly_to_Qp_poly n a f k = (f k) a"
  using assms UP_cring.poly_lift_hom_cf[of "Fun\<^bsub>n\<^esub> Q\<^sub>p" Q\<^sub>p "eval_hom a" f k] eval_hom_is_hom[of a]
  unfolding  Qp_fpoly_to_Qp_poly_def eval_hom_def
  using Qp_funs_is_cring ring_hom_ring.homh  ring_hom_ring.homh
  unfolding eval_hom_def UP_cring_def
  using UPQ.R_cring by blast

lemma Qp_fpoly_to_Qp_poly_eval:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "P \<in> carrier (UP (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
  assumes "f \<in> carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
  shows "(UP_cring.to_fun (Fun\<^bsub>n\<^esub> Q\<^sub>p) P f) a  = UP_cring.to_fun Q\<^sub>p (Qp_fpoly_to_Qp_poly n a P) (f a)"
  unfolding Qp_fpoly_to_Qp_poly_def
  using UP_cring.poly_lift_hom_eval[of "Fun\<^bsub>n\<^esub> Q\<^sub>p" Q\<^sub>p "eval_hom a" P f]
        eval_hom_is_hom[of a] eval_hom_def assms ring_hom_ring.homh Qp_funs_is_cring
  unfolding eval_hom_def UP_cring_def
  using UPQ.R_cring by blast

lemma Qp_fpoly_to_Qp_poly_sub:
  assumes "f \<in> carrier (UP (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
  assumes "g \<in> carrier (UP (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "Qp_fpoly_to_Qp_poly n a (compose (Fun\<^bsub>n\<^esub> Q\<^sub>p) f g) = compose Q\<^sub>p (Qp_fpoly_to_Qp_poly n a f) (Qp_fpoly_to_Qp_poly n a g)"
  unfolding Qp_fpoly_to_Qp_poly_def
  using assms UP_cring.poly_lift_hom_sub[of "Fun\<^bsub>n\<^esub> Q\<^sub>p" Q\<^sub>p "eval_hom a" f g]
        eval_hom_is_hom[of a] ring_hom_ring.homh[of "Fun\<^bsub>n\<^esub> Q\<^sub>p" Q\<^sub>p "eval_hom a"]
        Qp_funs_is_cring
  unfolding eval_hom_def UP_cring_def
  using UPQ.R_cring by blast

lemma Qp_fpoly_to_Qp_poly_taylor_poly:
  assumes "F \<in> carrier (UP (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
  assumes "c \<in> carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "Qp_fpoly_to_Qp_poly n a (taylor_expansion (Fun\<^bsub>n\<^esub> Q\<^sub>p) c F) =
        taylor_expansion Q\<^sub>p (c a) (Qp_fpoly_to_Qp_poly n a F)"
proof-
  have 0: "X_poly (Fun\<^bsub>n\<^esub> Q\<^sub>p) \<oplus>\<^bsub>UP (Fun\<^bsub>n\<^esub> Q\<^sub>p)\<^esub> to_polynomial (Fun\<^bsub>n\<^esub> Q\<^sub>p) c \<in> carrier (UP (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
    by (metis Qp_funs_is_cring UP_cring.X_plus_closed UP_cring_def X_poly_plus_def assms(2))
  have 1: "poly_lift_hom (Fun\<^bsub>n\<^esub> Q\<^sub>p) Q\<^sub>p (eval_hom a) (X_poly (Fun\<^bsub>n\<^esub> Q\<^sub>p) \<oplus>\<^bsub>UP (Fun\<^bsub>n\<^esub> Q\<^sub>p)\<^esub> to_polynomial (Fun\<^bsub>n\<^esub> Q\<^sub>p) c) = X_poly Q\<^sub>p \<oplus>\<^bsub>Q\<^sub>p_x\<^esub> UPQ.to_poly (c a)"
  proof-
    have 10: "poly_lift_hom (Fun\<^bsub>n\<^esub> Q\<^sub>p) Q\<^sub>p (eval_hom a) \<in> ring_hom (UP (Fun\<^bsub>n\<^esub> Q\<^sub>p)) Q\<^sub>p_x"
      using Qp_fpoly_to_Qp_poly_def Qp_fpoly_to_Qp_poly_is_hom assms
      by presburger
    have 11: " to_polynomial (Fun\<^bsub>n\<^esub> Q\<^sub>p) c \<in> carrier (UP (Fun\<^bsub>n\<^esub> Q\<^sub>p))"
      by (meson Qp_funs_is_cring UP_cring.intro UP_cring.to_poly_closed assms)
    have 12: "X_poly (Fun\<^bsub>n\<^esub> Q\<^sub>p) \<in> carrier (UP (Fun\<^bsub>n\<^esub> Q\<^sub>p)) "
      using UP_cring.X_closed[of "Fun\<^bsub>n\<^esub> Q\<^sub>p"] unfolding UP_cring_def
      using Qp_funs_is_cring
      by blast
    have "Qp_fpoly_to_Qp_poly n a (X_poly (Fun\<^bsub>n\<^esub> Q\<^sub>p) \<oplus>\<^bsub>UP (Fun\<^bsub>n\<^esub> Q\<^sub>p)\<^esub> to_polynomial (Fun\<^bsub>n\<^esub> Q\<^sub>p) c) =
    Qp_fpoly_to_Qp_poly n a (X_poly (Fun\<^bsub>n\<^esub> Q\<^sub>p)) \<oplus>\<^bsub>Q\<^sub>p_x\<^esub> Qp_fpoly_to_Qp_poly n a (to_polynomial (Fun\<^bsub>n\<^esub> Q\<^sub>p) c)"
      using assms 0 10 11 12 Qp_fpoly_to_Qp_poly_extends_apply[of a n c] Qp_fpoly_to_Qp_poly_is_hom[of a] Qp_fpoly_to_Qp_poly_X_var[of a]
      using ring_hom_add[of "Qp_fpoly_to_Qp_poly n a"  "UP (Fun\<^bsub>n\<^esub> Q\<^sub>p)" Q\<^sub>p_x "X_poly (Fun\<^bsub>n\<^esub> Q\<^sub>p)" "to_polynomial (Fun\<^bsub>n\<^esub> Q\<^sub>p) c" ]
      unfolding Qp_fpoly_to_Qp_poly_def
      by blast
     then show ?thesis
       using Qp_fpoly_to_Qp_poly_X_var Qp_fpoly_to_Qp_poly_def Qp_fpoly_to_Qp_poly_extends_apply assms
       by metis
  qed
  have 2: "poly_lift_hom (Fun\<^bsub>n\<^esub> Q\<^sub>p) Q\<^sub>p (eval_hom a) (compose (Fun\<^bsub>n\<^esub> Q\<^sub>p) F (X_poly (Fun\<^bsub>n\<^esub> Q\<^sub>p) \<oplus>\<^bsub>UP (Fun\<^bsub>n\<^esub> Q\<^sub>p)\<^esub> to_polynomial (Fun\<^bsub>n\<^esub> Q\<^sub>p) c)) =
   UPQ.sub (poly_lift_hom (Fun\<^bsub>n\<^esub> Q\<^sub>p) Q\<^sub>p (eval_hom a) F)
    (poly_lift_hom (Fun\<^bsub>n\<^esub> Q\<^sub>p) Q\<^sub>p (eval_hom a) (X_poly (Fun\<^bsub>n\<^esub> Q\<^sub>p) \<oplus>\<^bsub>UP (Fun\<^bsub>n\<^esub> Q\<^sub>p)\<^esub> to_polynomial (Fun\<^bsub>n\<^esub> Q\<^sub>p) c))"
    using 0 1 Qp_fpoly_to_Qp_poly_sub[of F n "X_poly_plus (Fun\<^bsub>n\<^esub> Q\<^sub>p) c" a] assms
    unfolding Qp_fpoly_to_Qp_poly_def X_poly_plus_def
    by blast
  show ?thesis
    using assms 0 1
    unfolding Qp_fpoly_to_Qp_poly_def  taylor_expansion_def X_poly_plus_def
    using "2" by presburger
qed

lemma SA_is_UP_cring:
  shows "UP_cring (SA n)"
  unfolding UP_cring_def
  by (simp add: SA_is_cring)

lemma eval_hom_is_SA_hom:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "ring_hom_ring (SA n) Q\<^sub>p (eval_hom a)"
  apply(rule ring_hom_ringI)
  using SA_is_cring cring.axioms(1) assms(1) apply blast
  using Qp.ring_axioms apply blast
  apply (metis (no_types, lifting) SA_car assms eval_hom_def Qp.function_ring_car_mem_closed semialg_functions_memE(2))
  apply (metis (mono_tags, lifting) Qp_funs_mult' SA_car SA_times assms eval_hom_def semialg_functions_memE(2))
  apply (metis (mono_tags, lifting) Qp_funs_add' SA_car SA_plus assms eval_hom_def semialg_functions_memE(2))
  using Qp_constE Qp.one_closed SA_one assms eval_hom_def function_one_as_constant
  by (metis function_one_eval)

text\<open>the homomorphism from \texttt{(SA n)[x]} to \texttt{Qp [x]} induced by evaluation of coefficients\<close>

definition SA_poly_to_Qp_poly where
"SA_poly_to_Qp_poly n a = poly_lift_hom (SA n) Q\<^sub>p (eval_hom a)"

lemma SA_poly_to_Qp_poly_is_hom:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "(SA_poly_to_Qp_poly n a) \<in> ring_hom (UP (SA n)) (Q\<^sub>p_x) "
  unfolding SA_poly_to_Qp_poly_def
  apply(rule UP_cring.poly_lift_hom_is_hom)
  using SA_is_cring assms(1) UP_cring.intro apply blast
  apply (simp add: UPQ.R_cring)
  using assms eval_hom_is_SA_hom ring_hom_ring.homh by blast

lemma SA_poly_to_Qp_poly_closed:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "P \<in> carrier (UP (SA n))"
  shows "SA_poly_to_Qp_poly n a P \<in> carrier Q\<^sub>p_x"
  using assms SA_poly_to_Qp_poly_is_hom[of a] ring_hom_closed[of "SA_poly_to_Qp_poly n a" "UP (SA n)" Q\<^sub>p_x P]
  by blast

lemma SA_poly_to_Qp_poly_add:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f \<in> carrier (UP (SA n))"
  assumes "g \<in> carrier (UP (SA n))"
  shows "SA_poly_to_Qp_poly n a (f \<oplus>\<^bsub>UP (SA n)\<^esub> g) = SA_poly_to_Qp_poly n a f \<oplus>\<^bsub>Q\<^sub>p_x\<^esub> SA_poly_to_Qp_poly n a g"
  using SA_poly_to_Qp_poly_is_hom ring_hom_add assms
  by (metis (no_types, opaque_lifting))

lemma SA_poly_to_Qp_poly_minus:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f \<in> carrier (UP (SA n))"
  assumes "g \<in> carrier (UP (SA n))"
   shows "SA_poly_to_Qp_poly n a (f \<ominus>\<^bsub>UP (SA n)\<^esub> g) = SA_poly_to_Qp_poly n a f \<ominus>\<^bsub>Q\<^sub>p_x\<^esub> SA_poly_to_Qp_poly n a g"
  using SA_poly_to_Qp_poly_is_hom[of a] assms SA_is_ring[of n]
        ring.ring_hom_minus[of "UP (SA n)" Q\<^sub>p_x "SA_poly_to_Qp_poly n a" f g] UP_SA_n_is_ring
        UPQ.UP_ring
  by blast

lemma SA_poly_to_Qp_poly_mult:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f \<in> carrier (UP (SA n))"
  assumes "g \<in> carrier (UP (SA n))"
  shows "SA_poly_to_Qp_poly n a (f \<otimes>\<^bsub>UP (SA n)\<^esub> g) = SA_poly_to_Qp_poly n a f \<otimes>\<^bsub>Q\<^sub>p_x\<^esub> SA_poly_to_Qp_poly n a g"
  using SA_poly_to_Qp_poly_is_hom ring_hom_mult assms
  by (metis (no_types, opaque_lifting))

lemma SA_poly_to_Qp_poly_extends_apply:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f \<in> carrier (SA n)"
  shows "SA_poly_to_Qp_poly n a (to_polynomial (SA n) f) = to_polynomial Q\<^sub>p (f a)"
  unfolding SA_poly_to_Qp_poly_def
  using assms eval_hom_is_SA_hom[of a] UP_cring.poly_lift_hom_extends_hom[of "SA n" Q\<^sub>p "eval_hom a" f]
         eval_hom_def   SA_is_cring Qp.cring_axioms ring_hom_ring.homh
  unfolding eval_hom_def UP_cring_def
  by blast

lemma SA_poly_to_Qp_poly_X_var:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "SA_poly_to_Qp_poly n a (X_poly (SA n)) = X_poly Q\<^sub>p"
  unfolding X_poly_def SA_poly_to_Qp_poly_def
  apply(rule UP_cring.poly_lift_hom_X_var)
    using SA_is_cring assms(1)
    using UP_cring.intro apply blast
    apply (simp add: Qp.cring_axioms)
    using assms eval_hom_is_SA_hom ring_hom_ring.homh by blast

lemma SA_poly_to_Qp_poly_X_plus:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "c \<in> carrier (SA n)"
  shows "SA_poly_to_Qp_poly n a (X_poly_plus (SA n) c) = UPQ.X_plus (c a)"
  unfolding X_poly_plus_def
  using assms SA_poly_to_Qp_poly_add[of a n "X_poly (SA n)" "to_polynomial (SA n) c"]
        SA_poly_to_Qp_poly_extends_apply[of a n c] UP_cring.X_closed[of "SA n"] SA_is_cring[of n]
        SA_poly_to_Qp_poly_X_var[of a] UP_cring.to_poly_closed[of "SA n" c]
  unfolding UP_cring_def
  by metis

lemma SA_poly_to_Qp_poly_X_minus:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "c \<in> carrier (SA n)"
  shows "SA_poly_to_Qp_poly n a (X_poly_minus (SA n) c) = UPQ.X_minus (c a)"
  unfolding X_poly_minus_def
  using assms SA_poly_to_Qp_poly_minus[of a n "X_poly (SA n)" "to_polynomial (SA n) c"]
        SA_poly_to_Qp_poly_extends_apply[of a n c] UP_cring.X_closed[of "SA n"] SA_is_cring[of n]
        SA_poly_to_Qp_poly_X_var[of a n] UP_cring.to_poly_closed[of "SA n" c]
  unfolding UP_cring_def
  by metis

lemma SA_poly_to_Qp_poly_monom:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f \<in> carrier (SA n)"
  shows "SA_poly_to_Qp_poly n a (up_ring.monom (UP (SA n)) f m) = up_ring.monom Q\<^sub>p_x (f a) m"
  unfolding SA_poly_to_Qp_poly_def
  using UP_cring.poly_lift_hom_monom[of "SA n" Q\<^sub>p "eval_hom a" f n] assms eval_hom_is_SA_hom eval_hom_def
   SA_is_cring Qp.cring_axioms UP_cring.poly_lift_hom_monom ring_hom_ring.homh
  by (metis UP_cring.intro)

lemma SA_poly_to_Qp_poly_coeff:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f \<in> carrier (UP (SA n))"
  shows "SA_poly_to_Qp_poly n a f k = (f k) a"
  using assms UP_cring.poly_lift_hom_cf[of "SA n" Q\<^sub>p "eval_hom a" f k] eval_hom_is_SA_hom[of a]
  using SA_is_cring Qp.cring_axioms ring_hom_ring.homh
  unfolding  SA_poly_to_Qp_poly_def eval_hom_def UP_cring_def
  by blast

lemma SA_poly_to_Qp_poly_eval:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "P \<in> carrier (UP (SA n))"
  assumes "f \<in> carrier (SA n)"
  shows "(UP_cring.to_fun (SA n) P f) a  = UP_cring.to_fun Q\<^sub>p (SA_poly_to_Qp_poly n a P) (f a)"
  unfolding SA_poly_to_Qp_poly_def
  using UP_cring.poly_lift_hom_eval[of "SA n" Q\<^sub>p "eval_hom a" P f]
        eval_hom_is_SA_hom[of a] eval_hom_def assms SA_is_cring Qp.cring_axioms ring_hom_ring.homh
  unfolding  SA_poly_to_Qp_poly_def eval_hom_def UP_cring_def
  by blast

lemma SA_poly_to_Qp_poly_sub:
  assumes "f \<in> carrier (UP (SA n))"
  assumes "g \<in> carrier (UP (SA n))"
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "SA_poly_to_Qp_poly n a (compose (SA n) f g) = compose Q\<^sub>p (SA_poly_to_Qp_poly n a f) (SA_poly_to_Qp_poly n a g)"
  unfolding SA_poly_to_Qp_poly_def
  using assms UP_cring.poly_lift_hom_sub[of "SA n" Q\<^sub>p "eval_hom a" f g]
        eval_hom_is_SA_hom[of a] ring_hom_ring.homh[of "SA n" Q\<^sub>p "eval_hom a"]
        SA_is_cring Qp.cring_axioms
  unfolding  SA_poly_to_Qp_poly_def eval_hom_def UP_cring_def
  by blast

lemma SA_poly_to_Qp_poly_deg_bound:
  assumes "g \<in> carrier (UP (SA m))"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "deg Q\<^sub>p (SA_poly_to_Qp_poly m x g) \<le> deg (SA m) g"
  apply(rule  UPQ.deg_leqI)
    using assms SA_poly_to_Qp_poly_closed[of x m g] apply blast
  proof- fix n assume A: "deg (SA m) g < n"
    then have "g n = \<zero>\<^bsub>SA m\<^esub>"
      using assms SA_is_UP_cring[of m] UP_cring.UP_car_memE(2) by blast
    thus "SA_poly_to_Qp_poly m x g n = \<zero>"
      using assms SA_poly_to_Qp_poly_coeff[of x m g n] function_zero_eval SA_zero by presburger
  qed

lemma SA_poly_to_Qp_poly_taylor_poly:
  assumes "F \<in> carrier (UP (SA n))"
  assumes "c \<in> carrier (SA n)"
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "SA_poly_to_Qp_poly n a (taylor_expansion (SA n) c F) =
        taylor_expansion Q\<^sub>p (c a) (SA_poly_to_Qp_poly n a F)"
  unfolding SA_poly_to_Qp_poly_def using assms Qp.cring_axioms SA_is_cring eval_hom_def
      eval_hom_is_SA_hom UP_cring.poly_lift_hom_comm_taylor_expansion[of "SA n" Q\<^sub>p "eval_hom a" F c] ring_hom_ring.homh
  unfolding  SA_poly_to_Qp_poly_def eval_hom_def UP_cring_def
  by metis

lemma SA_poly_to_Qp_poly_comm_taylor_term:
  assumes "F \<in> carrier (UP (SA n))"
  assumes "c \<in> carrier (SA n)"
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "SA_poly_to_Qp_poly n a (UP_cring.taylor_term (SA n) c F i) =
        UP_cring.taylor_term Q\<^sub>p (c a) (SA_poly_to_Qp_poly n a F) i"
  unfolding SA_poly_to_Qp_poly_def using assms  Qp.cring_axioms SA_is_cring eval_hom_def
      eval_hom_is_SA_hom UP_cring.poly_lift_hom_comm_taylor_term[of "SA n" Q\<^sub>p "eval_hom a" F c i] ring_hom_ring.homh
  unfolding  SA_poly_to_Qp_poly_def eval_hom_def UP_cring_def
  by metis

lemma SA_poly_to_Qp_poly_comm_pderiv:
  assumes "F \<in> carrier (UP (SA n))"
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "SA_poly_to_Qp_poly n a (UP_cring.pderiv (SA n) F) =
        UP_cring.pderiv Q\<^sub>p (SA_poly_to_Qp_poly n a F)"
  apply(rule UP_ring.poly_induct3[of "SA n" F]) unfolding UP_ring_def
  apply (simp add: SA_is_ring assms(1))
  using assms apply blast
proof-
  show "\<And>p q. q \<in> carrier (UP (SA n)) \<Longrightarrow>
           p \<in> carrier (UP (SA n)) \<Longrightarrow>
           SA_poly_to_Qp_poly n a (UP_cring.pderiv (SA n) p) = UPQ.pderiv (SA_poly_to_Qp_poly n a p) \<Longrightarrow>
           SA_poly_to_Qp_poly n a (UP_cring.pderiv (SA n) q) = UPQ.pderiv (SA_poly_to_Qp_poly n a q) \<Longrightarrow>
           SA_poly_to_Qp_poly n a (UP_cring.pderiv (SA n) (p \<oplus>\<^bsub>UP (SA n)\<^esub> q)) = UPQ.pderiv (SA_poly_to_Qp_poly n a (p \<oplus>\<^bsub>UP (SA n)\<^esub> q))"
  proof- fix p q assume A: "q \<in> carrier (UP (SA n))"
           "p \<in> carrier (UP (SA n))"
           "SA_poly_to_Qp_poly n a (UP_cring.pderiv (SA n) p) = UPQ.pderiv (SA_poly_to_Qp_poly n a p)"
           "SA_poly_to_Qp_poly n a (UP_cring.pderiv (SA n) q) = UPQ.pderiv (SA_poly_to_Qp_poly n a q)"
    show "SA_poly_to_Qp_poly n a (UP_cring.pderiv (SA n) (p \<oplus>\<^bsub>UP (SA n)\<^esub> q)) = UPQ.pderiv (SA_poly_to_Qp_poly n a (p \<oplus>\<^bsub>UP (SA n)\<^esub> q))"
    proof-
      have 0: "SA_poly_to_Qp_poly n a p \<in> carrier (UP Q\<^sub>p)"
        using A assms SA_poly_to_Qp_poly_closed[of a n p]
        by blast
      have 1: "SA_poly_to_Qp_poly n a q \<in> carrier (UP Q\<^sub>p)"
        using A SA_poly_to_Qp_poly_closed[of a n q] assms by blast
      have 2: "UPQ.pderiv (SA_poly_to_Qp_poly n a p) \<in> carrier (UP Q\<^sub>p)"
        using  UPQ.pderiv_closed[of "SA_poly_to_Qp_poly n a p"] 0  by blast
      have 3: "UPQ.pderiv (SA_poly_to_Qp_poly n a q) \<in> carrier (UP Q\<^sub>p)"
        using A assms  UPQ.pderiv_closed[of "SA_poly_to_Qp_poly n a q"] 1 by blast
      have 4: "UP_cring.pderiv (SA n) p \<in> carrier (UP (SA n))"
        using A UP_cring.pderiv_closed[of "SA n" p] unfolding UP_cring_def
        using SA_is_cring assms(1) by blast
      have 5: "UP_cring.pderiv (SA n) q \<in> carrier (UP (SA n))"
        using A UP_cring.pderiv_closed[of "SA n" q] unfolding UP_cring_def
        using SA_is_cring assms(1) by blast
      have 6: "SA_poly_to_Qp_poly n a (UP_cring.pderiv (SA n) p \<oplus>\<^bsub>UP (SA n)\<^esub> UP_cring.pderiv (SA n) q) =
    SA_poly_to_Qp_poly n a (UP_cring.pderiv (SA n) p) \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> SA_poly_to_Qp_poly n a (UP_cring.pderiv (SA n) q)"
        using A 4 5 SA_poly_to_Qp_poly_add assms  by blast
      have 7: "UPQ.pderiv (SA_poly_to_Qp_poly n a p \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> SA_poly_to_Qp_poly n a q) =
    UPQ.pderiv (SA_poly_to_Qp_poly n a p) \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> UPQ.pderiv (SA_poly_to_Qp_poly n a q)"
        using "0" "1" UPQ.pderiv_add by blast
      have 8: "UP_cring.pderiv (SA n) (p \<oplus>\<^bsub>UP (SA n)\<^esub> q) = UP_cring.pderiv (SA n) p \<oplus>\<^bsub>UP (SA n)\<^esub> UP_cring.pderiv (SA n) q"
        using A assms UP_cring.pderiv_add[of "SA n" p q]
        unfolding UP_cring_def  using SA_is_cring by blast
      have 9: "SA_poly_to_Qp_poly n a (UP_cring.pderiv (SA n) (p \<oplus>\<^bsub>UP (SA n)\<^esub> q)) =
    UPQ.pderiv (SA_poly_to_Qp_poly n a p) \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> UPQ.pderiv (SA_poly_to_Qp_poly n a q)"
        using A 6 8 by presburger
      have 10: "UPQ.pderiv (SA_poly_to_Qp_poly n a (p \<oplus>\<^bsub>UP (SA n)\<^esub> q)) =
    UPQ.pderiv (SA_poly_to_Qp_poly n a p) \<oplus> \<^bsub>UP Q\<^sub>p\<^esub> UPQ.pderiv (SA_poly_to_Qp_poly n a q)"
        using "7" A(1) A(2) SA_poly_to_Qp_poly_add assms  by presburger
      show ?thesis using 9 10
        by presburger
    qed
  qed
  show "\<And>aa na.
       aa \<in> carrier (SA n) \<Longrightarrow>
       SA_poly_to_Qp_poly n a (UP_cring.pderiv (SA n) (up_ring.monom (UP (SA n)) aa na)) =
       UPQ.pderiv (SA_poly_to_Qp_poly n a (up_ring.monom (UP (SA n)) aa na))"
  proof- fix b m assume A: "b \<in> carrier (SA n)"
    show "SA_poly_to_Qp_poly n a (UP_cring.pderiv (SA n) (up_ring.monom (UP (SA n)) b m)) =
       UPQ.pderiv (SA_poly_to_Qp_poly n a (up_ring.monom (UP (SA n)) b m))"
    proof-
      have 0: "(UP_cring.pderiv (SA n) (up_ring.monom (UP (SA n)) b m)) =
              (up_ring.monom (UP (SA n)) ([m]\<cdot>\<^bsub>SA n\<^esub>b) (m-1))"
        using UP_cring.pderiv_monom[of "SA n" b m] unfolding UP_cring_def
        using SA_is_cring \<open>b \<in> carrier (SA n)\<close> assms(1) by blast
      have 1: "(SA_poly_to_Qp_poly n a (up_ring.monom (UP (SA n)) b m)) =up_ring.monom (UP Q\<^sub>p) (b a) m"
        using SA_poly_to_Qp_poly_monom \<open>b \<in> carrier (SA n)\<close> assms  by blast
      have 2: "b a \<in> carrier Q\<^sub>p"
        using A assms Qp.function_ring_car_mem_closed SA_car_memE(2) by metis
      hence 3: "UPQ.pderiv (SA_poly_to_Qp_poly n a (up_ring.monom (UP (SA n)) b m)) = up_ring.monom (UP Q\<^sub>p) ([m]\<cdot>(b a)) (m-1)"
        using 1 2 A UPQ.pderiv_monom[of "b a" m]
        by presburger
      have 4: "[m] \<cdot>\<^bsub>SA n\<^esub> b \<in> carrier (SA n)"
        using A assms  SA_is_cring[of n] ring.add_pow_closed[of "SA n" b m] SA_is_ring
        by blast
      have 5: "SA_poly_to_Qp_poly n a (up_ring.monom (UP (SA n)) ([m] \<cdot>\<^bsub>SA n\<^esub> b) (m-1)) = up_ring.monom (UP Q\<^sub>p) (([m] \<cdot>\<^bsub>SA n\<^esub> b) a) (m-1)"
        using SA_poly_to_Qp_poly_monom[of a n "[m]\<cdot>\<^bsub>SA n\<^esub>b" "m-1"] assms 4 by blast
      have 6: "SA_poly_to_Qp_poly n a (UP_cring.pderiv (SA n) (up_ring.monom (UP (SA n)) b m)) = up_ring.monom (UP Q\<^sub>p) (([m] \<cdot>\<^bsub>SA n\<^esub> b) a) (m - 1)"
         using 5 0  by presburger
      thus ?thesis using assms A 3 6 SA_add_pow_apply[of b n a]
        by auto
    qed
  qed
qed

lemma SA_poly_to_Qp_poly_pderiv:
  assumes "g \<in> carrier (UP (SA m))"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "UPQ.pderiv (SA_poly_to_Qp_poly m x g) = (SA_poly_to_Qp_poly m x (pderiv m g))"
proof
  fix n
  have 0: "UPQ.pderiv (SA_poly_to_Qp_poly m x g) n = [Suc n] \<cdot> SA_poly_to_Qp_poly m x g (Suc n)"
    by(rule UPQ.pderiv_cfs[of "SA_poly_to_Qp_poly m x g"n], rule SA_poly_to_Qp_poly_closed, rule assms , rule assms)
  have 1: "SA_poly_to_Qp_poly m x (UPSA.pderiv m g) n = UPSA.pderiv m g n x"
    by(rule SA_poly_to_Qp_poly_coeff[of x m "UPSA.pderiv m g" n], rule assms, rule UPSA.pderiv_closed, rule assms)
  have 2: "SA_poly_to_Qp_poly m x (UPSA.pderiv m g) n = ([Suc n] \<cdot>\<^bsub>SA m\<^esub> g (Suc n)) x"
    using UPSA.pderiv_cfs[of g m n] assms unfolding 1 by auto
  show "UPQ.pderiv (SA_poly_to_Qp_poly m x g) n = SA_poly_to_Qp_poly m x (UPSA.pderiv m g) n"
    unfolding 0 2 using SA_poly_to_Qp_poly_coeff assms
    by (metis "0" "2" SA_poly_to_Qp_poly_comm_pderiv)
qed

lemma(in UP_cring) pderiv_deg_lt:
  assumes "f \<in> carrier (UP R)"
  assumes "deg R f > 0"
  shows "deg R (pderiv f) < deg R f"
proof-
  obtain n where n_def: "n = deg R f"
    by blast
  have 0: "\<And>k. k \<ge> n \<Longrightarrow> pderiv f k = \<zero>"
    using pderiv_cfs assms unfolding n_def
    by (simp add: UP_car_memE(2))
  obtain k where k_def: "n = Suc k"
    using n_def assms gr0_implies_Suc by presburger
  have "deg R (pderiv f) \<le> k"
    apply(rule deg_leqI)
    using P_def assms(1) pderiv_closed apply presburger
    apply(rule 0)
    unfolding k_def by presburger
  thus ?thesis using k_def unfolding n_def by linarith
qed

lemma deg_pderiv:
  assumes "f \<in> carrier (UP (SA m))"
  assumes "deg (SA m) f > 0"
  shows "deg (SA m) (pderiv m f) = deg (SA m) f - 1"
proof-
  obtain n where n_def: "n = deg (SA m) f"
    by blast
  have 0: "f n \<noteq> \<zero>\<^bsub>SA m\<^esub>"
    unfolding n_def using assms UPSA.deg_ltrm by fastforce
  have 1: "(pderiv m f) (n-1) = [n]\<cdot>\<^bsub>SA m\<^esub> (f n)"
    using assms unfolding n_def using  Suc_diff_1 UPSA.pderiv_cfs by presburger
  have 2: "deg (SA m) (pderiv m f) \<ge> (n-1)"
    using 0 assms SA_char_zero
    by (metis "1" UPSA.deg_eqI UPSA.lcf_closed UPSA.pderiv_closed n_def nat_le_linear)
  have 3: "deg (SA m) (pderiv m f) < deg (SA m) f"
    using assms  pderiv_deg_lt by auto
  thus ?thesis using 2  unfolding  n_def by presburger
qed

lemma SA_poly_to_Qp_poly_smult:
  assumes "a \<in> carrier (SA m)"
  assumes "f \<in> carrier (UP (SA m))"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "SA_poly_to_Qp_poly m x (a \<odot>\<^bsub>UP (SA m)\<^esub> f) = a x \<odot>\<^bsub>UP Q\<^sub>p\<^esub> SA_poly_to_Qp_poly m x f"
proof-
  have 0: "a \<odot>\<^bsub>UP (SA m)\<^esub> f = to_polynomial (SA m) a \<otimes>\<^bsub>UP (SA m)\<^esub> f"
    using assms  UPSA.to_poly_mult_simp(1) by presburger
  have 1: "SA_poly_to_Qp_poly m x (a \<odot>\<^bsub>UP (SA m)\<^esub> f) = SA_poly_to_Qp_poly m x (to_polynomial (SA m) a) \<otimes>\<^bsub>UP Q\<^sub>p\<^esub> SA_poly_to_Qp_poly m x f"
    unfolding 0 apply(rule SA_poly_to_Qp_poly_mult)
    using assms apply blast
    using assms to_poly_closed  apply blast
    using assms by blast
  have 2: "SA_poly_to_Qp_poly m x (a \<odot>\<^bsub>UP (SA m)\<^esub> f) = (to_polynomial Q\<^sub>p (a x)) \<otimes>\<^bsub>UP Q\<^sub>p\<^esub> SA_poly_to_Qp_poly m x f"
    unfolding 1 using assms SA_poly_to_Qp_poly_monom unfolding to_polynomial_def
    by presburger
  show ?thesis
    unfolding 2 apply(rule UP_cring.to_poly_mult_simp(1)[of Q\<^sub>p "a x" "SA_poly_to_Qp_poly m x f"])
    unfolding UP_cring_def
    using F.R_cring apply blast
    using assms SA_car_memE apply blast
    using assms SA_poly_to_Qp_poly_closed[of x m f] by blast
qed

lemma SA_poly_constant_res_class_semialg:
  assumes "f \<in> carrier (UP (SA m))"
  assumes "\<And>i x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> f i x \<in> \<O>\<^sub>p"
  assumes "deg (SA m) f \<le> d"
  assumes "C \<in> poly_res_classes n d"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). SA_poly_to_Qp_poly m x f \<in> C}"
proof-
  obtain Fs where Fs_def: "Fs = f ` {..d}"
    by blast
  obtain g where g_def: "g \<in> val_ring_polys_grad d \<and> C = poly_res_class n d g"
    using assms unfolding poly_res_classes_def by blast
  have C_eq: " C = poly_res_class n d g"
    using g_def by blast
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). SA_poly_to_Qp_poly m x f \<in> C} =
            (\<Inter> i \<in> {..d}. {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). f i x \<in> \<O>\<^sub>p \<and> Qp_res (f i x) n = Qp_res (g i) n})"
    apply(rule equalityI')
    unfolding mem_Collect_eq
  proof(rule InterI)
    fix x S
    assume A: " x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<and> SA_poly_to_Qp_poly m x f \<in> C"
           "S \<in> (\<lambda>i. {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). f i x \<in> \<O>\<^sub>p \<and> Qp_res (f i x) n = Qp_res (g i) n}) ` {..d}"
    have 0: "C = poly_res_class n d (SA_poly_to_Qp_poly m x f)"
      unfolding C_eq
      apply(rule equalityI', rule poly_res_class_memI, rule poly_res_class_memE[of _ n d g], blast
          , rule poly_res_class_memE[of _ n d g], blast,  rule poly_res_class_memE[of _ n d g], blast)
      using poly_res_class_memE[of _ n d ]A
       apply (metis (no_types, lifting) C_eq)
      apply(rule poly_res_class_memI, rule poly_res_class_memE[of _ n d "SA_poly_to_Qp_poly m x f"], blast,
            rule poly_res_class_memE[of _ n d "SA_poly_to_Qp_poly m x f"], blast,
            rule poly_res_class_memE[of _ n d "SA_poly_to_Qp_poly m x f"], blast)
      using poly_res_class_memE[of _ n d ]A
       by (metis (no_types, lifting) C_eq)
    obtain i where i_def: "i \<in> {..d} \<and>
                            S = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). f i x \<in> \<O>\<^sub>p \<and> Qp_res (f i x) n = Qp_res (g i) n}"
      using A by blast
    have S_eq: "S = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). f i x \<in> \<O>\<^sub>p \<and> Qp_res (f i x) n = Qp_res (g i) n}"
      using i_def by blast
    have 1: "\<And>i. SA_poly_to_Qp_poly m x f i = f i x"
      apply(rule SA_poly_to_Qp_poly_coeff)
      using A apply blast by(rule assms)
    have 2: "deg Q\<^sub>p (SA_poly_to_Qp_poly m x f) \<le> d"
      using assms SA_poly_to_Qp_poly_deg_bound[of f m x]
      using A(1) by linarith
    have 3: "Qp_res (SA_poly_to_Qp_poly m x f i) n = Qp_res (g i) n"
      apply(rule poly_res_class_memE[of _ _ d], rule poly_res_class_memI)
      using g_def val_ring_polys_grad_memE apply blast
      using g_def val_ring_polys_grad_memE apply blast
      using g_def val_ring_polys_grad_memE apply blast
      apply(rule poly_res_class_memE[of _ _ d],rule poly_res_class_memI)
         apply(rule SA_poly_to_Qp_poly_closed)
      using A apply blast
         apply(rule assms)
      apply(rule 2)
      unfolding 1 using assms A apply blast
      using A unfolding C_eq
      using poly_res_class_memE(4)[of "SA_poly_to_Qp_poly m x f" n d g]
      unfolding 1 by metis
    show "x \<in> S"
      using A 3 assms
      unfolding S_eq mem_Collect_eq unfolding 1
      by blast
  next

    show "\<And>x. x \<in> (\<Inter>i\<le>d. {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). f i x \<in> \<O>\<^sub>p \<and> Qp_res (f i x) n = Qp_res (g i) n}) \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<and> SA_poly_to_Qp_poly m x f \<in> C"
    proof-
      fix x assume A: "x \<in> (\<Inter>i\<le>d. {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). f i x \<in> \<O>\<^sub>p \<and> Qp_res (f i x) n = Qp_res (g i) n})"
      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using A by blast
      have 0: "\<And>i. SA_poly_to_Qp_poly m x f i = f i x"
        apply(rule SA_poly_to_Qp_poly_coeff)
        using A apply blast by(rule assms)
      have 1: "deg Q\<^sub>p (SA_poly_to_Qp_poly m x f) \<le> d"
        using assms SA_poly_to_Qp_poly_deg_bound[of f m x]
        using x_closed by linarith
      have 2: "\<And>i. Qp_res (f i x) n = Qp_res (g i) n"
      proof- fix i
        have 20: "i > d \<Longrightarrow> i > deg Q\<^sub>p g"
          using g_def val_ring_polys_grad_memE(2) by fastforce
        have 21: "i > d \<Longrightarrow> g i= \<zero>"
          using 20 g_def val_ring_polys_grad_memE UPQ.deg_leE by blast
        have 22: "i > d \<Longrightarrow> Qp_res (g i) n = 0"
          unfolding 21 Qp_res_zero by blast
        have 23: "i > d \<Longrightarrow> SA_poly_to_Qp_poly m x f i = \<zero>"
          apply(rule UPQ.deg_leE, rule SA_poly_to_Qp_poly_closed, rule x_closed, rule assms)
          by(rule le_less_trans[of _ d], rule 1, blast)
        show " Qp_res (f i x) n = Qp_res (g i) n"
          apply(cases "i \<le> d")
          using A apply blast
          using 22 21 1 23 unfolding 0
          by (metis less_or_eq_imp_le linorder_neqE_nat)
      qed
      have 3: "SA_poly_to_Qp_poly m x f \<in> C"
        unfolding C_eq
        apply(rule poly_res_class_memI, rule SA_poly_to_Qp_poly_closed, rule x_closed, rule assms, rule 1)
        unfolding 0
        by(rule assms, rule x_closed, rule 2)
      show " x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<and> SA_poly_to_Qp_poly m x f \<in> C"
        using x_closed 3 by blast
    qed
  qed
  have 1: "\<And>i. is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). f i x \<in> \<O>\<^sub>p \<and> Qp_res (f i x) n = Qp_res (g i) n}"
    apply(rule SA_constant_res_set_semialg, rule Qp_res_closed, rule val_ring_polys_grad_memE[of _ d])
    using g_def apply blast
    using assms UPSA.UP_car_memE(1) by blast
  show "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). SA_poly_to_Qp_poly m x f \<in> C}"
    unfolding 0
    apply(rule finite_intersection_is_semialg, blast, blast, rule subsetI)
    using 1 unfolding is_semialgebraic_def by blast
qed

text\<open>Maps a polynomial $F(t) \in UP (SA n)$ to a function sending $(t, a) \in (Q_p (n + 1) \mapsto F(a)(t) \in Q_p$ \<close>

definition SA_poly_to_SA_fun where
  "SA_poly_to_SA_fun n P = (\<lambda> a \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>). UP_cring.to_fun Q\<^sub>p (SA_poly_to_Qp_poly n (tl a) P) (hd a))"

lemma SA_poly_to_SA_fun_is_fun:
  assumes "P \<in> carrier (UP (SA n))"
  shows "SA_poly_to_SA_fun n P \<in> (carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>) \<rightarrow> carrier Q\<^sub>p)"
proof fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
  obtain t where t_def: "t = hd x" by blast
  obtain a where a_def: "a = tl x" by blast
  have t_closed: "t \<in> carrier Q\<^sub>p"
    using A t_def cartesian_power_head
    by blast
  have a_closed: "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
    using A a_def cartesian_power_tail
    by blast
  have 0: "SA_poly_to_SA_fun n P x = UP_cring.to_fun Q\<^sub>p (SA_poly_to_Qp_poly n a P) t"
    unfolding SA_poly_to_SA_fun_def using t_def a_def
    by (meson A restrict_apply')
  show "SA_poly_to_SA_fun n P x \<in> carrier Q\<^sub>p"
    using assms t_closed a_def 0 UP_cring.to_fun_closed[of Q\<^sub>p "SA_poly_to_Qp_poly n a P" ]
    unfolding SA_poly_to_SA_fun_def
    using SA_poly_to_Qp_poly_closed a_closed UPQ.to_fun_closed by presburger
qed

lemma SA_poly_to_SA_fun_formula:
  assumes "P \<in> carrier (UP (SA n))"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "t \<in> carrier Q\<^sub>p"
  shows "SA_poly_to_SA_fun n P (t#x) = (SA_poly_to_Qp_poly n x P)\<bullet>t"
proof-
  have 0: "hd (t#x) = t"
    by simp
  have 1: "tl (t#x) = x"
    by auto
  have 2: "(t#x) \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
    by (metis add.commute assms cartesian_power_cons plus_1_eq_Suc)
  show ?thesis
    unfolding SA_poly_to_SA_fun_def
    using 0 1 2 assms
    by (metis (no_types, lifting) restrict_apply')
qed

lemma semialg_map_comp_in_SA:
  assumes "f \<in> carrier (SA n)"
  assumes "is_semialg_map m n g"
  shows "(\<lambda> a \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). f (g a)) \<in> carrier (SA m)"
proof(rule SA_car_memI)
  show "(\<lambda>a\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). f (g a)) \<in> carrier (Qp_funs m)"
  proof(rule Qp_funs_car_memI)
    show " (\<lambda>a\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). f (g a)) \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
    proof fix a assume A: "a \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      then have "g a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
        using is_semialg_map_def[of m n g] assms
        by blast
      then show  "f (g a) \<in> carrier Q\<^sub>p"
        using A assms  SA_car_memE(3)[of f n]
        by blast
    qed
    show " \<And>x. x \<notin> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> (\<lambda>a\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). f (g a)) x = undefined"
      unfolding restrict_def by metis
  qed
  have 0: "is_semialg_function m (f \<circ> g)"
    using assms semialg_function_comp_closed[of n f m g] SA_car_memE(1)[of f n]
    by blast
  have 1: " (\<And>a. a \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> (f \<circ> g) a = (\<lambda>a\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). f (g a)) a)"
    using assms  comp_apply[of f g] unfolding restrict_def
    by metis
  then show "is_semialg_function m (\<lambda>a\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). f (g a))"
    using 0 1 semialg_function_on_carrier'[of m "f \<circ> g" "\<lambda> a \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). f (g a)" ]
    by blast
qed

lemma tl_comp_in_SA:
  assumes "f \<in> carrier (SA n)"
  shows "(\<lambda> a \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>). f (tl a)) \<in> carrier (SA (Suc n))"
  using assms semialg_map_comp_in_SA[of f _ _  tl] tl_is_semialg_map[of "n"]
  by blast

lemma SA_poly_to_SA_fun_add_eval:
  assumes "f \<in> carrier (UP (SA n))"
  assumes "g \<in> carrier (UP (SA n))"
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
  shows "SA_poly_to_SA_fun n (f \<oplus>\<^bsub>UP (SA n)\<^esub> g) a = SA_poly_to_SA_fun n f a \<oplus>\<^bsub>Q\<^sub>p\<^esub> SA_poly_to_SA_fun n g a"
  unfolding SA_poly_to_SA_fun_def
  using assms SA_poly_to_Qp_poly_add[of "tl a" n f g]
  by (metis (no_types, lifting) SA_poly_to_Qp_poly_closed UPQ.to_fun_plus cartesian_power_head cartesian_power_tail restrict_apply')

lemma SA_poly_to_SA_fun_add:
  assumes "f \<in> carrier (UP (SA n))"
  assumes "g \<in> carrier (UP (SA n))"
  shows "SA_poly_to_SA_fun n (f \<oplus>\<^bsub>UP (SA n)\<^esub> g) = SA_poly_to_SA_fun n f \<oplus>\<^bsub>SA (Suc n)\<^esub> SA_poly_to_SA_fun n g"
proof fix x
  show " SA_poly_to_SA_fun n (f \<oplus>\<^bsub>UP (SA n)\<^esub> g) x = (SA_poly_to_SA_fun n f \<oplus>\<^bsub>SA (Suc n)\<^esub> SA_poly_to_SA_fun n g) x"
  proof(cases "x \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)")
    case True
    then show ?thesis using SA_poly_to_SA_fun_add_eval[of f n g x] SA_add[of x n]
      using SA_mult assms(1) assms(2) SA_add
      by blast
  next
    case False
    have F0: "SA_poly_to_SA_fun n (f \<oplus>\<^bsub>UP (SA n)\<^esub> g) x = undefined"
      unfolding SA_poly_to_SA_fun_def
      by (meson False restrict_apply)
    have F1: "(SA_poly_to_SA_fun n f \<oplus>\<^bsub>SA (Suc n)\<^esub> SA_poly_to_SA_fun n g) x = undefined"
      using  False SA_add' by blast
    then show ?thesis
      using F0 by blast
  qed
qed

lemma SA_poly_to_SA_fun_monom:
  assumes "f \<in> carrier (SA n)"
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
  shows "SA_poly_to_SA_fun n (up_ring.monom (UP (SA n)) f k) a = (f (tl a))\<otimes>(hd a)[^]\<^bsub>Q\<^sub>p\<^esub>k "
proof-
  have "SA_poly_to_SA_fun n (up_ring.monom (UP (SA n)) f k) a = SA_poly_to_Qp_poly n (tl a) (up_ring.monom (UP (SA n)) f k) \<bullet> lead_coeff a"
    unfolding SA_poly_to_SA_fun_def using assms
    by (meson restrict_apply)
  then have "SA_poly_to_SA_fun n (up_ring.monom (UP (SA n)) f k) a = up_ring.monom Q\<^sub>p_x (f (tl a)) k\<bullet> lead_coeff a"
    using SA_poly_to_Qp_poly_monom[of "tl a" n f k] assms
    by (metis cartesian_power_tail)
  then show ?thesis using assms
    by (metis (no_types, lifting) SA_car cartesian_power_head cartesian_power_tail UPQ.to_fun_monom Qp.function_ring_car_mem_closed semialg_functions_memE(2))
qed

lemma SA_poly_to_SA_fun_monom':
  assumes "f \<in> carrier (SA n)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "t \<in> carrier Q\<^sub>p"
  shows "SA_poly_to_SA_fun n (up_ring.monom (UP (SA n)) f k) (t#x) = (f x)\<otimes>t[^]\<^bsub>Q\<^sub>p\<^esub>k "
proof-
  have 0: "hd (t#x) = t"
    by simp
  have 1: "tl (t#x) = x"
    by auto
  have 2: "(t#x) \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
    by (metis add.commute assms  cartesian_power_cons plus_1_eq_Suc)
  show ?thesis
    using 0 1 2 SA_poly_to_SA_fun_monom[of f n "t#x" k] assms SA_poly_to_SA_fun_monom
    by presburger
qed

lemma hd_is_semialg_function:
  assumes "n > 0"
  shows "is_semialg_function n hd"
proof-
  have 0: "is_semialg_function n (\<lambda> a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). a!0)"
    using assms index_is_semialg_function restrict_is_semialg by blast
  have 1: "restrict (\<lambda>a\<in>carrier (Q\<^sub>p\<^bsup>n\<^esup>). a ! 0) (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) = restrict lead_coeff (carrier (Q\<^sub>p\<^bsup>n\<^esup>))"
  proof fix x
    show "restrict (\<lambda>a\<in>carrier (Q\<^sub>p\<^bsup>n\<^esup>). a ! 0) (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) x = restrict lead_coeff (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) x"
      unfolding restrict_def
      apply(cases "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)")
       apply (metis assms cartesian_power_car_memE drop_0 hd_drop_conv_nth)
      by presburger
  qed
  show ?thesis
    using 0 1 assms semialg_function_on_carrier[of n "(\<lambda> a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). a!0)" hd]
    by blast
qed

lemma SA_poly_to_SA_fun_monom_closed:
  assumes "f \<in> carrier (SA n)"
  shows "SA_poly_to_SA_fun n (up_ring.monom (UP (SA n)) f k) \<in> carrier (SA (Suc n))"
proof-
  have 0: "is_semialg_function (Suc n) (f \<circ> tl)"
    using SA_imp_semialg assms(1)  semialg_function_comp_closed tl_is_semialg_map by blast
  obtain h where h_def: "h = restrict hd (carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>))"
    by blast
  have h_closed: "h \<in> carrier (SA (Suc n))"
    using hd_is_semialg_function SA_car h_def restrict_in_semialg_functions
    by blast
  have h_pow_closed: "h[^]\<^bsub>SA (Suc n)\<^esub> k \<in> carrier (SA (Suc n))"
    using assms(1) h_closed monoid.nat_pow_closed[of "SA (Suc n)" h k] SA_is_monoid[of "Suc n"]
    by blast
  have monom_term_closed: "(f \<circ> tl) \<otimes>\<^bsub>SA (Suc n)\<^esub> h[^]\<^bsub>SA (Suc n)\<^esub> k \<in> carrier (SA (Suc n))"
    apply(rule SA_mult_closed_right)
    using "0" apply linarith
    using h_pow_closed by blast

  have 0: "\<And>a. a \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>) \<Longrightarrow> SA_poly_to_SA_fun n (up_ring.monom (UP (SA n)) f k) a = ((f \<circ> tl) \<otimes>\<^bsub>SA (Suc n)\<^esub> h[^]\<^bsub>SA (Suc n)\<^esub> k) a"
  proof- fix a assume "a \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
    then show "SA_poly_to_SA_fun n (up_ring.monom (UP (SA n)) f k) a = ((f \<circ> tl) \<otimes>\<^bsub>SA (Suc n)\<^esub> h[^]\<^bsub>SA (Suc n)\<^esub> k) a"
      using assms SA_poly_to_SA_fun_monom[of f n a k] comp_apply[of f tl a] h_def restrict_apply
            SA_mult[of a "Suc n" "f \<circ> tl" "h [^]\<^bsub>SA (Suc n)\<^esub> k"] SA_nat_pow[of a "Suc n" h k]
      by metis
  qed
  have 1: "SA_poly_to_SA_fun n (up_ring.monom (UP (SA n)) f k) = ((f \<circ> tl) \<otimes>\<^bsub>SA (Suc n)\<^esub> h[^]\<^bsub>SA (Suc n)\<^esub> k)"
  proof fix x
    show "SA_poly_to_SA_fun n (up_ring.monom (UP (SA n)) f k) x = ((f \<circ> tl) \<otimes>\<^bsub>SA (Suc n)\<^esub> h [^]\<^bsub>SA (Suc n)\<^esub> k) x"
      apply(cases "x \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)")
      using "0" apply blast
      using monom_term_closed unfolding SA_poly_to_SA_fun_def
      using restrict_apply
      by (metis (no_types, lifting) SA_mult')
  qed
  show ?thesis
    using 1 monom_term_closed
    by presburger
qed

lemma SA_poly_to_SA_fun_is_SA:
  assumes "P \<in> carrier (UP (SA n))"
  shows "SA_poly_to_SA_fun n P \<in> carrier (SA (Suc n))"
  apply(rule UP_ring.poly_induct3[of "SA n" P])
  unfolding UP_ring_def using assms SA_is_ring apply blast
  using assms apply blast
  using assms SA_poly_to_SA_fun_add[of ]
  using SA_add_closed_right SA_imp_semialg  zero_less_Suc apply presburger
  using SA_poly_to_SA_fun_monom_closed assms(1)
  by blast

lemma SA_poly_to_SA_fun_mult:
  assumes "f \<in> carrier (UP (SA n))"
  assumes "g \<in> carrier (UP (SA n))"
  shows "SA_poly_to_SA_fun n (f \<otimes>\<^bsub>UP (SA n)\<^esub> g) = SA_poly_to_SA_fun n f \<otimes>\<^bsub>SA (Suc n)\<^esub> SA_poly_to_SA_fun n g"
proof(rule function_ring_car_eqI[of _ "Suc n"])
  show "SA_poly_to_SA_fun n (f \<otimes>\<^bsub>UP (SA n)\<^esub> g) \<in> carrier (function_ring (carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)) Q\<^sub>p)"
  proof-
    have "f \<otimes>\<^bsub>UP (SA n)\<^esub> g \<in> carrier (UP (SA n))"
      using assms  SA_is_UP_cring
      by (meson cring.cring_simprules(5) padic_fields.UP_SA_n_is_cring padic_fields_axioms)
    thus ?thesis
      using SA_is_UP_cring assms SA_poly_to_SA_fun_is_SA[of "f \<otimes>\<^bsub>UP (SA n)\<^esub> g"] SA_car_in_Qp_funs_car[of "Suc n"]
      by blast
  qed
  show "SA_poly_to_SA_fun n f \<otimes>\<^bsub>SA (Suc n)\<^esub> SA_poly_to_SA_fun n g \<in> carrier (function_ring (carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)) Q\<^sub>p)"
    using SA_is_UP_cring SA_poly_to_SA_fun_is_SA assms
    by (meson SA_car_memE(2) SA_mult_closed_left less_Suc_eq_0_disj padic_fields.SA_car_memE(1) padic_fields_axioms)
  show "\<And>a. a \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>) \<Longrightarrow> SA_poly_to_SA_fun n (f \<otimes>\<^bsub>UP (SA n)\<^esub> g) a = (SA_poly_to_SA_fun n f \<otimes>\<^bsub>SA (Suc n)\<^esub> SA_poly_to_SA_fun n g) a"
  proof- fix a assume  A: "a \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
    then obtain t b where tb_def: "a = t#b"
      using cartesian_power_car_memE[of a Q\<^sub>p "Suc n"] by (meson length_Suc_conv)
    have t_closed: "t \<in> carrier Q\<^sub>p"
      using tb_def A cartesian_power_head[of a Q\<^sub>p n] by (metis list.sel(1))
    have b_closed: "b \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
      using tb_def A cartesian_power_tail[of a Q\<^sub>p n] by (metis list.sel(3))
    have 0: "f \<otimes>\<^bsub>UP (SA n)\<^esub> g \<in> carrier (UP (SA n))"
      using assms by (meson UP_SA_n_is_cring cring.cring_simprules(5))
    have 1: "SA_poly_to_SA_fun n (f \<otimes>\<^bsub>UP (SA n)\<^esub> g) a  = (SA_poly_to_Qp_poly n b (f \<otimes>\<^bsub>UP (SA n)\<^esub> g))\<bullet>t"
      using SA_poly_to_SA_fun_formula[of "f \<otimes>\<^bsub>UP (SA n)\<^esub> g" n b t] t_closed b_closed tb_def  0  assms(1)
      by blast
    have 2: "(SA_poly_to_SA_fun n f \<otimes>\<^bsub>SA (Suc n)\<^esub> SA_poly_to_SA_fun n g) a =
            SA_poly_to_SA_fun n f a \<otimes> SA_poly_to_SA_fun n g a"
      using SA_poly_to_SA_fun_is_fun assms A SA_mult by blast
    hence 3: "(SA_poly_to_SA_fun n f \<otimes>\<^bsub>SA (Suc n)\<^esub> SA_poly_to_SA_fun n g) a =
            ((SA_poly_to_Qp_poly n b f) \<bullet> t) \<otimes> ((SA_poly_to_Qp_poly n b g) \<bullet> t)"
      using SA_poly_to_SA_fun_formula assms
      by (metis b_closed t_closed tb_def)
    have 4: "SA_poly_to_SA_fun n (f \<otimes>\<^bsub>UP (SA n)\<^esub> g) a  = ((SA_poly_to_Qp_poly n b f) \<bullet> t) \<otimes> ((SA_poly_to_Qp_poly n b g) \<bullet> t)"
      using 1 assms SA_poly_to_Qp_poly_closed[of b] SA_poly_to_Qp_poly_mult UPQ.to_fun_mult b_closed t_closed
      by presburger
    show " SA_poly_to_SA_fun n (f \<otimes>\<^bsub>UP (SA n)\<^esub> g) a = (SA_poly_to_SA_fun n f \<otimes>\<^bsub>SA (Suc n)\<^esub> SA_poly_to_SA_fun n g) a"
      using "3" "4" by blast
  qed
qed

lemma SA_poly_to_SA_fun_one:
  shows "SA_poly_to_SA_fun n (\<one>\<^bsub>UP (SA n)\<^esub>) = \<one>\<^bsub>SA (Suc n)\<^esub>"
proof(rule function_ring_car_eqI[of _ "Suc n"])
  have "\<one>\<^bsub>UP (SA n)\<^esub> \<in> carrier (UP (SA n))"
    using UP_SA_n_is_cring cring.cring_simprules(6) by blast
  thus " SA_poly_to_SA_fun n \<one>\<^bsub>UP (SA n)\<^esub> \<in> carrier (function_ring (carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)) Q\<^sub>p)"
    using SA_poly_to_SA_fun_is_SA[of "\<one>\<^bsub>UP (SA n)\<^esub>"] SA_car_in_Qp_funs_car[of "Suc n"]  SA_is_UP_cring[of n]
    by blast
  show "\<one>\<^bsub>SA (Suc n)\<^esub> \<in> carrier (function_ring (carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)) Q\<^sub>p)"
    unfolding SA_one
    using function_one_closed by blast
  show "\<And>a. a \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>) \<Longrightarrow> SA_poly_to_SA_fun n \<one>\<^bsub>UP (SA n)\<^esub> a = \<one>\<^bsub>SA (Suc n)\<^esub> a"
  proof- fix a assume A: "  a \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
    then obtain t b where tb_def: "a = t#b"
      using cartesian_power_car_memE[of a Q\<^sub>p "Suc n"] by (meson length_Suc_conv)
    have t_closed: "t \<in> carrier Q\<^sub>p"
      using tb_def A cartesian_power_head[of a Q\<^sub>p n] by (metis list.sel(1))
    have b_closed: "b \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
      using tb_def A cartesian_power_tail[of a Q\<^sub>p n] by (metis list.sel(3))
    have 0: "SA_poly_to_SA_fun n \<one>\<^bsub>UP (SA n)\<^esub> a  = (SA_poly_to_Qp_poly n b \<one>\<^bsub>UP (SA n)\<^esub>)\<bullet>t"
      using SA_poly_to_SA_fun_formula \<open>\<one>\<^bsub>UP (SA n)\<^esub> \<in> carrier (UP (SA n))\<close>  b_closed t_closed tb_def
      by blast
    have 1: "SA_poly_to_Qp_poly n b \<one>\<^bsub>UP (SA n)\<^esub> = \<one>\<^bsub>UP Q\<^sub>p\<^esub>"
      using  SA_poly_to_Qp_poly_is_hom[of b] ring_hom_one[of _ "UP (SA n)" "UP Q\<^sub>p"] b_closed
      by blast
    thus "SA_poly_to_SA_fun n \<one>\<^bsub>UP (SA n)\<^esub> a = \<one>\<^bsub>SA (Suc n)\<^esub> a"
      using "0" A function_one_eval SA_one UPQ.to_fun_one t_closed by presburger
  qed
qed

lemma SA_poly_to_SA_fun_ring_hom:
  shows "SA_poly_to_SA_fun n \<in> ring_hom (UP (SA n)) (SA (Suc n))"
  apply(rule ring_hom_memI)
  using SA_poly_to_SA_fun_is_SA  apply blast
  apply (meson SA_poly_to_SA_fun_mult)
  apply (meson SA_poly_to_SA_fun_add)
  by (meson SA_poly_to_SA_fun_one)

lemma SA_poly_to_SA_fun_taylor_term:
  assumes "F \<in> carrier (UP (SA n))"
  assumes "c \<in> carrier (SA n)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "t \<in> carrier Q\<^sub>p"
  assumes "f = SA_poly_to_Qp_poly n x F"
  shows "SA_poly_to_SA_fun n (UP_cring.taylor_term (SA n) c F k) (t#x) = (taylor_expansion Q\<^sub>p (c x) f k) \<otimes>(t \<ominus> c x)[^]\<^bsub>Q\<^sub>p\<^esub> k"
proof-
  have 0: "hd (t#x) = t"
    by simp
  have 1: "tl (t#x) = x"
    by auto
  have 2: "(t#x) \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
    by (metis Suc_eq_plus1 assms cartesian_power_cons)
  show ?thesis
    using assms 0 1 2 Pi_iff  SA_car_memE(3)
          SA_poly_to_Qp_poly_closed SA_poly_to_Qp_poly_comm_taylor_term[of F n c x k] restrict_apply'
    unfolding SA_poly_to_SA_fun_def
    by (metis (no_types, lifting) UPQ.taylor_def UPQ.to_fun_taylor_term)
qed

lemma SA_finsum_eval:
  assumes "finite I"
  assumes "F \<in> I \<rightarrow> carrier (SA m)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "(\<Oplus>\<^bsub>SA m\<^esub>i\<in>I. F i) x = (\<Oplus>i\<in>I. F i x)"
proof-
  have "F \<in> I \<rightarrow> carrier (SA m) \<longrightarrow> (\<Oplus>\<^bsub>SA m\<^esub>i\<in>I. F i) x = (\<Oplus>i\<in>I. F i x)"
    apply(rule finite.induct[of I])
    apply (simp add: assms(1))
    using  abelian_monoid.finsum_empty[of "SA m" F] assms unfolding Qp.finsum_empty
    using SA_is_abelian_monoid SA_zeroE apply presburger
  proof fix A a assume IH: "finite A" " F \<in> A \<rightarrow> carrier (SA m) \<longrightarrow> finsum (SA m) F A x = (\<Oplus>i\<in>A. F i x)"
                            "F \<in> insert a A \<rightarrow> carrier (SA m)"
    then have 0: "F \<in> A \<rightarrow> carrier (SA m)"
      by blast
    then have 1: "finsum (SA m) F A x = (\<Oplus>i\<in>A. F i x)"
      using IH by blast
    show "finsum (SA m) F (insert a A) x = (\<Oplus>i\<in>insert a A. F i x)"
    proof(cases "a \<in> A")
      case True
      then show ?thesis using insert_absorb[of a A] IH
        by presburger
    next
      case False
      have F0: "(\<lambda>i. F i x) \<in> A \<rightarrow> carrier Q\<^sub>p" proof fix i assume "i \<in> A" thus "F i x \<in> carrier Q\<^sub>p"
        using 0 assms(3) SA_car_memE(3)[of "F i" m] by blast qed
      have F1: "F a x \<in> carrier Q\<^sub>p"
        using IH assms(3) SA_car_memE(3)[of "F a" m] by blast
      have F2: "finsum (SA m) F (insert a A) x = F a x \<oplus> finsum (SA m) F A x"
      proof-
        have " finsum (SA m) F (insert a A) = F a \<oplus>\<^bsub>SA m\<^esub> finsum (SA m) F A"
          using False IH abelian_monoid.finsum_insert[of "SA m" A a F ] 0
          by (meson Pi_split_insert_domain SA_is_abelian_monoid)
        thus ?thesis using    abelian_monoid.finsum_closed[of "SA m" F A] 1 F0  F1
            SA_add[of x m "F a" "finsum (SA m) F A"]
          using assms(3) by presburger
      qed
      show ?thesis using False 0 IH  Qp.finsum_insert[of A a "\<lambda>i. F i x"] unfolding F2 1
        using F0 F1 by blast
    qed
  qed
  thus ?thesis using assms by blast
qed

lemma(in ring) finsum_ring_hom:
  assumes "ring S"
  assumes "h \<in> ring_hom R S"
  assumes "F \<in> I \<rightarrow> carrier R"
  assumes "finite I"
  shows "h (\<Oplus>i\<in>I. F i) = (\<Oplus>\<^bsub>S\<^esub>i\<in>I. h (F i))"
proof-
  have "F \<in> I \<rightarrow> carrier R \<longrightarrow> h (\<Oplus>i\<in>I. F i) = (\<Oplus>\<^bsub>S\<^esub>i\<in>I. h (F i))"
    apply(rule finite.induct[of I])
      apply (simp add: assms(4))
    unfolding finsum_empty using assms abelian_monoid.finsum_empty[of S]
    unfolding ring_def abelian_group_def
    apply (simp add: \<open>\<And>f. abelian_monoid S \<Longrightarrow> finsum S f {} = \<zero>\<^bsub>S\<^esub>\<close> assms(1) local.ring_axioms ring_hom_zero)
  proof fix A a assume A: "finite A" "  F \<in> A \<rightarrow> carrier R \<longrightarrow> h (finsum R F A) = (\<Oplus>\<^bsub>S\<^esub>i\<in>A. h (F i))"
       "   F \<in> insert a A \<rightarrow> carrier R"
    then have 0: "F \<in> A \<rightarrow> carrier R "
      by blast
    have 1: "h (finsum R F A) = (\<Oplus>\<^bsub>S\<^esub>i\<in>A. h (F i))"
      using "0" A(2) by linarith
    have 2: "(finsum R F A) \<in> carrier R"
      using finsum_closed[of F A] 0 by blast
    have 3: "(\<Oplus>\<^bsub>S\<^esub>i\<in>A. h (F i)) \<in> carrier S"
    using assms 1 2 ring_hom_closed
    by metis
    have 4: "F a \<in> carrier R" using A by blast
    have 5: "h (F a) \<in> carrier S"
      using assms 4
      by (meson ring_hom_closed)
    show "h (finsum R F (insert a A)) = (\<Oplus>\<^bsub>S\<^esub>i\<in>insert a A. h (F i))"
      apply(cases "a \<in> A")
      using insert_absorb 1
       apply metis
    proof- assume C: "a \<notin>A"
      have 6: "finsum R F (insert a A) = F a \<oplus> finsum R F A"
      using A finsum_insert[of A a F]  C by blast
    have 7: "(\<Oplus>\<^bsub>S\<^esub>i\<in>insert a A. h (F i)) = h (F a) \<oplus>\<^bsub>S\<^esub> (\<Oplus>\<^bsub>S\<^esub>i\<in>A. h (F i))"
    apply(rule abelian_monoid.finsum_insert[of S A a "\<lambda>i. h (F i)"])
          apply (simp add: abelian_group.axioms(1) assms(1) ring.is_abelian_group)
         apply (simp add: A(1))
        apply (simp add: C)
       apply(intro Pi_I ring_hom_closed[of h R S] assms)
      using 0 A 5 assms by auto
    thus ?thesis
    using    0 1 2 3 4 5 6  7 assms ring_hom_add[of h R S "F a" "finsum R F A" ]

      unfolding 1 ring_def abelian_group_def
      by presburger
  qed
  qed
  thus ?thesis using assms by auto
qed

lemma SA_poly_to_SA_fun_finsum:
  assumes "finite I"
  assumes "F \<in> I \<rightarrow> carrier (UP (SA m))"
  assumes "f = (\<Oplus>\<^bsub>UP (SA m)\<^esub>i\<in>I. F i)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  shows "SA_poly_to_SA_fun m f x = (\<Oplus>i\<in>I. SA_poly_to_SA_fun m (F i) x)"
proof-
  have "SA_poly_to_SA_fun m \<in> ring_hom (UP (SA m)) (SA (Suc m))"
    using SA_poly_to_SA_fun_ring_hom by blast
  have f_closed: "f \<in> carrier (UP (SA m))"
    unfolding assms apply(rule finsum_closed)  using assms by blast
  have 0: "SA_poly_to_SA_fun m f = (\<Oplus>\<^bsub>SA (Suc m)\<^esub>i\<in>I. SA_poly_to_SA_fun m (F i))"
    unfolding assms
    apply(rule finsum_ring_hom)
       apply (simp add: SA_is_ring)
    using \<open>SA_poly_to_SA_fun m \<in> ring_hom (UP (SA m)) (SA (Suc m))\<close> apply blast
    using assms(2) apply blast
    by (simp add: assms(1))
  show ?thesis unfolding 0 apply(rule SA_finsum_eval)
    using assms apply blast using assms
    apply (meson Pi_I Pi_mem padic_fields.SA_poly_to_SA_fun_is_SA padic_fields_axioms)
    using assms by blast
qed

lemma SA_poly_to_SA_fun_taylor_expansion:
  assumes "f \<in> carrier (UP (SA m))"
  assumes "c \<in> carrier (SA m)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  shows "SA_poly_to_SA_fun m f x = (\<Oplus>i\<in>{..deg (SA m) f}. taylor_expansion (SA m) c f i (tl x) \<otimes> (hd x \<ominus> c (tl x)) [^] i)"
proof-
  have 0: "f = (\<Oplus>\<^bsub>UP (SA m)\<^esub>i\<in>{..deg (SA m) f}. UP_cring.taylor_term (SA m) c f i)"
    using taylor_sum[of f m "deg (SA m) f" c] assms unfolding UPSA.taylor_term_def UPSA.taylor_def
    by blast
  have 1: "SA_poly_to_SA_fun m f x = (\<Oplus>i\<in>{..deg (SA m) f}. SA_poly_to_SA_fun m (UP_cring.taylor_term (SA m) c f i) x)"
    apply(rule SA_poly_to_SA_fun_finsum)
       apply simp
      apply (meson Pi_I UPSA.taylor_term_closed assms(1) assms(2))
    using 0 apply blast
    using assms by blast
  have hd_closed: "hd x \<in> carrier Q\<^sub>p"
    using assms cartesian_power_head by blast
  have tl_closed: "tl x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms cartesian_power_tail by blast
  obtain t a where ta_def: " x = t#a"
    using assms cartesian_power_car_memE[of x Q\<^sub>p "Suc m" ]
    by (metis Suc_length_conv)
  have 2: "t = hd x"
    by (simp add: ta_def)
  have 3: "a = tl x "
    by (simp add: ta_def)
  have 4: "\<And>i. SA_poly_to_SA_fun m (UPSA.taylor_term m c f i) x =
    taylor_expansion Q\<^sub>p (c (tl x)) (SA_poly_to_Qp_poly m (tl x) f) i \<otimes> (lead_coeff x \<ominus> c (tl x)) [^] i"
    using tl_closed hd_closed assms SA_poly_to_SA_fun_taylor_term[of f m c a t  "SA_poly_to_Qp_poly m a f"  ]
    unfolding 2 3  by (metis "2" "3" ta_def)
  have 5: "SA_poly_to_SA_fun m f x = (\<Oplus>i\<in>{..deg (SA m) f}. (taylor_expansion Q\<^sub>p (c (tl x)) (SA_poly_to_Qp_poly m (tl x) f) i) \<otimes>((hd x) \<ominus> c (tl x))[^]\<^bsub>Q\<^sub>p\<^esub> i)"
    using 1 2 unfolding 4 by blast
  have 6: "taylor_expansion Q\<^sub>p (c (tl x)) (SA_poly_to_Qp_poly m (tl x) f) = SA_poly_to_Qp_poly m (tl x) (taylor_expansion (SA m) c f)"

    using SA_poly_to_Qp_poly_taylor_poly[of f m c "tl x"] assms(1) assms(2) tl_closed by presburger
  have 7: "\<And>i. taylor_expansion Q\<^sub>p (c (tl x)) (SA_poly_to_Qp_poly m (tl x) f) i =
                taylor_expansion (SA m) c f i (tl x)"
    unfolding 6 using SA_poly_to_Qp_poly_coeff[of "tl x" m "taylor_expansion (SA m) c f"]
    by (metis UPSA.taylor_closed UPSA.taylor_def assms(1) assms(2) tl_closed)
  show ?thesis using 5 unfolding 7 by blast
qed

lemma SA_deg_one_eval:
  assumes "g \<in> carrier (UP (SA m))"
  assumes "deg (SA m) g = 1"
  assumes "\<xi> \<in> carrier (Fun\<^bsub>m\<^esub> Q\<^sub>p)"
  assumes "UP_ring.lcf (SA m) g \<in> Units (SA m)"
  assumes "\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (SA_poly_to_SA_fun m g) (\<xi> x#x) = \<zero>"
  shows "\<xi> = \<ominus>\<^bsub>SA m\<^esub>(g 0)\<otimes>\<^bsub>SA m\<^esub> (inv\<^bsub>SA m\<^esub> (g 1))"
proof(rule ext)
  fix x show " \<xi> x = (\<ominus>\<^bsub>SA m\<^esub> g 0 \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> g 1) x"
  proof(cases "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)")
    case True
    then have "(SA_poly_to_SA_fun m g) (\<xi> x#x) = \<zero>"
      using assms by blast
    then have T0: "SA_poly_to_Qp_poly m x g \<bullet> \<xi> x = \<zero>"
      using SA_poly_to_SA_fun_formula[of g m x "\<xi> x"] assms
            Qp.function_ring_car_mem_closed True by metis
    have "deg Q\<^sub>p (SA_poly_to_Qp_poly m x g) = 1"
    proof(rule UPQ.deg_eqI)
      show "SA_poly_to_Qp_poly m x g \<in> carrier (UP Q\<^sub>p)"
        using assms True SA_poly_to_Qp_poly_closed by blast
      show "deg Q\<^sub>p (SA_poly_to_Qp_poly m x g) \<le> 1"
        using SA_poly_to_Qp_poly_deg_bound by (metis True assms(1) assms(2) )
      show " SA_poly_to_Qp_poly m x g 1 \<noteq> \<zero>"
        using SA_poly_to_Qp_poly_coeff[of x m g 1] assms SA_Units_memE' True by presburger
    qed
    hence T1: "SA_poly_to_Qp_poly m x g \<bullet> \<xi> x = SA_poly_to_Qp_poly m x g 0 \<oplus> SA_poly_to_Qp_poly m x g 1 \<otimes> (\<xi> x)"
      using UP_cring.deg_one_eval[of Q\<^sub>p _ "\<xi> x"]
      by (meson Qp.function_ring_car_mem_closed SA_poly_to_Qp_poly_closed True UPQ.deg_one_eval assms)
    hence T2: "g 0 x \<oplus> g 1 x \<otimes> (\<xi> x) = \<zero>"
      using True T0 assms SA_poly_to_Qp_poly_coeff[of x m g]
      by metis
    have T3: "g 0 x \<in> carrier Q\<^sub>p"
      using True assms UP_ring.cfs_closed
      by (metis SA_poly_to_Qp_poly_closed SA_poly_to_Qp_poly_coeff UPQ.is_UP_ring)
    have T4: "\<xi> x \<in> carrier Q\<^sub>p"
      using True assms Qp.function_ring_car_memE by blast
    have T5: "g 1 x \<in> nonzero Q\<^sub>p"
      using True assms
      by (metis Qp.function_ring_car_memE SA_Units_closed SA_Units_memE' SA_car_memE(2) not_nonzero_Qp)
    have T6: "\<ominus> (g 0 x) = g 1 x \<otimes> (\<xi> x)"
      using T2 T3 T4 T5 by (metis Qp.m_closed Qp.minus_equality Qp.minus_minus Qp.nonzero_closed)
    hence T7: "\<ominus> (g 0 x) \<otimes> inv (g 1 x)= \<xi> x"
      using T5 by (metis Qp.inv_cancelR(2) Qp.m_closed Qp.nonzero_closed T4 Units_eq_nonzero)
    have T8: "(inv\<^bsub>SA m\<^esub> g 1) x = inv (g 1 x)"
      using assms True Qp_funs_m_inv SA_Units_Qp_funs_Units SA_Units_Qp_funs_inv by presburger
    have T9: "(\<ominus>\<^bsub>SA m\<^esub> g 0) x = \<ominus> (g 0 x)"
      using SA_a_inv_eval[of "g 0" m x] UP_ring.cfs_closed[of "SA m" g 0] assms True SA_is_ring
      unfolding UP_ring_def by blast
    have T11: "((\<ominus>\<^bsub>SA m\<^esub> g 0) \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> g 1) x = \<ominus> (g 0 x) \<otimes> inv (g 1 x)"
      using assms UP_ring.cfs_closed T8 T9 T7 True SA_mult by presburger
    thus "\<xi> x = (\<ominus>\<^bsub>SA m\<^esub> g 0 \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> g 1) x"
      using T7 by blast
  next
    case False
    then show ?thesis
      using SA_mult' SA_times assms function_ring_not_car by auto
  qed
qed

lemma SA_deg_one_eval':
  assumes "g \<in> carrier (UP (SA m))"
  assumes "deg (SA m) g = 1"
  assumes "\<xi> \<in> carrier (Fun\<^bsub>m\<^esub> Q\<^sub>p)"
  assumes "UP_ring.lcf (SA m) g \<in> Units (SA m)"
  assumes "\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (SA_poly_to_SA_fun m g) (\<xi> x#x) = \<zero>"
  shows "\<xi> \<in> carrier (SA m)"
proof-
  have 0: "\<xi> = \<ominus>\<^bsub>SA m\<^esub>(g 0)\<otimes>\<^bsub>SA m\<^esub> (inv\<^bsub>SA m\<^esub> (g 1))"
    using assms SA_deg_one_eval by blast
  have 1: "(inv\<^bsub>SA m\<^esub> (g 1)) \<in> carrier (SA m)"
    using assms SA_Units_inv_closed by presburger
  have "(g 0) \<in> carrier (SA m)"
    using assms(1) assms(2) UP_ring.cfs_closed[of "SA m" g 0] SA_is_ring[of m ] unfolding UP_ring_def
    by blast
  hence 2: "\<ominus>\<^bsub>SA m\<^esub>(g 0) \<in> carrier (SA m)"
    by (meson SA_is_cring assms(1) cring.cring_simprules(3))
  show ?thesis
    using 0 1 2  SA_imp_semialg SA_mult_closed_left assms(1) by blast
qed

lemma Qp_pow_ConsI:
  assumes "t \<in> carrier Q\<^sub>p"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  using assms cartesian_power_cons[of x Q\<^sub>p m t] Suc_eq_plus1 by presburger

lemma Qp_pow_ConsE:
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  shows "tl x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        "hd x \<in> carrier Q\<^sub>p"
  using assms cartesian_power_tail apply blast
  using assms cartesian_power_head by blast

lemma(in ring) add_monoid_one:
"\<one>\<^bsub>add_monoid R\<^esub> = \<zero>"
  by simp

lemma(in ring) add_monoid_carrier:
"carrier (add_monoid R) = carrier R"
  unfolding Congruence.partial_object.simps(1)
  by simp

lemma(in ring) finsum_mono_neutral_cong:
  assumes "F \<in> I \<rightarrow> carrier R"
  assumes "finite I"
  assumes "\<And>i. i \<notin> J \<Longrightarrow> F i = \<zero>"
  assumes "J \<subseteq> I"
  shows "finsum R F I = finsum R F J"
  unfolding finsum_def apply(rule comm_monoid.finprod_mono_neutral_cong)
  using local.add.comm_monoid_axioms apply blast
  using assms(2) assms(4) rev_finite_subset apply blast
  apply (simp add: assms(2))
  using assms(4) apply blast
  unfolding add_monoid_one using assms apply blast
  apply blast
  using add_monoid_carrier assms(1) apply blast
  using add_monoid_carrier assms  by blast

text\<open>
  This lemma helps to formalize statements like "by passing to a partition, we can assume the
  Taylor coefficients are either always zero or never zero"\<close>

lemma SA_poly_to_SA_fun_taylor_on_refined_set:
  assumes "f \<in> carrier (UP (SA m))"
  assumes "c \<in> carrier (SA m)"
  assumes "is_semialgebraic m A"
  assumes "\<And>i. A \<subseteq> SA_zero_set m (taylor_expansion (SA m) c f i) \<or> A \<subseteq> SA_nonzero_set m (taylor_expansion (SA m) c f i)"
  assumes "a = to_fun_unit m \<circ> taylor_expansion (SA m) c f"
  assumes "inds = {i. i \<le> deg (SA m) f \<and> A \<subseteq> SA_nonzero_set m (taylor_expansion (SA m) c f i)}"
  assumes "x \<in> A"
  assumes "t \<in> carrier Q\<^sub>p"
  shows "SA_poly_to_SA_fun m f (t#x) = (\<Oplus>i\<in>inds. (a i x)\<otimes>(t \<ominus> c x)[^]i)"
proof-
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms(3) assms(7)
  by (metis (no_types, lifting) Diff_eq_empty_iff Diff_iff empty_iff is_semialgebraic_closed)
  have tx_closed: "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    using x_closed assms(8) cartesian_power_cons[of x Q\<^sub>p m t] Qp_pow_ConsI by blast
  have "SA_poly_to_SA_fun m f (t # x) =
    (\<Oplus>i\<in>{..deg (SA m) f}. taylor_expansion (SA m) c f i (tl (t # x)) \<otimes> (hd (t # x) \<ominus> c (tl (t # x))) [^] i)"
    using tx_closed assms SA_poly_to_SA_fun_taylor_expansion[of f m c "t#x"]
    by linarith
  then have 0: "SA_poly_to_SA_fun m f (t#x) = (\<Oplus>i\<in>{..deg (SA m) f}. taylor_expansion (SA m) c f i x \<otimes> (t \<ominus> c x) [^] i)"
    unfolding list_tl list_hd by blast
  have 1: "\<And>i. i \<notin> inds \<Longrightarrow> taylor_expansion (SA m) c f i x = \<zero>"
  proof- fix i assume A: "i \<notin> inds"
    show "taylor_expansion (SA m) c f i x = \<zero>"
    proof(cases "i \<le> deg (SA m) f")
    case True
    then have "A \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). taylor_expansion (SA m) c f i x = \<zero>}"
      using A assms(8) assms(4)[of i] unfolding assms mem_Collect_eq SA_zero_set_def
      by linarith
    thus ?thesis using x_closed assms by blast
   next
    case False
    then have "taylor_expansion (SA m) c f i = \<zero>\<^bsub>SA m\<^esub>"
      using assms taylor_deg[of c m f] unfolding UPSA.taylor_def
      by (metis (no_types, lifting) UPSA.taylor_closed UPSA.taylor_def UPSA.deg_eqI nat_le_linear)
    then show ?thesis
      using x_closed SA_car_memE SA_zeroE by presburger
    qed
  qed
  hence 2: "\<And>i. i \<notin> inds \<Longrightarrow> taylor_expansion (SA m) c f i x \<otimes> (t \<ominus> c x) [^] i = \<zero>"
    using assms x_closed  SA_car_memE
    by (metis (no_types, lifting) Qp.cring_simprules(26) Qp.function_ring_car_memE Qp.minus_closed Qp.nat_pow_closed)
  have 3: "(\<lambda>i. taylor_expansion (SA m) c f i x \<otimes> (t \<ominus> c x) [^] i) \<in> {..deg (SA m) f} \<rightarrow> carrier Q\<^sub>p"
  proof fix i assume A: "i \<in> {..deg (SA m) f}"
    have 30: "taylor_expansion (SA m) c f i \<in> carrier (SA m)"
      using  assms UPSA.taylor_closed[of f m c] unfolding UPSA.taylor_def
      using UPSA.UP_car_memE(1) by blast
    hence 31: "taylor_expansion (SA m) c f i x \<in> carrier Q\<^sub>p"
      using x_closed function_ring_car_closed SA_car_memE(2) by blast
    have 32: "c x \<in> carrier Q\<^sub>p"
      using assms x_closed SA_car_memE(3) by blast
    hence 33: "(t \<ominus> c x)[^] i \<in> carrier Q\<^sub>p"
      using assms by blast
    show "taylor_expansion (SA m) c f i x \<otimes> (t \<ominus> c x) [^] i \<in> carrier Q\<^sub>p"
      using 30 31 32 33 by blast
  qed
  have 4: "SA_poly_to_SA_fun m f (t#x) = (\<Oplus>i\<in>inds. taylor_expansion (SA m) c f i x \<otimes> (t \<ominus> c x) [^] i)"
    unfolding 0 apply(rule Qp.finsum_mono_neutral_cong)
    using assms UPSA.taylor_closed[of f m c] unfolding UPSA.taylor_def
    using "3" apply blast
      apply blast
    using 2 apply blast
    unfolding assms by blast
  have A: "\<And>i. i \<in> inds \<Longrightarrow> a i x = taylor_expansion (SA m) c f i x"
    unfolding assms mem_Collect_eq SA_nonzero_set_def comp_apply
    apply(rule to_fun_unit_eq[of _ m x])
    using UPSA.taylor_closed[of f m c] assms unfolding UPSA.taylor_def
    using UPSA.UP_car_memE(1) apply blast
    using x_closed apply blast
    using assms(7) by blast
  have a_closed: "a \<in> UNIV \<rightarrow> carrier (SA m)"
    apply(rule Pi_I) unfolding assms comp_apply apply(rule to_fun_unit_closed[of _ m])
    apply(rule cfs_closed) using assms UPSA.taylor_closed[of f m c] unfolding UPSA.taylor_def by blast
  have 5: "(\<lambda>i. a i x \<otimes> (t \<ominus> c x) [^] i) \<in> inds \<rightarrow> carrier Q\<^sub>p"
  proof fix i assume A: "i \<in> inds"
    show "a i x \<otimes> (t \<ominus> c x) [^] i \<in> carrier Q\<^sub>p"
    using assms(8) x_closed a_closed SA_car_memE(3)[of c m] SA_car_memE(3)[of "a i" m]
         assms(2) by blast
  qed
  have 6: "\<And>i. i \<in> inds \<Longrightarrow> taylor_expansion (SA m) c f i x \<otimes> (t \<ominus> c x) [^] i = a i x \<otimes> (t \<ominus> c x) [^] i"
    unfolding A by blast
  show ?thesis
    unfolding 4 apply(rule Qp.finsum_cong') apply blast
    using 5 apply blast
    using 6 by blast
qed

lemma SA_poly_to_Qp_poly_taylor_cfs:
  assumes "f \<in> carrier (UP (SA m))"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "c \<in> carrier (SA m)"
  shows "taylor_expansion (SA m) c f i x =
    taylor_expansion Q\<^sub>p (c x) (SA_poly_to_Qp_poly m x f) i"
proof-
  have 0: "SA_poly_to_Qp_poly m x (taylor_expansion (SA m) c f) =
         taylor_expansion Q\<^sub>p (c x) (SA_poly_to_Qp_poly m x f)"
    using SA_poly_to_Qp_poly_taylor_poly[of f m c x] assms by blast
  hence 1: "SA_poly_to_Qp_poly m x (taylor_expansion (SA m) c f) i =
  taylor_expansion Q\<^sub>p (c x) (SA_poly_to_Qp_poly m x f) i"
    by presburger
  thus ?thesis
    using assms SA_poly_to_Qp_poly_coeff[of x m "taylor_expansion (SA m) c f" i]
      UPSA.taylor_closed[of f m c] unfolding UPSA.taylor_def assms by blast
qed

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Common Morphisms on Polynomial Rings\<close>
(**************************************************************************************************)
(**************************************************************************************************)


text\<open>Evaluation homomorphism from multivariable polynomials to semialgebraic functions\<close>

definition Qp_ev_hom where
"Qp_ev_hom n P = restrict (Qp_ev P) (carrier (Q\<^sub>p\<^bsup>n\<^esup>))"

lemma Qp_ev_hom_ev:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "Qp_ev_hom n P a = Qp_ev P a"
  using assms unfolding Qp_ev_hom_def
  by (meson restrict_apply')

lemma Qp_ev_hom_closed:
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "Qp_ev_hom n f \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  using Qp_ev_hom_ev assms by (metis Pi_I eval_at_point_closed)

lemma Qp_ev_hom_is_semialg_function:
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "is_semialg_function n (Qp_ev_hom n f)"
  unfolding Qp_ev_hom_def
  using assms poly_is_semialg[of  f] restrict_is_semialg by blast

lemma Qp_ev_hom_closed':
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "Qp_ev_hom n f \<in> carrier (Fun\<^bsub>n\<^esub> Q\<^sub>p)"
  apply(rule Qp.function_ring_car_memI)
  using  Qp_ev_hom_closed[of f n] assms apply blast
  unfolding Qp_ev_hom_def using assms by (meson restrict_apply)

lemma Qp_ev_hom_in_SA:
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "Qp_ev_hom n f \<in> carrier (SA n)"
  apply(rule SA_car_memI)
  using Qp_ev_hom_closed' assms(1)  apply blast
  using Qp_ev_hom_is_semialg_function assms(1) by blast

lemma Qp_ev_hom_add:
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "Qp_ev_hom n (f \<oplus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> g) = (Qp_ev_hom n f) \<oplus>\<^bsub>SA n\<^esub> (Qp_ev_hom n g)"
  apply(rule function_ring_car_eqI[of _ n])
  using assms MP.add.m_closed Qp_ev_hom_closed' apply blast
  using assms Qp_ev_hom_closed' fun_add_closed SA_plus apply presburger
proof- fix a assume A: "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  have " Qp_ev_hom n (f \<oplus>\<^bsub>Q\<^sub>p [\<X>\<^bsub>n\<^esub>]\<^esub> g) a =  Qp_ev_hom n f a \<oplus> Qp_ev_hom n g a"
    using A Qp_ev_hom_ev assms eval_at_point_add by presburger
  then show "Qp_ev_hom n (f \<oplus>\<^bsub>Q\<^sub>p [\<X>\<^bsub>n\<^esub>]\<^esub> g) a = (Qp_ev_hom n f \<oplus>\<^bsub>SA n\<^esub> Qp_ev_hom n g) a"
    using A SA_add by blast
qed

lemma Qp_ev_hom_mult:
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "Qp_ev_hom n (f \<otimes>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> g) = (Qp_ev_hom n f) \<otimes>\<^bsub>SA n\<^esub> (Qp_ev_hom n g)"
  apply(rule function_ring_car_eqI[of _ n])
  using assms MP.m_closed Qp_ev_hom_closed' apply blast
  using assms Qp_ev_hom_closed' fun_mult_closed SA_mult
  apply (meson Qp_ev_hom_in_SA SA_car_memE(2) SA_imp_semialg SA_mult_closed)
proof- fix a assume A: "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  have " Qp_ev_hom n (f \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>n\<^esub>]\<^esub> g) a =  Qp_ev_hom n f a \<otimes> Qp_ev_hom n g a"
    using A Qp_ev_hom_ev assms eval_at_point_mult by presburger
  then show "Qp_ev_hom n (f \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>n\<^esub>]\<^esub> g) a = (Qp_ev_hom n f \<otimes>\<^bsub>SA n\<^esub> Qp_ev_hom n g) a"
    using A SA_mult by blast
qed

lemma Qp_ev_hom_one:
  shows "Qp_ev_hom n \<one>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> = \<one>\<^bsub>SA n\<^esub>"
  apply(rule function_ring_car_eqI[of _ n])
  using Qp_ev_hom_closed' apply blast
  using  function_one_closed SA_one apply presburger
  unfolding Qp_ev_hom_def
  using function_one_eval Qp_ev_hom_def Qp_ev_hom_ev Qp_ev_one SA_one by presburger

lemma Qp_ev_hom_is_hom:
  shows "Qp_ev_hom n \<in> ring_hom (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) (SA n)"
  apply(rule ring_hom_memI)
  using   Qp_ev_hom_in_SA apply blast
    using  Qp_ev_hom_mult apply blast
      using  Qp_ev_hom_add apply blast
        using  Qp_ev_hom_one by blast

lemma Qp_ev_hom_constant:
  assumes "c \<in> carrier Q\<^sub>p"
  shows "Qp_ev_hom n (Qp.indexed_const c) = \<cc>\<^bsub>n\<^esub> c"
  apply(rule function_ring_car_eqI[of _ n])
  using Qp_ev_hom_closed' Qp_to_IP_car assms(1)  apply blast
  using constant_function_closed assms  apply blast
  by (metis Qp_constE Qp_ev_hom_ev assms eval_at_point_const)

notation  Qp.variable ("\<vv>\<^bsub>_, _\<^esub>")

lemma Qp_ev_hom_pvar:
  assumes "i < n"
  shows "Qp_ev_hom n (pvar Q\<^sub>p i) = \<vv>\<^bsub>n, i\<^esub>"
  apply(rule function_ring_car_eqI[of _ n])
  using assms Qp_ev_hom_closed' local.pvar_closed apply blast
  using Qp.var_in_car assms apply blast
  unfolding Qp_ev_hom_def var_def using assms eval_pvar
  by (metis (no_types, lifting) restrict_apply)

definition ext_hd where
"ext_hd m = (\<lambda> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). hd x)"

lemma hd_zeroth:
"length x > 0 \<Longrightarrow> x!0 = hd x"
  apply(induction x)
  apply simp
  by simp

lemma ext_hd_pvar:
  assumes "m > 0"
  shows "ext_hd m = (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). eval_at_point Q\<^sub>p x (pvar Q\<^sub>p 0) )"
  unfolding ext_hd_def restrict_def using assms eval_pvar[of 0 m]
  using hd_zeroth
  by (metis (no_types, opaque_lifting) cartesian_power_car_memE)

lemma ext_hd_closed:
  assumes "m > 0"
  shows "ext_hd m \<in> carrier (SA m)"
  using ext_hd_pvar[of m] assms pvar_closed[of 0 m] Qp_ev_hom_def Qp_ev_hom_in_SA by presburger

lemma UP_Qp_poly_to_UP_SA_is_hom:
  shows "poly_lift_hom (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) (SA n) (Qp_ev_hom n) \<in> ring_hom (UP (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])) (UP (SA n))"
  using UP_cring.poly_lift_hom_is_hom[of "Q\<^sub>p[\<X>\<^bsub>n\<^esub>]" "SA n" "Qp_ev_hom n"]
  unfolding UP_cring_def
  using Qp_ev_hom_is_hom SA_is_cring  coord_cring_cring by blast

definition coord_ring_to_UP_SA where
"coord_ring_to_UP_SA n = poly_lift_hom (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) (SA n) (Qp_ev_hom n) \<circ> to_univ_poly (Suc n) 0"

lemma coord_ring_to_UP_SA_is_hom:
  shows "coord_ring_to_UP_SA n \<in> ring_hom (Q\<^sub>p[\<X>\<^bsub>Suc n\<^esub>]) (UP (SA n))"
  unfolding coord_ring_to_UP_SA_def
  using UP_Qp_poly_to_UP_SA_is_hom[of n] to_univ_poly_is_hom[of 0 "n"] ring_hom_trans
  by blast

lemma coord_ring_to_UP_SA_add:
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>Suc n\<^esub>])"
  assumes "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>Suc n\<^esub>])"
  shows "coord_ring_to_UP_SA n (f \<oplus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>Suc n\<^esub>]\<^esub>g) = coord_ring_to_UP_SA n f  \<oplus>\<^bsub>UP (SA n)\<^esub> coord_ring_to_UP_SA n g"
  using assms coord_ring_to_UP_SA_is_hom ring_hom_add
  by (metis (mono_tags, opaque_lifting))

lemma coord_ring_to_UP_SA_mult:
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>Suc n\<^esub>])"
  assumes "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>Suc n\<^esub>])"
  shows "coord_ring_to_UP_SA n (f \<otimes>\<^bsub>Q\<^sub>p[\<X>\<^bsub>Suc n\<^esub>]\<^esub>g) = coord_ring_to_UP_SA n f  \<otimes>\<^bsub>UP (SA n)\<^esub> coord_ring_to_UP_SA n g"
  using assms coord_ring_to_UP_SA_is_hom ring_hom_mult
  by (metis (no_types, opaque_lifting))

lemma coord_ring_to_UP_SA_one:
  shows "coord_ring_to_UP_SA n \<one>\<^bsub>Q\<^sub>p[\<X>\<^bsub>Suc n\<^esub>]\<^esub> = \<one>\<^bsub>UP (SA n)\<^esub>"
  using coord_ring_to_UP_SA_is_hom ring_hom_one
  by blast

lemma coord_ring_to_UP_SA_closed:
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>Suc n\<^esub>])"
  shows "coord_ring_to_UP_SA n f \<in> carrier (UP (SA n))"
  using assms coord_ring_to_UP_SA_is_hom ring_hom_closed
  by (metis (no_types, opaque_lifting))

lemma coord_ring_to_UP_SA_constant:
  assumes "c \<in> carrier Q\<^sub>p"
  shows "coord_ring_to_UP_SA n (Qp.indexed_const c) = to_polynomial (SA n) (\<cc>\<^bsub>n\<^esub> c)"
proof-
  have 0: "pre_to_univ_poly (Suc n) 0 (Qp.indexed_const c) = ring.indexed_const (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) (Qp.indexed_const c)"
    unfolding to_univ_poly_def
    using pre_to_univ_poly_is_hom(5)[of 0 "Suc n" "pre_to_univ_poly (Suc n) 0" c] assms unfolding coord_ring_def
    using diff_Suc_1 zero_less_Suc by presburger
  hence 1: "to_univ_poly (Suc n) 0 (Qp.indexed_const c) = to_polynomial (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) (Qp.indexed_const c) "
    unfolding to_univ_poly_def
    using UP_cring.IP_to_UP_indexed_const[of "Q\<^sub>p[\<X>\<^bsub>n\<^esub>]" "Qp.indexed_const c" "0::nat"] assms
          comp_apply[of "IP_to_UP (0::nat)" "pre_to_univ_poly (Suc n) (0::nat)" "Qp.indexed_const c"]
    unfolding UP_cring_def using Qp_to_IP_car coord_cring_cring by presburger
  have 2: "Qp_ev_hom n (Qp.indexed_const c) = \<cc>\<^bsub>n\<^esub> c"
    using Qp_ev_hom_constant[of c n] assms by blast
  have 3: "poly_lift_hom (Q\<^sub>p [\<X>\<^bsub>n\<^esub>]) (SA n) (Qp_ev_hom n) (to_polynomial (Q\<^sub>p [\<X>\<^bsub>n\<^esub>]) (Qp.indexed_const c)) = to_polynomial (SA n) (Qp_ev_hom n (Qp.indexed_const c))"
    using UP_cring.poly_lift_hom_extends_hom[of "Q\<^sub>p[\<X>\<^bsub>n\<^esub>]" "SA n" "Qp_ev_hom n" "Qp.indexed_const c"]
    unfolding UP_cring_def coord_ring_def coord_ring_to_UP_SA_def
    by (metis Qp_ev_hom_is_hom Qp_to_IP_car SA_is_cring assms(1) coord_cring_cring coord_ring_def)
  hence 4: "poly_lift_hom (Q\<^sub>p [\<X>\<^bsub>n\<^esub>]) (SA n) (Qp_ev_hom n) (to_univ_poly (Suc n) 0 (Qp.indexed_const c) ) = to_polynomial (SA n) (\<cc>\<^bsub>n\<^esub> c)"
    using "1" "2" by presburger
  show ?thesis
    using assms 4 Qp.indexed_const_closed[of c "{..<n}"]
          comp_apply[of "poly_lift_hom (Pring Q\<^sub>p {..<n}) (SA n) (Qp_ev_hom n)" "to_univ_poly (Suc n) 0" "Qp.indexed_const c"]
    unfolding coord_ring_to_UP_SA_def
    by (metis coord_ring_def)
qed

lemma coord_ring_to_UP_SA_pvar_0:
  shows "coord_ring_to_UP_SA n (pvar Q\<^sub>p 0) = up_ring.monom (UP (SA n)) \<one>\<^bsub>SA n\<^esub> 1"
proof-
  have 0: "pre_to_univ_poly (Suc n) 0 (pvar Q\<^sub>p 0) = pvar (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) 0"
    using pre_to_univ_poly_is_hom(3)[of 0 "Suc n" "pre_to_univ_poly (Suc n) 0"] diff_Suc_1 zero_less_Suc
    by presburger
  have 1: "IP_to_UP (0::nat) (pvar (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) 0) = up_ring.monom (UP (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])) \<one>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> 1"
    using cring.IP_to_UP_var[of "Q\<^sub>p[\<X>\<^bsub>n\<^esub>]" "0::nat"] unfolding X_poly_def var_to_IP_def
    using coord_cring_cring by blast
  have 2: "to_univ_poly (Suc n) 0 (pvar Q\<^sub>p 0) = up_ring.monom (UP (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])) \<one>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> 1"
    unfolding to_univ_poly_def using 0 1 comp_apply
    by metis
  have 3: "poly_lift_hom (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) (SA n) (Qp_ev_hom n) (up_ring.monom (UP (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])) \<one>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> 1)
             = up_ring.monom (UP (SA n)) \<one>\<^bsub>SA n\<^esub> 1"
    using UP_cring.poly_lift_hom_monom[of "Q\<^sub>p[\<X>\<^bsub>n\<^esub>]" "SA n" "Qp_ev_hom n"]
    unfolding UP_cring_def
    using MP.one_closed Qp_ev_hom_is_hom Qp_ev_hom_one SA_is_cring coord_cring_cring by presburger
  thus ?thesis unfolding coord_ring_to_UP_SA_def
    using 2 3  comp_apply
    by metis
qed

lemma coord_ring_to_UP_SA_pvar_Suc:
  assumes "i > 0"
  assumes "i < Suc n"
  shows "coord_ring_to_UP_SA n (pvar Q\<^sub>p i) = to_polynomial (SA n) (\<vv>\<^bsub>n, i-1\<^esub>)"
proof-
  have 0: "pre_to_univ_poly (Suc n) 0 (pvar Q\<^sub>p i) = ring.indexed_const (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) (pvar Q\<^sub>p (i-1))"
    using pre_to_univ_poly_is_hom(4)[of 0 "Suc n" "pre_to_univ_poly (Suc n) 0" i] diff_Suc_1 zero_less_Suc
          assms
    unfolding coord_ring_def by presburger
  have 1: "IP_to_UP (0::nat) (ring.indexed_const (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) (pvar Q\<^sub>p (i-1))) = to_polynomial (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) (pvar Q\<^sub>p (i-1))"
    using UP_cring.IP_to_UP_indexed_const[of "Q\<^sub>p[\<X>\<^bsub>n\<^esub>]" "pvar Q\<^sub>p (i-1)" "0::nat"] coord_cring_cring
    unfolding UP_cring_def
    by (metis assms diff_less less_Suc_eq less_imp_diff_less less_numeral_extra(1) local.pvar_closed)
  have 2: "to_univ_poly (Suc n) 0 (pvar Q\<^sub>p i) = to_polynomial (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) (pvar Q\<^sub>p (i-1))"
    unfolding to_univ_poly_def using 0 1 comp_apply
    by metis
  have 3: "poly_lift_hom (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) (SA n) (Qp_ev_hom n) (to_polynomial (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) (pvar Q\<^sub>p (i-1)))
             = to_polynomial (SA n) (\<vv>\<^bsub>n, (i-1)\<^esub>)"
    using UP_cring.poly_lift_hom_extends_hom[of "Q\<^sub>p[\<X>\<^bsub>n\<^esub>]" "SA n" "Qp_ev_hom n" "pvar Q\<^sub>p (i-1)"]
    unfolding UP_cring_def
    by (metis (no_types, lifting) Qp_ev_hom_is_hom Qp_ev_hom_pvar SA_is_cring Suc_diff_1
        Suc_less_eq assms  coord_cring_cring local.pvar_closed)
  thus ?thesis unfolding coord_ring_to_UP_SA_def
    using 2 3 assms comp_apply
    by metis
qed

lemma coord_ring_to_UP_SA_eval:
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>Suc n\<^esub>])"
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "t \<in> carrier Q\<^sub>p"
  shows "Qp_ev f (t#a) = ((SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n f))) \<bullet> t"
proof(rule coord_ring_car_induct[of f "Suc n"])
  have ta_closed: "t # a \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
    using assms cartesian_power_cons  by (metis Suc_eq_plus1)
  show "f \<in> carrier (Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>])"
    by (simp add: assms)
  show "\<And>c. c \<in> carrier Q\<^sub>p \<Longrightarrow> eval_at_point Q\<^sub>p (t # a) (Qp.indexed_const c) = SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n (Qp.indexed_const c)) \<bullet> t"
  proof- fix c assume A: "c \<in> carrier Q\<^sub>p"
    have 0: "eval_at_point Q\<^sub>p (t # a) (Qp.indexed_const c) = c"
      using A eval_at_point_const ta_closed by blast
    have 1: "SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n (Qp.indexed_const c)) = to_polynomial Q\<^sub>p c"
      using coord_ring_to_UP_SA_constant[of c n]  A Qp_constE SA_car
            SA_poly_to_Qp_poly_extends_apply assms  constant_function_in_semialg_functions
      by presburger
    show "eval_at_point Q\<^sub>p (t # a) (Qp.indexed_const c) = SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n (Qp.indexed_const c)) \<bullet> t"
      using 0 1 A UPQ.to_fun_to_poly assms by presburger
  qed
  show " \<And>p q. p \<in> carrier (Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>]) \<Longrightarrow>
           q \<in> carrier (Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>]) \<Longrightarrow>
           eval_at_point Q\<^sub>p (t # a) p = SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n p) \<bullet> t \<Longrightarrow>
           eval_at_point Q\<^sub>p (t # a) q = SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n q) \<bullet> t \<Longrightarrow>
           eval_at_point Q\<^sub>p (t # a) (p \<oplus>\<^bsub>Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>]\<^esub> q) = SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n (p \<oplus>\<^bsub>Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>]\<^esub> q)) \<bullet> t"
  proof- fix p q assume A: "p \<in> carrier (Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>])" "q \<in> carrier (Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>])"
           "eval_at_point Q\<^sub>p (t # a) p = SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n p) \<bullet> t"
           "eval_at_point Q\<^sub>p (t # a) q = SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n q) \<bullet> t"
    have 0: "eval_at_point Q\<^sub>p (t # a) (p \<oplus>\<^bsub>Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>]\<^esub> q) = eval_at_point Q\<^sub>p (t # a) p \<oplus> eval_at_point Q\<^sub>p (t # a) q"
      using A(1) A(2) eval_at_point_add ta_closed by blast
    have 1: "SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n (p \<oplus>\<^bsub>Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>]\<^esub> q))=
    SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n p)  \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n q)"
      using coord_ring_to_UP_SA_add[of ] assms coord_ring_to_UP_SA_closed A
            SA_poly_to_Qp_poly_add[of  a n "coord_ring_to_UP_SA n p" "coord_ring_to_UP_SA n q"]
      by presburger
    show "eval_at_point Q\<^sub>p (t # a) (p \<oplus>\<^bsub>Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>]\<^esub> q) = SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n (p \<oplus>\<^bsub>Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>]\<^esub> q)) \<bullet> t"
      using 0 1  assms SA_poly_to_Qp_poly_closed[of a n] SA_poly_to_Qp_poly_closed A(1) A(2) A(3) A(4) UPQ.to_fun_plus coord_ring_to_UP_SA_closed
      by presburger
  qed
  show "\<And>p i. p \<in> carrier (Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>]) \<Longrightarrow>
           i < Suc n \<Longrightarrow>
           eval_at_point Q\<^sub>p (t # a) p = SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n p) \<bullet> t \<Longrightarrow>
           eval_at_point Q\<^sub>p (t # a) (p \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>]\<^esub> pvar Q\<^sub>p i) = SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n (p \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>]\<^esub> pvar Q\<^sub>p i)) \<bullet> t"
  proof- fix p i assume A: "p \<in> carrier (Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>])" "i < Suc n"
           "eval_at_point Q\<^sub>p (t # a) p = SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n p) \<bullet> t"
    show " eval_at_point Q\<^sub>p (t # a) (p \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>]\<^esub> pvar Q\<^sub>p i) = SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n (p \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>]\<^esub> pvar Q\<^sub>p i)) \<bullet> t"
    proof-
      have 0: "eval_at_point Q\<^sub>p (t # a) (p \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>]\<^esub> pvar Q\<^sub>p i) = eval_at_point Q\<^sub>p (t # a) p \<otimes>  eval_at_point Q\<^sub>p (t # a) (pvar Q\<^sub>p i)"
        using A(1) A(2) eval_at_point_mult local.pvar_closed ta_closed by blast
      have 1: "coord_ring_to_UP_SA n (p \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>]\<^esub> pvar Q\<^sub>p i) = coord_ring_to_UP_SA n p \<otimes>\<^bsub>UP (SA n)\<^esub> coord_ring_to_UP_SA n (pvar Q\<^sub>p i)"
        using A(1) A(2) assms(1) coord_ring_to_UP_SA_mult local.pvar_closed by blast
      hence 2: "SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n (p \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>]\<^esub> pvar Q\<^sub>p i)) =
              SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n p) \<otimes>\<^bsub>UP Q\<^sub>p\<^esub>SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n (pvar Q\<^sub>p i))"
        using SA_poly_to_Qp_poly_mult coord_ring_to_UP_SA_closed A(1) A(2) assms local.pvar_closed
        by presburger
      show "eval_at_point Q\<^sub>p (t # a) (p \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>]\<^esub> pvar Q\<^sub>p i) = SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n (p \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>]\<^esub> pvar Q\<^sub>p i)) \<bullet> t"
      proof(cases  "i = 0")
        case True
        have T0: "SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n (p \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>]\<^esub> pvar Q\<^sub>p i)) =
              SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n p) \<otimes>\<^bsub>UP Q\<^sub>p\<^esub> up_ring.monom (UP Q\<^sub>p) \<one> 1"
          using True coord_ring_to_UP_SA_pvar_0 SA_poly_to_Qp_poly_monom
          by (metis "2" function_one_eval Qp.one_closed SA_car SA_one assms constant_function_in_semialg_functions function_one_as_constant)
        have T1: "eval_at_point Q\<^sub>p (t # a) (p \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>]\<^esub> pvar Q\<^sub>p i) = eval_at_point Q\<^sub>p (t # a) p \<otimes>  t"
          using 0 True ta_closed eval_pvar[of 0 "Suc n" "t#a"]
          by (metis A(2) nth_Cons_0)
        then show ?thesis
          using T0 A SA_poly_to_Qp_poly_closed[of a n  "coord_ring_to_UP_SA n p"] UPQ.to_fun_X[of t] to_fun_mult
                coord_ring_to_UP_SA_closed[of  ] UPQ.X_closed[of ] unfolding X_poly_def
          using assms UPQ.to_fun_mult by presburger
      next
        case False
        have "\<vv>\<^bsub>n, i - 1\<^esub> a = a!(i-1)"
          by (metis A(2) False Qp.varE Suc_diff_1 Suc_less_eq assms  less_Suc_eq_0_disj)
        hence F0: "SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n (p \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>]\<^esub> pvar Q\<^sub>p i)) =
              SA_poly_to_Qp_poly n a (coord_ring_to_UP_SA n p) \<otimes>\<^bsub>UP Q\<^sub>p\<^esub> to_polynomial Q\<^sub>p (a!(i-1))"
          using False coord_ring_to_UP_SA_pvar_Suc[of i n] SA_poly_to_Qp_poly_extends_apply[of a n "\<vv>\<^bsub>n, i - 1\<^esub>"]
          by (metis (no_types, lifting) "2" A(2) Qp_ev_hom_in_SA Qp_ev_hom_pvar Suc_diff_1 Suc_less_eq assms  local.pvar_closed neq0_conv)
        have F1: "eval_at_point Q\<^sub>p (t # a) (p \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>Suc n\<^esub>]\<^esub> pvar Q\<^sub>p i) = eval_at_point Q\<^sub>p (t # a) p \<otimes> (a!(i-1))"
          using 0 False ta_closed eval_pvar[of i "Suc n" "t#a"]
          by (metis A(2) nth_Cons')
        then show ?thesis
          using F0 A SA_poly_to_Qp_poly_closed[of a n "coord_ring_to_UP_SA n p"] to_fun_mult
                coord_ring_to_UP_SA_closed[of p n]   False UPQ.to_fun_to_poly UPQ.to_poly_closed assms
              eval_at_point_closed eval_pvar local.pvar_closed neq0_conv nth_Cons_pos ta_closed
          by (metis (no_types, lifting) UPQ.to_fun_mult)
      qed
    qed
  qed
qed


(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Gluing Semialgebraic Polynomials\<close>
(**************************************************************************************************)
(**************************************************************************************************)


definition SA_poly_glue where
"SA_poly_glue m S f g = (\<lambda> n. fun_glue m S (f n) (g n))"

lemma SA_poly_glue_closed:
  assumes "f \<in> carrier (UP (SA m))"
  assumes "g \<in> carrier (UP (SA m))"
  assumes "is_semialgebraic m S"
  shows "SA_poly_glue m S f g \<in> carrier (UP (SA m))"
proof(rule UP_car_memI[of "max (deg (SA m) f) (deg (SA m) g)"])
  fix n assume A: "max (deg (SA m) f) (deg (SA m) g) < n" show "SA_poly_glue m S f g n = \<zero>\<^bsub>SA m\<^esub>"
    unfolding SA_poly_glue_def
  proof-
    have 0: "n > (deg (SA m) f)"
      using A by simp
    have 1: "n > (deg (SA m) g)"
      using A by simp
    have 2: "f n = \<zero>\<^bsub>SA m\<^esub>"
      using 0 assms UPSA.deg_leE by blast
    have 3: "g n = \<zero>\<^bsub>SA m\<^esub>"
      using 1 assms UPSA.deg_leE by blast
    show "fun_glue m S (f n) (g n) = \<zero>\<^bsub>SA m\<^esub>"
      unfolding SA_zero function_ring_def ring_record_simps function_zero_def 2 3
    proof fix x
      show " fun_glue m S (\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<zero>) (\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<zero>) x = (\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<zero>) x"
        apply(cases "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)")
        unfolding fun_glue_def restrict_def apply presburger
        by auto
    qed
  qed
  next
  show " \<And>n. SA_poly_glue m S f g n \<in> carrier (SA m)"
    unfolding SA_poly_glue_def apply(rule fun_glue_closed)
    by(rule cfs_closed, rule assms, rule cfs_closed, rule assms, rule assms)
qed

lemma SA_poly_glue_deg:
  assumes "f \<in> carrier (UP (SA m))"
  assumes "g \<in> carrier (UP (SA m))"
  assumes "is_semialgebraic m S"
  assumes "deg (SA m) f \<le> d"
  assumes "deg (SA m) g \<le> d"
  shows "deg (SA m) (SA_poly_glue m S f g) \<le> d"
  apply(rule deg_leqI,  rule SA_poly_glue_closed, rule assms, rule assms, rule assms)
proof- fix n assume A: "d < n"
  show "SA_poly_glue m S f g n = \<zero>\<^bsub>SA m\<^esub>"
    unfolding SA_poly_glue_def
  proof-
    have 0: "n > (deg (SA m) f)"
      using A assms by linarith
    have 1: "n > (deg (SA m) g)"
      using A assms by linarith
    have 2: "f n = \<zero>\<^bsub>SA m\<^esub>"
      using 0 assms UPSA.deg_leE by blast
    have 3: "g n = \<zero>\<^bsub>SA m\<^esub>"
      using 1 assms UPSA.deg_leE by blast
    show "fun_glue m S (f n) (g n) = \<zero>\<^bsub>SA m\<^esub>"
      unfolding SA_zero function_ring_def ring_record_simps function_zero_def 2 3
    proof fix x
      show " fun_glue m S (\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<zero>) (\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<zero>) x = (\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<zero>) x"
        apply(cases "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)")
        unfolding fun_glue_def restrict_def apply presburger
        by auto
    qed
  qed
qed

lemma UP_SA_cfs_closed:
  assumes "g \<in> carrier (UP (SA m))"
  shows "g k \<in> carrier (SA m)"
  using assms UP_ring.cfs_closed[of "SA m" g k] SA_is_ring[of m] unfolding UP_ring_def
  by blast


lemma SA_poly_glue_cfs1:
  assumes "f \<in> carrier (UP (SA m))"
  assumes "g \<in> carrier (UP (SA m))"
  assumes "is_semialgebraic m S"
  assumes "x \<in> S"
  shows "(SA_poly_glue m S f g) n x = f n x"
  unfolding SA_poly_glue_def fun_glue_def restrict_def
  using assms
  by (metis SA_car local.function_ring_not_car padic_fields.UP_SA_cfs_closed padic_fields_axioms semialg_functions_memE(2))

lemma SA_poly_glue_cfs2:
  assumes "f \<in> carrier (UP (SA m))"
  assumes "g \<in> carrier (UP (SA m))"
  assumes "is_semialgebraic m S"
  assumes "x \<notin> S"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "(SA_poly_glue m S f g) n x = g n x"
  unfolding SA_poly_glue_def fun_glue_def restrict_def
  using assms by meson

lemma SA_poly_glue_to_Qp_poly1:
  assumes "f \<in> carrier (UP (SA m))"
  assumes "g \<in> carrier (UP (SA m))"
  assumes "is_semialgebraic m S"
  assumes "x \<in> S"
  shows "SA_poly_to_Qp_poly m x (SA_poly_glue m S f g) = SA_poly_to_Qp_poly m x f"
proof fix n
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms is_semialgebraic_closed by blast
  have 0: "SA_poly_to_Qp_poly m x (SA_poly_glue m S f g) n = (SA_poly_glue m S f g) n x"
    by(rule SA_poly_to_Qp_poly_coeff[of x m "SA_poly_glue m S f g"], rule x_closed, rule SA_poly_glue_closed
          , rule assms, rule assms, rule assms)
  have 1: "(SA_poly_glue m S f g) n x = f n x"
    by(rule SA_poly_glue_cfs1 , rule assms, rule assms, rule assms, rule assms)
  show "SA_poly_to_Qp_poly m x (SA_poly_glue m S f g) n = SA_poly_to_Qp_poly m x f n"
    unfolding 0 1 using SA_poly_to_Qp_poly_coeff[of x m f n] assms (1) x_closed by blast
qed

lemma SA_poly_glue_to_Qp_poly2:
  assumes "f \<in> carrier (UP (SA m))"
  assumes "g \<in> carrier (UP (SA m))"
  assumes "is_semialgebraic m S"
  assumes "x \<notin> S"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "SA_poly_to_Qp_poly m x (SA_poly_glue m S f g) = SA_poly_to_Qp_poly m x g"
proof fix n
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms is_semialgebraic_closed by blast
  have 0: "SA_poly_to_Qp_poly m x (SA_poly_glue m S f g) n = (SA_poly_glue m S f g) n x"
    by(rule SA_poly_to_Qp_poly_coeff[of x m "SA_poly_glue m S f g"], rule x_closed, rule SA_poly_glue_closed
          , rule assms, rule assms, rule assms)
  have 1: "(SA_poly_glue m S f g) n x = g n x"
    by(rule SA_poly_glue_cfs2 , rule assms, rule assms, rule assms, rule assms, rule x_closed)
  show "SA_poly_to_Qp_poly m x (SA_poly_glue m S f g) n = SA_poly_to_Qp_poly m x g n"
    unfolding 0 1 using SA_poly_to_Qp_poly_coeff[of x m g n] assms x_closed by blast
qed


(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Polynomials over the Valuation Ring\<close>
(**************************************************************************************************)
(**************************************************************************************************)


definition integral_on where
"integral_on m B = {f \<in> carrier (UP (SA m)). (\<forall>x \<in> B. \<forall>i. SA_poly_to_Qp_poly m x f i \<in> \<O>\<^sub>p)}"

lemma integral_on_memI:
  assumes "f \<in> carrier (UP (SA m))"
  assumes "\<And>x i. x \<in> B \<Longrightarrow> SA_poly_to_Qp_poly m x f i \<in> \<O>\<^sub>p"
  shows "f \<in> integral_on m B"
  unfolding integral_on_def mem_Collect_eq using assms by blast

lemma integral_on_memE:
  assumes "f \<in> integral_on m B"
  shows  "f \<in> carrier (UP (SA m))"
          "\<And>x. x \<in> B \<Longrightarrow> SA_poly_to_Qp_poly m x f i \<in> \<O>\<^sub>p"
 using assms unfolding integral_on_def mem_Collect_eq apply blast
 using assms unfolding integral_on_def mem_Collect_eq by blast

lemma one_integral_on:
  assumes "B \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "\<one> \<^bsub>UP (SA m)\<^esub> \<in> integral_on m B"
  apply(rule integral_on_memI)
  apply blast
proof- fix x i assume A: "x \<in> B"
  have 0: "SA_poly_to_Qp_poly m x \<one>\<^bsub>UP (SA m)\<^esub> = \<one>\<^bsub>UP Q\<^sub>p\<^esub>"
    apply(rule ring_hom_one[of _ "UP (SA m)"])
    using SA_poly_to_Qp_poly_is_hom[of x m] A assms by blast
  show "SA_poly_to_Qp_poly m x \<one>\<^bsub>UP (SA m)\<^esub> i \<in> \<O>\<^sub>p"
    unfolding 0
    apply(rule val_ring_memI)
     apply(rule UPQ.cfs_closed)
     apply blast
    apply(cases "i = 0")
     apply (metis Qp.add.nat_pow_eone Qp.one_closed UPQ.cfs_one val_of_nat_inc val_one)
    by (metis Qp.int_inc_zero UPQ.cfs_one val_of_int_inc)
qed

lemma integral_on_plus:
  assumes "B \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "f \<in> integral_on m B"
  assumes "g \<in> integral_on m B"
  shows "f \<oplus>\<^bsub>UP (SA m)\<^esub> g \<in> integral_on m B"
proof(rule integral_on_memI)
  show "f \<oplus>\<^bsub>UP (SA m)\<^esub> g \<in> carrier (UP (SA m))"
    using assms integral_on_memE by blast
  show "\<And>x i. x \<in> B \<Longrightarrow> SA_poly_to_Qp_poly m x (f \<oplus>\<^bsub>UP (SA m)\<^esub> g) i \<in> \<O>\<^sub>p"
  proof- fix x i assume A: "x \<in> B"
    have 0: "SA_poly_to_Qp_poly m x (f \<oplus>\<^bsub>UP (SA m)\<^esub> g) = SA_poly_to_Qp_poly m x f
                                                          \<oplus>\<^bsub>UP Q\<^sub>p\<^esub>  SA_poly_to_Qp_poly m x g"
      apply(rule SA_poly_to_Qp_poly_add)
      using A assms apply blast using assms integral_on_memE apply blast
      using assms integral_on_memE by blast
    have 1: "SA_poly_to_Qp_poly m x (f \<oplus>\<^bsub>UP (SA m)\<^esub> g) i = SA_poly_to_Qp_poly m x f i
                                                          \<oplus>  SA_poly_to_Qp_poly m x g i"
      unfolding 0 apply(rule UPQ.cfs_add)
       apply(rule SA_poly_to_Qp_poly_closed)
      using  A assms apply blast
      using assms integral_on_memE  apply blast
       apply(rule SA_poly_to_Qp_poly_closed)
      using  A assms apply blast
      using assms integral_on_memE  by blast
    show "SA_poly_to_Qp_poly m x (f \<oplus>\<^bsub>UP (SA m)\<^esub> g) i \<in> \<O>\<^sub>p"
      unfolding 1 using assms integral_on_memE
      using A val_ring_add_closed by presburger
  qed
qed

lemma integral_on_times:
  assumes "B \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "f \<in> integral_on m B"
  assumes "g \<in> integral_on m B"
  shows "f \<otimes>\<^bsub>UP (SA m)\<^esub> g \<in> integral_on m B"
proof(rule integral_on_memI)
  show "f \<otimes>\<^bsub>UP (SA m)\<^esub> g \<in> carrier (UP (SA m))"
    using assms integral_on_memE by blast
  show "\<And>x i. x \<in> B \<Longrightarrow> SA_poly_to_Qp_poly m x (f \<otimes>\<^bsub>UP (SA m)\<^esub> g) i \<in> \<O>\<^sub>p"
  proof- fix x i assume A: "x \<in> B"
    have 0: "SA_poly_to_Qp_poly m x (f \<otimes>\<^bsub>UP (SA m)\<^esub> g) = SA_poly_to_Qp_poly m x f
                                                          \<otimes>\<^bsub>UP Q\<^sub>p\<^esub>  SA_poly_to_Qp_poly m x g"
      apply(rule SA_poly_to_Qp_poly_mult)
      using A assms apply blast using assms integral_on_memE apply blast
      using assms integral_on_memE by blast
    obtain S where S_def: "S = UP (Q\<^sub>p \<lparr> carrier := \<O>\<^sub>p \<rparr>)"
      by blast
    have 1: "cring S"
      unfolding S_def apply(rule UPQ.UP_ring_subring_is_ring)
      using val_ring_subring by blast
    have 2: " carrier S = {h \<in> carrier (UP Q\<^sub>p). \<forall>n. h n \<in> \<O>\<^sub>p}"
      unfolding S_def  using UPQ.UP_ring_subring_car[of \<O>\<^sub>p] val_ring_subring by blast
    have 3: "SA_poly_to_Qp_poly m x f \<in> carrier S"
      unfolding 2 mem_Collect_eq using assms integral_on_memE SA_poly_to_Qp_poly_closed A
      by blast
    have 4: "SA_poly_to_Qp_poly m x g \<in> carrier S"
      unfolding 2 mem_Collect_eq using assms integral_on_memE SA_poly_to_Qp_poly_closed A
      by blast
    have 5: "SA_poly_to_Qp_poly m x (f \<otimes>\<^bsub>UP (SA m)\<^esub> g) \<in> carrier S"
      unfolding 0
      using  cring.cring_simprules(5)[of S]3 4 1 UPQ.UP_ring_subring_mult[of \<O>\<^sub>p "SA_poly_to_Qp_poly m x f" "SA_poly_to_Qp_poly m x g"]
      using S_def val_ring_subring by metis
    show "SA_poly_to_Qp_poly m x (f \<otimes>\<^bsub>UP (SA m)\<^esub> g) i \<in> \<O>\<^sub>p"
      using 5 unfolding 2 mem_Collect_eq by blast
  qed
qed

lemma integral_on_a_minus:
  assumes "B \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "f \<in> integral_on m B"
  shows "\<ominus>\<^bsub>UP (SA m)\<^esub> f \<in> integral_on m B"
  apply(rule integral_on_memI)
  using assms integral_on_memE(1)[of f m B]
  apply blast
proof- fix x i assume A: "x \<in> B"
  have 0: "SA_poly_to_Qp_poly m x (\<ominus>\<^bsub>UP (SA m)\<^esub> f) = \<ominus>\<^bsub>UP Q\<^sub>p\<^esub> SA_poly_to_Qp_poly m x f"
    apply(rule  UP_cring.ring_hom_uminus[of "UP Q\<^sub>p" "UP (SA m)" "SA_poly_to_Qp_poly m x" f ] )
    unfolding UP_cring_def
       apply (simp add: UPQ.M_cring)
      apply (simp add: UPSA.P.ring_axioms)
     apply(rule SA_poly_to_Qp_poly_is_hom)
    using A assms apply blast
    using assms integral_on_memE by blast
  have 2: "\<And>f. f \<in> carrier (UP Q\<^sub>p) \<Longrightarrow> (\<ominus>\<^bsub>UP Q\<^sub>p\<^esub> f) i = \<ominus> (f i)"
    using UPQ.cfs_a_inv by blast
  have 1: "SA_poly_to_Qp_poly m x (\<ominus>\<^bsub>UP (SA m)\<^esub> f) i = \<ominus> (SA_poly_to_Qp_poly m x f) i "
    unfolding 0 apply(rule 2)
    using integral_on_memE  assms A SA_poly_to_Qp_poly_closed[of x m f] by blast
  show "SA_poly_to_Qp_poly m x (\<ominus>\<^bsub>UP (SA m)\<^esub> f) i \<in> \<O>\<^sub>p"
    unfolding 1 using A assms integral_on_memE(2)[of f m B x i]
    using val_ring_ainv_closed by blast
qed

lemma integral_on_subring:
  assumes "B \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "subring (integral_on m B) (UP (SA m))"
proof(rule subringI)
  show "integral_on m B \<subseteq> carrier (UP (SA m))"
    unfolding integral_on_def by blast
  show "\<one>\<^bsub>UP (SA m)\<^esub> \<in> integral_on m B"
    using one_integral_on assms by blast
  show " \<And>h. h \<in> integral_on m B \<Longrightarrow> \<ominus>\<^bsub>UP (SA m)\<^esub> h \<in> integral_on m B"
    using integral_on_a_minus assms by blast
  show "\<And>h1 h2. h1 \<in> integral_on m B \<Longrightarrow> h2 \<in> integral_on m B \<Longrightarrow> h1 \<otimes>\<^bsub>UP (SA m)\<^esub> h2 \<in> integral_on m B"
    using integral_on_times assms by blast
  show "\<And>h1 h2. h1 \<in> integral_on m B \<Longrightarrow> h2 \<in> integral_on m B \<Longrightarrow> h1 \<oplus>\<^bsub>UP (SA m)\<^esub> h2 \<in> integral_on m B"
    using integral_on_plus assms by blast
qed

lemma val_ring_add_pow:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "val a \<ge> 0"
  shows "val ([(n::nat)]\<cdot>a) \<ge> 0"
proof-
  have 0: "[(n::nat)]\<cdot>a = ([n]\<cdot>\<one>)\<otimes>a"
    using assms Qp.add_pow_ldistr Qp.cring_simprules(12) Qp.one_closed by presburger
  show ?thesis unfolding 0 using assms
    by (meson Qp.nat_inc_closed val_ring_memE val_of_nat_inc val_ringI val_ring_times_closed)
qed

lemma val_ring_poly_eval:
  assumes "f \<in> carrier (UP Q\<^sub>p)"
  assumes "\<And> i. f i \<in> \<O>\<^sub>p"
  shows "\<And>x. x \<in> \<O>\<^sub>p \<Longrightarrow> f \<bullet> x \<in> \<O>\<^sub>p"
proof- fix x assume A: "x \<in> \<O>\<^sub>p"
  obtain S where S_def: "S = (Q\<^sub>p \<lparr> carrier := \<O>\<^sub>p \<rparr>)"
    by blast
  have 0: "UP_cring S"
    unfolding S_def apply(rule UPQ.UP_ring_subring(1))
    using val_ring_subring by blast
  have 1: "to_function Q\<^sub>p f x = to_function S f x"
    unfolding S_def  apply(rule UPQ.UP_subring_eval)
    using val_ring_subring apply blast
    apply(rule UPQ.poly_cfs_subring)    using val_ring_subring apply blast
    using assms apply blast
    using assms apply blast using A by blast
  have 2: "f \<in> carrier (UP S)"
    unfolding S_def
    using UPQ.UP_ring_subring_car[of \<O>\<^sub>p] assms val_ring_subring by blast
  have 3: "to_function S f x \<in> \<O>\<^sub>p"
      using UPQ.UP_subring_eval_closed[of \<O>\<^sub>p f x]
    using 1 0 UP_cring.to_fun_closed[of S f x]
    unfolding S_def
    by (metis "2" A S_def UPQ.to_fun_def val_ring_subring)
  thus "f \<bullet> x \<in> \<O>\<^sub>p"
    using 1 UPQ.to_fun_def by presburger
qed

lemma SA_poly_constant_res_class_semialg':
  assumes "f \<in> carrier (UP (SA m))"
  assumes "\<And>i x. x \<in> B \<Longrightarrow> f i x \<in> \<O>\<^sub>p"
  assumes "deg (SA m) f \<le> d"
  assumes "C \<in> poly_res_classes n d"
  assumes "is_semialgebraic m B"
  shows "is_semialgebraic m {x \<in> B. SA_poly_to_Qp_poly m x f \<in> C}"
proof-
  obtain g where g_def: "g = SA_poly_glue m B f (\<one>\<^bsub>UP (SA m)\<^esub>)"
    by blast
  have g_closed: "g \<in> carrier (UP (SA m))"
    unfolding g_def by(rule SA_poly_glue_closed, rule assms, blast, rule assms)
  have g_deg: "deg (SA m) g \<le> d"
    unfolding g_def apply(rule SA_poly_glue_deg, rule assms, blast, rule assms, rule assms)
    unfolding deg_one by blast
  have 0: "{x \<in> B. SA_poly_to_Qp_poly m x f \<in> C} = B \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). SA_poly_to_Qp_poly m x g \<in> C}"
    apply(rule equalityI', rule IntI, blast)
    unfolding mem_Collect_eq apply(rule conjI)
    using assms is_semialgebraic_closed apply blast
    unfolding g_def using SA_poly_glue_cfs1[of f m "\<one>\<^bsub>UP (SA m)\<^esub>" B] assms
    using SA_poly_glue_to_Qp_poly1 UPSA.P.cring_simprules(6) apply presburger
    unfolding g_def using SA_poly_glue_cfs1[of f m "\<one>\<^bsub>UP (SA m)\<^esub>" B] assms
    using SA_poly_glue_to_Qp_poly1 UPSA.P.cring_simprules(6)
    by (metis (no_types, lifting) Int_iff mem_Collect_eq)
  have 1: "\<And>i x. x \<in> B \<Longrightarrow> g i x = f i x"
    unfolding g_def by(rule SA_poly_glue_cfs1, rule assms, blast, rule assms, blast)
  have 2: "\<And>i x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> g i x \<in> \<O>\<^sub>p"
  proof- fix i x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    show "g i x \<in> \<O>\<^sub>p"
      unfolding g_def apply(cases "x \<in> B")
      using SA_poly_glue_cfs1[of f m "\<one>\<^bsub>UP (SA m)\<^esub>" B x i]
            assms(1) assms(2)[of x i] 1
      using UPSA.P.cring_simprules(6) assms(5) apply presburger
      using SA_poly_glue_cfs2[of g m "\<one>\<^bsub>UP (SA m)\<^esub>" B x i] g_closed assms A
      by (metis (mono_tags, opaque_lifting) SA_poly_glue_cfs2 SA_poly_to_Qp_poly_coeff
          UPSA.P.cring_simprules(6) carrier_is_semialgebraic g_def integral_on_memE(2) is_semialgebraic_closed one_integral_on )
  qed
  have 3: "\<And>i x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> x \<notin> B \<Longrightarrow> g i x = \<one>\<^bsub>UP (SA m)\<^esub> i x"
    unfolding g_def apply(rule SA_poly_glue_cfs2[of f m "\<one>\<^bsub>UP (SA m)\<^esub>" B ])
    by(rule assms, blast, rule assms, blast, blast)
  have 4: "\<And>i x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> x \<notin> B \<Longrightarrow> g i x \<in> \<O>\<^sub>p "
    using 3 cfs_one[of m] 2 by blast
  have 5: "\<And>i x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> g i x \<in> \<O>\<^sub>p"
    using 1 4 assms 2  by blast
  have 6: "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). SA_poly_to_Qp_poly m x g \<in> C}"
    by(rule SA_poly_constant_res_class_semialg[of _ _ d _ n], rule g_closed, rule 5, blast, rule g_deg, rule assms)
  show ?thesis unfolding 0
    by(rule intersection_is_semialg, rule assms, rule 6)
qed

lemma SA_poly_constant_res_class_decomp:
  assumes "f \<in> carrier (UP (SA m))"
  assumes "\<And>i x. x \<in> B \<Longrightarrow> f i x \<in> \<O>\<^sub>p"
  assumes "deg (SA m) f \<le> d"
  assumes "is_semialgebraic m B"
  shows "B = (\<Union> C \<in> poly_res_classes n d. {x \<in> B. SA_poly_to_Qp_poly m x f \<in> C})"
proof(rule equalityI')fix x assume A: "x \<in> B"
  obtain g where g_def: "g = SA_poly_glue m B f (\<one>\<^bsub>UP (SA m)\<^esub>)"
    by blast
  have g_closed: "g \<in> carrier (UP (SA m))"
    unfolding g_def by(rule SA_poly_glue_closed, rule assms, blast, rule assms)
  have g_deg: "deg (SA m) g \<le> d"
    unfolding g_def apply(rule SA_poly_glue_deg, rule assms, blast, rule assms, rule assms)
    unfolding deg_one by blast
  have 1: "\<And>i x. x \<in> B \<Longrightarrow> g i x = f i x"
    unfolding g_def by(rule SA_poly_glue_cfs1, rule assms, blast, rule assms, blast)
  have 2: "\<And>i x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> g i x \<in> \<O>\<^sub>p"
  proof- fix i x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    show "g i x \<in> \<O>\<^sub>p"
      unfolding g_def apply(cases "x \<in> B")
      using SA_poly_glue_cfs1[of f m "\<one>\<^bsub>UP (SA m)\<^esub>" B x i]
            assms(1) assms(2)[of x i] 1
      using UPSA.P.cring_simprules(6) assms(4) apply presburger
      using SA_poly_glue_cfs2[of g m "\<one>\<^bsub>UP (SA m)\<^esub>" B x i] g_closed assms A
      by (metis (mono_tags, opaque_lifting) SA_poly_glue_cfs2 SA_poly_to_Qp_poly_coeff
          UPSA.P.cring_simprules(6) carrier_is_semialgebraic g_def integral_on_memE(2) is_semialgebraic_closed one_integral_on )
  qed
  have 3: "\<And>i x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> x \<notin> B \<Longrightarrow> g i x = \<one>\<^bsub>UP (SA m)\<^esub> i x"
    unfolding g_def apply(rule SA_poly_glue_cfs2[of f m "\<one>\<^bsub>UP (SA m)\<^esub>" B ])
    by(rule assms, blast, rule assms, blast, blast)
  have 4: "\<And>i x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> x \<notin> B \<Longrightarrow> g i x \<in> \<O>\<^sub>p "
    using 3 cfs_one[of m] 2 by blast
  have 5: "\<And>i x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> g i x \<in> \<O>\<^sub>p"
    using 1 4 assms 2  by blast
  have 6: "\<And> i x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> SA_poly_to_Qp_poly m x g i = g i x"
    by(rule SA_poly_to_Qp_poly_coeff, blast, rule g_closed)
  have 7: "\<And> x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> SA_poly_to_Qp_poly m x g \<in> val_ring_polys_grad d"
    apply(rule val_ring_polys_grad_memI, rule SA_poly_to_Qp_poly_closed, blast, rule g_closed)
    unfolding  6 apply(rule 5, blast)
    using g_closed  SA_poly_to_Qp_poly_deg_bound[of g m] g_deg le_trans by blast
  have 8: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> SA_poly_to_Qp_poly m x g \<in> poly_res_class n d (SA_poly_to_Qp_poly m x g)"
    by(rule poly_res_class_refl, rule 7)
  have 9: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> poly_res_class n d (SA_poly_to_Qp_poly m x g) \<in> poly_res_classes n d"
    unfolding poly_res_classes_def using 7 by blast
  have 10: "\<And>x. x \<in> B \<Longrightarrow> SA_poly_to_Qp_poly m x g = SA_poly_to_Qp_poly m x f"
    unfolding g_def by(rule SA_poly_glue_to_Qp_poly1, rule assms, blast, rule assms, blast)
  have 11: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using A is_semialgebraic_closed assms by blast
  have 12: "SA_poly_to_Qp_poly m x g = SA_poly_to_Qp_poly m x f"
    by(rule 10, rule A)
  have 13: "x \<in> {x \<in> B. SA_poly_to_Qp_poly m x f \<in> poly_res_class n d (SA_poly_to_Qp_poly m x g)}"
    using 11 10[of x] A 9[of x] 8[of x] unfolding 12 mem_Collect_eq  by blast
  show  "x \<in> (\<Union>C\<in>poly_res_classes n d. {x \<in> B. SA_poly_to_Qp_poly m x f \<in> C})"
    using 13 9[of x] 11  unfolding 12 mem_simps(8) mem_Collect_eq by auto
next
  show "\<And>x. x \<in> (\<Union>C\<in>poly_res_classes n d. {x \<in> B. SA_poly_to_Qp_poly m x f \<in> C}) \<Longrightarrow> x \<in> B"
    by blast
qed

end

context UP_cring
begin

lemma pderiv_deg_bound:
  assumes "p \<in> carrier P"
  assumes "deg R p \<le> (Suc d)"
  shows "deg R (pderiv p) \<le> d"
proof-
  have "deg R p \<le> (Suc d) \<longrightarrow> deg R (pderiv p) \<le> d"
    apply(rule poly_induct[of p])
      apply (simp add: assms(1))
    using deg_zero pderiv_deg_0 apply presburger
  proof fix p assume A: "(\<And>q. q \<in> carrier P \<Longrightarrow> deg R q < deg R p \<Longrightarrow> deg R q \<le> Suc d \<longrightarrow> deg R (pderiv q) \<le> d)"
                        "p \<in> carrier P" "0 < deg R p" "deg R p \<le> Suc d"
    obtain q where q_def: "q \<in> carrier P \<and> deg R q < deg R p \<and> p = q \<oplus>\<^bsub>P\<^esub> ltrm p"
      using A  ltrm_decomp by metis
    have 0: "deg R (pderiv (ltrm p)) \<le> d"
    proof-
      have 1: "pderiv (ltrm p) = up_ring.monom P ([deg R p] \<cdot> p (deg R p)) (deg R p - 1)"
        using pderiv_monom[of "lcf p" "deg R p"] A  P_def UP_car_memE(1) by auto
      show ?thesis unfolding 1
        by (metis (no_types, lifting) A(2) A(3) A(4) R.add_pow_closed Suc_diff_1 cfs_closed deg_monom_le le_trans not_less_eq_eq)
    qed
    have "deg R q \<le> Suc d" using A q_def  by linarith
    then have 1: "deg R (pderiv q) \<le> d"
      using A q_def by blast
    hence "max (deg R (pderiv q)) (deg R (pderiv (up_ring.monom P (p (deg R p)) (deg R p)))) \<le>  d"
      using 0 max.bounded_iff by blast
    thus "deg R (pderiv p) \<le> d "
      using q_def pderiv_add pderiv_monom[of "lcf p" "deg R p"] A deg_add[of "pderiv q" "pderiv (ltrm p)"]
      by (metis "0" "1" ltrm_closed bound_deg_sum pderiv_closed)
  qed
  thus ?thesis
    using assms(2) by blast
qed

lemma(in cring) minus_zero:
"a \<in> carrier R \<Longrightarrow> a \<ominus> \<zero> = a"
  unfolding a_minus_def
  by (metis add.l_cancel_one' cring_simprules(2) cring_simprules(22))

lemma (in UP_cring) taylor_expansion_at_zero:
  assumes "g \<in> carrier (UP R)"
  shows "taylor_expansion R \<zero> g = g"
proof-
  have 0: "X_plus \<zero> = X_poly R"
    unfolding X_poly_plus_def
    by (metis ctrm_degree lcf_eq P.r_zero P_def R.zero_closed UP_cring.ctrm_is_poly UP_cring.to_poly_inverse UP_zero_closed X_closed deg_nzero_nzero is_UP_cring to_fun_ctrm to_fun_zero)
  show ?thesis
    unfolding taylor_expansion_def 0
    using assms UP_cring.X_sub is_UP_cring by blast
qed
end
(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Partitioning Semialgebraic Sets By Zero Sets of Function\<close>
(**************************************************************************************************)
(**************************************************************************************************)

context padic_fields
begin

definition SA_funs_to_SA_decomp where
"SA_funs_to_SA_decomp n Fs S = atoms_of ((\<inter>) S ` ((SA_zero_set n ` Fs) \<union> (SA_nonzero_set n ` Fs))) "

lemma SA_funs_to_SA_decomp_closed_0:
  assumes "Fs \<subseteq> carrier (SA n)"
  assumes "is_semialgebraic n S"
  shows "(\<inter>) S ` ((SA_zero_set n ` Fs) \<union> (SA_nonzero_set n ` Fs)) \<subseteq> semialg_sets n"
proof(rule subsetI)
  fix x assume A: "x \<in> (\<inter>) S ` (SA_zero_set n ` Fs \<union> SA_nonzero_set n ` Fs)"
  show " x \<in> semialg_sets n"
  proof(cases "x \<in> (\<inter>) S ` SA_zero_set n ` Fs")
    case True
    then obtain f where f_def: "f \<in> Fs \<and> x = S \<inter> SA_zero_set n f"
      by blast
    then show "x \<in> semialg_sets n" using assms SA_zero_set_is_semialgebraic
      by (meson is_semialgebraicE semialg_intersect subset_iff)
  next
    case False
    then have "x \<in> (\<inter>) S ` SA_nonzero_set n ` Fs"
      using A by blast
    then obtain f where f_def: "f \<in> Fs \<and> x = S \<inter> SA_nonzero_set n f"
      using A by blast
    then show "x \<in> semialg_sets n" using assms SA_nonzero_set_is_semialgebraic
      by (meson padic_fields.is_semialgebraicE padic_fields.semialg_intersect padic_fields_axioms subset_iff)
  qed
qed

lemma SA_funs_to_SA_decomp_closed:
  assumes "finite Fs"
  assumes "Fs \<subseteq> carrier (SA n)"
  assumes "is_semialgebraic n S"
  shows "SA_funs_to_SA_decomp n Fs S \<subseteq> semialg_sets n"
  unfolding SA_funs_to_SA_decomp_def semialg_sets_def
  apply(rule atoms_of_gen_boolean_algebra)
  using SA_funs_to_SA_decomp_closed_0[of Fs n S]  assms  unfolding semialg_sets_def
   apply blast
  using assms
  by blast

lemma SA_funs_to_SA_decomp_finite:
  assumes "finite Fs"
  assumes "Fs \<subseteq> carrier (SA n)"
  assumes "is_semialgebraic n S"
  shows "finite (SA_funs_to_SA_decomp n Fs S)"
  unfolding SA_funs_to_SA_decomp_def
  apply(rule finite_set_imp_finite_atoms)
  using assms by blast

lemma SA_funs_to_SA_decomp_disjoint:
  assumes "finite Fs"
  assumes "Fs \<subseteq> carrier (SA n)"
  assumes "is_semialgebraic n S"
  shows "disjoint (SA_funs_to_SA_decomp n Fs S)"
  apply(rule disjointI) unfolding SA_funs_to_SA_decomp_def
  apply(rule atoms_of_disjoint[of _ " ((\<inter>) S ` (SA_zero_set n ` Fs \<union> SA_nonzero_set n ` Fs))"])
    apply blast apply blast by blast

lemma pre_SA_funs_to_SA_decomp_in_algebra:
  shows " ((\<inter>) S ` (SA_zero_set n ` Fs \<union> SA_nonzero_set n ` Fs)) \<subseteq> gen_boolean_algebra S (SA_zero_set n ` Fs \<union> SA_nonzero_set n ` Fs)"
proof(rule subsetI) fix x assume A: " x \<in>  (\<inter>) S ` (SA_zero_set n ` Fs \<union> SA_nonzero_set n ` Fs)"
  then obtain A where A_def: "A \<in> (SA_zero_set n ` Fs \<union> SA_nonzero_set n ` Fs) \<and> x = S \<inter> A"
    by blast
  then show "x \<in> gen_boolean_algebra S (SA_zero_set n ` Fs \<union> SA_nonzero_set n ` Fs)"
    using gen_boolean_algebra.generator[of A "SA_zero_set n ` Fs \<union> SA_nonzero_set n ` Fs" S]
    by (metis inf.commute)
qed

lemma SA_funs_to_SA_decomp_in_algebra:
  assumes "finite Fs"
  shows "SA_funs_to_SA_decomp n Fs S \<subseteq> gen_boolean_algebra S (SA_zero_set n ` Fs \<union> SA_nonzero_set n ` Fs)"
  unfolding SA_funs_to_SA_decomp_def  apply(rule atoms_of_gen_boolean_algebra)
  using pre_SA_funs_to_SA_decomp_in_algebra[of S n Fs] apply blast
  using assms by blast

lemma SA_funs_to_SA_decomp_subset:
  assumes "finite Fs"
  assumes "Fs \<subseteq> carrier (SA n)"
  assumes "is_semialgebraic n S"
  assumes "A \<in> SA_funs_to_SA_decomp n Fs S"
  shows "A \<subseteq> S"
proof-
  have "A \<in> gen_boolean_algebra S (SA_zero_set n ` Fs \<union> SA_nonzero_set n ` Fs)"
  using assms SA_funs_to_SA_decomp_in_algebra[of Fs n S]
        atoms_of_gen_boolean_algebra[of _  S "(SA_zero_set n ` Fs \<union> SA_nonzero_set n ` Fs)"]
  unfolding SA_funs_to_SA_decomp_def by blast
  then show ?thesis using gen_boolean_algebra_subset by blast
qed

lemma SA_funs_to_SA_decomp_memE:
  assumes "finite Fs"
  assumes "Fs \<subseteq> carrier (SA n)"
  assumes "is_semialgebraic n S"
  assumes "A \<in> (SA_funs_to_SA_decomp n Fs S)"
  assumes "f \<in> Fs"
  shows "A \<subseteq> SA_zero_set n f \<or> A \<subseteq> SA_nonzero_set n f"
proof(cases "A \<subseteq> S \<inter> SA_zero_set n f")
case True
  then show ?thesis
    by blast
next
  case False
  have 0: "S \<inter> SA_zero_set n f \<in> (\<inter>) S ` (SA_zero_set n ` Fs \<union> SA_nonzero_set n ` Fs)"
    using assms
    by blast
  then have 1: "A \<inter> (S \<inter> SA_zero_set n f) = {}"
    using False assms atoms_are_minimal[of A "((\<inter>) S ` (SA_zero_set n ` Fs \<union> SA_nonzero_set n ` Fs))" "S \<inter> SA_zero_set n f"]
    unfolding SA_funs_to_SA_decomp_def
    by blast
  have 2: "A \<subseteq> S"
    using assms SA_funs_to_SA_decomp_subset by blast
  then show ?thesis
    using 0 1 False zero_set_nonzero_set_covers_semialg_set[of n S] assms(3) by auto
qed

lemma SA_funs_to_SA_decomp_covers:
  assumes "finite Fs"
  assumes "Fs \<noteq> {}"
  assumes "Fs \<subseteq> carrier (SA n)"
  assumes "is_semialgebraic n S"
  shows "S = \<Union> (SA_funs_to_SA_decomp n Fs S)"
proof-
  have 0: "S = \<Union> ((\<inter>) S ` ((SA_zero_set n ` Fs) \<union> (SA_nonzero_set n ` Fs)))"
  proof
    obtain f where f_def: "f \<in> Fs"
      using assms by blast
    have 0: "S \<inter> SA_nonzero_set n f \<in> ((\<inter>) S ` ((SA_zero_set n ` Fs) \<union> (SA_nonzero_set n ` Fs)))"
      using f_def by blast
    have 1: "S \<inter> SA_zero_set n f \<in> ((\<inter>) S ` ((SA_zero_set n ` Fs) \<union> (SA_nonzero_set n ` Fs)))"
      using f_def by blast
    have 2: "S = S \<inter> SA_zero_set n f \<union> S \<inter> SA_nonzero_set n f"
      by (simp add: assms(4) zero_set_nonzero_set_covers_semialg_set)
    then show "S \<subseteq> \<Union> ((\<inter>) S ` (SA_zero_set n ` Fs \<union> SA_nonzero_set n ` Fs))"
      using 0 1 Sup_upper2 Un_subset_iff subset_refl by blast
    show "\<Union> ((\<inter>) S ` (SA_zero_set n ` Fs \<union> SA_nonzero_set n ` Fs)) \<subseteq> S"
      by blast
  qed
  show ?thesis
    unfolding SA_funs_to_SA_decomp_def atoms_of_covers' using 0 by blast
qed

end
end

