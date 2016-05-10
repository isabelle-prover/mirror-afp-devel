(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Abstract Multivariate Polynomials\<close>

theory Abstract_Poly
imports Power_Products
begin

text \<open>This theory introduces abstract multivariate polynomials, represented as functions from some
  abstract power-product type to some type of sort @{class zero}. These (coefficient-) functions
  must have finite support, of course.
  The representing function maps a polynomial @{term p} and a power-product @{term s} to the
  coefficient of @{term s} in @{term p}; only finitely of these may be non-zero.\<close>

subsection \<open>General Properties of Polynomials\<close>

text \<open>Polynomials are represented as functions from power-products to coefficients with finite
  support.\<close>

typedef (overloaded) ('a, 'b) mpoly = "{f :: 'a \<Rightarrow> 'b::zero. finite {t. f t \<noteq> 0}}"
  morphisms coeff Abs_poly
proof
  show "(\<lambda>x. 0) \<in> {f. finite {t. f t \<noteq> 0}}" by simp
qed

setup_lifting type_definition_mpoly

lift_definition supp::"('a, 'b::zero) mpoly \<Rightarrow> 'a set" is "\<lambda>p. {t. p t \<noteq> 0}" .

text \<open>Monomials are not needed for Gr\"obner bases, but only for proving that @{typ "('a, 'b) mpoly"}
  forms a ring.\<close>

lift_definition monom::"'b::zero \<Rightarrow> 'a \<Rightarrow> ('a, 'b) mpoly" is "\<lambda>c s. (\<lambda>t. (if t = s then c else 0))"
proof -
  fix c::'b and s::"'a"
  show "finite {t. (if t = s then c else 0) \<noteq> 0}" by simp
qed

lemma supp_finite:
  shows "finite (supp p)"
by (transfer, assumption)

lemma in_supp:
  shows "(t \<in> supp p) \<longleftrightarrow> (coeff p t \<noteq> 0)"
by (transfer, simp)

lemma mpoly_ext:
  fixes p q::"('a, 'b::zero) mpoly"
  assumes "\<And>t. coeff p t = coeff q t"
  shows "p = q"
using assms by (transfer, auto)

lemma coeff_monom:
  fixes c::"'b::zero" and s t::"'a"
  shows "coeff (monom c s) t = (if t = s then c else 0)"
by (transfer, simp)

lemma supp_monom:
  fixes c::"'b::zero" and t::"'a"
  assumes "c \<noteq> 0"
  shows "supp (monom c t) = {t}"
using assms by (transfer, auto)

subsubsection \<open>@{typ "('a, 'b) mpoly"} forms an additive Abelian group\<close>

instantiation mpoly :: (type, "{equal, zero}") equal
begin
definition equal_mpoly::"('a, 'b) mpoly \<Rightarrow> ('a, 'b) mpoly \<Rightarrow> bool" where
  "equal_mpoly p q \<equiv> (\<forall>t. coeff p t = coeff q t)"

instance by (standard, simp only: equal_mpoly_def, transfer, auto)
end

instantiation mpoly :: (type, zero) zero
begin
lift_definition zero_mpoly::"('a, 'b) mpoly" is "\<lambda>_. 0::'b" by simp

lemma supp_0:
  fixes p::"('a, 'b) mpoly"
  shows "(supp p = {}) \<longleftrightarrow> (p = 0)"
proof transfer
  fix p::"'a \<Rightarrow> 'b"
  show "({t. p t \<noteq> 0} = {}) = (p = (\<lambda>_. 0))"
  proof
    assume "{t. p t \<noteq> 0} = {}"
    thus "p = (\<lambda>_. 0)" by auto
  next
    assume "p = (\<lambda>_. 0)"
    thus "{t. p t \<noteq> 0} = {}" by simp
  qed
qed

lemma monom_0I:
  fixes c::"'b::zero" and t::"'a"
  assumes "c = 0"
  shows "monom c t = 0"
using assms
proof transfer
  fix c::'b and t::"'a"
  assume "c = 0"
  show "(\<lambda>ta. if ta = t then c else 0) = (\<lambda>_. 0)" by (rule, simp add: \<open>c = 0\<close>)
qed

lemma monom_0D:
  fixes c::"'b::zero" and t::"'a"
  assumes "monom c t = 0"
  shows "c = 0"
using assms
proof transfer
  fix c::'b and t::"'a"
  assume "(\<lambda>s. if s = t then c else 0) = (\<lambda>_. 0)"
  from subst[OF this, of "\<lambda>f. f t = c"] have "0 = c" by simp
  thus "c = 0" by simp
qed

instance ..
end

instantiation mpoly :: (one, "{zero, one}") one
begin
definition one_mpoly::"('a, 'b) mpoly" where "one_mpoly \<equiv> monom 1 1"

lemma zero_not_one_mpoly:
  assumes "0 \<noteq> (1::'b)"
  shows "0 \<noteq> (1::('a, 'b) mpoly)"
unfolding one_mpoly_def
proof (transfer, rule)
  def f1 \<equiv> "\<lambda>_::'a. 0::'b"
  def f2 \<equiv> "\<lambda>t::'a. (if t = 1 then 1 else 0::'b)"
  assume "(\<lambda>_. 0::'b) = (\<lambda>t::'a. if t = 1 then 1 else 0)"
  hence "f1 = f2" unfolding f1_def f2_def by simp
  hence "f1 1 = f2 1" by simp
  hence "0 = (if 1 = (1::'a pp) then 1 else 0::'b)" unfolding f1_def f2_def by simp
  hence "0 = (1::'b)" by simp
  thus False using assms by simp
qed

instance ..
end

instantiation mpoly :: (type, comm_monoid_add) comm_monoid_add
begin

lift_definition plus_mpoly::"('a, 'b) mpoly \<Rightarrow> ('a, 'b) mpoly \<Rightarrow> ('a, 'b) mpoly" is
  "\<lambda>p q. (\<lambda>s. p s + q s)"
proof -
  fix fun1 fun2::"'a \<Rightarrow> 'b"
  assume "finite {t. fun1 t \<noteq> 0}" and "finite {t. fun2 t \<noteq> 0}"
  hence "finite ({t. fun1 t \<noteq> 0} \<union> {t. fun2 t \<noteq> 0})" by (intro finite_UnI)
  hence finite_union: "finite {t. (fun1 t \<noteq> 0) \<or> (fun2 t \<noteq> 0)}" by (simp only: Collect_disj_eq)
  have "{t. fun1 t + fun2 t \<noteq> 0} \<subseteq> {t. (fun1 t \<noteq> 0) \<or> (fun2 t \<noteq> 0)}"
  proof (intro Collect_mono, rule)
    fix t::'a
    assume sum_not_zero: "((fun1 t) + (fun2 t)) \<noteq> 0"
    have "fun1 t = 0 \<longrightarrow> fun2 t \<noteq> 0"
    proof
      assume "fun1 t = 0"
      thus "fun2 t \<noteq> 0" using sum_not_zero by simp
    qed
    thus "fun1 t \<noteq> 0 \<or> fun2 t \<noteq> 0" by auto
  qed
  from finite_subset[OF this] finite_union show "finite {t. fun1 t + fun2 t \<noteq> 0}" .
qed

lemma plus_mpoly_assoc:
  fixes a b c::"('a, 'b) mpoly"
  shows "(a + b) + c = a + (b + c)"
proof transfer
  fix a b c::"'a \<Rightarrow> 'b"
  show "(\<lambda>s. a s + b s + c s) = (\<lambda>s. a s + (b s + c s))" by (rule, simp add: ac_simps)
qed

lemma plus_mpoly_comm:
  fixes a b::"('a, 'b) mpoly"
  shows "a + b = b + a"
proof transfer
  fix a b::"'a \<Rightarrow> 'b"
  show "(\<lambda>s. a s + b s) = (\<lambda>s. b s + a s)" by (rule, simp add: ac_simps)
qed

lemma plus_mpoly_zero_neutral:
  fixes a::"('a, 'b) mpoly"
  shows "0 + a = a"
proof transfer
  fix a::"'a \<Rightarrow> 'b"
  show "(\<lambda>s. 0 + a s) = a" by (rule, simp)
qed

instance
apply standard
subgoal by (rule plus_mpoly_assoc)
subgoal by (rule plus_mpoly_comm)
subgoal by (rule plus_mpoly_zero_neutral)
done

end

instantiation mpoly :: (type, ab_group_add) ab_group_add
begin
lift_definition uminus_mpoly::"('a, 'b) mpoly \<Rightarrow> ('a, 'b) mpoly" is "\<lambda>p. (\<lambda>t. -(p t))" by simp

definition minus_mpoly::"('a, 'b) mpoly \<Rightarrow> ('a, 'b) mpoly \<Rightarrow> ('a, 'b) mpoly" where
  "minus_mpoly p q = p + (-q)"

lemma plus_mpoly_inv:
  fixes a b::"('a, 'b) mpoly"
  shows "-a + a = 0"
proof transfer
  fix a::"'a \<Rightarrow> 'b"
  show "(\<lambda>s. (- a s) + a s) = (\<lambda>_. 0)" by (rule, simp)
qed

instance
apply standard
subgoal by (rule plus_mpoly_inv)
subgoal by (simp add: minus_mpoly_def)
done

end

lemma coeff_0:
  fixes t::"'a"
  shows "coeff 0 t = 0"
by (transfer, simp)

lemma coeff_plus:
  fixes p q::"('a, 'b::comm_monoid_add) mpoly"
  shows "coeff (p + q) t = coeff p t + coeff q t"
by (transfer, simp)

lemma coeff_uminus:
  fixes p::"('a, 'b::ab_group_add) mpoly"
  shows "coeff (-p) t = - coeff p t"
by (transfer, simp)

lemma coeff_minus:
  fixes p q::"('a, 'b::ab_group_add) mpoly"
  shows "coeff (p - q) t = coeff p t - coeff q t"
using coeff_plus[of p "-q" t] coeff_uminus[of q t] unfolding minus_mpoly_def by simp

subsubsection \<open>Multiplication by Monomials\<close>

context powerprod
begin

lift_definition monom_mult::"'b::semiring_0 \<Rightarrow> 'a \<Rightarrow> ('a, 'b) mpoly \<Rightarrow> ('a, 'b) mpoly" is
  "\<lambda>c::'b. \<lambda>t p. (\<lambda>s. (if t dvd s then c * (p (s divide t)) else 0))"
proof -
  fix c::'b and t::'a and p::"'a \<Rightarrow> 'b"
  have "{s. (if t dvd s then c * p (s divide t) else 0) \<noteq> 0} \<subseteq> (\<lambda>x. t * x) ` {s. p s \<noteq> 0}"
    (is "?L \<subseteq> ?R")
  proof
    fix x::"'a"
    assume "x \<in> ?L"
    hence "(if t dvd x then c * p (x divide t) else 0) \<noteq> 0" by simp
    hence "t dvd x" and cp_not_zero: "c * p (x divide t) \<noteq> 0" by (simp_all split: split_if_asm)
    show "x \<in> ?R"
    proof
      from dvd_divide[OF \<open>t dvd x\<close>] show "x = t * (x divide t)" by (simp add: ac_simps)
    next
      from mult_not_zero[OF cp_not_zero] show "x divide t \<in> {t. p t \<noteq> 0}" by (rule, simp)
    qed
  qed
  assume "finite {t. p t \<noteq> 0}"
  hence "finite ?R" by (intro finite_imageI)
  from finite_subset[OF \<open>?L \<subseteq> ?R\<close> this]
    show "finite {s. (if t dvd s then c * p (s divide t) else 0) \<noteq> 0}" .
qed

lemma monom_mult_coeff:
  fixes c::"'b::semiring_0" and t s::"'a" and p::"('a, 'b) mpoly"
  shows "coeff (monom_mult c t p) (t * s) = c * coeff p s"
proof transfer
  fix c::"'b" and t s::"'a" and p::"'a \<Rightarrow> 'b"
  from dvd_triv_left[of t s] times_divide_2[of t s]
    show "(if t dvd t * s then c * p (t * s divide t) else 0) = c * p s" by simp
qed

lemma monom_mult_assoc:
  fixes c d::"'b::semiring_0" and s t::"'a" and p::"('a, 'b) mpoly"
  shows "monom_mult c s (monom_mult d t p) = monom_mult (c * d) (s * t) p"
proof transfer
  fix c d::"'b::semiring_0" and s t::"'a" and p::"'a \<Rightarrow> 'b"
  show "(\<lambda>x. if s dvd x then c * (if t dvd x divide s then d * p (x divide s divide t) else 0) else 0) =
          (\<lambda>x. if s * t dvd x then c * d * p (x divide (s * t)) else 0)"
  proof
    fix x
    from divide_divide[of x s t] times_dvd[of t s x] show
      "(if s dvd x then c * (if t dvd x divide s then d * p ((x divide s) divide t) else 0) else 0) =
         (if s * t dvd x then c * d * p (x divide (s * t)) else 0)" by (auto simp add: ac_simps)
  qed
qed

lemma monom_mult_uminus_left:
  fixes c::"'b::ring" and t::"'a" and p::"('a, 'b) mpoly"
  shows "monom_mult (-c) t p = -(monom_mult c t p)"
by (transfer, auto)

lemma monom_mult_uminus_right:
  fixes c::"'b::ring" and t::"'a" and p::"('a, 'b) mpoly"
  shows "monom_mult c t (-p) = -(monom_mult c t p)"
by (transfer, auto)

lemma uminus_monom_mult:
  fixes p::"('a, 'b::comm_ring_1) mpoly"
  shows "-p = monom_mult (-1) 1 p"
proof transfer
  fix p::"'a \<Rightarrow> 'b"
  show "(\<lambda>t. - p t) = (\<lambda>s. if 1 dvd s then - 1 * p (s divide 1) else 0)"
  proof
    fix t::"'a"
    show "- p t = (if 1 dvd t then - 1 * p (t divide 1) else 0)" by (simp add: divide_one)
  qed
qed

lemma monom_mult_dist_left:
  fixes c d::"'b::semiring_0" and t::"'a" and p::"('a, 'b) mpoly"
  shows "monom_mult (c + d) t p = (monom_mult c t p) + (monom_mult d t p)"
by (transfer, auto simp add: algebra_simps)

lemma monom_mult_dist_left_minus:
  fixes c d::"'b::ring" and t::"'a" and p::"('a, 'b) mpoly"
  shows "monom_mult (c - d) t p = (monom_mult c t p) - (monom_mult d t p)"
using monom_mult_dist_left[of c "-d" t p] monom_mult_uminus_left[of d t p] by simp

lemma monom_mult_dist_right:
  fixes c::"'b::semiring_0" and t::"'a" and p q::"('a, 'b) mpoly"
  shows "monom_mult c t (p + q) = (monom_mult c t p) + (monom_mult c t q)"
by (transfer, auto simp add: algebra_simps)

lemma monom_mult_dist_right_minus:
  fixes c::"'b::ring" and t::"'a" and p q::"('a, 'b) mpoly"
  shows "monom_mult c t (p - q) = (monom_mult c t p) - (monom_mult c t q)"
using monom_mult_dist_right[of c t p "-q"] monom_mult_uminus_right[of c t q]
unfolding minus_mpoly_def by simp

lemma monom_mult_left0:
  fixes t::"'a" and p::"('a, 'b::semiring_0) mpoly"
  shows "monom_mult 0 t p = 0"
by (transfer, auto)

lemma monom_mult_right0:
  fixes c::"'b::semiring_0" and t::"'a"
  shows "monom_mult c t 0 = 0"
by (transfer, auto)

lemma monom_mult_left1:
  fixes p::"('a, 'b::semiring_1) mpoly"
  shows "(monom_mult 1 1 p) = p"
proof (transfer, rule)
  fix p::"'a \<Rightarrow> 'b" and s::"'a"
  from divide_one[of s] show "(if 1 dvd s then 1 * p (s divide 1) else 0) = p s" by simp
qed

lemma monom_mult_monom:
  fixes c d::"'b::comm_semiring_0" and s t::"'a"
  shows "monom_mult c s (monom d t) = monom_mult d t (monom c s)"
proof (transfer, rule)
  fix c::'b and s::"'a" and d t u
  show "(if s dvd u then c * (if u divide s = t then d else 0) else 0) =
        (if t dvd u then d * (if u divide t = s then c else 0) else 0)"
  proof (simp, intro conjI, intro impI)
    assume ust: "u divide s = t"
    show "(u divide t = s \<longrightarrow> (s dvd u \<longrightarrow> (t dvd u \<longrightarrow> c * d = d * c) \<and>
          (\<not> t dvd u \<longrightarrow> c * d = 0)) \<and> (\<not> s dvd u \<longrightarrow> t dvd u \<longrightarrow> d * c = 0)) \<and>
          (u divide t \<noteq> s \<longrightarrow> s dvd u \<longrightarrow> c * d = 0)"
    proof (intro conjI, intro impI)
      assume uts: "u divide t = s"
      show "(s dvd u \<longrightarrow> (t dvd u \<longrightarrow> c * d = d * c) \<and> (\<not> t dvd u \<longrightarrow> c * d = 0)) \<and>
            (\<not> s dvd u \<longrightarrow> t dvd u \<longrightarrow> d * c = 0)"
      proof (intro conjI, intro impI)
        assume "s dvd u"
        show "(t dvd u \<longrightarrow> c * d = d * c) \<and> (\<not> t dvd u \<longrightarrow> c * d = 0)"
        proof (intro conjI, intro impI)
          show "c * d = d * c" by (simp add: ac_simps)
        next
          show "\<not> t dvd u \<longrightarrow> c * d = 0"
          proof (intro impI)
            assume "\<not> t dvd u"
            from dvd_divide[OF \<open>s dvd u\<close>] ust have "u = t * s" by simp
            hence "t dvd u" by simp
            from this \<open>\<not> t dvd u\<close> show "c * d = 0" by simp
          qed
        qed
      next
        show "\<not> s dvd u \<longrightarrow> t dvd u \<longrightarrow> d * c = 0"
        proof (intro impI)
          assume "\<not> s dvd u" and "t dvd u"
          from dvd_divide[OF \<open>t dvd u\<close>] uts have "u = s * t" by simp
          hence "s dvd u" by simp
          from this \<open>\<not> s dvd u\<close> show "d * c = 0" by simp
        qed
      qed
    next
      show "u divide t \<noteq> s \<longrightarrow> s dvd u \<longrightarrow> c * d = 0"
      proof (intro impI)
        assume "u divide t \<noteq> s" and "s dvd u"
        from dvd_divide[OF \<open>s dvd u\<close>] ust have "u = t * s" by simp
        from this times_divide_2[of t s] have "u divide t = s" by simp
        from this \<open>u divide t \<noteq> s\<close> show "c * d = 0" by simp
      qed
    qed
  next
    show "u divide s \<noteq> t \<longrightarrow> u divide t = s \<longrightarrow> t dvd u \<longrightarrow> d * c = 0"
    proof (intro impI)
      assume "u divide s \<noteq> t" and "u divide t = s" and "t dvd u"
      from dvd_divide[OF \<open>t dvd u\<close>] \<open>u divide t = s\<close> have "u = s * t" by simp
      from this times_divide_2[of s t] have "u divide s = t" by simp
      from this \<open>u divide s \<noteq> t\<close> show "d * c = 0" by simp
    qed
  qed
qed

subsubsection \<open>Polynomial Ideals\<close>

text \<open>According to the definition of @{term pideal}, @{term pideal} must be closed only under
  multiplication by monomials. After introducing general multiplication @{term pideal} is shown to
  be closed under multiplication by arbitrary polynomials as well (in lemma
  @{text pideal_closed_times}), making it really an ideal.\<close>

inductive_set pideal::"('a, 'b::semiring_0) mpoly set \<Rightarrow> ('a, 'b) mpoly set"
for bs::"('a, 'b) mpoly set" where
  pideal_0: "0 \<in> (pideal bs)"|
  pideal_plus: "a \<in> (pideal bs) \<Longrightarrow> b \<in> bs \<Longrightarrow> a + monom_mult c t b \<in> (pideal bs)"

lemma monom_mult_in_pideal:
  fixes bs::"('a, 'b::semiring_0) mpoly set"
  assumes "b \<in> bs"
  shows "monom_mult c t b \<in> pideal bs"
proof -
  have "0 + monom_mult c t b \<in> pideal bs" by (rule pideal_plus, rule pideal_0, fact)
  thus ?thesis by simp
qed

lemma generator_subset_pideal:
  fixes bs::"('a, 'b::semiring_1) mpoly set"
  shows "bs \<subseteq> pideal bs"
proof
  fix b
  assume b_in: "b \<in> bs"
  from monom_mult_left1[of b] monom_mult_in_pideal[OF b_in, of 1 1] show "b \<in> pideal bs" by simp
qed

lemma pideal_closed_plus:
  fixes bs::"('a, 'b::semiring_0) mpoly set"
  assumes p_in: "p \<in> pideal bs" and q_in: "q \<in> pideal bs"
  shows "p + q \<in> pideal bs"
using p_in
proof (induct p)
  from q_in show "0 + q \<in> pideal bs" by simp
next
  fix a b c t
  assume a_in: "a \<in> pideal bs" and IH: "a + q \<in> pideal bs" and b_in: "b \<in> bs"
  have "(a + q) + monom_mult c t b \<in> pideal bs" by (rule pideal_plus, fact+)
  thus "(a + monom_mult c t b) + q \<in> pideal bs"
    by (simp only: plus_mpoly_comm[of "monom_mult c t b" q] plus_mpoly_assoc)
qed

lemma pideal_closed_uminus:
  fixes bs::"('a, 'b::comm_ring) mpoly set"
  assumes p_in: "p \<in> pideal bs"
  shows "-p \<in> pideal bs"
using p_in
proof (induct p)
  show "-0 \<in> pideal bs" by (simp, rule pideal_0)
next
  fix a b c t
  assume IH: "-a \<in> pideal bs" and b_in: "b \<in> bs"
  have eq: "- (a + monom_mult c t b) = (-a) + (- (monom_mult c t b))" by simp
  from monom_mult_in_pideal[OF b_in, of "-c" t] monom_mult_uminus_left[of c t b]
    have "- (monom_mult c t b) \<in> pideal bs" by simp
  thus "- (a + monom_mult c t b) \<in> pideal bs" unfolding eq by (rule pideal_closed_plus[OF IH])
qed

lemma pideal_closed_minus:
  fixes bs::"('a, 'b::comm_ring) mpoly set"
  assumes "p \<in> pideal bs" and "q \<in> pideal bs"
  shows "p - q \<in> pideal bs"
unfolding minus_mpoly_def by (rule pideal_closed_plus, fact, rule pideal_closed_uminus, fact)

lemma pideal_closed_monom_mult:
  fixes bs::"('a, 'b::comm_ring) mpoly set"
  assumes "p \<in> pideal bs"
  shows "monom_mult c t p \<in> pideal bs"
using assms
proof (induct p)
  show "monom_mult c t 0 \<in> pideal bs" unfolding monom_mult_right0[of c t] by (rule pideal_0)
next
  fix a b d s
  assume "a \<in> pideal bs" and "monom_mult c t a \<in> pideal bs" and "b \<in> bs"
  show "monom_mult c t (a + monom_mult d s b) \<in> pideal bs"
    unfolding monom_mult_dist_right[of c t a "monom_mult d s b"]
  proof (rule pideal_closed_plus, fact)
    from monom_mult_assoc[of c t d s b] monom_mult_in_pideal[OF \<open>b \<in> bs\<close>]
      show "monom_mult c t (monom_mult d s b) \<in> pideal bs" by simp
  qed
qed

lemma pideal_in_insertI:
  fixes bs::"('a, 'b::comm_ring) mpoly set"
  assumes "p \<in> pideal bs"
  shows "p \<in> pideal (insert q bs)"
using assms
proof (induct p)
  show "0 \<in> pideal (insert q bs)" ..
next
  fix a b c t
  assume "a \<in> pideal (insert q bs)" and b_in: "b \<in> bs"
  show "a + monom_mult c t b \<in> pideal (insert q bs)" proof (rule, fact)
    from b_in show "b \<in> insert q bs" by simp
  qed
qed

lemma pideal_in_insertD:
  fixes bs::"('a, 'b::comm_ring) mpoly set"
  assumes p_in: "p \<in> pideal (insert q bs)" and q_in: "q \<in> pideal bs"
  shows "p \<in> pideal bs"
using p_in
proof (induct p)
  show "0 \<in> pideal bs" ..
next
  fix a b c t
  assume a_in: "a \<in> pideal bs" and b_in: "b \<in> insert q bs"
  from b_in have "b = q \<or> b \<in> bs" by simp
  thus "a + monom_mult c t b \<in> pideal bs"
  proof
    assume eq: "b = q"
    show ?thesis unfolding eq by (rule pideal_closed_plus, fact, rule pideal_closed_monom_mult, fact)
  next
    assume "b \<in> bs"
    show ?thesis by (rule, fact+)
  qed
qed

lemma pideal_insert:
  fixes bs::"('a, 'b::comm_ring) mpoly set"
  assumes "q \<in> pideal bs"
  shows "pideal (insert q bs) = pideal bs"
proof (rule, rule)
  fix p
  assume "p \<in> pideal (insert q bs)"
  from pideal_in_insertD[OF this assms] show "p \<in> pideal bs" .
next
  show "pideal bs \<subseteq> pideal (insert q bs)"
  proof
    fix p
    assume "p \<in> pideal bs"
    from pideal_in_insertI[OF this] show "p \<in> pideal (insert q bs)" .
  qed
qed

end (* powerprod *)

subsection \<open>Multiplication\<close>

lift_definition except::"('a, 'b::zero) mpoly \<Rightarrow> 'a \<Rightarrow> ('a, 'b) mpoly"
  is "\<lambda>p s. (\<lambda>t. (if t = s then 0 else p t))"
proof transfer
  fix p::"'a \<Rightarrow> 'b" and s::'a
  assume "finite {t. p t \<noteq> 0}"
  show "finite {t. (if t = s then 0 else p t) \<noteq> 0}"
  proof (rule finite_subset[of _ "{t. p t \<noteq> 0}"], rule)
    fix u
    assume "u \<in> {t. (if t = s then 0 else p t) \<noteq> 0}"
    hence "(if u = s then 0 else p u) \<noteq> 0" by simp
    hence "p u \<noteq> 0" by metis
    thus "u \<in> {t. p t \<noteq> 0}" by simp
  qed (fact)
qed

lemma coeff_except1:
  shows "coeff (except p t) t = 0"
by (transfer, simp)

lemma coeff_except2:
  assumes "s \<noteq> t"
  shows "coeff (except p t) s = coeff p s"
using assms by (transfer, simp)

text \<open>@{term "some_term p"} shall only return @{emph \<open>some\<close>} term appearing in @{term p} with
  non-zero coefficient (not necessarily the biggest one w.r.t. a certain ordering). However, if we
  use something like @{term "SOME t. t \<in> supp p"} instead, multiplication cannot be made executable.\<close>

definition some_term::"('a::{powerprod, linorder}, 'b::zero) mpoly \<Rightarrow> 'a"
  where "some_term p \<equiv> (if p = 0 then 1 else Max (supp p))"
definition rest_mpoly::"('a::{powerprod, linorder}, 'b::zero) mpoly \<Rightarrow> ('a, 'b) mpoly"
  where "rest_mpoly p \<equiv> except p (some_term p)"

lemma some_term_nonzero:
  assumes "p \<noteq> 0"
  shows "some_term p \<in> supp p"
proof -
  from supp_0[of p] assms have "supp p \<noteq> {}" by simp
  from Max_in[OF supp_finite[of p] this] assms show ?thesis unfolding some_term_def by simp
qed

lemma coeff_some_term:
  assumes "p \<noteq> 0"
  shows "coeff p (some_term p) \<noteq> 0"
using some_term_nonzero[OF assms] unfolding in_supp .

lemma coeff_rest_some_term:
  "coeff (rest_mpoly p) (some_term p) = 0"
unfolding rest_mpoly_def some_term_def
by (transfer, simp)

lemma coeff_rest:
  assumes "t \<noteq> some_term p"
  shows "coeff (rest_mpoly p) t = coeff p t"
using assms unfolding rest_mpoly_def some_term_def by (transfer, simp)

lemma rest_zero:
  "rest_mpoly 0 = 0"
unfolding rest_mpoly_def some_term_def by (transfer, simp)

lemma supp_rest:
  shows "supp (rest_mpoly p) = (supp p) - {some_term p}"
proof
  show "supp (rest_mpoly p) \<subseteq> supp p - {some_term p}"
  proof (rule)
    fix x
    assume "x \<in> supp (rest_mpoly p)"
    from this in_supp[of x "rest_mpoly p"] have cr: "coeff (rest_mpoly p) x \<noteq> 0" by simp
    from this coeff_rest_some_term have "x \<noteq> some_term p" by auto
    from cr coeff_rest[OF this] have "coeff p x \<noteq> 0" by simp
    show "x \<in> supp p - {some_term p}"
    proof
      from \<open>coeff p x \<noteq> 0\<close> in_supp[of x p] show "x \<in> supp p" by simp
    next
      from \<open>x \<noteq> some_term p\<close> show "x \<notin> {some_term p}" by simp
    qed
  qed
next
  show "supp p - {some_term p} \<subseteq> supp (rest_mpoly p)"
  proof (rule)
    fix x
    assume "x \<in> supp p - {some_term p}"
    hence x1: "x \<in> supp p" and x2: "x \<notin> {some_term p}" by simp_all
    from x1 in_supp[of x p] have cp: "coeff p x \<noteq> 0" by simp
    moreover from x2 have "x \<noteq> some_term p" by simp
    from coeff_rest[OF this] in_supp[of x "rest_mpoly p"] cp show "x \<in> supp (rest_mpoly p)" by simp
  qed
qed

lemma supp_rest_insert:
  assumes "p \<noteq> 0"
  shows "supp p = insert (some_term p) (supp (rest_mpoly p))"
by (simp add: supp_rest insert_absorb[OF some_term_nonzero[OF assms]])
  
lemma supp_rest_subset:
  assumes "p \<noteq> 0"
  shows "supp (rest_mpoly p) \<subset> supp p"
proof (simp only: supp_rest, rule, rule Diff_subset, rule)
  assume "supp p - {some_term p} = supp p"
  hence "supp p \<subseteq> supp p - {some_term p}" by simp
  hence "\<And>t. t \<in> supp p \<Longrightarrow> t \<in> (supp p - {some_term p})" by auto
  from this[OF some_term_nonzero[OF assms]] have "some_term p \<notin> {some_term p}" by simp
  thus False by simp
qed

lemma supp_subset_wf:
  "wfP (\<lambda>p q::('a, 'b::zero) mpoly. supp p \<subset> supp q)"
unfolding wfP_def
proof (intro wfI_min)
  fix x::"('a, 'b) mpoly" and Q
  assume x_in: "x \<in> Q"
  let ?Q0 = "card ` supp ` Q"
  from x_in have "card (supp x) \<in> ?Q0" by simp
  from wfE_min[OF wf this] obtain z0
    where z0_in: "z0 \<in> ?Q0" and z0_min: "\<And>y. (y, z0) \<in> {(x, y). x < y} \<Longrightarrow> y \<notin> ?Q0" by auto
  from z0_in obtain z where z0_def: "z0 = card (supp z)" and "z \<in> Q" by auto
  show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> {(p, q). supp p \<subset> supp q} \<longrightarrow> y \<notin> Q"
  proof (intro bexI[of _ z], rule, rule)
    fix y::"('a, 'b) mpoly"
    let ?y0 = "card (supp y)"
    assume "(y, z) \<in> {(p, q). supp p \<subset> supp q}"
    hence "supp y \<subset> supp z" by simp
    hence "?y0 < z0" unfolding z0_def by (simp add: supp_finite psubset_card_mono) 
    hence "(?y0, z0) \<in> {(x, y). x < y}" by simp
    from z0_min[OF this] show "y \<notin> Q" by auto
  qed (fact)
qed

lemma mpoly_supp_induct:
  assumes base: "P 0" and ind: "\<And>p. p \<noteq> 0 \<Longrightarrow> P (rest_mpoly p) \<Longrightarrow> P p"
  shows "P p"
proof (induct rule: wfP_induct[OF supp_subset_wf])
  fix p::"('a, 'b) mpoly"
  assume IH: "\<forall>q. supp q \<subset> supp p \<longrightarrow> P q"
  show "P p"
  proof (cases "p = 0")
    case True
    thus ?thesis using base by simp
  next
    case False
    show ?thesis
    proof (rule ind, fact)
      from IH[rule_format, OF supp_rest_subset[OF False]] show "P (rest_mpoly p)" .
    qed
  qed
qed

lemma some_term_monom:
  assumes "c \<noteq> (0::'b::zero)"
  shows "some_term (monom c t) = t"
proof -
  from assms monom_0D[of c t] have nz: "monom c t \<noteq> 0" by auto
  from nz supp_monom[OF assms, of t] show ?thesis unfolding some_term_def by simp
qed

lemma coeff_some_term_monom:
  assumes "c \<noteq> (0::'b::zero)"
  shows "coeff (monom c t) (some_term (monom c t)) = c"
by (simp add: some_term_monom[OF assms] coeff_monom[of c t])

lemma rest_monom:
  shows "rest_mpoly (monom c t) = (0::('a::{powerprod, linorder}, 'b::zero) mpoly)"
proof (cases "c = 0")
  case True
  from monom_0I[OF this, of t] rest_zero show ?thesis by simp
next
  case False
  show ?thesis
  proof (intro mpoly_ext, simp only: coeff_0)
    fix s
    show "coeff (rest_mpoly (monom c t)) s = 0"
    proof (cases "s = t")
      assume "s = t"
      from this some_term_monom[OF False, of t] have "some_term (monom c t) = s" by simp
      from this coeff_rest_some_term[of "monom c t"] show ?thesis by simp
    next
      assume "s \<noteq> t"
      from this some_term_monom[OF False, of t] have "s \<noteq> some_term (monom c t)" by simp
      from \<open>s \<noteq> t\<close> coeff_monom[of c t s] coeff_rest[OF this] show ?thesis by simp
    qed
  qed
qed

lemma some_monomial_rest:
  fixes p::"('a::{powerprod, linorder}, 'b::comm_monoid_add) mpoly"
  assumes "p \<noteq> 0"
  shows "p = monom (coeff p (some_term p)) (some_term p) + rest_mpoly p"
proof (rule mpoly_ext)
  fix t
  have "coeff p t = coeff (monom (coeff p (some_term p)) (some_term p)) t + coeff (rest_mpoly p) t"
  proof (cases "t = (some_term p)")
    case True
    hence c1: "coeff (rest_mpoly p) t = 0" by (simp only: coeff_rest_some_term)
    from True have c2: "coeff (monom (coeff p (some_term p)) (some_term p)) t = coeff p (some_term p)"
      unfolding coeff_monom by simp
    from True c1 c2 show ?thesis by simp
  next
    case False
    hence c1: "coeff (rest_mpoly p) t = coeff p t" by (simp add: coeff_rest)
    from False have c2: "coeff (monom (coeff p (some_term p)) (some_term p)) t = 0"
      unfolding coeff_monom by simp
    from c1 c2 show ?thesis by simp
  qed
  thus "coeff p t = coeff (monom (coeff p (some_term p)) (some_term p) + rest_mpoly p) t"
    by (simp add: coeff_plus)
qed

instantiation mpoly :: ("{powerprod, linorder}", comm_semiring_0) comm_semiring_0
begin

function times_mpoly::"('a, 'b) mpoly \<Rightarrow> ('a, 'b) mpoly \<Rightarrow> ('a, 'b) mpoly" where
  "times_mpoly p q =
    (if p = 0 then
      0
    else
      monom_mult (coeff p (some_term p)) (some_term p) q + times_mpoly (rest_mpoly p) q
    )"
by auto
termination proof -
  let ?r = "{(x, y::('a, 'b) mpoly). supp x \<subset> supp y} <*lex*> {}"
  show ?thesis
  proof
    show "wf ?r"
    proof
      from supp_subset_wf show "wf {(x, y::('a, 'b) mpoly). supp x \<subset> supp y}" unfolding wfP_def .
    qed (simp)
  next
    fix p q::"('a, 'b) mpoly"
    assume "p \<noteq> 0"
    from supp_rest_subset[OF this] show "((rest_mpoly p, q), (p, q)) \<in> ?r" by simp
  qed
qed

lemma times_mpoly_induct:
  assumes base: "P 0 q 0"
  assumes ind: "\<And>p. p \<noteq> 0 \<Longrightarrow> P (rest_mpoly p) q ((rest_mpoly p) * q) \<Longrightarrow>
                  P p q (monom_mult (coeff p (some_term p)) (some_term p) q + (rest_mpoly p) * q)"
  shows "P p q (p * q)"
proof (rule times_mpoly.induct[of "\<lambda>x _. P x q (x * q)"])
  fix p qa
  assume IH: "p \<noteq> 0 \<Longrightarrow> P (rest_mpoly p) q (rest_mpoly p * q)"
  show "P p q (p * q)"
  proof (cases "p = 0")
    case True
    from True base show ?thesis by simp
  next
    case False
    have "P p q (monom_mult (coeff p (some_term p)) (some_term p) q + (rest_mpoly p) * q)"
      by (rule ind, fact, rule IH, fact)
    thus ?thesis using False by simp
  qed
qed

lemma times_mpoly_left0:
  fixes p::"('a, 'b) mpoly"
  shows "0 * p = 0"
by simp

lemma times_mpoly_right0:
  fixes p::"('a, 'b) mpoly"
  shows "p * 0 = 0"
proof (induct rule: times_mpoly_induct)
  fix p
  assume "rest_mpoly p * 0 = 0"
  thus "monom_mult (coeff p (some_term p)) (some_term p) 0 + rest_mpoly p * 0 = 0"
    using monom_mult_right0 by simp
qed (simp)

lemma times_mpoly_left_monom:
  shows "(monom c t) * p = monom_mult c t p"
proof (cases "c = 0")
  case True
  from True monom_0I[OF this, of t] times_mpoly_left0[of p] monom_mult_left0[of t p]
    show ?thesis by simp
next
  case False
  have "monom c t \<noteq> 0"
  proof
    assume "monom c t = 0"
    from False monom_0D[OF this] show False ..
  qed
  from this some_term_monom[OF False, of t] coeff_some_term_monom[OF False, of t] rest_monom[of c t]
    show ?thesis by simp
qed

lemma times_mpoly_right_monom:
  shows "p * (monom c t) = monom_mult c t p"
proof (induct rule: times_mpoly_induct[of _ "monom c t" p])
  from monom_mult_right0 show "0 = monom_mult c t 0" by simp
next
  fix p
  assume "p \<noteq> 0" and IH: "rest_mpoly p * monom c t = monom_mult c t (rest_mpoly p)"
  from monom_mult_monom[of "coeff p (some_term p)" "some_term p"] IH some_monomial_rest[OF \<open>p \<noteq> 0\<close>]
    monom_mult_dist_right[of c t "monom (coeff p (some_term p)) (some_term p)" "rest_mpoly p"]
  show "monom_mult (coeff p (some_term p)) (some_term p) (monom c t) + rest_mpoly p * monom c t =
        monom_mult c t p" by simp
qed

lemma times_mpoly_dist_left:
  fixes p q r::"('a, 'b) mpoly"
  shows "p * (q + r) = p * q + p * r"
proof (rule times_mpoly_induct[of "\<lambda>x _ _. x * (q + r) = x * q + x * r"])
  from times_mpoly_left0 show "0 * (q + r) = 0 * q + 0 * r" by simp
next
  fix p
  assume "p \<noteq> 0" and IH: "rest_mpoly p * (q + r) = rest_mpoly p * q + rest_mpoly p * r"
  let ?c = "coeff p (some_term p)"
  let ?t = "some_term p"
  from \<open>p \<noteq> 0\<close> have "p * (q + r) = (monom_mult ?c ?t (q + r)) + (rest_mpoly p) * (q + r)" by simp
  also have "\<dots> = (monom_mult ?c ?t q) + (monom_mult ?c ?t r) + (rest_mpoly p) * (q + r)"
    using monom_mult_dist_right[of ?c ?t q r] by simp
  also have "\<dots> = ((monom_mult ?c ?t q) + (monom_mult ?c ?t r)) + ((rest_mpoly p) * q + (rest_mpoly p) * r)"
    using IH by simp
  also have "\<dots> = ((monom_mult ?c ?t q) + (rest_mpoly p) * q) + ((monom_mult ?c ?t r) + (rest_mpoly p) * r)"
    by (simp only: ac_simps)
  also have "\<dots> = p * q + p * r" using \<open>p \<noteq> 0\<close> times_mpoly.simps[of p] by simp
  finally show "p * (q + r) = p * q + p * r" .
qed

lemma times_mpoly_dist_right:
  fixes p q r::"('a, 'b) mpoly"
  shows "(p + q) * r = p * r + q * r"
proof (induct rule: times_mpoly_induct[of _ "p + q" r])
  from times_mpoly_right0 show "(p + q) * 0 = p * 0 + q * 0" by simp
next
  fix r
  assume "r \<noteq> 0" and IH: "(p + q) * (rest_mpoly r) = p * rest_mpoly r + q * rest_mpoly r"
  let ?c = "coeff r (some_term r)"
  let ?t = "some_term r"
  let ?r = "rest_mpoly r"
  from some_monomial_rest[OF \<open>r \<noteq> 0\<close>] have "(p + q) * r = (p + q) * (monom ?c ?t + ?r)" by simp
  also have "\<dots> = (p + q) * (monom ?c ?t) + (p + q) * ?r"
    using times_mpoly_dist_left by simp
  also have "\<dots> = (p + q) * (monom ?c ?t) + (p * ?r + q * ?r)"
    using IH by simp
  also have "\<dots> = monom_mult ?c ?t (p + q) + (p * ?r + q * ?r)"
    using times_mpoly_right_monom by simp
  also have "\<dots> = (monom_mult ?c ?t p + monom_mult ?c ?t q) + (p * ?r + q * ?r)"
    by (simp only: monom_mult_dist_right)
  also have "\<dots> = (p * (monom ?c ?t) + q * (monom ?c ?t)) + (p * ?r + q * ?r)"
    using times_mpoly_right_monom by simp
  also have "\<dots> = (p * (monom ?c ?t) + p * ?r) + (q * (monom ?c ?t) + q * ?r)"
    by (simp only: ac_simps)
  also have "\<dots> = (p * (monom ?c ?t + ?r)) + (q * (monom ?c ?t + ?r))"
    using times_mpoly_dist_left by simp
  also have "\<dots> = p * r + q * r" using some_monomial_rest[OF \<open>r \<noteq> 0\<close>] by simp
  finally show "(p + q) * r = p * r + q * r" .
qed

lemma times_mpoly_comm:
  fixes p q::"('a, 'b) mpoly"
  shows "p * q = q * p"
proof (induct rule: times_mpoly_induct)
  from times_mpoly_right0 show "p * 0 = 0" .
next
  fix q::"('a, 'b) mpoly"
  let ?c = "coeff q (some_term q)"
  let ?t = "some_term q"
  let ?r = "rest_mpoly q"
  assume "q \<noteq> 0" and IH: "p * ?r = ?r * p"
  have "p * q = p * (monom ?c ?t + ?r)"
    using some_monomial_rest[OF \<open>q \<noteq> 0\<close>] by simp
  also have "\<dots> = p * (monom ?c ?t) + p * ?r"
    using times_mpoly_dist_left by simp
  also have "\<dots> = p * (monom ?c ?t) + ?r * p"
    using IH by simp
  also have "\<dots> = monom_mult ?c ?t p + ?r * p"
    using times_mpoly_right_monom by simp
  finally show "p * q = monom_mult ?c ?t p + ?r * p" .
qed

lemma times_mpoly_assoc_monom_mult:
  fixes c::'b and t::"'a" and p q::"('a, 'b) mpoly"
  shows "(monom_mult c t p) * q = monom_mult c t (p * q)"
proof (induct rule: times_mpoly_induct[of "\<lambda>x y _. (monom_mult c t y) * x = monom_mult c t (y * x)"])
  from times_mpoly_right0 monom_mult_right0 show "monom_mult c t p * 0 = monom_mult c t (p * 0)"
    by simp
next
  fix q::"('a, 'b) mpoly"
  let ?c = "coeff q (some_term q)"
  let ?t = "some_term q"
  let ?r = "rest_mpoly q"
  assume "q \<noteq> 0" and IH: "monom_mult c t p * ?r = monom_mult c t (p * ?r)"
  have "monom_mult c t p * q = (monom_mult c t p * (monom ?c ?t + ?r))"
    using some_monomial_rest[OF \<open>q \<noteq> 0\<close>] by simp
  also have "\<dots> = (monom_mult c t p * (monom (?c) (?t))) + (monom_mult c t p * (?r))"
    using times_mpoly_dist_left by simp
  also have "\<dots> = (monom_mult c t p * (monom (?c) (?t))) + monom_mult c t (p * (?r))"
    using IH by simp
  also have "\<dots> = (monom_mult (?c) (?t) (monom_mult c t p)) + monom_mult c t (p * (?r))"
    using times_mpoly_right_monom[of _ "?c" "?t"] by simp
  also have "\<dots> = (monom_mult (c * ?c) (t * ?t) p) + monom_mult c t (p * (?r))"
    using monom_mult_assoc[of "?c" "?t" c t p] by (simp only: ac_simps)
  also have "\<dots> = (monom_mult c t (monom_mult (?c) (?t) p)) + monom_mult c t (p * (?r))"
    using monom_mult_assoc[of c t "?c" "?t" p] by simp
  also have "\<dots> = (monom_mult c t (p * (monom (?c) (?t)))) + monom_mult c t (p * (?r))"
    using times_mpoly_right_monom by simp
  also have "\<dots> = monom_mult c t (p * (monom (?c) (?t)) + p * (?r))"
    using monom_mult_dist_right[of c t] by simp
  also have "\<dots> = monom_mult c t (p * (monom (?c) (?t) + ?r))"
    using times_mpoly_dist_left by simp
  also have "\<dots> = monom_mult c t (p * q)"
    using some_monomial_rest[OF \<open>q \<noteq> 0\<close>] by simp
  finally show "monom_mult c t p * q = monom_mult c t (p * q)" .
qed

lemma times_mpoly_assoc:
  fixes p q r::"('a, 'b) mpoly"
  shows "(p * q) * r = p * (q * r)"
proof (induct rule: times_mpoly_induct)
  from times_mpoly_left0 show "(0 * q) * r = 0" by simp
next
  fix p::"('a, 'b) mpoly"
  let ?c = "coeff p (some_term p)"
  let ?t = "some_term p"
  let ?r = "rest_mpoly p"
  assume "p \<noteq> 0" and IH: "(?r * q) * r = ?r * (q * r)"
  from \<open>p \<noteq> 0\<close> have "(p * q) * r = (monom_mult ?c ?t q + ?r * q) * r" by simp
  also have "\<dots> = ((monom_mult ?c ?t q) * r) + (?r * q) * r"
    using times_mpoly_dist_right by simp
  also have "\<dots> = ((monom_mult ?c ?t q) * r) + ?r * (q * r)"
    using IH by simp
  also have "\<dots> = monom_mult ?c ?t (q * r) + ?r * (q * r)"
    using times_mpoly_assoc_monom_mult by simp
  finally show "(p * q) * r = monom_mult ?c ?t (q * r) + ?r * (q * r)" .
qed

instance proof
  fix p::"('a, 'b) mpoly"
  from times_mpoly_left0 show "0 * p = 0" .
next
  fix p::"('a, 'b) mpoly"
  from times_mpoly_right0 show "p * 0 = 0" .
next
  fix p q r::"('a, 'b) mpoly"
  from times_mpoly_assoc show "(p * q) * r = p * (q * r)" .
next
  fix p q r::"('a, 'b) mpoly"
  from times_mpoly_dist_right show "(p + q) * r = p * r + q * r" .
next
  fix p q::"('a, 'b) mpoly"
  from times_mpoly_comm show "p * q = q * p" .
qed

end (* instantiation *)

instantiation mpoly :: ("{powerprod, linorder}", comm_ring) comm_ring
begin
instance ..

lemma pideal_closed_times:
  fixes bs::"('a, 'b) mpoly set"
  assumes p_in: "p \<in> pideal bs"
  shows "q * p \<in> pideal bs"
proof (induct rule: times_mpoly_induct)
  from pideal_0 show "0 \<in> pideal bs" .
next
  fix q
  assume "q \<noteq> 0" and "rest_mpoly q * p \<in> pideal bs"
  show "monom_mult (coeff q (some_term q)) (some_term q) p + rest_mpoly q * p \<in> pideal bs"
    by (rule pideal_closed_plus, rule pideal_closed_monom_mult, fact+)
qed

end (* instantiation *)

instantiation mpoly :: ("{powerprod, linorder}", comm_ring_1) comm_ring_1
begin

instance proof
  fix p::"('a, 'b) mpoly"
  from times_mpoly_left_monom[of 1 1 p] monom_mult_left1[of p] show "1 * p = p"
    unfolding one_mpoly_def by simp
next
  from zero_not_one_mpoly[OF zero_neq_one] show "0 \<noteq> (1::('a, 'b) mpoly)" . 
qed

end (* instantiation *)

subsection \<open>Polynomials in Ordered Power-products\<close>

context ordered_powerprod
begin

subsubsection \<open>Leading Power-Product, Leading Coefficient, and Tail\<close>

lift_definition higher::"('a, 'b::zero) mpoly \<Rightarrow> 'a \<Rightarrow> ('a, 'b) mpoly" is
  "(\<lambda>p t. (\<lambda>s. (if t \<prec> s then p s else 0)))"
proof -
  fix p::"'a \<Rightarrow> 'b" and t::"'a"
  assume fin: "finite {t. p t \<noteq> 0}"
  have "{s. (if t \<prec> s then p s else 0) \<noteq> 0} \<subseteq> {t. p t \<noteq> 0}"
  proof
    fix s::"'a"
    assume "s \<in> {x. (if t \<prec> x then p x else 0) \<noteq> 0}"
    hence "(if t \<prec> s then p s else 0) \<noteq> 0" by simp
    hence "p s \<noteq> 0" by (simp split: split_if_asm)
    thus "s \<in> {t. p t \<noteq> 0}" by simp
  qed
  from finite_subset[OF this fin] show "finite {s. (if t \<prec> s then p s else 0) \<noteq> 0}" .
qed
lift_definition lower::"('a, 'b::zero) mpoly \<Rightarrow> 'a \<Rightarrow> ('a, 'b) mpoly" is
  "(\<lambda>p t. (\<lambda>s. (if s \<prec> t then p s else 0)))"
proof -
  fix p::"'a \<Rightarrow> 'b" and t::"'a"
  assume fin: "finite {t. p t \<noteq> 0}"
  have "{s. (if s \<prec> t then p s else 0) \<noteq> 0} \<subseteq> {t. p t \<noteq> 0}"
  proof
    fix s::"'a"
    assume "s \<in> {x. (if x \<prec> t then p x else 0) \<noteq> 0}"
    hence "(if s \<prec> t then p s else 0) \<noteq> 0" by simp
    hence "p s \<noteq> 0" by (simp split: split_if_asm)
    thus "s \<in> {t. p t \<noteq> 0}" by simp
  qed
  from finite_subset[OF this fin] show "finite {s. (if s \<prec> t then p s else 0) \<noteq> 0}" .
qed
definition lp::"('a, 'b::zero) mpoly \<Rightarrow> 'a" where
  "lp p \<equiv> (if p = 0 then 1 else ordered_powerprod_lin.Max (supp p))"
definition lc::"('a, 'b::zero) mpoly \<Rightarrow> 'b" where
  "lc p \<equiv> coeff p (lp p)"
definition tail::"('a, 'b::zero) mpoly \<Rightarrow> ('a, 'b) mpoly" where
  "tail p \<equiv> lower p (lp p)"

lemma higher_plus:
  fixes p q::"('a, 'b::ring) mpoly"
  shows "higher (p + q) t = higher p t + higher q t"
proof transfer
  fix p q::"'a \<Rightarrow> 'b" and t::"'a"
  show "(\<lambda>s. if t \<prec> s then p s + q s else 0) =
        (\<lambda>s. (if t \<prec> s then p s else 0) + (if t \<prec> s then q s else 0))" by (rule, simp)
qed

lemma higher_uminus:
  fixes p::"('a, 'b::ring) mpoly"
  shows "higher (-p) t = -(higher p t)"
proof transfer
  fix p::"'a \<Rightarrow> 'b" and t::"'a"
  show "(\<lambda>s. if t \<prec> s then - p s else 0) = (\<lambda>ta. - (if t \<prec> ta then p ta else 0))" by (rule, simp)
qed

lemma higher_minus:
  fixes p q::"('a, 'b::ring) mpoly"
  shows "higher (p - q) t = higher p t - higher q t"
unfolding minus_mpoly_def by (simp only: higher_plus higher_uminus)

lemma higher_0:
  shows "higher 0 t = 0"
proof transfer
  fix t::"'a"
  show "(\<lambda>s. if t \<prec> s then 0 else 0) = (\<lambda>_. 0)" by simp
qed

lemma higher_equal:
  shows "higher p t = higher q t \<longleftrightarrow> (\<forall>s. t \<prec> s \<longrightarrow> coeff p s = coeff q s)"
proof transfer
  fix p q::"'a \<Rightarrow> 'b" and t::"'a"
  show "((\<lambda>s. if t \<prec> s then p s else 0) = (\<lambda>s. if t \<prec> s then q s else 0)) = (\<forall>s. t \<prec> s \<longrightarrow> p s = q s)"
  proof
    assume "(\<lambda>s. if t \<prec> s then p s else 0) = (\<lambda>s. if t \<prec> s then q s else 0)" (is "?L = ?R")
    show "\<forall>s. t \<prec> s \<longrightarrow> p s = q s"
    proof (intro allI, intro impI)
      fix s
      assume "t \<prec> s"
      from \<open>?L = ?R\<close> have "(if t \<prec> s then p s else 0) = (if t \<prec> s then q s else 0)" by meson
      thus "p s = q s" using \<open>t \<prec> s\<close> by simp
    qed
  next
    assume a: "\<forall>s. t \<prec> s \<longrightarrow> p s = q s"
    show "(\<lambda>s. if t \<prec> s then p s else 0) = (\<lambda>s. if t \<prec> s then q s else 0)"
    proof
      fix s
      from a have b: "t \<prec> s \<longrightarrow> p s = q s" ..
      show "(if t \<prec> s then p s else 0) = (if t \<prec> s then q s else 0)"
      proof (simp split: if_splits(1), intro impI)
        assume "t \<prec> s"
        thus "p s = q s" using b by simp
      qed
    qed
  qed
qed

lemma higher_equal_0:
  shows "higher p t = 0 \<longleftrightarrow> (\<forall>s. t \<prec> s \<longrightarrow> coeff p s = 0)"
proof -
  from higher_equal[of p t 0] higher_0[of t, symmetric]
    have "higher p t = 0 \<longleftrightarrow> (\<forall>s. t \<prec> s \<longrightarrow> coeff p s = coeff 0 s)" by auto
  moreover have "\<dots> \<longleftrightarrow> (\<forall>s. t \<prec> s \<longrightarrow> coeff p s = 0)" using coeff_0 by auto
  ultimately show ?thesis by simp
qed

lemma lp_alt:
  assumes "p \<noteq> 0"
  shows "lp p = ordered_powerprod_lin.Max (supp p)"
using assms unfolding lp_def by simp

lemma lp_max:
  assumes "coeff p t \<noteq> 0"
  shows "t \<preceq> lp p"
proof -
  from assms have t_in: "t \<in> supp p" unfolding supp_def by simp
  hence "supp p \<noteq> {}" by auto
  hence "p \<noteq> 0" by (simp add: supp_0)
  from lp_alt[OF this] ordered_powerprod_lin.Max_ge[OF supp_finite t_in] show ?thesis by simp
qed

lemma lp_eqI:
  assumes ct_not_0: "coeff p t \<noteq> 0" and a2: "\<And>s. coeff p s \<noteq> 0 \<Longrightarrow> s \<preceq> t"
  shows "lp p = t"
proof -
  from ct_not_0 have "t \<in> supp p" unfolding supp_def by simp
  hence "supp p \<noteq> {}" by auto
  hence "p \<noteq> 0" by (simp add: supp_0)
  have "\<And>s. s \<in> supp p \<Longrightarrow> s \<preceq> t"
  proof -
    fix s::"'a"
    assume "s \<in> supp p"
    hence "coeff p s \<noteq> 0" unfolding supp_def by simp
    from a2[OF this] show "s \<preceq> t" .
  qed
  from lp_alt[OF \<open>p \<noteq> 0\<close>] ordered_powerprod_lin.Max_eqI[OF supp_finite this \<open>t \<in> supp p\<close>]
    show ?thesis by simp
qed

lemma lp_less:
  assumes a: "\<And>s. t \<preceq> s \<Longrightarrow> coeff p s = 0" and "p \<noteq> 0"
  shows "lp p \<prec> t"
proof -
  from \<open>p \<noteq> 0\<close> have "supp p \<noteq> {}" using supp_0[of p] by simp
  have "\<forall>s\<in>supp p. s \<prec> t"
  proof
    fix s::"'a"
    assume "s \<in> supp p"
    hence "coeff p s \<noteq> 0" unfolding supp_def by simp
    hence "\<not> t \<preceq> s" using a[of s] by auto
    thus "s \<prec> t" by simp
  qed
  with lp_alt[OF \<open>p \<noteq> 0\<close>] ordered_powerprod_lin.Max_less_iff[OF supp_finite[of p] \<open>supp p \<noteq> {}\<close>]
    show ?thesis by simp
qed

lemma lp_gr:
  assumes "coeff p s \<noteq> 0" and "t \<prec> s"
  shows "t \<prec> lp p"
proof -
  from \<open>coeff p s \<noteq> 0\<close> have "s \<in> supp p" unfolding supp_def by simp
  hence "supp p \<noteq> {}" by auto
  hence "p \<noteq> 0" by (simp add: supp_0)
  have "\<exists>s\<in>supp p. t \<prec> s"
  proof
    from \<open>t \<prec> s\<close> show "t \<prec> s" .
  next
    from \<open>s \<in> supp p\<close> show "s \<in> supp p" .
  qed
  with lp_alt[OF \<open>p \<noteq> 0\<close>] ordered_powerprod_lin.Max_gr_iff[OF supp_finite[of p] \<open>supp p \<noteq> {}\<close>]
    show?thesis  by simp
qed

lemma lc_not_0:
  assumes "p \<noteq> 0"
  shows "lc p \<noteq> 0"
proof -
  from supp_0 assms have "supp p \<noteq> {}" by auto
  from lp_alt[OF assms] ordered_powerprod_lin.Max_in[OF supp_finite this]
    show ?thesis unfolding lc_def supp_def by simp
qed

lemma coeff_tail:
  assumes "p \<noteq> 0"
  shows "coeff (tail p) t = (if t \<prec> lp p then coeff p t else 0)"
using assms lp_max[of p] lc_not_0[of p] unfolding lp_alt[OF assms] lc_def tail_def
by (transfer, simp)

lemma coeff_tail_2:
  assumes "p \<noteq> 0"
  shows "coeff (tail p) t = (if t = lp p then 0 else coeff p t)"
proof (rule ordered_powerprod_lin.linorder_cases[of t "lp p"])
  assume "t \<prec> lp p"
  hence "t \<noteq> lp p" by simp
  from this \<open>t \<prec> lp p\<close> coeff_tail[OF assms, of t] show ?thesis by simp
next
  assume "t = lp p"
  hence "\<not> t \<prec> lp p" by simp
  from \<open>t = lp p\<close> this coeff_tail[OF assms, of t] show ?thesis by simp
next
  assume "lp p \<prec> t"
  hence "\<not> t \<preceq> lp p" by simp
  hence cp: "coeff p t = 0" using lp_max[of p t] by auto
  from \<open>\<not> t \<preceq> lp p\<close> have "\<not> t = lp p" and "\<not> t \<prec> lp p" by simp_all
  thus ?thesis using cp coeff_tail[OF assms, of t] by simp
qed

lemma leading_monomial_tail:
  fixes p::"('a, 'b::comm_monoid_add) mpoly"
  assumes "p \<noteq> 0"
  shows "p = monom (lc p) (lp p) + tail p"
proof (rule mpoly_ext)
  fix t
  have "coeff p t = coeff (monom (lc p) (lp p)) t + coeff (tail p) t"
  proof (cases "t \<preceq> lp p")
    case True
    show ?thesis
    proof (cases "t = lp p")
      assume "t = lp p"
      hence "\<not> t \<prec> lp p" by simp
      hence c3: "coeff (tail p) t = 0" unfolding coeff_tail[OF assms, of t] by simp
      from \<open>t = lp p\<close> have c2: "coeff (monom (lc p) (lp p)) t = lc p" unfolding coeff_monom by simp
      from \<open>t = lp p\<close> have c1: "coeff p t = lc p" unfolding lc_def by simp
      from c1 c2 c3 show ?thesis by simp
    next
      assume "t \<noteq> lp p"
      from this True have "t \<prec> lp p" by simp
      hence c2: "coeff (tail p) t = coeff p t" unfolding coeff_tail[OF assms, of t] by simp
      from \<open>t \<noteq> lp p\<close> have c1: "coeff (monom (lc p) (lp p)) t = 0" unfolding coeff_monom by simp
      from c1 c2 show ?thesis by simp
    qed
  next
    case False
    hence "lp p \<prec> t" by simp
    hence "lp p \<noteq> t" by simp
    from False have "\<not> t \<prec> lp p" by simp
    have c1: "coeff p t = 0"
    proof (rule ccontr)
      assume "coeff p t \<noteq> 0"
      from lp_max[OF this] False show False by simp
    qed
    from \<open>lp p \<noteq> t\<close> have c2: "coeff (monom (lc p) (lp p)) t = 0" unfolding coeff_monom by simp
    from \<open>\<not> t \<prec> lp p\<close> coeff_tail[OF assms, of t] have c3: "coeff (tail p) t = 0" by simp
    from c1 c2 c3 show ?thesis by simp
  qed
  thus "coeff p t = coeff (monom (lc p) (lp p) + tail p) t"
    using coeff_plus[of "monom (lc p) (lp p)"] by simp
qed

lemma tail_0:
  shows "tail 0 = 0"
unfolding tail_def lp_def
by (transfer, simp)

lemma lp_tail:
  assumes "tail p \<noteq> 0"
  shows "lp (tail p) \<prec> lp p"
proof -
  have "p \<noteq> 0"
  proof
    assume "p = 0"
    thus False using assms tail_0 by auto
  qed
  show ?thesis
  proof (intro lp_less)
    from assms show "tail p \<noteq> 0" .
  next
    fix s::"'a"
    assume "lp p \<preceq> s"
    hence "\<not> s \<prec> lp p" by simp
    thus "coeff (tail p) s = 0" unfolding coeff_tail[OF \<open>p \<noteq> 0\<close>, of s] by simp
  qed
qed

lemma lp_monom:
  assumes "c \<noteq> 0"
  shows "lp (monom c t) = t"
proof (rule lp_eqI)
  from coeff_monom[of c t t] assms show "coeff (monom c t) t \<noteq> 0" by simp
next
  fix s
  assume "coeff (monom c t) s \<noteq> 0"
  from this coeff_monom[of c t s] have "(if s = t then c else 0) \<noteq> 0" by simp
  hence "s = t" by meson
  thus "s \<preceq> t" by simp
qed

lemma lc_monom:
  assumes "c \<noteq> 0"
  shows "lc (monom c t) = c"
unfolding lc_def lp_monom[OF assms] by (simp add: coeff_monom)

lemma tail_monom:
  shows "tail (monom c t) = 0"
proof (cases "c = 0")
  case True
  hence "monom c t = 0" by (rule monom_0I)
  thus ?thesis using tail_0 by simp
next
  case False
  have a: "monom c t \<noteq> 0"
  proof
    assume "monom c t = 0"
    from monom_0D[OF this] False show False by simp
  qed
  show ?thesis
  proof (rule mpoly_ext, simp add: coeff_0 coeff_tail[OF a] lp_monom[OF False], intro impI)
    fix s
    assume "s \<prec> t"
    hence "s \<noteq> t" by simp
    thus "coeff (monom c t) s = 0" unfolding coeff_monom by simp
  qed
qed

lemma coeff_higher:
  shows "coeff (higher p s) t = (if s \<prec> t then coeff p t else 0)"
using assms lp_max[of p] lc_not_0[of p] unfolding lp_def lc_def
proof transfer
  fix p::"'a \<Rightarrow> 'b" and t s::"'a"
  show "(if s \<prec> t then p t else 0) = (if s \<prec> t then p t else 0)" by simp
qed

lemma lp_mult:
  fixes c::"'b::semiring_no_zero_divisors"
  assumes "c \<noteq> 0" and "p \<noteq> 0"
  shows "lp (monom_mult c t p) = t * lp p"
proof (intro lp_eqI)
  from assms lc_not_0[OF \<open>p \<noteq> 0\<close>] show "coeff (monom_mult c t p) (t * lp p) \<noteq> 0"
    unfolding lc_def lp_alt[OF \<open>p \<noteq> 0\<close>]
  proof transfer
    fix c::'b and t::"'a" and p::"'a \<Rightarrow> 'b" and ord::"'a \<Rightarrow> 'a \<Rightarrow> bool"
    assume "c \<noteq> 0" and a: "p (linorder.Max ord {t. p t \<noteq> 0}) \<noteq> 0"
    have "t dvd t * linorder.Max ord {s. p s \<noteq> 0}" by (rule, simp)
    from this \<open>c \<noteq> 0\<close> a times_divide_2[of t "linorder.Max ord {s. p s \<noteq> 0}"] show
      "(if t dvd t * linorder.Max ord {t. p t \<noteq> 0} then
          c * p (t * linorder.Max ord {t. p t \<noteq> 0} divide t)
        else
          0
       ) \<noteq> 0" by simp
  qed
next
  show "\<And>s. coeff (monom_mult c t p) s \<noteq> 0 \<Longrightarrow> s \<preceq> t * lp p"
  proof -
    fix s::"'a"
    from assms lp_max[of p] times_monotone[of _ "lp p"]
      show "coeff (monom_mult c t p) s \<noteq> 0 \<Longrightarrow> s \<preceq> t * lp p" unfolding lc_def lp_alt[OF \<open>p \<noteq> 0\<close>]
    proof (transfer fixing: s)
      fix c::"'b" and t::"'a" and p::"'a \<Rightarrow> 'b" and ord::"'a \<Rightarrow> 'a \<Rightarrow> bool"
      assume "c \<noteq> 0" and "(if t dvd s then c * p (s divide t) else 0) \<noteq> 0"
        and b: "\<And>t. p t \<noteq> 0 \<Longrightarrow> ord t (linorder.Max ord {t. p t \<noteq> 0})"
        and c: "(\<And>s u. ord s (linorder.Max ord {t. p t \<noteq> 0}) \<Longrightarrow>
                ord (s * u) (linorder.Max ord {t. p t \<noteq> 0} * u))"
      hence "t dvd s" and a: "c * p (s divide t) \<noteq> 0" by (simp_all split: split_if_asm)
      from \<open>t dvd s\<close> obtain u::"'a" where "s = t * u" unfolding dvd_def ..
      hence "s divide t = u" using times_divide_2 by simp
      hence "p u \<noteq> 0" using a by simp
      from \<open>s = t * u\<close> c[OF b[OF this], of t]
        show "ord s (t * linorder.Max ord {t. p t \<noteq> 0})" by (simp add: ac_simps)
    qed
  qed
qed

lemma lc_mult:
  fixes c::"'b::semiring_no_zero_divisors"
  assumes "c \<noteq> 0" and "p \<noteq> 0"
  shows "lc (monom_mult c t p) = c * lc p"
unfolding lc_def
proof -
  from monom_mult_coeff[of c t p "lp p"] lp_mult[OF assms, of t]
    show "coeff (monom_mult c t p) (lp (monom_mult c t p)) = c * coeff p (lp p)" by simp
qed

lemma coeff_mult_0:
  fixes c::"'b::semiring_no_zero_divisors"
  assumes "s * lp p \<prec> t"
  shows "coeff (monom_mult c s p) t = 0"
proof (cases "p = 0")
  assume "p = 0"
  thus ?thesis using monom_mult_right0[of c s] coeff_0[of t] by simp
next
  assume "p \<noteq> 0"
  show ?thesis
  proof (cases "c = 0")
    assume "c = 0"
    thus ?thesis using monom_mult_left0[of s p] coeff_0[of t] by simp
  next
    assume "c \<noteq> 0"
    from lp_mult[OF \<open>c \<noteq> 0\<close> \<open>p \<noteq> 0\<close>, of s] assms have "lp (monom_mult c s p) \<prec> t" by simp
    hence "\<not> t \<preceq> lp (monom_mult c s p)" by simp
    thus ?thesis using lp_max[of "monom_mult c s p" t] by auto
  qed
qed

subsubsection \<open>Order Relation on Polynomials\<close>

definition ord_strict_p::"('a, 'b::zero) mpoly \<Rightarrow> ('a, 'b) mpoly \<Rightarrow> bool" (infixl "\<prec>p" 50) where
  "ord_strict_p p q \<equiv> (\<exists>t. coeff p t = 0 \<and> coeff q t \<noteq> 0 \<and> (\<forall>s. t \<prec> s \<longrightarrow> coeff p s = coeff q s))"
definition ord_p::"('a, 'b::zero) mpoly \<Rightarrow> ('a, 'b) mpoly \<Rightarrow> bool" (infixl "\<preceq>p" 50) where
  "ord_p p q \<equiv> (p \<prec>p q \<or> p = q)"

lemma ord_strict_higher:
  shows "p \<prec>p q \<longleftrightarrow> (\<exists>t. coeff p t = 0 \<and> coeff q t \<noteq> 0 \<and> higher p t = higher q t)"
unfolding ord_strict_p_def higher_equal ..

lemma ord_strict_p_asymmetric:
  assumes "p \<prec>p q"
  shows "\<not> q \<prec>p p"
using assms unfolding ord_strict_p_def
proof
  fix t1::"'a"
  assume "coeff p t1 = 0 \<and> coeff q t1 \<noteq> 0 \<and> (\<forall>s. t1 \<prec> s \<longrightarrow> coeff p s = coeff q s)"
  hence "coeff p t1 = 0" and "coeff q t1 \<noteq> 0" and t1: "\<forall>s. t1 \<prec> s \<longrightarrow> coeff p s = coeff q s"
    by auto
  show "\<not> (\<exists>t. coeff q t = 0 \<and> coeff p t \<noteq> 0 \<and> (\<forall>s. t \<prec> s \<longrightarrow> coeff q s = coeff p s))"
  proof (intro notI, erule exE)
    fix t2::"'a"
    assume "coeff q t2 = 0 \<and> coeff p t2 \<noteq> 0 \<and> (\<forall>s. t2 \<prec> s \<longrightarrow> coeff q s = coeff p s)"
    hence "coeff q t2 = 0" and "coeff p t2 \<noteq> 0" and t2: "\<forall>s. t2 \<prec> s \<longrightarrow> coeff q s = coeff p s"
      by auto
    have "t1 \<prec> t2 \<or> t1 = t2 \<or> t2 \<prec> t1" using less_linear by auto
    thus False
    proof
      assume "t1 \<prec> t2"
      from t1[rule_format, OF this] \<open>coeff q t2 = 0\<close> \<open>coeff p t2 \<noteq> 0\<close> show ?thesis by simp
    next
      assume "t1 = t2 \<or> t2 \<prec> t1"
      thus ?thesis
      proof
        assume "t1 = t2"
        thus ?thesis using \<open>coeff p t1 = 0\<close> \<open>coeff p t2 \<noteq> 0\<close> by simp
      next
        assume "t2 \<prec> t1"
        from t2[rule_format, OF this] \<open>coeff p t1 = 0\<close> \<open>coeff q t1 \<noteq> 0\<close> show ?thesis by simp
      qed
    qed
  qed
qed

lemma ord_strict_p_irreflexive:
  shows "\<not> p \<prec>p p"
unfolding ord_strict_p_def
proof (intro notI, erule exE)
  fix t::"'a"
  assume "coeff p t = 0 \<and> coeff p t \<noteq> 0 \<and> (\<forall>s. t \<prec> s \<longrightarrow> coeff p s = coeff p s)"
  hence "coeff p t = 0" and "coeff p t \<noteq> 0" by auto
  thus False by simp
qed

lemma ord_strict_p_transitive:
  assumes "a \<prec>p b" and "b \<prec>p c"
  shows "a \<prec>p c"
proof -
  from \<open>a \<prec>p b\<close> obtain t1 where "coeff a t1 = 0"
                            and "coeff b t1 \<noteq> 0"
                            and t1[rule_format]: "(\<forall>s. t1 \<prec> s \<longrightarrow> coeff a s = coeff b s)"
    unfolding ord_strict_p_def by auto
  from \<open>b \<prec>p c\<close> obtain t2 where "coeff b t2 = 0"
                            and "coeff c t2 \<noteq> 0"
                            and t2[rule_format]: "(\<forall>s. t2 \<prec> s \<longrightarrow> coeff b s = coeff c s)"
    unfolding ord_strict_p_def by auto
  have "t1 \<prec> t2 \<or> t1 = t2 \<or> t2 \<prec> t1" using less_linear by auto
  thus "a \<prec>p c"
  proof
    assume "t1 \<prec> t2"
    show ?thesis unfolding ord_strict_p_def
    proof
      show "coeff a t2 = 0 \<and> coeff c t2 \<noteq> 0 \<and> (\<forall>s. t2 \<prec> s \<longrightarrow> coeff a s = coeff c s)"
      proof
        from \<open>coeff b t2 = 0\<close> t1[OF \<open>t1 \<prec> t2\<close>] show "coeff a t2 = 0" by simp
      next
        show "coeff c t2 \<noteq> 0 \<and> (\<forall>s. t2 \<prec> s \<longrightarrow> coeff a s = coeff c s)"
        proof
          from \<open>coeff c t2 \<noteq> 0\<close> show "coeff c t2 \<noteq> 0" .
        next
          show "\<forall>s. t2 \<prec> s \<longrightarrow> coeff a s = coeff c s"
          proof (rule, rule)
            fix s::"'a"
            assume "t2 \<prec> s"
            from ordered_powerprod_lin.less_trans[OF \<open>t1 \<prec> t2\<close> this] have "t1 \<prec> s" .
            from t2[OF \<open>t2 \<prec> s\<close>] t1[OF this] show "coeff a s = coeff c s" by simp
          qed
        qed
      qed
    qed
  next
    assume "t1 = t2 \<or> t2 \<prec> t1"
    thus ?thesis
    proof
      assume "t2 \<prec> t1"
      show ?thesis unfolding ord_strict_p_def
      proof
        show "coeff a t1 = 0 \<and> coeff c t1 \<noteq> 0 \<and> (\<forall>s. t1 \<prec> s \<longrightarrow> coeff a s = coeff c s)"
        proof
          from \<open>coeff a t1 = 0\<close> show "coeff a t1 = 0" .
        next
          show "coeff c t1 \<noteq> 0 \<and> (\<forall>s. t1 \<prec> s \<longrightarrow> coeff a s = coeff c s)"
          proof
            from \<open>coeff b t1 \<noteq> 0\<close> t2[OF \<open>t2 \<prec> t1\<close>] show "coeff c t1 \<noteq> 0" by simp
          next
            show "\<forall>s. t1 \<prec> s \<longrightarrow> coeff a s = coeff c s"
            proof (rule, rule)
              fix s::"'a"
              assume "t1 \<prec> s"
              from ordered_powerprod_lin.less_trans[OF \<open>t2 \<prec> t1\<close> this] have "t2 \<prec> s" .
              from t1[OF \<open>t1 \<prec> s\<close>] t2[OF this] show "coeff a s = coeff c s" by simp
            qed
          qed
        qed
      qed
    next
      assume "t1 = t2"
      thus ?thesis using \<open>coeff b t1 \<noteq> 0\<close> \<open>coeff b t2 = 0\<close> by simp
    qed
  qed
qed

sublocale order ord_p ord_strict_p
proof (intro order_strictI)
  fix p q::"('a, 'b) mpoly"
  show "(p \<preceq>p q) = (p \<prec>p q \<or> p = q)" unfolding ord_p_def ..
next
  fix p q::"('a, 'b) mpoly"
  assume "p \<prec>p q"
  from ord_strict_p_asymmetric[OF this] show "\<not> q \<prec>p p" .
next
  fix p::"('a, 'b) mpoly"
  from ord_strict_p_irreflexive[of p] show "\<not> p \<prec>p p" .
next
  fix a b c::"('a, 'b) mpoly"
  assume "a \<prec>p b" and "b \<prec>p c"
  from ord_strict_p_transitive[OF this] show "a \<prec>p c" .
qed

lemma ord_p_0_min:
  shows "0 \<preceq>p p"
unfolding ord_p_def ord_strict_p_def
proof (cases "p = 0")
  case True
  thus "(\<exists>t. coeff 0 t = 0 \<and> coeff p t \<noteq> 0 \<and> (\<forall>s. t \<prec> s \<longrightarrow> coeff 0 s = coeff p s)) \<or> 0 = p"
    by auto
next
  case False
  show "(\<exists>t. coeff 0 t = 0 \<and> coeff p t \<noteq> 0 \<and> (\<forall>s. t \<prec> s \<longrightarrow> coeff 0 s = coeff p s)) \<or> 0 = p"
  proof
    show "(\<exists>t. coeff 0 t = 0 \<and> coeff p t \<noteq> 0 \<and> (\<forall>s. t \<prec> s \<longrightarrow> coeff 0 s = coeff p s))"
    proof
      show "coeff 0 (lp p) = 0 \<and> coeff p (lp p) \<noteq> 0 \<and> (\<forall>s. (lp p) \<prec> s \<longrightarrow> coeff 0 s = coeff p s)"
      proof
        show "coeff 0 (lp p) = 0" by (transfer, simp)
      next
        show "coeff p (lp p) \<noteq> 0 \<and> (\<forall>s. lp p \<prec> s \<longrightarrow> coeff 0 s = coeff p s)"
        proof
          from lc_not_0[OF False] show "coeff p (lp p) \<noteq> 0" unfolding lc_def .
        next
          show "\<forall>s. lp p \<prec> s \<longrightarrow> coeff 0 s = coeff p s"
          proof (rule, rule)
            fix s::"'a"
            assume "lp p \<prec> s"
            hence "\<not> s \<preceq> lp p" by simp
            hence "coeff p s = 0" using lp_max[of p s] by auto
            thus "coeff 0 s = coeff p s" by (transfer, simp)
          qed
        qed
      qed
    qed
  qed
qed

lemma lp_ord_p:
  assumes "q \<noteq> 0" and "lp p \<prec> lp q"
  shows "p \<prec>p q"
unfolding ord_strict_p_def
proof (intro exI, intro conjI)
  show "coeff p (lp q) = 0"
  proof (rule ccontr)
    assume "coeff p (lp q) \<noteq> 0"
    from lp_max[OF this] \<open>lp p \<prec> lp q\<close> show False by simp
  qed
next
  from lc_not_0[OF \<open>q \<noteq> 0\<close>] show "coeff q (lp q) \<noteq> 0" unfolding lc_def .
next
  show "\<forall>s. lp q \<prec> s \<longrightarrow> coeff p s = coeff q s"
  proof (intro allI, intro impI)
    fix s
    assume "lp q \<prec> s"
    hence "lp p \<prec> s" using \<open>lp p \<prec> lp q\<close> by simp
    have c1: "coeff q s = 0"
    proof (rule ccontr)
      assume "coeff q s \<noteq> 0"
      from lp_max[OF this] \<open>lp q \<prec> s\<close> show False by simp
    qed
    have c2: "coeff p s = 0"
    proof (rule ccontr)
      assume "coeff p s \<noteq> 0"
      from lp_max[OF this] \<open>lp p \<prec> s\<close> show False by simp
    qed
    from c1 c2 show "coeff p s = coeff q s" by simp
  qed
qed

lemma ord_p_lp:
  assumes "p \<preceq>p q" and "p \<noteq> 0"
  shows "lp p \<preceq> lp q"
proof (rule ccontr)
  assume "\<not> lp p \<preceq> lp q"
  hence "lp q \<prec> lp p" by simp
  from lp_ord_p[OF \<open>p \<noteq> 0\<close> this] \<open>p \<preceq>p q\<close> show False by simp
qed

lemma ord_p_tail:
  assumes "p \<noteq> 0" and "lp p = lp q" and "p \<prec>p q"
  shows "tail p \<prec>p tail q"
using assms unfolding ord_strict_p_def
proof -
  assume "p \<noteq> 0" and "lp p = lp q"
    and "\<exists>t. coeff p t = 0 \<and> coeff q t \<noteq> 0 \<and> (\<forall>s. t \<prec> s \<longrightarrow> coeff p s = coeff q s)"
  then obtain t where "coeff p t = 0"
                  and "coeff q t \<noteq> 0"
                  and a: "\<forall>s. t \<prec> s \<longrightarrow> coeff p s = coeff q s" by auto
  from lp_max[OF \<open>coeff q t \<noteq> 0\<close>] \<open>lp p = lp q\<close> have "t \<prec> lp p \<or> t = lp p" by auto
  hence "t \<prec> lp p"
  proof
    assume "t \<prec> lp p"
    thus ?thesis .
  next
    assume "t = lp p"
    thus ?thesis using lc_not_0[OF \<open>p \<noteq> 0\<close>] \<open>coeff p t = 0\<close> unfolding lc_def by simp
  qed
  have pt: "coeff (tail p) t = coeff p t" using coeff_tail[OF \<open>p \<noteq> 0\<close>, of t] \<open>t \<prec> lp p\<close> by simp
  have "q \<noteq> 0"
  proof
    assume "q = 0"
    hence  "p \<prec>p 0" using \<open>p \<prec>p q\<close> by simp
    hence "\<not> 0 \<preceq>p p" by auto
    thus False using ord_p_0_min[of p] by simp
  qed
  have qt: "coeff (tail q) t = coeff q t"
    using coeff_tail[OF \<open>q \<noteq> 0\<close>, of t] \<open>t \<prec> lp p\<close> \<open>lp p = lp q\<close> by simp
  show "\<exists>t. coeff (tail p) t = 0 \<and> coeff (tail q) t \<noteq> 0 \<and>
        (\<forall>s. t \<prec> s \<longrightarrow> coeff (tail p) s = coeff (tail q) s)"
  proof (rule, rule)
    from pt \<open>coeff p t = 0\<close> show "coeff (tail p) t = 0" by simp
  next
    show "coeff (tail q) t \<noteq> 0 \<and> (\<forall>s. t \<prec> s \<longrightarrow> coeff (tail p) s = coeff (tail q) s)"
    proof
      from qt \<open>coeff q t \<noteq> 0\<close> show "coeff (tail q) t \<noteq> 0" by simp
    next
      show "\<forall>s. t \<prec> s \<longrightarrow> coeff (tail p) s = coeff (tail q) s"
      proof (rule, rule)
        fix s::"'a"
        assume "t \<prec> s"
        from a[rule_format, OF \<open>t \<prec> s\<close>] coeff_tail[OF \<open>p \<noteq> 0\<close>, of s] coeff_tail[OF \<open>q \<noteq> 0\<close>, of s]
          \<open>lp p = lp q\<close> show "coeff (tail p) s = coeff (tail q) s" by simp
      qed
    qed
  qed
qed

lemma tail_ord_p:
  assumes "p \<noteq> 0"
  shows "tail p \<prec>p p"
proof (cases "tail p = 0")
  case True
  from this ord_p_0_min[of p] \<open>p \<noteq> 0\<close> show ?thesis by simp
next
  case False
  from lp_ord_p[OF \<open>p \<noteq> 0\<close> lp_tail[OF False]] show ?thesis .
qed

lemma higher_coeff_equal_0:
  assumes pt: "coeff p t = 0" and hp: "higher p t = 0" and le: "q \<preceq>p p"
  shows "(coeff q t = 0) \<and> (higher q t) = 0"
using le unfolding ord_p_def
proof
  assume "q \<prec>p p"
  thus ?thesis unfolding ord_strict_p_def
  proof
    fix s::"'a"
    assume "coeff q s = 0 \<and> coeff p s \<noteq> 0 \<and> (\<forall>u. s \<prec> u \<longrightarrow> coeff q u = coeff p u)"
    hence qs: "coeff q s = 0" and ps: "coeff p s \<noteq> 0" and u: "\<forall>u. s \<prec> u \<longrightarrow> coeff q u = coeff p u"
      by auto
    from hp have pu: "\<forall>u. t \<prec> u \<longrightarrow> coeff p u = 0" by (simp only: higher_equal_0)
    from pu[rule_format, of s] ps have "\<not> t \<prec> s" by auto
    hence "s \<preceq> t" by simp
    hence "s \<prec> t \<or> s = t" by auto
    hence st: "s \<prec> t"
    proof (rule disjE, simp_all)
      assume "s = t"
      from this pt ps show False by simp
    qed
    show ?thesis
    proof
      from u[rule_format, OF st] pt show "coeff q t = 0" by simp
    next
      have "\<forall>u. t \<prec> u \<longrightarrow> coeff q u = 0"
      proof (intro allI, intro impI)
        fix u
        assume "t \<prec> u"
        from this st have "s \<prec> u" by simp
        from u[rule_format, OF this] pu[rule_format, OF \<open>t \<prec> u\<close>] show "coeff q u = 0" by simp
      qed
      thus "higher q t = 0" by (simp only: higher_equal_0)
    qed
  qed
next
  assume "q = p"
  thus ?thesis using assms by simp
qed

lemma ord_strict_p_recI:
  assumes "q \<noteq> 0" and "p \<noteq> 0" and "lp p = lp q" and "lc p = lc q" and tail: "tail p \<prec>p tail q"
  shows "p \<prec>p q"
proof -
  from tail obtain t where pt: "coeff (tail p) t = 0"
                      and qt: "coeff (tail q) t \<noteq> 0"
                      and a: "\<forall>s. t \<prec> s \<longrightarrow> coeff (tail p) s = coeff (tail q) s"
    unfolding ord_strict_p_def by auto
  from qt coeff_0[of t] have "tail q \<noteq> 0" by auto
  from lp_max[OF qt] lp_tail[OF this] have "t \<prec> lp q" by simp
  hence "t \<prec> lp p" using \<open>lp p = lp q\<close> by simp
  show ?thesis unfolding ord_strict_p_def
  proof (rule exI[of _ t], intro conjI)
    from coeff_tail[OF \<open>p \<noteq> 0\<close>, of t] \<open>t \<prec> lp p\<close> pt show "coeff p t = 0" by simp
  next
    from coeff_tail[OF \<open>q \<noteq> 0\<close>, of t] \<open>t \<prec> lp q\<close> qt show "coeff q t \<noteq> 0" by simp
  next
    show "\<forall>s. t \<prec> s \<longrightarrow> coeff p s = coeff q s"
    proof (intro allI, intro impI)
      fix s
      assume "t \<prec> s"
      from this a have s: "coeff (tail p) s = coeff (tail q) s" by simp
      show "coeff p s = coeff q s"
      proof (cases "s = lp p")
        case True
        from True \<open>lc p = lc q\<close> \<open>lp p = lp q\<close> show ?thesis unfolding lc_def by simp
      next
        case False
        from False s coeff_tail_2[OF \<open>p \<noteq> 0\<close>, of s] coeff_tail_2[OF \<open>q \<noteq> 0\<close>, of s] \<open>lp p = lp q\<close>
          show ?thesis by simp
      qed
    qed
  qed
qed

lemma ord_strict_p_recE1:
  assumes "p \<prec>p q"
  shows "q \<noteq> 0"
proof
  assume "q = 0"
  from this assms ord_p_0_min[of p] show False by simp
qed

lemma ord_strict_p_recE2:
  assumes "p \<noteq> 0" and "p \<prec>p q" and "lp p = lp q"
  shows "lc p = lc q"
proof -
  from \<open>p \<prec>p q\<close> obtain t where pt: "coeff p t = 0"
                          and qt: "coeff q t \<noteq> 0"
                          and a: "\<forall>s. t \<prec> s \<longrightarrow> coeff p s = coeff q s"
    unfolding ord_strict_p_def by auto
  show ?thesis
  proof (cases "t \<prec> lp p")
    case True
    from this a have "coeff p (lp p) = coeff q (lp p)" by simp
    thus ?thesis using \<open>lp p = lp q\<close> unfolding lc_def by simp
  next
    case False
    from this lp_max[OF qt] \<open>lp p = lp q\<close> have "t = lp p" by simp
    from this lc_not_0[OF \<open>p \<noteq> 0\<close>] pt show ?thesis unfolding lc_def by simp
  qed
qed

lemma ord_strict_p_rec[code]:
  "p \<prec>p q =
  (q \<noteq> 0 \<and>
    (p = 0 \<or>
      (let l1 = lp p; l2 = lp q in
        (l1 \<prec> l2 \<or> (l1 = l2 \<and> coeff p l1 = coeff q l2 \<and> lower p l1 \<prec>p lower q l2))
      )
    )
   )"
  (is "?L = ?R")
proof
  assume ?L
  show ?R
  proof (intro conjI, rule ord_strict_p_recE1, fact)
    have "((lp p = lp q \<and> lc p = lc q \<and> tail p \<prec>p tail q) \<or> lp p \<prec> lp q) \<or> p = 0"
    proof (intro disjCI)
      assume "p \<noteq> 0" and nl: "\<not> lp p \<prec> lp q"
      from \<open>?L\<close> have "p \<preceq>p q" by simp
      from ord_p_lp[OF this \<open>p \<noteq> 0\<close>] nl have "lp p = lp q" by simp
      show "lp p = lp q \<and> lc p = lc q \<and> tail p \<prec>p tail q"
        by (intro conjI, fact, rule ord_strict_p_recE2, fact+, rule ord_p_tail, fact+)
    qed
    thus "p = 0 \<or>
            (let l1 = lp p; l2 = lp q in
              (l1 \<prec> l2 \<or> l1 = l2 \<and> coeff p l1 = coeff q l2 \<and> lower p l1 \<prec>p lower q l2)
            )"
      unfolding lc_def tail_def by auto
  qed
next
  assume ?R
  hence "q \<noteq> 0"
    and dis: "p = 0 \<or>
                (let l1 = lp p; l2 = lp q in
                  (l1 \<prec> l2 \<or> l1 = l2 \<and> coeff p l1 = coeff q l2 \<and> lower p l1 \<prec>p lower q l2)
                )"
    by simp_all
  show ?L
  proof (cases "p = 0")
    assume "p = 0"
    hence "p \<preceq>p q" using ord_p_0_min[of q] by simp
    thus ?thesis using \<open>p = 0\<close> \<open>q \<noteq> 0\<close> by simp
  next
    assume "p \<noteq> 0"
    hence "let l1 = lp p; l2 = lp q in
            (l1 \<prec> l2 \<or> l1 = l2 \<and> coeff p l1 = coeff q l2 \<and> lower p l1 \<prec>p lower q l2)"
      using dis by simp
    hence "lp p \<prec> lp q \<or> (lp p = lp q \<and> lc p = lc q \<and> tail p \<prec>p tail q)"
      unfolding lc_def tail_def by (simp add: Let_def)
    thus ?thesis
    proof
      assume "lp p \<prec> lp q"
      from lp_ord_p[OF \<open>q \<noteq> 0\<close> this] show ?thesis .
    next
      assume "lp p = lp q \<and> lc p = lc q \<and> tail p \<prec>p tail q"
      hence "lp p = lp q" and "lc p = lc q" and "tail p \<prec>p tail q" by simp_all
      from ord_strict_p_recI[OF \<open>q \<noteq> 0\<close> \<open>p \<noteq> 0\<close> this] show ?thesis .
    qed
  qed
qed

(*The following two lemmas prove that \<prec>p is well-founded.
Although the first proof uses induction on power-products whereas the second one does not,
the two proofs share a lot of common structure. Maybe this can be exploited to make things
shorter ...?*)
lemma ord_p_wf_aux:
  assumes "x \<in> Q" and a2: "\<forall>y\<in>Q. y = 0 \<or> lp y \<prec> s"
  shows "\<exists>p\<in>Q. (\<forall>q\<in>Q. \<not> q \<prec>p p)"
using assms
proof (induct s arbitrary: x Q rule: wfP_induct[OF wf_ord_strict])
  fix s::"'a" and x::"('a, 'b) mpoly" and Q::"('a, 'b) mpoly set"
  assume hyp: "\<forall>s0. s0 \<prec> s \<longrightarrow> (\<forall>x0 Q0::('a, 'b) mpoly set. x0 \<in> Q0 \<longrightarrow>
                                  (\<forall>y\<in>Q0. y = 0 \<or> lp y \<prec> s0) \<longrightarrow> (\<exists>p\<in>Q0. \<forall>q\<in>Q0. \<not> q \<prec>p p))"
  assume "x \<in> Q"
  assume bounded: "\<forall>y\<in>Q. y = 0 \<or> lp y \<prec> s"
  show "\<exists>p\<in>Q. \<forall>q\<in>Q. \<not> q \<prec>p p"
  proof (cases "0 \<in> Q")
    case True
    show ?thesis
    proof (rule, rule, rule)
      fix q::"('a, 'b) mpoly"
      assume "q \<prec>p 0"
      thus False using ord_p_0_min[of q] by simp
    next
      from True show "0 \<in> Q" .
    qed
  next
    case False
    def Q1 \<equiv> "{lp p | p. p \<in> Q}"
    from \<open>x \<in> Q\<close> have "lp x \<in> Q1" unfolding Q1_def by auto
    from wf_ord_strict have "wf {(x, y). x \<prec> y}" unfolding wfP_def .
    from wfE_min[OF this \<open>lp x \<in> Q1\<close>] obtain t where
      "t \<in> Q1" and t_min_1: "\<And>y. (y, t) \<in> {(x, y). x \<prec> y} \<Longrightarrow> y \<notin> Q1" by auto
    have t_min: "\<And>q. q \<in> Q \<Longrightarrow> t \<preceq> lp q"
    proof -
      fix q::"('a, 'b) mpoly"
      assume "q \<in> Q"
      hence "lp q \<in> Q1" unfolding Q1_def by auto
      hence "(lp q, t) \<notin> {(x, y). x \<prec> y}" using t_min_1 by auto
      hence "\<not> lp q \<prec> t" by simp
      thus "t \<preceq> lp q" by simp
    qed
    from \<open>t \<in> Q1\<close> obtain p where "lp p = t" and "p \<in> Q" unfolding Q1_def by auto
    hence "p \<noteq> 0" using False by auto
    hence "lp p \<prec> s" using bounded[rule_format, OF \<open>p \<in> Q\<close>] by auto
    def Q2 \<equiv> "{tail p | p. p \<in> Q \<and> lp p = t}"
    from \<open>p \<in> Q\<close> \<open>lp p = t\<close> have "tail p \<in> Q2" unfolding Q2_def by auto
    have "\<And>q. q \<in> Q2 \<Longrightarrow> q = 0 \<or> lp q \<prec> lp p"
    proof -
      fix q::"('a, 'b) mpoly"
      assume "q \<in> Q2"
      then obtain q0 where "q = tail q0" and "lp q0 = lp p" using \<open>lp p = t\<close> unfolding Q2_def by auto
      have "q \<noteq> 0 \<Longrightarrow> lp q \<prec> lp p"
      proof -
        assume "q \<noteq> 0"
        hence "tail q0 \<noteq> 0" using \<open>q = tail q0\<close> by simp
        from lp_tail[OF this] \<open>q = tail q0\<close> \<open>lp q0 = lp p\<close> show "lp q \<prec> lp p" by simp
      qed
      thus "q = 0 \<or> lp q \<prec> lp p" by auto
    qed
    from hyp[rule_format, OF \<open>lp p \<prec> s\<close> \<open>tail p \<in> Q2\<close> this] obtain q where
      "q \<in> Q2" and q_min: "\<forall>r\<in>Q2. \<not> r \<prec>p q" ..
    from \<open>q \<in> Q2\<close> obtain m where "q = tail m" and "m \<in> Q" and "lp m = t" unfolding Q2_def by auto
    from q_min \<open>q = tail m\<close> have m_tail_min: "\<And>r. r \<in> Q2 \<Longrightarrow> \<not> r \<prec>p tail m" by simp
    show ?thesis
    proof
      from \<open>m \<in> Q\<close> show "m \<in> Q" .
    next
      show "\<forall>r\<in>Q. \<not> r \<prec>p m"
      proof
        fix r::"('a, 'b) mpoly"
        assume "r \<in> Q"
        hence "r \<noteq> 0" using False by auto
        show "\<not> r \<prec>p m"
        proof
          assume "r \<prec>p m"
          hence "r \<preceq>p m" by simp
          from t_min[OF \<open>r \<in> Q\<close>] ord_p_lp[OF \<open>r \<preceq>p m\<close> \<open>r \<noteq> 0\<close>] \<open>lp m = t\<close> have "lp r = t" by simp
          hence "lp r = lp m" using \<open>lp m = t\<close> by simp
          from \<open>r \<in> Q\<close> \<open>lp r = t\<close> have "tail r \<in> Q2" unfolding Q2_def by auto
          from ord_p_tail[OF \<open>r \<noteq> 0\<close> \<open>lp r = lp m\<close> \<open>r \<prec>p m\<close>] m_tail_min[OF \<open>tail r \<in> Q2\<close>]
            show False by simp
        qed
      qed
    qed
  qed
qed

theorem ord_p_wf:
  shows "wfP (op \<prec>p)"
unfolding wfP_def
proof (intro wfI_min)
  fix Q::"('a, 'b) mpoly set" and x::"('a, 'b) mpoly"
  assume "x \<in> Q"
  show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> {(x, y). x \<prec>p y} \<longrightarrow> y \<notin> Q"
  proof (cases "0 \<in> Q")
    case True
    show ?thesis
    proof (rule, rule, rule)
      from True show "0 \<in> Q" .
    next
      fix q::"('a, 'b) mpoly"
      assume "(q, 0) \<in> {(x, y). x \<prec>p y}"
      thus "q \<notin> Q" using ord_p_0_min[of q] by simp
    qed
  next
    case False
    def Q1 \<equiv> "{lp p | p. p \<in> Q}"
    from \<open>x \<in> Q\<close> have "lp x \<in> Q1" unfolding Q1_def by auto
    from wf_ord_strict have "wf {(x, y). x \<prec> y}" unfolding wfP_def .
    from wfE_min[OF this \<open>lp x \<in> Q1\<close>] obtain t where
      "t \<in> Q1" and t_min_1: "\<And>y. (y, t) \<in> {(x, y). x \<prec> y} \<Longrightarrow> y \<notin> Q1" by auto
    have t_min: "\<And>q. q \<in> Q \<Longrightarrow> t \<preceq> lp q"
    proof -
      fix q::"('a, 'b) mpoly"
      assume "q \<in> Q"
      hence "lp q \<in> Q1" unfolding Q1_def by auto
      hence "(lp q, t) \<notin> {(x, y). x \<prec> y}" using t_min_1 by auto
      hence "\<not> lp q \<prec> t" by simp
      thus "t \<preceq> lp q" by simp
    qed
    def Q2 \<equiv> "{tail p | p. p \<in> Q \<and> lp p = t}"
    from \<open>t \<in> Q1\<close> obtain p where "lp p = t" and "p \<in> Q" unfolding Q1_def by auto
    hence "tail p \<in> Q2" unfolding Q2_def by auto
    have "\<forall>y\<in>Q2. y = 0 \<or> lp y \<prec> t"
    proof
      fix y::"('a, 'b) mpoly"
      assume "y \<in> Q2"
      from \<open>y \<in> Q2\<close> obtain z where "y = tail z" and "lp z = t" unfolding Q2_def by auto
      have "y \<noteq> 0 \<Longrightarrow> lp y \<prec> t"
      proof -
        assume "y \<noteq> 0"
        hence "tail z \<noteq> 0" using \<open>y = tail z\<close> by simp
        from lp_tail[OF this] \<open>y = tail z\<close> \<open>lp z = t\<close> show "lp y \<prec> t" by simp
      qed
      thus "y = 0 \<or> lp y \<prec> t" by auto
    qed
    from ord_p_wf_aux[OF \<open>tail p \<in> Q2\<close> this] obtain r where "r \<in> Q2" and r_min: "\<forall>q\<in>Q2. \<not> q \<prec>p r"
      by auto
    then obtain m where "m \<in> Q" and "lp m = t" and m_min: "\<And>q. q \<in> Q2 \<Longrightarrow> \<not> q \<prec>p tail m"
      unfolding Q2_def by auto
    show "\<exists>m\<in>Q. \<forall>q. (q, m) \<in> {(x, y). x \<prec>p y} \<longrightarrow> q \<notin> Q"
    proof
      from \<open>m \<in> Q\<close> show "m \<in> Q" .
    next
      show "\<forall>q. (q, m) \<in> {(x, y). x \<prec>p y} \<longrightarrow> q \<notin> Q"
      proof (rule, rule)
        fix q::"('a, 'b) mpoly"
        assume "(q, m) \<in> {(x, y). x\<prec>p y}"
        hence "q \<prec>p m" by simp
        hence "q \<preceq>p m" by simp
        show "q \<notin> Q"
        proof
          assume "q \<in> Q"
          hence "q \<noteq> 0" using False by auto
          from ord_p_lp[OF \<open>q \<preceq>p m\<close> this] t_min[OF \<open>q \<in> Q\<close>] \<open>lp m = t\<close> have "lp q = lp m" by simp
          hence "lp q = t" using \<open>lp m = t\<close> by simp
          hence "tail q \<in> Q2" using \<open>q \<in> Q\<close> unfolding Q2_def by auto
          from ord_p_tail[OF \<open>q \<noteq> 0\<close> \<open>lp q = lp m\<close> \<open>q \<prec>p m\<close>] m_min[OF \<open>tail q \<in> Q2\<close>]
            show False by simp
        qed
      qed
    qed
  qed
qed

lemma mpoly_induct:
  assumes base: "P 0" and ind: "\<And>p. p \<noteq> 0 \<Longrightarrow> P (tail p) \<Longrightarrow> P p"
  shows "P p"
proof (induct rule: wfP_induct[OF ord_p_wf])
  fix p
  assume IH: "\<forall>q. q \<prec>p p \<longrightarrow> P q"
  show "P p"
  proof (cases "p = 0")
    case True
    thus ?thesis using base by simp
  next
    case False
    show ?thesis
    proof (rule ind, fact)
      from IH[rule_format, OF tail_ord_p[OF False]] show "P (tail p)" .
    qed
  qed
qed

end (* ordered_powerprod *)

end (* theory *)