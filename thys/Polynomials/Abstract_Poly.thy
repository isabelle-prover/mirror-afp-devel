(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Type-Class-Multivariate Polynomials\<close>

theory Abstract_Poly
  imports
    Power_Products
    "HOL-Library.Function_Algebras"
begin

text \<open>This theory views \<open>'a \<Rightarrow>\<^sub>0 'b\<close> as multivariate polynomials, where type class constraints on
\<open>'a\<close> ensure that \<open>'a\<close> represents something like monomials.\<close>

lemma mpoly_ext: "p = q" if "\<And>t. coeff p t = coeff q t"
  using that
  by (metis coeff_def mapping_of_inverse poly_mapping_eqI)

lemma coeff_monom:
  "coeff (monom s c) t = (if t = s then c else 0)"
  by (auto simp: coeff_monom)

instantiation poly_mapping :: (type, "{equal, zero}") equal
begin
definition equal_poly_mapping::"('a, 'b) poly_mapping \<Rightarrow> ('a, 'b) poly_mapping \<Rightarrow> bool" where
  "equal_poly_mapping p q \<equiv> (\<forall>t. lookup p t = lookup q t)"

instance by standard (auto simp: equal_poly_mapping_def poly_mapping_eq_iff)

end

subsubsection \<open>Multiplication by Monomials (in type class)\<close>

context comm_powerprod
begin

lemma when_distrib: "f (a when b) = (f a when b)" if "f 0 = 0"
  using that by (auto simp: when_def)

lift_definition monom_mult::"'b::semiring_0 \<Rightarrow> 'a \<Rightarrow> ('a, 'b) poly_mapping \<Rightarrow> ('a, 'b) poly_mapping" is
  "\<lambda>c::'b. \<lambda>t p. (\<lambda>s. (if t adds s then c * (p (s - t)) else 0))"
proof -
  fix c::'b and t::'a and p::"'a \<Rightarrow> 'b"
  have "{s. (if t adds s then c * p (s - t) else 0) \<noteq> 0} \<subseteq> (\<lambda>x. t + x) ` {s. p s \<noteq> 0}"
    (is "?L \<subseteq> ?R")
  proof
    fix x::"'a"
    assume "x \<in> ?L"
    hence "(if t adds x then c * p (x - t) else 0) \<noteq> 0" by simp
    hence "t adds x" and cp_not_zero: "c * p (x - t) \<noteq> 0" by (simp_all split: if_split_asm)
    show "x \<in> ?R"
    proof
      from adds_minus[OF \<open>t adds x\<close>] show "x = t + (x - t)" by (simp add: ac_simps)
    next
      from mult_not_zero[OF cp_not_zero] show "x - t \<in> {t. p t \<noteq> 0}" by (rule, simp)
    qed
  qed
  assume "finite {t. p t \<noteq> 0}"
  hence "finite ?R" by (intro finite_imageI)
  from finite_subset[OF \<open>?L \<subseteq> ?R\<close> this]
  show "finite {s. (if t adds s then c * p (s - t) else 0) \<noteq> 0}" .
qed

lift_definition monom_mult_right::"('a, 'b) poly_mapping \<Rightarrow> 'b::semiring_0 \<Rightarrow> 'a \<Rightarrow> ('a, 'b) poly_mapping" is
  "\<lambda>p. \<lambda>c::'b. \<lambda>t. (\<lambda>s. (if t adds s then (p (s - t)) * c else 0))"
proof -
  fix c::'b and t::'a and p::"'a \<Rightarrow> 'b"
  have "{s. (if t adds s then p (s - t) * c else 0) \<noteq> 0} \<subseteq> (\<lambda>x. t + x) ` {s. p s \<noteq> 0}"
    (is "?L \<subseteq> ?R")
  proof
    fix x::"'a"
    assume "x \<in> ?L"
    hence "(if t adds x then p (x - t) * c else 0) \<noteq> 0" by simp
    hence "t adds x" and cp_not_zero: "p (x - t) * c \<noteq> 0" by (simp_all split: if_split_asm)
    show "x \<in> ?R"
    proof
      from adds_minus[OF \<open>t adds x\<close>] show "x = t + (x - t)" by (simp add: ac_simps)
    next
      from mult_not_zero[OF cp_not_zero] show "x - t \<in> {t. p t \<noteq> 0}" by (rule, simp)
    qed
  qed
  assume "finite {t. p t \<noteq> 0}"
  hence "finite ?R" by (intro finite_imageI)
  from finite_subset[OF \<open>?L \<subseteq> ?R\<close> this]
  show "finite {s. (if t adds s then p (s - t) * c else 0) \<noteq> 0}" .
qed

lemma monom_mult_lookup:
  fixes c::"'b::semiring_0" and t s::"'a" and p::"('a, 'b) poly_mapping"
  shows "lookup (monom_mult c t p) (t + s) = c * lookup p s"
  by (simp add: monom_mult.rep_eq)

lemma monom_mult_right_coeff:
  fixes c::"'b::semiring_0" and t s::"'a" and p::"('a, 'b) poly_mapping"
  shows "lookup (monom_mult_right p c t) (s + t) = lookup p s * c"
  by transfer simp

lemma monom_mult_assoc:
  fixes c d::"'b::semiring_0" and s t::"'a" and p::"('a, 'b) poly_mapping"
  shows "monom_mult c s (monom_mult d t p) = monom_mult (c * d) (s + t) p"
  by transfer (auto simp: algebra_simps adds_def intro!: ext)

lemma monom_mult_right_assoc:
  fixes c d::"'b::semiring_0" and s t::"'a" and p::"('a, 'b) poly_mapping"
  shows "monom_mult_right (monom_mult_right p c s) d t = monom_mult_right p (c * d) (s + t)"
  apply transfer
  apply (auto simp: algebra_simps adds_def  intro!: ext)
  using add.left_commute
  apply auto
  apply (metis add_diff_cancel_left')
  apply blast
  done

lemma monom_mult_uminus_left:
  fixes c::"'b::ring" and t::"'a" and p::"('a, 'b) poly_mapping"
  shows "monom_mult (-c) t p = -(monom_mult c t p)"
by (transfer, auto)

lemma monom_mult_right_uminus_left:
  fixes c::"'b::ring" and t::"'a" and p::"('a, 'b) poly_mapping"
  shows "monom_mult_right (-p) c t = -(monom_mult_right p c t)"
  by (transfer, auto)

lemma monom_mult_uminus_right:
  fixes c::"'b::ring" and t::"'a" and p::"('a, 'b) poly_mapping"
  shows "monom_mult c t (-p) = -(monom_mult c t p)"
  by (transfer, auto)

lemma monom_mult_right_uminus_right:
  fixes c::"'b::ring" and t::"'a" and p::"('a, 'b) poly_mapping"
  shows "monom_mult_right p (-c) t = -(monom_mult_right p c t)"
  by (transfer, auto)

lemma uminus_monom_mult:
  fixes p::"('a, 'b::comm_ring_1) poly_mapping"
  shows "-p = monom_mult (-1) 0 p"
  by transfer (auto simp: )

lemma uminus_monom_mult_right:
  fixes p::"('a, 'b::comm_ring_1) poly_mapping"
  shows "-p = monom_mult_right p (-1) 0"
  by transfer auto

lemma monom_mult_dist_left:
  fixes c d::"'b::semiring_0" and t::"'a" and p::"('a, 'b) poly_mapping"
  shows "monom_mult (c + d) t p = (monom_mult c t p) + (monom_mult d t p)"
  by (transfer, auto simp add: algebra_simps)

lemma monom_mult_right_dist_left:
  fixes c::"'b::semiring_0" and t::"'a" and p q::"('a, 'b) poly_mapping"
  shows "monom_mult_right (p + q) c t = (monom_mult_right p c t) + (monom_mult_right q c t)"
  by (transfer, auto simp add: algebra_simps)

lemma monom_mult_dist_left_minus:
  fixes c d::"'b::ring" and t::"'a" and p::"('a, 'b) poly_mapping"
  shows "monom_mult (c - d) t p = (monom_mult c t p) - (monom_mult d t p)"
  using monom_mult_dist_left[of c "-d" t p] monom_mult_uminus_left[of d t p] by simp

lemma monom_mult_right_dist_left_minus:
  fixes c::"'b::ring" and t::"'a" and p q::"('a, 'b) poly_mapping"
  shows "monom_mult_right (p - q) c t = (monom_mult_right p c t) - (monom_mult_right q c t)"
  using monom_mult_right_dist_left[of p "-q" c t] monom_mult_right_uminus_left[of q c t]
  by simp

lemma monom_mult_dist_right:
  fixes c::"'b::semiring_0" and t::"'a" and p q::"('a, 'b) poly_mapping"
  shows "monom_mult c t (p + q) = (monom_mult c t p) + (monom_mult c t q)"
  by (transfer, auto simp add: algebra_simps)

lemma monom_mult_right_dist_right:
  fixes c d::"'b::semiring_0" and t::"'a" and p::"('a, 'b) poly_mapping"
  shows "monom_mult_right p (c + d) t = (monom_mult_right p c t) + (monom_mult_right p d t)"
  by (transfer, auto simp add: algebra_simps)

lemma monom_mult_dist_right_minus:
  fixes c::"'b::ring" and t::"'a" and p q::"('a, 'b) poly_mapping"
  shows "monom_mult c t (p - q) = (monom_mult c t p) - (monom_mult c t q)"
  using monom_mult_dist_right[of c t p "-q"] monom_mult_uminus_right[of c t q]
  by simp

lemma monom_mult_right_dist_right_minus:
  fixes c d::"'b::ring" and t::"'a" and p::"('a, 'b) poly_mapping"
  shows "monom_mult_right p (c - d) t = (monom_mult_right p c t) - (monom_mult_right p d t)"
  using monom_mult_right_dist_right[of p c "-d" t] monom_mult_right_uminus_right[of p d t] by simp

lemma monom_mult_left0:
  fixes t::"'a" and p::"('a, 'b::semiring_0) poly_mapping"
  shows "monom_mult 0 t p = 0"
  by (transfer, auto)

lemma monom_mult_right_left0:
  fixes c::"'b::semiring_0" and t::"'a"
  shows "monom_mult_right 0 c t = 0"
  by (transfer, auto)

lemma monom_mult_right0:
  fixes c::"'b::semiring_0" and t::"'a"
  shows "monom_mult c t 0 = 0"
  by (transfer, auto)

lemma monom_mult_right_right0:
  fixes t::"'a" and p::"('a, 'b::semiring_0) poly_mapping"
  shows "monom_mult_right p 0 t = 0"
  by (transfer, auto)

lemma monom_mult_left1:
  fixes p::"('a, 'b::semiring_1) poly_mapping"
  shows "(monom_mult 1 0 p) = p"
  by (transfer, auto)

lemma monom_mult_right_right1:
  fixes p::"('a, 'b::semiring_1) poly_mapping"
  shows "(monom_mult_right p 1 0) = p"
  by (transfer, auto)

lemma monom_mult_monom:
  fixes c d::"'b::semiring_0" and s t::"'a"
  shows "monom_mult c s (PP_Poly_Mapping.single t d) = PP_Poly_Mapping.single (s + t) (c * d)"
proof (transfer)
  fix c::'b and s::'a and t d sa
  have "\<forall>k. l \<noteq> s + k \<Longrightarrow> (c * d when s + t = l) = 0" for l
    by (metis (mono_tags, lifting) zero_class.when(2))
  then show " (\<lambda>sa. if s adds sa then c * (d when t = sa - s) else 0) = (\<lambda>k'. c * d when s + t = k')"
    by (force simp: when_def adds_def mult_when)
qed

lemma monom_mult_right_monom:
  fixes c d::"'b::semiring_0" and s t::"'a"
  shows "monom_mult_right (PP_Poly_Mapping.single s c) d t = PP_Poly_Mapping.single  (s + t) (c * d)"
proof (transfer)
  fix s::'a and c::'b and d t
  have "(c * d when s = k) = (c * d when s + t = t + k)" for k
    by (metis (full_types) add_commute local.add_implies_diff zero_class.when_simps(1))
  moreover have "\<forall>k. l \<noteq> t + k \<Longrightarrow> (c * d when s + t = l) = 0" for l
    by (metis (mono_tags, lifting) add_commute zero_class.when_simps(2))
  ultimately
  show "(\<lambda>sa. if t adds sa then (c when s = sa - t) * d else 0) = (\<lambda>k'. c * d when s + t = k')"
    by (auto simp: when_def adds_def when_mult mult_when intro!: ext)
qed

lemma monom_mult_left_monom_monom_mult_right:
  fixes c d::"'b::semiring_0" and s t::"'a"
  shows "monom_mult c s (PP_Poly_Mapping.single t d) = monom_mult_right (PP_Poly_Mapping.single s c) d t"
  using monom_mult_monom[of c s] monom_mult_right_monom[of s c] by simp

lemma monom_mult_left_monom_mult_right:
  fixes c::"'b::comm_semiring_0" and t::"'a" and p::"('a, 'b) poly_mapping"
  shows "monom_mult c t p = monom_mult_right p c t"
  by (transfer) (auto simp: ac_simps)

lemma monom_mult_left_monom:
  fixes c d::"'b::comm_semiring_0" and s t::"'a"
  shows "monom_mult c s (PP_Poly_Mapping.single t d) = monom_mult d t (PP_Poly_Mapping.single s c)"
  using monom_mult_left_monom_mult_right[of d t] monom_mult_left_monom_monom_mult_right by simp

lemma monom_mult_right_monom':
  fixes c d::"'b::comm_semiring_0" and s t::"'a"
  shows "monom_mult_right (PP_Poly_Mapping.single s c) d t = monom_mult_right (PP_Poly_Mapping.single t d) c s"
  using monom_mult_left_monom_mult_right[of d t] monom_mult_left_monom_monom_mult_right[of d t]
  by simp


subsubsection \<open>Polynomial Ideals\<close>

text \<open>We now introduce polynomial ideals. Actually, we only consider left-ideals here (i.\,e.
  cofactors may only be multiplied from the left).\<close>

text \<open>According to the definition of @{term pideal}, @{term pideal} must be closed only under
  multiplication by monomials. After introducing general multiplication @{term pideal} is shown to
  be closed under multiplication by arbitrary polynomials as well (in lemma
  @{text pideal_closed_times}), making it really an ideal.\<close>

inductive_set pideal::"('a, 'b::semiring_0) poly_mapping set \<Rightarrow> ('a, 'b) poly_mapping set"
for bs::"('a, 'b) poly_mapping set" where
  pideal_0: "0 \<in> (pideal bs)"|
  pideal_plus: "a \<in> (pideal bs) \<Longrightarrow> b \<in> bs \<Longrightarrow> a + monom_mult c t b \<in> (pideal bs)"

lemma monom_mult_in_pideal:
  fixes bs::"('a, 'b::semiring_0) poly_mapping set"
  assumes "b \<in> bs"
  shows "monom_mult c t b \<in> pideal bs"
proof -
  have "0 + monom_mult c t b \<in> pideal bs" by (rule pideal_plus, rule pideal_0, fact)
  thus ?thesis by simp
qed

lemma generator_subset_pideal:
  fixes bs::"('a, 'b::semiring_1) poly_mapping set"
  shows "bs \<subseteq> pideal bs"
proof
  fix b
  assume b_in: "b \<in> bs"
  from monom_mult_left1[of b] monom_mult_in_pideal[OF b_in, of 1 0] show "b \<in> pideal bs"
    by simp
qed

lemma pideal_closed_plus:
  fixes bs::"('a, 'b::semiring_0) poly_mapping set"
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
    by (metis ab_semigroup_add_class.add.commute semigroup_add_class.add.assoc)
qed

lemma pideal_closed_uminus:
  fixes bs::"('a, 'b::ring) poly_mapping set"
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
  fixes bs::"('a, 'b::ring) poly_mapping set"
  assumes "p \<in> pideal bs" and "q \<in> pideal bs"
  shows "p - q \<in> pideal bs"
  using assms pideal_closed_plus pideal_closed_uminus by fastforce

lemma pideal_closed_monom_mult:
  fixes bs::"('a, 'b::ring) poly_mapping set"
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
  fixes bs::"('a, 'b::ring) poly_mapping set"
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
  fixes bs::"('a, 'b::ring) poly_mapping set"
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
  fixes bs::"('a, 'b::ring) poly_mapping set"
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

end

subsection \<open>Multiplication\<close>

lift_definition except::
  "('a, 'b::zero)poly_mapping \<Rightarrow> 'a \<Rightarrow> ('a, 'b::zero) poly_mapping" is
  "\<lambda>p s t. if t = (s::'a) then (0::'b) else p t"
proof -
  fix p::"'a \<Rightarrow> 'b" and s::'a
  assume "finite {t. p t \<noteq> 0}"
  show "finite {t. (if t = s then 0 else p t) \<noteq> 0}"
  proof (rule finite_subset[of _ "{t. p t \<noteq> 0}"], rule)
    fix u
    assume "u \<in> {t. (if t = s then 0 else p t) \<noteq> 0}"
    hence "(if u = s then 0 else p u) \<noteq> 0" by simp
    hence "p u \<noteq> 0" by meson
    thus "u \<in> {t. p t \<noteq> 0}" by simp
  qed (fact)
qed

lemma lookup_except: "lookup (except p s) m = (if m = s then 0 else lookup p m)"
  by (auto simp: except.rep_eq except.rep_eq)

lemma lookup_except1: "lookup (except p t) t = 0"
  by (simp add: lookup_except)

lemma lookup_except2:
  assumes "s \<noteq> t"
  shows "lookup (except p t) s = lookup p s"
  using assms by (simp add: lookup_except)

text \<open>@{term "some_term p"} shall only return @{emph \<open>some\<close>} term appearing in @{term p} with
  non-zero lookupicient (not necessarily the biggest one w.r.t. a certain ordering). However, if we
  use something like @{term "SOME t. t \<in> keys p"} instead, multiplication cannot be made executable.\<close>

definition some_term::"('a::{comm_powerprod,linorder}, 'b::zero) poly_mapping \<Rightarrow> 'a"
  where "some_term p \<equiv> (if p = 0 then 0 else Max (keys p))"
definition rest_mpoly::"('a::{comm_powerprod,linorder}, 'b::zero) poly_mapping \<Rightarrow> ('a, 'b) poly_mapping"
  where "rest_mpoly p \<equiv> except p (some_term p)"

lemma keys_eq_empty_iff[simp]: "keys p = {} \<longleftrightarrow> p = 0"
  by (metis keys_zero lookup_zero not_in_keys_iff_lookup_eq_zero poly_mapping_eqI)

lemma some_term_nonzero:
  assumes "p \<noteq> 0"
  shows "some_term p \<in> keys p"
proof -
  from assms have "keys p \<noteq> {}" using assms by auto
  from Max_in[OF finite_keys[of p] this] assms show ?thesis unfolding some_term_def by simp
qed

lemma lookup_some_term:
  assumes "p \<noteq> 0"
  shows "lookup p (some_term p) \<noteq> 0"
  by (simp add: assms some_term_nonzero)

lemma lookup_rest_some_term:
  "lookup (rest_mpoly p) (some_term p) = 0"
  by (simp add: lookup_except1 rest_mpoly_def)

lemma lookup_rest:
  assumes "t \<noteq> some_term p"
  shows "lookup (rest_mpoly p) t = lookup p t"
  by (simp add: assms lookup_except2 rest_mpoly_def)

lemma rest_zero: "rest_mpoly 0 = 0"
  by (metis lookup_except lookup_some_term rest_mpoly_def zero_poly_mapping.rep_eq)

lemma keys_rest:
  shows "keys (rest_mpoly p) = (keys p) - {some_term p}"
proof
  show "keys (rest_mpoly p) \<subseteq> keys p - {some_term p}"
  proof (rule)
    fix x
    assume "x \<in> keys (rest_mpoly p)"
    from this have cr: "lookup (rest_mpoly p) x \<noteq> 0"
      by auto
    from this lookup_rest_some_term have "x \<noteq> some_term p" using cr by force
    from cr lookup_rest[OF this] have "lookup p x \<noteq> 0" by simp
    show "x \<in> keys p - {some_term p}"
    proof
      from \<open>lookup p x \<noteq> 0\<close> show "x \<in> keys p" by simp
    next
      from \<open>x \<noteq> some_term p\<close> show "x \<notin> {some_term p}" by simp
    qed
  qed
next
  show "keys p - {some_term p} \<subseteq> keys (rest_mpoly p)"
  proof (rule)
    fix x
    assume "x \<in> keys p - {some_term p}"
    hence x1: "x \<in> keys p" and x2: "x \<notin> {some_term p}" by simp_all
    from x1 have cp: "lookup p x \<noteq> 0" by simp
    moreover from x2 have "x \<noteq> some_term p" by simp
    from lookup_rest[OF this] cp show "x \<in> keys (rest_mpoly p)"
      apply (auto)
      using in_keys_iff by fastforce
  qed
qed

lemma keys_rest_insert:
  assumes "p \<noteq> 0"
  shows "keys p = insert (some_term p) (keys (rest_mpoly p))"
by (simp add: keys_rest insert_absorb[OF some_term_nonzero[OF assms]])

lemma keys_rest_subset:
  assumes "p \<noteq> 0"
  shows "keys (rest_mpoly p) \<subset> keys p"
proof (simp only: keys_rest, rule, rule Diff_subset, rule)
  assume "keys p - {some_term p} = keys p"
  hence "keys p \<subseteq> keys p - {some_term p}" by simp
  hence "\<And>t. t \<in> keys p \<Longrightarrow> t \<in> (keys p - {some_term p})" by auto
  from this[OF some_term_nonzero[OF assms]] have "some_term p \<notin> {some_term p}" by simp
  thus False by simp
qed

lemma keys_subset_wf:
  "wfP (\<lambda>p q::('a, 'b::zero) poly_mapping. keys p \<subset> keys q)"
unfolding wfP_def
proof (intro wfI_min)
  fix x::"('a, 'b) poly_mapping" and Q
  assume x_in: "x \<in> Q"
  let ?Q0 = "card ` keys ` Q"
  from x_in have "card (keys x) \<in> ?Q0" by simp
  from wfE_min[OF wf this] obtain z0
    where z0_in: "z0 \<in> ?Q0" and z0_min: "\<And>y. (y, z0) \<in> {(x, y). x < y} \<Longrightarrow> y \<notin> ?Q0" by auto
  from z0_in obtain z where z0_def: "z0 = card (keys z)" and "z \<in> Q" by auto
  show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> {(p, q). keys p \<subset> keys q} \<longrightarrow> y \<notin> Q"
  proof (intro bexI[of _ z], rule, rule)
    fix y::"('a, 'b) poly_mapping"
    let ?y0 = "card (keys y)"
    assume "(y, z) \<in> {(p, q). keys p \<subset> keys q}"
    hence "keys y \<subset> keys z" by simp
    hence "?y0 < z0" unfolding z0_def by (simp add: finite_keys psubset_card_mono) 
    hence "(?y0, z0) \<in> {(x, y). x < y}" by simp
    from z0_min[OF this] show "y \<notin> Q" by auto
  qed (fact)
qed

lemma mpoly_keys_induct:
  assumes base: "P 0" and ind: "\<And>p. p \<noteq> 0 \<Longrightarrow> P (rest_mpoly p) \<Longrightarrow> P p"
  shows "P p"
proof (induct rule: wfP_induct[OF keys_subset_wf])
  fix p::"('a, 'b) poly_mapping"
  assume IH: "\<forall>q. keys q \<subset> keys p \<longrightarrow> P q"
  show "P p"
  proof (cases "p = 0")
    case True
    thus ?thesis using base by simp
  next
    case False
    show ?thesis
    proof (rule ind, fact)
      from IH[rule_format, OF keys_rest_subset[OF False]] show "P (rest_mpoly p)" .
    qed
  qed
qed

lemma some_term_monom:
  assumes "c \<noteq> (0::'b::zero)"
  shows "some_term (PP_Poly_Mapping.single t c) = t"
  by (metis assms lookup_single_eq lookup_single_not_eq lookup_some_term)

lemma lookup_some_term_monom:
  assumes "c \<noteq> (0::'b::zero)"
  shows "lookup (PP_Poly_Mapping.single t c) (some_term (PP_Poly_Mapping.single t c)) = c"
  by (simp add: assms some_term_monom)

lemma rest_monom:
  "rest_mpoly (PP_Poly_Mapping.single t c) = (0::('a::{linorder,comm_powerprod}, 'b::zero) poly_mapping)"
  by (metis (no_types, hide_lams) lookup_except1 lookup_rest lookup_single_not_eq lookup_some_term rest_mpoly_def)

lemma some_monomial_rest:
  fixes p::"('a::{comm_powerprod,linorder}, 'b::comm_monoid_add) poly_mapping"
  assumes "p \<noteq> 0"
  shows "p = PP_Poly_Mapping.single (some_term p) (lookup p (some_term p)) + rest_mpoly p"
  by (auto simp: lookup_add lookup_single when_def lookup_rest_some_term lookup_rest
      intro!: poly_mapping_eqI)

function times_poly_mapping_class::"('a::{linorder,comm_powerprod}, 'b::semiring_0) poly_mapping \<Rightarrow> ('a, 'b) poly_mapping \<Rightarrow> ('a, 'b) poly_mapping"
  (infixl "*pm" 70)
  where
  "times_poly_mapping_class p q =
    (if p = 0 then
      0
    else
      monom_mult (lookup p (some_term p)) (some_term p) q + times_poly_mapping_class (rest_mpoly p) q
    )"
by auto
termination proof -
  let ?r = "{(x, y::('a, 'b) poly_mapping). keys x \<subset> keys y} <*lex*> {}"
  show ?thesis
  proof
    show "wf ?r"
    proof
      from keys_subset_wf show "wf {(x, y::('a, 'b) poly_mapping). keys x \<subset> keys y}" unfolding wfP_def .
    qed (simp)
  next
    fix p q::"('a, 'b) poly_mapping"
    assume "p \<noteq> 0"
    from keys_rest_subset[OF this] show "((rest_mpoly p, q), (p, q)) \<in> ?r" by simp
  qed
qed

text \<open>@{const times_poly_mapping_class} was used in Maletzky's original formalization,
  but it is equivalent to the definition of @{term "op *"} on poly mapping, see below...\<close>

lemma times_mpoly_induct:
  assumes base: "P 0 q 0"
  assumes ind: "\<And>p. p \<noteq> 0 \<Longrightarrow> P (rest_mpoly p) q (times_poly_mapping_class (rest_mpoly p) q) \<Longrightarrow>
                  P p q (monom_mult (lookup p (some_term p)) (some_term p) q + times_poly_mapping_class (rest_mpoly p) q)"
  shows "P p q (times_poly_mapping_class p q)"
proof (rule times_poly_mapping_class.induct[of "\<lambda>x _. P x q (times_poly_mapping_class x q)"])
  fix p qa
  assume IH: "p \<noteq> 0 \<Longrightarrow> P (rest_mpoly p) q (times_poly_mapping_class (rest_mpoly p) q)"
  show "P p q (times_poly_mapping_class p q)"
  proof (cases "p = 0")
    case True
    from True base show ?thesis by simp
  next
    case False
    have "P p q (monom_mult (lookup p (some_term p)) (some_term p) q + times_poly_mapping_class (rest_mpoly p) q)"
      by (rule ind, fact, rule IH, fact)
    thus ?thesis using False
      by simp
  qed
qed

lemma times_mpoly_left0: "times_poly_mapping_class 0 p = 0"
  by simp

lemma times_mpoly_right0:
  shows "times_poly_mapping_class p 0 = 0"
proof (induct rule: times_mpoly_induct)
  fix p::"'a \<Rightarrow>\<^sub>0 'b"
  assume "times_poly_mapping_class (rest_mpoly p) 0 = 0"
  thus "monom_mult (lookup p (some_term p)) (some_term p) 0 + rest_mpoly p *pm 0 = 0"
    using monom_mult_right0 by simp
qed (simp)

lemma monom_0I:
  fixes c::"'b::zero" and t::"'a"
  assumes "c = 0"
  shows "PP_Poly_Mapping.single t c = 0"
  using assms
  by transfer (auto)

lemma monom_0D:
  fixes c::"'b::zero" and t::"'a"
  assumes "PP_Poly_Mapping.single t c = 0"
  shows "c = 0"
  using assms
  by transfer (auto simp: fun_eq_iff when_def; meson)

lemma times_mpoly_left_monom:
  shows "(PP_Poly_Mapping.single c t) *pm p = monom_mult t c p"
proof (cases "t = 0")
  case True
  show ?thesis unfolding True
    by (simp add: monom_mult_left0)
next
  case False
  have "PP_Poly_Mapping.single c t \<noteq> 0"
  proof
    assume "PP_Poly_Mapping.single c t = 0"
    from False monom_0D[OF this] show False ..
  qed
  from this some_term_monom[OF False, of c] lookup_some_term_monom[OF False, of c] rest_monom[of c t]
  show ?thesis by simp
qed

lemma times_mpoly_right_monom:
  shows "p *pm (PP_Poly_Mapping.single t c) = monom_mult_right p c t"
proof (induct rule: times_mpoly_induct[of _ "PP_Poly_Mapping.single t c" p])
  from monom_mult_right_left0 show "0 = monom_mult_right 0 c t" by simp
next
  fix p
  assume "p \<noteq> 0" and IH: "rest_mpoly p *pm PP_Poly_Mapping.single t c = monom_mult_right (rest_mpoly p) c t"
  from IH some_monomial_rest[OF \<open>p \<noteq> 0\<close>]
       monom_mult_left_monom_monom_mult_right[of "lookup p (some_term p)" "some_term p" t c]
       monom_mult_right_dist_left[of "PP_Poly_Mapping.single (some_term p)  (lookup p (some_term p))" "rest_mpoly p" c t]
  show "monom_mult (lookup p (some_term p)) (some_term p) (PP_Poly_Mapping.single t c) +
         rest_mpoly p *pm PP_Poly_Mapping.single t c =
         monom_mult_right p c t" by simp
qed

lemma times_mpoly_dist_left:
  fixes p q r::"('a::{linorder,comm_powerprod}, 'b::semiring_0) poly_mapping"
  shows "p *pm (q + r) = p *pm q + p *pm r"
proof (rule times_mpoly_induct[of "\<lambda>x _ _. x *pm (q + r) = x *pm q + x *pm r"])
  from times_mpoly_left0 show "0 *pm (q + r) = 0 *pm q + 0 *pm r" by simp
next
  fix p
  assume "p \<noteq> 0" and IH: "rest_mpoly p *pm (q + r) = rest_mpoly p *pm q + rest_mpoly p *pm r"
  let ?c = "lookup p (some_term p)"
  let ?t = "some_term p"
  from \<open>p \<noteq> 0\<close> have "p *pm (q + r) = (monom_mult ?c ?t (q + r)) + (rest_mpoly p) *pm (q + r)" by simp
  also have "\<dots> = (monom_mult ?c ?t q) + (monom_mult ?c ?t r) + (rest_mpoly p) *pm (q + r)"
    using monom_mult_dist_right[of ?c ?t q r] by simp
  also have "\<dots> = ((monom_mult ?c ?t q) + (monom_mult ?c ?t r)) + ((rest_mpoly p) *pm q + (rest_mpoly p) *pm r)"
    using IH by (simp)
  also have "\<dots> = ((monom_mult ?c ?t q) + (rest_mpoly p) *pm q) + ((monom_mult ?c ?t r) + (rest_mpoly p) *pm r)"
    by (simp only: ac_simps)
  also have "\<dots> = p *pm q + p *pm r" using \<open>p \<noteq> 0\<close> times_poly_mapping_class.simps[of p] by simp
  finally show "p *pm (q + r) = p *pm q + p *pm r" .
qed

lemma times_mpoly_dist_right:
  fixes p q r::"('a::{linorder,comm_powerprod}, 'b::semiring_0) poly_mapping"
  shows "(p + q) *pm r = p *pm r + q *pm r"
proof (induct rule: times_mpoly_induct[of _ "p + q" r])
  show "(p + q) *pm 0 = p *pm 0 + q *pm 0"
    unfolding times_mpoly_right0 by simp
next
  fix r
  assume "r \<noteq> 0" and IH: "(p + q) *pm (rest_mpoly r) = p *pm rest_mpoly r + q *pm rest_mpoly r"
  let ?c = "lookup r (some_term r)"
  let ?t = "some_term r"
  let ?r = "rest_mpoly r"
  from some_monomial_rest[OF \<open>r \<noteq> 0\<close>] have "(p + q) *pm r = (p + q) *pm (PP_Poly_Mapping.single ?t ?c + ?r)" by simp
  also have "\<dots> = (p + q) *pm (PP_Poly_Mapping.single ?t ?c) + (p + q) *pm ?r"
    unfolding times_mpoly_dist_left by simp
  also have "\<dots> = (p + q) *pm (PP_Poly_Mapping.single ?t ?c) + (p *pm ?r + q *pm ?r)"
    unfolding IH ..
  also have "\<dots> = monom_mult_right (p + q) ?c ?t + (p *pm ?r + q *pm ?r)"
    unfolding times_mpoly_right_monom ..
  also have "\<dots> = (monom_mult_right p ?c ?t + monom_mult_right q ?c ?t) + (p *pm ?r + q *pm ?r)"
    by (simp only: monom_mult_right_dist_left)
  also have "\<dots> = (p *pm (PP_Poly_Mapping.single ?t ?c) + q *pm (PP_Poly_Mapping.single ?t ?c)) + (p *pm ?r + q *pm ?r)"
    unfolding times_mpoly_right_monom ..
  also have "\<dots> = (p *pm (PP_Poly_Mapping.single ?t ?c) + p *pm ?r) + (q *pm (PP_Poly_Mapping.single ?t ?c) + q *pm ?r)"
    by (simp only: ac_simps)
  also have "\<dots> = (p *pm (PP_Poly_Mapping.single ?t ?c + ?r)) + (q *pm (PP_Poly_Mapping.single ?t ?c + ?r))"
    unfolding times_mpoly_dist_left ..
  also have "\<dots> = p *pm r + q *pm r" using some_monomial_rest[OF \<open>r \<noteq> 0\<close>] by simp
  finally show "(p + q) *pm r = p *pm r + q *pm r" .
qed

lemma times_mpoly_assoc_monom_mult:
  fixes c::"'b::semiring_0" and t::"'a::{linorder,comm_powerprod}" and p q::"('a, 'b) poly_mapping"
  shows "(monom_mult c t p) *pm q = monom_mult c t (p *pm q)"
proof (induct rule: times_mpoly_induct[of "\<lambda>x y _. (monom_mult c t x) *pm y = monom_mult c t (x *pm y)"])
  from times_mpoly_left0 monom_mult_right0[of c t] show "monom_mult c t 0 *pm q = monom_mult c t (0 *pm q)"
    by simp
next
  fix p::"('a, 'b) poly_mapping"
  let ?c = "lookup p (some_term p)"
  let ?t = "some_term p"
  let ?r = "rest_mpoly p"
  assume "p \<noteq> 0" and IH: "monom_mult c t ?r *pm q = monom_mult c t (?r *pm q)"
  
  have "monom_mult c t p = monom_mult c t ((PP_Poly_Mapping.single ?t ?c) + ?r)"
    using some_monomial_rest[OF \<open>p \<noteq> 0\<close>] by simp
  also have "\<dots> = monom_mult c t (PP_Poly_Mapping.single ?t ?c) + monom_mult c t ?r"
    using monom_mult_dist_right[of c t] by simp
  finally have eq: "monom_mult c t p = monom_mult c t (PP_Poly_Mapping.single ?t ?c) + monom_mult c t ?r" .
  
  have "monom_mult c t p *pm q = (monom_mult c t (PP_Poly_Mapping.single ?t ?c) + monom_mult c t ?r) *pm q"
    by (simp only: eq)
  also have "\<dots> = (monom_mult c t (PP_Poly_Mapping.single ?t ?c)) *pm q + (monom_mult c t ?r) *pm q"
    by (simp only: times_mpoly_dist_right)
  also have "\<dots> = (monom_mult c t (PP_Poly_Mapping.single ?t ?c)) *pm q + monom_mult c t (?r *pm q)"
    by (simp only: IH)
  also have "\<dots> = (PP_Poly_Mapping.single (t + ?t) (c * ?c)) *pm q + monom_mult c t (?r *pm q)"
    by (simp only: monom_mult_monom)
  also have "\<dots> = monom_mult (c * ?c) (t + ?t) q + monom_mult c t (?r *pm q)"
    by (simp only: times_mpoly_left_monom)
  also have "\<dots> = monom_mult c t (monom_mult ?c ?t q) + monom_mult c t (?r *pm q)"
    by (simp only: monom_mult_assoc)
  also have "\<dots> = monom_mult c t ((monom_mult ?c ?t q) + ?r *pm q)"
    by (simp only: monom_mult_dist_right)
  also have "\<dots> = monom_mult c t ((PP_Poly_Mapping.single ?t ?c) *pm q + ?r *pm q)"
    by (simp only: times_mpoly_left_monom)
  also have "\<dots> = monom_mult c t (((PP_Poly_Mapping.single ?t ?c) + ?r) *pm q)"
    by (simp only: times_mpoly_dist_right)
  also have "\<dots> = monom_mult c t (p *pm q)"
    using some_monomial_rest[OF \<open>p \<noteq> 0\<close>] by simp
  finally show "monom_mult c t p *pm q = monom_mult c t (p *pm q)" .
qed

lemma times_mpoly_assoc:
  fixes p q r::"('a::{linorder,comm_powerprod}, 'b::semiring_0) poly_mapping"
  shows "(p *pm q) *pm r = p *pm (q *pm r)"
proof (induct rule: times_mpoly_induct)
  from times_mpoly_left0 show "(0 *pm q) *pm r = 0" by simp
next
  fix p::"('a, 'b) poly_mapping"
  let ?c = "lookup p (some_term p)"
  let ?t = "some_term p"
  let ?r = "rest_mpoly p"
  assume "p \<noteq> 0" and IH: "(?r *pm q) *pm r = ?r *pm (q *pm r)"
  from \<open>p \<noteq> 0\<close> have "(p *pm q) *pm r = (monom_mult ?c ?t q + ?r *pm q) *pm r" by simp
  also have "\<dots> = ((monom_mult ?c ?t q) *pm r) + (?r *pm q) *pm r"
    unfolding times_mpoly_dist_right ..
  also have "\<dots> = ((monom_mult ?c ?t q) *pm r) + ?r *pm (q *pm r)"
    unfolding IH ..
  also have "\<dots> = monom_mult ?c ?t (q *pm r) + ?r *pm (q *pm r)"
    unfolding times_mpoly_assoc_monom_mult ..
  finally show "(p *pm q) *pm r = monom_mult ?c ?t (q *pm r) + ?r *pm (q *pm r)" .
qed

lemma monom_mult_add_distrib: "monom_mult a x q + b * q = (PP_Poly_Mapping.single x a + b) * q"
  for p q::"('a::{linorder,comm_powerprod}, 'b::semiring_0) poly_mapping"
proof (induction q rule: poly_mapping_induct)
  case (single k v)
  then show ?case by (metis distrib_right monom_mult_monom mult_single)
next
  case (sum f g k v)
  then show ?case
  proof -
    have "b * (f + g) = b * f + b * PP_Poly_Mapping.single k v"
      by (metis distrib_left sum.hyps(1))
    then have f1: "monom_mult a x (f + g) + b * (f + g) =
        b * f + b * PP_Poly_Mapping.single k v + (monom_mult a x f + monom_mult a x g)"
      by (metis add.commute monom_mult_dist_right)
    have "b * f + b * PP_Poly_Mapping.single k v + monom_mult a x g =
        b * f + (PP_Poly_Mapping.single x a + b) * g"
      by (metis add.commute add.left_commute sum.IH(2) sum.hyps(1))
    then have "b * f + b * PP_Poly_Mapping.single k v + monom_mult a x g =
        (PP_Poly_Mapping.single x a + b) * g + b * f"
      by (metis add.commute)
    then have "monom_mult a x (f + g) + b * (f + g) =
        monom_mult a x f + ((PP_Poly_Mapping.single x a + b) * g + b * f)"
      by (metis add.left_commute f1)
    then have "monom_mult a x (f + g) + b * (f + g) =
        (PP_Poly_Mapping.single x a + b) * g + (PP_Poly_Mapping.single x a + b) * f"
      by (metis ab_semigroup_add_class.add_ac(1) add.commute sum.IH(1))
    then show ?thesis
      by (metis add.commute distrib_left)
  qed
qed

lemma times_poly_mapping_eq_times[simp]: "p *pm q = p * q"
  by (induction p q rule: times_mpoly_induct)
    (auto split: if_splits simp: monom_mult_add_distrib some_monomial_rest[symmetric]
      simp del: times_poly_mapping_class.simps)

text \<open>the lifted version is times on type mpoly...\<close>

lift_definition times_mpoly_class::"('b::semiring_0) mpoly \<Rightarrow> ('b) mpoly \<Rightarrow> ('b) mpoly"
  (infixl "*mp" 70)
  is "(op *pm)::((nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> _ \<Rightarrow> _" .

lemma times_mpoly_class_eq_times[simp]: "p *mp q = p * q" for p q::"('b::semiring_0) mpoly"
  apply transfer
  subgoal for p q
    by (induction p q rule: times_mpoly_induct)
      (auto split: if_splits simp: monom_mult_add_distrib some_monomial_rest[symmetric]
        simp del: times_poly_mapping_class.simps)
  done


subsection \<open>Polynomials in Ordered Power-products\<close>

context ordered_powerprod
begin

subsubsection \<open>Leading Power-Product, Leading Coefficient, and Tail\<close>

lift_definition higher::"('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)" is
  "(\<lambda>p t. (\<lambda>s. (if t \<prec> s then p s else 0)))"
proof -
  fix p::"'a \<Rightarrow> 'b" and t::"'a"
  assume fin: "finite {t. p t \<noteq> 0}"
  have "{s. (if t \<prec> s then p s else 0) \<noteq> 0} \<subseteq> {t. p t \<noteq> 0}"
  proof
    fix s::"'a"
    assume "s \<in> {x. (if t \<prec> x then p x else 0) \<noteq> 0}"
    hence "(if t \<prec> s then p s else 0) \<noteq> 0" by simp
    hence "p s \<noteq> 0" by (simp split: if_split_asm)
    thus "s \<in> {t. p t \<noteq> 0}" by simp
  qed
  from finite_subset[OF this fin] show "finite {s. (if t \<prec> s then p s else 0) \<noteq> 0}" .
qed

lift_definition lower::"('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)" is
  "(\<lambda>p t. (\<lambda>s. (if s \<prec> t then p s else 0)))"
proof -
  fix p::"'a \<Rightarrow> 'b" and t::"'a"
  assume fin: "finite {t. p t \<noteq> 0}"
  have "{s. (if s \<prec> t then p s else 0) \<noteq> 0} \<subseteq> {t. p t \<noteq> 0}"
  proof
    fix s::"'a"
    assume "s \<in> {x. (if x \<prec> t then p x else 0) \<noteq> 0}"
    hence "(if s \<prec> t then p s else 0) \<noteq> 0" by simp
    hence "p s \<noteq> 0" by (simp split: if_split_asm)
    thus "s \<in> {t. p t \<noteq> 0}" by simp
  qed
  from finite_subset[OF this fin] show "finite {s. (if s \<prec> t then p s else 0) \<noteq> 0}" .
qed

definition lp::"('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 'a" where
  "lp p \<equiv> (if p = 0 then 0 else ordered_powerprod_lin.Max (keys p))"
definition lc::"('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 'b" where
  "lc p \<equiv> PP_Poly_Mapping.lookup p (lp p)"
definition tail::"('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)" where
  "tail p \<equiv> lower p (lp p)"

lemma higher_plus:
  fixes p q::"('a, 'b::ring) poly_mapping"
  shows "higher (p + q) t = higher p t + higher q t"
proof transfer
  fix p q::"'a \<Rightarrow> 'b" and t::"'a"
  show "(\<lambda>s. if t \<prec> s then p s + q s else 0) =
        (\<lambda>s. (if t \<prec> s then p s else 0) + (if t \<prec> s then q s else 0))" by (rule, simp)
qed

lemma higher_uminus:
  fixes p::"('a, 'b::ring) poly_mapping"
  shows "higher (-p) t = -(higher p t)"
  by transfer auto

lemma higher_minus:
  fixes p q::"('a, 'b::ring) poly_mapping"
  shows "higher (p - q) t = higher p t - higher q t"
  by (auto intro!: poly_mapping_eqI simp: lookup_minus higher.rep_eq)

lemma higher_0:
  shows "higher 0 t = 0"
proof transfer
  fix t::"'a"
  show "(\<lambda>s. if t \<prec> s then 0 else 0) = (\<lambda>_. 0)" by simp
qed

lemma higher_equal:
  shows "higher p t = higher q t \<longleftrightarrow> (\<forall>s. t \<prec> s \<longrightarrow> lookup p s = lookup q s)"
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
  shows "higher p t = 0 \<longleftrightarrow> (\<forall>s. t \<prec> s \<longrightarrow> lookup p s = 0)"
proof -
  from higher_equal[of p t 0] higher_0[of t, symmetric]
  have "higher p t = 0 \<longleftrightarrow> (\<forall>s. t \<prec> s \<longrightarrow> lookup p s = lookup 0 s)" by auto
  moreover have "\<dots> \<longleftrightarrow> (\<forall>s. t \<prec> s \<longrightarrow> lookup p s = 0)" using lookup_zero by auto
  ultimately show ?thesis by simp
qed

lemma lp_alt:
  assumes "p \<noteq> 0"
  shows "lp p = ordered_powerprod_lin.Max (keys p)"
using assms unfolding lp_def by simp

lemma lp_max:
  assumes "lookup p t \<noteq> 0"
  shows "t \<preceq> lp p"
proof -
  from assms have t_in: "t \<in> keys p" by simp
  hence "keys p \<noteq> {}" by auto
  hence "p \<noteq> 0" using keys_zero by blast
  from lp_alt[OF this] ordered_powerprod_lin.Max_ge[OF finite_keys t_in] show ?thesis by simp
qed

lemma lp_eqI:
  assumes ct_not_0: "lookup p t \<noteq> 0" and a2: "\<And>s. lookup p s \<noteq> 0 \<Longrightarrow> s \<preceq> t"
  shows "lp p = t"
proof -
  from ct_not_0 have "t \<in> keys p" by simp
  hence "keys p \<noteq> {}" by auto
  hence "p \<noteq> 0"
    using keys_zero by blast
  have "s \<preceq> t" if "s \<in> keys p" for s
  proof -
    from that have "lookup p s \<noteq> 0" by simp
    from a2[OF this] show "s \<preceq> t" .
  qed
  from lp_alt[OF \<open>p \<noteq> 0\<close>] ordered_powerprod_lin.Max_eqI[OF finite_keys this \<open>t \<in> keys p\<close>]
    show ?thesis by simp
qed

lemma lp_less:
  assumes a: "\<And>s. t \<preceq> s \<Longrightarrow> lookup p s = 0" and "p \<noteq> 0"
  shows "lp p \<prec> t"
proof -
  from \<open>p \<noteq> 0\<close> have "keys p \<noteq> {}" by (auto simp: poly_mapping_eq_iff)
  have "\<forall>s\<in>keys p. s \<prec> t"
  proof
    fix s::"'a"
    assume "s \<in> keys p"
    hence "lookup p s \<noteq> 0" by simp
    hence "\<not> t \<preceq> s" using a[of s] by auto
    thus "s \<prec> t" by simp
  qed
  with lp_alt[OF \<open>p \<noteq> 0\<close>] ordered_powerprod_lin.Max_less_iff[OF finite_keys \<open>keys p \<noteq> {}\<close>]
    show ?thesis by simp
qed

lemma lp_gr:
  assumes "lookup p s \<noteq> 0" and "t \<prec> s"
  shows "t \<prec> lp p"
proof -
  from \<open>lookup p s \<noteq> 0\<close> have "s \<in> keys p" by simp
  hence "keys p \<noteq> {}" by auto
  hence "p \<noteq> 0" by auto
  have "\<exists>s\<in>keys p. t \<prec> s"
  proof
    from \<open>t \<prec> s\<close> show "t \<prec> s" .
  next
    from \<open>s \<in> keys p\<close> show "s \<in> keys p" .
  qed
  with lp_alt[OF \<open>p \<noteq> 0\<close>] ordered_powerprod_lin.Max_gr_iff[OF finite_keys \<open>keys p \<noteq> {}\<close>]
    show?thesis  by simp
qed

lemma lc_not_0:
  assumes "p \<noteq> 0"
  shows "lc p \<noteq> 0"
proof -
  from keys_zero assms have "keys p \<noteq> {}" by auto
  from lp_alt[OF assms] ordered_powerprod_lin.Max_in[OF finite_keys this]
    show ?thesis unfolding lc_def by simp
qed

lemma lookup_tail:
  assumes "p \<noteq> 0"
  shows "lookup (tail p) t = (if t \<prec> lp p then lookup p t else 0)"
  by (simp add: lower.rep_eq tail_def)

lemma lookup_tail_2:
  assumes "p \<noteq> 0"
  shows "lookup (tail p) t = (if t = lp p then 0 else lookup p t)"
proof (rule ordered_powerprod_lin.linorder_cases[of t "lp p"])
  assume "t \<prec> lp p"
  hence "t \<noteq> lp p" by simp
  from this \<open>t \<prec> lp p\<close> lookup_tail[OF assms, of t] show ?thesis by simp
next
  assume "t = lp p"
  hence "\<not> t \<prec> lp p" by simp
  from \<open>t = lp p\<close> this lookup_tail[OF assms, of t] show ?thesis by simp
next
  assume "lp p \<prec> t"
  hence "\<not> t \<preceq> lp p" by simp
  hence cp: "lookup p t = 0"
    using lp_max by blast
  from \<open>\<not> t \<preceq> lp p\<close> have "\<not> t = lp p" and "\<not> t \<prec> lp p" by simp_all
  thus ?thesis using cp lookup_tail[OF assms, of t] by simp
qed

lemma leading_monomial_tail:
  fixes p::"('a, 'b::comm_monoid_add) poly_mapping"
  assumes "p \<noteq> 0"
  shows "p = PP_Poly_Mapping.single (lp p) (lc p) + tail p"
proof (rule poly_mapping_eqI)
  fix t
  have "lookup p t = lookup (PP_Poly_Mapping.single (lp p) (lc p)) t + lookup (tail p) t"
  proof (cases "t \<preceq> lp p")
    case True
    show ?thesis
    proof (cases "t = lp p")
      assume "t = lp p"
      hence "\<not> t \<prec> lp p" by simp
      hence c3: "lookup (tail p) t = 0" unfolding lookup_tail[OF assms, of t] by simp
      from \<open>t = lp p\<close> have c2: "lookup (PP_Poly_Mapping.single (lp p) (lc p)) t = lc p" unfolding coeff_monom by simp
      from \<open>t = lp p\<close> have c1: "lookup p t = lc p" unfolding lc_def by simp
      from c1 c2 c3 show ?thesis by simp
    next
      assume "t \<noteq> lp p"
      from this True have "t \<prec> lp p" by simp
      hence c2: "lookup (tail p) t = lookup p t" unfolding lookup_tail[OF assms, of t] by simp
      from \<open>t \<noteq> lp p\<close> have c1: "lookup (PP_Poly_Mapping.single (lp p) (lc p)) t = 0"
        unfolding lookup_single by simp
      from c1 c2 show ?thesis by simp
    qed
  next
    case False
    hence "lp p \<prec> t" by simp
    hence "lp p \<noteq> t" by simp
    from False have "\<not> t \<prec> lp p" by simp
    have c1: "lookup p t = 0"
    proof (rule ccontr)
      assume "lookup p t \<noteq> 0"
      from lp_max[OF this] False show False by simp
    qed
    from \<open>lp p \<noteq> t\<close> have c2: "lookup (PP_Poly_Mapping.single (lp p) (lc p)) t = 0"
      unfolding lookup_single by simp
    from \<open>\<not> t \<prec> lp p\<close> lookup_tail[OF assms, of t] have c3: "lookup (tail p) t = 0" by simp
    from c1 c2 c3 show ?thesis by simp
  qed
  thus "lookup p t = lookup (PP_Poly_Mapping.single (lp p) (lc p) + tail p) t"
    unfolding lookup_add by simp
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
    thus "lookup (tail p) s = 0" unfolding lookup_tail[OF \<open>p \<noteq> 0\<close>, of s] by simp
  qed
qed

lemma lp_monom:
  assumes "c \<noteq> 0"
  shows "lp (PP_Poly_Mapping.single t c) = t"
  by (metis assms lookup_single_eq lookup_single_not_eq lp_eqI ordered_powerprod_lin.eq_iff)

lemma lc_monom:
  assumes "c \<noteq> 0"
  shows "lc (PP_Poly_Mapping.single t c) = c"
unfolding lc_def lp_monom[OF assms] by (simp add: coeff_monom)

lemma tail_monom:
  shows "tail (PP_Poly_Mapping.single t c) = 0"
  by (metis (no_types, lifting) lookup_tail_2 lookup_single_not_eq lp_less lp_monom
      ordered_powerprod_lin.dual_order.strict_implies_not_eq single_zero tail_0)

lemma coeff_higher:
  shows "lookup (higher p s) t = (if s \<prec> t then lookup p t else 0)"
using lp_max[of p] lc_not_0[of p] unfolding lp_def lc_def
proof transfer
  fix p::"'a \<Rightarrow> 'b" and t s::"'a"
  show "(if s \<prec> t then p t else 0) = (if s \<prec> t then p t else 0)" by simp
qed

lemma lp_mult:
  fixes c::"'b::semiring_no_zero_divisors"
  assumes "c \<noteq> 0" and "p \<noteq> 0"
  shows "lp (monom_mult c t p) = t + lp p"
proof (intro lp_eqI)
  from assms lc_not_0[OF \<open>p \<noteq> 0\<close>] show "lookup (monom_mult c t p) (t + lp p) \<noteq> 0"
    unfolding lc_def lp_alt[OF \<open>p \<noteq> 0\<close>]
  proof transfer
    fix c::'b and t::"'a" and p::"'a \<Rightarrow> 'b" and ord::"'a \<Rightarrow> 'a \<Rightarrow> bool"
    assume "c \<noteq> 0" and a: "p (linorder.Max ord {t. p t \<noteq> 0}) \<noteq> 0"
    have "t adds t + linorder.Max ord {s. p s \<noteq> 0}" by (rule, simp)
    from this \<open>c \<noteq> 0\<close> a add_minus_2[of t "linorder.Max ord {s. p s \<noteq> 0}"] show
      "(if t adds t + linorder.Max ord {t. p t \<noteq> 0} then
          c * p (t + linorder.Max ord {t. p t \<noteq> 0} - t)
        else
          0
       ) \<noteq> 0" by simp
  qed
next
  show "\<And>s. lookup (monom_mult c t p) s \<noteq> 0 \<Longrightarrow> s \<preceq> t + lp p"
  proof -
    fix s::"'a"
    from assms lp_max[of p] plus_monotone[of _ "lp p"]
    show "lookup (monom_mult c t p) s \<noteq> 0 \<Longrightarrow> s \<preceq> t + lp p" unfolding lc_def lp_alt[OF \<open>p \<noteq> 0\<close>]
    proof (transfer fixing: s)
      fix c::"'b" and t::"'a" and p::"'a \<Rightarrow> 'b" and ord::"'a \<Rightarrow> 'a \<Rightarrow> bool"
      assume "c \<noteq> 0" and "(if t adds s then c * p (s - t) else 0) \<noteq> 0"
        and b: "\<And>t. p t \<noteq> 0 \<Longrightarrow> ord t (linorder.Max ord {t. p t \<noteq> 0})"
        and c: "(\<And>s u. ord s (linorder.Max ord {t. p t \<noteq> 0}) \<Longrightarrow>
                ord (s + u) (linorder.Max ord {t. p t \<noteq> 0} + u))"
      hence "t adds s" and a: "c * p (s - t) \<noteq> 0" by (simp_all split: if_split_asm)
      from \<open>t adds s\<close> obtain u::"'a" where "s = t + u" unfolding dvd_def ..
      hence "s - t = u" using add_minus_2 by simp
      hence "p u \<noteq> 0" using a by simp
      from \<open>s = t + u\<close> c[OF b[OF this], of t]
      show "ord s (t + linorder.Max ord {t. p t \<noteq> 0})" by (simp add: ac_simps)
    qed
  qed
qed

lemma lc_mult:
  fixes c::"'b::semiring_no_zero_divisors"
  assumes "c \<noteq> 0" and "p \<noteq> 0"
  shows "lc (monom_mult c t p) = c * lc p"
  by (simp add: assms(1) assms(2) lc_def lp_mult monom_mult_lookup)

lemma coeff_mult_0:
  fixes c::"'b::semiring_no_zero_divisors"
  assumes "s + lp p \<prec> t"
  shows "lookup (monom_mult c s p) t = 0"
  by (metis assms aux lp_gr lp_mult monom_mult_left0 monom_mult_right0
      ordered_powerprod_lin.order.strict_implies_not_eq)


subsubsection \<open>Order Relation on Polynomials\<close>

definition ord_strict_p::"('a, 'b::zero) poly_mapping \<Rightarrow> ('a, 'b) poly_mapping \<Rightarrow> bool" (infixl "\<prec>p" 50) where
  "ord_strict_p p q \<equiv> (\<exists>t. lookup p t = 0 \<and> lookup q t \<noteq> 0 \<and> (\<forall>s. t \<prec> s \<longrightarrow> lookup p s = lookup q s))"
definition ord_p::"('a, 'b::zero) poly_mapping \<Rightarrow> ('a, 'b) poly_mapping \<Rightarrow> bool" (infixl "\<preceq>p" 50) where
  "ord_p p q \<equiv> (p \<prec>p q \<or> p = q)"

lemma ord_strict_higher:
  shows "p \<prec>p q \<longleftrightarrow> (\<exists>t. lookup p t = 0 \<and> lookup q t \<noteq> 0 \<and> higher p t = higher q t)"
unfolding ord_strict_p_def higher_equal ..

lemma ord_strict_p_asymmetric:
  assumes "p \<prec>p q"
  shows "\<not> q \<prec>p p"
using assms unfolding ord_strict_p_def
proof
  fix t1::"'a"
  assume "lookup p t1 = 0 \<and> lookup q t1 \<noteq> 0 \<and> (\<forall>s. t1 \<prec> s \<longrightarrow> lookup p s = lookup q s)"
  hence "lookup p t1 = 0" and "lookup q t1 \<noteq> 0" and t1: "\<forall>s. t1 \<prec> s \<longrightarrow> lookup p s = lookup q s"
    by auto
  show "\<not> (\<exists>t. lookup q t = 0 \<and> lookup p t \<noteq> 0 \<and> (\<forall>s. t \<prec> s \<longrightarrow> lookup q s = lookup p s))"
  proof (intro notI, erule exE)
    fix t2::"'a"
    assume "lookup q t2 = 0 \<and> lookup p t2 \<noteq> 0 \<and> (\<forall>s. t2 \<prec> s \<longrightarrow> lookup q s = lookup p s)"
    hence "lookup q t2 = 0" and "lookup p t2 \<noteq> 0" and t2: "\<forall>s. t2 \<prec> s \<longrightarrow> lookup q s = lookup p s"
      by auto
    have "t1 \<prec> t2 \<or> t1 = t2 \<or> t2 \<prec> t1" using less_linear by auto
    thus False
    proof
      assume "t1 \<prec> t2"
      from t1[rule_format, OF this] \<open>lookup q t2 = 0\<close> \<open>lookup p t2 \<noteq> 0\<close> show ?thesis by simp
    next
      assume "t1 = t2 \<or> t2 \<prec> t1"
      thus ?thesis
      proof
        assume "t1 = t2"
        thus ?thesis using \<open>lookup p t1 = 0\<close> \<open>lookup p t2 \<noteq> 0\<close> by simp
      next
        assume "t2 \<prec> t1"
        from t2[rule_format, OF this] \<open>lookup p t1 = 0\<close> \<open>lookup q t1 \<noteq> 0\<close> show ?thesis by simp
      qed
    qed
  qed
qed

lemma ord_strict_p_irreflexive:
  shows "\<not> p \<prec>p p"
unfolding ord_strict_p_def
proof (intro notI, erule exE)
  fix t::"'a"
  assume "lookup p t = 0 \<and> lookup p t \<noteq> 0 \<and> (\<forall>s. t \<prec> s \<longrightarrow> lookup p s = lookup p s)"
  hence "lookup p t = 0" and "lookup p t \<noteq> 0" by auto
  thus False by simp
qed

lemma ord_strict_p_transitive:
  assumes "a \<prec>p b" and "b \<prec>p c"
  shows "a \<prec>p c"
proof -
  from \<open>a \<prec>p b\<close> obtain t1 where "lookup a t1 = 0"
                            and "lookup b t1 \<noteq> 0"
                            and t1[rule_format]: "(\<forall>s. t1 \<prec> s \<longrightarrow> lookup a s = lookup b s)"
    unfolding ord_strict_p_def by auto
  from \<open>b \<prec>p c\<close> obtain t2 where "lookup b t2 = 0"
                            and "lookup c t2 \<noteq> 0"
                            and t2[rule_format]: "(\<forall>s. t2 \<prec> s \<longrightarrow> lookup b s = lookup c s)"
    unfolding ord_strict_p_def by auto
  have "t1 \<prec> t2 \<or> t1 = t2 \<or> t2 \<prec> t1" using less_linear by auto
  thus "a \<prec>p c"
  proof
    assume "t1 \<prec> t2"
    show ?thesis unfolding ord_strict_p_def
    proof
      show "lookup a t2 = 0 \<and> lookup c t2 \<noteq> 0 \<and> (\<forall>s. t2 \<prec> s \<longrightarrow> lookup a s = lookup c s)"
      proof
        from \<open>lookup b t2 = 0\<close> t1[OF \<open>t1 \<prec> t2\<close>] show "lookup a t2 = 0" by simp
      next
        show "lookup c t2 \<noteq> 0 \<and> (\<forall>s. t2 \<prec> s \<longrightarrow> lookup a s = lookup c s)"
        proof
          from \<open>lookup c t2 \<noteq> 0\<close> show "lookup c t2 \<noteq> 0" .
        next
          show "\<forall>s. t2 \<prec> s \<longrightarrow> lookup a s = lookup c s"
          proof (rule, rule)
            fix s::"'a"
            assume "t2 \<prec> s"
            from ordered_powerprod_lin.less_trans[OF \<open>t1 \<prec> t2\<close> this] have "t1 \<prec> s" .
            from t2[OF \<open>t2 \<prec> s\<close>] t1[OF this] show "lookup a s = lookup c s" by simp
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
        show "lookup a t1 = 0 \<and> lookup c t1 \<noteq> 0 \<and> (\<forall>s. t1 \<prec> s \<longrightarrow> lookup a s = lookup c s)"
        proof
          from \<open>lookup a t1 = 0\<close> show "lookup a t1 = 0" .
        next
          show "lookup c t1 \<noteq> 0 \<and> (\<forall>s. t1 \<prec> s \<longrightarrow> lookup a s = lookup c s)"
          proof
            from \<open>lookup b t1 \<noteq> 0\<close> t2[OF \<open>t2 \<prec> t1\<close>] show "lookup c t1 \<noteq> 0" by simp
          next
            show "\<forall>s. t1 \<prec> s \<longrightarrow> lookup a s = lookup c s"
            proof (rule, rule)
              fix s::"'a"
              assume "t1 \<prec> s"
              from ordered_powerprod_lin.less_trans[OF \<open>t2 \<prec> t1\<close> this] have "t2 \<prec> s" .
              from t1[OF \<open>t1 \<prec> s\<close>] t2[OF this] show "lookup a s = lookup c s" by simp
            qed
          qed
        qed
      qed
    next
      assume "t1 = t2"
      thus ?thesis using \<open>lookup b t1 \<noteq> 0\<close> \<open>lookup b t2 = 0\<close> by simp
    qed
  qed
qed

sublocale order ord_p ord_strict_p
proof (intro order_strictI)
  fix p q::"('a, 'b) poly_mapping"
  show "(p \<preceq>p q) = (p \<prec>p q \<or> p = q)" unfolding ord_p_def ..
next
  fix p q::"('a, 'b) poly_mapping"
  assume "p \<prec>p q"
  from ord_strict_p_asymmetric[OF this] show "\<not> q \<prec>p p" .
next
  fix p::"('a, 'b) poly_mapping"
  from ord_strict_p_irreflexive[of p] show "\<not> p \<prec>p p" .
next
  fix a b c::"('a, 'b) poly_mapping"
  assume "a \<prec>p b" and "b \<prec>p c"
  from ord_strict_p_transitive[OF this] show "a \<prec>p c" .
qed

lemma ord_p_0_min:
  shows "0 \<preceq>p p"
unfolding ord_p_def ord_strict_p_def
proof (cases "p = 0")
  case True
  thus "(\<exists>t. lookup 0 t = 0 \<and> lookup p t \<noteq> 0 \<and> (\<forall>s. t \<prec> s \<longrightarrow> lookup 0 s = lookup p s)) \<or> 0 = p"
    by auto
next
  case False
  show "(\<exists>t. lookup 0 t = 0 \<and> lookup p t \<noteq> 0 \<and> (\<forall>s. t \<prec> s \<longrightarrow> lookup 0 s = lookup p s)) \<or> 0 = p"
  proof
    show "(\<exists>t. lookup 0 t = 0 \<and> lookup p t \<noteq> 0 \<and> (\<forall>s. t \<prec> s \<longrightarrow> lookup 0 s = lookup p s))"
    proof
      show "lookup 0 (lp p) = 0 \<and> lookup p (lp p) \<noteq> 0 \<and> (\<forall>s. (lp p) \<prec> s \<longrightarrow> lookup 0 s = lookup p s)"
      proof
        show "lookup 0 (lp p) = 0" by (transfer, simp)
      next
        show "lookup p (lp p) \<noteq> 0 \<and> (\<forall>s. lp p \<prec> s \<longrightarrow> lookup 0 s = lookup p s)"
        proof
          from lc_not_0[OF False] show "lookup p (lp p) \<noteq> 0" unfolding lc_def .
        next
          show "\<forall>s. lp p \<prec> s \<longrightarrow> lookup 0 s = lookup p s"
          proof (rule, rule)
            fix s::"'a"
            assume "lp p \<prec> s"
            hence "\<not> s \<preceq> lp p" by simp
            hence "lookup p s = 0" using lp_max[of p s]
              by metis
            thus "lookup 0 s = lookup p s" by (transfer, simp)
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
  show "lookup p (lp q) = 0"
  proof (rule ccontr)
    assume "lookup p (lp q) \<noteq> 0"
    from lp_max[OF this] \<open>lp p \<prec> lp q\<close> show False by simp
  qed
next
  from lc_not_0[OF \<open>q \<noteq> 0\<close>] show "lookup q (lp q) \<noteq> 0" unfolding lc_def .
next
  show "\<forall>s. lp q \<prec> s \<longrightarrow> lookup p s = lookup q s"
  proof (intro allI, intro impI)
    fix s
    assume "lp q \<prec> s"
    hence "lp p \<prec> s" using \<open>lp p \<prec> lp q\<close> by simp
    have c1: "lookup q s = 0"
    proof (rule ccontr)
      assume "lookup q s \<noteq> 0"
      from lp_max[OF this] \<open>lp q \<prec> s\<close> show False by simp
    qed
    have c2: "lookup p s = 0"
    proof (rule ccontr)
      assume "lookup p s \<noteq> 0"
      from lp_max[OF this] \<open>lp p \<prec> s\<close> show False by simp
    qed
    from c1 c2 show "lookup p s = lookup q s" by simp
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
    and "\<exists>t. lookup p t = 0 \<and> lookup q t \<noteq> 0 \<and> (\<forall>s. t \<prec> s \<longrightarrow> lookup p s = lookup q s)"
  then obtain t where "lookup p t = 0"
                  and "lookup q t \<noteq> 0"
                  and a: "\<forall>s. t \<prec> s \<longrightarrow> lookup p s = lookup q s" by auto
  from lp_max[OF \<open>lookup q t \<noteq> 0\<close>] \<open>lp p = lp q\<close> have "t \<prec> lp p \<or> t = lp p" by auto
  hence "t \<prec> lp p"
  proof
    assume "t \<prec> lp p"
    thus ?thesis .
  next
    assume "t = lp p"
    thus ?thesis using lc_not_0[OF \<open>p \<noteq> 0\<close>] \<open>lookup p t = 0\<close> unfolding lc_def by auto
  qed
  have pt: "lookup (tail p) t = lookup p t" using lookup_tail[OF \<open>p \<noteq> 0\<close>, of t] \<open>t \<prec> lp p\<close> by simp
  have "q \<noteq> 0"
  proof
    assume "q = 0"
    hence  "p \<prec>p 0" using \<open>p \<prec>p q\<close> by simp
    hence "\<not> 0 \<preceq>p p" by auto
    thus False using ord_p_0_min[of p] by simp
  qed
  have qt: "lookup (tail q) t = lookup q t"
    using lookup_tail[OF \<open>q \<noteq> 0\<close>, of t] \<open>t \<prec> lp p\<close> \<open>lp p = lp q\<close> by simp
  show "\<exists>t. lookup (tail p) t = 0 \<and> lookup (tail q) t \<noteq> 0 \<and>
        (\<forall>s. t \<prec> s \<longrightarrow> lookup (tail p) s = lookup (tail q) s)"
  proof (rule, rule)
    from pt \<open>lookup p t = 0\<close> show "lookup (tail p) t = 0" by simp
  next
    show "lookup (tail q) t \<noteq> 0 \<and> (\<forall>s. t \<prec> s \<longrightarrow> lookup (tail p) s = lookup (tail q) s)"
    proof
      from qt \<open>lookup q t \<noteq> 0\<close> show "lookup (tail q) t \<noteq> 0" by simp
    next
      show "\<forall>s. t \<prec> s \<longrightarrow> lookup (tail p) s = lookup (tail q) s"
      proof (rule, rule)
        fix s::"'a"
        assume "t \<prec> s"
        from a[rule_format, OF \<open>t \<prec> s\<close>] lookup_tail[OF \<open>p \<noteq> 0\<close>, of s] lookup_tail[OF \<open>q \<noteq> 0\<close>, of s]
          \<open>lp p = lp q\<close> show "lookup (tail p) s = lookup (tail q) s" by simp
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

lemma higher_lookup_equal_0:
  assumes pt: "lookup p t = 0" and hp: "higher p t = 0" and le: "q \<preceq>p p"
  shows "(lookup q t = 0) \<and> (higher q t) = 0"
using le unfolding ord_p_def
proof
  assume "q \<prec>p p"
  thus ?thesis unfolding ord_strict_p_def
  proof
    fix s::"'a"
    assume "lookup q s = 0 \<and> lookup p s \<noteq> 0 \<and> (\<forall>u. s \<prec> u \<longrightarrow> lookup q u = lookup p u)"
    hence qs: "lookup q s = 0" and ps: "lookup p s \<noteq> 0" and u: "\<forall>u. s \<prec> u \<longrightarrow> lookup q u = lookup p u"
      by auto
    from hp have pu: "\<forall>u. t \<prec> u \<longrightarrow> lookup p u = 0" by (simp only: higher_equal_0)
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
      from u[rule_format, OF st] pt show "lookup q t = 0" by simp
    next
      have "\<forall>u. t \<prec> u \<longrightarrow> lookup q u = 0"
      proof (intro allI, intro impI)
        fix u
        assume "t \<prec> u"
        from this st have "s \<prec> u" by simp
        from u[rule_format, OF this] pu[rule_format, OF \<open>t \<prec> u\<close>] show "lookup q u = 0" by simp
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
  from tail obtain t where pt: "lookup (tail p) t = 0"
                      and qt: "lookup (tail q) t \<noteq> 0"
                      and a: "\<forall>s. t \<prec> s \<longrightarrow> lookup (tail p) s = lookup (tail q) s"
    unfolding ord_strict_p_def by auto
  from qt lookup_zero[of t] have "tail q \<noteq> 0" by auto
  from lp_max[OF qt] lp_tail[OF this] have "t \<prec> lp q" by simp
  hence "t \<prec> lp p" using \<open>lp p = lp q\<close> by simp
  show ?thesis unfolding ord_strict_p_def
  proof (rule exI[of _ t], intro conjI)
    from lookup_tail[OF \<open>p \<noteq> 0\<close>, of t] \<open>t \<prec> lp p\<close> pt show "lookup p t = 0" by simp
  next
    from lookup_tail[OF \<open>q \<noteq> 0\<close>, of t] \<open>t \<prec> lp q\<close> qt show "lookup q t \<noteq> 0" by simp
  next
    show "\<forall>s. t \<prec> s \<longrightarrow> lookup p s = lookup q s"
    proof (intro allI, intro impI)
      fix s
      assume "t \<prec> s"
      from this a have s: "lookup (tail p) s = lookup (tail q) s" by simp
      show "lookup p s = lookup q s"
      proof (cases "s = lp p")
        case True
        from True \<open>lc p = lc q\<close> \<open>lp p = lp q\<close> show ?thesis unfolding lc_def by simp
      next
        case False
        from False s lookup_tail_2[OF \<open>p \<noteq> 0\<close>, of s] lookup_tail_2[OF \<open>q \<noteq> 0\<close>, of s] \<open>lp p = lp q\<close>
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
  from \<open>p \<prec>p q\<close> obtain t where pt: "lookup p t = 0"
                          and qt: "lookup q t \<noteq> 0"
                          and a: "\<forall>s. t \<prec> s \<longrightarrow> lookup p s = lookup q s"
    unfolding ord_strict_p_def by auto
  show ?thesis
  proof (cases "t \<prec> lp p")
    case True
    from this a have "lookup p (lp p) = lookup q (lp p)" by simp
    thus ?thesis using \<open>lp p = lp q\<close> unfolding lc_def by simp
  next
    case False
    from this lp_max[OF qt] \<open>lp p = lp q\<close> have "t = lp p" by simp
    from this lc_not_0[OF \<open>p \<noteq> 0\<close>] pt show ?thesis unfolding lc_def by auto
  qed
qed

lemma ord_strict_p_rec[code]:
  "p \<prec>p q =
  (q \<noteq> 0 \<and>
    (p = 0 \<or>
      (let l1 = lp p; l2 = lp q in
        (l1 \<prec> l2 \<or> (l1 = l2 \<and> lookup p l1 = lookup q l2 \<and> lower p l1 \<prec>p lower q l2))
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
              (l1 \<prec> l2 \<or> l1 = l2 \<and> lookup p l1 = lookup q l2 \<and> lower p l1 \<prec>p lower q l2)
            )"
      unfolding lc_def tail_def by auto
  qed
next
  assume ?R
  hence "q \<noteq> 0"
    and dis: "p = 0 \<or>
                (let l1 = lp p; l2 = lp q in
                  (l1 \<prec> l2 \<or> l1 = l2 \<and> lookup p l1 = lookup q l2 \<and> lower p l1 \<prec>p lower q l2)
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
            (l1 \<prec> l2 \<or> l1 = l2 \<and> lookup p l1 = lookup q l2 \<and> lower p l1 \<prec>p lower q l2)"
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

end (* ordered_powerprod *)

context od_powerprod
begin

(*The following two lemmas prove that \<prec>p is well-founded.
Although the first proof uses induction on power-products whereas the second one does not,
the two proofs share a lot of common structure. Maybe this can be exploited to make things
shorter ...?*)
lemma ord_p_wf_aux:
  assumes "x \<in> Q" and a2: "\<forall>y\<in>Q. y = 0 \<or> lp y \<prec> s"
  shows "\<exists>p\<in>Q. (\<forall>q\<in>Q. \<not> q \<prec>p p)"
using assms
proof (induct s arbitrary: x Q rule: wfP_induct[OF wf_ord_strict])
  fix s::"'a" and x::"('a, 'b) poly_mapping" and Q::"('a, 'b) poly_mapping set"
  assume hyp: "\<forall>s0. s0 \<prec> s \<longrightarrow> (\<forall>x0 Q0::('a, 'b) poly_mapping set. x0 \<in> Q0 \<longrightarrow>
                                  (\<forall>y\<in>Q0. y = 0 \<or> lp y \<prec> s0) \<longrightarrow> (\<exists>p\<in>Q0. \<forall>q\<in>Q0. \<not> q \<prec>p p))"
  assume "x \<in> Q"
  assume bounded: "\<forall>y\<in>Q. y = 0 \<or> lp y \<prec> s"
  show "\<exists>p\<in>Q. \<forall>q\<in>Q. \<not> q \<prec>p p"
  proof (cases "0 \<in> Q")
    case True
    show ?thesis
    proof (rule, rule, rule)
      fix q::"('a, 'b) poly_mapping"
      assume "q \<prec>p 0"
      thus False using ord_p_0_min[of q] by simp
    next
      from True show "0 \<in> Q" .
    qed
  next
    case False
    define Q1 where "Q1 = {lp p | p. p \<in> Q}"
    from \<open>x \<in> Q\<close> have "lp x \<in> Q1" unfolding Q1_def by auto
    from wf_ord_strict have "wf {(x, y). x \<prec> y}" unfolding wfP_def .
    from wfE_min[OF this \<open>lp x \<in> Q1\<close>] obtain t where
      "t \<in> Q1" and t_min_1: "\<And>y. (y, t) \<in> {(x, y). x \<prec> y} \<Longrightarrow> y \<notin> Q1" by auto
    have t_min: "\<And>q. q \<in> Q \<Longrightarrow> t \<preceq> lp q"
    proof -
      fix q::"('a, 'b) poly_mapping"
      assume "q \<in> Q"
      hence "lp q \<in> Q1" unfolding Q1_def by auto
      hence "(lp q, t) \<notin> {(x, y). x \<prec> y}" using t_min_1 by auto
      hence "\<not> lp q \<prec> t" by simp
      thus "t \<preceq> lp q" by simp
    qed
    from \<open>t \<in> Q1\<close> obtain p where "lp p = t" and "p \<in> Q" unfolding Q1_def by auto
    hence "p \<noteq> 0" using False by auto
    hence "lp p \<prec> s" using bounded[rule_format, OF \<open>p \<in> Q\<close>] by auto
    define Q2 where "Q2 = {tail p | p. p \<in> Q \<and> lp p = t}"
    from \<open>p \<in> Q\<close> \<open>lp p = t\<close> have "tail p \<in> Q2" unfolding Q2_def by auto
    have "\<And>q. q \<in> Q2 \<Longrightarrow> q = 0 \<or> lp q \<prec> lp p"
    proof -
      fix q::"('a, 'b) poly_mapping"
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
        fix r::"('a, 'b) poly_mapping"
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
  fix Q::"('a, 'b) poly_mapping set" and x::"('a, 'b) poly_mapping"
  assume "x \<in> Q"
  show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> {(x, y). x \<prec>p y} \<longrightarrow> y \<notin> Q"
  proof (cases "0 \<in> Q")
    case True
    show ?thesis
    proof (rule, rule, rule)
      from True show "0 \<in> Q" .
    next
      fix q::"('a, 'b) poly_mapping"
      assume "(q, 0) \<in> {(x, y). x \<prec>p y}"
      thus "q \<notin> Q" using ord_p_0_min[of q] by simp
    qed
  next
    case False
    define Q1 where "Q1 = {lp p | p. p \<in> Q}"
    from \<open>x \<in> Q\<close> have "lp x \<in> Q1" unfolding Q1_def by auto
    from wf_ord_strict have "wf {(x, y). x \<prec> y}" unfolding wfP_def .
    from wfE_min[OF this \<open>lp x \<in> Q1\<close>] obtain t where
      "t \<in> Q1" and t_min_1: "\<And>y. (y, t) \<in> {(x, y). x \<prec> y} \<Longrightarrow> y \<notin> Q1" by auto
    have t_min: "\<And>q. q \<in> Q \<Longrightarrow> t \<preceq> lp q"
    proof -
      fix q::"('a, 'b) poly_mapping"
      assume "q \<in> Q"
      hence "lp q \<in> Q1" unfolding Q1_def by auto
      hence "(lp q, t) \<notin> {(x, y). x \<prec> y}" using t_min_1 by auto
      hence "\<not> lp q \<prec> t" by simp
      thus "t \<preceq> lp q" by simp
    qed
    define Q2 where "Q2 = {tail p | p. p \<in> Q \<and> lp p = t}"
    from \<open>t \<in> Q1\<close> obtain p where "lp p = t" and "p \<in> Q" unfolding Q1_def by auto
    hence "tail p \<in> Q2" unfolding Q2_def by auto
    have "\<forall>y\<in>Q2. y = 0 \<or> lp y \<prec> t"
    proof
      fix y::"('a, 'b) poly_mapping"
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
        fix q::"('a, 'b) poly_mapping"
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

end (* od_powerprod *)

end (* theory *)