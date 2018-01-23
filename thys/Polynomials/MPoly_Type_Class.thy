(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Type-Class-Multivariate Polynomials\<close>

theory MPoly_Type_Class
  imports
    Power_Products
begin

text \<open>This theory views \<open>'a \<Rightarrow>\<^sub>0 'b\<close> as multivariate polynomials, where type class constraints on
\<open>'a\<close> ensure that \<open>'a\<close> represents something like monomials.\<close>

lemma mpoly_ext: "p = q" if "\<And>t. coeff p t = coeff q t"
  using that
  by (metis coeff_def mapping_of_inverse poly_mapping_eqI)

lemma coeff_monom:
  "coeff (monom s c) t = (if t = s then c else 0)"
  by (auto simp: coeff_monom)

abbreviation "monomial \<equiv> (\<lambda>c t. Poly_Mapping.single t c)"

lemma keys_of_monomial:
  assumes "c \<noteq> 0"
  shows "keys (monomial c t) = {t}"
  using assms by simp

lemma monomial_uminus:
  shows "- monomial c s = monomial (-c) s"
  by (transfer, rule ext, simp add: Poly_Mapping.when_def)

subsection \<open>Multiplication by Monomials (in type class)\<close>

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

lemma lookup_monom_mult:
  fixes c::"'b::semiring_0" and t s::"'a" and p::"('a, 'b) poly_mapping"
  shows "lookup (monom_mult c t p) (t + s) = c * lookup p s"
  by (simp add: monom_mult.rep_eq)

lemma lookup_monom_mult_right:
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

lemma monom_mult_monomial:
  fixes c d::"'b::semiring_0" and s t::"'a"
  shows "monom_mult c s (monomial d t) = monomial (c * d) (s + t)"
proof (transfer)
  fix c::'b and s::'a and t d sa
  have "\<forall>k. l \<noteq> s + k \<Longrightarrow> (c * d when s + t = l) = 0" for l
    by (metis (mono_tags, lifting) zero_class.when(2))
  then show " (\<lambda>sa. if s adds sa then c * (d when t = sa - s) else 0) = (\<lambda>k'. c * d when s + t = k')"
    by (force simp: when_def adds_def mult_when)
qed

lemma monom_mult_right_monomial:
  fixes c d::"'b::semiring_0" and s t::"'a"
  shows "monom_mult_right (monomial c s) d t = monomial (c * d) (s + t)"
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

lemma monom_mult_left_monomial_monom_mult_right:
  fixes c d::"'b::semiring_0" and s t::"'a"
  shows "monom_mult c s (monomial d t) = monom_mult_right (monomial c s) d t"
  using monom_mult_monomial[of c s] monom_mult_right_monomial[of s c] by simp

lemma monom_mult_left_monom_mult_right:
  fixes c::"'b::comm_semiring_0" and t::"'a" and p::"('a, 'b) poly_mapping"
  shows "monom_mult c t p = monom_mult_right p c t"
  by (transfer) (auto simp: ac_simps)

lemma monom_mult_left_monomial:
  fixes c d::"'b::comm_semiring_0" and s t::"'a"
  shows "monom_mult c s (monomial d t) = monom_mult d t (monomial c s)"
  using monom_mult_left_monom_mult_right[of d t] monom_mult_left_monomial_monom_mult_right by simp

lemma monom_mult_right_monomial':
  fixes c d::"'b::comm_semiring_0" and s t::"'a"
  shows "monom_mult_right (monomial c s) d t = monom_mult_right (monomial d t) c s"
  using monom_mult_left_monom_mult_right[of d t] monom_mult_left_monomial_monom_mult_right[of d t]
  by simp

lemma monom_mult_0_iff:
  fixes c::"'b::semiring_no_zero_divisors" and t p
  shows "(monom_mult c t p = 0) \<longleftrightarrow> (c = 0 \<or> p = 0)"
proof
  assume eq: "monom_mult c t p = 0"
  show "c = 0 \<or> p = 0"
  proof (rule ccontr, simp)
    assume "c \<noteq> 0 \<and> p \<noteq> 0"
    hence "c \<noteq> 0" and "p \<noteq> 0" by simp_all
    from lookup_zero poly_mapping_eq_iff[of p 0] \<open>p \<noteq> 0\<close> obtain s where "lookup p s \<noteq> 0" by fastforce
    from eq lookup_zero have "lookup (monom_mult c t p) (t + s) = 0" by simp
    hence "c * lookup p s = 0" by (simp only: lookup_monom_mult)
    with \<open>c \<noteq> 0\<close> \<open>lookup p s \<noteq> 0\<close> show False by auto
  qed
next
  assume "c = 0 \<or> p = 0"
  with monom_mult_left0[of t p] monom_mult_right0[of c t] show "monom_mult c t p = 0" by auto
qed

lemma monom_mult_right_0_iff:
  fixes c::"'b::semiring_no_zero_divisors" and t p
  shows "(monom_mult_right p c t = 0) \<longleftrightarrow> (c = 0 \<or> p = 0)"
proof
  assume eq: "monom_mult_right p c t = 0"
  show "c = 0 \<or> p = 0"
  proof (rule ccontr, simp)
    assume "c \<noteq> 0 \<and> p \<noteq> 0"
    hence "c \<noteq> 0" and "p \<noteq> 0" by simp_all
    from lookup_zero poly_mapping_eq_iff[of p 0] \<open>p \<noteq> 0\<close> obtain s where "lookup p s \<noteq> 0" by fastforce
    from eq lookup_zero have "lookup (monom_mult_right p c t) (s + t) = 0" by simp
    hence "lookup p s * c = 0" by (simp only: lookup_monom_mult_right)
    with \<open>c \<noteq> 0\<close> \<open>lookup p s \<noteq> 0\<close> show False by auto
  qed
next
  assume "c = 0 \<or> p = 0"
  with monom_mult_right_right0[of p t] monom_mult_right_left0[of c t] show "monom_mult_right p c t = 0" by auto
qed

subsection \<open>@{const keys}\<close>

lemma in_keys_plusI1:
  assumes "t \<in> keys p" and "t \<notin> keys q"
  shows "t \<in> keys (p + q)"
  using assms unfolding in_keys_iff lookup_add by simp

lemma in_keys_plusI2:
  assumes "t \<in> keys q" and "t \<notin> keys p"
  shows "t \<in> keys (p + q)"
  using assms unfolding in_keys_iff lookup_add by simp

lemma keys_plus_eqI:
  assumes "keys p \<inter> keys q = {}"
  shows "keys (p + q) = (keys p \<union> keys q)"
proof (rule, rule keys_add_subset, rule)
  fix t
  assume "t \<in> keys p \<union> keys q"
  thus "t \<in> keys (p + q)"
  proof
    assume "t \<in> keys p"
    moreover from assms this have "t \<notin> keys q" by auto
    ultimately show ?thesis by (rule in_keys_plusI1)
  next
    assume "t \<in> keys q"
    moreover from assms this have "t \<notin> keys p" by auto
    ultimately show ?thesis by (rule in_keys_plusI2)
  qed
qed
  
lemma keys_uminus: "keys (-p) = keys p"
  by (transfer, auto)

lemma keys_minus: "keys (p - q) \<subseteq> (keys p \<union> keys q)"
  by (transfer, auto)
    
lemma keys_monom_multI:
  assumes "s \<in> keys p" and "c \<noteq> (0::'b::semiring_no_zero_divisors)"
  shows "t + s \<in> keys (monom_mult c t p)"
  using assms unfolding in_keys_iff lookup_monom_mult by simp
    
lemma keys_monom_multE:
  assumes "s \<in> keys (monom_mult c t p)"
  obtains x where "x \<in> keys p" and "s = t + x"
proof -
  from assms have "t adds s \<and> lookup p (s - t) \<noteq> 0" by (transfer, auto split: if_splits)
  hence a: "t adds s" and b: "lookup p (s - t) \<noteq> 0" by simp_all
  from a obtain x where s: "s = t + x" by (rule addsE)
  have "s - t = x" unfolding s by simp
  with b have "lookup p x \<noteq> 0" by simp
  show ?thesis
  proof
    from \<open>lookup p x \<noteq> 0\<close> show "x \<in> keys p" unfolding in_keys_iff .
  qed fact
qed

lemma keys_monom_mult_subset: "keys (monom_mult c t p) \<subseteq> ((+) t) ` (keys p)"
proof
  fix s
  assume "s \<in> keys (monom_mult c t p)"
  then obtain x where "x \<in> keys p" and "s = t + x" by (rule keys_monom_multE)
  thus "s \<in> ((+) t) ` (keys p)" unfolding image_iff ..
qed

lemma keys_monom_mult:
  assumes "c \<noteq> (0::'b::semiring_no_zero_divisors)"
  shows "keys (monom_mult c t p) = ((+) t) ` (keys p)"
proof (rule, fact keys_monom_mult_subset, rule)
  fix s
  assume "s \<in> (+) t ` keys p"
  hence "\<exists>x\<in>keys p. s = t + x" unfolding image_iff .
  then obtain x where "x \<in> keys p" and s: "s = t + x" ..
  from \<open>x \<in> keys p\<close> assms show "s \<in> keys (monom_mult c t p)" unfolding s by (rule keys_monom_multI)
qed

lemma poly_mapping_keys_eqI:
  assumes a1: "keys p = keys q" and a2: "\<And>t. t \<in> keys p \<Longrightarrow> lookup p t = lookup q t"
  shows "p = q"
proof (rule poly_mapping_eqI)
  fix t
  show "lookup p t = lookup q t"
  proof (cases "t \<in> keys p")
    case True
    thus ?thesis by (rule a2)
  next
    case False
    moreover from this have "t \<notin> keys q" unfolding a1 .
    ultimately have "lookup p t = 0" and "lookup q t = 0" unfolding in_keys_iff by simp_all
    thus ?thesis by simp
  qed
qed

end (* comm_powerprod *)

subsection \<open>except\<close>

lift_definition except::
  "('a, 'b::zero) poly_mapping \<Rightarrow> 'a set \<Rightarrow> ('a, 'b::zero) poly_mapping" is
  "\<lambda>p S t. if t \<in> S then (0::'b) else p t"
proof -
  fix p::"'a \<Rightarrow> 'b" and S::"'a set"
  assume "finite {t. p t \<noteq> 0}"
  show "finite {t. (if t \<in> S then 0 else p t) \<noteq> 0}"
  proof (rule finite_subset[of _ "{t. p t \<noteq> 0}"], rule)
    fix u
    assume "u \<in> {t. (if t \<in> S then 0 else p t) \<noteq> 0}"
    hence "(if u \<in> S then 0 else p u) \<noteq> 0" by simp
    hence "p u \<noteq> 0" by meson
    thus "u \<in> {t. p t \<noteq> 0}" by simp
  qed (fact)
qed

lemma lookup_except: "lookup (except p S) t = (if t \<in> S then 0 else lookup p t)"
  by (auto simp: except.rep_eq)

lemma lookup_except_when: "lookup (except p S) t = (lookup p t when t \<notin> S)"
  by (auto simp: when_def lookup_except)

lemma lookup_except_singleton: "lookup (except p {t}) t = 0"
  by (simp add: lookup_except)

lemma except_zero[simp]: "except 0 S = 0"
  by (transfer, auto)

lemma lookup_except_eq_idI:
  assumes "t \<notin> S"
  shows "lookup (except p S) t = lookup p t"
  using assms by (simp add: lookup_except)

lemma lookup_except_eq_zeroI:
  assumes "t \<in> S"
  shows "lookup (except p S) t = 0"
  using assms by (simp add: lookup_except)

lemma except_empty[simp]: "except p {} = p"
  by (transfer, auto)

lemma except_eq_zeroI:
  assumes "keys p \<subseteq> S"
  shows "except p S = 0"
proof (rule poly_mapping_eqI, simp)
  fix t
  show "lookup (except p S) t = 0"
  proof (cases "t \<in> S")
    case True
    thus ?thesis by (rule lookup_except_eq_zeroI)
  next
    case False
    hence "lookup (except p S) t = lookup p t" by (rule lookup_except_eq_idI)
    also have "... = 0" using False assms by auto
    finally show ?thesis .
  qed
qed

lemma except_eq_zeroE:
  assumes "except p S = 0"
  shows "keys p \<subseteq> S"
proof
  fix t
  assume "t \<in> keys p"
  hence "lookup p t \<noteq> 0" by simp
  moreover from assms have "lookup (except p S) t = 0" by simp
  ultimately show "t \<in> S" unfolding lookup_except by presburger
qed                                                                    

lemma except_eq_zero_iff: "except p S = 0 \<longleftrightarrow> keys p \<subseteq> S"
  by (rule, elim except_eq_zeroE, elim except_eq_zeroI)

lemma except_keys[simp]: "except p (keys p) = 0"
  by (rule except_eq_zeroI, rule subset_refl)

lemma plus_except: "p = monomial (lookup p t) t + except p {t}"
  by (rule poly_mapping_eqI, simp add: lookup_add lookup_single lookup_except when_def split: if_split)

lemma keys_except: "keys (except p S) = keys p - S"
  by (transfer, auto)

lemma keys_eq_empty_iff[simp]: "keys p = {} \<longleftrightarrow> p = 0"
  by (metis keys_zero lookup_zero not_in_keys_iff_lookup_eq_zero poly_mapping_eqI)

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
    hence "?y0 < z0" unfolding z0_def by (simp add: psubset_card_mono) 
    hence "(?y0, z0) \<in> {(x, y). x < y}" by simp
    from z0_min[OF this] show "y \<notin> Q" by auto
  qed (fact)
qed

lemma poly_mapping_except_induct:
  assumes base: "P 0" and ind: "\<And>p t. p \<noteq> 0 \<Longrightarrow> t \<in> keys p \<Longrightarrow> P (except p {t}) \<Longrightarrow> P p"
  shows "P p"
proof (induct rule: wfP_induct[OF keys_subset_wf])
  fix p::"('a, 'b) poly_mapping"
  assume "\<forall>q. keys q \<subset> keys p \<longrightarrow> P q"
  hence IH: "\<And>q. keys q \<subset> keys p \<Longrightarrow> P q" by simp
  show "P p"
  proof (cases "p = 0")
    case True
    thus ?thesis using base by simp
  next
    case False
    hence "keys p \<noteq> {}" by simp
    then obtain t where "t \<in> keys p" by blast
    show ?thesis
    proof (rule ind, fact, fact, rule IH, simp only: keys_except, rule, rule Diff_subset, rule)
      assume "keys p - {t} = keys p"
      hence "t \<notin> keys p" by blast
      from this \<open>t \<in> keys p\<close> show False ..
    qed
  qed
qed

lemma poly_mapping_except_induct':
  assumes "\<And>p. (\<And>t. t \<in> keys p \<Longrightarrow> P (except p {t})) \<Longrightarrow> P p"
  shows "P p"
proof (induct "card (keys p)" arbitrary: p)
  case 0
  with finite_keys[of p] have "keys p = {}" by simp
  show ?case by (rule assms, simp add: \<open>keys p = {}\<close>)
next
  case step: (Suc n)
  show ?case
  proof (rule assms)
    fix t
    assume "t \<in> keys p"
    show "P (except p {t})"
    proof (rule step(1), simp add: keys_except)
      from step(2) \<open>t \<in> keys p\<close> finite_keys[of p] show "n = card (keys p - {t})" by simp
    qed
  qed
qed

lemma poly_mapping_plus_induct:
  assumes "P 0" and "\<And>p c t. c \<noteq> 0 \<Longrightarrow> t \<notin> keys p \<Longrightarrow> P p \<Longrightarrow> P (monomial c t + p)"
  shows "P p"
proof (induct "card (keys p)" arbitrary: p)
  case 0
  with finite_keys[of p] have "keys p = {}" by simp
  hence "p = 0" by simp
  with assms(1) show ?case by simp
next
  case step: (Suc n)
  from step(2) obtain t where t: "t \<in> keys p" by (metis card_eq_SucD insert_iff)
  define c where "c = lookup p t"
  define q where "q = except p {t}"
  have *: "p = monomial c t + q"
    by (rule poly_mapping_eqI, simp add: lookup_add lookup_single Poly_Mapping.when_def, intro conjI impI,
        simp add: q_def lookup_except c_def, simp add: q_def lookup_except_eq_idI)
  show ?case
  proof (simp only: *, rule assms(2))
    from t show "c \<noteq> 0" by (simp add: c_def)
  next
    show "t \<notin> keys q" by (simp add: q_def keys_except)
  next
    show "P q"
    proof (rule step(1))
      from step(2) \<open>t \<in> keys p\<close> show "n = card (keys q)" unfolding q_def keys_except
        by (metis Suc_inject card.remove finite_keys)
    qed
  qed
qed

subsection \<open>Multiplication\<close>

lemma monomial_0I:
  fixes c::"'b::zero" and t::"'a"
  assumes "c = 0"
  shows "monomial c t = 0"
  using assms
  by transfer (auto)

lemma monomial_0D:
  fixes c::"'b::zero" and t::"'a"
  assumes "monomial c t = 0"
  shows "c = 0"
  using assms
  by transfer (auto simp: fun_eq_iff when_def; meson)

corollary monomial_0_iff: "monomial c t = 0 \<longleftrightarrow> c = 0"
  by (rule, erule monomial_0D, erule monomial_0I)

lemma times_monomial_left: "(monomial c t) * p = monom_mult c t p"
proof (induct p rule: poly_mapping_except_induct, simp add: monom_mult_right0)
  fix p::"('a, 'b) poly_mapping" and s
  assume "p \<noteq> 0" and "s \<in> keys p" and IH: "monomial c t * except p {s} = monom_mult c t (except p {s})"
  from plus_except[of p s] have "monomial c t * p = monomial c t * (monomial (lookup p s) s + except p {s})"
    by simp
  also have "... = monomial c t * monomial (lookup p s) s + monomial c t * except p {s}"
    by (simp add: algebra_simps)
  also have "... = monom_mult c t (monomial (lookup p s) s) + monom_mult c t (except p {s})"
    by (simp only: mult_single monom_mult_monomial IH)
  also have "... = monom_mult c t (monomial (lookup p s) s + except p {s})"
    by (simp only: monom_mult_dist_right)
  finally show "monomial c t * p = monom_mult c t p" by (simp only: plus_except[symmetric])
qed

lemma times_monomial_right: "p * (monomial c t) = monom_mult_right p c t"
proof (induct p rule: poly_mapping_except_induct, simp add: monom_mult_right_left0)
  fix p::"('a, 'b) poly_mapping" and s
  assume "p \<noteq> 0" and "s \<in> keys p" and IH: "except p {s} * monomial c t = monom_mult_right (except p {s}) c t"
  from plus_except[of p s] have "p * monomial c t = (monomial (lookup p s) s + except p {s}) * monomial c t"
    by simp
  also have "... = monomial (lookup p s) s * monomial c t + except p {s} * monomial c t"
    by (simp add: algebra_simps)
  also have "... = monom_mult_right (monomial (lookup p s) s) c t + monom_mult_right (except p {s}) c t"
    by (simp only: mult_single monom_mult_right_monomial IH)
  also have "... = monom_mult_right (monomial (lookup p s) s + except p {s}) c t"
    by (simp only: monom_mult_right_dist_left)
  finally show "p * monomial c t = monom_mult_right p c t" by (simp only: plus_except[symmetric])
qed

lemma times_rec_left:
  "p * q = monom_mult (lookup p t) t q + (except p {t}) * q"
proof -
  from plus_except[of p t] have "p * q = (monomial (lookup p t) t + except p {t}) * q" by simp
  also have "... = monomial (lookup p t) t * q + except p {t} * q" by (simp only: algebra_simps)
  finally show ?thesis by (simp only: times_monomial_left)
qed

lemma times_rec_right:
  "p * q = monom_mult_right p (lookup q t) t + p * except q {t}"
proof -
  from plus_except[of q t] have "p * q = p * (monomial (lookup q t) t + except q {t})" by simp
  also have "... = p * monomial (lookup q t) t + p * except q {t}" by (simp only: algebra_simps)
  finally show ?thesis by (simp only: times_monomial_right)
qed

lemma in_keys_timesE:
  assumes "t \<in> keys (p * q)"
  obtains u v where "u \<in> keys p" and "v \<in> keys q" and "t = u + v"
proof -
  from assms have "lookup (p * q) t \<noteq> 0" by simp
  hence "(\<Sum>u. lookup p u * (\<Sum>v. lookup q v when t = u + v)) \<noteq> 0"
    by (simp add: lookup_mult)
  then obtain u where "lookup p u * (\<Sum>v. lookup q v when t = u + v) \<noteq> 0"
    using Sum_any.not_neutral_obtains_not_neutral by blast
  from mult_not_zero[OF this] have "lookup p u \<noteq> 0" and "(\<Sum>v. lookup q v when t = u + v) \<noteq> 0" by simp_all
  from this(2) obtain v where "(lookup q v when t = u + v) \<noteq> 0"
    using Sum_any.not_neutral_obtains_not_neutral by blast
  hence "v \<in> keys q" and "u + v = t" by simp_all
  moreover from \<open>lookup p u \<noteq> 0\<close> have "u \<in> keys p" by simp
  ultimately show ?thesis using that by blast
qed

subsection \<open>Ideal-like Sets of Polynomials\<close>

text \<open>We now introduce ideal-like sets of polynomials, i.e. sets that are closed under addition and
  under multiplication by polynomials from a certain set @{term C} @{emph \<open>from the left\<close>}.
  We later define "real" ideals as well as linear hulls in terms of these ideal-like sets; in the
  former case, @{term C} is taken to be the universe, in the latter case it is taken to be the set
  of all monomials with power-product @{term 0}.\<close>

inductive_set ideal_like::"('a::comm_powerprod, 'b::semiring_0) poly_mapping set \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) set"
for C::"('a, 'b) poly_mapping set" and B::"('a, 'b) poly_mapping set" where
  ideal_like_0: "0 \<in> (ideal_like C B)"|
  ideal_like_plus: "a \<in> (ideal_like C B) \<Longrightarrow> b \<in> B \<Longrightarrow> q \<in> C \<Longrightarrow> a + q * b \<in> (ideal_like C B)"

lemma times_in_ideal_like:
  assumes "q \<in> C" and "b \<in> B"
  shows "q * b \<in> ideal_like C B"
proof -
  have "0 + q * b \<in> ideal_like C B" by (rule ideal_like_plus, rule ideal_like_0, fact+)
  thus ?thesis by (simp add: times_monomial_left)
qed

lemma monom_mult_in_ideal_like:
  assumes "monomial c t \<in> C" and "b \<in> B"
  shows "monom_mult c t b \<in> ideal_like C B"
  unfolding times_monomial_left[symmetric] using assms by (rule times_in_ideal_like)

lemma generator_subset_ideal_like:
  fixes B::"('a::comm_powerprod, 'b::semiring_1) poly_mapping set"
  assumes "1 \<in> C"
  shows "B \<subseteq> ideal_like C B"
proof
  fix b
  assume b_in: "b \<in> B"
  have "0 + 1 * b \<in> ideal_like C B" by (rule ideal_like_plus, fact ideal_like_0, fact+)
  thus "b \<in> ideal_like C B" by simp
qed

lemma ideal_like_closed_plus:
  assumes p_in: "p \<in> ideal_like C B" and r_in: "r \<in> ideal_like C B"
  shows "p + r \<in> ideal_like C B"
  using p_in
proof (induct p)
  case ideal_like_0
  from r_in show "0 + r \<in> ideal_like C B" by simp
next
  case step: (ideal_like_plus a b q)
  have "(a + r) + q * b \<in> ideal_like C B" by (rule ideal_like_plus, fact+)
  thus "(a + q * b) + r \<in> ideal_like C B"
    by (metis ab_semigroup_add_class.add.commute semigroup_add_class.add.assoc)
qed

lemma ideal_like_closed_uminus:
  fixes B::"('a::comm_powerprod, 'b::ring) poly_mapping set"
  assumes "\<And>q. q \<in> C \<Longrightarrow> -q \<in> C"
  assumes p_in: "p \<in> ideal_like C B"
  shows "-p \<in> ideal_like C B"
  using p_in
proof (induct p)
  case ideal_like_0
  show "-0 \<in> ideal_like C B" by (simp, rule ideal_like_0)
next
  case step: (ideal_like_plus a b q)
  have eq: "- (a + q * b) = (-a) + ((-q) * b)" by simp
  from step(4) have "-q \<in> C" by (rule assms(1))
  have "0 + (-q) * b \<in> ideal_like C B" by (rule ideal_like_plus, fact ideal_like_0, fact+)
  hence "(-q) * b \<in> ideal_like C B" by simp
  with step(2) show "- (a + q * b) \<in> ideal_like C B" unfolding eq
    by (rule ideal_like_closed_plus)
qed

lemma ideal_like_closed_minus:
  fixes B::"('a::comm_powerprod, 'b::ring) poly_mapping set"
  assumes "\<And>q. q \<in> C \<Longrightarrow> -q \<in> C"
  assumes "p \<in> ideal_like C B" and "r \<in> ideal_like C B"
  shows "p - r \<in> ideal_like C B"
  using assms(2) assms(3) ideal_like_closed_plus ideal_like_closed_uminus[OF assms(1)] by fastforce

lemma ideal_like_closed_times:
  assumes "\<And>q. q \<in> C \<Longrightarrow> r * q \<in> C"
  assumes "p \<in> ideal_like C B"
  shows "r * p \<in> ideal_like C B"
  using assms(2)
proof (induct p)
  case ideal_like_0
  show "r * 0 \<in> ideal_like C B" by (simp, rule ideal_like_0)
next
  case step: (ideal_like_plus a b q)
  have *: "r * (a + q * b) = r * a + (r * q) * b" by (simp add: algebra_simps)
  show "r * (a + q * b) \<in> ideal_like C B" unfolding *
    by (rule ideal_like_plus, fact, fact, rule assms(1), fact)
qed

lemma ideal_like_closed_monom_mult:
  assumes "\<And>q. q \<in> C \<Longrightarrow> monom_mult c t q \<in> C"
  assumes "p \<in> ideal_like C B"
  shows "monom_mult c t p \<in> ideal_like C B"
  unfolding times_monomial_left[symmetric] using _ assms(2)
proof (rule ideal_like_closed_times)
  fix q
  assume "q \<in> C"
  thus "monomial c t * q \<in> C" unfolding times_monomial_left by (rule assms(1))
qed

lemma ideal_like_mono_1:
  assumes "C1 \<subseteq> C2"
  shows "ideal_like C1 B \<subseteq> ideal_like C2 B"
proof
  fix p
  assume "p \<in> ideal_like C1 B"
  thus "p \<in> ideal_like C2 B"
  proof (induct p rule: ideal_like.induct)
    case ideal_like_0
    show ?case ..
  next
    case step: (ideal_like_plus a b q)
    show ?case by (rule ideal_like_plus, fact, fact, rule, fact+)
  qed
qed

lemma ideal_like_mono_2:
  assumes "A \<subseteq> B"
  shows "ideal_like C A \<subseteq> ideal_like C B"
proof
  fix p
  assume "p \<in> ideal_like C A"
  thus "p \<in> ideal_like C B"
  proof (induct p rule: ideal_like.induct)
    case ideal_like_0
    show ?case ..
  next
    case step: (ideal_like_plus a b q)
    show ?case by (rule ideal_like_plus, fact, rule, fact+)
  qed
qed

lemma in_ideal_like_insertI:
  assumes "p \<in> ideal_like C B"
  shows "p \<in> ideal_like C (insert r B)"
  using assms
proof (induct p)
  case ideal_like_0
  show "0 \<in> ideal_like C (insert r B)" ..
next
  case step: (ideal_like_plus a b q)
  show "a + q * b \<in> ideal_like C (insert r B)"
  proof (rule, fact)
    from step(3) show "b \<in> insert r B" by simp
  qed fact
qed

lemma in_ideal_like_insertD:
  assumes "\<And>q1 q2. q1 \<in> C \<Longrightarrow> q2 \<in> C \<Longrightarrow> q1 * q2 \<in> C"
  assumes p_in: "p \<in> ideal_like C (insert r B)" and r_in: "r \<in> ideal_like C B"
  shows "p \<in> ideal_like C B"
  using p_in
proof (induct p)
  case ideal_like_0
  show "0 \<in> ideal_like C B" ..
next
  case step: (ideal_like_plus a b q)
  from step(3) have "b = r \<or> b \<in> B" by simp
  thus "a + q * b \<in> ideal_like C B"
  proof
    assume eq: "b = r"
    show ?thesis unfolding eq
      by (rule ideal_like_closed_plus, fact, rule ideal_like_closed_times, rule assms(1), rule step(4),
          assumption, fact)
  next
    assume "b \<in> B"
    show ?thesis by (rule, fact+)
  qed
qed

lemma ideal_like_insert:
  assumes "\<And>q1 q2. q1 \<in> C \<Longrightarrow> q2 \<in> C \<Longrightarrow> q1 * q2 \<in> C"
  assumes "r \<in> ideal_like C B"
  shows "ideal_like C (insert r B) = ideal_like C B"
proof (rule, rule)
  fix p
  assume "p \<in> ideal_like C (insert r B)"
  from assms(1) this assms(2) show "p \<in> ideal_like C B" by (rule in_ideal_like_insertD)
next
  show "ideal_like C B \<subseteq> ideal_like C (insert r B)"
  proof
    fix p
    assume "p \<in> ideal_like C B"
    thus "p \<in> ideal_like C (insert r B)" by (rule in_ideal_like_insertI)
  qed
qed

lemma ideal_like_insert_zero: "ideal_like C (insert 0 B) = ideal_like C B"
proof (rule, rule)
  fix p
  assume "p \<in> ideal_like C (insert 0 B)"
  thus "p \<in> ideal_like C B"
  proof (induct p)
    case ideal_like_0
    show "0 \<in> ideal_like C B" ..
  next
    case step: (ideal_like_plus a b q)
    from step(3) have "b = 0 \<or> b \<in> B" by simp
    thus "a + q * b \<in> ideal_like C B"
    proof
      assume "b = 0"
      thus ?thesis using step(2) by simp
    next
      assume "b \<in> B"
      show ?thesis by (rule, fact+)
    qed
  qed
next
  show "ideal_like C B \<subseteq> ideal_like C (insert 0 B)" by (rule ideal_like_mono_2, auto)
qed

lemma ideal_like_minus_singleton_zero: "ideal_like C (B - {0}) = ideal_like C B"
  by (metis ideal_like_insert_zero insert_Diff_single)

lemma ideal_like_empty_1: "ideal_like {} B = {0}"
proof (rule, rule)
  fix p::"('a, 'b) poly_mapping"
  assume "p \<in> ideal_like {} B"
  thus "p \<in> {0}" by (induct p, simp_all)
next
  show "{0} \<subseteq> ideal_like {} B" by (rule, simp add: ideal_like_0)
qed

lemma ideal_like_empty_2: "ideal_like C {} = {0}"
proof (rule, rule)
  fix p::"('a, 'b) poly_mapping"
  assume "p \<in> ideal_like C {}"
  thus "p \<in> {0}" by (induct p, simp_all)
next
  show "{0} \<subseteq> ideal_like C {}" by (rule, simp add: ideal_like_0)
qed
  
lemma generator_in_ideal_like:
  assumes "1 \<in> C" and "(f::('a::comm_powerprod, 'b::semiring_1) poly_mapping) \<in> B"
  shows "f \<in> ideal_like C B"
  by (rule, fact assms(2), rule generator_subset_ideal_like, fact)

lemma ideal_like_insert_subset:
  assumes "1 \<in> C" and "\<And>q1 q2. q1 \<in> C \<Longrightarrow> q2 \<in> C \<Longrightarrow> q1 * q2 \<in> C"
  assumes "ideal_like C A \<subseteq> ideal_like C B" and "r \<in> ideal_like C (B::('a::comm_powerprod, 'b::semiring_1) poly_mapping set)"
  shows "ideal_like C (insert r A) \<subseteq> ideal_like C B"
proof
  fix p
  assume "p \<in> ideal_like C (insert r A)"
  thus "p \<in> ideal_like C B"
  proof (induct p rule: ideal_like.induct)
    case ideal_like_0
    show ?case ..
  next
    case step: (ideal_like_plus a b q)
    show ?case
    proof (rule ideal_like_closed_plus)
      show "q * b \<in> ideal_like C B"
      proof (rule ideal_like_closed_times, rule assms(2), rule step(4), assumption)
        from \<open>b \<in> insert r A\<close> show "b \<in> ideal_like C B"
        proof
          assume "b = r"
          thus "b \<in> ideal_like C B" using \<open>r \<in> ideal_like C B\<close> by simp
        next
          assume "b \<in> A"
          hence "b \<in> ideal_like C A" using generator_subset_ideal_like[OF assms(1), of A] ..
          thus "b \<in> ideal_like C B" using \<open>ideal_like C A \<subseteq> ideal_like C B\<close> ..
        qed
      qed
    qed fact
  qed
qed

lemma in_ideal_like_finite_subset:
  assumes "p \<in> (ideal_like C B)"
  obtains A where "finite A" and "A \<subseteq> B" and "p \<in> (ideal_like C A)"
  using assms
proof (induct p arbitrary: thesis)
  case ideal_like_0
  show ?case
  proof (rule ideal_like_0(1))
    show "finite {}" ..
  next
    show "{} \<subseteq> B" ..
  qed (simp add: ideal_like_empty_2)
next
  case step: (ideal_like_plus p b q)
  obtain A where 1: "finite A" and 2: "A \<subseteq> B" and 3: "p \<in> (ideal_like C A)" by (rule step(2))
  let ?A = "insert b A"
  show ?case
  proof (rule step(5))
    from 1 show "finite ?A" ..
  next
    from step(3) 2 show "insert b A \<subseteq> B" by simp
  next
    show "p + q * b \<in> ideal_like C (insert b A)"
      by (rule ideal_like_plus, rule, fact 3, rule ideal_like_mono_2, auto intro: step(4))
  qed
qed

lemma in_ideal_like_finiteE:
  assumes "0 \<in> C" and C_closed: "\<And>q1 q2. q1 \<in> C \<Longrightarrow> q2 \<in> C \<Longrightarrow> q1 + q2 \<in> C"
  assumes fin: "finite B" and p_in: "p \<in> (ideal_like C B)"
  obtains q where "\<And>x. q x \<in> C" and "p = (\<Sum>b\<in>B. (q b) * b)"
  using p_in
proof (induct p arbitrary: thesis)
  case base: ideal_like_0
  let ?q = "\<lambda>_. (0::('a, 'b) poly_mapping)"
  show ?case
  proof (rule base(1))
    fix x
    from assms(1) show "?q x \<in> C" .
  next
    show "0 = (\<Sum>b\<in>B. ?q b * b)" by simp
  qed
next
  case step: (ideal_like_plus p b r)
  obtain q where *: "\<And>x. q x \<in> C" and **: "p = (\<Sum>b\<in>B. (q b) * b)" by (rule step(2), auto)
  let ?q = "q(b := (q b + r))"
  show ?case
  proof (rule step(5))
    have "p = q b * b + (\<Sum>b\<in>B - {b}. q b * b)"
      by (simp only: **, simp add: comm_monoid_add_class.sum.remove[OF assms(3) step(3)])
    thus "p + r * b = (\<Sum>b\<in>B. ?q b * b)"
      by (simp add: comm_monoid_add_class.sum.remove[OF assms(3) step(3)]
          algebra_simps times_monomial_left)
  next
    fix x
    show "?q x \<in> C" by (simp, intro conjI impI, rule C_closed, rule *, rule step(4), rule *)
  qed
qed

lemma in_ideal_likeE:
  assumes "0 \<in> C" and C_closed: "\<And>q1 q2. q1 \<in> C \<Longrightarrow> q2 \<in> C \<Longrightarrow> q1 + q2 \<in> C"
  assumes "p \<in> (ideal_like C B)"
  obtains A q where "finite A" and "A \<subseteq> B" and "\<And>x. q x \<in> C" and "p = (\<Sum>b\<in>A. (q b) * b)"
proof -
  from assms(3) obtain A where 1: "finite A" and 2: "A \<subseteq> B" and 3: "p \<in> ideal_like C A"
    by (rule in_ideal_like_finite_subset)
  from assms(1) assms(2) 1 3 obtain q where "\<And>x. q x \<in> C" and "p = (\<Sum>b\<in>A. (q b) * b)"
    by (rule in_ideal_like_finiteE, auto)
  with 1 2 show ?thesis ..
qed

lemma sum_in_ideal_likeI:
  assumes "\<And>b. b \<in> B \<Longrightarrow> q b \<in> C"
  shows "(\<Sum>b\<in>B. q b * b) \<in> ideal_like C B"
proof (cases "finite B")
  case True
  from this assms show ?thesis
  proof (induct B, simp add: ideal_like_0)
    case ind: (insert b B)
    have "(\<Sum>b\<in>B. q b * b) \<in> ideal_like C (insert b B)"
      by (rule, rule ind(3), rule ind(4), simp, rule ideal_like_mono_2, auto)
    moreover have "b \<in> insert b B" by simp
    moreover have "q b \<in> C" by (rule ind(4), simp)
    ultimately have "(\<Sum>b\<in>B. q b * b) + q b * b \<in> ideal_like C (insert b B)" by (rule ideal_like_plus)
    thus ?case unfolding sum.insert[OF ind(1) ind(2)] by (simp add: ac_simps)
  qed
next
  case False
  thus ?thesis by (simp add: ideal_like_0)
qed

lemma ideal_like_subset_ideal_likeI:
  assumes "\<And>r q. r \<in> C \<Longrightarrow> q \<in> C \<Longrightarrow> r * q \<in> C"
  assumes "A \<subseteq> ideal_like C B"
  shows "ideal_like C A \<subseteq> ideal_like C B"
proof
  fix p
  assume "p \<in> ideal_like C A"
  thus "p \<in> ideal_like C B"
  proof (induct p)
    case base: ideal_like_0
    show ?case by (fact ideal_like_0)
  next
    case step: (ideal_like_plus a b q)
    from step(3) assms(2) have "b \<in> ideal_like C B" ..
    with _ have "q * b \<in> ideal_like C B"
    proof (rule ideal_like_closed_times)
      fix r
      assume "r \<in> C"
      with step(4) show "q * r \<in> C" by (rule assms(1))
    qed
    with step(2) show ?case by (rule ideal_like_closed_plus)
  qed
qed

subsubsection \<open>Polynomial Ideals\<close>

definition pideal::"('a::comm_powerprod, 'b::semiring_0) poly_mapping set \<Rightarrow> ('a, 'b) poly_mapping set"
  where "pideal = ideal_like UNIV"

lemma zero_in_pideal: "0 \<in> pideal B"
  unfolding pideal_def by (rule ideal_like_0)

lemma times_in_pideal:
  assumes "b \<in> B"
  shows "q * b \<in> pideal B"
  unfolding pideal_def by (rule times_in_ideal_like, rule, fact)

lemma monom_mult_in_pideal:
  assumes "b \<in> B"
  shows "monom_mult c t b \<in> pideal B"
  unfolding pideal_def by (rule monom_mult_in_ideal_like, rule, fact)

lemma generator_subset_pideal:
  fixes B::"('a::comm_powerprod, 'b::semiring_1) poly_mapping set"
  shows "B \<subseteq> pideal B"
  unfolding pideal_def by (rule generator_subset_ideal_like, rule)

lemma pideal_closed_plus:
  assumes "p \<in> pideal B" and "q \<in> pideal B"
  shows "p + q \<in> pideal B"
  using assms unfolding pideal_def by (rule ideal_like_closed_plus)

lemma pideal_closed_uminus:
  fixes B::"('a::comm_powerprod, 'b::ring) poly_mapping set"
  assumes p_in: "p \<in> pideal B"
  shows "-p \<in> pideal B"
  using _ assms unfolding pideal_def by (rule ideal_like_closed_uminus, intro UNIV_I)

lemma pideal_closed_minus:
  fixes B::"('a::comm_powerprod, 'b::ring) poly_mapping set"
  assumes "p \<in> pideal B" and "q \<in> pideal B"
  shows "p - q \<in> pideal B"
  using assms pideal_closed_plus pideal_closed_uminus by fastforce

lemma pideal_closed_times:
  assumes "p \<in> pideal B"
  shows "q * p \<in> pideal B"
  using _ assms unfolding pideal_def by (rule ideal_like_closed_times, intro UNIV_I)

lemma pideal_closed_monom_mult:
  assumes "p \<in> pideal B"
  shows "monom_mult c t p \<in> pideal B"
  using _ assms unfolding pideal_def by (rule ideal_like_closed_monom_mult, intro UNIV_I)

lemma in_pideal_insertI:
  assumes "p \<in> pideal B"
  shows "p \<in> pideal (insert q B)"
  using assms unfolding pideal_def by (rule in_ideal_like_insertI)

lemma in_pideal_insertD:
  assumes "p \<in> pideal (insert q B)" and "q \<in> pideal B"
  shows "p \<in> pideal B"
  using _ assms unfolding pideal_def by (rule in_ideal_like_insertD, intro UNIV_I)

lemma pideal_insert:
  assumes "q \<in> pideal B"
  shows "pideal (insert q B) = pideal B"
  using _ assms unfolding pideal_def by (rule ideal_like_insert, intro UNIV_I)

lemma pideal_empty: "pideal {} = {0}"
  unfolding pideal_def by (fact ideal_like_empty_2)

lemma pideal_insert_zero: "pideal (insert 0 B) = pideal B"
  unfolding pideal_def by (fact ideal_like_insert_zero)

lemma pideal_minus_singleton_zero: "pideal (B - {0}) = pideal B"
  unfolding pideal_def by (fact ideal_like_minus_singleton_zero)
  
lemma generator_in_pideal:
  assumes "(f::('a::comm_powerprod, 'b::semiring_1) poly_mapping) \<in> B"
  shows "f \<in> pideal B"
  by (rule, fact assms, rule generator_subset_pideal)

lemma pideal_mono:
  assumes "A \<subseteq> B"
  shows "pideal A \<subseteq> pideal B"
  unfolding pideal_def using assms by (rule ideal_like_mono_2)

lemma pideal_insert_subset:
  assumes "pideal A \<subseteq> pideal B" and "q \<in> pideal (B::('a::comm_powerprod, 'b::semiring_1) poly_mapping set)"
  shows "pideal (insert q A) \<subseteq> pideal B"
  using _ _ assms unfolding pideal_def by (rule ideal_like_insert_subset, intro UNIV_I, intro UNIV_I)

lemma in_pideal_finite_subset:
  assumes "p \<in> (pideal B)"
  obtains A where "finite A" and "A \<subseteq> B" and "p \<in> (pideal A)"
  using assms unfolding pideal_def by (rule in_ideal_like_finite_subset)

lemma in_pideal_finiteE:
  assumes "finite B" and "p \<in> (pideal B)"
  obtains q where "p = (\<Sum>b\<in>B. (q b) * b)"
  using _ _ assms unfolding pideal_def by (rule in_ideal_like_finiteE, intro UNIV_I, intro UNIV_I)

lemma in_pidealE:
  assumes "p \<in> (pideal B)"
  obtains A q where "finite A" and "A \<subseteq> B" and "p = (\<Sum>b\<in>A. (q b) * b)"
proof -
  from assms obtain A where 1: "finite A" and 2: "A \<subseteq> B" and 3: "p \<in> pideal A"
    by (rule in_pideal_finite_subset)
  from 1 3 obtain q where "p = (\<Sum>b\<in>A. (q b) * b)" by (rule in_pideal_finiteE)
  with 1 2 show ?thesis ..
qed

lemma sum_in_pidealI: "(\<Sum>b\<in>B. q b * b) \<in> pideal B"
  unfolding pideal_def by (rule sum_in_ideal_likeI, intro UNIV_I)

lemma pideal_induct [consumes 1, case_names pideal_0 pideal_plus]:
  assumes "p \<in> pideal B" and "P 0" and "\<And>a p c t. a \<in> pideal B \<Longrightarrow> P a \<Longrightarrow> p \<in> B \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> P (a + monom_mult c t p)"
  shows "P p"
  using assms(1) unfolding pideal_def
proof (induct p)
  case ideal_like_0
  from assms(2) show ?case .
next
  case ind: (ideal_like_plus a b q)
  from this(1) this(2) show ?case
  proof (induct q arbitrary: a rule: poly_mapping_except_induct)
    case 1
    thus ?case by simp
  next
    case step: (2 q0 t)
    from this(4) have "a \<in> pideal B" by (simp only: pideal_def)
    from this step(5) \<open>b \<in> B\<close> have "P (a + monomial (lookup q0 t) t * b)" unfolding times_monomial_left
    proof (rule assms(3))
      from step(2) show "lookup q0 t \<noteq> 0" by simp
    qed
    with _ have "P ((a + monomial (lookup q0 t) t * b) + except q0 {t} * b)"
    proof (rule step(3))
      from step(4) \<open>b \<in> B\<close> show "a + monomial (lookup q0 t) t * b \<in> ideal_like UNIV B"
        by (rule ideal_like_plus, intro UNIV_I)
    qed
    hence "P (a + (monomial (lookup q0 t) t + except q0 {t}) * b)" by (simp add: algebra_simps)
    thus ?case by (simp only: plus_except[of q0 t, symmetric])
  qed
qed

lemma pideal_subset_pidealI:
  assumes "A \<subseteq> pideal B"
  shows "pideal A \<subseteq> pideal B"
  using _ assms unfolding pideal_def by (rule ideal_like_subset_ideal_likeI, intro UNIV_I)

lemma pideal_eq_UNIV_iff_contains_one:
  "pideal F = UNIV \<longleftrightarrow> (1::'a::comm_powerprod \<Rightarrow>\<^sub>0 'b::semiring_1) \<in> pideal F"
proof
  assume *: "1 \<in> pideal F"
  show "pideal F = UNIV"
  proof
    show "UNIV \<subseteq> pideal F"
    proof
      fix p
      from * have "p * 1 \<in> pideal F" by (rule pideal_closed_times)
      thus "p \<in> pideal F" by simp
    qed
  qed simp
qed simp

subsubsection \<open>Linear Hulls of Sets of Polynomials\<close>

definition phull::"('a::comm_powerprod, 'b::semiring_0) poly_mapping set \<Rightarrow> ('a, 'b) poly_mapping set"
  where "phull = ideal_like {monomial c 0 | c. True}"

lemma zero_in_phull: "0 \<in> phull B"
  unfolding phull_def by (rule ideal_like_0)

lemma times_in_phull:
  assumes "b \<in> B"
  shows "monomial c 0 * b \<in> phull B"
  unfolding phull_def by (rule times_in_ideal_like, auto intro: assms)

lemma monom_mult_in_phull:
  assumes "b \<in> B"
  shows "monom_mult c 0 b \<in> phull B"
  unfolding phull_def by (rule monom_mult_in_ideal_like, auto intro: assms)

lemma generator_subset_phull:
  fixes B::"('a::comm_powerprod, 'b::semiring_1) poly_mapping set"
  shows "B \<subseteq> phull B"
  unfolding phull_def
proof (rule generator_subset_ideal_like, simp, rule)
  show "monomial 1 0 = 1" by simp
qed

lemma phull_closed_plus:
  assumes "p \<in> phull B" and "q \<in> phull B"
  shows "p + q \<in> phull B"
  using assms unfolding phull_def by (rule ideal_like_closed_plus)

lemma phull_closed_uminus:
  fixes B::"('a::comm_powerprod, 'b::ring) poly_mapping set"
  assumes p_in: "p \<in> phull B"
  shows "-p \<in> phull B"
  using _ assms unfolding phull_def
  by (rule ideal_like_closed_uminus, auto simp add: single_uminus[symmetric])

lemma phull_closed_minus:
  fixes B::"('a::comm_powerprod, 'b::ring) poly_mapping set"
  assumes "p \<in> phull B" and "q \<in> phull B"
  shows "p - q \<in> phull B"
  using assms phull_closed_plus phull_closed_uminus by fastforce

lemma phull_closed_times:
  assumes "p \<in> phull B"
  shows "monomial c 0 * p \<in> phull B"
  using _ assms unfolding phull_def by (rule ideal_like_closed_times, auto simp add: mult_single)

lemma phull_closed_monom_mult:
  assumes "p \<in> phull B"
  shows "monom_mult c 0 p \<in> phull B"
  using _ assms unfolding phull_def by (rule ideal_like_closed_monom_mult, auto simp add: monom_mult_monomial)

lemma in_phull_insertI:
  assumes "p \<in> phull B"
  shows "p \<in> phull (insert q B)"
  using assms unfolding phull_def by (rule in_ideal_like_insertI)

lemma in_phull_insertD:
  assumes "p \<in> phull (insert q B)" and "q \<in> phull B"
  shows "p \<in> phull B"
  using _ assms unfolding phull_def by (rule in_ideal_like_insertD, auto simp add: mult_single)

lemma phull_insert:
  assumes "q \<in> phull B"
  shows "phull (insert q B) = phull B"
  using _ assms unfolding phull_def by (rule ideal_like_insert, auto simp add: mult_single)

lemma phull_empty: "phull {} = {0}"
  unfolding phull_def by (fact ideal_like_empty_2)

lemma phull_insert_zero: "phull (insert 0 B) = phull B"
  unfolding phull_def by (fact ideal_like_insert_zero)

lemma phull_minus_singleton_zero: "phull (B - {0}) = phull B"
  unfolding phull_def by (fact ideal_like_minus_singleton_zero)
  
lemma generator_in_phull:
  assumes "(f::('a::comm_powerprod, 'b::semiring_1) poly_mapping) \<in> B"
  shows "f \<in> phull B"
  by (rule, fact assms, rule generator_subset_phull)

lemma phull_mono:
  assumes "A \<subseteq> B"
  shows "phull A \<subseteq> phull B"
  unfolding phull_def using assms by (rule ideal_like_mono_2)

lemma phull_subset_pideal: "phull B \<subseteq> pideal B"
  unfolding phull_def pideal_def by (rule ideal_like_mono_1, simp)

lemma phull_insert_subset:
  assumes "phull A \<subseteq> phull B" and "q \<in> phull (B::('a::comm_powerprod, 'b::semiring_1) poly_mapping set)"
  shows "phull (insert q A) \<subseteq> phull B"
  using _ _ assms unfolding phull_def
proof (rule ideal_like_insert_subset, simp, intro exI)
  show "monomial 1 0 = 1" by simp
qed (auto simp add: mult_single)

lemma in_phull_finite_subset:
  assumes "p \<in> phull B"
  obtains A where "finite A" and "A \<subseteq> B" and "p \<in> phull A"
  using assms unfolding phull_def by (rule in_ideal_like_finite_subset)

lemma in_phull_finiteE:
  assumes "finite B" and "p \<in> phull B"
  obtains c where "p = (\<Sum>b\<in>B. monom_mult (c b) 0 b)"
proof -
  from _ _ assms obtain q where *: "\<And>x. q x \<in> {monomial c 0 | c. True}" and **: "p = (\<Sum>b\<in>B. q b * b)"
    unfolding phull_def
  proof (rule in_ideal_like_finiteE, simp, intro exI)
    show "monomial 0 0 = 0" by simp
  next
    fix q1 q2::"('a, 'b) poly_mapping"
    assume "q1 \<in> {monomial c 0 |c. True}" and "q2 \<in> {monomial c 0 |c. True}"
    thus "q1 + q2 \<in> {monomial c 0 |c. True}" by (auto, metis single_add)
  qed auto
  from * have "\<forall>x. \<exists>c. q x = monomial c 0" by simp
  hence "\<exists>c. \<forall>x. q x = monomial (c x) 0" by (rule choice)
  then obtain c where ***: "\<And>x. q x = monomial (c x) 0" by auto
  show ?thesis
  proof
    show "p = (\<Sum>b\<in>B. monom_mult (c b) 0 b)" by (simp only: ** *** times_monomial_left)
  qed
qed

lemma in_phullE:
  assumes "p \<in> phull B"
  obtains A c where "finite A" and "A \<subseteq> B" and "p = (\<Sum>b\<in>A. monom_mult (c b) 0 b)"
proof -
  from assms obtain A where 1: "finite A" and 2: "A \<subseteq> B" and 3: "p \<in> phull A"
    by (rule in_phull_finite_subset)
  from 1 3 obtain c where "p = (\<Sum>b\<in>A. monom_mult (c b) 0 b)" by (rule in_phull_finiteE)
  with 1 2 show ?thesis ..
qed

lemma sum_in_phullI: "(\<Sum>b\<in>B. monom_mult (c b) 0 b) \<in> phull B"
  unfolding phull_def times_monomial_left[symmetric] by (rule sum_in_ideal_likeI, auto)

lemma phull_induct [consumes 1, case_names phull_0 phull_plus]:
  assumes "p \<in> phull B" and "P 0" and "\<And>a p c. a \<in> phull B \<Longrightarrow> P a \<Longrightarrow> p \<in> B \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> P (a + monom_mult c 0 p)"
  shows "P p"
  using assms(1) unfolding phull_def
proof (induct p)
  case ideal_like_0
  from assms(2) show ?case .
next
  case ind: (ideal_like_plus a b q)
  from this(1) have "a \<in> phull B" by (simp only: phull_def)
  from ind(4) obtain c where q: "q = monomial c 0" by auto
  show ?case
  proof (cases "c = 0")
    case True
    from ind(2) show ?thesis unfolding q True by simp
  next
    case False
    from \<open>a \<in> phull B\<close> ind(2) ind(3) False show ?thesis unfolding q times_monomial_left by (rule assms(3))
  qed
qed

lemma phull_subset_phullI:
  assumes "A \<subseteq> phull B"
  shows "phull A \<subseteq> phull B"
  using _ assms unfolding phull_def by (rule ideal_like_subset_ideal_likeI, auto simp add: mult_single)

subsection \<open>Polynomials in Ordered Power-products\<close>

context ordered_powerprod
begin

definition higher::"('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)" where
  "higher p t = except p {s. s \<preceq> t}"

definition lower::"('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)" where
  "lower p t = except p {s. t \<preceq> s}"

definition lp::"('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 'a" where
  "lp p \<equiv> (if p = 0 then 0 else ordered_powerprod_lin.Max (keys p))"

definition lc::"('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 'b" where
  "lc p \<equiv> Poly_Mapping.lookup p (lp p)"

definition tail::"('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)" where
  "tail p \<equiv> lower p (lp p)"

subsubsection \<open>@{term higher} and @{term lower}\<close>

lemma lookup_higher: "lookup (higher p s) t = (if s \<prec> t then lookup p t else 0)"
  by (auto simp add: higher_def lookup_except)

lemma lookup_higher_when: "lookup (higher p s) t = (lookup p t when s \<prec> t)"
  by (auto simp add: lookup_higher when_def)

lemma higher_plus: "higher (p + q) t = higher p t + higher q t"
  by (rule poly_mapping_eqI, simp add: lookup_add lookup_higher)

lemma higher_uminus: "higher (-p) t = -(higher p t)"
  by (rule poly_mapping_eqI, simp add: lookup_higher)

lemma higher_minus: "higher (p - q) t = higher p t - higher q t"
  by (auto intro!: poly_mapping_eqI simp: lookup_minus lookup_higher)

lemma higher_zero[simp]: "higher 0 t = 0"
  by (rule poly_mapping_eqI, simp add: lookup_higher)

lemma higher_eq_iff: "higher p t = higher q t \<longleftrightarrow> (\<forall>s. t \<prec> s \<longrightarrow> lookup p s = lookup q s)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R
  proof (intro allI impI)
    fix s
    assume "t \<prec> s"
    moreover from \<open>?L\<close> have "lookup (higher p t) s = lookup (higher q t) s" by simp
    ultimately show "lookup p s = lookup q s" by (simp add: lookup_higher)
  qed
next
  assume ?R
  show ?L
  proof (rule poly_mapping_eqI, simp add: lookup_higher, rule)
    fix s
    assume "t \<prec> s"
    with \<open>?R\<close> show "lookup p s = lookup q s" by simp
  qed
qed

lemma higher_eq_zero_iff: "higher p t = 0 \<longleftrightarrow> (\<forall>s. t \<prec> s \<longrightarrow> lookup p s = 0)"
proof -
  have "higher p t = higher 0 t \<longleftrightarrow> (\<forall>s. t \<prec> s \<longrightarrow> lookup p s = lookup 0 s)" by (rule higher_eq_iff)
  thus ?thesis by simp
qed

lemma keys_higher: "keys (higher p t) = {s\<in>(keys p). t \<prec> s}"
  by (rule set_eqI, simp only: in_keys_iff, simp add: lookup_higher)

lemma higher_higher: "higher (higher p s) t = higher p (ordered_powerprod_lin.max s t)"
  by (rule poly_mapping_eqI, simp add: lookup_higher)

lemma lookup_lower: "lookup (lower p s) t = (if t \<prec> s then lookup p t else 0)"
  by (auto simp add: lower_def lookup_except)

lemma lookup_lower_when: "lookup (lower p s) t = (lookup p t when t \<prec> s)"
  by (auto simp add: lookup_lower when_def)

lemma lower_plus: "lower (p + q) t = lower p t + lower q t"
  by (rule poly_mapping_eqI, simp add: lookup_add lookup_lower)

lemma lower_uminus: "lower (-p) t = -(lower p t)"
  by (rule poly_mapping_eqI, simp add: lookup_lower)

lemma lower_minus:  "lower (p - (q::('a, 'b::ab_group_add) poly_mapping)) t = lower p t - lower q t"
   by (auto intro!: poly_mapping_eqI simp: lookup_minus lookup_lower)

lemma lower_zero[simp]: "lower 0 t = 0"
  by (rule poly_mapping_eqI, simp add: lookup_lower)

lemma lower_eq_iff: "lower p t = lower q t \<longleftrightarrow> (\<forall>s. s \<prec> t \<longrightarrow> lookup p s = lookup q s)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R
  proof (intro allI impI)
    fix s
    assume "s \<prec> t"
    moreover from \<open>?L\<close> have "lookup (lower p t) s = lookup (lower q t) s" by simp
    ultimately show "lookup p s = lookup q s" by (simp add: lookup_lower)
  qed
next
  assume ?R
  show ?L
  proof (rule poly_mapping_eqI, simp add: lookup_lower, rule)
    fix s
    assume "s \<prec> t"
    with \<open>?R\<close> show "lookup p s = lookup q s" by simp
  qed
qed

lemma lower_eq_zero_iff: "lower p t = 0 \<longleftrightarrow> (\<forall>s. s \<prec> t \<longrightarrow> lookup p s = 0)"
proof -
  have "lower p t = lower 0 t \<longleftrightarrow> (\<forall>s. s \<prec> t \<longrightarrow> lookup p s = lookup 0 s)" by (rule lower_eq_iff)
  thus ?thesis by simp
qed

lemma keys_lower: "keys (lower p t) = {s\<in>(keys p). s \<prec> t}"
  by (rule set_eqI, simp only: in_keys_iff, simp add: lookup_lower)

lemma lower_lower: "lower (lower p s) t = lower p (ordered_powerprod_lin.min s t)"
  by (rule poly_mapping_eqI, simp add: lookup_lower)

subsubsection \<open>Leading Power-Product and Leading Coefficient: @{term lp} and @{term lc}\<close>

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

lemma lp_in_keys:
  assumes "p \<noteq> 0"
  shows "lp p \<in> (keys p)"
  by (metis assms in_keys_iff lc_def lc_not_0)

lemma lp_monomial:
  assumes "c \<noteq> 0"
  shows "lp (monomial c t) = t"
  by (metis assms lookup_single_eq lookup_single_not_eq lp_eqI ordered_powerprod_lin.eq_iff)

lemma lc_monomial:
  assumes "c \<noteq> 0"
  shows "lc (monomial c t) = c"
  unfolding lc_def lp_monomial[OF assms] by simp

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
  by (simp add: assms(1) assms(2) lc_def lp_mult lookup_monom_mult)

lemma lookup_mult_0:
  fixes c::"'b::semiring_no_zero_divisors"
  assumes "s + lp p \<prec> t"
  shows "lookup (monom_mult c s p) t = 0"
  by (metis assms aux lp_gr lp_mult monom_mult_left0 monom_mult_right0
      ordered_powerprod_lin.order.strict_implies_not_eq)

lemma lp_le:
  assumes a: "\<And>s. t \<prec> s \<Longrightarrow> lookup p s = 0"
  shows "lp p \<preceq> t"
proof (cases "p = 0")
  case True
  thus ?thesis using zero_min[of t] by (simp add: lp_def)
next
  case False
  hence "keys p \<noteq> {}" using keys_eq_empty_iff[of p] by simp
  have "\<forall>s\<in>keys p. s \<preceq> t"
  proof
    fix s::"'a"
    assume "s \<in> keys p"
    hence "lookup p s \<noteq> 0" unfolding keys_def by simp
    hence "\<not> t \<prec> s" using a[of s] by auto
    thus "s \<preceq> t" by simp
  qed
  with lp_alt[OF \<open>p \<noteq> 0\<close>] ordered_powerprod_lin.Max_le_iff[OF finite_keys[of p] \<open>keys p \<noteq> {}\<close>]
    show ?thesis by simp
qed
   
lemma lp_le_iff: "lp p \<preceq> t \<longleftrightarrow> (\<forall>s. t \<prec> s \<longrightarrow> lookup p s = 0)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R
  proof (intro allI impI)
    fix s
    note \<open>lp p \<preceq> t\<close>
    also assume "t \<prec> s"
    finally have "lp p \<prec> s" .
    hence "\<not> s \<preceq> lp p" by simp
    with lp_max[of p s] show "lookup p s = 0" by blast
  qed
next
  assume ?R
  thus ?L using lp_le by auto
qed

lemma lp_plus_eqI:
  assumes "lp p \<prec> lp q"
  shows "lp (p + q) = lp q"
proof (cases "q = 0")
  case True
  with assms have "lp p \<prec> 0" by (simp add: lp_def)
  with zero_min[of "lp p"] show ?thesis by simp
next
  case False
  show ?thesis
  proof (intro lp_eqI)
    from lp_gr[of p "lp q" "lp p"] \<open>lp p \<prec> lp q\<close> have "lookup p (lp q) = 0" by blast
    with lookup_add[of p q "lp q"] lc_not_0[OF False] show "lookup (p + q) (lp q) \<noteq> 0"
      unfolding lc_def by simp
  next
    fix s
    assume "lookup (p + q) s \<noteq> 0"
    show "s \<preceq> lp q"
    proof (rule ccontr)
      assume "\<not> s \<preceq> lp q"
      hence qs: "lp q \<prec> s" by simp
      hence "lp p \<prec> s" using \<open>lp p \<prec> lp q\<close> by simp
      with lp_gr[of p s "lp p"] have "lookup p s = 0" by blast
      also from qs lp_gr[of q s "lp q"] have "lookup q s = 0" by blast
      ultimately show False using \<open>lookup (p + q) s \<noteq> 0\<close> lookup_add[of p q s] by auto
    qed
  qed
qed

lemma lp_plus_eqI_2:
  assumes "lp q \<prec> lp p"
  shows "lp (p + q) = lp p"
proof (cases "p = 0")
  case True
  with assms have "lp q \<prec> 0" by (simp add: lp_def)
  with zero_min[of "lp q"] show ?thesis by simp
next
  case False
  show ?thesis
  proof (intro lp_eqI)
    from lp_gr[of q "lp p" "lp q"] \<open>lp q \<prec> lp p\<close> have "lookup q (lp p) = 0" by blast
    with lookup_add[of p q "lp p"] lc_not_0[OF False] show "lookup (p + q) (lp p) \<noteq> 0"
      unfolding lc_def by simp
  next
    fix s
    assume "lookup (p + q) s \<noteq> 0"
    show "s \<preceq> lp p"
    proof (rule ccontr)
      assume "\<not> s \<preceq> lp p"
      hence ps: "lp p \<prec> s" by simp
      hence "lp q \<prec> s" using \<open>lp q \<prec> lp p\<close> by simp
      with lp_gr[of q s "lp q"] have "lookup q s = 0" by blast
      also from ps lp_gr[of p s "lp p"] have "lookup p s = 0" by blast
      ultimately show False using \<open>lookup (p + q) s \<noteq> 0\<close> lookup_add[of p q s] by auto
    qed
  qed
qed
    
lemma lp_plus_lessE:
  assumes "lp p \<prec> lp (p + (q::('a, 'b::monoid_add) poly_mapping))"
  shows "lp p \<prec> lp q"
proof (rule ccontr)
  assume "\<not> lp p \<prec> lp q"
  hence "lp p = lp q \<or> lp q \<prec> lp p" by auto
  thus False
  proof
    assume lp_eq: "lp p = lp q"
    have "lp (p + q) \<preceq> lp p"
    proof (rule lp_le)
      fix s
      assume "lp p \<prec> s"
      with lp_gr[of p s "lp p"] have "lookup p s = 0" by blast
      from \<open>lp p \<prec> s\<close> have "lp q \<prec> s" using lp_eq by simp
      with lp_gr[of q s "lp q"] have "lookup q s = 0" by blast
      with \<open>lookup p s = 0\<close> show "lookup (p + q) s = 0" using lookup_add[of p q s] by simp
    qed
    with assms show False by simp
  next
    assume "lp q \<prec> lp p"
    from lp_plus_eqI_2[OF this] assms show False by simp
  qed
qed
  
lemma lp_plus_lessI:
  fixes p q :: "('a, 'b::ring) poly_mapping"
  assumes "p + q \<noteq> 0" and lp_eq: "lp q = lp p" and lc_eq: "lc q = - lc p"
  shows "lp (p + q) \<prec> lp p"
proof (rule ccontr)
  assume "\<not> lp (p + q) \<prec> lp p"
  hence "lp (p + q) = lp p \<or> lp p \<prec> lp (p + q)" by auto
  thus False
  proof
    assume "lp (p + q) = lp p"
    have "lookup (p + q) (lp p) = (lookup p (lp p)) + (lookup q (lp q))" unfolding lp_eq lookup_add ..
    also have "... = lc p + lc q" unfolding lc_def ..
    also have "... = 0" unfolding lc_eq by simp
    finally have "lookup (p + q) (lp p) = 0" .
    hence "lp (p + q) \<noteq> lp p" using lc_not_0[OF \<open>p + q \<noteq> 0\<close>] unfolding lc_def by auto
    with \<open>lp (p + q) = lp p\<close> show False by simp
  next
    assume "lp p \<prec> lp (p + q)"
    have "lp p \<prec> lp q" by (rule lp_plus_lessE, fact+)
    hence "lp p \<noteq> lp q" by simp
    with lp_eq show False by simp
  qed
qed

lemma lp_plus_distinct_eq_max:
  assumes "lp p \<noteq> lp q"
  shows "lp (p + q) = ordered_powerprod_lin.max (lp p) (lp q)"
proof (rule ordered_powerprod_lin.linorder_cases)
  assume a: "lp p \<prec> lp q"
  hence "lp (p + q) = lp q" by (rule lp_plus_eqI)
  also from a have "... = ordered_powerprod_lin.max (lp p) (lp q)"
    by (simp add: ordered_powerprod_lin.max.absorb2)
  finally show ?thesis .
next
  assume a: "lp q \<prec> lp p"
  hence "lp (p + q) = lp p" by (rule lp_plus_eqI_2)
  also from a have "... = ordered_powerprod_lin.max (lp p) (lp q)"
    by (simp add: ordered_powerprod_lin.max.absorb1)
  finally show ?thesis .
next
  assume "lp p = lp q"
  with assms show ?thesis ..
qed

lemma lp_plus_le_max: "lp (p + q) \<preceq> ordered_powerprod_lin.max (lp p) (lp q)"
proof (cases "lp p = lp q")
  case True
  show ?thesis
  proof (rule lp_le)
    fix s
    assume "ordered_powerprod_lin.max (lp p) (lp q) \<prec> s"
    hence "lp p \<prec> s" and "lp q \<prec> s" by simp_all
    hence "lookup p s = 0" and "lookup q s = 0" using lp_max ordered_powerprod_lin.leD by blast+
    thus "lookup (p + q) s = 0" by (simp add: lookup_add)
  qed
next
  case False
  hence "lp (p + q) = ordered_powerprod_lin.max (lp p) (lp q)" by (rule lp_plus_distinct_eq_max)
  thus ?thesis by simp
qed
    
lemma lp_max_keys:
  assumes "t \<in> keys p"
  shows "t \<preceq> lp p"
proof (rule lp_max)
  from assms show "lookup p t \<noteq> 0" by simp
qed

lemma lp_eqI_keys:
  assumes "t \<in> keys p" and a2: "\<And>s. s \<in> keys p \<Longrightarrow> s \<preceq> t"
  shows "lp p = t"
  by (rule lp_eqI, simp_all only: in_keys_iff[symmetric], fact+)
    
lemma lp_gr_keys:
  assumes "s \<in> keys p" and "t \<prec> s"
  shows "t \<prec> lp p"
proof (rule lp_gr)
  from assms(1) show "lookup p s \<noteq> 0" by simp
qed fact

lemma lp_uminus: "lp (-p) = lp p"
  by (simp add: lp_def keys_uminus)

lemma lc_uminus: "lc (-p) = - lc p"
  by (simp add: lc_def lp_uminus)

subsubsection \<open>Trailing Power-Product and Trailing Coefficient: @{term tp} and @{term tc}\<close>

definition tp::"('a, 'b::zero) poly_mapping \<Rightarrow> 'a" where
  "tp p \<equiv> (if p = 0 then 0 else ordered_powerprod_lin.Min (keys p))"

definition tc::"('a, 'b::zero) poly_mapping \<Rightarrow> 'b" where
  "tc p \<equiv> lookup p (tp p)"
  
lemma tp_alt:
  assumes "p \<noteq> 0"
  shows "tp p = ordered_powerprod_lin.Min (keys p)"
using assms unfolding tp_def by simp

lemma tp_min_keys:
  assumes "t \<in> keys p"
  shows "tp p \<preceq> t"
proof -
  from assms have "keys p \<noteq> {}" by auto
  hence "p \<noteq> 0" by simp
  from tp_alt[OF this] ordered_powerprod_lin.Min_le[OF finite_keys assms] show ?thesis by simp
qed

lemma tp_min:
  assumes "lookup p t \<noteq> 0"
  shows "tp p \<preceq> t"
proof -
  from assms have t_in: "t \<in> keys p" unfolding keys_def by simp
  thus ?thesis by (rule tp_min_keys)
qed
  
lemma tp_in_keys:
  assumes "p \<noteq> 0"
  shows "tp p \<in> keys p"
  unfolding tp_alt[OF assms]
  by (rule ordered_powerprod_lin.Min_in, fact finite_keys, simp add: assms)

lemma tp_eqI:
  assumes a1: "t \<in> keys p" and a2: "\<And>s. s \<in> keys p \<Longrightarrow> t \<preceq> s"
  shows "tp p = t"
proof -
  from a1 have "keys p \<noteq> {}" by auto
  hence "p \<noteq> 0" by simp
  from a1 have "tp p \<preceq> t" by (rule tp_min_keys)
  moreover have "t \<preceq> tp p" by (rule a2, rule tp_in_keys, fact \<open>p \<noteq> 0\<close>)
  ultimately show ?thesis by simp
qed

lemma tp_gr:
  assumes a: "\<And>s. s \<in> keys p \<Longrightarrow> t \<prec> s" and "p \<noteq> 0"
  shows "t \<prec> tp p"
proof -
  from \<open>p \<noteq> 0\<close> have "keys p \<noteq> {}" using keys_eq_empty_iff[of p] by simp
  show ?thesis by (rule a, rule tp_in_keys, fact \<open>p \<noteq> 0\<close>)
qed

lemma tp_less:
  assumes "s \<in> keys p" and "s \<prec> t"
  shows "tp p \<prec> t"
proof -
  from \<open>s \<in> keys p\<close> have "tp p \<preceq> s" by (rule tp_min_keys)
  also have "... \<prec> t" by fact
  finally show "tp p \<prec> t" .
qed
  
lemma tp_ge:
  assumes a: "\<And>s. s \<prec> t \<Longrightarrow> lookup p s = 0" and "p \<noteq> 0"
  shows "t \<preceq> tp p"
proof -
  from \<open>p \<noteq> 0\<close> have "keys p \<noteq> {}" using keys_eq_empty_iff[of p] by simp
  have "\<forall>s\<in>keys p. t \<preceq> s"
  proof
    fix s::"'a"
    assume "s \<in> keys p"
    hence "lookup p s \<noteq> 0" unfolding keys_def by simp
    hence "\<not> s \<prec> t" using a[of s] by auto
    thus "t \<preceq> s" by simp
  qed
  with tp_alt[OF \<open>p \<noteq> 0\<close>] ordered_powerprod_lin.Min_ge_iff[OF finite_keys[of p] \<open>keys p \<noteq> {}\<close>]
    show ?thesis by simp
qed
  
lemma tp_ge_keys:
  assumes a: "\<And>s. s \<in> keys p \<Longrightarrow> t \<preceq> s" and "p \<noteq> 0"
  shows "t \<preceq> tp p"
  by (rule a, rule tp_in_keys, fact)
    
lemma tp_ge_iff: "t \<preceq> tp p \<longleftrightarrow> ((p \<noteq> 0 \<or> t = 0) \<and> (\<forall>s. s \<prec> t \<longrightarrow> lookup p s = 0))" (is "?L \<longleftrightarrow> (?A \<and> ?B)")
proof
  assume ?L
  show "?A \<and> ?B"
  proof (intro conjI allI impI)
    show "p \<noteq> 0 \<or> t = 0"
    proof (cases "p = 0")
      case True
      show ?thesis
      proof (rule disjI2)
        from \<open>?L\<close> True have "t \<preceq> 0" by (simp add: tp_def)
        with zero_min[of t] show "t = 0" by simp
      qed
    next
      case False
      thus ?thesis ..
    qed
  next
    fix s
    assume "s \<prec> t"
    also note \<open>t \<preceq> tp p\<close>
    finally have "s \<prec> tp p" .
    hence "\<not> tp p \<preceq> s" by simp
    with tp_min[of p s] show "lookup p s = 0" by blast
  qed
next
  assume "?A \<and> ?B"
  hence ?A and ?B by simp_all
  show ?L
  proof (cases "p = 0")
    case True
    with \<open>?A\<close> have "t = 0" by simp
    with True show ?thesis by (simp add: tp_def)
  next
    case False
    from \<open>?B\<close> show ?thesis using tp_ge[OF _ False] by auto
  qed
qed

lemma tc_not_0:
  assumes "p \<noteq> 0"
  shows "tc p \<noteq> 0"
  unfolding tc_def in_keys_iff[symmetric] using assms by (rule tp_in_keys)

lemma tp_monomial:
  assumes "c \<noteq> 0"
  shows "tp (monomial c t) = t"
proof (rule tp_eqI)
  from keys_of_monomial[OF assms, of t] show "t \<in> keys (monomial c t)" by simp
next
  fix s
  assume "s \<in> keys (monomial c t)"
  with keys_of_monomial[OF assms, of t] have "s = t" by simp
  thus "t \<preceq> s" by simp
qed

lemma tc_monomial:
  assumes "c \<noteq> 0"
  shows "tc (monomial c t) = c"
  unfolding tc_def tp_monomial[OF assms] by (simp add: lookup_single)

lemma tp_monom_mult:
  fixes c::"'b::semiring_no_zero_divisors"
  assumes "c \<noteq> 0" and "p \<noteq> 0"
  shows "tp (monom_mult c t p) = t + tp p"
proof (intro tp_eqI, rule keys_monom_multI, rule tp_in_keys, fact, fact)
  fix s
  assume "s \<in> keys (monom_mult c t p)"
  then obtain x where "x \<in> keys p" and s: "s = t + x" by (rule keys_monom_multE)
  show "t + tp p \<preceq> s" unfolding s add.commute[of t] by (rule plus_monotone, rule tp_min_keys, fact)
qed

lemma tc_monom_mult:
  fixes c::"'b::semiring_no_zero_divisors"
  assumes "c \<noteq> 0" and "p \<noteq> 0"
  shows "tc (monom_mult c t p) = c * tc p"
  unfolding tc_def tp_monom_mult[OF assms] lookup_monom_mult ..
  
lemma tp_plus_eqI:
  fixes p q
  assumes "p \<noteq> 0" and "tp p \<prec> tp q"
  shows "tp (p + q) = tp p"
proof (intro tp_eqI)
  from tp_less[of "tp p" q "tp q"] \<open>tp p \<prec> tp q\<close> have "tp p \<notin> keys q" by blast
  with lookup_add[of p q "tp p"] tc_not_0[OF \<open>p \<noteq> 0\<close>] show "tp p \<in> keys (p + q)"
    unfolding in_keys_iff tc_def by simp
next
  fix s
  assume "s \<in> keys (p + q)"
  show "tp p \<preceq> s"
  proof (rule ccontr)
    assume "\<not> tp p \<preceq> s"
    hence sp: "s \<prec> tp p" by simp
    hence "s \<prec> tp q" using \<open>tp p \<prec> tp q\<close> by simp
    with tp_less[of s q "tp q"] have "s \<notin> keys q" by blast
    moreover from sp tp_less[of s p "tp p"] have "s \<notin> keys p" by blast
    ultimately show False using \<open>s \<in> keys (p + q)\<close> keys_add_subset[of p q] by auto
  qed
qed
    
lemma tp_plus_lessE:
  fixes p q
  assumes "p + q \<noteq> 0" and tp: "tp (p + q) \<prec> tp p"
  shows "tp q \<prec> tp p"
proof (cases "p = 0")
  case True
  with tp show ?thesis by simp
next
  case False
  show ?thesis
  proof (rule ccontr)
    assume "\<not> tp q \<prec> tp p"
    hence "tp p = tp q \<or> tp p \<prec> tp q" by auto
    thus False
    proof
      assume tp_eq: "tp p = tp q"
      have "tp p \<preceq> tp (p + q)"
      proof (rule tp_ge_keys)
        fix s
        assume "s \<in> keys (p + q)"
        hence "s \<in> keys p \<union> keys q"
        proof
          show "keys (p + q) \<subseteq> keys p \<union> keys q" by (fact keys_add_subset)
        qed
        thus "tp p \<preceq> s"
        proof
          assume "s \<in> keys p"
          thus ?thesis by (rule tp_min_keys)
        next
          assume "s \<in> keys q"
          thus ?thesis unfolding tp_eq by (rule tp_min_keys)
        qed
      qed (fact \<open>p + q \<noteq> 0\<close>)
      with tp show False by simp
    next
      assume "tp p \<prec> tp q"
      from tp_plus_eqI[OF False this] tp show False by (simp add: ac_simps)
    qed
  qed
qed
  
lemma tp_plus_lessI:
  fixes p q :: "('a, 'b::ring) poly_mapping"
  assumes "p + q \<noteq> 0" and tp_eq: "tp q = tp p" and tc_eq: "tc q = - tc p"
  shows "tp p \<prec> tp (p + q)"
proof (rule ccontr)
  assume "\<not> tp p \<prec> tp (p + q)"
  hence "tp p = tp (p + q) \<or> tp (p + q) \<prec> tp p" by auto
  thus False
  proof
    assume "tp p = tp (p + q)"
    have "lookup (p + q) (tp p) = (lookup p (tp p)) + (lookup q (tp q))" unfolding tp_eq lookup_add ..
    also have "... = tc p + tc q" unfolding tc_def ..
    also have "... = 0" unfolding tc_eq by simp
    finally have "lookup (p + q) (tp p) = 0" .
    hence "tp (p + q) \<noteq> tp p" using tc_not_0[OF \<open>p + q \<noteq> 0\<close>] unfolding tc_def by auto
    with \<open>tp p = tp (p + q)\<close> show False by simp
  next
    assume "tp (p + q) \<prec> tp p"
    have "tp q \<prec> tp p" by (rule tp_plus_lessE, fact+)
    hence "tp q \<noteq> tp p" by simp
    with tp_eq show False by simp
  qed
qed

lemma tp_uminus: "tp (-p) = tp p"
  by (simp add: tp_def keys_uminus)

lemma tc_uminus: "tc (-p) = - tc p"
  by (simp add: tc_def tp_uminus)

lemma lp_ge_tp: "tp p \<preceq> lp p"
proof (cases "p = 0")
  case True
  show ?thesis unfolding True lp_def tp_def by simp
next
  case False
  show ?thesis by (rule lp_max_keys, rule tp_in_keys, fact False)
qed

subsubsection \<open>@{term tail}\<close>

lemma lookup_tail: "lookup (tail p) t = (if t \<prec> lp p then lookup p t else 0)"
  by (simp add: lookup_lower tail_def)

lemma lookup_tail_when: "lookup (tail p) t = (lookup p t when t \<prec> lp p)"
  by (simp add: lookup_lower_when tail_def)

lemma lookup_tail_2: "lookup (tail p) t = (if t = lp p then 0 else lookup p t)"
proof (rule ordered_powerprod_lin.linorder_cases[of t "lp p"])
  assume "t \<prec> lp p"
  hence "t \<noteq> lp p" by simp
  from this \<open>t \<prec> lp p\<close> lookup_tail[of p t] show ?thesis by simp
next
  assume "t = lp p"
  hence "\<not> t \<prec> lp p" by simp
  from \<open>t = lp p\<close> this lookup_tail[of p t] show ?thesis by simp
next
  assume "lp p \<prec> t"
  hence "\<not> t \<preceq> lp p" by simp
  hence cp: "lookup p t = 0"
    using lp_max by blast
  from \<open>\<not> t \<preceq> lp p\<close> have "\<not> t = lp p" and "\<not> t \<prec> lp p" by simp_all
  thus ?thesis using cp lookup_tail[of p t] by simp
qed

lemma leading_monomial_tail:
  "p = monomial (lc p) (lp p) + tail p"
  for p::"('a, 'b::comm_monoid_add) poly_mapping"
proof (rule poly_mapping_eqI)
  fix t
  have "lookup p t = lookup (monomial (lc p) (lp p)) t + lookup (tail p) t"
  proof (cases "t \<preceq> lp p")
    case True
    show ?thesis
    proof (cases "t = lp p")
      assume "t = lp p"
      hence "\<not> t \<prec> lp p" by simp
      hence c3: "lookup (tail p) t = 0" unfolding lookup_tail[of p t] by simp
      from \<open>t = lp p\<close> have c2: "lookup (monomial (lc p) (lp p)) t = lc p" by simp
      from \<open>t = lp p\<close> have c1: "lookup p t = lc p" unfolding lc_def by simp
      from c1 c2 c3 show ?thesis by simp
    next
      assume "t \<noteq> lp p"
      from this True have "t \<prec> lp p" by simp
      hence c2: "lookup (tail p) t = lookup p t" unfolding lookup_tail[of p t] by simp
      from \<open>t \<noteq> lp p\<close> have c1: "lookup (monomial (lc p) (lp p)) t = 0"
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
    from \<open>lp p \<noteq> t\<close> have c2: "lookup (monomial (lc p) (lp p)) t = 0"
      unfolding lookup_single by simp
    from \<open>\<not> t \<prec> lp p\<close> lookup_tail[of p t] have c3: "lookup (tail p) t = 0" by simp
    from c1 c2 c3 show ?thesis by simp
  qed
  thus "lookup p t = lookup (monomial (lc p) (lp p) + tail p) t"
    unfolding lookup_add by simp
qed

lemma tail_alt: "tail p = except p {lp p}"
  by (rule poly_mapping_eqI, simp add: lookup_tail_2 lookup_except)

corollary tail_alt_2: "tail p = p - monomial (lc p) (lp p)"
proof -
  have "p = monomial (lc p) (lp p) + tail p" by (fact leading_monomial_tail)
  also have "... = tail p + monomial (lc p) (lp p)" by (simp only: add.commute)
  finally have "p - monomial (lc p) (lp p) = (tail p + monomial (lc p) (lp p)) - monomial (lc p) (lp p)" by simp
  thus ?thesis by simp
qed

lemma tail_zero[simp]: "tail 0 = 0"
  by (simp only: tail_alt except_zero)

lemma lp_tail:
  assumes "tail p \<noteq> 0"
  shows "lp (tail p) \<prec> lp p"
proof (intro lp_less)
  fix s::"'a"
  assume "lp p \<preceq> s"
  hence "\<not> s \<prec> lp p" by simp
  thus "lookup (tail p) s = 0" unfolding lookup_tail[of p s] by simp
qed fact

lemma keys_tail: "keys (tail p) = keys p - {lp p}"
  by (simp add: tail_alt keys_except)

lemma tail_monomial: "tail (monomial c t) = 0"
  by (metis (no_types, lifting) lookup_tail_2 lookup_single_not_eq lp_less lp_monomial
      ordered_powerprod_lin.dual_order.strict_implies_not_eq single_zero tail_zero)

lemma times_tail_rec_left: "p * q = monom_mult (lc p) (lp p) q + (tail p) * q"
  unfolding tail_alt lc_def by (rule times_rec_left)

lemma times_tail_rec_right: "p * q = monom_mult_right p (lc q) (lp q) + p * (tail q)"
  unfolding tail_alt lc_def by (rule times_rec_right)


subsubsection \<open>Order Relation on Polynomials\<close>

definition ord_strict_p::"('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool" (infixl "\<prec>p" 50) where
  "p \<prec>p q \<longleftrightarrow> (\<exists>t. lookup p t = 0 \<and> lookup q t \<noteq> 0 \<and> (\<forall>s. t \<prec> s \<longrightarrow> lookup p s = lookup q s))"

definition ord_p::"('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool" (infixl "\<preceq>p" 50) where
  "ord_p p q \<equiv> (p \<prec>p q \<or> p = q)"

lemma ord_strict_higher: "p \<prec>p q \<longleftrightarrow> (\<exists>t. lookup p t = 0 \<and> lookup q t \<noteq> 0 \<and> higher p t = higher q t)"
  unfolding ord_strict_p_def higher_eq_iff ..

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

lemma ord_strict_p_irreflexive: "\<not> p \<prec>p p"
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

lemma ord_p_0_min: "0 \<preceq>p p"
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
  assumes "lp p \<prec> lp q"
  shows "p \<prec>p q"
proof -
  have "q \<noteq> 0"
  proof
    assume "q = 0"
    with assms have "lp p \<prec> 0" by (simp add: lp_def)
    with zero_min[of "lp p"] show False by simp
  qed
  show ?thesis
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
qed

lemma ord_p_lp:
  assumes "p \<preceq>p q"
  shows "lp p \<preceq> lp q"
proof (rule ccontr)
  assume "\<not> lp p \<preceq> lp q"
  hence "lp q \<prec> lp p" by simp
  from lp_ord_p[OF this] \<open>p \<preceq>p q\<close> show False by simp
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
  have pt: "lookup (tail p) t = lookup p t" using lookup_tail[of p t] \<open>t \<prec> lp p\<close> by simp
  have "q \<noteq> 0"
  proof
    assume "q = 0"
    hence  "p \<prec>p 0" using \<open>p \<prec>p q\<close> by simp
    hence "\<not> 0 \<preceq>p p" by auto
    thus False using ord_p_0_min[of p] by simp
  qed
  have qt: "lookup (tail q) t = lookup q t"
    using lookup_tail[of q t] \<open>t \<prec> lp p\<close> \<open>lp p = lp q\<close> by simp
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
        from a[rule_format, OF \<open>t \<prec> s\<close>] lookup_tail[of p s] lookup_tail[of q s]
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
  from lp_ord_p[OF lp_tail[OF False]] show ?thesis .
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
    from hp have pu: "\<forall>u. t \<prec> u \<longrightarrow> lookup p u = 0" by (simp only: higher_eq_zero_iff)
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
      thus "higher q t = 0" by (simp only: higher_eq_zero_iff)
    qed
  qed
next
  assume "q = p"
  thus ?thesis using assms by simp
qed

lemma ord_strict_p_recI:
  assumes "lp p = lp q" and "lc p = lc q" and tail: "tail p \<prec>p tail q"
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
    from lookup_tail[of p t] \<open>t \<prec> lp p\<close> pt show "lookup p t = 0" by simp
  next
    from lookup_tail[of q t] \<open>t \<prec> lp q\<close> qt show "lookup q t \<noteq> 0" by simp
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
        from False s lookup_tail_2[of p s] lookup_tail_2[of q s] \<open>lp p = lp q\<close>
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
      from ord_p_lp[OF this] nl have "lp p = lp q" by simp
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
      from lp_ord_p[OF this] show ?thesis .
    next
      assume "lp p = lp q \<and> lc p = lc q \<and> tail p \<prec>p tail q"
      hence "lp p = lp q" and "lc p = lc q" and "tail p \<prec>p tail q" by simp_all
      thus ?thesis by (rule ord_strict_p_recI)
    qed
  qed
qed

lemma ord_strict_p_monomial_iff: "p \<prec>p monomial c t \<longleftrightarrow> (c \<noteq> 0 \<and> (p = 0 \<or> lp p \<prec> t))"
proof -
  from ord_p_0_min[of "tail p"] have *: "\<not> tail p \<prec>p 0" by auto
  show ?thesis
    by (simp add: ord_strict_p_rec[of p] Let_def tail_def[symmetric] lc_def[symmetric]
        monomial_0_iff tail_monomial *, simp add: lp_monomial cong: conj_cong)
qed

corollary ord_strict_p_monomial_plus:
  assumes "p \<prec>p monomial c t" and "q \<prec>p monomial c t"
  shows "p + q \<prec>p monomial c t"
proof -
  from assms(1) have "c \<noteq> 0" and "p = 0 \<or> lp p \<prec> t" by (simp_all add: ord_strict_p_monomial_iff)
  from this(2) show ?thesis
  proof
    assume "p = 0"
    with assms(2) show ?thesis by simp
  next
    assume "lp p \<prec> t"
    from assms(2) have "q = 0 \<or> lp q \<prec> t" by (simp add: ord_strict_p_monomial_iff)
    thus ?thesis
    proof
      assume "q = 0"
      with assms(1) show ?thesis by simp
    next
      assume "lp q \<prec> t"
      with \<open>lp p \<prec> t\<close> have "lp (p + q) \<prec> t"
        using lp_plus_le_max ordered_powerprod_lin.dual_order.strict_trans2 ordered_powerprod_lin.max_less_iff_conj
        by blast 
      with \<open>c \<noteq> 0\<close> show ?thesis by (simp add: ord_strict_p_monomial_iff)
    qed
  qed
qed

lemma ord_strict_p_monom_mult:
  assumes "p \<prec>p q" and "c \<noteq> (0::'b::semiring_no_zero_divisors)"
  shows "monom_mult c s p \<prec>p monom_mult c s q"
proof -
  from assms(1) obtain t where 1: "lookup p t = 0" and 2: "lookup q t \<noteq> 0"
    and 3: "\<And>s. t \<prec> s \<Longrightarrow> lookup p s = lookup q s" unfolding ord_strict_p_def by auto
  show ?thesis unfolding ord_strict_p_def
  proof (intro exI conjI allI impI)
    from 1 show "lookup (monom_mult c s p) (s + t) = 0" by (simp add: lookup_monom_mult)
  next
    from 2 assms(2) show "lookup (monom_mult c s q) (s + t) \<noteq> 0" by (simp add: lookup_monom_mult)
  next
    fix u
    assume "s + t \<prec> u"
    show "lookup (monom_mult c s p) u = lookup (monom_mult c s q) u"
    proof (cases "s adds u")
      case True
      then obtain v where u: "u = s + v" ..
      from \<open>s + t \<prec> u\<close> have "t \<prec> v" unfolding u by (rule ord_strict_canc_left)
      hence "lookup p v = lookup q v" by (rule 3)
      thus ?thesis by (simp add: u lookup_monom_mult)
    next
      case False
      thus ?thesis by (simp add: monom_mult.rep_eq)
    qed
  qed
qed

lemma ord_strict_p_plus:
  assumes "p \<prec>p q" and "keys r \<inter> keys q = {}"
  shows "p + r \<prec>p q + r"
proof -
  from assms(1) obtain t where 1: "lookup p t = 0" and 2: "lookup q t \<noteq> 0"
    and 3: "\<And>s. t \<prec> s \<Longrightarrow> lookup p s = lookup q s" unfolding ord_strict_p_def by auto
  from 2 assms(2) have eq: "lookup r t = 0" by auto
  show ?thesis unfolding ord_strict_p_def
  proof (intro exI conjI allI impI, simp_all add: lookup_add)
    from 1 show "lookup p t + lookup r t = 0" by (simp add: eq)
  next
    from 2 show "lookup q t + lookup r t \<noteq> 0" by (simp add: eq)
  next
    fix s
    assume "t \<prec> s"
    hence "lookup p s = lookup q s" by (rule 3)
    thus "lookup p s + lookup r s = lookup q s + lookup r s" by simp
  qed
qed

lemma poly_mapping_tail_induct [case_names 0 tail]:
  assumes "P 0" and "\<And>p. p \<noteq> 0 \<Longrightarrow> P (tail p) \<Longrightarrow> P p"
  shows "P p"
proof (induct "card (keys p)" arbitrary: p)
  case 0
  with finite_keys[of p] have "keys p = {}" by simp
  hence "p = 0" by simp
  from \<open>P 0\<close> show ?case unfolding \<open>p = 0\<close> .
next
  case ind: (Suc n)
  from ind(2) have "keys p \<noteq> {}" by auto
  hence "p \<noteq> 0" by simp
  thus ?case
  proof (rule assms(2))
    show "P (tail p)"
    proof (rule ind(1))
      from \<open>p \<noteq> 0\<close> have "lp p \<in> keys p" by (rule lp_in_keys)
      hence "card (keys (tail p)) = card (keys p) - 1" by (simp add: keys_tail)
      also have "... = n" unfolding ind(2)[symmetric] by simp
      finally show "n = card (keys (tail p))" by simp
    qed
  qed
qed

end (* ordered_powerprod *)

subsubsection \<open>@{term dgrad_p}\<close>

context gd_powerprod
begin

definition dgrad_p :: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> nat"
  where "dgrad_p d p = (if keys p = {} then 0 else Max (d ` keys p))"

definition dgrad_p_set :: "('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::zero) set"
  where "dgrad_p_set d m = {p. \<forall>t\<in>keys p. d t \<le> m}"

lemma dgrad_p_zero [simp]: "dgrad_p d 0 = 0"
  by (simp add: dgrad_p_def)

lemma dgrad_p_geI:
  assumes "t \<in> keys p"
  shows "d t \<le> dgrad_p d p"
  using assms by (auto simp add: dgrad_p_def)

lemma dgrad_p_geI_lp:
  assumes "p \<noteq> 0"
  shows "d (lp p) \<le> dgrad_p d p"
  by (rule dgrad_p_geI, rule lp_in_keys, fact)

lemma dgrad_p_leI:
  assumes "\<And>t. t \<in> keys p \<Longrightarrow> d t \<le> m"
  shows "dgrad_p d p \<le> m"
  using assms by (auto simp add: dgrad_p_def)

lemma in_dgrad_p_set_iff: "p \<in> dgrad_p_set d m \<longleftrightarrow> (\<forall>t\<in>keys p. d t \<le> m)"
  by (simp add: dgrad_p_set_def)

lemma dgrad_p_set_alt: "dgrad_p_set d m = {p. dgrad_p d p \<le> m}"
  by (auto simp add: dgrad_p_set_def dgrad_p_def)

lemma dgrad_p_set_dgrad_p: "p \<in> dgrad_p_set d (dgrad_p d p)"
  by (simp add: dgrad_p_set_alt)

lemma dgrad_p_setI [intro]:
  assumes "\<And>t. t \<in> keys p \<Longrightarrow> d t \<le> m"
  shows "p \<in> dgrad_p_set d m"
  using assms by (auto simp: in_dgrad_p_set_iff)

lemma dgrad_p_setD:
  assumes "p \<in> dgrad_p_set d m" and "t \<in> keys p"
  shows "d t \<le> m"
  using assms by (simp only: in_dgrad_p_set_iff)

lemma zero_in_dgrad_p_set: "0 \<in> dgrad_p_set d m"
  by (rule, simp)

lemma dgrad_p_set_zero [simp]: "dgrad_p_set (\<lambda>_. 0) m = UNIV"
  by auto

lemma subset_dgrad_p_set_zero: "F \<subseteq> dgrad_p_set (\<lambda>_. 0) m"
  by simp

lemma dgrad_p_set_subset:
  assumes "m \<le> n"
  shows "dgrad_p_set d m \<subseteq> dgrad_p_set d n"
  using assms by (auto simp: dgrad_p_set_def)

lemma dgrad_p_setD_lp:
  assumes "p \<in> dgrad_p_set d m" and "p \<noteq> 0"
  shows "d (lp p) \<le> m"
  by (rule dgrad_p_setD, fact, rule lp_in_keys, fact)

lemma dgrad_p_set_exhaust_expl:
  assumes "finite F"
  shows "F \<subseteq> dgrad_p_set d (Max ((dgrad_p d) ` F))"
proof
  fix f
  assume "f \<in> F"
  hence "dgrad_p d f \<in> (dgrad_p d) ` F" by simp
  with _ have "dgrad_p d f \<le> Max ((dgrad_p d) ` F)"
  proof (rule Max_ge)
    from assms show "finite ((dgrad_p d) ` F)" by auto
  qed
  hence "dgrad_p_set d (dgrad_p d f) \<subseteq> dgrad_p_set d (Max ((dgrad_p d) ` F))" by (rule dgrad_p_set_subset)
  moreover have "f \<in> dgrad_p_set d (dgrad_p d f)" by (fact dgrad_p_set_dgrad_p)
  ultimately show "f \<in> dgrad_p_set d (Max ((dgrad_p d) ` F))" ..
qed

lemma dgrad_p_set_exhaust:
  assumes "finite F"
  obtains m where "F \<subseteq> dgrad_p_set d m"
proof
  from assms show "F \<subseteq> dgrad_p_set d (Max ((dgrad_p d) ` F))" by (rule dgrad_p_set_exhaust_expl)
qed

lemma dgrad_p_except: "dgrad_p d (except p S) \<le> dgrad_p d p"
  by (rule dgrad_p_leI, rule dgrad_p_geI, simp add: keys_except)

lemma dgrad_p_tail: "dgrad_p d (tail p) \<le> dgrad_p d p"
  by (rule dgrad_p_leI, rule dgrad_p_geI, simp add: keys_tail)

lemma dgrad_p_plus: "dgrad_p d (p + q) \<le> ord_class.max (dgrad_p d p) (dgrad_p d q)"
proof (rule dgrad_p_leI)
  fix t
  assume "t \<in> keys (p + q)"
  with keys_add_subset have "t \<in> keys p \<union> keys q" ..
  thus "d t \<le> ord_class.max (dgrad_p d p) (dgrad_p d q)"
  proof
    assume "t \<in> keys p"
    hence "d t \<le> dgrad_p d p" by (rule dgrad_p_geI)
    thus ?thesis by simp
  next
    assume "t \<in> keys q"
    hence "d t \<le> dgrad_p d q" by (rule dgrad_p_geI)
    thus ?thesis by simp
  qed
qed

lemma dgrad_p_uminus [simp]: "dgrad_p d (-p) = dgrad_p d p"
  by (simp add: dgrad_p_def keys_uminus)

lemma dgrad_p_minus:  "dgrad_p d (p - q) \<le> ord_class.max (dgrad_p d p) (dgrad_p d q)"
proof (rule dgrad_p_leI)
  fix t
  assume "t \<in> keys (p - q)"
  with keys_minus have "t \<in> keys p \<union> keys q" ..
  thus "d t \<le> ord_class.max (dgrad_p d p) (dgrad_p d q)"
  proof
    assume "t \<in> keys p"
    hence "d t \<le> dgrad_p d p" by (rule dgrad_p_geI)
    thus ?thesis by simp
  next
    assume "t \<in> keys q"
    hence "d t \<le> dgrad_p d q" by (rule dgrad_p_geI)
    thus ?thesis by simp
  qed
qed

lemma dgrad_p_monom_mult:
  assumes "dickson_grading (+) d"
  shows "dgrad_p d (monom_mult c t p) \<le> ord_class.max (d t) (dgrad_p d p)"
proof (rule dgrad_p_leI)
  fix s
  assume "s \<in> keys (monom_mult c t p)"
  with keys_monom_mult_subset have "s \<in> ((+) t) ` keys p" ..
  then obtain u where "u \<in> keys p" and "s = t + u" ..
  from this(1) have "d u \<le> dgrad_p d p" by (rule dgrad_p_geI)
  moreover have "d s = ord_class.max (d t) (d u)"
    by (simp only: \<open>s = t + u\<close> dickson_gradingD1[OF assms(1)])
  ultimately show "d s \<le> ord_class.max (d t) (dgrad_p d p)" by simp
qed

lemma dgrad_p_set_closed_plus:
  assumes "p \<in> dgrad_p_set d m" and "q \<in> dgrad_p_set d m"
  shows "p + q \<in> dgrad_p_set d m"
proof -
  have "dgrad_p d (p + q) \<le> ord_class.max (dgrad_p d p) (dgrad_p d q)" by (fact dgrad_p_plus)
  also from assms have "... \<le> m" by (simp add: dgrad_p_set_alt)
  finally show ?thesis by (simp add: dgrad_p_set_alt)
qed

lemma dgrad_p_set_closed_uminus:
  assumes "p \<in> dgrad_p_set d m"
  shows "-p \<in> dgrad_p_set d m"
  using assms by (simp add: dgrad_p_set_alt)

lemma dgrad_p_set_closed_minus:
  assumes "p \<in> dgrad_p_set d m" and "q \<in> dgrad_p_set d m"
  shows "p - q \<in> dgrad_p_set d m"
proof -
  have "dgrad_p d (p - q) \<le> ord_class.max (dgrad_p d p) (dgrad_p d q)" by (fact dgrad_p_minus)
  also from assms have "... \<le> m" by (simp add: dgrad_p_set_alt)
  finally show ?thesis by (simp add: dgrad_p_set_alt)
qed

lemma dgrad_p_set_closed_monom_mult:
  assumes "dickson_grading (+) d" and "d t \<le> m" and "p \<in> dgrad_p_set d m"
  shows "monom_mult c t p \<in> dgrad_p_set d m"
proof -
  from assms(1) have "dgrad_p d (monom_mult c t p) \<le> ord_class.max (d t) (dgrad_p d p)"
    by (rule dgrad_p_monom_mult)
  also from assms have "... \<le> m" by (simp add: dgrad_p_set_alt)
  finally show ?thesis by (simp add: dgrad_p_set_alt)
qed

lemma dgrad_p_set_closed_except:
  assumes "p \<in> dgrad_p_set d m"
  shows "except p S \<in> dgrad_p_set d m"
  by (rule dgrad_p_setI, rule dgrad_p_setD, rule assms, simp add: keys_except)

lemma dgrad_p_set_closed_tail:
  assumes "p \<in> dgrad_p_set d m"
  shows "tail p \<in> dgrad_p_set d m"
  unfolding tail_def lower_def using assms by (rule dgrad_p_set_closed_except)

subsubsection \<open>Well-foundedness\<close>

definition dickson_less_p :: "('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "dickson_less_p d m p q \<longleftrightarrow> ({p, q} \<subseteq> dgrad_p_set d m \<and> p \<prec>p q)"

lemma dickson_less_pI:
  assumes "p \<in> dgrad_p_set d m" and "q \<in> dgrad_p_set d m" and "p \<prec>p q"
  shows "dickson_less_p d m p q"
  using assms by (simp add: dickson_less_p_def)

lemma dickson_less_pD1:
  assumes "dickson_less_p d m p q"
  shows "p \<in> dgrad_p_set d m"
  using assms by (simp add: dickson_less_p_def)

lemma dickson_less_pD2:
  assumes "dickson_less_p d m p q"
  shows "q \<in> dgrad_p_set d m"
  using assms by (simp add: dickson_less_p_def)

lemma dickson_less_pD3:
  assumes "dickson_less_p d m p q"
  shows "p \<prec>p q"
  using assms by (simp add: dickson_less_p_def)

lemma dickson_less_p_irrefl: "\<not> dickson_less_p d m p p"
  by (simp add: dickson_less_p_def)

lemma dickson_less_p_trans:
  assumes "dickson_less_p d m p q" and "dickson_less_p d m q r"
  shows "dickson_less_p d m p r"
  using assms by (auto simp add: dickson_less_p_def)

lemma dickson_less_p_mono:
  assumes "dickson_less_p d m p q" and "m \<le> n"
  shows "dickson_less_p d n p q"
proof -
  from assms(2) have "dgrad_p_set d m \<subseteq> dgrad_p_set d n" by (rule dgrad_p_set_subset)
  moreover from assms(1) have "p \<in> dgrad_p_set d m" and "q \<in> dgrad_p_set d m" and "p \<prec>p q"
    by (rule dickson_less_pD1, rule dickson_less_pD2, rule dickson_less_pD3)
  ultimately have "p \<in> dgrad_p_set d n" and "q \<in> dgrad_p_set d n" by auto
  from this \<open>p \<prec>p q\<close> show ?thesis by (rule dickson_less_pI)
qed

lemma dickson_less_p_zero: "dickson_less_p (\<lambda>_. 0) m = (\<prec>p)"
  by (rule, rule, simp add: dickson_less_p_def)

lemma dickson_less_p_wf_aux:
  assumes "dickson_grading (+) d"
  assumes "x \<in> Q" and "\<forall>y\<in>Q. y \<noteq> 0 \<longrightarrow> (y \<in> dgrad_p_set d m \<and> dickson_less d m (lp y) s)"
  shows "\<exists>p\<in>Q. (\<forall>q\<in>Q. \<not> dickson_less_p d m q p)"
  using assms(2) assms(3)
proof (induct s arbitrary: x Q rule: wfP_induct[OF wf_dickson_less, OF assms(1)])
  fix s::"'a" and x::"('a, 'b) poly_mapping" and Q::"('a, 'b) poly_mapping set"
  assume hyp: "\<forall>s0. dickson_less d m s0 s \<longrightarrow> (\<forall>x0 Q0::('a, 'b) poly_mapping set. x0 \<in> Q0 \<longrightarrow>
                            (\<forall>y\<in>Q0. y \<noteq> 0 \<longrightarrow> (y \<in> dgrad_p_set d m \<and> dickson_less d m (lp y) s0)) \<longrightarrow>
                            (\<exists>p\<in>Q0. \<forall>q\<in>Q0. \<not> dickson_less_p d m q p))"
  assume "x \<in> Q"
  assume "\<forall>y\<in>Q. y \<noteq> 0 \<longrightarrow> (y \<in> dgrad_p_set d m \<and> dickson_less d m (lp y) s)"
  hence bounded: "\<And>y. y \<in> Q \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> (y \<in> dgrad_p_set d m \<and> dickson_less d m (lp y) s)" by auto
  show "\<exists>p\<in>Q. \<forall>q\<in>Q. \<not> dickson_less_p d m q p"
  proof (cases "0 \<in> Q")
    case True
    show ?thesis
    proof (rule, rule, rule)
      fix q::"('a, 'b) poly_mapping"
      assume "dickson_less_p d m q 0"
      hence "q \<prec>p 0" by (rule dickson_less_pD3)
      thus False using ord_p_0_min[of q] by simp
    next
      from True show "0 \<in> Q" .
    qed
  next
    case False
    define Q1 where "Q1 = {lp p | p. p \<in> Q}"
    from \<open>x \<in> Q\<close> have "lp x \<in> Q1" unfolding Q1_def by auto
    with wf_dickson_less[OF assms(1)] obtain t
      where "t \<in> Q1" and t_min_1: "\<And>q. dickson_less d m q t \<Longrightarrow> q \<notin> Q1"
      by (rule wfE_min[to_pred], auto)
    have t_min: "\<And>q. q \<in> Q \<Longrightarrow> \<not> dickson_less d m (lp q) t"
    proof -
      fix q::"('a, 'b) poly_mapping"
      assume "q \<in> Q"
      hence "lp q \<in> Q1" unfolding Q1_def by auto
      thus "\<not> dickson_less d m (lp q) t" using t_min_1 by auto
    qed
    from \<open>t \<in> Q1\<close> obtain p where "lp p = t" and "p \<in> Q" unfolding Q1_def by auto
    hence "p \<noteq> 0" using False by auto
    with \<open>p \<in> Q\<close> have "p \<in> dgrad_p_set d m \<and> dickson_less d m (lp p) s" by (rule bounded)
    hence "p \<in> dgrad_p_set d m" and "dickson_less d m (lp p) s" by simp_all
    moreover from this(1) \<open>p \<noteq> 0\<close> have "d (lp p) \<le> m" by (rule dgrad_p_setD_lp)
    ultimately have "d t \<le> m" by (simp add: \<open>lp p = t\<close>)
    define Q2 where "Q2 = {tail p | p. p \<in> Q \<and> lp p = t}"
    from \<open>p \<in> Q\<close> \<open>lp p = t\<close> have "tail p \<in> Q2" unfolding Q2_def by auto
    have "\<forall>q\<in>Q2. q \<noteq> 0 \<longrightarrow> (q \<in> dgrad_p_set d m \<and> dickson_less d m (lp q) (lp p))"
    proof (intro ballI impI)
      fix q::"('a, 'b) poly_mapping"
      assume "q \<in> Q2"
      then obtain q0 where q: "q = tail q0" and "lp q0 = lp p" and "q0 \<in> Q"
        using \<open>lp p = t\<close> by (auto simp add: Q2_def)
      assume "q \<noteq> 0"
      hence "tail q0 \<noteq> 0" using \<open>q = tail q0\<close> by simp
      hence "q0 \<noteq> 0" by auto
      with \<open>q0 \<in> Q\<close> have "q0 \<in> dgrad_p_set d m \<and> dickson_less d m (lp q0) s" by (rule bounded)
      hence "q0 \<in> dgrad_p_set d m" and "dickson_less d m (lp q0) s" by simp_all
      from this(1) have "q \<in> dgrad_p_set d m" unfolding q by (rule dgrad_p_set_closed_tail)
      show "q \<in> dgrad_p_set d m \<and> dickson_less d m (lp q) (lp p)"
      proof
        show "dickson_less d m (lp q) (lp p)"
        proof (rule dickson_lessI)
          from \<open>q \<in> dgrad_p_set d m\<close> \<open>q \<noteq> 0\<close> show "d (lp q) \<le> m" by (rule dgrad_p_setD_lp)
        next
          from \<open>dickson_less d m (lp p) s\<close> show "d (lp p) \<le> m" by (rule dickson_lessD1)
        next
          from lp_tail[OF \<open>tail q0 \<noteq> 0\<close>] \<open>q = tail q0\<close> \<open>lp q0 = lp p\<close> show "lp q \<prec> lp p" by simp
        qed
      qed fact
    qed
    with hyp \<open>dickson_less d m (lp p) s\<close> \<open>tail p \<in> Q2\<close> have "\<exists>p\<in>Q2. \<forall>q\<in>Q2. \<not> dickson_less_p d m q p"
      by blast
    then obtain q where "q \<in> Q2" and q_min: "\<forall>r\<in>Q2. \<not> dickson_less_p d m r q" ..
    from \<open>q \<in> Q2\<close> obtain q0 where "q = tail q0" and "q0 \<in> Q" and "lp q0 = t" unfolding Q2_def by auto
    from q_min \<open>q = tail q0\<close> have q0_tail_min: "\<And>r. r \<in> Q2 \<Longrightarrow> \<not> dickson_less_p d m r (tail q0)" by simp
    from \<open>q0 \<in> Q\<close> show ?thesis
    proof
      show "\<forall>r\<in>Q. \<not> dickson_less_p d m r q0"
      proof (intro ballI notI)
        fix r::"('a, 'b) poly_mapping"
        assume "dickson_less_p d m r q0"
        hence "r \<in> dgrad_p_set d m" and "q0 \<in> dgrad_p_set d m" and "r \<prec>p q0"
          by (rule dickson_less_pD1, rule dickson_less_pD2, rule dickson_less_pD3)
        from this(3) have "lp r \<preceq> lp q0" by (simp add: ord_p_lp)
        with \<open>lp q0 = t\<close> have "lp r \<preceq> t" by simp
        assume "r \<in> Q"
        hence "\<not> dickson_less d m (lp r) t" by (rule t_min)
        from False \<open>r \<in> Q\<close> have "r \<noteq> 0" using False by blast
        with \<open>r \<in> dgrad_p_set d m\<close> have "d (lp r) \<le> m" by (rule dgrad_p_setD_lp)
        have "\<not> lp r \<prec> t"
        proof
          assume "lp r \<prec> t"
          with \<open>d (lp r) \<le> m\<close> \<open>d t \<le> m\<close> have "dickson_less d m (lp r) t" by (rule dickson_lessI)
          with \<open>\<not> dickson_less d m (lp r) t\<close> show False ..
        qed
        with \<open>lp r \<preceq> t\<close> have "lp r = t" by simp
        with \<open>r \<in> Q\<close> have "tail r \<in> Q2" by (auto simp add: Q2_def)
        have "dickson_less_p d m (tail r) (tail q0)"
        proof (rule dickson_less_pI)
          show "tail r \<in> dgrad_p_set d m" by (rule dgrad_p_set_closed_tail, fact)
        next
          show "tail q0 \<in> dgrad_p_set d m" by (rule dgrad_p_set_closed_tail, fact)
        next
          have "lp r = lp q0" by (simp only: \<open>lp r = t\<close> \<open>lp q0 = t\<close>)
          from \<open>r \<noteq> 0\<close> this \<open>r \<prec>p q0\<close> show "tail r \<prec>p tail q0" by (rule ord_p_tail)
        qed
        with q0_tail_min[OF \<open>tail r \<in> Q2\<close>] show False ..
      qed
    qed
  qed
qed

theorem dickson_less_p_wf:
  assumes "dickson_grading (+) d"
  shows "wfP (dickson_less_p d m)"
proof (rule wfI_min[to_pred])
  fix Q::"('a, 'b) poly_mapping set" and x::"('a, 'b) poly_mapping"
  assume "x \<in> Q"
  show "\<exists>z\<in>Q. \<forall>y. dickson_less_p d m y z \<longrightarrow> y \<notin> Q"
  proof (cases "0 \<in> Q")
    case True
    show ?thesis
    proof (rule, rule, rule)
      from True show "0 \<in> Q" .
    next
      fix q::"('a, 'b) poly_mapping"
      assume "dickson_less_p d m q 0"
      hence "q \<prec>p 0" by (rule dickson_less_pD3)
      thus "q \<notin> Q" using ord_p_0_min[of q] by simp
    qed
  next
    case False
    show ?thesis
    proof (cases "Q \<subseteq> dgrad_p_set d m")
      case True
      show ?thesis
      proof (cases "\<forall>u::'a. u = 0")
        case True
        hence eq: "\<And>u v::'a. u = v" by (metis(full_types))
        have tail: "\<And>p::('a, 'b) poly_mapping. tail p = 0"
        proof (rule ccontr)
          fix p::"('a, 'b) poly_mapping"
          assume "tail p \<noteq> 0"
          hence "lp (tail p) \<prec> lp p" by (rule lp_tail)
          also have "... = lp (tail p)" by (rule eq)
          finally show False ..
        qed
        from \<open>x \<in> Q\<close> show ?thesis
        proof
          show "\<forall>y. dickson_less_p d m y x \<longrightarrow> y \<notin> Q"
          proof (intro allI impI notI)
            fix y
            assume "y \<in> Q"
            with \<open>0 \<notin> Q\<close> have "y \<noteq> 0" by blast
            assume "dickson_less_p d m y x"
            hence "y \<prec>p x" by (rule dickson_less_pD3)
            with \<open>y \<noteq> 0\<close> eq have "tail y \<prec>p tail x" by (rule ord_p_tail)
            thus False by (simp add: tail)
          qed
        qed
      next
        case False
        hence "\<exists>u::'a. u \<noteq> 0" by simp
        then obtain u::'a where "u \<noteq> 0" ..
        hence "0 \<prec> u" using zero_min[of u] by simp
        define s where "s = lp x + u"
        define n where "n = ord_class.max m (d s)"
        have "m \<le> n" and "d s \<le> n" by (simp_all add: n_def)
        define Q1 where "Q1 = {q\<in>Q. lp q \<prec> s}"
        from assms have "\<exists>z\<in>Q1. \<forall>q\<in>Q1. \<not> dickson_less_p d n q z"
        proof (rule dickson_less_p_wf_aux)
          show "x \<in> Q1"
          proof (simp add: Q1_def, rule, fact)
            from \<open>0 \<prec> u\<close> have "lp x + 0 \<prec> lp x + u" by (rule plus_monotone_strict_left)
            thus "lp x \<prec> s" by (simp add: s_def)
          qed
        next
          show "\<forall>y\<in>Q1. y \<noteq> 0 \<longrightarrow> y \<in> dgrad_p_set d n \<and> dickson_less d n (lp y) s"
          proof (intro ballI impI)
            fix y::"('a, 'b) poly_mapping"
            assume "y \<noteq> 0"
            assume "y \<in> Q1"
            hence "y \<in> Q" and "lp y \<prec> s" by (simp_all add: Q1_def)
            from \<open>Q \<subseteq> dgrad_p_set d m\<close> this(1) have "y \<in> dgrad_p_set d m" ..
            from dgrad_p_set_subset[OF \<open>m \<le> n\<close>] this have "y \<in> dgrad_p_set d n" ..
            show "y \<in> dgrad_p_set d n \<and> dickson_less d n (lp y) s"
              by (rule, fact, rule dickson_lessI, rule le_trans, rule dgrad_p_setD_lp, fact, fact,
                  rule, fact+)
          qed
        qed
        then obtain z where "z \<in> Q1" and z_min: "\<And>q. q \<in> Q1 \<Longrightarrow> \<not> dickson_less_p d n q z" by auto
        from this(1) have "z \<in> Q" and "lp z \<prec> s" by (simp_all add: Q1_def)
        from this(1) show ?thesis
        proof
          show "\<forall>y. dickson_less_p d m y z \<longrightarrow> y \<notin> Q"
          proof (intro allI impI notI)
            fix y
            assume "dickson_less_p d m y z"
            hence "y \<prec>p z" and "dickson_less_p d n y z"
              by (rule dickson_less_pD3, rule dickson_less_p_mono, intro \<open>m \<le> n\<close>)
            from this(1) have "lp y \<preceq> lp z" by (simp add: ord_p_lp)
            from this \<open>lp z \<prec> s\<close> have "lp y \<prec> s" by simp
            moreover assume "y \<in> Q"
            ultimately have "y \<in> Q1" by (simp add: Q1_def)
            hence "\<not> dickson_less_p d n y z" by (rule z_min)
            from this \<open>dickson_less_p d n y z\<close> show False ..
          qed
        qed
      qed
    next
      case False
      then obtain q where "q \<in> Q" and "q \<notin> dgrad_p_set d m" by blast
      from this(1) show ?thesis
      proof
        show "\<forall>y. dickson_less_p d m y q \<longrightarrow> y \<notin> Q"
        proof (intro allI impI)
          fix y
          assume "dickson_less_p d m y q"
          hence "q \<in> dgrad_p_set d m" by (rule dickson_less_pD2)
          with \<open>q \<notin> dgrad_p_set d m\<close> show "y \<notin> Q" ..
        qed
      qed
    qed
  qed
qed

corollary ord_p_minimum_dgrad_p_set:
  assumes "dickson_grading (+) d" and "x \<in> Q" and "Q \<subseteq> dgrad_p_set d m"
  obtains q where "q \<in> Q" and "\<And>y. y \<prec>p q \<Longrightarrow> y \<notin> Q"
proof -
  from assms(1) have "wfP (dickson_less_p d m)" by (rule dickson_less_p_wf)
  from this assms(2) obtain q where "q \<in> Q" and *: "\<And>y. dickson_less_p d m y q \<Longrightarrow> y \<notin> Q"
    by (rule wfE_min[to_pred], auto)
  from assms(3) \<open>q \<in> Q\<close> have "q \<in> dgrad_p_set d m" ..
  from \<open>q \<in> Q\<close> show ?thesis
  proof
    fix y
    assume "y \<prec>p q"
    show "y \<notin> Q"
    proof
      assume "y \<in> Q"
      with assms(3) have "y \<in> dgrad_p_set d m" ..
      from this \<open>q \<in> dgrad_p_set d m\<close> \<open>y \<prec>p q\<close> have "dickson_less_p d m y q"
        by (rule dickson_less_pI)
      hence "y \<notin> Q" by (rule *)
      from this \<open>y \<in> Q\<close> show False ..
    qed
  qed
qed

end (* gd_powerprod *)

lemma (in od_powerprod) ord_p_wf: "wfP (\<prec>p)"
proof -
  from dickson_grading_zero have "wfP (dickson_less_p (\<lambda>_. 0) 0)" by (rule dickson_less_p_wf)
  thus ?thesis by (simp only: dickson_less_p_zero)
qed

end (* theory *)
