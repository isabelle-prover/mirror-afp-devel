theory Chevalley_Warning
  imports
    "HOL-Number_Theory.Residues"
    "HOL-Computational_Algebra.Polynomial"
    "HOL-Library.FuncSet"
    "Polynomials.Polynomials"
begin

section \<open>The Chevalley-Warning theorem\<close>

text \<open>
  We reuse the concrete multivariate-polynomial representation from the AFP
  entry \<^theory>\<open>Polynomials.Polynomials\<close>.  Thus a polynomial has type
  @{typ "('v, 'a) poly"} and consists of AFP monomials paired with
  coefficients.  The theorem takes an explicit finite set of variables, so it
  applies directly to the usual natural-number-indexed AFP polynomials.
\<close>

definition variables_poly ::
    "'v::linorder set \<Rightarrow> ('v, 'a) poly \<Rightarrow> bool" where
  "variables_poly V p \<longleftrightarrow> poly_vars p \<subseteq> V"

definition total_degree_poly_le :: "('v::linorder, 'a) poly \<Rightarrow> nat \<Rightarrow> bool" where
  "total_degree_poly_le p d \<longleftrightarrow> poly_degree p \<le> d"

definition total_degree_poly_less :: "('v::linorder, 'a) poly \<Rightarrow> nat \<Rightarrow> bool" where
  "total_degree_poly_less p d \<longleftrightarrow> poly_degree p < d"

definition common_zeros ::
    "'v::linorder set \<Rightarrow>
      ('v, 'a::comm_semiring_1) poly list \<Rightarrow> ('v \<Rightarrow> 'a) set" where
  "common_zeros V ps =
    {\<alpha> \<in> PiE V (\<lambda>_. UNIV). list_all (\<lambda>p. eval_poly \<alpha> p = 0) ps}"

lemma variables_poly_UNIV [simp]: "variables_poly UNIV p"
  by (simp add: variables_poly_def)

lemma monom_vars_subset_poly_vars:
  assumes "(m, c) \<in> set p"
  shows "monom_vars m \<subseteq> poly_vars p"
  using assms
  by (auto simp: monom_vars_def poly_vars_def)

lemma poly_degree_leI:
  assumes "\<And>m c. (m, c) \<in> set p \<Longrightarrow> monom_degree m \<le> d"
  shows "poly_degree p \<le> d"
  using assms
  by (induction p) (auto simp: poly_degree_def split: prod.splits)

lemma total_degree_poly_leD:
  assumes "total_degree_poly_le p d" "(m, c) \<in> set p"
  shows "monom_degree m \<le> d"
proof -
  have "monom_degree m \<in> set (map (\<lambda>(m, c). monom_degree m) p)"
    using assms(2) by force
  then have "monom_degree m \<le> max_list (map (\<lambda>(m, c). monom_degree m) p)"
    by (rule max_list)
  with assms(1) show ?thesis
    by (simp add: total_degree_poly_le_def poly_degree_def)
qed

lemma total_degree_poly_lessD:
  assumes "total_degree_poly_less p d" "(m, c) \<in> set p"
  shows "monom_degree m < d"
  using total_degree_poly_leD[of p "poly_degree p" m c] assms
  by (simp add: total_degree_poly_le_def total_degree_poly_less_def)

lemma total_degree_poly_le_mono:
  assumes "total_degree_poly_le p d" "d \<le> e"
  shows "total_degree_poly_le p e"
  using assms by (simp add: total_degree_poly_le_def)

lemma total_degree_poly_less_of_le:
  assumes "total_degree_poly_le p d" "d < e"
  shows "total_degree_poly_less p e"
  using assms
  by (simp add: total_degree_poly_le_def total_degree_poly_less_def)

subsection \<open>Polynomial operations\<close>

fun poly_prod :: "('v::linorder, 'a::comm_semiring_1) poly list \<Rightarrow> ('v, 'a) poly" where
  "poly_prod [] = one_poly"
| "poly_prod (p # ps) = poly_mult p (poly_prod ps)"

definition indicator_factor ::
    "nat \<Rightarrow> ('v::linorder, 'a::comm_ring_1) poly \<Rightarrow> ('v, 'a) poly" where
  "indicator_factor q p = poly_minus (poly_const 1) (poly_power p (q - 1))"

definition indicator_poly ::
    "nat \<Rightarrow> ('v::linorder, 'a::comm_ring_1) poly list \<Rightarrow> ('v, 'a) poly" where
  "indicator_poly q ps = poly_prod (map (indicator_factor q) ps)"

lemma monom_list_degree_mult:
  "monom_list_degree (monom_mult_list m n) =
    monom_list_degree m + monom_list_degree n"
  by (induction m n rule: monom_mult_list.induct)
    (auto simp: monom_list_degree_def monom_mult_list.simps
      split: list.splits prod.splits if_splits)

lemma monom_degree_mult [simp]:
  "monom_degree (m * n) = monom_degree m + monom_degree n"
  by transfer (rule monom_list_degree_mult)

lemma monom_degree_one [simp]:
  "monom_degree (1::'v::linorder monom) = 0"
  by transfer (simp add: monom_list_degree_def)

lemma monom_vars_mult [simp]:
  "monom_vars (m * n) = monom_vars m \<union> monom_vars n"
  unfolding monom_vars_def
  by transfer (metis monom_list_mult_list_vars set_map)

lemma monom_mult_poly_monoms:
  "poly_monoms (monom_mult_poly (m, c) p) \<subseteq> (*) m ` poly_monoms p"
proof (induction p)
  case Nil
  then show ?case
    by (simp add: monom_mult_poly.simps)
next
  case (Cons t p)
  obtain n d where t: "t = (n, d)"
    by force
  show ?case
    using Cons.IH
    by (cases "c * d = 0")
      (auto simp: monom_mult_poly.simps t)
qed

lemma variables_poly_const [simp]:
  "variables_poly V (poly_const c :: ('v::linorder, 'a::zero) poly)"
  by (auto simp: variables_poly_def poly_vars_def poly_const_def monom_vars_def)

lemma total_degree_poly_le_const [simp]:
  "total_degree_poly_le (poly_const c :: ('v::linorder, 'a::zero) poly) 0"
  by (auto simp: total_degree_poly_le_def poly_degree_def poly_const_def)

lemma variables_poly_add:
  assumes p: "variables_poly V p" and q: "variables_poly V q"
  shows "variables_poly V (poly_add p q)"
proof (unfold variables_poly_def, rule subsetI)
  fix x
  assume "x \<in> poly_vars (poly_add p q)"
  then obtain m c where
    mc: "(m, c) \<in> set (poly_add p q)" and x: "x \<in> monom_vars m"
    by (auto simp: poly_vars_def monom_vars_def)
  have "m \<in> poly_monoms p \<union> poly_monoms q"
    using poly_add_monoms[of p q] mc by force
  then have "monom_vars m \<subseteq> V"
  proof
    assume "m \<in> poly_monoms p"
    then obtain c' where "(m, c') \<in> set p"
      by auto
    then show ?thesis
      using monom_vars_subset_poly_vars[of m c' p] p
      by (auto simp: variables_poly_def)
  next
    assume "m \<in> poly_monoms q"
    then obtain c' where "(m, c') \<in> set q"
      by auto
    then show ?thesis
      using monom_vars_subset_poly_vars[of m c' q] q
      by (auto simp: variables_poly_def)
  qed
  with x show "x \<in> V"
    by blast
qed

lemma total_degree_poly_le_add:
  assumes p: "total_degree_poly_le p d" and q: "total_degree_poly_le q d"
  shows "total_degree_poly_le (poly_add p q) d"
proof (unfold total_degree_poly_le_def, rule poly_degree_leI)
  fix m c
  assume "(m, c) \<in> set (poly_add p q)"
  then have "m \<in> poly_monoms (poly_add p q)"
    by force
  then have "m \<in> poly_monoms p \<union> poly_monoms q"
    using poly_add_monoms[of p q] by blast
  then show "monom_degree m \<le> d"
    using total_degree_poly_leD[OF p] total_degree_poly_leD[OF q]
    by auto
qed

lemma total_degree_monom_mult_poly:
  assumes m: "monom_degree m \<le> d" and p: "total_degree_poly_le p e"
  shows "total_degree_poly_le (monom_mult_poly (m, c) p) (d + e)"
proof (unfold total_degree_poly_le_def, rule poly_degree_leI)
  fix r a
  assume "(r, a) \<in> set (monom_mult_poly (m, c) p)"
  then have "r \<in> poly_monoms (monom_mult_poly (m, c) p)"
    by force
  then obtain r' where r': "r = m * r'" and "r' \<in> poly_monoms p"
    using monom_mult_poly_monoms[of m c p] by blast
  then obtain b where "(r', b) \<in> set p"
    by auto
  then have "monom_degree r' \<le> e"
    by (rule total_degree_poly_leD[OF p])
  with m show "monom_degree r \<le> d + e"
    by (simp add: r')
qed

lemma variables_monom_mult_poly:
  assumes m: "monom_vars m \<subseteq> V" and p: "variables_poly V p"
  shows "variables_poly V (monom_mult_poly (m, c) p)"
proof (unfold variables_poly_def, rule subsetI)
  fix x
  assume "x \<in> poly_vars (monom_mult_poly (m, c) p)"
  then obtain r a where
    ra: "(r, a) \<in> set (monom_mult_poly (m, c) p)"
    and x: "x \<in> monom_vars r"
    by (auto simp: poly_vars_def monom_vars_def)
  then obtain r' where r': "r = m * r'" and "r' \<in> poly_monoms p"
    using monom_mult_poly_monoms[of m c p] by force
  then obtain b where r'p: "(r', b) \<in> set p"
    by auto
  have "monom_vars r' \<subseteq> V"
    using monom_vars_subset_poly_vars[OF r'p] p
    by (auto simp: variables_poly_def)
  with m x show "x \<in> V"
    by (auto simp: r')
qed

lemma variables_poly_mult:
  assumes p: "variables_poly V p" and q: "variables_poly V q"
  shows "variables_poly V (poly_mult p q)"
  using p
proof (induction p)
  case Nil
  then show ?case
    by (simp add: poly_mult.simps variables_poly_def poly_vars_def)
next
  case (Cons t p)
  obtain m c where t: "t = (m, c)"
    by force
  have m_vars: "monom_vars m \<subseteq> V"
    using monom_vars_subset_poly_vars[of m c "t # p"] Cons.prems t
    by (auto simp: variables_poly_def)
  have p_vars: "variables_poly V p"
    using Cons.prems
    by (auto simp: variables_poly_def poly_vars_def)
  have head: "variables_poly V (monom_mult_poly (m, c) q)"
    by (rule variables_monom_mult_poly[OF m_vars q])
  have tail: "variables_poly V (poly_mult p q)"
    by (rule Cons.IH[OF p_vars])
  show ?case
    by (simp add: poly_mult.simps t variables_poly_add[OF head tail])
qed

lemma total_degree_poly_le_mult:
  assumes p: "total_degree_poly_le p d" and q: "total_degree_poly_le q e"
  shows "total_degree_poly_le (poly_mult p q) (d + e)"
  using p
proof (induction p)
  case Nil
  then show ?case
    by (simp add: poly_mult.simps total_degree_poly_le_def poly_degree_def)
next
  case (Cons t p)
  obtain m c where t: "t = (m, c)"
    by force
  have mc: "(m, c) \<in> set (t # p)"
    by (simp add: t)
  have m_degree: "monom_degree m \<le> d"
    by (rule total_degree_poly_leD[OF Cons.prems mc])
  have p_degree: "total_degree_poly_le p d"
    using Cons.prems t
    by (auto simp: total_degree_poly_le_def poly_degree_def)
  have head:
    "total_degree_poly_le (monom_mult_poly (m, c) q) (d + e)"
    by (rule total_degree_monom_mult_poly[OF m_degree q])
  have tail: "total_degree_poly_le (poly_mult p q) (d + e)"
    by (rule Cons.IH[OF p_degree])
  have "total_degree_poly_le
      (poly_add (monom_mult_poly (m, c) q) (poly_mult p q)) (d + e)"
    by (rule total_degree_poly_le_add[OF head tail])
  then show ?case
    by (simp add: poly_mult.simps t)
qed

lemma variables_poly_minus:
  assumes p: "variables_poly V p" and q: "variables_poly V q"
  shows "variables_poly V (poly_minus p q)"
proof -
  have neg: "variables_poly V (monom_mult_poly (1, -1) q)"
    by (rule variables_monom_mult_poly[OF _ q])
      (simp add: monom_vars_def)
  show ?thesis
    unfolding poly_minus_def
    by (rule variables_poly_add[OF p neg])
qed

lemma total_degree_poly_le_minus:
  assumes p: "total_degree_poly_le p d" and q: "total_degree_poly_le q d"
  shows "total_degree_poly_le (poly_minus p q) d"
proof -
  have neg': "total_degree_poly_le (monom_mult_poly (1, -1) q) (0 + d)"
    by (rule total_degree_monom_mult_poly[OF _ q]) simp
  have neg: "total_degree_poly_le (monom_mult_poly (1, -1) q) d"
    using neg' by simp
  show ?thesis
    unfolding poly_minus_def
    by (rule total_degree_poly_le_add[OF p neg])
qed

lemma variables_poly_power:
  assumes p: "variables_poly V p"
  shows "variables_poly V (poly_power p k)"
proof (induction k)
  case 0
  then show ?case
    by (simp add: poly_power.simps one_poly_def variables_poly_def poly_vars_def)
next
  case (Suc k)
  show ?case
    unfolding poly_power.simps
    by (rule variables_poly_mult[OF p Suc.IH])
qed

lemma total_degree_poly_le_power:
  assumes p: "total_degree_poly_le p d"
  shows "total_degree_poly_le (poly_power p k) (k * d)"
proof (induction k)
  case 0
  then show ?case
    by (simp add: poly_power.simps one_poly_def
      total_degree_poly_le_def poly_degree_def)
next
  case (Suc k)
  have "total_degree_poly_le (poly_mult p (poly_power p k)) (d + k * d)"
    by (rule total_degree_poly_le_mult[OF p Suc.IH])
  then show ?case
    by (simp add: poly_power.simps algebra_simps)
qed

lemma eval_poly_prod:
  "eval_poly \<alpha> (poly_prod ps) = prod_list (map (eval_poly \<alpha>) ps)"
  by (induction ps) simp_all

lemma variables_poly_prod:
  assumes "list_all (variables_poly V) ps"
  shows "variables_poly V (poly_prod ps)"
  using assms
proof (induction ps)
  case Nil
  then show ?case
    by (simp add: one_poly_def variables_poly_def poly_vars_def)
next
  case (Cons p ps)
  have p: "variables_poly V p" and ps: "list_all (variables_poly V) ps"
    using Cons.prems by simp_all
  show ?case
    by (simp add: variables_poly_mult[OF p Cons.IH[OF ps]])
qed

lemma total_degree_poly_prod:
  assumes "list_all2 total_degree_poly_le ps ds"
  shows "total_degree_poly_le (poly_prod ps) (sum_list ds)"
  using assms
proof (induction ps arbitrary: ds)
  case Nil
  then show ?case
    by (simp add: one_poly_def total_degree_poly_le_def poly_degree_def)
next
  case (Cons p ps)
  then obtain d ds' where ds: "ds = d # ds'"
    by (cases ds) auto
  have p: "total_degree_poly_le p d"
    using Cons.prems ds by simp
  have rest: "list_all2 total_degree_poly_le ps ds'"
    using Cons.prems ds by simp
  have "total_degree_poly_le (poly_mult p (poly_prod ps)) (d + sum_list ds')"
    by (rule total_degree_poly_le_mult[OF p Cons.IH[OF rest]])
  then show ?case
    by (simp add: ds)
qed

lemma eval_indicator_factor:
  "eval_poly \<alpha> (indicator_factor q p) = 1 - eval_poly \<alpha> p ^ (q - 1)"
  by (simp add: indicator_factor_def)

lemma eval_indicator_poly:
  "eval_poly \<alpha> (indicator_poly q ps) =
    prod_list (map (\<lambda>p. 1 - eval_poly \<alpha> p ^ (q - 1)) ps)"
  unfolding indicator_poly_def
  by (simp add: eval_poly_prod eval_indicator_factor comp_def)

lemma variables_indicator_factor:
  assumes "variables_poly V p"
  shows "variables_poly V (indicator_factor q p)"
  using assms
  by (simp add: indicator_factor_def variables_poly_minus variables_poly_power)

lemma variables_indicator_poly:
  assumes "list_all (variables_poly V) ps"
  shows "variables_poly V (indicator_poly q ps)"
proof -
  have "list_all (variables_poly V) (map (indicator_factor q) ps)"
    using assms
    by (auto simp: list_all_iff intro: variables_indicator_factor)
  then show ?thesis
    unfolding indicator_poly_def
    by (rule variables_poly_prod)
qed

lemma total_degree_indicator_factor:
  fixes p :: "('v::linorder, 'a::comm_ring_1) poly"
  assumes p: "total_degree_poly_le p d"
  shows "total_degree_poly_le (indicator_factor q p) ((q - 1) * d)"
proof -
  have pow: "total_degree_poly_le (poly_power p (q - 1)) ((q - 1) * d)"
    by (rule total_degree_poly_le_power[OF p])
  have const:
    "total_degree_poly_le (poly_const 1 :: ('v, 'a) poly)
      ((q - 1) * d)"
    by (rule total_degree_poly_le_mono[OF total_degree_poly_le_const]) simp
  show ?thesis
    unfolding indicator_factor_def
    by (rule total_degree_poly_le_minus[OF const pow])
qed

lemma total_degree_indicator_poly:
  assumes "list_all2 total_degree_poly_le ps ds"
  shows "total_degree_poly_le (indicator_poly q ps) ((q - 1) * sum_list ds)"
  using assms
proof (induction ps arbitrary: ds)
  case Nil
  then show ?case
    by (simp add: indicator_poly_def one_poly_def
      total_degree_poly_le_def poly_degree_def)
next
  case (Cons p ps)
  then obtain d ds' where ds: "ds = d # ds'"
    by (cases ds) auto
  have p: "total_degree_poly_le p d"
    using Cons.prems ds by simp
  have rest: "list_all2 total_degree_poly_le ps ds'"
    using Cons.prems ds by simp
  have factor:
    "total_degree_poly_le (indicator_factor q p) ((q - 1) * d)"
    by (rule total_degree_indicator_factor[OF p])
  have tail:
    "total_degree_poly_le (indicator_poly q ps) ((q - 1) * sum_list ds')"
    by (rule Cons.IH[OF rest])
  have "total_degree_poly_le
      (poly_mult (indicator_factor q p) (indicator_poly q ps))
      ((q - 1) * d + (q - 1) * sum_list ds')"
    by (rule total_degree_poly_le_mult[OF factor tail])
  then show ?case
    by (simp add: indicator_poly_def ds algebra_simps)
qed

subsection \<open>Finite-field power sums\<close>

lemma finite_field_card_gt_one:
  "1 < card (UNIV :: 'a::finite_field set)"
proof -
  have "card ({0, 1} :: 'a set) \<le> card (UNIV :: 'a set)"
    by (rule card_mono) auto
  then show ?thesis
    by simp
qed

lemma finite_field_power_card_minus_one:
  fixes x :: "'a::finite_field"
  assumes "x \<noteq> 0"
  shows "x ^ (card (UNIV :: 'a set) - 1) = 1"
proof -
  let ?q = "card (UNIV :: 'a set)"
  have q_gt: "1 < ?q"
    by (rule finite_field_card_gt_one)
  have "x ^ ?q = x"
    by (rule finite_field_power_card_eq_same)
  moreover have "x ^ ?q = x ^ (?q - 1) * x"
  proof -
    have q_suc: "?q = Suc (?q - 1)"
      using q_gt by simp
    have "x ^ ?q = x ^ Suc (?q - 1)"
      using q_suc by simp
    also have "\<dots> = x ^ (?q - 1) * x"
      by (rule power_Suc2)
    finally show ?thesis .
  qed
  ultimately have "x ^ (?q - 1) * x = 1 * x"
    by simp
  then show ?thesis
    using assms by simp
qed

lemma finite_field_exists_power_ne_one:
  fixes k :: nat
  assumes k_pos: "0 < k"
  assumes k_lt: "k < card (UNIV :: 'a::finite_field set) - 1"
  shows "\<exists>a::'a. a \<noteq> 0 \<and> a ^ k \<noteq> 1"
proof -
  let ?P = "monom (1::'a) k - 1"
  have P_nonzero: "?P \<noteq> 0"
  proof
    assume "?P = 0"
    then have "poly.coeff ?P k = 0"
      by simp
    moreover have "poly.coeff ?P k = 1"
      using k_pos by simp
    ultimately show False
      by simp
  qed
  have deg_P: "degree ?P \<le> k"
  proof -
    have deg_monom: "degree (monom (1::'a) k) \<le> k"
      by (rule degree_monom_le)
    have deg_one: "degree (1::'a Polynomial.poly) \<le> k"
      using k_pos by simp
    have "degree ?P \<le>
        max (degree (monom (1::'a) k)) (degree (1::'a Polynomial.poly))"
      by (rule degree_diff_le_max)
    also have "\<dots> \<le> k"
      using deg_monom deg_one by simp
    finally show ?thesis .
  qed
  have roots_bound: "card {x::'a. poly ?P x = 0} \<le> k"
  proof -
    have "card {x::'a. poly ?P x = 0} \<le> degree ?P"
      by (rule card_poly_roots_bound[OF P_nonzero])
    also have "\<dots> \<le> k"
      by (rule deg_P)
    finally show ?thesis .
  qed
  let ?NZ = "{x::'a. x \<noteq> 0}"
  have card_NZ: "card ?NZ = card (UNIV :: 'a set) - 1"
  proof -
    have "?NZ = (UNIV :: 'a set) - {0}"
      by auto
    also have "card \<dots> = card (UNIV :: 'a set) - card ({0} :: 'a set)"
      by (rule card_Diff_subset) auto
    finally show ?thesis
      by simp
  qed
  show ?thesis
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have all_roots: "\<And>x::'a. x \<noteq> 0 \<Longrightarrow> x ^ k = 1"
      by blast
    have NZ_roots: "?NZ \<subseteq> {x::'a. poly ?P x = 0}"
      using all_roots by (auto simp: poly_monom)
    have "card ?NZ \<le> card {x::'a. poly ?P x = 0}"
      by (rule card_mono[OF poly_roots_finite[OF P_nonzero] NZ_roots])
    also have "\<dots> \<le> k"
      by (rule roots_bound)
    finally show False
      using k_lt card_NZ by simp
  qed
qed

lemma finite_field_power_sum_less:
  assumes k_lt: "k < card (UNIV :: 'a::finite_field set) - 1"
  shows "(\<Sum>x\<in>UNIV. x ^ k :: 'a) = 0"
proof (cases "k = 0")
  case True
  have "(of_nat (card (UNIV :: 'a set)) :: 'a) = 0"
    by (simp add: of_nat_eq_0_iff_char_dvd CHAR_dvd_CARD)
  with True show ?thesis
    by simp
next
  case False
  then obtain a :: 'a where a0: "a \<noteq> 0" and ak: "a ^ k \<noteq> 1"
    using finite_field_exists_power_ne_one[of k] k_lt by auto
  let ?S = "(\<Sum>x\<in>UNIV. x ^ k :: 'a)"
  have "?S = (\<Sum>x\<in>UNIV. (a * x) ^ k)"
    by (rule sum.reindex_bij_witness[where i = "\<lambda>x. a * x" and j = "\<lambda>x. x / a"])
      (use a0 in auto)
  also have "\<dots> = a ^ k * ?S"
    by (simp add: power_mult_distrib sum_distrib_left)
  finally have "(a ^ k - 1) * ?S = 0"
    by (simp add: algebra_simps)
  with ak show ?thesis
    by simp
qed

lemma eval_monom_list_prod_sum_var:
  fixes \<alpha> :: "'v::linorder \<Rightarrow> 'a::comm_semiring_1"
  assumes finite: "finite V" and vars: "fst ` set m \<subseteq> V"
  shows "eval_monom_list \<alpha> m =
    (\<Prod>x\<in>V. \<alpha> x ^ sum_var_list m x)"
  using assms
proof (induction m)
  case Nil
  then show ?case
    by (simp add: sum_var_list_def)
next
  case (Cons ve m)
  obtain v e where ve: "ve = (v, e)"
    by force
  have vV: "v \<in> V" and mV: "fst ` set m \<subseteq> V"
    using Cons.prems by (auto simp: ve)
  have delta_prod:
    "(\<Prod>x\<in>V. \<alpha> x ^ (if x = v then e else 0)) = \<alpha> v ^ e"
  proof -
    have "(\<Prod>x\<in>V. \<alpha> x ^ (if x = v then e else 0)) =
        (\<Prod>x\<in>V. if x = v then \<alpha> x ^ e else 1)"
      by (intro prod.cong) auto
    also have "\<dots> = \<alpha> v ^ e"
      using Cons.prems(1) vV
      by (simp add: prod.delta)
    finally show ?thesis .
  qed
  have "(\<Prod>x\<in>V. \<alpha> x ^ sum_var_list (ve # m) x) =
      (\<Prod>x\<in>V.
        \<alpha> x ^ (if x = v then e else 0) * \<alpha> x ^ sum_var_list m x)"
    by (intro prod.cong)
      (simp_all add: ve sum_var_list_def power_add)
  also have "\<dots> =
      (\<Prod>x\<in>V. \<alpha> x ^ (if x = v then e else 0)) *
      (\<Prod>x\<in>V. \<alpha> x ^ sum_var_list m x)"
    by (rule prod.distrib)
  also have "\<dots> = \<alpha> v ^ e * eval_monom_list \<alpha> m"
    by (simp add: delta_prod Cons.IH[OF Cons.prems(1) mV])
  also have "\<dots> = eval_monom_list \<alpha> (ve # m)"
    by (simp add: ve algebra_simps)
  finally show ?case
    by simp
qed

lemma eval_monom_prod_sum_var:
  fixes \<alpha> :: "'v::linorder \<Rightarrow> 'a::comm_semiring_1"
  assumes "finite V" "monom_vars m \<subseteq> V"
  shows "eval_monom \<alpha> m = (\<Prod>x\<in>V. \<alpha> x ^ sum_var m x)"
  using assms
  unfolding monom_vars_def
  by transfer (auto intro: eval_monom_list_prod_sum_var)

lemma monom_list_degree_sum_var:
  fixes m :: "'v::linorder monom_list"
  assumes "finite V" "fst ` set m \<subseteq> V"
  shows "monom_list_degree m = (\<Sum>x\<in>V. sum_var_list m x)"
  using assms
proof (induction m)
  case Nil
  then show ?case
    by (simp add: monom_list_degree_def sum_var_list_def)
next
  case (Cons ve m)
  obtain v e where ve: "ve = (v, e)"
    by force
  have vV: "v \<in> V" and mV: "fst ` set m \<subseteq> V"
    using Cons.prems by (auto simp: ve)
  have IH:
    "monom_list_degree m = (\<Sum>x\<in>V. sum_var_list m x)"
    by (rule Cons.IH[OF Cons.prems(1) mV])
  have delta: "(\<Sum>x\<in>V. if x = v then e else 0) = e"
    using Cons.prems(1) vV
    by (simp add: sum.delta)
  have "monom_list_degree (ve # m) = e + monom_list_degree m"
    by (simp add: ve monom_list_degree_def)
  also have "\<dots> = e + (\<Sum>x\<in>V. sum_var_list m x)"
    using IH by simp
  also have "\<dots> =
      (\<Sum>x\<in>V. if x = v then e else 0) +
      (\<Sum>x\<in>V. sum_var_list m x)"
    using delta by simp
  also have "\<dots> =
      (\<Sum>x\<in>V. (if x = v then e else 0) + sum_var_list m x)"
    by (simp add: sum.distrib)
  also have "\<dots> = (\<Sum>x\<in>V. sum_var_list (ve # m) x)"
    by (intro sum.cong) (simp_all add: ve sum_var_list_def)
  finally show ?case .
qed

lemma monom_degree_sum_var:
  fixes m :: "'v::linorder monom"
  assumes "finite V" "monom_vars m \<subseteq> V"
  shows "monom_degree m = (\<Sum>x\<in>V. sum_var m x)"
  using assms
  unfolding monom_vars_def
  by transfer (auto intro: monom_list_degree_sum_var)

lemma sum_monom_assignments:
  fixes m :: "'v::linorder monom"
  assumes finite: "finite V" and vars: "monom_vars m \<subseteq> V"
  shows "(\<Sum>\<alpha>\<in>PiE V (\<lambda>_. UNIV :: 'a::finite_field set).
      eval_monom \<alpha> m) =
    (\<Prod>x\<in>V. \<Sum>y\<in>(UNIV :: 'a set). y ^ sum_var m x)"
proof -
  have "(\<Prod>x\<in>V. \<Sum>y\<in>(UNIV :: 'a set). y ^ sum_var m x) =
      (\<Sum>\<alpha>\<in>PiE V (\<lambda>_. UNIV).
        \<Prod>x\<in>V. \<alpha> x ^ sum_var m x)"
    by (rule prod_sum_PiE[OF finite]) simp
  then show ?thesis
    by (simp add: eval_monom_prod_sum_var[OF finite vars])
qed

lemma exists_variable_degree_lt:
  assumes finite: "finite V"
  assumes "(\<Sum>x\<in>V. f x) < card V * k"
  shows "\<exists>x\<in>V. f x < k"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have ge: "\<And>x. x \<in> V \<Longrightarrow> k \<le> f x"
    by force
  have "card V * k = (\<Sum>x\<in>V. k)"
    using finite by simp
  also have "\<dots> \<le> (\<Sum>x\<in>V. f x)"
    by (rule sum_mono) (use ge in auto)
  finally show False
    using assms by simp
qed

lemma monomial_sum_zero_if_degree_lt:
  fixes m :: "'v::linorder monom"
  assumes finite: "finite V" and vars: "monom_vars m \<subseteq> V"
  assumes deg:
    "monom_degree m <
      card V * (card (UNIV :: 'a::finite_field set) - 1)"
  shows "(\<Sum>\<alpha>\<in>PiE V (\<lambda>_. UNIV :: 'a set). eval_monom \<alpha> m) = 0"
proof -
  have "\<exists>x\<in>V. sum_var m x < card (UNIV :: 'a set) - 1"
  proof (rule exists_variable_degree_lt[OF finite])
    show "(\<Sum>x\<in>V. sum_var m x) <
        card V * (card (UNIV :: 'a set) - 1)"
      using deg monom_degree_sum_var[OF finite vars] by simp
  qed
  then obtain x where xV: "x \<in> V"
    and x_lt: "sum_var m x < card (UNIV :: 'a set) - 1"
    by blast
  have factor_zero:
    "(\<Sum>y\<in>UNIV. (y::'a) ^ sum_var m x) = 0"
    by (rule finite_field_power_sum_less[OF x_lt])
  have "(\<Prod>x\<in>V. \<Sum>y\<in>(UNIV :: 'a set). y ^ sum_var m x) = 0"
  proof (rule prod_zero[OF finite])
    show "\<exists>x\<in>V. (\<Sum>y\<in>(UNIV :: 'a set). y ^ sum_var m x) = 0"
      using xV factor_zero by blast
  qed
  then show ?thesis
    using sum_monom_assignments[OF finite vars, where 'a='a] by simp
qed

lemma finite_field_sum_poly_zero:
  assumes finite: "finite V" and vars: "variables_poly V p"
  assumes deg:
    "total_degree_poly_less p
      (card V * (card (UNIV :: 'a::finite_field set) - 1))"
  shows "(\<Sum>\<alpha>\<in>PiE V (\<lambda>_. UNIV :: 'a set). eval_poly \<alpha> p) = 0"
  using vars deg
proof (induction p)
  case Nil
  then show ?case
    by simp
next
  case (Cons t p)
  obtain m c where t: "t = (m, c)"
    by force
  have m_vars: "monom_vars m \<subseteq> V"
    using monom_vars_subset_poly_vars[of m c "t # p"] Cons.prems(1) t
    by (auto simp: variables_poly_def)
  have mc: "(m, c) \<in> set (t # p)"
    by (simp add: t)
  have m_deg:
    "monom_degree m <
      card V * (card (UNIV :: 'a set) - 1)"
    by (rule total_degree_poly_lessD[OF Cons.prems(2) mc])
  have p_vars: "variables_poly V p"
    using Cons.prems(1)
    by (auto simp: variables_poly_def poly_vars_def)
  have p_deg:
    "total_degree_poly_less p
      (card V * (card (UNIV :: 'a set) - 1))"
    using Cons.prems(2) t
    by (auto simp: total_degree_poly_less_def poly_degree_def)
  have head:
    "(\<Sum>\<alpha>\<in>PiE V (\<lambda>_. UNIV :: 'a set). eval_monom \<alpha> m * c) = 0"
  proof -
    have "(\<Sum>\<alpha>\<in>PiE V (\<lambda>_. UNIV :: 'a set).
        eval_monom \<alpha> m * c) =
        (\<Sum>\<alpha>\<in>PiE V (\<lambda>_. UNIV :: 'a set). eval_monom \<alpha> m) * c"
      by (simp add: sum_distrib_right)
    also have "\<dots> = 0"
      by (simp add: monomial_sum_zero_if_degree_lt[OF finite m_vars m_deg])
    finally show ?thesis .
  qed
  have "(\<Sum>\<alpha>\<in>PiE V (\<lambda>_. UNIV :: 'a set).
      eval_poly \<alpha> (t # p)) =
      (\<Sum>\<alpha>\<in>PiE V (\<lambda>_. UNIV :: 'a set).
        eval_monom \<alpha> m * c + eval_poly \<alpha> p)"
    by (intro sum.cong) (simp_all add: t)
  also have "\<dots> =
      (\<Sum>\<alpha>\<in>PiE V (\<lambda>_. UNIV :: 'a set).
        eval_monom \<alpha> m * c) +
      (\<Sum>\<alpha>\<in>PiE V (\<lambda>_. UNIV :: 'a set). eval_poly \<alpha> p)"
    by (simp add: sum.distrib)
  also have "\<dots> = 0"
    using head Cons.IH[OF p_vars p_deg] by simp
  finally show ?case .
qed

subsection \<open>The theorem\<close>

lemma finite_field_indicator_factor_value:
  fixes y :: "'a::finite_field"
  shows "1 - y ^ (card (UNIV :: 'a set) - 1) = of_bool (y = 0)"
proof (cases "y = 0")
  case True
  have "0 < card (UNIV :: 'a set) - 1"
    using finite_field_card_gt_one[where 'a='a] by simp
  with True show ?thesis
    by (simp add: of_bool_def)
next
  case False
  then have "y ^ (card (UNIV :: 'a set) - 1) = 1"
    by (rule finite_field_power_card_minus_one)
  with False show ?thesis
    by (simp add: of_bool_def)
qed

lemma prod_list_of_bool_list_all:
  "prod_list (map (\<lambda>x. of_bool (P x) :: 'a::comm_semiring_1) xs) =
    of_bool (list_all P xs)"
  by (induction xs) (simp_all add: of_bool_def)

lemma eval_indicator_poly_value:
  fixes ps :: "('v::linorder, 'a::finite_field) poly list"
  shows "eval_poly \<alpha> (indicator_poly (card (UNIV :: 'a set)) ps) =
    of_bool (list_all (\<lambda>p. eval_poly \<alpha> p = 0) ps)"
proof -
  have "eval_poly \<alpha> (indicator_poly (card (UNIV :: 'a set)) ps) =
      prod_list
        (map (\<lambda>p. 1 - eval_poly \<alpha> p ^ (card (UNIV :: 'a set) - 1)) ps)"
    by (rule eval_indicator_poly)
  also have "\<dots> =
      prod_list (map (\<lambda>p. of_bool (eval_poly \<alpha> p = 0) :: 'a) ps)"
  proof (rule arg_cong[where f=prod_list])
    show "map (\<lambda>p. 1 - eval_poly \<alpha> p ^ (card (UNIV :: 'a set) - 1)) ps =
      map (\<lambda>p. of_bool (eval_poly \<alpha> p = 0) :: 'a) ps"
      by (intro map_cong refl finite_field_indicator_factor_value)
  qed
  also have "\<dots> = of_bool (list_all (\<lambda>p. eval_poly \<alpha> p = 0) ps)"
    by (rule prod_list_of_bool_list_all)
  finally show ?thesis .
qed

lemma list_all2_variables:
  assumes
    "list_all2 (\<lambda>p d. variables_poly V p \<and> total_degree_poly_le p d) ps ds"
  shows "list_all (variables_poly V) ps"
  using assms
proof (induction ps arbitrary: ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons p ps)
  then obtain d ds' where ds: "ds = d # ds'"
    by (cases ds) auto
  then show ?case
    using Cons.IH[of ds'] Cons.prems by auto
qed

lemma list_all2_degrees:
  assumes
    "list_all2 (\<lambda>p d. variables_poly V p \<and> total_degree_poly_le p d) ps ds"
  shows "list_all2 total_degree_poly_le ps ds"
  using assms
proof (induction ps arbitrary: ds)
  case Nil
  then show ?case
    by (cases ds) auto
next
  case (Cons p ps)
  then obtain d ds' where
    ds: "ds = d # ds'"
    and p: "total_degree_poly_le p d"
    and rest:
      "list_all2
        (\<lambda>p d. variables_poly V p \<and> total_degree_poly_le p d) ps ds'"
    by (cases ds) auto
  have "list_all2 total_degree_poly_le ps ds'"
    by (rule Cons.IH[OF rest])
  with p show ?case
    by (simp add: ds)
qed

theorem chevalley_warning:
  fixes V :: "'v::linorder set"
    and ps :: "('v, 'a::finite_field) poly list"
  assumes finite: "finite V"
  assumes polys:
    "list_all2 (\<lambda>p d. variables_poly V p \<and> total_degree_poly_le p d) ps ds"
  assumes degree_sum: "sum_list ds < card V"
  shows "CHAR('a) dvd card (common_zeros V ps)"
proof -
  let ?q = "card (UNIV :: 'a set)"
  let ?I = "indicator_poly ?q ps"
  have q_minus_pos: "0 < ?q - 1"
    using finite_field_card_gt_one[where 'a='a] by simp
  have variables: "list_all (variables_poly V) ps"
    by (rule list_all2_variables[OF polys])
  have I_variables: "variables_poly V ?I"
    by (rule variables_indicator_poly[OF variables])
  have degrees: "list_all2 total_degree_poly_le ps ds"
    by (rule list_all2_degrees[OF polys])
  have I_degree_le:
    "total_degree_poly_le ?I ((?q - 1) * sum_list ds)"
    by (rule total_degree_indicator_poly[OF degrees])
  have degree_bound:
    "(?q - 1) * sum_list ds < card V * (?q - 1)"
    using degree_sum q_minus_pos
    by (simp add: mult_less_cancel1)
  have I_degree_less:
    "total_degree_poly_less ?I (card V * (?q - 1))"
    by (rule total_degree_poly_less_of_le[OF I_degree_le degree_bound])
  have sum_zero:
    "(\<Sum>\<alpha>\<in>PiE V (\<lambda>_. UNIV :: 'a set). eval_poly \<alpha> ?I) = 0"
    by (rule finite_field_sum_poly_zero[OF finite I_variables I_degree_less])
  have finite_assignments: "finite (PiE V (\<lambda>_. UNIV :: 'a set))"
    by (rule finite_PiE[OF finite]) simp
  have sum_card:
    "(\<Sum>\<alpha>\<in>PiE V (\<lambda>_. UNIV :: 'a set). eval_poly \<alpha> ?I) =
      of_nat (card (common_zeros V ps))"
  proof -
    have "(\<Sum>\<alpha>\<in>PiE V (\<lambda>_. UNIV :: 'a set). eval_poly \<alpha> ?I) =
        (\<Sum>\<alpha>\<in>PiE V (\<lambda>_. UNIV :: 'a set).
          of_bool (list_all (\<lambda>p. eval_poly \<alpha> p = 0) ps) :: 'a)"
      by (intro sum.cong)
        (simp_all add: eval_indicator_poly_value)
    also have "\<dots> =
        of_nat (card {\<alpha> \<in> PiE V (\<lambda>_. UNIV :: 'a set).
          list_all (\<lambda>p. eval_poly \<alpha> p = 0) ps})"
    proof -
      have "(PiE V (\<lambda>_. UNIV :: 'a set) \<inter>
          {\<alpha>. list_all (\<lambda>p. eval_poly \<alpha> p = 0) ps}) =
          {\<alpha> \<in> PiE V (\<lambda>_. UNIV :: 'a set).
            list_all (\<lambda>p. eval_poly \<alpha> p = 0) ps}"
        by auto
      with finite_assignments show ?thesis
        by simp
    qed
    also have "{\<alpha> \<in> PiE V (\<lambda>_. UNIV :: 'a set).
          list_all (\<lambda>p. eval_poly \<alpha> p = 0) ps} = common_zeros V ps"
      by (auto simp: common_zeros_def)
    finally show ?thesis .
  qed
  have "(of_nat (card (common_zeros V ps)) :: 'a) = 0"
    using sum_zero sum_card by simp
  then show ?thesis
    by (simp add: of_nat_eq_0_iff_char_dvd)
qed

corollary chevalley_warning_finite_type:
  fixes ps :: "('v::{finite,linorder}, 'a::finite_field) poly list"
  assumes polys: "list_all2 total_degree_poly_le ps ds"
  assumes degree_sum: "sum_list ds < card (UNIV :: 'v set)"
  shows "CHAR('a) dvd card (common_zeros UNIV ps)"
proof (rule chevalley_warning[where ds=ds])
  show "finite (UNIV :: 'v set)"
    by simp
  show "list_all2
      (\<lambda>p d. variables_poly UNIV p \<and> total_degree_poly_le p d) ps ds"
    using polys
    by (rule list_all2_mono) simp
  show "sum_list ds < card (UNIV :: 'v set)"
    using degree_sum by simp
qed

end
