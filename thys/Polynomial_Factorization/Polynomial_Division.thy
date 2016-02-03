(*
    Author:      René Thiemann
    License:     BSD
*)

section \<open>Division of Polynomials over Integral Domains\<close>

text \<open>This theory contains two algorithms to compute (pseudo) polynomial long division
  of polynomials over integral domains. The one for pseudo division of $f$ and $g$ computes 
  a quotient and remainder such that $cf = qg + r$ for a suitable constant $c$. The latter
  one implements standard polynomial long division where it is guaranteed that division of
  $fg$ by $g$ yields $f$.\<close>

theory Polynomial_Division
imports 
  "../Polynomial_Interpolation/Missing_Polynomial"
  Complex
begin
text \<open>A following type class is similar to @{class idom_divide}, but it has its own division operator.
  This is necessary for nesting, since the existing division on polynomials is only defined if the coefficients
  are taken from a field. In contrast, the upcoming algorithms allow nesting of polynomials, e.g., to perform
  division of polynomials over polynomials over polynomials over integer numbers.\<close>

class idom_div = idom + 
  fixes exact_div :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes exact_div_right[simp]: "b \<noteq> 0 \<Longrightarrow> exact_div (a * b) b = a"  
begin
lemma exact_div_left[simp]: "b \<noteq> 0 \<Longrightarrow> exact_div (b * a) b = a" unfolding mult.commute[of b a]
  by (rule exact_div_right)
end

definition pseudo_exponent :: "'a :: semiring_0 poly \<Rightarrow> 'a poly \<Rightarrow> nat" where
  "pseudo_exponent p q = (Suc (degree p) - degree q)" 

fun pseudo_divmod_main :: "'a :: idom_div \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly 
  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a poly \<times> 'a poly" where
  "pseudo_divmod_main lc q r d dr n = (if n = 0 then (q,r) else let
     rr = smult lc r;
     a = coeff rr dr;
     qq = exact_div a lc;
     n1 = n - 1;
     b = monom qq n1;
     rrr = rr - b * d;
     qqq = smult lc q + b
     in pseudo_divmod_main lc qqq rrr d (dr - 1) n1)"

fun p_div_main :: "'a :: idom_div \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly 
  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a poly" where
  "p_div_main lc q r d dr n = (if n = 0 then q else let
     a = coeff r dr;
     qq = exact_div a lc;
     n1 = n - 1;
     b = monom qq n1;
     rr = r - b * d;
     qqq = q + b
     in p_div_main lc qqq rr d (dr - 1) n1)"

definition pseudo_divmod :: "'a :: idom_div poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<times> 'a poly" where
  "pseudo_divmod p q = (let dp = degree p; dq = degree q 
     in pseudo_divmod_main (coeff q dq) 0 p q dp (1 + dp - dq))"

definition p_div :: "'a :: idom_div poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "p_div p q = (let dp = degree p; dq = degree q 
     in p_div_main (coeff q dq) 0 p q dp (1 + dp - dq))"

lemma coeff_0_degree_minus_1: "coeff rrr dr = 0 \<Longrightarrow> degree rrr \<le> dr \<Longrightarrow> degree rrr \<le> dr - 1"
  using eq_zero_or_degree_less by fastforce
  
lemma pseudo_divmod_main: assumes d: "d \<noteq> 0" "lc = coeff d (degree d)"
  and *: "degree r \<le> dr" "pseudo_divmod_main lc q r d dr n = (q',r')" 
    "n = 1 + dr - degree d \<or> dr = 0 \<and> n = 0 \<and> r = 0" 
  shows "(r' = 0 \<or> degree r' < degree d) \<and> smult (lc^n) (d * q + r) = d * q' + r'"
  using *
proof (induct n arbitrary: q r dr)
  case (Suc n q r dr)
  let ?rr = "smult lc r"
  let ?a = "coeff ?rr dr"
  let ?qq = "exact_div ?a lc"
  def qq \<equiv> ?qq
  let ?n = "Suc n"
  let ?b = "monom qq n"
  def b \<equiv> ?b
  let ?rrr = "?rr - b * d"
  def rrr \<equiv> ?rrr
  let ?qqq = "smult lc q + b"
  note res = Suc(3)
  from res[unfolded pseudo_divmod_main.simps[of lc q] Let_def] 
  have res: "pseudo_divmod_main lc ?qqq ?rrr d (dr - 1) n = (q',r')" 
    by (simp del: pseudo_divmod_main.simps add: b_def qq_def)
  have dr: "dr = n + degree d" using Suc(4) by auto
  have c1: "coeff ?rr dr = lc * coeff r dr" by simp
  have lc: "lc \<noteq> 0" using d by auto
  have "coeff (b * d) dr = coeff b n * coeff d (degree d)"
  proof (cases "qq = 0")
    case True
    thus ?thesis unfolding b_def by auto
  next
    case False
    hence n: "n = degree b" unfolding b_def by (simp add: degree_monom_eq)
    show ?thesis unfolding n dr by (simp add: coeff_mult_degree_sum)
  qed
  also have "\<dots> = lc * coeff b n" unfolding d by simp
  finally have c2: "coeff (b * d) dr = lc * coeff b n" .
  have c0: "coeff ?rrr dr = 0" unfolding coeff_diff c1 c2 
    unfolding b_def qq_def coeff_monom coeff_smult using lc by auto
  have dr: "dr = n + degree d" using Suc(4) by auto
  have deg_rr: "degree ?rr \<le> dr" using Suc(2) by auto
  have deg_bd: "degree (b * d) \<le> dr" by (auto simp: dr b_def, rule order.trans[OF degree_mult_le],
    auto simp: degree_monom_le)
  have "degree ?rrr \<le> dr"
    by (rule degree_diff_le[OF deg_rr deg_bd])
  with c0 have deg_rrr: "degree ?rrr \<le> (dr - 1)" by (rule coeff_0_degree_minus_1)
  have "n = 1 + (dr - 1) - degree d \<or> dr - 1 = 0 \<and> n = 0 \<and> ?rrr = 0"  
  proof (cases dr)
    case 0
    with Suc(4) have 0: "dr = 0" "n = 0" "degree d = 0" by auto
    with deg_rrr have "degree ?rrr = 0" by simp
    from degree0_coeffs[OF this] obtain a where rrr: "?rrr = [:a:]" by auto
    show ?thesis unfolding 0 using c0 unfolding rrr 0 by simp
  qed (insert Suc(4), auto)
  note IH = Suc(1)[OF deg_rrr res this]
  show ?case
  proof (intro conjI)
    show "r' = 0 \<or> degree r' < degree d" using IH by blast
    show "smult (lc ^ Suc n) (d * q + r) = d * q' + r'"
      unfolding IH[THEN conjunct2,symmetric]
      by (simp add: field_simps smult_add_right)
  qed
qed auto

lemma pseudo_divmod: assumes g: "g \<noteq> 0"
  and *: "pseudo_divmod f g = (q,r)" 
  shows "smult (coeff g (degree g) ^ pseudo_exponent f g) f = g * q + r" "r = 0 \<or> degree r < degree g"
proof -
  from *[unfolded pseudo_divmod_def Let_def]
  have "pseudo_divmod_main (coeff g (degree g)) 0 f g (degree f) (1 + degree f - degree g) = (q, r)" by (auto simp: g)
  note main = pseudo_divmod_main[OF _ _ _ this, OF g refl le_refl]
  from main show "r = 0 \<or> degree r < degree g" by auto
  from main show "smult (coeff g (degree g) ^ pseudo_exponent f g) f = g * q + r" 
    by (simp add: pseudo_exponent_def)
qed

lemma p_div_main: assumes d: "d \<noteq> 0" "lc = coeff d (degree d)"
  and *: "degree (d * r) \<le> dr" "p_div_main lc q (d * r) d dr n = q'" 
    "n = 1 + dr - degree d \<or> dr = 0 \<and> n = 0 \<and> d * r = 0" 
  shows "q' = q + r"
  using *
proof (induct n arbitrary: q r dr)
  case (Suc n q r dr)
  let ?rr = "d * r"
  let ?a = "coeff ?rr dr"
  let ?qq = "exact_div ?a lc"
  def qq \<equiv> ?qq
  let ?n = "Suc n"
  let ?b = "monom qq n"
  def b \<equiv> ?b
  let ?rrr = "d * (r - b)"
  def rrr \<equiv> ?rrr
  let ?qqq = "q + b"
  note res = Suc(3)
  from res[unfolded p_div_main.simps[of lc q] Let_def] 
  have res: "p_div_main lc ?qqq ?rrr d (dr - 1) n = q'" 
    by (simp del: p_div_main.simps add: b_def qq_def field_simps)
  note IH = Suc(1)[OF _ res] 
  have dr: "dr = n + degree d" using Suc(4) by auto
  have lc: "lc \<noteq> 0" using d by auto
  have "coeff (b * d) dr = coeff b n * coeff d (degree d)"
  proof (cases "qq = 0")
    case True
    thus ?thesis unfolding b_def by auto
  next
    case False
    hence n: "n = degree b" unfolding b_def by (simp add: degree_monom_eq)
    show ?thesis unfolding n dr by (simp add: coeff_mult_degree_sum)
  qed
  also have "\<dots> = lc * coeff b n" unfolding d by simp
  finally have c2: "coeff (b * d) dr = lc * coeff b n" .
  have rrr: "?rrr = ?rr - b * d" by (simp add: field_simps)
  have c1: "coeff (d * r) dr = lc * coeff r n"
  proof (cases "degree r = n")
    case True
    thus ?thesis using Suc(2) unfolding dr using coeff_mult_degree_sum[of d r] d by (auto simp: ac_simps)
  next
    case False
    have "degree r \<le> n" using dr Suc(2) by auto
      (metis add.commute add_le_cancel_left d(1) degree_0 degree_mult_eq diff_is_0_eq diff_zero le_cases)
    with False have r_n: "degree r < n" by auto
    hence right: "lc * coeff r n = 0" by (simp add: coeff_eq_0)
    have "coeff (d * r) dr = coeff (d * r) (degree d + n)" unfolding dr by (simp add: ac_simps)
    also have "\<dots> = 0" using r_n
      by (metis False Suc.prems(1) add.commute add_left_imp_eq coeff_degree_mult coeff_eq_0 
        coeff_mult_degree_sum degree_mult_le dr le_eq_less_or_eq)
    finally show ?thesis unfolding right .
  qed
  have c0: "coeff ?rrr dr = 0" unfolding rrr coeff_diff c2
    unfolding b_def qq_def coeff_monom coeff_smult c1 using lc by auto
  have dr: "dr = n + degree d" using Suc(4) by auto
  have deg_rr: "degree ?rr \<le> dr" using Suc(2) by auto
  have deg_bd: "degree (b * d) \<le> dr" by (auto simp: dr b_def, rule order.trans[OF degree_mult_le],
    auto simp: degree_monom_le)
  have "degree ?rrr \<le> dr" unfolding rrr
    by (rule degree_diff_le[OF deg_rr deg_bd])
  with c0 have deg_rrr: "degree ?rrr \<le> (dr - 1)" by (rule coeff_0_degree_minus_1)
  have "n = 1 + (dr - 1) - degree d \<or> dr - 1 = 0 \<and> n = 0 \<and> ?rrr = 0"  
  proof (cases dr)
    case 0
    with Suc(4) have 0: "dr = 0" "n = 0" "degree d = 0" by auto
    with deg_rrr have "degree ?rrr = 0" by simp
    from degree0_coeffs[OF this] obtain a where rrr: "?rrr = [:a:]" by auto
    show ?thesis unfolding 0 using c0 unfolding rrr 0 by simp
  qed (insert Suc(4), auto)
  note IH = IH[OF deg_rrr this]
  show ?case using IH by simp
next
  case (0 q r dr)
  show ?case 
  proof (cases "r = 0")
    case True
    thus ?thesis using 0 by auto
  next
    case False
    have "degree (d * r) = degree d + degree r" using d False 
      by (subst degree_mult_eq, auto)
    thus ?thesis using 0 d by auto
  qed
qed 

lemma p_div: assumes g: "g \<noteq> 0"
  shows "p_div (f * g) g = f" 
proof -
  have "p_div_main (coeff g (degree g)) 0 (g * f) g (degree (g * f)) (1 + degree (g * f) - degree g) 
    = p_div (f * g) g" unfolding p_div_def Let_def by (simp add: ac_simps)
  from p_div_main[OF g _ _ this]
  show ?thesis by simp
qed

  
instantiation int :: idom_div
begin
definition exact_div_int :: "int \<Rightarrow> int \<Rightarrow> int" where
  [code_unfold]: "exact_div_int = op div"
instance 
  by (standard, auto simp: exact_div_int_def)
end

instantiation rat :: idom_div
begin
definition exact_div_rat :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  [code_unfold]: "exact_div_rat = op div"
instance 
  by (standard, auto simp: exact_div_rat_def)
end

instantiation real :: idom_div
begin
definition exact_div_real :: "real \<Rightarrow> real \<Rightarrow> real" where
  [code_unfold]: "exact_div_real = op div"
instance 
  by (standard, auto simp: exact_div_real_def)
end

instantiation complex :: idom_div
begin
definition exact_div_complex :: "complex \<Rightarrow> complex \<Rightarrow> complex" where
  [code_unfold]: "exact_div_complex = op div"
instance 
  by (standard, auto simp: exact_div_complex_def)
end

instantiation poly :: (idom_div) idom_div
begin
definition exact_div_poly :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  [code_unfold]: "exact_div_poly = p_div"
instance
  by (standard, auto simp: exact_div_poly_def p_div)
end

end
