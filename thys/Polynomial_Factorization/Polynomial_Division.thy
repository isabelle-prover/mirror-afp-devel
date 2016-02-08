(*
    Author:      René Thiemann
    License:     BSD
*)

section \<open>Division of Polynomials over Integral Domains\<close>

text \<open>This theory contains two algorithms to compute (pseudo) polynomial long division
  of polynomials over integral domains. The one for pseudo division of $f$ and $g$ computes 
  a quotient and remainder such that $cf = qg + r$ for a suitable constant $c$. The latter
  one implements standard polynomial long division where it is guaranteed that division of
  $fg$ by $g$ yields $f$.
  
  Moreover, there is an algorithm to compute GCDs of integer polynomials, where at the
  moment it is only proven that the returned result is a common divisor.\<close>

theory Polynomial_Division
imports 
  "../Polynomial_Interpolation/Missing_Polynomial"
  Complex
  Gauss_Lemma
begin
text \<open>A following type class is similar to @{class idom_divide}, but it has its own division operator.
  This is necessary for nesting, since the existing division on polynomials is only defined if the coefficients
  are taken from a field. In contrast, the upcoming algorithms allow nesting of polynomials, e.g., to perform
  division of polynomials over polynomials over polynomials over integer numbers.\<close>

class idom_div = idom + 
  fixes exact_div :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes exact_div_right[simp]: "b \<noteq> 0 \<Longrightarrow> exact_div (a * b) b = a"
  and exact_div_zero_right[simp]: "exact_div a 0 = 0"
begin
lemma exact_div_left[simp]: "b \<noteq> 0 \<Longrightarrow> exact_div (b * a) b = a" unfolding mult.commute[of b a]
  by (rule exact_div_right)

lemma exact_div_dvdD[dest]: assumes a: "a dvd b"
  shows "a * exact_div b a = b"
proof (cases "a = 0")
  case True
  thus ?thesis using a unfolding dvd_def by auto
next
  case False
  thus ?thesis using exact_div_right[OF False] a[unfolded dvd_def] by auto
qed

lemma exact_div_zero_left[simp]: "exact_div 0 a = 0"
  by (cases "a = 0", auto, insert divisors_zero dvd_0_right) blast
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

lemma p_div_main_0: "p_div_main 0 0 r d dr n = 0"
proof (induct n arbitrary: r d dr)
  case (Suc n r d dr)
  show ?case unfolding p_div_main.simps[of _ _ r] Let_def
    by (simp add: Suc del: p_div_main.simps)
qed simp

lemma p_div_0: "p_div f 0 = 0" unfolding p_div_def Let_def
  by (simp add: Let_def p_div_main_0 del: p_div_main.simps)
  
definition "pseudo_mod_main lc r d dr n = snd (pseudo_divmod_main lc 0 r d dr n)"

lemma snd_pseudo_divmod_main: "snd (pseudo_divmod_main lc q r d dr n) = snd (pseudo_divmod_main lc q' r d dr n)"
proof (induct n arbitrary: q q' lc r d dr)
  case (Suc n q q' lc r d dr)
  show ?case unfolding pseudo_divmod_main.simps[of _ _ _ _ _ "Suc n"] Let_def using Suc
    by simp
qed simp

lemma pseudo_mod_main_code[code]: "pseudo_mod_main lc r d dr n = (if n = 0 then r else let
     rr = smult lc r;
     a = coeff rr dr;
     qq = exact_div a lc;
     n1 = n - 1;
     b = monom qq n1;
     rrr = rr - b * d
     in pseudo_mod_main lc rrr d (dr - 1) n1)"
  unfolding pseudo_mod_main_def pseudo_divmod_main.simps[of _ _ _ _ _ n]
    using snd_pseudo_divmod_main[of lc] 
  by (auto simp: Let_def simp del: pseudo_divmod_main.simps)

definition pseudo_mod :: "'a :: idom_div poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "pseudo_mod f g = snd (pseudo_divmod f g)"
  
lemma pseudo_mod_code[code]: "pseudo_mod p q = (let dp = degree p; dq = degree q 
   in pseudo_mod_main (coeff q dq) p q dp (1 + dp - dq))"
   unfolding pseudo_mod_def pseudo_divmod_def pseudo_mod_main_def Let_def ..
   
lemma pseudo_mod: assumes g: "g \<noteq> 0"
  and *: "pseudo_mod f g = r" 
  shows "\<exists> a q. a \<noteq> 0 \<and> smult a f = g * q + r" "r = 0 \<or> degree r < degree g"
proof - 
  let ?cg = "coeff g (degree g)"
  let ?cge = "?cg ^ pseudo_exponent f g"
  def a \<equiv> ?cge
  obtain q where pdm: "pseudo_divmod f g = (q,r)" using *[unfolded pseudo_mod_def]
    by (cases "pseudo_divmod f g", auto)
  from pseudo_divmod[OF g pdm] have id: "smult a f = g * q + r" and "r = 0 \<or> degree r < degree g" 
    unfolding a_def by auto
  show "r = 0 \<or> degree r < degree g" by fact
  from g have "a \<noteq> 0" unfolding a_def by auto
  thus "\<exists> a q. a \<noteq> 0 \<and> smult a f = g * q + r" using id by auto
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
  by (standard, auto simp: exact_div_poly_def p_div p_div_0)
end

text \<open>Using pseudo-division, we can write a GCD-algorithm for polynomials over integers.\<close>

text \<open>Specialization to @{type int} at this point, since several results on contents are
  only available for @{type int}.\<close>
function primitive_prs :: "int poly \<Rightarrow> int poly \<Rightarrow> int poly" where
  "primitive_prs f g = (if g = 0 then f else let
    r = pseudo_mod f g;
    h = normalize_content r
  in primitive_prs g h)"
  by pat_completeness auto
  
termination 
proof (relation "measure (\<lambda> (f,g). if g = 0 then 0 else Suc (degree g))", force, clarify, goal_cases)
  case (1 f g)
  with pseudo_mod(2)[OF this refl, of f]
  show ?case by auto
qed  

declare primitive_prs.simps[simp del]

lemma normalize_content_1: "(normalize_content p :: int poly) \<noteq> 0 \<Longrightarrow> content (normalize_content p) = 1" 
  using content_normalize_content_1 by force
  
lemma primitive_prs: assumes "h = primitive_prs f g"
  "g \<noteq> 0 \<Longrightarrow> content g = 1"
  "f \<noteq> 0 \<Longrightarrow> content f = 1" 
  and ck: "k \<noteq> 0 \<Longrightarrow> content k = 1"
  shows "h dvd f \<and> h dvd g \<and> (h \<noteq> 0 \<longrightarrow> content h = 1) \<and> 
    (k dvd f \<longrightarrow> k dvd g \<longrightarrow> k dvd h)"
  using assms(1-3)
proof (induct f g arbitrary: h rule: primitive_prs.induct)
  case (1 f g h)
  def r \<equiv> "pseudo_mod f g"
  let ?h = "normalize_content r"
  from 1(2) have h: "h = (if g = 0 then f else primitive_prs g ?h)"
    unfolding primitive_prs.simps[of f] r_def Let_def by auto
  show ?case
  proof (cases "g = 0")
    case True
    thus ?thesis unfolding h using 1(2-) by auto
  next
    case False
    hence g: "g \<noteq> 0" and h: "h = primitive_prs g ?h" unfolding h by auto
    from pseudo_mod[OF g refl, of f, folded r_def] obtain a q where
      a: "a \<noteq> 0" and id: "smult a f = g * q + r" and r: "r = 0 \<or> degree r < degree g" by auto
    from 1(1)[OF False refl refl h[unfolded r_def], folded r_def, OF normalize_content_1 1(3)] g
    have hg: "h dvd g"  and hr: "h dvd ?h" and ch: "content h = 1"
      and k: "k dvd g \<Longrightarrow> k dvd ?h \<Longrightarrow> k dvd h" by auto
    from hr have hr: "h dvd r" by (metis dvd_smult smult_normalize_content)
    with hg have "h dvd smult a f" unfolding id by simp
    with ch a have hf: "h dvd f" 
      by (metis dvd_smult_int smult_1_left smult_normalize_content) 
    {
      assume kf: "k dvd f" and kg: "k dvd g"
      from kf have "k dvd g * q + r" unfolding id[symmetric] by (rule dvd_smult)
      with kg have "k dvd r" by algebra
      hence kh: "k dvd ?h" using ck
        by (metis content_0_iff dvd_smult_int normalize_content_0 smult_1_left smult_normalize_content)
      have "k dvd h"
        by (rule k[OF kg kh])
    }
    thus ?thesis using hf hg ch by auto
  qed
qed    
  
definition gcd_int_poly :: "int poly \<Rightarrow> int poly \<Rightarrow> int poly" where
  "gcd_int_poly f g = (
    let cf = content f;
        cg = content g;
        f' = div_poly cf f;
        g' = div_poly cg g
      in smult (gcd cf cg) (primitive_prs f' g'))"

lemma dvd_dvd_smult: "a dvd b \<Longrightarrow> f dvd g \<Longrightarrow> smult a f dvd smult b g"
  unfolding dvd_def by (metis mult_smult_left mult_smult_right smult_smult)
  
lemma gcd_int_poly: assumes "h = gcd_int_poly f g"
  shows "h dvd f" "h dvd g" "p dvd f \<Longrightarrow> p dvd g \<Longrightarrow> p dvd h"
proof -
  let ?f = "normalize_content f"
  let ?g = "normalize_content g"
  let ?p = "normalize_content p"
  let ?cf = "content f"
  let ?cg = "content g"
  let ?cp = "content p"
  def a \<equiv> "gcd ?cf ?cg"
  def k \<equiv> "primitive_prs ?f ?g"
  have h: "h = smult a k" unfolding assms k_def gcd_int_poly_def Let_def a_def 
    normalize_content_def by auto
  have a: "a dvd ?cf" "a dvd ?cg" unfolding a_def by auto
  note main = primitive_prs[OF refl, of ?g ?f, folded k_def, OF normalize_content_1 normalize_content_1]
  from main[of 0]
  have k: "k dvd ?f" "k dvd ?g" "k \<noteq> 0 \<Longrightarrow> content k = 1" by auto
  have f: "f = smult ?cf ?f" by (simp add: smult_normalize_content)
  from arg_cong[OF this, of "\<lambda> x. h dvd x"]
  have "(h dvd f) = (h dvd smult ?cf ?f)" .
  also have "\<dots> = (smult a k dvd smult ?cf ?f)" unfolding h ..
  also have "\<dots>" using a(1) k(1) by (rule dvd_dvd_smult)
  finally show "h dvd f" .
  have g: "g = smult ?cg ?g" by (simp add: smult_normalize_content)
  from arg_cong[OF this, of "\<lambda> x. h dvd x"]
  have "(h dvd g) = (h dvd smult ?cg ?g)" .
  also have "\<dots> = (smult a k dvd smult ?cg ?g)" unfolding h ..
  also have "\<dots>" using a(2) k(2) by (rule dvd_dvd_smult)
  finally show "h dvd g" .
  assume p: "p dvd f" "p dvd g"
  have id: "p = smult ?cp ?p" by (simp add: smult_normalize_content)
  from p id have dvd: "?p dvd f" "?p dvd g" by (metis smult_dvd_cancel)+
  hence "?p dvd ?f" "?p dvd ?g"
    by (metis f dvd_smult_int normalize_content_0 p(1) smult_eq_0_iff,
        metis g dvd_smult_int normalize_content_0 p(2) smult_eq_0_iff)
  with main[OF _ _ normalize_content_1[of p]] have dvd: "?p dvd k" by auto
  from p gauss_lemma[of p] have "?cp dvd ?cf" "?cp dvd ?cg" by (metis dvdI exact_div_dvdD)+
  hence "?cp dvd a" unfolding a_def by auto
  thus "p dvd h" using dvd id unfolding h using dvd_dvd_smult by force
qed

definition gcd_rat_poly :: "rat poly \<Rightarrow> rat poly \<Rightarrow> rat poly" where
  "gcd_rat_poly f g = (let
     f' = snd (rat_to_int_poly f);
     g' = snd (rat_to_int_poly g);
     h = map_poly rat_of_int (gcd_int_poly f' g')
   in smult (inverse (coeff h (degree h))) h)"

lemma gcd_rat_poly[simp]: "gcd_rat_poly = gcd"
proof (intro ext)
  fix f g
  let ?ri = "map_poly rat_of_int"
  obtain a' f' where faf': "rat_to_int_poly f = (a',f')" by force
  from rat_to_int_poly[OF this] obtain a where 
    f: "f = smult a (?ri f')" and a: "a \<noteq> 0" by auto
  obtain b' g' where gbg': "rat_to_int_poly g = (b',g')" by force
  from rat_to_int_poly[OF this] obtain b where 
    g: "g = smult b (?ri g')" and b: "b \<noteq> 0" by auto
  def h \<equiv> "gcd_int_poly f' g'"
  note gcd = gcd_int_poly[OF refl, of f' g', folded h_def]
  let ?h = "?ri h"
  def lc \<equiv> "inverse (coeff ?h (degree ?h))"
  let ?gcd = "smult lc ?h"
  have id: "gcd_rat_poly f g = ?gcd"
    unfolding lc_def h_def gcd_rat_poly_def Let_def faf' gbg' snd_conv by auto
  show "gcd_rat_poly f g = gcd f g" unfolding id
  proof (rule sym, rule poly_gcd_unique)
    have "?h dvd ?ri f'" using gcd(1) unfolding dvd_def by auto
    hence "?h dvd f" unfolding f by (rule dvd_smult)
    thus dvd_f: "?gcd dvd f"
      by (metis dvdE inverse_zero_imp_zero lc_def leading_coeff_neq_0 mult_eq_0_iff smult_dvd_iff)
    have "?h dvd ?ri g'" using gcd(2) unfolding dvd_def by auto
    hence "?h dvd g" unfolding g by (rule dvd_smult)
    thus dvd_g: "?gcd dvd g"
      by (metis dvdE inverse_zero_imp_zero lc_def leading_coeff_neq_0 mult_eq_0_iff smult_dvd_iff)
    show "coeff ?gcd (degree ?gcd) = (if f = 0 \<and> g = 0 then 0 else 1)" 
    proof (cases "f = 0 \<and> g = 0")
      case True
      hence idd: "f = 0" "g = 0" by auto
      show ?thesis unfolding id[symmetric] unfolding idd by code_simp
    next
      case False
      hence "lc \<noteq> 0" using dvd_f dvd_g by auto
      thus ?thesis using False unfolding lc_def by simp
    qed
    fix k
    assume dvd: "k dvd f" "k dvd g"
    obtain k' c where kck: "rat_to_normalized_int_poly k = (c,k')" by force
    from rat_to_normalized_int_poly[OF this] have k: "k = smult c (?ri k')" and c: "c \<noteq> 0" by auto
    from dvd(1) have kf: "k dvd ?ri f'" unfolding f using a by (rule dvd_smult_cancel)
    from dvd(2) have kg: "k dvd ?ri g'" unfolding g using b by (rule dvd_smult_cancel)
    from kf kg obtain kf kg where kf: "?ri f' = k * kf" and kg: "?ri g' = k * kg" unfolding dvd_def by auto    
    from rat_to_int_factor_explicit[OF kf kck] have kf: "k' dvd f'" unfolding dvd_def by blast
    from rat_to_int_factor_explicit[OF kg kck] have kg: "k' dvd g'" unfolding dvd_def by blast
    from gcd_int_poly(3)[OF refl kf kg, folded h_def] 
    have "k' dvd h" .
    hence "?ri k' dvd ?ri h" unfolding dvd_def by auto
    hence "k dvd ?ri h" unfolding k using c by (rule smult_dvd)
    thus "k dvd ?gcd" by (rule dvd_smult)
  qed
qed

lemma gcd_rat_poly_unfold[code_unfold]: "gcd = gcd_rat_poly" by simp
end
