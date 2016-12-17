(*
    Author:      René Thiemann
    License:     BSD
*)

section \<open>GCD of integer polynomials.\<close>

text \<open>This theory contains an algorithm to compute GCDs of integer polynomials, where at the
  moment it is only proven that the returned result is a common divisor.\<close>

theory Polynomial_Division
imports 
  "../Polynomial_Interpolation/Missing_Polynomial"
  Complex
  Gauss_Lemma
begin

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
  with pseudo_mod(2)[OF this, of f]
  show ?case by auto
qed  

declare primitive_prs.simps[simp del]

lemma normalize_content_1: "(normalize_content p :: int poly) \<noteq> 0 \<Longrightarrow> content (normalize_content p) = 1" 
  using content_normalize_content_1[of p]
  by (cases "p = 0") auto
  
  
lemma primitive_prs: assumes "h = primitive_prs f g"
  "g \<noteq> 0 \<Longrightarrow> content g = 1"
  "f \<noteq> 0 \<Longrightarrow> content f = 1" 
  and ck: "k \<noteq> 0 \<Longrightarrow> content k = 1"
  shows "h dvd f \<and> h dvd g \<and> (h \<noteq> 0 \<longrightarrow> content h = 1) \<and> 
    (k dvd f \<longrightarrow> k dvd g \<longrightarrow> k dvd h)"
  using assms(1-3)
proof (induct f g arbitrary: h rule: primitive_prs.induct)
  case (1 f g h)
  define r where "r = pseudo_mod f g"
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
    from pseudo_mod[OF g, of f, folded r_def] obtain a q where
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
  define a where "a = gcd ?cf ?cg"
  define k where "k = primitive_prs ?f ?g"
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
  from p gauss_lemma[of p] have "?cp dvd ?cf" "?cp dvd ?cg" by (metis dvdE dvd_triv_left)+
  hence "?cp dvd a" unfolding a_def by auto
  thus "p dvd h" using dvd id unfolding h using dvd_dvd_smult by force
qed

definition gcd_rat_poly :: "rat poly \<Rightarrow> rat poly \<Rightarrow> rat poly" where
  "gcd_rat_poly f g = (let
     f' = snd (rat_to_int_poly f);
     g' = snd (rat_to_int_poly g);
     h = map_poly rat_of_int (gcd_int_poly f' g')
   in smult (inverse (coeff h (degree h))) h)"

lemma normalize_smult: 
  assumes "a \<noteq> (0::'a::{field,euclidean_ring_gcd})"
  shows   "normalize (smult a p) = normalize p"
proof -
  have "smult a p = [:a:] * p" by simp
  also from assms have "normalize \<dots> = normalize p"
    by (subst normalize_mult) (simp_all add: normalize_const_poly is_unit_normalize dvd_field_iff)
  finally show ?thesis .
qed

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
  define h where "h = gcd_int_poly f' g'"
  note gcd = gcd_int_poly[OF refl, of f' g', folded h_def]
  let ?h = "?ri h"
  define lc where "lc = inverse (coeff ?h (degree ?h))"
  let ?gcd = "smult lc ?h"
  have id: "gcd_rat_poly f g = ?gcd"
    unfolding lc_def h_def gcd_rat_poly_def Let_def faf' gbg' snd_conv by auto
  show "gcd_rat_poly f g = gcd f g" unfolding id
  proof (rule gcdI)
    have "?h dvd ?ri f'" using gcd(1) unfolding dvd_def by auto
    hence "?h dvd f" unfolding f by (rule dvd_smult)
    thus dvd_f: "?gcd dvd f"
      by (metis dvdE inverse_zero_imp_zero lc_def leading_coeff_neq_0 mult_eq_0_iff smult_dvd_iff)
    have "?h dvd ?ri g'" using gcd(2) unfolding dvd_def by auto
    hence "?h dvd g" unfolding g by (rule dvd_smult)
    thus dvd_g: "?gcd dvd g"
      by (metis dvdE inverse_zero_imp_zero lc_def leading_coeff_neq_0 mult_eq_0_iff smult_dvd_iff)
    show "normalize ?gcd = ?gcd"
      by (cases "lc = 0") (simp_all add: normalize_poly_eq_div lead_coeff_def 
                             one_poly_def [symmetric] field_simps lc_def)
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
