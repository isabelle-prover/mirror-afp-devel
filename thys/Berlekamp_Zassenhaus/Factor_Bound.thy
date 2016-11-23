(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsection \<open>The Mignotte Bound\<close>
theory Factor_Bound
imports 
  Mahler_Measure
begin

lemma binomial_mono_left: "n \<le> N \<Longrightarrow> n choose k \<le> N choose k" 
proof (induct n arbitrary: k N)
  case (0 k N)
  thus ?case by (cases k, auto)
next
  case (Suc n k N) note IH = this
  show ?case
  proof (cases k)
    case 0
    thus ?thesis by auto
  next
    case (Suc kk)
    from IH obtain NN where N: "N = Suc NN" and le: "n \<le> NN" by (cases N, auto)     
    show ?thesis unfolding N Suc using IH(1)[OF le] 
      by (simp add: add_le_mono)
  qed
qed



definition coeff_int where "coeff_int p i = (if i<0 then 0 else coeff p (nat i))"
lemma coeff_int[simp]: "coeff_int p n = coeff p n"  unfolding coeff_int_def by auto

lemma coeff_int_oprs[simp]:
  "coeff_int (a - b) i = coeff_int a i - coeff_int b i"
  "coeff_int (pCons 0 b) i = coeff_int b (i - 1)"
  "coeff_int (smult v r) i = v * coeff_int r i"
  by(auto simp:Nitpick.case_nat_unfold coeff_int_def coeff_pCons nat_diff_distrib')

definition choose_int where "choose_int m n = (if n < 0 then 0 else m choose (nat n))"

lemma choose_int[simp]: "choose_int p n = p choose n" unfolding choose_int_def by auto

lemma choose_int_suc[simp]:
  "choose_int (Suc n) i = choose_int n (i-1) + choose_int n i"
proof(cases "nat i")
  case 0 thus ?thesis by (simp add:choose_int_def) next
  case (Suc v) hence "nat (i - 1) = v" "i\<noteq>0" by simp_all
    thus ?thesis unfolding choose_int_def Suc by simp
qed

lemma sum_le_1_prod: assumes d: "1 \<le> d" and c: "1 \<le> c"
  shows "c + d \<le> 1 + c * (d :: real)"
proof -
  from d c have "(c - 1) * (d - 1) \<ge> 0" by auto
  thus ?thesis by (auto simp: field_simps)
qed

lemma mignotte_helper_coeff_int: "cmod (coeff_int (\<Prod>a\<leftarrow>lst. [:- a, 1:]) i)
    \<le> choose_int (length lst - 1) i * (\<Prod>a\<leftarrow>lst. (max 1 (cmod a))) 
    + choose_int (length lst - 1) (i - 1)"
proof(induct lst arbitrary:i)
  case Nil thus ?case by (auto simp:coeff_int_def choose_int_def)
  case (Cons v xs i)
  show ?case
  proof (cases "xs = []")
    case True
    show ?thesis unfolding True 
    proof (auto simp: coeff_int_def choose_int_def, cases "nat i", auto, cases "nat (i - 1)", auto, goal_cases)
      case (1 n nn)
      then obtain k where n: "n = Suc k" by (cases n, auto)
      thus ?case by auto
    qed
  next
    case False
    hence id: "length (v # xs) - 1 = Suc (length xs - 1)" by auto
    have id': "choose_int (length xs) i = choose_int (Suc (length xs - 1)) i" for i
      using False by (cases xs, auto)
    let ?r = "(\<Prod>a\<leftarrow>xs. [:- a, 1:])"
    let ?mv = "(\<Prod>a\<leftarrow>xs. (max 1 (cmod a)))"
    let ?c1 = "real (choose_int (length xs - 1) (i - 1 - 1))" 
    let ?c2 = "real (choose_int (length (v # xs) - 1) i - choose_int (length xs - 1) i)" 
    let "?m xs n" = "choose_int (length xs - 1) n * (\<Prod>a\<leftarrow>xs. (max 1 (cmod a)))"
    have le1:"1 \<le> max 1 (cmod v)" by auto
    have le2:"cmod v \<le> max 1 (cmod v)" by auto
    have mv_ge_1:"1 \<le> ?mv" by (rule prod_list_ge1, auto)
    obtain a b c d where abcd : 
      "a = real (choose_int (length xs - 1) i)" 
      "b = real (choose_int (length xs - 1) (i - 1))" 
      "c = (\<Prod>a\<leftarrow>xs. max 1 (cmod a))" 
      "d = cmod v" by auto
    {
      have c1: "c \<ge> 1" unfolding abcd by (rule mv_ge_1)
      have b: "b = 0 \<or> b \<ge> 1" unfolding abcd by auto
      have a: "a = 0 \<or> a \<ge> 1" unfolding abcd by auto
      hence a0: "a \<ge> 0" by auto
      have acd: "a * (c * d) \<le> a * (c * max 1 d)" using a0 c1
        by (simp add: mult_left_mono)
      from b have "b * (c + d) \<le> b * (1  + (c * max 1 d))" 
      proof 
        assume "b \<ge> 1" 
        hence "?thesis = (c + d \<le> 1 + c * max 1 d)" by simp
        also have \<dots>
        proof (cases "d \<ge> 1")
          case False
          hence id: "max 1 d = 1" by simp
          show ?thesis using False unfolding id by simp
        next
          case True
          hence id: "max 1 d = d" by simp
          show ?thesis using True c1 unfolding id by (rule sum_le_1_prod)
        qed
        finally show ?thesis .
      qed auto
      with acd have "b * c + (b * d + a * (c * d)) \<le> b + (a * (c * max 1 d) + b * (c * max 1 d))" 
        by (auto simp: field_simps)
    } note abcd_main = this      
    have "cmod (coeff_int ([:- v, 1:] * ?r) i) \<le> cmod (coeff_int ?r (i - 1)) + cmod (coeff_int (smult v ?r) i)"
      using norm_triangle_ineq4 by auto
    also have "\<dots> \<le> ?m xs (i - 1) + (choose_int (length xs - 1) (i - 1 - 1)) + cmod (coeff_int (smult v ?r) i)" 
      using Cons[of "i-1"] by auto
    also have "choose_int (length xs - 1) (i - 1) = choose_int (length (v # xs) - 1) i - choose_int (length xs - 1) i" 
      unfolding id choose_int_suc by auto
    also have "?c2 * (\<Prod>a\<leftarrow>xs. max 1 (cmod a)) + ?c1 +
       cmod (coeff_int (smult v (\<Prod>a\<leftarrow>xs. [:- a, 1:])) i) \<le> 
       ?c2 * (\<Prod>a\<leftarrow>xs. max 1 (cmod a)) + ?c1 + cmod v * (
         real (choose_int (length xs - 1) i) * (\<Prod>a\<leftarrow>xs. max 1 (cmod a)) + 
         real (choose_int (length xs - 1) (i - 1)))"
      using mult_mono'[OF order_refl Cons, of "cmod v" i, simplified] by (auto simp: norm_mult)
    also have "\<dots> \<le> ?m (v # xs) i + (choose_int (length xs) (i - 1))" using abcd_main[unfolded abcd]
      by (simp add: field_simps id')
    finally show ?thesis by simp
  qed
qed

lemma mignotte_helper_coeff_int': "cmod (coeff_int (\<Prod>a\<leftarrow>lst. [:- a, 1:]) i)
    \<le> ((length lst - 1) choose i) * (\<Prod>a\<leftarrow>lst. (max 1 (cmod a))) 
    + ((length lst - 1) choose (nat (i - 1)))"
  by (rule order.trans[OF mignotte_helper_coeff_int], auto simp: choose_int_def)

lemma mignotte_helper_coeff:
  "cmod (coeff h i) \<le> (degree h - 1 choose i) * mahler_measure_poly h 
      + (degree h - 1 choose (i - 1)) * cmod (lead_coeff h)"
proof -
  let ?r = "complex_roots_complex h"
  have "cmod (coeff h i) = cmod (coeff (smult (lead_coeff h) (\<Prod>a\<leftarrow>?r. [:- a, 1:])) i)"
    unfolding complex_roots by auto
  also have "\<dots> = cmod (lead_coeff h) * cmod (coeff (\<Prod>a\<leftarrow>?r. [:- a, 1:]) i)" by(simp add:norm_mult)
  also have "\<dots> \<le> cmod (lead_coeff h) * ((degree h - 1 choose i) * mahler_measure_monic h + ((degree h - 1) choose nat (int i - 1)))"    
    unfolding mahler_measure_monic_def
    by (rule mult_left_mono, insert mignotte_helper_coeff_int'[of ?r i], auto)
  also have "\<dots> = (degree h - 1 choose i) * mahler_measure_poly h + cmod (lead_coeff h) * ((degree h - 1) choose nat (int i - 1))" 
    unfolding mahler_measure_poly_via_monic by (simp add: field_simps)
  also have "nat (int i - 1) = i - 1" by (cases i, auto)
  finally show ?thesis by (simp add: ac_simps)
qed

context begin

interpretation i1: inj_semiring_hom complex_of_int by(unfold_locales,auto)

lemma cmod_through_lead_coeff[simp]:
  "cmod (lead_coeff (of_int_poly h)) = abs (lead_coeff h)"
  by (auto simp: i1.map_poly_preservers(1)[symmetric])

lemma mignotte_coeff_helper:
  "abs (coeff h i) \<le> 
   (degree h - 1 choose i) * mahler_measure h +
   (degree h - 1 choose (i - 1)) * abs (lead_coeff h)"
  unfolding mahler_measure_def
  using mignotte_helper_coeff[of "of_int_poly h" i] 
  by auto
end

lemma mahler_measure_poly_ge_1:
  assumes "h\<noteq>0"
  shows "(1::real) \<le> mahler_measure h"
proof -
  from assms have "cmod (lead_coeff (map_poly complex_of_int h)) > 0" by simp
  hence "cmod (lead_coeff (map_poly complex_of_int h)) \<ge> 1"
    by(cases "abs (lead_coeff h)";auto)
  from mult_mono[OF this mahler_measure_monic_ge_1 norm_ge_zero]
  show ?thesis unfolding mahler_measure_def mahler_measure_poly_via_monic
    by auto
qed

lemma choose_approx: "n \<le> N \<Longrightarrow> n choose k \<le> N choose (N div 2)" 
  by (rule order.trans[OF binomial_mono_left binomial_maximum])

text \<open>For Mignotte's factor bound, we currently do not support queries for individual coefficients,
  as we do not have a combined factor bound algorithm.\<close>

definition mignotte_bound :: "int poly \<Rightarrow> nat \<Rightarrow> int" where
  "mignotte_bound f d = (let d' = d - 1; d2 = d' div 2; binom = (d' choose d2) in
     binom * (mahler_approximation 2 f + abs (lead_coeff f)))" 

lemma mignotte_bound: fixes mm :: "nat \<Rightarrow> int poly \<Rightarrow> int" 
    assumes "f \<noteq> 0" "g dvd f" "degree g \<le> n"
  shows "\<bar>coeff g k\<bar> \<le> mignotte_bound f n"  
proof-
  let ?approx = "mahler_approximation 2 f" 
  obtain h where gh:"g * h = f" using assms by (metis dvdE)
  have nz:"g\<noteq>0" "h\<noteq>0" using gh assms(1) by auto
  have g1:"(1::real) \<le> mahler_measure h" using mahler_measure_poly_ge_1 gh assms(1) by auto
  note g0 = mahler_measure_ge_0
  let ?n = "(n - 1) choose ((n - 1) div 2)" 
  have to_n: "(degree g - 1 choose k) \<le> real ?n" for k
    using choose_approx[of "degree g - 1" "n - 1" k] assms(3) by auto
  have "\<bar>coeff g k\<bar> \<le> (degree g - 1 choose k) * mahler_measure g
    + real (degree g - 1 choose (k - 1)) * \<bar>lead_coeff g\<bar>" using mignotte_coeff_helper[of g k] by simp
  also have "\<dots> \<le> ?n * (real_of_int ?approx) + real ?n * \<bar>lead_coeff f\<bar>"
  proof (rule add_mono[OF mult_mono[OF to_n] mult_mono[OF to_n]])
    have "mahler_measure g  \<le> mahler_measure g * mahler_measure h" using g1 g0[of g]
      using mahler_measure_poly_ge_1 nz(1) by force
    also have "\<dots> = mahler_measure f" 
      using measure_eq_prod[of "of_int_poly g" "of_int_poly h"]
      unfolding mahler_measure_def gh[symmetric] by auto
    also have "\<dots> \<le> ?approx" using mahler_approximation[of f]
      by (simp add: ceiling_le_iff)
    finally show "mahler_measure g \<le> ?approx"  .
    have *: "lead_coeff f = lead_coeff g * lead_coeff h" 
      unfolding arg_cong[OF gh, of lead_coeff, symmetric] by (rule lead_coeff_mult)
    have "\<bar>lead_coeff h\<bar> \<noteq> 0" using nz(2) by auto
    hence lh: "\<bar>lead_coeff h\<bar> \<ge> 1" by linarith
    have "\<bar>lead_coeff f\<bar> = \<bar>lead_coeff g\<bar> * \<bar>lead_coeff h\<bar>" unfolding * by (rule abs_mult)
    also have "\<dots> \<ge> \<bar>lead_coeff g\<bar> * 1" 
      by (rule mult_mono, insert lh, auto)
    finally have "\<bar>lead_coeff g\<bar> \<le> \<bar>lead_coeff f\<bar>" by simp
    thus "real_of_int \<bar>lead_coeff g\<bar> \<le> real_of_int \<bar>lead_coeff f\<bar>" by simp
  qed (auto simp: g0)
  finally have "\<bar>coeff g k\<bar> \<le> ?n * (real_of_int ?approx) + ?n * \<bar>lead_coeff f\<bar>" by simp
  also have "\<dots> = real_of_int (?n * ?approx + ?n * \<bar>lead_coeff f\<bar>)" by simp
  finally have "\<bar>coeff g k\<bar> \<le> ?n * ?approx + ?n * \<bar>lead_coeff f\<bar>" by linarith
  thus ?thesis unfolding mignotte_bound_def Let_def by (auto simp: field_simps)
qed


text \<open>As indicated before, at the moment the only available factor bound is Mignotte's one.
  As future work one might use a combined bound.\<close>

definition factor_bound :: "int poly \<Rightarrow> nat \<Rightarrow> int" where
  "factor_bound = mignotte_bound"

lemma factor_bound: assumes "f \<noteq> 0" "g dvd f" "degree g \<le> n"
  shows "\<bar>coeff g k\<bar> \<le> factor_bound f n"
  unfolding factor_bound_def by (rule mignotte_bound[OF assms])
end 
