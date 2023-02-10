theory Abs_Qr

imports Mod_Plus_Minus
        Kyber_spec

begin
text \<open>Auxiliary lemmas\<close>

lemma finite_range_plus: 
  assumes "finite (range f)"
          "finite (range g)"
  shows "finite (range (\<lambda>x. f x + g x))"
proof -
  have subs: "range (\<lambda>x. (f x, g x)) \<subseteq> range f \<times> range g" by auto
  have cart: "finite (range f \<times> range g)" using assms by auto
  have finite: "finite (range (\<lambda>x. (f x, g x)))" 
    using rev_finite_subset[OF cart subs] .
  have "range (\<lambda>x. f x + g x) = (\<lambda>(a,b). a+b) ` range (\<lambda>x. (f x, g x))"
    using range_composition[of "(\<lambda>(a,b). a+b)" "(\<lambda>x. (f x, g x))"] 
    by auto
  then show ?thesis 
    using finite finite_image_set[where f = "(\<lambda>(a,b). a+b)"] 
    by auto
qed

lemma all_impl_Max: 
  assumes "\<forall>x. f x \<ge> (a::int)"
          "finite (range f)"
  shows "(MAX x. f x) \<ge> a"
by (simp add: Max_ge_iff assms(1) assms(2))

lemma Max_mono':
  assumes "\<forall>x. f x \<le> g x"
          "finite (range f)"
          "finite (range g)"
  shows "(MAX x. f x) \<le> (MAX x. g x)"
using assms 
by (metis (no_types, lifting) Max_ge_iff Max_in UNIV_not_empty 
  image_is_empty rangeE rangeI)  

lemma Max_mono_plus:
  assumes "finite (range (f::_\<Rightarrow>_::ordered_ab_semigroup_add))" 
          "finite (range g)"
  shows "(MAX x. f x + g x) \<le> (MAX x. f x) + (MAX x. g x)"
proof -
  obtain xmax where xmax_def: "f xmax + g xmax = (MAX x. f x + g x)" 
    using finite_range_plus[OF assms] Max_in by fastforce
  have "(MAX x. f x + g x) = f xmax + g xmax" using xmax_def by auto
  also have "\<dots> \<le> (MAX x. f x) + g xmax" 
    using Max_ge[OF assms(1), of "f xmax"] 
    by (auto simp add: add_right_mono[of "f xmax"]) 
  also have "\<dots> \<le> (MAX x. f x) + (MAX x. g x)" 
    using Max_ge[OF assms(2), of "g xmax"]
    by (auto simp add: add_left_mono[of "g xmax"])
  finally show ?thesis by auto
qed



text \<open>Lemmas for porting to \<open>qr\<close>.\<close>

lemma of_qr_mult:
  "of_qr (a * b) = of_qr a * of_qr b mod qr_poly"
by (metis of_qr_to_qr to_qr_mult to_qr_of_qr)

lemma of_qr_scale:
  "of_qr (to_module s * b) = 
  Polynomial.smult (of_int_mod_ring s) (of_qr b)"
unfolding to_module_def
  by (auto simp add: of_qr_mult[of "to_qr [:of_int_mod_ring s:]" "b"] 
  of_qr_to_qr) (simp add: mod_mult_left_eq mod_smult_left of_qr.rep_eq)

lemma to_module_mult:
  "poly.coeff (of_qr (to_module s * a)) x1 = 
   of_int_mod_ring (s) * poly.coeff (of_qr a) x1"
using of_qr_scale[of s a] by simp

text \<open>Lemmas on \<open>round\<close> and \<open>floor\<close>.\<close>
lemma odd_round_up:
assumes "odd x"
shows "round (real_of_int x / 2) = (x+1) div 2"
proof -
  have "round (real_of_int x / 2) = round (real_of_int (x+1) /2)"
    using assms unfolding round_def 
    by (metis (no_types, opaque_lifting) add.commute 
      add_divide_distrib even_add even_succ_div_2 
      floor_divide_of_int_eq odd_one of_int_add 
      of_int_hom.hom_one of_int_numeral)
  also have "\<dots> = (x+1) div 2"
    by (metis add_divide_distrib calculation 
    floor_divide_of_int_eq of_int_add of_int_hom.hom_one 
    of_int_numeral round_def)
  finally show ?thesis by blast
qed

lemma floor_unique:
assumes "real_of_int a \<le> x" "x < a+1"
shows "floor x = a"
  using assms(1) assms(2) by linarith

lemma same_floor:
assumes "real_of_int a \<le> x" "real_of_int a \<le> y" 
  "x < a+1" "y < a+1"
shows "floor x = floor y"
using assms floor_unique  by presburger

lemma one_mod_four_round:
assumes "x mod 4 = 1"
shows "round (real_of_int x / 4) = (x-1) div 4"
proof -
  have leq: "(x-1) div 4 \<le> real_of_int x / 4  + 1 / 2"
    using assms by linarith 
  have gr: "real_of_int x / 4  + 1 / 2 < (x-1) div 4 + 1" 
  proof -
    have "x+2 < 4 * ((x-1) div 4 + 1)" 
    proof -
      have *:  "(x-1) div 4 + 1 = (x+3) div 4" by auto
      have "4 dvd x + 3" using assms by presburger
      then have "4 * ((x+3) div 4) = x+3" 
        by (subst dvd_imp_mult_div_cancel_left, auto)
      then show ?thesis unfolding * by auto
    qed
    then show ?thesis by auto
  qed
  show "round (real_of_int x / 4) = (x-1) div 4"
    using floor_unique[OF leq gr] unfolding round_def by auto
qed

lemma odd_half_floor:
assumes "odd x"
shows "\<lfloor>real_of_int x / 2\<rfloor> = (x-1) div 2"
using assms by (metis add.commute diff_add_cancel even_add 
 even_succ_div_2 floor_divide_of_int_eq odd_one of_int_numeral)


section \<open>Re-centered "Norm" Function\<close>

context module_spec
begin 
text \<open>We want to show that \<open>abs_infty_q\<close> is a function induced by the 
  Euclidean norm on the \<open>mod_ring\<close> using a re-centered representative via \<open>mod+-\<close>.

  \<open>abs_infty_poly\<close> is the induced norm by \<open>abs_infty_q\<close> on polynomials over the polynomial 
  ring over the \<open>mod_ring\<close>. 

  Unfortunately this is not a norm per se, as the homogeneity only holds in 
  inequality, not equality. Still, it fulfils its purpose, since we only 
  need the triangular inequality.\<close>

definition abs_infty_q :: "('a mod_ring) \<Rightarrow> int" where
  "abs_infty_q p = abs ((to_int_mod_ring p) mod+- q)"

definition abs_infty_poly :: "'a qr \<Rightarrow> int" where
  "abs_infty_poly p = Max (range (abs_infty_q \<circ> poly.coeff (of_qr p)))"

text \<open>Helping lemmas and properties of \<open>Max\<close>, \<open>range\<close> and \<open>finite\<close>.\<close>

lemma to_int_mod_ring_range: 
  "range (to_int_mod_ring :: 'a mod_ring \<Rightarrow> int) = {0 ..< q}"
using CARD_a by (simp add: range_to_int_mod_ring)

lemma finite_Max:
  "finite (range (\<lambda>xa. abs_infty_q (poly.coeff (of_qr x) xa)))"
proof -
  have finite_range: "finite (range (\<lambda>xa. (poly.coeff (of_qr x) xa)))" 
  using MOST_coeff_eq_0[of "of_qr x"] by auto
  have "range (\<lambda>xa. \<bar>to_int_mod_ring (poly.coeff (of_qr x) xa) mod+- q\<bar>)
    = (\<lambda>z. \<bar>to_int_mod_ring z mod+- q\<bar>) ` range (poly.coeff (of_qr x))"
  using range_composition[of "(\<lambda>z. abs (to_int_mod_ring z mod+- q))" 
    "poly.coeff (of_qr x)"] by auto
  then show ?thesis 
    using finite_range finite_image_set[where 
      f = "(\<lambda>z. abs (to_int_mod_ring z) mod+- q)"] 
    by (auto simp add: abs_infty_q_def)
qed

lemma finite_Max_scale:
  "finite (range (\<lambda>xa. abs_infty_q (of_int_mod_ring s *
    poly.coeff (of_qr x) xa)))"
proof -
  have "of_int_mod_ring s * poly.coeff (of_qr x) xa = 
    poly.coeff (of_qr (to_module s * x)) xa" for xa
  by (metis coeff_smult of_qr_to_qr_smult to_qr_of_qr 
    to_qr_smult_to_module to_module_def)
  then show ?thesis
  using finite_Max by presburger
qed

lemma finite_Max_sum: 
  "finite (range (\<lambda>xa. abs_infty_q 
    (poly.coeff (of_qr x) xa + poly.coeff (of_qr y) xa)))"
proof -
  have finite_range: "finite (range (\<lambda>xa. (poly.coeff (of_qr x) xa + 
    poly.coeff (of_qr y) xa)))" 
  using MOST_coeff_eq_0[of "of_qr x"] by auto
  have "range (\<lambda>xa. \<bar>to_int_mod_ring (poly.coeff (of_qr x) xa + 
    poly.coeff (of_qr y) xa) mod+- q\<bar>) = 
    (\<lambda>z. \<bar>to_int_mod_ring z mod+- q\<bar>) ` 
    range (\<lambda>xa. poly.coeff (of_qr x) xa + poly.coeff (of_qr y) xa)"
  using range_composition[of "(\<lambda>z. abs (to_int_mod_ring z mod+- q))" 
    "(\<lambda>xa. poly.coeff (of_qr x) xa + poly.coeff (of_qr y) xa)"] 
  by auto
  then show ?thesis 
    using finite_range finite_image_set[where 
      f = "(\<lambda>z. abs (to_int_mod_ring z) mod+- q)" ] 
    by (auto simp add: abs_infty_q_def)
qed


lemma finite_Max_sum':
  "finite (range
     (\<lambda>xa. abs_infty_q (poly.coeff (of_qr x) xa) + 
      abs_infty_q (poly.coeff (of_qr y) xa)))"
proof -
  have finite_range_x: 
    "finite (range (\<lambda>xa. abs_infty_q (poly.coeff (of_qr x) xa)))" 
    using finite_Max[of x] by auto
  have finite_range_y: 
    "finite (range (\<lambda>xa. abs_infty_q (poly.coeff (of_qr y) xa)))" 
    using finite_Max[of y] by auto
  show ?thesis 
    using finite_range_plus[OF finite_range_x finite_range_y] by auto
qed




lemma Max_scale:
"(MAX xa. \<bar>s\<bar> * abs_infty_q (poly.coeff (of_qr x) xa)) =
    \<bar>s\<bar> * (MAX xa. abs_infty_q (poly.coeff (of_qr x) xa))"
proof -
  have "(MAX xa. \<bar>s\<bar> * abs_infty_q (poly.coeff (of_qr x) xa)) =
    (Max (range (\<lambda>xa. \<bar>s\<bar> * abs_infty_q (poly.coeff (of_qr x) xa))))"
    by auto
  moreover have "\<dots> = (Max ((\<lambda>a. \<bar>s\<bar> * a) `
    (range (\<lambda>xa. abs_infty_q (poly.coeff (of_qr x) xa)))))"
    by (metis range_composition)
  moreover have "\<dots> = \<bar>s\<bar> * (Max (range 
    (\<lambda>xa. abs_infty_q (poly.coeff (of_qr x) xa))))"
    by (subst mono_Max_commute[symmetric])
       (auto simp add: finite_Max Rings.mono_mult)
  moreover have "\<dots> =  \<bar>s\<bar> * 
    (MAX xa. abs_infty_q (poly.coeff (of_qr x) xa))"
    by auto
  ultimately show ?thesis by auto
qed



text \<open>Show that \<open>abs_infty_q\<close> is definite, positive and fulfils the triangle inequality.\<close>

lemma abs_infty_q_definite:
  "abs_infty_q x = 0 \<longleftrightarrow> x = 0"
proof (auto simp add: abs_infty_q_def 
  mod_plus_minus_zero'[OF q_gt_zero q_odd])
  assume "to_int_mod_ring x mod+- q = 0"
  then have "to_int_mod_ring x mod q = 0" 
    using mod_plus_minus_zero[of "to_int_mod_ring x" q] 
    by auto
  then have "to_int_mod_ring x = 0" 
    using to_int_mod_ring_range CARD_a
    by (metis mod_rangeE range_eqI)
  then show "x = 0" by force
qed

lemma abs_infty_q_pos:
  "abs_infty_q x \<ge> 0"
by (auto simp add: abs_infty_q_def) 


lemma abs_infty_q_minus:
  "abs_infty_q (- x) = abs_infty_q x"
proof (cases "x=0")
case True
  then show ?thesis by auto
next
case False
  have minus_x: "to_int_mod_ring (-x) = q - to_int_mod_ring x"
  proof -
    have "to_int_mod_ring (-x) = to_int_mod_ring (-x) mod q"
      by (metis CARD_a Rep_mod_ring_mod to_int_mod_ring.rep_eq)
    also have "\<dots> = (- to_int_mod_ring x) mod q" 
      by (metis (no_types, opaque_lifting) CARD_a diff_eq_eq 
        mod_add_right_eq plus_mod_ring.rep_eq to_int_mod_ring.rep_eq 
        uminus_add_conv_diff)
    also have "\<dots> = q - to_int_mod_ring x" 
    proof -
      have "- to_int_mod_ring x \<in> {-q<..<0}"
      using CARD_a range_to_int_mod_ring False 
        by (smt (verit, best) Rep_mod_ring_mod greaterThanLessThan_iff 
          q_gt_zero to_int_mod_ring.rep_eq to_int_mod_ring_hom.eq_iff 
          to_int_mod_ring_hom.hom_zero zmod_trivial_iff)
      then have "q-to_int_mod_ring x\<in>{0<..<q}" by auto
      then show ?thesis 
        using minus_mod_self1 mod_rangeE
        by (simp add: to_int_mod_ring.rep_eq zmod_zminus1_eq_if)
    qed
    finally show ?thesis by auto
  qed
  then have "\<bar>to_int_mod_ring (- x) mod+- q\<bar> = 
    \<bar>(q - (to_int_mod_ring x)) mod+- q\<bar>" 
    by auto
  also have "\<dots> = \<bar> (- to_int_mod_ring x) mod+- q\<bar>" 
    unfolding mod_plus_minus_def by (smt (z3) mod_add_self2)
  also have "\<dots> = \<bar> - (to_int_mod_ring x mod+- q)\<bar>" 
    using neg_mod_plus_minus[OF q_odd q_gt_zero, 
      of "to_int_mod_ring x"] by simp
  also have "\<dots> = \<bar>to_int_mod_ring x mod+- q\<bar>" by auto
  finally show ?thesis unfolding abs_infty_q_def by auto
qed



lemma to_int_mod_ring_mult:
  "to_int_mod_ring (a*b) =  to_int_mod_ring (a::'a mod_ring) * 
    to_int_mod_ring (b::'a mod_ring) mod q"
by (metis (no_types, lifting) CARD_a of_int_hom.hom_mult 
  of_int_mod_ring.rep_eq of_int_mod_ring_to_int_mod_ring 
  of_int_of_int_mod_ring to_int_mod_ring.rep_eq)



text \<open>Scaling only with inequality not equality! This causes a problem in proof of the 
  Kyber scheme. Needed to add $q\equiv 1 \mod 4$ to change proof.\<close>
lemma mod_plus_minus_leq_mod: 
  "\<bar>x mod+- q\<bar> \<le> \<bar>x\<bar>"
by (smt (verit, best) atLeastAtMost_iff mod_plus_minus_range_odd
  mod_plus_minus_rangeE q_gt_zero q_odd)

lemma abs_infty_q_scale_pos:
  assumes "s\<ge>0"
  shows "abs_infty_q ((of_int_mod_ring s :: 'a mod_ring) * x) \<le> 
    \<bar>s\<bar> * (abs_infty_q x)"
proof -
  have "\<bar>to_int_mod_ring (of_int_mod_ring s * x) mod+- q\<bar> = 
        \<bar>(to_int_mod_ring (of_int_mod_ring s ::'a mod_ring) * 
          to_int_mod_ring x mod q) mod+- q\<bar>"
    using to_int_mod_ring_mult[of "of_int_mod_ring s" x] by simp
  also have "\<dots> = \<bar>(s mod q * to_int_mod_ring x) mod+- q\<bar>"
  by (simp add: CARD_a mod_plus_minus_def of_int_mod_ring.rep_eq to_int_mod_ring.rep_eq)
  also have "\<dots> \<le> \<bar>s mod q\<bar> * \<bar>to_int_mod_ring x mod+- q\<bar>" 
  proof -
    have "\<bar>s mod q * to_int_mod_ring x mod+- q\<bar> = 
          \<bar>(s mod q mod+- q) * (to_int_mod_ring x mod+- q) mod+- q\<bar>"
      using mod_plus_minus_mult by auto
    also have "\<dots> \<le> \<bar>(s mod q mod+- q) * (to_int_mod_ring x mod+- q)\<bar>" 
      using mod_plus_minus_leq_mod by blast
    also have "\<dots> \<le> \<bar>s mod q mod+- q\<bar> * \<bar>(to_int_mod_ring x mod+- q)\<bar>" 
      by (simp add: abs_mult)
    also have "\<dots> \<le> \<bar>s mod q\<bar> * \<bar>(to_int_mod_ring x mod+- q)\<bar>"
      using mod_plus_minus_leq_mod[of "s mod q"] 
      by (simp add: mult_right_mono)
    finally show ?thesis by auto
  qed 
  also have "\<dots> \<le> \<bar>s\<bar> * \<bar>to_int_mod_ring x mod+- q\<bar>" using assms
    by (simp add: mult_mono' q_gt_zero zmod_le_nonneg_dividend)
  finally show ?thesis unfolding abs_infty_q_def by auto
qed

lemma abs_infty_q_scale_neg:
  assumes "s<0"
  shows "abs_infty_q ((of_int_mod_ring s :: 'a mod_ring) * x) \<le> 
    \<bar>s\<bar> * (abs_infty_q x)"
using abs_infty_q_minus abs_infty_q_scale_pos 
by (smt (verit, best) mult_minus_left of_int_minus of_int_of_int_mod_ring)

lemma abs_infty_q_scale:
  "abs_infty_q ((of_int_mod_ring s :: 'a mod_ring) * x) \<le> 
    \<bar>s\<bar> * (abs_infty_q x)"
apply (cases "s\<ge>0") 
using abs_infty_q_scale_pos apply presburger 
using abs_infty_q_scale_neg by force


text \<open>Triangle inequality for \<open>abs_infty_q\<close>.\<close>

lemma abs_infty_q_triangle_ineq:
  "abs_infty_q (x+y) \<le> abs_infty_q x + abs_infty_q y"
proof -
  have "to_int_mod_ring (x + y) mod+- q = 
        (to_int_mod_ring x + to_int_mod_ring y) mod q mod+-q"
    by (simp add: to_int_mod_ring_def CARD_a plus_mod_ring.rep_eq)
  also have "\<dots> = (to_int_mod_ring x + to_int_mod_ring y) mod+-q"
    unfolding mod_plus_minus_def by auto
  also have "\<dots> = (to_int_mod_ring x mod+- q + 
    to_int_mod_ring y mod+- q) mod+- q"
    unfolding mod_plus_minus_def 
    by (smt (verit, ccfv_threshold) minus_mod_self2 mod_add_eq)
  finally have rewrite:"to_int_mod_ring (x + y) mod+- q = 
    (to_int_mod_ring x mod+- q + to_int_mod_ring y mod+- q) mod+- q" .
  then have "\<bar>to_int_mod_ring (x + y) mod+- q\<bar>
    \<le> \<bar>to_int_mod_ring x mod+- q\<bar> + \<bar>to_int_mod_ring y mod+- q\<bar>"
    proof (cases 
    "(to_int_mod_ring x mod+- q + to_int_mod_ring y mod+- q) \<in> 
       {-\<lfloor>real_of_int q/2\<rfloor>..<\<lfloor>real_of_int q/2\<rfloor>}")
    case True
      then have True': "to_int_mod_ring x mod+- q + to_int_mod_ring y mod+- q
        \<in> {- \<lfloor>real_of_int q / 2\<rfloor>..\<lfloor>real_of_int q / 2\<rfloor>}" by auto
      then have "(to_int_mod_ring x mod+- q + 
        to_int_mod_ring y mod+- q) mod+- q
       = to_int_mod_ring x mod+- q + to_int_mod_ring y mod+- q" 
        using mod_plus_minus_rangeE[OF True' q_odd q_gt_zero] by auto 
      then show ?thesis by (simp add: rewrite)
    next
    case False
      then have "\<bar>(to_int_mod_ring x mod+- q + 
        to_int_mod_ring y mod+- q)\<bar> \<ge> \<lfloor>real_of_int q /2\<rfloor>" 
        by auto
      then have "\<bar>(to_int_mod_ring x mod+- q + 
        to_int_mod_ring y mod+- q)\<bar> \<ge> \<bar>(to_int_mod_ring x mod+- q +
        to_int_mod_ring y mod+- q) mod+- q\<bar>"
      using mod_plus_minus_range_odd[OF q_gt_zero q_odd, 
        of "(to_int_mod_ring x mod+- q + to_int_mod_ring y mod+- q)"]
      by auto
      then show ?thesis by (simp add: rewrite)
    qed
  then show ?thesis 
    by (auto simp add: abs_infty_q_def mod_plus_minus_def)
qed

text \<open>Show that \<open>abs_infty_poly\<close> is definite, positive and fulfils the triangle inequality.\<close>

lemma abs_infty_poly_definite:
  "abs_infty_poly x = 0 \<longleftrightarrow> x = 0"
proof (auto simp add: abs_infty_poly_def abs_infty_q_definite)
  assume "(MAX xa. abs_infty_q (poly.coeff (of_qr x) xa)) = 0"
  then have abs_le_zero: "abs_infty_q (poly.coeff (of_qr x) xa) \<le> 0"
    for xa
    using Max_ge[OF finite_Max[of x], 
      of "abs_infty_q (poly.coeff (of_qr x) xa)"]
    by (auto simp add: Max_ge[OF finite_Max])
  have "abs_infty_q (poly.coeff (of_qr x) xa) = 0" for xa 
    using abs_infty_q_pos[of "poly.coeff (of_qr x) xa"] 
    abs_le_zero[of xa] by auto
  then have "poly.coeff (of_qr x) xa = 0" for xa
    by (auto simp add: abs_infty_q_definite)
  then show "x = 0" 
    using leading_coeff_0_iff of_qr_eq_0_iff by blast
qed


lemma abs_infty_poly_pos:
  "abs_infty_poly x \<ge> 0"
proof (auto simp add: abs_infty_poly_def)
  have f_ge_zero: "\<forall>xa. abs_infty_q (poly.coeff (of_qr x) xa) \<ge> 0"
    by (auto simp add: abs_infty_q_pos)
  then show " 0 \<le> (MAX xa. abs_infty_q (poly.coeff (of_qr x) xa))"
    using all_impl_Max[OF f_ge_zero finite_Max] by auto
qed


text \<open>Again, homogeneity is only true for inequality not necessarily equality! 
  Need to add $q\equiv 1\mod 4$ such that proof of crypto scheme works out.\<close>
lemma abs_infty_poly_scale:
  "abs_infty_poly ((to_module s) * x) \<le> (abs s) * (abs_infty_poly x)"
proof -
  have fin1: "finite (range (\<lambda>xa. abs_infty_q (of_int_mod_ring s *
    poly.coeff (of_qr x) xa)))"
    using finite_Max_scale by auto
  have fin2: "finite (range (\<lambda>xa. \<bar>s\<bar> *
     abs_infty_q (poly.coeff (of_qr x) xa)))"
    by (metis finite_Max finite_imageI range_composition)
  have "abs_infty_poly (to_module s * x) = 
        (MAX xa. abs_infty_q
         ((of_int_mod_ring s) * poly.coeff (of_qr x) xa))"
  using abs_infty_poly_def to_module_mult
    by (metis (mono_tags, lifting) comp_apply image_cong)   
  also have "\<dots> \<le> (MAX xa. \<bar>s\<bar> * abs_infty_q (poly.coeff (of_qr x) xa))"
    using abs_infty_q_scale fin1 fin2 by (subst Max_mono', auto)
  also have "\<dots> = \<bar>s\<bar> * abs_infty_poly x"
    unfolding abs_infty_poly_def comp_def using Max_scale by auto
  finally show ?thesis by blast
qed


text \<open>Triangle inequality for \<open>abs_infty_poly\<close>.\<close>
lemma abs_infty_poly_triangle_ineq:
  "abs_infty_poly (x+y) \<le> abs_infty_poly x + abs_infty_poly y"
proof -
  have "abs_infty_q (poly.coeff (of_qr x) xa + 
    poly.coeff (of_qr y) xa) \<le> 
    abs_infty_q (poly.coeff (of_qr x) xa) + 
    abs_infty_q (poly.coeff (of_qr y) xa)"
    for xa
    using abs_infty_q_triangle_ineq[of 
      "poly.coeff (of_qr x) xa" "poly.coeff (of_qr y) xa"]
    by auto
  then have abs_q_triang: "\<forall>xa. 
    abs_infty_q (poly.coeff (of_qr x) xa + poly.coeff (of_qr y) xa) \<le>
    abs_infty_q (poly.coeff (of_qr x) xa) + 
    abs_infty_q (poly.coeff (of_qr y) xa)"
    by auto
  have "(MAX xa. abs_infty_q (poly.coeff (of_qr x) xa + 
      poly.coeff (of_qr y) xa))
    \<le> (MAX xa. abs_infty_q (poly.coeff (of_qr x) xa) + 
      abs_infty_q (poly.coeff (of_qr y) xa))"
    using Max_mono'[OF abs_q_triang finite_Max_sum finite_Max_sum'] 
    by auto
  also have "\<dots> \<le> (MAX xa. abs_infty_q (poly.coeff (of_qr x) xa)) +
       (MAX xb. abs_infty_q (poly.coeff (of_qr y) xb))" 
    using Max_mono_plus[OF finite_Max[of x] finite_Max[of y]] 
    by auto
  finally have "(MAX xa. abs_infty_q (poly.coeff (of_qr x) xa + 
      poly.coeff (of_qr y) xa))
    \<le> (MAX xa. abs_infty_q (poly.coeff (of_qr x) xa)) +
       (MAX xb. abs_infty_q (poly.coeff (of_qr y) xb))"
    by auto
  then show ?thesis 
    by (auto simp add: abs_infty_poly_def)
qed

end

text \<open>Estimation inequality using message bit.\<close>

lemma(in kyber_spec) abs_infty_poly_ineq_pm_1:
assumes "\<exists>x. poly.coeff (of_qr a) x \<in> {of_int_mod_ring (-1),1}"
shows "abs_infty_poly (to_module (round((real_of_int q)/2)) * a) \<ge> 
              2 * round (real_of_int q / 4)"
proof -
  let ?x = "to_module (round((real_of_int q)/2)) * a"
  obtain x1 where x1_def: 
    "poly.coeff (of_qr a) x1 \<in> {of_int_mod_ring(-1),1}" 
    using assms by auto
  have "abs_infty_poly (to_module (round((real_of_int q)/2)) * a)
    \<ge> abs_infty_q (poly.coeff (of_qr (to_module 
      (round (real_of_int q / 2)) * a)) x1)" 
    unfolding abs_infty_poly_def using x1_def 
    by (simp add: finite_Max)
  also have "abs_infty_q (poly.coeff (of_qr (to_module 
    (round (real_of_int q / 2)) * a)) x1)
  = abs_infty_q (of_int_mod_ring (round (real_of_int q / 2))
    * (poly.coeff (of_qr a) x1))" 
    using to_module_mult[of "round (real_of_int q / 2)" a] 
    by simp
  also have "\<dots> = abs_infty_q (of_int_mod_ring 
    (round (real_of_int q / 2)))" 
  proof -
    consider "poly.coeff (of_qr a) x1=1" | 
      "poly.coeff (of_qr a) x1 = of_int_mod_ring (-1)" 
      using x1_def by auto
    then show ?thesis 
    proof (cases)
      case 2
      then show ?thesis
      by (metis abs_infty_q_minus mult.right_neutral mult_minus_right
          of_int_hom.hom_one of_int_minus of_int_of_int_mod_ring)
    qed (auto)
  qed
  also have "\<dots> = \<bar>round (real_of_int q / 2) mod+- q\<bar>" 
    unfolding abs_infty_q_def 
    using to_int_mod_ring_of_int_mod_ring 
    by (simp add: CARD_a mod_add_left_eq mod_plus_minus_def 
      of_int_mod_ring.rep_eq to_int_mod_ring.rep_eq)
  also have "\<dots> = \<bar>((q + 1) div 2) mod+- q\<bar>" 
    using odd_round_up[OF q_odd] by auto 
  also have "\<dots> = \<bar>((2 * q) div 2) mod q - (q - 1) div 2\<bar>" 
  proof -
    have "(q + 1) div 2 mod q = (q + 1) div 2" using q_gt_two by auto
    moreover have "(q + 1) div 2 - q = - ((q - 1) div 2)" by (simp add: q_odd)
    ultimately show ?thesis
    unfolding mod_plus_minus_def odd_half_floor[OF q_odd] 
    by (split if_splits) simp
  qed
  also have "\<dots> = \<bar>(q-1) div 2\<bar>" using q_odd 
    by (subst nonzero_mult_div_cancel_left[of 2 q], simp) 
       (simp add: abs_div abs_minus_commute)
  also have "\<dots> = 2 * ((q-1) div 4)" 
  proof -
    from q_gt_two have "(q-1) div 2 > 0" by simp
    then have "\<bar>(q-1) div 2\<bar> = (q-1) div 2" by auto
    also have "\<dots> = 2 * ((q-1) div 4)" 
      by (subst div_mult_swap) (use q_mod_4 in 
      \<open>metis dvd_minus_mod\<close>, force)
    finally show ?thesis by blast
  qed
  also have "\<dots> = 2 * round (real_of_int q / 4)" 
    unfolding odd_round_up[OF q_odd] one_mod_four_round[OF q_mod_4] 
    by (simp add: round_def)
  finally show ?thesis unfolding abs_infty_poly_def by simp
qed

end