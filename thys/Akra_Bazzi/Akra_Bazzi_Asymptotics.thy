(* File:   Akra_Bazzi_Asymptotics.thy
   Author: Manuel Eberl <eberlm@in.tum.de>
   
   Proofs for the four(ish) asymptotic inequalities required for proving the 
   Akra Bazzi theorem with variation functions in the recursive calls.
*)

section {* Asymptotic bounds *}
theory Akra_Bazzi_Asymptotics
imports 
  Complex_Main
  "../Landau_Symbols/Landau_Symbols"
  Akra_Bazzi_Library
begin

(* Taylor-expand all the things! *)

lemma ev3:
  assumes c: "(c::real) > 0" and p: "p > 0"
  assumes "eventually (\<lambda>x. f x \<ge> (x - c) powr (-p) - (p*c/2) * (x - c) powr (-(p+1))) at_top"
  shows   "eventually (\<lambda>x. f x \<ge> x powr (-p)) at_top"
proof-
  from one_minus_x_lower_bound[of "p+1"] guess k . note k = this
  show ?thesis using assms(3) eventually_gt_at_top eventually_gt_at_top
  proof eventually_elim
    fix x assume x: "x > 2*c" "x > 2*k*c/p" 
    assume fx: "f x \<ge> (x - c) powr (-p) - (p*c/2) * (x - c) powr (-(p+1))"
    from x c have x': "x > 0" by simp 
    from x x' c have "c / x > 0" "c / x < 0.5" by (simp_all add: field_simps)
    from k(2)[OF this] have "(1 - c / x) powr (p+1) \<le> 1 - (p+1)*c / x + k*c^2 / x^2" 
      by (simp add: field_simps)
    hence "(1 - c / x) powr (p+1) + c*(p/2 + 1) / x \<le> 
             1 - (p+1)*c / x + k*c^2 / x^2 + c*(p/2 + 1) / x" by simp
    also from x' have "... = 1 - (c*p / (2*x) - k*c^2 / x^2)" by (simp add: field_simps)
    also from x x' c p have "... \<le> 1" by (simp add: field_simps power2_eq_square)
    finally have B: "(1 - c / x) powr (p + 1) + c * (p / 2 + 1) / x \<le> 1" .
    
    from x' have "x - c = x * (1 - c / x)" by (simp add: field_simps)
    also from x c have "... powr (p + 1) = x powr (p + 1) * (1 - c/x) powr (p + 1)"
      by (subst powr_mult[symmetric]) (simp_all add: field_simps)
    also from mult_left_mono[OF B, of "x powr p"] x' c p have
      "... + c * (p / 2 + 1) * x powr p \<le> x powr (p + 1)"
      by (simp add: field_simps powr_add)
    finally have C: "(x - c) powr (p + 1) + c * (p / 2 + 1) * x powr p \<le> x powr (p + 1)" .
    hence "(x - c) powr (p + 1) \<le> x powr (p + 1) - c * (p / 2 + 1) * x powr p" by simp
    also from x' have "... = x powr p * (x - c) - c*p/2 * x powr p"
      by (simp add: field_simps powr_add)
    finally have "x powr (-p) \<le> ((x - c) - (c*p/2)) * (x - c) powr (-(p+1))"
      using x x' by (subst (1 2) powr_minus) (simp add: field_simps powr_add)
    also from x c have "... = (x - c) powr (-p) - (p*c/2) * (x - c) powr (-(p+1))"
      by (subst (1 2 3) powr_minus) (simp add: field_simps powr_add)
    also note fx
    finally show "f x \<ge> x powr (-p)" .
  qed
qed


  
locale akra_bazzi_asymptotics_bep =
  fixes b e p hb :: real
  assumes bep: "b > 0" "b < 1" "e > 0" "hb > 0"
begin

context
begin

text {*
  Functions that are negligible w.r.t. @{term "ln (b*x) powr (e/2 + 1)"}.
*}
private abbreviation (input) negl :: "(real \<Rightarrow> real) \<Rightarrow> bool" where
  "negl f \<equiv> f \<in> o(\<lambda>x. ln (b*x) powr (-(e/2 + 1)))"

private lemma neglD: "negl f \<Longrightarrow> c > 0 \<Longrightarrow> eventually (\<lambda>x. \<bar>f x\<bar> \<le> c / ln (b*x) powr (e/2+1)) at_top"
  by (drule (1) landau_o.smallD, subst (asm) powr_minus) (simp add: field_simps)

private lemma negl_mult: "negl f \<Longrightarrow> negl g \<Longrightarrow> negl (\<lambda>x. f x * g x)"
  by (erule landau_o.small_1_mult, rule landau_o.small_imp_big, erule landau_o.small_trans)
     (insert bep, simp)

private lemma ev4:
  assumes e:  "e > 0"
  assumes f: "eventually (\<lambda>x. f (ln x) \<ge> ln (b*x) powr (-e/2) - g x) at_top"
  assumes g: "negl g"
  shows   "eventually (\<lambda>x. f (ln x) \<ge> ln x powr (-e/2)) at_top"
proof (subst eventually_ln_at_top, subst divide_minus_left, rule ev3)
  let ?k = "-ln b*e/4"
  from bep show "-ln b > 0" by simp
  from bep have k: "?k > 0" by (auto intro: mult_pos_neg simp: field_simps)
  from e show "e/2 > 0" by simp
  show "eventually (\<lambda>x. (x - - ln b) powr - (e / 2) - e / 2 * - ln b / 2 *
          (x - - ln b) powr - (e / 2 + 1) \<le> f x) at_top" 
    apply (subst eventually_ln_at_top[symmetric]) using f eventually_gt_at_top neglD[OF g k]
  proof eventually_elim
    fix x :: real assume x: "x > 0"
    assume f: "f (ln x) \<ge> ln (b * x) powr (-e/2) - g x"
    assume g: "\<bar>g x\<bar> \<le> ?k / (ln (b*x)) powr (e/2 + 1)"
    from x bep have "(ln x + ln b) = ln (b*x)" by (simp add: ln_mult)
    hence "(ln x - -ln b) powr - (e/2) - e/2 * - 
                  ln b/2 * (ln x - -ln b) powr - (e/2 + 1) =
             ln (b*x) powr - (e/2) - ?k / ln (b*x) powr (e/2 + 1)"
      by (subst (2) powr_minus) (simp add: field_simps)
    also from g have "-g x \<ge> -?k / (ln (b*x)) powr (e/2 + 1)" by simp
    hence "ln (b*x) powr - (e/2) - ?k / ln (b*x) powr (e/2 + 1) \<le>
               ln (b*x) powr - (e/2) - g x" by simp
    also from f have "... \<le> f (ln x)" by simp
    finally show "(ln x - - ln b) powr - (e / 2) - e / 2 * - ln b / 2 *
                        (ln x - - ln b) powr - (e / 2 + 1) \<le> f (ln x)" .
  qed
qed

private lemma ev41':
  assumes e: "e > 0" 
  assumes g: "negl g"
  assumes f: "eventually (\<lambda>x. f x \<ge> 1 + ln (b*x) powr (-e/2) - g x) at_top"
  shows   "eventually (\<lambda>x. f x \<ge> 1 + ln x powr (-e/2)) at_top"
proof-
  have "eventually (\<lambda>x::real. exp (ln x) = x) at_top"
    using eventually_gt_at_top[of 0] by eventually_elim simp
  have "eventually (\<lambda>x. f (exp (ln x)) - 1 \<ge> ln (b*x) powr (-e/2) - g x) at_top"
    using f eventually_gt_at_top[of 0] by eventually_elim simp
  with assms have "eventually (\<lambda>x. ln x powr (- e / 2) \<le> f (exp (ln x)) - 1) at_top"
    by (intro ev4)
  thus ?thesis using eventually_gt_at_top[of "0::real"] by eventually_elim simp
qed

private lemma ev42':
  assumes e: "e > 0" 
  assumes g: "negl g"
  assumes f: "eventually (\<lambda>x. f x \<le> 1 - ln (b*x) powr (-e/2) + g x) at_top"
  shows   "eventually (\<lambda>x. f x \<le> 1 - ln x powr (-e/2)) at_top"
proof-
  have "eventually (\<lambda>x. -f (exp (ln x)) + 1 \<ge> ln (b*x) powr (-e/2) - g x) at_top"
    using f eventually_gt_at_top[of "0::real"] by eventually_elim simp
  with assms have "eventually (\<lambda>x. ln x powr (-e/2) \<le> -f (exp (ln x)) + 1) at_top"
    by (intro ev4)
  thus ?thesis using eventually_gt_at_top[of "0::real"] by eventually_elim simp
qed


private lemma powr_add': "(x::real) powr ((y + z)/u) = x powr (y/u) * x powr (z/u)"
  by (subst add_divide_distrib) (simp add: powr_add)

private lemma powr_2: "(x::real) > 0 \<Longrightarrow> x powr 2 = x * x"
proof-
  assume x: "x > 0"
  have "2 = 1 + (1::real)" by simp
  also from x have "x powr ... = x * x" by (subst powr_add) simp
  finally show ?thesis .
qed
  
private lemma powr_three_halves: "(x::real) powr (y*3/2) = x powr y * x powr (y/2)"
proof-
  have "y* 3/2 = y + y/2" by simp
  also have "x powr ... = x powr y * x powr (y/2)" by (subst powr_add) simp
  finally show ?thesis .
qed
  
private lemma ev11:
  obtains g where 
    "negl g" and
    "eventually (\<lambda>x. (1 - (hb * inverse b * ln x powr (-(1+e)))) powr p \<ge> 1 - g x \<and>
                     1 - g x > 0) at_top"
proof-
  let ?y = "\<lambda>x. hb * inverse b * ln x powr (-(1 + e))"
  from bep have "(?y ---> 0) at_top"
    by (intro tendsto_mult_right_zero tendsto_neg_powr ln_at_top) simp
  from tendstoD[OF this, of "1/2"] have ev: "eventually (\<lambda>x. \<bar>?y x\<bar> < 0.5) at_top"
    by (simp add: dist_real_def)
  
  obtain k where k: "k \<ge> 0" 
      "\<And>x. ?y x > 0 \<Longrightarrow> ?y x < 0.5 \<Longrightarrow> (1 - ?y x) powr p \<ge> 1 - k * ?y x"
    by (rule one_minus_x_lower_bound'[of p]) blast
  def g \<equiv> "\<lambda>x. (k * hb * inverse b) * ln x powr (-(1+e))"
  from bep have "(g ---> 0) at_top" unfolding g_def
    by (intro tendsto_mult_right_zero tendsto_neg_powr ln_at_top) simp
  hence ev_g: "eventually (\<lambda>x. \<bar>g x\<bar> < 1) at_top"
    by (subst (asm) tendsto_iff) (auto simp: dist_real_def)
  have "eventually (\<lambda>x. (1 - (hb * inverse b * ln x powr (-(1+e)))) powr p \<ge> 1 - g x \<and>
          1 - g x > 0) at_top" using ev_g eventually_gt_at_top ev apply eventually_elim
  proof (intro conjI)
    fix x assume x: "x > 1" and A: "\<bar>?y x\<bar> < 0.5" and B: "\<bar>g x\<bar> < 1"
    from x bep have "?y x > 0" by (simp add: field_simps)
    moreover from this and A have "?y x < 0.5" by simp
    ultimately have "(1 - ?y x) powr p \<ge> 1 - k * ?y x" by (rule k)
    also have "1 - k * ?y x = 1 - g x" unfolding g_def by simp
    finally show "(1 - ?y x) powr p \<ge> 1 - g x" .
    from B show "1 - g x > 0" by simp
  qed
  moreover from bep have "negl g" unfolding g_def by simp
  ultimately show ?thesis by (intro that) simp_all
qed

private lemma ev11':
  obtains g where 
    "negl g" and
    "eventually (\<lambda>x. (1 + (hb * inverse b * ln x powr (-(1+e)))) powr p \<ge> 1 + g x \<and>
                     1 + g x > 0) at_top"
proof-
  let ?y = "\<lambda>x. hb * inverse b * ln x powr (-(1 + e))"
  from bep have "(?y ---> 0) at_top"
    by (intro tendsto_mult_right_zero tendsto_neg_powr ln_at_top) simp
  from tendstoD[OF this, of 1] have ev: "eventually (\<lambda>x. \<bar>?y x\<bar> < 1) at_top"
    by (simp add: dist_real_def)
  from bep have "eventually (\<lambda>x. ln x powr (-(1+e)) > 0) at_top"
    by (simp add: eventually_ln_not_equal)
  hence ev': "eventually (\<lambda>x. ?y x > 0) at_top" by eventually_elim (insert bep, simp)

  obtain k where k: "\<And>x. ?y x > 0 \<Longrightarrow> ?y x < 1 \<Longrightarrow> (1 + ?y x) powr p \<ge> 1 + k * ?y x"
    by (rule one_plus_x_lower_bound'[of p]) blast
  def g \<equiv> "\<lambda>x. (k * hb * inverse b) * ln x powr (-(1+e))"
  from bep have "(g ---> 0) at_top" unfolding g_def
    by (intro tendsto_mult_right_zero tendsto_neg_powr ln_at_top) simp
  hence ev_g: "eventually (\<lambda>x. \<bar>g x\<bar> < 1) at_top"
    by (subst (asm) tendsto_iff) (auto simp: dist_real_def)
  have "eventually (\<lambda>x. (1 + (hb * inverse b * ln x powr (-(1+e)))) powr p \<ge> 1 + g x \<and>
          1 + g x > 0) at_top" using ev_g eventually_gt_at_top ev ev' apply eventually_elim
  proof (intro conjI)
    fix x assume x: "x > 1" and A: "\<bar>?y x\<bar> < 1" and B: "?y x > 0" and C: "\<bar>g x\<bar> < 1"
    from A B have "(1 + ?y x) powr p \<ge> 1 + k * ?y x" by (intro k) simp_all
    also have "1 + k * ?y x = 1 + g x" unfolding g_def by simp
    finally show "(1 + ?y x) powr p \<ge> 1 + g x" .
    from C show "1 + g x > 0" by simp
  qed
  moreover from bep have "negl g" unfolding g_def by simp
  ultimately show ?thesis by (intro that) simp_all
qed


private lemma ev12:
  obtains g where 
    "negl g" and
    "eventually (\<lambda>x. (1 + (hb * inverse b * ln x powr (-(1+e)))) powr p \<le> 1 + g x \<and>
                     1 + g x > 0) at_top"
proof-
  let ?y = "\<lambda>x. hb * inverse b * ln x powr (-(1 + e))"
  from bep have "(?y ---> 0) at_top"
    by (intro tendsto_mult_right_zero tendsto_neg_powr ln_at_top) simp
  hence ev: "eventually (\<lambda>x. \<bar>?y x\<bar> < 1) at_top"
    by (subst (asm) tendsto_iff) (simp add: dist_real_def)
  
  obtain k where k: "k \<ge> 0" 
      "\<And>x. ?y x > 0 \<Longrightarrow> ?y x < 1 \<Longrightarrow> (1 + ?y x) powr p \<le> 1 + k * ?y x"
    by (rule one_plus_x_upper_bound[of p]) blast
  def g \<equiv> "\<lambda>x. (k * hb * inverse b) * ln x powr (-(1+e))"
  from bep have "(g ---> 0) at_top" unfolding g_def
    by (intro tendsto_mult_right_zero tendsto_neg_powr ln_at_top) simp
  hence ev_g: "eventually (\<lambda>x. \<bar>g x\<bar> < 1) at_top"
    by (subst (asm) tendsto_iff) (auto simp: dist_real_def)
    
  have "eventually (\<lambda>x. (1 + (hb * inverse b * ln x powr (-(1+e)))) powr p \<le> 1 + g x \<and>
          1 + g x > 0) at_top" using eventually_gt_at_top ev ev_g apply eventually_elim
  proof (intro conjI)
    fix x assume x: "x > 1" and A: "\<bar>?y x\<bar> < 1" and B: "\<bar>g x\<bar> < 1"
    from x bep have "?y x > 0" by (simp add: field_simps)
    moreover from this and A have "?y x < 1" by simp
    ultimately have "(1 + ?y x) powr p \<le> 1 + k * ?y x" by (rule k)
    also have "1 + k * ?y x = 1 + g x" unfolding g_def by simp
    finally show "(1 + ?y x) powr p \<le> 1 + g x" .
    from B show "1 + g x > 0" by simp
  qed
  moreover from bep have "negl g" unfolding g_def by simp
  ultimately show ?thesis by (intro that) simp_all
qed

private lemma ev12':
  obtains g where 
    "negl g" and
    "eventually (\<lambda>x. (1 - (hb * inverse b * ln x powr (-(1+e)))) powr p \<le> 1 + g x \<and>
                     1 + g x > 0) at_top"
proof-
  let ?y = "\<lambda>x. hb * inverse b * ln x powr (-(1 + e))"
  from bep have "(?y ---> 0) at_top"
    by (intro tendsto_mult_right_zero tendsto_neg_powr ln_at_top) simp
  from tendstoD[OF this, of "0.5"] have ev: "eventually (\<lambda>x. \<bar>?y x\<bar> < 0.5) at_top"
    by (simp add: dist_real_def)
  
  obtain k where k: "\<And>x. ?y x > 0 \<Longrightarrow> ?y x < 0.5 \<Longrightarrow> (1 - ?y x) powr p \<le> 1 + k * ?y x"
    by (rule one_minus_x_upper_bound'[of p]) blast
  def g \<equiv> "\<lambda>x. (k * hb * inverse b) * ln x powr (-(1+e))"
  from bep have "(g ---> 0) at_top" unfolding g_def
    by (intro tendsto_mult_right_zero tendsto_neg_powr ln_at_top) simp
  hence ev_g: "eventually (\<lambda>x. \<bar>g x\<bar> < 1) at_top"
    by (subst (asm) tendsto_iff) (auto simp: dist_real_def)
    
  have "eventually (\<lambda>x. (1 - (hb * inverse b * ln x powr (-(1+e)))) powr p \<le> 1 + g x \<and>
          1 + g x > 0) at_top" using eventually_gt_at_top ev ev_g apply eventually_elim
  proof (intro conjI)
    fix x assume x: "x > 1" and A: "\<bar>?y x\<bar> < 0.5" and B: "\<bar>g x\<bar> < 1"
    from x bep have "?y x > 0" by (simp add: field_simps)
    moreover from this and A have "?y x < 0.5" by simp
    ultimately have "(1 - ?y x) powr p \<le> 1 + k * ?y x" by (intro k)
    also have "1 + k * ?y x = 1 + g x" unfolding g_def by simp
    finally show "(1 - ?y x) powr p \<le> 1 + g x" .
    from B show "1 + g x > 0" by simp
  qed
  moreover from bep have "negl g" unfolding g_def by simp
  ultimately show ?thesis by (intro that) simp_all
qed

private lemma ev2: 
  obtains g where
    "negl g"
    "eventually (\<lambda>x. ln (b * x + hb * x / ln x powr (1 + e)) powr (-e/2) \<ge> 
         ln (b * x) powr (-e/2) - g x \<and> \<bar>ln (b * x) powr (-e/2) - g x\<bar> < 1) at_top"
proof-
  let ?h = "\<lambda>x. ln (b * x + hb * x / ln x powr (1 + e)) powr (- e / 2)"
  def f \<equiv> "\<lambda>x. ln (1 + hb * inverse b * ln x powr - (1 + e)) / ln (b * x)"
  def g \<equiv> "\<lambda>x. e/2 * f x * ln (b * x) powr (-e/2)"
  def g' \<equiv> "\<lambda>x. hb * e / (2 * b) * ln (b * x) powr - (2 + 3/2 * e)"

  have lim_g': "(g' ---> 0) at_top" unfolding g'_def using bep
    by (intro tendsto_mult_right_zero tendsto_neg_powr 
              filterlim_compose[OF ln_at_top] filterlim_ident
              filterlim_tendsto_pos_mult_at_top[OF tendsto_const]) simp
  hence ev_g': "eventually (\<lambda>x. \<bar>g' x\<bar> < 1) at_top"
    by (subst (asm) tendsto_iff) (simp add: dist_real_def bep)
    
  from bep lim_g' have "((\<lambda>x. ln (b*x) powr (-e/2) - g' x) ---> 0 - 0) at_top"
    by (intro tendsto_intros tendsto_neg_powr filterlim_ident filterlim_compose[OF 
              ln_at_top filterlim_tendsto_pos_mult_at_top[OF tendsto_const]]) simp_all
  hence ev_lg: "eventually (\<lambda>x. \<bar>ln (b*x) powr (-e/2) - g' x\<bar> < 1) at_top"
    by (subst (asm) tendsto_iff) (auto simp: dist_real_def)
    
  have limf: "(f ---> 0) at_top" unfolding f_def using bep
    apply (intro tendsto_divide_0[OF _ filterlim_at_top_imp_at_infinity])
    apply (rule tendsto_ln[OF tendsto_add[OF tendsto_const tendsto_mult_right_zero]])
    apply (rule tendsto_neg_powr[OF _ ln_at_top], simp, simp)
    apply (rule filterlim_compose[OF ln_at_top filterlim_tendsto_pos_mult_at_top])
    apply (rule tendsto_const, simp add: bep, rule filterlim_ident)
    done
  hence ev_f: "eventually (\<lambda>x. \<bar>f x\<bar> < 2 / e) at_top"
    by (subst (asm) tendsto_iff) (simp add: dist_real_def bep)
  from limf have ev_f': "eventually (\<lambda>x. \<bar>f x\<bar> < 1/2) at_top"
    by (subst (asm) tendsto_iff, elim allE[of _ "1/2"]) (simp add: dist_real_def)

  have "eventually (\<lambda>x. ?h x \<ge> ln (b * x) powr (-e/2) - g' x \<and> 
                         \<bar>ln (b * x) powr (-e/2) - g' x\<bar> < 1) at_top"
    using eventually_gt_at_top ev_f ev_f' ev_g' ev_lg
  proof (eventually_elim, intro conjI)
    fix x :: real assume x: "x > inverse b" and f: "\<bar>f x\<bar> < 2 / e" and f'': "\<bar>f x\<bar> < 1/2"
    assume g': "\<bar>g' x \<bar> < 1"
    from bep have "inverse b > 1" by (simp add: field_simps)
    with x have x': "x > 1" by simp
    from x' bep have A: "hb * inverse b * ln x powr - (1 + e) > 0"
      by (intro add_pos_pos mult_pos_pos) (simp_all add: field_simps)
    with bep x have f_pos: "f x > 0" unfolding f_def 
      by (intro divide_pos_pos mult_pos_pos ln_gt_zero) (simp_all add: field_simps)
    with f bep have f': "1 - e/2 * f x > 0" by (simp add: field_simps)
      
    from x bep have "b*x + hb * x / (ln x powr (1 + e)) = 
                     (b*x) * (1 + hb * inverse (b * ln x powr (1 + e)))"
      by (simp add: field_simps)
    also have "hb * inverse (b * ln x powr (1 + e)) = hb * inverse b * ln x powr (-(1 + e))"
      by (subst powr_minus) simp
    also have "ln (b*x*(1 + hb * inverse b * ln x powr - (1 + e))) =  
                   ln (b*x) + ln (1 + hb * inverse b * ln x powr - (1 + e))"
      using bep x A by (subst ln_mult) (simp_all add: field_simps)
    also have "... = ln (b * x) * (1 + f x)" 
      using bep x by (simp add: field_simps f_def)
    also have "... powr (-e/2) = (ln (b * x)) powr (-e/2) * (1 + f x) powr (-e/2)" unfolding f_def  
      using bep x by (intro powr_mult) (auto intro!: add_pos_pos ln_gt_zero simp: field_simps)
    finally have B: "ln (b * x + hb * x / ln x powr (1 + e)) powr (-e/2) =
                     ln (b * x) powr (-e/2) * (1 + f x) powr (-e/2)" .

    also from bep f'' x have "(1 + f x) powr (-e/2) \<ge> 1 + - e/2 * f x"
      by (intro one_plus_powr_ge divide_pos_pos) simp_all
    hence "... \<ge> 1 - e/2 * f x" by simp
    hence "ln (b * x) powr (-e/2) * ... \<ge> ln (b * x) powr (-e/2) * (1 - e/2 * f x)"
      by (intro mult_left_mono) (simp_all add: f')
    finally have A: "?h x \<ge> ln (b * x) powr (-e/2) - g x"
      by (simp add: algebra_simps g_def)
    
    from x bep have "ln (b * x) * ln (b * x) powr (e / 2) =
                         ln (b * x) powr ((e + 2) / 2)"
      by (subst add_divide_distrib, subst powr_add) (simp add: field_simps )
    with x bep have "g x = e/2 * ln (b * x) powr -(1+e/2) * ln (1 + hb*inverse b * ln x powr - (1 + e))"
      unfolding g_def f_def by (simp add: field_simps powr_add powr_minus)
    also from x bep have "... \<le> e/2 * ln (b * x) powr -(1+e/2) * (hb*inverse b * ln x powr - (1 + e))"
      by (intro mult_left_mono ln_add_one_self_le_self) simp_all
    also from bep x x' have "... \<le> e/2 * ln (b * x) powr -(1+e/2) * (hb*inverse b * ln (b*x) powr -(1+e))"
      by (intro mult_left_mono powr_mono2') (simp_all add: field_simps)
    also have "... = hb * (e/(2*b)) * (ln (b*x) powr -(1+e/2) * ln (b*x) powr -(1+e))" by (simp add: field_simps)
    also from bep x have "(ln (b*x) powr -(1+e/2) * ln (b*x) powr -(1+e)) = ln (b*x) powr -(2+1.5*e)"
      by (subst (1 2 3) powr_minus) (simp_all add: powr_add powr_add' powr_three_halves powr_2 field_simps)
    finally have "g x \<le> g' x" by (simp add: g'_def)
    with A show "?h x \<ge> ln (b*x) powr (-e/2) - g' x" by simp
  qed
  moreover from bep have "negl g'" unfolding g'_def by simp
  ultimately show ?thesis by (intro that) simp_all
qed

private lemma ev21:
  obtains g where
    "negl g"
    "eventually (\<lambda>x. 1 + ln (b * x + hb * x / ln x powr (1 + e)) powr (-e/2) \<ge> 
         1 + ln (b * x) powr (-e/2) - g x \<and> 1 + ln (b * x) powr (-e/2) - g x > 0) at_top"
proof-
  from ev2 guess g .
  note g = this
  from g(2) have "eventually (\<lambda>x. 1 + ln (b * x + hb * x / ln x powr (1 + e)) powr (-e/2) \<ge> 
         1 + ln (b * x) powr (-e/2) - g x \<and> 1 + ln (b * x) powr (-e/2) - g x > 0) at_top"
    by eventually_elim auto
  with g(1) show ?thesis by (rule that)
qed

private lemma ev22:
  obtains g where
    "negl g"
    "eventually (\<lambda>x. 1 - ln (b * x + hb * x / ln x powr (1 + e)) powr (-e/2) \<le> 
         1 - ln (b * x) powr (-e/2) + g x \<and> 1 - ln (b * x) powr (-e/2) + g x > 0) at_top"
proof-
  from ev2 guess g .
  note g = this
  from g(2) have A: "eventually (\<lambda>x. 1 - ln (b * x) powr (-e/2) + g x > 0) at_top"
  proof (eventually_elim, clarify)
    fix x assume A: "\<bar>ln (b*x) powr (-e/2) - g x\<bar> < 1"
    hence "-1 < -\<bar>ln (b*x) powr (-e/2) - g x\<bar>" by simp
    also have "... \<le> -(ln (b*x) powr (-e/2) - g x)" by simp
    finally show "1 - ln (b * x) powr (-e/2) + g x > 0" by simp
  qed
  show ?thesis apply (rule that[OF g(1)]) using A g(2) by eventually_elim simp
qed


lemma asymptotics1:
  shows "eventually (\<lambda>x. 
             (1 - hb * inverse b * ln x powr -(1+e)) powr p * 
             (1 + ln (b * x + hb * x / ln x powr (1 + e)) powr (- e / 2)) \<ge>
             1 + (ln x powr (-e/2))) at_top"
proof-
  let ?f = "\<lambda>x. (1 - hb * inverse b * ln x powr -(1+e)) powr p"
  let ?g = "\<lambda>x. 1 + ln (b * x + hb * x / ln x powr (1 + e)) powr (- e / 2)"
  from ev11 guess f . note f = this
  from ev21 guess g . note g = this
  def h \<equiv> "\<lambda>x. g x + f x + f x * ln (b*x) powr (-e/2) - f x * g x"
  
  have "eventually (\<lambda>x. ?f x * ?g x \<ge> 1 + ln (b*x) powr (-e/2) - h x) at_top"
    using f(2) g(2) apply eventually_elim
  proof clarify
    fix x 
    assume f: "?f x \<ge> 1 - f x"
    assume f_pos: "1 - f x > 0"
    assume g: "?g x \<ge> 1 + ln (b * x) powr (- e / 2) - g x"
    assume g_pos: "1 + ln (b * x) powr (- e / 2) - g x > 0"
    let ?t = "ln (b*x) powr (-e/2)"
    have "1 + ?t - h x = (1 - f x) * (1 + ln (b*x) powr (-e/2) - g x)"
      by (simp add: algebra_simps h_def)
    also from f g f_pos g_pos have "?f x * ?g x \<ge> 
          (1 - f x) * (1 + ln (b*x) powr (-e/2) - g x)" 
      by (intro mult_mono) simp_all
    finally show "?f x * ?g x \<ge> 1 + ln (b*x) powr (-e/2) - h x" .
  qed
  also from bep f(1) g(1) have "negl h" unfolding h_def
    by (fastforce intro!: sum_in_smallo landau_o.small.mult simp: powr_divide2[symmetric] 
                  intro: landau_o.small_trans)+
  ultimately show ?thesis using bep by (intro ev41') simp_all
qed

lemma asymptotics1':
  shows "eventually (\<lambda>x. 
             (1 + hb * inverse b * ln x powr -(1+e)) powr p * 
             (1 + ln (b * x + hb * x / ln x powr (1 + e)) powr (- e / 2)) \<ge>
             1 + (ln x powr (-e/2))) at_top"
proof-
  let ?f = "\<lambda>x. (1 + hb * inverse b * ln x powr -(1+e)) powr p"
  let ?g = "\<lambda>x. 1 + ln (b * x + hb * x / ln x powr (1 + e)) powr (- e / 2)"
  from ev11' guess f . note f = this
  from ev21 guess g . note g = this
  def h \<equiv> "\<lambda>x. g x - f x - f x * ln (b*x) powr (-e/2) + f x * g x"

  have "eventually (\<lambda>x. ?f x * ?g x \<ge> 1 + ln (b*x) powr (-e/2) - h x) at_top"
    using f(2) g(2) apply eventually_elim
  proof clarify
    fix x 
    assume f: "?f x \<ge> 1 + f x"
    assume f_pos: "1 + f x > 0"
    assume g: "?g x \<ge> 1 + ln (b * x) powr (- e / 2) - g x"
    assume g_pos: "1 + ln (b * x) powr (- e / 2) - g x > 0"
    let ?t = "ln (b*x) powr (-e/2)"
    have "1 + ?t - h x = (1 + f x) * (1 + ln (b*x) powr (-e/2) - g x)"
      by (simp add: algebra_simps h_def)
    also from f g f_pos g_pos have "?f x * ?g x \<ge> 
          (1 + f x) * (1 + ln (b*x) powr (-e/2) - g x)" 
      by (intro mult_mono) simp_all
    finally show "?f x * ?g x \<ge> 1 + ln (b*x) powr (-e/2) - h x" .
  qed
  also from bep f(1) g(1) have "negl h" unfolding h_def
    by (fastforce intro!: sum_in_smallo landau_o.small.mult simp: powr_divide2[symmetric] 
                  intro: landau_o.small_trans)+
  ultimately show ?thesis using bep by (intro ev41') simp_all
qed

lemma asymptotics2:
  shows "eventually (\<lambda>x. 
             (1 + hb * inverse b * ln x powr -(1+e)) powr p * 
             (1 - ln (b * x + hb * x / ln x powr (1 + e)) powr (- e / 2)) \<le>
             1 - (ln x powr (-e/2))) at_top"
proof-
  let ?f = "\<lambda>x. (1 + hb * inverse b * ln x powr -(1+e)) powr p"
  let ?g = "\<lambda>x. 1 - ln (b * x + hb * x / ln x powr (1 + e)) powr (- e / 2)"
  
  from bep have "LIM x at_top. b * x :> at_top"
    by (intro filterlim_tendsto_pos_mult_at_top[OF tendsto_const])
       (simp_all add: filterlim_ident)
  hence "LIM x at_top. b * x + hb * x / ln x powr (1 + e) :> at_top"
     apply (rule filterlim_at_top_mono) using eventually_gt_at_top[of 0] apply eventually_elim
     apply (insert bep, simp) done
  with bep have "(?g ---> 1 - 0) at_top"
    by (intro tendsto_intros tendsto_neg_powr filterlim_compose[OF ln_at_top]) simp_all
  hence ev_g: "eventually (\<lambda>x. \<bar>?g x - 1\<bar> < 1) at_top"
    by (subst (asm) tendsto_iff) (auto simp: dist_real_def)
  
  from ev12 guess f . note f = this
  from ev22 guess g . note g = this
  def h \<equiv> "\<lambda>x. g x + f x - f x * ln (b*x) powr (-e/2) + f x * g x"
  
  have "eventually (\<lambda>x. ?f x * ?g x \<le> 1 - ln (b*x) powr (-e/2) + h x) at_top"
    using f(2) g(2) ev_g apply eventually_elim
  proof clarify
    fix x 
    assume f: "?f x \<le> 1 + f x" and  f_pos: "1 + f x > 0" and 
           g: "?g x \<le> 1 - ln (b * x) powr (- e / 2) + g x"
    assume "\<bar>?g x - 1\<bar> < 1"
    hence g_pos: "?g x > 0" by simp
    let ?t = "ln (b*x) powr (-e/2)"
    from f g f_pos g_pos have "?f x * ?g x \<le>
          (1 + f x) * (1 - ln (b*x) powr (-e/2) + g x)"
      by (intro mult_mono) simp_all
    also have "... = 1 - ?t + h x" by (simp add: algebra_simps h_def)
    finally show "?f x * ?g x \<le> 1 - ln (b*x) powr (-e/2) + h x" .
  qed
  also from bep f(1) g(1) have "negl h" unfolding h_def
    by (fastforce intro!: sum_in_smallo landau_o.small.mult simp: powr_divide2[symmetric] 
                  intro: landau_o.small_trans)+
  ultimately show ?thesis using bep by (intro ev42') simp_all
qed

lemma asymptotics2':
  shows "eventually (\<lambda>x. 
             (1 - hb * inverse b * ln x powr -(1+e)) powr p * 
             (1 - ln (b * x + hb * x / ln x powr (1 + e)) powr (- e / 2)) \<le>
             1 - (ln x powr (-e/2))) at_top"
proof-
  let ?f = "\<lambda>x. (1 - hb * inverse b * ln x powr -(1+e)) powr p"
  let ?g = "\<lambda>x. 1 - ln (b * x + hb * x / ln x powr (1 + e)) powr (- e / 2)"
  
  from bep have "LIM x at_top. b * x :> at_top"
    by (intro filterlim_tendsto_pos_mult_at_top[OF tendsto_const])
       (simp_all add: filterlim_ident)
  hence "LIM x at_top. b * x + hb * x / ln x powr (1 + e) :> at_top"
     apply (rule filterlim_at_top_mono) using eventually_gt_at_top[of 0] apply eventually_elim
     apply (insert bep, simp) done
  with bep have "(?g ---> 1 - 0) at_top"
    by (intro tendsto_intros tendsto_neg_powr filterlim_compose[OF ln_at_top]) simp_all
  hence ev_g: "eventually (\<lambda>x. \<bar>?g x - 1\<bar> < 1) at_top"
    by (subst (asm) tendsto_iff) (auto simp: dist_real_def)
  
  from ev12' guess f . note f = this
  from ev22 guess g . note g = this
  def h \<equiv> "\<lambda>x. g x + f x - f x * ln (b*x) powr (-e/2) + f x * g x"
  
  have "eventually (\<lambda>x. ?f x * ?g x \<le> 1 - ln (b*x) powr (-e/2) + h x) at_top"
    using f(2) g(2) ev_g apply eventually_elim
  proof clarify
    fix x 
    assume f: "?f x \<le> 1 + f x" and  f_pos: "1 + f x > 0" and 
           g: "?g x \<le> 1 - ln (b * x) powr (- e / 2) + g x"
    assume "\<bar>?g x - 1\<bar> < 1"
    hence g_pos: "?g x > 0" by simp
    let ?t = "ln (b*x) powr (-e/2)"
    from f g f_pos g_pos have "?f x * ?g x \<le>
          (1 + f x) * (1 - ln (b*x) powr (-e/2) + g x)"
      by (intro mult_mono) simp_all
    also have "... = 1 - ?t + h x" by (simp add: algebra_simps h_def)
    finally show "?f x * ?g x \<le> 1 - ln (b*x) powr (-e/2) + h x" .
  qed
  also from bep f(1) g(1) have "negl h" unfolding h_def
    by (fastforce intro!: sum_in_smallo landau_o.small.mult simp: powr_divide2[symmetric] 
                  intro: landau_o.small_trans)+
  ultimately show ?thesis using bep by (intro ev42') simp_all
qed

lemma asymptotics3: "eventually (\<lambda>x. (1 + (ln x powr (-e/2))) / 2 \<le> 1) at_top"
  (is "eventually (\<lambda>x. ?f x \<le> 1) _")
proof (rule eventually_mp[OF always_eventually], clarify)
  from bep have "(?f ---> 1/2) at_top"
    by (force intro: tendsto_eq_intros tendsto_neg_powr ln_at_top)
  hence "\<And>e. e>0 \<Longrightarrow> eventually (\<lambda>x. \<bar>?f x - 0.5\<bar> < e) at_top"
    by (subst (asm) tendsto_iff) (simp add: dist_real_def)
  from this[of "0.5"] show "eventually (\<lambda>x. \<bar>?f x - 0.5\<bar> < 0.5) at_top" by simp
  fix x assume "\<bar>?f x - 0.5\<bar> < 0.5"
  hence "?f x - 0.5 \<le> 0.5" by (rule abs_le_D1[OF order.strict_implies_order])
  thus "?f x \<le> 1" by simp
qed

lemma asymptotics4: "eventually (\<lambda>x. (1 - (ln x powr (-e/2))) * 2 \<ge> 1) at_top"
  (is "eventually (\<lambda>x. ?f x \<ge> 1) _")
proof (rule eventually_mp[OF always_eventually], clarify)
  from bep have "(?f ---> 2) at_top"
    by (force intro: tendsto_eq_intros tendsto_neg_powr ln_at_top)
  hence "\<And>e. e>0 \<Longrightarrow> eventually (\<lambda>x. \<bar>?f x - 2\<bar> < e) at_top"
    by (subst (asm) tendsto_iff) (simp add: dist_real_def)
  from this[of 1] show "eventually (\<lambda>x. \<bar>?f x - 2\<bar> < 1) at_top" by simp
  fix x assume "\<bar>?f x - 2\<bar> < 1"
  hence "-(?f x - 2) \<le> 1"  by (rule abs_le_D2[OF order.strict_implies_order])
  thus "?f x \<ge> 1" by simp
qed
    
lemma asymptotics5: "eventually (\<lambda>x. ln (b*x - hb*x*ln x powr -(1+e)) powr (-e/2) < 1) at_top"
proof-
  from bep have "((\<lambda>x. b - hb * ln x powr -(1+e)) ---> b - 0) at_top"
    by (intro tendsto_intros tendsto_mult_right_zero tendsto_neg_powr ln_at_top) simp_all
  hence "LIM x at_top. (b - hb * ln x powr -(1+e)) * x :> at_top"
    by (rule filterlim_tendsto_pos_mult_at_top[OF _ _ filterlim_ident], insert bep) simp_all
  also have "(\<lambda>x. (b - hb * ln x powr -(1+e)) * x) = (\<lambda>x. b*x - hb*x*ln x powr -(1+e))"
    by (intro ext) (simp add: algebra_simps)
  finally have "filterlim ... at_top at_top" .
  with bep have "((\<lambda>x. ln (b*x - hb*x*ln x powr -(1+e)) powr -(e/2)) ---> 0) at_top"
    by (intro tendsto_neg_powr filterlim_compose[OF ln_at_top]) simp_all
  hence "eventually (\<lambda>x. \<bar>ln (b*x - hb*x*ln x powr -(1+e)) powr (-e/2)\<bar> < 1) at_top"
    by (subst (asm) tendsto_iff) (simp add: dist_real_def)
  thus ?thesis by simp
qed

lemma asymptotics6: "eventually (\<lambda>x. hb / ln x powr (1 + e) < b/2) at_top"
  and asymptotics7: "eventually (\<lambda>x. hb / ln x powr (1 + e) < (1 - b) / 2) at_top"
  and asymptotics8: "eventually (\<lambda>x. x*(1 - b - hb / ln x powr (1 + e)) > 1) at_top"
proof-
  from bep have A: "(\<lambda>x. hb / ln x powr (1 + e)) \<in> o(\<lambda>_. 1)" by simp
  from bep have B: "b/3 > 0" and C: "(1 - b)/3 > 0" by simp_all
  from landau_o.smallD[OF A B] show "eventually (\<lambda>x. hb / ln x powr (1+e) < b/2) at_top" 
    by eventually_elim (insert bep, simp)
  from landau_o.smallD[OF A C] show "eventually (\<lambda>x. hb / ln x powr (1 + e) < (1 - b)/2) at_top"
    by eventually_elim (insert bep, simp)

  from bep have "(\<lambda>x. hb / ln x powr (1 + e)) \<in> o(\<lambda>_. 1)" "(1 - b) / 2 > 0" by simp_all
  from landau_o.smallD[OF this] eventually_gt_at_top[of "1::real"]
    have A: "eventually (\<lambda>x. 1 - b - hb / ln x powr (1 + e) > 0) at_top"
    by eventually_elim (insert bep, simp add: field_simps)
  from bep have "(\<lambda>x. x * (1 - b - hb / ln x powr (1+e))) \<in> \<omega>(\<lambda>_. 1)" "(0::real) < 2" by simp_all
  from landau_omega.smallD[OF this] A eventually_gt_at_top[of "0::real"]
    show "eventually (\<lambda>x. x*(1 - b - hb / ln x powr (1 + e)) > 1) at_top"
    by eventually_elim (simp_all add: abs_mult)
qed

end
end


definition "akra_bazzi_asymptotic1 b hb e p x \<longleftrightarrow>
  (1 - hb * inverse b * ln x powr -(1+e)) powr p * (1 + ln (b*x + hb*x/ln x powr (1+e)) powr (-e/2))
  \<ge> 1 + (ln x powr (-e/2) :: real)"
definition "akra_bazzi_asymptotic1' b hb e p x \<longleftrightarrow>
  (1 + hb * inverse b * ln x powr -(1+e)) powr p * (1 + ln (b*x + hb*x/ln x powr (1+e)) powr (-e/2))
  \<ge> 1 + (ln x powr (-e/2) :: real)"
definition "akra_bazzi_asymptotic2 b hb e p x \<longleftrightarrow>
  (1 + hb * inverse b * ln x powr -(1+e)) powr p * (1 - ln (b*x + hb*x/ln x powr (1+e)) powr (-e/2))
      \<le> 1 - ln x powr (-e/2 :: real)"
definition "akra_bazzi_asymptotic2' b hb e p x \<longleftrightarrow>
  (1 - hb * inverse b * ln x powr -(1+e)) powr p * (1 - ln (b*x + hb*x/ln x powr (1+e)) powr (-e/2))
      \<le> 1 - ln x powr (-e/2 :: real)"
definition "akra_bazzi_asymptotic3 e x \<longleftrightarrow> (1 + (ln x powr (-e/2))) / 2 \<le> (1::real)"
definition "akra_bazzi_asymptotic4 e x \<longleftrightarrow> (1 - (ln x powr (-e/2))) * 2 \<ge> (1::real)"
definition "akra_bazzi_asymptotic5 b hb e x \<longleftrightarrow> 
  ln (b*x - hb*x*ln x powr -(1+e)) powr (-e/2::real) < 1"

definition "akra_bazzi_asymptotic6 b hb e x \<longleftrightarrow> hb / ln x powr (1 + e :: real) < b/2"
definition "akra_bazzi_asymptotic7 b hb e x \<longleftrightarrow> hb / ln x powr (1 + e :: real) < (1 - b) / 2"
definition "akra_bazzi_asymptotic8 b hb e x \<longleftrightarrow> x*(1 - b - hb / ln x powr (1 + e :: real)) > 1"

definition "akra_bazzi_asymptotics b hb e p x \<longleftrightarrow>
  akra_bazzi_asymptotic1 b hb e p x \<and> akra_bazzi_asymptotic1' b hb e p x \<and>
  akra_bazzi_asymptotic2 b hb e p x \<and> akra_bazzi_asymptotic2' b hb e p x \<and>
  akra_bazzi_asymptotic3 e x \<and> akra_bazzi_asymptotic4 e x \<and> akra_bazzi_asymptotic5 b hb e x \<and>
  akra_bazzi_asymptotic6 b hb e x \<and> akra_bazzi_asymptotic7 b hb e x \<and> 
  akra_bazzi_asymptotic8 b hb e x"

lemmas akra_bazzi_asymptotic_defs = 
  akra_bazzi_asymptotic1_def akra_bazzi_asymptotic1'_def 
  akra_bazzi_asymptotic2_def akra_bazzi_asymptotic2'_def akra_bazzi_asymptotic3_def
  akra_bazzi_asymptotic4_def akra_bazzi_asymptotic5_def akra_bazzi_asymptotic6_def
  akra_bazzi_asymptotic7_def akra_bazzi_asymptotic8_def akra_bazzi_asymptotics_def

lemma akra_bazzi_asymptotics:
  assumes "\<And>b. b \<in> set bs \<Longrightarrow> b \<in> {0<..<1}"
  assumes "hb > 0" "e > 0"
  shows "eventually (\<lambda>x. \<forall>b\<in>set bs. akra_bazzi_asymptotics b hb e p x) at_top"
proof (intro eventually_ball_finite ballI)
  fix b assume "b \<in> set bs"
  with assms interpret akra_bazzi_asymptotics_bep b e p hb by unfold_locales auto 
  show "eventually (\<lambda>x. akra_bazzi_asymptotics b hb e p x) at_top"
  unfolding akra_bazzi_asymptotic_defs
    by (intro eventually_conj asymptotics1 asymptotics1' asymptotics2 asymptotics2' asymptotics3 
              asymptotics4 asymptotics5 asymptotics6 asymptotics7 asymptotics8)
qed simp

hide_fact ev3

end