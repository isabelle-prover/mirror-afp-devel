(*  
    Author:      Sebastiaan Joosten
                 René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Algebraic Numbers -- Preliminary Implementation\<close>

text \<open>This theory gathers some preliminary results to implement algebraic numbers,
  e.g., it defines an invariant to have unique representing polynomials and shows
  that polynomials for unary minus and inversion preserve this invariant.\<close>


theory Algebraic_Numbers_Pre_Impl
imports 
  "Abstract-Rewriting.SN_Order_Carrier"
  Deriving.Compare_Rat
  Deriving.Compare_Real
  Jordan_Normal_Form.Gauss_Jordan_IArray_Impl
  Algebraic_Numbers
  Sturm_Rat
  Factors_of_Int_Poly
  Min_Int_Poly
begin

text \<open>For algebraic numbers, it turned out that @{const gcd_int_poly} is not
  preferable to the default implementation of @{const gcd}, which just implements
  Collin's primitive remainder sequence.\<close>
declare gcd_int_poly_code[code_unfold del]

(*TODO: move *)
lemma ex1_imp_Collect_singleton: "(\<exists>!x. P x) \<and> P x \<longleftrightarrow> Collect P = {x}"
proof(intro iffI conjI, unfold conj_imp_eq_imp_imp)
  assume "Ex1 P" "P x" then show "Collect P = {x}" by blast
next
  assume Px: "Collect P = {x}"
  then have "P y \<longleftrightarrow> x = y" for y by auto
  then show "Ex1 P" by auto
  from Px show "P x" by auto
qed

lemma ex1_Collect_singleton[consumes 2]:
  assumes "\<exists>!x. P x" and "P x" and "Collect P = {x} \<Longrightarrow> thesis" shows thesis
  by (rule assms(3), subst ex1_imp_Collect_singleton[symmetric], insert assms(1,2), auto)

lemma ex1_iff_Collect_singleton: "P x \<Longrightarrow> (\<exists>!x. P x) \<longleftrightarrow> Collect P = {x}"
  by (subst ex1_imp_Collect_singleton[symmetric], auto)

context
  fixes f
  assumes bij: "bij f"
begin
lemma bij_imp_ex1_iff: "(\<exists>!x. P (f x)) \<longleftrightarrow> (\<exists>!y. P y)" (is "?l = ?r")
proof (intro iffI)
  assume l: ?l
  then obtain x where "P (f x)" by auto
  with l have *: "{x} = Collect (P o f)" by auto
  also have "f ` \<dots> = {y. P (f (Hilbert_Choice.inv f y))}" using bij_image_Collect_eq[OF bij] by auto
  also have "\<dots> = {y. P y}"
  proof-
    have "f (Hilbert_Choice.inv f y) = y" for y by (meson bij bij_inv_eq_iff)
    then show ?thesis by simp
  qed
  finally have "Collect P = {f x}" by auto
  then show ?r by (fold ex1_imp_Collect_singleton, auto)
next
  assume r: ?r
  then obtain y where "P y" by auto
  with r have "{y} = Collect P" by auto
  also have "Hilbert_Choice.inv f ` \<dots> = Collect (P \<circ> f)"
    using bij_image_Collect_eq[OF bij_imp_bij_inv[OF bij]] bij by (auto simp: inv_inv_eq)
  finally have "Collect (P o f) = {Hilbert_Choice.inv f y}" by (simp add: o_def)
  then show ?l by (fold ex1_imp_Collect_singleton, auto)
qed

lemma bij_ex1_imp_the_shift:
  assumes ex1: "\<exists>!y. P y" shows "(THE x. P (f x)) = Hilbert_Choice.inv f (THE y. P y)" (is "?l = ?r")
proof-
  from ex1 have "P (THE y. P y)" by (rule the1I2)
  moreover from ex1[folded bij_imp_ex1_iff] have "P (f (THE x. P (f x)))" by (rule the1I2)
  ultimately have "(THE y. P y) = f (THE x. P (f x))" using ex1 by auto
  also have "Hilbert_Choice.inv f \<dots> = (THE x. P (f x))" using bij by (simp add: bij_is_inj)
  finally show "?l = ?r" by auto
qed

lemma bij_imp_Collect_image: "{x. P (f x)} = Hilbert_Choice.inv f ` {y. P y}" (is "?l = ?g ` _")
proof-
  have "?l = ?g ` f ` ?l" by (simp add: image_comp inv_o_cancel[OF bij_is_inj[OF bij]])
  also have "f ` ?l = {f x | x. P (f x)}" by auto
  also have "\<dots> = {y. P y}" by (metis bij bij_iff)
  finally show ?thesis.
qed

lemma bij_imp_card_image: "card (f ` X) = card X"
  by (metis bij bij_iff card.infinite finite_imageD inj_onI inj_on_iff_eq_card)

end

definition poly_cond :: "int poly \<Rightarrow> bool" where
  "poly_cond p = (lead_coeff p > 0 \<and> irreducible p)"

lemma poly_condI[intro]:
  assumes "lead_coeff p > 0" and "irreducible p" shows "poly_cond p" using assms by (auto simp: poly_cond_def)

lemma poly_condD:
  assumes "poly_cond p"
  shows "irreducible p" and "lead_coeff p > 0" and "root_free p" and "square_free p" and "p \<noteq> 0"
  using assms unfolding poly_cond_def using irreducible_root_free irreducible_imp_square_free cf_pos_def by auto

lemma poly_condE[elim]:
  assumes "poly_cond p"
      and "irreducible p \<Longrightarrow> lead_coeff p > 0 \<Longrightarrow> root_free p \<Longrightarrow> square_free p \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> thesis"
  shows thesis
  using assms by (auto dest:poly_condD)

lemma poly_cond_abs_int_poly[simp]: "irreducible p \<Longrightarrow> poly_cond (abs_int_poly p)" 
  unfolding poly_cond_def by (cases "p = 0", auto)


definition poly_uminus_abs :: "int poly \<Rightarrow> int poly" where
  "poly_uminus_abs p = abs_int_poly (poly_uminus p)" 

lemma irreducible_poly_uminus[simp]: "irreducible p \<Longrightarrow> irreducible (poly_uminus (p :: int poly))"  
proof (cases "degree p = 0")
  case True
  from degree0_coeffs[OF this]
  obtain a where p: "p = [:a:]" by auto
  have "poly_uminus p = p" unfolding p by (cases "a = 0", auto)
  thus "irreducible p \<Longrightarrow> irreducible (poly_uminus p)" by auto
next
  case False
  from poly_uminus_irreducible[OF _ this]   
  show "irreducible p \<Longrightarrow> irreducible (poly_uminus p)" .
qed

lemma irreducible_poly_uminus_abs[simp]: "irreducible p \<Longrightarrow> irreducible (poly_uminus_abs p)"
  unfolding poly_uminus_abs_def using irreducible_poly_uminus[of p] by auto

lemma poly_cond_poly_uminus_abs[simp]: "poly_cond p \<Longrightarrow> poly_cond (poly_uminus_abs p)"
  by (auto simp: poly_cond_def, unfold poly_uminus_abs_def, subst pos_poly_abs_poly, auto)

lemma ipoly_poly_uminus_abs_zero[simp]: "ipoly (poly_uminus_abs p) (x :: 'a :: idom) = 0 \<longleftrightarrow> ipoly p (-x) = 0" 
  unfolding poly_uminus_abs_def by simp  

lemma degree_poly_uminus_abs[simp]: "degree (poly_uminus_abs p) = degree p" 
  unfolding poly_uminus_abs_def by auto

definition poly_inverse :: "int poly \<Rightarrow> int poly" where
  "poly_inverse p = abs_int_poly (reflect_poly p)" 

lemma irreducible_poly_inverse[simp]: "coeff p 0 \<noteq> 0 \<Longrightarrow> irreducible p \<Longrightarrow> irreducible (poly_inverse p)" 
  unfolding poly_inverse_def by (auto simp: irreducible_reflect_poly)

lemma degree_poly_inverse[simp]: "coeff p 0 \<noteq> 0 \<Longrightarrow> degree (poly_inverse p) = degree p" 
  unfolding poly_inverse_def by auto

lemma ipoly_poly_inverse[simp]: assumes "coeff p 0 \<noteq> 0" 
  shows "ipoly (poly_inverse p) (x :: 'a :: field_char_0) = 0 \<longleftrightarrow> ipoly p (inverse x) = 0" 
  unfolding poly_inverse_def ipoly_abs_int_poly_eq_zero_iff
proof (cases "x = 0")
  case False
  thus "(ipoly (reflect_poly p) x = 0) = (ipoly p (inverse x) = 0)" 
    by (subst ipoly_reflect_poly, auto)
next
  case True
  show "(ipoly (reflect_poly p) x = 0) = (ipoly p (inverse x) = 0)" unfolding True using assms by (auto simp: poly_0_coeff_0)
qed

lemma ipoly_roots_finite: "p \<noteq> 0 \<Longrightarrow> finite {x :: 'a :: {idom, ring_char_0}. ipoly p x = 0}"
  by (rule poly_roots_finite, simp)

lemma root_sign_change: assumes
    p0: "poly (p::real poly) x = 0" and
    pd_ne0: "poly (pderiv p) x \<noteq> 0"
  obtains d where
    "0 < d"
    "sgn (poly p (x - d)) \<noteq> sgn (poly p (x + d))"
    "sgn (poly p (x - d)) \<noteq> 0"
    "0 \<noteq> sgn (poly p (x + d))"
    "\<forall> d' > 0. d' \<le> d \<longrightarrow> sgn (poly p (x + d')) = sgn (poly p (x + d)) \<and> sgn (poly p (x - d')) = sgn (poly p (x - d))"
proof -
  assume a:"(\<And>d. 0 < d \<Longrightarrow>
          sgn (poly p (x - d)) \<noteq> sgn (poly p (x + d)) \<Longrightarrow>
          sgn (poly p (x - d)) \<noteq> 0 \<Longrightarrow>
          0 \<noteq> sgn (poly p (x + d)) \<Longrightarrow>
          \<forall>d'>0. d' \<le> d \<longrightarrow>
                 sgn (poly p (x + d')) = sgn (poly p (x + d)) \<and> sgn (poly p (x - d')) = sgn (poly p (x - d)) \<Longrightarrow>
          thesis)"
  from pd_ne0 consider "poly (pderiv p) x > 0" | "poly (pderiv p) x < 0" by linarith
  thus ?thesis proof(cases)
    case 1
    obtain d1 where d1:"\<And>h. 0<h \<Longrightarrow> h < d1 \<Longrightarrow> poly p (x - h) < 0" "d1 > 0"
      using DERIV_pos_inc_left[OF poly_DERIV 1] p0 by auto
    obtain d2 where d2:"\<And>h. 0<h \<Longrightarrow> h < d2 \<Longrightarrow> poly p (x + h) > 0" "d2 > 0"
      using DERIV_pos_inc_right[OF poly_DERIV 1] p0 by auto
    have g0:"0 < (min d1 d2) / 2" using d1 d2 by auto
    hence m1:"min d1 d2 / 2 < d1" and m2:"min d1 d2 / 2 < d2" by auto
    { fix d
      assume a1:"0 < d" and a2:"d < min d1 d2"
      have "sgn (poly p (x - d)) = -1" "sgn (poly p (x + d)) = 1"
        using d1(1)[OF a1] d2(1)[OF a1] a2 by auto
    } note d=this
    show ?thesis by(rule a[OF g0];insert d g0 m1 m2, simp)
  next
    case 2
    obtain d1 where d1:"\<And>h. 0<h \<Longrightarrow> h < d1 \<Longrightarrow> poly p (x - h) > 0" "d1 > 0"
      using DERIV_neg_dec_left[OF poly_DERIV 2] p0 by auto
    obtain d2 where d2:"\<And>h. 0<h \<Longrightarrow> h < d2 \<Longrightarrow> poly p (x + h) < 0" "d2 > 0"
      using DERIV_neg_dec_right[OF poly_DERIV 2] p0 by auto
    have g0:"0 < (min d1 d2) / 2" using d1 d2 by auto
    hence m1:"min d1 d2 / 2 < d1" and m2:"min d1 d2 / 2 < d2" by auto
    { fix d
      assume a1:"0 < d" and a2:"d < min d1 d2"
      have "sgn (poly p (x - d)) = 1" "sgn (poly p (x + d)) = -1"
        using d1(1)[OF a1] d2(1)[OF a1] a2 by auto
    } note d=this
    show ?thesis by(rule a[OF g0];insert d g0 m1 m2, simp)
  qed
qed


lemma gt_rat_sign_change_square_free:
  assumes ur: "\<exists>! x. root_cond plr x"
    and plr[simp]: "plr = (p,l,r)" 
    and sf: "square_free p" and in_interval: "l \<le> y" "y \<le> r"
    and py0: "ipoly p y \<noteq> 0" and pr0: "ipoly p r \<noteq> 0" 
  shows "(sgn (ipoly p y) = sgn (ipoly p r)) = (of_rat y > (THE x. root_cond plr x))" (is "?gt = _")
proof (rule ccontr)
  define ur where "ur = (THE x. root_cond plr x)" 
  assume "\<not> ?thesis" 
  hence "?gt \<noteq> (real_of_rat y > ur)" unfolding ur_def by auto
  note a = this[unfolded plr]
  from py0 have "p \<noteq> 0" unfolding irreducible_def by auto
  hence p0_real: "real_of_int_poly p \<noteq> (0::real poly)" by auto
  let ?p = "real_of_int_poly p"
  let ?r = real_of_rat
  from in_interval have in':"?r l \<le> ?r y" "?r y \<le> ?r r" unfolding of_rat_less_eq by auto
  from sf square_free_of_int_poly[of p] square_free_rsquarefree
  have rsf:"rsquarefree ?p" by auto
  from ur have "root_cond plr ur" by (metis ur_def theI')
  note urD = this[unfolded root_cond_def plr split] this[unfolded plr]
  have ur3:"poly ?p ur = 0" using urD by auto
  from urD have "ur \<le> of_rat r" by auto
  moreover
  from pr0 have "ipoly p (real_of_rat r) \<noteq> 0" by auto
  with ur3 have "real_of_rat r \<noteq> ur" by force
  ultimately have "ur < ?r r" by auto
  hence ur2: "0 < ?r r - ur" by linarith
  from rsquarefree_roots rsf ur3
  have pd_nonz:"poly (pderiv ?p) ur \<noteq> 0" by auto
  obtain d where d':"\<And>d'. d'>0 \<Longrightarrow> d' \<le> d \<Longrightarrow>
             sgn (poly ?p (ur + d')) = sgn (poly ?p (ur + d)) \<and>
             sgn (poly ?p (ur - d')) = sgn (poly ?p (ur - d))"
    "sgn (poly ?p (ur - d)) \<noteq> sgn (poly ?p (ur + d))"
    "sgn (poly ?p (ur + d)) \<noteq> 0"
    and d_ge_0:"d > 0"
    by (metis root_sign_change[OF ur3 pd_nonz])
  have sr:"sgn (poly ?p (ur + d)) = sgn (poly ?p (?r r))"
  proof (cases "?r r - ur \<le> d")
    case True show ?thesis using d'(1)[OF ur2 True] by auto
  next
    case False hence less:"ur + d < ?r r" by auto
    show ?thesis
    proof(rule no_roots_inbetween_imp_same_sign[OF less,rule_format],goal_cases)
      case (1 x)
      from ur 1 d_ge_0 have ran: "real_of_rat l \<le> x" "x \<le> real_of_rat r" using urD by auto
      from 1 d_ge_0 have "ur \<noteq> x" by auto
      with ur urD have "\<not> root_cond (p,l,r) x" by (auto simp: root_cond_def)
      with ran show ?case by (auto simp: root_cond_def)
    qed
  qed
  consider "?r l < ur - d" "?r l < ur" | "0 < ur - ?r l" "ur - ?r l \<le> d" | "ur = ?r l"
    using urD by argo
  hence sl:"sgn (poly ?p (ur - d)) = sgn (poly ?p (?r l)) \<or> 0 = sgn (poly ?p (?r l))"
  proof (cases)
    case 1
    have "sgn (poly ?p (?r l)) = sgn (poly ?p (ur - d))"
    proof(rule no_roots_inbetween_imp_same_sign[OF 1(1),rule_format],goal_cases)
      case (1 x)
      from ur 1 d_ge_0 urD have ran: "real_of_rat l \<le> x" "x \<le> real_of_rat r" by auto
      from 1 d_ge_0 have "ur \<noteq> x" by auto
      with ur urD have "\<not> root_cond (p,l,r) x" by (auto simp: root_cond_def)
      with ran show ?case by (auto simp: root_cond_def)
    qed
    thus ?thesis by auto
  next 
    case 2 show ?thesis using d'(1)[OF 2] by simp
  qed (insert ur3,simp)
  have diff_sign: "sgn (ipoly p l) \<noteq> sgn (ipoly p r)"
    using d'(2-) sr sl real_of_rat_sgn by auto
  have ur':"\<And>x. real_of_rat l \<le> x \<and> x \<le> real_of_rat y \<Longrightarrow> ipoly p x = 0 \<Longrightarrow> \<not> (?r y \<le> ur)"
  proof(standard+,goal_cases)
    case (1 x)
    {
      assume id: "ur = ?r y" 
      with urD ur py0 have False by auto
    } note neq = this
    have x: "root_cond (p, l, r) x" unfolding root_cond_def
      using 1 a ur urD by auto
    from ur urD x have ur_eqI: "ur = x" 
      by auto
    with 1 have "ur = of_rat y" by auto
    with urD(1) py0 show False by auto
  qed
  hence ur'':"\<forall>x. real_of_rat y \<le> x \<and> x \<le> real_of_rat r \<longrightarrow> poly (real_of_int_poly p) x \<noteq> 0 \<Longrightarrow> \<not> (?r y \<le> ur)"
    using urD by auto
  have "(sgn (ipoly p y) = sgn (ipoly p r)) = (?r y > ur)"
  proof(cases "sgn (ipoly p r) = sgn (ipoly p y)")
    case True
    have sgn:"sgn (poly ?p (real_of_rat l)) \<noteq> sgn (poly ?p (real_of_rat y))" using True diff_sign
      by (simp add: real_of_rat_sgn)
    have ly:"of_rat l < (of_rat y::real)" using in_interval True diff_sign less_eq_rat_def of_rat_less by auto
    with no_roots_inbetween_imp_same_sign[OF ly,of ?p] sgn ur' True
    show ?thesis by force
  next
    case False
    hence ne:"sgn (ipoly p (real_of_rat y)) \<noteq> sgn (ipoly p (real_of_rat r))" by (simp add: real_of_rat_sgn)
    have ry:"of_rat y < (of_rat r::real)" using in_interval False diff_sign less_eq_rat_def of_rat_less by auto
    obtain x where x:"real_of_rat y \<le> x" "x \<le> real_of_rat r" "ipoly p x = 0"
      using no_roots_inbetween_imp_same_sign[OF ry,of ?p] ne by auto
    hence lx:"real_of_rat l \<le> x" using in_interval
      using False a urD by auto
    with x have "root_cond (p,l,r) x" by (auto simp: root_cond_def)
    with urD ur
    have "ur = x" by auto
    then show ?thesis using False x by auto
  qed
  thus False using diff_sign(1) a py0 by(cases "ipoly p r = 0";auto simp:sgn_0_0)
qed

definition algebraic_real :: "real \<Rightarrow> bool" where 
  [simp]: "algebraic_real = algebraic" 

lemma algebraic_real_iff[code_unfold]: "algebraic = algebraic_real" by simp

end
