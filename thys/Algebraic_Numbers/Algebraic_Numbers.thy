(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Algebraic Numbers: Addition and Multiplication\<close>

text \<open>This theory contains the remaining field operations for algebraic numbers, namely
  addition and multiplication. In contrast to the previous development which have been
  generic, here we have specific results for complex and real algebraic numbers. The main
  reason is that we only proved that the resultant will be non-zero for complex and real
  numbers.\<close>

theory Algebraic_Numbers
imports 
  Algebraic_Numbers_Prelim
  Resultant
  "../Polynomial_Interpolation/Ring_Hom_Poly"
  "../Polynomial_Factorization/Polynomial_Divisibility"
begin

subsection \<open>Addition of Algebraic Numbers\<close>

abbreviation "x_y == [: [: 0, 1 :], -1 :]"

lemma poly2_x_y[simp]: fixes x :: "'a :: comm_ring_1" shows "poly2 x_y x y = x - y"
  unfolding poly2_def by simp

definition "poly_x_minus_y p = poly_lift p \<circ>\<^sub>p x_y"

lemma degree_poly_x_minus_y[simp]:
  fixes p :: "'a::idom poly"
  shows "degree (poly_x_minus_y p) = degree p"
  unfolding poly_x_minus_y_def by auto

lemma poly_x_minus_y_0[simp]: "poly_x_minus_y 0 = 0"
  unfolding poly_x_minus_y_def by simp

lemma poly_x_minus_y_pCons[simp]:
  "poly_x_minus_y (pCons a p) = [:[: a :]:] + poly_x_minus_y p * x_y"
  unfolding poly_x_minus_y_def
  unfolding poly_lift2_pCons by simp

lemma poly_poly_x_minus_y:
  fixes p :: "'a :: comm_ring_1 poly"
  shows "poly (poly_x_minus_y p) q = p \<circ>\<^sub>p ([:0,1:] - q)"
  by (induct p; simp add: ring_distribs)

lemma poly_poly_poly_x_minus_y[simp]:
  fixes p :: "'a :: comm_ring_1 poly"
  shows "poly (poly (poly_x_minus_y p) q) x = poly p (x - poly q x)"
  by (induct p; simp add: ring_distribs)

lemma poly2_poly_x_minus_y[simp]:
  fixes p :: "'a :: comm_ring_1 poly"
  shows "poly2 (poly_x_minus_y p) x y = poly p (x-y)"
  unfolding poly2_def by simp

lemma poly_x_minus_y_nonzero[simp]:
  fixes p :: "'a::{ring_char_0,idom} poly"
  shows "poly_x_minus_y p = 0 \<longleftrightarrow> p = 0"
proof
  assume 0: "poly_x_minus_y p = 0"
  { fix x
    have "poly2 (poly_x_minus_y p) x 0 = 0" using 0 by simp
    also have "poly2 (poly_x_minus_y p) x 0 = poly p x" by simp
    finally have "poly p x = 0" by auto
  }
  thus "p = 0" using poly_all_0_iff_0 by auto
qed auto

lemma poly_x_minus_y_1[simp]: "poly_x_minus_y 1 = 1"
  unfolding poly_x_minus_y_def
  unfolding poly_lift2_def
  unfolding one_poly_def
  by simp

lemma poly_x_minus_y_eq_iff[simp]:
  fixes p q :: "'a :: {ring_char_0,idom} poly"
  shows "poly_x_minus_y p = poly_x_minus_y q \<longleftrightarrow> p = q" (is "?p = ?q \<longleftrightarrow> _")
proof(intro iffI)
  assume l: "?p = ?q"
  { fix x
    from l have "poly2 ?p x 0 = poly2 ?q x 0" by auto
    hence "poly p x = poly q x" by auto
  }
  thus "p = q" by auto
qed auto

locale ring_hom_poly_x_minus_y begin
sublocale irh: inj_ring_hom "poly_x_minus_y :: 'a :: {ring_char_0,idom} poly \<Rightarrow> 'a poly poly"
  by(unfold_locales;force)
end

lemma (in map_poly_ring_hom) map_poly_x_minus_y:
  "map_poly (map_poly hom) (poly_x_minus_y p) = poly_x_minus_y (map_poly hom p)"
  by (induct p;simp)

definition poly_add :: "'a :: comm_ring_1 poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "poly_add p q = resultant (poly_x_minus_y p) (poly_lift q)"

lemma poly_add:
  fixes p q :: "'a ::comm_ring_1 poly"
  assumes q0: "q \<noteq> 0" and x: "poly p x = 0" and y: "poly q y = 0"
  shows "poly (poly_add p q) (x+y) = 0"
  unfolding poly_add_def
proof (rule poly_resultant_zero[OF disjI2])
  have "degree q > 0" using poly_zero q0 y by auto
  thus degq: "degree (poly_lift q) > 0" by auto
qed (insert x y, simp_all)

lemma (in ring_hom) degree_map_poly_map_poly:  assumes zero: "\<forall>x. hom x = 0 \<longrightarrow> x = 0"
   shows "degree (map_poly (map_poly hom) p) = degree p"
  by (rule degree_map_poly, insert zero, auto)

lemma (in ring_hom) poly_lift_hom: "poly_lift (map_poly hom q) = map_poly (map_poly hom) (poly_lift q)"
proof -
  interpret hc: ring_hom_coeff_lift.
  show ?thesis
    unfolding poly_lift_def
    unfolding map_poly_map_poly[of coeff_lift,OF hc.hom_zero]
    unfolding map_poly_coeff_lift_hom by simp
qed

lemma (in inj_ring_hom) poly_add_hom:
  "poly_add (map_poly hom p) (map_poly hom q) = map_poly hom (poly_add p q)"
proof -
  have zero: "\<forall>x. hom x = 0 \<longrightarrow> x = 0" by simp
  note deg = degree_map_poly_map_poly[OF zero]
  interpret mh: map_poly_ring_hom hom by unfold_locales
  have cong: "\<And> x y x' y'. x = x' \<Longrightarrow> y = y' \<Longrightarrow> resultant x y = resultant x' y'" by auto
  show ?thesis unfolding poly_add_def
    by (subst mh.rh.resultant_map_poly(1), force simp: deg, force simp: deg, 
      rule cong[OF mh.map_poly_x_minus_y[symmetric] poly_lift_hom])
qed


lemma poly_lift_const:
  fixes p :: "'a :: {idom, ring_char_0} poly poly"
  assumes const: "\<forall>i \<le> degree p. degree (coeff p i) = 0"
  shows "poly_lift (map_poly (\<lambda>a. coeff a 0) p) = p" (is  "?l = _")
proof(rule poly_eqI2)
  interpret rh: ring_hom_coeff_lift.
  show deg: "degree ?l = degree p"
    unfolding degree_poly_lift
    apply(rule degree_map_poly,simp)
    using leading_coeff_0_iff[of "coeff p (degree p)"] const by auto
  fix i
  assume "i \<le> degree ?l"
  from this[unfolded deg] const have "degree (coeff p i) = 0" by auto
  from degree_0_id[OF this]
  show "coeff ?l i = coeff p i"
    unfolding coeff_poly_lift
    by(subst coeff_map_poly,auto)
qed

context begin

abbreviation "y_x == [: [: 0, -1 :], 1 :]"

private lemma poly2_y_x[simp]: fixes x :: "'a :: comm_ring_1" shows "poly2 y_x x y = y - x"
  unfolding poly2_def by simp

definition "poly_y_minus_x p \<equiv> poly_lift p \<circ>\<^sub>p y_x"

private lemma poly_y_minus_x_0[simp]: "poly_y_minus_x 0 = 0"
  unfolding poly_y_minus_x_def by simp

private lemma poly_y_minus_x_pCons[simp]:
  "poly_y_minus_x (pCons a p) = [:[: a :]:] + poly_y_minus_x p * y_x"
  unfolding poly_y_minus_x_def
  unfolding poly_lift2_pCons by simp

private lemma poly_poly_y_minus_x[simp]:
  fixes p :: "'a :: comm_ring_1 poly"
  shows "poly (poly (poly_y_minus_x p) q) x = poly p (poly q x - x)"
  by (induct p; simp add: ring_distribs)

private lemma poly2_poly_y_minus_x[simp]:
  fixes p :: "'a :: comm_ring_1 poly"
  shows "poly2 (poly_y_minus_x p) x y = poly p (y - x)"
  unfolding poly2_def by (auto simp: ring_distribs)

lemma poly_y_x_poly_x_minus_y[simp]:
  fixes p :: "'a :: {idom, ring_char_0} poly"
  shows "poly_y_x (poly_x_minus_y p) = poly_y_minus_x p"
  by (intro poly2_ext,simp)

lemma degree_poly_y_minus_x[simp]:
  fixes p :: "'a :: idom poly"
  shows "degree (poly_y_minus_x p) = degree p"
  unfolding poly_y_minus_x_def by auto

end

lemma poly_poly_x_minus_y_0:
  fixes p q :: "'a :: {idom,ring_char_0} poly"
  shows "poly (poly_x_minus_y p) 0 = p"
  apply (rule poly_ext)
  unfolding poly_poly_x_minus_y
  unfolding poly_pcompose
  by simp

lemma degree_poly_y_x_zero_imp_poly_lift:
  fixes p :: "'a :: comm_ring_1 poly poly"
  assumes "degree (poly_y_x p) = 0"
  shows "p = poly_lift (\<Sum>i\<le>degree p. monom (coeff (coeff p i) 0) i)"
proof (cases "p = 0")
  interpret rh: ring_hom_coeff_lift.
  interpret rhm: ring_hom_poly_lift.
  case False
  note assms[unfolded degree_poly_y_x[OF False]]
  from Max_ge[of "{degree (coeff p i) |i. i \<le> degree p}", unfolded this]
  have "\<And>i. i\<le>degree p \<Longrightarrow> degree (coeff p i) = 0" by auto
  from degree_0_id[OF this,symmetric]
  have "p = (\<Sum>i\<le>degree p. monom [: coeff (coeff p i) 0 :] i)"
    unfolding poly_lift_def by(subst poly_as_sum_of_monoms[symmetric],auto)
  thus ?thesis unfolding rh.monom_hom unfolding poly_lift_def[symmetric] by simp
qed auto


subsection {* For nonzero resultant *}


lemma rpoly_complex_of_real: "rpoly p (complex_of_real x) = complex_of_real (rpoly p x)"
proof -
  let ?c = complex_of_real
  interpret c: inj_field_hom ?c
    by (unfold_locales, auto)
  have id: "of_rat = ?c o of_rat" unfolding comp_def by auto
  show "rpoly p (complex_of_real x) = ?c (rpoly p x)" 
    unfolding rpoly.poly_map_poly_eval_poly[symmetric] 
    unfolding id
    by (subst map_poly_compose[symmetric], auto)
qed

lemma alg_poly_complex_of_real: "alg_poly (complex_of_real x) p = alg_poly x p"
  unfolding alg_poly_def rpoly_complex_of_real by auto

lemma poly_lift_dvd_non_const: fixes q :: "complex poly"
  assumes dvd: "r dvd (poly_lift q)" and r: "\<not> r dvd 1" and degq: "degree q > 0"
  shows "\<exists> y. poly q y = 0 \<and> (\<forall> x. poly2 r x y = 0)"
proof -
  let ?q = "poly_lift q"
  interpret rh: ring_hom_coeff_lift.
  interpret rhm: ring_hom_poly_lift.
  interpret rhyx: ring_hom_poly_y_x.
  from dvd obtain q' where q': "?q = r * q'" unfolding dvd_def by auto
  have "degree q = degree ?q" by simp
  with q' have r0: "r \<noteq> 0" and q'0: "q' \<noteq> 0" using degq by auto

  let ?q' = "poly_y_x q'"
  def r' \<equiv> "\<Sum>i\<le>degree r. monom (coeff (coeff r i) 0) i"
  have q'0: "?q' \<noteq> 0" using q'0 by auto
  let ?r = "poly_y_x r"
  have r'0: "?r \<noteq> 0" using r0 by auto
  have "?r * ?q' = poly_y_x (r * q')" by auto
  also have "... = poly_y_x ?q" unfolding q' by auto
  also note poly_y_x_poly_lift
  also have "degree (monom q 0) = 0" using degree_monom_le[of q 0] by auto
  finally have degrq: "degree (?r * ?q') = 0".
  hence "degree ?r = 0"
    using degree_mult_eq[OF _ q'0, of ?r] by (cases "?r = 0", auto)
  from degree_poly_y_x_zero_imp_poly_lift[OF this]
  have r': "r = poly_lift r'" unfolding r'_def by auto

  from r0[unfolded r'] have r0': "r' \<noteq> 0" by auto
  with r have deg: "degree r' \<noteq> 0" unfolding r' poly_dvd_1 dvd_field by (cases r', auto)
  have "\<exists>z. poly r' z = 0"
    by (rule fundamental_theorem_of_algebra_alt, insert deg, auto)
  then obtain y where rt: "poly r' y = 0" by auto
  with q'[unfolded r'] have rt_q: "poly q y = 0"
    by (metis pCons_eq_0_iff poly_mult_zero_iff poly_poly_lift)
  from rt have "\<And> x. poly2 r x y = 0" unfolding r' poly2_poly_lift by simp
  thus ?thesis using rt_q by auto
qed

lemma poly_x_minus_y_poly_lift_coprime_complex:
  fixes p q :: "complex poly"
  assumes degp: "degree p > 0" and degq: "degree q > 0"
  shows "coprime\<^sub>I (poly_x_minus_y p) (poly_lift q)" (is "coprime\<^sub>I ?p ?q")
proof (rule coprime_idom_prime_divisorI, rule ccontr)
  fix r assume "r dvd ?q" and r: "\<not> r dvd 1"
  from poly_lift_dvd_non_const[OF this degq] obtain y where rt: "\<And> x. poly2 r x y = 0" by auto

  assume "r dvd ?p" 
  then obtain p' where p': "?p = r * p'" unfolding dvd_def by auto
  have rt: "\<And> x. poly2 ?p x y = 0" using p' rt by auto
  have "p \<noteq> 0" using degp by auto
  then obtain x where x: "poly p x \<noteq> 0" by fastforce
  from poly2_poly_x_minus_y[of p "x + y" y] x have "poly2 ?p (x+y) y \<noteq> 0" by auto
  with rt[of "x + y"] show False by auto
qed


subsection \<open>Multiplication of Algebraic Numbers\<close>

lemma coeff_0_0_implies_x_dvd: assumes "coeff p 0 = (0 :: 'a :: idom)"
  shows "[:0,1:] dvd p"
proof -
  from assms have "poly p 0 = 0" 
    by (metis add.right_neutral coeff_pCons_0 mult_zero_left pCons_cases poly_pCons)
  thus "[:0,1:] dvd p" by (simp add: dvd_iff_poly_eq_0)
qed

text \<open>The proof that the resultant will be nonzero relies upon the fact that the input
  polynomials do not have 0 as root. Hence, we will eliminate zero divisors before.\<close>

function eliminate_zero_divisors :: "'a :: idom_divide poly \<Rightarrow> 'a poly" where
  "eliminate_zero_divisors p = (if coeff p 0 = 0 \<and> p \<noteq> 0 then 
    eliminate_zero_divisors (p div [:0,1:]) else p)"
  by pat_completeness auto

termination 
proof -
  {
    fix p :: "'a :: idom_divide poly"
    let ?x = "[:0,1 :: 'a:]"
    let ?q = "p div ?x"
    assume p: "p \<noteq> 0" and p0: "coeff p 0 = 0"    
    from coeff_0_0_implies_x_dvd[OF p0]
    have "?x dvd p" by auto
    from dvd_imp_mult_div_cancel_left[OF this] have id: "?x * ?q = p" .
    with p have "?x \<noteq> 0" "?q \<noteq> 0" by auto
    from degree_mult_eq[OF this, unfolded id]
    have "degree (p div ?x) < degree p" by simp 
  } note main = this
  show ?thesis
    by (relation "measure degree", auto simp: main)
qed

declare eliminate_zero_divisors.simps[simp del]

lemma rpoly_eliminate_zero_divisors: assumes x: "x \<noteq> 0"
  shows "rpoly (eliminate_zero_divisors p) x = 0 \<longleftrightarrow> rpoly p x = 0"
proof (induct p rule: eliminate_zero_divisors.induct)
  case (1 p)
  note [simp] = eliminate_zero_divisors.simps[of p]
  show ?case
  proof (cases "coeff p 0 = 0 \<and> p \<noteq> 0")
    case True
    note IH = 1[OF this]
    let ?xx = "[:0 :: rat, 1:]"
    def q \<equiv> "p div ?xx"
    have mult: "\<And> p q. rpoly (p * q) x = rpoly p x * rpoly q x"
      by (metis poly_mult rpoly.map_poly_mult rpoly.poly_map_poly_eval_poly)
    from True have "coeff p 0 = 0" by auto
    from dvd_imp_mult_div_cancel_left[OF coeff_0_0_implies_x_dvd[OF this]]
    have id: "p = ?xx * q" unfolding q_def by auto 
    have id2: "rpoly p x = 0 \<longleftrightarrow> rpoly q x = 0"
      unfolding arg_cong[OF id, of "\<lambda> p. rpoly p x = 0", unfolded mult] using x  
      by (simp add: eval_poly_def q_def)
    from True have id: "eliminate_zero_divisors p = eliminate_zero_divisors q"
      by (simp add: q_def)
    show ?thesis unfolding id using IH id2 by (simp add: q_def)
  qed auto
qed 

lemma eliminate_zero_divisors_0: "(p :: 'a :: idom_divide poly) \<noteq> 0 \<Longrightarrow> 
  eliminate_zero_divisors p \<noteq> 0 \<and> poly (eliminate_zero_divisors p) 0 \<noteq> 0"
proof (induct p rule: eliminate_zero_divisors.induct)
  case (1 p)
  note [simp] = eliminate_zero_divisors.simps[of p]
  note p = 1(2)
  show ?case
  proof (cases "coeff p 0 = 0 \<and> p \<noteq> 0")
    case True
    note IH = 1(1)[OF this]
    let ?xx = "[:0 :: 'a, 1:]"
    def q \<equiv> "p div ?xx"
    from True have "coeff p 0 = 0" by auto
    from dvd_imp_mult_div_cancel_left[OF coeff_0_0_implies_x_dvd[OF this]]
    have id: "p = ?xx * q" unfolding q_def by auto 
    with p 1(2) have "q \<noteq> 0" by auto
    note IH = IH[folded id q_def, OF this]
    from True have id: "eliminate_zero_divisors p = eliminate_zero_divisors q"
      by (simp add: q_def)
    show ?thesis unfolding id using IH by auto
  next
    case False
    hence id: "eliminate_zero_divisors p = p" by auto
    show ?thesis unfolding id using p False by (cases p, auto)
  qed
qed 

definition poly_x_div_y :: "'a :: comm_ring_1 poly \<Rightarrow> 'a poly poly" where
  [code del]: "poly_x_div_y p = (\<Sum> i \<le> degree p. monom (monom (coeff p i) i) (degree p - i))"

lemma poly_x_div_y_code[code]: 
  "poly_x_div_y p = (listsum (map (\<lambda> i. monom (monom (coeff p i) i) (degree p - i)) [0 ..< Suc (degree p)]))"
  (is "_ = ?r")
proof -
  have "poly_x_div_y p = setsum (\<lambda> i. monom (monom (coeff p i) i) (degree p - i)) (set [0 ..< Suc (degree p)])"
    unfolding poly_x_div_y_def
    by (rule setsum.cong, auto)
  also have "\<dots> = ?r" unfolding setsum.set_conv_list
    by (subst distinct_remdups_id, auto)
  finally show ?thesis .
qed

definition poly_mult' :: "'a :: comm_ring_1 poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "poly_mult' p q = resultant (poly_x_div_y p) (poly_lift q)"

definition poly_mult :: "'a :: idom_divide poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "poly_mult p q = poly_mult' (eliminate_zero_divisors p) (eliminate_zero_divisors q)"

lemma poly2_poly_x_div_y: fixes p :: "'a :: field poly"
  assumes y: "y \<noteq> 0"
  shows "poly2 (poly_x_div_y p) x y = y ^ degree p * poly p (x / y)" (is "?l = ?r")
proof -
  from poly_as_sum_of_monoms[of p]
  have "?r = y ^ degree p * poly ((\<Sum>x\<le>degree p. monom (coeff p x) x)) (x / y)" 
    by simp
  also have "\<dots> = (\<Sum>k\<le>degree p. y ^ degree p * (coeff p k * (x / y) ^ k))" 
    unfolding poly_setsum by (simp add: setsum_right_distrib poly_monom)
  also have "\<dots> = (\<Sum>k\<le>degree p. coeff p k * x ^ k * y ^ (degree p - k))" (is "_ = ?m")
    by (rule setsum.cong, insert y, auto simp: power_diff power_divide)
  finally have rm: "?r = ?m" .
   
  have "?l = (\<Sum>k\<le>degree p. poly (poly (monom (monom (coeff p k) k) (degree p - k)) [:y:]) x)"
    unfolding poly2_def poly_x_div_y_def poly_setsum ..
  also have "\<dots> = ?m" unfolding poly_monom poly_mult poly_power by simp
  finally have lm: "?l = ?m" .

  show ?thesis unfolding lm rm ..
qed


lemma poly_x_div_y_0[simp]: "poly_x_div_y p = 0 \<longleftrightarrow> p = 0"
proof (cases "degree p = 0")
  case True 
  from degree0_coeffs[OF this] obtain a where p: "p = [:a:]" by auto
  thus ?thesis  
    unfolding poly_x_div_y_def by simp
next
  case False
  have "coeff (poly_x_div_y p) 0 \<noteq> 0"
    unfolding poly_x_div_y_def coeff_setsum coeff_monom
    by (subst setsum.remove[of _ "degree p"], force, force, subst setsum.neutral, insert False, auto)
  thus ?thesis using False by auto
qed

lemma poly_x_div_y_degree_eq[simp]: assumes p0: "poly p 0 \<noteq> 0"
  shows "degree (poly_x_div_y p) = degree p"
proof - 
  have "coeff (poly_x_div_y p) (degree p) \<noteq> 0"
    unfolding poly_x_div_y_def coeff_setsum coeff_monom
    by (subst setsum.remove[of _ 0], force, force, 
      subst setsum.neutral, insert p0, auto simp: poly_0_coeff_0)
  hence ge: "degree (poly_x_div_y p) \<ge> degree p" by (rule le_degree)
  have le: "degree (poly_x_div_y p) \<le> degree p" unfolding poly_x_div_y_def
    by (rule degree_setsum_le, force, rule order.trans, rule degree_monom_le, auto)
  from le ge show ?thesis by auto
qed


lemma poly_mult':
  fixes p q :: "'a :: field poly"
  assumes q0: "q \<noteq> 0"
      and x: "poly p x = 0" and y: "poly q y = 0"
      and y0: "y \<noteq> 0" 
  shows "poly (poly_mult' p q) (x*y) = 0"
  unfolding poly_mult'_def
proof (rule poly_resultant_zero[OF disjI2])
  have "degree q > 0" using order_degree[OF q0, of y] y[unfolded order_root] q0 by force
  thus degq: "degree (poly_lift q) > 0" by auto
qed (insert x y y0, auto simp: poly2_poly_x_div_y)

lemma poly_x_div_y_poly_lift_coprime_complex:
  fixes p q :: "complex poly"
  assumes degp: "degree p > 0" and degq: "degree q > 0" and q0: "poly q 0 \<noteq> 0"
  shows "coprime\<^sub>I (poly_x_div_y p) (poly_lift q)" (is "coprime\<^sub>I ?p ?q")
proof (rule coprime_idom_prime_divisorI, rule ccontr)
  fix r assume "r dvd ?q" and r: "\<not> r dvd 1"
  from poly_lift_dvd_non_const[OF this degq] obtain y where rt: "\<And> x. poly2 r x y = 0" 
    and rt_q: "poly q y = 0" by auto
  with q0 have y: "y \<noteq> 0" by auto

  assume "r dvd ?p"
  then obtain p' where p': "?p = r * p'" unfolding dvd_def by auto
  have rt: "\<And> x. poly2 ?p x y = 0" using p' rt by auto
  have "p \<noteq> 0" using degp by auto
  then obtain x where x: "poly p x \<noteq> 0" by fastforce
  from x have "poly2 ?p (x*y) y \<noteq> 0" unfolding poly2_poly_x_div_y[OF y, of p "x * y"] using y by auto
  with rt[of "x * y"] show False by auto
qed

lemma poly_mult'_nonzero_complex:
  fixes p q :: "complex poly"
  assumes p0: "p \<noteq> 0" and q0: "q \<noteq> 0"
      and x: "poly p x = 0" and y: "poly q y = 0"       
      and p00: "poly p 0 \<noteq> 0" and q00: "poly q 0 \<noteq> 0"
  shows "poly_mult' p q \<noteq> 0"
proof
  have degp: "degree p > 0" using order_degree[OF p0] x[unfolded order_root] p0 by force
  have degq: "degree q > 0" using order_degree[OF q0] y[unfolded order_root] q0 by force
  have pp0: "poly_x_div_y p \<noteq> 0" (is "?p \<noteq> _") using p0 by simp
  have qq0: "poly_lift q \<noteq> 0" (is "?q \<noteq> _") using q0 by auto
  have degpp: "degree ?p = degree p" unfolding poly_x_div_y_degree_eq[OF p00] ..
  have degqq: "degree ?q = degree q" by auto
  assume 0: "poly_mult' p q = 0"
  hence r0: "resultant ?p ?q = 0" unfolding poly_mult'_def.
  with resultant_zero_imp_common_factor degp[folded degpp]
  have "\<not> coprime\<^sub>I ?p ?q" by auto
  with poly_x_div_y_poly_lift_coprime_complex[OF degp degq q00] 
  show False by auto
qed

lemma (in inj_ring_hom) poly_x_div_y_hom: 
  "poly_x_div_y (map_poly hom p) = map_poly (map_poly hom) (poly_x_div_y p)"
proof -
  interpret mh: map_poly_ring_hom hom by unfold_locales
  interpret mmh: map_poly_ring_hom "map_poly hom" by unfold_locales
  show ?thesis
    unfolding poly_x_div_y_def 
    unfolding mmh.rh.hom_setsum degree_map_poly
    unfolding coeff_map_poly_hom monom_hom mh.rh.monom_hom by simp
qed

lemma (in inj_ring_hom) poly_mult'_hom: 
  "poly_mult' (map_poly hom p) (map_poly hom q) = map_poly hom (poly_mult' p q)"
proof -
  have zero: "\<forall>x. hom x = 0 \<longrightarrow> x = 0" by simp
  interpret mh: map_poly_ring_hom hom by unfold_locales
  have cong: "\<And> x y x' y'. x = x' \<Longrightarrow> y = y' \<Longrightarrow> resultant x y = resultant x' y'" by auto
  note deg = degree_map_poly_map_poly[OF zero]
  show ?thesis unfolding poly_mult'_def
    by (subst mh.rh.resultant_map_poly, force simp: deg, force simp: deg, 
      rule cong[OF poly_x_div_y_hom poly_lift_hom])
qed

lemma eliminate_zero_divisors_hom:  
  assumes "inj_ring_hom (h :: 'a :: idom_divide \<Rightarrow> 'b :: idom_divide)"
  shows "eliminate_zero_divisors (map_poly h p) = map_poly h (eliminate_zero_divisors p)"
proof -
  interpret inj_ring_hom h by fact
  show ?thesis
  proof (induct p rule: eliminate_zero_divisors.induct)
    case (1 p)
    let ?h = "map_poly h"
    let ?p = "?h p"
    note simp = eliminate_zero_divisors.simps
    note simp = simp[of p] simp[of ?p]
    show ?case
    proof (cases "coeff p 0 = 0 \<and> p \<noteq> 0")
      case True
      note IH = 1(1)[OF this]
      let ?x = "[:0, 1 :: 'a:]"
      let ?hx = "[:0, 1 :: 'b:]"
      def q \<equiv> "p div ?x"
      def hq \<equiv> "?p div ?hx"
      from True have "coeff p 0 = 0" by auto
      from dvd_imp_mult_div_cancel_left[OF coeff_0_0_implies_x_dvd[OF this]]
      have id: "p = ?x * q" unfolding q_def by auto 
      from arg_cong[OF id, of ?h] have id': "?p = ?hx * (?h q)" by auto
      have hx: "?hx \<noteq> 0" by simp
      from True have "coeff ?p 0 = 0" by auto
      from dvd_imp_mult_div_cancel_left[OF coeff_0_0_implies_x_dvd[OF this]]
      have "?p = ?hx * hq" unfolding hq_def by auto
      with id' have "?hx * (?h q) = ?hx * hq" by auto
      from arg_cong[OF this, of "\<lambda> x. x div ?hx", unfolded nonzero_mult_divide_cancel_left[OF hx]]
      have id: "?h q = hq".
      have "?thesis = (eliminate_zero_divisors (?p div ?hx)
        = ?h (eliminate_zero_divisors (p div ?x)))"
        unfolding simp using True by auto
      also have "?h (eliminate_zero_divisors (p div ?x)) 
        = eliminate_zero_divisors (?h (p div ?x))" using IH by simp
      also have "?h (p div ?x) = ?p div ?h ?x" using id
        by (simp add: q_def hq_def)
      finally show ?thesis by simp
    qed (insert simp, auto)
  qed
qed

lemma poly_mult_hom:  
  assumes h: "inj_ring_hom h"
  shows "poly_mult (map_poly h p) (map_poly h q) = map_poly h (poly_mult p q)"
proof -
  interpret inj_ring_hom h by fact
  show ?thesis unfolding poly_mult'_hom poly_mult_def eliminate_zero_divisors_hom[OF h] ..
qed

lemma alg_poly_mult'_complex:
  fixes x :: "complex"
  assumes x: "alg_poly x p" and y: "alg_poly y q"
  and p00: "poly p 0 \<noteq> 0"
  and q00: "poly q 0 \<noteq> 0"
  and x0: "x \<noteq> 0" 
  and y0: "y \<noteq> 0" 
  shows "alg_poly (x * y) (poly_mult' p q)"
proof -
  have p0: "p \<noteq> 0" using x by auto
  hence p'0: "map_poly of_rat p \<noteq> 0" by(subst map_poly_zero, auto)
  have "rpoly p x = 0" using x by auto
  hence px0: "poly (map_poly of_rat p) x = 0" unfolding eval_poly_def by auto
  have q0: "q \<noteq> 0" using y by auto
  hence q'0: "map_poly of_rat q \<noteq> 0" by(subst map_poly_zero, auto)
  have "rpoly q y = 0" using y by auto
  hence qy0: "poly (map_poly of_rat q) y = 0" unfolding eval_poly_def by auto
  show ?thesis
  proof (rule alg_polyI)
    {
      fix p :: "rat poly"
      assume p00: "poly p 0 \<noteq> 0"
      have "poly (map_poly of_rat p) 0 = poly (map_poly of_rat p) (of_rat 0 :: complex)" by simp
      also have "\<dots> = of_rat (poly p 0)" by (rule rpoly.poly_map_poly)
      also have "\<dots> \<noteq> 0" using p00 by simp
      finally have "poly (map_poly of_rat p) 0 \<noteq> (0 :: complex)" .
    } note 00 = this
    show "rpoly (poly_mult' p q) (x * y) = (0::complex)"
      unfolding eval_poly_def
      apply(subst rpoly.poly_mult'_hom[symmetric])
      using poly_mult'[OF q'0 px0 qy0 y0] by auto
    interpret cr: inj_field_hom "of_rat :: rat \<Rightarrow> complex" by unfold_locales auto
    have "map_poly of_rat (poly_mult' p q) \<noteq> (0::complex poly)"
      apply(subst rpoly.poly_mult'_hom[symmetric])
      apply(subst poly_mult'_nonzero_complex[OF p'0 q'0 px0 qy0], insert 00[OF p00] 00[OF q00], auto)
      done
    thus "poly_mult' p q \<noteq> 0" by auto
  qed
qed

lemma alg_poly_mult_complex:
  fixes x :: "complex"
  assumes x: "alg_poly x p" and y: "alg_poly y q"
  and x0: "x \<noteq> 0"
  and y0: "y \<noteq> 0" 
  shows "alg_poly (x * y) (poly_mult p q)"
proof -
  {
    fix p and x :: complex
    assume x: "alg_poly x p" and x0: "x \<noteq> 0"
    let ?p = "eliminate_zero_divisors p"
    from x[unfolded alg_poly_def] have p: "p \<noteq> 0" and rt: "rpoly p x = 0" by auto
    from eliminate_zero_divisors_0[OF p] have p: "?p \<noteq> 0" and p00: "poly ?p 0 \<noteq> 0" by auto
    from rpoly_eliminate_zero_divisors[OF x0, of p] rt have "rpoly ?p x = 0" by auto
    with p p00 have "alg_poly x ?p" "poly ?p 0 \<noteq> 0" unfolding alg_poly_def by auto
  } note conv = this
  show ?thesis unfolding poly_mult_def
    by (rule alg_poly_mult'_complex[OF _ _ _ _ x0 y0],
      insert conv[OF x x0] conv[OF y y0], auto)
qed

lemma alg_poly_mult_real:
  fixes x :: "real"
  assumes x: "alg_poly x p" and y: "alg_poly y q"
  and x0: "x \<noteq> 0" 
  and y0: "y \<noteq> 0" 
  shows "alg_poly (x * y) (poly_mult p q)"
proof -
  let ?c = complex_of_real
  show ?thesis using alg_poly_mult_complex[of "?c x" p "?c y" q] x y x0 y0
    by (simp add: alg_poly_complex_of_real of_real_mult[symmetric] del: of_real_mult)
qed

subsection \<open>Summary: Closure Properties of Algebraic Numbers\<close>

lemma algebraic_alg_polyI: "alg_poly x p \<Longrightarrow> algebraic x"
  unfolding alg_poly_def algebraic_altdef_rpoly by auto

lemma algebraic_alg_polyE: "algebraic x \<Longrightarrow> (\<And> p. alg_poly x p \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding algebraic_altdef_rpoly alg_poly_def by auto

lemma algebraic_of_rat: "algebraic (of_rat x)"
  by (rule algebraic_alg_polyI[OF alg_poly_of_rat])

lemma algebraic_uminus: "algebraic x \<Longrightarrow> algebraic (-x)"
  by (elim algebraic_alg_polyE, rule algebraic_alg_polyI[OF alg_poly_uminus])

lemma algebraic_inverse: "algebraic x \<Longrightarrow> algebraic (inverse x)"
proof (cases "x = 0")
  case False
  thus "algebraic x \<Longrightarrow> algebraic (inverse x)" 
    by (elim algebraic_alg_polyE, rule algebraic_alg_polyI[OF alg_poly_inverse])
qed (insert algebraic_of_rat[of 0], auto)

lemma algebraic_times_complex: fixes x :: complex
  shows "algebraic x \<Longrightarrow> algebraic y \<Longrightarrow> algebraic (x * y)"
proof (cases "x = 0 \<or> y = 0")
  case False
  show "algebraic x \<Longrightarrow> algebraic y \<Longrightarrow> algebraic (x * y)"
    by (elim algebraic_alg_polyE, rule algebraic_alg_polyI[OF alg_poly_mult_complex], insert False, auto)
qed (insert algebraic_of_rat[of 0], auto)

lemma algebraic_times_real: fixes x :: real
  shows "algebraic x \<Longrightarrow> algebraic y \<Longrightarrow> algebraic (x * y)"
proof (cases "x = 0 \<or> y = 0")
  case False
  show "algebraic x \<Longrightarrow> algebraic y \<Longrightarrow> algebraic (x * y)"
    by (elim algebraic_alg_polyE, rule algebraic_alg_polyI[OF alg_poly_mult_real], insert False, auto)
qed (insert algebraic_of_rat[of 0], auto)

lemma algebraic_root: "algebraic x \<Longrightarrow> algebraic (root n x)"
proof -
  assume "algebraic x"
  from algebraic_alg_polyE[OF this] obtain p where p: "alg_poly x p" by auto
  from 
    algebraic_alg_polyI[OF alg_poly_nth_root_neg_real[OF _ this, of n]]
    algebraic_alg_polyI[OF alg_poly_nth_root_pos_real[OF _ this, of n]]
    algebraic_of_rat[of 0]
  show ?thesis by (cases "n = 0", force, cases "n > 0", force, cases "n < 0", auto)
qed

lemma algebraic_nth_root: "n \<noteq> 0 \<Longrightarrow> algebraic x \<Longrightarrow> y^n = x \<Longrightarrow> algebraic y"
  by (elim algebraic_alg_polyE, rule algebraic_alg_polyI[OF alg_poly_nth_root], auto)

subsection {* Interfacing UFD properties *}

lemma dvd_dvd_imp_smult:
  fixes p q :: "'a :: idom poly"
  assumes pq: "p dvd q" and qp: "q dvd p" shows "\<exists>c. p = smult c q"
proof (cases "p = 0")
  case True
    then show ?thesis by auto
next
  case False
    from qp obtain r where r: "p = q * r" by (elim dvdE, auto)
    with False qp have r0: "r \<noteq> 0" and q0: "q \<noteq> 0" by auto
    with divides_degree[OF pq] divides_degree[OF qp] False
    have "degree p = degree q" by auto
    with r degree_mult_eq[OF q0 r0] have "degree r = 0" by auto
    from degree_0_id[OF this] obtain c where "r = [:c:]" by metis
    from r[unfolded this] show ?thesis by auto
qed

lemma dvd_const:
  assumes pq: "(p::'a::semidom poly) dvd q" and q0: "q \<noteq> 0" and degq: "degree q = 0"
  shows "degree p = 0"
proof-
  from dvdE[OF pq] obtain r where *: "q = p * r".
  with q0 have "p \<noteq> 0" "r \<noteq> 0" by auto
  from degree_mult_eq[OF this] degq * show "degree p = 0" by auto
qed

(*TODO why need "algebraic_"? *)

class algebraic_idom = algebraic_semidom + idom_divide

instance poly::(idom_divide) algebraic_idom..

subclass(in Fields.field) algebraic_idom..

lemma Units_connect[simp]:
  "Units (mk_monoid::'a::algebraic_idom monoid) = Collect is_unit" (is "?L = ?R")
proof(intro Set.equalityI subsetI, unfold mem_Collect_eq)
  fix x assume "x \<in> ?L" thus "is_unit x" unfolding Units_def by (auto simp: dvdI)
next
  fix x :: 'a assume "is_unit x"
  from this obtain y where "x * y = 1" "y * x = 1" by (elim dvdE, auto simp: mult.commute)
  moreover then have "y \<noteq> 0" "x \<noteq> 0" by auto
  ultimately show "x \<in> ?L" by (auto simp: Units_def)
qed

lemma is_unit_poly[simp]:
  "(is_unit :: 'a :: algebraic_idom poly \<Rightarrow> bool) = (\<lambda> p. degree p = 0 \<and> is_unit (coeff p 0))"
proof(intro ext iffI conjI, unfold conj_imp_eq_imp_imp)
  fix p :: "'a poly"
  assume degp: "degree p = 0" and p0: "is_unit (coeff p 0)"
  with degree_0_id[symmetric] obtain c where pc: "p = [:c:]" and c: "is_unit c" by auto
  from c obtain d where "1 = c * d" by (elim dvdE)
  with pc have "1 = p * [: d :]" by (auto simp: one_poly_def mult.commute)
  then show "is_unit p" by (intro dvdI)
next
  fix p :: "'a poly"
  assume p: "is_unit p"
  from p obtain q where pq: "1 = p * q" by (elim dvdE)
  then have "p \<noteq> 0" "q \<noteq> 0" by auto
  with pq degree_mult_eq[of p q] have degp: "degree p = 0" and degq: "degree q = 0" by auto
  with pq have "[: coeff p 0 :] * [: coeff q 0 :] = 1"
    by (auto simp: degree_0_id)
  then have "1 = coeff p 0 * coeff q 0" by (simp add: one_poly_def mult.commute)
  then show "is_unit (coeff p 0)" by(rule dvdI)
  show "degree p = 0" by fact
qed

definition "irred x \<equiv> \<forall>y. y dvd x \<longrightarrow> \<not> x dvd y \<longrightarrow> is_unit y"

lemma irredI[intro!]:
  assumes "\<And>y. y dvd x \<Longrightarrow> \<not> x dvd y \<Longrightarrow> is_unit y"
  shows "irred x"
  using assms unfolding irred_def by auto

lemma irredD[dest]:
  assumes "irred x"
  shows "y dvd x \<Longrightarrow> \<not> x dvd y \<Longrightarrow> is_unit y"
  using assms[unfolded irred_def] by auto

lemma irred_0_imp_unit_iff_nonzero[simp]:
  assumes "irred (0 :: 'a:: algebraic_idom)" shows "is_unit (x::'a) \<longleftrightarrow> x \<noteq> 0"
proof (cases "0 dvd x")
  case True then have "x = 0" by simp
    moreover then have "\<not> is_unit x" by auto
    ultimately show ?thesis by auto
next
  case False
    then have "x \<noteq> 0" by auto
    moreover have "x dvd 0" by auto
    from irredD[OF assms this False]
    have "is_unit x".
    ultimately show ?thesis by auto
qed

lemma irred_unit_mult:
  assumes x: "irred (x::'a::algebraic_idom)" and y: "is_unit y"
  shows "irred (x*y)"
  using assms by (auto simp: dvd_mult_unit_iff mult_unit_dvd_iff) 

lemma factor_connect[simp]:
  fixes x y :: "'a :: idom"
  shows "factor x y \<longleftrightarrow> (x = 0 \<longleftrightarrow> y = 0) \<and> x dvd y" (is "?L \<longleftrightarrow> ?R")
proof (intro iffI)
  assume L: ?L
  from this[unfolded factor_def] obtain r where "r \<noteq> 0" "y = x * r" by auto
  then show ?R by (cases "x = 0", auto)
next
  assume R: ?R
  with dvdE obtain r where r: "y = x * r" by auto
  show ?L
  proof (cases "x = 0")
    case True
      with r have "y = 0" by auto
      then show ?L unfolding factor_def True by (auto intro: exI[of _ 1])
  next
    case False
      with R r have "r \<noteq> 0" by auto
      with r show ?L unfolding factor_def by auto
  qed
qed

abbreviation ddvd (infix "ddvd" 40) where "x ddvd y \<equiv> x dvd y \<and> y dvd x"

lemma associated_connect[simp]:
  shows "(associated mk_monoid :: 'a :: idom \<Rightarrow> 'a \<Rightarrow> bool) = op ddvd" (is "?l = ?r")
proof(intro ext)
  fix x y
  show "?l x y \<longleftrightarrow> ?r x y"
  proof(cases "x = 0")
    case True then show ?thesis by (simp add: associated_def)
  next
    case False show ?thesis
    proof
      assume "associated mk_monoid x y" then show "x ddvd y" by (simp add: associated_def)
    next
      assume "x ddvd y"
      moreover with False have "y \<noteq> 0" by auto
      ultimately show "associated mk_monoid x y" by (auto simp: associated_def)
    qed
  qed
qed

lemma irred_connect[simp]:
  shows "(Divisibility.irreducible mk_monoid :: 'a :: algebraic_idom \<Rightarrow> bool) =
    (\<lambda>p. p = 0 \<or> (\<not> is_unit p \<and> irred p))" (is "?l = ?r")
proof (intro ext iffI)
  fix p assume R: "?r p" show "?l p"
  proof (cases "p = 0")
    case True
      then show ?thesis
        unfolding Divisibility.irreducible_def properfactor_def by auto
  next case False
    with R have "\<not> is_unit p" "irred p" by auto
    with False show ?thesis
      unfolding Divisibility.irreducible_def properfactor_def by auto
  qed
next
  fix p assume L: "?l p" show "?r p"
  proof(cases "p = 0")
    case True then show ?thesis by auto
  next
    case False
    with L[unfolded Divisibility.irreducible_def properfactor_def]
    have *: "\<not> is_unit p"
     and **: "\<And>q. q \<noteq> 0 \<Longrightarrow> q dvd p \<Longrightarrow> \<not> p dvd q \<Longrightarrow> is_unit q" by auto
    have "irred p"
    proof
      fix q assume qp: "q dvd p"
      with False have "q \<noteq> 0" by auto
      from **[OF this qp]
      show "\<not> p dvd q \<Longrightarrow> is_unit q" by auto
    qed
    with * show ?thesis by auto
  qed
qed

lemma factors_id:
  shows "factors = (\<lambda>fs p :: 'a :: algebraic_idom. (\<forall>f \<in> set fs. f = 0 \<or> (\<not> is_unit f \<and> irred f)) \<and> p = listprod fs)"
  by (intro ext, auto simp: listprod.eq_foldr factors_def)

lemma factors_with_0:
  fixes p :: "'a :: algebraic_idom"
  assumes "0 \<in> set fs"
  shows "factors fs p \<Longrightarrow> p = 0"
  unfolding factors_id using assms[folded listprod_zero_iff] by auto

lemma factors_nonzero:
  assumes p0: "(p :: 'a :: algebraic_idom) \<noteq> 0"
  shows "factors fs p \<longleftrightarrow> (\<forall>f \<in> set fs. \<not> is_unit f \<and> irred f) \<and> p = listprod fs" (is "?L \<longleftrightarrow> ?R") 
proof
  assume L: ?L
  with p0 factors_with_0[of fs p] have "0 \<notin> set fs" by auto
  with L[unfolded factors_id] show ?R by auto
next
  assume R: ?R
  with p0 show ?L unfolding factors_id by auto
qed

definition "mset_factors F p \<equiv> F \<noteq> {#} \<and> (\<forall>f. f \<in># F \<longrightarrow> \<not> is_unit f \<and> irred f) \<and> p = msetprod F"

lemma mset_factorsI[intro!]:
  assumes "\<And>f. f \<in># F \<Longrightarrow> irred f \<and> \<not> is_unit f"
      and "F \<noteq> {#}"
      and "msetprod F = p"
  shows "mset_factors F p"
  unfolding mset_factors_def using assms by auto

lemma mset_factorsD[dest]:
  assumes "mset_factors F (p :: 'a :: algebraic_idom)"
  shows "f \<in># F \<Longrightarrow> irred f \<and> \<not> is_unit f"
    and "F \<noteq> {#}"
    and "msetprod F = p"
  using assms[unfolded mset_factors_def] by auto

lemma mset_factors_imp_not_is_unit:
  assumes "mset_factors F (p :: 'a :: algebraic_idom)"
  shows "\<not> is_unit p"
proof(cases F)
  case empty with assms show ?thesis by auto
next
  case (add F f)
  with assms have "\<not> is_unit f" "msetprod F * f = p" by auto
  with is_unit_mult_iff show ?thesis by blast
qed

lemma factors_empty[simp]: "factors [] p \<longleftrightarrow> p = 1"
  unfolding factors_def by auto

lemma factors_connect[simp]:
  assumes p0: "(p :: 'a :: algebraic_idom) \<noteq> 0"
      and pU: "\<not> is_unit p"
  shows "factors fs p \<longleftrightarrow> mset_factors (mset fs) p" (is "?L \<longleftrightarrow> ?R")
  unfolding factors_nonzero[OF p0] mset_factors_def using pU by (cases fs,auto)

abbreviation poly_associated (infix "\<sim>\<^sub>p" 40)
  where "p \<sim>\<^sub>p q \<equiv> \<exists>c. is_unit c \<and> p = smult c q"

lemma associated_connect_poly[simp]:
  shows "associated mk_monoid = (op \<sim>\<^sub>p :: 'a :: algebraic_idom poly \<Rightarrow> 'a poly \<Rightarrow> bool)" (is "?L = ?R")
proof(intro ext iffI)
  fix p q
  assume "?L p q"
  note this[unfolded associated_def factor_def monoid.simps]
  then obtain c d where c0: "c \<noteq> 0" and d0: "d \<noteq> 0" and qpc: "q = p * c" and pqd: "p = q * d" by force
  then have "p = 0 \<longleftrightarrow> q = 0" by auto
  then consider (zero) "p = 0" "q = 0" | (nonzero) "p \<noteq> 0" "q \<noteq> 0" by auto
  then show "\<exists>c. is_unit c \<and> p = smult c q"
  proof (cases)
    case zero then show ?thesis by (auto intro: exI[of _ 1])
  next
    case nonzero
      from qpc degree_mult_eq[OF nonzero(1) c0] have "degree q = degree p + degree c" by auto
      moreover
      from pqd degree_mult_eq[OF nonzero(2) d0] have "degree p = degree q + degree d" by auto
      ultimately have "degree d = 0" "degree c = 0" by auto
      with degree_0_id[symmetric] c0 d0 obtain e f where "c = [:e:]" "d = [:f:]" by auto
      with qpc pqd have pfq: "p = smult f q" and "q = smult e p" by auto
      then have "p = smult (f*e) p" by auto
      also have "lead_coeff ... = f * e * lead_coeff p" by (auto simp: lead_coeff_def)
      finally have "lead_coeff p = (f * e) * lead_coeff p" by simp
      with nonzero lead_coeff_nonzero have "f * e = 1" by auto
      then have "is_unit f" by (auto intro: dvdI)
      with pfq show ?thesis by auto
  qed
next
  fix p q :: "'a poly"
  assume R: "\<exists>c. is_unit c \<and> p = smult c q"
  then have "p = 0 \<longleftrightarrow> q = 0" by auto
  then consider (zero) "p = 0" "q = 0" | (nonzero) "p \<noteq> 0" "q \<noteq> 0" by auto
  then show "?L p q"
  proof (cases)
    case zero
      show ?thesis unfolding associated_def factor_def monoid.simps zero by (auto intro: exI[of _ 1])
  next
    case nonzero
      moreover with R obtain c where c: "p = smult c q" and unit: "is_unit c" by auto
      from c have qp: "q dvd p" by (simp add: dvd_smult)
      moreover from unit obtain d where "1 = c * d" by (elim dvdE)
      then have "q = smult d p" unfolding c by (simp add: mult.commute)
      then have pq: "p dvd q" by (simp add: dvd_smult)
      ultimately show ?thesis unfolding associated_def factorid by auto
  qed
qed

locale ufd_loc_algebraic = ufd_loc ty for ty :: "'a :: {ufd,algebraic_idom} itself"
begin

lemma mset_factors_unique:
  assumes p0: "(p :: 'a) \<noteq> 0" and F: "mset_factors F (p::'a)" and F': "mset_factors F' p"
  shows "rel_mset (op ddvd) F F'"
proof -
  from mset_factors_imp_not_is_unit[OF F] have pU: "\<not> is_unit p" by auto
  obtain fs where fsF: "mset fs = F" using ex_mset by auto
  with F p0 pU have fs: "factors fs p" by auto
  obtain fs' where fs'F': "mset fs' = F'" using ex_mset by auto
  with F' p0 pU have fs': "factors fs' p" by auto
  have "\<exists>fs''. F = mset fs'' \<and> list_all2 (op ddvd) fs'' fs'"
  proof -
    from p0 fs fs' factors_with_0 have "0 \<notin> set fs" "0 \<notin> set fs'" by metis+
    with factors_unique[OF fs fs'] p0 pU
    have "essentially_equal mk_monoid fs fs'" by auto
    from this[unfolded essentially_equal_def associated_connect]
    obtain fs''
    where perm: "mset fs = mset fs''"
      and corr: "list_all2 (op ddvd) fs'' fs'"
      by (auto simp: mset_eq_perm)
    then show ?thesis by (auto simp: fsF)
  qed
  with fs'F' show ?thesis unfolding rel_mset_def by auto
qed

lemma mset_factors_exist:
  assumes p0: "(p :: 'a) \<noteq> 0" and pU: "\<not> is_unit p"
  shows "\<exists> F. mset_factors F p"
proof -
  from factors_exist[of p] p0 pU obtain fs where "factors fs p" by auto
  with pU show ?thesis using p0 by auto
qed

end

subsection {* Preservation of Irreducibility *}


lemma is_unit_field_poly[simp]:
  "is_unit (p::'a::field poly) \<longleftrightarrow> p \<noteq> 0 \<and> degree p = 0"
  unfolding is_unit_poly
proof(intro iffI conjI, unfold conj_imp_eq_imp_imp)
  assume "is_unit p"
  then obtain q where *: "p * q = 1" by (elim dvdE, auto)
  from * show p0: "p \<noteq> 0" by auto
  from * have q0: "q \<noteq> 0" by auto
  from * degree_mult_eq[OF p0 q0]
  show "degree p = 0" by auto
next
  assume "degree p = 0"
  from degree_0_id[OF this,symmetric]
  obtain c where c: "p = [:c:]" by auto
  assume "p \<noteq> 0"
  with c have "c \<noteq> 0" by auto
  with c have "1 = p * [:1/c:]" unfolding one_poly_def by auto
  from dvdI[OF this] show "is_unit p".
qed

locale ring_hom_algebraic = ring_hom hom for hom :: "'a :: algebraic_idom \<Rightarrow> 'b :: algebraic_idom"
begin
lemma is_unit_hom: "is_unit x \<Longrightarrow> is_unit (hom x)" by (metis hom_dvd hom_one)
end

lemma (in semiring_hom) msetprod_hom[simp]:
  shows "msetprod (image_mset hom M) = hom (msetprod M)"
  by (induct M, auto)

lemma not_irred_0_poly[simp]:
  "\<not> irred (0::'a::algebraic_idom poly)"
proof
  assume irr: "irred (0::'a poly)"
  have "~ is_unit [:0::'a,1:]" by (simp add: poly_dvd_1)
  with irr show False by auto
qed

locale factor_preserving_hom =
  ring_hom_algebraic hom for hom :: "'a :: algebraic_idom \<Rightarrow> 'b :: algebraic_idom" +
  assumes irred_hom [simp]: "irred a \<Longrightarrow> irred (hom a)"
      and is_unit_hom_if: "is_unit (hom a) \<Longrightarrow> is_unit a"
begin

lemma is_unit_hom_iff[simp]: "is_unit (hom a) \<longleftrightarrow> is_unit a"
  by (rule iffI[OF is_unit_hom_if is_unit_hom])

lemma hom_mset_factors:
  assumes F: "mset_factors F p"
  shows "mset_factors (image_mset hom F) (hom p)"
proof (unfold mset_factors_def, intro conjI allI impI)
  note * = F[unfolded mset_factors_def]
  then show "hom p = msetprod (image_mset hom F)" "image_mset hom F \<noteq> {#}" by auto 
  fix f' assume "f' \<in># image_mset hom F"
  then obtain f where f: "f \<in># F" and f'f: "f' = hom f" by auto
  with * have irr: "irred f" and nu: "\<not> is_unit f" by auto
  from irr irred_hom show "irred f'" unfolding f'f by auto
  from nu show "\<not> is_unit f'" by (simp add: f'f)
qed

end

lemma factor_preserving_hom_comp:
  assumes f: "factor_preserving_hom f" and g: "factor_preserving_hom g"
  shows "factor_preserving_hom (f o g)"
proof-
  interpret f: factor_preserving_hom f by (rule f)
  interpret g: factor_preserving_hom g by (rule g)
  show ?thesis apply standard using f.irred_hom g.irred_hom by auto
qed

locale ring_isom = ring_hom isom for isom +
  assumes bij: "bij isom"
begin

sublocale inj_ring_hom isom by (standard, rule injD[OF bij_betw_imp_inj_on[OF bij]])

lemma isom_dvd[simp]: "isom a dvd isom b \<longleftrightarrow> a dvd b"
proof
  assume "isom a dvd isom b"
  then obtain hc where "isom b = isom a * hc" by (elim dvdE)
  moreover with bij obtain c where "hc = isom c" by (elim bij_pointE)
  ultimately have "isom b = isom (a * c)" by auto
  from this[unfolded hom_eq_iff] have "b = a * c".
  then show "a dvd b" by (intro dvdI)
qed (rule hom_dvd)

end

locale ring_isom_algebraic =
  ring_isom isom for isom :: "'a :: algebraic_idom \<Rightarrow> 'b :: algebraic_idom"
begin

lemma isom_is_unit[simp]: "is_unit (isom a) \<longleftrightarrow> is_unit a"
  by (subst hom_one[symmetric], rule isom_dvd)

lemma isom_irred[simp]: "irred (isom a) \<longleftrightarrow> irred a"
proof
  assume a: "irred a"
  show "irred (isom a)"
  proof (rule ccontr)
    assume "\<not> irred (isom a)"
    then obtain hb
      where degq: "hb dvd isom a" "\<not> isom a dvd hb" and "\<not> is_unit (hb)"
      unfolding irred_def by auto
    moreover from bij obtain b where "hb = isom b" by (elim bij_pointE)
    ultimately have "b dvd a" "\<not> a dvd b" "\<not> is_unit b" by auto
    with irredD[OF a] show False by auto
  qed
next
  assume ha: "irred (isom a)"
  show "irred a"
  proof (rule ccontr)
    assume "\<not> irred a"
    then obtain b where "b dvd a" "\<not> a dvd b" and "\<not> is_unit b" by auto
    then have "isom b dvd isom a" "\<not> isom a dvd isom b" and "\<not> is_unit (isom b)" by auto
    with irredD[OF ha, of "isom b"] show False by auto
  qed
qed


sublocale factor_preserving_hom isom by (standard; simp)

end

lemma id_imp_bij:
  assumes id: "\<And>x. f (f x) = x" shows "bij f"
proof (intro bijI injI surjI[of f, OF id])
  fix x y assume "f x = f y"
  then have "f (f x) = f (f y)" by auto
  with id show "x = y" by auto
qed

lemma irred_poly_uminus[simp]:
  fixes p:: "'a :: {algebraic_idom, ring_char_0} poly"
  shows "irred (p \<circ>\<^sub>p [:0,-1:]) \<longleftrightarrow> irred p"
proof-
  let ?h = "\<lambda>p :: 'a poly. p \<circ>\<^sub>p [:0,-1:]"
  interpret ring_hom_pcompose "[:0,-1:]".
  interpret ring_isom_algebraic ?h by (standard, rule id_imp_bij, auto simp: poly_pcompose)
  show ?thesis by auto
qed

interpretation ring_hom_x_y: ring_hom_pcompose "x_y".

interpretation ring_isom_x_y:
  ring_isom_algebraic "\<lambda>p :: 'a :: {algebraic_idom, ring_char_0} poly poly. p \<circ>\<^sub>p x_y"
  by (standard, rule id_imp_bij, auto simp: poly2_def poly_pcompose)

interpretation ring_hom_poly_y_x: ring_hom_poly_y_x.

interpretation ring_isom_poly_y_x:
  ring_isom_algebraic "poly_y_x :: 'a :: {algebraic_idom,ring_char_0} poly poly \<Rightarrow> 'a poly poly"
  by (standard, rule id_imp_bij, auto)

lemma irred_poly_lift[simp]:
  fixes p:: "'a :: {algebraic_idom,ring_char_0} poly"
  assumes p: "irred p"
  shows "irred (poly_lift p)"
proof(rule ccontr)
  interpret l_rh: ring_hom_poly_lift.
  interpret l: ring_hom_algebraic "poly_lift"..
  interpret yx_rh: ring_hom_poly_y_x.
  interpret yx: ring_isom_algebraic "poly_y_x::'a poly poly \<Rightarrow> 'a poly poly"
    by (standard, rule id_imp_bij, auto)
  from p have p0: "p \<noteq> 0" by auto
  assume "\<not> irred (poly_lift p)"
  then obtain q where "q dvd poly_lift p" and pq: "\<not> poly_lift p dvd q" and q: "\<not> is_unit q"
    by (auto simp: irred_def)
  then obtain r where "q * r = poly_lift p" by (elim dvdE, auto)
  then have "poly_y_x (q * r) = poly_y_x (poly_lift p)" by auto
  also have "... = [:p:]" by (auto simp: poly_y_x_poly_lift monom_0)
  also have "poly_y_x (q * r) = poly_y_x q * poly_y_x r" by auto
  finally have "... = [:p:]" by auto
  then have qp: "poly_y_x q dvd [:p:]" by (metis dvdI)
  from dvd_const[OF this] p0 have "degree (poly_y_x q) = 0" by auto
  from degree_0_id[OF this,symmetric] obtain s
    where qs: "poly_y_x q = [:s:]" by auto
  have "poly_lift s = poly_y_x (poly_y_x (poly_lift s))" by auto
    also have "... = poly_y_x [:s:]" by (auto simp: poly_y_x_poly_lift monom_0)
    also have "... = q" by (auto simp: qs[symmetric])
  finally have sq: "poly_lift s = q" by auto
  from qp[unfolded qs] have sp: "s dvd p" by (auto simp: const_poly_dvd)
  from irredD[OF p this] consider "p dvd s" | "is_unit s" by auto
  then show False
  proof (cases)
    case 1 from l_rh.irh.hom_dvd[OF this] sq pq show ?thesis by auto
  next
    case 2 from l.is_unit_hom[OF this] sq q show ?thesis by auto
  qed
qed

lemma degree_poly_lift_0_imp:
  assumes "degree (poly_lift (p::'a::comm_ring_1 poly)) = 0"
  shows "poly_lift p = [:p:]"
  by (metis assms degree_eq_zeroE degree_poly_lift poly_lift_0 poly_lift_pCons)

interpretation factor_preserving_hom_poly_lift:
  factor_preserving_hom "poly_lift::'a::field_char_0 poly \<Rightarrow> 'a poly poly"
proof-
  interpret rhl: ring_hom_poly_lift.
  show "factor_preserving_hom (poly_lift::'a::field_char_0 poly \<Rightarrow> 'a poly poly)"
  proof(standard, simp)
    fix p :: "'a poly"
    assume ulp: "is_unit (poly_lift p)"
    from this[unfolded poly_dvd_1]
    have deglp: "degree (poly_lift p) = 0"
     and *: "degree (coeff (poly_lift p) 0) = 0" "is_unit (coeff (coeff (poly_lift p) 0) 0)" by auto
    from *[unfolded degree_poly_lift_0_imp[OF deglp]]
    show "is_unit p" by auto
  qed
qed

lemma poly_x_minus_y_as_comp: "poly_x_minus_y = (\<lambda>p. p \<circ>\<^sub>p x_y) \<circ> poly_lift"
  by(intro ext, unfold poly_x_minus_y_def, auto)

interpretation factor_preserving_hom_poly_x_minus_y:
  factor_preserving_hom "poly_x_minus_y :: 'a :: field_char_0 poly \<Rightarrow> 'a poly poly"
  unfolding poly_x_minus_y_as_comp
  by (rule factor_preserving_hom_comp,standard)

lemma ddvd_trans: "(a :: 'a :: semidom) ddvd b \<Longrightarrow> b ddvd c \<Longrightarrow> a ddvd c"
  using dvd_trans by auto

definition "is_mset_set X \<equiv> \<forall>x \<in># X. count X x = 1"

lemma is_mset_setD[dest]: "is_mset_set X \<Longrightarrow> x \<in># X \<Longrightarrow> count X x = 1"
  unfolding is_mset_set_def by auto

lemma is_mset_setI[intro]:
  assumes "\<And>x. x \<in># X \<Longrightarrow> count X x = 1"
  shows "is_mset_set X"
  using assms unfolding is_mset_set_def by auto

lemma is_mset_set[simp]: "is_mset_set (mset_set X)"
  unfolding is_mset_set_def
  by (meson count_mset_set(1) count_mset_set(2) count_mset_set(3) not_in_iff)

lemma is_mset_set_add[simp]:
  "is_mset_set (X + {#x#}) \<longleftrightarrow> is_mset_set X \<and> x \<notin># X" (is "?L \<longleftrightarrow> ?R")
proof(intro iffI conjI)
  assume L: ?L
  with count_eq_zero_iff count_single show "is_mset_set X"
    unfolding is_mset_set_def by fastforce 
  show "x \<notin># X"
  proof
    assume "x \<in># X"
    then have "count (X + {#x#}) x > 1" by auto
    with L show False by (auto simp: is_mset_set_def)
  qed
next
  assume R: ?R show ?L
  proof
    fix x' assume x': "x' \<in># X + {#x#}"
    show "count (X + {#x#}) x' = 1"
    proof(cases "x' \<in># X")
      case True with R have "count X x' = 1" by auto
        moreover from True R have "count {#x#} x' = 0" by auto
        ultimately show ?thesis by auto
    next
      case False then have "count X x' = 0" by (simp add: not_in_iff)
        with R x' show ?thesis by auto
    qed
  qed
qed


lemma mset_set_id[simp]:
  assumes "is_mset_set X"
  shows "mset_set (set_mset X) = X"
  using assms unfolding is_mset_set_def
  by (metis count_eq_zero_iff count_mset_set(1) count_mset_set(3) finite_set_mset multiset_eqI)

lemma count_image_mset:
  shows "count (image_mset f X) y = (\<Sum>x | x \<in># X \<and> y = f x. count X x)"
proof(induct X)
  case empty show ?case by auto
next
  case (add X x)
    def X' \<equiv> "X + {#x#}"
    have "(\<Sum>z | z \<in># X' \<and> y = f z. count (X + {#x#}) z) =
          (\<Sum>z | z \<in># X' \<and> y = f z. count X z) + (\<Sum>z | z \<in># X' \<and> y = f z. count {#x#} z)"
      unfolding plus_multiset.rep_eq setsum.distrib..
    also have split:
      "{z. z \<in># X' \<and> y = f z} =
       {z. z \<in># X' \<and> y = f z \<and> z \<noteq> x} \<union> {z. z \<in># X' \<and> y = f z \<and> z = x}" by blast
    then have "(\<Sum>z | z \<in># X' \<and> y = f z. count {#x#} z) =
      (\<Sum>z | z \<in># X' \<and> y = f z \<and> z = x. count {#x#} z)"
      unfolding split by (subst setsum.union_disjoint, auto)
    also have "... = (if y = f x then 1 else 0)" using card_eq_Suc_0_ex1 by (auto simp: X'_def)
    also have "(\<Sum>z | z \<in># X' \<and> y = f z. count X z) = (\<Sum>z | z \<in># X \<and> y = f z. count X z)"
    proof(cases "x \<in># X")
      case True then have "z \<in># X' \<longleftrightarrow> z \<in># X" for z by (auto simp: X'_def)
      then show ?thesis by auto 
    next
      case False
        have split: "{z. z \<in># X' \<and> y = f z} = {z. z \<in># X \<and> y = f z} \<union> {z. z = x \<and> y = f z}"
          by (auto simp: X'_def)
        also have "setsum (count X) ... = (\<Sum>z | z \<in># X \<and> y = f z. count X z) + (\<Sum>z | z = x \<and> y = f z. count X z)"
          by (subst setsum.union_disjoint, auto simp: False)
        also with False have "\<And>z. z = x \<and> y = f z \<Longrightarrow> count X z = 0" by (meson count_inI)
        with setsum.neutral_const have "(\<Sum>z | z = x \<and> y = f z. count X z) = 0" by auto
        finally show ?thesis by auto
    qed
    also have "... = count (image_mset f X) y" using add by auto
    finally show ?case by (simp add: X'_def)  
qed

lemma is_mset_set_image:
  assumes "inj_on f (set_mset X)" and "is_mset_set X"
  shows "is_mset_set (image_mset f X)"
proof (cases X)
  case empty then show ?thesis by auto
next
  case (add X x)
    def X' \<equiv> "X + {#x#}"
    with assms add have inj:"inj_on f (set_mset X')"
          and X': "is_mset_set X'" by auto
  show ?thesis
  proof(unfold add, intro is_mset_setI, fold X'_def)
    fix y assume "y \<in># image_mset f X'"
    then have "y \<in> f ` set_mset X'" by auto 
    with inj have "\<exists>!x'. x' \<in># X' \<and> y = f x'" by (meson imageE inj_onD)
    then obtain x' where x': "{x'. x' \<in># X' \<and> y = f x'} = {x'}" by auto
    then have "count (image_mset f X') y = count X' x'"
      unfolding count_image_mset by auto
    also from X' x' have "... = 1" by auto
    finally show "count (image_mset f X') y = 1".
  qed
qed

lemma image_mset_inj_on:
  assumes fin: "finite X" and inj: "inj_on f X"
  shows "image_mset f (mset_set X) = mset_set (f ` X)" (is "?l = ?r")
proof(intro multiset_eqI)
  fix x
  from inj fin have "is_mset_set ?l" by (subst is_mset_set_image, auto)
  from is_mset_setD[OF this, of x] fin
  have "count ?l x = (if x \<in> f ` X then 1 else 0)" by (auto simp: count_image_mset)
  also from fin have "... = count ?r x" by simp
  finally show "count ?l x = ..." by auto 
qed

lemma rel_mset_free:
  assumes rel: "rel_mset rel X Y" and xs: "mset xs = X"
  shows "\<exists>ys. mset ys = Y \<and> list_all2 rel xs ys"
proof-
  from rel[unfolded rel_mset_def] obtain xs' ys'
    where xs': "mset xs' = X" and ys': "mset ys' = Y" and xsys': "list_all2 rel xs' ys'" by auto
  from xs' xs mset_eq_perm have perm: "xs <~~> xs'" by auto
  from permutation_Ex_bij[OF perm] obtain f
    where bij: "bij_betw f {..<length xs} {..<length xs'}"
      and *: "\<And>i. i < length xs \<Longrightarrow> xs ! i = xs' ! f i" by auto
  note [simp] = perm_length[OF perm,symmetric]
  note [simp] = list_all2_lengthD[OF xsys',symmetric]
  note [simp] = atLeast0LessThan[symmetric]
  def ys \<equiv> "map (nth ys' \<circ> f) [0..<length ys']"
  then have [simp]: "length ys = length ys'" by auto 
  have "mset ys = mset (map (nth ys') (map f [0..<length ys']))"
   unfolding ys_def by auto
  also have "... = image_mset (nth ys') (image_mset f (mset [0..<length ys']))"
    unfolding mset_map by simp
  also have "(mset [0..<length ys']) = mset_set {0..<length ys'}"
    by (metis mset_sorted_list_of_multiset sorted_list_of_mset_set sorted_list_of_set_range) 
  also have "image_mset f (...) = mset_set (f ` {..<length ys'})"
    using bij_betw_imp_inj_on[OF bij]
    by (subst image_mset_inj_on; simp)
  also have "... = mset [0..<length ys']" using bij by (simp add: bij_betw_def)
  also have "image_mset (nth ys') ... = mset ys'" by(fold mset_map, unfold map_nth, auto)
  finally have "mset ys = Y" using ys' by auto
  moreover have "list_all2 rel xs ys"
  proof(rule list_all2_all_nthI)
    fix i assume i: "i < length xs"
    with * have "xs ! i = xs' ! f i" by auto
    also from i list_all2_nthD[OF xsys', of "f i"] bij_betwE[OF bij] lessThan_iff
    have "rel (xs' ! f i) (ys' ! f i)" by auto 
    finally show "rel (xs ! i) (ys ! i)" unfolding ys_def using i by simp
  qed simp
  ultimately show ?thesis by auto
qed

lemma rel_mset_split:
  assumes rel: "rel_mset rel (X1+X2) Y"
  shows "\<exists>Y1 Y2. Y = Y1 + Y2 \<and> rel_mset rel X1 Y1 \<and> rel_mset rel X2 Y2"
proof-
  obtain xs1 where xs1: "mset xs1 = X1" using ex_mset by auto
  obtain xs2 where xs2: "mset xs2 = X2" using ex_mset by auto
  from xs1 xs2 have "mset (xs1 @ xs2) = X1 + X2" by auto
  from rel_mset_free[OF rel this] obtain ys
    where ys: "mset ys = Y" "list_all2 rel (xs1 @ xs2) ys" by auto
  then obtain ys1 ys2
    where ys12: "ys = ys1 @ ys2"
      and xs1ys1: "list_all2 rel xs1 ys1"
      and xs2ys2: "list_all2 rel xs2 ys2"
    using list_all2_append1 by blast
  from ys12 ys have "Y = mset ys1 + mset ys2" by auto
  moreover from xs1 xs1ys1 have "rel_mset rel X1 (mset ys1)" unfolding rel_mset_def by auto
  moreover from xs2 xs2ys2 have "rel_mset rel X2 (mset ys2)" unfolding rel_mset_def by auto
  ultimately show ?thesis by (subst exI[of _ "mset ys1"], subst exI[of _ "mset ys2"],auto)
qed

lemma mset_factors_mult:
  assumes F: "mset_factors F (a::'a::algebraic_idom)"
      and G: "mset_factors G b"
  shows "mset_factors (F+G) (a*b)"
proof(intro mset_factorsI)
  fix f assume "f \<in># F + G"
  then consider "f \<in># F" | "f \<in># G" by auto
  then show "irred f \<and> \<not> is_unit f" by(cases, insert F G, auto)
qed (insert F G, auto)
  
lemma (in ufd_loc_algebraic) dvd_imp_subset_factors:
  assumes ab: "(a::'a) dvd b"
      and b0: "b \<noteq> 0"
      and F: "mset_factors F a"
      and G: "mset_factors G b"
  shows "\<exists>G'. G' \<subseteq># G \<and> rel_mset (op ddvd) F G'"
proof-
  from ab obtain c where c: "b = a * c" by (elim dvdE, auto)
  with b0 have a0: "a \<noteq> 0" and c0: "c \<noteq> 0" by auto
  show ?thesis
  proof(cases "is_unit c")
    case True show ?thesis
      proof(cases F)
        case empty with F show ?thesis by auto
      next
        case (add F' f)
          with F
          have "msetprod F' * f = a"
           and F': "\<And>f. f \<in># F' \<Longrightarrow> \<not>is_unit f \<and> irred f"
           and fU: "\<not>is_unit f"
           and irrf: "irred f" by auto
          with c have "msetprod F' * (f * c) = b" by auto
          moreover {
            from fU True is_unit_mult_iff have "\<not>is_unit (f * c)" by blast
            moreover from irred_unit_mult[OF irrf True] have "irred (f * c)" by auto
            ultimately have "\<And>f'. f' \<in># F' + {#f * c#} \<Longrightarrow> irred f' \<and> \<not> is_unit f'"
              using F' True by auto
          }
          ultimately have "mset_factors (F' + {#f * c#}) b" by (intro mset_factorsI, auto)
          from mset_factors_unique[OF b0 this G]
          have F'G: "rel_mset op ddvd (F' + {#f * c#}) G".
          from True add have FF': "rel_mset op ddvd F (F' + {#f * c#})"
            by (simp add: multiset.rel_refl rel_mset_Plus)
          have "rel_mset op ddvd F G"
            apply(rule transpD[OF multiset.rel_transp[OF transpI] FF' F'G])
            using ddvd_trans.
          then show ?thesis by auto
      qed
  next
    case False
      from mset_factors_exist[OF c0 this] obtain H where H: "mset_factors H c" by auto
      from c mset_factors_mult[OF F H] have "mset_factors (F + H) b" by auto
      note mset_factors_unique[OF b0 this G]
      from rel_mset_split[OF this] obtain G1 G2
        where "G = G1 + G2" "rel_mset (op ddvd) F G1" "rel_mset (op ddvd) H G2" by auto
      then show ?thesis by (intro exI[of _ "G1"], auto)
  qed
qed

lemma irred_factor_singleton:
  assumes a: "irred (a::'a::algebraic_idom)" and a0: "a \<noteq> 0" and F: "mset_factors F a"
  shows "F = {#a#}"
proof(cases F)
  case empty with mset_factorsD[OF F] show ?thesis by auto
next
  case (add F' f)
    with mset_factorsD[OF F] have *: "a = msetprod F' * f" by auto
    then have fa: "f dvd a" by auto
    from * a0 have f0: "f \<noteq> 0" by auto
    from add have "f \<in># F" by auto
    with F have f: "\<not>is_unit f" "irred f" by auto
    from add have "F' \<subseteq># F" by auto
    then have unitemp: "is_unit (msetprod F') \<Longrightarrow> F' = {#}"
    proof(induct F')
      case empty then show ?case by auto
    next
      case (add F' f)
        from add have "f \<in># F" by (simp add: mset_subset_eq_insertD)
        with F have "\<not> is_unit f" by auto
        then have "\<not> is_unit (msetprod F' * f)" by (simp add: is_unit_mult_iff)
        with add show ?case by auto
    qed
    show ?thesis
    proof(cases "a dvd f")
      case True
        then obtain r where "f = r * a" by (elim dvdE, auto)
        with * have "f = (r * msetprod F') * f" by (auto simp: mult.assoc)
        with f0 have "r * msetprod F' = 1" by auto
        then have "is_unit (msetprod F')" by (metis dvd_triv_right)
        with unitemp * add show ?thesis by auto
    next
      case False with fa a f show ?thesis by auto
    qed
qed

lemma singleton_mset: "mset xs = {# x #} \<longleftrightarrow> xs = [x]"
proof
  assume "mset xs = {#x#}" then show "xs = [x]"
  by (metis empty_iff insert_iff list.set(2) mset.simps(2) mset_zero_iff neq_Nil_conv set_mset_mset set_mset_single single_is_union)
next
  assume "xs = [x]" then show "mset xs = {# x #}" by auto
qed

lemma (in ufd_loc_algebraic) irred_dvd_imp_factor:
  assumes ab: "(a::'a) dvd b"
      and b0: "b \<noteq> 0"
      and a: "\<not> is_unit a" "irred a"
      and G: "mset_factors G b"
  shows "\<exists>g \<in># G. a ddvd g"
proof-
  from a have "mset_factors {#a#} a" by auto
  from dvd_imp_subset_factors[OF ab b0 this G]
  obtain G' where G'G: "G' \<subseteq># G" and rel: "rel_mset (op ddvd) {#a#} G'" by auto
  with rel_mset_size size_1_singleton_mset size_single
  obtain g where gG': "G' = {#g#}" by fastforce
  from rel[unfolded this rel_mset_def singleton_mset]
  have "a ddvd g" by auto
  with gG' G'G show ?thesis by auto
qed

lemma factors_dvd: assumes "mset_factors F x" "f \<in># F" shows "f dvd x"
  using assms by (simp add: dvd_msetprod mset_factors_def)

lemma coprime_poly_x_minus_y_poly_lift:
  fixes p q :: "'a :: field_char_0 poly"
  assumes degp: "degree p > 0" and degq: "degree q > 0"
  shows "coprime\<^sub>I (poly_x_minus_y p) (poly_lift q)"
proof(rule ccontr)
  from degp have p: "\<not> is_unit p" by (auto simp: dvd_const)
  from degp have p0: "p \<noteq> 0" by auto
  from ufd_loc_algebraic.mset_factors_exist[OF p0 p]
  obtain F where F: "mset_factors F p" by auto
  with factor_preserving_hom_poly_x_minus_y.hom_mset_factors
  have pF: "mset_factors (image_mset poly_x_minus_y F) (poly_x_minus_y p)" by auto

  from degq have q: "\<not> is_unit q" by (auto simp: dvd_const)
  from degq have q0: "q \<noteq> 0" by auto
  from ufd_loc_algebraic.mset_factors_exist[OF q0 q]
  obtain G where G: "mset_factors G q" by auto
  with factor_preserving_hom_poly_lift.hom_mset_factors
  have pG: "mset_factors (image_mset poly_lift G) (poly_lift q)" by auto

  assume "\<not> coprime\<^sub>I (poly_x_minus_y p) (poly_lift q)"
  from this[unfolded not_coprime_iff_common_factor]
  obtain r
  where rp: "r dvd (poly_x_minus_y p)"
    and rq: "r dvd (poly_lift q)"
    and rU: "\<not>is_unit r" by auto
  from rp p0 have r0: "r \<noteq> 0" by auto
  from ufd_loc_algebraic.mset_factors_exist[OF r0 rU] obtain H
  where H: "mset_factors H r" by auto
  then have "H \<noteq> {#}" by auto
  then obtain h where hH: "h \<in># H" by fastforce
  with H factors_dvd have hr: "h dvd r" and h: "\<not> is_unit h" "irred h" by auto
  from hr rp have "h dvd (poly_x_minus_y p)" by (rule dvd_trans)
  from ufd_loc_algebraic.irred_dvd_imp_factor[OF this _ h pF] p0
  obtain f where f: "f \<in># F" and fh: "poly_x_minus_y f ddvd h" by auto
  from hr rq have "h dvd (poly_lift q)" by (rule dvd_trans)
  from ufd_loc_algebraic.irred_dvd_imp_factor[OF this _ h pG] q0
  obtain g where g: "g \<in># G" and gh: "poly_lift g ddvd h" by auto  
  from fh gh have "poly_x_minus_y f ddvd poly_lift g" using ddvd_trans by auto
  then have "poly_y_x (poly_x_minus_y f) ddvd poly_y_x (poly_lift g)"
    unfolding ring_isom_poly_y_x.isom_dvd by auto
  also have "poly_y_x (poly_lift g) = [:g:]" unfolding poly_y_x_poly_lift monom_0 by auto
  finally have "poly_y_x (poly_x_minus_y f) ddvd [:g:]" by auto
  then have "degree (poly_y_x (poly_x_minus_y f)) = 0"
    by (metis degree_pCons_0 dvd_0_left_iff dvd_const)
  then have "degree f = 0" by simp
  with F p0 f show False by auto
qed  



subsection {* @{const poly_add} for general *}

lemma poly_add_nonzero:
  fixes p q :: "'a :: field_char_0 poly"
  assumes p0: "p \<noteq> 0" and q0: "q \<noteq> 0"
      and x: "poly p x = 0" and y: "poly q y = 0"
  shows "poly_add p q \<noteq> 0"
proof
  have degp: "degree p > 0" using order_degree[OF p0] x[unfolded order_root] p0 by force
  have degq: "degree q > 0" using order_degree[OF q0] y[unfolded order_root] q0 by force
  have pp0: "poly_x_minus_y p \<noteq> 0" (is "?p \<noteq> _") using p0 by auto
  have qq0: "poly_lift q \<noteq> 0" (is "?q \<noteq> _") using q0 by auto
  have degpp: "degree ?p = degree p" by auto
  have degqq: "degree ?q = degree q" by auto
  assume 0: "poly_add p q = 0"
  hence r0: "resultant ?p ?q = 0" unfolding poly_add_def.
  with resultant_zero_imp_common_factor[of ?p] degp[folded degpp]
  have "\<not> coprime\<^sub>I ?p ?q" by auto
  with coprime_poly_x_minus_y_poly_lift[OF degp degq]
  show False by auto
qed

lemma alg_poly_add:
  fixes x :: "'a :: field_char_0"
  assumes x: "alg_poly x p" and y: "alg_poly y q"
  shows "alg_poly (x + y) (poly_add p q)"
proof -
  have p0: "p \<noteq> 0" using x by auto
  hence p'0: "map_poly of_rat p \<noteq> 0" by(subst map_poly_zero, auto)
  have "rpoly p x = 0" using x by auto
  hence px0: "poly (map_poly of_rat p) x = 0" unfolding eval_poly_def by auto
  have q0: "q \<noteq> 0" using y by auto
  hence q'0: "map_poly of_rat q \<noteq> 0" by(subst map_poly_zero, auto)
  have "rpoly q y = 0" using y by auto
  hence qy0: "poly (map_poly of_rat q) y = 0" unfolding eval_poly_def by auto
  show ?thesis
  proof (rule alg_polyI)
    show "rpoly (poly_add p q) (x + y) = 0"
      unfolding eval_poly_def
      apply(subst rpoly.poly_add_hom[symmetric])
      using poly_add[OF q'0 px0 qy0] by auto
    have "map_poly of_rat (poly_add p q) \<noteq> (0 :: 'a poly)"
      by (subst rpoly.poly_add_hom[symmetric], subst poly_add_nonzero[OF p'0 q'0 px0 qy0], auto)
    thus "poly_add p q \<noteq> 0" by auto
  qed
qed

lemma algebraic_plus: fixes x :: "'a :: field_char_0"
  shows "algebraic x \<Longrightarrow> algebraic y \<Longrightarrow> algebraic (x + y)"
  by (elim algebraic_alg_polyE, rule algebraic_alg_polyI[OF alg_poly_add])

hide_const x_y

end