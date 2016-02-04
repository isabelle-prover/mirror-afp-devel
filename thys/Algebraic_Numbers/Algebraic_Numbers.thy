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
  fixes p q :: "'a ::{ring_char_0,idom} poly"
  assumes p0: "p \<noteq> 0" and q0: "q \<noteq> 0"
      and x: "poly p x = 0" and y: "poly q y = 0"
  shows "poly (poly_add p q) (x+y) = 0"
proof -
  have p'0: "poly_x_minus_y p \<noteq> 0" using p0 by simp
  have q'0: "poly_lift q \<noteq> 0" using q0 by simp
  have "degree p > 0" using le_0_eq order_degree order_root p0 x by fastforce
  hence degp: "degree (poly_x_minus_y p) > 0" by auto
  have "degree q > 0" using le_0_eq order_degree order_root q0 y by fastforce
  hence degq: "degree (poly_lift q) > 0"  by auto
  def z == "x+y"
  have "poly2 (poly_x_minus_y p) z (z-x) = 0"
   and "poly2 (poly_lift q) z y = 0" using x y by simp+
  thus ?thesis unfolding poly_add_def using poly_resultant_zero[OF degp degq] by force
qed

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


lemma poly_add_nonzero_complex:
  fixes p q :: "complex poly"
  assumes p0: "p \<noteq> 0" and q0: "q \<noteq> 0"
      and x: "poly p x = 0" and y: "poly q y = 0"
  shows "poly_add p q \<noteq> 0"
proof
  have degp: "degree p > 0" using le_0_eq order_degree order_root p0 x by fastforce
  have degq: "degree q > 0" using le_0_eq order_degree order_root q0 y by fastforce
  have pp0: "poly_x_minus_y p \<noteq> 0" (is "?p \<noteq> _") using p0 by auto
  have qq0: "poly_lift q \<noteq> 0" (is "?q \<noteq> _") using q0 by auto
  have degpp: "degree ?p = degree p" by auto
  have degqq: "degree ?q = degree q" by auto
  assume 0: "poly_add p q = 0"
  hence r0: "resultant ?p ?q = 0" unfolding poly_add_def.
  with resultant_zero_imp_common_factor[of ?p] degp[folded degpp]
  have "\<not> coprime\<^sub>I ?p ?q" by auto
  with poly_x_minus_y_poly_lift_coprime_complex[OF degp degq]
  show False by auto
qed


lemma alg_poly_add_complex:
  fixes x :: "complex"
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
    show "rpoly (poly_add p q) (x + y) = (0::complex)"
      unfolding eval_poly_def
      apply(subst rpoly.poly_add_hom[symmetric])
      using poly_add[OF p'0 q'0 px0 qy0] by auto
    have "map_poly of_rat (poly_add p q) \<noteq> (0::complex poly)"
      apply(subst rpoly.poly_add_hom[symmetric])
      apply(subst poly_add_nonzero_complex[OF p'0 q'0 px0 qy0], auto)
      done
    thus "poly_add p q \<noteq> 0" by auto
  qed
qed

lemma alg_poly_add_real:
  fixes x :: "real"
  assumes x: "alg_poly x p" and y: "alg_poly y q"
  shows "alg_poly (x + y) (poly_add p q)"
proof -
  let ?c = complex_of_real
  show ?thesis using alg_poly_add_complex[of "?c x" p "?c y" q] x y
    by (simp add: alg_poly_complex_of_real of_real_add[symmetric] del: of_real_add)
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

function eliminate_zero_divisors :: "'a :: idom_div poly \<Rightarrow> 'a poly" where
  "eliminate_zero_divisors p = (if coeff p 0 = 0 \<and> p \<noteq> 0 then 
    eliminate_zero_divisors (exact_div p [:0,1:]) else p)"
  by pat_completeness auto

termination 
proof -
  {
    fix p :: "'a :: idom_div poly"
    let ?x = "[:0,1 :: 'a:]"
    let ?q = "exact_div p ?x"
    assume p: "p \<noteq> 0" and p0: "coeff p 0 = 0"    
    from coeff_0_0_implies_x_dvd[OF p0]
    have "?x dvd p" by auto
    from exact_div_dvdD[OF this] have id: "?x * ?q = p" .
    with p have "?x \<noteq> 0" "?q \<noteq> 0" by auto
    from degree_mult_eq[OF this, unfolded id]
    have "degree (exact_div p ?x) < degree p" by simp 
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
    def q \<equiv> "exact_div p ?xx"
    have mult: "\<And> p q. rpoly (p * q) x = rpoly p x * rpoly q x"
      by (metis poly_mult rpoly.map_poly_mult rpoly.poly_map_poly_eval_poly)
    from True have "coeff p 0 = 0" by auto
    from exact_div_dvdD[OF coeff_0_0_implies_x_dvd[OF this]]
    have id: "p = ?xx * q" unfolding q_def by auto 
    have id2: "rpoly p x = 0 \<longleftrightarrow> rpoly q x = 0"
      unfolding arg_cong[OF id, of "\<lambda> p. rpoly p x = 0", unfolded mult] using x  
      by (simp add: eval_poly_def q_def)
    from True have id: "eliminate_zero_divisors p = eliminate_zero_divisors q"
      by (simp add: q_def)
    show ?thesis unfolding id using IH id2 by (simp add: q_def)
  qed auto
qed 

lemma eliminate_zero_divisors_0: "(p :: 'a :: idom_div poly) \<noteq> 0 \<Longrightarrow> 
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
    def q \<equiv> "exact_div p ?xx"
    from True have "coeff p 0 = 0" by auto
    from exact_div_dvdD[OF coeff_0_0_implies_x_dvd[OF this]]
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

definition poly_mult :: "'a :: idom_div poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
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
  assumes p0: "p \<noteq> 0" and q0: "q \<noteq> 0"
      and x: "poly p x = 0" and y: "poly q y = 0"
      and p00: "poly p 0 \<noteq> 0"
      and x0: "x \<noteq> 0"
      and y0: "y \<noteq> 0" 
  shows "poly (poly_mult' p q) (x*y) = 0"
proof -
  have p'0: "poly_x_div_y p \<noteq> 0" using p0 by simp
  have q'0: "poly_lift q \<noteq> 0" using q0 by simp
  have dp: "degree p > 0" using le_0_eq order_degree order_root p0 x by fastforce
  hence degp: "degree (poly_x_div_y p) > 0" by (subst poly_x_div_y_degree_eq[OF p00])
  have "degree q > 0" using le_0_eq order_degree order_root q0 y by fastforce
  hence degq: "degree (poly_lift q) > 0"  by auto
  def z == "x*y"
  hence yzx: "y = z / x" using x0 by auto
  hence 1: "poly2 (poly_x_div_y p) z (z / x) = 0"
   and 2: "poly2 (poly_lift q) z (z / x) = 0" using x y y0 by (auto simp: poly2_poly_x_div_y dp)
  show ?thesis unfolding poly_mult'_def using poly_resultant_zero[OF degp degq conjI[OF 1 2]] 
    by (simp add: z_def)
qed

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
  have degp: "degree p > 0" using le_0_eq order_degree order_root p0 x by fastforce
  have degq: "degree q > 0" using le_0_eq order_degree order_root q0 y by fastforce
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
  assumes "inj_ring_hom (h :: 'a :: idom_div \<Rightarrow> 'b :: idom_div)"
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
      def q \<equiv> "exact_div p ?x"
      def hq \<equiv> "exact_div ?p ?hx"
      from True have "coeff p 0 = 0" by auto
      from exact_div_dvdD[OF coeff_0_0_implies_x_dvd[OF this]]
      have id: "p = ?x * q" unfolding q_def by auto 
      from arg_cong[OF id, of ?h] have id': "?p = ?hx * (?h q)" by auto
      have hx: "?hx \<noteq> 0" by simp
      from True have "coeff ?p 0 = 0" by auto
      from exact_div_dvdD[OF coeff_0_0_implies_x_dvd[OF this]]
      have "?p = ?hx * hq" unfolding hq_def by auto
      with id' have "?hx * (?h q) = ?hx * hq" by auto
      from arg_cong[OF this, of "\<lambda> x. exact_div x ?hx", unfolded exact_div_left[OF hx]]
      have id: "?h q = hq" .
      have "?thesis = (eliminate_zero_divisors (exact_div ?p ?hx)
        = ?h (eliminate_zero_divisors (exact_div p ?x)))"
        unfolding simp using True by auto
      also have "?h (eliminate_zero_divisors (exact_div p ?x)) 
        = eliminate_zero_divisors (?h (exact_div p ?x))" using IH by simp
      also have "?h (exact_div p ?x) = exact_div ?p (?h ?x)" using id
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
      using poly_mult'[OF p'0 q'0 px0 qy0 00[OF p00] x0 y0] by auto
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
  
hide_const x_y

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

lemma algebraic_plus_complex: fixes x :: complex
  shows "algebraic x \<Longrightarrow> algebraic y \<Longrightarrow> algebraic (x + y)"
  by (elim algebraic_alg_polyE, rule algebraic_alg_polyI[OF alg_poly_add_complex])

lemma algebraic_plus_real: fixes x :: real
  shows "algebraic x \<Longrightarrow> algebraic y \<Longrightarrow> algebraic (x + y)"
  by (elim algebraic_alg_polyE, rule algebraic_alg_polyI[OF alg_poly_add_real])

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

end