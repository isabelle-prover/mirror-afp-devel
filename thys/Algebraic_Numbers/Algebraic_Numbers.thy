(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Algebraic Numbers: Addition and Multiplication\<close>

text \<open>This theory contains the remaining field operations for algebraic numbers, namely
  addition and multiplication.\<close>

theory Algebraic_Numbers
imports
  Algebraic_Numbers_Prelim
  Resultant
  "../Polynomial_Factorization/Polynomial_Divisibility"
begin

interpretation coeff_lift_hom:
  factor_preserving_hom "coeff_lift :: 'a :: {comm_semiring_1,semiring_no_zero_divisors} \<Rightarrow> _"
  by (unfold_locales, auto simp: const_poly_dvd_1)

lemmas [simp del] =
  coeff_lift_hom.hom_one
  coeff_lift_hom.hom_uminus

subsection \<open>Addition of Algebraic Numbers\<close>

abbreviation "x_y == [: [: 0, 1 :], -1 :]"

definition "poly_x_minus_y p = poly_lift p \<circ>\<^sub>p x_y"

text \<open>The following polynomial represents the sum of two algebraic numbers.\<close>

definition poly_add :: "'a :: comm_ring_1 poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "poly_add p q = resultant (poly_x_minus_y p) (poly_lift q)"

subsubsection \<open>@{term poly_add} has desired root\<close>

interpretation poly_x_minus_y_hom:
  comm_ring_hom poly_x_minus_y by (unfold_locales; simp add: poly_x_minus_y_def)

lemma poly2_x_y[simp]:
  fixes x :: "'a :: comm_ring_1"
  shows "poly2 x_y x y = x - y" unfolding poly2_def by simp

lemma degree_poly_x_minus_y[simp]:
  fixes p :: "'a::idom poly"
  shows "degree (poly_x_minus_y p) = degree p" unfolding poly_x_minus_y_def by auto

lemma poly_x_minus_y_pCons[simp]:
  "poly_x_minus_y (pCons a p) = [:[: a :]:] + poly_x_minus_y p * x_y"
  unfolding poly_x_minus_y_def by simp

lemma poly_poly_poly_x_minus_y[simp]:
  fixes p :: "'a :: comm_ring_1 poly"
  shows "poly (poly (poly_x_minus_y p) q) x = poly p (x - poly q x)" by (induct p; simp add: ring_distribs)

lemma poly2_poly_x_minus_y[simp]:
  fixes p :: "'a :: comm_ring_1 poly"
  shows "poly2 (poly_x_minus_y p) x y = poly p (x-y)" unfolding poly2_def by simp

lemma poly_x_minus_y_zero_iff[simp]:
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

lemma poly_x_minus_y_eq_iff[simp]:
  fixes p q :: "'a :: {ring_char_0,idom} poly"
  shows "poly_x_minus_y p = poly_x_minus_y q \<longleftrightarrow> p = q" (is "?p = ?q \<longleftrightarrow> _")
proof(intro iffI poly_ext)
  fix x
  assume "?p = ?q"
  then have "poly2 ?p x 0 = poly2 ?q x 0" by auto
  then show "poly p x = poly q x" by auto
qed auto

lemma poly_add:
  fixes p q :: "'a ::comm_ring_1 poly"
  assumes q0: "q \<noteq> 0" and x: "poly p x = 0" and y: "poly q y = 0"
  shows "poly (poly_add p q) (x+y) = 0"
proof (unfold poly_add_def, rule poly_resultant_zero[OF disjI2])
  have "degree q > 0" using poly_zero q0 y by auto
  thus degq: "degree (poly_lift q) > 0" by auto
qed (insert x y, simp_all)


subsubsection {* @{const poly_add} is nonzero *}

text {*
  We first prove that @{const poly_lift} preserves factorization. The result will be essential
  also in the next section for division of algebraic numbers.
 *}


interpretation poly_y_x_hom:
  bijective "poly_y_x :: 'a :: {idom,ring_char_0} poly poly \<Rightarrow> 'a poly poly"
  by(unfold bijective_eq_bij, rule id_imp_bij, auto intro!: poly2_ext)

interpretation poly_y_x_hom:
  idom_isom "poly_y_x :: 'a :: {idom,ring_char_0} poly poly \<Rightarrow> 'a poly poly"
  by (unfold_locales, rule poly2_ext, auto)

interpretation poly_lift_hom:
  unit_preserving_hom "poly_lift :: 'a :: {idom,ring_char_0} poly \<Rightarrow> _"
proof
  fix x :: "'a poly"
  assume "poly_lift x dvd 1"
  then have "poly_y_x (poly_lift x) dvd poly_y_x 1"
    by simp
  then have "monom x 0 dvd poly_y_x 1"
    by (simp add: poly_y_x_poly_lift)
  then show "x dvd 1"
    by (simp add: monom_0)
qed

interpretation poly_lift_hom:
  factor_preserving_hom "poly_lift::'a::{idom,ring_char_0} poly \<Rightarrow> 'a poly poly"
proof unfold_locales
  fix p :: "'a poly"
  assume p: "irreducible p"
  show "irreducible (poly_lift p)"
  proof(rule ccontr)
    from p have p0: "p \<noteq> 0" and "\<not> p dvd 1" by (auto dest: irreducible_not_unit)
    with poly_lift_hom.hom_dvd[of p 1] have p1: "\<not> poly_lift p dvd 1" by auto
    assume "\<not> irreducible (poly_lift p)"
    from this[unfolded irreducible_altdef,simplified] p0 p1
    obtain q where "q dvd poly_lift p" and pq: "\<not> poly_lift p dvd q" and q: "\<not> q dvd 1" by auto
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
    from irreducibleD'[OF p this] sq q pq show False by auto
  qed
qed

text {*
  We now show that @{const poly_x_minus_y} is a factor-preserving homomorphism. This is
  essential for this section. This is easy since @{const poly_x_minus_y} can be represented
  as the composition of two factor-preserving homomorphisms.
*}

lemma poly_x_minus_y_as_comp: "poly_x_minus_y = (\<lambda>p. p \<circ>\<^sub>p x_y) \<circ> poly_lift"
  by (intro ext, unfold poly_x_minus_y_def, auto)

interpretation poly_x_minus_y_hom:
  factor_preserving_hom "poly_x_minus_y :: 'a :: field_char_0 poly \<Rightarrow> 'a poly poly"
proof-
  interpret x_y_hom: bijective "\<lambda>p :: 'a poly poly. p \<circ>\<^sub>p x_y"
  proof (unfold bijective_eq_bij, rule id_imp_bij)
    fix p :: "'a poly poly" show "p \<circ>\<^sub>p x_y \<circ>\<^sub>p x_y = p" by (induct p, auto simp: pcompose_smult)
  qed
  interpret x_y_hom: idom_isom "\<lambda>p :: 'a poly poly. p \<circ>\<^sub>p x_y" by (unfold_locales, auto)
  show "factor_preserving_hom (poly_x_minus_y :: 'a poly \<Rightarrow> _)"
    by (unfold poly_x_minus_y_as_comp, rule factor_preserving_hom_comp, unfold_locales)
qed

text {*
  Now we show that results of @{const poly_x_minus_y} and @{const poly_lift} are coprime.
*}
context begin

private abbreviation "y_x == [: [: 0, -1 :], 1 :]"

private lemma poly2_y_x[simp]: fixes x :: "'a :: comm_ring_1" shows "poly2 y_x x y = y - x"
  unfolding poly2_def by simp

private definition "poly_y_minus_x p \<equiv> poly_lift p \<circ>\<^sub>p y_x"

private lemma poly_y_minus_x_0: "poly_y_minus_x 0 = 0" by (simp add: poly_y_minus_x_def)

private lemma poly_y_minus_x_pCons:
  "poly_y_minus_x (pCons a p) = [:[: a :]:] + poly_y_minus_x p * y_x" by (simp add: poly_y_minus_x_def)

private lemma poly_poly_y_minus_x:
  fixes p :: "'a :: comm_ring_1 poly"
  shows "poly (poly (poly_y_minus_x p) q) x = poly p (poly q x - x)"
  by (induct p; simp add: ring_distribs poly_y_minus_x_pCons poly_y_minus_x_0)

private lemma poly2_poly_y_minus_x:
  fixes p :: "'a :: comm_ring_1 poly"
  shows "poly2 (poly_y_minus_x p) x y = poly p (y - x)"
  by (simp add: ring_distribs poly2_def poly_poly_y_minus_x)

private lemma poly_y_x_poly_x_minus_y:
  fixes p :: "'a :: {idom, ring_char_0} poly"
  shows "poly_y_x (poly_x_minus_y p) = poly_y_minus_x p" by (intro poly2_ext, simp add: poly2_poly_y_minus_x)

lemma degree_poly_y_minus_x[simp]:
  fixes p :: "'a :: {idom, ring_char_0} poly"
  shows "degree (poly_y_x (poly_x_minus_y p)) = degree p" by (simp add: poly_y_minus_x_def poly_y_x_poly_x_minus_y)

end

lemma coprime_poly_x_minus_y_poly_lift:
  fixes p q :: "'a :: field_char_0 poly"
  assumes degp: "degree p > 0" and degq: "degree q > 0"
  shows "coprime (poly_x_minus_y p) (poly_lift q)"
proof(rule ccontr)
  from degp have p: "\<not> p dvd 1" by (auto simp: dvd_const)
  from degp have p0: "p \<noteq> 0" by auto
  from mset_factors_exist[of p, OF p0 p]
  obtain F where F: "mset_factors F p" by auto
  with poly_x_minus_y_hom.hom_mset_factors
  have pF: "mset_factors (image_mset poly_x_minus_y F) (poly_x_minus_y p)" by auto

  from degq have q: "\<not> is_unit q" by (auto simp: dvd_const)
  from degq have q0: "q \<noteq> 0" by auto
  from mset_factors_exist[OF q0 q]
  obtain G where G: "mset_factors G q" by auto
  with poly_lift_hom.hom_mset_factors
  have pG: "mset_factors (image_mset poly_lift G) (poly_lift q)" by auto

  assume "\<not> coprime (poly_x_minus_y p) (poly_lift q)"
  from this[unfolded not_coprime_iff_common_factor]
  obtain r
  where rp: "r dvd (poly_x_minus_y p)"
    and rq: "r dvd (poly_lift q)"
    and rU: "\<not> r dvd 1" by auto note poly_lift_hom.hom_dvd
  from rp p0 have r0: "r \<noteq> 0" by auto
  from mset_factors_exist[OF r0 rU]
  obtain H where H: "mset_factors H r" by auto
  then have "H \<noteq> {#}" by auto
  then obtain h where hH: "h \<in># H" by fastforce
  with H mset_factors_imp_dvd have hr: "h dvd r" and h: "irreducible h" by auto
  from irreducible_not_unit[OF h] have hU: "\<not> h dvd 1" by auto
  from hr rp have "h dvd (poly_x_minus_y p)" by (rule dvd_trans)
  from irreducible_dvd_imp_factor[OF this h pF] p0
  obtain f where f: "f \<in># F" and fh: "poly_x_minus_y f ddvd h" by auto
  from hr rq have "h dvd (poly_lift q)" by (rule dvd_trans)
  from irreducible_dvd_imp_factor[OF this h pG] q0
  obtain g where g: "g \<in># G" and gh: "poly_lift g ddvd h" by auto
  from fh gh have "poly_x_minus_y f ddvd poly_lift g" using ddvd_trans by auto
  then have "poly_y_x (poly_x_minus_y f) ddvd poly_y_x (poly_lift g)" by simp
  also have "poly_y_x (poly_lift g) = [:g:]" unfolding poly_y_x_poly_lift monom_0 by auto
  finally have ddvd: "poly_y_x (poly_x_minus_y f) ddvd [:g:]" by auto
  then have "degree (poly_y_x (poly_x_minus_y f)) = 0" by (metis degree_pCons_0 dvd_0_left_iff dvd_const)
  then have "degree f = 0" by simp
  then obtain i where fi: "f = [:i:]" by (auto dest: degree0_coeffs)
  with F f irreducible_const_poly_iff have "irreducible i" by (auto elim!: mset_factorsE)
  then show False by auto
qed

lemma poly_add_nonzero:
  fixes p q :: "'a :: field_char_0 poly"
  assumes p0: "p \<noteq> 0" and q0: "q \<noteq> 0" and x: "poly p x = 0" and y: "poly q y = 0"
  shows "poly_add p q \<noteq> 0"
proof
  have degp: "degree p > 0" using le_0_eq order_degree order_root p0 x by (metis gr0I)
  have degq: "degree q > 0" using le_0_eq order_degree order_root q0 y by (metis gr0I)
  assume 0: "poly_add p q = 0"
  from resultant_zero_imp_common_factor[OF _ this[unfolded poly_add_def]] degp
   and coprime_poly_x_minus_y_poly_lift[OF degp degq]
  show False by auto
qed


subsubsection \<open>Summary for addition\<close>

text {* Now we lift the results to one that uses @{const ipoly}, by showing some homomorphism lemmas. *}

lemma (in comm_ring_hom) map_poly_x_minus_y:
  "map_poly (map_poly hom) (poly_x_minus_y p) = poly_x_minus_y (map_poly hom p)"
proof-
  interpret mp: map_poly_comm_ring_hom hom..
  interpret mmp: map_poly_comm_ring_hom "map_poly hom"..
  show ?thesis by (induct p; simp)
qed

lemma (in comm_ring_hom) poly_lift_hom[simp]:
  "map_poly (map_poly hom) (poly_lift q) = poly_lift (map_poly hom q)"
proof -
  show ?thesis
    unfolding poly_lift_def
    unfolding map_poly_map_poly[of coeff_lift,OF coeff_lift_hom.hom_zero]
    unfolding map_poly_coeff_lift_hom by simp
qed

lemma (in inj_comm_ring_hom) poly_add_hom:
  "map_poly hom (poly_add p q) = poly_add (map_poly hom p) (map_poly hom q)"
proof -
  have zero: "\<forall>x. hom x = 0 \<longrightarrow> x = 0" by simp
  interpret mh: map_poly_inj_comm_ring_hom..
  show ?thesis unfolding poly_add_def mh.resultant_hom[symmetric]
    by (simp add: map_poly_x_minus_y)
qed

lemma ipoly_poly_add:
  assumes "q \<noteq> 0" and "ipoly p x = 0" and "ipoly q y = 0"
  shows "ipoly (poly_add p q) (x+y) = 0"
  by (unfold of_int_hom.poly_add_hom, rule poly_add, insert assms, auto)

lemma ipoly_poly_add_nonzero:
  fixes x y :: "'a :: field_char_0"
  assumes "p \<noteq> 0" and "q \<noteq> 0" and "ipoly p x = 0" and "ipoly q y = 0"
  shows "poly_add p q \<noteq> 0"
proof-
  from assms have "(of_int_poly (poly_add p q) :: 'a poly) \<noteq> 0"
    by (unfold of_int_hom.poly_add_hom, intro poly_add_nonzero, auto)
  then show ?thesis by auto
qed

lemma represents_add:
  fixes x y :: "'a :: field_char_0"
  assumes x: "p represents x" and y: "q represents y"
  shows "(poly_add p q) represents (x + y)"
  using x y by (intro representsI ipoly_poly_add ipoly_poly_add_nonzero, auto)

subsection \<open>Division of Algebraic Numbers\<close>

definition poly_x_mult_y where
  [code del]: "poly_x_mult_y p \<equiv> (\<Sum> i \<le> degree p. monom (monom (coeff p i) i) i)"

lemma coeff_poly_x_mult_y:
  shows "coeff (poly_x_mult_y p) i = monom (coeff p i) i" (is "?l = ?r")
proof(cases "degree p < i")
  case i: False
  have "?l = sum (\<lambda>j. if j = i then (monom (coeff p j) j) else 0) {..degree p}"
   (is "_ = sum ?f ?A") by (simp add: poly_x_mult_y_def coeff_sum)
  also have "... = sum ?f {i}" using i by (intro sum.mono_neutral_right, auto)
  also have "... = ?f i" by simp
  also have "... = ?r" by auto
  finally show ?thesis.
next
  case True then show ?thesis by (auto simp: poly_x_mult_y_def coeff_eq_0 coeff_sum)
qed

lemma poly_x_mult_y_code[code]: "poly_x_mult_y p = (let cs = coeffs p
  in poly_of_list (map (\<lambda> (i, ai). monom ai i) (zip [0 ..< length cs] cs)))" 
  unfolding Let_def poly_of_list_def 
proof (rule poly_eqI, unfold coeff_poly_x_mult_y)
  fix n
  let ?xs = "zip [0..<length (coeffs p)] (coeffs p)" 
  let ?f = "(\<lambda>(i, ai). monom ai i)" 
  show "monom (coeff p n) n = coeff (Poly (map ?f ?xs)) n" 
  proof (cases "n < length (coeffs p)")
    case True
    hence n: "n < length (map ?f ?xs)" and nn: "n < length ?xs" 
      unfolding degree_eq_length_coeffs by auto
    show ?thesis unfolding coeff_Poly nth_default_nth[OF n] nth_map[OF nn]
      using True by (simp add: nth_coeffs_coeff)
  next
    case False
    hence id: "coeff (Poly (map ?f ?xs)) n = 0" unfolding coeff_Poly
      by (subst nth_default_beyond, auto)
    from False have "n > degree p \<or> p = 0" unfolding degree_eq_length_coeffs by (cases n, auto)
    hence "monom (coeff p n) n = 0" using coeff_eq_0[of p n] by auto
    thus ?thesis unfolding id by simp
  qed
qed

definition poly_div :: "'a :: comm_ring_1 poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "poly_div p q = resultant (poly_x_mult_y p) (poly_lift q)"

text {* @{const poly_div} has desired roots. *}

lemma poly2_poly_x_mult_y:
  fixes p :: "'a :: comm_ring_1 poly"
  shows "poly2 (poly_x_mult_y p) x y = poly p (x * y)"
  apply (subst(3) poly_as_sum_of_monoms[symmetric])
  by (auto simp: poly_x_mult_y_def poly2_monom poly_monom power_mult_distrib ac_simps)

lemma poly_div:
  fixes p q :: "'a ::field poly"
  assumes q0: "q \<noteq> 0" and x: "poly p x = 0" and y: "poly q y = 0" and y0: "y \<noteq> 0"
  shows "poly (poly_div p q) (x/y) = 0"
proof (unfold poly_div_def, rule poly_resultant_zero[OF disjI2])
  have "degree q > 0" using poly_zero q0 y by auto
  thus degq: "degree (poly_lift q) > 0" by auto
qed (insert x y y0, simp_all add: poly2_poly_x_mult_y)


text {* @{const poly_div} is nonzero. *}

interpretation poly_x_mult_y_hom: ring_hom "poly_x_mult_y :: 'a :: {idom,ring_char_0} poly \<Rightarrow> _"
  by (unfold_locales, auto intro: poly2_ext simp: poly2_poly_x_mult_y)

interpretation poly_x_mult_y_hom: inj_ring_hom "poly_x_mult_y :: 'a :: {idom,ring_char_0} poly \<Rightarrow> _"
proof
  let ?h = poly_x_mult_y
  fix f :: "'a poly"
  assume "?h f = 0"
  then have "poly2 (?h f) x 1 = 0" for x by simp
  from this[unfolded poly2_poly_x_mult_y]
  show "f = 0" by auto
qed

lemma degree_poly_x_mult_y[simp]:
  fixes p :: "'a :: {idom, ring_char_0} poly"
  shows "degree (poly_x_mult_y p) = degree p" (is "?l = ?r")
proof(rule antisym)
  show "?r \<le> ?l" by (cases "p=0", auto intro: le_degree simp: coeff_poly_x_mult_y)
  show "?l \<le> ?r" unfolding poly_x_mult_y_def
    by (auto intro: degree_sum_le le_trans[OF degree_monom_le])
qed

interpretation poly_x_mult_y_hom: unit_preserving_hom "poly_x_mult_y :: 'a :: field_char_0 poly \<Rightarrow> _"
proof(unfold_locales)
  let ?h = "poly_x_mult_y :: 'a poly \<Rightarrow> _"
  fix f :: "'a poly"
  assume unit: "?h f dvd 1"
  then have "degree (?h f) = 0" and "coeff (?h f) 0 dvd 1" unfolding poly_dvd_1 by auto
  then have deg: "degree f = 0" by (auto simp add: degree_monom_eq)
  with unit show "f dvd 1" by(cases "f = 0", auto)
qed

lemmas poly_y_x_o_poly_lift = o_def[of poly_y_x poly_lift, unfolded poly_y_x_poly_lift]

lemma coprime_poly_x_mult_y_poly_lift:
  fixes p q :: "'a :: field_char_0 poly"
  assumes degp: "degree p > 0" and degq: "degree q > 0" and p_0: "poly p 0 \<noteq> 0"
  shows "coprime (poly_x_mult_y p) (poly_lift q)"
proof(rule ccontr)
  from degp have p: "\<not> p dvd 1" by (auto simp: dvd_const)
  from degp have p0: "p \<noteq> 0" by auto
  from mset_factors_exist[of p, OF p0 p]
  obtain F where F: "mset_factors F p" by auto
  then have pF: "prod_mset (image_mset poly_x_mult_y F) = poly_x_mult_y p" by auto

  from degq have q: "\<not> is_unit q" by (auto simp: dvd_const)
  from degq have q0: "q \<noteq> 0" by auto
  from mset_factors_exist[OF q0 q]
  obtain G where G: "mset_factors G q" by auto
  with poly_lift_hom.hom_mset_factors
  have pG: "mset_factors (image_mset poly_lift G) (poly_lift q)" by auto
  from poly_y_x_hom.hom_mset_factors[OF this]
  have pG: "mset_factors (image_mset coeff_lift G) [:q:]"
    by (auto simp: poly_y_x_poly_lift monom_0 image_mset.compositionality poly_y_x_o_poly_lift)

  assume "\<not> coprime (poly_x_mult_y p) (poly_lift q)"
  then have "\<not> coprime (poly_y_x (poly_x_mult_y p)) (poly_y_x (poly_lift q))"
    by simp
  from this[unfolded not_coprime_iff_common_factor]
  obtain r
  where rp: "r dvd poly_y_x (poly_x_mult_y p)"
    and rq: "r dvd poly_y_x (poly_lift q)"
    and rU: "\<not> r dvd 1" by auto
  from rp p0 have r0: "r \<noteq> 0" by auto
  from mset_factors_exist[OF r0 rU]
  obtain H where H: "mset_factors H r" by auto
  then have "H \<noteq> {#}" by auto
  then obtain h where hH: "h \<in># H" by fastforce
  with H mset_factors_imp_dvd have hr: "h dvd r" and h: "irreducible h" by auto
  from irreducible_not_unit[OF h] have hU: "\<not> h dvd 1" by auto
  from hr rp have "h dvd poly_y_x (poly_x_mult_y p)" by (rule dvd_trans)
  note this[folded pF,simplified]
  from prime_elem_dvd_prod_mset[OF h[folded prime_elem_iff_irreducible] this]
  obtain f where f: "f \<in># F" and hf: "h dvd poly_y_x (poly_x_mult_y f)" by auto
  from F f p_0 have f_0: "poly f 0 \<noteq> 0" by auto

  from dvd_trans[OF hr rq] have "h dvd [:q:]" by (simp add: poly_y_x_poly_lift monom_0)
  from irreducible_dvd_imp_factor[OF this h pG] q0
  obtain g where g: "g \<in># G" and gh: "[:g:] dvd h" by auto
  from dvd_trans[OF gh hf] have "[:g:] dvd poly_y_x (poly_x_mult_y f)" using dvd_trans by auto
  from poly_hom.hom_dvd[OF this]
  have *: "g dvd poly (poly_y_x (poly_x_mult_y f)) [:0:]" by simp
  also have "... = [:poly f 0:]" by (intro poly_ext, fold poly2_def, simp add: poly2_poly_x_mult_y)
  also have "... dvd 1" using f_0 by auto
  finally have "g dvd 1".
  with g G show False by (auto elim!: mset_factorsE dest!: irreducible_not_unit)
qed

lemma poly_div_nonzero:
  fixes p q :: "'a :: field_char_0 poly"
  assumes p0: "p \<noteq> 0" and q0: "q \<noteq> 0" and x: "poly p x = 0" and y: "poly q y = 0"
      and p_0: "poly p 0 \<noteq> 0"
  shows "poly_div p q \<noteq> 0"
proof
  have degp: "degree p > 0" using le_0_eq order_degree order_root p0 x by (metis gr0I)
  have degq: "degree q > 0" using le_0_eq order_degree order_root q0 y by (metis gr0I)
  assume 0: "poly_div p q = 0"
  from resultant_zero_imp_common_factor[OF _ this[unfolded poly_div_def]] degp
   and coprime_poly_x_mult_y_poly_lift[OF degp degq] p_0
  show False by auto
qed

subsubsection \<open>Summary for division\<close>

text {* Now we lift the results to one that uses @{const ipoly}, by showing some homomorphism lemmas. *}

lemma (in inj_comm_ring_hom) poly_x_mult_y_hom:
  "poly_x_mult_y (map_poly hom p) = map_poly (map_poly hom) (poly_x_mult_y p)"
proof -
  interpret mh: map_poly_inj_comm_ring_hom..
  interpret mmh: map_poly_inj_comm_ring_hom "map_poly hom"..
  show ?thesis unfolding poly_x_mult_y_def by simp
qed

lemma (in inj_comm_ring_hom) poly_div_hom:
  "map_poly hom (poly_div p q) = poly_div (map_poly hom p) (map_poly hom q)"
proof -
  have zero: "\<forall>x. hom x = 0 \<longrightarrow> x = 0" by simp
  interpret mh: map_poly_inj_comm_ring_hom..
  show ?thesis unfolding poly_div_def mh.resultant_hom[symmetric]
    by (simp add: poly_x_mult_y_hom)
qed

lemma ipoly_poly_div:
  assumes "q \<noteq> 0" and "ipoly p x = 0" and "ipoly q y = 0" and "y \<noteq> 0"
  shows "ipoly (poly_div p q) (x/y) = 0"
  by (unfold of_int_hom.poly_div_hom, rule poly_div, insert assms, auto)

lemma ipoly_poly_div_nonzero:
  fixes x y :: "'a :: field_char_0"
  assumes "p \<noteq> 0" and "q \<noteq> 0" and "ipoly p x = 0" and "ipoly q y = 0" and "poly p 0 \<noteq> 0"
  shows "poly_div p q \<noteq> 0"
proof-
  from assms have "(of_int_poly (poly_div p q) :: 'a poly) \<noteq> 0" using of_int_hom.poly_map_poly[of p]
    by (subst of_int_hom.poly_div_hom, subst poly_div_nonzero, auto) 
  then show ?thesis by auto
qed

lemma represents_div:
  fixes x y :: "'a :: field_char_0"
  assumes "p represents x" and "q represents y" and "poly p 0 \<noteq> 0" and "y \<noteq> 0"
  shows "(poly_div p q) represents (x / y)"
  using assms by (intro representsI ipoly_poly_div ipoly_poly_div_nonzero, auto)




subsection \<open>Multiplication of Algebraic Numbers\<close>

definition poly_mult where "poly_mult p q \<equiv> poly_div p (poly_inverse q)"

lemma represents_mult:
  assumes px: "p represents x" and qy: "q represents y" and p_0: "poly p 0 \<noteq> 0" and y0: "y \<noteq> 0"
  shows "(poly_mult p q) represents (x * y)"
proof-
  from represents_inverse[OF y0 qy] y0 px p_0
  have "poly_mult p q represents x / (inverse y)"
    unfolding poly_mult_def by (intro represents_div, auto)
  with y0 show ?thesis by (simp add: field_simps)
qed

subsection \<open>Summary: Closure Properties of Algebraic Numbers\<close>

lemma algebraic_representsI: "p represents x \<Longrightarrow> algebraic x"
  unfolding represents_def algebraic_altdef_ipoly by auto

lemma algebraic_of_rat: "algebraic (of_rat x)"
  by (rule algebraic_representsI[OF poly_rat_represents_of_rat])

lemma algebraic_uminus: "algebraic x \<Longrightarrow> algebraic (-x)"
  by (auto dest: algebraic_imp_represents_irreducible intro: algebraic_representsI represents_uminus)

lemma algebraic_inverse: "algebraic x \<Longrightarrow> algebraic (inverse x)"
  using algebraic_of_rat[of 0]
  by (cases "x = 0", auto dest: algebraic_imp_represents_irreducible intro: algebraic_representsI represents_inverse)

lemma algebraic_plus: "algebraic x \<Longrightarrow> algebraic y \<Longrightarrow> algebraic (x + y)"
  by (auto dest: algebraic_imp_represents_irreducible intro: algebraic_representsI[OF represents_add])

lemma algebraic_div:
  assumes x: "algebraic x" and y: "algebraic y" shows "algebraic (x/y)"
proof(cases "y = 0 \<or> x = 0")
  case True
  then show ?thesis using algebraic_of_rat[of 0] by auto
next
  case False
  then have x0: "x \<noteq> 0" and y0: "y \<noteq> 0" by auto
  from x y obtain p q
  where px: "p represents x" and p: "irreducible p" and qy: "q represents y"
    by (auto dest!: algebraic_imp_represents_irreducible)
  show ?thesis
    using False px represents_irr_non_0[OF p px]
    by (auto intro!: algebraic_representsI[OF represents_div[OF px qy]])
qed

lemma algebraic_times: "algebraic x \<Longrightarrow> algebraic y \<Longrightarrow> algebraic (x * y)"
  using algebraic_div[OF _ algebraic_inverse, of x y] by (simp add: field_simps)

lemma algebraic_root: "algebraic x \<Longrightarrow> algebraic (root n x)"
proof -
  assume "algebraic x"
  then obtain p where p: "p represents x" by (auto dest: algebraic_imp_represents_irreducible_cf_pos)
  from 
    algebraic_representsI[OF represents_nth_root_neg_real[OF _ this, of n]]
    algebraic_representsI[OF represents_nth_root_pos_real[OF _ this, of n]]
    algebraic_of_rat[of 0]
  show ?thesis by (cases "n = 0", force, cases "n > 0", force, cases "n < 0", auto)
qed

lemma algebraic_nth_root: "n \<noteq> 0 \<Longrightarrow> algebraic x \<Longrightarrow> y^n = x \<Longrightarrow> algebraic y"
  by (auto dest: algebraic_imp_represents_irreducible_cf_pos intro: algebraic_representsI represents_nth_root)

hide_const x_y

end
