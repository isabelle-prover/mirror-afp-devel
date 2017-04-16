(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Connecting Polynomials with Homomorphism Locales\<close>

theory Ring_Hom_Poly
imports 
  "~~/src/HOL/Computational_Algebra/Euclidean_Algorithm"
  Ring_Hom
  Missing_Polynomial
  Rat
begin

text{* @{term poly} as a homomorphism. Note that types differ. *}

interpretation poly_hom: comm_semiring_hom "\<lambda>p. poly p a" by (unfold_locales, auto)

interpretation poly_hom: comm_ring_hom "\<lambda>p. poly p a" by (unfold_locales, auto)

interpretation poly_hom: idom_hom "\<lambda>p. poly p a" by (unfold_locales, auto)

text {* @{term "op \<circ>\<^sub>p"} as a homomorphism. *}

interpretation pcompose_hom: comm_semiring_hom "\<lambda>q. q \<circ>\<^sub>p p"
  using pcompose_add pcompose_mult pcompose_1 by (unfold_locales, auto)

interpretation pcompose_hom: comm_ring_hom "\<lambda>q. q \<circ>\<^sub>p p"
  using pcompose_1 by (unfold_locales, auto)

interpretation pcompose_hom: idom_hom "\<lambda>q. q \<circ>\<^sub>p p"
  using pcompose_add pcompose_mult pcompose_1 pcompose_uminus by (unfold_locales, auto)



definition eval_poly :: "('a \<Rightarrow> 'b :: comm_semiring_1) \<Rightarrow> 'a :: zero poly \<Rightarrow> 'b \<Rightarrow> 'b" where
  [code del]: "eval_poly h p = poly (map_poly h p)"

lemma eval_poly_code[code]: "eval_poly h p x = fold_coeffs (\<lambda> a b. h a + x * b) p 0" 
  by (induct p, auto simp: eval_poly_def)

lemma eval_poly_as_sum:
  fixes h :: "'a :: zero \<Rightarrow> 'b :: comm_semiring_1"
  assumes "h 0 = 0"
  shows "eval_poly h p x = (\<Sum>i\<le>degree p. x^i * h (coeff p i))"
  unfolding eval_poly_def
proof (induct p)
  case 0 show ?case using assms by simp
  next case (pCons a p) thus ?case
    proof (cases "p = 0")
      case True show ?thesis by (simp add: True map_poly_simps assms)
      next case False show ?thesis
        unfolding degree_pCons_eq[OF False]
        unfolding sum_atMost_Suc_shift
        unfolding map_poly_pCons[OF pCons(1)]
        by (simp add: pCons(2) sum_distrib_left mult.assoc)
  qed
qed

lemma coeff_const: "coeff [: a :] i = (if i = 0 then a else 0)"
  by (metis coeff_monom monom_0)

lemma x_as_monom: "[:0,1:] = monom 1 1"
  by (simp add: monom_0 monom_Suc)

lemma x_pow_n: "(monom 1 1)^n = monom 1 n"
  by (induct n, auto simp: one_poly_def monom_0 monom_Suc)

lemma map_poly_eval_poly: assumes h0: "h 0 = 0"
  shows "map_poly h p = eval_poly (\<lambda> a. [: h a :]) p [:0,1:]" (is "?mp = ?ep")
proof (rule poly_eqI)
  fix i :: nat
  have 2: "(\<Sum>x\<le>i. \<Sum>xa\<le>degree p. (if xa = x then 1 else 0) * coeff [:h (coeff p xa):] (i - x)) 
    = h (coeff p i)" (is "sum ?f ?s = ?r")
  proof -
    have "sum ?f ?s = ?f i + sum ?f ({..i} - {i})"
      by (rule sum.remove[of _ i], auto)
    also have "sum ?f ({..i} - {i}) = 0"
      by (rule sum.neutral, intro ballI, rule sum.neutral, auto simp: coeff_const)
    also have "?f i = (\<Sum>xa\<le>degree p. (if xa = i then 1 else 0) * h (coeff p xa))" (is "_ = ?m")
      unfolding coeff_const by simp
    also have "\<dots> = ?r"
    proof (cases "i \<le> degree p")
      case True
      show ?thesis
        by (subst sum.remove[of _ i], insert True, auto)
    next
      case False
      hence [simp]: "coeff p i = 0" using le_degree by blast
      show ?thesis
        by (subst sum.neutral, auto simp: h0)
    qed
    finally show ?thesis by simp
  qed
  have h'0: "[: h 0 :] = 0" using h0 by auto
  show "coeff ?mp i = coeff ?ep i"
    unfolding coeff_map_poly[of h, OF h0]
    unfolding eval_poly_as_sum[of "\<lambda>a. [: h a :]", OF h'0]
    unfolding coeff_sum
    unfolding x_as_monom x_pow_n coeff_mult
    unfolding sum.commute[of _ _ "{..degree p}"]
    unfolding coeff_monom using 2 by auto
qed

lemma map_poly_eqI: assumes f: "\<And> x. x \<in> set (coeffs p) \<Longrightarrow> f x = x" and f0: "f 0 = 0"
  shows "map_poly f p = p"
proof (rule poly_eqI)
  fix i
  show "coeff (map_poly f p) i = coeff p i" using f[of "coeff p i"] f0
    unfolding coeff_map_poly[of f p i, OF f0] using range_coeff[of p]
    by (cases "coeff p i \<in> set (coeffs p)", force+)
qed

lemma smult_map_poly: "smult a = map_poly (op * a)"
  by (rule ext, rule poly_eqI, subst coeff_map_poly, auto)

context comm_semiring_hom
begin
  lemma map_poly_hom_monom[hom_distribs,simp]: "map_poly hom (monom a i) = monom (hom a) i"
    by(rule map_poly_monom,auto)
  lemma map_poly_hom_smult[simp,hom_distribs]:
    "map_poly hom (smult c p) = smult (hom c) (map_poly hom p)"
  proof(induct p)
    case (pCons a p)
      show ?case
        unfolding map_poly_pCons[OF pCons(1)]
        unfolding smult_pCons
        unfolding pCons(2)[symmetric]
        unfolding map_poly_simps
        by (auto intro: hom_mult_eq_zero)
  qed auto
  lemma map_poly_hom_1[simp,hom_removes]: "map_poly hom 1 = 1" by (simp add: one_poly_def)
  lemma map_poly_hom_add[hom_distribs,simp]:
    "map_poly hom (p + q) = map_poly hom p + map_poly hom q"
    by (rule map_poly_add;simp)
  lemma map_poly_hom_mult[hom_distribs,simp]:
    "map_poly hom (p * q) = map_poly hom p * map_poly hom q"
  proof (induct p)
    case (pCons a p) thus ?case
      proof(cases "p * q = 0")
        case True thus ?thesis using pCons by simp
        next case False thus ?thesis
        unfolding mult_pCons_left
        unfolding map_poly_add
        unfolding map_poly_pCons[OF pCons(1)]
        using pCons(2) by simp
      qed
  qed auto
end

context comm_semiring begin
  lemma map_poly_inj:
    assumes id: "map_poly f p = map_poly f q"
        and f: "\<And> x y. f x = f y \<Longrightarrow> x = y"
        and f0: "f 0 = 0"
    shows "p = q"
    using f[OF arg_cong[OF id, of "\<lambda> p. coeff p i" for i, unfolded coeff_map_poly[of f, OF f0]]]
    by (rule poly_eqI)
end

locale map_poly_comm_semiring_hom = base: comm_semiring_hom
begin
  sublocale comm_semiring_hom "map_poly hom" by (unfold_locales, auto)
end

locale map_poly_comm_ring_hom = base: comm_ring_hom
begin
  sublocale map_poly_comm_semiring_hom..
  sublocale comm_ring_hom "map_poly hom"..
end

locale map_poly_idom_hom = base: idom_hom
begin
  sublocale map_poly_comm_ring_hom..
  sublocale idom_hom "map_poly hom"..
end

locale map_poly_inj_comm_semiring_hom = base: inj_comm_semiring_hom
begin
  sublocale map_poly_comm_semiring_hom..
  sublocale inj_semiring_hom "map_poly hom" by (unfold_locales, auto intro: map_poly_inj)
end

locale map_poly_inj_comm_ring_hom = base: inj_comm_ring_hom
begin
  sublocale map_poly_inj_comm_semiring_hom..
  sublocale inj_comm_ring_hom "map_poly hom"..
end

locale map_poly_inj_idom_hom = base: inj_idom_hom
begin
  sublocale map_poly_inj_comm_ring_hom..
  sublocale inj_idom_hom "map_poly hom"..
end

context zero_hom begin

lemma coeff_map_poly_hom[simp]: "coeff (map_poly hom p) i = hom (coeff p i)"
  by (rule coeff_map_poly, rule hom_zero)
end

context comm_semiring_hom begin

interpretation map_poly_hom: map_poly_comm_semiring_hom..

lemma eval_poly_0[simp]: "eval_poly hom 0 x = 0" unfolding eval_poly_def by simp
lemma eval_poly_monom: "eval_poly hom (monom a n) x = hom a * x ^ n"
  unfolding eval_poly_def
  unfolding map_poly_monom[of hom, OF hom_zero] using poly_monom.

lemma poly_map_poly_eval_poly: "poly (map_poly hom p) = eval_poly hom p"
  unfolding eval_poly_def..

lemma map_poly_eval_poly: 
  "map_poly hom p = eval_poly (\<lambda> a. [: hom a :]) p [:0,1:]" 
  by (rule map_poly_eval_poly, simp)

lemma degree_extension: assumes "degree p \<le> n"
  shows "(\<Sum>i\<le>degree p. x ^ i * hom (coeff p i))
      = (\<Sum>i\<le>n. x ^ i * hom (coeff p i))" (is "?l = ?r")
proof -
  let ?f = "\<lambda> i. x ^ i * hom (coeff p i)"
  define m where "m = n - degree p"
  have n: "n = degree p + m" unfolding m_def using assms by auto
  have "?r = (\<Sum> i \<le> degree p + m. ?f i)" unfolding n ..
  also have "\<dots> = ?l + sum ?f {Suc (degree p) .. degree p + m}"
    by (subst sum.union_disjoint[symmetric], auto intro: sum.cong)
  also have "sum ?f {Suc (degree p) .. degree p + m} = 0"
    by (rule sum.neutral, auto simp: coeff_eq_0)
  finally show ?thesis by simp
qed

lemma poly_map_poly[simp]: "poly (map_poly hom p) (hom x) = hom (poly p x)"
  by (induct p,simp+)

lemma eval_poly_add[simp]: "eval_poly hom (p + q) x = eval_poly hom p x + eval_poly hom q x"
  unfolding eval_poly_def by simp

lemma eval_poly_sum: "eval_poly hom (\<Sum>k\<in>A. p k) x = (\<Sum>k\<in>A. eval_poly hom (p k) x)"
proof (induct A rule: infinite_finite_induct)
  case (insert a A)
  show ?case
    unfolding sum.insert[OF insert(1-2)] insert(3)[symmetric] by simp
qed (auto simp: eval_poly_def)

lemma eval_poly_poly: "eval_poly hom p (hom x) = hom (poly p x)"
  unfolding eval_poly_def by auto

lemma map_poly_pCons_hom[hom_distribs,simp]: "map_poly hom (pCons a p) = pCons (hom a) (map_poly hom p)"
  unfolding map_poly_simps by auto

lemma monom_hom: "monom (hom a) d = map_poly hom (monom a d)"
  apply(induct d) unfolding monom_0 apply simp
  unfolding monom_Suc by simp

lemma map_poly_hom_as_monom_sum:
  "(\<Sum>j\<le>degree p. monom (hom (coeff p j)) j) = map_poly hom p"
proof -
  interpret rhm: semiring_hom "map_poly hom" by(unfold_locales,auto)
  show ?thesis
    apply(subst(6) poly_as_sum_of_monoms'[OF le_refl, symmetric])
    using monom_hom by auto
qed

lemma map_poly_pcompose[hom_distribs]:
  "map_poly hom (f \<circ>\<^sub>p g) = map_poly hom f \<circ>\<^sub>p map_poly hom g"
  by (induct f arbitrary: g, auto)

lemma map_poly_single[simp]:
  "map_poly hom [:h:] = ([:hom h:])"
  unfolding map_poly_def fold_coeffs_def coeffs_def by simp

lemma map_poly_preserves_prod_list[simp]:
  "map_poly hom (prod_list x) = prod_list (map (map_poly hom) x)"
  by(induct x,auto simp:one_poly_def)

lemma map_poly_preserves_sum_list[simp]:
  "map_poly hom (sum_list x) = sum_list (map (map_poly hom) x)"
  by(induct x,auto simp:one_poly_def)    
end

lemma degree_map_poly_le: "degree (map_poly h p) \<le> degree p"
  by(induct p;auto)

lemma degree_map_poly:
  assumes h0: "h 0 = 0" and lead: "h (coeff p (degree p)) = 0 \<Longrightarrow> p = 0"
  shows "degree (map_poly h p) = degree p" (is "degree ?p = _")
proof (cases "p = 0")
  case True thus ?thesis by auto
  next case False
    hence "coeff ?p (degree p) \<noteq> 0" unfolding coeff_map_poly[of h, OF h0] using lead by auto
    hence "degree ?p \<ge> degree p" using le_degree by auto
    thus ?thesis using degree_map_poly_le[of h p] by auto
qed



lemma coeffs_map_poly:
  assumes h: "\<And> x. x \<in> range (coeff p) \<Longrightarrow> h x = 0 \<longleftrightarrow> x = 0"
  shows "coeffs (map_poly h p) = map h (coeffs p)"
proof -
  have h0: "h 0 = 0" using h by (auto simp: range_coeff)
  have deg: "degree (map_poly h p) = degree p"
    apply (rule degree_map_poly[of h, OF h0]) using h by auto
  show ?thesis
    unfolding coeffs_def deg using coeff_map_poly[of h, OF h0]
    by (auto simp: poly_eq_iff h)
qed

context zero_hom_0 begin
  lemma map_poly_0_iff[simp,hom_removes]: "map_poly hom p = 0 \<longleftrightarrow> p = 0"
    unfolding poly_eq_iff coeff_map_poly by auto
  lemma degree_map_poly[simp,hom_removes]: "degree (map_poly hom p) = degree p"
    by (rule degree_map_poly, auto)
  lemma coeffs_map_poly[simp]: "coeffs (map_poly hom p) = map hom (coeffs p)"
    by (rule coeffs_map_poly, auto)
  declare coeffs_map_poly[symmetric, hom_distribs]
  lemma hom_lead_coeff[simp]:
    "lead_coeff (map_poly hom p) = hom (lead_coeff p)"
    by simp
end

context inj_comm_ring_hom
begin

  interpretation map_poly_hom: map_poly_inj_comm_ring_hom..

  lemma pseudo_divmod_main_hom:
    "pseudo_divmod_main (hom lc) (map_poly hom q) (map_poly hom r) (map_poly hom d) dr i =
     map_prod (map_poly hom) (map_poly hom) (pseudo_divmod_main lc q r d dr i)"
    by (induct lc q r d dr i rule:pseudo_divmod_main.induct, auto simp: Let_def)

  lemma pseudo_divmod_hom:
    "pseudo_divmod (map_poly hom p) (map_poly hom q) =
     map_prod (map_poly hom) (map_poly hom) (pseudo_divmod p q)"
    unfolding pseudo_divmod_def using pseudo_divmod_main_hom[of _ 0] by (cases "q = 0",auto)

end

lemma(in inj_idom_hom) pseudo_mod_hom:
  "pseudo_mod (map_poly hom p) (map_poly hom q) = map_poly hom (pseudo_mod p q)"
  using pseudo_divmod_hom unfolding pseudo_mod_def by auto

lemma(in idom_hom) map_poly_pderiv[simp,hom_distribs]: "map_poly hom (pderiv p) = pderiv (map_poly hom p)"
proof (induct p rule: pderiv.induct)
  case (1 a p)
  then show ?case unfolding pderiv.simps map_poly_pCons_hom by (cases "p = 0", auto)
qed

context field_hom
begin

lemma map_poly_pdivmod[hom_distribs]:
  "map_prod (map_poly hom) (map_poly hom) (p div q, p mod q) =
    (map_poly hom p div map_poly hom q, map_poly hom p mod map_poly hom q)"
  (is "?l = ?r")
proof -
  let ?mp = "map_poly hom"
  obtain r s where dm: "(p div q, p mod q) = (r, s)"
    by force  
  hence r: "r = p div q" and s: "s = p mod q"
    by simp_all
  from dm [folded pdivmod_pdivmodrel] have "eucl_rel_poly p q (r, s)"
    by auto
  from this[unfolded eucl_rel_poly_iff]
  have eq: "p = r * q + s" and cond: "(if q = 0 then r = 0 else s = 0 \<or> degree s < degree q)" by auto
  from arg_cong[OF eq, of ?mp, unfolded map_poly_add]
  have eq: "?mp p = ?mp q * ?mp r + ?mp s" by auto
  from cond have cond: "(if ?mp q = 0 then ?mp r = 0 else ?mp s = 0 \<or> degree (?mp s) < degree (?mp q))"
    unfolding map_poly_0_iff degree_map_poly .
  from eq cond have "eucl_rel_poly (?mp p) (?mp q) (?mp r, ?mp s)"
    unfolding eucl_rel_poly_iff by auto
  from this[unfolded pdivmod_pdivmodrel]
  show ?thesis unfolding dm prod.simps by simp
qed

lemma map_poly_div[hom_distribs,simp]: "map_poly hom (p div q) = map_poly hom p div map_poly hom q"
  using map_poly_pdivmod[of p q] by simp

lemma map_poly_mod[hom_distribs,simp]: "map_poly hom (p mod q) = map_poly hom p mod map_poly hom q"
  using map_poly_pdivmod[of p q] by simp

end

locale field_hom' = field_hom hom
  for hom :: "'a :: {field,euclidean_ring_gcd} \<Rightarrow> 'b :: {field,euclidean_ring_gcd}"
begin

lemma map_poly_normalize[hom_distribs]: "map_poly hom (normalize p) = normalize (map_poly hom p)"
  by (simp add: normalize_poly_def)

lemma map_poly_gcd[hom_distribs]: "map_poly hom (gcd p q) = gcd (map_poly hom p) (map_poly hom q)"
  by (induct p q rule: eucl_induct)
    (simp_all add: map_poly_normalize ac_simps)

end

definition div_poly :: "'a :: semiring_div \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "div_poly a p = map_poly (\<lambda> c. c div a) p"

lemma smult_div_poly: assumes "\<And> c. c \<in> set (coeffs p) \<Longrightarrow> a dvd c"
  shows "smult a (div_poly a p) = p" 
  unfolding smult_map_poly div_poly_def 
  by (subst map_poly_map_poly, force, subst map_poly_idI, insert assms, auto)

lemma coeff_div_poly: "coeff (div_poly a f) n = coeff f n div a" 
  unfolding div_poly_def
  by (rule coeff_map_poly, auto)

lemma (in comm_semiring_hom) poly_map_poly_0[simp]:
  "poly (map_poly hom p) 0 = hom (poly p 0)" (is "?l = ?r")
proof-
  have "?l = poly (map_poly hom p) (hom 0)" by auto
  then show ?thesis unfolding poly_map_poly.
qed

lemma (in comm_semiring_hom) poly_map_poly_1[simp]:
  "poly (map_poly hom p) 1 = hom (poly p 1)" (is "?l = ?r")
proof-
  have "?l = poly (map_poly hom p) (hom 1)" by auto
  then show ?thesis unfolding poly_map_poly.
qed

locale zero_hom_0_map_poly = base: zero_hom_0
begin
  sublocale zero_hom_0 "map_poly hom" by (unfold_locales, auto)
end


subsection {* Example Interpretations *}

abbreviation "of_int_poly \<equiv> map_poly of_int"

interpretation of_int_poly_hom: map_poly_comm_semiring_hom of_int..
interpretation of_int_poly_hom: map_poly_comm_ring_hom of_int..
interpretation of_int_poly_hom: map_poly_idom_hom of_int..
interpretation of_int_poly_hom:
  map_poly_inj_comm_ring_hom "of_int :: int  \<Rightarrow> 'a :: {comm_ring_1,ring_char_0}" ..
interpretation of_int_poly_hom:
  map_poly_inj_idom_hom "of_int :: int  \<Rightarrow> 'a :: {idom,ring_char_0}" ..


end
