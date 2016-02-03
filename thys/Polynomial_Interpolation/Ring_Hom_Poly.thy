(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Connecting Polynomials with Homomorphism Locales\<close>

theory Ring_Hom_Poly
imports 
  Ring_Hom
  Missing_Polynomial
  Rat
begin

text{* @{term poly} as a homomorphism *}

interpretation poly_semiring_hom: semiring_hom "\<lambda>p. poly p a" by (unfold_locales; auto)

interpretation poly_ring_hom: ring_hom "\<lambda>p. poly p a" by (unfold_locales; auto)

text {* @{term "op \<circ>\<^sub>p"} as a homomorphism *}

locale ring_hom_pcompose =
  fixes p :: "'a :: {idom,ring_char_0} poly"
begin
  sublocale ring_hom "\<lambda>q. q \<circ>\<^sub>p p"
  using pcompose_add pcompose_mult pcompose_1 pcompose_uminus by (unfold_locales, auto)
end



lemma (in semiring_hom) map_poly_hom_monom[simp]: "map_poly hom (monom a i) = monom (hom a) i"
  by(rule map_poly_monom,auto)

definition eval_poly :: "('a \<Rightarrow> 'b :: comm_semiring_1) \<Rightarrow> 'a :: zero poly \<Rightarrow> 'b \<Rightarrow> 'b" where
  [code del]: "eval_poly h p = poly (map_poly h p)"

lemma eval_poly_code[code]: "eval_poly h p x = fold_coeffs (\<lambda> a b. h a + x * b) p 0" 
  by (induct p, auto simp: eval_poly_def)

lemma eval_poly_as_setsum:
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
        unfolding setsum_atMost_Suc_shift
        unfolding map_poly_pCons[OF pCons(1)]
        by (simp add: pCons(2) setsum_right_distrib mult.assoc)
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
    = h (coeff p i)" (is "setsum ?f ?s = ?r")
  proof -
    have "setsum ?f ?s = ?f i + setsum ?f ({..i} - {i})"
      by (rule setsum.remove[of _ i], auto)
    also have "setsum ?f ({..i} - {i}) = 0"
      by (rule setsum.neutral, intro ballI, rule setsum.neutral, auto simp: coeff_const)
    also have "?f i = (\<Sum>xa\<le>degree p. (if xa = i then 1 else 0) * h (coeff p xa))" (is "_ = ?m")
      unfolding coeff_const by simp
    also have "\<dots> = ?r"
    proof (cases "i \<le> degree p")
      case True
      show ?thesis
        by (subst setsum.remove[of _ i], insert True, auto)
    next
      case False
      hence [simp]: "coeff p i = 0" using le_degree by blast
      show ?thesis
        by (subst setsum.neutral, auto simp: h0)
    qed
    finally show ?thesis by simp
  qed
  have h'0: "[: h 0 :] = 0" using h0 by auto
  show "coeff ?mp i = coeff ?ep i"
    unfolding coeff_map_poly[of h, OF h0]
    unfolding eval_poly_as_setsum[of "\<lambda>a. [: h a :]", OF h'0]
    unfolding coeff_setsum
    unfolding x_as_monom x_pow_n coeff_mult
    unfolding setsum.commute[of _ _ "{..degree p}"]
    unfolding coeff_monom using 2 by auto
qed  

lemma map_poly_compose: assumes h: "h 0 = 0" and g: "g 0 = 0"
  shows "map_poly h (map_poly g p) = map_poly (h o g) p"
  by (rule poly_eqI, insert h g, auto simp: coeff_map_poly)

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

context semiring_hom
begin
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
  def m \<equiv> "n - degree p"
  have n: "n = degree p + m" unfolding m_def using assms by auto
  have "?r = (\<Sum> i \<le> degree p + m. ?f i)" unfolding n ..
  also have "\<dots> = ?l + setsum ?f {Suc (degree p) .. degree p + m}"
    by (subst setsum.union_disjoint[symmetric], auto intro: setsum.cong)
  also have "setsum ?f {Suc (degree p) .. degree p + m} = 0"
    by (rule setsum.neutral, auto simp: coeff_eq_0)
  finally show ?thesis by simp
qed

lemma map_poly_1[simp]: "map_poly hom 1 = 1" unfolding one_poly_def by simp

lemma map_poly_hom_add[simp]: "map_poly hom (p + q) = map_poly hom p + map_poly hom q"
  by (rule map_poly_add;simp)

lemma map_poly_smult[simp]:
  "map_poly hom (smult c p) = smult (hom c) (map_poly hom p)"
proof(induct p)
  case (pCons a p)
    show ?case
      unfolding map_poly_pCons[OF pCons(1)]
      unfolding smult_pCons
      unfolding pCons(2)[symmetric]
      unfolding map_poly_simps
      by simp
qed auto

lemma map_poly_mult[simp]: "map_poly hom (p * q) = map_poly hom p * map_poly hom q"
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

lemma semiring_hom_map_poly: "semiring_hom (map_poly hom)"
  by (unfold_locales, auto)

lemma poly_map_poly[simp]: "poly (map_poly hom p) (hom x) = hom (poly p x)"
  by (induct p,simp+)

lemma eval_poly_add[simp]: "eval_poly hom (p + q) x = eval_poly hom p x + eval_poly hom q x"
  unfolding eval_poly_def by simp

lemma eval_poly_setsum: "eval_poly hom (\<Sum>k\<in>A. p k) x = (\<Sum>k\<in>A. eval_poly hom (p k) x)"
proof (induct A rule: infinite_finite_induct)
  case (insert a A)
  show ?case
    unfolding setsum.insert[OF insert(1-2)] insert(3)[symmetric] by simp
qed (auto simp: eval_poly_def)

lemma eval_poly_poly: "eval_poly hom p (hom x) = hom (poly p x)"
  unfolding eval_poly_def by auto

lemma coeff_map_poly_hom[simp]: "coeff (map_poly hom p) i = hom (coeff p i)"
  by (rule coeff_map_poly, rule hom_zero)

lemma map_poly_pCons_hom[simp]: "map_poly hom (pCons a p) = pCons (hom a) (map_poly hom p)"
  unfolding map_poly_simps by auto

lemma (in semiring_hom) monom_hom: "monom (hom a) d = map_poly hom (monom a d)"
  apply(induct d) unfolding monom_0 apply simp
  unfolding monom_Suc by simp

lemma (in semiring_hom) map_poly_hom_as_monom_sum:
  "(\<Sum>j\<le>degree p. monom (hom (coeff p j)) j) = map_poly hom p"
proof -
  interpret rhm: semiring_hom "map_poly hom" by(unfold_locales,auto)
  show ?thesis
    apply(subst(6) poly_as_sum_of_monoms'[OF le_refl, symmetric])
    using monom_hom by auto
qed


end

locale map_poly_semiring_hom = semiring_hom
begin
  sublocale semiring_hom "map_poly hom" using semiring_hom_map_poly.
end

context ring_hom
begin
  lemma map_poly_uminus[simp]: "map_poly hom (-p) = - map_poly hom p"
    by (induct p;simp)

lemma map_poly_minus: "map_poly hom (p - q) = map_poly hom p - map_poly hom q"
  unfolding diff_conv_add_uminus
  unfolding map_poly_hom_add by simp

  lemma ring_hom_map_poly: "ring_hom (map_poly hom)"
    using semiring_hom_map_poly by (unfold_locales, auto)
end

locale map_poly_ring_hom = ring_hom
begin
  sublocale rh: ring_hom "map_poly hom" using ring_hom_map_poly.
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

lemma map_poly_inj: assumes id: "map_poly f p = map_poly f q"
  and f: "\<And> x y. f x = f y \<Longrightarrow> x = y"
  and f0: "f 0 = 0"
  shows "p = q"
  using f[OF arg_cong[OF id, of "\<lambda> p. coeff p i" for i, unfolded coeff_map_poly[of f, OF f0]]]
  by (rule poly_eqI)



lemma coeffs_map_poly: assumes h: "\<And> x. x \<in> range (coeff p) \<Longrightarrow> h x = 0 \<longleftrightarrow> x = 0"
  shows "(coeffs (map_poly h p)) = map h (coeffs p)" 
proof -
  have h0: "h 0 = 0" using h by (auto simp: range_coeff)
  have deg: "degree (map_poly h p) = degree p"
    apply (rule degree_map_poly[of h, OF h0]) using h by auto
  show ?thesis
    unfolding coeffs_def deg using coeff_map_poly[of h, OF h0]
    by (auto simp: poly_eq_iff h)
qed
  
context inj_semiring_hom
begin
lemma map_poly_0_iff: "map_poly hom p = 0 \<longleftrightarrow> p = 0"
  unfolding poly_eq_iff coeff_map_poly by auto

lemma degree_map_poly[simp]: "degree (map_poly hom p) = degree p"
  by (rule degree_map_poly, auto)

lemma map_poly_inj: assumes "map_poly hom p = map_poly hom q"
  shows "p = q"
  by (rule map_poly_inj[OF assms], auto simp: hom_inj)

lemma coeffs_map_poly: "(coeffs (map_poly hom p)) = map hom (coeffs p)" 
  by (rule coeffs_map_poly, auto)

lemma inj_semiring_hom_map_poly: "inj_semiring_hom (map_poly hom)"
proof -
  interpret semiring_hom "map_poly hom" by (rule semiring_hom_map_poly)
  show ?thesis
    by (unfold_locales, rule map_poly_inj)
qed
end

lemma (in inj_ring_hom) inj_ring_hom_map_poly: "inj_ring_hom (map_poly hom)"
proof -
  interpret inj_semiring_hom "map_poly hom" by (rule inj_semiring_hom_map_poly)
  interpret ring_hom "map_poly hom" by (rule ring_hom_map_poly)
  show ?thesis by unfold_locales
qed

locale inj_ring_hom_map_poly = inj_ring_hom
begin
  sublocale inj_ring_hom "map_poly hom" using inj_ring_hom_map_poly.
end


lemma pdivmod_pdivmodrel: "pdivmod_rel p q r s \<longleftrightarrow> pdivmod p q = (r,s)" 
  by (metis pdivmod_def pdivmod_rel pdivmod_rel_unique prod.sel)

context inj_field_hom
begin
lemma map_poly_pdivmod: 
  "map_prod (map_poly hom) (map_poly hom) (pdivmod p q) = pdivmod (map_poly hom p) (map_poly hom q)"
  (is "?l = ?r")
proof -
  let ?mp = "map_poly hom"
  obtain r s where dm: "pdivmod p q = (r,s)" by force  
  hence r: "r = p div q" and s: "s = p mod q" 
    by (auto simp add: div_poly_code mod_poly_code)
  from dm[folded pdivmod_pdivmodrel] have "pdivmod_rel p q r s" by auto
  from this[unfolded pdivmod_rel_def]
  have eq: "p = r * q + s" and cond: "(if q = 0 then r = 0 else s = 0 \<or> degree s < degree q)" by auto
  from arg_cong[OF eq, of ?mp, unfolded map_poly_add map_poly_mult]
  have eq: "?mp p = ?mp q * ?mp r + ?mp s" by auto
  from cond have cond: "(if ?mp q = 0 then ?mp r = 0 else ?mp s = 0 \<or> degree (?mp s) < degree (?mp q))"
    unfolding map_poly_0_iff degree_map_poly .
  from eq cond have "pdivmod_rel (?mp p) (?mp q) (?mp r) (?mp s)"
    unfolding pdivmod_rel_def by auto
  from this[unfolded pdivmod_pdivmodrel]
  show ?thesis unfolding dm prod.simps by simp
qed

lemma map_poly_div: "map_poly hom (p div q) = map_poly hom p div map_poly hom q"
  using map_poly_pdivmod[of p q] unfolding div_poly_code by (metis fst_map_prod)

lemma map_poly_mod: "map_poly hom (p mod q) = map_poly hom p mod map_poly hom q"
  using map_poly_pdivmod[of p q] unfolding mod_poly_code by (metis snd_map_prod)

lemma map_poly_gcd: "map_poly hom (gcd p q) = gcd (map_poly hom p) (map_poly hom q)"
proof (induct p q rule: gcd_poly.induct)
  case (1 p)
  show ?case unfolding map_poly_simp_0 gcd_poly.simps 
    map_poly_smult degree_map_poly hom_inverse coeff_map_poly by simp
next
  case (2 p q)
  assume p: "p \<noteq> 0"
  hence mp: "map_poly hom p \<noteq> 0" unfolding map_poly_0_iff .
  note simp = gcd_poly.simps(2)
  show ?case unfolding simp[OF p] simp[OF mp] 2(2) map_poly_mod by simp
qed
  
lemma map_poly_power: "map_poly hom (p ^ n) = (map_poly hom p) ^ n"
  by (induct n, auto)
end


definition div_poly :: "'a :: semiring_div \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "div_poly a p = map_poly (\<lambda> c. c div a) p"

lemma smult_div_poly: assumes "\<And> c. c \<in> set (coeffs p) \<Longrightarrow> a dvd c"
  shows "smult a (div_poly a p) = p" 
  unfolding smult_map_poly div_poly_def 
  by (subst map_poly_compose, force+, subst map_poly_eqI, insert assms, auto)

interpretation ri: inj_ring_hom rat_of_int
  by (unfold_locales, auto)

end
