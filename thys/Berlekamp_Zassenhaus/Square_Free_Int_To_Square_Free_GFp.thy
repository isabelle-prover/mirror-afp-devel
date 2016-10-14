(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
section \<open>Reconstructing Factors of Integer Polynomials\<close>

subsection \<open>Square-Free Polynomials over Finite Fields and Integers\<close>
theory Square_Free_Int_To_Square_Free_GFp
imports   
  "../Polynomial_Factorization/Square_Free_Factorization"
  Finite_Field
  "../Algebraic_Numbers/Resultant"
begin

locale idom_hom = ring_hom hom 
  for hom :: "'a :: idom \<Rightarrow> 'b :: idom"
begin
lemma map_poly_pderiv: "pderiv (map_poly hom p) = map_poly hom (pderiv p)"
proof (induct p rule: pderiv.induct)
  case (1 a p)
  show ?case 
    unfolding pderiv.simps
      map_poly_pCons_hom using 1 by (cases "p = 0", auto)
qed
end

lemma square_free_int_rat: assumes sf: "square_free f"
  shows "square_free (map_poly rat_of_int f)"
proof -
  let ?r = "map_poly rat_of_int" 
  interpret idom_hom rat_of_int ..
  from sf[unfolded square_free_def] have f0: "f \<noteq> 0" "\<And> q. degree q \<noteq> 0 \<Longrightarrow> \<not> q * q dvd f" by auto
  show ?thesis
  proof (rule square_freeI)
    show "?r f \<noteq> 0" using f0 by auto
    fix q
    assume dq: "degree q \<noteq> 0" and dvd: "q * q dvd ?r f" 
    hence q0: "q \<noteq> 0" by auto
    obtain q' c where norm: "rat_to_normalized_int_poly q = (c,q')" by force
    from rat_to_normalized_int_poly[OF norm] have c0: "c \<noteq> 0" by auto
    note q = rat_to_normalized_int_poly(1)[OF norm]
    from dvd obtain k where rf: "?r f = q * (q * k)" unfolding dvd_def by (auto simp: ac_simps)
    from rat_to_int_factor_explicit[OF this norm] obtain s where 
      f: "f = q' * smult (content f) s" by auto
    let ?s = "smult (content f) s" 
    from arg_cong[OF f, of ?r] c0 
    have "?r f = q * (smult (inverse c) (?r ?s))" 
      by (simp add: field_simps q)
    from arg_cong[OF this[unfolded rf], of "\<lambda> f. f div q"] q0 
    have "q * k = smult (inverse c) (?r ?s)" 
      by (metis nonzero_mult_divide_cancel_left)
    from arg_cong[OF this, of "smult c"] have "?r ?s = q * smult c k" using c0
      by (auto simp: field_simps)
    from rat_to_int_factor_explicit[OF this norm] obtain t where "?s = q' * t" by blast
    from f[unfolded this] sf[unfolded square_free_def] f0 have "degree q' = 0" by auto
    with rat_to_normalized_int_poly(4)[OF norm] dq show False by auto
  qed
qed

lemma coprime_idom_iff: 
  "coprime (p :: 'a :: factorial_ring_gcd) q = (\<forall>r. 
  r dvd p \<longrightarrow> r dvd q \<longrightarrow> r dvd 1)"
  by (metis gcd_dvd1 gcd_dvd2 is_unit_gcd semiring_gcd_class.gcd_greatest_iff)  

lemma square_free_imp_resultant_non_zero: assumes sf: "square_free (f :: int poly)" 
  shows "resultant f (pderiv f) \<noteq> 0" 
proof (cases "degree f = 0")
  case True
  from degree0_coeffs[OF this] obtain c where f: "f = [:c:]" by auto
  with sf have c: "c \<noteq> 0" unfolding square_free_def by auto  
  show ?thesis unfolding f by simp
next
  case False note deg = this
  define pp where "pp = normalize_content f" 
  define c where "c = content f"
  from sf have f0: "f \<noteq> 0" unfolding square_free_def by auto
  hence c0: "c \<noteq> 0" unfolding c_def by auto
  have f: "f = smult c pp" unfolding c_def pp_def unfolding smult_normalize_content[of f] ..
  from sf[unfolded f] c0 have sf': "square_free pp" by (metis dvd_smult smult_0_right square_free_def)  
  from deg[unfolded f] c0 have deg': "\<And> x. degree pp > 0 \<or> x" by auto
  from content_normalize_content_1[OF f0] have cp: "content pp = 1" unfolding pp_def .
  let ?p' = "pderiv pp" 
  {
    assume "resultant pp ?p' = 0" 
    from resultant_zero_imp_common_factor[OF deg' this, unfolded coprime_idom_iff]
    obtain r where r: "r dvd pp" "r dvd ?p'" "\<not> r dvd 1" by auto
    from r(1) obtain k where "pp = r * k" unfolding dvd_def by auto
    from pos_zmult_eq_1_iff_lemma[OF arg_cong[OF this, 
      of content, unfolded gauss_lemma cp, symmetric]] content_ge_0_int[of r]
    have cr: "content r = 1" by auto
    with r(3) have dr: "degree r \<noteq> 0"
      by (metis \<open>degree (smult c pp) \<noteq> 0\<close> degree_smult_eq dvdE dvd_poly_int_content_1 
        is_unit_iff_degree mult_eq_0_iff r(1) 
        ri.degree_map_poly unit_imp_dvd)
    let ?r = "map_poly rat_of_int"
    interpret idom_hom rat_of_int ..
    from r(1) have dvd: "?r r dvd ?r pp" unfolding dvd_def by auto
    from r(2) have "?r r dvd ?r ?p'" unfolding dvd_def by auto
    also have "?r ?p' = pderiv (?r pp)" unfolding map_poly_pderiv ..
    finally have dvd': "?r r dvd pderiv (?r pp)" by auto
    from dr have dr': "degree (?r r) \<noteq> 0" by simp
    from square_free_coprime_pderiv[OF square_free_int_rat[OF sf']]
    have cop: "coprime (?r pp) (pderiv (?r pp))" .
    from f0 f have pp0: "pp \<noteq> 0" by auto
    from dvd dvd' have "?r r dvd gcd (?r pp) (pderiv (?r pp))" by auto
    from divides_degree[OF this] pp0 have "degree (?r r) \<le> degree (gcd (?r pp) (pderiv (?r pp)))" 
      by auto
    with dr' have "degree (gcd (?r pp) (pderiv (?r pp))) \<noteq> 0" by auto
    hence "\<not> coprime (?r pp) (pderiv (?r pp))" by auto
    with cop have False by auto
  }
  hence "resultant pp ?p' \<noteq> 0" by auto
  with resultant_smult_left[OF c0, of pp ?p', folded f] c0 
  have "resultant f ?p' \<noteq> 0" by auto
  with resultant_smult_right[OF c0, of f ?p', folded pderiv_smult f] c0
  show "resultant f (pderiv f) \<noteq> 0" by auto
qed

lemma large_mod_0: assumes "(n :: int) > 1" "\<bar>k\<bar> < n" "k mod n = 0" shows "k = 0" 
proof (cases "k \<ge> 0")
  case False
  with assms have "k mod n = k + n" 
    using mod_add_self1 mod_pos_pos_trivial semiring_numeral_div_class.mod_less
    by (metis abs_0_eq abs_ge_zero abs_mult abs_of_pos less_trans mod_mult_self1_is_0 zero_less_one_class.zero_less_one zmod_eq_0D)
  with assms show ?thesis by auto
qed (insert assms, auto)

definition square_free_bound :: "int poly \<Rightarrow> int" where
  "square_free_bound f = max (abs (resultant f (pderiv f))) 
    (max (abs (lead_coeff f)) (abs (lead_coeff (pderiv f))))"

lemma square_free_int_imp_resultant_non_zero_mod_ring: assumes sf: "square_free f" 
  and large: "int CARD('a) > square_free_bound f"
  shows "resultant (map_poly of_int f :: 'a :: prime_card mod_ring poly) (pderiv (map_poly of_int f)) \<noteq> 0
  \<and> map_poly of_int f \<noteq> (0 :: 'a mod_ring poly)" 
proof (intro conjI, rule notI)
  let ?i = "of_int :: int \<Rightarrow> 'a mod_ring" 
  let ?m = "map_poly ?i" 
  let ?f = "?m f" 
  from sf[unfolded square_free_def] have f0: "f \<noteq> 0" by auto
  hence lf: "lead_coeff f \<noteq> 0" unfolding lead_coeff_def by auto
  {
    fix k :: int
    have C1: "int CARD('a) > 1" using prime_card[where 'a = 'a] by (auto simp: prime_nat_iff)
    assume "abs k < CARD('a)" and "?i k = 0" 
    hence "k = 0" unfolding of_int_of_int_mod_ring
        by (transfer) (rule large_mod_0[OF C1])
  } note of_int_0 = this
  from square_free_imp_resultant_non_zero[OF sf]
  have non0: "resultant f (pderiv f) \<noteq> 0" .
  interpret idom_hom ?i by (standard, auto)
  {
    fix g :: "int poly" 
    assume abs: "abs (lead_coeff g) < CARD('a)"     
    have "degree (?m g) = degree g"
    proof (rule degree_map_poly, force)
      assume "?i (coeff g (degree g)) = 0" 
      from of_int_0[OF abs[unfolded lead_coeff_def] this]
      show "g = 0" by auto
    qed
  } note deg = this
  note large = large[unfolded square_free_bound_def]
  from of_int_0[of "lead_coeff f"] large lf have "?i (lead_coeff f) \<noteq> 0" by auto
  also have "?i (lead_coeff f) = coeff ?f (degree f)" unfolding lead_coeff_def by simp
  finally show f0: "?f \<noteq> 0" unfolding poly_eq_iff by auto  
  assume 0: "resultant ?f (pderiv ?f) = 0" 
  have "resultant ?f (pderiv ?f) = ?i (resultant f (pderiv f))"
    unfolding map_poly_pderiv
    by (subst resultant_map_poly(1)[OF deg deg], insert large, auto)
  from of_int_0[OF _ this[symmetric, unfolded 0]] non0
  show False using large by auto
qed

lemma mod_const_0[simp]: "c \<noteq> 0 \<Longrightarrow> f mod [:c:] = 0" 
proof -
  assume c: "c \<noteq> 0" 
  obtain q r where "pdivmod f [:c:] = (q,r)" by force
  hence pd: "pdivmod_rel f [:c:] q r"
    by (simp add: Ring_Hom_Poly.pdivmod_pdivmodrel)
  from this[unfolded pdivmod_rel_def] c have "r = 0" by auto
  thus ?thesis using mod_poly_eq[OF pd] by simp
qed

lemma resultant_non_zero_imp_coprime: assumes nz: "resultant (f :: 'a :: {field,euclidean_ring_gcd} poly) g \<noteq> 0" 
  and nz': "f \<noteq> 0 \<or> g \<noteq> 0" 
  shows "coprime f g" 
proof (cases "degree f = 0 \<or> degree g = 0")
  case False
  define r where "r = [:resultant f g:]" 
  from nz have r: "r \<noteq> 0" unfolding r_def by auto
  from False have "degree f > 0" "degree g > 0" by auto
  from resultant_as_nonzero_poly_weak[OF this nz]
  obtain p q where "degree p < degree g" "degree q < degree f" 
    and id: "r = p * f + q * g"
    and "p \<noteq> 0" "q \<noteq> 0" unfolding r_def by auto
  define h where "h = gcd f g" 
  have "h dvd f" "h dvd g" unfolding h_def by auto
  then obtain j k where f: "f = h * j" and g: "g = h * k" unfolding dvd_def by auto
  from id[unfolded f g] have id: "h * (p * j + q * k) = r" by (auto simp: field_simps)
  from arg_cong[OF id, of degree] have "degree (h * (p * j + q * k)) = 0" 
    unfolding r_def by auto
  also have "degree (h * (p * j + q * k)) = degree h + degree (p * j + q * k)" 
    by (subst degree_mult_eq, insert id r, auto)
  finally have h: "degree h = 0" "h \<noteq> 0" using r id by auto
  thus ?thesis unfolding h_def using is_unit_gcd is_unit_iff_degree by blast
next
  case True
  {
    fix f g :: "'a poly" 
    assume g: "degree g = 0" and res: "resultant f g \<noteq> 0" and nz: "f \<noteq> 0 \<or> g \<noteq> 0" 
    from degree0_coeffs[OF g] obtain c where g: "g = [:c:]" by auto
    from res[unfolded this resultant_const] have cf: "c ^ degree f \<noteq> 0" by auto
    {
      assume c: "c \<noteq> 0" 
      have "gcd f g = gcd g 0" unfolding g gcd_poly_def gcd_eucl_eq_gcd_factorial[symmetric] gcd_eucl.simps[of f] using c by simp
      also have "\<dots> = normalize [:c:]" unfolding g by simp
      also have "\<dots> = 1" using c by (metis Polynomial_Division.normalize_smult normalize_1 smult_1)
      finally have "coprime f g" .
    }
    moreover
    {
      assume c: "c = 0"
      with g have g: "g = 0" by auto
      from c cf have "degree f = 0" by auto
      from degree0_coeffs[OF this] obtain d where f: "f = [:d:]" by auto
      from nz[unfolded g f] have d: "d \<noteq> 0" by auto
      have "gcd f g = normalize [:d:]" unfolding g f by simp
      also have "\<dots> = 1" using d by (metis Polynomial_Division.normalize_smult normalize_1 smult_1)
      finally have "coprime f g" .
    }
    ultimately have "coprime f g" by auto
  } note main = this
  from True
  show ?thesis
  proof
    assume f: "degree f = 0" 
    from nz[unfolded resultant_swap[of f g]] have "resultant g f \<noteq> 0" by (auto split: if_splits)
    from main[OF f this] nz' show ?thesis by (auto simp: gcd.commute)
  next
    assume "degree g = 0" 
    from main[OF this nz nz'] show ?thesis .
  qed
qed  
   

lemma square_free_int_imp_square_free_mod_ring: assumes sf: "square_free f" 
  and large: "int CARD('a) > square_free_bound f"
  shows "square_free (map_poly of_int f :: 'a :: prime_card mod_ring poly)" 
proof - 
  define g where "g = map_poly (of_int :: int \<Rightarrow> 'a mod_ring) f"
  from square_free_int_imp_resultant_non_zero_mod_ring[OF sf large]
  have res: "resultant g (pderiv g) \<noteq> 0" and g: "g \<noteq> 0" unfolding g_def by auto
  from resultant_non_zero_imp_coprime[OF res] g
  have "coprime g (pderiv g)" by auto
  hence "square_free g" by (rule coprime_pderiv_imp_square_free)
  thus ?thesis unfolding g_def .
qed

end
