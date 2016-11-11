(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
section \<open>Hensel Lifting\<close>

subsection \<open>Properties about Factors\<close>

text \<open>We define and prove properties of Hensel-lifting. Here, we show the result that 
  Hensel-lifting can lift a factorization mod $p$ to a factorization mod $p^n$. 
  For the lifting we have proofs for both versions, the original linear Hensel-lifting or 
  the quadratic approach from Zassenhaus. 
  Via the linear version, we also show a uniqueness result, however only in the 
  binary case, i.e., where $f = g \cdot h$. Uniqueness of the general case will later be shown 
  in theory Berlekamp-Hensel by incorporating the factorization algorithm for finite fields algorithm.\<close>

theory Hensel_Lifting
imports 
  "~~/src/HOL/Number_Theory/Euclidean_Algorithm"
  Poly_Mod_Finite_Field_Record_Based
  "../Sqrt_Babylonian/NthRoot_Impl" (* for log_ceil *)
  "~~/src/HOL/Library/Types_To_Sets"
  "../Polynomial_Factorization/Square_Free_Factorization"
begin

lemma prod_mset[simp]:"prod_mset (mset x) = prod_list x" by (induct x,auto)

lemma mult_1_is_id[simp]: "op * (1 :: 'a :: ring_1) = id" by auto

definition pdivmod_monic :: "'a::comm_ring_1 poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<times> 'a poly" where
  "pdivmod_monic f g \<equiv> let cg = coeffs g; cf = coeffs f; 
     (q, r) = divmod_poly_one_main_list [] (rev cf) (rev cg) (1 + length cf - length cg)
         in (poly_of_list q, poly_of_list (rev r))"

lemma pseudo_divmod_main_list_1_is_divmod_poly_one_main_list: 
  "pseudo_divmod_main_list (1 :: 'a :: comm_ring_1) q f g n = divmod_poly_one_main_list q f g n"
  by (induct n arbitrary: q f g, auto simp: Let_def)

lemma pdivmod_monic_pseudo_divmod: assumes g: "monic g" shows "pdivmod_monic f g = pseudo_divmod f g" 
proof -
  from g have id: "(coeffs g = []) = False" by auto
  from g have mon: "hd (rev (coeffs g)) = 1" by (metis coeffs_eq_Nil hd_rev id last_coeffs_eq_coeff_degree)
  show ?thesis
    unfolding pseudo_divmod_impl pseudo_divmod_list_def id if_False pdivmod_monic_def Let_def mon
      pseudo_divmod_main_list_1_is_divmod_poly_one_main_list by (auto split: prod.splits)
qed

lemma pdivmod_monic: assumes g: "monic g" and res: "pdivmod_monic f g = (q, r)"
  shows "f = g * q + r" "r = 0 \<or> degree r < degree g"
proof -
  from g have g0: "g \<noteq> 0" by auto
  from pseudo_divmod[OF g0 res[unfolded pdivmod_monic_pseudo_divmod[OF g]], unfolded g]
  show "f = g * q + r" "r = 0 \<or> degree r < degree g" by auto
qed

context poly_mod
begin

definition dupe_monic :: "int poly \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> 
  int poly * int poly" where
  "dupe_monic D H S T U = (case pdivmod_monic (Mp (T * U)) D of (q,r) \<Rightarrow>
     (Mp (S * U + H * q), Mp r))"

end

declare poly_mod.dupe_monic_def[code]

context poly_mod
begin

lemma degree_m_eq_monic: "monic f \<Longrightarrow> m > 1 \<Longrightarrow> degree_m f = degree f" 
  by (rule degree_m_eq, auto)

lemma monic_degree_m_lift: assumes "monic f" "k > 1" "m > 1"
  shows "monic (poly_mod.Mp (m * k) f)" 
proof -
  have deg: "degree (poly_mod.Mp (m * k) f) = degree f" 
    by (rule poly_mod.degree_m_eq_monic[of f "m * k", unfolded poly_mod.degree_m_def], 
    insert assms, auto simp: less_1_mult)
  show ?thesis unfolding poly_mod.Mp_coeff deg assms poly_mod.M_def using assms(2-)
    by (simp add: less_1_mult)
qed  
end



lemma uniqueness_poly_equality: assumes cop: "coprime f g" 
  and deg: "B = 0 \<or> degree B < degree f" "B' = 0 \<or> degree B' < degree f"
  and f: "f \<noteq> 0" and eq: "A * f + B * g = A' * f + B' * g" 
  shows "A = A'" "B = B'" 
proof -
  from eq have *: "(A - A') * f = (B' - B) * g" by (simp add: field_simps)
  hence "f dvd (B' - B) * g" unfolding dvd_def by (intro exI[of _ "A - A'"], auto simp: field_simps)
  with cop have dvd: "f dvd (B' - B)" by (rule coprime_dvd_mult)
  from divides_degree[OF this] have "degree f \<le> degree (B' - B) \<or> B = B'" by auto
  with degree_diff_le_max[of B' B] deg have B: "B = B'" by auto
  with * f show "A = A'" "B = B'" by auto
qed

context poly_mod_type
begin
lemma uniqueness_poly_equality_mod_int: assumes 
    deg: "b =m 0 \<or> degree_m b < degree_m f" "b' =m 0 \<or> degree_m b' < degree_m f"
  and f0: "\<not> (f =m 0)" 
  and cop: "coprime_m f g" 
  and eq: "a * f + b * g =m a' * f + b' * g" 
  shows "a =m a'" "b =m b'" 
proof -
  obtain F G A B A' B' :: "'a mod_ring poly" where 
    f: "F = of_int_poly f"
  and g: "G = of_int_poly g" 
  and a: "A = of_int_poly a"
  and b: "B = of_int_poly b"
  and a': "A' = of_int_poly a'"
  and b': "B' = of_int_poly b'" by auto
  have f[transfer_rule]: "MP_Rel f F" unfolding f MP_Rel_def
    by (simp add: Mp_f_representative)
  have g[transfer_rule]: "MP_Rel g G" unfolding g MP_Rel_def
    by (simp add: Mp_f_representative)
  have a[transfer_rule]: "MP_Rel a A" unfolding a MP_Rel_def
    by (simp add: Mp_f_representative)
  have b[transfer_rule]: "MP_Rel b B" unfolding b MP_Rel_def
    by (simp add: Mp_f_representative)
  have a'[transfer_rule]: "MP_Rel a' A'" unfolding a' MP_Rel_def
    by (simp add: Mp_f_representative)
  have b'[transfer_rule]: "MP_Rel b' B'" unfolding b' MP_Rel_def
    by (simp add: Mp_f_representative)
  have eq: "A * F + B * G = A' * F + B' * G" by (transfer, rule eq)
  have 0: "F \<noteq> 0" by (transfer, rule f0)
  have degB: "B = 0 \<or> degree B < degree F" by (transfer, rule deg)
  have degB': "B' = 0 \<or> degree B' < degree F" by (transfer, rule deg)
  from cop have "coprime F G" using coprime_MP_Rel[unfolded rel_fun_def, rule_format, OF f g] by auto
  from uniqueness_poly_equality[OF this degB degB' 0 eq, untransferred] show "a =m a'" "b =m b'" .
qed
end

context poly_mod
begin

lemma uniqueness_poly_equality_mod: assumes 
    deg: "b =m 0 \<or> degree_m b < degree_m f" "b' =m 0 \<or> degree_m b' < degree_m f"
  and f0: "\<not> (f =m 0)" 
  and cop: "coprime_m f g" 
  and eq: "a * f + b * g =m a' * f + b' * g" 
  and p: "prime m" 
  shows "a =m a'" "b =m b'" 
proof -
  have ne: "{0..<m} \<noteq> {}" using prime_ge_2_int[OF p] by auto
  {
    assume "\<exists>(Rep :: 'b \<Rightarrow> int) Abs. type_definition Rep Abs {0 ..< m :: int}"
    from prime_type_prime_card[OF p this]
    have "class.prime_card TYPE('b)" "m = int CARD('b)" by auto
    from poly_mod_type.uniqueness_poly_equality_mod_int[unfolded prime_field_def poly_mod_type_def, 
      internalize_sort "'a :: prime_card", OF this deg f0 cop eq]
    have "a =m a' \<and> b =m b'" by auto
  }
  from this[cancel_type_definition, OF ne]
  show "a =m a'" "b =m b'" by auto
qed
end

locale poly_mod_2 = poly_mod m for m +
  assumes m1: "m > 1"
begin

lemma M_1[simp]: "M 1 = 1" unfolding M_def using m1 by auto

lemma Mp_1[simp]: "Mp 1 = 1" unfolding Mp_def one_poly_def by simp

lemma monic_degree_Mp: "monic f \<Longrightarrow> degree (Mp f) = degree f" 
  using degree_m_eq_monic[of f] unfolding degree_m_def using m1 by auto

lemma monic_Mp: "monic f \<Longrightarrow> monic (Mp f)" 
  by (subst monic_degree_Mp, auto simp: Mp_coeff)

lemma dupe_monic: assumes 1: "D*S + H*T =m 1" 
  and mon: "monic D" 
  and dupe: "dupe_monic D H S T U = (A,B)" 
  shows "A * D + B * H =m U" "B = 0 \<or> degree B < degree D" "Mp A = A" "Mp B = B" 
    "coprime_m D H \<Longrightarrow> A' * D + B' * H =m U \<Longrightarrow> B' = 0 \<or> degree B' < degree D \<Longrightarrow> Mp D = D 
    \<Longrightarrow> Mp A' = A' \<Longrightarrow> Mp B' = B' \<Longrightarrow> prime m
    \<Longrightarrow> A' = A \<and> B' = B"
proof -
  obtain q r where div: "pdivmod_monic (Mp (T * U)) D = (q,r)" by force
  from dupe[unfolded dupe_monic_def div split]
  have A: "A = Mp (S * U + H * q)" and B: "B = Mp r" by auto
  from pdivmod_monic[OF mon div] have TU: "Mp (T * U) = D * q + r" and 
    deg: "r = 0 \<or> degree r < degree D" by auto
  hence "Mp r = Mp (Mp (T * U) - D * q)" by simp
  also have "\<dots> = Mp (T * U - Mp (Mp (Mp D * q)))" unfolding Mp_Mp unfolding minus_Mp
    using minus_Mp mult_Mp by metis
  also have "\<dots> = Mp (T * U - D * q)" by simp
  finally have r: "Mp r = Mp (T * U - D * q)" by simp
  have "Mp (A * D + B * H) = Mp (Mp (A * D) + Mp (B * H))" by simp
  also have "Mp (A * D) = Mp ((S * U + H * q) * D)" unfolding A by simp
  also have "Mp (B * H) = Mp (Mp r * Mp H)" unfolding B by simp
  also have "\<dots> = Mp ((T * U - D * q) * H)" unfolding r by simp
  also have "Mp (Mp ((S * U + H * q) * D) + Mp ((T * U - D * q) * H)) = 
    Mp ((S * U + H * q) * D + (T * U - D * q) * H)" by simp
  also have "(S * U + H * q) * D + (T * U - D * q) * H = (D * S + H * T) * U"
    by (simp add: field_simps)
  also have "Mp \<dots> = Mp (Mp (D * S + H * T) * U)" by simp
  also have "Mp (D * S + H * T) = 1" using 1 unfolding equivalent_def by simp  
  finally show eq: "A * D + B * H =m U" unfolding equivalent_def by simp
  have id: "degree_m (Mp r) = degree_m r" unfolding degree_m_def by simp
  have id': "degree D = degree_m D" using monic_degree_Mp[OF mon] unfolding degree_m_def by simp
  show degB: "B = 0 \<or> degree B < degree D" using deg unfolding B degree_m_def[symmetric] id id'
    using degree_m_le[of r] by (cases "r = 0", auto)    
  show Mp: "Mp A = A" "Mp B = B" unfolding A B by auto
  assume another: "A' * D + B' * H =m U" and degB': "B' = 0 \<or> degree B' < degree D" 
    and norm: "Mp A' = A'" "Mp B' = B'" and cop: "coprime_m D H" and D: "Mp D = D" 
    and prime: "prime m" 
  from degB Mp D have degB: "B =m 0 \<or> degree_m B < degree_m D" 
    unfolding degree_m_def equivalent_def by auto
  from degB' Mp D norm have degB': "B' =m 0 \<or> degree_m B' < degree_m D" 
    unfolding degree_m_def equivalent_def by auto
  from mon D have D0: "\<not> (D =m 0)" unfolding equivalent_def by auto
  from another eq have "A' * D + B' * H =m A * D + B * H" unfolding equivalent_def by simp
  from uniqueness_poly_equality_mod[OF degB' degB D0 cop this prime]
  show "A' = A \<and> B' = B" unfolding equivalent_def norm Mp by auto
qed

lemma Mp_0_smult_div_poly: assumes "Mp f = 0" 
  shows "smult m (div_poly m f) = f" 
  unfolding equivalent_def
proof (intro poly_eqI, unfold Mp_coeff coeff_smult div_poly_def, subst coeff_map_poly, force)
  fix n
  from assms have "coeff (Mp f) n = 0" by simp
  hence 0: "coeff f n mod m = 0" unfolding Mp_coeff M_def .
  thus "m * (coeff f n div m) = coeff f n" by auto
qed

lemma Mp_product_modulus: "m' = m * k \<Longrightarrow> k > 0 \<Longrightarrow> Mp (poly_mod.Mp m' f) = Mp f" 
  by (intro poly_eqI, unfold poly_mod.Mp_coeff poly_mod.M_def, auto simp: mod_mod_cancel) 
end

lemma (in poly_mod) degree_m_eq_prime:  
  assumes f0: "Mp f \<noteq> 0"
  and deg: "degree_m f = degree f" 
  and eq: "f =m g * h" 
  and p: "prime m" 
  shows "degree_m f = degree_m g + degree_m h" 
proof -
  interpret poly_mod_2 m using prime_ge_2_int[OF p] unfolding poly_mod_2_def by simp
  from f0 eq have "Mp (Mp g * Mp h) \<noteq> 0" unfolding equivalent_def by auto
  hence "Mp g * Mp h \<noteq> 0" using Mp_0 by (cases "Mp g * Mp h", auto)
  hence g0: "Mp g \<noteq> 0" and h0: "Mp h \<noteq> 0" by auto
  have "degree (Mp (g * h)) = degree_m (Mp g * Mp h)" unfolding degree_m_def by simp
  also have "\<dots> = degree (Mp g * Mp h)" 
  proof (rule degree_m_eq[OF _ m1], rule)
    have id: "\<And> g. coeff (Mp g) (degree (Mp g)) mod m = coeff (Mp g) (degree (Mp g))" 
      unfolding M_def[symmetric] Mp_coeff by simp
    from p have p': "prime m" unfolding prime_int_nat_transfer unfolding prime_nat_iff by auto 
    assume "coeff (Mp g * Mp h) (degree (Mp g * Mp h)) mod m = 0" 
    from this[unfolded coeff_degree_mult] 
    have "coeff (Mp g) (degree (Mp g)) mod m = 0 \<or> coeff (Mp h) (degree (Mp h)) mod m = 0"
      unfolding dvd_eq_mod_eq_0[symmetric] using m1 prime_dvd_mult_int[OF p'] by auto    
    with g0 h0 show False unfolding id by auto
  qed
  also have "\<dots> = degree (Mp g) + degree (Mp h)" 
    by (rule degree_mult_eq[OF g0 h0])
  finally show ?thesis unfolding degree_m_def
    using eq unfolding equivalent_def by simp
qed 

lemma monic_smult_add_small: assumes "f = 0 \<or> degree f < degree g" and mon: "monic g" 
  shows "monic (g + smult q f)"
proof (cases "f = 0")
  case True
  thus ?thesis using mon by auto
next
  case False
  with assms have "degree f < degree g" by auto
  hence "degree (smult q f) < degree g" by (meson degree_smult_le not_less order_trans)
  thus ?thesis using mon using coeff_eq_0 degree_add_eq_left by fastforce
qed


definition euclid_ext_poly_no_gcd :: "'a :: prime_card mod_ring poly \<Rightarrow> 'a mod_ring poly \<Rightarrow> 'a mod_ring  poly \<times> 'a mod_ring  poly" where
  "euclid_ext_poly_no_gcd f g = (case euclid_ext f g of (a,b,_) \<Rightarrow> (a, b))"

lemma euclid_ext_poly_no_gcd: assumes cop: "coprime f g" and ext: "euclid_ext_poly_no_gcd f g = (a,b)" 
  shows "f * a + g * b = 1"  
proof -
  obtain a' b' c where fg: "euclid_ext f g = (a',b',c)" by (cases "euclid_ext f g")
  from euclid_ext_correct[of f g, unfolded fg split cop] have "f * a' + g * b' = 1"
    by (simp add: ac_simps)
  with ext show "f * a + g * b = 1" unfolding euclid_ext_poly_no_gcd_def fg split by auto
qed

context poly_mod_2
begin

lemma factorization_m_lead_coeff: assumes "factorization_m f (c,fs)" 
  shows "lead_coeff (Mp f) = M c" 
proof -
  note * = assms[unfolded factorization_m_def split]
  have "monic (prod_mset (image_mset Mp fs))" by (rule monic_prod_mset, insert *, auto)
  hence "monic (Mp (prod_mset (image_mset Mp fs)))" by (rule monic_Mp)
  from this[unfolded Mp_prod_mset] have monic: "monic (Mp (prod_mset fs))" by simp
  from * have "lead_coeff (Mp f) = lead_coeff (Mp (smult c (prod_mset fs)))" 
    by (simp add: equivalent_def)
  also have "Mp (smult c (prod_mset fs)) = Mp (smult (M c) (Mp (prod_mset fs)))" by simp
  finally show ?thesis using monic
    by (metis M_M Mp_0 Mp_coeff degree_m_eq lead_coeff_def lead_coeff_smult m1 
      mult_cancel_left2 poly_mod.M_def poly_mod.degree_m_def smult_eq_0_iff)
qed

lemma factorization_m_smult: assumes "factorization_m f (c,fs)" 
  shows "factorization_m (smult d f) (c * d,fs)"
proof -
  note * = assms[unfolded factorization_m_def split]
  from * have f: "Mp f = Mp (smult c (prod_mset fs))" unfolding equivalent_def by simp
  have "Mp (smult d f) = Mp (smult d (Mp f))" by simp
  also have "\<dots> = Mp (smult (c * d) (prod_mset fs))" unfolding f by (simp add: ac_simps)
  finally show ?thesis using assms
  unfolding factorization_m_def split by (auto simp: equivalent_def)
qed

lemma factorization_m_prod: assumes "factorization_m f (c,fs)" "factorization_m g (d,gs)" 
  shows "factorization_m (f * g) (c * d, fs + gs)"
proof -
  note * = assms[unfolded factorization_m_def split]
  have "Mp (f * g) = Mp (Mp f * Mp g)" by simp
  also have "Mp f = Mp (smult c (prod_mset fs))" using * unfolding equivalent_def by simp
  also have "Mp g = Mp (smult d (prod_mset gs))" using * unfolding equivalent_def by simp
  finally have "Mp (f * g) = Mp (smult (c * d) (prod_mset (fs + gs)))" unfolding mult_Mp
    by (simp add: ac_simps)
  with * show ?thesis unfolding factorization_m_def split equivalent_def by auto
qed

lemma Mp_factorization_m[simp]: "factorization_m (Mp f) cfs = factorization_m f cfs" 
  unfolding factorization_m_def equivalent_def by simp

lemma Mp_unique_factorization_m[simp]: 
  "unique_factorization_m (Mp f) cfs = unique_factorization_m f cfs" 
  unfolding unique_factorization_m_alt_def by simp

lemma unique_factorization_m_cong: "unique_factorization_m f cfs \<Longrightarrow> Mp f = Mp g 
  \<Longrightarrow> unique_factorization_m g cfs"
  unfolding Mp_unique_factorization_m[of f, symmetric] by simp

lemma unique_factorization_mI: assumes "factorization_m f (c,fs)" 
  and "\<And> d gs. factorization_m f (d,gs) \<Longrightarrow> Mf (d,gs) = Mf (c,fs)"
  shows "unique_factorization_m f (c,fs)" 
  unfolding unique_factorization_m_alt_def 
    by (intro conjI[OF assms(1)] allI impI, insert assms(2), auto)

lemma unique_factorization_m_smult: assumes uf: "unique_factorization_m f (c,fs)"
  and d: "M (di * d) = 1"
  shows "unique_factorization_m (smult d f) (c * d,fs)"
proof (rule unique_factorization_mI[OF factorization_m_smult])
  show "factorization_m f (c, fs)" using uf[unfolded unique_factorization_m_alt_def] by auto
  fix e gs
  assume fact: "factorization_m (smult d f) (e,gs)" 
  from factorization_m_smult[OF this, of di] 
  have "factorization_m (Mp (smult di (smult d f))) (e * di, gs)" by simp
  also have "Mp (smult di (smult d f)) = Mp (smult (M (di * d)) f)" by simp
  also have "\<dots> = Mp f" unfolding d by simp
  finally have fact: "factorization_m f (e * di, gs)" by simp
  with uf[unfolded unique_factorization_m_alt_def] have eq: "Mf (e * di, gs) = Mf (c, fs)" by blast
  from eq[unfolded Mf_def] have "M (e * di) = M c" by simp
  from arg_cong[OF this, of "\<lambda> x. M (x * d)"]
  have "M (e * M (di * d)) = M (c * d)" by (simp add: ac_simps)
  from this[unfolded d] have e: "M e = M (c * d)" by simp
  with eq
  show "Mf (e,gs) = Mf (c * d, fs)" unfolding Mf_def split by simp
qed  

lemma unique_factorization_m_smultD: assumes uf: "unique_factorization_m (smult d f) (c,fs)"
  and d: "M (di * d) = 1"
  shows "unique_factorization_m f (c * di,fs)"
proof -
  from d have d': "M (d * di) = 1" by (simp add: ac_simps)
  show ?thesis
  proof (rule unique_factorization_m_cong[OF unique_factorization_m_smult[OF uf d']], 
    rule poly_eqI, unfold Mp_coeff coeff_smult)
    fix n
    have "M (di * (d * coeff f n)) = M (M (di * d) * coeff f n)" by (auto simp: ac_simps)
    from this[unfolded d] show "M (di * (d * coeff f n)) = M (coeff f n)" by simp
  qed
qed

lemma degree_m_eq_lead_coeff: "degree_m f = degree f \<Longrightarrow> lead_coeff (Mp f) = M (lead_coeff f)" 
  unfolding lead_coeff_def degree_m_def
  by (simp add: Mp_coeff)

lemma unique_factorization_m_zero: assumes "unique_factorization_m f (c,fs)" 
  shows "M c \<noteq> 0" 
proof
  assume c: "M c = 0" 
  from unique_factorization_m_imp_factorization[OF assms]
  have "Mp f = Mp (smult (M c) (prod_mset fs))" unfolding factorization_m_def equivalent_def split 
    by simp
  from this[unfolded c] have f: "Mp f = 0" by simp
  have "factorization_m f (0,{#})" 
    unfolding factorization_m_def split equivalent_def f by auto
  moreover have "Mf (0,{#}) = (0,{#})" unfolding Mf_def by auto
  ultimately have fact1: "(0, {#}) \<in> Mf ` Collect (factorization_m f)" by force
  define g :: "int poly" where "g = [:0,1:]" 
  have mpg: "Mp g = [:0,1:]" unfolding Mp_def
    by (auto simp: g_def)
  {
    fix g h
    assume *: "degree (Mp g) = 0" "degree (Mp h) = 0" "[:0, 1:] = Mp (g * h)" 
    from arg_cong[OF *(3), of degree] have "1 = degree_m (Mp g * Mp h)" by (simp add: degree_m_def)
    also have "\<dots> \<le> degree (Mp g * Mp h)" by (rule degree_m_le)
    also have "\<dots> \<le> degree (Mp g) + degree (Mp h)" by (rule degree_mult_le)
    also have "\<dots> \<le> 0" using * by simp
    finally have False by simp
  } note irr = this    
  have "factorization_m f (0,{# g #})" 
    unfolding factorization_m_def split using irr
    by (auto simp: irreducible_m_def degree_m_def equivalent_def f mpg)
  moreover have "Mf (0,{# g #}) = (0,{# g #})" unfolding Mf_def by (auto simp: mpg, simp add: g_def)
  ultimately have fact2: "(0, {#g#}) \<in> Mf ` Collect (factorization_m f)" by force
  note [simp] = assms[unfolded unique_factorization_m_def]
  from fact1[simplified, folded fact2[simplified]] show False by auto
qed


end

context poly_mod
begin

lemma dvdm_smult: assumes "f dvdm g" 
  shows "f dvdm smult c g" 
proof -
  from assms[unfolded dvdm_def] obtain h where g: "g =m f * h" by auto
  show ?thesis unfolding dvdm_def equivalent_def
  proof (intro exI[of _ "smult c h"])
    have "Mp (smult c g) = Mp (smult c (Mp g))" by simp
    also have "Mp g = Mp (f * h)" using g[unfolded equivalent_def] by simp
    finally show "Mp (smult c g) = Mp (f * smult c h)" by simp
  qed
qed

lemma dvdm_factor: assumes "f dvdm g" 
  shows "f dvdm g * h" 
proof -
  from assms[unfolded dvdm_def] obtain k where g: "g =m f * k" by auto
  show ?thesis unfolding dvdm_def equivalent_def
  proof (intro exI[of _ "h * k"])
    have "Mp (g * h) = Mp (Mp g * h)" by simp
    also have "Mp g = Mp (f * k)" using g[unfolded equivalent_def] by simp
    finally show "Mp (g * h) = Mp (f * (h * k))" by (simp add: ac_simps)
  qed
qed    

lemma square_free_m_smultD: assumes "square_free_m (smult c f)" 
  shows "square_free_m f" 
  unfolding square_free_m_def
proof (intro conjI allI impI)
  fix g
  assume "degree_m g \<noteq> 0" 
  with assms[unfolded square_free_m_def] have "\<not> g * g dvdm smult c f" by auto
  thus "\<not> g * g dvdm f" using dvdm_smult[of "g * g" f c] by blast
next
  from assms[unfolded square_free_m_def] have "\<not> smult c f =m 0" by simp
  thus "\<not> f =m 0" unfolding equivalent_def 
    by (metis Mp_smult(2) smult_0_right)
qed

lemma square_free_m_smultI: assumes sf: "square_free_m f" 
  and inv: "M (ci * c) = 1" 
  shows "square_free_m (smult c f)" 
proof -
  have "square_free_m (smult ci (smult c f))" 
  proof (rule square_free_m_cong[OF sf], rule poly_eqI, unfold Mp_coeff coeff_smult)
    fix n
    have "M (ci * (c * coeff f n)) = M ( M (ci * c) * coeff f n)" by (simp add: ac_simps)
    from this[unfolded inv] show "M (coeff f n) = M (ci * (c * coeff f n))" by simp
  qed
  from square_free_m_smultD[OF this] show ?thesis .
qed


lemma square_free_m_factor: assumes "square_free_m (f * g)" 
  shows "square_free_m f" "square_free_m g"
proof -
  {
    fix f g
    assume sf: "square_free_m (f * g)" 
    have "square_free_m f"         
      unfolding square_free_m_def
    proof (intro conjI allI impI)
      fix h
      assume "degree_m h \<noteq> 0" 
      with sf[unfolded square_free_m_def] have "\<not> h * h dvdm f * g" by auto
      thus "\<not> h * h dvdm f" using dvdm_factor[of "h * h" f g] by blast        
    next
      from sf[unfolded square_free_m_def] have "\<not> f * g =m 0" by simp
      thus "\<not> f =m 0" unfolding equivalent_def
        by (metis mult.commute mult_zero_right poly_mod.equivalent_def poly_mod.mult_Mp(2))
    qed
  }
  from this[of f g] this[of g f] assms 
  show "square_free_m f" "square_free_m g" by (auto simp: ac_simps)
qed
end

context poly_mod_type
begin
lemma euclid_ext_poly_no_gcd_mod_int: assumes f: "(F :: 'a mod_ring poly) = of_int_poly f"
  and g: "(G :: 'a mod_ring poly) = of_int_poly g" 
  and cop: "coprime_m f g" 
  and fact: "euclid_ext_poly_no_gcd F G = (A,B)" 
  and a: "a = to_int_poly A"
  and b: "b = to_int_poly B"
  shows "f * a + g * b =m 1" 
proof -
  have f[transfer_rule]: "MP_Rel f F" unfolding f MP_Rel_def by (simp add: Mp_f_representative)
  have g[transfer_rule]: "MP_Rel g G" unfolding g MP_Rel_def by (simp add: Mp_f_representative)
  have [transfer_rule]: "MP_Rel a A" unfolding a MP_Rel_def by (rule Mp_to_int_poly)
  have [transfer_rule]: "MP_Rel b B" unfolding b MP_Rel_def by (rule Mp_to_int_poly)
  from cop have "coprime F G" using coprime_MP_Rel[unfolded rel_fun_def] f g by auto
  from euclid_ext_poly_no_gcd[OF this fact]
  have "F * A + G * B = 1" .
  from this[untransferred]
  show ?thesis .
qed
end
  
definition euclid_ext_poly_no_gcd_i :: "'i arith_ops_record \<Rightarrow> 'i list \<Rightarrow> 'i list \<Rightarrow> 'i list \<times> 'i list" where
  "euclid_ext_poly_no_gcd_i ff_ops f g = (case euclid_ext_poly_i ff_ops f g of 
      (a,b,_) \<Rightarrow> (a, b))" 

definition euclid_ext_poly_mod_main :: "int \<Rightarrow> 'a arith_ops_record \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> int poly \<times> int poly" where
  "euclid_ext_poly_mod_main p ff_ops f g = (case euclid_ext_poly_no_gcd_i ff_ops (of_int_poly_i ff_ops f) (of_int_poly_i ff_ops g) of 
      (a,b) \<Rightarrow> (to_int_poly_i ff_ops a, to_int_poly_i ff_ops b))" 

definition euclid_ext_poly_mod :: "int \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> int poly \<times> int poly" where
  "euclid_ext_poly_mod p = ( 
    if p \<le> 65535 
    then euclid_ext_poly_mod_main p (finite_field_ops32 (uint32_of_int p))
    else euclid_ext_poly_mod_main p (finite_field_ops p))" 
  
context prime_field_gen
begin
lemma euclid_ext_poly_no_gcd_i[transfer_rule]: 
  "(poly_rel ===> poly_rel ===> rel_prod poly_rel poly_rel)
     (euclid_ext_poly_no_gcd_i ff_ops) euclid_ext_poly_no_gcd"
  unfolding euclid_ext_poly_no_gcd_i_def[abs_def] euclid_ext_poly_no_gcd_def[abs_def]
  by transfer_prover


lemma euclid_ext_poly_no_gcd_i_sound: assumes f: "f' = of_int_poly_i ff_ops f" "Mp f = f"
  and g: "g' = of_int_poly_i ff_ops g" "Mp g = g"  
  and cop: "coprime_m f g" 
  and res: "euclid_ext_poly_no_gcd_i ff_ops f' g' = (a',b')" 
  and a: "a = to_int_poly_i ff_ops a'"
  and b: "b = to_int_poly_i ff_ops b'"
  shows "f * a + g * b =m 1" 
proof -
  from f have f': "f' = of_int_poly_i ff_ops (Mp f)" by simp
  define f'' where "f'' \<equiv> of_int_poly (Mp f) :: 'a mod_ring poly"
  have f'': "f'' = of_int_poly f" unfolding f''_def f by simp
  have rel_f[transfer_rule]: "poly_rel f' f''" 
    by (rule poly_rel_coeffs_Mp_of_int_poly[OF f'], simp add: f'' f)
  from g have g': "g' = of_int_poly_i ff_ops (Mp g)" by simp
  define g'' where "g'' \<equiv> of_int_poly (Mp g) :: 'a mod_ring poly"
  have g'': "g'' = of_int_poly g" unfolding g''_def g by simp
  have rel_g[transfer_rule]: "poly_rel g' g''"     
    by (rule poly_rel_coeffs_Mp_of_int_poly[OF g'], simp add: g'' g)
  obtain a'' b'' where eucl: "euclid_ext_poly_no_gcd f'' g'' = (a'',b'')" by force
  from euclid_ext_poly_no_gcd_i[unfolded rel_fun_def rel_prod_conv, rule_format, OF rel_f rel_g,
    unfolded res split eucl]
  have rel[transfer_rule]: "poly_rel a' a''" "poly_rel b' b''" by auto
  with to_int_poly_i have a: "a = to_int_poly a''" 
    and b: "b = to_int_poly b''" unfolding a b by auto
  from euclid_ext_poly_no_gcd_mod_int[OF f'' g'' cop eucl a b]
  show ?thesis .
qed

lemma euclid_ext_poly_mod_main: assumes cop: "coprime_m f g" 
  and f: "Mp f = f" and g: "Mp g = g" 
  and res: "euclid_ext_poly_mod_main m ff_ops f g = (a,b)" 
shows "f * a + g * b =m 1" 
proof -
  obtain a' b' where res': "euclid_ext_poly_no_gcd_i ff_ops (of_int_poly_i ff_ops f) 
    (of_int_poly_i ff_ops g) = (a', b')" by force
  show ?thesis
    by (rule euclid_ext_poly_no_gcd_i_sound[OF refl f refl g cop res'], insert
    res[unfolded euclid_ext_poly_mod_main_def res'], auto)
qed
end

context poly_mod
begin

lemma euclid_ext_poly_mod_int: assumes cop: "coprime_m f g" 
  and f: "Mp f = f" and g: "Mp g = g" 
  and p: "prime m" 
  and res: "euclid_ext_poly_mod_main m (finite_field_ops m) f g = (a,b)" 
  shows "f * a + g * b =m 1" 
proof -
  have ne: "{0..<m} \<noteq> {}" using prime_ge_2_int[OF p] by auto
  {
    assume "\<exists>(Rep :: 'b \<Rightarrow> int) Abs. type_definition Rep Abs {0 ..< m :: int}"
    from prime_type_prime_card[OF p this]
    have "class.prime_card TYPE('b)" "m = int CARD('b)" by auto
    from prime_field_gen.euclid_ext_poly_mod_main[OF prime_field.prime_field_finite_field_ops,
      unfolded prime_field_def mod_ring_locale_def,
      internalize_sort "'a :: prime_card", OF this cop f g res]
    have ?thesis.
  }
  from this[cancel_type_definition, OF ne]
  show ?thesis .
qed

lemma euclid_ext_poly_mod_uint32: assumes cop: "coprime_m f g" 
  and f: "Mp f = f" and g: "Mp g = g" 
  and p: "prime m" and small: "m \<le> 65535" 
  and res: "euclid_ext_poly_mod_main m (finite_field_ops32 (uint32_of_int m)) f g = (a,b)" 
  shows "f * a + g * b =m 1" 
proof -
  have ne: "{0..<m} \<noteq> {}" using prime_ge_2_int[OF p] by auto
  {
    assume "\<exists>(Rep :: 'b \<Rightarrow> int) Abs. type_definition Rep Abs {0 ..< m :: int}"
    from prime_type_prime_card[OF p this]
    have "class.prime_card TYPE('b)" "m = int CARD('b)" by auto
    from prime_field_gen.euclid_ext_poly_mod_main[OF prime_field.prime_field_finite_field_ops32,
      unfolded prime_field_def mod_ring_locale_def, 
      internalize_sort "'a :: prime_card", OF this small cop f g res]
    have ?thesis .
  }
  from this[cancel_type_definition, OF ne]
  show ?thesis .
qed

lemma euclid_ext_poly_mod: assumes cop: "coprime_m f g" 
  and f: "Mp f = f" and g: "Mp g = g" 
  and p: "prime m" 
  and res: "euclid_ext_poly_mod m f g = (a,b)" 
shows "f * a + g * b =m 1" 
  using euclid_ext_poly_mod_int[OF cop f g p, of a b]
    euclid_ext_poly_mod_uint32[OF cop f g p, of a b]
    res[unfolded euclid_ext_poly_mod_def] by (auto split: if_splits)
end


context poly_mod_2
begin

lemma Mp_ident_iff: "Mp f = f \<longleftrightarrow> (\<forall> n. coeff f n \<in> {0 ..< m})" 
proof -
  have m0: "m > 0" using m1 by simp
  show ?thesis unfolding poly_eq_iff Mp_coeff M_def mod_ident_iff[OF m0] by simp
qed

lemma Mp_ident_iff': "Mp f = f \<longleftrightarrow> (set (coeffs f) \<subseteq> {0 ..< m})" 
proof -
  have 0: "0 \<in> {0 ..< m}" using m1 by auto
  have ran: "(\<forall>n. coeff f n \<in> {0..<m}) \<longleftrightarrow> range (coeff f) \<subseteq> {0 ..< m}" by blast
  show ?thesis unfolding Mp_ident_iff ran using range_coeff[of f] 0 by auto
qed
end

lemma range_sum_prod: assumes xy: "x \<in> {0..<q}" "(y :: int) \<in> {0..<p}" 
  shows "x + q * y \<in> {0..<p * q}"
proof -
  {
    fix x q :: int
    have "x \<in> {0 ..< q} \<longleftrightarrow> 0 \<le> x \<and> x < q" by auto
  } note id = this
  from xy have 0: "0 \<le> x + q * y" by auto
  have "x + q * y \<le> q - 1 + q * y" using xy by simp
  also have "q * y \<le> q * (p - 1)" using xy by auto
  finally have "x + q * y \<le> q - 1 + q * (p - 1)" by auto
  also have "\<dots> = p * q - 1" by (simp add: field_simps)
  finally show ?thesis using 0 by auto
qed

context poly_mod
begin

definition Dp :: "int poly \<Rightarrow> int poly" where
  "Dp f = map_poly (\<lambda> a. a div m) f" 

lemma Dp_Mp_eq: "f = Mp f + smult m (Dp f)"
  by (rule poly_eqI, auto simp: Mp_coeff M_def Dp_def coeff_map_poly)
end

context 
  fixes C :: "int poly" 
begin

context
  fixes p :: int and S T D1 H1 :: "int poly" 
begin
(* The linear lifting is implemented for ease of provability.
   Aim: show uniqueness of factorization *)
fun linear_hensel_main where 
  "linear_hensel_main (Suc 0) = (D1,H1)" 
| "linear_hensel_main (Suc n) = (
      let (D,H) = linear_hensel_main n;
        q = p ^ n;
        U = div_poly q (C - D * H);   (* H2 *)
        U = poly_mod.Mp p U;          (* H3 *)
        (A,B) = poly_mod.dupe_monic p D1 H1 S T U
      in (D + smult q B, H + smult q A))" (* H4 *)
    | "linear_hensel_main 0 = (D1,H1)" 
  
lemma linear_hensel_code[code]: "linear_hensel_main n = (if n \<le> 1 then (D1,H1) else
  let n1 = n - 1;
    (D,H) = linear_hensel_main n1;
        q = p ^ n1;
        U = div_poly q (C - D * H);  
        U = poly_mod.Mp p U;         
        (A,B) = poly_mod.dupe_monic p D1 H1 S T U
      in (D + smult q B, H + smult q A))"
  by (cases n, force, cases "n - 1", auto)


lemma linear_hensel_main: assumes 1: "poly_mod.equivalent p (D1 * S + H1 * T) 1" 
  and equiv: "poly_mod.equivalent p C (D1 * H1)"
  and monD1: "monic D1" 
  and normDH1: "poly_mod.Mp p D1 = D1" "poly_mod.Mp p H1 = H1"  
  and res: "linear_hensel_main n = (D,H)" 
  and n: "n \<noteq> 0" 
  and prime: "prime p" (* p > 1 suffices if one does not need uniqueness *)
  and cop: "poly_mod.coprime_m p D1 H1" 
  shows "poly_mod.equivalent (p^n) C (D * H) 
    \<and> monic D
    \<and> poly_mod.equivalent p D1 D \<and> poly_mod.equivalent p H1 H
    \<and> poly_mod.Mp (p^n) D = D
    \<and> poly_mod.Mp (p^n) H = H \<and> 
    (poly_mod.equivalent (p^n) C (D' * H') \<longrightarrow>
     poly_mod.equivalent p D1 D' \<longrightarrow> 
     poly_mod.equivalent p H1 H' \<longrightarrow>
     poly_mod.Mp (p^n) D' = D' \<longrightarrow>
     poly_mod.Mp (p^n) H' = H' \<longrightarrow> monic D' \<longrightarrow> D' = D \<and> H' = H)
     " 
  using res n 
proof (induct n arbitrary: D H D' H')
  case (Suc n D' H' D'' H'')
  show ?case
  proof (cases "n = 0")
    case True
    with Suc equiv monD1 normDH1 show ?thesis by (auto simp: poly_mod.equivalent_def)
  next
    case False
    hence n: "n \<noteq> 0" by auto
    let ?q = "p^n"
    let ?pq = "p * p^n"
    from prime have p: "p > 1" using prime_gt_1_int by force
    from n p have q: "?q > 1" by auto
    from n p have pq: "?pq > 1" by (metis power_gt1_lemma)
    interpret p: poly_mod_2 p using p unfolding poly_mod_2_def .
    interpret q: poly_mod_2 ?q using q unfolding poly_mod_2_def .
    interpret pq: poly_mod_2 ?pq using pq unfolding poly_mod_2_def .
    obtain D H where rec: "linear_hensel_main n = (D,H)" by force
    obtain V where V: "div_poly (p ^ n) (C - D * H) = V" by force
    obtain U where U: "p.Mp (div_poly ?q (C - D * H)) = U" by auto
    obtain A B where dupe: "p.dupe_monic D1 H1 S T U = (A,B)" by force
    note IH = Suc(1)[OF rec n]
    from IH
    have CDH: "q.equivalent C (D * H)" 
      and monD: "monic D"
      and p_eq: "p.equivalent D1 D" "p.equivalent H1 H" 
      and norm: "q.Mp D = D" "q.Mp H = H" by auto
    from n obtain k where n: "n = Suc k" by (cases n, auto)
    have qq: "?q * ?q = ?pq * p^k" unfolding n by simp
    from Suc(2)[unfolded n linear_hensel_main.simps, folded n, unfolded rec split Let_def U dupe]
    have D': "D' = D + smult ?q B" and H': "H' = H + smult ?q A" by auto
    note dupe = p.dupe_monic[OF 1 monD1 dupe]
    from CDH[unfolded q.equivalent_def] have "q.Mp C - q.Mp (D * H) = 0" by simp
    hence "q.Mp (q.Mp C - q.Mp (D * H)) = 0" by simp
    hence "q.Mp (C - D*H) = 0" by simp
    from q.Mp_0_smult_div_poly[OF this] have CDHq: "smult ?q (div_poly ?q (C - D * H)) = C - D * H" .
    have ADBHU: "p.equivalent (A * D + B * H) U" using p_eq dupe(1) 
      unfolding p.equivalent_def by (metis (mono_tags, lifting) p.mult_Mp(2) poly_mod.plus_Mp)
    
    have "pq.Mp (D' * H') = pq.Mp ((D + smult ?q B) * (H + smult ?q A))" 
      unfolding D' H' by simp
    also have "(D + smult ?q B) * (H + smult ?q A) = (D * H + smult ?q (A * D + B * H)) + smult (?q * ?q) (A * B)" 
      by (simp add: field_simps smult_distribs)
    also have "pq.Mp \<dots> = pq.Mp (D * H + pq.Mp (smult ?q (A * D + B * H)) + pq.Mp (smult (?q * ?q) (A * B)))"
      using pq.plus_Mp by metis
    also have "pq.Mp (smult (?q * ?q) (A * B)) = 0" unfolding qq
      by (metis pq.Mp_smult_m_0 smult_smult)
    finally have DH': "pq.Mp (D' * H') = pq.Mp (D * H + pq.Mp (smult ?q (A * D + B * H)))" by simp
    also have "pq.Mp (smult ?q (A * D + B * H)) = pq.Mp (smult ?q U)"
      using p.Mp_lift_modulus[OF ADBHU, of ?q] unfolding pq.equivalent_def by simp
    also have "\<dots> = pq.Mp (C - D * H)" 
      unfolding arg_cong[OF CDHq, of pq.Mp, symmetric] U[symmetric] V
      by (rule p.Mp_lift_modulus[of _ _ ?q, unfolded pq.equivalent_def], auto simp: p.equivalent_def) 
    also have "pq.Mp (D * H + pq.Mp (C - D * H)) = pq.Mp C" by simp
    finally have CDH: "pq.equivalent C (D' * H')" unfolding pq.equivalent_def by simp

    have deg: "degree D1 = degree D" using p_eq(1) monD1 monD
      by (metis p.equivalent_def p.monic_degree_Mp)
    have mon: "monic D'" unfolding D' using dupe(2) monD unfolding deg by (rule monic_smult_add_small)
    have normD': "pq.Mp D' = D'" 
      unfolding D' pq.Mp_ident_iff poly_mod.Mp_coeff plus_poly.rep_eq coeff_smult 
    proof 
      fix i
      from norm(1) dupe(4) have "coeff D i \<in> {0..<?q}" "coeff B i \<in> {0..<p}" 
        unfolding p.Mp_ident_iff q.Mp_ident_iff by auto
      thus "coeff D i + ?q * coeff B i \<in> {0..< ?pq}" by (rule range_sum_prod)
    qed
    have normH': "pq.Mp H' = H'" 
      unfolding H' pq.Mp_ident_iff poly_mod.Mp_coeff plus_poly.rep_eq coeff_smult 
    proof 
      fix i
      from norm(2) dupe(3) have "coeff H i \<in> {0..<?q}" "coeff A i \<in> {0..<p}" 
        unfolding p.Mp_ident_iff q.Mp_ident_iff by auto
      thus "coeff H i + ?q * coeff A i \<in> {0..< ?pq}" by (rule range_sum_prod)
    qed
    have eq: "p.equivalent D D'" "p.equivalent H H'" unfolding D' H' p.equivalent_def n 
        poly_eq_iff p.Mp_coeff p.M_def by (auto simp: field_simps)
    with p_eq have eq: "p.equivalent D1 D'" "p.equivalent H1 H'" unfolding p.equivalent_def by auto
    {
      assume CDH'': "pq.equivalent C (D'' * H'')" 
        and DH1'': "p.equivalent D1 D''" "p.equivalent H1 H''"
        and norm'': "pq.Mp D'' = D''" "pq.Mp H'' = H''" 
        and monD'': "monic D''" 
      from q.Dp_Mp_eq[of D''] obtain d B' where D'': "D'' = q.Mp d + smult ?q B'" by auto
      from q.Dp_Mp_eq[of H''] obtain h A' where H'': "H'' = q.Mp h + smult ?q A'" by auto
      {
        fix A B
        assume *: "pq.Mp (q.Mp A + smult ?q B) = q.Mp A + smult ?q B" 
        have "p.Mp B = B" unfolding p.Mp_ident_iff
        proof 
          fix i
          from arg_cong[OF *, of "\<lambda> f. coeff f i", unfolded pq.Mp_coeff pq.M_def]
          have "coeff (q.Mp A + smult ?q B) i \<in> {0 ..< ?pq}" using "*" pq.Mp_ident_iff by blast 
          hence sum: "coeff (q.Mp A) i + ?q * coeff B i \<in> {0 ..< ?pq}" by auto
          have "q.Mp (q.Mp A) = q.Mp A" by auto
          from this[unfolded q.Mp_ident_iff] have A: "coeff (q.Mp A) i \<in> {0 ..< p^n}" by auto
          {
            assume "coeff B i < 0" hence "coeff B i \<le> -1" by auto
            from mult_left_mono[OF this, of ?q] q.m1 have "?q * coeff B i \<le> -?q" by simp
            with A sum have False by auto
          } hence "coeff B i \<ge> 0" by force
          moreover
          {
            assume "coeff B i \<ge> p" 
            from mult_left_mono[OF this, of ?q] q.m1 have "?q * coeff B i \<ge> ?pq" by simp
            with A sum have False by auto
          } hence "coeff B i < p" by force
          ultimately show "coeff B i \<in> {0 ..< p}" by auto
        qed
      } note norm_convert = this
      from norm_convert[OF norm''(1)[unfolded D'']] have normB': "p.Mp B' = B'" . 
      from norm_convert[OF norm''(2)[unfolded H'']] have normA': "p.Mp A' = A'" . 
      let ?d = "q.Mp d" 
      let ?h = "q.Mp h"
      {
        assume lt: "degree ?d < degree B'"
        hence eq: "degree D'' = degree B'" unfolding D'' using q.m1 p.m1
          by (subst degree_add_eq_right, auto)
        from lt have [simp]: "coeff ?d (degree B') = 0" by (rule coeff_eq_0)
        from monD''[unfolded eq, unfolded D'', simplified] False q.m1 lt have False
          by (metis mod_mult_self1_is_0 poly_mod.M_def q.M_1 zero_neq_one)
      }
      hence deg_dB': "degree ?d \<ge> degree B'" by presburger
      {
        assume eq: "degree ?d = degree B'" and B': "B' \<noteq> 0"  
        let ?B = "coeff B' (degree B')" 
        from normB'[unfolded p.Mp_ident_iff, rule_format, of "degree B'"] B'
        have "?B \<in> {0..<p} - {0}" by simp
        hence bnds: "?B > 0" "?B < p" by auto
        have degD'': "degree D'' \<le> degree ?d" unfolding D'' using eq by (simp add: degree_add_le)
        have "?q * ?B \<ge> 1 * 1" by (rule mult_mono, insert q.m1 bnds, auto) 
        moreover have "coeff D'' (degree ?d) = 1 + ?q * ?B" using monD''
          unfolding D'' using eq 
          by (metis D'' coeff_smult monD'' plus_poly.rep_eq poly_mod.Dp_Mp_eq 
              poly_mod.degree_m_eq_monic poly_mod.plus_Mp(1) 
              q.Mp_smult_m_0 q.degree_m_def q.m1 q.monic_Mp q.plus_Mp(2))
        ultimately have gt: "coeff D'' (degree ?d) > 1" by auto
        hence "coeff D'' (degree ?d) \<noteq> 0" by auto
        hence "degree D'' \<ge> degree ?d" by (rule le_degree)
        with degree_add_le_max[of ?d "smult ?q B'", folded D''] eq 
        have deg: "degree D'' = degree ?d" using degD'' by linarith
        from gt[folded this] have "\<not> monic D''" by auto
        with monD'' have False by auto
      }
      with deg_dB' have deg_dB2: "B' = 0 \<or> degree B' < degree ?d" by fastforce
      have d: "q.Mp D'' = ?d" unfolding D''
        by (metis add.right_neutral poly_mod.Mp_smult_m_0 poly_mod.plus_Mp)
      have h: "q.Mp H'' = ?h" unfolding H''
        by (metis add.right_neutral poly_mod.Mp_smult_m_0 poly_mod.plus_Mp)
      from CDH'' have "pq.Mp C = pq.Mp (D'' * H'')" unfolding pq.equivalent_def by simp
      from arg_cong[OF this, of q.Mp] 
      have "q.Mp C = q.Mp (D'' * H'')"
        using p.m1 q.Mp_product_modulus by auto
      also have "\<dots> = q.Mp (q.Mp D'' * q.Mp H'')" by simp
      also have "\<dots> = q.Mp (?d * ?h)" unfolding d h by simp
      finally have eqC: "q.equivalent C (?d * ?h)" unfolding q.equivalent_def .
      have d1: "p.equivalent D1 ?d" unfolding d[symmetric] using DH1'' unfolding p.equivalent_def
        using assms(4) n p.Mp_product_modulus p.m1 by auto
      have h1: "p.equivalent H1 ?h" unfolding h[symmetric] using DH1'' unfolding p.equivalent_def
        using assms(5) n p.Mp_product_modulus p.m1 by auto
      have mond: "monic (q.Mp d)" using monD'' deg_dB2 unfolding D''
        using d monD'' q.monic_Mp by force
      from eqC d1 h1 mond IH[of "q.Mp d" "q.Mp h"] have IH: "?d = D" "?h = H" by auto
      from deg_dB2[unfolded IH] have degB': "B' = 0 \<or> degree B' < degree D" by auto
      from IH have D'': "D'' = D + smult ?q B'" and H'': "H'' = H + smult ?q A'" 
        unfolding D'' H'' by auto
      have "pq.Mp (D'' * H'') = pq.Mp (D' * H')" using CDH'' CDH unfolding pq.equivalent_def by simp
      also have "pq.Mp (D'' * H'') = pq.Mp ((D + smult ?q B') * (H + smult ?q A'))" 
        unfolding D'' H'' by simp
      also have "(D + smult ?q B') * (H + smult ?q A') = (D * H + smult ?q (A' * D + B' * H)) + smult (?q * ?q) (A' * B')" 
        by (simp add: field_simps smult_distribs)
      also have "pq.Mp \<dots> = pq.Mp (D * H + pq.Mp (smult ?q (A' * D + B' * H)) + pq.Mp (smult (?q * ?q) (A' * B')))"
        using pq.plus_Mp by metis
      also have "pq.Mp (smult (?q * ?q) (A' * B')) = 0" unfolding qq
        by (metis pq.Mp_smult_m_0 smult_smult)
      finally have "pq.Mp (D * H + pq.Mp (smult ?q (A' * D + B' * H))) 
        = pq.Mp (D * H + pq.Mp (smult ?q (A * D + B * H)))" unfolding DH' by simp
      hence "pq.Mp (smult ?q (A' * D + B' * H)) = pq.Mp (smult ?q (A * D + B * H))"
        by (metis (no_types, lifting) add_diff_cancel_left' poly_mod.minus_Mp(1) poly_mod.plus_Mp(2))
      hence "p.Mp (A' * D + B' * H) = p.Mp (A * D + B * H)" unfolding poly_eq_iff p.Mp_coeff pq.Mp_coeff coeff_smult
        by (insert p, auto simp: p.M_def pq.M_def)
      hence "p.Mp (A' * D1 + B' * H1) = p.Mp (A * D1 + B * H1)" using p_eq unfolding p.equivalent_def 
        by (metis p.mult_Mp(2) poly_mod.plus_Mp)
      hence eq: "p.equivalent (A' * D1 + B' * H1) U" using dupe(1) unfolding p.equivalent_def by auto
      have "degree D = degree D1" using monD monD1 
          arg_cong[OF p_eq(1)[unfolded p.equivalent_def], of degree] 
          p.degree_m_eq_monic[OF _ p.m1, unfolded p.degree_m_def] by auto
      hence "B' = 0 \<or> degree B' < degree D1" using degB' by simp
      from dupe(5)[OF cop eq this normDH1(1) normA' normB' prime] have "A' = A" "B' = B" by auto
      hence "D'' = D'" "H'' = H'" unfolding D'' H'' D' H' by auto
    }
    thus ?thesis using normD' normH' CDH mon eq by simp
  qed
qed simp
end
end

definition linear_hensel_binary :: "int \<Rightarrow> nat \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> int poly \<times> int poly" where
  "linear_hensel_binary p n C D H = (let
     (S,T) = euclid_ext_poly_mod p D H
     in linear_hensel_main C p S T D H n)"

lemma Mp_Mp_pow_is_Mp: "n \<noteq> 0 \<Longrightarrow> p > 1 \<Longrightarrow> poly_mod.Mp p (poly_mod.Mp (p^n) f) 
  = poly_mod.Mp p f"
  using  poly_mod_2.Mp_product_modulus poly_mod_2_def by(subst realpow_num_eq_if, auto)

lemma M_M_pow_is_M: "n \<noteq> 0 \<Longrightarrow> p > 1 \<Longrightarrow> poly_mod.M p (poly_mod.M (p^n) f) 
  = poly_mod.M p f" using Mp_Mp_pow_is_Mp[of n p "[:f:]"]
  by (metis coeff_pCons_0 poly_mod.Mp_coeff)

lemma irreducible_lifting: assumes p1: "p > 1"
  and n: "n \<noteq> 0" 
  and deg: "poly_mod.degree_m (p^n) f = poly_mod.degree_m p f" 
  and irr: "poly_mod.irreducible_m p f"
  shows "poly_mod.irreducible_m (p^n) f" 
proof -
  interpret poly_mod_2 "p^n" unfolding poly_mod_2_def using p1 n by simp
  interpret p: poly_mod_2 p unfolding poly_mod_2_def using p1 by simp
  note irr = irr[unfolded p.irreducible_m_def]
  show "irreducible_m f" unfolding irreducible_m_def dvdm_def
  proof (intro conjI allI impI notI)
    from deg irr show "degree_m f = 0 \<Longrightarrow> False" by simp
    note pMp_Mp = Mp_Mp_pow_is_Mp[OF n p1]
    fix h g
    assume deg_g: "degree_m g < degree_m f" "degree_m h < degree_m f" and
      eq: "equivalent f (g * h)" 
    have le: "\<And> g. p.degree_m g \<le> degree_m g" 
      by (metis pMp_Mp poly_mod.degree_m_def poly_mod.degree_m_le)
    from deg_g le[of g] le[of h] deg 
    have lt: "p.degree_m g < p.degree_m f" "p.degree_m h < p.degree_m f" by auto
    from eq have eq: "Mp f = Mp (g * h)" unfolding equivalent_def by auto
    from arg_cong[OF eq, of p.Mp]
    have p_eq: "p.equivalent f (g * h)" 
      by (auto simp: pMp_Mp p.equivalent_def ac_simps)
    with irr[unfolded p.dvdm_def] lt show False by auto 
  qed
qed  

definition inverse_mod :: "int \<Rightarrow> int \<Rightarrow> int" where
  "inverse_mod x m = (case euclid_ext x m of (a,b,g) \<Rightarrow> a)" 

lemma inverse_mod: assumes "coprime x m" "m > 1" shows "(inverse_mod x m * x) mod m = 1" 
proof (cases "euclid_ext x m")
  case (fields i a g)
  from euclid_ext_correct[of x m, unfolded this split assms] have i: "i * x + a * m = g" by simp
  from arg_cong[OF this, of "\<lambda> x. x mod m"] assms(2) have "(i * x) mod m = 1"
    by (simp add: \<open>i * x + a * m = g \<and> g = 1\<close> add.commute)
  thus ?thesis unfolding inverse_mod_def fields split .
qed

lemma inverse_mod_pow: assumes "coprime x p" "p > 1" "n \<noteq> 0" 
  shows "(inverse_mod x (p^n) * x) mod (p^n) = 1" 
  by (rule inverse_mod[OF coprime_exp[OF assms(1)]], insert assms, simp) 

lemma (in poly_mod) inverse_mod_coprime: assumes p: "prime m" 
  and cop: "coprime x m" shows "M (inverse_mod x m * x) = 1" 
  unfolding M_def using inverse_mod_pow[OF cop, of 1] p
  by (auto simp: prime_int_iff)

lemma (in poly_mod) inverse_mod_coprime_exp: assumes m: "m = p^n" and p: "prime p" 
  and n: "n \<noteq> 0" and cop: "coprime x p" shows "M (inverse_mod x m * x) = 1" 
  unfolding M_def unfolding m using inverse_mod_pow[OF cop _ n] p
  by (auto simp: prime_int_iff)

locale poly_mod_prime = poly_mod p for p :: int +
  assumes prime: "prime p" 
begin

sublocale poly_mod_2 p using prime unfolding poly_mod_2_def
  using prime_gt_1_int by force

lemma square_free_m_prod_imp_coprime_m: assumes sf: "square_free_m (A * B)" 
  shows "coprime_m A B" 
  unfolding coprime_m_def
proof
  fix h
  {
    assume "dvdm h 1"
    then obtain k where 1: "Mp (h * k) = 1" unfolding dvdm_def equivalent_def by auto
    hence "dvdm h A \<and> dvdm h B" unfolding dvdm_def equivalent_def 
    proof (intro conjI exI) 
      have "Mp A = Mp (Mp (h * k) * A)" unfolding 1 by simp
      also have "\<dots> = Mp (h * (k * A))" by (simp add: ac_simps)
      finally show "Mp A = Mp (h * (k * A))" .
      have "Mp B = Mp (Mp (h * k) * B)" unfolding 1 by simp
      also have "\<dots> = Mp (h * (k * B))" by (simp add: ac_simps)
      finally show "Mp B = Mp (h * (k * B))" .
    qed
  }
  moreover
  {
    assume dvd: "dvdm h A" "dvdm h B" 
    then obtain ha hb where *: "Mp A = Mp (h * ha)" "Mp B = Mp (h * hb)" 
      unfolding dvdm_def equivalent_def by auto
    have AB: "Mp (A * B) = Mp (Mp A * Mp B)" by simp
    from this[unfolded *, simplified] 
    have eq: "Mp (A * B) = Mp (h * h * (ha * hb))" by (simp add: ac_simps)
    hence dvd_hh: "dvdm (h * h) (A * B)" unfolding dvdm_def equivalent_def by auto
    {
      assume "degree_m h \<noteq> 0" 
      from sf[unfolded square_free_m_def, THEN conjunct2, rule_format, OF this]
      have "\<not> dvdm (h * h) (A * B)" . 
      with dvd_hh have False by simp
    }
    hence "degree (Mp h) = 0" unfolding degree_m_def by auto
    then obtain c where hc: "Mp h = [: c :]" by (rule degree_eq_zeroE)
    {
      assume "c = 0" 
      hence "Mp h = 0" unfolding hc by auto
      with *(1) have "Mp A = 0"
        by (metis Mp_0 mult_zero_left poly_mod.mult_Mp(1))
      with sf[unfolded square_free_m_def, THEN conjunct1] have False unfolding equivalent_def
        by (simp add: AB)
    }
    hence c0: "c \<noteq> 0" by auto    
    with arg_cong[OF hc[symmetric], of "\<lambda> f. coeff f 0", unfolded Mp_coeff M_def] m1
    have "c \<ge> 0" "c < p" by auto
    with c0 have c_props:"c > 0" "c < p" by auto
    with prime have "prime p" using prime_int_nat_transfer by auto
    hence "coprime p c"
      by (metis (no_types) c_props gcd_dvd1 gcd_ge_0_int gcd_le2_int not_less prime_int_iff)
    hence "coprime c p" by (simp add: gcd.commute)
    from inverse_mod_coprime[OF prime this]
    obtain d where d: "M (c * d) = 1" by (auto simp: ac_simps)
    have "dvdm h 1" unfolding dvdm_def equivalent_def 
    proof (intro exI[of _ "[:d:]"])
      have "Mp (h * [: d :]) = Mp (Mp h * [: d :])" by simp
      also have "\<dots> = Mp ([: c * d :])" unfolding hc by (auto simp: ac_simps)
      also have "\<dots> = [: M (c * d) :]" unfolding Mp_def
          by (metis (no_types) M_0 Missing_Polynomial.map_poly_pCons Mp_0 Mp_def d zero_neq_one)
      also have "\<dots> = 1" unfolding d one_poly_def by simp
      finally show "Mp 1 = Mp (h * [:d:])" by simp
    qed
  }
  ultimately show "(dvdm h A \<and> dvdm h B) = dvdm h 1" by auto
qed

lemma unique_hensel_binary: 
  assumes prime: "prime p"
  and cop: "coprime_m D H" and eq: "equivalent C (D * H)"
  and normalized_input: "Mp D = D" "Mp H = H"
  and monic_input: "monic D" 
  and n: "n \<noteq> 0" 
shows "\<exists>! (D',H'). (* D', H' are computed via linear_hensel_binary *)
      poly_mod.equivalent (p^n) C (D' * H') (* the main result: equivalence mod p^n *)
    \<and> monic D' (* monic output *)
    \<and> equivalent D D' \<and> equivalent H H' (* apply `mod p` on D' and H' yields D and H again *)
    \<and> poly_mod.Mp (p^n) D' = D' \<and> poly_mod.Mp (p^n) H' = H'" (* output is normalized *)
proof -
  obtain D' H' where hensel_result: "linear_hensel_binary p n C D H = (D',H')" by force
  from m1 have p: "p > 1" .
  obtain S T where ext: "euclid_ext_poly_mod p D H = (S,T)" by force
  obtain D1 H1 where main: "linear_hensel_main C p S T D H n = (D1,H1)" by force
  from hensel_result[unfolded linear_hensel_binary_def ext split Let_def main]
  have id: "D1 = D'" "H1 = H'" by auto
  from linear_hensel_main[OF euclid_ext_poly_mod[OF cop normalized_input prime ext] 
      eq monic_input normalized_input main[unfolded id] n prime cop] show ?thesis by auto
qed
end

(* The quadratic lifting is implemented more efficienty.
   Aim: compute factorization *)
context
  fixes C :: "int poly"
begin
fun quadratic_hensel_main where 
  "quadratic_hensel_main (Suc j) q S T D H = (
      let U = div_poly q (C - D * H) (* Z2 *)
        in if U = 0 then (D,H) else let (* optimization (iii) *)
        U = poly_mod.Mp q U;          (* Z3 *)
        (A,B) = poly_mod.dupe_monic q D H S T U;
        D' = D + smult q B; (* Z4 *)
        H' = H + smult q A;
        U' = div_poly q (S*D' + T*H' - 1); (* Z5 *)
        U' = poly_mod.Mp q U'; (* Z6 *)
        (A',B') = poly_mod.dupe_monic q D H S T U';
        q' = q * q;
        S' = poly_mod.Mp q' (S - smult q A'); (* Z7 *)
        T' = poly_mod.Mp q' (T - smult q B')
      in quadratic_hensel_main j q' S' T' D' H')" 
| "quadratic_hensel_main 0 q S T D H = (D,H)" 

lemma quadratic_hensel_main: assumes "poly_mod.equivalent q (D * S + H * T) 1"
  and "poly_mod.equivalent q C (D * H)" 
  and "monic D" 
  and "quadratic_hensel_main j q S T D H = (D',H')" 
  and "q > 1" 
  and "poly_mod.Mp q D = D" "poly_mod.Mp q H = H"  
  shows "poly_mod.equivalent (q^(2^j)) C (D' * H') \<and> monic D'
    \<and> poly_mod.equivalent q D D' \<and> poly_mod.equivalent q H H'
    \<and> poly_mod.Mp (q^(2^j)) D' = D'
    \<and> poly_mod.Mp (q^(2^j)) H' = H'" 
  using assms
proof (induct j arbitrary: q S T D H D' H')
  case 0
  thus ?case by (simp add: poly_mod.equivalent_def)
next
  case (Suc j q S T D H D'' H'')
  note res = Suc(5)
  note mon = Suc(4)
  note 1 = Suc(2)
  note CDH = Suc(3)
  note q = Suc(6)
  note D = Suc(7)
  note H = Suc(8)
  interpret poly_mod_2 q using q unfolding poly_mod_2_def .
  from q have qq: "q * q > 1" by (simp add: less_1_mult)
  interpret qq: poly_mod_2 "q * q" using qq unfolding poly_mod_2_def .  
  note dupe = dupe_monic[OF 1 mon]
  define U1 where "U1 \<equiv> Mp (div_poly q (C - D * H))" 
  from CDH[unfolded equivalent_def] have "Mp C - Mp (D * H) = 0" by simp
  hence "Mp (Mp C - Mp (D * H)) = 0" by simp
  hence "Mp (C - D*H) = 0" by simp
  from Mp_0_smult_div_poly[OF this] have CDHq: "smult q (div_poly q (C - D * H)) = C - D * H" .
  obtain A B where dupe1: "dupe_monic D H S T U1 = (A,B)" by force
  define D' where "D' \<equiv> D + smult q B" 
  define H' where "H' \<equiv> H + smult q A"
  define U2 where "U2 \<equiv> Mp (div_poly q (S * D' + T * H' - 1))" 
  obtain A' B' where dupe2: "dupe_monic D H S T U2 = (A',B')" by force
  define S' where "S' \<equiv> qq.Mp (S - smult q A')" 
  define T' where "T' \<equiv> qq.Mp (T - smult q B')" 
  show ?case
  proof (cases "div_poly q (C - D * H) = 0")
    case True
    with res have res: "D'' = D" "H'' = H" by auto
    from True CDHq have C: "C = D * H" by simp
    have "2 * 2 ^ j > (1 :: nat)" using one_less_numeral_iff power_gt1_lemma semiring_norm(76) 
      by blast
    hence "\<exists> k \<ge> 1. 2 * 2 ^ j = Suc k" by presburger
    then obtain k where id: "2 * 2 ^ j = Suc k" and k: "k \<ge> 1" by auto
    from q have [simp]: "q ^ k > 0" by auto
    show ?thesis unfolding res C using mon D H by (auto simp: poly_mod.equivalent_def id
      intro!: Mp_ident_product)
  next
    case False
    hence [simp]: "(div_poly q (C - D * H) = 0) = False" by simp
    from res[simplified, simplified, folded U1_def, unfolded dupe1 split Let_def, 
      folded D'_def H'_def, folded U2_def, unfolded dupe2 split, folded S'_def T'_def]
    have res: "quadratic_hensel_main j (q * q) S' T' D' H' = (D'', H'')" by auto
    note dupe1 = dupe[OF dupe1]
    note dupe2 = dupe[OF dupe2]  
    have "qq.Mp (D' * H') = qq.Mp ((D + smult q B) * (H + smult q A))" 
      unfolding D'_def H'_def by simp
    also have "(D + smult q B) * (H + smult q A) = (D * H + smult q (A * D + B * H)) + smult (q * q) (A * B)" 
      by (simp add: field_simps smult_distribs)
    also have "qq.Mp \<dots> = qq.Mp (D * H + qq.Mp (smult q (A * D + B * H)) + qq.Mp (smult (q * q) (A * B)))"
      using qq.plus_Mp by metis
    also have "qq.Mp (smult (q * q) (A * B)) = 0" by simp
    also have "qq.Mp (smult q (A * D + B * H)) = qq.Mp (smult q U1)" 
      using Mp_lift_modulus[OF dupe1(1), of q] unfolding qq.equivalent_def by simp
    also have "\<dots> = qq.Mp (C - D * H)" 
      unfolding arg_cong[OF CDHq, of qq.Mp, symmetric]
      using Mp_lift_modulus[of U1 "div_poly q (C - D * H)" q] unfolding poly_mod.equivalent_def U1_def 
      by simp
    also have "qq.Mp (D * H + qq.Mp (C - D * H) + 0) = qq.Mp C" by simp
    finally have CDH: "qq.equivalent C (D' * H')" unfolding qq.equivalent_def by simp
    have mon: "monic D'" unfolding D'_def using dupe1(2) mon by (rule monic_smult_add_small)
    have "Mp (S * D' + T * H' - 1) = Mp (Mp (D * S + H * T) + (smult q (S * B + T * A) - 1))" 
      unfolding D'_def H'_def plus_Mp by (simp add: field_simps smult_distribs)
    also have "Mp (D * S + H * T) = 1" using 1[unfolded equivalent_def] by simp
    also have "Mp (1 + (smult q (S * B + T * A) - 1)) = 0" by simp
    finally have "Mp (S * D' + T * H' - 1) = 0" .
    from Mp_0_smult_div_poly[OF this] 
    have SDTH: "smult q (div_poly q (S * D' + T * H' - 1)) = S * D' + T * H' - 1" .
    have "qq.Mp (D' * S' + H' * T') = 
      qq.Mp ((D + smult q B) * (S - smult q A') + (H + smult q A) * (T - smult q B'))"
      unfolding D'_def S'_def H'_def T'_def using qq.plus_Mp qq.mult_Mp by metis
    also have "\<dots> = qq.Mp ((D * S + H * T +
      smult q (B * S + A * T)) - smult q (A' * D + B' * H) - smult (q * q) (A * B' + B * A'))" 
      by (simp add: field_simps smult_distribs)
    also have "\<dots> = qq.Mp ((D * S + H * T +
      smult q (B * S + A * T)) - qq.Mp (smult q (A' * D + B' * H)) - qq.Mp (smult (q * q) (A * B' + B * A')))"
      using qq.plus_Mp qq.minus_Mp by metis
    also have "qq.Mp (smult (q * q) (A * B' + B * A')) = 0" by simp
    also have "qq.Mp (smult q (A' * D + B' * H)) = qq.Mp (smult q U2)" 
      using Mp_lift_modulus[OF dupe2(1), of q] unfolding qq.equivalent_def by simp
    also have "\<dots> = qq.Mp (S * D' + T * H' - 1)" 
      unfolding arg_cong[OF SDTH, of qq.Mp, symmetric]
      using Mp_lift_modulus[of U2 "div_poly q (S * D' + T * H' - 1)" q] 
      unfolding poly_mod.equivalent_def U2_def 
      by simp
    also have "S * D' + T * H' - 1 = S * D + T * H + smult q (B * S + A * T) - 1" 
      unfolding D'_def H'_def by (simp add: field_simps smult_distribs)
    also have "qq.Mp (D * S + H * T + smult q (B * S + A * T) -
       qq.Mp (S * D + T * H + smult q (B * S + A * T) - 1) - 0) 
         = 1" by simp
    finally have 1: "qq.equivalent (D' * S' + H' * T') 1" 
      unfolding qq.equivalent_def by simp
    have qq22: "q ^ (2 * 2 ^ j) = (q * q) ^ (2 ^ j)"
      by (simp add: power_mult_distrib semiring_normalization_rules(30-))
    have D': "qq.Mp D' = D'" unfolding D'_def qq.Mp_ident_iff poly_mod.Mp_coeff plus_poly.rep_eq
      coeff_smult 
    proof 
      fix n
      from D dupe1(4) have "coeff D n \<in> {0..<q}" "coeff B n \<in> {0..<q}" unfolding Mp_ident_iff by auto
      thus "coeff D n + q * coeff B n \<in> {0..<q * q}" using q by (metis range_sum_prod)
    qed
    have H': "qq.Mp H' = H'" unfolding H'_def qq.Mp_ident_iff poly_mod.Mp_coeff plus_poly.rep_eq
      coeff_smult 
    proof 
      fix n
      from H dupe1(3) have "coeff H n \<in> {0..<q}" "coeff A n \<in> {0..<q}" unfolding Mp_ident_iff by auto
      thus "coeff H n + q * coeff A n \<in> {0..<q * q}" using q by (metis range_sum_prod)
    qed
    note IH = Suc(1)[OF 1 CDH mon res qq D' H']
    from IH have "qq.equivalent D' D''" "qq.equivalent H' H''" by auto
    hence "equivalent D' D''" "equivalent H' H''" using Mp_shrink_modulus[of q] q by auto  
    moreover have "equivalent D D'" "equivalent H H'" unfolding D'_def H'_def
      unfolding equivalent_def plus_Mp(2)[of _ "smult q _", symmetric] by auto
    ultimately have "equivalent D D''" "equivalent H H''" unfolding equivalent_def by auto
    moreover from IH have "poly_mod.equivalent (q ^ 2 ^ Suc j) C (D'' * H'')" "monic D''" 
      "poly_mod.Mp (q ^ 2 ^ Suc j) D'' = D''" "poly_mod.Mp (q ^ 2 ^ Suc j) H'' = H''" by (auto simp: qq22)
    ultimately show ?thesis by simp
  qed
qed

end

context
  fixes p pn :: int
  and lg_n :: nat
  and two_lg_n_is_n :: bool
begin
definition quadratic_hensel_binary :: "int poly \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> int poly \<times> int poly" where
  "quadratic_hensel_binary C D H = (let
     (S,T) = euclid_ext_poly_mod p D H;
     (D',H') = quadratic_hensel_main C lg_n p S T D H
     in if two_lg_n_is_n then (D',H') else let Mo = poly_mod.Mp pn in (Mo D', Mo H'))" 

fun hensel_lifting_main :: "int poly \<Rightarrow> int poly list \<Rightarrow> int poly list" where
  "hensel_lifting_main u vs' = (let n = length vs' in if n \<le> 1 then if n = 1 then [u] else []
    else let 
      i = n div 2;
      vs_1 = take i vs';
      vs_2 = drop i vs';
      Mp = poly_mod.Mp p;
      v = Mp (prod_list vs_1); 
      w = Mp (prod_list vs_2); 
      (V,W) = quadratic_hensel_binary u v w
      in hensel_lifting_main V vs_1 @ hensel_lifting_main W vs_2)"
end

definition hensel_lifting_monic :: "int \<Rightarrow> nat \<Rightarrow> int poly \<Rightarrow> int poly list \<Rightarrow> int poly list" where
  "hensel_lifting_monic p n u vs = (let 
     pn = p^n; 
     lg_n = log_ceil 2 n;
     two_lg_n_is_n = (2^lg_n = n);
     C = poly_mod.Mp pn u     
     in hensel_lifting_main p pn lg_n two_lg_n_is_n C vs)" 

locale poly_mod_prime_hensel = poly_mod p for p :: int +
  fixes pn n lg_n two_lg_n_is_n
  assumes prime: "prime p"
  and pn: "pn = p^n" 
  and lg_n: "lg_n = log_ceil 2 n" 
  and lg_n_test: "two_lg_n_is_n = (2^lg_n = n)"
  and n: "n \<noteq> 0" 
begin 
sublocale poly_mod_2 p unfolding poly_mod_2_def using prime_gt_1_int[OF prime] by auto

abbreviation "hensel_binary \<equiv> quadratic_hensel_binary p pn lg_n two_lg_n_is_n" 

abbreviation "hensel_main \<equiv> hensel_lifting_main p pn lg_n two_lg_n_is_n" 

lemma hensel_binary: 
  assumes cop: "coprime_m D H" and eq: "equivalent C (D * H)"
  and normalized_input: "Mp D = D" "Mp H = H"
  and monic_input: "monic D" 
  and hensel_result: "hensel_binary C D H = (D',H')" 
  shows "poly_mod.equivalent (p^n) C (D' * H') (* the main result: equivalence mod p^n *)
    \<and> monic D' (* monic output *)
    \<and> equivalent D D' \<and> equivalent H H' (* apply `mod p` on D' and H' yields D and H again *)
    \<and> poly_mod.Mp (p^n) D' = D' \<and> poly_mod.Mp (p^n) H' = H'" (* output is normalized *)
proof -
  from m1 have p: "p > 1" .
  obtain S T where ext: "euclid_ext_poly_mod p D H = (S,T)" by force
  obtain D1 H1 where main: "quadratic_hensel_main C lg_n p S T D H = (D1,H1)" by force
  note hen = hensel_result[unfolded quadratic_hensel_binary_def ext split Let_def main]
  have main: "poly_mod.equivalent (p^(2^lg_n)) C (D1 * H1) \<and> monic D1
    \<and> equivalent D D1 \<and> equivalent H H1 \<and> poly_mod.Mp (p^(2^lg_n)) D1 = D1 \<and> poly_mod.Mp (p^(2^lg_n)) H1 = H1"  
    by (rule quadratic_hensel_main[OF euclid_ext_poly_mod[OF cop normalized_input prime ext] eq
        monic_input main p normalized_input])
  show ?thesis
  proof (cases two_lg_n_is_n)
    case True
    with main hen lg_n_test lg_n show ?thesis by auto
  next
    case False
    with hen lg_n_test lg_n pn have D': "D' = poly_mod.Mp (p ^ n) D1" and H': "H' = poly_mod.Mp (p ^ n) H1" by auto
    note * = log_ceil[of 2 n, folded lg_n]
    from * n have "lg_n = nat \<lceil>log 2 (real n)\<rceil>" by auto
    hence "(2 :: real) ^lg_n = 2^(nat \<lceil>log 2 (real n)\<rceil>)" by simp
    also have "\<dots> = 2 powr \<lceil>log 2 (real n)\<rceil>" 
      using * int_eq_iff n powr_int by auto
    also have "\<dots> \<ge> 2 powr (log 2 (real n))" 
      by (rule powr_mono, auto)
    also have "2 powr (log 2 (real n)) = real n" using n by auto
    finally have "real n \<le> (real 2)^lg_n" by simp
    hence j: "n \<le> 2^lg_n" by simp
    with False lg_n_test lg_n have "\<exists> k \<ge> 1. 2^lg_n = n + k " by simp presburger
    then obtain k where j: "2^lg_n = n + k" and k: "k \<ge> 1" by auto
    from main[unfolded j] have eq: "poly_mod.equivalent (p ^ n * p^k) C (D1 * H1)" unfolding power_add ..
    interpret pn: poly_mod_2 "p^n" using p n unfolding poly_mod_2_def by auto
    from poly_mod.Mp_shrink_modulus[OF eq] p have "pn.equivalent C (D1 * H1)" 
      by auto
    moreover have "pn.Mp (D1 * H1) = pn.Mp (pn.Mp D1 * pn.Mp H1)" by simp
    ultimately have CDH: "pn.equivalent C (D' * H')" unfolding D' H' pn.equivalent_def by metis
    from n p have "p ^ n = p * p ^ (n - 1)" "p ^ (n - 1) > 0" by (cases n, auto)
    note prod_mod = Mp_product_modulus[OF this]
    from main have "monic D1" by simp
    hence mon: "monic D'" unfolding D' by (rule pn.monic_Mp)
    have MpD: "pn.Mp D' = D'" unfolding D' by simp
    have MpH: "pn.Mp H' = H'" unfolding H' by simp
    from main have "equivalent D D1" "equivalent H H1" by auto
    hence "equivalent D D'" "equivalent H H'" unfolding D' H' 
      unfolding poly_mod.equivalent_def by (auto simp: prod_mod)
    with mon CDH MpD MpH show ?thesis by auto
  qed
qed

lemma hensel_main: 
  assumes eq: "equivalent C (prod_list Fs)"
  and "\<And> F. F \<in> set Fs \<Longrightarrow> Mp F = F \<and> monic F"  
  and hensel_result: "hensel_main C Fs = Gs" 
  and C: "monic C" "poly_mod.Mp (p^n) C = C" 
  and sf: "square_free_m C" 
  shows "poly_mod.equivalent (p^n) C (prod_list Gs) (* the main result: equivalence mod p^n *)
    \<and> length Fs = length Gs
    \<and> (\<forall> G. G \<in> set Gs \<longrightarrow> monic G \<and> poly_mod.Mp (p^n) G = G)
    \<and> (\<forall> F G. (F,G) \<in> set (zip Fs Gs) \<longrightarrow> equivalent F G)"
  using assms
proof (induct Fs arbitrary: C Gs rule: wf_induct[OF wf_measure[of length]])
  case (1 Fs C Gs)
  note simps = hensel_lifting_main.simps[of p pn lg_n two_lg_n_is_n C Fs]
  note IH = 1(1)[rule_format]
  note res = 1(4)[unfolded simps Let_def]
  note eq = 1(2)
  note Fs = 1(3)
  note C = 1(5,6)
  note sf = 1(7)
  let ?n = "length Fs" 
  show ?case
  proof (cases "?n \<le> 1")
    case True
    show ?thesis
    proof (cases "?n = 1")
      case True
      with res have Gs: "Gs = [C]" by auto
      from True obtain F where F: "Fs = [F]" by (cases Fs, auto)
      with eq Fs[of F] Gs C show ?thesis by (auto simp: poly_mod.equivalent_def)
    next
      case False
      with True have Fs: "Fs = []" by (cases Fs, auto)
      from False True res have Gs: "Gs = []" by auto
      from eq C have "Mp C = 1" unfolding Fs by (simp add: poly_mod.equivalent_def)
      hence "degree (Mp C) = 0" by simp
      with degree_m_eq_monic[OF C(1) m1] have "degree C = 0" unfolding degree_m_def by simp
      with C(1) have "C = 1" using monic_degree_0 by blast
      thus ?thesis using C eq unfolding Fs Gs by (simp add: poly_mod.equivalent_def)
    qed
  next
    case False
    let ?Mp = "poly_mod.Mp (p^n)" 
    define D where "D \<equiv> take (?n div 2) Fs" 
    define H where "H \<equiv> drop (?n div 2) Fs" 
    have FDH: "Fs = D @ H" unfolding D_def H_def by simp
    let ?D = "Mp (prod_list D)" 
    let ?H = "Mp (prod_list H)"
    obtain A B where hen: "hensel_binary C ?D ?H = (A,B)" by force
    obtain AD where AD': "AD = hensel_main A D" by auto
    obtain BH where BH': "BH = hensel_main B H" by auto
    from square_free_m_cong[OF sf, of "prod_list D * prod_list H"] eq[unfolded FDH]
    have sf': "square_free_m (prod_list D * prod_list H)" by (auto simp: equivalent_def)
    from poly_mod_prime.square_free_m_prod_imp_coprime_m[OF _ this]
    have "coprime_m (prod_list D) (prod_list H)" unfolding poly_mod_prime_def using prime .
    hence cop': "coprime_m ?D ?H" unfolding coprime_m_def dvdm_def equivalent_def Mp_Mp .
    from eq have eq': "equivalent C (?D * ?H)" unfolding FDH by (simp add: equivalent_def)
    have step: "poly_mod.equivalent (p ^ n) C (A * B) \<and> monic A \<and> equivalent ?D A \<and>
       equivalent ?H B \<and> ?Mp A = A \<and> ?Mp B = B" 
      by (rule hensel_binary[OF cop' eq' Mp_Mp Mp_Mp monic_Mp[OF monic_prod_list] hen],
        insert Fs, auto simp: FDH)
    from res[folded D_def H_def, unfolded hen split] False 
    have Gs: "Gs = AD @ BH" by (simp add: AD' BH')
    have AD: "equivalent A (prod_list D)" "?Mp A = A"  and monA: "monic A"
      using step by (auto simp: equivalent_def)
    from False have lenD: "(D,Fs) \<in> measure length" unfolding D_def by auto
    note sf_fact = square_free_m_factor[OF sf']
    from square_free_m_cong[OF sf_fact(1)] AD have sfA: "square_free_m A" unfolding equivalent_def by auto 
    have IH1: "poly_mod.equivalent (p ^ n) A (prod_list AD) \<and>
      length D = length AD \<and>
      (\<forall>G. G \<in> set AD \<longrightarrow> monic G \<and> ?Mp G = G) \<and>
      (\<forall>F G. (F, G) \<in> set (zip D AD) \<longrightarrow> equivalent F G)" 
      by (rule IH[OF lenD AD(1) _ AD'[symmetric] monA AD(2) sfA],
        insert Fs, auto simp: FDH)
    from False have lenH: "(H,Fs) \<in> measure length" unfolding H_def by auto
    have BH: "equivalent B (prod_list H)" "poly_mod.Mp (p ^ n) B = B"
      using step by (auto simp: equivalent_def)
    from step have "poly_mod.equivalent (p ^ n) C (A * B)" by simp
    hence "?Mp C = ?Mp (A * B)" by (simp add: poly_mod.equivalent_def)
    with C monA AD(2) BH(2) have monB: "monic B"
      by (metis (no_types, lifting) coeff_degree_mult degree_map_poly leading_coeff_neq_0  
       mult.commute mult.right_neutral poly_mod.M_0 poly_mod.Mp_coeff poly_mod.Mp_def)
    from square_free_m_cong[OF sf_fact(2)] BH have sfB: "square_free_m B" unfolding equivalent_def by auto 
    have IH2: "poly_mod.equivalent (p ^ n) B (prod_list BH) \<and>
      length H = length BH \<and>
      (\<forall>G. G \<in> set BH \<longrightarrow> monic G \<and> ?Mp G = G) \<and>
      (\<forall>F G. (F, G) \<in> set (zip H BH) \<longrightarrow> equivalent F G)" 
      by (rule IH[OF lenH BH(1) _ BH'[symmetric] monB BH(2) sfB],
        insert Fs, auto simp: FDH)
    from step have "?Mp C = ?Mp (?Mp A * ?Mp B)" by (auto simp: poly_mod.equivalent_def) 
    also have "?Mp A = ?Mp (prod_list AD)" using IH1 by (auto simp: poly_mod.equivalent_def)
    also have "?Mp B = ?Mp (prod_list BH)" using IH2 by (auto simp: poly_mod.equivalent_def)
    finally have "poly_mod.equivalent (p ^ n) C (prod_list AD * prod_list BH)" 
      by (auto simp: poly_mod.equivalent_def poly_mod.mult_Mp)
    thus ?thesis unfolding Gs FDH using IH1 IH2 by (auto simp: poly_mod.equivalent_def)
  qed
qed
end

lemma hensel_lifting_monic: 
  assumes eq: "poly_mod.equivalent p C (prod_list Fs)"
  and Fs: "\<And> F. F \<in> set Fs \<Longrightarrow> poly_mod.Mp p F = F \<and> monic F"  
  and hensel_result: "hensel_lifting_monic p n C Fs = Gs" 
  and mon: "monic (poly_mod.Mp (p^n) C)" 
  and prime: "prime p" 
  and sf: "poly_mod.square_free_m p C"
  and n: "n \<noteq> 0" 
  shows "poly_mod.equivalent (p^n) C (prod_list Gs)"
    "length Fs = length Gs"
    "\<And> G. G \<in> set Gs \<Longrightarrow> monic G \<and> poly_mod.Mp (p^n) G = G"
    "\<And> F G. (F,G) \<in> set (zip Fs Gs) \<Longrightarrow> poly_mod.equivalent p F G"
proof -
  let ?Mp = "poly_mod.Mp (p ^ n)" 
  interpret poly_mod_prime_hensel p "p^n" n "log_ceil 2 n" "2^(log_ceil 2 n) = n"
    by (unfold_locales, insert n prime, auto)
  from hensel_result[unfolded hensel_lifting_monic_def Let_def]
  have hen: "hensel_main (?Mp C) Fs = Gs" by simp
  from eq n have eq: "equivalent (?Mp C) (prod_list Fs)"
      using Mp_Mp_pow_is_Mp eq m1 n poly_mod.equivalent_def by force
  have "Mp C = Mp (?Mp C)" using n by (simp add: Mp_Mp_pow_is_Mp m1)
  from hensel_main[OF eq Fs hen mon poly_mod.Mp_Mp square_free_m_cong[OF sf this]]
  show "poly_mod.equivalent (p^n) C (prod_list Gs)"
    "length Fs = length Gs"
    "\<And> G. G \<in> set Gs \<Longrightarrow> monic G \<and> poly_mod.Mp (p^n) G = G"
    "\<And> F G. (F,G) \<in> set (zip Fs Gs) \<Longrightarrow> poly_mod.equivalent p F G" 
    by (auto simp: poly_mod.equivalent_def poly_mod.Mp_Mp)
qed

definition hensel_lifting :: "int \<Rightarrow> nat \<Rightarrow> int poly \<Rightarrow> int poly list \<Rightarrow> int poly list" where 
  "hensel_lifting p n f gs = (let lc = lead_coeff f; 
     pn = p^n;
     ilc = inverse_mod lc pn;
     g = smult ilc f
     in hensel_lifting_monic p n g gs)"     
  
lemma hensel_lifting: assumes 
  prime: "prime p" 
  and n: "n \<noteq> 0" 
  and res: "hensel_lifting p n f fs = gs"                        (* result of hensel is fact. gs *)
  and cop: "coprime (lead_coeff f) p" 
  and sf: "poly_mod.square_free_m p f" 
  and fact: "poly_mod.factorization_m p f (c, mset fs)"          (* input is fact. fs mod p *)
  and c: "c \<in> {0..<p}" 
  and norm: "(\<forall>fi\<in>set fs. set (coeffs fi) \<subseteq> {0..<p})" 
shows "poly_mod.factorization_m (p^n) f (lead_coeff f, mset gs)" (* factorization mod p^n *)
    "map degree fs = map degree gs"                              (* degrees stay the same *)
    "\<And> g. g \<in> set gs \<Longrightarrow> monic g \<and> poly_mod.Mp (p^n) g = g \<and>    (* monic and normalized *)
      poly_mod.irreducible_m p g \<and>                               (* irreducibility even mod p *)
      poly_mod.degree_m p g = degree g"   (* mod p does not change degree of g *)     
proof -
  interpret poly_mod_2 p using prime unfolding poly_mod_2_def using prime_gt_1_int by fastforce
  interpret q: poly_mod_2 "p^n" using m1 n unfolding poly_mod_2_def by auto
  from fact have eq: "equivalent f (smult c (prod_list fs))"  
    and mon_fs: "(\<forall>fi\<in>set fs. monic (Mp fi) \<and> irreducible_m fi)" 
    unfolding factorization_m_def by auto
  {
    fix f
    assume "f \<in> set fs" 
    with mon_fs norm have "set (coeffs f) \<subseteq> {0..<p}" and "monic (Mp f)" by auto
    hence "monic f" using Mp_ident_iff' by force
  } note mon_fs' = this
  have Mp_id: "\<And> f. Mp (q.Mp f) = Mp f" by (simp add: Mp_Mp_pow_is_Mp m1 n)
  let ?lc = "lead_coeff f" 
  let ?q = "p ^ n" 
  define ilc where "ilc \<equiv> inverse_mod ?lc ?q" 
  define F where "F \<equiv> smult ilc f" 
  from res[unfolded hensel_lifting_def Let_def] 
  have hen: "hensel_lifting_monic p n F fs = gs" 
    unfolding ilc_def F_def .
  from inverse_mod_pow[OF cop m1 n, folded ilc_def]
  have inv: "q.M (ilc * ?lc) = 1" unfolding q.M_def .
  hence ilc0: "ilc \<noteq> 0" by (cases "ilc = 0", auto)
  {
    fix q
    assume "ilc * ?lc = ?q * q" 
    from arg_cong[OF this, of q.M] have "q.M (ilc * ?lc) = 0" 
      unfolding q.M_def by auto
    with inv have False by auto
  } note not_dvd = this
  have mon: "monic (q.Mp F)" unfolding F_def q.Mp_coeff coeff_smult q.degree_m_def[symmetric]
    by (subst q.degree_m_eq[OF _ q.m1], insert not_dvd, auto simp: inv ilc0 lead_coeff_def[symmetric])
  have "q.Mp f = q.Mp (smult (q.M (?lc * ilc)) f)" using inv by (simp add: ac_simps)
  also have "\<dots> = q.Mp (smult ?lc F)" by (simp add: F_def)
  finally have f: "q.Mp f = q.Mp (smult ?lc F)" .
  from arg_cong[OF f, of Mp]
  have f_p: "Mp f = Mp (smult ?lc F)" 
    by (simp add: Mp_Mp_pow_is_Mp n m1)
  from arg_cong[OF this, of square_free_m, unfolded Mp_square_free_m] sf
  have "square_free_m (smult ?lc F)" by simp
  from square_free_m_smultD[OF this] have sf: "square_free_m F" .
  
  define c' where "c' \<equiv> M (c * ilc)"
  from factorization_m_smult[OF fact, of ilc, folded F_def] 
  have fact: "factorization_m F (c', mset fs)" unfolding c'_def factorization_m_def equivalent_def by auto
  hence eq: "equivalent F (smult c' (prod_list fs))" unfolding factorization_m_def by auto
  from factorization_m_lead_coeff[OF fact] monic_Mp[OF mon, unfolded Mp_id] have "M c' = 1" 
    unfolding lead_coeff_def by auto
  hence c': "c' = 1" unfolding c'_def by auto
  with eq have eq: "equivalent F (prod_list fs)" by auto 
  {
    fix f
    assume "f \<in> set fs" 
    with mon_fs' norm have "Mp f = f \<and> monic f" unfolding Mp_ident_iff'
      by auto
  } note fs = this
  note hen = hensel_lifting_monic[OF eq fs hen mon prime sf n]
  from hen(2) have len: "length fs = length gs" by auto
  have eq: "q.equivalent f (smult ?lc (prod_list gs))" 
    unfolding q.equivalent_def f using arg_cong[OF hen(1)[unfolded q.equivalent_def], 
    of "\<lambda> f. q.Mp (smult ?lc f)"] by simp
  {
    fix g 
    assume g: "g \<in> set gs"
    from hen(3)[OF _ g] have mon_g: "monic g" and Mp_g: "q.Mp g = g" by auto
    from g obtain f where fg: "(f,g) \<in> set (zip fs gs)" and f: "f \<in> set fs" unfolding set_zip 
      unfolding set_conv_nth len by auto
    from hen(4)[OF _ fg] have fg: "equivalent f g" by auto
    from mon_fs f fs have irr_f: "irreducible_m f" and mon_f: "monic f" and Mp_f: "Mp f = f" by auto
    have deg: "degree_m g = degree g" 
      by (rule degree_m_eq_monic[OF mon_g m1])
    from irr_f fg have irr_g: "irreducible_m g" 
      unfolding irreducible_m_def degree_m_def equivalent_def dvdm_def by simp
    have "q.irreducible_m g"
      by (rule irreducible_lifting[OF m1 n _ irr_g], unfold deg, rule q.degree_m_eq_monic[OF mon_g q.m1])
    note mon_g Mp_g deg irr_g this
  } note g = this
  {
    fix g
    assume "g \<in> set gs" 
    from g[OF this]
    show "monic g \<and> q.Mp g = g \<and> irreducible_m g \<and> degree_m g = degree g" by auto
  }
  show "map degree fs = map degree gs"
  proof (intro nth_equalityI allI impI; unfold length_map)
    show "length fs = length gs" using len by simp
    fix i
    assume i: "i < length fs" 
    with len have zip: "(fs ! i, gs ! i) \<in> set (zip fs gs)" and i': "i < length gs" 
      and mem: "fs ! i \<in> set fs" "gs ! i \<in> set gs" 
      using in_set_conv_nth by fastforce+
    from g[OF mem(2)]
    have mon: "monic (gs ! i)" by auto
    from hen(4)[OF _ zip] have eq: "equivalent (fs ! i) (gs ! i)" by auto
    have "map degree fs ! i = map degree gs ! i \<longleftrightarrow> degree (fs ! i) = degree (gs ! i)" 
      using i i' by auto
    also have "degree (fs ! i) = degree (Mp (fs ! i))" using fs[OF mem(1)] by simp
    also have "\<dots> = degree (Mp (gs ! i))" using eq unfolding equivalent_def by auto
    also have "\<dots> = degree (gs ! i)" using mon by (rule monic_degree_Mp)
    finally show "map degree fs ! i = map degree gs ! i" by simp
  qed
  show "q.factorization_m f (lead_coeff f, mset gs)" 
    using eq g unfolding q.factorization_m_def by auto
qed

end
