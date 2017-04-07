section \<open>More on Polynomials\<close>
  
text \<open>This theory contains several results on content, gcd, primitive part, etc..
  Moreover, there is a slightly improved code-equation for computing the gcd.\<close>
  
theory Missing_Polynomial_Factorial
  imports "~~/src/HOL/Library/Polynomial_Factorial" 
begin

text \<open>Improved code equation for @{const gcd_poly_code}
  which avoids computing the content twice.\<close>
lemma gcd_poly_code_code[code]: "gcd_poly_code p q = 
           (if p = 0 then normalize q else if q = 0 then normalize p else let
              c1 = content p; 
              c2 = content q;
              p' = map_poly (\<lambda> x. x div c1) p;  
              q' = map_poly (\<lambda> x. x div c2) q
              in smult (gcd c1 c2) (gcd_poly_code_aux p' q'))" 
  unfolding gcd_poly_code_def Let_def primitive_part_def by simp
  
lemma gcd_smult: fixes f g :: "'a :: factorial_ring_gcd poly" 
  defines cf: "cf \<equiv> content f" 
  and cg: "cg \<equiv> content g" 
shows "gcd (smult a f) g = (if a = 0 \<or> f = 0 then normalize g else 
  smult (gcd a (cg div (gcd cf cg))) (gcd f g))" 
proof (cases "a = 0 \<or> f = 0")
  case False
  let ?c = "content" 
  let ?pp = primitive_part
  let ?ua = "unit_factor a" 
  let ?na = "normalize a" 
  define H where "H = gcd (?c f) (?c g)" 
  have "H dvd ?c f" unfolding H_def by auto
  then obtain F where fh: "?c f = H * F" unfolding dvd_def by blast
  from False have cf0: "?c f \<noteq> 0" by auto
  hence H: "H \<noteq> 0" unfolding H_def by auto
  from arg_cong[OF fh, of "\<lambda> f. f div H"] H have F: "F = ?c f div H" by auto
  have "H dvd ?c g" unfolding H_def by auto
  then obtain G where gh: "?c g = H * G" unfolding dvd_def by blast
  from arg_cong[OF gh, of "\<lambda> f. f div H"] H have G: "G = ?c g div H" by auto
  have "is_unit ?ua" using False by simp
  hence ua: "is_unit [: ?ua :]" by (simp add: one_poly_def)
  have "gcd (smult a f) g = smult (gcd (?na * ?c f) (?c g))
     (gcd (smult ?ua (?pp f)) (?pp g))"   
    unfolding gcd_poly_decompose[of "smult a f"]
    content_smult primitive_part_smult by simp
  also have "smult ?ua (?pp f) = ?pp f * [: ?ua :]" by simp
  also have "gcd \<dots> (?pp g) = gcd (?pp f) (?pp g)" 
    unfolding gcd_mult_unit1[OF ua] ..
  also have "gcd (?na * ?c f) (?c g) = gcd ((?na * F) * H) (G * H)" 
    unfolding fh gh by (simp add: ac_simps)
  also have "\<dots> = gcd (?na * F) G * normalize H" unfolding gcd_mult_right gcd.commute[of G] by simp
  also have "normalize H = H" by (metis H_def normalize_gcd)      
  finally 
  have "gcd (smult a f) g = smult (gcd (?na * F) G) (smult  H (gcd (?pp f) (?pp g)))" by simp
  also have "smult H (gcd (?pp f) (?pp g)) = gcd f g" unfolding H_def
    by (rule gcd_poly_decompose[symmetric])
  also have "gcd (?na * F) G = gcd (F * ?na) G" by (simp add: ac_simps)
  also have "\<dots> = gcd ?na G" 
  proof (rule gcd_mult_cancel)
    show "coprime F G" using H unfolding F G H_def
      using cf0 div_gcd_coprime by blast
  qed
  finally show ?thesis unfolding G H_def cg cf using False by simp
next
  case True
  hence "gcd (smult a f) g = normalize g" by (cases "a = 0", auto)
  thus ?thesis using True by simp
qed
  
lemma gcd_smult_ex: assumes "a \<noteq> 0" 
  shows "\<exists> b. gcd (smult a f) g = smult b (gcd f g) \<and> b \<noteq> 0" 
proof (cases "f = 0")
  case True
  thus ?thesis by (intro exI[of _ 1], auto)
next
  case False
  hence id: "(a = 0 \<or> f = 0) = False" using assms by auto
  show ?thesis unfolding gcd_smult id if_False
    by (intro exI conjI, rule refl, insert assms, auto)
qed

lemma primitive_part_idemp[simp]: "primitive_part (primitive_part f) = primitive_part f" 
  by (metis content_primitive_part primitive_part_def primitive_part_prim)
  
lemma content_gcd_primitive: 
   "f \<noteq> 0 \<Longrightarrow> content (gcd (primitive_part f) g) = 1"
   "f \<noteq> 0 \<Longrightarrow> content (gcd (primitive_part f) (primitive_part g)) = 1"
  by (metis (no_types, lifting) content_dvd_contentI content_primitive_part gcd_dvd1 is_unit_content_iff)+
    
lemma content_gcd_content: "content (gcd f g) = gcd (content f) (content g)" 
  (is "?l = ?r")
proof -
  let ?c = "content" 
  have "?l = normalize (gcd (?c f) (?c g)) *
    ?c (gcd (primitive_part f) (primitive_part g))" 
    unfolding gcd_poly_decompose[of f g] content_smult ..
  also have "\<dots> = gcd (?c f) (?c g) *
    ?c (gcd (primitive_part f) (primitive_part g))" by simp
  also have "\<dots> = ?r" using content_gcd_primitive[of f g]
    by (metis (no_types, lifting) content_dvd_contentI content_eq_zero_iff 
    content_primitive_part gcd_dvd2 gcd_eq_0_iff is_unit_content_iff mult_cancel_left1)
  finally show ?thesis .
qed  

lemma gcd_primitive_part: 
  "gcd (primitive_part f) (primitive_part g) = normalize (primitive_part (gcd f g))" 
  proof(cases "f = 0")
    case True
    show ?thesis unfolding gcd_poly_decompose[of f g] gcd_0_left primitive_part_0 True
      by (simp add: associatedI primitive_part_dvd_primitive_partI)
  next
    case False
    have "normalize 1 = normalize (unit_factor (gcd (content f) (content g)))"
      by (simp add: False) 
    then show ?thesis unfolding gcd_poly_decompose[of f g]
      by (metis (no_types) normalize_smult content_gcd_primitive(1)[OF False] content_times_primitive_part normalize_gcd primitive_part_smult)
qed

lemma primitive_part_gcd: "primitive_part (gcd f g) 
  = unit_factor (gcd f g) * gcd (primitive_part f) (primitive_part g)" 
  unfolding gcd_primitive_part by (metis (no_types, lifting) 
  content_times_primitive_part gcd_0_right gcd_eq_0_iff mult_cancel_right 
  mult_smult_right primitive_part_def smult_content_normalize_primitive_part unit_factor_mult_normalize)

lemma primitive_part_normalize: "primitive_part (normalize f) = normalize (primitive_part f)" 
proof (cases "f = 0")
  case True
  thus ?thesis by simp
next
  case False
  have "normalize (content (normalize (primitive_part f))) = 1"
    using content_primitive_part[OF False] content_dvd content_const
          content_dvd_contentI dvd_normalize_iff is_unit_content_iff by (metis (no_types))
  then have "content (normalize (primitive_part f)) = 1" by fastforce
  then have "content (normalize f) = 1 * content f"
    by (metis (no_types) content_smult mult.commute normalize_content 
    smult_content_normalize_primitive_part)
  then have "content f = content (normalize f)"
    by simp
  then show ?thesis unfolding smult_content_normalize_primitive_part[of f,symmetric]
    by (metis (no_types) False content_times_primitive_part mult.commute mult_cancel_left
                                   mult_smult_right smult_content_normalize_primitive_part)
qed
  
lemma length_coeffs_primitive_part[simp]: "length (coeffs (primitive_part f)) = length (coeffs f)" 
proof (cases "f = 0")
  case False
  hence "length (coeffs f) \<noteq> 0" "length (coeffs (primitive_part f)) \<noteq> 0" by auto
  thus ?thesis using degree_primitive_part[of f, unfolded degree_eq_length_coeffs] by linarith
qed simp

lemma degree_unit_factor[simp]: "degree (unit_factor f) = 0"
  by (simp add: monom_0 unit_factor_poly_def)
  
lemma degree_normalize[simp]: "degree (normalize f) = degree f"
proof (cases "f = 0")
  case False
  have "degree f = degree (unit_factor f * normalize f)" by simp      
  also have "\<dots> = degree (unit_factor f) + degree (normalize f)" 
    by (rule degree_mult_eq, insert False, auto)
  finally show ?thesis by simp
qed simp
  
end