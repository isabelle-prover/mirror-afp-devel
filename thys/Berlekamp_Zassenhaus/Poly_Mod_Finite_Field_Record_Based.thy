(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsubsection \<open>Over a Finite Field\<close>
theory Poly_Mod_Finite_Field_Record_Based
imports
  Poly_Mod_Finite_Field
  Finite_Field_Record_Based
  Polynomial_Record_Based
begin

lemma prime_type_prime_card: assumes p: "prime p" 
  and "\<exists>(Rep :: 'a \<Rightarrow> int) Abs. type_definition Rep Abs {0 ..< p :: int}"
  shows "class.prime_card (TYPE('a)) \<and> int CARD('a) = p"
proof -
  from p have p2: "p \<ge> 2" by (rule prime_ge_2_int)
  from assms obtain rep :: "'a \<Rightarrow> int" and abs :: "int \<Rightarrow> 'a" where t: "type_definition rep abs {0 ..< p}" by auto
  have "card (UNIV :: 'a set) = card {0 ..< p}" using t by (rule type_definition.card)
  also have "\<dots> = p" using p2 by auto
  finally have bn: "int CARD ('a) = p" .
  hence "class.prime_card (TYPE('a))" unfolding class.prime_card_def
    using p p2 by auto
  with bn show ?thesis by blast
qed

definition of_int_poly_i :: "'i arith_ops_record \<Rightarrow> int poly \<Rightarrow> 'i list" where
  "of_int_poly_i ops f = map (arith_ops_record.of_int ops) (coeffs f)" 

definition to_int_poly_i :: "'i arith_ops_record \<Rightarrow> 'i list \<Rightarrow> int poly" where
  "to_int_poly_i ops f = poly_of_list (map (arith_ops_record.to_int ops) f)" 

locale prime_field_gen = field_ops ff_ops R for ff_ops :: "'i arith_ops_record" and
  R :: "'i \<Rightarrow> 'a :: prime_card mod_ring \<Rightarrow> bool" +
  fixes p :: int 
  assumes p: "p = int CARD('a)"
  and of_int: "0 \<le> x \<Longrightarrow> x < p \<Longrightarrow> R (arith_ops_record.of_int ff_ops x) (of_int x)" 
  and to_int: "R y z \<Longrightarrow> arith_ops_record.to_int ff_ops y = to_int_mod_ring z" 
begin

lemma nat_p: "nat p = CARD('a)" unfolding p by simp

sublocale poly_mod_type p "TYPE('a)"
  by (unfold_locales, rule p)

notation equivalent (infixl "=m" 50)

lemma coeffs_to_int_poly: "coeffs (to_int_poly (x :: 'a mod_ring poly)) = map to_int_mod_ring (coeffs x)" 
  by (rule coeffs_map_poly, auto)

lemma coeffs_of_int_poly: "coeffs (of_int_poly (Mp x) :: 'a mod_ring poly) = map of_int (coeffs (Mp x))"
  apply (rule coeffs_map_poly)
  by (metis M_0 M_M Mp_coeff leading_coeff_0_iff of_int_hom.hom_zero to_int_mod_ring_of_int_M)

lemma to_int_poly_i: assumes "poly_rel f g" shows "to_int_poly_i ff_ops f = to_int_poly g"
proof -
  have *: "map (arith_ops_record.to_int ff_ops) f = coeffs (to_int_poly g)"
    unfolding coeffs_to_int_poly 
    by (rule nth_equalityI, insert assms, auto simp: list_all2_conv_all_nth poly_rel_def to_int)
  show ?thesis unfolding coeffs_eq_iff to_int_poly_i_def poly_of_list_def coeffs_Poly *
    strip_while_coeffs..
qed

lemma poly_rel_coeffs_Mp_of_int_poly: assumes id: "f' = of_int_poly_i ff_ops (Mp f)" "f'' = of_int_poly (Mp f)" 
  shows "poly_rel f' f''" unfolding id poly_rel_def
  unfolding list_all2_conv_all_nth coeffs_of_int_poly of_int_poly_i_def length_map
  by (rule conjI[OF refl], intro allI impI, simp add: nth_coeffs_coeff Mp_coeff M_def, rule of_int,
    insert p, auto)

end

context prime_field
begin
lemma prime_field_finite_field_ops: "prime_field_gen (finite_field_ops p) mod_ring_rel p" 
proof -
  interpret field_ops "finite_field_ops p" mod_ring_rel by (rule finite_field_ops)
  show ?thesis
    by (unfold_locales, rule p, 
      auto simp: finite_field_ops_def p mod_ring_rel_def of_int_of_int_mod_ring)
qed

lemma prime_field_finite_field_ops32: assumes small: "p \<le> 65535" 
  shows "prime_field_gen (finite_field_ops32 (uint32_of_int p)) mod_ring_rel32 p" 
proof -
  let ?pp = "uint32_of_int p" 
  have ppp: "p = int_of_uint32 ?pp"
    by (subst int_of_uint32_inv, insert small p2, auto)
  note * = ppp small 
  interpret field_ops "finite_field_ops32 ?pp" mod_ring_rel32 
    by (rule finite_field_ops32, insert *)
  interpret int: prime_field_gen "finite_field_ops p" mod_ring_rel
    by (rule prime_field_finite_field_ops)
  show ?thesis
  proof (unfold_locales, rule p, auto simp: finite_field_ops32_def)
    fix x
    assume x: "0 \<le> x" "x < p" 
    from int.of_int[OF this] have "mod_ring_rel x (of_int x)" by (simp add: finite_field_ops_def)
    thus "mod_ring_rel32 (uint32_of_int x) (of_int x)" unfolding mod_ring_rel32_def[OF *]
      by (intro exI[of _ x], auto simp: urel32_def[OF *], subst int_of_uint32_inv, insert * x, auto)
  next
    fix y z
    assume "mod_ring_rel32 y z" 
    from this[unfolded mod_ring_rel32_def[OF *]] obtain x where yx: "urel32 y x" and xz: "mod_ring_rel x z" by auto
    from int.to_int[OF xz] have zx: "to_int_mod_ring z = x" by (simp add: finite_field_ops_def)
    show "int_of_uint32 y = to_int_mod_ring z" unfolding zx using yx unfolding urel32_def[OF *] by simp
  qed
qed

lemma prime_field_finite_field_ops64: assumes small: "p \<le> 4294967295" 
  shows "prime_field_gen (finite_field_ops64 (uint64_of_int p)) mod_ring_rel64 p" 
proof -
  let ?pp = "uint64_of_int p" 
  have ppp: "p = int_of_uint64 ?pp"
    by (subst int_of_uint64_inv, insert small p2, auto)
  note * = ppp small 
  interpret field_ops "finite_field_ops64 ?pp" mod_ring_rel64
    by (rule finite_field_ops64, insert *)
  interpret int: prime_field_gen "finite_field_ops p" mod_ring_rel
    by (rule prime_field_finite_field_ops)
  show ?thesis
  proof (unfold_locales, rule p, auto simp: finite_field_ops64_def)
    fix x
    assume x: "0 \<le> x" "x < p" 
    from int.of_int[OF this] have "mod_ring_rel x (of_int x)" by (simp add: finite_field_ops_def)
    thus "mod_ring_rel64 (uint64_of_int x) (of_int x)" unfolding mod_ring_rel64_def[OF *]
      by (intro exI[of _ x], auto simp: urel64_def[OF *], subst int_of_uint64_inv, insert * x, auto)
  next
    fix y z
    assume "mod_ring_rel64 y z" 
    from this[unfolded mod_ring_rel64_def[OF *]] obtain x where yx: "urel64 y x" and xz: "mod_ring_rel x z" by auto
    from int.to_int[OF xz] have zx: "to_int_mod_ring z = x" by (simp add: finite_field_ops_def)
    show "int_of_uint64 y = to_int_mod_ring z" unfolding zx using yx unfolding urel64_def[OF *] by simp
  qed
qed
end

end
