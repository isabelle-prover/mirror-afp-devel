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

context prime_field
begin

abbreviation "ff_ops \<equiv> finite_field_ops p" 
sublocale ff: field_ops ff_ops mod_ring_rel by (rule finite_field_ops)

sublocale poly_mod_type p "TYPE('a)"
  by (unfold_locales, rule p)

notation equivalent (infixl "=m" 50)

lemma coeffs_to_int_poly: "coeffs (to_int_poly (x :: 'a mod_ring poly)) = map to_int_mod_ring (coeffs x)" 
  by (rule coeffs_map_poly, auto)

lemma coeffs_of_int_poly: "coeffs (of_int_poly (Mp x) :: 'a mod_ring poly) = map of_int (coeffs (Mp x))" 
proof (rule coeffs_map_poly)
  fix y
  assume "y \<in> range (coeff (Mp x))" 
  then obtain i where y: "y = coeff (Mp x) i" by auto
  from this[unfolded Mp_coeff]
  show "(of_int y = (0 :: 'a mod_ring)) = (y = 0)"
    using M_0 M_def mod_mod_trivial of_int_mod_ring.rep_eq of_int_mod_ring_0 p by (metis of_int_of_int_mod_ring)
qed

lemma poly_of_list_to_int_poly: assumes "ff.poly_rel f g" shows "poly_of_list f = to_int_poly g"
proof -
  from assms have "f = coeffs (to_int_poly g)"
    by (simp add: coeffs_to_int_poly ff.poly_rel_def list_all2_conv_all_nth mod_ring_rel_def nth_equalityI)
  then show ?thesis by auto
qed

lemma poly_rel_coeffs_Mp_of_int_poly: assumes id: "f' = coeffs (Mp f)" "f'' = of_int_poly (Mp f)" 
  shows "ff.poly_rel f' f''" unfolding id ff.poly_rel_def
  unfolding list_all2_conv_all_nth coeffs_of_int_poly
  by (metis Mp_Mp length_map nth_map poly_mod.Mp_coeff mod_ring_rel_def nth_coeffs_coeff to_int_mod_ring_of_int_M)

end
end
