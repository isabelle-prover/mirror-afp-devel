theory Kyber_Values
  imports 
    Crypto_Scheme
    (* Check_Prime *)
    (* NTT_Scheme *)
begin

section \<open>Specification for Kyber\<close>

typedef fin7681 = "{0..<7681::int}"
  morphisms fin7681_rep fin7681_abs
  by (rule_tac x = 0 in exI, simp)

setup_lifting type_definition_fin7681


lemma CARD_fin7681 [simp]: "CARD (fin7681) = 7681" 
  unfolding type_definition.card [OF type_definition_fin7681]
  by simp

lemma fin7681_nontriv [simp]: "1 < CARD(fin7681)"
  unfolding CARD_fin7681 by auto

lemma prime_7681: "prime (7681::nat)" by eval

instantiation fin7681 :: comm_ring_1
begin

lift_definition zero_fin7681 :: "fin7681" is "0" by simp

lift_definition one_fin7681 :: "fin7681" is "1" by simp

lift_definition plus_fin7681 :: "fin7681 \<Rightarrow> fin7681 \<Rightarrow> fin7681"
  is "(\<lambda>x y. (x+y) mod 7681)"
  by auto

lift_definition uminus_fin7681 :: "fin7681 \<Rightarrow> fin7681"
  is "(\<lambda>x. (uminus x) mod 7681)"
  by auto

lift_definition minus_fin7681 :: "fin7681 \<Rightarrow> fin7681 \<Rightarrow> fin7681"
  is "(\<lambda>x y. (x-y) mod 7681)"
  by auto

lift_definition times_fin7681 :: "fin7681 \<Rightarrow> fin7681 \<Rightarrow> fin7681"
  is "(\<lambda>x y. (x*y) mod 7681)"
  by auto


instance 
proof 
  fix a b c ::fin7681
  show "a * b * c = a * (b * c)" 
    by (transfer, simp add: algebra_simps mod_mult_left_eq mod_mult_right_eq)
  show "a + b + c = a + (b + c)" 
    by (transfer, simp add: algebra_simps mod_add_left_eq mod_add_right_eq)
  show "(a + b) * c = a * c + b * c" 
    by (transfer, simp add: algebra_simps mod_add_right_eq  mod_mult_right_eq)
qed (transfer; simp add: algebra_simps mod_add_right_eq; fail)+

end


instantiation fin7681 :: finite
begin
instance 
proof
  show "finite (UNIV :: fin7681 set)" unfolding type_definition.univ [OF type_definition_fin7681]
    by auto
qed
end


instantiation fin7681 :: equal
begin
lift_definition equal_fin7681 :: "fin7681 \<Rightarrow> fin7681 \<Rightarrow> bool" is "(=)" .
instance by (intro_classes, transfer, auto)
end

instantiation fin7681 :: nontriv
begin
instance 
proof
  show "1 < CARD(fin7681)" unfolding CARD_fin7681 by auto
qed
end

instantiation fin7681 :: prime_card
begin
instance 
proof
  show "prime CARD(fin7681)" unfolding CARD_fin7681 using prime_7681
    by blast 
qed
end

instantiation fin7681 :: qr_spec
begin

definition qr_poly'_fin7681:: "fin7681 itself \<Rightarrow> int poly" where
  "qr_poly'_fin7681 \<equiv> (\<lambda>_. Polynomial.monom (1::int) 256 + 1)"

instance proof 
  have "lead_coeff (qr_poly' TYPE(fin7681)) = 1" unfolding qr_poly'_fin7681_def 
    by (simp add: degree_add_eq_left degree_monom_eq)
  then show "\<not> int CARD(fin7681) dvd
       lead_coeff (qr_poly' TYPE(fin7681))" 
    unfolding CARD_fin7681 by auto
next
  have "degree (qr_poly' TYPE(fin7681)) = 256" unfolding qr_poly'_fin7681_def
    by (simp add: degree_add_eq_left degree_monom_eq)
  then show "0 < degree (qr_poly' TYPE(fin7681))"  by auto
qed
end

lift_definition to_int_fin7681 :: "fin7681 \<Rightarrow> int" is "\<lambda>x. x" .

lift_definition of_int_fin7681 :: "int \<Rightarrow> fin7681" is "\<lambda>x. (x mod 7681)"
  by simp

interpretation to_int_fin7681_hom: inj_zero_hom to_int_fin7681
  by (unfold_locales; transfer, auto)

interpretation of_int_fin7681_hom: zero_hom of_int_fin7681
  by (unfold_locales, transfer, auto)

lemma to_int_fin7681_of_int_fin7681 [simp]:
  "to_int_fin7681 (of_int_fin7681 x) = x mod 7681"
  using of_int_fin7681.rep_eq to_int_fin7681.rep_eq by presburger

lemma of_int_fin7681_to_int_fin7681 [simp]:
  "of_int_fin7681 (to_int_fin7681 x) = x" 
  using fin7681_rep to_int_fin7681.rep_eq to_int_fin7681_hom.injectivity 
    to_int_fin7681_of_int_fin7681 by force

lemma of_int_mod_ring_eq_iff [simp]:
  "(of_int_fin7681 a = of_int_fin7681 b) \<longleftrightarrow>
   ((a mod 7681) = (b mod 7681))"
  by (metis of_int_fin7681.abs_eq of_int_fin7681.rep_eq)

interpretation kyber7681: kyber_spec 256 7681 3 8 "TYPE(fin7681)" "TYPE(3)"
proof (unfold_locales, goal_cases)
  case 4
  then show ?case using prime_7681 prime_int_numeral_eq by blast
next
  case 5
  then show ?case using CARD_fin7681 by auto
next
  case 7
  then show ?case unfolding qr_poly'_fin7681_def by auto
qed auto

end