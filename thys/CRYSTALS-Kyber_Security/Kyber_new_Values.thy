theory Kyber_new_Values
imports 
  Crypto_Scheme_new

begin
section \<open>Specification for Kyber with $q=3329$\<close>

text \<open>Since NIST round 2, Kyber changed the modulus $q$ from $7981$ to $3329$.
In the following, a finite type with $3329$ elements is defined and shown to fulfil the 
\<open>prime_card\<close> property.\<close>

typedef fin3329 = "{0..<3329::int}"
morphisms fin3329_rep fin3329_abs
by (rule_tac x = 0 in exI, simp)

setup_lifting type_definition_fin3329


lemma CARD_fin3329 [simp]:
"CARD (fin3329) = 3329" 
unfolding type_definition.card [OF type_definition_fin3329]
by simp

lemma fin3329_nontriv [simp]:
"1 < CARD(fin3329)"
unfolding CARD_fin3329 by auto

text \<open>The type $fin3329$ fulfils the \<open>prime_card\<close> property required by the \<open>kyber_spec\<close> locale.\<close>

lemma prime_3329: "prime (3329::nat)" by eval

instantiation fin3329 :: comm_ring_1
begin

lift_definition zero_fin3329 :: "fin3329" is "0" by simp

lift_definition one_fin3329 :: "fin3329" is "1" by simp

lift_definition plus_fin3329 :: "fin3329 \<Rightarrow> fin3329 \<Rightarrow> fin3329"
  is "(\<lambda>x y. (x+y) mod 3329)"
by auto

lift_definition uminus_fin3329 :: "fin3329 \<Rightarrow> fin3329"
  is "(\<lambda>x. (uminus x) mod 3329)"
by auto

lift_definition minus_fin3329 :: "fin3329 \<Rightarrow> fin3329 \<Rightarrow> fin3329"
  is "(\<lambda>x y. (x-y) mod 3329)"
by auto

lift_definition times_fin3329 :: "fin3329 \<Rightarrow> fin3329 \<Rightarrow> fin3329"
  is "(\<lambda>x y. (x*y) mod 3329)"
by auto


instance 
proof 
  fix a b c ::fin3329
  show "a * b * c = a * (b * c)" 
    by (transfer, simp add: algebra_simps mod_mult_left_eq mod_mult_right_eq)
  show "a + b + c = a + (b + c)" 
    by (transfer, simp add: algebra_simps mod_add_left_eq mod_add_right_eq)
  show "(a + b) * c = a * c + b * c" 
    by (transfer, simp add: algebra_simps mod_add_right_eq  mod_mult_right_eq)
qed (transfer; simp add: algebra_simps mod_add_right_eq; fail)+

end


instantiation fin3329 :: finite
begin
instance 
proof
  show "finite (UNIV :: fin3329 set)" unfolding type_definition.univ [OF type_definition_fin3329]
  by auto
qed
end


instantiation fin3329 :: equal
begin
lift_definition equal_fin3329 :: "fin3329 \<Rightarrow> fin3329 \<Rightarrow> bool" is "(=)" .
instance by (intro_classes, transfer, auto)
end

instantiation fin3329 :: nontriv
begin
instance 
proof
  show "1 < CARD(fin3329)" unfolding CARD_fin3329 by auto
qed
end

instantiation fin3329 :: prime_card
begin
instance 
proof
  show "prime CARD(fin3329)" unfolding CARD_fin3329 using prime_3329
  by blast 
qed
end

text \<open>Now, we can define the quotient type of $R_{3329}$ over \<open>fin3329\<close>.\<close>
instantiation fin3329 :: qr_spec
begin

definition qr_poly'_fin3329:: "fin3329 itself \<Rightarrow> int poly" where
"qr_poly'_fin3329 \<equiv> (\<lambda>_. Polynomial.monom (1::int) 256 + 1)"

instance proof 
have "lead_coeff (qr_poly' TYPE(fin3329)) = 1" unfolding qr_poly'_fin3329_def 
by (simp add: degree_add_eq_left degree_monom_eq)
then show "\<not> int CARD(fin3329) dvd
       lead_coeff (qr_poly' TYPE(fin3329))" 
  unfolding CARD_fin3329 by auto
next
have "degree (qr_poly' TYPE(fin3329)) = 256" unfolding qr_poly'_fin3329_def
by (simp add: degree_add_eq_left degree_monom_eq)
then show "0 < degree (qr_poly' TYPE(fin3329))"  by auto
qed
end

lift_definition to_int_fin3329 :: "fin3329 \<Rightarrow> int" is "\<lambda>x. x" .

lift_definition of_int_fin3329 :: "int \<Rightarrow> fin3329" is "\<lambda>x. (x mod 3329)"
by simp

interpretation to_int_fin3329_hom: inj_zero_hom to_int_fin3329
  by (unfold_locales; transfer, auto)

interpretation of_int_fin3329_hom: zero_hom of_int_fin3329
  by (unfold_locales, transfer, auto)

lemma to_int_fin3329_of_int_fin3329 [simp]:
"to_int_fin3329 (of_int_fin3329 x) = x mod 3329"
using of_int_fin3329.rep_eq to_int_fin3329.rep_eq by presburger

lemma of_int_fin3329_to_int_fin3329 [simp]:
"of_int_fin3329 (to_int_fin3329 x) = x" 
using fin3329_rep to_int_fin3329.rep_eq to_int_fin3329_hom.injectivity 
to_int_fin3329_of_int_fin3329 by force

lemma of_int_mod_ring_eq_iff [simp]:
  "(of_int_fin3329 a = of_int_fin3329 b) \<longleftrightarrow>
   ((a mod 3329) = (b mod 3329))"
by (metis of_int_fin3329.abs_eq of_int_fin3329.rep_eq)

text \<open>Finally, we show that the Kyber algorithms can be instantiated with $q=3329$.\<close>

interpretation kyber3329: kyber_spec  256 3329 3 8 "TYPE(fin3329)" "TYPE(3)"
proof (unfold_locales, goal_cases)
  case 4
  then show ?case using prime_3329 prime_int_numeral_eq by blast
next
  case 5
  then show ?case using CARD_fin3329 by auto
next
  case 7
  then show ?case unfolding qr_poly'_fin3329_def by auto
qed auto

end