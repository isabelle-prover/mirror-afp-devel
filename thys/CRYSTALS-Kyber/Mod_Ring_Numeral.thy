theory Mod_Ring_Numeral
imports
  "Berlekamp_Zassenhaus.Poly_Mod" 
  "Berlekamp_Zassenhaus.Poly_Mod_Finite_Field"
  "HOL-Library.Numeral_Type"

begin
section \<open>Lemmas for Simplification of Modulo Equivalences\<close>
lemma to_int_mod_ring_of_int [simp]:
  "to_int_mod_ring (of_int n :: 'a :: nontriv mod_ring) = n mod int CARD('a)"
  by transfer auto

lemma to_int_mod_ring_of_nat [simp]:
  "to_int_mod_ring (of_nat n :: 'a :: nontriv mod_ring) = n mod CARD('a)"
  by transfer (auto simp: of_nat_mod)

lemma to_int_mod_ring_numeral [simp]:
  "to_int_mod_ring (numeral n :: 'a :: nontriv mod_ring) = numeral n mod CARD('a)"
  by (metis of_nat_numeral to_int_mod_ring_of_nat)

lemma of_int_mod_ring_eq_iff [simp]:
  "((of_int a :: 'a :: nontriv mod_ring) = of_int b) \<longleftrightarrow>
   ((a mod CARD('a)) = (b mod CARD('a)))"
  by (metis to_int_mod_ring_hom.eq_iff to_int_mod_ring_of_int)

lemma of_nat_mod_ring_eq_iff [simp]:
  "((of_nat a :: 'a :: nontriv mod_ring) = of_nat b) \<longleftrightarrow>
   ((a mod CARD('a)) = (b mod CARD('a)))"
  by (metis of_nat_eq_iff to_int_mod_ring_hom.eq_iff to_int_mod_ring_of_nat)

lemma one_eq_numeral_mod_ring_iff [simp]:
  "(1 :: 'a :: nontriv mod_ring) = numeral a \<longleftrightarrow> (1 mod CARD('a)) = (numeral a mod CARD('a))"
  using of_nat_mod_ring_eq_iff[of 1 "numeral a", where ?'a = 'a]
  by (simp del: of_nat_mod_ring_eq_iff)

lemma numeral_eq_one_mod_ring_iff [simp]:
  "numeral a = (1 :: 'a :: nontriv mod_ring) \<longleftrightarrow> (numeral a mod CARD('a)) = (1 mod CARD('a))"
  using of_nat_mod_ring_eq_iff[of "numeral a" 1, where ?'a = 'a]
  by (simp del: of_nat_mod_ring_eq_iff)

lemma zero_eq_numeral_mod_ring_iff [simp]:
  "(0 :: 'a :: nontriv mod_ring) = numeral a \<longleftrightarrow> 0 = (numeral a mod CARD('a))"
  using of_nat_mod_ring_eq_iff[of 0 "numeral a", where ?'a = 'a]
  by (simp del: of_nat_mod_ring_eq_iff)

lemma numeral_eq_zero_mod_ring_iff [simp]:
  "numeral a = (0 :: 'a :: nontriv mod_ring) \<longleftrightarrow> (numeral a mod CARD('a)) = 0"
  using of_nat_mod_ring_eq_iff[of "numeral a" 0, where ?'a = 'a]
  by (simp del: of_nat_mod_ring_eq_iff)

lemma numeral_mod_ring_eq_iff [simp]:
  "((numeral a :: 'a :: nontriv mod_ring) = numeral b) \<longleftrightarrow>
   ((numeral a mod CARD('a)) = (numeral b mod CARD('a)))"
  using of_nat_mod_ring_eq_iff[of "numeral a" "numeral b", where ?'a = 'a]
  by (simp del: of_nat_mod_ring_eq_iff)


instantiation bit1 :: (finite) nontriv
begin
instance proof
  show "1 < CARD('a bit1)" by simp
qed
end



end