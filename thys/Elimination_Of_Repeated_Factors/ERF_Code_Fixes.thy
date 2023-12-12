(*
  File:      Elimination_Of_Repeated_Factors/ERF_Code_Fixes.thy
  Authors:   Katharina Kreuzer (TU München)
             Manuel Eberl (University of Innsbruck)

  Some small tweaks to make arithmetic on finite fields properly executable.
  Should probably eventually be moved elsewhere (TODO).
*)
theory ERF_Code_Fixes
  imports Berlekamp_Zassenhaus.Finite_Field 
  Perfect_Fields.Perfect_Fields
begin

section \<open>Code Generation for ERF and Example\<close>

lemma inverse_mod_ring_altdef:
  fixes x :: "'p :: prime_card mod_ring"
  defines "x' \<equiv> Rep_mod_ring x"
  shows   "Rep_mod_ring (inverse x) = fst (bezout_coefficients x' CARD('p)) mod CARD('p)"
proof (cases "x' = 0")
  case False
  define y where "y = fst (bezout_coefficients x' CARD('p))"
  define z where "z = fst (bezout_coefficients x' CARD('p))"
  define p where "p = CARD('p)"
  from False have "coprime x' p"
    by (metis Rep_mod_ring_mod algebraic_semidom_class.coprime_commute 
         dvd_imp_mod_0 prime_card_int prime_imp_coprime p_def assms)
  have "[x' * (y mod p) = x' * y] (mod p)"
    by (intro cong_mult cong_refl) auto
  also have "x' * y = x' * y + 0"
    by simp
  also have "[x' * y + 0 = x' * y + z * p] (mod p)"
    by (intro cong_add cong_refl) (auto simp: cong_def)
  also have "[x' * y + z * p = gcd x' p] (mod p)"
    by (metis bezout_coefficients_fst_snd cong_def mod_mult_self2 mult.commute y_def z_def p_def)
  also have "gcd x' p = 1"
    using \<open>coprime x' p\<close> by auto
  finally have "(x' * (y mod p)) mod p = 1"
    by (simp add: cong_def p_def)
  thus ?thesis
    unfolding p_def y_def x'_def
    by (metis Rep_mod_ring_inverse inverse_unique of_int_mod_ring.rep_eq one_mod_ring.rep_eq times_mod_ring.rep_eq)
next
  case True
  hence "x = 0"
    by (metis Rep_mod_ring_inverse x'_def zero_mod_ring_def)
  thus ?thesis unfolding True
    by (auto simp: x'_def bezout_coefficients_left_0 inverse_mod_ring_def zero_mod_ring.rep_eq)
qed

lemmas inverse_mod_ring_code' [code] =
  inverse_mod_ring_altdef [where 'p = "'p :: {prime_card, card_UNIV}"]

lemma divide_mod_ring_code' [code]:
  "x / (y :: 'p :: {prime_card, card_UNIV} mod_ring) = x * inverse y"
  by (fact divide_inverse)

instantiation mod_ring :: ("{finite, card_UNIV}") card_UNIV
begin
definition "card_UNIV = Phantom('a mod_ring) (of_phantom (card_UNIV :: 'a card_UNIV))"
definition "finite_UNIV = Phantom('a mod_ring) True"
instance 
  by intro_classes
     (simp_all add: finite_UNIV_mod_ring_def finite_UNIV card_UNIV_mod_ring_def card_UNIV)
end

lemmas of_int_mod_ring_code [code] =
  of_int_mod_ring.rep_eq[where ?'a = "'a :: {finite, card_UNIV}"]

lemmas plus_mod_ring_code [code] =
  plus_mod_ring.rep_eq[where ?'a = "'a :: {finite, card_UNIV}"]

lemmas minus_mod_ring_code [code] =
  minus_mod_ring.rep_eq[where ?'a = "'a :: {finite, card_UNIV}"]

lemmas uminus_mod_ring_code [code] =
  uminus_mod_ring.rep_eq[where ?'a = "'a :: {finite, card_UNIV}"]

lemmas times_mod_ring_code [code] =
  times_mod_ring.rep_eq[where ?'a = "'a :: {finite, card_UNIV}"]

lemmas inverse_mod_ring_code [code] =
  inverse_mod_ring_def[where ?'a = "'a :: {prime_card, finite, card_UNIV}"]

lemmas divide_mod_ring_code [code] =
  divide_mod_ring_def[where ?'a = "'a :: {prime_card, finite, card_UNIV}"]

lemma card_UNIV_code:
  "card (UNIV :: 'a :: card_UNIV set) = of_phantom (card_UNIV :: ('a, nat) phantom)"
  by (simp add: card_UNIV)

setup \<open>
  Code_Preproc.map_pre (fn ctxt =>
    ctxt addsimprocs
      [Simplifier.make_simproc \<^context> "card_UNIV"
        {lhss = [\<^term>\<open>card UNIV\<close>],
         proc = fn _ => fn _ => fn ct =>
          SOME @{thm card_UNIV_code [THEN eq_reflection]}}])
\<close>


class semiring_char_code = semiring_1 +
  fixes semiring_char_code :: "('a, nat) phantom"
  assumes semiring_char_code_correct: "semiring_char_code = Phantom('a) CHAR('a)"

instantiation mod_ring :: ("{finite,nontriv,card_UNIV}") semiring_char_code
begin
definition semiring_char_code_mod_ring :: "('a mod_ring, nat) phantom" where
  "semiring_char_code_mod_ring = Phantom('a mod_ring) (of_phantom (card_UNIV :: ('a, nat) phantom))"
instance 
  by standard (auto simp: semiring_char_code_mod_ring_def card_UNIV)
end

instantiation poly :: ("{semiring_char_code, comm_semiring_1}") semiring_char_code
begin
definition
  "semiring_char_code_poly =
      Phantom('a poly) (of_phantom (semiring_char_code :: ('a, nat) phantom))"
instance 
  by standard (auto simp: semiring_char_code_poly_def semiring_char_code_correct)
end

instantiation fps :: ("{semiring_char_code, comm_semiring_1}") semiring_char_code
begin
definition
  "semiring_char_code_fps =
      Phantom('a fps) (of_phantom (semiring_char_code :: ('a, nat) phantom))"
instance 
  by standard (auto simp: semiring_char_code_fps_def semiring_char_code_correct)
end

instantiation fls :: ("{semiring_char_code, comm_semiring_1}") semiring_char_code
begin
definition
  "semiring_char_code_fls =
      Phantom('a fls) (of_phantom (semiring_char_code :: ('a, nat) phantom))"
instance 
  by standard (auto simp: semiring_char_code_fls_def semiring_char_code_correct)
end


lemma semiring_char_code [code]:
  "semiring_char x =
     (if x = TYPE('a :: semiring_char_code) then
        of_phantom (semiring_char_code :: ('a, nat) phantom) else
        Code.abort STR ''semiring_char'' (\<lambda>_. semiring_char x))"
  by (auto simp: semiring_char_code_correct)

end