theory Polynomial_Applications
  imports
    Nagata_Lemmas
    "HOL-Algebra.Polynomial_Divisibility"
begin

section \<open>Polynomial applications\<close>

text \<open>
  This theory packages the first concrete application layer on top of the
  record-based Nagata descent theorem.  The present results isolate the
  abstract ``localize away X'' step for HOL-Algebra polynomial rings,
  together with the standard field-coefficient specialization in which
  X is prime by the degree-one irreducibility criterion.
\<close>

context domain
begin

lemma polynomial_prime_X:
  assumes K: "subfield K R"
  shows "ring_prime\<^bsub>K[X]\<^esub> X"
proof -
  have X_in: "X \<in> carrier (K[X])"
    using var_closed(1)[OF subfieldE(1)[OF K]] .
  have X_irred: "pirreducible K X"
    using degree_one_imp_pirreducible[OF K X_in]
    by (simp add: var_def)
  show ?thesis
    using pprime_iff_pirreducible[OF K X_in] X_irred by simp
qed

lemma polynomial_prime_generated_powers_X:
  assumes K: "subring K R"
    and hX: "ring_prime\<^bsub>K[X]\<^esub> X"
  shows "ring_prime_generated (K[X]) (ring_powers_set (K[X]) X)"
  using ring_prime_generated_powers_set[OF univ_poly_is_ring[OF K] var_closed(1)[OF K] hX] .

end

locale polynomial_away_X_localization =
  fixes R (structure) and P (structure) and S and K
  assumes poly_axioms: "nagata_localization P S"
    and base_axioms: "domain R"
    and P_eq: "P = K[X]"
    and S_eq: "S = ring_powers_set (K[X]) X"
begin

abbreviation loc_ring where "loc_ring \<equiv> eq_obj_rng_of_frac.rec_rng_of_frac P S"

text \<open>
  Once a localization of K[X] at the powers of X has been fixed, Nagata's
  theorem reduces factoriality of K[X] to factoriality of that localization,
  provided X is prime.
\<close>

lemma polynomial_factorial_of_localized_X_factorial:
  assumes K: "subring K R"
    and noeth: "noetherian_domain (K[X])"
    and hX: "ring_prime\<^bsub>K[X]\<^esub> X"
    and loc_fd: "factorial_domain loc_ring"
  shows "factorial_domain (K[X])"
proof -
  have noethP: "noetherian_domain P"
    using noeth unfolding P_eq .
  have hXP: "ring_prime\<^bsub>P\<^esub> X"
    using hX unfolding P_eq .
  have hS: "ring_prime_generated P S"
    unfolding P_eq S_eq
    by (rule domain.polynomial_prime_generated_powers_X[OF base_axioms K hX])
  have fdP: "factorial_domain P"
    by (rule nagata_localization.nagata_theorem[OF poly_axioms noethP hS loc_fd])
  show ?thesis
    using fdP unfolding P_eq .
qed

lemma polynomial_factorial_of_localized_X_factorial_field:
  assumes K: "subfield K R"
    and noeth: "noetherian_domain (K[X])"
    and loc_fd: "factorial_domain loc_ring"
  shows "factorial_domain (K[X])"
proof -
  have hX: "ring_prime\<^bsub>K[X]\<^esub> X"
    by (rule domain.polynomial_prime_X[OF base_axioms K])
  show ?thesis
    by (rule polynomial_factorial_of_localized_X_factorial[
          OF subfieldE(1)[OF K] noeth hX loc_fd])
qed

end

end
