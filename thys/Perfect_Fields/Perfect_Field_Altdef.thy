(*
  File:      Perfect_Fields/Perfect_Field_Altdef.thy
  Authors:   Katharina Kreuzer (TU München)
             Manuel Eberl (University of Innsbruck)

  Proof that a field where every irreducible polynomial is separable is perfect.
  This effectively shows that our definition is equivalent to the textbook one.

  We put this in a separate file because importing HOL-Algebra.Algebraic_Closure
  comes with a lot of annoying baggage that we don't want to pollute our namespace
  with.
*)
subsection \<open>Alternative definition of perfect fields\<close>
theory Perfect_Field_Altdef
imports 
  Algebraic_Closure_Type
  Perfect_Fields
  Perfect_Field_Algebraically_Closed
  "HOL-Computational_Algebra.Field_as_Ring"
begin

(* TODO: Orphan instance. Move! *)
instance poly :: ("{field, normalization_euclidean_semiring, factorial_ring_gcd,
                    semiring_gcd_mult_normalize}") factorial_semiring_multiplicative ..

text \<open>
  In the following, we will show that our definition of perfect fields is equivalent
  to the usual textbook one (for example \cite{conrad}). 
That is: a field in which every irreducible polynomial is separable
  (or, equivalently, has non-zero derivative) either has characteristic $0$ or a surjective
  Frobenius endomorphism.

  The proof works like this:

  Let's call our field \<open>K\<close> with prime characteristic \<open>p\<close>.
  Suppose there were some \<open>c \<in> K\<close> that is not a \<open>p\<close>-th root.
  The polynomial $P := X^p - c$ in $K[X]$ clearly has a zero derivative and is therefore
  not separable. By our assumption, it must then have a monic non-trivial factor
  $Q \in K[X]$.

  Let \<open>L\<close> be some field extension of \<open>K\<close> where \<open>c\<close> does have a \<open>p\<close>-th root \<open>\<alpha>\<close> (in our
  case, we choose \<open>L\<close> to be the algebraic closure of \<open>K\<close>).

  Clearly, \<open>Q\<close> is also a non-trivial factor of \<open>P\<close> in \<open>L\<close>. However, we also
  have \<open>P = X^p - c = X^p - \<alpha>^p = (X - \<alpha>)^p\<close>, so we must have $Q = (X - \alpha )^m$
  for some \<open>0 \<le> m < p\<close> since \<open>X - \<alpha>\<close> is prime.

  However, the coefficient of $X^{m-1}$ in $(X - \alpha )^m$ is \<open>-m\<alpha>\<close>, and since
  \<open>Q \<in> K[X]\<close> we must have \<open>-m\<alpha> \<in> K\<close> and therefore \<open>\<alpha> \<in> K\<close>.
\<close>
theorem perfect_field_alt:
  assumes "\<And>p :: 'a :: field_gcd poly. Factorial_Ring.irreducible p \<Longrightarrow> pderiv p \<noteq> 0"
  shows   "CHAR('a) = 0 \<or> surj (frob :: 'a \<Rightarrow> 'a)"
proof (cases "CHAR('a) = 0")
  case False
  let ?p = "CHAR('a)"
  from False have "Factorial_Ring.prime ?p"
    by (simp add: prime_CHAR_semidom)
  hence "?p > 1"
    using prime_gt_1_nat by blast
  note p = \<open>Factorial_Ring.prime ?p\<close> \<open>?p > 1\<close>

  interpret to_ac: map_poly_inj_comm_ring_hom "to_ac :: 'a \<Rightarrow> 'a alg_closure"
    by unfold_locales auto

  have "surj (frob :: 'a \<Rightarrow> 'a)"
  proof safe
    fix c :: 'a
    obtain \<alpha> :: "'a alg_closure" where \<alpha>: "\<alpha> ^ ?p = to_ac c"
      using p nth_root_exists[of ?p "to_ac c"] by auto
    define P where "P = Polynomial.monom 1 ?p + [:-c:]"
    define P' where "P' = map_poly to_ac P"
    have deg: "Polynomial.degree P = ?p"
      unfolding P_def using p by (subst degree_add_eq_left) (auto simp: degree_monom_eq)

    have "[:-\<alpha>, 1:] ^ ?p = ([:0, 1:] + [:-\<alpha>:]) ^ ?p"
      by (simp add: one_pCons)
    also have "\<dots> = [:0, 1:] ^ ?p - [:\<alpha>^?p:]"
      using p by (subst freshmans_dream) (auto simp: poly_const_pow minus_power_prime_CHAR)
    also have "\<alpha> ^ ?p = to_ac c"
      by (simp add: \<alpha>)
    also have "[:0, 1:] ^ CHAR('a) - [:to_ac c:] = P'"
      by (simp add: P_def P'_def to_ac.hom_add to_ac.hom_power 
               to_ac.base.map_poly_pCons_hom monom_altdef)
    finally have eq: "P' = [:-\<alpha>, 1:] ^ ?p" ..

    have "\<not>is_unit P" "P \<noteq> 0"
      using deg p by auto
    then obtain Q where Q: "Factorial_Ring.prime Q" "Q dvd P"
      by (metis prime_divisor_exists)
    have "monic Q"
      using unit_factor_prime[OF Q(1)] by (auto simp: unit_factor_poly_def one_pCons)

    from Q(2) have "map_poly to_ac Q dvd P'"
      by (auto simp: P'_def)
    hence "map_poly to_ac Q dvd [:-\<alpha>, 1:] ^ ?p"
      by (simp add: \<open>P' = [:-\<alpha>, 1:] ^ ?p\<close>)
    moreover have "Factorial_Ring.prime_elem [:-\<alpha>, 1:]"
      by (intro prime_elem_linear_field_poly) auto
    hence "Factorial_Ring.prime [:-\<alpha>, 1:]"
      unfolding Factorial_Ring.prime_def by (auto simp: normalize_monic)
    ultimately obtain m where "m \<le> ?p" "normalize (map_poly to_ac Q) = [:-\<alpha>, 1:] ^ m"
      using divides_primepow by blast
    hence "map_poly to_ac Q = [:-\<alpha>, 1:] ^ m"
      using \<open>monic Q\<close> by (subst (asm) normalize_monic) auto
    moreover from this have "m > 0"
      using Q by (intro Nat.gr0I) auto
    moreover have "m \<noteq> ?p"
    proof
      assume "m = ?p"
      hence "Q = P"
        using \<open>map_poly to_ac Q = [:-\<alpha>, 1:] ^ m\<close> eq
        by (simp add: P'_def to_ac.injectivity)
      with Q have "Factorial_Ring.irreducible P"
        using idom_class.prime_elem_imp_irreducible by blast
      with assms have "pderiv P \<noteq> 0"
        by blast
      thus False
        by (auto simp: P_def pderiv_add pderiv_monom of_nat_eq_0_iff_char_dvd)
    qed
    ultimately have m: "m \<in> {0<..<?p}" "map_poly to_ac Q = [:-\<alpha>, 1:] ^ m"
      using \<open>m \<le> ?p\<close> by auto

    from m(1) have "\<not>?p dvd m"
      using p by auto
    have "poly.coeff ([:-\<alpha>, 1:] ^ m) (m - 1) = - of_nat (m choose (m - 1)) * \<alpha>"
      using m(1) by (subst coeff_linear_poly_power) auto
    also have "m choose (m - 1) = m"
      using \<open>0 < m\<close> by (subst binomial_symmetric) auto
    also have "[:-\<alpha>, 1:] ^ m = map_poly to_ac Q"
      using m(2) ..
    also have "poly.coeff \<dots> (m - 1) = to_ac (poly.coeff Q (m - 1))"
      by simp
    finally have "\<alpha> = to_ac (-poly.coeff Q (m - 1) / of_nat m)"
      using m(1) p \<open>\<not>?p dvd m\<close> by (auto simp: field_simps of_nat_eq_0_iff_char_dvd)
    hence "(- poly.coeff Q (m - 1) / of_nat m) ^ ?p = c"
      using \<alpha> by (metis to_ac.base.eq_iff to_ac.base.hom_power)
    thus "c \<in> range frob"
      unfolding frob_def by blast
  qed auto
  thus ?thesis ..
qed auto

corollary perfect_field_alt':
  assumes "\<And>p :: 'a :: field_gcd poly. Factorial_Ring.irreducible p \<Longrightarrow> Rings.coprime p (pderiv p)"
  shows   "CHAR('a) = 0 \<or> surj (frob :: 'a \<Rightarrow> 'a)"
proof (rule perfect_field_alt)
  fix p :: "'a poly"
  assume p: "Factorial_Ring.irreducible p"
  with assms[OF p] show "pderiv p \<noteq> 0"
    by auto
qed

end
