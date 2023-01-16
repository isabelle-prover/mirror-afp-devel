section \<open>Introduction\<close>

text \<open>The following section starts with preliminary results. Section~\ref{sec:ring_char} introduces
the characteristic of rings with the Frobenius endomorphism. Whenever it makes sense,
the definitions and facts do not assume the finiteness of the fields or rings. For example the
characteristic is defined over arbitrary rings (and also fields). 

While formal derivatives do exist for type-class based structures in
\verb|HOL-Computational_Algebra|, as far as I can tell, they do not exist for the structure based
polynomials in \verb|HOL-Algebra|. These are introduced in Section~\ref{sec:pderiv}.

A cornerstone of the proof is the derivation of Gauss' formula for the number of monic irreducible
polynomials over a finite field $R$ in Section~\ref{sec:card_irred}. The proof follows the
derivation by Ireland and Rosen~\<^cite>\<open>\<open>\textsection 7\<close> in "ireland1982"\<close> closely, with the caveat that it
does not assume that $R$ is a simple prime field, but that it is just a finite field.
This works by adjusting a proof step with the information that the order of a finite field must be 
of the form $p^n$, where $p$ is the characteristic of the field, derived in Section~\ref{sec:ring_char}.
The final step relies on the M\"obius inversion theorem formalized by
Eberl~\<^cite>\<open>"Dirichlet_Series-AFP"\<close>.\footnote{Thanks to Katharina Kreuzer for discovering that
formalization.}

With Gauss' formula it is possible to show the existence of the finite fields of order $p^n$ 
where $p$ is a prime and $n > 0$. During the proof the fact that the polynomial $X^n - X$ splits
in a field of order $n$ is also derived, which is necessary for the uniqueness result as well.

The uniqueness proof is inspired by the derivation of the same result in
Lidl and Niederreiter~\<^cite>\<open>"lidl1986"\<close>, but because of the already derived existence proof for 
irreducible polynomials, it was possible to reduce its complexity.

The classification consists of three theorems:
\begin{itemize}
\item \emph{Existence}: For each prime power $p^n$ there exists a finite field of that size. 
  This is shown at the conclusion of Section~\ref{sec:card_irred}.
\item \emph{Uniqueness}: Any two finite fields of the same size are isomorphic. 
  This is shown at the conclusion of Section~\ref{sec:uniqueness}.
\item \emph{Completeness}: Any finite fields' size must be a prime power. 
  This is shown at the conclusion of Section~\ref{sec:ring_char}.
\end{itemize}
\<close>

section \<open>Preliminary Results\<close>

theory Finite_Fields_Preliminary_Results
  imports "HOL-Algebra.Polynomial_Divisibility"
begin

subsection \<open>Summation in the discrete topology\<close>

text \<open>The following lemmas transfer the corresponding result from the summation over finite sets
to summation over functions which vanish outside of a finite set.\<close>

lemma sum'_subtractf_nat:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "finite {i \<in> A. f i \<noteq> 0}"
  assumes "\<And>i. i \<in> A \<Longrightarrow> g i \<le> f i"
  shows "sum' (\<lambda>i. f i - g i) A = sum' f A - sum' g A"
    (is "?lhs = ?rhs")
proof -
  have c:"finite {i \<in> A. g i \<noteq> 0}"
    using assms(2)
    by (intro finite_subset[OF _ assms(1)] subsetI, force) 
  let ?B = "{i \<in> A. f i \<noteq> 0 \<or> g i \<noteq> 0}"

  have b:"?B = {i \<in> A. f i \<noteq> 0} \<union> {i \<in> A. g i \<noteq> 0}"
    by (auto simp add:set_eq_iff)
  have a:"finite ?B"
    using assms(1) c by (subst b, simp)
  have "?lhs = sum' (\<lambda>i. f i - g i) ?B"
    by (intro sum.mono_neutral_cong_right', simp_all)
  also have "... = sum (\<lambda>i. f i - g i) ?B"
    by (intro sum.eq_sum a) 
  also have "... = sum f ?B - sum g ?B"
    using assms(2) by (subst sum_subtractf_nat, auto)
  also have "... = sum' f ?B - sum' g ?B"
    by (intro arg_cong2[where f="(-)"] sum.eq_sum[symmetric] a)
  also have "... = ?rhs"
    by (intro arg_cong2[where f="(-)"] sum.mono_neutral_cong_left')
      simp_all
  finally show ?thesis
    by simp
qed

lemma sum'_nat_eq_0_iff:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "finite {i \<in> A. f i \<noteq> 0}"
  assumes "sum' f A = 0"
  shows "\<And>i. i \<in> A \<Longrightarrow> f i = 0"
proof -
  let ?B = "{i \<in> A. f i \<noteq> 0}"

  have "sum f ?B = sum' f ?B"
    by (intro sum.eq_sum[symmetric] assms(1))
  also have "... = sum' f A"
    by (intro sum.non_neutral')
  also have "... = 0" using assms(2) by simp
  finally have a:"sum f ?B = 0" by simp
  have "\<And>i. i \<in> ?B \<Longrightarrow> f i = 0"
    using sum_nonneg_0[OF assms(1) _ a] by blast
  thus "\<And>i. i \<in> A \<Longrightarrow> f i = 0"
    by blast
qed

lemma sum'_eq_iff:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "finite {i \<in> A. f i \<noteq> 0}"
  assumes "\<And>i. i \<in> A \<Longrightarrow> f i \<ge> g i"
  assumes "sum' f A \<le> sum' g A"
  shows "\<forall>i \<in> A. f i = g i"
proof -
  have "{i \<in> A. g i \<noteq> 0} \<subseteq> {i \<in> A. f i \<noteq> 0}"
    using assms(2) order_less_le_trans 
    by (intro subsetI, auto) 
  hence a:"finite {i \<in> A. g i \<noteq> 0}"
    by (rule finite_subset, intro assms(1))
  have " {i \<in> A. f i - g i \<noteq> 0} \<subseteq> {i \<in> A. f i \<noteq> 0}" 
    by (intro subsetI, simp_all)
  hence b: "finite {i \<in> A. f i - g i \<noteq> 0}" 
    by (rule finite_subset, intro assms(1))
  have "sum' (\<lambda>i. f i - g i) A = sum' f A - sum' g A"
    using assms(1,2) a by (subst sum'_subtractf_nat, auto) 
  also have "... = 0"
    using assms(3) by simp
  finally have "sum' (\<lambda>i. f i - g i) A = 0" by simp
  hence "\<And>i. i \<in> A \<Longrightarrow> f i - g i = 0"
    using sum'_nat_eq_0_iff[OF b] by simp
  thus ?thesis
    using assms(2) diff_is_0_eq' diffs0_imp_equal by blast
qed

subsection \<open>Polynomials\<close>

text \<open>The embedding of the constant polynomials into the polynomials is injective:\<close>

lemma (in ring) poly_of_const_inj:
  "inj poly_of_const"
proof -
  have "coeff (poly_of_const x) 0 = x" for x 
    unfolding poly_of_const_def normalize_coeff[symmetric]
    by simp
  thus ?thesis by (metis injI)
qed

lemma (in domain) embed_hom:
  assumes "subring K R"
  shows "ring_hom_ring (K[X]) (poly_ring R) id"
proof (rule ring_hom_ringI)
  show "ring (K[X])"
    using univ_poly_is_ring[OF assms(1)] by simp
  show "ring (poly_ring R)"
    using univ_poly_is_ring[OF carrier_is_subring] by simp
  have "K \<subseteq> carrier R" 
    using subringE(1)[OF assms(1)] by simp
  thus "\<And>x. x \<in> carrier (K [X]) \<Longrightarrow> id x \<in> carrier (poly_ring R)"
    unfolding univ_poly_carrier[symmetric] polynomial_def by auto
  show "id (x \<otimes>\<^bsub>K [X]\<^esub> y) = id x \<otimes>\<^bsub>poly_ring R\<^esub> id y" 
    if "x \<in> carrier (K [X])" "y \<in> carrier (K [X])" for x y
    unfolding univ_poly_mult by simp
  show "id (x \<oplus>\<^bsub>K [X]\<^esub> y) = id x \<oplus>\<^bsub>poly_ring R\<^esub> id y"
    if "x \<in> carrier (K [X])" "y \<in> carrier (K [X])" for x y
    unfolding univ_poly_add by simp
  show "id \<one>\<^bsub>K [X]\<^esub> = \<one>\<^bsub>poly_ring R\<^esub>"
    unfolding univ_poly_one by simp
qed

text \<open>The following are versions of the properties of the degrees of polynomials, that abstract
over the definition of the polynomial ring structure. In the theories
@{theory "HOL-Algebra.Polynomials"} and also @{theory "HOL-Algebra.Polynomial_Divisibility"}
these abstract version are usually indicated with the suffix ``shell'', consider for example:
@{thm [source] "domain.pdivides_iff_shell"}.\<close>

lemma (in ring) degree_add_distinct:
  assumes "subring K R" 
  assumes "f \<in> carrier (K[X]) - {\<zero>\<^bsub>K[X]\<^esub>}"
  assumes "g \<in> carrier (K[X]) - {\<zero>\<^bsub>K[X]\<^esub>}"
  assumes "degree f \<noteq> degree g"
  shows "degree (f \<oplus>\<^bsub>K[X]\<^esub> g) = max (degree f) (degree g)"
  unfolding univ_poly_add using assms(2,3,4) 
  by (subst poly_add_degree_eq[OF assms(1)])
    (auto simp:univ_poly_carrier univ_poly_zero)

lemma (in domain) degree_mult:
  assumes "subring K R" 
  assumes "f \<in> carrier (K[X]) - {\<zero>\<^bsub>K[X]\<^esub>}"
  assumes "g \<in> carrier (K[X]) - {\<zero>\<^bsub>K[X]\<^esub>}"
  shows "degree (f \<otimes>\<^bsub>K[X]\<^esub> g) = degree f + degree g"
  unfolding univ_poly_mult using assms(2,3) 
  by (subst poly_mult_degree_eq[OF assms(1)])
    (auto simp:univ_poly_carrier univ_poly_zero)

lemma (in ring) degree_one:
  "degree (\<one>\<^bsub>K[X]\<^esub>) = 0"
  unfolding univ_poly_one by simp

lemma (in domain) pow_non_zero: 
  "x \<in> carrier R \<Longrightarrow> x \<noteq> \<zero> \<Longrightarrow> x [^] (n :: nat) \<noteq> \<zero>"
  using integral by (induction n, auto) 

lemma (in domain) degree_pow:
  assumes "subring K R" 
  assumes "f \<in> carrier (K[X]) - {\<zero>\<^bsub>K[X]\<^esub>}"
  shows "degree (f [^]\<^bsub>K[X]\<^esub> n) = degree f * n"
proof -
  interpret p:domain "K[X]"
    using univ_poly_is_domain[OF assms(1)] by simp

  show ?thesis
  proof (induction n)
    case 0
    then show ?case by (simp add:univ_poly_one)
  next
    case (Suc n)
    have "degree (f [^]\<^bsub>K [X]\<^esub> Suc n) = degree (f [^]\<^bsub>K [X]\<^esub> n \<otimes>\<^bsub>K[X]\<^esub> f)"
      by simp
    also have "... = degree (f [^]\<^bsub>K [X]\<^esub> n) + degree f"
      using p.pow_non_zero assms(2)
      by (subst degree_mult[OF assms(1)], auto)
    also have "... = degree f * Suc n"
      by (subst Suc, simp)
    finally show ?case by simp
  qed
qed

lemma (in ring) degree_var:
  "degree (X\<^bsub>R\<^esub>) = 1"
  unfolding var_def by simp

lemma (in domain) var_carr:
  fixes n :: nat
  assumes "subring K R"
  shows "X\<^bsub>R\<^esub> \<in> carrier (K[X]) - {\<zero>\<^bsub>K [X]\<^esub>}"
proof -
  have "X\<^bsub>R\<^esub> \<in> carrier (K[X])" 
    using var_closed[OF assms(1)] by simp
  moreover have "X \<noteq> \<zero>\<^bsub>K [X]\<^esub>"
    unfolding var_def univ_poly_zero by simp
  ultimately show ?thesis by simp
qed

lemma (in domain) var_pow_carr:
  fixes n :: nat
  assumes "subring K R"
  shows "X\<^bsub>R\<^esub> [^]\<^bsub>K [X]\<^esub> n \<in> carrier (K[X]) - {\<zero>\<^bsub>K [X]\<^esub>}"
proof -
  interpret p:domain "K[X]"
    using univ_poly_is_domain[OF assms(1)] by simp

  have "X\<^bsub>R\<^esub> [^]\<^bsub>K [X]\<^esub> n \<in> carrier (K[X])" 
    using var_pow_closed[OF assms(1)] by simp
  moreover have "X \<noteq> \<zero>\<^bsub>K [X]\<^esub>"
    unfolding var_def univ_poly_zero by simp
  hence "X\<^bsub>R\<^esub> [^]\<^bsub>K [X]\<^esub> n \<noteq> \<zero>\<^bsub>K [X]\<^esub>"
    using var_closed(1)[OF assms(1)]
    by (intro p.pow_non_zero, auto)
  ultimately show ?thesis by simp
qed

lemma (in domain) var_pow_degree:
  fixes n :: nat
  assumes "subring K R"
  shows "degree (X\<^bsub>R\<^esub> [^]\<^bsub>K [X]\<^esub> n) = n"
  using var_carr[OF assms(1)] degree_var
  by (subst degree_pow[OF assms(1)], auto)

lemma (in domain) finprod_non_zero:
  assumes "finite A"
  assumes "f \<in> A \<rightarrow> carrier R - {\<zero>}"
  shows "(\<Otimes>i \<in> A. f i) \<in> carrier R - {\<zero>}"
  using assms
proof (induction A rule:finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  have "finprod R f (insert x F) = f x \<otimes> finprod R f F"
    using insert by (subst finprod_insert, simp_all add:Pi_def)
  also have "... \<in> carrier R-{\<zero>}"
    using integral insert by auto
  finally show ?case by simp
qed

lemma (in domain) degree_prod:
  assumes "finite A"
  assumes "subring K R" 
  assumes "f \<in> A \<rightarrow> carrier (K[X]) - {\<zero>\<^bsub>K[X]\<^esub>}"
  shows "degree (\<Otimes>\<^bsub>K[X]\<^esub>i \<in> A. f i) = (\<Sum>i \<in> A. degree (f i))"
  using assms
proof -
  interpret p:domain "K[X]"
    using univ_poly_is_domain[OF assms(2)] by simp

  show ?thesis
    using assms(1,3)
  proof (induction A rule: finite_induct)
    case empty
    then show ?case by (simp add:univ_poly_one)
  next
    case (insert x F)
    have "degree (finprod (K[X]) f (insert x F)) = 
      degree (f x \<otimes>\<^bsub>K[X]\<^esub> finprod (K[X]) f F)"
      using insert by (subst p.finprod_insert, auto)
    also have "... = degree (f x) + degree (finprod (K[X]) f F)"
      using insert p.finprod_non_zero[OF insert(1)]
      by (subst degree_mult[OF assms(2)], simp_all) 
    also have "... = degree (f x) + (\<Sum>i \<in> F. degree (f i))"
      using insert by (subst insert(3), auto) 
    also have "... = (\<Sum>i \<in> insert x F. degree (f i))"
      using insert by simp
    finally show ?case by simp
  qed
qed

lemma (in ring) coeff_add:
  assumes "subring K R"
  assumes "f \<in> carrier (K[X])" "g \<in> carrier (K[X])"
  shows "coeff (f \<oplus>\<^bsub>K[X]\<^esub> g) i = coeff f i \<oplus>\<^bsub>R\<^esub> coeff g i"
proof -
  have a:"set f \<subseteq> carrier R"
    using assms(1,2) univ_poly_carrier 
    using subringE(1)[OF assms(1)] polynomial_incl
    by blast
  have b:"set g \<subseteq> carrier R" 
    using assms(1,3) univ_poly_carrier
    using subringE(1)[OF assms(1)] polynomial_incl
    by blast
  show ?thesis
    unfolding univ_poly_add poly_add_coeff[OF a b] by simp
qed

text \<open>This is a version of geometric sums for commutative rings:\<close>

lemma (in cring) geom:
  fixes q:: nat
  assumes [simp]: "a \<in> carrier R"
  shows "(a \<ominus> \<one>) \<otimes> (\<Oplus>i\<in>{..<q}. a [^] i) = (a [^] q \<ominus> \<one>)"
    (is "?lhs = ?rhs")
proof -
  have [simp]: "a [^] i \<in> carrier R" for i :: nat
    by (intro nat_pow_closed assms)
  have [simp]: "\<ominus> \<one> \<otimes> x = \<ominus> x" if "x \<in> carrier R" for x
    using l_minus l_one one_closed that by presburger

  let ?cterm = "(\<Oplus>i\<in>{1..<q}. a [^] i)"

  have "?lhs = a \<otimes> (\<Oplus>i\<in>{..<q}. a [^] i)  \<ominus> (\<Oplus>i\<in>{..<q}. a [^] i)"
    unfolding a_minus_def by (subst l_distr, simp_all add:Pi_def)
  also have "... = (\<Oplus>i\<in>{..<q}. a \<otimes> a [^] i) \<ominus> (\<Oplus>i\<in>{..<q}. a [^] i)"
    by (subst finsum_rdistr, simp_all add:Pi_def)
  also have "... = (\<Oplus>i\<in>{..<q}. a [^] (Suc i)) \<ominus> (\<Oplus>i\<in>{..<q}. a [^] i)"
    by (subst nat_pow_Suc, simp_all add:m_comm)
  also have "... = (\<Oplus>i\<in>Suc ` {..<q}. a [^] i) \<ominus> (\<Oplus>i\<in>{..<q}. a [^] i)"
    by (subst finsum_reindex, simp_all)
  also have "... = 
    (\<Oplus>i\<in> insert q {1..<q}. a [^] i) \<ominus> 
    (\<Oplus>i\<in> insert 0 {1..<q}. a [^] i)"
  proof (cases "q > 0")
    case True
    moreover have "Suc ` {..<q} = insert q {Suc 0..<q}" 
      using True lessThan_atLeast0 by fastforce 
    moreover have "{..<q} = insert 0 {Suc 0..<q}"
      using True by (auto simp add:set_eq_iff) 
    ultimately show ?thesis 
      by (intro arg_cong2[where f="\<lambda>x y. x \<ominus> y"] finsum_cong)
        simp_all
  next
    case False
    then show ?thesis by (simp, algebra)
  qed
  also have "... = (a [^] q \<oplus> ?cterm) \<ominus> (\<one> \<oplus> ?cterm)"
    by simp
  also have "... = a [^] q \<oplus> ?cterm \<oplus> (\<ominus> \<one> \<oplus> \<ominus> ?cterm)"
    unfolding a_minus_def by (subst minus_add, simp_all)
  also have "... = a [^] q \<oplus> (?cterm \<oplus> (\<ominus> \<one> \<oplus> \<ominus> ?cterm))"
    by (subst a_assoc, simp_all)
  also have "... = a [^] q \<oplus> (?cterm \<oplus> (\<ominus> ?cterm \<oplus> \<ominus> \<one>))"
    by (subst a_comm[where x="\<ominus> \<one>"], simp_all)
  also have "... = a [^] q \<oplus> ((?cterm \<oplus> (\<ominus> ?cterm)) \<oplus> \<ominus> \<one>)"
    by (subst a_assoc, simp_all)
  also have "... = a [^] q \<oplus> (\<zero> \<oplus> \<ominus> \<one>)"
    by (subst r_neg, simp_all)
  also have "... = a [^] q \<ominus> \<one>" 
    unfolding a_minus_def by simp
  finally show ?thesis by simp
qed

lemma (in domain) rupture_eq_0_iff:
  assumes "subfield K R" "p \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "rupture_surj K p q = \<zero>\<^bsub>Rupt K p\<^esub> \<longleftrightarrow> p pdivides q"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  interpret h:ring_hom_ring "K[X]" "(Rupt K p)" "(rupture_surj K p)"
    using assms subfieldE by (intro rupture_surj_hom) auto

  have a: "q pmod p \<in> (\<lambda>q. q pmod p) ` carrier (K [X])" 
    using assms(3) by simp
  have "\<zero>\<^bsub>K[X]\<^esub> = \<zero>\<^bsub>K[X]\<^esub> pmod p" 
    using assms(1,2) long_division_zero(2)
    by (simp add:univ_poly_zero)
  hence b: "\<zero>\<^bsub>K[X]\<^esub> \<in> (\<lambda>q. q pmod p) ` carrier (K[X])" 
    by (simp add:image_iff) auto

  have "?lhs \<longleftrightarrow> rupture_surj K p (q pmod p) = 
    rupture_surj K p (\<zero>\<^bsub>K[X]\<^esub>)" 
    by (subst rupture_surj_composed_with_pmod[OF assms]) simp
  also have "... \<longleftrightarrow> q pmod p = \<zero>\<^bsub>K[X]\<^esub>"
    using assms(3)
    by (intro inj_on_eq_iff[OF rupture_surj_inj_on[OF assms(1,2)]] a b)
  also have "... \<longleftrightarrow> ?rhs"
    unfolding univ_poly_zero
    by (intro pmod_zero_iff_pdivides[OF assms(1)] assms(2,3))
  finally show "?thesis" by simp
qed

subsection \<open>Ring Isomorphisms\<close>

text \<open>The following lemma shows that an isomorphism between domains also induces an isomorphism
between the corresponding polynomial rings.\<close>

lemma lift_iso_to_poly_ring:
  assumes "h \<in> ring_iso R S" "domain R" "domain S"
  shows "map h \<in> ring_iso (poly_ring R) (poly_ring S)"
proof (rule ring_iso_memI)
  interpret dr: domain "R" using assms(2) by blast
  interpret ds: domain "S" using assms(3) by blast
  interpret pdr: domain "poly_ring R"
    using dr.univ_poly_is_domain[OF dr.carrier_is_subring] by simp
  interpret pds: domain "poly_ring S"
    using ds.univ_poly_is_domain[OF ds.carrier_is_subring] by simp
  interpret h: ring_hom_ring "R" "S" h
    using dr.ring_axioms ds.ring_axioms assms(1)
    by (intro ring_hom_ringI2, simp_all add:ring_iso_def)
  let ?R = "poly_ring R"
  let ?S = "poly_ring S"

  have h_img: "h ` (carrier R) = carrier S" 
    using assms(1) unfolding ring_iso_def bij_betw_def by auto
  have h_inj: "inj_on h (carrier R)" 
    using assms(1) unfolding ring_iso_def bij_betw_def by auto
  hence h_non_zero_iff:  "h x \<noteq> \<zero>\<^bsub>S\<^esub>"
    if "x \<noteq> \<zero>\<^bsub>R\<^esub>" "x \<in> carrier R" for x
    using h.hom_zero dr.zero_closed inj_onD that by metis

  have norm_elim: "ds.normalize (map h x) = map h x" 
    if "x \<in> carrier (poly_ring R)" for x 
  proof (cases "x")
    case Nil then show ?thesis by simp
  next
    case (Cons xh xt)
    have "xh \<in> carrier R" "xh \<noteq> \<zero>\<^bsub>R\<^esub>"
      using that unfolding Cons univ_poly_carrier[symmetric] 
      unfolding polynomial_def by auto
    hence "h xh \<noteq> \<zero>\<^bsub>S\<^esub>" using h_non_zero_iff by simp
    then show ?thesis unfolding Cons by simp
  qed

  show t_1: "map h x \<in> carrier ?S" 
    if "x \<in> carrier ?R" for x
    using that hd_in_set h_non_zero_iff hd_map
    unfolding univ_poly_carrier[symmetric] polynomial_def 
    by (cases x, auto)

  show "map h (x \<otimes>\<^bsub>?R\<^esub> y) = map h x \<otimes>\<^bsub>?S\<^esub> map h y" 
    if "x \<in> carrier ?R" "y \<in> carrier ?R" for x y
  proof -
    have "map h (x \<otimes>\<^bsub>?R\<^esub> y) = ds.normalize (map h (x \<otimes>\<^bsub>?R\<^esub> y))"
      using that by (intro norm_elim[symmetric],simp) 
    also have "... = map h x \<otimes>\<^bsub>?S\<^esub> map h y"
      using that unfolding univ_poly_mult univ_poly_carrier[symmetric] 
      unfolding polynomial_def
      by (intro h.poly_mult_hom'[of x y] , auto)
    finally show ?thesis by simp
  qed

  show "map h (x \<oplus>\<^bsub>?R\<^esub> y) = map h x \<oplus>\<^bsub>?S\<^esub> map h y"
    if "x \<in> carrier ?R" "y \<in> carrier ?R" for x y
  proof -
    have "map h (x \<oplus>\<^bsub>?R\<^esub> y) = ds.normalize (map h (x \<oplus>\<^bsub>?R\<^esub> y))"
      using that by (intro norm_elim[symmetric],simp) 
    also have "... = map h x \<oplus>\<^bsub>?S\<^esub> map h y"
      using that
      unfolding univ_poly_add univ_poly_carrier[symmetric] 
      unfolding polynomial_def
      by (intro h.poly_add_hom'[of x y], auto)
    finally show ?thesis by simp
  qed

  show "map h \<one>\<^bsub>?R\<^esub> = \<one>\<^bsub>?S\<^esub>" 
    unfolding univ_poly_one by simp

  let ?hinv = "map (the_inv_into (carrier R) h)"

  have "map h \<in> carrier ?R \<rightarrow> carrier ?S" 
    using t_1 by simp
  moreover have "?hinv x \<in> carrier ?R" 
    if "x \<in> carrier ?S" for x
  proof (cases "x = []")
    case True
    then show ?thesis 
      by (simp add:univ_poly_carrier[symmetric] polynomial_def)
  next
    case False
    have set_x: "set x \<subseteq> h ` carrier R" 
      using that h_img unfolding univ_poly_carrier[symmetric]
      unfolding polynomial_def by auto
    have "lead_coeff x \<noteq> \<zero>\<^bsub>S\<^esub>" "lead_coeff x \<in> carrier S"
      using that False unfolding univ_poly_carrier[symmetric]
      unfolding polynomial_def by auto
    hence "the_inv_into (carrier R) h (lead_coeff x) \<noteq> 
      the_inv_into (carrier R) h \<zero>\<^bsub>S\<^esub>" 
      using inj_on_the_inv_into[OF h_inj] inj_onD 
      using ds.zero_closed h_img by metis
    hence "the_inv_into (carrier R) h (lead_coeff x) \<noteq> \<zero>\<^bsub>R\<^esub>" 
      unfolding h.hom_zero[symmetric] 
      unfolding the_inv_into_f_f[OF h_inj dr.zero_closed] by simp
    hence "lead_coeff (?hinv x) \<noteq> \<zero>\<^bsub>R\<^esub>" 
      using False by (simp add:hd_map)
    moreover have "the_inv_into (carrier R) h ` set x \<subseteq> carrier R" 
      using the_inv_into_into[OF h_inj] set_x
      by (intro image_subsetI) auto
    hence "set (?hinv x) \<subseteq> carrier R" by simp 
    ultimately show ?thesis
      by (simp add:univ_poly_carrier[symmetric] polynomial_def)
  qed
  moreover have "?hinv (map h x) = x" if "x \<in> carrier ?R" for x 
  proof -
    have set_x: "set x \<subseteq> carrier R" 
      using that unfolding univ_poly_carrier[symmetric]
      unfolding polynomial_def by auto
    have "?hinv (map h x) = 
      map (\<lambda>y. the_inv_into (carrier R) h (h y)) x"
      by simp
    also have "... = map id x"
      using set_x by (intro map_cong)
        (auto simp add:the_inv_into_f_f[OF h_inj])
    also have "... = x" by simp
    finally show ?thesis by simp
  qed
  moreover have "map h (?hinv x) = x" 
    if "x \<in> carrier ?S" for x
  proof -
    have set_x: "set x \<subseteq> h ` carrier R" 
      using that h_img unfolding univ_poly_carrier[symmetric]
      unfolding polynomial_def by auto
    have "map h (?hinv x) = 
      map (\<lambda>y. h (the_inv_into (carrier R) h y)) x"
      by simp
    also have "... = map id x"
      using set_x by (intro map_cong)
        (auto simp add:f_the_inv_into_f[OF h_inj])
    also have "... = x" by simp
    finally show ?thesis by simp
  qed
  ultimately show "bij_betw (map h) (carrier ?R) (carrier ?S)" 
    by (intro bij_betwI[where g="?hinv"], auto) 
qed

lemma carrier_hom:
  assumes "f \<in> carrier (poly_ring R)"
  assumes "h \<in> ring_iso R S" "domain R" "domain S"
  shows "map h f \<in> carrier (poly_ring S)"
proof -
  note poly_iso = lift_iso_to_poly_ring[OF assms(2,3,4)] 
  show ?thesis
    using ring_iso_memE(1)[OF poly_iso assms(1)] by simp
qed

lemma carrier_hom':
  assumes "f \<in> carrier (poly_ring R)"
  assumes "h \<in> ring_hom R S"
  assumes "domain R" "domain S" 
  assumes "inj_on h (carrier R)"
  shows "map h f \<in> carrier (poly_ring S)"
proof -
  let ?S = "S \<lparr> carrier := h ` carrier R \<rparr>"

  interpret dr: domain "R" using assms(3) by blast
  interpret ds: domain "S" using assms(4) by blast
  interpret h1: ring_hom_ring R S h
    using assms(2) ring_hom_ringI2 dr.ring_axioms 
    using ds.ring_axioms by blast 
  have subr: "subring (h ` carrier R) S" 
    using h1.img_is_subring[OF dr.carrier_is_subring] by blast
  interpret h: ring_hom_ring "((h ` carrier R)[X]\<^bsub>S\<^esub>)" "poly_ring S" "id"
    using ds.embed_hom[OF subr] by simp

  let ?S = "S \<lparr> carrier := h ` carrier R \<rparr>"
  have "h \<in> ring_hom R ?S"
    using assms(2) unfolding ring_hom_def by simp
  moreover have "bij_betw h (carrier R) (carrier ?S)"
    using assms(5) bij_betw_def by auto
  ultimately have h_iso: "h \<in> ring_iso R ?S"
    unfolding ring_iso_def by simp

  have dom_S: "domain ?S" 
    using ds.subring_is_domain[OF subr] by simp

  note poly_iso = lift_iso_to_poly_ring[OF h_iso assms(3) dom_S]
  have "map h f \<in> carrier (poly_ring ?S)"
    using ring_iso_memE(1)[OF poly_iso assms(1)] by simp
  also have "carrier (poly_ring ?S) = 
    carrier (univ_poly S (h ` carrier R))"
    using ds.univ_poly_consistent[OF subr] by simp
  also have "... \<subseteq> carrier (poly_ring S)"
    using h.hom_closed by auto
  finally show ?thesis by simp
qed

text \<open>The following lemmas transfer properties like divisibility, irreducibility etc. between
ring isomorphisms.\<close>

lemma divides_hom:
  assumes "h \<in> ring_iso R S" 
  assumes "domain R" "domain S" 
  assumes "x \<in> carrier R" "y \<in> carrier R"
  shows "x divides\<^bsub>R\<^esub> y \<longleftrightarrow> (h x) divides\<^bsub>S\<^esub> (h y)"  (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  interpret dr: domain "R" using assms(2) by blast
  interpret ds: domain "S" using assms(3) by blast
  interpret pdr: domain "poly_ring R"
    using dr.univ_poly_is_domain[OF dr.carrier_is_subring] by simp
  interpret pds: domain "poly_ring S"
    using ds.univ_poly_is_domain[OF ds.carrier_is_subring] by simp
  interpret h: ring_hom_ring "R" "S" h
    using dr.ring_axioms ds.ring_axioms assms(1)
    by (intro ring_hom_ringI2, simp_all add:ring_iso_def)

  have h_inj_on: "inj_on h (carrier R)" 
    using assms(1) unfolding ring_iso_def bij_betw_def by auto
  have h_img: "h ` (carrier R) = carrier S" 
    using assms(1) unfolding ring_iso_def bij_betw_def by auto

  have "?lhs \<longleftrightarrow> (\<exists>c \<in> carrier R. y = x \<otimes>\<^bsub>R\<^esub> c)"
    unfolding factor_def by simp
  also have "... \<longleftrightarrow> (\<exists>c \<in> carrier R. h y = h x \<otimes>\<^bsub>S\<^esub> h c)"
    using assms(4,5) inj_onD[OF h_inj_on]
    by (intro bex_cong, auto simp flip:h.hom_mult) 
  also have "... \<longleftrightarrow> (\<exists>c \<in> carrier S. h y = h x  \<otimes>\<^bsub>S\<^esub> c)"
    unfolding h_img[symmetric] by simp
  also have "... \<longleftrightarrow> ?rhs" 
    unfolding factor_def by simp
  finally show ?thesis by simp
qed

lemma properfactor_hom:
  assumes "h \<in> ring_iso R S" 
  assumes "domain R" "domain S" 
  assumes "x \<in> carrier R" "b \<in> carrier R"
  shows "properfactor R b x \<longleftrightarrow> properfactor S (h b) (h x)" 
  using divides_hom[OF assms(1,2,3)] assms(4,5)
  unfolding properfactor_def by simp

lemma Units_hom:
  assumes "h \<in> ring_iso R S" 
  assumes "domain R" "domain S" 
  assumes "x \<in> carrier R"
  shows "x \<in> Units R \<longleftrightarrow>  h x \<in> Units S"
proof -

  interpret dr: domain "R" using assms(2) by blast
  interpret ds: domain "S" using assms(3) by blast
  interpret pdr: domain "poly_ring R"
    using dr.univ_poly_is_domain[OF dr.carrier_is_subring] by simp
  interpret pds: domain "poly_ring S"
    using ds.univ_poly_is_domain[OF ds.carrier_is_subring] by simp
  interpret h: ring_hom_ring "R" "S" h
    using dr.ring_axioms ds.ring_axioms assms(1)
    by (intro ring_hom_ringI2, simp_all add:ring_iso_def)

  have h_img: "h ` (carrier R) = carrier S" 
    using assms(1) unfolding ring_iso_def bij_betw_def by auto

  have h_inj_on: "inj_on h (carrier R)" 
    using assms(1) unfolding ring_iso_def bij_betw_def by auto

  hence h_one_iff: "h x = \<one>\<^bsub>S\<^esub> \<longleftrightarrow> x = \<one>\<^bsub>R\<^esub>" if "x \<in> carrier R" for x
    using h.hom_one that by (metis dr.one_closed inj_onD)

  have "x \<in> Units R \<longleftrightarrow> 
    (\<exists>y\<in>carrier R. x \<otimes>\<^bsub>R\<^esub> y = \<one>\<^bsub>R\<^esub> \<and> y \<otimes>\<^bsub>R\<^esub> x = \<one>\<^bsub>R\<^esub>)"
    using assms unfolding Units_def by auto
  also have "... \<longleftrightarrow> 
    (\<exists>y\<in>carrier R. h x \<otimes>\<^bsub>S\<^esub> h y = h \<one>\<^bsub>R\<^esub> \<and> h y \<otimes>\<^bsub>S\<^esub> h x = h \<one>\<^bsub>R\<^esub>)"
    using h_one_iff assms by (intro bex_cong, simp_all flip:h.hom_mult)
  also have "... \<longleftrightarrow> 
    (\<exists>y\<in>carrier S. h x \<otimes>\<^bsub>S\<^esub> y = h \<one>\<^bsub>R\<^esub> \<and> y \<otimes>\<^bsub>S\<^esub> h x = \<one>\<^bsub>S\<^esub>)"
    unfolding h_img[symmetric] by simp
  also have "... \<longleftrightarrow> h x \<in> Units S"
    using assms h.hom_closed unfolding Units_def by auto
  finally show ?thesis by simp
qed

lemma irreducible_hom:
  assumes "h \<in> ring_iso R S" 
  assumes "domain R" "domain S" 
  assumes "x \<in> carrier R"
  shows "irreducible R x = irreducible S (h x)"
proof -
  have h_img: "h ` (carrier R) = carrier S" 
    using assms(1) unfolding ring_iso_def bij_betw_def by auto

  have "irreducible R x \<longleftrightarrow> (x \<notin> Units R \<and> 
    (\<forall>b\<in>carrier R. properfactor R b x \<longrightarrow> b \<in> Units R))"
    unfolding Divisibility.irreducible_def by simp
  also have "... \<longleftrightarrow> (x \<notin> Units R \<and> 
    (\<forall>b\<in>carrier R. properfactor S (h b) (h x) \<longrightarrow> b \<in> Units R))"
    using properfactor_hom[OF assms(1,2,3)] assms(4) by simp
  also have "... \<longleftrightarrow> (h x \<notin> Units S \<and> 
    (\<forall>b\<in>carrier R. properfactor S (h b) (h x) \<longrightarrow> h b \<in> Units S))"
    using assms(4) Units_hom[OF assms(1,2,3)] by simp
  also have "...\<longleftrightarrow> (h x \<notin> Units S \<and> 
    (\<forall>b\<in>h ` carrier R. properfactor S b (h x) \<longrightarrow> b \<in> Units S))"
    by simp
  also have "... \<longleftrightarrow> irreducible S (h x)"
    unfolding h_img Divisibility.irreducible_def by simp
  finally show ?thesis by simp
qed

lemma pirreducible_hom:
  assumes "h \<in> ring_iso R S" 
  assumes "domain R" "domain S"
  assumes "f \<in> carrier (poly_ring R)"
  shows "pirreducible\<^bsub>R\<^esub> (carrier R) f = 
    pirreducible\<^bsub>S\<^esub> (carrier S) (map h f)" 
    (is "?lhs = ?rhs")
proof -
  note lift_iso = lift_iso_to_poly_ring[OF assms(1,2,3)]
  interpret dr: domain "R" using assms(2) by blast
  interpret ds: domain "S" using assms(3) by blast
  interpret pdr: domain "poly_ring R"
    using dr.univ_poly_is_domain[OF dr.carrier_is_subring] by simp
  interpret pds: domain "poly_ring S"
    using ds.univ_poly_is_domain[OF ds.carrier_is_subring] by simp

  have mh_inj_on: "inj_on (map h) (carrier (poly_ring R))" 
    using lift_iso unfolding ring_iso_def bij_betw_def by auto
  moreover have "map h \<zero>\<^bsub>poly_ring R\<^esub> = \<zero>\<^bsub>poly_ring S\<^esub>"
    by (simp add:univ_poly_zero)
  ultimately have mh_zero_iff: 
    "map h f = \<zero>\<^bsub>poly_ring S\<^esub> \<longleftrightarrow> f = \<zero>\<^bsub>poly_ring R\<^esub>"
    using assms(4) by (metis pdr.zero_closed inj_onD)

  have "?lhs \<longleftrightarrow> (f \<noteq> \<zero>\<^bsub>poly_ring R\<^esub> \<and> irreducible (poly_ring R) f)"
    unfolding ring_irreducible_def by simp
  also have "... \<longleftrightarrow> 
    (f \<noteq> \<zero>\<^bsub>poly_ring R\<^esub> \<and> irreducible (poly_ring S) (map h f))"
    using irreducible_hom[OF lift_iso] pdr.domain_axioms
    using assms(4) pds.domain_axioms by simp
  also have "... \<longleftrightarrow> 
    (map h f \<noteq> \<zero>\<^bsub>poly_ring S\<^esub> \<and> irreducible (poly_ring S) (map h f))"
    using mh_zero_iff by simp
  also have "... \<longleftrightarrow> ?rhs"
    unfolding ring_irreducible_def by simp
  finally show ?thesis by simp
qed


lemma ring_hom_cong:
  assumes "\<And>x. x \<in> carrier R \<Longrightarrow> f' x = f x" 
  assumes "ring R"
  assumes "f \<in> ring_hom R S"
  shows "f' \<in> ring_hom R S"
proof -
  interpret ring "R" using assms(2) by simp
  show ?thesis 
    using assms(1) ring_hom_memE[OF assms(3)]
    by (intro ring_hom_memI, auto) 
qed

text \<open>The natural homomorphism between factor rings, where one ideal is a subset of the other.\<close>

lemma (in ring) quot_quot_hom: 
  assumes "ideal I R"
  assumes "ideal J R"
  assumes "I \<subseteq> J"
  shows "(\<lambda>x. (J <+>\<^bsub>R\<^esub> x)) \<in> ring_hom (R Quot I) (R Quot J)"  
proof (rule ring_hom_memI)
  interpret ji: ideal J R
    using assms(2) by simp
  interpret ii: ideal I R
    using assms(1) by simp

  have a:"J <+>\<^bsub>R\<^esub> I = J"
    using assms(3) unfolding set_add_def set_mult_def by auto

  show "J <+>\<^bsub>R\<^esub> x \<in> carrier (R Quot J)"
    if "x \<in> carrier (R Quot I)" for x
  proof -
    have " \<exists>y\<in>carrier R. x = I +> y" 
      using that unfolding FactRing_def A_RCOSETS_def' by simp
    then obtain y where y_def: "y \<in> carrier R" "x = I +> y"
      by auto
    have "J <+>\<^bsub>R\<^esub> (I +> y) = (J <+>\<^bsub>R\<^esub> I) +> y"
      using y_def(1) by (subst a_setmult_rcos_assoc) auto
    also have "... = J +> y" using a by simp
    finally have "J <+>\<^bsub>R\<^esub> (I +> y) = J +> y" by simp
    thus ?thesis
      using y_def unfolding FactRing_def A_RCOSETS_def' by auto 
  qed

  show "J <+>\<^bsub>R\<^esub> x \<otimes>\<^bsub>R Quot I\<^esub> y = 
    (J <+>\<^bsub>R\<^esub> x) \<otimes>\<^bsub>R Quot J\<^esub> (J <+>\<^bsub>R\<^esub> y)"
    if "x \<in> carrier (R Quot I)" "y \<in> carrier (R Quot I)" 
    for x y
  proof -
    have "\<exists>x1\<in>carrier R. x = I +> x1" "\<exists>y1\<in>carrier R. y = I +> y1" 
      using that unfolding FactRing_def A_RCOSETS_def' by auto
    then obtain x1 y1 
      where x1_def: "x1 \<in> carrier R" "x = I +> x1"
        and y1_def: "y1 \<in> carrier R" "y = I +> y1"
      by auto
    have "J <+>\<^bsub>R\<^esub> x \<otimes>\<^bsub>R Quot I\<^esub> y = J <+>\<^bsub>R\<^esub> (I +> x1 \<otimes> y1)"
      using x1_def y1_def
      by (simp add: FactRing_def ii.rcoset_mult_add)
    also have "... = (J <+>\<^bsub>R\<^esub> I) +> x1 \<otimes> y1"
      using x1_def(1) y1_def(1)
      by (subst a_setmult_rcos_assoc) auto
    also have "... = J +> x1 \<otimes> y1"
      using a by simp
    also have "... = [mod J:] (J +> x1) \<Otimes> (J +> y1)" 
      using x1_def(1) y1_def(1) by (subst ji.rcoset_mult_add, auto)
    also have "... = 
      [mod J:] ((J <+>\<^bsub>R\<^esub> I) +> x1) \<Otimes> ((J <+>\<^bsub>R\<^esub> I) +> y1)" 
      using a by simp
    also have "... = 
      [mod J:] (J <+>\<^bsub>R\<^esub> (I +> x1)) \<Otimes> (J <+>\<^bsub>R\<^esub> (I +> y1))"
      using x1_def(1) y1_def(1)
      by (subst (1 2) a_setmult_rcos_assoc) auto
    also have "... = (J <+>\<^bsub>R\<^esub> x) \<otimes>\<^bsub>R Quot J\<^esub> (J <+>\<^bsub>R\<^esub> y)"
      using x1_def y1_def by (simp add: FactRing_def)
    finally show ?thesis by simp
  qed

  show "J <+>\<^bsub>R\<^esub> x \<oplus>\<^bsub>R Quot I\<^esub> y = 
    (J <+>\<^bsub>R\<^esub> x) \<oplus>\<^bsub>R Quot J\<^esub> (J <+>\<^bsub>R\<^esub> y)"
    if "x \<in> carrier (R Quot I)" "y \<in> carrier (R Quot I)"
    for x y
  proof -
    have "\<exists>x1\<in>carrier R. x = I +> x1" "\<exists>y1\<in>carrier R. y = I +> y1" 
      using that unfolding FactRing_def A_RCOSETS_def' by auto
    then obtain x1 y1 
      where x1_def: "x1 \<in> carrier R" "x = I +> x1"
        and y1_def: "y1 \<in> carrier R" "y = I +> y1"
      by auto
    have "J <+>\<^bsub>R\<^esub> x \<oplus>\<^bsub>R Quot I\<^esub> y = 
      J <+>\<^bsub>R\<^esub> ((I +> x1) <+>\<^bsub>R\<^esub> (I +> y1))"
      using x1_def y1_def by (simp add:FactRing_def)
    also have "... = J <+>\<^bsub>R\<^esub> (I +> (x1 \<oplus> y1))"
      using x1_def y1_def ii.a_rcos_sum by simp
    also have "... = (J <+>\<^bsub>R\<^esub> I) +> (x1 \<oplus> y1)"
      using x1_def y1_def by (subst a_setmult_rcos_assoc) auto
    also have "... = J +> (x1 \<oplus> y1)"
      using a by simp
    also have "... = 
      ((J <+>\<^bsub>R\<^esub> I) +> x1) <+>\<^bsub>R\<^esub> ((J <+>\<^bsub>R\<^esub> I) +> y1)"
      using x1_def y1_def ji.a_rcos_sum a by simp
    also have "... = 
      J <+>\<^bsub>R\<^esub> (I +> x1) <+>\<^bsub>R\<^esub> (J <+>\<^bsub>R\<^esub> (I +> y1))" 
      using x1_def y1_def by (subst (1 2) a_setmult_rcos_assoc) auto
    also have "... = (J <+>\<^bsub>R\<^esub> x) \<oplus>\<^bsub>R Quot J\<^esub> (J <+>\<^bsub>R\<^esub> y)"
      using x1_def y1_def by (simp add:FactRing_def)
    finally show ?thesis by simp
  qed

  have "J <+>\<^bsub>R\<^esub> \<one>\<^bsub>R Quot I\<^esub> = J <+>\<^bsub>R\<^esub> (I +> \<one>)"
    unfolding FactRing_def by simp
  also have "... = (J <+>\<^bsub>R\<^esub> I) +> \<one>" 
    by (subst a_setmult_rcos_assoc) auto
  also have "... = J +> \<one>" using a by simp
  also have "... = \<one>\<^bsub>R Quot J\<^esub>"
    unfolding FactRing_def by simp
  finally show "J <+>\<^bsub>R\<^esub> \<one>\<^bsub>R Quot I\<^esub> = \<one>\<^bsub>R Quot J\<^esub>" 
    by simp
qed

lemma (in ring) quot_carr:
  assumes "ideal I R"
  assumes "y \<in> carrier (R Quot I)"
  shows "y \<subseteq> carrier R"
proof -
  interpret ideal I R using assms(1) by simp
  have "y \<in> a_rcosets I"
    using assms(2) unfolding FactRing_def by simp
  then obtain v where y_def: "y = I +> v" "v \<in> carrier R"
    unfolding A_RCOSETS_def' by auto
  have "I +> v \<subseteq> carrier R" 
    using y_def(2) a_r_coset_subset_G a_subset by presburger
  thus "y \<subseteq> carrier R" unfolding y_def by simp
qed

lemma (in ring) set_add_zero:
  assumes "A \<subseteq> carrier R"
  shows "{\<zero>} <+>\<^bsub>R\<^esub> A = A"
proof -
  have "{\<zero>} <+>\<^bsub>R\<^esub> A = (\<Union>x\<in>A. {\<zero> \<oplus> x})"
    using assms unfolding set_add_def set_mult_def by simp
  also have "... = (\<Union>x\<in>A. {x})"
    using assms by (intro arg_cong[where f="Union"] image_cong, auto)
  also have "... = A" by simp
  finally show ?thesis by simp
qed

text \<open>Adapted from the proof of @{thm [source] domain.polynomial_rupture}\<close>

lemma (in domain) rupture_surj_as_eval:
  assumes "subring K R" 
  assumes "p \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "rupture_surj K p q = 
    ring.eval (Rupt K p) (map ((rupture_surj K p) \<circ> poly_of_const) q) 
    (rupture_surj K p X)"
proof -
  let ?surj = "rupture_surj K p"

  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF assms(1)] .
  interpret h: ring_hom_ring "K[X]" "Rupt K p" ?surj
    using rupture_surj_hom(2)[OF assms(1,2)] .

  have "(h.S.eval) (map (?surj \<circ> poly_of_const) q) (?surj X) = 
    ?surj ((UP.eval) (map poly_of_const q) X)"
    using h.eval_hom[OF UP.carrier_is_subring var_closed(1)[OF assms(1)]
          map_norm_in_poly_ring_carrier[OF assms(1,3)]] by simp
  also have " ... = ?surj q"
    unfolding sym[OF eval_rewrite[OF assms(1,3)]] ..
  finally show ?thesis by simp
qed

subsection \<open>Divisibility\<close>

lemma  (in field) f_comm_group_1:
  assumes "x \<in> carrier R" "y \<in> carrier R"
  assumes "x \<noteq> \<zero>" "y \<noteq> \<zero>"
  assumes "x \<otimes> y = \<zero>"
  shows "False" 
  using integral assms by auto

lemma (in field) f_comm_group_2:
  assumes "x \<in> carrier R"
  assumes "x \<noteq> \<zero>"
  shows " \<exists>y\<in>carrier R - {\<zero>}. y \<otimes> x = \<one>"
proof -
  have x_unit: "x \<in> Units R" using field_Units assms by simp
  thus ?thesis unfolding Units_def by auto
qed

sublocale field < mult_of: comm_group "mult_of R"
  rewrites "mult (mult_of R) = mult R"
       and "one  (mult_of R) = one R"
  using f_comm_group_1 f_comm_group_2
  by (auto intro!:comm_groupI m_assoc m_comm)

lemma (in domain) div_neg:
  assumes "a \<in> carrier R" "b \<in> carrier R"
  assumes "a divides b"
  shows "a divides (\<ominus> b)"
proof -
  obtain r1 where r1_def: "r1 \<in> carrier R" "a \<otimes> r1 = b"
    using assms by (auto simp:factor_def) 

  have "a \<otimes> (\<ominus> r1) = \<ominus> (a \<otimes> r1)"
    using assms(1) r1_def(1) by algebra
  also have "... = \<ominus> b"
    using r1_def(2) by simp
  finally have "\<ominus>b = a \<otimes> (\<ominus> r1)" by simp
  moreover have "\<ominus>r1 \<in> carrier R"
    using r1_def(1) by simp
  ultimately show ?thesis
    by (auto simp:factor_def) 
qed

lemma (in domain) div_sum:
  assumes "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R"
  assumes "a divides b"
  assumes "a divides c"
  shows "a divides (b \<oplus> c)"
proof -
  obtain r1 where r1_def: "r1 \<in> carrier R" "a \<otimes> r1 = b"
    using assms by (auto simp:factor_def) 

  obtain r2 where r2_def: "r2 \<in> carrier R" "a \<otimes> r2 = c"
    using assms by (auto simp:factor_def) 

  have "a \<otimes> (r1 \<oplus> r2) = (a \<otimes> r1) \<oplus> (a \<otimes> r2)"
    using assms(1) r1_def(1) r2_def(1) by algebra
  also have "... = b \<oplus> c"
    using r1_def(2) r2_def(2) by simp
  finally have "b \<oplus> c = a \<otimes> (r1 \<oplus> r2)" by simp
  moreover have "r1 \<oplus> r2 \<in> carrier R"
    using r1_def(1) r2_def(1) by simp
  ultimately show ?thesis
    by (auto simp:factor_def) 
qed

lemma (in domain) div_sum_iff:
  assumes "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R"
  assumes "a divides b"
  shows "a divides (b \<oplus> c) \<longleftrightarrow> a divides c"
proof 
  assume "a divides (b \<oplus> c)"
  moreover have "a divides (\<ominus> b)"
    using div_neg assms(1,2,4) by simp
  ultimately have "a divides ((b \<oplus> c) \<oplus> (\<ominus> b))"
    using div_sum assms by simp
  also have "... = c" using assms(1,2,3) by algebra
  finally show "a divides c" by simp
next
  assume "a divides c"
  thus "a divides (b \<oplus> c)"
    using assms by (intro div_sum) auto
qed

end
