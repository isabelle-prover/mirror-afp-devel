section \<open>Factorisation of Polynomials\<close>

theory Factorisation
  imports
    "Berlekamp_Zassenhaus.Finite_Field"
    "Berlekamp_Zassenhaus.Finite_Field_Factorization"
    "Elimination_Of_Repeated_Factors.ERF_Perfect_Field_Factorization"
    "Elimination_Of_Repeated_Factors.ERF_Algorithm"
begin

hide_const (open) Coset.order
hide_const (open) module.smult
hide_const (open) UnivPoly.coeff
hide_const (open) Formal_Power_Series.radical

lemma proots_finite_field_factorization:
  assumes
    "square_free f"
    "finite_field_factorization f = (c, us)"
  shows "proots f = sum_list (map proots us)"
proof -
  have fffp: "f = smult c (prod_list us)" "(\<forall> u \<in> set us. monic u \<and> irreducible u)"
    using finite_field_factorization_explicit assms by auto
  then have "0 \<notin> set us"
    by blast
  then have "proots (\<Prod>u\<leftarrow>us. u) = (\<Sum>u\<leftarrow>us. proots u)"
    using proots_prod_list fffp by auto
  then show ?thesis using assms
    by (simp add: fffp square_free_def)
qed

text \<open>The following fact is an improved version of 
@{thm "squarefree_square_free"}, which does not require the assumtion that @{term "p \<noteq> 0"}.\<close>
lemma squarefree_square_free':
  fixes p :: "'a:: field poly"
  shows "squarefree p = square_free p"
  by (metis not_squarefree_0 square_free_def squarefree_square_free)


text \<open>This function returns the roots of an irreducible polynomial:\<close>
fun extract_root :: "'a::prime_card mod_ring poly \<Rightarrow> 'a mod_ring multiset" where
  "extract_root p = (if degree p = 1 then {# - coeff p 0 #} else {#})"

lemma degree1_monic:
  assumes "degree p = 1"
  assumes "monic p"
  obtains c where "p = [:c,1:]"
proof -
  obtain a b where op: "p = [: b, a :]"
    using degree1_coeffs assms(1) by meson
  then have "a = 1"
    using assms by simp
  then show ?thesis
    using op using that by simp
qed

lemma extract_root:
  assumes "monic p" "irreducible p"
  shows "extract_root p = proots p"
proof -
  consider (A) "degree p = 0" | (B) "degree p = 1" | (C) "degree p > 1"
    by linarith
  thus ?thesis
  proof (cases)
    case A
    hence "extract_root p = {#}" by simp
    also have "\<dots> = proots 1" by simp
    also have "\<dots> = proots p" using A assms(1) monic_degree_0 by blast
    finally show ?thesis by simp
  next
    case B
    obtain c where p_def: "p = [:c,1:]"
      using assms(1) B degree1_monic by blast

    hence "proots p = {#-c#}"
      using proots_linear_factor by blast
    also have "\<dots> = extract_root p"
      unfolding p_def by simp
    finally show ?thesis by simp
  next
    case C
    have "False" if "x \<in># proots p" for x
    proof -
      have "p \<noteq> 0" using C by auto
      hence "poly p x = 0" using set_count_proots that by simp
      thus "False" using C assms root_imp_reducible_poly by blast
    qed
    hence "proots p = {#}" by auto
    also have "\<dots> = extract_root p"
      using C by simp
    finally show ?thesis by simp
  qed
qed

fun extract_roots :: "'a::prime_card mod_ring poly list \<Rightarrow> 'a mod_ring multiset" where
  "extract_roots [] = {#}"
| "extract_roots (p#ps) = extract_root p + extract_roots ps"

lemma extract_roots:
  "\<forall> p \<in> set ps. monic p \<and> irreducible p \<Longrightarrow>
    sum_list (map proots ps) = extract_roots ps"
proof (induction ps)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  have "sum_list (map proots (p # ps)) = proots p + sum_list (map proots ps)" by simp
  also have "\<dots> = extract_root p + sum_list (map proots ps)"
    using Cons(2) by (subst extract_root) auto
  also have "\<dots> =  extract_roots (p # ps)" using Cons by simp
  finally show ?case by simp
qed

lemma proots_extract_roots_factorized:
  assumes "squarefree p"
  shows "proots p = extract_roots (snd (finite_field_factorization p))"
proof -
  have sf:"square_free p"
    using squarefree_square_free' assms by blast

  have "proots p = sum_list (map proots (snd (finite_field_factorization p)))"
    using proots_finite_field_factorization[OF sf] by (metis prod.collapse)
  also have "\<dots> = extract_roots (snd (finite_field_factorization p))"
    using finite_field_factorization_explicit[OF sf]
    by (intro extract_roots) (metis prod.collapse)
  finally show ?thesis  by simp
qed


subsection \<open>Elimination of Repeated Factors\<close>

text \<open>Wrapper around the ERF algorithm, which returns each factor with multiplicity in the input
polynomial\<close>

function ERF' where
  "ERF' p = (
    if degree p = 0 then [] else
      let factors = ERF p in
        ERF' (p div (prod_list factors)) @ factors)"
  by auto

lemma degree_zero_iff_no_factors:
  fixes p :: "'a :: {factorial_ring_gcd,semiring_gcd_mult_normalize,field} poly"
  assumes "p \<noteq> 0"
  shows "prime_factors p = {} \<longleftrightarrow> degree p = 0"
proof
  assume "prime_factors p = {}"
  hence "is_unit p" using assms
    by (meson prime_factorization_empty_iff set_mset_eq_empty_iff)
  thus "degree p = 0"
    using poly_dvd_1 by blast
next
  assume "degree p  = 0"
  thus "prime_factors p = {}" using assms prime_factors_degree0 by metis
qed

lemma ERF'_termination:
  assumes "degree p > 0"
  shows "degree (p div prod_list (ERF p)) < degree p"
proof (intro degree_div_less)
  show p_ne_0: "p \<noteq> 0" using assms by auto

  have a:"radical p = prod_list (ERF p)"
    using p_ne_0 ERF_correct(1) by metis

  show "prod_list (ERF p) dvd p" unfolding a[symmetric] by (rule radical_dvd)

  have "prime_factors p \<noteq> {}"
    using p_ne_0 assms(1) degree_zero_iff_no_factors[OF p_ne_0] by simp
  hence "prime_factors (radical p) \<noteq> {}"
    using p_ne_0 prime_factors_radical by metis
  moreover have "radical p \<noteq> 0"
    using radical_eq_0_iff p_ne_0 by auto
  ultimately have "degree (radical p) > 0"
    using degree_zero_iff_no_factors by blast

  thus "degree (prod_list (ERF p)) \<noteq> 0"
    using a by simp
qed

termination
  using ERF'_termination
  by (relation "measure degree") auto

lemma ERF'_squarefree:
  assumes "x \<in> set (ERF' p)"
  shows "squarefree x" using assms
proof (induct p rule: ERF'.induct)
  case (1 p)
  define factors where "factors = ERF p"
  show ?case
  proof (cases "degree p > 0")
    case True
    hence a: "ERF' p = ERF' (p div prod_list factors) @ factors"
      unfolding factors_def
      by (subst ERF'.simps) (simp add:Let_def)
    hence "x \<in> set (ERF' (p div prod_list factors)) \<or> x \<in> set (factors)"
      using 1(2) unfolding a  by simp

    moreover have "x \<in> set (factors) \<Longrightarrow> squarefree x"
      using ERF_correct(2) True factors_def
      by (metis degree_0 order_less_irrefl)
    ultimately show ?thesis
      using 1(1)[OF _ factors_def] True by auto
  next
    case False
    hence  "ERF' p = []" by simp
    thus ?thesis using 1(2) by simp
  qed
qed

lemma ERF_not0: "p \<noteq> 0 \<Longrightarrow> 0 \<notin> set (ERF p)"
  using ERF_correct(2) not_squarefree_0 by blast

lemma ERF'_not0: "0 \<notin> set (ERF' p)"
  using ERF'_squarefree not_squarefree_0 by blast

lemma ERF'_proots: "proots (\<Prod>x\<leftarrow> ERF' p. x) = proots p"
proof (induct p rule: ERF'.induct)
  case (1 p)
  show ?case
  proof (cases "degree p > 0")
    case True
    let ?prod = "prod_list (ERF p)"

    have a:"ERF' p = ERF' (p div ?prod) @ (ERF p)"
      unfolding factors_def
      by (subst ERF'.simps) (simp add:Let_def)

    have h: "proots (\<Prod>x\<leftarrow>ERF' (p div ?prod). x) = proots (p div ?prod)"
      using 1 True by simp

    have p0: "p \<noteq> 0"
      using True by force
    then have l0: "?prod \<noteq> 0"
      using ERF_not0 by simp

    have "radical p dvd p"
      by simp
    then have pdvd: "?prod dvd p"
      using ERF_correct(1) p0 by metis
    then have d0: "(p div ?prod) \<noteq> 0"
      using p0 using dvd_div_eq_0_iff by blast

    have "proots (p div ?prod) + proots ?prod =
      proots (p div ?prod * ?prod)"
      using proots_mult l0 d0 by metis
    then have 1: "proots p = proots (p div ?prod) + proots ?prod"
      using pdvd by simp

    have "(\<Prod>x\<leftarrow>ERF' (p div ?prod). x) \<noteq> 0"
      using ERF'_not0 by force
    then have "proots (\<Prod>x\<leftarrow>ERF' (p div ?prod). x) + proots ?prod
       = proots ((\<Prod>x\<leftarrow>ERF' (p div ?prod). x) * ?prod)"
      using proots_mult l0 by metis
    also have "\<dots> = proots (\<Prod>x\<leftarrow>ERF' p. x)"
      using a by force
    finally have "proots (\<Prod>x\<leftarrow>ERF' p. x) = proots (p div ?prod) + proots ?prod"
      using h by argo

    then show ?thesis using 1 by argo
  next
    case False
    then have deg: "degree p = 0"
      by simp
    then have "ERF' p = []"
      by (subst ERF'.simps) simp
    then have 1: "proots (\<Prod>x\<leftarrow>ERF' p. x) = {#}"
      by simp
    from deg obtain x where "p = [:x:]"
      using degree_eq_zeroE by blast
    then have "proots p = {#}"
      by simp
    thus ?thesis using 1 by simp
  qed
qed


subsection \<open>Executable version of @{term "proots"}\<close>

fun proots_eff :: "'a::prime_card mod_ring poly \<Rightarrow> 'a mod_ring multiset" where
  "proots_eff p = sum_list (map (extract_roots \<circ> snd \<circ> finite_field_factorization) (ERF' p))"

lemma proots_eff_correct [code_unfold]: "proots p = proots_eff p"
proof -
  have "proots p = proots (\<Prod>x\<leftarrow> ERF' p. x)"
    using ERF'_proots  by metis
  also have "\<dots> = sum_list (map proots (ERF' p))"
    using ERF'_squarefree not_squarefree_0 by (intro proots_prod_list) blast
  also have "\<dots> = sum_list (map (extract_roots \<circ> snd \<circ> finite_field_factorization) (ERF' p))"
    using proots_extract_roots_factorized[OF ERF'_squarefree]
    by (intro arg_cong[where f="sum_list"] map_cong refl) (auto simp add:comp_def)
  finally show ?thesis by simp
qed

subsection \<open>Executable version of @{term "order"}\<close>

fun order_eff :: "'a mod_ring \<Rightarrow> 'a::prime_card mod_ring poly \<Rightarrow> nat" where
  "order_eff x p = count (proots_eff p) x"

lemma order_eff_code [code_unfold]: "p \<noteq> 0 \<Longrightarrow> order x p = order_eff x p"
  unfolding order_eff.simps proots_eff_correct [symmetric] count_proots
  by auto

end
