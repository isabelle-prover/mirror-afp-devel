section \<open>Executable Code for Rabin's Irreducibility Test\<close>

theory Rabin_Irreducibility_Test_Code
  imports
    Finite_Fields_Poly_Ring_Code
    Finite_Fields_Mod_Ring_Code
    Rabin_Irreducibility_Test
begin

fun pcoprime\<^sub>C :: "('a, 'b) idx_ring_scheme \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where "pcoprime\<^sub>C R f g = (length (snd (ext_euclidean R f g)) = 1)"

declare pcoprime\<^sub>C.simps[simp del]

lemma pcoprime_c:
  assumes "field\<^sub>C R"
  assumes "f \<in> carrier (poly_ring (ring_of R))"
  assumes "g \<in> carrier (poly_ring (ring_of R))"
  shows "pcoprime\<^sub>C R f g \<longleftrightarrow> pcoprime\<^bsub>ring_of R\<^esub> f g"  (is "?L = ?R")
proof (cases "f = [] \<and> g = []")
  case True
  interpret field "ring_of R"
    using assms(1) unfolding field\<^sub>C_def by simp
  interpret d_poly_ring: domain "poly_ring (ring_of R)"
    by (rule univ_poly_is_domain[OF carrier_is_subring])

  have "?L = False" using True by (simp add: pcoprime\<^sub>C.simps ext_euclidean.simps poly_def)
  also have "... \<longleftrightarrow>  (length \<zero>\<^bsub>poly_ring (ring_of R)\<^esub> = 1)" by (simp add:univ_poly_zero)
  also have "... \<longleftrightarrow> pcoprime\<^bsub>ring_of R\<^esub> \<zero>\<^bsub>poly_ring (ring_of R)\<^esub>  []"
    by (subst pcoprime_zero_iff) (simp_all)
  also have "... \<longleftrightarrow> ?R" using True by (simp add: univ_poly_zero)
  finally show ?thesis by simp
next
  case False

  let ?P = "poly_ring (ring_of R)"
  interpret field "ring_of R"
    using assms(1) unfolding field\<^sub>C_def by simp
  interpret d_poly_ring: domain "poly_ring (ring_of R)"
    by (rule univ_poly_is_domain[OF carrier_is_subring])

  obtain s u v where suv_def: "((u,v),s) = ext_euclidean R f g" by (metis surj_pair)

  have s_eq:"s = f \<otimes>\<^bsub>?P\<^esub> u \<oplus>\<^bsub>?P\<^esub> g \<otimes>\<^bsub>?P\<^esub> v" (is "?T1")
    and s_div_f: "s pdivides\<^bsub>ring_of R\<^esub> f" and s_div_g: "s pdivides\<^bsub>ring_of R\<^esub> g" (is "?T3")
    and suv_carr: "{s, u, v} \<subseteq> carrier ?P"
    and s_nz: "s \<noteq> []"
    using False suv_def[symmetric] ext_euclidean[OF assms(1,2,3)] by auto

  have "?L \<longleftrightarrow> length s = 1" using suv_def[symmetric] by (simp add:pcoprime\<^sub>C.simps)
  also have "... \<longleftrightarrow> ?R"
    unfolding pcoprime_def
  proof (intro iffI impI ballI)
    fix r assume len_s: "length s = 1"
    assume r_carr:"r \<in> carrier ?P"
      and "r pdivides\<^bsub>ring_of R\<^esub> f \<and> r pdivides\<^bsub>ring_of R\<^esub> g"
    hence r_div: "pmod f r = \<zero>\<^bsub>?P\<^esub>"  "pmod g r = \<zero>\<^bsub>?P\<^esub>" unfolding univ_poly_zero
      using assms(2,3) pmod_zero_iff_pdivides[OF carrier_is_subfield] by auto

    have "pmod s r = pmod (f \<otimes>\<^bsub>?P\<^esub> u) r \<oplus>\<^bsub>?P\<^esub> pmod (g \<otimes>\<^bsub>?P\<^esub> v) r"
      using r_carr suv_carr assms unfolding s_eq
      by (intro long_division_add[OF carrier_is_subfield]) auto
    also have "... = pmod (pmod f r \<otimes>\<^bsub>?P\<^esub> u) r  \<oplus>\<^bsub>?P\<^esub> pmod (pmod g r \<otimes>\<^bsub>?P\<^esub> v) r"
      using r_carr suv_carr assms by (intro arg_cong2[where f="(\<oplus>\<^bsub>?P\<^esub>)"] pmod_mult_left) auto
    also have "... = pmod \<zero>\<^bsub>?P\<^esub> r  \<oplus>\<^bsub>?P\<^esub> pmod \<zero>\<^bsub>?P\<^esub> r"
      using suv_carr unfolding r_div by simp
    also have "... = []" using r_carr unfolding univ_poly_zero
      by (simp add: long_division_zero[OF carrier_is_subfield] univ_poly_add)
    finally have "pmod s r =  []" by simp
    hence "r pdivides\<^bsub>ring_of R\<^esub> s"
      using r_carr suv_carr pmod_zero_iff_pdivides[OF carrier_is_subfield] by auto
    hence "degree r \<le> degree s"
      using s_nz r_carr suv_carr by (intro pdivides_imp_degree_le[OF carrier_is_subring]) auto
    thus "degree r = 0" using len_s by simp
  next
    assume "\<forall>r\<in>carrier ?P. r pdivides\<^bsub>ring_of R\<^esub> f \<and> r pdivides\<^bsub>ring_of R\<^esub> g \<longrightarrow> degree r = 0"
    hence "degree s = 0" using s_div_f s_div_g suv_carr by simp
    thus "length s =1" using s_nz
      by (metis diff_is_0_eq diffs0_imp_equal length_0_conv less_one linorder_le_less_linear)
  qed
  finally show ?thesis by simp
qed

text \<open>The following is a fast version of @{term "pmod"} for polynomials (to a high power) that
need to be reduced, this is used for the higher order term of the Gauss polynomial.\<close>

fun pmod_pow\<^sub>C :: "('a,'b) idx_ring_scheme \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "pmod_pow\<^sub>C F f n g = (
    let r = (if n \<ge> 2 then pmod_pow\<^sub>C F f (n div 2) g ^\<^sub>C\<^bsub>poly F\<^esub> 2 else 1\<^sub>C\<^bsub>poly F\<^esub>)
    in pmod\<^sub>C F (r *\<^sub>C\<^bsub>poly F\<^esub> (f ^\<^sub>C\<^bsub>poly F\<^esub> (n mod 2))) g)"

declare pmod_pow\<^sub>C.simps[simp del]

lemma pmod_pow_c:
  assumes "field\<^sub>C R"
  assumes "f \<in> carrier (poly_ring (ring_of R))"
  assumes "g \<in> carrier (poly_ring (ring_of R))"
  shows "pmod_pow\<^sub>C R f n g = ring.pmod (ring_of R) (f [^]\<^bsub>poly_ring (ring_of R)\<^esub> n) g"
proof (induction n rule:nat_less_induct)
  case (1 n)

  let ?P = "poly_ring (ring_of R)"
  interpret field "ring_of R"
    using assms(1) unfolding field\<^sub>C_def by simp
  interpret d_poly_ring: domain "poly_ring (ring_of R)"
    by (rule univ_poly_is_domain[OF carrier_is_subring])

  have ring_c: "ring\<^sub>C R" using assms(1) unfolding field\<^sub>C_def domain\<^sub>C_def cring\<^sub>C_def by auto
  have d_poly: "domain\<^sub>C (poly R)" using assms (1) unfolding field\<^sub>C_def by (intro poly_domain) auto

  have ind: "pmod_pow\<^sub>C R f m g = pmod (f [^]\<^bsub>?P\<^esub> m) g" if "m < n" for m
    using 1 that by auto

  define r where "r = (if n \<ge> 2 then pmod_pow\<^sub>C R f (n div 2) g ^\<^sub>C\<^bsub>poly R\<^esub> 2 else 1\<^sub>C\<^bsub>poly R\<^esub>)"

  have "pmod r g = pmod (f [^]\<^bsub>?P\<^esub> (n - (n mod 2))) g \<and> r \<in> carrier ?P"
  proof (cases "n \<ge> 2")
    case True
    hence "r = pmod_pow\<^sub>C R f (n div 2) g [^]\<^bsub>?P\<^esub> (2 :: nat)"
      unfolding r_def domain_cD[OF d_poly] by (simp add:ring_of_poly[OF ring_c])
    also have "... = pmod (f [^]\<^bsub>?P\<^esub> (n div 2)) g [^]\<^bsub>?P\<^esub> (2 :: nat)"
      using True by (intro arg_cong2[where f="([^]\<^bsub>?P\<^esub>)"] refl ind) auto
    finally have r_alt: "r = pmod (f [^]\<^bsub>?P\<^esub> (n div 2)) g [^]\<^bsub>?P\<^esub> (2 :: nat)"
      by simp

    have "pmod r g = pmod (pmod (f [^]\<^bsub>?P\<^esub> (n div 2)) g \<otimes>\<^bsub>?P\<^esub> pmod (f [^]\<^bsub>?P\<^esub> (n div 2)) g) g"
      unfolding r_alt using assms(2,3) long_division_closed[OF carrier_is_subfield]
      by (simp add:numeral_eq_Suc) algebra
    also have "... = pmod (f [^]\<^bsub>?P\<^esub> (n div 2) \<otimes>\<^bsub>?P\<^esub> f [^]\<^bsub>?P\<^esub> (n div 2)) g"
      using assms(2,3) by (intro pmod_mult_both[symmetric]) auto
    also have "... = pmod (f [^]\<^bsub>?P\<^esub> ((n div 2)+(n div 2))) g"
      using assms(2,3) by (subst d_poly_ring.nat_pow_mult) auto
    also have "... = pmod (f [^]\<^bsub>?P\<^esub> (n - (n mod 2))) g"
      by (intro arg_cong2[where f="pmod"] refl arg_cong2[where f="([^]\<^bsub>?P\<^esub>)"]) presburger
    finally have "pmod r g = pmod (f [^]\<^bsub>?P\<^esub> (n - (n mod 2))) g"
      by simp
    moreover have "r \<in> carrier ?P"
      using assms(2,3) long_division_closed[OF carrier_is_subfield] unfolding r_alt by auto
    ultimately show ?thesis by auto
  next
    case False
    hence "r = \<one>\<^bsub>?P\<^esub>"
      unfolding r_def using domain_cD[OF d_poly] ring_of_poly[OF ring_c] by simp
    also have "... = f [^]\<^bsub>?P\<^esub> (0 :: nat)" by simp
    also have "... = f [^]\<^bsub>?P\<^esub> (n - (n mod 2))"
      using False by (intro arg_cong2[where f="([^]\<^bsub>?P\<^esub>)"] refl) auto
    finally have "r = f [^]\<^bsub>?P\<^esub> (n - (n mod 2))" by simp
    then show ?thesis using assms(2) by simp
  qed

  hence r_exp: "pmod r g = pmod (f [^]\<^bsub>?P\<^esub> (n - (n mod 2))) g" and r_carr: "r \<in> carrier ?P"
    by auto

  have "pmod_pow\<^sub>C R f n g = pmod\<^sub>C R (r *\<^sub>C\<^bsub>poly R\<^esub> (f ^\<^sub>C\<^bsub>poly R\<^esub> (n mod 2))) g"
    by (subst pmod_pow\<^sub>C.simps) (simp add:r_def[symmetric])
  also have "... = pmod\<^sub>C R (r \<otimes>\<^bsub>?P\<^esub> (f [^]\<^bsub>?P\<^esub> (n mod 2))) g"
    unfolding domain_cD[OF d_poly] by (simp add:ring_of_poly[OF ring_c])
  also have "... = pmod (r \<otimes>\<^bsub>?P\<^esub> (f [^]\<^bsub>?P\<^esub> (n mod 2))) g"
    using r_carr assms(2,3) by (intro pmod_c[OF assms(1)]) auto
  also have "... = pmod (pmod r g \<otimes>\<^bsub>?P\<^esub> (f [^]\<^bsub>?P\<^esub> (n mod 2))) g"
    using r_carr assms(2,3) by (intro pmod_mult_left) auto
  also have "... = pmod (f [^]\<^bsub>?P\<^esub> (n - (n mod 2)) \<otimes>\<^bsub>?P\<^esub> (f [^]\<^bsub>?P\<^esub> (n mod 2))) g"
    using assms(2,3) unfolding r_exp by (intro pmod_mult_left[symmetric]) auto
  also have "... = pmod (f [^]\<^bsub>?P\<^esub> ((n - (n mod 2)) + (n mod 2))) g"
    using assms(2,3) by (intro arg_cong2[where f="pmod"] refl d_poly_ring.nat_pow_mult) auto
  also have "... = pmod (f [^]\<^bsub>?P\<^esub> n) g" by simp
  finally show "pmod_pow\<^sub>C R f n g = pmod (f [^]\<^bsub>?P\<^esub> n) g" by simp
qed

text \<open>The following function checks whether a given polynomial is coprime with the
Gauss polynomial $X^n - X$.\<close>

definition pcoprime_with_gauss_poly :: "('a,'b) idx_ring_scheme \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool"
  where "pcoprime_with_gauss_poly F p n =
    (pcoprime\<^sub>C F p (pmod_pow\<^sub>C F X\<^sub>C\<^bsub>F\<^esub> n p +\<^sub>C\<^bsub>poly F\<^esub> (-\<^sub>C\<^bsub>poly F\<^esub> pmod\<^sub>C F X\<^sub>C\<^bsub>F\<^esub> p)))"


definition divides_gauss_poly :: "('a,'b) idx_ring_scheme \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool"
  where "divides_gauss_poly F p n =
    (pmod_pow\<^sub>C F X\<^sub>C\<^bsub>F\<^esub> n p +\<^sub>C\<^bsub>poly F\<^esub> (-\<^sub>C\<^bsub>poly F\<^esub> pmod\<^sub>C F X\<^sub>C\<^bsub>F\<^esub> p) = [])"

lemma mod_gauss_poly:
  assumes "field\<^sub>C R"
  assumes "f \<in> carrier (poly_ring (ring_of R))"
  shows "pmod_pow\<^sub>C R X\<^sub>C\<^bsub>R\<^esub> n f +\<^sub>C\<^bsub>poly R\<^esub> (-\<^sub>C\<^bsub>poly R\<^esub> pmod\<^sub>C R X\<^sub>C\<^bsub>R\<^esub> f) =
    ring.pmod (ring_of R) (gauss_poly (ring_of R) n) f" (is "?L = ?R")
proof -
  interpret field "ring_of R"
    using assms(1) unfolding field\<^sub>C_def by simp
  interpret d_poly_ring: domain "poly_ring (ring_of R)"
    by (rule univ_poly_is_domain[OF carrier_is_subring])

  have ring_c: "ring\<^sub>C R" using assms(1) unfolding field\<^sub>C_def domain\<^sub>C_def cring\<^sub>C_def by auto
  have d_poly: "domain\<^sub>C (poly R)" using assms (1) unfolding field\<^sub>C_def by (intro poly_domain) auto
  let ?P = "poly_ring (ring_of R)"

  have "?L = pmod_pow\<^sub>C R X\<^bsub>ring_of R\<^esub> n f \<oplus>\<^bsub>?P\<^esub> -\<^sub>C\<^bsub>poly R\<^esub> pmod\<^sub>C R X\<^bsub>ring_of R\<^esub> f"
    by (simp add: poly_var domain_cD[OF d_poly] ring_of_poly[OF ring_c])
  also have "...= pmod (X\<^bsub>ring_of R\<^esub>[^]\<^bsub>?P\<^esub> n) f\<oplus>\<^bsub>?P\<^esub> -\<^sub>C\<^bsub>poly R\<^esub> pmod X\<^bsub>ring_of R\<^esub> f"
    using assms var_carr[OF carrier_is_subring] by (intro refl arg_cong2[where f="(\<oplus>\<^bsub>?P\<^esub>)"]
        pmod_pow_c arg_cong[where f="\<lambda>x. (-\<^sub>C\<^bsub>poly R\<^esub> x)"] pmod_c) auto
  also have "... =pmod (X\<^bsub>ring_of R\<^esub>[^]\<^bsub>?P\<^esub> n) f\<ominus>\<^bsub>?P\<^esub> pmod X\<^bsub>ring_of R\<^esub> f"
    unfolding a_minus_def using assms(1,2) var_carr[OF carrier_is_subring]
      ring_of_poly[OF ring_c] long_division_closed[OF carrier_is_subfield]
    by (subst domain_cD[OF d_poly]) auto
  also have "... = pmod (X\<^bsub>ring_of R\<^esub>[^]\<^bsub>?P\<^esub> n) f \<oplus>\<^bsub>?P\<^esub> pmod (\<ominus>\<^bsub>?P\<^esub> X\<^bsub>ring_of R\<^esub>) f"
    using assms(2) var_carr[OF carrier_is_subring]
    unfolding a_minus_def by (subst long_division_a_inv[OF carrier_is_subfield]) auto
  also have " ... = pmod (gauss_poly (ring_of R) n) f"
    using assms(2) var_carr[OF carrier_is_subring] var_pow_carr[OF carrier_is_subring]
    unfolding gauss_poly_def a_minus_def by (subst long_division_add[OF carrier_is_subfield]) auto
  finally show ?thesis by simp
qed

lemma pcoprime_with_gauss_poly:
  assumes "field\<^sub>C R"
  assumes "f \<in> carrier (poly_ring (ring_of R))"
  shows "pcoprime_with_gauss_poly R f n \<longleftrightarrow> pcoprime\<^bsub>ring_of R\<^esub> (gauss_poly (ring_of R) n) f"
    (is "?L = ?R")
proof -
  interpret field "ring_of R"
    using assms(1) unfolding field\<^sub>C_def by simp

  have "?L \<longleftrightarrow> pcoprime\<^sub>C R f (pmod (gauss_poly (ring_of R) n) f)"
    unfolding pcoprime_with_gauss_poly_def using assms by (subst mod_gauss_poly) auto
  also have "... = pcoprime\<^bsub>ring_of R\<^esub> f (pmod (gauss_poly (ring_of R) n) f)"
    using assms gauss_poly_carr long_division_closed[OF carrier_is_subfield]
    by (intro pcoprime_c) auto
  also have "... = pcoprime\<^bsub>ring_of R\<^esub> (gauss_poly (ring_of R) n) f"
    by (intro pcoprime_step[symmetric] gauss_poly_carr assms)
  finally show ?thesis by simp
qed

lemma divides_gauss_poly:
  assumes "field\<^sub>C R"
  assumes "f \<in> carrier (poly_ring (ring_of R))"
  shows "divides_gauss_poly R f n \<longleftrightarrow> f pdivides\<^bsub>ring_of R\<^esub> (gauss_poly (ring_of R) n)"
    (is "?L = ?R")
proof -
  interpret field "ring_of R"
    using assms(1) unfolding field\<^sub>C_def by simp
  have "?L \<longleftrightarrow> (pmod (gauss_poly (ring_of R) n) f = [])"
    unfolding divides_gauss_poly_def using assms by (subst mod_gauss_poly) auto
  also have "... \<longleftrightarrow> ?R"
    using assms gauss_poly_carr by (intro pmod_zero_iff_pdivides[OF carrier_is_subfield]) auto
  finally show ?thesis
    by simp
qed


fun rabin_test_powers :: "('a, 'b) idx_ring_enum_scheme \<Rightarrow> nat \<Rightarrow> nat list"
  where "rabin_test_powers F n =
    map (\<lambda>p. idx_size F^(n div p)) (filter (\<lambda>p. prime p \<and> p dvd n) [2..<(n+1)] )"

text \<open>Given a monic polynomial with coefficients over a finite field returns true, if it is
irreducible\<close>

fun rabin_test :: "('a, 'b) idx_ring_enum_scheme \<Rightarrow> 'a list \<Rightarrow> bool"
  where "rabin_test F f = (
    if degree f = 0 then
      False
    else (if \<not>divides_gauss_poly F f (idx_size F^degree f) then
      False
    else (list_all (pcoprime_with_gauss_poly F f) (rabin_test_powers F (degree f)))))"

declare rabin_test.simps[simp del]

context
  fixes R
  assumes field_R: "field\<^sub>C R"
  assumes enum_R: "enum\<^sub>C R"
begin

interpretation finite_field "(ring_of R)"
  using field_R enum_cD[OF enum_R] unfolding field\<^sub>C_def
  by (simp add:finite_field_def finite_field_axioms_def)

lemma rabin_test_powers:
  assumes "n > 0"
  shows "set (rabin_test_powers R n) =
    {order (ring_of R)^ (n div p) | p . Factorial_Ring.prime p \<and> p dvd n}"
    (is "?L = ?R")
proof -
  let ?f = "(\<lambda>x. order (ring_of R) ^ (n div x))"

  have 0:"p \<in> {2..n}" if "Factorial_Ring.prime p" "p dvd n"  for p
    using assms that by (simp add: dvd_imp_le prime_ge_2_nat)

  have "?L = ?f ` {p \<in> {2..n}.  Factorial_Ring.prime p \<and> p dvd n}"
    using enum_cD[OF enum_R] by auto
  also have "... = ?f ` {p.  Factorial_Ring.prime p \<and> p dvd n}"
    using 0 by (intro image_cong Collect_cong) auto
  also have "... = ?R"
    by auto
  finally show ?thesis by simp
qed

lemma rabin_test:
  assumes "monic_poly (ring_of R) f"
  shows "rabin_test R f \<longleftrightarrow> monic_irreducible_poly (ring_of R) f" (is "?L = ?R")
proof (cases "degree f = 0")
  case True
  thus ?thesis unfolding rabin_test.simps using monic_poly_min_degree by fastforce
next
  case False
  define N where "N = {degree f div p | p . Factorial_Ring.prime p \<and> p dvd degree f}"

  have f_carr: "f \<in> carrier (poly_ring (ring_of R))"
    using assms(1) unfolding monic_poly_def by auto

  have deg_f_gt_0: "degree f > 0"
    using False by auto
  have rt_powers: "set (rabin_test_powers R (degree f)) = (\<lambda>x. order (ring_of R)^x) ` N"
    unfolding rabin_test_powers[OF deg_f_gt_0] N_def by auto

  have "?L \<longleftrightarrow> divides_gauss_poly R f (idx_size R ^ degree f) \<and>
    (\<forall>n \<in> set (rabin_test_powers R (degree f)). (pcoprime_with_gauss_poly R f n))"
    using False by (simp add: list_all_def rabin_test.simps del:rabin_test_powers.simps)
  also have "... \<longleftrightarrow> f pdivides\<^bsub>ring_of R\<^esub> (gauss_poly (ring_of R) (order (ring_of R) ^ degree f))
    \<and> (\<forall>n \<in> N. pcoprime\<^bsub>ring_of R\<^esub> (gauss_poly (ring_of R) (order (ring_of R) ^n)) f)"
    unfolding divides_gauss_poly[OF field_R f_carr] pcoprime_with_gauss_poly[OF field_R f_carr]
      rt_powers enum_cD[OF enum_R] by simp
  also have "... \<longleftrightarrow> ?R"
    using False unfolding N_def by (intro rabin_irreducibility_condition[symmetric] assms(1)) auto
  finally show ?thesis by simp
qed

end

end