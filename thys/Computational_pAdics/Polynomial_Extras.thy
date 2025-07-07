(*  Title:       Computational p-Adics: Polynomial Extras
    Author:      Jeremy Sylvestre <jeremy.sylvestre at ualberta.ca>, 2025
    Maintainer:  Jeremy Sylvestre <jeremy.sylvestre at ualberta.ca>
*)


theory Polynomial_Extras

imports "HOL-Computational_Algebra.Polynomial"

begin


section \<open>Additional facts about polynomials\<close>


subsection \<open>General facts\<close>

lemma set_strip_while: "set (strip_while P xs) \<subseteq> set xs"
  using split_strip_while_append[of P xs] by force

lemma pCons_induct' [case_names 0 pCons0 pCons]:
  "P p"
  if  zero     : "P 0"
  and pCons0   : "\<And>a. a \<noteq> 0 \<Longrightarrow> P (pCons a 0)"
  and pCons_n0 : "\<And>a p. p \<noteq> 0 \<Longrightarrow> P p \<Longrightarrow> P (pCons a p)"
proof (induct p, rule zero)
  case (pCons a p) thus ?case by (cases "p = 0", simp_all add: pCons0 pCons_n0)
qed

lemma pCons_decomp: "pCons a p = pCons a 0 + pCons 0 p"
  by (induct p, simp_all)

lemma coeffs_smult_eq_smult_coeffs:
  "coeffs (smult x p) = map ((*) x) (strip_while (\<lambda>c. x * c = 0) (coeffs p))"
proof-
  have "coeffs (smult x p) = strip_while ((=) 0) (map ((*) x) (coeffs p))"
    by (induct p) auto
  thus ?thesis by (simp add: strip_while_map comp_def)
qed

lemma coeffs_smult_eq_smult_coeffs_no_zero_divisors:
  "coeffs (smult x p) = map ((*) x) (coeffs p)" if "x \<noteq> 0"
  for x :: "'a::{comm_semiring_0,semiring_no_zero_divisors}" and p :: "'a poly"
  using that cCons_def[of "x * _"] cCons_def[of _ "coeffs _"]
  by    (induct p, simp, fastforce)


subsection \<open>Derivatives\<close>

text \<open>
  The type sort on @{const pderiv} is overly restrictive for algebraic purposes,
  so here is the relevant material with the type sort relaxed.
\<close>

function polyderiv :: "('a :: comm_monoid_add) poly \<Rightarrow> 'a poly"
  where "polyderiv (pCons a p) = (if p = 0 then 0 else p + pCons 0 (polyderiv p))"
  by (auto intro: pCons_cases)

termination polyderiv
  by (relation "measure degree") simp_all

declare polyderiv.simps[simp del]

lemma polyderiv_0 [simp]: "polyderiv 0 = 0"
  using polyderiv.simps [of 0 0] by simp

lemma polyderiv_pCons: "polyderiv (pCons a p) = p + pCons 0 (polyderiv p)"
  by (simp add: polyderiv.simps)

lemma polyderiv_1 [simp]: "polyderiv 1 = 0"
  by (simp add: one_pCons polyderiv_pCons)


subsection \<open>Additive polynomials\<close>

text \<open>
  The Binomial Theorem implies that to every polynomial can be associated a finite list of
  polynomials that describe how the original polynomial evaluates on binomial arguments.
\<close>

function additive_poly_poly :: "'a::comm_semiring_1 poly \<Rightarrow> 'a poly poly"
  where
    "additive_poly_poly (pCons a p) =
      (if p = 0
        then [:[:a:]:]
        else smult (pCons 0 1) (additive_poly_poly p) + pCons [:a:] (additive_poly_poly p)
      )"
  by (auto intro: pCons_cases)

termination additive_poly_poly
  by (relation "measure degree") simp_all

declare additive_poly_poly.simps[simp del]

lemma additive_poly_poly_0 [simp]: "additive_poly_poly 0 = 0"
  using additive_poly_poly.simps[of 0 0] by simp

lemma additive_poly_poly_pCons0:
  "a \<noteq> 0 \<Longrightarrow> additive_poly_poly [:a:] = [:[:a:]:]"
  using additive_poly_poly.simps[of a 0] by argo

lemma additive_poly_poly_pCons:
  "p \<noteq> 0 \<Longrightarrow>
    additive_poly_poly (pCons a p) =
      smult (pCons 0 1) (additive_poly_poly p) + pCons [:a:] (additive_poly_poly p)"
  by (simp add: additive_poly_poly.simps)

lemma additive_poly_poly: "poly p (x + y) = poly (poly (additive_poly_poly p) [:x:]) y"
  by  (induct p rule: pCons_induct')
      (simp_all add: algebra_simps additive_poly_poly_pCons0 additive_poly_poly_pCons)

lemma additive_poly_poly_coeff0: "coeff (additive_poly_poly p) 0 = p"
  by  (induct p rule: pCons_induct')
      (simp_all add: additive_poly_poly_pCons0 additive_poly_poly_pCons)

lemma additive_poly_poly_coeff1: "coeff (additive_poly_poly p) 1 = polyderiv p"
  by  (induct p rule: pCons_induct')
      (simp_all add:
        ac_simps additive_poly_poly_pCons0 additive_poly_poly_pCons additive_poly_poly_coeff0
        polyderiv_pCons
      )

lemma additive_poly_poly_eq0_iff: "additive_poly_poly p = 0 \<longleftrightarrow> p = 0"
  using additive_poly_poly_coeff0[of p] by fastforce

lemma additive_poly_poly_degree: "degree (additive_poly_poly p) = degree p"
proof (induct p rule: pCons_induct')
  case (pCons a p)
  moreover have
    "degree (smult (pCons 0 1) (additive_poly_poly p)) <
      degree (pCons [:a:] (additive_poly_poly p))"
  proof (rule degree_lessI, safe)
    fix k assume "k \<ge> degree (pCons [:a:] (additive_poly_poly p))"
    with pCons(1) show "coeff (smult (pCons 0 1) (additive_poly_poly p)) k = 0"
      using additive_poly_poly_eq0_iff coeff_eq_0[of _ k] by force
  qed (simp add: pCons(1) additive_poly_poly_eq0_iff)
  ultimately show ?case
    using degree_add_eq_right additive_poly_poly_pCons degree_pCons_eq additive_poly_poly_eq0_iff
    by    metis
qed (simp, simp add: additive_poly_poly_pCons0)

lemma poly_additive_poly_poly_pCons:
  "poly (additive_poly_poly (pCons a p)) [:x:] =
    pCons a (poly (additive_poly_poly p) [:x:]) + smult x (poly (additive_poly_poly p) [:x:])"
  if "p \<noteq> 0"
  using that additive_poly_poly_pCons pCons_decomp
  by    (fastforce simp add: add.assoc[symmetric] add.commute)

lemma poly_additive_poly_poly_eq0_iff:
  "poly (additive_poly_poly p) [:x:] = 0 \<longleftrightarrow> p = 0"
proof
  show "p = 0 \<Longrightarrow> poly (additive_poly_poly p) [:x:] = 0"
    using additive_poly_poly_eq0_iff by simp
next
  show "poly (additive_poly_poly p) [:x:] = 0 \<Longrightarrow> p = 0"
  proof (induct p rule: pCons_induct')
  next
    case (pCons a p)
    moreover define poly_app_x :: "'a poly \<Rightarrow> 'a poly"
      where "poly_app_x \<equiv> \<lambda>p. poly (additive_poly_poly p) [:x:]"
    moreover from this pCons(1) have
      "coeff (poly_app_x (pCons a p)) (Suc (degree (poly_app_x p))) = lead_coeff (poly_app_x p)"
      using poly_additive_poly_poly_pCons coeff_eq_0[of "poly_app_x p"] by fastforce
    ultimately show ?case using leading_coeff_neq_0 by simp
  qed (simp, simp add: additive_poly_poly_pCons0)
qed

lemma degree_poly_additive_poly_poly:
  "degree (poly (additive_poly_poly p) [:x:]) = degree p"
proof (induct p rule: pCons_induct')
  case (pCons a p)
  define poly_app_x :: "'a poly \<Rightarrow> 'a poly"
    where "poly_app_x \<equiv> \<lambda>p. poly (additive_poly_poly p) [:x:]"
  from pCons(1) poly_app_x_def
    have  deg: "degree (pCons a (poly_app_x p)) = Suc (degree (poly_app_x p))"
    using degree_pCons_eq[of "poly_app_x p" a] poly_additive_poly_poly_eq0_iff
    by    auto
  from pCons(1) have "degree (smult x (poly_app_x p)) \<le> degree (poly_app_x p)"
    using degree_smult_le[of x "poly_app_x p"] by blast
  also have "\<dots> < Suc (degree (poly_app_x p))" by blast
  finally have "degree (smult x (poly_app_x p)) < degree (pCons a (poly_app_x p))" using deg by argo
  with pCons poly_app_x_def show ?case
    by (metis deg poly_additive_poly_poly_pCons degree_add_eq_left degree_pCons_eq)
qed (simp, simp add: additive_poly_poly_pCons0)

lemma coeff_poly_additive_poly_poly:
  "coeff (poly (additive_poly_poly p) [:x:]) n = poly (coeff (additive_poly_poly p) n) x"
proof-
  have
    "\<forall>k\<le>n.
      coeff (poly (additive_poly_poly p) [:x:]) k = poly (coeff (additive_poly_poly p) k) x"
  proof (induct p rule: pCons_induct', safe)
    fix k case (pCons0 a)
    moreover have "coeff [:a:] k = poly (coeff [:[:a:]:] k) x" by (cases k, simp_all)
    ultimately show
      "coeff (poly (additive_poly_poly [:a:]) [:x:]) k =
        poly (coeff (additive_poly_poly [:a:]) k) x"
      using additive_poly_poly_pCons0 by fastforce
  next
    case (pCons a p) fix k assume "k \<le> n" with pCons show
      "coeff (poly (additive_poly_poly (pCons a p)) [:x:]) k =
        poly (coeff (additive_poly_poly (pCons a p)) k) x"
      using poly_additive_poly_poly_pCons additive_poly_poly_pCons
        by (cases k) (fastforce, force simp add: add.commute)
  qed simp
  thus ?thesis by blast
qed

lemma additive_poly_poly_decomp:
  "poly p (x + y) = (\<Sum>i\<le>degree p. (poly (coeff (additive_poly_poly p) i) x) * y ^ i)"
  using poly_altdef[of _ y] coeff_poly_additive_poly_poly[of p x] additive_poly_poly[of p x y]
        degree_poly_additive_poly_poly[of p x]
  by    presburger


end (* theory *)
