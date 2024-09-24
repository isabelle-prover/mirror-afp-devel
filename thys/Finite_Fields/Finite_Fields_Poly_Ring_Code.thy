section \<open>Executable Polynomial Rings\<close>

theory Finite_Fields_Poly_Ring_Code
  imports
    Finite_Fields_Indexed_Algebra_Code
    "HOL-Algebra.Polynomials"
    Finite_Fields.Card_Irreducible_Polynomials_Aux
begin

fun o_normalize :: "('a,'b) idx_ring_scheme \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
    "o_normalize E [] = []"
  | "o_normalize E p = (if lead_coeff p \<noteq> 0\<^sub>C\<^bsub>E\<^esub> then p else o_normalize E (tl p))"

fun o_poly_add :: "('a,'b) idx_ring_scheme \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "o_poly_add E p1 p2 = (
    if length p1 \<ge> length p2
      then o_normalize E (map2 (idx_plus E) p1 ((replicate (length p1 - length p2) 0\<^sub>C\<^bsub>E\<^esub> ) @ p2))
      else o_poly_add E p2 p1)"

fun o_poly_mult :: "('a,'b) idx_ring_scheme \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
    "o_poly_mult E [] p2 = []"
  | "o_poly_mult E p1 p2 =
       o_poly_add E ((map (idx_mult E (hd p1)) p2) @
      (replicate (degree p1) 0\<^sub>C\<^bsub>E\<^esub> )) (o_poly_mult E (tl p1) p2)"

definition poly :: "('a,'b) idx_ring_scheme \<Rightarrow> 'a list idx_ring"
  where "poly E = \<lparr>
    idx_pred = (\<lambda>x. (x = [] \<or> hd x \<noteq> 0\<^sub>C\<^bsub>E\<^esub>) \<and> list_all (idx_pred E) x),
    idx_uminus = (\<lambda>x. map (idx_uminus E) x),
    idx_plus = o_poly_add E,
    idx_udivide = (\<lambda>x. [idx_udivide E (hd x)]),
    idx_mult = o_poly_mult E,
    idx_zero = [],
    idx_one = [idx_one E] \<rparr>"

definition poly_var :: "('a,'b) idx_ring_scheme \<Rightarrow> 'a list"  (\<open>X\<^sub>C\<index>\<close>)
  where "poly_var E = [idx_one E, idx_zero E]"

lemma poly_var: "poly_var R = X\<^bsub>ring_of R\<^esub>"
  unfolding var_def poly_var_def by (simp add:ring_of_def)

fun poly_eval :: "('a,'b) idx_ring_scheme \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a"
  where "poly_eval R fs x = fold (\<lambda>a b. b *\<^sub>C\<^bsub>R\<^esub> x +\<^sub>C\<^bsub>R\<^esub> a) fs 0\<^sub>C\<^bsub>R\<^esub>"



lemma ring_of_poly:
  assumes "ring\<^sub>C A"
  shows "ring_of (poly A) = poly_ring (ring_of A)"
proof (intro ring.equality)
  interpret ring "ring_of A" using assms unfolding ring\<^sub>C_def by auto

  have b: "\<zero>\<^bsub>ring_of A\<^esub> = 0\<^sub>C\<^bsub>A\<^esub>" unfolding ring_of_def by simp
  have c: "(\<otimes>\<^bsub>ring_of A\<^esub>) = (*\<^sub>C\<^bsub>A\<^esub>)" unfolding ring_of_def by simp
  have d: "(\<oplus>\<^bsub>ring_of A\<^esub>) = (+\<^sub>C\<^bsub>A\<^esub>)" unfolding ring_of_def by simp

  have " o_normalize A  x = normalize x" for x
    using b by (induction x) simp_all

  hence "o_poly_add A x y = poly_add x y" if "length y \<le> length x" for x y
    using that by (subst o_poly_add.simps, subst poly_add.simps) (simp add: b d)
  hence a:"o_poly_add A x y = poly_add x y" for x y
    by (subst o_poly_add.simps, subst poly_add.simps) simp

  hence "x \<oplus>\<^bsub>ring_of (poly A)\<^esub> y = x \<oplus>\<^bsub>poly_ring (ring_of A)\<^esub> y" for x y
    by (simp add:univ_poly_def poly_def ring_of_def)

  thus "(\<oplus>\<^bsub>ring_of (poly A)\<^esub>) = (\<oplus>\<^bsub>poly_ring (ring_of A)\<^esub>)" by (intro ext)

  show "carrier (ring_of (poly A)) = carrier (poly_ring (ring_of A))"
    by (auto simp add: ring_of_def poly_def univ_poly_def polynomial_def list_all_iff)

  have "o_poly_mult A x y = poly_mult x y" for x y
  proof (induction x)
    case Nil then show ?case by simp
  next
    case (Cons a x) then show ?case
      by (subst o_poly_mult.simps,subst poly_mult.simps)
        (simp add:a b c del:poly_add.simps o_poly_add.simps)
  qed
  hence "x \<otimes>\<^bsub>ring_of (poly A)\<^esub> y = x \<otimes>\<^bsub>poly_ring (ring_of A)\<^esub> y" for x y
    by (simp add:  univ_poly_def poly_def ring_of_def)
  thus "(\<otimes>\<^bsub>ring_of (poly A)\<^esub>) = (\<otimes>\<^bsub>poly_ring (ring_of A)\<^esub>)" by (intro ext)

qed (simp_all add:ring_of_def poly_def univ_poly_def)

lemma poly_eval:
  assumes "ring\<^sub>C R"
  assumes fsc:"fs \<in> carrier (ring_of (poly R))" and xc:"x \<in> carrier (ring_of R)"
  shows "poly_eval R fs x = ring.eval (ring_of R) fs x"
proof -
  interpret ring "ring_of R" using assms unfolding ring\<^sub>C_def by auto

  have fs_carr:"fs \<in> carrier (poly_ring (ring_of R))" using ring_of_poly[OF assms(1)] fsc by auto
  hence "set fs \<subseteq> carrier (ring_of R)" by (simp add: polynomial_incl univ_poly_carrier)
  thus ?thesis
  proof (induction rule:rev_induct)
    case Nil thus ?case by simp (simp add:ring_of_def)
  next
    case (snoc ft fh)
    have "poly_eval R (fh @ [ft]) x = poly_eval R fh x *\<^sub>C\<^bsub>R\<^esub> x +\<^sub>C\<^bsub>R\<^esub> ft" by simp
    also have "... = eval fh x *\<^sub>C\<^bsub>R\<^esub> x +\<^sub>C\<^bsub>R\<^esub> ft" using snoc by (subst snoc) auto
    also have "... = eval fh x \<otimes>\<^bsub>ring_of R\<^esub> x \<oplus>\<^bsub>ring_of R\<^esub> ft " by (simp add:ring_of_def)
    also have " ... = eval (fh@[ft]) x" using snoc by (intro eval_append_aux[symmetric] xc) auto
    finally show ?case by auto
  qed
qed

lemma poly_domain:
  assumes "domain\<^sub>C A"
  shows "domain\<^sub>C (poly A)"
proof -
  interpret domain "ring_of A" using assms unfolding domain\<^sub>C_def by auto

  have a:"\<ominus>\<^bsub>ring_of A\<^esub> x = -\<^sub>C\<^bsub>A\<^esub> x" if "x \<in> carrier (ring_of A)" for x
    using that by (intro domain_cD[symmetric] assms)
  have "ring\<^sub>C A"
    using assms unfolding domain\<^sub>C_def cring\<^sub>C_def by auto
  hence b:"ring_of (poly A) = poly_ring (ring_of A)"
    by (subst ring_of_poly) auto

  have c:"domain (ring_of (poly A))"
    unfolding b by (rule univ_poly_is_domain[OF carrier_is_subring])

  interpret d: domain "poly_ring (ring_of A)"
    using c unfolding b by simp

  have "-\<^sub>C\<^bsub>poly A\<^esub> x = \<ominus>\<^bsub>ring_of (poly A)\<^esub> x" if "x \<in> carrier (ring_of (poly A))" for x
  proof -
    have "\<ominus>\<^bsub>ring_of (poly A)\<^esub> x =  map (a_inv (ring_of A)) x"
      using that unfolding b by (subst univ_poly_a_inv_def'[OF carrier_is_subring]) auto
    also have "... = map (\<lambda>r. -\<^sub>C\<^bsub>A\<^esub> r) x"
      using that  unfolding b univ_poly_carrier[symmetric] polynomial_def
      by (intro map_cong refl a) auto
    also have "... = -\<^sub>C\<^bsub>poly A\<^esub> x"
      unfolding poly_def by simp
    finally show ?thesis by simp
  qed
  moreover have "x \<inverse>\<^sub>C\<^bsub>poly A\<^esub> = inv\<^bsub>ring_of (poly A)\<^esub> x" if "x \<in> Units (ring_of (poly A))" for x
  proof -
    have "x \<in> {[k] |k. k \<in> carrier (ring_of A) - {\<zero>\<^bsub>ring_of A\<^esub>}}"
      using that univ_poly_carrier_units_incl unfolding b by auto
    then obtain k where x_eq: "k \<in> carrier (ring_of A) - {\<zero>\<^bsub>ring_of A\<^esub>}" "x = [k]" by auto
    have "inv\<^bsub>ring_of (poly A)\<^esub> x \<in> Units (poly_ring (ring_of A))"
      using that unfolding b by simp
    hence "inv\<^bsub>ring_of (poly A)\<^esub> x \<in> {[k] |k. k \<in> carrier (ring_of A) - {\<zero>\<^bsub>ring_of A\<^esub>}}"
      using that univ_poly_carrier_units_incl unfolding b by auto
    then obtain v where x_inv_eq: "v\<in> carrier (ring_of A) - {\<zero>\<^bsub>ring_of A\<^esub>}"
      "inv\<^bsub>ring_of (poly A)\<^esub> x = [v]" by auto

    have "poly_mult [k] [v] = [k] \<otimes>\<^bsub>ring_of (poly A)\<^esub> [v]" unfolding b univ_poly_mult by simp
    also have "... = x \<otimes>\<^bsub>ring_of (poly A)\<^esub> inv\<^bsub>ring_of (poly A)\<^esub> x" using x_inv_eq x_eq by auto
    also have "... = \<one>\<^bsub>ring_of (poly A)\<^esub>" using that unfolding b by simp
    also have "... = [\<one>\<^bsub>ring_of A\<^esub>]" unfolding b univ_poly_one by (simp add:ring_of_def)
    finally have "poly_mult [k] [v] = [\<one>\<^bsub>ring_of A\<^esub>]" by simp
    hence "k \<otimes>\<^bsub>ring_of A\<^esub> v \<oplus>\<^bsub>ring_of A\<^esub> \<zero>\<^bsub>ring_of A\<^esub> =  \<one>\<^bsub>ring_of A\<^esub>"
      by (simp add:if_distribR if_distrib) (simp cong:if_cong, metis)
    hence e: "k \<otimes>\<^bsub>ring_of A\<^esub> v = \<one>\<^bsub>ring_of A\<^esub>" using x_eq(1) x_inv_eq(1) by simp
    hence f: "v \<otimes>\<^bsub>ring_of A\<^esub> k = \<one>\<^bsub>ring_of A\<^esub>" using x_eq(1) x_inv_eq(1) m_comm by simp
    have g: "v = inv\<^bsub>ring_of A\<^esub> k"
      using e x_eq(1) x_inv_eq(1) by (intro comm_inv_char[symmetric]) auto
    hence h: "k \<in> Units (ring_of A)" unfolding Units_def using e f x_eq(1) x_inv_eq(1) by blast

    have "x \<inverse>\<^sub>C\<^bsub>poly A\<^esub> = [k] \<inverse>\<^sub>C\<^bsub>poly A\<^esub>" unfolding x_eq by simp
    also have "... = [k \<inverse>\<^sub>C\<^bsub>A\<^esub>]" unfolding poly_def by simp
    also have "... = [v]"
      unfolding g by (intro domain_cD[OF assms(1)] arg_cong2[where f="(#)"] h refl)
    also have "... = inv\<^bsub>ring_of (poly A)\<^esub> x" unfolding x_inv_eq by simp
    finally show ?thesis by simp
  qed
  ultimately show ?thesis using c by (intro domain_cI)
qed

function long_division\<^sub>C :: "('a,'b) idx_ring_scheme \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list"
  where "long_division\<^sub>C F f g = (
    if (length g = 0 \<or> length f < length g)
      then ([], f)
      else (
        let k = length f - length g;
            \<alpha> = -\<^sub>C\<^bsub>F\<^esub> (hd f *\<^sub>C\<^bsub>F\<^esub>  (hd g) \<inverse>\<^sub>C\<^bsub>F\<^esub>);
            h = [\<alpha>] *\<^sub>C\<^bsub>poly F\<^esub> X\<^sub>C\<^bsub>F\<^esub> ^\<^sub>C\<^bsub>poly F\<^esub> k;
            f' = f +\<^sub>C\<^bsub>poly F\<^esub> (h *\<^sub>C\<^bsub>poly F\<^esub> g);
            f'' = take (length f - 1) f'
        in apfst (\<lambda>x. x +\<^sub>C\<^bsub>poly F\<^esub> -\<^sub>C\<^bsub>poly F\<^esub> h) (long_division\<^sub>C F f'' g)))"
  by pat_completeness auto

lemma pmod_termination_helper:
  "g \<noteq> [] \<Longrightarrow> \<not>length f < length g \<Longrightarrow> min x (length f - 1) < length f"
  by (metis diff_less length_greater_0_conv list.size(3) min.strict_coboundedI2 zero_less_one)

termination by (relation "measure (\<lambda>(_, f, _). length f)") (use pmod_termination_helper in auto)

declare long_division\<^sub>C.simps[simp del]

lemma long_division_c_length:
  assumes "length g > 0"
  shows "length (snd (long_division\<^sub>C R f g)) < length g"
proof (induction "length f" arbitrary:f rule:nat_less_induct)
  case 1
  have 0:"length (snd (long_division\<^sub>C R x g)) < length g"
    if "length x < length f" for x using 1 that by blast

  show "length (snd (long_division\<^sub>C R f g)) < length g"
  proof (cases "length f < length g")
    case True then show ?thesis by (subst long_division\<^sub>C.simps) simp
  next
    case False
    hence "length f > 0" using assms by auto
    thus ?thesis using assms by (subst long_division\<^sub>C.simps)
       (auto intro!:0 simp: min.commute min.strict_coboundedI1 Let_def)
  qed
qed


context field
begin

interpretation r:polynomial_ring R "(carrier R)"
    unfolding polynomial_ring_def polynomial_ring_axioms_def
    using carrier_is_subfield field_axioms by force

lemma poly_length_from_coeff:
  assumes "p \<in> carrier (poly_ring R)"
  assumes "\<And>i. i \<ge> k \<Longrightarrow> coeff p i = \<zero>"
  shows "length p \<le> k"
proof (rule ccontr)
  assume a:"\<not>length p \<le> k"
  hence p_nz: "p \<noteq> []" by auto
  have "k < length p" using a by simp
  hence "k \<le> length p - 1" by simp
  hence "\<zero> = coeff p (degree p)" by (intro assms(2)[symmetric])
  also have "... = lead_coeff p" by (intro lead_coeff_simp[OF p_nz])
  finally have "\<zero> = lead_coeff p" by simp
  thus "False"
    using p_nz assms(1) unfolding univ_poly_def polynomial_def by simp
qed

lemma  poly_add_cancel_len:
  assumes "f \<in> carrier (poly_ring R) - {\<zero>\<^bsub>poly_ring R\<^esub>}"
  assumes "g \<in> carrier (poly_ring R) - {\<zero>\<^bsub>poly_ring R\<^esub>}"
  assumes "hd f = \<ominus> hd g" "degree f = degree g"
  shows "length (f \<oplus>\<^bsub>poly_ring R\<^esub> g) < length f"
proof -
  have f_ne: "f \<noteq> []" using assms(1) unfolding univ_poly_zero by simp
  have g_ne: "g \<noteq> []" using assms(2) unfolding univ_poly_zero by simp

  have "coeff f i = \<ominus>coeff g i" if "i \<ge> degree f" for i
  proof (cases "i = degree f")
    case True
    have "coeff f i = hd f" unfolding True by (subst lead_coeff_simp[OF f_ne]) simp
    also have "... = \<ominus>hd g" using assms(3) by simp
    also have "... = \<ominus>coeff g i" unfolding True assms(4) by (subst lead_coeff_simp[OF g_ne]) simp
    finally show ?thesis by simp
  next
    case False
    hence "i > degree f" "i > degree g" using  assms(4) that by auto
    thus "coeff f i = \<ominus> coeff g i" using coeff_degree by simp
  qed
  hence "coeff (f \<oplus>\<^bsub>poly_ring R\<^esub> g) i = \<zero>" if "i \<ge> degree f" for i
    using assms(1,2) that by (subst r.coeff_add) (auto intro:l_neg simp:  r.coeff_range)

  hence "length (f \<oplus>\<^bsub>poly_ring R\<^esub> g) \<le> length f - 1"
    using assms(1,2) by (intro poly_length_from_coeff) auto
  also have "... < length f" using f_ne by simp
  finally show ?thesis by simp
qed

lemma pmod_mult_left:
  assumes "f \<in> carrier (poly_ring R)"
  assumes "g \<in> carrier (poly_ring R)"
  assumes "h \<in> carrier (poly_ring R)"
  shows "(f \<otimes>\<^bsub>poly_ring R\<^esub> g) pmod h = ((f pmod h) \<otimes>\<^bsub>poly_ring R\<^esub> g) pmod h" (is "?L = ?R")
proof -
  have "h pdivides (h \<otimes>\<^bsub>poly_ring R\<^esub> (f pdiv h)) \<otimes>\<^bsub>poly_ring R\<^esub> g"
    using assms long_division_closed[OF carrier_is_subfield]
    by (simp add: dividesI' pdivides_def r.p.m_assoc)
  hence 0:"(h \<otimes>\<^bsub>poly_ring R\<^esub> (f pdiv h)) \<otimes>\<^bsub>poly_ring R\<^esub> g pmod h = \<zero>\<^bsub>poly_ring R\<^esub>"
    using pmod_zero_iff_pdivides[OF carrier_is_subfield] assms
      long_division_closed[OF carrier_is_subfield] univ_poly_zero
    by (metis (no_types, opaque_lifting) r.p.m_closed)

  have "?L = (h \<otimes>\<^bsub>poly_ring R\<^esub> (f pdiv h) \<oplus>\<^bsub>poly_ring R\<^esub> (f pmod h)) \<otimes>\<^bsub>poly_ring R\<^esub> g pmod h"
    using assms by (intro arg_cong2[where f="(\<otimes>\<^bsub>poly_ring R\<^esub>)"] arg_cong2[where f="(pmod)"]
     pdiv_pmod[OF carrier_is_subfield]) auto
  also have "... = ((h \<otimes>\<^bsub>poly_ring R\<^esub> (f pdiv h)) \<otimes>\<^bsub>poly_ring R\<^esub> g \<oplus>\<^bsub>poly_ring R\<^esub>
    (f pmod h) \<otimes>\<^bsub>poly_ring R\<^esub> g) pmod h"
    using assms long_division_closed[OF carrier_is_subfield]
    by (intro r.p.l_distr arg_cong2[where f="(pmod)"]) auto
  also have "... = ((h \<otimes>\<^bsub>poly_ring R\<^esub> (f pdiv h)) \<otimes>\<^bsub>poly_ring R\<^esub> g) pmod h \<oplus>\<^bsub>poly_ring R\<^esub>
    ((f pmod h) \<otimes>\<^bsub>poly_ring R\<^esub> g pmod h)"
    using assms long_division_closed[OF carrier_is_subfield]
    by (intro long_division_add[OF carrier_is_subfield]) auto
  also have "... = ?R"
    using assms long_division_closed[OF carrier_is_subfield] unfolding 0 by auto
  finally show ?thesis
    by simp
qed

lemma pmod_mult_right:
  assumes "f \<in> carrier (poly_ring R)"
  assumes "g \<in> carrier (poly_ring R)"
  assumes "h \<in> carrier (poly_ring R)"
  shows "(f \<otimes>\<^bsub>poly_ring R\<^esub> g) pmod h = (f \<otimes>\<^bsub>poly_ring R\<^esub> (g pmod h)) pmod h" (is "?L = ?R")
proof -
  have "?L = (g \<otimes>\<^bsub>poly_ring R\<^esub> f) pmod h" using assms by algebra
  also have "... = ((g pmod h) \<otimes>\<^bsub>poly_ring R\<^esub> f) pmod h" by (intro pmod_mult_left assms)
  also have "... = ?R" using assms long_division_closed[OF carrier_is_subfield] by algebra
  finally show ?thesis by simp
qed

lemma pmod_mult_both:
  assumes "f \<in> carrier (poly_ring R)"
  assumes "g \<in> carrier (poly_ring R)"
  assumes "h \<in> carrier (poly_ring R)"
  shows "(f \<otimes>\<^bsub>poly_ring R\<^esub> g) pmod h = ((f pmod h) \<otimes>\<^bsub>poly_ring R\<^esub> (g pmod h)) pmod h"
    (is "?L = ?R")
proof -
  have "(f \<otimes>\<^bsub>poly_ring R\<^esub> g) pmod h = ((f pmod h) \<otimes>\<^bsub>poly_ring R\<^esub> g) pmod h"
    by (intro pmod_mult_left assms)
  also have "... = ?R"
    using assms long_division_closed[OF carrier_is_subfield] by (intro pmod_mult_right) auto
  finally show ?thesis by simp
qed

lemma field_Unit_minus_closed:
  assumes "x \<in> Units R"
  shows "\<ominus> x \<in> Units R"
  using assms mult_of.Units_eq by auto

end

lemma long_division_c:
  assumes "field\<^sub>C R"
  assumes "f \<in> carrier (poly_ring (ring_of R))"
  assumes "g \<in> carrier (poly_ring (ring_of R))"
  shows "long_division\<^sub>C R f g = (ring.pdiv (ring_of R) f g, ring.pmod (ring_of R) f g)"
proof -
  let ?P = "poly_ring (ring_of R)"
  let ?result = "(\<lambda>f r. f = snd r \<oplus>\<^bsub>poly_ring (ring_of R)\<^esub> (fst r \<otimes>\<^bsub>poly_ring (ring_of R)\<^esub> g))"

  define r where "r = long_division\<^sub>C R f g"

  interpret field "ring_of R" using assms(1) unfolding field\<^sub>C_def by auto
  interpret d_poly_ring: domain "poly_ring (ring_of R)"
    by (rule univ_poly_is_domain[OF carrier_is_subring])

  have ring_c: "ring\<^sub>C R" using assms(1) unfolding field\<^sub>C_def domain\<^sub>C_def cring\<^sub>C_def by auto
  have d_poly: "domain\<^sub>C (poly R)" using assms (1) unfolding field\<^sub>C_def by (intro poly_domain) auto

  have "r = long_division\<^sub>C R f g \<Longrightarrow> ?result f r \<and> {fst r, snd r} \<subseteq> carrier (poly_ring (ring_of R))"
    using assms(2)
  proof (induction "length f" arbitrary: f r rule:nat_less_induct)
    case 1

    have ind: "x = snd q \<oplus>\<^bsub>?P\<^esub> fst q \<otimes>\<^bsub>?P\<^esub> g" "{fst q, snd q} \<subseteq> carrier (poly_ring (ring_of R))"
      if "length x < length f " "q = long_division\<^sub>C R x g" "x \<in> carrier (poly_ring (ring_of R)) "
      for x q using 1(1) that by auto

    show ?case
    proof (cases "length g = 0 \<or> length f < length g")
      case True
      hence "r = (\<zero>\<^bsub>poly_ring (ring_of R)\<^esub>, f)"
        unfolding 1(2) univ_poly_zero by (subst long_division\<^sub>C.simps) simp
      then show ?thesis using assms(3) 1(3) by simp
    next
      case False
      hence "length g > 0" "length f \<ge> length g" by auto
      hence "f \<noteq> []" "g \<noteq> []" by auto
      hence f_carr: "f \<in> carrier ?P - {\<zero>\<^bsub>?P\<^esub>}" and g_carr: "g \<in> carrier ?P - {\<zero>\<^bsub>?P\<^esub>}"
         using 1(3) assms(3) univ_poly_zero by auto

      define k where "k = length f - length g"
      define \<alpha> where "\<alpha> = -\<^sub>C\<^bsub>R\<^esub> (hd f *\<^sub>C\<^bsub>R\<^esub>  (hd g) \<inverse>\<^sub>C\<^bsub>R\<^esub>)"
      define h where "h = [\<alpha>] *\<^sub>C\<^bsub>poly R\<^esub> X\<^sub>C\<^bsub>R\<^esub> ^\<^sub>C\<^bsub>poly R\<^esub> k"
      define f' where "f' = f +\<^sub>C\<^bsub>poly R\<^esub> (h *\<^sub>C\<^bsub>poly R\<^esub> g)"
      define f'' where "f'' = take (length f - 1) f'"
      obtain s t where st_def: "(s,t) = long_division\<^sub>C R f'' g" by (metis surj_pair)

      have "r = apfst (\<lambda>x. x +\<^sub>C\<^bsub>poly R\<^esub> -\<^sub>C\<^bsub>poly R\<^esub> h) (long_division\<^sub>C R f'' g)"
        using False unfolding 1(2)
        by (subst long_division\<^sub>C.simps) (simp add:Let_def f''_def f'_def h_def \<alpha>_def k_def)

      hence r_def: "r = (s +\<^sub>C\<^bsub>poly R\<^esub> -\<^sub>C\<^bsub>poly R\<^esub> h, t)"
        unfolding st_def[symmetric] by simp

      have "monic_poly (ring_of R) (X\<^bsub>ring_of R\<^esub> [^]\<^bsub>poly_ring (ring_of R)\<^esub> k)"
        by (intro monic_poly_pow monic_poly_var)
      hence [simp]: "lead_coeff (X\<^bsub>ring_of R\<^esub> [^]\<^bsub>poly_ring (ring_of R)\<^esub> k) = \<one>\<^bsub>ring_of R\<^esub>"
        unfolding monic_poly_def by simp

      have hd_f_unit: "hd f \<in> Units (ring_of R)" and hd_g_unit: "hd g \<in> Units (ring_of R)"
        using f_carr g_carr lead_coeff_carr field_Units by auto
      hence hd_f_carr: "hd f \<in> carrier (ring_of R)" and hd_g_carr: "hd g \<in> carrier (ring_of R)"
        by auto

      have k_def': "k = degree f - degree g" using False unfolding k_def by auto
      have \<alpha>_def': "\<alpha> = \<ominus>\<^bsub>ring_of R\<^esub> (hd f \<otimes>\<^bsub>ring_of R\<^esub> inv\<^bsub>ring_of R\<^esub> hd g)"
        unfolding \<alpha>_def using hd_g_unit hd_f_carr field_cD[OF assms(1)] by simp

      have \<alpha>_unit: "\<alpha> \<in> Units (ring_of R)" unfolding \<alpha>_def' using hd_f_unit hd_g_unit
        by (intro field_Unit_minus_closed) simp
      hence \<alpha>_carr: "\<alpha> \<in> carrier (ring_of R) - {\<zero>\<^bsub>ring_of R\<^esub>}" unfolding field_Units by simp
      hence \<alpha>_poly_carr: "[\<alpha>] \<in> carrier (poly_ring (ring_of R)) - {\<zero>\<^bsub>poly_ring (ring_of R)\<^esub>}"
        by (simp add: univ_poly_carrier[symmetric] univ_poly_zero polynomial_def)

      have h_def': "h = [\<alpha>] \<otimes>\<^bsub>?P\<^esub> X\<^bsub>ring_of R\<^esub> [^]\<^bsub>?P\<^esub> k"
        unfolding h_def poly_var domain_cD[OF d_poly] by (simp add:ring_of_poly[OF ring_c])
      have f'_def': "f' = f \<oplus>\<^bsub>?P\<^esub> (h \<otimes>\<^bsub>?P\<^esub> g)"
        unfolding f'_def domain_cD[OF d_poly] by (simp add:ring_of_poly[OF ring_c])

      have h_carr: "h \<in> carrier (poly_ring (ring_of R)) - {\<zero>\<^bsub>poly_ring (ring_of R)\<^esub>}"
        using d_poly_ring.mult_of.m_closed \<alpha>_poly_carr var_pow_carr[OF carrier_is_subring]
        unfolding h_def' by auto

      have "degree f = k + degree g" using False unfolding k_def by linarith
      also have "... = degree [\<alpha>] + degree (X\<^bsub>ring_of R\<^esub> [^]\<^bsub>?P\<^esub> k) + degree g"
        unfolding var_pow_degree[OF carrier_is_subring] by simp
      also have "... = degree h + degree g" unfolding h_def'
        by (intro arg_cong2[where f="(+)"] degree_mult[symmetric]
            carrier_is_subring \<alpha>_poly_carr var_pow_carr refl)
      also have "... = degree (h \<otimes>\<^bsub>poly_ring (ring_of R)\<^esub> g)"
        by (intro degree_mult[symmetric] carrier_is_subring h_carr g_carr)
      finally have deg_f: "degree f = degree (h \<otimes>\<^bsub>poly_ring (ring_of R)\<^esub> g)" by simp

      have f'_carr: "f' \<in> carrier (poly_ring (ring_of R))"
        using f_carr h_carr g_carr unfolding f'_def' by auto

      have "hd f = \<ominus>\<^bsub>ring_of R\<^esub> (\<alpha> \<otimes>\<^bsub>ring_of R\<^esub> lead_coeff g)"
        using hd_g_unit hd_f_carr hd_g_carr \<alpha>_unit \<alpha>_carr unfolding \<alpha>_def'
        by (simp add: m_assoc l_minus)
      also have "... = \<ominus>\<^bsub>ring_of R\<^esub> (hd h \<otimes>\<^bsub>ring_of R\<^esub> hd g)"
        using hd_f_carr \<alpha>_carr \<alpha>_poly_carr var_pow_carr[OF carrier_is_subring] unfolding h_def'
        by (subst lead_coeff_mult) (simp_all add:algebra_simps)
      also have "... = \<ominus>\<^bsub>ring_of R\<^esub> hd (h \<otimes>\<^bsub>poly_ring (ring_of R)\<^esub> g)"
        using h_carr g_carr by (subst lead_coeff_mult) auto
      finally have "hd f = \<ominus>\<^bsub>ring_of R\<^esub> hd (h \<otimes>\<^bsub>poly_ring (ring_of R)\<^esub> g)"
        by simp
      hence len_f': "length f' < length f" using deg_f h_carr g_carr d_poly_ring.integral
        unfolding f'_def' by (intro poly_add_cancel_len f_carr) auto
      hence f''_def': "f'' = f'" unfolding f''_def by simp

      have "{fst (s,t),snd (s,t)} \<subseteq> carrier (poly_ring (ring_of R))"
        using len_f' f''_def' f'_carr by (intro ind(2)[where x="f''"] st_def) auto
      hence s_carr: "s \<in> carrier ?P" and t_carr: "t \<in> carrier ?P" by auto

      have r_def': "r = (s \<ominus>\<^bsub>poly_ring (ring_of R)\<^esub> h, t)"
        using h_carr domain_cD[OF d_poly] unfolding r_def a_minus_def
        using ring_of_poly[OF ring_c,symmetric] by simp

      have r_carr: "{fst r, snd r} \<subseteq> carrier (poly_ring (ring_of R))"
        using s_carr t_carr h_carr unfolding r_def' by auto
      have "f = f'' \<ominus>\<^bsub>?P\<^esub> h \<otimes>\<^bsub>?P\<^esub> g"
        using h_carr g_carr f_carr unfolding f''_def' f'_def' by simp algebra
      also have "... = (snd (s,t) \<oplus>\<^bsub>?P\<^esub> fst (s,t) \<otimes>\<^bsub>?P\<^esub> g) \<ominus>\<^bsub>?P\<^esub> h \<otimes>\<^bsub>?P\<^esub> g"
        using f'_carr f''_def' len_f'
        by (intro arg_cong2[where f="\<lambda>x y. x \<ominus>\<^bsub>?P\<^esub> y"] ind(1) st_def) auto
      also have "... = t \<oplus>\<^bsub>?P\<^esub> (s \<ominus>\<^bsub>?P\<^esub> h) \<otimes>\<^bsub>?P\<^esub> g"
        using s_carr t_carr h_carr g_carr by simp algebra
      also have "... = snd r \<oplus>\<^bsub>poly_ring (ring_of R)\<^esub> fst r \<otimes>\<^bsub>poly_ring (ring_of R)\<^esub> g"
        unfolding r_def' by simp
      finally have "f = snd r \<oplus>\<^bsub>poly_ring (ring_of R)\<^esub> fst r \<otimes>\<^bsub>poly_ring (ring_of R)\<^esub> g" by simp
      thus ?thesis using r_carr by auto
    qed
  qed
  hence result: "?result f r" "{fst r, snd r} \<subseteq> carrier (poly_ring (ring_of R))"
    using r_def by auto
  show ?thesis
  proof (cases "g = []")
    case True then show ?thesis by (simp add:long_division\<^sub>C.simps pmod_def pdiv_def)
  next
    case False
    hence "snd r = [] \<or> degree (snd r) < degree g"
      using long_division_c_length unfolding r_def
      by (metis One_nat_def Suc_pred length_greater_0_conv not_less_eq)
    moreover have "f = g \<otimes>\<^bsub>?P\<^esub> (fst r) \<oplus>\<^bsub>poly_ring (ring_of R)\<^esub> (snd r)"
      using result(1,2) assms(2,3) by simp algebra
    ultimately have "long_divides f g (fst r, snd r)"
      using result(2) unfolding long_divides_def by (auto simp:mem_Times_iff)
    hence "(fst r, snd r) = (pdiv f g, pmod f g)"
      by (intro long_divisionI[OF carrier_is_subfield] False assms)
    then show ?thesis unfolding r_def by simp
  qed
qed

definition pdiv\<^sub>C :: "('a,'b) idx_ring_scheme \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "pdiv\<^sub>C R f g = fst (long_division\<^sub>C R f g)"

lemma pdiv_c:
  assumes "field\<^sub>C R"
  assumes "f \<in> carrier (poly_ring (ring_of R))"
  assumes "g \<in> carrier (poly_ring (ring_of R))"
  shows "pdiv\<^sub>C R f g = ring.pdiv (ring_of R) f g"
  unfolding pdiv\<^sub>C_def long_division_c[OF assms] by simp

definition pmod\<^sub>C :: "('a,'b) idx_ring_scheme \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "pmod\<^sub>C R f g = snd (long_division\<^sub>C R f g)"

lemma pmod_c:
  assumes "field\<^sub>C R"
  assumes "f \<in> carrier (poly_ring (ring_of R))"
  assumes "g \<in> carrier (poly_ring (ring_of R))"
  shows "pmod\<^sub>C R f g = ring.pmod (ring_of R) f g"
  unfolding pmod\<^sub>C_def long_division_c[OF assms] by simp

function ext_euclidean ::
  "('a,'b) idx_ring_scheme \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'a list) \<times> 'a list"
  where "ext_euclidean F f g = (
    if f = [] \<or> g = [] then
      ((1\<^sub>C\<^bsub>poly F\<^esub>, 1\<^sub>C\<^bsub>poly F\<^esub>),f +\<^sub>C\<^bsub>poly F\<^esub> g)
    else (
      let (p,q) = long_division\<^sub>C F f g;
          ((u,v),r) = ext_euclidean F g q
       in ((v,u +\<^sub>C\<^bsub>poly F\<^esub> (-\<^sub>C\<^bsub>poly F\<^esub> (p *\<^sub>C\<^bsub>poly F\<^esub> v))),r)))"
  by pat_completeness auto

termination
  apply (relation "measure (\<lambda>(_, _, f). length f)")
  subgoal by simp
  by (metis case_prod_conv in_measure length_greater_0_conv long_division_c_length prod.sel(2))

(* TODO MOVE *)
lemma (in domain) pdivides_self:
  assumes "x \<in> carrier (poly_ring R)"
  shows "x pdivides x"
proof -
  interpret d:domain "poly_ring R" by (rule univ_poly_is_domain[OF carrier_is_subring])
  show ?thesis
    using assms unfolding pdivides_def
    by (intro dividesI[where c="\<one>\<^bsub>poly_ring R\<^esub>"]) simp_all
qed

declare ext_euclidean.simps[simp del]

lemma ext_euclidean:
  assumes "field\<^sub>C R"
  defines "P \<equiv> poly_ring (ring_of R)"
  assumes "f \<in> carrier (poly_ring (ring_of R))"
  assumes "g \<in> carrier (poly_ring (ring_of R))"
  defines "r \<equiv> ext_euclidean R f g"
  shows "snd r = f \<otimes>\<^bsub>P\<^esub> (fst (fst r)) \<oplus>\<^bsub>P\<^esub> g \<otimes>\<^bsub>P\<^esub> (snd (fst r))" (is "?T1")
    and "snd r pdivides\<^bsub>ring_of R\<^esub> f" (is "?T2") "snd r pdivides\<^bsub>ring_of R\<^esub> g" (is "?T3")
    and "{snd r, fst (fst r), snd (fst r)} \<subseteq> carrier P" (is "?T4")
    and "snd r = [] \<longrightarrow> f = [] \<and> g = []" (is "?T5")
proof -
  let ?P= "poly_ring (ring_of R)"

  interpret field "ring_of R" using assms(1) unfolding field\<^sub>C_def by auto
  interpret d_poly_ring: domain "poly_ring (ring_of R)"
    by (rule univ_poly_is_domain[OF carrier_is_subring])

  have ring_c: "ring\<^sub>C R" using assms(1) unfolding field\<^sub>C_def domain\<^sub>C_def cring\<^sub>C_def by auto
  have d_poly: "domain\<^sub>C (poly R)" using assms (1) unfolding field\<^sub>C_def by (intro poly_domain) auto

  have pdiv_zero: "x pdivides\<^bsub>ring_of R\<^esub> \<zero>\<^bsub>?P\<^esub>" if "x \<in> carrier ?P" for x
    using that unfolding univ_poly_zero by (intro pdivides_zero[OF carrier_is_subring])

  have "snd r = f \<otimes>\<^bsub>?P\<^esub> (fst (fst r)) \<oplus>\<^bsub>?P\<^esub> g \<otimes>\<^bsub>?P\<^esub> (snd (fst r)) \<and>
    snd r pdivides\<^bsub>ring_of R\<^esub> f \<and> snd r pdivides\<^bsub>ring_of R\<^esub> g \<and>
    {snd r, fst (fst r), snd (fst r)} \<subseteq> carrier ?P \<and>
    (snd r = [] \<longrightarrow> f = [] \<and> g = [])"
    if "r = ext_euclidean R f g" "{f,g} \<subseteq> carrier ?P"
    using that
  proof (induction "length g" arbitrary: f g r rule:nat_less_induct)
    case 1
    have ind:
      "snd s = x \<otimes>\<^bsub>?P\<^esub> fst (fst s) \<oplus>\<^bsub>?P\<^esub> y \<otimes>\<^bsub>?P\<^esub> snd (fst s)"
      "snd s pdivides\<^bsub>ring_of R\<^esub> x" "snd s pdivides\<^bsub>ring_of R\<^esub> y"
      "{snd s, fst (fst s), snd (fst s)} \<subseteq> carrier ?P"
      "(snd s = [] \<longrightarrow> x = [] \<and> y = [])"
      if "length y < length g" "s = ext_euclidean R x y" "{x, y} \<subseteq> carrier ?P"
      for x y s using that 1(1) by metis+
    show ?case
    proof (cases "f = [] \<or> g = []")
      case True
      hence r_def: "r = ((\<one>\<^bsub>?P\<^esub>, \<one>\<^bsub>?P\<^esub>), f \<oplus>\<^bsub>?P\<^esub> g)" unfolding 1(2)
        by (simp add:ext_euclidean.simps domain_cD[OF d_poly] ring_of_poly[OF ring_c])

      consider "f = \<zero>\<^bsub>?P\<^esub>" |  "g = \<zero>\<^bsub>?P\<^esub>"
        using True unfolding univ_poly_zero by auto
      hence "snd r pdivides\<^bsub>ring_of R\<^esub> f \<and> snd r pdivides\<^bsub>ring_of R\<^esub> g"
        using 1(3) pdiv_zero pdivides_self unfolding r_def by cases auto
      moreover have "snd r = f \<otimes>\<^bsub>?P\<^esub> fst (fst r) \<oplus>\<^bsub>?P\<^esub> g \<otimes>\<^bsub>?P\<^esub> snd (fst r)"
        using 1(3) unfolding r_def by simp
      moreover have "{snd r, fst (fst r), snd (fst r)} \<subseteq> carrier ?P"
        using 1(3) unfolding r_def by auto
      moreover have "snd r = [] \<longrightarrow> f = [] \<and> g = []"
        using 1(3) True unfolding r_def by (auto simp:univ_poly_zero)
      ultimately show ?thesis by (intro conjI) metis+
    next
      case False
      obtain p q where pq_def: "(p,q) = long_division\<^sub>C R f g"
        by (metis surj_pair)
      obtain u v s where uvs_def: "((u,v),s) = ext_euclidean R g q"
        by (metis surj_pair)

      have "(p,q) = (pdiv f g, pmod f g)"
        using 1(3) unfolding pq_def by (intro long_division_c[OF assms(1)]) auto
      hence p_def: "p = pdiv f g" and q_def: "q = pmod f g" by auto
      have p_carr: "p \<in> carrier ?P" and q_carr: "q \<in> carrier ?P"
        using 1(3) long_division_closed[OF carrier_is_subfield] unfolding p_def q_def by auto

      have "length g > 0" using False by auto
      hence len_q: "length q < length g" using long_division_c_length pq_def by (metis snd_conv)
      have s_eq: "s = g \<otimes>\<^bsub>?P\<^esub> u \<oplus>\<^bsub>?P\<^esub> q \<otimes>\<^bsub>?P\<^esub> v"
        and s_div_g: "s pdivides\<^bsub>ring_of R\<^esub> g"
        and s_div_q: "s pdivides\<^bsub>ring_of R\<^esub> q"
        and suv_carr: "{s,u,v} \<subseteq> carrier ?P"
        and s_zero_iff: "s = [] \<longrightarrow> g = [] \<and> q = []"
        using ind[OF len_q uvs_def _] q_carr 1(3) by auto

      have "r = ((v,u +\<^sub>C\<^bsub>poly R\<^esub> (-\<^sub>C\<^bsub>poly R\<^esub> (p *\<^sub>C\<^bsub>poly R\<^esub> v))),s)" unfolding 1(2) using False
        by (subst ext_euclidean.simps) (simp add: pq_def[symmetric] uvs_def[symmetric])
      also have "... = ((v, u \<ominus>\<^bsub>?P\<^esub> (p \<otimes>\<^bsub>?P\<^esub> v)), s)" using p_carr suv_carr domain_cD[OF d_poly]
        unfolding a_minus_def ring_of_poly[OF ring_c] by (intro arg_cong2[where f="Pair"] refl) simp
      finally have r_def: "r = ((v, u \<ominus>\<^bsub>?P\<^esub> (p \<otimes>\<^bsub>?P\<^esub> v)), s)" by simp

      have "snd r = g \<otimes>\<^bsub>?P\<^esub> u \<oplus>\<^bsub>?P\<^esub> q \<otimes>\<^bsub>?P\<^esub> v" unfolding r_def s_eq by simp
      also have "... = g \<otimes>\<^bsub>?P\<^esub> u \<oplus>\<^bsub>?P\<^esub> (f \<ominus>\<^bsub>?P\<^esub> g \<otimes>\<^bsub>?P\<^esub> p) \<otimes>\<^bsub>?P\<^esub> v"
        using 1(3) p_carr q_carr suv_carr
        by (subst pdiv_pmod[OF carrier_is_subfield, of "f" "g"])
         (simp_all add:p_def[symmetric] q_def[symmetric], algebra)
      also have "... = f \<otimes>\<^bsub>?P\<^esub> v \<oplus>\<^bsub>?P\<^esub> g \<otimes>\<^bsub>?P\<^esub> (u \<ominus>\<^bsub>?P\<^esub> ((p \<otimes>\<^bsub>?P\<^esub> v)))"
        using 1(3) p_carr q_carr suv_carr  by simp algebra
      finally have r1: "snd r = f \<otimes>\<^bsub>?P\<^esub> fst (fst r) \<oplus>\<^bsub>?P\<^esub> g \<otimes>\<^bsub>?P\<^esub> snd (fst r)"
        unfolding r_def by simp
      have "pmod f s = pmod (g \<otimes>\<^bsub>?P\<^esub> p \<oplus>\<^bsub>?P\<^esub> q) s" using 1(3)
        by (subst pdiv_pmod[OF carrier_is_subfield, of "f" "g"])
          (simp_all add:p_def[symmetric] q_def[symmetric])
      also have "... = pmod (g \<otimes>\<^bsub>?P\<^esub> p) s \<oplus>\<^bsub>?P\<^esub> pmod q s"
        using 1(3) p_carr q_carr suv_carr
        by (subst long_division_add[OF carrier_is_subfield]) simp_all
      also have "... = pmod (pmod g s \<otimes>\<^bsub>?P\<^esub> p) s \<oplus>\<^bsub>?P\<^esub> []"
        using 1(3) p_carr q_carr suv_carr s_div_q
        by (intro arg_cong2[where f="(\<oplus>\<^bsub>?P\<^esub>)"] pmod_mult_left)
          (simp_all add: pmod_zero_iff_pdivides[OF carrier_is_subfield])
      also have "... = pmod (\<zero>\<^bsub>?P\<^esub> \<otimes>\<^bsub>?P\<^esub> p) s \<oplus>\<^bsub>?P\<^esub> \<zero>\<^bsub>?P\<^esub>" unfolding univ_poly_zero
        using 1(3) p_carr q_carr suv_carr s_div_g by (intro arg_cong2[where f="(\<oplus>\<^bsub>?P\<^esub>)"]
            arg_cong2[where f="(\<otimes>\<^bsub>?P\<^esub>)"] arg_cong2[where f="pmod"])
          (simp_all add: pmod_zero_iff_pdivides[OF carrier_is_subfield])
      also have "... = pmod \<zero>\<^bsub>?P\<^esub> s"
        using p_carr suv_carr long_division_closed[OF carrier_is_subfield] by simp
      also have "... = []" unfolding univ_poly_zero
        using suv_carr long_division_zero(2)[OF carrier_is_subfield] by simp
      finally have "pmod f s = []" by simp
      hence r2: "snd r pdivides\<^bsub>ring_of R\<^esub> f" using suv_carr 1(3)  unfolding r_def
        by (subst pmod_zero_iff_pdivides[OF carrier_is_subfield,symmetric]) simp_all
      have r3: "snd r pdivides\<^bsub>ring_of R\<^esub> g" unfolding r_def using s_div_g by auto
      have r4: "{snd r, fst (fst r), snd (fst r)} \<subseteq> carrier ?P"
        using suv_carr p_carr unfolding r_def by simp_all
      have r5: "f = [] \<and> g = []" if "snd r = []"
      proof -
        have r5_a: "g = [] \<and> q = []" using that s_zero_iff unfolding r_def by simp
        hence "pmod f [] = []" unfolding q_def by auto
        hence "f = []" using pmod_def by simp
        thus ?thesis using r5_a by auto
      qed

      show ?thesis using r1 r2 r3 r4 r5  by (intro conjI) metis+
    qed
  qed
  thus ?T1 ?T2 ?T3 ?T4 ?T5 using assms by auto
qed

end