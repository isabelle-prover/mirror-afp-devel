(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsection \<open>Mahler Measure\<close>

text \<open>This part contains a definition of the Mahler measure, it contains Landau's inequality and
  the Graeffe-transformation. We also assemble a heuristic to approximate the Mahler's measure.\<close>

theory Mahler_Measure
imports
  "../Sqrt_Babylonian/Sqrt_Babylonian"
  Poly_Mod_Finite_Field_Record_Based (* stuff about polynomials *)
  "../Polynomial_Factorization/Fundamental_Theorem_Algebra_Factorized"
  "../Polynomial_Factorization/Missing_Multiset"
begin

context comm_monoid_list begin
  lemma induct_gen_abs:
    assumes "\<And> a r. a\<in>set lst \<Longrightarrow> P (f (h a) r) (f (g a) r)"
            "\<And> x y z. P x y \<Longrightarrow> P y z \<Longrightarrow> P x z"
            "P (F (map g lst)) (F (map g lst))"
    shows "P (F (map h lst)) (F (map g lst)) "
  using assms proof(induct lst arbitrary:P)
    case (Cons a as P)
    have inl:"a\<in>set (a#as)" by auto
    let ?uf = "\<lambda> v w. P (f (g a) v) (f (g a) w)"
    have p_suc:"?uf (F (map g as)) (F (map g as))"
      using Cons.prems(3) by auto
    { fix r aa assume "aa \<in> set as" hence ins:"aa \<in> set (a#as)" by auto
      have "P (f (g a) (f (h aa) r)) (f (g a) (f (g aa) r))"
        using Cons.prems(1)[of aa "f r (g a)",OF ins]
        by (auto simp: assoc commute left_commute)
    } note h = this
    from Cons.hyps(1)[of ?uf, OF h Cons.prems(2)[simplified] p_suc]
    have e1:"P (f (g a) (F (map h as))) (f (g a) (F (map g as)))" by simp
    have e2:"P (f (h a) (F (map h as))) (f (g a) (F (map h as)))"
      using Cons.prems(1)[OF inl] by blast
    from Cons(3)[OF e2 e1] show ?case by auto next
  qed auto
end

lemma prod_induct_gen:
  assumes "\<And> a r. f (h a * r :: 'a :: {comm_monoid_mult}) = f (g a * r)"
  shows "f (\<Prod>v\<leftarrow>lst. h v) = f (\<Prod>v\<leftarrow>lst. g v)"
proof - let "?P x y" = "f x = f y"
  show ?thesis using comm_monoid_mult_class.prod_list.induct_gen_abs[of _ ?P,OF assms] by auto
qed

context semiring_hom begin
lemma map_poly_single[simp]:
  "map_poly hom [:h:] = ([:hom h:])"
  unfolding map_poly_def fold_coeffs_def coeffs_def by simp
lemma map_poly_preserves_prod_list[simp]:
  "map_poly hom (prod_list x) = prod_list (map (map_poly hom) x)"
  by(induct x,auto simp:one_poly_def)
lemma map_poly_preserves_sum_list[simp]:
  "map_poly hom (sum_list x) = sum_list (map (map_poly hom) x)"
  by(induct x,auto simp:one_poly_def)
end

context inj_semiring_hom
begin
declare map_poly_0_iff[simp add]
lemma map_poly_preservers:
  "hom (lead_coeff p) = lead_coeff (map_poly hom p)"
  "hom (coeff p n) = coeff (map_poly hom p) n"
  unfolding poly_eq_iff lead_coeff_def by simp_all
end

abbreviation complex_of_int::"int => complex" where
  "complex_of_int \<equiv> of_int"


definition l2norm_list :: "int list \<Rightarrow> int" where
  "l2norm_list lst = \<lfloor>sqrt (sum_list (map (\<lambda> a. a * a) lst))\<rfloor>"

abbreviation l2norm :: "int poly \<Rightarrow> int" where
  "l2norm p \<equiv> l2norm_list (coeffs p)"

abbreviation "norm2 p \<equiv> \<Sum>a\<leftarrow>coeffs p. (cmod a)\<^sup>2" (* the square of the Euclidean/l2-norm *)

abbreviation l2norm_complex where
  "l2norm_complex p \<equiv> sqrt (norm2 p)"

abbreviation height :: "int poly \<Rightarrow> int" where
  "height p \<equiv> max_list (map (nat \<circ> abs) (coeffs p))"

definition complex_roots_complex where
  "complex_roots_complex (p::complex poly) = (SOME as. smult (coeff p (degree p)) (\<Prod>a\<leftarrow>as. [:- a, 1:]) = p \<and> length as = degree p)"

lemma complex_roots:
  "smult (lead_coeff p) (\<Prod>a\<leftarrow>complex_roots_complex p. [:- a, 1:]) = p"
  "length (complex_roots_complex p) = degree p"
  using someI_ex[OF fundamental_theorem_algebra_factorized]
  unfolding complex_roots_complex_def lead_coeff_def by simp_all

lemma complex_roots_c:"complex_roots_complex [:c:] = []"
  using complex_roots(2)[of "[:c:]"] by auto
lemma complex_roots_1:"complex_roots_complex 1 = []" unfolding one_poly_def complex_roots_c by auto

declare complex_roots(2)[simp add]

lemma linear_term_irreducible[simp]: "irreducible [:- a, 1:]" 
  by (rule linear_irreducible, simp)

definition complex_roots_int where
  "complex_roots_int (p::int poly) = complex_roots_complex (map_poly of_int p)"

lemma complex_roots_int:
  "smult (lead_coeff p) (\<Prod>a\<leftarrow>complex_roots_int p. [:- a, 1:]) = map_poly of_int p"
  "length (complex_roots_int p) = degree p"
proof -
  interpret inj_semiring_hom complex_of_int by(unfold_locales,auto)
  show   "smult (lead_coeff p) (\<Prod>a\<leftarrow>complex_roots_int p. [:- a, 1:]) = map_poly of_int p"
  "length (complex_roots_int p) = degree p"
  using complex_roots[of "map_poly of_int p"] unfolding complex_roots_int_def 
  by (simp_all add: map_poly_preservers)
qed

text {* The measure for polynomials, after K. Mahler *}

definition mahler_measure_poly where
  "mahler_measure_poly p = cmod (lead_coeff p) * (\<Prod>a\<leftarrow>complex_roots_complex p. (max 1 (cmod a)))"

definition mahler_measure where
  "mahler_measure p = mahler_measure_poly (map_poly complex_of_int p)"

definition mahler_measure_monic where
  "mahler_measure_monic p = (\<Prod>a\<leftarrow>complex_roots_complex p. (max 1 (cmod a)))"

lemma mahler_measure_poly_via_monic :
  "mahler_measure_poly p = cmod (lead_coeff p) * mahler_measure_monic p"
  unfolding mahler_measure_poly_def mahler_measure_monic_def by simp

lemma smult_inj[simp]: assumes "(a::'a::idom) \<noteq> 0" shows "inj (smult a)"
using assms unfolding inj_on_def
by (metis Ring_Hom_Poly.map_poly_inj mult_cancel_left mult_zero_right smult_map_poly)

definition reconstruct_poly::"'a::idom \<Rightarrow> 'a list \<Rightarrow> 'a poly" where
  "reconstruct_poly c roots = smult c (\<Prod>a\<leftarrow>roots. [:- a, 1:])"

lemma reconstruct_is_original_poly:
  "reconstruct_poly (lead_coeff p) (complex_roots_complex p) = p"
  by (simp add:complex_roots(1) reconstruct_poly_def)

lemma reconstruct_with_type_conversion:
  "smult (lead_coeff (map_poly of_int f)) (prod_list (map (\<lambda> a. [:- a, 1:]) (complex_roots_int f)))
   = map_poly of_int f"
unfolding complex_roots_int_def complex_roots(1) by simp

lemma reconstruct_prod:
  shows "reconstruct_poly (a::complex) as * reconstruct_poly b bs
        = reconstruct_poly (a * b) (as @ bs)"
unfolding reconstruct_poly_def by auto

lemma linear_term_inj[simp]: "inj (\<lambda> a. [:- a, 1::'a::idom:])"
  unfolding inj_on_def by simp

lemma reconstruct_poly_monic_defines_mset:
  assumes "(\<Prod>a\<leftarrow>as. [:- a, 1:]) = (\<Prod>a\<leftarrow>bs. [:- a, 1::'a::{field,euclidean_ring_gcd}:])"
  shows "mset as = mset bs"
proof -
  let ?as = "mset (map (\<lambda> a. [:- a, 1:]) as)"
  let ?bs = "mset (map (\<lambda> a. [:- a, 1:]) bs)"
  have eq_smult:"prod_mset ?as = prod_mset ?bs" using assms by (metis prod_mset_prod_list)
  have irr:"\<And> as. set_mset (mset (map (\<lambda> a. [:- a, 1:]) as)) \<subseteq> {q. irreducible q \<and> monic q}"
    by auto
  from monic_factorization_unique_mset[OF eq_smult irr irr]
  show ?thesis by (simp add: inj_eq multiset.inj_map)
qed

lemma reconstruct_poly_defines_mset_of_argument:
  assumes "(a::'a::{field,euclidean_ring_gcd}) \<noteq> 0"
          "reconstruct_poly a as = reconstruct_poly a bs"
  shows "mset as = mset bs"
proof -
  have eq_smult:"smult a (\<Prod>a\<leftarrow>as. [:- a, 1:]) = smult a (\<Prod>a\<leftarrow>bs. [:- a, 1:])"
     using assms(2) by (auto simp:reconstruct_poly_def)
  from reconstruct_poly_monic_defines_mset[OF Fun.injD[OF smult_inj[OF assms(1)] eq_smult]]
  show ?thesis by simp
qed

lemma complex_roots_complex_prod [simp]:
  assumes "f \<noteq> 0" "g \<noteq> 0"
  shows  "mset (complex_roots_complex (f * g))
        = mset (complex_roots_complex f) + mset (complex_roots_complex g)"
proof -
  let ?p = "f * g"
  let "?lc v" = "(lead_coeff (v:: complex poly))"
  have nonzero_prod:"?lc ?p \<noteq> 0" using assms unfolding lead_coeff_def by auto
  from reconstruct_prod[of "?lc f" "complex_roots_complex f" "?lc g" "complex_roots_complex g"]
  have "reconstruct_poly (?lc ?p) (complex_roots_complex ?p)
       = reconstruct_poly (?lc ?p) (complex_roots_complex f @ complex_roots_complex g)"
    unfolding lead_coeff_mult[symmetric] reconstruct_is_original_poly by auto
  from reconstruct_poly_defines_mset_of_argument[OF nonzero_prod this]
  show ?thesis by simp
qed

lemma mset_mult_add:
  assumes "mset (a::'a::field list) = mset b + mset c"
  shows "prod_list a = prod_list b * prod_list c"
  unfolding prod_mset_prod_list[symmetric]
  using prod_mset_Un[of "mset b" "mset c",unfolded assms[symmetric]].

lemma mset_mult_add_2:
  assumes "mset a = mset b + mset c"
  shows "prod_list (map i a::'b::field list) = prod_list (map i b) * prod_list (map i c)"
proof -
  have r:"mset (map i a) = mset (map i b) + mset (map i c) " using assms 
    by (metis map_append mset_append mset_map)
  show ?thesis using mset_mult_add[OF r] by auto
qed

lemma measure_mono_eq_prod:
  assumes "f \<noteq> 0" "g \<noteq> 0"
  shows "mahler_measure_monic (f * g) = mahler_measure_monic f * mahler_measure_monic g"
  unfolding mahler_measure_monic_def
  using mset_mult_add_2[OF complex_roots_complex_prod[OF assms],of "\<lambda> a. max 1 (cmod a)"] by simp

lemma mahler_measure_poly_0[simp]: "mahler_measure_poly 0 = 0" unfolding mahler_measure_poly_via_monic by auto

lemma measure_eq_prod: (* Remark 10.2 *)
  "mahler_measure_poly (f * g) = mahler_measure_poly f * mahler_measure_poly g"
proof -
  consider "f = 0" | "g = 0" | (both) "f \<noteq> 0" "g \<noteq> 0" by auto
  thus ?thesis proof(cases)
    case both show ?thesis unfolding mahler_measure_poly_via_monic norm_mult lead_coeff_mult
      by (auto simp: measure_mono_eq_prod[OF both])
  qed (simp_all)
qed

lemma prod_cmod[simp]:
  "cmod (\<Prod>a\<leftarrow>lst. f a) = (\<Prod>a\<leftarrow>lst. cmod (f a))"
  by(induct lst,auto simp:real_normed_div_algebra_class.norm_mult)

lemma lead_coeff_of_prod[simp]:
  "lead_coeff (\<Prod>a\<leftarrow>lst. f a::'a::{idom} poly) = (\<Prod>a\<leftarrow>lst. lead_coeff (f a))"
by(induct lst,auto simp:lead_coeff_mult)

lemma ineq_about_squares:assumes "x \<le> (y::real)" shows "x \<le> c^2 + y" using assms
  by (simp add: add.commute add_increasing2)

lemma first_coeff_le_tail:"(cmod (lead_coeff g))^2 \<le> (\<Sum>a\<leftarrow>coeffs g. (cmod a)^2)"
proof(induct g)
  case (pCons a p)
    thus ?case proof(cases "p = 0") case False
      show ?thesis using pCons unfolding lead_coeff_pCons(1)[OF False]
        by(cases "a = 0",simp_all add:ineq_about_squares)
    qed simp
qed simp


lemma square_prod_cmod[simp]:
  "(cmod (a * b))^2 = cmod a ^ 2 * cmod b ^ 2"
by (simp add: norm_mult power_mult_distrib)

lemma coeffs_smult[simp]:
  "(\<Sum>a\<leftarrow>coeffs (smult v p). (cmod a)^2) = (cmod v)^2 * (\<Sum>a\<leftarrow>coeffs p. (cmod a)^2)" 
  (is "?l = ?r")
proof - 
  have "?l = (\<Sum>a\<leftarrow>coeffs p. (cmod v)^2 * (cmod a)^2)" by(cases "v=0";induct p,auto)
  thus ?thesis by (auto simp:sum_list_const_mult)
qed

abbreviation "linH a \<equiv> if (cmod a > 1) then [:- 1,cnj a:] else [:- a,1:]"

lemma coeffs_cong_1[simp]: "cCons a v = cCons b v \<longleftrightarrow> a = b" unfolding cCons_def by auto

lemma strip_while_singleton[simp]:
  "strip_while (op = 0) [v * a] = cCons (v * a) []" unfolding cCons_def strip_while_def by auto

lemma coeffs_times_linterm:
  shows "coeffs (pCons 0 (smult a p) + smult b p) = strip_while (HOL.eq (0::'a::{comm_ring_1}))
     (map (\<lambda>(c,d).b*d+c*a) (zip (0 # coeffs p) (coeffs p @ [0])))" proof -
{fix v
have "coeffs (smult b p + pCons (a* v) (smult a p)) = strip_while (HOL.eq 0) (map (\<lambda>(c,d).b*d+c*a) (zip ([v] @ coeffs p) (coeffs p @ [0])))"
proof(induct p arbitrary:v) case (pCons pa ps) thus ?case by auto qed auto (* just putting ;auto does not work *)
}
from this[of 0] show ?thesis by (simp add: add.commute)
qed

lemma filter_distr_rev[simp]:
  shows "filter f (rev lst) = rev (filter f lst)"
by(induct lst;auto)

lemma strip_while_filter:
  shows "filter (op \<noteq> 0) (strip_while (op = 0) (lst::'a::zero list)) = filter (op \<noteq> 0) lst"
proof - {fix lst::"'a list"
  have "filter (op \<noteq> 0) (dropWhile (op = 0) lst) = filter (op \<noteq> 0) lst" by (induct lst;auto)
  hence "(filter (op \<noteq> 0) (strip_while (op = 0) (rev lst))) = filter (op \<noteq> 0) (rev lst)"
  unfolding strip_while_def by(simp)}
  from this[of "rev lst"] show ?thesis by simp
qed

lemma sum_stripwhile[simp]:
  assumes "f 0 = 0"
  shows "(\<Sum>a\<leftarrow>strip_while (op = 0) lst. f a) = (\<Sum>a\<leftarrow>lst. f a)"
proof -
  {fix lst
    have "(\<Sum>a\<leftarrow>filter (op \<noteq> 0) lst. f a) = (\<Sum>a\<leftarrow>lst. f a)" by(induct lst,auto simp:assms)}
  note f=this
  have "sum_list (map f (filter (op \<noteq> 0) (strip_while (op = 0) lst)))
       = sum_list (map f (filter (op \<noteq> 0) lst))"
  using strip_while_filter[of lst] by(simp)
  thus ?thesis unfolding f.
qed

lemma complex_split : "Complex a b = c \<longleftrightarrow> (a = Re c \<and> b = Im c)"
  using complex_surj by auto

lemma norm_times_const:"(\<Sum>y\<leftarrow>lst. (cmod (a * y))\<^sup>2) = (cmod a)\<^sup>2 * (\<Sum>y\<leftarrow>lst. (cmod y)\<^sup>2)"
by(induct lst,auto simp:ring_distribs)

fun bisumTail where (* Used for Landau's lemma *)
  "bisumTail f (Cons a (Cons b bs)) = f a b + bisumTail f (Cons b bs)" |
  "bisumTail f (Cons a Nil) = f a 0" |
  "bisumTail f Nil = f 1 0" (* never called, not used in proofs *)
fun bisum where
  "bisum f (Cons a as) = f 0 a + bisumTail f (Cons a as)" |
  "bisum f Nil = f 0 0"

lemma bisumTail_is_map_zip:
  "(\<Sum>x\<leftarrow>zip (v # l1) (l1 @ [0]). f x) = bisumTail (\<lambda>x y .f (x,y))  (v#l1)"
by(induct l1 arbitrary:v,auto)
(* converting to and from bisum *)
lemma bisum_is_map_zip:
  "(\<Sum>x\<leftarrow>zip (0 # l1) (l1 @ [0]). f x) = bisum (\<lambda>x y. f (x,y)) l1"
using bisumTail_is_map_zip[of f "hd l1" "tl l1"] by(cases l1,auto)
lemma map_zip_is_bisum:
  "bisum f l1 = (\<Sum>(x,y)\<leftarrow>zip (0 # l1) (l1 @ [0]). f x y)"
using bisum_is_map_zip[of "\<lambda>(x,y). f x y"] by auto

lemma bisum_outside :
  "(bisum (\<lambda> x y. f1 x - f2 x y + f3 y) lst :: 'a :: field)
  = sum_list (map f1 lst) + f1 0 - bisum f2 lst + sum_list (map f3 lst) + f3 0"
proof(cases lst)
  case (Cons a lst) show ?thesis unfolding map_zip_is_bisum Cons by(induct lst arbitrary:a,auto)
qed auto

lemma Landau_lemma:
  "(\<Sum>a\<leftarrow>coeffs (\<Prod>a\<leftarrow>lst. [:- a, 1:]). (cmod a)\<^sup>2) = (\<Sum>a\<leftarrow>coeffs (\<Prod>a\<leftarrow>lst. linH a). (cmod a)\<^sup>2)"
  (is "norm2 ?l = norm2 ?r")
proof -
  have a:"\<And> a. (cmod a)\<^sup>2 = Re (a * cnj a) " using complex_norm_square
    unfolding complex_split complex_of_real_def by simp
  have b:"\<And> x a y. (cmod (x - a * y))^2
               = (cmod x)\<^sup>2 - Re (a * y * cnj x + x * cnj (a * y)) + (cmod (a * y))^2"
     unfolding left_diff_distrib right_diff_distrib a complex_cnj_diff by simp
  have c:"\<And> y a x. (cmod (cnj a * x - y))\<^sup>2
               = (cmod (a * x))\<^sup>2 - Re (a * y * cnj x + x * cnj (a * y)) + (cmod y)^2"
     unfolding left_diff_distrib right_diff_distrib a complex_cnj_diff
     by (simp add: mult.assoc mult.left_commute)
  { fix f1 a
    have "norm2 ([:- a, 1 :] * f1) = bisum (\<lambda>x y. cmod (x - a * y)^2) (coeffs f1)"
      by(simp add: bisum_is_map_zip[of _ "coeffs f1"] coeffs_times_linterm[of 1 _ "-a",simplified])
    also have "\<dots> = norm2 f1 + cmod a^2*norm2 f1
                  - bisum (\<lambda>x y. Re (a * y * cnj x + x * cnj (a * y))) (coeffs f1)"
      unfolding b bisum_outside norm_times_const by simp
    also have "\<dots> = bisum (\<lambda>x y. cmod (cnj a * x - y)^2) (coeffs f1)"
      unfolding c bisum_outside norm_times_const by auto
    also have "\<dots> = norm2 ([:- 1, cnj a :] * f1)"
      using coeffs_times_linterm[of "cnj a" _ "-1"]
      by(simp add: bisum_is_map_zip[of _ "coeffs f1"] mult.commute)
    finally have "norm2 ([:- a, 1 :] * f1) = \<dots>".}
  hence h:"\<And> a f1. norm2 ([:- a, 1 :] * f1) = norm2 (linH a * f1)" by auto
  show ?thesis by(rule prod_induct_gen[OF h])
qed

lemma Landau_inequality:
  "mahler_measure_poly f \<le> l2norm_complex f"
proof -
  let ?f = "reconstruct_poly (lead_coeff f) (complex_roots_complex f)"
  let ?roots = "(complex_roots_complex f)"
  let ?g = "\<Prod>a\<leftarrow>?roots. linH a"
  (* g is chosen such that lead_coeff_g holds, and its l2 norm is equal to f's l2 norm *)
  have max:"\<And>a. cmod (if 1 < cmod a then cnj a else 1) = max 1 (cmod a)" by(simp add:if_split,auto)
  have "\<And>a. 1 < cmod a \<Longrightarrow> a \<noteq> 0" by auto
  hence "\<And>a. lead_coeff (linH a) = (if (cmod a > 1) then cnj a else 1)" by(auto simp:if_split)
  hence lead_coeff_g:"cmod (lead_coeff ?g) = (\<Prod>a\<leftarrow>?roots. max 1 (cmod a))" by(auto simp:max)
  
  have "norm2 f = (\<Sum>a\<leftarrow>coeffs ?f. (cmod a)^2)" unfolding reconstruct_is_original_poly..
  also have "\<dots> = cmod (lead_coeff f)^2 * (\<Sum>a\<leftarrow>coeffs (\<Prod>a\<leftarrow>?roots. [:- a, 1:]). (cmod a)\<^sup>2)" 
    unfolding reconstruct_poly_def using coeffs_smult.
  finally have fg_norm:"norm2 f = cmod (lead_coeff f)^2 * (\<Sum>a\<leftarrow>coeffs ?g. (cmod a)^2)"
    unfolding Landau_lemma by auto

  have "(cmod (lead_coeff ?g))^2 \<le> (\<Sum>a\<leftarrow>coeffs ?g. (cmod a)^2)"
    using first_coeff_le_tail by blast
  from ordered_comm_semiring_class.comm_mult_left_mono[OF this]
  have "(cmod (lead_coeff f) * cmod (lead_coeff ?g))^2 \<le> (\<Sum>a\<leftarrow>coeffs f. (cmod a)^2)"
    unfolding fg_norm by (simp add:power_mult_distrib)
  hence "cmod (lead_coeff f) * (\<Prod>a\<leftarrow>?roots. max 1 (cmod a)) \<le> sqrt (norm2 f)"
    using NthRoot.real_le_rsqrt lead_coeff_g by auto
  thus "mahler_measure_poly f \<le> sqrt (norm2 f)"
    using reconstruct_with_type_conversion[unfolded complex_roots_int_def]
    by (simp add: mahler_measure_poly_via_monic mahler_measure_monic_def complex_roots_int_def)
qed

lemma prod_list_ge1:
  assumes "Ball (set x) (\<lambda> (a::real). a \<ge> 1)"
  shows "prod_list x \<ge> 1"
using assms proof(induct x)
  case (Cons a as)
    have "\<forall>a\<in>set as. 1 \<le> a" "1 \<le> a" using Cons(2) by auto
    thus ?case using Cons.hyps mult_mono' by fastforce
qed auto

lemma mahler_measure_monic_ge_1: "mahler_measure_monic p \<ge> 1"
  unfolding mahler_measure_monic_def by(rule prod_list_ge1,simp)

lemma mahler_measure_monic_ge_0: "mahler_measure_monic p \<ge> 0"
  using mahler_measure_monic_ge_1 le_numeral_extra(1) order_trans by blast

lemma mahler_measure_ge_0: "0 \<le> mahler_measure h" unfolding mahler_measure_def mahler_measure_poly_via_monic
  by (simp add: mahler_measure_monic_ge_0)

lemma mahler_measure_constant[simp]: "mahler_measure_poly [:c:] = cmod c" 
proof -
  have main: "complex_roots_complex [:c:] = []" unfolding complex_roots_complex_def
    by (rule some_equality, auto)
  show ?thesis unfolding mahler_measure_poly_def lead_coeff_def main by auto
qed
  
lemma mahler_measure_factor[simp]: "mahler_measure_poly [:- a, 1:] = max 1 (cmod a)" 
proof -
  have main: "complex_roots_complex [:- a, 1:] = [a]" unfolding complex_roots_complex_def
  proof (rule some_equality, auto, goal_cases)
    case (1 as)
    thus ?case by (cases as, auto)
  qed
  show ?thesis unfolding mahler_measure_poly_def lead_coeff_def main by auto
qed

lemma mahler_measure_poly_explicit: "mahler_measure_poly (smult c (\<Prod>a\<leftarrow>as. [:- a, 1:]))
  = cmod c * (\<Prod>a\<leftarrow>as. (max 1 (cmod a)))" 
proof (cases "c = 0")
  case True
  thus ?thesis by auto
next
  case False note c = this
  show ?thesis
  proof (induct as)
    case (Cons a as)
    have "mahler_measure_poly (smult c (\<Prod>a\<leftarrow>a # as. [:- a, 1:]))
      = mahler_measure_poly (smult c (\<Prod>a\<leftarrow>as. [:- a, 1:]) * [: -a, 1 :])"
      by (rule arg_cong[of _ _ mahler_measure_poly], unfold list.simps prod_list.Cons mult_smult_left, simp)
    also have "\<dots> = mahler_measure_poly (smult c (\<Prod>a\<leftarrow>as. [:- a, 1:])) * mahler_measure_poly ([:- a, 1:])" 
      (is "_ = ?l * ?r") by (rule measure_eq_prod)
    also have "?l = cmod c * (\<Prod>a\<leftarrow>as. max 1 (cmod a))" unfolding Cons by simp
    also have "?r = max 1 (cmod a)" by simp
    finally show ?case by simp
  next
    case Nil
    show ?case by (simp add: one_poly_def)
  qed
qed

definition graeffe_poly :: "'a \<Rightarrow> 'a :: comm_ring_1 list \<Rightarrow> nat \<Rightarrow> 'a poly" where
  "graeffe_poly c as m = smult (c ^ (2^m)) (\<Prod>a\<leftarrow>as. [:- (a ^ (2^m)), 1:])" 
  

context
  fixes f :: "complex poly" and c as
  assumes f: "f = smult c (\<Prod>a\<leftarrow>as. [:- a, 1:])"
begin
lemma mahler_graeffe: "mahler_measure_poly (graeffe_poly c as m) = (mahler_measure_poly f)^(2^m)"
proof -
  have graeffe: "graeffe_poly c as m = smult (c ^ 2 ^ m) (\<Prod>a\<leftarrow>(map (\<lambda> a. a ^ 2 ^ m) as). [:- a, 1:])" 
    unfolding graeffe_poly_def
    by (rule arg_cong[of _ _ "smult (c ^ 2 ^ m)"], induct as, auto)
  {
    fix n :: nat
    assume n: "n > 0" 
    have id: "max 1 (cmod a ^ n) = max 1 (cmod a) ^ n" for a
    proof (cases "cmod a \<le> 1")
      case True 
      hence "cmod a ^ n \<le> 1" by (simp add: power_le_one)
      with True show ?thesis by (simp add: max_def)
    qed (auto simp: max_def)
    have "(\<Prod>x\<leftarrow>as. max 1 (cmod x ^ n)) = (\<Prod>a\<leftarrow>as. max 1 (cmod a)) ^ n"  
      by (induct as, auto simp: field_simps n id)
  }
  thus ?thesis unfolding f mahler_measure_poly_explicit graeffe 
    by (auto simp: o_def field_simps norm_power)
qed
end

fun drop_half :: "'a list \<Rightarrow> 'a list" where
  "drop_half (x # y # ys) = x # drop_half ys" 
| "drop_half xs = xs" 

fun alternate :: "'a list \<Rightarrow> 'a list \<times> 'a list" where
  "alternate (x # y # ys) = (case alternate ys of (evn, od) \<Rightarrow> (x # evn, y # od))" 
| "alternate xs = (xs,[])" 
  
definition poly_square_subst :: "'a :: comm_ring_1 poly \<Rightarrow> 'a poly" where
  "poly_square_subst f = poly_of_list (drop_half (coeffs f))" 
  
definition poly_even_odd :: "'a :: comm_ring_1 poly \<Rightarrow> 'a poly \<times> 'a poly" where
  "poly_even_odd f = (case alternate (coeffs f) of (evn,od) \<Rightarrow> (poly_of_list evn, poly_of_list od))" 

  
lemma poly_square_subst_coeff: "coeff (poly_square_subst f) i = coeff f (2 * i)" 
proof -
  have id: "coeff f (2 * i) = coeff (Poly (coeffs f)) (2 * i)" by simp
  obtain xs where xs: "coeffs f = xs" by auto
  show ?thesis unfolding poly_square_subst_def poly_of_list_def coeff_Poly_eq id xs
  proof (induct xs arbitrary: i rule: drop_half.induct)
    case (1 x y ys i) thus ?case by (cases i, auto)
  next
    case ("2_2" x i) thus ?case by (cases i, auto)
  qed auto
qed

lemma poly_even_odd_coeff: assumes "poly_even_odd f = (ev,od)"
  shows "coeff ev i = coeff f (2 * i)" "coeff od i = coeff f (2 * i + 1)" 
proof -
  have id: "\<And> i. coeff f i = coeff (Poly (coeffs f)) i" by simp
  obtain xs where xs: "coeffs f = xs" by auto
  from assms[unfolded poly_even_odd_def] 
  have ev_od: "ev = Poly (fst (alternate xs))" "od = Poly (snd (alternate xs))" 
    by (auto simp: xs split: prod.splits)
  have "coeff ev i = coeff f (2 * i) \<and> coeff od i = coeff f (2 * i + 1)" 
    unfolding poly_of_list_def coeff_Poly_eq id xs ev_od
  proof (induct xs arbitrary: i rule: alternate.induct)
    case (1 x y ys i) thus ?case by (cases "alternate ys"; cases i, auto)
  next
    case ("2_2" x i) thus ?case by (cases i, auto)
  qed auto
  thus "coeff ev i = coeff f (2 * i)" "coeff od i = coeff f (2 * i + 1)" by auto
qed

lemma coeff_pcompose_monom: fixes f :: "'a :: comm_ring_1 poly" 
  assumes n: "j < n" 
  shows "coeff (f \<circ>\<^sub>p monom 1 n) (n * i + j) = (if j = 0 then coeff f i else 0)"     
proof (induct f arbitrary: i)
  case (pCons a f i)
  note d = pcompose_pCons coeff_add coeff_monom_mult coeff_pCons
  show ?case 
  proof (cases i)
    case 0
    show ?thesis unfolding d 0 using n by (cases j, auto)
  next
    case (Suc ii)
    have id: "n * Suc ii + j - n = n * ii + j" using n by (simp add: diff_mult_distrib2)
    have id1: "(n \<le> n * Suc ii + j) = True" by auto
    have id2: "(case n * Suc ii + j of 0 \<Rightarrow> a | Suc x \<Rightarrow> coeff 0 x) = 0" using n
      by (cases "n * Suc ii + j", auto)
    show ?thesis unfolding d Suc id id1 id2 pCons(2) if_True by auto
  qed
qed auto


lemma coeff_pcompose_x_pow_n: fixes f :: "'a :: comm_ring_1 poly" 
  assumes n: "n \<noteq> 0" 
  shows "coeff (f \<circ>\<^sub>p monom 1 n) (n * i) = coeff f i"     
  using coeff_pcompose_monom[of 0 n f i] n by auto

lemma poly_square_subst: "poly_square_subst (f \<circ>\<^sub>p (monom 1 2)) = f" 
  by (rule poly_eqI, unfold poly_square_subst_coeff, subst coeff_pcompose_x_pow_n, auto)

lemma poly_even_odd: assumes "poly_even_odd f = (g,h)" 
  shows "f = g \<circ>\<^sub>p monom 1 2 + monom 1 1 * (h \<circ>\<^sub>p monom 1 2)" 
proof -
  note id = poly_even_odd_coeff[OF assms]
  show ?thesis
  proof (rule poly_eqI, unfold coeff_add coeff_monom_mult)
    fix n :: nat
    obtain m i where mi: "m = n div 2" "i = n mod 2" by auto
    have nmi: "n = 2 * m + i" "i < 2" "0 < (2 :: nat)" "1 < (2 :: nat)" unfolding mi by auto
    have "(2 :: nat) \<noteq> 0" by auto
    show "coeff f n = coeff (g \<circ>\<^sub>p monom 1 2) n + (if 1 \<le> n then 1 * coeff (h \<circ>\<^sub>p monom 1 2) (n - 1) else 0)" 
    proof (cases "i = 1")
      case True
      hence id1: "2 * m + i - 1 = 2 * m + 0" by auto
      show ?thesis unfolding nmi id id1 coeff_pcompose_monom[OF nmi(2)] coeff_pcompose_monom[OF nmi(3)]
        unfolding True by auto
    next
      case False
      with nmi have i0: "i = 0" by auto
      show ?thesis 
      proof (cases m)
        case (Suc k)
        hence id1: "2 * m + i - 1 = 2 * k + 1" using i0 by auto
        show ?thesis unfolding nmi id coeff_pcompose_monom[OF nmi(2)] 
          coeff_pcompose_monom[OF nmi(4)] id1 unfolding Suc i0 by auto
      next
        case 0
        show ?thesis unfolding nmi id coeff_pcompose_monom[OF nmi(2)] unfolding i0 0 by auto
      qed
    qed
  qed
qed

context
  fixes f :: "'a :: idom poly" 
begin

lemma graeffe_0: "f = smult c (\<Prod>a\<leftarrow>as. [:- a, 1:]) \<Longrightarrow> graeffe_poly c as 0 = f" 
  unfolding graeffe_poly_def by auto

lemma graeffe_recursion: assumes "graeffe_poly c as m = f"
  shows "graeffe_poly c as (Suc m) = smult ((-1)^(degree f)) (poly_square_subst (f * f \<circ>\<^sub>p [:0,-1:]))"  
proof -
  let ?g = "graeffe_poly c as m" 
  have "f * f \<circ>\<^sub>p [:0,-1:] = ?g * ?g \<circ>\<^sub>p [:0,-1:]" unfolding assms by simp
  also have "?g \<circ>\<^sub>p [:0,-1:] = smult ((- 1) ^ length as) (smult (c ^ 2 ^ m) (\<Prod>a\<leftarrow>as. [:a ^ 2 ^ m, 1:]))" 
    unfolding graeffe_poly_def
  proof (induct as)
    case (Cons a as)
    have "?case = ((smult (c ^ 2 ^ m) ([:- (a ^ 2 ^ m), 1:] \<circ>\<^sub>p [:0, - 1:] * (\<Prod>a\<leftarrow>as. [:- (a ^ 2 ^ m), 1:]) \<circ>\<^sub>p [:0, - 1:]) =
     smult (-1 * (- 1) ^ length as)
      (smult (c ^ 2 ^ m) ([: a ^ 2 ^ m, 1:] * (\<Prod>a\<leftarrow>as. [:a ^ 2 ^ m, 1:])))))" 
      unfolding list.simps prod_list.Cons pcompose_smult pcompose_mult  by simp
    also have "smult (c ^ 2 ^ m) ([:- (a ^ 2 ^ m), 1:] \<circ>\<^sub>p [:0, - 1:] * (\<Prod>a\<leftarrow>as. [:- (a ^ 2 ^ m), 1:]) \<circ>\<^sub>p [:0, - 1:])
      = smult (c ^ 2 ^ m) ((\<Prod>a\<leftarrow>as. [:- (a ^ 2 ^ m), 1:]) \<circ>\<^sub>p [:0, - 1:]) * [:- (a ^ 2 ^ m), 1:] \<circ>\<^sub>p [:0, - 1:]" 
      unfolding mult_smult_left by simp
    also have "smult (c ^ 2 ^ m) ((\<Prod>a\<leftarrow>as. [:- (a ^ 2 ^ m), 1:]) \<circ>\<^sub>p [:0, - 1:]) = 
      smult ((- 1) ^ length as) (smult (c ^ 2 ^ m) (\<Prod>a\<leftarrow>as. [:a ^ 2 ^ m, 1:]))"
      unfolding pcompose_smult[symmetric] Cons ..
    also have "[:- (a ^ 2 ^ m), 1:] \<circ>\<^sub>p [:0, - 1:] = smult (-1) [: a^2^m, 1:]" by simp
    finally have id: "?case = (smult ((- 1) ^ length as) (smult (c ^ 2 ^ m) (\<Prod>a\<leftarrow>as. [:a ^ 2 ^ m, 1:])) * smult (- 1) [:a ^ 2 ^ m, 1:] =
      smult (- 1 * (- 1) ^ length as) (smult (c ^ 2 ^ m) ([:a ^ 2 ^ m, 1:] * (\<Prod>a\<leftarrow>as. [:a ^ 2 ^ m, 1:]))))" by simp
    obtain c d where id': "(\<Prod>a\<leftarrow>as. [:a ^ 2 ^ m, 1:]) = c" "[:a ^ 2 ^ m, 1:] = d" by auto
    show ?case unfolding id unfolding id' by (simp add: ac_simps)
  qed (simp add: one_poly_def)
  finally have "f * f \<circ>\<^sub>p [:0, - 1:] =
    smult ((- 1) ^ length as * (c ^ 2 ^ m * c ^ 2 ^ m)) 
    ((\<Prod>a\<leftarrow>as. [:- (a ^ 2 ^ m), 1:]) * (\<Prod>a\<leftarrow>as. [:a ^ 2 ^ m, 1:]))" 
    unfolding graeffe_poly_def by (simp add: ac_simps)
  also have "c ^ 2 ^ m * c ^ 2 ^ m = c ^ 2 ^ (Suc m)" by (simp add: semiring_normalization_rules(36))
  also have "(\<Prod>a\<leftarrow>as. [:- (a ^ 2 ^ m), 1:]) * (\<Prod>a\<leftarrow>as. [:a ^ 2 ^ m, 1:]) = 
    (\<Prod>a\<leftarrow>as. [:- (a ^ 2 ^ (Suc m)), 1:]) \<circ>\<^sub>p monom 1 2" 
  proof (induct as)
    case (Cons a as)
    have id: "(monom 1 2 :: 'a poly) = [:0,0,1:]" 
      by (metis monom_altdef pCons_0_as_mult power2_eq_square smult_1_left)
    have "(\<Prod>a\<leftarrow>a # as. [:- (a ^ 2 ^ m), 1:]) * (\<Prod>a\<leftarrow>a # as. [:a ^ 2 ^ m, 1:])
      = ([:- (a ^ 2 ^ m), 1:] * [: a ^ 2 ^ m, 1:]) * ((\<Prod>a\<leftarrow> as. [:- (a ^ 2 ^ m), 1:]) * (\<Prod>a\<leftarrow> as. [:a ^ 2 ^ m, 1:]))" 
        (is "_ = ?a * ?b")
      unfolding list.simps prod_list.Cons by (simp only: ac_simps)
    also have "?b = (\<Prod>a\<leftarrow>as. [:- (a ^ 2 ^ Suc m), 1:]) \<circ>\<^sub>p monom 1 2" unfolding Cons by simp
    also have "?a = [: - (a ^ 2 ^ (Suc m)), 0 , 1:]" by (simp add: semiring_normalization_rules(36))
    also have "\<dots> = [: - (a ^ 2 ^ (Suc m)), 1:] \<circ>\<^sub>p monom 1 2" by (simp add: id)
    also have "[: - (a ^ 2 ^ (Suc m)), 1:] \<circ>\<^sub>p monom 1 2 * (\<Prod>a\<leftarrow>as. [:- (a ^ 2 ^ Suc m), 1:]) \<circ>\<^sub>p monom 1 2 =
      (\<Prod>a\<leftarrow>a # as. [:- (a ^ 2 ^ Suc m), 1:]) \<circ>\<^sub>p monom 1 2" unfolding pcompose_mult[symmetric] by simp
    finally show ?case .
  qed (simp add: one_poly_def)
  finally have "f * f \<circ>\<^sub>p [:0, - 1:] = (smult ((- 1) ^ length as) (graeffe_poly c as (Suc m)) \<circ>\<^sub>p monom 1 2)" 
    unfolding graeffe_poly_def pcompose_smult by simp
  from arg_cong[OF this, of "\<lambda> f. smult ((- 1) ^ length as) (poly_square_subst f)", unfolded poly_square_subst]
  have "graeffe_poly c as (Suc m) = smult ((- 1) ^ length as) (poly_square_subst (f * f \<circ>\<^sub>p [:0, - 1:]))" by simp
  also have "\<dots> = smult ((- 1) ^ degree f) (poly_square_subst (f * f \<circ>\<^sub>p [:0, - 1:]))" 
  proof (cases "f = 0")
    case True
    thus ?thesis by (auto simp: poly_square_subst_def)
  next
    case False
    with assms have c0: "c \<noteq> 0" unfolding graeffe_poly_def by auto
    from arg_cong[OF assms, of degree] 
    have "degree f = degree (smult (c ^ 2 ^ m) (\<Prod>a\<leftarrow>as. [:- (a ^ 2 ^ m), 1:]))" unfolding graeffe_poly_def by auto
    also have "\<dots> = degree (\<Prod>a\<leftarrow>as. [:- (a ^ 2 ^ m), 1:])" unfolding degree_smult_eq using c0 by auto
    also have "\<dots> = length as" unfolding degree_linear_factors by simp
    finally show ?thesis by simp
  qed
  finally show ?thesis .
qed
end

definition graeffe_one_step :: "'a \<Rightarrow> 'a :: idom poly \<Rightarrow> 'a poly" where 
  "graeffe_one_step c f = smult c (poly_square_subst (f * f \<circ>\<^sub>p [:0,-1:]))" 
  
lemma graeffe_one_step_code: fixes c :: "'a :: idom" 
  shows "graeffe_one_step c f = (case poly_even_odd f of (g,h)
  \<Rightarrow> smult c (g * g - monom 1 1 * h * h))" 
proof -
  obtain g h where eo: "poly_even_odd f = (g,h)" by force
  from poly_even_odd[OF eo] have fgh: "f = g \<circ>\<^sub>p monom 1 2 + monom 1 1 * h \<circ>\<^sub>p monom 1 2 " by auto 
  have m2: "monom (1 :: 'a) 2 = [:0,0,1:]" "monom (1 :: 'a) 1 = [:0,1:]" 
    unfolding coeffs_eq_iff coeffs_monom by auto
  show ?thesis unfolding eo split graeffe_one_step_def
  proof (rule arg_cong[of _ _ "smult c"])
    let ?g = "g \<circ>\<^sub>p monom 1 2" 
    let ?h = "h \<circ>\<^sub>p monom 1 2" 
    let ?x = "monom (1 :: 'a) 1"
    have 2: "2 = Suc (Suc 0)" by simp
    have "f * f \<circ>\<^sub>p [:0, - 1:] = (g \<circ>\<^sub>p monom 1 2 + monom 1 1 * h \<circ>\<^sub>p monom 1 2) * 
      (g \<circ>\<^sub>p monom 1 2 + monom 1 1 * h \<circ>\<^sub>p monom 1 2) \<circ>\<^sub>p [:0, - 1:]" unfolding fgh by simp
    also have "(g \<circ>\<^sub>p monom 1 2 + monom 1 1 * h \<circ>\<^sub>p monom 1 2) \<circ>\<^sub>p [:0, - 1:]
      = g \<circ>\<^sub>p (monom 1 2 \<circ>\<^sub>p [:0, - 1:]) + monom 1 1 \<circ>\<^sub>p [:0, - 1:] * h \<circ>\<^sub>p (monom 1 2 \<circ>\<^sub>p [:0, - 1:])" 
      unfolding pcompose_add pcompose_mult pcompose_assoc by simp
    also have "monom (1 :: 'a) 2 \<circ>\<^sub>p [:0, - 1:] = monom 1 2" unfolding m2 by auto
    also have "?x \<circ>\<^sub>p [:0, - 1:] = [:0, -1:]" unfolding m2 by auto
    also have "[:0, - 1:] * h \<circ>\<^sub>p monom 1 2 = (-?x) * ?h" unfolding m2 by simp
    also have "(?g + ?x * ?h) * (?g + (- ?x) * ?h) = (?g * ?g - (?x * ?x) * ?h * ?h)"       
      by (auto simp: field_simps)
    also have "?x * ?x = ?x \<circ>\<^sub>p monom 1 2" unfolding mult_monom by (insert m2, simp add: 2)
    also have "(?g * ?g - \<dots> * ?h * ?h) = (g * g - ?x * h * h) \<circ>\<^sub>p monom 1 2" 
      unfolding pcompose_diff pcompose_mult by auto
    finally have "poly_square_subst (f * f \<circ>\<^sub>p [:0, - 1:]) 
      = poly_square_subst ((g * g - ?x * h * h) \<circ>\<^sub>p monom 1 2)" by simp
    also have "\<dots> = g * g - ?x * h * h" unfolding poly_square_subst by simp
    finally show "poly_square_subst (f * f \<circ>\<^sub>p [:0, - 1:]) = g * g - ?x * h * h" .
  qed
qed

fun graeffe_poly_impl_main :: "'a \<Rightarrow> 'a :: idom poly \<Rightarrow> nat \<Rightarrow> 'a poly" where
  "graeffe_poly_impl_main c f 0 = f" 
| "graeffe_poly_impl_main c f (Suc m) = graeffe_one_step c (graeffe_poly_impl_main c f m)" 
  
lemma graeffe_poly_impl_main: assumes "f = smult c (\<Prod>a\<leftarrow>as. [:- a, 1:])"
  shows "graeffe_poly_impl_main ((-1)^degree f) f m = graeffe_poly c as m"
proof (induct m)
  case 0
  show ?case using graeffe_0[OF assms] by simp
next
  case (Suc m)
  have [simp]: "degree (graeffe_poly c as m) = degree f" unfolding graeffe_poly_def degree_smult_eq assms
    degree_linear_factors by auto    
  from arg_cong[OF Suc, of degree]  
  show ?case unfolding graeffe_recursion[OF Suc[symmetric]]
    by (simp add: graeffe_one_step_def)
qed

definition graeffe_poly_impl :: "'a :: idom poly \<Rightarrow> nat \<Rightarrow> 'a poly" where
  "graeffe_poly_impl f = graeffe_poly_impl_main ((-1)^(degree f)) f" 

lemma graeffe_poly_impl: assumes "f = smult c (\<Prod>a\<leftarrow>as. [:- a, 1:])"
  shows "graeffe_poly_impl f m = graeffe_poly c as m"
  using graeffe_poly_impl_main[OF assms] unfolding graeffe_poly_impl_def .

lemma drop_half_map: "drop_half (map f xs) = map f (drop_half xs)" 
  by (induct xs rule: drop_half.induct, auto)

lemma (in inj_ring_hom) map_poly_poly_square_subst: 
  "map_poly hom (poly_square_subst f) = poly_square_subst (map_poly hom f)" 
  unfolding poly_square_subst_def coeffs_map_poly drop_half_map poly_of_list_def
  by (rule poly_eqI, auto simp: nth_default_map_eq)

(* TODO: move *)
lemma (in semiring_hom) map_poly_pcompose: 
  "map_poly hom (f \<circ>\<^sub>p g) = map_poly hom f \<circ>\<^sub>p map_poly hom g" 
  by (induct f arbitrary: g, auto)

locale inj_idom_hom = idom_hom + inj_ring_hom
begin

lemma graeffe_poly_impl_hom: 
  "map_poly hom (graeffe_poly_impl f m) = graeffe_poly_impl (map_poly hom f) m"
proof -
  let ?h = "map_poly hom" 
  obtain c where c: "(((- 1) ^ degree f) :: 'a) = c" by auto
  have c': "(((- 1) ^ degree f) :: 'b) = hom c" unfolding c[symmetric] by simp
  show ?thesis unfolding graeffe_poly_impl_def degree_map_poly c c'
  proof (induct m arbitrary: f)
    case (Suc m f)
    obtain g where g: "(graeffe_poly_impl_main c f m) = g" by auto
    show ?case unfolding graeffe_poly_impl_main.simps graeffe_one_step_def Suc[symmetric] g map_poly_smult
      map_poly_poly_square_subst map_poly_mult map_poly_pcompose by simp
  qed simp
qed
end

lemma graeffe_poly_impl_mahler: "mahler_measure (graeffe_poly_impl f m) = mahler_measure f ^ 2 ^ m" 
proof -
  let ?c = "complex_of_int" 
  let ?cc = "map_poly ?c" 
  let ?f = "?cc f" 
  note eq = complex_roots(1)[of ?f]
  interpret inj_idom_hom complex_of_int by (standard, auto)
  show ?thesis  
    unfolding mahler_measure_def mahler_graeffe[OF eq[symmetric], symmetric]
     graeffe_poly_impl[OF eq[symmetric], symmetric] by (simp add: graeffe_poly_impl_hom)
qed

definition mahler_landau_graeffe_approximation :: "nat \<Rightarrow> int poly \<Rightarrow> int" where
  "mahler_landau_graeffe_approximation k f = (let kk = 2^(Suc k);
     no = sum_list (map (\<lambda> a. a * a) (coeffs f))
    in root_int_ceiling kk (no))" 
  
lemma mahler_landau_graeffe_approximation: 
  assumes g: "g = graeffe_poly_impl f k" 
  shows "\<lceil>mahler_measure f\<rceil> \<le> mahler_landau_graeffe_approximation k g"
proof -
  show ?thesis
    unfolding mahler_landau_graeffe_approximation_def Let_def root_int_ceiling of_int_mult 
  proof (rule ceiling_mono)
    have "mahler_measure f = root (2^k) (mahler_measure f ^ (2^k))" 
      by (simp add: real_root_power_cancel mahler_measure_ge_0) 
    also have "\<dots> = root (2^k) (mahler_measure g)" 
      unfolding graeffe_poly_impl_mahler g by simp
    also have "\<dots> = root (2^k) (root 2 (((mahler_measure g)^2)))" 
      by (simp add: real_root_power_cancel mahler_measure_ge_0) 
    also have "\<dots> = root (2^Suc k) (((mahler_measure g)^2))"
      by (metis power_Suc2 real_root_mult_exp)
    also have "\<dots> \<le> root (2 ^ Suc k) (real_of_int (\<Sum>a\<leftarrow>coeffs g. a * a))" 
    proof (rule real_root_le_mono, force)
      have square_mono: "0 \<le> (x :: real) \<Longrightarrow> x \<le> y \<Longrightarrow> x * x \<le> y * y" for x y
        by (simp add: mult_mono')
      obtain gs where gs: "coeffs g = gs" by auto
      have "(mahler_measure g)\<^sup>2 \<le> real_of_int \<bar>\<Sum>a\<leftarrow>coeffs g. a * a\<bar>" 
        using square_mono[OF mahler_measure_ge_0 Landau_inequality[of "of_int_poly g", folded mahler_measure_def]]
        by (auto simp: power2_eq_square coeffs_map_poly o_def)
      also have "\<bar>\<Sum>a\<leftarrow>coeffs g. a * a\<bar> = (\<Sum>a\<leftarrow>coeffs g. a * a)" unfolding gs
        by (induct gs, auto)
      finally show "(mahler_measure g)\<^sup>2 \<le> real_of_int (\<Sum>a\<leftarrow>coeffs g. a * a)" .
    qed
    finally show "mahler_measure f \<le> root (2 ^ Suc k) (real_of_int (\<Sum>a\<leftarrow>coeffs g. a * a))" .
  qed 
qed

context 
  fixes bnd :: nat
begin
function mahler_approximation_main :: "int \<Rightarrow> int poly \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
  "mahler_approximation_main c g mm k = (let mmm = mahler_landau_graeffe_approximation k g;
     new_mm = (if k = 0 then mmm else min mm mmm)
     in (if k \<ge> bnd then new_mm else 
     (* abort after \<open>bnd\<close> iterations of Graeffe transformation *)
      mahler_approximation_main c (graeffe_one_step c g) new_mm (Suc k)))" 
  by pat_completeness auto

termination by (relation "measure (\<lambda> (c,f,mm,k). Suc bnd - k)", auto)
declare mahler_approximation_main.simps[simp del]

lemma mahler_approximation_main: assumes "k \<noteq> 0 \<Longrightarrow> \<lceil>mahler_measure f\<rceil> \<le> mm"
    and "c = (-1)^(degree f)" 
    and "g = graeffe_poly_impl_main c f k" 
  shows "\<lceil>mahler_measure f\<rceil> \<le> mahler_approximation_main c g mm k" 
  using assms
proof (induct c g mm k rule: mahler_approximation_main.induct)
  case (1 c g mm k)
  let ?mf = "\<lceil>mahler_measure f\<rceil>" 
  note g = 1(4)
  note c = 1(3)
  note mm = 1(2)
  note IH = 1(1)
  note mahl = mahler_approximation_main.simps[of c g mm k]
  define mmm where "mmm = mahler_landau_graeffe_approximation k g" 
  define new_mm where "new_mm = (if k = 0 then mmm else min mm mmm)" 
  let ?cond = "bnd \<le> k" 
  have id: "mahler_approximation_main c g mm k = (if ?cond then new_mm
        else mahler_approximation_main c (graeffe_one_step c g) new_mm (Suc k))" 
    unfolding mahl mmm_def[symmetric] Let_def new_mm_def[symmetric] by simp
  have gg: "g = (graeffe_poly_impl f k)" unfolding g graeffe_poly_impl_def c ..
  from mahler_landau_graeffe_approximation[OF gg, folded mmm_def]
  have mmm: "?mf \<le> mmm" .
  with mm have new_mm: "?mf \<le> new_mm" unfolding new_mm_def by auto
  show ?case
  proof (cases ?cond)
    case True
    show ?thesis unfolding id using True new_mm by auto
  next
    case False
    hence id: "mahler_approximation_main c g mm k = 
      mahler_approximation_main c (graeffe_one_step c g) new_mm (Suc k)" 
      unfolding id by auto
    have id': "graeffe_one_step c g = graeffe_poly_impl_main c f (Suc k)" 
      unfolding g by simp
    from IH[OF mmm_def new_mm_def False new_mm c id']
    show ?thesis unfolding id .
  qed
qed 

definition mahler_approximation :: "int poly \<Rightarrow> int" where
  "mahler_approximation f = mahler_approximation_main ((-1)^(degree f)) f (-1) 0" 

lemma mahler_approximation: "\<lceil>mahler_measure f\<rceil> \<le> mahler_approximation f"
  unfolding mahler_approximation_def
  by (rule mahler_approximation_main, auto)
end
end
