(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsection \<open>The Mignotte Bound\<close>
theory Factor_Bound
imports 
  "../Sqrt_Babylonian/Sqrt_Babylonian"
  Poly_Mod_Finite_Field_Record_Based (* stuff about polynomials *)
  "../Polynomial_Factorization/Fundamental_Theorem_Algebra_Factorized"
  "../Polynomial_Factorization/Missing_Multiset"
begin

lemma binomial_mono_left: "n \<le> N \<Longrightarrow> n choose k \<le> N choose k" 
proof (induct n arbitrary: k N)
  case (0 k N)
  thus ?case by (cases k, auto)
next
  case (Suc n k N) note IH = this
  show ?case
  proof (cases k)
    case 0
    thus ?thesis by auto
  next
    case (Suc kk)
    from IH obtain NN where N: "N = Suc NN" and le: "n \<le> NN" by (cases N, auto)     
    show ?thesis unfolding N Suc using IH(1)[OF le] 
      by (simp add: add_le_mono)
  qed
qed

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


context begin

abbreviation complex_of_int::"int => complex" where
  "complex_of_int \<equiv> of_int"
interpretation ia: semiring_hom of_int by(unfold_locales,auto)
interpretation ib: semiring_hom of_nat by(unfold_locales,auto)
interpretation i1: inj_semiring_hom complex_of_int by(unfold_locales,auto)
interpretation i2: inj_semiring_hom complex_of_real by(unfold_locales,auto)
interpretation i3: inj_semiring_hom real_of_int by(unfold_locales,auto)
interpretation i4: inj_semiring_hom real by(unfold_locales,auto)
(* Question: how can I get the simp rules of several locales at once? *)

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
  using complex_roots[of "map_poly of_int p"] unfolding complex_roots_int_def 
  by (simp_all add: i1.map_poly_preservers)

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

definition coeff_int where "coeff_int p i = (if i<0 then 0 else coeff p (nat i))"
lemma coeff_int[simp]: "coeff_int p n = coeff p n"  unfolding coeff_int_def by auto

lemma coeff_int_oprs[simp]:
  "coeff_int (a - b) i = coeff_int a i - coeff_int b i"
  "coeff_int (pCons 0 b) i = coeff_int b (i - 1)"
  "coeff_int (smult v r) i = v * coeff_int r i"
  by(auto simp:Nitpick.case_nat_unfold coeff_int_def coeff_pCons nat_diff_distrib')

definition choose_int where "choose_int m n = (if n < 0 then 0 else m choose (nat n))"

lemma choose_int[simp]: "choose_int p n = p choose n" unfolding choose_int_def by auto

lemma choose_int_suc[simp]:
  "choose_int (Suc n) i = choose_int n (i-1) + choose_int n i"
proof(cases "nat i")
  case 0 thus ?thesis by (simp add:choose_int_def) next
  case (Suc v) hence "nat (i - 1) = v" "i\<noteq>0" by simp_all
    thus ?thesis unfolding choose_int_def Suc by simp
qed

lemma sum_le_1_prod: assumes d: "1 \<le> d" and c: "1 \<le> c"
  shows "c + d \<le> 1 + c * (d :: real)"
proof -
  from d c have "(c - 1) * (d - 1) \<ge> 0" by auto
  thus ?thesis by (auto simp: field_simps)
qed

lemma mignotte_helper_coeff_int: "cmod (coeff_int (\<Prod>a\<leftarrow>lst. [:- a, 1:]) i)
    \<le> choose_int (length lst - 1) i * (\<Prod>a\<leftarrow>lst. (max 1 (cmod a))) 
    + choose_int (length lst - 1) (i - 1)"
proof(induct lst arbitrary:i)
  case Nil thus ?case by (auto simp:coeff_int_def choose_int_def)
  case (Cons v xs i)
  show ?case
  proof (cases "xs = []")
    case True
    show ?thesis unfolding True 
    proof (auto simp: coeff_int_def choose_int_def, cases "nat i", auto, cases "nat (i - 1)", auto, goal_cases)
      case (1 n nn)
      then obtain k where n: "n = Suc k" by (cases n, auto)
      thus ?case by auto
    qed
  next
    case False
    hence id: "length (v # xs) - 1 = Suc (length xs - 1)" by auto
    have id': "choose_int (length xs) i = choose_int (Suc (length xs - 1)) i" for i
      using False by (cases xs, auto)
    let ?r = "(\<Prod>a\<leftarrow>xs. [:- a, 1:])"
    let ?mv = "(\<Prod>a\<leftarrow>xs. (max 1 (cmod a)))"
    let ?c1 = "real (choose_int (length xs - 1) (i - 1 - 1))" 
    let ?c2 = "real (choose_int (length (v # xs) - 1) i - choose_int (length xs - 1) i)" 
    let "?m xs n" = "choose_int (length xs - 1) n * (\<Prod>a\<leftarrow>xs. (max 1 (cmod a)))"
    have le1:"1 \<le> max 1 (cmod v)" by auto
    have le2:"cmod v \<le> max 1 (cmod v)" by auto
    have mv_ge_1:"1 \<le> ?mv" by (rule prod_list_ge1, auto)
    obtain a b c d where abcd : 
      "a = real (choose_int (length xs - 1) i)" 
      "b = real (choose_int (length xs - 1) (i - 1))" 
      "c = (\<Prod>a\<leftarrow>xs. max 1 (cmod a))" 
      "d = cmod v" by auto
    {
      have c1: "c \<ge> 1" unfolding abcd by (rule mv_ge_1)
      have b: "b = 0 \<or> b \<ge> 1" unfolding abcd by auto
      have a: "a = 0 \<or> a \<ge> 1" unfolding abcd by auto
      hence a0: "a \<ge> 0" by auto
      have acd: "a * (c * d) \<le> a * (c * max 1 d)" using a0 c1
        by (simp add: mult_left_mono)
      from b have "b * (c + d) \<le> b * (1  + (c * max 1 d))" 
      proof 
        assume "b \<ge> 1" 
        hence "?thesis = (c + d \<le> 1 + c * max 1 d)" by simp
        also have \<dots>
        proof (cases "d \<ge> 1")
          case False
          hence id: "max 1 d = 1" by simp
          show ?thesis using False unfolding id by simp
        next
          case True
          hence id: "max 1 d = d" by simp
          show ?thesis using True c1 unfolding id by (rule sum_le_1_prod)
        qed
        finally show ?thesis .
      qed auto
      with acd have "b * c + (b * d + a * (c * d)) \<le> b + (a * (c * max 1 d) + b * (c * max 1 d))" 
        by (auto simp: field_simps)
    } note abcd_main = this      
    have "cmod (coeff_int ([:- v, 1:] * ?r) i) \<le> cmod (coeff_int ?r (i - 1)) + cmod (coeff_int (smult v ?r) i)"
      using norm_triangle_ineq4 by auto
    also have "\<dots> \<le> ?m xs (i - 1) + (choose_int (length xs - 1) (i - 1 - 1)) + cmod (coeff_int (smult v ?r) i)" 
      using Cons[of "i-1"] by auto
    also have "choose_int (length xs - 1) (i - 1) = choose_int (length (v # xs) - 1) i - choose_int (length xs - 1) i" 
      unfolding id choose_int_suc by auto
    also have "?c2 * (\<Prod>a\<leftarrow>xs. max 1 (cmod a)) + ?c1 +
       cmod (coeff_int (smult v (\<Prod>a\<leftarrow>xs. [:- a, 1:])) i) \<le> 
       ?c2 * (\<Prod>a\<leftarrow>xs. max 1 (cmod a)) + ?c1 + cmod v * (
         real (choose_int (length xs - 1) i) * (\<Prod>a\<leftarrow>xs. max 1 (cmod a)) + 
         real (choose_int (length xs - 1) (i - 1)))"
      using mult_mono'[OF order_refl Cons, of "cmod v" i, simplified] by (auto simp: norm_mult)
    also have "\<dots> \<le> ?m (v # xs) i + (choose_int (length xs) (i - 1))" using abcd_main[unfolded abcd]
      by (simp add: field_simps id')
    finally show ?thesis by simp
  qed
qed

lemma mignotte_helper_coeff_int': "cmod (coeff_int (\<Prod>a\<leftarrow>lst. [:- a, 1:]) i)
    \<le> ((length lst - 1) choose i) * (\<Prod>a\<leftarrow>lst. (max 1 (cmod a))) 
    + ((length lst - 1) choose (nat (i - 1)))"
  by (rule order.trans[OF mignotte_helper_coeff_int], auto simp: choose_int_def)

lemma mignotte_helper_coeff:
  "cmod (coeff h i) \<le> (degree h - 1 choose i) * mahler_measure_poly h 
      + (degree h - 1 choose (i - 1)) * cmod (lead_coeff h)"
proof -
  let ?r = "complex_roots_complex h"
  have "cmod (coeff h i) = cmod (coeff (smult (lead_coeff h) (\<Prod>a\<leftarrow>?r. [:- a, 1:])) i)"
    unfolding complex_roots by auto
  also have "\<dots> = cmod (lead_coeff h) * cmod (coeff (\<Prod>a\<leftarrow>?r. [:- a, 1:]) i)" by(simp add:norm_mult)
  also have "\<dots> \<le> cmod (lead_coeff h) * ((degree h - 1 choose i) * mahler_measure_monic h + ((degree h - 1) choose nat (int i - 1)))"    
    unfolding mahler_measure_monic_def
    by (rule mult_left_mono, insert mignotte_helper_coeff_int'[of ?r i], auto)
  also have "\<dots> = (degree h - 1 choose i) * mahler_measure_poly h + cmod (lead_coeff h) * ((degree h - 1) choose nat (int i - 1))" 
    unfolding mahler_measure_poly_via_monic by (simp add: field_simps)
  also have "nat (int i - 1) = i - 1" by (cases i, auto)
  finally show ?thesis by (simp add: ac_simps)
qed

lemma cmod_through_lead_coeff[simp]:
  "cmod (lead_coeff (of_int_poly h)) = abs (lead_coeff h)"
  by (auto simp: i1.map_poly_preservers(1)[symmetric])

lemma mignotte_coeff_helper:
  "abs (coeff h i) \<le> 
   (degree h - 1 choose i) * mahler_measure h +
   (degree h - 1 choose (i - 1)) * abs (lead_coeff h)"
  unfolding mahler_measure_def
  using mignotte_helper_coeff[of "of_int_poly h" i] 
  by auto

lemma mahler_measure_poly_ge_1:
  assumes "h\<noteq>0"
  shows "(1::real) \<le> mahler_measure h"
proof -
  from assms have "cmod (lead_coeff (map_poly complex_of_int h)) > 0" by simp
  hence "cmod (lead_coeff (map_poly complex_of_int h)) \<ge> 1"
    by(cases "abs (lead_coeff h)";auto)
  from mult_mono[OF this mahler_measure_monic_ge_1 norm_ge_zero]
  show ?thesis unfolding mahler_measure_def mahler_measure_poly_via_monic
    by auto
qed

lemma choose_approx: "n \<le> N \<Longrightarrow> n choose k \<le> N choose (N div 2)" 
  by (rule order.trans[OF binomial_mono_left binomial_maximum])

text \<open>For estimating Mahler's measure, we use Landau's approximation.
  This should be improved as soon as better complex root estimation algorithms have been formalized.\<close>

definition mahler_approximation :: "nat \<Rightarrow> int poly \<Rightarrow> int" where
  "mahler_approximation c f = sqrt_int_floor (c^2 * sum_list (map (\<lambda> a. a * a) (coeffs f)))" 

lemma mahler_approximation: "\<lfloor>real d * mahler_measure f\<rfloor> \<le> mahler_approximation d f" 
proof -
  have landau: "real d * mahler_measure f \<le> sqrt (d^2 * norm2 (of_int_poly f))" 
    using mult_left_mono[OF Landau_inequality[of "of_int_poly f"]] 
    unfolding mahler_measure_def real_sqrt_mult by simp
  from floor_mono[OF landau] show ?thesis unfolding mahler_approximation_def 
    by (auto simp: power2_eq_square coeffs_map_poly o_def)
qed

text \<open>For Mignotte's factor bound, we currently do not support queries for individual coefficients,
  as we do not have a combined factor bound algorithm.\<close>

definition mignotte_bound :: "int poly \<Rightarrow> nat \<Rightarrow> int" where
  "mignotte_bound f d = (let d' = d - 1; d2 = d' div 2; binom = (d' choose d2) in
     mahler_approximation binom f + binom * abs (lead_coeff f))" 

lemma mignotte_bound: fixes mm :: "nat \<Rightarrow> int poly \<Rightarrow> int" 
    assumes "f \<noteq> 0" "g dvd f" "degree g \<le> n"
  shows "\<bar>coeff g k\<bar> \<le> mignotte_bound f n"  
proof-
  obtain h where gh:"g * h = f" using assms by (metis dvdE)
  have nz:"g\<noteq>0" "h\<noteq>0" using gh assms(1) by auto
  have g1:"(1::real) \<le> mahler_measure h" using mahler_measure_poly_ge_1 gh assms(1) by auto
  have g0:"\<And> h. 0 \<le> mahler_measure h" unfolding mahler_measure_def mahler_measure_poly_via_monic
    by (simp add: mahler_measure_monic_ge_0)
  let ?n = "(n - 1) choose ((n - 1) div 2)" 
  have to_n: "(degree g - 1 choose k) \<le> real ?n" for k
    using choose_approx[of "degree g - 1" "n - 1" k] assms(3) by auto
  have "\<bar>coeff g k\<bar> \<le> (degree g - 1 choose k) * mahler_measure g
    + real (degree g - 1 choose (k - 1)) * \<bar>lead_coeff g\<bar>" using mignotte_coeff_helper[of g k] by simp
  also have "\<dots> \<le> ?n * mahler_measure f + real ?n * \<bar>lead_coeff f\<bar>"
  proof (rule add_mono[OF mult_mono[OF to_n] mult_mono[OF to_n]])
    have "mahler_measure g  \<le> mahler_measure g * mahler_measure h" using g1 g0[of g]
      using mahler_measure_poly_ge_1 nz(1) by force
    thus "mahler_measure g \<le> mahler_measure f" 
      using measure_eq_prod[of "of_int_poly g" "of_int_poly h"]
      unfolding mahler_measure_def gh[symmetric] by auto
    have *: "lead_coeff f = lead_coeff g * lead_coeff h" 
      unfolding arg_cong[OF gh, of lead_coeff, symmetric] by (rule lead_coeff_mult)
    have "\<bar>lead_coeff h\<bar> \<noteq> 0" using nz(2) by auto
    hence lh: "\<bar>lead_coeff h\<bar> \<ge> 1" by linarith
    have "\<bar>lead_coeff f\<bar> = \<bar>lead_coeff g\<bar> * \<bar>lead_coeff h\<bar>" unfolding * by (rule abs_mult)
    also have "\<dots> \<ge> \<bar>lead_coeff g\<bar> * 1" 
      by (rule mult_mono, insert lh, auto)
    finally have "\<bar>lead_coeff g\<bar> \<le> \<bar>lead_coeff f\<bar>" by simp
    thus "real_of_int \<bar>lead_coeff g\<bar> \<le> real_of_int \<bar>lead_coeff f\<bar>" by simp
  qed (auto simp: g0)
  finally have "\<bar>coeff g k\<bar> \<le> ?n * mahler_measure f + real_of_int (?n * \<bar>lead_coeff f\<bar>)" by simp
  from floor_mono[OF this, folded floor_add_int]
  have "\<bar>coeff g k\<bar> \<le> floor (?n * mahler_measure f) + ?n * \<bar>lead_coeff f\<bar>" by linarith
  thus ?thesis unfolding mignotte_bound_def Let_def using mahler_approximation[of ?n f] by auto
qed


text \<open>As indicated before, at the moment the only available factor bound is Mignotte's one.
  As future work one might use a combined bound.\<close>

definition factor_bound :: "int poly \<Rightarrow> nat \<Rightarrow> int" where
  "factor_bound = mignotte_bound"

lemma factor_bound: assumes "f \<noteq> 0" "g dvd f" "degree g \<le> n"
  shows "\<bar>coeff g k\<bar> \<le> factor_bound f n"
  unfolding factor_bound_def by (rule mignotte_bound[OF assms])
end
end