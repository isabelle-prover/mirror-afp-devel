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
lemma add_induct_gen_le:
  assumes "\<And> a r. f (h a + r :: 'a :: {comm_monoid_add}) \<le> (f (g a + r)::'b::linorder)"
  shows "f (\<Sum>v\<leftarrow>lst. h v) \<le> f (\<Sum>v\<leftarrow>lst. g v)"
proof - let "?P x y" = "f x \<le> f y"
  show ?thesis using comm_monoid_add_class.sum_list.induct_gen_abs[of _ ?P,OF assms,simplified]
    order.trans by fastforce
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


text \<open>We exclude prime number 2 since some algorithms later on require odd primes.\<close>

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

lemma Least_le2:
assumes "\<forall> v. P1 (v::nat) \<longrightarrow> P2 v" "\<exists> v'. P1 v'"
shows "Least P1 \<ge> Least P2"
proof -
  have "P2 (Least P1)" using assms LeastI2 by blast
  thus ?thesis using Least_le by blast
qed

definition l2norm_list :: "int list \<Rightarrow> int" where
  "l2norm_list lst = \<lfloor>sqrt (sum_list (map (\<lambda> a. a * a) lst))\<rfloor>"

abbreviation l2norm :: "int poly \<Rightarrow> int" where
  "l2norm p \<equiv> l2norm_list (coeffs p)"

abbreviation "norm2 p \<equiv> \<Sum>a\<leftarrow>coeffs p. (cmod a)\<^sup>2" (* the square of the Euclidean/l2-norm *)

abbreviation l2norm_complex where
  "l2norm_complex p \<equiv> sqrt (norm2 p)"

abbreviation height :: "int poly \<Rightarrow> int" where
  "height p \<equiv> max_list (map (nat \<circ> abs) (coeffs p))"

lemma sum_of_squares_pos : "(\<Sum>a::'a::linordered_idom\<leftarrow>lst. a * a) \<ge> 0" by(induct lst;auto)

lemma l2norm_pos : "l2norm p \<ge> 0"
  using linordered_idom_class.of_int_nonneg[OF sum_of_squares_pos[of "coeffs p"]]
  unfolding l2norm_list_def by auto

lemma my_sqrt_sumsq: "abs x \<le> sqrt (real_of_int(x * x) + abs y)"
by (simp add: power2_eq_square real_le_rsqrt)

lemma my_sqrt_sumsq2: "sqrt y \<le> sqrt (real_of_int(x * x) + abs y)"
by (metis add.commute le_add_same_cancel1 of_int_mult power2_eq_square real_le_rsqrt real_sqrt_mult_self zero_le_square)

lemma ispos_unfold:"abs (real_of_int (\<Sum>a\<leftarrow>xs. a * a)) = real_of_int (\<Sum>a\<leftarrow>xs. a * a)"
  using sum_of_squares_pos abs_of_nonneg of_int_0_le_iff by blast

lemma height_le_norm2_list: "max_list (map (nat \<circ> abs) lst) \<le>  \<lfloor>sqrt (real_of_int (\<Sum>a\<leftarrow>lst. a * a))\<rfloor>"
  (is "int (?maxl lst) \<le> \<lfloor>?sqrt lst\<rfloor>")
unfolding le_floor_iff Int.ring_1_class.of_int_of_nat_eq
proof(induct lst)
  case (Cons a xs)
  consider (a) "real (?maxl (a # xs)) = abs a" | (b) "?maxl (a # xs) = ?maxl xs" by fastforce
  thus ?case proof(cases)
    case a
      from my_sqrt_sumsq[of a "real_of_int (\<Sum>a\<leftarrow>xs. a * a)"]
      show ?thesis unfolding ispos_unfold a by simp next
    case b
      from my_sqrt_sumsq2[of "real_of_int (\<Sum>a\<leftarrow>xs. a * a)" a] Cons
      have "(max_list (map (nat \<circ> abs) xs)) \<le> sqrt ((a * a) + real_of_int (\<Sum>a\<leftarrow>xs. a * a))"
        unfolding ispos_unfold by linarith
      thus ?thesis unfolding b by simp
  qed
qed auto

lemma triangle_ineq: assumes "b \<ge> 0"
  shows "\<lfloor>sqrt (a * a + b)\<rfloor> \<le> abs a + \<lfloor>sqrt b\<rfloor>"
proof -
  have "sqrt (a * a + b) \<le> abs a + sqrt b" using sqrt_add_le_add_sqrt[of "a*a",OF _ assms] by simp
  thus ?thesis by (metis add.commute floor_add_int floor_mono of_int_power power2_eq_square)
qed

lemma height_le_norm2 : (* Remark 11, eqn 85.1 *)
  "height g \<le> l2norm g"
unfolding l2norm_list_def using height_le_norm2_list by auto

lemma norm2_le_norm1 : (* Remark 11, eqn 85.2 *)
  "l2norm g \<le> sum_list (map abs (coeffs g))"
proof - {fix lst
  have "l2norm_list lst \<le> sum_list (map abs lst)" unfolding l2norm_list_def proof(induct lst)
    case Nil thus ?case by auto next
    case (Cons x xs)
      from triangle_ineq[OF sum_of_squares_pos[of "map real_of_int xs"],simplified,of "x"] 
      have "\<lfloor>sqrt (real_of_int x * real_of_int x + (\<Sum>x\<leftarrow>xs. real_of_int x * real_of_int x))\<rfloor> \<le>
            \<bar>x\<bar> + \<lfloor>sqrt (real_of_int (\<Sum>a\<leftarrow>xs. a * a))\<rfloor>"
        by (simp add: o_def)
      also have "\<dots> \<le> \<bar>x\<bar> + sum_list (map abs xs)" using Cons by simp
      finally show ?case by (simp add: o_def)
  qed
  }
  thus ?thesis by auto
qed

lemma height_le_norm1: "height g \<le> sum_list (map abs (coeffs g))"
  using order_trans[OF height_le_norm2 norm2_le_norm1].

lemma sq_mono:
  assumes "abs (x::'a::linordered_idom) \<le> y"
  shows "x*x \<le> y*y"
proof -
  have "(abs x \<le> abs y)" using assms by auto
  from this[unfolded abs_le_square_iff power2_eq_square] show ?thesis.
qed

lemma all_elems_ge:
 assumes "a \<in> set (lst::int list)"
 shows "abs a \<le> (max_list (map (nat \<circ> abs) lst))"
proof - 
  have spltRule:"\<And> x a b. x \<le> real (max a b) \<longleftrightarrow> (x \<le> a \<or> x \<le> b)" by auto
  show ?thesis using assms by(induct lst,auto simp:spltRule assms)
qed

lemma norm2_le_height_times_list :
  "sqrt (real_of_int (\<Sum>a\<leftarrow>lst. a * a)) \<le> sqrt (real (length lst)) * real (max_list (map (nat \<circ> abs) lst))"
  (is "_ \<le> _ * real (?ml lst)")
proof -
  have pos:"0 \<le> length lst" "0 \<le> ?ml lst" by auto
  have main:"(\<Sum>a\<leftarrow>lst. a * a) \<le> length lst * int (?ml lst) * int (?ml lst)" proof(induct lst)
    case Nil thus ?case by auto next
    case (Cons a as)
      have a_in_set:"a \<in> set (a # as)" by simp
      have *:"int (length (a # as)) = 1 + int (length as)"
             "(\<Sum>a\<leftarrow>a # as. a * a) = a * a + (\<Sum>a\<leftarrow> as. a * a)" by simp_all
      have helper: "int (?ml as) \<le> ?ml (a # as)" "0 \<le> int (?ml as)" "0 \<le> int (length as)"
        by(induct as,auto)
      have "\<And> a b c d v::int. a\<le>b \<Longrightarrow> c\<le>v * d * d \<Longrightarrow> a+c \<le> 1*b+v *d*d"
           "\<And> v d e::int. d\<le>e \<Longrightarrow> 0\<le>d \<Longrightarrow> 0\<le>v \<Longrightarrow> v *d*d \<le> v *e*e" by (simp_all add: mult_mono')
      hence "\<And> a b c d v e::int. a\<le>b \<Longrightarrow> c\<le>v *d*d \<Longrightarrow> d\<le>e \<Longrightarrow> 0\<le>d \<Longrightarrow> 0\<le>v \<Longrightarrow> a+c \<le> 1*b+v *e*e"
        by fastforce
      from this[OF sq_mono[OF all_elems_ge[OF a_in_set]] Cons helper]
      show ?case unfolding * by (simp add: o_def sign_simps)
  qed
  have "\<And> b c. b \<ge> 0 \<Longrightarrow> c \<ge> 0 \<Longrightarrow> sqrt (b * c * c) = sqrt (b) * c" by (simp add: real_sqrt_mult)
  hence "\<And> a b c. a \<ge> 0 \<Longrightarrow> b \<ge> 0 \<Longrightarrow> c \<ge> 0 \<Longrightarrow> 
                a \<le> int b * c * c \<Longrightarrow> sqrt a \<le> sqrt (real b) * real c"
    using of_int_le_iff of_int_mult of_int_of_nat_eq of_nat_0_le_iff real_sqrt_le_iff
    by (metis (mono_tags, lifting))
  from this[OF sum_of_squares_pos pos main] show ?thesis .
qed

lemma norm2_le_height_times : (* Remark 11, eqn 85.4 *)
  "l2norm g \<le> sqrt (Suc (degree g)) * height g"
proof(cases "g = 0")
  case False 
    have ln:"length (coeffs g) = Suc (degree g)" using length_coeffs[OF False,symmetric] by force
    show ?thesis using norm2_le_height_times_list
      unfolding of_int_of_nat_eq l2norm_list_def
      by (metis floor_mono le_floor_iff ln) next
  case True
    show ?thesis unfolding l2norm_list_def True by simp
qed

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
  unfolding irreducible_def by auto

lemma coeffs_nth_2:
  assumes "p \<noteq> 0"
  shows   "coeff p n = (if n \<le> degree p then coeffs p ! n else 0)"
using coeffs_nth[OF assms] le_degree by (cases "n \<le> degree p",auto)

lemma map_poly_const_1[simp]:"map_poly f 1 = [:f 1:]" unfolding map_poly_def fold_coeffs_def by auto

definition complex_roots_int where
  "complex_roots_int (p::int poly) = complex_roots_complex (map_poly of_int p)"

lemma complex_roots_int:
  "smult (lead_coeff p) (\<Prod>a\<leftarrow>complex_roots_int p. [:- a, 1:]) = map_poly of_int p"
  "length (complex_roots_int p) = degree p"
  using complex_roots[of "map_poly of_int p"] unfolding complex_roots_int_def 
  by (simp_all add: i1.map_poly_preservers)

text {* The measure for polynomials, after K. Mahler *}

definition measure_poly where
  "measure_poly p = cmod (lead_coeff p) * prod_list (map (max 1 \<circ> cmod) (complex_roots_complex p))"

definition measure_poly_int where
  "measure_poly_int p = measure_poly (map_poly complex_of_int p)"

definition measure_monic where
  "measure_monic p = (\<Prod>a\<leftarrow>complex_roots_complex p. (max 1 (cmod a)))"

lemma measure_poly_via_monic :
  "measure_poly p = cmod (lead_coeff p) * measure_monic p"
  unfolding measure_poly_def measure_monic_def by (meson comp_apply)

lemma smult_inj[simp]: assumes "(a::'a::idom) \<noteq> 0" shows "inj (smult a)"
using assms unfolding inj_on_def
by (metis Ring_Hom_Poly.map_poly_inj mult_cancel_left mult_zero_right smult_map_poly)

definition reconstruct_poly::"'a::idom \<Rightarrow> 'a list \<Rightarrow> 'a poly" where
  "reconstruct_poly c roots = smult c (\<Prod>a\<leftarrow>roots. [:- a, 1:])"

lemma reconstruct_is_original_poly:
  "reconstruct_poly (lead_coeff p) (complex_roots_complex p) = p"
  by (simp add:complex_roots(1) reconstruct_poly_def)

lemma reconstruct_poly_monic_is_monic[simp]:
  "monic (\<Prod>a\<leftarrow>xs. [:- a, 1::'a::idom:])"
proof -
  have "(\<And>a. a \<in> set (map (\<lambda> a. [:- a, 1:]) xs) \<Longrightarrow> monic a)" by auto
  from this monic_prod_list[of "map (\<lambda> a. [:- a, 1:]) xs"]
       show ?thesis by metis
qed

lemma reconstruct_with_type_conversion:
  "smult (lead_coeff (map_poly of_int f)) (prod_list (map (\<lambda> a. [:- a, 1:]) (complex_roots_int f)))
   = map_poly of_int f"
unfolding complex_roots_int_def complex_roots(1) by simp

lemma reconstruct_prod:
  shows "reconstruct_poly (a::complex) as * reconstruct_poly b bs
        = reconstruct_poly (a * b) (as @ bs)"
unfolding reconstruct_poly_def by auto

lemma reconstruct_poly_defines_first_argument:
 assumes "reconstruct_poly a as = reconstruct_poly b bs"
   shows "a = b"
using assms reconstruct_poly_monic_is_monic
using  coeff_smult degree_smult_eq mult.right_neutral reconstruct_poly_def smult_eq_0_iff
by (metis (no_types, lifting) coeff_smult degree_smult_eq mult.right_neutral reconstruct_poly_def smult_eq_0_iff)

lemma linear_term_inj[simp]: "inj (\<lambda> a. [:- a, 1::'a::idom:])"
  unfolding inj_on_def by simp

lemma reconstruct_poly_monic_defines_mset:
  assumes "(\<Prod>a\<leftarrow>as. [:- a, 1:]) = (\<Prod>a\<leftarrow>bs. [:- a, 1::'a::{field,euclidean_ring_gcd}:])"
  shows "mset as = mset bs"
proof -
  let ?as = "mset (map (\<lambda> a. [:- a, 1:]) as)"
  let ?bs = "mset (map (\<lambda> a. [:- a, 1:]) bs)"
  have eq_smult:"prod_mset ?as = prod_mset ?bs" using assms by (metis prod_mset_multiset_of)
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

lemma complex_roots_int_prod:
  assumes "f \<noteq> 0" "g \<noteq> 0"
  shows "mset (complex_roots_int (f * g)) = mset (complex_roots_int f) + mset (complex_roots_int g)"
proof -
  have "map_poly complex_of_int f \<noteq> 0" "map_poly complex_of_int g \<noteq> 0" using assms by auto
  thus ?thesis unfolding complex_roots_int_def by(simp)
qed

lemma mset_mult_add:
  assumes "mset (a::'a::field list) = mset b + mset c"
  shows "prod_list a = prod_list b * prod_list c"
  unfolding prod_mset_multiset_of[symmetric]
  using prod_mset_Un[of "mset b" "mset c",unfolded assms[symmetric]].

lemma prod_list_append:
  shows "prod_list b * prod_list c = prod_list (b @ c)"
by (induct c,auto)

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
  shows "measure_monic (f * g) = measure_monic f * measure_monic g"
  unfolding measure_monic_def
  using mset_mult_add_2[OF complex_roots_complex_prod[OF assms],of "\<lambda> a. max 1 (cmod a)"] by simp

lemma measure_poly_0[simp]: "measure_poly 0 = 0" unfolding measure_poly_via_monic by auto

lemma measure_eq_prod: (* Remark 10.2 *)
  "measure_poly (f * g) = measure_poly f * measure_poly g"
proof -
  consider "f = 0" | "g = 0" | (both) "f \<noteq> 0" "g \<noteq> 0" by auto
  thus ?thesis proof(cases)
    case both show ?thesis unfolding measure_poly_via_monic norm_mult lead_coeff_mult
      by (auto simp: measure_mono_eq_prod[OF both])
  qed (simp_all)
qed

lemma lead_coeff_smult_monic:
  assumes "monic p"
  shows "lead_coeff (smult v p) = (v::'v::idom)"
unfolding lead_coeff_def coeff_smult using assms by simp

lemma reconstruct_of_complex_roots:
  assumes "v \<noteq> 0"
  shows "(\<Prod>a\<leftarrow> (complex_roots_complex (smult v (\<Prod>a\<leftarrow>(map of_int as). [:- a, 1:]))). [:- a, 1:])
         = (\<Prod>a\<leftarrow>(map of_int as). [:- a, 1:])"
  using injD[OF smult_inj[OF assms]]
        complex_roots(1)[of "(smult v ((\<Prod>a\<leftarrow>map of_int as. [:- a, 1:])))"]
  unfolding lead_coeff_smult_monic[OF reconstruct_poly_monic_is_monic]
  by blast

lemma reconstruct_of_int_roots[simp]:
  assumes "v \<noteq> 0"
  shows "(\<Prod>a\<leftarrow> (complex_roots_int (smult v (\<Prod>a\<leftarrow>(map of_int as). [:- a, 1:]))). [:- a, 1:])
         = (\<Prod>a\<leftarrow>(map of_int as). [:- a, 1:])"
  unfolding complex_roots_int_def using reconstruct_of_complex_roots[of "of_int v"] assms
  by (simp add: o_def)

lemma complex_roots_complex_of_reconstructed:
  assumes nonzero:"x \<noteq> 0" shows
  "mset (complex_roots_complex (smult x (\<Prod>a\<leftarrow>as. [:- a, 1:]))) = mset as"
  (is "mset ?l = _")
proof -
  have "smult x (\<Prod>a\<leftarrow>?l. [:- a, 1:]) = smult x (\<Prod>a\<leftarrow>as. [:- a, 1:])"
    using complex_roots(1)[of "(smult x (\<Prod>a\<leftarrow>as. [:- a, 1:]))"]
    unfolding lead_coeff_smult_monic[OF reconstruct_poly_monic_is_monic] by auto
  from reconstruct_poly_monic_defines_mset[OF injD[OF smult_inj[OF nonzero] this]]
  show ?thesis by auto
qed

lemma complex_abs_is_real_abs_coeff[simp]:
"abs (coeff (map_poly of_int p) n) = cmod (coeff p n)" 
by (metis Reals_of_int complex_Re_of_int in_Reals_norm i3.map_poly_preservers(2))

lemma complex_abs_is_real_abs[simp]:
"cmod (lead_coeff p1) = abs (lead_coeff (map_poly real_of_int p2)) \<longleftrightarrow> 
 cmod (lead_coeff p1) = cmod (lead_coeff p2)"
unfolding lead_coeff_def
by (metis complex_abs_is_real_abs_coeff lead_coeff_def i3.map_poly_preservers)

lemma measure_of_reconstructed[simp]:
  assumes "x \<noteq> 0" shows
  "measure_monic (reconstruct_poly x as) = (\<Prod>a\<leftarrow>as. (max 1 (cmod a)))" (is "?l = ?r")
unfolding measure_monic_def reconstruct_poly_def
using complex_roots_complex_of_reconstructed[OF assms]
by (metis (no_types, lifting) mset_map prod_mset_multiset_of)

lemma max_via_filter: (* can be generalised to a different function than 'cmod' *)
  "(\<Prod>a\<leftarrow>filter (\<lambda> v. cmod v > 1) lst. cmod a) = (\<Prod>a\<leftarrow>lst. max 1 (cmod a))"
  by(induct lst,auto)

lemma prod_cmod[simp]:
  "cmod (\<Prod>a\<leftarrow>lst. f a) = (\<Prod>a\<leftarrow>lst. cmod (f a))"
  by(induct lst,auto simp:real_normed_div_algebra_class.norm_mult)

lemma prod_degree:
  assumes "Ball (set lst) (\<lambda> x. (f x :: 'a :: {semidom,field} poly) \<noteq> 0)"
  shows "degree (\<Prod>a\<leftarrow>lst. f a) = (\<Sum> a\<leftarrow>lst. degree (f a))"
proof -
  have "Ball (set lst) (\<lambda> x. f x \<noteq> 0) \<Longrightarrow>
        (\<Prod>a\<leftarrow>lst. f a) \<noteq> 0 \<and> ?thesis"
  proof(induct lst) case (Cons a lst)
    have nonz:"f a \<noteq> 0" "prod_list (map f lst) \<noteq> 0" and
         deg:"degree (prod_list (map f lst)) = (\<Sum>a\<leftarrow>lst. degree (f a))" using Cons by auto
    from degree_mult_eq[OF nonz] deg 
         semiring_no_zero_divisors_class.no_zero_divisors[OF nonz]
    show ?case by(auto)
  qed auto
  thus ?thesis using assms by simp
qed

lemma prod_degree_of_linear_formulas[simp]:
  assumes "\<And>x. x \<in> set lst \<Longrightarrow> degree (f x :: 'a :: {semidom,field} poly) = 1"
  shows "degree (\<Prod>a\<leftarrow>lst. f a) = length lst"
proof -
  have "Ball (set lst) (\<lambda> x. (f x) \<noteq> 0)" using assms by force
  hence "degree (\<Prod>a\<leftarrow>lst. f a) = (\<Sum> a\<leftarrow>lst. degree (f a))" using prod_degree by auto
  moreover have "\<dots> = length lst" using assms by(induct lst,auto)
  ultimately show ?thesis by auto
qed

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

lemma norm2_helper:
  "(\<Sum>a\<leftarrow>lst. (cmod a)\<^sup>2) = (\<Sum>a\<leftarrow>lst. a * cnj a)"
proof -
  have a:"\<And> a. a * cnj a = (complex_of_real (cmod a))\<^sup>2" using complex_norm_square by auto
  show ?thesis by(induct lst,auto simp:a)
qed

fun hd_poly where
  "hd_poly Nil = 0" |
  "hd_poly (Cons a as) = a"
fun tl_poly where
  "tl_poly Nil = []" |
  "tl_poly (Cons a as) = as"
lemma "tl_poly v = drop 1 v" by(induct v;auto)
lemma tl_of_cCons[simp]:"tl_poly (cCons a as) = as" by(induct as;auto simp:cCons_def)

lemma make_cCons:
  shows "coeffs (smult b p + pCons v (smult a p)) = cCons (b * hd_poly (coeffs p)+v) (tl_poly (coeffs (p*[:b,a:])))"
by(induct p;auto)

lemma coeffs_cong_1[simp]: "cCons a v = cCons b v \<longleftrightarrow> a = b" unfolding cCons_def by auto
lemma coeffs_cong_2[simp]: "cCons v a = cCons v b \<longleftrightarrow> a = b" unfolding cCons_def by auto
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

lemma norm2_cCons[simp]:
  shows "(\<Sum>a\<leftarrow>cCons a (coeffs as). (cmod a)\<^sup>2) = cmod a^2 + norm2 as"
by(induct as;cases "a = 0";auto)


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
  "measure_poly f \<le> l2norm_complex f"
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
  thus "measure_poly f \<le> sqrt (norm2 f)"
    using reconstruct_with_type_conversion[unfolded complex_roots_int_def]
    by (simp add: measure_poly_via_monic measure_monic_def complex_roots_int_def)
qed

lemma l1_norm_pos:"(0::int) \<le> sum_list (map abs lst)"
  by(induct lst,auto)
lemma l1_norm_cmod_pos:"(0::int) \<le> (\<Sum>x\<leftarrow>h. cmod (complex_of_int x))"
  by(induct h,auto)

lemma prod_list_ge1:
  assumes "Ball (set x) (\<lambda> (a::real). a \<ge> 1)"
  shows "prod_list x \<ge> 1"
using assms proof(induct x)
  case (Cons a as)
    have "\<forall>a\<in>set as. 1 \<le> a" "1 \<le> a" using Cons(2) by auto
    thus ?case using Cons.hyps mult_mono' by fastforce
qed auto

lemma measure_monic_ge_1: "measure_monic p \<ge> 1"
  unfolding measure_monic_def by(rule prod_list_ge1,simp)
lemma measure_monic_ge_0: "measure_monic p \<ge> 0"
  using measure_monic_ge_1 le_numeral_extra(1) order_trans by blast

lemma coeff_in_coeffs:
  assumes "coeff g k \<noteq> 0"
  shows "coeff g k \<in> set (coeffs g)"
proof -
  from nth_default_coeffs_eq have "nth_default 0 (coeffs g) k = coeff g k" by metis
  hence "coeff g k \<in> insert 0 (set (coeffs g))" using range_nth_default by (metis UNIV_I image_eqI)
  thus ?thesis using assms by simp
qed

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

lemma mignotte_helper_coeff_int:"cmod (coeff_int (\<Prod>a\<leftarrow>lst. [:- a, 1:]) i)
    \<le> choose_int (length lst) i * (\<Prod>a\<leftarrow>lst. (max 1 (cmod a)))"
proof(induct lst arbitrary:i)
  case Nil thus ?case by(auto simp:coeff_int_def choose_int_def)
  case (Cons v xs i)
  let ?r = "(\<Prod>a\<leftarrow>xs. [:- a, 1:])"
  let ?mv = "(\<Prod>a\<leftarrow>xs. (max 1 (cmod a)))"
  let "?m n" = "choose_int (length xs) n * ?mv"
  let ?split_choice = "choose_int (length xs) (i - 1) * 1 + choose_int (length xs) i * cmod v"
  let ?comb_choice = "choose_int (Suc (length xs)) i * max 1 (cmod v)"
  have le1:"1 \<le> max 1 (cmod v)" by auto
  have le2:"cmod v \<le> max 1 (cmod v)" by auto
  from ordered_ab_semigroup_add_class.add_mono[OF 
       ordered_comm_semiring_class.comm_mult_left_mono[OF le1 of_nat_0_le_iff]
       ordered_comm_semiring_class.comm_mult_left_mono[OF le2 of_nat_0_le_iff]]
  have "?split_choice \<le>
        choose_int (length xs) (i - 1) * max 1 (cmod v) + choose_int (length xs) i * max 1 (cmod v)"
    by simp
  also have "\<dots> = (choose_int (length xs) (i - 1) + choose_int (length xs) i) * max 1 (cmod v)"
    by (simp add: distrib_right)
  finally have le_max:"?split_choice \<le> ?comb_choice" by simp
  have mv_ge_0:"0 \<le> ?mv" by (induct xs,auto)
  hence m_ge_0:"\<And> n. 0 \<le> ?m n" by(auto simp:choose_int_def mult.left_commute)
  have "cmod (coeff_int ([:- v, 1:] * ?r) i) \<le> cmod (coeff_int ?r (i - 1)) + cmod (coeff_int (smult v ?r) i)"
    using norm_triangle_ineq4 by auto
  also have "\<dots> \<le> ?m (i - 1) + (cmod v * ?m i)"
    using ordered_ab_semigroup_add_class.add_mono[OF Cons mult_mono'[OF order_refl Cons], of "cmod v" i "i-1",simplified] by (simp add: norm_mult mult_mono')
  also have "\<dots> \<le> ?split_choice * ?mv"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> ?comb_choice * ?mv" using mult_mono'[OF le_max order_refl _ mv_ge_0] by auto
  finally show ?case by auto
qed

lemma mignotte_helper_coeff:
  shows "cmod (coeff h i) \<le> (degree h choose i) * measure_poly h"
proof -
  let ?r = "complex_roots_complex h"
  have "cmod (coeff h i) = cmod (coeff (smult (lead_coeff h) (\<Prod>a\<leftarrow>?r. [:- a, 1:])) i)"
    unfolding complex_roots by auto
  also have "\<dots> = cmod (lead_coeff h) * cmod (coeff (\<Prod>a\<leftarrow>?r. [:- a, 1:]) i)" by(simp add:norm_mult)
  also have "\<dots> \<le> cmod (lead_coeff h) * (degree h choose i) * measure_monic h"
    proof(cases "h = 0") case False hence "cmod (lead_coeff h) > 0" by (simp add:lead_coeff_nonzero)
      thus ?thesis using measure_monic_def mignotte_helper_coeff_int[of ?r i] by simp
    qed auto
  also have "\<dots> = (degree h choose i) * measure_poly h"
    unfolding measure_poly_via_monic by simp
  finally show ?thesis.
qed

lemma sum_conv:
shows "(\<Sum>i = 0..v. g i) = (\<Sum>i\<leftarrow>[0..<Suc v]. g i)"
proof -
  have h:"\<And> v. {0..v} = set [0..< Suc v]" by(induct;auto)
  show ?thesis using sum.set_conv_list[of g "[0..< Suc v]",folded h,unfolded remdups_upt].
qed

lemma mignotte_helper_complex:
  shows "(\<Sum>v\<leftarrow>coeffs h. cmod v) \<le> 2 ^ degree h * measure_poly h" (is "?l \<le> ?r")
proof -
  have "?l = (\<Sum>i\<leftarrow>[0..< Suc (degree h)]. cmod (coeff h i))"
    unfolding coeffs_def by (auto simp: o_def)
  also have "\<dots> \<le> (\<Sum>i\<leftarrow>[0..< Suc (degree h)]. (degree h choose i) * measure_poly h)"
    using add_induct_gen_le[of id,simplified] add_mono[OF mignotte_helper_coeff order_refl]
    by fast
  also have "\<dots> = (\<Sum>i = 0..degree h. (degree h choose i)) * measure_poly h"
    unfolding sum_list_mult_const degree_eq_length_coeffs sum_conv
    by (simp add: o_def)
  also have "\<dots> = ?r" by (simp add: choose_row_sum)
  finally show ?thesis.
qed

lemma mignotte_helper:
  shows "sum_list (map abs (coeffs h)) \<le> 2 ^ degree h * measure_poly_int h"
unfolding measure_poly_int_def
  using mignotte_helper_complex[of "map_poly complex_of_int h"] 
  by (simp add: o_def coeffs_map_poly)

lemma cmod_through_lead_coeff[simp]:
  "cmod (lead_coeff (map_poly complex_of_int h)) = abs (lead_coeff h)"
proof(induct h) case (pCons a h)
  from pCons consider "a \<noteq> 0 \<and> h = 0" | "h \<noteq> 0" by auto
  thus ?case by (cases, auto simp: i1.map_poly_preservers[symmetric])  
qed auto

lemma measure_poly_ge_1:
  assumes "h\<noteq>0"
  shows "(1::real) \<le> measure_poly_int h"
proof -
  from assms have "cmod (lead_coeff (map_poly complex_of_int h)) > 0" by simp
  hence "cmod (lead_coeff (map_poly complex_of_int h)) \<ge> 1"
    by(cases "abs (lead_coeff h)";auto)
  from mult_mono[OF this measure_monic_ge_1 norm_ge_zero]
  show ?thesis unfolding measure_poly_int_def measure_poly_via_monic
    by auto
qed

lemma twopow:"\<And> a b. a \<le> b \<Longrightarrow> (2::'a::{linordered_semidom})^a \<le> 2^b" by simp

definition factor_bound :: "int poly \<Rightarrow> nat \<Rightarrow> int" where
  "factor_bound f g = 2 ^ g * sqrt_int_ceiling (sum_list (map (\<lambda> a. a * a) (coeffs f)))" 

lemma factor_bound: assumes "f \<noteq> 0" "g dvd f" "degree g \<le> n"
  shows "\<bar>coeff g k\<bar> \<le> factor_bound f n"  proof-
  obtain h where gh:"g * h = f" using assms by (metis dvdE)
  have nz:"g\<noteq>0" "h\<noteq>0" using gh assms(1) by auto
  have g1:"(1::real) \<le> measure_poly_int h" using measure_poly_ge_1 gh assms(1) by auto
  have g0:"\<And> h. 0 \<le> measure_poly_int h" unfolding measure_poly_int_def measure_poly_via_monic
    by (simp add: measure_monic_ge_0)
  have "\<bar>coeff g k\<bar> \<le> height g" using all_elems_ge coeff_in_coeffs by force
  also have "\<dots> \<le>  2 ^ degree g * measure_poly_int g"
    using order_trans[OF _ mignotte_helper] height_le_norm1 by presburger
  also have "\<dots> \<le> 2 ^ degree g * measure_poly_int g * measure_poly_int h"
    using mult_mono[OF order_refl g1] by (simp add: g0)
  also have "\<dots> \<le> 2 ^ degree g * measure_poly_int f"
    using measure_eq_prod[of "map_poly complex_of_int g" "map_poly complex_of_int h"]
    unfolding measure_poly_int_def gh[symmetric] by simp
  also have "\<dots> \<le> 2 ^ n * measure_poly_int f"
    using mult_mono[OF twopow[OF assms(3)] order_refl _ g0] by auto
  also have "\<dots> \<le> 2 ^ n * (l2norm_complex (map_poly complex_of_int f))"
    using Landau_inequality[of "(map_poly complex_of_int f)"] unfolding measure_poly_int_def
     by simp
  also have "\<dots> \<le> 2 ^ n * ceiling (l2norm_complex  (map_poly complex_of_int f))"
     by simp
  also have "\<dots> = factor_bound f n"
    unfolding factor_bound_def by (auto simp: power2_eq_square coeffs_map_poly o_def)
  finally show ?thesis unfolding of_int_le_iff by blast
qed

lemma mignotte: (* note: no longer needed, but it is the lemma in its common symmetric form *)
  assumes "g \<noteq> 0" "h\<noteq>0"
  shows "height g * height h \<le> 2 ^ (degree g + degree h) * (l2norm_complex (map_poly complex_of_int (g * h)))"
proof -
  let ?df = "degree g + degree h"
  have mp: "\<And> h. 0 \<le> 2 ^ degree h * measure_poly_int h"
    by (simp add: measure_poly_int_def measure_monic_ge_0 measure_poly_via_monic)
  have np: "\<And> h. 0 \<le> real_of_int (sum_list (map abs h))" using l1_norm_pos of_int_le_iff
    by presburger
  have "height g * height h \<le> l2norm g * l2norm h"
    using mult_mono[OF height_le_norm2 height_le_norm2 l2norm_pos] by auto
  also have "\<dots> \<le> sum_list (map abs (coeffs g)) * sum_list (map abs (coeffs h))"
    using mult_mono[OF norm2_le_norm1 norm2_le_norm1 l1_norm_pos l2norm_pos].
  also have "\<dots> \<le> 2 ^ degree g * measure_poly_int g * 2 ^ degree h * measure_poly_int h"
    using mult_mono[OF mignotte_helper mignotte_helper mp np]
    by (simp add: mult.assoc)
  also have "\<dots> = 2 ^ ?df * measure_poly_int g * measure_poly_int h"
    by (simp add: power_add)
  also have "\<dots> = 2 ^ ?df * measure_poly_int (g * h)"
    using measure_eq_prod[of "map_poly complex_of_int g" "map_poly complex_of_int h"]
    unfolding measure_poly_int_def by simp
  also have "\<dots> \<le> 2 ^ ?df * (l2norm_complex (map_poly complex_of_int (g*h)))"
    using Landau_inequality[of "(map_poly complex_of_int (g*h))"] unfolding measure_poly_int_def
     by simp
  finally show ?thesis by linarith
qed

definition factor_bound_no_degree :: "int poly \<Rightarrow> int" where
  "factor_bound_no_degree f = 2 ^ degree f * sqrt_int_ceiling (sum_list (map (\<lambda> a. a * a) (coeffs f)))" 

lemma factor_bound_no_degree: assumes "f \<noteq> 0" "g dvd f"
  shows "\<bar>coeff g k\<bar> \<le> factor_bound_no_degree f" proof-
  have p1:"\<bar>coeff g k\<bar> \<le> factor_bound f (degree g)" using factor_bound assms by auto
  show ?thesis using mult_mono[OF twopow[OF dvd_imp_degree_le[OF assms(2) assms(1)]] p1]
    unfolding factor_bound_def factor_bound_no_degree_def by auto
qed
end
end
