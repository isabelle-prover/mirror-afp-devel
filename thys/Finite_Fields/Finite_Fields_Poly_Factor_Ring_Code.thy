section \<open>Executable Polynomial Factor Rings\<close>

theory Finite_Fields_Poly_Factor_Ring_Code
  imports
    Finite_Fields_Poly_Ring_Code
    Rabin_Irreducibility_Test_Code
    Finite_Fields_More_Bijections
begin

text \<open>Enumeration of the polynomials with a given degree:\<close>

definition poly_enum :: "('a,'b) idx_ring_enum_scheme \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list"
  where "poly_enum R l n =
    dropWhile ((=) 0\<^sub>C\<^bsub>R\<^esub>) (map (\<lambda>p. idx_enum R (nth_digit n (l-1-p) (idx_size R))) [0..<l])"

lemma replicate_drop_while_cancel:
  assumes "k = length (takeWhile ((=) x) y)"
  shows  "replicate k x @ dropWhile ((=) x) y = y" (is "?L = ?R")
proof -
  have "replicate k x = takeWhile ((=) x) y"
    using assms by (metis (full_types) replicate_length_same set_takeWhileD)
  thus ?thesis by simp
qed

lemma arg_cong3:
  assumes "x = u" "y = v" "z = w"
  shows "f x y z = f u v w"
  using assms by simp

lemma list_all_dropwhile: "list_all p xs \<Longrightarrow> list_all p (dropWhile q xs)"
  by (induction xs) auto

lemma bij_betw_poly_enum:
  assumes "enum\<^sub>C R" "ring\<^sub>C R"
  shows "bij_betw (poly_enum R l) {..<idx_size R^l}
  {xs. xs \<in> carrier (poly_ring (ring_of R)) \<and> length xs \<le> l}"
proof -
  let ?b = "idx_size R"
  let ?S0 = "{..<l} \<rightarrow>\<^sub>E {..<order (ring_of R)}"
  let ?S1 = "{..<l} \<rightarrow>\<^sub>E {x. idx_pred R x}"
  let ?S2 = "{xs. list_all (idx_pred R) xs \<and> length xs = l}"
  let ?S3 = "{xs. (xs = [] \<or> hd xs \<noteq> 0\<^sub>C\<^bsub>R\<^esub>) \<and> list_all (idx_pred R) xs \<and> length xs \<le> l}"
  let ?S4 = "{xs. xs \<in> carrier (poly_ring (ring_of R)) \<and> length xs \<le> l}"

  interpret ring "ring_of R" using assms(2) unfolding ring\<^sub>C_def by simp

  have "0 < order (ring_of R)" using enum_cD(1)[OF assms(1)] order_gt_0_iff_finite by metis
  also have "... = ?b" using enum_cD[OF assms(1)] by auto
  finally have b_gt_0: "?b > 0" by simp

  note bij0 = lift_bij_betw[OF enum_cD(3)[OF assms(1)], where I="{..<l}"]
  note bij1 = lists_bij[where d="l" and S="{x. idx_pred R x}"]

  have "bij_betw (dropWhile ((=) 0\<^sub>C\<^bsub>R\<^esub>)) ?S2 ?S3"
  proof (rule bij_betwI[where g="\<lambda>xs. replicate (l - length xs) 0\<^sub>C\<^bsub>R\<^esub> @ xs"])
    have "dropWhile ((=) 0\<^sub>C\<^bsub>R\<^esub>) xs \<in> ?S3" if "xs \<in> ?S2" for xs
    proof -
      have "dropWhile ((=) 0\<^sub>C\<^bsub>R\<^esub>) xs = [] \<or> hd (dropWhile ((=) 0\<^sub>C\<^bsub>R\<^esub>) xs) \<noteq> 0\<^sub>C\<^bsub>R\<^esub>"
        using hd_dropWhile by (metis (full_types))
      moreover have "length (dropWhile ((=) 0\<^sub>C\<^bsub>R\<^esub>) xs) \<le> l"
        by (metis (mono_tags, lifting) mem_Collect_eq length_dropWhile_le that)
      ultimately show ?thesis using that by (auto simp:list_all_dropwhile)
    qed
    thus "dropWhile ((=) 0\<^sub>C\<^bsub>R\<^esub>) \<in> ?S2 \<rightarrow> ?S3"  by auto
    have "replicate (l - length xs) 0\<^sub>C\<^bsub>R\<^esub> @ xs \<in> ?S2" if "xs \<in> ?S3" for xs
    proof -
      have "idx_pred R 0\<^sub>C\<^bsub>R\<^esub>" using add.one_closed by (simp add:ring_of_def)
      moreover have "length (replicate (l - length xs) 0\<^sub>C\<^bsub>R\<^esub> @ xs) = l" using that by auto
      ultimately show ?thesis using that by (auto simp:list_all_iff)
    qed
    thus "(\<lambda>xs. replicate (l - length xs) 0\<^sub>C\<^bsub>R\<^esub> @ xs) \<in> ?S3 \<rightarrow> ?S2" by auto

    show "replicate (l - length (dropWhile ((=) 0\<^sub>C\<^bsub>R\<^esub>) x)) 0\<^sub>C\<^bsub>R\<^esub> @ dropWhile ((=) 0\<^sub>C\<^bsub>R\<^esub>) x = x"
      if "x \<in> ?S2" for x
    proof -
      have "length (takeWhile ((=) 0\<^sub>C\<^bsub>R\<^esub>) x) + length (dropWhile ((=) 0\<^sub>C\<^bsub>R\<^esub>) x) = length x"
        unfolding length_append[symmetric] by simp
      thus ?thesis using that by (intro replicate_drop_while_cancel) auto
    qed
    show "dropWhile ((=) 0\<^sub>C\<^bsub>R\<^esub>) (replicate (l - length y) 0\<^sub>C\<^bsub>R\<^esub> @ y) = y"
      if "y \<in> ?S3" for y
    proof -
      have "dropWhile ((=) 0\<^sub>C\<^bsub>R\<^esub>) (replicate (l - length y) 0\<^sub>C\<^bsub>R\<^esub> @ y) = dropWhile ((=) 0\<^sub>C\<^bsub>R\<^esub>) y"
        by (intro dropWhile_append2) simp
      also have "... = y" using that by (intro iffD2[OF dropWhile_eq_self_iff]) auto
      finally show ?thesis by simp
    qed
  qed
  moreover have "?S3 = ?S4"
    unfolding ring_of_poly[OF assms(2),symmetric] by (simp add:ring_of_def poly_def)
  ultimately have bij2: "bij_betw (dropWhile ((=) 0\<^sub>C\<^bsub>R\<^esub>)) ?S2 ?S4" by simp

  have bij3: "bij_betw (\<lambda>x. l-1-x) {..<l}  {..<l}"
    by (intro bij_betwI[where g="\<lambda>x. l-1-x"]) auto
  note bij4 = bij_betw_reindex[OF bij3, where S="{..<order (ring_of R)}"]
  have bij5: "bij_betw (\<lambda>n. (\<lambda>p\<in>{..<l}. nth_digit n p ?b)) {..<?b^l} ?S0"
    using nth_digit_bij[where n="l"] enum_cD[OF assms(1)] by simp
  have bij6: "bij_betw (\<lambda>n. (\<lambda>p\<in>{..<l}. nth_digit n (l-1-p) ?b)) {..<?b^l} ?S0"
    by (intro iffD2[OF arg_cong3[where f="bij_betw"] bij_betw_trans[OF bij5 bij4]]) force+

  have "carrier (ring_of R) = {x. idx_pred R x}" unfolding ring_of_def by auto
  hence bij7: "bij_betw (\<lambda>n. (\<lambda>p\<in>{..<l}. idx_enum R (nth_digit n (l-1-p) ?b))) {..<?b^l} ?S1"
    by (intro iffD2[OF arg_cong3[where f="bij_betw"] bij_betw_trans[OF bij6 bij0]]) fastforce+

  have bij8: "bij_betw (\<lambda>n. map (\<lambda>p. idx_enum R (nth_digit n (l-1-p) ?b)) [0..<l]) {..<?b^l} ?S2"
    by (intro iffD2[OF arg_cong3[where f="bij_betw"] bij_betw_trans[OF bij7 bij1]])
       (auto simp:comp_def list_all_iff atLeast0LessThan[symmetric])

  thus "bij_betw (poly_enum R l) {..<idx_size R ^ l} ?S4"
    using bij_betw_trans[OF bij8 bij2] unfolding poly_enum_def comp_def by simp
qed


definition poly_enum_inv :: "('a,'b) idx_ring_enum_scheme \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat"
  where "poly_enum_inv R l f =
    (let f' = replicate (l - length f) 0\<^sub>C\<^bsub>R\<^esub> @ f in
    (\<Sum>i<l. idx_enum_inv R (f' ! (l - 1 - i)) * idx_size R ^i ))"

find_theorems "(\<Sum>i<?l. ?f i * ?x^i) < ?x^?l"

lemma poly_enum_inv:
  assumes "enum\<^sub>C R" "ring\<^sub>C R"
  assumes "x \<in>  {xs. xs \<in> carrier (poly_ring (ring_of R)) \<and> length xs \<le> l}"
  shows "the_inv_into {..<idx_size R^l} (poly_enum R l) x = poly_enum_inv R l x"
proof -
  define f where "f = replicate (l- length x) 0\<^sub>C\<^bsub>R\<^esub> @ x"
  let ?b = "idx_size R"
  let ?d = "dropWhile ((=) 0\<^sub>C\<^bsub>R\<^esub>)"

  have len_f: "length f = l" using assms(3) unfolding f_def by auto
  note enum_c = enum_cD[OF assms(1)]

  interpret ring "ring_of R" using assms(2) unfolding ring\<^sub>C_def by simp

  have 0: "idx_enum_inv R y < ?b" if "y \<in> carrier (ring_of R)" for y
    using bij_betw_imp_surj_on[OF enum_c(4)] enum_c(2) that by auto
  have 1: "(x = [] \<or> lead_coeff x \<noteq> 0\<^sub>C\<^bsub>R\<^esub>) \<and> list_all (idx_pred R) x \<and> length x \<le> l"
    using assms(3) unfolding ring_of_poly[OF assms(2),symmetric] by (simp add:ring_of_def poly_def)
  moreover have "\<zero>\<^bsub>ring_of R\<^esub> \<in> carrier (ring_of R)" by simp
  hence "idx_pred R 0\<^sub>C\<^bsub>R\<^esub>" unfolding ring_of_def by simp
  ultimately have 2: "set f \<subseteq> carrier (ring_of R)"
    unfolding f_def by (auto simp add:ring_of_def list_all_iff)

  have "poly_enum R l(poly_enum_inv R l x)= poly_enum R l (\<Sum>i<l. idx_enum_inv R (f ! (l-1-i))*?b^i)"
    unfolding poly_enum_inv_def f_def[symmetric] by simp
  also have "... = ?d (map (\<lambda>p. idx_enum R (idx_enum_inv R (f ! (l - 1 - (l - 1 - p))))) [0..<l])"
    unfolding poly_enum_def using 2 len_f by (intro arg_cong[where f="?d"]
        arg_cong[where f="idx_enum R"] map_cong refl nth_digit_sum 0) auto
  also have "... =?d (map (\<lambda>p. (f ! (l-1 - (l-1-p)))) [0..<l])"
    using 2 len_f by (intro arg_cong[where f="?d"] map_cong refl enum_c) auto
  also have "... =?d (map (\<lambda>p. (f ! p)) [0..<l])"
    by (intro arg_cong[where f="?d"] map_cong) auto
  also have "... = ?d f" using len_f map_nth by (intro arg_cong[where f="?d"]) auto
  also have "... = ?d x" unfolding f_def by (intro dropWhile_append2) auto
  also have "... = x" using 1 by (intro iffD2[OF dropWhile_eq_self_iff]) auto
  finally have "poly_enum R l (poly_enum_inv R l x) = x" by simp
  moreover have "poly_enum_inv R l x < idx_size R^l"
    unfolding poly_enum_inv_def Let_def f_def[symmetric] using len_f 2
    by (intro nth_digit_sum(2) 0) auto
  ultimately show ?thesis
    by (intro the_inv_into_f_eq bij_betw_imp_inj_on[OF bij_betw_poly_enum[OF assms(1,2)]]) auto
qed

definition poly_mod_ring :: "('a,'b) idx_ring_enum_scheme \<Rightarrow> 'a list => 'a list idx_ring_enum"
  where "poly_mod_ring R f = \<lparr>
    idx_pred = (\<lambda>xs. idx_pred (poly R) xs \<and> length xs \<le> degree f),
    idx_uminus = idx_uminus (poly R),
    idx_plus = (\<lambda>x y. pmod\<^sub>C R (x +\<^sub>C\<^bsub>poly R\<^esub> y) f),
    idx_udivide = (\<lambda>x. let ((u,v),r) = ext_euclidean R x f in pmod\<^sub>C R (r\<inverse>\<^sub>C\<^bsub>poly R\<^esub> *\<^sub>C\<^bsub>poly R\<^esub> u) f),
    idx_mult = (\<lambda>x y. pmod\<^sub>C R (x *\<^sub>C\<^bsub>poly R\<^esub> y) f),
    idx_zero = 0\<^sub>C\<^bsub>poly R\<^esub>,
    idx_one = 1\<^sub>C\<^bsub>poly R\<^esub>,
    idx_size = idx_size R ^ degree f,
    idx_enum = poly_enum R (degree f),
    idx_enum_inv = poly_enum_inv R (degree f) \<rparr>"

definition poly_mod_ring_iso :: "('a,'b) idx_ring_enum_scheme \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list set"
  where "poly_mod_ring_iso R f x = PIdl\<^bsub>poly_ring (ring_of R)\<^esub> f +>\<^bsub>poly_ring (ring_of R)\<^esub> x"

definition poly_mod_ring_iso_inv :: "('a,'b) idx_ring_enum_scheme \<Rightarrow> 'a list \<Rightarrow> 'a list set \<Rightarrow> 'a list"
  where "poly_mod_ring_iso_inv R f =
    the_inv_into (carrier (ring_of (poly_mod_ring R f))) (poly_mod_ring_iso R f)"

context
  fixes f
  fixes R :: "('a,'b) idx_ring_enum_scheme"
  assumes field_R: "field\<^sub>C R"
  assumes f_carr: "f \<in> carrier (poly_ring (ring_of R))"
  assumes deg_f: "degree f > 0"
begin

private abbreviation P where "P \<equiv> poly_ring (ring_of R)"
private abbreviation I where "I \<equiv> PIdl\<^bsub>poly_ring (ring_of R)\<^esub> f"

interpretation field "ring_of R"
  using field_R unfolding field\<^sub>C_def by auto

interpretation d: domain "P"
  by (intro univ_poly_is_domain carrier_is_subring)

interpretation i: ideal I P
  using f_carr by (intro d.cgenideal_ideal) auto

interpretation s: ring_hom_ring P "P Quot I"  "(+>\<^bsub>P\<^esub>) I"
  using i.rcos_ring_hom_ring by auto

interpretation cr: cring "P Quot I"
    by (intro i.quotient_is_cring d.cring_axioms)

lemma ring_c: "ring\<^sub>C R"
  using field_R unfolding field\<^sub>C_def domain\<^sub>C_def cring\<^sub>C_def by auto

lemma d_poly: "domain\<^sub>C (poly R)" using field_R unfolding field\<^sub>C_def by (intro poly_domain) auto

lemma ideal_mod:
  assumes "y \<in> carrier P"
  shows "I +>\<^bsub>P\<^esub> (pmod y f) = I +>\<^bsub>P\<^esub> y"
proof -
  have "f \<in> I" by (intro d.cgenideal_self f_carr)
  hence "(f \<otimes>\<^bsub>P\<^esub> (pdiv y f)) \<in> I"
    using long_division_closed[OF carrier_is_subfield] assms f_carr
    by (intro i.I_r_closed) (simp_all)
  hence "y \<in> I +>\<^bsub>P\<^esub> (pmod y f)"
    using assms f_carr unfolding a_r_coset_def'
    by (subst pdiv_pmod[OF carrier_is_subfield, where q="f"]) auto
  thus ?thesis
    by (intro i.a_repr_independence' assms long_division_closed[OF carrier_is_subfield] f_carr)
qed

lemma poly_mod_ring_carr_1:
  "carrier (ring_of (poly_mod_ring R f)) = {xs. xs \<in> carrier P \<and> degree xs < degree f}"
  (is "?L = ?R")
proof -
  have "?L = {xs. xs \<in> carrier (ring_of (poly R)) \<and> degree xs < degree f}"
    using deg_f unfolding poly_mod_ring_def ring_of_def by auto
  also have "... = ?R" unfolding ring_of_poly[OF ring_c] by simp
  finally show ?thesis by simp
qed

lemma poly_mod_ring_carr:
  assumes "y \<in> carrier P"
  shows "pmod y f \<in> carrier (ring_of (poly_mod_ring R f))"
proof -
  have "f \<noteq> []" using deg_f by auto
  hence "pmod y f = [] \<or> degree (pmod y f) < degree f"
    by (intro pmod_degree[OF carrier_is_subfield] assms f_carr)
  hence "degree (pmod y f) < degree f" using deg_f by auto
  moreover have "pmod y f \<in> carrier P"
    using f_carr assms long_division_closed[OF carrier_is_subfield] by auto
  ultimately show ?thesis unfolding poly_mod_ring_carr_1 by auto
qed

lemma poly_mod_ring_iso_ran:
  "poly_mod_ring_iso R f ` carrier (ring_of (poly_mod_ring R f)) = carrier (P Quot I)"
proof -
  have "poly_mod_ring_iso R f x \<in> carrier (P Quot I)"
    if "x \<in> carrier (ring_of (poly_mod_ring R f))" for x
  proof -
    have "I \<subseteq> carrier P" by auto
    moreover have "x \<in> carrier P" using that unfolding poly_mod_ring_carr_1 by auto
    ultimately have "poly_mod_ring_iso R f x \<in> a_rcosets\<^bsub>P\<^esub> I"
      using that f_carr unfolding  poly_mod_ring_iso_def by (intro d.a_rcosetsI) auto
    thus ?thesis unfolding FactRing_def by simp
  qed
  moreover have "x \<in> poly_mod_ring_iso R f ` carrier (ring_of (poly_mod_ring R f))"
    if "x \<in> carrier (P Quot I)" for x
  proof -
    have "x \<in> a_rcosets\<^bsub>P\<^esub> I" using that unfolding FactRing_def by auto
    then obtain y where y_def: "x = I +>\<^bsub>P\<^esub> y" "y \<in> carrier P"
      using that unfolding A_RCOSETS_def' by auto
    define z where "z = pmod y f"
    have "I +>\<^bsub>P\<^esub> z = I +>\<^bsub>P\<^esub> y" unfolding z_def by (intro ideal_mod y_def)
    hence "poly_mod_ring_iso R f z = x" unfolding poly_mod_ring_iso_def y_def by simp
    moreover have "z \<in> carrier (ring_of (poly_mod_ring R f))"
      unfolding z_def by (intro poly_mod_ring_carr y_def)
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis by auto
qed

lemma poly_mod_ring_iso_inj:
  "inj_on (poly_mod_ring_iso R f) (carrier (ring_of (poly_mod_ring R f)))"
proof (rule inj_onI)
  fix x y
  assume "x \<in> carrier (ring_of (poly_mod_ring R f))"
  hence x:"x \<in> carrier P" "degree x < degree f" unfolding poly_mod_ring_carr_1 by auto
  assume "y \<in> carrier (ring_of (poly_mod_ring R f))"
  hence y:"y \<in> carrier P" "degree y < degree f" unfolding poly_mod_ring_carr_1 by auto

  have "degree (x \<ominus>\<^bsub>P\<^esub> y) \<le> max (degree x) (degree (\<ominus>\<^bsub>P\<^esub>y))"
    unfolding a_minus_def by (intro degree_add)
  also have "... = max (degree x) (degree y)"
    unfolding univ_poly_a_inv_degree[OF carrier_is_subring y(1)] by simp
  also have "... < degree f" using x(2) y(2) by simp
  finally have d:"degree (x \<ominus>\<^bsub>P\<^esub> y) < degree f" by simp

  assume "poly_mod_ring_iso R f x = poly_mod_ring_iso R f y"
  hence "I +>\<^bsub>P\<^esub> x = I +>\<^bsub>P\<^esub> y" unfolding poly_mod_ring_iso_def by simp
  hence "x \<ominus>\<^bsub>P\<^esub> y \<in> I" using x y by (subst d.quotient_eq_iff_same_a_r_cos[OF i.ideal_axioms]) auto
  hence "f pdivides\<^bsub>ring_of R\<^esub> (x \<ominus>\<^bsub>P\<^esub> y)"
    using f_carr x(1) y d.m_comm unfolding cgenideal_def pdivides_def factor_def by auto
  hence "(x \<ominus>\<^bsub>P\<^esub> y) = [] \<or> degree (x \<ominus>\<^bsub>P\<^esub> y) \<ge> degree f"
    using x(1) y(1) f_carr pdivides_imp_degree_le[OF carrier_is_subring] by (meson d.minus_closed)
  hence "(x \<ominus>\<^bsub>P\<^esub> y) = \<zero>\<^bsub>P\<^esub>" unfolding univ_poly_zero using d by simp
  thus "x = y" using x(1) y(1) by simp
qed

lemma poly_mod_iso_ring_bij:
  "bij_betw (poly_mod_ring_iso R f) (carrier (ring_of (poly_mod_ring R f))) (carrier (P Quot I))"
  using poly_mod_ring_iso_ran poly_mod_ring_iso_inj unfolding bij_betw_def by simp

lemma poly_mod_iso_ring_bij_2:
  "bij_betw (poly_mod_ring_iso_inv R f) (carrier (P Quot I)) (carrier (ring_of (poly_mod_ring R f)))"
  unfolding poly_mod_ring_iso_inv_def using poly_mod_iso_ring_bij bij_betw_the_inv_into by blast

lemma poly_mod_ring_iso_inv_1:
  assumes "x \<in> carrier (P Quot I)"
  shows "poly_mod_ring_iso R f (poly_mod_ring_iso_inv R f x) = x"
  unfolding poly_mod_ring_iso_inv_def using assms poly_mod_iso_ring_bij
  by (intro f_the_inv_into_f_bij_betw) auto

lemma poly_mod_ring_iso_inv_2:
  assumes "x \<in> carrier (ring_of (poly_mod_ring R f))"
  shows "poly_mod_ring_iso_inv R f (poly_mod_ring_iso R f x) = x"
  unfolding poly_mod_ring_iso_inv_def using assms
  by (intro the_inv_into_f_f poly_mod_ring_iso_inj)

lemma poly_mod_ring_add:
  assumes "x \<in> carrier P"
  assumes "y \<in> carrier P"
  shows "x \<oplus>\<^bsub>ring_of (poly_mod_ring R f)\<^esub> y = pmod (x \<oplus>\<^bsub>P\<^esub> y) f" (is "?L = ?R")
proof -
  have "?L = pmod\<^sub>C R (x \<oplus>\<^bsub>ring_of (poly R)\<^esub> y) f"
    unfolding poly_mod_ring_def ring_of_def using domain_cD[OF d_poly] by simp
  also have "... = ?R"
    using assms unfolding ring_of_poly[OF ring_c] by (intro pmod_c[OF field_R] f_carr) auto
  finally show ?thesis
    by simp
qed

lemma poly_mod_ring_zero: "\<zero>\<^bsub>ring_of (poly_mod_ring R f)\<^esub> = \<zero>\<^bsub>P\<^esub>"
proof-
  have "\<zero>\<^bsub>ring_of (poly_mod_ring R f)\<^esub> = \<zero>\<^bsub>ring_of (poly R)\<^esub>"
    using domain_cD[OF d_poly] unfolding ring_of_def poly_mod_ring_def by simp
  also have "... = \<zero>\<^bsub>P\<^esub>" unfolding ring_of_poly[OF ring_c] by simp
  finally show ?thesis by simp
qed

lemma poly_mod_ring_one: "\<one>\<^bsub>ring_of (poly_mod_ring R f)\<^esub> = \<one>\<^bsub>P\<^esub>"
proof-
  have "\<one>\<^bsub>ring_of (poly_mod_ring R f)\<^esub> = \<one>\<^bsub>ring_of (poly R)\<^esub>"
    using domain_cD[OF d_poly] unfolding ring_of_def poly_mod_ring_def by simp
  also have "... = \<one>\<^bsub>P\<^esub>" unfolding ring_of_poly[OF ring_c] by simp
  finally show "\<one>\<^bsub>ring_of (poly_mod_ring R f)\<^esub> = \<one>\<^bsub>P\<^esub>" by simp
qed

lemma poly_mod_ring_mult:
  assumes "x \<in> carrier P"
  assumes "y \<in> carrier P"
  shows "x \<otimes>\<^bsub>ring_of (poly_mod_ring R f)\<^esub> y = pmod (x \<otimes>\<^bsub>P\<^esub> y) f" (is "?L = ?R")
proof -
  have "?L = pmod\<^sub>C R (x \<otimes>\<^bsub>ring_of (poly R)\<^esub> y) f"
    unfolding poly_mod_ring_def ring_of_def using domain_cD[OF d_poly] by simp
  also have "... = ?R"
    using assms unfolding poly_mod_ring_carr_1 ring_of_poly[OF ring_c]
    by (intro pmod_c[OF field_R] f_carr) auto
  finally show ?thesis
    by simp
qed

lemma poly_mod_ring_iso_inv:
  "poly_mod_ring_iso_inv R f \<in> ring_iso (P Quot I) (ring_of (poly_mod_ring R f))"
  (is "?f \<in> ring_iso ?S ?T")
proof (rule ring_iso_memI)
  fix x assume "x \<in> carrier ?S"
  thus "?f x \<in> carrier ?T" using bij_betw_apply[OF poly_mod_iso_ring_bij_2] by auto
next
  fix x y assume x:"x \<in> carrier ?S" and y: "y \<in> carrier ?S"
  have "?f x \<in> carrier (ring_of (poly_mod_ring R f))"
    by (rule bij_betw_apply[OF poly_mod_iso_ring_bij_2 x])
  hence x':"?f x \<in> carrier P" unfolding poly_mod_ring_carr_1 by simp
  have "?f y \<in> carrier (ring_of (poly_mod_ring R f))"
    by (rule bij_betw_apply[OF poly_mod_iso_ring_bij_2 y])
  hence y':"?f y \<in> carrier P" unfolding poly_mod_ring_carr_1 by simp

  have 0:"?f x \<otimes>\<^bsub>?T\<^esub> ?f y = pmod (?f x \<otimes>\<^bsub>P\<^esub> ?f y) f"
    by (intro poly_mod_ring_mult x' y')
  also have "... \<in> carrier (ring_of (poly_mod_ring R f))"
    using x' y' by (intro poly_mod_ring_carr) auto
  finally have xy: "?f x \<otimes>\<^bsub>?T\<^esub> ?f y \<in> carrier (ring_of (poly_mod_ring R f))" by simp

  have "?f (x \<otimes>\<^bsub>?S\<^esub> y) = ?f (poly_mod_ring_iso R f (?f x) \<otimes>\<^bsub>?S\<^esub> poly_mod_ring_iso R f (?f y))"
    using x y by (simp add:poly_mod_ring_iso_inv_1)
  also have "... = ?f ((I +>\<^bsub>P\<^esub> (?f x)) \<otimes>\<^bsub>?S\<^esub> (I +>\<^bsub>P\<^esub> (?f y)))"
    unfolding poly_mod_ring_iso_def by simp
  also have "... = ?f (I +>\<^bsub>P\<^esub> (?f x \<otimes>\<^bsub>P\<^esub> ?f y))"
    using x' y' by simp
  also have "... = ?f (I +>\<^bsub>P\<^esub> (pmod (?f x \<otimes>\<^bsub>P\<^esub> ?f y) f))"
    using x' y' by (subst ideal_mod) auto
  also have "... = ?f (I +>\<^bsub>P\<^esub> (?f x \<otimes>\<^bsub>?T\<^esub> ?f y))"
    unfolding 0 by simp
  also have "... = ?f (poly_mod_ring_iso R f (?f x \<otimes>\<^bsub>?T\<^esub> ?f y))"
    unfolding poly_mod_ring_iso_def by simp
  also have "... = ?f x \<otimes>\<^bsub>?T\<^esub> ?f y"
    using xy by (intro poly_mod_ring_iso_inv_2)
  finally show "?f (x \<otimes>\<^bsub>?S\<^esub> y) = ?f x \<otimes>\<^bsub>?T\<^esub> ?f y" by simp
next
  fix x y assume x:"x \<in> carrier ?S" and y: "y \<in> carrier ?S"
  have "?f x \<in> carrier (ring_of (poly_mod_ring R f))"
    by (rule bij_betw_apply[OF poly_mod_iso_ring_bij_2 x])
  hence x':"?f x \<in> carrier P" unfolding poly_mod_ring_carr_1 by simp
  have "?f y \<in> carrier (ring_of (poly_mod_ring R f))"
    by (rule bij_betw_apply[OF poly_mod_iso_ring_bij_2 y])
  hence y':"?f y \<in> carrier P" unfolding poly_mod_ring_carr_1 by simp

  have 0:"?f x \<oplus>\<^bsub>?T\<^esub> ?f y = pmod (?f x \<oplus>\<^bsub>P\<^esub> ?f y) f"  by (intro poly_mod_ring_add x' y')
  also have "... \<in> carrier (ring_of (poly_mod_ring R f))"
    using x' y' by (intro poly_mod_ring_carr) auto
  finally have xy: "?f x \<oplus>\<^bsub>?T\<^esub> ?f y \<in> carrier (ring_of (poly_mod_ring R f))" by simp

  have "?f (x \<oplus>\<^bsub>?S\<^esub> y) = ?f (poly_mod_ring_iso R f (?f x) \<oplus>\<^bsub>?S\<^esub> poly_mod_ring_iso R f (?f y))"
    using x y by (simp add:poly_mod_ring_iso_inv_1)
  also have "... = ?f ((I +>\<^bsub>P\<^esub> (?f x)) \<oplus>\<^bsub>?S\<^esub> (I +>\<^bsub>P\<^esub> (?f y)))"
    unfolding poly_mod_ring_iso_def by simp
  also have "... = ?f (I +>\<^bsub>P\<^esub> (?f x \<oplus>\<^bsub>P\<^esub> ?f y))"
    using x' y' by simp
  also have "... = ?f (I +>\<^bsub>P\<^esub> (pmod (?f x \<oplus>\<^bsub>P\<^esub> ?f y) f))"
    using x' y' by (subst ideal_mod) auto
  also have "... = ?f (I +>\<^bsub>P\<^esub> (?f x \<oplus>\<^bsub>?T\<^esub> ?f y))"
    unfolding 0 by simp
  also have "... = ?f (poly_mod_ring_iso R f (?f x \<oplus>\<^bsub>?T\<^esub> ?f y))"
    unfolding poly_mod_ring_iso_def by simp
  also have "... = ?f x \<oplus>\<^bsub>?T\<^esub> ?f y"
    using xy by (intro poly_mod_ring_iso_inv_2)
  finally show "?f (x \<oplus>\<^bsub>?S\<^esub> y) = ?f x \<oplus>\<^bsub>?T\<^esub> ?f y" by simp
next
  have "poly_mod_ring_iso R f \<one>\<^bsub>ring_of (poly_mod_ring R f)\<^esub> = (I +>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
    unfolding poly_mod_ring_one poly_mod_ring_iso_def by simp
  also have "... = \<one>\<^bsub>P Quot I\<^esub>" using s.hom_one by simp
  finally have "poly_mod_ring_iso R f \<one>\<^bsub>ring_of (poly_mod_ring R f)\<^esub> = \<one>\<^bsub>P Quot I\<^esub>" by simp
  moreover have "degree \<one>\<^bsub>P\<^esub> < degree f"
    using deg_f unfolding univ_poly_one by simp
  hence "\<one>\<^bsub>ring_of (poly_mod_ring R f)\<^esub> \<in> carrier (ring_of (poly_mod_ring R f))"
    unfolding poly_mod_ring_one poly_mod_ring_carr_1 by simp
  ultimately show "?f (\<one>\<^bsub>?S\<^esub>) = \<one>\<^bsub>?T\<^esub>"
    unfolding poly_mod_ring_iso_inv_def by (intro the_inv_into_f_eq poly_mod_ring_iso_inj)
next
  show "bij_betw ?f (carrier ?S) (carrier ?T)" by (rule poly_mod_iso_ring_bij_2)
qed

lemma cring_poly_mod_ring_1:
  shows "ring_of (poly_mod_ring R f)\<lparr>zero := poly_mod_ring_iso_inv R f \<zero>\<^bsub>P Quot I\<^esub>\<rparr> =
    ring_of (poly_mod_ring R f)"
    and  "cring (ring_of (poly_mod_ring R f))"
proof -
  let ?f = "poly_mod_ring_iso_inv R f"

  have "poly_mod_ring_iso R f \<zero>\<^bsub>P\<^esub> = \<zero>\<^bsub>P Quot PIdl\<^bsub>P\<^esub> f\<^esub>"
    unfolding poly_mod_ring_iso_def by simp
  moreover have "[] \<in> carrier P" using univ_poly_zero[where K="carrier (ring_of R)"] by auto
  ultimately have "?f \<zero>\<^bsub>P Quot I\<^esub> = \<zero>\<^bsub>P\<^esub>"
    unfolding univ_poly_zero poly_mod_ring_iso_inv_def using deg_f
    by (intro the_inv_into_f_eq bij_betw_imp_inj_on[OF poly_mod_iso_ring_bij])
      (simp_all add:add:poly_mod_ring_carr_1)
  also have "... = 0\<^sub>C\<^bsub>poly R\<^esub>" using ring_of_poly[OF ring_c] domain_cD[OF d_poly] by auto
  finally have "?f \<zero>\<^bsub>P Quot I\<^esub> = 0\<^sub>C\<^bsub>poly R\<^esub>" by simp
  thus "ring_of (poly_mod_ring R f)\<lparr>zero := ?f \<zero>\<^bsub>P Quot I\<^esub>\<rparr> = ring_of (poly_mod_ring R f)"
    unfolding ring_of_def poly_mod_ring_def by auto
  thus "cring (ring_of (poly_mod_ring R f))"
    using cr.ring_iso_imp_img_cring[OF poly_mod_ring_iso_inv] by simp
qed

interpretation cr_p: cring "(ring_of (poly_mod_ring R f))"
  by (rule cring_poly_mod_ring_1)

lemma cring_c_poly_mod_ring: "cring\<^sub>C (poly_mod_ring R f)"
proof -
  let ?P = "ring_of (poly_mod_ring R f)"
  have "-\<^sub>C\<^bsub>poly_mod_ring R f\<^esub> x = \<ominus>\<^bsub>ring_of (poly_mod_ring R f)\<^esub> x" (is "?L = ?R")
    if "x \<in> carrier (ring_of (poly_mod_ring R f))" for x
  proof (rule cr_p.minus_equality[symmetric, OF _ that])
    have "-\<^sub>C\<^bsub>poly_mod_ring R f\<^esub> x = -\<^sub>C\<^bsub>poly R\<^esub> x" unfolding poly_mod_ring_def by simp
    also have "... = \<ominus>\<^bsub>P\<^esub> x" using that unfolding poly_mod_ring_carr_1
      by (subst domain_cD[OF d_poly]) (simp_all add:ring_of_poly[OF ring_c])
    finally have 0:"-\<^sub>C\<^bsub>poly_mod_ring R f\<^esub> x = \<ominus>\<^bsub>P\<^esub> x" by simp

    have 1:"\<ominus>\<^bsub>P\<^esub> x \<in>  carrier (ring_of (poly_mod_ring R f))"
      using that univ_poly_a_inv_degree[OF carrier_is_subring] unfolding poly_mod_ring_carr_1
      by auto

    have "-\<^sub>C\<^bsub>poly_mod_ring R f\<^esub> x \<oplus>\<^bsub>?P\<^esub> x = pmod (\<ominus>\<^bsub>P\<^esub> x \<oplus>\<^bsub>P\<^esub> x) f"
      using that 1 unfolding 0 poly_mod_ring_carr_1 by (intro poly_mod_ring_add) auto
    also have "... = pmod \<zero>\<^bsub>P\<^esub> f"
      using that unfolding poly_mod_ring_carr_1 by simp algebra
    also have "... = []"
      unfolding univ_poly_zero using carrier_is_subfield f_carr long_division_zero(2) by presburger
    also have "... =  \<zero>\<^bsub>?P\<^esub>" by (simp add:poly_mod_ring_def ring_of_def poly_def)
    finally show "-\<^sub>C\<^bsub>poly_mod_ring R f\<^esub> x \<oplus>\<^bsub>?P\<^esub> x = \<zero>\<^bsub>?P\<^esub>" by simp

    show " -\<^sub>C\<^bsub>poly_mod_ring R f\<^esub> x \<in> carrier (ring_of (poly_mod_ring R f))"
      unfolding 0 by (rule 1)
  qed
  moreover have "x \<inverse>\<^sub>C\<^bsub>poly_mod_ring R f\<^esub> = inv\<^bsub>ring_of (poly_mod_ring R f)\<^esub> x"
    if x_unit: "x \<in> Units (ring_of (poly_mod_ring R f))" for x
  proof (rule cr_p.comm_inv_char[symmetric])
    show x_carr: "x \<in> carrier (ring_of (poly_mod_ring R f))"
      using that unfolding Units_def by auto

    obtain y where y:"x \<otimes>\<^bsub>ring_of (poly_mod_ring R f)\<^esub> y = \<one>\<^bsub>ring_of (poly_mod_ring R f)\<^esub>"
       and y_carr: "y \<in> carrier (ring_of (poly_mod_ring R f))"
      using x_unit unfolding Units_def by auto

    have "pmod (x \<otimes>\<^bsub>P\<^esub> y) f =x \<otimes>\<^bsub>ring_of (poly_mod_ring R f)\<^esub> y"
      using x_carr y_carr by (intro poly_mod_ring_mult[symmetric]) (auto simp:poly_mod_ring_carr_1)
    also have "... = \<one>\<^bsub>P\<^esub>"
      unfolding y poly_mod_ring_one by simp
    finally have 1:"pmod (x \<otimes>\<^bsub>P\<^esub> y) f = \<one>\<^bsub>P\<^esub>" by simp

    have "pcoprime\<^bsub>ring_of R\<^esub> (x \<otimes>\<^bsub>P\<^esub> y) f = pcoprime\<^bsub>ring_of R\<^esub> f (pmod (x \<otimes>\<^bsub>P\<^esub> y) f)"
      using x_carr y_carr f_carr unfolding poly_mod_ring_carr_1 by (intro pcoprime_step) auto
    also have "... = pcoprime \<^bsub>ring_of R\<^esub> f  \<one>\<^bsub>P\<^esub>" unfolding 1 by simp
    also have "... = True" using pcoprime_one by simp
    finally have "pcoprime\<^bsub>ring_of R\<^esub> (x \<otimes>\<^bsub>P\<^esub> y) f" by simp
    hence "pcoprime\<^bsub>ring_of R\<^esub> x f"
      using x_carr y_carr f_carr pcoprime_left_factor unfolding poly_mod_ring_carr_1 by blast
    hence 2:"length (snd ( ext_euclidean R x f)) = 1"
      using f_carr x_carr pcoprime_c[OF field_R] unfolding poly_mod_ring_carr_1 pcoprime\<^sub>C.simps
      by auto

    obtain u v r where uvr_def: "((u,v),r) = ext_euclidean R x f"  by (metis surj_pair)

    have x_carr': "x \<in> carrier P" using x_carr unfolding poly_mod_ring_carr_1 by auto
    have r_eq:"r = x \<otimes>\<^bsub>P\<^esub> u \<oplus>\<^bsub>P\<^esub> f \<otimes>\<^bsub>P\<^esub> v" and ruv_carr: "{r, u, v} \<subseteq> carrier P"
      using uvr_def[symmetric] ext_euclidean[OF field_R x_carr' f_carr] by auto

    have "length r = 1" using 2 uvr_def[symmetric] by simp
    hence 3:"r = [hd r]" by (cases r) auto
    hence "r \<noteq> \<zero>\<^bsub>P\<^esub>" unfolding univ_poly_zero by auto
    hence "hd r \<in> carrier (ring_of R) - {\<zero>\<^bsub>ring_of R\<^esub>}"
      using ruv_carr by (intro lead_coeff_carr) auto
    hence r_unit: "r \<in> Units P" using 3 univ_poly_units[OF carrier_is_subfield] by auto
    hence inv_r_carr: "inv\<^bsub>P\<^esub> r \<in> carrier P" by simp

    have 0: "x \<inverse>\<^sub>C\<^bsub>poly_mod_ring R f\<^esub> = pmod\<^sub>C R (r \<inverse>\<^sub>C\<^bsub>poly R\<^esub> *\<^sub>C\<^bsub>poly R\<^esub> u) f"
      by (simp add:poly_mod_ring_def uvr_def[symmetric])
    also have "... = pmod\<^sub>C R (inv\<^bsub>P\<^esub> r \<otimes>\<^bsub>P\<^esub> u) f"
      using r_unit unfolding domain_cD[OF d_poly]
      by (subst domain_cD[OF d_poly]) (simp_all add:ring_of_poly[OF ring_c])
    also have "... = pmod (inv\<^bsub>P\<^esub> r \<otimes>\<^bsub>P\<^esub> u) f"
      using ruv_carr inv_r_carr by (intro pmod_c[OF field_R] f_carr) simp
    finally have 0: "x \<inverse>\<^sub>C\<^bsub>poly_mod_ring R f\<^esub> = pmod (inv\<^bsub>P\<^esub> r \<otimes>\<^bsub>P\<^esub> u) f"
      by simp

    show "x \<inverse>\<^sub>C\<^bsub>poly_mod_ring R f\<^esub> \<in> carrier (ring_of (poly_mod_ring R f))"
      using ruv_carr r_unit unfolding 0 by (intro poly_mod_ring_carr) simp

    have 4: "degree \<one>\<^bsub>P\<^esub> < degree f" unfolding univ_poly_one using deg_f by auto

    have "f divides\<^bsub>P\<^esub> inv\<^bsub>P\<^esub> r \<otimes>\<^bsub>P\<^esub> f \<otimes>\<^bsub>P\<^esub> v"
      using inv_r_carr ruv_carr  f_carr
      by (intro dividesI[where c="inv\<^bsub>P\<^esub> r \<otimes>\<^bsub>P\<^esub> v"]) (simp_all, algebra)
    hence 5: "pmod (inv\<^bsub>P\<^esub> r \<otimes>\<^bsub>P\<^esub> f \<otimes>\<^bsub>P\<^esub> v) f = []"
      using f_carr ruv_carr inv_r_carr
      by (intro  iffD2[OF pmod_zero_iff_pdivides[OF carrier_is_subfield]]) (auto simp:pdivides_def)

    have "x \<otimes>\<^bsub>?P\<^esub> x \<inverse>\<^sub>C\<^bsub>poly_mod_ring R f\<^esub> = pmod (x \<otimes>\<^bsub>P\<^esub> pmod (inv\<^bsub>P\<^esub> r \<otimes>\<^bsub>P\<^esub> u) f) f"
      using ruv_carr inv_r_carr f_carr unfolding 0
      by (intro poly_mod_ring_mult x_carr' long_division_closed[OF carrier_is_subfield]) simp_all
    also have "... = pmod (x \<otimes>\<^bsub>P\<^esub> (inv\<^bsub>P\<^esub> r \<otimes>\<^bsub>P\<^esub> u)) f"
      using ruv_carr inv_r_carr f_carr by (intro pmod_mult_right[symmetric] x_carr') auto
    also have "... = pmod (inv\<^bsub>P\<^esub> r \<otimes>\<^bsub>P\<^esub> (x \<otimes>\<^bsub>P\<^esub> u)) f"
      using x_carr' ruv_carr inv_r_carr by (intro arg_cong2[where f="pmod"] refl) (simp, algebra)
    also have "... = pmod (inv\<^bsub>P\<^esub> r \<otimes>\<^bsub>P\<^esub> (r \<ominus>\<^bsub>P\<^esub> f \<otimes>\<^bsub>P\<^esub> v)) f" using ruv_carr f_carr x_carr'
      by (intro arg_cong2[where f="pmod"] arg_cong2[where f="(\<otimes>\<^bsub>P\<^esub>)"] refl) (simp add:r_eq, algebra)
    also have "... = pmod (inv\<^bsub>P\<^esub> r \<otimes>\<^bsub>P\<^esub> r \<ominus>\<^bsub>P\<^esub> inv\<^bsub>P\<^esub> r \<otimes>\<^bsub>P\<^esub> f \<otimes>\<^bsub>P\<^esub> v) f"
      using ruv_carr inv_r_carr f_carr by (intro arg_cong2[where f="pmod"] refl) (simp, algebra)
    also have "... = pmod \<one>\<^bsub>P\<^esub> f \<oplus>\<^bsub>P\<^esub> pmod (\<ominus>\<^bsub>P\<^esub> (inv\<^bsub>P\<^esub> r \<otimes>\<^bsub>P\<^esub> f \<otimes>\<^bsub>P\<^esub> v)) f"
      using ruv_carr inv_r_carr f_carr  unfolding d.Units_l_inv[OF r_unit] a_minus_def
      by (intro long_division_add[OF carrier_is_subfield]) simp_all
    also have "... = \<one>\<^bsub>P\<^esub> \<ominus>\<^bsub>P\<^esub> pmod (inv\<^bsub>P\<^esub> r \<otimes>\<^bsub>P\<^esub> f \<otimes>\<^bsub>P\<^esub> v) f"
      using ruv_carr f_carr inv_r_carr unfolding a_minus_def
      by (intro arg_cong2[where f="(\<oplus>\<^bsub>P\<^esub>)"] pmod_const[OF carrier_is_subfield]
          long_division_a_inv[OF carrier_is_subfield] 4) simp_all
    also have "... = \<one>\<^bsub>P\<^esub> \<ominus>\<^bsub>P\<^esub> \<zero>\<^bsub>P\<^esub>" unfolding 5 univ_poly_zero by simp
    also have "... =  \<one>\<^bsub>ring_of (poly_mod_ring R f)\<^esub>" unfolding poly_mod_ring_one by algebra
    finally show "x \<otimes>\<^bsub>ring_of (poly_mod_ring R f)\<^esub> x \<inverse>\<^sub>C\<^bsub>poly_mod_ring R f\<^esub> = \<one>\<^bsub>?P\<^esub>" by simp
  qed
  ultimately show ?thesis using cring_poly_mod_ring_1 by (intro cring_cI)
qed


end

lemma field_c_poly_mod_ring:
  assumes field_R: "field\<^sub>C R"
  assumes "monic_irreducible_poly (ring_of R) f"
  shows "field\<^sub>C (poly_mod_ring R f)"
proof -
  interpret field "ring_of R" using field_R unfolding field\<^sub>C_def by auto

  have f_carr: "f \<in> carrier (poly_ring (ring_of R))"
    using assms(2) monic_poly_carr unfolding monic_irreducible_poly_def by auto

  have deg_f: "degree f > 0" using monic_poly_min_degree assms(2) by fastforce

  have f_irred: "pirreducible\<^bsub>ring_of R\<^esub> (carrier (ring_of R)) f"
    using assms(2) unfolding monic_irreducible_poly_def by auto

  interpret r:field "poly_ring (ring_of R) Quot (PIdl\<^bsub>poly_ring (ring_of R)\<^esub> f)"
    using f_irred f_carr iffD2[OF rupture_is_field_iff_pirreducible[OF carrier_is_subfield]]
    unfolding rupture_def by blast

  have "field (ring_of (poly_mod_ring R f))"
    using r.ring_iso_imp_img_field[OF poly_mod_ring_iso_inv[OF field_R f_carr deg_f]]
    using cring_poly_mod_ring_1(1)[OF field_R f_carr deg_f] by simp
  moreover have "cring\<^sub>C (poly_mod_ring R f)"
    by (rule cring_c_poly_mod_ring[OF field_R f_carr deg_f])
  ultimately show ?thesis unfolding field\<^sub>C_def domain\<^sub>C_def using field.axioms(1) by blast
qed


lemma enum_c_poly_mod_ring:
  assumes "enum\<^sub>C R" "ring\<^sub>C R"
  shows "enum\<^sub>C (poly_mod_ring R f)"
proof (rule enum_cI)
  let ?l = "degree f"
  let ?b = "idx_size R"
  let ?S = "carrier (ring_of (poly_mod_ring R f))"

  note bij_0 = bij_betw_poly_enum[where l="degree f", OF assms(1,2)]
  have "?S = {xs \<in> carrier (poly_ring (ring_of R)). length xs \<le> ?l}"
    unfolding ring_of_poly[OF assms(2),symmetric] poly_mod_ring_def by (simp add:ring_of_def)
  hence bij_1:"bij_betw (poly_enum R (degree f)) {..<idx_size R ^ degree f} ?S"
    using bij_0 by simp
  hence bij_2:"bij_betw (idx_enum (poly_mod_ring R f)) {..<idx_size R^degree f} ?S"
    unfolding poly_mod_ring_def by simp

  have "order (ring_of (poly_mod_ring R f)) = card ?S"
    unfolding Coset.order_def by simp
  also have "... = card {..<idx_size R ^ degree f}" using bij_2 by (metis bij_betw_same_card)
  finally have ord_poly_mod_ring: "order (ring_of (poly_mod_ring R f)) = idx_size R^degree f"
    by simp

  show "finite ?S" using bij_2 bij_betw_finite by blast
  show "idx_size (poly_mod_ring R f) = order (ring_of (poly_mod_ring R f))"
    unfolding ord_poly_mod_ring by (simp add:poly_mod_ring_def)
  show "bij_betw (idx_enum (poly_mod_ring R f)) {..<order (ring_of (poly_mod_ring R f))} ?S"
    using bij_2 ord_poly_mod_ring by auto
  show "idx_enum_inv (poly_mod_ring R f) (idx_enum (poly_mod_ring R f) x) = x" (is "?L = _ ")
    if "x < order (ring_of (poly_mod_ring R f))" for x
  proof -
    have "?L = poly_enum_inv R (degree f) (poly_enum R (degree f) x)"
      unfolding poly_mod_ring_def by simp
    also have "... = the_inv_into {..<?b ^ ?l} (poly_enum R ?l) (poly_enum R ?l x)"
      using that ord_poly_mod_ring
      by (intro poly_enum_inv[OF assms(1,2),symmetric] bij_betw_apply[OF bij_0]) auto
    also have "... = x"
      using that ord_poly_mod_ring by (intro the_inv_into_f_f bij_betw_imp_inj_on[OF bij_0]) auto
    finally show ?thesis by simp
  qed
qed

end