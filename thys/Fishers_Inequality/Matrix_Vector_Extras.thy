(* Title: Matrix_Vector_Extras.thy 
   Author: Chelsea Edmonds
*)
section \<open> Matrix and Vector Additions \<close>

theory Matrix_Vector_Extras imports Set_Multiset_Extras Jordan_Normal_Form.Matrix 
Design_Theory.Multisets_Extras "Groebner_Bases.Macaulay_Matrix" "Polynomial_Factorization.Missing_List"
begin


subsection \<open>Vector Extras\<close>
text \<open>For ease of use, a number of additions to the existing vector library as initially developed
in the JNF AFP Entry, are given below\<close>

text \<open>We define the concept of summing up elements of a vector \<close>

definition (in comm_monoid_add) sum_vec :: "'a vec \<Rightarrow> 'a" where
"sum_vec v \<equiv> sum (\<lambda> i . v $ i) {0..<dim_vec v}"

lemma sum_vec_vNil[simp]: "sum_vec vNil = 0"
  by (simp add: sum_vec_def)

lemma sum_vec_vCons: "sum_vec (vCons a v) = a + sum_vec v"
proof -
  have 0: "a = (vCons a v) $ 0"
    by simp 
  have "sum_vec v = sum (\<lambda> i . v $ i) {0..<dim_vec v}" by (simp add: sum_vec_def)
  also have "... = sum (\<lambda> i . (vCons a v) $ Suc i) {0..< dim_vec v}"
    by force
  also have "... = sum (\<lambda> i . (vCons a v) $ i) {Suc 0..< (Suc (dim_vec v))}"
    by (metis sum.shift_bounds_Suc_ivl)  
  finally have sum: "sum_vec v = sum (\<lambda> i . (vCons a v) $ i) {Suc 0..< dim_vec (vCons a v)}" by simp
  have "sum_vec (vCons a v) = sum (\<lambda> i . (vCons a v) $ i){0..< dim_vec (vCons a v)}" 
    by (simp add: sum_vec_def)
  then have "sum_vec (vCons a v) = (vCons a v) $ 0 + sum (\<lambda> i . (vCons a v) $ i){Suc 0..< dim_vec (vCons a v)}"
    by (metis dim_vec_vCons sum.atLeast_Suc_lessThan zero_less_Suc) 
  thus ?thesis using sum 0 by simp
qed

lemma sum_vec_list: "sum_list (list_of_vec v) = sum_vec v"
  by (induct v)(simp_all add: sum_vec_vCons)

lemma sum_vec_mset: "sum_vec v = (\<Sum> x \<in># (mset (list_of_vec v)) . x)"
  by (simp add: sum_vec_list)

lemma dim_vec_vCons_ne_0: "dim_vec (vCons a v) > 0"
  by (cases v) simp_all

lemma sum_vec_vCons_lt: 
  assumes "\<And> i. i < dim_vec (vCons a v) \<Longrightarrow> (vCons a v) $ i \<le> (n ::int)"
  assumes "sum_vec v \<le> m"
  shows "sum_vec (vCons a v) \<le> n + m"
proof -
  have split: "sum_vec (vCons a v) = a + sum_vec v" by (simp add: sum_vec_vCons)
  have a: "(vCons a v) $ 0 = a" by simp
  then have "0 < dim_vec (vCons a v)" using dim_vec_vCons_ne_0 by simp
  then have "a \<le> n" using assms by (metis a) 
  thus ?thesis using split assms
    by (simp add: add_mono) 
qed

lemma sum_vec_one_zero: 
  assumes "\<And> i. i < dim_vec (v :: int vec) \<Longrightarrow> v $ i \<le> (1 ::int)"
  shows "sum_vec v \<le> dim_vec v"
  using assms 
proof (induct v)
  case vNil
  then show ?case by simp
next
  case (vCons a v)
  then have "(\<And> i. i < dim_vec v \<Longrightarrow> v $ i \<le> (1 ::int))"
    using vCons.prems by force
  then have lt: "sum_vec v \<le> int (dim_vec v)" by (simp add: vCons.hyps)  
  then show ?case using sum_vec_vCons_lt lt vCons.prems by simp
qed

text \<open>Definition to convert a vector to a multiset \<close>

definition vec_mset:: "'a vec \<Rightarrow> 'a multiset" where
"vec_mset v \<equiv> image_mset (vec_index v) (mset_set {..<dim_vec v})"

lemma vec_elem_exists_mset: "(\<exists> i \<in> {..<dim_vec v}. v $ i = x) \<longleftrightarrow> x \<in># vec_mset v"
  by (auto simp add: vec_mset_def)

lemma mset_vec_same_size: "dim_vec v = size (vec_mset v)"
  by (simp add: vec_mset_def)

lemma mset_vec_eq_mset_list: "vec_mset v = mset (list_of_vec v)"
  by (auto simp add: vec_mset_def)
  (metis list_of_vec_map mset_map mset_set_upto_eq_mset_upto)

lemma vec_mset_img_map: "image_mset f (mset (xs)) = vec_mset (map_vec f (vec_of_list xs))"
  by (metis list_vec mset_map mset_vec_eq_mset_list vec_of_list_map)

lemma vec_mset_vNil: "vec_mset vNil = {#}" 
  by (simp add: vec_mset_def)

lemma vec_mset_vCons: "vec_mset (vCons x v) = add_mset x (vec_mset v)"
proof -
  have "vec_mset (vCons x v) = mset (list_of_vec (vCons x v))"
    by (simp add: mset_vec_eq_mset_list)
  then have "mset (list_of_vec (vCons x v)) = add_mset x (mset (list_of_vec v))"
    by simp 
  thus ?thesis
    by (metis mset_vec_eq_mset_list) 
qed

lemma vec_mset_set: "vec_set v = set_mset (vec_mset v)"
  by (simp add: mset_vec_eq_mset_list set_list_of_vec)

lemma vCons_set_contains_in: "a \<in> set\<^sub>v v \<Longrightarrow> set\<^sub>v (vCons a v) = set\<^sub>v v"
  by (metis remdups_mset_singleton_sum set_mset_remdups_mset vec_mset_set vec_mset_vCons)

lemma vCons_set_contains_add: "a \<notin> set\<^sub>v v \<Longrightarrow> set\<^sub>v (vCons a v) = set\<^sub>v v \<union> {a}"
  using vec_mset_set vec_mset_vCons
  by (metis Un_insert_right set_mset_add_mset_insert sup_bot_right) 

lemma setv_vec_mset_not_in_iff: "a \<notin> set\<^sub>v v \<longleftrightarrow> a \<notin># vec_mset v"
  by (simp add: vec_mset_set)

text \<open>Abbreviation for counting occurrences of an element in a vector \<close>

abbreviation "count_vec v a \<equiv> count (vec_mset v) a"

lemma vec_count_lt_dim: "count_vec v a \<le> dim_vec v"
  by (metis mset_vec_same_size order_refl set_count_size_min)

lemma count_vec_empty: "dim_vec v = 0 \<Longrightarrow> count_vec v a = 0"
  by (simp add: mset_vec_same_size)

lemma count_vec_vNil: "count_vec vNil a = 0"
  by (simp add: vec_mset_def)

lemma count_vec_vCons: "count_vec (vCons aa v) a = (if (aa = a) then count_vec v a + 1 else count_vec v a)"
  by(simp add: vec_mset_vCons)

lemma elem_exists_count_min: "\<exists> i \<in>{..<dim_vec v}. v $ i = x \<Longrightarrow> count_vec v x \<ge> 1"
  by (simp add: vec_elem_exists_mset)

lemma count_vec_count_mset: "vec_mset v = image_mset f A \<Longrightarrow> count_vec v a = count (image_mset f A) a"
  by (simp)

lemma count_vec_alt_list: "count_vec v a = length (filter (\<lambda>y. a = y) (list_of_vec v))"
  by (simp add: mset_vec_eq_mset_list) (metis count_mset)

lemma count_vec_alt: "count_vec v x = card { i. v $ i = x \<and> i< dim_vec v}"
proof -
  have "count_vec v x = count (image_mset (($) v) (mset_set {..<dim_vec v})) x" by (simp add: vec_mset_def)
  also have "... = size {#a \<in># (image_mset (($) v) (mset_set {..<dim_vec v})) . x = a#}"
    by (simp add: filter_mset_eq)
  also have "... = size {#a \<in># (mset_set {..<dim_vec v}) . x = (v $ a) #}"
    by (simp add: filter_mset_image_mset)
  finally have "count_vec v x = card {a \<in> {..<dim_vec v} . x = (v $ a)}" by simp
  thus ?thesis by (smt (verit) Collect_cong lessThan_iff) 
qed

lemma count_vec_sum_ones: 
  fixes v :: "'a :: {ring_1} vec"
  assumes "\<And> i. i < dim_vec v \<Longrightarrow> v $ i = 1 \<or> v $ i = 0"
  shows "of_nat (count_vec v 1) = sum_vec v"
  using assms 
proof (induct v)
  case vNil 
  then show ?case
     by (simp add: vec_mset_vNil)  
 next
  case (vCons a v)
  then have lim: "dim_vec (vCons a v) \<ge> 1"
    by simp 
  have "(\<And> i. i < dim_vec v \<Longrightarrow> v $ i = 1 \<or> v$ i = 0)"
    using vCons.prems by force
  then have hyp: "of_nat (count_vec v 1) = sum_vec v"
    using vCons.hyps by blast 
  have "sum (($) (vCons a v)) {0..<dim_vec (vCons a v)} = sum_vec (vCons a v)" 
    by (simp add: sum_vec_def)
  then have sv: "sum (($) (vCons a v)) {0..<dim_vec (vCons a v)} = sum_vec (v) + a" 
    by (simp add: sum_vec_vCons)
  then show ?case using count_vec_vCons dim_vec_vCons_ne_0 sum_vec_vCons vCons.prems
    by (metis add.commute add_0 hyp of_nat_1 of_nat_add vec_index_vCons_0)
qed

lemma count_vec_two_elems: 
  fixes v :: "'a :: {zero_neq_one} vec"
  assumes "\<And> i. i < dim_vec v \<Longrightarrow> v $ i = 1 \<or> v $ i = 0"
  shows "count_vec v 1 + count_vec v 0 = dim_vec v"
proof -
  have ss: "vec_set v \<subseteq> {0, 1}" using assms by (auto simp add: vec_set_def)
  have "dim_vec v = size (vec_mset v)"
    by (simp add: mset_vec_same_size) 
  have "size (vec_mset v) = (\<Sum> x \<in> (vec_set v) . count (vec_mset v) x)"
    by (simp add: vec_mset_set size_multiset_overloaded_eq) 
  also have  "... = (\<Sum> x \<in> {0, 1} . count (vec_mset v) x)"
    using size_count_mset_ss ss
    by (metis calculation finite.emptyI finite.insertI vec_mset_set)
  finally have "size (vec_mset v) = count (vec_mset v) 0 + count (vec_mset v) 1" by simp
  thus ?thesis
    by (simp add: \<open>dim_vec v = size (vec_mset v)\<close>) 
qed

lemma count_vec_sum_zeros: 
  fixes v :: "'a :: {ring_1} vec"
  assumes "\<And> i. i < dim_vec v \<Longrightarrow> v $ i = 1 \<or> v $ i = 0"
  shows "of_nat (count_vec v 0) = of_nat (dim_vec v) - sum_vec v"
  using count_vec_two_elems assms count_vec_sum_ones
  by (metis add_diff_cancel_left' of_nat_add)  

lemma count_vec_sum_ones_alt: 
  fixes v :: "'a :: {ring_1} vec"
  assumes "vec_set v \<subseteq> {0, 1}"
  shows "of_nat (count_vec v 1) = sum_vec v"
proof -
  have "\<And> i. i < dim_vec v \<Longrightarrow> v $ i = 1 \<or> v $ i = 0" using assms
    by (meson insertE singletonD subsetD vec_setI) 
  thus ?thesis using count_vec_sum_ones 
    by blast 
qed

lemma setv_not_in_count0_iff: "a \<notin> set\<^sub>v v \<longleftrightarrow> count_vec v a = 0"
  using setv_vec_mset_not_in_iff
  by (metis count_eq_zero_iff) 

lemma sum_count_vec: 
  assumes "finite (set\<^sub>v v)"
  shows "(\<Sum> i \<in> set\<^sub>v v. count_vec v i) = dim_vec v"
using assms proof (induct "v")
  case vNil
  then show ?case
    by (simp add: count_vec_empty) 
next
  case (vCons a v)
  then show ?case proof (cases "a \<in> set\<^sub>v v")
    case True
    have cv: "\<And> x. x \<in>(set\<^sub>v v) - {a} \<Longrightarrow> count_vec (vCons a v) x = count_vec v x" 
      using count_vec_vCons by (metis DiffD2 singletonI)
    then have "sum (count_vec (vCons a v)) (set\<^sub>v (vCons a v)) =  sum (count_vec (vCons a v)) (set\<^sub>v v)" 
      using vCons_set_contains_in True by metis
    also have "... = count_vec (vCons a v) a + sum (count_vec (vCons a v)) ((set\<^sub>v v) - {a})" 
      using sum.remove True vCons.prems(1) by (metis vCons_set_contains_in) 
    also have "... = count_vec v a + 1 + sum (count_vec v) ((set\<^sub>v v) - {a})" 
      using cv count_vec_vCons by (metis sum.cong) 
    also have "... = 1 + sum (count_vec v) ((set\<^sub>v v))"
      using sum.remove add.commute vCons.prems vCons_set_contains_in True
      by (metis (no_types, opaque_lifting) ab_semigroup_add_class.add_ac(1))
    also have "... = 1 + dim_vec v" using vCons.hyps
      by (metis True vCons.prems vCons_set_contains_in) 
    finally show ?thesis by simp
  next
    case False
    then have cv: "\<And> x. x \<in>(set\<^sub>v v) \<Longrightarrow> count_vec (vCons a v) x = count_vec v x" 
      using count_vec_vCons by (metis) 
    have f: "finite (set\<^sub>v v)" 
      using vCons.prems False vCons_set_contains_add by (metis Un_infinite) 
    have "sum (count_vec (vCons a v)) (set\<^sub>v (vCons a v)) = 
        count_vec (vCons a v) a + sum (count_vec (vCons a v)) (set\<^sub>v v)" 
      using False vCons_set_contains_add
      by (metis Un_insert_right finite_Un sum.insert sup_bot_right vCons.prems ) 
    also have "... = count_vec v a + 1 + sum (count_vec v) ((set\<^sub>v v) )" 
      using cv count_vec_vCons by (metis sum.cong) 
    also have "... = 1 + sum (count_vec v) ((set\<^sub>v v))" 
      using False setv_not_in_count0_iff by (metis add_0)
    finally show ?thesis using vCons.hyps f by simp
  qed
qed

lemma sum_setv_subset_eq: 
  assumes "finite A"
  assumes "set\<^sub>v v \<subseteq> A"
  shows "(\<Sum> i \<in> set\<^sub>v v. count_vec v i) = (\<Sum> i \<in> A. count_vec v i)"
proof -
  have ni: "\<And> x. x \<notin> set\<^sub>v v \<Longrightarrow> count_vec v x = 0"
    by (simp add: setv_not_in_count0_iff) 
  have "(\<Sum> i \<in> A. count_vec v i) = (\<Sum> i \<in> A - (set\<^sub>v v). count_vec v i) + (\<Sum> i \<in> (set\<^sub>v v). count_vec v i)" 
    using sum.subset_diff assms by auto
  then show ?thesis using ni
    by simp 
qed

lemma sum_count_vec_subset:  "finite A \<Longrightarrow> set\<^sub>v v \<subseteq> A \<Longrightarrow> (\<Sum> i \<in> A. count_vec v i) = dim_vec v"
  using sum_setv_subset_eq sum_count_vec finite_subset by metis 

text \<open>An abbreviation for checking if an element is in a vector \<close>

abbreviation vec_contains :: "'a \<Rightarrow> 'a vec \<Rightarrow> bool" (infix "\<in>$" 50)where 
"a \<in>$ v \<equiv> a \<in> set\<^sub>v v"

lemma vec_set_mset_contains_iff: "a \<in>$ v \<longleftrightarrow> a \<in># vec_mset v"
  by (simp add: vec_mset_def vec_set_def)

lemma vec_contains_count_gt1_iff: "a \<in>$ v \<longleftrightarrow> count_vec v a \<ge> 1"
  by (simp add: vec_set_mset_contains_iff)

lemma vec_contains_obtains_index: 
  assumes "a \<in>$ v"
  obtains i where "i < dim_vec v" and "v $ i = a"
  by (metis assms vec_setE)

lemma vec_count_eq_list_count: "count (mset xs) a = count_vec (vec_of_list xs) a"
  by (simp add: list_vec mset_vec_eq_mset_list) 

lemma vec_contains_col_elements_mat: 
  assumes "j < dim_col M"
  assumes "a \<in>$ col M j"
  shows "a \<in> elements_mat M"
proof -
  have "dim_vec (col M j) = dim_row M" by simp
  then obtain i where ilt: "i < dim_row M" and "(col M j) $ i = a" 
    using vec_setE by (metis assms(2))
  then have "M $$ (i, j) = a"
    by (simp add: assms(1)) 
  thus ?thesis using assms(1) ilt
    by blast
qed

lemma vec_contains_row_elements_mat: 
  assumes "i < dim_row M"
  assumes "a \<in>$ row M i"
  shows "a \<in> elements_mat M"
proof -
  have "dim_vec (row M i) = dim_col M" by simp
  then obtain j where jlt: "j < dim_col M" and "(row M i) $ j = a" using vec_setE
    by (metis assms(2))
  then have "M $$ (i, j) = a"
    by (simp add: assms(1)) 
  thus ?thesis using assms(1) jlt
    by blast
qed

lemma vec_contains_img: "a \<in>$ v \<Longrightarrow> f a \<in>$ (map_vec f v)"
  by (metis index_map_vec(1) index_map_vec(2) vec_contains_obtains_index vec_setI)

text \<open> The existing vector library contains the identity and zero vectors, but no definition 
of a vector where all elements are 1, as defined below \<close>

definition all_ones_vec ::  "nat \<Rightarrow> 'a :: {zero,one} vec" ("u\<^sub>v") where
  "u\<^sub>v n \<equiv> vec n (\<lambda> i. 1)"

lemma dim_vec_all_ones[simp]: "dim_vec (u\<^sub>v n) = n"
  by (simp add: all_ones_vec_def)

lemma all_ones_index [simp]: "i < n \<Longrightarrow> u\<^sub>v n $ i = 1"
  by (simp add: all_ones_vec_def)

lemma dim_vec_mult_vec_mat [simp]: "dim_vec (v \<^sub>v* A) = dim_col A"
  unfolding mult_vec_mat_def by simp

lemma all_ones_vec_smult[simp]: "i < n \<Longrightarrow> ((k :: ('a :: {one, zero, monoid_mult})) \<cdot>\<^sub>v (u\<^sub>v n)) $ i = k"
  by (simp add: smult_vec_def)

text \<open>Extra lemmas on existing vector operations \<close>

lemma smult_scalar_prod_sum: 
  fixes x :: "'a :: {comm_ring_1}" 
  assumes "vx \<in> carrier_vec n"
  assumes "vy \<in> carrier_vec n"
  shows "(\<Sum> i \<in> {0..<n} .((x \<cdot>\<^sub>v vx) $ i) * ((y \<cdot>\<^sub>v vy) $ i)) = x * y * (vx \<bullet> vy)"
proof -
  have "\<And> i . i < n \<Longrightarrow> ((x \<cdot>\<^sub>v vx) $ i) * ((y \<cdot>\<^sub>v vy) $ i) = x * y * (vx $ i) * (vy $ i)" 
    using assms by simp
  then have "(\<Sum> i \<in> {0..<n} .((x \<cdot>\<^sub>v vx) $ i) * ((y \<cdot>\<^sub>v vy) $ i)) = 
      (\<Sum> i \<in> {0..<n} .x * y * (vx $ i) * (vy $ i))" 
    by simp
  also have "... = x * y * (\<Sum> i \<in> {0..<n} . (vx $ i) * (vy $ i))"
    using sum_distrib_left[of "x * y" "(\<lambda> i. (vx $ i) * (vy $ i))" "{0..<n}"]
    by (metis (no_types, lifting) mult.assoc sum.cong) 
  finally have "(\<Sum> i \<in> {0..<n} .((x \<cdot>\<^sub>v vx) $ i) * ((y \<cdot>\<^sub>v vy) $ i)) = x * y * (vx \<bullet> vy)" 
    using scalar_prod_def assms by (metis carrier_vecD) 
  thus ?thesis by simp
qed

lemma scalar_prod_double_sum_fn_vec:
  fixes c :: "nat \<Rightarrow> ('a :: {comm_semiring_0})"
  fixes f :: "nat \<Rightarrow> 'a vec"
  assumes "\<And> j . j < k \<Longrightarrow> dim_vec (f j) = n"
  shows "(vec n (\<lambda>i. \<Sum>j = 0..<k. c j * (f j) $ i)) \<bullet> (vec n (\<lambda>i. \<Sum>j = 0..<k. c j * (f j) $ i)) = 
    (\<Sum> j1 \<in> {0..<k} . c j1 * c j1 * ((f j1) \<bullet> (f j1))) + 
    (\<Sum> j1 \<in> {0..<k} . (\<Sum> j2 \<in> ({0..< k} - {j1}) . c j1 * c j2 * ((f j1) \<bullet> (f j2))))"
proof -
  have sum_simp: "\<And> j1 j2. (\<Sum>l \<in> {0..<n} . c j1 * (f j1) $ l * (c j2 * (f j2) $ l)) = 
    c j1 * c j2 *(\<Sum>l \<in> {0..<n} .  (f j1) $ l * (f j2) $ l)"
  proof -
    fix j1 j2
    have "(\<Sum>l \<in> {0..<n} . c j1 * (f j1) $ l * (c j2 * (f j2) $ l)) = 
        (\<Sum>l \<in> {0..<n} . c j1  * c j2 * (f j1) $ l * (f j2) $ l)"
      using mult.commute sum.cong
      by (smt (z3) ab_semigroup_mult_class.mult_ac(1)) (* SLOW *)
    then show "(\<Sum>l \<in> {0..<n} . c j1 * (f j1) $ l * (c j2 * (f j2) $ l)) = 
        c j1 * c j2 *(\<Sum>l \<in> {0..<n} .  (f j1) $ l * (f j2) $ l)"
      using sum_distrib_left[of " c j1 * c j2" "\<lambda> l. (f j1) $ l * (f j2) $ l" "{0..<n}"]
      by (metis (no_types, lifting) mult.assoc sum.cong) 
  qed
  have "(vec n (\<lambda>i. \<Sum>j = 0..<k. c j * (f j) $ i)) \<bullet> (vec n (\<lambda>i. \<Sum>j = 0..<k. c j * (f j) $ i))
       = (\<Sum> l = 0..<n. (\<Sum>j1 = 0..<k. c j1 * (f j1) $ l) * (\<Sum>j2 = 0..<k. c j2 * (f j2) $ l))"
    unfolding scalar_prod_def by simp
  also have "... = (\<Sum> l \<in> {0..<n} . (\<Sum> j1 \<in> {0..<k} . (\<Sum> j2 \<in> {0..< k}. c j1 * (f j1) $ l *  (c j2 * (f j2) $ l))))" 
    by (metis (no_types) sum_product)
  also have "... = (\<Sum> j1 \<in> {0..<k} . (\<Sum> j2 \<in> {0..<k} . (\<Sum>l \<in> {0..<n} . c j1 * (f j1) $ l * (c j2 * (f j2) $ l))))" 
    using sum_reorder_triple[of "\<lambda> l j1 j2 .(c j1 * (f j1) $ l * (c j2 * (f j2) $ l))" "{0..<k}" "{0..<k}" "{0..<n}"] 
    by simp
  also have "... = (\<Sum> j1 \<in> {0..<k} . (\<Sum> j2 \<in> {0..<k} . c j1 * c j2 * (\<Sum>l \<in> {0..<n} . (f j1) $ l * (f j2) $ l)))" 
    using sum_simp by simp
  also have "... = (\<Sum> j1 \<in> {0..<k} . (\<Sum> j2 \<in> {0..<k} . c j1 * c j2 * ((f j1) \<bullet> (f j2))))" 
    unfolding scalar_prod_def using dim_col assms by simp
  finally show ?thesis
    using double_sum_split_case by fastforce
qed

lemma vec_prod_zero: "(0\<^sub>v n) \<bullet> (0\<^sub>v n) = 0"
  by simp

lemma map_vec_compose: "map_vec f (map_vec g v) = map_vec (f \<circ> g) v"
  by auto

subsection \<open>Matrix Extras\<close>

text \<open>As with vectors, the all ones mat definition defines the concept of a matrix where all 
elements are 1 \<close>

definition all_ones_mat :: "nat \<Rightarrow> 'a :: {zero,one} mat" ("J\<^sub>m") where
  "J\<^sub>m n \<equiv> mat n n (\<lambda> (i,j). 1)"

lemma all_ones_mat_index[simp]: "i < dim_row (J\<^sub>m n) \<Longrightarrow> j < dim_col (J\<^sub>m n) \<Longrightarrow> J\<^sub>m n $$ (i, j)= 1"
  by (simp add: all_ones_mat_def)

lemma all_ones_mat_dim_row[simp]: "dim_row (J\<^sub>m n) = n"
  by (simp add: all_ones_mat_def)

lemma all_ones_mat_dim_col[simp]: "dim_col (J\<^sub>m n) = n"
  by (simp add: all_ones_mat_def)

text \<open>Basic lemmas on existing matrix operations \<close>
lemma index_mult_vec_mat[simp]: "j < dim_col A \<Longrightarrow> (v \<^sub>v* A) $ j = v \<bullet> col A j"
  by (auto simp: mult_vec_mat_def)

lemma transpose_mat_mult_entries: "i < dim_row A \<Longrightarrow> j < dim_row A \<Longrightarrow> 
    (A * A\<^sup>T) $$ (i, j) = (\<Sum>k\<in> {0..<(dim_col A)}. (A $$ (i, k)) * (A $$ (j, k)))"
  by (simp add: times_mat_def scalar_prod_def)

lemma transpose_mat_elems: "elements_mat A = elements_mat A\<^sup>T"
  by fastforce

lemma row_elems_subset_mat: "i < dim_row N \<Longrightarrow> vec_set (row N i) \<subseteq> elements_mat N"
  by (auto simp add: vec_set_def elements_matI)

lemma col_elems_subset_mat: "i < dim_col N \<Longrightarrow> vec_set (col N i) \<subseteq> elements_mat N"
  by (auto simp add: vec_set_def elements_matI)

lemma obtain_row_index: 
  assumes "r \<in> set (rows M)"
  obtains i where "row M i = r" and "i < dim_row M"
  by (metis assms in_set_conv_nth length_rows nth_rows)

lemma row_prop_cond: "(\<And> i. i < dim_row M \<Longrightarrow> P (row M i)) \<Longrightarrow> r \<in> set (rows M) \<Longrightarrow> P r"
  using obtain_row_index by metis 

lemma obtain_col_index: 
  assumes "c \<in> set (cols M)"
  obtains j where "col M j = c" and "j < dim_col M"
  by (metis assms cols_length cols_nth obtain_set_list_item)

lemma col_prop_cond: "(\<And> j. j < dim_col M \<Longrightarrow> P (col M j)) \<Longrightarrow> c \<in> set (cols M) \<Longrightarrow> P c"
  using obtain_col_index by metis  

text \<open> Lemmas on the @{term "map_mat"} definition \<close>

lemma row_map_mat[simp]:
  assumes "i < dim_row A" shows "row (map_mat f A) i = map_vec f (row A i)"
  unfolding map_mat_def map_vec_def using assms by auto

lemma map_vec_mat_rows: "map (map_vec f) (rows M) = rows ((map_mat f) M)"
  by (simp add: map_nth_eq_conv) 

lemma map_vec_mat_cols: "map (map_vec f) (cols M) = cols ((map_mat f) M)"
  by (simp add: map_nth_eq_conv)

lemma map_mat_compose: "map_mat f (map_mat g A) = map_mat (f \<circ> g) A"
  by (auto)

lemmas map_mat_elements = elements_mat_map

text \<open> Reasoning on sets and multisets of matrix elements \<close>
lemma set_cols_carrier: "A \<in> carrier_mat m n \<Longrightarrow> v \<in> set (cols A) \<Longrightarrow> v \<in> carrier_vec m"
  by (auto simp: cols_def)

lemma mset_cols_index_map:  "image_mset (\<lambda> j. col M j) (mset_set {0..< dim_col M}) = mset (cols M)"
  by (simp add: cols_def)

lemma mset_rows_index_map:  "image_mset (\<lambda> i. row M i) (mset_set {0..< dim_row M}) = mset (rows M)"
  by (simp add: rows_def)

lemma index_to_col_card_size_prop: 
  assumes "i < dim_row M"
  assumes "\<And> j. j < dim_col M \<Longrightarrow> P j \<longleftrightarrow> Q (col M j)" 
  shows "card {j . j < dim_col M \<and> P j} = size {#c \<in># (mset (cols M)) . Q c #}"
proof -
  have "card {j . j < dim_col M \<and> P j} = size (mset_set({j \<in> {0..<dim_col M}.  P j}))"
    by simp
  also have "... = size (mset_set({j \<in> {0..<dim_col M}.  Q (col M j)}))"
    using assms(2)
    by (metis lessThan_atLeast0 lessThan_iff)
  also have "... = size (image_mset (\<lambda> j. col M j)  {# j \<in># mset_set {0..< dim_col M} . Q (col M j) #})"
    by simp
  also have "... = size ({# c \<in># (image_mset (\<lambda> j. col M j) (mset_set {0..< dim_col M})) .  Q c #})"
    using image_mset_filter_swap[of "(\<lambda> j. col M j)"  "Q" "(mset_set {0..< dim_col M})"] by simp
  finally have "card {j . j < dim_col M \<and> P j} = size ({# c \<in># (mset (cols M)) .  Q c #})"
    using mset_cols_index_map by metis  
  thus ?thesis by simp
qed

lemma index_to_row_card_size_prop: 
  assumes "j < dim_col M"
  assumes "\<And> i. i < dim_row M \<Longrightarrow> P i \<longleftrightarrow> Q (row M i)" 
  shows "card {i . i < dim_row M \<and> P i} = size {#r \<in># (mset (rows M)) . Q r #}"
proof -
  have "card {i . i < dim_row M \<and> P i} = size (mset_set({i \<in> {0..<dim_row M}.  P i}))"
    by simp
  also have "... = size (mset_set({i \<in> {0..<dim_row M}.  Q (row M i)}))"
    using assms(2)
    by (metis lessThan_atLeast0 lessThan_iff) 
  also have "... = size (image_mset (\<lambda> i. row M i)  {# i \<in># mset_set {0..< dim_row M} . Q (row M i) #})"
    by simp
  also have "... = size ({# r \<in># (image_mset (\<lambda> i. row M i) (mset_set {0..< dim_row M})) .  Q r #})"
    using image_mset_filter_swap[of "(\<lambda> j. row M j)"  "Q" "(mset_set {0..< dim_row M})"] by simp
  finally have "card {j . j < dim_row M \<and> P j} = size ({# c \<in># (mset (rows M)) .  Q c #})"
    using mset_rows_index_map by metis  
  thus ?thesis by simp
qed

lemma setv_row_subset_mat_elems: 
  assumes "v \<in> set (rows M)"
  shows "set\<^sub>v v \<subseteq> elements_mat M" 
proof (intro subsetI)
  fix x assume "x \<in>$ v"
  then obtain i where "v = row M i" and "i < dim_row M"
    by (metis assms obtain_row_index) 
  then show "x \<in> elements_mat M"
    by (metis \<open>x \<in>$ v\<close> vec_contains_row_elements_mat) 
qed

lemma setv_col_subset_mat_elems: 
  assumes "v \<in> set (cols M)"
  shows "set\<^sub>v v \<subseteq> elements_mat M" 
proof (intro subsetI)
  fix x assume "x \<in>$ v"
  then obtain i where "v = col M i" and "i < dim_col M"
    by (metis assms obtain_col_index) 
  then show "x \<in> elements_mat M"
    by (metis \<open>x \<in>$ v\<close> vec_contains_col_elements_mat) 
qed

subsection \<open> Vector and Matrix Homomorphism \<close>

text \<open>We extend on the existing lemmas on homomorphism mappings as applied to vectors and matrices \<close>

context semiring_hom
begin

lemma  vec_hom_smult2: 
  assumes "dim_vec v2 \<le> dim_vec v1"
  shows "hom (v1 \<bullet> v2) = vec\<^sub>h v1 \<bullet> vec\<^sub>h v2"
  unfolding scalar_prod_def using index_map_vec assms by (auto simp add: hom_distribs)

end


lemma map_vec_vCons: "vCons (f a) (map_vec f v) = map_vec f (vCons a v)"
  by (intro eq_vecI, simp_all add: vec_index_vCons)
          
context inj_zero_hom
begin

lemma  vec_hom_zero_iff[simp]: "(map_vec hom x = 0\<^sub>v n) = (x = 0\<^sub>v n)"
proof -
  {
    fix i
    assume i: "i < n" "dim_vec x = n"
    hence "map_vec hom x $ i = 0 \<longleftrightarrow> x $ i = 0"
      using index_map_vec(1)[of i x] by simp
  } note main = this
  show ?thesis unfolding vec_eq_iff by (simp, insert main, auto)
qed

lemma  mat_hom_inj: "map_mat hom A = map_mat hom B \<Longrightarrow> A = B"
  unfolding mat_eq_iff by auto

lemma  vec_hom_inj: "map_vec hom v = map_vec hom w \<Longrightarrow> v = w"
  unfolding vec_eq_iff by auto

lemma  vec_hom_set_distinct_iff: 
  fixes xs :: "'a vec list"
  shows "distinct xs \<longleftrightarrow> distinct (map (map_vec hom) xs)"
  using vec_hom_inj by (induct xs) (auto)

lemma vec_hom_mset: "image_mset hom (vec_mset v) = vec_mset (map_vec hom v)"
  apply (induction v)
   apply (metis mset.simps(1) vec_mset_img_map vec_mset_vNil vec_of_list_Nil)
  by (metis mset_vec_eq_mset_list vec_list vec_mset_img_map)

lemma vec_hom_set: "hom ` set\<^sub>v v = set\<^sub>v (map_vec hom v)"
proof (induct v)
  case vNil
  then show ?case by (metis image_mset_empty set_image_mset vec_hom_zero_iff vec_mset_set vec_mset_vNil zero_vec_zero)
next
  case (vCons a v)
  have "hom ` set\<^sub>v (vCons a v) = hom ` ({a} \<union> set\<^sub>v v)"
    by (metis Un_commute insert_absorb insert_is_Un vCons_set_contains_add vCons_set_contains_in) 
  also have "... = {hom a} \<union> (hom ` (set\<^sub>v v))" by simp
  also have "... = {hom a} \<union> (set\<^sub>v (map_vec hom v))" using vCons.hyps by simp
  also have "... = set\<^sub>v (vCons (hom a) (map_vec hom v))"
    by (metis Un_commute insert_absorb insert_is_Un vCons_set_contains_add vCons_set_contains_in) 
  finally show ?case using map_vec_vCons
    by metis 
qed

end

subsection \<open> Zero One injections and homomorphisms \<close>

text \<open>Define a locale to encapsulate when a function is injective on a certain set (i.e. not
a universal homomorphism for the type\<close>
locale injective_lim =
  fixes A :: "'a set"
  fixes f :: "'a \<Rightarrow> 'b" assumes injectivity_lim: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> f x = f y \<Longrightarrow> x = y"
begin
  lemma eq_iff[simp]: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> f x = f y \<longleftrightarrow> x = y" using injectivity_lim by auto
lemma inj_on_f: "inj_on f A" by (auto intro: inj_onI)

end

sublocale injective \<subseteq> injective_lim Univ
  by(unfold_locales) simp

context injective_lim
begin

lemma mat_hom_inj_lim: 
  assumes "elements_mat M \<subseteq> A" and "elements_mat N \<subseteq> A"
  shows "map_mat f M = map_mat f N \<Longrightarrow> M = N"
  unfolding mat_eq_iff apply auto
  using assms injectivity_lim by blast

lemma vec_hom_inj_lim: assumes "set\<^sub>v v \<subseteq> A" "set\<^sub>v w \<subseteq> A"
  shows "map_vec f v = map_vec f w \<Longrightarrow> v = w"
  unfolding vec_eq_iff apply (auto)
  using vec_setI in_mono assms injectivity_lim by metis 

lemma lim_inj_hom_count_vec: 
  assumes "set\<^sub>v v \<subseteq> A"
  assumes "x \<in> A"
  shows "count_vec v x = count_vec (map_vec f v) (f x)"
using assms proof (induct v)
  case vNil
  have "(map_vec f vNil) = vNil" by auto
  then show ?case
    by (smt (verit) count_vec_vNil)
next
  case (vCons a v)
  have 1: "map_vec f (vCons a v) = vCons (f a) (map_vec f v)"
    by (simp add: map_vec_vCons) 
  then show ?case proof (cases "a = x")
    case True
    have "count_vec (vCons a v) x = count_vec v x + 1"
      by (simp add: True count_vec_vCons)
    then show ?thesis using Un_subset_iff 1 count_vec_vCons vCons.hyps vCons.prems(1) 
          vCons.prems(2) vCons_set_contains_add vCons_set_contains_in
      by metis 
  next
    case False
    then have "count_vec (vCons a v) x = count_vec v x"
      by (simp add: count_vec_vCons)
    then show ?thesis using "1" Un_empty_right Un_insert_right count_vec_vCons insert_absorb insert_subset 
          vCons.hyps vCons.prems(1) vCons.prems(2) vCons_set_contains_add vCons_set_contains_in
      by (metis (no_types, lifting) injectivity_lim)  
  qed
qed

lemma vec_hom_lim_set_distinct_iff: 
  fixes xs :: "'a vec list"
  assumes "\<And> v . v \<in> set (xs) \<Longrightarrow> set\<^sub>v v \<subseteq> A"
  shows "distinct xs \<longleftrightarrow> distinct (map (map_vec f) xs)"
  using assms vec_hom_inj_lim by (induct xs, simp_all) (metis (no_types, lifting) image_iff) 

lemma mat_rows_hom_lim_distinct_iff: 
  assumes "elements_mat M \<subseteq> A"
  shows "distinct (rows M) \<longleftrightarrow> distinct (map (map_vec f) (rows M))"
  apply (intro vec_hom_lim_set_distinct_iff)
  using setv_row_subset_mat_elems assms by blast 

lemma mat_cols_hom_lim_distinct_iff: 
  assumes "elements_mat M \<subseteq> A"
  shows "distinct (cols M) \<longleftrightarrow> distinct (map (map_vec f) (cols M))"
  apply (intro vec_hom_lim_set_distinct_iff)
  using setv_col_subset_mat_elems assms by blast 

end

locale inj_on_01_hom = zero_hom + one_hom + injective_lim "{0, 1}" hom
begin

lemma inj_0_iff: "x \<in> {0, 1} \<Longrightarrow> hom x = 0 \<longleftrightarrow> x = 0"
  by (metis hom_zero insertI1 local.eq_iff)

lemma inj_1_iff: "x \<in> {0, 1} \<Longrightarrow> hom x = 1 \<longleftrightarrow> x = 1"
  using inj_0_iff by fastforce
  
end

context zero_neq_one
begin

definition of_zero_neq_one :: "'b :: {zero_neq_one} \<Rightarrow> 'a" where
"of_zero_neq_one x \<equiv> if (x = 0) then 0 else 1"

lemma of_zero_neq_one_1 [simp]: "of_zero_neq_one 1 = 1"
  by (simp add: of_zero_neq_one_def)

lemma of_zero_neq_one_0 [simp]:  "of_zero_neq_one 0 = 0"
  by (simp add: of_zero_neq_one_def)

lemma of_zero_neq_one_0_iff[iff]: "of_zero_neq_one x = 0 \<longleftrightarrow> x = 0"
  by (simp add: of_zero_neq_one_def)

lemma of_zero_neq_one_lim_eq: "x \<in> {0, 1} \<Longrightarrow> y \<in> {0, 1} \<Longrightarrow> of_zero_neq_one x = of_zero_neq_one y \<longleftrightarrow> x = y"
  by (auto simp add: of_zero_neq_one_def)


end

interpretation of_zero_hom: zero_hom_0 of_zero_neq_one
  by(unfold_locales) (simp_all)

interpretation of_injective_lim: injective_lim "{0, 1}" of_zero_neq_one
  by (unfold_locales)(simp_all add: of_zero_neq_one_lim_eq)

interpretation of_inj_on_01_hom: inj_on_01_hom of_zero_neq_one
  by (unfold_locales)(simp_all add: of_zero_neq_one_lim_eq)

text \<open>We want the ability to transform any 0-1 vector or matrix to another @{typ "'c :: zero_neq_one"} type \<close>
definition lift_01_vec :: "'b :: {zero_neq_one} vec \<Rightarrow> 'c :: {zero_neq_one} vec" where 
"lift_01_vec v \<equiv> map_vec of_zero_neq_one v"

lemma lift_01_vec_simp[simp]: "dim_vec (lift_01_vec v) = dim_vec v"
"i < dim_vec v \<Longrightarrow> (lift_01_vec v) $ i = of_zero_neq_one (v $ i)"
  by (simp_all add: lift_01_vec_def)

lemma lift_01_vec_count: 
  assumes "set\<^sub>v v \<subseteq> {0, 1}"
  assumes "x \<in> {0, 1}"
  shows "count_vec v x = count_vec (lift_01_vec v) (of_zero_neq_one x)"
  using of_injective_lim.lim_inj_hom_count_vec
  by (metis assms(1) assms(2) lift_01_vec_def)  

definition lift_01_mat :: "'b :: {zero_neq_one} mat \<Rightarrow> 'c :: {zero_neq_one} mat" where 
"lift_01_mat M \<equiv> map_mat of_zero_neq_one M"

lemma lift_01_mat_simp[simp]: "dim_row (lift_01_mat M) = dim_row M"
  "dim_col (lift_01_mat M) = dim_col M"
  "i < dim_row M \<Longrightarrow> j < dim_col M \<Longrightarrow> (lift_01_mat M) $$ (i, j) = of_zero_neq_one (M $$ (i, j))"
  by (simp_all add: lift_01_mat_def)

lemma lift_01_mat_carrier: "lift_01_mat M \<in> carrier_mat (dim_row M) (dim_col M)"
  using lift_01_mat_def by auto

end