section \<open>Farey Sequences and Ford Circles\<close>

theory Farey_Ford
  imports  "HOL-Analysis.Analysis" "HOL-Number_Theory.Totient" "HOL-Library.Sublist"

begin

subsection \<open>Library material\<close>

(*added to distribution 2024-04-11*)
lemma sum_squared_le_sum_of_squares:
  fixes f :: "'a \<Rightarrow> real"
  assumes "finite I"
  shows "(\<Sum>i\<in>I. f i)\<^sup>2 \<le> (\<Sum>y\<in>I. (f y)\<^sup>2) * card I"
proof (cases "finite I \<and> I \<noteq> {}")
  case True
  then have "(\<Sum>i\<in>I. f i / real (card I))\<^sup>2 \<le> (\<Sum>i\<in>I. (f i)\<^sup>2 / real (card I))"
    using assms convex_on_sum [OF _ _ convex_power2, where a = "\<lambda>x. 1 / real(card I)" and S=I]
    by simp
  then show ?thesis
    using assms  
    by (simp add: divide_simps power2_eq_square split: if_split_asm flip: sum_divide_distrib)
qed auto

(*added to distribution 2024-04-11*)
lemma sum_squared_le_sum_of_squares_2:
  "(x+y)/2 \<le> sqrt ((x\<^sup>2 + y\<^sup>2) / 2)"
proof -
  have "(x + y)\<^sup>2 / 2^2 \<le> (x\<^sup>2 + y\<^sup>2) / 2"
    using sum_squared_le_sum_of_squares [of UNIV "\<lambda>b. if b then x else y"]
    by (simp add: UNIV_bool add.commute)
  then show ?thesis
    by (metis power_divide real_le_rsqrt)
qed

(*added to distribution 2024-04-10*)
lemma sphere_scale:
  assumes "a \<noteq> 0"
  shows   "(\<lambda>x. a *\<^sub>R x) ` sphere c r = sphere (a *\<^sub>R c :: 'a :: real_normed_vector) (\<bar>a\<bar> * r)"
proof -
  have *: "(\<lambda>x. a *\<^sub>R x) ` sphere c r \<subseteq> sphere (a *\<^sub>R c) (\<bar>a\<bar> * r)" for a r and c :: 'a
    by (metis (no_types, opaque_lifting) scaleR_right_diff_distrib dist_norm image_subsetI mem_sphere norm_scaleR)
  have "sphere (a *\<^sub>R c) (\<bar>a\<bar> * r) = (\<lambda>x. a *\<^sub>R x) ` (\<lambda>x. inverse a *\<^sub>R x) ` sphere (a *\<^sub>R c) (\<bar>a\<bar> * r)"
    unfolding image_image using assms by simp
  also have "\<dots> \<subseteq> (\<lambda>x. a *\<^sub>R x) ` sphere (inverse a *\<^sub>R (a *\<^sub>R c)) (\<bar>inverse a\<bar> * (\<bar>a\<bar> * r))"
    using "*" by blast
  also have "\<dots> = (\<lambda>x. a *\<^sub>R x) ` sphere c r"
    using assms by (simp add: algebra_simps)
  finally have "sphere (a *\<^sub>R c) (\<bar>a\<bar> * r) \<subseteq> (\<lambda>x. a *\<^sub>R x) ` sphere c r" .
  moreover have "(\<lambda>x. a *\<^sub>R x) ` sphere c r \<subseteq> sphere (a *\<^sub>R c) (\<bar>a\<bar> * r)"
    using "*" by blast
  ultimately show ?thesis by blast
qed

(*added to distribution 2024-04-10*)
lemma sphere_cscale:
  assumes "a \<noteq> 0"
  shows   "(\<lambda>x. a * x) ` sphere c r = sphere (a * c :: complex) (cmod a * r)"
proof -
  have *: "(\<lambda>x. a * x) ` sphere c r \<subseteq> sphere (a * c) (cmod a * r)" for a r c
    by (metis (no_types, lifting) dist_complex_def image_subsetI mem_sphere norm_mult
    right_diff_distrib')
  have "sphere (a * c) (cmod a * r) = (\<lambda>x. a * x) ` (\<lambda>x. inverse a * x) ` sphere (a * c) (cmod a * r)"
    by (simp add: image_image inverse_eq_divide)
  also have "\<dots> \<subseteq> (\<lambda>x. a * x) ` sphere (inverse a * (a * c)) (cmod (inverse a) * (cmod a * r))"
    using "*" by blast
  also have "\<dots> = (\<lambda>x. a * x) ` sphere c r"
    using assms by (simp add: field_simps flip: norm_mult)
  finally have "sphere (a * c) (cmod a * r) \<subseteq> (\<lambda>x. a * x) ` sphere c r" .
  moreover have "(\<lambda>x. a * x) ` sphere c r \<subseteq> sphere (a * c) (cmod a * r)"
    using "*" by blast
  ultimately show ?thesis by blast
qed

(*added to distribution 2024-05-15*)
lemma Complex_divide_complex_of_real: "Complex x y / of_real r = Complex (x/r) (y/r)"
  by (metis complex_of_real_mult_Complex divide_inverse mult.commute of_real_inverse)
lemma cmod_neg_real: "cmod (Complex (-x) y) = cmod (Complex x y)"
  by (metis complex_cnj complex_minus complex_mod_cnj norm_minus_cancel)

subsection \<open>Farey sequences\<close>

lemma sorted_two_sublist:
  fixes x:: "'a::order"
  assumes sorted: "sorted_wrt (<) l"
  shows "sublist [x, y] l \<longleftrightarrow> x < y \<and> x \<in> set l \<and> y \<in> set l \<and> (\<forall>z \<in> set l. z \<le> x \<or> z \<ge> y)"
proof (cases "x < y \<and> x \<in> set l \<and> y \<in> set l")
  case True
  then obtain xs us where us: "l = xs @ [x] @ us"
    by (metis append_Cons append_Nil in_set_conv_decomp_first)
  with True assms have "y \<in> set us"
    by (fastforce simp add: sorted_wrt_append)
  then obtain ys zs where yz: "l = xs @ [x] @ ys @ [y] @ zs"
    by (metis split_list us append_Cons append_Nil)
  have "sublist [x, y] l \<longleftrightarrow> ys = []"
    using sorted yz 
    apply (simp add: sublist_def sorted_wrt_append)
    by (metis (mono_tags, opaque_lifting) append_Cons_eq_iff append_Nil assms sorted_wrt.simps(2)
        sorted_wrt_append less_irrefl)
  also have "\<dots> = (\<forall>z \<in> set l. z \<le> x \<or> z \<ge> y)"
    using sorted yz
    apply (simp add: sublist_def sorted_wrt_append)
    by (metis Un_iff empty_iff less_le_not_le list.exhaust list.set(1) list.set_intros(1))
  finally show ?thesis
    using True by blast 
next
  case False
  then show ?thesis
    by (metis list.set_intros(1) set_subset_Cons sorted_wrt.simps(2) sorted_wrt_append sublist_def
        set_mono_sublist sorted subset_iff)
qed

(* added to distribution 2025-03-20*)
lemma quotient_of_rat_of_int [simp]: "quotient_of (rat_of_int i) = (i, 1)"
  using Rat.of_int_def quotient_of_int by force

(* added to distribution 2025-03-20*)
lemma quotient_of_rat_of_nat [simp]: "quotient_of (rat_of_nat i) = (int i, 1)"
  by (metis of_int_of_nat_eq quotient_of_rat_of_int)

(* added to distribution 2025-03-20*)
lemma int_div_le_self: 
  \<open>x div k \<le> x\<close> if \<open>0 < x\<close>  for x k :: int
  by (metis div_by_1 int_div_less_self less_le_not_le nle_le nonneg1_imp_zdiv_pos_iff order.trans that)

(* not clear to do with these transp lemmas, are they of general use?*)
lemma transp_add1_int:
  assumes "\<And>n::int. R (f n) (f (1 + n))"
    and "n < n'"
    and "transp R"
  shows "R (f n) (f n')"
proof -
  have "R (f n) (f (1 + n + int k))" for k
    by (induction k) (use assms in \<open>auto elim!: transpE\<close>)
  then show ?thesis
    by (metis add.commute assms(2) zle_iff_zadd zless_imp_add1_zle)
qed

lemma refl_transp_add1_int:
  assumes "\<And>n::int. R (f n) (f (1 + n))"
      and "n \<le> n'"
      and "reflp R" "transp R"
    shows "R (f n) (f n')"
  by (metis assms order_le_less reflpE transp_add1_int)

lemma transp_Suc:
  assumes "\<And>n. R (f n) (f (Suc n))"
      and "n < n'"
      and "transp R"
    shows "R (f n) (f n')"
proof -
  have "R (f n) (f (1 + n + k))" for k
  by (induction k) (use assms in \<open>auto elim!: transpE\<close>)
  then show ?thesis
    by (metis add_Suc_right add_Suc_shift assms(2) less_natE plus_1_eq_Suc)
qed

lemma refl_transp_Suc:
  assumes "\<And>n. R (f n) (f (Suc n))"
      and "n \<le> n'"
      and "reflp R" "transp R"
    shows "R (f n) (f n')"
  by (metis assms dual_order.order_iff_strict reflpE transp_Suc)

(* added to distribution 2025-03-20*)
lemma sorted_subset_imp_subseq:
  fixes xs :: "'a::order list"
  assumes "set xs \<subseteq> set ys" "sorted_wrt (<) xs" "sorted_wrt (\<le>) ys"
  shows "subseq xs ys"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case
    by auto
next
  case (Cons x xs)
  then have "x \<in> set ys"
    by auto
  then obtain us vs where \<section>: "ys = us @ [x] @ vs"
    by (metis append.left_neutral append_eq_Cons_conv split_list) 
  moreover 
  have "set xs \<subseteq> set vs"
    using Cons.prems by (fastforce simp: \<section> sorted_wrt_append)
  with Cons have "subseq xs vs"
    by (metis \<section> sorted_wrt.simps(2) sorted_wrt_append)
  ultimately show ?case
    by auto
qed

lemma coprime_unimodular_int:
  fixes a b::int
  assumes "coprime a b" "a>1" "b>1"
  obtains x y where "a*x - b*y = 1" "0 < x" "x < b" "0 < y" "y < a"
proof -
  obtain u v where 1: "a * u + b * v = 1"
    by (metis \<open>coprime a b\<close> cong_iff_lin coprime_iff_invertible_int)
  define k where "k \<equiv> u div b"
  define x where "x \<equiv> u - k*b"
  define y where "y \<equiv> -(v + k*a)"
  show thesis
  proof
    show *: "a * x - b * y = 1" 
      using 1 by (simp add: x_def y_def algebra_simps)
    have "u \<noteq> k*b" "b>0"
      using assms "*"  by (auto simp: k_def x_def y_def zmult_eq_neg1_iff) 
    moreover have "u - k*b \<ge> 0"
      by (simp add: k_def \<open>b>0\<close> minus_div_mult_eq_mod)
    ultimately show "x > 0"
      by (fastforce simp: x_def)
    show "x < b"
      by (simp add: \<open>0 < b\<close> k_def minus_div_mult_eq_mod x_def)
    have "a*x > 1"
      by (metis \<open>0 < x\<close> \<open>a>1\<close> int_one_le_iff_zero_less less_1_mult linorder_not_less
          mult.right_neutral nle_le)
    then have "\<not> b * y \<le> 0"
      using "*" by linarith
    then show "y > 0"
      by (simp add: \<open>0 < b\<close> mult_less_0_iff order_le_less)
    show "y < a"
      using "*" \<open>0 < x\<close> \<open>x < b\<close>
      by (smt (verit, best) \<open>a>1\<close> mult.commute mult_less_le_imp_less)
  qed
qed

subsection \<open>Farey Fractions\<close>

type_synonym farey = rat

definition num_farey :: "farey \<Rightarrow> int" 
  where "num_farey \<equiv> \<lambda>x. fst (quotient_of x)" 

definition denom_farey :: "farey \<Rightarrow> int"
  where "denom_farey \<equiv> \<lambda>x. snd (quotient_of x)" 

definition farey :: "[int,int] \<Rightarrow> farey" 
  where "farey \<equiv> \<lambda>a b. max 0 (min 1 (Fract a b))"

lemma farey01 [simp]: "0 \<le> farey a b" "farey a b \<le> 1"
  by (auto simp: min_def max_def farey_def)

lemma farey_0 [simp]: "farey 0 n = 0"
  by (simp add: farey_def rat_number_collapse)

lemma farey_1 [simp]: "farey 1 1 = 1"
  by (auto simp: farey_def rat_number_expand)

lemma num_farey_nonneg: "x \<in> {0..1} \<Longrightarrow> num_farey x \<ge> 0"
  by (cases x) (simp add: num_farey_def quotient_of_Fract zero_le_Fract_iff)

lemma num_farey_le_denom: "x \<in> {0..1} \<Longrightarrow> num_farey x \<le> denom_farey x"
  by (cases x) (simp add: Fract_le_one_iff denom_farey_def num_farey_def quotient_of_Fract)

lemma denom_farey_pos: "denom_farey x > 0"
  by (simp add: denom_farey_def quotient_of_denom_pos')

lemma coprime_num_denom_farey [intro]: "coprime (num_farey x) (denom_farey x)"
  by (simp add: denom_farey_def num_farey_def quotient_of_coprime)

lemma rat_of_farey_conv_num_denom:
  "x = rat_of_int (num_farey x) / rat_of_int (denom_farey x)"
  by (simp add: denom_farey_def num_farey_def quotient_of_div)

lemma num_denom_farey_eqI:
  assumes "x = of_int a / of_int b" "b > 0" "coprime a b"
  shows   "num_farey x = a" "denom_farey x = b"
  using Fract_of_int_quotient assms quotient_of_Fract
  by (auto simp: num_farey_def denom_farey_def)

lemma farey_cases [cases type, case_names farey]:
  assumes "x \<in> {0..1}"
  obtains a b where "0\<le>a" "a\<le>b" "coprime a b" "x = Fract a b"
  by (metis Fract_of_int_quotient Rat_cases assms num_denom_farey_eqI num_farey_le_denom num_farey_nonneg)

lemma rat_of_farey: "\<lbrakk>x = of_int a / of_int b; x \<in> {0..1}\<rbrakk> \<Longrightarrow> x = farey a b"
  by (simp add: Fract_of_int_quotient farey_def max_def)

lemma farey_num_denom_eq [simp]: "x \<in> {0..1} \<Longrightarrow> farey (num_farey x) (denom_farey x) = x"
  using rat_of_farey rat_of_farey_conv_num_denom by fastforce

lemma farey_eqI:
  assumes "num_farey x = num_farey y" "denom_farey x = denom_farey y"
  shows   "x=y"
  by (metis Rat.of_int_def assms rat_of_farey_conv_num_denom)

lemma
  assumes "coprime a b" "0\<le>a" "a<b"
  shows num_farey_eq [simp]: "num_farey (farey a b) = a"
  and denom_farey_eq [simp]: "denom_farey (farey a b) = b"
  using Fract_less_one_iff quotient_of_Fract zero_le_Fract_iff
  using assms num_denom_farey_eqI rat_of_farey by force+

lemma
  assumes "0 \<le> a" "a \<le> b" "0<b"
  shows num_farey: "num_farey (farey a b) = a div (gcd a b)" 
    and denom_farey: "denom_farey (farey a b) = b div (gcd a b)"
proof -
  have "0 \<le> Fract a b" "Fract a b \<le> 1"
    using assms by (auto simp: Fract_le_one_iff zero_le_Fract_iff)
  with assms show "num_farey (farey a b) = a div (gcd a b)" "denom_farey (farey a b) = b div (gcd a b)"
    by (auto simp: num_farey_def denom_farey_def farey_def quotient_of_Fract Rat.normalize_def Let_def)
qed

lemma
  assumes "coprime a b" "0<b"
  shows num_farey_Fract [simp]: "num_farey (Fract a b) = a"
  and denom_farey_Fract [simp]: "denom_farey (Fract a b) = b"
  using Fract_of_int_quotient assms num_denom_farey_eqI by force+

lemma num_farey_0 [simp]: "num_farey 0 = 0"
  and denom_farey_0 [simp]: "denom_farey 0 = 1"
  and num_farey_1 [simp]: "num_farey 1 = 1"
  and denom_farey_1 [simp]: "denom_farey 1 = 1"
  by (auto simp: num_farey_def denom_farey_def)

lemma num_farey_neq_denom: "denom_farey x \<noteq> 1 \<Longrightarrow> num_farey x \<noteq> denom_farey x"
  by (metis denom_farey_0 div_0 div_self num_farey_1 rat_of_farey_conv_num_denom)

lemma num_farey_0_iff [simp]: "num_farey x = 0 \<longleftrightarrow> x = 0"
  unfolding num_farey_def
  by (metis div_0 eq_fst_iff of_int_0 quotient_of_div rat_zero_code)

lemma denom_farey_le1_cases:
  assumes "denom_farey x \<le> 1" "x \<in> {0..1}"
  shows "x = 0 \<or> x = 1"
proof -
  consider "num_farey x = 0" | "num_farey x = 1" "denom_farey x = 1"
    using assms num_farey_le_denom [of x] num_farey_nonneg [of x] by linarith
  then show ?thesis
    by (metis denom_farey_1 farey_eqI num_farey_0_iff num_farey_1)
qed

definition mediant :: "farey \<Rightarrow> farey \<Rightarrow> farey" where 
  "mediant \<equiv> \<lambda>x y. Fract (fst (quotient_of x) + fst (quotient_of y)) 
                         (snd (quotient_of x) + snd (quotient_of y))"

lemma mediant_eq_Fract:
  "mediant x y = Fract (num_farey x + num_farey y) (denom_farey x + denom_farey y)"
  by (simp add: denom_farey_def num_farey_def mediant_def)

lemma mediant_eq_farey:
  assumes "x \<in> {0..1}" "y \<in> {0..1}"
  shows "mediant x y = farey (num_farey x + num_farey y) (denom_farey x + denom_farey y)"
proof -
  have "0 \<le> num_farey x + num_farey y"
    using assms num_farey_nonneg by auto
  moreover have "num_farey x + num_farey y \<le> denom_farey x + denom_farey y"
    by (meson add_mono assms num_farey_le_denom)
  ultimately show ?thesis
    by (simp add: add_pos_pos denom_farey_pos Fract_of_int_quotient rat_of_farey mediant_eq_Fract)
qed


definition farey_unimodular :: "farey \<Rightarrow> farey \<Rightarrow> bool" where
  "farey_unimodular x y \<longleftrightarrow>
     denom_farey x * num_farey y - num_farey x * denom_farey y = 1"

lemma farey_unimodular_imp_less:
  assumes "farey_unimodular x y"
  shows   "x < y"
  using assms
  by (auto simp: farey_unimodular_def rat_less_code denom_farey_def num_farey_def)

lemma denom_mediant: "denom_farey (mediant x y) \<le> denom_farey x + denom_farey y"
  using quotient_of_denom_pos' [of x] quotient_of_denom_pos' [of y]
  by (simp add: mediant_eq_Fract denom_farey_def num_farey_def quotient_of_Fract normalize_def Let_def int_div_le_self)

lemma unimodular_imp_both_coprime:
  fixes a:: "'a::{algebraic_semidom,comm_ring_1}"
  assumes "b*c - a*d = 1" 
  shows   "coprime a b" "coprime c d"
  using mult.commute by (metis assms coprimeI dvd_diff dvd_mult2)+

lemma unimodular_imp_coprime:
  fixes a:: "'a::{algebraic_semidom,comm_ring_1}"
  assumes "b*c - a*d = 1" 
  shows   "coprime (a+c) (b+d)"
proof (rule coprimeI)
  fix k 
  assume k: "k dvd (a+c)" "k dvd (b+d)"
  moreover have "(b+d)*c = (a+c)*d + 1"
    using assms by (simp add: algebra_simps)
  ultimately show "is_unit k"
    by (metis add_diff_cancel_left' dvd_diff dvd_mult2)
qed

definition fareys :: "int \<Rightarrow> rat list"
  where "fareys n \<equiv> sorted_list_of_set {x \<in> {0..1}. denom_farey x \<le> n}"

lemma strict_sorted_fareys: "sorted_wrt (<) (fareys n)"
  by (simp add: fareys_def)

lemma farey_set_UN_farey: "{x \<in> {0..1}. denom_farey x \<le> n} = (\<Union>b \<in> {1..n}. \<Union>a \<in> {0..b}. {farey a b})"
proof -
  have "\<exists>b \<in> {1..n}. \<exists>a \<in> {0..b}. x = farey a b"
    if "denom_farey x \<le> n" "x \<in> {0..1}" for x :: farey
    unfolding Bex_def
    using that denom_farey_pos int_one_le_iff_zero_less num_farey_le_denom num_farey_nonneg
    by fastforce
  moreover have "\<And>b a::int. 0 \<le> b \<Longrightarrow> b div gcd a b \<le> b"
    by (metis div_0 int_div_le_self nless_le)
  ultimately show ?thesis
    by (auto simp: denom_farey) (meson order_trans)
qed

lemma farey_set_UN_farey': "{x \<in> {0..1}. denom_farey x \<le> n} = (\<Union>b \<in> {1..n}. \<Union>a \<in> {0..b}. if coprime a b then {farey a b} else {})"
proof -
  have "\<exists>aa ba. farey a b = farey aa ba \<and> 0 \<le> aa \<and> aa \<le> ba \<and> 1 \<le> ba \<and> ba \<le> n \<and> coprime aa ba"
    if "1 \<le> b" and "b \<le> n" and "0 \<le> a" and "a \<le> b" for a b
  proof -
    let ?a = "a div gcd a b"
    let ?b = "b div gcd a b"
    have "coprime ?a ?b"
      by (metis div_gcd_coprime not_one_le_zero \<open>b\<ge>1\<close>)
    moreover have "farey a b = farey ?a ?b"
      using Fract_coprime farey_def by presburger
    moreover have "?a \<le> ?b \<and> ?b \<le> n"
      by (smt (verit, best) gcd_pos_int int_div_le_self that zdiv_mono1)
    ultimately show ?thesis
      using that by (metis denom_farey denom_farey_pos div_int_pos_iff gcd_ge_0_int int_one_le_iff_zero_less)
  qed
  then show ?thesis
    unfolding farey_set_UN_farey
    by (fastforce split: if_splits)
qed

lemma farey_set_UN_Fract: "{x \<in> {0..1}. denom_farey x \<le> n} = (\<Union>b \<in> {1..n}. \<Union>a \<in> {0..b}. {Fract a b})"
  unfolding farey_set_UN_farey
  by (simp add: Fract_of_int_quotient farey_def)

lemma farey_set_UN_Fract': "{x \<in> {0..1}. denom_farey x \<le> n} = (\<Union>b \<in> {1..n}. \<Union>a \<in> {0..b}. if coprime a b then {Fract a b} else {})"
  unfolding farey_set_UN_farey'
  by (simp add: Fract_of_int_quotient farey_def)

lemma finite_farey_set: "finite {x \<in> {0..1}. denom_farey x \<le> n}"
  unfolding farey_set_UN_farey by blast

lemma denom_in_fareys_iff: "x \<in> set (fareys n) \<longleftrightarrow> denom_farey x \<le> int n \<and> x \<in> {0..1}"
  using finite_farey_set by (auto simp: fareys_def)

lemma denom_fareys_leI: "x \<in> set (fareys n) \<Longrightarrow> denom_farey x \<le> n"
  using finite_farey_set by (auto simp: fareys_def)

lemma denom_fareys_leD: "\<lbrakk>denom_farey x \<le> int n; x \<in> {0..1}\<rbrakk> \<Longrightarrow> x \<in> set (fareys n)"
  using denom_in_fareys_iff by blast

lemma fareys_increasing_1: "set (fareys n) \<subseteq> set (fareys (1 + n))"
  using farey_set_UN_farey by (force simp: fareys_def)

definition fareys_new :: "int \<Rightarrow> rat set" where
  "fareys_new n \<equiv> {Fract a n| a. coprime a n \<and> a \<in> {0..n}}"

lemma fareys_new_0 [simp]: "fareys_new 0 = {}"
  by (auto simp: fareys_new_def)

lemma fareys_new_1 [simp]: "fareys_new 1 = {0,1}"
proof -
  have "Fract a 1 = 1"
    if a: "Fract a 1 \<noteq> 0" "0 \<le> a" "a \<le> 1" for a
    by (metis One_rat_def int_one_le_iff_zero_less nless_le order_antisym_conv
        rat_number_collapse(1) that) 
  moreover have "\<exists>a. Fract a 1 = 0 \<and> 0 \<le> a \<and> a \<le> 1"
    using rat_number_expand(1) by auto
  moreover have "\<exists>a. Fract a 1 = 1 \<and> 0 \<le> a \<and> a \<le> 1"
    using One_rat_def by fastforce
  ultimately show ?thesis
    by (auto simp: fareys_new_def)
qed

lemma fareys_new_not01:
  assumes "n>1"
  shows "0 \<notin> (fareys_new n)" "1 \<notin> (fareys_new n)"
  using assms by (simp_all add: Fract_of_int_quotient fareys_new_def)

lemma inj_num_farey: "inj_on num_farey (fareys_new n)"
proof (cases "n=1")
  case True
  then show ?thesis
    using fareys_new_1 by auto
next
  case False
  then show ?thesis
  proof -
    have "Fract a n = Fract a' n"
      if "coprime a n" "0 \<le> a" "a \<le> n"
        and "coprime a' n" "0 \<le> a'" "a' \<le> n"
        and "num_farey (Fract a n) = num_farey (Fract a' n)"
      for a a'
    proof -
      from that
      obtain "a < n" "a' < n"
        using False by force+
      with that show ?thesis
        by auto
    qed
    with False show ?thesis
      by (auto simp: inj_on_def fareys_new_def)
  qed
qed
 
lemma finite_fareys_new [simp]: "finite (fareys_new n)"
  by (auto simp: fareys_new_def)

lemma card_fareys_new:
  assumes "n > 1"
  shows "card (fareys_new (int n)) = totient n"
proof -
  have "bij_betw num_farey (fareys_new n) (int ` totatives n)"
  proof -
    have "\<exists>a>0. a \<le> n \<and> coprime a n \<and> num_farey x = int a"
      if x: "x \<in> fareys_new n" for x
    proof -
      obtain a where a: "x = Fract a (int n)" "coprime a (int n)" "0 \<le> a" "a \<le> int n"
        using x by (auto simp: fareys_new_def)
      then have "a > 0"
        using assms less_le_not_le by fastforce
      moreover have "coprime (nat a) n"
        by (metis a(2,3) coprime_int_iff nat_0_le)
      ultimately have "num_farey x = int (nat a)"
        using a num_farey by auto
      then show ?thesis
        using \<open>0 < a\<close> \<open>coprime (nat a) n\<close> a(4) nat_le_iff zero_less_nat_eq by blast
    qed
    moreover have "\<exists>x\<in>fareys_new n. int a = num_farey x"
      if "0 < a" "a \<le> n" "coprime a n" for a 
    proof -
      have \<section>: "coprime (int a) (int n)" "0 \<le> (int a)" "(int a) \<le> int n"
        using that by auto
      then have "Fract (int a) (int n) = Fract (int a) (int n)"
        using Fract_of_int_quotient assms rat_of_farey by auto
      with \<section> have "Fract (int a) (int n) \<in> fareys_new n"
        by (auto simp: fareys_new_def)
      then have "int a = num_farey (Fract (int a) n)"
        using \<open>coprime (int a) (int n)\<close> assms by auto
      then show ?thesis
        using \<open>Fract (int a) (int n) \<in> fareys_new (int n)\<close> by blast
    qed
    ultimately show ?thesis
      by (auto simp add: totatives_def bij_betw_def inj_num_farey comp_inj_on image_iff)
  qed
  then show ?thesis
    unfolding totient_def by (metis bij_betw_same_card bij_betw_of_nat)
qed

lemma disjoint_fareys_plus1: 
  assumes "n > 0"
  shows "disjnt (set (fareys n)) (fareys_new (1 + n))"
proof -
  have False
    if \<section>: "0 \<le> a" "a \<le> 1 + n" "coprime a (1 + n)"
      "1 \<le> d" "d \<le> n" "Fract a (1 + n) = Fract c d" "0 \<le> c" "c \<le> d" "coprime c d"
    for a c d
  proof (cases "c<d")
    case True
    have alen: "a \<le> n"
      using nle_le that by fastforce
    have "d = denom_farey (Fract c d)"
      using that by force
    also have "\<dots> = 1 + n"
      using denom_farey_Fract that by fastforce
    finally show False
      using that(5) by fastforce
  next
    case False
    with \<open>c \<le> d\<close> have "c=d" by auto
    with that have "d=1" by force
    with that have "1 + n = 1"
      by (metis One_rat_def \<open>c = d\<close> assms denom_farey_1 denom_farey_Fract le_imp_0_less
          order_less_le)
    then show ?thesis
      using \<open>c = d\<close> \<section> assms by auto
  qed
  then show ?thesis
  unfolding fareys_def farey_set_UN_Fract' fareys_new_def disjnt_iff
    by auto
qed


lemma set_fareys_plus1: "set (fareys (1 + n)) = set (fareys n) \<union> fareys_new (1 + n)"
proof -
  have "\<exists>b\<ge>1. b \<le> n \<and> (\<exists>a\<ge>0. a \<le> b \<and> coprime a b \<and> Fract c d = Fract a b)"
    if "Fract c d \<notin> fareys_new (1 + n)"
      and "coprime c d" "1 \<le> d" "d \<le> 1 + n" "0 \<le> c" "c \<le> d"
    for c d
  proof (cases "d = 1 + n")
    case True
    with that show ?thesis
      by (auto simp: fareys_new_def)
  qed (use that in auto)
  moreover have "\<exists>d\<ge>1. d \<le> 1 + n \<and> (\<exists>c\<ge>0. c \<le> d \<and> coprime c d \<and> x = Fract c d)"
    if "x \<in> fareys_new (1 + n)" for x
    using that nle_le by (fastforce simp add: fareys_new_def)
  ultimately show ?thesis
    unfolding fareys_def farey_set_UN_Fract' by fastforce
qed

lemma length_fareys_Suc: 
  assumes "n>0"
  shows "length (fareys (1 + int n)) = length (fareys n) + totient (Suc n)"
proof -
  have "length (fareys (1 + int n)) = card (set (fareys (1 + int n)))"
    by (metis fareys_def finite_farey_set sorted_list_of_set.sorted_key_list_of_set_unique)
  also have "\<dots> = card (set (fareys n)) + card (fareys_new(1 + int n))"
    using disjoint_fareys_plus1 assms by (simp add: set_fareys_plus1 card_Un_disjnt)
  also have "\<dots> = card (set (fareys n)) + totient (Suc n)"
    using assms card_fareys_new by force
  also have "\<dots> = length (fareys n) + totient (Suc n)"
    using fareys_def finite_farey_set by auto
  finally show ?thesis .
qed


lemma fareys_0 [simp]: "fareys 0 = []"
  unfolding fareys_def farey_set_UN_farey
  by simp

lemma fareys_1 [simp]: "fareys 1 = [0, 1]"
proof -
  have "{x \<in> {0..1}. denom_farey x \<le> 1} = {0,1}"
    using denom_farey_le1_cases by auto
  then show ?thesis
    by (simp add: fareys_def)
qed

lemma fareys_2 [simp]: "fareys 2 = [0, farey 1 2, 1]"
proof -
  have \<section>: "denom_farey x \<le> 2 \<longleftrightarrow> denom_farey x = 1 \<or> denom_farey x = 2" for x
    using denom_farey_pos [of x] by auto
  have "{x \<in> {0..1}. denom_farey x \<le> 2} = {farey 0 1, farey 1 2, farey 1 1}"
  proof -
    have "x = farey 1 1"
      if "x \<noteq> farey 0 1" "x \<in> {0..1}" "denom_farey x = 1" for x
      using that denom_farey_le1_cases order.eq_iff rat_of_farey by auto
    moreover have False
      if "x \<noteq> farey 0 1" "x \<noteq> farey 1 2" "denom_farey x = 2" "x \<in> {0..1}" for x
      using that num_farey_neq_denom
      by (smt (verit) farey_0 farey_num_denom_eq num_farey_le_denom num_farey_nonneg)
    moreover have "denom_farey (farey 1 1) = 1"
       by (simp add: Fract_of_int_quotient farey_def)
    ultimately show ?thesis
      by (auto simp: farey_set_UN_farey \<section>)
  qed
  also have "\<dots> = {0, 1/2, 1::rat}"
    by (simp add: farey_def Fract_of_int_quotient)
  finally show ?thesis
    by (simp add: fareys_def farey_def Fract_of_int_quotient)
qed

lemma length_fareys_1: 
  shows "length (fareys 1) = 1 + totient 1"
  by simp

lemma length_fareys: "n>0 \<Longrightarrow> length (fareys n) = 1 + (\<Sum>k=1..n. totient k)"
proof (induction n)
  case (Suc n)
  then show ?case
    by (cases "n=0") (auto simp add: length_fareys_Suc)
qed auto

lemma subseq_fareys_1: "subseq (fareys n) (fareys (1 + n))"
  by (metis fareys_increasing_1 strict_sorted_fareys sorted_subset_imp_subseq strict_sorted_imp_sorted)

lemma monotone_fareys: "monotone (\<le>) subseq fareys"
  using refl_transp_add1_int [OF _ _ subseq_order.reflp_on_le subseq_order.transp_on_le]
  by (metis monotoneI subseq_fareys_1)

lemma farey_unimodular_0_1 [simp, intro]: "farey_unimodular 0 1"
  by (auto simp: farey_unimodular_def)

text \<open>Apostol's Theorem 5.2 for integers\<close>
lemma mediant_lies_betw_int:
  fixes a b c d::int
  assumes "rat_of_int a / of_int b < of_int c / of_int d" "b>0" "d>0"
  shows "rat_of_int a / of_int b < (of_int a + of_int c) / (of_int b + of_int d)" 
        "(rat_of_int a + of_int c) / (of_int b + of_int d) < of_int c / of_int d"
    using assms by (simp_all add: field_split_simps)

text \<open>Apostol's Theorem 5.2\<close>
theorem mediant_inbetween:
  fixes x y::farey
  assumes "x < y"
  shows "x < mediant x y" "mediant x y < y"
  using assms mediant_lies_betw_int Fract_of_int_quotient
  by (metis denom_farey_pos mediant_eq_Fract of_int_add rat_of_farey_conv_num_denom)+

lemma sublist_fareysD:
  assumes "sublist [x,y] (fareys n)"
  obtains "x \<in> set (fareys n)" "y \<in> set (fareys n)"
  by (meson assms list.set_intros set_mono_sublist subsetD)

text \<open>Adding the denominators of two consecutive Farey fractions\<close>
lemma sublist_fareys_add_denoms:
  fixes a b c d::int
  defines "x \<equiv> Fract a b"
  defines "y \<equiv> Fract c d"
  assumes sub: "sublist [x,y] (fareys (int n))" and "b>0" "d>0" "coprime a b" "coprime c d"
  shows "b + d > n"
proof (rule ccontr)
  have \<section>: "x < y" "\<forall>z \<in> set (fareys n). z \<le> x \<or> z \<ge> y"
    using sorted_two_sublist strict_sorted_fareys sub by blast+
  assume "\<not> int n < b + d"
  with assms have "denom_farey (mediant x y) \<le> int n"
    by (metis denom_farey_Fract denom_mediant dual_order.trans leI)
  then have "mediant x y \<in> set (fareys n)"
    by (metis sub atLeastAtMost_iff denom_in_fareys_iff farey01 mediant_eq_farey
        sublist_fareysD)
  moreover have "x < mediant x y" "mediant x y < y"
    by (simp_all add: mediant_inbetween \<open>x < y\<close>)
  ultimately show False
    using \<section> x_def y_def by fastforce
qed

subsection \<open>Apostol's Theorems 5.3--5.5\<close>

theorem consec_subset_fareys:
  fixes a b c d::int
  assumes abcd: "0 \<le> Fract a b" "Fract a b < Fract c d" "Fract c d \<le> 1"
    and consec: "b*c - a*d = 1"
    and max: "max b d \<le> n" "n < b+d" 
    and "b>0" 
  shows "sublist [Fract a b, Fract c d] (fareys n)"
proof (rule ccontr)
  assume con: "\<not> ?thesis"
  have "d > 0"
    using max by force
  have "coprime a b" "coprime c d"
    using consec unimodular_imp_both_coprime by blast+
  with \<open>b > 0\<close> \<open>d > 0\<close> have "denom_farey (Fract a b) = b" "denom_farey (Fract c d) = d"
    by auto
  moreover have "b\<le>n" "d\<le>n"
    using max by auto
  ultimately have ab: "Fract a b \<in> set (fareys n)" and cd: "Fract c d \<in> set (fareys n)"
    using abcd finite_farey_set by (auto simp: fareys_def)
  then obtain xs us where us: "fareys n = xs @ [Fract a b] @ us"
    using abcd by (metis append_Cons append_Nil split_list)
  have "Fract c d \<in> set us"
    using abcd cd strict_sorted_fareys [of n]
    by (fastforce simp add: us sorted_wrt_append)
  then obtain ys zs where yz: "fareys n = xs @ [Fract a b] @ ys @ [Fract c d] @ zs"
    by (metis split_list us append_Cons append_Nil)
  with con have "ys \<noteq> []"
    by (metis Cons_eq_append_conv sublist_appendI)
  then obtain h k where hk: "coprime h k" "Fract h k \<in> set ys"  "k>0"
    by (metis Rat_cases list.set_sel(1))
  then have hk_fareys: "Fract h k \<in> set (fareys n)" 
    by (auto simp: yz)
  have less: "Fract a b < Fract h k" "Fract h k < Fract c d" 
    using hk strict_sorted_fareys [of n] by (auto simp add: yz sorted_wrt_append)
  with \<open>b > 0\<close> \<open>d > 0\<close> hk have *: "k*a < h*b" "d*h < c*k"
    by (simp_all add: Fract_of_int_quotient mult.commute divide_simps flip: of_int_mult)
  have "k \<le> n"
    using hk by (metis hk_fareys denom_fareys_leI denom_farey_Fract)
  have "k = (b*c - a*d)*k"
    by (simp add: consec)
  also have "\<dots> = b*(c*k - d*h) + d*(b*h - a*k)"
    by (simp add: algebra_simps)
  finally have k: "k = b * (c * k - d * h) + d * (b * h - a * k)" .  
  moreover have "c*k - d*h \<ge> 1" "b*h - a*k \<ge> 1"
    using \<open>b > 0\<close> \<open>d > 0\<close> * by (auto simp: mult.commute)
  ultimately have "b * (c * k - d * h) + d * (b * h - a * k) \<ge> b+d"
    by (metis \<open>b > 0\<close> \<open>d > 0\<close> add_mono mult.right_neutral mult_left_mono
        order_le_less)
  then show False
    using \<open>k \<le> n\<close> max k by force
qed

lemma farey_unimodular_mediant:
  assumes "farey_unimodular x y"
  shows "farey_unimodular x (mediant x y)" "farey_unimodular (mediant x y) y"
  using assms quotient_of_denom_pos' [of x] quotient_of_denom_pos' [of y]
  unfolding farey_unimodular_def
  by (auto simp: mediant_eq_Fract denom_farey_def num_farey_def quotient_of_Fract unimodular_imp_coprime algebra_simps)

text \<open>Apostol's Theorem 5.4\<close>
theorem mediant_unimodular:
  fixes a b c d::int
  assumes abcd: "0 \<le> Fract a b" "Fract a b < Fract c d" "Fract c d \<le> 1"
    and consec: "b*c - a*d = 1"
    and 0: "b>0" "d>0" 
  defines "h \<equiv> a+c"
  defines "k \<equiv> b+d"
  obtains "Fract a b < Fract h k" "Fract h k < Fract c d" "coprime h k"
          "b*h - a*k = 1"  "c*k - d*h = 1"
proof
  show "Fract a b < Fract h k" "Fract h k < Fract c d"
    using abcd 0
    by (simp_all add: Fract_of_int_quotient h_def k_def distrib_left distrib_right divide_simps)
  show "coprime h k"
    by (simp add: consec unimodular_imp_coprime h_def k_def)
  show "b * h - a * k = 1"
    by (simp add: consec distrib_left h_def k_def)
  show "c * k - d * h = 1"
    by (simp add: consec h_def distrib_left k_def mult.commute)
qed

text \<open>Apostol's Theorem 5.5, first part: "Each fraction in @{term"F(n+1)"} which is not in @{term"F(n)"}
      is the mediant of a pair of consecutive fractions in @{term"F(n)"}\<close>

lemma get_consecutive_parents:
  fixes m n::int
  assumes "coprime m n" "0<m" "m<n"
  obtains a b c d where "m = a+c" "n = b+d" "b*c - a*d = 1" "a\<ge>0" "b>0" "c>0" "d>0" "a<b" "c\<le>d"
proof (cases "m=1")
  case True
  show ?thesis
  proof
    show "m = 0 + 1" "n = 1 + (n-1)"
      by (auto simp: True)
  qed (use True \<open>m<n\<close> in auto)
next
  case False
  then obtain d c where *: "n*c - m*d = 1" "0 < d" "d < n" "0 < c" "c < m"
    using coprime_unimodular_int
 [of n m] coprime_commute assms by (smt (verit) coprime_commute)
  then have **: "n * (c - d) + (n - m) * d = 1"
    by (metis mult_diff_mult)
  show ?thesis
  proof
    show "c\<le>d"
      using * ** \<open>m<n\<close> by (smt (verit) mult_le_0_iff)
    show "(n-d) * c - (m-c) * d = 1"
      using * by (simp add: algebra_simps)
    with * \<open>m<n\<close> show "m-c < n-d"
      by (smt (verit, best) mult_mono)
  qed (use * in auto)
qed

theorem fareys_new_eq_mediant:
  assumes "x \<in> fareys_new n" "n>1"
  obtains a b c d where 
    "sublist [Fract a b, Fract c d] (fareys (n-1))" 
    "x = mediant (Fract a b) (Fract c d)" "coprime a b" "coprime c d" "a\<ge>0" "b>0" "c>0" "d>0" 
proof -
  obtain m where m: "coprime m n" "0 \<le> m" "m \<le> n" "x = Fract m n"
    using assms nless_le zero_less_imp_eq_int by (force simp: fareys_new_def)
  moreover
  have "x \<noteq> 0" "x \<noteq> 1"
    using assms fareys_new_not01 by auto
  with m have "0<m" "m<n"
    using \<open>n>1\<close> of_nat_le_0_iff by fastforce+
  ultimately
  obtain a b c d where 
    abcd: "m = a+c" "n = b+d" "b*c - a*d = 1" "a\<ge>0" "b>0" "c>0" "d>0" "a<b" "c\<le>d"
    by (metis get_consecutive_parents)
  show thesis
  proof
    have "Fract a b < Fract c d"
      using abcd mult.commute[of b c] by force
    with consec_subset_fareys
    show "sublist [Fract a b, Fract c d] (fareys (n-1))"
      using Fract_le_one_iff abcd zero_le_Fract_iff by auto
    show "x = mediant (Fract a b) (Fract c d)"
      using abcd \<open>x = Fract m n\<close> mediant_eq_Fract unimodular_imp_both_coprime by fastforce
    show "coprime a b" "coprime c d"
      using \<open>b * c - a * d = 1\<close> unimodular_imp_both_coprime by blast+
  qed (use abcd in auto)
qed

text \<open>Apostol's Theorem 5.5, second part: "Moreover, if @{term"a/b<c/d"} are consecutive in any @{term"F(n)"},
then they satisfy the unimodular relation @{term"bc - ad = 1"}.\<close>
theorem consec_imp_unimodular:
  assumes "sublist [Fract a b, Fract c d] (fareys (int n))" "b>0" "d>0" "coprime a b" "coprime c d"
  shows  "b*c - a*d = 1"
  using assms 
proof (induction n arbitrary: a b c d)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  show ?case
  proof (cases "n=0")
    case True
    with Suc.prems have "Fract a b = 0" "Fract c d = 1"
      by (auto simp add: sublist_Cons_right)
    with Suc.prems obtain "a=0" "b=1" "c=1" "d=1"
      by (auto simp: Fract_of_int_quotient)
    then show ?thesis
      by auto
  next
    case False
    have "Fract a b < Fract c d" 
      and ab: "Fract a b \<in> set (fareys (1 + int n))" and cd: "Fract c d \<in> set (fareys (1 + int n))"
      using strict_sorted_fareys [of "Suc n"] Suc.prems
      by (auto simp add: sublist_def sorted_wrt_append)
    have con: "z \<le> Fract a b \<or> Fract c d \<le> z" if "z \<in> set (fareys (int n))" for z
    proof -
      have "z \<in> set (fareys (1 + int n))"
        using fareys_increasing_1 that by blast
      with Suc.prems strict_sorted_fareys [of "1 + int n"] show ?thesis
        by (fastforce simp add: sublist_def sorted_wrt_append)
    qed
    show ?thesis
    proof (cases "Fract a b \<in> set (fareys n) \<and> Fract c d \<in> set (fareys n)")
      case True
      then have "sublist [Fract a b, Fract c d] (fareys n)"
        using con \<open>Fract a b < Fract c d\<close> sorted_two_sublist strict_sorted_fareys by blast
      then show ?thesis
        by (simp add: Suc) 
    next
      case False
      have notboth: False if \<section>: "Fract a b \<in> fareys_new (1+n)" "Fract c d \<in> fareys_new (1+n)"
      proof -
        obtain a' b' c' d' where eq':
          "sublist [Fract a' b', Fract c' d'] (fareys n)" "Fract a b = mediant (Fract a' b') (Fract c' d')"
          by (smt (verit) \<open>n\<noteq>0\<close> \<section> fareys_new_eq_mediant of_nat_Suc of_nat_le_0_iff plus_1_eq_Suc)
        then have abcd': "Fract a' b' \<in> set (fareys n)" "Fract c' d' \<in> set (fareys n)"
          by (auto simp: sublist_def)
        have con': "z \<le> Fract a' b' \<or> Fract c' d' \<le> z" if "z \<in> set (fareys n)" for z
          by (metis eq'(1) sorted_two_sublist strict_sorted_fareys that)
        have "Fract a' b' < Fract c' d'"
          using eq'(1) sorted_two_sublist [OF strict_sorted_fareys] by blast         
        then obtain A: "Fract a' b' < Fract a b" "Fract a b < Fract c' d'"
          using eq'(2) mediant_inbetween by presburger
          obtain a'' b'' c'' d'' where eq'':
          "sublist [Fract a'' b'', Fract c'' d''] (fareys n)" "Fract c d = mediant (Fract a'' b'') (Fract c'' d'')"
          by (smt (verit) \<section> \<open>n\<noteq>0\<close> fareys_new_eq_mediant of_nat_Suc of_nat_le_0_iff plus_1_eq_Suc)
        then have abcd'': "Fract a'' b'' \<in> set (fareys n)" "Fract c'' d'' \<in> set (fareys n)"
          by (auto simp: sublist_def)
        then have "Fract c'' d'' \<in> set (fareys (1 + int n))"
          using fareys_increasing_1 by blast
        have con'': "z \<le> Fract a'' b'' \<or> Fract c'' d'' \<le> z" if "z \<in> set (fareys n)" for z
          using sorted_two_sublist [OF strict_sorted_fareys] eq''(1) that by blast
        then obtain "Fract a'' b'' < Fract c'' d''" "Fract a'' b'' < Fract c d" "Fract c d < Fract c'' d''"
          by (metis eq'' sorted_two_sublist [OF strict_sorted_fareys] mediant_inbetween)
        with A show False
          using con' con'' abcd' abcd'' con \<open>Fract a b < Fract c d\<close>
          by (metis eq'(2) eq''(2) dual_order.strict_trans1 not_less_iff_gr_or_eq)
      qed
      consider "Fract a b \<in> fareys_new (1+n)" | "Fract c d \<in> fareys_new (1+n)"
        using False set_fareys_plus1 [of n]
        by (metis (mono_tags, opaque_lifting) Suc.prems(1) Suc_eq_plus1_left UnE list.set_intros(1) of_nat_Suc set_mono_sublist
            set_subset_Cons subset_iff)
      then show ?thesis
      proof cases
        case 1
        then obtain a' b' c' d' where eq:
          "sublist [Fract a' b', Fract c' d'] (fareys n)" 
          "Fract a b = mediant (Fract a' b') (Fract c' d')" "coprime a' b'" "coprime c' d'" "b'>0" "d'>0" 
          by (smt (verit) \<open>n\<noteq>0\<close> fareys_new_eq_mediant of_nat_Suc of_nat_le_0_iff plus_1_eq_Suc)
        then have abcd': "Fract a' b' \<in> set (fareys n)" "Fract c' d' \<in> set (fareys n)"
          by (auto simp: sublist_def)
        have con': "z \<le> Fract a' b' \<or> Fract c' d' \<le> z" if "z \<in> set (fareys n)" for z
          using eq(1) sorted_two_sublist strict_sorted_fareys that by blast
        obtain "Fract a' b' < Fract c' d'" "Fract a b < Fract c' d'"
          using eq by (simp add: mediant_inbetween(2) sorted_two_sublist strict_sorted_fareys)
        then have "Fract c d \<le> Fract c' d'"
          using con abcd' linorder_not_less by blast
        moreover have "Fract c' d' \<le> Fract c d" 
          if "Fract c d \<in> set (fareys n)"
          by (metis con' \<open>Fract a b < Fract c d\<close> \<open>Fract a' b' < Fract c' d'\<close> eq(2) order.trans linorder_not_less mediant_inbetween(1)
              nless_le that)
        ultimately have "Fract c' d' = Fract c d"
          using notboth "1" cd set_fareys_plus1 by auto
        with Suc.prems obtain "c' = c" "d' = d"
          by (metis \<open>0 < d'\<close> \<open>coprime c' d'\<close> denom_farey_Fract num_farey_Fract)
        then have uni: "b'*c - a'*d = 1"
          using Suc eq by blast
        then obtain "a = a' + c" "b = b' + d"
          using eq Suc.prems apply (simp add: mediant_eq_Fract)
          by (metis \<open>c' = c\<close> \<open>d' = d\<close> denom_farey_Fract num_farey_Fract pos_add_strict
              unimodular_imp_coprime)
        with uni show ?thesis
          by (auto simp: algebra_simps)
      next
        case 2
        then obtain a' b' c' d' where eq:
          "sublist [Fract a' b', Fract c' d'] (fareys n)" 
          "Fract c d = mediant (Fract a' b') (Fract c' d')" "coprime a' b'" "coprime c' d'" "b'>0" "d'>0" 
          by (smt (verit) \<open>n\<noteq>0\<close> fareys_new_eq_mediant of_nat_Suc of_nat_le_0_iff plus_1_eq_Suc)
        then have abcd': "Fract a' b' \<in> set (fareys n)" "Fract c' d' \<in> set (fareys n)"
          by (auto simp: sublist_def)
        have con': "z \<le> Fract a' b' \<or> Fract c' d' \<le> z" if "z \<in> set (fareys n)" for z
          using eq(1) sorted_two_sublist strict_sorted_fareys that by blast
        obtain "Fract a' b' < Fract c' d'" "Fract a' b' < Fract c d"
          using eq mediant_inbetween
          by (metis sorted_two_sublist strict_sorted_fareys)
        then have "Fract a' b' \<le> Fract a b"
          using con abcd' linorder_not_less by blast
        moreover have "Fract a b \<le> Fract a' b'" 
          if "Fract a b \<in> set (fareys n)"
          by (metis \<open>Fract a b < Fract c d\<close> \<open>Fract a' b' < Fract c' d'\<close> con' order.strict_trans2 eq(2) mediant_inbetween(2)
              not_less_iff_gr_or_eq that)
        ultimately have "Fract a' b' = Fract a b"
          using notboth 2 ab set_fareys_plus1 by auto
        with Suc.prems obtain "a' = a" "b' = b"
          by (metis \<open>0 < b'\<close> \<open>coprime a' b'\<close> denom_farey_Fract num_farey_Fract)
        then have uni: "b*c' - a*d' = 1"
          using Suc.IH Suc.prems eq by blast
        then obtain "c = a + c'" "d = b + d'"
          using eq Suc.prems apply (simp add: mediant_eq_Fract)
          by (metis \<open>a' = a\<close> \<open>b' = b\<close> denom_farey_Fract num_farey_Fract pos_add_strict
              unimodular_imp_coprime)
        with uni show ?thesis
          by (auto simp: algebra_simps)
      qed
    qed
  qed
qed

subsection \<open>Ford circles\<close>

definition Ford_center :: "rat \<Rightarrow> complex" where
  "Ford_center r \<equiv> (\<lambda>(h,k). Complex (h/k) (1/(2 * k^2))) (quotient_of r)"

definition Ford_radius :: "rat \<Rightarrow> real" where
  "Ford_radius r \<equiv> (\<lambda>(h,k). 1/(2 * k^2)) (quotient_of r)"

definition Ford_tan :: "[rat,rat] \<Rightarrow> bool" where
  "Ford_tan r s \<equiv> dist (Ford_center r) (Ford_center s) = Ford_radius r + Ford_radius s"

definition Ford_circle :: "rat \<Rightarrow> complex set" where
  "Ford_circle r \<equiv> sphere (Ford_center r) (Ford_radius r)"

lemma Im_Ford_center [simp]: "Im (Ford_center r) = Ford_radius r"
  by (auto simp: Ford_center_def Ford_radius_def split: prod.splits)

lemma Ford_radius_nonneg: "Ford_radius r \<ge> 0"
  by (simp add: Ford_radius_def split: prod.splits)

lemma two_Ford_tangent:
  assumes r: "(a,b) = quotient_of r" and s: "(c,d) = quotient_of s"
  shows "(dist (Ford_center r) (Ford_center s))^2 - (Ford_radius r + Ford_radius s)^2 
       = ((a*d - b*c)^2 - 1) / (b*d)^2"
proof -
  obtain 0: "b > 0" "d > 0"
    by (metis assms quotient_of_denom_pos)
  have 1: "dist (Ford_center r) (Ford_center s) ^ 2 = (a/b - c/d)^2 + (1/(2*b^2) - 1/(2*d^2)) ^ 2"
    using assms by (force simp: Ford_center_def dist_norm complex_norm complex_diff split: prod.splits)
  have 2: "(Ford_radius r + Ford_radius s) ^ 2 = (1/(2*b^2) + 1/(2*d^2)) ^ 2"
    using assms by (force simp: Ford_radius_def split: prod.splits)
  show ?thesis
    using 0 unfolding 1 2 by (simp add: field_simps eval_nat_numeral)
qed

text \<open>Apostol's Theorem 5.6\<close>
lemma two_Ford_tangent_iff:
  assumes r: "(a,b) = quotient_of r" and s: "(c,d) = quotient_of s"
  shows "Ford_tan r s \<longleftrightarrow> \<bar>b * c - a * d\<bar> = 1"
proof -
  obtain 0: "b > 0" "d > 0"
    by (metis assms quotient_of_denom_pos)
  have "Ford_tan r s \<longleftrightarrow> dist (Ford_center r) (Ford_center s) ^ 2 = (Ford_radius r + Ford_radius s) ^ 2"
    using Ford_radius_nonneg by (simp add: Ford_tan_def)
  also have "\<dots> \<longleftrightarrow> ((a*d - b*c)^2 - 1) / (b*d)^2 = 0"
    using two_Ford_tangent [OF assms] by (simp add: diff_eq_eq)
  also have "\<dots> \<longleftrightarrow> \<bar>b * c - a * d\<bar> = 1"
    using 0 by (simp add: abs_square_eq_1 abs_minus_commute flip: of_int_mult of_int_diff)
  finally show ?thesis .
qed

text \<open>Also Apostol's Theorem 5.6: Distinct Ford circles do not overlap\<close>
lemma Ford_no_overlap:
  assumes "r \<noteq> s"
  shows "dist (Ford_center r) (Ford_center s) \<ge> Ford_radius r + Ford_radius s"
proof -
  obtain a b c d where r: "(a,b) = quotient_of r" and s: "(c,d) = quotient_of s"
                 and "b>0" "d>0"
    by (metis quotient_of_denom_pos surj_pair)
  moreover have "a \<noteq> c \<or> b \<noteq> d"
    using assms r s quotient_of_inject by force
  ultimately have "a * d \<noteq> c * b"
    by (metis Fract_of_int_quotient assms eq_rat(1) less_irrefl quotient_of_div)
  then have "(a*d - b*c)^2 \<ge> (1::int)"
    by (simp add: mult.commute int_one_le_iff_zero_less)
  then have "((a*d - b*c)^2 - 1) / (b*d)^2 \<ge> (0::real)"
    by (simp add: divide_simps mult_less_0_iff flip: of_int_mult of_int_power)
  then show ?thesis
    using two_Ford_tangent [OF r s]
    by (metis (no_types, lifting) ge_iff_diff_ge_0 of_int_1 of_int_diff of_int_mult 
              of_int_power power2_le_imp_le zero_le_dist)
qed

lemma Ford_aux1:
  assumes "a\<noteq>0"
  shows "cmod (Complex (b / (a * (a\<^sup>2 + b\<^sup>2))) (1 / (2 * a\<^sup>2) - inverse (a\<^sup>2 + b\<^sup>2))) = 1 / (2 * a\<^sup>2)"
       (is "cmod ?z = ?r")
proof -
  have "(2 * a\<^sup>2) * cmod ?z = cmod ((2 * a\<^sup>2) * ?z)"
    by (simp add: norm_mult power2_eq_square)
  also have "\<dots> = cmod (Complex (2*a*b / (a\<^sup>2 + b\<^sup>2)) (1 - (2 * a\<^sup>2) / (a\<^sup>2 + b\<^sup>2)))"
    unfolding complex_of_real_mult_Complex inverse_eq_divide
    using \<open>a\<noteq>0\<close> by (simp add: power2_eq_square mult.assoc right_diff_distrib)
  also have "\<dots> = cmod (Complex (2*a*b) ((a\<^sup>2 + b\<^sup>2) - (2 * a\<^sup>2)) / (a\<^sup>2 + b\<^sup>2))"
    unfolding Complex_divide_complex_of_real diff_divide_distrib
    using assms by force
  also have "\<dots> = cmod (Complex (2*a*b) ((a\<^sup>2 + b\<^sup>2) - (2 * a\<^sup>2))) / (a\<^sup>2 + b\<^sup>2)"
    by (smt (verit) norm_divide norm_of_real not_sum_power2_lt_zero)
  also have "\<dots> = sqrt ((a\<^sup>2 + b\<^sup>2)^2) / (a\<^sup>2 + b\<^sup>2)"
    unfolding power2_eq_square complex_norm
    by (simp add: algebra_simps)
  also have "\<dots> = 1"
    using assms by auto
  finally show ?thesis
    by (metis inverse_eq_divide inverse_unique)
qed

lemma Ford_aux2:
  assumes "a\<noteq>0"
  shows "cmod (Complex (a / (b * (b\<^sup>2 + a\<^sup>2)) - 1 / (a * b)) (1 / (2 * a\<^sup>2) - inverse (b\<^sup>2 + a\<^sup>2))) = 1 / (2 * a\<^sup>2)"
       (is "cmod ?z = ?r")
proof -
  have "a / (b * (b\<^sup>2 + a\<^sup>2)) - 1 / (a * b) = -b / (a * (b\<^sup>2 + a\<^sup>2))"
    by (simp add: divide_simps power2_eq_square)
  then have "cmod ?z = cmod (Complex (b / (a * (a\<^sup>2 + b\<^sup>2))) (1 / (2 * a\<^sup>2) - inverse (a\<^sup>2 + b\<^sup>2)))"
    by (simp add: cmod_neg_real add.commute)
  also have "\<dots> = 1 / (2 * a\<^sup>2)"
    using Ford_aux1 assms by simp
  finally show ?thesis .
qed

definition Radem_trans :: "rat \<Rightarrow> complex \<Rightarrow> complex" where
  "Radem_trans \<equiv> \<lambda>r \<tau>. let (h,k) = quotient_of r in - \<i> * of_int k ^ 2 * (\<tau> - of_rat r)"

text \<open>Theorem 5.8 first part\<close>
lemma Radem_trans_image: "Radem_trans r ` Ford_circle r = sphere (of_rat (1/2)) (1/2)"
proof -
  obtain h k where r: "quotient_of r = (h,k)" and "k>0" and req: "r = of_int h / of_int k"
    using quotient_of_denom_pos quotient_of_div by fastforce
  have "Radem_trans r ` Ford_circle r = ((*) (-\<i> * of_int k ^ 2)) ` (\<lambda>\<tau>. \<tau> - of_rat r) ` Ford_circle r"
    by (simp add: Radem_trans_def r image_comp)
  also have "\<dots> = ((*) (-\<i> * of_int k ^ 2)) ` sphere (Ford_center r - of_rat r) (Ford_radius r)"
    by (simp add: Ford_circle_def flip: sphere_translation_subtract)
  also have "\<dots> = sphere (- \<i> * (of_int k)\<^sup>2 * (Ford_center r - r))
                          (cmod (- \<i> * (of_int k)\<^sup>2) * Ford_radius r)"
    using \<open>k>0\<close> by (intro sphere_cscale) auto
  also have "\<dots> = sphere (of_rat (1/2)) (1/2)"
  proof -
    have "(- \<i> * (of_int k)\<^sup>2 * (Ford_center r - r)) = 1/2"
      using \<open>k>0\<close>
      apply (simp add: Ford_center_def r algebra_simps Complex_eq)
      by (simp add: of_rat_divide req)
    moreover 
    have "(cmod (- \<i> * (of_int k)\<^sup>2) * Ford_radius r) = 1/2"
      using \<open>k>0\<close>
      by (simp add: norm_mult norm_power Ford_radius_def r)
    ultimately show ?thesis
      by (metis of_rat_1 of_rat_divide of_rat_numeral_eq)
  qed
  finally show ?thesis .
qed

locale three_Ford =
  fixes N::nat
  fixes h1 k1 h k h2 k2::int
  assumes sub1: "sublist [Fract h1 k1, Fract h k] (fareys (int N))"
  assumes sub2: "sublist [Fract h k, Fract h2 k2] (fareys (int N))"
  assumes coprime: "coprime h1 k1" "coprime h k" "coprime h2 k2"
  assumes k_pos: "k1 > 0" "k > 0" "k2 > 0"

begin

definition "r1 \<equiv> Fract h1 k1"
definition "r \<equiv> Fract h k"
definition "r2 \<equiv> Fract h2 k2"

lemma N_pos: "N>0"
  using sub1 gr0I by force

lemma r_eq_quotient:
  "(h1,k1) = quotient_of r1" "(h,k) = quotient_of r" "(h2,k2) = quotient_of r2"
  by (simp_all add: coprime k_pos quotient_of_Fract r1_def r_def r2_def)

lemma r_eq_divide:
  "r1 = of_int h1 / of_int k1" "r = of_int h / of_int k" "r2 = of_int h2/ of_int k2"
  by (simp_all add: Fract_of_int_quotient of_rat_divide r1_def r2_def r_def)

lemma collapse_r:
  "real_of_int h1 / of_int k1 = of_rat r1" 
  "real_of_int h / of_int k = of_rat r" "real_of_int h2/ of_int k2 = of_rat r2"
  by (simp_all add: of_rat_divide r_eq_divide)

lemma unimod1: "k1*h - h1*k = 1"
  and unimod2: "k*h2 - h*k2 = 1"
  using consec_imp_unimodular coprime k_pos sub1 sub2 by blast+

lemma r_less: "r1 < r" "r < r2"
  using r1_def r_def r2_def sub1 sub2 sorted_two_sublist [OF strict_sorted_fareys] by auto

lemma r01:
  obtains "r1 \<in> {0..1}" "r \<in> {0..1}" "r2 \<in> {0..1}"
  by (metis denom_in_fareys_iff r1_def r2_def r_def sub1 sub2 sublist_fareysD)

lemma atMost_N:
  obtains "k1 \<le> N" "k \<le> N" "k2 \<le> N"
  by (metis denom_farey_def denom_in_fareys_iff prod.sel(2) r1_def r2_def r_def r_eq_quotient sub1 sub2
      sublist_fareysD)

lemma greaterN1: "k1 + k > N"
  using sublist_fareys_add_denoms coprime k_pos sub1 by blast

lemma greaterN2: "k + k2 > N"
  using sublist_fareys_add_denoms coprime k_pos sub2 by blast

definition "alpha1 \<equiv> Complex (h/k - k1 / of_int(k * (k\<^sup>2 + k1\<^sup>2))) (inverse (of_int (k\<^sup>2 + k1\<^sup>2)))"
definition "alpha2 \<equiv> Complex (h/k + k2 / of_int(k * (k\<^sup>2 + k2\<^sup>2))) (inverse (of_int (k\<^sup>2 + k2\<^sup>2)))"

definition "zed1 \<equiv> Complex (k\<^sup>2) (k*k1) / ((k\<^sup>2 + k1\<^sup>2))"
definition "zed2 \<equiv> Complex (k\<^sup>2) (- k*k2) / ((k\<^sup>2 + k2\<^sup>2))"

text \<open>Apostol's Theorem 5.7\<close>
lemma three_Ford_tangent:
  obtains "alpha1 \<in> Ford_circle r" "alpha1 \<in> Ford_circle r1"
          "alpha2 \<in> Ford_circle r" "alpha2 \<in> Ford_circle r2"
proof
  show "alpha1 \<in> Ford_circle r"
    using k_pos Ford_aux1 r_eq_quotient
    by (force simp: alpha1_def Ford_circle_def Ford_center_def dist_norm complex_diff 
        Ford_radius_def split: prod.splits)
  have 1: "real_of_int h1 / real_of_int k1 = real_of_int h / real_of_int k - 1 / (k1*k)"
    using unimod1 k_pos
    by (simp add: divide_simps) (simp add: algebra_simps flip: of_int_mult of_int_diff)
  show "alpha1 \<in> Ford_circle r1"
    using k_pos Ford_aux2 r_eq_quotient
    by (force simp: alpha1_def Ford_circle_def Ford_center_def dist_norm complex_diff 1 Ford_radius_def split: prod.splits)
  show "alpha2 \<in> Ford_circle r"
    using k_pos Ford_aux1 [of k k2] cmod_neg_real r_eq_quotient
    by (force simp add: alpha2_def Ford_circle_def Ford_center_def dist_norm complex_diff Ford_radius_def split: prod.splits)
  have 2: "real_of_int h / real_of_int k = real_of_int h2 / real_of_int k2 - 1 / (k*k2)"
    using unimod2 k_pos
    by (simp add: divide_simps) (simp add: algebra_simps flip: of_int_mult of_int_diff)
  show "alpha2 \<in> Ford_circle r2"
    using k_pos Ford_aux2 [of k2 k] cmod_neg_real r_eq_quotient
    apply (simp add: alpha2_def Ford_circle_def Ford_center_def dist_norm complex_diff 2 Ford_radius_def split: prod.splits)
    by (smt (verit) mult.commute prod.sel)
qed

text \<open>Theorem 5.8 second part, for alpha1\<close>
lemma Radem_trans_alpha1: "Radem_trans r alpha1 = zed1"
proof -
  have "Radem_trans r alpha1 = ((*) (-\<i> * of_int k ^ 2)) ((\<lambda>\<tau>. \<tau> - of_rat r) alpha1)"
    by (metis Radem_trans_def prod.simps(2) r_eq_quotient(2))
  also have "\<dots> = ((*) (-\<i> * of_int k ^ 2)) (Complex (- k1 / of_int(k * (k\<^sup>2 + k1\<^sup>2))) (inverse (of_int (k\<^sup>2 + k1\<^sup>2))))"
    using k_pos by (simp add: alpha1_def r_def of_rat_rat Complex_eq)
  also have "\<dots> = zed1"
    unfolding complex_eq_iff by (simp add: zed1_def inverse_eq_divide power2_eq_square)
  finally show ?thesis .
qed

text \<open>Theorem 5.8 second part, for alpha2\<close>
lemma Radem_trans_alpha2: "Radem_trans r alpha2 = zed2"
proof -
  have "Radem_trans r alpha2 = ((*) (-\<i> * of_int k ^ 2)) ((\<lambda>\<tau>. \<tau> - of_rat r) alpha2)"
    by (metis Radem_trans_def prod.simps(2) r_eq_quotient(2))
  also have "\<dots> = ((*) (-\<i> * of_int k ^ 2)) (Complex (k2 / of_int(k * (k\<^sup>2 + k2\<^sup>2))) (inverse (of_int (k\<^sup>2 + k2\<^sup>2))))"
    using k_pos by (simp add: alpha2_def r_def of_rat_rat Complex_eq)
  also have "\<dots> = zed2"
    unfolding complex_eq_iff by (simp add: zed2_def inverse_eq_divide power2_eq_square)
  finally show ?thesis .
qed

text \<open>Theorem 5.9, for zed1\<close>
lemma cmod_zed1: "cmod zed1 = k / sqrt (k\<^sup>2 + k1\<^sup>2)"
proof -
  have "cmod zed1 ^ 2 = (k^4 + k\<^sup>2 * k1\<^sup>2) / (k\<^sup>2 + k1\<^sup>2)^2"
    by (simp add: zed1_def cmod_def divide_simps)
  also have "\<dots> = (of_int k) ^ 2 / (k\<^sup>2 + k1\<^sup>2)"
    by (simp add: eval_nat_numeral divide_simps) argo
  finally have "cmod zed1 ^ 2 = (of_int k) ^ 2 / (k\<^sup>2 + k1\<^sup>2)" .
  with k_pos real_sqrt_divide show ?thesis
    unfolding cmod_def by force
qed

text \<open>Theorem 5.9, for zed2\<close>
lemma cmod_zed2: "cmod zed2 = k / sqrt (k\<^sup>2 + k2\<^sup>2)"
proof -
  have "cmod zed2 ^ 2 = (k^4 + k\<^sup>2 * k2\<^sup>2) / (k\<^sup>2 + k2\<^sup>2)^2"
    by (simp add: zed2_def cmod_def divide_simps)
  also have "\<dots> = (of_int k) ^ 2 / (k\<^sup>2 + k2\<^sup>2)"
    by (simp add: eval_nat_numeral divide_simps) argo
  finally have "cmod zed2 ^ 2 = (of_int k) ^ 2 / (k\<^sup>2 + k2\<^sup>2)" .
  with k_pos real_sqrt_divide show ?thesis
    unfolding cmod_def by force
qed


text \<open>The last part of theorem 5.9\<close>

lemma RMS_calc:
  assumes "k' > 0" "k' + k > int N"
  shows "k / sqrt (k\<^sup>2 + k'\<^sup>2) < sqrt 2 * k/N"
proof -
  have \<section>: "(k + k')/2 \<le> sqrt ((k\<^sup>2 + k'\<^sup>2) / 2)"
    using sum_squared_le_sum_of_squares_2 by simp
  have "N / sqrt 2 < (N+1) / sqrt 2"
    by (simp add: divide_strict_right_mono)
  also have "\<dots> \<le> (k + k') / sqrt 2"
    using assms by (simp add: divide_simps)
  also have "\<dots> = (k + k')/2 * sqrt 2"
    by (metis nonzero_divide_eq_eq real_div_sqrt times_divide_eq_right zero_le_numeral
        zero_neq_numeral)
  also have "\<dots> \<le> sqrt (k\<^sup>2 + k'\<^sup>2)"
    using \<section> by (simp add: le_divide_eq real_sqrt_divide)
  finally have 1: "real N / sqrt 2 < sqrt (real_of_int (k\<^sup>2 + k'\<^sup>2))" .
  with N_pos k_pos not_sum_power2_lt_zero show ?thesis
    by (force simp add: cmod_zed1 mult.commute divide_simps)
qed

lemma on_chord_bounded_cmod:
  assumes "z \<in> closed_segment zed1 zed2"
  shows "cmod z < sqrt 2 * k/N"
proof -
  have "cmod z \<le> max (cmod zed1) (cmod zed2)"
    using segment_furthest_le [OF assms, of 0] by auto
  moreover
  obtain "cmod zed1 < sqrt 2 * k/N" "cmod zed2 < sqrt 2 * k/N"
    using RMS_calc cmod_zed1 cmod_zed2 greaterN1 greaterN2 k_pos by force
  ultimately show ?thesis
    using assms cmod_zed1 cmod_zed2 by linarith
qed

end

end
