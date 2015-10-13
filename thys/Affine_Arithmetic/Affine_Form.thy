section {* Affine Form *}
theory Affine_Form
imports
  "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
  "~~/src/HOL/Library/Permutation"
begin
text {* \label{sec:aforms} *}

subsection {* Auxiliary developments *}

lemma listsum_mono:
  fixes xs ys::"'a::ordered_ab_group_add list"
  shows
    "length xs = length ys \<Longrightarrow> (\<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> x \<le> y) \<Longrightarrow>
      listsum xs \<le> listsum ys"
  by (induct xs ys rule: list_induct2) (auto simp: algebra_simps intro: add_mono)

lemma listsum_nth_eqI:
  fixes xs ys::"'a::monoid_add list"
  shows
    "length xs = length ys \<Longrightarrow> (\<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> x = y) \<Longrightarrow>
      listsum xs = listsum ys"
  by (induct xs ys rule: list_induct2) auto

lemma
  fixes xs::"'a::ordered_comm_monoid_add list"
  shows listsum_nonneg: "(\<And>x. x \<in> set xs \<Longrightarrow> x \<ge> 0) \<Longrightarrow> listsum xs \<ge> 0"
  by (induct xs) (auto intro!: add_nonneg_nonneg)

lemma list_allI: "(\<And>x. x \<in> set xs \<Longrightarrow> P x) \<Longrightarrow> list_all P xs"
  by (auto simp: list_all_iff)

lemma map_filter:
  "map f (filter (\<lambda>x. P (f x)) xs) = filter P (map f xs)"
  by (induct xs) simp_all

lemma
  map_of_zip_upto2_length_eq_nth:
  assumes "distinct B"
  assumes "i < length B"
  shows "(map_of (zip B [0..<length B]) (B ! i)) = Some i"
proof -
  have "length [0..<length B] = length B"
    by simp
  from map_of_zip_is_Some[OF this, of i] assms
  have "map_of (zip B [0..<length B]) (B ! i) = Some i"
    using assms by (auto simp: in_set_zip)
  thus ?thesis by simp
qed

lemma distinct_map_fst_snd_eqD:
  "distinct (map fst xs) \<Longrightarrow> (i, a) \<in> set xs \<Longrightarrow> (i, b) \<in> set xs \<Longrightarrow> a = b"
  by (metis (lifting) map_of_is_SomeI option.inject)

lemma length_filter_snd_zip:
  "length ys = length xs \<Longrightarrow> length (filter (p \<circ> snd) (zip ys xs)) = length (filter p xs)"
  by (induct ys xs rule: list_induct2) (auto )

lemma filter_snd_nth:
  "length ys = length xs \<Longrightarrow> n < length (filter p xs) \<Longrightarrow>
    snd (filter (p \<circ> snd) (zip ys xs) ! n) = filter p xs ! n"
  by (induct ys xs arbitrary: n rule: list_induct2) (auto simp: o_def nth_Cons split: nat.split)

lemma distinct_map_snd_fst_eqD:
  "distinct (map snd xs) \<Longrightarrow> (i, a) \<in> set xs \<Longrightarrow> (j, a) \<in> set xs \<Longrightarrow> i = j"
  by (metis Pair_inject inj_on_contraD snd_conv distinct_map)

lemma map_of_mapk_inj_on_SomeI:
  "inj_on f (fst ` (set t)) \<Longrightarrow> map_of t k = Some x \<Longrightarrow>
    map_of (map (case_prod (\<lambda>k. Pair (f k))) t) (f k) = Some x"
  by (induct t) (auto simp add: inj_on_def dest!: map_of_SomeD split: split_if_asm)

lemma map_abs_nonneg[simp]:
  fixes xs::"'a::ordered_ab_group_add_abs list"
  shows "list_all (\<lambda>x. x \<ge> 0) xs \<Longrightarrow> map abs xs = xs"
  by (induct xs) auto

lemma the_inv_into_image_eq: "inj_on f A \<Longrightarrow> Y \<subseteq> f ` A \<Longrightarrow> the_inv_into A f ` Y = f -` Y \<inter> A"
  using f_the_inv_into_f the_inv_into_f_f[where f = f and A = A]
  by force

lemma image_fst_zip: "length ys = length xs \<Longrightarrow> fst ` set (zip ys xs) = set ys"
  by (metis dom_map_of_conv_image_fst dom_map_of_zip)

lemma inj_on_fst_set_zip_distinct[simp]:
  "distinct xs \<Longrightarrow> length xs = length ys \<Longrightarrow> inj_on fst (set (zip xs ys))"
  by (force simp add: in_set_zip distinct_conv_nth intro!: inj_onI)

lemma mem_greaterThanLessThan_absI:
  fixes x::real
  assumes "abs x < 1"
  shows "x \<in> {-1 <..< 1}"
  using assms by (auto simp: abs_real_def split: split_if_asm)

lemma minus_one_less_divideI: "b > 0 \<Longrightarrow> -b < a \<Longrightarrow> -1 < a / (b::real)"
  by (auto simp: field_simps)

lemma divide_less_oneI: "b > 0 \<Longrightarrow> b > a \<Longrightarrow> a / (b::real) < 1"
  by (auto simp: field_simps)

lemma closed_segment_real:
  fixes a b::real
  shows "closed_segment a b = (if a \<le> b then {a .. b} else {b .. a})" (is "_ = ?if")
proof safe
  fix x assume "x \<in> closed_segment a b"
  from segment_bound[OF this]
  show "x \<in> ?if" by (auto simp: abs_real_def split: split_if_asm)
next
  fix x
  assume "x \<in> ?if"
  thus "x \<in> closed_segment a b"
    by (auto simp: closed_segment_def intro!: exI[where x="(x - a)/(b - a)"]
      simp: divide_simps algebra_simps)
qed


subsection {* Partial Deviations *}

typedef (overloaded) 'a pdevs = "{x::nat \<Rightarrow> 'a::zero. finite {i. x i \<noteq> 0}}"
  morphisms pdevs_apply Abs_pdev
  by (auto intro!: exI[where x="\<lambda>x. 0"])

setup_lifting type_definition_pdevs

lemma pdevs_eqI: "(\<And>i. pdevs_apply x i = pdevs_apply y i) \<Longrightarrow> x = y"
  by transfer auto

definition pdevs_val :: "(nat \<Rightarrow> real) \<Rightarrow> 'a::real_normed_vector pdevs \<Rightarrow> 'a"
  where "pdevs_val e x = (\<Sum>i. e i *\<^sub>R pdevs_apply x i)"

definition valuate:: "((nat \<Rightarrow> real) \<Rightarrow> 'a) \<Rightarrow> 'a set"
  where "valuate x = x ` (UNIV \<rightarrow> {-1 .. 1})"

lemma valuate_ex: "x \<in> valuate f \<longleftrightarrow> (\<exists>e. (\<forall>i. e i \<in> {-1 .. 1}) \<and> x = f e)"
  unfolding valuate_def
  by (auto simp add: valuate_def Pi_iff) blast

instantiation pdevs :: (equal) equal
begin

definition equal_pdevs::"'a pdevs \<Rightarrow> 'a pdevs \<Rightarrow> bool"
  where "equal_pdevs a b \<longleftrightarrow> a = b"

instance proof qed (simp add: equal_pdevs_def)
end


subsection {* Affine Forms *}

text {* The data structure of affine forms represents particular sets, zonotopes *}

type_synonym 'a aform = "'a \<times> 'a pdevs"


subsection {* Evaluation, Range, Joint Range *}

definition aform_val :: "(nat \<Rightarrow> real) \<Rightarrow> 'a::real_normed_vector aform \<Rightarrow> 'a"
  where "aform_val e X = fst X + pdevs_val e (snd X)"

definition Affine ::
    "'a::real_normed_vector aform \<Rightarrow> 'a set"
  where "Affine X = valuate (\<lambda>e. aform_val e X)"

definition Joints ::
    "'a::real_normed_vector aform list \<Rightarrow> 'a list set"
  where "Joints XS = valuate (\<lambda>e. map (aform_val e) XS)"

lemma Joints_nthE:
  assumes "zs \<in> Joints ZS"
  obtains e where
    "\<And>i. i < length zs \<Longrightarrow> zs ! i = aform_val e (ZS ! i)"
    "\<And>i. e i \<in> {-1..1}"
  using assms
  by atomize_elim (auto simp: Joints_def Pi_iff valuate_ex)

lemma Joints_mapE:
  assumes "ys \<in> Joints YS"
  obtains e where
    "ys = map (\<lambda>x. aform_val e x) YS"
    "\<And>i. e i \<in> {-1 .. 1}"
  using assms
  by (force simp: Joints_def valuate_def)

lemma
  zipped_subset_mapped_Elem:
  assumes "xs = map (aform_val e) XS"
  assumes e: "\<And>i. e i \<in> {-1 .. 1}"
  assumes [simp]: "length xs = length XS"
  assumes [simp]: "length ys = length YS"
  assumes "set (zip ys YS) \<subseteq> set (zip xs XS)"
  shows "ys = map (aform_val e) YS"
proof -
  from assms have ys: "\<And>i. i < length xs \<Longrightarrow> xs ! i = aform_val e (XS ! i)"
    by auto
  from assms have set_eq: "{(ys ! i, YS ! i) |i. i < length ys \<and> i < length YS} \<subseteq>
    {(xs ! i, XS ! i) |i. i < length xs \<and> i < length XS}"
    using assms(2)
    by (auto simp: set_zip)
  hence "\<forall>i<length YS. \<exists>j<length XS. ys ! i = xs ! j \<and> YS ! i = XS ! j"
    by auto
  then obtain j where j: "\<And>i. i < length YS \<Longrightarrow> ys ! i = xs ! (j i)"
    "\<And>i. i < length YS \<Longrightarrow> YS ! i = XS ! (j i)"
    "\<And>i. i < length YS \<Longrightarrow> j i < length XS"
    by metis
  show ?thesis
    using assms
    by (auto simp: Joints_def j ys intro!: exI[where x=e] nth_equalityI)
qed

lemma Joints_set_zip_subset:
  assumes "xs \<in> Joints XS"
  assumes "length xs = length XS"
  assumes "length ys = length YS"
  assumes "set (zip ys YS) \<subseteq> set (zip xs XS)"
  shows "ys \<in> Joints YS"
proof -
  from Joints_mapE assms obtain e where
    ys: "xs = map (\<lambda>x. aform_val e x) XS"
    and e: "\<And>i. e i \<in> {-1 .. 1}"
    by blast
  show "ys \<in> Joints YS"
    using e zipped_subset_mapped_Elem[OF ys e assms(2-4)]
    by (auto simp: Joints_def valuate_def intro!: exI[where x=e])
qed

lemma Joints_set_zip:
  assumes "ys \<in> Joints YS"
  assumes "length xs = length XS"
  assumes "length YS = length XS"
  assumes sets_eq: "set (zip xs XS) = set (zip ys YS)"
  shows "xs \<in> Joints XS"
proof -
  from assms have "length ys = length YS"
    by (auto simp: Joints_def valuate_def)
  from assms(1) this assms(2) show ?thesis
    by (rule Joints_set_zip_subset) (simp add: assms)
qed

definition Joints2 ::
    "'a::real_normed_vector aform list \<Rightarrow>'b::real_normed_vector aform \<Rightarrow> ('a list \<times> 'b) set"
  where "Joints2 XS Y = valuate (\<lambda>e. (map (aform_val e) XS, aform_val e Y))"

lemma Joints2E:
  assumes "zs_y \<in> Joints2 ZS Y"
  obtains e where
    "\<And>i. i < length (fst zs_y) \<Longrightarrow> (fst zs_y) ! i = aform_val e (ZS ! i)"
    "snd (zs_y) = aform_val e Y"
    "\<And>i. e i \<in> {-1..1}"
  using assms
  by atomize_elim (auto simp: Joints2_def Pi_iff valuate_ex)


subsection {* Domain *}

definition "pdevs_domain x = {i. pdevs_apply x i \<noteq> 0}"

lemma finite_pdevs_domain[intro, simp]: "finite (pdevs_domain x)"
  unfolding pdevs_domain_def by transfer

lemma in_pdevs_domain[simp]: "i \<in> pdevs_domain x \<longleftrightarrow> pdevs_apply x i \<noteq> 0"
  by (auto simp: pdevs_domain_def)


subsection {* Least Fresh Index *}

definition degree::"'a::real_vector pdevs \<Rightarrow> nat"
  where "degree x = (LEAST i. \<forall>j\<ge>i. pdevs_apply x j = 0)"

lemma degree[rule_format, intro, simp]:
  shows "\<forall>j\<ge>degree x. pdevs_apply x j = 0"
  unfolding degree_def
proof (rule LeastI_ex)
  from assms have "\<And>j. j > Max (pdevs_domain x) \<Longrightarrow> j \<notin> (pdevs_domain x)"
    by (metis Max_less_iff all_not_in_conv less_irrefl_nat finite_pdevs_domain)
  then show "\<exists>xa. \<forall>j\<ge>xa. pdevs_apply x j = 0"
    by (auto intro!: exI[where x="Max (pdevs_domain x) + 1"])
qed

lemma degree_le:
  assumes d: "\<forall>j \<ge> d. pdevs_apply x j = 0"
  shows "degree x \<le> d"
  unfolding degree_def
  by (rule Least_le) (rule d)

lemma degree_gt: "pdevs_apply x j \<noteq> 0 \<Longrightarrow> degree x > j"
  by auto

lemma pdevs_val_pdevs_domain: "pdevs_val e X = (\<Sum>i\<in>pdevs_domain X. e i *\<^sub>R pdevs_apply X i)"
  by (auto simp: pdevs_val_def intro!: suminf_finite)

lemma pdevs_val_setsum: "pdevs_val e X = (\<Sum>i < degree X. e i *\<^sub>R pdevs_apply X i)"
  by (auto intro!: degree_gt setsum.mono_neutral_cong_left simp: pdevs_val_pdevs_domain)

lemma pdevs_val_zero[simp]: "pdevs_val (\<lambda>_. 0) x = 0"
  by (auto simp: pdevs_val_setsum)

lemma degree_eqI:
  assumes "pdevs_apply x d \<noteq> 0"
  assumes "\<And>j. j > d \<Longrightarrow> pdevs_apply x j = 0"
  shows "degree x = Suc d"
  unfolding eq_iff
  by (auto intro!: degree_gt degree_le assms simp: Suc_le_eq)

lemma finite_degree_nonzero[intro, simp]: "finite {i. pdevs_apply x i \<noteq> 0}"
  by transfer (auto simp: vimage_def Collect_neg_eq)

lemma degree_eq_Suc_max:
  "degree x = (if (\<forall>i. pdevs_apply x i = 0) then 0 else Suc (Max {i. pdevs_apply x i \<noteq> 0}))"
proof -
  {
    assume "\<And>i. pdevs_apply x i = 0"
    hence ?thesis
      by auto (metis degree_le le_0_eq)
  } moreover {
    fix i assume "pdevs_apply x i \<noteq> 0"
    hence ?thesis
      using Max_in[OF finite_degree_nonzero, of x]
      by (auto intro!: degree_eqI) (metis Max.coboundedI[OF finite_degree_nonzero] in_pdevs_domain
        le_eq_less_or_eq less_asym pdevs_domain_def)
  } ultimately show ?thesis
    by blast
qed

lemma pdevs_val_degree_cong:
  assumes "b = d"
  assumes "\<And>i. i < degree b \<Longrightarrow> a i = c i"
  shows "pdevs_val a b = pdevs_val c d"
  using assms
  by (auto simp: pdevs_val_setsum)

abbreviation degree_aform::"'a::real_vector aform \<Rightarrow> nat"
  where "degree_aform X \<equiv> degree (snd X)"

lemma degree_cong: "(\<And>i. (pdevs_apply x i = 0) = (pdevs_apply y i = 0)) \<Longrightarrow> degree x = degree y"
  unfolding degree_def
  by auto

lemma Least_True_nat[intro, simp]: "(LEAST i::nat. True) = 0"
  by (metis (lifting) One_nat_def less_one not_less_Least not_less_eq)

lemma sorted_list_of_pdevs_domain_eq:
  "sorted_list_of_set (pdevs_domain X) = filter (op \<noteq> 0 o pdevs_apply X) [0..<degree X]"
  by (auto simp: degree_gt intro!: sorted_distinct_set_unique sorted_filter[of "\<lambda>x. x", simplified])


subsection {* Total Deviation *}

definition tdev::"'a::ordered_euclidean_space pdevs \<Rightarrow> 'a" where
  "tdev x = (\<Sum>i<degree x. \<bar>pdevs_apply x i\<bar>)"

lemma abs_pdevs_val_le_tdev: "e \<in> UNIV \<rightarrow> {-1 .. 1} \<Longrightarrow> \<bar>pdevs_val e x\<bar> \<le> tdev x"
  by (force simp: pdevs_val_setsum tdev_def abs_scaleR Pi_iff
    intro!: order_trans[OF setsum_abs] setsum_mono scaleR_left_le_one_le
    intro: abs_leI)


subsection {* Binary Pointwise Operations *}

definition binop_pdevs_raw::"('a::real_vector \<Rightarrow> 'b::real_vector \<Rightarrow> 'c::real_vector) \<Rightarrow>
    (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'c"
  where "binop_pdevs_raw f x y i = (if x i = 0 \<and> y i = 0 then 0 else f (x i) (y i))"

lemma nonzeros_binop_pdevs_subset:
  "{i. binop_pdevs_raw f x y i \<noteq> 0} \<subseteq> {i. x i \<noteq> 0} \<union> {i. y i \<noteq> 0}"
  by (auto simp: binop_pdevs_raw_def)

lift_definition binop_pdevs::
    "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a::real_vector pdevs \<Rightarrow> 'b::real_vector pdevs \<Rightarrow> 'c::real_vector pdevs"
  is binop_pdevs_raw
  using nonzeros_binop_pdevs_subset
  by (rule finite_subset) auto

lemma pdevs_apply_binop_pdevs[simp]: "pdevs_apply (binop_pdevs f x y) i =
  (if pdevs_apply x i = 0 \<and> pdevs_apply y i = 0 then 0 else f (pdevs_apply x i) (pdevs_apply y i))"
  by transfer (auto simp: binop_pdevs_raw_def)


subsection {* Addition *}

definition add_pdevs::"'a::real_vector pdevs \<Rightarrow> 'a pdevs \<Rightarrow> 'a pdevs"
  where "add_pdevs = binop_pdevs op +"

lemma pdevs_apply_add_pdevs[simp]:
  "pdevs_apply (add_pdevs X Y) n = pdevs_apply X n + pdevs_apply Y n"
  by (auto simp: add_pdevs_def)

lemma pdevs_val_add_pdevs[simp]:
  fixes x y::"'a::euclidean_space"
  shows "pdevs_val e (add_pdevs X Y) = pdevs_val e X + pdevs_val e Y"
proof -
  let ?sum = "\<lambda>m X. \<Sum>i < m. e i *\<^sub>R pdevs_apply X i"
  let ?m = "max (degree X) (degree Y)"
  have "pdevs_val e X + pdevs_val e Y = ?sum (degree X) X + ?sum (degree Y) Y"
    by (simp add: pdevs_val_setsum)
  also have "?sum (degree X) X = ?sum ?m X"
    by (rule setsum.mono_neutral_cong_left) auto
  also have "?sum (degree Y) Y = ?sum ?m Y"
    by (rule setsum.mono_neutral_cong_left) auto
  also have "?sum ?m X + ?sum ?m Y = (\<Sum>i < ?m. e i *\<^sub>R (pdevs_apply X i + pdevs_apply Y i))"
    by (simp add: scaleR_right_distrib setsum.distrib)
  also have "\<dots> = (\<Sum>i. e i *\<^sub>R (pdevs_apply X i + pdevs_apply Y i))"
    by (rule suminf_finite[symmetric]) auto
  also have "\<dots> = pdevs_val e (add_pdevs X Y)"
    by (simp add: pdevs_val_def)
  finally show "pdevs_val e (add_pdevs X Y) = pdevs_val e X + pdevs_val e Y" by simp
qed


subsection {* Total Deviation *}

lemma tdev_eq_zero_iff: fixes X::"real pdevs" shows "tdev X = 0 \<longleftrightarrow> (\<forall>e. pdevs_val e X = 0)"
  by (force simp add: pdevs_val_setsum tdev_def setsum_nonneg_eq_0_iff
    dest!: spec[where x="\<lambda>i. if pdevs_apply X i \<ge> 0 then 1 else -1"] split: split_if_asm)

lemma tdev_nonneg[intro, simp]: "tdev X \<ge> 0"
  by (auto simp: tdev_def)

lemma tdev_nonpos_iff[simp]: "tdev X \<le> 0 \<longleftrightarrow> tdev X = 0"
  by (auto simp: order.antisym)


subsection {* Unary Operations *}

definition unop_pdevs_raw::
    "('a::zero \<Rightarrow> 'b::zero) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'b"
  where "unop_pdevs_raw f x i = (if x i = 0 then 0 else f (x i))"

lemma nonzeros_unop_pdevs_subset: "{i. unop_pdevs_raw f x i \<noteq> 0} \<subseteq> {i. x i \<noteq> 0}"
  by (auto simp: unop_pdevs_raw_def)

lift_definition unop_pdevs::
    "('a \<Rightarrow> 'b) \<Rightarrow> 'a::zero pdevs \<Rightarrow> 'b::zero pdevs"
  is unop_pdevs_raw
  using nonzeros_unop_pdevs_subset
  by (rule finite_subset) auto

lemma pdevs_apply_unop_pdevs[simp]: "pdevs_apply (unop_pdevs f x) i =
  (if pdevs_apply x i = 0 then 0 else f (pdevs_apply x i))"
  by transfer (auto simp: unop_pdevs_raw_def)

lemma pdevs_domain_unop_linear:
  assumes "linear f"
  shows "pdevs_domain (unop_pdevs f x) \<subseteq> pdevs_domain x"
proof -
  interpret f: linear f by fact
  show ?thesis
    by (auto simp: f.zero)
qed

lemma
  pdevs_val_unop_linear:
  assumes "linear f"
  shows "pdevs_val e (unop_pdevs f x) = f (pdevs_val e x)"
proof -
  interpret f: linear f by fact
  have *: "\<And>i. (if pdevs_apply x i = 0 then 0 else f (pdevs_apply x i)) = f (pdevs_apply x i)"
    by (auto simp: f.zero)
  have "pdevs_val e (unop_pdevs f x) =
      (\<Sum>i\<in>pdevs_domain (unop_pdevs f x). e i *\<^sub>R f (pdevs_apply x i))"
    by (auto simp add: pdevs_val_pdevs_domain *)
  also have "\<dots> = (\<Sum>xa\<in>pdevs_domain x. e xa *\<^sub>R f (pdevs_apply x xa))"
    by (auto intro!: setsum.mono_neutral_cong_left)
  also have "\<dots> = f (pdevs_val e x)"
    by (auto simp add: pdevs_val_pdevs_domain f.setsum f.scaleR)
  finally show ?thesis .
qed


subsection {* Pointwise Scaling of Partial Deviations *}

definition scaleR_pdevs::"real \<Rightarrow> 'a::real_vector pdevs \<Rightarrow> 'a pdevs"
  where "scaleR_pdevs r x = unop_pdevs (op *\<^sub>R r) x"

lemma pdevs_apply_scaleR_pdevs[simp]:
  "pdevs_apply (scaleR_pdevs x Y) n = x *\<^sub>R pdevs_apply Y n"
  by (auto simp: scaleR_pdevs_def)

lemma degree_scaleR_pdevs[simp]: "degree (scaleR_pdevs r x) = (if r = 0 then 0 else degree x)"
  unfolding degree_def
  by auto

lemma pdevs_val_scaleR_pdevs[simp]:
  fixes x::real and Y::"'a::real_normed_vector pdevs"
  shows "pdevs_val e (scaleR_pdevs x Y) = x *\<^sub>R pdevs_val e Y"
  by (auto simp: pdevs_val_setsum scaleR_setsum_right ac_simps)


subsection {* Partial Deviations Scale Pointwise *}

definition pdevs_scaleR::"real pdevs \<Rightarrow> 'a::real_vector \<Rightarrow> 'a pdevs"
  where "pdevs_scaleR r x = unop_pdevs (\<lambda>r. r *\<^sub>R x) r"

lemma pdevs_apply_pdevs_scaleR[simp]:
  "pdevs_apply (pdevs_scaleR X y) n = pdevs_apply X n *\<^sub>R y"
  by (auto simp: pdevs_scaleR_def)

lemma degree_pdevs_scaleR[simp]: "degree (pdevs_scaleR r x) = (if x = 0 then 0 else degree r)"
  unfolding degree_def
  by auto

lemma pdevs_val_pdevs_scaleR[simp]:
  fixes X::"real pdevs" and y::"'a::real_normed_vector"
  shows "pdevs_val e (pdevs_scaleR X y) = pdevs_val e X *\<^sub>R y"
  by (auto simp: pdevs_val_setsum scaleR_setsum_left)


subsection {* Pointwise Unary Minus *}

definition uminus_pdevs::"'a::real_vector pdevs \<Rightarrow> 'a pdevs"
  where "uminus_pdevs = unop_pdevs uminus"

lemma pdevs_apply_uminus_pdevs[simp]: "pdevs_apply (uminus_pdevs x) = - pdevs_apply x"
  by (auto simp: uminus_pdevs_def)

lemma degree_uminus_pdevs[simp]: "degree (uminus_pdevs x) = degree x"
  by (rule degree_cong) simp

lemma pdevs_val_uminus_pdevs[simp]: "pdevs_val e (uminus_pdevs x) = - pdevs_val e x"
  unfolding pdevs_val_setsum
  by (auto simp: setsum_negf)

definition "uminus_aform X = (- fst X, uminus_pdevs (snd X))"

lemma fst_uminus_aform[simp]: "fst (uminus_aform Y) = - fst Y"
  by (simp add: uminus_aform_def)

lemma aform_val_uminus_aform[simp]: "aform_val e (uminus_aform X) = - aform_val e X"
  by (auto simp: uminus_aform_def aform_val_def)


subsection {* Constant *}

lift_definition zero_pdevs::"'a::zero pdevs" is "\<lambda>_. 0" by simp

lemma pdevs_apply_zero_pdevs[simp]: "pdevs_apply zero_pdevs i = 0"
  by transfer simp

lemma pdevs_val_zero_pdevs[simp]: "pdevs_val e zero_pdevs = 0"
  by (auto simp: pdevs_val_def)

definition "num_aform f = (f, zero_pdevs)"


subsection {* Inner Product *}

definition pdevs_inner::"'a::euclidean_space pdevs \<Rightarrow> 'a \<Rightarrow> real pdevs"
  where "pdevs_inner x b = unop_pdevs (\<lambda>x. x \<bullet> b) x"

lemma pdevs_apply_pdevs_inner[simp]: "pdevs_apply (pdevs_inner p a) i = pdevs_apply p i \<bullet> a"
  by (simp add: pdevs_inner_def)

lemma pdevs_val_pdevs_inner[simp]: "pdevs_val e (pdevs_inner p a) = pdevs_val e p \<bullet> a"
  by (auto simp add: inner_setsum_left pdevs_val_pdevs_domain intro!: setsum.mono_neutral_cong_left)

definition inner_aform::"'a::euclidean_space aform \<Rightarrow> 'a \<Rightarrow> real aform"
  where "inner_aform X b = (fst X \<bullet> b, pdevs_inner (snd X) b)"



subsection {* Inner Product Pair *}

definition inner2::"'a::euclidean_space \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real*real"
  where "inner2 x n l = (x \<bullet> n, x \<bullet> l)"

definition pdevs_inner2::"'a::euclidean_space pdevs \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (real*real) pdevs"
  where "pdevs_inner2 X n l = unop_pdevs (\<lambda>x. inner2 x n l) X"

lemma pdevs_apply_pdevs_inner2[simp]:
  "pdevs_apply (pdevs_inner2 p a b) i = (pdevs_apply p i \<bullet> a, pdevs_apply p i \<bullet> b)"
  by (simp add: pdevs_inner2_def inner2_def zero_prod_def)

definition inner2_aform::"'a::euclidean_space aform \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (real*real) aform"
  where "inner2_aform X a b = (inner2 (fst X) a b, pdevs_inner2 (snd X) a b)"

lemma linear_inner2[intro, simp]: "linear (\<lambda>x. inner2 x n i)"
  by unfold_locales (auto simp: inner2_def algebra_simps)

lemma aform_val_inner2_aform[simp]: "aform_val e (inner2_aform Z n i) = inner2 (aform_val e Z) n i"
proof -
  have "aform_val e (inner2_aform Z n i) = inner2 (fst Z) n i + inner2 (pdevs_val e (snd Z)) n i"
    by (auto simp: aform_val_def inner2_aform_def pdevs_inner2_def pdevs_val_unop_linear)
  also have "\<dots> = inner2 (aform_val e Z) n i"
    by (simp add: inner2_def algebra_simps aform_val_def)
  finally show ?thesis .
qed


subsection {* Update *}

lemma pdevs_val_upd[simp]:
  "pdevs_val (e(n := e')) X = pdevs_val e X - e n * pdevs_apply X n + e' * pdevs_apply X n"
  unfolding pdevs_val_def
  by (subst suminf_finite[OF finite.insertI[OF finite_degree_nonzero], of n X],
    auto simp: pdevs_val_def setsum.insert_remove)+

lemma nonzeros_fun_upd:
  "{i. (f(n := a)) i \<noteq> 0} \<subseteq> {i. f i \<noteq> 0} \<union> {n}"
  by (auto split: split_if_asm)

lift_definition pdev_upd::"'a::real_vector pdevs \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a pdevs"
  is "\<lambda>x n a. x(n:=a)"
  by (rule finite_subset[OF nonzeros_fun_upd]) simp

lemma pdevs_apply_pdev_upd[simp]:
  "pdevs_apply (pdev_upd X n x) = (pdevs_apply X)(n:=x)"
  by transfer simp

lemma pdevs_val_pdev_upd[simp]:
  "pdevs_val e (pdev_upd X n x) = pdevs_val e X + e n *\<^sub>R x - e n *\<^sub>R pdevs_apply X n"
  unfolding pdevs_val_def
  by (subst suminf_finite[OF finite.insertI[OF finite_degree_nonzero], of n X],
    auto simp: pdevs_val_def setsum.insert_remove)+

lemma degree_pdev_upd:
  assumes "x = 0 \<longleftrightarrow> pdevs_apply X n = 0"
  shows "degree (pdev_upd X n x) = degree X"
  using assms
  by (auto intro!: degree_cong split: split_if_asm)


subsection {* Inf/Sup *}

definition "Inf_aform X = fst X - tdev (snd X)"

definition "Sup_aform X = fst X + tdev (snd X)"

lemma Inf_aform:
  assumes "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  shows "Inf_aform X \<le> aform_val e X"
  using order_trans[OF abs_ge_minus_self abs_pdevs_val_le_tdev[OF assms]]
  by (auto simp: Inf_aform_def aform_val_def minus_le_iff)

lemma Sup_aform:
  assumes "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  shows "aform_val e X \<le> Sup_aform X"
  using order_trans[OF abs_ge_self abs_pdevs_val_le_tdev[OF assms]]
  by (auto simp: Sup_aform_def aform_val_def)


subsection {* Minkowski Sum *}

definition msum_pdevs_raw::"nat\<Rightarrow>(nat \<Rightarrow> 'a::real_vector)\<Rightarrow>(nat \<Rightarrow> 'a)\<Rightarrow>(nat\<Rightarrow>'a)" where
  "msum_pdevs_raw n x y i = (if i < n then x i else y (i - n))"

lemma nonzeros_msum_pdevs_raw:
  "{i. msum_pdevs_raw n f g i \<noteq> 0} = ({0..<n} \<inter> {i. f i \<noteq> 0}) \<union> op + n ` ({i. g i \<noteq> 0})"
  by (force simp: msum_pdevs_raw_def not_less split: split_if_asm)

lift_definition msum_pdevs::"nat\<Rightarrow>'a::real_vector pdevs\<Rightarrow>'a pdevs\<Rightarrow>'a pdevs" is msum_pdevs_raw
  unfolding nonzeros_msum_pdevs_raw by simp

lemma pdevs_apply_msum_pdevs: "pdevs_apply (msum_pdevs n f g) i =
  (if i < n then pdevs_apply f i else pdevs_apply g (i - n))"
  by transfer (auto simp: msum_pdevs_raw_def)

lemma degree_least_nonzero:
  assumes "degree f \<noteq> 0"
  shows "pdevs_apply f (degree f - 1) \<noteq> 0"
proof
  assume H: "pdevs_apply f (degree f - 1) = 0"
  {
    fix j
    assume "j\<ge>degree f - 1"
    with H have "pdevs_apply f j = 0"
      by (cases "degree f - 1 = j") auto
  }
  from degree_le[rule_format, OF this]
  have "degree f \<le> degree f - 1"
    by blast
  with assms show False by simp
qed

lemma degree_leI:
  assumes "(\<And>i. pdevs_apply y i = 0 \<Longrightarrow> pdevs_apply x i = 0)"
  shows "degree x \<le> degree y"
proof cases
  assume "degree x \<noteq> 0"
  from degree_least_nonzero[OF this]
  have "pdevs_apply y (degree x - 1) \<noteq> 0"
    by (auto simp: assms split: split_if_asm)
  from degree_gt[OF this] show ?thesis
    by simp
qed simp

lemma degree_msum_pdevs_ge1:
  shows "degree f \<le> n \<Longrightarrow> degree f \<le> degree (msum_pdevs n f g)"
  by (rule degree_leI) (auto simp: pdevs_apply_msum_pdevs split: split_if_asm)

lemma degree_msum_pdevs_ge2:
  assumes "degree f \<le> n"
  shows "degree g \<le> degree (msum_pdevs n f g) - n"
proof cases
  assume "degree g \<noteq> 0"
  hence "pdevs_apply g (degree g - 1) \<noteq> 0" by (rule degree_least_nonzero)
  hence "pdevs_apply (msum_pdevs n f g) (n + degree g - 1) \<noteq> 0"
    using assms
    by (auto simp: pdevs_apply_msum_pdevs)
  from degree_gt[OF this]
  show ?thesis
    by simp
qed simp

lemma
  setsum_msum_pdevs_cases:
  assumes "degree f \<le> n"
  assumes [simp]: "\<And>i. e i 0 = 0"
  shows
    "(\<Sum>i <degree (msum_pdevs n f g).
      e i (if i < n then pdevs_apply f i else pdevs_apply g (i - n))) =
    (\<Sum>i <degree f. e i (pdevs_apply f i)) + (\<Sum>i <degree g. e (i + n) (pdevs_apply g i))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sum>i\<in>{..<degree (msum_pdevs n f g)} \<inter> {i. i < n}. e i (pdevs_apply f i)) +
    (\<Sum>i\<in>{..<degree (msum_pdevs n f g)} \<inter> - {i. i < n}. e i (pdevs_apply g (i - n)))"
    (is "_ = ?sum_f + ?sum_g")
     by (simp add: setsum.If_cases if_distrib)
  also have "?sum_f = (\<Sum>i = 0..<degree f. e i (pdevs_apply f i))"
    using assms degree_msum_pdevs_ge1[of f n g]
    by (intro setsum.mono_neutral_cong_right) auto
  also
  have "?sum_g = (\<Sum>i\<in>{0 + n..<degree (msum_pdevs n f g) - n + n}. e i (pdevs_apply g (i - n)))"
    by (rule setsum.cong) auto
  also have "\<dots> = (\<Sum>i = 0..<degree (msum_pdevs n f g) - n. e (i + n) (pdevs_apply g (i + n - n)))"
    by (rule setsum_shift_bounds_nat_ivl)
  also have "\<dots> = (\<Sum>i = 0..<degree g. e (i + n) (pdevs_apply g i))"
    using assms degree_msum_pdevs_ge2[of f n]
    by (intro setsum.mono_neutral_cong_right) (auto intro!: setsum.mono_neutral_cong_right)
  finally show ?thesis
    by (simp add: atLeast0LessThan)
qed

lemma tdev_msum_pdevs: "degree f \<le> n \<Longrightarrow> tdev (msum_pdevs n f g) = tdev f + tdev g"
  by (auto simp: tdev_def pdevs_apply_msum_pdevs intro!: setsum_msum_pdevs_cases)

lemma pdevs_val_msum_pdevs:
  "degree f \<le> n \<Longrightarrow> pdevs_val e (msum_pdevs n f g) = pdevs_val e f + pdevs_val (\<lambda>i. e (i + n)) g"
  by (auto simp: pdevs_val_setsum pdevs_apply_msum_pdevs intro!: setsum_msum_pdevs_cases)

definition msum_aform::"nat \<Rightarrow> 'a::real_vector aform \<Rightarrow> 'a aform \<Rightarrow> 'a aform"
  where "msum_aform n f g = (fst f + fst g, msum_pdevs n (snd f) (snd g))"

lemma fst_msum_aform[simp]: "fst (msum_aform n f g) = fst f + fst g"
  by (simp add: msum_aform_def)

lemma snd_msum_aform[simp]: "snd (msum_aform n f g) = msum_pdevs n (snd f) (snd g)"
  by (simp add: msum_aform_def)

lemma finite_nonzero_summable: "finite {i. f i \<noteq> 0} \<Longrightarrow> summable f"
  by (auto intro!: sums_summable sums_finite)

lemma aform_val_msum_aform:
  assumes "degree_aform f \<le> n"
  shows "aform_val e (msum_aform n f g) = aform_val e f + aform_val (\<lambda>i. e (i + n)) g"
  using assms
  by (auto simp: pdevs_val_msum_pdevs aform_val_def)

lemma Inf_aform_msum_aform:
  "degree_aform X \<le> n \<Longrightarrow> Inf_aform (msum_aform n X Y) = Inf_aform X + Inf_aform Y"
  by (simp add: Inf_aform_def tdev_msum_pdevs)

lemma Sup_aform_msum_aform:
  "degree_aform X \<le> n \<Longrightarrow> Sup_aform (msum_aform n X Y) = Sup_aform X + Sup_aform Y"
  by (simp add: Sup_aform_def tdev_msum_pdevs)

definition "independent_aform X Y = msum_aform (degree_aform X) (0, zero_pdevs) Y"

lemma degree_zero_pdevs[simp]: "degree zero_pdevs = 0"
  by (metis degree_least_nonzero pdevs_apply_zero_pdevs)

lemma independent_aform_Joints:
  assumes "x \<in> Affine X"
  assumes "y \<in> Affine Y"
  shows "[x, y] \<in> Joints [X, independent_aform X Y]"
  using assms
  unfolding Affine_def valuate_def Joints_def
  apply safe
  subgoal premises prems for e ea
    using prems
    by (intro image_eqI[where x="\<lambda>i. if i < degree_aform X then e i else ea (i - degree_aform X)"])
      (auto simp: aform_val_def pdevs_val_msum_pdevs Pi_iff
      independent_aform_def intro!: pdevs_val_degree_cong)
  done

lemma Affine_msum_aform:
  assumes "d \<ge> degree_aform X"
  shows "Affine (msum_aform d X Y) = {x + y |x y. x \<in> Affine X \<and> y \<in> Affine Y}"
  unfolding Affine_def valuate_def
proof (safe, goal_cases)
  case (1 x e)
  thus ?case
    using assms
    by (intro exI[where x = "aform_val e X"] exI[where x = "aform_val ((\<lambda>i. e (i + d))) Y"])
      (auto simp add: aform_val_def pdevs_val_msum_pdevs)
next
  case (2 x xa y e ea)
  thus ?case using assms
    by (intro image_eqI[where x="\<lambda>i. if i < d then e i else ea (i - d)"])
      (force simp: aform_val_def pdevs_val_msum_pdevs intro!: pdevs_val_degree_cong)+
qed

lemma Affine_zero_pdevs[simp]: "Affine (0, zero_pdevs) = {0}"
  by (force simp: Affine_def valuate_def aform_val_def)

lemma Affine_independent_aform:
  "Affine (independent_aform X Y) = Affine Y"
  by (auto simp: independent_aform_def Affine_msum_aform)

lemma
  abs_diff_eq1:
  fixes l u::"'a::ordered_euclidean_space"
  shows "l \<le> u \<Longrightarrow> \<bar>u - l\<bar> = u - l"
  by (metis abs_of_nonneg diff_add_cancel le_add_same_cancel2)

lemma compact_setsum:
  fixes f :: "'a \<Rightarrow> 'b::topological_space \<Rightarrow> 'c::real_normed_vector"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> compact (S i)"
  assumes "\<And>i. i \<in> I \<Longrightarrow> continuous_on (S i) (f i)"
  assumes "I \<subseteq> J"
  shows "compact {\<Sum>i\<in>I. f i (x i) | x. x \<in> Pi J S}"
  using assms
proof (induct I)
  case empty
  thus ?case
  proof (cases "\<exists>x. x \<in> Pi J S")
    case False
    hence *: "{\<Sum>i\<in>{}. f i (x i) |x. x \<in> Pi J S} = {}"
      by (auto simp: Pi_iff)
    show ?thesis unfolding * by simp
  qed auto
next
  case (insert a I)
  hence "{\<Sum>i\<in>insert a I. f i (xa i) |xa. xa \<in> Pi J S}
    = {x + y |x y. x \<in> f a ` S a \<and> y \<in> {\<Sum>i\<in>I. f i (x i) |x. x \<in> Pi J S}}"
  proof safe
    fix s x
    assume "s \<in> S a" "x \<in> Pi J S"
    thus "\<exists>xa. f a s + (\<Sum>i\<in>I. f i (x i)) = (\<Sum>i\<in>insert a I. f i (xa i)) \<and> xa \<in> Pi J S"
      using insert
      by (auto intro!: exI[where x="x(a:=s)"] setsum.cong)
  qed force
  also have "compact \<dots>"
    using insert
    by (intro compact_sums) (auto intro!: compact_continuous_image)
  finally show ?case .
qed

lemma compact_Affine:
  fixes X::"'a::ordered_euclidean_space aform"
  shows "compact (Affine X)"
proof -
  have "Affine X = {x + y|x y. x \<in> {fst X} \<and>
      y \<in> {(\<Sum>i \<in> {0..<degree_aform X}. e i *\<^sub>R pdevs_apply (snd X) i) | e. e \<in> UNIV \<rightarrow> {-1 .. 1}}}"
    by (auto simp: Affine_def valuate_def aform_val_def pdevs_val_setsum atLeast0LessThan)
  also have "compact \<dots>"
    by (rule compact_sums) (auto intro!: compact_setsum continuous_intros)
  finally show ?thesis .
qed

lemma Joints2_JointsI:
  "(xs, x) \<in> Joints2 XS X \<Longrightarrow> x#xs \<in> Joints (X#XS)"
  by (auto simp: Joints_def Joints2_def valuate_def)


subsection {* Splitting *}

definition "split_aform X i =
  (let xi = pdevs_apply (snd X) i /\<^sub>R 2
  in ((fst X - xi, pdev_upd (snd X) i xi), (fst X + xi, pdev_upd (snd X) i xi)))"

lemma split_aformE:
  assumes "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  assumes "x = aform_val e X"
  obtains err where "x = aform_val (e(i:=err)) (fst (split_aform X i))" "err \<in> {-1 .. 1}"
    | err where "x = aform_val (e(i:=err)) (snd (split_aform X i))" "err \<in> {-1 .. 1}"
proof (atomize_elim)
  let ?thesis = "(\<exists>err. x = aform_val (e(i := err)) (fst (split_aform X i)) \<and> err \<in> {- 1..1}) \<or>
    (\<exists>err. x = aform_val (e(i := err)) (snd (split_aform X i)) \<and> err \<in> {- 1..1})"
  {
    assume "pdevs_apply (snd X) i = 0"
    hence "X = fst (split_aform X i)"
      by (auto simp: split_aform_def intro!: prod_eqI pdevs_eqI)
    with assms have ?thesis by (auto intro!: exI[where x="e i"])
  } moreover {
    assume "pdevs_apply (snd X) i \<noteq> 0"
    hence [simp]: "degree_aform X > i"
      by (rule degree_gt)
    note assms(2)
    also
    have "aform_val e X = fst X + (\<Sum>i<degree_aform X. e i *\<^sub>R pdevs_apply (snd X) i)"
      by (simp add: aform_val_def pdevs_val_setsum)
    also
    have rewr: "{..<degree_aform X} = {0..<degree_aform X} - {i} \<union> {i}"
      by auto
    have "(\<Sum>i<degree_aform X. e i *\<^sub>R pdevs_apply (snd X) i) =
        (\<Sum>i \<in> {0..<degree_aform X} - {i}. e i *\<^sub>R pdevs_apply (snd X) i) +
        e i *\<^sub>R pdevs_apply (snd X) i"
      by (subst rewr, subst setsum.union_disjoint) auto
    finally have "x = fst X + \<dots>" .
    hence "x = aform_val (e(i:=2 * e i - 1)) (snd (split_aform X i))"
        "x = aform_val (e(i:=2 * e i + 1)) (fst (split_aform X i))"
      by (auto simp: aform_val_def split_aform_def Let_def pdevs_val_setsum atLeast0LessThan
        Diff_eq degree_pdev_upd if_distrib setsum.If_cases field_simps
        scaleR_left_distrib[symmetric])
    moreover
    have "2 * e i - 1 \<in> {-1 .. 1} \<or> 2 * e i + 1 \<in> {-1 .. 1}"
      using assms by (auto simp: not_le Pi_iff dest!: spec[where x=i])
    ultimately have ?thesis by blast
  } ultimately show ?thesis by blast
qed

lemma pdevs_val_add: "pdevs_val (\<lambda>i. e i + f i) xs = pdevs_val e xs + pdevs_val f xs"
  by (auto simp: pdevs_val_pdevs_domain algebra_simps setsum.distrib)

lemma pdevs_val_minus: "pdevs_val (\<lambda>i. e i - f i) xs = pdevs_val e xs - pdevs_val f xs"
  by (auto simp: pdevs_val_pdevs_domain algebra_simps setsum_subtractf)

lemma pdevs_val_cmul: "pdevs_val (\<lambda>i. u * e i) xs = u *\<^sub>R pdevs_val e xs"
  by (auto simp: pdevs_val_pdevs_domain scaleR_setsum_right)

lemma atLeastAtMost_absI: "- a \<le> a \<Longrightarrow> \<bar>x::real\<bar> \<le> \<bar>a\<bar> \<Longrightarrow> x \<in> atLeastAtMost (- a) a"
  by auto

lemma divide_atLeastAtMost_1_absI: "\<bar>x::real\<bar> \<le> \<bar>a\<bar> \<Longrightarrow> x/a \<in> {-1 .. 1}"
  by (intro atLeastAtMost_absI) (auto simp: divide_le_eq_1)

lemma convex_scaleR_aux: "u + v = 1 \<Longrightarrow> u *\<^sub>R x + v *\<^sub>R x = (x::'a::real_vector)"
  by (metis scaleR_add_left scaleR_one)

lemma convex_mult_aux: "u + v = 1 \<Longrightarrow> u * x + v * x = (x::real)"
  using convex_scaleR_aux[of u v x] by simp

lemma convex_Affine: "convex (Affine X)"
proof (rule convexI)
  fix x y::'a and u v::real
  assume "x \<in> Affine X" "y \<in> Affine X" and convex: "0 \<le> u" "0 \<le> v" "u + v = 1"
  then obtain e f where x: "x = aform_val e X" "e \<in> UNIV \<rightarrow> {-1 .. 1}"
    and y: "y = aform_val f X" "f \<in> UNIV \<rightarrow> {-1 .. 1}"
    by (auto simp: Affine_def valuate_def)
  let ?conv = "\<lambda>i. u * e i + v * f i"
  {
    fix i
    have "\<bar>?conv i\<bar> \<le> u * \<bar>e i\<bar> + v * \<bar>f i\<bar>"
      using convex by (intro order_trans[OF abs_triangle_ineq]) (simp add: abs_mult)
    also have "\<dots> \<le> 1"
      using convex x y
      by (intro convex_bound_le) (auto simp: Pi_iff abs_real_def)
    finally have "?conv i \<le> 1" "-1 \<le> ?conv i"
      by (auto simp: abs_real_def split: split_if_asm)
  }
  thus "u *\<^sub>R x + v *\<^sub>R y \<in> Affine X"
    using convex x y
    by (auto simp: Affine_def valuate_def aform_val_def pdevs_val_add pdevs_val_cmul algebra_simps
      convex_scaleR_aux intro!: image_eqI[where x="?conv"])
qed

lemma segment_in_aform_val:
  assumes "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  assumes "f \<in> UNIV \<rightarrow> {-1 .. 1}"
  shows "closed_segment (aform_val e X) (aform_val f X) \<subseteq> Affine X"
proof -
  have "aform_val e X \<in> Affine X" "aform_val f X \<in> Affine X"
    using assms by (auto simp: Affine_def valuate_def)
  with convex_Affine[of X, simplified convex_contains_segment]
  show ?thesis
    by simp
qed


subsection {* From List of Generators *}

lift_definition pdevs_of_list::"'a::zero list \<Rightarrow> 'a pdevs"
  is "\<lambda>xs i. if i < length xs then xs ! i else 0"
  by auto

lemma pdevs_apply_pdevs_of_list:
  "pdevs_apply (pdevs_of_list xs) i = (if i < length xs then xs ! i else 0)"
  by transfer simp

lemma pdevs_apply_pdevs_of_list_Nil[simp]:
  "pdevs_apply (pdevs_of_list []) i = 0"
  by transfer auto

lemma pdevs_apply_pdevs_of_list_Cons:
  "pdevs_apply (pdevs_of_list (x # xs)) i =
    (if i = 0 then x else pdevs_apply (pdevs_of_list xs) (i - 1))"
  by transfer auto

lemma pdevs_domain_pdevs_of_list_Cons[simp]: "pdevs_domain (pdevs_of_list (x # xs)) =
  (if x = 0 then {} else {0}) \<union> op + 1 ` pdevs_domain (pdevs_of_list xs)"
  by (force simp: pdevs_apply_pdevs_of_list_Cons split: split_if_asm)

lemma pdevs_val_pdevs_of_list_eq[simp]:
  "pdevs_val e (pdevs_of_list (x # xs)) = e 0 *\<^sub>R x + pdevs_val (e o op + 1) (pdevs_of_list xs)"
proof -
  have "pdevs_val e (pdevs_of_list (x # xs)) =
    (\<Sum>i\<in>pdevs_domain (pdevs_of_list (x # xs)) \<inter> {0}. e i *\<^sub>R x) +
    (\<Sum>i\<in>pdevs_domain (pdevs_of_list (x # xs)) \<inter> - {0}.
      e i *\<^sub>R pdevs_apply (pdevs_of_list xs) (i - Suc 0))"
    (is "_ = ?l + ?r")
    by (simp add: pdevs_val_pdevs_domain if_distrib setsum.If_cases pdevs_apply_pdevs_of_list_Cons)
  also
  have "?r = (\<Sum>i\<in>pdevs_domain (pdevs_of_list xs). e (Suc i) *\<^sub>R pdevs_apply (pdevs_of_list xs) i)"
    by (rule setsum.reindex_cong[of "\<lambda>i. i + 1"]) auto
  also have "\<dots> = pdevs_val (e o op + 1) (pdevs_of_list xs)"
    by (simp add: pdevs_val_pdevs_domain  )
  also have "?l = (\<Sum>i\<in>{0}. e i *\<^sub>R x)"
    by (rule setsum.mono_neutral_cong_left) auto
  also have "\<dots> = e 0 *\<^sub>R x" by simp
  finally show ?thesis .
qed

lemma
  less_degree_pdevs_of_list_imp_less_length:
  assumes "i < degree (pdevs_of_list xs)"
  shows "i < length xs"
proof -
  from assms have "pdevs_apply (pdevs_of_list xs) (degree (pdevs_of_list xs) - 1) \<noteq> 0"
    by (metis degree_least_nonzero less_nat_zero_code)
  hence "degree (pdevs_of_list xs) - 1 < length xs"
    by (simp add: pdevs_apply_pdevs_of_list split: split_if_asm)
  with assms show ?thesis
    by simp
qed

lemma tdev_pdevs_of_list[simp]: "tdev (pdevs_of_list xs) = listsum (map abs xs)"
  by (auto simp: tdev_def pdevs_apply_pdevs_of_list listsum_setsum_nth
    less_degree_pdevs_of_list_imp_less_length
    intro!: setsum.mono_neutral_cong_left degree_gt)

lemma pdevs_of_list_Nil[simp]: "pdevs_of_list [] = zero_pdevs"
  by (auto intro!: pdevs_eqI)

lemma pdevs_val_inj_setsumI:
  fixes K::"'a set" and g::"'a \<Rightarrow> nat"
  assumes "finite K"
  assumes "inj_on g K"
  assumes "pdevs_domain x \<subseteq> g ` K"
  assumes "\<And>i. i \<in> K \<Longrightarrow> g i \<notin> pdevs_domain x \<Longrightarrow> f i = 0"
  assumes "\<And>i. i \<in> K \<Longrightarrow> g i \<in> pdevs_domain x \<Longrightarrow> f i = e (g i) *\<^sub>R pdevs_apply x (g i)"
  shows "pdevs_val e x = (\<Sum>i\<in>K. f i)"
proof -
  have [simp]: "inj_on (the_inv_into K g) (pdevs_domain x)"
    using assms
    by (auto simp: intro!: subset_inj_on[OF inj_on_the_inv_into])
  {
    fix y assume y: "y \<in> pdevs_domain x"
    have g_inv: "g (the_inv_into K g y) = y"
      by (meson assms(2) assms(3) y f_the_inv_into_f subset_eq)
    have inv_in: "the_inv_into K g y \<in> K"
      by (meson assms(2) assms(3) y subset_iff in_pdevs_domain the_inv_into_into)
    have inv3: "the_inv_into (pdevs_domain x) (the_inv_into K g) (the_inv_into K g y) =
        g (the_inv_into K g y)"
      using assms y
      by (subst the_inv_into_f_f) (auto simp: f_the_inv_into_f[OF assms(2)])
    note g_inv inv_in inv3
  } note this[simp]
  have "pdevs_val e x = (\<Sum>i\<in>pdevs_domain x. e i *\<^sub>R pdevs_apply x i)"
    by (simp add: pdevs_val_pdevs_domain)
  also have "\<dots> = (\<Sum>i \<in> the_inv_into K g ` pdevs_domain x. e (g i) *\<^sub>R pdevs_apply x (g i))"
    by (rule setsum.reindex_cong[OF inj_on_the_inv_into]) auto
  also have "\<dots> = (\<Sum>i\<in>K. f i)"
    using assms
    by (intro setsum.mono_neutral_cong_left) (auto simp: the_inv_into_image_eq)
  finally show ?thesis .
qed

lemma pdevs_domain_pdevs_of_list_le: "pdevs_domain (pdevs_of_list xs) \<subseteq> {0..<length xs}"
  by (auto simp: pdevs_apply_pdevs_of_list split: split_if_asm)

lemma pdevs_val_zip: "pdevs_val e (pdevs_of_list xs) = (\<Sum>(i,x)\<leftarrow>zip [0..<length xs] xs. e i *\<^sub>R x)"
  by (auto simp: listsum_distinct_conv_setsum_set
    in_set_zip image_fst_zip pdevs_apply_pdevs_of_list distinct_zipI1
    intro!: pdevs_val_inj_setsumI[of _ fst]
    split: split_if_asm)

lemma scaleR_listsum:
  fixes xs::"'a::real_vector list"
  shows "a *\<^sub>R listsum xs = listsum (map (scaleR a) xs)"
  by (induct xs) (auto simp: algebra_simps)

lemma pdevs_val_const_pdevs_of_list: "pdevs_val (\<lambda>_. c) (pdevs_of_list xs) = c *\<^sub>R listsum xs"
  unfolding pdevs_val_zip split_beta' scaleR_listsum
  by (rule arg_cong) (auto intro!: nth_equalityI)

lemma pdevs_val_partition:
  assumes "e \<in> UNIV \<rightarrow> I"
  obtains f g where "pdevs_val e (pdevs_of_list xs) =
    pdevs_val f (pdevs_of_list (filter p xs)) +
    pdevs_val g (pdevs_of_list (filter (Not o p) xs))"
    "f \<in> UNIV \<rightarrow> I"
    "g \<in> UNIV \<rightarrow> I"
proof -
  obtain i where i: "i \<in> I"
    by (metis assms funcset_mem iso_tuple_UNIV_I)
  let ?zip = "zip [0..<length xs] xs"
  def part \<equiv> "partition (p \<circ> snd) ?zip"
  let ?f =
    "(\<lambda>n. if n < degree (pdevs_of_list (filter p xs)) then e (map fst (fst part) ! n) else i)"
  let ?g =
    "(\<lambda>n. if n < degree (pdevs_of_list (filter (Not \<circ> p) xs))
      then e (map fst (snd part) ! n)
      else i)"
  show ?thesis
  proof
    have "pdevs_val e (pdevs_of_list xs) = (\<Sum>(i,x)\<leftarrow>?zip. e i *\<^sub>R x)"
      by (rule pdevs_val_zip)
    also have "\<dots> = (\<Sum>(i, x)\<in>set ?zip. e i *\<^sub>R x)"
      by (simp add: listsum_distinct_conv_setsum_set distinct_zipI1)
    also
    have [simp]: "set (fst part) \<inter> set (snd part) = {}"
      by (auto simp: part_def)
    from partition_set[of "p o snd" ?zip "fst part" "snd part"]
    have "set ?zip = set (fst part) \<union> set (snd part)"
      by (auto simp: part_def)
    also have "(\<Sum>a\<in>set (fst part) \<union> set (snd part). case a of (i, x) \<Rightarrow> e i *\<^sub>R x) =
        (\<Sum>(i, x)\<in>set (fst part). e i *\<^sub>R x) + (\<Sum>(i, x)\<in>set (snd part). e i *\<^sub>R x)"
      by (auto simp: split_beta setsum_Un)
    also
    have "(\<Sum>(i, x)\<in>set (fst part). e i *\<^sub>R x) = (\<Sum>(i, x)\<leftarrow>(fst part). e i *\<^sub>R x)"
      by (simp add: listsum_distinct_conv_setsum_set distinct_zipI1 part_def)
    also have "\<dots> = (\<Sum>i<length (fst part). case (fst part ! i) of (i, x) \<Rightarrow> e i *\<^sub>R x)"
      by (subst listsum_setsum_nth) (simp add: split_beta' atLeast0LessThan)
    also have "\<dots> =
      pdevs_val (\<lambda>n. e (map fst (fst part) ! n)) (pdevs_of_list (map snd (fst part)))"
      by (force
        simp: pdevs_val_zip listsum_distinct_conv_setsum_set distinct_zipI1 split_beta' in_set_zip
        intro!:
          setsum.reindex_cong[where l=fst] image_eqI[where x = "(x, map snd (fst part) ! x)" for x])
    also
    have "(\<Sum>(i, x)\<in>set (snd part). e i *\<^sub>R x) = (\<Sum>(i, x)\<leftarrow>(snd part). e i *\<^sub>R x)"
      by (simp add: listsum_distinct_conv_setsum_set distinct_zipI1 part_def)
    also have "\<dots> = (\<Sum>i<length (snd part). case (snd part ! i) of (i, x) \<Rightarrow> e i *\<^sub>R x)"
      by (subst listsum_setsum_nth) (simp add: split_beta' atLeast0LessThan)
    also have "\<dots> =
      pdevs_val (\<lambda>n. e (map fst (snd part) ! n)) (pdevs_of_list (map snd (snd part)))"
      by (force simp: pdevs_val_zip listsum_distinct_conv_setsum_set distinct_zipI1 split_beta'
        in_set_zip
        intro!: setsum.reindex_cong[where l=fst]
          image_eqI[where x = "(x, map snd (snd part) ! x)" for x])
    also
    have "pdevs_val (\<lambda>n. e (map fst (fst part) ! n)) (pdevs_of_list (map snd (fst part))) =
      pdevs_val (\<lambda>n.
          if n < degree (pdevs_of_list (map snd (fst part))) then e (map fst (fst part) ! n) else i)
        (pdevs_of_list (map snd (fst part)))"
      by (rule pdevs_val_degree_cong) simp_all
    also
    have "pdevs_val (\<lambda>n. e (map fst (snd part) ! n)) (pdevs_of_list (map snd (snd part))) =
      pdevs_val (\<lambda>n.
          if n < degree (pdevs_of_list (map snd (snd part))) then e (map fst (snd part) ! n) else i)
        (pdevs_of_list (map snd (snd part)))"
      by (rule pdevs_val_degree_cong) simp_all
    also have "map snd (snd part) = filter (Not o p) xs"
      by (simp add: part_def filter_map[symmetric] o_assoc)
    also have "map snd (fst part) = filter p xs"
      by (simp add: part_def filter_map[symmetric])
    finally
    show
      "pdevs_val e (pdevs_of_list xs) =
        pdevs_val ?f (pdevs_of_list (filter p xs)) +
        pdevs_val ?g (pdevs_of_list (filter (Not \<circ> p) xs))" .
    show "?f \<in> UNIV \<rightarrow> I" "?g \<in> UNIV \<rightarrow> I"
      using assms `i\<in>I`
      by (auto simp: Pi_iff)
  qed
qed

lemma pdevs_apply_pdevs_of_list_append:
  "pdevs_apply (pdevs_of_list (xs @ zs)) i =
    (if i < length xs
    then pdevs_apply (pdevs_of_list xs) i else pdevs_apply (pdevs_of_list zs) (i - length xs))"
  by (auto simp: pdevs_apply_pdevs_of_list nth_append)

lemma degree_pdevs_of_list_le_length[intro, simp]: "degree (pdevs_of_list xs) \<le> length xs"
  by (metis less_irrefl_nat le_less_linear less_degree_pdevs_of_list_imp_less_length)

lemma degree_pdevs_of_list_append:
  "degree (pdevs_of_list (xs @ ys)) \<le> length xs + degree (pdevs_of_list ys)"
  by (rule degree_le) (auto simp: pdevs_apply_pdevs_of_list_append)

lemma pdevs_val_pdevs_of_list_append:
  assumes "f \<in> UNIV \<rightarrow> I"
  assumes "g \<in> UNIV \<rightarrow> I"
  obtains e where
    "pdevs_val f (pdevs_of_list xs) + pdevs_val g (pdevs_of_list ys) =
      pdevs_val e (pdevs_of_list (xs @ ys))"
    "e \<in> UNIV \<rightarrow> I"
proof
  let ?e = "(\<lambda>i. if i < length xs then f i else g (i - length xs))"
  have f: "pdevs_val f (pdevs_of_list xs) =
      (\<Sum>i\<in>{..<length xs}. ?e i *\<^sub>R pdevs_apply (pdevs_of_list (xs @ ys)) i)"
    by (auto simp: pdevs_val_setsum degree_gt pdevs_apply_pdevs_of_list_append
      intro: setsum.mono_neutral_cong_left)
  have g: "pdevs_val g (pdevs_of_list ys) =
      (\<Sum>i=length xs ..<length xs + degree (pdevs_of_list ys).
        ?e i *\<^sub>R pdevs_apply (pdevs_of_list (xs @ ys)) i)"
    (is "_ = ?sg")
    by (auto simp: pdevs_val_setsum pdevs_apply_pdevs_of_list_append
      intro!: inj_onI image_eqI[where x="length xs + x" for x]
        setsum.reindex_cong[where l="\<lambda>i. i - length xs"])
  show "pdevs_val f (pdevs_of_list xs) + pdevs_val g (pdevs_of_list ys) =
      pdevs_val ?e (pdevs_of_list (xs @ ys))"
    unfolding f g
    by (subst setsum.union_disjoint[symmetric])
      (force simp: pdevs_val_setsum ivl_disj_un degree_pdevs_of_list_append
        intro!: setsum.mono_neutral_cong_right
        split: split_if_asm)+
  show "?e \<in> UNIV \<rightarrow> I"
    using assms by (auto simp: Pi_iff)
qed

lemma
  setsum_general_mono:
  fixes f::"'a\<Rightarrow>('b::ordered_ab_group_add)"
  assumes [simp,intro]: "finite s" "finite t"
  assumes f: "\<And>x. x \<in> s - t \<Longrightarrow> f x \<le> 0"
  assumes g: "\<And>x. x \<in> t - s \<Longrightarrow> g x \<ge> 0"
  assumes fg: "\<And>x. x \<in> s \<inter> t \<Longrightarrow> f x \<le> g x"
  shows "(\<Sum>x \<in> s. f x) \<le> (\<Sum>x \<in> t. g x)"
proof -
  have "s = (s - t) \<union> (s \<inter> t)" and [intro, simp]: "(s - t) \<inter> (s \<inter> t) = {}" by auto
  hence "(\<Sum>x \<in> s. f x) = (\<Sum>x \<in> s - t \<union> s \<inter> t. f x)"
    using assms by simp
  also have "\<dots> = (\<Sum>x \<in> s - t. f x) + (\<Sum>x \<in> s \<inter> t. f x)"
    by (simp add: setsum_Un)
  also have "(\<Sum>x \<in> s - t. f x) \<le> 0"
    by (auto intro!: setsum_nonpos f)
  also have "0 \<le> (\<Sum>x \<in> t - s. g x)"
    by (auto intro!: setsum_nonneg g)
  also have "(\<Sum>x \<in> s \<inter> t. f x) \<le> (\<Sum>x \<in> s \<inter> t. g x)"
    by (auto intro!: setsum_mono fg)
  also
  have [intro, simp]: "(t - s) \<inter> (s \<inter> t) = {}" by auto
  hence "setsum g (t - s) + setsum g (s \<inter> t) = setsum g ((t - s) \<union> (s \<inter> t))"
    by (simp add: setsum_Un)
  also have "\<dots> = setsum g t"
    by (auto intro!: setsum.cong)
  finally show ?thesis by simp
qed

lemma pdevs_val_perm_ex:
  assumes "xs <~~> ys"
  assumes mem: "e \<in> UNIV \<rightarrow> I"
  shows "\<exists>e'. e' \<in> UNIV \<rightarrow> I \<and> pdevs_val e (pdevs_of_list xs) = pdevs_val e' (pdevs_of_list ys)"
  using assms
proof (induct arbitrary: e)
  case Nil
  thus ?case
    by auto
next
  case (Cons xs ys z)
  hence "(e \<circ> op + (Suc 0)) \<in> UNIV \<rightarrow> I" by auto
  from Cons(2)[OF this] obtain e' where "e' \<in> UNIV \<rightarrow> I"
      "pdevs_val (e \<circ> op + (Suc 0)) (pdevs_of_list xs) = pdevs_val e' (pdevs_of_list ys)"
    by metis
  thus ?case using Cons
    by (auto intro!: exI[where x="\<lambda>x. if x = 0 then e 0 else e' (x - 1)"] simp: o_def Pi_iff)
next
  case (trans xs ys zs)
  thus ?case by metis
next
  case (swap y x l)
  thus ?case
    by (auto intro!: exI[where x="\<lambda>i. if i = 0 then e 1 else if i = 1 then e 0 else e i"]
      simp: o_def Pi_iff)
qed

lemma pdevs_val_perm:
  assumes "xs <~~> ys"
  assumes mem: "e \<in> UNIV \<rightarrow> I"
  obtains e' where "e' \<in> UNIV \<rightarrow> I"
    "pdevs_val e (pdevs_of_list xs) = pdevs_val e' (pdevs_of_list ys)"
  using assms
  by (metis pdevs_val_perm_ex)

lemma set_distinct_permI: "set xs = set ys \<Longrightarrow> distinct xs \<Longrightarrow> distinct ys \<Longrightarrow> xs <~~> ys"
  by (metis eq_set_perm_remdups remdups_id_iff_distinct)

lemmas pdevs_val_permute = pdevs_val_perm[OF set_distinct_permI]

lemma partition_permI:
  "filter p xs @ filter (Not o p) xs <~~> xs"
proof (induct xs)
  case (Cons x xs)
  have swap_app_Cons: "filter p xs @ x # [a\<leftarrow>xs . \<not> p a] <~~> x # filter p xs @ [a\<leftarrow>xs . \<not> p a]"
    by (metis perm_sym perm_append_Cons)
  also have "\<dots> <~~> x#xs"
    using Cons by auto
  finally (trans)
  show ?case using Cons
    by simp
qed simp

lemma pdevs_val_eqI:
  assumes "\<And>i. i \<in> pdevs_domain y \<Longrightarrow> i \<in> pdevs_domain x \<Longrightarrow>
      e i *\<^sub>R pdevs_apply x i = f i *\<^sub>R pdevs_apply y i"
  assumes "\<And>i. i \<in> pdevs_domain y \<Longrightarrow> i \<notin> pdevs_domain x \<Longrightarrow> f i *\<^sub>R pdevs_apply y i = 0"
  assumes "\<And>i. i \<in> pdevs_domain x \<Longrightarrow> i \<notin> pdevs_domain y \<Longrightarrow> e i *\<^sub>R pdevs_apply x i = 0"
  shows "pdevs_val e x = pdevs_val f y"
  using assms
  by (force simp: pdevs_val_pdevs_domain
    intro!:
      setsum.reindex_bij_witness_not_neutral[where
        i=id and j = id and
        S'="pdevs_domain x - pdevs_domain y" and
        T'="pdevs_domain y - pdevs_domain x"])

definition
  filter_pdevs_raw::"(nat \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 'a::real_vector) \<Rightarrow> (nat \<Rightarrow> 'a)"
  where "filter_pdevs_raw I X = (\<lambda>i. if I i (X i) then X i else 0)"

lemma filter_pdevs_raw_nonzeros: "{i. filter_pdevs_raw s f i \<noteq> 0} = {i. f i \<noteq> 0} \<inter> {x. s x (f x)}"
  by (auto simp: filter_pdevs_raw_def)

lift_definition filter_pdevs::"(nat \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a::real_vector pdevs \<Rightarrow> 'a pdevs"
  is filter_pdevs_raw
  by (simp add: filter_pdevs_raw_nonzeros)

lemma pdevs_apply_filter_pdevs[simp]:
  "pdevs_apply (filter_pdevs I x) i = (if I i (pdevs_apply x i) then pdevs_apply x i else 0)"
  by transfer (auto simp: filter_pdevs_raw_def)

lemma degree_filter_pdevs_le: "degree (filter_pdevs I x) \<le> degree x"
  by (rule degree_leI) (simp split: split_if_asm)

lemma pdevs_val_filter_pdevs:
  "pdevs_val e (filter_pdevs I x) =
    (\<Sum>i \<in> {..<degree x} \<inter> {i. I i (pdevs_apply x i)}. e i *\<^sub>R pdevs_apply x i)"
  by (auto simp: pdevs_val_setsum if_distrib setsum.inter_restrict degree_filter_pdevs_le degree_gt
    intro!: setsum.mono_neutral_cong_left split: split_if_asm)

lemma pdevs_val_filter_pdevs_dom:
  "pdevs_val e (filter_pdevs I x) =
    (\<Sum>i \<in> pdevs_domain x \<inter> {i. I i (pdevs_apply x i)}. e i *\<^sub>R pdevs_apply x i)"
  by (auto
    simp: pdevs_val_pdevs_domain if_distrib setsum.inter_restrict degree_filter_pdevs_le degree_gt
    intro!: setsum.mono_neutral_cong_left split: split_if_asm)

lemma pdevs_val_filter_pdevs_eval:
  "pdevs_val e (filter_pdevs p x) = pdevs_val (\<lambda>i. if p i (pdevs_apply x i) then e i else 0) x"
  by (auto split: split_if_asm intro!: pdevs_val_eqI)

definition "dense_list_of_pdevs x = map (\<lambda>i. pdevs_apply x i) [0..<degree x]"

definition "list_of_pdevs x =
  map (\<lambda>i. (i, pdevs_apply x i)) (rev (sorted_list_of_set (pdevs_domain x)))"

lemma list_of_pdevszero_pdevs[simp]: "list_of_pdevs zero_pdevs = []"
  by (auto simp: list_of_pdevs_def)

lemma listsum_list_of_pdevs: "listsum (map snd (list_of_pdevs x)) = listsum (dense_list_of_pdevs x)"
  by (auto intro!: setsum.mono_neutral_cong_left
    simp add: degree_gt listsum_distinct_conv_setsum_set dense_list_of_pdevs_def list_of_pdevs_def)

lemma listsum_filter_dense_list_of_pdevs[symmetric]:
  "listsum (map snd (filter (p o snd) (list_of_pdevs x))) =
    listsum (filter p (dense_list_of_pdevs x))"
  by (auto intro!: setsum.mono_neutral_cong_left
    simp add: degree_gt listsum_distinct_conv_setsum_set dense_list_of_pdevs_def list_of_pdevs_def
      o_def filter_map)

lemma pdevs_of_list_dense_list_of_pdevs: "pdevs_of_list (dense_list_of_pdevs x) = x"
  by (auto simp: pdevs_apply_pdevs_of_list dense_list_of_pdevs_def pdevs_eqI)

lemma pdevs_val_listsum: "pdevs_val (\<lambda>_. c) X = c *\<^sub>R listsum (map snd (list_of_pdevs X))"
  by (auto simp: pdevs_val_setsum listsum_list_of_pdevs pdevs_val_const_pdevs_of_list[symmetric]
    pdevs_of_list_dense_list_of_pdevs)

lemma list_of_pdevs_all_nonzero: "list_all (\<lambda>x. x \<noteq> 0) (map snd (list_of_pdevs xs))"
  by (auto simp: list_of_pdevs_def list_all_iff)

lemma list_of_pdevs_nonzero: "x \<in> set (map snd (list_of_pdevs xs)) \<Longrightarrow> x \<noteq> 0"
  by (auto simp: list_of_pdevs_def)

lemma pdevs_of_list_scaleR_0[simp]:
  fixes xs::"'a::real_vector list"
  shows "pdevs_of_list (map (op *\<^sub>R 0) xs) = zero_pdevs"
  by (auto simp: pdevs_apply_pdevs_of_list intro!: pdevs_eqI)

lemma degree_pdevs_of_list_scaleR:
  "degree (pdevs_of_list (map (op *\<^sub>R c) xs)) = (if c \<noteq> 0 then degree (pdevs_of_list xs) else 0)"
  by (auto simp: pdevs_apply_pdevs_of_list intro!: degree_cong)

lemma list_of_pdevs_eq:
  "rev (list_of_pdevs X) = (filter (op \<noteq> 0 o snd) (map (\<lambda>i. (i, pdevs_apply X i)) [0..<degree X]))"
  (is "_ = filter ?P (map ?f ?xs)")
  using map_filter[of ?f ?P ?xs]
  by (auto simp: list_of_pdevs_def o_def sorted_list_of_pdevs_domain_eq rev_map)

lemma listsum_take_pdevs_val_eq:
  "listsum (take d xs) = pdevs_val (\<lambda>i. if i < d then 1 else 0) (pdevs_of_list xs)"
proof -
  have "listsum (take d xs) = 1 *\<^sub>R listsum (take d xs)" by simp
  also note pdevs_val_const_pdevs_of_list[symmetric]
  also have "pdevs_val (\<lambda>_. 1) (pdevs_of_list (take d xs)) =
      pdevs_val (\<lambda>i. if i < d then 1 else 0) (pdevs_of_list xs)"
    by (auto simp: pdevs_apply_pdevs_of_list split: split_if_asm intro!: pdevs_val_eqI)
  finally show ?thesis .
qed

lemma zero_in_range_pdevs_apply[intro, simp]:
  fixes X::"'a::real_vector pdevs" shows "0 \<in> range (pdevs_apply X)"
  by (metis degree_gt less_irrefl rangeI)

lemma dense_list_in_range: "x \<in> set (dense_list_of_pdevs X) \<Longrightarrow> x \<in> range (pdevs_apply X)"
  by (auto simp: dense_list_of_pdevs_def)

lemma not_in_dense_list_zeroD:
  assumes "pdevs_apply X i \<notin> set (dense_list_of_pdevs X)"
  shows "pdevs_apply X i = 0"
proof (rule ccontr)
  assume "pdevs_apply X i \<noteq> 0"
  hence "i < degree X"
    by (rule degree_gt)
  thus False using assms
    by (auto simp: dense_list_of_pdevs_def)
qed

lemma list_all_list_of_pdevsI:
  assumes "\<And>i. i \<in> pdevs_domain X \<Longrightarrow> P (pdevs_apply X i)"
  shows "list_all (\<lambda>x. P x) (map snd (list_of_pdevs X))"
  using assms by (auto simp: list_all_iff list_of_pdevs_def)

lemma pdevs_of_list_map_scaleR:
  "pdevs_of_list (map (scaleR r) xs) = scaleR_pdevs r (pdevs_of_list xs)"
  by (auto intro!: pdevs_eqI simp: pdevs_apply_pdevs_of_list)

lemma
  map_permI:
  assumes "xs <~~> ys"
  shows "map f xs <~~> map f ys"
  using assms by induct auto

lemma rev_perm: "rev xs <~~> ys \<longleftrightarrow> xs <~~> ys"
  by (metis perm.trans perm_rev rev_rev_ident)

lemma list_of_pdevs_perm_filter_nonzero:
  "map snd (list_of_pdevs X) <~~> (filter (op \<noteq> 0) (dense_list_of_pdevs X))"
proof -
  have zip_map:
    "zip [0..<degree X] (dense_list_of_pdevs X) = map (\<lambda>i. (i, pdevs_apply X i)) [0..<degree X]"
    by (auto simp: dense_list_of_pdevs_def intro!: nth_equalityI)
  have "rev (list_of_pdevs X) <~~>
      filter (op \<noteq> 0 o snd) (zip [0..<degree X] (dense_list_of_pdevs X))"
    by (auto simp: list_of_pdevs_eq o_def zip_map)
  from map_permI[OF this, of snd]
  have "map snd (list_of_pdevs X) <~~>
      map snd (filter (op \<noteq> 0 \<circ> snd) (zip [0..<degree X] (dense_list_of_pdevs X)))"
    by (simp add: rev_map[symmetric] rev_perm)
  also have "map snd (filter (op \<noteq> 0 \<circ> snd) (zip [0..<degree X] (dense_list_of_pdevs X))) =
      filter (op \<noteq> 0) (dense_list_of_pdevs X)"
    using map_filter[of snd "op \<noteq> 0" "(zip [0..<degree X] (dense_list_of_pdevs X))"]
    by (simp add: o_def dense_list_of_pdevs_def)
   finally
   show ?thesis .
qed

lemma pdevs_val_filter:
  assumes mem: "e \<in> UNIV \<rightarrow> I"
  assumes "0 \<in> I"
  obtains e' where
    "pdevs_val e (pdevs_of_list (filter p xs)) = pdevs_val e' (pdevs_of_list xs)"
    "e' \<in> UNIV \<rightarrow> I"
  unfolding pdevs_val_filter_pdevs_eval
proof -
  have "(\<lambda>_::nat. 0) \<in> UNIV \<rightarrow> I" using assms by simp
  have "pdevs_val e (pdevs_of_list (filter p xs)) =
      pdevs_val e (pdevs_of_list (filter p xs)) +
      pdevs_val (\<lambda>_. 0) (pdevs_of_list (filter (Not o p) xs))"
    by (simp add: pdevs_val_setsum)
  also
  from pdevs_val_pdevs_of_list_append[OF `e \<in> _` `(\<lambda>_. 0) \<in> _`]
  obtain e' where "e' \<in> UNIV \<rightarrow> I"
      "\<dots> = pdevs_val e' (pdevs_of_list (filter p xs @ filter (Not o p) xs))"
    by metis
  note this(2)
  also
  from pdevs_val_perm[OF partition_permI `e' \<in> _`]
  obtain e'' where "\<dots> = pdevs_val e'' (pdevs_of_list xs)" "e'' \<in> UNIV \<rightarrow> I" by metis
  note this(1)
  finally show ?thesis using `e'' \<in> _` ..
qed

lemma
  pdevs_val_of_list_of_pdevs:
  assumes "e \<in> UNIV \<rightarrow> I"
  assumes "0 \<in> I"
  obtains e' where
    "pdevs_val e (pdevs_of_list (map snd (list_of_pdevs X))) = pdevs_val e' X"
    "e' \<in> UNIV \<rightarrow> I"
proof -
  obtain e' where "e' \<in> UNIV \<rightarrow> I"
    and "pdevs_val e (pdevs_of_list (map snd (list_of_pdevs X))) =
      pdevs_val e' (pdevs_of_list (filter (op \<noteq> 0) (dense_list_of_pdevs X)))"
    by (rule pdevs_val_perm[OF list_of_pdevs_perm_filter_nonzero assms(1)])
  note this(2)
  also from pdevs_val_filter[OF `e' \<in> _` `0 \<in> I`, of "op \<noteq> 0" "dense_list_of_pdevs X"]
  obtain e'' where "e'' \<in> UNIV \<rightarrow> I"
    and "\<dots> = pdevs_val e'' (pdevs_of_list (dense_list_of_pdevs X))"
    by metis
  note this(2)
  also have "\<dots> = pdevs_val e'' X" by (simp add: pdevs_of_list_dense_list_of_pdevs)
  finally show ?thesis using `e'' \<in> UNIV \<rightarrow> I` ..
qed

lemma
  pdevs_val_of_list_of_pdevs2:
  assumes "e \<in> UNIV \<rightarrow> I"
  obtains e' where
    "pdevs_val e X = pdevs_val e' (pdevs_of_list (map snd (list_of_pdevs X)))"
    "e' \<in> UNIV \<rightarrow> I"
proof -
  from list_of_pdevs_perm_filter_nonzero[of X]
  have perm: "(filter (op \<noteq> 0) (dense_list_of_pdevs X)) <~~> map snd (list_of_pdevs X)"
    by (simp add: perm_sym)
  have "pdevs_val e X = pdevs_val e (pdevs_of_list (dense_list_of_pdevs X))"
    by (simp add: pdevs_of_list_dense_list_of_pdevs)
  also from pdevs_val_partition[OF `e \<in> _`, of "dense_list_of_pdevs X" "op \<noteq> 0"]
  obtain f g where "f \<in> UNIV \<rightarrow> I" "g \<in> UNIV \<rightarrow> I"
    "\<dots> = pdevs_val f (pdevs_of_list (filter (op \<noteq> 0) (dense_list_of_pdevs X))) +
      pdevs_val g (pdevs_of_list (filter (Not \<circ> op \<noteq> 0) (dense_list_of_pdevs X)))"
    (is "_ = ?f + ?g")
    by metis
  note this(3)
  also
  have "pdevs_of_list [x\<leftarrow>dense_list_of_pdevs X . x = 0] = zero_pdevs"
    by (auto intro!: pdevs_eqI simp: pdevs_apply_pdevs_of_list dest!: nth_mem)
  hence "?g = 0" by (auto simp: o_def )
  also
  obtain e' where "e' \<in> UNIV \<rightarrow> I"
    and "?f = pdevs_val e' (pdevs_of_list (map snd (list_of_pdevs X)))"
    by (rule pdevs_val_perm[OF perm `f \<in> _`])
  note this(2)
  finally show ?thesis using `e' \<in> UNIV \<rightarrow> I` by (auto intro!: that)
qed

lemma dense_list_of_pdevs_scaleR:
  "r \<noteq> 0 \<Longrightarrow> map (op *\<^sub>R r) (dense_list_of_pdevs x) = dense_list_of_pdevs (scaleR_pdevs r x)"
  by (auto simp: dense_list_of_pdevs_def)

lemma degree_pdevs_of_list_eq:
  "(\<And>x. x \<in> set xs \<Longrightarrow> x \<noteq> 0) \<Longrightarrow> degree (pdevs_of_list xs) = length xs"
  by (cases xs) (auto simp add: pdevs_apply_pdevs_of_list nth_Cons
    intro!: degree_eqI
    split: nat.split)

lemma dense_list_of_pdevs_pdevs_of_list:
  "(\<And>x. x \<in> set xs \<Longrightarrow> x \<noteq> 0) \<Longrightarrow> dense_list_of_pdevs (pdevs_of_list xs) = xs"
  by (auto simp: dense_list_of_pdevs_def degree_pdevs_of_list_eq pdevs_apply_pdevs_of_list
    intro!: nth_equalityI)

lemma pdevs_of_list_setsum:
  assumes "distinct xs"
  assumes "e \<in> UNIV \<rightarrow> I"
  obtains f where "f \<in> UNIV \<rightarrow> I" "pdevs_val e (pdevs_of_list xs) = (\<Sum>P\<in>set xs. f P *\<^sub>R P)"
proof -
  def f \<equiv> "\<lambda>X. e (the (map_of (zip xs [0..<length xs]) X))"
  from assms have "f \<in> UNIV \<rightarrow> I"
    by (auto simp: f_def)
  moreover
  have "pdevs_val e (pdevs_of_list xs) = (\<Sum>P\<in>set xs. f P *\<^sub>R P)"
    by (auto simp add: pdevs_val_zip f_def assms listsum_distinct_conv_setsum_set[symmetric]
      in_set_zip map_of_zip_upto2_length_eq_nth
      intro!: listsum_nth_eqI)
  ultimately show ?thesis ..
qed

lemma pdevs_domain_eq_pdevs_of_list:
  assumes nz: "\<And>x. x \<in> set (xs) \<Longrightarrow> x \<noteq> 0"
  shows "pdevs_domain (pdevs_of_list xs) = {0..<length xs}"
  using nz
  by (auto simp: pdevs_apply_pdevs_of_list split: split_if_asm)

lemma length_list_of_pdevs_pdevs_of_list:
  assumes nz: "\<And>x. x \<in> set xs \<Longrightarrow> x \<noteq> 0"
  shows "length (list_of_pdevs (pdevs_of_list xs)) = length xs"
  using nz by (auto simp: list_of_pdevs_def pdevs_domain_eq_pdevs_of_list)

lemma nth_list_of_pdevs_pdevs_of_list:
  assumes nz: "\<And>x. x \<in> set xs \<Longrightarrow> x \<noteq> 0"
  assumes l: "n < length xs"
  shows "list_of_pdevs (pdevs_of_list xs) ! n  = ((length xs - Suc n), xs ! (length xs - Suc n))"
  using nz l
  by (auto simp: list_of_pdevs_def pdevs_domain_eq_pdevs_of_list rev_nth pdevs_apply_pdevs_of_list)

lemma list_of_pdevs_pdevs_of_list_eq:
  "(\<And>x. x \<in> set xs \<Longrightarrow> x \<noteq> 0) \<Longrightarrow>
    list_of_pdevs (pdevs_of_list xs) = zip (rev [0..<length xs]) (rev xs)"
  by (auto simp: nth_list_of_pdevs_pdevs_of_list length_list_of_pdevs_pdevs_of_list rev_nth
    intro!: nth_equalityI)

lemma listsum_filter_list_of_pdevs_of_list:
  fixes xs::"'a::comm_monoid_add list"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x \<noteq> 0"
  shows "listsum (filter p (map snd (list_of_pdevs (pdevs_of_list xs)))) = listsum (filter p xs)"
  using assms
  by (auto simp: list_of_pdevs_pdevs_of_list_eq rev_filter[symmetric])

lemma
  listsum_partition:
  fixes xs::"'a::comm_monoid_add list"
  shows "listsum (filter p xs) + listsum (filter (Not o p) xs) = listsum xs"
  by (induct xs) (auto simp: ac_simps)

end
