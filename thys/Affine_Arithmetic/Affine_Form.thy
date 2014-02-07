header {* Affine Form *}
theory Affine_Form
imports
  "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
begin

text {*\label{sec:affineform}*}

subsection {* Partial Deviations *}

typedef 'a pdevs = "{x::nat \<Rightarrow> 'a::zero. finite {i. x i \<noteq> 0}}"
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

lemma zipped_equals_mapped_Elem:
  assumes "ys = map (aform_val e) YS"
  assumes e: "\<And>i. e i \<in> {-1 .. 1}"
  assumes [simp]: "length xs = length XS"
  assumes [simp]: "length ys = length XS"
  assumes "set (zip xs XS) = set (zip ys YS)"
  shows "xs = map (aform_val e) XS"
proof -
  from assms have ys: "\<And>i. i < length ys \<Longrightarrow> ys ! i = aform_val e (YS ! i)"
    by auto
  from assms have set_eq: "{(xs ! i, XS ! i) |i. i < length xs \<and> i < length XS} \<subseteq>
    {(ys ! i, YS ! i) |i. i < length ys \<and> i < length YS}"
    using assms(2)
    by (auto simp: set_zip)
  hence "\<forall>i<length XS. \<exists>j<length XS. xs ! i = ys ! j \<and> XS ! i = YS ! j"
    by auto
  then obtain j where j: "\<And>i. i < length XS \<Longrightarrow> xs ! i = ys ! (j i)"
    "\<And>i. i < length XS \<Longrightarrow> XS ! i = YS ! (j i)"
    "\<And>i. i < length XS \<Longrightarrow> j i < length XS"
    by metis
  show ?thesis
    using assms
    by (auto simp: Joints_def j ys intro!: exI[where x=e] nth_equalityI)
qed

lemma Joints_set_zip:
  assumes "ys \<in> Joints YS"
  assumes [simp]: "length xs = length XS"
  assumes [simp]: "length YS = length XS"
  assumes sets_eq: "set (zip xs XS) = set (zip ys YS)"
  shows "xs \<in> Joints XS"
proof -
  from assms have ls[simp]: "length ys = length XS"
    by (auto simp: Joints_def valuate_def)
  from Joints_mapE assms obtain e where
    ys: "ys = map (\<lambda>x. aform_val e x) YS"
    and e: "\<And>i. e i \<in> {-1 .. 1}"
    by blast
  show "xs \<in> Joints XS"
    using e zipped_equals_mapped_Elem[OF ys e assms(2) ls sets_eq]
    by (auto simp: Joints_def valuate_def intro!: exI[where x=e])
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
  by (auto intro!: degree_gt setsum_mono_zero_cong_left simp: pdevs_val_pdevs_domain)

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


subsection {* Total Deviation *}

definition tdev::"'a::ordered_euclidean_space pdevs \<Rightarrow> 'a" where
  "tdev x = (\<Sum>i<degree x. \<bar>pdevs_apply x i\<bar>)"

lemma abs_pdevs_val_le_tdev: "e \<in> UNIV \<rightarrow> {-1 .. 1} \<Longrightarrow> \<bar>pdevs_val e x\<bar> \<le> tdev x"
  by (force simp: pdevs_val_setsum tdev_def abs_scaleR Pi_iff
    intro!: order_trans[OF setsum_abs] setsum_mono scaleR_left_le_one_le
    intro: abs_leI)


subsection {* Binary Pointwise Operations *}

definition binop_pdevs_raw::
    "('a::real_vector \<Rightarrow> 'b::real_vector \<Rightarrow> 'c::real_vector) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'c"
  where "binop_pdevs_raw f x y i = (if x i = 0 \<and> y i = 0 then 0 else f (x i) (y i))"

lemma nonzeros_binop_pdevs_subset: "{i. binop_pdevs_raw f x y i \<noteq> 0} \<subseteq> {i. x i \<noteq> 0} \<union> {i. y i \<noteq> 0}"
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
    by (rule setsum_mono_zero_cong_left) auto
  also have "?sum (degree Y) Y = ?sum ?m Y"
    by (rule setsum_mono_zero_cong_left) auto
  also have "?sum ?m X + ?sum ?m Y = (\<Sum>i < ?m. e i *\<^sub>R (pdevs_apply X i + pdevs_apply Y i))"
    by (simp add: scaleR_right_distrib setsum_addf)
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
  by (auto simp add: inner_setsum_left pdevs_val_pdevs_domain intro!: setsum_mono_zero_cong_left)

definition inner_aform::"'a::euclidean_space aform \<Rightarrow> 'a \<Rightarrow> real aform"
  where "inner_aform X b = (fst X \<bullet> b, pdevs_inner (snd X) b)"


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
  shows "(\<Sum>i <degree (msum_pdevs n f g). e i (if i < n then pdevs_apply f i else pdevs_apply g (i - n))) =
    (\<Sum>i <degree f. e i (pdevs_apply f i)) + (\<Sum>i <degree g. e (i + n) (pdevs_apply g i))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sum>i\<in>{..<degree (msum_pdevs n f g)} \<inter> {i. i < n}. e i (pdevs_apply f i)) +
    (\<Sum>i\<in>{..<degree (msum_pdevs n f g)} \<inter> - {i. i < n}. e i (pdevs_apply g (i - n)))"
    (is "_ = ?sum_f + ?sum_g")
     by (simp add: setsum_cases if_distrib)
  also have "?sum_f = (\<Sum>i = 0..<degree f. e i (pdevs_apply f i))"
    using assms degree_msum_pdevs_ge1[of f n g]
    by (intro setsum_mono_zero_cong_right) auto
  also have "?sum_g = (\<Sum>i\<in>{0 + n..<degree (msum_pdevs n f g) - n + n}. e i (pdevs_apply g (i - n)))"
    by (rule setsum_cong) auto
  also have "\<dots> = (\<Sum>i = 0..<degree (msum_pdevs n f g) - n. e (i + n) (pdevs_apply g (i + n - n)))"
    by (rule setsum_shift_bounds_nat_ivl)
  also have "\<dots> = (\<Sum>i = 0..<degree g. e (i + n) (pdevs_apply g i))"
    using assms degree_msum_pdevs_ge2[of f n]
    by (intro setsum_mono_zero_cong_right) (auto intro!: setsum_mono_zero_cong_right)
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

text {* TODO: msum-aform could also round the Center... *}

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

lemma Affine_msum_aform:
    "Affine (msum_aform (degree_aform X) X Y) = {x + y |x y. x \<in> Affine X \<and> y \<in> Affine Y}"
  unfolding Affine_def valuate_def
proof safe
  case goal1
  thus ?case
    by (intro exI[where x = "aform_val e X"] exI[where x = "aform_val ((\<lambda>i. e (i + degree_aform X))) Y"])
      (auto simp add: aform_val_def pdevs_val_msum_pdevs)
next
  case goal2
  thus ?case
    by (intro image_eqI[where x="\<lambda>i. if i < degree_aform X then e i else ea (i - degree_aform X)"])
      (force simp: aform_val_def pdevs_val_msum_pdevs intro!: pdevs_val_degree_cong)+
qed

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
      by (auto intro!: exI[where x="x(a:=s)"] setsum_cong)
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
    by (rule compact_sums) (auto intro!: compact_setsum continuous_on_intros)
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
        (\<Sum>i \<in> {0..<degree_aform X} - {i}. e i *\<^sub>R pdevs_apply (snd X) i) + e i *\<^sub>R pdevs_apply (snd X) i"
      by (subst rewr, subst setsum_Un_disjoint) auto
    finally have "x = fst X + \<dots>" .
    hence "x = aform_val (e(i:=2 * e i - 1)) (snd (split_aform X i))"
        "x = aform_val (e(i:=2 * e i + 1)) (fst (split_aform X i))"
      by (auto simp: aform_val_def split_aform_def Let_def pdevs_val_setsum atLeast0LessThan
        Diff_eq degree_pdev_upd if_distrib setsum_cases field_simps scaleR_left_distrib[symmetric])
    moreover
    have "2 * e i - 1 \<in> {-1 .. 1} \<or> 2 * e i + 1 \<in> {-1 .. 1}"
      using assms by (auto simp: not_le Pi_iff dest!: spec[where x=i])
    ultimately have ?thesis by blast
  } ultimately show ?thesis by blast
qed

end
