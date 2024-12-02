(*
  Title:  Maximal Consistent Sets
  Author: Asta Halkjær From

  Based on:
  - First-Order Logic (1968) by Smullyan, R.
  - Model Theory (1990) by Chang, C. C. and Keisler, H. J.
*)

chapter \<open>Maximal Consistent Sets\<close>

theory Maximal_Consistent_Sets imports "HOL-Cardinals.Cardinal_Order_Relation" begin

section \<open>Utility\<close>

lemma Set_Diff_Un: \<open>X - (Y \<union> Z) = X - Y - Z\<close>
  by blast

lemma infinite_Diff_fin_Un: \<open>infinite (X - Y) \<Longrightarrow> finite Z \<Longrightarrow> infinite (X - (Z \<union> Y))\<close>
  by (simp add: Set_Diff_Un Un_commute)

lemma infinite_Diff_subset: \<open>infinite (X - A) \<Longrightarrow> B \<subseteq> A \<Longrightarrow> infinite (X - B)\<close>
  by (meson Diff_cancel Diff_eq_empty_iff Diff_mono infinite_super)

lemma finite_bound:
  fixes X :: \<open>('a :: size) set\<close>
  assumes \<open>finite X\<close> \<open>X \<noteq> {}\<close>
  shows \<open>\<exists>x \<in> X. \<forall>y \<in> X. size y \<le> size x\<close>
  using assms by (induct X rule: finite_induct) force+

lemma infinite_UNIV_size:
  fixes f :: \<open>('a :: size) \<Rightarrow> 'a\<close>
  assumes \<open>\<And>x. size x < size (f x)\<close>
  shows \<open>infinite (UNIV :: 'a set)\<close>
proof
  assume \<open>finite (UNIV :: 'a set)\<close>
  then obtain x :: 'a where \<open>\<forall>y :: 'a. size y \<le> size x\<close>
    using finite_bound by fastforce
  moreover have \<open>size x < size (f x)\<close>
    using assms .
  ultimately show False
    using leD by blast
qed

context wo_rel begin

lemma underS_bound: \<open>a \<in> underS c \<Longrightarrow> b \<in> underS c \<Longrightarrow> a \<in> under b \<or> b \<in> under a\<close>
  by (meson BNF_Least_Fixpoint.underS_Field REFL Refl_under_in in_mono under_ofilter ofilter_linord)

lemma finite_underS_bound:
  assumes \<open>finite X\<close> \<open>X \<subseteq> underS c\<close> \<open>X \<noteq> {}\<close>
  shows \<open>\<exists>a \<in> X. \<forall>b \<in> X. b \<in> under a\<close>
  using assms
proof (induct X rule: finite_induct)
  case (insert x F)
  then show ?case
  proof (cases \<open>F = {}\<close>)
    case True
    then show ?thesis
      using insert underS_bound by fast
  next
    case False
    then show ?thesis
      using insert underS_bound by (metis TRANS insert_absorb insert_iff insert_subset under_trans)
  qed
qed simp

lemma finite_bound_under:
  assumes \<open>finite p\<close> \<open>p \<subseteq> (\<Union>a \<in> Field r. f a)\<close>
  shows \<open>\<exists>b. p \<subseteq> (\<Union>a \<in> under b. f a)\<close>
  using assms
proof (induct rule: finite_induct)
  case (insert x p)
  then obtain b where \<open>p \<subseteq> (\<Union>a \<in> under b. f a)\<close>
    by fast
  moreover obtain b' where \<open>x \<in> f b'\<close> \<open>b' \<in> Field r\<close>
    using insert(4) by blast
  then have \<open>x \<in> (\<Union>a \<in> under b'. f a)\<close>
    using REFL Refl_under_in by fast
  ultimately have \<open>{x} \<union> p \<subseteq> (\<Union>a \<in> under b. f a) \<union> (\<Union>a \<in> under b'. f a)\<close>
    by fast
  then show ?case
    by (metis SUP_union Un_commute insert_is_Un sup.absorb_iff2 ofilter_linord under_ofilter)
qed simp

lemma underS_trans: \<open>a \<in> underS b \<Longrightarrow> b \<in> underS c \<Longrightarrow> a \<in> underS c\<close>
  by (meson ANTISYM TRANS underS_underS_trans)

end

lemma card_of_infinite_smaller_Union:
  assumes \<open>\<forall>x. |f x| <o |X|\<close> \<open>infinite X\<close>
  shows \<open>|\<Union>x \<in> X. f x| \<le>o |X|\<close>
  using assms by (metis (full_types) Field_card_of card_of_UNION_ordLeq_infinite
      card_of_well_order_on ordLeq_iff_ordLess_or_ordIso ordLess_or_ordLeq)

lemma card_of_params_marker_lists:
  assumes \<open>infinite (UNIV :: 'i set)\<close> \<open>|UNIV :: 'm set| \<le>o |UNIV :: nat set|\<close>
  shows \<open>|UNIV :: ('i + 'm \<times> nat) list set| \<le>o |UNIV :: 'i set|\<close>
proof -
  have \<open>(UNIV :: 'm set) \<noteq> {}\<close>
    by simp
  then have \<open>|UNIV :: 'm set| *c |UNIV :: nat set| \<le>o |UNIV :: nat set|\<close>
    using assms(2) by (simp add: cinfinite_def cprod_cinfinite_bound ordLess_imp_ordLeq)
  then have \<open>|UNIV :: ('m \<times> nat) set| \<le>o |UNIV :: nat set|\<close>
    unfolding cprod_def by simp
  moreover have \<open>|UNIV :: nat set| \<le>o |UNIV :: 'i set|\<close>
    using assms infinite_iff_card_of_nat by blast
  ultimately have \<open>|UNIV :: ('m \<times> nat) set| \<le>o |UNIV :: 'i set|\<close>
    using ordLeq_transitive by blast
  moreover have \<open>Cinfinite |UNIV :: 'i set|\<close>
    using assms by (simp add: cinfinite_def)
  ultimately have \<open>|UNIV :: 'i set| +c |UNIV :: ('m \<times> nat) set| =o |UNIV :: 'i set|\<close>
    using csum_absorb1 by blast
  then have \<open>|UNIV :: ('i + 'm \<times> nat) set| =o |UNIV :: 'i set|\<close>
    unfolding csum_def by simp
  then have \<open>|UNIV :: ('i + 'm \<times> nat) set| \<le>o |UNIV :: 'i set|\<close>
    using ordIso_iff_ordLeq by blast
  moreover have \<open>infinite (UNIV :: ('i + 'm \<times> nat) set)\<close>
    using assms by simp
  then have \<open>|UNIV :: ('i + 'm \<times> nat) list set| =o |UNIV :: ('i + 'm \<times> nat) set|\<close>
    by (metis card_of_lists_infinite lists_UNIV)
  ultimately have \<open>|UNIV :: ('i + 'm \<times> nat) list set| \<le>o |UNIV :: 'i set|\<close>
    using ordIso_ordLeq_trans by blast
  then show ?thesis
    using ordLeq_transitive by blast
qed

section \<open>Base Locales\<close>

locale MCS_Base =
  fixes consistent :: \<open>'a set \<Rightarrow> bool\<close>
  assumes consistent_hereditary: \<open>\<And>S S'. consistent S \<Longrightarrow> S' \<subseteq> S \<Longrightarrow> consistent S'\<close>
    and inconsistent_finite: \<open>\<And>S. \<not> consistent S \<Longrightarrow> \<exists>S' \<subseteq> S. finite S' \<and> \<not> consistent S'\<close>
begin

definition maximal :: \<open>'a set \<Rightarrow> bool\<close> where
  \<open>maximal S \<equiv> \<forall>p. consistent ({p} \<union> S) \<longrightarrow> p \<in> S\<close>

end

locale MCS_Witness = MCS_Base consistent
  for consistent :: \<open>'a set \<Rightarrow> bool\<close> +
  fixes witness :: \<open>'a \<Rightarrow> 'a set \<Rightarrow> 'a set\<close>
    and params :: \<open>'a \<Rightarrow> 'i set\<close>
  assumes finite_params: \<open>\<And>p. finite (params p)\<close>
    and finite_witness_params: \<open>\<And>p S. finite (\<Union>q \<in> witness p S. params q)\<close>
    and consistent_witness: \<open>\<And>p S. consistent ({p} \<union> S)
      \<Longrightarrow> infinite (UNIV - (\<Union>q \<in> S. params q))
      \<Longrightarrow> consistent ({p} \<union> S \<union> witness p S)\<close>
begin

definition witnessed :: \<open>'a set \<Rightarrow> bool\<close> where
  \<open>witnessed S \<equiv> \<forall>p \<in> S. \<exists>S'. witness p S' \<subseteq> S\<close>

abbreviation MCS :: \<open>'a set \<Rightarrow> bool\<close> where
  \<open>MCS S \<equiv> consistent S \<and> maximal S \<and> witnessed S\<close>

end

locale MCS_No_Witness = MCS_Base consistent for consistent :: \<open>'a set \<Rightarrow> bool\<close>

sublocale MCS_No_Witness \<subseteq> MCS_Witness consistent \<open>\<lambda>_ _. {}\<close> \<open>\<lambda>_. {}\<close>
proof qed simp_all

section \<open>Ordinal Locale\<close>

locale MCS_Lim_Ord = MCS_Witness consistent witness params
  for consistent :: \<open>'a set \<Rightarrow> bool\<close>
    and witness :: \<open>'a \<Rightarrow> 'a set \<Rightarrow> 'a set\<close>
    and params :: \<open>'a \<Rightarrow> 'i set\<close> +
  fixes r :: \<open>'a rel\<close>
  assumes Cinfinite_r: \<open>Cinfinite r\<close>
begin

lemma WELL: \<open>Well_order r\<close>
  using Cinfinite_r by simp

lemma wo_rel_r: \<open>wo_rel r\<close>
  by (simp add: WELL wo_rel.intro)

lemma isLimOrd_r: \<open>isLimOrd r\<close>
  using Cinfinite_r card_order_infinite_isLimOrd cinfinite_def by blast

lemma nonempty_Field_r: \<open>Field r \<noteq> {}\<close>
  using Cinfinite_r cinfinite_def infinite_imp_nonempty by blast

subsection \<open>Lindenbaum Extension\<close>

abbreviation paramss :: \<open>'a set \<Rightarrow> 'i set\<close> where
  \<open>paramss S \<equiv> \<Union>p \<in> S. params p\<close>

definition extendS :: \<open>'a \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> where
  \<open>extendS a prev \<equiv> if consistent ({a} \<union> prev) then {a} \<union> prev \<union> witness a prev else prev\<close>

definition extendL :: \<open>('a \<Rightarrow> 'a set) \<Rightarrow> 'a \<Rightarrow> 'a set\<close> where
  \<open>extendL rec a \<equiv> \<Union>b \<in> underS r a. rec b\<close>

definition extend :: \<open>'a set \<Rightarrow> 'a \<Rightarrow> 'a set\<close> where
  \<open>extend S a \<equiv> worecZSL r S extendS extendL a\<close>

lemma adm_woL_extendL: \<open>adm_woL r extendL\<close>
  unfolding extendL_def wo_rel.adm_woL_def[OF wo_rel_r] by blast

definition Extend :: \<open>'a set \<Rightarrow> 'a set\<close> where
  \<open>Extend S \<equiv> \<Union>a \<in> Field r. extend S a\<close>

lemma extend_subset: \<open>a \<in> Field r \<Longrightarrow> S \<subseteq> extend S a\<close>
proof (induct a rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case
    unfolding extend_def wo_rel.worecZSL_zero[OF wo_rel_r adm_woL_extendL]
    by simp
next
  case (2 i)
  moreover from this have \<open>i \<in> Field r\<close>
    by (meson FieldI1 wo_rel.succ_in wo_rel_r)
  ultimately show ?case
    unfolding extend_def extendS_def wo_rel.worecZSL_succ[OF wo_rel_r adm_woL_extendL 2(1)]
    by auto
next
  case (3 i)
  then show ?case
    unfolding extend_def extendL_def wo_rel.worecZSL_isLim[OF wo_rel_r adm_woL_extendL 3(1-2)]
    using wo_rel.zero_in_Field[OF wo_rel_r] wo_rel.zero_smallest[OF wo_rel_r]
    by (metis SUP_upper2 emptyE underS_I)
qed

lemma Extend_subset: \<open>S \<subseteq> Extend S\<close>
  unfolding Extend_def using extend_subset nonempty_Field_r by fast

lemma extend_underS: \<open>b \<in> underS r a \<Longrightarrow> extend S b \<subseteq> extend S a\<close>
proof (induct a rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case
    unfolding extend_def using wo_rel.underS_zero[OF wo_rel_r] by fast
next
  case (2 i)
  moreover from this have \<open>b = i \<or> b \<in> underS r i\<close>
    by (metis wo_rel.less_succ[OF wo_rel_r] underS_E underS_I)
  ultimately show ?case
    unfolding extend_def extendS_def wo_rel.worecZSL_succ[OF wo_rel_r adm_woL_extendL 2(1)] by auto
next
  case (3 i)
  then show ?case
    unfolding extend_def extendL_def wo_rel.worecZSL_isLim[OF wo_rel_r adm_woL_extendL 3(1-2)]
    by blast
qed

lemma extend_under: \<open>b \<in> under r a \<Longrightarrow> extend S b \<subseteq> extend S a\<close>
  using extend_underS wo_rel.supr_greater[OF wo_rel_r] wo_rel.supr_under[OF wo_rel_r]
  by (metis emptyE in_Above_under set_eq_subset underS_I under_empty)

subsection \<open>Consistency\<close>

lemma params_origin:
  assumes \<open>x \<in> paramss (extend S a)\<close>
  shows \<open>x \<in> paramss S \<or> (\<exists>b \<in> underS r a. x \<in> paramss ({b} \<union> witness b (extend S b)))\<close>
  using assms
proof (induct a rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case
    unfolding extend_def wo_rel.worecZSL_zero[OF wo_rel_r adm_woL_extendL]
    by blast
next
  case (2 i)
  then consider (here) \<open>x \<in> paramss ({i} \<union> witness i (extend S i))\<close> | (there) \<open>x \<in> paramss (extend S i)\<close>
    using wo_rel.worecZSL_succ[OF wo_rel_r adm_woL_extendL 2(1)] extendS_def extend_def
    by (auto split: if_splits)
  then show ?case
  proof cases
    case here
    moreover have \<open>i \<in> Field r\<close>
      by (meson WELL 2(1) well_order_on_domain wo_rel.succ_in_diff[OF wo_rel_r])
    ultimately show ?thesis
      using 2(1) by (metis Refl_under_in wo_rel.underS_succ[OF wo_rel_r] wo_rel.REFL[OF wo_rel_r])
  next
    case there
    then show ?thesis
      using 2 by (metis in_mono underS_subset_under wo_rel.underS_succ[OF wo_rel_r])
  next
  qed
next
  case (3 i)
  then obtain j where \<open>j \<in> underS r i\<close> \<open>x \<in> paramss (extend S j)\<close>
    unfolding extend_def extendL_def wo_rel.worecZSL_isLim[OF wo_rel_r adm_woL_extendL 3(1-2)]
    by blast
  then show ?case
    using 3 wo_rel.underS_trans[OF wo_rel_r, of _ j i] by meson
qed

lemma consistent_extend:
  assumes \<open>consistent S\<close> \<open>r \<le>o |UNIV - paramss S|\<close>
  shows \<open>consistent (extend S a)\<close>
  using assms(1)
proof (induct a rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case
    unfolding extend_def wo_rel.worecZSL_zero[OF wo_rel_r adm_woL_extendL]
    by blast
next
  case (2 i)
  then have \<open>i \<in> Field r\<close>
    by (meson WELL  well_order_on_domain wo_rel.succ_in_diff[OF wo_rel_r])
  then have *: \<open>|underS r i| <o r\<close>
    using card_of_underS by (simp add: Cinfinite_r)
  let ?paramss = \<open>\<lambda>k. paramss ({k} \<union> witness k (extend S k))\<close>
  let ?X = \<open>\<Union>k \<in> underS r i. ?paramss k\<close>
  have \<open>|?X| <o r\<close>
  proof (cases \<open>finite (underS r i)\<close>)
    case True
    then have \<open>finite ?X\<close>
      by (simp add: finite_params finite_witness_params)
    then show ?thesis
      using Cinfinite_r assms(2) unfolding cinfinite_def by (simp add: finite_ordLess_infinite)
  next
    case False
    moreover have \<open>\<forall>k. finite (?paramss k)\<close>
      by (simp add: finite_params finite_witness_params)
    then have \<open>\<forall>k. |?paramss k| <o |underS r i|\<close>
      using False by simp
    ultimately have \<open>|?X| \<le>o |underS r i|\<close>
      using card_of_infinite_smaller_Union by fast
    then show ?thesis
      using * ordLeq_ordLess_trans by blast
  qed
  then have \<open>|?X| <o |UNIV - paramss S|\<close>
    using assms(2) ordLess_ordLeq_trans by blast
  moreover have \<open>infinite (UNIV - paramss S)\<close>
    using assms(2) Cinfinite_r unfolding cinfinite_def by (metis Field_card_of ordLeq_finite_Field)
  ultimately have \<open>|UNIV - paramss S - ?X| =o |UNIV - paramss S|\<close>
    using card_of_Un_diff_infinite by blast
  moreover from this have \<open>infinite (UNIV - paramss S - ?X)\<close>
    using \<open>infinite (UNIV - paramss S)\<close> card_of_ordIso_finite by blast
  moreover have \<open>\<And>a. a \<in> paramss (extend S i) \<Longrightarrow> a \<in> paramss S \<or> a \<in> ?X\<close>
    using params_origin by simp
  then have \<open>paramss (extend S i) \<subseteq> paramss S \<union> ?X\<close>
    by fast
  ultimately have \<open>infinite (UNIV - paramss (extend S i))\<close>
    using infinite_Diff_subset by (metis (no_types, lifting) Set_Diff_Un)
  with 2 show ?case
    unfolding extend_def extendS_def wo_rel.worecZSL_succ[OF wo_rel_r adm_woL_extendL 2(1)]
    using consistent_witness by simp
  next
  case (3 i)
  show ?case
  proof (rule ccontr)
    assume \<open>\<not> consistent (extend S i)\<close>
    then obtain S' where S': \<open>finite S'\<close> \<open>S' \<subseteq> (\<Union>a \<in> underS r i. extend S a)\<close> \<open>\<not> consistent S'\<close>
      unfolding extend_def extendL_def wo_rel.worecZSL_isLim[OF wo_rel_r adm_woL_extendL 3(1-2)]
      using inconsistent_finite by auto
    then obtain as where as: \<open>S' \<subseteq> (\<Union>a \<in> as. extend S a)\<close> \<open>as \<subseteq> underS r i\<close> \<open>finite as\<close>
      by (metis finite_subset_Union finite_subset_image)
    moreover have \<open>as \<noteq> {}\<close>
      using S'(3) assms calculation(1) consistent_hereditary by auto
    ultimately obtain j where \<open>\<forall>a \<in> as. a \<in> under r j\<close> \<open>j \<in> underS r i\<close>
      using wo_rel.finite_underS_bound wo_rel_r as by (meson subset_iff)
    then have \<open>\<forall>a \<in> as. extend S a \<subseteq> extend S j\<close>
      using extend_under by fast
    then have \<open>S' \<subseteq> extend S j\<close>
      using S' as(1) by blast
    then show False
      using 3(3-) \<open>\<not> consistent S'\<close> consistent_hereditary \<open>j \<in> underS r i\<close>
      by (meson BNF_Least_Fixpoint.underS_Field)
  qed
qed

lemma consistent_Extend:
  assumes \<open>consistent S\<close> \<open>r \<le>o |UNIV - paramss S|\<close>
  shows \<open>consistent (Extend S)\<close>
  unfolding Extend_def
proof (rule ccontr)
  assume \<open>\<not> consistent (\<Union>a \<in> Field r. extend S a)\<close>
  then obtain S' where \<open>finite S'\<close> \<open>S' \<subseteq> (\<Union>a \<in> Field r. extend S a)\<close> \<open>\<not> consistent S'\<close>
    using inconsistent_finite by metis
  then obtain b where \<open>S' \<subseteq> (\<Union>a \<in> under r b. extend S a)\<close> \<open>b \<in> Field r\<close>
    using wo_rel.finite_bound_under[OF wo_rel_r] assms consistent_hereditary
    by (metis Sup_empty emptyE image_empty subsetI under_empty)
  then have \<open>S' \<subseteq> extend S b\<close>
    using extend_under by fast
  moreover have \<open>consistent (extend S b)\<close>
    using assms consistent_extend \<open>b \<in> Field r\<close> by blast
  ultimately show False
    using \<open>\<not> consistent S'\<close> consistent_hereditary by blast
qed

lemma Extend_bound: \<open>a \<in> Field r \<Longrightarrow> extend S a \<subseteq> Extend S\<close>
  unfolding Extend_def by blast

subsection \<open>Maximality\<close>

definition maximal' :: \<open>'a set \<Rightarrow> bool\<close> where
  \<open>maximal' S \<equiv> \<forall>p \<in> Field r. consistent ({p} \<union> S) \<longrightarrow> p \<in> S\<close>

lemma maximal'_Extend: \<open>maximal' (Extend S)\<close>
  unfolding maximal'_def
proof safe
  fix p
  assume *: \<open>p \<in> Field r\<close> \<open>consistent ({p} \<union> Extend S)\<close>
  then have \<open>{p} \<union> extend S p \<subseteq> {p} \<union> Extend S\<close>
    unfolding Extend_def by blast
  then have **: \<open>consistent ({p} \<union> extend S p)\<close>
    using * consistent_hereditary by blast
  moreover have succ: \<open>aboveS r p \<noteq> {}\<close>
    using * isLimOrd_r wo_rel.isLimOrd_aboveS[OF wo_rel_r] by blast
  then have \<open>succ r p \<in> Field r\<close>
    using wo_rel.succ_in_Field[OF wo_rel_r] by blast
  moreover have \<open>p \<in> extend S (succ r p)\<close>
    using ** unfolding extend_def extendS_def wo_rel.worecZSL_succ[OF wo_rel_r adm_woL_extendL succ]
    by simp
  ultimately show \<open>p \<in> Extend S\<close>
    using Extend_bound by fast
qed

subsection \<open>Witnessing\<close>

definition witnessed' :: \<open>'a set \<Rightarrow> bool\<close> where
  \<open>witnessed' S \<equiv> \<forall>p \<in> Field r. p \<in> S \<longrightarrow> (\<exists>S'. witness p S' \<subseteq> S)\<close>

lemma witnessed'_Extend:
  assumes \<open>consistent (Extend S)\<close>
  shows \<open>witnessed' (Extend S)\<close>
  unfolding witnessed'_def
proof safe
  fix p
  assume *: \<open>p \<in> Field r\<close> \<open>p \<in> Extend S\<close>
  then have \<open>extend S p \<subseteq> Extend S\<close>
    unfolding Extend_def by blast
  then have \<open>consistent ({p} \<union> extend S p)\<close>
    using assms(1) * consistent_hereditary by auto
  moreover have succ: \<open>aboveS r p \<noteq> {}\<close>
    using * isLimOrd_r wo_rel.isLimOrd_aboveS wo_rel_r by fast
  then have \<open>succ r p \<in> Field r\<close>
    using wo_rel_r by (simp add: wo_rel.succ_in_Field)
  ultimately have \<open>extend S (succ r p) = {p} \<union> extend S p \<union> witness p (extend S p)\<close>
    unfolding extend_def extendS_def wo_rel.worecZSL_succ[OF wo_rel_r adm_woL_extendL succ]
    by simp
  moreover have \<open>extend S (succ r p) \<subseteq> Extend S\<close>
    unfolding Extend_def using \<open>succ r p \<in> Field r\<close> by blast
  ultimately show \<open>\<exists>a. witness p a \<subseteq> Extend S\<close>
    by fast
qed

end

section \<open>Locales for Universe Well-Order\<close>

locale MCS_Witness_UNIV = MCS_Witness consistent witness params
  for consistent :: \<open>'a set \<Rightarrow> bool\<close>
    and witness :: \<open>'a \<Rightarrow> 'a set \<Rightarrow> 'a set\<close>
    and params :: \<open>'a \<Rightarrow> 'i set\<close> +
  assumes infinite_UNIV: \<open>infinite (UNIV :: 'a set)\<close>

sublocale MCS_Witness_UNIV \<subseteq> MCS_Lim_Ord consistent witness params \<open>|UNIV|\<close>
proof
  show \<open>Cinfinite |UNIV :: 'a set|\<close>
    unfolding cinfinite_def using infinite_UNIV by simp
qed

context MCS_Witness_UNIV begin

lemma maximal_maximal': \<open>maximal S \<longleftrightarrow> maximal' S\<close>
  unfolding maximal_def maximal'_def by simp

lemma maximal_Extend: \<open>maximal (Extend S)\<close>
  using maximal'_Extend maximal_maximal' by fast

lemma witnessed_witnessed': \<open>witnessed S \<longleftrightarrow> witnessed' S\<close>
  unfolding witnessed_def witnessed'_def by auto

lemma witnessed_Extend:
  assumes \<open>consistent (Extend S)\<close>
  shows \<open>witnessed (Extend S)\<close>
  using assms witnessed'_Extend witnessed_witnessed' by blast

theorem MCS_Extend:
  assumes \<open>consistent S\<close> \<open>|UNIV :: 'a set| \<le>o |UNIV - paramss S|\<close>
  shows \<open>MCS (Extend S)\<close>
  using assms consistent_Extend maximal_Extend witnessed_Extend by blast

end

locale MCS_No_Witness_UNIV = MCS_No_Witness consistent
  for consistent :: \<open>'a set \<Rightarrow> bool\<close> +
  assumes infinite_UNIV' [simp]: \<open>infinite (UNIV :: 'a set)\<close>

sublocale MCS_No_Witness_UNIV \<subseteq> MCS_Witness_UNIV consistent \<open>\<lambda>_ _. {}\<close> \<open>\<lambda>_. {}\<close>
proof qed simp

context MCS_No_Witness_UNIV
begin

theorem MCS_Extend':
  assumes \<open>consistent S\<close>
  shows \<open>MCS (Extend S)\<close>
  unfolding witnessed_def using assms consistent_Extend maximal_Extend
  by (metis Diff_empty UN_constant card_of_UNIV empty_subsetI)

end

section \<open>Truth Lemma\<close>

locale Truth_Base =
  fixes semics :: \<open>'model \<Rightarrow> ('model \<Rightarrow> 'fm \<Rightarrow> bool) \<Rightarrow> 'fm \<Rightarrow> bool\<close> (\<open>(_ \<lbrakk>_\<rbrakk> _)\<close> [55, 0, 55] 55)
    and semantics :: \<open>'model \<Rightarrow> 'fm \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<close> 50)
    and \<M> :: \<open>'a set \<Rightarrow> 'model set\<close>
    and \<R> :: \<open>'a set \<Rightarrow> 'model \<Rightarrow> 'fm \<Rightarrow> bool\<close>
  assumes semics_semantics: \<open>M \<Turnstile> p \<longleftrightarrow> M \<lbrakk>(\<Turnstile>)\<rbrakk> p\<close>
begin

abbreviation saturated :: \<open>'a set \<Rightarrow> bool\<close> where
  \<open>saturated S \<equiv> \<forall>p. \<forall>M \<in> \<M>(S). M \<lbrakk>\<R>(S)\<rbrakk> p \<longleftrightarrow> \<R>(S) M p\<close>

end

locale Truth_Witness = Truth_Base semics semantics \<M> \<R> + MCS_Witness consistent witness params
  for semics :: \<open>'model \<Rightarrow> ('model \<Rightarrow> 'fm \<Rightarrow> bool) \<Rightarrow> 'fm \<Rightarrow> bool\<close> (\<open>(_ \<lbrakk>_\<rbrakk> _)\<close> [55, 0, 55] 55)
    and semantics :: \<open>'model \<Rightarrow> 'fm \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<close> 50)
    and \<M> :: \<open>'a set \<Rightarrow> 'model set\<close>
    and \<R> :: \<open>'a set \<Rightarrow> 'model \<Rightarrow> 'fm \<Rightarrow> bool\<close>
    and consistent :: \<open>'a set \<Rightarrow> bool\<close>
    and witness :: \<open>'a \<Rightarrow> 'a set \<Rightarrow> 'a set\<close>
    and params :: \<open>'a \<Rightarrow> 'i set\<close> +
  assumes saturated_semantics: \<open>\<And>S M p. saturated S \<Longrightarrow> M \<in> \<M>(S) \<Longrightarrow> M \<Turnstile> p \<longleftrightarrow> \<R>(S) M p\<close>
    and MCS_saturated: \<open>\<And>S. MCS S \<Longrightarrow> saturated S\<close>
begin

theorem truth_lemma:
  assumes \<open>MCS S\<close> \<open>M \<in> \<M>(S)\<close>
  shows \<open>M \<Turnstile> p \<longleftrightarrow> \<R>(S) M p\<close>
  using saturated_semantics MCS_saturated assms by blast

end

locale Truth_No_Witness = Truth_Witness semics semantics \<M> \<R> consistent  \<open>\<lambda>_ _. {}\<close> \<open>\<lambda>_. {}\<close>
  for semics :: \<open>'model \<Rightarrow> ('model \<Rightarrow> 'fm \<Rightarrow> bool) \<Rightarrow> 'fm \<Rightarrow> bool\<close>
    and semantics :: \<open>'model \<Rightarrow> 'fm \<Rightarrow> bool\<close>
    and \<M> :: \<open>'a set \<Rightarrow> 'model set\<close>
    and \<R> :: \<open>'a set \<Rightarrow> 'model \<Rightarrow> 'fm \<Rightarrow> bool\<close>
    and consistent :: \<open>'a set \<Rightarrow> bool\<close>

end
