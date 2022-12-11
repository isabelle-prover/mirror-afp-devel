(*
  File:      Maximal_Consistent_Sets.thy
  Author:    Asta Halkjær From

  Maximal Consistent Sets based on the transfinite Lindenbaum construction in the textbook
  "Model Theory" by Chang and Keisler (Elsevier Science Publishers 1990)
*)

theory Maximal_Consistent_Sets imports "HOL-Cardinals.Cardinal_Order_Relation" begin

context wo_rel begin

lemma underS_bound: \<open>a \<in> underS n \<Longrightarrow> b \<in> underS n \<Longrightarrow> a \<in> under b \<or> b \<in> under a\<close>
  by (meson BNF_Least_Fixpoint.underS_Field REFL Refl_under_in in_mono under_ofilter ofilter_linord)

lemma finite_underS_bound:
  assumes \<open>finite X\<close> \<open>X \<subseteq> underS n\<close> \<open>X \<noteq> {}\<close>
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
  assumes \<open>finite p\<close> \<open>p \<subseteq> (\<Union>n \<in> Field r. f n)\<close>
  shows \<open>\<exists>m. p \<subseteq> (\<Union>n \<in> under m. f n)\<close>
    using assms
proof (induct rule: finite_induct)
  case (insert x p)
  then obtain m where \<open>p \<subseteq> (\<Union>n \<in> under m. f n)\<close>
    by fast
  moreover obtain m' where \<open>x \<in> f m'\<close> \<open>m' \<in> Field r\<close>
    using insert(4) by blast
  then have \<open>x \<in> (\<Union>n \<in> under m'. f n)\<close>
    using REFL Refl_under_in by fast
  ultimately have \<open>{x} \<union> p \<subseteq> (\<Union>n \<in> under m. f n) \<union> (\<Union>n \<in> under m'. f n)\<close>
    by fast
  then show ?case
    by (metis SUP_union Un_commute insert_is_Un sup.absorb_iff2 ofilter_linord under_ofilter)
qed simp

end

locale MCS_Lim_Ord =
  fixes r :: \<open>'a rel\<close>
  assumes WELL: \<open>Well_order r\<close>
    and isLimOrd_r: \<open>isLimOrd r\<close>
  fixes consistent :: \<open>'a set \<Rightarrow> bool\<close>
  assumes consistent_hereditary: \<open>consistent S \<Longrightarrow> S' \<subseteq> S \<Longrightarrow> consistent S'\<close>
    and inconsistent_finite: \<open>\<And>S. \<not> consistent S \<Longrightarrow> \<exists>S' \<subseteq> S. finite S' \<and> \<not> consistent S'\<close>
begin

definition extendS :: \<open>'a set \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> where
  \<open>extendS S n prev \<equiv> if consistent ({n} \<union> prev) then {n} \<union> prev else prev\<close>

definition extendL :: \<open>('a \<Rightarrow> 'a set) \<Rightarrow> 'a \<Rightarrow> 'a set\<close> where
  \<open>extendL rec n \<equiv> \<Union>m \<in> underS r n. rec m\<close>

definition extend :: \<open>'a set \<Rightarrow> 'a \<Rightarrow> 'a set\<close> where
  \<open>extend S n \<equiv> worecZSL r S (extendS S) extendL n\<close>

lemma wo_rel_r: \<open>wo_rel r\<close>
  by (simp add: WELL wo_rel.intro)

lemma adm_woL_extendL: \<open>adm_woL r extendL\<close>
  unfolding extendL_def wo_rel.adm_woL_def[OF wo_rel_r] by blast

definition Extend :: \<open>'a set \<Rightarrow> 'a set\<close> where
  \<open>Extend S \<equiv> \<Union>n \<in> Field r. extend S n\<close>


lemma extend_subset: \<open>n \<in> Field r \<Longrightarrow> S \<subseteq> extend S n\<close>
proof (induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case
    unfolding extend_def wo_rel.worecZSL_zero[OF wo_rel_r adm_woL_extendL]
    by simp
next
  case (2 i)
  moreover from this have \<open>i \<in> Field r\<close>
    by (meson FieldI1 wo_rel.succ_in wo_rel_r)
  ultimately show ?case
    unfolding extend_def extendS_def
      wo_rel.worecZSL_succ[OF wo_rel_r adm_woL_extendL 2(1)] by auto
next
  case (3 i)
  then show ?case
    unfolding extend_def extendL_def
      wo_rel.worecZSL_isLim[OF wo_rel_r adm_woL_extendL 3(1-2)]
    using wo_rel_r by (metis SUP_upper2 emptyE underS_I wo_rel.zero_in_Field wo_rel.zero_smallest)
qed

lemma Extend_subset': \<open>Field r \<noteq> {} \<Longrightarrow> S \<subseteq> Extend S\<close>
  unfolding Extend_def using extend_subset by fast

lemma extend_underS: \<open>m \<in> underS r n \<Longrightarrow> extend S m \<subseteq> extend S n\<close>
proof (induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case
    unfolding extend_def using wo_rel_r by (simp add: wo_rel.underS_zero)
next
  case (2 i)
  moreover from this have \<open>m = i \<or> m \<in> underS r i\<close>
    by (metis wo_rel.less_succ underS_E underS_I wo_rel_r)
  ultimately show ?case
    unfolding extend_def extendS_def
      wo_rel.worecZSL_succ[OF wo_rel_r adm_woL_extendL 2(1)]
    by auto
next
  case (3 i)
  then show ?case
    unfolding extend_def extendL_def
      wo_rel.worecZSL_isLim[OF wo_rel_r adm_woL_extendL 3(1-2)]
    by blast
qed

lemma extend_under: \<open>m \<in> under r n \<Longrightarrow> extend S m \<subseteq> extend S n\<close>
  using extend_underS wo_rel_r
  by (metis empty_iff in_Above_under set_eq_subset wo_rel.supr_greater wo_rel.supr_under underS_I
      under_Field under_empty)

lemma consistent_extend:
  assumes \<open>consistent S\<close>
  shows \<open>consistent (extend S n)\<close>
  using assms
proof (induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case
    unfolding extend_def wo_rel.worecZSL_zero[OF wo_rel_r adm_woL_extendL] .
next
  case (2 i)
  then show ?case
    unfolding extend_def extendS_def
      wo_rel.worecZSL_succ[OF wo_rel_r adm_woL_extendL 2(1)]
    by auto
next
  case (3 i)
  show ?case
  proof (rule ccontr)
    assume \<open>\<not> consistent (extend S i)\<close>
    then obtain S' where S': \<open>finite S'\<close> \<open>S' \<subseteq> (\<Union>n \<in> underS r i. extend S n)\<close> \<open>\<not> consistent S'\<close>
      unfolding extend_def extendL_def
        wo_rel.worecZSL_isLim[OF wo_rel_r adm_woL_extendL 3(1-2)]
      using inconsistent_finite by auto
    then obtain ns where ns: \<open>S' \<subseteq> (\<Union>n \<in> ns. extend S n)\<close> \<open>ns \<subseteq> underS r i\<close> \<open>finite ns\<close>
      by (metis finite_subset_Union finite_subset_image)
    moreover have \<open>ns \<noteq> {}\<close>
      using S'(3) assms calculation(1) consistent_hereditary by auto
    ultimately obtain j where \<open>\<forall>n \<in> ns. n \<in> under r j\<close> \<open>j \<in> underS r i\<close>
      using wo_rel.finite_underS_bound wo_rel_r ns by (meson subset_iff)
    then have \<open>\<forall>n \<in> ns. extend S n \<subseteq> extend S j\<close>
      using extend_under by fast
    then have \<open>S' \<subseteq> extend S j\<close>
      using S' ns(1) by blast
    then show False
      using 3(3) \<open>\<not> consistent S'\<close> assms consistent_hereditary \<open>j \<in> underS r i\<close> by blast
  qed
qed

lemma consistent_Extend:
  assumes \<open>consistent S\<close>
  shows \<open>consistent (Extend S)\<close>
  unfolding Extend_def
proof (rule ccontr)
  assume \<open>\<not> consistent (\<Union>n \<in> Field r. extend S n)\<close>
  then obtain S' where \<open>finite S'\<close> \<open>S' \<subseteq> (\<Union>n \<in> Field r. extend S n)\<close> \<open>\<not> consistent S'\<close>
    using inconsistent_finite by metis
  then obtain m where \<open>S' \<subseteq> (\<Union>n \<in> under r m. extend S n)\<close> \<open>m \<in> Field r\<close>
    using wo_rel.finite_bound_under wo_rel_r
    by (metis SUP_le_iff assms consistent_hereditary emptyE under_empty)
  then have \<open>S' \<subseteq> extend S m\<close>
    using extend_under by fast
  moreover have \<open>consistent (extend S m)\<close>
    using assms consistent_extend by blast
  ultimately show False
    using \<open>\<not> consistent S'\<close> consistent_hereditary by blast
qed

definition maximal' :: \<open>'a set \<Rightarrow> bool\<close> where
  \<open>maximal' S \<equiv> \<forall>p \<in> Field r. consistent ({p} \<union> S) \<longrightarrow> p \<in> S\<close>

lemma Extend_bound: \<open>n \<in> Field r \<Longrightarrow> extend S n \<subseteq> Extend S\<close>
  unfolding Extend_def by blast

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
    using * isLimOrd_r wo_rel.isLimOrd_aboveS wo_rel_r by fast
  then have \<open>succ r p \<in> Field r\<close>
    using wo_rel_r by (simp add: wo_rel.succ_in_Field)
  moreover have \<open>p \<in> extend S (succ r p)\<close>
    using ** unfolding extend_def extendS_def
      wo_rel.worecZSL_succ[OF wo_rel_r adm_woL_extendL succ]
    by simp
  ultimately show \<open>p \<in> Extend S\<close>
    using Extend_bound by fast
qed

end

locale MCS =
  fixes consistent :: \<open>'a set \<Rightarrow> bool\<close>
  assumes infinite_UNIV: \<open>infinite (UNIV :: 'a set)\<close>
    and \<open>consistent S \<Longrightarrow> S' \<subseteq> S \<Longrightarrow> consistent S'\<close>
    and \<open>\<And>S. \<not> consistent S \<Longrightarrow> \<exists>S' \<subseteq> S. finite S' \<and> \<not> consistent S'\<close>

sublocale MCS \<subseteq> MCS_Lim_Ord \<open>|UNIV|\<close>
proof
  show \<open>Well_order |UNIV|\<close>
    by simp
next
  have \<open>infinite ( Field |UNIV :: 'a set| )\<close>
    using infinite_UNIV by simp
  with card_order_infinite_isLimOrd card_of_Card_order
  show \<open>isLimOrd |UNIV :: 'a set|\<close> .
next
  fix S S'
  show \<open>consistent S \<Longrightarrow> S' \<subseteq> S \<Longrightarrow> consistent S'\<close>
    using MCS_axioms unfolding MCS_def by blast
next
  fix S S'
  show \<open>\<not> consistent S \<Longrightarrow> \<exists>S' \<subseteq> S. finite S' \<and> \<not> consistent S'\<close>
    using MCS_axioms unfolding MCS_def by blast
qed

context MCS begin

lemma Extend_subset: \<open>S \<subseteq> Extend S\<close>
  by (simp add: Extend_subset')

definition maximal :: \<open>'a set \<Rightarrow> bool\<close> where
  \<open>maximal S \<equiv> \<forall>p. consistent ({p} \<union> S) \<longrightarrow> p \<in> S\<close>

lemma maximal_maximal': \<open>maximal S \<longleftrightarrow> maximal' S\<close>
  unfolding maximal_def maximal'_def by simp

lemma maximal_Extend: \<open>maximal (Extend S)\<close>
  using maximal'_Extend maximal_maximal' by fast

end

end
